/*********************************************************************
 * SMART MICROWAVE OVEN
 *
 * DESCRIPTION:
 * An embedded C application for a smart microwave oven simulator
 * using a keypad, 16x2 LCD, 7-segment display, stepper motor
 * (turntable), DAC (audio), and pqiv-based monitor animation.
 *
 * Architecture is deliberately mirrored on snack_dispenser.c
 * (same port-mapping pattern, keypad scan, LCD driver, pqiv ring
 * buffer, non-blocking animation engine, DAC square-wave beeps)
 * so both projects share one common hardware-abstraction style.
 *
 * HARDWARE-DRIVEN ADAPTATIONS FROM THE ORIGINAL SPEC:
 * The keypad only exposes 12 keys: 0-9, A, B (same ScanTable as
 * the snack dispenser). There is no physical C/D key and the scan
 * routine resolves one key at a time, so a simultaneous A+B chord
 * cannot be reliably detected. Three features were adapted to fit:
 *
 *   1. Cancel: no dedicated C key -> press A twice.
 *      1st A during cooking = Pause. 2nd A while paused = Cancel.
 *   2. Child Lock: no reliable A+B chord -> hold A alone for 3s
 *      while at the Home screen (idle, no digits typed) to toggle
 *      lock on/off.
 *   3. Door sensor: no physical door switch wired in -> digit key
 *      '5' is repurposed as a "toggle door" hotkey, but ONLY while
 *      the state machine is actually waiting on the door (door
 *      check screen, or during cooking/paused). In every other
 *      state '5' behaves as a normal digit, so there's no clash
 *      with numeric entry (time / weight / menu selection).
 *
 * These are noted again at the point in the code where each applies.
 *********************************************************************/

#include <stdio.h>
#include <unistd.h>
#include <string.h>
#include <time.h>
#include <stdlib.h>
#include <ctype.h>
#include <signal.h>
#include <sys/types.h>
#include <sys/stat.h>

#include "library.h"

/* ===== Ports (NORMAL mapping) ===== */
#define LEDPORT_NORMAL 0x3A
#define LCDPORT_NORMAL 0x3B
#define SMPORT_NORMAL  0x39
#define KBDPORT_NORMAL 0x3C

/* ===== Ports (SERVICE mapping via DIP) ===== */
#define LEDPORT_ADMIN  0x1A
#define LCDPORT_ADMIN  0x1B
#define SMPORT_ADMIN   0x19
#define KBDPORT_ADMIN  0x1C

static unsigned char gLedPort = LEDPORT_NORMAL;
static unsigned char gLcdPort = LCDPORT_NORMAL;
static unsigned char gSmPort  = SMPORT_NORMAL;
static unsigned char gKbdPort = KBDPORT_NORMAL;

static void set_port_mapping(int admin)
{
    if (admin) {
        gLedPort = LEDPORT_ADMIN;
        gLcdPort = LCDPORT_ADMIN;
        gSmPort  = SMPORT_ADMIN;
        gKbdPort = KBDPORT_ADMIN;
    } else {
        gLedPort = LEDPORT_NORMAL;
        gLcdPort = LCDPORT_NORMAL;
        gSmPort  = SMPORT_NORMAL;
        gKbdPort = KBDPORT_NORMAL;
    }
}

/* ===== Keypad scan constants (identical to snack dispenser rig) ===== */
#define Col7Lo 0xF7
#define Col6Lo 0xFB
#define Col5Lo 0xFD
#define Col4Lo 0xFE

static const unsigned char ScanTable[12] =
/* 0..9, A, B */
{
    0xB7, 0x7E, 0xBE, 0xDE,
    0x7D, 0xBD, 0xDD, 0x7B,
    0xBB, 0xDB, 0x77, 0xD7
};
static unsigned char ScanCode;

/* ===== 7-seg ===== */
static const unsigned char Bin2LED[] =
{
    0x40, 0x79, 0x24, 0x30,
    0x19, 0x12, 0x02, 0x78,
    0x00, 0x18, 0x08, 0x03,
    0x46, 0x21, 0x06, 0x0E
};

static void seg_blank(void) { CM3_outport(gLedPort, 0xFF); }
static void seg_show_digit(int d)
{
    if (d < 0 || d > 9) { seg_blank(); return; }
    CM3_outport(gLedPort, Bin2LED[d]);
}

/* ===== Stepper ===== */
static int full_seq_drive[4] = {0x08, 0x04, 0x02, 0x01};

static long long now_ms(void)
{
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (long long)ts.tv_sec * 1000LL + ts.tv_nsec / 1000000LL;
}

/* ===== LCD ===== */
static void initlcd(void);
static void lcd_writecmd(char cmd);
static void LCDprint(char *sptr);
static void lcddata(unsigned char cmd);

static void lcd_clear(void)
{
    lcd_writecmd(0x01);
    usleep(2000);
}
static void lcd_line2(void) { lcd_writecmd(0xC0); }

static void lcd_print2(const char *l1, const char *l2)
{
    char a[17], b[17];
    snprintf(a, sizeof(a), "%-16.16s", l1);
    snprintf(b, sizeof(b), "%-16.16s", l2);
    initlcd();
    lcd_clear();
    lcd_writecmd(0x80);
    LCDprint(a);
    lcd_line2();
    LCDprint(b);
}

/* ===== Files ===== */
static int file_exists(const char *p)
{
    struct stat st;
    return (stat(p, &st) == 0);
}

/* ===== PQIV / X helpers (identical pattern to snack dispenser) ===== */
static void env_for_x(void)
{
    const char *disp = getenv("DISPLAY");
    if (!disp || !*disp) {
        if (file_exists("/tmp/.X11-unix/X1")) disp = ":1";
        else if (file_exists("/tmp/.X11-unix/X0")) disp = ":0";
        else disp = ":0";
        setenv("DISPLAY", disp, 1);
    }
    const char *home = getenv("HOME");
    if (home && *home) {
        char xa[512];
        snprintf(xa, sizeof(xa), "%s/.Xauthority", home);
        setenv("XAUTHORITY", xa, 1);
    } else {
        unsetenv("XAUTHORITY");
    }
    setenv("NO_AT_BRIDGE", "1", 1);
}

static void kill_pid_soft_hard(pid_t p)
{
    if (p <= 0) return;
    kill(p, SIGTERM);
    usleep(60000);
    kill(p, SIGKILL);
}

#define PQIV_KEEP 8
static pid_t pqiv_ring[PQIV_KEEP] = {0};
static int pqiv_pos = 0;
static int pqiv_count = 0;

#define IMG_HOME "/tmp/mw_home.jpg"

static void pqiv_kill_all_spawned(void)
{
    for (int i = 0; i < PQIV_KEEP; i++) {
        kill_pid_soft_hard(pqiv_ring[i]);
        pqiv_ring[i] = 0;
    }
    pqiv_pos = 0;
    pqiv_count = 0;
}

static void show_image(const char *path)
{
    if (pqiv_count >= PQIV_KEEP) {
        kill_pid_soft_hard(pqiv_ring[pqiv_pos]);
        pqiv_ring[pqiv_pos] = 0;
    }
    pid_t pid = fork();
    if (pid == 0) {
        env_for_x();
        execlp("pqiv", "pqiv", "-f", path, (char*)NULL);
        _exit(127);
    } else if (pid > 0) {
        pqiv_ring[pqiv_pos] = pid;
        pqiv_pos = (pqiv_pos + 1) % PQIV_KEEP;
        if (pqiv_count < PQIV_KEEP) pqiv_count++;
    }
    usleep(25000);
}

/* ===== Shared Animation Engine (non-blocking, oneshot OR loop) ===== */
typedef struct {
    int active;
    int loop;               /* 1 = cycle forever, 0 = oneshot */
    const char **frames;
    int nframes;
    int idx;
    int direction;
    long long next_ms;
    int frame_ms;
    int oneshot_done;
} Anim;

static void anim_start(Anim *a, const char **frames, int nframes, int direction, int frame_ms)
{
    a->active = 1;
    a->loop = 0;
    a->frames = frames;
    a->nframes = nframes;
    a->direction = (direction >= 0) ? +1 : -1;
    a->frame_ms = frame_ms;
    a->oneshot_done = 0;
    a->idx = (a->direction > 0) ? 0 : (nframes - 1);
    a->next_ms = now_ms();
}

static void anim_start_loop(Anim *a, const char **frames, int nframes, int frame_ms)
{
    a->active = 1;
    a->loop = 1;
    a->frames = frames;
    a->nframes = nframes;
    a->direction = +1;
    a->frame_ms = frame_ms;
    a->oneshot_done = 0;
    a->idx = 0;
    a->next_ms = now_ms();
}

static void anim_stop(Anim *a) { a->active = 0; }

static void anim_tick(Anim *a)
{
    if (!a->active) return;
    if (!a->loop && a->oneshot_done) return;

    long long t = now_ms();
    if (t < a->next_ms) return;

    const char *p = a->frames[a->idx];
    if (!file_exists(p)) p = IMG_HOME;
    show_image(p);

    a->next_ms = t + a->frame_ms;

    if (a->loop) {
        a->idx = (a->idx + 1) % a->nframes;
        return;
    }

    if (a->direction > 0) {
        if (a->idx == a->nframes - 1) { a->oneshot_done = 1; a->active = 0; }
        else a->idx++;
    } else {
        if (a->idx == 0) { a->oneshot_done = 1; a->active = 0; }
        else a->idx--;
    }
}

/* ===== Door open/close animation (service enter/exit) ===== */
#define IMG_DOOR_1 "/tmp/mw_door_1.jpg"
#define IMG_DOOR_2 "/tmp/mw_door_2.jpg"
#define IMG_DOOR_3 "/tmp/mw_door_3.jpg"
#define IMG_DOOR_4 "/tmp/mw_door_4.jpg"
static const char* door_frames[] = { IMG_DOOR_1, IMG_DOOR_2, IMG_DOOR_3, IMG_DOOR_4 };
static const int DOOR_N = 4;
#define DOOR_FRAME_MS 800

/* ===== Cooking loop animation (rotating food + steam) ===== */
#define IMG_ROTATE_1 "/tmp/mw_rotate1.jpg"
#define IMG_ROTATE_2 "/tmp/mw_rotate2.jpg"
#define IMG_ROTATE_3 "/tmp/mw_rotate3.jpg"
#define IMG_STEAM    "/tmp/mw_steam.jpg"
static const char* cook_frames[] = { IMG_ROTATE_1, IMG_ROTATE_2, IMG_ROTATE_3, IMG_STEAM };
static const int COOK_N = 4;

static Anim gDoorAnim;
static Anim gCookAnim;

/* ===== Other screens ===== */
#define IMG_COOK       "/tmp/mw_cook.jpg"
#define IMG_REHEAT     "/tmp/mw_reheat.jpg"
#define IMG_DEFROST    "/tmp/mw_defrost.jpg"
#define IMG_BEVERAGE   "/tmp/mw_beverage.jpg"
#define IMG_POPCORN    "/tmp/mw_popcorn.jpg"
#define IMG_LASTUSED   "/tmp/mw_lastused.jpg"
#define IMG_DOOR_CLOSED "/tmp/mw_door_closed.jpg"
#define IMG_DOOR_OPEN   "/tmp/mw_door_open.jpg"
#define IMG_PAUSED      "/tmp/mw_paused.jpg"
#define IMG_FINISHED    "/tmp/mw_finished.jpg"
#define IMG_LOCKED      "/tmp/mw_locked.jpg"

#define IMG_SVC_MENU       "/tmp/mw_service.jpg"
#define IMG_SVC_DOOR_TEST  "/tmp/mw_svc_door.jpg"
#define IMG_SVC_MOTOR_TEST "/tmp/mw_svc_motor.jpg"
#define IMG_SVC_LCD_TEST   "/tmp/mw_svc_lcd.jpg"
#define IMG_SVC_SOUND_TEST "/tmp/mw_svc_sound.jpg"
#define IMG_SVC_STATS      "/tmp/mw_svc_stats.jpg"
#define IMG_SVC_RESET      "/tmp/mw_svc_reset.jpg"

/* ===== Exit handling ===== */
static void cleanup(void) { pqiv_kill_all_spawned(); }
static void on_sig(int sig) { (void)sig; cleanup(); _exit(0); }

/* ===== Keypad ===== */
static unsigned char ProcKey(void)
{
    for (unsigned char j = 0; j < 12; j++) {
        if (ScanCode == ScanTable[j]) {
            if (j > 9) return (unsigned char)(j + 0x37); /* A, B */
            return (unsigned char)(j + 0x30);            /* 0-9 */
        }
    }
    return 0xFF;
}

static unsigned char ScanKey(void)
{
    CM3_outport(gKbdPort, Col7Lo);
    ScanCode = CM3_inport(gKbdPort);
    ScanCode |= 0x0F;
    ScanCode &= Col7Lo;
    if (ScanCode != Col7Lo) return ProcKey();

    CM3_outport(gKbdPort, Col6Lo);
    ScanCode = CM3_inport(gKbdPort);
    ScanCode |= 0x0F;
    ScanCode &= Col6Lo;
    if (ScanCode != Col6Lo) return ProcKey();

    CM3_outport(gKbdPort, Col5Lo);
    ScanCode = CM3_inport(gKbdPort);
    ScanCode |= 0x0F;
    ScanCode &= Col5Lo;
    if (ScanCode != Col5Lo) return ProcKey();

    CM3_outport(gKbdPort, Col4Lo);
    ScanCode = CM3_inport(gKbdPort);
    ScanCode |= 0x0F;
    ScanCode &= Col4Lo;
    if (ScanCode != Col4Lo) return ProcKey();

    return 0xFF;
}

static void wait_key_release(void)
{
    while (ScanKey() != 0xFF) usleep(12000);
}

#define KEY_BACK  'A'
#define KEY_ENTER 'B'
#define KEY_DOOR_TOGGLE '5'   /* only honoured in door-check / cooking / paused states */

/* ===== Motor helpers ===== */
static void motor_write_phase(int phase)
{
    CM3_outport(gSmPort, full_seq_drive[phase & 3]);
}

/* Continuous non-blocking turntable rotation while cooking.
   Phase-step delay (ms) varies with power level -> visibly
   different rotation speed for High / Medium / Low. */
static int gMotorPhase = 0;
static long long gMotorNextStepMs = 0;

static int power_phase_delay_ms(int power)
{
    if (power == 1) return 3;   /* High   - fast  */
    if (power == 2) return 6;   /* Medium - normal*/
    return 12;                  /* Low    - slow  */
}

static void motor_cook_tick(long long t, int power)
{
    if (t < gMotorNextStepMs) return;
    motor_write_phase(gMotorPhase);
    gMotorPhase = (gMotorPhase + 1) & 3;
    gMotorNextStepMs = t + power_phase_delay_ms(power);
}

static void motor_stop(void) { CM3_outport(gSmPort, 0x00); }

/* Service motor test: short spin, N cycles (blocking, like snack dispenser) */
#define MOTOR_STEPS_PER_CYCLE 18
#define MOTOR_PHASE_DELAY_US  4500

static void motor_spin_one_cycle(void)
{
    static int phase = 0;
    for (int s = 0; s < MOTOR_STEPS_PER_CYCLE; s++) {
        for (int i = 0; i < 4; i++) {
            motor_write_phase(phase);
            phase = (phase + 1) & 3;
            usleep(MOTOR_PHASE_DELAY_US);
        }
    }
    motor_stop();
}

static void run_motor_test_cycles(int cycles)
{
    if (cycles < 1) cycles = 1;
    if (cycles > 15) cycles = 15;
    for (int c = 0; c < cycles; c++) {
        motor_spin_one_cycle();
        usleep(500000);
    }
}

/* ===== Stats (incremented as the system runs) ===== */
typedef struct {
    long cook_count;
    long door_opens;
    long errors;
    long total_cook_seconds;
} Stats;
static Stats gStats = {0, 0, 0, 0};

/* ===== DAC beeps ===== */
static void dac_write(unsigned char v)
{
    CM3PortWrite(3, v);
    CM3PortWrite(5, v);
}

static void beep_square(int duration_ms, int half_period_us, unsigned char hi, unsigned char lo)
{
    long long end = now_ms() + duration_ms;
    while (now_ms() < end) {
        dac_write(hi);
        usleep(half_period_us);
        dac_write(lo);
        usleep(half_period_us);
    }
    dac_write(0);
}

static void beep_keypress(void) { beep_square(25, 650, 200, 20); }

/* Error = buzz. Every error beep also counts toward Statistics. */
static void beep_error(void)
{
    gStats.errors++;
    beep_square(160, 1400, 180, 0);
}

/* Start = beep beep */
static void beep_start(void)
{
    beep_square(70, 700, 220, 0);
    usleep(60000);
    beep_square(70, 700, 220, 0);
}

/* Finish = beep beep beep */
static void beep_finish(void)
{
    for (int i = 0; i < 3; i++) {
        beep_square(80, 650, 220, 0);
        usleep(60000);
    }
}

/* Cancel = one long beep */
static void beep_cancel(void) { beep_square(500, 900, 200, 0); }

/* Key press during cooking countdown (last 10s) - short tick */
static void beep_tick(void) { beep_square(15, 500, 150, 0); }

/* ===== Time helpers ===== */
static void format_mmss(int total_sec, char out[12])
{
    if (total_sec < 0) total_sec = 0;
    int m = total_sec / 60;
    int s = total_sec % 60;
    snprintf(out, 12, "%02d:%02d", m, s);
}

/* Cook-mode time entry is packed digits: last 2 digits = seconds,
   remaining leading digits = minutes. e.g. "130" -> 1:30, "45" -> 0:45 */
static int parse_cook_time(const char *buf, int *out_sec)
{
    int len = (int)strlen(buf);
    if (len == 0) return 0;
    int mm, ss;
    if (len <= 2) {
        mm = 0;
        ss = atoi(buf);
    } else {
        char mbuf[8];
        int mlen = len - 2;
        strncpy(mbuf, buf, mlen);
        mbuf[mlen] = '\0';
        mm = atoi(mbuf);
        ss = atoi(buf + mlen);
    }
    if (ss > 59) return 0;
    int total = mm * 60 + ss;
    if (total < 1 || total > 3600) return 0; /* cap 60:00 */
    *out_sec = total;
    return 1;
}

/* Defrost: time (sec) = weight (g) * rate. 500g -> 300s matches spec example. */
#define DEFROST_SEC_PER_GRAM 0.6f
static int defrost_time_from_weight(int grams)
{
    return (int)(grams * DEFROST_SEC_PER_GRAM);
}

/* ===== Presets ===== */
typedef struct { const char *name; int time_sec; int power; } ReheatItem;
static ReheatItem reheat_items[] = {
    { "Rice",    120, 2 }, /* 2:00 Medium */
    { "Pizza",    90, 1 }, /* 1:30 High   */
    { "Soup",    180, 2 }, /* 3:00 Medium - assumed, adjust as needed */
    { "Noodles", 150, 1 }, /* 2:30 High   - assumed, adjust as needed */
};
static const int REHEAT_N = 4;

typedef struct { const char *name; } DefrostItem;
static DefrostItem defrost_items[] = { {"Chicken"}, {"Fish"}, {"Beef"} };
static const int DEFROST_N = 3;

typedef struct { const char *name; int time_sec; int power; } BeverageItem;
static BeverageItem beverage_items[] = {
    { "Coffee", 90, 1 }, /* assumed presets, adjust as needed */
    { "Tea",    60, 1 },
    { "Milk",   75, 2 },
};
static const int BEVERAGE_N = 3;

#define POPCORN_TIME_SEC 135  /* 2:15 */
#define POPCORN_POWER    1    /* High */

static const char *power_name(int p)
{
    if (p == 1) return "High";
    if (p == 2) return "Med";
    return "Low";
}

/* ===== Last Used memory ===== */
typedef struct {
    int valid;
    char mode_name[16];
    int time_sec;
    int power;
} LastUsed;
static LastUsed gLastUsed = { 0, "", 0, 0 };

/* ===== Idle timeout (30s), applies to all non-cooking, non-service states ===== */
#define IDLE_TIMEOUT_MS 30000
static long long idle_deadline = 0;

static void idle_reset(void) { idle_deadline = now_ms() + IDLE_TIMEOUT_MS; }
static void idle_stop(void) { idle_deadline = 0; }
static int idle_expired(long long t)
{
    return (idle_deadline > 0 && t >= idle_deadline);
}

/* ===== Service 7-seg blink (reused pattern) ===== */
static long long svc_blink_next = 0;
static int svc_blink_on = 1;
static void service_blink_tick(long long t)
{
    if (svc_blink_next == 0) {
        svc_blink_next = t + 500;
        svc_blink_on = 1;
        seg_show_digit(0);
        return;
    }
    if (t >= svc_blink_next) {
        svc_blink_next += 500;
        svc_blink_on = !svc_blink_on;
        if (svc_blink_on) seg_show_digit(0); else seg_blank();
    }
}
static void service_blink_reset(void) { svc_blink_next = 0; svc_blink_on = 1; seg_show_digit(0); }

/* ===== Small digit-buffer helpers ===== */
static void buf_clear(char *buf, int *len) { *len = 0; buf[0] = '\0'; }
static void buf_append(char *buf, int *len, int maxlen, char c)
{
    if (*len < maxlen) { buf[(*len)++] = c; buf[*len] = '\0'; }
}
static void buf_backspace(char *buf, int *len)
{
    if (*len > 0) { (*len)--; buf[*len] = '\0'; }
}

/* ===== MAIN ===== */
int main(void)
{
    atexit(cleanup);
    signal(SIGINT, on_sig);
    signal(SIGTERM, on_sig);

    CM3DeviceInit();
    CM3DeviceSpiInit(0);
    CM3PortInit(4);
    CM3PortInit(1);
    CM3PortInit(0);
    CM3PortInit(3);
    CM3PortInit(5);

    enum {
        ST_HOME = 0,
        ST_COOK_TIME, ST_COOK_POWER,
        ST_REHEAT_SELECT,
        ST_DEFROST_SELECT, ST_DEFROST_WEIGHT,
        ST_BEVERAGE_SELECT,
        ST_POPCORN_CONFIRM,
        ST_LASTUSED_CONFIRM,
        ST_DOOR_CHECK,
        ST_COOKING,
        ST_PAUSED,
        ST_FINISHED,

        ST_SVC_GATE, ST_RETURN_GATE,
        ST_DOOR_ANIM_OPEN, ST_DOOR_ANIM_CLOSE,
        ST_SVC_MENU,
        ST_SVC_DOOR_TEST,
        ST_SVC_MOTOR_TEST,
        ST_SVC_LCD_TEST,
        ST_SVC_SOUND_TEST,
        ST_SVC_STATS,
        ST_SVC_RESET_CONFIRM
    } st = ST_HOME;

    char selbuf[8] = {0}; int sellen = 0;   /* home menu / sub-menu digit entry */
    char timebuf[8] = {0}; int timelen = 0; /* cook time / weight / service digit entry */

    int pending_power = 0;
    int pending_time_sec = 0;
    char pending_mode_name[16] = "";
    int pending_food_idx = -1; /* used by defrost/reheat/beverage selection */

    int remaining_ms = 0;
    long long last_tick_ms = 0;
    int last_shown_sec = -1;

    int door_open = 0;          /* 0 = closed, 1 = open */
    int paused_reason = 0;      /* 0 = user pause, 1 = door-open pause */

    int child_lock = 0;

    int service_mode = 0;
    long long svc_gate_deadline = 0;
    long long return_gate_deadline = 0;

    int svc_motor_cycles_buf_len = 0; char svc_motor_cycles_buf[8] = {0};
    int svc_sound_choice = 0;
    int svc_stats_page = 0;
    int svc_lcd_test_active = 0;

    show_image(IMG_HOME);
    lcd_print2("Smart Microwave", "1-6 then B");
    beep_start(); /* startup sound cue */
    seg_blank();
    idle_reset();

    while (1) {
        long long t = now_ms();

        anim_tick(&gDoorAnim);

        /* ===== Cooking-state background processing (highest priority) ===== */
        if (st == ST_COOKING || st == ST_PAUSED) {
            /* Door forces a pause any time it's open while cooking */
            if (st == ST_COOKING && door_open) {
                st = ST_PAUSED;
                paused_reason = 1;
                motor_stop();
                anim_stop(&gCookAnim);
                show_image(IMG_DOOR_OPEN);
                lcd_print2("Door Open", "Close Door");
                last_tick_ms = t;
            }
            /* Door closing while door-paused auto-resumes */
            else if (st == ST_PAUSED && paused_reason == 1 && !door_open) {
                st = ST_COOKING;
                anim_start_loop(&gCookAnim, cook_frames, COOK_N, 800);
                last_tick_ms = t;
            }

            if (st == ST_COOKING) {
                long long delta = t - last_tick_ms;
                last_tick_ms = t;
                remaining_ms -= (int)delta;
                if (remaining_ms < 0) remaining_ms = 0;

                anim_tick(&gCookAnim);
                motor_cook_tick(t, pending_power);

                int remaining_sec = (remaining_ms + 999) / 1000;
                if (remaining_sec != last_shown_sec) {
                    last_shown_sec = remaining_sec;
                    char l2[17]; char mmss[12];
                    format_mmss(remaining_sec, mmss);
                    snprintf(l2, sizeof(l2), "%s", mmss);
                    lcd_print2("Cooking", l2);

                    if (remaining_sec <= 10 && remaining_sec >= 1) {
                        seg_show_digit(remaining_sec == 10 ? 0 : remaining_sec);
                        beep_tick();
                    } else {
                        seg_blank();
                    }
                }

                if (remaining_ms <= 0) {
                    motor_stop();
                    anim_stop(&gCookAnim);
                    st = ST_FINISHED;
                    gStats.cook_count++;
                    gStats.total_cook_seconds += pending_time_sec;
                    show_image(IMG_FINISHED);
                    lcd_print2("Finished", "Enjoy!");
                    beep_finish();
                    idle_stop();
                }
            }
        }

        if (st == ST_FINISHED) {
            /* Wait five seconds then auto-return home (spec-defined) */
            static long long finished_deadline = 0;
            if (finished_deadline == 0) finished_deadline = t + 5000;
            if (t >= finished_deadline) {
                finished_deadline = 0;
                st = ST_HOME;
                pending_power = 0; pending_time_sec = 0; pending_food_idx = -1;
                pending_mode_name[0] = '\0';
                buf_clear(selbuf, &sellen);
                buf_clear(timebuf, &timelen);
                show_image(IMG_HOME);
                lcd_print2("Smart Microwave", "1-6 then B");
                idle_reset();
            }
            usleep(20000);
            continue;
        }

        /* ===== Door animation transitions (service entry/exit, reused pattern) ===== */
        if (st == ST_DOOR_ANIM_OPEN && gDoorAnim.oneshot_done) {
            st = ST_SVC_MENU;
            buf_clear(selbuf, &sellen);
            show_image(IMG_SVC_MENU);
            lcd_print2("Service Menu", "1-6 then B");
        }
        if (st == ST_DOOR_ANIM_CLOSE && gDoorAnim.oneshot_done) {
            service_mode = 0;
            set_port_mapping(0);
            st = ST_HOME;
            buf_clear(selbuf, &sellen);
            buf_clear(timebuf, &timelen);
            show_image(IMG_HOME);
            lcd_print2("Smart Microwave", "1-6 then B");
            idle_reset();
        }

        /* ===== Service gate timeouts ===== */
        if (st == ST_SVC_GATE && svc_gate_deadline > 0 && t >= svc_gate_deadline) {
            beep_error();
            svc_gate_deadline = 0;
            set_port_mapping(0);
            service_mode = 0;
            st = ST_HOME;
            show_image(IMG_HOME);
            lcd_print2("Smart Microwave", "1-6 then B");
            idle_reset();
            continue;
        }
        if (st == ST_RETURN_GATE && return_gate_deadline > 0 && t >= return_gate_deadline) {
            beep_error();
            return_gate_deadline = 0;
            service_mode = 1;
            set_port_mapping(1);
            st = ST_SVC_MENU;
            show_image(IMG_SVC_MENU);
            lcd_print2("Service Menu", "1-6 then B");
            continue;
        }

        /* ===== 7-seg for service mode ===== */
        if (service_mode) service_blink_tick(t);

        /* ===== Idle 30s timeout (menu/selection states only) ===== */
        if (!service_mode && st != ST_COOKING && st != ST_PAUSED && st != ST_FINISHED
            && st != ST_DOOR_CHECK) {
            if (idle_expired(t)) {
                st = ST_HOME;
                buf_clear(selbuf, &sellen);
                buf_clear(timebuf, &timelen);
                pending_power = 0; pending_time_sec = 0; pending_food_idx = -1;
                show_image(IMG_HOME);
                lcd_print2("Returning Home", "...");
                usleep(700000);
                lcd_print2("Smart Microwave", "1-6 then B");
                idle_reset();
                continue;
            }
        }

        unsigned char k = ScanKey();
        if (k == 0xFF) { usleep(20000); continue; }

        /* ===== Child Lock: hold A for 3s at Home, idle, no digits typed =====
           (Adapted from the spec's A+B chord - see header note.) */
        if (st == ST_HOME && sellen == 0 && !service_mode && k == KEY_BACK) {
            long long hold_start = now_ms();
            int held_full = 0;
            while (ScanKey() == KEY_BACK) {
                if (now_ms() - hold_start >= 3000) { held_full = 1; break; }
                usleep(20000);
            }
            wait_key_release();
            if (held_full) {
                child_lock = !child_lock;
                if (child_lock) {
                    show_image(IMG_LOCKED);
                    lcd_print2("Child Lock", "Enabled");
                } else {
                    show_image(IMG_HOME);
                    lcd_print2("Child Lock", "Disabled");
                }
                beep_cancel();
                usleep(1000000);
                if (child_lock) { lcd_print2("Locked", "Hold A to unlock"); }
                else { lcd_print2("Smart Microwave", "1-6 then B"); }
                idle_reset();
                continue;
            }
            /* short tap: falls through to normal back-key handling below */
        }

        if (child_lock && st == ST_HOME) {
            /* Only the hold-A unlock gesture above works; everything else is blocked */
            beep_error();
            lcd_print2("Locked", "Hold A to unlock");
            usleep(300000);
            continue;
        }

        beep_keypress();
        wait_key_release();

        /* ===== Service gate confirms (any key) ===== */
        if (st == ST_SVC_GATE) {
            svc_gate_deadline = 0;
            service_mode = 1;
            service_blink_reset();
            st = ST_DOOR_ANIM_OPEN;
            gDoorAnim.oneshot_done = 0;
            anim_start(&gDoorAnim, door_frames, DOOR_N, +1, DOOR_FRAME_MS);
            continue;
        }
        if (st == ST_RETURN_GATE) {
            return_gate_deadline = 0;
            st = ST_DOOR_ANIM_CLOSE;
            gDoorAnim.oneshot_done = 0;
            anim_start(&gDoorAnim, door_frames, DOOR_N, -1, DOOR_FRAME_MS);
            continue;
        }

        /* ===== Door toggle hotkey ('5'), only meaningful in these states ===== */
        if (k == KEY_DOOR_TOGGLE &&
            (st == ST_DOOR_CHECK || st == ST_COOKING || st == ST_PAUSED)) {
            int was_open = door_open;
            door_open = !door_open;
            if (!was_open && door_open) gStats.door_opens++;

            if (st == ST_DOOR_CHECK) {
                if (door_open) { show_image(IMG_DOOR_OPEN); lcd_print2("Door Open", "Close Door"); }
                else { show_image(IMG_DOOR_CLOSED); lcd_print2("Door Closed?", "B=Start"); }
            }
            continue;
        }

        /* ===== A = Back / Pause / Cancel (context dependent) ===== */
        if (k == KEY_BACK) {
            if (service_mode) {
                if (st == ST_SVC_MENU) {
                    /* handled by ENTER-with-"1234" below; A here just clears buffer */
                    buf_clear(selbuf, &sellen);
                    lcd_print2("Service Menu", "1-6 then B");
                } else {
                    st = ST_SVC_MENU;
                    buf_clear(selbuf, &sellen);
                    buf_clear(svc_motor_cycles_buf, &svc_motor_cycles_buf_len);
                    svc_stats_page = 0;
                    show_image(IMG_SVC_MENU);
                    lcd_print2("Service Menu", "1-6 then B");
                }
                continue;
            }

            if (st == ST_COOKING) {
                /* 1st A = Pause (user-initiated) */
                st = ST_PAUSED;
                paused_reason = 0;
                motor_stop();
                anim_stop(&gCookAnim);
                show_image(IMG_PAUSED);
                lcd_print2("Paused", "B=Resume A=Cancel");
                continue;
            }
            if (st == ST_PAUSED && paused_reason == 0) {
                /* 2nd A while user-paused = Cancel */
                beep_cancel();
                motor_stop();
                anim_stop(&gCookAnim);
                st = ST_HOME;
                pending_power = 0; pending_time_sec = 0; pending_food_idx = -1;
                buf_clear(selbuf, &sellen);
                buf_clear(timebuf, &timelen);
                show_image(IMG_HOME);
                lcd_print2("Cancelled", "");
                usleep(700000);
                lcd_print2("Smart Microwave", "1-6 then B");
                idle_reset();
                continue;
            }

            /* Generic back-out-one-level / clear-digit behaviour */
            if (st == ST_HOME) {
                if (sellen > 0) {
                    buf_backspace(selbuf, &sellen);
                    char l1[17]; snprintf(l1, sizeof(l1), "Mode:%-4.4s", selbuf);
                    lcd_print2(l1, "1-6 then B");
                } else {
                    lcd_print2("Smart Microwave", "1-6 then B");
                }
            } else if (st == ST_COOK_TIME) {
                if (timelen > 0) {
                    buf_backspace(timebuf, &timelen);
                    char l1[17]; snprintf(l1, sizeof(l1), "Time:%-6.6s", timebuf);
                    lcd_print2(l1, "MMSS then B");
                } else {
                    st = ST_HOME;
                    show_image(IMG_HOME);
                    lcd_print2("Smart Microwave", "1-6 then B");
                }
            } else if (st == ST_COOK_POWER) {
                st = ST_COOK_TIME;
                buf_clear(timebuf, &timelen);
                show_image(IMG_COOK);
                lcd_print2("Enter time", "MMSS then B");
            } else if (st == ST_DEFROST_WEIGHT) {
                st = ST_DEFROST_SELECT;
                buf_clear(timebuf, &timelen);
                show_image(IMG_DEFROST);
                lcd_print2("1 Chick 2 Fish", "3 Beef, B=OK");
            } else if (st == ST_REHEAT_SELECT || st == ST_DEFROST_SELECT ||
                       st == ST_BEVERAGE_SELECT || st == ST_POPCORN_CONFIRM ||
                       st == ST_LASTUSED_CONFIRM) {
                st = ST_HOME;
                buf_clear(selbuf, &sellen);
                buf_clear(timebuf, &timelen);
                show_image(IMG_HOME);
                lcd_print2("Smart Microwave", "1-6 then B");
            } else if (st == ST_DOOR_CHECK) {
                st = ST_HOME;
                buf_clear(selbuf, &sellen);
                buf_clear(timebuf, &timelen);
                show_image(IMG_HOME);
                lcd_print2("Smart Microwave", "1-6 then B");
            }
            idle_reset();
            continue;
        }

        /* ===== Digits (0-9), routed by state ===== */
        if (isdigit((int)k)) {
            if (service_mode) {
                if (st == ST_SVC_MENU) {
                    buf_append(selbuf, &sellen, 4, (char)k);
                    char l1[17]; snprintf(l1, sizeof(l1), "Svc:%-8.8s", selbuf);
                    lcd_print2(l1, "1-6 or 1234, B");
                } else if (st == ST_SVC_MOTOR_TEST) {
                    buf_append(svc_motor_cycles_buf, &svc_motor_cycles_buf_len, 2, (char)k);
                    char l1[17]; snprintf(l1, sizeof(l1), "Cycles:%-4.4s", svc_motor_cycles_buf);
                    lcd_print2(l1, "B=Run A=Back");
                } else if (st == ST_SVC_SOUND_TEST) {
                    /* single digit choice 1-4, handled immediately */
                    int choice = k - '0';
                    if (choice >= 1 && choice <= 4) {
                        svc_sound_choice = choice;
                        lcd_print2("Playing...", "Please wait");
                        if (choice == 1) beep_keypress();
                        else if (choice == 2) beep_error();
                        else if (choice == 3) beep_finish();
                        else if (choice == 4) beep_cancel();
                        show_image(IMG_SVC_SOUND_TEST);
                        lcd_print2("1 Key 2 Warn", "3 Fin 4 Cancel");
                    } else {
                        beep_error();
                        lcd_print2("Pick 1-4", "Try again");
                    }
                }
                idle_reset();
                continue;
            }

            switch (st) {
                case ST_HOME:
                    buf_append(selbuf, &sellen, 4, (char)k);
                    { char l1[17]; snprintf(l1, sizeof(l1), "Mode:%-4.4s", selbuf);
                      lcd_print2(l1, "1-6 then B"); }
                    break;
                case ST_COOK_TIME:
                    buf_append(timebuf, &timelen, 4, (char)k);
                    { char l1[17]; snprintf(l1, sizeof(l1), "Time:%-6.6s", timebuf);
                      lcd_print2(l1, "MMSS then B"); }
                    break;
                case ST_COOK_POWER:
                    /* single digit 1-3, immediate */
                    if (k == '1' || k == '2' || k == '3') {
                        pending_power = k - '0';
                        char l1[17]; snprintf(l1, sizeof(l1), "Power: %s", power_name(pending_power));
                        lcd_print2(l1, "B=Confirm");
                    } else {
                        beep_error();
                        lcd_print2("Power 1-3 only", "1 Hi 2 Med 3 Lo");
                    }
                    break;
                case ST_REHEAT_SELECT: {
                    int idx = k - '0';
                    if (idx >= 1 && idx <= REHEAT_N) {
                        pending_food_idx = idx - 1;
                        char l1[17]; snprintf(l1, sizeof(l1), "%s", reheat_items[pending_food_idx].name);
                        lcd_print2(l1, "B=Confirm");
                    } else {
                        beep_error();
                        lcd_print2("Pick 1-4", "Try again");
                    }
                    break;
                }
                case ST_DEFROST_SELECT: {
                    int idx = k - '0';
                    if (idx >= 1 && idx <= DEFROST_N) {
                        pending_food_idx = idx - 1;
                        char l1[17]; snprintf(l1, sizeof(l1), "%s", defrost_items[pending_food_idx].name);
                        lcd_print2(l1, "B=Next (weight)");
                    } else {
                        beep_error();
                        lcd_print2("Pick 1-3", "Try again");
                    }
                    break;
                }
                case ST_DEFROST_WEIGHT:
                    buf_append(timebuf, &timelen, 4, (char)k);
                    { char l1[17]; snprintf(l1, sizeof(l1), "Weight:%-4.4sg", timebuf);
                      lcd_print2(l1, "grams then B"); }
                    break;
                case ST_BEVERAGE_SELECT: {
                    int idx = k - '0';
                    if (idx >= 1 && idx <= BEVERAGE_N) {
                        pending_food_idx = idx - 1;
                        char l1[17]; snprintf(l1, sizeof(l1), "%s", beverage_items[pending_food_idx].name);
                        lcd_print2(l1, "B=Confirm");
                    } else {
                        beep_error();
                        lcd_print2("Pick 1-3", "Try again");
                    }
                    break;
                }
                default:
                    beep_error();
                    break;
            }
            idle_reset();
            continue;
        }

        /* ===== B = Confirm/Enter/Resume (context dependent) ===== */
        if (k == KEY_ENTER) {
            if (st == ST_PAUSED && paused_reason == 0) {
                st = ST_COOKING;
                last_tick_ms = now_ms();
                anim_start_loop(&gCookAnim, cook_frames, COOK_N, 800);
                continue;
            }

            if (service_mode) {
                if (st == ST_SVC_MENU) {
                    if (strcmp(selbuf, "1234") == 0) {
                        buf_clear(selbuf, &sellen);
                        show_image(IMG_SVC_MENU);
                        lcd_print2("Revert SA5 DIP", "Press any key");
                        usleep(120000);
                        set_port_mapping(0);
                        st = ST_RETURN_GATE;
                        return_gate_deadline = now_ms() + 8000;
                        continue;
                    }
                    if (strcmp(selbuf, "1") == 0) {
                        st = ST_SVC_DOOR_TEST;
                        show_image(IMG_SVC_DOOR_TEST);
                        lcd_print2("Door Test", "B=Run A=Back");
                    } else if (strcmp(selbuf, "2") == 0) {
                        st = ST_SVC_MOTOR_TEST;
                        buf_clear(svc_motor_cycles_buf, &svc_motor_cycles_buf_len);
                        show_image(IMG_SVC_MOTOR_TEST);
                        lcd_print2("Motor cyc 1-15", "B=Run A=Back");
                    } else if (strcmp(selbuf, "3") == 0) {
                        st = ST_SVC_LCD_TEST;
                        svc_lcd_test_active = 1;
                        show_image(IMG_SVC_LCD_TEST);
                        lcd_print2("ABCDEFGHIJKLMNO", "1234567890");
                    } else if (strcmp(selbuf, "4") == 0) {
                        st = ST_SVC_SOUND_TEST;
                        show_image(IMG_SVC_SOUND_TEST);
                        lcd_print2("1 Key 2 Warn", "3 Fin 4 Cancel");
                    } else if (strcmp(selbuf, "5") == 0) {
                        st = ST_SVC_STATS;
                        svc_stats_page = 0;
                        show_image(IMG_SVC_STATS);
                        char l1[17], l2[17];
                        snprintf(l1, sizeof(l1), "Cooks:%ld", gStats.cook_count);
                        snprintf(l2, sizeof(l2), "B=Next A=Back");
                        lcd_print2(l1, l2);
                    } else if (strcmp(selbuf, "6") == 0) {
                        st = ST_SVC_RESET_CONFIRM;
                        show_image(IMG_SVC_RESET);
                        lcd_print2("Factory Reset?", "B=Yes A=No");
                    } else {
                        beep_error();
                        lcd_print2("Invalid choice", "Use 1-6 / 1234");
                        usleep(700000);
                        show_image(IMG_SVC_MENU);
                        lcd_print2("Service Menu", "1-6 then B");
                    }
                    buf_clear(selbuf, &sellen);
                    continue;
                }
                if (st == ST_SVC_DOOR_TEST) {
                    gDoorAnim.oneshot_done = 0;
                    anim_start(&gDoorAnim, door_frames, DOOR_N, +1, DOOR_FRAME_MS);
                    while (!gDoorAnim.oneshot_done) { anim_tick(&gDoorAnim); usleep(20000); }
                    usleep(300000);
                    gDoorAnim.oneshot_done = 0;
                    anim_start(&gDoorAnim, door_frames, DOOR_N, -1, DOOR_FRAME_MS);
                    while (!gDoorAnim.oneshot_done) { anim_tick(&gDoorAnim); usleep(20000); }
                    beep_finish();
                    show_image(IMG_SVC_DOOR_TEST);
                    lcd_print2("Door Test", "B=Run A=Back");
                    continue;
                }
                if (st == ST_SVC_MOTOR_TEST) {
                    if (svc_motor_cycles_buf_len == 0) {
                        beep_error();
                        lcd_print2("No cycles", "Type 1-15");
                        usleep(700000);
                        show_image(IMG_SVC_MOTOR_TEST);
                        lcd_print2("Motor cyc 1-15", "B=Run A=Back");
                        continue;
                    }
                    int cycles = atoi(svc_motor_cycles_buf);
                    if (cycles < 1 || cycles > 15) {
                        beep_error();
                        lcd_print2("Cycles 1-15", "Try again");
                        usleep(700000);
                    } else {
                        lcd_print2("Motor test", "Running...");
                        run_motor_test_cycles(cycles);
                        beep_finish();
                    }
                    buf_clear(svc_motor_cycles_buf, &svc_motor_cycles_buf_len);
                    show_image(IMG_SVC_MOTOR_TEST);
                    lcd_print2("Motor cyc 1-15", "B=Run A=Back");
                    continue;
                }
                if (st == ST_SVC_LCD_TEST) {
                    /* re-show test pattern (already shown on entry) */
                    lcd_print2("ABCDEFGHIJKLMNO", "1234567890");
                    continue;
                }
                if (st == ST_SVC_STATS) {
                    svc_stats_page = (svc_stats_page + 1) % 4;
                    char l1[17], l2[17];
                    if (svc_stats_page == 0) {
                        snprintf(l1, sizeof(l1), "Cooks:%ld", gStats.cook_count);
                    } else if (svc_stats_page == 1) {
                        snprintf(l1, sizeof(l1), "DoorOpens:%ld", gStats.door_opens);
                    } else if (svc_stats_page == 2) {
                        snprintf(l1, sizeof(l1), "Errors:%ld", gStats.errors);
                    } else {
                        float hrs = gStats.total_cook_seconds / 3600.0f;
                        snprintf(l1, sizeof(l1), "Hours:%.2f", hrs);
                    }
                    snprintf(l2, sizeof(l2), "B=Next A=Back");
                    lcd_print2(l1, l2);
                    continue;
                }
                if (st == ST_SVC_RESET_CONFIRM) {
                    gLastUsed.valid = 0;
                    gStats.cook_count = 0; gStats.door_opens = 0;
                    gStats.errors = 0; gStats.total_cook_seconds = 0;
                    beep_finish();
                    lcd_print2("Factory Reset", "Complete");
                    usleep(1000000);
                    st = ST_SVC_MENU;
                    show_image(IMG_SVC_MENU);
                    lcd_print2("Service Menu", "1-6 then B");
                    continue;
                }
                continue;
            }

            /* ===== NORMAL MODE ENTER ===== */
            switch (st) {
                case ST_HOME: {
                    if (sellen == 0) {
                        beep_error();
                        lcd_print2("No selection", "Pick 1-6");
                        usleep(700000);
                        lcd_print2("Smart Microwave", "1-6 then B");
                        break;
                    }
                    if (strcmp(selbuf, "1234") == 0) {
                        buf_clear(selbuf, &sellen);
                        show_image(IMG_HOME);
                        lcd_print2("Flip SA5 DIP", "Press any key");
                        usleep(120000);
                        set_port_mapping(1);
                        st = ST_SVC_GATE;
                        svc_gate_deadline = now_ms() + 8000;
                        break;
                    }
                    int choice = atoi(selbuf);
                    buf_clear(selbuf, &sellen);
                    if (choice == 1) {
                        st = ST_COOK_TIME;
                        buf_clear(timebuf, &timelen);
                        show_image(IMG_COOK);
                        lcd_print2("Enter time", "MMSS then B");
                    } else if (choice == 2) {
                        st = ST_REHEAT_SELECT;
                        pending_food_idx = -1;
                        show_image(IMG_REHEAT);
                        lcd_print2("1 Rice 2 Pizza", "3 Soup 4 Noodle");
                    } else if (choice == 3) {
                        st = ST_DEFROST_SELECT;
                        pending_food_idx = -1;
                        show_image(IMG_DEFROST);
                        lcd_print2("1 Chick 2 Fish", "3 Beef, B=OK");
                    } else if (choice == 4) {
                        st = ST_BEVERAGE_SELECT;
                        pending_food_idx = -1;
                        show_image(IMG_BEVERAGE);
                        lcd_print2("1 Coffee 2 Tea", "3 Milk, B=OK");
                    } else if (choice == 5) {
                        st = ST_POPCORN_CONFIRM;
                        show_image(IMG_POPCORN);
                        lcd_print2("Popcorn", "B=Start A=Back");
                    } else if (choice == 6) {
                        if (!gLastUsed.valid) {
                            beep_error();
                            lcd_print2("No history yet", "");
                            usleep(1000000);
                            lcd_print2("Smart Microwave", "1-6 then B");
                        } else {
                            st = ST_LASTUSED_CONFIRM;
                            char l1[17], l2[17]; char mmss[12];
                            format_mmss(gLastUsed.time_sec, mmss);
                            snprintf(l1, sizeof(l1), "%s %s", gLastUsed.mode_name, mmss);
                            snprintf(l2, sizeof(l2), "Repeat? B=Y A=N");
                            show_image(IMG_LASTUSED);
                            lcd_print2(l1, l2);
                        }
                    } else {
                        beep_error();
                        lcd_print2("Invalid Selection", "");
                        usleep(1000000);
                        lcd_print2("Smart Microwave", "1-6 then B");
                    }
                    break;
                }

                case ST_COOK_TIME: {
                    int secs;
                    if (!parse_cook_time(timebuf, &secs)) {
                        beep_error();
                        lcd_print2("Invalid Time", "MMSS, max 60:00");
                        usleep(1000000);
                        buf_clear(timebuf, &timelen);
                        char l1[17]; snprintf(l1, sizeof(l1), "Time:");
                        lcd_print2(l1, "MMSS then B");
                        break;
                    }
                    pending_time_sec = secs;
                    st = ST_COOK_POWER;
                    pending_power = 0;
                    lcd_print2("Power? 1-3", "1Hi 2Med 3Lo,B");
                    break;
                }

                case ST_COOK_POWER: {
                    if (pending_power == 0) {
                        beep_error();
                        lcd_print2("Pick power 1-3", "then B");
                        usleep(700000);
                        break;
                    }
                    strncpy(pending_mode_name, "Cook", sizeof(pending_mode_name));
                    st = ST_DOOR_CHECK;
                    show_image(door_open ? IMG_DOOR_OPEN : IMG_DOOR_CLOSED);
                    lcd_print2(door_open ? "Door Open" : "Door Closed?",
                               door_open ? "Close Door" : "B=Start");
                    break;
                }

                case ST_REHEAT_SELECT: {
                    if (pending_food_idx < 0) {
                        beep_error();
                        lcd_print2("Pick 1-4 first", "");
                        usleep(700000);
                        break;
                    }
                    pending_time_sec = reheat_items[pending_food_idx].time_sec;
                    pending_power = reheat_items[pending_food_idx].power;
                    snprintf(pending_mode_name, sizeof(pending_mode_name), "%s", reheat_items[pending_food_idx].name);
                    st = ST_DOOR_CHECK;
                    show_image(door_open ? IMG_DOOR_OPEN : IMG_DOOR_CLOSED);
                    lcd_print2(door_open ? "Door Open" : "Door Closed?",
                               door_open ? "Close Door" : "B=Start");
                    break;
                }

                case ST_DEFROST_SELECT: {
                    if (pending_food_idx < 0) {
                        beep_error();
                        lcd_print2("Pick 1-3 first", "");
                        usleep(700000);
                        break;
                    }
                    st = ST_DEFROST_WEIGHT;
                    buf_clear(timebuf, &timelen);
                    lcd_print2("Weight (g):", "then B");
                    break;
                }

                case ST_DEFROST_WEIGHT: {
                    if (timelen == 0) {
                        beep_error();
                        lcd_print2("No weight", "Type grams");
                        usleep(700000);
                        break;
                    }
                    int grams = atoi(timebuf);
                    if (grams < 50 || grams > 5000) {
                        beep_error();
                        lcd_print2("Weight 50-5000g", "Try again");
                        usleep(1000000);
                        buf_clear(timebuf, &timelen);
                        lcd_print2("Weight (g):", "then B");
                        break;
                    }
                    pending_time_sec = defrost_time_from_weight(grams);
                    pending_power = 3; /* Defrost always uses Low power - assumption */
                    snprintf(pending_mode_name, sizeof(pending_mode_name), "Defrost %s",
                             defrost_items[pending_food_idx].name);
                    st = ST_DOOR_CHECK;
                    show_image(door_open ? IMG_DOOR_OPEN : IMG_DOOR_CLOSED);
                    lcd_print2(door_open ? "Door Open" : "Door Closed?",
                               door_open ? "Close Door" : "B=Start");
                    break;
                }

                case ST_BEVERAGE_SELECT: {
                    if (pending_food_idx < 0) {
                        beep_error();
                        lcd_print2("Pick 1-3 first", "");
                        usleep(700000);
                        break;
                    }
                    pending_time_sec = beverage_items[pending_food_idx].time_sec;
                    pending_power = beverage_items[pending_food_idx].power;
                    snprintf(pending_mode_name, sizeof(pending_mode_name), "%s", beverage_items[pending_food_idx].name);
                    st = ST_DOOR_CHECK;
                    show_image(door_open ? IMG_DOOR_OPEN : IMG_DOOR_CLOSED);
                    lcd_print2(door_open ? "Door Open" : "Door Closed?",
                               door_open ? "Close Door" : "B=Start");
                    break;
                }

                case ST_POPCORN_CONFIRM: {
                    pending_time_sec = POPCORN_TIME_SEC;
                    pending_power = POPCORN_POWER;
                    strncpy(pending_mode_name, "Popcorn", sizeof(pending_mode_name));
                    st = ST_DOOR_CHECK;
                    show_image(door_open ? IMG_DOOR_OPEN : IMG_DOOR_CLOSED);
                    lcd_print2(door_open ? "Door Open" : "Door Closed?",
                               door_open ? "Close Door" : "B=Start");
                    break;
                }

                case ST_LASTUSED_CONFIRM: {
                    pending_time_sec = gLastUsed.time_sec;
                    pending_power = gLastUsed.power;
                    snprintf(pending_mode_name, sizeof(pending_mode_name), "%s", gLastUsed.mode_name);
                    st = ST_DOOR_CHECK;
                    show_image(door_open ? IMG_DOOR_OPEN : IMG_DOOR_CLOSED);
                    lcd_print2(door_open ? "Door Open" : "Door Closed?",
                               door_open ? "Close Door" : "B=Start");
                    break;
                }

                case ST_DOOR_CHECK: {
                    if (door_open) {
                        beep_error();
                        lcd_print2("Door Open", "Close Door");
                        break;
                    }
                    /* Door closed -> start cooking */
                    remaining_ms = pending_time_sec * 1000;
                    last_shown_sec = -1;
                    last_tick_ms = now_ms();

                    gLastUsed.valid = 1;
                    snprintf(gLastUsed.mode_name, sizeof(gLastUsed.mode_name), "%s", pending_mode_name);
                    gLastUsed.time_sec = pending_time_sec;
                    gLastUsed.power = pending_power;

                    st = ST_COOKING;
                    idle_stop();
                    beep_start();
                    anim_start_loop(&gCookAnim, cook_frames, COOK_N, 800);
                    lcd_print2("Cooking", "");
                    seg_blank();
                    break;
                }

                default:
                    beep_error();
                    break;
            }
            idle_reset();
            continue;
        }

        /* anything else falls through */
        beep_error();
    }
}

/* ===== LCD low-level ===== */
static void initlcd(void)
{
    usleep(20000);
    lcd_writecmd(0x30);
    usleep(20000);
    lcd_writecmd(0x30);
    usleep(20000);
    lcd_writecmd(0x30);

    lcd_writecmd(0x02);
    lcd_writecmd(0x28);
    lcd_writecmd(0x01);
    lcd_writecmd(0x0c);
    lcd_writecmd(0x06);
    lcd_writecmd(0x80);
}

static void lcd_writecmd(char cmd)
{
    char data;
    data = (cmd & 0xf0);
    CM3_outport(gLcdPort, data | 0x04);
    usleep(10);
    CM3_outport(gLcdPort, data);
    usleep(200);

    data = (cmd & 0x0f) << 4;
    CM3_outport(gLcdPort, data | 0x04);
    usleep(10);
    CM3_outport(gLcdPort, data);
    usleep(2000);
}

static void LCDprint(char *sptr)
{
    while (*sptr) lcddata(*sptr++);
}

static void lcddata(unsigned char cmd)
{
    char data;
    data = (cmd & 0xf0);
    CM3_outport(gLcdPort, data | 0x05);
    usleep(10);
    CM3_outport(gLcdPort, data);
    usleep(200);

    data = (cmd & 0x0f) << 4;
    CM3_outport(gLcdPort, data | 0x05);
    usleep(10);
    CM3_outport(gLcdPort, data);
    usleep(2000);
}
