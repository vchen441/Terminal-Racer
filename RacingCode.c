// Inputs:  2x PmodALS (steering), PmodMAXSONAR (cover bonus multiplier)
// Outputs: Serial terminal (ASCII road), PmodOLED (score + high score)
// Start:   Press BTN0 to start (fallback 's' on keyboard)
// Restart: Press BTN0 after crash (fallback 'r' on keyboard)
// Highscore: Stored in RAM (persists across restarts; resets on power-cycle)
//
// EVENTS:
// - Straight
// - Left turns (turn wall sweeps down; must hit wall once during the event)
// - Right turns (turn wall sweeps down; must hit wall once during the event)
// - Lane closures (close up to 3 lanes) that SWEEP DOWN (not instant) and DO NOT immediately disappear (they "open" via another downward sweep).
//
// IMPORTANT GAME RULES:
// - If you steer into a closed lane '#' at the BOTTOM row, you crash immediately.
// - If a lane closure sweeps down onto your lane at the bottom row, you crash.
// - Obstacles spawn at the top (row 0).
// - Constant-speed game (no speed variable).
// - "Streak multiplier" increases every second you do NOT change lanes.
// - Time limit: 60 seconds (crash when reached).
// - Covering MAXSONAR adds an additional multiplier.

#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include "xparameters.h"
#include "xil_printf.h"
#include "sleep.h"
#include "xgpio.h"

#include "PmodALS.h"
#include "PmodOLED.h"
#include "PmodMAXSONAR.h"

#ifdef XPAR_XUARTPS_0_BASEADDR
#include "xuartps_hw.h"
#endif

// addresses
#define ALS_BASEADDR          XPAR_PMODALS_0_AXI_LITE_SPI_BASEADDR
#define ALS_BASEADDR2         XPAR_PMODALS_1_AXI_LITE_SPI_BASEADDR
#define OLED_GPIO_BASEADDR    XPAR_PMODOLED_0_AXI_LITE_GPIO_BASEADDR
#define OLED_SPI_BASEADDR     XPAR_PMODOLED_0_AXI_LITE_SPI_BASEADDR
#define MAXSONAR_BASEADDR     XPAR_PMODMAXSONAR_0_AXI_LITE_GPIO_BASEADDR

#define CLK_FREQ              100000000U

// tunables
#define TICK_US               200000      // 200ms per game tick
#define TICKS_PER_SEC         5

// timelimit
#define TIME_LIMIT_SEC        60
#define TIME_LIMIT_TICKS      (TIME_LIMIT_SEC * TICKS_PER_SEC)

#define LANES                 5
#define ROAD_H                12

// steering
#define ALS_DEADBAND          8
#define ALS_STEER_COOLDOWN    1

// constant obstacle movement probability (per tick)
#define OBSTACLE_MOVE_PROB    65   // 

// MAXSONAR "covered" detection
#define SONAR_COVER_IN        10    // value to be registered as "covered"

// scoring
#define BASE_POINTS_PER_SEC   10   // points per second before multipliers

// multiplier:
// starts at 1.0x and increases by +0.1x per second without lane change.
#define STREAK_STEP_TENTHS    1    // +0.1x per second
#define STREAK_MAX_TENTHS     50   // caps at +5.0x (so max 6.0x total)

// conar cover multiplier: 1.0x normally, 1.5x when covered
#define SONAR_MULT_TENTHS     15   // 1.5x when covered

// event tuning
#define SEG_TICKS            16      // all segments are equal length

// turn “aggression”
#define TURN_STEP_TENTHS      2      // 0.2 lanes per tick
#define TURN_MAX_SHIFT_TENTHS 10     // max shift = 1.0 lane

// lane closure tuning (up to 3 lanes closed)
#define LANE_CLOSE_MIN        1
#define LANE_CLOSE_MAX        3

#define EVENT_TICKS          (SEG_TICKS + ROAD_H) 

typedef enum {
    EV_STRAIGHT = 0,
    EV_LEFT_TURN,
    EV_RIGHT_TURN,
    EV_LANES_DISAPPEAR
} EventType;

typedef enum {
    CLS_NONE = 0,
    CLS_CLOSING,   // closed region grows downward (top becomes closed first)
    CLS_OPENING    // closed region shrinks downward (top becomes open first)
} ClosureState;

typedef struct {
    EventType type;
    int ticks_left;
} Segment;

typedef struct {
    int car_lane;     // 0..LANES-1
    int obs_lane;     // 0..LANES-1
    int obs_y;        // 0..ROAD_H-1 or ROAD_H=inactivate
    int ticks;        // time ticks (each tick is 200ms)
    int score_tenths; // score in 0.1-point units
    int crashed;      // 0/1
    int steer_cd;     // steering cooldown

    // lane-change streak tracking
    int ticks_since_lane_change;

    // road state
    int center_shift_tenths;   // -10..+10
    int turn_wall_hit;         // 1 once wall hit during turn event

    // turn sweep
    int turn_front_y;          // 0..ROAD_H
    unsigned turn_mask;        // mask for swept turn region

    Segment seg;

    ClosureState closure_state;
    int lane_close_count;      // 1..3 during lane close event
    int closure_front_y;       // sweep boundary (moves down)
    unsigned mask_normal;      // open lanes without closure
    unsigned mask_closed;      // open lanes with closure applied
} Game;

// pmod
static PmodALS alsL;
static PmodALS alsR;
static PmodOLED oled;
static PmodMAXSONAR sonar;

// highscore (ram)
static int g_high_tenths = 0;

// util
static int clampi(int v, int lo, int hi) {
    if (v < lo) return lo;
    if (v > hi) return hi;
    return v;
}

static int is_lane_active(unsigned mask, int lane) {
    return (int)((mask >> lane) & 1U);
}

static int count_active(unsigned mask) {
    int c = 0;
    for (int i = 0; i < LANES; i++) c += (int)((mask >> i) & 1U);
    return c;
}

static int random_active_lane(unsigned mask) {
    int active[LANES];
    int n = 0;
    for (int i = 0; i < LANES; i++) {
        if (is_lane_active(mask, i)) active[n++] = i;
    }
    if (n == 0) return -1;
    return active[rand() % n];
}

static const char* ev_name(EventType t) {
    switch (t) {
        case EV_STRAIGHT:        return "STRAIGHT";
        case EV_LEFT_TURN:       return "LEFT TURN";
        case EV_RIGHT_TURN:      return "RIGHT TURN";
        case EV_LANES_DISAPPEAR: return "LANES CLOSE";
        default:                 return "?";
    }
}

// build “road” mask of width LANES, shifted by center_shift_tenths,
static unsigned build_active_mask(int center_shift_tenths, int closed_lanes) {
    int open = LANES - closed_lanes;
    if (open < 1) open = 1;
    if (open > LANES) open = LANES;

    int shift_lanes = (center_shift_tenths >= 0) ? (center_shift_tenths / 10)
        : -((-center_shift_tenths) / 10);
    int center = (LANES / 2) + shift_lanes;
    center = clampi(center, 0, LANES - 1);

    int start = center - (open / 2);
    start = clampi(start, 0, LANES - open);

    unsigned mask = 0;
    for (int i = 0; i < open; i++) mask |= (1U << (start + i));
    return mask;
}

// row-dependent active mask.
static unsigned active_mask_at_row(const Game *g, int y) {
    // turn sweep logic (top becomes turn wall first, moves downward)
    if (g->seg.type == EV_LEFT_TURN || g->seg.type == EV_RIGHT_TURN) {
        if (y < g->turn_front_y) return g->turn_mask;
        return g->mask_normal;
    }

    // lane close sweep logic
    if (g->seg.type == EV_LANES_DISAPPEAR) {
        if (g->closure_state == CLS_CLOSING) {
            if (y < g->closure_front_y) return g->mask_closed;
            return g->mask_normal;
        } else if (g->closure_state == CLS_OPENING) {
            if (y < g->closure_front_y) return g->mask_normal;
            return g->mask_closed;
        }
    }

    return g->mask_normal;
}

// button (BTN0)
#if defined(XPAR_AXI_GPIO_0_DEVICE_ID)
#define BTN_GPIO_DEVICE_ID XPAR_AXI_GPIO_0_DEVICE_ID
#elif defined(XPAR_GPIO_0_DEVICE_ID)
#define BTN_GPIO_DEVICE_ID XPAR_GPIO_0_DEVICE_ID
#endif

#define BTN_GPIO_CHANNEL   1
#define BTN0_MASK          0x1U

static XGpio g_btn_gpio;
static int   g_btn_gpio_ok = 0;

static void btn_gpio_init(void) {
#ifdef BTN_GPIO_DEVICE_ID
    if (XGpio_Initialize(&g_btn_gpio, BTN_GPIO_DEVICE_ID) == XST_SUCCESS) {
        XGpio_SetDataDirection(&g_btn_gpio, BTN_GPIO_CHANNEL, 0xFFFFFFFFU);
        g_btn_gpio_ok = 1;
    }
#endif
}

static int btn0_is_pressed(void) {
    if (!g_btn_gpio_ok) return 0;
    u32 v = XGpio_DiscreteRead(&g_btn_gpio, BTN_GPIO_CHANNEL);
    return (v & BTN0_MASK) ? 1 : 0;
}

static void wait_for_btn0_press(void) {
    while (btn0_is_pressed()) usleep(20000);
    while (!btn0_is_pressed()) usleep(20000);
    usleep(30000);
    while (btn0_is_pressed()) usleep(20000);
    usleep(30000);
}

// UART
static int try_get_char_nonblocking(void) {
#ifdef XPAR_XUARTPS_0_BASEADDR
    if (XUartPs_IsReceiveData(XPAR_XUARTPS_0_BASEADDR)) {
        return (int)XUartPs_RecvByte(XPAR_XUARTPS_0_BASEADDR);
    }
#endif
    return -1;
}

// OLED
static void oled_show_status(char *l0, char *l1, char *l2, char *l3) {
    OLED_Clear(&oled);
    OLED_SetCursor(&oled, 0, 0); OLED_PutString(&oled, l0);
    OLED_SetCursor(&oled, 0, 1); OLED_PutString(&oled, l1);
    OLED_SetCursor(&oled, 0, 2); OLED_PutString(&oled, l2);
    OLED_SetCursor(&oled, 0, 3); OLED_PutString(&oled, l3);
    OLED_Update(&oled);
}

static void oled_show_score(int score_tenths, int high_tenths, int streak_mult_tenths, int sonar_mult_tenths, const char *ev) {
    char l0[20], l1[20], l2[20], l3[20];

    snprintf(l0, sizeof(l0), "Score:%d.%dpt", score_tenths/10, score_tenths%10);
    snprintf(l1, sizeof(l1), "High :%d.%dpt", high_tenths/10, high_tenths%10);
    snprintf(l2, sizeof(l2), "Mult:%d.%dx", streak_mult_tenths/10, streak_mult_tenths%10);
    snprintf(l3, sizeof(l3), "S:%d.%d %.10s", sonar_mult_tenths/10, sonar_mult_tenths%10, ev);

    oled_show_status(l0, l1, l2, l3);
}

// start/restart screens
static void wait_for_start(void) {
    char l0[20], l1[20], l2[20], l3[20];

    snprintf(l0, sizeof(l0), "Zybo RACER");
    snprintf(l1, sizeof(l1), "High:%d.%dpt", g_high_tenths/10, g_high_tenths%10);
    snprintf(l2, sizeof(l2), "Press BTN0");
    snprintf(l3, sizeof(l3), "to start");

    oled_show_status(l0, l1, l2, l3);

    xil_printf("\n=== Zybo RACER ===\r\n");
    xil_printf("Press BTN0 to start\r\n");

    if (g_btn_gpio_ok) {
        wait_for_btn0_press();
    } else {
        while (1) {
            int c = try_get_char_nonblocking();
            if (c == 's' || c == 'S') break;
            usleep(20000);
        }
    }

    OLED_Clear(&oled);
    OLED_Update(&oled);
}

static void wait_for_restart_prompt(void) {
    char l0[20], l1[20], l2[20], l3[20];

    snprintf(l0, sizeof(l0), "CRASH!");
    snprintf(l1, sizeof(l1), "High:%d.%dpt", g_high_tenths/10, g_high_tenths%10);
    snprintf(l2, sizeof(l2), "Press BTN0");
    snprintf(l3, sizeof(l3), "to restart");

    oled_show_status(l0, l1, l2, l3);

    xil_printf("\n=== Press BTN0 to restart ===\r\n");

    if (g_btn_gpio_ok) {
        wait_for_btn0_press();
    } else {
        while (1) {
            int c = try_get_char_nonblocking();
            if (c == 'r' || c == 'R') break;
            usleep(20000);
        }
    }
}

// displaying to serial monitor
static void print_road(const Game *g, int rawL, int rawR, int dist_in, int covered,
                       int streak_mult_tenths, int sonar_mult_tenths) {
    xil_printf("\033[2J\033[H");

    int tenths_sec = g->ticks * 2; // 200ms per tick
    xil_printf("Zybo Racer | Time:%d.%ds/%ds | Score:%d.%dpt | Mult:%d.%dx | Sonar:%s (%din)\r\n",
               tenths_sec/10, tenths_sec%10, TIME_LIMIT_SEC,
               g->score_tenths/10, g->score_tenths%10,
               streak_mult_tenths/10, streak_mult_tenths%10,
               covered ? "COVER" : " open",
               dist_in);

    unsigned bottommask = active_mask_at_row(g, ROAD_H - 1);
    xil_printf("Event:%-11s | Open(bottom): %d/%d | ALS1:%3d ALS2:%3d diff:%2d | BMult:%d.%dx\r\n",
               ev_name(g->seg.type),
               count_active(bottommask), LANES,
               rawL, rawR, (rawL - rawR),
               sonar_mult_tenths/10, sonar_mult_tenths%10);

    xil_printf("Legend: A=car  X=obstacle  #=closed lane  !=turn wall\r\n\r\n");
    xil_printf("Rules: \r\n");
    xil_printf("1. Avoid the obstacles and closed lanes; '!' are safe, be in lane to survive\r\n");
    xil_printf("2. Steer with the ALS's;steering less often = more points! \r\n");
    xil_printf("3. Drink non-alcoholic beer by covering MAXSONAR; more points while drinking!\r\n");
    xil_printf("4. Each round is 60s, try to get as many points as you can! \r\n");

    for (int y = 0; y < ROAD_H; y++) {
        unsigned rowmask = active_mask_at_row(g, y);

        xil_printf("|");
        for (int lane = 0; lane < LANES; lane++) {
            char cell;

            int turn_active_on_row =
                (g->seg.type == EV_LEFT_TURN || g->seg.type == EV_RIGHT_TURN) && (y < g->turn_front_y);

            if (turn_active_on_row && g->seg.type == EV_LEFT_TURN && lane == 0) {
                cell = '!';
            } else if (turn_active_on_row && g->seg.type == EV_RIGHT_TURN && lane == (LANES - 1)) {
                cell = '!';
            } else if (!is_lane_active(rowmask, lane)) {
                cell = '#';
            } else {
                cell = (y % 2 == 0) ? '.' : ' ';
            }

            if (y == g->obs_y && lane == g->obs_lane) cell = 'X';
            if (y == ROAD_H - 1 && lane == g->car_lane) cell = 'A';

            xil_printf(" %c |", cell);
        }
        xil_printf("\r\n");
    }

    if (g->crashed) {
        xil_printf("\r\nCRASH! Final Score:%d.%dpt\r\n", g->score_tenths/10, g->score_tenths%10);
    }
}

// spawning obstacles
static void spawn_obstacle(Game *g) {
    unsigned topmask = active_mask_at_row(g, 0);
    g->obs_lane = random_active_lane(topmask);
    if (g->obs_lane < 0) g->obs_lane = LANES / 2;
    g->obs_y = 0;
}

static int in_turn(const Game *g) {
    return (g->seg.type == EV_LEFT_TURN || g->seg.type == EV_RIGHT_TURN);
}

// event selection
static void new_segment(Game *g) {
    int r = rand() % 100;
    EventType t;

    if (r < 30) t = EV_STRAIGHT;
    else if (r < 45) t = EV_LEFT_TURN;
    else if (r < 60) t = EV_RIGHT_TURN;
    else t = EV_LANES_DISAPPEAR;

    g->seg.type = t;

    g->seg.ticks_left = EVENT_TICKS;

    g->turn_wall_hit = 0;
    g->turn_front_y = 0;
    g->turn_mask = 0U;

    if (t == EV_LEFT_TURN) {
        g->turn_mask = (1U << 0);
    } else if (t == EV_RIGHT_TURN) {
        g->turn_mask = (1U << (LANES - 1));
    }

    if (t == EV_LANES_DISAPPEAR) {
        g->lane_close_count = LANE_CLOSE_MIN + (rand() % (LANE_CLOSE_MAX - LANE_CLOSE_MIN + 1));
        g->closure_state = CLS_CLOSING;
        g->closure_front_y = 0;
    } else {
        g->lane_close_count = 0;
        g->closure_state = CLS_NONE;
        g->closure_front_y = 0;
    }
}


// apply events
static void apply_segment(Game *g) {
    int elapsed = EVENT_TICKS - g->seg.ticks_left;
    if (elapsed < 0) elapsed = 0;
    if (elapsed > EVENT_TICKS) elapsed = EVENT_TICKS;

    switch (g->seg.type) {
        case EV_STRAIGHT:
            if (g->center_shift_tenths > 0) g->center_shift_tenths -= TURN_STEP_TENTHS;
            if (g->center_shift_tenths < 0) g->center_shift_tenths += TURN_STEP_TENTHS;
            break;

        case EV_LEFT_TURN:
            g->center_shift_tenths -= TURN_STEP_TENTHS;
            g->center_shift_tenths = clampi(g->center_shift_tenths, -TURN_MAX_SHIFT_TENTHS, TURN_MAX_SHIFT_TENTHS);
            break;

        case EV_RIGHT_TURN:
            g->center_shift_tenths += TURN_STEP_TENTHS;
            g->center_shift_tenths = clampi(g->center_shift_tenths, -TURN_MAX_SHIFT_TENTHS, TURN_MAX_SHIFT_TENTHS);
            break;

        case EV_LANES_DISAPPEAR:
        default:
            break;
    }

    // normal road mask always based on shift
    g->mask_normal = build_active_mask(g->center_shift_tenths, 0);

    // closed mask only meaningful during lane closure
    int closed = 0;
    if (g->seg.type == EV_LANES_DISAPPEAR) closed = g->lane_close_count;
    g->mask_closed = build_active_mask(g->center_shift_tenths, closed);

    // turn sweep: spread across full ticks
    if (g->seg.type == EV_LEFT_TURN || g->seg.type == EV_RIGHT_TURN) {
        int front = (elapsed * ROAD_H) / EVENT_TICKS;   // 0..ROAD_H
        if (front > ROAD_H) front = ROAD_H;
        g->turn_front_y = front;
    }

    // lane closure: close for SEG_TICKS, then open for ROAD_H
    if (g->seg.type == EV_LANES_DISAPPEAR) {
        if (elapsed < SEG_TICKS) {
            // closing phase (duration = SEG_TICKS)
            g->closure_state = CLS_CLOSING;
            int front = (elapsed * ROAD_H) / SEG_TICKS;  
            if (front > ROAD_H) front = ROAD_H;
            g->closure_front_y = front;
        } else {
            // opening phase (duration = ROAD_H)
            g->closure_state = CLS_OPENING;
            int open_elapsed = elapsed - SEG_TICKS;       // 0..ROAD_H
            if (open_elapsed > ROAD_H) open_elapsed = ROAD_H;
            g->closure_front_y = open_elapsed;
        }
    }

    // one tick has passed
    g->seg.ticks_left--;

    // event ending
    if (g->seg.ticks_left <= 0) {
        // turn rule: must hit wall once to continue playing
        if ((g->seg.type == EV_LEFT_TURN || g->seg.type == EV_RIGHT_TURN) && !g->turn_wall_hit) {
            g->crashed = 1;
            return;
        }

        // cleanup
        if (g->seg.type == EV_LANES_DISAPPEAR) {
            g->closure_state = CLS_NONE;
            g->lane_close_count = 0;
            g->closure_front_y = 0;
        }

        new_segment(g);
    }
}


// one game
static void run_one_game(void) {
    Game g;

    g.car_lane = LANES / 2;
    g.ticks = 0;
    g.score_tenths = 0;
    g.crashed = 0;
    g.steer_cd = 0;

    g.ticks_since_lane_change = 0;

    g.center_shift_tenths = 0;

    g.turn_front_y = 0;
    g.turn_mask = 0U;

    g.closure_state = CLS_NONE;
    g.lane_close_count = 0;
    g.closure_front_y = 0;
    g.mask_normal = (1U << LANES) - 1U;
    g.mask_closed = (1U << LANES) - 1U;

    new_segment(&g);

    // If in a turn, keep obstacle inactive until turns end.
    g.obs_y = ROAD_H;
    g.obs_lane = LANES / 2;

    if (!in_turn(&g)) {
        spawn_obstacle(&g);
    }

    while (!g.crashed) {
        apply_segment(&g);

        int raw1 = (int)ALS_read(&alsL);
        int raw2 = (int)ALS_read(&alsR);
        int dist_in = MAXSONAR_getDistance(&sonar);

        int diff = raw1 - raw2;
        if (g.steer_cd > 0) g.steer_cd--;

        // steering (*lane changes reset streak timer)
        if (g.steer_cd == 0) {
            int new_lane = g.car_lane;

            if (diff > ALS_DEADBAND) {
                new_lane = g.car_lane - 1;
                g.steer_cd = ALS_STEER_COOLDOWN;
            } else if (diff < -ALS_DEADBAND) {
                new_lane = g.car_lane + 1;
                g.steer_cd = ALS_STEER_COOLDOWN;
            }

            new_lane = clampi(new_lane, 0, LANES - 1);

            if (new_lane != g.car_lane) {
                g.car_lane = new_lane;
                g.ticks_since_lane_change = 0; //resetting streak clock

                //steering into closed lane = crash
                unsigned bm = active_mask_at_row(&g, ROAD_H - 1);
                if (!is_lane_active(bm, g.car_lane)) {
                    g.crashed = 1;
                }
            }
        }

        // crash if lane becomes closed under you
        // turn wall hit requirement (can hit at any time during sweep)
        if (!g.crashed && (g.seg.type == EV_LEFT_TURN || g.seg.type == EV_RIGHT_TURN)) {
            if (g.seg.type == EV_LEFT_TURN  && g.car_lane == 0)          g.turn_wall_hit = 1;
            if (g.seg.type == EV_RIGHT_TURN && g.car_lane == (LANES - 1)) g.turn_wall_hit = 1;
        }

        // turn wall hit requirement (only once sweep fully present)
        if (!g.crashed && g.turn_front_y >= ROAD_H) {
            if (g.seg.type == EV_LEFT_TURN  && g.car_lane == 0)          g.turn_wall_hit = 1;
            if (g.seg.type == EV_RIGHT_TURN && g.car_lane == (LANES - 1)) g.turn_wall_hit = 1;
        }

        // crash if sitting in a closed lane 
        if (!g.crashed) {
            // Check the bottom row (includes lane closures)
            unsigned bottom_mask = active_mask_at_row(&g, ROAD_H - 1);
            if (!is_lane_active(bottom_mask, g.car_lane)) {
                // turn walls are safe (!)
                int on_turn_wall = 0;
                if (g.seg.type == EV_LEFT_TURN && g.car_lane == 0) on_turn_wall = 1;
                if (g.seg.type == EV_RIGHT_TURN && g.car_lane == (LANES - 1)) on_turn_wall = 1;

                if (!on_turn_wall) {
                    g.crashed = 1;
                }
            }
        }

        // sonar covered multiplier
        int covered = (dist_in > 0 && dist_in <= SONAR_COVER_IN);

        // obstacle movement
        if (g.obs_y < ROAD_H) {
            if ((rand() % 100) < OBSTACLE_MOVE_PROB) g.obs_y++;
        }

        // respawn obstacle only when not in a turn
        if (g.obs_y >= ROAD_H) {
            if (!in_turn(&g)) {
                spawn_obstacle(&g);
            } else {
                g.obs_y = ROAD_H; // inactive during turns
            }
        }

        // crash on obstacle hit
        int car_y = ROAD_H - 1;
        if (!g.crashed && g.obs_y == car_y && g.obs_lane == g.car_lane) {
            unsigned bm = active_mask_at_row(&g, car_y);
            if (is_lane_active(bm, g.car_lane)) {
                g.crashed = 1;
            }
        }

        // time
        g.ticks += 1;
        g.ticks_since_lane_change += 1;

        if (g.ticks >= TIME_LIMIT_TICKS) {
            g.crashed = 1;
        }

        // multipliers
        int seconds_since_change = g.ticks_since_lane_change / TICKS_PER_SEC;

        // streak_mult = 1.0 + 0.1*secondssincelastchange
        int extra_tenths = seconds_since_change * STREAK_STEP_TENTHS;
        if (extra_tenths > STREAK_MAX_TENTHS) extra_tenths = STREAK_MAX_TENTHS;
        int streak_mult_tenths = 10 + extra_tenths; // 10 = 1.0x

        int sonar_mult_tenths = covered ? SONAR_MULT_TENTHS : 10;

        // points/sec in tenths = BASE_POINTS_PER_SEC * 10
        // per tick: divide by TICKS_PER_SEC
        // apply multipliers in tenths: (base * streak * sonar) / (10*10)
        int base_per_tick_tenths = (BASE_POINTS_PER_SEC * 10) / TICKS_PER_SEC;

        long long scaled = (long long)base_per_tick_tenths * (long long)streak_mult_tenths * (long long)sonar_mult_tenths;
        int delta = (int)((scaled + 50) / 100); // 100 because 10*10, +50 for rounding

        if (delta < 0) delta = 0;
        g.score_tenths += delta;

        if (g.score_tenths > g_high_tenths) g_high_tenths = g.score_tenths;

        // oled serial display
        oled_show_score(g.score_tenths, g_high_tenths, streak_mult_tenths, sonar_mult_tenths, ev_name(g.seg.type));
        print_road(&g, raw1, raw2, dist_in, covered, streak_mult_tenths, sonar_mult_tenths);

        usleep(TICK_US);
    }

    if (g.score_tenths > g_high_tenths) g_high_tenths = g.score_tenths;
    wait_for_restart_prompt();
}

// main
int main(void) {
    xil_printf("Zybo Racing Game (ALS steer, SONAR cover mult, OLED score)\r\n");

    btn_gpio_init();

    ALS_begin(&alsL, ALS_BASEADDR);
    ALS_begin(&alsR, ALS_BASEADDR2);

    OLED_Begin(&oled, OLED_GPIO_BASEADDR, OLED_SPI_BASEADDR, 0, 0);
    OLED_Clear(&oled);
    OLED_Update(&oled);

    MAXSONAR_begin(&sonar, MAXSONAR_BASEADDR, CLK_FREQ);

    srand(12345);

    wait_for_start();
    while (1) {
        run_one_game();
    }
    return 0;
}
