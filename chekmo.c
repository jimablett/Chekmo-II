/*
 * CHEKMO-II - Chess Program for PDP-8
 * Converted to ANSI C with WinBoard Protocol
 * Enhanced evaluation and king safety
 * Ported by Jim Ablett (May/June 2026)
 * Original Author: JOHN E. COMEAU (1976)
 * 
 * CHEKMO-II (DECUS 8-822) was created for PDP-8 computers by Digital 
 * Equipment Corporation (Maynard, MA) electrical engineer and industrial 
 * instructor John E. Comeau (1976)
 *
 */
 

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <signal.h>
#include <ctype.h>
#include <time.h>
#include <stdarg.h>
#include <setjmp.h>
#include <sys/time.h>
#ifdef _WIN32
#include <io.h>      /* for _isatty, _fileno */
#else
#include <unistd.h>  /* for isatty, fileno */
#endif

/* Compiler-specific inlining hints */
#if defined(__GNUC__) || defined(__clang__)
#define HOT_INLINE __attribute__((always_inline)) inline
#define LIKELY(x)   __builtin_expect(!!(x), 1)
#define UNLIKELY(x) __builtin_expect(!!(x), 0)
#else
#define HOT_INLINE inline
#define LIKELY(x)   (x)
#define UNLIKELY(x) (x)
#endif

/* Wall-clock helper: returns nanoseconds via gettimeofday */
static HOT_INLINE int64_t now_ns(void) {
    struct timeval tv;
    gettimeofday(&tv, NULL);
    return (int64_t)tv.tv_sec * 1000000000LL + (int64_t)tv.tv_usec * 1000LL;
}


/* ==================== TERMINAL CHECK ==================== */

static int is_stdin_terminal(void) {
#ifdef _WIN32
    return _isatty(_fileno(stdin));
#else
    return isatty(fileno(stdin));
#endif
}

/* ==================== CONSTANTS & DEFINITIONS ==================== */

#define WB_WHITE 0
#define WB_BLACK 1

#define BOARD_SIZE 64

#define KING_VAL   1500
#define QUEEN_VAL   900
#define ROOK_VAL    500
#define BISHOP_VAL  325
#define KNIGHT_VAL  300
#define PAWN_VAL    100

#define EMPTY       0
#define PAWN        1
#define KNIGHT      2
#define BISHOP      3
#define ROOK        4
#define QUEEN       5
#define KING        6

#define PDL_SIZE 16000
#define CHECKMATE_VALUE 30000
#define STALEMATE_VALUE 0
#define MAX_SCORE 32767
#define MAX_PLY 16
#define MATE_SCORE 28000

/* King safety enhancement constants */
#define SHIELD_FILES 3
#define MAX_SHIELD_RANK 3
#define NO_SHIELD_PENALTY 35
#define PARTIAL_SHIELD_PENALTY 15
#define WEAK_SHIELD_FILE_PENALTY 20
#define CASTLE_SHELTER_BONUS 40
#define OPEN_FILE_PENALTY 25
#define KNIGHT_PROXIMITY_PENALTY 18

/* Repetition detection - proper stack, depth = game ply + search ply */
#define REP_HISTORY_SIZE 256
static uint32_t pos_history[REP_HISTORY_SIZE];
static int history_ptr = 0;

/* WinBoard post/nopost */
static int wb_post_mode = 1;

/* Global killer moves persistence flag */
static int killers_initialized = 0;

/* ==================== GLOBAL VARIABLES ==================== */

static int board[BOARD_SIZE];
static int pdl1[PDL_SIZE];
static int pdl2[PDL_SIZE];
static int pdl1_ptr;
static int pdl2_ptr;


static int to_mak1;
static int to_mak2;

static int wpsw;
static int bpsw;
static int wking;
static int bking;
static int cking;

static int whose;
static int last_move;
static int ply;
static int depth;
static int bogus;
static int domap;

static int gncnt;
static int gnchek;
static int kngblk;
static int mobmod;
static int mob0, mob1;
static int qmvcnt;

static int gn1, gn2, gn3, gn4;
static int gnmsw, gnmdw;
static int cntr1;

static int stratg;
static int pw;
static int uval1;
static int cval1;
static int rval1;
static int comp;

static int cmsw;
static int smsw;

static int pcnt;
static int pval;
static int psqr;

static int whowhi;
static int whoblk;
static int blitz_mode;
static int console_think_ms = 5000;  /* default 5 seconds per move in console mode */

static int random_val;

static char input_buffer[256];
static int white_map[17];
static int black_map[17];
static int white_map_ptr;
static int black_map_ptr;

static int bestbl[MAX_PLY * 2 + 4];  // 36 entries
static int hiepms;

static int enprad, enpval, enpsqr, enpcnt;

static int halfmove_clock = 0;
static int in_quiesce = 0;
static int qply = 0;

#define SQR_RANK(s)  ((s) >> 3)
#define SQR_FILE(s)  ((s) & 7)
#define MAKE_SQ(r,c) (((r)<<3)|(c))

static int eg_cache = -1;
static int game_phase_cache = -1;

static int computer_side = WB_WHITE;
static int wb_force = 0;
static int game_over = 0;

static int wcastled = 0;
static int bcastled = 0;
static jmp_buf search_abort_jmp;
static int search_aborted = 0;

static int wb_time_cs = 0;
static int wb_otim_cs = 0;
static int wb_level_mps = 0;
static int wb_level_base_cs = 0;
static int wb_level_inc_cs = 0;
static int wb_move_num = 0;

static int64_t search_start_clk;
static int64_t search_limit_clk;
static int search_use_timer = 0;
static long search_nodes = 0;
static int base_depth = 3;  /* iterative-deepening depth for current iteration */

#define MAX_SEARCH_DEPTH 12

static int pv_msw[MAX_PLY][MAX_PLY];
static int pv_mdw[MAX_PLY][MAX_PLY];
static int pv_len[MAX_PLY];

static const int piece_value[] = {0, PAWN_VAL, KNIGHT_VAL, BISHOP_VAL, ROOK_VAL, QUEEN_VAL, KING_VAL};

#define KILLER_SLOTS 2
static int killer_msw[MAX_PLY][KILLER_SLOTS];
static int killer_mdw[MAX_PLY][KILLER_SLOTS];

static const int otrx[8] = {1, 1, 1, -1, -1, -1, -1, 1};
static const int otr[8] = {1, 0, 0, 1, -1, 0, 0, -1};
static const int knlst[16] = {2, 1, 2, -1, -2, 1, -2, -1, 1, 2, 1, -2, -1, 2, -1, -2};

/* ==================== FUNCTION PROTOTYPES ==================== */

static int move_score(int msw, int mdw);
static void sort_moves(void);
static void setbrd(void);
static void display(void);
static void input_position(void);
static void mk_mv(void);
static void un_mv(void);
static void gnmv(void);
static void gnwmv(void);
static void gnbmv(void);
static void gnmvsm(void);
static void gnstr(void);
static void gen_pawn_moves(void);
static void gen_knight_moves(void);
static void gen_bishop_moves(void);
static void gen_rook_moves(void);
static void gen_queen_moves(void);
static void gen_king_moves(void);
static void chkatk(int sqr, int fast_mode);
static void test_check(int msw, int *in_check);
static void eval(void);
static void breval(void);
static void coeval(void);
static void casteval(void);
static int  king_safety(void);
static int  mobget(void);
static int  clrfix(int val);
static int  enpris(int sqr);
static int  hiep(void);
static int  looka(void);
static int  quiesce(int alpha, int beta);
static void prune(void);
static void store_killer(int ply_idx, int msw, int mdw);
static void bstop(void);
static void popout(void);
static void push1(int val);
static int pop1(void);
static void push2(int val);
static int pop2(void);
static void init_pdl1(void);
static void init_pdl2(void);
static void pdl_overflow(void);
static void mapec(void);
static inline void build_msw(void);
static void out_sqr(int sqr);
static void outmv(int msw, int mdw);
static int parse_square(const char *str);
static int parse_algebraic_move(const char *move_str, int *msw, int *mdw);
static int inmv(void);
static void handle_command(const char *cmd);
static void show_help(void);
static void wb_send_move(int msw, int mdw);
static void wb_handle_command(const char *cmd);
static void wb_setboard(const char *fen);
static void wb_go(void);
static void wb_parse_level(const char *args);
static int  wb_compute_move_time(void);
static void wb_do_search(void);
static void print_coord_move(int msw, int mdw);
static void invalidate_eval_cache(void);
static uint32_t compute_position_hash(void);
static int is_repetition(void);
static void push_position_hash(void);
static void pop_position_hash(void);
static int game_phase_compute(void);

/* TACTICAL*/
static int is_attacked(int sq, int side);
static int see_capture(int to_sq, int from_sq, int captured_val);
static int hanging_piece_penalty(void);
static int opponent_hanging_bonus(void);

/* KING SAFETY */
static int king_shield_score(int king_sq, int side);
static int castled_shelter_bonus(int side);
static int is_king_in_open(int king_sq, int side);

/* PSQ and Pawn evaluation prototypes */
static int psq_bonus(int piece, int sq);
static int pawneval(void);

/* ==================== HOT INLINE HELPER FUNCTIONS ==================== */

/* Fast square construction - called millions of times */
static HOT_INLINE int make_sq(int r, int c) {
    return (r << 3) | c;
}

/* Fast bounds checking - critical for move generation */
static HOT_INLINE int is_valid_square(int r, int c) {
    return (unsigned)r < 8u && (unsigned)c < 8u;
}

/* Fast piece value access */
static HOT_INLINE int get_piece_value(int piece) {
    int ap = piece < 0 ? -piece : piece;
    return piece_value[ap];
}

/* Fast piece color check */
static HOT_INLINE int piece_color(int piece) {
    return piece > 0 ? 1 : (piece < 0 ? -1 : 0);
}

/* Fast king position access */
static HOT_INLINE int get_king_pos(int side) {
    return side == 0 ? wking : bking;
}

/* Fast board access without checks */
static HOT_INLINE int get_piece_fast(int sq) {
    return board[sq];
}

/* Fast board write without checks */
static HOT_INLINE void set_piece_fast(int sq, int piece) {
    board[sq] = piece;
}

/* Time expiration check - called every N nodes */
static HOT_INLINE int time_expired(int64_t now, int64_t limit) {
    return now >= limit;
}

/* Hash combination for repetition detection */
static HOT_INLINE uint32_t hash_combine(uint32_t h, uint32_t val) {
    return h * 1664525u + val;
}

/* King center distance for endgame evaluation */
static HOT_INLINE int king_center_dist(int sq) {
    int r = sq >> 3, c = sq & 7;
    int dr = r < 4 ? 3 - r : r - 4;
    int dc = c < 4 ? 3 - c : c - 4;
    int d = dr > dc ? dr : dc;
    return d < 0 ? -d : d;
}

/* Fast material update helpers */
static HOT_INLINE void add_material(int piece, int delta) {
    pw += (piece > 0) ? delta : -delta;
}

static HOT_INLINE void sub_material(int piece, int delta) {
    pw -= (piece > 0) ? delta : -delta;
}

/* Contempt: when engine is clearly ahead, make draws undesirable; when behind, acceptable */
static HOT_INLINE int draw_score(void) {
    /* pw > 0 means white is ahead; engine_balance > 0 means the engine is ahead */
    int engine_balance = (computer_side == WB_WHITE) ? pw : -pw;
    if (engine_balance > 150)  return -30;  /* avoid draw when clearly winning */
    if (engine_balance < -150) return  15;  /* accept draw when clearly losing */
    return 0;
}

/* ==================== PUSH DOWN LIST ==================== */

static void push1(int val) {
    pdl1_ptr++;
    if (pdl1_ptr >= PDL_SIZE) pdl_overflow();
    pdl1[pdl1_ptr] = val;
}

static int pop1(void) {
    if (pdl1_ptr < 0) return 0;
    return pdl1[pdl1_ptr--];
}

static HOT_INLINE void push2(int val) {
    if (++pdl2_ptr >= PDL_SIZE) pdl_overflow();
    pdl2[pdl2_ptr] = val;
}

static HOT_INLINE int pop2(void) {
    if (pdl2_ptr < 0) return 0;
    return pdl2[pdl2_ptr--];
}

static void init_pdl1(void) { pdl1_ptr = -1; }
static void init_pdl2(void) { pdl2_ptr = -1; }

static void pdl_overflow(void) {
    init_pdl1();
    init_pdl2();
    longjmp(search_abort_jmp, 1);
}

static void popout(void) {
    while (pdl2_ptr >= 0) {
        (void)pop2();
        if (pdl2_ptr < 0) break;
        int msw = pop2();
        if (msw == 0) break;
    }
    init_pdl2();
}

/* ==================== CACHE MANAGEMENT ==================== */

static void invalidate_eval_cache(void) {
    eg_cache = -1;
    game_phase_cache = -1;
}

static int game_phase_compute(void);

static HOT_INLINE int is_endgame(void) {
    if (eg_cache < 0) {
        eg_cache = (game_phase_compute() < 64) ? 1 : 0;
    }
    return eg_cache;
}

static HOT_INLINE int game_phase(void) {
    if (game_phase_cache < 0) {
        game_phase_cache = game_phase_compute();
    }
    return game_phase_cache;
}

/* ==================== REPETITION DETECTION ==================== */

static uint32_t compute_position_hash(void) {
    uint32_t h = (uint32_t)whose + 1;  /* side to move */
    h = hash_combine(h, (wpsw & 07777) + (bpsw & 07777) + last_move);
    for (int i = 0; i < BOARD_SIZE; i++) {
        h = hash_combine(h, (uint32_t)(board[i] + 128));
    }
    return h;
}

static int is_repetition(void) {
    uint32_t current = compute_position_hash();
    int count = 0;
    for (int i = history_ptr - 1; i >= 0; i--) {
        if (pos_history[i] == current) {
            count++;
            if (count >= 2) return 1;
        }
    }
    return 0;
}

static void push_position_hash(void) {
    if (history_ptr < REP_HISTORY_SIZE)
        pos_history[history_ptr++] = compute_position_hash();
}

static void pop_position_hash(void) {
    if (history_ptr > 0) history_ptr--;
}

/* ==================== BOARD SETUP ==================== */

static void setbrd(void) {
    static const int initial_board[BOARD_SIZE] = {
        ROOK, KNIGHT, BISHOP, QUEEN, KING, BISHOP, KNIGHT, ROOK,
        PAWN, PAWN, PAWN, PAWN, PAWN, PAWN, PAWN, PAWN,
        EMPTY, EMPTY, EMPTY, EMPTY, EMPTY, EMPTY, EMPTY, EMPTY,
        EMPTY, EMPTY, EMPTY, EMPTY, EMPTY, EMPTY, EMPTY, EMPTY,
        EMPTY, EMPTY, EMPTY, EMPTY, EMPTY, EMPTY, EMPTY, EMPTY,
        EMPTY, EMPTY, EMPTY, EMPTY, EMPTY, EMPTY, EMPTY, EMPTY,
        -PAWN, -PAWN, -PAWN, -PAWN, -PAWN, -PAWN, -PAWN, -PAWN,
        -ROOK, -KNIGHT, -BISHOP, -QUEEN, -KING, -BISHOP, -KNIGHT, -ROOK
    };
    memcpy(board, initial_board, sizeof(initial_board));
    last_move = 0; wpsw = bpsw = 0; pw = 0; domap = 1; whose = 0;
    for (int i = 0; i < BOARD_SIZE; i++) {
        if (board[i] != EMPTY) {
            int av = abs(board[i]);
            pw += (board[i] > 0) ? piece_value[av] : -piece_value[av];
        }
    }
    wking = 4; bking = 60; wcastled = bcastled = 0; halfmove_clock = 0;
    /* Clear repetition history on new game */
    history_ptr = 0;
    memset(pos_history, 0, sizeof(pos_history));
    invalidate_eval_cache();
    push_position_hash();
    killers_initialized = 0;
    /* Clear killer move tables for new game */
    memset(killer_msw, 0, sizeof(killer_msw));
    memset(killer_mdw, 0, sizeof(killer_mdw));
    /* Clear PV line storage */
    memset(pv_len, 0, sizeof(pv_len));
}

static void mapec(void) {
    if (!domap) return;
    domap = 0;
    white_map_ptr = black_map_ptr = 0;
    for (int i = 0; i < BOARD_SIZE; i++) {
        int piece = board[i];
        if (piece != EMPTY) {
            if (piece > 0) {
                white_map[white_map_ptr++] = i;
                if (piece == KING) wking = i;
            } else {
                black_map[black_map_ptr++] = i;
                if (piece == -KING) bking = i;
            }
        }
    }
    white_map[white_map_ptr] = black_map[black_map_ptr] = 0;
}

static inline int clrfix(int val) { return (val < 0) ? -val : val; }

/* ==================== MOVE HANDLING ==================== */

static HOT_INLINE void split(int msw, int *to_addr, int *from_addr) {
    *to_addr = msw & 0x3F;
    *from_addr = (msw >> 6) & 0x3F;
}

static HOT_INLINE int build_to_addr(int rank, int file) { return make_sq(rank, file); }
static HOT_INLINE void build_msw(void) { gnmsw = (((gn1 << 3) | gn2) << 6) | ((gn3 << 3) | gn4); }
static void gnstr(void) { gncnt++; if (!bogus) { push2(gnmsw); push2(gnmdw); } }

static void mk_mv(void) {
    int to_sqr, from_sqr, captured = 0, special;
    domap = 1;
    split(to_mak1, &to_sqr, &from_sqr);
    
    if (to_mak2 < 0) {
        captured = board[to_sqr];
        push1(captured);
        pw -= (captured > 0) ? get_piece_value(captured) : -get_piece_value(captured);
    }
    push1(to_mak1);
    board[to_sqr] = board[from_sqr];
    board[from_sqr] = EMPTY;
    push1(wpsw); push1(bpsw); push1(last_move); push1(halfmove_clock);
    
    if (to_mak2 < 0 || abs(board[to_sqr]) == PAWN)
        halfmove_clock = 0;
    else
        halfmove_clock++;
    last_move = to_mak2;
    
    special = (to_mak2 >= 0) ? (to_mak2 & 7) : ((-to_mak2 >= 4) ? ((-to_mak2) & 7) : 0);

    if (from_sqr == 4)  wpsw |= 03000;
    if (from_sqr == 60) bpsw |= 03000;
    if (from_sqr == 0)  wpsw |= 01000;
    if (from_sqr == 7)  wpsw |= 02000;
    if (from_sqr == 56) bpsw |= 01000;
    if (from_sqr == 63) bpsw |= 02000;
    if (to_mak2 < 0) {
        if (to_sqr == 0)  wpsw |= 01000;
        if (to_sqr == 7)  wpsw |= 02000;
        if (to_sqr == 56) bpsw |= 01000;
        if (to_sqr == 63) bpsw |= 02000;
    }

    switch(special) {
        case 1:
            if (board[to_sqr] == KING) {
                board[from_sqr - 1] = board[from_sqr - 4];
                board[from_sqr - 4] = EMPTY;
                wpsw |= 01000; wcastled = 1;
            } else if (board[to_sqr] == -KING) {
                board[from_sqr - 1] = board[from_sqr - 4];
                board[from_sqr - 4] = EMPTY;
                bpsw |= 01000; bcastled = 1;
            }
            break;
        case 2:
            if (board[to_sqr] == KING) {
                board[from_sqr + 1] = board[from_sqr + 3];
                board[from_sqr + 3] = EMPTY;
                wpsw |= 02000; wcastled = 1;
            } else if (board[to_sqr] == -KING) {
                board[from_sqr + 1] = board[from_sqr + 3];
                board[from_sqr + 3] = EMPTY;
                bpsw |= 02000; bcastled = 1;
            }
            break;
        case 3: {
            int cp = to_sqr + ((board[to_sqr] > 0) ? -8 : 8);
            pw += (board[to_sqr] > 0) ? PAWN_VAL : -PAWN_VAL;
            board[cp] = EMPTY;
            break;
        }
        case 4: case 5: case 6: case 7: {
            int is_white = (board[to_sqr] > 0);
            int pv;
            switch(special) {
                case 4: pv = is_white ? KNIGHT : -KNIGHT; break;
                case 5: pv = is_white ? BISHOP : -BISHOP; break;
                case 6: pv = is_white ? ROOK : -ROOK; break;
                default: pv = is_white ? QUEEN : -QUEEN; break;
            }
            pw -= is_white ? PAWN_VAL : -PAWN_VAL;
            board[to_sqr] = pv;
            pw += is_white ? get_piece_value(pv) : -get_piece_value(pv);
            break;
        }
    }
    whose = (whose == 0) ? -1 : 0;
    invalidate_eval_cache();
    push_position_hash();
}

static void un_mv(void) {
    int to_sqr, from_sqr, old_msw, old_mdw, special;
    domap = 1;
    old_mdw = last_move;
    halfmove_clock = pop1();
    last_move = pop1();
    bpsw = pop1();
    wpsw = pop1();
    old_msw = pop1();
    to_mak1 = old_msw;
    split(old_msw, &to_sqr, &from_sqr);
    special = (old_mdw >= 0) ? (old_mdw & 7) : ((-old_mdw >= 4) ? ((-old_mdw) & 7) : 0);
    
    switch(special) {
        case 1:
            if (board[to_sqr] == KING) {
                board[from_sqr - 4] = board[from_sqr - 1];
                board[from_sqr - 1] = EMPTY;
                wcastled = 0;
            } else if (board[to_sqr] == -KING) {
                board[from_sqr - 4] = board[from_sqr - 1];
                board[from_sqr - 1] = EMPTY;
                bcastled = 0;
            }
            break;
        case 2:
            if (board[to_sqr] == KING) {
                board[from_sqr + 3] = board[from_sqr + 1];
                board[from_sqr + 1] = EMPTY;
                wcastled = 0;
            } else if (board[to_sqr] == -KING) {
                board[from_sqr + 3] = board[from_sqr + 1];
                board[from_sqr + 1] = EMPTY;
                bcastled = 0;
            }
            break;
        case 3: {
            int cp = to_sqr + ((board[to_sqr] > 0) ? -8 : 8);
            board[cp] = (board[to_sqr] > 0) ? -PAWN : PAWN;
            pw -= (board[to_sqr] > 0) ? PAWN_VAL : -PAWN_VAL;
            break;
        }
        case 4: case 5: case 6: case 7: {
            int is_white = (board[to_sqr] > 0);
            pw -= is_white ? get_piece_value(board[to_sqr]) : -get_piece_value(board[to_sqr]);
            board[to_sqr] = is_white ? PAWN : -PAWN;
            pw += is_white ? PAWN_VAL : -PAWN_VAL;
            break;
        }
    }
    
    board[from_sqr] = board[to_sqr];
    if (old_mdw < 0) {
        int captured = pop1();
        board[to_sqr] = captured;
        pw += (captured > 0) ? get_piece_value(captured) : -get_piece_value(captured);
    } else {
        board[to_sqr] = EMPTY;
    }
    
    whose = (whose == 0) ? -1 : 0;
    invalidate_eval_cache();
    pop_position_hash();
}

/* ==================== MOVE GENERATION ==================== */

static inline int sno(int val) { return (unsigned)val < 8u; }

static void gen_pawn_moves(void) {
    int pd = (whose == 0) ? 1 : -1;
    int start = (whose == 0) ? 1 : 6;
    int prom = (whose == 0) ? 7 : 0;
    int in_check, r, c;
    
    r = gn1 + pd; c = gn2;
    if (is_valid_square(r, c) && get_piece_fast(make_sq(r, c)) == EMPTY) {
        gn3 = r; gn4 = c; build_msw(); gnmdw = 0;
        test_check(gnmsw, &in_check);
        if (!in_check) {
            if (r == prom) {
                for (int p = 4; p <= 7; p++) { gnmdw = p; gnstr(); }
            } else gnstr();
        }
    }
    
    if (gn1 == start) {
        r = gn1 + 2 * pd;
        if (is_valid_square(r, c)) {
            int mid = make_sq(gn1 + pd, gn2);
            int to = make_sq(r, gn2);
            if (board[mid] == EMPTY && board[to] == EMPTY) {
                gn3 = r; gn4 = gn2; build_msw(); gnmdw = (gn3 * 8 + gn4) << 3;
                test_check(gnmsw, &in_check);
                if (!in_check) gnstr();
            }
        }
    }
    
    for (int dc = -1; dc <= 1; dc += 2) {
        c = gn2 + dc;
        if (is_valid_square(r, c)) {
            r = gn1 + pd;
            if (is_valid_square(r, c)) {
                int to = make_sq(r, c);
                if (board[to] != EMPTY && ((whose == 0 && board[to] < 0) || (whose != 0 && board[to] > 0))) {
                    gn3 = r; gn4 = c; build_msw(); gnmdw = -1;
                    test_check(gnmsw, &in_check);
                    if (!in_check) {
                        if (r == prom) {
                            for (int p = 4; p <= 7; p++) { gnmdw = -p; gnstr(); }
                        } else gnstr();
                    }
                }
            }
        }
    }
    
    if (last_move > 7) {
        int ep_sq = last_move >> 3;
        int epf = ep_sq % 8;
        int epr = ep_sq / 8;
        if (abs(gn1 - epr) == 0 && abs(gn2 - epf) == 1) {
            gn3 = gn1 + pd; gn4 = epf; build_msw(); gnmdw = 3;
            test_check(gnmsw, &in_check);
            if (!in_check) gnstr();
        }
    }
}

static void gen_knight_moves(void) {
    int in_check;
    for (int i = 0; i < 16; i += 2) {
        int r = gn1 + knlst[i], c = gn2 + knlst[i+1];
        if (is_valid_square(r, c)) {
            int to = make_sq(r, c);
            if (board[to] == EMPTY) {
                gn3 = r; gn4 = c; build_msw(); gnmdw = 0;
                test_check(gnmsw, &in_check);
                if (!in_check) gnstr();
            } else if ((whose == 0 && board[to] < 0) || (whose != 0 && board[to] > 0)) {
                gn3 = r; gn4 = c; build_msw(); gnmdw = -1;
                test_check(gnmsw, &in_check);
                if (!in_check) gnstr();
            }
        }
    }
}

static void gen_bishop_moves(void) {
    int in_check;
    for (int i = 0; i < 8; i += 2) {
        int dr = otrx[i], dc = otrx[i+1];
        int r = gn1 + dr, c = gn2 + dc;
        while (is_valid_square(r, c)) {
            int to = make_sq(r, c);
            if (board[to] != EMPTY) {
                if ((whose == 0 && board[to] < 0) || (whose != 0 && board[to] > 0)) {
                    gn3 = r; gn4 = c; build_msw(); gnmdw = -1;
                    test_check(gnmsw, &in_check);
                    if (!in_check) { qmvcnt++; gnstr(); }
                }
                break;
            }
            gn3 = r; gn4 = c; build_msw(); gnmdw = 0;
            test_check(gnmsw, &in_check);
            if (!in_check) gnstr();
            r += dr; c += dc;
        }
    }
}

static void gen_rook_moves(void) {
    int in_check;
    for (int i = 0; i < 8; i += 2) {
        int dr = otr[i], dc = otr[i+1];
        int r = gn1 + dr, c = gn2 + dc;
        while (is_valid_square(r, c)) {
            int to = make_sq(r, c);
            if (board[to] != EMPTY) {
                if ((whose == 0 && board[to] < 0) || (whose != 0 && board[to] > 0)) {
                    gn3 = r; gn4 = c; build_msw(); gnmdw = -1;
                    test_check(gnmsw, &in_check);
                    if (!in_check) gnstr();
                }
                break;
            }
            gn3 = r; gn4 = c; build_msw(); gnmdw = 0;
            test_check(gnmsw, &in_check);
            if (!in_check) gnstr();
            r += dr; c += dc;
        }
    }
}

static void gen_queen_moves(void) {
    gen_bishop_moves();
    gen_rook_moves();
}

static void gen_king_moves(void) {
    int in_check, ks = (whose == 0) ? 4 : 60;
    
    if (cntr1 == ks) {
        int kpsw = (whose == 0) ? wpsw : bpsw;
        test_check(0, &in_check);
        
        if (!in_check && gnchek == 0) {
            if (!(kpsw & 01000)) {
                int rs = (whose == 0) ? 0 : 56;
                if (board[rs] == ((whose == 0) ? ROOK : -ROOK)) {
                    int empty = 1;
                    for (int s = ks - 1; s > rs; s--) if (board[s] != EMPTY) { empty = 0; break; }
                    if (empty) {
                        int safe = 1;
                        for (int s = ks - 2; s <= ks; s++) {
                            int ow = whose;
                            whose = (whose == 0) ? -1 : 0;
                            chkatk(s, 1);
                            whose = ow;
                            if (pcnt > 0) { safe = 0; break; }
                        }
                        if (safe) { gn3 = gn1; gn4 = gn2 - 2; build_msw(); gnmdw = 1; gnstr(); }
                    }
                }
            }
            if (!(kpsw & 02000)) {
                int rs = (whose == 0) ? 7 : 63;
                if (board[rs] == ((whose == 0) ? ROOK : -ROOK)) {
                    int empty = 1;
                    for (int s = ks + 1; s < rs; s++) if (board[s] != EMPTY) { empty = 0; break; }
                    if (empty) {
                        int safe = 1;
                        for (int s = ks; s <= ks + 2; s++) {
                            int ow = whose;
                            whose = (whose == 0) ? -1 : 0;
                            chkatk(s, 1);
                            whose = ow;
                            if (pcnt > 0) { safe = 0; break; }
                        }
                        if (safe) { gn3 = gn1; gn4 = gn2 + 2; build_msw(); gnmdw = 2; gnstr(); }
                    }
                }
            }
        }
    }
    
    for (int dr = -1; dr <= 1; dr++) {
        for (int dc = -1; dc <= 1; dc++) {
            if (dr == 0 && dc == 0) continue;
            int r = gn1 + dr, c = gn2 + dc;
            if (is_valid_square(r, c)) {
                int to = make_sq(r, c);
                if (board[to] == EMPTY || ((whose == 0 && board[to] < 0) || (whose != 0 && board[to] > 0))) {
                    int old_piece = board[to], old_from = board[cntr1];
                    board[to] = board[cntr1];
                    board[cntr1] = EMPTY;
                    int ow = whose;
                    whose = (whose == 0) ? -1 : 0;
                    chkatk(to, 1);
                    whose = ow;
                    board[cntr1] = old_from;
                    board[to] = old_piece;
                    if (pcnt == 0) {
                        gn3 = r; gn4 = c; build_msw();
                        gnmdw = (board[to] != EMPTY) ? -1 : 0;
                        gnstr();
                    } else kngblk++;
                }
            }
        }
    }
}

static void gnmv(void) {
    gncnt = cmsw = smsw = kngblk = mobmod = qmvcnt = 0;
    cking = get_king_pos(whose);
    cntr1 = cking;
    
    int ow = whose;
    whose = (whose == 0) ? -1 : 0;
    chkatk(cking, 1);
    whose = ow;
    gnchek = pcnt;
    
    if (!bogus) { push2(0); push2(0); }
    
    gn1 = SQR_RANK(cking); gn2 = SQR_FILE(cking); cntr1 = cking;
    gen_king_moves();
    
    if (gnchek < 2) {
        for (int sq = 0; sq < BOARD_SIZE; sq++) {
            int piece = board[sq];
            if (piece == EMPTY) continue;
            if ((whose == 0 && piece > 0) || (whose != 0 && piece < 0)) {
                gn1 = SQR_RANK(sq); gn2 = SQR_FILE(sq); cntr1 = sq;
                switch(abs(piece)) {
                    case PAWN: gen_pawn_moves(); break;
                    case KNIGHT: gen_knight_moves(); break;
                    case BISHOP: gen_bishop_moves(); break;
                    case ROOK: gen_rook_moves(); break;
                    case QUEEN: gen_queen_moves(); break;
                    default: break;
                }
            }
        }
    }
    
    mobmod = gncnt - (qmvcnt * 3 / 4);
    if (gncnt == 0) { if (gnchek > 0) cmsw = 1; else smsw = 1; }
}

static void gnwmv(void) { whose = 0; mapec(); gnmv(); }
static void gnbmv(void) { whose = -1; mapec(); gnmv(); }
static void gnmvsm(void) { if (whose == 0) gnwmv(); else gnbmv(); }

/* ==================== ATTACK DETECTION ==================== */

static void chkatk(int sqr, int fast_mode) {
    int r = SQR_RANK(sqr), c = SQR_FILE(sqr), piece;
    pcnt = 0; pval = 999; psqr = -1;
    
    int pd = (whose == 0) ? -1 : 1;
    for (int dc = -1; dc <= 1; dc += 2) {
        int pr = r + pd, pc_c = c + dc;
        if (is_valid_square(pr, pc_c)) {
            int ps = make_sq(pr, pc_c);
            piece = board[ps];
            if (piece != EMPTY && abs(piece) == PAWN && ((whose == 0 && piece > 0) || (whose != 0 && piece < 0))) {
                pcnt++; if (fast_mode) return;
                if (PAWN_VAL < pval) { pval = PAWN_VAL; psqr = ps; }
            }
        }
    }
    
    for (int i = 0; i < 16; i += 2) {
        int kr = r + knlst[i], kc = c + knlst[i+1];
        if (is_valid_square(kr, kc)) {
            int ks = make_sq(kr, kc);
            piece = board[ks];
            if (piece != EMPTY && abs(piece) == KNIGHT && ((whose == 0 && piece > 0) || (whose != 0 && piece < 0))) {
                pcnt++; if (fast_mode) return;
                if (KNIGHT_VAL < pval) { pval = KNIGHT_VAL; psqr = ks; }
            }
        }
    }
    
    for (int dr = -1; dr <= 1; dr++) {
        for (int dc = -1; dc <= 1; dc++) {
            if (dr == 0 && dc == 0) continue;
            int kr = r + dr, kc = c + dc;
            if (is_valid_square(kr, kc)) {
                int ks = make_sq(kr, kc);
                piece = board[ks];
                if (piece != EMPTY && abs(piece) == KING && ((whose == 0 && piece > 0) || (whose != 0 && piece < 0))) {
                    pcnt++; if (fast_mode) return;
                    if (KING_VAL < pval) { pval = KING_VAL; psqr = ks; }
                }
            }
        }
    }
    
    for (int i = 0; i < 8; i += 2) {
        int dr = otrx[i], dc = otrx[i+1];
        int tr = r + dr, tc = c + dc;
        while (is_valid_square(tr, tc)) {
            int ts = make_sq(tr, tc);
            piece = board[ts];
            if (piece != EMPTY) {
                int ap = abs(piece);
                if ((ap == BISHOP || ap == QUEEN) && ((whose == 0 && piece > 0) || (whose != 0 && piece < 0))) {
                    pcnt++; if (fast_mode) return;
                    int val = (ap == BISHOP) ? BISHOP_VAL : QUEEN_VAL;
                    if (val < pval) { pval = val; psqr = ts; }
                }
                break;
            }
            tr += dr; tc += dc;
        }
    }
    
    for (int i = 0; i < 8; i += 2) {
        int dr = otr[i], dc = otr[i+1];
        int tr = r + dr, tc = c + dc;
        while (is_valid_square(tr, tc)) {
            int ts = make_sq(tr, tc);
            piece = board[ts];
            if (piece != EMPTY) {
                int ap = abs(piece);
                if ((ap == ROOK || ap == QUEEN) && ((whose == 0 && piece > 0) || (whose != 0 && piece < 0))) {
                    pcnt++; if (fast_mode) return;
                    int val = (ap == ROOK) ? ROOK_VAL : QUEEN_VAL;
                    if (val < pval) { pval = val; psqr = ts; }
                }
                break;
            }
            tr += dr; tc += dc;
        }
    }
}

static void test_check(int msw, int *in_check) {
    int to_sqr, from_sqr, old_to, old_from, king_sqr;
    if (msw == 0) {
        int ow = whose;
        whose = (whose == 0) ? -1 : 0;
        chkatk(cking, 1);
        whose = ow;
        *in_check = (pcnt > 0);
        return;
    }
    split(msw, &to_sqr, &from_sqr);
    old_to = board[to_sqr]; old_from = board[from_sqr];
    board[to_sqr] = board[from_sqr]; board[from_sqr] = EMPTY;

    int ep_sqr = -1, ep_save = 0;
    if (abs(old_from) == PAWN && (from_sqr % 8) != (to_sqr % 8) && old_to == EMPTY) {
        ep_sqr  = (from_sqr / 8) * 8 + (to_sqr % 8);
        ep_save = board[ep_sqr];
        board[ep_sqr] = EMPTY;
    }

    king_sqr = (from_sqr == cking) ? to_sqr : cking;
    int ow = whose;
    whose = (whose == 0) ? -1 : 0;
    chkatk(king_sqr, 1);
    whose = ow;
    *in_check = (pcnt > 0);
    board[from_sqr] = old_from; board[to_sqr] = old_to;
    if (ep_sqr >= 0) board[ep_sqr] = ep_save;
}

/* ==================== EVALUATION FUNCTIONS ==================== */

static const int cdist[64] = {
    3,3,3,3,3,3,3,3,
    3,2,2,2,2,2,2,3,
    3,2,1,1,1,1,2,3,
    3,2,1,0,0,1,2,3,
    3,2,1,0,0,1,2,3,
    3,2,1,1,1,1,2,3,
    3,2,2,2,2,2,2,3,
    3,3,3,3,3,3,3,3
};

/* ==================== TAPERED EVAL PHASE ==================== */
#define TAPER(mg, eg, ph) (((mg) * (ph) + (eg) * (256 - (ph))) >> 8)

/* Phase weights per piece (queen=4, rook=2, minor=1 each) */
#define PH_QUEEN   4
#define PH_ROOK    2
#define PH_MINOR   1
#define PH_TOTAL   24

static int game_phase_compute(void) {
    int ph = 0;
    for (int i = 0; i < BOARD_SIZE; i++) {
        int av = abs(board[i]);
        switch (av) {
            case QUEEN:  ph += PH_QUEEN; break;
            case ROOK:   ph += PH_ROOK;  break;
            case BISHOP:
            case KNIGHT: ph += PH_MINOR; break;
            default: break;
        }
    }
    if (ph > PH_TOTAL) ph = PH_TOTAL;
    return (ph * 256) / PH_TOTAL;
}

static void breval(void) {
    int ph = game_phase();
    int wm = 0, bm = 0;
    for (int f = 0; f < 8; f++) {
        int p = board[f], ap = abs(p);
        if (ap == KNIGHT || ap == BISHOP) { if (p > 0) wm++; else bm++; }
        p = board[56 + f]; ap = abs(p);
        if (ap == KNIGHT || ap == BISHOP) { if (p > 0) wm++; else bm++; }
    }
    stratg += TAPER((bm - wm) * 25, 0, ph);
}

static void coeval(void) {
    static const int cs[] = {27, 28, 35, 36};
    static const int ext[] = {18,19,20,21,26,29,34,37,42,43,44,45};
    int i, p;
    int ph = game_phase();
    int mg = 0;

    for (i = 0; i < 4; i++) {
        p = board[cs[i]];
        if (p != EMPTY) mg += (p > 0) ? 10 : -10;
        if (p ==  PAWN) mg += 10;
        if (p == -PAWN) mg -= 10;
    }
    for (i = 0; i < 12; i++) {
        p = board[ext[i]];
        if (p != EMPTY) mg += (p > 0) ? 3 : -3;
    }
    if (board[11] == PAWN)  mg -= 8;
    if (board[12] == PAWN)  mg -= 8;
    if (board[51] == -PAWN) mg += 8;
    if (board[52] == -PAWN) mg += 8;

    stratg += TAPER(mg, 0, ph);
}

static void casteval(void) {
    int ph = game_phase();
    int mg_w = 0, mg_b = 0;

    if (wcastled)                       mg_w += 50;
    else if ((wpsw & 03000) == 03000)   mg_w -= 45;
    else if (wpsw & 03000)              mg_w -= 15;

    if (bcastled)                       mg_b += 50;
    else if ((bpsw & 03000) == 03000)   mg_b -= 45;
    else if (bpsw & 03000)              mg_b -= 15;
    
    /* Add bonus for pawns protecting king even if not castled */
    if (!wcastled && wking >= 0 && (wking / 8) == 0) {
        int kf = wking % 8;
        if (kf == 2 || kf == 3 || kf == 4 || kf == 5) {
            int has_f_pawn = 0, has_g_pawn = 0;
            for (int r = 1; r < 3; r++) {
                if (kf < 7 && board[r*8 + kf + 1] == PAWN) has_f_pawn = 1;
                if (kf > 0 && board[r*8 + kf - 1] == PAWN) has_g_pawn = 1;
            }
            if (has_f_pawn && has_g_pawn) mg_w += 20;
            else if (has_f_pawn || has_g_pawn) mg_w += 10;
        }
    }
    
    if (!bcastled && bking >= 0 && (bking / 8) == 7) {
        int kf = bking % 8;
        if (kf == 2 || kf == 3 || kf == 4 || kf == 5) {
            int has_f_pawn = 0, has_g_pawn = 0;
            for (int r = 6; r > 4; r--) {
                if (kf < 7 && board[r*8 + kf + 1] == -PAWN) has_f_pawn = 1;
                if (kf > 0 && board[r*8 + kf - 1] == -PAWN) has_g_pawn = 1;
            }
            if (has_f_pawn && has_g_pawn) mg_b += 20;
            else if (has_f_pawn || has_g_pawn) mg_b += 10;
        }
    }

    stratg += TAPER(mg_w - mg_b, 0, ph);
}

/* ==================== ENHANCED KING SAFETY FUNCTIONS ==================== */

static int king_shield_score(int king_sq, int side) {
    /* side: 0 = white, 1 = black */
    /* Returns positive score for good shield, negative for weak shield */
    int shield_score = 0;
    int kf = king_sq % 8;
    int kr = king_sq / 8;
    int pawn_dir = (side == 0) ? 1 : -1;
    int start_rank = (side == 0) ? kr + 1 : kr - 1;
    int end_rank = (side == 0) ? kr + MAX_SHIELD_RANK : kr - MAX_SHIELD_RANK;
    
    int file_start = kf - SHIELD_FILES/2;
    if (file_start < 0) file_start = 0;
    int file_end = kf + SHIELD_FILES/2;
    if (file_end > 7) file_end = 7;
    
    int total_pawns = 0;
    
    /* Check pawn directly in front of king (most important) */
    int front_sq = (side == 0) ? king_sq + 8 : king_sq - 8;
    if (front_sq >= 0 && front_sq < 64) {
        int front_piece = board[front_sq];
        if ((side == 0 && front_piece == PAWN) || (side == 1 && front_piece == -PAWN)) {
            shield_score += 25;
            total_pawns++;
        } else {
            shield_score -= 20;
        }
    }
    
    /* Check pawns on adjacent files in front ranks */
    for (int df = -1; df <= 1; df++) {
        if (df == 0) continue;
        int check_file = kf + df;
        if (check_file >= 0 && check_file < 8) {
            int pawn_count = 0;
            for (int r = start_rank; (side == 0 ? r <= end_rank : r >= end_rank); 
                 r += pawn_dir) {
                if (r < 0 || r >= 8) break;
                int sq = r * 8 + check_file;
                int piece = board[sq];
                if ((side == 0 && piece == PAWN) || (side == 1 && piece == -PAWN)) {
                    pawn_count++;
                    total_pawns++;
                    int rank_dist = (side == 0) ? r - kr : kr - r;
                    if (rank_dist == 1) shield_score += 18;
                    else if (rank_dist == 2) shield_score += 10;
                    else shield_score += 5;
                }
            }
            if (pawn_count == 0 && abs(df) == 1) {
                shield_score -= 12;
            }
        }
    }
    
    /* Check the file two steps away */
    for (int df = -2; df <= 2; df += 4) {
        if (df == 0) continue;
        int check_file = kf + df;
        if (check_file >= 0 && check_file < 8) {
            int pawn_count = 0;
            for (int r = start_rank; (side == 0 ? r <= end_rank : r >= end_rank); 
                 r += pawn_dir) {
                if (r < 0 || r >= 8) break;
                int sq = r * 8 + check_file;
                int piece = board[sq];
                if ((side == 0 && piece == PAWN) || (side == 1 && piece == -PAWN)) {
                    pawn_count++;
                    total_pawns++;
                    if (r == start_rank) shield_score += 8;
                    else shield_score += 4;
                }
            }
        }
    }
    
    /* Bonus for multiple shield pawns */
    if (total_pawns >= 3) shield_score += 15;
    else if (total_pawns == 2) shield_score += 8;
    else if (total_pawns == 1) shield_score += 0;
    else if (total_pawns == 0) shield_score -= NO_SHIELD_PENALTY;
    
    /* Check for open files adjacent to king */
    for (int df = -1; df <= 1; df++) {
        int check_file = kf + df;
        if (check_file < 0 || check_file >= 8) continue;
        int has_pawn = 0;
        for (int r = 0; r < 8; r++) {
            int sq = r * 8 + check_file;
            int piece = board[sq];
            if ((side == 0 && piece == PAWN) || (side == 1 && piece == -PAWN)) {
                has_pawn = 1;
                break;
            }
        }
        if (!has_pawn && df != 0) {
            shield_score -= OPEN_FILE_PENALTY;
        }
        else if (!has_pawn && df == 0) {
            shield_score -= OPEN_FILE_PENALTY * 2;
        }
    }
    
    return shield_score;
}

static int castled_shelter_bonus(int side) {
    int bonus = 0;
    
    if (side == 0) {
        if (wcastled) {
            bonus += CASTLE_SHELTER_BONUS;
            if ((board[7] == ROOK) && (board[6] == EMPTY) && (board[5] == EMPTY)) {
                bonus += 15;
            }
            if (board[5] == PAWN && board[6] == PAWN) {
                bonus += 10;
            }
        } else if ((wpsw & 03000) == 03000) {
            bonus -= 30;
        }
    } else {
        if (bcastled) {
            bonus += CASTLE_SHELTER_BONUS;
            if ((board[56] == -ROOK) && (board[57] == EMPTY) && (board[58] == EMPTY)) {
                bonus += 15;
            }
            if (board[61] == -PAWN && board[62] == -PAWN) {
                bonus += 10;
            }
        } else if ((bpsw & 03000) == 03000) {
            bonus -= 30;
        }
    }
    
    return bonus;
}

static int is_king_in_open(int king_sq, int side) {
    int kf = king_sq % 8;
    int open_penalty = 0;
    
    if (is_endgame()) return 0;
    
    int enemy_q = (side == 0) ? -QUEEN : QUEEN;
    int enemy_r = (side == 0) ? -ROOK : ROOK;
    
    for (int r = 0; r < 8; r++) {
        int sq = r * 8 + kf;
        int piece = board[sq];
        if (piece == enemy_q || piece == enemy_r) {
            open_penalty += 15;
            break;
        }
    }
    for (int f = 0; f < 8; f++) {
        int sq = king_sq / 8 * 8 + f;
        int piece = board[sq];
        if (piece == enemy_q || piece == enemy_r) {
            open_penalty += 15;
            break;
        }
    }
    
    return -open_penalty;
}

/* Main king safety evaluation */
static int king_safety(void) {
    int ph = game_phase();
    int mg_score = 0, eg_score = 0;
    int r, kf, kr, pf;
    int wshield, bshield;
    int w_shelter, b_shelter;
    
    /* King distance from center affects endgame */
    if (wking >= 0 && cdist[wking] > 2) eg_score -= 20;
    if (bking >= 0 && cdist[bking] > 2) eg_score += 20;
    
    /* ========== WHITE KING SAFETY ========== */
    if (wking >= 0) {
        wshield = king_shield_score(wking, 0);
        mg_score += wshield;
        
        w_shelter = castled_shelter_bonus(0);
        mg_score += w_shelter;
        
        mg_score += is_king_in_open(wking, 0);
        
        kr = wking / 8;
        kf = wking % 8;
        
        /* Check each file around king for pawn structure weaknesses */
        for (pf = kf - 1; pf <= kf + 1; pf++) {
            if (pf < 0 || pf > 7) continue;
            int pawn_present = 0;
            int pawn_weak = 0;
            
            for (r = kr + 1; r < 8; r++) {
                int sq = r * 8 + pf;
                int piece = board[sq];
                if (piece == PAWN) {
                    pawn_present = 1;
                    int has_neighbor = 0;
                    if (pf > 0) {
                        for (int rr = kr + 1; rr < 8; rr++) {
                            if (board[rr * 8 + pf - 1] == PAWN) { has_neighbor = 1; break; }
                        }
                    }
                    if (pf < 7) {
                        for (int rr = kr + 1; rr < 8; rr++) {
                            if (board[rr * 8 + pf + 1] == PAWN) { has_neighbor = 1; break; }
                        }
                    }
                    if (!has_neighbor) pawn_weak = 1;
                    break;
                }
            }
            
            if (!pawn_present && pf == kf) {
                mg_score -= 12;
            } else if (pawn_weak && pf == kf) {
                mg_score -= 8;
            }
        }
        
        /* Enemy knight proximity to king */
        int wkf = wking % 8, wkr = wking / 8;
        for (int i = 0; i < 16; i += 2) {
            int nr = wkr + knlst[i], nf = wkf + knlst[i+1];
            if (is_valid_square(nr, nf)) {
                int nsq = make_sq(nr, nf);
                if (board[nsq] == -KNIGHT) {
                    mg_score -= KNIGHT_PROXIMITY_PENALTY;
                }
            }
        }
    }
    
    /* ========== BLACK KING SAFETY ========== */
    if (bking >= 0) {
        bshield = king_shield_score(bking, 1);
        mg_score -= bshield;
        
        b_shelter = castled_shelter_bonus(1);
        mg_score -= b_shelter;
        
        mg_score -= is_king_in_open(bking, 1);
        
        kr = bking / 8;
        kf = bking % 8;
        
        for (pf = kf - 1; pf <= kf + 1; pf++) {
            if (pf < 0 || pf > 7) continue;
            int pawn_present = 0;
            int pawn_weak = 0;
            
            for (r = kr - 1; r >= 0; r--) {
                int sq = r * 8 + pf;
                int piece = board[sq];
                if (piece == -PAWN) {
                    pawn_present = 1;
                    int has_neighbor = 0;
                    if (pf > 0) {
                        for (int rr = kr - 1; rr >= 0; rr--) {
                            if (board[rr * 8 + pf - 1] == -PAWN) { has_neighbor = 1; break; }
                        }
                    }
                    if (pf < 7) {
                        for (int rr = kr - 1; rr >= 0; rr--) {
                            if (board[rr * 8 + pf + 1] == -PAWN) { has_neighbor = 1; break; }
                        }
                    }
                    if (!has_neighbor) pawn_weak = 1;
                    break;
                }
            }
            
            if (!pawn_present && pf == kf) {
                mg_score += 12;
            } else if (pawn_weak && pf == kf) {
                mg_score += 8;
            }
        }
        
        int bkf = bking % 8, bkr = bking / 8;
        for (int i = 0; i < 16; i += 2) {
            int nr = bkr + knlst[i], nf = bkf + knlst[i+1];
            if (is_valid_square(nr, nf)) {
                int nsq = make_sq(nr, nf);
                if (board[nsq] == KNIGHT) {
                    mg_score += KNIGHT_PROXIMITY_PENALTY;
                }
            }
        }
    }
    
    return TAPER(mg_score, eg_score, ph);
}

/* ==================== PSQ BONUS FUNCTION ==================== */
static HOT_INLINE int psq_bonus(int piece, int sq) {
    int rank, file, adv, cd, mg, eg;
    int ph = game_phase();

    if (piece > 0) {
        rank = sq / 8;
        file = sq % 8;
    } else {
        rank = 7 - (sq / 8);
        file = sq % 8;
    }

    cd = cdist[sq];

    switch (piece < 0 ? -piece : piece) {
    case PAWN:
        adv = rank - 1;
        mg = adv * 6;
        if (file >= 2 && file <= 5) mg += 16;
        if (file >= 3 && file <= 4) mg += 12;
        eg = adv * 8;
        if (file >= 2 && file <= 5) eg += 8;
        if (file >= 3 && file <= 4) eg += 4;
        break;
    case KNIGHT:
        mg = (cd == 3) ? -12 : (3 - cd) * 14;
        if (file == 0 || file == 7) mg -= 8;
        eg = (cd == 3) ? -20 : (3 - cd) * 10;
        if (file == 0 || file == 7) eg -= 14;
        break;
    case BISHOP:
        mg = (3 - cd) * 8;
        eg = (3 - cd) * 10;
        break;
    case ROOK:
        mg = (rank == 6) ? 30 : 0;
        eg = (rank == 6) ? 20 : 0;
        break;
    case QUEEN:
        mg = 0;
        if (file == 0 || file == 7) mg -= 12;
        if (rank >= 2 && rank <= 4) mg += (3 - cd) * 2;
        if (rank >= 5) mg -= (rank - 4) * 8;
        eg = (rank >= 2) ? (3 - cd) * 8 : 0;
        break;
    case KING:
        mg = (rank == 0) ? 12 : -rank * 8;
        if (file == 0 || file == 7) mg += 4;
        else if (file == 1 || file == 6) mg += 3;
        eg = (3 - cd) * 38;
        if (rank == 0) eg -= 20;
        else if (rank >= 3 && rank <= 4) eg += 16;
        break;
    default:
        mg = eg = 0;
        break;
    }

    int bonus = TAPER(mg, eg, ph);
    return (piece > 0) ? bonus : -bonus;
}

/* ==================== PAWN EVALUATION ==================== */
static const int passed_bonus[8] = { 0, 0, 15, 30, 55, 90, 0, 0 };

static int pawneval(void) {
    int pos = 0;
    int f, r, sq, af, df;

    int wfile[8]  = {0}, bfile[8]  = {0};
    int wfront[8] = {0}, bfront[8] = {7,7,7,7,7,7,7,7};

    for (sq = 0; sq < BOARD_SIZE; sq++) {
        int p = board[sq];
        if (p == PAWN) {
            f = sq % 8; r = sq / 8;
            wfile[f]++;
            if (r > wfront[f]) wfront[f] = r;
        } else if (p == -PAWN) {
            f = sq % 8; r = sq / 8;
            bfile[f]++;
            if (r < bfront[f]) bfront[f] = r;
        }
    }

    for (f = 0; f < 8; f++) {
        if (wfile[f] > 1) pos -= 16 * (wfile[f] - 1);
        if (bfile[f] > 1) pos += 16 * (bfile[f] - 1);

        {
            int wneighbour = (f > 0 && wfile[f-1] > 0) || (f < 7 && wfile[f+1] > 0);
            int bneighbour = (f > 0 && bfile[f-1] > 0) || (f < 7 && bfile[f+1] > 0);
            if (wfile[f] > 0 && !wneighbour) pos -= 18;
            if (bfile[f] > 0 && !bneighbour) pos += 18;
        }

        if (wfile[f] > 0) {
            int best = wfront[f];
            int passed = 1;
            for (df = -1; df <= 1 && passed; df++) {
                af = f + df;
                if (af < 0 || af >= 8) continue;
                if (bfile[af] > 0 && bfront[af] > best) passed = 0;
            }
            if (passed) {
                int bonus = passed_bonus[best];
                if (best == 6) bonus += 150;
                bonus = TAPER(bonus, bonus * 2, game_phase());
                if (f > 0 && wfile[f-1] > 0) bonus += bonus / 4;
                if (f < 7 && wfile[f+1] > 0) bonus += bonus / 4;
                if (best < 7 && board[(best+1)*8 + f] < 0) bonus -= bonus / 3;
                if (is_endgame() && wking >= 0) {
                    int kf = wking % 8, kr = wking / 8;
                    int kdist_f = kf - f; if (kdist_f < 0) kdist_f = -kdist_f;
                    int kdist_r = kr - best; if (kdist_r < 0) kdist_r = -kdist_r;
                    int kdist = (kdist_f > kdist_r) ? kdist_f : kdist_r;
                    if (kdist <= 2) bonus += (3 - kdist) * 15;
                    if (bking >= 0) {
                        int bkr = bking / 8, bkf = bking % 8;
                        int bdf = bkf - f; if (bdf < 0) bdf = -bdf;
                        int bdr = bkr - 7; if (bdr < 0) bdr = -bdr;
                        int bdist = (bdf > bdr) ? bdf : bdr;
                        if (bdist > 2) bonus += (bdist - 2) * 8;
                        int wdf = kf - f; if (wdf < 0) wdf = -wdf;
                        int wdr = 7 - kr;
                        int wdist = (wdf > wdr) ? wdf : wdr;
                        if (wdist < bdist) bonus += 20;
                    }
                }
                pos += bonus;
            }
        }

        if (bfile[f] > 0) {
            int best = bfront[f];
            int passed = 1;
            for (df = -1; df <= 1 && passed; df++) {
                af = f + df;
                if (af < 0 || af >= 8) continue;
                if (wfile[af] > 0 && wfront[af] < best) passed = 0;
            }
            if (passed) {
                int adv = 7 - best;
                int bonus = passed_bonus[adv];
                if (best == 1) bonus += 150;
                bonus = TAPER(bonus, bonus * 2, game_phase());
                if (f > 0 && bfile[f-1] > 0) bonus += bonus / 4;
                if (f < 7 && bfile[f+1] > 0) bonus += bonus / 4;
                if (best > 0 && board[(best-1)*8 + f] > 0) bonus -= bonus / 3;
                if (is_endgame() && bking >= 0) {
                    int kf = bking % 8, kr = bking / 8;
                    int kdist_f = kf - f; if (kdist_f < 0) kdist_f = -kdist_f;
                    int kdist_r = kr - best; if (kdist_r < 0) kdist_r = -kdist_r;
                    int kdist = (kdist_f > kdist_r) ? kdist_f : kdist_r;
                    if (kdist <= 2) bonus += (3 - kdist) * 15;
                    if (wking >= 0) {
                        int wkr = wking / 8, wkf = wking % 8;
                        int wdf = wkf - f; if (wdf < 0) wdf = -wdf;
                        int wdr = wkr;
                        int wdist = (wdf > wdr) ? wdf : wdr;
                        if (wdist > 2) bonus += (wdist - 2) * 8;
                        int bdf = kf - f; if (bdf < 0) bdf = -bdf;
                        int bdr = kr;
                        int bdist = (bdf > bdr) ? bdf : bdr;
                        if (bdist < wdist) bonus += 20;
                    }
                }
                pos -= bonus;
            }
        }
    }

    return pos;
}

/* ==================== EVALUATION FUNCTION (ORIGINAL, WORKING) ==================== */

static void eval(void) {
    int pos = 0;
    int wbishops = 0, bbishops = 0;
    
    stratg = 0;
    random_val = (random_val * 1103515245 + 12345) & 0x7fffffff;
    stratg += (random_val & 1);
    
    unsigned int wpf = 0, bpf = 0;
    for (int sq = 0; sq < BOARD_SIZE; sq++) {
        int p = board[sq];
        if (p == EMPTY) continue;
        if (p ==  PAWN) { wpf |= (1u << (sq & 7)); continue; }
        if (p == -PAWN) { bpf |= (1u << (sq & 7)); continue; }
        if (p ==  BISHOP) wbishops++;
        else if (p == -BISHOP) bbishops++;
    }
    for (int sq = 0; sq < BOARD_SIZE; sq++) {
        int p = board[sq];
        if (p == EMPTY) continue;
        pos += psq_bonus(p, sq);
        if (abs(p) == ROOK) {
            unsigned int fb = 1u << (sq & 7);
            int has_own = (p > 0) ? (wpf & fb) : (bpf & fb);
            int has_opp = (p > 0) ? (bpf & fb) : (wpf & fb);
            if (!has_own && !has_opp) pos += (p > 0) ?  30 : -30;
            else if (!has_own)        pos += (p > 0) ?  16 : -16;
            if (is_endgame()) {
                int rf = sq & 7;
                if (p > 0) {
                    int rr = sq >> 3;
                    for (int pr = rr + 1; pr < 8; pr++) {
                        int psq2 = (pr << 3) | rf;
                        if (board[psq2] == PAWN) { pos += 20; break; }
                        if (board[psq2] != EMPTY) break;
                    }
                } else {
                    int rr = sq >> 3;
                    for (int pr = rr - 1; pr >= 0; pr--) {
                        int psq2 = (pr << 3) | rf;
                        if (board[psq2] == -PAWN) { pos -= 20; break; }
                        if (board[psq2] != EMPTY) break;
                    }
                }
            }
        }
    }

    if (wbishops >= 2) pos += 50;
    if (bbishops >= 2) pos -= 50;
    
    pos += pawneval();
    stratg += pw;
    breval(); coeval(); casteval();
    
    {
        int ks = king_safety();
        stratg += (whose == 0) ? ks : -ks;
    }

    if (wking >= 0 && bking >= 0) {
        int ph = game_phase();
        int wkr = wking / 8, wkf = wking % 8;
        int bkr = bking / 8, bkf = bking % 8;
        int eg = 0;

        {
            int dr = wkr - bkr, df = wkf - bkf;
            if (dr < 0) dr = -dr;
            if (df < 0) df = -df;
            if ((dr == 0 && df == 2) || (df == 0 && dr == 2)) {
                if (whose == 0) eg -= 15;
                else            eg += 15;
            }
        }

        int chebyshev = (((wkr > bkr) ? wkr - bkr : bkr - wkr) >
                         ((wkf > bkf) ? wkf - bkf : bkf - wkf))
                        ? ((wkr > bkr) ? wkr - bkr : bkr - wkr)
                        : ((wkf > bkf) ? wkf - bkf : bkf - wkf);
        int k_prox = 7 - chebyshev;

        if (pw >= BISHOP_VAL + 50) {
            int bk_edge = cdist[bking] * 20;
            eg += bk_edge + k_prox * 8;
        } else if (pw <= -(BISHOP_VAL + 50)) {
            int wk_edge = cdist[wking] * 20;
            eg -= wk_edge + k_prox * 8;
        }

        {
            int ph_local = game_phase();
            if (ph_local < 32) {
                int wcd = cdist[wking];
                int bcd = cdist[bking];
                eg += (bcd - wcd) * 10;
            }
        }

        pos += TAPER(0, eg, ph);
    }

    /* Convert to side-to-move perspective */
    stratg = (whose == 0) ? stratg : -stratg;
    
    int pos_orient = (whose == 0) ? pos : -pos;
    stratg += pos_orient / 2;
    
    if (!in_quiesce) {
        stratg += mobget();
        domap = 1;
        
        stratg -= hanging_piece_penalty();
        stratg += opponent_hanging_bonus();
        
        int opp_king = (whose == 0) ? bking : wking;
        if (opp_king >= 0) {
            int kr = opp_king / 8, kf = opp_king % 8;
            for (int i = 0; i < 16; i += 2) {
                int tr = kr + knlst[i], tf = kf + knlst[i+1];
                if (is_valid_square(tr, tf)) {
                    int tsq = make_sq(tr, tf);
                    int piece = board[tsq];
                    if (abs(piece) == KNIGHT && ((whose == 0 && piece < 0) || (whose != 0 && piece > 0))) {
                        stratg -= 50;
                    }
                }
            }
        }
    }
    
    comp = stratg;
}

static int mobget(void) {
    int save_whose = whose;
    int save_cmsw = cmsw, save_smsw = smsw;
    int save_gncnt = gncnt, save_kngblk = kngblk;
    int save_mobmod = mobmod, save_qmvcnt = qmvcnt;
    int save_gnchek = gnchek, save_cking = cking;
    int save_domap = domap;
    int save_wking = wking, save_bking = bking;
    int wmob, bmob;

    domap = 1; bogus = 1; whose = 0;  gnmv(); wmob = mobmod;
    domap = 1; bogus = 1; whose = -1; gnmv(); bmob = mobmod;

    whose = save_whose;
    cmsw = save_cmsw; smsw = save_smsw;
    gncnt = save_gncnt; kngblk = save_kngblk;
    mobmod = save_mobmod; qmvcnt = save_qmvcnt;
    gnchek = save_gnchek; cking = save_cking;
    domap = save_domap;
    wking = save_wking; bking = save_bking;
    bogus = 0;

    return (save_whose == 0) ? (wmob - bmob) / 10 : (bmob - wmob) / 10;
}

static int enpris(int sqr) {
    int piece = board[sqr];
    if (piece == EMPTY) return 0;
    int side = (piece > 0) ? 0 : -1, ow = whose;
    whose = (side == 0) ? -1 : 0;
    chkatk(sqr, 0);
    int att = pcnt, aval = pval, asqr = psqr;
    if (att == 0) { whose = ow; return 0; }
    whose = side;
    chkatk(sqr, 0);
    int def = pcnt, dval = pval;
    whose = ow;
    int piece_val = get_piece_value(piece);
    int hanging = 0;
    if (def == 0 && att > 0)
        hanging = 1;
    else if (att > 0 && aval < piece_val)
        hanging = 1;
    else if (att > def && aval < piece_val + dval)
        hanging = 1;
    if (hanging) {
        enprad = sqr; enpval = aval; enpsqr = asqr; enpcnt = att;
        return piece_val;
    }
    return 0;
}

static int hiep(void) {
    int best = 0;
    mapec();
    int *map  = (whose == 0) ? white_map  : black_map;
    int  mptr = (whose == 0) ? white_map_ptr : black_map_ptr;
    for (int i = 0; i < mptr; i++) {
        int ex = enpris(map[i]);
        if (ex > best) {
            best = ex;
            hiepms = (enpsqr >= 0) ? ((enpsqr << 6) | map[i]) : hiepms;
        }
    }
    return best;
}

/* ==================== TACTICAL FUNCTIONS ==================== */

static int is_attacked(int sq, int side) {
    int save_whose = whose;
    whose = side;
    chkatk(sq, 1);
    whose = save_whose;
    return pcnt > 0;
}

static int see_capture(int to_sq, int from_sq, int captured_val) {
    int attacker = board[from_sq];
    int attacker_val = get_piece_value(attacker);
    int victim_val = captured_val;
    
    if (victim_val > attacker_val) return victim_val - attacker_val;
    
    int save_whose = whose;
    whose = (whose == 0) ? -1 : 0;
    chkatk(to_sq, 0);
    int defenders = pcnt;
    whose = save_whose;
    
    if (defenders == 0) return victim_val;
    if (defenders >= 1 && victim_val <= attacker_val) return -attacker_val;
    
    return victim_val - attacker_val;
}

static int hanging_piece_penalty(void) {
    int penalty = 0;
    mapec();
    
    int *map = (whose == 0) ? white_map : black_map;
    int mptr = (whose == 0) ? white_map_ptr : black_map_ptr;
    for (int i = 0; i < mptr; i++) {
        int sq = map[i];
        int piece = board[sq];
        if (abs(piece) == KING) continue;
        
        int save_whose = whose;
        whose = (save_whose == 0) ? -1 : 0;
        chkatk(sq, 0);
        int attacked = pcnt;
        whose = save_whose;
        chkatk(sq, 0);
        int defended = pcnt;
        whose = save_whose;
        
        if (attacked > 0) {
            int pv = get_piece_value(piece);
            if (defended == 0) {
                penalty += (pv * 3) / 4;
            }
            else if (attacked > defended) {
                penalty += pv / 4;
            }
        }
    }
    return penalty;
}

static int opponent_hanging_bonus(void) {
    int bonus = 0;
    int save_whose = whose;
    mapec();
    
    int *map = (save_whose == 0) ? black_map : white_map;
    int mptr = (save_whose == 0) ? black_map_ptr : white_map_ptr;
    for (int i = 0; i < mptr; i++) {
        int sq = map[i];
        int piece = board[sq];
        if (abs(piece) == KING) continue;
        
        whose = save_whose;
        chkatk(sq, 0);
        int we_attack = pcnt;
        
        whose = (save_whose == 0) ? -1 : 0;
        chkatk(sq, 0);
        int they_defend = pcnt;
        
        whose = save_whose;
        
        if (we_attack > 0) {
            int pv = get_piece_value(piece);
            if (they_defend == 0) {
                 bonus += (pv * 3) / 4;
            }
            else if (we_attack > they_defend) {
                bonus += pv / 4;
            }
        }
    }
    whose = save_whose;
    return bonus;
}

/* ==================== LOOKAHEAD SEARCH (ORIGINAL, WORKING) ==================== */

static int looka(void) {
    int sv, su, sg, s0, s1, sd, best_msw = 0, best_mdw = 0;

    if (search_use_timer && ((++search_nodes) & 0xFFF) == 0) {
        if (time_expired(now_ns(), search_limit_clk))
            longjmp(search_abort_jmp, 2);
    }

    ply++;
    su = uval1; sv = cval1; sg = gncnt; s0 = stratg; s1 = mob0; sd = depth;
    mob0 = mob1; mob1 = mobmod; mobmod = 0;
    uval1 = -sv; cval1 = -su; gncnt = 0;

    if (halfmove_clock >= 100 && ply > 1) { rval1 = draw_score(); goto done; }
    if (ply > 1 && is_repetition()) { rval1 = draw_score(); goto done; }

    /* Mate distance pruning */
    if (cval1 > MATE_SCORE) {
        int mate_in = (CHECKMATE_VALUE - cval1 + 1) / 2;
        int bound = CHECKMATE_VALUE - (mate_in - 1) * 2;
        if (bound < cval1) cval1 = bound;
    }
    if (uval1 < -MATE_SCORE) {
        int mate_in = (CHECKMATE_VALUE + uval1 + 1) / 2;
        int bound = -CHECKMATE_VALUE + (mate_in - 1) * 2;
        if (bound > uval1) uval1 = bound;
    }
    if (cval1 >= uval1) {
        rval1 = cval1;
        goto done;
    }

    if (ply >= depth) {
        eval();
        qply = 0;
        rval1 = quiesce(cval1, uval1);
        goto done;
    }

    gnmvsm();
    
    int original_global_depth = depth;
    int effective_depth = depth;
    
    if (gnchek > 0 && effective_depth < base_depth + 3)
        effective_depth++;

    if (gncnt == 1 && effective_depth < base_depth + 3)
        effective_depth++;

    depth = effective_depth;

    if (cmsw || smsw) {
        if (pdl2_ptr >= 1) { pop2(); pop2(); }
        rval1 = cmsw ? (-CHECKMATE_VALUE + ply) : draw_score();
        depth = original_global_depth;
        goto done;
    }

    prune();
    {
        int found_sentinel = 0;
        while (pdl2_ptr >= 0) {
            int mdw = pop2(), msw = pop2();
            if (msw == 0) { found_sentinel = 1; break; }
            to_mak2 = mdw; to_mak1 = msw;
            { int nxt = ply; if (nxt >= 0 && nxt < MAX_PLY) pv_len[nxt] = 0; }
            mk_mv(); int val = -looka(); un_mv();
            if (val > cval1) { 
                cval1 = val; best_msw = msw; best_mdw = mdw;
                int p = ply - 1;
                if (p >= 0 && p < MAX_PLY) {
                    pv_msw[p][0] = msw; pv_mdw[p][0] = mdw;
                    int nxt = p + 1;
                    if (nxt < MAX_PLY && pv_len[nxt] > 0) {
                        int copy_n = pv_len[nxt];
                        if (1 + copy_n > MAX_PLY) copy_n = MAX_PLY - 1;
                        memcpy(&pv_msw[p][1], pv_msw[nxt], copy_n * sizeof(int));
                        memcpy(&pv_mdw[p][1], pv_mdw[nxt], copy_n * sizeof(int));
                        pv_len[p] = 1 + copy_n;
                    } else {
                        pv_len[p] = 1;
                    }
                }
            }
            if (cval1 > uval1 && ply > 1) {
                store_killer(ply, msw, mdw);
                break;
            }
        }
        if (!found_sentinel) {
            while (pdl2_ptr >= 0) {
                (void)pop2();
                if (pdl2_ptr < 0) break;
                int msw = pop2();
                if (msw == 0) break;
            }
        }
    }
    if (ply == 1) { to_mak1 = best_msw; to_mak2 = best_mdw; }
    bestbl[ply * 2] = best_msw; bestbl[ply * 2 + 1] = best_mdw;
    rval1 = cval1;
done:
    uval1 = su; cval1 = sv; gncnt = sg; stratg = s0; mobmod = mob1; mob1 = mob0; mob0 = s1;
    depth = sd;
    ply--;
    return rval1;
}

/* ==================== QUIESCENCE SEARCH (ORIGINAL, WORKING) ==================== */

static int quiesce(int alpha, int beta) {
    int stand_pat, save_pdl2_ptr;

    if (search_use_timer && ((++search_nodes) & 0xFFF) == 0) {
        if (time_expired(now_ns(), search_limit_clk))
            longjmp(search_abort_jmp, 2);
    }

    if (qply >= 5) {
        stratg = pw;
        int ks = king_safety();
        stratg += (whose == 0) ? ks : -ks;
        comp = stratg;
        stand_pat = stratg;
    } else {
        in_quiesce = 1;
        eval();
        in_quiesce = 0;
        stand_pat = stratg;
    }
    
    if (stand_pat >= beta) return beta;
    if (stand_pat > alpha) alpha = stand_pat;

    save_pdl2_ptr = pdl2_ptr;
    gnmvsm();
    if (cmsw) {
        while (pdl2_ptr > save_pdl2_ptr) pop2();
        return -CHECKMATE_VALUE + ply;
    }

    {
        int base = save_pdl2_ptr + 2;
        int nmoves = (pdl2_ptr - base + 2) / 2;
        if (nmoves > 2) { sort_moves(); bstop(); }
    }

    while (pdl2_ptr > save_pdl2_ptr) {
        int mdw = pop2(), msw = pop2();
        if (msw == 0) break;
        int sp = (mdw < 0) ? 0 : (mdw & 7);
        int is_capture = (mdw < 0) || (sp == 3);
        
        if (!is_capture) continue;
        
        int to_sq = msw & 0x3F;
        int victim = board[to_sq];
        int victim_val = (victim != EMPTY) ? get_piece_value(victim) : 0;
        if (stand_pat + victim_val + PAWN_VAL < alpha) continue;

        to_mak1 = msw; to_mak2 = mdw;
        ply++;
        mk_mv();
        qply++;
        int val = -quiesce(-beta, -alpha);
        qply--;
        un_mv();
        ply--;

        if (val >= beta) {
            while (pdl2_ptr > save_pdl2_ptr) pop2();
            return beta;
        }
        if (val > alpha) alpha = val;
    }
    while (pdl2_ptr > save_pdl2_ptr) pop2();
    return alpha;
}

/* ==================== MOVE SORTING (ORIGINAL, WORKING) ==================== */

static void sort_moves(void) {
    int base = 1;
    for (int i = pdl2_ptr - 1; i >= 0; i -= 2) {
        if (pdl2[i] == 0) { base = i + 2; break; }
    }
    int n_moves = (pdl2_ptr - base + 2) / 2;
    if (n_moves <= 1) return;

    int scores[512];
    if (n_moves > 512) n_moves = 512;
    for (int i = 0; i < n_moves; i++)
        scores[i] = move_score(pdl2[base + i * 2], pdl2[base + i * 2 + 1]);

    for (int i = 1; i < n_moves; i++) {
        int key_s = scores[i];
        int key_m = pdl2[base + i*2], key_d = pdl2[base + i*2 + 1];
        int j = i - 1;
        while (j >= 0 && scores[j] < key_s) {
            scores[j+1] = scores[j];
            pdl2[base+(j+1)*2] = pdl2[base+j*2];
            pdl2[base+(j+1)*2+1] = pdl2[base+j*2+1];
            j--;
        }
        scores[j+1] = key_s;
        pdl2[base+(j+1)*2] = key_m;
        pdl2[base+(j+1)*2+1] = key_d;
    }
}

static void prune(void) {
    sort_moves();
    bstop();
}

static void store_killer(int ply_idx, int msw, int mdw) {
    if (mdw < 0) return;
    if (ply_idx < 0 || ply_idx >= MAX_PLY) return;
    if (killer_msw[ply_idx][0] == msw) return;
    killer_msw[ply_idx][1] = killer_msw[ply_idx][0];
    killer_mdw[ply_idx][1] = killer_mdw[ply_idx][0];
    killer_msw[ply_idx][0] = msw;
    killer_mdw[ply_idx][0] = mdw;
}

static int move_score(int msw, int mdw) {
    int to_sqr  = msw & 0x3F;
    int from_sqr = (msw >> 6) & 0x3F;
    int sp = (mdw < 0) ? 0 : (mdw & 7);

    if (sp >= 4 && sp <= 7) {
        static const int prom_val[] = {0,0,0,0,KNIGHT_VAL,BISHOP_VAL,ROOK_VAL,QUEEN_VAL};
        int base_score = 80 + prom_val[sp];
        if (mdw < 0) base_score += get_piece_value(board[to_sqr]);
        return base_score;
    }

    if (mdw < 0 || sp == 3) {
        int victim_val, attacker_val;
        if (sp == 3) {
            victim_val = PAWN_VAL;
        } else {
            int victim = board[to_sqr];
            victim_val = (victim != EMPTY) ? get_piece_value(victim) : 0;
        }
        attacker_val = get_piece_value(board[from_sqr]);
        
        int see_score = see_capture(to_sqr, from_sqr, victim_val);
        int base = 300 + see_score * 2;

        if (victim_val <= KNIGHT_VAL) {
            int opp_king = (whose == 0) ? bking : wking;
            int attacker = board[from_sqr];
            int atype = abs(attacker);
            if (opp_king >= 0 && atype >= 1 && atype <= 5) {
                int kr = opp_king / 8, kf = opp_king % 8;
                int tr = to_sqr / 8, tf = to_sqr % 8;
                int dr = tr - kr, df = tf - kf;
                int gives_chk = 0;
                
                if ((atype == ROOK || atype == QUEEN) && (dr == 0 || df == 0)) {
                    int sr = (dr == 0) ? 0 : (dr > 0 ? 1 : -1);
                    int sf = (df == 0) ? 0 : (df > 0 ? 1 : -1);
                    int r = kr + sr, f = kf + sf;
                    int blocked = 0;
                    int saw_piece = 0;
                    while (r != tr || f != tf) {
                        int sq = make_sq(r, f);
                        int piece = board[sq];
                        if (piece != EMPTY) {
                            if (sq == from_sqr && !saw_piece) {
                                saw_piece = 1;
                            } else {
                                blocked = 1;
                                break;
                            }
                        }
                        r += sr; f += sf;
                    }
                    if (!blocked) gives_chk = 1;
                }
                
                if (!gives_chk && (atype == BISHOP || atype == QUEEN)
                        && abs(dr) == abs(df) && dr != 0) {
                    int sr = (dr > 0) ? 1 : -1, sf = (df > 0) ? 1 : -1;
                    int r = kr + sr, f = kf + sf;
                    int blocked = 0;
                    int saw_piece = 0;
                    while (r != tr || f != tf) {
                        int sq = make_sq(r, f);
                        int piece = board[sq];
                        if (piece != EMPTY) {
                            if (sq == from_sqr && !saw_piece) {
                                saw_piece = 1;
                            } else {
                                blocked = 1;
                                break;
                            }
                        }
                        r += sr; f += sf;
                    }
                    if (!blocked) gives_chk = 1;
                }
                
                if (!gives_chk && atype == KNIGHT) {
                    if ((abs(dr)==2 && abs(df)==1) || (abs(dr)==1 && abs(df)==2))
                        gives_chk = 1;
                }
                if (gives_chk) base += 10000;
            }
        }
        return base;
    }

    int pidx = ply;
    if (pidx >= 0 && pidx < MAX_PLY) {
        for (int k = 0; k < KILLER_SLOTS; k++) {
            if (killer_msw[pidx][k] == msw) return 50 - k;
        }
    }

    {
        int opp_king = (whose == 0) ? bking : wking;
        int attacker = board[from_sqr];
        int atype = abs(attacker);
        if (opp_king >= 0 && atype >= 1 && atype <= 5) {
            int kr = opp_king / 8, kf = opp_king % 8;
            int tr = to_sqr / 8, tf = to_sqr % 8;
            int dr = tr - kr, df = tf - kf;
            int gives_chk = 0;
            if ((atype == ROOK || atype == QUEEN) && (dr == 0 || df == 0)) {
                int sr = (dr == 0) ? 0 : (dr > 0 ? 1 : -1);
                int sf = (df == 0) ? 0 : (df > 0 ? 1 : -1);
                int r = kr + sr, f = kf + sf;
                int blocked = 0;
                int saw_piece = 0;
                while (r != tr || f != tf) {
                    int sq = make_sq(r, f);
                    int piece = board[sq];
                    if (piece != EMPTY) {
                        if (sq == from_sqr && !saw_piece) {
                            saw_piece = 1;
                        } else {
                            blocked = 1;
                            break;
                        }
                    }
                    r += sr; f += sf;
                }
                if (!blocked) gives_chk = 1;
            }
            if (!gives_chk && (atype == BISHOP || atype == QUEEN)
                    && abs(dr) == abs(df) && dr != 0) {
                int sr = (dr > 0) ? 1 : -1, sf = (df > 0) ? 1 : -1;
                int r = kr + sr, f = kf + sf;
                int blocked = 0;
                int saw_piece = 0;
                while (r != tr || f != tf) {
                    int sq = make_sq(r, f);
                    int piece = board[sq];
                    if (piece != EMPTY) {
                        if (sq == from_sqr && !saw_piece) {
                            saw_piece = 1;
                        } else {
                            blocked = 1;
                            break;
                        }
                    }
                    r += sr; f += sf;
                }
                if (!blocked) gives_chk = 1;
            }
            if (!gives_chk && atype == KNIGHT) {
                if ((abs(dr)==2 && abs(df)==1) || (abs(dr)==1 && abs(df)==2))
                    gives_chk = 1;
            }
            if (gives_chk) return 80;
        }
    }
    return 0;
}

static void bstop(void) {
    if (gncnt == 0) return;
    int tmsw = bestbl[ply * 2], tmdw = bestbl[ply * 2 + 1];
    if (tmsw == 0) return;

    int base = 1;
    for (int i = pdl2_ptr - 1; i >= 0; i -= 2) {
        if (pdl2[i] == 0) { base = i + 2; break; }
    }

    for (int i = base; i <= pdl2_ptr - 1; i += 2) {
        if (pdl2[i] == tmsw && (abs(pdl2[i+1]) & 7) == (abs(tmdw) & 7)) {
            int s_msw = pdl2[pdl2_ptr - 1], s_mdw = pdl2[pdl2_ptr];
            pdl2[pdl2_ptr - 1] = pdl2[i]; pdl2[pdl2_ptr] = pdl2[i+1];
            pdl2[i] = s_msw; pdl2[i+1] = s_mdw;
            break;
        }
    }
}

/* ==================== BOARD DISPLAY ==================== */

static void out_sqr(int sqr) {
    printf("%c%d", 'a' + (sqr % 8), (sqr / 8) + 1);
}

static void outmv(int msw, int mdw) {
    int to, from;
    split(msw, &to, &from);
    int sp = (mdw >= 0) ? (mdw & 7) : ((-mdw) & 7);
    if (mdw >= 0 && sp == 2) { printf("O-O"); return; }
    if (mdw >= 0 && sp == 1) { printf("O-O-O"); return; }
    out_sqr(from);
    printf("%c", (mdw < 0) ? 'x' : '-');
    out_sqr(to);
    if (sp >= 4 && sp <= 7) {
        printf("=");
        switch(sp) { case 4: printf("N"); break; case 5: printf("B"); break; case 6: printf("R"); break; case 7: printf("Q"); break; }
    }
}

static void display(void) {
    printf("\n");
    for (int r = 7; r >= 0; r--) {
        for (int f = 0; f < 8; f++) {
            int p = board[r * 8 + f];
            if (p == EMPTY) printf("%s", ((r + f) % 2 == 0) ? "**" : "--");
            else printf("%c%c", (p > 0) ? 'W' : 'B', " PNBRQK"[abs(p)]);
            if (f < 7) printf(" ");
        }
        printf("\n");
    }
    printf("\n");
}

/* ==================== MOVE PARSING (unchanged from original) ==================== */

static int parse_square(const char *str) {
    if (!str || strlen(str) < 2) return -1;
    char f_char = tolower(str[0]);
    char r_char = str[1];
    if (f_char < 'a' || f_char > 'h') return -1;
    if (r_char < '1' || r_char > '8') return -1;
    int f = f_char - 'a';
    int r = r_char - '1';
    return make_sq(r, f);
}

static int parse_algebraic_move(const char *move_str, int *msw, int *mdw) {
    char clean[32];
    int j = 0;
    for (int i = 0; move_str[i]; i++) if (!isspace(move_str[i])) clean[j++] = move_str[i];
    clean[j] = '\0';
    int len = strlen(clean);
    
    if (strcmp(clean, "O-O") == 0 || strcmp(clean, "0-0") == 0) {
        int ks = (whose == 0) ? 4 : 60;
        *msw = (ks << 6) | ((ks + 2) & 0x3F); *mdw = 2; return 1;
    }
    if (strcmp(clean, "O-O-O") == 0 || strcmp(clean, "0-0-0") == 0) {
        int ks = (whose == 0) ? 4 : 60;
        *msw = (ks << 6) | ((ks - 2) & 0x3F); *mdw = 1; return 1;
    }
    if (len >= 4) {
        char fs[3] = {clean[0], clean[1], 0}, ts[3] = {clean[2], clean[3], 0};
        int fsq = parse_square(fs), tsq = parse_square(ts);
        if (fsq >= 0 && tsq >= 0) {
            *msw = (fsq << 6) | (tsq & 0x3F);
            *mdw = (board[tsq] != EMPTY) ? -1 : 0;
            if (abs(board[fsq]) == KING && abs((fsq % 8) - (tsq % 8)) == 2) {
                *mdw = (tsq > fsq) ? 2 : 1;
            } else if (len >= 5) {
                int pcode;
                switch(tolower(clean[4])) {
                    case 'n': pcode = 4; break;
                    case 'b': pcode = 5; break;
                    case 'r': pcode = 6; break;
                    default:  pcode = 7; break;
                }
                *mdw = (board[tsq] != EMPTY) ? -pcode : pcode;
            }
            return 1;
        }
    }
    if (len >= 2) {
        char pc = 'P';
        int si = 0;
        if (isalpha(clean[0]) && strchr("NBRQK", toupper(clean[0]))) { pc = toupper(clean[0]); si = 1; }
        if (pc == 'P' && len >= 3 && clean[1] == 'x') si = 2;
        if (len >= si + 2) {
            int tf = clean[si] - 'a', tr = clean[si + 1] - '1';
            if (tf >= 0 && tf < 8 && tr >= 0 && tr < 8) {
                int tsq = make_sq(tr, tf), pt = 0;
                switch(pc) {
                    case 'N': pt = KNIGHT; break;
                    case 'B': pt = BISHOP; break;
                    case 'R': pt = ROOK; break;
                    case 'Q': pt = QUEEN; break;
                    case 'K': pt = KING; break;
                    default: pt = PAWN; break;
                }
                init_pdl2(); gnmvsm();
                int found = 0;
                while (pdl2_ptr >= 0 && !found) {
                    int tmdw = pop2(), tmsw = pop2();
                    if (tmsw == 0) break;
                    int tto, tfrom; split(tmsw, &tto, &tfrom);
                    if (tto == tsq && abs(board[tfrom]) == pt) {
                        if (pt == PAWN && si == 2 && (tfrom % 8) != (clean[0] - 'a')) continue;
                        *msw = tmsw; *mdw = tmdw; found = 1; break;
                    }
                }
                popout();
                if (found) return 1;
            }
        }
    }
    return 0;
}

static int inmv(void) {
    int msw, mdw;
    if (!parse_algebraic_move(input_buffer, &msw, &mdw)) return 0;
    init_pdl2();
    gnmvsm();
    int found = 0;
    while (pdl2_ptr >= 0) {
        int tmdw = pop2(), tmsw = pop2();
        if (tmsw == 0) break;
        int sp_gen    = abs(tmdw) & 7;
        int sp_parsed = abs(mdw)  & 7;
        int type_match = (sp_parsed >= 4) ? (sp_gen == sp_parsed) : 1;
        if (tmsw == msw && type_match) {
            to_mak1 = tmsw; to_mak2 = tmdw; found = 1; break;
        }
    }
    init_pdl2();
    if (!found) return 0;
    mk_mv();
    return 1;
}

/* ==================== POSITION INPUT ==================== */

static void input_position(void) {
    char line[256];
    printf("> "); fflush(stdout);
    if (!fgets(line, sizeof(line), stdin)) return;
    line[strcspn(line, "\n")] = '\0';
    int rank = 7, file = 0;
    for (char *p = line; *p; p++) {
        if (*p == '/') { rank--; file = 0; continue; }
        if (isdigit(*p)) {
            int e = *p - '0';
            for (int i = 0; i < e && file < 8; i++) board[make_sq(rank, file++)] = EMPTY;
        } else if (isalpha(*p)) {
            int pv = 0;
            switch(toupper(*p)) {
                case 'P': pv = PAWN; break;
                case 'N': pv = KNIGHT; break;
                case 'B': pv = BISHOP; break;
                case 'R': pv = ROOK; break;
                case 'Q': pv = QUEEN; break;
                case 'K': pv = KING; break;
            }
            if (pv) board[make_sq(rank, file++)] = isupper(*p) ? pv : -pv;
        }
    }
    pw = 0; wking = bking = -1;
    for (int i = 0; i < BOARD_SIZE; i++) {
        if (board[i] != EMPTY) {
            int av = abs(board[i]);
            pw += (board[i] > 0) ? piece_value[av] : -piece_value[av];
            if (av == KING) { if (board[i] > 0) wking = i; else bking = i; }
        }
    }
    wpsw = bpsw = last_move = 0; domap = 1;
    invalidate_eval_cache();
    display();
}

/* ==================== COMMAND HANDLING ==================== */

static void show_help(void) {
    printf("\nCHEKMO-II Commands:\n");
    printf("==================\n");
    printf("  PW / white      - Computer plays white\n");
    printf("  PB / black      - Computer plays black\n");
    printf("  PN / neither    - Computer plays neither\n");
    printf("  BD / board      - Display board\n");
    printf("  IP / input      - Input position (Forsyth)\n");
    printf("  RE / reset      - Reset/Resign (new game)\n");
    printf("  MV / move       - Force computer to move\n");
    printf("  SK / skip       - Skip a move\n");
    printf("  BM / blitz      - Blitz mode (fast, 0.5s)\n");
    printf("  TM / tournament - Tournament mode (use current ST time)\n");
    printf("  ST <secs>       - Set think time per move (default: 5)\n");
    printf("  HELP / ?        - Show this help\n");
    printf("  QUIT / exit     - Exit program\n\n");
    printf("Move Formats: e2e4, Nf3, exd5, O-O, e7e8q, etc.\n\n");
}

static void handle_command(const char *cmd) {
    char lc[32];
    int i;
    for (i = 0; cmd[i] && i < 31; i++) lc[i] = tolower(cmd[i]);
    lc[i] = '\0';
    
    if (strcmp(lc, "pw") == 0 || strcmp(lc, "white") == 0) {
        whowhi = 1; whoblk = 0; computer_side = WB_WHITE;
        printf("Computer will play white.\n");
    } else if (strcmp(lc, "pb") == 0 || strcmp(lc, "black") == 0) {
        whowhi = 0; whoblk = 1; computer_side = WB_BLACK;
        printf("Computer will play black.\n");
    } else if (strcmp(lc, "pn") == 0 || strcmp(lc, "neither") == 0) {
        whowhi = whoblk = 0;
        printf("Computer will not play.\n");
    } else if (strcmp(lc, "bd") == 0 || strcmp(lc, "board") == 0 || strcmp(lc, "display") == 0) {
        display();
    } else if (strcmp(lc, "ip") == 0 || strcmp(lc, "input") == 0) {
        input_position();
    } else if (strcmp(lc, "re") == 0 || strcmp(lc, "reset") == 0 || strcmp(lc, "resign") == 0) {
        setbrd(); whose = 0; whowhi = whoblk = 0; blitz_mode = 0; depth = 3;
        printf("New game started.\n"); display();
    } else if (strcmp(lc, "mv") == 0 || strcmp(lc, "move") == 0) {
        if ((whose == 0 && whowhi) || (whose != 0 && whoblk)) {
            depth = blitz_mode ? 1 : 3; ply = 0; uval1 = MAX_SCORE; cval1 = -MAX_SCORE;
            search_aborted = 0;
            if (setjmp(search_abort_jmp) == 0) {
                looka(); 
                
                {
                    int best_msw = to_mak1;
                    int best_mdw = to_mak2;
                    int valid = 0;
                    init_pdl2();
                    gnmvsm();
                    while (pdl2_ptr >= 0) {
                        int tmdw = pop2(), tmsw = pop2();
                        if (tmsw == 0) break;
                        if (tmsw == best_msw) {
                            int sp_gen  = (tmdw < 0) ? 0 : (tmdw & 7);
                            int sp_best = (best_mdw < 0) ? 0 : (best_mdw & 7);
                            if ((sp_best >= 4 && sp_gen == sp_best) || sp_best < 4) {
                                valid = 1;
                                to_mak2 = tmdw;
                                break;
                            }
                        }
                    }
                    init_pdl2();
                    if (!valid && best_msw != 0) {
                        depth = 1; ply = 0; uval1 = MAX_SCORE; cval1 = -MAX_SCORE;
                        init_pdl2();
                        if (setjmp(search_abort_jmp) == 0) {
                            looka();
                        }
                    }
                }
                
                mk_mv(); 
                outmv(to_mak1, to_mak2); 
                printf("\n"); 
                display();
            } else {
                printf("I RESIGN (search overflow)\n");
            }
        } else printf("Computer is not configured to play this side.\n");
    } else if (strcmp(lc, "sk") == 0 || strcmp(lc, "skip") == 0) {
        whose = (whose == 0) ? -1 : 0; last_move = 0;
        printf("Move skipped. It is now %s's turn.\n", (whose == 0) ? "white" : "black");
    } else if (strcmp(lc, "bm") == 0 || strcmp(lc, "blitz") == 0) {
        depth = 1; blitz_mode = 1;
        printf("Blitz mode enabled (0.5s per move).\n");
    } else if (strcmp(lc, "tm") == 0 || strcmp(lc, "tournament") == 0) {
        depth = 3; blitz_mode = 0;
        printf("Tournament mode enabled (%ds per move).\n", console_think_ms / 1000);
    } else if (strncmp(lc, "st", 2) == 0 && (lc[2] == ' ' || lc[2] == '\0')) {
        int secs = (lc[2] == ' ') ? atoi(lc + 3) : 0;
        if (secs >= 1 && secs <= 300) {
            console_think_ms = secs * 1000;
            blitz_mode = 0;
            printf("Think time set to %d second%s per move.\n", secs, secs==1?"":"s");
        } else {
            printf("Usage: st <seconds>  (1-300, current: %d)\n", console_think_ms/1000);
        }
    } else if (strcmp(lc, "help") == 0 || strcmp(lc, "?") == 0) {
        show_help();
    } else if (strcmp(lc, "quit") == 0 || strcmp(lc, "exit") == 0) {
        printf("Goodbye!\n"); exit(0);
    } else {
        if (isalpha(lc[0]) && strchr("abcdefghknbrq", lc[0]))
            printf("? Invalid move: %s\nCheck legality or try coordinate format (e2e4).\n", cmd);
        else
            printf("Unknown command: %s\nType 'help' for available commands.\n", cmd);
    }
}

/* ==================== WINBOARD PROTOCOL ==================== */

static void wb_send_move(int msw, int mdw) {
    int sp = abs(mdw) & 7;
    int to, from;
    split(msw, &to, &from);
    printf("move %c%d%c%d", 'a' + (from % 8), (from / 8) + 1, 'a' + (to % 8), (to / 8) + 1);
    if (sp >= 4 && sp <= 7) printf("%c", (sp == 4) ? 'n' : (sp == 5) ? 'b' : (sp == 6) ? 'r' : 'q');
    printf("\n"); fflush(stdout);
}

static void print_coord_move(int msw, int mdw) {
    int to, from;
    int sp = (mdw >= 0) ? (mdw & 7) : ((-mdw) & 7);
    split(msw, &to, &from);
    if (mdw >= 0 && sp == 2) { printf("O-O"); return; }
    if (mdw >= 0 && sp == 1) { printf("O-O-O"); return; }
    printf("%c%d%c%d", 'a' + (from % 8), (from / 8) + 1, 'a' + (to % 8), (to / 8) + 1);
    if (sp >= 4 && sp <= 7)
        printf("%c", (sp == 4) ? 'n' : (sp == 5) ? 'b' : (sp == 6) ? 'r' : 'q');
}

/* wb_setboard with proper initialization */
static void wb_setboard(const char *fen) {
    for (int i = 0; i < BOARD_SIZE; i++) board[i] = EMPTY;
    int rank = 7, file = 0;
    for (const char *p = fen; *p && *p != ' '; p++) {
        if (*p == '/') { rank--; file = 0; continue; }
        if (isdigit(*p)) { int e = *p - '0'; for (int i = 0; i < e && file < 8; i++) board[make_sq(rank, file++)] = EMPTY; }
        else if (isalpha(*p)) {
            int pv = 0;
            switch(toupper(*p)) {
                case 'P': pv = PAWN; break; case 'N': pv = KNIGHT; break;
                case 'B': pv = BISHOP; break; case 'R': pv = ROOK; break;
                case 'Q': pv = QUEEN; break; case 'K': pv = KING; break;
            }
            if (pv) board[make_sq(rank, file++)] = isupper(*p) ? pv : -pv;
        }
    }
    pw = 0; wking = bking = -1;
    for (int i = 0; i < BOARD_SIZE; i++) {
        if (board[i] != EMPTY) {
            int av = abs(board[i]);
            pw += (board[i] > 0) ? piece_value[av] : -piece_value[av];
            if (av == KING) { if (board[i] > 0) wking = i; else bking = i; }
        }
    }
    
    wpsw = bpsw = last_move = 0; domap = 1; whose = 0; game_over = 0;
    wcastled = 0; bcastled = 0; halfmove_clock = 0;
    history_ptr = 0;
    memset(pos_history, 0, sizeof(pos_history));
    invalidate_eval_cache();
    push_position_hash();
    
    const char *fp = fen;
    while (*fp && *fp != ' ') fp++;
    if (*fp == ' ') {
        fp++;
        if (*fp == 'b') whose = -1;
        while (*fp && *fp != ' ') fp++;
    }
    if (*fp == ' ') {
        fp++;
        wpsw = 03000; bpsw = 03000;
        if (*fp != '-') {
            for (const char *cp = fp; *cp && *cp != ' '; cp++) {
                switch (*cp) {
                    case 'K': wpsw &= ~02000; break;
                    case 'Q': wpsw &= ~01000; break;
                    case 'k': bpsw &= ~02000; break;
                    case 'q': bpsw &= ~01000; break;
                }
            }
        }
        while (*fp && *fp != ' ') fp++;
    }
    if (*fp == ' ') { fp++; while (*fp && *fp != ' ') fp++; }
    if (*fp == ' ') { fp++; halfmove_clock = atoi(fp); }
    
    /* Re-invalidate after parsing castling rights */
    invalidate_eval_cache();
    
    /* Reset killer moves for new position */
    memset(killer_msw, 0, sizeof(killer_msw));
    memset(killer_mdw, 0, sizeof(killer_mdw));
    killers_initialized = 1;
    
    /* Clear PV line storage */
    memset(pv_len, 0, sizeof(pv_len));
}

/* wb_handle_command with proper reset on 'new' */
static void wb_handle_command(const char *cmd) {
    if (strcmp(cmd, "xboard") == 0) { printf("\n"); fflush(stdout); }
    else if (strcmp(cmd, "protover 2") == 0) {
        printf("feature done=0\n");
        printf("feature myname=\"CHEKMO-II\"\n");
        printf("feature variants=\"normal\"\n");
        printf("feature colors=0\n");
        printf("feature usermove=1\n");
        printf("feature setboard=1\n");
        printf("feature time=1\n");
        printf("feature ping=1\n");
        printf("feature analyze=0\n");
        printf("feature post=1\n");  
        printf("feature done=1\n");
        fflush(stdout);
    }
    else if (strcmp(cmd, "new") == 0) {
        setbrd(); whose = 0; game_over = 0; wb_force = 0;
        wb_move_num = 0; wb_time_cs = wb_level_base_cs;
        /* Reset killer tables for new game */
        memset(killer_msw, 0, sizeof(killer_msw));
        memset(killer_mdw, 0, sizeof(killer_mdw));
        killers_initialized = 1;
        memset(pv_len, 0, sizeof(pv_len));
    }
    else if (strcmp(cmd, "force") == 0)   { wb_force = 1; }
    else if (strcmp(cmd, "go") == 0)      { wb_force = 0; wb_go(); }
    else if (strcmp(cmd, "post") == 0)    { wb_post_mode = 1; }     
    else if (strcmp(cmd, "nopost") == 0)  { wb_post_mode = 0; }     
    else if (strcmp(cmd, "analyze") == 0) { wb_force = 1; }
    else if (strcmp(cmd, "exit") == 0)    { wb_force = 0; }
    else if (strcmp(cmd, "computer") == 0) { }
    else if (strcmp(cmd, "white") == 0)   { computer_side = WB_WHITE; whose = 0; }
    else if (strcmp(cmd, "black") == 0)   { computer_side = WB_BLACK; whose = 0; }
    else if (strncmp(cmd, "setboard ", 9) == 0) { wb_setboard(cmd + 9); }
    else if (strncmp(cmd, "level ", 6) == 0) {
        wb_parse_level(cmd + 6);
        wb_time_cs = wb_level_base_cs;
    }
    else if (strncmp(cmd, "time ", 5) == 0)  { wb_time_cs  = atoi(cmd + 5); }
    else if (strncmp(cmd, "otim ", 5) == 0)  { wb_otim_cs  = atoi(cmd + 5); }
    else if (strncmp(cmd, "ping ", 5) == 0)  { printf("pong %s\n", cmd + 5); fflush(stdout); }
    else if (strcmp(cmd, "?") == 0)  { }
    else if (strncmp(cmd, "result ", 7) == 0) { game_over = 1; }
    else if (strncmp(cmd, "usermove ", 9) == 0) {
        strcpy(input_buffer, cmd + 9);
        if (inmv()) {
            computer_side = (whose == 0) ? WB_WHITE : WB_BLACK;
            bogus = 1; gnmvsm(); bogus = 0;
            if (cmsw) {
                const char *res = (computer_side == WB_WHITE) ? "0-1 {Black mates}" : "1-0 {White mates}";
                printf("%s\n", res); fflush(stdout); game_over = 1;
            }
            else if (smsw) { printf("1/2-1/2 {Stalemate}\n"); fflush(stdout); game_over = 1; }
            else if (halfmove_clock >= 100) {
                printf("1/2-1/2 {50-move rule}\n"); fflush(stdout); game_over = 1;
            }
            else if (!wb_force && !game_over) {
                wb_do_search();
            }
        } else { printf("Illegal move: %s\n", cmd + 9); fflush(stdout); }
    }
    else if (strcmp(cmd, "quit") == 0 || strcmp(cmd, "resign") == 0) { exit(0); }
    else {
        strcpy(input_buffer, cmd);
        if (inmv()) {
            bogus = 1; gnmvsm(); bogus = 0;
            if (cmsw) {
                const char *res = (computer_side == WB_WHITE) ? "1-0 {White mates}" : "0-1 {Black mates}";
                printf("%s\n", res); fflush(stdout); game_over = 1;
            }
            else if (smsw) { printf("1/2-1/2 {Stalemate}\n"); fflush(stdout); game_over = 1; }
            else if (halfmove_clock >= 100) {
                printf("1/2-1/2 {50-move rule}\n"); fflush(stdout); game_over = 1;
            }
            else if (!wb_force && !game_over) {
                wb_do_search();
            }
        }
    }
}

static void wb_parse_level(const char *args) {
    int mps = 0, base_min = 0, base_sec = 0, inc = 0;
    if (sscanf(args, "%d %d:%d %d", &mps, &base_min, &base_sec, &inc) < 3)
        sscanf(args, "%d %d %d", &mps, &base_min, &inc);
    wb_level_mps     = mps;
    wb_level_base_cs = (base_min * 60 + base_sec) * 100;
    wb_level_inc_cs  = inc * 100;
}

/* ==================== TIME MANAGEMENT ==================== */
#define MIN_TIME_FOR_DEPTH4_CS  200
#define MAX_EMERGENCY_REDUCTION 30
#define TIME_RESERVE_FACTOR     80
#define MAX_MOVE_TIME_CS        1000
#define MIN_MOVE_TIME_CS        50

static int wb_compute_move_time(void) {
    int t = wb_time_cs;
    if (t <= 0) t = wb_level_base_cs > 0 ? wb_level_base_cs : 12000;

    int moves_left;
    if (wb_level_mps > 0) {
        int done = wb_move_num;
        moves_left = wb_level_mps - (done % wb_level_mps);
        if (moves_left <= 0) moves_left = wb_level_mps;
    } else {
        int pieces_left = 0;
        for (int i = 0; i < BOARD_SIZE; i++) {
            if (board[i] != EMPTY && abs(board[i]) != KING) pieces_left++;
        }
        if (pieces_left < 6) {
            moves_left = 20;
        } else if (pieces_left < 12) {
            moves_left = 30;
        } else {
            moves_left = 40;
        }
        moves_left -= wb_move_num;
        if (moves_left < 4) moves_left = 4;
        if (moves_left > 40) moves_left = 40;
    }

    int alloc = (t * TIME_RESERVE_FACTOR / 100) / moves_left;
    alloc += wb_level_inc_cs * 6 / 10;
    
    int pieces_remaining = 0;
    int has_queens = 0;
    for (int i = 0; i < BOARD_SIZE; i++) {
        int p = board[i];
        if (p != EMPTY && abs(p) != KING) {
            pieces_remaining++;
            if (abs(p) == QUEEN) has_queens = 1;
        }
    }
    
    int is_endgame_tactical = (pieces_remaining <= 10) || (!has_queens && pieces_remaining <= 14);
    
    if (alloc > t / 3) {
        alloc = t / 3;
    }
    
    if (is_endgame_tactical) {
        if (t < 300) {
            alloc = 30;
            return alloc;
        } else if (t < 600) {
            alloc = (t / 4) + 30;
        } else {
            if (alloc > 400) alloc = 400;
            if (alloc < 120) alloc = 120;
        }
    } else {
        if (alloc > MAX_MOVE_TIME_CS) alloc = MAX_MOVE_TIME_CS;
        if (alloc < MIN_MOVE_TIME_CS) alloc = MIN_MOVE_TIME_CS;
    }
    
    int material_balance = (computer_side == WB_WHITE) ? pw : -pw;
    if (material_balance < -200 && t < 1000) {
        alloc = alloc * 70 / 100;
        if (alloc < 40) alloc = 40;
    }
    
    if (alloc > t / 2) {
        alloc = t / 2;
    }
    
    if (alloc < 30) alloc = 30;
    
    return alloc;
}

static void wb_do_search(void) {
    volatile int best_msw = 0, best_mdw = 0;

    if (wb_time_cs < 100) {
        init_pdl2();
        gnmvsm();
        while (pdl2_ptr >= 0) {
            int tmdw = pop2(), tmsw = pop2();
            if (tmsw == 0) break;
            best_msw = tmsw;
            best_mdw = tmdw;
            break;
        }
        init_pdl2();
        if (best_msw != 0) {
            to_mak1 = best_msw;
            to_mak2 = best_mdw;
            mk_mv();
            wb_send_move(to_mak1, to_mak2);
            wb_move_num++;
            return;
        }
    }

    int save_board[BOARD_SIZE];
    int save_pw, save_wking, save_bking;
    int save_wpsw, save_bpsw, save_last_move;
    int save_whose, save_pdl1_ptr, save_domap;
    int save_halfmove_clock, save_history_ptr;
    int save_wcastled, save_bcastled;
    memcpy(save_board, board, sizeof(board));
    save_pw = pw; save_wking = wking; save_bking = bking;
    save_wpsw = wpsw; save_bpsw = bpsw; save_last_move = last_move;
    save_whose = whose; save_pdl1_ptr = pdl1_ptr; save_domap = domap;
    save_halfmove_clock = halfmove_clock; save_history_ptr = history_ptr;
    save_wcastled = wcastled; save_bcastled = bcastled;

    int time_cs = wb_compute_move_time();
    search_start_clk = now_ns();
    search_limit_clk = search_start_clk + (int64_t)time_cs * 10000000LL;
    search_use_timer = 1;
    search_nodes = 0;
    memset(bestbl, 0, sizeof(bestbl));

#define RESTORE_STATE() do { \
    memcpy(board, save_board, sizeof(board));   \
    pw = save_pw; wking = save_wking; bking = save_bking; \
    wpsw = save_wpsw; bpsw = save_bpsw; last_move = save_last_move; \
    whose = save_whose; pdl1_ptr = save_pdl1_ptr; domap = save_domap; \
    halfmove_clock = save_halfmove_clock; history_ptr = save_history_ptr; \
    wcastled = save_wcastled; bcastled = save_bcastled; \
    ply = 0; \
} while(0)

    volatile int d;
    volatile int prev_score = 0;
    volatile int64_t iter_limit_clk = search_limit_clk;
    int64_t original_alloc = search_limit_clk - search_start_clk;
    
    int min_depth = 2;
    int pieces_remaining = 0;
    int has_queens = 0;
    for (int i = 0; i < BOARD_SIZE; i++) {
        int p = board[i];
        if (p != EMPTY && abs(p) != KING) {
            pieces_remaining++;
            if (abs(p) == QUEEN) has_queens = 1;
        }
    }
    int is_endgame_tactical = (pieces_remaining <= 10) || (!has_queens && pieces_remaining <= 14);
    
    int time_available = wb_time_cs;
    
    if (is_endgame_tactical) {
        if (time_available >= 600) {
            min_depth = 4;
        } else if (time_available >= 300) {
            min_depth = 3;
        } else {
            min_depth = 2;
        }
    } else {
        if (time_available >= 400) {
            min_depth = 3;
        } else {
            min_depth = 2;
        }
    }
    
    if (time_available < 200) {
        min_depth = 1;
    }
    
    int min_depth_reached = 0;
    int best_score_at_min_depth = 0;
    
    if (!killers_initialized || history_ptr < 5) {
        memset(killer_msw, 0, sizeof(killer_msw));
        memset(killer_mdw, 0, sizeof(killer_mdw));
        killers_initialized = 1;
    }
    
    for (d = 2; d <= MAX_SEARCH_DEPTH; d++) {
        depth = d; ply = 0; base_depth = d;
        if (d >= 4) {
            uval1 = prev_score + 50;
            cval1 = prev_score - 50;
        } else {
            uval1 = MAX_SCORE; cval1 = -MAX_SCORE;
        }
        search_aborted = 0;
        memset(pv_len, 0, sizeof(pv_len));
        init_pdl2();

        int rc = setjmp(search_abort_jmp);
        if (rc == 0) {
            int score = looka();

            if (d >= min_depth && !min_depth_reached) {
                min_depth_reached = 1;
                best_score_at_min_depth = score;
                best_msw = to_mak1;
                best_mdw = to_mak2;
            }

            if (d >= 4 && (score <= cval1 || score >= uval1)) {
                RESTORE_STATE();
                depth = d; ply = 0; uval1 = MAX_SCORE; cval1 = -MAX_SCORE;
                memset(pv_len, 0, sizeof(pv_len));
                init_pdl2();
                if (setjmp(search_abort_jmp) == 0) {
                    score = looka();
                } else {
                    RESTORE_STATE();
                    break;
                }
            }

            if (d >= 3 && score < prev_score - 15) {
                int drop = prev_score - score;
                int num, den;
                if      (drop >= 100) { num = 3; den = 1; }
                else if (drop >=  50) { num = 2; den = 1; }
                else                  { num = 3; den = 2; }
                int64_t new_limit = search_start_clk + original_alloc * num / den;
                int64_t hard_cap  = search_start_clk + original_alloc * 3;
                if (new_limit > hard_cap) new_limit = hard_cap;
                if (search_limit_clk < new_limit)
                    search_limit_clk = new_limit;
                iter_limit_clk = search_limit_clk;
            }

            prev_score = score;
            best_msw = to_mak1; best_mdw = to_mak2;

            for (int pi = 0; pi < MAX_PLY && pi < pv_len[0]; pi++) {
                bestbl[(pi+1)*2]   = pv_msw[0][pi];
                bestbl[(pi+1)*2+1] = pv_mdw[0][pi];
            }

            if (wb_post_mode) {
                int64_t elapsed_ns = now_ns() - search_start_clk;
                long time_cs_out = (long)(elapsed_ns / 10000000LL);
                int cp_score = score;
                printf("%d %d %ld %ld", d, cp_score, time_cs_out, search_nodes);
                for (int i = 0; i < pv_len[0] && i < d; i++) {
                    printf(" "); print_coord_move(pv_msw[0][i], pv_mdw[0][i]);
                }
                printf("\n"); fflush(stdout);
            }
            
        } else {
            if (!min_depth_reached && best_msw != 0) {
                to_mak1 = best_msw;
                to_mak2 = best_mdw;
                RESTORE_STATE();
                break;
            }
            RESTORE_STATE();
            break;
        }

        if (now_ns() >= iter_limit_clk) {
            if (!min_depth_reached && d < min_depth) {
                int64_t extra_time = (now_ns() - search_start_clk) / 2;
                if (extra_time > 0) {
                    search_limit_clk = now_ns() + extra_time;
                    continue;
                }
            }
            break;
        }
    }

    if (best_msw == 0) {
        RESTORE_STATE();
        depth = (min_depth > 3) ? min_depth : 3;
        ply = 0; uval1 = MAX_SCORE; cval1 = -MAX_SCORE;
        init_pdl2();
        if (setjmp(search_abort_jmp) == 0) {
            looka();
            best_msw = to_mak1;
            best_mdw = to_mak2;
        } else {
            RESTORE_STATE();
        }
    }

    RESTORE_STATE();
    search_use_timer = 0;

    {
        int64_t elapsed_ns = now_ns() - search_start_clk;
        int elapsed_cs = (int)(elapsed_ns / 10000000LL);
        
        elapsed_cs = elapsed_cs * 9 / 10;
        if (elapsed_cs < 1) elapsed_cs = 1;
        
        wb_time_cs -= elapsed_cs;
        
        wb_time_cs += wb_level_inc_cs;
        
        if (wb_time_cs < 10) wb_time_cs = 10;
    }

    {
        int valid = 0;
        init_pdl2();
        gnmvsm();

        while (pdl2_ptr >= 0) {
            int tmdw = pop2(), tmsw = pop2();
            if (tmsw == 0) break;

            if (tmsw == best_msw) {
                int sp_gen  = (tmdw < 0) ? 0 : (tmdw & 7);
                int sp_best = (best_mdw < 0) ? 0 : (best_mdw & 7);
                if ((sp_best >= 4 && sp_gen == sp_best) || sp_best < 4) {
                    valid = 1;
                    best_mdw = tmdw;
                    break;
                }
            }
        }
        init_pdl2();

        if (!valid && best_msw != 0) {
            RESTORE_STATE();
            depth = 1; ply = 0; uval1 = MAX_SCORE; cval1 = -MAX_SCORE;
            init_pdl2();
            if (setjmp(search_abort_jmp) == 0) {
                looka();
                best_msw = to_mak1;
                best_mdw = to_mak2;
            } else {
                RESTORE_STATE();
            }
        }

        if (best_msw == 0) {
            init_pdl2();
            gnmvsm();
            while (pdl2_ptr >= 0) {
                int tmdw = pop2(), tmsw = pop2();
                if (tmsw == 0) break;
                best_msw = tmsw;
                best_mdw = tmdw;
                break;
            }
            init_pdl2();
        }
    }

    to_mak1 = best_msw; 
    to_mak2 = best_mdw;
    mk_mv();
    wb_send_move(to_mak1, to_mak2);
    wb_move_num++;

    bogus = 1; gnmvsm(); bogus = 0;

    if (cmsw) {
        const char *res = (computer_side == WB_WHITE) ? "1-0 {White mates}" : "0-1 {Black mates}";
        printf("%s\n", res); fflush(stdout); game_over = 1;
    }
    else if (smsw) { 
        printf("1/2-1/2 {Stalemate}\n"); fflush(stdout); game_over = 1; 
    }
    else if (halfmove_clock >= 100) {
        printf("1/2-1/2 {50-move rule}\n"); fflush(stdout); game_over = 1;
    }
}

static void wb_go(void) {
    if (game_over) return;
    computer_side = (whose == 0) ? WB_WHITE : WB_BLACK;
    wb_do_search();
}

/* ==================== MAIN PROGRAM ==================== */

static void catch_sigint(int s) {
    signal(s, catch_sigint);
}


int main(int argc, char *argv[]) {
    setbuf(stdout, NULL);
    setvbuf(stdout, NULL, _IONBF, 0);
    signal(SIGINT, catch_sigint);

    srand(time(NULL));
    random_val = rand();
    setbrd();
    whose = whowhi = whoblk = 0;
    blitz_mode = 0; depth = 3; ply = 0;
    init_pdl1(); init_pdl2();

    char line[256];
    int in_xboard_session = 0;
    
    /* Check if stdin is coming from a terminal or from pipe/GUI */
    if (!is_stdin_terminal()) {
        /* Input is piped (xboard mode) - read first line to detect xboard */
        if (fgets(line, sizeof(line), stdin)) {
            line[strcspn(line, "\n")] = '\0';
            if (strcmp(line, "xboard") == 0) {
                in_xboard_session = 1;
                wb_handle_command(line);
            } else {
                /* Not xboard but piped - treat as console with initial command */
                in_xboard_session = 0;
                printf("\n  CHEKMO-II - Chess Program (PDP-8 Original by JOHN E. COMEAU 1976)\n");
                printf("  Enhanced version with King Safety improvements - Type 'help' for commands.\n\n");
                display();
                if (strlen(line) > 0) {
                    int probe_msw, probe_mdw;
                    int looks_like_move = parse_algebraic_move(line, &probe_msw, &probe_mdw);
                    if (!looks_like_move) {
                        handle_command(line);
                    } else {
                        strcpy(input_buffer, line);
                        if (inmv()) {
                            display();
                            bogus = 1; gnmvsm(); bogus = 0;
                            if (cmsw) { printf("CHECKMATE\n"); setbrd(); whose = 0; }
                            if (smsw) { printf("STALEMATE\n"); setbrd(); whose = 0; }
                            if (halfmove_clock >= 100) { printf("DRAW (50-move rule)\n"); setbrd(); whose = 0; }
                        }
                    }
                }
            }
        }
    } else {
        /* Normal console mode (terminal input) - show banner immediately */
        in_xboard_session = 0;
        printf("\n  CHEKMO-II - Chess Program (PDP-8 Original by JOHN E. COMEAU 1976)\n");
        printf("  Enhanced version with evaluation improvements - Type 'help' for commands.\n\n");
        display();
    }

    while (1) {
        /* If we're in an xboard session, always use xboard handling */
        if (in_xboard_session) {
            if (!fgets(line, sizeof(line), stdin)) break;
            line[strcspn(line, "\n")] = '\0';
            wb_handle_command(line);
        } else {
            /* Console mode handling */
            while (!game_over && ((whose == 0 && whowhi) || (whose != 0 && whoblk))) {
                printf("%s. COMPUTER MOVES...\n", (whose == 0) ? "W" : "B");
                init_pdl2();
                depth = blitz_mode ? 1 : 3; ply = 0; uval1 = MAX_SCORE; cval1 = -MAX_SCORE;
                search_aborted = 0;
                if (setjmp(search_abort_jmp) == 0) {
                    {
                        int save_board_c[BOARD_SIZE];
                        int save_pw_c, save_wking_c, save_bking_c;
                        int save_wpsw_c, save_bpsw_c, save_lm_c, save_hmc_c;
                        int save_whose_c, save_pdl1_c, save_domap_c;
                        int save_hist_c, save_wcast_c, save_bcast_c;
                        memcpy(save_board_c, board, sizeof(board));
                        save_pw_c = pw; save_wking_c = wking; save_bking_c = bking;
                        save_wpsw_c = wpsw; save_bpsw_c = bpsw;
                        save_lm_c = last_move; save_hmc_c = halfmove_clock;
                        save_whose_c = whose; save_pdl1_c = pdl1_ptr; save_domap_c = domap;
                        save_hist_c = history_ptr; save_wcast_c = wcastled; save_bcast_c = bcastled;
#define RESTORE_CONSOLE() do { \
    memcpy(board, save_board_c, sizeof(board)); \
    pw = save_pw_c; wking = save_wking_c; bking = save_bking_c; \
    wpsw = save_wpsw_c; bpsw = save_bpsw_c; \
    last_move = save_lm_c; halfmove_clock = save_hmc_c; \
    whose = save_whose_c; pdl1_ptr = save_pdl1_c; domap = save_domap_c; \
    history_ptr = save_hist_c; wcastled = save_wcast_c; bcastled = save_bcast_c; \
    ply = 0; \
} while(0)
                        int64_t think_ns = blitz_mode ? 500000000LL
                                                      : (int64_t)console_think_ms * 1000000LL;
                        search_start_clk = now_ns();
                        search_limit_clk = search_start_clk + think_ns;
                        search_use_timer = 1;
                        search_nodes = 0;
                        memset(bestbl, 0, sizeof(bestbl));
                        volatile int cd; volatile int cprev = 0;
                        int console_start_d = blitz_mode ? 1 : 2;
                        
                        if (!killers_initialized || history_ptr < 5) {
                            memset(killer_msw, 0, sizeof(killer_msw));
                            memset(killer_mdw, 0, sizeof(killer_mdw));
                            killers_initialized = 1;
                        }
                        
                        for (cd = console_start_d; cd <= MAX_SEARCH_DEPTH; cd++) {
                            depth = cd; ply = 0; base_depth = cd;
                            if (cd >= 4) { uval1 = cprev+50; cval1 = cprev-50; }
                            else         { uval1 = MAX_SCORE;    cval1 = -MAX_SCORE;   }
                            search_aborted = 0;
                            memset(pv_len, 0, sizeof(pv_len));
                            init_pdl2();
                            int crc = setjmp(search_abort_jmp);
                            if (crc == 0) {
                                int cscore = looka();
                                if (cd >= 4 && (cscore <= cval1 || cscore >= uval1)) {
                                    RESTORE_CONSOLE();
                                    depth = cd; ply = 0; uval1 = MAX_SCORE; cval1 = -MAX_SCORE;
                                    memset(pv_len, 0, sizeof(pv_len)); init_pdl2();
                                    if (setjmp(search_abort_jmp) == 0) cscore = looka();
                                    else { RESTORE_CONSOLE(); break; }
                                }
                                cprev = cscore;
                            } else { RESTORE_CONSOLE(); break; }
                            if (now_ns() >= search_limit_clk) break;
                        }
                        search_use_timer = 0;
                        RESTORE_CONSOLE();
#undef RESTORE_CONSOLE
                        to_mak1 = bestbl[2]; to_mak2 = bestbl[3];
                        if (to_mak1 == 0) {
                            depth = 3; ply = 0; uval1 = MAX_SCORE; cval1 = -MAX_SCORE;
                            init_pdl2(); looka();
                        }
                    }
                    mk_mv(); outmv(to_mak1, to_mak2); printf("\n"); display();
                    bogus = 1; gnmvsm(); bogus = 0;
                    if (cmsw) { printf("CHECKMATE\n"); setbrd(); whose = 0; game_over = 0; break; }
                    else if (smsw) { printf("STALEMATE\n"); setbrd(); whose = 0; game_over = 0; break; }
                    else if (halfmove_clock >= 100) { printf("DRAW (50-move rule)\n"); setbrd(); whose = 0; game_over = 0; break; }
                } else {
                    printf("I RESIGN (search overflow)\n"); setbrd(); whose = 0; break;
                }
            }
            if (!((whose == 0 && whowhi) || (whose != 0 && whoblk))) {
                printf("%s. YOUR MOVE? ", (whose == 0) ? "W" : "B");
                fflush(stdout);
            }
            if (!fgets(line, sizeof(line), stdin)) break;
            line[strcspn(line, "\n")] = '\0';
            if (strlen(line) == 0) continue;

            {
                int probe_msw, probe_mdw;
                int looks_like_move = parse_algebraic_move(line, &probe_msw, &probe_mdw);
                if (!looks_like_move) {
                    handle_command(line);
                    continue;
                }
            }

            if ((whose == 0 && !whowhi) || (whose != 0 && !whoblk)) {
                strcpy(input_buffer, line);
                if (inmv()) {
                    display();
                    bogus = 1; gnmvsm(); bogus = 0;
                    if (cmsw) { printf("CHECKMATE\n"); setbrd(); whose = 0; continue; }
                    if (smsw) { printf("STALEMATE\n"); setbrd(); whose = 0; continue; }
                    if (halfmove_clock >= 100) { printf("DRAW (50-move rule)\n"); setbrd(); whose = 0; continue; }
                } else { printf("? Invalid move. Try again.\n"); continue; }
            }
        }
    }
    return 0;
}