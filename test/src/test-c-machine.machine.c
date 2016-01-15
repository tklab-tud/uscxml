#include <stdint.h> // explicit types
#include <stddef.h> // NULL

#define IS_SET(idx, bitset)   ((bitset[idx >> 3] &  (1 << (idx & 7))) != 0)
#define SET_BIT(idx, bitset)    bitset[idx >> 3] |= (1 << (idx & 7));
#define CLEARBIT(idx, bitset)   bitset[idx >> 3] &= (1 << (idx & 7)) ^ 0xFF;

#ifdef __GNUC__
#define likely(x)       (__builtin_expect(!!(x), 1))
#define unlikely(x)     (__builtin_expect(!!(x), 0))
#else
#define likely(x)       (x)
#define unlikely(x)     (x)
#endif

// error return codes
#define SCXML_ERR_OK                0
#define SCXML_ERR_IDLE              1
#define SCXML_ERR_DONE              2
#define SCXML_ERR_MISSING_CALLBACK  3
#define SCXML_ERR_FOREACH_DONE      4
#define SCXML_ERR_EXEC_CONTENT      5
#define SCXML_ERR_INVALID_TARGET    6
#define SCXML_ERR_INVALID_TYPE      7
#define SCXML_ERR_UNSUPPORTED       8

#define SCXML_MACHINE_NAME ""
#define SCXML_NUMBER_STATES 11
#define SCXML_NUMBER_TRANSITIONS 13

#define SCXML_TRANS_SPONTANEOUS      0x01
#define SCXML_TRANS_TARGETLESS       0x02
#define SCXML_TRANS_INTERNAL         0x04
#define SCXML_TRANS_HISTORY          0x08
#define SCXML_TRANS_INITIAL          0x10

#define SCXML_STATE_ATOMIC           0x01
#define SCXML_STATE_PARALLEL         0x02
#define SCXML_STATE_COMPOUND         0x03
#define SCXML_STATE_FINAL            0x04
#define SCXML_STATE_HISTORY_DEEP     0x05
#define SCXML_STATE_HISTORY_SHALLOW  0x06
#define SCXML_STATE_INITIAL          0x07

#define SCXML_CTX_PRISTINE           0x00
#define SCXML_CTX_SPONTANEOUS        0x01
#define SCXML_CTX_INITIALIZED        0x02
#define SCXML_CTX_TOP_LEVEL_FINAL    0x04
#define SCXML_CTX_TRANSITION_FOUND   0x08

#define ELEM_DATA_IS_SET(data) (data->id != NULL)
#define ELEM_DONEDATA_IS_SET(donedata) (donedata->content != NULL || donedata->contentexpr != NULL || donedata->params != NULL)
#define ELEM_PARAM_IS_SET(param) (param->name != NULL)


typedef struct scxml_transition scxml_transition;
typedef struct scxml_state scxml_state;
typedef struct scxml_ctx scxml_ctx;
typedef struct scxml_invoke scxml_invoke;

typedef struct scxml_elem_send scxml_elem_send;
typedef struct scxml_elem_param scxml_elem_param;
typedef struct scxml_elem_data scxml_elem_data;
typedef struct scxml_elem_donedata scxml_elem_donedata;
typedef struct scxml_elem_foreach scxml_elem_foreach;

typedef void* (*dequeue_internal_cb_t)(const scxml_ctx* ctx);
typedef void* (*dequeue_external_cb_t)(const scxml_ctx* ctx);
typedef int (*is_enabled_cb_t)(const scxml_ctx* ctx, const scxml_transition* transition, const void* event);
typedef int (*is_true_cb_t)(const scxml_ctx* ctx, const char* expr);
typedef int (*exec_content_t)(const scxml_ctx* ctx, const scxml_state* state, const void* event);
typedef int (*raise_done_event_t)(const scxml_ctx* ctx, const scxml_state* state, const scxml_elem_donedata* donedata);
typedef int (*invoke_t)(const scxml_ctx* ctx, const scxml_state* s, const scxml_invoke* x);

typedef int (*exec_content_log_t)(const scxml_ctx* ctx, const char* label, const char* expr);
typedef int (*exec_content_raise_t)(const scxml_ctx* ctx, const char* event);
typedef int (*exec_content_send_t)(const scxml_ctx* ctx, const scxml_elem_send* send);
typedef int (*exec_content_foreach_init_t)(const scxml_ctx* ctx, const scxml_elem_foreach* foreach);
typedef int (*exec_content_foreach_next_t)(const scxml_ctx* ctx, const scxml_elem_foreach* foreach);
typedef int (*exec_content_foreach_done_t)(const scxml_ctx* ctx, const scxml_elem_foreach* foreach);
typedef int (*exec_content_assign_t)(const scxml_ctx* ctx, const char* location, const char* expr);
typedef int (*exec_content_init_t)(const scxml_ctx* ctx, const scxml_elem_data* data);
typedef int (*exec_content_cancel_t)(const scxml_ctx* ctx, const char* sendid, const char* sendidexpr);
typedef int (*exec_content_finalize_t)(const scxml_ctx* ctx, const scxml_invoke* invoker, const void* event);
typedef int (*exec_content_script_t)(const scxml_ctx* ctx, const char* src, const char* content);

struct scxml_elem_data {
    const char* id;
    const char* src;
    const char* expr;
    const char* content;
};

struct scxml_state {
    const char* name; // eventual name
    uint16_t parent; // parent
    exec_content_t on_entry; // on entry handlers
    exec_content_t on_exit; // on exit handlers
    invoke_t invoke; // invocations
    char children[2]; // all children
    char completion[2]; // default completion
    char ancestors[2]; // all ancestors
    const scxml_elem_data* data;
    uint8_t type; // atomic, parallel, compound, final, history
};

struct scxml_transition {
    uint16_t source;
    char target[2];
    const char* event;
    const char* condition;
    exec_content_t on_transition;
    uint8_t type;
    char conflicts[2];
    char exit_set[2];
};

struct scxml_elem_foreach {
    const char* array;
    const char* item;
    const char* index;
};

struct scxml_elem_param {
    const char* name;
    const char* expr;
    const char* location;
};

struct scxml_elem_donedata {
    uint16_t source;
    const char* content;
    const char* contentexpr;
    const scxml_elem_param* params;
};

struct scxml_elem_invoke {
    const char* type;
    const char* typeexpr;
    const char* src;
    const char* srcexpr;
    const char* id;
    const char* idlocation;
    const char* namelist;
    uint8_t autoforward;
    const scxml_elem_param* params;
    const exec_content_finalize_t* finalize;
    const char* content;
    const char* contentexpr;
    void* user_data;
};

struct scxml_elem_send {
    const char* event;
    const char* eventexpr;
    const char* target;
    const char* targetexpr;
    const char* type;
    const char* typeexpr;
    const char* id;
    const char* idlocation;
    const char* delay;
    const char* delayexpr;
    const char* namelist;
    const char* content;
    const char* contentexpr;
    const scxml_elem_param* params;
    void* user_data;
};

struct scxml_ctx {
    uint8_t flags;

    char config[2];
    char history[2];
    char pending_invokes[2];
    char initialized_data[2];

    void* user_data;
    void* event;

    dequeue_internal_cb_t dequeue_internal;
    dequeue_external_cb_t dequeue_external;
    is_enabled_cb_t is_enabled;
    is_true_cb_t is_true;
    raise_done_event_t raise_done_event;

    exec_content_log_t exec_content_log;
    exec_content_raise_t exec_content_raise;
    exec_content_send_t exec_content_send;
    exec_content_foreach_init_t exec_content_foreach_init;
    exec_content_foreach_next_t exec_content_foreach_next;
    exec_content_foreach_done_t exec_content_foreach_done;
    exec_content_assign_t exec_content_assign;
    exec_content_init_t exec_content_init;
    exec_content_cancel_t exec_content_cancel;
    exec_content_script_t exec_content_script;
    invoke_t invoke;
};

static scxml_elem_data scxml_elem_datas[2] = {
    { "Var1", NULL, "0", NULL },
    { NULL, NULL, NULL, NULL }
};

static scxml_elem_send scxml_elem_sends[1] = {
    { "timeout", NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL, "'1s'", NULL, NULL, NULL, NULL, NULL }
};

static scxml_elem_donedata scxml_elem_donedatas[1] = {
    { 0, NULL, NULL }
};

static int global_script(const scxml_ctx* ctx, const scxml_state* state, const void* event) {
    return SCXML_ERR_OK;
}

static int s0_on_exit_0(const scxml_ctx* ctx, const scxml_state* state, const void* event) {
    int err = SCXML_ERR_OK;
    if likely(ctx->exec_content_assign != NULL) {
        if ((ctx->exec_content_assign(ctx, "Var1", "Var1 + 1")) != SCXML_ERR_OK) return err;
    } else {
        return SCXML_ERR_MISSING_CALLBACK;
    }
    if likely(ctx->exec_content_log != NULL) {
        if unlikely((ctx->exec_content_log(ctx, "Var1 is", "Var1")) != SCXML_ERR_OK) return err;
    } else {
        return SCXML_ERR_MISSING_CALLBACK;
    }
    return SCXML_ERR_OK;
}

static int s0_on_exit(const scxml_ctx* ctx, const scxml_state* state, const void* event) {
    s0_on_exit_0(ctx, state, event);
    return SCXML_ERR_OK;
}

static int s0_on_entry_0(const scxml_ctx* ctx, const scxml_state* state, const void* event) {
    int err = SCXML_ERR_OK;
    if likely(ctx->exec_content_send != NULL) {
        if ((ctx->exec_content_send(ctx, &scxml_elem_sends[0])) != SCXML_ERR_OK) return err;
    } else {
        return SCXML_ERR_MISSING_CALLBACK;
    }
    if likely(ctx->exec_content_raise != NULL) {
        if unlikely((ctx->exec_content_raise(ctx, "event1")) != SCXML_ERR_OK) return err;
    } else {
        return SCXML_ERR_MISSING_CALLBACK;
    }
    return SCXML_ERR_OK;
}

static int s0_initial(const scxml_ctx* ctx, const scxml_state* state, const void* event) {
    int err = SCXML_ERR_OK;
    if likely(ctx->exec_content_raise != NULL) {
        if unlikely((ctx->exec_content_raise(ctx, "event2")) != SCXML_ERR_OK) return err;
    } else {
        return SCXML_ERR_MISSING_CALLBACK;
    }
    if likely(ctx->exec_content_log != NULL) {
        if unlikely((ctx->exec_content_log(ctx, "initial transition in s0", NULL)) != SCXML_ERR_OK) return err;
    } else {
        return SCXML_ERR_MISSING_CALLBACK;
    }
    return SCXML_ERR_OK;
}

static int s0_on_entry(const scxml_ctx* ctx, const scxml_state* state, const void* event) {
    s0_on_entry_0(ctx, state, event);
    s0_initial(ctx, state, event);
    return SCXML_ERR_OK;
}

static int s03_on_entry_0(const scxml_ctx* ctx, const scxml_state* state, const void* event) {
    int err = SCXML_ERR_OK;
    if likely(ctx->exec_content_log != NULL) {
        if unlikely((ctx->exec_content_log(ctx, "Var1 when entering s03", "Var1")) != SCXML_ERR_OK) return err;
    } else {
        return SCXML_ERR_MISSING_CALLBACK;
    }
    return SCXML_ERR_OK;
}

static int s03_on_entry(const scxml_ctx* ctx, const scxml_state* state, const void* event) {
    s03_on_entry_0(ctx, state, event);
    return SCXML_ERR_OK;
}

static int pass_on_entry_0(const scxml_ctx* ctx, const scxml_state* state, const void* event) {
    int err = SCXML_ERR_OK;
    if likely(ctx->exec_content_log != NULL) {
        if unlikely((ctx->exec_content_log(ctx, "Outcome", "'pass'")) != SCXML_ERR_OK) return err;
    } else {
        return SCXML_ERR_MISSING_CALLBACK;
    }
    return SCXML_ERR_OK;
}

static int pass_on_entry(const scxml_ctx* ctx, const scxml_state* state, const void* event) {
    pass_on_entry_0(ctx, state, event);
    return SCXML_ERR_OK;
}

static int fail_on_entry_0(const scxml_ctx* ctx, const scxml_state* state, const void* event) {
    int err = SCXML_ERR_OK;
    if likely(ctx->exec_content_log != NULL) {
        if unlikely((ctx->exec_content_log(ctx, "Outcome", "'fail'")) != SCXML_ERR_OK) return err;
    } else {
        return SCXML_ERR_MISSING_CALLBACK;
    }
    return SCXML_ERR_OK;
}

static int fail_on_entry(const scxml_ctx* ctx, const scxml_state* state, const void* event) {
    fail_on_entry_0(ctx, state, event);
    return SCXML_ERR_OK;
}

static int sh1_transition0_on_trans(const scxml_ctx* ctx, const scxml_state* state, const void* event) {
    int err = SCXML_ERR_OK;
    if likely(ctx->exec_content_raise != NULL) {
        if unlikely((ctx->exec_content_raise(ctx, "event3")) != SCXML_ERR_OK) return err;
    } else {
        return SCXML_ERR_MISSING_CALLBACK;
    }
    if likely(ctx->exec_content_log != NULL) {
        if unlikely((ctx->exec_content_log(ctx, "history transition in sh1", NULL)) != SCXML_ERR_OK) return err;
    } else {
        return SCXML_ERR_MISSING_CALLBACK;
    }
    return SCXML_ERR_OK;
}

static scxml_state scxml_states[11] = {
    { NULL, 0, NULL, NULL, NULL, { 0x82, 0x07 /* 01000001111, 1 7 8 9 10 */ }, { 0x02, 0x00 /* 01000000000, 1 */ }, { 0x00, 0x00 /* 00000000000, */ }, (const scxml_elem_data*)&scxml_elem_datas[0], SCXML_STATE_COMPOUND },
    { "s0", 0, s0_on_entry, s0_on_exit, NULL, { 0x7c, 0x00 /* 00111110000, 2 3 4 5 6 */ }, { 0x04, 0x00 /* 00100000000, 2 */ }, { 0x01, 0x00 /* 10000000000, 0 */ }, NULL, SCXML_STATE_COMPOUND },
    { NULL, 1, NULL, NULL, NULL, { 0x00, 0x00 /* 00000000000, */ }, { 0x00, 0x00 /* 00000000000, */ }, { 0x03, 0x00 /* 11000000000, 0 1 */ }, NULL, SCXML_STATE_INITIAL },
    { "sh1", 1, NULL, NULL, NULL, { 0x00, 0x00 /* 00000000000, */ }, { 0x74, 0x00 /* 00101110000, 2 4 5 6 */ }, { 0x03, 0x00 /* 11000000000, 0 1 */ }, NULL, SCXML_STATE_HISTORY_SHALLOW },
    { "s01", 1, NULL, NULL, NULL, { 0x00, 0x00 /* 00000000000, */ }, { 0x00, 0x00 /* 00000000000, */ }, { 0x03, 0x00 /* 11000000000, 0 1 */ }, NULL, SCXML_STATE_ATOMIC },
    { "s02", 1, NULL, NULL, NULL, { 0x00, 0x00 /* 00000000000, */ }, { 0x00, 0x00 /* 00000000000, */ }, { 0x03, 0x00 /* 11000000000, 0 1 */ }, NULL, SCXML_STATE_ATOMIC },
    { "s03", 1, s03_on_entry, NULL, NULL, { 0x00, 0x00 /* 00000000000, */ }, { 0x00, 0x00 /* 00000000000, */ }, { 0x03, 0x00 /* 11000000000, 0 1 */ }, NULL, SCXML_STATE_ATOMIC },
    { "s2", 0, NULL, NULL, NULL, { 0x00, 0x00 /* 00000000000, */ }, { 0x00, 0x00 /* 00000000000, */ }, { 0x01, 0x00 /* 10000000000, 0 */ }, NULL, SCXML_STATE_ATOMIC },
    { "s3", 0, NULL, NULL, NULL, { 0x00, 0x00 /* 00000000000, */ }, { 0x00, 0x00 /* 00000000000, */ }, { 0x01, 0x00 /* 10000000000, 0 */ }, NULL, SCXML_STATE_ATOMIC },
    { "pass", 0, pass_on_entry, NULL, NULL, { 0x00, 0x00 /* 00000000000, */ }, { 0x00, 0x00 /* 00000000000, */ }, { 0x01, 0x00 /* 10000000000, 0 */ }, NULL, SCXML_STATE_FINAL },
    { "fail", 0, fail_on_entry, NULL, NULL, { 0x00, 0x00 /* 00000000000, */ }, { 0x00, 0x00 /* 00000000000, */ }, { 0x01, 0x00 /* 10000000000, 0 */ }, NULL, SCXML_STATE_FINAL }
};

static scxml_transition scxml_transitions[13] = {
    { 2, { 0x08, 0x00 /* 00010000000 */ }, NULL, NULL, NULL, SCXML_TRANS_SPONTANEOUS | SCXML_TRANS_INITIAL, { 0xff, 0x1f /* 1111111111111 */ }, { 0xfe, 0x07 /* 01111111111 */ } },
    { 3, { 0x10, 0x00 /* 00001000000 */ }, NULL, NULL, sh1_transition0_on_trans, SCXML_TRANS_SPONTANEOUS | SCXML_TRANS_HISTORY, { 0xff, 0x1f /* 1111111111111 */ }, { 0xfe, 0x07 /* 01111111111 */ } },
    { 4, { 0x20, 0x00 /* 00000100000 */ }, "event1", NULL, NULL, 0, { 0xff, 0x1f /* 1111111111111 */ }, { 0x7c, 0x00 /* 00111110000 */ } },
    { 4, { 0x00, 0x04 /* 00000000001 */ }, "*", NULL, NULL, 0, { 0xff, 0x1f /* 1111111111111 */ }, { 0xfe, 0x07 /* 01111111111 */ } },
    { 5, { 0x40, 0x00 /* 00000010000 */ }, "event2", NULL, NULL, 0, { 0xff, 0x1f /* 1111111111111 */ }, { 0x7c, 0x00 /* 00111110000 */ } },
    { 5, { 0x00, 0x04 /* 00000000001 */ }, "*", NULL, NULL, 0, { 0xff, 0x1f /* 1111111111111 */ }, { 0xfe, 0x07 /* 01111111111 */ } },
    { 6, { 0x02, 0x00 /* 01000000000 */ }, "event3", "Var1==0", NULL, 0, { 0xff, 0x1f /* 1111111111111 */ }, { 0xfe, 0x07 /* 01111111111 */ } },
    { 6, { 0x80, 0x00 /* 00000001000 */ }, "event1", "Var1==1", NULL, 0, { 0xff, 0x1f /* 1111111111111 */ }, { 0xfe, 0x07 /* 01111111111 */ } },
    { 6, { 0x00, 0x04 /* 00000000001 */ }, "*", NULL, NULL, 0, { 0xff, 0x1f /* 1111111111111 */ }, { 0xfe, 0x07 /* 01111111111 */ } },
    { 7, { 0x00, 0x01 /* 00000000100 */ }, "event2", NULL, NULL, 0, { 0xff, 0x1f /* 1111111111111 */ }, { 0xfe, 0x07 /* 01111111111 */ } },
    { 7, { 0x00, 0x04 /* 00000000001 */ }, "*", NULL, NULL, 0, { 0xff, 0x1f /* 1111111111111 */ }, { 0xfe, 0x07 /* 01111111111 */ } },
    { 8, { 0x00, 0x04 /* 00000000001 */ }, "event3", NULL, NULL, 0, { 0xff, 0x1f /* 1111111111111 */ }, { 0xfe, 0x07 /* 01111111111 */ } },
    { 8, { 0x00, 0x02 /* 00000000010 */ }, "timeout", NULL, NULL, 0, { 0xff, 0x1f /* 1111111111111 */ }, { 0xfe, 0x07 /* 01111111111 */ } }
};

#ifdef SCXML_VERBOSE
static void printStateNames(const char* a) {
    const char* seperator = "";
    for (int i = 0; i < SCXML_NUMBER_STATES; i++) {
        if (IS_SET(i, a)) {
            printf("%s%s", seperator, (scxml_states[i].name != NULL ? scxml_states[i].name : "UNK"));
            seperator = ", ";
        }
    }
    printf("\n");
}

static void printBitsetIndices(const char* a, size_t length) {
    const char* seperator = "";
    for (int i = 0; i < length; i++) {
        if (IS_SET(i, a)) {
            printf("%s%d", seperator, i);
            seperator = ", ";
        }
    }
    printf("\n");
}
#endif

static void bit_or(char* dest, const char* mask, size_t i) {
    do {
        dest[i - 1] |= mask[i - 1];
    } while(--i);
}

static void bit_copy(char* dest, const char* source, size_t i) {
    do {
        dest[i - 1] = source[i - 1];
    } while(--i);
}

static int bit_has_and(const char* a, const char* b, size_t i) {
    do {
        if (a[i - 1] & b[i - 1])
            return true;
    } while(--i);
    return false;
}

static void bit_and_not(char* dest, const char* mask, size_t i) {
    do {
        dest[i - 1] &= ~mask[i - 1];
    } while(--i);
}

static void bit_and(char* dest, const char* mask, size_t i) {
    do {
        dest[i - 1] &= mask[i - 1];
    } while(--i);
}

static int bit_any_set(const char* a, size_t i) {
    do {
        if (a[i - 1] > 0)
            return true;
    } while(--i);
    return false;
}

int scxml_step(scxml_ctx* ctx) {

#ifdef SCXML_VERBOSE
    printf("Config: ");
    printStateNames(ctx->config);
#endif

MACRO_STEP:
    ctx->flags &= ~SCXML_CTX_TRANSITION_FOUND;

    if (ctx->flags & SCXML_CTX_TOP_LEVEL_FINAL) 
        return SCXML_ERR_DONE; 

    int err = SCXML_ERR_OK;
    char conflicts[2] = {0, 0};
    char target_set[2] = {0, 0};
    char exit_set[2] = {0, 0};
    char trans_set[2] = {0, 0};
    char entry_set[2] = {0, 0};

    if unlikely(ctx->flags == SCXML_CTX_PRISTINE) {
        global_script(ctx, &scxml_states[0], NULL);
        bit_or(target_set, scxml_states[0].completion, 2);
        ctx->flags |= SCXML_CTX_SPONTANEOUS | SCXML_CTX_INITIALIZED;
        goto ESTABLISH_ENTRY_SET;
    }

    if (ctx->flags & SCXML_CTX_SPONTANEOUS) {
        ctx->event = NULL;
        goto SELECT_TRANSITIONS;
    }
    if ((ctx->event = ctx->dequeue_internal(ctx)) != NULL) {
        goto SELECT_TRANSITIONS;
    }
    if ((ctx->event = ctx->dequeue_external(ctx)) != NULL) {
        goto SELECT_TRANSITIONS;
    }

SELECT_TRANSITIONS:
    for (int i = 0; i < SCXML_NUMBER_TRANSITIONS; i++) {
        // never select history or initial transitions automatically
        if unlikely(scxml_transitions[i].type & (SCXML_TRANS_HISTORY | SCXML_TRANS_INITIAL))
            continue;

        // is the transition active?
        if (IS_SET(scxml_transitions[i].source, ctx->config)) {
            // is it non-conflicting?
            if (!IS_SET(i, conflicts)) {
                // is it enabled?
                if (ctx->is_enabled(ctx, &scxml_transitions[i], ctx->event) > 0) {
                    // remember that we found a transition
                    ctx->flags |= SCXML_CTX_TRANSITION_FOUND;

                    // transitions that are pre-empted
                    bit_or(conflicts, scxml_transitions[i].conflicts, 2);

                    // states that are directly targeted (resolve as entry-set later)
                    bit_or(target_set, scxml_transitions[i].target, 2);

                    // states that will be left
                    bit_or(exit_set, scxml_transitions[i].exit_set, 2);

                    SET_BIT(i, trans_set);
                }
            }
        }
    }
    bit_and(exit_set, ctx->config, 2);

    if (ctx->flags & SCXML_CTX_TRANSITION_FOUND) {
        ctx->flags |= SCXML_CTX_SPONTANEOUS;
    } else {
        ctx->flags &= ~SCXML_CTX_SPONTANEOUS;
    }

#ifdef SCXML_VERBOSE
    printf("Targets: ");
    printStateNames(target_set);
#endif

#ifdef SCXML_VERBOSE
    printf("Exiting: ");
    printStateNames(exit_set);
#endif

#ifdef SCXML_VERBOSE
    printf("History: ");
    printStateNames(ctx->history);
#endif

    
    // REMEMBER_HISTORY:
    for (int i = 0; i < SCXML_NUMBER_STATES; i++) {
        if unlikely(scxml_states[i].type == SCXML_STATE_HISTORY_SHALLOW || scxml_states[i].type == SCXML_STATE_HISTORY_DEEP) {
            // a history state whose parent is about to be exited
            if unlikely(IS_SET(scxml_states[i].parent, exit_set)) {
                char history[2] = {0, 0};
                bit_copy(history, scxml_states[i].completion, 2);
                
                // set those states who were enabled
                bit_and(history, ctx->config, 2);
                
                // clear current history with completion mask - TODO: errornously clears nested history
                bit_and_not(ctx->history, scxml_states[i].completion, 2);
                
                // set history
                bit_or(ctx->history, history, 2);
            }
        }
    }
#ifdef SCXML_VERBOSE
    printf("Transitions: ");
    printBitsetIndices(trans_set, sizeof(char) * 8 * 2);
#endif

ESTABLISH_ENTRY_SET:
    // calculate new entry set
    bit_copy(entry_set, target_set, 2);

    // iterate for ancestors
    for (int i = 0; i < SCXML_NUMBER_STATES; i++) {
        if (IS_SET(i, entry_set)) {
            bit_or(entry_set, scxml_states[i].ancestors, 2);
        }
    }

    // iterate for descendants
    for (int i = 0; i < SCXML_NUMBER_STATES; i++) {
        if (IS_SET(i, entry_set)) {
            switch (scxml_states[i].type) {
                case SCXML_STATE_PARALLEL: {
                    bit_or(entry_set, scxml_states[i].completion, 2);
                    break;
                }
                case SCXML_STATE_HISTORY_SHALLOW:
                case SCXML_STATE_HISTORY_DEEP: {
                    char history_targets[2] = {0, 0};
                    if (!bit_has_and(scxml_states[i].completion, ctx->history, 2) &&
                        !IS_SET(scxml_states[i].parent, ctx->config)) {
                        // nothing set for history, look for a default transition or enter parents completion
                        for (int j = 0; j < SCXML_NUMBER_TRANSITIONS; j++) {
                            if unlikely(scxml_transitions[j].source == i) {
                                bit_or(entry_set, scxml_transitions[j].target, 2);
                                SET_BIT(j, trans_set);
                                break;
                            }
                        }
                        // TODO: enter parents default completion here
                    } else {
                        bit_copy(history_targets, scxml_states[i].completion, 2);
                        bit_and(history_targets, ctx->history, 2);
                        bit_or(entry_set, history_targets, 2);
                    }
                    break;
                }
                case SCXML_STATE_INITIAL: {
                    for (int j = 0; j < SCXML_NUMBER_TRANSITIONS; j++) {
                        if (scxml_transitions[j].source == i) {
                            SET_BIT(j, trans_set);
                            CLEARBIT(i, entry_set);
                            bit_or(entry_set, scxml_transitions[j].target, 2);
                            // one target may have been above, reestablish completion
                            // goto ADD_DESCENDANTS; // initial will have to be first!
                        }
                    }
                    break;
                }
                case SCXML_STATE_COMPOUND: { // we need to check whether one child is already in entry_set
                    if (!bit_has_and(entry_set, scxml_states[i].children, 2) &&
                        (!bit_has_and(ctx->config, scxml_states[i].children, 2) ||
                        bit_has_and(exit_set, scxml_states[i].children, 2)))
                    {
                        bit_or(entry_set, scxml_states[i].completion, 2);
                    }
                    break;
                }
            }
        }
    }

// EXIT_STATES:
    for (int i = SCXML_NUMBER_STATES - 1; i >= 0; i--) {
        if (IS_SET(i, exit_set) && IS_SET(i, ctx->config)) {
            // call all on exit handlers
            if (scxml_states[i].on_exit != NULL) {
                if unlikely((err = scxml_states[i].on_exit(ctx, &scxml_states[i], ctx->event)) != SCXML_ERR_OK)
                    return err;
            }
            CLEARBIT(i, ctx->config);
        }
    }

// TAKE_TRANSITIONS:
    for (int i = 0; i < SCXML_NUMBER_TRANSITIONS; i++) {
        if (IS_SET(i, trans_set) && (scxml_transitions[i].type & SCXML_TRANS_HISTORY) == 0) {
            // call executable content in transition
            if (scxml_transitions[i].on_transition != NULL) {
                if unlikely((err = scxml_transitions[i].on_transition(ctx,
                                                             &scxml_states[scxml_transitions[i].source],
                                                             ctx->event)) != SCXML_ERR_OK)
                    return err;
            }
        }
    }

#ifdef SCXML_VERBOSE
    printf("Entering: ");
    printStateNames(entry_set);
#endif

// ENTER_STATES:
    for (int i = 0; i < SCXML_NUMBER_STATES; i++) {
        if (IS_SET(i, entry_set) && !IS_SET(i, ctx->config)) {
            // these are no proper states
            if unlikely(scxml_states[i].type == SCXML_STATE_HISTORY_DEEP ||
                        scxml_states[i].type == SCXML_STATE_HISTORY_SHALLOW ||
                        scxml_states[i].type == SCXML_STATE_INITIAL)
                continue;

            SET_BIT(i, ctx->config);

            // initialize data
            if (!IS_SET(i, ctx->initialized_data)) {
                if unlikely(scxml_states[i].data != NULL && ctx->exec_content_init != NULL) {
                    ctx->exec_content_init(ctx, scxml_states[i].data);
                }
                SET_BIT(i, ctx->initialized_data);
            }

            if (scxml_states[i].on_entry != NULL) {
                if unlikely((err = scxml_states[i].on_entry(ctx, &scxml_states[i], ctx->event)) != SCXML_ERR_OK)
                    return err;
            }

            // take history transitions
            for (int j = 0; j < SCXML_NUMBER_TRANSITIONS; j++) {
                if unlikely(IS_SET(j, trans_set) &&
                            (scxml_transitions[j].type & SCXML_TRANS_HISTORY) &&
                            scxml_states[scxml_transitions[j].source].parent == i) {
                    // call executable content in transition
                    if (scxml_transitions[j].on_transition != NULL) {
                        if unlikely((err = scxml_transitions[j].on_transition(ctx,
                                                                              &scxml_states[i],
                                                                              ctx->event)) != SCXML_ERR_OK)
                            return err;
                    }
                }
            }

            // handle final states
            if unlikely(scxml_states[i].type == SCXML_STATE_FINAL) {
                if unlikely(scxml_states[i].ancestors[0] == 0x01) {
                    ctx->flags |= SCXML_CTX_TOP_LEVEL_FINAL;
                } else {
                    // raise done event
                    scxml_elem_donedata* donedata = &scxml_elem_donedatas[0];
                    while(ELEM_DONEDATA_IS_SET(donedata)) {
                        if unlikely(donedata->source == i)
                            break;
                        donedata++;
                    }
                    ctx->raise_done_event(ctx, &scxml_states[scxml_states[i].parent], (ELEM_DONEDATA_IS_SET(donedata) ? donedata : NULL));
                }

                /**
                 * are we the last final state to leave a parallel state?:
                 * 1. Gather all parallel states in our ancestor chain
                 * 2. Find all states for which these parallels are ancestors
                 * 3. Iterate all active final states and remove their ancestors
                 * 4. If a state remains, not all children of a parallel are final
                 */
                for (int j = 0; j < SCXML_NUMBER_STATES; j++) {
                    if unlikely(scxml_states[j].type == SCXML_STATE_PARALLEL) {
                        char parallel_children[2] = {0, 0};
                        size_t parallel = j;
                        for (int k = 0; k < SCXML_NUMBER_STATES; k++) {
                            if unlikely(IS_SET(parallel, scxml_states[k].ancestors) && IS_SET(k, ctx->config)) {
                                if (scxml_states[k].type == SCXML_STATE_FINAL) {
                                    bit_and_not(parallel_children, scxml_states[k].ancestors, 2);
                                } else {
                                    SET_BIT(k, parallel_children);
                                }
                            }
                        }
                        if unlikely(!bit_any_set(parallel_children, 2)) {
                            ctx->raise_done_event(ctx, &scxml_states[parallel], NULL);
                        }
                    }
                }

            }

        }
    }

    return SCXML_ERR_OK;
}

