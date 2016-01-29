#include <stdint.h> // explicit types
#include <stddef.h> // NULL

#define BIT_HAS(idx, bitset)   ((bitset[idx >> 3] &  (1 << (idx & 7))) != 0)
#define BIT_SET_AT(idx, bitset)  bitset[idx >> 3] |= (1 << (idx & 7));
#define BIT_CLEAR(idx, bitset)   bitset[idx >> 3] &= (1 << (idx & 7)) ^ 0xFF;

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
#define SCXML_NUMBER_STATES 9
#define SCXML_NUMBER_TRANSITIONS 6

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
#define SCXML_STATE_HAS_HISTORY      0x80 // highest bit
#define SCXML_STATE_MASK(t)          (t & 0x7F) // mask highest bit

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

typedef void* (*dequeue_internal_t)(const scxml_ctx* ctx);
typedef void* (*dequeue_external_t)(const scxml_ctx* ctx);
typedef int (*is_enabled_t)(const scxml_ctx* ctx, const scxml_transition* transition, const void* event);
typedef int (*is_true_t)(const scxml_ctx* ctx, const char* expr);
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
    const uint8_t parent; // parent
    const exec_content_t on_entry; // on entry handlers
    const exec_content_t on_exit; // on exit handlers
    const invoke_t invoke; // invocations
    const char children[2]; // all children
    const char completion[2]; // default completion
    const char ancestors[2]; // all ancestors
    const scxml_elem_data* data;
    const uint8_t type; // atomic, parallel, compound, final, history
};

struct scxml_transition {
    const uint8_t source;
    const char target[2];
    const char* event;
    const char* condition;
    const exec_content_t on_transition;
    const uint8_t type;
    const char conflicts[1];
    const char exit_set[2];
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
    const uint8_t source;
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
    const uint8_t autoforward;
    const scxml_elem_param* params;
    const exec_content_finalize_t* finalize;
    const char* content;
    const char* contentexpr;
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
};

struct scxml_ctx {
    uint8_t flags;

    char config[2];
    char history[2];
    char pending_invokes[2];
    char initialized_data[2];

    void* user_data;
    void* event;

    dequeue_internal_t dequeue_internal;
    dequeue_external_t dequeue_external;
    is_enabled_t is_enabled;
    is_true_t is_true;
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

static const scxml_elem_data scxml_elem_datas[2] = {
    /* id, src, expr, content */
    { "Var1", NULL, "0", NULL },
    { NULL, NULL, NULL, NULL }
};

static const scxml_elem_param scxml_elem_params[2] = {
    /* name, expr, location */
    { "Var1", "1", NULL },
    { NULL, NULL, NULL }
};

static const scxml_elem_donedata scxml_elem_donedatas[3] = {
    /* source, content, contentexpr, params */
    { 3, NULL, NULL, &scxml_elem_params[0] },
    { 6, "foo", NULL, NULL },
    { 0, NULL, NULL, NULL }
};

static int global_script(const scxml_ctx* ctx, const scxml_state* state, const void* event) {
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

static const scxml_state scxml_states[9] = {
    {   /* state number 0 */
        /* name       */ NULL,
        /* parent     */ 0,
        /* onentry    */ NULL,
        /* onexit     */ NULL,
        /* invoke     */ NULL,
        /* children   */ { 0x92, 0x01 /* 010010011, 1 4 7 8 */ },
        /* completion */ { 0x02, 0x00 /* 010000000, 1 */ }, 	
        /* ancestors  */ { 0x00, 0x00 /* 000000000, */ },
        /* data       */ &scxml_elem_datas[0],
        /* type       */ SCXML_STATE_COMPOUND,
    },
    {   /* state number 1 */
        /* name       */ "s0",
        /* parent     */ 0,
        /* onentry    */ NULL,
        /* onexit     */ NULL,
        /* invoke     */ NULL,
        /* children   */ { 0x0c, 0x00 /* 001100000, 2 3 */ },
        /* completion */ { 0x04, 0x00 /* 001000000, 2 */ }, 	
        /* ancestors  */ { 0x01, 0x00 /* 100000000, 0 */ },
        /* data       */ NULL,
        /* type       */ SCXML_STATE_COMPOUND,
    },
    {   /* state number 2 */
        /* name       */ "s01",
        /* parent     */ 1,
        /* onentry    */ NULL,
        /* onexit     */ NULL,
        /* invoke     */ NULL,
        /* children   */ { 0x00, 0x00 /* 000000000, */ },
        /* completion */ { 0x00, 0x00 /* 000000000, */ }, 	
        /* ancestors  */ { 0x03, 0x00 /* 110000000, 0 1 */ },
        /* data       */ NULL,
        /* type       */ SCXML_STATE_ATOMIC,
    },
    {   /* state number 3 */
        /* name       */ "s02",
        /* parent     */ 1,
        /* onentry    */ NULL,
        /* onexit     */ NULL,
        /* invoke     */ NULL,
        /* children   */ { 0x00, 0x00 /* 000000000, */ },
        /* completion */ { 0x00, 0x00 /* 000000000, */ }, 	
        /* ancestors  */ { 0x03, 0x00 /* 110000000, 0 1 */ },
        /* data       */ NULL,
        /* type       */ SCXML_STATE_FINAL,
    },
    {   /* state number 4 */
        /* name       */ "s1",
        /* parent     */ 0,
        /* onentry    */ NULL,
        /* onexit     */ NULL,
        /* invoke     */ NULL,
        /* children   */ { 0x60, 0x00 /* 000001100, 5 6 */ },
        /* completion */ { 0x20, 0x00 /* 000001000, 5 */ }, 	
        /* ancestors  */ { 0x01, 0x00 /* 100000000, 0 */ },
        /* data       */ NULL,
        /* type       */ SCXML_STATE_COMPOUND,
    },
    {   /* state number 5 */
        /* name       */ "s11",
        /* parent     */ 4,
        /* onentry    */ NULL,
        /* onexit     */ NULL,
        /* invoke     */ NULL,
        /* children   */ { 0x00, 0x00 /* 000000000, */ },
        /* completion */ { 0x00, 0x00 /* 000000000, */ }, 	
        /* ancestors  */ { 0x11, 0x00 /* 100010000, 0 4 */ },
        /* data       */ NULL,
        /* type       */ SCXML_STATE_ATOMIC,
    },
    {   /* state number 6 */
        /* name       */ "s12",
        /* parent     */ 4,
        /* onentry    */ NULL,
        /* onexit     */ NULL,
        /* invoke     */ NULL,
        /* children   */ { 0x00, 0x00 /* 000000000, */ },
        /* completion */ { 0x00, 0x00 /* 000000000, */ }, 	
        /* ancestors  */ { 0x11, 0x00 /* 100010000, 0 4 */ },
        /* data       */ NULL,
        /* type       */ SCXML_STATE_FINAL,
    },
    {   /* state number 7 */
        /* name       */ "pass",
        /* parent     */ 0,
        /* onentry    */ pass_on_entry,
        /* onexit     */ NULL,
        /* invoke     */ NULL,
        /* children   */ { 0x00, 0x00 /* 000000000, */ },
        /* completion */ { 0x00, 0x00 /* 000000000, */ }, 	
        /* ancestors  */ { 0x01, 0x00 /* 100000000, 0 */ },
        /* data       */ NULL,
        /* type       */ SCXML_STATE_FINAL,
    },
    {   /* state number 8 */
        /* name       */ "fail",
        /* parent     */ 0,
        /* onentry    */ fail_on_entry,
        /* onexit     */ NULL,
        /* invoke     */ NULL,
        /* children   */ { 0x00, 0x00 /* 000000000, */ },
        /* completion */ { 0x00, 0x00 /* 000000000, */ }, 	
        /* ancestors  */ { 0x01, 0x00 /* 100000000, 0 */ },
        /* data       */ NULL,
        /* type       */ SCXML_STATE_FINAL,
    }
};

static const scxml_transition scxml_transitions[6] = {
    {   /* transition number 0 with priority 0
           target: s02
         */
        /* source     */ 2,
        /* target     */ { 0x08, 0x00 /* 000100000, 3 */ },
        /* event      */ NULL,
        /* condition  */ NULL,
        /* ontrans    */ NULL,
        /* type       */ SCXML_TRANS_SPONTANEOUS,
        /* conflicts  */ { 0x37 /* 111011, 0 1 2 4 5 */ }, 
        /* exit set   */ { 0x0c, 0x00 /* 001100000, 2 3 */ }
    },
    {   /* transition number 1 with priority 1
           target: s1
         */
        /* source     */ 1,
        /* target     */ { 0x10, 0x00 /* 000010000, 4 */ },
        /* event      */ "done.state.s0",
        /* condition  */ "_event.data['Var1']==1",
        /* ontrans    */ NULL,
        /* type       */ 0,
        /* conflicts  */ { 0x3f /* 111111, 0 1 2 3 4 5 */ }, 
        /* exit set   */ { 0xfe, 0x01 /* 011111111, 1 2 3 4 5 6 7 8 */ }
    },
    {   /* transition number 2 with priority 2
           target: fail
         */
        /* source     */ 1,
        /* target     */ { 0x00, 0x01 /* 000000001, 8 */ },
        /* event      */ "done.state.s0",
        /* condition  */ NULL,
        /* ontrans    */ NULL,
        /* type       */ 0,
        /* conflicts  */ { 0x3f /* 111111, 0 1 2 3 4 5 */ }, 
        /* exit set   */ { 0xfe, 0x01 /* 011111111, 1 2 3 4 5 6 7 8 */ }
    },
    {   /* transition number 3 with priority 3
           target: s12
         */
        /* source     */ 5,
        /* target     */ { 0x40, 0x00 /* 000000100, 6 */ },
        /* event      */ NULL,
        /* condition  */ NULL,
        /* ontrans    */ NULL,
        /* type       */ SCXML_TRANS_SPONTANEOUS,
        /* conflicts  */ { 0x3e /* 011111, 1 2 3 4 5 */ }, 
        /* exit set   */ { 0x60, 0x00 /* 000001100, 5 6 */ }
    },
    {   /* transition number 4 with priority 4
           target: pass
         */
        /* source     */ 4,
        /* target     */ { 0x80, 0x00 /* 000000010, 7 */ },
        /* event      */ "done.state.s1",
        /* condition  */ "_event.data == 'foo'",
        /* ontrans    */ NULL,
        /* type       */ 0,
        /* conflicts  */ { 0x3f /* 111111, 0 1 2 3 4 5 */ }, 
        /* exit set   */ { 0xfe, 0x01 /* 011111111, 1 2 3 4 5 6 7 8 */ }
    },
    {   /* transition number 5 with priority 5
           target: fail
         */
        /* source     */ 4,
        /* target     */ { 0x00, 0x01 /* 000000001, 8 */ },
        /* event      */ "done.state.s1",
        /* condition  */ NULL,
        /* ontrans    */ NULL,
        /* type       */ 0,
        /* conflicts  */ { 0x3f /* 111111, 0 1 2 3 4 5 */ }, 
        /* exit set   */ { 0xfe, 0x01 /* 011111111, 1 2 3 4 5 6 7 8 */ }
    }
};

#ifdef SCXML_VERBOSE
static void printStateNames(const char* a) {
    size_t i;
    const char* seperator = "";
    for (i = 0; i < SCXML_NUMBER_STATES; i++) {
        if (BIT_HAS(i, a)) {
            printf("%s%s", seperator, (scxml_states[i].name != NULL ? scxml_states[i].name : "UNK"));
            seperator = ", ";
        }
    }
    printf("\n");
}

static void printBitsetIndices(const char* a, size_t length) {
    size_t i;
    const char* seperator = "";
    for (i = 0; i < length; i++) {
        if (BIT_HAS(i, a)) {
            printf("%s%lu", seperator, i);
            seperator = ", ";
        }
    }
    printf("\n");
}
#endif

static int bit_has_and(const char* a, const char* b, size_t i) {
    do {
        if (a[i - 1] & b[i - 1])
            return 1;
    } while(--i);
    return 0;
}

static int bit_has_any(const char* a, size_t i) {
    do {
        if (a[i - 1] > 0)
            return 1;
    } while(--i);
    return 0;
}

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

int scxml_step(scxml_ctx* ctx) {

#ifdef SCXML_VERBOSE
    printf("Config: ");
    printStateNames(ctx->config);
#endif

// MACRO_STEP:

    if (ctx->flags & SCXML_CTX_TOP_LEVEL_FINAL) 
        return SCXML_ERR_DONE; 

    size_t i, j, k;
    int err = SCXML_ERR_OK;
    char conflicts[1] = {0};
    char target_set[2] = {0, 0};
    char exit_set[2] = {0, 0};
    char trans_set[1] = {0};
    char entry_set[2] = {0, 0};
    char tmp_states[2] = {0, 0};

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
    for (i = 0; i < SCXML_NUMBER_TRANSITIONS; i++) {
        // never select history or initial transitions automatically
        if unlikely(scxml_transitions[i].type & (SCXML_TRANS_HISTORY | SCXML_TRANS_INITIAL))
            continue;

        // is the transition active?
        if (BIT_HAS(scxml_transitions[i].source, ctx->config)) {
            // is it non-conflicting?
            if (!BIT_HAS(i, conflicts)) {
                // is it enabled?
                if (ctx->is_enabled(ctx, &scxml_transitions[i], ctx->event) > 0) {
                    // remember that we found a transition
                    ctx->flags |= SCXML_CTX_TRANSITION_FOUND;

                    // transitions that are pre-empted
                    bit_or(conflicts, scxml_transitions[i].conflicts, 1);

                    // states that are directly targeted (resolve as entry-set later)
                    bit_or(target_set, scxml_transitions[i].target, 2);

                    // states that will be left
                    bit_or(exit_set, scxml_transitions[i].exit_set, 2);

                    BIT_SET_AT(i, trans_set);
                }
            }
        }
    }
    bit_and(exit_set, ctx->config, 2);

    if (ctx->flags & SCXML_CTX_TRANSITION_FOUND) {
        ctx->flags |= SCXML_CTX_SPONTANEOUS;
        ctx->flags &= ~SCXML_CTX_TRANSITION_FOUND;
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
    for (i = 0; i < SCXML_NUMBER_STATES; i++) {
        if unlikely(SCXML_STATE_MASK(scxml_states[i].type) == SCXML_STATE_HISTORY_SHALLOW ||
                    SCXML_STATE_MASK(scxml_states[i].type) == SCXML_STATE_HISTORY_DEEP) {
            // a history state whose parent is about to be exited
            if unlikely(BIT_HAS(scxml_states[i].parent, exit_set)) {
                bit_copy(tmp_states, scxml_states[i].completion, 2);

                // set those states who were enabled
                bit_and(tmp_states, ctx->config, 2);

                // clear current history with completion mask
                bit_and_not(ctx->history, scxml_states[i].completion, 2);

                // set history
                bit_or(ctx->history, tmp_states, 2);
            }
        }
    }

ESTABLISH_ENTRY_SET:
    // calculate new entry set
    bit_copy(entry_set, target_set, 2);

    // iterate for ancestors
    for (i = 0; i < SCXML_NUMBER_STATES; i++) {
        if (BIT_HAS(i, entry_set)) {
            bit_or(entry_set, scxml_states[i].ancestors, 2);
        }
    }

    // iterate for descendants
    for (i = 0; i < SCXML_NUMBER_STATES; i++) {
        if (BIT_HAS(i, entry_set)) {
            switch (SCXML_STATE_MASK(scxml_states[i].type)) {
                case SCXML_STATE_PARALLEL: {
                    bit_or(entry_set, scxml_states[i].completion, 2);
                    break;
                }
                case SCXML_STATE_HISTORY_SHALLOW:
                case SCXML_STATE_HISTORY_DEEP: {
                    if (!bit_has_and(scxml_states[i].completion, ctx->history, 2) &&
                        !BIT_HAS(scxml_states[i].parent, ctx->config)) {
                        // nothing set for history, look for a default transition
                        for (j = 0; j < SCXML_NUMBER_TRANSITIONS; j++) {
                            if unlikely(scxml_transitions[j].source == i) {
                                bit_or(entry_set, scxml_transitions[j].target, 2);
                                if(SCXML_STATE_MASK(scxml_states[i].type) == SCXML_STATE_HISTORY_DEEP &&
                                   !bit_has_and(scxml_transitions[j].target, scxml_states[i].children, 2)) {
                                    for (k = i + 1; k < SCXML_NUMBER_STATES; k++) {
                                        if (BIT_HAS(k, scxml_transitions[j].target)) {
                                            bit_or(entry_set, scxml_states[k].ancestors, 2);
                                            break;
                                        }
                                    }
                                }
                                BIT_SET_AT(j, trans_set);
                                break;
                            }
                            // Note: SCXML mandates every history to have a transition!
                        }
                    } else {
                        bit_copy(tmp_states, scxml_states[i].completion, 2);
                        bit_and(tmp_states, ctx->history, 2);
                        bit_or(entry_set, tmp_states, 2);
                        if (scxml_states[i].type == (SCXML_STATE_HAS_HISTORY | SCXML_STATE_HISTORY_DEEP)) {
                            // a deep history state with nested histories -> more completion
                            for (j = i + 1; j < SCXML_NUMBER_STATES; j++) {
                                if (BIT_HAS(j, scxml_states[i].completion) &&
                                    BIT_HAS(j, entry_set) &&
                                    (scxml_states[j].type & SCXML_STATE_HAS_HISTORY)) {
                                    for (k = j + 1; k < SCXML_NUMBER_STATES; k++) {
                                        // add nested history to entry_set
                                        if ((SCXML_STATE_MASK(scxml_states[k].type) == SCXML_STATE_HISTORY_DEEP ||
                                             SCXML_STATE_MASK(scxml_states[k].type) == SCXML_STATE_HISTORY_SHALLOW) &&
                                            BIT_HAS(k, scxml_states[j].children)) {
                                            // a nested history state
                                            BIT_SET_AT(k, entry_set);
                                        }
                                    }
                                }
                            }
                        }
                    }
                    break;
                }
                case SCXML_STATE_INITIAL: {
                    for (j = 0; j < SCXML_NUMBER_TRANSITIONS; j++) {
                        if (scxml_transitions[j].source == i) {
                            BIT_SET_AT(j, trans_set);
                            BIT_CLEAR(i, entry_set);
                            bit_or(entry_set, scxml_transitions[j].target, 2);
                            for (k = i + 1; k < SCXML_NUMBER_STATES; k++) {
                                if (BIT_HAS(k, scxml_transitions[j].target)) {
                                    bit_or(entry_set, scxml_states[k].ancestors, 2);
                                }
                            }
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
                        if (!bit_has_and(scxml_states[i].completion, scxml_states[i].children, 2)) {
                            // deep completion
                            for (j = i + 1; j < SCXML_NUMBER_STATES; j++) {
                                if (BIT_HAS(j, scxml_states[i].completion)) {
                                    bit_or(entry_set, scxml_states[j].ancestors, 2);
                                    break; // completion of compound is single state
                                }
                            }
                        }
                    }
                    break;
                }
            }
        }
    }

#ifdef SCXML_VERBOSE
    printf("Transitions: ");
    printBitsetIndices(trans_set, sizeof(char) * 8 * 1);
#endif

// EXIT_STATES:
    i = SCXML_NUMBER_STATES;
    while(i-- > 0) {
        if (BIT_HAS(i, exit_set) && BIT_HAS(i, ctx->config)) {
            // call all on exit handlers
            if (scxml_states[i].on_exit != NULL) {
                if unlikely((err = scxml_states[i].on_exit(ctx, &scxml_states[i], ctx->event)) != SCXML_ERR_OK)
                    return err;
            }
            BIT_CLEAR(i, ctx->config);
        }
    }

// TAKE_TRANSITIONS:
    for (i = 0; i < SCXML_NUMBER_TRANSITIONS; i++) {
        if (BIT_HAS(i, trans_set) && (scxml_transitions[i].type & (SCXML_TRANS_HISTORY | SCXML_TRANS_INITIAL)) == 0) {
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
    for (i = 0; i < SCXML_NUMBER_STATES; i++) {
        if (BIT_HAS(i, entry_set) && !BIT_HAS(i, ctx->config)) {
            // these are no proper states
            if unlikely(SCXML_STATE_MASK(scxml_states[i].type) == SCXML_STATE_HISTORY_DEEP ||
                        SCXML_STATE_MASK(scxml_states[i].type) == SCXML_STATE_HISTORY_SHALLOW ||
                        SCXML_STATE_MASK(scxml_states[i].type) == SCXML_STATE_INITIAL)
                continue;

            BIT_SET_AT(i, ctx->config);

            // initialize data
            if (!BIT_HAS(i, ctx->initialized_data)) {
                if unlikely(scxml_states[i].data != NULL && ctx->exec_content_init != NULL) {
                    ctx->exec_content_init(ctx, scxml_states[i].data);
                }
                BIT_SET_AT(i, ctx->initialized_data);
            }

            if (scxml_states[i].on_entry != NULL) {
                if unlikely((err = scxml_states[i].on_entry(ctx, &scxml_states[i], ctx->event)) != SCXML_ERR_OK)
                    return err;
            }

            // take history and initial transitions
            for (j = 0; j < SCXML_NUMBER_TRANSITIONS; j++) {
                if unlikely(BIT_HAS(j, trans_set) &&
                            (scxml_transitions[j].type & (SCXML_TRANS_HISTORY | SCXML_TRANS_INITIAL)) &&
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
            if unlikely(SCXML_STATE_MASK(scxml_states[i].type) == SCXML_STATE_FINAL) {
                if unlikely(scxml_states[i].ancestors[0] == 0x01) {
                    ctx->flags |= SCXML_CTX_TOP_LEVEL_FINAL;
                } else {
                    // raise done event
                    const scxml_elem_donedata* donedata = &scxml_elem_donedatas[0];
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
                for (j = 0; j < SCXML_NUMBER_STATES; j++) {
                    if unlikely(SCXML_STATE_MASK(scxml_states[j].type) == SCXML_STATE_PARALLEL &&
                                BIT_HAS(j, scxml_states[i].ancestors)) {
                        bit_and_not(tmp_states, tmp_states, 2);
                        for (k = 0; k < SCXML_NUMBER_STATES; k++) {
                            if unlikely(BIT_HAS(j, scxml_states[k].ancestors) && BIT_HAS(k, ctx->config)) {
                                if (SCXML_STATE_MASK(scxml_states[k].type) == SCXML_STATE_FINAL) {
                                    bit_and_not(tmp_states, scxml_states[k].ancestors, 2);
                                } else {
                                    BIT_SET_AT(k, tmp_states);
                                }
                            }
                        }
                        if unlikely(!bit_has_any(tmp_states, 2)) {
                            ctx->raise_done_event(ctx, &scxml_states[j], NULL);
                        }
                    }
                }

            }

        }
    }

    return SCXML_ERR_OK;
}

