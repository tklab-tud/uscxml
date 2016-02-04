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

#ifndef SCXML_NR_STATES_TYPE 
#  define SCXML_NR_STATES_TYPE uint8_t
#endif 

#ifndef SCXML_NR_TRANS_TYPE 
#  define SCXML_NR_TRANS_TYPE uint8_t
#endif 

#ifndef SCXML_MAX_NR_STATES_BYTES 
#  define SCXML_MAX_NR_STATES_BYTES 1
#endif 

#ifndef SCXML_MAX_NR_TRANS_BYTES 
#  define SCXML_MAX_NR_TRANS_BYTES 1
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

#define SCXML_NUMBER_STATES (ctx->machine->nr_states)
#define SCXML_NUMBER_TRANS (ctx->machine->nr_transitions)

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
#define SCXML_MACHINE_IS_SET(machine) (machine->nr_states > 0)


typedef struct scxml_machine scxml_machine;
typedef struct scxml_transition scxml_transition;
typedef struct scxml_state scxml_state;
typedef struct scxml_ctx scxml_ctx;
typedef struct scxml_elem_invoke scxml_elem_invoke;

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
typedef int (*invoke_t)(const scxml_ctx* ctx, const scxml_state* s, const scxml_elem_invoke* invocation, uint8_t uninvoke);

typedef int (*exec_content_log_t)(const scxml_ctx* ctx, const char* label, const char* expr);
typedef int (*exec_content_raise_t)(const scxml_ctx* ctx, const char* event);
typedef int (*exec_content_send_t)(const scxml_ctx* ctx, const scxml_elem_send* send);
typedef int (*exec_content_foreach_init_t)(const scxml_ctx* ctx, const scxml_elem_foreach* foreach);
typedef int (*exec_content_foreach_next_t)(const scxml_ctx* ctx, const scxml_elem_foreach* foreach);
typedef int (*exec_content_foreach_done_t)(const scxml_ctx* ctx, const scxml_elem_foreach* foreach);
typedef int (*exec_content_assign_t)(const scxml_ctx* ctx, const char* location, const char* expr);
typedef int (*exec_content_init_t)(const scxml_ctx* ctx, const scxml_elem_data* data);
typedef int (*exec_content_cancel_t)(const scxml_ctx* ctx, const char* sendid, const char* sendidexpr);
typedef int (*exec_content_finalize_t)(const scxml_ctx* ctx, const scxml_elem_invoke* invoker, const void* event);
typedef int (*exec_content_script_t)(const scxml_ctx* ctx, const char* src, const char* content);

struct scxml_machine {
    uint8_t                    flags;
    SCXML_NR_STATES_TYPE       nr_states;
    SCXML_NR_TRANS_TYPE        nr_transitions;
    const char*                name;
    const char*                datamodel;
    const char*                uuid;
    const scxml_state*         states;
    const scxml_transition*    transitions;
    const scxml_machine*       parent;
    const scxml_elem_donedata* donedata;
    const exec_content_t       script;
};

// forward declare machines to allow references
extern const scxml_machine scxml_machines[3];

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
    const char children[SCXML_MAX_NR_STATES_BYTES]; // all children
    const char completion[SCXML_MAX_NR_STATES_BYTES]; // default completion
    const char ancestors[SCXML_MAX_NR_STATES_BYTES]; // all ancestors
    const scxml_elem_data* data;
    const uint8_t type; // atomic, parallel, compound, final, history
};

struct scxml_transition {
    const uint8_t source;
    const char target[SCXML_MAX_NR_STATES_BYTES];
    const char* event;
    const char* condition;
    const exec_content_t on_transition;
    const uint8_t type;
    const char conflicts[SCXML_MAX_NR_TRANS_BYTES];
    const char exit_set[SCXML_MAX_NR_STATES_BYTES];
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
    const scxml_machine* machine;
    const char* type;
    const char* typeexpr;
    const char* src;
    const char* srcexpr;
    const char* id;
    const char* idlocation;
    const char* namelist;
    const uint8_t autoforward;
    const scxml_elem_param* params;
    exec_content_finalize_t finalize;
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
    uint8_t        flags;
    const scxml_machine* machine;

    char config[SCXML_MAX_NR_STATES_BYTES];
    char history[SCXML_MAX_NR_STATES_BYTES];
    char invocations[SCXML_MAX_NR_STATES_BYTES];
    char initialized_data[SCXML_MAX_NR_STATES_BYTES];

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

static const scxml_elem_data _scxml_6A932FF1_elem_datas[2] = {
    /* id, src, expr, content */
    { "Var1", NULL, "1", NULL },
    { NULL, NULL, NULL, NULL }
};

static const scxml_elem_param _scxml_6A932FF1_elem_params[2] = {
    /* name, expr, location */
    { "aParam", "2", NULL },
    { NULL, NULL, NULL }
};

static const scxml_elem_send _scxml_6A932FF1_elem_sends[2] = {
    { 
        /* event       */ "timeout", 
        /* eventexpr   */ NULL, 
        /* target      */ NULL, 
        /* targetexpr  */ NULL, 
        /* type        */ NULL, 
        /* typeexpr    */ NULL, 
        /* id          */ NULL, 
        /* idlocation  */ NULL, 
        /* delay       */ "300s", 
        /* delayexpr   */ NULL, 
        /* namelist    */ NULL, 
        /* content     */ NULL,
        /* contentexpr */ NULL,
        /* params      */ NULL 
    },
    { 
        /* event       */ "childToParent", 
        /* eventexpr   */ NULL, 
        /* target      */ "#_parent", 
        /* targetexpr  */ NULL, 
        /* type        */ NULL, 
        /* typeexpr    */ NULL, 
        /* id          */ NULL, 
        /* idlocation  */ NULL, 
        /* delay       */ NULL, 
        /* delayexpr   */ NULL, 
        /* namelist    */ NULL, 
        /* content     */ NULL,
        /* contentexpr */ NULL,
        /* params      */ &_scxml_6A932FF1_elem_params[0] 
    }
};

static const scxml_elem_donedata _scxml_6A932FF1_elem_donedatas[1] = {
    /* source, content, contentexpr, params */
    { 0, NULL, NULL, NULL }
};

static int _scxml_6A932FF1_s0_invoke0_finalize0(const scxml_ctx* ctx, const scxml_elem_invoke* invocation, const void* event) {
    int err = SCXML_ERR_OK;
    if likely(ctx->exec_content_assign != NULL) {
        if ((ctx->exec_content_assign(ctx, "Var1", "_event.data.aParam")) != SCXML_ERR_OK) return err;
    } else {
        return SCXML_ERR_MISSING_CALLBACK;
    }
    return SCXML_ERR_OK;
}

static const scxml_elem_invoke _scxml_6A932FF1_elem_invokes[1] = {
    { 
        /* machine     */ &scxml_machines[1], 
        /* type        */ "http://www.w3.org/TR/scxml/", 
        /* typeexpr    */ NULL, 
        /* src         */ NULL, 
        /* srcexpr     */ NULL, 
        /* id          */ "d2170d67-da91-4aba-99a1-b1c021513e75", 
        /* idlocation  */ NULL, 
        /* namelist    */ NULL, 
        /* autoforward */ 0, 
        /* params      */ NULL, 
        /* finalize    */ _scxml_6A932FF1_s0_invoke0_finalize0, 
        /* content     */ NULL,
        /* contentexpr */ NULL,
    }
};

static int _scxml_6A932FF1_s0_on_entry_0(const scxml_ctx* ctx, const scxml_state* state, const void* event) {
    int err = SCXML_ERR_OK;
    if likely(ctx->exec_content_send != NULL) {
        if ((ctx->exec_content_send(ctx, &_scxml_6A932FF1_elem_sends[0])) != SCXML_ERR_OK) return err;
    } else {
        return SCXML_ERR_MISSING_CALLBACK;
    }
    return SCXML_ERR_OK;
}

static int _scxml_6A932FF1_s0_on_entry(const scxml_ctx* ctx, const scxml_state* state, const void* event) {
    _scxml_6A932FF1_s0_on_entry_0(ctx, state, event);
    return SCXML_ERR_OK;
}

static int _scxml_6A932FF1_s0_invoke(const scxml_ctx* ctx, const scxml_state* s, const scxml_elem_invoke* invocation, uint8_t uninvoke) {
    ctx->invoke(ctx, s, &_scxml_6A932FF1_elem_invokes[0], uninvoke);

    return SCXML_ERR_OK;
}
static int _scxml_6A932FF1_pass_on_entry_0(const scxml_ctx* ctx, const scxml_state* state, const void* event) {
    int err = SCXML_ERR_OK;
    if likely(ctx->exec_content_log != NULL) {
        if unlikely((ctx->exec_content_log(ctx, "Outcome", "'pass'")) != SCXML_ERR_OK) return err;
    } else {
        return SCXML_ERR_MISSING_CALLBACK;
    }
    return SCXML_ERR_OK;
}

static int _scxml_6A932FF1_pass_on_entry(const scxml_ctx* ctx, const scxml_state* state, const void* event) {
    _scxml_6A932FF1_pass_on_entry_0(ctx, state, event);
    return SCXML_ERR_OK;
}

static int _scxml_6A932FF1_fail_on_entry_0(const scxml_ctx* ctx, const scxml_state* state, const void* event) {
    int err = SCXML_ERR_OK;
    if likely(ctx->exec_content_log != NULL) {
        if unlikely((ctx->exec_content_log(ctx, "Outcome", "'fail'")) != SCXML_ERR_OK) return err;
    } else {
        return SCXML_ERR_MISSING_CALLBACK;
    }
    return SCXML_ERR_OK;
}

static int _scxml_6A932FF1_fail_on_entry(const scxml_ctx* ctx, const scxml_state* state, const void* event) {
    _scxml_6A932FF1_fail_on_entry_0(ctx, state, event);
    return SCXML_ERR_OK;
}

static const scxml_state _scxml_6A932FF1_states[4] = {
    {   /* state number 0 */
        /* name       */ NULL,
        /* parent     */ 0,
        /* onentry    */ NULL,
        /* onexit     */ NULL,
        /* invoke     */ NULL,
        /* children   */ { 0x0e /* 0111 */ },
        /* completion */ { 0x02 /* 0100 */ }, 	
        /* ancestors  */ { 0x00 /* 0000 */ },
        /* data       */ &_scxml_6A932FF1_elem_datas[0],
        /* type       */ SCXML_STATE_COMPOUND,
    },
    {   /* state number 1 */
        /* name       */ "s0",
        /* parent     */ 0,
        /* onentry    */ _scxml_6A932FF1_s0_on_entry,
        /* onexit     */ NULL,
        /* invoke     */ _scxml_6A932FF1_s0_invoke,
        /* children   */ { 0x00 /* 0000 */ },
        /* completion */ { 0x00 /* 0000 */ }, 	
        /* ancestors  */ { 0x01 /* 1000 */ },
        /* data       */ NULL,
        /* type       */ SCXML_STATE_ATOMIC,
    },
    {   /* state number 2 */
        /* name       */ "pass",
        /* parent     */ 0,
        /* onentry    */ _scxml_6A932FF1_pass_on_entry,
        /* onexit     */ NULL,
        /* invoke     */ NULL,
        /* children   */ { 0x00 /* 0000 */ },
        /* completion */ { 0x00 /* 0000 */ }, 	
        /* ancestors  */ { 0x01 /* 1000 */ },
        /* data       */ NULL,
        /* type       */ SCXML_STATE_FINAL,
    },
    {   /* state number 3 */
        /* name       */ "fail",
        /* parent     */ 0,
        /* onentry    */ _scxml_6A932FF1_fail_on_entry,
        /* onexit     */ NULL,
        /* invoke     */ NULL,
        /* children   */ { 0x00 /* 0000 */ },
        /* completion */ { 0x00 /* 0000 */ }, 	
        /* ancestors  */ { 0x01 /* 1000 */ },
        /* data       */ NULL,
        /* type       */ SCXML_STATE_FINAL,
    }
};

static const scxml_transition _scxml_6A932FF1_transitions[2] = {
    {   /* transition number 0 with priority 0
           target: pass
         */
        /* source     */ 1,
        /* target     */ { 0x04 /* 0010 */ },
        /* event      */ "childToParent",
        /* condition  */ "Var1==2",
        /* ontrans    */ NULL,
        /* type       */ 0,
        /* conflicts  */ { 0x03 /* 11 */ }, 
        /* exit set   */ { 0x0e /* 0111 */ }
    },
    {   /* transition number 1 with priority 1
           target: fail
         */
        /* source     */ 1,
        /* target     */ { 0x08 /* 0001 */ },
        /* event      */ "*",
        /* condition  */ NULL,
        /* ontrans    */ NULL,
        /* type       */ 0,
        /* conflicts  */ { 0x03 /* 11 */ }, 
        /* exit set   */ { 0x0e /* 0111 */ }
    }
};

static const scxml_elem_param _scxml_74EC8913_elem_params[2] = {
    /* name, expr, location */
    { "aParam", "2", NULL },
    { NULL, NULL, NULL }
};

static const scxml_elem_send _scxml_74EC8913_elem_sends[1] = {
    { 
        /* event       */ "childToParent", 
        /* eventexpr   */ NULL, 
        /* target      */ "#_parent", 
        /* targetexpr  */ NULL, 
        /* type        */ NULL, 
        /* typeexpr    */ NULL, 
        /* id          */ NULL, 
        /* idlocation  */ NULL, 
        /* delay       */ NULL, 
        /* delayexpr   */ NULL, 
        /* namelist    */ NULL, 
        /* content     */ NULL,
        /* contentexpr */ NULL,
        /* params      */ &_scxml_74EC8913_elem_params[0] 
    }
};

static const scxml_elem_donedata _scxml_74EC8913_elem_donedatas[1] = {
    /* source, content, contentexpr, params */
    { 0, NULL, NULL, NULL }
};

static int _scxml_74EC8913_subFinal_on_entry_0(const scxml_ctx* ctx, const scxml_state* state, const void* event) {
    int err = SCXML_ERR_OK;
    if likely(ctx->exec_content_send != NULL) {
        if ((ctx->exec_content_send(ctx, &_scxml_74EC8913_elem_sends[0])) != SCXML_ERR_OK) return err;
    } else {
        return SCXML_ERR_MISSING_CALLBACK;
    }
    return SCXML_ERR_OK;
}

static int _scxml_74EC8913_subFinal_on_entry(const scxml_ctx* ctx, const scxml_state* state, const void* event) {
    _scxml_74EC8913_subFinal_on_entry_0(ctx, state, event);
    return SCXML_ERR_OK;
}

static const scxml_state _scxml_74EC8913_states[2] = {
    {   /* state number 0 */
        /* name       */ NULL,
        /* parent     */ 0,
        /* onentry    */ NULL,
        /* onexit     */ NULL,
        /* invoke     */ NULL,
        /* children   */ { 0x02 /* 01 */ },
        /* completion */ { 0x02 /* 01 */ }, 	
        /* ancestors  */ { 0x00 /* 00 */ },
        /* data       */ NULL,
        /* type       */ SCXML_STATE_COMPOUND,
    },
    {   /* state number 1 */
        /* name       */ "subFinal",
        /* parent     */ 0,
        /* onentry    */ _scxml_74EC8913_subFinal_on_entry,
        /* onexit     */ NULL,
        /* invoke     */ NULL,
        /* children   */ { 0x00 /* 00 */ },
        /* completion */ { 0x00 /* 00 */ }, 	
        /* ancestors  */ { 0x01 /* 10 */ },
        /* data       */ NULL,
        /* type       */ SCXML_STATE_FINAL,
    }
};

static const scxml_transition _scxml_74EC8913_transitions[0] = {
};

const scxml_machine scxml_machines[3] = {
    {
        /* flags          */ 0,
        /* nr_states      */ 4,
        /* nr_transitions */ 2,
        /* name           */ "",
        /* datamodel      */ "ecmascript",
        /* uuid           */ "6A932FF17BFF1735E3F3C77F7B54C218",
        /* states         */ &_scxml_6A932FF1_states[0], 
        /* transitions    */ &_scxml_6A932FF1_transitions[0], 
        /* parent         */ NULL,
        /* donedata       */ &_scxml_6A932FF1_elem_donedatas[0], 
        /* script         */ NULL
    },
    {
        /* flags          */ 0,
        /* nr_states      */ 2,
        /* nr_transitions */ 0,
        /* name           */ "",
        /* datamodel      */ "ecmascript",
        /* uuid           */ "74EC8913A9386F1A7EC5EF2A0426752B",
        /* states         */ &_scxml_74EC8913_states[0], 
        /* transitions    */ &_scxml_74EC8913_transitions[0], 
        /* parent         */ &scxml_machines[0],
        /* donedata       */ &_scxml_74EC8913_elem_donedatas[0], 
        /* script         */ NULL
    },
    {0, 0, 0, NULL, NULL, NULL, NULL, NULL, NULL }
};

#ifdef SCXML_VERBOSE
static void printStateNames(const scxml_ctx* ctx, const char* a, size_t length) {
    size_t i;
    const char* seperator = "";
    for (i = 0; i < length; i++) {
        if (BIT_HAS(i, a)) {
            printf("%s%s", seperator, (ctx->machine->states[i].name != NULL ? ctx->machine->states[i].name : "UNK"));
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
    while(i--) {
        if (a[i] & b[i])
            return 1;
    }
    return 0;
}

static void bit_clear_all(char* a, size_t i) {
    while(i--) {
        a[i] = 0;
    }
}

static int bit_has_any(const char* a, size_t i) {
    while(i--) {
        if (a[i] > 0)
            return 1;
    }
    return 0;
}

static void bit_or(char* dest, const char* mask, size_t i) {
    while(i--) {
        dest[i] |= mask[i];
    }
}

static void bit_copy(char* dest, const char* source, size_t i) {
    while(i--) {
        dest[i] = source[i];
    }
}

static void bit_and_not(char* dest, const char* mask, size_t i) {
    while(i--) {
        dest[i] &= ~mask[i];
    }
}

static void bit_and(char* dest, const char* mask, size_t i) {
    while(i--) {
        dest[i] &= mask[i];
    };
}

int scxml_step(scxml_ctx* ctx) {

#ifdef SCXML_VERBOSE
    printf("Config: ");
    printStateNames(ctx, ctx->config, SCXML_NUMBER_STATES);
#endif

    if (ctx->flags & SCXML_CTX_TOP_LEVEL_FINAL) 
        return SCXML_ERR_DONE; 

    SCXML_NR_STATES_TYPE i, j, k;
    SCXML_NR_STATES_TYPE nr_states_bytes = ((SCXML_NUMBER_STATES + 7) & ~7) >> 3;
    SCXML_NR_TRANS_TYPE  nr_trans_bytes  = ((SCXML_NUMBER_TRANS + 7) & ~7) >> 3;
    int err = SCXML_ERR_OK;
    char conflicts  [SCXML_MAX_NR_TRANS_BYTES];
    char trans_set  [SCXML_MAX_NR_TRANS_BYTES];
    char target_set [SCXML_MAX_NR_STATES_BYTES];
    char exit_set   [SCXML_MAX_NR_STATES_BYTES];
    char entry_set  [SCXML_MAX_NR_STATES_BYTES];
    char tmp_states [SCXML_MAX_NR_STATES_BYTES];

    bit_clear_all(target_set, nr_states_bytes);
    bit_clear_all(trans_set, nr_trans_bytes);
    if unlikely(ctx->flags == SCXML_CTX_PRISTINE) {
        if (ctx->machine->script != NULL)
            ctx->machine->script(ctx, &ctx->machine->states[0], NULL);
        bit_or(target_set, ctx->machine->states[0].completion, nr_states_bytes);
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

    // manage invocations
    for (i = 0; i < SCXML_NUMBER_STATES; i++) {
        // uninvoke
        if (!BIT_HAS(i, ctx->config) && BIT_HAS(i, ctx->invocations)) {
            if (ctx->machine->states[i].invoke != NULL)
                ctx->machine->states[i].invoke(ctx, &ctx->machine->states[i], NULL, 1);
            BIT_CLEAR(i, ctx->invocations)
        }
        // invoke
        if (BIT_HAS(i, ctx->config) && !BIT_HAS(i, ctx->invocations)) {
            if (ctx->machine->states[i].invoke != NULL)
                ctx->machine->states[i].invoke(ctx, &ctx->machine->states[i], NULL, 0);
            BIT_SET_AT(i, ctx->invocations)
        }
    }

    if ((ctx->event = ctx->dequeue_external(ctx)) != NULL) {
        goto SELECT_TRANSITIONS;
    }

SELECT_TRANSITIONS:
    bit_clear_all(conflicts, nr_trans_bytes);
    bit_clear_all(exit_set, nr_states_bytes);
    for (i = 0; i < SCXML_NUMBER_TRANS; i++) {
        // never select history or initial transitions automatically
        if unlikely(ctx->machine->transitions[i].type & (SCXML_TRANS_HISTORY | SCXML_TRANS_INITIAL))
            continue;

        // is the transition active?
        if (BIT_HAS(ctx->machine->transitions[i].source, ctx->config)) {
            // is it non-conflicting?
            if (!BIT_HAS(i, conflicts)) {
                // is it enabled?
                if (ctx->is_enabled(ctx, &ctx->machine->transitions[i], ctx->event) > 0) {
                    // remember that we found a transition
                    ctx->flags |= SCXML_CTX_TRANSITION_FOUND;

                    // transitions that are pre-empted
                    bit_or(conflicts, ctx->machine->transitions[i].conflicts, nr_trans_bytes);

                    // states that are directly targeted (resolve as entry-set later)
                    bit_or(target_set, ctx->machine->transitions[i].target, nr_states_bytes);

                    // states that will be left
                    bit_or(exit_set, ctx->machine->transitions[i].exit_set, nr_states_bytes);

                    BIT_SET_AT(i, trans_set);
                }
            }
        }
    }
    bit_and(exit_set, ctx->config, nr_states_bytes);

    if (ctx->flags & SCXML_CTX_TRANSITION_FOUND) {
        ctx->flags |= SCXML_CTX_SPONTANEOUS;
        ctx->flags &= ~SCXML_CTX_TRANSITION_FOUND;
    } else {
        ctx->flags &= ~SCXML_CTX_SPONTANEOUS;
    }

#ifdef SCXML_VERBOSE
    printf("Targets: ");
    printStateNames(ctx, target_set, SCXML_NUMBER_STATES);
#endif

#ifdef SCXML_VERBOSE
    printf("Exiting: ");
    printStateNames(ctx, exit_set, SCXML_NUMBER_STATES);
#endif

#ifdef SCXML_VERBOSE
    printf("History: ");
    printStateNames(ctx, ctx->history, SCXML_NUMBER_STATES);
#endif

// REMEMBER_HISTORY:
    for (i = 0; i < SCXML_NUMBER_STATES; i++) {
        if unlikely(SCXML_STATE_MASK(ctx->machine->states[i].type) == SCXML_STATE_HISTORY_SHALLOW ||
                    SCXML_STATE_MASK(ctx->machine->states[i].type) == SCXML_STATE_HISTORY_DEEP) {
            // a history state whose parent is about to be exited
            if unlikely(BIT_HAS(ctx->machine->states[i].parent, exit_set)) {
                bit_copy(tmp_states, ctx->machine->states[i].completion, nr_states_bytes);

                // set those states who were enabled
                bit_and(tmp_states, ctx->config, nr_states_bytes);

                // clear current history with completion mask
                bit_and_not(ctx->history, ctx->machine->states[i].completion, nr_states_bytes);

                // set history
                bit_or(ctx->history, tmp_states, nr_states_bytes);
            }
        }
    }

ESTABLISH_ENTRY_SET:
    // calculate new entry set
    bit_copy(entry_set, target_set, nr_states_bytes);

    // iterate for ancestors
    for (i = 0; i < SCXML_NUMBER_STATES; i++) {
        if (BIT_HAS(i, entry_set)) {
            bit_or(entry_set, ctx->machine->states[i].ancestors, nr_states_bytes);
        }
    }

    // iterate for descendants
    for (i = 0; i < SCXML_NUMBER_STATES; i++) {
        if (BIT_HAS(i, entry_set)) {
            switch (SCXML_STATE_MASK(ctx->machine->states[i].type)) {
                case SCXML_STATE_PARALLEL: {
                    bit_or(entry_set, ctx->machine->states[i].completion, nr_states_bytes);
                    break;
                }
                case SCXML_STATE_HISTORY_SHALLOW:
                case SCXML_STATE_HISTORY_DEEP: {
                    if (!bit_has_and(ctx->machine->states[i].completion, ctx->history, nr_states_bytes) &&
                        !BIT_HAS(ctx->machine->states[i].parent, ctx->config)) {
                        // nothing set for history, look for a default transition
                        for (j = 0; j < SCXML_NUMBER_TRANS; j++) {
                            if unlikely(ctx->machine->transitions[j].source == i) {
                                bit_or(entry_set, ctx->machine->transitions[j].target, nr_states_bytes);
                                if(SCXML_STATE_MASK(ctx->machine->states[i].type) == SCXML_STATE_HISTORY_DEEP &&
                                   !bit_has_and(ctx->machine->transitions[j].target, ctx->machine->states[i].children, nr_states_bytes)) {
                                    for (k = i + 1; k < SCXML_NUMBER_STATES; k++) {
                                        if (BIT_HAS(k, ctx->machine->transitions[j].target)) {
                                            bit_or(entry_set, ctx->machine->states[k].ancestors, nr_states_bytes);
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
                        bit_copy(tmp_states, ctx->machine->states[i].completion, nr_states_bytes);
                        bit_and(tmp_states, ctx->history, nr_states_bytes);
                        bit_or(entry_set, tmp_states, nr_states_bytes);
                        if (ctx->machine->states[i].type == (SCXML_STATE_HAS_HISTORY | SCXML_STATE_HISTORY_DEEP)) {
                            // a deep history state with nested histories -> more completion
                            for (j = i + 1; j < SCXML_NUMBER_STATES; j++) {
                                if (BIT_HAS(j, ctx->machine->states[i].completion) &&
                                    BIT_HAS(j, entry_set) &&
                                    (ctx->machine->states[j].type & SCXML_STATE_HAS_HISTORY)) {
                                    for (k = j + 1; k < SCXML_NUMBER_STATES; k++) {
                                        // add nested history to entry_set
                                        if ((SCXML_STATE_MASK(ctx->machine->states[k].type) == SCXML_STATE_HISTORY_DEEP ||
                                             SCXML_STATE_MASK(ctx->machine->states[k].type) == SCXML_STATE_HISTORY_SHALLOW) &&
                                            BIT_HAS(k, ctx->machine->states[j].children)) {
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
                    for (j = 0; j < SCXML_NUMBER_TRANS; j++) {
                        if (ctx->machine->transitions[j].source == i) {
                            BIT_SET_AT(j, trans_set);
                            BIT_CLEAR(i, entry_set);
                            bit_or(entry_set, ctx->machine->transitions[j].target, nr_states_bytes);
                            for (k = i + 1; k < SCXML_NUMBER_STATES; k++) {
                                if (BIT_HAS(k, ctx->machine->transitions[j].target)) {
                                    bit_or(entry_set, ctx->machine->states[k].ancestors, nr_states_bytes);
                                }
                            }
                        }
                    }
                    break;
                }
                case SCXML_STATE_COMPOUND: { // we need to check whether one child is already in entry_set
                    if (!bit_has_and(entry_set, ctx->machine->states[i].children, nr_states_bytes) &&
                        (!bit_has_and(ctx->config, ctx->machine->states[i].children, nr_states_bytes) ||
                         bit_has_and(exit_set, ctx->machine->states[i].children, nr_states_bytes)))
                    {
                        bit_or(entry_set, ctx->machine->states[i].completion, nr_states_bytes);
                        if (!bit_has_and(ctx->machine->states[i].completion, ctx->machine->states[i].children, nr_states_bytes)) {
                            // deep completion
                            for (j = i + 1; j < SCXML_NUMBER_STATES; j++) {
                                if (BIT_HAS(j, ctx->machine->states[i].completion)) {
                                    bit_or(entry_set, ctx->machine->states[j].ancestors, nr_states_bytes);
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
    printBitsetIndices(trans_set, sizeof(char) * 8 * nr_trans_bytes);
#endif

// EXIT_STATES:
    i = SCXML_NUMBER_STATES;
    while(i-- > 0) {
        if (BIT_HAS(i, exit_set) && BIT_HAS(i, ctx->config)) {
            // call all on exit handlers
            if (ctx->machine->states[i].on_exit != NULL) {
                if unlikely((err = ctx->machine->states[i].on_exit(ctx, &ctx->machine->states[i], ctx->event)) != SCXML_ERR_OK)
                    return err;
            }
            BIT_CLEAR(i, ctx->config);
        }
    }

// TAKE_TRANSITIONS:
    for (i = 0; i < SCXML_NUMBER_TRANS; i++) {
        if (BIT_HAS(i, trans_set) && (ctx->machine->transitions[i].type & (SCXML_TRANS_HISTORY | SCXML_TRANS_INITIAL)) == 0) {
            // call executable content in transition
            if (ctx->machine->transitions[i].on_transition != NULL) {
                if unlikely((err = ctx->machine->transitions[i].on_transition(ctx,
                                                                              &ctx->machine->states[ctx->machine->transitions[i].source],
                                                                              ctx->event)) != SCXML_ERR_OK)
                    return err;
            }
        }
    }

#ifdef SCXML_VERBOSE
    printf("Entering: ");
    printStateNames(ctx, entry_set, SCXML_NUMBER_STATES);
#endif

// ENTER_STATES:
    for (i = 0; i < SCXML_NUMBER_STATES; i++) {
        if (BIT_HAS(i, entry_set) && !BIT_HAS(i, ctx->config)) {
            // these are no proper states
            if unlikely(SCXML_STATE_MASK(ctx->machine->states[i].type) == SCXML_STATE_HISTORY_DEEP ||
                        SCXML_STATE_MASK(ctx->machine->states[i].type) == SCXML_STATE_HISTORY_SHALLOW ||
                        SCXML_STATE_MASK(ctx->machine->states[i].type) == SCXML_STATE_INITIAL)
                continue;

            BIT_SET_AT(i, ctx->config);

            // initialize data
            if (!BIT_HAS(i, ctx->initialized_data)) {
                if unlikely(ctx->machine->states[i].data != NULL && ctx->exec_content_init != NULL) {
                    ctx->exec_content_init(ctx, ctx->machine->states[i].data);
                }
                BIT_SET_AT(i, ctx->initialized_data);
            }

            if (ctx->machine->states[i].on_entry != NULL) {
                if unlikely((err = ctx->machine->states[i].on_entry(ctx, &ctx->machine->states[i], ctx->event)) != SCXML_ERR_OK)
                    return err;
            }

            // take history and initial transitions
            for (j = 0; j < SCXML_NUMBER_TRANS; j++) {
                if unlikely(BIT_HAS(j, trans_set) &&
                            (ctx->machine->transitions[j].type & (SCXML_TRANS_HISTORY | SCXML_TRANS_INITIAL)) &&
                            ctx->machine->states[ctx->machine->transitions[j].source].parent == i) {
                    // call executable content in transition
                    if (ctx->machine->transitions[j].on_transition != NULL) {
                        if unlikely((err = ctx->machine->transitions[j].on_transition(ctx,
                                                                                      &ctx->machine->states[i],
                                                                                      ctx->event)) != SCXML_ERR_OK)
                            return err;
                    }
                }
            }

            // handle final states
            if unlikely(SCXML_STATE_MASK(ctx->machine->states[i].type) == SCXML_STATE_FINAL) {
                if unlikely(ctx->machine->states[i].ancestors[0] == 0x01) {
                    ctx->flags |= SCXML_CTX_TOP_LEVEL_FINAL;
                } else {
                    // raise done event
                    const scxml_elem_donedata* donedata = &ctx->machine->donedata[0];
                    while(ELEM_DONEDATA_IS_SET(donedata)) {
                        if unlikely(donedata->source == i)
                            break;
                        donedata++;
                    }
                    ctx->raise_done_event(ctx, &ctx->machine->states[ctx->machine->states[i].parent], (ELEM_DONEDATA_IS_SET(donedata) ? donedata : NULL));
                }

                /**
                 * are we the last final state to leave a parallel state?:
                 * 1. Gather all parallel states in our ancestor chain
                 * 2. Find all states for which these parallels are ancestors
                 * 3. Iterate all active final states and remove their ancestors
                 * 4. If a state remains, not all children of a parallel are final
                 */
                for (j = 0; j < SCXML_NUMBER_STATES; j++) {
                    if unlikely(SCXML_STATE_MASK(ctx->machine->states[j].type) == SCXML_STATE_PARALLEL &&
                                BIT_HAS(j, ctx->machine->states[i].ancestors)) {
                        bit_clear_all(tmp_states, nr_states_bytes);
                        for (k = 0; k < SCXML_NUMBER_STATES; k++) {
                            if unlikely(BIT_HAS(j, ctx->machine->states[k].ancestors) && BIT_HAS(k, ctx->config)) {
                                if (SCXML_STATE_MASK(ctx->machine->states[k].type) == SCXML_STATE_FINAL) {
                                    bit_and_not(tmp_states, ctx->machine->states[k].ancestors, nr_states_bytes);
                                } else {
                                    BIT_SET_AT(k, tmp_states);
                                }
                            }
                        }
                        if unlikely(!bit_has_any(tmp_states, nr_states_bytes)) {
                            ctx->raise_done_event(ctx, &ctx->machine->states[j], NULL);
                        }
                    }
                }

            }

        }
    }

    return SCXML_ERR_OK;
}

