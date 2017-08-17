/**
  Generated from source:
  file:///C:/cygwin64/home/Puneet/ContikiBinding/test/promela/scxml-files/test144.scxml
*/

#ifndef USCXML_NO_STDTYPES_H
#  include <stdint.h> /* explicit types */
#endif
#include <stddef.h> /* NULL */

#ifndef USCXML_NO_GEN_C_MACROS

/**
 * All macros used for the scxml types and functions
 * 
 * ** IMPORTANT: Make sure to set the following macros prior to including. **
 *               They are used to represent the machine in the types to follow
 *               and to allocate stack memory during a micro-step function.
 *               When in doubt, overprovide.
 * 
 *    USCXML_NR_STATES_TYPE
 *      as the smallest type for positive integers that can contain the
 *      largest number of states from an individual state machine. E.g.:
 *      < 2^8  states => uint8_t
 *      < 2^16 states => uint16_t
 *      < 2^32 states => uint32_t
 */

#ifndef USCXML_NR_STATES_TYPE 
#  define USCXML_NR_STATES_TYPE uint8_t
#endif 

/**
 *    USCXML_NR_TRANS_TYPE
 *      the same as above but for the number of transitions.
 */

#ifndef USCXML_NR_TRANS_TYPE 
#  define USCXML_NR_TRANS_TYPE uint8_t
#endif 

/** 
 *    USCXML_MAX_NR_STATES_BYTES
 *      the smallest multiple of 8 that, if multiplied by 8,
 *      is larger than USCXML_NR_STATES_TYPE, e.g:
 *      1-8   states => 1
 *      9-16  states => 2
 *      17-24 states => 3
 *      25-32 states => 4
 *      ...
 */

#ifndef USCXML_MAX_NR_STATES_BYTES 
#  define USCXML_MAX_NR_STATES_BYTES 1
#endif 

/**
 *    USCXML_MAX_NR_TRANS_BYTES
 *      same as above but for transitions.
 */

#ifndef USCXML_MAX_NR_TRANS_BYTES 
#  define USCXML_MAX_NR_TRANS_BYTES 1
#endif 

/**
 *    USCXML_NUMBER_STATES / USCXML_NUMBER_TRANS
 *      Per default the number of states / transitions is retrieved from the machine
 *      info in the uscxml_ctx struct, but you can also hard-code it per macro.
 */

#ifndef USCXML_NUMBER_STATES
#  define USCXML_NUMBER_STATES (ctx->machine->nr_states)
#endif

#ifndef USCXML_NUMBER_TRANS
#  define USCXML_NUMBER_TRANS (ctx->machine->nr_transitions)
#endif

/**
 *    USCXML_GET_STATE / USCXML_GET_TRANS
 *      Per default an individual state or transitions is retrieved from the machine
 *      info in the uscxml_ctx struct, but you can also hard-code it per macro.
 */

#ifndef USCXML_GET_STATE
#  define USCXML_GET_STATE(i) (ctx->machine->states[i])
#endif

#ifndef USCXML_GET_TRANS
#  define USCXML_GET_TRANS(i) (ctx->machine->transitions[i])
#endif


/* Common macros below */

#define BIT_HAS(idx, bitset)   ((bitset[idx >> 3] &  (1 << (idx & 7))) != 0)
#define BIT_SET_AT(idx, bitset)  bitset[idx >> 3] |= (1 << (idx & 7));
#define BIT_CLEAR(idx, bitset)   bitset[idx >> 3] &= (1 << (idx & 7)) ^ 0xFF;

#ifdef __GNUC__
#  define likely(x)       (__builtin_expect(!!(x), 1))
#  define unlikely(x)     (__builtin_expect(!!(x), 0))
#else
#  define likely(x)       (x)
#  define unlikely(x)     (x)
#endif

/* error return codes */
#define USCXML_ERR_OK                0
#define USCXML_ERR_IDLE              1
#define USCXML_ERR_DONE              2
#define USCXML_ERR_MISSING_CALLBACK  3
#define USCXML_ERR_FOREACH_DONE      4
#define USCXML_ERR_EXEC_CONTENT      5
#define USCXML_ERR_INVALID_TARGET    6
#define USCXML_ERR_INVALID_TYPE      7
#define USCXML_ERR_UNSUPPORTED       8

#define USCXML_TRANS_SPONTANEOUS      0x01
#define USCXML_TRANS_TARGETLESS       0x02
#define USCXML_TRANS_INTERNAL         0x04
#define USCXML_TRANS_HISTORY          0x08
#define USCXML_TRANS_INITIAL          0x10

#define USCXML_STATE_ATOMIC           0x01
#define USCXML_STATE_PARALLEL         0x02
#define USCXML_STATE_COMPOUND         0x03
#define USCXML_STATE_FINAL            0x04
#define USCXML_STATE_HISTORY_DEEP     0x05
#define USCXML_STATE_HISTORY_SHALLOW  0x06
#define USCXML_STATE_INITIAL          0x07
#define USCXML_STATE_HAS_HISTORY      0x80  /* highest bit */
#define USCXML_STATE_MASK(t)     (t & 0x7F) /* mask highest bit */

#define USCXML_CTX_PRISTINE           0x00
#define USCXML_CTX_SPONTANEOUS        0x01
#define USCXML_CTX_INITIALIZED        0x02
#define USCXML_CTX_TOP_LEVEL_FINAL    0x04
#define USCXML_CTX_TRANSITION_FOUND   0x08
#define USCXML_CTX_FINISHED           0x10

#define USCXML_ELEM_DATA_IS_SET(data) (data->id != NULL)
#define USCXML_ELEM_DONEDATA_IS_SET(donedata) (donedata->content != NULL || donedata->contentexpr != NULL || donedata->params != NULL)
#define USCXML_ELEM_PARAM_IS_SET(param) (param->name != NULL)
#define USCXML_MACHINE_IS_SET(machine) (machine->nr_states > 0)

#define USCXML_NO_GEN_C_MACROS
#endif


#ifndef USCXML_NO_GEN_C_TYPES

/**
 * All types required to represent an SCXML state chart.
 * Just predefine the USCXML_NO_GEN_C_TYPES macro if you do not need them.
 */

typedef struct uscxml_machine uscxml_machine;
typedef struct uscxml_transition uscxml_transition;
typedef struct uscxml_state uscxml_state;
typedef struct uscxml_ctx uscxml_ctx;
typedef struct uscxml_elem_invoke uscxml_elem_invoke;

typedef struct uscxml_elem_send uscxml_elem_send;
typedef struct uscxml_elem_param uscxml_elem_param;
typedef struct uscxml_elem_data uscxml_elem_data;
typedef struct uscxml_elem_assign uscxml_elem_assign;
typedef struct uscxml_elem_donedata uscxml_elem_donedata;
typedef struct uscxml_elem_foreach uscxml_elem_foreach;

typedef void* (*dequeue_internal_t)(const uscxml_ctx* ctx);
typedef void* (*dequeue_external_t)(const uscxml_ctx* ctx);
typedef int (*is_enabled_t)(const uscxml_ctx* ctx, const uscxml_transition* transition);
typedef int (*is_matched_t)(const uscxml_ctx* ctx, const uscxml_transition* transition, const void* event);
typedef int (*is_true_t)(const uscxml_ctx* ctx, const char* expr);
typedef int (*exec_content_t)(const uscxml_ctx* ctx, const uscxml_state* state, const void* event);
typedef int (*raise_done_event_t)(const uscxml_ctx* ctx, const uscxml_state* state, const uscxml_elem_donedata* donedata);
typedef int (*invoke_t)(const uscxml_ctx* ctx, const uscxml_state* s, const uscxml_elem_invoke* invocation, unsigned char uninvoke);

typedef int (*exec_content_log_t)(const uscxml_ctx* ctx, const char* label, const char* expr);
typedef int (*exec_content_raise_t)(const uscxml_ctx* ctx, const char* event);
typedef int (*exec_content_send_t)(const uscxml_ctx* ctx, const uscxml_elem_send* send);
typedef int (*exec_content_foreach_init_t)(const uscxml_ctx* ctx, const uscxml_elem_foreach* foreach);
typedef int (*exec_content_foreach_next_t)(const uscxml_ctx* ctx, const uscxml_elem_foreach* foreach);
typedef int (*exec_content_foreach_done_t)(const uscxml_ctx* ctx, const uscxml_elem_foreach* foreach);
typedef int (*exec_content_assign_t)(const uscxml_ctx* ctx, const uscxml_elem_assign* assign);
typedef int (*exec_content_init_t)(const uscxml_ctx* ctx, const uscxml_elem_data* data);
typedef int (*exec_content_cancel_t)(const uscxml_ctx* ctx, const char* sendid, const char* sendidexpr);
typedef int (*exec_content_finalize_t)(const uscxml_ctx* ctx, const uscxml_elem_invoke* invoker, const void* event);
typedef int (*exec_content_script_t)(const uscxml_ctx* ctx, const char* src, const char* content);

/**
 * A single SCXML state-machine.
 */
struct uscxml_machine {
    unsigned char               flags;           /* Unused */
    USCXML_NR_STATES_TYPE       nr_states;       /* Make sure to set type per macro! */
    USCXML_NR_TRANS_TYPE        nr_transitions;  /* Make sure to set type per macro! */
    const char*                 name;
    const char*                 datamodel;
    const char*                 uuid;            /* currently MD5 sum */
    const uscxml_state*         states;
    const uscxml_transition*    transitions;
    const uscxml_machine*       parent;
    const uscxml_elem_donedata* donedata;
    const exec_content_t        script;          /* Global script elements */
};

/**
 * All information pertaining to a <data> element->
 * With late data binding, blocks of data elements are separated by NULL
 * use USCXML_ELEM_DATA_IS_SET to test for end of a block.
 */
struct uscxml_elem_data {
    const char* id;
    const char* src;
    const char* expr;
    const char* content;
};

/**
 * All information pertaining to an <assign> element->
 */
struct uscxml_elem_assign {
    const char* location;
    const char* expr;
    const char* content;
};

/**
 * All information pertaining to any state element->
 */
struct uscxml_state {
    const char* name;                                  /* eventual name          */
    const USCXML_NR_STATES_TYPE parent;                /* parent                 */
    const exec_content_t on_entry;                     /* on entry handlers      */
    const exec_content_t on_exit;                      /* on exit handlers       */
    const invoke_t invoke;                             /* invocations            */
    const unsigned char children[USCXML_MAX_NR_STATES_BYTES];   /* all children           */
    const unsigned char completion[USCXML_MAX_NR_STATES_BYTES]; /* default completion     */
    const unsigned char ancestors[USCXML_MAX_NR_STATES_BYTES];  /* all ancestors          */
    const uscxml_elem_data* data;                      /* data with late binding */
    const unsigned char type;                          /* One of USCXML_STATE_*  */
};

/**
 * All information pertaining to a <transitions> element->
 */
struct uscxml_transition {
    const USCXML_NR_STATES_TYPE source;
    const unsigned char target[USCXML_MAX_NR_STATES_BYTES];
    const char* event;
    const char* condition;
    const is_enabled_t is_enabled;
    const exec_content_t on_transition;
    const unsigned char type;
    const unsigned char conflicts[USCXML_MAX_NR_TRANS_BYTES];
    const unsigned char exit_set[USCXML_MAX_NR_STATES_BYTES];
};

/**
 * All information pertaining to a <foreach> element->
 */
struct uscxml_elem_foreach {
    const char* array;
    const char* item;
    const char* index;
};

/**
 * All information pertaining to a <param> element->
 * Blocks of params are separated by NULL params, use
 * USCXML_ELEM_PARAM_IS_SET to test for end of a block.
 */
struct uscxml_elem_param {
    const char* name;
    const char* expr;
    const char* location;
};

/**
 * All information pertaining to a <donedata> element->
 */
struct uscxml_elem_donedata {
    const USCXML_NR_STATES_TYPE source;
    const char* content;
    const char* contentexpr;
    const uscxml_elem_param* params;
};

/**
 * All information pertaining to an <invoke> element->
 */
struct uscxml_elem_invoke {
    const uscxml_machine* machine;
    const char* type;
    const char* typeexpr;
    const char* src;
    const char* srcexpr;
    const char* id;
    const char* idlocation;
    const char* sourcename;
    const char* namelist;
    const unsigned char autoforward;
    const uscxml_elem_param* params;
    exec_content_finalize_t finalize;
    const char* content;
    const char* contentexpr;
};

/**
 * All information pertaining to a <send> element->
 */
struct uscxml_elem_send {
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
    const char* namelist;    /* not space-separated, still as in attribute value */
    const char* content;
    const char* contentexpr;
    const uscxml_elem_param* params;
};

/**
 * Represents an instance of a state-chart at runtime/
 */
struct uscxml_ctx {
    unsigned char         flags;
    const uscxml_machine* machine;

    unsigned char config[USCXML_MAX_NR_STATES_BYTES]; /* Make sure these macros specify a sufficient size */
    unsigned char history[USCXML_MAX_NR_STATES_BYTES];
    unsigned char invocations[USCXML_MAX_NR_STATES_BYTES];
    unsigned char initialized_data[USCXML_MAX_NR_STATES_BYTES];

    void* user_data;
    void* event;

    dequeue_internal_t dequeue_internal;
    dequeue_external_t dequeue_external;
    is_matched_t       is_matched;
    is_true_t          is_true;
    raise_done_event_t raise_done_event;

    exec_content_log_t          exec_content_log;
    exec_content_raise_t        exec_content_raise;
    exec_content_send_t         exec_content_send;
    exec_content_foreach_init_t exec_content_foreach_init;
    exec_content_foreach_next_t exec_content_foreach_next;
    exec_content_foreach_done_t exec_content_foreach_done;
    exec_content_assign_t       exec_content_assign;
    exec_content_init_t         exec_content_init;
    exec_content_cancel_t       exec_content_cancel;
    exec_content_script_t       exec_content_script;

    invoke_t invoke;
};

#define USCXML_NO_GEN_C_TYPES
#endif

/* forward declare machines to allow references */
extern const uscxml_machine _uscxml_32F2390B__machine;

#ifndef USCXML_NO_ELEM_INFO

static const uscxml_elem_donedata _uscxml_32F2390B__elem_donedatas[1] = {
    /* source, content, contentexpr, params */
    { 0, NULL, NULL, NULL }
};

#endif

#ifndef USCXML_NO_ELEM_INFO

#endif

#ifndef USCXML_NO_EXEC_CONTENT

static int _uscxml_32F2390B__s0_on_entry_0(const uscxml_ctx* ctx, const uscxml_state* state, const void* event) {
    int err = USCXML_ERR_OK;
    if likely(ctx->exec_content_raise != NULL) {
        if unlikely((ctx->exec_content_raise(ctx, "foo")) != USCXML_ERR_OK) return err;
    } else {
        return USCXML_ERR_MISSING_CALLBACK;
    }
    if likely(ctx->exec_content_raise != NULL) {
        if unlikely((ctx->exec_content_raise(ctx, "bar")) != USCXML_ERR_OK) return err;
    } else {
        return USCXML_ERR_MISSING_CALLBACK;
    }
    return USCXML_ERR_OK;
}

static int _uscxml_32F2390B__s0_on_entry(const uscxml_ctx* ctx, const uscxml_state* state, const void* event) {
    _uscxml_32F2390B__s0_on_entry_0(ctx, state, event);
    return USCXML_ERR_OK;
}

static int _uscxml_32F2390B__pass_on_entry_0(const uscxml_ctx* ctx, const uscxml_state* state, const void* event) {
    int err = USCXML_ERR_OK;
    if likely(ctx->exec_content_log != NULL) {
        if unlikely((ctx->exec_content_log(ctx, "Outcome", "'pass'")) != USCXML_ERR_OK) return err;
    } else {
        return USCXML_ERR_MISSING_CALLBACK;
    }
    return USCXML_ERR_OK;
}

static int _uscxml_32F2390B__pass_on_entry(const uscxml_ctx* ctx, const uscxml_state* state, const void* event) {
    _uscxml_32F2390B__pass_on_entry_0(ctx, state, event);
    return USCXML_ERR_OK;
}

static int _uscxml_32F2390B__fail_on_entry_0(const uscxml_ctx* ctx, const uscxml_state* state, const void* event) {
    int err = USCXML_ERR_OK;
    if likely(ctx->exec_content_log != NULL) {
        if unlikely((ctx->exec_content_log(ctx, "Outcome", "'fail'")) != USCXML_ERR_OK) return err;
    } else {
        return USCXML_ERR_MISSING_CALLBACK;
    }
    return USCXML_ERR_OK;
}

static int _uscxml_32F2390B__fail_on_entry(const uscxml_ctx* ctx, const uscxml_state* state, const void* event) {
    _uscxml_32F2390B__fail_on_entry_0(ctx, state, event);
    return USCXML_ERR_OK;
}

#endif

#ifndef USCXML_NO_ELEM_INFO

static const uscxml_state _uscxml_32F2390B__states[5] = {
    {   /* state number 0 */
        /* name       */ NULL,
        /* parent     */ 0,
        /* onentry    */ NULL,
        /* onexit     */ NULL,
        /* invoke     */ NULL,
        /* children   */ { 0x1e /* 01111 */ },
        /* completion */ { 0x02 /* 01000 */ }, 	
        /* ancestors  */ { 0x00 /* 00000 */ },
        /* data       */ NULL,
        /* type       */ USCXML_STATE_COMPOUND,
    },
    {   /* state number 1 */
        /* name       */ "s0",
        /* parent     */ 0,
        /* onentry    */ _uscxml_32F2390B__s0_on_entry,
        /* onexit     */ NULL,
        /* invoke     */ NULL,
        /* children   */ { 0x00 /* 00000 */ },
        /* completion */ { 0x00 /* 00000 */ }, 	
        /* ancestors  */ { 0x01 /* 10000 */ },
        /* data       */ NULL,
        /* type       */ USCXML_STATE_ATOMIC,
    },
    {   /* state number 2 */
        /* name       */ "s1",
        /* parent     */ 0,
        /* onentry    */ NULL,
        /* onexit     */ NULL,
        /* invoke     */ NULL,
        /* children   */ { 0x00 /* 00000 */ },
        /* completion */ { 0x00 /* 00000 */ }, 	
        /* ancestors  */ { 0x01 /* 10000 */ },
        /* data       */ NULL,
        /* type       */ USCXML_STATE_ATOMIC,
    },
    {   /* state number 3 */
        /* name       */ "pass",
        /* parent     */ 0,
        /* onentry    */ _uscxml_32F2390B__pass_on_entry,
        /* onexit     */ NULL,
        /* invoke     */ NULL,
        /* children   */ { 0x00 /* 00000 */ },
        /* completion */ { 0x00 /* 00000 */ }, 	
        /* ancestors  */ { 0x01 /* 10000 */ },
        /* data       */ NULL,
        /* type       */ USCXML_STATE_FINAL,
    },
    {   /* state number 4 */
        /* name       */ "fail",
        /* parent     */ 0,
        /* onentry    */ _uscxml_32F2390B__fail_on_entry,
        /* onexit     */ NULL,
        /* invoke     */ NULL,
        /* children   */ { 0x00 /* 00000 */ },
        /* completion */ { 0x00 /* 00000 */ }, 	
        /* ancestors  */ { 0x01 /* 10000 */ },
        /* data       */ NULL,
        /* type       */ USCXML_STATE_FINAL,
    }
};

#endif

#ifndef USCXML_NO_ELEM_INFO

static const uscxml_transition _uscxml_32F2390B__transitions[4] = {
    {   /* transition number 0 with priority 0
           target: s1
         */
        /* source     */ 1,
        /* target     */ { 0x04 /* 00100 */ },
        /* event      */ "foo",
        /* condition  */ NULL,
        /* is_enabled */ NULL,
        /* ontrans    */ NULL,
        /* type       */ 0,
        /* conflicts  */ { 0x0f /* 1111 */ }, 
        /* exit set   */ { 0x1e /* 01111 */ }
    },
    {   /* transition number 1 with priority 1
           target: fail
         */
        /* source     */ 1,
        /* target     */ { 0x10 /* 00001 */ },
        /* event      */ "*",
        /* condition  */ NULL,
        /* is_enabled */ NULL,
        /* ontrans    */ NULL,
        /* type       */ 0,
        /* conflicts  */ { 0x0f /* 1111 */ }, 
        /* exit set   */ { 0x1e /* 01111 */ }
    },
    {   /* transition number 2 with priority 2
           target: pass
         */
        /* source     */ 2,
        /* target     */ { 0x08 /* 00010 */ },
        /* event      */ "bar",
        /* condition  */ NULL,
        /* is_enabled */ NULL,
        /* ontrans    */ NULL,
        /* type       */ 0,
        /* conflicts  */ { 0x0f /* 1111 */ }, 
        /* exit set   */ { 0x1e /* 01111 */ }
    },
    {   /* transition number 3 with priority 3
           target: fail
         */
        /* source     */ 2,
        /* target     */ { 0x10 /* 00001 */ },
        /* event      */ "*",
        /* condition  */ NULL,
        /* is_enabled */ NULL,
        /* ontrans    */ NULL,
        /* type       */ 0,
        /* conflicts  */ { 0x0f /* 1111 */ }, 
        /* exit set   */ { 0x1e /* 01111 */ }
    }
};

#endif

#ifndef USCXML_NO_ELEM_INFO

#ifndef USCXML_MACHINE
#  define USCXML_MACHINE _uscxml_32F2390B__machine
#endif
#define USCXML_MACHINE_0 _uscxml_32F2390B__machine
#define USCXML_MACHINE_TEST144_SCXML _uscxml_32F2390B__machine

const uscxml_machine _uscxml_32F2390B__machine = {
        /* flags          */ 0,
        /* nr_states      */ 5,
        /* nr_transitions */ 4,
        /* name           */ "test144.scxml",
        /* datamodel      */ "promela",
        /* uuid           */ "32F2390BA5077C6C2095BF49A984CB72",
        /* states         */ &_uscxml_32F2390B__states[0], 
        /* transitions    */ &_uscxml_32F2390B__transitions[0], 
        /* parent         */ NULL,
        /* donedata       */ &_uscxml_32F2390B__elem_donedatas[0], 
        /* script         */ NULL
};

#endif

#ifdef USCXML_VERBOSE
/**
 * Print name of states contained in a (debugging).
 */
static void printStateNames(const uscxml_ctx* ctx, const unsigned char* a, size_t length) {
    size_t i;
    const char* seperator = "";
    for (i = 0; i < length; i++) {
        if (BIT_HAS(i, a)) {
            printf("%s%s", seperator, (USCXML_GET_STATE(i).name != NULL ? USCXML_GET_STATE(i).name : "UNK"));
            seperator = ", ";
        }
    }
    printf("\n");
}

/**
 * Print bits set in a in a binary representation (debugging).
 */
static void printBitsetIndices(const unsigned char* a, size_t length) {
    size_t i;
    const char* seperator = "";
    for (i = 0; i < length; i++) {
        if (BIT_HAS(i, a)) {
            printf("%s%zu", seperator, i);
            seperator = ", ";
        }
    }
    printf("\n");
}
#endif

#ifndef USCXML_NO_BIT_OPERATIONS
/**
 * Return true if there is a common bit in a and b.
 */
static int bit_has_and(const unsigned char* a, const unsigned char* b, size_t i) {
    while(i--) {
        if (a[i] & b[i])
            return 1;
    }
    return 0;
}

/**
 * Set all bits to 0, this corresponds to memset(a, 0, i), 
 * but does not require string.h or cstring.
 */
static void bit_clear_all(unsigned char* a, size_t i) {
    while(i--) {
        a[i] = 0;
    }
}

/**
 * Return true if there is any bit set in a.
 */
static int bit_has_any(unsigned const char* a, size_t i) {
    while(i--) {
        if (a[i] > 0)
            return 1;
    }
    return 0;
}

/**
 * Set all bits from given mask in dest, this is |= for bit arrays.
 */
static void bit_or(unsigned char* dest, const unsigned char* mask, size_t i) {
    while(i--) {
        dest[i] |= mask[i];
    }
}

/**
 * Copy all bits from source to dest, this corresponds to memcpy(a, b, i), 
 * but does not require string.h or cstring.
 */
static void bit_copy(unsigned char* dest, const unsigned char* source, size_t i) {
    while(i--) {
        dest[i] = source[i];
    }
}

/**
 * Unset bits from mask in dest.
 */
static void bit_and_not(unsigned char* dest, const unsigned char* mask, size_t i) {
    while(i--) {
        dest[i] &= ~mask[i];
    }
}

/**
 * Set bits from mask in dest.
 */
static void bit_and(unsigned char* dest, const unsigned char* mask, size_t i) {
    while(i--) {
        dest[i] &= mask[i];
    };
}

#define USCXML_NO_BIT_OPERATIONS
#endif

#ifndef USCXML_NO_STEP_FUNCTION
int uscxml_step(uscxml_ctx* ctx) {

    USCXML_NR_STATES_TYPE i, j, k;
    USCXML_NR_STATES_TYPE nr_states_bytes = ((USCXML_NUMBER_STATES + 7) & ~7) >> 3;
    USCXML_NR_TRANS_TYPE  nr_trans_bytes  = ((USCXML_NUMBER_TRANS + 7) & ~7) >> 3;
    int err = USCXML_ERR_OK;
    unsigned char conflicts  [USCXML_MAX_NR_TRANS_BYTES];
    unsigned char trans_set  [USCXML_MAX_NR_TRANS_BYTES];
    unsigned char target_set [USCXML_MAX_NR_STATES_BYTES];
    unsigned char exit_set   [USCXML_MAX_NR_STATES_BYTES];
    unsigned char entry_set  [USCXML_MAX_NR_STATES_BYTES];
    unsigned char tmp_states [USCXML_MAX_NR_STATES_BYTES];

#ifdef USCXML_VERBOSE
    printf("Config: ");
    printStateNames(ctx, ctx->config, USCXML_NUMBER_STATES);
#endif

    if (ctx->flags & USCXML_CTX_FINISHED)
        return USCXML_ERR_DONE;

    if (ctx->flags & USCXML_CTX_TOP_LEVEL_FINAL) {
        /* exit all remaining states */
        i = USCXML_NUMBER_STATES;
        while(i-- > 0) {
            if (BIT_HAS(i, ctx->config)) {
                /* call all on exit handlers */
                if (USCXML_GET_STATE(i).on_exit != NULL) {
                    if unlikely((err = USCXML_GET_STATE(i).on_exit(ctx, &USCXML_GET_STATE(i), ctx->event)) != USCXML_ERR_OK)
                        return err;
                }
            }
            if (BIT_HAS(i, ctx->invocations)) {
                if (USCXML_GET_STATE(i).invoke != NULL)
                    USCXML_GET_STATE(i).invoke(ctx, &USCXML_GET_STATE(i), NULL, 1);
                BIT_CLEAR(i, ctx->invocations);
            }
        }
        ctx->flags |= USCXML_CTX_FINISHED;
        return USCXML_ERR_DONE;
    }

    bit_clear_all(target_set, nr_states_bytes);
    bit_clear_all(trans_set, nr_trans_bytes);
    if unlikely(ctx->flags == USCXML_CTX_PRISTINE) {
        if (ctx->machine->script != NULL)
            ctx->machine->script(ctx, &ctx->machine->states[0], NULL);
        bit_or(target_set, ctx->machine->states[0].completion, nr_states_bytes);
        ctx->flags |= USCXML_CTX_SPONTANEOUS | USCXML_CTX_INITIALIZED;
        goto ESTABLISH_ENTRY_SET;
    }

DEQUEUE_EVENT:
    if (ctx->flags & USCXML_CTX_SPONTANEOUS) {
        ctx->event = NULL;
        goto SELECT_TRANSITIONS;
    }
    if (ctx->dequeue_internal != NULL && (ctx->event = ctx->dequeue_internal(ctx)) != NULL) {
        goto SELECT_TRANSITIONS;
    }

    /* manage invocations */
    for (i = 0; i < USCXML_NUMBER_STATES; i++) {
        /* uninvoke */
        if (!BIT_HAS(i, ctx->config) && BIT_HAS(i, ctx->invocations)) {
            if (USCXML_GET_STATE(i).invoke != NULL)
                USCXML_GET_STATE(i).invoke(ctx, &USCXML_GET_STATE(i), NULL, 1);
            BIT_CLEAR(i, ctx->invocations)
        }
        /* invoke */
        if (BIT_HAS(i, ctx->config) && !BIT_HAS(i, ctx->invocations)) {
            if (USCXML_GET_STATE(i).invoke != NULL)
                USCXML_GET_STATE(i).invoke(ctx, &USCXML_GET_STATE(i), NULL, 0);
            BIT_SET_AT(i, ctx->invocations)
        }
    }

    if (ctx->dequeue_external != NULL && (ctx->event = ctx->dequeue_external(ctx)) != NULL) {
        goto SELECT_TRANSITIONS;
    }

    if (ctx->dequeue_external == NULL) {
        return USCXML_ERR_DONE;
    }
    return USCXML_ERR_IDLE;

SELECT_TRANSITIONS:
    bit_clear_all(conflicts, nr_trans_bytes);
    bit_clear_all(exit_set, nr_states_bytes);
    for (i = 0; i < USCXML_NUMBER_TRANS; i++) {
        /* never select history or initial transitions automatically */
        if unlikely(USCXML_GET_TRANS(i).type & (USCXML_TRANS_HISTORY | USCXML_TRANS_INITIAL))
            continue;

        /* is the transition active? */
        if (BIT_HAS(USCXML_GET_TRANS(i).source, ctx->config)) {
            /* is it non-conflicting? */
            if (!BIT_HAS(i, conflicts)) {
                /* is it spontaneous with an event or vice versa? */
                if ((USCXML_GET_TRANS(i).event == NULL && ctx->event == NULL) || 
                    (USCXML_GET_TRANS(i).event != NULL && ctx->event != NULL)) {
                    /* is it enabled? */
                    if ((ctx->event == NULL || ctx->is_matched(ctx, &USCXML_GET_TRANS(i), ctx->event) > 0) &&
                        (USCXML_GET_TRANS(i).condition == NULL || 
                         USCXML_GET_TRANS(i).is_enabled(ctx, &USCXML_GET_TRANS(i)) > 0)) {
                        /* remember that we found a transition */
                        ctx->flags |= USCXML_CTX_TRANSITION_FOUND;

                        /* transitions that are pre-empted */
                        bit_or(conflicts, USCXML_GET_TRANS(i).conflicts, nr_trans_bytes);

                        /* states that are directly targeted (resolve as entry-set later) */
                        bit_or(target_set, USCXML_GET_TRANS(i).target, nr_states_bytes);

                        /* states that will be left */
                        bit_or(exit_set, USCXML_GET_TRANS(i).exit_set, nr_states_bytes);

                        BIT_SET_AT(i, trans_set);
                    }
                }
            }
        }
    }
    bit_and(exit_set, ctx->config, nr_states_bytes);

    if (ctx->flags & USCXML_CTX_TRANSITION_FOUND) {
        ctx->flags |= USCXML_CTX_SPONTANEOUS;
        ctx->flags &= ~USCXML_CTX_TRANSITION_FOUND;
    } else {
        ctx->flags &= ~USCXML_CTX_SPONTANEOUS;
        goto DEQUEUE_EVENT;
    }

#ifdef USCXML_VERBOSE
    printf("Targets: ");
    printStateNames(ctx, target_set, USCXML_NUMBER_STATES);
#endif

#ifdef USCXML_VERBOSE
    printf("Exiting: ");
    printStateNames(ctx, exit_set, USCXML_NUMBER_STATES);
#endif

#ifdef USCXML_VERBOSE
    printf("History: ");
    printStateNames(ctx, ctx->history, USCXML_NUMBER_STATES);
#endif

/* REMEMBER_HISTORY: */
    for (i = 0; i < USCXML_NUMBER_STATES; i++) {
        if unlikely(USCXML_STATE_MASK(USCXML_GET_STATE(i).type) == USCXML_STATE_HISTORY_SHALLOW ||
                    USCXML_STATE_MASK(USCXML_GET_STATE(i).type) == USCXML_STATE_HISTORY_DEEP) {
            /* a history state whose parent is about to be exited */
            if unlikely(BIT_HAS(USCXML_GET_STATE(i).parent, exit_set)) {
                bit_copy(tmp_states, USCXML_GET_STATE(i).completion, nr_states_bytes);

                /* set those states who were enabled */
                bit_and(tmp_states, ctx->config, nr_states_bytes);

                /* clear current history with completion mask */
                bit_and_not(ctx->history, USCXML_GET_STATE(i).completion, nr_states_bytes);

                /* set history */
                bit_or(ctx->history, tmp_states, nr_states_bytes);
            }
        }
    }

ESTABLISH_ENTRY_SET:
    /* calculate new entry set */
    bit_copy(entry_set, target_set, nr_states_bytes);

    /* iterate for ancestors */
    for (i = 0; i < USCXML_NUMBER_STATES; i++) {
        if (BIT_HAS(i, entry_set)) {
            bit_or(entry_set, USCXML_GET_STATE(i).ancestors, nr_states_bytes);
        }
    }

    /* iterate for descendants */
    for (i = 0; i < USCXML_NUMBER_STATES; i++) {
        if (BIT_HAS(i, entry_set)) {
            switch (USCXML_STATE_MASK(USCXML_GET_STATE(i).type)) {
                case USCXML_STATE_PARALLEL: {
                    bit_or(entry_set, USCXML_GET_STATE(i).completion, nr_states_bytes);
                    break;
                }
                case USCXML_STATE_HISTORY_SHALLOW:
                case USCXML_STATE_HISTORY_DEEP: {
                    if (!bit_has_and(USCXML_GET_STATE(i).completion, ctx->history, nr_states_bytes) &&
                        !BIT_HAS(USCXML_GET_STATE(i).parent, ctx->config)) {
                        /* nothing set for history, look for a default transition */
                        for (j = 0; j < USCXML_NUMBER_TRANS; j++) {
                            if unlikely(ctx->machine->transitions[j].source == i) {
                                bit_or(entry_set, ctx->machine->transitions[j].target, nr_states_bytes);
                                if(USCXML_STATE_MASK(USCXML_GET_STATE(i).type) == USCXML_STATE_HISTORY_DEEP &&
                                   !bit_has_and(ctx->machine->transitions[j].target, USCXML_GET_STATE(i).children, nr_states_bytes)) {
                                    for (k = i + 1; k < USCXML_NUMBER_STATES; k++) {
                                        if (BIT_HAS(k, ctx->machine->transitions[j].target)) {
                                            bit_or(entry_set, ctx->machine->states[k].ancestors, nr_states_bytes);
                                            break;
                                        }
                                    }
                                }
                                BIT_SET_AT(j, trans_set);
                                break;
                            }
                            /* Note: SCXML mandates every history to have a transition! */
                        }
                    } else {
                        bit_copy(tmp_states, USCXML_GET_STATE(i).completion, nr_states_bytes);
                        bit_and(tmp_states, ctx->history, nr_states_bytes);
                        bit_or(entry_set, tmp_states, nr_states_bytes);
                        if (USCXML_GET_STATE(i).type == (USCXML_STATE_HAS_HISTORY | USCXML_STATE_HISTORY_DEEP)) {
                            /* a deep history state with nested histories -> more completion */
                            for (j = i + 1; j < USCXML_NUMBER_STATES; j++) {
                                if (BIT_HAS(j, USCXML_GET_STATE(i).completion) &&
                                    BIT_HAS(j, entry_set) &&
                                    (ctx->machine->states[j].type & USCXML_STATE_HAS_HISTORY)) {
                                    for (k = j + 1; k < USCXML_NUMBER_STATES; k++) {
                                        /* add nested history to entry_set */
                                        if ((USCXML_STATE_MASK(ctx->machine->states[k].type) == USCXML_STATE_HISTORY_DEEP ||
                                             USCXML_STATE_MASK(ctx->machine->states[k].type) == USCXML_STATE_HISTORY_SHALLOW) &&
                                            BIT_HAS(k, ctx->machine->states[j].children)) {
                                            /* a nested history state */
                                            BIT_SET_AT(k, entry_set);
                                        }
                                    }
                                }
                            }
                        }
                    }
                    break;
                }
                case USCXML_STATE_INITIAL: {
                    for (j = 0; j < USCXML_NUMBER_TRANS; j++) {
                        if (ctx->machine->transitions[j].source == i) {
                            BIT_SET_AT(j, trans_set);
                            BIT_CLEAR(i, entry_set);
                            bit_or(entry_set, ctx->machine->transitions[j].target, nr_states_bytes);
                            for (k = i + 1; k < USCXML_NUMBER_STATES; k++) {
                                if (BIT_HAS(k, ctx->machine->transitions[j].target)) {
                                    bit_or(entry_set, ctx->machine->states[k].ancestors, nr_states_bytes);
                                }
                            }
                        }
                    }
                    break;
                }
                case USCXML_STATE_COMPOUND: { /* we need to check whether one child is already in entry_set */
                    if (!bit_has_and(entry_set, USCXML_GET_STATE(i).children, nr_states_bytes) &&
                        (!bit_has_and(ctx->config, USCXML_GET_STATE(i).children, nr_states_bytes) ||
                         bit_has_and(exit_set, USCXML_GET_STATE(i).children, nr_states_bytes)))
                    {
                        bit_or(entry_set, USCXML_GET_STATE(i).completion, nr_states_bytes);
                        if (!bit_has_and(USCXML_GET_STATE(i).completion, USCXML_GET_STATE(i).children, nr_states_bytes)) {
                            /* deep completion */
                            for (j = i + 1; j < USCXML_NUMBER_STATES; j++) {
                                if (BIT_HAS(j, USCXML_GET_STATE(i).completion)) {
                                    bit_or(entry_set, ctx->machine->states[j].ancestors, nr_states_bytes);
                                    break; /* completion of compound is single state */
                                }
                            }
                        }
                    }
                    break;
                }
            }
        }
    }

#ifdef USCXML_VERBOSE
    printf("Transitions: ");
    printBitsetIndices(trans_set, sizeof(char) * 8 * nr_trans_bytes);
#endif

/* EXIT_STATES: */
    i = USCXML_NUMBER_STATES;
    while(i-- > 0) {
        if (BIT_HAS(i, exit_set) && BIT_HAS(i, ctx->config)) {
            /* call all on exit handlers */
            if (USCXML_GET_STATE(i).on_exit != NULL) {
                if unlikely((err = USCXML_GET_STATE(i).on_exit(ctx, &USCXML_GET_STATE(i), ctx->event)) != USCXML_ERR_OK)
                    return err;
            }
            BIT_CLEAR(i, ctx->config);
        }
    }

/* TAKE_TRANSITIONS: */
    for (i = 0; i < USCXML_NUMBER_TRANS; i++) {
        if (BIT_HAS(i, trans_set) && (USCXML_GET_TRANS(i).type & (USCXML_TRANS_HISTORY | USCXML_TRANS_INITIAL)) == 0) {
            /* call executable content in transition */
            if (USCXML_GET_TRANS(i).on_transition != NULL) {
                if unlikely((err = USCXML_GET_TRANS(i).on_transition(ctx,
                                                                              &ctx->machine->states[USCXML_GET_TRANS(i).source],
                                                                              ctx->event)) != USCXML_ERR_OK)
                    return err;
            }
        }
    }

#ifdef USCXML_VERBOSE
    printf("Entering: ");
    printStateNames(ctx, entry_set, USCXML_NUMBER_STATES);
#endif

/* ENTER_STATES: */
    for (i = 0; i < USCXML_NUMBER_STATES; i++) {
        if (BIT_HAS(i, entry_set) && !BIT_HAS(i, ctx->config)) {
            /* these are no proper states */
            if unlikely(USCXML_STATE_MASK(USCXML_GET_STATE(i).type) == USCXML_STATE_HISTORY_DEEP ||
                        USCXML_STATE_MASK(USCXML_GET_STATE(i).type) == USCXML_STATE_HISTORY_SHALLOW ||
                        USCXML_STATE_MASK(USCXML_GET_STATE(i).type) == USCXML_STATE_INITIAL)
                continue;

            BIT_SET_AT(i, ctx->config);

            /* initialize data */
            if (!BIT_HAS(i, ctx->initialized_data)) {
                if unlikely(USCXML_GET_STATE(i).data != NULL && ctx->exec_content_init != NULL) {
                    ctx->exec_content_init(ctx, USCXML_GET_STATE(i).data);
                }
                BIT_SET_AT(i, ctx->initialized_data);
            }

            if (USCXML_GET_STATE(i).on_entry != NULL) {
                if unlikely((err = USCXML_GET_STATE(i).on_entry(ctx, &USCXML_GET_STATE(i), ctx->event)) != USCXML_ERR_OK)
                    return err;
            }

            /* take history and initial transitions */
            for (j = 0; j < USCXML_NUMBER_TRANS; j++) {
                if unlikely(BIT_HAS(j, trans_set) &&
                            (ctx->machine->transitions[j].type & (USCXML_TRANS_HISTORY | USCXML_TRANS_INITIAL)) &&
                            ctx->machine->states[ctx->machine->transitions[j].source].parent == i) {
                    /* call executable content in transition */
                    if (ctx->machine->transitions[j].on_transition != NULL) {
                        if unlikely((err = ctx->machine->transitions[j].on_transition(ctx,
                                                                                      &USCXML_GET_STATE(i),
                                                                                      ctx->event)) != USCXML_ERR_OK)
                            return err;
                    }
                }
            }

            /* handle final states */
            if unlikely(USCXML_STATE_MASK(USCXML_GET_STATE(i).type) == USCXML_STATE_FINAL) {
                if unlikely(USCXML_GET_STATE(i).ancestors[0] == 0x01) {
                    ctx->flags |= USCXML_CTX_TOP_LEVEL_FINAL;
                } else {
                    /* raise done event */
                    const uscxml_elem_donedata* donedata = &ctx->machine->donedata[0];
                    while(USCXML_ELEM_DONEDATA_IS_SET(donedata)) {
                        if unlikely(donedata->source == i)
                            break;
                        donedata++;
                    }
                    ctx->raise_done_event(ctx, &ctx->machine->states[USCXML_GET_STATE(i).parent], (USCXML_ELEM_DONEDATA_IS_SET(donedata) ? donedata : NULL));
                }

                /**
                 * are we the last final state to leave a parallel state?:
                 * 1. Gather all parallel states in our ancestor chain
                 * 2. Find all states for which these parallels are ancestors
                 * 3. Iterate all active final states and remove their ancestors
                 * 4. If a state remains, not all children of a parallel are final
                 */
                for (j = 0; j < USCXML_NUMBER_STATES; j++) {
                    if unlikely(USCXML_STATE_MASK(ctx->machine->states[j].type) == USCXML_STATE_PARALLEL &&
                                BIT_HAS(j, USCXML_GET_STATE(i).ancestors)) {
                        bit_clear_all(tmp_states, nr_states_bytes);
                        for (k = 0; k < USCXML_NUMBER_STATES; k++) {
                            if unlikely(BIT_HAS(j, ctx->machine->states[k].ancestors) && BIT_HAS(k, ctx->config)) {
                                if (USCXML_STATE_MASK(ctx->machine->states[k].type) == USCXML_STATE_FINAL) {
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

    return USCXML_ERR_OK;
}

#define USCXML_NO_STEP_FUNCTION
#endif

