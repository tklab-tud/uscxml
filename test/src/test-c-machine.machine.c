#include <stdint.h> // explicit types
#include <stddef.h> // NULL

#define IS_SET(idx, bitset)   ((bitset[idx >> 3] &  (1 << (idx & 7))) != 0)
#define SET_BIT(idx, bitset)    bitset[idx >> 3] |= (1 << (idx & 7));
#define CLEARBIT(idx, bitset)   bitset[idx >> 3] &= (1 << (idx & 7)) ^ 0xFF;

// error return codes
#define SCXML_ERR_OK                0
#define SCXML_ERR_IDLE              1
#define SCXML_ERR_DONE              2
#define SCXML_ERR_MISSING_CALLBACK  3
#define SCXML_ERR_FOREACH_DONE      4
#define SCXML_ERR_EXEC_CONTENT      5
#define SCXML_ERR_INVALID_TARGET    6
#define SCXML_ERR_INVALID_TYPE      7

#define SCXML_NUMBER_STATES 5
#define SCXML_NUMBER_TRANSITIONS 4

#define SCXML_TRANS_SPONTANEOUS      0x01
#define SCXML_TRANS_TARGETLESS       0x02
#define SCXML_TRANS_INTERNAL         0x04

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
#define ELEM_PARAM_IS_SET(param) (param->name != NULL)


typedef struct scxml_transition scxml_transition;
typedef struct scxml_state scxml_state;
typedef struct scxml_ctx scxml_ctx;
typedef struct scxml_invoke scxml_invoke;

typedef struct scxml_elem_send scxml_elem_send;
typedef struct scxml_elem_param scxml_elem_param;
typedef struct scxml_elem_data scxml_elem_data;
typedef struct scxml_elem_foreach scxml_elem_foreach;

typedef void* (*dequeue_internal_cb_t)(const scxml_ctx* ctx);
typedef void* (*dequeue_external_cb_t)(const scxml_ctx* ctx);
typedef int (*is_enabled_cb_t)(const scxml_ctx* ctx, const scxml_transition* transition, const void* event);
typedef int (*is_true_cb_t)(const scxml_ctx* ctx, const char* expr);
typedef int (*exec_content_t)(const scxml_ctx* ctx, const scxml_state* state, const void* event);
typedef int (*raise_done_event_t)(const scxml_ctx* ctx, const scxml_state* state);
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
    exec_content_t on_entry; // on entry handlers
    exec_content_t on_exit; // on exit handlers
    invoke_t invoke; // invocations
    char children[1]; // all children
    char completion[1]; // default completion
    char ancestors[1]; // all ancestors
    const scxml_elem_data* data;
    uint8_t type; // atomic, parallel, compound, final, history
};

struct scxml_transition {
    uint16_t source;
    char target[1];
    const char* event;
    const char* condition;
    exec_content_t on_transition;
    uint8_t type;
    char conflicts[1];
    char exit_set[1];
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
    const scxml_elem_param* params;
    void* user_data;
};

struct scxml_ctx {
    uint8_t flags;

    char config[1];
    char history[1];
    char pending_invokes[1];
    char initialized_data[1];

    void* user_data;

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

scxml_elem_data scxml_elem_datas[4] = {
    { "Var1", NULL, NULL, NULL },
    { NULL, NULL, NULL, NULL },
    { "Var2", NULL, "1", NULL },
    { NULL, NULL, NULL, NULL }
};

int s1_on_entry_0(const scxml_ctx* ctx, const scxml_state* state, const void* event) {
    int err = SCXML_ERR_OK;
    if (ctx->exec_content_assign != NULL) {
        if ((ctx->exec_content_assign(ctx, "Var1", "Var2")) != SCXML_ERR_OK) return err;
    } else {
        return SCXML_ERR_MISSING_CALLBACK;
    }
    return SCXML_ERR_OK;
}

int s1_on_entry(const scxml_ctx* ctx, const scxml_state* state, const void* event) {
    s1_on_entry_0(ctx, state, event);
    return SCXML_ERR_OK;
}

int pass_on_entry_0(const scxml_ctx* ctx, const scxml_state* state, const void* event) {
    int err = SCXML_ERR_OK;
    if (ctx->exec_content_log != NULL) {
        if ((ctx->exec_content_log(ctx, "Outcome", "'pass'")) != SCXML_ERR_OK) return err;
    } else {
        return SCXML_ERR_MISSING_CALLBACK;
    }
    return SCXML_ERR_OK;
}

int pass_on_entry(const scxml_ctx* ctx, const scxml_state* state, const void* event) {
    pass_on_entry_0(ctx, state, event);
    return SCXML_ERR_OK;
}

int fail_on_entry_0(const scxml_ctx* ctx, const scxml_state* state, const void* event) {
    int err = SCXML_ERR_OK;
    if (ctx->exec_content_log != NULL) {
        if ((ctx->exec_content_log(ctx, "Outcome", "'fail'")) != SCXML_ERR_OK) return err;
    } else {
        return SCXML_ERR_MISSING_CALLBACK;
    }
    return SCXML_ERR_OK;
}

int fail_on_entry(const scxml_ctx* ctx, const scxml_state* state, const void* event) {
    fail_on_entry_0(ctx, state, event);
    return SCXML_ERR_OK;
}

scxml_state scxml_states[5] = {
    { NULL, NULL, NULL, NULL, { 0x1e /* 01111, 1 2 3 4 */ }, { 0x02 /* 01000, 1 */ }, { 0x00 /* 00000, */ }, (const scxml_elem_data*)&scxml_elem_datas[0], SCXML_STATE_COMPOUND },
    { "s0", NULL, NULL, NULL, { 0x00 /* 00000, */ }, { 0x00 /* 00000, */ }, { 0x01 /* 10000, 0 */ }, NULL, SCXML_STATE_ATOMIC },
    { "s1", s1_on_entry, NULL, NULL, { 0x00 /* 00000, */ }, { 0x00 /* 00000, */ }, { 0x01 /* 10000, 0 */ }, (const scxml_elem_data*)&scxml_elem_datas[1], SCXML_STATE_ATOMIC },
    { "pass", pass_on_entry, NULL, NULL, { 0x00 /* 00000, */ }, { 0x00 /* 00000, */ }, { 0x01 /* 10000, 0 */ }, NULL, SCXML_STATE_FINAL },
    { "fail", fail_on_entry, NULL, NULL, { 0x00 /* 00000, */ }, { 0x00 /* 00000, */ }, { 0x01 /* 10000, 0 */ }, NULL, SCXML_STATE_FINAL }
};

scxml_transition scxml_transitions[4] = {
    { 1, { 0x04 /* 00100 */ }, NULL, "typeof Var2 === 'undefined' ", NULL, SCXML_TRANS_SPONTANEOUS, { 0x0f /* 1111 */ }, { 0x1e /* 01111 */ } },
    { 1, { 0x10 /* 00001 */ }, NULL, NULL, NULL, SCXML_TRANS_SPONTANEOUS, { 0x0f /* 1111 */ }, { 0x1e /* 01111 */ } },
    { 2, { 0x08 /* 00010 */ }, NULL, "Var1===Var2", NULL, SCXML_TRANS_SPONTANEOUS, { 0x0f /* 1111 */ }, { 0x1e /* 01111 */ } },
    { 2, { 0x10 /* 00001 */ }, NULL, NULL, NULL, SCXML_TRANS_SPONTANEOUS, { 0x0f /* 1111 */ }, { 0x1e /* 01111 */ } }
};

#ifdef SCXML_VERBOSE
void printStateNames(const char* a) {
    const char* seperator = "";
    for (int i = 0; i < SCXML_NUMBER_STATES; i++) {
        if (IS_SET(i, a)) {
            printf("%s%s", seperator, (scxml_states[i].name != NULL ? scxml_states[i].name : "UNK"));
            seperator = ", ";
        }
    }
    printf("\n");
}

void printBitsetIndices(const char* a, size_t length) {
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

void bit_or(char* dest, const char* mask, size_t length) {
    for (int i = 0; i < length; ++i) {
        dest[i] |= mask[i];
    }
}

void bit_copy(char* dest, const char* source, size_t length) {
    for (int i = 0; i < length; ++i) {
        dest[i] = source[i];
    }
}

int bit_has_and(const char* a, const char* b, size_t length) {
    for (int i = 0; i < length; ++i) {
        if (a[i] & b[i])
            return true;
    }
    return false;
}

void bit_and_not(char* dest, const char* mask, size_t length) {
    for (int i = 0; i < length; ++i) {
        dest[i] &= ~mask[i];
    }
}

int bit_any_set(const char* a, size_t length) {
    for (int i = 0; i < length; ++i) {
        if (a[i] > 0)
            return true;
    }
    return false;
}

int scxml_step(scxml_ctx* ctx) {

#ifdef SCXML_VERBOSE
    printStateNames(ctx->config);
#endif

MACRO_STEP:
    ctx->flags &= ~SCXML_CTX_TRANSITION_FOUND;

    if (ctx->flags & SCXML_CTX_TOP_LEVEL_FINAL) 
        return SCXML_ERR_DONE; 

    int err = SCXML_ERR_OK;
    char conflicts[1] = {0};
    char target_set[1] = {0};
    char exit_set[1] = {0};
    char trans_set[1] = {0};
    char entry_set[1] = {0};

    void* event;
    if (ctx->flags == SCXML_CTX_PRISTINE) {
        bit_or(target_set, scxml_states[0].completion, 1);
        ctx->flags |= SCXML_CTX_SPONTANEOUS | SCXML_CTX_INITIALIZED;
        goto COMPLETE_CONFIG;
    }

    if (ctx->flags & SCXML_CTX_SPONTANEOUS) {
        event = NULL;
        goto SELECT_TRANSITIONS;
    }
    if ((event = ctx->dequeue_internal(ctx)) != NULL) {
        goto SELECT_TRANSITIONS;
    }
    if ((event = ctx->dequeue_external(ctx)) != NULL) {
        goto SELECT_TRANSITIONS;
    }

SELECT_TRANSITIONS:
    for (int i = 0; i < SCXML_NUMBER_TRANSITIONS; i++) {
        // is the transition active?
        if (IS_SET(scxml_transitions[i].source, ctx->config)) {
            // is it non-conflicting?
            if (!IS_SET(i, conflicts)) {
                // is it enabled?
                if (ctx->is_enabled(ctx, &scxml_transitions[i], event) > 0) {
                    // remember that we found a transition
                    ctx->flags |= SCXML_CTX_TRANSITION_FOUND;

                    // transitions that are pre-empted
                    bit_or(conflicts, scxml_transitions[i].conflicts, 1);

                    // states that are directly targeted (resolve as entry-set later)
                    bit_or(target_set, scxml_transitions[i].target, 1);

                    // states that will be left
                    bit_or(exit_set, scxml_transitions[i].exit_set, 1);

                    SET_BIT(i, trans_set);
                }
            }
        }
    }

    if (ctx->flags & SCXML_CTX_TRANSITION_FOUND) {
        ctx->flags |= SCXML_CTX_SPONTANEOUS;
    } else {
        ctx->flags &= ~SCXML_CTX_SPONTANEOUS;
        goto MACRO_STEP;
    }

REMEMBER_HISTORY:
    // are my ancestors in the exit set?
    for (int i = 0; i < SCXML_NUMBER_STATES; i++) {
        if (IS_SET(i, ctx->config) && bit_has_and(exit_set, scxml_states[i].ancestors, 1)) {
            SET_BIT(i, ctx->history);
        }
    }

#ifdef SCXML_VERBOSE
    printf("Exiting: ");
    printStateNames(exit_set);
#endif

EXIT_STATES:
    for (int i = SCXML_NUMBER_STATES - 1; i >= 0; i--) {
        if (IS_SET(i, exit_set) && IS_SET(i, ctx->config)) {
            // call all on exit handlers
            if (scxml_states[i].on_exit != NULL) {
                if((err = scxml_states[i].on_exit(ctx, &scxml_states[i], event)) != SCXML_ERR_OK)
                    return err;
            }
            CLEARBIT(i, ctx->config);
        }
    }

COMPLETE_CONFIG:
    // calculate new entry set
    bit_copy(entry_set, target_set, 1);

    // iterate for ancestors
    for (int i = 0; i < SCXML_NUMBER_STATES; i++) {
        if (IS_SET(i, entry_set)) {
            bit_or(entry_set, scxml_states[i].ancestors, 1);
        }
    }

ADD_DESCENDANTS:
    // iterate for descendants
    for (int i = 0; i < SCXML_NUMBER_STATES; i++) {
        if (IS_SET(i, entry_set)) {
            switch (scxml_states[i].type) {
                case SCXML_STATE_PARALLEL: {
                    bit_or(entry_set, scxml_states[i].completion, 1);
                    break;
                }
                case SCXML_STATE_INITIAL: {
                    for (int j = 0; j < SCXML_NUMBER_TRANSITIONS; j++) {
                        if (scxml_transitions[j].source == i) {
                            SET_BIT(j, trans_set);
                            CLEARBIT(i, entry_set);
                            bit_or(entry_set, scxml_transitions[j].target, 1);
                            // one target may have been above, reestablish completion
                            goto ADD_DESCENDANTS;
                        }
                    }
                    break;
                }
                case SCXML_STATE_COMPOUND: { // we need to check whether one child is already in entry_set
                    if (!bit_has_and(entry_set, scxml_states[i].children, 1)) {
                        bit_or(entry_set, scxml_states[i].completion, 1);
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

TAKE_TRANSITIONS:
    for (int i = 0; i < SCXML_NUMBER_TRANSITIONS; i++) {
        if (IS_SET(i, trans_set)) {
            // call executable content in transition
            if (scxml_transitions[i].on_transition != NULL) {
                if((err = scxml_transitions[i].on_transition(ctx,
                                                             &scxml_states[scxml_transitions[i].source],
                                                             event)) != SCXML_ERR_OK)
                    return err;
            }
        }
    }

#ifdef SCXML_VERBOSE
    printf("Entering: ");
    printStateNames(entry_set);
#endif

ENTER_STATES:
    for (int i = 0; i < SCXML_NUMBER_STATES; i++) {
        if (IS_SET(i, entry_set) && !IS_SET(i, ctx->config)) {
            SET_BIT(i, ctx->config);
            if (scxml_states[i].on_entry != NULL) {
                if((err = scxml_states[i].on_entry(ctx, &scxml_states[i], event)) != SCXML_ERR_OK)
                    return err;
            }

            // initialize data
            if(!IS_SET(i, ctx->initialized_data)) {
                if (scxml_states[i].data != NULL && ctx->exec_content_init != NULL) {
                    ctx->exec_content_init(ctx, scxml_states[i].data);
                }
                SET_BIT(i, ctx->initialized_data);
            }

            // handle final states
            if (scxml_states[i].type == SCXML_STATE_FINAL) {
                if (scxml_states[i].ancestors[0] == 0x01) {
                    ctx->flags |= SCXML_CTX_TOP_LEVEL_FINAL;
                } else {
                    // raise done event
                    size_t parent = 0;
                    for (int j = 0; j < SCXML_NUMBER_STATES; j++) {
                        // we could trade runtime for memory here by saving the parent index
                        if (!IS_SET(j, scxml_states[i].ancestors)) {
                            if (parent != 0) {
                                break;
                            }
                            continue;
                        } else {
                            parent = j;
                        }
                    }
                    ctx->raise_done_event(ctx, &scxml_states[parent]);
                }

                /**
                 * are we the last final state to leave a parallel state?:
                 * 1. Gather all parallel states in our ancestor chain
                 * 2. Find all states for which these parallels are ancestors
                 * 3. Iterate all active final states and remove their ancestors
                 * 4. If a state remains, not all children of a parallel are final
                 */
                for (int j = 0; j < SCXML_NUMBER_STATES; j++) {
                    if (scxml_states[j].type == SCXML_STATE_PARALLEL) {
                        char parallel_children[2] = {0, 0};
                        size_t parallel = j;
                        for (int k = 0; k < SCXML_NUMBER_STATES; k++) {
                            if (IS_SET(parallel, scxml_states[k].ancestors) && IS_SET(k, ctx->config)) {
                                if (scxml_states[k].type == SCXML_STATE_FINAL) {
                                    bit_and_not(parallel_children, scxml_states[k].ancestors, 2);
                                } else {
                                    SET_BIT(k, parallel_children);
                                }
                            }
                        }
                        if (!bit_any_set(parallel_children, 2)) {
                            ctx->raise_done_event(ctx, &scxml_states[parallel]);
                        }
                    }
                }

            }

        }
    }

    return SCXML_ERR_OK;
}

