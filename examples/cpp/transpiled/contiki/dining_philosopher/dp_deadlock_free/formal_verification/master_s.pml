/** generated from 
  file:///C:/Puneet/education/TU_Darmstadt/Theses/Dining_philospher/june20/dp_solution/uscxml_browser/scxml/master_s.scxml
  Verify as:
  $ spin -a this.pml
  $ gcc -DMEMLIM=1024 -DVECTORSZ=8192 -O2 -DXUSAFE pan.c -o pan
  $ ./pan -a -m10000 -n -N w3c
 */

/* machine state flags */
#define USCXML_CTX_PRISTINE          0 /* can be out-factored */
#define USCXML_CTX_SPONTANEOUS       1
#define USCXML_CTX_TOP_LEVEL_FINAL   2
#define USCXML_CTX_TRANSITION_FOUND  3
#define USCXML_CTX_FINISHED          4
#define USCXML_CTX_DEQUEUE_EXTERNAL  5

#define USCXML_TRANS_SPONTANEOUS     0
#define USCXML_TRANS_TARGETLESS      1
#define USCXML_TRANS_INTERNAL        2
#define USCXML_TRANS_HISTORY         3
#define USCXML_TRANS_INITIAL         4

#define USCXML_STATE_ATOMIC          0
#define USCXML_STATE_PARALLEL        1
#define USCXML_STATE_COMPOUND        2
#define USCXML_STATE_FINAL           3
#define USCXML_STATE_HISTORY_DEEP    4
#define USCXML_STATE_HISTORY_SHALLOW 5
#define USCXML_STATE_INITIAL         6
#define USCXML_STATE_HAS_HISTORY     7

#define USCXML_ERR_OK                0
#define USCXML_ERR_DONE              1

#define USCXML_EVENT_SPONTANEOUS     0

#define TRACE_EXECUTION              1


/* states, events and string literals */
#define ROOT_S0 1 /* index for state s0 */
#define ROOT_S01 2 /* index for state s01 */
#define ROOT_FAIL 3 /* index for state fail */
#define ROOT 1 /* index for invoker ROOT */
#define INV_F5426 2 /* index for invoker INV_f5426 */
#define INV_8CB85 3 /* index for invoker INV_8cb85 */
#define INV_5C805 4 /* index for invoker INV_5c805 */
#define INV_F88AA 5 /* index for invoker INV_f88aa */
#define INV_41D63 6 /* index for invoker INV_41d63 */
#define ROOT__NAME 8 /* ROOT__name */
#define ROOT__SESSIONID 7 /* ROOT__sessionid */
#define U2827EABC__NAME 29 /* U2827EABC__name */
#define U2827EABC__SESSIONID 28 /* U2827EABC__sessionid */
#define U4C987312__NAME 23 /* U4C987312__name */
#define U4C987312__SESSIONID 22 /* U4C987312__sessionid */
#define U984EF850__NAME 16 /* U984EF850__name */
#define U984EF850__SESSIONID 15 /* U984EF850__sessionid */
#define UF38FC1F9__NAME 26 /* UF38FC1F9__name */
#define UF38FC1F9__SESSIONID 25 /* UF38FC1F9__sessionid */
#define UF9BA6A05__NAME 20 /* UF9BA6A05__name */
#define UF9BA6A05__SESSIONID 19 /* UF9BA6A05__sessionid */
#define DONE_INVOKE 5 /* done.invoke */
#define DONE_INVOKE_INV_41D63 30 /* done.invoke.INV_41d63 */
#define DONE_INVOKE_INV_5C805 24 /* done.invoke.INV_5c805 */
#define DONE_INVOKE_INV_8CB85 21 /* done.invoke.INV_8cb85 */
#define DONE_INVOKE_INV_F5426 18 /* done.invoke.INV_f5426 */
#define DONE_INVOKE_INV_F88AA 27 /* done.invoke.INV_f88aa */
#define DONE_STATE_PHILOSOPHER_ROUTINE 14 /* done.state.Philosopher_routine */
#define DONE_STATE_S0 6 /* done.state.s0 */
#define EATING_OVER 11 /* eating_over */
#define FAIL 9 /* fail */
#define NEED_FORKS 1 /* need_forks */
#define RESEND_NEED_FORKS 13 /* resend_need_forks */
#define RESOURCE_DENIED 3 /* resource_denied */
#define RESOURCE_DENIED_TIMER 17 /* resource_denied_timer */
#define RETURN_FORKS 4 /* return_forks */
#define TAKE_FORKS 2 /* take_forks */
#define THINKING_OVER 10 /* thinking_over */
#define TIMEOUT 12 /* timeout */

/** is there a common bit in t1 and t2 */
#define ROOT_TRANS_HAS_AND(a, b) \
(false \
 || a[0] & b[0] \
 || a[1] & b[1] \
 || a[2] & b[2] \
)

#define ROOT_STATES_HAS_AND(a, b) \
(false \
 || a[0] & b[0] \
 || a[1] & b[1] \
 || a[2] & b[2] \
 || a[3] & b[3] \
)


/** is there bit set in a */
#define ROOT_TRANS_HAS_ANY(a) \
(false \
 || a[0] \
 || a[1] \
 || a[2] \
)

#define ROOT_STATES_HAS_ANY(a) \
(false \
 || a[0] \
 || a[1] \
 || a[2] \
 || a[3] \
)


/** or'ing bits in a with mask */
#define ROOT_TRANS_OR(a, mask) \
a[0] = a[0] | mask[0]; \
a[1] = a[1] | mask[1]; \
a[2] = a[2] | mask[2]; \

#define ROOT_STATES_OR(a, mask) \
a[0] = a[0] | mask[0]; \
a[1] = a[1] | mask[1]; \
a[2] = a[2] | mask[2]; \
a[3] = a[3] | mask[3]; \


/** clearing all bits of a */
#define ROOT_TRANS_CLEAR(a) \
a[0] = false; \
a[1] = false; \
a[2] = false; \

#define ROOT_STATES_CLEAR(a) \
a[0] = false; \
a[1] = false; \
a[2] = false; \
a[3] = false; \


/** copy bits from a to b */
#define ROOT_TRANS_COPY(a, b) \
a[0] = b[0]; \
a[1] = b[1]; \
a[2] = b[2]; \

#define ROOT_STATES_COPY(a, b) \
a[0] = b[0]; \
a[1] = b[1]; \
a[2] = b[2]; \
a[3] = b[3]; \


/** and'ing bits in a with mask */
#define ROOT_TRANS_AND(a, mask) \
a[0] = a[0] & mask[0]; \
a[1] = a[1] & mask[1]; \
a[2] = a[2] & mask[2]; \

#define ROOT_STATES_AND(a, mask) \
a[0] = a[0] & mask[0]; \
a[1] = a[1] & mask[1]; \
a[2] = a[2] & mask[2]; \
a[3] = a[3] & mask[3]; \


/** not and'ing bits in a with mask */
#define ROOT_TRANS_AND_NOT(a, mask) \
a[0] = a[0] & !mask[0]; \
a[1] = a[1] & !mask[1]; \
a[2] = a[2] & !mask[2]; \

#define ROOT_STATES_AND_NOT(a, mask) \
a[0] = a[0] & !mask[0]; \
a[1] = a[1] & !mask[1]; \
a[2] = a[2] & !mask[2]; \
a[3] = a[3] & !mask[3]; \


/* custom type definitions for ROOT_ */

/** is there a common bit in t1 and t2 */
#define INV_F5426_TRANS_HAS_AND(a, b) \
(false \
 || a[0] & b[0] \
 || a[1] & b[1] \
 || a[2] & b[2] \
 || a[3] & b[3] \
 || a[4] & b[4] \
 || a[5] & b[5] \
 || a[6] & b[6] \
)

#define INV_F5426_STATES_HAS_AND(a, b) \
(false \
 || a[0] & b[0] \
 || a[1] & b[1] \
 || a[2] & b[2] \
 || a[3] & b[3] \
 || a[4] & b[4] \
 || a[5] & b[5] \
 || a[6] & b[6] \
)


/** is there bit set in a */
#define INV_F5426_TRANS_HAS_ANY(a) \
(false \
 || a[0] \
 || a[1] \
 || a[2] \
 || a[3] \
 || a[4] \
 || a[5] \
 || a[6] \
)

#define INV_F5426_STATES_HAS_ANY(a) \
(false \
 || a[0] \
 || a[1] \
 || a[2] \
 || a[3] \
 || a[4] \
 || a[5] \
 || a[6] \
)


/** or'ing bits in a with mask */
#define INV_F5426_TRANS_OR(a, mask) \
a[0] = a[0] | mask[0]; \
a[1] = a[1] | mask[1]; \
a[2] = a[2] | mask[2]; \
a[3] = a[3] | mask[3]; \
a[4] = a[4] | mask[4]; \
a[5] = a[5] | mask[5]; \
a[6] = a[6] | mask[6]; \

#define INV_F5426_STATES_OR(a, mask) \
a[0] = a[0] | mask[0]; \
a[1] = a[1] | mask[1]; \
a[2] = a[2] | mask[2]; \
a[3] = a[3] | mask[3]; \
a[4] = a[4] | mask[4]; \
a[5] = a[5] | mask[5]; \
a[6] = a[6] | mask[6]; \


/** clearing all bits of a */
#define INV_F5426_TRANS_CLEAR(a) \
a[0] = false; \
a[1] = false; \
a[2] = false; \
a[3] = false; \
a[4] = false; \
a[5] = false; \
a[6] = false; \

#define INV_F5426_STATES_CLEAR(a) \
a[0] = false; \
a[1] = false; \
a[2] = false; \
a[3] = false; \
a[4] = false; \
a[5] = false; \
a[6] = false; \


/** copy bits from a to b */
#define INV_F5426_TRANS_COPY(a, b) \
a[0] = b[0]; \
a[1] = b[1]; \
a[2] = b[2]; \
a[3] = b[3]; \
a[4] = b[4]; \
a[5] = b[5]; \
a[6] = b[6]; \

#define INV_F5426_STATES_COPY(a, b) \
a[0] = b[0]; \
a[1] = b[1]; \
a[2] = b[2]; \
a[3] = b[3]; \
a[4] = b[4]; \
a[5] = b[5]; \
a[6] = b[6]; \


/** and'ing bits in a with mask */
#define INV_F5426_TRANS_AND(a, mask) \
a[0] = a[0] & mask[0]; \
a[1] = a[1] & mask[1]; \
a[2] = a[2] & mask[2]; \
a[3] = a[3] & mask[3]; \
a[4] = a[4] & mask[4]; \
a[5] = a[5] & mask[5]; \
a[6] = a[6] & mask[6]; \

#define INV_F5426_STATES_AND(a, mask) \
a[0] = a[0] & mask[0]; \
a[1] = a[1] & mask[1]; \
a[2] = a[2] & mask[2]; \
a[3] = a[3] & mask[3]; \
a[4] = a[4] & mask[4]; \
a[5] = a[5] & mask[5]; \
a[6] = a[6] & mask[6]; \


/** not and'ing bits in a with mask */
#define INV_F5426_TRANS_AND_NOT(a, mask) \
a[0] = a[0] & !mask[0]; \
a[1] = a[1] & !mask[1]; \
a[2] = a[2] & !mask[2]; \
a[3] = a[3] & !mask[3]; \
a[4] = a[4] & !mask[4]; \
a[5] = a[5] & !mask[5]; \
a[6] = a[6] & !mask[6]; \

#define INV_F5426_STATES_AND_NOT(a, mask) \
a[0] = a[0] & !mask[0]; \
a[1] = a[1] & !mask[1]; \
a[2] = a[2] & !mask[2]; \
a[3] = a[3] & !mask[3]; \
a[4] = a[4] & !mask[4]; \
a[5] = a[5] & !mask[5]; \
a[6] = a[6] & !mask[6]; \


/* custom type definitions for ROOT_ */

/** is there a common bit in t1 and t2 */
#define INV_8CB85_TRANS_HAS_AND(a, b) \
(false \
 || a[0] & b[0] \
 || a[1] & b[1] \
 || a[2] & b[2] \
 || a[3] & b[3] \
 || a[4] & b[4] \
 || a[5] & b[5] \
 || a[6] & b[6] \
)

#define INV_8CB85_STATES_HAS_AND(a, b) \
(false \
 || a[0] & b[0] \
 || a[1] & b[1] \
 || a[2] & b[2] \
 || a[3] & b[3] \
 || a[4] & b[4] \
 || a[5] & b[5] \
 || a[6] & b[6] \
)


/** is there bit set in a */
#define INV_8CB85_TRANS_HAS_ANY(a) \
(false \
 || a[0] \
 || a[1] \
 || a[2] \
 || a[3] \
 || a[4] \
 || a[5] \
 || a[6] \
)

#define INV_8CB85_STATES_HAS_ANY(a) \
(false \
 || a[0] \
 || a[1] \
 || a[2] \
 || a[3] \
 || a[4] \
 || a[5] \
 || a[6] \
)


/** or'ing bits in a with mask */
#define INV_8CB85_TRANS_OR(a, mask) \
a[0] = a[0] | mask[0]; \
a[1] = a[1] | mask[1]; \
a[2] = a[2] | mask[2]; \
a[3] = a[3] | mask[3]; \
a[4] = a[4] | mask[4]; \
a[5] = a[5] | mask[5]; \
a[6] = a[6] | mask[6]; \

#define INV_8CB85_STATES_OR(a, mask) \
a[0] = a[0] | mask[0]; \
a[1] = a[1] | mask[1]; \
a[2] = a[2] | mask[2]; \
a[3] = a[3] | mask[3]; \
a[4] = a[4] | mask[4]; \
a[5] = a[5] | mask[5]; \
a[6] = a[6] | mask[6]; \


/** clearing all bits of a */
#define INV_8CB85_TRANS_CLEAR(a) \
a[0] = false; \
a[1] = false; \
a[2] = false; \
a[3] = false; \
a[4] = false; \
a[5] = false; \
a[6] = false; \

#define INV_8CB85_STATES_CLEAR(a) \
a[0] = false; \
a[1] = false; \
a[2] = false; \
a[3] = false; \
a[4] = false; \
a[5] = false; \
a[6] = false; \


/** copy bits from a to b */
#define INV_8CB85_TRANS_COPY(a, b) \
a[0] = b[0]; \
a[1] = b[1]; \
a[2] = b[2]; \
a[3] = b[3]; \
a[4] = b[4]; \
a[5] = b[5]; \
a[6] = b[6]; \

#define INV_8CB85_STATES_COPY(a, b) \
a[0] = b[0]; \
a[1] = b[1]; \
a[2] = b[2]; \
a[3] = b[3]; \
a[4] = b[4]; \
a[5] = b[5]; \
a[6] = b[6]; \


/** and'ing bits in a with mask */
#define INV_8CB85_TRANS_AND(a, mask) \
a[0] = a[0] & mask[0]; \
a[1] = a[1] & mask[1]; \
a[2] = a[2] & mask[2]; \
a[3] = a[3] & mask[3]; \
a[4] = a[4] & mask[4]; \
a[5] = a[5] & mask[5]; \
a[6] = a[6] & mask[6]; \

#define INV_8CB85_STATES_AND(a, mask) \
a[0] = a[0] & mask[0]; \
a[1] = a[1] & mask[1]; \
a[2] = a[2] & mask[2]; \
a[3] = a[3] & mask[3]; \
a[4] = a[4] & mask[4]; \
a[5] = a[5] & mask[5]; \
a[6] = a[6] & mask[6]; \


/** not and'ing bits in a with mask */
#define INV_8CB85_TRANS_AND_NOT(a, mask) \
a[0] = a[0] & !mask[0]; \
a[1] = a[1] & !mask[1]; \
a[2] = a[2] & !mask[2]; \
a[3] = a[3] & !mask[3]; \
a[4] = a[4] & !mask[4]; \
a[5] = a[5] & !mask[5]; \
a[6] = a[6] & !mask[6]; \

#define INV_8CB85_STATES_AND_NOT(a, mask) \
a[0] = a[0] & !mask[0]; \
a[1] = a[1] & !mask[1]; \
a[2] = a[2] & !mask[2]; \
a[3] = a[3] & !mask[3]; \
a[4] = a[4] & !mask[4]; \
a[5] = a[5] & !mask[5]; \
a[6] = a[6] & !mask[6]; \


/* custom type definitions for ROOT_ */

/** is there a common bit in t1 and t2 */
#define INV_5C805_TRANS_HAS_AND(a, b) \
(false \
 || a[0] & b[0] \
 || a[1] & b[1] \
 || a[2] & b[2] \
 || a[3] & b[3] \
 || a[4] & b[4] \
 || a[5] & b[5] \
 || a[6] & b[6] \
)

#define INV_5C805_STATES_HAS_AND(a, b) \
(false \
 || a[0] & b[0] \
 || a[1] & b[1] \
 || a[2] & b[2] \
 || a[3] & b[3] \
 || a[4] & b[4] \
 || a[5] & b[5] \
 || a[6] & b[6] \
)


/** is there bit set in a */
#define INV_5C805_TRANS_HAS_ANY(a) \
(false \
 || a[0] \
 || a[1] \
 || a[2] \
 || a[3] \
 || a[4] \
 || a[5] \
 || a[6] \
)

#define INV_5C805_STATES_HAS_ANY(a) \
(false \
 || a[0] \
 || a[1] \
 || a[2] \
 || a[3] \
 || a[4] \
 || a[5] \
 || a[6] \
)


/** or'ing bits in a with mask */
#define INV_5C805_TRANS_OR(a, mask) \
a[0] = a[0] | mask[0]; \
a[1] = a[1] | mask[1]; \
a[2] = a[2] | mask[2]; \
a[3] = a[3] | mask[3]; \
a[4] = a[4] | mask[4]; \
a[5] = a[5] | mask[5]; \
a[6] = a[6] | mask[6]; \

#define INV_5C805_STATES_OR(a, mask) \
a[0] = a[0] | mask[0]; \
a[1] = a[1] | mask[1]; \
a[2] = a[2] | mask[2]; \
a[3] = a[3] | mask[3]; \
a[4] = a[4] | mask[4]; \
a[5] = a[5] | mask[5]; \
a[6] = a[6] | mask[6]; \


/** clearing all bits of a */
#define INV_5C805_TRANS_CLEAR(a) \
a[0] = false; \
a[1] = false; \
a[2] = false; \
a[3] = false; \
a[4] = false; \
a[5] = false; \
a[6] = false; \

#define INV_5C805_STATES_CLEAR(a) \
a[0] = false; \
a[1] = false; \
a[2] = false; \
a[3] = false; \
a[4] = false; \
a[5] = false; \
a[6] = false; \


/** copy bits from a to b */
#define INV_5C805_TRANS_COPY(a, b) \
a[0] = b[0]; \
a[1] = b[1]; \
a[2] = b[2]; \
a[3] = b[3]; \
a[4] = b[4]; \
a[5] = b[5]; \
a[6] = b[6]; \

#define INV_5C805_STATES_COPY(a, b) \
a[0] = b[0]; \
a[1] = b[1]; \
a[2] = b[2]; \
a[3] = b[3]; \
a[4] = b[4]; \
a[5] = b[5]; \
a[6] = b[6]; \


/** and'ing bits in a with mask */
#define INV_5C805_TRANS_AND(a, mask) \
a[0] = a[0] & mask[0]; \
a[1] = a[1] & mask[1]; \
a[2] = a[2] & mask[2]; \
a[3] = a[3] & mask[3]; \
a[4] = a[4] & mask[4]; \
a[5] = a[5] & mask[5]; \
a[6] = a[6] & mask[6]; \

#define INV_5C805_STATES_AND(a, mask) \
a[0] = a[0] & mask[0]; \
a[1] = a[1] & mask[1]; \
a[2] = a[2] & mask[2]; \
a[3] = a[3] & mask[3]; \
a[4] = a[4] & mask[4]; \
a[5] = a[5] & mask[5]; \
a[6] = a[6] & mask[6]; \


/** not and'ing bits in a with mask */
#define INV_5C805_TRANS_AND_NOT(a, mask) \
a[0] = a[0] & !mask[0]; \
a[1] = a[1] & !mask[1]; \
a[2] = a[2] & !mask[2]; \
a[3] = a[3] & !mask[3]; \
a[4] = a[4] & !mask[4]; \
a[5] = a[5] & !mask[5]; \
a[6] = a[6] & !mask[6]; \

#define INV_5C805_STATES_AND_NOT(a, mask) \
a[0] = a[0] & !mask[0]; \
a[1] = a[1] & !mask[1]; \
a[2] = a[2] & !mask[2]; \
a[3] = a[3] & !mask[3]; \
a[4] = a[4] & !mask[4]; \
a[5] = a[5] & !mask[5]; \
a[6] = a[6] & !mask[6]; \


/* custom type definitions for ROOT_ */

/** is there a common bit in t1 and t2 */
#define INV_F88AA_TRANS_HAS_AND(a, b) \
(false \
 || a[0] & b[0] \
 || a[1] & b[1] \
 || a[2] & b[2] \
 || a[3] & b[3] \
 || a[4] & b[4] \
 || a[5] & b[5] \
 || a[6] & b[6] \
)

#define INV_F88AA_STATES_HAS_AND(a, b) \
(false \
 || a[0] & b[0] \
 || a[1] & b[1] \
 || a[2] & b[2] \
 || a[3] & b[3] \
 || a[4] & b[4] \
 || a[5] & b[5] \
 || a[6] & b[6] \
)


/** is there bit set in a */
#define INV_F88AA_TRANS_HAS_ANY(a) \
(false \
 || a[0] \
 || a[1] \
 || a[2] \
 || a[3] \
 || a[4] \
 || a[5] \
 || a[6] \
)

#define INV_F88AA_STATES_HAS_ANY(a) \
(false \
 || a[0] \
 || a[1] \
 || a[2] \
 || a[3] \
 || a[4] \
 || a[5] \
 || a[6] \
)


/** or'ing bits in a with mask */
#define INV_F88AA_TRANS_OR(a, mask) \
a[0] = a[0] | mask[0]; \
a[1] = a[1] | mask[1]; \
a[2] = a[2] | mask[2]; \
a[3] = a[3] | mask[3]; \
a[4] = a[4] | mask[4]; \
a[5] = a[5] | mask[5]; \
a[6] = a[6] | mask[6]; \

#define INV_F88AA_STATES_OR(a, mask) \
a[0] = a[0] | mask[0]; \
a[1] = a[1] | mask[1]; \
a[2] = a[2] | mask[2]; \
a[3] = a[3] | mask[3]; \
a[4] = a[4] | mask[4]; \
a[5] = a[5] | mask[5]; \
a[6] = a[6] | mask[6]; \


/** clearing all bits of a */
#define INV_F88AA_TRANS_CLEAR(a) \
a[0] = false; \
a[1] = false; \
a[2] = false; \
a[3] = false; \
a[4] = false; \
a[5] = false; \
a[6] = false; \

#define INV_F88AA_STATES_CLEAR(a) \
a[0] = false; \
a[1] = false; \
a[2] = false; \
a[3] = false; \
a[4] = false; \
a[5] = false; \
a[6] = false; \


/** copy bits from a to b */
#define INV_F88AA_TRANS_COPY(a, b) \
a[0] = b[0]; \
a[1] = b[1]; \
a[2] = b[2]; \
a[3] = b[3]; \
a[4] = b[4]; \
a[5] = b[5]; \
a[6] = b[6]; \

#define INV_F88AA_STATES_COPY(a, b) \
a[0] = b[0]; \
a[1] = b[1]; \
a[2] = b[2]; \
a[3] = b[3]; \
a[4] = b[4]; \
a[5] = b[5]; \
a[6] = b[6]; \


/** and'ing bits in a with mask */
#define INV_F88AA_TRANS_AND(a, mask) \
a[0] = a[0] & mask[0]; \
a[1] = a[1] & mask[1]; \
a[2] = a[2] & mask[2]; \
a[3] = a[3] & mask[3]; \
a[4] = a[4] & mask[4]; \
a[5] = a[5] & mask[5]; \
a[6] = a[6] & mask[6]; \

#define INV_F88AA_STATES_AND(a, mask) \
a[0] = a[0] & mask[0]; \
a[1] = a[1] & mask[1]; \
a[2] = a[2] & mask[2]; \
a[3] = a[3] & mask[3]; \
a[4] = a[4] & mask[4]; \
a[5] = a[5] & mask[5]; \
a[6] = a[6] & mask[6]; \


/** not and'ing bits in a with mask */
#define INV_F88AA_TRANS_AND_NOT(a, mask) \
a[0] = a[0] & !mask[0]; \
a[1] = a[1] & !mask[1]; \
a[2] = a[2] & !mask[2]; \
a[3] = a[3] & !mask[3]; \
a[4] = a[4] & !mask[4]; \
a[5] = a[5] & !mask[5]; \
a[6] = a[6] & !mask[6]; \

#define INV_F88AA_STATES_AND_NOT(a, mask) \
a[0] = a[0] & !mask[0]; \
a[1] = a[1] & !mask[1]; \
a[2] = a[2] & !mask[2]; \
a[3] = a[3] & !mask[3]; \
a[4] = a[4] & !mask[4]; \
a[5] = a[5] & !mask[5]; \
a[6] = a[6] & !mask[6]; \


/* custom type definitions for ROOT_ */

/** is there a common bit in t1 and t2 */
#define INV_41D63_TRANS_HAS_AND(a, b) \
(false \
 || a[0] & b[0] \
 || a[1] & b[1] \
 || a[2] & b[2] \
 || a[3] & b[3] \
 || a[4] & b[4] \
 || a[5] & b[5] \
 || a[6] & b[6] \
)

#define INV_41D63_STATES_HAS_AND(a, b) \
(false \
 || a[0] & b[0] \
 || a[1] & b[1] \
 || a[2] & b[2] \
 || a[3] & b[3] \
 || a[4] & b[4] \
 || a[5] & b[5] \
 || a[6] & b[6] \
)


/** is there bit set in a */
#define INV_41D63_TRANS_HAS_ANY(a) \
(false \
 || a[0] \
 || a[1] \
 || a[2] \
 || a[3] \
 || a[4] \
 || a[5] \
 || a[6] \
)

#define INV_41D63_STATES_HAS_ANY(a) \
(false \
 || a[0] \
 || a[1] \
 || a[2] \
 || a[3] \
 || a[4] \
 || a[5] \
 || a[6] \
)


/** or'ing bits in a with mask */
#define INV_41D63_TRANS_OR(a, mask) \
a[0] = a[0] | mask[0]; \
a[1] = a[1] | mask[1]; \
a[2] = a[2] | mask[2]; \
a[3] = a[3] | mask[3]; \
a[4] = a[4] | mask[4]; \
a[5] = a[5] | mask[5]; \
a[6] = a[6] | mask[6]; \

#define INV_41D63_STATES_OR(a, mask) \
a[0] = a[0] | mask[0]; \
a[1] = a[1] | mask[1]; \
a[2] = a[2] | mask[2]; \
a[3] = a[3] | mask[3]; \
a[4] = a[4] | mask[4]; \
a[5] = a[5] | mask[5]; \
a[6] = a[6] | mask[6]; \


/** clearing all bits of a */
#define INV_41D63_TRANS_CLEAR(a) \
a[0] = false; \
a[1] = false; \
a[2] = false; \
a[3] = false; \
a[4] = false; \
a[5] = false; \
a[6] = false; \

#define INV_41D63_STATES_CLEAR(a) \
a[0] = false; \
a[1] = false; \
a[2] = false; \
a[3] = false; \
a[4] = false; \
a[5] = false; \
a[6] = false; \


/** copy bits from a to b */
#define INV_41D63_TRANS_COPY(a, b) \
a[0] = b[0]; \
a[1] = b[1]; \
a[2] = b[2]; \
a[3] = b[3]; \
a[4] = b[4]; \
a[5] = b[5]; \
a[6] = b[6]; \

#define INV_41D63_STATES_COPY(a, b) \
a[0] = b[0]; \
a[1] = b[1]; \
a[2] = b[2]; \
a[3] = b[3]; \
a[4] = b[4]; \
a[5] = b[5]; \
a[6] = b[6]; \


/** and'ing bits in a with mask */
#define INV_41D63_TRANS_AND(a, mask) \
a[0] = a[0] & mask[0]; \
a[1] = a[1] & mask[1]; \
a[2] = a[2] & mask[2]; \
a[3] = a[3] & mask[3]; \
a[4] = a[4] & mask[4]; \
a[5] = a[5] & mask[5]; \
a[6] = a[6] & mask[6]; \

#define INV_41D63_STATES_AND(a, mask) \
a[0] = a[0] & mask[0]; \
a[1] = a[1] & mask[1]; \
a[2] = a[2] & mask[2]; \
a[3] = a[3] & mask[3]; \
a[4] = a[4] & mask[4]; \
a[5] = a[5] & mask[5]; \
a[6] = a[6] & mask[6]; \


/** not and'ing bits in a with mask */
#define INV_41D63_TRANS_AND_NOT(a, mask) \
a[0] = a[0] & !mask[0]; \
a[1] = a[1] & !mask[1]; \
a[2] = a[2] & !mask[2]; \
a[3] = a[3] & !mask[3]; \
a[4] = a[4] & !mask[4]; \
a[5] = a[5] & !mask[5]; \
a[6] = a[6] & !mask[6]; \

#define INV_41D63_STATES_AND_NOT(a, mask) \
a[0] = a[0] & !mask[0]; \
a[1] = a[1] & !mask[1]; \
a[2] = a[2] & !mask[2]; \
a[3] = a[3] & !mask[3]; \
a[4] = a[4] & !mask[4]; \
a[5] = a[5] & !mask[5]; \
a[6] = a[6] & !mask[6]; \


/* custom type definitions for ROOT_ */

/* common type definitions */
typedef _event_data_t {
  int p_id;
};

typedef _event_t {
  bool delay;
  short seqNr;
  byte name;
  byte invokeid;
  byte origin;
  _event_data_t data;
  int sendid;
};


/* custom definitions and global variables */
bool ROOT_flags[6];
bool ROOT_config[4];
bool ROOT_history[4];
bool ROOT_invocations[4];
hidden _event_t ROOT__event;               /* current event */
hidden _event_t ROOT__tmpE;          /* temporary event for send */
chan ROOT_iQ   = [7] of {_event_t}  /* internal queue */
chan ROOT_eQ   = [13] of {_event_t}  /* external queue */

typedef ROOT_transition_t {
  unsigned source : 2;
  bool target[4];
  bool type[5];
  bool conflicts[3];
  bool exit_set[4];
}
hidden ROOT_transition_t ROOT_transitions[3];

typedef ROOT_state_t {
  unsigned parent : 2;
  bool children[4];
  bool completion[4];
  bool ancestors[4];
  bool type[8];
}
hidden ROOT_state_t ROOT_states[4];

typedef ROOT_ctx_t {
  bool conflicts[3];
  bool trans_set[3];
  bool target_set[4];
  bool exit_set[4];
  bool entry_set[4];
  bool tmp_states[4];
}
hidden ROOT_ctx_t ROOT_ctx;


int ROOT_forks[5];
int ROOT_NUM_OF_PHIL;
int ROOT_current_phil;
int ROOT_delay;
int ROOT_left_fork;
int ROOT_right_fork;
int ROOT_seed;
hidden int ROOT_procid;             /* the process id running this machine */

/* custom definitions and global variables */
bool INV_F5426_flags[6];
bool INV_F5426_config[7];
bool INV_F5426_history[7];
bool INV_F5426_invocations[7];
hidden _event_t INV_F5426__event;               /* current event */
hidden _event_t INV_F5426__tmpE;          /* temporary event for send */
chan INV_F5426_iQ   = [7] of {_event_t}  /* internal queue */
chan INV_F5426_eQ   = [13] of {_event_t}  /* external queue */

typedef INV_F5426_transition_t {
  unsigned source : 3;
  bool target[7];
  bool type[5];
  bool conflicts[7];
  bool exit_set[7];
}
hidden INV_F5426_transition_t INV_F5426_transitions[7];

typedef INV_F5426_state_t {
  unsigned parent : 3;
  bool children[7];
  bool completion[7];
  bool ancestors[7];
  bool type[8];
}
hidden INV_F5426_state_t INV_F5426_states[7];

typedef INV_F5426_ctx_t {
  bool conflicts[7];
  bool trans_set[7];
  bool target_set[7];
  bool exit_set[7];
  bool entry_set[7];
  bool tmp_states[7];
}
hidden INV_F5426_ctx_t INV_F5426_ctx;


int INV_F5426_p_id;
int INV_F5426_delay;
int INV_F5426_random_delay;
hidden int INV_F5426_procid;             /* the process id running this machine */

/* custom definitions and global variables */
bool INV_8CB85_flags[6];
bool INV_8CB85_config[7];
bool INV_8CB85_history[7];
bool INV_8CB85_invocations[7];
hidden _event_t INV_8CB85__event;               /* current event */
hidden _event_t INV_8CB85__tmpE;          /* temporary event for send */
chan INV_8CB85_iQ   = [7] of {_event_t}  /* internal queue */
chan INV_8CB85_eQ   = [13] of {_event_t}  /* external queue */

typedef INV_8CB85_transition_t {
  unsigned source : 3;
  bool target[7];
  bool type[5];
  bool conflicts[7];
  bool exit_set[7];
}
hidden INV_8CB85_transition_t INV_8CB85_transitions[7];

typedef INV_8CB85_state_t {
  unsigned parent : 3;
  bool children[7];
  bool completion[7];
  bool ancestors[7];
  bool type[8];
}
hidden INV_8CB85_state_t INV_8CB85_states[7];

typedef INV_8CB85_ctx_t {
  bool conflicts[7];
  bool trans_set[7];
  bool target_set[7];
  bool exit_set[7];
  bool entry_set[7];
  bool tmp_states[7];
}
hidden INV_8CB85_ctx_t INV_8CB85_ctx;


int INV_8CB85_p_id;
int INV_8CB85_delay;
int INV_8CB85_random_delay;
hidden int INV_8CB85_procid;             /* the process id running this machine */

/* custom definitions and global variables */
bool INV_5C805_flags[6];
bool INV_5C805_config[7];
bool INV_5C805_history[7];
bool INV_5C805_invocations[7];
hidden _event_t INV_5C805__event;               /* current event */
hidden _event_t INV_5C805__tmpE;          /* temporary event for send */
chan INV_5C805_iQ   = [7] of {_event_t}  /* internal queue */
chan INV_5C805_eQ   = [13] of {_event_t}  /* external queue */

typedef INV_5C805_transition_t {
  unsigned source : 3;
  bool target[7];
  bool type[5];
  bool conflicts[7];
  bool exit_set[7];
}
hidden INV_5C805_transition_t INV_5C805_transitions[7];

typedef INV_5C805_state_t {
  unsigned parent : 3;
  bool children[7];
  bool completion[7];
  bool ancestors[7];
  bool type[8];
}
hidden INV_5C805_state_t INV_5C805_states[7];

typedef INV_5C805_ctx_t {
  bool conflicts[7];
  bool trans_set[7];
  bool target_set[7];
  bool exit_set[7];
  bool entry_set[7];
  bool tmp_states[7];
}
hidden INV_5C805_ctx_t INV_5C805_ctx;


int INV_5C805_p_id;
int INV_5C805_delay;
int INV_5C805_random_delay;
hidden int INV_5C805_procid;             /* the process id running this machine */

/* custom definitions and global variables */
bool INV_F88AA_flags[6];
bool INV_F88AA_config[7];
bool INV_F88AA_history[7];
bool INV_F88AA_invocations[7];
hidden _event_t INV_F88AA__event;               /* current event */
hidden _event_t INV_F88AA__tmpE;          /* temporary event for send */
chan INV_F88AA_iQ   = [7] of {_event_t}  /* internal queue */
chan INV_F88AA_eQ   = [13] of {_event_t}  /* external queue */

typedef INV_F88AA_transition_t {
  unsigned source : 3;
  bool target[7];
  bool type[5];
  bool conflicts[7];
  bool exit_set[7];
}
hidden INV_F88AA_transition_t INV_F88AA_transitions[7];

typedef INV_F88AA_state_t {
  unsigned parent : 3;
  bool children[7];
  bool completion[7];
  bool ancestors[7];
  bool type[8];
}
hidden INV_F88AA_state_t INV_F88AA_states[7];

typedef INV_F88AA_ctx_t {
  bool conflicts[7];
  bool trans_set[7];
  bool target_set[7];
  bool exit_set[7];
  bool entry_set[7];
  bool tmp_states[7];
}
hidden INV_F88AA_ctx_t INV_F88AA_ctx;


int INV_F88AA_p_id;
int INV_F88AA_delay;
int INV_F88AA_random_delay;
hidden int INV_F88AA_procid;             /* the process id running this machine */

/* custom definitions and global variables */
bool INV_41D63_flags[6];
bool INV_41D63_config[7];
bool INV_41D63_history[7];
bool INV_41D63_invocations[7];
hidden _event_t INV_41D63__event;               /* current event */
hidden _event_t INV_41D63__tmpE;          /* temporary event for send */
chan INV_41D63_iQ   = [7] of {_event_t}  /* internal queue */
chan INV_41D63_eQ   = [13] of {_event_t}  /* external queue */

typedef INV_41D63_transition_t {
  unsigned source : 3;
  bool target[7];
  bool type[5];
  bool conflicts[7];
  bool exit_set[7];
}
hidden INV_41D63_transition_t INV_41D63_transitions[7];

typedef INV_41D63_state_t {
  unsigned parent : 3;
  bool children[7];
  bool completion[7];
  bool ancestors[7];
  bool type[8];
}
hidden INV_41D63_state_t INV_41D63_states[7];

typedef INV_41D63_ctx_t {
  bool conflicts[7];
  bool trans_set[7];
  bool target_set[7];
  bool exit_set[7];
  bool entry_set[7];
  bool tmp_states[7];
}
hidden INV_41D63_ctx_t INV_41D63_ctx;


int INV_41D63_p_id;
int INV_41D63_delay;
int INV_41D63_random_delay;
hidden int INV_41D63_procid;             /* the process id running this machine */

hidden int tmpIndex;
hidden _event_t tmpE;
hidden int _lastSendId = 0;         /* sequential counter for send ids */
hidden short _lastSeqId = 0;     /* sequential counter for delayed events */


hidden _event_t _iwdQ[12];
hidden int _iwdQLength = 0;
hidden int _iwdIdx1 = 0;
hidden int _iwdIdx2 = 0;
hidden _event_t _iwdTmpE;
hidden _event_t _iwdLastE;
bool _iwdInserted = false;

/* last event in given queue is potentially at wrong position */
inline insertWithDelay(queue) {
  d_step {

    /* only process for non-trivial queues */
    if
    :: len(queue) > 1 -> {

#if TRACE_EXECUTION
printf("%d: Reshuffling events\n", _pid);
#endif


      /* move all events but last over and remember the last one */
      _iwdIdx1 = 0;
      _iwdQLength = len(queue) - 1;

      do
      :: _iwdIdx1 < _iwdQLength -> {
        queue?_iwdTmpE;
        _iwdQ[_iwdIdx1].name = _iwdTmpE.name;
                _iwdQ[_iwdIdx1].data.p_id = _iwdTmpE.data.p_id;
                _iwdQ[_iwdIdx1].delay = _iwdTmpE.delay;
                _iwdQ[_iwdIdx1].invokeid = _iwdTmpE.invokeid;
                _iwdQ[_iwdIdx1].name = _iwdTmpE.name;
                _iwdQ[_iwdIdx1].origin = _iwdTmpE.origin;
                _iwdQ[_iwdIdx1].sendid = _iwdTmpE.sendid;
                _iwdQ[_iwdIdx1].seqNr = _iwdTmpE.seqNr;
        _iwdIdx1++;
      }
      :: else -> break;
      od

      queue?_iwdLastE;

      /* _iwdQ now contains all but last item in _iwdLastE */
      assert(len(queue) == 0);

      /* reinsert into queue and place _iwdLastE correctly */
      _iwdInserted = false;
      _iwdIdx2 = 0;

      do
      :: _iwdIdx2 < _iwdIdx1 -> {
        _iwdTmpE.name = _iwdQ[_iwdIdx2].name;
        _iwdTmpE.data.p_id = _iwdQ[_iwdIdx2].data.p_id;
        _iwdTmpE.delay = _iwdQ[_iwdIdx2].delay;
        _iwdTmpE.invokeid = _iwdQ[_iwdIdx2].invokeid;
        _iwdTmpE.name = _iwdQ[_iwdIdx2].name;
        _iwdTmpE.origin = _iwdQ[_iwdIdx2].origin;
        _iwdTmpE.sendid = _iwdQ[_iwdIdx2].sendid;
        _iwdTmpE.seqNr = _iwdQ[_iwdIdx2].seqNr;

        if
        :: _iwdTmpE.delay > _iwdLastE.delay && !_iwdInserted -> {
          queue!_iwdLastE;

#if TRACE_EXECUTION
printf("%d: Event %d has delay %d (last)\n", _pid, _iwdLastE.name, _iwdLastE.delay);
#endif

          _iwdInserted = true;
        }
        :: else -> skip
        fi;

        queue!_iwdTmpE;

#if TRACE_EXECUTION
printf("%d: Event %d has delay %d\n", _pid, _iwdTmpE.name, _iwdTmpE.delay);
#endif

        _iwdIdx2++;
      }
      :: else -> break;
      od

      if
      :: !_iwdInserted -> {
         queue!_iwdLastE;

#if TRACE_EXECUTION
printf("%d: Event %d has delay %d (last)\n", _pid, _iwdLastE.name, _iwdLastE.delay);
#endif

      }
      :: else -> skip;
      fi;

    }
    :: else -> skip;
    fi;
  }
}

inline advanceTime(increment, queue) {
  tmpIndex = 0;
  do
  :: tmpIndex < len(queue) -> {
    queue?tmpE;
    if
    :: tmpE.delay >= increment -> tmpE.delay = tmpE.delay - increment;
    :: else -> skip;
    fi
    queue!tmpE;
    tmpIndex++;
  }
  :: else -> break;
  od
}

inline scheduleMachines() {
  /* schedule state-machines with regard to their event's delay */
  skip;
  d_step {

/* determine smallest delay */
    int smallestDelay = 2147483647;
    determineSmallestDelay(smallestDelay, ROOT_eQ);
    determineSmallestDelay(smallestDelay, INV_F5426_eQ);
    determineSmallestDelay(smallestDelay, INV_8CB85_eQ);
    determineSmallestDelay(smallestDelay, INV_5C805_eQ);
    determineSmallestDelay(smallestDelay, INV_F88AA_eQ);
    determineSmallestDelay(smallestDelay, INV_41D63_eQ);

#if TRACE_EXECUTION
printf("%d: Smallest delay is %d\n", _pid, smallestDelay);
#endif


/* prioritize processes with lowest delay or internal events */
    rescheduleProcess(smallestDelay, ROOT_procid, ROOT_iQ, ROOT_eQ);
    rescheduleProcess(smallestDelay, INV_F5426_procid, INV_F5426_iQ, INV_F5426_eQ);
    rescheduleProcess(smallestDelay, INV_8CB85_procid, INV_8CB85_iQ, INV_8CB85_eQ);
    rescheduleProcess(smallestDelay, INV_5C805_procid, INV_5C805_iQ, INV_5C805_eQ);
    rescheduleProcess(smallestDelay, INV_F88AA_procid, INV_F88AA_iQ, INV_F88AA_eQ);
    rescheduleProcess(smallestDelay, INV_41D63_procid, INV_41D63_iQ, INV_41D63_eQ);

/* advance time by subtracting the smallest delay from all event delays */
    if
    :: (smallestDelay > 0) -> {
      advanceTime(smallestDelay, ROOT_eQ);
      advanceTime(smallestDelay, INV_F5426_eQ);
      advanceTime(smallestDelay, INV_8CB85_eQ);
      advanceTime(smallestDelay, INV_5C805_eQ);
      advanceTime(smallestDelay, INV_F88AA_eQ);
      advanceTime(smallestDelay, INV_41D63_eQ);
    }
    :: else -> skip;
    fi;
  }
  set_priority(_pid, 10);

}

inline rescheduleProcess(smallestDelay, procId, internalQ, externalQ) {
  set_priority(procId, 1);
  if
  :: len(internalQ) > 0 -> set_priority(procId, 10);
  :: else {
    if
    :: len(externalQ) > 0 -> {
      externalQ?<tmpE>;
      if
      :: smallestDelay == tmpE.delay -> set_priority(procId, 10);
      :: else -> skip;
      fi;
    }
    :: else -> skip;
    fi;
  }
  fi;
}

inline determineSmallestDelay(smallestDelay, queue) {
  if
  :: len(queue) > 0 -> {
    queue?<tmpE>;
    if
    :: (tmpE.delay < smallestDelay) -> { smallestDelay = tmpE.delay; }
    :: else -> skip;
    fi;
  }
  :: else -> skip;
  fi;
}

inline removePendingEventsFromInvoker(invoker) {
  removePendingEventsFromInvokerOnQueue(invoker, ROOT_eQ);
  removePendingEventsFromInvokerOnQueue(invoker, INV_F5426_eQ);
  removePendingEventsFromInvokerOnQueue(invoker, INV_8CB85_eQ);
  removePendingEventsFromInvokerOnQueue(invoker, INV_5C805_eQ);
  removePendingEventsFromInvokerOnQueue(invoker, INV_F88AA_eQ);
  removePendingEventsFromInvokerOnQueue(invoker, INV_41D63_eQ);
}

inline removePendingEventsFromInvokerOnQueue(invoker, queue) {
  tmpIndex = len(queue);
  do
  :: tmpIndex > 0 -> {
    queue?tmpE;
    if
    :: false || tmpE.delay == 0 || tmpE.invokeid != invoker
 -> {

#if TRACE_EXECUTION
printf("%d: Reenqueing event %d\n", _pid, tmpE.name);
#endif

      queue!tmpE;
    }
    :: else -> {

#if TRACE_EXECUTION
printf("%d: Dropping event %d\n", _pid, tmpE.name);
#endif

      skip;
    }
    fi
    tmpIndex = tmpIndex - 1;
  }
  :: else -> break;
  od
}

inline cancelSendId(sendIdentifier, source) {
  cancelSendIdOnQueue(sendIdentifier, source, ROOT_eQ);
  cancelSendIdOnQueue(sendIdentifier, source, INV_F5426_eQ);
  cancelSendIdOnQueue(sendIdentifier, source, INV_8CB85_eQ);
  cancelSendIdOnQueue(sendIdentifier, source, INV_5C805_eQ);
  cancelSendIdOnQueue(sendIdentifier, source, INV_F88AA_eQ);
  cancelSendIdOnQueue(sendIdentifier, source, INV_41D63_eQ);
}

inline cancelSendIdOnQueue(sendIdentifier, source, queue) {
  tmpIndex = 0;
  do
  :: tmpIndex < len(queue) -> {
    queue?tmpE;
    if
    :: tmpE.sendid != sendIdentifier || tmpE.origin != source || tmpE.delay == 0 -> queue!tmpE;
    :: else -> skip;
    fi
    tmpIndex++;
  }
  :: else -> break;
  od
}

/* machine microstep function */
#define ROOT_USCXML_NUMBER_STATES 4
#define ROOT_USCXML_NUMBER_TRANS 3

proctype ROOT_step() { atomic {

ROOT_procid = _pid;
unsigned i : 3,  j : 3,  k : 3;


/* ---------------------------- */
ROOT_MICROSTEP:
do
:: !ROOT_flags[USCXML_CTX_FINISHED] -> {
  /* Run until machine is finished */


#if TRACE_EXECUTION
printf("%d: Taking a step\n", _pid);
#endif

  /* Dequeue an event */
  ROOT_flags[USCXML_CTX_DEQUEUE_EXTERNAL] = false;
  if
  ::ROOT_flags[USCXML_CTX_SPONTANEOUS] -> {
    ROOT__event.name = USCXML_EVENT_SPONTANEOUS;

#if TRACE_EXECUTION
printf("%d: Trying with a spontaneous event\n", _pid);
#endif

  }
  :: else -> {
    if
    :: len(ROOT_iQ) != 0 -> {
      ROOT_iQ ? ROOT__event;

#if TRACE_EXECUTION
printf("%d: Deqeued an internal event\n", _pid);
#endif

    }
    :: else -> {
      ROOT_flags[USCXML_CTX_DEQUEUE_EXTERNAL] = true;
    }
    fi;
  }
  fi;


  if
  :: ROOT_flags[USCXML_CTX_DEQUEUE_EXTERNAL] -> {
    /* manage invocations */
    i = 0;
    do
    :: i < ROOT_USCXML_NUMBER_STATES -> {
      d_step { 
      /* uninvoke */
      if
      :: !ROOT_config[i] && ROOT_invocations[i] -> {

#if TRACE_EXECUTION
printf("%d: Uninvoking in state %d\n", _pid, i);
#endif

        if
        :: i == 1 -> {
          INV_F5426_flags[USCXML_CTX_FINISHED] = true;
          INV_8CB85_flags[USCXML_CTX_FINISHED] = true;
          INV_5C805_flags[USCXML_CTX_FINISHED] = true;
          INV_F88AA_flags[USCXML_CTX_FINISHED] = true;
          INV_41D63_flags[USCXML_CTX_FINISHED] = true;
        }
        :: else -> skip;
        fi
        ROOT_invocations[i] = false;
        skip;
      }
      :: else -> skip;
      fi;
      } /* d_step */

      /* invoke */
      if
      :: ROOT_config[i] && !ROOT_invocations[i] -> {
        if
      :: i == 1 -> {
          INV_F5426_p_id = 0;
          INV_F5426_delay = 3000 * ROOT_NUM_OF_PHIL;
          INV_F5426_random_delay = ROOT_seed;

#if TRACE_EXECUTION
printf("%d: Invoking in state %d\n", _pid, i);
#endif

          run INV_F5426_step() priority 20;
          INV_8CB85_p_id = 1;
          INV_8CB85_delay = 3000 * ROOT_NUM_OF_PHIL;
          INV_8CB85_random_delay = ROOT_seed;

#if TRACE_EXECUTION
printf("%d: Invoking in state %d\n", _pid, i);
#endif

          run INV_8CB85_step() priority 20;
          INV_5C805_p_id = 2;
          INV_5C805_delay = 3000 * ROOT_NUM_OF_PHIL;
          INV_5C805_random_delay = ROOT_seed;

#if TRACE_EXECUTION
printf("%d: Invoking in state %d\n", _pid, i);
#endif

          run INV_5C805_step() priority 20;
          INV_F88AA_p_id = 3;
          INV_F88AA_delay = 3000 * ROOT_NUM_OF_PHIL;
          INV_F88AA_random_delay = ROOT_seed;

#if TRACE_EXECUTION
printf("%d: Invoking in state %d\n", _pid, i);
#endif

          run INV_F88AA_step() priority 20;
          INV_41D63_p_id = 4;
          INV_41D63_delay = 3000 * ROOT_NUM_OF_PHIL;
          INV_41D63_random_delay = ROOT_seed;

#if TRACE_EXECUTION
printf("%d: Invoking in state %d\n", _pid, i);
#endif

          run INV_41D63_step() priority 20;
          ROOT_invocations[i] = true;
          skip;
        }
        :: else -> skip;
        fi
      }
      :: else -> skip;
      fi;
      i = i + 1;
    }
    :: else -> break;
    od;

    /* Determine machines with smallest delay and set their process priority */
    scheduleMachines();

    /* we may return to find ourselves terminated */
    if
    :: ROOT_flags[USCXML_CTX_FINISHED] -> {
      goto ROOT_TERMINATE_MACHINE;
    }
    :: else -> skip;
    fi
    /* Not sure if this should be before the invocation due to auto-forwarding */
    if
    :: len(ROOT_eQ) != 0 -> {
      ROOT_eQ ? ROOT__event;

      d_step {
      /* auto-forward event */
      i = 0;
      do
      :: i < ROOT_USCXML_NUMBER_STATES -> {
        if
        :: i == 1 && ROOT_invocations[i] -> { 
        skip;
      }
        :: else -> skip;
        fi
        i = i + 1;
      }
      :: else -> break;
      od

      /* finalize event */
      if
      :: ROOT__event.invokeid == INV_F5426 -> {

#if TRACE_EXECUTION
printf("%d: Finalizing event\n", _pid);
#endif

        skip
      }
      :: ROOT__event.invokeid == INV_8CB85 -> {

#if TRACE_EXECUTION
printf("%d: Finalizing event\n", _pid);
#endif

        skip
      }
      :: ROOT__event.invokeid == INV_5C805 -> {

#if TRACE_EXECUTION
printf("%d: Finalizing event\n", _pid);
#endif

        skip
      }
      :: ROOT__event.invokeid == INV_F88AA -> {

#if TRACE_EXECUTION
printf("%d: Finalizing event\n", _pid);
#endif

        skip
      }
      :: ROOT__event.invokeid == INV_41D63 -> {

#if TRACE_EXECUTION
printf("%d: Finalizing event\n", _pid);
#endif

        skip
      }
      :: else -> skip;
      fi
      } /* d_step */

#if TRACE_EXECUTION
printf("%d: Deqeued an external event\n", _pid);
#endif

    }
    fi;
  }
  :: else -> skip;
  fi


d_step { skip;

/* ---------------------------- */
ROOT_SELECT_TRANSITIONS:
ROOT_STATES_CLEAR(ROOT_ctx.target_set)
ROOT_STATES_CLEAR(ROOT_ctx.exit_set)
ROOT_TRANS_CLEAR(ROOT_ctx.conflicts)
ROOT_TRANS_CLEAR(ROOT_ctx.trans_set)
#if TRACE_EXECUTION
printf("%d: Establishing optimal transition set for event %d\n", _pid, ROOT__event.name );
#endif

#if TRACE_EXECUTION
printf("Configuration: ");
printf("%d%d%d%d", 
    ROOT_config[0], 
    ROOT_config[1], 
    ROOT_config[2], 
    ROOT_config[3]);
printf("\n");
#endif

  ROOT_flags[USCXML_CTX_TRANSITION_FOUND] = false;
  i = 0;
  do
  :: i < ROOT_USCXML_NUMBER_TRANS -> {
    /* only select non-history, non-initial transitions */
    if
    :: !ROOT_transitions[i].type[USCXML_TRANS_HISTORY] &&
       !ROOT_transitions[i].type[USCXML_TRANS_INITIAL] -> {
      if
      :: /* is the transition active? */
         ROOT_config[ROOT_transitions[i].source] && 

         /* is it non-conflicting? */
         !ROOT_ctx.conflicts[i] && 

         /* is it spontaneous with an event or vice versa? */
         ((ROOT__event.name == USCXML_EVENT_SPONTANEOUS && 
           ROOT_transitions[i].type[USCXML_TRANS_SPONTANEOUS]) || 
          (ROOT__event.name != USCXML_EVENT_SPONTANEOUS && 
           !ROOT_transitions[i].type[USCXML_TRANS_SPONTANEOUS])) &&

         /* is it matching and enabled? */
         (false 
          || (i == 0 && (false || ROOT__event.name == NEED_FORKS))
          || (i == 1 && (false || ROOT__event.name == RETURN_FORKS))
          || (i == 2 && (false || ROOT__event.name == DONE_INVOKE_INV_5C805 || ROOT__event.name == DONE_INVOKE_INV_8CB85 || ROOT__event.name == DONE_INVOKE || ROOT__event.name == DONE_INVOKE_INV_F5426 || ROOT__event.name == DONE_INVOKE_INV_41D63 || ROOT__event.name == DONE_INVOKE_INV_F88AA))
         ) -> {
        /* remember that we found a transition */
        ROOT_flags[USCXML_CTX_TRANSITION_FOUND] = true;

        /* transitions that are pre-empted */
        ROOT_TRANS_OR(ROOT_ctx.conflicts, ROOT_transitions[i].conflicts)

        /* states that are directly targeted (resolve as entry-set later) */
        ROOT_STATES_OR(ROOT_ctx.target_set, ROOT_transitions[i].target)

        /* states that will be left */
        ROOT_STATES_OR(ROOT_ctx.exit_set, ROOT_transitions[i].exit_set)

        ROOT_ctx.trans_set[i] = true;
      }
      :: else {
        skip;
      }
      fi
    }
    :: else -> {
      skip;
    }
    fi
    i = i + 1;
  }
  :: else -> break;
  od;
  ROOT_STATES_AND(ROOT_ctx.exit_set, ROOT_config)

#if TRACE_EXECUTION
printf("Selected Transitions: ");
printf("%d%d%d", 
    ROOT_ctx.trans_set[0], 
    ROOT_ctx.trans_set[1], 
    ROOT_ctx.trans_set[2]);
printf("\n");
#endif


#if TRACE_EXECUTION
printf("Target Set: ");
printf("%d%d%d%d", 
    ROOT_ctx.target_set[0], 
    ROOT_ctx.target_set[1], 
    ROOT_ctx.target_set[2], 
    ROOT_ctx.target_set[3]);
printf("\n");
#endif


#if TRACE_EXECUTION
printf("Exit Set: ");
printf("%d%d%d%d", 
    ROOT_ctx.exit_set[0], 
    ROOT_ctx.exit_set[1], 
    ROOT_ctx.exit_set[2], 
    ROOT_ctx.exit_set[3]);
printf("\n");
#endif

  if
  :: !ROOT_STATES_HAS_ANY(ROOT_config) -> {
    /* Enter initial configuration */
    ROOT_STATES_COPY(ROOT_ctx.target_set, ROOT_states[0].completion)
    ROOT_flags[USCXML_CTX_SPONTANEOUS] = true;
    ROOT_flags[USCXML_CTX_TRANSITION_FOUND] = true;

#if TRACE_EXECUTION
printf("%d: Entering initial default completion\n", _pid);
#endif


  }
  :: ROOT_flags[USCXML_CTX_TRANSITION_FOUND] -> {

#if TRACE_EXECUTION
printf("%d: Found transitions\n", _pid);
#endif

    ROOT_flags[USCXML_CTX_SPONTANEOUS] = true;
  }
  :: else {
    ROOT_flags[USCXML_CTX_SPONTANEOUS] = false;

#if TRACE_EXECUTION
printf("%d: Found NO transitions\n", _pid);
#endif

  }
  fi


  if
  :: ROOT_flags[USCXML_CTX_TRANSITION_FOUND] -> {
    /* only process anything if we found transitions or are on initial entry */
/* ---------------------------- */
/* REMEMBER_HISTORY: */

#if TRACE_EXECUTION
printf("%d: Save history configurations\n", _pid);
#endif

  if
  :: ROOT_STATES_HAS_ANY(ROOT_config) -> {
    /* only remember history on non-initial entry */
    i = 0;
    do
    :: i < ROOT_USCXML_NUMBER_STATES -> {
      if
      :: ROOT_states[i].type[USCXML_STATE_HISTORY_SHALLOW] ||
         ROOT_states[i].type[USCXML_STATE_HISTORY_DEEP] -> {
        if
        :: ROOT_ctx.exit_set[ROOT_states[i].parent] -> {
          /* a history state whose parent is about to be exited */

#if TRACE_EXECUTION
printf("%d: history state %d is about to be exited\n", _pid, i);
#endif


#if TRACE_EXECUTION
printf("COMPLET: ");
printf("%d%d%d%d", 
    ROOT_states[i].completion[0], 
    ROOT_states[i].completion[1], 
    ROOT_states[i].completion[2], 
    ROOT_states[i].completion[3]);
printf("\n");
#endif

          ROOT_STATES_COPY(ROOT_ctx.tmp_states, ROOT_states[i].completion)

          /* set those states who were enabled */
          ROOT_STATES_AND(ROOT_ctx.tmp_states, ROOT_config)

#if TRACE_EXECUTION
printf("CONFIG : ");
printf("%d%d%d%d", 
    ROOT_config[0], 
    ROOT_config[1], 
    ROOT_config[2], 
    ROOT_config[3]);
printf("\n");
#endif


#if TRACE_EXECUTION
printf("TMP_STS: ");
printf("%d%d%d%d", 
    ROOT_ctx.tmp_states[0], 
    ROOT_ctx.tmp_states[1], 
    ROOT_ctx.tmp_states[2], 
    ROOT_ctx.tmp_states[3]);
printf("\n");
#endif


          /* clear current history with completion mask */
          ROOT_STATES_AND_NOT(ROOT_history, ROOT_states[i].completion)

          /* set history */
          ROOT_STATES_OR(ROOT_history, ROOT_ctx.tmp_states)

        }
        :: else -> skip;
        fi;
      }
      :: else -> skip;
      fi;
      i = i + 1;
    }
    :: else -> break;
    od;


#if TRACE_EXECUTION
printf("History: ");
printf("%d%d%d%d", 
    ROOT_history[0], 
    ROOT_history[1], 
    ROOT_history[2], 
    ROOT_history[3]);
printf("\n");
#endif
  }
  :: else -> skip;
  fi;

/* ---------------------------- */
ROOT_ESTABLISH_ENTRY_SET:
  /* calculate new entry set */
  ROOT_STATES_COPY(ROOT_ctx.entry_set, ROOT_ctx.target_set)

  i = 0;
  do
  :: i < ROOT_USCXML_NUMBER_STATES -> {
    if
    :: ROOT_ctx.entry_set[i] -> {
      /* ancestor completion */
      ROOT_STATES_OR(ROOT_ctx.entry_set, ROOT_states[i].ancestors)
    }
    :: else -> skip;
    fi;
    i = i + 1;
  }
  :: else -> break;
  od;

  /* iterate for descendants */
  i = 0;
  do
  :: i < ROOT_USCXML_NUMBER_STATES -> {
    if
    :: ROOT_ctx.entry_set[i] -> {
      if
      :: ROOT_states[i].type[USCXML_STATE_PARALLEL] -> {
        ROOT_STATES_OR(ROOT_ctx.entry_set, ROOT_states[i].completion)
      }
      :: ROOT_states[i].type[USCXML_STATE_HISTORY_SHALLOW] ||
         ROOT_states[i].type[USCXML_STATE_HISTORY_DEEP] -> {

#if TRACE_EXECUTION
printf("%d: Descendant completion for history state %d\n", _pid, i);
#endif

        if
        :: !ROOT_STATES_HAS_AND(ROOT_states[i].completion, ROOT_history) && !ROOT_config[ROOT_states[i].parent] -> {
          /* nothing set for history, look for a default transition */

#if TRACE_EXECUTION
printf("%d: Fresh history in target set\n", _pid);
#endif

          j = 0;
          do
          :: j < ROOT_USCXML_NUMBER_TRANS -> {
             if
             :: ROOT_transitions[j].source == i -> {
               ROOT_ctx.trans_set[j] = true;
               ROOT_STATES_OR(ROOT_ctx.entry_set, ROOT_transitions[j].target)

               if
               :: (ROOT_states[i].type[USCXML_STATE_HISTORY_DEEP] &&
                   !ROOT_STATES_HAS_AND(ROOT_transitions[j].target, ROOT_states[i].children)                  ) -> {
                 k = i + 1
                 do
                 :: k < ROOT_USCXML_NUMBER_STATES -> {
                   if
                   :: ROOT_transitions[j].target[k] -> {
                     ROOT_STATES_OR(ROOT_ctx.entry_set, ROOT_states[k].ancestors)
                     break;

                   }
                   :: else -> skip;
                   fi
                   k = k + 1;
                 }
                 :: else -> break;
                 od
               }
               :: else -> skip;
               fi
               break;
             }
             :: else -> skip;
             fi
             j = j + 1;
          }
          :: else -> break
          od
          skip;
        }
        :: else -> {

#if TRACE_EXECUTION
printf("%d: Established history in target set\n", _pid);
#endif

          ROOT_STATES_COPY(ROOT_ctx.tmp_states, ROOT_states[i].completion)
          ROOT_STATES_AND(ROOT_ctx.tmp_states, ROOT_history)
          ROOT_STATES_OR(ROOT_ctx.entry_set, ROOT_ctx.tmp_states)
          if
          :: ROOT_states[i].type[USCXML_STATE_HAS_HISTORY] ||
             ROOT_states[i].type[USCXML_STATE_HISTORY_DEEP] -> { 
            /* a deep history state with nested histories -> more completion */

#if TRACE_EXECUTION
printf("%d: DEEP HISTORY\n", _pid);
#endif

            j = i + 1;
            do
            :: j < ROOT_USCXML_NUMBER_STATES -> {
              if
              :: (ROOT_states[i].completion[j] &&
                  ROOT_ctx.entry_set[j] && 
                  ROOT_states[j].type[USCXML_STATE_HAS_HISTORY]) -> {
                k = j + 1;
                do
                :: k < ROOT_USCXML_NUMBER_STATES -> {
                  /* add nested history to entry_set */
                  if
                  :: (ROOT_states[k].type[USCXML_STATE_HISTORY_DEEP] ||
                      ROOT_states[k].type[USCXML_STATE_HISTORY_SHALLOW]) &&
                     ROOT_states[j].children[k] -> {
                    /* a nested history state */
                    ROOT_ctx.entry_set[k] = true;
                  }
                  :: else -> skip;
                  fi
                  k = k + 1;
                }
                :: else -> break;
                od
              }
              :: else -> skip;
              fi
            }
            j = j + 1;
            :: else -> break;
            od
          }
          :: else -> skip;
          fi
        }
        fi;
      }
      :: ROOT_states[i].type[USCXML_STATE_INITIAL] -> {

#if TRACE_EXECUTION
printf("%d: Descendant completion for initial state %d\n", _pid, i);
#endif

        j = 0
        do
        :: j < ROOT_USCXML_NUMBER_TRANS -> {
          if
          :: ROOT_transitions[j].source == i -> {
            ROOT_ctx.trans_set[j] = true;
            ROOT_ctx.entry_set[i] = false;

#if TRACE_EXECUTION
printf("%d: Adding transition %d!\n", _pid, j);
#endif

            ROOT_STATES_OR(ROOT_ctx.entry_set, ROOT_transitions[j].target)

            k = i + 1;
            do
            :: k < ROOT_USCXML_NUMBER_STATES -> {
              if
              :: ROOT_transitions[j].target[k] -> {
                ROOT_STATES_OR(ROOT_ctx.entry_set, ROOT_states[k].ancestors)

              }
              :: else -> break;
              fi
              k = k + 1;
            }
            :: else -> break
            od
          }
          :: else -> skip;
          fi
          j = j + 1;
        }
        :: else -> break
        od;
      }
      :: ROOT_states[i].type[USCXML_STATE_COMPOUND] -> {
        /* we need to check whether one child is already in entry_set */
        if
        :: (
          !ROOT_STATES_HAS_AND(ROOT_ctx.entry_set, ROOT_states[i].children) && 
           (!ROOT_STATES_HAS_AND(ROOT_config, ROOT_states[i].children) || ROOT_STATES_HAS_AND(ROOT_ctx.exit_set, ROOT_states[i].children)
)) 
        -> {
          ROOT_STATES_OR(ROOT_ctx.entry_set, ROOT_states[i].completion)
          if
          :: (ROOT_STATES_HAS_AND(ROOT_states[i].completion, ROOT_states[i].children)
          ) -> {
            /* deep completion */
            j = i + 1;
            do
            :: j < ROOT_USCXML_NUMBER_STATES - 1 -> {
              j = j + 1;
              if
              :: ROOT_states[i].completion[j] -> {
                ROOT_STATES_OR(ROOT_ctx.entry_set, ROOT_states[j].ancestors)

                /* completion of compound is single state */
                break;
              } 
              :: else -> skip;
              fi
            }
            :: else -> break;
            od
          }
          :: else -> skip;
          fi
        }
        :: else -> skip;
        fi
      }
      :: else -> skip;
      fi;
    }
    :: else -> skip;
    fi;
    i = i + 1;
  }
  :: else -> break;
  od;


#if TRACE_EXECUTION
printf("Entry Set");
printf("%d%d%d%d", 
    ROOT_ctx.entry_set[0], 
    ROOT_ctx.entry_set[1], 
    ROOT_ctx.entry_set[2], 
    ROOT_ctx.entry_set[3]);
printf("\n");
#endif


/* ---------------------------- */
/* EXIT_STATES: */
  i = ROOT_USCXML_NUMBER_STATES;
  do
  :: i > 0 -> {
    i = i - 1;
    if
    :: ROOT_ctx.exit_set[i] && ROOT_config[i] -> {
      /* call all on-exit handlers */

#if TRACE_EXECUTION
printf("%d: Exiting state %d\n", _pid, i);
#endif

      if
      :: else -> skip;
      fi

      ROOT_config[i] = false;
      skip;
    }
    :: else -> skip;
    fi;
  }
  :: else -> break;
  od;


/* ---------------------------- */
/* TAKE_TRANSITIONS: */
  i = 0;
  do
  :: i < ROOT_USCXML_NUMBER_TRANS -> {
    if
    :: ROOT_ctx.trans_set[i] && 
       !ROOT_transitions[i].type[USCXML_TRANS_HISTORY] && 
       !ROOT_transitions[i].type[USCXML_TRANS_INITIAL] -> {
      /* Call executable content in normal transition */

#if TRACE_EXECUTION
printf("%d: Taking transition %d\n", _pid, i);
#endif

      if
      :: i == 0 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, i);
#endif

          ROOT_current_phil = ROOT__event.data.p_id;
          ROOT_left_fork = ROOT_current_phil;
          ROOT_right_fork = (ROOT_current_phil+1) % ROOT_NUM_OF_PHIL;
        if
        :: (ROOT_forks[ROOT_left_fork]==0 && ROOT_forks[ROOT_right_fork]==0) -> {
            ROOT_forks[ROOT_left_fork] = 1;
            ROOT_forks[ROOT_right_fork] = 1;
          if
          :: !ROOT_flags[USCXML_CTX_FINISHED] || ROOT_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
            {
              ROOT__tmpE.data.p_id = 0;
              ROOT__tmpE.delay = 0;
              ROOT__tmpE.invokeid = 0;
              ROOT__tmpE.name = 0;
              ROOT__tmpE.origin = 0;
              ROOT__tmpE.sendid = 0;
              ROOT__tmpE.seqNr = 0;
              ROOT__tmpE.name = TAKE_FORKS;
              ROOT__tmpE.origin = ROOT;
              _lastSeqId = _lastSeqId + 1;
              ROOT__tmpE.delay = 0;
              ROOT__tmpE.seqNr = _lastSeqId;
#if TRACE_EXECUTION
printf("%d: Sending TAKE_FORKS (%d) to ROOT_eQ\n", _pid, ROOT__tmpE.name );
#endif

              ROOT_eQ!ROOT__tmpE;
              insertWithDelay(ROOT_eQ);
            }
            skip;
          }
          :: else -> skip;
          fi
        }
        :: else -> {
          if
          :: (ROOT_forks[ROOT_left_fork]==1 || ROOT_forks[ROOT_right_fork]==1) -> {
            if
            :: !ROOT_flags[USCXML_CTX_FINISHED] || ROOT_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
              {
                ROOT__tmpE.data.p_id = 0;
                ROOT__tmpE.delay = 0;
                ROOT__tmpE.invokeid = 0;
                ROOT__tmpE.name = 0;
                ROOT__tmpE.origin = 0;
                ROOT__tmpE.sendid = 0;
                ROOT__tmpE.seqNr = 0;
                ROOT__tmpE.name = RESOURCE_DENIED;
                ROOT__tmpE.origin = ROOT;
                _lastSeqId = _lastSeqId + 1;
                ROOT__tmpE.delay = 0;
                ROOT__tmpE.seqNr = _lastSeqId;
#if TRACE_EXECUTION
printf("%d: Sending RESOURCE_DENIED (%d) to ROOT_eQ\n", _pid, ROOT__tmpE.name );
#endif

                ROOT_eQ!ROOT__tmpE;
                insertWithDelay(ROOT_eQ);
              }
              skip;
            }
            :: else -> skip;
            fi
          }
          :: else -> skip;
          fi;
        }
        fi;
        skip;
      }
      :: i == 1 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, i);
#endif

          ROOT_current_phil = ROOT__event.data.p_id;
          ROOT_left_fork = ROOT_current_phil;
          ROOT_right_fork = (ROOT_current_phil+1) % ROOT_NUM_OF_PHIL;
          ROOT_forks[ROOT_left_fork] = 0;
          ROOT_forks[ROOT_right_fork] = 0;
        skip;
      }
      :: i == 2 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, i);
#endif

        skip;
      }
      :: else ->skip;
      fi

    }
    :: else -> skip;
    fi;
    i = i + 1;
  }
  :: else -> break;
  od;

/* ---------------------------- */
/* ENTER_STATES: */
  i = 0;
  do
  :: i < ROOT_USCXML_NUMBER_STATES -> {
    if
    :: (ROOT_ctx.entry_set[i] &&
        !ROOT_config[i] && 
        /* these are no proper states */
        !ROOT_states[i].type[USCXML_STATE_HISTORY_DEEP] && 
        !ROOT_states[i].type[USCXML_STATE_HISTORY_SHALLOW] && 
        !ROOT_states[i].type[USCXML_STATE_INITIAL]
       ) -> {

#if TRACE_EXECUTION
printf("%d: Entering state %d\n", _pid, i);
#endif

         ROOT_config[i] = true;

         /* Process executable content for entering a state */
         if
         :: i == 3 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for entering state %d\n", _pid, i);
#endif

          printf("Outcome: %d", FAIL);
         }
         :: else ->skip;
         fi

         /* take history and initial transitions */
         j = 0;
         do
         :: j < ROOT_USCXML_NUMBER_TRANS -> {
           if
           :: (ROOT_ctx.trans_set[j] &&
              (ROOT_transitions[j].type[USCXML_TRANS_HISTORY] ||
               ROOT_transitions[j].type[USCXML_TRANS_INITIAL]) && 
               ROOT_states[ROOT_transitions[j].source].parent == i) -> {
              /* Call executable content in history or initial transition */
              if
              :: j == 0 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, j);
#endif

                  ROOT_current_phil = ROOT__event.data.p_id;
                  ROOT_left_fork = ROOT_current_phil;
                  ROOT_right_fork = (ROOT_current_phil+1) % ROOT_NUM_OF_PHIL;
                if
                :: (ROOT_forks[ROOT_left_fork]==0 && ROOT_forks[ROOT_right_fork]==0) -> {
                    ROOT_forks[ROOT_left_fork] = 1;
                    ROOT_forks[ROOT_right_fork] = 1;
                  if
                  :: !ROOT_flags[USCXML_CTX_FINISHED] || ROOT_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
                    {
                      ROOT__tmpE.data.p_id = 0;
                      ROOT__tmpE.delay = 0;
                      ROOT__tmpE.invokeid = 0;
                      ROOT__tmpE.name = 0;
                      ROOT__tmpE.origin = 0;
                      ROOT__tmpE.sendid = 0;
                      ROOT__tmpE.seqNr = 0;
                      ROOT__tmpE.name = TAKE_FORKS;
                      ROOT__tmpE.origin = ROOT;
                      _lastSeqId = _lastSeqId + 1;
                      ROOT__tmpE.delay = 0;
                      ROOT__tmpE.seqNr = _lastSeqId;
#if TRACE_EXECUTION
printf("%d: Sending TAKE_FORKS (%d) to ROOT_eQ\n", _pid, ROOT__tmpE.name );
#endif

                      ROOT_eQ!ROOT__tmpE;
                      insertWithDelay(ROOT_eQ);
                    }
                    skip;
                  }
                  :: else -> skip;
                  fi
                }
                :: else -> {
                  if
                  :: (ROOT_forks[ROOT_left_fork]==1 || ROOT_forks[ROOT_right_fork]==1) -> {
                    if
                    :: !ROOT_flags[USCXML_CTX_FINISHED] || ROOT_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
                      {
                        ROOT__tmpE.data.p_id = 0;
                        ROOT__tmpE.delay = 0;
                        ROOT__tmpE.invokeid = 0;
                        ROOT__tmpE.name = 0;
                        ROOT__tmpE.origin = 0;
                        ROOT__tmpE.sendid = 0;
                        ROOT__tmpE.seqNr = 0;
                        ROOT__tmpE.name = RESOURCE_DENIED;
                        ROOT__tmpE.origin = ROOT;
                        _lastSeqId = _lastSeqId + 1;
                        ROOT__tmpE.delay = 0;
                        ROOT__tmpE.seqNr = _lastSeqId;
#if TRACE_EXECUTION
printf("%d: Sending RESOURCE_DENIED (%d) to ROOT_eQ\n", _pid, ROOT__tmpE.name );
#endif

                        ROOT_eQ!ROOT__tmpE;
                        insertWithDelay(ROOT_eQ);
                      }
                      skip;
                    }
                    :: else -> skip;
                    fi
                  }
                  :: else -> skip;
                  fi;
                }
                fi;
                skip;
              }
              :: j == 1 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, j);
#endif

                  ROOT_current_phil = ROOT__event.data.p_id;
                  ROOT_left_fork = ROOT_current_phil;
                  ROOT_right_fork = (ROOT_current_phil+1) % ROOT_NUM_OF_PHIL;
                  ROOT_forks[ROOT_left_fork] = 0;
                  ROOT_forks[ROOT_right_fork] = 0;
                skip;
              }
              :: j == 2 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, j);
#endif

                skip;
              }
              :: else ->skip;
              fi

           }
           :: else -> skip;
           fi
           j = j + 1;
         }
         :: else -> break;
         od
         /* handle final states */
         if
         :: ROOT_states[i].type[USCXML_STATE_FINAL] -> {
           if
           :: ROOT_states[ROOT_states[i].parent].children[1] -> {
             /* exit topmost SCXML state */
             ROOT_flags[USCXML_CTX_TOP_LEVEL_FINAL] = true;
             ROOT_flags[USCXML_CTX_FINISHED] = true;
           }
           :: else -> {
             /* raise done event */
             if
             :: else -> skip;
             fi
           }
           fi
           /**
            * are we the last final state to leave a parallel state?:
            * 1. Gather all parallel states in our ancestor chain
            * 2. Find all states for which these parallels are ancestors
            * 3. Iterate all active final states and remove their ancestors
            * 4. If a state remains, not all children of a parallel are final
            */
            j = 0;
            do
            :: j < ROOT_USCXML_NUMBER_STATES -> {
              if
              :: ROOT_states[j].type[USCXML_STATE_PARALLEL] && ROOT_states[i].ancestors[j] -> {
                ROOT_STATES_CLEAR(ROOT_ctx.tmp_states)
                k = 0;
                do
                :: k < ROOT_USCXML_NUMBER_STATES -> {
                  if
                  :: ROOT_states[k].ancestors[j] && ROOT_config[k] -> {
                    if
                    :: ROOT_states[k].type[USCXML_STATE_FINAL] -> {
                      ROOT_STATES_AND_NOT(ROOT_ctx.tmp_states, ROOT_states[k].ancestors)
                    }
                    :: else -> {
                      ROOT_ctx.tmp_states[k] = true;
                    }
                    fi
                  }
                  :: else -> skip;
                  fi
                  k = k + 1;
                }
                :: else -> break;
                od
                if
                :: !ROOT_STATES_HAS_ANY(ROOT_ctx.tmp_states) -> {
                  if
                  :: else -> skip;
                  fi
                }
                :: else -> skip;
                fi
              }
              :: else -> skip;
              fi
              j = j + 1;
            }
            :: else -> break;
            od
         }
         :: else -> skip;
         fi

    }
    :: else -> skip;
    i = i + 1;
    fi;
  }
  :: else -> break;
  od;

  }
  :: else -> skip;
  fi /* USCXML_CTX_TRANSITION_FOUND */
  } skip; /* d_step */
} /* !USCXML_CTX_FINISHED */
:: else -> break;
od

/* ---------------------------- */
ROOT_TERMINATE_MACHINE:
skip; d_step {

#if TRACE_EXECUTION
printf("%d: Machine finished\n", _pid);
#endif

/* exit all remaining states */
i = ROOT_USCXML_NUMBER_STATES;
do
:: i > 0 -> {
  i = i - 1;
  if
  :: ROOT_config[i] && ROOT_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
    /* call all on exit handlers */
   if
    :: else -> skip;
    fi

    skip;
    
  }
  :: else -> skip;
  fi;

  if
  :: ROOT_invocations[i] -> {
    /* cancel invocations */
    ROOT_invocations[i] = false;
    if
    :: i == 1 -> {
      INV_F5426_flags[USCXML_CTX_FINISHED] = true;
    }
    :: i == 1 -> {
      INV_8CB85_flags[USCXML_CTX_FINISHED] = true;
    }
    :: i == 1 -> {
      INV_5C805_flags[USCXML_CTX_FINISHED] = true;
    }
    :: i == 1 -> {
      INV_F88AA_flags[USCXML_CTX_FINISHED] = true;
    }
    :: i == 1 -> {
      INV_41D63_flags[USCXML_CTX_FINISHED] = true;
    }
    :: else -> skip;
    fi
    skip;

  }
  :: else -> skip;
  fi;
}
:: else -> break;
od;


#if TRACE_EXECUTION
printf("%d: Removing pending events\n", _pid);
#endif

removePendingEventsFromInvoker(ROOT)
} /* d_step */


#if TRACE_EXECUTION
printf("%d: Done\n", _pid);
#endif

} } /* atomic, step() */


/* machine microstep function */
#define INV_F5426_USCXML_NUMBER_STATES 7
#define INV_F5426_USCXML_NUMBER_TRANS 7

proctype INV_F5426_step() { atomic {

INV_F5426_procid = _pid;
unsigned i : 3,  j : 3,  k : 3;


/* ---------------------------- */
INV_F5426_MICROSTEP:
do
:: !INV_F5426_flags[USCXML_CTX_FINISHED] -> {
  /* Run until machine is finished */


#if TRACE_EXECUTION
printf("%d: Taking a step\n", _pid);
#endif

  /* Dequeue an event */
  INV_F5426_flags[USCXML_CTX_DEQUEUE_EXTERNAL] = false;
  if
  ::INV_F5426_flags[USCXML_CTX_SPONTANEOUS] -> {
    INV_F5426__event.name = USCXML_EVENT_SPONTANEOUS;

#if TRACE_EXECUTION
printf("%d: Trying with a spontaneous event\n", _pid);
#endif

  }
  :: else -> {
    if
    :: len(INV_F5426_iQ) != 0 -> {
      INV_F5426_iQ ? INV_F5426__event;

#if TRACE_EXECUTION
printf("%d: Deqeued an internal event\n", _pid);
#endif

    }
    :: else -> {
      INV_F5426_flags[USCXML_CTX_DEQUEUE_EXTERNAL] = true;
    }
    fi;
  }
  fi;


  if
  :: INV_F5426_flags[USCXML_CTX_DEQUEUE_EXTERNAL] -> {
    /* manage invocations */
    i = 0;
    do
    :: i < INV_F5426_USCXML_NUMBER_STATES -> {
      d_step { 
      /* uninvoke */
      if
      :: !INV_F5426_config[i] && INV_F5426_invocations[i] -> {

#if TRACE_EXECUTION
printf("%d: Uninvoking in state %d\n", _pid, i);
#endif

        if
        :: else -> skip;
        fi
        INV_F5426_invocations[i] = false;
        skip;
      }
      :: else -> skip;
      fi;
      } /* d_step */

      /* invoke */
      if
      :: INV_F5426_config[i] && !INV_F5426_invocations[i] -> {
        if
        :: else -> skip;
        fi
      }
      :: else -> skip;
      fi;
      i = i + 1;
    }
    :: else -> break;
    od;

    /* Determine machines with smallest delay and set their process priority */
    scheduleMachines();

    /* we may return to find ourselves terminated */
    if
    :: INV_F5426_flags[USCXML_CTX_FINISHED] -> {
      goto INV_F5426_TERMINATE_MACHINE;
    }
    :: else -> skip;
    fi
    /* Not sure if this should be before the invocation due to auto-forwarding */
    if
    :: len(INV_F5426_eQ) != 0 -> {
      INV_F5426_eQ ? INV_F5426__event;

#if TRACE_EXECUTION
printf("%d: Deqeued an external event\n", _pid);
#endif

    }
    fi;
  }
  :: else -> skip;
  fi


d_step { skip;

/* ---------------------------- */
INV_F5426_SELECT_TRANSITIONS:
INV_F5426_STATES_CLEAR(INV_F5426_ctx.target_set)
INV_F5426_STATES_CLEAR(INV_F5426_ctx.exit_set)
INV_F5426_TRANS_CLEAR(INV_F5426_ctx.conflicts)
INV_F5426_TRANS_CLEAR(INV_F5426_ctx.trans_set)
#if TRACE_EXECUTION
printf("%d: Establishing optimal transition set for event %d\n", _pid, INV_F5426__event.name );
#endif

#if TRACE_EXECUTION
printf("Configuration: ");
printf("%d%d%d%d%d%d%d", 
    INV_F5426_config[0], 
    INV_F5426_config[1], 
    INV_F5426_config[2], 
    INV_F5426_config[3], 
    INV_F5426_config[4], 
    INV_F5426_config[5], 
    INV_F5426_config[6]);
printf("\n");
#endif

  INV_F5426_flags[USCXML_CTX_TRANSITION_FOUND] = false;
  i = 0;
  do
  :: i < INV_F5426_USCXML_NUMBER_TRANS -> {
    /* only select non-history, non-initial transitions */
    if
    :: !INV_F5426_transitions[i].type[USCXML_TRANS_HISTORY] &&
       !INV_F5426_transitions[i].type[USCXML_TRANS_INITIAL] -> {
      if
      :: /* is the transition active? */
         INV_F5426_config[INV_F5426_transitions[i].source] && 

         /* is it non-conflicting? */
         !INV_F5426_ctx.conflicts[i] && 

         /* is it spontaneous with an event or vice versa? */
         ((INV_F5426__event.name == USCXML_EVENT_SPONTANEOUS && 
           INV_F5426_transitions[i].type[USCXML_TRANS_SPONTANEOUS]) || 
          (INV_F5426__event.name != USCXML_EVENT_SPONTANEOUS && 
           !INV_F5426_transitions[i].type[USCXML_TRANS_SPONTANEOUS])) &&

         /* is it matching and enabled? */
         (false 
          || (i == 0 && (false || INV_F5426__event.name == THINKING_OVER))
          || (i == 1 && (false || INV_F5426__event.name == TAKE_FORKS))
          || (i == 2 && (false || INV_F5426__event.name == RESOURCE_DENIED))
          || (i == 3 && (false || INV_F5426__event.name == EATING_OVER))
          || (i == 4 && (false || INV_F5426__event.name == TAKE_FORKS))
          || (i == 5 && (false || INV_F5426__event.name == RESEND_NEED_FORKS))
          || (i == 6 && (false || INV_F5426__event.name == TIMEOUT))
         ) -> {
        /* remember that we found a transition */
        INV_F5426_flags[USCXML_CTX_TRANSITION_FOUND] = true;

        /* transitions that are pre-empted */
        INV_F5426_TRANS_OR(INV_F5426_ctx.conflicts, INV_F5426_transitions[i].conflicts)

        /* states that are directly targeted (resolve as entry-set later) */
        INV_F5426_STATES_OR(INV_F5426_ctx.target_set, INV_F5426_transitions[i].target)

        /* states that will be left */
        INV_F5426_STATES_OR(INV_F5426_ctx.exit_set, INV_F5426_transitions[i].exit_set)

        INV_F5426_ctx.trans_set[i] = true;
      }
      :: else {
        skip;
      }
      fi
    }
    :: else -> {
      skip;
    }
    fi
    i = i + 1;
  }
  :: else -> break;
  od;
  INV_F5426_STATES_AND(INV_F5426_ctx.exit_set, INV_F5426_config)

#if TRACE_EXECUTION
printf("Selected Transitions: ");
printf("%d%d%d%d%d%d%d", 
    INV_F5426_ctx.trans_set[0], 
    INV_F5426_ctx.trans_set[1], 
    INV_F5426_ctx.trans_set[2], 
    INV_F5426_ctx.trans_set[3], 
    INV_F5426_ctx.trans_set[4], 
    INV_F5426_ctx.trans_set[5], 
    INV_F5426_ctx.trans_set[6]);
printf("\n");
#endif


#if TRACE_EXECUTION
printf("Target Set: ");
printf("%d%d%d%d%d%d%d", 
    INV_F5426_ctx.target_set[0], 
    INV_F5426_ctx.target_set[1], 
    INV_F5426_ctx.target_set[2], 
    INV_F5426_ctx.target_set[3], 
    INV_F5426_ctx.target_set[4], 
    INV_F5426_ctx.target_set[5], 
    INV_F5426_ctx.target_set[6]);
printf("\n");
#endif


#if TRACE_EXECUTION
printf("Exit Set: ");
printf("%d%d%d%d%d%d%d", 
    INV_F5426_ctx.exit_set[0], 
    INV_F5426_ctx.exit_set[1], 
    INV_F5426_ctx.exit_set[2], 
    INV_F5426_ctx.exit_set[3], 
    INV_F5426_ctx.exit_set[4], 
    INV_F5426_ctx.exit_set[5], 
    INV_F5426_ctx.exit_set[6]);
printf("\n");
#endif

  if
  :: !INV_F5426_STATES_HAS_ANY(INV_F5426_config) -> {
    /* Enter initial configuration */
    INV_F5426_STATES_COPY(INV_F5426_ctx.target_set, INV_F5426_states[0].completion)
    INV_F5426_flags[USCXML_CTX_SPONTANEOUS] = true;
    INV_F5426_flags[USCXML_CTX_TRANSITION_FOUND] = true;

#if TRACE_EXECUTION
printf("%d: Entering initial default completion\n", _pid);
#endif


  }
  :: INV_F5426_flags[USCXML_CTX_TRANSITION_FOUND] -> {

#if TRACE_EXECUTION
printf("%d: Found transitions\n", _pid);
#endif

    INV_F5426_flags[USCXML_CTX_SPONTANEOUS] = true;
  }
  :: else {
    INV_F5426_flags[USCXML_CTX_SPONTANEOUS] = false;

#if TRACE_EXECUTION
printf("%d: Found NO transitions\n", _pid);
#endif

  }
  fi


  if
  :: INV_F5426_flags[USCXML_CTX_TRANSITION_FOUND] -> {
    /* only process anything if we found transitions or are on initial entry */
/* ---------------------------- */
/* REMEMBER_HISTORY: */

#if TRACE_EXECUTION
printf("%d: Save history configurations\n", _pid);
#endif

  if
  :: INV_F5426_STATES_HAS_ANY(INV_F5426_config) -> {
    /* only remember history on non-initial entry */
    i = 0;
    do
    :: i < INV_F5426_USCXML_NUMBER_STATES -> {
      if
      :: INV_F5426_states[i].type[USCXML_STATE_HISTORY_SHALLOW] ||
         INV_F5426_states[i].type[USCXML_STATE_HISTORY_DEEP] -> {
        if
        :: INV_F5426_ctx.exit_set[INV_F5426_states[i].parent] -> {
          /* a history state whose parent is about to be exited */

#if TRACE_EXECUTION
printf("%d: history state %d is about to be exited\n", _pid, i);
#endif


#if TRACE_EXECUTION
printf("COMPLET: ");
printf("%d%d%d%d%d%d%d", 
    INV_F5426_states[i].completion[0], 
    INV_F5426_states[i].completion[1], 
    INV_F5426_states[i].completion[2], 
    INV_F5426_states[i].completion[3], 
    INV_F5426_states[i].completion[4], 
    INV_F5426_states[i].completion[5], 
    INV_F5426_states[i].completion[6]);
printf("\n");
#endif

          INV_F5426_STATES_COPY(INV_F5426_ctx.tmp_states, INV_F5426_states[i].completion)

          /* set those states who were enabled */
          INV_F5426_STATES_AND(INV_F5426_ctx.tmp_states, INV_F5426_config)

#if TRACE_EXECUTION
printf("CONFIG : ");
printf("%d%d%d%d%d%d%d", 
    INV_F5426_config[0], 
    INV_F5426_config[1], 
    INV_F5426_config[2], 
    INV_F5426_config[3], 
    INV_F5426_config[4], 
    INV_F5426_config[5], 
    INV_F5426_config[6]);
printf("\n");
#endif


#if TRACE_EXECUTION
printf("TMP_STS: ");
printf("%d%d%d%d%d%d%d", 
    INV_F5426_ctx.tmp_states[0], 
    INV_F5426_ctx.tmp_states[1], 
    INV_F5426_ctx.tmp_states[2], 
    INV_F5426_ctx.tmp_states[3], 
    INV_F5426_ctx.tmp_states[4], 
    INV_F5426_ctx.tmp_states[5], 
    INV_F5426_ctx.tmp_states[6]);
printf("\n");
#endif


          /* clear current history with completion mask */
          INV_F5426_STATES_AND_NOT(INV_F5426_history, INV_F5426_states[i].completion)

          /* set history */
          INV_F5426_STATES_OR(INV_F5426_history, INV_F5426_ctx.tmp_states)

        }
        :: else -> skip;
        fi;
      }
      :: else -> skip;
      fi;
      i = i + 1;
    }
    :: else -> break;
    od;


#if TRACE_EXECUTION
printf("History: ");
printf("%d%d%d%d%d%d%d", 
    INV_F5426_history[0], 
    INV_F5426_history[1], 
    INV_F5426_history[2], 
    INV_F5426_history[3], 
    INV_F5426_history[4], 
    INV_F5426_history[5], 
    INV_F5426_history[6]);
printf("\n");
#endif
  }
  :: else -> skip;
  fi;

/* ---------------------------- */
INV_F5426_ESTABLISH_ENTRY_SET:
  /* calculate new entry set */
  INV_F5426_STATES_COPY(INV_F5426_ctx.entry_set, INV_F5426_ctx.target_set)

  i = 0;
  do
  :: i < INV_F5426_USCXML_NUMBER_STATES -> {
    if
    :: INV_F5426_ctx.entry_set[i] -> {
      /* ancestor completion */
      INV_F5426_STATES_OR(INV_F5426_ctx.entry_set, INV_F5426_states[i].ancestors)
    }
    :: else -> skip;
    fi;
    i = i + 1;
  }
  :: else -> break;
  od;

  /* iterate for descendants */
  i = 0;
  do
  :: i < INV_F5426_USCXML_NUMBER_STATES -> {
    if
    :: INV_F5426_ctx.entry_set[i] -> {
      if
      :: INV_F5426_states[i].type[USCXML_STATE_PARALLEL] -> {
        INV_F5426_STATES_OR(INV_F5426_ctx.entry_set, INV_F5426_states[i].completion)
      }
      :: INV_F5426_states[i].type[USCXML_STATE_HISTORY_SHALLOW] ||
         INV_F5426_states[i].type[USCXML_STATE_HISTORY_DEEP] -> {

#if TRACE_EXECUTION
printf("%d: Descendant completion for history state %d\n", _pid, i);
#endif

        if
        :: !INV_F5426_STATES_HAS_AND(INV_F5426_states[i].completion, INV_F5426_history) && !INV_F5426_config[INV_F5426_states[i].parent] -> {
          /* nothing set for history, look for a default transition */

#if TRACE_EXECUTION
printf("%d: Fresh history in target set\n", _pid);
#endif

          j = 0;
          do
          :: j < INV_F5426_USCXML_NUMBER_TRANS -> {
             if
             :: INV_F5426_transitions[j].source == i -> {
               INV_F5426_ctx.trans_set[j] = true;
               INV_F5426_STATES_OR(INV_F5426_ctx.entry_set, INV_F5426_transitions[j].target)

               if
               :: (INV_F5426_states[i].type[USCXML_STATE_HISTORY_DEEP] &&
                   !INV_F5426_STATES_HAS_AND(INV_F5426_transitions[j].target, INV_F5426_states[i].children)                  ) -> {
                 k = i + 1
                 do
                 :: k < INV_F5426_USCXML_NUMBER_STATES -> {
                   if
                   :: INV_F5426_transitions[j].target[k] -> {
                     INV_F5426_STATES_OR(INV_F5426_ctx.entry_set, INV_F5426_states[k].ancestors)
                     break;

                   }
                   :: else -> skip;
                   fi
                   k = k + 1;
                 }
                 :: else -> break;
                 od
               }
               :: else -> skip;
               fi
               break;
             }
             :: else -> skip;
             fi
             j = j + 1;
          }
          :: else -> break
          od
          skip;
        }
        :: else -> {

#if TRACE_EXECUTION
printf("%d: Established history in target set\n", _pid);
#endif

          INV_F5426_STATES_COPY(INV_F5426_ctx.tmp_states, INV_F5426_states[i].completion)
          INV_F5426_STATES_AND(INV_F5426_ctx.tmp_states, INV_F5426_history)
          INV_F5426_STATES_OR(INV_F5426_ctx.entry_set, INV_F5426_ctx.tmp_states)
          if
          :: INV_F5426_states[i].type[USCXML_STATE_HAS_HISTORY] ||
             INV_F5426_states[i].type[USCXML_STATE_HISTORY_DEEP] -> { 
            /* a deep history state with nested histories -> more completion */

#if TRACE_EXECUTION
printf("%d: DEEP HISTORY\n", _pid);
#endif

            j = i + 1;
            do
            :: j < INV_F5426_USCXML_NUMBER_STATES -> {
              if
              :: (INV_F5426_states[i].completion[j] &&
                  INV_F5426_ctx.entry_set[j] && 
                  INV_F5426_states[j].type[USCXML_STATE_HAS_HISTORY]) -> {
                k = j + 1;
                do
                :: k < INV_F5426_USCXML_NUMBER_STATES -> {
                  /* add nested history to entry_set */
                  if
                  :: (INV_F5426_states[k].type[USCXML_STATE_HISTORY_DEEP] ||
                      INV_F5426_states[k].type[USCXML_STATE_HISTORY_SHALLOW]) &&
                     INV_F5426_states[j].children[k] -> {
                    /* a nested history state */
                    INV_F5426_ctx.entry_set[k] = true;
                  }
                  :: else -> skip;
                  fi
                  k = k + 1;
                }
                :: else -> break;
                od
              }
              :: else -> skip;
              fi
            }
            j = j + 1;
            :: else -> break;
            od
          }
          :: else -> skip;
          fi
        }
        fi;
      }
      :: INV_F5426_states[i].type[USCXML_STATE_INITIAL] -> {

#if TRACE_EXECUTION
printf("%d: Descendant completion for initial state %d\n", _pid, i);
#endif

        j = 0
        do
        :: j < INV_F5426_USCXML_NUMBER_TRANS -> {
          if
          :: INV_F5426_transitions[j].source == i -> {
            INV_F5426_ctx.trans_set[j] = true;
            INV_F5426_ctx.entry_set[i] = false;

#if TRACE_EXECUTION
printf("%d: Adding transition %d!\n", _pid, j);
#endif

            INV_F5426_STATES_OR(INV_F5426_ctx.entry_set, INV_F5426_transitions[j].target)

            k = i + 1;
            do
            :: k < INV_F5426_USCXML_NUMBER_STATES -> {
              if
              :: INV_F5426_transitions[j].target[k] -> {
                INV_F5426_STATES_OR(INV_F5426_ctx.entry_set, INV_F5426_states[k].ancestors)

              }
              :: else -> break;
              fi
              k = k + 1;
            }
            :: else -> break
            od
          }
          :: else -> skip;
          fi
          j = j + 1;
        }
        :: else -> break
        od;
      }
      :: INV_F5426_states[i].type[USCXML_STATE_COMPOUND] -> {
        /* we need to check whether one child is already in entry_set */
        if
        :: (
          !INV_F5426_STATES_HAS_AND(INV_F5426_ctx.entry_set, INV_F5426_states[i].children) && 
           (!INV_F5426_STATES_HAS_AND(INV_F5426_config, INV_F5426_states[i].children) || INV_F5426_STATES_HAS_AND(INV_F5426_ctx.exit_set, INV_F5426_states[i].children)
)) 
        -> {
          INV_F5426_STATES_OR(INV_F5426_ctx.entry_set, INV_F5426_states[i].completion)
          if
          :: (INV_F5426_STATES_HAS_AND(INV_F5426_states[i].completion, INV_F5426_states[i].children)
          ) -> {
            /* deep completion */
            j = i + 1;
            do
            :: j < INV_F5426_USCXML_NUMBER_STATES - 1 -> {
              j = j + 1;
              if
              :: INV_F5426_states[i].completion[j] -> {
                INV_F5426_STATES_OR(INV_F5426_ctx.entry_set, INV_F5426_states[j].ancestors)

                /* completion of compound is single state */
                break;
              } 
              :: else -> skip;
              fi
            }
            :: else -> break;
            od
          }
          :: else -> skip;
          fi
        }
        :: else -> skip;
        fi
      }
      :: else -> skip;
      fi;
    }
    :: else -> skip;
    fi;
    i = i + 1;
  }
  :: else -> break;
  od;


#if TRACE_EXECUTION
printf("Entry Set");
printf("%d%d%d%d%d%d%d", 
    INV_F5426_ctx.entry_set[0], 
    INV_F5426_ctx.entry_set[1], 
    INV_F5426_ctx.entry_set[2], 
    INV_F5426_ctx.entry_set[3], 
    INV_F5426_ctx.entry_set[4], 
    INV_F5426_ctx.entry_set[5], 
    INV_F5426_ctx.entry_set[6]);
printf("\n");
#endif


/* ---------------------------- */
/* EXIT_STATES: */
  i = INV_F5426_USCXML_NUMBER_STATES;
  do
  :: i > 0 -> {
    i = i - 1;
    if
    :: INV_F5426_ctx.exit_set[i] && INV_F5426_config[i] -> {
      /* call all on-exit handlers */

#if TRACE_EXECUTION
printf("%d: Exiting state %d\n", _pid, i);
#endif

      if
      :: i == 5 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for exiting state %d\n", _pid, i);
#endif

      if
      :: (INV_F5426__event.name == TAKE_FORKS) -> {
          cancelSendId(RESOURCE_DENIED_TIMER,INV_F5426);
      }
      :: else -> skip;
      fi;
      }
      :: else -> skip;
      fi

      INV_F5426_config[i] = false;
      skip;
    }
    :: else -> skip;
    fi;
  }
  :: else -> break;
  od;


/* ---------------------------- */
/* TAKE_TRANSITIONS: */
  i = 0;
  do
  :: i < INV_F5426_USCXML_NUMBER_TRANS -> {
    if
    :: INV_F5426_ctx.trans_set[i] && 
       !INV_F5426_transitions[i].type[USCXML_TRANS_HISTORY] && 
       !INV_F5426_transitions[i].type[USCXML_TRANS_INITIAL] -> {
      /* Call executable content in normal transition */

#if TRACE_EXECUTION
printf("%d: Taking transition %d\n", _pid, i);
#endif

      if
      :: i == 0 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, i);
#endif

        skip;
      }
      :: i == 1 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, i);
#endif

        skip;
      }
      :: i == 2 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, i);
#endif

        skip;
      }
      :: i == 3 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, i);
#endif

        if
        :: !INV_F5426_flags[USCXML_CTX_FINISHED] || INV_F5426_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
          {
            INV_F5426__tmpE.data.p_id = 0;
            INV_F5426__tmpE.delay = 0;
            INV_F5426__tmpE.invokeid = 0;
            INV_F5426__tmpE.name = 0;
            INV_F5426__tmpE.origin = 0;
            INV_F5426__tmpE.sendid = 0;
            INV_F5426__tmpE.seqNr = 0;
            INV_F5426__tmpE.name = RETURN_FORKS;
            INV_F5426__tmpE.invokeid = INV_F5426;
            INV_F5426__tmpE.origin = INV_F5426;
            _lastSeqId = _lastSeqId + 1;
            INV_F5426__tmpE.delay = 0;
            INV_F5426__tmpE.seqNr = _lastSeqId;
            INV_F5426__tmpE.data.p_id = INV_F5426_p_id;
#if TRACE_EXECUTION
printf("%d: Sending RETURN_FORKS (%d) to ROOT_eQ\n", _pid, INV_F5426__tmpE.name );
#endif

            ROOT_eQ!INV_F5426__tmpE;
            insertWithDelay(ROOT_eQ);
          }
          skip;
        }
        :: else -> skip;
        fi
        skip;
      }
      :: i == 4 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, i);
#endif

        skip;
      }
      :: i == 5 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, i);
#endif

        if
        :: !INV_F5426_flags[USCXML_CTX_FINISHED] || INV_F5426_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
          {
            INV_F5426__tmpE.data.p_id = 0;
            INV_F5426__tmpE.delay = 0;
            INV_F5426__tmpE.invokeid = 0;
            INV_F5426__tmpE.name = 0;
            INV_F5426__tmpE.origin = 0;
            INV_F5426__tmpE.sendid = 0;
            INV_F5426__tmpE.seqNr = 0;
            INV_F5426__tmpE.name = NEED_FORKS;
            INV_F5426__tmpE.invokeid = INV_F5426;
            INV_F5426__tmpE.origin = INV_F5426;
            _lastSeqId = _lastSeqId + 1;
            INV_F5426__tmpE.delay = 0;
            INV_F5426__tmpE.seqNr = _lastSeqId;
            INV_F5426__tmpE.data.p_id = INV_F5426_p_id;
#if TRACE_EXECUTION
printf("%d: Sending NEED_FORKS (%d) to ROOT_eQ\n", _pid, INV_F5426__tmpE.name );
#endif

            ROOT_eQ!INV_F5426__tmpE;
            insertWithDelay(ROOT_eQ);
          }
          skip;
        }
        :: else -> skip;
        fi
        skip;
      }
      :: i == 6 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, i);
#endif

        printf("philospher: : %d", INV_F5426_p_id);
        printf("Time(in ms) since resource denied: : %d", INV_F5426_delay);
        skip;
      }
      :: else ->skip;
      fi

    }
    :: else -> skip;
    fi;
    i = i + 1;
  }
  :: else -> break;
  od;

/* ---------------------------- */
/* ENTER_STATES: */
  i = 0;
  do
  :: i < INV_F5426_USCXML_NUMBER_STATES -> {
    if
    :: (INV_F5426_ctx.entry_set[i] &&
        !INV_F5426_config[i] && 
        /* these are no proper states */
        !INV_F5426_states[i].type[USCXML_STATE_HISTORY_DEEP] && 
        !INV_F5426_states[i].type[USCXML_STATE_HISTORY_SHALLOW] && 
        !INV_F5426_states[i].type[USCXML_STATE_INITIAL]
       ) -> {

#if TRACE_EXECUTION
printf("%d: Entering state %d\n", _pid, i);
#endif

         INV_F5426_config[i] = true;

         /* Process executable content for entering a state */
         if
         :: i == 1 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for entering state %d\n", _pid, i);
#endif

          printf("Hello, I am philospher number: : %d", INV_F5426_p_id);
         }
         :: i == 2 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for entering state %d\n", _pid, i);
#endif

          printf("Thinking professor: : %d", INV_F5426_p_id);
            INV_F5426_random_delay = ((1103515245*INV_F5426_random_delay+12345)%2147483647)%2000;
          if
          :: !INV_F5426_flags[USCXML_CTX_FINISHED] || INV_F5426_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
            {
              INV_F5426__tmpE.data.p_id = 0;
              INV_F5426__tmpE.delay = 0;
              INV_F5426__tmpE.invokeid = 0;
              INV_F5426__tmpE.name = 0;
              INV_F5426__tmpE.origin = 0;
              INV_F5426__tmpE.sendid = 0;
              INV_F5426__tmpE.seqNr = 0;
              INV_F5426__tmpE.name = THINKING_OVER;
              INV_F5426__tmpE.invokeid = INV_F5426;
              INV_F5426__tmpE.origin = INV_F5426;
              _lastSeqId = _lastSeqId + 1;
              INV_F5426__tmpE.delay = INV_F5426_random_delay*(INV_F5426_p_id+1);
              INV_F5426__tmpE.seqNr = _lastSeqId;
#if TRACE_EXECUTION
printf("%d: Sending THINKING_OVER (%d) to INV_F5426_eQ\n", _pid, INV_F5426__tmpE.name );
#endif

              INV_F5426_eQ!INV_F5426__tmpE;
              insertWithDelay(INV_F5426_eQ);
            }
            skip;
          }
          :: else -> skip;
          fi
         }
         :: i == 3 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for entering state %d\n", _pid, i);
#endif

          printf("Hungry professor: : %d", INV_F5426_p_id);
          if
          :: !INV_F5426_flags[USCXML_CTX_FINISHED] || INV_F5426_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
            {
              INV_F5426__tmpE.data.p_id = 0;
              INV_F5426__tmpE.delay = 0;
              INV_F5426__tmpE.invokeid = 0;
              INV_F5426__tmpE.name = 0;
              INV_F5426__tmpE.origin = 0;
              INV_F5426__tmpE.sendid = 0;
              INV_F5426__tmpE.seqNr = 0;
              INV_F5426__tmpE.name = NEED_FORKS;
              INV_F5426__tmpE.invokeid = INV_F5426;
              INV_F5426__tmpE.origin = INV_F5426;
              _lastSeqId = _lastSeqId + 1;
              INV_F5426__tmpE.delay = 300;
              INV_F5426__tmpE.seqNr = _lastSeqId;
              INV_F5426__tmpE.data.p_id = INV_F5426_p_id;
#if TRACE_EXECUTION
printf("%d: Sending NEED_FORKS (%d) to ROOT_eQ\n", _pid, INV_F5426__tmpE.name );
#endif

              ROOT_eQ!INV_F5426__tmpE;
              insertWithDelay(ROOT_eQ);
            }
            skip;
          }
          :: else -> skip;
          fi
         }
         :: i == 4 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for entering state %d\n", _pid, i);
#endif

          printf("Eating professor: : %d", INV_F5426_p_id);
          if
          :: !INV_F5426_flags[USCXML_CTX_FINISHED] || INV_F5426_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
            {
              INV_F5426__tmpE.data.p_id = 0;
              INV_F5426__tmpE.delay = 0;
              INV_F5426__tmpE.invokeid = 0;
              INV_F5426__tmpE.name = 0;
              INV_F5426__tmpE.origin = 0;
              INV_F5426__tmpE.sendid = 0;
              INV_F5426__tmpE.seqNr = 0;
              INV_F5426__tmpE.name = EATING_OVER;
              INV_F5426__tmpE.invokeid = INV_F5426;
              INV_F5426__tmpE.origin = INV_F5426;
              _lastSeqId = _lastSeqId + 1;
              INV_F5426__tmpE.delay = 500;
              INV_F5426__tmpE.seqNr = _lastSeqId;
#if TRACE_EXECUTION
printf("%d: Sending EATING_OVER (%d) to INV_F5426_eQ\n", _pid, INV_F5426__tmpE.name );
#endif

              INV_F5426_eQ!INV_F5426__tmpE;
              insertWithDelay(INV_F5426_eQ);
            }
            skip;
          }
          :: else -> skip;
          fi
         }
         :: i == 5 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for entering state %d\n", _pid, i);
#endif

          printf("Resource Denied professor: : %d", INV_F5426_p_id);
          if
          :: !INV_F5426_flags[USCXML_CTX_FINISHED] || INV_F5426_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
            {
              INV_F5426__tmpE.data.p_id = 0;
              INV_F5426__tmpE.delay = 0;
              INV_F5426__tmpE.invokeid = 0;
              INV_F5426__tmpE.name = 0;
              INV_F5426__tmpE.origin = 0;
              INV_F5426__tmpE.sendid = 0;
              INV_F5426__tmpE.seqNr = 0;
              INV_F5426__tmpE.name = TIMEOUT;
              INV_F5426__tmpE.sendid = RESOURCE_DENIED_TIMER;
              INV_F5426__tmpE.invokeid = INV_F5426;
              INV_F5426__tmpE.origin = INV_F5426;
              _lastSeqId = _lastSeqId + 1;
              INV_F5426__tmpE.delay = INV_F5426_delay;
              INV_F5426__tmpE.seqNr = _lastSeqId;
#if TRACE_EXECUTION
printf("%d: Sending TIMEOUT (%d) to INV_F5426_eQ\n", _pid, INV_F5426__tmpE.name );
#endif

              INV_F5426_eQ!INV_F5426__tmpE;
              insertWithDelay(INV_F5426_eQ);
            }
            skip;
          }
          :: else -> skip;
          fi
          if
          :: !INV_F5426_flags[USCXML_CTX_FINISHED] || INV_F5426_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
            {
              INV_F5426__tmpE.data.p_id = 0;
              INV_F5426__tmpE.delay = 0;
              INV_F5426__tmpE.invokeid = 0;
              INV_F5426__tmpE.name = 0;
              INV_F5426__tmpE.origin = 0;
              INV_F5426__tmpE.sendid = 0;
              INV_F5426__tmpE.seqNr = 0;
              INV_F5426__tmpE.name = RESEND_NEED_FORKS;
              INV_F5426__tmpE.invokeid = INV_F5426;
              INV_F5426__tmpE.origin = INV_F5426;
              _lastSeqId = _lastSeqId + 1;
              INV_F5426__tmpE.delay = 300;
              INV_F5426__tmpE.seqNr = _lastSeqId;
#if TRACE_EXECUTION
printf("%d: Sending RESEND_NEED_FORKS (%d) to INV_F5426_eQ\n", _pid, INV_F5426__tmpE.name );
#endif

              INV_F5426_eQ!INV_F5426__tmpE;
              insertWithDelay(INV_F5426_eQ);
            }
            skip;
          }
          :: else -> skip;
          fi
         }
         :: else ->skip;
         fi

         /* take history and initial transitions */
         j = 0;
         do
         :: j < INV_F5426_USCXML_NUMBER_TRANS -> {
           if
           :: (INV_F5426_ctx.trans_set[j] &&
              (INV_F5426_transitions[j].type[USCXML_TRANS_HISTORY] ||
               INV_F5426_transitions[j].type[USCXML_TRANS_INITIAL]) && 
               INV_F5426_states[INV_F5426_transitions[j].source].parent == i) -> {
              /* Call executable content in history or initial transition */
              if
              :: j == 0 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, j);
#endif

                skip;
              }
              :: j == 1 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, j);
#endif

                skip;
              }
              :: j == 2 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, j);
#endif

                skip;
              }
              :: j == 3 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, j);
#endif

                if
                :: !INV_F5426_flags[USCXML_CTX_FINISHED] || INV_F5426_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
                  {
                    INV_F5426__tmpE.data.p_id = 0;
                    INV_F5426__tmpE.delay = 0;
                    INV_F5426__tmpE.invokeid = 0;
                    INV_F5426__tmpE.name = 0;
                    INV_F5426__tmpE.origin = 0;
                    INV_F5426__tmpE.sendid = 0;
                    INV_F5426__tmpE.seqNr = 0;
                    INV_F5426__tmpE.name = RETURN_FORKS;
                    INV_F5426__tmpE.invokeid = INV_F5426;
                    INV_F5426__tmpE.origin = INV_F5426;
                    _lastSeqId = _lastSeqId + 1;
                    INV_F5426__tmpE.delay = 0;
                    INV_F5426__tmpE.seqNr = _lastSeqId;
                    INV_F5426__tmpE.data.p_id = INV_F5426_p_id;
#if TRACE_EXECUTION
printf("%d: Sending RETURN_FORKS (%d) to ROOT_eQ\n", _pid, INV_F5426__tmpE.name );
#endif

                    ROOT_eQ!INV_F5426__tmpE;
                    insertWithDelay(ROOT_eQ);
                  }
                  skip;
                }
                :: else -> skip;
                fi
                skip;
              }
              :: j == 4 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, j);
#endif

                skip;
              }
              :: j == 5 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, j);
#endif

                if
                :: !INV_F5426_flags[USCXML_CTX_FINISHED] || INV_F5426_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
                  {
                    INV_F5426__tmpE.data.p_id = 0;
                    INV_F5426__tmpE.delay = 0;
                    INV_F5426__tmpE.invokeid = 0;
                    INV_F5426__tmpE.name = 0;
                    INV_F5426__tmpE.origin = 0;
                    INV_F5426__tmpE.sendid = 0;
                    INV_F5426__tmpE.seqNr = 0;
                    INV_F5426__tmpE.name = NEED_FORKS;
                    INV_F5426__tmpE.invokeid = INV_F5426;
                    INV_F5426__tmpE.origin = INV_F5426;
                    _lastSeqId = _lastSeqId + 1;
                    INV_F5426__tmpE.delay = 0;
                    INV_F5426__tmpE.seqNr = _lastSeqId;
                    INV_F5426__tmpE.data.p_id = INV_F5426_p_id;
#if TRACE_EXECUTION
printf("%d: Sending NEED_FORKS (%d) to ROOT_eQ\n", _pid, INV_F5426__tmpE.name );
#endif

                    ROOT_eQ!INV_F5426__tmpE;
                    insertWithDelay(ROOT_eQ);
                  }
                  skip;
                }
                :: else -> skip;
                fi
                skip;
              }
              :: j == 6 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, j);
#endif

                printf("philospher: : %d", INV_F5426_p_id);
                printf("Time(in ms) since resource denied: : %d", INV_F5426_delay);
                skip;
              }
              :: else ->skip;
              fi

           }
           :: else -> skip;
           fi
           j = j + 1;
         }
         :: else -> break;
         od
         /* handle final states */
         if
         :: INV_F5426_states[i].type[USCXML_STATE_FINAL] -> {
           if
           :: INV_F5426_states[INV_F5426_states[i].parent].children[1] -> {
             /* exit topmost SCXML state */
             INV_F5426_flags[USCXML_CTX_TOP_LEVEL_FINAL] = true;
             INV_F5426_flags[USCXML_CTX_FINISHED] = true;
           }
           :: else -> {
             /* raise done event */
             if
             :: else -> skip;
             fi
           }
           fi
           /**
            * are we the last final state to leave a parallel state?:
            * 1. Gather all parallel states in our ancestor chain
            * 2. Find all states for which these parallels are ancestors
            * 3. Iterate all active final states and remove their ancestors
            * 4. If a state remains, not all children of a parallel are final
            */
            j = 0;
            do
            :: j < INV_F5426_USCXML_NUMBER_STATES -> {
              if
              :: INV_F5426_states[j].type[USCXML_STATE_PARALLEL] && INV_F5426_states[i].ancestors[j] -> {
                INV_F5426_STATES_CLEAR(INV_F5426_ctx.tmp_states)
                k = 0;
                do
                :: k < INV_F5426_USCXML_NUMBER_STATES -> {
                  if
                  :: INV_F5426_states[k].ancestors[j] && INV_F5426_config[k] -> {
                    if
                    :: INV_F5426_states[k].type[USCXML_STATE_FINAL] -> {
                      INV_F5426_STATES_AND_NOT(INV_F5426_ctx.tmp_states, INV_F5426_states[k].ancestors)
                    }
                    :: else -> {
                      INV_F5426_ctx.tmp_states[k] = true;
                    }
                    fi
                  }
                  :: else -> skip;
                  fi
                  k = k + 1;
                }
                :: else -> break;
                od
                if
                :: !INV_F5426_STATES_HAS_ANY(INV_F5426_ctx.tmp_states) -> {
                  if
                  :: else -> skip;
                  fi
                }
                :: else -> skip;
                fi
              }
              :: else -> skip;
              fi
              j = j + 1;
            }
            :: else -> break;
            od
         }
         :: else -> skip;
         fi

    }
    :: else -> skip;
    i = i + 1;
    fi;
  }
  :: else -> break;
  od;

  }
  :: else -> skip;
  fi /* USCXML_CTX_TRANSITION_FOUND */
  } skip; /* d_step */
} /* !USCXML_CTX_FINISHED */
:: else -> break;
od

/* ---------------------------- */
INV_F5426_TERMINATE_MACHINE:
skip; d_step {

#if TRACE_EXECUTION
printf("%d: Machine finished\n", _pid);
#endif

/* exit all remaining states */
i = INV_F5426_USCXML_NUMBER_STATES;
do
:: i > 0 -> {
  i = i - 1;
  if
  :: INV_F5426_config[i] && INV_F5426_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
    /* call all on exit handlers */
   if
    :: i == 5 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for exiting state %d\n", _pid, i);
#endif

    if
    :: (INV_F5426__event.name == TAKE_FORKS) -> {
        cancelSendId(RESOURCE_DENIED_TIMER,INV_F5426);
    }
    :: else -> skip;
    fi;
    }
    :: else -> skip;
    fi

    skip;
    
  }
  :: else -> skip;
  fi;

  if
  :: INV_F5426_invocations[i] -> {
    /* cancel invocations */
    INV_F5426_invocations[i] = false;
    if
    :: else -> skip;
    fi
    skip;

  }
  :: else -> skip;
  fi;
}
:: else -> break;
od;


#if TRACE_EXECUTION
printf("%d: Removing pending events\n", _pid);
#endif

removePendingEventsFromInvoker(INV_F5426)
/* send done event */
if
:: INV_F5426_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
    INV_F5426__tmpE.data.p_id = 0;
    INV_F5426__tmpE.delay = 0;
    INV_F5426__tmpE.invokeid = 0;
    INV_F5426__tmpE.name = 0;
    INV_F5426__tmpE.origin = 0;
    INV_F5426__tmpE.sendid = 0;
    INV_F5426__tmpE.seqNr = 0;

    INV_F5426__tmpE.name = DONE_INVOKE_INV_F5426
    INV_F5426__tmpE.invokeid = INV_F5426

#if TRACE_EXECUTION
printf("%d: Sending DONE.INVOKE\n", _pid);
#endif

    ROOT_eQ!INV_F5426__tmpE;
    insertWithDelay(ROOT_eQ);
}
:: else -> skip
fi;

} /* d_step */


#if TRACE_EXECUTION
printf("%d: Done\n", _pid);
#endif

} } /* atomic, step() */


/* machine microstep function */
#define INV_8CB85_USCXML_NUMBER_STATES 7
#define INV_8CB85_USCXML_NUMBER_TRANS 7

proctype INV_8CB85_step() { atomic {

INV_8CB85_procid = _pid;
unsigned i : 3,  j : 3,  k : 3;


/* ---------------------------- */
INV_8CB85_MICROSTEP:
do
:: !INV_8CB85_flags[USCXML_CTX_FINISHED] -> {
  /* Run until machine is finished */


#if TRACE_EXECUTION
printf("%d: Taking a step\n", _pid);
#endif

  /* Dequeue an event */
  INV_8CB85_flags[USCXML_CTX_DEQUEUE_EXTERNAL] = false;
  if
  ::INV_8CB85_flags[USCXML_CTX_SPONTANEOUS] -> {
    INV_8CB85__event.name = USCXML_EVENT_SPONTANEOUS;

#if TRACE_EXECUTION
printf("%d: Trying with a spontaneous event\n", _pid);
#endif

  }
  :: else -> {
    if
    :: len(INV_8CB85_iQ) != 0 -> {
      INV_8CB85_iQ ? INV_8CB85__event;

#if TRACE_EXECUTION
printf("%d: Deqeued an internal event\n", _pid);
#endif

    }
    :: else -> {
      INV_8CB85_flags[USCXML_CTX_DEQUEUE_EXTERNAL] = true;
    }
    fi;
  }
  fi;


  if
  :: INV_8CB85_flags[USCXML_CTX_DEQUEUE_EXTERNAL] -> {
    /* manage invocations */
    i = 0;
    do
    :: i < INV_8CB85_USCXML_NUMBER_STATES -> {
      d_step { 
      /* uninvoke */
      if
      :: !INV_8CB85_config[i] && INV_8CB85_invocations[i] -> {

#if TRACE_EXECUTION
printf("%d: Uninvoking in state %d\n", _pid, i);
#endif

        if
        :: else -> skip;
        fi
        INV_8CB85_invocations[i] = false;
        skip;
      }
      :: else -> skip;
      fi;
      } /* d_step */

      /* invoke */
      if
      :: INV_8CB85_config[i] && !INV_8CB85_invocations[i] -> {
        if
        :: else -> skip;
        fi
      }
      :: else -> skip;
      fi;
      i = i + 1;
    }
    :: else -> break;
    od;

    /* Determine machines with smallest delay and set their process priority */
    scheduleMachines();

    /* we may return to find ourselves terminated */
    if
    :: INV_8CB85_flags[USCXML_CTX_FINISHED] -> {
      goto INV_8CB85_TERMINATE_MACHINE;
    }
    :: else -> skip;
    fi
    /* Not sure if this should be before the invocation due to auto-forwarding */
    if
    :: len(INV_8CB85_eQ) != 0 -> {
      INV_8CB85_eQ ? INV_8CB85__event;

#if TRACE_EXECUTION
printf("%d: Deqeued an external event\n", _pid);
#endif

    }
    fi;
  }
  :: else -> skip;
  fi


d_step { skip;

/* ---------------------------- */
INV_8CB85_SELECT_TRANSITIONS:
INV_8CB85_STATES_CLEAR(INV_8CB85_ctx.target_set)
INV_8CB85_STATES_CLEAR(INV_8CB85_ctx.exit_set)
INV_8CB85_TRANS_CLEAR(INV_8CB85_ctx.conflicts)
INV_8CB85_TRANS_CLEAR(INV_8CB85_ctx.trans_set)
#if TRACE_EXECUTION
printf("%d: Establishing optimal transition set for event %d\n", _pid, INV_8CB85__event.name );
#endif

#if TRACE_EXECUTION
printf("Configuration: ");
printf("%d%d%d%d%d%d%d", 
    INV_8CB85_config[0], 
    INV_8CB85_config[1], 
    INV_8CB85_config[2], 
    INV_8CB85_config[3], 
    INV_8CB85_config[4], 
    INV_8CB85_config[5], 
    INV_8CB85_config[6]);
printf("\n");
#endif

  INV_8CB85_flags[USCXML_CTX_TRANSITION_FOUND] = false;
  i = 0;
  do
  :: i < INV_8CB85_USCXML_NUMBER_TRANS -> {
    /* only select non-history, non-initial transitions */
    if
    :: !INV_8CB85_transitions[i].type[USCXML_TRANS_HISTORY] &&
       !INV_8CB85_transitions[i].type[USCXML_TRANS_INITIAL] -> {
      if
      :: /* is the transition active? */
         INV_8CB85_config[INV_8CB85_transitions[i].source] && 

         /* is it non-conflicting? */
         !INV_8CB85_ctx.conflicts[i] && 

         /* is it spontaneous with an event or vice versa? */
         ((INV_8CB85__event.name == USCXML_EVENT_SPONTANEOUS && 
           INV_8CB85_transitions[i].type[USCXML_TRANS_SPONTANEOUS]) || 
          (INV_8CB85__event.name != USCXML_EVENT_SPONTANEOUS && 
           !INV_8CB85_transitions[i].type[USCXML_TRANS_SPONTANEOUS])) &&

         /* is it matching and enabled? */
         (false 
          || (i == 0 && (false || INV_8CB85__event.name == THINKING_OVER))
          || (i == 1 && (false || INV_8CB85__event.name == TAKE_FORKS))
          || (i == 2 && (false || INV_8CB85__event.name == RESOURCE_DENIED))
          || (i == 3 && (false || INV_8CB85__event.name == EATING_OVER))
          || (i == 4 && (false || INV_8CB85__event.name == TAKE_FORKS))
          || (i == 5 && (false || INV_8CB85__event.name == RESEND_NEED_FORKS))
          || (i == 6 && (false || INV_8CB85__event.name == TIMEOUT))
         ) -> {
        /* remember that we found a transition */
        INV_8CB85_flags[USCXML_CTX_TRANSITION_FOUND] = true;

        /* transitions that are pre-empted */
        INV_8CB85_TRANS_OR(INV_8CB85_ctx.conflicts, INV_8CB85_transitions[i].conflicts)

        /* states that are directly targeted (resolve as entry-set later) */
        INV_8CB85_STATES_OR(INV_8CB85_ctx.target_set, INV_8CB85_transitions[i].target)

        /* states that will be left */
        INV_8CB85_STATES_OR(INV_8CB85_ctx.exit_set, INV_8CB85_transitions[i].exit_set)

        INV_8CB85_ctx.trans_set[i] = true;
      }
      :: else {
        skip;
      }
      fi
    }
    :: else -> {
      skip;
    }
    fi
    i = i + 1;
  }
  :: else -> break;
  od;
  INV_8CB85_STATES_AND(INV_8CB85_ctx.exit_set, INV_8CB85_config)

#if TRACE_EXECUTION
printf("Selected Transitions: ");
printf("%d%d%d%d%d%d%d", 
    INV_8CB85_ctx.trans_set[0], 
    INV_8CB85_ctx.trans_set[1], 
    INV_8CB85_ctx.trans_set[2], 
    INV_8CB85_ctx.trans_set[3], 
    INV_8CB85_ctx.trans_set[4], 
    INV_8CB85_ctx.trans_set[5], 
    INV_8CB85_ctx.trans_set[6]);
printf("\n");
#endif


#if TRACE_EXECUTION
printf("Target Set: ");
printf("%d%d%d%d%d%d%d", 
    INV_8CB85_ctx.target_set[0], 
    INV_8CB85_ctx.target_set[1], 
    INV_8CB85_ctx.target_set[2], 
    INV_8CB85_ctx.target_set[3], 
    INV_8CB85_ctx.target_set[4], 
    INV_8CB85_ctx.target_set[5], 
    INV_8CB85_ctx.target_set[6]);
printf("\n");
#endif


#if TRACE_EXECUTION
printf("Exit Set: ");
printf("%d%d%d%d%d%d%d", 
    INV_8CB85_ctx.exit_set[0], 
    INV_8CB85_ctx.exit_set[1], 
    INV_8CB85_ctx.exit_set[2], 
    INV_8CB85_ctx.exit_set[3], 
    INV_8CB85_ctx.exit_set[4], 
    INV_8CB85_ctx.exit_set[5], 
    INV_8CB85_ctx.exit_set[6]);
printf("\n");
#endif

  if
  :: !INV_8CB85_STATES_HAS_ANY(INV_8CB85_config) -> {
    /* Enter initial configuration */
    INV_8CB85_STATES_COPY(INV_8CB85_ctx.target_set, INV_8CB85_states[0].completion)
    INV_8CB85_flags[USCXML_CTX_SPONTANEOUS] = true;
    INV_8CB85_flags[USCXML_CTX_TRANSITION_FOUND] = true;

#if TRACE_EXECUTION
printf("%d: Entering initial default completion\n", _pid);
#endif


  }
  :: INV_8CB85_flags[USCXML_CTX_TRANSITION_FOUND] -> {

#if TRACE_EXECUTION
printf("%d: Found transitions\n", _pid);
#endif

    INV_8CB85_flags[USCXML_CTX_SPONTANEOUS] = true;
  }
  :: else {
    INV_8CB85_flags[USCXML_CTX_SPONTANEOUS] = false;

#if TRACE_EXECUTION
printf("%d: Found NO transitions\n", _pid);
#endif

  }
  fi


  if
  :: INV_8CB85_flags[USCXML_CTX_TRANSITION_FOUND] -> {
    /* only process anything if we found transitions or are on initial entry */
/* ---------------------------- */
/* REMEMBER_HISTORY: */

#if TRACE_EXECUTION
printf("%d: Save history configurations\n", _pid);
#endif

  if
  :: INV_8CB85_STATES_HAS_ANY(INV_8CB85_config) -> {
    /* only remember history on non-initial entry */
    i = 0;
    do
    :: i < INV_8CB85_USCXML_NUMBER_STATES -> {
      if
      :: INV_8CB85_states[i].type[USCXML_STATE_HISTORY_SHALLOW] ||
         INV_8CB85_states[i].type[USCXML_STATE_HISTORY_DEEP] -> {
        if
        :: INV_8CB85_ctx.exit_set[INV_8CB85_states[i].parent] -> {
          /* a history state whose parent is about to be exited */

#if TRACE_EXECUTION
printf("%d: history state %d is about to be exited\n", _pid, i);
#endif


#if TRACE_EXECUTION
printf("COMPLET: ");
printf("%d%d%d%d%d%d%d", 
    INV_8CB85_states[i].completion[0], 
    INV_8CB85_states[i].completion[1], 
    INV_8CB85_states[i].completion[2], 
    INV_8CB85_states[i].completion[3], 
    INV_8CB85_states[i].completion[4], 
    INV_8CB85_states[i].completion[5], 
    INV_8CB85_states[i].completion[6]);
printf("\n");
#endif

          INV_8CB85_STATES_COPY(INV_8CB85_ctx.tmp_states, INV_8CB85_states[i].completion)

          /* set those states who were enabled */
          INV_8CB85_STATES_AND(INV_8CB85_ctx.tmp_states, INV_8CB85_config)

#if TRACE_EXECUTION
printf("CONFIG : ");
printf("%d%d%d%d%d%d%d", 
    INV_8CB85_config[0], 
    INV_8CB85_config[1], 
    INV_8CB85_config[2], 
    INV_8CB85_config[3], 
    INV_8CB85_config[4], 
    INV_8CB85_config[5], 
    INV_8CB85_config[6]);
printf("\n");
#endif


#if TRACE_EXECUTION
printf("TMP_STS: ");
printf("%d%d%d%d%d%d%d", 
    INV_8CB85_ctx.tmp_states[0], 
    INV_8CB85_ctx.tmp_states[1], 
    INV_8CB85_ctx.tmp_states[2], 
    INV_8CB85_ctx.tmp_states[3], 
    INV_8CB85_ctx.tmp_states[4], 
    INV_8CB85_ctx.tmp_states[5], 
    INV_8CB85_ctx.tmp_states[6]);
printf("\n");
#endif


          /* clear current history with completion mask */
          INV_8CB85_STATES_AND_NOT(INV_8CB85_history, INV_8CB85_states[i].completion)

          /* set history */
          INV_8CB85_STATES_OR(INV_8CB85_history, INV_8CB85_ctx.tmp_states)

        }
        :: else -> skip;
        fi;
      }
      :: else -> skip;
      fi;
      i = i + 1;
    }
    :: else -> break;
    od;


#if TRACE_EXECUTION
printf("History: ");
printf("%d%d%d%d%d%d%d", 
    INV_8CB85_history[0], 
    INV_8CB85_history[1], 
    INV_8CB85_history[2], 
    INV_8CB85_history[3], 
    INV_8CB85_history[4], 
    INV_8CB85_history[5], 
    INV_8CB85_history[6]);
printf("\n");
#endif
  }
  :: else -> skip;
  fi;

/* ---------------------------- */
INV_8CB85_ESTABLISH_ENTRY_SET:
  /* calculate new entry set */
  INV_8CB85_STATES_COPY(INV_8CB85_ctx.entry_set, INV_8CB85_ctx.target_set)

  i = 0;
  do
  :: i < INV_8CB85_USCXML_NUMBER_STATES -> {
    if
    :: INV_8CB85_ctx.entry_set[i] -> {
      /* ancestor completion */
      INV_8CB85_STATES_OR(INV_8CB85_ctx.entry_set, INV_8CB85_states[i].ancestors)
    }
    :: else -> skip;
    fi;
    i = i + 1;
  }
  :: else -> break;
  od;

  /* iterate for descendants */
  i = 0;
  do
  :: i < INV_8CB85_USCXML_NUMBER_STATES -> {
    if
    :: INV_8CB85_ctx.entry_set[i] -> {
      if
      :: INV_8CB85_states[i].type[USCXML_STATE_PARALLEL] -> {
        INV_8CB85_STATES_OR(INV_8CB85_ctx.entry_set, INV_8CB85_states[i].completion)
      }
      :: INV_8CB85_states[i].type[USCXML_STATE_HISTORY_SHALLOW] ||
         INV_8CB85_states[i].type[USCXML_STATE_HISTORY_DEEP] -> {

#if TRACE_EXECUTION
printf("%d: Descendant completion for history state %d\n", _pid, i);
#endif

        if
        :: !INV_8CB85_STATES_HAS_AND(INV_8CB85_states[i].completion, INV_8CB85_history) && !INV_8CB85_config[INV_8CB85_states[i].parent] -> {
          /* nothing set for history, look for a default transition */

#if TRACE_EXECUTION
printf("%d: Fresh history in target set\n", _pid);
#endif

          j = 0;
          do
          :: j < INV_8CB85_USCXML_NUMBER_TRANS -> {
             if
             :: INV_8CB85_transitions[j].source == i -> {
               INV_8CB85_ctx.trans_set[j] = true;
               INV_8CB85_STATES_OR(INV_8CB85_ctx.entry_set, INV_8CB85_transitions[j].target)

               if
               :: (INV_8CB85_states[i].type[USCXML_STATE_HISTORY_DEEP] &&
                   !INV_8CB85_STATES_HAS_AND(INV_8CB85_transitions[j].target, INV_8CB85_states[i].children)                  ) -> {
                 k = i + 1
                 do
                 :: k < INV_8CB85_USCXML_NUMBER_STATES -> {
                   if
                   :: INV_8CB85_transitions[j].target[k] -> {
                     INV_8CB85_STATES_OR(INV_8CB85_ctx.entry_set, INV_8CB85_states[k].ancestors)
                     break;

                   }
                   :: else -> skip;
                   fi
                   k = k + 1;
                 }
                 :: else -> break;
                 od
               }
               :: else -> skip;
               fi
               break;
             }
             :: else -> skip;
             fi
             j = j + 1;
          }
          :: else -> break
          od
          skip;
        }
        :: else -> {

#if TRACE_EXECUTION
printf("%d: Established history in target set\n", _pid);
#endif

          INV_8CB85_STATES_COPY(INV_8CB85_ctx.tmp_states, INV_8CB85_states[i].completion)
          INV_8CB85_STATES_AND(INV_8CB85_ctx.tmp_states, INV_8CB85_history)
          INV_8CB85_STATES_OR(INV_8CB85_ctx.entry_set, INV_8CB85_ctx.tmp_states)
          if
          :: INV_8CB85_states[i].type[USCXML_STATE_HAS_HISTORY] ||
             INV_8CB85_states[i].type[USCXML_STATE_HISTORY_DEEP] -> { 
            /* a deep history state with nested histories -> more completion */

#if TRACE_EXECUTION
printf("%d: DEEP HISTORY\n", _pid);
#endif

            j = i + 1;
            do
            :: j < INV_8CB85_USCXML_NUMBER_STATES -> {
              if
              :: (INV_8CB85_states[i].completion[j] &&
                  INV_8CB85_ctx.entry_set[j] && 
                  INV_8CB85_states[j].type[USCXML_STATE_HAS_HISTORY]) -> {
                k = j + 1;
                do
                :: k < INV_8CB85_USCXML_NUMBER_STATES -> {
                  /* add nested history to entry_set */
                  if
                  :: (INV_8CB85_states[k].type[USCXML_STATE_HISTORY_DEEP] ||
                      INV_8CB85_states[k].type[USCXML_STATE_HISTORY_SHALLOW]) &&
                     INV_8CB85_states[j].children[k] -> {
                    /* a nested history state */
                    INV_8CB85_ctx.entry_set[k] = true;
                  }
                  :: else -> skip;
                  fi
                  k = k + 1;
                }
                :: else -> break;
                od
              }
              :: else -> skip;
              fi
            }
            j = j + 1;
            :: else -> break;
            od
          }
          :: else -> skip;
          fi
        }
        fi;
      }
      :: INV_8CB85_states[i].type[USCXML_STATE_INITIAL] -> {

#if TRACE_EXECUTION
printf("%d: Descendant completion for initial state %d\n", _pid, i);
#endif

        j = 0
        do
        :: j < INV_8CB85_USCXML_NUMBER_TRANS -> {
          if
          :: INV_8CB85_transitions[j].source == i -> {
            INV_8CB85_ctx.trans_set[j] = true;
            INV_8CB85_ctx.entry_set[i] = false;

#if TRACE_EXECUTION
printf("%d: Adding transition %d!\n", _pid, j);
#endif

            INV_8CB85_STATES_OR(INV_8CB85_ctx.entry_set, INV_8CB85_transitions[j].target)

            k = i + 1;
            do
            :: k < INV_8CB85_USCXML_NUMBER_STATES -> {
              if
              :: INV_8CB85_transitions[j].target[k] -> {
                INV_8CB85_STATES_OR(INV_8CB85_ctx.entry_set, INV_8CB85_states[k].ancestors)

              }
              :: else -> break;
              fi
              k = k + 1;
            }
            :: else -> break
            od
          }
          :: else -> skip;
          fi
          j = j + 1;
        }
        :: else -> break
        od;
      }
      :: INV_8CB85_states[i].type[USCXML_STATE_COMPOUND] -> {
        /* we need to check whether one child is already in entry_set */
        if
        :: (
          !INV_8CB85_STATES_HAS_AND(INV_8CB85_ctx.entry_set, INV_8CB85_states[i].children) && 
           (!INV_8CB85_STATES_HAS_AND(INV_8CB85_config, INV_8CB85_states[i].children) || INV_8CB85_STATES_HAS_AND(INV_8CB85_ctx.exit_set, INV_8CB85_states[i].children)
)) 
        -> {
          INV_8CB85_STATES_OR(INV_8CB85_ctx.entry_set, INV_8CB85_states[i].completion)
          if
          :: (INV_8CB85_STATES_HAS_AND(INV_8CB85_states[i].completion, INV_8CB85_states[i].children)
          ) -> {
            /* deep completion */
            j = i + 1;
            do
            :: j < INV_8CB85_USCXML_NUMBER_STATES - 1 -> {
              j = j + 1;
              if
              :: INV_8CB85_states[i].completion[j] -> {
                INV_8CB85_STATES_OR(INV_8CB85_ctx.entry_set, INV_8CB85_states[j].ancestors)

                /* completion of compound is single state */
                break;
              } 
              :: else -> skip;
              fi
            }
            :: else -> break;
            od
          }
          :: else -> skip;
          fi
        }
        :: else -> skip;
        fi
      }
      :: else -> skip;
      fi;
    }
    :: else -> skip;
    fi;
    i = i + 1;
  }
  :: else -> break;
  od;


#if TRACE_EXECUTION
printf("Entry Set");
printf("%d%d%d%d%d%d%d", 
    INV_8CB85_ctx.entry_set[0], 
    INV_8CB85_ctx.entry_set[1], 
    INV_8CB85_ctx.entry_set[2], 
    INV_8CB85_ctx.entry_set[3], 
    INV_8CB85_ctx.entry_set[4], 
    INV_8CB85_ctx.entry_set[5], 
    INV_8CB85_ctx.entry_set[6]);
printf("\n");
#endif


/* ---------------------------- */
/* EXIT_STATES: */
  i = INV_8CB85_USCXML_NUMBER_STATES;
  do
  :: i > 0 -> {
    i = i - 1;
    if
    :: INV_8CB85_ctx.exit_set[i] && INV_8CB85_config[i] -> {
      /* call all on-exit handlers */

#if TRACE_EXECUTION
printf("%d: Exiting state %d\n", _pid, i);
#endif

      if
      :: i == 5 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for exiting state %d\n", _pid, i);
#endif

      if
      :: (INV_8CB85__event.name == TAKE_FORKS) -> {
          cancelSendId(RESOURCE_DENIED_TIMER,INV_8CB85);
      }
      :: else -> skip;
      fi;
      }
      :: else -> skip;
      fi

      INV_8CB85_config[i] = false;
      skip;
    }
    :: else -> skip;
    fi;
  }
  :: else -> break;
  od;


/* ---------------------------- */
/* TAKE_TRANSITIONS: */
  i = 0;
  do
  :: i < INV_8CB85_USCXML_NUMBER_TRANS -> {
    if
    :: INV_8CB85_ctx.trans_set[i] && 
       !INV_8CB85_transitions[i].type[USCXML_TRANS_HISTORY] && 
       !INV_8CB85_transitions[i].type[USCXML_TRANS_INITIAL] -> {
      /* Call executable content in normal transition */

#if TRACE_EXECUTION
printf("%d: Taking transition %d\n", _pid, i);
#endif

      if
      :: i == 0 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, i);
#endif

        skip;
      }
      :: i == 1 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, i);
#endif

        skip;
      }
      :: i == 2 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, i);
#endif

        skip;
      }
      :: i == 3 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, i);
#endif

        if
        :: !INV_8CB85_flags[USCXML_CTX_FINISHED] || INV_8CB85_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
          {
            INV_8CB85__tmpE.data.p_id = 0;
            INV_8CB85__tmpE.delay = 0;
            INV_8CB85__tmpE.invokeid = 0;
            INV_8CB85__tmpE.name = 0;
            INV_8CB85__tmpE.origin = 0;
            INV_8CB85__tmpE.sendid = 0;
            INV_8CB85__tmpE.seqNr = 0;
            INV_8CB85__tmpE.name = RETURN_FORKS;
            INV_8CB85__tmpE.invokeid = INV_8CB85;
            INV_8CB85__tmpE.origin = INV_8CB85;
            _lastSeqId = _lastSeqId + 1;
            INV_8CB85__tmpE.delay = 0;
            INV_8CB85__tmpE.seqNr = _lastSeqId;
            INV_8CB85__tmpE.data.p_id = INV_8CB85_p_id;
#if TRACE_EXECUTION
printf("%d: Sending RETURN_FORKS (%d) to ROOT_eQ\n", _pid, INV_8CB85__tmpE.name );
#endif

            ROOT_eQ!INV_8CB85__tmpE;
            insertWithDelay(ROOT_eQ);
          }
          skip;
        }
        :: else -> skip;
        fi
        skip;
      }
      :: i == 4 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, i);
#endif

        skip;
      }
      :: i == 5 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, i);
#endif

        if
        :: !INV_8CB85_flags[USCXML_CTX_FINISHED] || INV_8CB85_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
          {
            INV_8CB85__tmpE.data.p_id = 0;
            INV_8CB85__tmpE.delay = 0;
            INV_8CB85__tmpE.invokeid = 0;
            INV_8CB85__tmpE.name = 0;
            INV_8CB85__tmpE.origin = 0;
            INV_8CB85__tmpE.sendid = 0;
            INV_8CB85__tmpE.seqNr = 0;
            INV_8CB85__tmpE.name = NEED_FORKS;
            INV_8CB85__tmpE.invokeid = INV_8CB85;
            INV_8CB85__tmpE.origin = INV_8CB85;
            _lastSeqId = _lastSeqId + 1;
            INV_8CB85__tmpE.delay = 0;
            INV_8CB85__tmpE.seqNr = _lastSeqId;
            INV_8CB85__tmpE.data.p_id = INV_8CB85_p_id;
#if TRACE_EXECUTION
printf("%d: Sending NEED_FORKS (%d) to ROOT_eQ\n", _pid, INV_8CB85__tmpE.name );
#endif

            ROOT_eQ!INV_8CB85__tmpE;
            insertWithDelay(ROOT_eQ);
          }
          skip;
        }
        :: else -> skip;
        fi
        skip;
      }
      :: i == 6 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, i);
#endif

        printf("philospher: : %d", INV_8CB85_p_id);
        printf("Time(in ms) since resource denied: : %d", INV_8CB85_delay);
        skip;
      }
      :: else ->skip;
      fi

    }
    :: else -> skip;
    fi;
    i = i + 1;
  }
  :: else -> break;
  od;

/* ---------------------------- */
/* ENTER_STATES: */
  i = 0;
  do
  :: i < INV_8CB85_USCXML_NUMBER_STATES -> {
    if
    :: (INV_8CB85_ctx.entry_set[i] &&
        !INV_8CB85_config[i] && 
        /* these are no proper states */
        !INV_8CB85_states[i].type[USCXML_STATE_HISTORY_DEEP] && 
        !INV_8CB85_states[i].type[USCXML_STATE_HISTORY_SHALLOW] && 
        !INV_8CB85_states[i].type[USCXML_STATE_INITIAL]
       ) -> {

#if TRACE_EXECUTION
printf("%d: Entering state %d\n", _pid, i);
#endif

         INV_8CB85_config[i] = true;

         /* Process executable content for entering a state */
         if
         :: i == 1 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for entering state %d\n", _pid, i);
#endif

          printf("Hello, I am philospher number: : %d", INV_8CB85_p_id);
         }
         :: i == 2 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for entering state %d\n", _pid, i);
#endif

          printf("Thinking professor: : %d", INV_8CB85_p_id);
            INV_8CB85_random_delay = ((1103515245*INV_8CB85_random_delay+12345)%2147483647)%2000;
          if
          :: !INV_8CB85_flags[USCXML_CTX_FINISHED] || INV_8CB85_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
            {
              INV_8CB85__tmpE.data.p_id = 0;
              INV_8CB85__tmpE.delay = 0;
              INV_8CB85__tmpE.invokeid = 0;
              INV_8CB85__tmpE.name = 0;
              INV_8CB85__tmpE.origin = 0;
              INV_8CB85__tmpE.sendid = 0;
              INV_8CB85__tmpE.seqNr = 0;
              INV_8CB85__tmpE.name = THINKING_OVER;
              INV_8CB85__tmpE.invokeid = INV_8CB85;
              INV_8CB85__tmpE.origin = INV_8CB85;
              _lastSeqId = _lastSeqId + 1;
              INV_8CB85__tmpE.delay = INV_8CB85_random_delay*(INV_8CB85_p_id+1);
              INV_8CB85__tmpE.seqNr = _lastSeqId;
#if TRACE_EXECUTION
printf("%d: Sending THINKING_OVER (%d) to INV_8CB85_eQ\n", _pid, INV_8CB85__tmpE.name );
#endif

              INV_8CB85_eQ!INV_8CB85__tmpE;
              insertWithDelay(INV_8CB85_eQ);
            }
            skip;
          }
          :: else -> skip;
          fi
         }
         :: i == 3 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for entering state %d\n", _pid, i);
#endif

          printf("Hungry professor: : %d", INV_8CB85_p_id);
          if
          :: !INV_8CB85_flags[USCXML_CTX_FINISHED] || INV_8CB85_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
            {
              INV_8CB85__tmpE.data.p_id = 0;
              INV_8CB85__tmpE.delay = 0;
              INV_8CB85__tmpE.invokeid = 0;
              INV_8CB85__tmpE.name = 0;
              INV_8CB85__tmpE.origin = 0;
              INV_8CB85__tmpE.sendid = 0;
              INV_8CB85__tmpE.seqNr = 0;
              INV_8CB85__tmpE.name = NEED_FORKS;
              INV_8CB85__tmpE.invokeid = INV_8CB85;
              INV_8CB85__tmpE.origin = INV_8CB85;
              _lastSeqId = _lastSeqId + 1;
              INV_8CB85__tmpE.delay = 300;
              INV_8CB85__tmpE.seqNr = _lastSeqId;
              INV_8CB85__tmpE.data.p_id = INV_8CB85_p_id;
#if TRACE_EXECUTION
printf("%d: Sending NEED_FORKS (%d) to ROOT_eQ\n", _pid, INV_8CB85__tmpE.name );
#endif

              ROOT_eQ!INV_8CB85__tmpE;
              insertWithDelay(ROOT_eQ);
            }
            skip;
          }
          :: else -> skip;
          fi
         }
         :: i == 4 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for entering state %d\n", _pid, i);
#endif

          printf("Eating professor: : %d", INV_8CB85_p_id);
          if
          :: !INV_8CB85_flags[USCXML_CTX_FINISHED] || INV_8CB85_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
            {
              INV_8CB85__tmpE.data.p_id = 0;
              INV_8CB85__tmpE.delay = 0;
              INV_8CB85__tmpE.invokeid = 0;
              INV_8CB85__tmpE.name = 0;
              INV_8CB85__tmpE.origin = 0;
              INV_8CB85__tmpE.sendid = 0;
              INV_8CB85__tmpE.seqNr = 0;
              INV_8CB85__tmpE.name = EATING_OVER;
              INV_8CB85__tmpE.invokeid = INV_8CB85;
              INV_8CB85__tmpE.origin = INV_8CB85;
              _lastSeqId = _lastSeqId + 1;
              INV_8CB85__tmpE.delay = 500;
              INV_8CB85__tmpE.seqNr = _lastSeqId;
#if TRACE_EXECUTION
printf("%d: Sending EATING_OVER (%d) to INV_8CB85_eQ\n", _pid, INV_8CB85__tmpE.name );
#endif

              INV_8CB85_eQ!INV_8CB85__tmpE;
              insertWithDelay(INV_8CB85_eQ);
            }
            skip;
          }
          :: else -> skip;
          fi
         }
         :: i == 5 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for entering state %d\n", _pid, i);
#endif

          printf("Resource Denied professor: : %d", INV_8CB85_p_id);
          if
          :: !INV_8CB85_flags[USCXML_CTX_FINISHED] || INV_8CB85_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
            {
              INV_8CB85__tmpE.data.p_id = 0;
              INV_8CB85__tmpE.delay = 0;
              INV_8CB85__tmpE.invokeid = 0;
              INV_8CB85__tmpE.name = 0;
              INV_8CB85__tmpE.origin = 0;
              INV_8CB85__tmpE.sendid = 0;
              INV_8CB85__tmpE.seqNr = 0;
              INV_8CB85__tmpE.name = TIMEOUT;
              INV_8CB85__tmpE.sendid = RESOURCE_DENIED_TIMER;
              INV_8CB85__tmpE.invokeid = INV_8CB85;
              INV_8CB85__tmpE.origin = INV_8CB85;
              _lastSeqId = _lastSeqId + 1;
              INV_8CB85__tmpE.delay = INV_8CB85_delay;
              INV_8CB85__tmpE.seqNr = _lastSeqId;
#if TRACE_EXECUTION
printf("%d: Sending TIMEOUT (%d) to INV_8CB85_eQ\n", _pid, INV_8CB85__tmpE.name );
#endif

              INV_8CB85_eQ!INV_8CB85__tmpE;
              insertWithDelay(INV_8CB85_eQ);
            }
            skip;
          }
          :: else -> skip;
          fi
          if
          :: !INV_8CB85_flags[USCXML_CTX_FINISHED] || INV_8CB85_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
            {
              INV_8CB85__tmpE.data.p_id = 0;
              INV_8CB85__tmpE.delay = 0;
              INV_8CB85__tmpE.invokeid = 0;
              INV_8CB85__tmpE.name = 0;
              INV_8CB85__tmpE.origin = 0;
              INV_8CB85__tmpE.sendid = 0;
              INV_8CB85__tmpE.seqNr = 0;
              INV_8CB85__tmpE.name = RESEND_NEED_FORKS;
              INV_8CB85__tmpE.invokeid = INV_8CB85;
              INV_8CB85__tmpE.origin = INV_8CB85;
              _lastSeqId = _lastSeqId + 1;
              INV_8CB85__tmpE.delay = 300;
              INV_8CB85__tmpE.seqNr = _lastSeqId;
#if TRACE_EXECUTION
printf("%d: Sending RESEND_NEED_FORKS (%d) to INV_8CB85_eQ\n", _pid, INV_8CB85__tmpE.name );
#endif

              INV_8CB85_eQ!INV_8CB85__tmpE;
              insertWithDelay(INV_8CB85_eQ);
            }
            skip;
          }
          :: else -> skip;
          fi
         }
         :: else ->skip;
         fi

         /* take history and initial transitions */
         j = 0;
         do
         :: j < INV_8CB85_USCXML_NUMBER_TRANS -> {
           if
           :: (INV_8CB85_ctx.trans_set[j] &&
              (INV_8CB85_transitions[j].type[USCXML_TRANS_HISTORY] ||
               INV_8CB85_transitions[j].type[USCXML_TRANS_INITIAL]) && 
               INV_8CB85_states[INV_8CB85_transitions[j].source].parent == i) -> {
              /* Call executable content in history or initial transition */
              if
              :: j == 0 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, j);
#endif

                skip;
              }
              :: j == 1 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, j);
#endif

                skip;
              }
              :: j == 2 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, j);
#endif

                skip;
              }
              :: j == 3 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, j);
#endif

                if
                :: !INV_8CB85_flags[USCXML_CTX_FINISHED] || INV_8CB85_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
                  {
                    INV_8CB85__tmpE.data.p_id = 0;
                    INV_8CB85__tmpE.delay = 0;
                    INV_8CB85__tmpE.invokeid = 0;
                    INV_8CB85__tmpE.name = 0;
                    INV_8CB85__tmpE.origin = 0;
                    INV_8CB85__tmpE.sendid = 0;
                    INV_8CB85__tmpE.seqNr = 0;
                    INV_8CB85__tmpE.name = RETURN_FORKS;
                    INV_8CB85__tmpE.invokeid = INV_8CB85;
                    INV_8CB85__tmpE.origin = INV_8CB85;
                    _lastSeqId = _lastSeqId + 1;
                    INV_8CB85__tmpE.delay = 0;
                    INV_8CB85__tmpE.seqNr = _lastSeqId;
                    INV_8CB85__tmpE.data.p_id = INV_8CB85_p_id;
#if TRACE_EXECUTION
printf("%d: Sending RETURN_FORKS (%d) to ROOT_eQ\n", _pid, INV_8CB85__tmpE.name );
#endif

                    ROOT_eQ!INV_8CB85__tmpE;
                    insertWithDelay(ROOT_eQ);
                  }
                  skip;
                }
                :: else -> skip;
                fi
                skip;
              }
              :: j == 4 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, j);
#endif

                skip;
              }
              :: j == 5 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, j);
#endif

                if
                :: !INV_8CB85_flags[USCXML_CTX_FINISHED] || INV_8CB85_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
                  {
                    INV_8CB85__tmpE.data.p_id = 0;
                    INV_8CB85__tmpE.delay = 0;
                    INV_8CB85__tmpE.invokeid = 0;
                    INV_8CB85__tmpE.name = 0;
                    INV_8CB85__tmpE.origin = 0;
                    INV_8CB85__tmpE.sendid = 0;
                    INV_8CB85__tmpE.seqNr = 0;
                    INV_8CB85__tmpE.name = NEED_FORKS;
                    INV_8CB85__tmpE.invokeid = INV_8CB85;
                    INV_8CB85__tmpE.origin = INV_8CB85;
                    _lastSeqId = _lastSeqId + 1;
                    INV_8CB85__tmpE.delay = 0;
                    INV_8CB85__tmpE.seqNr = _lastSeqId;
                    INV_8CB85__tmpE.data.p_id = INV_8CB85_p_id;
#if TRACE_EXECUTION
printf("%d: Sending NEED_FORKS (%d) to ROOT_eQ\n", _pid, INV_8CB85__tmpE.name );
#endif

                    ROOT_eQ!INV_8CB85__tmpE;
                    insertWithDelay(ROOT_eQ);
                  }
                  skip;
                }
                :: else -> skip;
                fi
                skip;
              }
              :: j == 6 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, j);
#endif

                printf("philospher: : %d", INV_8CB85_p_id);
                printf("Time(in ms) since resource denied: : %d", INV_8CB85_delay);
                skip;
              }
              :: else ->skip;
              fi

           }
           :: else -> skip;
           fi
           j = j + 1;
         }
         :: else -> break;
         od
         /* handle final states */
         if
         :: INV_8CB85_states[i].type[USCXML_STATE_FINAL] -> {
           if
           :: INV_8CB85_states[INV_8CB85_states[i].parent].children[1] -> {
             /* exit topmost SCXML state */
             INV_8CB85_flags[USCXML_CTX_TOP_LEVEL_FINAL] = true;
             INV_8CB85_flags[USCXML_CTX_FINISHED] = true;
           }
           :: else -> {
             /* raise done event */
             if
             :: else -> skip;
             fi
           }
           fi
           /**
            * are we the last final state to leave a parallel state?:
            * 1. Gather all parallel states in our ancestor chain
            * 2. Find all states for which these parallels are ancestors
            * 3. Iterate all active final states and remove their ancestors
            * 4. If a state remains, not all children of a parallel are final
            */
            j = 0;
            do
            :: j < INV_8CB85_USCXML_NUMBER_STATES -> {
              if
              :: INV_8CB85_states[j].type[USCXML_STATE_PARALLEL] && INV_8CB85_states[i].ancestors[j] -> {
                INV_8CB85_STATES_CLEAR(INV_8CB85_ctx.tmp_states)
                k = 0;
                do
                :: k < INV_8CB85_USCXML_NUMBER_STATES -> {
                  if
                  :: INV_8CB85_states[k].ancestors[j] && INV_8CB85_config[k] -> {
                    if
                    :: INV_8CB85_states[k].type[USCXML_STATE_FINAL] -> {
                      INV_8CB85_STATES_AND_NOT(INV_8CB85_ctx.tmp_states, INV_8CB85_states[k].ancestors)
                    }
                    :: else -> {
                      INV_8CB85_ctx.tmp_states[k] = true;
                    }
                    fi
                  }
                  :: else -> skip;
                  fi
                  k = k + 1;
                }
                :: else -> break;
                od
                if
                :: !INV_8CB85_STATES_HAS_ANY(INV_8CB85_ctx.tmp_states) -> {
                  if
                  :: else -> skip;
                  fi
                }
                :: else -> skip;
                fi
              }
              :: else -> skip;
              fi
              j = j + 1;
            }
            :: else -> break;
            od
         }
         :: else -> skip;
         fi

    }
    :: else -> skip;
    i = i + 1;
    fi;
  }
  :: else -> break;
  od;

  }
  :: else -> skip;
  fi /* USCXML_CTX_TRANSITION_FOUND */
  } skip; /* d_step */
} /* !USCXML_CTX_FINISHED */
:: else -> break;
od

/* ---------------------------- */
INV_8CB85_TERMINATE_MACHINE:
skip; d_step {

#if TRACE_EXECUTION
printf("%d: Machine finished\n", _pid);
#endif

/* exit all remaining states */
i = INV_8CB85_USCXML_NUMBER_STATES;
do
:: i > 0 -> {
  i = i - 1;
  if
  :: INV_8CB85_config[i] && INV_8CB85_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
    /* call all on exit handlers */
   if
    :: i == 5 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for exiting state %d\n", _pid, i);
#endif

    if
    :: (INV_8CB85__event.name == TAKE_FORKS) -> {
        cancelSendId(RESOURCE_DENIED_TIMER,INV_8CB85);
    }
    :: else -> skip;
    fi;
    }
    :: else -> skip;
    fi

    skip;
    
  }
  :: else -> skip;
  fi;

  if
  :: INV_8CB85_invocations[i] -> {
    /* cancel invocations */
    INV_8CB85_invocations[i] = false;
    if
    :: else -> skip;
    fi
    skip;

  }
  :: else -> skip;
  fi;
}
:: else -> break;
od;


#if TRACE_EXECUTION
printf("%d: Removing pending events\n", _pid);
#endif

removePendingEventsFromInvoker(INV_8CB85)
/* send done event */
if
:: INV_8CB85_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
    INV_8CB85__tmpE.data.p_id = 0;
    INV_8CB85__tmpE.delay = 0;
    INV_8CB85__tmpE.invokeid = 0;
    INV_8CB85__tmpE.name = 0;
    INV_8CB85__tmpE.origin = 0;
    INV_8CB85__tmpE.sendid = 0;
    INV_8CB85__tmpE.seqNr = 0;

    INV_8CB85__tmpE.name = DONE_INVOKE_INV_8CB85
    INV_8CB85__tmpE.invokeid = INV_8CB85

#if TRACE_EXECUTION
printf("%d: Sending DONE.INVOKE\n", _pid);
#endif

    ROOT_eQ!INV_8CB85__tmpE;
    insertWithDelay(ROOT_eQ);
}
:: else -> skip
fi;

} /* d_step */


#if TRACE_EXECUTION
printf("%d: Done\n", _pid);
#endif

} } /* atomic, step() */


/* machine microstep function */
#define INV_5C805_USCXML_NUMBER_STATES 7
#define INV_5C805_USCXML_NUMBER_TRANS 7

proctype INV_5C805_step() { atomic {

INV_5C805_procid = _pid;
unsigned i : 3,  j : 3,  k : 3;


/* ---------------------------- */
INV_5C805_MICROSTEP:
do
:: !INV_5C805_flags[USCXML_CTX_FINISHED] -> {
  /* Run until machine is finished */


#if TRACE_EXECUTION
printf("%d: Taking a step\n", _pid);
#endif

  /* Dequeue an event */
  INV_5C805_flags[USCXML_CTX_DEQUEUE_EXTERNAL] = false;
  if
  ::INV_5C805_flags[USCXML_CTX_SPONTANEOUS] -> {
    INV_5C805__event.name = USCXML_EVENT_SPONTANEOUS;

#if TRACE_EXECUTION
printf("%d: Trying with a spontaneous event\n", _pid);
#endif

  }
  :: else -> {
    if
    :: len(INV_5C805_iQ) != 0 -> {
      INV_5C805_iQ ? INV_5C805__event;

#if TRACE_EXECUTION
printf("%d: Deqeued an internal event\n", _pid);
#endif

    }
    :: else -> {
      INV_5C805_flags[USCXML_CTX_DEQUEUE_EXTERNAL] = true;
    }
    fi;
  }
  fi;


  if
  :: INV_5C805_flags[USCXML_CTX_DEQUEUE_EXTERNAL] -> {
    /* manage invocations */
    i = 0;
    do
    :: i < INV_5C805_USCXML_NUMBER_STATES -> {
      d_step { 
      /* uninvoke */
      if
      :: !INV_5C805_config[i] && INV_5C805_invocations[i] -> {

#if TRACE_EXECUTION
printf("%d: Uninvoking in state %d\n", _pid, i);
#endif

        if
        :: else -> skip;
        fi
        INV_5C805_invocations[i] = false;
        skip;
      }
      :: else -> skip;
      fi;
      } /* d_step */

      /* invoke */
      if
      :: INV_5C805_config[i] && !INV_5C805_invocations[i] -> {
        if
        :: else -> skip;
        fi
      }
      :: else -> skip;
      fi;
      i = i + 1;
    }
    :: else -> break;
    od;

    /* Determine machines with smallest delay and set their process priority */
    scheduleMachines();

    /* we may return to find ourselves terminated */
    if
    :: INV_5C805_flags[USCXML_CTX_FINISHED] -> {
      goto INV_5C805_TERMINATE_MACHINE;
    }
    :: else -> skip;
    fi
    /* Not sure if this should be before the invocation due to auto-forwarding */
    if
    :: len(INV_5C805_eQ) != 0 -> {
      INV_5C805_eQ ? INV_5C805__event;

#if TRACE_EXECUTION
printf("%d: Deqeued an external event\n", _pid);
#endif

    }
    fi;
  }
  :: else -> skip;
  fi


d_step { skip;

/* ---------------------------- */
INV_5C805_SELECT_TRANSITIONS:
INV_5C805_STATES_CLEAR(INV_5C805_ctx.target_set)
INV_5C805_STATES_CLEAR(INV_5C805_ctx.exit_set)
INV_5C805_TRANS_CLEAR(INV_5C805_ctx.conflicts)
INV_5C805_TRANS_CLEAR(INV_5C805_ctx.trans_set)
#if TRACE_EXECUTION
printf("%d: Establishing optimal transition set for event %d\n", _pid, INV_5C805__event.name );
#endif

#if TRACE_EXECUTION
printf("Configuration: ");
printf("%d%d%d%d%d%d%d", 
    INV_5C805_config[0], 
    INV_5C805_config[1], 
    INV_5C805_config[2], 
    INV_5C805_config[3], 
    INV_5C805_config[4], 
    INV_5C805_config[5], 
    INV_5C805_config[6]);
printf("\n");
#endif

  INV_5C805_flags[USCXML_CTX_TRANSITION_FOUND] = false;
  i = 0;
  do
  :: i < INV_5C805_USCXML_NUMBER_TRANS -> {
    /* only select non-history, non-initial transitions */
    if
    :: !INV_5C805_transitions[i].type[USCXML_TRANS_HISTORY] &&
       !INV_5C805_transitions[i].type[USCXML_TRANS_INITIAL] -> {
      if
      :: /* is the transition active? */
         INV_5C805_config[INV_5C805_transitions[i].source] && 

         /* is it non-conflicting? */
         !INV_5C805_ctx.conflicts[i] && 

         /* is it spontaneous with an event or vice versa? */
         ((INV_5C805__event.name == USCXML_EVENT_SPONTANEOUS && 
           INV_5C805_transitions[i].type[USCXML_TRANS_SPONTANEOUS]) || 
          (INV_5C805__event.name != USCXML_EVENT_SPONTANEOUS && 
           !INV_5C805_transitions[i].type[USCXML_TRANS_SPONTANEOUS])) &&

         /* is it matching and enabled? */
         (false 
          || (i == 0 && (false || INV_5C805__event.name == THINKING_OVER))
          || (i == 1 && (false || INV_5C805__event.name == TAKE_FORKS))
          || (i == 2 && (false || INV_5C805__event.name == RESOURCE_DENIED))
          || (i == 3 && (false || INV_5C805__event.name == EATING_OVER))
          || (i == 4 && (false || INV_5C805__event.name == TAKE_FORKS))
          || (i == 5 && (false || INV_5C805__event.name == RESEND_NEED_FORKS))
          || (i == 6 && (false || INV_5C805__event.name == TIMEOUT))
         ) -> {
        /* remember that we found a transition */
        INV_5C805_flags[USCXML_CTX_TRANSITION_FOUND] = true;

        /* transitions that are pre-empted */
        INV_5C805_TRANS_OR(INV_5C805_ctx.conflicts, INV_5C805_transitions[i].conflicts)

        /* states that are directly targeted (resolve as entry-set later) */
        INV_5C805_STATES_OR(INV_5C805_ctx.target_set, INV_5C805_transitions[i].target)

        /* states that will be left */
        INV_5C805_STATES_OR(INV_5C805_ctx.exit_set, INV_5C805_transitions[i].exit_set)

        INV_5C805_ctx.trans_set[i] = true;
      }
      :: else {
        skip;
      }
      fi
    }
    :: else -> {
      skip;
    }
    fi
    i = i + 1;
  }
  :: else -> break;
  od;
  INV_5C805_STATES_AND(INV_5C805_ctx.exit_set, INV_5C805_config)

#if TRACE_EXECUTION
printf("Selected Transitions: ");
printf("%d%d%d%d%d%d%d", 
    INV_5C805_ctx.trans_set[0], 
    INV_5C805_ctx.trans_set[1], 
    INV_5C805_ctx.trans_set[2], 
    INV_5C805_ctx.trans_set[3], 
    INV_5C805_ctx.trans_set[4], 
    INV_5C805_ctx.trans_set[5], 
    INV_5C805_ctx.trans_set[6]);
printf("\n");
#endif


#if TRACE_EXECUTION
printf("Target Set: ");
printf("%d%d%d%d%d%d%d", 
    INV_5C805_ctx.target_set[0], 
    INV_5C805_ctx.target_set[1], 
    INV_5C805_ctx.target_set[2], 
    INV_5C805_ctx.target_set[3], 
    INV_5C805_ctx.target_set[4], 
    INV_5C805_ctx.target_set[5], 
    INV_5C805_ctx.target_set[6]);
printf("\n");
#endif


#if TRACE_EXECUTION
printf("Exit Set: ");
printf("%d%d%d%d%d%d%d", 
    INV_5C805_ctx.exit_set[0], 
    INV_5C805_ctx.exit_set[1], 
    INV_5C805_ctx.exit_set[2], 
    INV_5C805_ctx.exit_set[3], 
    INV_5C805_ctx.exit_set[4], 
    INV_5C805_ctx.exit_set[5], 
    INV_5C805_ctx.exit_set[6]);
printf("\n");
#endif

  if
  :: !INV_5C805_STATES_HAS_ANY(INV_5C805_config) -> {
    /* Enter initial configuration */
    INV_5C805_STATES_COPY(INV_5C805_ctx.target_set, INV_5C805_states[0].completion)
    INV_5C805_flags[USCXML_CTX_SPONTANEOUS] = true;
    INV_5C805_flags[USCXML_CTX_TRANSITION_FOUND] = true;

#if TRACE_EXECUTION
printf("%d: Entering initial default completion\n", _pid);
#endif


  }
  :: INV_5C805_flags[USCXML_CTX_TRANSITION_FOUND] -> {

#if TRACE_EXECUTION
printf("%d: Found transitions\n", _pid);
#endif

    INV_5C805_flags[USCXML_CTX_SPONTANEOUS] = true;
  }
  :: else {
    INV_5C805_flags[USCXML_CTX_SPONTANEOUS] = false;

#if TRACE_EXECUTION
printf("%d: Found NO transitions\n", _pid);
#endif

  }
  fi


  if
  :: INV_5C805_flags[USCXML_CTX_TRANSITION_FOUND] -> {
    /* only process anything if we found transitions or are on initial entry */
/* ---------------------------- */
/* REMEMBER_HISTORY: */

#if TRACE_EXECUTION
printf("%d: Save history configurations\n", _pid);
#endif

  if
  :: INV_5C805_STATES_HAS_ANY(INV_5C805_config) -> {
    /* only remember history on non-initial entry */
    i = 0;
    do
    :: i < INV_5C805_USCXML_NUMBER_STATES -> {
      if
      :: INV_5C805_states[i].type[USCXML_STATE_HISTORY_SHALLOW] ||
         INV_5C805_states[i].type[USCXML_STATE_HISTORY_DEEP] -> {
        if
        :: INV_5C805_ctx.exit_set[INV_5C805_states[i].parent] -> {
          /* a history state whose parent is about to be exited */

#if TRACE_EXECUTION
printf("%d: history state %d is about to be exited\n", _pid, i);
#endif


#if TRACE_EXECUTION
printf("COMPLET: ");
printf("%d%d%d%d%d%d%d", 
    INV_5C805_states[i].completion[0], 
    INV_5C805_states[i].completion[1], 
    INV_5C805_states[i].completion[2], 
    INV_5C805_states[i].completion[3], 
    INV_5C805_states[i].completion[4], 
    INV_5C805_states[i].completion[5], 
    INV_5C805_states[i].completion[6]);
printf("\n");
#endif

          INV_5C805_STATES_COPY(INV_5C805_ctx.tmp_states, INV_5C805_states[i].completion)

          /* set those states who were enabled */
          INV_5C805_STATES_AND(INV_5C805_ctx.tmp_states, INV_5C805_config)

#if TRACE_EXECUTION
printf("CONFIG : ");
printf("%d%d%d%d%d%d%d", 
    INV_5C805_config[0], 
    INV_5C805_config[1], 
    INV_5C805_config[2], 
    INV_5C805_config[3], 
    INV_5C805_config[4], 
    INV_5C805_config[5], 
    INV_5C805_config[6]);
printf("\n");
#endif


#if TRACE_EXECUTION
printf("TMP_STS: ");
printf("%d%d%d%d%d%d%d", 
    INV_5C805_ctx.tmp_states[0], 
    INV_5C805_ctx.tmp_states[1], 
    INV_5C805_ctx.tmp_states[2], 
    INV_5C805_ctx.tmp_states[3], 
    INV_5C805_ctx.tmp_states[4], 
    INV_5C805_ctx.tmp_states[5], 
    INV_5C805_ctx.tmp_states[6]);
printf("\n");
#endif


          /* clear current history with completion mask */
          INV_5C805_STATES_AND_NOT(INV_5C805_history, INV_5C805_states[i].completion)

          /* set history */
          INV_5C805_STATES_OR(INV_5C805_history, INV_5C805_ctx.tmp_states)

        }
        :: else -> skip;
        fi;
      }
      :: else -> skip;
      fi;
      i = i + 1;
    }
    :: else -> break;
    od;


#if TRACE_EXECUTION
printf("History: ");
printf("%d%d%d%d%d%d%d", 
    INV_5C805_history[0], 
    INV_5C805_history[1], 
    INV_5C805_history[2], 
    INV_5C805_history[3], 
    INV_5C805_history[4], 
    INV_5C805_history[5], 
    INV_5C805_history[6]);
printf("\n");
#endif
  }
  :: else -> skip;
  fi;

/* ---------------------------- */
INV_5C805_ESTABLISH_ENTRY_SET:
  /* calculate new entry set */
  INV_5C805_STATES_COPY(INV_5C805_ctx.entry_set, INV_5C805_ctx.target_set)

  i = 0;
  do
  :: i < INV_5C805_USCXML_NUMBER_STATES -> {
    if
    :: INV_5C805_ctx.entry_set[i] -> {
      /* ancestor completion */
      INV_5C805_STATES_OR(INV_5C805_ctx.entry_set, INV_5C805_states[i].ancestors)
    }
    :: else -> skip;
    fi;
    i = i + 1;
  }
  :: else -> break;
  od;

  /* iterate for descendants */
  i = 0;
  do
  :: i < INV_5C805_USCXML_NUMBER_STATES -> {
    if
    :: INV_5C805_ctx.entry_set[i] -> {
      if
      :: INV_5C805_states[i].type[USCXML_STATE_PARALLEL] -> {
        INV_5C805_STATES_OR(INV_5C805_ctx.entry_set, INV_5C805_states[i].completion)
      }
      :: INV_5C805_states[i].type[USCXML_STATE_HISTORY_SHALLOW] ||
         INV_5C805_states[i].type[USCXML_STATE_HISTORY_DEEP] -> {

#if TRACE_EXECUTION
printf("%d: Descendant completion for history state %d\n", _pid, i);
#endif

        if
        :: !INV_5C805_STATES_HAS_AND(INV_5C805_states[i].completion, INV_5C805_history) && !INV_5C805_config[INV_5C805_states[i].parent] -> {
          /* nothing set for history, look for a default transition */

#if TRACE_EXECUTION
printf("%d: Fresh history in target set\n", _pid);
#endif

          j = 0;
          do
          :: j < INV_5C805_USCXML_NUMBER_TRANS -> {
             if
             :: INV_5C805_transitions[j].source == i -> {
               INV_5C805_ctx.trans_set[j] = true;
               INV_5C805_STATES_OR(INV_5C805_ctx.entry_set, INV_5C805_transitions[j].target)

               if
               :: (INV_5C805_states[i].type[USCXML_STATE_HISTORY_DEEP] &&
                   !INV_5C805_STATES_HAS_AND(INV_5C805_transitions[j].target, INV_5C805_states[i].children)                  ) -> {
                 k = i + 1
                 do
                 :: k < INV_5C805_USCXML_NUMBER_STATES -> {
                   if
                   :: INV_5C805_transitions[j].target[k] -> {
                     INV_5C805_STATES_OR(INV_5C805_ctx.entry_set, INV_5C805_states[k].ancestors)
                     break;

                   }
                   :: else -> skip;
                   fi
                   k = k + 1;
                 }
                 :: else -> break;
                 od
               }
               :: else -> skip;
               fi
               break;
             }
             :: else -> skip;
             fi
             j = j + 1;
          }
          :: else -> break
          od
          skip;
        }
        :: else -> {

#if TRACE_EXECUTION
printf("%d: Established history in target set\n", _pid);
#endif

          INV_5C805_STATES_COPY(INV_5C805_ctx.tmp_states, INV_5C805_states[i].completion)
          INV_5C805_STATES_AND(INV_5C805_ctx.tmp_states, INV_5C805_history)
          INV_5C805_STATES_OR(INV_5C805_ctx.entry_set, INV_5C805_ctx.tmp_states)
          if
          :: INV_5C805_states[i].type[USCXML_STATE_HAS_HISTORY] ||
             INV_5C805_states[i].type[USCXML_STATE_HISTORY_DEEP] -> { 
            /* a deep history state with nested histories -> more completion */

#if TRACE_EXECUTION
printf("%d: DEEP HISTORY\n", _pid);
#endif

            j = i + 1;
            do
            :: j < INV_5C805_USCXML_NUMBER_STATES -> {
              if
              :: (INV_5C805_states[i].completion[j] &&
                  INV_5C805_ctx.entry_set[j] && 
                  INV_5C805_states[j].type[USCXML_STATE_HAS_HISTORY]) -> {
                k = j + 1;
                do
                :: k < INV_5C805_USCXML_NUMBER_STATES -> {
                  /* add nested history to entry_set */
                  if
                  :: (INV_5C805_states[k].type[USCXML_STATE_HISTORY_DEEP] ||
                      INV_5C805_states[k].type[USCXML_STATE_HISTORY_SHALLOW]) &&
                     INV_5C805_states[j].children[k] -> {
                    /* a nested history state */
                    INV_5C805_ctx.entry_set[k] = true;
                  }
                  :: else -> skip;
                  fi
                  k = k + 1;
                }
                :: else -> break;
                od
              }
              :: else -> skip;
              fi
            }
            j = j + 1;
            :: else -> break;
            od
          }
          :: else -> skip;
          fi
        }
        fi;
      }
      :: INV_5C805_states[i].type[USCXML_STATE_INITIAL] -> {

#if TRACE_EXECUTION
printf("%d: Descendant completion for initial state %d\n", _pid, i);
#endif

        j = 0
        do
        :: j < INV_5C805_USCXML_NUMBER_TRANS -> {
          if
          :: INV_5C805_transitions[j].source == i -> {
            INV_5C805_ctx.trans_set[j] = true;
            INV_5C805_ctx.entry_set[i] = false;

#if TRACE_EXECUTION
printf("%d: Adding transition %d!\n", _pid, j);
#endif

            INV_5C805_STATES_OR(INV_5C805_ctx.entry_set, INV_5C805_transitions[j].target)

            k = i + 1;
            do
            :: k < INV_5C805_USCXML_NUMBER_STATES -> {
              if
              :: INV_5C805_transitions[j].target[k] -> {
                INV_5C805_STATES_OR(INV_5C805_ctx.entry_set, INV_5C805_states[k].ancestors)

              }
              :: else -> break;
              fi
              k = k + 1;
            }
            :: else -> break
            od
          }
          :: else -> skip;
          fi
          j = j + 1;
        }
        :: else -> break
        od;
      }
      :: INV_5C805_states[i].type[USCXML_STATE_COMPOUND] -> {
        /* we need to check whether one child is already in entry_set */
        if
        :: (
          !INV_5C805_STATES_HAS_AND(INV_5C805_ctx.entry_set, INV_5C805_states[i].children) && 
           (!INV_5C805_STATES_HAS_AND(INV_5C805_config, INV_5C805_states[i].children) || INV_5C805_STATES_HAS_AND(INV_5C805_ctx.exit_set, INV_5C805_states[i].children)
)) 
        -> {
          INV_5C805_STATES_OR(INV_5C805_ctx.entry_set, INV_5C805_states[i].completion)
          if
          :: (INV_5C805_STATES_HAS_AND(INV_5C805_states[i].completion, INV_5C805_states[i].children)
          ) -> {
            /* deep completion */
            j = i + 1;
            do
            :: j < INV_5C805_USCXML_NUMBER_STATES - 1 -> {
              j = j + 1;
              if
              :: INV_5C805_states[i].completion[j] -> {
                INV_5C805_STATES_OR(INV_5C805_ctx.entry_set, INV_5C805_states[j].ancestors)

                /* completion of compound is single state */
                break;
              } 
              :: else -> skip;
              fi
            }
            :: else -> break;
            od
          }
          :: else -> skip;
          fi
        }
        :: else -> skip;
        fi
      }
      :: else -> skip;
      fi;
    }
    :: else -> skip;
    fi;
    i = i + 1;
  }
  :: else -> break;
  od;


#if TRACE_EXECUTION
printf("Entry Set");
printf("%d%d%d%d%d%d%d", 
    INV_5C805_ctx.entry_set[0], 
    INV_5C805_ctx.entry_set[1], 
    INV_5C805_ctx.entry_set[2], 
    INV_5C805_ctx.entry_set[3], 
    INV_5C805_ctx.entry_set[4], 
    INV_5C805_ctx.entry_set[5], 
    INV_5C805_ctx.entry_set[6]);
printf("\n");
#endif


/* ---------------------------- */
/* EXIT_STATES: */
  i = INV_5C805_USCXML_NUMBER_STATES;
  do
  :: i > 0 -> {
    i = i - 1;
    if
    :: INV_5C805_ctx.exit_set[i] && INV_5C805_config[i] -> {
      /* call all on-exit handlers */

#if TRACE_EXECUTION
printf("%d: Exiting state %d\n", _pid, i);
#endif

      if
      :: i == 5 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for exiting state %d\n", _pid, i);
#endif

      if
      :: (INV_5C805__event.name == TAKE_FORKS) -> {
          cancelSendId(RESOURCE_DENIED_TIMER,INV_5C805);
      }
      :: else -> skip;
      fi;
      }
      :: else -> skip;
      fi

      INV_5C805_config[i] = false;
      skip;
    }
    :: else -> skip;
    fi;
  }
  :: else -> break;
  od;


/* ---------------------------- */
/* TAKE_TRANSITIONS: */
  i = 0;
  do
  :: i < INV_5C805_USCXML_NUMBER_TRANS -> {
    if
    :: INV_5C805_ctx.trans_set[i] && 
       !INV_5C805_transitions[i].type[USCXML_TRANS_HISTORY] && 
       !INV_5C805_transitions[i].type[USCXML_TRANS_INITIAL] -> {
      /* Call executable content in normal transition */

#if TRACE_EXECUTION
printf("%d: Taking transition %d\n", _pid, i);
#endif

      if
      :: i == 0 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, i);
#endif

        skip;
      }
      :: i == 1 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, i);
#endif

        skip;
      }
      :: i == 2 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, i);
#endif

        skip;
      }
      :: i == 3 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, i);
#endif

        if
        :: !INV_5C805_flags[USCXML_CTX_FINISHED] || INV_5C805_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
          {
            INV_5C805__tmpE.data.p_id = 0;
            INV_5C805__tmpE.delay = 0;
            INV_5C805__tmpE.invokeid = 0;
            INV_5C805__tmpE.name = 0;
            INV_5C805__tmpE.origin = 0;
            INV_5C805__tmpE.sendid = 0;
            INV_5C805__tmpE.seqNr = 0;
            INV_5C805__tmpE.name = RETURN_FORKS;
            INV_5C805__tmpE.invokeid = INV_5C805;
            INV_5C805__tmpE.origin = INV_5C805;
            _lastSeqId = _lastSeqId + 1;
            INV_5C805__tmpE.delay = 0;
            INV_5C805__tmpE.seqNr = _lastSeqId;
            INV_5C805__tmpE.data.p_id = INV_5C805_p_id;
#if TRACE_EXECUTION
printf("%d: Sending RETURN_FORKS (%d) to ROOT_eQ\n", _pid, INV_5C805__tmpE.name );
#endif

            ROOT_eQ!INV_5C805__tmpE;
            insertWithDelay(ROOT_eQ);
          }
          skip;
        }
        :: else -> skip;
        fi
        skip;
      }
      :: i == 4 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, i);
#endif

        skip;
      }
      :: i == 5 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, i);
#endif

        if
        :: !INV_5C805_flags[USCXML_CTX_FINISHED] || INV_5C805_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
          {
            INV_5C805__tmpE.data.p_id = 0;
            INV_5C805__tmpE.delay = 0;
            INV_5C805__tmpE.invokeid = 0;
            INV_5C805__tmpE.name = 0;
            INV_5C805__tmpE.origin = 0;
            INV_5C805__tmpE.sendid = 0;
            INV_5C805__tmpE.seqNr = 0;
            INV_5C805__tmpE.name = NEED_FORKS;
            INV_5C805__tmpE.invokeid = INV_5C805;
            INV_5C805__tmpE.origin = INV_5C805;
            _lastSeqId = _lastSeqId + 1;
            INV_5C805__tmpE.delay = 0;
            INV_5C805__tmpE.seqNr = _lastSeqId;
            INV_5C805__tmpE.data.p_id = INV_5C805_p_id;
#if TRACE_EXECUTION
printf("%d: Sending NEED_FORKS (%d) to ROOT_eQ\n", _pid, INV_5C805__tmpE.name );
#endif

            ROOT_eQ!INV_5C805__tmpE;
            insertWithDelay(ROOT_eQ);
          }
          skip;
        }
        :: else -> skip;
        fi
        skip;
      }
      :: i == 6 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, i);
#endif

        printf("philospher: : %d", INV_5C805_p_id);
        printf("Time(in ms) since resource denied: : %d", INV_5C805_delay);
        skip;
      }
      :: else ->skip;
      fi

    }
    :: else -> skip;
    fi;
    i = i + 1;
  }
  :: else -> break;
  od;

/* ---------------------------- */
/* ENTER_STATES: */
  i = 0;
  do
  :: i < INV_5C805_USCXML_NUMBER_STATES -> {
    if
    :: (INV_5C805_ctx.entry_set[i] &&
        !INV_5C805_config[i] && 
        /* these are no proper states */
        !INV_5C805_states[i].type[USCXML_STATE_HISTORY_DEEP] && 
        !INV_5C805_states[i].type[USCXML_STATE_HISTORY_SHALLOW] && 
        !INV_5C805_states[i].type[USCXML_STATE_INITIAL]
       ) -> {

#if TRACE_EXECUTION
printf("%d: Entering state %d\n", _pid, i);
#endif

         INV_5C805_config[i] = true;

         /* Process executable content for entering a state */
         if
         :: i == 1 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for entering state %d\n", _pid, i);
#endif

          printf("Hello, I am philospher number: : %d", INV_5C805_p_id);
         }
         :: i == 2 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for entering state %d\n", _pid, i);
#endif

          printf("Thinking professor: : %d", INV_5C805_p_id);
            INV_5C805_random_delay = ((1103515245*INV_5C805_random_delay+12345)%2147483647)%2000;
          if
          :: !INV_5C805_flags[USCXML_CTX_FINISHED] || INV_5C805_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
            {
              INV_5C805__tmpE.data.p_id = 0;
              INV_5C805__tmpE.delay = 0;
              INV_5C805__tmpE.invokeid = 0;
              INV_5C805__tmpE.name = 0;
              INV_5C805__tmpE.origin = 0;
              INV_5C805__tmpE.sendid = 0;
              INV_5C805__tmpE.seqNr = 0;
              INV_5C805__tmpE.name = THINKING_OVER;
              INV_5C805__tmpE.invokeid = INV_5C805;
              INV_5C805__tmpE.origin = INV_5C805;
              _lastSeqId = _lastSeqId + 1;
              INV_5C805__tmpE.delay = INV_5C805_random_delay*(INV_5C805_p_id+1);
              INV_5C805__tmpE.seqNr = _lastSeqId;
#if TRACE_EXECUTION
printf("%d: Sending THINKING_OVER (%d) to INV_5C805_eQ\n", _pid, INV_5C805__tmpE.name );
#endif

              INV_5C805_eQ!INV_5C805__tmpE;
              insertWithDelay(INV_5C805_eQ);
            }
            skip;
          }
          :: else -> skip;
          fi
         }
         :: i == 3 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for entering state %d\n", _pid, i);
#endif

          printf("Hungry professor: : %d", INV_5C805_p_id);
          if
          :: !INV_5C805_flags[USCXML_CTX_FINISHED] || INV_5C805_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
            {
              INV_5C805__tmpE.data.p_id = 0;
              INV_5C805__tmpE.delay = 0;
              INV_5C805__tmpE.invokeid = 0;
              INV_5C805__tmpE.name = 0;
              INV_5C805__tmpE.origin = 0;
              INV_5C805__tmpE.sendid = 0;
              INV_5C805__tmpE.seqNr = 0;
              INV_5C805__tmpE.name = NEED_FORKS;
              INV_5C805__tmpE.invokeid = INV_5C805;
              INV_5C805__tmpE.origin = INV_5C805;
              _lastSeqId = _lastSeqId + 1;
              INV_5C805__tmpE.delay = 300;
              INV_5C805__tmpE.seqNr = _lastSeqId;
              INV_5C805__tmpE.data.p_id = INV_5C805_p_id;
#if TRACE_EXECUTION
printf("%d: Sending NEED_FORKS (%d) to ROOT_eQ\n", _pid, INV_5C805__tmpE.name );
#endif

              ROOT_eQ!INV_5C805__tmpE;
              insertWithDelay(ROOT_eQ);
            }
            skip;
          }
          :: else -> skip;
          fi
         }
         :: i == 4 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for entering state %d\n", _pid, i);
#endif

          printf("Eating professor: : %d", INV_5C805_p_id);
          if
          :: !INV_5C805_flags[USCXML_CTX_FINISHED] || INV_5C805_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
            {
              INV_5C805__tmpE.data.p_id = 0;
              INV_5C805__tmpE.delay = 0;
              INV_5C805__tmpE.invokeid = 0;
              INV_5C805__tmpE.name = 0;
              INV_5C805__tmpE.origin = 0;
              INV_5C805__tmpE.sendid = 0;
              INV_5C805__tmpE.seqNr = 0;
              INV_5C805__tmpE.name = EATING_OVER;
              INV_5C805__tmpE.invokeid = INV_5C805;
              INV_5C805__tmpE.origin = INV_5C805;
              _lastSeqId = _lastSeqId + 1;
              INV_5C805__tmpE.delay = 500;
              INV_5C805__tmpE.seqNr = _lastSeqId;
#if TRACE_EXECUTION
printf("%d: Sending EATING_OVER (%d) to INV_5C805_eQ\n", _pid, INV_5C805__tmpE.name );
#endif

              INV_5C805_eQ!INV_5C805__tmpE;
              insertWithDelay(INV_5C805_eQ);
            }
            skip;
          }
          :: else -> skip;
          fi
         }
         :: i == 5 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for entering state %d\n", _pid, i);
#endif

          printf("Resource Denied professor: : %d", INV_5C805_p_id);
          if
          :: !INV_5C805_flags[USCXML_CTX_FINISHED] || INV_5C805_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
            {
              INV_5C805__tmpE.data.p_id = 0;
              INV_5C805__tmpE.delay = 0;
              INV_5C805__tmpE.invokeid = 0;
              INV_5C805__tmpE.name = 0;
              INV_5C805__tmpE.origin = 0;
              INV_5C805__tmpE.sendid = 0;
              INV_5C805__tmpE.seqNr = 0;
              INV_5C805__tmpE.name = TIMEOUT;
              INV_5C805__tmpE.sendid = RESOURCE_DENIED_TIMER;
              INV_5C805__tmpE.invokeid = INV_5C805;
              INV_5C805__tmpE.origin = INV_5C805;
              _lastSeqId = _lastSeqId + 1;
              INV_5C805__tmpE.delay = INV_5C805_delay;
              INV_5C805__tmpE.seqNr = _lastSeqId;
#if TRACE_EXECUTION
printf("%d: Sending TIMEOUT (%d) to INV_5C805_eQ\n", _pid, INV_5C805__tmpE.name );
#endif

              INV_5C805_eQ!INV_5C805__tmpE;
              insertWithDelay(INV_5C805_eQ);
            }
            skip;
          }
          :: else -> skip;
          fi
          if
          :: !INV_5C805_flags[USCXML_CTX_FINISHED] || INV_5C805_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
            {
              INV_5C805__tmpE.data.p_id = 0;
              INV_5C805__tmpE.delay = 0;
              INV_5C805__tmpE.invokeid = 0;
              INV_5C805__tmpE.name = 0;
              INV_5C805__tmpE.origin = 0;
              INV_5C805__tmpE.sendid = 0;
              INV_5C805__tmpE.seqNr = 0;
              INV_5C805__tmpE.name = RESEND_NEED_FORKS;
              INV_5C805__tmpE.invokeid = INV_5C805;
              INV_5C805__tmpE.origin = INV_5C805;
              _lastSeqId = _lastSeqId + 1;
              INV_5C805__tmpE.delay = 300;
              INV_5C805__tmpE.seqNr = _lastSeqId;
#if TRACE_EXECUTION
printf("%d: Sending RESEND_NEED_FORKS (%d) to INV_5C805_eQ\n", _pid, INV_5C805__tmpE.name );
#endif

              INV_5C805_eQ!INV_5C805__tmpE;
              insertWithDelay(INV_5C805_eQ);
            }
            skip;
          }
          :: else -> skip;
          fi
         }
         :: else ->skip;
         fi

         /* take history and initial transitions */
         j = 0;
         do
         :: j < INV_5C805_USCXML_NUMBER_TRANS -> {
           if
           :: (INV_5C805_ctx.trans_set[j] &&
              (INV_5C805_transitions[j].type[USCXML_TRANS_HISTORY] ||
               INV_5C805_transitions[j].type[USCXML_TRANS_INITIAL]) && 
               INV_5C805_states[INV_5C805_transitions[j].source].parent == i) -> {
              /* Call executable content in history or initial transition */
              if
              :: j == 0 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, j);
#endif

                skip;
              }
              :: j == 1 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, j);
#endif

                skip;
              }
              :: j == 2 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, j);
#endif

                skip;
              }
              :: j == 3 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, j);
#endif

                if
                :: !INV_5C805_flags[USCXML_CTX_FINISHED] || INV_5C805_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
                  {
                    INV_5C805__tmpE.data.p_id = 0;
                    INV_5C805__tmpE.delay = 0;
                    INV_5C805__tmpE.invokeid = 0;
                    INV_5C805__tmpE.name = 0;
                    INV_5C805__tmpE.origin = 0;
                    INV_5C805__tmpE.sendid = 0;
                    INV_5C805__tmpE.seqNr = 0;
                    INV_5C805__tmpE.name = RETURN_FORKS;
                    INV_5C805__tmpE.invokeid = INV_5C805;
                    INV_5C805__tmpE.origin = INV_5C805;
                    _lastSeqId = _lastSeqId + 1;
                    INV_5C805__tmpE.delay = 0;
                    INV_5C805__tmpE.seqNr = _lastSeqId;
                    INV_5C805__tmpE.data.p_id = INV_5C805_p_id;
#if TRACE_EXECUTION
printf("%d: Sending RETURN_FORKS (%d) to ROOT_eQ\n", _pid, INV_5C805__tmpE.name );
#endif

                    ROOT_eQ!INV_5C805__tmpE;
                    insertWithDelay(ROOT_eQ);
                  }
                  skip;
                }
                :: else -> skip;
                fi
                skip;
              }
              :: j == 4 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, j);
#endif

                skip;
              }
              :: j == 5 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, j);
#endif

                if
                :: !INV_5C805_flags[USCXML_CTX_FINISHED] || INV_5C805_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
                  {
                    INV_5C805__tmpE.data.p_id = 0;
                    INV_5C805__tmpE.delay = 0;
                    INV_5C805__tmpE.invokeid = 0;
                    INV_5C805__tmpE.name = 0;
                    INV_5C805__tmpE.origin = 0;
                    INV_5C805__tmpE.sendid = 0;
                    INV_5C805__tmpE.seqNr = 0;
                    INV_5C805__tmpE.name = NEED_FORKS;
                    INV_5C805__tmpE.invokeid = INV_5C805;
                    INV_5C805__tmpE.origin = INV_5C805;
                    _lastSeqId = _lastSeqId + 1;
                    INV_5C805__tmpE.delay = 0;
                    INV_5C805__tmpE.seqNr = _lastSeqId;
                    INV_5C805__tmpE.data.p_id = INV_5C805_p_id;
#if TRACE_EXECUTION
printf("%d: Sending NEED_FORKS (%d) to ROOT_eQ\n", _pid, INV_5C805__tmpE.name );
#endif

                    ROOT_eQ!INV_5C805__tmpE;
                    insertWithDelay(ROOT_eQ);
                  }
                  skip;
                }
                :: else -> skip;
                fi
                skip;
              }
              :: j == 6 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, j);
#endif

                printf("philospher: : %d", INV_5C805_p_id);
                printf("Time(in ms) since resource denied: : %d", INV_5C805_delay);
                skip;
              }
              :: else ->skip;
              fi

           }
           :: else -> skip;
           fi
           j = j + 1;
         }
         :: else -> break;
         od
         /* handle final states */
         if
         :: INV_5C805_states[i].type[USCXML_STATE_FINAL] -> {
           if
           :: INV_5C805_states[INV_5C805_states[i].parent].children[1] -> {
             /* exit topmost SCXML state */
             INV_5C805_flags[USCXML_CTX_TOP_LEVEL_FINAL] = true;
             INV_5C805_flags[USCXML_CTX_FINISHED] = true;
           }
           :: else -> {
             /* raise done event */
             if
             :: else -> skip;
             fi
           }
           fi
           /**
            * are we the last final state to leave a parallel state?:
            * 1. Gather all parallel states in our ancestor chain
            * 2. Find all states for which these parallels are ancestors
            * 3. Iterate all active final states and remove their ancestors
            * 4. If a state remains, not all children of a parallel are final
            */
            j = 0;
            do
            :: j < INV_5C805_USCXML_NUMBER_STATES -> {
              if
              :: INV_5C805_states[j].type[USCXML_STATE_PARALLEL] && INV_5C805_states[i].ancestors[j] -> {
                INV_5C805_STATES_CLEAR(INV_5C805_ctx.tmp_states)
                k = 0;
                do
                :: k < INV_5C805_USCXML_NUMBER_STATES -> {
                  if
                  :: INV_5C805_states[k].ancestors[j] && INV_5C805_config[k] -> {
                    if
                    :: INV_5C805_states[k].type[USCXML_STATE_FINAL] -> {
                      INV_5C805_STATES_AND_NOT(INV_5C805_ctx.tmp_states, INV_5C805_states[k].ancestors)
                    }
                    :: else -> {
                      INV_5C805_ctx.tmp_states[k] = true;
                    }
                    fi
                  }
                  :: else -> skip;
                  fi
                  k = k + 1;
                }
                :: else -> break;
                od
                if
                :: !INV_5C805_STATES_HAS_ANY(INV_5C805_ctx.tmp_states) -> {
                  if
                  :: else -> skip;
                  fi
                }
                :: else -> skip;
                fi
              }
              :: else -> skip;
              fi
              j = j + 1;
            }
            :: else -> break;
            od
         }
         :: else -> skip;
         fi

    }
    :: else -> skip;
    i = i + 1;
    fi;
  }
  :: else -> break;
  od;

  }
  :: else -> skip;
  fi /* USCXML_CTX_TRANSITION_FOUND */
  } skip; /* d_step */
} /* !USCXML_CTX_FINISHED */
:: else -> break;
od

/* ---------------------------- */
INV_5C805_TERMINATE_MACHINE:
skip; d_step {

#if TRACE_EXECUTION
printf("%d: Machine finished\n", _pid);
#endif

/* exit all remaining states */
i = INV_5C805_USCXML_NUMBER_STATES;
do
:: i > 0 -> {
  i = i - 1;
  if
  :: INV_5C805_config[i] && INV_5C805_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
    /* call all on exit handlers */
   if
    :: i == 5 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for exiting state %d\n", _pid, i);
#endif

    if
    :: (INV_5C805__event.name == TAKE_FORKS) -> {
        cancelSendId(RESOURCE_DENIED_TIMER,INV_5C805);
    }
    :: else -> skip;
    fi;
    }
    :: else -> skip;
    fi

    skip;
    
  }
  :: else -> skip;
  fi;

  if
  :: INV_5C805_invocations[i] -> {
    /* cancel invocations */
    INV_5C805_invocations[i] = false;
    if
    :: else -> skip;
    fi
    skip;

  }
  :: else -> skip;
  fi;
}
:: else -> break;
od;


#if TRACE_EXECUTION
printf("%d: Removing pending events\n", _pid);
#endif

removePendingEventsFromInvoker(INV_5C805)
/* send done event */
if
:: INV_5C805_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
    INV_5C805__tmpE.data.p_id = 0;
    INV_5C805__tmpE.delay = 0;
    INV_5C805__tmpE.invokeid = 0;
    INV_5C805__tmpE.name = 0;
    INV_5C805__tmpE.origin = 0;
    INV_5C805__tmpE.sendid = 0;
    INV_5C805__tmpE.seqNr = 0;

    INV_5C805__tmpE.name = DONE_INVOKE_INV_5C805
    INV_5C805__tmpE.invokeid = INV_5C805

#if TRACE_EXECUTION
printf("%d: Sending DONE.INVOKE\n", _pid);
#endif

    ROOT_eQ!INV_5C805__tmpE;
    insertWithDelay(ROOT_eQ);
}
:: else -> skip
fi;

} /* d_step */


#if TRACE_EXECUTION
printf("%d: Done\n", _pid);
#endif

} } /* atomic, step() */


/* machine microstep function */
#define INV_F88AA_USCXML_NUMBER_STATES 7
#define INV_F88AA_USCXML_NUMBER_TRANS 7

proctype INV_F88AA_step() { atomic {

INV_F88AA_procid = _pid;
unsigned i : 3,  j : 3,  k : 3;


/* ---------------------------- */
INV_F88AA_MICROSTEP:
do
:: !INV_F88AA_flags[USCXML_CTX_FINISHED] -> {
  /* Run until machine is finished */


#if TRACE_EXECUTION
printf("%d: Taking a step\n", _pid);
#endif

  /* Dequeue an event */
  INV_F88AA_flags[USCXML_CTX_DEQUEUE_EXTERNAL] = false;
  if
  ::INV_F88AA_flags[USCXML_CTX_SPONTANEOUS] -> {
    INV_F88AA__event.name = USCXML_EVENT_SPONTANEOUS;

#if TRACE_EXECUTION
printf("%d: Trying with a spontaneous event\n", _pid);
#endif

  }
  :: else -> {
    if
    :: len(INV_F88AA_iQ) != 0 -> {
      INV_F88AA_iQ ? INV_F88AA__event;

#if TRACE_EXECUTION
printf("%d: Deqeued an internal event\n", _pid);
#endif

    }
    :: else -> {
      INV_F88AA_flags[USCXML_CTX_DEQUEUE_EXTERNAL] = true;
    }
    fi;
  }
  fi;


  if
  :: INV_F88AA_flags[USCXML_CTX_DEQUEUE_EXTERNAL] -> {
    /* manage invocations */
    i = 0;
    do
    :: i < INV_F88AA_USCXML_NUMBER_STATES -> {
      d_step { 
      /* uninvoke */
      if
      :: !INV_F88AA_config[i] && INV_F88AA_invocations[i] -> {

#if TRACE_EXECUTION
printf("%d: Uninvoking in state %d\n", _pid, i);
#endif

        if
        :: else -> skip;
        fi
        INV_F88AA_invocations[i] = false;
        skip;
      }
      :: else -> skip;
      fi;
      } /* d_step */

      /* invoke */
      if
      :: INV_F88AA_config[i] && !INV_F88AA_invocations[i] -> {
        if
        :: else -> skip;
        fi
      }
      :: else -> skip;
      fi;
      i = i + 1;
    }
    :: else -> break;
    od;

    /* Determine machines with smallest delay and set their process priority */
    scheduleMachines();

    /* we may return to find ourselves terminated */
    if
    :: INV_F88AA_flags[USCXML_CTX_FINISHED] -> {
      goto INV_F88AA_TERMINATE_MACHINE;
    }
    :: else -> skip;
    fi
    /* Not sure if this should be before the invocation due to auto-forwarding */
    if
    :: len(INV_F88AA_eQ) != 0 -> {
      INV_F88AA_eQ ? INV_F88AA__event;

#if TRACE_EXECUTION
printf("%d: Deqeued an external event\n", _pid);
#endif

    }
    fi;
  }
  :: else -> skip;
  fi


d_step { skip;

/* ---------------------------- */
INV_F88AA_SELECT_TRANSITIONS:
INV_F88AA_STATES_CLEAR(INV_F88AA_ctx.target_set)
INV_F88AA_STATES_CLEAR(INV_F88AA_ctx.exit_set)
INV_F88AA_TRANS_CLEAR(INV_F88AA_ctx.conflicts)
INV_F88AA_TRANS_CLEAR(INV_F88AA_ctx.trans_set)
#if TRACE_EXECUTION
printf("%d: Establishing optimal transition set for event %d\n", _pid, INV_F88AA__event.name );
#endif

#if TRACE_EXECUTION
printf("Configuration: ");
printf("%d%d%d%d%d%d%d", 
    INV_F88AA_config[0], 
    INV_F88AA_config[1], 
    INV_F88AA_config[2], 
    INV_F88AA_config[3], 
    INV_F88AA_config[4], 
    INV_F88AA_config[5], 
    INV_F88AA_config[6]);
printf("\n");
#endif

  INV_F88AA_flags[USCXML_CTX_TRANSITION_FOUND] = false;
  i = 0;
  do
  :: i < INV_F88AA_USCXML_NUMBER_TRANS -> {
    /* only select non-history, non-initial transitions */
    if
    :: !INV_F88AA_transitions[i].type[USCXML_TRANS_HISTORY] &&
       !INV_F88AA_transitions[i].type[USCXML_TRANS_INITIAL] -> {
      if
      :: /* is the transition active? */
         INV_F88AA_config[INV_F88AA_transitions[i].source] && 

         /* is it non-conflicting? */
         !INV_F88AA_ctx.conflicts[i] && 

         /* is it spontaneous with an event or vice versa? */
         ((INV_F88AA__event.name == USCXML_EVENT_SPONTANEOUS && 
           INV_F88AA_transitions[i].type[USCXML_TRANS_SPONTANEOUS]) || 
          (INV_F88AA__event.name != USCXML_EVENT_SPONTANEOUS && 
           !INV_F88AA_transitions[i].type[USCXML_TRANS_SPONTANEOUS])) &&

         /* is it matching and enabled? */
         (false 
          || (i == 0 && (false || INV_F88AA__event.name == THINKING_OVER))
          || (i == 1 && (false || INV_F88AA__event.name == TAKE_FORKS))
          || (i == 2 && (false || INV_F88AA__event.name == RESOURCE_DENIED))
          || (i == 3 && (false || INV_F88AA__event.name == EATING_OVER))
          || (i == 4 && (false || INV_F88AA__event.name == TAKE_FORKS))
          || (i == 5 && (false || INV_F88AA__event.name == RESEND_NEED_FORKS))
          || (i == 6 && (false || INV_F88AA__event.name == TIMEOUT))
         ) -> {
        /* remember that we found a transition */
        INV_F88AA_flags[USCXML_CTX_TRANSITION_FOUND] = true;

        /* transitions that are pre-empted */
        INV_F88AA_TRANS_OR(INV_F88AA_ctx.conflicts, INV_F88AA_transitions[i].conflicts)

        /* states that are directly targeted (resolve as entry-set later) */
        INV_F88AA_STATES_OR(INV_F88AA_ctx.target_set, INV_F88AA_transitions[i].target)

        /* states that will be left */
        INV_F88AA_STATES_OR(INV_F88AA_ctx.exit_set, INV_F88AA_transitions[i].exit_set)

        INV_F88AA_ctx.trans_set[i] = true;
      }
      :: else {
        skip;
      }
      fi
    }
    :: else -> {
      skip;
    }
    fi
    i = i + 1;
  }
  :: else -> break;
  od;
  INV_F88AA_STATES_AND(INV_F88AA_ctx.exit_set, INV_F88AA_config)

#if TRACE_EXECUTION
printf("Selected Transitions: ");
printf("%d%d%d%d%d%d%d", 
    INV_F88AA_ctx.trans_set[0], 
    INV_F88AA_ctx.trans_set[1], 
    INV_F88AA_ctx.trans_set[2], 
    INV_F88AA_ctx.trans_set[3], 
    INV_F88AA_ctx.trans_set[4], 
    INV_F88AA_ctx.trans_set[5], 
    INV_F88AA_ctx.trans_set[6]);
printf("\n");
#endif


#if TRACE_EXECUTION
printf("Target Set: ");
printf("%d%d%d%d%d%d%d", 
    INV_F88AA_ctx.target_set[0], 
    INV_F88AA_ctx.target_set[1], 
    INV_F88AA_ctx.target_set[2], 
    INV_F88AA_ctx.target_set[3], 
    INV_F88AA_ctx.target_set[4], 
    INV_F88AA_ctx.target_set[5], 
    INV_F88AA_ctx.target_set[6]);
printf("\n");
#endif


#if TRACE_EXECUTION
printf("Exit Set: ");
printf("%d%d%d%d%d%d%d", 
    INV_F88AA_ctx.exit_set[0], 
    INV_F88AA_ctx.exit_set[1], 
    INV_F88AA_ctx.exit_set[2], 
    INV_F88AA_ctx.exit_set[3], 
    INV_F88AA_ctx.exit_set[4], 
    INV_F88AA_ctx.exit_set[5], 
    INV_F88AA_ctx.exit_set[6]);
printf("\n");
#endif

  if
  :: !INV_F88AA_STATES_HAS_ANY(INV_F88AA_config) -> {
    /* Enter initial configuration */
    INV_F88AA_STATES_COPY(INV_F88AA_ctx.target_set, INV_F88AA_states[0].completion)
    INV_F88AA_flags[USCXML_CTX_SPONTANEOUS] = true;
    INV_F88AA_flags[USCXML_CTX_TRANSITION_FOUND] = true;

#if TRACE_EXECUTION
printf("%d: Entering initial default completion\n", _pid);
#endif


  }
  :: INV_F88AA_flags[USCXML_CTX_TRANSITION_FOUND] -> {

#if TRACE_EXECUTION
printf("%d: Found transitions\n", _pid);
#endif

    INV_F88AA_flags[USCXML_CTX_SPONTANEOUS] = true;
  }
  :: else {
    INV_F88AA_flags[USCXML_CTX_SPONTANEOUS] = false;

#if TRACE_EXECUTION
printf("%d: Found NO transitions\n", _pid);
#endif

  }
  fi


  if
  :: INV_F88AA_flags[USCXML_CTX_TRANSITION_FOUND] -> {
    /* only process anything if we found transitions or are on initial entry */
/* ---------------------------- */
/* REMEMBER_HISTORY: */

#if TRACE_EXECUTION
printf("%d: Save history configurations\n", _pid);
#endif

  if
  :: INV_F88AA_STATES_HAS_ANY(INV_F88AA_config) -> {
    /* only remember history on non-initial entry */
    i = 0;
    do
    :: i < INV_F88AA_USCXML_NUMBER_STATES -> {
      if
      :: INV_F88AA_states[i].type[USCXML_STATE_HISTORY_SHALLOW] ||
         INV_F88AA_states[i].type[USCXML_STATE_HISTORY_DEEP] -> {
        if
        :: INV_F88AA_ctx.exit_set[INV_F88AA_states[i].parent] -> {
          /* a history state whose parent is about to be exited */

#if TRACE_EXECUTION
printf("%d: history state %d is about to be exited\n", _pid, i);
#endif


#if TRACE_EXECUTION
printf("COMPLET: ");
printf("%d%d%d%d%d%d%d", 
    INV_F88AA_states[i].completion[0], 
    INV_F88AA_states[i].completion[1], 
    INV_F88AA_states[i].completion[2], 
    INV_F88AA_states[i].completion[3], 
    INV_F88AA_states[i].completion[4], 
    INV_F88AA_states[i].completion[5], 
    INV_F88AA_states[i].completion[6]);
printf("\n");
#endif

          INV_F88AA_STATES_COPY(INV_F88AA_ctx.tmp_states, INV_F88AA_states[i].completion)

          /* set those states who were enabled */
          INV_F88AA_STATES_AND(INV_F88AA_ctx.tmp_states, INV_F88AA_config)

#if TRACE_EXECUTION
printf("CONFIG : ");
printf("%d%d%d%d%d%d%d", 
    INV_F88AA_config[0], 
    INV_F88AA_config[1], 
    INV_F88AA_config[2], 
    INV_F88AA_config[3], 
    INV_F88AA_config[4], 
    INV_F88AA_config[5], 
    INV_F88AA_config[6]);
printf("\n");
#endif


#if TRACE_EXECUTION
printf("TMP_STS: ");
printf("%d%d%d%d%d%d%d", 
    INV_F88AA_ctx.tmp_states[0], 
    INV_F88AA_ctx.tmp_states[1], 
    INV_F88AA_ctx.tmp_states[2], 
    INV_F88AA_ctx.tmp_states[3], 
    INV_F88AA_ctx.tmp_states[4], 
    INV_F88AA_ctx.tmp_states[5], 
    INV_F88AA_ctx.tmp_states[6]);
printf("\n");
#endif


          /* clear current history with completion mask */
          INV_F88AA_STATES_AND_NOT(INV_F88AA_history, INV_F88AA_states[i].completion)

          /* set history */
          INV_F88AA_STATES_OR(INV_F88AA_history, INV_F88AA_ctx.tmp_states)

        }
        :: else -> skip;
        fi;
      }
      :: else -> skip;
      fi;
      i = i + 1;
    }
    :: else -> break;
    od;


#if TRACE_EXECUTION
printf("History: ");
printf("%d%d%d%d%d%d%d", 
    INV_F88AA_history[0], 
    INV_F88AA_history[1], 
    INV_F88AA_history[2], 
    INV_F88AA_history[3], 
    INV_F88AA_history[4], 
    INV_F88AA_history[5], 
    INV_F88AA_history[6]);
printf("\n");
#endif
  }
  :: else -> skip;
  fi;

/* ---------------------------- */
INV_F88AA_ESTABLISH_ENTRY_SET:
  /* calculate new entry set */
  INV_F88AA_STATES_COPY(INV_F88AA_ctx.entry_set, INV_F88AA_ctx.target_set)

  i = 0;
  do
  :: i < INV_F88AA_USCXML_NUMBER_STATES -> {
    if
    :: INV_F88AA_ctx.entry_set[i] -> {
      /* ancestor completion */
      INV_F88AA_STATES_OR(INV_F88AA_ctx.entry_set, INV_F88AA_states[i].ancestors)
    }
    :: else -> skip;
    fi;
    i = i + 1;
  }
  :: else -> break;
  od;

  /* iterate for descendants */
  i = 0;
  do
  :: i < INV_F88AA_USCXML_NUMBER_STATES -> {
    if
    :: INV_F88AA_ctx.entry_set[i] -> {
      if
      :: INV_F88AA_states[i].type[USCXML_STATE_PARALLEL] -> {
        INV_F88AA_STATES_OR(INV_F88AA_ctx.entry_set, INV_F88AA_states[i].completion)
      }
      :: INV_F88AA_states[i].type[USCXML_STATE_HISTORY_SHALLOW] ||
         INV_F88AA_states[i].type[USCXML_STATE_HISTORY_DEEP] -> {

#if TRACE_EXECUTION
printf("%d: Descendant completion for history state %d\n", _pid, i);
#endif

        if
        :: !INV_F88AA_STATES_HAS_AND(INV_F88AA_states[i].completion, INV_F88AA_history) && !INV_F88AA_config[INV_F88AA_states[i].parent] -> {
          /* nothing set for history, look for a default transition */

#if TRACE_EXECUTION
printf("%d: Fresh history in target set\n", _pid);
#endif

          j = 0;
          do
          :: j < INV_F88AA_USCXML_NUMBER_TRANS -> {
             if
             :: INV_F88AA_transitions[j].source == i -> {
               INV_F88AA_ctx.trans_set[j] = true;
               INV_F88AA_STATES_OR(INV_F88AA_ctx.entry_set, INV_F88AA_transitions[j].target)

               if
               :: (INV_F88AA_states[i].type[USCXML_STATE_HISTORY_DEEP] &&
                   !INV_F88AA_STATES_HAS_AND(INV_F88AA_transitions[j].target, INV_F88AA_states[i].children)                  ) -> {
                 k = i + 1
                 do
                 :: k < INV_F88AA_USCXML_NUMBER_STATES -> {
                   if
                   :: INV_F88AA_transitions[j].target[k] -> {
                     INV_F88AA_STATES_OR(INV_F88AA_ctx.entry_set, INV_F88AA_states[k].ancestors)
                     break;

                   }
                   :: else -> skip;
                   fi
                   k = k + 1;
                 }
                 :: else -> break;
                 od
               }
               :: else -> skip;
               fi
               break;
             }
             :: else -> skip;
             fi
             j = j + 1;
          }
          :: else -> break
          od
          skip;
        }
        :: else -> {

#if TRACE_EXECUTION
printf("%d: Established history in target set\n", _pid);
#endif

          INV_F88AA_STATES_COPY(INV_F88AA_ctx.tmp_states, INV_F88AA_states[i].completion)
          INV_F88AA_STATES_AND(INV_F88AA_ctx.tmp_states, INV_F88AA_history)
          INV_F88AA_STATES_OR(INV_F88AA_ctx.entry_set, INV_F88AA_ctx.tmp_states)
          if
          :: INV_F88AA_states[i].type[USCXML_STATE_HAS_HISTORY] ||
             INV_F88AA_states[i].type[USCXML_STATE_HISTORY_DEEP] -> { 
            /* a deep history state with nested histories -> more completion */

#if TRACE_EXECUTION
printf("%d: DEEP HISTORY\n", _pid);
#endif

            j = i + 1;
            do
            :: j < INV_F88AA_USCXML_NUMBER_STATES -> {
              if
              :: (INV_F88AA_states[i].completion[j] &&
                  INV_F88AA_ctx.entry_set[j] && 
                  INV_F88AA_states[j].type[USCXML_STATE_HAS_HISTORY]) -> {
                k = j + 1;
                do
                :: k < INV_F88AA_USCXML_NUMBER_STATES -> {
                  /* add nested history to entry_set */
                  if
                  :: (INV_F88AA_states[k].type[USCXML_STATE_HISTORY_DEEP] ||
                      INV_F88AA_states[k].type[USCXML_STATE_HISTORY_SHALLOW]) &&
                     INV_F88AA_states[j].children[k] -> {
                    /* a nested history state */
                    INV_F88AA_ctx.entry_set[k] = true;
                  }
                  :: else -> skip;
                  fi
                  k = k + 1;
                }
                :: else -> break;
                od
              }
              :: else -> skip;
              fi
            }
            j = j + 1;
            :: else -> break;
            od
          }
          :: else -> skip;
          fi
        }
        fi;
      }
      :: INV_F88AA_states[i].type[USCXML_STATE_INITIAL] -> {

#if TRACE_EXECUTION
printf("%d: Descendant completion for initial state %d\n", _pid, i);
#endif

        j = 0
        do
        :: j < INV_F88AA_USCXML_NUMBER_TRANS -> {
          if
          :: INV_F88AA_transitions[j].source == i -> {
            INV_F88AA_ctx.trans_set[j] = true;
            INV_F88AA_ctx.entry_set[i] = false;

#if TRACE_EXECUTION
printf("%d: Adding transition %d!\n", _pid, j);
#endif

            INV_F88AA_STATES_OR(INV_F88AA_ctx.entry_set, INV_F88AA_transitions[j].target)

            k = i + 1;
            do
            :: k < INV_F88AA_USCXML_NUMBER_STATES -> {
              if
              :: INV_F88AA_transitions[j].target[k] -> {
                INV_F88AA_STATES_OR(INV_F88AA_ctx.entry_set, INV_F88AA_states[k].ancestors)

              }
              :: else -> break;
              fi
              k = k + 1;
            }
            :: else -> break
            od
          }
          :: else -> skip;
          fi
          j = j + 1;
        }
        :: else -> break
        od;
      }
      :: INV_F88AA_states[i].type[USCXML_STATE_COMPOUND] -> {
        /* we need to check whether one child is already in entry_set */
        if
        :: (
          !INV_F88AA_STATES_HAS_AND(INV_F88AA_ctx.entry_set, INV_F88AA_states[i].children) && 
           (!INV_F88AA_STATES_HAS_AND(INV_F88AA_config, INV_F88AA_states[i].children) || INV_F88AA_STATES_HAS_AND(INV_F88AA_ctx.exit_set, INV_F88AA_states[i].children)
)) 
        -> {
          INV_F88AA_STATES_OR(INV_F88AA_ctx.entry_set, INV_F88AA_states[i].completion)
          if
          :: (INV_F88AA_STATES_HAS_AND(INV_F88AA_states[i].completion, INV_F88AA_states[i].children)
          ) -> {
            /* deep completion */
            j = i + 1;
            do
            :: j < INV_F88AA_USCXML_NUMBER_STATES - 1 -> {
              j = j + 1;
              if
              :: INV_F88AA_states[i].completion[j] -> {
                INV_F88AA_STATES_OR(INV_F88AA_ctx.entry_set, INV_F88AA_states[j].ancestors)

                /* completion of compound is single state */
                break;
              } 
              :: else -> skip;
              fi
            }
            :: else -> break;
            od
          }
          :: else -> skip;
          fi
        }
        :: else -> skip;
        fi
      }
      :: else -> skip;
      fi;
    }
    :: else -> skip;
    fi;
    i = i + 1;
  }
  :: else -> break;
  od;


#if TRACE_EXECUTION
printf("Entry Set");
printf("%d%d%d%d%d%d%d", 
    INV_F88AA_ctx.entry_set[0], 
    INV_F88AA_ctx.entry_set[1], 
    INV_F88AA_ctx.entry_set[2], 
    INV_F88AA_ctx.entry_set[3], 
    INV_F88AA_ctx.entry_set[4], 
    INV_F88AA_ctx.entry_set[5], 
    INV_F88AA_ctx.entry_set[6]);
printf("\n");
#endif


/* ---------------------------- */
/* EXIT_STATES: */
  i = INV_F88AA_USCXML_NUMBER_STATES;
  do
  :: i > 0 -> {
    i = i - 1;
    if
    :: INV_F88AA_ctx.exit_set[i] && INV_F88AA_config[i] -> {
      /* call all on-exit handlers */

#if TRACE_EXECUTION
printf("%d: Exiting state %d\n", _pid, i);
#endif

      if
      :: i == 5 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for exiting state %d\n", _pid, i);
#endif

      if
      :: (INV_F88AA__event.name == TAKE_FORKS) -> {
          cancelSendId(RESOURCE_DENIED_TIMER,INV_F88AA);
      }
      :: else -> skip;
      fi;
      }
      :: else -> skip;
      fi

      INV_F88AA_config[i] = false;
      skip;
    }
    :: else -> skip;
    fi;
  }
  :: else -> break;
  od;


/* ---------------------------- */
/* TAKE_TRANSITIONS: */
  i = 0;
  do
  :: i < INV_F88AA_USCXML_NUMBER_TRANS -> {
    if
    :: INV_F88AA_ctx.trans_set[i] && 
       !INV_F88AA_transitions[i].type[USCXML_TRANS_HISTORY] && 
       !INV_F88AA_transitions[i].type[USCXML_TRANS_INITIAL] -> {
      /* Call executable content in normal transition */

#if TRACE_EXECUTION
printf("%d: Taking transition %d\n", _pid, i);
#endif

      if
      :: i == 0 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, i);
#endif

        skip;
      }
      :: i == 1 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, i);
#endif

        skip;
      }
      :: i == 2 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, i);
#endif

        skip;
      }
      :: i == 3 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, i);
#endif

        if
        :: !INV_F88AA_flags[USCXML_CTX_FINISHED] || INV_F88AA_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
          {
            INV_F88AA__tmpE.data.p_id = 0;
            INV_F88AA__tmpE.delay = 0;
            INV_F88AA__tmpE.invokeid = 0;
            INV_F88AA__tmpE.name = 0;
            INV_F88AA__tmpE.origin = 0;
            INV_F88AA__tmpE.sendid = 0;
            INV_F88AA__tmpE.seqNr = 0;
            INV_F88AA__tmpE.name = RETURN_FORKS;
            INV_F88AA__tmpE.invokeid = INV_F88AA;
            INV_F88AA__tmpE.origin = INV_F88AA;
            _lastSeqId = _lastSeqId + 1;
            INV_F88AA__tmpE.delay = 0;
            INV_F88AA__tmpE.seqNr = _lastSeqId;
            INV_F88AA__tmpE.data.p_id = INV_F88AA_p_id;
#if TRACE_EXECUTION
printf("%d: Sending RETURN_FORKS (%d) to ROOT_eQ\n", _pid, INV_F88AA__tmpE.name );
#endif

            ROOT_eQ!INV_F88AA__tmpE;
            insertWithDelay(ROOT_eQ);
          }
          skip;
        }
        :: else -> skip;
        fi
        skip;
      }
      :: i == 4 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, i);
#endif

        skip;
      }
      :: i == 5 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, i);
#endif

        if
        :: !INV_F88AA_flags[USCXML_CTX_FINISHED] || INV_F88AA_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
          {
            INV_F88AA__tmpE.data.p_id = 0;
            INV_F88AA__tmpE.delay = 0;
            INV_F88AA__tmpE.invokeid = 0;
            INV_F88AA__tmpE.name = 0;
            INV_F88AA__tmpE.origin = 0;
            INV_F88AA__tmpE.sendid = 0;
            INV_F88AA__tmpE.seqNr = 0;
            INV_F88AA__tmpE.name = NEED_FORKS;
            INV_F88AA__tmpE.invokeid = INV_F88AA;
            INV_F88AA__tmpE.origin = INV_F88AA;
            _lastSeqId = _lastSeqId + 1;
            INV_F88AA__tmpE.delay = 0;
            INV_F88AA__tmpE.seqNr = _lastSeqId;
            INV_F88AA__tmpE.data.p_id = INV_F88AA_p_id;
#if TRACE_EXECUTION
printf("%d: Sending NEED_FORKS (%d) to ROOT_eQ\n", _pid, INV_F88AA__tmpE.name );
#endif

            ROOT_eQ!INV_F88AA__tmpE;
            insertWithDelay(ROOT_eQ);
          }
          skip;
        }
        :: else -> skip;
        fi
        skip;
      }
      :: i == 6 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, i);
#endif

        printf("philospher: : %d", INV_F88AA_p_id);
        printf("Time(in ms) since resource denied: : %d", INV_F88AA_delay);
        skip;
      }
      :: else ->skip;
      fi

    }
    :: else -> skip;
    fi;
    i = i + 1;
  }
  :: else -> break;
  od;

/* ---------------------------- */
/* ENTER_STATES: */
  i = 0;
  do
  :: i < INV_F88AA_USCXML_NUMBER_STATES -> {
    if
    :: (INV_F88AA_ctx.entry_set[i] &&
        !INV_F88AA_config[i] && 
        /* these are no proper states */
        !INV_F88AA_states[i].type[USCXML_STATE_HISTORY_DEEP] && 
        !INV_F88AA_states[i].type[USCXML_STATE_HISTORY_SHALLOW] && 
        !INV_F88AA_states[i].type[USCXML_STATE_INITIAL]
       ) -> {

#if TRACE_EXECUTION
printf("%d: Entering state %d\n", _pid, i);
#endif

         INV_F88AA_config[i] = true;

         /* Process executable content for entering a state */
         if
         :: i == 1 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for entering state %d\n", _pid, i);
#endif

          printf("Hello, I am philospher number: : %d", INV_F88AA_p_id);
         }
         :: i == 2 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for entering state %d\n", _pid, i);
#endif

          printf("Thinking professor: : %d", INV_F88AA_p_id);
            INV_F88AA_random_delay = ((1103515245*INV_F88AA_random_delay+12345)%2147483647)%2000;
          if
          :: !INV_F88AA_flags[USCXML_CTX_FINISHED] || INV_F88AA_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
            {
              INV_F88AA__tmpE.data.p_id = 0;
              INV_F88AA__tmpE.delay = 0;
              INV_F88AA__tmpE.invokeid = 0;
              INV_F88AA__tmpE.name = 0;
              INV_F88AA__tmpE.origin = 0;
              INV_F88AA__tmpE.sendid = 0;
              INV_F88AA__tmpE.seqNr = 0;
              INV_F88AA__tmpE.name = THINKING_OVER;
              INV_F88AA__tmpE.invokeid = INV_F88AA;
              INV_F88AA__tmpE.origin = INV_F88AA;
              _lastSeqId = _lastSeqId + 1;
              INV_F88AA__tmpE.delay = INV_F88AA_random_delay*(INV_F88AA_p_id+1);
              INV_F88AA__tmpE.seqNr = _lastSeqId;
#if TRACE_EXECUTION
printf("%d: Sending THINKING_OVER (%d) to INV_F88AA_eQ\n", _pid, INV_F88AA__tmpE.name );
#endif

              INV_F88AA_eQ!INV_F88AA__tmpE;
              insertWithDelay(INV_F88AA_eQ);
            }
            skip;
          }
          :: else -> skip;
          fi
         }
         :: i == 3 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for entering state %d\n", _pid, i);
#endif

          printf("Hungry professor: : %d", INV_F88AA_p_id);
          if
          :: !INV_F88AA_flags[USCXML_CTX_FINISHED] || INV_F88AA_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
            {
              INV_F88AA__tmpE.data.p_id = 0;
              INV_F88AA__tmpE.delay = 0;
              INV_F88AA__tmpE.invokeid = 0;
              INV_F88AA__tmpE.name = 0;
              INV_F88AA__tmpE.origin = 0;
              INV_F88AA__tmpE.sendid = 0;
              INV_F88AA__tmpE.seqNr = 0;
              INV_F88AA__tmpE.name = NEED_FORKS;
              INV_F88AA__tmpE.invokeid = INV_F88AA;
              INV_F88AA__tmpE.origin = INV_F88AA;
              _lastSeqId = _lastSeqId + 1;
              INV_F88AA__tmpE.delay = 300;
              INV_F88AA__tmpE.seqNr = _lastSeqId;
              INV_F88AA__tmpE.data.p_id = INV_F88AA_p_id;
#if TRACE_EXECUTION
printf("%d: Sending NEED_FORKS (%d) to ROOT_eQ\n", _pid, INV_F88AA__tmpE.name );
#endif

              ROOT_eQ!INV_F88AA__tmpE;
              insertWithDelay(ROOT_eQ);
            }
            skip;
          }
          :: else -> skip;
          fi
         }
         :: i == 4 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for entering state %d\n", _pid, i);
#endif

          printf("Eating professor: : %d", INV_F88AA_p_id);
          if
          :: !INV_F88AA_flags[USCXML_CTX_FINISHED] || INV_F88AA_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
            {
              INV_F88AA__tmpE.data.p_id = 0;
              INV_F88AA__tmpE.delay = 0;
              INV_F88AA__tmpE.invokeid = 0;
              INV_F88AA__tmpE.name = 0;
              INV_F88AA__tmpE.origin = 0;
              INV_F88AA__tmpE.sendid = 0;
              INV_F88AA__tmpE.seqNr = 0;
              INV_F88AA__tmpE.name = EATING_OVER;
              INV_F88AA__tmpE.invokeid = INV_F88AA;
              INV_F88AA__tmpE.origin = INV_F88AA;
              _lastSeqId = _lastSeqId + 1;
              INV_F88AA__tmpE.delay = 500;
              INV_F88AA__tmpE.seqNr = _lastSeqId;
#if TRACE_EXECUTION
printf("%d: Sending EATING_OVER (%d) to INV_F88AA_eQ\n", _pid, INV_F88AA__tmpE.name );
#endif

              INV_F88AA_eQ!INV_F88AA__tmpE;
              insertWithDelay(INV_F88AA_eQ);
            }
            skip;
          }
          :: else -> skip;
          fi
         }
         :: i == 5 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for entering state %d\n", _pid, i);
#endif

          printf("Resource Denied professor: : %d", INV_F88AA_p_id);
          if
          :: !INV_F88AA_flags[USCXML_CTX_FINISHED] || INV_F88AA_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
            {
              INV_F88AA__tmpE.data.p_id = 0;
              INV_F88AA__tmpE.delay = 0;
              INV_F88AA__tmpE.invokeid = 0;
              INV_F88AA__tmpE.name = 0;
              INV_F88AA__tmpE.origin = 0;
              INV_F88AA__tmpE.sendid = 0;
              INV_F88AA__tmpE.seqNr = 0;
              INV_F88AA__tmpE.name = TIMEOUT;
              INV_F88AA__tmpE.sendid = RESOURCE_DENIED_TIMER;
              INV_F88AA__tmpE.invokeid = INV_F88AA;
              INV_F88AA__tmpE.origin = INV_F88AA;
              _lastSeqId = _lastSeqId + 1;
              INV_F88AA__tmpE.delay = INV_F88AA_delay;
              INV_F88AA__tmpE.seqNr = _lastSeqId;
#if TRACE_EXECUTION
printf("%d: Sending TIMEOUT (%d) to INV_F88AA_eQ\n", _pid, INV_F88AA__tmpE.name );
#endif

              INV_F88AA_eQ!INV_F88AA__tmpE;
              insertWithDelay(INV_F88AA_eQ);
            }
            skip;
          }
          :: else -> skip;
          fi
          if
          :: !INV_F88AA_flags[USCXML_CTX_FINISHED] || INV_F88AA_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
            {
              INV_F88AA__tmpE.data.p_id = 0;
              INV_F88AA__tmpE.delay = 0;
              INV_F88AA__tmpE.invokeid = 0;
              INV_F88AA__tmpE.name = 0;
              INV_F88AA__tmpE.origin = 0;
              INV_F88AA__tmpE.sendid = 0;
              INV_F88AA__tmpE.seqNr = 0;
              INV_F88AA__tmpE.name = RESEND_NEED_FORKS;
              INV_F88AA__tmpE.invokeid = INV_F88AA;
              INV_F88AA__tmpE.origin = INV_F88AA;
              _lastSeqId = _lastSeqId + 1;
              INV_F88AA__tmpE.delay = 300;
              INV_F88AA__tmpE.seqNr = _lastSeqId;
#if TRACE_EXECUTION
printf("%d: Sending RESEND_NEED_FORKS (%d) to INV_F88AA_eQ\n", _pid, INV_F88AA__tmpE.name );
#endif

              INV_F88AA_eQ!INV_F88AA__tmpE;
              insertWithDelay(INV_F88AA_eQ);
            }
            skip;
          }
          :: else -> skip;
          fi
         }
         :: else ->skip;
         fi

         /* take history and initial transitions */
         j = 0;
         do
         :: j < INV_F88AA_USCXML_NUMBER_TRANS -> {
           if
           :: (INV_F88AA_ctx.trans_set[j] &&
              (INV_F88AA_transitions[j].type[USCXML_TRANS_HISTORY] ||
               INV_F88AA_transitions[j].type[USCXML_TRANS_INITIAL]) && 
               INV_F88AA_states[INV_F88AA_transitions[j].source].parent == i) -> {
              /* Call executable content in history or initial transition */
              if
              :: j == 0 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, j);
#endif

                skip;
              }
              :: j == 1 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, j);
#endif

                skip;
              }
              :: j == 2 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, j);
#endif

                skip;
              }
              :: j == 3 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, j);
#endif

                if
                :: !INV_F88AA_flags[USCXML_CTX_FINISHED] || INV_F88AA_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
                  {
                    INV_F88AA__tmpE.data.p_id = 0;
                    INV_F88AA__tmpE.delay = 0;
                    INV_F88AA__tmpE.invokeid = 0;
                    INV_F88AA__tmpE.name = 0;
                    INV_F88AA__tmpE.origin = 0;
                    INV_F88AA__tmpE.sendid = 0;
                    INV_F88AA__tmpE.seqNr = 0;
                    INV_F88AA__tmpE.name = RETURN_FORKS;
                    INV_F88AA__tmpE.invokeid = INV_F88AA;
                    INV_F88AA__tmpE.origin = INV_F88AA;
                    _lastSeqId = _lastSeqId + 1;
                    INV_F88AA__tmpE.delay = 0;
                    INV_F88AA__tmpE.seqNr = _lastSeqId;
                    INV_F88AA__tmpE.data.p_id = INV_F88AA_p_id;
#if TRACE_EXECUTION
printf("%d: Sending RETURN_FORKS (%d) to ROOT_eQ\n", _pid, INV_F88AA__tmpE.name );
#endif

                    ROOT_eQ!INV_F88AA__tmpE;
                    insertWithDelay(ROOT_eQ);
                  }
                  skip;
                }
                :: else -> skip;
                fi
                skip;
              }
              :: j == 4 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, j);
#endif

                skip;
              }
              :: j == 5 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, j);
#endif

                if
                :: !INV_F88AA_flags[USCXML_CTX_FINISHED] || INV_F88AA_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
                  {
                    INV_F88AA__tmpE.data.p_id = 0;
                    INV_F88AA__tmpE.delay = 0;
                    INV_F88AA__tmpE.invokeid = 0;
                    INV_F88AA__tmpE.name = 0;
                    INV_F88AA__tmpE.origin = 0;
                    INV_F88AA__tmpE.sendid = 0;
                    INV_F88AA__tmpE.seqNr = 0;
                    INV_F88AA__tmpE.name = NEED_FORKS;
                    INV_F88AA__tmpE.invokeid = INV_F88AA;
                    INV_F88AA__tmpE.origin = INV_F88AA;
                    _lastSeqId = _lastSeqId + 1;
                    INV_F88AA__tmpE.delay = 0;
                    INV_F88AA__tmpE.seqNr = _lastSeqId;
                    INV_F88AA__tmpE.data.p_id = INV_F88AA_p_id;
#if TRACE_EXECUTION
printf("%d: Sending NEED_FORKS (%d) to ROOT_eQ\n", _pid, INV_F88AA__tmpE.name );
#endif

                    ROOT_eQ!INV_F88AA__tmpE;
                    insertWithDelay(ROOT_eQ);
                  }
                  skip;
                }
                :: else -> skip;
                fi
                skip;
              }
              :: j == 6 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, j);
#endif

                printf("philospher: : %d", INV_F88AA_p_id);
                printf("Time(in ms) since resource denied: : %d", INV_F88AA_delay);
                skip;
              }
              :: else ->skip;
              fi

           }
           :: else -> skip;
           fi
           j = j + 1;
         }
         :: else -> break;
         od
         /* handle final states */
         if
         :: INV_F88AA_states[i].type[USCXML_STATE_FINAL] -> {
           if
           :: INV_F88AA_states[INV_F88AA_states[i].parent].children[1] -> {
             /* exit topmost SCXML state */
             INV_F88AA_flags[USCXML_CTX_TOP_LEVEL_FINAL] = true;
             INV_F88AA_flags[USCXML_CTX_FINISHED] = true;
           }
           :: else -> {
             /* raise done event */
             if
             :: else -> skip;
             fi
           }
           fi
           /**
            * are we the last final state to leave a parallel state?:
            * 1. Gather all parallel states in our ancestor chain
            * 2. Find all states for which these parallels are ancestors
            * 3. Iterate all active final states and remove their ancestors
            * 4. If a state remains, not all children of a parallel are final
            */
            j = 0;
            do
            :: j < INV_F88AA_USCXML_NUMBER_STATES -> {
              if
              :: INV_F88AA_states[j].type[USCXML_STATE_PARALLEL] && INV_F88AA_states[i].ancestors[j] -> {
                INV_F88AA_STATES_CLEAR(INV_F88AA_ctx.tmp_states)
                k = 0;
                do
                :: k < INV_F88AA_USCXML_NUMBER_STATES -> {
                  if
                  :: INV_F88AA_states[k].ancestors[j] && INV_F88AA_config[k] -> {
                    if
                    :: INV_F88AA_states[k].type[USCXML_STATE_FINAL] -> {
                      INV_F88AA_STATES_AND_NOT(INV_F88AA_ctx.tmp_states, INV_F88AA_states[k].ancestors)
                    }
                    :: else -> {
                      INV_F88AA_ctx.tmp_states[k] = true;
                    }
                    fi
                  }
                  :: else -> skip;
                  fi
                  k = k + 1;
                }
                :: else -> break;
                od
                if
                :: !INV_F88AA_STATES_HAS_ANY(INV_F88AA_ctx.tmp_states) -> {
                  if
                  :: else -> skip;
                  fi
                }
                :: else -> skip;
                fi
              }
              :: else -> skip;
              fi
              j = j + 1;
            }
            :: else -> break;
            od
         }
         :: else -> skip;
         fi

    }
    :: else -> skip;
    i = i + 1;
    fi;
  }
  :: else -> break;
  od;

  }
  :: else -> skip;
  fi /* USCXML_CTX_TRANSITION_FOUND */
  } skip; /* d_step */
} /* !USCXML_CTX_FINISHED */
:: else -> break;
od

/* ---------------------------- */
INV_F88AA_TERMINATE_MACHINE:
skip; d_step {

#if TRACE_EXECUTION
printf("%d: Machine finished\n", _pid);
#endif

/* exit all remaining states */
i = INV_F88AA_USCXML_NUMBER_STATES;
do
:: i > 0 -> {
  i = i - 1;
  if
  :: INV_F88AA_config[i] && INV_F88AA_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
    /* call all on exit handlers */
   if
    :: i == 5 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for exiting state %d\n", _pid, i);
#endif

    if
    :: (INV_F88AA__event.name == TAKE_FORKS) -> {
        cancelSendId(RESOURCE_DENIED_TIMER,INV_F88AA);
    }
    :: else -> skip;
    fi;
    }
    :: else -> skip;
    fi

    skip;
    
  }
  :: else -> skip;
  fi;

  if
  :: INV_F88AA_invocations[i] -> {
    /* cancel invocations */
    INV_F88AA_invocations[i] = false;
    if
    :: else -> skip;
    fi
    skip;

  }
  :: else -> skip;
  fi;
}
:: else -> break;
od;


#if TRACE_EXECUTION
printf("%d: Removing pending events\n", _pid);
#endif

removePendingEventsFromInvoker(INV_F88AA)
/* send done event */
if
:: INV_F88AA_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
    INV_F88AA__tmpE.data.p_id = 0;
    INV_F88AA__tmpE.delay = 0;
    INV_F88AA__tmpE.invokeid = 0;
    INV_F88AA__tmpE.name = 0;
    INV_F88AA__tmpE.origin = 0;
    INV_F88AA__tmpE.sendid = 0;
    INV_F88AA__tmpE.seqNr = 0;

    INV_F88AA__tmpE.name = DONE_INVOKE_INV_F88AA
    INV_F88AA__tmpE.invokeid = INV_F88AA

#if TRACE_EXECUTION
printf("%d: Sending DONE.INVOKE\n", _pid);
#endif

    ROOT_eQ!INV_F88AA__tmpE;
    insertWithDelay(ROOT_eQ);
}
:: else -> skip
fi;

} /* d_step */


#if TRACE_EXECUTION
printf("%d: Done\n", _pid);
#endif

} } /* atomic, step() */


/* machine microstep function */
#define INV_41D63_USCXML_NUMBER_STATES 7
#define INV_41D63_USCXML_NUMBER_TRANS 7

proctype INV_41D63_step() { atomic {

INV_41D63_procid = _pid;
unsigned i : 3,  j : 3,  k : 3;


/* ---------------------------- */
INV_41D63_MICROSTEP:
do
:: !INV_41D63_flags[USCXML_CTX_FINISHED] -> {
  /* Run until machine is finished */


#if TRACE_EXECUTION
printf("%d: Taking a step\n", _pid);
#endif

  /* Dequeue an event */
  INV_41D63_flags[USCXML_CTX_DEQUEUE_EXTERNAL] = false;
  if
  ::INV_41D63_flags[USCXML_CTX_SPONTANEOUS] -> {
    INV_41D63__event.name = USCXML_EVENT_SPONTANEOUS;

#if TRACE_EXECUTION
printf("%d: Trying with a spontaneous event\n", _pid);
#endif

  }
  :: else -> {
    if
    :: len(INV_41D63_iQ) != 0 -> {
      INV_41D63_iQ ? INV_41D63__event;

#if TRACE_EXECUTION
printf("%d: Deqeued an internal event\n", _pid);
#endif

    }
    :: else -> {
      INV_41D63_flags[USCXML_CTX_DEQUEUE_EXTERNAL] = true;
    }
    fi;
  }
  fi;


  if
  :: INV_41D63_flags[USCXML_CTX_DEQUEUE_EXTERNAL] -> {
    /* manage invocations */
    i = 0;
    do
    :: i < INV_41D63_USCXML_NUMBER_STATES -> {
      d_step { 
      /* uninvoke */
      if
      :: !INV_41D63_config[i] && INV_41D63_invocations[i] -> {

#if TRACE_EXECUTION
printf("%d: Uninvoking in state %d\n", _pid, i);
#endif

        if
        :: else -> skip;
        fi
        INV_41D63_invocations[i] = false;
        skip;
      }
      :: else -> skip;
      fi;
      } /* d_step */

      /* invoke */
      if
      :: INV_41D63_config[i] && !INV_41D63_invocations[i] -> {
        if
        :: else -> skip;
        fi
      }
      :: else -> skip;
      fi;
      i = i + 1;
    }
    :: else -> break;
    od;

    /* Determine machines with smallest delay and set their process priority */
    scheduleMachines();

    /* we may return to find ourselves terminated */
    if
    :: INV_41D63_flags[USCXML_CTX_FINISHED] -> {
      goto INV_41D63_TERMINATE_MACHINE;
    }
    :: else -> skip;
    fi
    /* Not sure if this should be before the invocation due to auto-forwarding */
    if
    :: len(INV_41D63_eQ) != 0 -> {
      INV_41D63_eQ ? INV_41D63__event;

#if TRACE_EXECUTION
printf("%d: Deqeued an external event\n", _pid);
#endif

    }
    fi;
  }
  :: else -> skip;
  fi


d_step { skip;

/* ---------------------------- */
INV_41D63_SELECT_TRANSITIONS:
INV_41D63_STATES_CLEAR(INV_41D63_ctx.target_set)
INV_41D63_STATES_CLEAR(INV_41D63_ctx.exit_set)
INV_41D63_TRANS_CLEAR(INV_41D63_ctx.conflicts)
INV_41D63_TRANS_CLEAR(INV_41D63_ctx.trans_set)
#if TRACE_EXECUTION
printf("%d: Establishing optimal transition set for event %d\n", _pid, INV_41D63__event.name );
#endif

#if TRACE_EXECUTION
printf("Configuration: ");
printf("%d%d%d%d%d%d%d", 
    INV_41D63_config[0], 
    INV_41D63_config[1], 
    INV_41D63_config[2], 
    INV_41D63_config[3], 
    INV_41D63_config[4], 
    INV_41D63_config[5], 
    INV_41D63_config[6]);
printf("\n");
#endif

  INV_41D63_flags[USCXML_CTX_TRANSITION_FOUND] = false;
  i = 0;
  do
  :: i < INV_41D63_USCXML_NUMBER_TRANS -> {
    /* only select non-history, non-initial transitions */
    if
    :: !INV_41D63_transitions[i].type[USCXML_TRANS_HISTORY] &&
       !INV_41D63_transitions[i].type[USCXML_TRANS_INITIAL] -> {
      if
      :: /* is the transition active? */
         INV_41D63_config[INV_41D63_transitions[i].source] && 

         /* is it non-conflicting? */
         !INV_41D63_ctx.conflicts[i] && 

         /* is it spontaneous with an event or vice versa? */
         ((INV_41D63__event.name == USCXML_EVENT_SPONTANEOUS && 
           INV_41D63_transitions[i].type[USCXML_TRANS_SPONTANEOUS]) || 
          (INV_41D63__event.name != USCXML_EVENT_SPONTANEOUS && 
           !INV_41D63_transitions[i].type[USCXML_TRANS_SPONTANEOUS])) &&

         /* is it matching and enabled? */
         (false 
          || (i == 0 && (false || INV_41D63__event.name == THINKING_OVER))
          || (i == 1 && (false || INV_41D63__event.name == TAKE_FORKS))
          || (i == 2 && (false || INV_41D63__event.name == RESOURCE_DENIED))
          || (i == 3 && (false || INV_41D63__event.name == EATING_OVER))
          || (i == 4 && (false || INV_41D63__event.name == TAKE_FORKS))
          || (i == 5 && (false || INV_41D63__event.name == RESEND_NEED_FORKS))
          || (i == 6 && (false || INV_41D63__event.name == TIMEOUT))
         ) -> {
        /* remember that we found a transition */
        INV_41D63_flags[USCXML_CTX_TRANSITION_FOUND] = true;

        /* transitions that are pre-empted */
        INV_41D63_TRANS_OR(INV_41D63_ctx.conflicts, INV_41D63_transitions[i].conflicts)

        /* states that are directly targeted (resolve as entry-set later) */
        INV_41D63_STATES_OR(INV_41D63_ctx.target_set, INV_41D63_transitions[i].target)

        /* states that will be left */
        INV_41D63_STATES_OR(INV_41D63_ctx.exit_set, INV_41D63_transitions[i].exit_set)

        INV_41D63_ctx.trans_set[i] = true;
      }
      :: else {
        skip;
      }
      fi
    }
    :: else -> {
      skip;
    }
    fi
    i = i + 1;
  }
  :: else -> break;
  od;
  INV_41D63_STATES_AND(INV_41D63_ctx.exit_set, INV_41D63_config)

#if TRACE_EXECUTION
printf("Selected Transitions: ");
printf("%d%d%d%d%d%d%d", 
    INV_41D63_ctx.trans_set[0], 
    INV_41D63_ctx.trans_set[1], 
    INV_41D63_ctx.trans_set[2], 
    INV_41D63_ctx.trans_set[3], 
    INV_41D63_ctx.trans_set[4], 
    INV_41D63_ctx.trans_set[5], 
    INV_41D63_ctx.trans_set[6]);
printf("\n");
#endif


#if TRACE_EXECUTION
printf("Target Set: ");
printf("%d%d%d%d%d%d%d", 
    INV_41D63_ctx.target_set[0], 
    INV_41D63_ctx.target_set[1], 
    INV_41D63_ctx.target_set[2], 
    INV_41D63_ctx.target_set[3], 
    INV_41D63_ctx.target_set[4], 
    INV_41D63_ctx.target_set[5], 
    INV_41D63_ctx.target_set[6]);
printf("\n");
#endif


#if TRACE_EXECUTION
printf("Exit Set: ");
printf("%d%d%d%d%d%d%d", 
    INV_41D63_ctx.exit_set[0], 
    INV_41D63_ctx.exit_set[1], 
    INV_41D63_ctx.exit_set[2], 
    INV_41D63_ctx.exit_set[3], 
    INV_41D63_ctx.exit_set[4], 
    INV_41D63_ctx.exit_set[5], 
    INV_41D63_ctx.exit_set[6]);
printf("\n");
#endif

  if
  :: !INV_41D63_STATES_HAS_ANY(INV_41D63_config) -> {
    /* Enter initial configuration */
    INV_41D63_STATES_COPY(INV_41D63_ctx.target_set, INV_41D63_states[0].completion)
    INV_41D63_flags[USCXML_CTX_SPONTANEOUS] = true;
    INV_41D63_flags[USCXML_CTX_TRANSITION_FOUND] = true;

#if TRACE_EXECUTION
printf("%d: Entering initial default completion\n", _pid);
#endif


  }
  :: INV_41D63_flags[USCXML_CTX_TRANSITION_FOUND] -> {

#if TRACE_EXECUTION
printf("%d: Found transitions\n", _pid);
#endif

    INV_41D63_flags[USCXML_CTX_SPONTANEOUS] = true;
  }
  :: else {
    INV_41D63_flags[USCXML_CTX_SPONTANEOUS] = false;

#if TRACE_EXECUTION
printf("%d: Found NO transitions\n", _pid);
#endif

  }
  fi


  if
  :: INV_41D63_flags[USCXML_CTX_TRANSITION_FOUND] -> {
    /* only process anything if we found transitions or are on initial entry */
/* ---------------------------- */
/* REMEMBER_HISTORY: */

#if TRACE_EXECUTION
printf("%d: Save history configurations\n", _pid);
#endif

  if
  :: INV_41D63_STATES_HAS_ANY(INV_41D63_config) -> {
    /* only remember history on non-initial entry */
    i = 0;
    do
    :: i < INV_41D63_USCXML_NUMBER_STATES -> {
      if
      :: INV_41D63_states[i].type[USCXML_STATE_HISTORY_SHALLOW] ||
         INV_41D63_states[i].type[USCXML_STATE_HISTORY_DEEP] -> {
        if
        :: INV_41D63_ctx.exit_set[INV_41D63_states[i].parent] -> {
          /* a history state whose parent is about to be exited */

#if TRACE_EXECUTION
printf("%d: history state %d is about to be exited\n", _pid, i);
#endif


#if TRACE_EXECUTION
printf("COMPLET: ");
printf("%d%d%d%d%d%d%d", 
    INV_41D63_states[i].completion[0], 
    INV_41D63_states[i].completion[1], 
    INV_41D63_states[i].completion[2], 
    INV_41D63_states[i].completion[3], 
    INV_41D63_states[i].completion[4], 
    INV_41D63_states[i].completion[5], 
    INV_41D63_states[i].completion[6]);
printf("\n");
#endif

          INV_41D63_STATES_COPY(INV_41D63_ctx.tmp_states, INV_41D63_states[i].completion)

          /* set those states who were enabled */
          INV_41D63_STATES_AND(INV_41D63_ctx.tmp_states, INV_41D63_config)

#if TRACE_EXECUTION
printf("CONFIG : ");
printf("%d%d%d%d%d%d%d", 
    INV_41D63_config[0], 
    INV_41D63_config[1], 
    INV_41D63_config[2], 
    INV_41D63_config[3], 
    INV_41D63_config[4], 
    INV_41D63_config[5], 
    INV_41D63_config[6]);
printf("\n");
#endif


#if TRACE_EXECUTION
printf("TMP_STS: ");
printf("%d%d%d%d%d%d%d", 
    INV_41D63_ctx.tmp_states[0], 
    INV_41D63_ctx.tmp_states[1], 
    INV_41D63_ctx.tmp_states[2], 
    INV_41D63_ctx.tmp_states[3], 
    INV_41D63_ctx.tmp_states[4], 
    INV_41D63_ctx.tmp_states[5], 
    INV_41D63_ctx.tmp_states[6]);
printf("\n");
#endif


          /* clear current history with completion mask */
          INV_41D63_STATES_AND_NOT(INV_41D63_history, INV_41D63_states[i].completion)

          /* set history */
          INV_41D63_STATES_OR(INV_41D63_history, INV_41D63_ctx.tmp_states)

        }
        :: else -> skip;
        fi;
      }
      :: else -> skip;
      fi;
      i = i + 1;
    }
    :: else -> break;
    od;


#if TRACE_EXECUTION
printf("History: ");
printf("%d%d%d%d%d%d%d", 
    INV_41D63_history[0], 
    INV_41D63_history[1], 
    INV_41D63_history[2], 
    INV_41D63_history[3], 
    INV_41D63_history[4], 
    INV_41D63_history[5], 
    INV_41D63_history[6]);
printf("\n");
#endif
  }
  :: else -> skip;
  fi;

/* ---------------------------- */
INV_41D63_ESTABLISH_ENTRY_SET:
  /* calculate new entry set */
  INV_41D63_STATES_COPY(INV_41D63_ctx.entry_set, INV_41D63_ctx.target_set)

  i = 0;
  do
  :: i < INV_41D63_USCXML_NUMBER_STATES -> {
    if
    :: INV_41D63_ctx.entry_set[i] -> {
      /* ancestor completion */
      INV_41D63_STATES_OR(INV_41D63_ctx.entry_set, INV_41D63_states[i].ancestors)
    }
    :: else -> skip;
    fi;
    i = i + 1;
  }
  :: else -> break;
  od;

  /* iterate for descendants */
  i = 0;
  do
  :: i < INV_41D63_USCXML_NUMBER_STATES -> {
    if
    :: INV_41D63_ctx.entry_set[i] -> {
      if
      :: INV_41D63_states[i].type[USCXML_STATE_PARALLEL] -> {
        INV_41D63_STATES_OR(INV_41D63_ctx.entry_set, INV_41D63_states[i].completion)
      }
      :: INV_41D63_states[i].type[USCXML_STATE_HISTORY_SHALLOW] ||
         INV_41D63_states[i].type[USCXML_STATE_HISTORY_DEEP] -> {

#if TRACE_EXECUTION
printf("%d: Descendant completion for history state %d\n", _pid, i);
#endif

        if
        :: !INV_41D63_STATES_HAS_AND(INV_41D63_states[i].completion, INV_41D63_history) && !INV_41D63_config[INV_41D63_states[i].parent] -> {
          /* nothing set for history, look for a default transition */

#if TRACE_EXECUTION
printf("%d: Fresh history in target set\n", _pid);
#endif

          j = 0;
          do
          :: j < INV_41D63_USCXML_NUMBER_TRANS -> {
             if
             :: INV_41D63_transitions[j].source == i -> {
               INV_41D63_ctx.trans_set[j] = true;
               INV_41D63_STATES_OR(INV_41D63_ctx.entry_set, INV_41D63_transitions[j].target)

               if
               :: (INV_41D63_states[i].type[USCXML_STATE_HISTORY_DEEP] &&
                   !INV_41D63_STATES_HAS_AND(INV_41D63_transitions[j].target, INV_41D63_states[i].children)                  ) -> {
                 k = i + 1
                 do
                 :: k < INV_41D63_USCXML_NUMBER_STATES -> {
                   if
                   :: INV_41D63_transitions[j].target[k] -> {
                     INV_41D63_STATES_OR(INV_41D63_ctx.entry_set, INV_41D63_states[k].ancestors)
                     break;

                   }
                   :: else -> skip;
                   fi
                   k = k + 1;
                 }
                 :: else -> break;
                 od
               }
               :: else -> skip;
               fi
               break;
             }
             :: else -> skip;
             fi
             j = j + 1;
          }
          :: else -> break
          od
          skip;
        }
        :: else -> {

#if TRACE_EXECUTION
printf("%d: Established history in target set\n", _pid);
#endif

          INV_41D63_STATES_COPY(INV_41D63_ctx.tmp_states, INV_41D63_states[i].completion)
          INV_41D63_STATES_AND(INV_41D63_ctx.tmp_states, INV_41D63_history)
          INV_41D63_STATES_OR(INV_41D63_ctx.entry_set, INV_41D63_ctx.tmp_states)
          if
          :: INV_41D63_states[i].type[USCXML_STATE_HAS_HISTORY] ||
             INV_41D63_states[i].type[USCXML_STATE_HISTORY_DEEP] -> { 
            /* a deep history state with nested histories -> more completion */

#if TRACE_EXECUTION
printf("%d: DEEP HISTORY\n", _pid);
#endif

            j = i + 1;
            do
            :: j < INV_41D63_USCXML_NUMBER_STATES -> {
              if
              :: (INV_41D63_states[i].completion[j] &&
                  INV_41D63_ctx.entry_set[j] && 
                  INV_41D63_states[j].type[USCXML_STATE_HAS_HISTORY]) -> {
                k = j + 1;
                do
                :: k < INV_41D63_USCXML_NUMBER_STATES -> {
                  /* add nested history to entry_set */
                  if
                  :: (INV_41D63_states[k].type[USCXML_STATE_HISTORY_DEEP] ||
                      INV_41D63_states[k].type[USCXML_STATE_HISTORY_SHALLOW]) &&
                     INV_41D63_states[j].children[k] -> {
                    /* a nested history state */
                    INV_41D63_ctx.entry_set[k] = true;
                  }
                  :: else -> skip;
                  fi
                  k = k + 1;
                }
                :: else -> break;
                od
              }
              :: else -> skip;
              fi
            }
            j = j + 1;
            :: else -> break;
            od
          }
          :: else -> skip;
          fi
        }
        fi;
      }
      :: INV_41D63_states[i].type[USCXML_STATE_INITIAL] -> {

#if TRACE_EXECUTION
printf("%d: Descendant completion for initial state %d\n", _pid, i);
#endif

        j = 0
        do
        :: j < INV_41D63_USCXML_NUMBER_TRANS -> {
          if
          :: INV_41D63_transitions[j].source == i -> {
            INV_41D63_ctx.trans_set[j] = true;
            INV_41D63_ctx.entry_set[i] = false;

#if TRACE_EXECUTION
printf("%d: Adding transition %d!\n", _pid, j);
#endif

            INV_41D63_STATES_OR(INV_41D63_ctx.entry_set, INV_41D63_transitions[j].target)

            k = i + 1;
            do
            :: k < INV_41D63_USCXML_NUMBER_STATES -> {
              if
              :: INV_41D63_transitions[j].target[k] -> {
                INV_41D63_STATES_OR(INV_41D63_ctx.entry_set, INV_41D63_states[k].ancestors)

              }
              :: else -> break;
              fi
              k = k + 1;
            }
            :: else -> break
            od
          }
          :: else -> skip;
          fi
          j = j + 1;
        }
        :: else -> break
        od;
      }
      :: INV_41D63_states[i].type[USCXML_STATE_COMPOUND] -> {
        /* we need to check whether one child is already in entry_set */
        if
        :: (
          !INV_41D63_STATES_HAS_AND(INV_41D63_ctx.entry_set, INV_41D63_states[i].children) && 
           (!INV_41D63_STATES_HAS_AND(INV_41D63_config, INV_41D63_states[i].children) || INV_41D63_STATES_HAS_AND(INV_41D63_ctx.exit_set, INV_41D63_states[i].children)
)) 
        -> {
          INV_41D63_STATES_OR(INV_41D63_ctx.entry_set, INV_41D63_states[i].completion)
          if
          :: (INV_41D63_STATES_HAS_AND(INV_41D63_states[i].completion, INV_41D63_states[i].children)
          ) -> {
            /* deep completion */
            j = i + 1;
            do
            :: j < INV_41D63_USCXML_NUMBER_STATES - 1 -> {
              j = j + 1;
              if
              :: INV_41D63_states[i].completion[j] -> {
                INV_41D63_STATES_OR(INV_41D63_ctx.entry_set, INV_41D63_states[j].ancestors)

                /* completion of compound is single state */
                break;
              } 
              :: else -> skip;
              fi
            }
            :: else -> break;
            od
          }
          :: else -> skip;
          fi
        }
        :: else -> skip;
        fi
      }
      :: else -> skip;
      fi;
    }
    :: else -> skip;
    fi;
    i = i + 1;
  }
  :: else -> break;
  od;


#if TRACE_EXECUTION
printf("Entry Set");
printf("%d%d%d%d%d%d%d", 
    INV_41D63_ctx.entry_set[0], 
    INV_41D63_ctx.entry_set[1], 
    INV_41D63_ctx.entry_set[2], 
    INV_41D63_ctx.entry_set[3], 
    INV_41D63_ctx.entry_set[4], 
    INV_41D63_ctx.entry_set[5], 
    INV_41D63_ctx.entry_set[6]);
printf("\n");
#endif


/* ---------------------------- */
/* EXIT_STATES: */
  i = INV_41D63_USCXML_NUMBER_STATES;
  do
  :: i > 0 -> {
    i = i - 1;
    if
    :: INV_41D63_ctx.exit_set[i] && INV_41D63_config[i] -> {
      /* call all on-exit handlers */

#if TRACE_EXECUTION
printf("%d: Exiting state %d\n", _pid, i);
#endif

      if
      :: i == 5 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for exiting state %d\n", _pid, i);
#endif

      if
      :: (INV_41D63__event.name == TAKE_FORKS) -> {
          cancelSendId(RESOURCE_DENIED_TIMER,INV_41D63);
      }
      :: else -> skip;
      fi;
      }
      :: else -> skip;
      fi

      INV_41D63_config[i] = false;
      skip;
    }
    :: else -> skip;
    fi;
  }
  :: else -> break;
  od;


/* ---------------------------- */
/* TAKE_TRANSITIONS: */
  i = 0;
  do
  :: i < INV_41D63_USCXML_NUMBER_TRANS -> {
    if
    :: INV_41D63_ctx.trans_set[i] && 
       !INV_41D63_transitions[i].type[USCXML_TRANS_HISTORY] && 
       !INV_41D63_transitions[i].type[USCXML_TRANS_INITIAL] -> {
      /* Call executable content in normal transition */

#if TRACE_EXECUTION
printf("%d: Taking transition %d\n", _pid, i);
#endif

      if
      :: i == 0 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, i);
#endif

        skip;
      }
      :: i == 1 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, i);
#endif

        skip;
      }
      :: i == 2 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, i);
#endif

        skip;
      }
      :: i == 3 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, i);
#endif

        if
        :: !INV_41D63_flags[USCXML_CTX_FINISHED] || INV_41D63_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
          {
            INV_41D63__tmpE.data.p_id = 0;
            INV_41D63__tmpE.delay = 0;
            INV_41D63__tmpE.invokeid = 0;
            INV_41D63__tmpE.name = 0;
            INV_41D63__tmpE.origin = 0;
            INV_41D63__tmpE.sendid = 0;
            INV_41D63__tmpE.seqNr = 0;
            INV_41D63__tmpE.name = RETURN_FORKS;
            INV_41D63__tmpE.invokeid = INV_41D63;
            INV_41D63__tmpE.origin = INV_41D63;
            _lastSeqId = _lastSeqId + 1;
            INV_41D63__tmpE.delay = 0;
            INV_41D63__tmpE.seqNr = _lastSeqId;
            INV_41D63__tmpE.data.p_id = INV_41D63_p_id;
#if TRACE_EXECUTION
printf("%d: Sending RETURN_FORKS (%d) to ROOT_eQ\n", _pid, INV_41D63__tmpE.name );
#endif

            ROOT_eQ!INV_41D63__tmpE;
            insertWithDelay(ROOT_eQ);
          }
          skip;
        }
        :: else -> skip;
        fi
        skip;
      }
      :: i == 4 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, i);
#endif

        skip;
      }
      :: i == 5 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, i);
#endif

        if
        :: !INV_41D63_flags[USCXML_CTX_FINISHED] || INV_41D63_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
          {
            INV_41D63__tmpE.data.p_id = 0;
            INV_41D63__tmpE.delay = 0;
            INV_41D63__tmpE.invokeid = 0;
            INV_41D63__tmpE.name = 0;
            INV_41D63__tmpE.origin = 0;
            INV_41D63__tmpE.sendid = 0;
            INV_41D63__tmpE.seqNr = 0;
            INV_41D63__tmpE.name = NEED_FORKS;
            INV_41D63__tmpE.invokeid = INV_41D63;
            INV_41D63__tmpE.origin = INV_41D63;
            _lastSeqId = _lastSeqId + 1;
            INV_41D63__tmpE.delay = 0;
            INV_41D63__tmpE.seqNr = _lastSeqId;
            INV_41D63__tmpE.data.p_id = INV_41D63_p_id;
#if TRACE_EXECUTION
printf("%d: Sending NEED_FORKS (%d) to ROOT_eQ\n", _pid, INV_41D63__tmpE.name );
#endif

            ROOT_eQ!INV_41D63__tmpE;
            insertWithDelay(ROOT_eQ);
          }
          skip;
        }
        :: else -> skip;
        fi
        skip;
      }
      :: i == 6 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, i);
#endif

        printf("philospher: : %d", INV_41D63_p_id);
        printf("Time(in ms) since resource denied: : %d", INV_41D63_delay);
        skip;
      }
      :: else ->skip;
      fi

    }
    :: else -> skip;
    fi;
    i = i + 1;
  }
  :: else -> break;
  od;

/* ---------------------------- */
/* ENTER_STATES: */
  i = 0;
  do
  :: i < INV_41D63_USCXML_NUMBER_STATES -> {
    if
    :: (INV_41D63_ctx.entry_set[i] &&
        !INV_41D63_config[i] && 
        /* these are no proper states */
        !INV_41D63_states[i].type[USCXML_STATE_HISTORY_DEEP] && 
        !INV_41D63_states[i].type[USCXML_STATE_HISTORY_SHALLOW] && 
        !INV_41D63_states[i].type[USCXML_STATE_INITIAL]
       ) -> {

#if TRACE_EXECUTION
printf("%d: Entering state %d\n", _pid, i);
#endif

         INV_41D63_config[i] = true;

         /* Process executable content for entering a state */
         if
         :: i == 1 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for entering state %d\n", _pid, i);
#endif

          printf("Hello, I am philospher number: : %d", INV_41D63_p_id);
         }
         :: i == 2 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for entering state %d\n", _pid, i);
#endif

          printf("Thinking professor: : %d", INV_41D63_p_id);
            INV_41D63_random_delay = ((1103515245*INV_41D63_random_delay+12345)%2147483647)%2000;
          if
          :: !INV_41D63_flags[USCXML_CTX_FINISHED] || INV_41D63_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
            {
              INV_41D63__tmpE.data.p_id = 0;
              INV_41D63__tmpE.delay = 0;
              INV_41D63__tmpE.invokeid = 0;
              INV_41D63__tmpE.name = 0;
              INV_41D63__tmpE.origin = 0;
              INV_41D63__tmpE.sendid = 0;
              INV_41D63__tmpE.seqNr = 0;
              INV_41D63__tmpE.name = THINKING_OVER;
              INV_41D63__tmpE.invokeid = INV_41D63;
              INV_41D63__tmpE.origin = INV_41D63;
              _lastSeqId = _lastSeqId + 1;
              INV_41D63__tmpE.delay = INV_41D63_random_delay*(INV_41D63_p_id+1);
              INV_41D63__tmpE.seqNr = _lastSeqId;
#if TRACE_EXECUTION
printf("%d: Sending THINKING_OVER (%d) to INV_41D63_eQ\n", _pid, INV_41D63__tmpE.name );
#endif

              INV_41D63_eQ!INV_41D63__tmpE;
              insertWithDelay(INV_41D63_eQ);
            }
            skip;
          }
          :: else -> skip;
          fi
         }
         :: i == 3 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for entering state %d\n", _pid, i);
#endif

          printf("Hungry professor: : %d", INV_41D63_p_id);
          if
          :: !INV_41D63_flags[USCXML_CTX_FINISHED] || INV_41D63_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
            {
              INV_41D63__tmpE.data.p_id = 0;
              INV_41D63__tmpE.delay = 0;
              INV_41D63__tmpE.invokeid = 0;
              INV_41D63__tmpE.name = 0;
              INV_41D63__tmpE.origin = 0;
              INV_41D63__tmpE.sendid = 0;
              INV_41D63__tmpE.seqNr = 0;
              INV_41D63__tmpE.name = NEED_FORKS;
              INV_41D63__tmpE.invokeid = INV_41D63;
              INV_41D63__tmpE.origin = INV_41D63;
              _lastSeqId = _lastSeqId + 1;
              INV_41D63__tmpE.delay = 300;
              INV_41D63__tmpE.seqNr = _lastSeqId;
              INV_41D63__tmpE.data.p_id = INV_41D63_p_id;
#if TRACE_EXECUTION
printf("%d: Sending NEED_FORKS (%d) to ROOT_eQ\n", _pid, INV_41D63__tmpE.name );
#endif

              ROOT_eQ!INV_41D63__tmpE;
              insertWithDelay(ROOT_eQ);
            }
            skip;
          }
          :: else -> skip;
          fi
         }
         :: i == 4 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for entering state %d\n", _pid, i);
#endif

          printf("Eating professor: : %d", INV_41D63_p_id);
          if
          :: !INV_41D63_flags[USCXML_CTX_FINISHED] || INV_41D63_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
            {
              INV_41D63__tmpE.data.p_id = 0;
              INV_41D63__tmpE.delay = 0;
              INV_41D63__tmpE.invokeid = 0;
              INV_41D63__tmpE.name = 0;
              INV_41D63__tmpE.origin = 0;
              INV_41D63__tmpE.sendid = 0;
              INV_41D63__tmpE.seqNr = 0;
              INV_41D63__tmpE.name = EATING_OVER;
              INV_41D63__tmpE.invokeid = INV_41D63;
              INV_41D63__tmpE.origin = INV_41D63;
              _lastSeqId = _lastSeqId + 1;
              INV_41D63__tmpE.delay = 500;
              INV_41D63__tmpE.seqNr = _lastSeqId;
#if TRACE_EXECUTION
printf("%d: Sending EATING_OVER (%d) to INV_41D63_eQ\n", _pid, INV_41D63__tmpE.name );
#endif

              INV_41D63_eQ!INV_41D63__tmpE;
              insertWithDelay(INV_41D63_eQ);
            }
            skip;
          }
          :: else -> skip;
          fi
         }
         :: i == 5 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for entering state %d\n", _pid, i);
#endif

          printf("Resource Denied professor: : %d", INV_41D63_p_id);
          if
          :: !INV_41D63_flags[USCXML_CTX_FINISHED] || INV_41D63_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
            {
              INV_41D63__tmpE.data.p_id = 0;
              INV_41D63__tmpE.delay = 0;
              INV_41D63__tmpE.invokeid = 0;
              INV_41D63__tmpE.name = 0;
              INV_41D63__tmpE.origin = 0;
              INV_41D63__tmpE.sendid = 0;
              INV_41D63__tmpE.seqNr = 0;
              INV_41D63__tmpE.name = TIMEOUT;
              INV_41D63__tmpE.sendid = RESOURCE_DENIED_TIMER;
              INV_41D63__tmpE.invokeid = INV_41D63;
              INV_41D63__tmpE.origin = INV_41D63;
              _lastSeqId = _lastSeqId + 1;
              INV_41D63__tmpE.delay = INV_41D63_delay;
              INV_41D63__tmpE.seqNr = _lastSeqId;
#if TRACE_EXECUTION
printf("%d: Sending TIMEOUT (%d) to INV_41D63_eQ\n", _pid, INV_41D63__tmpE.name );
#endif

              INV_41D63_eQ!INV_41D63__tmpE;
              insertWithDelay(INV_41D63_eQ);
            }
            skip;
          }
          :: else -> skip;
          fi
          if
          :: !INV_41D63_flags[USCXML_CTX_FINISHED] || INV_41D63_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
            {
              INV_41D63__tmpE.data.p_id = 0;
              INV_41D63__tmpE.delay = 0;
              INV_41D63__tmpE.invokeid = 0;
              INV_41D63__tmpE.name = 0;
              INV_41D63__tmpE.origin = 0;
              INV_41D63__tmpE.sendid = 0;
              INV_41D63__tmpE.seqNr = 0;
              INV_41D63__tmpE.name = RESEND_NEED_FORKS;
              INV_41D63__tmpE.invokeid = INV_41D63;
              INV_41D63__tmpE.origin = INV_41D63;
              _lastSeqId = _lastSeqId + 1;
              INV_41D63__tmpE.delay = 300;
              INV_41D63__tmpE.seqNr = _lastSeqId;
#if TRACE_EXECUTION
printf("%d: Sending RESEND_NEED_FORKS (%d) to INV_41D63_eQ\n", _pid, INV_41D63__tmpE.name );
#endif

              INV_41D63_eQ!INV_41D63__tmpE;
              insertWithDelay(INV_41D63_eQ);
            }
            skip;
          }
          :: else -> skip;
          fi
         }
         :: else ->skip;
         fi

         /* take history and initial transitions */
         j = 0;
         do
         :: j < INV_41D63_USCXML_NUMBER_TRANS -> {
           if
           :: (INV_41D63_ctx.trans_set[j] &&
              (INV_41D63_transitions[j].type[USCXML_TRANS_HISTORY] ||
               INV_41D63_transitions[j].type[USCXML_TRANS_INITIAL]) && 
               INV_41D63_states[INV_41D63_transitions[j].source].parent == i) -> {
              /* Call executable content in history or initial transition */
              if
              :: j == 0 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, j);
#endif

                skip;
              }
              :: j == 1 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, j);
#endif

                skip;
              }
              :: j == 2 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, j);
#endif

                skip;
              }
              :: j == 3 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, j);
#endif

                if
                :: !INV_41D63_flags[USCXML_CTX_FINISHED] || INV_41D63_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
                  {
                    INV_41D63__tmpE.data.p_id = 0;
                    INV_41D63__tmpE.delay = 0;
                    INV_41D63__tmpE.invokeid = 0;
                    INV_41D63__tmpE.name = 0;
                    INV_41D63__tmpE.origin = 0;
                    INV_41D63__tmpE.sendid = 0;
                    INV_41D63__tmpE.seqNr = 0;
                    INV_41D63__tmpE.name = RETURN_FORKS;
                    INV_41D63__tmpE.invokeid = INV_41D63;
                    INV_41D63__tmpE.origin = INV_41D63;
                    _lastSeqId = _lastSeqId + 1;
                    INV_41D63__tmpE.delay = 0;
                    INV_41D63__tmpE.seqNr = _lastSeqId;
                    INV_41D63__tmpE.data.p_id = INV_41D63_p_id;
#if TRACE_EXECUTION
printf("%d: Sending RETURN_FORKS (%d) to ROOT_eQ\n", _pid, INV_41D63__tmpE.name );
#endif

                    ROOT_eQ!INV_41D63__tmpE;
                    insertWithDelay(ROOT_eQ);
                  }
                  skip;
                }
                :: else -> skip;
                fi
                skip;
              }
              :: j == 4 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, j);
#endif

                skip;
              }
              :: j == 5 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, j);
#endif

                if
                :: !INV_41D63_flags[USCXML_CTX_FINISHED] || INV_41D63_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
                  {
                    INV_41D63__tmpE.data.p_id = 0;
                    INV_41D63__tmpE.delay = 0;
                    INV_41D63__tmpE.invokeid = 0;
                    INV_41D63__tmpE.name = 0;
                    INV_41D63__tmpE.origin = 0;
                    INV_41D63__tmpE.sendid = 0;
                    INV_41D63__tmpE.seqNr = 0;
                    INV_41D63__tmpE.name = NEED_FORKS;
                    INV_41D63__tmpE.invokeid = INV_41D63;
                    INV_41D63__tmpE.origin = INV_41D63;
                    _lastSeqId = _lastSeqId + 1;
                    INV_41D63__tmpE.delay = 0;
                    INV_41D63__tmpE.seqNr = _lastSeqId;
                    INV_41D63__tmpE.data.p_id = INV_41D63_p_id;
#if TRACE_EXECUTION
printf("%d: Sending NEED_FORKS (%d) to ROOT_eQ\n", _pid, INV_41D63__tmpE.name );
#endif

                    ROOT_eQ!INV_41D63__tmpE;
                    insertWithDelay(ROOT_eQ);
                  }
                  skip;
                }
                :: else -> skip;
                fi
                skip;
              }
              :: j == 6 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, j);
#endif

                printf("philospher: : %d", INV_41D63_p_id);
                printf("Time(in ms) since resource denied: : %d", INV_41D63_delay);
                skip;
              }
              :: else ->skip;
              fi

           }
           :: else -> skip;
           fi
           j = j + 1;
         }
         :: else -> break;
         od
         /* handle final states */
         if
         :: INV_41D63_states[i].type[USCXML_STATE_FINAL] -> {
           if
           :: INV_41D63_states[INV_41D63_states[i].parent].children[1] -> {
             /* exit topmost SCXML state */
             INV_41D63_flags[USCXML_CTX_TOP_LEVEL_FINAL] = true;
             INV_41D63_flags[USCXML_CTX_FINISHED] = true;
           }
           :: else -> {
             /* raise done event */
             if
             :: else -> skip;
             fi
           }
           fi
           /**
            * are we the last final state to leave a parallel state?:
            * 1. Gather all parallel states in our ancestor chain
            * 2. Find all states for which these parallels are ancestors
            * 3. Iterate all active final states and remove their ancestors
            * 4. If a state remains, not all children of a parallel are final
            */
            j = 0;
            do
            :: j < INV_41D63_USCXML_NUMBER_STATES -> {
              if
              :: INV_41D63_states[j].type[USCXML_STATE_PARALLEL] && INV_41D63_states[i].ancestors[j] -> {
                INV_41D63_STATES_CLEAR(INV_41D63_ctx.tmp_states)
                k = 0;
                do
                :: k < INV_41D63_USCXML_NUMBER_STATES -> {
                  if
                  :: INV_41D63_states[k].ancestors[j] && INV_41D63_config[k] -> {
                    if
                    :: INV_41D63_states[k].type[USCXML_STATE_FINAL] -> {
                      INV_41D63_STATES_AND_NOT(INV_41D63_ctx.tmp_states, INV_41D63_states[k].ancestors)
                    }
                    :: else -> {
                      INV_41D63_ctx.tmp_states[k] = true;
                    }
                    fi
                  }
                  :: else -> skip;
                  fi
                  k = k + 1;
                }
                :: else -> break;
                od
                if
                :: !INV_41D63_STATES_HAS_ANY(INV_41D63_ctx.tmp_states) -> {
                  if
                  :: else -> skip;
                  fi
                }
                :: else -> skip;
                fi
              }
              :: else -> skip;
              fi
              j = j + 1;
            }
            :: else -> break;
            od
         }
         :: else -> skip;
         fi

    }
    :: else -> skip;
    i = i + 1;
    fi;
  }
  :: else -> break;
  od;

  }
  :: else -> skip;
  fi /* USCXML_CTX_TRANSITION_FOUND */
  } skip; /* d_step */
} /* !USCXML_CTX_FINISHED */
:: else -> break;
od

/* ---------------------------- */
INV_41D63_TERMINATE_MACHINE:
skip; d_step {

#if TRACE_EXECUTION
printf("%d: Machine finished\n", _pid);
#endif

/* exit all remaining states */
i = INV_41D63_USCXML_NUMBER_STATES;
do
:: i > 0 -> {
  i = i - 1;
  if
  :: INV_41D63_config[i] && INV_41D63_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
    /* call all on exit handlers */
   if
    :: i == 5 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for exiting state %d\n", _pid, i);
#endif

    if
    :: (INV_41D63__event.name == TAKE_FORKS) -> {
        cancelSendId(RESOURCE_DENIED_TIMER,INV_41D63);
    }
    :: else -> skip;
    fi;
    }
    :: else -> skip;
    fi

    skip;
    
  }
  :: else -> skip;
  fi;

  if
  :: INV_41D63_invocations[i] -> {
    /* cancel invocations */
    INV_41D63_invocations[i] = false;
    if
    :: else -> skip;
    fi
    skip;

  }
  :: else -> skip;
  fi;
}
:: else -> break;
od;


#if TRACE_EXECUTION
printf("%d: Removing pending events\n", _pid);
#endif

removePendingEventsFromInvoker(INV_41D63)
/* send done event */
if
:: INV_41D63_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
    INV_41D63__tmpE.data.p_id = 0;
    INV_41D63__tmpE.delay = 0;
    INV_41D63__tmpE.invokeid = 0;
    INV_41D63__tmpE.name = 0;
    INV_41D63__tmpE.origin = 0;
    INV_41D63__tmpE.sendid = 0;
    INV_41D63__tmpE.seqNr = 0;

    INV_41D63__tmpE.name = DONE_INVOKE_INV_41D63
    INV_41D63__tmpE.invokeid = INV_41D63

#if TRACE_EXECUTION
printf("%d: Sending DONE.INVOKE\n", _pid);
#endif

    ROOT_eQ!INV_41D63__tmpE;
    insertWithDelay(ROOT_eQ);
}
:: else -> skip
fi;

} /* d_step */


#if TRACE_EXECUTION
printf("%d: Done\n", _pid);
#endif

} } /* atomic, step() */


init {
/* initialize state and transition information */
  ROOT_transitions[0].source = 2;
  ROOT_transitions[0].target[2] = 1;
  ROOT_transitions[0].conflicts[0] = 1;
  ROOT_transitions[0].conflicts[1] = 1;
  ROOT_transitions[0].conflicts[2] = 1;
  ROOT_transitions[0].exit_set[2] = 1;

  ROOT_transitions[1].source = 2;
  ROOT_transitions[1].target[2] = 1;
  ROOT_transitions[1].conflicts[0] = 1;
  ROOT_transitions[1].conflicts[1] = 1;
  ROOT_transitions[1].conflicts[2] = 1;
  ROOT_transitions[1].exit_set[2] = 1;

  ROOT_transitions[2].source = 2;
  ROOT_transitions[2].target[3] = 1;
  ROOT_transitions[2].conflicts[0] = 1;
  ROOT_transitions[2].conflicts[1] = 1;
  ROOT_transitions[2].conflicts[2] = 1;
  ROOT_transitions[2].exit_set[1] = 1;
  ROOT_transitions[2].exit_set[2] = 1;
  ROOT_transitions[2].exit_set[3] = 1;


  ROOT_states[0].parent = 0;
  ROOT_states[0].children[1] = 1;
  ROOT_states[0].children[3] = 1;
  ROOT_states[0].completion[1] = 1;
  ROOT_states[0].type[USCXML_STATE_COMPOUND] = 1;

  ROOT_states[1].parent = 0;
  ROOT_states[1].children[2] = 1;
  ROOT_states[1].completion[2] = 1;
  ROOT_states[1].ancestors[0] = 1;
  ROOT_states[1].type[USCXML_STATE_COMPOUND] = 1;

  ROOT_states[2].parent = 1;
  ROOT_states[2].ancestors[0] = 1;
  ROOT_states[2].ancestors[1] = 1;
  ROOT_states[2].type[USCXML_STATE_ATOMIC] = 1;

  ROOT_states[3].parent = 0;
  ROOT_states[3].ancestors[0] = 1;
  ROOT_states[3].type[USCXML_STATE_FINAL] = 1;


/* initialize data model variables */
  ROOT_flags[USCXML_CTX_PRISTINE]  = true;
  ROOT_flags[USCXML_CTX_SPONTANEOUS] = true;
  ROOT_forks[0] = 0;
  ROOT_forks[1] = 0;
  ROOT_forks[2] = 0;
  ROOT_forks[3] = 0;
  ROOT_forks[4] = 0;
  ROOT_NUM_OF_PHIL = 5;
  ROOT_current_phil = 0;
  ROOT_delay = 0;
  ROOT_left_fork = 0;
  ROOT_right_fork = 0;
  ROOT_seed = 123456789;
  INV_F5426_transitions[0].source = 2;
  INV_F5426_transitions[0].target[3] = 1;
  INV_F5426_transitions[0].conflicts[0] = 1;
  INV_F5426_transitions[0].conflicts[1] = 1;
  INV_F5426_transitions[0].conflicts[2] = 1;
  INV_F5426_transitions[0].conflicts[3] = 1;
  INV_F5426_transitions[0].conflicts[4] = 1;
  INV_F5426_transitions[0].conflicts[5] = 1;
  INV_F5426_transitions[0].conflicts[6] = 1;
  INV_F5426_transitions[0].exit_set[2] = 1;
  INV_F5426_transitions[0].exit_set[3] = 1;
  INV_F5426_transitions[0].exit_set[4] = 1;
  INV_F5426_transitions[0].exit_set[5] = 1;

  INV_F5426_transitions[1].source = 3;
  INV_F5426_transitions[1].target[4] = 1;
  INV_F5426_transitions[1].conflicts[0] = 1;
  INV_F5426_transitions[1].conflicts[1] = 1;
  INV_F5426_transitions[1].conflicts[2] = 1;
  INV_F5426_transitions[1].conflicts[3] = 1;
  INV_F5426_transitions[1].conflicts[4] = 1;
  INV_F5426_transitions[1].conflicts[5] = 1;
  INV_F5426_transitions[1].conflicts[6] = 1;
  INV_F5426_transitions[1].exit_set[2] = 1;
  INV_F5426_transitions[1].exit_set[3] = 1;
  INV_F5426_transitions[1].exit_set[4] = 1;
  INV_F5426_transitions[1].exit_set[5] = 1;

  INV_F5426_transitions[2].source = 3;
  INV_F5426_transitions[2].target[5] = 1;
  INV_F5426_transitions[2].conflicts[0] = 1;
  INV_F5426_transitions[2].conflicts[1] = 1;
  INV_F5426_transitions[2].conflicts[2] = 1;
  INV_F5426_transitions[2].conflicts[3] = 1;
  INV_F5426_transitions[2].conflicts[4] = 1;
  INV_F5426_transitions[2].conflicts[5] = 1;
  INV_F5426_transitions[2].conflicts[6] = 1;
  INV_F5426_transitions[2].exit_set[2] = 1;
  INV_F5426_transitions[2].exit_set[3] = 1;
  INV_F5426_transitions[2].exit_set[4] = 1;
  INV_F5426_transitions[2].exit_set[5] = 1;

  INV_F5426_transitions[3].source = 4;
  INV_F5426_transitions[3].target[2] = 1;
  INV_F5426_transitions[3].conflicts[0] = 1;
  INV_F5426_transitions[3].conflicts[1] = 1;
  INV_F5426_transitions[3].conflicts[2] = 1;
  INV_F5426_transitions[3].conflicts[3] = 1;
  INV_F5426_transitions[3].conflicts[4] = 1;
  INV_F5426_transitions[3].conflicts[5] = 1;
  INV_F5426_transitions[3].conflicts[6] = 1;
  INV_F5426_transitions[3].exit_set[2] = 1;
  INV_F5426_transitions[3].exit_set[3] = 1;
  INV_F5426_transitions[3].exit_set[4] = 1;
  INV_F5426_transitions[3].exit_set[5] = 1;

  INV_F5426_transitions[4].source = 5;
  INV_F5426_transitions[4].target[4] = 1;
  INV_F5426_transitions[4].conflicts[0] = 1;
  INV_F5426_transitions[4].conflicts[1] = 1;
  INV_F5426_transitions[4].conflicts[2] = 1;
  INV_F5426_transitions[4].conflicts[3] = 1;
  INV_F5426_transitions[4].conflicts[4] = 1;
  INV_F5426_transitions[4].conflicts[5] = 1;
  INV_F5426_transitions[4].conflicts[6] = 1;
  INV_F5426_transitions[4].exit_set[2] = 1;
  INV_F5426_transitions[4].exit_set[3] = 1;
  INV_F5426_transitions[4].exit_set[4] = 1;
  INV_F5426_transitions[4].exit_set[5] = 1;

  INV_F5426_transitions[5].source = 5;
  INV_F5426_transitions[5].target[5] = 1;
  INV_F5426_transitions[5].conflicts[0] = 1;
  INV_F5426_transitions[5].conflicts[1] = 1;
  INV_F5426_transitions[5].conflicts[2] = 1;
  INV_F5426_transitions[5].conflicts[3] = 1;
  INV_F5426_transitions[5].conflicts[4] = 1;
  INV_F5426_transitions[5].conflicts[5] = 1;
  INV_F5426_transitions[5].conflicts[6] = 1;
  INV_F5426_transitions[5].exit_set[2] = 1;
  INV_F5426_transitions[5].exit_set[3] = 1;
  INV_F5426_transitions[5].exit_set[4] = 1;
  INV_F5426_transitions[5].exit_set[5] = 1;

  INV_F5426_transitions[6].source = 5;
  INV_F5426_transitions[6].target[6] = 1;
  INV_F5426_transitions[6].conflicts[0] = 1;
  INV_F5426_transitions[6].conflicts[1] = 1;
  INV_F5426_transitions[6].conflicts[2] = 1;
  INV_F5426_transitions[6].conflicts[3] = 1;
  INV_F5426_transitions[6].conflicts[4] = 1;
  INV_F5426_transitions[6].conflicts[5] = 1;
  INV_F5426_transitions[6].conflicts[6] = 1;
  INV_F5426_transitions[6].exit_set[1] = 1;
  INV_F5426_transitions[6].exit_set[2] = 1;
  INV_F5426_transitions[6].exit_set[3] = 1;
  INV_F5426_transitions[6].exit_set[4] = 1;
  INV_F5426_transitions[6].exit_set[5] = 1;
  INV_F5426_transitions[6].exit_set[6] = 1;


  INV_F5426_states[0].parent = 0;
  INV_F5426_states[0].children[1] = 1;
  INV_F5426_states[0].children[6] = 1;
  INV_F5426_states[0].completion[1] = 1;
  INV_F5426_states[0].type[USCXML_STATE_COMPOUND] = 1;

  INV_F5426_states[1].parent = 0;
  INV_F5426_states[1].children[2] = 1;
  INV_F5426_states[1].children[3] = 1;
  INV_F5426_states[1].children[4] = 1;
  INV_F5426_states[1].children[5] = 1;
  INV_F5426_states[1].completion[2] = 1;
  INV_F5426_states[1].ancestors[0] = 1;
  INV_F5426_states[1].type[USCXML_STATE_COMPOUND] = 1;

  INV_F5426_states[2].parent = 1;
  INV_F5426_states[2].ancestors[0] = 1;
  INV_F5426_states[2].ancestors[1] = 1;
  INV_F5426_states[2].type[USCXML_STATE_ATOMIC] = 1;

  INV_F5426_states[3].parent = 1;
  INV_F5426_states[3].ancestors[0] = 1;
  INV_F5426_states[3].ancestors[1] = 1;
  INV_F5426_states[3].type[USCXML_STATE_ATOMIC] = 1;

  INV_F5426_states[4].parent = 1;
  INV_F5426_states[4].ancestors[0] = 1;
  INV_F5426_states[4].ancestors[1] = 1;
  INV_F5426_states[4].type[USCXML_STATE_ATOMIC] = 1;

  INV_F5426_states[5].parent = 1;
  INV_F5426_states[5].ancestors[0] = 1;
  INV_F5426_states[5].ancestors[1] = 1;
  INV_F5426_states[5].type[USCXML_STATE_ATOMIC] = 1;

  INV_F5426_states[6].parent = 0;
  INV_F5426_states[6].ancestors[0] = 1;
  INV_F5426_states[6].type[USCXML_STATE_FINAL] = 1;


/* initialize data model variables */
  INV_F5426_flags[USCXML_CTX_PRISTINE]  = true;
  INV_F5426_flags[USCXML_CTX_SPONTANEOUS] = true;
  INV_8CB85_transitions[0].source = 2;
  INV_8CB85_transitions[0].target[3] = 1;
  INV_8CB85_transitions[0].conflicts[0] = 1;
  INV_8CB85_transitions[0].conflicts[1] = 1;
  INV_8CB85_transitions[0].conflicts[2] = 1;
  INV_8CB85_transitions[0].conflicts[3] = 1;
  INV_8CB85_transitions[0].conflicts[4] = 1;
  INV_8CB85_transitions[0].conflicts[5] = 1;
  INV_8CB85_transitions[0].conflicts[6] = 1;
  INV_8CB85_transitions[0].exit_set[2] = 1;
  INV_8CB85_transitions[0].exit_set[3] = 1;
  INV_8CB85_transitions[0].exit_set[4] = 1;
  INV_8CB85_transitions[0].exit_set[5] = 1;

  INV_8CB85_transitions[1].source = 3;
  INV_8CB85_transitions[1].target[4] = 1;
  INV_8CB85_transitions[1].conflicts[0] = 1;
  INV_8CB85_transitions[1].conflicts[1] = 1;
  INV_8CB85_transitions[1].conflicts[2] = 1;
  INV_8CB85_transitions[1].conflicts[3] = 1;
  INV_8CB85_transitions[1].conflicts[4] = 1;
  INV_8CB85_transitions[1].conflicts[5] = 1;
  INV_8CB85_transitions[1].conflicts[6] = 1;
  INV_8CB85_transitions[1].exit_set[2] = 1;
  INV_8CB85_transitions[1].exit_set[3] = 1;
  INV_8CB85_transitions[1].exit_set[4] = 1;
  INV_8CB85_transitions[1].exit_set[5] = 1;

  INV_8CB85_transitions[2].source = 3;
  INV_8CB85_transitions[2].target[5] = 1;
  INV_8CB85_transitions[2].conflicts[0] = 1;
  INV_8CB85_transitions[2].conflicts[1] = 1;
  INV_8CB85_transitions[2].conflicts[2] = 1;
  INV_8CB85_transitions[2].conflicts[3] = 1;
  INV_8CB85_transitions[2].conflicts[4] = 1;
  INV_8CB85_transitions[2].conflicts[5] = 1;
  INV_8CB85_transitions[2].conflicts[6] = 1;
  INV_8CB85_transitions[2].exit_set[2] = 1;
  INV_8CB85_transitions[2].exit_set[3] = 1;
  INV_8CB85_transitions[2].exit_set[4] = 1;
  INV_8CB85_transitions[2].exit_set[5] = 1;

  INV_8CB85_transitions[3].source = 4;
  INV_8CB85_transitions[3].target[2] = 1;
  INV_8CB85_transitions[3].conflicts[0] = 1;
  INV_8CB85_transitions[3].conflicts[1] = 1;
  INV_8CB85_transitions[3].conflicts[2] = 1;
  INV_8CB85_transitions[3].conflicts[3] = 1;
  INV_8CB85_transitions[3].conflicts[4] = 1;
  INV_8CB85_transitions[3].conflicts[5] = 1;
  INV_8CB85_transitions[3].conflicts[6] = 1;
  INV_8CB85_transitions[3].exit_set[2] = 1;
  INV_8CB85_transitions[3].exit_set[3] = 1;
  INV_8CB85_transitions[3].exit_set[4] = 1;
  INV_8CB85_transitions[3].exit_set[5] = 1;

  INV_8CB85_transitions[4].source = 5;
  INV_8CB85_transitions[4].target[4] = 1;
  INV_8CB85_transitions[4].conflicts[0] = 1;
  INV_8CB85_transitions[4].conflicts[1] = 1;
  INV_8CB85_transitions[4].conflicts[2] = 1;
  INV_8CB85_transitions[4].conflicts[3] = 1;
  INV_8CB85_transitions[4].conflicts[4] = 1;
  INV_8CB85_transitions[4].conflicts[5] = 1;
  INV_8CB85_transitions[4].conflicts[6] = 1;
  INV_8CB85_transitions[4].exit_set[2] = 1;
  INV_8CB85_transitions[4].exit_set[3] = 1;
  INV_8CB85_transitions[4].exit_set[4] = 1;
  INV_8CB85_transitions[4].exit_set[5] = 1;

  INV_8CB85_transitions[5].source = 5;
  INV_8CB85_transitions[5].target[5] = 1;
  INV_8CB85_transitions[5].conflicts[0] = 1;
  INV_8CB85_transitions[5].conflicts[1] = 1;
  INV_8CB85_transitions[5].conflicts[2] = 1;
  INV_8CB85_transitions[5].conflicts[3] = 1;
  INV_8CB85_transitions[5].conflicts[4] = 1;
  INV_8CB85_transitions[5].conflicts[5] = 1;
  INV_8CB85_transitions[5].conflicts[6] = 1;
  INV_8CB85_transitions[5].exit_set[2] = 1;
  INV_8CB85_transitions[5].exit_set[3] = 1;
  INV_8CB85_transitions[5].exit_set[4] = 1;
  INV_8CB85_transitions[5].exit_set[5] = 1;

  INV_8CB85_transitions[6].source = 5;
  INV_8CB85_transitions[6].target[6] = 1;
  INV_8CB85_transitions[6].conflicts[0] = 1;
  INV_8CB85_transitions[6].conflicts[1] = 1;
  INV_8CB85_transitions[6].conflicts[2] = 1;
  INV_8CB85_transitions[6].conflicts[3] = 1;
  INV_8CB85_transitions[6].conflicts[4] = 1;
  INV_8CB85_transitions[6].conflicts[5] = 1;
  INV_8CB85_transitions[6].conflicts[6] = 1;
  INV_8CB85_transitions[6].exit_set[1] = 1;
  INV_8CB85_transitions[6].exit_set[2] = 1;
  INV_8CB85_transitions[6].exit_set[3] = 1;
  INV_8CB85_transitions[6].exit_set[4] = 1;
  INV_8CB85_transitions[6].exit_set[5] = 1;
  INV_8CB85_transitions[6].exit_set[6] = 1;


  INV_8CB85_states[0].parent = 0;
  INV_8CB85_states[0].children[1] = 1;
  INV_8CB85_states[0].children[6] = 1;
  INV_8CB85_states[0].completion[1] = 1;
  INV_8CB85_states[0].type[USCXML_STATE_COMPOUND] = 1;

  INV_8CB85_states[1].parent = 0;
  INV_8CB85_states[1].children[2] = 1;
  INV_8CB85_states[1].children[3] = 1;
  INV_8CB85_states[1].children[4] = 1;
  INV_8CB85_states[1].children[5] = 1;
  INV_8CB85_states[1].completion[2] = 1;
  INV_8CB85_states[1].ancestors[0] = 1;
  INV_8CB85_states[1].type[USCXML_STATE_COMPOUND] = 1;

  INV_8CB85_states[2].parent = 1;
  INV_8CB85_states[2].ancestors[0] = 1;
  INV_8CB85_states[2].ancestors[1] = 1;
  INV_8CB85_states[2].type[USCXML_STATE_ATOMIC] = 1;

  INV_8CB85_states[3].parent = 1;
  INV_8CB85_states[3].ancestors[0] = 1;
  INV_8CB85_states[3].ancestors[1] = 1;
  INV_8CB85_states[3].type[USCXML_STATE_ATOMIC] = 1;

  INV_8CB85_states[4].parent = 1;
  INV_8CB85_states[4].ancestors[0] = 1;
  INV_8CB85_states[4].ancestors[1] = 1;
  INV_8CB85_states[4].type[USCXML_STATE_ATOMIC] = 1;

  INV_8CB85_states[5].parent = 1;
  INV_8CB85_states[5].ancestors[0] = 1;
  INV_8CB85_states[5].ancestors[1] = 1;
  INV_8CB85_states[5].type[USCXML_STATE_ATOMIC] = 1;

  INV_8CB85_states[6].parent = 0;
  INV_8CB85_states[6].ancestors[0] = 1;
  INV_8CB85_states[6].type[USCXML_STATE_FINAL] = 1;


/* initialize data model variables */
  INV_8CB85_flags[USCXML_CTX_PRISTINE]  = true;
  INV_8CB85_flags[USCXML_CTX_SPONTANEOUS] = true;
  INV_5C805_transitions[0].source = 2;
  INV_5C805_transitions[0].target[3] = 1;
  INV_5C805_transitions[0].conflicts[0] = 1;
  INV_5C805_transitions[0].conflicts[1] = 1;
  INV_5C805_transitions[0].conflicts[2] = 1;
  INV_5C805_transitions[0].conflicts[3] = 1;
  INV_5C805_transitions[0].conflicts[4] = 1;
  INV_5C805_transitions[0].conflicts[5] = 1;
  INV_5C805_transitions[0].conflicts[6] = 1;
  INV_5C805_transitions[0].exit_set[2] = 1;
  INV_5C805_transitions[0].exit_set[3] = 1;
  INV_5C805_transitions[0].exit_set[4] = 1;
  INV_5C805_transitions[0].exit_set[5] = 1;

  INV_5C805_transitions[1].source = 3;
  INV_5C805_transitions[1].target[4] = 1;
  INV_5C805_transitions[1].conflicts[0] = 1;
  INV_5C805_transitions[1].conflicts[1] = 1;
  INV_5C805_transitions[1].conflicts[2] = 1;
  INV_5C805_transitions[1].conflicts[3] = 1;
  INV_5C805_transitions[1].conflicts[4] = 1;
  INV_5C805_transitions[1].conflicts[5] = 1;
  INV_5C805_transitions[1].conflicts[6] = 1;
  INV_5C805_transitions[1].exit_set[2] = 1;
  INV_5C805_transitions[1].exit_set[3] = 1;
  INV_5C805_transitions[1].exit_set[4] = 1;
  INV_5C805_transitions[1].exit_set[5] = 1;

  INV_5C805_transitions[2].source = 3;
  INV_5C805_transitions[2].target[5] = 1;
  INV_5C805_transitions[2].conflicts[0] = 1;
  INV_5C805_transitions[2].conflicts[1] = 1;
  INV_5C805_transitions[2].conflicts[2] = 1;
  INV_5C805_transitions[2].conflicts[3] = 1;
  INV_5C805_transitions[2].conflicts[4] = 1;
  INV_5C805_transitions[2].conflicts[5] = 1;
  INV_5C805_transitions[2].conflicts[6] = 1;
  INV_5C805_transitions[2].exit_set[2] = 1;
  INV_5C805_transitions[2].exit_set[3] = 1;
  INV_5C805_transitions[2].exit_set[4] = 1;
  INV_5C805_transitions[2].exit_set[5] = 1;

  INV_5C805_transitions[3].source = 4;
  INV_5C805_transitions[3].target[2] = 1;
  INV_5C805_transitions[3].conflicts[0] = 1;
  INV_5C805_transitions[3].conflicts[1] = 1;
  INV_5C805_transitions[3].conflicts[2] = 1;
  INV_5C805_transitions[3].conflicts[3] = 1;
  INV_5C805_transitions[3].conflicts[4] = 1;
  INV_5C805_transitions[3].conflicts[5] = 1;
  INV_5C805_transitions[3].conflicts[6] = 1;
  INV_5C805_transitions[3].exit_set[2] = 1;
  INV_5C805_transitions[3].exit_set[3] = 1;
  INV_5C805_transitions[3].exit_set[4] = 1;
  INV_5C805_transitions[3].exit_set[5] = 1;

  INV_5C805_transitions[4].source = 5;
  INV_5C805_transitions[4].target[4] = 1;
  INV_5C805_transitions[4].conflicts[0] = 1;
  INV_5C805_transitions[4].conflicts[1] = 1;
  INV_5C805_transitions[4].conflicts[2] = 1;
  INV_5C805_transitions[4].conflicts[3] = 1;
  INV_5C805_transitions[4].conflicts[4] = 1;
  INV_5C805_transitions[4].conflicts[5] = 1;
  INV_5C805_transitions[4].conflicts[6] = 1;
  INV_5C805_transitions[4].exit_set[2] = 1;
  INV_5C805_transitions[4].exit_set[3] = 1;
  INV_5C805_transitions[4].exit_set[4] = 1;
  INV_5C805_transitions[4].exit_set[5] = 1;

  INV_5C805_transitions[5].source = 5;
  INV_5C805_transitions[5].target[5] = 1;
  INV_5C805_transitions[5].conflicts[0] = 1;
  INV_5C805_transitions[5].conflicts[1] = 1;
  INV_5C805_transitions[5].conflicts[2] = 1;
  INV_5C805_transitions[5].conflicts[3] = 1;
  INV_5C805_transitions[5].conflicts[4] = 1;
  INV_5C805_transitions[5].conflicts[5] = 1;
  INV_5C805_transitions[5].conflicts[6] = 1;
  INV_5C805_transitions[5].exit_set[2] = 1;
  INV_5C805_transitions[5].exit_set[3] = 1;
  INV_5C805_transitions[5].exit_set[4] = 1;
  INV_5C805_transitions[5].exit_set[5] = 1;

  INV_5C805_transitions[6].source = 5;
  INV_5C805_transitions[6].target[6] = 1;
  INV_5C805_transitions[6].conflicts[0] = 1;
  INV_5C805_transitions[6].conflicts[1] = 1;
  INV_5C805_transitions[6].conflicts[2] = 1;
  INV_5C805_transitions[6].conflicts[3] = 1;
  INV_5C805_transitions[6].conflicts[4] = 1;
  INV_5C805_transitions[6].conflicts[5] = 1;
  INV_5C805_transitions[6].conflicts[6] = 1;
  INV_5C805_transitions[6].exit_set[1] = 1;
  INV_5C805_transitions[6].exit_set[2] = 1;
  INV_5C805_transitions[6].exit_set[3] = 1;
  INV_5C805_transitions[6].exit_set[4] = 1;
  INV_5C805_transitions[6].exit_set[5] = 1;
  INV_5C805_transitions[6].exit_set[6] = 1;


  INV_5C805_states[0].parent = 0;
  INV_5C805_states[0].children[1] = 1;
  INV_5C805_states[0].children[6] = 1;
  INV_5C805_states[0].completion[1] = 1;
  INV_5C805_states[0].type[USCXML_STATE_COMPOUND] = 1;

  INV_5C805_states[1].parent = 0;
  INV_5C805_states[1].children[2] = 1;
  INV_5C805_states[1].children[3] = 1;
  INV_5C805_states[1].children[4] = 1;
  INV_5C805_states[1].children[5] = 1;
  INV_5C805_states[1].completion[2] = 1;
  INV_5C805_states[1].ancestors[0] = 1;
  INV_5C805_states[1].type[USCXML_STATE_COMPOUND] = 1;

  INV_5C805_states[2].parent = 1;
  INV_5C805_states[2].ancestors[0] = 1;
  INV_5C805_states[2].ancestors[1] = 1;
  INV_5C805_states[2].type[USCXML_STATE_ATOMIC] = 1;

  INV_5C805_states[3].parent = 1;
  INV_5C805_states[3].ancestors[0] = 1;
  INV_5C805_states[3].ancestors[1] = 1;
  INV_5C805_states[3].type[USCXML_STATE_ATOMIC] = 1;

  INV_5C805_states[4].parent = 1;
  INV_5C805_states[4].ancestors[0] = 1;
  INV_5C805_states[4].ancestors[1] = 1;
  INV_5C805_states[4].type[USCXML_STATE_ATOMIC] = 1;

  INV_5C805_states[5].parent = 1;
  INV_5C805_states[5].ancestors[0] = 1;
  INV_5C805_states[5].ancestors[1] = 1;
  INV_5C805_states[5].type[USCXML_STATE_ATOMIC] = 1;

  INV_5C805_states[6].parent = 0;
  INV_5C805_states[6].ancestors[0] = 1;
  INV_5C805_states[6].type[USCXML_STATE_FINAL] = 1;


/* initialize data model variables */
  INV_5C805_flags[USCXML_CTX_PRISTINE]  = true;
  INV_5C805_flags[USCXML_CTX_SPONTANEOUS] = true;
  INV_F88AA_transitions[0].source = 2;
  INV_F88AA_transitions[0].target[3] = 1;
  INV_F88AA_transitions[0].conflicts[0] = 1;
  INV_F88AA_transitions[0].conflicts[1] = 1;
  INV_F88AA_transitions[0].conflicts[2] = 1;
  INV_F88AA_transitions[0].conflicts[3] = 1;
  INV_F88AA_transitions[0].conflicts[4] = 1;
  INV_F88AA_transitions[0].conflicts[5] = 1;
  INV_F88AA_transitions[0].conflicts[6] = 1;
  INV_F88AA_transitions[0].exit_set[2] = 1;
  INV_F88AA_transitions[0].exit_set[3] = 1;
  INV_F88AA_transitions[0].exit_set[4] = 1;
  INV_F88AA_transitions[0].exit_set[5] = 1;

  INV_F88AA_transitions[1].source = 3;
  INV_F88AA_transitions[1].target[4] = 1;
  INV_F88AA_transitions[1].conflicts[0] = 1;
  INV_F88AA_transitions[1].conflicts[1] = 1;
  INV_F88AA_transitions[1].conflicts[2] = 1;
  INV_F88AA_transitions[1].conflicts[3] = 1;
  INV_F88AA_transitions[1].conflicts[4] = 1;
  INV_F88AA_transitions[1].conflicts[5] = 1;
  INV_F88AA_transitions[1].conflicts[6] = 1;
  INV_F88AA_transitions[1].exit_set[2] = 1;
  INV_F88AA_transitions[1].exit_set[3] = 1;
  INV_F88AA_transitions[1].exit_set[4] = 1;
  INV_F88AA_transitions[1].exit_set[5] = 1;

  INV_F88AA_transitions[2].source = 3;
  INV_F88AA_transitions[2].target[5] = 1;
  INV_F88AA_transitions[2].conflicts[0] = 1;
  INV_F88AA_transitions[2].conflicts[1] = 1;
  INV_F88AA_transitions[2].conflicts[2] = 1;
  INV_F88AA_transitions[2].conflicts[3] = 1;
  INV_F88AA_transitions[2].conflicts[4] = 1;
  INV_F88AA_transitions[2].conflicts[5] = 1;
  INV_F88AA_transitions[2].conflicts[6] = 1;
  INV_F88AA_transitions[2].exit_set[2] = 1;
  INV_F88AA_transitions[2].exit_set[3] = 1;
  INV_F88AA_transitions[2].exit_set[4] = 1;
  INV_F88AA_transitions[2].exit_set[5] = 1;

  INV_F88AA_transitions[3].source = 4;
  INV_F88AA_transitions[3].target[2] = 1;
  INV_F88AA_transitions[3].conflicts[0] = 1;
  INV_F88AA_transitions[3].conflicts[1] = 1;
  INV_F88AA_transitions[3].conflicts[2] = 1;
  INV_F88AA_transitions[3].conflicts[3] = 1;
  INV_F88AA_transitions[3].conflicts[4] = 1;
  INV_F88AA_transitions[3].conflicts[5] = 1;
  INV_F88AA_transitions[3].conflicts[6] = 1;
  INV_F88AA_transitions[3].exit_set[2] = 1;
  INV_F88AA_transitions[3].exit_set[3] = 1;
  INV_F88AA_transitions[3].exit_set[4] = 1;
  INV_F88AA_transitions[3].exit_set[5] = 1;

  INV_F88AA_transitions[4].source = 5;
  INV_F88AA_transitions[4].target[4] = 1;
  INV_F88AA_transitions[4].conflicts[0] = 1;
  INV_F88AA_transitions[4].conflicts[1] = 1;
  INV_F88AA_transitions[4].conflicts[2] = 1;
  INV_F88AA_transitions[4].conflicts[3] = 1;
  INV_F88AA_transitions[4].conflicts[4] = 1;
  INV_F88AA_transitions[4].conflicts[5] = 1;
  INV_F88AA_transitions[4].conflicts[6] = 1;
  INV_F88AA_transitions[4].exit_set[2] = 1;
  INV_F88AA_transitions[4].exit_set[3] = 1;
  INV_F88AA_transitions[4].exit_set[4] = 1;
  INV_F88AA_transitions[4].exit_set[5] = 1;

  INV_F88AA_transitions[5].source = 5;
  INV_F88AA_transitions[5].target[5] = 1;
  INV_F88AA_transitions[5].conflicts[0] = 1;
  INV_F88AA_transitions[5].conflicts[1] = 1;
  INV_F88AA_transitions[5].conflicts[2] = 1;
  INV_F88AA_transitions[5].conflicts[3] = 1;
  INV_F88AA_transitions[5].conflicts[4] = 1;
  INV_F88AA_transitions[5].conflicts[5] = 1;
  INV_F88AA_transitions[5].conflicts[6] = 1;
  INV_F88AA_transitions[5].exit_set[2] = 1;
  INV_F88AA_transitions[5].exit_set[3] = 1;
  INV_F88AA_transitions[5].exit_set[4] = 1;
  INV_F88AA_transitions[5].exit_set[5] = 1;

  INV_F88AA_transitions[6].source = 5;
  INV_F88AA_transitions[6].target[6] = 1;
  INV_F88AA_transitions[6].conflicts[0] = 1;
  INV_F88AA_transitions[6].conflicts[1] = 1;
  INV_F88AA_transitions[6].conflicts[2] = 1;
  INV_F88AA_transitions[6].conflicts[3] = 1;
  INV_F88AA_transitions[6].conflicts[4] = 1;
  INV_F88AA_transitions[6].conflicts[5] = 1;
  INV_F88AA_transitions[6].conflicts[6] = 1;
  INV_F88AA_transitions[6].exit_set[1] = 1;
  INV_F88AA_transitions[6].exit_set[2] = 1;
  INV_F88AA_transitions[6].exit_set[3] = 1;
  INV_F88AA_transitions[6].exit_set[4] = 1;
  INV_F88AA_transitions[6].exit_set[5] = 1;
  INV_F88AA_transitions[6].exit_set[6] = 1;


  INV_F88AA_states[0].parent = 0;
  INV_F88AA_states[0].children[1] = 1;
  INV_F88AA_states[0].children[6] = 1;
  INV_F88AA_states[0].completion[1] = 1;
  INV_F88AA_states[0].type[USCXML_STATE_COMPOUND] = 1;

  INV_F88AA_states[1].parent = 0;
  INV_F88AA_states[1].children[2] = 1;
  INV_F88AA_states[1].children[3] = 1;
  INV_F88AA_states[1].children[4] = 1;
  INV_F88AA_states[1].children[5] = 1;
  INV_F88AA_states[1].completion[2] = 1;
  INV_F88AA_states[1].ancestors[0] = 1;
  INV_F88AA_states[1].type[USCXML_STATE_COMPOUND] = 1;

  INV_F88AA_states[2].parent = 1;
  INV_F88AA_states[2].ancestors[0] = 1;
  INV_F88AA_states[2].ancestors[1] = 1;
  INV_F88AA_states[2].type[USCXML_STATE_ATOMIC] = 1;

  INV_F88AA_states[3].parent = 1;
  INV_F88AA_states[3].ancestors[0] = 1;
  INV_F88AA_states[3].ancestors[1] = 1;
  INV_F88AA_states[3].type[USCXML_STATE_ATOMIC] = 1;

  INV_F88AA_states[4].parent = 1;
  INV_F88AA_states[4].ancestors[0] = 1;
  INV_F88AA_states[4].ancestors[1] = 1;
  INV_F88AA_states[4].type[USCXML_STATE_ATOMIC] = 1;

  INV_F88AA_states[5].parent = 1;
  INV_F88AA_states[5].ancestors[0] = 1;
  INV_F88AA_states[5].ancestors[1] = 1;
  INV_F88AA_states[5].type[USCXML_STATE_ATOMIC] = 1;

  INV_F88AA_states[6].parent = 0;
  INV_F88AA_states[6].ancestors[0] = 1;
  INV_F88AA_states[6].type[USCXML_STATE_FINAL] = 1;


/* initialize data model variables */
  INV_F88AA_flags[USCXML_CTX_PRISTINE]  = true;
  INV_F88AA_flags[USCXML_CTX_SPONTANEOUS] = true;
  INV_41D63_transitions[0].source = 2;
  INV_41D63_transitions[0].target[3] = 1;
  INV_41D63_transitions[0].conflicts[0] = 1;
  INV_41D63_transitions[0].conflicts[1] = 1;
  INV_41D63_transitions[0].conflicts[2] = 1;
  INV_41D63_transitions[0].conflicts[3] = 1;
  INV_41D63_transitions[0].conflicts[4] = 1;
  INV_41D63_transitions[0].conflicts[5] = 1;
  INV_41D63_transitions[0].conflicts[6] = 1;
  INV_41D63_transitions[0].exit_set[2] = 1;
  INV_41D63_transitions[0].exit_set[3] = 1;
  INV_41D63_transitions[0].exit_set[4] = 1;
  INV_41D63_transitions[0].exit_set[5] = 1;

  INV_41D63_transitions[1].source = 3;
  INV_41D63_transitions[1].target[4] = 1;
  INV_41D63_transitions[1].conflicts[0] = 1;
  INV_41D63_transitions[1].conflicts[1] = 1;
  INV_41D63_transitions[1].conflicts[2] = 1;
  INV_41D63_transitions[1].conflicts[3] = 1;
  INV_41D63_transitions[1].conflicts[4] = 1;
  INV_41D63_transitions[1].conflicts[5] = 1;
  INV_41D63_transitions[1].conflicts[6] = 1;
  INV_41D63_transitions[1].exit_set[2] = 1;
  INV_41D63_transitions[1].exit_set[3] = 1;
  INV_41D63_transitions[1].exit_set[4] = 1;
  INV_41D63_transitions[1].exit_set[5] = 1;

  INV_41D63_transitions[2].source = 3;
  INV_41D63_transitions[2].target[5] = 1;
  INV_41D63_transitions[2].conflicts[0] = 1;
  INV_41D63_transitions[2].conflicts[1] = 1;
  INV_41D63_transitions[2].conflicts[2] = 1;
  INV_41D63_transitions[2].conflicts[3] = 1;
  INV_41D63_transitions[2].conflicts[4] = 1;
  INV_41D63_transitions[2].conflicts[5] = 1;
  INV_41D63_transitions[2].conflicts[6] = 1;
  INV_41D63_transitions[2].exit_set[2] = 1;
  INV_41D63_transitions[2].exit_set[3] = 1;
  INV_41D63_transitions[2].exit_set[4] = 1;
  INV_41D63_transitions[2].exit_set[5] = 1;

  INV_41D63_transitions[3].source = 4;
  INV_41D63_transitions[3].target[2] = 1;
  INV_41D63_transitions[3].conflicts[0] = 1;
  INV_41D63_transitions[3].conflicts[1] = 1;
  INV_41D63_transitions[3].conflicts[2] = 1;
  INV_41D63_transitions[3].conflicts[3] = 1;
  INV_41D63_transitions[3].conflicts[4] = 1;
  INV_41D63_transitions[3].conflicts[5] = 1;
  INV_41D63_transitions[3].conflicts[6] = 1;
  INV_41D63_transitions[3].exit_set[2] = 1;
  INV_41D63_transitions[3].exit_set[3] = 1;
  INV_41D63_transitions[3].exit_set[4] = 1;
  INV_41D63_transitions[3].exit_set[5] = 1;

  INV_41D63_transitions[4].source = 5;
  INV_41D63_transitions[4].target[4] = 1;
  INV_41D63_transitions[4].conflicts[0] = 1;
  INV_41D63_transitions[4].conflicts[1] = 1;
  INV_41D63_transitions[4].conflicts[2] = 1;
  INV_41D63_transitions[4].conflicts[3] = 1;
  INV_41D63_transitions[4].conflicts[4] = 1;
  INV_41D63_transitions[4].conflicts[5] = 1;
  INV_41D63_transitions[4].conflicts[6] = 1;
  INV_41D63_transitions[4].exit_set[2] = 1;
  INV_41D63_transitions[4].exit_set[3] = 1;
  INV_41D63_transitions[4].exit_set[4] = 1;
  INV_41D63_transitions[4].exit_set[5] = 1;

  INV_41D63_transitions[5].source = 5;
  INV_41D63_transitions[5].target[5] = 1;
  INV_41D63_transitions[5].conflicts[0] = 1;
  INV_41D63_transitions[5].conflicts[1] = 1;
  INV_41D63_transitions[5].conflicts[2] = 1;
  INV_41D63_transitions[5].conflicts[3] = 1;
  INV_41D63_transitions[5].conflicts[4] = 1;
  INV_41D63_transitions[5].conflicts[5] = 1;
  INV_41D63_transitions[5].conflicts[6] = 1;
  INV_41D63_transitions[5].exit_set[2] = 1;
  INV_41D63_transitions[5].exit_set[3] = 1;
  INV_41D63_transitions[5].exit_set[4] = 1;
  INV_41D63_transitions[5].exit_set[5] = 1;

  INV_41D63_transitions[6].source = 5;
  INV_41D63_transitions[6].target[6] = 1;
  INV_41D63_transitions[6].conflicts[0] = 1;
  INV_41D63_transitions[6].conflicts[1] = 1;
  INV_41D63_transitions[6].conflicts[2] = 1;
  INV_41D63_transitions[6].conflicts[3] = 1;
  INV_41D63_transitions[6].conflicts[4] = 1;
  INV_41D63_transitions[6].conflicts[5] = 1;
  INV_41D63_transitions[6].conflicts[6] = 1;
  INV_41D63_transitions[6].exit_set[1] = 1;
  INV_41D63_transitions[6].exit_set[2] = 1;
  INV_41D63_transitions[6].exit_set[3] = 1;
  INV_41D63_transitions[6].exit_set[4] = 1;
  INV_41D63_transitions[6].exit_set[5] = 1;
  INV_41D63_transitions[6].exit_set[6] = 1;


  INV_41D63_states[0].parent = 0;
  INV_41D63_states[0].children[1] = 1;
  INV_41D63_states[0].children[6] = 1;
  INV_41D63_states[0].completion[1] = 1;
  INV_41D63_states[0].type[USCXML_STATE_COMPOUND] = 1;

  INV_41D63_states[1].parent = 0;
  INV_41D63_states[1].children[2] = 1;
  INV_41D63_states[1].children[3] = 1;
  INV_41D63_states[1].children[4] = 1;
  INV_41D63_states[1].children[5] = 1;
  INV_41D63_states[1].completion[2] = 1;
  INV_41D63_states[1].ancestors[0] = 1;
  INV_41D63_states[1].type[USCXML_STATE_COMPOUND] = 1;

  INV_41D63_states[2].parent = 1;
  INV_41D63_states[2].ancestors[0] = 1;
  INV_41D63_states[2].ancestors[1] = 1;
  INV_41D63_states[2].type[USCXML_STATE_ATOMIC] = 1;

  INV_41D63_states[3].parent = 1;
  INV_41D63_states[3].ancestors[0] = 1;
  INV_41D63_states[3].ancestors[1] = 1;
  INV_41D63_states[3].type[USCXML_STATE_ATOMIC] = 1;

  INV_41D63_states[4].parent = 1;
  INV_41D63_states[4].ancestors[0] = 1;
  INV_41D63_states[4].ancestors[1] = 1;
  INV_41D63_states[4].type[USCXML_STATE_ATOMIC] = 1;

  INV_41D63_states[5].parent = 1;
  INV_41D63_states[5].ancestors[0] = 1;
  INV_41D63_states[5].ancestors[1] = 1;
  INV_41D63_states[5].type[USCXML_STATE_ATOMIC] = 1;

  INV_41D63_states[6].parent = 0;
  INV_41D63_states[6].ancestors[0] = 1;
  INV_41D63_states[6].type[USCXML_STATE_FINAL] = 1;


/* initialize data model variables */
  INV_41D63_flags[USCXML_CTX_PRISTINE]  = true;
  INV_41D63_flags[USCXML_CTX_SPONTANEOUS] = true;

  run ROOT_step() priority 10;
}

ltl w3c { always !(ROOT_config[ROOT_FAIL]) }
