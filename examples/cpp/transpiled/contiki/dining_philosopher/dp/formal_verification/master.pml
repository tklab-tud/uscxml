/** generated from 
  file:///C:/Puneet/education/TU_Darmstadt/Theses/Dining_philospher/june20/dp/uscxml_browser/scxml/master.scxml
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
#define PHILOSOPHER1 2 /* index for invoker philosopher1 */
#define PHILOSOPHER2 3 /* index for invoker philosopher2 */
#define PHILOSOPHER3 4 /* index for invoker philosopher3 */
#define PHILOSOPHER4 5 /* index for invoker philosopher4 */
#define PHILOSOPHER5 6 /* index for invoker philosopher5 */
#define ROOT__NAME 14 /* ROOT__name */
#define ROOT__SESSIONID 13 /* ROOT__sessionid */
#define U152A04F7__NAME 27 /* U152A04F7__name */
#define U152A04F7__SESSIONID 26 /* U152A04F7__sessionid */
#define U579FA46E__NAME 36 /* U579FA46E__name */
#define U579FA46E__SESSIONID 35 /* U579FA46E__sessionid */
#define U58A2A14B__NAME 23 /* U58A2A14B__name */
#define U58A2A14B__SESSIONID 22 /* U58A2A14B__sessionid */
#define U66EEFC9F__NAME 30 /* U66EEFC9F__name */
#define U66EEFC9F__SESSIONID 29 /* U66EEFC9F__sessionid */
#define U6FC61343__NAME 33 /* U6FC61343__name */
#define U6FC61343__SESSIONID 32 /* U6FC61343__sessionid */
#define DONE_INVOKE 6 /* done.invoke */
#define DONE_INVOKE_PHILOSOPHER1 25 /* done.invoke.philosopher1 */
#define DONE_INVOKE_PHILOSOPHER2 28 /* done.invoke.philosopher2 */
#define DONE_INVOKE_PHILOSOPHER3 31 /* done.invoke.philosopher3 */
#define DONE_INVOKE_PHILOSOPHER4 34 /* done.invoke.philosopher4 */
#define DONE_INVOKE_PHILOSOPHER5 37 /* done.invoke.philosopher5 */
#define DONE_STATE_PHILOSOPHER1 8 /* done.state.philosopher1 */
#define DONE_STATE_PHILOSOPHER2 9 /* done.state.philosopher2 */
#define DONE_STATE_PHILOSOPHER3 10 /* done.state.philosopher3 */
#define DONE_STATE_PHILOSOPHER4 11 /* done.state.philosopher4 */
#define DONE_STATE_PHILOSOPHER5 12 /* done.state.philosopher5 */
#define DONE_STATE_PHILOSOPHER_ROUTINE 21 /* done.state.philosopher_routine */
#define DONE_STATE_S0 7 /* done.state.s0 */
#define EATING_OVER 20 /* eating_over */
#define FAIL 15 /* fail */
#define NEED_LEFT_FORK 1 /* need_left_fork */
#define NEED_RIGHT_FORK 3 /* need_right_fork */
#define RESEND_NEED_LEFT_FORK 19 /* resend_need_left_fork */
#define RESEND_NEED_RIGHT_FORK 18 /* resend_need_right_fork */
#define RETURN_FORKS 5 /* return_forks */
#define STARVATION_TIMER 24 /* starvation_timer */
#define TAKE_LEFT_FORK 2 /* take_left_fork */
#define TAKE_RIGHT_FORK 4 /* take_right_fork */
#define THINKING_OVER 16 /* thinking_over */
#define TIMEOUT 17 /* timeout */

/** is there a common bit in t1 and t2 */
#define ROOT_TRANS_HAS_AND(a, b) \
(false \
 || a[0] & b[0] \
 || a[1] & b[1] \
 || a[2] & b[2] \
 || a[3] & b[3] \
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
 || a[3] \
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
a[3] = a[3] | mask[3]; \

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
a[3] = false; \

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
a[3] = b[3]; \

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
a[3] = a[3] & mask[3]; \

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
a[3] = a[3] & !mask[3]; \

#define ROOT_STATES_AND_NOT(a, mask) \
a[0] = a[0] & !mask[0]; \
a[1] = a[1] & !mask[1]; \
a[2] = a[2] & !mask[2]; \
a[3] = a[3] & !mask[3]; \


/* custom type definitions for ROOT_ */

/** is there a common bit in t1 and t2 */
#define PHILOSOPHER1_TRANS_HAS_AND(a, b) \
(false \
 || a[0] & b[0] \
 || a[1] & b[1] \
 || a[2] & b[2] \
 || a[3] & b[3] \
 || a[4] & b[4] \
 || a[5] & b[5] \
 || a[6] & b[6] \
 || a[7] & b[7] \
 || a[8] & b[8] \
 || a[9] & b[9] \
 || a[10] & b[10] \
)

#define PHILOSOPHER1_STATES_HAS_AND(a, b) \
(false \
 || a[0] & b[0] \
 || a[1] & b[1] \
 || a[2] & b[2] \
 || a[3] & b[3] \
 || a[4] & b[4] \
 || a[5] & b[5] \
 || a[6] & b[6] \
 || a[7] & b[7] \
)


/** is there bit set in a */
#define PHILOSOPHER1_TRANS_HAS_ANY(a) \
(false \
 || a[0] \
 || a[1] \
 || a[2] \
 || a[3] \
 || a[4] \
 || a[5] \
 || a[6] \
 || a[7] \
 || a[8] \
 || a[9] \
 || a[10] \
)

#define PHILOSOPHER1_STATES_HAS_ANY(a) \
(false \
 || a[0] \
 || a[1] \
 || a[2] \
 || a[3] \
 || a[4] \
 || a[5] \
 || a[6] \
 || a[7] \
)


/** or'ing bits in a with mask */
#define PHILOSOPHER1_TRANS_OR(a, mask) \
a[0] = a[0] | mask[0]; \
a[1] = a[1] | mask[1]; \
a[2] = a[2] | mask[2]; \
a[3] = a[3] | mask[3]; \
a[4] = a[4] | mask[4]; \
a[5] = a[5] | mask[5]; \
a[6] = a[6] | mask[6]; \
a[7] = a[7] | mask[7]; \
a[8] = a[8] | mask[8]; \
a[9] = a[9] | mask[9]; \
a[10] = a[10] | mask[10]; \

#define PHILOSOPHER1_STATES_OR(a, mask) \
a[0] = a[0] | mask[0]; \
a[1] = a[1] | mask[1]; \
a[2] = a[2] | mask[2]; \
a[3] = a[3] | mask[3]; \
a[4] = a[4] | mask[4]; \
a[5] = a[5] | mask[5]; \
a[6] = a[6] | mask[6]; \
a[7] = a[7] | mask[7]; \


/** clearing all bits of a */
#define PHILOSOPHER1_TRANS_CLEAR(a) \
a[0] = false; \
a[1] = false; \
a[2] = false; \
a[3] = false; \
a[4] = false; \
a[5] = false; \
a[6] = false; \
a[7] = false; \
a[8] = false; \
a[9] = false; \
a[10] = false; \

#define PHILOSOPHER1_STATES_CLEAR(a) \
a[0] = false; \
a[1] = false; \
a[2] = false; \
a[3] = false; \
a[4] = false; \
a[5] = false; \
a[6] = false; \
a[7] = false; \


/** copy bits from a to b */
#define PHILOSOPHER1_TRANS_COPY(a, b) \
a[0] = b[0]; \
a[1] = b[1]; \
a[2] = b[2]; \
a[3] = b[3]; \
a[4] = b[4]; \
a[5] = b[5]; \
a[6] = b[6]; \
a[7] = b[7]; \
a[8] = b[8]; \
a[9] = b[9]; \
a[10] = b[10]; \

#define PHILOSOPHER1_STATES_COPY(a, b) \
a[0] = b[0]; \
a[1] = b[1]; \
a[2] = b[2]; \
a[3] = b[3]; \
a[4] = b[4]; \
a[5] = b[5]; \
a[6] = b[6]; \
a[7] = b[7]; \


/** and'ing bits in a with mask */
#define PHILOSOPHER1_TRANS_AND(a, mask) \
a[0] = a[0] & mask[0]; \
a[1] = a[1] & mask[1]; \
a[2] = a[2] & mask[2]; \
a[3] = a[3] & mask[3]; \
a[4] = a[4] & mask[4]; \
a[5] = a[5] & mask[5]; \
a[6] = a[6] & mask[6]; \
a[7] = a[7] & mask[7]; \
a[8] = a[8] & mask[8]; \
a[9] = a[9] & mask[9]; \
a[10] = a[10] & mask[10]; \

#define PHILOSOPHER1_STATES_AND(a, mask) \
a[0] = a[0] & mask[0]; \
a[1] = a[1] & mask[1]; \
a[2] = a[2] & mask[2]; \
a[3] = a[3] & mask[3]; \
a[4] = a[4] & mask[4]; \
a[5] = a[5] & mask[5]; \
a[6] = a[6] & mask[6]; \
a[7] = a[7] & mask[7]; \


/** not and'ing bits in a with mask */
#define PHILOSOPHER1_TRANS_AND_NOT(a, mask) \
a[0] = a[0] & !mask[0]; \
a[1] = a[1] & !mask[1]; \
a[2] = a[2] & !mask[2]; \
a[3] = a[3] & !mask[3]; \
a[4] = a[4] & !mask[4]; \
a[5] = a[5] & !mask[5]; \
a[6] = a[6] & !mask[6]; \
a[7] = a[7] & !mask[7]; \
a[8] = a[8] & !mask[8]; \
a[9] = a[9] & !mask[9]; \
a[10] = a[10] & !mask[10]; \

#define PHILOSOPHER1_STATES_AND_NOT(a, mask) \
a[0] = a[0] & !mask[0]; \
a[1] = a[1] & !mask[1]; \
a[2] = a[2] & !mask[2]; \
a[3] = a[3] & !mask[3]; \
a[4] = a[4] & !mask[4]; \
a[5] = a[5] & !mask[5]; \
a[6] = a[6] & !mask[6]; \
a[7] = a[7] & !mask[7]; \


/* custom type definitions for ROOT_ */

/** is there a common bit in t1 and t2 */
#define PHILOSOPHER2_TRANS_HAS_AND(a, b) \
(false \
 || a[0] & b[0] \
 || a[1] & b[1] \
 || a[2] & b[2] \
 || a[3] & b[3] \
 || a[4] & b[4] \
 || a[5] & b[5] \
 || a[6] & b[6] \
 || a[7] & b[7] \
 || a[8] & b[8] \
 || a[9] & b[9] \
 || a[10] & b[10] \
)

#define PHILOSOPHER2_STATES_HAS_AND(a, b) \
(false \
 || a[0] & b[0] \
 || a[1] & b[1] \
 || a[2] & b[2] \
 || a[3] & b[3] \
 || a[4] & b[4] \
 || a[5] & b[5] \
 || a[6] & b[6] \
 || a[7] & b[7] \
)


/** is there bit set in a */
#define PHILOSOPHER2_TRANS_HAS_ANY(a) \
(false \
 || a[0] \
 || a[1] \
 || a[2] \
 || a[3] \
 || a[4] \
 || a[5] \
 || a[6] \
 || a[7] \
 || a[8] \
 || a[9] \
 || a[10] \
)

#define PHILOSOPHER2_STATES_HAS_ANY(a) \
(false \
 || a[0] \
 || a[1] \
 || a[2] \
 || a[3] \
 || a[4] \
 || a[5] \
 || a[6] \
 || a[7] \
)


/** or'ing bits in a with mask */
#define PHILOSOPHER2_TRANS_OR(a, mask) \
a[0] = a[0] | mask[0]; \
a[1] = a[1] | mask[1]; \
a[2] = a[2] | mask[2]; \
a[3] = a[3] | mask[3]; \
a[4] = a[4] | mask[4]; \
a[5] = a[5] | mask[5]; \
a[6] = a[6] | mask[6]; \
a[7] = a[7] | mask[7]; \
a[8] = a[8] | mask[8]; \
a[9] = a[9] | mask[9]; \
a[10] = a[10] | mask[10]; \

#define PHILOSOPHER2_STATES_OR(a, mask) \
a[0] = a[0] | mask[0]; \
a[1] = a[1] | mask[1]; \
a[2] = a[2] | mask[2]; \
a[3] = a[3] | mask[3]; \
a[4] = a[4] | mask[4]; \
a[5] = a[5] | mask[5]; \
a[6] = a[6] | mask[6]; \
a[7] = a[7] | mask[7]; \


/** clearing all bits of a */
#define PHILOSOPHER2_TRANS_CLEAR(a) \
a[0] = false; \
a[1] = false; \
a[2] = false; \
a[3] = false; \
a[4] = false; \
a[5] = false; \
a[6] = false; \
a[7] = false; \
a[8] = false; \
a[9] = false; \
a[10] = false; \

#define PHILOSOPHER2_STATES_CLEAR(a) \
a[0] = false; \
a[1] = false; \
a[2] = false; \
a[3] = false; \
a[4] = false; \
a[5] = false; \
a[6] = false; \
a[7] = false; \


/** copy bits from a to b */
#define PHILOSOPHER2_TRANS_COPY(a, b) \
a[0] = b[0]; \
a[1] = b[1]; \
a[2] = b[2]; \
a[3] = b[3]; \
a[4] = b[4]; \
a[5] = b[5]; \
a[6] = b[6]; \
a[7] = b[7]; \
a[8] = b[8]; \
a[9] = b[9]; \
a[10] = b[10]; \

#define PHILOSOPHER2_STATES_COPY(a, b) \
a[0] = b[0]; \
a[1] = b[1]; \
a[2] = b[2]; \
a[3] = b[3]; \
a[4] = b[4]; \
a[5] = b[5]; \
a[6] = b[6]; \
a[7] = b[7]; \


/** and'ing bits in a with mask */
#define PHILOSOPHER2_TRANS_AND(a, mask) \
a[0] = a[0] & mask[0]; \
a[1] = a[1] & mask[1]; \
a[2] = a[2] & mask[2]; \
a[3] = a[3] & mask[3]; \
a[4] = a[4] & mask[4]; \
a[5] = a[5] & mask[5]; \
a[6] = a[6] & mask[6]; \
a[7] = a[7] & mask[7]; \
a[8] = a[8] & mask[8]; \
a[9] = a[9] & mask[9]; \
a[10] = a[10] & mask[10]; \

#define PHILOSOPHER2_STATES_AND(a, mask) \
a[0] = a[0] & mask[0]; \
a[1] = a[1] & mask[1]; \
a[2] = a[2] & mask[2]; \
a[3] = a[3] & mask[3]; \
a[4] = a[4] & mask[4]; \
a[5] = a[5] & mask[5]; \
a[6] = a[6] & mask[6]; \
a[7] = a[7] & mask[7]; \


/** not and'ing bits in a with mask */
#define PHILOSOPHER2_TRANS_AND_NOT(a, mask) \
a[0] = a[0] & !mask[0]; \
a[1] = a[1] & !mask[1]; \
a[2] = a[2] & !mask[2]; \
a[3] = a[3] & !mask[3]; \
a[4] = a[4] & !mask[4]; \
a[5] = a[5] & !mask[5]; \
a[6] = a[6] & !mask[6]; \
a[7] = a[7] & !mask[7]; \
a[8] = a[8] & !mask[8]; \
a[9] = a[9] & !mask[9]; \
a[10] = a[10] & !mask[10]; \

#define PHILOSOPHER2_STATES_AND_NOT(a, mask) \
a[0] = a[0] & !mask[0]; \
a[1] = a[1] & !mask[1]; \
a[2] = a[2] & !mask[2]; \
a[3] = a[3] & !mask[3]; \
a[4] = a[4] & !mask[4]; \
a[5] = a[5] & !mask[5]; \
a[6] = a[6] & !mask[6]; \
a[7] = a[7] & !mask[7]; \


/* custom type definitions for ROOT_ */

/** is there a common bit in t1 and t2 */
#define PHILOSOPHER3_TRANS_HAS_AND(a, b) \
(false \
 || a[0] & b[0] \
 || a[1] & b[1] \
 || a[2] & b[2] \
 || a[3] & b[3] \
 || a[4] & b[4] \
 || a[5] & b[5] \
 || a[6] & b[6] \
 || a[7] & b[7] \
 || a[8] & b[8] \
 || a[9] & b[9] \
 || a[10] & b[10] \
)

#define PHILOSOPHER3_STATES_HAS_AND(a, b) \
(false \
 || a[0] & b[0] \
 || a[1] & b[1] \
 || a[2] & b[2] \
 || a[3] & b[3] \
 || a[4] & b[4] \
 || a[5] & b[5] \
 || a[6] & b[6] \
 || a[7] & b[7] \
)


/** is there bit set in a */
#define PHILOSOPHER3_TRANS_HAS_ANY(a) \
(false \
 || a[0] \
 || a[1] \
 || a[2] \
 || a[3] \
 || a[4] \
 || a[5] \
 || a[6] \
 || a[7] \
 || a[8] \
 || a[9] \
 || a[10] \
)

#define PHILOSOPHER3_STATES_HAS_ANY(a) \
(false \
 || a[0] \
 || a[1] \
 || a[2] \
 || a[3] \
 || a[4] \
 || a[5] \
 || a[6] \
 || a[7] \
)


/** or'ing bits in a with mask */
#define PHILOSOPHER3_TRANS_OR(a, mask) \
a[0] = a[0] | mask[0]; \
a[1] = a[1] | mask[1]; \
a[2] = a[2] | mask[2]; \
a[3] = a[3] | mask[3]; \
a[4] = a[4] | mask[4]; \
a[5] = a[5] | mask[5]; \
a[6] = a[6] | mask[6]; \
a[7] = a[7] | mask[7]; \
a[8] = a[8] | mask[8]; \
a[9] = a[9] | mask[9]; \
a[10] = a[10] | mask[10]; \

#define PHILOSOPHER3_STATES_OR(a, mask) \
a[0] = a[0] | mask[0]; \
a[1] = a[1] | mask[1]; \
a[2] = a[2] | mask[2]; \
a[3] = a[3] | mask[3]; \
a[4] = a[4] | mask[4]; \
a[5] = a[5] | mask[5]; \
a[6] = a[6] | mask[6]; \
a[7] = a[7] | mask[7]; \


/** clearing all bits of a */
#define PHILOSOPHER3_TRANS_CLEAR(a) \
a[0] = false; \
a[1] = false; \
a[2] = false; \
a[3] = false; \
a[4] = false; \
a[5] = false; \
a[6] = false; \
a[7] = false; \
a[8] = false; \
a[9] = false; \
a[10] = false; \

#define PHILOSOPHER3_STATES_CLEAR(a) \
a[0] = false; \
a[1] = false; \
a[2] = false; \
a[3] = false; \
a[4] = false; \
a[5] = false; \
a[6] = false; \
a[7] = false; \


/** copy bits from a to b */
#define PHILOSOPHER3_TRANS_COPY(a, b) \
a[0] = b[0]; \
a[1] = b[1]; \
a[2] = b[2]; \
a[3] = b[3]; \
a[4] = b[4]; \
a[5] = b[5]; \
a[6] = b[6]; \
a[7] = b[7]; \
a[8] = b[8]; \
a[9] = b[9]; \
a[10] = b[10]; \

#define PHILOSOPHER3_STATES_COPY(a, b) \
a[0] = b[0]; \
a[1] = b[1]; \
a[2] = b[2]; \
a[3] = b[3]; \
a[4] = b[4]; \
a[5] = b[5]; \
a[6] = b[6]; \
a[7] = b[7]; \


/** and'ing bits in a with mask */
#define PHILOSOPHER3_TRANS_AND(a, mask) \
a[0] = a[0] & mask[0]; \
a[1] = a[1] & mask[1]; \
a[2] = a[2] & mask[2]; \
a[3] = a[3] & mask[3]; \
a[4] = a[4] & mask[4]; \
a[5] = a[5] & mask[5]; \
a[6] = a[6] & mask[6]; \
a[7] = a[7] & mask[7]; \
a[8] = a[8] & mask[8]; \
a[9] = a[9] & mask[9]; \
a[10] = a[10] & mask[10]; \

#define PHILOSOPHER3_STATES_AND(a, mask) \
a[0] = a[0] & mask[0]; \
a[1] = a[1] & mask[1]; \
a[2] = a[2] & mask[2]; \
a[3] = a[3] & mask[3]; \
a[4] = a[4] & mask[4]; \
a[5] = a[5] & mask[5]; \
a[6] = a[6] & mask[6]; \
a[7] = a[7] & mask[7]; \


/** not and'ing bits in a with mask */
#define PHILOSOPHER3_TRANS_AND_NOT(a, mask) \
a[0] = a[0] & !mask[0]; \
a[1] = a[1] & !mask[1]; \
a[2] = a[2] & !mask[2]; \
a[3] = a[3] & !mask[3]; \
a[4] = a[4] & !mask[4]; \
a[5] = a[5] & !mask[5]; \
a[6] = a[6] & !mask[6]; \
a[7] = a[7] & !mask[7]; \
a[8] = a[8] & !mask[8]; \
a[9] = a[9] & !mask[9]; \
a[10] = a[10] & !mask[10]; \

#define PHILOSOPHER3_STATES_AND_NOT(a, mask) \
a[0] = a[0] & !mask[0]; \
a[1] = a[1] & !mask[1]; \
a[2] = a[2] & !mask[2]; \
a[3] = a[3] & !mask[3]; \
a[4] = a[4] & !mask[4]; \
a[5] = a[5] & !mask[5]; \
a[6] = a[6] & !mask[6]; \
a[7] = a[7] & !mask[7]; \


/* custom type definitions for ROOT_ */

/** is there a common bit in t1 and t2 */
#define PHILOSOPHER4_TRANS_HAS_AND(a, b) \
(false \
 || a[0] & b[0] \
 || a[1] & b[1] \
 || a[2] & b[2] \
 || a[3] & b[3] \
 || a[4] & b[4] \
 || a[5] & b[5] \
 || a[6] & b[6] \
 || a[7] & b[7] \
 || a[8] & b[8] \
 || a[9] & b[9] \
 || a[10] & b[10] \
)

#define PHILOSOPHER4_STATES_HAS_AND(a, b) \
(false \
 || a[0] & b[0] \
 || a[1] & b[1] \
 || a[2] & b[2] \
 || a[3] & b[3] \
 || a[4] & b[4] \
 || a[5] & b[5] \
 || a[6] & b[6] \
 || a[7] & b[7] \
)


/** is there bit set in a */
#define PHILOSOPHER4_TRANS_HAS_ANY(a) \
(false \
 || a[0] \
 || a[1] \
 || a[2] \
 || a[3] \
 || a[4] \
 || a[5] \
 || a[6] \
 || a[7] \
 || a[8] \
 || a[9] \
 || a[10] \
)

#define PHILOSOPHER4_STATES_HAS_ANY(a) \
(false \
 || a[0] \
 || a[1] \
 || a[2] \
 || a[3] \
 || a[4] \
 || a[5] \
 || a[6] \
 || a[7] \
)


/** or'ing bits in a with mask */
#define PHILOSOPHER4_TRANS_OR(a, mask) \
a[0] = a[0] | mask[0]; \
a[1] = a[1] | mask[1]; \
a[2] = a[2] | mask[2]; \
a[3] = a[3] | mask[3]; \
a[4] = a[4] | mask[4]; \
a[5] = a[5] | mask[5]; \
a[6] = a[6] | mask[6]; \
a[7] = a[7] | mask[7]; \
a[8] = a[8] | mask[8]; \
a[9] = a[9] | mask[9]; \
a[10] = a[10] | mask[10]; \

#define PHILOSOPHER4_STATES_OR(a, mask) \
a[0] = a[0] | mask[0]; \
a[1] = a[1] | mask[1]; \
a[2] = a[2] | mask[2]; \
a[3] = a[3] | mask[3]; \
a[4] = a[4] | mask[4]; \
a[5] = a[5] | mask[5]; \
a[6] = a[6] | mask[6]; \
a[7] = a[7] | mask[7]; \


/** clearing all bits of a */
#define PHILOSOPHER4_TRANS_CLEAR(a) \
a[0] = false; \
a[1] = false; \
a[2] = false; \
a[3] = false; \
a[4] = false; \
a[5] = false; \
a[6] = false; \
a[7] = false; \
a[8] = false; \
a[9] = false; \
a[10] = false; \

#define PHILOSOPHER4_STATES_CLEAR(a) \
a[0] = false; \
a[1] = false; \
a[2] = false; \
a[3] = false; \
a[4] = false; \
a[5] = false; \
a[6] = false; \
a[7] = false; \


/** copy bits from a to b */
#define PHILOSOPHER4_TRANS_COPY(a, b) \
a[0] = b[0]; \
a[1] = b[1]; \
a[2] = b[2]; \
a[3] = b[3]; \
a[4] = b[4]; \
a[5] = b[5]; \
a[6] = b[6]; \
a[7] = b[7]; \
a[8] = b[8]; \
a[9] = b[9]; \
a[10] = b[10]; \

#define PHILOSOPHER4_STATES_COPY(a, b) \
a[0] = b[0]; \
a[1] = b[1]; \
a[2] = b[2]; \
a[3] = b[3]; \
a[4] = b[4]; \
a[5] = b[5]; \
a[6] = b[6]; \
a[7] = b[7]; \


/** and'ing bits in a with mask */
#define PHILOSOPHER4_TRANS_AND(a, mask) \
a[0] = a[0] & mask[0]; \
a[1] = a[1] & mask[1]; \
a[2] = a[2] & mask[2]; \
a[3] = a[3] & mask[3]; \
a[4] = a[4] & mask[4]; \
a[5] = a[5] & mask[5]; \
a[6] = a[6] & mask[6]; \
a[7] = a[7] & mask[7]; \
a[8] = a[8] & mask[8]; \
a[9] = a[9] & mask[9]; \
a[10] = a[10] & mask[10]; \

#define PHILOSOPHER4_STATES_AND(a, mask) \
a[0] = a[0] & mask[0]; \
a[1] = a[1] & mask[1]; \
a[2] = a[2] & mask[2]; \
a[3] = a[3] & mask[3]; \
a[4] = a[4] & mask[4]; \
a[5] = a[5] & mask[5]; \
a[6] = a[6] & mask[6]; \
a[7] = a[7] & mask[7]; \


/** not and'ing bits in a with mask */
#define PHILOSOPHER4_TRANS_AND_NOT(a, mask) \
a[0] = a[0] & !mask[0]; \
a[1] = a[1] & !mask[1]; \
a[2] = a[2] & !mask[2]; \
a[3] = a[3] & !mask[3]; \
a[4] = a[4] & !mask[4]; \
a[5] = a[5] & !mask[5]; \
a[6] = a[6] & !mask[6]; \
a[7] = a[7] & !mask[7]; \
a[8] = a[8] & !mask[8]; \
a[9] = a[9] & !mask[9]; \
a[10] = a[10] & !mask[10]; \

#define PHILOSOPHER4_STATES_AND_NOT(a, mask) \
a[0] = a[0] & !mask[0]; \
a[1] = a[1] & !mask[1]; \
a[2] = a[2] & !mask[2]; \
a[3] = a[3] & !mask[3]; \
a[4] = a[4] & !mask[4]; \
a[5] = a[5] & !mask[5]; \
a[6] = a[6] & !mask[6]; \
a[7] = a[7] & !mask[7]; \


/* custom type definitions for ROOT_ */

/** is there a common bit in t1 and t2 */
#define PHILOSOPHER5_TRANS_HAS_AND(a, b) \
(false \
 || a[0] & b[0] \
 || a[1] & b[1] \
 || a[2] & b[2] \
 || a[3] & b[3] \
 || a[4] & b[4] \
 || a[5] & b[5] \
 || a[6] & b[6] \
 || a[7] & b[7] \
 || a[8] & b[8] \
 || a[9] & b[9] \
 || a[10] & b[10] \
)

#define PHILOSOPHER5_STATES_HAS_AND(a, b) \
(false \
 || a[0] & b[0] \
 || a[1] & b[1] \
 || a[2] & b[2] \
 || a[3] & b[3] \
 || a[4] & b[4] \
 || a[5] & b[5] \
 || a[6] & b[6] \
 || a[7] & b[7] \
)


/** is there bit set in a */
#define PHILOSOPHER5_TRANS_HAS_ANY(a) \
(false \
 || a[0] \
 || a[1] \
 || a[2] \
 || a[3] \
 || a[4] \
 || a[5] \
 || a[6] \
 || a[7] \
 || a[8] \
 || a[9] \
 || a[10] \
)

#define PHILOSOPHER5_STATES_HAS_ANY(a) \
(false \
 || a[0] \
 || a[1] \
 || a[2] \
 || a[3] \
 || a[4] \
 || a[5] \
 || a[6] \
 || a[7] \
)


/** or'ing bits in a with mask */
#define PHILOSOPHER5_TRANS_OR(a, mask) \
a[0] = a[0] | mask[0]; \
a[1] = a[1] | mask[1]; \
a[2] = a[2] | mask[2]; \
a[3] = a[3] | mask[3]; \
a[4] = a[4] | mask[4]; \
a[5] = a[5] | mask[5]; \
a[6] = a[6] | mask[6]; \
a[7] = a[7] | mask[7]; \
a[8] = a[8] | mask[8]; \
a[9] = a[9] | mask[9]; \
a[10] = a[10] | mask[10]; \

#define PHILOSOPHER5_STATES_OR(a, mask) \
a[0] = a[0] | mask[0]; \
a[1] = a[1] | mask[1]; \
a[2] = a[2] | mask[2]; \
a[3] = a[3] | mask[3]; \
a[4] = a[4] | mask[4]; \
a[5] = a[5] | mask[5]; \
a[6] = a[6] | mask[6]; \
a[7] = a[7] | mask[7]; \


/** clearing all bits of a */
#define PHILOSOPHER5_TRANS_CLEAR(a) \
a[0] = false; \
a[1] = false; \
a[2] = false; \
a[3] = false; \
a[4] = false; \
a[5] = false; \
a[6] = false; \
a[7] = false; \
a[8] = false; \
a[9] = false; \
a[10] = false; \

#define PHILOSOPHER5_STATES_CLEAR(a) \
a[0] = false; \
a[1] = false; \
a[2] = false; \
a[3] = false; \
a[4] = false; \
a[5] = false; \
a[6] = false; \
a[7] = false; \


/** copy bits from a to b */
#define PHILOSOPHER5_TRANS_COPY(a, b) \
a[0] = b[0]; \
a[1] = b[1]; \
a[2] = b[2]; \
a[3] = b[3]; \
a[4] = b[4]; \
a[5] = b[5]; \
a[6] = b[6]; \
a[7] = b[7]; \
a[8] = b[8]; \
a[9] = b[9]; \
a[10] = b[10]; \

#define PHILOSOPHER5_STATES_COPY(a, b) \
a[0] = b[0]; \
a[1] = b[1]; \
a[2] = b[2]; \
a[3] = b[3]; \
a[4] = b[4]; \
a[5] = b[5]; \
a[6] = b[6]; \
a[7] = b[7]; \


/** and'ing bits in a with mask */
#define PHILOSOPHER5_TRANS_AND(a, mask) \
a[0] = a[0] & mask[0]; \
a[1] = a[1] & mask[1]; \
a[2] = a[2] & mask[2]; \
a[3] = a[3] & mask[3]; \
a[4] = a[4] & mask[4]; \
a[5] = a[5] & mask[5]; \
a[6] = a[6] & mask[6]; \
a[7] = a[7] & mask[7]; \
a[8] = a[8] & mask[8]; \
a[9] = a[9] & mask[9]; \
a[10] = a[10] & mask[10]; \

#define PHILOSOPHER5_STATES_AND(a, mask) \
a[0] = a[0] & mask[0]; \
a[1] = a[1] & mask[1]; \
a[2] = a[2] & mask[2]; \
a[3] = a[3] & mask[3]; \
a[4] = a[4] & mask[4]; \
a[5] = a[5] & mask[5]; \
a[6] = a[6] & mask[6]; \
a[7] = a[7] & mask[7]; \


/** not and'ing bits in a with mask */
#define PHILOSOPHER5_TRANS_AND_NOT(a, mask) \
a[0] = a[0] & !mask[0]; \
a[1] = a[1] & !mask[1]; \
a[2] = a[2] & !mask[2]; \
a[3] = a[3] & !mask[3]; \
a[4] = a[4] & !mask[4]; \
a[5] = a[5] & !mask[5]; \
a[6] = a[6] & !mask[6]; \
a[7] = a[7] & !mask[7]; \
a[8] = a[8] & !mask[8]; \
a[9] = a[9] & !mask[9]; \
a[10] = a[10] & !mask[10]; \

#define PHILOSOPHER5_STATES_AND_NOT(a, mask) \
a[0] = a[0] & !mask[0]; \
a[1] = a[1] & !mask[1]; \
a[2] = a[2] & !mask[2]; \
a[3] = a[3] & !mask[3]; \
a[4] = a[4] & !mask[4]; \
a[5] = a[5] & !mask[5]; \
a[6] = a[6] & !mask[6]; \
a[7] = a[7] & !mask[7]; \


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
  bool conflicts[4];
  bool exit_set[4];
}
hidden ROOT_transition_t ROOT_transitions[4];

typedef ROOT_state_t {
  unsigned parent : 2;
  bool children[4];
  bool completion[4];
  bool ancestors[4];
  bool type[8];
}
hidden ROOT_state_t ROOT_states[4];

typedef ROOT_ctx_t {
  bool conflicts[4];
  bool trans_set[4];
  bool target_set[4];
  bool exit_set[4];
  bool entry_set[4];
  bool tmp_states[4];
}
hidden ROOT_ctx_t ROOT_ctx;


int ROOT_forks[5];
int ROOT_NUM_OF_PHIL;
int ROOT_current_phil;
int ROOT_left_fork;
int ROOT_right_fork;
int ROOT_seed;
hidden int ROOT_procid;             /* the process id running this machine */

/* custom definitions and global variables */
bool PHILOSOPHER1_flags[6];
bool PHILOSOPHER1_config[8];
bool PHILOSOPHER1_history[8];
bool PHILOSOPHER1_invocations[8];
hidden _event_t PHILOSOPHER1__event;               /* current event */
hidden _event_t PHILOSOPHER1__tmpE;          /* temporary event for send */
chan PHILOSOPHER1_iQ   = [7] of {_event_t}  /* internal queue */
chan PHILOSOPHER1_eQ   = [13] of {_event_t}  /* external queue */

typedef PHILOSOPHER1_transition_t {
  unsigned source : 3;
  bool target[8];
  bool type[5];
  bool conflicts[11];
  bool exit_set[8];
}
hidden PHILOSOPHER1_transition_t PHILOSOPHER1_transitions[11];

typedef PHILOSOPHER1_state_t {
  unsigned parent : 3;
  bool children[8];
  bool completion[8];
  bool ancestors[8];
  bool type[8];
}
hidden PHILOSOPHER1_state_t PHILOSOPHER1_states[8];

typedef PHILOSOPHER1_ctx_t {
  bool conflicts[11];
  bool trans_set[11];
  bool target_set[8];
  bool exit_set[8];
  bool entry_set[8];
  bool tmp_states[8];
}
hidden PHILOSOPHER1_ctx_t PHILOSOPHER1_ctx;


int PHILOSOPHER1_p_id;
int PHILOSOPHER1_delay;
int PHILOSOPHER1_random_delay;
hidden int PHILOSOPHER1_procid;             /* the process id running this machine */

/* custom definitions and global variables */
bool PHILOSOPHER2_flags[6];
bool PHILOSOPHER2_config[8];
bool PHILOSOPHER2_history[8];
bool PHILOSOPHER2_invocations[8];
hidden _event_t PHILOSOPHER2__event;               /* current event */
hidden _event_t PHILOSOPHER2__tmpE;          /* temporary event for send */
chan PHILOSOPHER2_iQ   = [7] of {_event_t}  /* internal queue */
chan PHILOSOPHER2_eQ   = [13] of {_event_t}  /* external queue */

typedef PHILOSOPHER2_transition_t {
  unsigned source : 3;
  bool target[8];
  bool type[5];
  bool conflicts[11];
  bool exit_set[8];
}
hidden PHILOSOPHER2_transition_t PHILOSOPHER2_transitions[11];

typedef PHILOSOPHER2_state_t {
  unsigned parent : 3;
  bool children[8];
  bool completion[8];
  bool ancestors[8];
  bool type[8];
}
hidden PHILOSOPHER2_state_t PHILOSOPHER2_states[8];

typedef PHILOSOPHER2_ctx_t {
  bool conflicts[11];
  bool trans_set[11];
  bool target_set[8];
  bool exit_set[8];
  bool entry_set[8];
  bool tmp_states[8];
}
hidden PHILOSOPHER2_ctx_t PHILOSOPHER2_ctx;


int PHILOSOPHER2_p_id;
int PHILOSOPHER2_delay;
int PHILOSOPHER2_random_delay;
hidden int PHILOSOPHER2_procid;             /* the process id running this machine */

/* custom definitions and global variables */
bool PHILOSOPHER3_flags[6];
bool PHILOSOPHER3_config[8];
bool PHILOSOPHER3_history[8];
bool PHILOSOPHER3_invocations[8];
hidden _event_t PHILOSOPHER3__event;               /* current event */
hidden _event_t PHILOSOPHER3__tmpE;          /* temporary event for send */
chan PHILOSOPHER3_iQ   = [7] of {_event_t}  /* internal queue */
chan PHILOSOPHER3_eQ   = [13] of {_event_t}  /* external queue */

typedef PHILOSOPHER3_transition_t {
  unsigned source : 3;
  bool target[8];
  bool type[5];
  bool conflicts[11];
  bool exit_set[8];
}
hidden PHILOSOPHER3_transition_t PHILOSOPHER3_transitions[11];

typedef PHILOSOPHER3_state_t {
  unsigned parent : 3;
  bool children[8];
  bool completion[8];
  bool ancestors[8];
  bool type[8];
}
hidden PHILOSOPHER3_state_t PHILOSOPHER3_states[8];

typedef PHILOSOPHER3_ctx_t {
  bool conflicts[11];
  bool trans_set[11];
  bool target_set[8];
  bool exit_set[8];
  bool entry_set[8];
  bool tmp_states[8];
}
hidden PHILOSOPHER3_ctx_t PHILOSOPHER3_ctx;


int PHILOSOPHER3_p_id;
int PHILOSOPHER3_delay;
int PHILOSOPHER3_random_delay;
hidden int PHILOSOPHER3_procid;             /* the process id running this machine */

/* custom definitions and global variables */
bool PHILOSOPHER4_flags[6];
bool PHILOSOPHER4_config[8];
bool PHILOSOPHER4_history[8];
bool PHILOSOPHER4_invocations[8];
hidden _event_t PHILOSOPHER4__event;               /* current event */
hidden _event_t PHILOSOPHER4__tmpE;          /* temporary event for send */
chan PHILOSOPHER4_iQ   = [7] of {_event_t}  /* internal queue */
chan PHILOSOPHER4_eQ   = [13] of {_event_t}  /* external queue */

typedef PHILOSOPHER4_transition_t {
  unsigned source : 3;
  bool target[8];
  bool type[5];
  bool conflicts[11];
  bool exit_set[8];
}
hidden PHILOSOPHER4_transition_t PHILOSOPHER4_transitions[11];

typedef PHILOSOPHER4_state_t {
  unsigned parent : 3;
  bool children[8];
  bool completion[8];
  bool ancestors[8];
  bool type[8];
}
hidden PHILOSOPHER4_state_t PHILOSOPHER4_states[8];

typedef PHILOSOPHER4_ctx_t {
  bool conflicts[11];
  bool trans_set[11];
  bool target_set[8];
  bool exit_set[8];
  bool entry_set[8];
  bool tmp_states[8];
}
hidden PHILOSOPHER4_ctx_t PHILOSOPHER4_ctx;


int PHILOSOPHER4_p_id;
int PHILOSOPHER4_delay;
int PHILOSOPHER4_random_delay;
hidden int PHILOSOPHER4_procid;             /* the process id running this machine */

/* custom definitions and global variables */
bool PHILOSOPHER5_flags[6];
bool PHILOSOPHER5_config[8];
bool PHILOSOPHER5_history[8];
bool PHILOSOPHER5_invocations[8];
hidden _event_t PHILOSOPHER5__event;               /* current event */
hidden _event_t PHILOSOPHER5__tmpE;          /* temporary event for send */
chan PHILOSOPHER5_iQ   = [7] of {_event_t}  /* internal queue */
chan PHILOSOPHER5_eQ   = [13] of {_event_t}  /* external queue */

typedef PHILOSOPHER5_transition_t {
  unsigned source : 3;
  bool target[8];
  bool type[5];
  bool conflicts[11];
  bool exit_set[8];
}
hidden PHILOSOPHER5_transition_t PHILOSOPHER5_transitions[11];

typedef PHILOSOPHER5_state_t {
  unsigned parent : 3;
  bool children[8];
  bool completion[8];
  bool ancestors[8];
  bool type[8];
}
hidden PHILOSOPHER5_state_t PHILOSOPHER5_states[8];

typedef PHILOSOPHER5_ctx_t {
  bool conflicts[11];
  bool trans_set[11];
  bool target_set[8];
  bool exit_set[8];
  bool entry_set[8];
  bool tmp_states[8];
}
hidden PHILOSOPHER5_ctx_t PHILOSOPHER5_ctx;


int PHILOSOPHER5_p_id;
int PHILOSOPHER5_delay;
int PHILOSOPHER5_random_delay;
hidden int PHILOSOPHER5_procid;             /* the process id running this machine */

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
    determineSmallestDelay(smallestDelay, PHILOSOPHER1_eQ);
    determineSmallestDelay(smallestDelay, PHILOSOPHER2_eQ);
    determineSmallestDelay(smallestDelay, PHILOSOPHER3_eQ);
    determineSmallestDelay(smallestDelay, PHILOSOPHER4_eQ);
    determineSmallestDelay(smallestDelay, PHILOSOPHER5_eQ);

#if TRACE_EXECUTION
printf("%d: Smallest delay is %d\n", _pid, smallestDelay);
#endif


/* prioritize processes with lowest delay or internal events */
    rescheduleProcess(smallestDelay, ROOT_procid, ROOT_iQ, ROOT_eQ);
    rescheduleProcess(smallestDelay, PHILOSOPHER1_procid, PHILOSOPHER1_iQ, PHILOSOPHER1_eQ);
    rescheduleProcess(smallestDelay, PHILOSOPHER2_procid, PHILOSOPHER2_iQ, PHILOSOPHER2_eQ);
    rescheduleProcess(smallestDelay, PHILOSOPHER3_procid, PHILOSOPHER3_iQ, PHILOSOPHER3_eQ);
    rescheduleProcess(smallestDelay, PHILOSOPHER4_procid, PHILOSOPHER4_iQ, PHILOSOPHER4_eQ);
    rescheduleProcess(smallestDelay, PHILOSOPHER5_procid, PHILOSOPHER5_iQ, PHILOSOPHER5_eQ);

/* advance time by subtracting the smallest delay from all event delays */
    if
    :: (smallestDelay > 0) -> {
      advanceTime(smallestDelay, ROOT_eQ);
      advanceTime(smallestDelay, PHILOSOPHER1_eQ);
      advanceTime(smallestDelay, PHILOSOPHER2_eQ);
      advanceTime(smallestDelay, PHILOSOPHER3_eQ);
      advanceTime(smallestDelay, PHILOSOPHER4_eQ);
      advanceTime(smallestDelay, PHILOSOPHER5_eQ);
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
  removePendingEventsFromInvokerOnQueue(invoker, PHILOSOPHER1_eQ);
  removePendingEventsFromInvokerOnQueue(invoker, PHILOSOPHER2_eQ);
  removePendingEventsFromInvokerOnQueue(invoker, PHILOSOPHER3_eQ);
  removePendingEventsFromInvokerOnQueue(invoker, PHILOSOPHER4_eQ);
  removePendingEventsFromInvokerOnQueue(invoker, PHILOSOPHER5_eQ);
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
  cancelSendIdOnQueue(sendIdentifier, source, PHILOSOPHER1_eQ);
  cancelSendIdOnQueue(sendIdentifier, source, PHILOSOPHER2_eQ);
  cancelSendIdOnQueue(sendIdentifier, source, PHILOSOPHER3_eQ);
  cancelSendIdOnQueue(sendIdentifier, source, PHILOSOPHER4_eQ);
  cancelSendIdOnQueue(sendIdentifier, source, PHILOSOPHER5_eQ);
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
#define ROOT_USCXML_NUMBER_TRANS 4

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
          PHILOSOPHER1_flags[USCXML_CTX_FINISHED] = true;
          PHILOSOPHER2_flags[USCXML_CTX_FINISHED] = true;
          PHILOSOPHER3_flags[USCXML_CTX_FINISHED] = true;
          PHILOSOPHER4_flags[USCXML_CTX_FINISHED] = true;
          PHILOSOPHER5_flags[USCXML_CTX_FINISHED] = true;
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
          PHILOSOPHER1_p_id = 0;
          PHILOSOPHER1_delay = 2000 * ROOT_NUM_OF_PHIL;
          PHILOSOPHER1_random_delay = ROOT_seed;

#if TRACE_EXECUTION
printf("%d: Invoking in state %d\n", _pid, i);
#endif

          run PHILOSOPHER1_step() priority 20;
          PHILOSOPHER2_p_id = 1;
          PHILOSOPHER2_delay = 3000 * ROOT_NUM_OF_PHIL;
          PHILOSOPHER2_random_delay = ROOT_seed;

#if TRACE_EXECUTION
printf("%d: Invoking in state %d\n", _pid, i);
#endif

          run PHILOSOPHER2_step() priority 20;
          PHILOSOPHER3_p_id = 2;
          PHILOSOPHER3_delay = 3000 * ROOT_NUM_OF_PHIL;
          PHILOSOPHER3_random_delay = ROOT_seed;

#if TRACE_EXECUTION
printf("%d: Invoking in state %d\n", _pid, i);
#endif

          run PHILOSOPHER3_step() priority 20;
          PHILOSOPHER4_p_id = 3;
          PHILOSOPHER4_delay = 3000 * ROOT_NUM_OF_PHIL;
          PHILOSOPHER4_random_delay = ROOT_seed;

#if TRACE_EXECUTION
printf("%d: Invoking in state %d\n", _pid, i);
#endif

          run PHILOSOPHER4_step() priority 20;
          PHILOSOPHER5_p_id = 4;
          PHILOSOPHER5_delay = 3000 * ROOT_NUM_OF_PHIL;
          PHILOSOPHER5_random_delay = ROOT_seed;

#if TRACE_EXECUTION
printf("%d: Invoking in state %d\n", _pid, i);
#endif

          run PHILOSOPHER5_step() priority 20;
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
      :: ROOT__event.invokeid == PHILOSOPHER1 -> {

#if TRACE_EXECUTION
printf("%d: Finalizing event\n", _pid);
#endif

        skip
      }
      :: ROOT__event.invokeid == PHILOSOPHER2 -> {

#if TRACE_EXECUTION
printf("%d: Finalizing event\n", _pid);
#endif

        skip
      }
      :: ROOT__event.invokeid == PHILOSOPHER3 -> {

#if TRACE_EXECUTION
printf("%d: Finalizing event\n", _pid);
#endif

        skip
      }
      :: ROOT__event.invokeid == PHILOSOPHER4 -> {

#if TRACE_EXECUTION
printf("%d: Finalizing event\n", _pid);
#endif

        skip
      }
      :: ROOT__event.invokeid == PHILOSOPHER5 -> {

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
          || (i == 0 && (false || ROOT__event.name == NEED_LEFT_FORK))
          || (i == 1 && (false || ROOT__event.name == NEED_RIGHT_FORK))
          || (i == 2 && (false || ROOT__event.name == RETURN_FORKS))
          || (i == 3 && (false || ROOT__event.name == DONE_INVOKE_PHILOSOPHER3 || ROOT__event.name == DONE_INVOKE_PHILOSOPHER5 || ROOT__event.name == DONE_INVOKE_PHILOSOPHER2 || ROOT__event.name == DONE_INVOKE_PHILOSOPHER4 || ROOT__event.name == DONE_INVOKE_PHILOSOPHER1 || ROOT__event.name == DONE_INVOKE))
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
printf("%d%d%d%d", 
    ROOT_ctx.trans_set[0], 
    ROOT_ctx.trans_set[1], 
    ROOT_ctx.trans_set[2], 
    ROOT_ctx.trans_set[3]);
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
        if
        :: (ROOT_forks[ROOT_left_fork]==0) -> {
            ROOT_forks[ROOT_left_fork] = 1;
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
              ROOT__tmpE.name = TAKE_LEFT_FORK;
              ROOT__tmpE.origin = ROOT;
              _lastSeqId = _lastSeqId + 1;
              ROOT__tmpE.delay = 0;
              ROOT__tmpE.seqNr = _lastSeqId;
#if TRACE_EXECUTION
printf("%d: Sending TAKE_LEFT_FORK (%d) to ROOT_eQ\n", _pid, ROOT__tmpE.name );
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
        skip;
      }
      :: i == 1 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, i);
#endif

          ROOT_current_phil = ROOT__event.data.p_id;
          ROOT_right_fork = (ROOT_current_phil+1) % ROOT_NUM_OF_PHIL;
        if
        :: (ROOT_forks[ROOT_right_fork]==0) -> {
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
              ROOT__tmpE.name = TAKE_RIGHT_FORK;
              ROOT__tmpE.origin = ROOT;
              _lastSeqId = _lastSeqId + 1;
              ROOT__tmpE.delay = 0;
              ROOT__tmpE.seqNr = _lastSeqId;
#if TRACE_EXECUTION
printf("%d: Sending TAKE_RIGHT_FORK (%d) to ROOT_eQ\n", _pid, ROOT__tmpE.name );
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
        skip;
      }
      :: i == 2 -> {

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
      :: i == 3 -> {

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
                if
                :: (ROOT_forks[ROOT_left_fork]==0) -> {
                    ROOT_forks[ROOT_left_fork] = 1;
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
                      ROOT__tmpE.name = TAKE_LEFT_FORK;
                      ROOT__tmpE.origin = ROOT;
                      _lastSeqId = _lastSeqId + 1;
                      ROOT__tmpE.delay = 0;
                      ROOT__tmpE.seqNr = _lastSeqId;
#if TRACE_EXECUTION
printf("%d: Sending TAKE_LEFT_FORK (%d) to ROOT_eQ\n", _pid, ROOT__tmpE.name );
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
                skip;
              }
              :: j == 1 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, j);
#endif

                  ROOT_current_phil = ROOT__event.data.p_id;
                  ROOT_right_fork = (ROOT_current_phil+1) % ROOT_NUM_OF_PHIL;
                if
                :: (ROOT_forks[ROOT_right_fork]==0) -> {
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
                      ROOT__tmpE.name = TAKE_RIGHT_FORK;
                      ROOT__tmpE.origin = ROOT;
                      _lastSeqId = _lastSeqId + 1;
                      ROOT__tmpE.delay = 0;
                      ROOT__tmpE.seqNr = _lastSeqId;
#if TRACE_EXECUTION
printf("%d: Sending TAKE_RIGHT_FORK (%d) to ROOT_eQ\n", _pid, ROOT__tmpE.name );
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
                skip;
              }
              :: j == 2 -> {

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
              :: j == 3 -> {

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
      PHILOSOPHER1_flags[USCXML_CTX_FINISHED] = true;
    }
    :: i == 1 -> {
      PHILOSOPHER2_flags[USCXML_CTX_FINISHED] = true;
    }
    :: i == 1 -> {
      PHILOSOPHER3_flags[USCXML_CTX_FINISHED] = true;
    }
    :: i == 1 -> {
      PHILOSOPHER4_flags[USCXML_CTX_FINISHED] = true;
    }
    :: i == 1 -> {
      PHILOSOPHER5_flags[USCXML_CTX_FINISHED] = true;
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
#define PHILOSOPHER1_USCXML_NUMBER_STATES 8
#define PHILOSOPHER1_USCXML_NUMBER_TRANS 11

proctype PHILOSOPHER1_step() { atomic {

PHILOSOPHER1_procid = _pid;
unsigned i : 4,  j : 4,  k : 4;


/* ---------------------------- */
PHILOSOPHER1_MICROSTEP:
do
:: !PHILOSOPHER1_flags[USCXML_CTX_FINISHED] -> {
  /* Run until machine is finished */


#if TRACE_EXECUTION
printf("%d: Taking a step\n", _pid);
#endif

  /* Dequeue an event */
  PHILOSOPHER1_flags[USCXML_CTX_DEQUEUE_EXTERNAL] = false;
  if
  ::PHILOSOPHER1_flags[USCXML_CTX_SPONTANEOUS] -> {
    PHILOSOPHER1__event.name = USCXML_EVENT_SPONTANEOUS;

#if TRACE_EXECUTION
printf("%d: Trying with a spontaneous event\n", _pid);
#endif

  }
  :: else -> {
    if
    :: len(PHILOSOPHER1_iQ) != 0 -> {
      PHILOSOPHER1_iQ ? PHILOSOPHER1__event;

#if TRACE_EXECUTION
printf("%d: Deqeued an internal event\n", _pid);
#endif

    }
    :: else -> {
      PHILOSOPHER1_flags[USCXML_CTX_DEQUEUE_EXTERNAL] = true;
    }
    fi;
  }
  fi;


  if
  :: PHILOSOPHER1_flags[USCXML_CTX_DEQUEUE_EXTERNAL] -> {
    /* manage invocations */
    i = 0;
    do
    :: i < PHILOSOPHER1_USCXML_NUMBER_STATES -> {
      d_step { 
      /* uninvoke */
      if
      :: !PHILOSOPHER1_config[i] && PHILOSOPHER1_invocations[i] -> {

#if TRACE_EXECUTION
printf("%d: Uninvoking in state %d\n", _pid, i);
#endif

        if
        :: else -> skip;
        fi
        PHILOSOPHER1_invocations[i] = false;
        skip;
      }
      :: else -> skip;
      fi;
      } /* d_step */

      /* invoke */
      if
      :: PHILOSOPHER1_config[i] && !PHILOSOPHER1_invocations[i] -> {
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
    :: PHILOSOPHER1_flags[USCXML_CTX_FINISHED] -> {
      goto PHILOSOPHER1_TERMINATE_MACHINE;
    }
    :: else -> skip;
    fi
    /* Not sure if this should be before the invocation due to auto-forwarding */
    if
    :: len(PHILOSOPHER1_eQ) != 0 -> {
      PHILOSOPHER1_eQ ? PHILOSOPHER1__event;

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
PHILOSOPHER1_SELECT_TRANSITIONS:
PHILOSOPHER1_STATES_CLEAR(PHILOSOPHER1_ctx.target_set)
PHILOSOPHER1_STATES_CLEAR(PHILOSOPHER1_ctx.exit_set)
PHILOSOPHER1_TRANS_CLEAR(PHILOSOPHER1_ctx.conflicts)
PHILOSOPHER1_TRANS_CLEAR(PHILOSOPHER1_ctx.trans_set)
#if TRACE_EXECUTION
printf("%d: Establishing optimal transition set for event %d\n", _pid, PHILOSOPHER1__event.name );
#endif

#if TRACE_EXECUTION
printf("Configuration: ");
printf("%d%d%d%d%d%d%d%d", 
    PHILOSOPHER1_config[0], 
    PHILOSOPHER1_config[1], 
    PHILOSOPHER1_config[2], 
    PHILOSOPHER1_config[3], 
    PHILOSOPHER1_config[4], 
    PHILOSOPHER1_config[5], 
    PHILOSOPHER1_config[6], 
    PHILOSOPHER1_config[7]);
printf("\n");
#endif

  PHILOSOPHER1_flags[USCXML_CTX_TRANSITION_FOUND] = false;
  i = 0;
  do
  :: i < PHILOSOPHER1_USCXML_NUMBER_TRANS -> {
    /* only select non-history, non-initial transitions */
    if
    :: !PHILOSOPHER1_transitions[i].type[USCXML_TRANS_HISTORY] &&
       !PHILOSOPHER1_transitions[i].type[USCXML_TRANS_INITIAL] -> {
      if
      :: /* is the transition active? */
         PHILOSOPHER1_config[PHILOSOPHER1_transitions[i].source] && 

         /* is it non-conflicting? */
         !PHILOSOPHER1_ctx.conflicts[i] && 

         /* is it spontaneous with an event or vice versa? */
         ((PHILOSOPHER1__event.name == USCXML_EVENT_SPONTANEOUS && 
           PHILOSOPHER1_transitions[i].type[USCXML_TRANS_SPONTANEOUS]) || 
          (PHILOSOPHER1__event.name != USCXML_EVENT_SPONTANEOUS && 
           !PHILOSOPHER1_transitions[i].type[USCXML_TRANS_SPONTANEOUS])) &&

         /* is it matching and enabled? */
         (false 
          || (i == 0 && (false || PHILOSOPHER1__event.name == THINKING_OVER))
          || (i == 1 && (false || PHILOSOPHER1__event.name == TAKE_LEFT_FORK))
          || (i == 2 && (false || PHILOSOPHER1__event.name == TAKE_RIGHT_FORK))
          || (i == 3 && (false || PHILOSOPHER1__event.name == TIMEOUT))
          || (i == 4 && (false || PHILOSOPHER1__event.name == TAKE_RIGHT_FORK))
          || (i == 5 && (false || PHILOSOPHER1__event.name == RESEND_NEED_RIGHT_FORK))
          || (i == 6 && (false || PHILOSOPHER1__event.name == TIMEOUT))
          || (i == 7 && (false || PHILOSOPHER1__event.name == TAKE_LEFT_FORK))
          || (i == 8 && (false || PHILOSOPHER1__event.name == RESEND_NEED_LEFT_FORK))
          || (i == 9 && (false || PHILOSOPHER1__event.name == TIMEOUT))
          || (i == 10 && (false || PHILOSOPHER1__event.name == EATING_OVER))
         ) -> {
        /* remember that we found a transition */
        PHILOSOPHER1_flags[USCXML_CTX_TRANSITION_FOUND] = true;

        /* transitions that are pre-empted */
        PHILOSOPHER1_TRANS_OR(PHILOSOPHER1_ctx.conflicts, PHILOSOPHER1_transitions[i].conflicts)

        /* states that are directly targeted (resolve as entry-set later) */
        PHILOSOPHER1_STATES_OR(PHILOSOPHER1_ctx.target_set, PHILOSOPHER1_transitions[i].target)

        /* states that will be left */
        PHILOSOPHER1_STATES_OR(PHILOSOPHER1_ctx.exit_set, PHILOSOPHER1_transitions[i].exit_set)

        PHILOSOPHER1_ctx.trans_set[i] = true;
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
  PHILOSOPHER1_STATES_AND(PHILOSOPHER1_ctx.exit_set, PHILOSOPHER1_config)

#if TRACE_EXECUTION
printf("Selected Transitions: ");
printf("%d%d%d%d%d%d%d%d%d%d%d", 
    PHILOSOPHER1_ctx.trans_set[0], 
    PHILOSOPHER1_ctx.trans_set[1], 
    PHILOSOPHER1_ctx.trans_set[2], 
    PHILOSOPHER1_ctx.trans_set[3], 
    PHILOSOPHER1_ctx.trans_set[4], 
    PHILOSOPHER1_ctx.trans_set[5], 
    PHILOSOPHER1_ctx.trans_set[6], 
    PHILOSOPHER1_ctx.trans_set[7], 
    PHILOSOPHER1_ctx.trans_set[8], 
    PHILOSOPHER1_ctx.trans_set[9], 
    PHILOSOPHER1_ctx.trans_set[10]);
printf("\n");
#endif


#if TRACE_EXECUTION
printf("Target Set: ");
printf("%d%d%d%d%d%d%d%d", 
    PHILOSOPHER1_ctx.target_set[0], 
    PHILOSOPHER1_ctx.target_set[1], 
    PHILOSOPHER1_ctx.target_set[2], 
    PHILOSOPHER1_ctx.target_set[3], 
    PHILOSOPHER1_ctx.target_set[4], 
    PHILOSOPHER1_ctx.target_set[5], 
    PHILOSOPHER1_ctx.target_set[6], 
    PHILOSOPHER1_ctx.target_set[7]);
printf("\n");
#endif


#if TRACE_EXECUTION
printf("Exit Set: ");
printf("%d%d%d%d%d%d%d%d", 
    PHILOSOPHER1_ctx.exit_set[0], 
    PHILOSOPHER1_ctx.exit_set[1], 
    PHILOSOPHER1_ctx.exit_set[2], 
    PHILOSOPHER1_ctx.exit_set[3], 
    PHILOSOPHER1_ctx.exit_set[4], 
    PHILOSOPHER1_ctx.exit_set[5], 
    PHILOSOPHER1_ctx.exit_set[6], 
    PHILOSOPHER1_ctx.exit_set[7]);
printf("\n");
#endif

  if
  :: !PHILOSOPHER1_STATES_HAS_ANY(PHILOSOPHER1_config) -> {
    /* Enter initial configuration */
    PHILOSOPHER1_STATES_COPY(PHILOSOPHER1_ctx.target_set, PHILOSOPHER1_states[0].completion)
    PHILOSOPHER1_flags[USCXML_CTX_SPONTANEOUS] = true;
    PHILOSOPHER1_flags[USCXML_CTX_TRANSITION_FOUND] = true;

#if TRACE_EXECUTION
printf("%d: Entering initial default completion\n", _pid);
#endif


  }
  :: PHILOSOPHER1_flags[USCXML_CTX_TRANSITION_FOUND] -> {

#if TRACE_EXECUTION
printf("%d: Found transitions\n", _pid);
#endif

    PHILOSOPHER1_flags[USCXML_CTX_SPONTANEOUS] = true;
  }
  :: else {
    PHILOSOPHER1_flags[USCXML_CTX_SPONTANEOUS] = false;

#if TRACE_EXECUTION
printf("%d: Found NO transitions\n", _pid);
#endif

  }
  fi


  if
  :: PHILOSOPHER1_flags[USCXML_CTX_TRANSITION_FOUND] -> {
    /* only process anything if we found transitions or are on initial entry */
/* ---------------------------- */
/* REMEMBER_HISTORY: */

#if TRACE_EXECUTION
printf("%d: Save history configurations\n", _pid);
#endif

  if
  :: PHILOSOPHER1_STATES_HAS_ANY(PHILOSOPHER1_config) -> {
    /* only remember history on non-initial entry */
    i = 0;
    do
    :: i < PHILOSOPHER1_USCXML_NUMBER_STATES -> {
      if
      :: PHILOSOPHER1_states[i].type[USCXML_STATE_HISTORY_SHALLOW] ||
         PHILOSOPHER1_states[i].type[USCXML_STATE_HISTORY_DEEP] -> {
        if
        :: PHILOSOPHER1_ctx.exit_set[PHILOSOPHER1_states[i].parent] -> {
          /* a history state whose parent is about to be exited */

#if TRACE_EXECUTION
printf("%d: history state %d is about to be exited\n", _pid, i);
#endif


#if TRACE_EXECUTION
printf("COMPLET: ");
printf("%d%d%d%d%d%d%d%d", 
    PHILOSOPHER1_states[i].completion[0], 
    PHILOSOPHER1_states[i].completion[1], 
    PHILOSOPHER1_states[i].completion[2], 
    PHILOSOPHER1_states[i].completion[3], 
    PHILOSOPHER1_states[i].completion[4], 
    PHILOSOPHER1_states[i].completion[5], 
    PHILOSOPHER1_states[i].completion[6], 
    PHILOSOPHER1_states[i].completion[7]);
printf("\n");
#endif

          PHILOSOPHER1_STATES_COPY(PHILOSOPHER1_ctx.tmp_states, PHILOSOPHER1_states[i].completion)

          /* set those states who were enabled */
          PHILOSOPHER1_STATES_AND(PHILOSOPHER1_ctx.tmp_states, PHILOSOPHER1_config)

#if TRACE_EXECUTION
printf("CONFIG : ");
printf("%d%d%d%d%d%d%d%d", 
    PHILOSOPHER1_config[0], 
    PHILOSOPHER1_config[1], 
    PHILOSOPHER1_config[2], 
    PHILOSOPHER1_config[3], 
    PHILOSOPHER1_config[4], 
    PHILOSOPHER1_config[5], 
    PHILOSOPHER1_config[6], 
    PHILOSOPHER1_config[7]);
printf("\n");
#endif


#if TRACE_EXECUTION
printf("TMP_STS: ");
printf("%d%d%d%d%d%d%d%d", 
    PHILOSOPHER1_ctx.tmp_states[0], 
    PHILOSOPHER1_ctx.tmp_states[1], 
    PHILOSOPHER1_ctx.tmp_states[2], 
    PHILOSOPHER1_ctx.tmp_states[3], 
    PHILOSOPHER1_ctx.tmp_states[4], 
    PHILOSOPHER1_ctx.tmp_states[5], 
    PHILOSOPHER1_ctx.tmp_states[6], 
    PHILOSOPHER1_ctx.tmp_states[7]);
printf("\n");
#endif


          /* clear current history with completion mask */
          PHILOSOPHER1_STATES_AND_NOT(PHILOSOPHER1_history, PHILOSOPHER1_states[i].completion)

          /* set history */
          PHILOSOPHER1_STATES_OR(PHILOSOPHER1_history, PHILOSOPHER1_ctx.tmp_states)

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
printf("%d%d%d%d%d%d%d%d", 
    PHILOSOPHER1_history[0], 
    PHILOSOPHER1_history[1], 
    PHILOSOPHER1_history[2], 
    PHILOSOPHER1_history[3], 
    PHILOSOPHER1_history[4], 
    PHILOSOPHER1_history[5], 
    PHILOSOPHER1_history[6], 
    PHILOSOPHER1_history[7]);
printf("\n");
#endif
  }
  :: else -> skip;
  fi;

/* ---------------------------- */
PHILOSOPHER1_ESTABLISH_ENTRY_SET:
  /* calculate new entry set */
  PHILOSOPHER1_STATES_COPY(PHILOSOPHER1_ctx.entry_set, PHILOSOPHER1_ctx.target_set)

  i = 0;
  do
  :: i < PHILOSOPHER1_USCXML_NUMBER_STATES -> {
    if
    :: PHILOSOPHER1_ctx.entry_set[i] -> {
      /* ancestor completion */
      PHILOSOPHER1_STATES_OR(PHILOSOPHER1_ctx.entry_set, PHILOSOPHER1_states[i].ancestors)
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
  :: i < PHILOSOPHER1_USCXML_NUMBER_STATES -> {
    if
    :: PHILOSOPHER1_ctx.entry_set[i] -> {
      if
      :: PHILOSOPHER1_states[i].type[USCXML_STATE_PARALLEL] -> {
        PHILOSOPHER1_STATES_OR(PHILOSOPHER1_ctx.entry_set, PHILOSOPHER1_states[i].completion)
      }
      :: PHILOSOPHER1_states[i].type[USCXML_STATE_HISTORY_SHALLOW] ||
         PHILOSOPHER1_states[i].type[USCXML_STATE_HISTORY_DEEP] -> {

#if TRACE_EXECUTION
printf("%d: Descendant completion for history state %d\n", _pid, i);
#endif

        if
        :: !PHILOSOPHER1_STATES_HAS_AND(PHILOSOPHER1_states[i].completion, PHILOSOPHER1_history) && !PHILOSOPHER1_config[PHILOSOPHER1_states[i].parent] -> {
          /* nothing set for history, look for a default transition */

#if TRACE_EXECUTION
printf("%d: Fresh history in target set\n", _pid);
#endif

          j = 0;
          do
          :: j < PHILOSOPHER1_USCXML_NUMBER_TRANS -> {
             if
             :: PHILOSOPHER1_transitions[j].source == i -> {
               PHILOSOPHER1_ctx.trans_set[j] = true;
               PHILOSOPHER1_STATES_OR(PHILOSOPHER1_ctx.entry_set, PHILOSOPHER1_transitions[j].target)

               if
               :: (PHILOSOPHER1_states[i].type[USCXML_STATE_HISTORY_DEEP] &&
                   !PHILOSOPHER1_STATES_HAS_AND(PHILOSOPHER1_transitions[j].target, PHILOSOPHER1_states[i].children)                  ) -> {
                 k = i + 1
                 do
                 :: k < PHILOSOPHER1_USCXML_NUMBER_STATES -> {
                   if
                   :: PHILOSOPHER1_transitions[j].target[k] -> {
                     PHILOSOPHER1_STATES_OR(PHILOSOPHER1_ctx.entry_set, PHILOSOPHER1_states[k].ancestors)
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

          PHILOSOPHER1_STATES_COPY(PHILOSOPHER1_ctx.tmp_states, PHILOSOPHER1_states[i].completion)
          PHILOSOPHER1_STATES_AND(PHILOSOPHER1_ctx.tmp_states, PHILOSOPHER1_history)
          PHILOSOPHER1_STATES_OR(PHILOSOPHER1_ctx.entry_set, PHILOSOPHER1_ctx.tmp_states)
          if
          :: PHILOSOPHER1_states[i].type[USCXML_STATE_HAS_HISTORY] ||
             PHILOSOPHER1_states[i].type[USCXML_STATE_HISTORY_DEEP] -> { 
            /* a deep history state with nested histories -> more completion */

#if TRACE_EXECUTION
printf("%d: DEEP HISTORY\n", _pid);
#endif

            j = i + 1;
            do
            :: j < PHILOSOPHER1_USCXML_NUMBER_STATES -> {
              if
              :: (PHILOSOPHER1_states[i].completion[j] &&
                  PHILOSOPHER1_ctx.entry_set[j] && 
                  PHILOSOPHER1_states[j].type[USCXML_STATE_HAS_HISTORY]) -> {
                k = j + 1;
                do
                :: k < PHILOSOPHER1_USCXML_NUMBER_STATES -> {
                  /* add nested history to entry_set */
                  if
                  :: (PHILOSOPHER1_states[k].type[USCXML_STATE_HISTORY_DEEP] ||
                      PHILOSOPHER1_states[k].type[USCXML_STATE_HISTORY_SHALLOW]) &&
                     PHILOSOPHER1_states[j].children[k] -> {
                    /* a nested history state */
                    PHILOSOPHER1_ctx.entry_set[k] = true;
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
      :: PHILOSOPHER1_states[i].type[USCXML_STATE_INITIAL] -> {

#if TRACE_EXECUTION
printf("%d: Descendant completion for initial state %d\n", _pid, i);
#endif

        j = 0
        do
        :: j < PHILOSOPHER1_USCXML_NUMBER_TRANS -> {
          if
          :: PHILOSOPHER1_transitions[j].source == i -> {
            PHILOSOPHER1_ctx.trans_set[j] = true;
            PHILOSOPHER1_ctx.entry_set[i] = false;

#if TRACE_EXECUTION
printf("%d: Adding transition %d!\n", _pid, j);
#endif

            PHILOSOPHER1_STATES_OR(PHILOSOPHER1_ctx.entry_set, PHILOSOPHER1_transitions[j].target)

            k = i + 1;
            do
            :: k < PHILOSOPHER1_USCXML_NUMBER_STATES -> {
              if
              :: PHILOSOPHER1_transitions[j].target[k] -> {
                PHILOSOPHER1_STATES_OR(PHILOSOPHER1_ctx.entry_set, PHILOSOPHER1_states[k].ancestors)

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
      :: PHILOSOPHER1_states[i].type[USCXML_STATE_COMPOUND] -> {
        /* we need to check whether one child is already in entry_set */
        if
        :: (
          !PHILOSOPHER1_STATES_HAS_AND(PHILOSOPHER1_ctx.entry_set, PHILOSOPHER1_states[i].children) && 
           (!PHILOSOPHER1_STATES_HAS_AND(PHILOSOPHER1_config, PHILOSOPHER1_states[i].children) || PHILOSOPHER1_STATES_HAS_AND(PHILOSOPHER1_ctx.exit_set, PHILOSOPHER1_states[i].children)
)) 
        -> {
          PHILOSOPHER1_STATES_OR(PHILOSOPHER1_ctx.entry_set, PHILOSOPHER1_states[i].completion)
          if
          :: (PHILOSOPHER1_STATES_HAS_AND(PHILOSOPHER1_states[i].completion, PHILOSOPHER1_states[i].children)
          ) -> {
            /* deep completion */
            j = i + 1;
            do
            :: j < PHILOSOPHER1_USCXML_NUMBER_STATES - 1 -> {
              j = j + 1;
              if
              :: PHILOSOPHER1_states[i].completion[j] -> {
                PHILOSOPHER1_STATES_OR(PHILOSOPHER1_ctx.entry_set, PHILOSOPHER1_states[j].ancestors)

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
printf("%d%d%d%d%d%d%d%d", 
    PHILOSOPHER1_ctx.entry_set[0], 
    PHILOSOPHER1_ctx.entry_set[1], 
    PHILOSOPHER1_ctx.entry_set[2], 
    PHILOSOPHER1_ctx.entry_set[3], 
    PHILOSOPHER1_ctx.entry_set[4], 
    PHILOSOPHER1_ctx.entry_set[5], 
    PHILOSOPHER1_ctx.entry_set[6], 
    PHILOSOPHER1_ctx.entry_set[7]);
printf("\n");
#endif


/* ---------------------------- */
/* EXIT_STATES: */
  i = PHILOSOPHER1_USCXML_NUMBER_STATES;
  do
  :: i > 0 -> {
    i = i - 1;
    if
    :: PHILOSOPHER1_ctx.exit_set[i] && PHILOSOPHER1_config[i] -> {
      /* call all on-exit handlers */

#if TRACE_EXECUTION
printf("%d: Exiting state %d\n", _pid, i);
#endif

      if
      :: i == 3 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for exiting state %d\n", _pid, i);
#endif

      if
      :: (PHILOSOPHER1__event.name == TAKE_LEFT_FORK || PHILOSOPHER1__event.name == TAKE_RIGHT_FORK) -> {
          cancelSendId(STARVATION_TIMER,PHILOSOPHER1);
      }
      :: else -> skip;
      fi;
      }
      :: i == 4 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for exiting state %d\n", _pid, i);
#endif

      if
      :: (PHILOSOPHER1__event.name == TAKE_RIGHT_FORK) -> {
          cancelSendId(STARVATION_TIMER,PHILOSOPHER1);
      }
      :: else -> skip;
      fi;
      }
      :: i == 5 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for exiting state %d\n", _pid, i);
#endif

      if
      :: (PHILOSOPHER1__event.name == TAKE_LEFT_FORK) -> {
          cancelSendId(STARVATION_TIMER,PHILOSOPHER1);
      }
      :: else -> skip;
      fi;
      }
      :: else -> skip;
      fi

      PHILOSOPHER1_config[i] = false;
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
  :: i < PHILOSOPHER1_USCXML_NUMBER_TRANS -> {
    if
    :: PHILOSOPHER1_ctx.trans_set[i] && 
       !PHILOSOPHER1_transitions[i].type[USCXML_TRANS_HISTORY] && 
       !PHILOSOPHER1_transitions[i].type[USCXML_TRANS_INITIAL] -> {
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

        printf("philospher: : %d", PHILOSOPHER1_p_id);
        printf("starved in state hungry for Time(in ms) : : %d", PHILOSOPHER1_delay);
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
        :: !PHILOSOPHER1_flags[USCXML_CTX_FINISHED] || PHILOSOPHER1_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
          {
            PHILOSOPHER1__tmpE.data.p_id = 0;
            PHILOSOPHER1__tmpE.delay = 0;
            PHILOSOPHER1__tmpE.invokeid = 0;
            PHILOSOPHER1__tmpE.name = 0;
            PHILOSOPHER1__tmpE.origin = 0;
            PHILOSOPHER1__tmpE.sendid = 0;
            PHILOSOPHER1__tmpE.seqNr = 0;
            PHILOSOPHER1__tmpE.name = NEED_RIGHT_FORK;
            PHILOSOPHER1__tmpE.invokeid = PHILOSOPHER1;
            PHILOSOPHER1__tmpE.origin = PHILOSOPHER1;
            _lastSeqId = _lastSeqId + 1;
            PHILOSOPHER1__tmpE.delay = 0;
            PHILOSOPHER1__tmpE.seqNr = _lastSeqId;
            PHILOSOPHER1__tmpE.data.p_id = PHILOSOPHER1_p_id;
#if TRACE_EXECUTION
printf("%d: Sending NEED_RIGHT_FORK (%d) to ROOT_eQ\n", _pid, PHILOSOPHER1__tmpE.name );
#endif

            ROOT_eQ!PHILOSOPHER1__tmpE;
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

        printf("philospher: : %d", PHILOSOPHER1_p_id);
        printf("starved in state has_right_fork for Time(in ms) :: %d", PHILOSOPHER1_delay);
        skip;
      }
      :: i == 7 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, i);
#endif

        skip;
      }
      :: i == 8 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, i);
#endif

        if
        :: !PHILOSOPHER1_flags[USCXML_CTX_FINISHED] || PHILOSOPHER1_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
          {
            PHILOSOPHER1__tmpE.data.p_id = 0;
            PHILOSOPHER1__tmpE.delay = 0;
            PHILOSOPHER1__tmpE.invokeid = 0;
            PHILOSOPHER1__tmpE.name = 0;
            PHILOSOPHER1__tmpE.origin = 0;
            PHILOSOPHER1__tmpE.sendid = 0;
            PHILOSOPHER1__tmpE.seqNr = 0;
            PHILOSOPHER1__tmpE.name = NEED_LEFT_FORK;
            PHILOSOPHER1__tmpE.invokeid = PHILOSOPHER1;
            PHILOSOPHER1__tmpE.origin = PHILOSOPHER1;
            _lastSeqId = _lastSeqId + 1;
            PHILOSOPHER1__tmpE.delay = 0;
            PHILOSOPHER1__tmpE.seqNr = _lastSeqId;
            PHILOSOPHER1__tmpE.data.p_id = PHILOSOPHER1_p_id;
#if TRACE_EXECUTION
printf("%d: Sending NEED_LEFT_FORK (%d) to ROOT_eQ\n", _pid, PHILOSOPHER1__tmpE.name );
#endif

            ROOT_eQ!PHILOSOPHER1__tmpE;
            insertWithDelay(ROOT_eQ);
          }
          skip;
        }
        :: else -> skip;
        fi
        skip;
      }
      :: i == 9 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, i);
#endif

        printf("philospher: : %d", PHILOSOPHER1_p_id);
        printf("starved in state has_right_fork for Time(in ms) : : %d", PHILOSOPHER1_delay);
        skip;
      }
      :: i == 10 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, i);
#endif

        if
        :: !PHILOSOPHER1_flags[USCXML_CTX_FINISHED] || PHILOSOPHER1_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
          {
            PHILOSOPHER1__tmpE.data.p_id = 0;
            PHILOSOPHER1__tmpE.delay = 0;
            PHILOSOPHER1__tmpE.invokeid = 0;
            PHILOSOPHER1__tmpE.name = 0;
            PHILOSOPHER1__tmpE.origin = 0;
            PHILOSOPHER1__tmpE.sendid = 0;
            PHILOSOPHER1__tmpE.seqNr = 0;
            PHILOSOPHER1__tmpE.name = RETURN_FORKS;
            PHILOSOPHER1__tmpE.invokeid = PHILOSOPHER1;
            PHILOSOPHER1__tmpE.origin = PHILOSOPHER1;
            _lastSeqId = _lastSeqId + 1;
            PHILOSOPHER1__tmpE.delay = 0;
            PHILOSOPHER1__tmpE.seqNr = _lastSeqId;
            PHILOSOPHER1__tmpE.data.p_id = PHILOSOPHER1_p_id;
#if TRACE_EXECUTION
printf("%d: Sending RETURN_FORKS (%d) to ROOT_eQ\n", _pid, PHILOSOPHER1__tmpE.name );
#endif

            ROOT_eQ!PHILOSOPHER1__tmpE;
            insertWithDelay(ROOT_eQ);
          }
          skip;
        }
        :: else -> skip;
        fi
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
  :: i < PHILOSOPHER1_USCXML_NUMBER_STATES -> {
    if
    :: (PHILOSOPHER1_ctx.entry_set[i] &&
        !PHILOSOPHER1_config[i] && 
        /* these are no proper states */
        !PHILOSOPHER1_states[i].type[USCXML_STATE_HISTORY_DEEP] && 
        !PHILOSOPHER1_states[i].type[USCXML_STATE_HISTORY_SHALLOW] && 
        !PHILOSOPHER1_states[i].type[USCXML_STATE_INITIAL]
       ) -> {

#if TRACE_EXECUTION
printf("%d: Entering state %d\n", _pid, i);
#endif

         PHILOSOPHER1_config[i] = true;

         /* Process executable content for entering a state */
         if
         :: i == 1 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for entering state %d\n", _pid, i);
#endif

          printf("Hello, I am philospher number: : %d", PHILOSOPHER1_p_id);
         }
         :: i == 2 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for entering state %d\n", _pid, i);
#endif

          printf("Thinking philosopher: : %d", PHILOSOPHER1_p_id);
            PHILOSOPHER1_random_delay = ((1103515245*PHILOSOPHER1_random_delay+12345)%2147483647)%2000;
          if
          :: !PHILOSOPHER1_flags[USCXML_CTX_FINISHED] || PHILOSOPHER1_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
            {
              PHILOSOPHER1__tmpE.data.p_id = 0;
              PHILOSOPHER1__tmpE.delay = 0;
              PHILOSOPHER1__tmpE.invokeid = 0;
              PHILOSOPHER1__tmpE.name = 0;
              PHILOSOPHER1__tmpE.origin = 0;
              PHILOSOPHER1__tmpE.sendid = 0;
              PHILOSOPHER1__tmpE.seqNr = 0;
              PHILOSOPHER1__tmpE.name = THINKING_OVER;
              PHILOSOPHER1__tmpE.invokeid = PHILOSOPHER1;
              PHILOSOPHER1__tmpE.origin = PHILOSOPHER1;
              _lastSeqId = _lastSeqId + 1;
              PHILOSOPHER1__tmpE.delay = PHILOSOPHER1_random_delay*(PHILOSOPHER1_p_id+1);
              PHILOSOPHER1__tmpE.seqNr = _lastSeqId;
#if TRACE_EXECUTION
printf("%d: Sending THINKING_OVER (%d) to PHILOSOPHER1_eQ\n", _pid, PHILOSOPHER1__tmpE.name );
#endif

              PHILOSOPHER1_eQ!PHILOSOPHER1__tmpE;
              insertWithDelay(PHILOSOPHER1_eQ);
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

          printf("Hungry philosopher: : %d", PHILOSOPHER1_p_id);
          if
          :: !PHILOSOPHER1_flags[USCXML_CTX_FINISHED] || PHILOSOPHER1_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
            {
              PHILOSOPHER1__tmpE.data.p_id = 0;
              PHILOSOPHER1__tmpE.delay = 0;
              PHILOSOPHER1__tmpE.invokeid = 0;
              PHILOSOPHER1__tmpE.name = 0;
              PHILOSOPHER1__tmpE.origin = 0;
              PHILOSOPHER1__tmpE.sendid = 0;
              PHILOSOPHER1__tmpE.seqNr = 0;
              PHILOSOPHER1__tmpE.name = TIMEOUT;
              PHILOSOPHER1__tmpE.sendid = STARVATION_TIMER;
              PHILOSOPHER1__tmpE.invokeid = PHILOSOPHER1;
              PHILOSOPHER1__tmpE.origin = PHILOSOPHER1;
              _lastSeqId = _lastSeqId + 1;
              PHILOSOPHER1__tmpE.delay = PHILOSOPHER1_delay;
              PHILOSOPHER1__tmpE.seqNr = _lastSeqId;
#if TRACE_EXECUTION
printf("%d: Sending TIMEOUT (%d) to PHILOSOPHER1_eQ\n", _pid, PHILOSOPHER1__tmpE.name );
#endif

              PHILOSOPHER1_eQ!PHILOSOPHER1__tmpE;
              insertWithDelay(PHILOSOPHER1_eQ);
            }
            skip;
          }
          :: else -> skip;
          fi
          if
          :: !PHILOSOPHER1_flags[USCXML_CTX_FINISHED] || PHILOSOPHER1_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
            {
              PHILOSOPHER1__tmpE.data.p_id = 0;
              PHILOSOPHER1__tmpE.delay = 0;
              PHILOSOPHER1__tmpE.invokeid = 0;
              PHILOSOPHER1__tmpE.name = 0;
              PHILOSOPHER1__tmpE.origin = 0;
              PHILOSOPHER1__tmpE.sendid = 0;
              PHILOSOPHER1__tmpE.seqNr = 0;
              PHILOSOPHER1__tmpE.name = NEED_LEFT_FORK;
              PHILOSOPHER1__tmpE.invokeid = PHILOSOPHER1;
              PHILOSOPHER1__tmpE.origin = PHILOSOPHER1;
              _lastSeqId = _lastSeqId + 1;
              PHILOSOPHER1__tmpE.delay = 0;
              PHILOSOPHER1__tmpE.seqNr = _lastSeqId;
              PHILOSOPHER1__tmpE.data.p_id = PHILOSOPHER1_p_id;
#if TRACE_EXECUTION
printf("%d: Sending NEED_LEFT_FORK (%d) to ROOT_eQ\n", _pid, PHILOSOPHER1__tmpE.name );
#endif

              ROOT_eQ!PHILOSOPHER1__tmpE;
              insertWithDelay(ROOT_eQ);
            }
            skip;
          }
          :: else -> skip;
          fi
          if
          :: !PHILOSOPHER1_flags[USCXML_CTX_FINISHED] || PHILOSOPHER1_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
            {
              PHILOSOPHER1__tmpE.data.p_id = 0;
              PHILOSOPHER1__tmpE.delay = 0;
              PHILOSOPHER1__tmpE.invokeid = 0;
              PHILOSOPHER1__tmpE.name = 0;
              PHILOSOPHER1__tmpE.origin = 0;
              PHILOSOPHER1__tmpE.sendid = 0;
              PHILOSOPHER1__tmpE.seqNr = 0;
              PHILOSOPHER1__tmpE.name = NEED_RIGHT_FORK;
              PHILOSOPHER1__tmpE.invokeid = PHILOSOPHER1;
              PHILOSOPHER1__tmpE.origin = PHILOSOPHER1;
              _lastSeqId = _lastSeqId + 1;
              PHILOSOPHER1__tmpE.delay = 0;
              PHILOSOPHER1__tmpE.seqNr = _lastSeqId;
              PHILOSOPHER1__tmpE.data.p_id = PHILOSOPHER1_p_id;
#if TRACE_EXECUTION
printf("%d: Sending NEED_RIGHT_FORK (%d) to ROOT_eQ\n", _pid, PHILOSOPHER1__tmpE.name );
#endif

              ROOT_eQ!PHILOSOPHER1__tmpE;
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

          printf("in state has_left_fork for philosopher: : %d", PHILOSOPHER1_p_id);
          if
          :: !PHILOSOPHER1_flags[USCXML_CTX_FINISHED] || PHILOSOPHER1_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
            {
              PHILOSOPHER1__tmpE.data.p_id = 0;
              PHILOSOPHER1__tmpE.delay = 0;
              PHILOSOPHER1__tmpE.invokeid = 0;
              PHILOSOPHER1__tmpE.name = 0;
              PHILOSOPHER1__tmpE.origin = 0;
              PHILOSOPHER1__tmpE.sendid = 0;
              PHILOSOPHER1__tmpE.seqNr = 0;
              PHILOSOPHER1__tmpE.name = TIMEOUT;
              PHILOSOPHER1__tmpE.sendid = STARVATION_TIMER;
              PHILOSOPHER1__tmpE.invokeid = PHILOSOPHER1;
              PHILOSOPHER1__tmpE.origin = PHILOSOPHER1;
              _lastSeqId = _lastSeqId + 1;
              PHILOSOPHER1__tmpE.delay = PHILOSOPHER1_delay;
              PHILOSOPHER1__tmpE.seqNr = _lastSeqId;
#if TRACE_EXECUTION
printf("%d: Sending TIMEOUT (%d) to PHILOSOPHER1_eQ\n", _pid, PHILOSOPHER1__tmpE.name );
#endif

              PHILOSOPHER1_eQ!PHILOSOPHER1__tmpE;
              insertWithDelay(PHILOSOPHER1_eQ);
            }
            skip;
          }
          :: else -> skip;
          fi
          if
          :: !PHILOSOPHER1_flags[USCXML_CTX_FINISHED] || PHILOSOPHER1_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
            {
              PHILOSOPHER1__tmpE.data.p_id = 0;
              PHILOSOPHER1__tmpE.delay = 0;
              PHILOSOPHER1__tmpE.invokeid = 0;
              PHILOSOPHER1__tmpE.name = 0;
              PHILOSOPHER1__tmpE.origin = 0;
              PHILOSOPHER1__tmpE.sendid = 0;
              PHILOSOPHER1__tmpE.seqNr = 0;
              PHILOSOPHER1__tmpE.name = RESEND_NEED_RIGHT_FORK;
              PHILOSOPHER1__tmpE.invokeid = PHILOSOPHER1;
              PHILOSOPHER1__tmpE.origin = PHILOSOPHER1;
              _lastSeqId = _lastSeqId + 1;
              PHILOSOPHER1__tmpE.delay = 500;
              PHILOSOPHER1__tmpE.seqNr = _lastSeqId;
#if TRACE_EXECUTION
printf("%d: Sending RESEND_NEED_RIGHT_FORK (%d) to PHILOSOPHER1_eQ\n", _pid, PHILOSOPHER1__tmpE.name );
#endif

              PHILOSOPHER1_eQ!PHILOSOPHER1__tmpE;
              insertWithDelay(PHILOSOPHER1_eQ);
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

          printf("in state has_right_fork for philosopher: : %d", PHILOSOPHER1_p_id);
          if
          :: !PHILOSOPHER1_flags[USCXML_CTX_FINISHED] || PHILOSOPHER1_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
            {
              PHILOSOPHER1__tmpE.data.p_id = 0;
              PHILOSOPHER1__tmpE.delay = 0;
              PHILOSOPHER1__tmpE.invokeid = 0;
              PHILOSOPHER1__tmpE.name = 0;
              PHILOSOPHER1__tmpE.origin = 0;
              PHILOSOPHER1__tmpE.sendid = 0;
              PHILOSOPHER1__tmpE.seqNr = 0;
              PHILOSOPHER1__tmpE.name = TIMEOUT;
              PHILOSOPHER1__tmpE.sendid = STARVATION_TIMER;
              PHILOSOPHER1__tmpE.invokeid = PHILOSOPHER1;
              PHILOSOPHER1__tmpE.origin = PHILOSOPHER1;
              _lastSeqId = _lastSeqId + 1;
              PHILOSOPHER1__tmpE.delay = PHILOSOPHER1_delay;
              PHILOSOPHER1__tmpE.seqNr = _lastSeqId;
#if TRACE_EXECUTION
printf("%d: Sending TIMEOUT (%d) to PHILOSOPHER1_eQ\n", _pid, PHILOSOPHER1__tmpE.name );
#endif

              PHILOSOPHER1_eQ!PHILOSOPHER1__tmpE;
              insertWithDelay(PHILOSOPHER1_eQ);
            }
            skip;
          }
          :: else -> skip;
          fi
          if
          :: !PHILOSOPHER1_flags[USCXML_CTX_FINISHED] || PHILOSOPHER1_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
            {
              PHILOSOPHER1__tmpE.data.p_id = 0;
              PHILOSOPHER1__tmpE.delay = 0;
              PHILOSOPHER1__tmpE.invokeid = 0;
              PHILOSOPHER1__tmpE.name = 0;
              PHILOSOPHER1__tmpE.origin = 0;
              PHILOSOPHER1__tmpE.sendid = 0;
              PHILOSOPHER1__tmpE.seqNr = 0;
              PHILOSOPHER1__tmpE.name = RESEND_NEED_LEFT_FORK;
              PHILOSOPHER1__tmpE.invokeid = PHILOSOPHER1;
              PHILOSOPHER1__tmpE.origin = PHILOSOPHER1;
              _lastSeqId = _lastSeqId + 1;
              PHILOSOPHER1__tmpE.delay = 500;
              PHILOSOPHER1__tmpE.seqNr = _lastSeqId;
#if TRACE_EXECUTION
printf("%d: Sending RESEND_NEED_LEFT_FORK (%d) to PHILOSOPHER1_eQ\n", _pid, PHILOSOPHER1__tmpE.name );
#endif

              PHILOSOPHER1_eQ!PHILOSOPHER1__tmpE;
              insertWithDelay(PHILOSOPHER1_eQ);
            }
            skip;
          }
          :: else -> skip;
          fi
         }
         :: i == 6 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for entering state %d\n", _pid, i);
#endif

          printf("Eating philosopher: : %d", PHILOSOPHER1_p_id);
          if
          :: !PHILOSOPHER1_flags[USCXML_CTX_FINISHED] || PHILOSOPHER1_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
            {
              PHILOSOPHER1__tmpE.data.p_id = 0;
              PHILOSOPHER1__tmpE.delay = 0;
              PHILOSOPHER1__tmpE.invokeid = 0;
              PHILOSOPHER1__tmpE.name = 0;
              PHILOSOPHER1__tmpE.origin = 0;
              PHILOSOPHER1__tmpE.sendid = 0;
              PHILOSOPHER1__tmpE.seqNr = 0;
              PHILOSOPHER1__tmpE.name = EATING_OVER;
              PHILOSOPHER1__tmpE.invokeid = PHILOSOPHER1;
              PHILOSOPHER1__tmpE.origin = PHILOSOPHER1;
              _lastSeqId = _lastSeqId + 1;
              PHILOSOPHER1__tmpE.delay = PHILOSOPHER1_random_delay;
              PHILOSOPHER1__tmpE.seqNr = _lastSeqId;
#if TRACE_EXECUTION
printf("%d: Sending EATING_OVER (%d) to PHILOSOPHER1_eQ\n", _pid, PHILOSOPHER1__tmpE.name );
#endif

              PHILOSOPHER1_eQ!PHILOSOPHER1__tmpE;
              insertWithDelay(PHILOSOPHER1_eQ);
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
         :: j < PHILOSOPHER1_USCXML_NUMBER_TRANS -> {
           if
           :: (PHILOSOPHER1_ctx.trans_set[j] &&
              (PHILOSOPHER1_transitions[j].type[USCXML_TRANS_HISTORY] ||
               PHILOSOPHER1_transitions[j].type[USCXML_TRANS_INITIAL]) && 
               PHILOSOPHER1_states[PHILOSOPHER1_transitions[j].source].parent == i) -> {
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

                printf("philospher: : %d", PHILOSOPHER1_p_id);
                printf("starved in state hungry for Time(in ms) : : %d", PHILOSOPHER1_delay);
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
                :: !PHILOSOPHER1_flags[USCXML_CTX_FINISHED] || PHILOSOPHER1_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
                  {
                    PHILOSOPHER1__tmpE.data.p_id = 0;
                    PHILOSOPHER1__tmpE.delay = 0;
                    PHILOSOPHER1__tmpE.invokeid = 0;
                    PHILOSOPHER1__tmpE.name = 0;
                    PHILOSOPHER1__tmpE.origin = 0;
                    PHILOSOPHER1__tmpE.sendid = 0;
                    PHILOSOPHER1__tmpE.seqNr = 0;
                    PHILOSOPHER1__tmpE.name = NEED_RIGHT_FORK;
                    PHILOSOPHER1__tmpE.invokeid = PHILOSOPHER1;
                    PHILOSOPHER1__tmpE.origin = PHILOSOPHER1;
                    _lastSeqId = _lastSeqId + 1;
                    PHILOSOPHER1__tmpE.delay = 0;
                    PHILOSOPHER1__tmpE.seqNr = _lastSeqId;
                    PHILOSOPHER1__tmpE.data.p_id = PHILOSOPHER1_p_id;
#if TRACE_EXECUTION
printf("%d: Sending NEED_RIGHT_FORK (%d) to ROOT_eQ\n", _pid, PHILOSOPHER1__tmpE.name );
#endif

                    ROOT_eQ!PHILOSOPHER1__tmpE;
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

                printf("philospher: : %d", PHILOSOPHER1_p_id);
                printf("starved in state has_right_fork for Time(in ms) :: %d", PHILOSOPHER1_delay);
                skip;
              }
              :: j == 7 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, j);
#endif

                skip;
              }
              :: j == 8 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, j);
#endif

                if
                :: !PHILOSOPHER1_flags[USCXML_CTX_FINISHED] || PHILOSOPHER1_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
                  {
                    PHILOSOPHER1__tmpE.data.p_id = 0;
                    PHILOSOPHER1__tmpE.delay = 0;
                    PHILOSOPHER1__tmpE.invokeid = 0;
                    PHILOSOPHER1__tmpE.name = 0;
                    PHILOSOPHER1__tmpE.origin = 0;
                    PHILOSOPHER1__tmpE.sendid = 0;
                    PHILOSOPHER1__tmpE.seqNr = 0;
                    PHILOSOPHER1__tmpE.name = NEED_LEFT_FORK;
                    PHILOSOPHER1__tmpE.invokeid = PHILOSOPHER1;
                    PHILOSOPHER1__tmpE.origin = PHILOSOPHER1;
                    _lastSeqId = _lastSeqId + 1;
                    PHILOSOPHER1__tmpE.delay = 0;
                    PHILOSOPHER1__tmpE.seqNr = _lastSeqId;
                    PHILOSOPHER1__tmpE.data.p_id = PHILOSOPHER1_p_id;
#if TRACE_EXECUTION
printf("%d: Sending NEED_LEFT_FORK (%d) to ROOT_eQ\n", _pid, PHILOSOPHER1__tmpE.name );
#endif

                    ROOT_eQ!PHILOSOPHER1__tmpE;
                    insertWithDelay(ROOT_eQ);
                  }
                  skip;
                }
                :: else -> skip;
                fi
                skip;
              }
              :: j == 9 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, j);
#endif

                printf("philospher: : %d", PHILOSOPHER1_p_id);
                printf("starved in state has_right_fork for Time(in ms) : : %d", PHILOSOPHER1_delay);
                skip;
              }
              :: j == 10 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, j);
#endif

                if
                :: !PHILOSOPHER1_flags[USCXML_CTX_FINISHED] || PHILOSOPHER1_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
                  {
                    PHILOSOPHER1__tmpE.data.p_id = 0;
                    PHILOSOPHER1__tmpE.delay = 0;
                    PHILOSOPHER1__tmpE.invokeid = 0;
                    PHILOSOPHER1__tmpE.name = 0;
                    PHILOSOPHER1__tmpE.origin = 0;
                    PHILOSOPHER1__tmpE.sendid = 0;
                    PHILOSOPHER1__tmpE.seqNr = 0;
                    PHILOSOPHER1__tmpE.name = RETURN_FORKS;
                    PHILOSOPHER1__tmpE.invokeid = PHILOSOPHER1;
                    PHILOSOPHER1__tmpE.origin = PHILOSOPHER1;
                    _lastSeqId = _lastSeqId + 1;
                    PHILOSOPHER1__tmpE.delay = 0;
                    PHILOSOPHER1__tmpE.seqNr = _lastSeqId;
                    PHILOSOPHER1__tmpE.data.p_id = PHILOSOPHER1_p_id;
#if TRACE_EXECUTION
printf("%d: Sending RETURN_FORKS (%d) to ROOT_eQ\n", _pid, PHILOSOPHER1__tmpE.name );
#endif

                    ROOT_eQ!PHILOSOPHER1__tmpE;
                    insertWithDelay(ROOT_eQ);
                  }
                  skip;
                }
                :: else -> skip;
                fi
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
         :: PHILOSOPHER1_states[i].type[USCXML_STATE_FINAL] -> {
           if
           :: PHILOSOPHER1_states[PHILOSOPHER1_states[i].parent].children[1] -> {
             /* exit topmost SCXML state */
             PHILOSOPHER1_flags[USCXML_CTX_TOP_LEVEL_FINAL] = true;
             PHILOSOPHER1_flags[USCXML_CTX_FINISHED] = true;
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
            :: j < PHILOSOPHER1_USCXML_NUMBER_STATES -> {
              if
              :: PHILOSOPHER1_states[j].type[USCXML_STATE_PARALLEL] && PHILOSOPHER1_states[i].ancestors[j] -> {
                PHILOSOPHER1_STATES_CLEAR(PHILOSOPHER1_ctx.tmp_states)
                k = 0;
                do
                :: k < PHILOSOPHER1_USCXML_NUMBER_STATES -> {
                  if
                  :: PHILOSOPHER1_states[k].ancestors[j] && PHILOSOPHER1_config[k] -> {
                    if
                    :: PHILOSOPHER1_states[k].type[USCXML_STATE_FINAL] -> {
                      PHILOSOPHER1_STATES_AND_NOT(PHILOSOPHER1_ctx.tmp_states, PHILOSOPHER1_states[k].ancestors)
                    }
                    :: else -> {
                      PHILOSOPHER1_ctx.tmp_states[k] = true;
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
                :: !PHILOSOPHER1_STATES_HAS_ANY(PHILOSOPHER1_ctx.tmp_states) -> {
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
PHILOSOPHER1_TERMINATE_MACHINE:
skip; d_step {

#if TRACE_EXECUTION
printf("%d: Machine finished\n", _pid);
#endif

/* exit all remaining states */
i = PHILOSOPHER1_USCXML_NUMBER_STATES;
do
:: i > 0 -> {
  i = i - 1;
  if
  :: PHILOSOPHER1_config[i] && PHILOSOPHER1_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
    /* call all on exit handlers */
   if
    :: i == 3 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for exiting state %d\n", _pid, i);
#endif

    if
    :: (PHILOSOPHER1__event.name == TAKE_LEFT_FORK || PHILOSOPHER1__event.name == TAKE_RIGHT_FORK) -> {
        cancelSendId(STARVATION_TIMER,PHILOSOPHER1);
    }
    :: else -> skip;
    fi;
    }
    :: i == 4 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for exiting state %d\n", _pid, i);
#endif

    if
    :: (PHILOSOPHER1__event.name == TAKE_RIGHT_FORK) -> {
        cancelSendId(STARVATION_TIMER,PHILOSOPHER1);
    }
    :: else -> skip;
    fi;
    }
    :: i == 5 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for exiting state %d\n", _pid, i);
#endif

    if
    :: (PHILOSOPHER1__event.name == TAKE_LEFT_FORK) -> {
        cancelSendId(STARVATION_TIMER,PHILOSOPHER1);
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
  :: PHILOSOPHER1_invocations[i] -> {
    /* cancel invocations */
    PHILOSOPHER1_invocations[i] = false;
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

removePendingEventsFromInvoker(PHILOSOPHER1)
/* send done event */
if
:: PHILOSOPHER1_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
    PHILOSOPHER1__tmpE.data.p_id = 0;
    PHILOSOPHER1__tmpE.delay = 0;
    PHILOSOPHER1__tmpE.invokeid = 0;
    PHILOSOPHER1__tmpE.name = 0;
    PHILOSOPHER1__tmpE.origin = 0;
    PHILOSOPHER1__tmpE.sendid = 0;
    PHILOSOPHER1__tmpE.seqNr = 0;

    PHILOSOPHER1__tmpE.name = DONE_INVOKE_PHILOSOPHER1
    PHILOSOPHER1__tmpE.invokeid = PHILOSOPHER1

#if TRACE_EXECUTION
printf("%d: Sending DONE.INVOKE\n", _pid);
#endif

    ROOT_eQ!PHILOSOPHER1__tmpE;
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
#define PHILOSOPHER2_USCXML_NUMBER_STATES 8
#define PHILOSOPHER2_USCXML_NUMBER_TRANS 11

proctype PHILOSOPHER2_step() { atomic {

PHILOSOPHER2_procid = _pid;
unsigned i : 4,  j : 4,  k : 4;


/* ---------------------------- */
PHILOSOPHER2_MICROSTEP:
do
:: !PHILOSOPHER2_flags[USCXML_CTX_FINISHED] -> {
  /* Run until machine is finished */


#if TRACE_EXECUTION
printf("%d: Taking a step\n", _pid);
#endif

  /* Dequeue an event */
  PHILOSOPHER2_flags[USCXML_CTX_DEQUEUE_EXTERNAL] = false;
  if
  ::PHILOSOPHER2_flags[USCXML_CTX_SPONTANEOUS] -> {
    PHILOSOPHER2__event.name = USCXML_EVENT_SPONTANEOUS;

#if TRACE_EXECUTION
printf("%d: Trying with a spontaneous event\n", _pid);
#endif

  }
  :: else -> {
    if
    :: len(PHILOSOPHER2_iQ) != 0 -> {
      PHILOSOPHER2_iQ ? PHILOSOPHER2__event;

#if TRACE_EXECUTION
printf("%d: Deqeued an internal event\n", _pid);
#endif

    }
    :: else -> {
      PHILOSOPHER2_flags[USCXML_CTX_DEQUEUE_EXTERNAL] = true;
    }
    fi;
  }
  fi;


  if
  :: PHILOSOPHER2_flags[USCXML_CTX_DEQUEUE_EXTERNAL] -> {
    /* manage invocations */
    i = 0;
    do
    :: i < PHILOSOPHER2_USCXML_NUMBER_STATES -> {
      d_step { 
      /* uninvoke */
      if
      :: !PHILOSOPHER2_config[i] && PHILOSOPHER2_invocations[i] -> {

#if TRACE_EXECUTION
printf("%d: Uninvoking in state %d\n", _pid, i);
#endif

        if
        :: else -> skip;
        fi
        PHILOSOPHER2_invocations[i] = false;
        skip;
      }
      :: else -> skip;
      fi;
      } /* d_step */

      /* invoke */
      if
      :: PHILOSOPHER2_config[i] && !PHILOSOPHER2_invocations[i] -> {
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
    :: PHILOSOPHER2_flags[USCXML_CTX_FINISHED] -> {
      goto PHILOSOPHER2_TERMINATE_MACHINE;
    }
    :: else -> skip;
    fi
    /* Not sure if this should be before the invocation due to auto-forwarding */
    if
    :: len(PHILOSOPHER2_eQ) != 0 -> {
      PHILOSOPHER2_eQ ? PHILOSOPHER2__event;

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
PHILOSOPHER2_SELECT_TRANSITIONS:
PHILOSOPHER2_STATES_CLEAR(PHILOSOPHER2_ctx.target_set)
PHILOSOPHER2_STATES_CLEAR(PHILOSOPHER2_ctx.exit_set)
PHILOSOPHER2_TRANS_CLEAR(PHILOSOPHER2_ctx.conflicts)
PHILOSOPHER2_TRANS_CLEAR(PHILOSOPHER2_ctx.trans_set)
#if TRACE_EXECUTION
printf("%d: Establishing optimal transition set for event %d\n", _pid, PHILOSOPHER2__event.name );
#endif

#if TRACE_EXECUTION
printf("Configuration: ");
printf("%d%d%d%d%d%d%d%d", 
    PHILOSOPHER2_config[0], 
    PHILOSOPHER2_config[1], 
    PHILOSOPHER2_config[2], 
    PHILOSOPHER2_config[3], 
    PHILOSOPHER2_config[4], 
    PHILOSOPHER2_config[5], 
    PHILOSOPHER2_config[6], 
    PHILOSOPHER2_config[7]);
printf("\n");
#endif

  PHILOSOPHER2_flags[USCXML_CTX_TRANSITION_FOUND] = false;
  i = 0;
  do
  :: i < PHILOSOPHER2_USCXML_NUMBER_TRANS -> {
    /* only select non-history, non-initial transitions */
    if
    :: !PHILOSOPHER2_transitions[i].type[USCXML_TRANS_HISTORY] &&
       !PHILOSOPHER2_transitions[i].type[USCXML_TRANS_INITIAL] -> {
      if
      :: /* is the transition active? */
         PHILOSOPHER2_config[PHILOSOPHER2_transitions[i].source] && 

         /* is it non-conflicting? */
         !PHILOSOPHER2_ctx.conflicts[i] && 

         /* is it spontaneous with an event or vice versa? */
         ((PHILOSOPHER2__event.name == USCXML_EVENT_SPONTANEOUS && 
           PHILOSOPHER2_transitions[i].type[USCXML_TRANS_SPONTANEOUS]) || 
          (PHILOSOPHER2__event.name != USCXML_EVENT_SPONTANEOUS && 
           !PHILOSOPHER2_transitions[i].type[USCXML_TRANS_SPONTANEOUS])) &&

         /* is it matching and enabled? */
         (false 
          || (i == 0 && (false || PHILOSOPHER2__event.name == THINKING_OVER))
          || (i == 1 && (false || PHILOSOPHER2__event.name == TAKE_LEFT_FORK))
          || (i == 2 && (false || PHILOSOPHER2__event.name == TAKE_RIGHT_FORK))
          || (i == 3 && (false || PHILOSOPHER2__event.name == TIMEOUT))
          || (i == 4 && (false || PHILOSOPHER2__event.name == TAKE_RIGHT_FORK))
          || (i == 5 && (false || PHILOSOPHER2__event.name == RESEND_NEED_RIGHT_FORK))
          || (i == 6 && (false || PHILOSOPHER2__event.name == TIMEOUT))
          || (i == 7 && (false || PHILOSOPHER2__event.name == TAKE_LEFT_FORK))
          || (i == 8 && (false || PHILOSOPHER2__event.name == RESEND_NEED_LEFT_FORK))
          || (i == 9 && (false || PHILOSOPHER2__event.name == TIMEOUT))
          || (i == 10 && (false || PHILOSOPHER2__event.name == EATING_OVER))
         ) -> {
        /* remember that we found a transition */
        PHILOSOPHER2_flags[USCXML_CTX_TRANSITION_FOUND] = true;

        /* transitions that are pre-empted */
        PHILOSOPHER2_TRANS_OR(PHILOSOPHER2_ctx.conflicts, PHILOSOPHER2_transitions[i].conflicts)

        /* states that are directly targeted (resolve as entry-set later) */
        PHILOSOPHER2_STATES_OR(PHILOSOPHER2_ctx.target_set, PHILOSOPHER2_transitions[i].target)

        /* states that will be left */
        PHILOSOPHER2_STATES_OR(PHILOSOPHER2_ctx.exit_set, PHILOSOPHER2_transitions[i].exit_set)

        PHILOSOPHER2_ctx.trans_set[i] = true;
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
  PHILOSOPHER2_STATES_AND(PHILOSOPHER2_ctx.exit_set, PHILOSOPHER2_config)

#if TRACE_EXECUTION
printf("Selected Transitions: ");
printf("%d%d%d%d%d%d%d%d%d%d%d", 
    PHILOSOPHER2_ctx.trans_set[0], 
    PHILOSOPHER2_ctx.trans_set[1], 
    PHILOSOPHER2_ctx.trans_set[2], 
    PHILOSOPHER2_ctx.trans_set[3], 
    PHILOSOPHER2_ctx.trans_set[4], 
    PHILOSOPHER2_ctx.trans_set[5], 
    PHILOSOPHER2_ctx.trans_set[6], 
    PHILOSOPHER2_ctx.trans_set[7], 
    PHILOSOPHER2_ctx.trans_set[8], 
    PHILOSOPHER2_ctx.trans_set[9], 
    PHILOSOPHER2_ctx.trans_set[10]);
printf("\n");
#endif


#if TRACE_EXECUTION
printf("Target Set: ");
printf("%d%d%d%d%d%d%d%d", 
    PHILOSOPHER2_ctx.target_set[0], 
    PHILOSOPHER2_ctx.target_set[1], 
    PHILOSOPHER2_ctx.target_set[2], 
    PHILOSOPHER2_ctx.target_set[3], 
    PHILOSOPHER2_ctx.target_set[4], 
    PHILOSOPHER2_ctx.target_set[5], 
    PHILOSOPHER2_ctx.target_set[6], 
    PHILOSOPHER2_ctx.target_set[7]);
printf("\n");
#endif


#if TRACE_EXECUTION
printf("Exit Set: ");
printf("%d%d%d%d%d%d%d%d", 
    PHILOSOPHER2_ctx.exit_set[0], 
    PHILOSOPHER2_ctx.exit_set[1], 
    PHILOSOPHER2_ctx.exit_set[2], 
    PHILOSOPHER2_ctx.exit_set[3], 
    PHILOSOPHER2_ctx.exit_set[4], 
    PHILOSOPHER2_ctx.exit_set[5], 
    PHILOSOPHER2_ctx.exit_set[6], 
    PHILOSOPHER2_ctx.exit_set[7]);
printf("\n");
#endif

  if
  :: !PHILOSOPHER2_STATES_HAS_ANY(PHILOSOPHER2_config) -> {
    /* Enter initial configuration */
    PHILOSOPHER2_STATES_COPY(PHILOSOPHER2_ctx.target_set, PHILOSOPHER2_states[0].completion)
    PHILOSOPHER2_flags[USCXML_CTX_SPONTANEOUS] = true;
    PHILOSOPHER2_flags[USCXML_CTX_TRANSITION_FOUND] = true;

#if TRACE_EXECUTION
printf("%d: Entering initial default completion\n", _pid);
#endif


  }
  :: PHILOSOPHER2_flags[USCXML_CTX_TRANSITION_FOUND] -> {

#if TRACE_EXECUTION
printf("%d: Found transitions\n", _pid);
#endif

    PHILOSOPHER2_flags[USCXML_CTX_SPONTANEOUS] = true;
  }
  :: else {
    PHILOSOPHER2_flags[USCXML_CTX_SPONTANEOUS] = false;

#if TRACE_EXECUTION
printf("%d: Found NO transitions\n", _pid);
#endif

  }
  fi


  if
  :: PHILOSOPHER2_flags[USCXML_CTX_TRANSITION_FOUND] -> {
    /* only process anything if we found transitions or are on initial entry */
/* ---------------------------- */
/* REMEMBER_HISTORY: */

#if TRACE_EXECUTION
printf("%d: Save history configurations\n", _pid);
#endif

  if
  :: PHILOSOPHER2_STATES_HAS_ANY(PHILOSOPHER2_config) -> {
    /* only remember history on non-initial entry */
    i = 0;
    do
    :: i < PHILOSOPHER2_USCXML_NUMBER_STATES -> {
      if
      :: PHILOSOPHER2_states[i].type[USCXML_STATE_HISTORY_SHALLOW] ||
         PHILOSOPHER2_states[i].type[USCXML_STATE_HISTORY_DEEP] -> {
        if
        :: PHILOSOPHER2_ctx.exit_set[PHILOSOPHER2_states[i].parent] -> {
          /* a history state whose parent is about to be exited */

#if TRACE_EXECUTION
printf("%d: history state %d is about to be exited\n", _pid, i);
#endif


#if TRACE_EXECUTION
printf("COMPLET: ");
printf("%d%d%d%d%d%d%d%d", 
    PHILOSOPHER2_states[i].completion[0], 
    PHILOSOPHER2_states[i].completion[1], 
    PHILOSOPHER2_states[i].completion[2], 
    PHILOSOPHER2_states[i].completion[3], 
    PHILOSOPHER2_states[i].completion[4], 
    PHILOSOPHER2_states[i].completion[5], 
    PHILOSOPHER2_states[i].completion[6], 
    PHILOSOPHER2_states[i].completion[7]);
printf("\n");
#endif

          PHILOSOPHER2_STATES_COPY(PHILOSOPHER2_ctx.tmp_states, PHILOSOPHER2_states[i].completion)

          /* set those states who were enabled */
          PHILOSOPHER2_STATES_AND(PHILOSOPHER2_ctx.tmp_states, PHILOSOPHER2_config)

#if TRACE_EXECUTION
printf("CONFIG : ");
printf("%d%d%d%d%d%d%d%d", 
    PHILOSOPHER2_config[0], 
    PHILOSOPHER2_config[1], 
    PHILOSOPHER2_config[2], 
    PHILOSOPHER2_config[3], 
    PHILOSOPHER2_config[4], 
    PHILOSOPHER2_config[5], 
    PHILOSOPHER2_config[6], 
    PHILOSOPHER2_config[7]);
printf("\n");
#endif


#if TRACE_EXECUTION
printf("TMP_STS: ");
printf("%d%d%d%d%d%d%d%d", 
    PHILOSOPHER2_ctx.tmp_states[0], 
    PHILOSOPHER2_ctx.tmp_states[1], 
    PHILOSOPHER2_ctx.tmp_states[2], 
    PHILOSOPHER2_ctx.tmp_states[3], 
    PHILOSOPHER2_ctx.tmp_states[4], 
    PHILOSOPHER2_ctx.tmp_states[5], 
    PHILOSOPHER2_ctx.tmp_states[6], 
    PHILOSOPHER2_ctx.tmp_states[7]);
printf("\n");
#endif


          /* clear current history with completion mask */
          PHILOSOPHER2_STATES_AND_NOT(PHILOSOPHER2_history, PHILOSOPHER2_states[i].completion)

          /* set history */
          PHILOSOPHER2_STATES_OR(PHILOSOPHER2_history, PHILOSOPHER2_ctx.tmp_states)

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
printf("%d%d%d%d%d%d%d%d", 
    PHILOSOPHER2_history[0], 
    PHILOSOPHER2_history[1], 
    PHILOSOPHER2_history[2], 
    PHILOSOPHER2_history[3], 
    PHILOSOPHER2_history[4], 
    PHILOSOPHER2_history[5], 
    PHILOSOPHER2_history[6], 
    PHILOSOPHER2_history[7]);
printf("\n");
#endif
  }
  :: else -> skip;
  fi;

/* ---------------------------- */
PHILOSOPHER2_ESTABLISH_ENTRY_SET:
  /* calculate new entry set */
  PHILOSOPHER2_STATES_COPY(PHILOSOPHER2_ctx.entry_set, PHILOSOPHER2_ctx.target_set)

  i = 0;
  do
  :: i < PHILOSOPHER2_USCXML_NUMBER_STATES -> {
    if
    :: PHILOSOPHER2_ctx.entry_set[i] -> {
      /* ancestor completion */
      PHILOSOPHER2_STATES_OR(PHILOSOPHER2_ctx.entry_set, PHILOSOPHER2_states[i].ancestors)
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
  :: i < PHILOSOPHER2_USCXML_NUMBER_STATES -> {
    if
    :: PHILOSOPHER2_ctx.entry_set[i] -> {
      if
      :: PHILOSOPHER2_states[i].type[USCXML_STATE_PARALLEL] -> {
        PHILOSOPHER2_STATES_OR(PHILOSOPHER2_ctx.entry_set, PHILOSOPHER2_states[i].completion)
      }
      :: PHILOSOPHER2_states[i].type[USCXML_STATE_HISTORY_SHALLOW] ||
         PHILOSOPHER2_states[i].type[USCXML_STATE_HISTORY_DEEP] -> {

#if TRACE_EXECUTION
printf("%d: Descendant completion for history state %d\n", _pid, i);
#endif

        if
        :: !PHILOSOPHER2_STATES_HAS_AND(PHILOSOPHER2_states[i].completion, PHILOSOPHER2_history) && !PHILOSOPHER2_config[PHILOSOPHER2_states[i].parent] -> {
          /* nothing set for history, look for a default transition */

#if TRACE_EXECUTION
printf("%d: Fresh history in target set\n", _pid);
#endif

          j = 0;
          do
          :: j < PHILOSOPHER2_USCXML_NUMBER_TRANS -> {
             if
             :: PHILOSOPHER2_transitions[j].source == i -> {
               PHILOSOPHER2_ctx.trans_set[j] = true;
               PHILOSOPHER2_STATES_OR(PHILOSOPHER2_ctx.entry_set, PHILOSOPHER2_transitions[j].target)

               if
               :: (PHILOSOPHER2_states[i].type[USCXML_STATE_HISTORY_DEEP] &&
                   !PHILOSOPHER2_STATES_HAS_AND(PHILOSOPHER2_transitions[j].target, PHILOSOPHER2_states[i].children)                  ) -> {
                 k = i + 1
                 do
                 :: k < PHILOSOPHER2_USCXML_NUMBER_STATES -> {
                   if
                   :: PHILOSOPHER2_transitions[j].target[k] -> {
                     PHILOSOPHER2_STATES_OR(PHILOSOPHER2_ctx.entry_set, PHILOSOPHER2_states[k].ancestors)
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

          PHILOSOPHER2_STATES_COPY(PHILOSOPHER2_ctx.tmp_states, PHILOSOPHER2_states[i].completion)
          PHILOSOPHER2_STATES_AND(PHILOSOPHER2_ctx.tmp_states, PHILOSOPHER2_history)
          PHILOSOPHER2_STATES_OR(PHILOSOPHER2_ctx.entry_set, PHILOSOPHER2_ctx.tmp_states)
          if
          :: PHILOSOPHER2_states[i].type[USCXML_STATE_HAS_HISTORY] ||
             PHILOSOPHER2_states[i].type[USCXML_STATE_HISTORY_DEEP] -> { 
            /* a deep history state with nested histories -> more completion */

#if TRACE_EXECUTION
printf("%d: DEEP HISTORY\n", _pid);
#endif

            j = i + 1;
            do
            :: j < PHILOSOPHER2_USCXML_NUMBER_STATES -> {
              if
              :: (PHILOSOPHER2_states[i].completion[j] &&
                  PHILOSOPHER2_ctx.entry_set[j] && 
                  PHILOSOPHER2_states[j].type[USCXML_STATE_HAS_HISTORY]) -> {
                k = j + 1;
                do
                :: k < PHILOSOPHER2_USCXML_NUMBER_STATES -> {
                  /* add nested history to entry_set */
                  if
                  :: (PHILOSOPHER2_states[k].type[USCXML_STATE_HISTORY_DEEP] ||
                      PHILOSOPHER2_states[k].type[USCXML_STATE_HISTORY_SHALLOW]) &&
                     PHILOSOPHER2_states[j].children[k] -> {
                    /* a nested history state */
                    PHILOSOPHER2_ctx.entry_set[k] = true;
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
      :: PHILOSOPHER2_states[i].type[USCXML_STATE_INITIAL] -> {

#if TRACE_EXECUTION
printf("%d: Descendant completion for initial state %d\n", _pid, i);
#endif

        j = 0
        do
        :: j < PHILOSOPHER2_USCXML_NUMBER_TRANS -> {
          if
          :: PHILOSOPHER2_transitions[j].source == i -> {
            PHILOSOPHER2_ctx.trans_set[j] = true;
            PHILOSOPHER2_ctx.entry_set[i] = false;

#if TRACE_EXECUTION
printf("%d: Adding transition %d!\n", _pid, j);
#endif

            PHILOSOPHER2_STATES_OR(PHILOSOPHER2_ctx.entry_set, PHILOSOPHER2_transitions[j].target)

            k = i + 1;
            do
            :: k < PHILOSOPHER2_USCXML_NUMBER_STATES -> {
              if
              :: PHILOSOPHER2_transitions[j].target[k] -> {
                PHILOSOPHER2_STATES_OR(PHILOSOPHER2_ctx.entry_set, PHILOSOPHER2_states[k].ancestors)

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
      :: PHILOSOPHER2_states[i].type[USCXML_STATE_COMPOUND] -> {
        /* we need to check whether one child is already in entry_set */
        if
        :: (
          !PHILOSOPHER2_STATES_HAS_AND(PHILOSOPHER2_ctx.entry_set, PHILOSOPHER2_states[i].children) && 
           (!PHILOSOPHER2_STATES_HAS_AND(PHILOSOPHER2_config, PHILOSOPHER2_states[i].children) || PHILOSOPHER2_STATES_HAS_AND(PHILOSOPHER2_ctx.exit_set, PHILOSOPHER2_states[i].children)
)) 
        -> {
          PHILOSOPHER2_STATES_OR(PHILOSOPHER2_ctx.entry_set, PHILOSOPHER2_states[i].completion)
          if
          :: (PHILOSOPHER2_STATES_HAS_AND(PHILOSOPHER2_states[i].completion, PHILOSOPHER2_states[i].children)
          ) -> {
            /* deep completion */
            j = i + 1;
            do
            :: j < PHILOSOPHER2_USCXML_NUMBER_STATES - 1 -> {
              j = j + 1;
              if
              :: PHILOSOPHER2_states[i].completion[j] -> {
                PHILOSOPHER2_STATES_OR(PHILOSOPHER2_ctx.entry_set, PHILOSOPHER2_states[j].ancestors)

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
printf("%d%d%d%d%d%d%d%d", 
    PHILOSOPHER2_ctx.entry_set[0], 
    PHILOSOPHER2_ctx.entry_set[1], 
    PHILOSOPHER2_ctx.entry_set[2], 
    PHILOSOPHER2_ctx.entry_set[3], 
    PHILOSOPHER2_ctx.entry_set[4], 
    PHILOSOPHER2_ctx.entry_set[5], 
    PHILOSOPHER2_ctx.entry_set[6], 
    PHILOSOPHER2_ctx.entry_set[7]);
printf("\n");
#endif


/* ---------------------------- */
/* EXIT_STATES: */
  i = PHILOSOPHER2_USCXML_NUMBER_STATES;
  do
  :: i > 0 -> {
    i = i - 1;
    if
    :: PHILOSOPHER2_ctx.exit_set[i] && PHILOSOPHER2_config[i] -> {
      /* call all on-exit handlers */

#if TRACE_EXECUTION
printf("%d: Exiting state %d\n", _pid, i);
#endif

      if
      :: i == 3 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for exiting state %d\n", _pid, i);
#endif

      if
      :: (PHILOSOPHER2__event.name == TAKE_LEFT_FORK || PHILOSOPHER2__event.name == TAKE_RIGHT_FORK) -> {
          cancelSendId(STARVATION_TIMER,PHILOSOPHER2);
      }
      :: else -> skip;
      fi;
      }
      :: i == 4 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for exiting state %d\n", _pid, i);
#endif

      if
      :: (PHILOSOPHER2__event.name == TAKE_RIGHT_FORK) -> {
          cancelSendId(STARVATION_TIMER,PHILOSOPHER2);
      }
      :: else -> skip;
      fi;
      }
      :: i == 5 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for exiting state %d\n", _pid, i);
#endif

      if
      :: (PHILOSOPHER2__event.name == TAKE_LEFT_FORK) -> {
          cancelSendId(STARVATION_TIMER,PHILOSOPHER2);
      }
      :: else -> skip;
      fi;
      }
      :: else -> skip;
      fi

      PHILOSOPHER2_config[i] = false;
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
  :: i < PHILOSOPHER2_USCXML_NUMBER_TRANS -> {
    if
    :: PHILOSOPHER2_ctx.trans_set[i] && 
       !PHILOSOPHER2_transitions[i].type[USCXML_TRANS_HISTORY] && 
       !PHILOSOPHER2_transitions[i].type[USCXML_TRANS_INITIAL] -> {
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

        printf("philospher: : %d", PHILOSOPHER2_p_id);
        printf("starved in state hungry for Time(in ms) : : %d", PHILOSOPHER2_delay);
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
        :: !PHILOSOPHER2_flags[USCXML_CTX_FINISHED] || PHILOSOPHER2_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
          {
            PHILOSOPHER2__tmpE.data.p_id = 0;
            PHILOSOPHER2__tmpE.delay = 0;
            PHILOSOPHER2__tmpE.invokeid = 0;
            PHILOSOPHER2__tmpE.name = 0;
            PHILOSOPHER2__tmpE.origin = 0;
            PHILOSOPHER2__tmpE.sendid = 0;
            PHILOSOPHER2__tmpE.seqNr = 0;
            PHILOSOPHER2__tmpE.name = NEED_RIGHT_FORK;
            PHILOSOPHER2__tmpE.invokeid = PHILOSOPHER2;
            PHILOSOPHER2__tmpE.origin = PHILOSOPHER2;
            _lastSeqId = _lastSeqId + 1;
            PHILOSOPHER2__tmpE.delay = 0;
            PHILOSOPHER2__tmpE.seqNr = _lastSeqId;
            PHILOSOPHER2__tmpE.data.p_id = PHILOSOPHER2_p_id;
#if TRACE_EXECUTION
printf("%d: Sending NEED_RIGHT_FORK (%d) to ROOT_eQ\n", _pid, PHILOSOPHER2__tmpE.name );
#endif

            ROOT_eQ!PHILOSOPHER2__tmpE;
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

        printf("philospher: : %d", PHILOSOPHER2_p_id);
        printf("starved in state has_right_fork for Time(in ms) :: %d", PHILOSOPHER2_delay);
        skip;
      }
      :: i == 7 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, i);
#endif

        skip;
      }
      :: i == 8 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, i);
#endif

        if
        :: !PHILOSOPHER2_flags[USCXML_CTX_FINISHED] || PHILOSOPHER2_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
          {
            PHILOSOPHER2__tmpE.data.p_id = 0;
            PHILOSOPHER2__tmpE.delay = 0;
            PHILOSOPHER2__tmpE.invokeid = 0;
            PHILOSOPHER2__tmpE.name = 0;
            PHILOSOPHER2__tmpE.origin = 0;
            PHILOSOPHER2__tmpE.sendid = 0;
            PHILOSOPHER2__tmpE.seqNr = 0;
            PHILOSOPHER2__tmpE.name = NEED_LEFT_FORK;
            PHILOSOPHER2__tmpE.invokeid = PHILOSOPHER2;
            PHILOSOPHER2__tmpE.origin = PHILOSOPHER2;
            _lastSeqId = _lastSeqId + 1;
            PHILOSOPHER2__tmpE.delay = 0;
            PHILOSOPHER2__tmpE.seqNr = _lastSeqId;
            PHILOSOPHER2__tmpE.data.p_id = PHILOSOPHER2_p_id;
#if TRACE_EXECUTION
printf("%d: Sending NEED_LEFT_FORK (%d) to ROOT_eQ\n", _pid, PHILOSOPHER2__tmpE.name );
#endif

            ROOT_eQ!PHILOSOPHER2__tmpE;
            insertWithDelay(ROOT_eQ);
          }
          skip;
        }
        :: else -> skip;
        fi
        skip;
      }
      :: i == 9 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, i);
#endif

        printf("philospher: : %d", PHILOSOPHER2_p_id);
        printf("starved in state has_right_fork for Time(in ms) : : %d", PHILOSOPHER2_delay);
        skip;
      }
      :: i == 10 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, i);
#endif

        if
        :: !PHILOSOPHER2_flags[USCXML_CTX_FINISHED] || PHILOSOPHER2_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
          {
            PHILOSOPHER2__tmpE.data.p_id = 0;
            PHILOSOPHER2__tmpE.delay = 0;
            PHILOSOPHER2__tmpE.invokeid = 0;
            PHILOSOPHER2__tmpE.name = 0;
            PHILOSOPHER2__tmpE.origin = 0;
            PHILOSOPHER2__tmpE.sendid = 0;
            PHILOSOPHER2__tmpE.seqNr = 0;
            PHILOSOPHER2__tmpE.name = RETURN_FORKS;
            PHILOSOPHER2__tmpE.invokeid = PHILOSOPHER2;
            PHILOSOPHER2__tmpE.origin = PHILOSOPHER2;
            _lastSeqId = _lastSeqId + 1;
            PHILOSOPHER2__tmpE.delay = 0;
            PHILOSOPHER2__tmpE.seqNr = _lastSeqId;
            PHILOSOPHER2__tmpE.data.p_id = PHILOSOPHER2_p_id;
#if TRACE_EXECUTION
printf("%d: Sending RETURN_FORKS (%d) to ROOT_eQ\n", _pid, PHILOSOPHER2__tmpE.name );
#endif

            ROOT_eQ!PHILOSOPHER2__tmpE;
            insertWithDelay(ROOT_eQ);
          }
          skip;
        }
        :: else -> skip;
        fi
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
  :: i < PHILOSOPHER2_USCXML_NUMBER_STATES -> {
    if
    :: (PHILOSOPHER2_ctx.entry_set[i] &&
        !PHILOSOPHER2_config[i] && 
        /* these are no proper states */
        !PHILOSOPHER2_states[i].type[USCXML_STATE_HISTORY_DEEP] && 
        !PHILOSOPHER2_states[i].type[USCXML_STATE_HISTORY_SHALLOW] && 
        !PHILOSOPHER2_states[i].type[USCXML_STATE_INITIAL]
       ) -> {

#if TRACE_EXECUTION
printf("%d: Entering state %d\n", _pid, i);
#endif

         PHILOSOPHER2_config[i] = true;

         /* Process executable content for entering a state */
         if
         :: i == 1 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for entering state %d\n", _pid, i);
#endif

          printf("Hello, I am philospher number: : %d", PHILOSOPHER2_p_id);
         }
         :: i == 2 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for entering state %d\n", _pid, i);
#endif

          printf("Thinking philosopher: : %d", PHILOSOPHER2_p_id);
            PHILOSOPHER2_random_delay = ((1103515245*PHILOSOPHER2_random_delay+12345)%2147483647)%2000;
          if
          :: !PHILOSOPHER2_flags[USCXML_CTX_FINISHED] || PHILOSOPHER2_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
            {
              PHILOSOPHER2__tmpE.data.p_id = 0;
              PHILOSOPHER2__tmpE.delay = 0;
              PHILOSOPHER2__tmpE.invokeid = 0;
              PHILOSOPHER2__tmpE.name = 0;
              PHILOSOPHER2__tmpE.origin = 0;
              PHILOSOPHER2__tmpE.sendid = 0;
              PHILOSOPHER2__tmpE.seqNr = 0;
              PHILOSOPHER2__tmpE.name = THINKING_OVER;
              PHILOSOPHER2__tmpE.invokeid = PHILOSOPHER2;
              PHILOSOPHER2__tmpE.origin = PHILOSOPHER2;
              _lastSeqId = _lastSeqId + 1;
              PHILOSOPHER2__tmpE.delay = PHILOSOPHER2_random_delay*(PHILOSOPHER2_p_id+1);
              PHILOSOPHER2__tmpE.seqNr = _lastSeqId;
#if TRACE_EXECUTION
printf("%d: Sending THINKING_OVER (%d) to PHILOSOPHER2_eQ\n", _pid, PHILOSOPHER2__tmpE.name );
#endif

              PHILOSOPHER2_eQ!PHILOSOPHER2__tmpE;
              insertWithDelay(PHILOSOPHER2_eQ);
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

          printf("Hungry philosopher: : %d", PHILOSOPHER2_p_id);
          if
          :: !PHILOSOPHER2_flags[USCXML_CTX_FINISHED] || PHILOSOPHER2_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
            {
              PHILOSOPHER2__tmpE.data.p_id = 0;
              PHILOSOPHER2__tmpE.delay = 0;
              PHILOSOPHER2__tmpE.invokeid = 0;
              PHILOSOPHER2__tmpE.name = 0;
              PHILOSOPHER2__tmpE.origin = 0;
              PHILOSOPHER2__tmpE.sendid = 0;
              PHILOSOPHER2__tmpE.seqNr = 0;
              PHILOSOPHER2__tmpE.name = TIMEOUT;
              PHILOSOPHER2__tmpE.sendid = STARVATION_TIMER;
              PHILOSOPHER2__tmpE.invokeid = PHILOSOPHER2;
              PHILOSOPHER2__tmpE.origin = PHILOSOPHER2;
              _lastSeqId = _lastSeqId + 1;
              PHILOSOPHER2__tmpE.delay = PHILOSOPHER2_delay;
              PHILOSOPHER2__tmpE.seqNr = _lastSeqId;
#if TRACE_EXECUTION
printf("%d: Sending TIMEOUT (%d) to PHILOSOPHER2_eQ\n", _pid, PHILOSOPHER2__tmpE.name );
#endif

              PHILOSOPHER2_eQ!PHILOSOPHER2__tmpE;
              insertWithDelay(PHILOSOPHER2_eQ);
            }
            skip;
          }
          :: else -> skip;
          fi
          if
          :: !PHILOSOPHER2_flags[USCXML_CTX_FINISHED] || PHILOSOPHER2_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
            {
              PHILOSOPHER2__tmpE.data.p_id = 0;
              PHILOSOPHER2__tmpE.delay = 0;
              PHILOSOPHER2__tmpE.invokeid = 0;
              PHILOSOPHER2__tmpE.name = 0;
              PHILOSOPHER2__tmpE.origin = 0;
              PHILOSOPHER2__tmpE.sendid = 0;
              PHILOSOPHER2__tmpE.seqNr = 0;
              PHILOSOPHER2__tmpE.name = NEED_LEFT_FORK;
              PHILOSOPHER2__tmpE.invokeid = PHILOSOPHER2;
              PHILOSOPHER2__tmpE.origin = PHILOSOPHER2;
              _lastSeqId = _lastSeqId + 1;
              PHILOSOPHER2__tmpE.delay = 0;
              PHILOSOPHER2__tmpE.seqNr = _lastSeqId;
              PHILOSOPHER2__tmpE.data.p_id = PHILOSOPHER2_p_id;
#if TRACE_EXECUTION
printf("%d: Sending NEED_LEFT_FORK (%d) to ROOT_eQ\n", _pid, PHILOSOPHER2__tmpE.name );
#endif

              ROOT_eQ!PHILOSOPHER2__tmpE;
              insertWithDelay(ROOT_eQ);
            }
            skip;
          }
          :: else -> skip;
          fi
          if
          :: !PHILOSOPHER2_flags[USCXML_CTX_FINISHED] || PHILOSOPHER2_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
            {
              PHILOSOPHER2__tmpE.data.p_id = 0;
              PHILOSOPHER2__tmpE.delay = 0;
              PHILOSOPHER2__tmpE.invokeid = 0;
              PHILOSOPHER2__tmpE.name = 0;
              PHILOSOPHER2__tmpE.origin = 0;
              PHILOSOPHER2__tmpE.sendid = 0;
              PHILOSOPHER2__tmpE.seqNr = 0;
              PHILOSOPHER2__tmpE.name = NEED_RIGHT_FORK;
              PHILOSOPHER2__tmpE.invokeid = PHILOSOPHER2;
              PHILOSOPHER2__tmpE.origin = PHILOSOPHER2;
              _lastSeqId = _lastSeqId + 1;
              PHILOSOPHER2__tmpE.delay = 0;
              PHILOSOPHER2__tmpE.seqNr = _lastSeqId;
              PHILOSOPHER2__tmpE.data.p_id = PHILOSOPHER2_p_id;
#if TRACE_EXECUTION
printf("%d: Sending NEED_RIGHT_FORK (%d) to ROOT_eQ\n", _pid, PHILOSOPHER2__tmpE.name );
#endif

              ROOT_eQ!PHILOSOPHER2__tmpE;
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

          printf("in state has_left_fork for philosopher: : %d", PHILOSOPHER2_p_id);
          if
          :: !PHILOSOPHER2_flags[USCXML_CTX_FINISHED] || PHILOSOPHER2_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
            {
              PHILOSOPHER2__tmpE.data.p_id = 0;
              PHILOSOPHER2__tmpE.delay = 0;
              PHILOSOPHER2__tmpE.invokeid = 0;
              PHILOSOPHER2__tmpE.name = 0;
              PHILOSOPHER2__tmpE.origin = 0;
              PHILOSOPHER2__tmpE.sendid = 0;
              PHILOSOPHER2__tmpE.seqNr = 0;
              PHILOSOPHER2__tmpE.name = TIMEOUT;
              PHILOSOPHER2__tmpE.sendid = STARVATION_TIMER;
              PHILOSOPHER2__tmpE.invokeid = PHILOSOPHER2;
              PHILOSOPHER2__tmpE.origin = PHILOSOPHER2;
              _lastSeqId = _lastSeqId + 1;
              PHILOSOPHER2__tmpE.delay = PHILOSOPHER2_delay;
              PHILOSOPHER2__tmpE.seqNr = _lastSeqId;
#if TRACE_EXECUTION
printf("%d: Sending TIMEOUT (%d) to PHILOSOPHER2_eQ\n", _pid, PHILOSOPHER2__tmpE.name );
#endif

              PHILOSOPHER2_eQ!PHILOSOPHER2__tmpE;
              insertWithDelay(PHILOSOPHER2_eQ);
            }
            skip;
          }
          :: else -> skip;
          fi
          if
          :: !PHILOSOPHER2_flags[USCXML_CTX_FINISHED] || PHILOSOPHER2_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
            {
              PHILOSOPHER2__tmpE.data.p_id = 0;
              PHILOSOPHER2__tmpE.delay = 0;
              PHILOSOPHER2__tmpE.invokeid = 0;
              PHILOSOPHER2__tmpE.name = 0;
              PHILOSOPHER2__tmpE.origin = 0;
              PHILOSOPHER2__tmpE.sendid = 0;
              PHILOSOPHER2__tmpE.seqNr = 0;
              PHILOSOPHER2__tmpE.name = RESEND_NEED_RIGHT_FORK;
              PHILOSOPHER2__tmpE.invokeid = PHILOSOPHER2;
              PHILOSOPHER2__tmpE.origin = PHILOSOPHER2;
              _lastSeqId = _lastSeqId + 1;
              PHILOSOPHER2__tmpE.delay = 500;
              PHILOSOPHER2__tmpE.seqNr = _lastSeqId;
#if TRACE_EXECUTION
printf("%d: Sending RESEND_NEED_RIGHT_FORK (%d) to PHILOSOPHER2_eQ\n", _pid, PHILOSOPHER2__tmpE.name );
#endif

              PHILOSOPHER2_eQ!PHILOSOPHER2__tmpE;
              insertWithDelay(PHILOSOPHER2_eQ);
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

          printf("in state has_right_fork for philosopher: : %d", PHILOSOPHER2_p_id);
          if
          :: !PHILOSOPHER2_flags[USCXML_CTX_FINISHED] || PHILOSOPHER2_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
            {
              PHILOSOPHER2__tmpE.data.p_id = 0;
              PHILOSOPHER2__tmpE.delay = 0;
              PHILOSOPHER2__tmpE.invokeid = 0;
              PHILOSOPHER2__tmpE.name = 0;
              PHILOSOPHER2__tmpE.origin = 0;
              PHILOSOPHER2__tmpE.sendid = 0;
              PHILOSOPHER2__tmpE.seqNr = 0;
              PHILOSOPHER2__tmpE.name = TIMEOUT;
              PHILOSOPHER2__tmpE.sendid = STARVATION_TIMER;
              PHILOSOPHER2__tmpE.invokeid = PHILOSOPHER2;
              PHILOSOPHER2__tmpE.origin = PHILOSOPHER2;
              _lastSeqId = _lastSeqId + 1;
              PHILOSOPHER2__tmpE.delay = PHILOSOPHER2_delay;
              PHILOSOPHER2__tmpE.seqNr = _lastSeqId;
#if TRACE_EXECUTION
printf("%d: Sending TIMEOUT (%d) to PHILOSOPHER2_eQ\n", _pid, PHILOSOPHER2__tmpE.name );
#endif

              PHILOSOPHER2_eQ!PHILOSOPHER2__tmpE;
              insertWithDelay(PHILOSOPHER2_eQ);
            }
            skip;
          }
          :: else -> skip;
          fi
          if
          :: !PHILOSOPHER2_flags[USCXML_CTX_FINISHED] || PHILOSOPHER2_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
            {
              PHILOSOPHER2__tmpE.data.p_id = 0;
              PHILOSOPHER2__tmpE.delay = 0;
              PHILOSOPHER2__tmpE.invokeid = 0;
              PHILOSOPHER2__tmpE.name = 0;
              PHILOSOPHER2__tmpE.origin = 0;
              PHILOSOPHER2__tmpE.sendid = 0;
              PHILOSOPHER2__tmpE.seqNr = 0;
              PHILOSOPHER2__tmpE.name = RESEND_NEED_LEFT_FORK;
              PHILOSOPHER2__tmpE.invokeid = PHILOSOPHER2;
              PHILOSOPHER2__tmpE.origin = PHILOSOPHER2;
              _lastSeqId = _lastSeqId + 1;
              PHILOSOPHER2__tmpE.delay = 500;
              PHILOSOPHER2__tmpE.seqNr = _lastSeqId;
#if TRACE_EXECUTION
printf("%d: Sending RESEND_NEED_LEFT_FORK (%d) to PHILOSOPHER2_eQ\n", _pid, PHILOSOPHER2__tmpE.name );
#endif

              PHILOSOPHER2_eQ!PHILOSOPHER2__tmpE;
              insertWithDelay(PHILOSOPHER2_eQ);
            }
            skip;
          }
          :: else -> skip;
          fi
         }
         :: i == 6 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for entering state %d\n", _pid, i);
#endif

          printf("Eating philosopher: : %d", PHILOSOPHER2_p_id);
          if
          :: !PHILOSOPHER2_flags[USCXML_CTX_FINISHED] || PHILOSOPHER2_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
            {
              PHILOSOPHER2__tmpE.data.p_id = 0;
              PHILOSOPHER2__tmpE.delay = 0;
              PHILOSOPHER2__tmpE.invokeid = 0;
              PHILOSOPHER2__tmpE.name = 0;
              PHILOSOPHER2__tmpE.origin = 0;
              PHILOSOPHER2__tmpE.sendid = 0;
              PHILOSOPHER2__tmpE.seqNr = 0;
              PHILOSOPHER2__tmpE.name = EATING_OVER;
              PHILOSOPHER2__tmpE.invokeid = PHILOSOPHER2;
              PHILOSOPHER2__tmpE.origin = PHILOSOPHER2;
              _lastSeqId = _lastSeqId + 1;
              PHILOSOPHER2__tmpE.delay = PHILOSOPHER2_random_delay;
              PHILOSOPHER2__tmpE.seqNr = _lastSeqId;
#if TRACE_EXECUTION
printf("%d: Sending EATING_OVER (%d) to PHILOSOPHER2_eQ\n", _pid, PHILOSOPHER2__tmpE.name );
#endif

              PHILOSOPHER2_eQ!PHILOSOPHER2__tmpE;
              insertWithDelay(PHILOSOPHER2_eQ);
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
         :: j < PHILOSOPHER2_USCXML_NUMBER_TRANS -> {
           if
           :: (PHILOSOPHER2_ctx.trans_set[j] &&
              (PHILOSOPHER2_transitions[j].type[USCXML_TRANS_HISTORY] ||
               PHILOSOPHER2_transitions[j].type[USCXML_TRANS_INITIAL]) && 
               PHILOSOPHER2_states[PHILOSOPHER2_transitions[j].source].parent == i) -> {
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

                printf("philospher: : %d", PHILOSOPHER2_p_id);
                printf("starved in state hungry for Time(in ms) : : %d", PHILOSOPHER2_delay);
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
                :: !PHILOSOPHER2_flags[USCXML_CTX_FINISHED] || PHILOSOPHER2_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
                  {
                    PHILOSOPHER2__tmpE.data.p_id = 0;
                    PHILOSOPHER2__tmpE.delay = 0;
                    PHILOSOPHER2__tmpE.invokeid = 0;
                    PHILOSOPHER2__tmpE.name = 0;
                    PHILOSOPHER2__tmpE.origin = 0;
                    PHILOSOPHER2__tmpE.sendid = 0;
                    PHILOSOPHER2__tmpE.seqNr = 0;
                    PHILOSOPHER2__tmpE.name = NEED_RIGHT_FORK;
                    PHILOSOPHER2__tmpE.invokeid = PHILOSOPHER2;
                    PHILOSOPHER2__tmpE.origin = PHILOSOPHER2;
                    _lastSeqId = _lastSeqId + 1;
                    PHILOSOPHER2__tmpE.delay = 0;
                    PHILOSOPHER2__tmpE.seqNr = _lastSeqId;
                    PHILOSOPHER2__tmpE.data.p_id = PHILOSOPHER2_p_id;
#if TRACE_EXECUTION
printf("%d: Sending NEED_RIGHT_FORK (%d) to ROOT_eQ\n", _pid, PHILOSOPHER2__tmpE.name );
#endif

                    ROOT_eQ!PHILOSOPHER2__tmpE;
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

                printf("philospher: : %d", PHILOSOPHER2_p_id);
                printf("starved in state has_right_fork for Time(in ms) :: %d", PHILOSOPHER2_delay);
                skip;
              }
              :: j == 7 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, j);
#endif

                skip;
              }
              :: j == 8 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, j);
#endif

                if
                :: !PHILOSOPHER2_flags[USCXML_CTX_FINISHED] || PHILOSOPHER2_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
                  {
                    PHILOSOPHER2__tmpE.data.p_id = 0;
                    PHILOSOPHER2__tmpE.delay = 0;
                    PHILOSOPHER2__tmpE.invokeid = 0;
                    PHILOSOPHER2__tmpE.name = 0;
                    PHILOSOPHER2__tmpE.origin = 0;
                    PHILOSOPHER2__tmpE.sendid = 0;
                    PHILOSOPHER2__tmpE.seqNr = 0;
                    PHILOSOPHER2__tmpE.name = NEED_LEFT_FORK;
                    PHILOSOPHER2__tmpE.invokeid = PHILOSOPHER2;
                    PHILOSOPHER2__tmpE.origin = PHILOSOPHER2;
                    _lastSeqId = _lastSeqId + 1;
                    PHILOSOPHER2__tmpE.delay = 0;
                    PHILOSOPHER2__tmpE.seqNr = _lastSeqId;
                    PHILOSOPHER2__tmpE.data.p_id = PHILOSOPHER2_p_id;
#if TRACE_EXECUTION
printf("%d: Sending NEED_LEFT_FORK (%d) to ROOT_eQ\n", _pid, PHILOSOPHER2__tmpE.name );
#endif

                    ROOT_eQ!PHILOSOPHER2__tmpE;
                    insertWithDelay(ROOT_eQ);
                  }
                  skip;
                }
                :: else -> skip;
                fi
                skip;
              }
              :: j == 9 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, j);
#endif

                printf("philospher: : %d", PHILOSOPHER2_p_id);
                printf("starved in state has_right_fork for Time(in ms) : : %d", PHILOSOPHER2_delay);
                skip;
              }
              :: j == 10 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, j);
#endif

                if
                :: !PHILOSOPHER2_flags[USCXML_CTX_FINISHED] || PHILOSOPHER2_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
                  {
                    PHILOSOPHER2__tmpE.data.p_id = 0;
                    PHILOSOPHER2__tmpE.delay = 0;
                    PHILOSOPHER2__tmpE.invokeid = 0;
                    PHILOSOPHER2__tmpE.name = 0;
                    PHILOSOPHER2__tmpE.origin = 0;
                    PHILOSOPHER2__tmpE.sendid = 0;
                    PHILOSOPHER2__tmpE.seqNr = 0;
                    PHILOSOPHER2__tmpE.name = RETURN_FORKS;
                    PHILOSOPHER2__tmpE.invokeid = PHILOSOPHER2;
                    PHILOSOPHER2__tmpE.origin = PHILOSOPHER2;
                    _lastSeqId = _lastSeqId + 1;
                    PHILOSOPHER2__tmpE.delay = 0;
                    PHILOSOPHER2__tmpE.seqNr = _lastSeqId;
                    PHILOSOPHER2__tmpE.data.p_id = PHILOSOPHER2_p_id;
#if TRACE_EXECUTION
printf("%d: Sending RETURN_FORKS (%d) to ROOT_eQ\n", _pid, PHILOSOPHER2__tmpE.name );
#endif

                    ROOT_eQ!PHILOSOPHER2__tmpE;
                    insertWithDelay(ROOT_eQ);
                  }
                  skip;
                }
                :: else -> skip;
                fi
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
         :: PHILOSOPHER2_states[i].type[USCXML_STATE_FINAL] -> {
           if
           :: PHILOSOPHER2_states[PHILOSOPHER2_states[i].parent].children[1] -> {
             /* exit topmost SCXML state */
             PHILOSOPHER2_flags[USCXML_CTX_TOP_LEVEL_FINAL] = true;
             PHILOSOPHER2_flags[USCXML_CTX_FINISHED] = true;
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
            :: j < PHILOSOPHER2_USCXML_NUMBER_STATES -> {
              if
              :: PHILOSOPHER2_states[j].type[USCXML_STATE_PARALLEL] && PHILOSOPHER2_states[i].ancestors[j] -> {
                PHILOSOPHER2_STATES_CLEAR(PHILOSOPHER2_ctx.tmp_states)
                k = 0;
                do
                :: k < PHILOSOPHER2_USCXML_NUMBER_STATES -> {
                  if
                  :: PHILOSOPHER2_states[k].ancestors[j] && PHILOSOPHER2_config[k] -> {
                    if
                    :: PHILOSOPHER2_states[k].type[USCXML_STATE_FINAL] -> {
                      PHILOSOPHER2_STATES_AND_NOT(PHILOSOPHER2_ctx.tmp_states, PHILOSOPHER2_states[k].ancestors)
                    }
                    :: else -> {
                      PHILOSOPHER2_ctx.tmp_states[k] = true;
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
                :: !PHILOSOPHER2_STATES_HAS_ANY(PHILOSOPHER2_ctx.tmp_states) -> {
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
PHILOSOPHER2_TERMINATE_MACHINE:
skip; d_step {

#if TRACE_EXECUTION
printf("%d: Machine finished\n", _pid);
#endif

/* exit all remaining states */
i = PHILOSOPHER2_USCXML_NUMBER_STATES;
do
:: i > 0 -> {
  i = i - 1;
  if
  :: PHILOSOPHER2_config[i] && PHILOSOPHER2_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
    /* call all on exit handlers */
   if
    :: i == 3 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for exiting state %d\n", _pid, i);
#endif

    if
    :: (PHILOSOPHER2__event.name == TAKE_LEFT_FORK || PHILOSOPHER2__event.name == TAKE_RIGHT_FORK) -> {
        cancelSendId(STARVATION_TIMER,PHILOSOPHER2);
    }
    :: else -> skip;
    fi;
    }
    :: i == 4 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for exiting state %d\n", _pid, i);
#endif

    if
    :: (PHILOSOPHER2__event.name == TAKE_RIGHT_FORK) -> {
        cancelSendId(STARVATION_TIMER,PHILOSOPHER2);
    }
    :: else -> skip;
    fi;
    }
    :: i == 5 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for exiting state %d\n", _pid, i);
#endif

    if
    :: (PHILOSOPHER2__event.name == TAKE_LEFT_FORK) -> {
        cancelSendId(STARVATION_TIMER,PHILOSOPHER2);
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
  :: PHILOSOPHER2_invocations[i] -> {
    /* cancel invocations */
    PHILOSOPHER2_invocations[i] = false;
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

removePendingEventsFromInvoker(PHILOSOPHER2)
/* send done event */
if
:: PHILOSOPHER2_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
    PHILOSOPHER2__tmpE.data.p_id = 0;
    PHILOSOPHER2__tmpE.delay = 0;
    PHILOSOPHER2__tmpE.invokeid = 0;
    PHILOSOPHER2__tmpE.name = 0;
    PHILOSOPHER2__tmpE.origin = 0;
    PHILOSOPHER2__tmpE.sendid = 0;
    PHILOSOPHER2__tmpE.seqNr = 0;

    PHILOSOPHER2__tmpE.name = DONE_INVOKE_PHILOSOPHER2
    PHILOSOPHER2__tmpE.invokeid = PHILOSOPHER2

#if TRACE_EXECUTION
printf("%d: Sending DONE.INVOKE\n", _pid);
#endif

    ROOT_eQ!PHILOSOPHER2__tmpE;
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
#define PHILOSOPHER3_USCXML_NUMBER_STATES 8
#define PHILOSOPHER3_USCXML_NUMBER_TRANS 11

proctype PHILOSOPHER3_step() { atomic {

PHILOSOPHER3_procid = _pid;
unsigned i : 4,  j : 4,  k : 4;


/* ---------------------------- */
PHILOSOPHER3_MICROSTEP:
do
:: !PHILOSOPHER3_flags[USCXML_CTX_FINISHED] -> {
  /* Run until machine is finished */


#if TRACE_EXECUTION
printf("%d: Taking a step\n", _pid);
#endif

  /* Dequeue an event */
  PHILOSOPHER3_flags[USCXML_CTX_DEQUEUE_EXTERNAL] = false;
  if
  ::PHILOSOPHER3_flags[USCXML_CTX_SPONTANEOUS] -> {
    PHILOSOPHER3__event.name = USCXML_EVENT_SPONTANEOUS;

#if TRACE_EXECUTION
printf("%d: Trying with a spontaneous event\n", _pid);
#endif

  }
  :: else -> {
    if
    :: len(PHILOSOPHER3_iQ) != 0 -> {
      PHILOSOPHER3_iQ ? PHILOSOPHER3__event;

#if TRACE_EXECUTION
printf("%d: Deqeued an internal event\n", _pid);
#endif

    }
    :: else -> {
      PHILOSOPHER3_flags[USCXML_CTX_DEQUEUE_EXTERNAL] = true;
    }
    fi;
  }
  fi;


  if
  :: PHILOSOPHER3_flags[USCXML_CTX_DEQUEUE_EXTERNAL] -> {
    /* manage invocations */
    i = 0;
    do
    :: i < PHILOSOPHER3_USCXML_NUMBER_STATES -> {
      d_step { 
      /* uninvoke */
      if
      :: !PHILOSOPHER3_config[i] && PHILOSOPHER3_invocations[i] -> {

#if TRACE_EXECUTION
printf("%d: Uninvoking in state %d\n", _pid, i);
#endif

        if
        :: else -> skip;
        fi
        PHILOSOPHER3_invocations[i] = false;
        skip;
      }
      :: else -> skip;
      fi;
      } /* d_step */

      /* invoke */
      if
      :: PHILOSOPHER3_config[i] && !PHILOSOPHER3_invocations[i] -> {
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
    :: PHILOSOPHER3_flags[USCXML_CTX_FINISHED] -> {
      goto PHILOSOPHER3_TERMINATE_MACHINE;
    }
    :: else -> skip;
    fi
    /* Not sure if this should be before the invocation due to auto-forwarding */
    if
    :: len(PHILOSOPHER3_eQ) != 0 -> {
      PHILOSOPHER3_eQ ? PHILOSOPHER3__event;

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
PHILOSOPHER3_SELECT_TRANSITIONS:
PHILOSOPHER3_STATES_CLEAR(PHILOSOPHER3_ctx.target_set)
PHILOSOPHER3_STATES_CLEAR(PHILOSOPHER3_ctx.exit_set)
PHILOSOPHER3_TRANS_CLEAR(PHILOSOPHER3_ctx.conflicts)
PHILOSOPHER3_TRANS_CLEAR(PHILOSOPHER3_ctx.trans_set)
#if TRACE_EXECUTION
printf("%d: Establishing optimal transition set for event %d\n", _pid, PHILOSOPHER3__event.name );
#endif

#if TRACE_EXECUTION
printf("Configuration: ");
printf("%d%d%d%d%d%d%d%d", 
    PHILOSOPHER3_config[0], 
    PHILOSOPHER3_config[1], 
    PHILOSOPHER3_config[2], 
    PHILOSOPHER3_config[3], 
    PHILOSOPHER3_config[4], 
    PHILOSOPHER3_config[5], 
    PHILOSOPHER3_config[6], 
    PHILOSOPHER3_config[7]);
printf("\n");
#endif

  PHILOSOPHER3_flags[USCXML_CTX_TRANSITION_FOUND] = false;
  i = 0;
  do
  :: i < PHILOSOPHER3_USCXML_NUMBER_TRANS -> {
    /* only select non-history, non-initial transitions */
    if
    :: !PHILOSOPHER3_transitions[i].type[USCXML_TRANS_HISTORY] &&
       !PHILOSOPHER3_transitions[i].type[USCXML_TRANS_INITIAL] -> {
      if
      :: /* is the transition active? */
         PHILOSOPHER3_config[PHILOSOPHER3_transitions[i].source] && 

         /* is it non-conflicting? */
         !PHILOSOPHER3_ctx.conflicts[i] && 

         /* is it spontaneous with an event or vice versa? */
         ((PHILOSOPHER3__event.name == USCXML_EVENT_SPONTANEOUS && 
           PHILOSOPHER3_transitions[i].type[USCXML_TRANS_SPONTANEOUS]) || 
          (PHILOSOPHER3__event.name != USCXML_EVENT_SPONTANEOUS && 
           !PHILOSOPHER3_transitions[i].type[USCXML_TRANS_SPONTANEOUS])) &&

         /* is it matching and enabled? */
         (false 
          || (i == 0 && (false || PHILOSOPHER3__event.name == THINKING_OVER))
          || (i == 1 && (false || PHILOSOPHER3__event.name == TAKE_LEFT_FORK))
          || (i == 2 && (false || PHILOSOPHER3__event.name == TAKE_RIGHT_FORK))
          || (i == 3 && (false || PHILOSOPHER3__event.name == TIMEOUT))
          || (i == 4 && (false || PHILOSOPHER3__event.name == TAKE_RIGHT_FORK))
          || (i == 5 && (false || PHILOSOPHER3__event.name == RESEND_NEED_RIGHT_FORK))
          || (i == 6 && (false || PHILOSOPHER3__event.name == TIMEOUT))
          || (i == 7 && (false || PHILOSOPHER3__event.name == TAKE_LEFT_FORK))
          || (i == 8 && (false || PHILOSOPHER3__event.name == RESEND_NEED_LEFT_FORK))
          || (i == 9 && (false || PHILOSOPHER3__event.name == TIMEOUT))
          || (i == 10 && (false || PHILOSOPHER3__event.name == EATING_OVER))
         ) -> {
        /* remember that we found a transition */
        PHILOSOPHER3_flags[USCXML_CTX_TRANSITION_FOUND] = true;

        /* transitions that are pre-empted */
        PHILOSOPHER3_TRANS_OR(PHILOSOPHER3_ctx.conflicts, PHILOSOPHER3_transitions[i].conflicts)

        /* states that are directly targeted (resolve as entry-set later) */
        PHILOSOPHER3_STATES_OR(PHILOSOPHER3_ctx.target_set, PHILOSOPHER3_transitions[i].target)

        /* states that will be left */
        PHILOSOPHER3_STATES_OR(PHILOSOPHER3_ctx.exit_set, PHILOSOPHER3_transitions[i].exit_set)

        PHILOSOPHER3_ctx.trans_set[i] = true;
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
  PHILOSOPHER3_STATES_AND(PHILOSOPHER3_ctx.exit_set, PHILOSOPHER3_config)

#if TRACE_EXECUTION
printf("Selected Transitions: ");
printf("%d%d%d%d%d%d%d%d%d%d%d", 
    PHILOSOPHER3_ctx.trans_set[0], 
    PHILOSOPHER3_ctx.trans_set[1], 
    PHILOSOPHER3_ctx.trans_set[2], 
    PHILOSOPHER3_ctx.trans_set[3], 
    PHILOSOPHER3_ctx.trans_set[4], 
    PHILOSOPHER3_ctx.trans_set[5], 
    PHILOSOPHER3_ctx.trans_set[6], 
    PHILOSOPHER3_ctx.trans_set[7], 
    PHILOSOPHER3_ctx.trans_set[8], 
    PHILOSOPHER3_ctx.trans_set[9], 
    PHILOSOPHER3_ctx.trans_set[10]);
printf("\n");
#endif


#if TRACE_EXECUTION
printf("Target Set: ");
printf("%d%d%d%d%d%d%d%d", 
    PHILOSOPHER3_ctx.target_set[0], 
    PHILOSOPHER3_ctx.target_set[1], 
    PHILOSOPHER3_ctx.target_set[2], 
    PHILOSOPHER3_ctx.target_set[3], 
    PHILOSOPHER3_ctx.target_set[4], 
    PHILOSOPHER3_ctx.target_set[5], 
    PHILOSOPHER3_ctx.target_set[6], 
    PHILOSOPHER3_ctx.target_set[7]);
printf("\n");
#endif


#if TRACE_EXECUTION
printf("Exit Set: ");
printf("%d%d%d%d%d%d%d%d", 
    PHILOSOPHER3_ctx.exit_set[0], 
    PHILOSOPHER3_ctx.exit_set[1], 
    PHILOSOPHER3_ctx.exit_set[2], 
    PHILOSOPHER3_ctx.exit_set[3], 
    PHILOSOPHER3_ctx.exit_set[4], 
    PHILOSOPHER3_ctx.exit_set[5], 
    PHILOSOPHER3_ctx.exit_set[6], 
    PHILOSOPHER3_ctx.exit_set[7]);
printf("\n");
#endif

  if
  :: !PHILOSOPHER3_STATES_HAS_ANY(PHILOSOPHER3_config) -> {
    /* Enter initial configuration */
    PHILOSOPHER3_STATES_COPY(PHILOSOPHER3_ctx.target_set, PHILOSOPHER3_states[0].completion)
    PHILOSOPHER3_flags[USCXML_CTX_SPONTANEOUS] = true;
    PHILOSOPHER3_flags[USCXML_CTX_TRANSITION_FOUND] = true;

#if TRACE_EXECUTION
printf("%d: Entering initial default completion\n", _pid);
#endif


  }
  :: PHILOSOPHER3_flags[USCXML_CTX_TRANSITION_FOUND] -> {

#if TRACE_EXECUTION
printf("%d: Found transitions\n", _pid);
#endif

    PHILOSOPHER3_flags[USCXML_CTX_SPONTANEOUS] = true;
  }
  :: else {
    PHILOSOPHER3_flags[USCXML_CTX_SPONTANEOUS] = false;

#if TRACE_EXECUTION
printf("%d: Found NO transitions\n", _pid);
#endif

  }
  fi


  if
  :: PHILOSOPHER3_flags[USCXML_CTX_TRANSITION_FOUND] -> {
    /* only process anything if we found transitions or are on initial entry */
/* ---------------------------- */
/* REMEMBER_HISTORY: */

#if TRACE_EXECUTION
printf("%d: Save history configurations\n", _pid);
#endif

  if
  :: PHILOSOPHER3_STATES_HAS_ANY(PHILOSOPHER3_config) -> {
    /* only remember history on non-initial entry */
    i = 0;
    do
    :: i < PHILOSOPHER3_USCXML_NUMBER_STATES -> {
      if
      :: PHILOSOPHER3_states[i].type[USCXML_STATE_HISTORY_SHALLOW] ||
         PHILOSOPHER3_states[i].type[USCXML_STATE_HISTORY_DEEP] -> {
        if
        :: PHILOSOPHER3_ctx.exit_set[PHILOSOPHER3_states[i].parent] -> {
          /* a history state whose parent is about to be exited */

#if TRACE_EXECUTION
printf("%d: history state %d is about to be exited\n", _pid, i);
#endif


#if TRACE_EXECUTION
printf("COMPLET: ");
printf("%d%d%d%d%d%d%d%d", 
    PHILOSOPHER3_states[i].completion[0], 
    PHILOSOPHER3_states[i].completion[1], 
    PHILOSOPHER3_states[i].completion[2], 
    PHILOSOPHER3_states[i].completion[3], 
    PHILOSOPHER3_states[i].completion[4], 
    PHILOSOPHER3_states[i].completion[5], 
    PHILOSOPHER3_states[i].completion[6], 
    PHILOSOPHER3_states[i].completion[7]);
printf("\n");
#endif

          PHILOSOPHER3_STATES_COPY(PHILOSOPHER3_ctx.tmp_states, PHILOSOPHER3_states[i].completion)

          /* set those states who were enabled */
          PHILOSOPHER3_STATES_AND(PHILOSOPHER3_ctx.tmp_states, PHILOSOPHER3_config)

#if TRACE_EXECUTION
printf("CONFIG : ");
printf("%d%d%d%d%d%d%d%d", 
    PHILOSOPHER3_config[0], 
    PHILOSOPHER3_config[1], 
    PHILOSOPHER3_config[2], 
    PHILOSOPHER3_config[3], 
    PHILOSOPHER3_config[4], 
    PHILOSOPHER3_config[5], 
    PHILOSOPHER3_config[6], 
    PHILOSOPHER3_config[7]);
printf("\n");
#endif


#if TRACE_EXECUTION
printf("TMP_STS: ");
printf("%d%d%d%d%d%d%d%d", 
    PHILOSOPHER3_ctx.tmp_states[0], 
    PHILOSOPHER3_ctx.tmp_states[1], 
    PHILOSOPHER3_ctx.tmp_states[2], 
    PHILOSOPHER3_ctx.tmp_states[3], 
    PHILOSOPHER3_ctx.tmp_states[4], 
    PHILOSOPHER3_ctx.tmp_states[5], 
    PHILOSOPHER3_ctx.tmp_states[6], 
    PHILOSOPHER3_ctx.tmp_states[7]);
printf("\n");
#endif


          /* clear current history with completion mask */
          PHILOSOPHER3_STATES_AND_NOT(PHILOSOPHER3_history, PHILOSOPHER3_states[i].completion)

          /* set history */
          PHILOSOPHER3_STATES_OR(PHILOSOPHER3_history, PHILOSOPHER3_ctx.tmp_states)

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
printf("%d%d%d%d%d%d%d%d", 
    PHILOSOPHER3_history[0], 
    PHILOSOPHER3_history[1], 
    PHILOSOPHER3_history[2], 
    PHILOSOPHER3_history[3], 
    PHILOSOPHER3_history[4], 
    PHILOSOPHER3_history[5], 
    PHILOSOPHER3_history[6], 
    PHILOSOPHER3_history[7]);
printf("\n");
#endif
  }
  :: else -> skip;
  fi;

/* ---------------------------- */
PHILOSOPHER3_ESTABLISH_ENTRY_SET:
  /* calculate new entry set */
  PHILOSOPHER3_STATES_COPY(PHILOSOPHER3_ctx.entry_set, PHILOSOPHER3_ctx.target_set)

  i = 0;
  do
  :: i < PHILOSOPHER3_USCXML_NUMBER_STATES -> {
    if
    :: PHILOSOPHER3_ctx.entry_set[i] -> {
      /* ancestor completion */
      PHILOSOPHER3_STATES_OR(PHILOSOPHER3_ctx.entry_set, PHILOSOPHER3_states[i].ancestors)
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
  :: i < PHILOSOPHER3_USCXML_NUMBER_STATES -> {
    if
    :: PHILOSOPHER3_ctx.entry_set[i] -> {
      if
      :: PHILOSOPHER3_states[i].type[USCXML_STATE_PARALLEL] -> {
        PHILOSOPHER3_STATES_OR(PHILOSOPHER3_ctx.entry_set, PHILOSOPHER3_states[i].completion)
      }
      :: PHILOSOPHER3_states[i].type[USCXML_STATE_HISTORY_SHALLOW] ||
         PHILOSOPHER3_states[i].type[USCXML_STATE_HISTORY_DEEP] -> {

#if TRACE_EXECUTION
printf("%d: Descendant completion for history state %d\n", _pid, i);
#endif

        if
        :: !PHILOSOPHER3_STATES_HAS_AND(PHILOSOPHER3_states[i].completion, PHILOSOPHER3_history) && !PHILOSOPHER3_config[PHILOSOPHER3_states[i].parent] -> {
          /* nothing set for history, look for a default transition */

#if TRACE_EXECUTION
printf("%d: Fresh history in target set\n", _pid);
#endif

          j = 0;
          do
          :: j < PHILOSOPHER3_USCXML_NUMBER_TRANS -> {
             if
             :: PHILOSOPHER3_transitions[j].source == i -> {
               PHILOSOPHER3_ctx.trans_set[j] = true;
               PHILOSOPHER3_STATES_OR(PHILOSOPHER3_ctx.entry_set, PHILOSOPHER3_transitions[j].target)

               if
               :: (PHILOSOPHER3_states[i].type[USCXML_STATE_HISTORY_DEEP] &&
                   !PHILOSOPHER3_STATES_HAS_AND(PHILOSOPHER3_transitions[j].target, PHILOSOPHER3_states[i].children)                  ) -> {
                 k = i + 1
                 do
                 :: k < PHILOSOPHER3_USCXML_NUMBER_STATES -> {
                   if
                   :: PHILOSOPHER3_transitions[j].target[k] -> {
                     PHILOSOPHER3_STATES_OR(PHILOSOPHER3_ctx.entry_set, PHILOSOPHER3_states[k].ancestors)
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

          PHILOSOPHER3_STATES_COPY(PHILOSOPHER3_ctx.tmp_states, PHILOSOPHER3_states[i].completion)
          PHILOSOPHER3_STATES_AND(PHILOSOPHER3_ctx.tmp_states, PHILOSOPHER3_history)
          PHILOSOPHER3_STATES_OR(PHILOSOPHER3_ctx.entry_set, PHILOSOPHER3_ctx.tmp_states)
          if
          :: PHILOSOPHER3_states[i].type[USCXML_STATE_HAS_HISTORY] ||
             PHILOSOPHER3_states[i].type[USCXML_STATE_HISTORY_DEEP] -> { 
            /* a deep history state with nested histories -> more completion */

#if TRACE_EXECUTION
printf("%d: DEEP HISTORY\n", _pid);
#endif

            j = i + 1;
            do
            :: j < PHILOSOPHER3_USCXML_NUMBER_STATES -> {
              if
              :: (PHILOSOPHER3_states[i].completion[j] &&
                  PHILOSOPHER3_ctx.entry_set[j] && 
                  PHILOSOPHER3_states[j].type[USCXML_STATE_HAS_HISTORY]) -> {
                k = j + 1;
                do
                :: k < PHILOSOPHER3_USCXML_NUMBER_STATES -> {
                  /* add nested history to entry_set */
                  if
                  :: (PHILOSOPHER3_states[k].type[USCXML_STATE_HISTORY_DEEP] ||
                      PHILOSOPHER3_states[k].type[USCXML_STATE_HISTORY_SHALLOW]) &&
                     PHILOSOPHER3_states[j].children[k] -> {
                    /* a nested history state */
                    PHILOSOPHER3_ctx.entry_set[k] = true;
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
      :: PHILOSOPHER3_states[i].type[USCXML_STATE_INITIAL] -> {

#if TRACE_EXECUTION
printf("%d: Descendant completion for initial state %d\n", _pid, i);
#endif

        j = 0
        do
        :: j < PHILOSOPHER3_USCXML_NUMBER_TRANS -> {
          if
          :: PHILOSOPHER3_transitions[j].source == i -> {
            PHILOSOPHER3_ctx.trans_set[j] = true;
            PHILOSOPHER3_ctx.entry_set[i] = false;

#if TRACE_EXECUTION
printf("%d: Adding transition %d!\n", _pid, j);
#endif

            PHILOSOPHER3_STATES_OR(PHILOSOPHER3_ctx.entry_set, PHILOSOPHER3_transitions[j].target)

            k = i + 1;
            do
            :: k < PHILOSOPHER3_USCXML_NUMBER_STATES -> {
              if
              :: PHILOSOPHER3_transitions[j].target[k] -> {
                PHILOSOPHER3_STATES_OR(PHILOSOPHER3_ctx.entry_set, PHILOSOPHER3_states[k].ancestors)

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
      :: PHILOSOPHER3_states[i].type[USCXML_STATE_COMPOUND] -> {
        /* we need to check whether one child is already in entry_set */
        if
        :: (
          !PHILOSOPHER3_STATES_HAS_AND(PHILOSOPHER3_ctx.entry_set, PHILOSOPHER3_states[i].children) && 
           (!PHILOSOPHER3_STATES_HAS_AND(PHILOSOPHER3_config, PHILOSOPHER3_states[i].children) || PHILOSOPHER3_STATES_HAS_AND(PHILOSOPHER3_ctx.exit_set, PHILOSOPHER3_states[i].children)
)) 
        -> {
          PHILOSOPHER3_STATES_OR(PHILOSOPHER3_ctx.entry_set, PHILOSOPHER3_states[i].completion)
          if
          :: (PHILOSOPHER3_STATES_HAS_AND(PHILOSOPHER3_states[i].completion, PHILOSOPHER3_states[i].children)
          ) -> {
            /* deep completion */
            j = i + 1;
            do
            :: j < PHILOSOPHER3_USCXML_NUMBER_STATES - 1 -> {
              j = j + 1;
              if
              :: PHILOSOPHER3_states[i].completion[j] -> {
                PHILOSOPHER3_STATES_OR(PHILOSOPHER3_ctx.entry_set, PHILOSOPHER3_states[j].ancestors)

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
printf("%d%d%d%d%d%d%d%d", 
    PHILOSOPHER3_ctx.entry_set[0], 
    PHILOSOPHER3_ctx.entry_set[1], 
    PHILOSOPHER3_ctx.entry_set[2], 
    PHILOSOPHER3_ctx.entry_set[3], 
    PHILOSOPHER3_ctx.entry_set[4], 
    PHILOSOPHER3_ctx.entry_set[5], 
    PHILOSOPHER3_ctx.entry_set[6], 
    PHILOSOPHER3_ctx.entry_set[7]);
printf("\n");
#endif


/* ---------------------------- */
/* EXIT_STATES: */
  i = PHILOSOPHER3_USCXML_NUMBER_STATES;
  do
  :: i > 0 -> {
    i = i - 1;
    if
    :: PHILOSOPHER3_ctx.exit_set[i] && PHILOSOPHER3_config[i] -> {
      /* call all on-exit handlers */

#if TRACE_EXECUTION
printf("%d: Exiting state %d\n", _pid, i);
#endif

      if
      :: i == 3 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for exiting state %d\n", _pid, i);
#endif

      if
      :: (PHILOSOPHER3__event.name == TAKE_LEFT_FORK || PHILOSOPHER3__event.name == TAKE_RIGHT_FORK) -> {
          cancelSendId(STARVATION_TIMER,PHILOSOPHER3);
      }
      :: else -> skip;
      fi;
      }
      :: i == 4 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for exiting state %d\n", _pid, i);
#endif

      if
      :: (PHILOSOPHER3__event.name == TAKE_RIGHT_FORK) -> {
          cancelSendId(STARVATION_TIMER,PHILOSOPHER3);
      }
      :: else -> skip;
      fi;
      }
      :: i == 5 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for exiting state %d\n", _pid, i);
#endif

      if
      :: (PHILOSOPHER3__event.name == TAKE_LEFT_FORK) -> {
          cancelSendId(STARVATION_TIMER,PHILOSOPHER3);
      }
      :: else -> skip;
      fi;
      }
      :: else -> skip;
      fi

      PHILOSOPHER3_config[i] = false;
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
  :: i < PHILOSOPHER3_USCXML_NUMBER_TRANS -> {
    if
    :: PHILOSOPHER3_ctx.trans_set[i] && 
       !PHILOSOPHER3_transitions[i].type[USCXML_TRANS_HISTORY] && 
       !PHILOSOPHER3_transitions[i].type[USCXML_TRANS_INITIAL] -> {
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

        printf("philospher: : %d", PHILOSOPHER3_p_id);
        printf("starved in state hungry for Time(in ms) : : %d", PHILOSOPHER3_delay);
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
        :: !PHILOSOPHER3_flags[USCXML_CTX_FINISHED] || PHILOSOPHER3_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
          {
            PHILOSOPHER3__tmpE.data.p_id = 0;
            PHILOSOPHER3__tmpE.delay = 0;
            PHILOSOPHER3__tmpE.invokeid = 0;
            PHILOSOPHER3__tmpE.name = 0;
            PHILOSOPHER3__tmpE.origin = 0;
            PHILOSOPHER3__tmpE.sendid = 0;
            PHILOSOPHER3__tmpE.seqNr = 0;
            PHILOSOPHER3__tmpE.name = NEED_RIGHT_FORK;
            PHILOSOPHER3__tmpE.invokeid = PHILOSOPHER3;
            PHILOSOPHER3__tmpE.origin = PHILOSOPHER3;
            _lastSeqId = _lastSeqId + 1;
            PHILOSOPHER3__tmpE.delay = 0;
            PHILOSOPHER3__tmpE.seqNr = _lastSeqId;
            PHILOSOPHER3__tmpE.data.p_id = PHILOSOPHER3_p_id;
#if TRACE_EXECUTION
printf("%d: Sending NEED_RIGHT_FORK (%d) to ROOT_eQ\n", _pid, PHILOSOPHER3__tmpE.name );
#endif

            ROOT_eQ!PHILOSOPHER3__tmpE;
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

        printf("philospher: : %d", PHILOSOPHER3_p_id);
        printf("starved in state has_right_fork for Time(in ms) :: %d", PHILOSOPHER3_delay);
        skip;
      }
      :: i == 7 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, i);
#endif

        skip;
      }
      :: i == 8 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, i);
#endif

        if
        :: !PHILOSOPHER3_flags[USCXML_CTX_FINISHED] || PHILOSOPHER3_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
          {
            PHILOSOPHER3__tmpE.data.p_id = 0;
            PHILOSOPHER3__tmpE.delay = 0;
            PHILOSOPHER3__tmpE.invokeid = 0;
            PHILOSOPHER3__tmpE.name = 0;
            PHILOSOPHER3__tmpE.origin = 0;
            PHILOSOPHER3__tmpE.sendid = 0;
            PHILOSOPHER3__tmpE.seqNr = 0;
            PHILOSOPHER3__tmpE.name = NEED_LEFT_FORK;
            PHILOSOPHER3__tmpE.invokeid = PHILOSOPHER3;
            PHILOSOPHER3__tmpE.origin = PHILOSOPHER3;
            _lastSeqId = _lastSeqId + 1;
            PHILOSOPHER3__tmpE.delay = 0;
            PHILOSOPHER3__tmpE.seqNr = _lastSeqId;
            PHILOSOPHER3__tmpE.data.p_id = PHILOSOPHER3_p_id;
#if TRACE_EXECUTION
printf("%d: Sending NEED_LEFT_FORK (%d) to ROOT_eQ\n", _pid, PHILOSOPHER3__tmpE.name );
#endif

            ROOT_eQ!PHILOSOPHER3__tmpE;
            insertWithDelay(ROOT_eQ);
          }
          skip;
        }
        :: else -> skip;
        fi
        skip;
      }
      :: i == 9 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, i);
#endif

        printf("philospher: : %d", PHILOSOPHER3_p_id);
        printf("starved in state has_right_fork for Time(in ms) : : %d", PHILOSOPHER3_delay);
        skip;
      }
      :: i == 10 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, i);
#endif

        if
        :: !PHILOSOPHER3_flags[USCXML_CTX_FINISHED] || PHILOSOPHER3_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
          {
            PHILOSOPHER3__tmpE.data.p_id = 0;
            PHILOSOPHER3__tmpE.delay = 0;
            PHILOSOPHER3__tmpE.invokeid = 0;
            PHILOSOPHER3__tmpE.name = 0;
            PHILOSOPHER3__tmpE.origin = 0;
            PHILOSOPHER3__tmpE.sendid = 0;
            PHILOSOPHER3__tmpE.seqNr = 0;
            PHILOSOPHER3__tmpE.name = RETURN_FORKS;
            PHILOSOPHER3__tmpE.invokeid = PHILOSOPHER3;
            PHILOSOPHER3__tmpE.origin = PHILOSOPHER3;
            _lastSeqId = _lastSeqId + 1;
            PHILOSOPHER3__tmpE.delay = 0;
            PHILOSOPHER3__tmpE.seqNr = _lastSeqId;
            PHILOSOPHER3__tmpE.data.p_id = PHILOSOPHER3_p_id;
#if TRACE_EXECUTION
printf("%d: Sending RETURN_FORKS (%d) to ROOT_eQ\n", _pid, PHILOSOPHER3__tmpE.name );
#endif

            ROOT_eQ!PHILOSOPHER3__tmpE;
            insertWithDelay(ROOT_eQ);
          }
          skip;
        }
        :: else -> skip;
        fi
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
  :: i < PHILOSOPHER3_USCXML_NUMBER_STATES -> {
    if
    :: (PHILOSOPHER3_ctx.entry_set[i] &&
        !PHILOSOPHER3_config[i] && 
        /* these are no proper states */
        !PHILOSOPHER3_states[i].type[USCXML_STATE_HISTORY_DEEP] && 
        !PHILOSOPHER3_states[i].type[USCXML_STATE_HISTORY_SHALLOW] && 
        !PHILOSOPHER3_states[i].type[USCXML_STATE_INITIAL]
       ) -> {

#if TRACE_EXECUTION
printf("%d: Entering state %d\n", _pid, i);
#endif

         PHILOSOPHER3_config[i] = true;

         /* Process executable content for entering a state */
         if
         :: i == 1 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for entering state %d\n", _pid, i);
#endif

          printf("Hello, I am philospher number: : %d", PHILOSOPHER3_p_id);
         }
         :: i == 2 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for entering state %d\n", _pid, i);
#endif

          printf("Thinking philosopher: : %d", PHILOSOPHER3_p_id);
            PHILOSOPHER3_random_delay = ((1103515245*PHILOSOPHER3_random_delay+12345)%2147483647)%2000;
          if
          :: !PHILOSOPHER3_flags[USCXML_CTX_FINISHED] || PHILOSOPHER3_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
            {
              PHILOSOPHER3__tmpE.data.p_id = 0;
              PHILOSOPHER3__tmpE.delay = 0;
              PHILOSOPHER3__tmpE.invokeid = 0;
              PHILOSOPHER3__tmpE.name = 0;
              PHILOSOPHER3__tmpE.origin = 0;
              PHILOSOPHER3__tmpE.sendid = 0;
              PHILOSOPHER3__tmpE.seqNr = 0;
              PHILOSOPHER3__tmpE.name = THINKING_OVER;
              PHILOSOPHER3__tmpE.invokeid = PHILOSOPHER3;
              PHILOSOPHER3__tmpE.origin = PHILOSOPHER3;
              _lastSeqId = _lastSeqId + 1;
              PHILOSOPHER3__tmpE.delay = PHILOSOPHER3_random_delay*(PHILOSOPHER3_p_id+1);
              PHILOSOPHER3__tmpE.seqNr = _lastSeqId;
#if TRACE_EXECUTION
printf("%d: Sending THINKING_OVER (%d) to PHILOSOPHER3_eQ\n", _pid, PHILOSOPHER3__tmpE.name );
#endif

              PHILOSOPHER3_eQ!PHILOSOPHER3__tmpE;
              insertWithDelay(PHILOSOPHER3_eQ);
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

          printf("Hungry philosopher: : %d", PHILOSOPHER3_p_id);
          if
          :: !PHILOSOPHER3_flags[USCXML_CTX_FINISHED] || PHILOSOPHER3_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
            {
              PHILOSOPHER3__tmpE.data.p_id = 0;
              PHILOSOPHER3__tmpE.delay = 0;
              PHILOSOPHER3__tmpE.invokeid = 0;
              PHILOSOPHER3__tmpE.name = 0;
              PHILOSOPHER3__tmpE.origin = 0;
              PHILOSOPHER3__tmpE.sendid = 0;
              PHILOSOPHER3__tmpE.seqNr = 0;
              PHILOSOPHER3__tmpE.name = TIMEOUT;
              PHILOSOPHER3__tmpE.sendid = STARVATION_TIMER;
              PHILOSOPHER3__tmpE.invokeid = PHILOSOPHER3;
              PHILOSOPHER3__tmpE.origin = PHILOSOPHER3;
              _lastSeqId = _lastSeqId + 1;
              PHILOSOPHER3__tmpE.delay = PHILOSOPHER3_delay;
              PHILOSOPHER3__tmpE.seqNr = _lastSeqId;
#if TRACE_EXECUTION
printf("%d: Sending TIMEOUT (%d) to PHILOSOPHER3_eQ\n", _pid, PHILOSOPHER3__tmpE.name );
#endif

              PHILOSOPHER3_eQ!PHILOSOPHER3__tmpE;
              insertWithDelay(PHILOSOPHER3_eQ);
            }
            skip;
          }
          :: else -> skip;
          fi
          if
          :: !PHILOSOPHER3_flags[USCXML_CTX_FINISHED] || PHILOSOPHER3_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
            {
              PHILOSOPHER3__tmpE.data.p_id = 0;
              PHILOSOPHER3__tmpE.delay = 0;
              PHILOSOPHER3__tmpE.invokeid = 0;
              PHILOSOPHER3__tmpE.name = 0;
              PHILOSOPHER3__tmpE.origin = 0;
              PHILOSOPHER3__tmpE.sendid = 0;
              PHILOSOPHER3__tmpE.seqNr = 0;
              PHILOSOPHER3__tmpE.name = NEED_LEFT_FORK;
              PHILOSOPHER3__tmpE.invokeid = PHILOSOPHER3;
              PHILOSOPHER3__tmpE.origin = PHILOSOPHER3;
              _lastSeqId = _lastSeqId + 1;
              PHILOSOPHER3__tmpE.delay = 0;
              PHILOSOPHER3__tmpE.seqNr = _lastSeqId;
              PHILOSOPHER3__tmpE.data.p_id = PHILOSOPHER3_p_id;
#if TRACE_EXECUTION
printf("%d: Sending NEED_LEFT_FORK (%d) to ROOT_eQ\n", _pid, PHILOSOPHER3__tmpE.name );
#endif

              ROOT_eQ!PHILOSOPHER3__tmpE;
              insertWithDelay(ROOT_eQ);
            }
            skip;
          }
          :: else -> skip;
          fi
          if
          :: !PHILOSOPHER3_flags[USCXML_CTX_FINISHED] || PHILOSOPHER3_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
            {
              PHILOSOPHER3__tmpE.data.p_id = 0;
              PHILOSOPHER3__tmpE.delay = 0;
              PHILOSOPHER3__tmpE.invokeid = 0;
              PHILOSOPHER3__tmpE.name = 0;
              PHILOSOPHER3__tmpE.origin = 0;
              PHILOSOPHER3__tmpE.sendid = 0;
              PHILOSOPHER3__tmpE.seqNr = 0;
              PHILOSOPHER3__tmpE.name = NEED_RIGHT_FORK;
              PHILOSOPHER3__tmpE.invokeid = PHILOSOPHER3;
              PHILOSOPHER3__tmpE.origin = PHILOSOPHER3;
              _lastSeqId = _lastSeqId + 1;
              PHILOSOPHER3__tmpE.delay = 0;
              PHILOSOPHER3__tmpE.seqNr = _lastSeqId;
              PHILOSOPHER3__tmpE.data.p_id = PHILOSOPHER3_p_id;
#if TRACE_EXECUTION
printf("%d: Sending NEED_RIGHT_FORK (%d) to ROOT_eQ\n", _pid, PHILOSOPHER3__tmpE.name );
#endif

              ROOT_eQ!PHILOSOPHER3__tmpE;
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

          printf("in state has_left_fork for philosopher: : %d", PHILOSOPHER3_p_id);
          if
          :: !PHILOSOPHER3_flags[USCXML_CTX_FINISHED] || PHILOSOPHER3_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
            {
              PHILOSOPHER3__tmpE.data.p_id = 0;
              PHILOSOPHER3__tmpE.delay = 0;
              PHILOSOPHER3__tmpE.invokeid = 0;
              PHILOSOPHER3__tmpE.name = 0;
              PHILOSOPHER3__tmpE.origin = 0;
              PHILOSOPHER3__tmpE.sendid = 0;
              PHILOSOPHER3__tmpE.seqNr = 0;
              PHILOSOPHER3__tmpE.name = TIMEOUT;
              PHILOSOPHER3__tmpE.sendid = STARVATION_TIMER;
              PHILOSOPHER3__tmpE.invokeid = PHILOSOPHER3;
              PHILOSOPHER3__tmpE.origin = PHILOSOPHER3;
              _lastSeqId = _lastSeqId + 1;
              PHILOSOPHER3__tmpE.delay = PHILOSOPHER3_delay;
              PHILOSOPHER3__tmpE.seqNr = _lastSeqId;
#if TRACE_EXECUTION
printf("%d: Sending TIMEOUT (%d) to PHILOSOPHER3_eQ\n", _pid, PHILOSOPHER3__tmpE.name );
#endif

              PHILOSOPHER3_eQ!PHILOSOPHER3__tmpE;
              insertWithDelay(PHILOSOPHER3_eQ);
            }
            skip;
          }
          :: else -> skip;
          fi
          if
          :: !PHILOSOPHER3_flags[USCXML_CTX_FINISHED] || PHILOSOPHER3_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
            {
              PHILOSOPHER3__tmpE.data.p_id = 0;
              PHILOSOPHER3__tmpE.delay = 0;
              PHILOSOPHER3__tmpE.invokeid = 0;
              PHILOSOPHER3__tmpE.name = 0;
              PHILOSOPHER3__tmpE.origin = 0;
              PHILOSOPHER3__tmpE.sendid = 0;
              PHILOSOPHER3__tmpE.seqNr = 0;
              PHILOSOPHER3__tmpE.name = RESEND_NEED_RIGHT_FORK;
              PHILOSOPHER3__tmpE.invokeid = PHILOSOPHER3;
              PHILOSOPHER3__tmpE.origin = PHILOSOPHER3;
              _lastSeqId = _lastSeqId + 1;
              PHILOSOPHER3__tmpE.delay = 500;
              PHILOSOPHER3__tmpE.seqNr = _lastSeqId;
#if TRACE_EXECUTION
printf("%d: Sending RESEND_NEED_RIGHT_FORK (%d) to PHILOSOPHER3_eQ\n", _pid, PHILOSOPHER3__tmpE.name );
#endif

              PHILOSOPHER3_eQ!PHILOSOPHER3__tmpE;
              insertWithDelay(PHILOSOPHER3_eQ);
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

          printf("in state has_right_fork for philosopher: : %d", PHILOSOPHER3_p_id);
          if
          :: !PHILOSOPHER3_flags[USCXML_CTX_FINISHED] || PHILOSOPHER3_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
            {
              PHILOSOPHER3__tmpE.data.p_id = 0;
              PHILOSOPHER3__tmpE.delay = 0;
              PHILOSOPHER3__tmpE.invokeid = 0;
              PHILOSOPHER3__tmpE.name = 0;
              PHILOSOPHER3__tmpE.origin = 0;
              PHILOSOPHER3__tmpE.sendid = 0;
              PHILOSOPHER3__tmpE.seqNr = 0;
              PHILOSOPHER3__tmpE.name = TIMEOUT;
              PHILOSOPHER3__tmpE.sendid = STARVATION_TIMER;
              PHILOSOPHER3__tmpE.invokeid = PHILOSOPHER3;
              PHILOSOPHER3__tmpE.origin = PHILOSOPHER3;
              _lastSeqId = _lastSeqId + 1;
              PHILOSOPHER3__tmpE.delay = PHILOSOPHER3_delay;
              PHILOSOPHER3__tmpE.seqNr = _lastSeqId;
#if TRACE_EXECUTION
printf("%d: Sending TIMEOUT (%d) to PHILOSOPHER3_eQ\n", _pid, PHILOSOPHER3__tmpE.name );
#endif

              PHILOSOPHER3_eQ!PHILOSOPHER3__tmpE;
              insertWithDelay(PHILOSOPHER3_eQ);
            }
            skip;
          }
          :: else -> skip;
          fi
          if
          :: !PHILOSOPHER3_flags[USCXML_CTX_FINISHED] || PHILOSOPHER3_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
            {
              PHILOSOPHER3__tmpE.data.p_id = 0;
              PHILOSOPHER3__tmpE.delay = 0;
              PHILOSOPHER3__tmpE.invokeid = 0;
              PHILOSOPHER3__tmpE.name = 0;
              PHILOSOPHER3__tmpE.origin = 0;
              PHILOSOPHER3__tmpE.sendid = 0;
              PHILOSOPHER3__tmpE.seqNr = 0;
              PHILOSOPHER3__tmpE.name = RESEND_NEED_LEFT_FORK;
              PHILOSOPHER3__tmpE.invokeid = PHILOSOPHER3;
              PHILOSOPHER3__tmpE.origin = PHILOSOPHER3;
              _lastSeqId = _lastSeqId + 1;
              PHILOSOPHER3__tmpE.delay = 500;
              PHILOSOPHER3__tmpE.seqNr = _lastSeqId;
#if TRACE_EXECUTION
printf("%d: Sending RESEND_NEED_LEFT_FORK (%d) to PHILOSOPHER3_eQ\n", _pid, PHILOSOPHER3__tmpE.name );
#endif

              PHILOSOPHER3_eQ!PHILOSOPHER3__tmpE;
              insertWithDelay(PHILOSOPHER3_eQ);
            }
            skip;
          }
          :: else -> skip;
          fi
         }
         :: i == 6 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for entering state %d\n", _pid, i);
#endif

          printf("Eating philosopher: : %d", PHILOSOPHER3_p_id);
          if
          :: !PHILOSOPHER3_flags[USCXML_CTX_FINISHED] || PHILOSOPHER3_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
            {
              PHILOSOPHER3__tmpE.data.p_id = 0;
              PHILOSOPHER3__tmpE.delay = 0;
              PHILOSOPHER3__tmpE.invokeid = 0;
              PHILOSOPHER3__tmpE.name = 0;
              PHILOSOPHER3__tmpE.origin = 0;
              PHILOSOPHER3__tmpE.sendid = 0;
              PHILOSOPHER3__tmpE.seqNr = 0;
              PHILOSOPHER3__tmpE.name = EATING_OVER;
              PHILOSOPHER3__tmpE.invokeid = PHILOSOPHER3;
              PHILOSOPHER3__tmpE.origin = PHILOSOPHER3;
              _lastSeqId = _lastSeqId + 1;
              PHILOSOPHER3__tmpE.delay = PHILOSOPHER3_random_delay;
              PHILOSOPHER3__tmpE.seqNr = _lastSeqId;
#if TRACE_EXECUTION
printf("%d: Sending EATING_OVER (%d) to PHILOSOPHER3_eQ\n", _pid, PHILOSOPHER3__tmpE.name );
#endif

              PHILOSOPHER3_eQ!PHILOSOPHER3__tmpE;
              insertWithDelay(PHILOSOPHER3_eQ);
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
         :: j < PHILOSOPHER3_USCXML_NUMBER_TRANS -> {
           if
           :: (PHILOSOPHER3_ctx.trans_set[j] &&
              (PHILOSOPHER3_transitions[j].type[USCXML_TRANS_HISTORY] ||
               PHILOSOPHER3_transitions[j].type[USCXML_TRANS_INITIAL]) && 
               PHILOSOPHER3_states[PHILOSOPHER3_transitions[j].source].parent == i) -> {
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

                printf("philospher: : %d", PHILOSOPHER3_p_id);
                printf("starved in state hungry for Time(in ms) : : %d", PHILOSOPHER3_delay);
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
                :: !PHILOSOPHER3_flags[USCXML_CTX_FINISHED] || PHILOSOPHER3_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
                  {
                    PHILOSOPHER3__tmpE.data.p_id = 0;
                    PHILOSOPHER3__tmpE.delay = 0;
                    PHILOSOPHER3__tmpE.invokeid = 0;
                    PHILOSOPHER3__tmpE.name = 0;
                    PHILOSOPHER3__tmpE.origin = 0;
                    PHILOSOPHER3__tmpE.sendid = 0;
                    PHILOSOPHER3__tmpE.seqNr = 0;
                    PHILOSOPHER3__tmpE.name = NEED_RIGHT_FORK;
                    PHILOSOPHER3__tmpE.invokeid = PHILOSOPHER3;
                    PHILOSOPHER3__tmpE.origin = PHILOSOPHER3;
                    _lastSeqId = _lastSeqId + 1;
                    PHILOSOPHER3__tmpE.delay = 0;
                    PHILOSOPHER3__tmpE.seqNr = _lastSeqId;
                    PHILOSOPHER3__tmpE.data.p_id = PHILOSOPHER3_p_id;
#if TRACE_EXECUTION
printf("%d: Sending NEED_RIGHT_FORK (%d) to ROOT_eQ\n", _pid, PHILOSOPHER3__tmpE.name );
#endif

                    ROOT_eQ!PHILOSOPHER3__tmpE;
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

                printf("philospher: : %d", PHILOSOPHER3_p_id);
                printf("starved in state has_right_fork for Time(in ms) :: %d", PHILOSOPHER3_delay);
                skip;
              }
              :: j == 7 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, j);
#endif

                skip;
              }
              :: j == 8 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, j);
#endif

                if
                :: !PHILOSOPHER3_flags[USCXML_CTX_FINISHED] || PHILOSOPHER3_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
                  {
                    PHILOSOPHER3__tmpE.data.p_id = 0;
                    PHILOSOPHER3__tmpE.delay = 0;
                    PHILOSOPHER3__tmpE.invokeid = 0;
                    PHILOSOPHER3__tmpE.name = 0;
                    PHILOSOPHER3__tmpE.origin = 0;
                    PHILOSOPHER3__tmpE.sendid = 0;
                    PHILOSOPHER3__tmpE.seqNr = 0;
                    PHILOSOPHER3__tmpE.name = NEED_LEFT_FORK;
                    PHILOSOPHER3__tmpE.invokeid = PHILOSOPHER3;
                    PHILOSOPHER3__tmpE.origin = PHILOSOPHER3;
                    _lastSeqId = _lastSeqId + 1;
                    PHILOSOPHER3__tmpE.delay = 0;
                    PHILOSOPHER3__tmpE.seqNr = _lastSeqId;
                    PHILOSOPHER3__tmpE.data.p_id = PHILOSOPHER3_p_id;
#if TRACE_EXECUTION
printf("%d: Sending NEED_LEFT_FORK (%d) to ROOT_eQ\n", _pid, PHILOSOPHER3__tmpE.name );
#endif

                    ROOT_eQ!PHILOSOPHER3__tmpE;
                    insertWithDelay(ROOT_eQ);
                  }
                  skip;
                }
                :: else -> skip;
                fi
                skip;
              }
              :: j == 9 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, j);
#endif

                printf("philospher: : %d", PHILOSOPHER3_p_id);
                printf("starved in state has_right_fork for Time(in ms) : : %d", PHILOSOPHER3_delay);
                skip;
              }
              :: j == 10 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, j);
#endif

                if
                :: !PHILOSOPHER3_flags[USCXML_CTX_FINISHED] || PHILOSOPHER3_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
                  {
                    PHILOSOPHER3__tmpE.data.p_id = 0;
                    PHILOSOPHER3__tmpE.delay = 0;
                    PHILOSOPHER3__tmpE.invokeid = 0;
                    PHILOSOPHER3__tmpE.name = 0;
                    PHILOSOPHER3__tmpE.origin = 0;
                    PHILOSOPHER3__tmpE.sendid = 0;
                    PHILOSOPHER3__tmpE.seqNr = 0;
                    PHILOSOPHER3__tmpE.name = RETURN_FORKS;
                    PHILOSOPHER3__tmpE.invokeid = PHILOSOPHER3;
                    PHILOSOPHER3__tmpE.origin = PHILOSOPHER3;
                    _lastSeqId = _lastSeqId + 1;
                    PHILOSOPHER3__tmpE.delay = 0;
                    PHILOSOPHER3__tmpE.seqNr = _lastSeqId;
                    PHILOSOPHER3__tmpE.data.p_id = PHILOSOPHER3_p_id;
#if TRACE_EXECUTION
printf("%d: Sending RETURN_FORKS (%d) to ROOT_eQ\n", _pid, PHILOSOPHER3__tmpE.name );
#endif

                    ROOT_eQ!PHILOSOPHER3__tmpE;
                    insertWithDelay(ROOT_eQ);
                  }
                  skip;
                }
                :: else -> skip;
                fi
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
         :: PHILOSOPHER3_states[i].type[USCXML_STATE_FINAL] -> {
           if
           :: PHILOSOPHER3_states[PHILOSOPHER3_states[i].parent].children[1] -> {
             /* exit topmost SCXML state */
             PHILOSOPHER3_flags[USCXML_CTX_TOP_LEVEL_FINAL] = true;
             PHILOSOPHER3_flags[USCXML_CTX_FINISHED] = true;
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
            :: j < PHILOSOPHER3_USCXML_NUMBER_STATES -> {
              if
              :: PHILOSOPHER3_states[j].type[USCXML_STATE_PARALLEL] && PHILOSOPHER3_states[i].ancestors[j] -> {
                PHILOSOPHER3_STATES_CLEAR(PHILOSOPHER3_ctx.tmp_states)
                k = 0;
                do
                :: k < PHILOSOPHER3_USCXML_NUMBER_STATES -> {
                  if
                  :: PHILOSOPHER3_states[k].ancestors[j] && PHILOSOPHER3_config[k] -> {
                    if
                    :: PHILOSOPHER3_states[k].type[USCXML_STATE_FINAL] -> {
                      PHILOSOPHER3_STATES_AND_NOT(PHILOSOPHER3_ctx.tmp_states, PHILOSOPHER3_states[k].ancestors)
                    }
                    :: else -> {
                      PHILOSOPHER3_ctx.tmp_states[k] = true;
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
                :: !PHILOSOPHER3_STATES_HAS_ANY(PHILOSOPHER3_ctx.tmp_states) -> {
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
PHILOSOPHER3_TERMINATE_MACHINE:
skip; d_step {

#if TRACE_EXECUTION
printf("%d: Machine finished\n", _pid);
#endif

/* exit all remaining states */
i = PHILOSOPHER3_USCXML_NUMBER_STATES;
do
:: i > 0 -> {
  i = i - 1;
  if
  :: PHILOSOPHER3_config[i] && PHILOSOPHER3_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
    /* call all on exit handlers */
   if
    :: i == 3 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for exiting state %d\n", _pid, i);
#endif

    if
    :: (PHILOSOPHER3__event.name == TAKE_LEFT_FORK || PHILOSOPHER3__event.name == TAKE_RIGHT_FORK) -> {
        cancelSendId(STARVATION_TIMER,PHILOSOPHER3);
    }
    :: else -> skip;
    fi;
    }
    :: i == 4 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for exiting state %d\n", _pid, i);
#endif

    if
    :: (PHILOSOPHER3__event.name == TAKE_RIGHT_FORK) -> {
        cancelSendId(STARVATION_TIMER,PHILOSOPHER3);
    }
    :: else -> skip;
    fi;
    }
    :: i == 5 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for exiting state %d\n", _pid, i);
#endif

    if
    :: (PHILOSOPHER3__event.name == TAKE_LEFT_FORK) -> {
        cancelSendId(STARVATION_TIMER,PHILOSOPHER3);
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
  :: PHILOSOPHER3_invocations[i] -> {
    /* cancel invocations */
    PHILOSOPHER3_invocations[i] = false;
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

removePendingEventsFromInvoker(PHILOSOPHER3)
/* send done event */
if
:: PHILOSOPHER3_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
    PHILOSOPHER3__tmpE.data.p_id = 0;
    PHILOSOPHER3__tmpE.delay = 0;
    PHILOSOPHER3__tmpE.invokeid = 0;
    PHILOSOPHER3__tmpE.name = 0;
    PHILOSOPHER3__tmpE.origin = 0;
    PHILOSOPHER3__tmpE.sendid = 0;
    PHILOSOPHER3__tmpE.seqNr = 0;

    PHILOSOPHER3__tmpE.name = DONE_INVOKE_PHILOSOPHER3
    PHILOSOPHER3__tmpE.invokeid = PHILOSOPHER3

#if TRACE_EXECUTION
printf("%d: Sending DONE.INVOKE\n", _pid);
#endif

    ROOT_eQ!PHILOSOPHER3__tmpE;
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
#define PHILOSOPHER4_USCXML_NUMBER_STATES 8
#define PHILOSOPHER4_USCXML_NUMBER_TRANS 11

proctype PHILOSOPHER4_step() { atomic {

PHILOSOPHER4_procid = _pid;
unsigned i : 4,  j : 4,  k : 4;


/* ---------------------------- */
PHILOSOPHER4_MICROSTEP:
do
:: !PHILOSOPHER4_flags[USCXML_CTX_FINISHED] -> {
  /* Run until machine is finished */


#if TRACE_EXECUTION
printf("%d: Taking a step\n", _pid);
#endif

  /* Dequeue an event */
  PHILOSOPHER4_flags[USCXML_CTX_DEQUEUE_EXTERNAL] = false;
  if
  ::PHILOSOPHER4_flags[USCXML_CTX_SPONTANEOUS] -> {
    PHILOSOPHER4__event.name = USCXML_EVENT_SPONTANEOUS;

#if TRACE_EXECUTION
printf("%d: Trying with a spontaneous event\n", _pid);
#endif

  }
  :: else -> {
    if
    :: len(PHILOSOPHER4_iQ) != 0 -> {
      PHILOSOPHER4_iQ ? PHILOSOPHER4__event;

#if TRACE_EXECUTION
printf("%d: Deqeued an internal event\n", _pid);
#endif

    }
    :: else -> {
      PHILOSOPHER4_flags[USCXML_CTX_DEQUEUE_EXTERNAL] = true;
    }
    fi;
  }
  fi;


  if
  :: PHILOSOPHER4_flags[USCXML_CTX_DEQUEUE_EXTERNAL] -> {
    /* manage invocations */
    i = 0;
    do
    :: i < PHILOSOPHER4_USCXML_NUMBER_STATES -> {
      d_step { 
      /* uninvoke */
      if
      :: !PHILOSOPHER4_config[i] && PHILOSOPHER4_invocations[i] -> {

#if TRACE_EXECUTION
printf("%d: Uninvoking in state %d\n", _pid, i);
#endif

        if
        :: else -> skip;
        fi
        PHILOSOPHER4_invocations[i] = false;
        skip;
      }
      :: else -> skip;
      fi;
      } /* d_step */

      /* invoke */
      if
      :: PHILOSOPHER4_config[i] && !PHILOSOPHER4_invocations[i] -> {
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
    :: PHILOSOPHER4_flags[USCXML_CTX_FINISHED] -> {
      goto PHILOSOPHER4_TERMINATE_MACHINE;
    }
    :: else -> skip;
    fi
    /* Not sure if this should be before the invocation due to auto-forwarding */
    if
    :: len(PHILOSOPHER4_eQ) != 0 -> {
      PHILOSOPHER4_eQ ? PHILOSOPHER4__event;

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
PHILOSOPHER4_SELECT_TRANSITIONS:
PHILOSOPHER4_STATES_CLEAR(PHILOSOPHER4_ctx.target_set)
PHILOSOPHER4_STATES_CLEAR(PHILOSOPHER4_ctx.exit_set)
PHILOSOPHER4_TRANS_CLEAR(PHILOSOPHER4_ctx.conflicts)
PHILOSOPHER4_TRANS_CLEAR(PHILOSOPHER4_ctx.trans_set)
#if TRACE_EXECUTION
printf("%d: Establishing optimal transition set for event %d\n", _pid, PHILOSOPHER4__event.name );
#endif

#if TRACE_EXECUTION
printf("Configuration: ");
printf("%d%d%d%d%d%d%d%d", 
    PHILOSOPHER4_config[0], 
    PHILOSOPHER4_config[1], 
    PHILOSOPHER4_config[2], 
    PHILOSOPHER4_config[3], 
    PHILOSOPHER4_config[4], 
    PHILOSOPHER4_config[5], 
    PHILOSOPHER4_config[6], 
    PHILOSOPHER4_config[7]);
printf("\n");
#endif

  PHILOSOPHER4_flags[USCXML_CTX_TRANSITION_FOUND] = false;
  i = 0;
  do
  :: i < PHILOSOPHER4_USCXML_NUMBER_TRANS -> {
    /* only select non-history, non-initial transitions */
    if
    :: !PHILOSOPHER4_transitions[i].type[USCXML_TRANS_HISTORY] &&
       !PHILOSOPHER4_transitions[i].type[USCXML_TRANS_INITIAL] -> {
      if
      :: /* is the transition active? */
         PHILOSOPHER4_config[PHILOSOPHER4_transitions[i].source] && 

         /* is it non-conflicting? */
         !PHILOSOPHER4_ctx.conflicts[i] && 

         /* is it spontaneous with an event or vice versa? */
         ((PHILOSOPHER4__event.name == USCXML_EVENT_SPONTANEOUS && 
           PHILOSOPHER4_transitions[i].type[USCXML_TRANS_SPONTANEOUS]) || 
          (PHILOSOPHER4__event.name != USCXML_EVENT_SPONTANEOUS && 
           !PHILOSOPHER4_transitions[i].type[USCXML_TRANS_SPONTANEOUS])) &&

         /* is it matching and enabled? */
         (false 
          || (i == 0 && (false || PHILOSOPHER4__event.name == THINKING_OVER))
          || (i == 1 && (false || PHILOSOPHER4__event.name == TAKE_LEFT_FORK))
          || (i == 2 && (false || PHILOSOPHER4__event.name == TAKE_RIGHT_FORK))
          || (i == 3 && (false || PHILOSOPHER4__event.name == TIMEOUT))
          || (i == 4 && (false || PHILOSOPHER4__event.name == TAKE_RIGHT_FORK))
          || (i == 5 && (false || PHILOSOPHER4__event.name == RESEND_NEED_RIGHT_FORK))
          || (i == 6 && (false || PHILOSOPHER4__event.name == TIMEOUT))
          || (i == 7 && (false || PHILOSOPHER4__event.name == TAKE_LEFT_FORK))
          || (i == 8 && (false || PHILOSOPHER4__event.name == RESEND_NEED_LEFT_FORK))
          || (i == 9 && (false || PHILOSOPHER4__event.name == TIMEOUT))
          || (i == 10 && (false || PHILOSOPHER4__event.name == EATING_OVER))
         ) -> {
        /* remember that we found a transition */
        PHILOSOPHER4_flags[USCXML_CTX_TRANSITION_FOUND] = true;

        /* transitions that are pre-empted */
        PHILOSOPHER4_TRANS_OR(PHILOSOPHER4_ctx.conflicts, PHILOSOPHER4_transitions[i].conflicts)

        /* states that are directly targeted (resolve as entry-set later) */
        PHILOSOPHER4_STATES_OR(PHILOSOPHER4_ctx.target_set, PHILOSOPHER4_transitions[i].target)

        /* states that will be left */
        PHILOSOPHER4_STATES_OR(PHILOSOPHER4_ctx.exit_set, PHILOSOPHER4_transitions[i].exit_set)

        PHILOSOPHER4_ctx.trans_set[i] = true;
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
  PHILOSOPHER4_STATES_AND(PHILOSOPHER4_ctx.exit_set, PHILOSOPHER4_config)

#if TRACE_EXECUTION
printf("Selected Transitions: ");
printf("%d%d%d%d%d%d%d%d%d%d%d", 
    PHILOSOPHER4_ctx.trans_set[0], 
    PHILOSOPHER4_ctx.trans_set[1], 
    PHILOSOPHER4_ctx.trans_set[2], 
    PHILOSOPHER4_ctx.trans_set[3], 
    PHILOSOPHER4_ctx.trans_set[4], 
    PHILOSOPHER4_ctx.trans_set[5], 
    PHILOSOPHER4_ctx.trans_set[6], 
    PHILOSOPHER4_ctx.trans_set[7], 
    PHILOSOPHER4_ctx.trans_set[8], 
    PHILOSOPHER4_ctx.trans_set[9], 
    PHILOSOPHER4_ctx.trans_set[10]);
printf("\n");
#endif


#if TRACE_EXECUTION
printf("Target Set: ");
printf("%d%d%d%d%d%d%d%d", 
    PHILOSOPHER4_ctx.target_set[0], 
    PHILOSOPHER4_ctx.target_set[1], 
    PHILOSOPHER4_ctx.target_set[2], 
    PHILOSOPHER4_ctx.target_set[3], 
    PHILOSOPHER4_ctx.target_set[4], 
    PHILOSOPHER4_ctx.target_set[5], 
    PHILOSOPHER4_ctx.target_set[6], 
    PHILOSOPHER4_ctx.target_set[7]);
printf("\n");
#endif


#if TRACE_EXECUTION
printf("Exit Set: ");
printf("%d%d%d%d%d%d%d%d", 
    PHILOSOPHER4_ctx.exit_set[0], 
    PHILOSOPHER4_ctx.exit_set[1], 
    PHILOSOPHER4_ctx.exit_set[2], 
    PHILOSOPHER4_ctx.exit_set[3], 
    PHILOSOPHER4_ctx.exit_set[4], 
    PHILOSOPHER4_ctx.exit_set[5], 
    PHILOSOPHER4_ctx.exit_set[6], 
    PHILOSOPHER4_ctx.exit_set[7]);
printf("\n");
#endif

  if
  :: !PHILOSOPHER4_STATES_HAS_ANY(PHILOSOPHER4_config) -> {
    /* Enter initial configuration */
    PHILOSOPHER4_STATES_COPY(PHILOSOPHER4_ctx.target_set, PHILOSOPHER4_states[0].completion)
    PHILOSOPHER4_flags[USCXML_CTX_SPONTANEOUS] = true;
    PHILOSOPHER4_flags[USCXML_CTX_TRANSITION_FOUND] = true;

#if TRACE_EXECUTION
printf("%d: Entering initial default completion\n", _pid);
#endif


  }
  :: PHILOSOPHER4_flags[USCXML_CTX_TRANSITION_FOUND] -> {

#if TRACE_EXECUTION
printf("%d: Found transitions\n", _pid);
#endif

    PHILOSOPHER4_flags[USCXML_CTX_SPONTANEOUS] = true;
  }
  :: else {
    PHILOSOPHER4_flags[USCXML_CTX_SPONTANEOUS] = false;

#if TRACE_EXECUTION
printf("%d: Found NO transitions\n", _pid);
#endif

  }
  fi


  if
  :: PHILOSOPHER4_flags[USCXML_CTX_TRANSITION_FOUND] -> {
    /* only process anything if we found transitions or are on initial entry */
/* ---------------------------- */
/* REMEMBER_HISTORY: */

#if TRACE_EXECUTION
printf("%d: Save history configurations\n", _pid);
#endif

  if
  :: PHILOSOPHER4_STATES_HAS_ANY(PHILOSOPHER4_config) -> {
    /* only remember history on non-initial entry */
    i = 0;
    do
    :: i < PHILOSOPHER4_USCXML_NUMBER_STATES -> {
      if
      :: PHILOSOPHER4_states[i].type[USCXML_STATE_HISTORY_SHALLOW] ||
         PHILOSOPHER4_states[i].type[USCXML_STATE_HISTORY_DEEP] -> {
        if
        :: PHILOSOPHER4_ctx.exit_set[PHILOSOPHER4_states[i].parent] -> {
          /* a history state whose parent is about to be exited */

#if TRACE_EXECUTION
printf("%d: history state %d is about to be exited\n", _pid, i);
#endif


#if TRACE_EXECUTION
printf("COMPLET: ");
printf("%d%d%d%d%d%d%d%d", 
    PHILOSOPHER4_states[i].completion[0], 
    PHILOSOPHER4_states[i].completion[1], 
    PHILOSOPHER4_states[i].completion[2], 
    PHILOSOPHER4_states[i].completion[3], 
    PHILOSOPHER4_states[i].completion[4], 
    PHILOSOPHER4_states[i].completion[5], 
    PHILOSOPHER4_states[i].completion[6], 
    PHILOSOPHER4_states[i].completion[7]);
printf("\n");
#endif

          PHILOSOPHER4_STATES_COPY(PHILOSOPHER4_ctx.tmp_states, PHILOSOPHER4_states[i].completion)

          /* set those states who were enabled */
          PHILOSOPHER4_STATES_AND(PHILOSOPHER4_ctx.tmp_states, PHILOSOPHER4_config)

#if TRACE_EXECUTION
printf("CONFIG : ");
printf("%d%d%d%d%d%d%d%d", 
    PHILOSOPHER4_config[0], 
    PHILOSOPHER4_config[1], 
    PHILOSOPHER4_config[2], 
    PHILOSOPHER4_config[3], 
    PHILOSOPHER4_config[4], 
    PHILOSOPHER4_config[5], 
    PHILOSOPHER4_config[6], 
    PHILOSOPHER4_config[7]);
printf("\n");
#endif


#if TRACE_EXECUTION
printf("TMP_STS: ");
printf("%d%d%d%d%d%d%d%d", 
    PHILOSOPHER4_ctx.tmp_states[0], 
    PHILOSOPHER4_ctx.tmp_states[1], 
    PHILOSOPHER4_ctx.tmp_states[2], 
    PHILOSOPHER4_ctx.tmp_states[3], 
    PHILOSOPHER4_ctx.tmp_states[4], 
    PHILOSOPHER4_ctx.tmp_states[5], 
    PHILOSOPHER4_ctx.tmp_states[6], 
    PHILOSOPHER4_ctx.tmp_states[7]);
printf("\n");
#endif


          /* clear current history with completion mask */
          PHILOSOPHER4_STATES_AND_NOT(PHILOSOPHER4_history, PHILOSOPHER4_states[i].completion)

          /* set history */
          PHILOSOPHER4_STATES_OR(PHILOSOPHER4_history, PHILOSOPHER4_ctx.tmp_states)

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
printf("%d%d%d%d%d%d%d%d", 
    PHILOSOPHER4_history[0], 
    PHILOSOPHER4_history[1], 
    PHILOSOPHER4_history[2], 
    PHILOSOPHER4_history[3], 
    PHILOSOPHER4_history[4], 
    PHILOSOPHER4_history[5], 
    PHILOSOPHER4_history[6], 
    PHILOSOPHER4_history[7]);
printf("\n");
#endif
  }
  :: else -> skip;
  fi;

/* ---------------------------- */
PHILOSOPHER4_ESTABLISH_ENTRY_SET:
  /* calculate new entry set */
  PHILOSOPHER4_STATES_COPY(PHILOSOPHER4_ctx.entry_set, PHILOSOPHER4_ctx.target_set)

  i = 0;
  do
  :: i < PHILOSOPHER4_USCXML_NUMBER_STATES -> {
    if
    :: PHILOSOPHER4_ctx.entry_set[i] -> {
      /* ancestor completion */
      PHILOSOPHER4_STATES_OR(PHILOSOPHER4_ctx.entry_set, PHILOSOPHER4_states[i].ancestors)
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
  :: i < PHILOSOPHER4_USCXML_NUMBER_STATES -> {
    if
    :: PHILOSOPHER4_ctx.entry_set[i] -> {
      if
      :: PHILOSOPHER4_states[i].type[USCXML_STATE_PARALLEL] -> {
        PHILOSOPHER4_STATES_OR(PHILOSOPHER4_ctx.entry_set, PHILOSOPHER4_states[i].completion)
      }
      :: PHILOSOPHER4_states[i].type[USCXML_STATE_HISTORY_SHALLOW] ||
         PHILOSOPHER4_states[i].type[USCXML_STATE_HISTORY_DEEP] -> {

#if TRACE_EXECUTION
printf("%d: Descendant completion for history state %d\n", _pid, i);
#endif

        if
        :: !PHILOSOPHER4_STATES_HAS_AND(PHILOSOPHER4_states[i].completion, PHILOSOPHER4_history) && !PHILOSOPHER4_config[PHILOSOPHER4_states[i].parent] -> {
          /* nothing set for history, look for a default transition */

#if TRACE_EXECUTION
printf("%d: Fresh history in target set\n", _pid);
#endif

          j = 0;
          do
          :: j < PHILOSOPHER4_USCXML_NUMBER_TRANS -> {
             if
             :: PHILOSOPHER4_transitions[j].source == i -> {
               PHILOSOPHER4_ctx.trans_set[j] = true;
               PHILOSOPHER4_STATES_OR(PHILOSOPHER4_ctx.entry_set, PHILOSOPHER4_transitions[j].target)

               if
               :: (PHILOSOPHER4_states[i].type[USCXML_STATE_HISTORY_DEEP] &&
                   !PHILOSOPHER4_STATES_HAS_AND(PHILOSOPHER4_transitions[j].target, PHILOSOPHER4_states[i].children)                  ) -> {
                 k = i + 1
                 do
                 :: k < PHILOSOPHER4_USCXML_NUMBER_STATES -> {
                   if
                   :: PHILOSOPHER4_transitions[j].target[k] -> {
                     PHILOSOPHER4_STATES_OR(PHILOSOPHER4_ctx.entry_set, PHILOSOPHER4_states[k].ancestors)
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

          PHILOSOPHER4_STATES_COPY(PHILOSOPHER4_ctx.tmp_states, PHILOSOPHER4_states[i].completion)
          PHILOSOPHER4_STATES_AND(PHILOSOPHER4_ctx.tmp_states, PHILOSOPHER4_history)
          PHILOSOPHER4_STATES_OR(PHILOSOPHER4_ctx.entry_set, PHILOSOPHER4_ctx.tmp_states)
          if
          :: PHILOSOPHER4_states[i].type[USCXML_STATE_HAS_HISTORY] ||
             PHILOSOPHER4_states[i].type[USCXML_STATE_HISTORY_DEEP] -> { 
            /* a deep history state with nested histories -> more completion */

#if TRACE_EXECUTION
printf("%d: DEEP HISTORY\n", _pid);
#endif

            j = i + 1;
            do
            :: j < PHILOSOPHER4_USCXML_NUMBER_STATES -> {
              if
              :: (PHILOSOPHER4_states[i].completion[j] &&
                  PHILOSOPHER4_ctx.entry_set[j] && 
                  PHILOSOPHER4_states[j].type[USCXML_STATE_HAS_HISTORY]) -> {
                k = j + 1;
                do
                :: k < PHILOSOPHER4_USCXML_NUMBER_STATES -> {
                  /* add nested history to entry_set */
                  if
                  :: (PHILOSOPHER4_states[k].type[USCXML_STATE_HISTORY_DEEP] ||
                      PHILOSOPHER4_states[k].type[USCXML_STATE_HISTORY_SHALLOW]) &&
                     PHILOSOPHER4_states[j].children[k] -> {
                    /* a nested history state */
                    PHILOSOPHER4_ctx.entry_set[k] = true;
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
      :: PHILOSOPHER4_states[i].type[USCXML_STATE_INITIAL] -> {

#if TRACE_EXECUTION
printf("%d: Descendant completion for initial state %d\n", _pid, i);
#endif

        j = 0
        do
        :: j < PHILOSOPHER4_USCXML_NUMBER_TRANS -> {
          if
          :: PHILOSOPHER4_transitions[j].source == i -> {
            PHILOSOPHER4_ctx.trans_set[j] = true;
            PHILOSOPHER4_ctx.entry_set[i] = false;

#if TRACE_EXECUTION
printf("%d: Adding transition %d!\n", _pid, j);
#endif

            PHILOSOPHER4_STATES_OR(PHILOSOPHER4_ctx.entry_set, PHILOSOPHER4_transitions[j].target)

            k = i + 1;
            do
            :: k < PHILOSOPHER4_USCXML_NUMBER_STATES -> {
              if
              :: PHILOSOPHER4_transitions[j].target[k] -> {
                PHILOSOPHER4_STATES_OR(PHILOSOPHER4_ctx.entry_set, PHILOSOPHER4_states[k].ancestors)

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
      :: PHILOSOPHER4_states[i].type[USCXML_STATE_COMPOUND] -> {
        /* we need to check whether one child is already in entry_set */
        if
        :: (
          !PHILOSOPHER4_STATES_HAS_AND(PHILOSOPHER4_ctx.entry_set, PHILOSOPHER4_states[i].children) && 
           (!PHILOSOPHER4_STATES_HAS_AND(PHILOSOPHER4_config, PHILOSOPHER4_states[i].children) || PHILOSOPHER4_STATES_HAS_AND(PHILOSOPHER4_ctx.exit_set, PHILOSOPHER4_states[i].children)
)) 
        -> {
          PHILOSOPHER4_STATES_OR(PHILOSOPHER4_ctx.entry_set, PHILOSOPHER4_states[i].completion)
          if
          :: (PHILOSOPHER4_STATES_HAS_AND(PHILOSOPHER4_states[i].completion, PHILOSOPHER4_states[i].children)
          ) -> {
            /* deep completion */
            j = i + 1;
            do
            :: j < PHILOSOPHER4_USCXML_NUMBER_STATES - 1 -> {
              j = j + 1;
              if
              :: PHILOSOPHER4_states[i].completion[j] -> {
                PHILOSOPHER4_STATES_OR(PHILOSOPHER4_ctx.entry_set, PHILOSOPHER4_states[j].ancestors)

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
printf("%d%d%d%d%d%d%d%d", 
    PHILOSOPHER4_ctx.entry_set[0], 
    PHILOSOPHER4_ctx.entry_set[1], 
    PHILOSOPHER4_ctx.entry_set[2], 
    PHILOSOPHER4_ctx.entry_set[3], 
    PHILOSOPHER4_ctx.entry_set[4], 
    PHILOSOPHER4_ctx.entry_set[5], 
    PHILOSOPHER4_ctx.entry_set[6], 
    PHILOSOPHER4_ctx.entry_set[7]);
printf("\n");
#endif


/* ---------------------------- */
/* EXIT_STATES: */
  i = PHILOSOPHER4_USCXML_NUMBER_STATES;
  do
  :: i > 0 -> {
    i = i - 1;
    if
    :: PHILOSOPHER4_ctx.exit_set[i] && PHILOSOPHER4_config[i] -> {
      /* call all on-exit handlers */

#if TRACE_EXECUTION
printf("%d: Exiting state %d\n", _pid, i);
#endif

      if
      :: i == 3 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for exiting state %d\n", _pid, i);
#endif

      if
      :: (PHILOSOPHER4__event.name == TAKE_LEFT_FORK || PHILOSOPHER4__event.name == TAKE_RIGHT_FORK) -> {
          cancelSendId(STARVATION_TIMER,PHILOSOPHER4);
      }
      :: else -> skip;
      fi;
      }
      :: i == 4 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for exiting state %d\n", _pid, i);
#endif

      if
      :: (PHILOSOPHER4__event.name == TAKE_RIGHT_FORK) -> {
          cancelSendId(STARVATION_TIMER,PHILOSOPHER4);
      }
      :: else -> skip;
      fi;
      }
      :: i == 5 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for exiting state %d\n", _pid, i);
#endif

      if
      :: (PHILOSOPHER4__event.name == TAKE_LEFT_FORK) -> {
          cancelSendId(STARVATION_TIMER,PHILOSOPHER4);
      }
      :: else -> skip;
      fi;
      }
      :: else -> skip;
      fi

      PHILOSOPHER4_config[i] = false;
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
  :: i < PHILOSOPHER4_USCXML_NUMBER_TRANS -> {
    if
    :: PHILOSOPHER4_ctx.trans_set[i] && 
       !PHILOSOPHER4_transitions[i].type[USCXML_TRANS_HISTORY] && 
       !PHILOSOPHER4_transitions[i].type[USCXML_TRANS_INITIAL] -> {
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

        printf("philospher: : %d", PHILOSOPHER4_p_id);
        printf("starved in state hungry for Time(in ms) : : %d", PHILOSOPHER4_delay);
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
        :: !PHILOSOPHER4_flags[USCXML_CTX_FINISHED] || PHILOSOPHER4_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
          {
            PHILOSOPHER4__tmpE.data.p_id = 0;
            PHILOSOPHER4__tmpE.delay = 0;
            PHILOSOPHER4__tmpE.invokeid = 0;
            PHILOSOPHER4__tmpE.name = 0;
            PHILOSOPHER4__tmpE.origin = 0;
            PHILOSOPHER4__tmpE.sendid = 0;
            PHILOSOPHER4__tmpE.seqNr = 0;
            PHILOSOPHER4__tmpE.name = NEED_RIGHT_FORK;
            PHILOSOPHER4__tmpE.invokeid = PHILOSOPHER4;
            PHILOSOPHER4__tmpE.origin = PHILOSOPHER4;
            _lastSeqId = _lastSeqId + 1;
            PHILOSOPHER4__tmpE.delay = 0;
            PHILOSOPHER4__tmpE.seqNr = _lastSeqId;
            PHILOSOPHER4__tmpE.data.p_id = PHILOSOPHER4_p_id;
#if TRACE_EXECUTION
printf("%d: Sending NEED_RIGHT_FORK (%d) to ROOT_eQ\n", _pid, PHILOSOPHER4__tmpE.name );
#endif

            ROOT_eQ!PHILOSOPHER4__tmpE;
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

        printf("philospher: : %d", PHILOSOPHER4_p_id);
        printf("starved in state has_right_fork for Time(in ms) :: %d", PHILOSOPHER4_delay);
        skip;
      }
      :: i == 7 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, i);
#endif

        skip;
      }
      :: i == 8 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, i);
#endif

        if
        :: !PHILOSOPHER4_flags[USCXML_CTX_FINISHED] || PHILOSOPHER4_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
          {
            PHILOSOPHER4__tmpE.data.p_id = 0;
            PHILOSOPHER4__tmpE.delay = 0;
            PHILOSOPHER4__tmpE.invokeid = 0;
            PHILOSOPHER4__tmpE.name = 0;
            PHILOSOPHER4__tmpE.origin = 0;
            PHILOSOPHER4__tmpE.sendid = 0;
            PHILOSOPHER4__tmpE.seqNr = 0;
            PHILOSOPHER4__tmpE.name = NEED_LEFT_FORK;
            PHILOSOPHER4__tmpE.invokeid = PHILOSOPHER4;
            PHILOSOPHER4__tmpE.origin = PHILOSOPHER4;
            _lastSeqId = _lastSeqId + 1;
            PHILOSOPHER4__tmpE.delay = 0;
            PHILOSOPHER4__tmpE.seqNr = _lastSeqId;
            PHILOSOPHER4__tmpE.data.p_id = PHILOSOPHER4_p_id;
#if TRACE_EXECUTION
printf("%d: Sending NEED_LEFT_FORK (%d) to ROOT_eQ\n", _pid, PHILOSOPHER4__tmpE.name );
#endif

            ROOT_eQ!PHILOSOPHER4__tmpE;
            insertWithDelay(ROOT_eQ);
          }
          skip;
        }
        :: else -> skip;
        fi
        skip;
      }
      :: i == 9 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, i);
#endif

        printf("philospher: : %d", PHILOSOPHER4_p_id);
        printf("starved in state has_right_fork for Time(in ms) : : %d", PHILOSOPHER4_delay);
        skip;
      }
      :: i == 10 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, i);
#endif

        if
        :: !PHILOSOPHER4_flags[USCXML_CTX_FINISHED] || PHILOSOPHER4_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
          {
            PHILOSOPHER4__tmpE.data.p_id = 0;
            PHILOSOPHER4__tmpE.delay = 0;
            PHILOSOPHER4__tmpE.invokeid = 0;
            PHILOSOPHER4__tmpE.name = 0;
            PHILOSOPHER4__tmpE.origin = 0;
            PHILOSOPHER4__tmpE.sendid = 0;
            PHILOSOPHER4__tmpE.seqNr = 0;
            PHILOSOPHER4__tmpE.name = RETURN_FORKS;
            PHILOSOPHER4__tmpE.invokeid = PHILOSOPHER4;
            PHILOSOPHER4__tmpE.origin = PHILOSOPHER4;
            _lastSeqId = _lastSeqId + 1;
            PHILOSOPHER4__tmpE.delay = 0;
            PHILOSOPHER4__tmpE.seqNr = _lastSeqId;
            PHILOSOPHER4__tmpE.data.p_id = PHILOSOPHER4_p_id;
#if TRACE_EXECUTION
printf("%d: Sending RETURN_FORKS (%d) to ROOT_eQ\n", _pid, PHILOSOPHER4__tmpE.name );
#endif

            ROOT_eQ!PHILOSOPHER4__tmpE;
            insertWithDelay(ROOT_eQ);
          }
          skip;
        }
        :: else -> skip;
        fi
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
  :: i < PHILOSOPHER4_USCXML_NUMBER_STATES -> {
    if
    :: (PHILOSOPHER4_ctx.entry_set[i] &&
        !PHILOSOPHER4_config[i] && 
        /* these are no proper states */
        !PHILOSOPHER4_states[i].type[USCXML_STATE_HISTORY_DEEP] && 
        !PHILOSOPHER4_states[i].type[USCXML_STATE_HISTORY_SHALLOW] && 
        !PHILOSOPHER4_states[i].type[USCXML_STATE_INITIAL]
       ) -> {

#if TRACE_EXECUTION
printf("%d: Entering state %d\n", _pid, i);
#endif

         PHILOSOPHER4_config[i] = true;

         /* Process executable content for entering a state */
         if
         :: i == 1 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for entering state %d\n", _pid, i);
#endif

          printf("Hello, I am philospher number: : %d", PHILOSOPHER4_p_id);
         }
         :: i == 2 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for entering state %d\n", _pid, i);
#endif

          printf("Thinking philosopher: : %d", PHILOSOPHER4_p_id);
            PHILOSOPHER4_random_delay = ((1103515245*PHILOSOPHER4_random_delay+12345)%2147483647)%2000;
          if
          :: !PHILOSOPHER4_flags[USCXML_CTX_FINISHED] || PHILOSOPHER4_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
            {
              PHILOSOPHER4__tmpE.data.p_id = 0;
              PHILOSOPHER4__tmpE.delay = 0;
              PHILOSOPHER4__tmpE.invokeid = 0;
              PHILOSOPHER4__tmpE.name = 0;
              PHILOSOPHER4__tmpE.origin = 0;
              PHILOSOPHER4__tmpE.sendid = 0;
              PHILOSOPHER4__tmpE.seqNr = 0;
              PHILOSOPHER4__tmpE.name = THINKING_OVER;
              PHILOSOPHER4__tmpE.invokeid = PHILOSOPHER4;
              PHILOSOPHER4__tmpE.origin = PHILOSOPHER4;
              _lastSeqId = _lastSeqId + 1;
              PHILOSOPHER4__tmpE.delay = PHILOSOPHER4_random_delay*(PHILOSOPHER4_p_id+1);
              PHILOSOPHER4__tmpE.seqNr = _lastSeqId;
#if TRACE_EXECUTION
printf("%d: Sending THINKING_OVER (%d) to PHILOSOPHER4_eQ\n", _pid, PHILOSOPHER4__tmpE.name );
#endif

              PHILOSOPHER4_eQ!PHILOSOPHER4__tmpE;
              insertWithDelay(PHILOSOPHER4_eQ);
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

          printf("Hungry philosopher: : %d", PHILOSOPHER4_p_id);
          if
          :: !PHILOSOPHER4_flags[USCXML_CTX_FINISHED] || PHILOSOPHER4_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
            {
              PHILOSOPHER4__tmpE.data.p_id = 0;
              PHILOSOPHER4__tmpE.delay = 0;
              PHILOSOPHER4__tmpE.invokeid = 0;
              PHILOSOPHER4__tmpE.name = 0;
              PHILOSOPHER4__tmpE.origin = 0;
              PHILOSOPHER4__tmpE.sendid = 0;
              PHILOSOPHER4__tmpE.seqNr = 0;
              PHILOSOPHER4__tmpE.name = TIMEOUT;
              PHILOSOPHER4__tmpE.sendid = STARVATION_TIMER;
              PHILOSOPHER4__tmpE.invokeid = PHILOSOPHER4;
              PHILOSOPHER4__tmpE.origin = PHILOSOPHER4;
              _lastSeqId = _lastSeqId + 1;
              PHILOSOPHER4__tmpE.delay = PHILOSOPHER4_delay;
              PHILOSOPHER4__tmpE.seqNr = _lastSeqId;
#if TRACE_EXECUTION
printf("%d: Sending TIMEOUT (%d) to PHILOSOPHER4_eQ\n", _pid, PHILOSOPHER4__tmpE.name );
#endif

              PHILOSOPHER4_eQ!PHILOSOPHER4__tmpE;
              insertWithDelay(PHILOSOPHER4_eQ);
            }
            skip;
          }
          :: else -> skip;
          fi
          if
          :: !PHILOSOPHER4_flags[USCXML_CTX_FINISHED] || PHILOSOPHER4_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
            {
              PHILOSOPHER4__tmpE.data.p_id = 0;
              PHILOSOPHER4__tmpE.delay = 0;
              PHILOSOPHER4__tmpE.invokeid = 0;
              PHILOSOPHER4__tmpE.name = 0;
              PHILOSOPHER4__tmpE.origin = 0;
              PHILOSOPHER4__tmpE.sendid = 0;
              PHILOSOPHER4__tmpE.seqNr = 0;
              PHILOSOPHER4__tmpE.name = NEED_LEFT_FORK;
              PHILOSOPHER4__tmpE.invokeid = PHILOSOPHER4;
              PHILOSOPHER4__tmpE.origin = PHILOSOPHER4;
              _lastSeqId = _lastSeqId + 1;
              PHILOSOPHER4__tmpE.delay = 0;
              PHILOSOPHER4__tmpE.seqNr = _lastSeqId;
              PHILOSOPHER4__tmpE.data.p_id = PHILOSOPHER4_p_id;
#if TRACE_EXECUTION
printf("%d: Sending NEED_LEFT_FORK (%d) to ROOT_eQ\n", _pid, PHILOSOPHER4__tmpE.name );
#endif

              ROOT_eQ!PHILOSOPHER4__tmpE;
              insertWithDelay(ROOT_eQ);
            }
            skip;
          }
          :: else -> skip;
          fi
          if
          :: !PHILOSOPHER4_flags[USCXML_CTX_FINISHED] || PHILOSOPHER4_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
            {
              PHILOSOPHER4__tmpE.data.p_id = 0;
              PHILOSOPHER4__tmpE.delay = 0;
              PHILOSOPHER4__tmpE.invokeid = 0;
              PHILOSOPHER4__tmpE.name = 0;
              PHILOSOPHER4__tmpE.origin = 0;
              PHILOSOPHER4__tmpE.sendid = 0;
              PHILOSOPHER4__tmpE.seqNr = 0;
              PHILOSOPHER4__tmpE.name = NEED_RIGHT_FORK;
              PHILOSOPHER4__tmpE.invokeid = PHILOSOPHER4;
              PHILOSOPHER4__tmpE.origin = PHILOSOPHER4;
              _lastSeqId = _lastSeqId + 1;
              PHILOSOPHER4__tmpE.delay = 0;
              PHILOSOPHER4__tmpE.seqNr = _lastSeqId;
              PHILOSOPHER4__tmpE.data.p_id = PHILOSOPHER4_p_id;
#if TRACE_EXECUTION
printf("%d: Sending NEED_RIGHT_FORK (%d) to ROOT_eQ\n", _pid, PHILOSOPHER4__tmpE.name );
#endif

              ROOT_eQ!PHILOSOPHER4__tmpE;
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

          printf("in state has_left_fork for philosopher: : %d", PHILOSOPHER4_p_id);
          if
          :: !PHILOSOPHER4_flags[USCXML_CTX_FINISHED] || PHILOSOPHER4_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
            {
              PHILOSOPHER4__tmpE.data.p_id = 0;
              PHILOSOPHER4__tmpE.delay = 0;
              PHILOSOPHER4__tmpE.invokeid = 0;
              PHILOSOPHER4__tmpE.name = 0;
              PHILOSOPHER4__tmpE.origin = 0;
              PHILOSOPHER4__tmpE.sendid = 0;
              PHILOSOPHER4__tmpE.seqNr = 0;
              PHILOSOPHER4__tmpE.name = TIMEOUT;
              PHILOSOPHER4__tmpE.sendid = STARVATION_TIMER;
              PHILOSOPHER4__tmpE.invokeid = PHILOSOPHER4;
              PHILOSOPHER4__tmpE.origin = PHILOSOPHER4;
              _lastSeqId = _lastSeqId + 1;
              PHILOSOPHER4__tmpE.delay = PHILOSOPHER4_delay;
              PHILOSOPHER4__tmpE.seqNr = _lastSeqId;
#if TRACE_EXECUTION
printf("%d: Sending TIMEOUT (%d) to PHILOSOPHER4_eQ\n", _pid, PHILOSOPHER4__tmpE.name );
#endif

              PHILOSOPHER4_eQ!PHILOSOPHER4__tmpE;
              insertWithDelay(PHILOSOPHER4_eQ);
            }
            skip;
          }
          :: else -> skip;
          fi
          if
          :: !PHILOSOPHER4_flags[USCXML_CTX_FINISHED] || PHILOSOPHER4_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
            {
              PHILOSOPHER4__tmpE.data.p_id = 0;
              PHILOSOPHER4__tmpE.delay = 0;
              PHILOSOPHER4__tmpE.invokeid = 0;
              PHILOSOPHER4__tmpE.name = 0;
              PHILOSOPHER4__tmpE.origin = 0;
              PHILOSOPHER4__tmpE.sendid = 0;
              PHILOSOPHER4__tmpE.seqNr = 0;
              PHILOSOPHER4__tmpE.name = RESEND_NEED_RIGHT_FORK;
              PHILOSOPHER4__tmpE.invokeid = PHILOSOPHER4;
              PHILOSOPHER4__tmpE.origin = PHILOSOPHER4;
              _lastSeqId = _lastSeqId + 1;
              PHILOSOPHER4__tmpE.delay = 500;
              PHILOSOPHER4__tmpE.seqNr = _lastSeqId;
#if TRACE_EXECUTION
printf("%d: Sending RESEND_NEED_RIGHT_FORK (%d) to PHILOSOPHER4_eQ\n", _pid, PHILOSOPHER4__tmpE.name );
#endif

              PHILOSOPHER4_eQ!PHILOSOPHER4__tmpE;
              insertWithDelay(PHILOSOPHER4_eQ);
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

          printf("in state has_right_fork for philosopher: : %d", PHILOSOPHER4_p_id);
          if
          :: !PHILOSOPHER4_flags[USCXML_CTX_FINISHED] || PHILOSOPHER4_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
            {
              PHILOSOPHER4__tmpE.data.p_id = 0;
              PHILOSOPHER4__tmpE.delay = 0;
              PHILOSOPHER4__tmpE.invokeid = 0;
              PHILOSOPHER4__tmpE.name = 0;
              PHILOSOPHER4__tmpE.origin = 0;
              PHILOSOPHER4__tmpE.sendid = 0;
              PHILOSOPHER4__tmpE.seqNr = 0;
              PHILOSOPHER4__tmpE.name = TIMEOUT;
              PHILOSOPHER4__tmpE.sendid = STARVATION_TIMER;
              PHILOSOPHER4__tmpE.invokeid = PHILOSOPHER4;
              PHILOSOPHER4__tmpE.origin = PHILOSOPHER4;
              _lastSeqId = _lastSeqId + 1;
              PHILOSOPHER4__tmpE.delay = PHILOSOPHER4_delay;
              PHILOSOPHER4__tmpE.seqNr = _lastSeqId;
#if TRACE_EXECUTION
printf("%d: Sending TIMEOUT (%d) to PHILOSOPHER4_eQ\n", _pid, PHILOSOPHER4__tmpE.name );
#endif

              PHILOSOPHER4_eQ!PHILOSOPHER4__tmpE;
              insertWithDelay(PHILOSOPHER4_eQ);
            }
            skip;
          }
          :: else -> skip;
          fi
          if
          :: !PHILOSOPHER4_flags[USCXML_CTX_FINISHED] || PHILOSOPHER4_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
            {
              PHILOSOPHER4__tmpE.data.p_id = 0;
              PHILOSOPHER4__tmpE.delay = 0;
              PHILOSOPHER4__tmpE.invokeid = 0;
              PHILOSOPHER4__tmpE.name = 0;
              PHILOSOPHER4__tmpE.origin = 0;
              PHILOSOPHER4__tmpE.sendid = 0;
              PHILOSOPHER4__tmpE.seqNr = 0;
              PHILOSOPHER4__tmpE.name = RESEND_NEED_LEFT_FORK;
              PHILOSOPHER4__tmpE.invokeid = PHILOSOPHER4;
              PHILOSOPHER4__tmpE.origin = PHILOSOPHER4;
              _lastSeqId = _lastSeqId + 1;
              PHILOSOPHER4__tmpE.delay = 500;
              PHILOSOPHER4__tmpE.seqNr = _lastSeqId;
#if TRACE_EXECUTION
printf("%d: Sending RESEND_NEED_LEFT_FORK (%d) to PHILOSOPHER4_eQ\n", _pid, PHILOSOPHER4__tmpE.name );
#endif

              PHILOSOPHER4_eQ!PHILOSOPHER4__tmpE;
              insertWithDelay(PHILOSOPHER4_eQ);
            }
            skip;
          }
          :: else -> skip;
          fi
         }
         :: i == 6 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for entering state %d\n", _pid, i);
#endif

          printf("Eating philosopher: : %d", PHILOSOPHER4_p_id);
          if
          :: !PHILOSOPHER4_flags[USCXML_CTX_FINISHED] || PHILOSOPHER4_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
            {
              PHILOSOPHER4__tmpE.data.p_id = 0;
              PHILOSOPHER4__tmpE.delay = 0;
              PHILOSOPHER4__tmpE.invokeid = 0;
              PHILOSOPHER4__tmpE.name = 0;
              PHILOSOPHER4__tmpE.origin = 0;
              PHILOSOPHER4__tmpE.sendid = 0;
              PHILOSOPHER4__tmpE.seqNr = 0;
              PHILOSOPHER4__tmpE.name = EATING_OVER;
              PHILOSOPHER4__tmpE.invokeid = PHILOSOPHER4;
              PHILOSOPHER4__tmpE.origin = PHILOSOPHER4;
              _lastSeqId = _lastSeqId + 1;
              PHILOSOPHER4__tmpE.delay = PHILOSOPHER4_random_delay;
              PHILOSOPHER4__tmpE.seqNr = _lastSeqId;
#if TRACE_EXECUTION
printf("%d: Sending EATING_OVER (%d) to PHILOSOPHER4_eQ\n", _pid, PHILOSOPHER4__tmpE.name );
#endif

              PHILOSOPHER4_eQ!PHILOSOPHER4__tmpE;
              insertWithDelay(PHILOSOPHER4_eQ);
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
         :: j < PHILOSOPHER4_USCXML_NUMBER_TRANS -> {
           if
           :: (PHILOSOPHER4_ctx.trans_set[j] &&
              (PHILOSOPHER4_transitions[j].type[USCXML_TRANS_HISTORY] ||
               PHILOSOPHER4_transitions[j].type[USCXML_TRANS_INITIAL]) && 
               PHILOSOPHER4_states[PHILOSOPHER4_transitions[j].source].parent == i) -> {
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

                printf("philospher: : %d", PHILOSOPHER4_p_id);
                printf("starved in state hungry for Time(in ms) : : %d", PHILOSOPHER4_delay);
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
                :: !PHILOSOPHER4_flags[USCXML_CTX_FINISHED] || PHILOSOPHER4_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
                  {
                    PHILOSOPHER4__tmpE.data.p_id = 0;
                    PHILOSOPHER4__tmpE.delay = 0;
                    PHILOSOPHER4__tmpE.invokeid = 0;
                    PHILOSOPHER4__tmpE.name = 0;
                    PHILOSOPHER4__tmpE.origin = 0;
                    PHILOSOPHER4__tmpE.sendid = 0;
                    PHILOSOPHER4__tmpE.seqNr = 0;
                    PHILOSOPHER4__tmpE.name = NEED_RIGHT_FORK;
                    PHILOSOPHER4__tmpE.invokeid = PHILOSOPHER4;
                    PHILOSOPHER4__tmpE.origin = PHILOSOPHER4;
                    _lastSeqId = _lastSeqId + 1;
                    PHILOSOPHER4__tmpE.delay = 0;
                    PHILOSOPHER4__tmpE.seqNr = _lastSeqId;
                    PHILOSOPHER4__tmpE.data.p_id = PHILOSOPHER4_p_id;
#if TRACE_EXECUTION
printf("%d: Sending NEED_RIGHT_FORK (%d) to ROOT_eQ\n", _pid, PHILOSOPHER4__tmpE.name );
#endif

                    ROOT_eQ!PHILOSOPHER4__tmpE;
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

                printf("philospher: : %d", PHILOSOPHER4_p_id);
                printf("starved in state has_right_fork for Time(in ms) :: %d", PHILOSOPHER4_delay);
                skip;
              }
              :: j == 7 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, j);
#endif

                skip;
              }
              :: j == 8 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, j);
#endif

                if
                :: !PHILOSOPHER4_flags[USCXML_CTX_FINISHED] || PHILOSOPHER4_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
                  {
                    PHILOSOPHER4__tmpE.data.p_id = 0;
                    PHILOSOPHER4__tmpE.delay = 0;
                    PHILOSOPHER4__tmpE.invokeid = 0;
                    PHILOSOPHER4__tmpE.name = 0;
                    PHILOSOPHER4__tmpE.origin = 0;
                    PHILOSOPHER4__tmpE.sendid = 0;
                    PHILOSOPHER4__tmpE.seqNr = 0;
                    PHILOSOPHER4__tmpE.name = NEED_LEFT_FORK;
                    PHILOSOPHER4__tmpE.invokeid = PHILOSOPHER4;
                    PHILOSOPHER4__tmpE.origin = PHILOSOPHER4;
                    _lastSeqId = _lastSeqId + 1;
                    PHILOSOPHER4__tmpE.delay = 0;
                    PHILOSOPHER4__tmpE.seqNr = _lastSeqId;
                    PHILOSOPHER4__tmpE.data.p_id = PHILOSOPHER4_p_id;
#if TRACE_EXECUTION
printf("%d: Sending NEED_LEFT_FORK (%d) to ROOT_eQ\n", _pid, PHILOSOPHER4__tmpE.name );
#endif

                    ROOT_eQ!PHILOSOPHER4__tmpE;
                    insertWithDelay(ROOT_eQ);
                  }
                  skip;
                }
                :: else -> skip;
                fi
                skip;
              }
              :: j == 9 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, j);
#endif

                printf("philospher: : %d", PHILOSOPHER4_p_id);
                printf("starved in state has_right_fork for Time(in ms) : : %d", PHILOSOPHER4_delay);
                skip;
              }
              :: j == 10 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, j);
#endif

                if
                :: !PHILOSOPHER4_flags[USCXML_CTX_FINISHED] || PHILOSOPHER4_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
                  {
                    PHILOSOPHER4__tmpE.data.p_id = 0;
                    PHILOSOPHER4__tmpE.delay = 0;
                    PHILOSOPHER4__tmpE.invokeid = 0;
                    PHILOSOPHER4__tmpE.name = 0;
                    PHILOSOPHER4__tmpE.origin = 0;
                    PHILOSOPHER4__tmpE.sendid = 0;
                    PHILOSOPHER4__tmpE.seqNr = 0;
                    PHILOSOPHER4__tmpE.name = RETURN_FORKS;
                    PHILOSOPHER4__tmpE.invokeid = PHILOSOPHER4;
                    PHILOSOPHER4__tmpE.origin = PHILOSOPHER4;
                    _lastSeqId = _lastSeqId + 1;
                    PHILOSOPHER4__tmpE.delay = 0;
                    PHILOSOPHER4__tmpE.seqNr = _lastSeqId;
                    PHILOSOPHER4__tmpE.data.p_id = PHILOSOPHER4_p_id;
#if TRACE_EXECUTION
printf("%d: Sending RETURN_FORKS (%d) to ROOT_eQ\n", _pid, PHILOSOPHER4__tmpE.name );
#endif

                    ROOT_eQ!PHILOSOPHER4__tmpE;
                    insertWithDelay(ROOT_eQ);
                  }
                  skip;
                }
                :: else -> skip;
                fi
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
         :: PHILOSOPHER4_states[i].type[USCXML_STATE_FINAL] -> {
           if
           :: PHILOSOPHER4_states[PHILOSOPHER4_states[i].parent].children[1] -> {
             /* exit topmost SCXML state */
             PHILOSOPHER4_flags[USCXML_CTX_TOP_LEVEL_FINAL] = true;
             PHILOSOPHER4_flags[USCXML_CTX_FINISHED] = true;
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
            :: j < PHILOSOPHER4_USCXML_NUMBER_STATES -> {
              if
              :: PHILOSOPHER4_states[j].type[USCXML_STATE_PARALLEL] && PHILOSOPHER4_states[i].ancestors[j] -> {
                PHILOSOPHER4_STATES_CLEAR(PHILOSOPHER4_ctx.tmp_states)
                k = 0;
                do
                :: k < PHILOSOPHER4_USCXML_NUMBER_STATES -> {
                  if
                  :: PHILOSOPHER4_states[k].ancestors[j] && PHILOSOPHER4_config[k] -> {
                    if
                    :: PHILOSOPHER4_states[k].type[USCXML_STATE_FINAL] -> {
                      PHILOSOPHER4_STATES_AND_NOT(PHILOSOPHER4_ctx.tmp_states, PHILOSOPHER4_states[k].ancestors)
                    }
                    :: else -> {
                      PHILOSOPHER4_ctx.tmp_states[k] = true;
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
                :: !PHILOSOPHER4_STATES_HAS_ANY(PHILOSOPHER4_ctx.tmp_states) -> {
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
PHILOSOPHER4_TERMINATE_MACHINE:
skip; d_step {

#if TRACE_EXECUTION
printf("%d: Machine finished\n", _pid);
#endif

/* exit all remaining states */
i = PHILOSOPHER4_USCXML_NUMBER_STATES;
do
:: i > 0 -> {
  i = i - 1;
  if
  :: PHILOSOPHER4_config[i] && PHILOSOPHER4_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
    /* call all on exit handlers */
   if
    :: i == 3 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for exiting state %d\n", _pid, i);
#endif

    if
    :: (PHILOSOPHER4__event.name == TAKE_LEFT_FORK || PHILOSOPHER4__event.name == TAKE_RIGHT_FORK) -> {
        cancelSendId(STARVATION_TIMER,PHILOSOPHER4);
    }
    :: else -> skip;
    fi;
    }
    :: i == 4 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for exiting state %d\n", _pid, i);
#endif

    if
    :: (PHILOSOPHER4__event.name == TAKE_RIGHT_FORK) -> {
        cancelSendId(STARVATION_TIMER,PHILOSOPHER4);
    }
    :: else -> skip;
    fi;
    }
    :: i == 5 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for exiting state %d\n", _pid, i);
#endif

    if
    :: (PHILOSOPHER4__event.name == TAKE_LEFT_FORK) -> {
        cancelSendId(STARVATION_TIMER,PHILOSOPHER4);
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
  :: PHILOSOPHER4_invocations[i] -> {
    /* cancel invocations */
    PHILOSOPHER4_invocations[i] = false;
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

removePendingEventsFromInvoker(PHILOSOPHER4)
/* send done event */
if
:: PHILOSOPHER4_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
    PHILOSOPHER4__tmpE.data.p_id = 0;
    PHILOSOPHER4__tmpE.delay = 0;
    PHILOSOPHER4__tmpE.invokeid = 0;
    PHILOSOPHER4__tmpE.name = 0;
    PHILOSOPHER4__tmpE.origin = 0;
    PHILOSOPHER4__tmpE.sendid = 0;
    PHILOSOPHER4__tmpE.seqNr = 0;

    PHILOSOPHER4__tmpE.name = DONE_INVOKE_PHILOSOPHER4
    PHILOSOPHER4__tmpE.invokeid = PHILOSOPHER4

#if TRACE_EXECUTION
printf("%d: Sending DONE.INVOKE\n", _pid);
#endif

    ROOT_eQ!PHILOSOPHER4__tmpE;
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
#define PHILOSOPHER5_USCXML_NUMBER_STATES 8
#define PHILOSOPHER5_USCXML_NUMBER_TRANS 11

proctype PHILOSOPHER5_step() { atomic {

PHILOSOPHER5_procid = _pid;
unsigned i : 4,  j : 4,  k : 4;


/* ---------------------------- */
PHILOSOPHER5_MICROSTEP:
do
:: !PHILOSOPHER5_flags[USCXML_CTX_FINISHED] -> {
  /* Run until machine is finished */


#if TRACE_EXECUTION
printf("%d: Taking a step\n", _pid);
#endif

  /* Dequeue an event */
  PHILOSOPHER5_flags[USCXML_CTX_DEQUEUE_EXTERNAL] = false;
  if
  ::PHILOSOPHER5_flags[USCXML_CTX_SPONTANEOUS] -> {
    PHILOSOPHER5__event.name = USCXML_EVENT_SPONTANEOUS;

#if TRACE_EXECUTION
printf("%d: Trying with a spontaneous event\n", _pid);
#endif

  }
  :: else -> {
    if
    :: len(PHILOSOPHER5_iQ) != 0 -> {
      PHILOSOPHER5_iQ ? PHILOSOPHER5__event;

#if TRACE_EXECUTION
printf("%d: Deqeued an internal event\n", _pid);
#endif

    }
    :: else -> {
      PHILOSOPHER5_flags[USCXML_CTX_DEQUEUE_EXTERNAL] = true;
    }
    fi;
  }
  fi;


  if
  :: PHILOSOPHER5_flags[USCXML_CTX_DEQUEUE_EXTERNAL] -> {
    /* manage invocations */
    i = 0;
    do
    :: i < PHILOSOPHER5_USCXML_NUMBER_STATES -> {
      d_step { 
      /* uninvoke */
      if
      :: !PHILOSOPHER5_config[i] && PHILOSOPHER5_invocations[i] -> {

#if TRACE_EXECUTION
printf("%d: Uninvoking in state %d\n", _pid, i);
#endif

        if
        :: else -> skip;
        fi
        PHILOSOPHER5_invocations[i] = false;
        skip;
      }
      :: else -> skip;
      fi;
      } /* d_step */

      /* invoke */
      if
      :: PHILOSOPHER5_config[i] && !PHILOSOPHER5_invocations[i] -> {
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
    :: PHILOSOPHER5_flags[USCXML_CTX_FINISHED] -> {
      goto PHILOSOPHER5_TERMINATE_MACHINE;
    }
    :: else -> skip;
    fi
    /* Not sure if this should be before the invocation due to auto-forwarding */
    if
    :: len(PHILOSOPHER5_eQ) != 0 -> {
      PHILOSOPHER5_eQ ? PHILOSOPHER5__event;

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
PHILOSOPHER5_SELECT_TRANSITIONS:
PHILOSOPHER5_STATES_CLEAR(PHILOSOPHER5_ctx.target_set)
PHILOSOPHER5_STATES_CLEAR(PHILOSOPHER5_ctx.exit_set)
PHILOSOPHER5_TRANS_CLEAR(PHILOSOPHER5_ctx.conflicts)
PHILOSOPHER5_TRANS_CLEAR(PHILOSOPHER5_ctx.trans_set)
#if TRACE_EXECUTION
printf("%d: Establishing optimal transition set for event %d\n", _pid, PHILOSOPHER5__event.name );
#endif

#if TRACE_EXECUTION
printf("Configuration: ");
printf("%d%d%d%d%d%d%d%d", 
    PHILOSOPHER5_config[0], 
    PHILOSOPHER5_config[1], 
    PHILOSOPHER5_config[2], 
    PHILOSOPHER5_config[3], 
    PHILOSOPHER5_config[4], 
    PHILOSOPHER5_config[5], 
    PHILOSOPHER5_config[6], 
    PHILOSOPHER5_config[7]);
printf("\n");
#endif

  PHILOSOPHER5_flags[USCXML_CTX_TRANSITION_FOUND] = false;
  i = 0;
  do
  :: i < PHILOSOPHER5_USCXML_NUMBER_TRANS -> {
    /* only select non-history, non-initial transitions */
    if
    :: !PHILOSOPHER5_transitions[i].type[USCXML_TRANS_HISTORY] &&
       !PHILOSOPHER5_transitions[i].type[USCXML_TRANS_INITIAL] -> {
      if
      :: /* is the transition active? */
         PHILOSOPHER5_config[PHILOSOPHER5_transitions[i].source] && 

         /* is it non-conflicting? */
         !PHILOSOPHER5_ctx.conflicts[i] && 

         /* is it spontaneous with an event or vice versa? */
         ((PHILOSOPHER5__event.name == USCXML_EVENT_SPONTANEOUS && 
           PHILOSOPHER5_transitions[i].type[USCXML_TRANS_SPONTANEOUS]) || 
          (PHILOSOPHER5__event.name != USCXML_EVENT_SPONTANEOUS && 
           !PHILOSOPHER5_transitions[i].type[USCXML_TRANS_SPONTANEOUS])) &&

         /* is it matching and enabled? */
         (false 
          || (i == 0 && (false || PHILOSOPHER5__event.name == THINKING_OVER))
          || (i == 1 && (false || PHILOSOPHER5__event.name == TAKE_LEFT_FORK))
          || (i == 2 && (false || PHILOSOPHER5__event.name == TAKE_RIGHT_FORK))
          || (i == 3 && (false || PHILOSOPHER5__event.name == TIMEOUT))
          || (i == 4 && (false || PHILOSOPHER5__event.name == TAKE_RIGHT_FORK))
          || (i == 5 && (false || PHILOSOPHER5__event.name == RESEND_NEED_RIGHT_FORK))
          || (i == 6 && (false || PHILOSOPHER5__event.name == TIMEOUT))
          || (i == 7 && (false || PHILOSOPHER5__event.name == TAKE_LEFT_FORK))
          || (i == 8 && (false || PHILOSOPHER5__event.name == RESEND_NEED_LEFT_FORK))
          || (i == 9 && (false || PHILOSOPHER5__event.name == TIMEOUT))
          || (i == 10 && (false || PHILOSOPHER5__event.name == EATING_OVER))
         ) -> {
        /* remember that we found a transition */
        PHILOSOPHER5_flags[USCXML_CTX_TRANSITION_FOUND] = true;

        /* transitions that are pre-empted */
        PHILOSOPHER5_TRANS_OR(PHILOSOPHER5_ctx.conflicts, PHILOSOPHER5_transitions[i].conflicts)

        /* states that are directly targeted (resolve as entry-set later) */
        PHILOSOPHER5_STATES_OR(PHILOSOPHER5_ctx.target_set, PHILOSOPHER5_transitions[i].target)

        /* states that will be left */
        PHILOSOPHER5_STATES_OR(PHILOSOPHER5_ctx.exit_set, PHILOSOPHER5_transitions[i].exit_set)

        PHILOSOPHER5_ctx.trans_set[i] = true;
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
  PHILOSOPHER5_STATES_AND(PHILOSOPHER5_ctx.exit_set, PHILOSOPHER5_config)

#if TRACE_EXECUTION
printf("Selected Transitions: ");
printf("%d%d%d%d%d%d%d%d%d%d%d", 
    PHILOSOPHER5_ctx.trans_set[0], 
    PHILOSOPHER5_ctx.trans_set[1], 
    PHILOSOPHER5_ctx.trans_set[2], 
    PHILOSOPHER5_ctx.trans_set[3], 
    PHILOSOPHER5_ctx.trans_set[4], 
    PHILOSOPHER5_ctx.trans_set[5], 
    PHILOSOPHER5_ctx.trans_set[6], 
    PHILOSOPHER5_ctx.trans_set[7], 
    PHILOSOPHER5_ctx.trans_set[8], 
    PHILOSOPHER5_ctx.trans_set[9], 
    PHILOSOPHER5_ctx.trans_set[10]);
printf("\n");
#endif


#if TRACE_EXECUTION
printf("Target Set: ");
printf("%d%d%d%d%d%d%d%d", 
    PHILOSOPHER5_ctx.target_set[0], 
    PHILOSOPHER5_ctx.target_set[1], 
    PHILOSOPHER5_ctx.target_set[2], 
    PHILOSOPHER5_ctx.target_set[3], 
    PHILOSOPHER5_ctx.target_set[4], 
    PHILOSOPHER5_ctx.target_set[5], 
    PHILOSOPHER5_ctx.target_set[6], 
    PHILOSOPHER5_ctx.target_set[7]);
printf("\n");
#endif


#if TRACE_EXECUTION
printf("Exit Set: ");
printf("%d%d%d%d%d%d%d%d", 
    PHILOSOPHER5_ctx.exit_set[0], 
    PHILOSOPHER5_ctx.exit_set[1], 
    PHILOSOPHER5_ctx.exit_set[2], 
    PHILOSOPHER5_ctx.exit_set[3], 
    PHILOSOPHER5_ctx.exit_set[4], 
    PHILOSOPHER5_ctx.exit_set[5], 
    PHILOSOPHER5_ctx.exit_set[6], 
    PHILOSOPHER5_ctx.exit_set[7]);
printf("\n");
#endif

  if
  :: !PHILOSOPHER5_STATES_HAS_ANY(PHILOSOPHER5_config) -> {
    /* Enter initial configuration */
    PHILOSOPHER5_STATES_COPY(PHILOSOPHER5_ctx.target_set, PHILOSOPHER5_states[0].completion)
    PHILOSOPHER5_flags[USCXML_CTX_SPONTANEOUS] = true;
    PHILOSOPHER5_flags[USCXML_CTX_TRANSITION_FOUND] = true;

#if TRACE_EXECUTION
printf("%d: Entering initial default completion\n", _pid);
#endif


  }
  :: PHILOSOPHER5_flags[USCXML_CTX_TRANSITION_FOUND] -> {

#if TRACE_EXECUTION
printf("%d: Found transitions\n", _pid);
#endif

    PHILOSOPHER5_flags[USCXML_CTX_SPONTANEOUS] = true;
  }
  :: else {
    PHILOSOPHER5_flags[USCXML_CTX_SPONTANEOUS] = false;

#if TRACE_EXECUTION
printf("%d: Found NO transitions\n", _pid);
#endif

  }
  fi


  if
  :: PHILOSOPHER5_flags[USCXML_CTX_TRANSITION_FOUND] -> {
    /* only process anything if we found transitions or are on initial entry */
/* ---------------------------- */
/* REMEMBER_HISTORY: */

#if TRACE_EXECUTION
printf("%d: Save history configurations\n", _pid);
#endif

  if
  :: PHILOSOPHER5_STATES_HAS_ANY(PHILOSOPHER5_config) -> {
    /* only remember history on non-initial entry */
    i = 0;
    do
    :: i < PHILOSOPHER5_USCXML_NUMBER_STATES -> {
      if
      :: PHILOSOPHER5_states[i].type[USCXML_STATE_HISTORY_SHALLOW] ||
         PHILOSOPHER5_states[i].type[USCXML_STATE_HISTORY_DEEP] -> {
        if
        :: PHILOSOPHER5_ctx.exit_set[PHILOSOPHER5_states[i].parent] -> {
          /* a history state whose parent is about to be exited */

#if TRACE_EXECUTION
printf("%d: history state %d is about to be exited\n", _pid, i);
#endif


#if TRACE_EXECUTION
printf("COMPLET: ");
printf("%d%d%d%d%d%d%d%d", 
    PHILOSOPHER5_states[i].completion[0], 
    PHILOSOPHER5_states[i].completion[1], 
    PHILOSOPHER5_states[i].completion[2], 
    PHILOSOPHER5_states[i].completion[3], 
    PHILOSOPHER5_states[i].completion[4], 
    PHILOSOPHER5_states[i].completion[5], 
    PHILOSOPHER5_states[i].completion[6], 
    PHILOSOPHER5_states[i].completion[7]);
printf("\n");
#endif

          PHILOSOPHER5_STATES_COPY(PHILOSOPHER5_ctx.tmp_states, PHILOSOPHER5_states[i].completion)

          /* set those states who were enabled */
          PHILOSOPHER5_STATES_AND(PHILOSOPHER5_ctx.tmp_states, PHILOSOPHER5_config)

#if TRACE_EXECUTION
printf("CONFIG : ");
printf("%d%d%d%d%d%d%d%d", 
    PHILOSOPHER5_config[0], 
    PHILOSOPHER5_config[1], 
    PHILOSOPHER5_config[2], 
    PHILOSOPHER5_config[3], 
    PHILOSOPHER5_config[4], 
    PHILOSOPHER5_config[5], 
    PHILOSOPHER5_config[6], 
    PHILOSOPHER5_config[7]);
printf("\n");
#endif


#if TRACE_EXECUTION
printf("TMP_STS: ");
printf("%d%d%d%d%d%d%d%d", 
    PHILOSOPHER5_ctx.tmp_states[0], 
    PHILOSOPHER5_ctx.tmp_states[1], 
    PHILOSOPHER5_ctx.tmp_states[2], 
    PHILOSOPHER5_ctx.tmp_states[3], 
    PHILOSOPHER5_ctx.tmp_states[4], 
    PHILOSOPHER5_ctx.tmp_states[5], 
    PHILOSOPHER5_ctx.tmp_states[6], 
    PHILOSOPHER5_ctx.tmp_states[7]);
printf("\n");
#endif


          /* clear current history with completion mask */
          PHILOSOPHER5_STATES_AND_NOT(PHILOSOPHER5_history, PHILOSOPHER5_states[i].completion)

          /* set history */
          PHILOSOPHER5_STATES_OR(PHILOSOPHER5_history, PHILOSOPHER5_ctx.tmp_states)

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
printf("%d%d%d%d%d%d%d%d", 
    PHILOSOPHER5_history[0], 
    PHILOSOPHER5_history[1], 
    PHILOSOPHER5_history[2], 
    PHILOSOPHER5_history[3], 
    PHILOSOPHER5_history[4], 
    PHILOSOPHER5_history[5], 
    PHILOSOPHER5_history[6], 
    PHILOSOPHER5_history[7]);
printf("\n");
#endif
  }
  :: else -> skip;
  fi;

/* ---------------------------- */
PHILOSOPHER5_ESTABLISH_ENTRY_SET:
  /* calculate new entry set */
  PHILOSOPHER5_STATES_COPY(PHILOSOPHER5_ctx.entry_set, PHILOSOPHER5_ctx.target_set)

  i = 0;
  do
  :: i < PHILOSOPHER5_USCXML_NUMBER_STATES -> {
    if
    :: PHILOSOPHER5_ctx.entry_set[i] -> {
      /* ancestor completion */
      PHILOSOPHER5_STATES_OR(PHILOSOPHER5_ctx.entry_set, PHILOSOPHER5_states[i].ancestors)
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
  :: i < PHILOSOPHER5_USCXML_NUMBER_STATES -> {
    if
    :: PHILOSOPHER5_ctx.entry_set[i] -> {
      if
      :: PHILOSOPHER5_states[i].type[USCXML_STATE_PARALLEL] -> {
        PHILOSOPHER5_STATES_OR(PHILOSOPHER5_ctx.entry_set, PHILOSOPHER5_states[i].completion)
      }
      :: PHILOSOPHER5_states[i].type[USCXML_STATE_HISTORY_SHALLOW] ||
         PHILOSOPHER5_states[i].type[USCXML_STATE_HISTORY_DEEP] -> {

#if TRACE_EXECUTION
printf("%d: Descendant completion for history state %d\n", _pid, i);
#endif

        if
        :: !PHILOSOPHER5_STATES_HAS_AND(PHILOSOPHER5_states[i].completion, PHILOSOPHER5_history) && !PHILOSOPHER5_config[PHILOSOPHER5_states[i].parent] -> {
          /* nothing set for history, look for a default transition */

#if TRACE_EXECUTION
printf("%d: Fresh history in target set\n", _pid);
#endif

          j = 0;
          do
          :: j < PHILOSOPHER5_USCXML_NUMBER_TRANS -> {
             if
             :: PHILOSOPHER5_transitions[j].source == i -> {
               PHILOSOPHER5_ctx.trans_set[j] = true;
               PHILOSOPHER5_STATES_OR(PHILOSOPHER5_ctx.entry_set, PHILOSOPHER5_transitions[j].target)

               if
               :: (PHILOSOPHER5_states[i].type[USCXML_STATE_HISTORY_DEEP] &&
                   !PHILOSOPHER5_STATES_HAS_AND(PHILOSOPHER5_transitions[j].target, PHILOSOPHER5_states[i].children)                  ) -> {
                 k = i + 1
                 do
                 :: k < PHILOSOPHER5_USCXML_NUMBER_STATES -> {
                   if
                   :: PHILOSOPHER5_transitions[j].target[k] -> {
                     PHILOSOPHER5_STATES_OR(PHILOSOPHER5_ctx.entry_set, PHILOSOPHER5_states[k].ancestors)
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

          PHILOSOPHER5_STATES_COPY(PHILOSOPHER5_ctx.tmp_states, PHILOSOPHER5_states[i].completion)
          PHILOSOPHER5_STATES_AND(PHILOSOPHER5_ctx.tmp_states, PHILOSOPHER5_history)
          PHILOSOPHER5_STATES_OR(PHILOSOPHER5_ctx.entry_set, PHILOSOPHER5_ctx.tmp_states)
          if
          :: PHILOSOPHER5_states[i].type[USCXML_STATE_HAS_HISTORY] ||
             PHILOSOPHER5_states[i].type[USCXML_STATE_HISTORY_DEEP] -> { 
            /* a deep history state with nested histories -> more completion */

#if TRACE_EXECUTION
printf("%d: DEEP HISTORY\n", _pid);
#endif

            j = i + 1;
            do
            :: j < PHILOSOPHER5_USCXML_NUMBER_STATES -> {
              if
              :: (PHILOSOPHER5_states[i].completion[j] &&
                  PHILOSOPHER5_ctx.entry_set[j] && 
                  PHILOSOPHER5_states[j].type[USCXML_STATE_HAS_HISTORY]) -> {
                k = j + 1;
                do
                :: k < PHILOSOPHER5_USCXML_NUMBER_STATES -> {
                  /* add nested history to entry_set */
                  if
                  :: (PHILOSOPHER5_states[k].type[USCXML_STATE_HISTORY_DEEP] ||
                      PHILOSOPHER5_states[k].type[USCXML_STATE_HISTORY_SHALLOW]) &&
                     PHILOSOPHER5_states[j].children[k] -> {
                    /* a nested history state */
                    PHILOSOPHER5_ctx.entry_set[k] = true;
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
      :: PHILOSOPHER5_states[i].type[USCXML_STATE_INITIAL] -> {

#if TRACE_EXECUTION
printf("%d: Descendant completion for initial state %d\n", _pid, i);
#endif

        j = 0
        do
        :: j < PHILOSOPHER5_USCXML_NUMBER_TRANS -> {
          if
          :: PHILOSOPHER5_transitions[j].source == i -> {
            PHILOSOPHER5_ctx.trans_set[j] = true;
            PHILOSOPHER5_ctx.entry_set[i] = false;

#if TRACE_EXECUTION
printf("%d: Adding transition %d!\n", _pid, j);
#endif

            PHILOSOPHER5_STATES_OR(PHILOSOPHER5_ctx.entry_set, PHILOSOPHER5_transitions[j].target)

            k = i + 1;
            do
            :: k < PHILOSOPHER5_USCXML_NUMBER_STATES -> {
              if
              :: PHILOSOPHER5_transitions[j].target[k] -> {
                PHILOSOPHER5_STATES_OR(PHILOSOPHER5_ctx.entry_set, PHILOSOPHER5_states[k].ancestors)

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
      :: PHILOSOPHER5_states[i].type[USCXML_STATE_COMPOUND] -> {
        /* we need to check whether one child is already in entry_set */
        if
        :: (
          !PHILOSOPHER5_STATES_HAS_AND(PHILOSOPHER5_ctx.entry_set, PHILOSOPHER5_states[i].children) && 
           (!PHILOSOPHER5_STATES_HAS_AND(PHILOSOPHER5_config, PHILOSOPHER5_states[i].children) || PHILOSOPHER5_STATES_HAS_AND(PHILOSOPHER5_ctx.exit_set, PHILOSOPHER5_states[i].children)
)) 
        -> {
          PHILOSOPHER5_STATES_OR(PHILOSOPHER5_ctx.entry_set, PHILOSOPHER5_states[i].completion)
          if
          :: (PHILOSOPHER5_STATES_HAS_AND(PHILOSOPHER5_states[i].completion, PHILOSOPHER5_states[i].children)
          ) -> {
            /* deep completion */
            j = i + 1;
            do
            :: j < PHILOSOPHER5_USCXML_NUMBER_STATES - 1 -> {
              j = j + 1;
              if
              :: PHILOSOPHER5_states[i].completion[j] -> {
                PHILOSOPHER5_STATES_OR(PHILOSOPHER5_ctx.entry_set, PHILOSOPHER5_states[j].ancestors)

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
printf("%d%d%d%d%d%d%d%d", 
    PHILOSOPHER5_ctx.entry_set[0], 
    PHILOSOPHER5_ctx.entry_set[1], 
    PHILOSOPHER5_ctx.entry_set[2], 
    PHILOSOPHER5_ctx.entry_set[3], 
    PHILOSOPHER5_ctx.entry_set[4], 
    PHILOSOPHER5_ctx.entry_set[5], 
    PHILOSOPHER5_ctx.entry_set[6], 
    PHILOSOPHER5_ctx.entry_set[7]);
printf("\n");
#endif


/* ---------------------------- */
/* EXIT_STATES: */
  i = PHILOSOPHER5_USCXML_NUMBER_STATES;
  do
  :: i > 0 -> {
    i = i - 1;
    if
    :: PHILOSOPHER5_ctx.exit_set[i] && PHILOSOPHER5_config[i] -> {
      /* call all on-exit handlers */

#if TRACE_EXECUTION
printf("%d: Exiting state %d\n", _pid, i);
#endif

      if
      :: i == 3 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for exiting state %d\n", _pid, i);
#endif

      if
      :: (PHILOSOPHER5__event.name == TAKE_LEFT_FORK || PHILOSOPHER5__event.name == TAKE_RIGHT_FORK) -> {
          cancelSendId(STARVATION_TIMER,PHILOSOPHER5);
      }
      :: else -> skip;
      fi;
      }
      :: i == 4 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for exiting state %d\n", _pid, i);
#endif

      if
      :: (PHILOSOPHER5__event.name == TAKE_RIGHT_FORK) -> {
          cancelSendId(STARVATION_TIMER,PHILOSOPHER5);
      }
      :: else -> skip;
      fi;
      }
      :: i == 5 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for exiting state %d\n", _pid, i);
#endif

      if
      :: (PHILOSOPHER5__event.name == TAKE_LEFT_FORK) -> {
          cancelSendId(STARVATION_TIMER,PHILOSOPHER5);
      }
      :: else -> skip;
      fi;
      }
      :: else -> skip;
      fi

      PHILOSOPHER5_config[i] = false;
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
  :: i < PHILOSOPHER5_USCXML_NUMBER_TRANS -> {
    if
    :: PHILOSOPHER5_ctx.trans_set[i] && 
       !PHILOSOPHER5_transitions[i].type[USCXML_TRANS_HISTORY] && 
       !PHILOSOPHER5_transitions[i].type[USCXML_TRANS_INITIAL] -> {
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

        printf("philospher: : %d", PHILOSOPHER5_p_id);
        printf("starved in state hungry for Time(in ms) : : %d", PHILOSOPHER5_delay);
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
        :: !PHILOSOPHER5_flags[USCXML_CTX_FINISHED] || PHILOSOPHER5_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
          {
            PHILOSOPHER5__tmpE.data.p_id = 0;
            PHILOSOPHER5__tmpE.delay = 0;
            PHILOSOPHER5__tmpE.invokeid = 0;
            PHILOSOPHER5__tmpE.name = 0;
            PHILOSOPHER5__tmpE.origin = 0;
            PHILOSOPHER5__tmpE.sendid = 0;
            PHILOSOPHER5__tmpE.seqNr = 0;
            PHILOSOPHER5__tmpE.name = NEED_RIGHT_FORK;
            PHILOSOPHER5__tmpE.invokeid = PHILOSOPHER5;
            PHILOSOPHER5__tmpE.origin = PHILOSOPHER5;
            _lastSeqId = _lastSeqId + 1;
            PHILOSOPHER5__tmpE.delay = 0;
            PHILOSOPHER5__tmpE.seqNr = _lastSeqId;
            PHILOSOPHER5__tmpE.data.p_id = PHILOSOPHER5_p_id;
#if TRACE_EXECUTION
printf("%d: Sending NEED_RIGHT_FORK (%d) to ROOT_eQ\n", _pid, PHILOSOPHER5__tmpE.name );
#endif

            ROOT_eQ!PHILOSOPHER5__tmpE;
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

        printf("philospher: : %d", PHILOSOPHER5_p_id);
        printf("starved in state has_right_fork for Time(in ms) :: %d", PHILOSOPHER5_delay);
        skip;
      }
      :: i == 7 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, i);
#endif

        skip;
      }
      :: i == 8 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, i);
#endif

        if
        :: !PHILOSOPHER5_flags[USCXML_CTX_FINISHED] || PHILOSOPHER5_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
          {
            PHILOSOPHER5__tmpE.data.p_id = 0;
            PHILOSOPHER5__tmpE.delay = 0;
            PHILOSOPHER5__tmpE.invokeid = 0;
            PHILOSOPHER5__tmpE.name = 0;
            PHILOSOPHER5__tmpE.origin = 0;
            PHILOSOPHER5__tmpE.sendid = 0;
            PHILOSOPHER5__tmpE.seqNr = 0;
            PHILOSOPHER5__tmpE.name = NEED_LEFT_FORK;
            PHILOSOPHER5__tmpE.invokeid = PHILOSOPHER5;
            PHILOSOPHER5__tmpE.origin = PHILOSOPHER5;
            _lastSeqId = _lastSeqId + 1;
            PHILOSOPHER5__tmpE.delay = 0;
            PHILOSOPHER5__tmpE.seqNr = _lastSeqId;
            PHILOSOPHER5__tmpE.data.p_id = PHILOSOPHER5_p_id;
#if TRACE_EXECUTION
printf("%d: Sending NEED_LEFT_FORK (%d) to ROOT_eQ\n", _pid, PHILOSOPHER5__tmpE.name );
#endif

            ROOT_eQ!PHILOSOPHER5__tmpE;
            insertWithDelay(ROOT_eQ);
          }
          skip;
        }
        :: else -> skip;
        fi
        skip;
      }
      :: i == 9 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, i);
#endif

        printf("philospher: : %d", PHILOSOPHER5_p_id);
        printf("starved in state has_right_fork for Time(in ms) : : %d", PHILOSOPHER5_delay);
        skip;
      }
      :: i == 10 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, i);
#endif

        if
        :: !PHILOSOPHER5_flags[USCXML_CTX_FINISHED] || PHILOSOPHER5_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
          {
            PHILOSOPHER5__tmpE.data.p_id = 0;
            PHILOSOPHER5__tmpE.delay = 0;
            PHILOSOPHER5__tmpE.invokeid = 0;
            PHILOSOPHER5__tmpE.name = 0;
            PHILOSOPHER5__tmpE.origin = 0;
            PHILOSOPHER5__tmpE.sendid = 0;
            PHILOSOPHER5__tmpE.seqNr = 0;
            PHILOSOPHER5__tmpE.name = RETURN_FORKS;
            PHILOSOPHER5__tmpE.invokeid = PHILOSOPHER5;
            PHILOSOPHER5__tmpE.origin = PHILOSOPHER5;
            _lastSeqId = _lastSeqId + 1;
            PHILOSOPHER5__tmpE.delay = 0;
            PHILOSOPHER5__tmpE.seqNr = _lastSeqId;
            PHILOSOPHER5__tmpE.data.p_id = PHILOSOPHER5_p_id;
#if TRACE_EXECUTION
printf("%d: Sending RETURN_FORKS (%d) to ROOT_eQ\n", _pid, PHILOSOPHER5__tmpE.name );
#endif

            ROOT_eQ!PHILOSOPHER5__tmpE;
            insertWithDelay(ROOT_eQ);
          }
          skip;
        }
        :: else -> skip;
        fi
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
  :: i < PHILOSOPHER5_USCXML_NUMBER_STATES -> {
    if
    :: (PHILOSOPHER5_ctx.entry_set[i] &&
        !PHILOSOPHER5_config[i] && 
        /* these are no proper states */
        !PHILOSOPHER5_states[i].type[USCXML_STATE_HISTORY_DEEP] && 
        !PHILOSOPHER5_states[i].type[USCXML_STATE_HISTORY_SHALLOW] && 
        !PHILOSOPHER5_states[i].type[USCXML_STATE_INITIAL]
       ) -> {

#if TRACE_EXECUTION
printf("%d: Entering state %d\n", _pid, i);
#endif

         PHILOSOPHER5_config[i] = true;

         /* Process executable content for entering a state */
         if
         :: i == 1 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for entering state %d\n", _pid, i);
#endif

          printf("Hello, I am philospher number: : %d", PHILOSOPHER5_p_id);
         }
         :: i == 2 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for entering state %d\n", _pid, i);
#endif

          printf("Thinking philosopher: : %d", PHILOSOPHER5_p_id);
            PHILOSOPHER5_random_delay = ((1103515245*PHILOSOPHER5_random_delay+12345)%2147483647)%2000;
          if
          :: !PHILOSOPHER5_flags[USCXML_CTX_FINISHED] || PHILOSOPHER5_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
            {
              PHILOSOPHER5__tmpE.data.p_id = 0;
              PHILOSOPHER5__tmpE.delay = 0;
              PHILOSOPHER5__tmpE.invokeid = 0;
              PHILOSOPHER5__tmpE.name = 0;
              PHILOSOPHER5__tmpE.origin = 0;
              PHILOSOPHER5__tmpE.sendid = 0;
              PHILOSOPHER5__tmpE.seqNr = 0;
              PHILOSOPHER5__tmpE.name = THINKING_OVER;
              PHILOSOPHER5__tmpE.invokeid = PHILOSOPHER5;
              PHILOSOPHER5__tmpE.origin = PHILOSOPHER5;
              _lastSeqId = _lastSeqId + 1;
              PHILOSOPHER5__tmpE.delay = PHILOSOPHER5_random_delay*(PHILOSOPHER5_p_id+1);
              PHILOSOPHER5__tmpE.seqNr = _lastSeqId;
#if TRACE_EXECUTION
printf("%d: Sending THINKING_OVER (%d) to PHILOSOPHER5_eQ\n", _pid, PHILOSOPHER5__tmpE.name );
#endif

              PHILOSOPHER5_eQ!PHILOSOPHER5__tmpE;
              insertWithDelay(PHILOSOPHER5_eQ);
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

          printf("Hungry philosopher: : %d", PHILOSOPHER5_p_id);
          if
          :: !PHILOSOPHER5_flags[USCXML_CTX_FINISHED] || PHILOSOPHER5_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
            {
              PHILOSOPHER5__tmpE.data.p_id = 0;
              PHILOSOPHER5__tmpE.delay = 0;
              PHILOSOPHER5__tmpE.invokeid = 0;
              PHILOSOPHER5__tmpE.name = 0;
              PHILOSOPHER5__tmpE.origin = 0;
              PHILOSOPHER5__tmpE.sendid = 0;
              PHILOSOPHER5__tmpE.seqNr = 0;
              PHILOSOPHER5__tmpE.name = TIMEOUT;
              PHILOSOPHER5__tmpE.sendid = STARVATION_TIMER;
              PHILOSOPHER5__tmpE.invokeid = PHILOSOPHER5;
              PHILOSOPHER5__tmpE.origin = PHILOSOPHER5;
              _lastSeqId = _lastSeqId + 1;
              PHILOSOPHER5__tmpE.delay = PHILOSOPHER5_delay;
              PHILOSOPHER5__tmpE.seqNr = _lastSeqId;
#if TRACE_EXECUTION
printf("%d: Sending TIMEOUT (%d) to PHILOSOPHER5_eQ\n", _pid, PHILOSOPHER5__tmpE.name );
#endif

              PHILOSOPHER5_eQ!PHILOSOPHER5__tmpE;
              insertWithDelay(PHILOSOPHER5_eQ);
            }
            skip;
          }
          :: else -> skip;
          fi
          if
          :: !PHILOSOPHER5_flags[USCXML_CTX_FINISHED] || PHILOSOPHER5_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
            {
              PHILOSOPHER5__tmpE.data.p_id = 0;
              PHILOSOPHER5__tmpE.delay = 0;
              PHILOSOPHER5__tmpE.invokeid = 0;
              PHILOSOPHER5__tmpE.name = 0;
              PHILOSOPHER5__tmpE.origin = 0;
              PHILOSOPHER5__tmpE.sendid = 0;
              PHILOSOPHER5__tmpE.seqNr = 0;
              PHILOSOPHER5__tmpE.name = NEED_LEFT_FORK;
              PHILOSOPHER5__tmpE.invokeid = PHILOSOPHER5;
              PHILOSOPHER5__tmpE.origin = PHILOSOPHER5;
              _lastSeqId = _lastSeqId + 1;
              PHILOSOPHER5__tmpE.delay = 0;
              PHILOSOPHER5__tmpE.seqNr = _lastSeqId;
              PHILOSOPHER5__tmpE.data.p_id = PHILOSOPHER5_p_id;
#if TRACE_EXECUTION
printf("%d: Sending NEED_LEFT_FORK (%d) to ROOT_eQ\n", _pid, PHILOSOPHER5__tmpE.name );
#endif

              ROOT_eQ!PHILOSOPHER5__tmpE;
              insertWithDelay(ROOT_eQ);
            }
            skip;
          }
          :: else -> skip;
          fi
          if
          :: !PHILOSOPHER5_flags[USCXML_CTX_FINISHED] || PHILOSOPHER5_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
            {
              PHILOSOPHER5__tmpE.data.p_id = 0;
              PHILOSOPHER5__tmpE.delay = 0;
              PHILOSOPHER5__tmpE.invokeid = 0;
              PHILOSOPHER5__tmpE.name = 0;
              PHILOSOPHER5__tmpE.origin = 0;
              PHILOSOPHER5__tmpE.sendid = 0;
              PHILOSOPHER5__tmpE.seqNr = 0;
              PHILOSOPHER5__tmpE.name = NEED_RIGHT_FORK;
              PHILOSOPHER5__tmpE.invokeid = PHILOSOPHER5;
              PHILOSOPHER5__tmpE.origin = PHILOSOPHER5;
              _lastSeqId = _lastSeqId + 1;
              PHILOSOPHER5__tmpE.delay = 0;
              PHILOSOPHER5__tmpE.seqNr = _lastSeqId;
              PHILOSOPHER5__tmpE.data.p_id = PHILOSOPHER5_p_id;
#if TRACE_EXECUTION
printf("%d: Sending NEED_RIGHT_FORK (%d) to ROOT_eQ\n", _pid, PHILOSOPHER5__tmpE.name );
#endif

              ROOT_eQ!PHILOSOPHER5__tmpE;
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

          printf("in state has_left_fork for philosopher: : %d", PHILOSOPHER5_p_id);
          if
          :: !PHILOSOPHER5_flags[USCXML_CTX_FINISHED] || PHILOSOPHER5_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
            {
              PHILOSOPHER5__tmpE.data.p_id = 0;
              PHILOSOPHER5__tmpE.delay = 0;
              PHILOSOPHER5__tmpE.invokeid = 0;
              PHILOSOPHER5__tmpE.name = 0;
              PHILOSOPHER5__tmpE.origin = 0;
              PHILOSOPHER5__tmpE.sendid = 0;
              PHILOSOPHER5__tmpE.seqNr = 0;
              PHILOSOPHER5__tmpE.name = TIMEOUT;
              PHILOSOPHER5__tmpE.sendid = STARVATION_TIMER;
              PHILOSOPHER5__tmpE.invokeid = PHILOSOPHER5;
              PHILOSOPHER5__tmpE.origin = PHILOSOPHER5;
              _lastSeqId = _lastSeqId + 1;
              PHILOSOPHER5__tmpE.delay = PHILOSOPHER5_delay;
              PHILOSOPHER5__tmpE.seqNr = _lastSeqId;
#if TRACE_EXECUTION
printf("%d: Sending TIMEOUT (%d) to PHILOSOPHER5_eQ\n", _pid, PHILOSOPHER5__tmpE.name );
#endif

              PHILOSOPHER5_eQ!PHILOSOPHER5__tmpE;
              insertWithDelay(PHILOSOPHER5_eQ);
            }
            skip;
          }
          :: else -> skip;
          fi
          if
          :: !PHILOSOPHER5_flags[USCXML_CTX_FINISHED] || PHILOSOPHER5_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
            {
              PHILOSOPHER5__tmpE.data.p_id = 0;
              PHILOSOPHER5__tmpE.delay = 0;
              PHILOSOPHER5__tmpE.invokeid = 0;
              PHILOSOPHER5__tmpE.name = 0;
              PHILOSOPHER5__tmpE.origin = 0;
              PHILOSOPHER5__tmpE.sendid = 0;
              PHILOSOPHER5__tmpE.seqNr = 0;
              PHILOSOPHER5__tmpE.name = RESEND_NEED_RIGHT_FORK;
              PHILOSOPHER5__tmpE.invokeid = PHILOSOPHER5;
              PHILOSOPHER5__tmpE.origin = PHILOSOPHER5;
              _lastSeqId = _lastSeqId + 1;
              PHILOSOPHER5__tmpE.delay = 500;
              PHILOSOPHER5__tmpE.seqNr = _lastSeqId;
#if TRACE_EXECUTION
printf("%d: Sending RESEND_NEED_RIGHT_FORK (%d) to PHILOSOPHER5_eQ\n", _pid, PHILOSOPHER5__tmpE.name );
#endif

              PHILOSOPHER5_eQ!PHILOSOPHER5__tmpE;
              insertWithDelay(PHILOSOPHER5_eQ);
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

          printf("in state has_right_fork for philosopher: : %d", PHILOSOPHER5_p_id);
          if
          :: !PHILOSOPHER5_flags[USCXML_CTX_FINISHED] || PHILOSOPHER5_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
            {
              PHILOSOPHER5__tmpE.data.p_id = 0;
              PHILOSOPHER5__tmpE.delay = 0;
              PHILOSOPHER5__tmpE.invokeid = 0;
              PHILOSOPHER5__tmpE.name = 0;
              PHILOSOPHER5__tmpE.origin = 0;
              PHILOSOPHER5__tmpE.sendid = 0;
              PHILOSOPHER5__tmpE.seqNr = 0;
              PHILOSOPHER5__tmpE.name = TIMEOUT;
              PHILOSOPHER5__tmpE.sendid = STARVATION_TIMER;
              PHILOSOPHER5__tmpE.invokeid = PHILOSOPHER5;
              PHILOSOPHER5__tmpE.origin = PHILOSOPHER5;
              _lastSeqId = _lastSeqId + 1;
              PHILOSOPHER5__tmpE.delay = PHILOSOPHER5_delay;
              PHILOSOPHER5__tmpE.seqNr = _lastSeqId;
#if TRACE_EXECUTION
printf("%d: Sending TIMEOUT (%d) to PHILOSOPHER5_eQ\n", _pid, PHILOSOPHER5__tmpE.name );
#endif

              PHILOSOPHER5_eQ!PHILOSOPHER5__tmpE;
              insertWithDelay(PHILOSOPHER5_eQ);
            }
            skip;
          }
          :: else -> skip;
          fi
          if
          :: !PHILOSOPHER5_flags[USCXML_CTX_FINISHED] || PHILOSOPHER5_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
            {
              PHILOSOPHER5__tmpE.data.p_id = 0;
              PHILOSOPHER5__tmpE.delay = 0;
              PHILOSOPHER5__tmpE.invokeid = 0;
              PHILOSOPHER5__tmpE.name = 0;
              PHILOSOPHER5__tmpE.origin = 0;
              PHILOSOPHER5__tmpE.sendid = 0;
              PHILOSOPHER5__tmpE.seqNr = 0;
              PHILOSOPHER5__tmpE.name = RESEND_NEED_LEFT_FORK;
              PHILOSOPHER5__tmpE.invokeid = PHILOSOPHER5;
              PHILOSOPHER5__tmpE.origin = PHILOSOPHER5;
              _lastSeqId = _lastSeqId + 1;
              PHILOSOPHER5__tmpE.delay = 500;
              PHILOSOPHER5__tmpE.seqNr = _lastSeqId;
#if TRACE_EXECUTION
printf("%d: Sending RESEND_NEED_LEFT_FORK (%d) to PHILOSOPHER5_eQ\n", _pid, PHILOSOPHER5__tmpE.name );
#endif

              PHILOSOPHER5_eQ!PHILOSOPHER5__tmpE;
              insertWithDelay(PHILOSOPHER5_eQ);
            }
            skip;
          }
          :: else -> skip;
          fi
         }
         :: i == 6 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for entering state %d\n", _pid, i);
#endif

          printf("Eating philosopher: : %d", PHILOSOPHER5_p_id);
          if
          :: !PHILOSOPHER5_flags[USCXML_CTX_FINISHED] || PHILOSOPHER5_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
            {
              PHILOSOPHER5__tmpE.data.p_id = 0;
              PHILOSOPHER5__tmpE.delay = 0;
              PHILOSOPHER5__tmpE.invokeid = 0;
              PHILOSOPHER5__tmpE.name = 0;
              PHILOSOPHER5__tmpE.origin = 0;
              PHILOSOPHER5__tmpE.sendid = 0;
              PHILOSOPHER5__tmpE.seqNr = 0;
              PHILOSOPHER5__tmpE.name = EATING_OVER;
              PHILOSOPHER5__tmpE.invokeid = PHILOSOPHER5;
              PHILOSOPHER5__tmpE.origin = PHILOSOPHER5;
              _lastSeqId = _lastSeqId + 1;
              PHILOSOPHER5__tmpE.delay = PHILOSOPHER5_random_delay;
              PHILOSOPHER5__tmpE.seqNr = _lastSeqId;
#if TRACE_EXECUTION
printf("%d: Sending EATING_OVER (%d) to PHILOSOPHER5_eQ\n", _pid, PHILOSOPHER5__tmpE.name );
#endif

              PHILOSOPHER5_eQ!PHILOSOPHER5__tmpE;
              insertWithDelay(PHILOSOPHER5_eQ);
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
         :: j < PHILOSOPHER5_USCXML_NUMBER_TRANS -> {
           if
           :: (PHILOSOPHER5_ctx.trans_set[j] &&
              (PHILOSOPHER5_transitions[j].type[USCXML_TRANS_HISTORY] ||
               PHILOSOPHER5_transitions[j].type[USCXML_TRANS_INITIAL]) && 
               PHILOSOPHER5_states[PHILOSOPHER5_transitions[j].source].parent == i) -> {
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

                printf("philospher: : %d", PHILOSOPHER5_p_id);
                printf("starved in state hungry for Time(in ms) : : %d", PHILOSOPHER5_delay);
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
                :: !PHILOSOPHER5_flags[USCXML_CTX_FINISHED] || PHILOSOPHER5_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
                  {
                    PHILOSOPHER5__tmpE.data.p_id = 0;
                    PHILOSOPHER5__tmpE.delay = 0;
                    PHILOSOPHER5__tmpE.invokeid = 0;
                    PHILOSOPHER5__tmpE.name = 0;
                    PHILOSOPHER5__tmpE.origin = 0;
                    PHILOSOPHER5__tmpE.sendid = 0;
                    PHILOSOPHER5__tmpE.seqNr = 0;
                    PHILOSOPHER5__tmpE.name = NEED_RIGHT_FORK;
                    PHILOSOPHER5__tmpE.invokeid = PHILOSOPHER5;
                    PHILOSOPHER5__tmpE.origin = PHILOSOPHER5;
                    _lastSeqId = _lastSeqId + 1;
                    PHILOSOPHER5__tmpE.delay = 0;
                    PHILOSOPHER5__tmpE.seqNr = _lastSeqId;
                    PHILOSOPHER5__tmpE.data.p_id = PHILOSOPHER5_p_id;
#if TRACE_EXECUTION
printf("%d: Sending NEED_RIGHT_FORK (%d) to ROOT_eQ\n", _pid, PHILOSOPHER5__tmpE.name );
#endif

                    ROOT_eQ!PHILOSOPHER5__tmpE;
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

                printf("philospher: : %d", PHILOSOPHER5_p_id);
                printf("starved in state has_right_fork for Time(in ms) :: %d", PHILOSOPHER5_delay);
                skip;
              }
              :: j == 7 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, j);
#endif

                skip;
              }
              :: j == 8 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, j);
#endif

                if
                :: !PHILOSOPHER5_flags[USCXML_CTX_FINISHED] || PHILOSOPHER5_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
                  {
                    PHILOSOPHER5__tmpE.data.p_id = 0;
                    PHILOSOPHER5__tmpE.delay = 0;
                    PHILOSOPHER5__tmpE.invokeid = 0;
                    PHILOSOPHER5__tmpE.name = 0;
                    PHILOSOPHER5__tmpE.origin = 0;
                    PHILOSOPHER5__tmpE.sendid = 0;
                    PHILOSOPHER5__tmpE.seqNr = 0;
                    PHILOSOPHER5__tmpE.name = NEED_LEFT_FORK;
                    PHILOSOPHER5__tmpE.invokeid = PHILOSOPHER5;
                    PHILOSOPHER5__tmpE.origin = PHILOSOPHER5;
                    _lastSeqId = _lastSeqId + 1;
                    PHILOSOPHER5__tmpE.delay = 0;
                    PHILOSOPHER5__tmpE.seqNr = _lastSeqId;
                    PHILOSOPHER5__tmpE.data.p_id = PHILOSOPHER5_p_id;
#if TRACE_EXECUTION
printf("%d: Sending NEED_LEFT_FORK (%d) to ROOT_eQ\n", _pid, PHILOSOPHER5__tmpE.name );
#endif

                    ROOT_eQ!PHILOSOPHER5__tmpE;
                    insertWithDelay(ROOT_eQ);
                  }
                  skip;
                }
                :: else -> skip;
                fi
                skip;
              }
              :: j == 9 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, j);
#endif

                printf("philospher: : %d", PHILOSOPHER5_p_id);
                printf("starved in state has_right_fork for Time(in ms) : : %d", PHILOSOPHER5_delay);
                skip;
              }
              :: j == 10 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for transition %d\n", _pid, j);
#endif

                if
                :: !PHILOSOPHER5_flags[USCXML_CTX_FINISHED] || PHILOSOPHER5_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
                  {
                    PHILOSOPHER5__tmpE.data.p_id = 0;
                    PHILOSOPHER5__tmpE.delay = 0;
                    PHILOSOPHER5__tmpE.invokeid = 0;
                    PHILOSOPHER5__tmpE.name = 0;
                    PHILOSOPHER5__tmpE.origin = 0;
                    PHILOSOPHER5__tmpE.sendid = 0;
                    PHILOSOPHER5__tmpE.seqNr = 0;
                    PHILOSOPHER5__tmpE.name = RETURN_FORKS;
                    PHILOSOPHER5__tmpE.invokeid = PHILOSOPHER5;
                    PHILOSOPHER5__tmpE.origin = PHILOSOPHER5;
                    _lastSeqId = _lastSeqId + 1;
                    PHILOSOPHER5__tmpE.delay = 0;
                    PHILOSOPHER5__tmpE.seqNr = _lastSeqId;
                    PHILOSOPHER5__tmpE.data.p_id = PHILOSOPHER5_p_id;
#if TRACE_EXECUTION
printf("%d: Sending RETURN_FORKS (%d) to ROOT_eQ\n", _pid, PHILOSOPHER5__tmpE.name );
#endif

                    ROOT_eQ!PHILOSOPHER5__tmpE;
                    insertWithDelay(ROOT_eQ);
                  }
                  skip;
                }
                :: else -> skip;
                fi
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
         :: PHILOSOPHER5_states[i].type[USCXML_STATE_FINAL] -> {
           if
           :: PHILOSOPHER5_states[PHILOSOPHER5_states[i].parent].children[1] -> {
             /* exit topmost SCXML state */
             PHILOSOPHER5_flags[USCXML_CTX_TOP_LEVEL_FINAL] = true;
             PHILOSOPHER5_flags[USCXML_CTX_FINISHED] = true;
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
            :: j < PHILOSOPHER5_USCXML_NUMBER_STATES -> {
              if
              :: PHILOSOPHER5_states[j].type[USCXML_STATE_PARALLEL] && PHILOSOPHER5_states[i].ancestors[j] -> {
                PHILOSOPHER5_STATES_CLEAR(PHILOSOPHER5_ctx.tmp_states)
                k = 0;
                do
                :: k < PHILOSOPHER5_USCXML_NUMBER_STATES -> {
                  if
                  :: PHILOSOPHER5_states[k].ancestors[j] && PHILOSOPHER5_config[k] -> {
                    if
                    :: PHILOSOPHER5_states[k].type[USCXML_STATE_FINAL] -> {
                      PHILOSOPHER5_STATES_AND_NOT(PHILOSOPHER5_ctx.tmp_states, PHILOSOPHER5_states[k].ancestors)
                    }
                    :: else -> {
                      PHILOSOPHER5_ctx.tmp_states[k] = true;
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
                :: !PHILOSOPHER5_STATES_HAS_ANY(PHILOSOPHER5_ctx.tmp_states) -> {
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
PHILOSOPHER5_TERMINATE_MACHINE:
skip; d_step {

#if TRACE_EXECUTION
printf("%d: Machine finished\n", _pid);
#endif

/* exit all remaining states */
i = PHILOSOPHER5_USCXML_NUMBER_STATES;
do
:: i > 0 -> {
  i = i - 1;
  if
  :: PHILOSOPHER5_config[i] && PHILOSOPHER5_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
    /* call all on exit handlers */
   if
    :: i == 3 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for exiting state %d\n", _pid, i);
#endif

    if
    :: (PHILOSOPHER5__event.name == TAKE_LEFT_FORK || PHILOSOPHER5__event.name == TAKE_RIGHT_FORK) -> {
        cancelSendId(STARVATION_TIMER,PHILOSOPHER5);
    }
    :: else -> skip;
    fi;
    }
    :: i == 4 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for exiting state %d\n", _pid, i);
#endif

    if
    :: (PHILOSOPHER5__event.name == TAKE_RIGHT_FORK) -> {
        cancelSendId(STARVATION_TIMER,PHILOSOPHER5);
    }
    :: else -> skip;
    fi;
    }
    :: i == 5 -> {

#if TRACE_EXECUTION
printf("%d: Processing executable content for exiting state %d\n", _pid, i);
#endif

    if
    :: (PHILOSOPHER5__event.name == TAKE_LEFT_FORK) -> {
        cancelSendId(STARVATION_TIMER,PHILOSOPHER5);
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
  :: PHILOSOPHER5_invocations[i] -> {
    /* cancel invocations */
    PHILOSOPHER5_invocations[i] = false;
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

removePendingEventsFromInvoker(PHILOSOPHER5)
/* send done event */
if
:: PHILOSOPHER5_flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {
    PHILOSOPHER5__tmpE.data.p_id = 0;
    PHILOSOPHER5__tmpE.delay = 0;
    PHILOSOPHER5__tmpE.invokeid = 0;
    PHILOSOPHER5__tmpE.name = 0;
    PHILOSOPHER5__tmpE.origin = 0;
    PHILOSOPHER5__tmpE.sendid = 0;
    PHILOSOPHER5__tmpE.seqNr = 0;

    PHILOSOPHER5__tmpE.name = DONE_INVOKE_PHILOSOPHER5
    PHILOSOPHER5__tmpE.invokeid = PHILOSOPHER5

#if TRACE_EXECUTION
printf("%d: Sending DONE.INVOKE\n", _pid);
#endif

    ROOT_eQ!PHILOSOPHER5__tmpE;
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
  ROOT_transitions[0].type[USCXML_TRANS_INTERNAL] = 1;
  ROOT_transitions[0].conflicts[0] = 1;
  ROOT_transitions[0].conflicts[1] = 1;
  ROOT_transitions[0].conflicts[2] = 1;
  ROOT_transitions[0].conflicts[3] = 1;
  ROOT_transitions[0].exit_set[2] = 1;

  ROOT_transitions[1].source = 2;
  ROOT_transitions[1].target[2] = 1;
  ROOT_transitions[1].type[USCXML_TRANS_INTERNAL] = 1;
  ROOT_transitions[1].conflicts[0] = 1;
  ROOT_transitions[1].conflicts[1] = 1;
  ROOT_transitions[1].conflicts[2] = 1;
  ROOT_transitions[1].conflicts[3] = 1;
  ROOT_transitions[1].exit_set[2] = 1;

  ROOT_transitions[2].source = 2;
  ROOT_transitions[2].target[2] = 1;
  ROOT_transitions[2].type[USCXML_TRANS_INTERNAL] = 1;
  ROOT_transitions[2].conflicts[0] = 1;
  ROOT_transitions[2].conflicts[1] = 1;
  ROOT_transitions[2].conflicts[2] = 1;
  ROOT_transitions[2].conflicts[3] = 1;
  ROOT_transitions[2].exit_set[2] = 1;

  ROOT_transitions[3].source = 2;
  ROOT_transitions[3].target[3] = 1;
  ROOT_transitions[3].type[USCXML_TRANS_INTERNAL] = 1;
  ROOT_transitions[3].conflicts[0] = 1;
  ROOT_transitions[3].conflicts[1] = 1;
  ROOT_transitions[3].conflicts[2] = 1;
  ROOT_transitions[3].conflicts[3] = 1;
  ROOT_transitions[3].exit_set[1] = 1;
  ROOT_transitions[3].exit_set[2] = 1;
  ROOT_transitions[3].exit_set[3] = 1;


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
  ROOT_left_fork = 0;
  ROOT_right_fork = 0;
  ROOT_seed = 123456789;
  PHILOSOPHER1_transitions[0].source = 2;
  PHILOSOPHER1_transitions[0].target[3] = 1;
  PHILOSOPHER1_transitions[0].type[USCXML_TRANS_INTERNAL] = 1;
  PHILOSOPHER1_transitions[0].conflicts[0] = 1;
  PHILOSOPHER1_transitions[0].conflicts[1] = 1;
  PHILOSOPHER1_transitions[0].conflicts[2] = 1;
  PHILOSOPHER1_transitions[0].conflicts[3] = 1;
  PHILOSOPHER1_transitions[0].conflicts[4] = 1;
  PHILOSOPHER1_transitions[0].conflicts[5] = 1;
  PHILOSOPHER1_transitions[0].conflicts[6] = 1;
  PHILOSOPHER1_transitions[0].conflicts[7] = 1;
  PHILOSOPHER1_transitions[0].conflicts[8] = 1;
  PHILOSOPHER1_transitions[0].conflicts[9] = 1;
  PHILOSOPHER1_transitions[0].conflicts[10] = 1;
  PHILOSOPHER1_transitions[0].exit_set[2] = 1;
  PHILOSOPHER1_transitions[0].exit_set[3] = 1;
  PHILOSOPHER1_transitions[0].exit_set[4] = 1;
  PHILOSOPHER1_transitions[0].exit_set[5] = 1;
  PHILOSOPHER1_transitions[0].exit_set[6] = 1;

  PHILOSOPHER1_transitions[1].source = 3;
  PHILOSOPHER1_transitions[1].target[4] = 1;
  PHILOSOPHER1_transitions[1].type[USCXML_TRANS_INTERNAL] = 1;
  PHILOSOPHER1_transitions[1].conflicts[0] = 1;
  PHILOSOPHER1_transitions[1].conflicts[1] = 1;
  PHILOSOPHER1_transitions[1].conflicts[2] = 1;
  PHILOSOPHER1_transitions[1].conflicts[3] = 1;
  PHILOSOPHER1_transitions[1].conflicts[4] = 1;
  PHILOSOPHER1_transitions[1].conflicts[5] = 1;
  PHILOSOPHER1_transitions[1].conflicts[6] = 1;
  PHILOSOPHER1_transitions[1].conflicts[7] = 1;
  PHILOSOPHER1_transitions[1].conflicts[8] = 1;
  PHILOSOPHER1_transitions[1].conflicts[9] = 1;
  PHILOSOPHER1_transitions[1].conflicts[10] = 1;
  PHILOSOPHER1_transitions[1].exit_set[2] = 1;
  PHILOSOPHER1_transitions[1].exit_set[3] = 1;
  PHILOSOPHER1_transitions[1].exit_set[4] = 1;
  PHILOSOPHER1_transitions[1].exit_set[5] = 1;
  PHILOSOPHER1_transitions[1].exit_set[6] = 1;

  PHILOSOPHER1_transitions[2].source = 3;
  PHILOSOPHER1_transitions[2].target[5] = 1;
  PHILOSOPHER1_transitions[2].type[USCXML_TRANS_INTERNAL] = 1;
  PHILOSOPHER1_transitions[2].conflicts[0] = 1;
  PHILOSOPHER1_transitions[2].conflicts[1] = 1;
  PHILOSOPHER1_transitions[2].conflicts[2] = 1;
  PHILOSOPHER1_transitions[2].conflicts[3] = 1;
  PHILOSOPHER1_transitions[2].conflicts[4] = 1;
  PHILOSOPHER1_transitions[2].conflicts[5] = 1;
  PHILOSOPHER1_transitions[2].conflicts[6] = 1;
  PHILOSOPHER1_transitions[2].conflicts[7] = 1;
  PHILOSOPHER1_transitions[2].conflicts[8] = 1;
  PHILOSOPHER1_transitions[2].conflicts[9] = 1;
  PHILOSOPHER1_transitions[2].conflicts[10] = 1;
  PHILOSOPHER1_transitions[2].exit_set[2] = 1;
  PHILOSOPHER1_transitions[2].exit_set[3] = 1;
  PHILOSOPHER1_transitions[2].exit_set[4] = 1;
  PHILOSOPHER1_transitions[2].exit_set[5] = 1;
  PHILOSOPHER1_transitions[2].exit_set[6] = 1;

  PHILOSOPHER1_transitions[3].source = 3;
  PHILOSOPHER1_transitions[3].target[7] = 1;
  PHILOSOPHER1_transitions[3].type[USCXML_TRANS_INTERNAL] = 1;
  PHILOSOPHER1_transitions[3].conflicts[0] = 1;
  PHILOSOPHER1_transitions[3].conflicts[1] = 1;
  PHILOSOPHER1_transitions[3].conflicts[2] = 1;
  PHILOSOPHER1_transitions[3].conflicts[3] = 1;
  PHILOSOPHER1_transitions[3].conflicts[4] = 1;
  PHILOSOPHER1_transitions[3].conflicts[5] = 1;
  PHILOSOPHER1_transitions[3].conflicts[6] = 1;
  PHILOSOPHER1_transitions[3].conflicts[7] = 1;
  PHILOSOPHER1_transitions[3].conflicts[8] = 1;
  PHILOSOPHER1_transitions[3].conflicts[9] = 1;
  PHILOSOPHER1_transitions[3].conflicts[10] = 1;
  PHILOSOPHER1_transitions[3].exit_set[1] = 1;
  PHILOSOPHER1_transitions[3].exit_set[2] = 1;
  PHILOSOPHER1_transitions[3].exit_set[3] = 1;
  PHILOSOPHER1_transitions[3].exit_set[4] = 1;
  PHILOSOPHER1_transitions[3].exit_set[5] = 1;
  PHILOSOPHER1_transitions[3].exit_set[6] = 1;
  PHILOSOPHER1_transitions[3].exit_set[7] = 1;

  PHILOSOPHER1_transitions[4].source = 4;
  PHILOSOPHER1_transitions[4].target[6] = 1;
  PHILOSOPHER1_transitions[4].type[USCXML_TRANS_INTERNAL] = 1;
  PHILOSOPHER1_transitions[4].conflicts[0] = 1;
  PHILOSOPHER1_transitions[4].conflicts[1] = 1;
  PHILOSOPHER1_transitions[4].conflicts[2] = 1;
  PHILOSOPHER1_transitions[4].conflicts[3] = 1;
  PHILOSOPHER1_transitions[4].conflicts[4] = 1;
  PHILOSOPHER1_transitions[4].conflicts[5] = 1;
  PHILOSOPHER1_transitions[4].conflicts[6] = 1;
  PHILOSOPHER1_transitions[4].conflicts[7] = 1;
  PHILOSOPHER1_transitions[4].conflicts[8] = 1;
  PHILOSOPHER1_transitions[4].conflicts[9] = 1;
  PHILOSOPHER1_transitions[4].conflicts[10] = 1;
  PHILOSOPHER1_transitions[4].exit_set[2] = 1;
  PHILOSOPHER1_transitions[4].exit_set[3] = 1;
  PHILOSOPHER1_transitions[4].exit_set[4] = 1;
  PHILOSOPHER1_transitions[4].exit_set[5] = 1;
  PHILOSOPHER1_transitions[4].exit_set[6] = 1;

  PHILOSOPHER1_transitions[5].source = 4;
  PHILOSOPHER1_transitions[5].target[4] = 1;
  PHILOSOPHER1_transitions[5].type[USCXML_TRANS_INTERNAL] = 1;
  PHILOSOPHER1_transitions[5].conflicts[0] = 1;
  PHILOSOPHER1_transitions[5].conflicts[1] = 1;
  PHILOSOPHER1_transitions[5].conflicts[2] = 1;
  PHILOSOPHER1_transitions[5].conflicts[3] = 1;
  PHILOSOPHER1_transitions[5].conflicts[4] = 1;
  PHILOSOPHER1_transitions[5].conflicts[5] = 1;
  PHILOSOPHER1_transitions[5].conflicts[6] = 1;
  PHILOSOPHER1_transitions[5].conflicts[7] = 1;
  PHILOSOPHER1_transitions[5].conflicts[8] = 1;
  PHILOSOPHER1_transitions[5].conflicts[9] = 1;
  PHILOSOPHER1_transitions[5].conflicts[10] = 1;
  PHILOSOPHER1_transitions[5].exit_set[2] = 1;
  PHILOSOPHER1_transitions[5].exit_set[3] = 1;
  PHILOSOPHER1_transitions[5].exit_set[4] = 1;
  PHILOSOPHER1_transitions[5].exit_set[5] = 1;
  PHILOSOPHER1_transitions[5].exit_set[6] = 1;

  PHILOSOPHER1_transitions[6].source = 4;
  PHILOSOPHER1_transitions[6].target[7] = 1;
  PHILOSOPHER1_transitions[6].type[USCXML_TRANS_INTERNAL] = 1;
  PHILOSOPHER1_transitions[6].conflicts[0] = 1;
  PHILOSOPHER1_transitions[6].conflicts[1] = 1;
  PHILOSOPHER1_transitions[6].conflicts[2] = 1;
  PHILOSOPHER1_transitions[6].conflicts[3] = 1;
  PHILOSOPHER1_transitions[6].conflicts[4] = 1;
  PHILOSOPHER1_transitions[6].conflicts[5] = 1;
  PHILOSOPHER1_transitions[6].conflicts[6] = 1;
  PHILOSOPHER1_transitions[6].conflicts[7] = 1;
  PHILOSOPHER1_transitions[6].conflicts[8] = 1;
  PHILOSOPHER1_transitions[6].conflicts[9] = 1;
  PHILOSOPHER1_transitions[6].conflicts[10] = 1;
  PHILOSOPHER1_transitions[6].exit_set[1] = 1;
  PHILOSOPHER1_transitions[6].exit_set[2] = 1;
  PHILOSOPHER1_transitions[6].exit_set[3] = 1;
  PHILOSOPHER1_transitions[6].exit_set[4] = 1;
  PHILOSOPHER1_transitions[6].exit_set[5] = 1;
  PHILOSOPHER1_transitions[6].exit_set[6] = 1;
  PHILOSOPHER1_transitions[6].exit_set[7] = 1;

  PHILOSOPHER1_transitions[7].source = 5;
  PHILOSOPHER1_transitions[7].target[6] = 1;
  PHILOSOPHER1_transitions[7].type[USCXML_TRANS_INTERNAL] = 1;
  PHILOSOPHER1_transitions[7].conflicts[0] = 1;
  PHILOSOPHER1_transitions[7].conflicts[1] = 1;
  PHILOSOPHER1_transitions[7].conflicts[2] = 1;
  PHILOSOPHER1_transitions[7].conflicts[3] = 1;
  PHILOSOPHER1_transitions[7].conflicts[4] = 1;
  PHILOSOPHER1_transitions[7].conflicts[5] = 1;
  PHILOSOPHER1_transitions[7].conflicts[6] = 1;
  PHILOSOPHER1_transitions[7].conflicts[7] = 1;
  PHILOSOPHER1_transitions[7].conflicts[8] = 1;
  PHILOSOPHER1_transitions[7].conflicts[9] = 1;
  PHILOSOPHER1_transitions[7].conflicts[10] = 1;
  PHILOSOPHER1_transitions[7].exit_set[2] = 1;
  PHILOSOPHER1_transitions[7].exit_set[3] = 1;
  PHILOSOPHER1_transitions[7].exit_set[4] = 1;
  PHILOSOPHER1_transitions[7].exit_set[5] = 1;
  PHILOSOPHER1_transitions[7].exit_set[6] = 1;

  PHILOSOPHER1_transitions[8].source = 5;
  PHILOSOPHER1_transitions[8].target[5] = 1;
  PHILOSOPHER1_transitions[8].type[USCXML_TRANS_INTERNAL] = 1;
  PHILOSOPHER1_transitions[8].conflicts[0] = 1;
  PHILOSOPHER1_transitions[8].conflicts[1] = 1;
  PHILOSOPHER1_transitions[8].conflicts[2] = 1;
  PHILOSOPHER1_transitions[8].conflicts[3] = 1;
  PHILOSOPHER1_transitions[8].conflicts[4] = 1;
  PHILOSOPHER1_transitions[8].conflicts[5] = 1;
  PHILOSOPHER1_transitions[8].conflicts[6] = 1;
  PHILOSOPHER1_transitions[8].conflicts[7] = 1;
  PHILOSOPHER1_transitions[8].conflicts[8] = 1;
  PHILOSOPHER1_transitions[8].conflicts[9] = 1;
  PHILOSOPHER1_transitions[8].conflicts[10] = 1;
  PHILOSOPHER1_transitions[8].exit_set[2] = 1;
  PHILOSOPHER1_transitions[8].exit_set[3] = 1;
  PHILOSOPHER1_transitions[8].exit_set[4] = 1;
  PHILOSOPHER1_transitions[8].exit_set[5] = 1;
  PHILOSOPHER1_transitions[8].exit_set[6] = 1;

  PHILOSOPHER1_transitions[9].source = 5;
  PHILOSOPHER1_transitions[9].target[7] = 1;
  PHILOSOPHER1_transitions[9].type[USCXML_TRANS_INTERNAL] = 1;
  PHILOSOPHER1_transitions[9].conflicts[0] = 1;
  PHILOSOPHER1_transitions[9].conflicts[1] = 1;
  PHILOSOPHER1_transitions[9].conflicts[2] = 1;
  PHILOSOPHER1_transitions[9].conflicts[3] = 1;
  PHILOSOPHER1_transitions[9].conflicts[4] = 1;
  PHILOSOPHER1_transitions[9].conflicts[5] = 1;
  PHILOSOPHER1_transitions[9].conflicts[6] = 1;
  PHILOSOPHER1_transitions[9].conflicts[7] = 1;
  PHILOSOPHER1_transitions[9].conflicts[8] = 1;
  PHILOSOPHER1_transitions[9].conflicts[9] = 1;
  PHILOSOPHER1_transitions[9].conflicts[10] = 1;
  PHILOSOPHER1_transitions[9].exit_set[1] = 1;
  PHILOSOPHER1_transitions[9].exit_set[2] = 1;
  PHILOSOPHER1_transitions[9].exit_set[3] = 1;
  PHILOSOPHER1_transitions[9].exit_set[4] = 1;
  PHILOSOPHER1_transitions[9].exit_set[5] = 1;
  PHILOSOPHER1_transitions[9].exit_set[6] = 1;
  PHILOSOPHER1_transitions[9].exit_set[7] = 1;

  PHILOSOPHER1_transitions[10].source = 6;
  PHILOSOPHER1_transitions[10].target[2] = 1;
  PHILOSOPHER1_transitions[10].type[USCXML_TRANS_INTERNAL] = 1;
  PHILOSOPHER1_transitions[10].conflicts[0] = 1;
  PHILOSOPHER1_transitions[10].conflicts[1] = 1;
  PHILOSOPHER1_transitions[10].conflicts[2] = 1;
  PHILOSOPHER1_transitions[10].conflicts[3] = 1;
  PHILOSOPHER1_transitions[10].conflicts[4] = 1;
  PHILOSOPHER1_transitions[10].conflicts[5] = 1;
  PHILOSOPHER1_transitions[10].conflicts[6] = 1;
  PHILOSOPHER1_transitions[10].conflicts[7] = 1;
  PHILOSOPHER1_transitions[10].conflicts[8] = 1;
  PHILOSOPHER1_transitions[10].conflicts[9] = 1;
  PHILOSOPHER1_transitions[10].conflicts[10] = 1;
  PHILOSOPHER1_transitions[10].exit_set[2] = 1;
  PHILOSOPHER1_transitions[10].exit_set[3] = 1;
  PHILOSOPHER1_transitions[10].exit_set[4] = 1;
  PHILOSOPHER1_transitions[10].exit_set[5] = 1;
  PHILOSOPHER1_transitions[10].exit_set[6] = 1;


  PHILOSOPHER1_states[0].parent = 0;
  PHILOSOPHER1_states[0].children[1] = 1;
  PHILOSOPHER1_states[0].children[7] = 1;
  PHILOSOPHER1_states[0].completion[1] = 1;
  PHILOSOPHER1_states[0].type[USCXML_STATE_COMPOUND] = 1;

  PHILOSOPHER1_states[1].parent = 0;
  PHILOSOPHER1_states[1].children[2] = 1;
  PHILOSOPHER1_states[1].children[3] = 1;
  PHILOSOPHER1_states[1].children[4] = 1;
  PHILOSOPHER1_states[1].children[5] = 1;
  PHILOSOPHER1_states[1].children[6] = 1;
  PHILOSOPHER1_states[1].completion[2] = 1;
  PHILOSOPHER1_states[1].ancestors[0] = 1;
  PHILOSOPHER1_states[1].type[USCXML_STATE_COMPOUND] = 1;

  PHILOSOPHER1_states[2].parent = 1;
  PHILOSOPHER1_states[2].ancestors[0] = 1;
  PHILOSOPHER1_states[2].ancestors[1] = 1;
  PHILOSOPHER1_states[2].type[USCXML_STATE_ATOMIC] = 1;

  PHILOSOPHER1_states[3].parent = 1;
  PHILOSOPHER1_states[3].ancestors[0] = 1;
  PHILOSOPHER1_states[3].ancestors[1] = 1;
  PHILOSOPHER1_states[3].type[USCXML_STATE_ATOMIC] = 1;

  PHILOSOPHER1_states[4].parent = 1;
  PHILOSOPHER1_states[4].ancestors[0] = 1;
  PHILOSOPHER1_states[4].ancestors[1] = 1;
  PHILOSOPHER1_states[4].type[USCXML_STATE_ATOMIC] = 1;

  PHILOSOPHER1_states[5].parent = 1;
  PHILOSOPHER1_states[5].ancestors[0] = 1;
  PHILOSOPHER1_states[5].ancestors[1] = 1;
  PHILOSOPHER1_states[5].type[USCXML_STATE_ATOMIC] = 1;

  PHILOSOPHER1_states[6].parent = 1;
  PHILOSOPHER1_states[6].ancestors[0] = 1;
  PHILOSOPHER1_states[6].ancestors[1] = 1;
  PHILOSOPHER1_states[6].type[USCXML_STATE_ATOMIC] = 1;

  PHILOSOPHER1_states[7].parent = 0;
  PHILOSOPHER1_states[7].ancestors[0] = 1;
  PHILOSOPHER1_states[7].type[USCXML_STATE_FINAL] = 1;


/* initialize data model variables */
  PHILOSOPHER1_flags[USCXML_CTX_PRISTINE]  = true;
  PHILOSOPHER1_flags[USCXML_CTX_SPONTANEOUS] = true;
  PHILOSOPHER2_transitions[0].source = 2;
  PHILOSOPHER2_transitions[0].target[3] = 1;
  PHILOSOPHER2_transitions[0].type[USCXML_TRANS_INTERNAL] = 1;
  PHILOSOPHER2_transitions[0].conflicts[0] = 1;
  PHILOSOPHER2_transitions[0].conflicts[1] = 1;
  PHILOSOPHER2_transitions[0].conflicts[2] = 1;
  PHILOSOPHER2_transitions[0].conflicts[3] = 1;
  PHILOSOPHER2_transitions[0].conflicts[4] = 1;
  PHILOSOPHER2_transitions[0].conflicts[5] = 1;
  PHILOSOPHER2_transitions[0].conflicts[6] = 1;
  PHILOSOPHER2_transitions[0].conflicts[7] = 1;
  PHILOSOPHER2_transitions[0].conflicts[8] = 1;
  PHILOSOPHER2_transitions[0].conflicts[9] = 1;
  PHILOSOPHER2_transitions[0].conflicts[10] = 1;
  PHILOSOPHER2_transitions[0].exit_set[2] = 1;
  PHILOSOPHER2_transitions[0].exit_set[3] = 1;
  PHILOSOPHER2_transitions[0].exit_set[4] = 1;
  PHILOSOPHER2_transitions[0].exit_set[5] = 1;
  PHILOSOPHER2_transitions[0].exit_set[6] = 1;

  PHILOSOPHER2_transitions[1].source = 3;
  PHILOSOPHER2_transitions[1].target[4] = 1;
  PHILOSOPHER2_transitions[1].type[USCXML_TRANS_INTERNAL] = 1;
  PHILOSOPHER2_transitions[1].conflicts[0] = 1;
  PHILOSOPHER2_transitions[1].conflicts[1] = 1;
  PHILOSOPHER2_transitions[1].conflicts[2] = 1;
  PHILOSOPHER2_transitions[1].conflicts[3] = 1;
  PHILOSOPHER2_transitions[1].conflicts[4] = 1;
  PHILOSOPHER2_transitions[1].conflicts[5] = 1;
  PHILOSOPHER2_transitions[1].conflicts[6] = 1;
  PHILOSOPHER2_transitions[1].conflicts[7] = 1;
  PHILOSOPHER2_transitions[1].conflicts[8] = 1;
  PHILOSOPHER2_transitions[1].conflicts[9] = 1;
  PHILOSOPHER2_transitions[1].conflicts[10] = 1;
  PHILOSOPHER2_transitions[1].exit_set[2] = 1;
  PHILOSOPHER2_transitions[1].exit_set[3] = 1;
  PHILOSOPHER2_transitions[1].exit_set[4] = 1;
  PHILOSOPHER2_transitions[1].exit_set[5] = 1;
  PHILOSOPHER2_transitions[1].exit_set[6] = 1;

  PHILOSOPHER2_transitions[2].source = 3;
  PHILOSOPHER2_transitions[2].target[5] = 1;
  PHILOSOPHER2_transitions[2].type[USCXML_TRANS_INTERNAL] = 1;
  PHILOSOPHER2_transitions[2].conflicts[0] = 1;
  PHILOSOPHER2_transitions[2].conflicts[1] = 1;
  PHILOSOPHER2_transitions[2].conflicts[2] = 1;
  PHILOSOPHER2_transitions[2].conflicts[3] = 1;
  PHILOSOPHER2_transitions[2].conflicts[4] = 1;
  PHILOSOPHER2_transitions[2].conflicts[5] = 1;
  PHILOSOPHER2_transitions[2].conflicts[6] = 1;
  PHILOSOPHER2_transitions[2].conflicts[7] = 1;
  PHILOSOPHER2_transitions[2].conflicts[8] = 1;
  PHILOSOPHER2_transitions[2].conflicts[9] = 1;
  PHILOSOPHER2_transitions[2].conflicts[10] = 1;
  PHILOSOPHER2_transitions[2].exit_set[2] = 1;
  PHILOSOPHER2_transitions[2].exit_set[3] = 1;
  PHILOSOPHER2_transitions[2].exit_set[4] = 1;
  PHILOSOPHER2_transitions[2].exit_set[5] = 1;
  PHILOSOPHER2_transitions[2].exit_set[6] = 1;

  PHILOSOPHER2_transitions[3].source = 3;
  PHILOSOPHER2_transitions[3].target[7] = 1;
  PHILOSOPHER2_transitions[3].type[USCXML_TRANS_INTERNAL] = 1;
  PHILOSOPHER2_transitions[3].conflicts[0] = 1;
  PHILOSOPHER2_transitions[3].conflicts[1] = 1;
  PHILOSOPHER2_transitions[3].conflicts[2] = 1;
  PHILOSOPHER2_transitions[3].conflicts[3] = 1;
  PHILOSOPHER2_transitions[3].conflicts[4] = 1;
  PHILOSOPHER2_transitions[3].conflicts[5] = 1;
  PHILOSOPHER2_transitions[3].conflicts[6] = 1;
  PHILOSOPHER2_transitions[3].conflicts[7] = 1;
  PHILOSOPHER2_transitions[3].conflicts[8] = 1;
  PHILOSOPHER2_transitions[3].conflicts[9] = 1;
  PHILOSOPHER2_transitions[3].conflicts[10] = 1;
  PHILOSOPHER2_transitions[3].exit_set[1] = 1;
  PHILOSOPHER2_transitions[3].exit_set[2] = 1;
  PHILOSOPHER2_transitions[3].exit_set[3] = 1;
  PHILOSOPHER2_transitions[3].exit_set[4] = 1;
  PHILOSOPHER2_transitions[3].exit_set[5] = 1;
  PHILOSOPHER2_transitions[3].exit_set[6] = 1;
  PHILOSOPHER2_transitions[3].exit_set[7] = 1;

  PHILOSOPHER2_transitions[4].source = 4;
  PHILOSOPHER2_transitions[4].target[6] = 1;
  PHILOSOPHER2_transitions[4].type[USCXML_TRANS_INTERNAL] = 1;
  PHILOSOPHER2_transitions[4].conflicts[0] = 1;
  PHILOSOPHER2_transitions[4].conflicts[1] = 1;
  PHILOSOPHER2_transitions[4].conflicts[2] = 1;
  PHILOSOPHER2_transitions[4].conflicts[3] = 1;
  PHILOSOPHER2_transitions[4].conflicts[4] = 1;
  PHILOSOPHER2_transitions[4].conflicts[5] = 1;
  PHILOSOPHER2_transitions[4].conflicts[6] = 1;
  PHILOSOPHER2_transitions[4].conflicts[7] = 1;
  PHILOSOPHER2_transitions[4].conflicts[8] = 1;
  PHILOSOPHER2_transitions[4].conflicts[9] = 1;
  PHILOSOPHER2_transitions[4].conflicts[10] = 1;
  PHILOSOPHER2_transitions[4].exit_set[2] = 1;
  PHILOSOPHER2_transitions[4].exit_set[3] = 1;
  PHILOSOPHER2_transitions[4].exit_set[4] = 1;
  PHILOSOPHER2_transitions[4].exit_set[5] = 1;
  PHILOSOPHER2_transitions[4].exit_set[6] = 1;

  PHILOSOPHER2_transitions[5].source = 4;
  PHILOSOPHER2_transitions[5].target[4] = 1;
  PHILOSOPHER2_transitions[5].type[USCXML_TRANS_INTERNAL] = 1;
  PHILOSOPHER2_transitions[5].conflicts[0] = 1;
  PHILOSOPHER2_transitions[5].conflicts[1] = 1;
  PHILOSOPHER2_transitions[5].conflicts[2] = 1;
  PHILOSOPHER2_transitions[5].conflicts[3] = 1;
  PHILOSOPHER2_transitions[5].conflicts[4] = 1;
  PHILOSOPHER2_transitions[5].conflicts[5] = 1;
  PHILOSOPHER2_transitions[5].conflicts[6] = 1;
  PHILOSOPHER2_transitions[5].conflicts[7] = 1;
  PHILOSOPHER2_transitions[5].conflicts[8] = 1;
  PHILOSOPHER2_transitions[5].conflicts[9] = 1;
  PHILOSOPHER2_transitions[5].conflicts[10] = 1;
  PHILOSOPHER2_transitions[5].exit_set[2] = 1;
  PHILOSOPHER2_transitions[5].exit_set[3] = 1;
  PHILOSOPHER2_transitions[5].exit_set[4] = 1;
  PHILOSOPHER2_transitions[5].exit_set[5] = 1;
  PHILOSOPHER2_transitions[5].exit_set[6] = 1;

  PHILOSOPHER2_transitions[6].source = 4;
  PHILOSOPHER2_transitions[6].target[7] = 1;
  PHILOSOPHER2_transitions[6].type[USCXML_TRANS_INTERNAL] = 1;
  PHILOSOPHER2_transitions[6].conflicts[0] = 1;
  PHILOSOPHER2_transitions[6].conflicts[1] = 1;
  PHILOSOPHER2_transitions[6].conflicts[2] = 1;
  PHILOSOPHER2_transitions[6].conflicts[3] = 1;
  PHILOSOPHER2_transitions[6].conflicts[4] = 1;
  PHILOSOPHER2_transitions[6].conflicts[5] = 1;
  PHILOSOPHER2_transitions[6].conflicts[6] = 1;
  PHILOSOPHER2_transitions[6].conflicts[7] = 1;
  PHILOSOPHER2_transitions[6].conflicts[8] = 1;
  PHILOSOPHER2_transitions[6].conflicts[9] = 1;
  PHILOSOPHER2_transitions[6].conflicts[10] = 1;
  PHILOSOPHER2_transitions[6].exit_set[1] = 1;
  PHILOSOPHER2_transitions[6].exit_set[2] = 1;
  PHILOSOPHER2_transitions[6].exit_set[3] = 1;
  PHILOSOPHER2_transitions[6].exit_set[4] = 1;
  PHILOSOPHER2_transitions[6].exit_set[5] = 1;
  PHILOSOPHER2_transitions[6].exit_set[6] = 1;
  PHILOSOPHER2_transitions[6].exit_set[7] = 1;

  PHILOSOPHER2_transitions[7].source = 5;
  PHILOSOPHER2_transitions[7].target[6] = 1;
  PHILOSOPHER2_transitions[7].type[USCXML_TRANS_INTERNAL] = 1;
  PHILOSOPHER2_transitions[7].conflicts[0] = 1;
  PHILOSOPHER2_transitions[7].conflicts[1] = 1;
  PHILOSOPHER2_transitions[7].conflicts[2] = 1;
  PHILOSOPHER2_transitions[7].conflicts[3] = 1;
  PHILOSOPHER2_transitions[7].conflicts[4] = 1;
  PHILOSOPHER2_transitions[7].conflicts[5] = 1;
  PHILOSOPHER2_transitions[7].conflicts[6] = 1;
  PHILOSOPHER2_transitions[7].conflicts[7] = 1;
  PHILOSOPHER2_transitions[7].conflicts[8] = 1;
  PHILOSOPHER2_transitions[7].conflicts[9] = 1;
  PHILOSOPHER2_transitions[7].conflicts[10] = 1;
  PHILOSOPHER2_transitions[7].exit_set[2] = 1;
  PHILOSOPHER2_transitions[7].exit_set[3] = 1;
  PHILOSOPHER2_transitions[7].exit_set[4] = 1;
  PHILOSOPHER2_transitions[7].exit_set[5] = 1;
  PHILOSOPHER2_transitions[7].exit_set[6] = 1;

  PHILOSOPHER2_transitions[8].source = 5;
  PHILOSOPHER2_transitions[8].target[5] = 1;
  PHILOSOPHER2_transitions[8].type[USCXML_TRANS_INTERNAL] = 1;
  PHILOSOPHER2_transitions[8].conflicts[0] = 1;
  PHILOSOPHER2_transitions[8].conflicts[1] = 1;
  PHILOSOPHER2_transitions[8].conflicts[2] = 1;
  PHILOSOPHER2_transitions[8].conflicts[3] = 1;
  PHILOSOPHER2_transitions[8].conflicts[4] = 1;
  PHILOSOPHER2_transitions[8].conflicts[5] = 1;
  PHILOSOPHER2_transitions[8].conflicts[6] = 1;
  PHILOSOPHER2_transitions[8].conflicts[7] = 1;
  PHILOSOPHER2_transitions[8].conflicts[8] = 1;
  PHILOSOPHER2_transitions[8].conflicts[9] = 1;
  PHILOSOPHER2_transitions[8].conflicts[10] = 1;
  PHILOSOPHER2_transitions[8].exit_set[2] = 1;
  PHILOSOPHER2_transitions[8].exit_set[3] = 1;
  PHILOSOPHER2_transitions[8].exit_set[4] = 1;
  PHILOSOPHER2_transitions[8].exit_set[5] = 1;
  PHILOSOPHER2_transitions[8].exit_set[6] = 1;

  PHILOSOPHER2_transitions[9].source = 5;
  PHILOSOPHER2_transitions[9].target[7] = 1;
  PHILOSOPHER2_transitions[9].type[USCXML_TRANS_INTERNAL] = 1;
  PHILOSOPHER2_transitions[9].conflicts[0] = 1;
  PHILOSOPHER2_transitions[9].conflicts[1] = 1;
  PHILOSOPHER2_transitions[9].conflicts[2] = 1;
  PHILOSOPHER2_transitions[9].conflicts[3] = 1;
  PHILOSOPHER2_transitions[9].conflicts[4] = 1;
  PHILOSOPHER2_transitions[9].conflicts[5] = 1;
  PHILOSOPHER2_transitions[9].conflicts[6] = 1;
  PHILOSOPHER2_transitions[9].conflicts[7] = 1;
  PHILOSOPHER2_transitions[9].conflicts[8] = 1;
  PHILOSOPHER2_transitions[9].conflicts[9] = 1;
  PHILOSOPHER2_transitions[9].conflicts[10] = 1;
  PHILOSOPHER2_transitions[9].exit_set[1] = 1;
  PHILOSOPHER2_transitions[9].exit_set[2] = 1;
  PHILOSOPHER2_transitions[9].exit_set[3] = 1;
  PHILOSOPHER2_transitions[9].exit_set[4] = 1;
  PHILOSOPHER2_transitions[9].exit_set[5] = 1;
  PHILOSOPHER2_transitions[9].exit_set[6] = 1;
  PHILOSOPHER2_transitions[9].exit_set[7] = 1;

  PHILOSOPHER2_transitions[10].source = 6;
  PHILOSOPHER2_transitions[10].target[2] = 1;
  PHILOSOPHER2_transitions[10].type[USCXML_TRANS_INTERNAL] = 1;
  PHILOSOPHER2_transitions[10].conflicts[0] = 1;
  PHILOSOPHER2_transitions[10].conflicts[1] = 1;
  PHILOSOPHER2_transitions[10].conflicts[2] = 1;
  PHILOSOPHER2_transitions[10].conflicts[3] = 1;
  PHILOSOPHER2_transitions[10].conflicts[4] = 1;
  PHILOSOPHER2_transitions[10].conflicts[5] = 1;
  PHILOSOPHER2_transitions[10].conflicts[6] = 1;
  PHILOSOPHER2_transitions[10].conflicts[7] = 1;
  PHILOSOPHER2_transitions[10].conflicts[8] = 1;
  PHILOSOPHER2_transitions[10].conflicts[9] = 1;
  PHILOSOPHER2_transitions[10].conflicts[10] = 1;
  PHILOSOPHER2_transitions[10].exit_set[2] = 1;
  PHILOSOPHER2_transitions[10].exit_set[3] = 1;
  PHILOSOPHER2_transitions[10].exit_set[4] = 1;
  PHILOSOPHER2_transitions[10].exit_set[5] = 1;
  PHILOSOPHER2_transitions[10].exit_set[6] = 1;


  PHILOSOPHER2_states[0].parent = 0;
  PHILOSOPHER2_states[0].children[1] = 1;
  PHILOSOPHER2_states[0].children[7] = 1;
  PHILOSOPHER2_states[0].completion[1] = 1;
  PHILOSOPHER2_states[0].type[USCXML_STATE_COMPOUND] = 1;

  PHILOSOPHER2_states[1].parent = 0;
  PHILOSOPHER2_states[1].children[2] = 1;
  PHILOSOPHER2_states[1].children[3] = 1;
  PHILOSOPHER2_states[1].children[4] = 1;
  PHILOSOPHER2_states[1].children[5] = 1;
  PHILOSOPHER2_states[1].children[6] = 1;
  PHILOSOPHER2_states[1].completion[2] = 1;
  PHILOSOPHER2_states[1].ancestors[0] = 1;
  PHILOSOPHER2_states[1].type[USCXML_STATE_COMPOUND] = 1;

  PHILOSOPHER2_states[2].parent = 1;
  PHILOSOPHER2_states[2].ancestors[0] = 1;
  PHILOSOPHER2_states[2].ancestors[1] = 1;
  PHILOSOPHER2_states[2].type[USCXML_STATE_ATOMIC] = 1;

  PHILOSOPHER2_states[3].parent = 1;
  PHILOSOPHER2_states[3].ancestors[0] = 1;
  PHILOSOPHER2_states[3].ancestors[1] = 1;
  PHILOSOPHER2_states[3].type[USCXML_STATE_ATOMIC] = 1;

  PHILOSOPHER2_states[4].parent = 1;
  PHILOSOPHER2_states[4].ancestors[0] = 1;
  PHILOSOPHER2_states[4].ancestors[1] = 1;
  PHILOSOPHER2_states[4].type[USCXML_STATE_ATOMIC] = 1;

  PHILOSOPHER2_states[5].parent = 1;
  PHILOSOPHER2_states[5].ancestors[0] = 1;
  PHILOSOPHER2_states[5].ancestors[1] = 1;
  PHILOSOPHER2_states[5].type[USCXML_STATE_ATOMIC] = 1;

  PHILOSOPHER2_states[6].parent = 1;
  PHILOSOPHER2_states[6].ancestors[0] = 1;
  PHILOSOPHER2_states[6].ancestors[1] = 1;
  PHILOSOPHER2_states[6].type[USCXML_STATE_ATOMIC] = 1;

  PHILOSOPHER2_states[7].parent = 0;
  PHILOSOPHER2_states[7].ancestors[0] = 1;
  PHILOSOPHER2_states[7].type[USCXML_STATE_FINAL] = 1;


/* initialize data model variables */
  PHILOSOPHER2_flags[USCXML_CTX_PRISTINE]  = true;
  PHILOSOPHER2_flags[USCXML_CTX_SPONTANEOUS] = true;
  PHILOSOPHER3_transitions[0].source = 2;
  PHILOSOPHER3_transitions[0].target[3] = 1;
  PHILOSOPHER3_transitions[0].type[USCXML_TRANS_INTERNAL] = 1;
  PHILOSOPHER3_transitions[0].conflicts[0] = 1;
  PHILOSOPHER3_transitions[0].conflicts[1] = 1;
  PHILOSOPHER3_transitions[0].conflicts[2] = 1;
  PHILOSOPHER3_transitions[0].conflicts[3] = 1;
  PHILOSOPHER3_transitions[0].conflicts[4] = 1;
  PHILOSOPHER3_transitions[0].conflicts[5] = 1;
  PHILOSOPHER3_transitions[0].conflicts[6] = 1;
  PHILOSOPHER3_transitions[0].conflicts[7] = 1;
  PHILOSOPHER3_transitions[0].conflicts[8] = 1;
  PHILOSOPHER3_transitions[0].conflicts[9] = 1;
  PHILOSOPHER3_transitions[0].conflicts[10] = 1;
  PHILOSOPHER3_transitions[0].exit_set[2] = 1;
  PHILOSOPHER3_transitions[0].exit_set[3] = 1;
  PHILOSOPHER3_transitions[0].exit_set[4] = 1;
  PHILOSOPHER3_transitions[0].exit_set[5] = 1;
  PHILOSOPHER3_transitions[0].exit_set[6] = 1;

  PHILOSOPHER3_transitions[1].source = 3;
  PHILOSOPHER3_transitions[1].target[4] = 1;
  PHILOSOPHER3_transitions[1].type[USCXML_TRANS_INTERNAL] = 1;
  PHILOSOPHER3_transitions[1].conflicts[0] = 1;
  PHILOSOPHER3_transitions[1].conflicts[1] = 1;
  PHILOSOPHER3_transitions[1].conflicts[2] = 1;
  PHILOSOPHER3_transitions[1].conflicts[3] = 1;
  PHILOSOPHER3_transitions[1].conflicts[4] = 1;
  PHILOSOPHER3_transitions[1].conflicts[5] = 1;
  PHILOSOPHER3_transitions[1].conflicts[6] = 1;
  PHILOSOPHER3_transitions[1].conflicts[7] = 1;
  PHILOSOPHER3_transitions[1].conflicts[8] = 1;
  PHILOSOPHER3_transitions[1].conflicts[9] = 1;
  PHILOSOPHER3_transitions[1].conflicts[10] = 1;
  PHILOSOPHER3_transitions[1].exit_set[2] = 1;
  PHILOSOPHER3_transitions[1].exit_set[3] = 1;
  PHILOSOPHER3_transitions[1].exit_set[4] = 1;
  PHILOSOPHER3_transitions[1].exit_set[5] = 1;
  PHILOSOPHER3_transitions[1].exit_set[6] = 1;

  PHILOSOPHER3_transitions[2].source = 3;
  PHILOSOPHER3_transitions[2].target[5] = 1;
  PHILOSOPHER3_transitions[2].type[USCXML_TRANS_INTERNAL] = 1;
  PHILOSOPHER3_transitions[2].conflicts[0] = 1;
  PHILOSOPHER3_transitions[2].conflicts[1] = 1;
  PHILOSOPHER3_transitions[2].conflicts[2] = 1;
  PHILOSOPHER3_transitions[2].conflicts[3] = 1;
  PHILOSOPHER3_transitions[2].conflicts[4] = 1;
  PHILOSOPHER3_transitions[2].conflicts[5] = 1;
  PHILOSOPHER3_transitions[2].conflicts[6] = 1;
  PHILOSOPHER3_transitions[2].conflicts[7] = 1;
  PHILOSOPHER3_transitions[2].conflicts[8] = 1;
  PHILOSOPHER3_transitions[2].conflicts[9] = 1;
  PHILOSOPHER3_transitions[2].conflicts[10] = 1;
  PHILOSOPHER3_transitions[2].exit_set[2] = 1;
  PHILOSOPHER3_transitions[2].exit_set[3] = 1;
  PHILOSOPHER3_transitions[2].exit_set[4] = 1;
  PHILOSOPHER3_transitions[2].exit_set[5] = 1;
  PHILOSOPHER3_transitions[2].exit_set[6] = 1;

  PHILOSOPHER3_transitions[3].source = 3;
  PHILOSOPHER3_transitions[3].target[7] = 1;
  PHILOSOPHER3_transitions[3].type[USCXML_TRANS_INTERNAL] = 1;
  PHILOSOPHER3_transitions[3].conflicts[0] = 1;
  PHILOSOPHER3_transitions[3].conflicts[1] = 1;
  PHILOSOPHER3_transitions[3].conflicts[2] = 1;
  PHILOSOPHER3_transitions[3].conflicts[3] = 1;
  PHILOSOPHER3_transitions[3].conflicts[4] = 1;
  PHILOSOPHER3_transitions[3].conflicts[5] = 1;
  PHILOSOPHER3_transitions[3].conflicts[6] = 1;
  PHILOSOPHER3_transitions[3].conflicts[7] = 1;
  PHILOSOPHER3_transitions[3].conflicts[8] = 1;
  PHILOSOPHER3_transitions[3].conflicts[9] = 1;
  PHILOSOPHER3_transitions[3].conflicts[10] = 1;
  PHILOSOPHER3_transitions[3].exit_set[1] = 1;
  PHILOSOPHER3_transitions[3].exit_set[2] = 1;
  PHILOSOPHER3_transitions[3].exit_set[3] = 1;
  PHILOSOPHER3_transitions[3].exit_set[4] = 1;
  PHILOSOPHER3_transitions[3].exit_set[5] = 1;
  PHILOSOPHER3_transitions[3].exit_set[6] = 1;
  PHILOSOPHER3_transitions[3].exit_set[7] = 1;

  PHILOSOPHER3_transitions[4].source = 4;
  PHILOSOPHER3_transitions[4].target[6] = 1;
  PHILOSOPHER3_transitions[4].type[USCXML_TRANS_INTERNAL] = 1;
  PHILOSOPHER3_transitions[4].conflicts[0] = 1;
  PHILOSOPHER3_transitions[4].conflicts[1] = 1;
  PHILOSOPHER3_transitions[4].conflicts[2] = 1;
  PHILOSOPHER3_transitions[4].conflicts[3] = 1;
  PHILOSOPHER3_transitions[4].conflicts[4] = 1;
  PHILOSOPHER3_transitions[4].conflicts[5] = 1;
  PHILOSOPHER3_transitions[4].conflicts[6] = 1;
  PHILOSOPHER3_transitions[4].conflicts[7] = 1;
  PHILOSOPHER3_transitions[4].conflicts[8] = 1;
  PHILOSOPHER3_transitions[4].conflicts[9] = 1;
  PHILOSOPHER3_transitions[4].conflicts[10] = 1;
  PHILOSOPHER3_transitions[4].exit_set[2] = 1;
  PHILOSOPHER3_transitions[4].exit_set[3] = 1;
  PHILOSOPHER3_transitions[4].exit_set[4] = 1;
  PHILOSOPHER3_transitions[4].exit_set[5] = 1;
  PHILOSOPHER3_transitions[4].exit_set[6] = 1;

  PHILOSOPHER3_transitions[5].source = 4;
  PHILOSOPHER3_transitions[5].target[4] = 1;
  PHILOSOPHER3_transitions[5].type[USCXML_TRANS_INTERNAL] = 1;
  PHILOSOPHER3_transitions[5].conflicts[0] = 1;
  PHILOSOPHER3_transitions[5].conflicts[1] = 1;
  PHILOSOPHER3_transitions[5].conflicts[2] = 1;
  PHILOSOPHER3_transitions[5].conflicts[3] = 1;
  PHILOSOPHER3_transitions[5].conflicts[4] = 1;
  PHILOSOPHER3_transitions[5].conflicts[5] = 1;
  PHILOSOPHER3_transitions[5].conflicts[6] = 1;
  PHILOSOPHER3_transitions[5].conflicts[7] = 1;
  PHILOSOPHER3_transitions[5].conflicts[8] = 1;
  PHILOSOPHER3_transitions[5].conflicts[9] = 1;
  PHILOSOPHER3_transitions[5].conflicts[10] = 1;
  PHILOSOPHER3_transitions[5].exit_set[2] = 1;
  PHILOSOPHER3_transitions[5].exit_set[3] = 1;
  PHILOSOPHER3_transitions[5].exit_set[4] = 1;
  PHILOSOPHER3_transitions[5].exit_set[5] = 1;
  PHILOSOPHER3_transitions[5].exit_set[6] = 1;

  PHILOSOPHER3_transitions[6].source = 4;
  PHILOSOPHER3_transitions[6].target[7] = 1;
  PHILOSOPHER3_transitions[6].type[USCXML_TRANS_INTERNAL] = 1;
  PHILOSOPHER3_transitions[6].conflicts[0] = 1;
  PHILOSOPHER3_transitions[6].conflicts[1] = 1;
  PHILOSOPHER3_transitions[6].conflicts[2] = 1;
  PHILOSOPHER3_transitions[6].conflicts[3] = 1;
  PHILOSOPHER3_transitions[6].conflicts[4] = 1;
  PHILOSOPHER3_transitions[6].conflicts[5] = 1;
  PHILOSOPHER3_transitions[6].conflicts[6] = 1;
  PHILOSOPHER3_transitions[6].conflicts[7] = 1;
  PHILOSOPHER3_transitions[6].conflicts[8] = 1;
  PHILOSOPHER3_transitions[6].conflicts[9] = 1;
  PHILOSOPHER3_transitions[6].conflicts[10] = 1;
  PHILOSOPHER3_transitions[6].exit_set[1] = 1;
  PHILOSOPHER3_transitions[6].exit_set[2] = 1;
  PHILOSOPHER3_transitions[6].exit_set[3] = 1;
  PHILOSOPHER3_transitions[6].exit_set[4] = 1;
  PHILOSOPHER3_transitions[6].exit_set[5] = 1;
  PHILOSOPHER3_transitions[6].exit_set[6] = 1;
  PHILOSOPHER3_transitions[6].exit_set[7] = 1;

  PHILOSOPHER3_transitions[7].source = 5;
  PHILOSOPHER3_transitions[7].target[6] = 1;
  PHILOSOPHER3_transitions[7].type[USCXML_TRANS_INTERNAL] = 1;
  PHILOSOPHER3_transitions[7].conflicts[0] = 1;
  PHILOSOPHER3_transitions[7].conflicts[1] = 1;
  PHILOSOPHER3_transitions[7].conflicts[2] = 1;
  PHILOSOPHER3_transitions[7].conflicts[3] = 1;
  PHILOSOPHER3_transitions[7].conflicts[4] = 1;
  PHILOSOPHER3_transitions[7].conflicts[5] = 1;
  PHILOSOPHER3_transitions[7].conflicts[6] = 1;
  PHILOSOPHER3_transitions[7].conflicts[7] = 1;
  PHILOSOPHER3_transitions[7].conflicts[8] = 1;
  PHILOSOPHER3_transitions[7].conflicts[9] = 1;
  PHILOSOPHER3_transitions[7].conflicts[10] = 1;
  PHILOSOPHER3_transitions[7].exit_set[2] = 1;
  PHILOSOPHER3_transitions[7].exit_set[3] = 1;
  PHILOSOPHER3_transitions[7].exit_set[4] = 1;
  PHILOSOPHER3_transitions[7].exit_set[5] = 1;
  PHILOSOPHER3_transitions[7].exit_set[6] = 1;

  PHILOSOPHER3_transitions[8].source = 5;
  PHILOSOPHER3_transitions[8].target[5] = 1;
  PHILOSOPHER3_transitions[8].type[USCXML_TRANS_INTERNAL] = 1;
  PHILOSOPHER3_transitions[8].conflicts[0] = 1;
  PHILOSOPHER3_transitions[8].conflicts[1] = 1;
  PHILOSOPHER3_transitions[8].conflicts[2] = 1;
  PHILOSOPHER3_transitions[8].conflicts[3] = 1;
  PHILOSOPHER3_transitions[8].conflicts[4] = 1;
  PHILOSOPHER3_transitions[8].conflicts[5] = 1;
  PHILOSOPHER3_transitions[8].conflicts[6] = 1;
  PHILOSOPHER3_transitions[8].conflicts[7] = 1;
  PHILOSOPHER3_transitions[8].conflicts[8] = 1;
  PHILOSOPHER3_transitions[8].conflicts[9] = 1;
  PHILOSOPHER3_transitions[8].conflicts[10] = 1;
  PHILOSOPHER3_transitions[8].exit_set[2] = 1;
  PHILOSOPHER3_transitions[8].exit_set[3] = 1;
  PHILOSOPHER3_transitions[8].exit_set[4] = 1;
  PHILOSOPHER3_transitions[8].exit_set[5] = 1;
  PHILOSOPHER3_transitions[8].exit_set[6] = 1;

  PHILOSOPHER3_transitions[9].source = 5;
  PHILOSOPHER3_transitions[9].target[7] = 1;
  PHILOSOPHER3_transitions[9].type[USCXML_TRANS_INTERNAL] = 1;
  PHILOSOPHER3_transitions[9].conflicts[0] = 1;
  PHILOSOPHER3_transitions[9].conflicts[1] = 1;
  PHILOSOPHER3_transitions[9].conflicts[2] = 1;
  PHILOSOPHER3_transitions[9].conflicts[3] = 1;
  PHILOSOPHER3_transitions[9].conflicts[4] = 1;
  PHILOSOPHER3_transitions[9].conflicts[5] = 1;
  PHILOSOPHER3_transitions[9].conflicts[6] = 1;
  PHILOSOPHER3_transitions[9].conflicts[7] = 1;
  PHILOSOPHER3_transitions[9].conflicts[8] = 1;
  PHILOSOPHER3_transitions[9].conflicts[9] = 1;
  PHILOSOPHER3_transitions[9].conflicts[10] = 1;
  PHILOSOPHER3_transitions[9].exit_set[1] = 1;
  PHILOSOPHER3_transitions[9].exit_set[2] = 1;
  PHILOSOPHER3_transitions[9].exit_set[3] = 1;
  PHILOSOPHER3_transitions[9].exit_set[4] = 1;
  PHILOSOPHER3_transitions[9].exit_set[5] = 1;
  PHILOSOPHER3_transitions[9].exit_set[6] = 1;
  PHILOSOPHER3_transitions[9].exit_set[7] = 1;

  PHILOSOPHER3_transitions[10].source = 6;
  PHILOSOPHER3_transitions[10].target[2] = 1;
  PHILOSOPHER3_transitions[10].type[USCXML_TRANS_INTERNAL] = 1;
  PHILOSOPHER3_transitions[10].conflicts[0] = 1;
  PHILOSOPHER3_transitions[10].conflicts[1] = 1;
  PHILOSOPHER3_transitions[10].conflicts[2] = 1;
  PHILOSOPHER3_transitions[10].conflicts[3] = 1;
  PHILOSOPHER3_transitions[10].conflicts[4] = 1;
  PHILOSOPHER3_transitions[10].conflicts[5] = 1;
  PHILOSOPHER3_transitions[10].conflicts[6] = 1;
  PHILOSOPHER3_transitions[10].conflicts[7] = 1;
  PHILOSOPHER3_transitions[10].conflicts[8] = 1;
  PHILOSOPHER3_transitions[10].conflicts[9] = 1;
  PHILOSOPHER3_transitions[10].conflicts[10] = 1;
  PHILOSOPHER3_transitions[10].exit_set[2] = 1;
  PHILOSOPHER3_transitions[10].exit_set[3] = 1;
  PHILOSOPHER3_transitions[10].exit_set[4] = 1;
  PHILOSOPHER3_transitions[10].exit_set[5] = 1;
  PHILOSOPHER3_transitions[10].exit_set[6] = 1;


  PHILOSOPHER3_states[0].parent = 0;
  PHILOSOPHER3_states[0].children[1] = 1;
  PHILOSOPHER3_states[0].children[7] = 1;
  PHILOSOPHER3_states[0].completion[1] = 1;
  PHILOSOPHER3_states[0].type[USCXML_STATE_COMPOUND] = 1;

  PHILOSOPHER3_states[1].parent = 0;
  PHILOSOPHER3_states[1].children[2] = 1;
  PHILOSOPHER3_states[1].children[3] = 1;
  PHILOSOPHER3_states[1].children[4] = 1;
  PHILOSOPHER3_states[1].children[5] = 1;
  PHILOSOPHER3_states[1].children[6] = 1;
  PHILOSOPHER3_states[1].completion[2] = 1;
  PHILOSOPHER3_states[1].ancestors[0] = 1;
  PHILOSOPHER3_states[1].type[USCXML_STATE_COMPOUND] = 1;

  PHILOSOPHER3_states[2].parent = 1;
  PHILOSOPHER3_states[2].ancestors[0] = 1;
  PHILOSOPHER3_states[2].ancestors[1] = 1;
  PHILOSOPHER3_states[2].type[USCXML_STATE_ATOMIC] = 1;

  PHILOSOPHER3_states[3].parent = 1;
  PHILOSOPHER3_states[3].ancestors[0] = 1;
  PHILOSOPHER3_states[3].ancestors[1] = 1;
  PHILOSOPHER3_states[3].type[USCXML_STATE_ATOMIC] = 1;

  PHILOSOPHER3_states[4].parent = 1;
  PHILOSOPHER3_states[4].ancestors[0] = 1;
  PHILOSOPHER3_states[4].ancestors[1] = 1;
  PHILOSOPHER3_states[4].type[USCXML_STATE_ATOMIC] = 1;

  PHILOSOPHER3_states[5].parent = 1;
  PHILOSOPHER3_states[5].ancestors[0] = 1;
  PHILOSOPHER3_states[5].ancestors[1] = 1;
  PHILOSOPHER3_states[5].type[USCXML_STATE_ATOMIC] = 1;

  PHILOSOPHER3_states[6].parent = 1;
  PHILOSOPHER3_states[6].ancestors[0] = 1;
  PHILOSOPHER3_states[6].ancestors[1] = 1;
  PHILOSOPHER3_states[6].type[USCXML_STATE_ATOMIC] = 1;

  PHILOSOPHER3_states[7].parent = 0;
  PHILOSOPHER3_states[7].ancestors[0] = 1;
  PHILOSOPHER3_states[7].type[USCXML_STATE_FINAL] = 1;


/* initialize data model variables */
  PHILOSOPHER3_flags[USCXML_CTX_PRISTINE]  = true;
  PHILOSOPHER3_flags[USCXML_CTX_SPONTANEOUS] = true;
  PHILOSOPHER4_transitions[0].source = 2;
  PHILOSOPHER4_transitions[0].target[3] = 1;
  PHILOSOPHER4_transitions[0].type[USCXML_TRANS_INTERNAL] = 1;
  PHILOSOPHER4_transitions[0].conflicts[0] = 1;
  PHILOSOPHER4_transitions[0].conflicts[1] = 1;
  PHILOSOPHER4_transitions[0].conflicts[2] = 1;
  PHILOSOPHER4_transitions[0].conflicts[3] = 1;
  PHILOSOPHER4_transitions[0].conflicts[4] = 1;
  PHILOSOPHER4_transitions[0].conflicts[5] = 1;
  PHILOSOPHER4_transitions[0].conflicts[6] = 1;
  PHILOSOPHER4_transitions[0].conflicts[7] = 1;
  PHILOSOPHER4_transitions[0].conflicts[8] = 1;
  PHILOSOPHER4_transitions[0].conflicts[9] = 1;
  PHILOSOPHER4_transitions[0].conflicts[10] = 1;
  PHILOSOPHER4_transitions[0].exit_set[2] = 1;
  PHILOSOPHER4_transitions[0].exit_set[3] = 1;
  PHILOSOPHER4_transitions[0].exit_set[4] = 1;
  PHILOSOPHER4_transitions[0].exit_set[5] = 1;
  PHILOSOPHER4_transitions[0].exit_set[6] = 1;

  PHILOSOPHER4_transitions[1].source = 3;
  PHILOSOPHER4_transitions[1].target[4] = 1;
  PHILOSOPHER4_transitions[1].type[USCXML_TRANS_INTERNAL] = 1;
  PHILOSOPHER4_transitions[1].conflicts[0] = 1;
  PHILOSOPHER4_transitions[1].conflicts[1] = 1;
  PHILOSOPHER4_transitions[1].conflicts[2] = 1;
  PHILOSOPHER4_transitions[1].conflicts[3] = 1;
  PHILOSOPHER4_transitions[1].conflicts[4] = 1;
  PHILOSOPHER4_transitions[1].conflicts[5] = 1;
  PHILOSOPHER4_transitions[1].conflicts[6] = 1;
  PHILOSOPHER4_transitions[1].conflicts[7] = 1;
  PHILOSOPHER4_transitions[1].conflicts[8] = 1;
  PHILOSOPHER4_transitions[1].conflicts[9] = 1;
  PHILOSOPHER4_transitions[1].conflicts[10] = 1;
  PHILOSOPHER4_transitions[1].exit_set[2] = 1;
  PHILOSOPHER4_transitions[1].exit_set[3] = 1;
  PHILOSOPHER4_transitions[1].exit_set[4] = 1;
  PHILOSOPHER4_transitions[1].exit_set[5] = 1;
  PHILOSOPHER4_transitions[1].exit_set[6] = 1;

  PHILOSOPHER4_transitions[2].source = 3;
  PHILOSOPHER4_transitions[2].target[5] = 1;
  PHILOSOPHER4_transitions[2].type[USCXML_TRANS_INTERNAL] = 1;
  PHILOSOPHER4_transitions[2].conflicts[0] = 1;
  PHILOSOPHER4_transitions[2].conflicts[1] = 1;
  PHILOSOPHER4_transitions[2].conflicts[2] = 1;
  PHILOSOPHER4_transitions[2].conflicts[3] = 1;
  PHILOSOPHER4_transitions[2].conflicts[4] = 1;
  PHILOSOPHER4_transitions[2].conflicts[5] = 1;
  PHILOSOPHER4_transitions[2].conflicts[6] = 1;
  PHILOSOPHER4_transitions[2].conflicts[7] = 1;
  PHILOSOPHER4_transitions[2].conflicts[8] = 1;
  PHILOSOPHER4_transitions[2].conflicts[9] = 1;
  PHILOSOPHER4_transitions[2].conflicts[10] = 1;
  PHILOSOPHER4_transitions[2].exit_set[2] = 1;
  PHILOSOPHER4_transitions[2].exit_set[3] = 1;
  PHILOSOPHER4_transitions[2].exit_set[4] = 1;
  PHILOSOPHER4_transitions[2].exit_set[5] = 1;
  PHILOSOPHER4_transitions[2].exit_set[6] = 1;

  PHILOSOPHER4_transitions[3].source = 3;
  PHILOSOPHER4_transitions[3].target[7] = 1;
  PHILOSOPHER4_transitions[3].type[USCXML_TRANS_INTERNAL] = 1;
  PHILOSOPHER4_transitions[3].conflicts[0] = 1;
  PHILOSOPHER4_transitions[3].conflicts[1] = 1;
  PHILOSOPHER4_transitions[3].conflicts[2] = 1;
  PHILOSOPHER4_transitions[3].conflicts[3] = 1;
  PHILOSOPHER4_transitions[3].conflicts[4] = 1;
  PHILOSOPHER4_transitions[3].conflicts[5] = 1;
  PHILOSOPHER4_transitions[3].conflicts[6] = 1;
  PHILOSOPHER4_transitions[3].conflicts[7] = 1;
  PHILOSOPHER4_transitions[3].conflicts[8] = 1;
  PHILOSOPHER4_transitions[3].conflicts[9] = 1;
  PHILOSOPHER4_transitions[3].conflicts[10] = 1;
  PHILOSOPHER4_transitions[3].exit_set[1] = 1;
  PHILOSOPHER4_transitions[3].exit_set[2] = 1;
  PHILOSOPHER4_transitions[3].exit_set[3] = 1;
  PHILOSOPHER4_transitions[3].exit_set[4] = 1;
  PHILOSOPHER4_transitions[3].exit_set[5] = 1;
  PHILOSOPHER4_transitions[3].exit_set[6] = 1;
  PHILOSOPHER4_transitions[3].exit_set[7] = 1;

  PHILOSOPHER4_transitions[4].source = 4;
  PHILOSOPHER4_transitions[4].target[6] = 1;
  PHILOSOPHER4_transitions[4].type[USCXML_TRANS_INTERNAL] = 1;
  PHILOSOPHER4_transitions[4].conflicts[0] = 1;
  PHILOSOPHER4_transitions[4].conflicts[1] = 1;
  PHILOSOPHER4_transitions[4].conflicts[2] = 1;
  PHILOSOPHER4_transitions[4].conflicts[3] = 1;
  PHILOSOPHER4_transitions[4].conflicts[4] = 1;
  PHILOSOPHER4_transitions[4].conflicts[5] = 1;
  PHILOSOPHER4_transitions[4].conflicts[6] = 1;
  PHILOSOPHER4_transitions[4].conflicts[7] = 1;
  PHILOSOPHER4_transitions[4].conflicts[8] = 1;
  PHILOSOPHER4_transitions[4].conflicts[9] = 1;
  PHILOSOPHER4_transitions[4].conflicts[10] = 1;
  PHILOSOPHER4_transitions[4].exit_set[2] = 1;
  PHILOSOPHER4_transitions[4].exit_set[3] = 1;
  PHILOSOPHER4_transitions[4].exit_set[4] = 1;
  PHILOSOPHER4_transitions[4].exit_set[5] = 1;
  PHILOSOPHER4_transitions[4].exit_set[6] = 1;

  PHILOSOPHER4_transitions[5].source = 4;
  PHILOSOPHER4_transitions[5].target[4] = 1;
  PHILOSOPHER4_transitions[5].type[USCXML_TRANS_INTERNAL] = 1;
  PHILOSOPHER4_transitions[5].conflicts[0] = 1;
  PHILOSOPHER4_transitions[5].conflicts[1] = 1;
  PHILOSOPHER4_transitions[5].conflicts[2] = 1;
  PHILOSOPHER4_transitions[5].conflicts[3] = 1;
  PHILOSOPHER4_transitions[5].conflicts[4] = 1;
  PHILOSOPHER4_transitions[5].conflicts[5] = 1;
  PHILOSOPHER4_transitions[5].conflicts[6] = 1;
  PHILOSOPHER4_transitions[5].conflicts[7] = 1;
  PHILOSOPHER4_transitions[5].conflicts[8] = 1;
  PHILOSOPHER4_transitions[5].conflicts[9] = 1;
  PHILOSOPHER4_transitions[5].conflicts[10] = 1;
  PHILOSOPHER4_transitions[5].exit_set[2] = 1;
  PHILOSOPHER4_transitions[5].exit_set[3] = 1;
  PHILOSOPHER4_transitions[5].exit_set[4] = 1;
  PHILOSOPHER4_transitions[5].exit_set[5] = 1;
  PHILOSOPHER4_transitions[5].exit_set[6] = 1;

  PHILOSOPHER4_transitions[6].source = 4;
  PHILOSOPHER4_transitions[6].target[7] = 1;
  PHILOSOPHER4_transitions[6].type[USCXML_TRANS_INTERNAL] = 1;
  PHILOSOPHER4_transitions[6].conflicts[0] = 1;
  PHILOSOPHER4_transitions[6].conflicts[1] = 1;
  PHILOSOPHER4_transitions[6].conflicts[2] = 1;
  PHILOSOPHER4_transitions[6].conflicts[3] = 1;
  PHILOSOPHER4_transitions[6].conflicts[4] = 1;
  PHILOSOPHER4_transitions[6].conflicts[5] = 1;
  PHILOSOPHER4_transitions[6].conflicts[6] = 1;
  PHILOSOPHER4_transitions[6].conflicts[7] = 1;
  PHILOSOPHER4_transitions[6].conflicts[8] = 1;
  PHILOSOPHER4_transitions[6].conflicts[9] = 1;
  PHILOSOPHER4_transitions[6].conflicts[10] = 1;
  PHILOSOPHER4_transitions[6].exit_set[1] = 1;
  PHILOSOPHER4_transitions[6].exit_set[2] = 1;
  PHILOSOPHER4_transitions[6].exit_set[3] = 1;
  PHILOSOPHER4_transitions[6].exit_set[4] = 1;
  PHILOSOPHER4_transitions[6].exit_set[5] = 1;
  PHILOSOPHER4_transitions[6].exit_set[6] = 1;
  PHILOSOPHER4_transitions[6].exit_set[7] = 1;

  PHILOSOPHER4_transitions[7].source = 5;
  PHILOSOPHER4_transitions[7].target[6] = 1;
  PHILOSOPHER4_transitions[7].type[USCXML_TRANS_INTERNAL] = 1;
  PHILOSOPHER4_transitions[7].conflicts[0] = 1;
  PHILOSOPHER4_transitions[7].conflicts[1] = 1;
  PHILOSOPHER4_transitions[7].conflicts[2] = 1;
  PHILOSOPHER4_transitions[7].conflicts[3] = 1;
  PHILOSOPHER4_transitions[7].conflicts[4] = 1;
  PHILOSOPHER4_transitions[7].conflicts[5] = 1;
  PHILOSOPHER4_transitions[7].conflicts[6] = 1;
  PHILOSOPHER4_transitions[7].conflicts[7] = 1;
  PHILOSOPHER4_transitions[7].conflicts[8] = 1;
  PHILOSOPHER4_transitions[7].conflicts[9] = 1;
  PHILOSOPHER4_transitions[7].conflicts[10] = 1;
  PHILOSOPHER4_transitions[7].exit_set[2] = 1;
  PHILOSOPHER4_transitions[7].exit_set[3] = 1;
  PHILOSOPHER4_transitions[7].exit_set[4] = 1;
  PHILOSOPHER4_transitions[7].exit_set[5] = 1;
  PHILOSOPHER4_transitions[7].exit_set[6] = 1;

  PHILOSOPHER4_transitions[8].source = 5;
  PHILOSOPHER4_transitions[8].target[5] = 1;
  PHILOSOPHER4_transitions[8].type[USCXML_TRANS_INTERNAL] = 1;
  PHILOSOPHER4_transitions[8].conflicts[0] = 1;
  PHILOSOPHER4_transitions[8].conflicts[1] = 1;
  PHILOSOPHER4_transitions[8].conflicts[2] = 1;
  PHILOSOPHER4_transitions[8].conflicts[3] = 1;
  PHILOSOPHER4_transitions[8].conflicts[4] = 1;
  PHILOSOPHER4_transitions[8].conflicts[5] = 1;
  PHILOSOPHER4_transitions[8].conflicts[6] = 1;
  PHILOSOPHER4_transitions[8].conflicts[7] = 1;
  PHILOSOPHER4_transitions[8].conflicts[8] = 1;
  PHILOSOPHER4_transitions[8].conflicts[9] = 1;
  PHILOSOPHER4_transitions[8].conflicts[10] = 1;
  PHILOSOPHER4_transitions[8].exit_set[2] = 1;
  PHILOSOPHER4_transitions[8].exit_set[3] = 1;
  PHILOSOPHER4_transitions[8].exit_set[4] = 1;
  PHILOSOPHER4_transitions[8].exit_set[5] = 1;
  PHILOSOPHER4_transitions[8].exit_set[6] = 1;

  PHILOSOPHER4_transitions[9].source = 5;
  PHILOSOPHER4_transitions[9].target[7] = 1;
  PHILOSOPHER4_transitions[9].type[USCXML_TRANS_INTERNAL] = 1;
  PHILOSOPHER4_transitions[9].conflicts[0] = 1;
  PHILOSOPHER4_transitions[9].conflicts[1] = 1;
  PHILOSOPHER4_transitions[9].conflicts[2] = 1;
  PHILOSOPHER4_transitions[9].conflicts[3] = 1;
  PHILOSOPHER4_transitions[9].conflicts[4] = 1;
  PHILOSOPHER4_transitions[9].conflicts[5] = 1;
  PHILOSOPHER4_transitions[9].conflicts[6] = 1;
  PHILOSOPHER4_transitions[9].conflicts[7] = 1;
  PHILOSOPHER4_transitions[9].conflicts[8] = 1;
  PHILOSOPHER4_transitions[9].conflicts[9] = 1;
  PHILOSOPHER4_transitions[9].conflicts[10] = 1;
  PHILOSOPHER4_transitions[9].exit_set[1] = 1;
  PHILOSOPHER4_transitions[9].exit_set[2] = 1;
  PHILOSOPHER4_transitions[9].exit_set[3] = 1;
  PHILOSOPHER4_transitions[9].exit_set[4] = 1;
  PHILOSOPHER4_transitions[9].exit_set[5] = 1;
  PHILOSOPHER4_transitions[9].exit_set[6] = 1;
  PHILOSOPHER4_transitions[9].exit_set[7] = 1;

  PHILOSOPHER4_transitions[10].source = 6;
  PHILOSOPHER4_transitions[10].target[2] = 1;
  PHILOSOPHER4_transitions[10].type[USCXML_TRANS_INTERNAL] = 1;
  PHILOSOPHER4_transitions[10].conflicts[0] = 1;
  PHILOSOPHER4_transitions[10].conflicts[1] = 1;
  PHILOSOPHER4_transitions[10].conflicts[2] = 1;
  PHILOSOPHER4_transitions[10].conflicts[3] = 1;
  PHILOSOPHER4_transitions[10].conflicts[4] = 1;
  PHILOSOPHER4_transitions[10].conflicts[5] = 1;
  PHILOSOPHER4_transitions[10].conflicts[6] = 1;
  PHILOSOPHER4_transitions[10].conflicts[7] = 1;
  PHILOSOPHER4_transitions[10].conflicts[8] = 1;
  PHILOSOPHER4_transitions[10].conflicts[9] = 1;
  PHILOSOPHER4_transitions[10].conflicts[10] = 1;
  PHILOSOPHER4_transitions[10].exit_set[2] = 1;
  PHILOSOPHER4_transitions[10].exit_set[3] = 1;
  PHILOSOPHER4_transitions[10].exit_set[4] = 1;
  PHILOSOPHER4_transitions[10].exit_set[5] = 1;
  PHILOSOPHER4_transitions[10].exit_set[6] = 1;


  PHILOSOPHER4_states[0].parent = 0;
  PHILOSOPHER4_states[0].children[1] = 1;
  PHILOSOPHER4_states[0].children[7] = 1;
  PHILOSOPHER4_states[0].completion[1] = 1;
  PHILOSOPHER4_states[0].type[USCXML_STATE_COMPOUND] = 1;

  PHILOSOPHER4_states[1].parent = 0;
  PHILOSOPHER4_states[1].children[2] = 1;
  PHILOSOPHER4_states[1].children[3] = 1;
  PHILOSOPHER4_states[1].children[4] = 1;
  PHILOSOPHER4_states[1].children[5] = 1;
  PHILOSOPHER4_states[1].children[6] = 1;
  PHILOSOPHER4_states[1].completion[2] = 1;
  PHILOSOPHER4_states[1].ancestors[0] = 1;
  PHILOSOPHER4_states[1].type[USCXML_STATE_COMPOUND] = 1;

  PHILOSOPHER4_states[2].parent = 1;
  PHILOSOPHER4_states[2].ancestors[0] = 1;
  PHILOSOPHER4_states[2].ancestors[1] = 1;
  PHILOSOPHER4_states[2].type[USCXML_STATE_ATOMIC] = 1;

  PHILOSOPHER4_states[3].parent = 1;
  PHILOSOPHER4_states[3].ancestors[0] = 1;
  PHILOSOPHER4_states[3].ancestors[1] = 1;
  PHILOSOPHER4_states[3].type[USCXML_STATE_ATOMIC] = 1;

  PHILOSOPHER4_states[4].parent = 1;
  PHILOSOPHER4_states[4].ancestors[0] = 1;
  PHILOSOPHER4_states[4].ancestors[1] = 1;
  PHILOSOPHER4_states[4].type[USCXML_STATE_ATOMIC] = 1;

  PHILOSOPHER4_states[5].parent = 1;
  PHILOSOPHER4_states[5].ancestors[0] = 1;
  PHILOSOPHER4_states[5].ancestors[1] = 1;
  PHILOSOPHER4_states[5].type[USCXML_STATE_ATOMIC] = 1;

  PHILOSOPHER4_states[6].parent = 1;
  PHILOSOPHER4_states[6].ancestors[0] = 1;
  PHILOSOPHER4_states[6].ancestors[1] = 1;
  PHILOSOPHER4_states[6].type[USCXML_STATE_ATOMIC] = 1;

  PHILOSOPHER4_states[7].parent = 0;
  PHILOSOPHER4_states[7].ancestors[0] = 1;
  PHILOSOPHER4_states[7].type[USCXML_STATE_FINAL] = 1;


/* initialize data model variables */
  PHILOSOPHER4_flags[USCXML_CTX_PRISTINE]  = true;
  PHILOSOPHER4_flags[USCXML_CTX_SPONTANEOUS] = true;
  PHILOSOPHER5_transitions[0].source = 2;
  PHILOSOPHER5_transitions[0].target[3] = 1;
  PHILOSOPHER5_transitions[0].type[USCXML_TRANS_INTERNAL] = 1;
  PHILOSOPHER5_transitions[0].conflicts[0] = 1;
  PHILOSOPHER5_transitions[0].conflicts[1] = 1;
  PHILOSOPHER5_transitions[0].conflicts[2] = 1;
  PHILOSOPHER5_transitions[0].conflicts[3] = 1;
  PHILOSOPHER5_transitions[0].conflicts[4] = 1;
  PHILOSOPHER5_transitions[0].conflicts[5] = 1;
  PHILOSOPHER5_transitions[0].conflicts[6] = 1;
  PHILOSOPHER5_transitions[0].conflicts[7] = 1;
  PHILOSOPHER5_transitions[0].conflicts[8] = 1;
  PHILOSOPHER5_transitions[0].conflicts[9] = 1;
  PHILOSOPHER5_transitions[0].conflicts[10] = 1;
  PHILOSOPHER5_transitions[0].exit_set[2] = 1;
  PHILOSOPHER5_transitions[0].exit_set[3] = 1;
  PHILOSOPHER5_transitions[0].exit_set[4] = 1;
  PHILOSOPHER5_transitions[0].exit_set[5] = 1;
  PHILOSOPHER5_transitions[0].exit_set[6] = 1;

  PHILOSOPHER5_transitions[1].source = 3;
  PHILOSOPHER5_transitions[1].target[4] = 1;
  PHILOSOPHER5_transitions[1].type[USCXML_TRANS_INTERNAL] = 1;
  PHILOSOPHER5_transitions[1].conflicts[0] = 1;
  PHILOSOPHER5_transitions[1].conflicts[1] = 1;
  PHILOSOPHER5_transitions[1].conflicts[2] = 1;
  PHILOSOPHER5_transitions[1].conflicts[3] = 1;
  PHILOSOPHER5_transitions[1].conflicts[4] = 1;
  PHILOSOPHER5_transitions[1].conflicts[5] = 1;
  PHILOSOPHER5_transitions[1].conflicts[6] = 1;
  PHILOSOPHER5_transitions[1].conflicts[7] = 1;
  PHILOSOPHER5_transitions[1].conflicts[8] = 1;
  PHILOSOPHER5_transitions[1].conflicts[9] = 1;
  PHILOSOPHER5_transitions[1].conflicts[10] = 1;
  PHILOSOPHER5_transitions[1].exit_set[2] = 1;
  PHILOSOPHER5_transitions[1].exit_set[3] = 1;
  PHILOSOPHER5_transitions[1].exit_set[4] = 1;
  PHILOSOPHER5_transitions[1].exit_set[5] = 1;
  PHILOSOPHER5_transitions[1].exit_set[6] = 1;

  PHILOSOPHER5_transitions[2].source = 3;
  PHILOSOPHER5_transitions[2].target[5] = 1;
  PHILOSOPHER5_transitions[2].type[USCXML_TRANS_INTERNAL] = 1;
  PHILOSOPHER5_transitions[2].conflicts[0] = 1;
  PHILOSOPHER5_transitions[2].conflicts[1] = 1;
  PHILOSOPHER5_transitions[2].conflicts[2] = 1;
  PHILOSOPHER5_transitions[2].conflicts[3] = 1;
  PHILOSOPHER5_transitions[2].conflicts[4] = 1;
  PHILOSOPHER5_transitions[2].conflicts[5] = 1;
  PHILOSOPHER5_transitions[2].conflicts[6] = 1;
  PHILOSOPHER5_transitions[2].conflicts[7] = 1;
  PHILOSOPHER5_transitions[2].conflicts[8] = 1;
  PHILOSOPHER5_transitions[2].conflicts[9] = 1;
  PHILOSOPHER5_transitions[2].conflicts[10] = 1;
  PHILOSOPHER5_transitions[2].exit_set[2] = 1;
  PHILOSOPHER5_transitions[2].exit_set[3] = 1;
  PHILOSOPHER5_transitions[2].exit_set[4] = 1;
  PHILOSOPHER5_transitions[2].exit_set[5] = 1;
  PHILOSOPHER5_transitions[2].exit_set[6] = 1;

  PHILOSOPHER5_transitions[3].source = 3;
  PHILOSOPHER5_transitions[3].target[7] = 1;
  PHILOSOPHER5_transitions[3].type[USCXML_TRANS_INTERNAL] = 1;
  PHILOSOPHER5_transitions[3].conflicts[0] = 1;
  PHILOSOPHER5_transitions[3].conflicts[1] = 1;
  PHILOSOPHER5_transitions[3].conflicts[2] = 1;
  PHILOSOPHER5_transitions[3].conflicts[3] = 1;
  PHILOSOPHER5_transitions[3].conflicts[4] = 1;
  PHILOSOPHER5_transitions[3].conflicts[5] = 1;
  PHILOSOPHER5_transitions[3].conflicts[6] = 1;
  PHILOSOPHER5_transitions[3].conflicts[7] = 1;
  PHILOSOPHER5_transitions[3].conflicts[8] = 1;
  PHILOSOPHER5_transitions[3].conflicts[9] = 1;
  PHILOSOPHER5_transitions[3].conflicts[10] = 1;
  PHILOSOPHER5_transitions[3].exit_set[1] = 1;
  PHILOSOPHER5_transitions[3].exit_set[2] = 1;
  PHILOSOPHER5_transitions[3].exit_set[3] = 1;
  PHILOSOPHER5_transitions[3].exit_set[4] = 1;
  PHILOSOPHER5_transitions[3].exit_set[5] = 1;
  PHILOSOPHER5_transitions[3].exit_set[6] = 1;
  PHILOSOPHER5_transitions[3].exit_set[7] = 1;

  PHILOSOPHER5_transitions[4].source = 4;
  PHILOSOPHER5_transitions[4].target[6] = 1;
  PHILOSOPHER5_transitions[4].type[USCXML_TRANS_INTERNAL] = 1;
  PHILOSOPHER5_transitions[4].conflicts[0] = 1;
  PHILOSOPHER5_transitions[4].conflicts[1] = 1;
  PHILOSOPHER5_transitions[4].conflicts[2] = 1;
  PHILOSOPHER5_transitions[4].conflicts[3] = 1;
  PHILOSOPHER5_transitions[4].conflicts[4] = 1;
  PHILOSOPHER5_transitions[4].conflicts[5] = 1;
  PHILOSOPHER5_transitions[4].conflicts[6] = 1;
  PHILOSOPHER5_transitions[4].conflicts[7] = 1;
  PHILOSOPHER5_transitions[4].conflicts[8] = 1;
  PHILOSOPHER5_transitions[4].conflicts[9] = 1;
  PHILOSOPHER5_transitions[4].conflicts[10] = 1;
  PHILOSOPHER5_transitions[4].exit_set[2] = 1;
  PHILOSOPHER5_transitions[4].exit_set[3] = 1;
  PHILOSOPHER5_transitions[4].exit_set[4] = 1;
  PHILOSOPHER5_transitions[4].exit_set[5] = 1;
  PHILOSOPHER5_transitions[4].exit_set[6] = 1;

  PHILOSOPHER5_transitions[5].source = 4;
  PHILOSOPHER5_transitions[5].target[4] = 1;
  PHILOSOPHER5_transitions[5].type[USCXML_TRANS_INTERNAL] = 1;
  PHILOSOPHER5_transitions[5].conflicts[0] = 1;
  PHILOSOPHER5_transitions[5].conflicts[1] = 1;
  PHILOSOPHER5_transitions[5].conflicts[2] = 1;
  PHILOSOPHER5_transitions[5].conflicts[3] = 1;
  PHILOSOPHER5_transitions[5].conflicts[4] = 1;
  PHILOSOPHER5_transitions[5].conflicts[5] = 1;
  PHILOSOPHER5_transitions[5].conflicts[6] = 1;
  PHILOSOPHER5_transitions[5].conflicts[7] = 1;
  PHILOSOPHER5_transitions[5].conflicts[8] = 1;
  PHILOSOPHER5_transitions[5].conflicts[9] = 1;
  PHILOSOPHER5_transitions[5].conflicts[10] = 1;
  PHILOSOPHER5_transitions[5].exit_set[2] = 1;
  PHILOSOPHER5_transitions[5].exit_set[3] = 1;
  PHILOSOPHER5_transitions[5].exit_set[4] = 1;
  PHILOSOPHER5_transitions[5].exit_set[5] = 1;
  PHILOSOPHER5_transitions[5].exit_set[6] = 1;

  PHILOSOPHER5_transitions[6].source = 4;
  PHILOSOPHER5_transitions[6].target[7] = 1;
  PHILOSOPHER5_transitions[6].type[USCXML_TRANS_INTERNAL] = 1;
  PHILOSOPHER5_transitions[6].conflicts[0] = 1;
  PHILOSOPHER5_transitions[6].conflicts[1] = 1;
  PHILOSOPHER5_transitions[6].conflicts[2] = 1;
  PHILOSOPHER5_transitions[6].conflicts[3] = 1;
  PHILOSOPHER5_transitions[6].conflicts[4] = 1;
  PHILOSOPHER5_transitions[6].conflicts[5] = 1;
  PHILOSOPHER5_transitions[6].conflicts[6] = 1;
  PHILOSOPHER5_transitions[6].conflicts[7] = 1;
  PHILOSOPHER5_transitions[6].conflicts[8] = 1;
  PHILOSOPHER5_transitions[6].conflicts[9] = 1;
  PHILOSOPHER5_transitions[6].conflicts[10] = 1;
  PHILOSOPHER5_transitions[6].exit_set[1] = 1;
  PHILOSOPHER5_transitions[6].exit_set[2] = 1;
  PHILOSOPHER5_transitions[6].exit_set[3] = 1;
  PHILOSOPHER5_transitions[6].exit_set[4] = 1;
  PHILOSOPHER5_transitions[6].exit_set[5] = 1;
  PHILOSOPHER5_transitions[6].exit_set[6] = 1;
  PHILOSOPHER5_transitions[6].exit_set[7] = 1;

  PHILOSOPHER5_transitions[7].source = 5;
  PHILOSOPHER5_transitions[7].target[6] = 1;
  PHILOSOPHER5_transitions[7].type[USCXML_TRANS_INTERNAL] = 1;
  PHILOSOPHER5_transitions[7].conflicts[0] = 1;
  PHILOSOPHER5_transitions[7].conflicts[1] = 1;
  PHILOSOPHER5_transitions[7].conflicts[2] = 1;
  PHILOSOPHER5_transitions[7].conflicts[3] = 1;
  PHILOSOPHER5_transitions[7].conflicts[4] = 1;
  PHILOSOPHER5_transitions[7].conflicts[5] = 1;
  PHILOSOPHER5_transitions[7].conflicts[6] = 1;
  PHILOSOPHER5_transitions[7].conflicts[7] = 1;
  PHILOSOPHER5_transitions[7].conflicts[8] = 1;
  PHILOSOPHER5_transitions[7].conflicts[9] = 1;
  PHILOSOPHER5_transitions[7].conflicts[10] = 1;
  PHILOSOPHER5_transitions[7].exit_set[2] = 1;
  PHILOSOPHER5_transitions[7].exit_set[3] = 1;
  PHILOSOPHER5_transitions[7].exit_set[4] = 1;
  PHILOSOPHER5_transitions[7].exit_set[5] = 1;
  PHILOSOPHER5_transitions[7].exit_set[6] = 1;

  PHILOSOPHER5_transitions[8].source = 5;
  PHILOSOPHER5_transitions[8].target[5] = 1;
  PHILOSOPHER5_transitions[8].type[USCXML_TRANS_INTERNAL] = 1;
  PHILOSOPHER5_transitions[8].conflicts[0] = 1;
  PHILOSOPHER5_transitions[8].conflicts[1] = 1;
  PHILOSOPHER5_transitions[8].conflicts[2] = 1;
  PHILOSOPHER5_transitions[8].conflicts[3] = 1;
  PHILOSOPHER5_transitions[8].conflicts[4] = 1;
  PHILOSOPHER5_transitions[8].conflicts[5] = 1;
  PHILOSOPHER5_transitions[8].conflicts[6] = 1;
  PHILOSOPHER5_transitions[8].conflicts[7] = 1;
  PHILOSOPHER5_transitions[8].conflicts[8] = 1;
  PHILOSOPHER5_transitions[8].conflicts[9] = 1;
  PHILOSOPHER5_transitions[8].conflicts[10] = 1;
  PHILOSOPHER5_transitions[8].exit_set[2] = 1;
  PHILOSOPHER5_transitions[8].exit_set[3] = 1;
  PHILOSOPHER5_transitions[8].exit_set[4] = 1;
  PHILOSOPHER5_transitions[8].exit_set[5] = 1;
  PHILOSOPHER5_transitions[8].exit_set[6] = 1;

  PHILOSOPHER5_transitions[9].source = 5;
  PHILOSOPHER5_transitions[9].target[7] = 1;
  PHILOSOPHER5_transitions[9].type[USCXML_TRANS_INTERNAL] = 1;
  PHILOSOPHER5_transitions[9].conflicts[0] = 1;
  PHILOSOPHER5_transitions[9].conflicts[1] = 1;
  PHILOSOPHER5_transitions[9].conflicts[2] = 1;
  PHILOSOPHER5_transitions[9].conflicts[3] = 1;
  PHILOSOPHER5_transitions[9].conflicts[4] = 1;
  PHILOSOPHER5_transitions[9].conflicts[5] = 1;
  PHILOSOPHER5_transitions[9].conflicts[6] = 1;
  PHILOSOPHER5_transitions[9].conflicts[7] = 1;
  PHILOSOPHER5_transitions[9].conflicts[8] = 1;
  PHILOSOPHER5_transitions[9].conflicts[9] = 1;
  PHILOSOPHER5_transitions[9].conflicts[10] = 1;
  PHILOSOPHER5_transitions[9].exit_set[1] = 1;
  PHILOSOPHER5_transitions[9].exit_set[2] = 1;
  PHILOSOPHER5_transitions[9].exit_set[3] = 1;
  PHILOSOPHER5_transitions[9].exit_set[4] = 1;
  PHILOSOPHER5_transitions[9].exit_set[5] = 1;
  PHILOSOPHER5_transitions[9].exit_set[6] = 1;
  PHILOSOPHER5_transitions[9].exit_set[7] = 1;

  PHILOSOPHER5_transitions[10].source = 6;
  PHILOSOPHER5_transitions[10].target[2] = 1;
  PHILOSOPHER5_transitions[10].type[USCXML_TRANS_INTERNAL] = 1;
  PHILOSOPHER5_transitions[10].conflicts[0] = 1;
  PHILOSOPHER5_transitions[10].conflicts[1] = 1;
  PHILOSOPHER5_transitions[10].conflicts[2] = 1;
  PHILOSOPHER5_transitions[10].conflicts[3] = 1;
  PHILOSOPHER5_transitions[10].conflicts[4] = 1;
  PHILOSOPHER5_transitions[10].conflicts[5] = 1;
  PHILOSOPHER5_transitions[10].conflicts[6] = 1;
  PHILOSOPHER5_transitions[10].conflicts[7] = 1;
  PHILOSOPHER5_transitions[10].conflicts[8] = 1;
  PHILOSOPHER5_transitions[10].conflicts[9] = 1;
  PHILOSOPHER5_transitions[10].conflicts[10] = 1;
  PHILOSOPHER5_transitions[10].exit_set[2] = 1;
  PHILOSOPHER5_transitions[10].exit_set[3] = 1;
  PHILOSOPHER5_transitions[10].exit_set[4] = 1;
  PHILOSOPHER5_transitions[10].exit_set[5] = 1;
  PHILOSOPHER5_transitions[10].exit_set[6] = 1;


  PHILOSOPHER5_states[0].parent = 0;
  PHILOSOPHER5_states[0].children[1] = 1;
  PHILOSOPHER5_states[0].children[7] = 1;
  PHILOSOPHER5_states[0].completion[1] = 1;
  PHILOSOPHER5_states[0].type[USCXML_STATE_COMPOUND] = 1;

  PHILOSOPHER5_states[1].parent = 0;
  PHILOSOPHER5_states[1].children[2] = 1;
  PHILOSOPHER5_states[1].children[3] = 1;
  PHILOSOPHER5_states[1].children[4] = 1;
  PHILOSOPHER5_states[1].children[5] = 1;
  PHILOSOPHER5_states[1].children[6] = 1;
  PHILOSOPHER5_states[1].completion[2] = 1;
  PHILOSOPHER5_states[1].ancestors[0] = 1;
  PHILOSOPHER5_states[1].type[USCXML_STATE_COMPOUND] = 1;

  PHILOSOPHER5_states[2].parent = 1;
  PHILOSOPHER5_states[2].ancestors[0] = 1;
  PHILOSOPHER5_states[2].ancestors[1] = 1;
  PHILOSOPHER5_states[2].type[USCXML_STATE_ATOMIC] = 1;

  PHILOSOPHER5_states[3].parent = 1;
  PHILOSOPHER5_states[3].ancestors[0] = 1;
  PHILOSOPHER5_states[3].ancestors[1] = 1;
  PHILOSOPHER5_states[3].type[USCXML_STATE_ATOMIC] = 1;

  PHILOSOPHER5_states[4].parent = 1;
  PHILOSOPHER5_states[4].ancestors[0] = 1;
  PHILOSOPHER5_states[4].ancestors[1] = 1;
  PHILOSOPHER5_states[4].type[USCXML_STATE_ATOMIC] = 1;

  PHILOSOPHER5_states[5].parent = 1;
  PHILOSOPHER5_states[5].ancestors[0] = 1;
  PHILOSOPHER5_states[5].ancestors[1] = 1;
  PHILOSOPHER5_states[5].type[USCXML_STATE_ATOMIC] = 1;

  PHILOSOPHER5_states[6].parent = 1;
  PHILOSOPHER5_states[6].ancestors[0] = 1;
  PHILOSOPHER5_states[6].ancestors[1] = 1;
  PHILOSOPHER5_states[6].type[USCXML_STATE_ATOMIC] = 1;

  PHILOSOPHER5_states[7].parent = 0;
  PHILOSOPHER5_states[7].ancestors[0] = 1;
  PHILOSOPHER5_states[7].type[USCXML_STATE_FINAL] = 1;


/* initialize data model variables */
  PHILOSOPHER5_flags[USCXML_CTX_PRISTINE]  = true;
  PHILOSOPHER5_flags[USCXML_CTX_SPONTANEOUS] = true;

  run ROOT_step() priority 10;
}

ltl w3c { always !(ROOT_config[ROOT_FAIL]) }
