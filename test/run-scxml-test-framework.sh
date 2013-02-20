#!/bin/sh

set -e

ME=`basename $0`
DIR="$( cd "$( dirname "$0" )" && pwd )" 

if [ -z $1 ]; then
  echo
  echo "Expected filename of scxml-test-framework-client as first argument"
  echo
  exit;
fi
SCXML_TEST_FRAMEWORK_FULL="$( cd "$(dirname "$1")" && pwd)/$(basename $1)"
SCXML_TEST_FRAMEWORK_NAME=$(basename $1)

if [[ ! -x "${SCXML_TEST_FRAMEWORK_FULL}" ]]; then
  echo
  echo "${SCXML_TEST_FRAMEWORK_FULL} not an executable file"
  echo
fi

TESTS=""
# TESTS="${TESTS} scxml-test-framework/test/actionSend/send1.scxml" # passed
# TESTS="${TESTS} scxml-test-framework/test/actionSend/send2.scxml" # passed
# TESTS="${TESTS} scxml-test-framework/test/actionSend/send3.scxml" # passed
# TESTS="${TESTS} scxml-test-framework/test/actionSend/send4.scxml" # won't support
# TESTS="${TESTS} scxml-test-framework/test/actionSend/send5.scxml" # won't support
# TESTS="${TESTS} scxml-test-framework/test/actionSend/send6.scxml" # won't support
# TESTS="${TESTS} scxml-test-framework/test/actionSend/send7.scxml" # passed
# TESTS="${TESTS} scxml-test-framework/test/actionSend/send8.scxml" # won't support

# TESTS="${TESTS} scxml-test-framework/test/assign-current-small-step/test0.scxml" # passed
# TESTS="${TESTS} scxml-test-framework/test/assign-current-small-step/test1.scxml" # passed
# TESTS="${TESTS} scxml-test-framework/test/assign-current-small-step/test2.scxml" # passed
# TESTS="${TESTS} scxml-test-framework/test/assign-current-small-step/test3.scxml" # passed
# TESTS="${TESTS} scxml-test-framework/test/assign-current-small-step/test4.scxml" # passed

# TESTS="${TESTS} scxml-test-framework/test/assign-next-small-step/test0.scxml" # failed
# TESTS="${TESTS} scxml-test-framework/test/assign-next-small-step/test1.scxml" # never terminates: getData not defined
# TESTS="${TESTS} scxml-test-framework/test/assign-next-small-step/test2.scxml" # never terminates: getData not defined
# TESTS="${TESTS} scxml-test-framework/test/assign-next-small-step/test3.scxml" # failed

# TESTS="${TESTS} scxml-test-framework/test/atom3-basic-tests/m0.scxml" # passed
# TESTS="${TESTS} scxml-test-framework/test/atom3-basic-tests/m1.scxml" # passed
# TESTS="${TESTS} scxml-test-framework/test/atom3-basic-tests/m2.scxml" # passed
# TESTS="${TESTS} scxml-test-framework/test/atom3-basic-tests/m3.scxml" # passed

# TESTS="${TESTS} scxml-test-framework/test/basic/basic0.scxml" # passed
# TESTS="${TESTS} scxml-test-framework/test/basic/basic1.scxml" # passed
# TESTS="${TESTS} scxml-test-framework/test/basic/basic2.scxml" # passed

# TESTS="${TESTS} scxml-test-framework/test/cond-js/test0.scxml" # passed
# TESTS="${TESTS} scxml-test-framework/test/cond-js/test1.scxml" # passed
# TESTS="${TESTS} scxml-test-framework/test/cond-js/test2.scxml" # passed
# TESTS="${TESTS} scxml-test-framework/test/cond-js/TestConditionalTransition.scxml" # passed

# TESTS="${TESTS} scxml-test-framework/test/default-initial-state/initial1.scxml" # passed
# TESTS="${TESTS} scxml-test-framework/test/default-initial-state/initial2.scxml" # passed
# TESTS="${TESTS} scxml-test-framework/test/default-initial-state/initial3.scxml" # passed

# TESTS="${TESTS} scxml-test-framework/test/delayedSend/send1.scxml" # won't support: stable config is c not b
# TESTS="${TESTS} scxml-test-framework/test/delayedSend/send2.scxml" # won't support: stable config is c not b
# TESTS="${TESTS} scxml-test-framework/test/delayedSend/send3.scxml" # won't support: stable config is c not b

# TESTS="${TESTS} scxml-test-framework/test/documentOrder/documentOrder0.scxml" # passed

# TESTS="${TESTS} scxml-test-framework/test/foreach/test1.scxml" # passed

# TESTS="${TESTS} scxml-test-framework/test/hierarchy/hier0.scxml" # passed
# TESTS="${TESTS} scxml-test-framework/test/hierarchy/hier1.scxml" # passed
# TESTS="${TESTS} scxml-test-framework/test/hierarchy/hier2.scxml" # passed

# TESTS="${TESTS} scxml-test-framework/test/hierarchy+documentOrder/test0.scxml" # passed
# TESTS="${TESTS} scxml-test-framework/test/hierarchy+documentOrder/test1.scxml" # passed

# TESTS="${TESTS} scxml-test-framework/test/history/history0.scxml" # passed
# TESTS="${TESTS} scxml-test-framework/test/history/history1.scxml" # passed
# TESTS="${TESTS} scxml-test-framework/test/history/history2.scxml" # passed
# TESTS="${TESTS} scxml-test-framework/test/history/history3.scxml" # passed
# TESTS="${TESTS} scxml-test-framework/test/history/history4.scxml" # passed: removed history from "getChildStates" - see mail to w3c list
# TESTS="${TESTS} scxml-test-framework/test/history/history5.scxml" # passed
# TESTS="${TESTS} scxml-test-framework/test/history/history6.scxml" # passed

# TESTS="${TESTS} scxml-test-framework/test/if-else/test0.scxml" # failed: we enter state b with a === 11

# TESTS="${TESTS} scxml-test-framework/test/in/TestInPredicate.scxml" # passed

# TESTS="${TESTS} scxml-test-framework/test/more-parallel/test0.scxml" # passed
# TESTS="${TESTS} scxml-test-framework/test/more-parallel/test1.scxml" # passed
# TESTS="${TESTS} scxml-test-framework/test/more-parallel/test2.scxml" # passed
# TESTS="${TESTS} scxml-test-framework/test/more-parallel/test3.scxml" # failed: entered a1, b2 instead of a2, b2
# TESTS="${TESTS} scxml-test-framework/test/more-parallel/test4.scxml" # passed
# TESTS="${TESTS} scxml-test-framework/test/more-parallel/test5.scxml" # passed
# TESTS="${TESTS} scxml-test-framework/test/more-parallel/test6.scxml" # failed: entered a11, b12 instead of a22, b12
# TESTS="${TESTS} scxml-test-framework/test/more-parallel/test7.scxml" # passed
# TESTS="${TESTS} scxml-test-framework/test/more-parallel/test8.scxml" # passed
# TESTS="${TESTS} scxml-test-framework/test/more-parallel/test9.scxml" # passed

# TESTS="${TESTS} scxml-test-framework/test/multiple-events-per-transition/test1.scxml" # passed

# TESTS="${TESTS} scxml-test-framework/test/parallel/test0.scxml" # passed
# TESTS="${TESTS} scxml-test-framework/test/parallel/test1.scxml" # failed
# TESTS="${TESTS} scxml-test-framework/test/parallel/test2.scxml" # passed
# TESTS="${TESTS} scxml-test-framework/test/parallel/test3.scxml" # passed

# TESTS="${TESTS} scxml-test-framework/test/parallel+interrupt/test0.scxml" # failed
# TESTS="${TESTS} scxml-test-framework/test/parallel+interrupt/test1.scxml" # failed
# TESTS="${TESTS} scxml-test-framework/test/parallel+interrupt/test10.scxml" # passed
# TESTS="${TESTS} scxml-test-framework/test/parallel+interrupt/test11.scxml" # failed
# TESTS="${TESTS} scxml-test-framework/test/parallel+interrupt/test12.scxml" # failed
# TESTS="${TESTS} scxml-test-framework/test/parallel+interrupt/test13.scxml" # failed: transitioning to d not {c1, c2} on t
# TESTS="${TESTS} scxml-test-framework/test/parallel+interrupt/test14.scxml" # failed
# TESTS="${TESTS} scxml-test-framework/test/parallel+interrupt/test15.scxml" # failed
# TESTS="${TESTS} scxml-test-framework/test/parallel+interrupt/test16.scxml" # failed
# TESTS="${TESTS} scxml-test-framework/test/parallel+interrupt/test17.scxml" # failed
# TESTS="${TESTS} scxml-test-framework/test/parallel+interrupt/test18.scxml" # passed
# TESTS="${TESTS} scxml-test-framework/test/parallel+interrupt/test19.scxml" # failed
# TESTS="${TESTS} scxml-test-framework/test/parallel+interrupt/test2.scxml" # failed
# TESTS="${TESTS} scxml-test-framework/test/parallel+interrupt/test20.scxml" # failed
# TESTS="${TESTS} scxml-test-framework/test/parallel+interrupt/test21.scxml" # passed
# TESTS="${TESTS} scxml-test-framework/test/parallel+interrupt/test22.scxml" # failed
# TESTS="${TESTS} scxml-test-framework/test/parallel+interrupt/test23.scxml" # passed
# TESTS="${TESTS} scxml-test-framework/test/parallel+interrupt/test24.scxml" # failed
# TESTS="${TESTS} scxml-test-framework/test/parallel+interrupt/test25.scxml" # failed
# TESTS="${TESTS} scxml-test-framework/test/parallel+interrupt/test26.scxml" # passed
# TESTS="${TESTS} scxml-test-framework/test/parallel+interrupt/test27.scxml" # failed
# TESTS="${TESTS} scxml-test-framework/test/parallel+interrupt/test28.scxml" # passed
# TESTS="${TESTS} scxml-test-framework/test/parallel+interrupt/test29.scxml" # passed
# TESTS="${TESTS} scxml-test-framework/test/parallel+interrupt/test3.scxml" # failed
# TESTS="${TESTS} scxml-test-framework/test/parallel+interrupt/test30.scxml" # failed
# TESTS="${TESTS} scxml-test-framework/test/parallel+interrupt/test31.scxml" # failed
# TESTS="${TESTS} scxml-test-framework/test/parallel+interrupt/test4.scxml" # failed
# TESTS="${TESTS} scxml-test-framework/test/parallel+interrupt/test5.scxml" # failed
# TESTS="${TESTS} scxml-test-framework/test/parallel+interrupt/test6.scxml" # failed
# TESTS="${TESTS} scxml-test-framework/test/parallel+interrupt/test7.scxml" # failed
# TESTS="${TESTS} scxml-test-framework/test/parallel+interrupt/test8.scxml" # passed
# TESTS="${TESTS} scxml-test-framework/test/parallel+interrupt/test9.scxml" # passed

# TESTS="${TESTS} scxml-test-framework/test/script/test0.scxml" # getData not defined
# TESTS="${TESTS} scxml-test-framework/test/script/test1.scxml" # getData not defined
# TESTS="${TESTS} scxml-test-framework/test/script/test2.scxml" # getData not defined
# TESTS="${TESTS} scxml-test-framework/test/script-src/test0.scxml" # getData not defined
# TESTS="${TESTS} scxml-test-framework/test/script-src/test1.scxml" # getData not defined
#TESTS="${TESTS} scxml-test-framework/test/script-src/test2.scxml" # getData not defined
# TESTS="${TESTS} scxml-test-framework/test/script-src/test3.scxml" # getData not defined

# TESTS="${TESTS} scxml-test-framework/test/scxml-prefix-event-name-matching/star0.scxml" # passed
# TESTS="${TESTS} scxml-test-framework/test/scxml-prefix-event-name-matching/test0.scxml" # passed
# TESTS="${TESTS} scxml-test-framework/test/scxml-prefix-event-name-matching/test1.scxml" # passed

# TESTS="${TESTS} scxml-test-framework/test/send-data/send1.scxml" # failed: typing issue with ===
# TESTS="${TESTS} scxml-test-framework/test/send-internal/test0.scxml" # failed: typing issue with ===

# TESTS="${TESTS} scxml-test-framework/test/targetless-transition/test0.scxml" # passed
# TESTS="${TESTS} scxml-test-framework/test/targetless-transition/test1.scxml" # passed
# TESTS="${TESTS} scxml-test-framework/test/targetless-transition/test2.scxml" # passed
# TESTS="${TESTS} scxml-test-framework/test/targetless-transition/test3.scxml" # failed

TESTS="${TESTS} scxml-test-framework/test/*/*.scxml"

#trap 'killall ${SCXML_TEST_FRAMEWORK_NAME}' 0
#$SCXML_TEST_FRAMEWORK_FULL &
#sleep 1
cd $DIR

node scxml-test-framework --test-server-url http://localhost:8080/test $TESTS
