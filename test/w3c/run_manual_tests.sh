#!/bin/bash

USCXML_BIN=$1;
DATA_MODEL=$2;

echo
echo
echo "---- test178.scxml: --------"
echo "we test that multiple key/value pairs are included, even when the keys are the"
echo "same. This is a manual test. The tester must look at the log output and verify"
echo "that both keys are there. (This test uses the SCXML Event I/O processor, which"
echo "is the only one that all platforms must support. It does not specify the"
echo "message format, so we cannot test _event.raw directly. Therefore we print it"
echo "out for visual inspection"
echo

$USCXML_BIN -v ${DATA_MODEL}/test178.scxml


echo
echo
echo "---- test230.scxml: --------"
echo "a manual test that an autofowarded event has the same fields and values as the"
echo "original event. the child process sends the parent process an event which is"
echo "forwarded back to it. Both the parent and child process print out the contents"
echo "of the event. The tester must check if they are the same and report his result."
echo

$USCXML_BIN -v ${DATA_MODEL}/test230.scxml


echo
echo
echo "---- test250.scxml: --------"
echo "test that the onexit handlers run in the invoked process if it is cancelled."
echo "This has to be a manual test, since this process won't accept any events from"
echo "the child process once it has been cancelled. Tester must examine log output"
echo "from child process to determine success"
echo

$USCXML_BIN -v ${DATA_MODEL}/test250.scxml


echo
echo
echo "---- test301.scxml: --------"
echo "the processor should reject this document because it can't download the script."
echo "Therefore we fail if it runs at all. This test is valid only for datamodels"
echo "that support scripting"
echo

$USCXML_BIN -v ${DATA_MODEL}/test301.scxml


echo
echo
echo "---- test307.scxml: --------"
echo "with binding=late, in s0 we access a variable that isn't created until we get"
echo "to s1. Then in s1 we access a non-existent substructure of a variable. We use"
echo "log tags to report the values that both operations yield, and whether there are"
echo "errors. This is a manual test, since the tester must report whether the output"
echo "is the same in the two cases"
echo

$USCXML_BIN -v ${DATA_MODEL}/test307.scxml


echo
echo
echo "---- test313.scxml: --------"
echo "this is a manual test. The processor is allowed to reject this doc, but if it"
echo "executes it with its illegal expression, it must raise an error"
echo

$USCXML_BIN -v ${DATA_MODEL}/test313.scxml


echo
echo
echo "---- test314.scxml: --------"
echo "this is a manual test because the processor is allowed to reject this document."
echo "But if it executes it, it should not raise an error until it gets to s03 and"
echo "evaluates the illegal expr"
echo

$USCXML_BIN -v ${DATA_MODEL}/test314.scxml


echo
echo
echo "---- test415.scxml: --------"

echo "Test that the state machine halts when it enters a top-level final state. Since"
echo "the initial state is a final state, this machine should halt immediately"
echo "without processing \"event1\" which is raised in the final state's on-entry"
echo "handler. This is a manual test since there is no platform-independent way to"
echo "test that event1 is not processed"
echo

$USCXML_BIN -v ${DATA_MODEL}/test415.scxml


echo
echo
echo "---- test513.scxml: --------"

echo "This is a fully manual test. You send a well formed event to the 'location' URL"
echo "specified for your SCXML interpreter and check that you get a 200 response code"
echo "back. One way of doing this, using wget, is shown below (you can use any event"
echo "name you want, but you must use '_scxmleventname' to indicate the name of the"
echo "event)"
echo
 
cat << 'END_TEST513' > /tmp/test513.scxml
<scxml name="test513">
	<state id="idle">
		<transition event="quit" target="done" />
	</state>
	<final id="done" />
</scxml>
END_TEST513

${USCXML_BIN} -v -t35001 /tmp/test513.scxml &
sleep 1

wget --post-data='key1=value1&key2=value2' --header '_scxmleventname: quit' localhost:35001/test513/basichttp
rm basichttp*
