#include "../uscxml/config.h"
#include "uscxml/Message.h"
#include "uscxml/concurrency/tinythread.h"
#include <assert.h>
#include <boost/algorithm/string.hpp>
#include <iostream>
#include "uscxml/plugins/invoker/system/XmlBridgeInvoker.h"

using namespace uscxml;
using namespace boost;

int main(int argc, char** argv) {

	/* one intepreter for each datablock */
	std::cout << "Initializing interpreter " << endl;
	Interpreter interpreter = Interpreter::fromURI("file:///home/sunkiss/_Projects/uscxml/autoware.scxml");

	if (!interpreter)
		exit(EXIT_FAILURE);

	std::cout << endl << "Starting SCXML " << endl;
	interpreter.start(); /* calls XmlBridgeInvoker::invoke */

	while(interpreter.runOnMainThread(25)) {
		tthread::this_thread::sleep_for(tthread::chrono::milliseconds(20));

		const char *replydata = "<data type=\"temperature\" index=\"17\"><item i=\"0\"><nestedData type=\"setPoint\">30</nestedData></item><item i=\"1\"><nestedData type=\"setPoint\">20</nestedData></item></data>";
		//std::cout << endl << "Immettere il contenuto della risposta ricevuta dal TIM: " << endl;
		//cin.getline(replydata, 200);

		XmlBridgeInputEvents::receiveReplyID(100, replydata);
	}

	return EXIT_SUCCESS;
}
