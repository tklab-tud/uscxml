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
	Interpreter interpreter = Interpreter::fromURI("file:///home/sunkiss/_Projects/xmlBridgeCPP/autoware.scxml");

	if (!interpreter)
		exit(EXIT_FAILURE);

	/* initialized only once */
	//std::cout << "Initializing IO monitor" << endl;
	//XmlBridgeInputEvents dw();

	/* one monitor/watcher for each state machine */
	//XmlEventWatcher watcher;

	//dw->addMonitor(&watcher);

	std::cout << "Starting SCXML " << endl;
	interpreter.start(); /* calls XmlBridgeInvoker::invoke */

	while(interpreter.runOnMainThread(25)) {
		tthread::this_thread::sleep_for(tthread::chrono::milliseconds(20));

		char replydata[200];
		std::cout << "Immettere il contenuto della risposta ricevuta dal SIM: " << endl;
		cin.getline(replydata, 200);

		XmlBridgeInputEvents::receiveReplyID(100, replydata);
	}

	return EXIT_SUCCESS;
}
