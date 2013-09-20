#include "../uscxml/config.h"
#include "uscxml/Message.h"
#include "uscxml/concurrency/tinythread.h"
#include <assert.h>
#include <boost/algorithm/string.hpp>
#include <iostream>
#include "uscxml/plugins/invoker/system/XmlBridgeInvoker.h"

using namespace uscxml;
using namespace boost;

class XmlEventWatcher : public XmlEventsMonitor {
	void handleChanges(DirectoryWatch::Action action, const std::string dir, const std::string file, struct stat fileStat) {
		std::cout << "Monitor on " << dir << ": " << action << " for " << file << std::endl;
	}
};

int main(int argc, char** argv) {

	/* one intepreter for each datablock */
	Interpreter interpreter = Interpreter::fromURI("file:///home/sunkiss/_Projects/uscxml-master/test/samples/uscxml/test-dirmon.scxml");

	/* initialized only once */
	XmlBridgeSMIO* dw = new XmlBridgeSMIO(mybridgeconfig);

	/* one monitor/watcher for each state machine */
	XmlEventWatcher watcher;
	std::cout << "Adding Monitor " << endl;
	dw->addMonitor(&watcher);

	std::cout << "Starting SCXML " << endl;
	interpreter.start(); /* calls XmlBridgeInvoker::invoke */

	while(interpreter.runOnMainThread(25)) {
		dw->updateEntries();
	}

	return EXIT_SUCCESS;
}
