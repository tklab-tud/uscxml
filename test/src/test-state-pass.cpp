#include <xercesc/parsers/XercesDOMParser.hpp>
#include <xercesc/dom/DOM.hpp>
#include <xercesc/dom/DOMLSSerializer.hpp>
#include <xercesc/dom/DOMImplementationLS.hpp>
#include <xercesc/sax/HandlerBase.hpp>
#include <xercesc/util/XMLString.hpp>
#include <xercesc/util/PlatformUtils.hpp>

#include "uscxml/Interpreter.h"
#include "uscxml/interpreter/InterpreterMonitor.h"
#include "uscxml/util/DOM.h"
#include "uscxml/util/String.h"
#include "uscxml/util/UUID.h"
#include "uscxml/util/Predicates.h"
#include "uscxml/util/Convenience.h" // iequals

#include "uscxml/interpreter/Logging.h"

#include "uscxml/messages/Event.h"
#include "uscxml/server/HTTPServer.h"

#include <iostream>
#include <queue>
#include <condition_variable>

#include <event2/util.h>                // for evutil_socket_t
#include <event2/event.h>
#include <event2/thread.h>

#ifdef _WIN32
#include "XGetopt.h"
#include "XGetopt.cpp"
#else
#include <getopt.h>
#endif

using namespace std;
using namespace XERCESC_NS;
using namespace uscxml;


int main(int argc, char** argv) {
	size_t iterations = 1;

	std::string documentURI;
//	el::Loggers::reconfigureAllLoggers(el::ConfigurationType::Format, "%datetime %level %fbase:%line: %msg");

	if (argc < 2) {
		exit(EXIT_FAILURE);
	}

	int option;
	while ((option = getopt(argc, argv, "n:")) != -1) {
		switch(option) {
		case 'n':
			iterations = strTo<size_t>(optarg);
			break;
		default:
			break;
		}
	}

	documentURI = argv[optind];

	HTTPServer::getInstance(7080, 7443);

	while(iterations--) {
		try {
			Interpreter interpreter = Interpreter::fromURL(documentURI);

//			ActionLanguage al;
//			al.execContent = std::shared_ptr<ContentExecutorImpl>(new ContentExecutorBasic(interpreter.getImpl().get()));
//			interpreter.setActionLanguage(al);

			StateTransitionMonitor mon;
			interpreter.addMonitor(&mon);

			InterpreterState state = InterpreterState::USCXML_UNDEF;
			while(state != USCXML_FINISHED) {
				state = interpreter.step();
			}
			assert(interpreter.isInState("pass"));
		} catch (Event e) {
			std::cerr << "Thrown Event out of Interpreter: " << e;
			return EXIT_FAILURE;
		}
	}

	return 0;
}
