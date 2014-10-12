#include "uscxml/config.h"
#include "uscxml/Interpreter.h"
#include "uscxml/DOMUtils.h"

#include "uscxml/Factory.h"
#include "uscxml/server/HTTPServer.h"

#include "uscxml/transform/ChartToFSM.h"
#include <glog/logging.h>
#include <boost/algorithm/string.hpp>

#ifdef HAS_SIGNAL_H
#include <signal.h>
#endif

#ifdef _WIN32
#include "XGetopt.h"
#include "XGetopt.cpp"
#endif

static bool withFlattening = false;
static double delayFactor = 1;
static std::string documentURI;

int retCode = EXIT_FAILURE;

class W3CStatusMonitor : public uscxml::InterpreterMonitor {

	void beforeTakingTransition(uscxml::Interpreter interpreter, const Arabica::DOM::Element<std::string>& transition, bool moreComing) {
		std::cout << "Transition: " << uscxml::DOMUtils::xPathForNode(transition) << std::endl;
	}

	void onStableConfiguration(uscxml::Interpreter interpreter) {
		std::cout << "Config: {";
		printNodeSet(interpreter.getConfiguration());
		std::cout << "}" << std::endl;
	}

	void beforeProcessingEvent(uscxml::Interpreter interpreter, const uscxml::Event& event) {
		std::cout << "Event: " << event.name << std::endl;
	}

	void beforeExitingState(uscxml::Interpreter interpreter, const Arabica::DOM::Element<std::string>& state, bool moreComing) {
		exitingStates.push_back(state);
		if (!moreComing) {
			std::cout << "Exiting: {";
			printNodeSet(exitingStates);
			std::cout << "}" << std::endl;
			exitingStates = Arabica::XPath::NodeSet<std::string>();
		}
	}

	void beforeEnteringState(uscxml::Interpreter interpreter, const Arabica::DOM::Element<std::string>& state, bool moreComing) {
		enteringStates.push_back(state);
		if (!moreComing) {
			std::cout << "Entering: {";
			printNodeSet(enteringStates);
			std::cout << "}" << std::endl;
			enteringStates = Arabica::XPath::NodeSet<std::string>();
		}

	}

	void printNodeSet(const Arabica::XPath::NodeSet<std::string>& config) {
		std::string seperator;
		for (int i = 0; i < config.size(); i++) {
			std::cout << seperator << ATTR_CAST(config[i], "id");
			seperator = ", ";
		}
	}

	void beforeCompletion(uscxml::Interpreter interpreter) {
		Arabica::XPath::NodeSet<std::string> config = interpreter.getConfiguration();
		if (config.size() == 1) {
			if (withFlattening) {
				std::cout << ATTR_CAST(config[0], "id") << std::endl;
				if (boost::starts_with(ATTR_CAST(config[0], "id"), "active:{pass")) {
					std::cout << "TEST SUCCEEDED" << std::endl;
					retCode = EXIT_SUCCESS;
					return;
				}
			} else {
				if (boost::iequals(ATTR_CAST(config[0], "id"), "pass")) {
					std::cout << "TEST SUCCEEDED" << std::endl;
					retCode = EXIT_SUCCESS;
					return;
				}
			}
		}
		std::cout << "TEST FAILED" << std::endl;
	}

	Arabica::XPath::NodeSet<std::string> exitingStates;
	Arabica::XPath::NodeSet<std::string> enteringStates;
};

int main(int argc, char** argv) {
	using namespace uscxml;

	try {

#if defined(HAS_SIGNAL_H) && !defined(WIN32)
		signal(SIGPIPE, SIG_IGN);
#endif

		if (argc < 2) {
			exit(EXIT_FAILURE);
		}

		HTTPServer::getInstance(32954, 32955, NULL); // bind to some random tcp sockets for ioprocessor tests

		google::InitGoogleLogging(argv[0]);
		google::LogToStderr();

		char* dfEnv = getenv("USCXML_DELAY_FACTOR");
		if (dfEnv) {
			delayFactor = strTo<double>(dfEnv);
		}

		int option;
		while ((option = getopt(argc, argv, "fd:")) != -1) {
			switch(option) {
			case 'f':
				withFlattening = true;
				break;
			case 'd':
				delayFactor = strTo<double>(optarg);
				break;
			default:
				break;
			}
		}

		documentURI = argv[optind];

		Interpreter interpreter;
		LOG(INFO) << "Processing " << documentURI << (withFlattening ? " FSM converted" : "") << (delayFactor ? "" : " with delays *= " + toStr(delayFactor));
		if (withFlattening) {
			Interpreter flatInterpreter = Interpreter::fromURI(documentURI);
			interpreter = Interpreter::fromDOM(ChartToFSM::flatten(flatInterpreter).getDocument(), flatInterpreter.getNameSpaceInfo());
			interpreter.setSourceURI(flatInterpreter.getSourceURI());
		} else {
			interpreter = Interpreter::fromURI(documentURI);
		}

		if (delayFactor != 1) {
			Arabica::DOM::Document<std::string> document = interpreter.getDocument();
			Arabica::DOM::Element<std::string> root = document.getDocumentElement();
			Arabica::XPath::NodeSet<std::string> sends = InterpreterImpl::filterChildElements(interpreter.getNameSpaceInfo().xmlNSPrefix + "send", root, true);

			for (int i = 0; i < sends.size(); i++) {
				Arabica::DOM::Element<std::string> send = Arabica::DOM::Element<std::string>(sends[i]);
				if (HAS_ATTR(send, "delay")) {
					NumAttr delay(ATTR(send, "delay"));
					int value = strTo<int>(delay.value);
					if (delay.unit == "s")
						value *= 1000;
					value *= delayFactor;
					send.setAttribute("delay", toStr(value) + "ms");
					std::cout << ATTR(send, "delay") << std::endl;
				} else if (HAS_ATTR(send, "delayexpr")) {
					std::string delayExpr = ATTR(send, "delayexpr");
					send.setAttribute("delayexpr",
					                  "(" + delayExpr + ".indexOf('ms', " + delayExpr + ".length - 2) !== -1 ? "
					                  "(" + delayExpr + ".slice(0,-2) * " + toStr(delayFactor) + ") + \"ms\" : "
					                  "(" + delayExpr + ".slice(0,-1) * 1000 * " + toStr(delayFactor) + ") + \"ms\")");
					std::cout << ATTR(send, "delayexpr") << std::endl;
				}
			}
			std::list<InterpreterIssue> issues = interpreter.validate();
			for (std::list<InterpreterIssue>::iterator issueIter = issues.begin(); issueIter != issues.end(); issueIter++) {
				std::cout << *issueIter << std::endl;
			}
		}

		if (interpreter) {
			W3CStatusMonitor* vm = new W3CStatusMonitor();
			interpreter.addMonitor(vm);

			interpreter.start();
			while(interpreter.runOnMainThread(25));
		}
	} catch(Event e) {
		std::cout << e << std::endl;
	} catch(std::exception e) {
		std::cout << e.what() << std::endl;
	}
	return retCode;
}