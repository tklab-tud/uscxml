#include "uscxml/config.h"
#include "uscxml/Interpreter.h"
#include "uscxml/DOMUtils.h"

#include "uscxml/Factory.h"
#include "uscxml/server/HTTPServer.h"

#include "uscxml/transform/ChartToFlatSCXML.h"
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
static size_t benchmarkRuns = 0;
static std::string documentURI;

int retCode = EXIT_FAILURE;
uscxml::Interpreter interpreter;

void printUsageAndExit(const char* progName) {
    // remove path from program name
    std::string progStr(progName);
    if (progStr.find_last_of(PATH_SEPERATOR) != std::string::npos) {
        progStr = progStr.substr(progStr.find_last_of(PATH_SEPERATOR) + 1, progStr.length() - (progStr.find_last_of(PATH_SEPERATOR) + 1));
    }
    
    printf("%s version " USCXML_VERSION " (" CMAKE_BUILD_TYPE " build - " CMAKE_COMPILER_STRING ")\n", progStr.c_str());
    printf("Usage\n");
    printf("\t%s", progStr.c_str());
    printf(" [-f] [-dN] [-bN]");
#ifdef BUILD_AS_PLUGINS
    printf(" [-p pluginPath]");
#endif
    printf(" URL");
    printf("\n");
    printf("Options\n");
    printf("\t-f             : flatten to SCXML state-machine\n");
    printf("\t-d FACTOR      : delay factor\n");
    printf("\t-b ITERATIONS  : benchmark with number of runs\n");
    printf("\n");
    exit(1);
}

class W3CStatusMonitor : public uscxml::StateTransitionMonitor {

void beforeCompletion(uscxml::Interpreter tmp) {
	if (interpreter.getConfiguration().size() == 1 && interpreter.isInState("pass")) {
		std::cout << "TEST SUCCEEDED" << std::endl;
		retCode = EXIT_SUCCESS;
		return;
	}
	std::cout << "TEST FAILED" << std::endl;
}
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

		google::InitGoogleLogging(argv[0]);
		google::LogToStderr();

		HTTPServer::getInstance(32954, 32955, NULL); // bind to some random tcp sockets for ioprocessor tests

		char* dfEnv = getenv("USCXML_DELAY_FACTOR");
		if (dfEnv) {
			delayFactor = strTo<double>(dfEnv);
		}

		int option;
		while ((option = getopt(argc, argv, "fd:b:")) != -1) {
			switch(option) {
			case 'f':
				withFlattening = true;
				break;
			case 'd':
				delayFactor = strTo<double>(optarg);
				break;
            case 'b':
                benchmarkRuns = strTo<size_t>(optarg);
                break;
			default:
				break;
			}
		}

		documentURI = argv[optind];

        LOG(INFO) << "Processing " << documentURI << (withFlattening ? " FSM converted" : "") << (delayFactor ? "" : " with delays *= " + toStr(delayFactor)) << (benchmarkRuns > 0 ? " for " + toStr(benchmarkRuns) + " benchmarks" : "");
		if (withFlattening) {
			interpreter = Interpreter::fromURL(documentURI);
			Transformer flattener = ChartToFlatSCXML::transform(interpreter);
			interpreter = flattener;
//			std::cout << interpreter.getDocument() << std::endl;
		} else {
			interpreter = Interpreter::fromURL(documentURI);
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
            if (benchmarkRuns > 0) {
                LOG(INFO) << "Benchmarking " << documentURI << (withFlattening ? " FSM converted" : "") << (delayFactor ? "" : " with delays *= " + toStr(delayFactor));

                InterpreterState state = interpreter.getState();
                
                double avg = 0;
                uint64_t now = 0;
                size_t remainingRuns = benchmarkRuns;
                uint64_t start = tthread::chrono::system_clock::now();

                while(remainingRuns-- > 0) {
                    now = tthread::chrono::system_clock::now();
                    for(;;) {
                        state = interpreter.step(true);
                        if (state < 0)
                            break;
                    }
                    avg += (double)(tthread::chrono::system_clock::now() - now) / (double)benchmarkRuns;
                    interpreter.reset();
                }
                uint64_t totalDuration = tthread::chrono::system_clock::now() - start;
                std::cout << benchmarkRuns << " iterations in " << totalDuration << " ms" << std::endl;
                std::cout << avg << " ms on average" << std::endl;
                
            } else {
                W3CStatusMonitor* vm = new W3CStatusMonitor();
                interpreter.addMonitor(vm);

                interpreter.start();
                while(interpreter.runOnMainThread(25));
            }
		}
	} catch(Event e) {
		std::cout << e << std::endl;
	} catch(std::exception e) {
		std::cout << e.what() << std::endl;
	}
	return retCode;
}
