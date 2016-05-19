#include "uscxml/config.h"
#include "uscxml/Interpreter.h"
#include "uscxml/debug/InterpreterIssue.h"
#include "uscxml/interpreter/InterpreterMonitor.h"
#include "uscxml/util/DOM.h"

#include <easylogging++.h>

#include "uscxml/plugins/Factory.h"
#include "uscxml/server/HTTPServer.h"


int main(int argc, char** argv) {
	using namespace uscxml;

#if defined(HAS_SIGNAL_H) && !defined(WIN32)
	signal(SIGPIPE, SIG_IGN);
#endif

	InterpreterOptions options = InterpreterOptions::fromCmdLine(argc, argv);

	if (options.pluginPath.length() > 0) {
		Factory::setDefaultPluginPath(options.pluginPath);
	}

	if (options.verbose) {
		Factory::getInstance()->listComponents();
	}
	if (!options) {
		InterpreterOptions::printUsageAndExit(argv[0]);
	}

	// setup HTTP server
	HTTPServer::SSLConfig* sslConf = NULL;
	if (options.certificate.length() > 0) {
		sslConf = new HTTPServer::SSLConfig();
		sslConf->privateKey = options.certificate;
		sslConf->publicKey = options.certificate;
		sslConf->port = options.httpsPort;

	} else if (options.privateKey.length() > 0 && options.publicKey.length() > 0) {
		sslConf = new HTTPServer::SSLConfig();
		sslConf->privateKey = options.privateKey;
		sslConf->publicKey = options.publicKey;
		sslConf->port = options.httpsPort;

	}
	HTTPServer::getInstance(options.httpPort, options.wsPort, sslConf);

	// instantiate and configure interpreters
	std::list<Interpreter> interpreters;
	for(int i = 0; i < options.interpreters.size(); i++) {

		InterpreterOptions* currOptions = options.interpreters[0].second;
		std::string documentURL = options.interpreters[0].first;

		LOG(INFO) << "Processing " << documentURL;

		try {
			Interpreter interpreter = Interpreter::fromURL(documentURL);
			if (interpreter) {

				if (options.validate) {
					std::list<InterpreterIssue> issues = interpreter.validate();
					for (std::list<InterpreterIssue>::iterator issueIter = issues.begin(); issueIter != issues.end(); issueIter++) {
						std::cout << *issueIter << std::endl;
					}
					if (issues.size() == 0) {
						std::cout << "No issues found" << std::endl;
					}

				}

				if (options.verbose) {
					StateTransitionMonitor* vm = new StateTransitionMonitor();
					vm->copyToInvokers(true);
					interpreter.setMonitor(vm);
				}

				interpreters.push_back(interpreter);

			} else {
				LOG(ERROR) << "Cannot create interpreter from " << documentURL;
			}
		} catch (Event e) {
			std::cout << e << std::endl;
		}
	}

	// run interpreters
	try {
		std::list<Interpreter>::iterator interpreterIter = interpreters.begin();
        while (interpreters.size() > 0) {
            while(interpreterIter != interpreters.end()) {
                InterpreterState state = interpreterIter->step();
                if (state == USCXML_FINISHED) {
                    interpreterIter = interpreters.erase(interpreterIter);
                } else {
                    interpreterIter++;
                }
            }
            interpreterIter = interpreters.begin();
        }
	} catch (Event e) {
		std::cout << e << std::endl;
	}
	return EXIT_SUCCESS;
}