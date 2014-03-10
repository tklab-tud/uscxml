#include "uscxml/config.h"
#include "uscxml/Interpreter.h"
#include "uscxml/DOMUtils.h"
#include "uscxml/UUID.h"
#include "uscxml/debug/SCXMLDotWriter.h"
#include "uscxml/debug/Breakpoint.h"
#include "uscxml/debug/Debugger.h"
#include "uscxml/debug/DebuggerServlet.h"
#include <glog/logging.h>
#include <time.h> // mktime

#include <boost/algorithm/string.hpp>
#include <map>

#ifdef HAS_SIGNAL_H
#include <signal.h>
#endif

#ifdef HAS_EXECINFO_H
#include <execinfo.h>
#endif

#ifdef HAS_DLFCN_H
#include <dlfcn.h>
#endif

using namespace uscxml;

//class Debugger : public HTTPServlet {
//public:
//	
//	std::string _url;
//	Interpreter _interpreter;
//	
//	HTTPServer::Request _clientConn; // a request the client renews everytime
//	concurrency::BlockingQueue<Data> _sendQueue; // queue of things we have to return to the client
//	
//	tthread::recursive_mutex _mutex;
//	tthread::condition_variable _resumeCond;
//	
//	std::set<Breakpoint> _breakPoints;
//	std::string _sessionId;
//	
//	DebuggerMonitor _monitor;
//	
//	virtual ~Debugger() {
//	}
//	
//	// callbacks from http requests
//	
//		
//	// helpers
//	
//	
//	
//		
//};


int main(int argc, char** argv) {
	using namespace uscxml;

	InterpreterOptions options = InterpreterOptions::fromCmdLine(argc, argv);
	DebuggerServlet debuggerServlet;
	
	// setup logging
	google::InitGoogleLogging(argv[0]);
	google::AddLogSink(&debuggerServlet);

	// setup HTTP server
	HTTPServer::getInstance(18088, 18089, NULL);


	HTTPServer::getInstance()->registerServlet("/", &debuggerServlet);

	while(true)
		tthread::this_thread::sleep_for(tthread::chrono::seconds(1));
	
	
	return EXIT_SUCCESS;
}