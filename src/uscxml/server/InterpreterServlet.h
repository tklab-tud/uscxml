#ifndef INTERPRETERSERVLET_H_XQLWNMH4
#define INTERPRETERSERVLET_H_XQLWNMH4

#include "HTTPServer.h"

namespace uscxml {

class Interpreter;
	
class InterpreterServlet : public HTTPServlet {
public:
	InterpreterServlet(Interpreter* interpreter);
	virtual void httpRecvRequest(const HTTPServer::Request& req);

	std::string getPath() {
		return _path;
	}
	std::string getURL() {
		return _url;
	}
	void setURL(const std::string& url) {
		_url = url;
	}
	bool canAdaptPath() { return false; }

	std::map<std::string, HTTPServer::Request>& getRequests() {
		return _requests;
	}
	tthread::recursive_mutex& getMutex() {
		return _mutex;
	}

protected:
	Interpreter* _interpreter;
	
	tthread::recursive_mutex _mutex;
	std::map<std::string, HTTPServer::Request> _requests;
	std::string _path;
	std::string _url;

};
	
}


#endif /* end of include guard: INTERPRETERSERVLET_H_XQLWNMH4 */
