#ifndef HTTPSERVERINVOKER_H_OAAWX8NF
#define HTTPSERVERINVOKER_H_OAAWX8NF

#include <uscxml/Interpreter.h>
#include <uscxml/server/HTTPServer.h>

#ifdef BUILD_AS_PLUGINS
#include "uscxml/plugins/Plugins.h"
#endif

namespace uscxml {

class HTTPServletInvoker : public InvokerImpl, public HTTPServlet {
public:
	HTTPServletInvoker();
	virtual ~HTTPServletInvoker();
	virtual boost::shared_ptr<InvokerImpl> create(InterpreterImpl* interpreter);

	virtual std::set<std::string> getNames() {
		std::set<std::string> names;
		names.insert("httpservlet");
		names.insert("http://uscxml.tk.informatik.tu-darmstadt.de/#httpserver");
		return names;
	}

	virtual Data getDataModelVariables();
	virtual void send(const SendRequest& req);
	virtual void cancel(const std::string sendId);
	virtual void invoke(const InvokeRequest& req);

	// HTTPServlet
	virtual void httpRecvRequest(const HTTPServer::Request& req);
	virtual std::string getPath();
	virtual void setURL(const std::string& url) {
		_url = url;
	}
	bool canAdaptPath() {
		return false;
	}

protected:
	tthread::recursive_mutex _mutex;
	std::map<std::string, HTTPServer::Request> _requests;
	std::string _path;
	std::string _callback;
	std::string _url;
};

#ifdef BUILD_AS_PLUGINS
PLUMA_INHERIT_PROVIDER(HTTPServletInvoker, InvokerImpl);
#endif

}

#endif /* end of include guard: HTTPSERVERINVOKER_H_OAAWX8NF */
