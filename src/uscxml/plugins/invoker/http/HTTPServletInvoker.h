/**
 *  @file
 *  @author     2012-2013 Stefan Radomski (stefan.radomski@cs.tu-darmstadt.de)
 *  @copyright  Simplified BSD
 *
 *  @cond
 *  This program is free software: you can redistribute it and/or modify
 *  it under the terms of the FreeBSD license as published by the FreeBSD
 *  project.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 *
 *  You should have received a copy of the FreeBSD license along with this
 *  program. If not, see <http://www.opensource.org/licenses/bsd-license>.
 *  @endcond
 */

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

	virtual std::list<std::string> getNames() {
		std::list<std::string> names;
		names.push_back("httpservlet");
		names.push_back("http://uscxml.tk.informatik.tu-darmstadt.de/#httpserver");
		return names;
	}

	virtual Data getDataModelVariables();
	virtual void send(const SendRequest& req);
	virtual void cancel(const std::string sendId);
	virtual void invoke(const InvokeRequest& req);

	// HTTPServlet
	virtual bool httpRecvRequest(const HTTPServer::Request& req);
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
