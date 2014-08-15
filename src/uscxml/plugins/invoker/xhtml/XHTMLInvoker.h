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

#ifndef XHTMLINVOKER_H_W09J90F0
#define XHTMLINVOKER_H_W09J90F0

#include <uscxml/Interpreter.h>
#include "uscxml/server/HTTPServer.h"

#ifdef BUILD_AS_PLUGINS
#include "uscxml/plugins/Plugins.h"
#endif

namespace uscxml {

class XHTMLInvoker : public InvokerImpl, public HTTPServlet {
public:
	XHTMLInvoker();
	virtual ~XHTMLInvoker();
	virtual boost::shared_ptr<InvokerImpl> create(InterpreterImpl* interpreter);

	virtual std::list<std::string> getNames() {
		std::list<std::string> names;
		names.push_back("xhtml");
		names.push_back("http://www.w3.org/1999/xhtml");
		return names;
	}

	virtual Data getDataModelVariables();
	virtual void send(const SendRequest& req);
	virtual void cancel(const std::string sendId);
	virtual void invoke(const InvokeRequest& req);

	// HTTPServlet
	virtual bool httpRecvRequest(const HTTPServer::Request& request);
	virtual void setURL(const std::string& url) {
		_url = url;
	}

	void reply(const SendRequest& req, const HTTPServer::Request& longPoll);

protected:
	HTTPServer::Request _longPoll;
	std::deque<HTTPServer::Reply> _outQueue;

	tthread::recursive_mutex _mutex;
	InvokeRequest _invokeReq;

	std::string _url;
};

#ifdef BUILD_AS_PLUGINS
PLUMA_INHERIT_PROVIDER(XHTMLInvoker, InvokerImpl);
#endif

}


#endif /* end of include guard: XHTMLINVOKER_H_W09J90F0 */
