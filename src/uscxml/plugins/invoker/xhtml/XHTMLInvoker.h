#ifndef XHTMLINVOKER_H_W09J90F0
#define XHTMLINVOKER_H_W09J90F0

#include <uscxml/Interpreter.h>

#ifdef BUILD_AS_PLUGINS
#include "uscxml/plugins/Plugins.h"
#endif

namespace uscxml {

class XHTMLInvoker : public InvokerImpl, public HTTPServlet {
public:
	XHTMLInvoker();
	virtual ~XHTMLInvoker();
	virtual boost::shared_ptr<InvokerImpl> create(InterpreterImpl* interpreter);

	virtual std::set<std::string> getNames() {
		std::set<std::string> names;
		names.insert("xhtml");
		names.insert("http://www.w3.org/1999/xhtml");
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
	std::deque<SendRequest> _outQueue;

	tthread::recursive_mutex _mutex;
	InvokeRequest _invokeReq;
	IOProcessor _ioProc;
	std::string _url;
};

#ifdef BUILD_AS_PLUGINS
PLUMA_INHERIT_PROVIDER(XHTMLInvoker, InvokerImpl);
#endif

}


#endif /* end of include guard: XHTMLINVOKER_H_W09J90F0 */
