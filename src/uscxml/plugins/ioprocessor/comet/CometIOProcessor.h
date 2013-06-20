#ifndef COMETIOPROCESSOR_H_2CUY93KU
#define COMETIOPROCESSOR_H_2CUY93KU

#include "uscxml/concurrency/eventqueue/DelayedEventQueue.h"
#include "uscxml/server/HTTPServer.h"
#include "uscxml/Interpreter.h"
#include "uscxml/Factory.h"

#ifdef BUILD_AS_PLUGINS
#include "uscxml/plugins/Plugins.h"
#endif

namespace uscxml {

class CometIOProcessor : public IOProcessorImpl, public HTTPServlet {
public:
	CometIOProcessor();
	virtual ~CometIOProcessor();
	virtual boost::shared_ptr<IOProcessorImpl> create(uscxml::InterpreterImpl* interpreter);

	virtual std::set<std::string> getNames() {
		std::set<std::string> names;
		names.insert("comet");
		names.insert("http://www.w3.org/TR/scxml/#CometEventProcessor");
		return names;
	}

	/// This method can be overridden for specific replies
	virtual void reply(const SendRequest& req, const HTTPServer::Request& longPoll);

	virtual void send(const SendRequest& req);
	Data getDataModelVariables();

	virtual bool httpRecvRequest(const HTTPServer::Request& request);
	virtual void setURL(const std::string& url) {
		_url = url;
	}

protected:
	tthread::recursive_mutex _mutex;
	std::string _url;
	std::deque<SendRequest> _outQueue;
	HTTPServer::Request _longPollingReq;

};

#ifdef BUILD_AS_PLUGINS
PLUMA_INHERIT_PROVIDER(CometIOProcessor, IOProcessorImpl);
#endif

}

#endif /* end of include guard: COMETIOPROCESSOR_H_2CUY93KU */