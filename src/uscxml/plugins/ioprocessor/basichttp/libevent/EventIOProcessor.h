#ifndef EVENTIOPROCESSOR_H_2CUY93KU
#define EVENTIOPROCESSOR_H_2CUY93KU

#include "uscxml/concurrency/eventqueue/DelayedEventQueue.h"
#include "uscxml/server/HTTPServer.h"
#include "uscxml/Interpreter.h"
#include "uscxml/Factory.h"
#ifndef _WIN32
#include <sys/time.h>
#endif

#include <event2/http.h>
#include <event2/http_struct.h>

#ifdef BUILD_AS_PLUGINS
#include "uscxml/plugins/Plugins.h"
#endif

namespace uscxml {

class EventIOServer;

class EventIOProcessor : public IOProcessorImpl, public HTTPServlet, public URLMonitor {
public:
	EventIOProcessor();
	virtual ~EventIOProcessor();
	virtual boost::shared_ptr<IOProcessorImpl> create(uscxml::Interpreter* interpreter);

	virtual std::set<std::string> getNames() {
		std::set<std::string> names;
		names.insert("basichttp");
		names.insert("http://www.w3.org/TR/scxml/#BasicHTTPEventProcessor");
		return names;
	}

	virtual void send(const SendRequest& req);

	Data getDataModelVariables();

	/// HTTPServlet
	void httpRecvRequest(const HTTPServer::Request& req);
	void setURL(const std::string& url) {
		_url = url;
	}

	bool canAdaptPath() {
		return false;
	}

	// URLMonitor
	void downloadStarted(const URL& url);
	void downloadCompleted(const URL& url);
	void downloadFailed(const URL& url, int errorCode);

protected:
	std::string _url;
	std::map<std::string, std::pair<URL, SendRequest> > _sendRequests;
};

#ifdef BUILD_AS_PLUGINS
PLUMA_INHERIT_PROVIDER(EventIOProcessor, IOProcessorImpl);
#endif

}

#endif /* end of include guard: EVENTIOPROCESSOR_H_2CUY93KU */