#ifndef MMIEVENTSERVLET_H_92WSR1SU
#define MMIEVENTSERVLET_H_92WSR1SU


#include "uscxml/concurrency/eventqueue/DelayedEventQueue.h"
#include "uscxml/server/HTTPServer.h"
#include "uscxml/Interpreter.h"
#include "uscxml/Factory.h"
#ifndef _WIN32
#include <sys/time.h>
#endif

#include <event2/http.h>
#include <event2/http_struct.h>

#include <uscxml/plugins/ioprocessor/modality/MMIMessages.h>

namespace uscxml {

	class MMIEventServlet : public HTTPServlet, public URLMonitor, public MMIEventSender {
	public:
		MMIEventServlet(const std::string& path);
		virtual ~MMIEventServlet();
		
		void addMonitor(MMIEventReceiver* mmiMonitor) {
			_monitors.insert(mmiMonitor);
		}
		void removeMonitor(MMIEventReceiver* mmiMonitor) {
			_monitors.erase(mmiMonitor);
		}
		
		/// HTTPServlet
		bool httpRecvRequest(const HTTPServer::Request& req);
		void setURL(const std::string& url) {
			_url = url;
		}
		std::string getURL() { return _url; }
		
		bool canAdaptPath() {
			return false;
		}
		
		// URLMonitor
		void downloadStarted(const URL& url);
		void downloadCompleted(const URL& url);
		void downloadFailed(const URL& url, int errorCode);
		
		// MMIEventSender
		virtual void send(const MMIEvent& mmiEvent);

	protected:
		std::string _url;
		std::string _path;
		std::map<std::string, std::pair<URL, SendRequest> > _sendRequests;
		std::set<MMIEventReceiver*> _monitors;
	};
}

#endif /* end of include guard: MMIEVENTSERVLET_H_92WSR1SU */
