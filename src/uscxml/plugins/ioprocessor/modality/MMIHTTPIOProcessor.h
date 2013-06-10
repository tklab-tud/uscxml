#ifndef MMIHTTPIOPROCESSOR_H_P1FN0YPL
#define MMIHTTPIOPROCESSOR_H_P1FN0YPL

#include "uscxml/plugins/ioprocessor/basichttp/BasicHTTPIOProcessor.h"
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
	
	class MMIHTTPIOProcessor : public BasicHTTPIOProcessor {
	public:
		MMIHTTPIOProcessor();
		virtual ~MMIHTTPIOProcessor();
		virtual boost::shared_ptr<IOProcessorImpl> create(uscxml::InterpreterImpl* interpreter);

		virtual std::set<std::string> getNames() {
			std::set<std::string> names;
			names.insert("mmihttp");
			names.insert("http://www.w3.org/TR/mmi-arch/#HTTPTransport");
			return names;
		}

		virtual void send(const SendRequest& req);

		/// HTTPServlet
		void httpRecvRequest(const HTTPServer::Request& req);

		bool canAdaptPath() {
			return false;
		}

	protected:
		std::string _url;
		std::map<std::string, std::pair<URL, SendRequest> > _sendRequests;
	};

	#ifdef BUILD_AS_PLUGINS
	PLUMA_INHERIT_PROVIDER(MMIHTTPIOProcessor, IOProcessorImpl);
	#endif

}

#endif /* end of include guard: MMIHTTPIOPROCESSOR_H_P1FN0YPL */
