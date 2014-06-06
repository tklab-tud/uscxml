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

#ifndef BASICHTTPIOPROCESSOR_H_2CUY93KU
#define BASICHTTPIOPROCESSOR_H_2CUY93KU

extern "C" {
#include <event2/http.h>
#include <event2/http_struct.h>
}

#if defined(_WIN32) && !defined(USCXML_STATIC)
#	if (defined ioprocessor_basichttp_EXPORTS || defined USCXML_EXPORT)
#		define USCXML_PLUGIN_API __declspec(dllexport)
#	else
#		define USCXML_PLUGIN_API __declspec(dllimport)
#	endif
#else
#	define USCXML_PLUGIN_API
#endif

#include "uscxml/concurrency/eventqueue/DelayedEventQueue.h"
#include "uscxml/server/HTTPServer.h"
#include "uscxml/Interpreter.h"
#include "uscxml/Factory.h"
#ifndef _WIN32
#include <sys/time.h>
#endif

#ifdef BUILD_AS_PLUGINS
#include "uscxml/plugins/Plugins.h"
#endif

namespace uscxml {

class USCXML_PLUGIN_API BasicHTTPIOProcessor : public IOProcessorImpl, public HTTPServlet, public URLMonitor {
public:
	BasicHTTPIOProcessor();
	virtual ~BasicHTTPIOProcessor();
	virtual boost::shared_ptr<IOProcessorImpl> create(uscxml::InterpreterImpl* interpreter);

	virtual std::list<std::string> getNames() {
		std::list<std::string> names;
		names.push_back("basichttp");
		names.push_back("http://www.w3.org/TR/scxml/#BasicHTTPEventProcessor");
		return names;
	}

	virtual void send(const SendRequest& req);

	Data getDataModelVariables();

	/// HTTPServlet
	bool httpRecvRequest(const HTTPServer::Request& req);
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

// do not implement pluma plugins if we build an inherited plugin
#ifdef ioprocessor_basichttp_EXPORTS
#	ifdef BUILD_AS_PLUGINS
PLUMA_INHERIT_PROVIDER(BasicHTTPIOProcessor, IOProcessorImpl);
#	endif
#endif

}

#endif /* end of include guard: BASICHTTPIOPROCESSOR_H_2CUY93KU */