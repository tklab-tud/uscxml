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

#include "uscxml/config.h"

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

#include "uscxml/server/HTTPServer.h"
#include "uscxml/interpreter/InterpreterImpl.h"
#include "uscxml/plugins/IOProcessorImpl.h"

#ifndef _WIN32
#include <sys/time.h>
#endif

#ifdef BUILD_AS_PLUGINS
#include "uscxml/plugins/Plugins.h"
#endif

#define USCXML_IOPROC_BASICHTTP_TYPE "http://www.w3.org/TR/scxml/#BasicHTTPEventProcessor"

namespace uscxml {

/**
 * @ingroup ioproc
 * The basichttp I/O processor as per standard.
 */
class USCXML_PLUGIN_API BasicHTTPIOProcessor : public IOProcessorImpl, public HTTPServlet, public URLMonitor {
public:
	BasicHTTPIOProcessor();
	virtual ~BasicHTTPIOProcessor();
	virtual std::shared_ptr<IOProcessorImpl> create(uscxml::IOProcessorCallbacks* callbacks);

	virtual std::list<std::string> getNames() {
		std::list<std::string> names;
		names.push_back("basichttp");
		names.push_back(USCXML_IOPROC_BASICHTTP_TYPE);
		return names;
	}

	virtual void eventFromSCXML(const std::string& target, const Event& event);
	virtual bool isValidTarget(const std::string& target);

	Data getDataModelVariables();

	/// HTTPServlet
	bool requestFromHTTP(const HTTPServer::Request& req);
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
	std::map<std::string, std::pair<URL, Event> > _sendRequests;
};

#ifdef BUILD_AS_PLUGINS
PLUMA_INHERIT_PROVIDER(BasicHTTPIOProcessor, IOProcessorImpl)
#endif

}

#endif /* end of include guard: BASICHTTPIOPROCESSOR_H_2CUY93KU */
