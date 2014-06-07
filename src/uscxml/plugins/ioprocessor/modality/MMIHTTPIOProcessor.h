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

	virtual std::list<std::string> getNames() {
		std::list<std::string> names;
		names.insert("mmihttp");
		names.insert("http://www.w3.org/TR/mmi-arch/#HTTPTransport");
		return names;
	}

	virtual void send(const SendRequest& req);

	/// HTTPServlet
	bool httpRecvRequest(const HTTPServer::Request& req);

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
