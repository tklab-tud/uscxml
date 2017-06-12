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

#include "uscxml/Common.h"

#include "uscxml/plugins/ioprocessor/basichttp/BasicHTTPIOProcessor.h"
#include "uscxml/messages/Event.h"
#include "uscxml/util/DOM.h"

#include <string.h>

#include "uscxml/interpreter/Logging.h"
#include <boost/algorithm/string.hpp>

#ifdef _WIN32
#define NOMINMAX
#include <winsock2.h>
#include <windows.h>
#endif

#ifndef _WIN32
#include <netdb.h>
#include <arpa/inet.h>
#endif

#ifdef BUILD_AS_PLUGINS
#include <Pluma/Connector.hpp>
#endif

namespace uscxml {

#ifndef ioprocessor_scxml_EXPORTS
#	ifdef BUILD_AS_PLUGINS
PLUMA_CONNECTOR
bool pluginConnect(pluma::Host& host) {
	host.add( new BasicHTTPIOProcessorProvider() );
	return true;
}
#	endif
#endif

// see http://www.w3.org/TR/scxml/#BasicHTTPEventProcessor

BasicHTTPIOProcessor::BasicHTTPIOProcessor() {
}

BasicHTTPIOProcessor::~BasicHTTPIOProcessor() {
}


std::shared_ptr<IOProcessorImpl> BasicHTTPIOProcessor::create(IOProcessorCallbacks* callbacks) {
	std::shared_ptr<BasicHTTPIOProcessor> io(new BasicHTTPIOProcessor());
	io->_callbacks = callbacks;

	// register at http server
	std::string path = callbacks->getName();
	int i = 2;
	while (!HTTPServer::registerServlet(path + "/basichttp", io.get())) {
		std::stringstream ss;
		ss << callbacks->getName() << i++;
		path = ss.str();
	}

	return io;
}

bool BasicHTTPIOProcessor::requestFromHTTP(const HTTPServer::Request& req) {
	HTTPIOProcessor::requestFromHTTP(req);
	evhttp_send_reply(req.evhttpReq, 200, "OK", NULL);
	getUnansweredRequests().erase(req.getUUID());
	return true;
}


}
