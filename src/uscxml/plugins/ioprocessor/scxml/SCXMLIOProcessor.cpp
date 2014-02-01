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

#include <boost/algorithm/string.hpp>

#ifdef _WIN32
#include <winsock2.h>
#include <windows.h>
#endif

#include "uscxml/plugins/ioprocessor/scxml/SCXMLIOProcessor.h"
#include "uscxml/Message.h"
#include <iostream>
#include <event2/dns.h>
#include <event2/buffer.h>
#include <event2/keyvalq_struct.h>

#include <string.h>

#include <io/uri.hpp>
#include <glog/logging.h>

#ifndef _WIN32
#include <netdb.h>
#include <arpa/inet.h>
#endif

#ifdef BUILD_AS_PLUGINS
#include <Pluma/Connector.hpp>
#endif

namespace uscxml {

#ifdef BUILD_AS_PLUGINS
PLUMA_CONNECTOR
bool pluginConnect(pluma::Host& host) {
	host.add( new SCXMLIOProcessorProvider() );
	return true;
}
#endif

// see http://www.w3.org/TR/scxml/#SCXMLEventProcessor

SCXMLIOProcessor::SCXMLIOProcessor() {
}

SCXMLIOProcessor::~SCXMLIOProcessor() {
}


boost::shared_ptr<IOProcessorImpl> SCXMLIOProcessor::create(InterpreterImpl* interpreter) {
	boost::shared_ptr<SCXMLIOProcessor> io = boost::shared_ptr<SCXMLIOProcessor>(new SCXMLIOProcessor());
	io->_interpreter = interpreter;

	// register at http server
	std::string path = interpreter->getName();
	int i = 2;
	while (!HTTPServer::registerServlet(path + "/scxml", io.get())) {
		std::stringstream ss;
		ss << interpreter->getName() << i++;
		path = ss.str();
	}
	return io;
}

Data SCXMLIOProcessor::getDataModelVariables() {
	Data data;
	if(_url.length() > 0)
    data.compound["location"] = Data(_url, Data::VERBATIM);
	return data;
}


void SCXMLIOProcessor::send(const SendRequest& req) {
	// see http://www.w3.org/TR/scxml/#SendTargets

	SendRequest reqCopy(req);
	// test 253
	reqCopy.origintype = "http://www.w3.org/TR/scxml/#SCXMLEventProcessor";
	reqCopy.origin = _url;

	if (false) {
	} else if(reqCopy.target.length() == 0) {
		/**
		 * If neither the 'target' nor the 'targetexpr' attribute is specified, the
		 * SCXML Processor must add the event will be added to the external event
		 * queue of the sending session.
		 */

		// test333 vs test351
//		reqCopy.sendid = "";
		// test 198
		_interpreter->receive(reqCopy);
	} else if (iequals(reqCopy.target, "#_internal")) {
		/**
		 * #_internal: If the target is the special term '#_internal', the Processor
		 * must add the event to the internal event queue of the sending session.
		 */
		_interpreter->receiveInternal(reqCopy);

	} else if(boost::starts_with(reqCopy.target, "#_scxml_")) {
		/**
		 * #_scxml_sessionid: If the target is the special term '#_scxml_sessionid',
		 * where sessionid is the id of an SCXML session that is accessible to the
		 * Processor, the Processor must add the event to the external queue of that
		 * session. The set of SCXML sessions that are accessible to a given SCXML
		 * Processor is platform-dependent.
		 */
		std::string sessionId = reqCopy.target.substr(8, reqCopy.target.length() - 8);
		std::map<std::string, boost::weak_ptr<InterpreterImpl> > instances = Interpreter::getInstances();
		if (instances.find(sessionId) != instances.end()) {
			boost::shared_ptr<InterpreterImpl> other = instances[sessionId].lock();
			other->receive(reqCopy);
		} else {
			LOG(ERROR) << "Can not send to scxml session " << sessionId << " - not known" << std::endl;
			Event error("error.communication", Event::PLATFORM);
			error.sendid = reqCopy.sendid;
			_interpreter->receiveInternal(error);
		}
	} else if (iequals(reqCopy.target, "#_parent")) {
		/**
		 * #_parent: If the target is the special term '#_parent', the Processor must
		 * add the event to the external event queue of the SCXML session that invoked
		 * the sending session, if there is one.
		 */
		if (_interpreter->_parentQueue != NULL) {
			_interpreter->_parentQueue->push(reqCopy);
		} else {
			LOG(ERROR) << "Can not send to parent, we were not invoked" << std::endl;
			Event error("error.communication", Event::PLATFORM);
			error.sendid = reqCopy.sendid;
			_interpreter->receiveInternal(error);
		}
	} else if (boost::starts_with(reqCopy.target, "#_")) {
		/**
		 * #_invokeid: If the target is the special term '#_invokeid', where invokeid
		 * is the invokeid of an SCXML session that the sending session has created
		 * by <invoke>, the Processor must add the event to the external queue of that
		 * session.
		 */
		std::string invokeId = reqCopy.target.substr(2, reqCopy.target.length() - 2);
		if (_interpreter->_invokers.find(invokeId) != _interpreter->_invokers.end()) {
			tthread::lock_guard<tthread::recursive_mutex> lock(_interpreter->_mutex);
			try {
				_interpreter->_invokers[invokeId].send(reqCopy);
			} catch(Event e) {
				// Is this the right thing to do?
				_interpreter->receive(e);
			} catch(...) {
				LOG(ERROR) << "Exception caught while sending event to invoker " << invokeId;
			}
		} else {
			LOG(ERROR) << "Can not send to invoked component '" << invokeId << "', no such invokeId" << std::endl;
			Event error("error.communication", Event::PLATFORM);
			error.sendid = reqCopy.sendid;
			_interpreter->receiveInternal(error);
		}
	} else {
		URL target(reqCopy.target);
		if (target.isAbsolute()) {
			BasicHTTPIOProcessor::send(reqCopy);
		} else {
			LOG(ERROR) << "Not sure what to make of the target '" << reqCopy.target << "' - raising error" << std::endl;
			Event error("error.execution", Event::PLATFORM);
			error.sendid = reqCopy.sendid;
			// test 159 still fails
//			_interpreter->receiveInternal(error);
			throw error;
		}
	}
}



}