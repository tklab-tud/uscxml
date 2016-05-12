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


#include "SCXMLIOProcessor.h"
#include "uscxml/messages/Event.h"
#include "uscxml/interpreter/InterpreterImpl.h"

#include <string.h>


#ifndef _WIN32
#include <netdb.h>
#include <arpa/inet.h>
#endif

namespace uscxml {

// see http://www.w3.org/TR/scxml/#SCXMLEventProcessor

SCXMLIOProcessor::SCXMLIOProcessor() {
}

SCXMLIOProcessor::~SCXMLIOProcessor() {
}


std::shared_ptr<IOProcessorImpl> SCXMLIOProcessor::create(InterpreterImpl* interpreter) {
	std::shared_ptr<SCXMLIOProcessor> io(new SCXMLIOProcessor());
	io->_interpreter = interpreter;
	return io;
}

Data SCXMLIOProcessor::getDataModelVariables() {
	Data data;

	data.compound["location"] = Data("#_scxml_" + _interpreter->getSessionId(), Data::VERBATIM);

	return data;
}

bool SCXMLIOProcessor::isValidTarget(const std::string& target) {
	if (target.size() > 0 && (target[0] != '#' || target[1] != '_')) {
		ERROR_EXECUTION_THROW("Target '" + target + "' not supported in send");
	}
	return true;
}


void SCXMLIOProcessor::eventFromSCXML(const std::string& target, const Event& event) {
	// see http://www.w3.org/TR/scxml/#SendTargets
	Event eventCopy(event);

	// test 253 / 198 / 336
	eventCopy.origintype = "http://www.w3.org/TR/scxml/#SCXMLEventProcessor";

	// test 336
	eventCopy.origin = "#_scxml_" + _interpreter->getSessionId();

	if (false) {
	} else if(target.length() == 0) {
		/**
		 * If neither the 'target' nor the 'targetexpr' attribute is specified, the
		 * SCXML Processor must add the event will be added to the external event
		 * queue of the sending session.
		 */

		// test333 vs test351
//		reqCopy.sendid = "";

		// test 198
		_interpreter->enqueueExternal(eventCopy);

	} else if (iequals(target, "#_internal")) {
		/**
		 * #_internal: If the target is the special term '#_internal', the Processor
		 * must add the event to the internal event queue of the sending session.
		 */
		_interpreter->enqueueInternal(eventCopy);

	} else if (iequals(target, "#_parent")) {
		/**
		 * #_parent: If the target is the special term '#_parent', the Processor must
		 * add the event to the external event queue of the SCXML session that invoked
		 * the sending session, if there is one.
		 */

		if (_interpreter->_parentQueue) {
			_interpreter->_parentQueue.enqueue(eventCopy);
		} else {
			ERROR_COMMUNICATION_THROW("Sending to parent invoker, but none is set");
		}

	} else if (target.length() > 8 && iequals(target.substr(0, 8), "#_scxml_")) {
		/**
		 * #_scxml_sessionid: If the target is the special term '#_scxml_sessionid',
		 * where sessionid is the id of an SCXML session that is accessible to the
		 * Processor, the Processor must add the event to the external queue of that
		 * session. The set of SCXML sessions that are accessible to a given SCXML
		 * Processor is platform-dependent.
		 */
		std::string sessionId = target.substr(8);

		std::lock_guard<std::recursive_mutex> lock(_interpreter->_instanceMutex);
		std::map<std::string, std::weak_ptr<InterpreterImpl> > instances = InterpreterImpl::getInstances();
		if (instances.find(sessionId) != instances.end()) {
			std::shared_ptr<InterpreterImpl> otherSession = instances[sessionId].lock();
			if (otherSession) {
				otherSession->enqueueExternal(eventCopy);
			} else {
				ERROR_COMMUNICATION_THROW("Can not send to scxml session " + sessionId + " - not known");
			}
		} else {
			ERROR_COMMUNICATION_THROW("Invalid target scxml session for send");
		}

	} else if (target.length() > 2 && iequals(target.substr(0, 2), "#_")) {
		/**
		 * #_invokeid: If the target is the special term '#_invokeid', where invokeid
		 * is the invokeid of an SCXML session that the sending session has created
		 * by <invoke>, the Processor must add the event to the external queue of that
		 * session.
		 */
		std::string invokeId = target.substr(2);
		if (_interpreter->_invokers.find(invokeId) != _interpreter->_invokers.end()) {
			std::lock_guard<std::recursive_mutex> lock(_interpreter->_instanceMutex);
			try {
				_interpreter->_invokers[invokeId].eventFromSCXML(eventCopy);
			} catch(Event e) {
				// Is this the right thing to do?
//				_interpreter->enqueueExternal(eventCopy);
			} catch (const std::exception &e) {
				ERROR_COMMUNICATION_THROW("Exception caught while sending event to invoker '" + invokeId + "': " + e.what());
			} catch(...) {
				ERROR_COMMUNICATION_THROW("Exception caught while sending event to invoker '" + invokeId + "'");
			}
		} else {
			ERROR_COMMUNICATION_THROW("Can not send to invoked component '" + invokeId + "', no such invokeId");
		}
	} else {
		ERROR_COMMUNICATION_THROW("Not sure what to make of the target '" + target + "' - raising error");
	}
}



}