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

#include "uscxml/config.h"
#include "uscxml/Common.h"
#include "uscxml/util/UUID.h"
#include "uscxml/Interpreter.h"
#include "uscxml/interpreter/InterpreterImpl.h" // beware cyclic reference!
#include "uscxml/interpreter/BasicEventQueue.h"
#include "uscxml/interpreter/BasicDelayedEventQueue.h"
#include "uscxml/messages/Event.h"
#include "uscxml/util/String.h"
#include "uscxml/util/Predicates.h"
#include "uscxml/plugins/InvokerImpl.h"

#include "uscxml/interpreter/Logging.h"

#include <iostream>

#include <assert.h>
#include <algorithm>
#include <memory>
#include <mutex>

#include "uscxml/interpreter/FastMicroStep.h"
#include "uscxml/interpreter/BasicContentExecutor.h"

#include <xercesc/dom/DOM.hpp>
#include <xercesc/util/PlatformUtils.hpp>

#define VERBOSE 0

namespace uscxml {

std::map<std::string, std::weak_ptr<InterpreterImpl> > InterpreterImpl::_instances;
std::recursive_mutex InterpreterImpl::_instanceMutex;

std::map<std::string, std::weak_ptr<InterpreterImpl> > InterpreterImpl::getInstances() {
	std::lock_guard<std::recursive_mutex> lock(_instanceMutex);
	std::map<std::string, std::weak_ptr<InterpreterImpl> >::iterator instIter = _instances.begin();
	while(instIter != _instances.end()) {
		if (!instIter->second.lock()) {
			_instances.erase(instIter++);
		} else {
			instIter++;
		}
	}
	return _instances;
}

void InterpreterImpl::addInstance(std::shared_ptr<InterpreterImpl> interpreterImpl) {
	std::lock_guard<std::recursive_mutex> lock(_instanceMutex);
	assert(_instances.find(interpreterImpl->getSessionId()) == _instances.end());
	_instances[interpreterImpl->getSessionId()] = interpreterImpl;
}

InterpreterImpl::InterpreterImpl() : _isInitialized(false), _document(NULL), _scxml(NULL), _state(USCXML_INSTANTIATED) {
	try {
		::xercesc_3_1::XMLPlatformUtils::Initialize();
	} catch (const XERCESC_NS::XMLException& toCatch) {
		ERROR_PLATFORM_THROW("Cannot initialize XercesC: " + X(toCatch.getMessage()).str());
	}

	_sessionId = UUID::getUUID();
	_factory = Factory::getInstance();
}


InterpreterImpl::~InterpreterImpl() {

	// make sure we deallocate all user-data in the DOM,
	// this is neccesary if we were aborted early
	std::list<DOMElement*> invokes = DOMUtils::filterChildElements(_xmlPrefix.str() + "invoke", _scxml, true);
	for (auto invoke : invokes) {
		char* invokeId = (char*)invoke->getUserData(X("invokeid"));
		if (invokeId != NULL) {
			free(invokeId);
			invoke->setUserData(X("invokeid"), NULL, NULL);
		}
	}

	if (_delayQueue)
		_delayQueue.cancelAllDelayed();
	if (_document)
		delete _document;

	{
		std::lock_guard<std::recursive_mutex> lock(_instanceMutex);
		_instances.erase(getSessionId());
	}

//    assert(_invokers.size() == 0);
//    ::xercesc_3_1::XMLPlatformUtils::Terminate();

}

void InterpreterImpl::cancel() {
	_microStepper.markAsCancelled();
	Event unblock;
	enqueueExternal(unblock);
}


void InterpreterImpl::setupDOM() {

	if (!_document) {
		ERROR_PLATFORM_THROW("Interpreter has no XML document");
	}

	if (!_scxml) {
		// find scxml element
		XERCESC_NS::DOMNodeList* scxmls = NULL;

		// proper namespace
		scxmls = _document->getElementsByTagNameNS(X("http://www.w3.org/2005/07/scxml"), X("scxml"));
		if (scxmls->getLength() > 0)
			goto SCXML_STOP_SEARCH;

		// no namespace
		scxmls = _document->getElementsByTagName(X("scxml"));
		if (scxmls->getLength() > 0)
			goto SCXML_STOP_SEARCH;

SCXML_STOP_SEARCH:
		if (scxmls->getLength() == 0) {
			ERROR_PLATFORM_THROW("Cannot find SCXML element in DOM");
			return;
		}

		_scxml = dynamic_cast<XERCESC_NS::DOMElement*>(scxmls->item(0));

		_xmlPrefix = _scxml->getPrefix();
		_xmlNS = _scxml->getNamespaceURI();
		if (_xmlPrefix) {
			_xmlPrefix = std::string(_xmlPrefix) + ":";
		}
		if (HAS_ATTR(_scxml, "name")) {
			_name = ATTR(_scxml, "name");
		} else {
			_name = _baseURL.pathComponents().back();
		}

		_binding = (HAS_ATTR(_scxml, "binding") && iequals(ATTR(_scxml, "binding"), "late") ? LATE : EARLY);

	}

}

void InterpreterImpl::init() {

	if (_isInitialized)
		return;

	setupDOM();

	// register io processors
	std::map<std::string, IOProcessorImpl*> ioProcs = _factory->getIOProcessors();
	for (auto ioProcIter = ioProcs.begin(); ioProcIter != ioProcs.end(); ioProcIter++) {

		// do not override if already set
		if (_ioProcs.find(ioProcIter->first) != _ioProcs.end()) {
			ioProcIter++;
			continue;
		}

		// this might throw error.execution
		_ioProcs[ioProcIter->first] = _factory->createIOProcessor(ioProcIter->first, this);

		// register aliases
		std::list<std::string> names = _ioProcs[ioProcIter->first].getNames();
		for (auto nameIter = names.begin(); nameIter != names.end(); nameIter++) {
			// do not override
			if (!iequals(*nameIter, ioProcIter->first) && _ioProcs.find(*nameIter) == _ioProcs.end()) {
				_ioProcs[*nameIter] = _ioProcs[ioProcIter->first];
			}
		}

	}

	if (!_microStepper) {
		_microStepper = MicroStep(std::shared_ptr<MicroStepImpl>(new FastMicroStep(this)));
	}
	_microStepper.init(_scxml);

	if (!_dataModel) {
		_dataModel = _factory->createDataModel(HAS_ATTR(_scxml, "datamodel") ? ATTR(_scxml, "datamodel") : "null", this);
	}
	if (!_execContent) {
		_execContent = ContentExecutor(std::shared_ptr<ContentExecutorImpl>(new BasicContentExecutor(this)));
	}

	if (!_externalQueue) {
		_externalQueue = EventQueue(std::shared_ptr<EventQueueImpl>(new BasicEventQueue()));
	}
	if (!_internalQueue) {
		_internalQueue = EventQueue(std::shared_ptr<EventQueueImpl>(new BasicEventQueue()));
	}
	if (!_delayQueue) {
		_delayQueue = DelayedEventQueue(std::shared_ptr<DelayedEventQueueImpl>(new BasicDelayedEventQueue(this)));
	}

	_isInitialized = true;
}

void InterpreterImpl::initData(XERCESC_NS::DOMElement* root) {
	std::string id = ATTR(root, "id");
	Data d;
	try {
		if (Event::getParam(_invokeReq.params, id, d)) {
			_dataModel.init(id, d);
		} else if (_invokeReq.namelist.find(id) != _invokeReq.namelist.end()) {
			_dataModel.init(id, _invokeReq.namelist[id]);
		} else {
			_dataModel.init(id, _execContent.elementAsData(root));
		}
	} catch(ErrorEvent e) {
		// test 277
		enqueueInternal(e);
	}
}

void InterpreterImpl::assign(const std::string& location, const Data& data) {
	_dataModel.assign(location, data);
}

bool InterpreterImpl::isMatched(const Event& event, const std::string& eventDesc) {
	return nameMatch(eventDesc, event.name);
}

bool InterpreterImpl::isTrue(const std::string& expr) {
	try {
		return _dataModel.evalAsBool(expr);
	} catch (ErrorEvent e) {
		// test 244: deliver error execution

		LOG(getLogger(), USCXML_ERROR) << e;

		// test 344
		enqueueInternal(e);
		// test 245: undefined is false
		return false;

	}
}


bool InterpreterImpl::checkValidSendType(const std::string& type, const std::string& target) {

	// this is the responsibility of the calling method
	assert(type.size() > 0);

	if (_ioProcs.find(type) == _ioProcs.end()) {
		ERROR_EXECUTION_THROW("Type '" + type + "' not supported for sending");
	}

	if (!_ioProcs[type].isValidTarget(target)) {
		ERROR_COMMUNICATION_THROW("Target '" + target + "' not supported in send");
	}

	return true;
}

Event InterpreterImpl::dequeueExternal(size_t blockMs) {
	_currEvent = _externalQueue.dequeue(blockMs);
	if (_currEvent) {
		_dataModel.setEvent(_currEvent);

//		LOG(USCXML_ERROR) << e.name;

		// test 233
		if (_currEvent.invokeid.size() > 0 &&
		        _invokers.find(_currEvent.invokeid) != _invokers.end() &&
		        _invokers[_currEvent.invokeid].getFinalize() != NULL) {
			_execContent.process(_invokers[_currEvent.invokeid].getFinalize(), _xmlPrefix);
		}

		for (auto invIter = _invokers.begin(); invIter != _invokers.end(); invIter++) {
			// test 229
			if (_autoForwarders.find(invIter->first) != _autoForwarders.end()) {
				invIter->second.eventFromSCXML(_currEvent);
			}
		}
	}
	return _currEvent;
}

void InterpreterImpl::enqueue(const std::string& type, const std::string& target, size_t delayMs, const Event& sendEvent) {
	std::lock_guard<std::recursive_mutex> lock(_delayMutex);

	assert(sendEvent.uuid.length() > 0);
	assert(_delayedEventTargets.find(sendEvent.uuid) == _delayedEventTargets.end());

	_delayedEventTargets[sendEvent.uuid] = std::tuple<std::string, std::string, std::string>(sendEvent.sendid, type, target);
	if (delayMs == 0) {
		Event copy(sendEvent);
		return eventReady(copy, sendEvent.uuid);
	} else {
		return _delayQueue.enqueueDelayed(sendEvent, delayMs, sendEvent.uuid);
	}
}

void InterpreterImpl::cancelDelayed(const std::string& sendId) {
	std::lock_guard<std::recursive_mutex> lock(_delayMutex);

	// we need to find the uuids for the given sendid
	for (auto evIter = _delayedEventTargets.begin(); evIter != _delayedEventTargets.end();) {
		// inline deletion for maps: http://stackoverflow.com/a/263958/990120
		if (std::get<0>(evIter->second) == sendId) {
			_delayQueue.cancelDelayed(evIter->first);
			evIter = _delayedEventTargets.erase(evIter);
		} else {
			evIter++;
		}
	}
}

void InterpreterImpl::eventReady(Event& sendEvent, const std::string& eventUUID) {
	std::lock_guard<std::recursive_mutex> lock(_delayMutex);

	// we only arrive here after the delay already passed!
	assert(_delayedEventTargets.find(eventUUID) != _delayedEventTargets.end());

	std::string type = std::get<1>(_delayedEventTargets[eventUUID]);
	std::string target = std::get<2>(_delayedEventTargets[eventUUID]);

	// test 172
	if (type.size() == 0) {
		type = "http://www.w3.org/TR/scxml/#SCXMLEventProcessor";
	}

	_delayedEventTargets.erase(eventUUID);

	if (_ioProcs.find(type) != _ioProcs.end()) {
		_ioProcs[type].eventFromSCXML(target, sendEvent);
	} else {
		ERROR_PLATFORM_THROW("No IO processor " + type + " known");
	}
}

void InterpreterImpl::invoke(const std::string& type, const std::string& src, bool autoForward, XERCESC_NS::DOMElement* finalize, const Event& invokeEvent) {

	std::string tmp;
	if (src.size() > 0) {
		URL url(src);
		if (!url.isAbsolute()) {
			url = URL::resolve(url, _baseURL);
		}
		tmp = (std::string)url;
	}

	std::shared_ptr<InvokerImpl> invokerImpl = _factory->createInvoker(type, this);
	invokerImpl->setFinalize(finalize);
	_invokers[invokeEvent.invokeid] = invokerImpl;
	_invokers[invokeEvent.invokeid].invoke(tmp, invokeEvent);

	if (autoForward) {
		_autoForwarders.insert(invokeEvent.invokeid);
	}
}

void InterpreterImpl::uninvoke(const std::string& invokeId) {
	if (_invokers.find(invokeId) != _invokers.end()) {
		_invokers[invokeId].uninvoke();
		_autoForwarders.erase(invokeId);
		_invokers.erase(invokeId);
	}

}

}
