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
#include "uscxml/util/MD5.hpp"
#include "uscxml/plugins/InvokerImpl.h"

#include "uscxml/interpreter/Logging.h"

#include <fstream>

#include <assert.h>
#include <algorithm>
#include <memory>
#include <mutex>
#include <cstdio> // remove

#include "uscxml/interpreter/FastMicroStep.h"
#include "uscxml/interpreter/LargeMicroStep.h"
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
		::XERCESC_NS::XMLPlatformUtils::Initialize();
	} catch (const XERCESC_NS::XMLException& toCatch) {
		ERROR_PLATFORM_THROW("Cannot initialize XercesC: " + X(toCatch.getMessage()).str());
	}

	_sessionId = UUID::getUUID();
	_factory = Factory::getInstance();
}


InterpreterImpl::~InterpreterImpl() {

	// make sure we deallocate all user-data in the DOM,
	// this is neccesary if we were aborted early
	std::list<DOMElement*> invokes = DOMUtils::filterChildElements(_xmlPrefix + "invoke", _scxml, true);
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

	if (_lambdaMonitor)
		delete _lambdaMonitor;

	{
		std::lock_guard<std::recursive_mutex> lock(_instanceMutex);
		_instances.erase(getSessionId());
	}

//    assert(_invokers.size() == 0);
//    ::XERCESC_NS::XMLPlatformUtils::Terminate();

#ifdef WITH_CACHE_FILES
	if (!envVarIsTrue("USCXML_NOCACHE_FILES") && _document != NULL) {
		// save our cache
		std::string sharedTemp = URL::getTempDir(true);
		std::ofstream dataFS(sharedTemp + PATH_SEPERATOR + md5(_baseURL) + ".uscxml.cache");
		if (dataFS) {
			dataFS << _cache;
			dataFS.close();
		}
	}
#endif
}

InterpreterState InterpreterImpl::step(size_t blockMs) {
	std::lock_guard<std::recursive_mutex> lock(_serializationMutex);
	if (!_isInitialized) {
		init();
		_state = USCXML_INITIALIZED;
	} else {
		_state = _microStepper.step(blockMs);
	}
	return _state;
}

void InterpreterImpl::reset() {
	if (_microStepper)
		_microStepper.reset();

	_isInitialized = false;
	_state = USCXML_INSTANTIATED;
	//        _dataModel.reset();
	if (_delayQueue)
		_delayQueue.reset();
	//        _contentExecutor.reset();
}

void InterpreterImpl::cancel() {

	_microStepper.markAsCancelled();
	Event unblock;
	enqueueExternal(unblock);
}

void InterpreterImpl::deserialize(const std::string& encodedState) {

	init();
//    std::cout << encodedState << std::endl;
	Data state = Data::fromJSON(encodedState);
	if (!state.hasKey("microstepper")) {
		ERROR_PLATFORM_THROW("No microstepper information in serialized state");
	}

	if (!state.hasKey("url")) {
		ERROR_PLATFORM_THROW("No url information in serialized state");
	}

	if (!state.hasKey("md5")) {
		ERROR_PLATFORM_THROW("No MD5 hash in serialized state");
	}

	if (state.hasKey("externalQueue")) {
		_externalQueue.deserialize(state["externalQueue"]);
	}

	if (state.hasKey("delayQueue")) {
		_delayQueue.deserialize(state["delayQueue"]);
	}

	if (_md5.size() == 0) {
		// get md5 of current document
		std::stringstream ss;
		ss << *_document;
		_md5 = md5(ss.str());
	}

	if (state["md5"].atom != _md5) {
		ERROR_PLATFORM_THROW("MD5 hash mismatch in serialized state");
	}

	std::list<XERCESC_NS::DOMElement*> datas = DOMUtils::inDocumentOrder({ XML_PREFIX(_scxml).str() + "data" }, _scxml);
	for (auto data : datas) {
		if (HAS_ATTR(data, kXMLCharId) && state["datamodel"].hasKey(ATTR(data, kXMLCharId)))
			_dataModel.init(ATTR(data, kXMLCharId), state["datamodel"][ATTR(data, kXMLCharId)]);
	}

	_microStepper.deserialize(state["microstepper"]);

	std::list<XERCESC_NS::DOMElement*> invokes = DOMUtils::inDocumentOrder({ XML_PREFIX(_scxml).str() + "invoke" }, _scxml);
	for (auto invokeElem : invokes) {
		// BasicContentExecutor sets invokeid userdata upon invocation
		char* invokeId = (char*)invokeElem->getUserData(X("invokeid"));
		if (invokeId != NULL && _invokers.find(invokeId) != _invokers.end()) {
			std::string path = DOMUtils::xPathForNode(invokeElem);
			if (state.hasKey("invoker") && state["invoker"].hasKey(path)) {
				_invokers[invokeId].deserialize(state["invoker"][path]);
			}
		}
	}

}

std::string InterpreterImpl::serialize() {
	std::lock_guard<std::recursive_mutex> lock(_serializationMutex);

	Data serialized;
	if (_state != USCXML_IDLE && _state != USCXML_MACROSTEPPED && _state != USCXML_FINISHED) {
		ERROR_PLATFORM_THROW("Cannot serialize an unstable interpreter");
	}

	if (_md5.size() == 0) {
		// get md5 of current document
		std::stringstream ss;
		ss << *_document;
		_md5 = md5(ss.str());
	}

	serialized["md5"] = Data(_md5);
	serialized["url"] = Data(std::string(_baseURL));
	serialized["microstepper"] = _microStepper.serialize();

	// SCXML Rec: "the values of all attributes of type "id" must be unique within the session"
	std::list<XERCESC_NS::DOMElement*> datas = DOMUtils::inDocumentOrder({ XML_PREFIX(_scxml).str() + "data" }, _scxml);
	for (auto data : datas) {
		if (HAS_ATTR(data, kXMLCharId)) {
			serialized["datamodel"][ATTR(data, kXMLCharId)] = _dataModel.evalAsData(ATTR(data, kXMLCharId));
		}
	}

	// save all invokers' state
	std::list<XERCESC_NS::DOMElement*> invokes = DOMUtils::inDocumentOrder({ XML_PREFIX(_scxml).str() + "invoke" }, _scxml);
	for (auto invokeElem : invokes) {
		// BasicContentExecutor sets invokeid userdata upon invocation
		char* invokeId = (char*)invokeElem->getUserData(X("invokeid"));
		if (invokeId != NULL && _invokers.find(invokeId) != _invokers.end()) {
			std::string path = DOMUtils::xPathForNode(invokeElem);
			serialized["invoker"][path] = _invokers[invokeId].serialize();
		}
	}

//    serialized["internalQueue"] = _internalQueue.serialize();
	serialized["externalQueue"] = _externalQueue.serialize();
	serialized["delayQueue"] = _delayQueue.serialize();

	return serialized.asJSON();
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

		_xmlPrefix = X(_scxml->getPrefix()).str();
		_xmlNS = X(_scxml->getNamespaceURI()).str();
		if (_xmlPrefix.size() > 0) {
			_xmlPrefix = std::string(_xmlPrefix) + ":";
		}
		if (HAS_ATTR(_scxml, kXMLCharName)) {
			_name = ATTR(_scxml, kXMLCharName);
		} else {
			_name = _baseURL.pathComponents().back();
		}

		// download all script, see issue 134
		std::list<DOMElement*> scripts = DOMUtils::filterChildElements(_xmlPrefix + "script", _scxml, true);
		for (auto script : scripts) {
			if (HAS_ATTR(script, kXMLCharSource)) {
				std::string src = ATTR(script, kXMLCharSource);
				std::string contents;
				if (src.size() > 0) {
					URL url(src);
					if (!url.isAbsolute()) {
						url = URL::resolve(url, _baseURL);
					}
					contents = url.getInContent();
				} else {
					ERROR_COMMUNICATION2(exc, "Empty source attribute", script);
					throw exc;
				}

				XERCESC_NS::DOMText* scriptText = _document->createTextNode(X(contents));
				XERCESC_NS::DOMNode* newNode = _document->importNode(scriptText, true);
				script->appendChild(newNode);
				/**
				 * We nees to download all scripts (issue134) but also fail validation when there
				 * are child nodes with the src attribute present (issue141). Make a note that we
				 * already downloaded the content.
				 */
				script->setUserData(X("downloaded"), newNode, NULL);
			}
		}

		_binding = (HAS_ATTR(_scxml, kXMLCharBinding) && iequals(ATTR(_scxml, kXMLCharBinding), "late") ? LATE : EARLY);

	}
}

void InterpreterImpl::init() {

	if (_isInitialized)
		return;

	setupDOM();

#ifdef WITH_CACHE_FILES
	if (!envVarIsTrue("USCXML_NOCACHE_FILES")) {
		// try to open chached data from resource directory
		std::string sharedTemp = URL::getTempDir(true);
		std::ifstream dataFS(sharedTemp + PATH_SEPERATOR + md5(_baseURL) + ".uscxml.cache");
		try {
			if (dataFS.is_open()) {
				LOGD(USCXML_INFO) << "Using cache from '" << sharedTemp << PATH_SEPERATOR << md5(_baseURL) << ".uscxml.cache'" << std::endl;
				std::string cacheStr((std::istreambuf_iterator<char>(dataFS)),
				                     std::istreambuf_iterator<char>());
				_cache = Data::fromJSON(cacheStr);
			}
		} catch (...) {
			remove(std::string(sharedTemp + PATH_SEPERATOR + md5(_baseURL) + ".uscxml.cache").c_str());
		}

		// get md5 of current document
		if (_md5.length() == 0) {
			std::stringstream ss;
			ss << *_document;
			_md5 = md5(ss.str());
		}

		if (_cache.compound.find("InterpreterImpl") != _cache.compound.end() &&
		        _cache.compound["InterpreterImpl"].compound.find("md5") != _cache.compound["InterpreterImpl"].compound.end() &&
		        _cache.compound["InterpreterImpl"].compound["md5"].atom != _md5) {

			// that's not our cache!
			_cache.clear();
		}

		_cache.compound["InterpreterImpl"].compound["baseURL"] = Data(std::string(_baseURL));
		_cache.compound["InterpreterImpl"].compound["md5"] = Data(_md5);
	}
#endif

	// register io processors
	std::map<std::string, IOProcessorImpl*> ioProcs = _factory->getIOProcessors();
	for (auto ioProcIter = ioProcs.begin(); ioProcIter != ioProcs.end(); ioProcIter++) {

		// do not override if already set
		if (_ioProcs.find(ioProcIter->first) != _ioProcs.end()) {
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
		_microStepper = MicroStep(std::shared_ptr<MicroStepImpl>(new LargeMicroStep(this)));
	}
	_microStepper.init(_scxml);

	if (!_dataModel) {
		_dataModel = _factory->createDataModel(HAS_ATTR(_scxml, kXMLCharDataModel) ? ATTR(_scxml, kXMLCharDataModel) : "null", this);
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
	std::string id = ATTR(root, kXMLCharId);
	Data d;

	std::map<std::string, std::string> additionalAttr;
	auto xmlAttrs = root->getAttributes();
	size_t nrAttrs = xmlAttrs->getLength();
	for (size_t i = 0; i < nrAttrs; i++) {
		auto attr = xmlAttrs->item(i);
		additionalAttr[X(attr->getNodeName()).str()] = X(attr->getNodeValue()).str();
	}

	try {
		if (Event::getParam(_invokeReq.params, id, d)) {
			_dataModel.init(id, d, additionalAttr);
		} else if (_invokeReq.namelist.find(id) != _invokeReq.namelist.end()) {
			_dataModel.init(id, _invokeReq.namelist[id], additionalAttr);
		} else {
			_dataModel.init(id, _execContent.elementAsData(root), additionalAttr);
		}
	} catch(ErrorEvent e) {
		// test 277
		e.data.compound["xpath"] = uscxml::Data(DOMUtils::xPathForNode(root), uscxml::Data::VERBATIM);
		\
		enqueueInternal(e);
	}
}

void InterpreterImpl::assign(const std::string& location, const Data& data, const std::map<std::string, std::string>& attrs) {
	_dataModel.assign(location, data, attrs);
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
		        _finalize.find(_currEvent.invokeid) != _finalize.end() &&
		        _finalize[_currEvent.invokeid] != NULL) {
			_execContent.process(_finalize[_currEvent.invokeid]);
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

	assert(sendEvent.getUUID().length() > 0);
	assert(_delayedEventTargets.find(sendEvent.getUUID()) == _delayedEventTargets.end());

	_delayedEventTargets[sendEvent.getUUID()] = std::tuple<std::string, std::string, std::string>(sendEvent.sendid, type, target);
	if (delayMs == 0) {
		Event copy(sendEvent);
		return eventReady(copy, sendEvent.getUUID());
	} else {
		return _delayQueue.enqueueDelayed(sendEvent, delayMs, sendEvent.getUUID());
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
	_finalize[invokeEvent.invokeid] = finalize;
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
		_finalize.erase(invokeId);
		_invokers.erase(invokeId);
	}

}

void InterpreterImpl::enqueueAtInvoker(const std::string& invokeId, const Event& event) {
	if (_invokers.find(invokeId) != _invokers.end()) {
		std::lock_guard<std::recursive_mutex> lock(_instanceMutex);
		try {
			_invokers[invokeId].eventFromSCXML(event);
		} catch (const std::exception &e) {
			ERROR_COMMUNICATION_THROW("Exception caught while sending event to invoker '" + invokeId + "': " + e.what());
		} catch(...) {
			ERROR_COMMUNICATION_THROW("Exception caught while sending event to invoker '" + invokeId + "'");
		}
	} else {
		ERROR_COMMUNICATION_THROW("Can not send to invoked component '" + invokeId + "', no such invokeId");
	}

}

void InterpreterImpl::enqueueAtParent(const Event& event) {
	if (_parentQueue) {
		_parentQueue.enqueue(event);
	} else {
		ERROR_COMMUNICATION_THROW("Sending to parent invoker, but none is set");
	}

}

LambdaMonitor& InterpreterImpl::on() {
	if (_lambdaMonitor == NULL) {
		_lambdaMonitor = new LambdaMonitor();
		addMonitor(_lambdaMonitor);
	}
	return *_lambdaMonitor;
}

}
