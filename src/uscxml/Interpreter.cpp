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
#include "uscxml/Interpreter.h"
#include "uscxml/interpreter/InterpreterImpl.h"
#include "uscxml/util/DOM.h"
#include "uscxml/util/URL.h"
#include "uscxml/util/MD5.hpp"

#include <xercesc/parsers/XercesDOMParser.hpp>
#include <xercesc/framework/MemBufInputSource.hpp>
#include <xercesc/dom/DOM.hpp>
#include <xercesc/sax/HandlerBase.hpp>
#include <xercesc/util/XMLString.hpp>
#include <xercesc/util/PlatformUtils.hpp>
#include "uscxml/interpreter/Logging.h"

#include <boost/algorithm/string.hpp>

#include <assert.h>
#include <algorithm>
#include <memory>
#include <mutex>

#define VERBOSE 0

namespace uscxml {

// msxml.h defines all the DOM types as well
//using namespace XERCESC_NS;

static URL normalizeURL(const std::string url) {
	URL absUrl(url);

	// this is required for _baseURL to be considered absolute!
	if (absUrl.scheme() == "" || !absUrl.isAbsolute()) {
		absUrl = URL::resolveWithCWD(absUrl);
	}
	if (absUrl.scheme() == "") {
		absUrl = URL("file://" + url);
	}
	return absUrl;
}

Interpreter Interpreter::fromXML(const std::string& xml, const std::string& baseURL) {

	URL absUrl = normalizeURL(baseURL);

	std::shared_ptr<InterpreterImpl> interpreterImpl(new InterpreterImpl());
	Interpreter interpreter(interpreterImpl);

	std::unique_ptr<XERCESC_NS::XercesDOMParser> parser(new XERCESC_NS::XercesDOMParser());
	std::unique_ptr<XERCESC_NS::ErrorHandler> errHandler(new XERCESC_NS::HandlerBase());

	try {
		parser->setValidationScheme(XERCESC_NS::XercesDOMParser::Val_Always);
		parser->setDoNamespaces(true);
		parser->useScanner(XERCESC_NS::XMLUni::fgWFXMLScanner);

		parser->setErrorHandler(errHandler.get());

		XERCESC_NS::MemBufInputSource is((XMLByte*)xml.c_str(), xml.size(), X("fake"));
		parser->parse(is);

		interpreterImpl->_document = parser->adoptDocument();
		interpreterImpl->_baseURL = absUrl;
		interpreterImpl->_md5 = md5(xml);
		InterpreterImpl::addInstance(interpreterImpl);

	} catch (const XERCESC_NS::SAXParseException& toCatch) {
		ERROR_PLATFORM_THROW(X(toCatch.getMessage()).str());
	} catch (const XERCESC_NS::RuntimeException& toCatch) {
		ERROR_PLATFORM_THROW(X(toCatch.getMessage()).str());
	} catch (const XERCESC_NS::XMLException& toCatch) {
		ERROR_PLATFORM_THROW(X(toCatch.getMessage()).str());
	} catch (const XERCESC_NS::DOMException& toCatch) {
		ERROR_PLATFORM_THROW(X(toCatch.getMessage()).str());
	}

	return interpreter;
}

Interpreter Interpreter::fromElement(XERCESC_NS::DOMElement* scxml, const std::string& baseURL) {
	URL absUrl = normalizeURL(baseURL);

	std::shared_ptr<InterpreterImpl> interpreterImpl(new InterpreterImpl());
	Interpreter interpreter(interpreterImpl);

	// *copy* the given XERCESC_NS::DOM to get rid of event listeners
	XERCESC_NS::DOMImplementation* implementation = XERCESC_NS::DOMImplementationRegistry::getDOMImplementation(X("core"));
	interpreterImpl->_document = implementation->createDocument();

	// we need to import the parent - to support xpath test150
	XERCESC_NS::DOMNode* newNode = interpreterImpl->_document->importNode(scxml, true);
//    interpreterImpl->_document->adoptNode(newNode);
	interpreterImpl->_document->appendChild(newNode);

//    std::cerr << *(interpreterImpl->_document);

	interpreterImpl->_baseURL = absUrl;

	InterpreterImpl::addInstance(interpreterImpl);
	return interpreter;
}

Interpreter Interpreter::fromDocument(XERCESC_NS::DOMDocument* dom, const std::string& baseURL, bool copy) {
	URL absUrl = normalizeURL(baseURL);

	std::shared_ptr<InterpreterImpl> interpreterImpl(new InterpreterImpl());
	Interpreter interpreter(interpreterImpl);

	if (copy) {
		// *copy* the given XERCESC_NS::DOM to get rid of event listeners
		XERCESC_NS::DOMImplementation* implementation = XERCESC_NS::DOMImplementationRegistry::getDOMImplementation(X("core"));
		interpreterImpl->_document = implementation->createDocument();

		// we need to import the parent - to support xpath test150
		XERCESC_NS::DOMNode* newNode = interpreterImpl->_document->importNode(dom->getDocumentElement(), true);
		interpreterImpl->_document->appendChild(newNode);

	} else {
		interpreterImpl->_document = dom;
	}

	interpreterImpl->_baseURL = absUrl;

	InterpreterImpl::addInstance(interpreterImpl);
	return interpreter;
}

Interpreter Interpreter::fromURL(const std::string& url) {
	URL absUrl = normalizeURL(url);

#if 1
	// Xercesc is hard to build with SSL on windows, whereas curl uses winssl
	return fromXML(absUrl.getInContent(), absUrl);
#else

	std::shared_ptr<InterpreterImpl> interpreterImpl(new InterpreterImpl());
	Interpreter interpreter(interpreterImpl);

	std::unique_ptr<XERCESC_NS::XercesDOMParser> parser(new XERCESC_NS::XercesDOMParser());
	parser->setValidationScheme(XERCESC_NS::XercesDOMParser::Val_Always);
	parser->setDoNamespaces(true);

	// we do not have a real schema anyway
	parser->useScanner(XERCESC_NS::XMLUni::fgWFXMLScanner);

	std::unique_ptr<XERCESC_NS::ErrorHandler> errHandler(new XERCESC_NS::HandlerBase());
	parser->setErrorHandler(errHandler.get());


	try {
		std::string tmp = absUrl;
		parser->parse(tmp.c_str());
		interpreterImpl->_document = parser->adoptDocument();
		interpreterImpl->_baseURL = absUrl;
		InterpreterImpl::addInstance(interpreterImpl);
	}

	catch (const XERCESC_NS::SAXParseException& toCatch) {
		ERROR_PLATFORM_THROW(X(toCatch.getMessage()));
	} catch (const XERCESC_NS::RuntimeException& toCatch) {
		ERROR_PLATFORM_THROW(X(toCatch.getMessage()));
	} catch (const XERCESC_NS::XMLException& toCatch) {
		ERROR_PLATFORM_THROW(X(toCatch.getMessage()));
	} catch (const XERCESC_NS::DOMException& toCatch) {
		ERROR_PLATFORM_THROW(X(toCatch.getMessage()));
	}

	return interpreter;
#endif

}

Interpreter Interpreter::fromSessionId(const std::string& sessionId) {
	std::lock_guard<std::recursive_mutex> lock(InterpreterImpl::_instanceMutex);
	std::map<std::string, std::weak_ptr<InterpreterImpl> > instances = InterpreterImpl::getInstances();
	if (instances.find(sessionId) != instances.end()) {
		return Interpreter(instances[sessionId].lock());
	}
	return Interpreter();
}

void Interpreter::reset() {
	return _impl->reset();
}

void Interpreter::deserialize(const std::string& encodedState) {
	return _impl->deserialize(encodedState);
}

std::string Interpreter::serialize() {
	return _impl->serialize();
}

InterpreterState Interpreter::step(size_t blockMs) {
	return _impl->step(blockMs);
}

void loadState(const std::string& encodedState);

/**
 * Save the interpreter's state.
 */
std::string saveState();

void Interpreter::cancel() {
	return _impl->cancel();
}

bool Interpreter::isInState(const std::string& stateId) {
	return _impl->isInState(stateId);
}

InterpreterState Interpreter::getState() {
	return _impl->getState();
}

std::list<XERCESC_NS::DOMElement*> Interpreter::getConfiguration() {
	return _impl->getConfiguration();
}

void Interpreter::receive(const Event& event) {
	_impl->enqueueExternal(event);
}

void Interpreter::setActionLanguage(ActionLanguage actionLanguage) {
	return _impl->setActionLanguage(actionLanguage);
}

ActionLanguage* Interpreter::getActionLanguage() {
	return _impl->getActionLanguage();
}

void Interpreter::setFactory(Factory* factory) {
	return _impl->setFactory(factory);
}

void Interpreter::addMonitor(InterpreterMonitor* monitor) {
	return _impl->addMonitor(monitor);
}

void Interpreter::removeMonitor(InterpreterMonitor* monitor) {
	return _impl->removeMonitor(monitor);
}

Logger Interpreter::getLogger() {
	return _impl->getLogger();
}

std::list<InterpreterIssue> Interpreter::validate() {
	return InterpreterIssue::forInterpreter(_impl.get());
}

LambdaMonitor& Interpreter::on() {
	return _impl->on();
}

#if 1
static void printNodeSet(Logger& logger, const std::list<XERCESC_NS::DOMElement*> nodes) {
	std::string seperator;
	for (auto nIter = nodes.begin(); nIter != nodes.end(); nIter++) {
		LOG(logger, USCXML_VERBATIM) << seperator << (HAS_ATTR(*nIter, kXMLCharId) ? ATTR(*nIter, kXMLCharId) : DOMUtils::xPathForNode(*nIter));
		seperator = ", ";
	}
}
#endif

std::recursive_mutex StateTransitionMonitor::_mutex;

void StateTransitionMonitor::beforeTakingTransition(const std::string& sessionId,
                                                    const std::string& targetList,
                                                    const XERCESC_NS::DOMElement* transition) {
	std::lock_guard<std::recursive_mutex> lock(_mutex);
	LOG(_logger, USCXML_VERBATIM) << "Transition: " << uscxml::DOMUtils::xPathForNode(transition) << std::endl;
}

void StateTransitionMonitor::onStableConfiguration(const std::string& sessionId) {
	std::lock_guard<std::recursive_mutex> lock(_mutex);
	Interpreter interpreter = Interpreter::fromSessionId(sessionId);
	LOG(_logger, USCXML_VERBATIM) << "Stable Config: { ";
	printNodeSet(_logger, interpreter.getConfiguration());
	LOG(_logger, USCXML_VERBATIM) << " }" << std::endl;
}

void StateTransitionMonitor::beforeProcessingEvent(const std::string& sessionId, const uscxml::Event& event) {
	std::lock_guard<std::recursive_mutex> lock(_mutex);
	switch (event.eventType) {
	case uscxml::Event::INTERNAL:
		LOG(_logger, USCXML_VERBATIM) << "Internal Event: " << event.name << std::endl;
		break;
	case uscxml::Event::EXTERNAL:
		LOG(_logger, USCXML_VERBATIM) << "External Event: " << event.name << std::endl;
		break;
	case uscxml::Event::PLATFORM:
		LOG(_logger, USCXML_VERBATIM) << "Platform Event: " << event.name << std::endl;
		break;
	}
}

void StateTransitionMonitor::beforeExecutingContent(const std::string& sessionId, const XERCESC_NS::DOMElement* element) {
	std::lock_guard<std::recursive_mutex> lock(_mutex);
	LOG(_logger, USCXML_VERBATIM) << "Executable Content: " << DOMUtils::xPathForNode(element) << std::endl;
}

void StateTransitionMonitor::beforeExitingState(const std::string& sessionId,
        const std::string& stateName,
        const XERCESC_NS::DOMElement* state) {
	std::lock_guard<std::recursive_mutex> lock(_mutex);
	LOG(_logger, USCXML_VERBATIM) << "Exiting: " << (HAS_ATTR(state, kXMLCharId) ? ATTR(state, kXMLCharId) : DOMUtils::xPathForNode(state)) << std::endl;
}

void StateTransitionMonitor::beforeEnteringState(const std::string& sessionId,
        const std::string& stateName,
        const XERCESC_NS::DOMElement* state) {
	std::lock_guard<std::recursive_mutex> lock(_mutex);
	LOG(_logger, USCXML_VERBATIM) << "Entering: " << (HAS_ATTR(state, kXMLCharId) ? ATTR(state, kXMLCharId) : DOMUtils::xPathForNode(state)) << std::endl;

}

void StateTransitionMonitor::beforeMicroStep(const std::string& sessionId) {
	std::lock_guard<std::recursive_mutex> lock(_mutex);
	Interpreter interpreter = Interpreter::fromSessionId(sessionId);
	LOG(_logger, USCXML_VERBATIM) << "Microstep in config: {";
	printNodeSet(_logger, interpreter.getConfiguration());
	LOG(_logger, USCXML_VERBATIM) << "}" << std::endl;
}

}
