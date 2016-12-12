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

#include <xercesc/parsers/XercesDOMParser.hpp>
#include <xercesc/framework/MemBufInputSource.hpp>
#include <xercesc/dom/DOM.hpp>
#include <xercesc/sax/HandlerBase.hpp>
#include <xercesc/util/XMLString.hpp>
#include <xercesc/util/PlatformUtils.hpp>
#include "uscxml/interpreter/Logging.h"

#include <iostream>
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
		LOGD(USCXML_ERROR) << X(toCatch.getMessage());
	} catch (const XERCESC_NS::RuntimeException& toCatch) {
		LOGD(USCXML_ERROR) << X(toCatch.getMessage());
	} catch (const XERCESC_NS::XMLException& toCatch) {
		LOGD(USCXML_ERROR) << X(toCatch.getMessage());
	} catch (const XERCESC_NS::DOMException& toCatch) {
		LOGD(USCXML_ERROR) << X(toCatch.getMessage());
	}

	return interpreter;

}

void Interpreter::reset() {
	return _impl->reset();
}

InterpreterState Interpreter::step(size_t blockMs) {
	return _impl->step(blockMs);
};

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

std::recursive_mutex StateTransitionMonitor::_mutex;

#if 0
static void printNodeSet(const std::list<XERCESC_NS::DOMElement*> nodes) {
	std::string seperator;
	for (auto nIter = nodes.begin(); nIter != nodes.end(); nIter++) {
		std::cerr << seperator << (HAS_ATTR(*nIter, "id") ? ATTR(*nIter, "id") : DOMUtils::xPathForNode(*nIter));
		seperator = ", ";
	}
}
#endif

void StateTransitionMonitor::beforeTakingTransition(Interpreter& interpreter, const XERCESC_NS::DOMElement* transition) {
	std::lock_guard<std::recursive_mutex> lock(_mutex);
	std::cerr << "Transition: " << uscxml::DOMUtils::xPathForNode(transition) << std::endl;
}

void StateTransitionMonitor::onStableConfiguration(Interpreter& interpreter) {
	std::lock_guard<std::recursive_mutex> lock(_mutex);
	std::cerr << "Stable Config: { ";
//	printNodeSet(_interpreter.getConfiguration());
	std::cerr << " }" << std::endl;
}

void StateTransitionMonitor::beforeProcessingEvent(Interpreter& interpreter, const uscxml::Event& event) {
	std::lock_guard<std::recursive_mutex> lock(_mutex);
	switch (event.eventType) {
	case uscxml::Event::INTERNAL:
		std::cerr << "Internal Event: " << event.name << std::endl;
		break;
	case uscxml::Event::EXTERNAL:
		std::cerr << "External Event: " << event.name << std::endl;
		break;
	case uscxml::Event::PLATFORM:
		std::cerr << "Platform Event: " << event.name << std::endl;
		break;
	}
}

void StateTransitionMonitor::beforeExecutingContent(Interpreter& interpreter, const XERCESC_NS::DOMElement* element) {
	std::lock_guard<std::recursive_mutex> lock(_mutex);
	std::cerr << "Executable Content: " << DOMUtils::xPathForNode(element) << std::endl;
}

void StateTransitionMonitor::beforeExitingState(Interpreter& interpreter, const XERCESC_NS::DOMElement* state) {
	std::lock_guard<std::recursive_mutex> lock(_mutex);
	std::cerr << "Exiting: " << (HAS_ATTR(state, "id") ? ATTR(state, "id") : DOMUtils::xPathForNode(state)) << std::endl;
}

void StateTransitionMonitor::beforeEnteringState(Interpreter& interpreter, const XERCESC_NS::DOMElement* state) {
	std::lock_guard<std::recursive_mutex> lock(_mutex);
	std::cerr << "Entering: " << (HAS_ATTR(state, "id") ? ATTR(state, "id") : DOMUtils::xPathForNode(state)) << std::endl;

}

void StateTransitionMonitor::beforeMicroStep(Interpreter& interpreter) {
	std::lock_guard<std::recursive_mutex> lock(_mutex);
	std::cerr << "Config: {";
//	printNodeSet(_interpreter.getConfiguration());
	std::cerr << "}" << std::endl;
}

}
