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
#include "easylogging++.h"

#include <iostream>
#include <boost/algorithm/string.hpp>

#include <assert.h>
#include <algorithm>
#include <memory>
#include <mutex>

#include "getopt.h"

#include "easylogging++.h"
INITIALIZE_EASYLOGGINGPP

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
		LOG(ERROR) << X(toCatch.getMessage());
	} catch (const XERCESC_NS::RuntimeException& toCatch) {
		LOG(ERROR) << X(toCatch.getMessage());
	} catch (const XERCESC_NS::XMLException& toCatch) {
		LOG(ERROR) << X(toCatch.getMessage());
	} catch (const XERCESC_NS::DOMException& toCatch) {
		LOG(ERROR) << X(toCatch.getMessage());
	}

	return interpreter;

}

void Interpreter::reset() {
	return _impl->reset();
}

InterpreterState Interpreter::step(bool blocking) {
	return _impl->step(blocking);
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

void Interpreter::setMonitor(InterpreterMonitor* monitor) {
	return _impl->setMonitor(monitor);
}

std::list<InterpreterIssue> Interpreter::validate() {
	return InterpreterIssue::forInterpreter(_impl.get());
}

std::recursive_mutex StateTransitionMonitor::_mutex;

static void printNodeSet(const std::list<XERCESC_NS::DOMElement*> nodes) {
	std::string seperator;
	for (auto nIter = nodes.begin(); nIter != nodes.end(); nIter++) {
		std::cerr << seperator << (HAS_ATTR(*nIter, "id") ? ATTR(*nIter, "id") : DOMUtils::xPathForNode(*nIter));
		seperator = ", ";
	}
}

void StateTransitionMonitor::beforeTakingTransition(const XERCESC_NS::DOMElement* transition) {
	std::lock_guard<std::recursive_mutex> lock(_mutex);
	std::cerr << "Transition: " << uscxml::DOMUtils::xPathForNode(transition) << std::endl;
}

void StateTransitionMonitor::onStableConfiguration() {
	std::lock_guard<std::recursive_mutex> lock(_mutex);
	std::cerr << "Stable Config: { ";
//	printNodeSet(_interpreter.getConfiguration());
	std::cerr << " }" << std::endl;
}

void StateTransitionMonitor::beforeProcessingEvent(const  uscxml::Event& event) {
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

void StateTransitionMonitor::beforeExecutingContent(const XERCESC_NS::DOMElement* element) {
	std::lock_guard<std::recursive_mutex> lock(_mutex);
	std::cerr << "Executable Content: " << DOMUtils::xPathForNode(element) << std::endl;
}

void StateTransitionMonitor::beforeExitingState(const XERCESC_NS::DOMElement* state) {
	std::lock_guard<std::recursive_mutex> lock(_mutex);
	std::cerr << "Exiting: " << (HAS_ATTR(state, "id") ? ATTR(state, "id") : DOMUtils::xPathForNode(state)) << std::endl;
}

void StateTransitionMonitor::beforeEnteringState(const XERCESC_NS::DOMElement* state) {
	std::lock_guard<std::recursive_mutex> lock(_mutex);
	std::cerr << "Entering: " << (HAS_ATTR(state, "id") ? ATTR(state, "id") : DOMUtils::xPathForNode(state)) << std::endl;

}

void StateTransitionMonitor::beforeMicroStep() {
	std::lock_guard<std::recursive_mutex> lock(_mutex);
	std::cerr << "Config: {";
//	printNodeSet(_interpreter.getConfiguration());
	std::cerr << "}" << std::endl;
}

void InterpreterOptions::printUsageAndExit(const char* progName) {
	// remove path from program name
	std::string progStr(progName);
	if (progStr.find_last_of(PATH_SEPERATOR) != std::string::npos) {
		progStr = progStr.substr(progStr.find_last_of(PATH_SEPERATOR) + 1, progStr.length() - (progStr.find_last_of(PATH_SEPERATOR) + 1));
	}

	printf("%s version " USCXML_VERSION " (" CMAKE_BUILD_TYPE " build - " CMAKE_COMPILER_STRING ")\n", progStr.c_str());
	printf("Usage\n");
	printf("\t%s", progStr.c_str());
	printf(" [-v] [-d] [-lN]");
#ifdef BUILD_AS_PLUGINS
	printf(" [-p pluginPath]");
#endif
	printf(" [-tN]");
#ifdef EVENT_SSL_FOUND
	printf(" [-sN] [--certificate=FILE | --private-key=FILE --public-key=FILE] ");
#endif
	printf(" \\\n\t\t URL1 [--disable-http] [--option1=value1 --option2=value2]");
	printf(" \\\n\t\t[URL2 [--disable-http] [--option3=value3 --option4=value4]]");
	printf(" \\\n\t\t[URLN [--disable-http] [--optionN=valueN --optionM=valueM]]");
	printf("\n");
	printf("Options\n");
#ifdef BUILD_AS_PLUGINS
	printf("\t-p        : path to the uSCXML plugins (or export USCXML_PLUGIN_PATH)\n");
#endif
	printf("\t-v        : be verbose\n");
	printf("\t-c        : perform some sanity checks on the state-chart\n");
	printf("\t-lN       : set loglevel to N\n");
	printf("\t-tN       : port for HTTP server\n");
	printf("\t-sN       : port for HTTPS server\n");
	printf("\t-wN       : port for WebSocket server\n");
	printf("\n");
	exit(1);
}

InterpreterOptions InterpreterOptions::fromCmdLine(int argc, char** argv) {
	InterpreterOptions options;
	optind = 0;
	struct option longOptions[] = {
		{"check",         no_argument,       0, 'c'},
		{"verbose",       no_argument,       0, 'v'},
		{"debug",         no_argument,       0, 'd'},
		{"port",          required_argument, 0, 't'},
		{"ssl-port",      required_argument, 0, 's'},
		{"ws-port",       required_argument, 0, 'w'},
		{"certificate",   required_argument, 0, 0},
		{"private-key",   required_argument, 0, 0},
		{"public-key",    required_argument, 0, 0},
		{"plugin-path",   required_argument, 0, 'p'},
		{"loglevel",      required_argument, 0, 'l'},
		{0, 0, 0, 0}
	};

	opterr = 0;
	InterpreterOptions* currOptions = &options;

	// parse global options
	int optionInd = 0;
	int option;
	for (;;) {
		option = getopt_long_only(argc, argv, "+vcdt:s:w:p:l:", longOptions, &optionInd);
		if (option == -1) {
			if (optind == argc)
				// we are done with parsing
				goto DONE_PARSING_CMD;

			std::string url = argv[optind];

			options.interpreters.push_back(std::make_pair(url, new InterpreterOptions()));
			currOptions = options.interpreters.back().second;

			argc -= optind;
			argv += optind;
			optind = 0;

			if (argc <= 1)
				goto DONE_PARSING_CMD;

		}
		switch(option) {
		// cases without short option
		case 0: {
			if (iequals(longOptions[optionInd].name, "disable-http")) {
				currOptions->withHTTP = false;
			} else if (iequals(longOptions[optionInd].name, "private-key")) {
				currOptions->privateKey = optarg;
			} else if (iequals(longOptions[optionInd].name, "certificate")) {
				currOptions->certificate = optarg;
			} else if (iequals(longOptions[optionInd].name, "public-key")) {
				currOptions->publicKey = optarg;
			}
			break;
		}
		// cases with short-hand options
		case 'l':
			currOptions->logLevel = strTo<unsigned int>(optarg);
			break;
		case 'p':
			currOptions->pluginPath = optarg;
			break;
		case 'c':
			currOptions->validate = true;
			break;
		case 't':
			currOptions->httpPort = strTo<unsigned short>(optarg);
			break;
		case 's':
			currOptions->httpsPort = strTo<unsigned short>(optarg);
			break;
		case 'w':
			currOptions->wsPort = strTo<unsigned short>(optarg);
			break;
		case 'v':
			currOptions->verbose = true;
			break;
		case '?': {
			std::string param = argv[optind - 1];
			if (boost::starts_with(param, "--")) {
				param = param.substr(2, param.length() - 2);
			}	else if (boost::starts_with(param, "-")) {
				param = param.substr(1, param.length() - 1);
			} else {
				break;
			}
			boost::trim(param);

			size_t equalPos = param.find("=");
			if (equalPos != std::string::npos) {
				std::string key = param.substr(0, equalPos);
				std::string value = param.substr(equalPos + 1, param.length() - (equalPos + 1));
				currOptions->additionalParameters[key] = value;
			} else {
				currOptions->additionalParameters[param] = "";
			}
			break;
		}
		default:
			break;
		}
	}

DONE_PARSING_CMD:

	if (options.interpreters.size() == 0)
		options.error = "No SCXML document to evaluate";

	return options;
}


}
