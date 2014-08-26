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
#include "uscxml/URL.h"
#include "uscxml/UUID.h"
#include "uscxml/DOMUtils.h"
#include "uscxml/transform/FlatStateIdentifier.h"
#include "uscxml/transform/ChartToFSM.h" // only for testing

#include "getopt.h"

#include "uscxml/plugins/invoker/http/HTTPServletInvoker.h"
#include "uscxml/server/InterpreterServlet.h"
#include "uscxml/concurrency/DelayedEventQueue.h"

#include <DOM/Simple/DOMImplementation.hpp>
#include <SAX/helpers/InputSourceResolver.hpp>
#include <DOM/io/Stream.hpp>

#include <boost/lexical_cast.hpp>
#include <boost/tokenizer.hpp>
#include <boost/algorithm/string.hpp>

#include <glog/logging.h>
#include <iostream>
#include <io/uri.hpp>

#include <assert.h>
#include <algorithm>

#include "uscxml/Factory.h"

#if 1
#	define INTERPRETER_IMPL InterpreterDraft6
#	include "uscxml/interpreter/InterpreterDraft6.h"
#else
#	define INTERPRETER_IMPL InterpreterRC
#	include "uscxml/interpreter/InterpreterRC.h"
#endif

#define VERBOSE 0

/// valid interpreter state transitions
#define VALID_FROM_INSTANTIATED(newState) ( \
	newState == USCXML_MICROSTEPPED || \
	newState == USCXML_DESTROYED\
)

#define VALID_FROM_FAULTED(newState) ( \
	newState == USCXML_DESTROYED\
)

#define VALID_FROM_INITIALIZED(newState) ( \
	newState == USCXML_MICROSTEPPED || \
	newState == USCXML_FINISHED \
)

#define VALID_FROM_MICROSTEPPED(newState) ( \
	newState == USCXML_DESTROYED || \
	newState == USCXML_MACROSTEPPED || \
	newState == USCXML_MICROSTEPPED || \
	newState == USCXML_FINISHED \
)

#define VALID_FROM_MACROSTEPPED(newState) ( \
	newState == USCXML_DESTROYED || \
	newState == USCXML_MICROSTEPPED || \
	newState == USCXML_MACROSTEPPED || \
	newState == USCXML_IDLE || \
	newState == USCXML_FINISHED \
)

#define VALID_FROM_IDLE(newState) ( \
	newState == USCXML_DESTROYED || \
	newState == USCXML_MICROSTEPPED || \
	newState == USCXML_MACROSTEPPED \
)

#define VALID_FROM_FINISHED(newState) ( \
	newState == USCXML_DESTROYED || \
	newState == USCXML_INSTANTIATED \
)

/// macro to catch exceptions in executeContent
#define CATCH_AND_DISTRIBUTE(msg) \
catch (Event e) {\
	if (rethrow) {\
		throw(e);\
	} else {\
		LOG(ERROR) << msg << std::endl << e << std::endl;\
		e.name = "error.execution";\
		e.data.compound["cause"] = uscxml::Data(msg, uscxml::Data::VERBATIM); \
		e.eventType = Event::PLATFORM;\
		receiveInternal(e);\
	}\
}

#define CATCH_AND_DISTRIBUTE2(msg, node) \
catch (Event e) {\
	std::string xpathPos = DOMUtils::xPathForNode(node); \
	if (rethrow) {\
		throw(e);\
	} else {\
		LOG(ERROR) << msg << " " << xpathPos << ":" << std::endl << e << std::endl;\
		e.name = "error.execution";\
		e.data.compound["cause"] = uscxml::Data(msg, uscxml::Data::VERBATIM); \
		e.data.compound["xpath"] = uscxml::Data(xpathPos, uscxml::Data::VERBATIM); \
		e.eventType = Event::PLATFORM;\
		e.dom = node;\
		receiveInternal(e);\
	}\
}

namespace uscxml {

using namespace Arabica::XPath;
using namespace Arabica::DOM;

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
	printf("\t-d        : enable debugging via HTTP\n");
	printf("\t-lN       : set loglevel to N\n");
	printf("\t-tN       : port for HTTP server\n");
	printf("\t-sN       : port for HTTPS server\n");
	printf("\t-wN       : port for WebSocket server\n");
	printf("\n");
	exit(1);
}

unsigned int InterpreterOptions::getCapabilities() {
	unsigned int capabilities = CAN_NOTHING;
	if (withHTTP)
		capabilities = capabilities | CAN_GENERIC_HTTP | CAN_BASIC_HTTP;

	return capabilities;
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
		{"disable-http",  no_argument, 0, 0},
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
			if (boost::equals(longOptions[optionInd].name, "disable-http")) {
				currOptions->withHTTP = false;
			} else if (boost::equals(longOptions[optionInd].name, "private-key")) {
				currOptions->privateKey = optarg;
			} else if (boost::equals(longOptions[optionInd].name, "certificate")) {
				currOptions->certificate = optarg;
			} else if (boost::equals(longOptions[optionInd].name, "public-key")) {
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
		case 'd':
			currOptions->withDebugger = true;
			break;
		case 'c':
			currOptions->checking = true;
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

	if (options.interpreters.size() == 0 && !options.withDebugger)
		options.error = "No SCXML document to evaluate";

	return options;
}


void NameSpaceInfo::init(const std::map<std::string, std::string>& namespaceInfo) {
	nsInfo = namespaceInfo;
	nsURL = "";
	if (nsContext)
		delete nsContext;
	nsContext = new Arabica::XPath::StandardNamespaceContext<std::string>();

	std::map<std::string, std::string>::const_iterator nsIter = namespaceInfo.begin();
	while(nsIter != namespaceInfo.end()) {
		std::string uri = nsIter->first;
		std::string prefix = nsIter->second;
		if (iequals(uri, "http://www.w3.org/2005/07/scxml")) {
			nsURL = uri;
			if (prefix.size() == 0) {
				xpathPrefix = "scxml:";
				nsContext->addNamespaceDeclaration(uri, "scxml");
			} else {
				xpathPrefix = prefix + ":";
				xmlNSPrefix = xpathPrefix;
				nsContext->addNamespaceDeclaration(uri, prefix);
				nsToPrefix[uri] = prefix;
			}
		} else {
			nsContext->addNamespaceDeclaration(uri, prefix);
			nsToPrefix[uri] = prefix;
		}
		nsIter++;
	}
}

std::map<std::string, boost::weak_ptr<InterpreterImpl> > Interpreter::_instances;
tthread::recursive_mutex Interpreter::_instanceMutex;

std::map<std::string, boost::weak_ptr<InterpreterImpl> > Interpreter::getInstances() {
	tthread::lock_guard<tthread::recursive_mutex> lock(_instanceMutex);
	std::map<std::string, boost::weak_ptr<InterpreterImpl> >::iterator instIter = _instances.begin();
	while(instIter != _instances.end()) {
		if (!instIter->second.lock()) {
			_instances.erase(instIter++);
		} else {
			instIter++;
		}
	}
	return _instances;
}


InterpreterImpl::InterpreterImpl() {
	_state = USCXML_INSTANTIATED;

	_lastRunOnMainThread = 0;
	_thread = NULL;
	_isStarted = false;
	_isRunning = false;
	_sendQueue = NULL;
	_parentQueue = NULL;
	_topLevelFinalReached = false;
	_stable = false;
	_isInitialized = false;
	_userSuppliedDataModel = false;
	_domIsSetup = false;
	_httpServlet = NULL;
	_factory = NULL;
	_sessionId = UUID::getUUID();
	_capabilities = CAN_BASIC_HTTP | CAN_GENERIC_HTTP;
	_domEventListener._interpreter = this;

#ifdef _WIN32
	WSADATA wsaData;
	WSAStartup(MAKEWORD(2, 2), &wsaData);
#endif
}

Interpreter Interpreter::fromDOM(const Arabica::DOM::Document<std::string>& dom, const NameSpaceInfo& nameSpaceInfo) {
	tthread::lock_guard<tthread::recursive_mutex> lock(_instanceMutex);
	boost::shared_ptr<INTERPRETER_IMPL> interpreterImpl = boost::shared_ptr<INTERPRETER_IMPL>(new INTERPRETER_IMPL);
	Interpreter interpreter(interpreterImpl);
	
	// *copy* the given DOM to get rid of event listeners
	
	DOMImplementation<std::string> domFactory = Arabica::SimpleDOM::DOMImplementation<std::string>::getDOMImplementation();
	interpreterImpl->_document = domFactory.createDocument(dom.getNamespaceURI(), "", 0);
	
	Node<std::string> child = dom.getFirstChild();
	while (child) {
		Node<std::string> newNode = interpreterImpl->_document.importNode(child, true);
		interpreterImpl->_document.appendChild(newNode);
		child = child.getNextSibling();
	}
	
	interpreterImpl->setNameSpaceInfo(nameSpaceInfo);
	interpreterImpl->setupDOM();

//	interpreterImpl->init();
	_instances[interpreterImpl->getSessionId()] = interpreterImpl;
	return interpreter;
}

Interpreter Interpreter::fromXML(const std::string& xml) {
	std::stringstream* ss = new std::stringstream();
	(*ss) << xml;
	// we need an auto_ptr for arabica to assume ownership
	std::auto_ptr<std::istream> ssPtr(ss);
	Arabica::SAX::InputSource<std::string> inputSource;
	inputSource.setByteStream(ssPtr);
	return fromInputSource(inputSource);
}

Interpreter Interpreter::fromURI(const std::string& uri) {
	URL url(uri);
	return fromURI(url);
}

Interpreter Interpreter::fromURI(const URL& uri) {
	URL absUrl = uri;
	if (!absUrl.isAbsolute()) {
		if (!absUrl.toAbsoluteCwd()) {
			ERROR_COMMUNICATION_THROW("URL is not absolute or does not have file schema");
		}
	}

	Interpreter interpreter;

	if (iequals(absUrl.scheme(), "file")) {
		Arabica::SAX::InputSource<std::string> inputSource;
		inputSource.setSystemId(absUrl.asString());
		interpreter = fromInputSource(inputSource);
#if 0
	} else if (iequals(absUrl.scheme(), "http")) {
		// handle http per arabica - this will not follow redirects
		Arabica::SAX::InputSource<std::string> inputSource;
		inputSource.setSystemId(absUrl.asString());
		interpreter = fromInputSource(inputSource);
#endif
	} else {
		// use curl for everything else
		std::stringstream ss;
		ss << absUrl;
		if (absUrl.downloadFailed()) {
			ERROR_COMMUNICATION_THROW("Downloading SCXML document from '" + absUrl.asString() + "' failed");
		}
		interpreter = fromXML(ss.str());
	}

	// try to establish URI root for relative src attributes in document
	if (interpreter) {
		interpreter._impl->_baseURI = URL::asBaseURL(absUrl);
		interpreter._impl->_sourceURI = absUrl;
	} else {
		ERROR_PLATFORM_THROW("Cannot create interpreter from URI '" + absUrl.asString() + "'");
	}
	return interpreter;
}

Interpreter Interpreter::fromInputSource(Arabica::SAX::InputSource<std::string>& source) {
	tthread::lock_guard<tthread::recursive_mutex> lock(_instanceMutex);

	// remove old instances
	std::map<std::string, boost::weak_ptr<InterpreterImpl> >::iterator instIter = _instances.begin();
	while(instIter != _instances.end()) {
		if (!instIter->second.lock()) {
			_instances.erase(instIter++);
		} else {
			instIter++;
		}
	}

	boost::shared_ptr<INTERPRETER_IMPL> interpreterImpl = boost::shared_ptr<INTERPRETER_IMPL>(new INTERPRETER_IMPL);
	Interpreter interpreter(interpreterImpl);
	_instances[interpreterImpl->getSessionId()] = interpreterImpl;

	NameSpacingParser parser;
	if (parser.parse(source) && parser.getDocument() && parser.getDocument().hasChildNodes()) {
		interpreterImpl->setNameSpaceInfo(parser.nameSpace);
		interpreterImpl->_document = parser.getDocument();
		interpreterImpl->setupDOM();
	} else {
		if (parser.errorsReported()) {
			ERROR_PLATFORM_THROW(parser.errors())
		} else {
			ERROR_PLATFORM_THROW("Failed to create interpreter");
//			interpreterImpl->setInterpreterState(USCXML_FAULTED, parser.errors());
		}
	}
	return interpreter;
}

Interpreter Interpreter::fromClone(const Interpreter& other) {
	boost::shared_ptr<INTERPRETER_IMPL> interpreterImpl = boost::shared_ptr<INTERPRETER_IMPL>(new INTERPRETER_IMPL);

	other.getImpl()->copyTo(interpreterImpl);
	Interpreter interpreter(interpreterImpl);
	return interpreter;
}

void InterpreterImpl::copyTo(InterpreterImpl* other) {
	if (getDocument()) {
#if 0
		std::stringstream* ss = new std::stringstream();
		(*ss) << getDocument();
		// we need an auto_ptr for arabica to assume ownership
		std::auto_ptr<std::istream> ssPtr(ss);
		Arabica::SAX::InputSource<std::string> inputSource;
		inputSource.setByteStream(ssPtr);

		NameSpacingParser parser;
		if (parser.parse(inputSource) && parser.getDocument() && parser.getDocument().hasChildNodes()) {
			other->setNameSpaceInfo(parser.nameSpace);
			other->_document = parser.getDocument();
			other->setupDOM();
		} else {
			if (parser.errorsReported()) {
				LOG(ERROR) << parser.errors();
			}
		}

#else
		Arabica::DOM::Document<std::string> clonedDocument;
		DOMImplementation<std::string> domFactory = Arabica::SimpleDOM::DOMImplementation<std::string>::getDOMImplementation();
		clonedDocument = domFactory.createDocument(getDocument().getNamespaceURI(), "", 0);

		Node<std::string> child = getDocument().getFirstChild();
		while (child) {
			Node<std::string> newNode = clonedDocument.importNode(child, true);
			clonedDocument.appendChild(newNode);
			child = child.getNextSibling();
		}

		other->_document = clonedDocument;

		other->setNameSpaceInfo(_nsInfo);
		other->setupDOM();
#endif
	}
}

void InterpreterImpl::copyTo(boost::shared_ptr<InterpreterImpl> other) {
	copyTo(other.get());
}

void InterpreterImpl::setName(const std::string& name) {
	_name = name;
}

InterpreterImpl::~InterpreterImpl() {
	{
		// make sure we are done with setting up with early abort
		tthread::lock_guard<tthread::recursive_mutex> lock(_mutex);
		stop(); // unset started bit
	}
//	std::cout << "stopped " << this << std::endl;
//	tthread::lock_guard<tthread::recursive_mutex> lock(_mutex);
	if (_thread) {
		if (_thread->get_id() != tthread::this_thread::get_id()) {

			// unblock event queue
			Event event;
			event.name = "unblock.and.die";
			receive(event);

			_thread->join();
			delete(_thread);
		} else {
			// this can happen with a shared_from_this at an interpretermonitor
			setInterpreterState(USCXML_DESTROYED);
		}
	}
	join();
	if (_sendQueue)
		delete _sendQueue;

}

void InterpreterImpl::start() {
	_isStarted = true;
	_thread = new tthread::thread(InterpreterImpl::run, this);
}

void InterpreterImpl::stop() {
	_isStarted = false;
}

void InterpreterImpl::join() {
	stop();
	if (_thread != NULL) _thread->join();
};

bool InterpreterImpl::isRunning() {
	return _isRunning && !_topLevelFinalReached;
}

void InterpreterImpl::run(void* instance) {
	InterpreterImpl* interpreter = ((InterpreterImpl*)instance);
	interpreter->_isRunning = true;

	try {
		InterpreterState state;
		while(interpreter->_isStarted) {
			state = interpreter->step(-1);

			switch (state) {
			case uscxml::USCXML_FINISHED:
			case uscxml::USCXML_DESTROYED:
				// return as we finished
				goto DONE_THREAD;
			default:
				break;
			}
		}
	} catch (Event e) {
		LOG(ERROR) << e;
	} catch(std::exception e) {
		LOG(ERROR) << "InterpreterImpl::run catched an exception: " << e.what() << std::endl << "Unclean shutdown";
	} catch (...) {
		LOG(ERROR) << "InterpreterImpl::run catched unknown exception";
	}
DONE_THREAD:
	((InterpreterImpl*)instance)->_isRunning = false;
	((InterpreterImpl*)instance)->_isStarted = false;
}

void InterpreterImpl::exitInterpreter() {
	NodeSet<std::string> statesToExit = _configuration;
	statesToExit.forward(false);
	statesToExit.sort();
	
	for (int i = 0; i < statesToExit.size(); i++) {
		Arabica::XPath::NodeSet<std::string> onExitElems = filterChildElements(_nsInfo.xmlNSPrefix + "onexit", statesToExit[i]);
		for (int j = 0; j < onExitElems.size(); j++) {
			executeContent(Element<std::string>(onExitElems[j]));
		}
		Arabica::XPath::NodeSet<std::string> invokeElems = filterChildElements(_nsInfo.xmlNSPrefix + "invoke", statesToExit[i]);
		// TODO: we ought to cancel all remaining invokers just to be sure with the persist extension
		for (int j = 0; j < invokeElems.size(); j++) {
			cancelInvoke(Element<std::string>(invokeElems[j]));
		}
		Element<std::string> stateElem(statesToExit[i]);
		if (isFinal(stateElem) && parentIsScxmlState(stateElem)) {
			returnDoneEvent(statesToExit[i]);
		}
	}
	_configuration = NodeSet<std::string>();
}

	
InterpreterState InterpreterImpl::interpret() {
	InterpreterState state;
	while(true) {
		state = step(-1);
		
		switch (state) {
			case uscxml::USCXML_FINISHED:
			case uscxml::USCXML_DESTROYED:
				// return as we finished
				return state;
			default:
				
				// process invokers on main thread
				if(_thread == NULL) {
					runOnMainThread(200);
				}
				
				// process next step
				break;
		}
	}
	return state;
}

// setup / fetch the documents initial transitions
NodeSet<std::string> InterpreterImpl::getDocumentInitialTransitions() {
	NodeSet<std::string> initialTransitions;
	
	if (_startConfiguration.size() > 0) {
		// we emulate entering a given configuration by creating a pseudo deep history
		Element<std::string> initHistory = _document.createElementNS(_nsInfo.nsURL, "history");
		_nsInfo.setPrefix(initHistory);
		
		initHistory.setAttribute("id", UUID::getUUID());
		initHistory.setAttribute("type", "deep");
		_scxml.insertBefore(initHistory, _scxml.getFirstChild());
		
		std::string histId = ATTR(initHistory, "id");
		NodeSet<std::string> histStates;
		for (std::list<std::string>::const_iterator stateIter = _startConfiguration.begin(); stateIter != _startConfiguration.end(); stateIter++) {
			histStates.push_back(getState(*stateIter));
		}
		_historyValue[histId] = histStates;
		
		Element<std::string> initialElem = _document.createElementNS(_nsInfo.nsURL, "initial");
		_nsInfo.setPrefix(initialElem);
		
		initialElem.setAttribute("generated", "true");
		Element<std::string> transitionElem = _document.createElementNS(_nsInfo.nsURL, "transition");
		_nsInfo.setPrefix(transitionElem);
		
		transitionElem.setAttribute("target", histId);
		initialElem.appendChild(transitionElem);
		_scxml.appendChild(initialElem);
		initialTransitions.push_back(transitionElem);
		
	} else {
		// try to get initial transition from initial element
		initialTransitions = _xpath.evaluate("/" + _nsInfo.xpathPrefix + "initial/" + _nsInfo.xpathPrefix + "transition", _scxml).asNodeSet();
		if (initialTransitions.size() == 0) {
			Arabica::XPath::NodeSet<std::string> initialStates;
			// fetch per draft
			initialStates = getInitialStates();
			assert(initialStates.size() > 0);
			for (int i = 0; i < initialStates.size(); i++) {
				Element<std::string> initialElem = _document.createElementNS(_nsInfo.nsURL, "initial");
				_nsInfo.setPrefix(initialElem);
				
				initialElem.setAttribute("generated", "true");
				Element<std::string> transitionElem = _document.createElementNS(_nsInfo.nsURL, "transition");
				_nsInfo.setPrefix(transitionElem);
				
				transitionElem.setAttribute("target", ATTR_CAST(initialStates[i], "id"));
				initialElem.appendChild(transitionElem);
				_scxml.appendChild(initialElem);
				initialTransitions.push_back(transitionElem);
			}
		}
	}
	return initialTransitions;
}

InterpreterState InterpreterImpl::step(int waitForMS) {
	try {
		tthread::lock_guard<tthread::recursive_mutex> lock(_mutex);
		
		if (_state == USCXML_FINISHED || _state == USCXML_DESTROYED) {
			return _state;
		}
		
		NodeSet<std::string> enabledTransitions;
		
		// setup document and interpreter
		if (!_isInitialized) {
			init(); // will throw
		}
		
		if (_configuration.size() == 0) {
			// goto initial configuration
			NodeSet<std::string> initialTransitions = getDocumentInitialTransitions();
			assert(initialTransitions.size() > 0);
#if 1
			std::cout << _name << ": initialTransitions: " << std::endl;
			for (int i = 0; i < initialTransitions.size(); i++) {
				std::cout << initialTransitions[i] << std::endl;
			}
			std::cout << std::endl;
#endif

			enterStates(initialTransitions);
			setInterpreterState(USCXML_MICROSTEPPED);
		}
		
		assert(isLegalConfiguration(_configuration));
		
		// are there spontaneous transitions?
		if (!_stable) {
			enabledTransitions = selectEventlessTransitions();
			if (!enabledTransitions.empty()) {
				// test 403b
				enabledTransitions.to_document_order();
				microstep(enabledTransitions);
				
				setInterpreterState(USCXML_MICROSTEPPED);
				return _state;
			}
			_stable = true;
		}
		
		// test415
		if (_topLevelFinalReached)
			goto EXIT_INTERPRETER;
		
		// process internal event
		if (!_internalQueue.empty()) {
			_currEvent = _internalQueue.front();
			_internalQueue.pop_front();
			_stable = false;
			
			USCXML_MONITOR_CALLBACK2(beforeProcessingEvent, _currEvent)
			
			_dataModel.setEvent(_currEvent);
			enabledTransitions = selectTransitions(_currEvent.name);
			
			if (!enabledTransitions.empty()) {
				// test 403b
				enabledTransitions.to_document_order();
				microstep(enabledTransitions);
			}
			
			// test 319 - even if we do not enable transitions, consider it a microstep
			setInterpreterState(USCXML_MICROSTEPPED);
			return _state;
			
		} else {
			_stable = true;
		}
		
		if (_state != USCXML_MACROSTEPPED && _state != USCXML_IDLE)
			USCXML_MONITOR_CALLBACK(onStableConfiguration)
			
			setInterpreterState(USCXML_MACROSTEPPED);
		
		if (_topLevelFinalReached)
			goto EXIT_INTERPRETER;
		
		
		// when we reach a stable configuration, invoke
		for (unsigned int i = 0; i < _statesToInvoke.size(); i++) {
			NodeSet<std::string> invokes = filterChildElements(_nsInfo.xmlNSPrefix + "invoke", _statesToInvoke[i]);
			for (unsigned int j = 0; j < invokes.size(); j++) {
				Element<std::string> invokeElem = Element<std::string>(invokes[j]);
				if (!HAS_ATTR(invokeElem, "persist") || !DOMUtils::attributeIsTrue(ATTR(invokeElem, "persist"))) {
					invoke(invokeElem);
				}
			}
		}
		_statesToInvoke = NodeSet<std::string>();
		
		if (_externalQueue.isEmpty()) {
			setInterpreterState(USCXML_IDLE);
			
			if (waitForMS < 0) {
				// wait blockingly for an event forever
				while(_externalQueue.isEmpty()) {
					_condVar.wait(_mutex);
				}
			}
			
			if (waitForMS > 0) {
				// wait given number of milliseconds max
				uint64_t now = tthread::chrono::system_clock::now();
				uint64_t then = now + waitForMS;
				while(_externalQueue.isEmpty() && now < then) {
					_condVar.wait_for(_mutex, then - now);
					now = tthread::chrono::system_clock::now();
				}
			}
			
			if (_externalQueue.isEmpty()) {
				return _state;
			}
			
			setInterpreterState(USCXML_MACROSTEPPED);
		}
		
		_currEvent = _externalQueue.pop();
		_currEvent.eventType = Event::EXTERNAL; // make sure it is set to external
		_stable = false;
		
		if (_topLevelFinalReached)
			goto EXIT_INTERPRETER;
		
		USCXML_MONITOR_CALLBACK2(beforeProcessingEvent, _currEvent)
		
		if (iequals(_currEvent.name, "cancel.invoke." + _sessionId)) {
			goto EXIT_INTERPRETER;
		}
		
		try {
			_dataModel.setEvent(_currEvent);
		} catch (Event e) {
			LOG(ERROR) << "Syntax error while setting external event:" << std::endl << e << std::endl << _currEvent;
		}
		
		finalizeAndAutoForwardCurrentEvent();
		
		// run internal processing until we reach a stable configuration again
		enabledTransitions = selectTransitions(_currEvent.name);
		if (!enabledTransitions.empty()) {
			// test 403b
			enabledTransitions.to_document_order();
			microstep(enabledTransitions);
		}
		
		if (_topLevelFinalReached)
			goto EXIT_INTERPRETER;
		
		return _state;
		
	EXIT_INTERPRETER:
		USCXML_MONITOR_CALLBACK(beforeCompletion)
		
		exitInterpreter();
		if (_sendQueue) {
			std::map<std::string, std::pair<InterpreterImpl*, SendRequest> >::iterator sendIter = _sendIds.begin();
			while(sendIter != _sendIds.end()) {
				_sendQueue->cancelEvent(sendIter->first);
				sendIter++;
			}
		}
		
		USCXML_MONITOR_CALLBACK(afterCompletion)
		
		//		assert(hasLegalConfiguration());
		_mutex.unlock();
		
		// remove datamodel
		if(!_userSuppliedDataModel)
			_dataModel = DataModel();
		
		setInterpreterState(USCXML_FINISHED);
		return _state;
	} catch (boost::bad_weak_ptr e) {
		LOG(ERROR) << "Unclean shutdown " << std::endl << std::endl;
		setInterpreterState(USCXML_DESTROYED);
		return _state;
	}
	
	// set datamodel to null from this thread
	if(_dataModel)
		_dataModel = DataModel();
	
}

void InterpreterImpl::microstep(const Arabica::XPath::NodeSet<std::string>& enabledTransitions) {
	
	USCXML_MONITOR_CALLBACK(beforeMicroStep)
	
	exitStates(enabledTransitions);
	
	for (int i = 0; i < enabledTransitions.size(); i++) {
		Element<std::string> transition(enabledTransitions[i]);
		
		USCXML_MONITOR_CALLBACK3(beforeTakingTransition, transition, (i + 1 < enabledTransitions.size()))
		
		executeContent(transition);
		
		USCXML_MONITOR_CALLBACK3(afterTakingTransition, transition, (i + 1 < enabledTransitions.size()))
	}
	
	enterStates(enabledTransitions);
	
	USCXML_MONITOR_CALLBACK(afterMicroStep)
	
}

// process transitions until we are in a stable configuration again
void InterpreterImpl::stabilize() {
	
	NodeSet<std::string> enabledTransitions;
	_stable = false;
	
	if (_configuration.size() == 0) {
		// goto initial configuration
		NodeSet<std::string> initialTransitions = getDocumentInitialTransitions();
		assert(initialTransitions.size() > 0);
		enterStates(initialTransitions);
	}
	
	do { // process microsteps for enabled transitions until there are no more left
		
		enabledTransitions = selectEventlessTransitions();
		
		if (enabledTransitions.size() == 0) {
			if (_internalQueue.size() == 0) {
				_stable = true;
			} else {
				_currEvent = _internalQueue.front();
				_internalQueue.pop_front();
#if VERBOSE
				std::cout << "Received internal event " << _currEvent.name << std::endl;
#endif
				
				USCXML_MONITOR_CALLBACK2(beforeProcessingEvent, _currEvent)
				
				if (_dataModel)
					_dataModel.setEvent(_currEvent);
				enabledTransitions = selectTransitions(_currEvent.name);
			}
		}
		
		if (!enabledTransitions.empty()) {
			// test 403b
			enabledTransitions.to_document_order();
			microstep(enabledTransitions);
		}
	} while(!_internalQueue.empty() || !_stable);
	
	USCXML_MONITOR_CALLBACK(onStableConfiguration)
	
	// when we reach a stable configuration, invoke
	for (unsigned int i = 0; i < _statesToInvoke.size(); i++) {
		NodeSet<std::string> invokes = filterChildElements(_nsInfo.xmlNSPrefix + "invoke", _statesToInvoke[i]);
		for (unsigned int j = 0; j < invokes.size(); j++) {
			Element<std::string> invokeElem = Element<std::string>(invokes[j]);
			if (!HAS_ATTR(invokeElem, "persist") || !DOMUtils::attributeIsTrue(ATTR(invokeElem, "persist"))) {
				invoke(invokeElem);
			}
		}
	}
	_statesToInvoke = NodeSet<std::string>();
}

Arabica::XPath::NodeSet<std::string> InterpreterImpl::selectTransitions(const std::string& event) {
	Arabica::XPath::NodeSet<std::string> enabledTransitions;
	
	NodeSet<std::string> states;
	for (unsigned int i = 0; i < _configuration.size(); i++) {
		if (isAtomic(Element<std::string>(_configuration[i])))
			states.push_back(_configuration[i]);
	}
	states.to_document_order();
	
	unsigned int index = 0;
	while(states.size() > index) {
		NodeSet<std::string> transitions = filterChildElements(_nsInfo.xmlNSPrefix + "transition", states[index]);
		for (unsigned int k = 0; k < transitions.size(); k++) {
			if (isEnabledTransition(Element<std::string>(transitions[k]), event)) {
				enabledTransitions.push_back(transitions[k]);
				goto LOOP;
			}
		}
		{
			Node<std::string> parent = states[index].getParentNode();
			if (parent) {
				states.push_back(parent);
			}
		}
	LOOP:
		index++;
	}
	
	enabledTransitions = removeConflictingTransitions(enabledTransitions);
	return enabledTransitions;
}
	
	
Arabica::XPath::NodeSet<std::string> InterpreterImpl::selectEventlessTransitions() {
	Arabica::XPath::NodeSet<std::string> enabledTransitions;
	
	NodeSet<std::string> states;
	for (unsigned int i = 0; i < _configuration.size(); i++) {
		if (isAtomic(Element<std::string>(_configuration[i])))
			states.push_back(_configuration[i]);
	}
	states.to_document_order();
	
#if 0
	std::cout << "Atomic States: ";
	for (int i = 0; i < atomicStates.size(); i++) {
		std::cout << ATTR(atomicStates[i], "id") << ", ";
	}
	std::cout << std::endl;
#endif
	
	unsigned int index = 0;
	while(states.size() > index) {
		bool foundTransition = false;
		NodeSet<std::string> transitions = filterChildElements(_nsInfo.xmlNSPrefix + "transition", states[index]);
		for (unsigned int k = 0; k < transitions.size(); k++) {
			Element<std::string> transElem(transitions[k]);
			if (!HAS_ATTR(transElem, "event") && hasConditionMatch(transElem)) {
				enabledTransitions.push_back(transitions[k]);
				foundTransition = true;
				goto LOOP;
			}
		}
		if (!foundTransition) {
			Node<std::string> parent = states[index].getParentNode();
			if (parent) {
				states.push_back(parent);
			}
		}
	LOOP:
		index++;
	}
	
#if 0
	std::cout << "Enabled eventless transitions: " << std::endl;
	for (int i = 0; i < enabledTransitions.size(); i++) {
		std::cout << enabledTransitions[i] << std::endl << "----" << std::endl;
	}
	std::cout << std::endl;
#endif
	
	enabledTransitions = removeConflictingTransitions(enabledTransitions);
	return enabledTransitions;
}


bool InterpreterImpl::isEnabledTransition(const Element<std::string>& transition, const std::string& event) {
	std::string eventName;
	if (HAS_ATTR(transition, "event")) {
		eventName = ATTR(transition, "event");
	} else if(HAS_ATTR(transition, "eventexpr")) {
		if (_dataModel) {
			eventName = _dataModel.evalAsString(ATTR(transition, "eventexpr"));
		} else {
			LOG(ERROR) << "Transition has eventexpr attribute with no datamodel defined";
			return false;
		}
	} else {
		return false;
	}
	
	std::list<std::string> eventNames = tokenizeIdRefs(eventName);
	std::list<std::string>::iterator eventIter = eventNames.begin();
	while(eventIter != eventNames.end()) {
		if(nameMatch(*eventIter, event) && hasConditionMatch(transition)) {
			return true;
		}
		eventIter++;
	}
	return false;
}

	
InterpreterState InterpreterImpl::getInterpreterState() {
	return _state;
}

void InterpreterImpl::setInterpreterState(InterpreterState newState) {
	switch (_state) {
	case USCXML_INSTANTIATED:
		if (VALID_FROM_INSTANTIATED(newState))
			break;
		assert(false);
		break;
	case USCXML_MICROSTEPPED:
		if (VALID_FROM_MICROSTEPPED(newState))
			break;
		assert(false);
		break;
	case USCXML_MACROSTEPPED:
		if (VALID_FROM_MACROSTEPPED(newState))
			break;
		assert(false);
		break;
	case USCXML_IDLE:
		if (VALID_FROM_IDLE(newState))
			break;
		assert(false);
		break;
	case USCXML_FINISHED:
		if (VALID_FROM_FINISHED(newState))
			break;
		assert(false);
		break;
	case USCXML_DESTROYED:
		assert(false);
		break;

	default:
		break;
	}

	_state = newState;
}

bool InterpreterImpl::runOnMainThread(int fps, bool blocking) {
	if (_state == USCXML_FINISHED || _state == USCXML_DESTROYED || !_isStarted)
		return false;

	if (fps > 0) {
		uint64_t nextRun = _lastRunOnMainThread + (1000 / fps);
		if (blocking) {
			while(nextRun > tthread::timeStamp()) {
				tthread::this_thread::sleep_for(tthread::chrono::milliseconds(nextRun - tthread::timeStamp()));
			}
		} else {
			return true;
		}
	}

	tthread::lock_guard<tthread::recursive_mutex> lock(_mutex);
	_lastRunOnMainThread = tthread::timeStamp();

	{
		tthread::lock_guard<tthread::recursive_mutex> lock(_pluginMutex);
		std::map<std::string, IOProcessor>::iterator ioProcessorIter = _ioProcessors.begin();
		while(ioProcessorIter != _ioProcessors.end()) {
			ioProcessorIter->second.runOnMainThread();
			ioProcessorIter++;
		}
		std::map<std::string, Invoker>::iterator invokerIter = _invokers.begin();
		while(invokerIter != _invokers.end()) {
			invokerIter->second.runOnMainThread();
			invokerIter++;
		}
	}
	return (_thread != NULL);
}

void InterpreterImpl::reset() {
	tthread::lock_guard<tthread::recursive_mutex> lock(_mutex);

	_externalQueue.clear();
	_internalQueue.clear();
	_historyValue.clear();

	_currEvent = Event();
	_alreadyEntered = NodeSet<std::string>();
	_configuration = NodeSet<std::string>();
	_topLevelFinalReached = false;
	_isInitialized = false;
	_stable = false;

	setInterpreterState(USCXML_INSTANTIATED);
}

std::list<InterpreterIssue> InterpreterImpl::validate() {
	return InterpreterIssue::forInterpreter(this);
}

std::ostream& operator<< (std::ostream& os, const InterpreterIssue& issue) {
	switch (issue.severity) {
		case InterpreterIssue::USCXML_ISSUE_FATAL:
			os << "Issue (FATAL) ";
			break;
		case InterpreterIssue::USCXML_ISSUE_WARNING:
			os << "Issue (WARNING) ";
			break;
		case InterpreterIssue::USCXML_ISSUE_INFO:
			os << "Issue (INFO) ";
			break;
		default:
			break;
	}
	
	if (issue.xPath.size() > 0) {
		os << "at " << issue.xPath << ": ";
	} else {
		os << ": ";
	}
	os << issue.message;
	return os;
}

void InterpreterImpl::setupDOM() {
	if (_domIsSetup)
		return;

	if (!_document) {
		ERROR_PLATFORM_THROW("Interpreter has no DOM");
	}

	// find scxml element
	if (!_scxml) {
		NodeList<std::string> scxmls;
		if (_nsInfo.nsURL.size() == 0) {
			scxmls = _document.getElementsByTagName("scxml");
		} else {
			scxmls = _document.getElementsByTagNameNS(_nsInfo.nsURL, "scxml");
		}

		if (scxmls.getLength() == 0) {
			ERROR_PLATFORM_THROW("Cannot find SCXML element in DOM");
		}

		_scxml = (Arabica::DOM::Element<std::string>)scxmls.item(0);
	}
	
	if (_nsInfo.getNSContext() != NULL)
		_xpath.setNamespaceContext(*_nsInfo.getNSContext());

	// normalize document
	// TODO: Resolve XML includes

#if 0
	// make sure every state has an id
	Arabica::XPath::NodeSet<std::string> states;
	states.push_back(_xpath.evaluate("//" + _nsInfo.xpathPrefix + "state", _scxml).asNodeSet());
	states.push_back(_xpath.evaluate("//" + _nsInfo.xpathPrefix + "final", _scxml).asNodeSet());
	states.push_back(_xpath.evaluate("//" + _nsInfo.xpathPrefix + "history", _scxml).asNodeSet());
	for (int i = 0; i < states.size(); i++) {
		Arabica::DOM::Element<std::string> stateElem = Arabica::DOM::Element<std::string>(states[i]);
		if (!stateElem.hasAttribute("id")) {
			stateElem.setAttribute("id", UUID::getUUID());
		}
	}
#endif

	// make sure every invoke has an idlocation or id
	Arabica::XPath::NodeSet<std::string> invokes = _xpath.evaluate("//" + _nsInfo.xpathPrefix + "invoke", _scxml).asNodeSet();
	for (int i = 0; i < invokes.size(); i++) {
		Arabica::DOM::Element<std::string> invokeElem = Arabica::DOM::Element<std::string>(invokes[i]);
		if (!invokeElem.hasAttribute("id") && !invokeElem.hasAttribute("idlocation")) {
			invokeElem.setAttribute("id", UUID::getUUID());
		}
	}

#if 0
	// add an id to the scxml element
	if (!_scxml.hasAttribute("id")) {
		_scxml.setAttribute("id", UUID::getUUID());
	}
#endif

	// register for dom events to manage cached states
	Arabica::DOM::Events::EventTarget<std::string> eventTarget(_scxml);
	eventTarget.addEventListener("DOMNodeInserted", _domEventListener, true);
	eventTarget.addEventListener("DOMNodeRemoved", _domEventListener, true);
	eventTarget.addEventListener("DOMSubtreeModified", _domEventListener, true);
	_domIsSetup = true;
}

void InterpreterImpl::init() {
	// make sure we have a factory if none was set before
	if (_factory == NULL)
		_factory = Factory::getInstance();

	// setup and normalize DOM
	setupDOM();

	// get our name or generate as UUID
	if (_name.length() == 0)
		_name = (HAS_ATTR(_scxml, "name") ? ATTR(_scxml, "name") : UUID::getUUID());

	// setup event queue for delayed send
	if (!_sendQueue) {
		_sendQueue = new DelayedEventQueue();
		_sendQueue->start();
	}

	// start io processoes
	setupIOProcessors();

	// instantiate datamodel if not explicitly set
	if (!_dataModel) {
		if (HAS_ATTR(_scxml, "datamodel")) {
			// might throw
			_dataModel = _factory->createDataModel(ATTR(_scxml, "datamodel"), this);
		} else {
			_dataModel = _factory->createDataModel("null", this);
		}
	}

	_dataModel.assign("_x.args", _cmdLineOptions);

//	_running = true;
#if VERBOSE
	std::cout << "running " << this << std::endl;
#endif

	_binding = (HAS_ATTR(_scxml, "binding") && iequals(ATTR(_scxml, "binding"), "late") ? LATE : EARLY);

	if (_binding == EARLY) {
		// initialize all data elements
		NodeSet<std::string> dataElems = _xpath.evaluate("//" + _nsInfo.xpathPrefix + "data", _scxml).asNodeSet();
		for (unsigned int i = 0; i < dataElems.size(); i++) {
			// do not process data elements of nested documents from invokers
			if (!getAncestorElement(dataElems[i], _nsInfo.xmlNSPrefix + "invoke"))
				if (dataElems[i].getNodeType() == Node_base::ELEMENT_NODE) {
					initializeData(Element<std::string>(dataElems[i]));
				}
		}
	} else {
		// initialize current data elements
		NodeSet<std::string> topDataElems = filterChildElements(_nsInfo.xmlNSPrefix + "data", filterChildElements(_nsInfo.xmlNSPrefix + "datamodel", _scxml));
		for (unsigned int i = 0; i < topDataElems.size(); i++) {
			if (topDataElems[i].getNodeType() == Node_base::ELEMENT_NODE)
				initializeData(Element<std::string>(topDataElems[i]));
		}
	}

	// executeGlobalScriptElements
	NodeSet<std::string> globalScriptElems = filterChildElements(_nsInfo.xmlNSPrefix + "script", _scxml);
	for (unsigned int i = 0; i < globalScriptElems.size(); i++) {
		executeContent(Element<std::string>(globalScriptElems[i]));
	}

	_isInitialized = true;
	_stable = false;
}

/**
 * Called with a single data element from the topmost datamodel element.
 */
void InterpreterImpl::initializeData(const Element<std::string>& data) {

	/// test 226/240 - initialize from invoke request
	if (_invokeReq.params.find(ATTR(data, "id")) != _invokeReq.params.end()) {
		try {
			_dataModel.init(ATTR(data, "id"), _invokeReq.params.find(ATTR(data, "id"))->second);
		} catch (Event e) {
			LOG(ERROR) << "Syntax error when initializing data " << DOMUtils::xPathForNode(data) << " from parameters:" << std::endl << e << std::endl;
			receiveInternal(e);
		}
		return;
	}
	if (_invokeReq.namelist.find(ATTR(data, "id")) != _invokeReq.namelist.end()) {
		try {
			_dataModel.init(ATTR(data, "id"), _invokeReq.namelist.find(ATTR(data, "id"))->second);
		} catch (Event e) {
			LOG(ERROR) << "Syntax error when initializing data " << DOMUtils::xPathForNode(data) << " from namelist:" << std::endl << e << std::endl;
			receiveInternal(e);
		}
		return;
	}

	try {
		Arabica::DOM::Node<std::string> dom;
		std::string text;
		processDOMorText(data, dom, text);
		_dataModel.init(data, dom, text);
	} catch (Event e) {
		LOG(ERROR) << "Syntax error when initializing data " << DOMUtils::xPathForNode(data) << ":" << std::endl << e << std::endl;
		receiveInternal(e);
	}
}

void InterpreterImpl::receiveInternal(const Event& event) {
#if VERBOSE
	std::cout << _name << " receiveInternal: " << event.name << std::endl;
#endif
	_internalQueue.push_back(event);
//	_condVar.notify_all();
}

void InterpreterImpl::receive(const Event& event, bool toFront)   {
#if VERBOSE
	std::cout << _name << " receive: " << event.name << std::endl;
#endif
	if (toFront) {
		_externalQueue.push_front(event);
	} else {
		_externalQueue.push(event);
	}
	_condVar.notify_all();
}

void InterpreterImpl::internalDoneSend(const Arabica::DOM::Element<std::string>& state) {
	if (!isState(state))
		return;

	if (parentIsScxmlState(state))
		return;

	Event event;

	Arabica::XPath::NodeSet<std::string> doneDatas = filterChildElements(_nsInfo.xmlNSPrefix + "donedata", state);
	if (doneDatas.size() > 0) {
		// only process first donedata element
		Arabica::DOM::Element<std::string> doneData = Element<std::string>(doneDatas[0]);
		processParamChilds(doneData, event.params);
		Arabica::XPath::NodeSet<std::string> contents = filterChildElements(_nsInfo.xmlNSPrefix + "content", doneDatas[0]);
		if (contents.size() > 1)
			LOG(ERROR) << "Only a single content element is allowed for send elements - using first one";
		if (contents.size() > 0) {
			std::string expr;
			processContentElement(Element<std::string>(contents[0]), event.dom, event.content, expr);
			if (expr.length() > 0) {
				try {
					event.content =_dataModel.evalAsString(expr);
				} catch (Event e) {
					e.name = "error.execution";
					e.dom = contents[0];
					receiveInternal(e);
				}
			}
		}
	}

	event.name = "done.state." + ATTR_CAST(state.getParentNode(), "id"); // parent?!
	receiveInternal(event);

}

void InterpreterImpl::processContentElement(const Arabica::DOM::Element<std::string>& content,
        Arabica::DOM::Node<std::string>& dom,
        std::string& text,
        std::string& expr) {
	if (HAS_ATTR(content, "expr")) {
		expr = ATTR(content, "expr");
	} else if (content.hasChildNodes() || HAS_ATTR(content, "src") || HAS_ATTR(content, "srcexpr")) {
		processDOMorText(content, dom, text);
	} else {
		LOG(ERROR) << "content element does not specify any content.";
	}
}

void InterpreterImpl::processDOMorText(const Arabica::DOM::Element<std::string>& element,
                                       Arabica::DOM::Node<std::string>& dom,
                                       std::string& text) {
	// do we need to download?
	if (HAS_ATTR(element, "src") ||
	        (HAS_ATTR(element, "srcexpr"))) {
		std::stringstream srcContent;
		URL sourceURL(HAS_ATTR(element, "srcexpr") ? _dataModel.evalAsString(ATTR(element, "srcexpr")) : ATTR(element, "src"));
		if (!sourceURL.toAbsolute(_baseURI)) {
			LOG(ERROR) << LOCALNAME(element) << " element has relative src or srcexpr URI with no baseURI set.";
			return;
		}
		if (_cachedURLs.find(sourceURL.asString()) != _cachedURLs.end() && false) {
			srcContent << _cachedURLs[sourceURL.asString()];
		} else {
			srcContent << sourceURL;
			if (sourceURL.downloadFailed()) {
				LOG(ERROR) << LOCALNAME(element) << " source cannot be downloaded";
				return;
			}
			_cachedURLs[sourceURL.asString()] = sourceURL;
		}
		if (srcContent.str().length() > 0) {
			// try to parse as XML
			NameSpacingParser parser;
			std::stringstream* ss = new std::stringstream();
			(*ss) << srcContent.str();
			std::auto_ptr<std::istream> ssPtr(ss);
			Arabica::SAX::InputSource<std::string> inputSource;
			inputSource.setByteStream(ssPtr);

			if (parser.parse(inputSource) && parser.getDocument()) {
				Document<std::string> doc = parser.getDocument();
				dom = doc.getDocumentElement();
				return;
			} else {
				text = srcContent.str();
				return;
			}
		}
	}

	if (!element.hasChildNodes())
		return;

	/**
	 * Figure out whether the given element contains text, has one child or many childs
	 */
	bool hasTextContent = false;
	bool hasOneChild = false;
	Node<std::string> theOneChild;
	bool hasManyChilds = false;

	Node<std::string> child = element.getFirstChild();
	while (child) {
//		std::cout << child.getNodeType() << std::endl;
		if (child.getNodeType() == Node_base::TEXT_NODE ||
		        child.getNodeType() == Node_base::CDATA_SECTION_NODE) {
			std::string trimmed = child.getNodeValue();
			boost::trim(trimmed);
			if (trimmed.length() > 0) {
				hasTextContent = true;
			}
		} else {
			if (hasOneChild) {
				hasManyChilds = true;
				hasOneChild = false;
				break;
			}
			hasOneChild = true;
			theOneChild = child;
		}
		child = child.getNextSibling();
	}

	if (hasOneChild) {
		// if we have a single child, it will be the content of the dom
		dom = theOneChild;
	} else if (hasManyChilds) {
		// if we have multiple childs
		dom = element;
	} else if(hasTextContent) {
		child = element.getFirstChild();
		while(child) {
			if ((child.getNodeType() == Node_base::TEXT_NODE || child.getNodeType() == Node_base::CDATA_SECTION_NODE)) {
				text += child.getNodeValue();
			}
			child = child.getNextSibling();
		}
		// updated test 179 - conflicts with test 562
//		text = _dataModel.evalAsString(text);
	} else {
		LOG(ERROR) << LOCALNAME(element) << " has neither text nor element children.";
	}
}

void InterpreterImpl::processParamChilds(const Arabica::DOM::Element<std::string>& element, std::multimap<std::string, Data>& params) {
	NodeSet<std::string> paramElems = filterChildElements(_nsInfo.xmlNSPrefix + "param", element);
	for (int i = 0; i < paramElems.size(); i++) {
		try {
			Element<std::string> paramElem = Element<std::string>(paramElems[i]);
			if (!HAS_ATTR(paramElem, "name")) {
				LOG(ERROR) << "param element is missing name attribute";
				continue;
			}
			Data paramValue;
			if (HAS_ATTR(paramElem, "expr")) {
				paramValue = _dataModel.getStringAsData(ATTR(paramElem, "expr"));
			} else if(HAS_ATTR(paramElem, "location")) {
				paramValue = _dataModel.getStringAsData(ATTR(paramElem, "location"));
			} else {
				LOG(ERROR) << "param element is missing expr or location or no datamodel is specified";
				continue;
			}
			std::string paramKey = ATTR(paramElem, "name");
			params.insert(std::make_pair(paramKey, paramValue));
		} catch(Event e) {
			LOG(ERROR) << "Syntax error while processing params " << DOMUtils::xPathForNode(paramElems[i]) << ":" << std::endl << e << std::endl;
			// test 343
			std::multimap<std::string, Data>::iterator paramIter = params.begin();
			while(paramIter != params.end()) {
				params.erase(paramIter++);
			}
			e.name = "error.execution";
			receiveInternal(e);
			break;
		}
	}
}

void InterpreterImpl::send(const Arabica::DOM::Element<std::string>& element) {
	SendRequest sendReq;
	// test 331
	sendReq.Event::eventType = Event::EXTERNAL;
	try {
		// event
		if (HAS_ATTR(element, "eventexpr")) {
			sendReq.name = _dataModel.evalAsString(ATTR(element, "eventexpr"));
		} else if (HAS_ATTR(element, "event")) {
			sendReq.name = ATTR(element, "event");
		}
	} catch (Event e) {
		LOG(ERROR) << "Syntax error in send element eventexpr " << DOMUtils::xPathForNode(element) << ":" << std::endl << e << std::endl;
		return;
	}
	try {
		// target
		if (HAS_ATTR(element, "targetexpr")) {
			sendReq.target = _dataModel.evalAsString(ATTR(element, "targetexpr"));
		} else if (HAS_ATTR(element, "target")) {
			sendReq.target = ATTR(element, "target");
		}
	} catch (Event e) {
		LOG(ERROR) << "Syntax error in send element " << DOMUtils::xPathForNode(element) << " targetexpr:" << std::endl << e << std::endl;
		return;
	}
	try {
		// type
		if (HAS_ATTR(element, "typeexpr")) {
			sendReq.type = _dataModel.evalAsString(ATTR(element, "typeexpr"));
		} else if (HAS_ATTR(element, "type")) {
			sendReq.type = ATTR(element, "type");
		}
	} catch (Event e) {
		LOG(ERROR) << "Syntax error in send element " << DOMUtils::xPathForNode(element) << " typeexpr:" << std::endl << e << std::endl;
		return;
	}
	try {
		// id
		if (HAS_ATTR(element, "id")) {
			sendReq.sendid = ATTR(element, "id");
		} else {
			/*
			 * The ids for <send> and <invoke> are subtly different. In a conformant
			 * SCXML document, they must be unique within the session, but in the case
			 * where the author does not provide them, the processor must generate a
			 * new unique ID not at load time but each time the element is executed.
			 * Furthermore the attribute 'idlocation' can be used to capture this
			 * automatically generated id. Finally note that the automatically generated
			 * id for <invoke> has a special format. See 6.4.1 Attribute Details for
			 * details. The SCXML processor may generate all other ids in any format,
			 * as long as they are unique.
			 */

			/**
			 *
			 * If 'idlocation' is present, the SCXML Processor must generate an id when
			 * the parent <send> element is evaluated and store it in this location.
			 * See 3.14 IDs for details.
			 *
			 */
			sendReq.sendid = ATTR(getParentState(element), "id") + "." + UUID::getUUID();
			if (HAS_ATTR(element, "idlocation")) {
				_dataModel.assign(ATTR(element, "idlocation"), Data("'" + sendReq.sendid + "'", Data::INTERPRETED));
			} else {
				sendReq.hideSendId = true;
			}
		}
	} catch (Event e) {
		LOG(ERROR) << "Syntax error in send element " << DOMUtils::xPathForNode(element) << " idlocation:" << std::endl << e << std::endl;
		return;
	}

	try {
		// delay
		std::string delay;
		sendReq.delayMs = 0;
		if (HAS_ATTR(element, "delayexpr")) {
			delay = _dataModel.evalAsString(ATTR(element, "delayexpr"));
		} else if (HAS_ATTR(element, "delay")) {
			delay = ATTR(element, "delay");
		}
		if (delay.size() > 0) {
			boost::trim(delay);

			NumAttr delayAttr(delay);
			if (iequals(delayAttr.unit, "ms")) {
				sendReq.delayMs = strTo<uint32_t>(delayAttr.value);
			} else if (iequals(delayAttr.unit, "s")) {
				sendReq.delayMs = strTo<uint32_t>(delayAttr.value);
				sendReq.delayMs *= 1000;
			} else {
				LOG(ERROR) << "Cannot make sense of delay value " << delay << ": does not end in 's' or 'ms'";
			}
		}
	} catch (Event e) {
		LOG(ERROR) << "Syntax error in send element " << DOMUtils::xPathForNode(element) << " delayexpr:" << std::endl << e << std::endl;
		return;
	}

	try {
		// namelist
		if (HAS_ATTR(element, "namelist")) {
			std::list<std::string> names = tokenizeIdRefs(ATTR(element, "namelist"));
			for (std::list<std::string>::const_iterator nameIter = names.begin(); nameIter != names.end(); nameIter++) {
				if (!_dataModel.isLocation(*nameIter)) {
					LOG(ERROR) << "Error in send element " << DOMUtils::xPathForNode(element) << " namelist:" << std::endl << "'" << *nameIter << "' is not a location expression" << std::endl;
					ERROR_EXECUTION2(err, "Location expression '" + *nameIter + "' in namelist is invalid", element);
					receiveInternal(err);
					return;
				}
				Data namelistValue = _dataModel.getStringAsData(*nameIter);
				sendReq.namelist[*nameIter] = namelistValue;
				sendReq.data.compound[*nameIter] = namelistValue; // this is questionable
			}
		}
	} catch (Event e) {
		LOG(ERROR) << "Syntax error in send element " << DOMUtils::xPathForNode(element) << " namelist:" << std::endl << e << std::endl;
		return;
	}

	try {
		// params
		processParamChilds(element, sendReq.params);
	} catch (Event e) {
		LOG(ERROR) << "Syntax error in send element " << DOMUtils::xPathForNode(element) << " param expr:" << std::endl << e << std::endl;
		return;
	}
	try {
		// content
		NodeSet<std::string> contents = filterChildElements(_nsInfo.xmlNSPrefix + "content", element);
		if (contents.size() > 1)
			LOG(ERROR) << "Only a single content element is allowed for send elements " << DOMUtils::xPathForNode(element) << " - using first one";
		if (contents.size() > 0) {
			std::string expr;
			processContentElement(Element<std::string>(contents[0]), sendReq.dom, sendReq.content, expr);
			if (expr.length() > 0) {
				try {
					sendReq.data = _dataModel.getStringAsData(expr);
				} catch (Event e) {
					e.name = "error.execution";
					receiveInternal(e);
					return;
				}
				// set as content if it's only an atom
				if (sendReq.data.atom.length() > 0) {
					sendReq.content = sendReq.data.atom;
				}
			} else if (sendReq.content.length() > 0) {
				sendReq.data = Data::fromJSON(sendReq.content);
			}
		}
	} catch (Event e) {
		LOG(ERROR) << "Syntax error in send element " << DOMUtils::xPathForNode(element) << " content:" << std::endl << e << std::endl;
		return;
	}

	if (sendReq.dom) {
		std::stringstream ss;
		ss << sendReq.dom;
		sendReq.xml = ss.str();
		_dataModel.replaceExpressions(sendReq.xml);
	}

	assert(_sendIds.find(sendReq.sendid) == _sendIds.end());
	_sendIds[sendReq.sendid] = std::make_pair(this, sendReq);
	if (sendReq.delayMs > 0) {
		_sendQueue->addEvent(sendReq.sendid, InterpreterImpl::delayedSend, sendReq.delayMs, &_sendIds[sendReq.sendid]);
	} else {
		delayedSend(&_sendIds[sendReq.sendid], sendReq.name);
	}
}

void InterpreterImpl::delayedSend(void* userdata, std::string eventName) {
	std::pair<InterpreterImpl*, SendRequest>* data = (std::pair<InterpreterImpl*, SendRequest>*)(userdata);

	InterpreterImpl* INSTANCE = data->first;
	SendRequest sendReq = data->second;

	/**
	 * If neither the 'type' nor the 'typeexpr' is defined, the SCXML Processor
	 * must assume the default value of http://www.w3.org/TR/scxml/#SCXMLEventProcessor
	 */
	if (sendReq.type.length() == 0)
		sendReq.type = "http://www.w3.org/TR/scxml/#SCXMLEventProcessor";

	IOProcessor ioProc = INSTANCE->getIOProcessor(sendReq.type);
	if (ioProc) {
		try {
			ioProc.send(sendReq);
		} catch(Event e) {
			throw e;
		} catch (const std::exception &e) {
			LOG(ERROR) << "Exception caught while sending event to ioprocessor " << sendReq.type << ":" << e.what();
		} catch(...) {
			LOG(ERROR) << "Exception caught while sending event to ioprocessor " << sendReq.type;
		}
	} else {
		/**
		 * If the SCXML Processor does not support the type that is specified, it
		 * must place the event error.execution on the internal event queue.
		 */
		ERROR_EXECUTION(exc, "Unsupported type '" + sendReq.type + "' with send element");
		INSTANCE->receiveInternal(exc);
	}

	assert(INSTANCE->_sendIds.find(sendReq.sendid) != INSTANCE->_sendIds.end());
	INSTANCE->_sendIds.erase(sendReq.sendid);
}

void InterpreterImpl::invoke(const Arabica::DOM::Element<std::string>& element) {
	InvokeRequest invokeReq;
	invokeReq.Event::eventType = Event::EXTERNAL;
	try {
		// type
		if (HAS_ATTR(element, "typeexpr")) {
			invokeReq.type = _dataModel.evalAsString(ATTR(element, "typeexpr"));
		} else if (HAS_ATTR(element, "type")) {
			invokeReq.type = ATTR(element, "type");
		}

		// src
		std::string source;
		if (HAS_ATTR(element, "srcexpr")) {
			source = _dataModel.evalAsString(ATTR(element, "srcexpr"));
		} else if (HAS_ATTR(element, "src")) {
			source = ATTR(element, "src");
		}
		if (source.length() > 0) {
			URL srcURI(source);
			if (!srcURI.toAbsolute(_baseURI)) {
				LOG(ERROR) << "invoke element has relative src URI with no baseURI set.";
				return;
			}
			invokeReq.src = srcURI.asString();
		}

		// id
		try {
			if (HAS_ATTR(element, "id")) {
				invokeReq.invokeid = ATTR(element, "id");
			} else {
				invokeReq.invokeid = ATTR(getParentState(element), "id") + "." + UUID::getUUID();
				if (HAS_ATTR(element, "idlocation")) {
					_dataModel.assign(ATTR(element, "idlocation"), Data("'" + invokeReq.invokeid + "'", Data::INTERPRETED));
				}
			}
		} catch (Event e) {
			LOG(ERROR) << "Syntax error in invoke element idlocation:" << std::endl << e << std::endl;
			return;
		}

		// namelist
		if (HAS_ATTR(element, "namelist")) {
			std::list<std::string> names = tokenizeIdRefs(ATTR(element, "namelist"));
			for (std::list<std::string>::const_iterator nameIter = names.begin(); nameIter != names.end(); nameIter++) {
				if (!_dataModel.isLocation(*nameIter)) {
					LOG(ERROR) << "Error in send element " << DOMUtils::xPathForNode(element) << " namelist:" << std::endl << "'" << *nameIter << "' is not a location expression" << std::endl;
					ERROR_EXECUTION2(err, "Location expression '" + *nameIter + "' in namelist is invalid", element);
					receiveInternal(err);
					return;
				}
				Data namelistValue = _dataModel.getStringAsData(*nameIter);
				invokeReq.namelist[*nameIter] = namelistValue;
				invokeReq.data.compound[*nameIter] = namelistValue;
			}
		}

		// autoforward
		if (HAS_ATTR(element, "autoforward")) {
			if (iequals(ATTR(element, "autoforward"), "true")) {
				invokeReq.autoForward = true;
			}
		} else {
			invokeReq.autoForward = false;
		}

		// params
		processParamChilds(element, invokeReq.params);

		// content
		try {
			NodeSet<std::string> contents = filterChildElements(_nsInfo.xmlNSPrefix + "content", element);
			if (contents.size() > 1)
				LOG(ERROR) << "Only a single content element is allowed for send elements - using first one";
			if (contents.size() > 0) {
				std::string expr;
				processContentElement(Element<std::string>(contents[0]), invokeReq.dom, invokeReq.content, expr);
				if (expr.length() > 0) {
					try {
						invokeReq.data =_dataModel.getStringAsData(expr);
					} catch (Event e) {
						e.name = "error.execution";
						e.dom = contents[0];
						receiveInternal(e);
					}
				} else if (invokeReq.content.length() > 0) {
					invokeReq.data = Data::fromJSON(invokeReq.content);
				}

			}
		} catch (Event e) {
			LOG(ERROR) << "Syntax error in send element " << DOMUtils::xPathForNode(element) << " content:" << std::endl << e << std::endl;
			return;
		}

		if (invokeReq.dom) {
			std::stringstream ss;
			ss << invokeReq.dom;
			invokeReq.xml = ss.str();
			_dataModel.replaceExpressions(invokeReq.xml);
		}

		// test 422
		if (invokeReq.type.size() == 0)
			invokeReq.type = "http://www.w3.org/TR/scxml/";

		Invoker invoker;
		// is there such an invoker already?
		if (_invokers.find(invokeReq.invokeid) != _invokers.end()) {
			invoker = _invokers[invokeReq.invokeid];
		} else {
			try {
				invoker = _factory->createInvoker(invokeReq.type, this);
				invoker.setInvokeId(invokeReq.invokeid);
				invoker.setInterpreter(this);
				_invokers[invokeReq.invokeid] = invoker;
			} catch (Event e) {
				receiveInternal(e);
			}
		}
		if (invoker) {
			tthread::lock_guard<tthread::recursive_mutex> lock(_pluginMutex);
			try {

				if (!invoker.getElement())
					invoker.setElement(Element<std::string>(element));

				if (invoker.getType().size() == 0)
					invoker.setType(invokeReq.type);

				try {

					USCXML_MONITOR_CALLBACK3(beforeInvoking, Arabica::DOM::Element<std::string>(element), invokeReq.invokeid);

					invoker.invoke(invokeReq);
					LOG(INFO) << "Added invoker " << invokeReq.type << " at " << invokeReq.invokeid;

					USCXML_MONITOR_CALLBACK3(afterInvoking, Arabica::DOM::Element<std::string>(element), invokeReq.invokeid)

					// this is out of draft but so useful to know when an invoker started
//					Event invSuccess;
//					invSuccess.name = "invoke.success." + invokeReq.invokeid;
//					receive(invSuccess);

				} catch(boost::bad_lexical_cast e) {
					LOG(ERROR) << "Exception caught while sending invoke request to invoker " << invokeReq.invokeid << ": " << e.what();
				} catch (const std::exception &e) {
					LOG(ERROR) << "Unknown exception caught while sending invoke request to invoker " << invokeReq.invokeid << ": " << e.what();
				} catch(...) {
					LOG(ERROR) << "Unknown exception caught while sending invoke request to invoker " << invokeReq.invokeid;
				}
				try {
//						_dataModel.assign("_invokers['" + invokeReq.invokeid + "']", invoker.getDataModelVariables());
				} catch (const std::exception &e) {
					LOG(ERROR) << "Exception caught while assigning datamodel variables from invoker " << invokeReq.invokeid << ": " << e.what();
				} catch(...) {
					LOG(ERROR) << "Exception caught while assigning datamodel variables from invoker " << invokeReq.invokeid;
				}
			} catch (...) {
				LOG(ERROR) << "Invoker " << invokeReq.type << " threw an exception";
			}
		} else {
			LOG(ERROR) << "No invoker known for type " << invokeReq.type;
		}

	} catch (Event e) {
		LOG(ERROR) << "Syntax error in invoke element " << DOMUtils::xPathForNode(element) << ":" << std::endl << e << std::endl;
	}
}

void InterpreterImpl::cancelInvoke(const Arabica::DOM::Element<std::string>& element) {
	std::string invokeId;
	if (HAS_ATTR(element, "idlocation")) {
		invokeId = _dataModel.evalAsString(ATTR(element, "idlocation"));
	} else if (HAS_ATTR(element, "id")) {
		invokeId = ATTR(element, "id");
	} else {
		assert(false);
	}
	if (_invokers.find(invokeId) != _invokers.end()) {
		LOG(INFO) << "Removed invoker at " << invokeId;
		try {
			_dataModel.assign("_invokers['" + invokeId + "']", Data(std::string("''"), Data::INTERPRETED));
		} catch (Event e) {
			LOG(ERROR) << "Syntax when removing invoker:" << std::endl << e << std::endl;
		}

		USCXML_MONITOR_CALLBACK3(beforeUninvoking, Element<std::string>(element), invokeId)
		_invokers[invokeId].uninvoke();

		/**
		 * This should not be necessary. Most invokers have their "clean-up" code in their
		 * destructor and not their uninvoke method - we need to refactor them all!
		 */
		if (_invokers[invokeId].deleteOnUninvoke())
			_invokers.erase(invokeId);

		USCXML_MONITOR_CALLBACK3(beforeUninvoking, Element<std::string>(element), invokeId)

	} else {
		LOG(ERROR) << "Cannot cancel invoke for id " << invokeId << ": no such invokation";
	}
	//receiveInternal(Event("done.invoke." + invokeId, Event::PLATFORM));
}

#if 1

// see: http://www.w3.org/TR/scxml/#EventDescriptors
bool InterpreterImpl::nameMatch(const std::string& eventDescs, const std::string& eventName) {
	if(eventDescs.length() == 0 || eventName.length() == 0)
		return false;

	// naive case of single descriptor and exact match
	if (iequals(eventDescs, eventName))
		return true;

	size_t start = 0;
	std::string eventDesc;
	for (int i = 0; i < eventDescs.size(); i++) {
		if (isspace(eventDescs[i])) {
			if (i > 0 && start < i - 1) {
				eventDesc = eventDescs.substr(start, i - start);
			}
			while(isspace(eventDescs[++i])); // skip whitespaces
			start = i;
		} else if (i + 1 == eventDescs.size()) {
			eventDesc = eventDescs.substr(start, i + 1 - start);
		}

		if (eventDesc.size() > 0) {
			// remove optional trailing .* for CCXML compatibility
			if (eventDesc.find("*", eventDesc.size() - 1) != std::string::npos)
				eventDesc = eventDesc.substr(0, eventDesc.size() - 1);
			if (eventDesc.find(".", eventDesc.size() - 1) != std::string::npos)
				eventDesc = eventDesc.substr(0, eventDesc.size() - 1);

			// was eventDesc the * wildcard
			if (eventDesc.size() == 0)
				return true;

			// eventDesc has to be a real prefix of event now and therefore shorter
			if (eventDesc.size() >= eventName.size())
				goto NEXT_DESC;

			// are they already equal?
			if (iequals(eventDesc, eventName))
				return true;

			if (eventName.find(eventDesc) == 0) {
				if (eventName.find(".", eventDesc.size()) == eventDesc.size())
					return true;
			}
NEXT_DESC:
			eventDesc = "";
		}
	}
	return false;
}

#else
// see: http://www.w3.org/TR/scxml/#EventDescriptors
bool InterpreterImpl::nameMatch(const std::string& transitionEvent, const std::string& event) {
	if(transitionEvent.length() == 0 || event.length() == 0)
		return false;

	// naive case of single descriptor and exact match
	if (iequals(transitionEvent, event))
		return true;

	boost::char_separator<char> sep(" ");
	boost::tokenizer<boost::char_separator<char> > tokens(transitionEvent, sep);
	boost::tokenizer<boost::char_separator<char> >::iterator tokenIter = tokens.begin();

	while(tokenIter != tokens.end()) {
		std::string eventDesc(*tokenIter++);

		// remove optional trailing .* for CCXML compatibility
		if (eventDesc.find("*", eventDesc.size() - 1) != std::string::npos)
			eventDesc = eventDesc.substr(0, eventDesc.size() - 1);
		if (eventDesc.find(".", eventDesc.size() - 1) != std::string::npos)
			eventDesc = eventDesc.substr(0, eventDesc.size() - 1);

		// was eventDesc the * wildcard
		if (eventDesc.size() == 0)
			return true;

		// are they already equal?
		if (iequals(eventDesc, event))
			return true;

		// eventDesc has to be a real prefix of event now and therefore shorter
		if (eventDesc.size() >= event.size())
			continue;

		// it is a prefix of the event name and event continues with .something
		if (boost::istarts_with(event, eventDesc))
//		if (eventDesc.compare(event.substr(0, eventDesc.size())) == 0)
			if (event.find(".", eventDesc.size()) == eventDesc.size())
				return true;
	}
	return false;
}
#endif

bool InterpreterImpl::hasConditionMatch(const Arabica::DOM::Element<std::string>& conditional) {
	if (HAS_ATTR(conditional, "cond") && ATTR(conditional, "cond").length() > 0) {
		try {
			return _dataModel.evalAsBool(conditional, ATTR(conditional, "cond"));
		} catch (Event e) {
			LOG(ERROR) << "Syntax error in cond attribute of " << TAGNAME(conditional) << " element " << DOMUtils::xPathForNode(conditional) << ":" << std::endl << e << std::endl;
			e.name = "error.execution";
			receiveInternal(e);
			return false;
		}
	}
	return true; // no condition is always true
}


void InterpreterImpl::executeContent(const NodeList<std::string>& content, bool rethrow) {
	for (unsigned int i = 0; i < content.getLength(); i++) {
		const Arabica::DOM::Node<std::string>& node = content.item(i);
		if (node.getNodeType() != Node_base::ELEMENT_NODE)
			continue;
		try {
			executeContent(Element<std::string>(node), true);
		}
		CATCH_AND_DISTRIBUTE2("Error when executing content", content.item(i));
	}
}

void InterpreterImpl::executeContent(const NodeSet<std::string>& content, bool rethrow) {
	for (unsigned int i = 0; i < content.size(); i++) {
		const Arabica::DOM::Node<std::string>& node = content[i];
		if (node.getNodeType() != Node_base::ELEMENT_NODE)
			continue;
		try {
			executeContent(Element<std::string>(node), true);
		}
		CATCH_AND_DISTRIBUTE2("Error when executing content", content[i]);
	}
}

void InterpreterImpl::executeContent(const Arabica::DOM::Element<std::string>& content, bool rethrow) {

	if (iequals(TAGNAME(content), _nsInfo.xmlNSPrefix + "onentry") ||
	        iequals(TAGNAME(content), _nsInfo.xmlNSPrefix + "onexit") ||
	        iequals(TAGNAME(content), _nsInfo.xmlNSPrefix + "finalize") ||
	        iequals(TAGNAME(content), _nsInfo.xmlNSPrefix + "transition")) {
		// --- CONVENIENCE LOOP --------------------------
		NodeList<std::string> executable = content.getChildNodes();
		for (int i = 0; i < executable.getLength(); i++) {
			const Arabica::DOM::Node<std::string>& childNode = executable.item(i);
			if (childNode.getNodeType() != Node_base::ELEMENT_NODE)
				continue;
			executeContent(Element<std::string>(childNode), rethrow);
		}
		return;
	}

	USCXML_MONITOR_CALLBACK2(beforeExecutingContent, Element<std::string>(content))

	if (false) {
	} else if (iequals(TAGNAME(content), _nsInfo.xmlNSPrefix + "raise")) {
		// --- RAISE --------------------------
#if 0
		if (HAS_ATTR(content, "event")) {
			receiveInternal(Event(ATTR(content, "event")));
		}
#else
		// Extension for donedata in flat documents - we need to send them internally - use raise
		if (HAS_ATTR(content, "event")) {
			Event raised(ATTR(content, "event"));
			try {
				// content
				processParamChilds(content, raised.params);
				NodeSet<std::string> contents = filterChildElements(_nsInfo.xmlNSPrefix + "content", content);
				if (contents.size() > 1)
					LOG(ERROR) << "Only a single content element is allowed for raise elements " << DOMUtils::xPathForNode(content) << " - using first one";
				if (contents.size() > 0) {
					std::string expr;
					processContentElement(Element<std::string>(contents[0]), raised.dom, raised.content, expr);
					if (expr.length() > 0) {
						try {
							raised.data = _dataModel.getStringAsData(expr);
						} catch (Event e) {
							e.name = "error.execution";
							receiveInternal(e);
						}
						// set as content if it's only an atom
						if (raised.data.atom.length() > 0) {
							raised.content = raised.data.atom;
						}
					} else if (raised.content.length() > 0) {
						raised.data = Data::fromJSON(raised.content);
					}
				}
			} catch (Event e) {
				LOG(ERROR) << "Syntax error in send element " << DOMUtils::xPathForNode(content) << " content:" << std::endl << raised << std::endl;
				return;
			}

			if (raised.dom) {
				std::stringstream ss;
				ss << raised.dom;
				raised.xml = ss.str();
				_dataModel.replaceExpressions(raised.xml);
			}
			receiveInternal(raised);
		}
#endif
	} else if (iequals(TAGNAME(content), _nsInfo.xmlNSPrefix + "if")) {
		// --- IF / ELSEIF / ELSE --------------
		Arabica::DOM::Element<std::string> ifElem = (Arabica::DOM::Element<std::string>)content;
#if 0
		if (HAS_ATTR(ifElem, "cond"))
			std::cout << ATTR(ifElem, "cond") << std::endl;
#endif
		/**
		 * A block is everything up to or between elseifs and else. Those element
		 * determine whether the block is true and its executable content executed.
		 */
		if (ifElem.hasChildNodes()) {
			bool blockIsTrue = hasConditionMatch(ifElem);
			NodeList<std::string> childs = ifElem.getChildNodes();
			for (unsigned int i = 0; i < childs.getLength(); i++) {
				if (childs.item(i).getNodeType() != Node_base::ELEMENT_NODE)
					continue;
				Element<std::string> childElem(childs.item(i));
				if (iequals(TAGNAME_CAST(childs.item(i)), _nsInfo.xmlNSPrefix + "elseif") ||
				        iequals(TAGNAME_CAST(childs.item(i)), _nsInfo.xmlNSPrefix + "else")) {
					if (blockIsTrue) {
						// last block was true, break here
						break;
					} else {
						// is this block the one to execute?
						blockIsTrue = hasConditionMatch(childElem);
					}
				} else {
					if (blockIsTrue) {
						executeContent(childElem, rethrow);
					}
				}
			}
		}
	} else if (iequals(TAGNAME(content), _nsInfo.xmlNSPrefix + "elseif")) {
		std::cerr << "Found single elsif to evaluate!" << std::endl;
	} else if (iequals(TAGNAME(content), _nsInfo.xmlNSPrefix + "else")) {
		std::cerr << "Found single else to evaluate!" << std::endl;
	} else if (iequals(TAGNAME(content), _nsInfo.xmlNSPrefix + "foreach")) {
		// --- FOREACH --------------------------
		if (HAS_ATTR(content, "array") && HAS_ATTR(content, "item")) {
			std::string array = ATTR(content, "array");
			std::string item = ATTR(content, "item");
			std::string index = (HAS_ATTR(content, "index") ? ATTR(content, "index") : "");
			uint32_t iterations = 0;
			try {
				iterations = _dataModel.getLength(array);
			}
			CATCH_AND_DISTRIBUTE2("Syntax error in array attribute of foreach element", content)
			try {
				_dataModel.pushContext(); // copy old and enter new context
//					if (!_dataModel.isDeclared(item)) {
//						_dataModel.init(item, Data());
//					}
				for (uint32_t iteration = 0; iteration < iterations; iteration++) {
					_dataModel.setForeach(item, array, index, iteration);
					if (content.hasChildNodes())
						// execute content and have exception rethrown to break foreach
						executeContent(content.getChildNodes(), rethrow);
				}
				_dataModel.popContext(); // leave stacked context
			}
			CATCH_AND_DISTRIBUTE2("Syntax error in foreach element", content)
		} else {
			LOG(ERROR) << "Expected array and item attributes with foreach element!" << std::endl;
		}
	} else if (iequals(TAGNAME(content), _nsInfo.xmlNSPrefix + "log")) {
		// --- LOG --------------------------
		Arabica::DOM::Element<std::string> logElem = (Arabica::DOM::Element<std::string>)content;
		if (logElem.hasAttribute("label"))
			std::cout << logElem.getAttribute("label") << ": ";
		if (logElem.hasAttribute("expr")) {
			try {
				std::cout << _dataModel.evalAsString(logElem.getAttribute("expr")) << std::endl;
			}
			CATCH_AND_DISTRIBUTE2("Syntax error in expr attribute of log element", content)
		} else {
			if (logElem.hasAttribute("label"))
				std::cout << std::endl;
		}
	} else if (iequals(TAGNAME(content), _nsInfo.xmlNSPrefix + "assign")) {
		// --- ASSIGN --------------------------
		if (HAS_ATTR(content, "location")) {
			try {
				if (!_dataModel.isDeclared(ATTR(content, "location"))) {
					// test 286, 331
					ERROR_EXECUTION_THROW("Assigning to undeclared location '" + ATTR(content, "location") + "' not allowed.");
				} else {
					Node<std::string> dom;
					std::string text;
					processDOMorText(content, dom, text);
					_dataModel.assign(Element<std::string>(content), dom, text);
				}
			}
			CATCH_AND_DISTRIBUTE2("Syntax error in attributes of assign element", content)
		}
	} else if (iequals(TAGNAME(content), _nsInfo.xmlNSPrefix + "validate")) {
		// --- VALIDATE --------------------------
		std::string location = (HAS_ATTR(content, "location") ? ATTR(content, "location") : "");
		std::string schema = (HAS_ATTR(content, "schema") ? ATTR(content, "schema") : "");
		_dataModel.validate(location, schema);
	} else if (iequals(TAGNAME(content), _nsInfo.xmlNSPrefix + "script")) {
		// --- SCRIPT --------------------------
		if (HAS_ATTR(content, "src")) {
			URL scriptUrl(ATTR(content, "src"));
			if (!scriptUrl.isAbsolute() && !_baseURI) {
				LOG(ERROR) << "script element has relative URI " << ATTR(content, "src") <<  " with no base URI set for interpreter";
				return;
			}

			if (!scriptUrl.toAbsolute(_baseURI)) {
				LOG(ERROR) << "Failed to convert relative script URI " << ATTR(content, "src") << " to absolute with base URI " << _baseURI.asString();
				return;
			}

			std::stringstream srcContent;
			try {
				if (_cachedURLs.find(scriptUrl.asString()) != _cachedURLs.end() && false) {
					srcContent << _cachedURLs[scriptUrl.asString()];
				} else {
					srcContent << scriptUrl;
					if (scriptUrl.downloadFailed()) {
						LOG(ERROR) << "script element source cannot be downloaded";
					}
					_cachedURLs[scriptUrl.asString()] = scriptUrl;
				}
			} catch (Event exception) {
				// script failed to download
				if (exception.name == "error.communication") {
					throw exception; // terminate test329, test301
				}
				receive(exception);
				return;
			}

			try {
				_dataModel.eval((Element<std::string>)content, srcContent.str());
			}
			CATCH_AND_DISTRIBUTE("Syntax error while executing script element from '" + ATTR(content, "src") + "':")
		} else {
			if (content.hasChildNodes()) {
				// search for the text node with the actual script
				std::string scriptContent;
				for (Node<std::string> child = content.getFirstChild(); child; child = child.getNextSibling()) {
					if (child.getNodeType() == Node_base::TEXT_NODE || child.getNodeType() == Node_base::CDATA_SECTION_NODE)
						scriptContent += child.getNodeValue();
				}
				if (scriptContent.size() > 0) {
					try {
						_dataModel.eval((Element<std::string>)content, scriptContent);
					}
					CATCH_AND_DISTRIBUTE2("Syntax error while executing script element", content)
				}
			}
		}
	} else if (iequals(TAGNAME(content), _nsInfo.xmlNSPrefix + "send")) {
		// --- SEND --------------------------
		try {
			send(content);
		}
		CATCH_AND_DISTRIBUTE2("Error while sending content", content)
	} else if (iequals(TAGNAME(content), _nsInfo.xmlNSPrefix + "cancel")) {
		// --- CANCEL --------------------------
		std::string sendId;
		try {
			if (HAS_ATTR(content, "sendidexpr")) {
				sendId = _dataModel.evalAsString(ATTR(content, "sendidexpr"));
			} else if(HAS_ATTR(content, "sendid")) {
				sendId = ATTR(content, "sendid");
			} else {
				LOG(ERROR) << "Expected sendidexpr or sendid attribute in cancel element";
				return;
			}
			_sendQueue->cancelEvent(sendId);

		}
		CATCH_AND_DISTRIBUTE2("Syntax error while executing cancel element", content)
	} else if (iequals(TAGNAME(content), _nsInfo.xmlNSPrefix + "invoke")) {
		// --- INVOKE --------------------------
	} else {
		// --- Custom Executable Content
		ExecutableContent execContent;
		if (_executableContent.find(content) == _executableContent.end()) {
			_executableContent[content] = _factory->createExecutableContent(content.getLocalName(), content.getNamespaceURI(), this);
		}
		execContent = _executableContent[content];

		execContent.enterElement(content);
		if (execContent.processChildren()) {
			NodeList<std::string> executable = content.getChildNodes();
			for (int i = 0; i < executable.getLength(); i++) {
				if (executable.item(i).getNodeType() != Node_base::ELEMENT_NODE)
					continue;
				executeContent(Element<std::string>(executable.item(i)), rethrow);
			}
		}
		execContent.exitElement(content);
	}

	USCXML_MONITOR_CALLBACK2(afterExecutingContent, Element<std::string>(content))

}

void InterpreterImpl::finalizeAndAutoForwardCurrentEvent() {
	for (std::map<std::string, Invoker>::iterator invokeIter = _invokers.begin();
	        invokeIter != _invokers.end();
	        invokeIter++) {
		if (iequals(invokeIter->first, _currEvent.invokeid)) {
			Arabica::XPath::NodeSet<std::string> finalizes = filterChildElements(_nsInfo.xmlNSPrefix + "finalize", invokeIter->second.getElement());
			for (int k = 0; k < finalizes.size(); k++) {
				Element<std::string> finalizeElem = Element<std::string>(finalizes[k]);
				executeContent(finalizeElem);
			}
		}
		if (HAS_ATTR(invokeIter->second.getElement(), "autoforward") && DOMUtils::attributeIsTrue(ATTR(invokeIter->second.getElement(), "autoforward"))) {
			try {
				// do not autoforward to invokers that send to #_parent from the SCXML IO Processor!
				// Yes do so, see test229!
				// if (!boost::equals(_currEvent.getOriginType(), "http://www.w3.org/TR/scxml/#SCXMLEventProcessor"))
				invokeIter->second.send(_currEvent);
			} catch (const std::exception &e) {
				LOG(ERROR) << "Exception caught while sending event to invoker " << invokeIter->first << ": " << e.what();
			} catch(...) {
				LOG(ERROR) << "Exception caught while sending event to invoker " << invokeIter->first;
			}
		}
	}
}

void InterpreterImpl::returnDoneEvent(const Arabica::DOM::Node<std::string>& state) {
//	std::cout << state << std::endl;
	if (_parentQueue != NULL) {
		Event done;
		done.name = "done.invoke." + _sessionId;
		_parentQueue->push(done);
	}
}

bool InterpreterImpl::parentIsScxmlState(const Arabica::DOM::Element<std::string>& state) {
	Arabica::DOM::Element<std::string> parentElem = (Arabica::DOM::Element<std::string>)state.getParentNode();
	if (iequals(TAGNAME(parentElem), _nsInfo.xmlNSPrefix + "scxml"))
		return true;
	return false;
}

bool InterpreterImpl::isInFinalState(const Arabica::DOM::Element<std::string>& state) {
	if (isCompound(state)) {
		Arabica::XPath::NodeSet<std::string> childs = getChildStates(state);
		for (int i = 0; i < childs.size(); i++) {
			if (isFinal(Element<std::string>(childs[i])) && isMember(childs[i], _configuration))
				return true;
		}
	} else if (isParallel(state)) {
		Arabica::XPath::NodeSet<std::string> childs = getChildStates(state);
		for (int i = 0; i < childs.size(); i++) {
			if (!isInFinalState(Element<std::string>(childs[i])))
				return false;
		}
		return true;
	}
	return false;
}

bool InterpreterImpl::isMember(const Arabica::DOM::Node<std::string>& node, const Arabica::XPath::NodeSet<std::string>& set) {
	for (int i = 0; i < set.size(); i++) {
		if (set[i] == node)
			return true;
	}
	return false;
}

Arabica::XPath::NodeSet<std::string> InterpreterImpl::getChildStates(const Arabica::DOM::Node<std::string>& state) {
	Arabica::XPath::NodeSet<std::string> childs;

	Arabica::DOM::NodeList<std::string> childElems = state.getChildNodes();
	for (int i = 0; i < childElems.getLength(); i++) {
		if (childElems.item(i).getNodeType() != Node_base::ELEMENT_NODE)
			continue;
		if (isState(Element<std::string>(childElems.item(i)))) {
			childs.push_back(childElems.item(i));
		}
	}
	return childs;
}

Arabica::XPath::NodeSet<std::string> InterpreterImpl::getChildStates(const Arabica::XPath::NodeSet<std::string>& states) {
	Arabica::XPath::NodeSet<std::string> childs;
	for (int i = 0; i < states.size(); i++) {
		childs.push_back(getChildStates(states[i]));
	}
	return childs;
}

Arabica::DOM::Element<std::string> InterpreterImpl::getParentState(const Arabica::DOM::Node<std::string>& element) {
	Arabica::DOM::Node<std::string> parent = element.getParentNode();
	while(parent && !isState(Element<std::string>(parent))) {
		parent = parent.getParentNode();
	}
	return Element<std::string>(parent);
}

Arabica::DOM::Node<std::string> InterpreterImpl::getAncestorElement(const Arabica::DOM::Node<std::string>& node, const std::string tagName) {
	Arabica::DOM::Node<std::string> parent = node.getParentNode();
	while(parent) {
		if (parent.getNodeType() == Node_base::ELEMENT_NODE &&
		        iequals(TAGNAME_CAST(parent), tagName)) {
			return parent;
		}
		parent = parent.getParentNode();
	}
	return Arabica::DOM::Node<std::string>();
}

/**
 See: http://www.w3.org/TR/scxml/#LCCA
 The Least Common Compound Ancestor is the <state> or <scxml> element s such that s is a proper ancestor
 of all states on stateList and no descendant of s has this property. Note that there is guaranteed to be
 such an element since the <scxml> wrapper element is a common ancestor of all states. Note also that since
 we are speaking of proper ancestor (parent or parent of a parent, etc.) the LCCA is never a member of stateList.
*/

Arabica::DOM::Node<std::string> InterpreterImpl::findLCCA(const Arabica::XPath::NodeSet<std::string>& states) {
#if 0
	std::cout << "findLCCA: ";
	for (int i = 0; i < states.size(); i++) {
		std::cout << ATTR(states[i], "id") << " - " << TAGNAME(states[i]) << ", ";
	}
	std::cout << std::endl << std::flush;
#endif

	Arabica::XPath::NodeSet<std::string> ancestors = getProperAncestors(states[0], Arabica::DOM::Node<std::string>());
//	ancestors.push_back(states[0]); // state[0] may already be the ancestor - bug in W3C spec?
	Arabica::DOM::Node<std::string> ancestor;
	for (int i = 0; i < ancestors.size(); i++) {
		if (!isCompound(Element<std::string>(ancestors[i])))
			continue;
		for (int j = 0; j < states.size(); j++) {
#if 0
			std::cout << "Checking " << TAGNAME(states[j]) << " and " << TAGNAME(ancestors[i]) << std::endl;
#endif
			if (!isDescendant(states[j], ancestors[i]) && (states[j] != ancestors[i]))
				goto NEXT_ANCESTOR;
		}
		ancestor = ancestors[i];
		break;
NEXT_ANCESTOR:
		;
	}

	// take uppermost root as ancestor
	if (!ancestor)
		ancestor = _scxml;
	assert(ancestor);
#if 0
	std::cout << " -> " << ATTR(ancestor, "id") << " " << ancestor.getLocalName() << std::endl;
#endif
	return ancestor;
}

Arabica::XPath::NodeSet<std::string> InterpreterImpl::getStates(const std::list<std::string>& stateIds) {
	Arabica::XPath::NodeSet<std::string> states;
	std::list<std::string>::const_iterator tokenIter = stateIds.begin();
	while(tokenIter != stateIds.end()) {
		states.push_back(getState(*tokenIter));
		tokenIter++;
	}
	return states;
}

Arabica::DOM::Element<std::string> InterpreterImpl::getState(const std::string& stateId) {

	if (_cachedStates.find(stateId) != _cachedStates.end()) {
		return _cachedStates[stateId];
	}

	// first try atomic and compound states
	NodeSet<std::string> target = _xpath.evaluate("//" + _nsInfo.xpathPrefix + "state[@id='" + stateId + "']", _scxml).asNodeSet();
	if (target.size() > 0)
		goto FOUND;

	// now parallel states
	target = _xpath.evaluate("//" + _nsInfo.xpathPrefix + "parallel[@id='" + stateId + "']", _scxml).asNodeSet();
	if (target.size() > 0)
		goto FOUND;

	// now final states
	target = _xpath.evaluate("//" + _nsInfo.xpathPrefix + "final[@id='" + stateId + "']", _scxml).asNodeSet();
	if (target.size() > 0)
		goto FOUND;

	// now history states
	target = _xpath.evaluate("//" + _nsInfo.xpathPrefix + "history[@id='" + stateId + "']", _scxml).asNodeSet();
	if (target.size() > 0)
		goto FOUND;

	{
		ERROR_EXECUTION_THROW("No state with id '" + stateId + "' found");
	}
FOUND:
	if (target.size() > 0) {
		for (int i = 0; i < target.size(); i++) {
			Element<std::string> targetElem(target[i]);
			if (!isInEmbeddedDocument(targetElem)) {
				_cachedStates[stateId] = targetElem;
				return targetElem;
			}
		}
	}
	// return the empty node
	return Arabica::DOM::Element<std::string>();
}

Arabica::XPath::NodeSet<std::string> InterpreterImpl::getAllStates() {
	NodeSet<std::string> states;
	states.push_back(_xpath.evaluate("//" + _nsInfo.xpathPrefix + "state", _scxml).asNodeSet());
	states.push_back(_xpath.evaluate("//" + _nsInfo.xpathPrefix + "parallel", _scxml).asNodeSet());
	states.push_back(_xpath.evaluate("//" + _nsInfo.xpathPrefix + "final", _scxml).asNodeSet());
	states.push_back(_xpath.evaluate("//" + _nsInfo.xpathPrefix + "history", _scxml).asNodeSet());
	return states;
}

Arabica::DOM::Node<std::string> InterpreterImpl::getSourceState(const Arabica::DOM::Element<std::string>& transition) {
	if (iequals(TAGNAME_CAST(transition.getParentNode()), _nsInfo.xmlNSPrefix + "initial"))
		return transition.getParentNode().getParentNode();
	return transition.getParentNode();
}

/**
 * In a conformant SCXML document, a compound state may specify either an "initial"
 * attribute or an <initial> element, but not both. See 3.6 <initial> for a
 * discussion of the difference between the two notations. If neither the "initial"
 * attribute nor an <initial> element is specified, the SCXML Processor must use
 * the first child state in document order as the default initial state.
 */
Arabica::XPath::NodeSet<std::string> InterpreterImpl::getInitialStates(Arabica::DOM::Element<std::string> state) {
	if (!state) {
		state = _scxml;
	}

#if VERBOSE
	std::cout << "Getting initial state of " << TAGNAME(state) << " " << ATTR(state, "id") << std::endl;
#endif

	if (isAtomic(state)) {
		return Arabica::XPath::NodeSet<std::string>();
	}
	
	assert(isCompound(state) || isParallel(state));

	if (isParallel(state)) {
		return getChildStates(state);
	}
	
	// initial attribute at element
	Arabica::DOM::Element<std::string> stateElem = (Arabica::DOM::Element<std::string>)state;
	if (stateElem.hasAttribute("initial")) {
		return getStates(tokenizeIdRefs(stateElem.getAttribute("initial")));
	}

	// initial element as child - but not the implicit generated one
	NodeSet<std::string> initElems = filterChildElements(_nsInfo.xmlNSPrefix + "initial", state);
	if(initElems.size() == 1 && !iequals(ATTR_CAST(initElems[0], "generated"), "true")) {
		NodeSet<std::string> initTrans = filterChildElements(_nsInfo.xmlNSPrefix + "transition", initElems[0]);
		return getTargetStates(Element<std::string>(initTrans[0]));
	}

	// first child state
	Arabica::XPath::NodeSet<std::string> initStates;
	NodeList<std::string> childs = state.getChildNodes();
	for (int i = 0; i < childs.getLength(); i++) {
		if (childs.item(i).getNodeType() != Node_base::ELEMENT_NODE)
			continue;
		if (isState(Element<std::string>(childs.item(i)))) {
			initStates.push_back(childs.item(i));
			return initStates;
		}

	}
	// nothing found
	return Arabica::XPath::NodeSet<std::string>();
}

NodeSet<std::string> InterpreterImpl::getTargetStates(const Arabica::DOM::Element<std::string>& transition) {
	if (_cachedTargets.find(transition) != _cachedTargets.end())
		return _cachedTargets[transition];

	NodeSet<std::string> targetStates;

	assert(boost::ends_with(TAGNAME(transition), "transition"));

	// if we are called with a state, process all its transitions
	if (isState(transition) || (transition.getNodeType() == Node_base::ELEMENT_NODE && iequals(_nsInfo.xmlNSPrefix + "initial", TAGNAME(transition)))) {
		NodeList<std::string> childs = transition.getChildNodes();
		for (int i = 0; i < childs.getLength(); i++) {
			if (childs.item(i).getNodeType() != Node_base::ELEMENT_NODE)
				continue;
			Element<std::string> childElem = Element<std::string>(childs.item(i));
			if (iequals(TAGNAME(childElem), _nsInfo.xmlNSPrefix + "transition")) {
				targetStates.push_back(getTargetStates(childElem));
			}
		}
		_cachedTargets[transition] = targetStates;
		return targetStates;
	}

	std::string targetId = ((Arabica::DOM::Element<std::string>)transition).getAttribute("target");
	std::list<std::string> targetIds = InterpreterImpl::tokenizeIdRefs(ATTR(transition, "target"));
	for (std::list<std::string>::const_iterator targetIter = targetIds.begin(); targetIter != targetIds.end(); targetIter++) {
		Arabica::DOM::Node<std::string> state = getState(*targetIter);
		if (state) {
			assert(HAS_ATTR_CAST(state, "id"));
			targetStates.push_back(state);
		}
	}
	_cachedTargets[transition] = targetStates;
	return targetStates;
}

NodeSet<std::string> InterpreterImpl::getTargetStates(const Arabica::XPath::NodeSet<std::string>& transitions) {
	NodeSet<std::string> targets;
	for (unsigned int i = 0; i < transitions.size(); i++) {
		targets.push_back(getTargetStates(Element<std::string>(transitions[i])));
	}
	return targets;
}

std::list<std::string> InterpreterImpl::tokenizeIdRefs(const std::string& idRefs) {
	std::list<std::string> ids;

	// appr. 3x faster than stringstream
	size_t start = 0;
	for (int i = 0; i < idRefs.size(); i++) {
		if (isspace(idRefs[i])) {
			if (i > 0 && start < i) {
				ids.push_back(idRefs.substr(start, i - start));
			}
			while(isspace(idRefs[++i])); // skip whitespaces
			start = i;
		} else if (i + 1 == idRefs.size()) {
			ids.push_back(idRefs.substr(start, i + 1 - start));
		}
	}


#if 0
	if (idRefs.length() > 0) {
		std::istringstream iss(idRefs);

		std::copy(std::istream_iterator<std::string>(iss),
		          std::istream_iterator<std::string>(),
		          std::back_inserter<std::vector<std::string> >(ids));
	}
#endif

#if 0
	// this version is somewhat fatser than the one above
	std::stringstream ss (idRefs);
	std::string item;
	while(ss >> item)
		ids.push_back(item);
#endif

	return ids;
}

std::string InterpreterImpl::spaceNormalize(const std::string& text) {
	std::stringstream content;

#if 1
	// 195ms with test-performance-events.scml
	std::string seperator;

	size_t start = 0;
	for (int i = 0; i < text.size(); i++) {
		if (isspace(text[i])) {
			if (i > 0 && start < i) {
				content << seperator << text.substr(start, i - start);
				seperator = " ";
			}
			while(isspace(text[++i])); // skip whitespaces
			start = i;
		} else if (i + 1 == text.size()) {
			content << seperator << text.substr(start, i + 1 - start);
		}
	}
//	std::cout << ">>" << content.str() << "<<" << std::endl;

#else

// 291ms with test-performance-events.scml
	std::istringstream iss(text);
	std::string seperator;
	do {
		std::string token;
		iss >> token;
		if (token.length() > 0) {
			content << seperator << token;
			seperator = " ";
		}
	} while (iss);

#endif
	return content.str();
}


NodeSet<std::string> InterpreterImpl::filterChildElements(const std::string& tagName, const NodeSet<std::string>& nodeSet, bool recurse) {
	NodeSet<std::string> filteredChildElems;
	for (unsigned int i = 0; i < nodeSet.size(); i++) {
		filteredChildElems.push_back(filterChildElements(tagName, nodeSet[i], recurse));
	}
	return filteredChildElems;
}

NodeSet<std::string> InterpreterImpl::filterChildElements(const std::string& tagName, const Node<std::string>& node, bool recurse) {
	NodeSet<std::string> filteredChildElems;

	if (!node)
		return filteredChildElems;

	NodeList<std::string> childs = node.getChildNodes();
	for (unsigned int i = 0; i < childs.getLength(); i++) {
		if (childs.item(i).getNodeType() != Node_base::ELEMENT_NODE)
			continue;
//		std::cout << TAGNAME(childs.item(i)) << std::endl;
		if(iequals(TAGNAME_CAST(childs.item(i)), tagName)) {
			filteredChildElems.push_back(childs.item(i));
		}
		if (recurse) {
			filteredChildElems.push_back(filterChildElements(tagName, childs.item(i), recurse));
		}
	}
	return filteredChildElems;
}

NodeSet<std::string> InterpreterImpl::filterChildType(const Node_base::Type type, const NodeSet<std::string>& nodeSet, bool recurse) {
	NodeSet<std::string> filteredChildType;
	for (unsigned int i = 0; i < nodeSet.size(); i++) {
		filteredChildType.push_back(filterChildType(type, nodeSet[i], recurse));
	}
	return filteredChildType;
}

NodeSet<std::string> InterpreterImpl::filterChildType(const Node_base::Type type, const Node<std::string>& node, bool recurse) {
	NodeSet<std::string> filteredChildTypes;

	if (!node)
		return filteredChildTypes;

	NodeList<std::string> childs = node.getChildNodes();
	for (unsigned int i = 0; i < childs.getLength(); i++) {
		if (childs.item(i).getNodeType() == type)
			filteredChildTypes.push_back(childs.item(i));
		if (recurse) {
			filteredChildTypes.push_back(filterChildType(type, childs.item(i), recurse));
		}
	}
	return filteredChildTypes;
}


NodeSet<std::string> InterpreterImpl::getProperAncestors(const Arabica::DOM::Node<std::string>& s1,
        const Arabica::DOM::Node<std::string>& s2) {

	std::pair<Arabica::DOM::Node<std::string>, Arabica::DOM::Node<std::string> > ancPair = std::make_pair(s1, s2);
	if (_cachedProperAncestors.find(ancPair) != _cachedProperAncestors.end())
		return _cachedProperAncestors[ancPair];

	NodeSet<std::string> ancestors;
	if (isState(Element<std::string>(s1))) {
		Arabica::DOM::Node<std::string> node = s1;
		while((node = node.getParentNode())) {
			if (node.getNodeType() != Node_base::ELEMENT_NODE)
				continue;

			Element<std::string> nodeElem(node);
			if (!isState(nodeElem))
				break;
			if (iequals(TAGNAME(nodeElem), _nsInfo.xmlNSPrefix + "scxml")) // do not return scxml root itself - this is somewhat ill-defined
				break;
			if (!iequals(TAGNAME(nodeElem), _nsInfo.xmlNSPrefix + "parallel") &&
			        !iequals(TAGNAME(nodeElem), _nsInfo.xmlNSPrefix + "state") &&
			        !iequals(TAGNAME(nodeElem), _nsInfo.xmlNSPrefix + "scxml"))
				break;
			if (node == s2)
				break;
			ancestors.push_back(node);
		}
	}
	_cachedProperAncestors[ancPair] = ancestors;
	return ancestors;
}

bool InterpreterImpl::isDescendant(const Arabica::DOM::Node<std::string>& s1,
                                   const Arabica::DOM::Node<std::string>& s2) {
	Arabica::DOM::Node<std::string> parent = s1.getParentNode();
	while(parent) {
		if (s2 == parent)
			return true;
		parent = parent.getParentNode();
	}
	return false;
}

bool InterpreterImpl::isTargetless(const Arabica::DOM::Element<std::string>& transition) {
	if (transition.hasAttribute("target")) {
		return false;
	}
	return true;
}

bool InterpreterImpl::isState(const Arabica::DOM::Element<std::string>& state) {
	if (!state)
		return false;

	std::string tagName = LOCALNAME(state);
	if (iequals("state", tagName))
		return true;
	if (iequals("scxml", tagName))
		return true;
	if (iequals("parallel", tagName))
		return true;
//	if (iequals("history", tagName)) // this is no state, see mail to W3C list
//		return true;
	if (iequals("final", tagName))
		return true;
	return false;
}

bool InterpreterImpl::isFinal(const Arabica::DOM::Element<std::string>& state) {
	std::string tagName = LOCALNAME(state);
	if (iequals("final", tagName))
		return true;
	if (HAS_ATTR(state, "final") && iequals("true", ATTR(state, "final")))
		return true;
	return false;
}

bool InterpreterImpl::isInEmbeddedDocument(const Node<std::string>& node) {
	// a node is in an embedded document if there is a content element in its parents
	Node<std::string> parent = node;
	while(parent) {
		if(parent == _scxml) {
			return false;
		}
		if(iequals(parent.getLocalName(), "content")) {
			return true;
		}
		parent = parent.getParentNode();
	}
	return false;
}

bool InterpreterImpl::isInitial(const Arabica::DOM::Element<std::string>& state) {
	if (!isState(state))
		return false;

	Arabica::DOM::Node<std::string> parentNode = state.getParentNode();
	if (parentNode.getNodeType() != Node_base::ELEMENT_NODE)
		return false;

	Arabica::DOM::Element<std::string> parent = (Element<std::string>)parentNode;
	if (!isState(parent))
		return true; // scxml element

	if (isMember(state, getInitialStates(parent)))
		return true; // every nested node

//	if (isParallel(parent))
//		return true;

	return false;
}

bool InterpreterImpl::isPseudoState(const Arabica::DOM::Element<std::string>& state) {
	std::string tagName = LOCALNAME(state);
	if (iequals("initial", tagName))
		return true;
	if (iequals("history", tagName))
		return true;
	return false;
}

bool InterpreterImpl::isTransitionTarget(const Arabica::DOM::Element<std::string>& elem) {
	return (isState(elem) || iequals(LOCALNAME(elem), "history"));
}

bool InterpreterImpl::isAtomic(const Arabica::DOM::Element<std::string>& state) {
	if (iequals("final", LOCALNAME(state)))
		return true;

	if (iequals("parallel", LOCALNAME(state)))
		return false;

	Arabica::DOM::NodeList<std::string> childs = state.getChildNodes();
	for (unsigned int i = 0; i < childs.getLength(); i++) {
		if (childs.item(i).getNodeType() != Node_base::ELEMENT_NODE)
			continue;

		if (isState(Element<std::string>(childs.item(i))))
			return false;
	}
	return true;
}

bool InterpreterImpl::isHistory(const Arabica::DOM::Element<std::string>& state) {
	if (iequals("history", LOCALNAME(state)))
		return true;
	return false;
}

bool InterpreterImpl::isParallel(const Arabica::DOM::Element<std::string>& state) {
	if (!isState(state))
		return false;
	if (iequals("parallel", LOCALNAME(state)))
		return true;
	return false;
}


bool InterpreterImpl::isCompound(const Arabica::DOM::Element<std::string>& state) {
	if (!isState(state))
		return false;

	if (iequals(LOCALNAME(state), "parallel")) // parallel is no compound state
		return false;

	Arabica::DOM::NodeList<std::string> childs = state.getChildNodes();
	for (unsigned int i = 0; i < childs.getLength(); i++) {
		if (childs.item(i).getNodeType() != Node_base::ELEMENT_NODE)
			continue;
		if (isState(Element<std::string>(childs.item(i))))
			return true;
	}
	return false;
}

void InterpreterImpl::setupIOProcessors() {
	tthread::lock_guard<tthread::recursive_mutex> lock(_pluginMutex);
	std::map<std::string, IOProcessorImpl*> ioProcs = _factory->getIOProcessors();
	std::map<std::string, IOProcessorImpl*>::iterator ioProcIter = ioProcs.begin();
	while(ioProcIter != ioProcs.end()) {
		if (iequals(ioProcIter->first, "basichttp") && !(_capabilities & CAN_BASIC_HTTP)) {
			ioProcIter++;
			continue;
		}
		if (iequals(ioProcIter->first, "http") && !(_capabilities & CAN_GENERIC_HTTP)) {
			ioProcIter++;
			continue;
		}

		// do not override if already set
		if (_ioProcessors.find(ioProcIter->first) != _ioProcessors.end()) {
			ioProcIter++;
			continue;
		}

		// this might throw error.execution
		_ioProcessors[ioProcIter->first] = _factory->createIOProcessor(ioProcIter->first, this);
		_ioProcessors[ioProcIter->first].setType(ioProcIter->first);
		_ioProcessors[ioProcIter->first].setInterpreter(this);

		if (iequals(ioProcIter->first, "http")) {
			// this is somewhat ugly
			_httpServlet = static_cast<InterpreterHTTPServlet*>(_ioProcessors[ioProcIter->first]._impl.get());
		}

		if (iequals(ioProcIter->first, "websocket")) {
			// this is somewhat ugly
			_wsServlet = static_cast<InterpreterWebSocketServlet*>(_ioProcessors[ioProcIter->first]._impl.get());
		}

		// register aliases
		std::list<std::string> names = _ioProcessors[ioProcIter->first].getNames();
		std::list<std::string>::iterator nameIter = names.begin();
		while(nameIter != names.end()) {
			// do not override
			if (!boost::equal(*nameIter, ioProcIter->first) && _ioProcessors.find(*nameIter) == _ioProcessors.end())
				_ioProcessors[*nameIter] = _ioProcessors[ioProcIter->first];
			nameIter++;
		}
#if 0
		try {
			_dataModel.registerIOProcessor(ioProcIter->first, _ioProcessors[ioProcIter->first]);
		} catch (Event e) {
			LOG(ERROR) << "Syntax error when setting _ioprocessors:" << std::endl << e << std::endl;
		}
#endif
		ioProcIter++;
	}
}

IOProcessor InterpreterImpl::getIOProcessor(const std::string& type) {
	tthread::lock_guard<tthread::recursive_mutex> lock(_pluginMutex);
	if (_ioProcessors.find(type) == _ioProcessors.end()) {
		LOG(ERROR) << "No ioProcessor known for type " << type;
		return IOProcessor();
	}
	return _ioProcessors[type];
}

void InterpreterImpl::setCmdLineOptions(std::map<std::string, std::string> params) {
	std::map<std::string, std::string>::iterator paramIter = params.begin();
	while (paramIter != params.end()) {
		if (paramIter->second.length() > 0) {
			_cmdLineOptions.compound[paramIter->first] = Data(paramIter->second, Data::VERBATIM);
		} else {
			_cmdLineOptions.compound[paramIter->first] = Data("true");
		}
		paramIter++;
	}
}

bool InterpreterImpl::hasLegalConfiguration() {
	return isLegalConfiguration(_configuration);
}

bool InterpreterImpl::isLegalConfiguration(const std::list<std::string>& config) {
	NodeSet<std::string> states;
	for (std::list<std::string>::const_iterator confIter = config.begin(); confIter != config.end(); confIter++) {
		Element<std::string> state = getState(*confIter);
		if (!state) {
			LOG(INFO) << "No state with id '" << *confIter << "'";
			return false;
		}
		states.push_back(state);
		while((state = getParentState(state))) {
			states.push_back(state);
		};
	}
	return isLegalConfiguration(states);
}

/**
 * See: http://www.w3.org/TR/scxml/#LegalStateConfigurations
 */
bool InterpreterImpl::isLegalConfiguration(const NodeSet<std::string>& config) {

	// The configuration contains exactly one child of the <scxml> element.
	NodeSet<std::string> scxmlChilds = getChildStates(_scxml);
	Node<std::string> foundScxmlChild;
	for (int i = 0; i < scxmlChilds.size(); i++) {
		if (isMember(scxmlChilds[i], config)) {
			if (foundScxmlChild) {
				LOG(ERROR) << "Invalid configuration: Multiple childs of scxml root are active '" << ATTR_CAST(foundScxmlChild, "id") << "' and '" << ATTR_CAST(scxmlChilds[i], "id") << "'";
				return false;
			}
			foundScxmlChild = scxmlChilds[i];
		}
	}
	if (!foundScxmlChild)
		return false;

	// The configuration contains one or more atomic states.
	bool foundAtomicState = false;
	for (int i = 0; i < config.size(); i++) {
		if (isAtomic(Element<std::string>(config[i]))) {
			foundAtomicState = true;
			break;
		}
	}
	if (!foundAtomicState) {
		LOG(ERROR) << "Invalid configuration: No atomic state is active";
		return false;
	}

	// When the configuration contains an atomic state, it contains all of its <state> and <parallel> ancestors.
	for (int i = 0; i < config.size(); i++) {
		if (isAtomic(Element<std::string>(config[i]))) {
			Node<std::string> parent = config[i];
			while(((parent = parent.getParentNode()) && parent.getNodeType() == Node_base::ELEMENT_NODE)) {
				if (isState(Element<std::string>(parent)) &&
				        (iequals(LOCALNAME(parent), "state") ||
				         iequals(LOCALNAME(parent), "parallel"))) {
					if (!isMember(parent, config)) {
						LOG(ERROR) << "Invalid configuration: atomic state '" << ATTR_CAST(config[i], "id") << "' is active, but parent '" << ATTR_CAST(parent, "id") << "' is not";
						return false;
					}
				}
			}
		}
	}

	// When the configuration contains a non-atomic <state>, it contains one and only one of the state's children
	for (int i = 0; i < config.size(); i++) {
		Element<std::string> configElem(config[i]);
		if (!isAtomic(configElem) && !isParallel(configElem)) {
			Node<std::string> foundChildState;
			//std::cout << config[i] << std::endl;
			NodeSet<std::string> childs = getChildStates(config[i]);
			for (int j = 0; j < childs.size(); j++) {
				//std::cout << childs[j] << std::endl;
				if (isMember(childs[j], config)) {
					if (foundChildState) {
						LOG(ERROR) << "Invalid configuration: Multiple childs of compound '" << ATTR_CAST(config[i], "id")
						           << "' are active '" << ATTR_CAST(foundChildState, "id") << "' and '" << ATTR_CAST(childs[j], "id") << "'";
						return false;
					}
					foundChildState = childs[j];
				}
			}
			if (!foundChildState) {
				LOG(ERROR) << "Invalid configuration: No childs of compound '" << ATTR_CAST(config[i], "id") << "' are active";
				return false;
			}
		}
	}

	// If the configuration contains a <parallel> state, it contains all of its children
	for (int i = 0; i < config.size(); i++) {
		if (isParallel(Element<std::string>(config[i]))) {
			NodeSet<std::string> childs = getChildStates(config[i]);
			for (int j = 0; j < childs.size(); j++) {
				if (!isMember(childs[j], config) && !isHistory(Element<std::string>(childs[j]))) {
					LOG(ERROR) << "Invalid configuration: Not all children of parallel '" << ATTR_CAST(config[i], "id") << "' are active i.e. '" << ATTR_CAST(childs[j], "id") << "' is not";
					return false;
				}
			}
		}
	}

	// everything worked out fine!
	return true;
}

bool InterpreterImpl::isInState(const std::string& stateId) {
	if (HAS_ATTR(_scxml, "flat") && DOMUtils::attributeIsTrue(ATTR(_scxml, "flat"))) {
		// extension for flattened SCXML documents
		if (_configuration.size() > 0 && HAS_ATTR_CAST(_configuration[0], "id")) {
			// all states are encoded in the current statename
			FlatStateIdentifier flatId(ATTR_CAST(_configuration[0], "id"));
			for (std::list<std::string>::const_iterator iter = flatId.getActive().begin(); iter != flatId.getActive().end(); iter++) {
				if (iequals(stateId, *iter))
					return true;
			}
		}
		return false;
	} else {

		for (int i = 0; i < _configuration.size(); i++) {
			if (HAS_ATTR_CAST(_configuration[i], "id") &&
			        iequals(ATTR_CAST(_configuration[i], "id"), stateId)) {
				return true;
			}
		}
	}
	return false;
}

void InterpreterImpl::handleDOMEvent(Arabica::DOM::Events::Event<std::string>& event) {
	// clear targets
	_cachedTargets.clear();

	if (event.getType().compare("DOMAttrModified") == 0) // we do not care about other attributes
		return;

	// remove modified states from cache
	Node<std::string> target = Arabica::DOM::Node<std::string>(event.getTarget());
	NodeSet<std::string> childs = InterpreterImpl::filterChildElements(_nsInfo.xmlNSPrefix + "state", target);
	for (int i = 0; i < childs.size(); i++) {
		if (HAS_ATTR_CAST(childs[i], "id")) {
			_cachedStates.erase(ATTR_CAST(childs[i], "id"));
		}
	}
	// it's more stress to search through all pairs, just have them recalculated
	_cachedProperAncestors.clear();
}

void InterpreterImpl::DOMEventListener::handleEvent(Arabica::DOM::Events::Event<std::string>& event) {
	if (_interpreter)
		_interpreter->handleDOMEvent(event);
}

std::ostream& operator<< (std::ostream& os, const InterpreterState& interpreterState) {
	os << "[" << InterpreterImpl::stateToString(interpreterState) << "]" << std::endl;
	return os;
}

std::string InterpreterImpl::stateToString(InterpreterState state) {
	std::stringstream ss;

	switch(state) {
	case USCXML_INSTANTIATED:
		ss << "INSTANTIATED";
		break;
	case USCXML_MICROSTEPPED:
		ss << "MICROSTEPPED";
		break;
	case USCXML_MACROSTEPPED:
		ss << "MACROSTEPPED";
		break;
	case USCXML_IDLE:
		ss << "IDLE";
		break;
	case USCXML_FINISHED:
		ss << "FINISHED";
		break;
	case USCXML_DESTROYED:
		ss << "DESTROYED";
		break;
	default:
		ss << "INVALID";
		break;
	}

	return ss.str();
}


}
