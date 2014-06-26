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
#include "uscxml/transform/ChartToFSM.h" // only for testing

#include "uscxml/plugins/invoker/http/HTTPServletInvoker.h"

#include <DOM/Simple/DOMImplementation.hpp>
#include <SAX/helpers/InputSourceResolver.hpp>

#include <boost/lexical_cast.hpp>
#include <boost/tokenizer.hpp>
#include <boost/algorithm/string.hpp>

#include <glog/logging.h>

#include <assert.h>
#include <algorithm>

#include "uscxml/interpreter/InterpreterDraft6.h"
#include "uscxml/interpreter/InterpreterRC.h"

#if 1
#define INTERPRETER_IMPL InterpreterDraft6
#else
#define INTERPRETER_IMPL InterpreterRC
#endif

#define VERBOSE 0

/// valid interpreter state transitions
#define VALID_FROM_INSTANTIATED(newState) ( \
	newState == InterpreterState::USCXML_FAULTED || \
	newState == InterpreterState::USCXML_MICROSTEPPED || \
	newState == InterpreterState::USCXML_DESTROYED\
)

#define VALID_FROM_FAULTED(newState) ( \
	newState == InterpreterState::USCXML_DESTROYED\
)

#define VALID_FROM_INITIALIZED(newState) ( \
	newState == InterpreterState::USCXML_MICROSTEPPED || \
	newState == InterpreterState::USCXML_FINISHED \
)

#define VALID_FROM_MICROSTEPPED(newState) ( \
	newState == InterpreterState::USCXML_DESTROYED || \
	newState == InterpreterState::USCXML_MACROSTEPPED || \
	newState == InterpreterState::USCXML_MICROSTEPPED || \
	newState == InterpreterState::USCXML_FINISHED \
)

#define VALID_FROM_MACROSTEPPED(newState) ( \
	newState == InterpreterState::USCXML_DESTROYED || \
	newState == InterpreterState::USCXML_MICROSTEPPED || \
	newState == InterpreterState::USCXML_IDLE || \
	newState == InterpreterState::USCXML_FINISHED \
)

#define VALID_FROM_IDLE(newState) ( \
	newState == InterpreterState::USCXML_DESTROYED || \
	newState == InterpreterState::USCXML_MICROSTEPPED || \
	newState == InterpreterState::USCXML_MACROSTEPPED \
)

#define VALID_FROM_FINISHED(newState) ( \
	newState == InterpreterState::USCXML_DESTROYED || \
	newState == InterpreterState::USCXML_INSTANTIATED \
)

#define THROW_ERROR_PLATFORM(msg) \
	Event e; \
	e.name = "error.platform"; \
	e.data.compound["cause"] = Data(msg, Data::VERBATIM); \
	throw e; \
 

/// macro to catch exceptions in executeContent
#define CATCH_AND_DISTRIBUTE(msg) \
catch (Event e) {\
	LOG(ERROR) << msg << std::endl << e << std::endl;\
	if (rethrow) {\
		throw(e);\
	} else {\
		e.name = "error.execution";\
		e.eventType = Event::PLATFORM;\
		receiveInternal(e);\
	}\
}

#define CATCH_AND_DISTRIBUTE2(msg, node) \
catch (Event e) {\
	LOG(ERROR) << msg << " " << DOMUtils::xPathForNode(node) << ":" << std::endl << e << std::endl;\
	if (rethrow) {\
		throw(e);\
	} else {\
		e.name = "error.execution";\
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
		{"verbose",       no_argument,       0, 'v'},
		{"debug",         no_argument,       0, 'd'},
		{"port",          required_argument, 0, 't'},
		{"ssl-port",      required_argument, 0, 's'},
		{"ws-port",       required_argument, 0, 'w'},
		{"certificate",   required_argument, 0, 'c'},
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
		option = getopt_long_only(argc, argv, "+vdt:s:w:c:p:l:", longOptions, &optionInd);
		if (option == -1) {
			if (optind == argc)
				// we are done with parsing
				goto DONE_PARSING_CMD;

			std::string url = argv[optind];
			options.interpreters[url] = new InterpreterOptions();
			currOptions = options.interpreters[url];

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
			currOptions->certificate = optarg;
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
	_state.state = InterpreterState::USCXML_INSTANTIATED;
	_state.thread = 0;
	_lastRunOnMainThread = 0;
	_thread = NULL;
	_sendQueue = NULL;
	_parentQueue = NULL;
	_topLevelFinalReached = false;
	_stable = false;
	_isInitialized = false;
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
	interpreterImpl->_document = dom;
	interpreterImpl->setNameSpaceInfo(nameSpaceInfo);
	interpreterImpl->_document = dom;

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
	URL absUrl(uri);
	if (!absUrl.isAbsolute()) {
		if (!absUrl.toAbsoluteCwd()) {
			THROW_ERROR_PLATFORM("Given URL is not absolute or does not have file schema");
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
			THROW_ERROR_PLATFORM("Downloading SCXML document from " + absUrl.asString() + " failed");
		}
		interpreter = fromXML(ss.str());
	}

	// try to establish URI root for relative src attributes in document
	if (interpreter) {
		interpreter._impl->_baseURI = URL::asBaseURL(absUrl);
		interpreter._impl->_sourceURI = absUrl;
	} else {
		THROW_ERROR_PLATFORM("Cannot create interpreter from URI " + absUrl.asString() + "'");
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
	} else {
		if (parser.errorsReported()) {
			THROW_ERROR_PLATFORM(parser.errors())
		} else {
			THROW_ERROR_PLATFORM("Failed to create interpreter");
//			interpreterImpl->setInterpreterState(InterpreterState::USCXML_FAULTED, parser.errors());
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
			other->init();
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
		other->init();
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
			setInterpreterState(InterpreterState::USCXML_DESTROYED);
		}
	}
	join();
	if (_sendQueue)
		delete _sendQueue;

}

void InterpreterImpl::start() {
	_state.thread |= InterpreterState::USCXML_THREAD_STARTED;
	_thread = new tthread::thread(InterpreterImpl::run, this);
}

void InterpreterImpl::stop() {
	_state.thread &= ~InterpreterState::USCXML_THREAD_STARTED;
}

void InterpreterImpl::join() {
	stop();
	if (_thread != NULL) _thread->join();
};

bool InterpreterImpl::isRunning() {
	//		return _running || !_topLevelFinalReached;
	return (_state.thread & InterpreterState::USCXML_THREAD_RUNNING) > 0;
}

void InterpreterImpl::run(void* instance) {
	InterpreterImpl* interpreter = ((InterpreterImpl*)instance);
	interpreter->_state.thread |= InterpreterState::USCXML_THREAD_RUNNING;

	try {
		InterpreterState state;
		while(interpreter->_state.thread & InterpreterState::USCXML_THREAD_STARTED) {
			state = interpreter->step(-1);

			switch (state & InterpreterState::USCXML_INTERPRETER_MASK) {
			case uscxml::InterpreterState::USCXML_FAULTED:
			case uscxml::InterpreterState::USCXML_FINISHED:
			case uscxml::InterpreterState::USCXML_DESTROYED:
				// return as we finished
				goto DONE_THREAD;
			default:
				break;
			}
		}
	} catch (Event e) {
		LOG(ERROR) << e;
	} catch(boost::bad_lexical_cast e) {
		LOG(ERROR) << "InterpreterImpl::run catched exception: " << e.what();
	} catch (...) {
		LOG(ERROR) << "InterpreterImpl::run catched unknown exception";
	}
DONE_THREAD:
	((InterpreterImpl*)instance)->_state.thread &= ~InterpreterState::USCXML_THREAD_RUNNING;
	((InterpreterImpl*)instance)->_state.thread &= ~InterpreterState::USCXML_THREAD_STARTED;
}

InterpreterState InterpreterImpl::getInterpreterState() {
	return _state;
}

void InterpreterImpl::setInterpreterState(InterpreterState::State newState) {
	setInterpreterState(newState, Event());
}

void InterpreterImpl::setInterpreterState(InterpreterState::State newState, const std::string& error) {
	Event e;
	e.name = "error.platform";
	e.data.compound["cause"] = Data(error, Data::VERBATIM);
	setInterpreterState(newState, e);
}

void InterpreterImpl::setInterpreterState(InterpreterState::State newState, const Event& error) {
	switch (_state) {
	case InterpreterState::USCXML_INSTANTIATED:
		if (VALID_FROM_INSTANTIATED(newState))
			break;
		assert(false);
		break;
	case InterpreterState::USCXML_FAULTED:
		if (VALID_FROM_FAULTED(newState))
			break;
		assert(false);
		break;
	case InterpreterState::USCXML_MICROSTEPPED:
		if (VALID_FROM_MICROSTEPPED(newState))
			break;
		assert(false);
		break;
	case InterpreterState::USCXML_MACROSTEPPED:
		if (VALID_FROM_MACROSTEPPED(newState))
			break;
		assert(false);
		break;
	case InterpreterState::USCXML_IDLE:
		if (VALID_FROM_IDLE(newState))
			break;
		assert(false);
		break;
	case InterpreterState::USCXML_FINISHED:
		if (VALID_FROM_FINISHED(newState))
			break;
		assert(false);
		break;
	case InterpreterState::USCXML_DESTROYED:
		assert(false);
		break;

	default:
		break;
	}

	_state.state = newState;
	_state.msg = error;
}

bool InterpreterImpl::runOnMainThread(int fps, bool blocking) {
	tthread::lock_guard<tthread::recursive_mutex> lock(_mutex);
	if (_state == InterpreterState::USCXML_FINISHED || _state == InterpreterState::USCXML_FAULTED || _state == InterpreterState::USCXML_DESTROYED)
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

	_alreadyEntered = NodeSet<std::string>();
	_configuration = NodeSet<std::string>();
	_topLevelFinalReached = false;
	_isInitialized = false;

	setInterpreterState(InterpreterState::USCXML_INSTANTIATED);
}

void InterpreterImpl::setupAndNormalizeDOM() {
	if (_domIsSetup)
		return;

	if (!_document) {
		Event error("error.platform");
		error.data.compound["cause"] = Data("Interpreter has no DOM", Data::VERBATIM);
		throw error;
	}

	// find scxml element
	NodeList<std::string> scxmls;
	if (_nsInfo.nsURL.size() == 0) {
		scxmls = _document.getElementsByTagName("scxml");
	} else {
		scxmls = _document.getElementsByTagNameNS(_nsInfo.nsURL, "scxml");
	}

	if (scxmls.getLength() == 0) {
		Event error("error.platform");
		error.data.compound["cause"] = Data("Cannot find SCXML element in DOM", Data::VERBATIM);
		throw error;
	}

	_scxml = (Arabica::DOM::Element<std::string>)scxmls.item(0);

	if (_nsInfo.getNSContext() != NULL)
		_xpath.setNamespaceContext(*_nsInfo.getNSContext());

	// normalize document
	// TODO: Resolve XML includes

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

	// make sure every invoke has an idlocation or id
	Arabica::XPath::NodeSet<std::string> invokes = _xpath.evaluate("//" + _nsInfo.xpathPrefix + "invoke", _scxml).asNodeSet();
	for (int i = 0; i < invokes.size(); i++) {
		Arabica::DOM::Element<std::string> invokeElem = Arabica::DOM::Element<std::string>(invokes[i]);
		if (!invokeElem.hasAttribute("id") && !invokeElem.hasAttribute("idlocation")) {
			invokeElem.setAttribute("id", UUID::getUUID());
		}
	}

	// add an id to the scxml element
	if (!_scxml.hasAttribute("id")) {
		_scxml.setAttribute("id", UUID::getUUID());
	}

	// register for dom events to manage cached states
	Arabica::DOM::Events::EventTarget<std::string> eventTarget(_scxml);
	eventTarget.addEventListener("DOMNodeInserted", _domEventListener, true);
	eventTarget.addEventListener("DOMNodeRemoved", _domEventListener, true);
	eventTarget.addEventListener("DOMSubtreeModified", _domEventListener, true);

}

void InterpreterImpl::init() {
	// make sure we have a factory if none was set before
	if (_factory == NULL)
		_factory = Factory::getInstance();

	// setup and normalize DOM
	setupAndNormalizeDOM();

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

	// instantiate datamodel
	if (HAS_ATTR(_scxml, "datamodel")) {
		_dataModel = _factory->createDataModel(ATTR(_scxml, "datamodel"), this);
		if (!_dataModel) {
			Event e;
			e.data.compound["cause"] = Data("Cannot instantiate datamodel", Data::VERBATIM);
			throw e;
		}
	} else {
		_dataModel = _factory->createDataModel("null", this);
	}

	_dataModel.assign("_x.args", _cmdLineOptions);

//	_running = true;
#if VERBOSE
	std::cout << "running " << this << std::endl;
#endif

	_binding = (HAS_ATTR(_scxml, "binding") && iequals(ATTR(_scxml, "binding"), "late") ? LATE : EARLY);

	// @TODO: Reread http://www.w3.org/TR/scxml/#DataBinding

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
		if (_dataModel) {
			executeContent(globalScriptElems[i]);
		}
	}

	_isInitialized = true;
	_stable = false;
}

/**
 * Called with a single data element from the topmost datamodel element.
 */
void InterpreterImpl::initializeData(const Element<std::string>& data) {
	if (!_dataModel) {
		LOG(ERROR) << "Cannot initialize data when no datamodel is given!";
		return;
	}

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

void InterpreterImpl::internalDoneSend(const Arabica::DOM::Node<std::string>& state) {
	if (!isState(state))
		return;

	Arabica::DOM::Element<std::string> stateElem = (Arabica::DOM::Element<std::string>)state;
	Arabica::DOM::Element<std::string> parent = (Arabica::DOM::Element<std::string>)stateElem.getParentNode();
	Event event;

	Arabica::XPath::NodeSet<std::string> doneDatas = filterChildElements(_nsInfo.xmlNSPrefix + "donedata", stateElem);
	if (doneDatas.size() > 0) {
		// only process first donedata element
		Arabica::DOM::Node<std::string> doneData = doneDatas[0];
		processParamChilds(doneData, event.params);
		Arabica::XPath::NodeSet<std::string> contents = filterChildElements(_nsInfo.xmlNSPrefix + "content", doneDatas[0]);
		if (contents.size() > 1)
			LOG(ERROR) << "Only a single content element is allowed for send elements - using first one";
		if (contents.size() > 0) {
			std::string expr;
			processContentElement(contents[0], event.dom, event.content, expr);
			if (expr.length() > 0 && _dataModel) {
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

	event.name = "done.state." + ATTR(stateElem.getParentNode(), "id"); // parent?!
	receiveInternal(event);

}

void InterpreterImpl::processContentElement(const Arabica::DOM::Node<std::string>& content,
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

void InterpreterImpl::processDOMorText(const Arabica::DOM::Node<std::string>& element,
                                       Arabica::DOM::Node<std::string>& dom,
                                       std::string& text) {
	// do we need to download?
	if (HAS_ATTR(element, "src") ||
	        (HAS_ATTR(element, "srcexpr") && _dataModel)) {
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

void InterpreterImpl::processParamChilds(const Arabica::DOM::Node<std::string>& element, std::multimap<std::string, Data>& params) {
	NodeSet<std::string> paramElems = filterChildElements(_nsInfo.xmlNSPrefix + "param", element);
	for (int i = 0; i < paramElems.size(); i++) {
		try {
			if (!HAS_ATTR(paramElems[i], "name")) {
				LOG(ERROR) << "param element is missing name attribute";
				continue;
			}
			Data paramValue;
			if (HAS_ATTR(paramElems[i], "expr") && _dataModel) {
				paramValue = _dataModel.getStringAsData(ATTR(paramElems[i], "expr"));
			} else if(HAS_ATTR(paramElems[i], "location") && _dataModel) {
				paramValue = _dataModel.getStringAsData(ATTR(paramElems[i], "location"));
			} else {
				LOG(ERROR) << "param element is missing expr or location or no datamodel is specified";
				continue;
			}
			std::string paramKey = ATTR(paramElems[i], "name");
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

void InterpreterImpl::send(const Arabica::DOM::Node<std::string>& element) {
	SendRequest sendReq;
	// test 331
	sendReq.Event::eventType = Event::EXTERNAL;
	try {
		// event
		if (HAS_ATTR(element, "eventexpr") && _dataModel) {
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
		if (HAS_ATTR(element, "targetexpr") && _dataModel) {
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
		if (HAS_ATTR(element, "typeexpr") && _dataModel) {
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
			if (HAS_ATTR(element, "idlocation") && _dataModel) {
				_dataModel.assign(ATTR(element, "idlocation"), "'" + sendReq.sendid + "'");
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
		if (HAS_ATTR(element, "delayexpr") && _dataModel) {
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
			if (_dataModel) {
				std::list<std::string> names = tokenizeIdRefs(ATTR(element, "namelist"));
				for (std::list<std::string>::const_iterator nameIter = names.begin(); nameIter != names.end(); nameIter++) {
					Data namelistValue = _dataModel.getStringAsData(*nameIter);
					sendReq.namelist[*nameIter] = namelistValue;
					sendReq.data.compound[*nameIter] = namelistValue;
				}
			} else {
				LOG(ERROR) << "Namelist attribute at send requires datamodel to be defined";
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
			processContentElement(contents[0], sendReq.dom, sendReq.content, expr);
			if (expr.length() > 0 && _dataModel) {
				try {
					sendReq.data = _dataModel.getStringAsData(expr);
				} catch (Event e) {
					e.name = "error.execution";
					receiveInternal(e);
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
		} catch(...) {
			LOG(ERROR) << "Exception caught while sending event to ioprocessor " << sendReq.type;
		}
	} else {
		/**
		 * If the SCXML Processor does not support the type that is specified, it
		 * must place the event error.execution on the internal event queue.
		 */
		Event exceptionEvent("error.execution", Event::PLATFORM);
//			exceptionEvent.sendid = sendReq.sendid;
		INSTANCE->receiveInternal(exceptionEvent);
	}

	assert(INSTANCE->_sendIds.find(sendReq.sendid) != INSTANCE->_sendIds.end());
	INSTANCE->_sendIds.erase(sendReq.sendid);
}

void InterpreterImpl::invoke(const Arabica::DOM::Node<std::string>& element) {
	InvokeRequest invokeReq;
	invokeReq.Event::eventType = Event::EXTERNAL;
	try {
		// type
		if (HAS_ATTR(element, "typeexpr") && _dataModel) {
			invokeReq.type = _dataModel.evalAsString(ATTR(element, "typeexpr"));
		} else if (HAS_ATTR(element, "type")) {
			invokeReq.type = ATTR(element, "type");
		}

		// src
		std::string source;
		if (HAS_ATTR(element, "srcexpr") && _dataModel) {
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
				if (HAS_ATTR(element, "idlocation") && _dataModel) {
					_dataModel.assign(ATTR(element, "idlocation"), "'" + invokeReq.invokeid + "'");
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
				invokeReq.namelist[*nameIter] = _dataModel.evalAsString(*nameIter);
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
				processContentElement(contents[0], invokeReq.dom, invokeReq.content, expr);
				if (expr.length() > 0 && _dataModel) {
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

		Invoker invoker(_factory->createInvoker(invokeReq.type, this));
		if (invoker) {
			tthread::lock_guard<tthread::recursive_mutex> lock(_pluginMutex);
			try {
				invoker.setInvokeId(invokeReq.invokeid);
				invoker.setType(invokeReq.type);
				invoker.setInterpreter(this);
				invoker.setElement(Element<std::string>(element));
				_invokers[invokeReq.invokeid] = invoker;
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
				} catch(...) {
					LOG(ERROR) << "Unknown exception caught while sending invoke request to invoker " << invokeReq.invokeid;
				}
				if (_dataModel) {
					try {
//						_dataModel.assign("_invokers['" + invokeReq.invokeid + "']", invoker.getDataModelVariables());
					} catch(...) {
						LOG(ERROR) << "Exception caught while assigning datamodel variables from invoker " << invokeReq.invokeid;
					}
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

void InterpreterImpl::cancelInvoke(const Arabica::DOM::Node<std::string>& element) {
	std::string invokeId;
	if (HAS_ATTR(element, "idlocation") && _dataModel) {
		invokeId = _dataModel.evalAsString(ATTR(element, "idlocation"));
	} else if (HAS_ATTR(element, "id")) {
		invokeId = ATTR(element, "id");
	} else {
		assert(false);
	}
	if (_invokers.find(invokeId) != _invokers.end()) {
		LOG(INFO) << "Removed invoker at " << invokeId;
		if (_dataModel) {
			try {
				_dataModel.assign("_invokers['" + invokeId + "']", std::string("''"));
			} catch (Event e) {
				LOG(ERROR) << "Syntax when removing invoker:" << std::endl << e << std::endl;
			}
		}

		USCXML_MONITOR_CALLBACK3(beforeUninvoking, Element<std::string>(element), invokeId)

		_invokers.erase(invokeId);

		USCXML_MONITOR_CALLBACK3(beforeUninvoking, Element<std::string>(element), invokeId)

	} else {
		LOG(ERROR) << "Cannot cancel invoke for id " << invokeId << ": no such invokation";
	}
	//receiveInternal(Event("done.invoke." + invokeId, Event::PLATFORM));
}


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


bool InterpreterImpl::hasConditionMatch(const Arabica::DOM::Node<std::string>& conditional) {

	if (HAS_ATTR(conditional, "cond") && ATTR(conditional, "cond").length() > 0) {
		try {
			return _dataModel.evalAsBool(ATTR_NODE(conditional, "cond"), ATTR(conditional, "cond"));
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
			executeContent(node, true);
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
			executeContent(node, true);
		}
		CATCH_AND_DISTRIBUTE2("Error when executing content", content[i]);
	}
}

void InterpreterImpl::executeContent(const Arabica::DOM::Node<std::string>& content, bool rethrow) {
	if (content.getNodeType() != Node_base::ELEMENT_NODE)
		return;

	if (iequals(TAGNAME(content), _nsInfo.xmlNSPrefix + "onentry") ||
	        iequals(TAGNAME(content), _nsInfo.xmlNSPrefix + "onexit") ||
	        iequals(TAGNAME(content), _nsInfo.xmlNSPrefix + "finalize") ||
	        iequals(TAGNAME(content), _nsInfo.xmlNSPrefix + "transition")) {
		// --- CONVENIENCE LOOP --------------------------
		NodeList<std::string> executable = content.getChildNodes();
		for (int i = 0; i < executable.getLength(); i++) {
			executeContent(executable.item(i), rethrow);
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
					processContentElement(contents[0], raised.dom, raised.content, expr);
					if (expr.length() > 0 && _dataModel) {
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
				if (iequals(TAGNAME(childs.item(i)), _nsInfo.xmlNSPrefix + "elseif") ||
				        iequals(TAGNAME(childs.item(i)), _nsInfo.xmlNSPrefix + "else")) {
					if (blockIsTrue) {
						// last block was true, break here
						break;
					} else {
						// is this block the one to execute?
						blockIsTrue = hasConditionMatch(childs.item(i));
					}
				} else {
					if (blockIsTrue) {
						executeContent(childs.item(i), rethrow);
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
		if (_dataModel) {
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
		if (_dataModel && HAS_ATTR(content, "location")) {
			try {
				if (!_dataModel.isDeclared(ATTR(content, "location"))) {
					// test 286, 331
					LOG(ERROR) << "Assigning to undeclared location '" << ATTR(content, "location") << "' not allowed." << std::endl;
					throw Event("error.execution", Event::PLATFORM);
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
		if (_dataModel) {
			std::string location = (HAS_ATTR(content, "location") ? ATTR(content, "location") : "");
			std::string schema = (HAS_ATTR(content, "schema") ? ATTR(content, "schema") : "");
			_dataModel.validate(location, schema);
		}
	} else if (iequals(TAGNAME(content), _nsInfo.xmlNSPrefix + "script")) {
		// --- SCRIPT --------------------------
		if (_dataModel) {
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
				CATCH_AND_DISTRIBUTE("Syntax error while executing script element from '" << ATTR(content, "src") << "':")
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
			execContent = _factory->createExecutableContent(content.getLocalName(), content.getNamespaceURI(), this);
			if (!execContent) {
				LOG(ERROR) << "No custom executable content known for element '"
				           << content.getLocalName() << "' in namespace '" << content.getNamespaceURI() << "'";
				return;
			}
			_executableContent[content] = execContent;
		} else {
			execContent = _executableContent[content];
		}

		execContent.enterElement(content);
		if (execContent.processChildren()) {
			NodeList<std::string> executable = content.getChildNodes();
			for (int i = 0; i < executable.getLength(); i++) {
				executeContent(executable.item(i), rethrow);
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

bool InterpreterImpl::parentIsScxmlState(const Arabica::DOM::Node<std::string>& state) {
	Arabica::DOM::Element<std::string> stateElem = (Arabica::DOM::Element<std::string>)state;
	Arabica::DOM::Element<std::string> parentElem = (Arabica::DOM::Element<std::string>)state.getParentNode();
	if (iequals(TAGNAME(parentElem), _nsInfo.xmlNSPrefix + "scxml"))
		return true;
	return false;
}

bool InterpreterImpl::isInFinalState(const Arabica::DOM::Node<std::string>& state) {
	if (isCompound(state)) {
		Arabica::XPath::NodeSet<std::string> childs = getChildStates(state);
		for (int i = 0; i < childs.size(); i++) {
			if (isFinal(childs[i]) && isMember(childs[i], _configuration))
				return true;
		}
	} else if (isParallel(state)) {
		Arabica::XPath::NodeSet<std::string> childs = getChildStates(state);
		for (int i = 0; i < childs.size(); i++) {
			if (!isInFinalState(childs[i]))
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
		if (isState(childElems.item(i))) {
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

Arabica::DOM::Node<std::string> InterpreterImpl::getParentState(const Arabica::DOM::Node<std::string>& element) {
	Arabica::DOM::Node<std::string> parent = element.getParentNode();
	while(parent && !isState(parent)) {
		parent = parent.getParentNode();
	}
	return parent;
}

Arabica::DOM::Node<std::string> InterpreterImpl::getAncestorElement(const Arabica::DOM::Node<std::string>& node, const std::string tagName) {
	Arabica::DOM::Node<std::string> parent = node.getParentNode();
	while(parent) {
		if (parent.getNodeType() == Node_base::ELEMENT_NODE &&
		        iequals(TAGNAME(parent), tagName)) {
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
		if (!isCompound(ancestors[i]))
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

Arabica::DOM::Node<std::string> InterpreterImpl::getState(const std::string& stateId) {

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

	LOG(ERROR) << "No state with id " << stateId << " found!";
	{
		Event ev;
		ev.name = "error.execution";
		ev.eventType = Event::PLATFORM;
		ev.data.compound["cause"] = Data("No state with id " + stateId + " found", Data::VERBATIM);
		throw ev;
	}
FOUND:
	if (target.size() > 0) {
		for (int i = 0; i < target.size(); i++) {
			if (!isInEmbeddedDocument(target[i])) {
				_cachedStates[stateId] = target[i];
				return target[i];
			}
		}
	}
	// return the empty node
	return Arabica::DOM::Node<std::string>();
}

Arabica::XPath::NodeSet<std::string> InterpreterImpl::getAllStates() {
	NodeSet<std::string> states;
	states.push_back(_xpath.evaluate("//" + _nsInfo.xpathPrefix + "state", _scxml).asNodeSet());
	states.push_back(_xpath.evaluate("//" + _nsInfo.xpathPrefix + "parallel", _scxml).asNodeSet());
	states.push_back(_xpath.evaluate("//" + _nsInfo.xpathPrefix + "final", _scxml).asNodeSet());
	states.push_back(_xpath.evaluate("//" + _nsInfo.xpathPrefix + "history", _scxml).asNodeSet());
	return states;
}

Arabica::DOM::Node<std::string> InterpreterImpl::getSourceState(const Arabica::DOM::Node<std::string>& transition) {
	if (iequals(TAGNAME(transition.getParentNode()), _nsInfo.xmlNSPrefix + "initial"))
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
Arabica::XPath::NodeSet<std::string> InterpreterImpl::getInitialStates(Arabica::DOM::Node<std::string> state) {
	if (!state) {
		state = _scxml;
	}

#if VERBOSE
	std::cout << "Getting initial state of " << TAGNAME(state) << " " << ATTR(state, "id") << std::endl;
#endif

	assert(isCompound(state) || isParallel(state));

	// initial attribute at element
	Arabica::DOM::Element<std::string> stateElem = (Arabica::DOM::Element<std::string>)state;
	if (stateElem.hasAttribute("initial")) {
		return getStates(tokenizeIdRefs(stateElem.getAttribute("initial")));
	}

	// initial element as child - but not the implicit generated one
	NodeSet<std::string> initElems = filterChildElements(_nsInfo.xmlNSPrefix + "initial", state);
	if(initElems.size() == 1 && !iequals(ATTR(initElems[0], "generated"), "true")) {
		NodeSet<std::string> initTrans = filterChildElements(_nsInfo.xmlNSPrefix + "transition", initElems[0]);
		return getTargetStates(initTrans[0]);
	}

	// first child state
	Arabica::XPath::NodeSet<std::string> initStates;
	NodeList<std::string> childs = state.getChildNodes();
	for (int i = 0; i < childs.getLength(); i++) {
		if (isState(childs.item(i))) {
			initStates.push_back(childs.item(i));
			return initStates;
		}

	}
	// nothing found
	return Arabica::XPath::NodeSet<std::string>();
}

NodeSet<std::string> InterpreterImpl::getTargetStates(const Arabica::DOM::Node<std::string>& transition) {
	NodeSet<std::string> targetStates;

	assert(boost::ends_with(TAGNAME(transition), "transition"));

	// if we are called with a state, process all its transitions
	if (isState(transition) || (transition.getNodeType() == Node_base::ELEMENT_NODE && iequals(_nsInfo.xmlNSPrefix + "initial", TAGNAME(transition)))) {
		NodeList<std::string> childs = transition.getChildNodes();
		for (int i = 0; i < childs.getLength(); i++) {
			if (childs.item(i).getNodeType() == Node_base::ELEMENT_NODE && iequals(TAGNAME(childs.item(i)), _nsInfo.xmlNSPrefix + "transition")) {
				targetStates.push_back(getTargetStates(childs.item(i)));
			}
		}
		return targetStates;
	}

	std::string targetId = ((Arabica::DOM::Element<std::string>)transition).getAttribute("target");
	std::list<std::string> targetIds = InterpreterImpl::tokenizeIdRefs(ATTR(transition, "target"));
	for (std::list<std::string>::const_iterator targetIter = targetIds.begin(); targetIter != targetIds.end(); targetIter++) {
		Arabica::DOM::Node<std::string> state = getState(*targetIter);
		if (state) {
			assert(HAS_ATTR(state, "id"));
			targetStates.push_back(state);
		}
	}
	return targetStates;
}

NodeSet<std::string> InterpreterImpl::getTargetStates(const Arabica::XPath::NodeSet<std::string>& transitions) {
	NodeSet<std::string> targets;
	for (unsigned int i = 0; i < transitions.size(); i++) {
		targets.push_back(getTargetStates(transitions[i]));
	}
	return targets;
}

std::list<std::string> InterpreterImpl::tokenizeIdRefs(const std::string& idRefs) {
	std::list<std::string> ids;

	// appr. 3x faster than stringstream
	size_t start = 0;
	for (int i = 0; i < idRefs.size(); i++) {
		if (isspace(idRefs[i])) {
			if (i > 0 && start < i - 1) {
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
	std::istringstream iss(text);
	std::stringstream content;
	std::string seperator;
	do {
		std::string token;
		iss >> token;
		if (token.length() > 0) {
			content << seperator << token;
			seperator = " ";
		}
	} while (iss);
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
		if (childs.item(i).getNodeType() == Node_base::ELEMENT_NODE) {
//		std::cout << TAGNAME(childs.item(i)) << std::endl;
			if(iequals(TAGNAME(childs.item(i)), tagName)) {
				filteredChildElems.push_back(childs.item(i));
			}
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
	NodeSet<std::string> ancestors;
	if (isState(s1)) {
		Arabica::DOM::Node<std::string> node = s1;
		while((node = node.getParentNode())) {
			if (!isState(node))
				break;
			if (iequals(TAGNAME(node), _nsInfo.xmlNSPrefix + "scxml")) // do not return scxml root itself - this is somewhat ill-defined
				break;
			if (!iequals(TAGNAME(node), _nsInfo.xmlNSPrefix + "parallel") &&
			        !iequals(TAGNAME(node), _nsInfo.xmlNSPrefix + "state") &&
			        !iequals(TAGNAME(node), _nsInfo.xmlNSPrefix + "scxml"))
				break;
			if (node == s2)
				break;
			ancestors.push_back(node);
		}
	}
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

bool InterpreterImpl::isTargetless(const Arabica::DOM::Node<std::string>& transition) {
	if (transition.hasAttributes()) {
		if (((Arabica::DOM::Element<std::string>)transition).hasAttribute("target"))
			return false;
	}
	return true;
}

bool InterpreterImpl::isState(const Arabica::DOM::Node<std::string>& state) {
	if (!state)
		return false;
	if (state.getNodeType() != Arabica::DOM::Node_base::ELEMENT_NODE)
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

bool InterpreterImpl::isFinal(const Arabica::DOM::Node<std::string>& state) {
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

bool InterpreterImpl::isInitial(const Arabica::DOM::Node<std::string>& state) {
	if (!isState(state))
		return false;

	Arabica::DOM::Node<std::string> parent = state.getParentNode();
	if (!isState(parent))
		return true; // scxml element

	if (isMember(state, getInitialStates(parent)))
		return true; // every nested node

	return false;
}

bool InterpreterImpl::isPseudoState(const Arabica::DOM::Node<std::string>& state) {
	std::string tagName = LOCALNAME(state);
	if (iequals("initial", tagName))
		return true;
	if (iequals("history", tagName))
		return true;
	return false;
}

bool InterpreterImpl::isTransitionTarget(const Arabica::DOM::Node<std::string>& elem) {
	return (isState(elem) || iequals(LOCALNAME(elem), "history"));
}

bool InterpreterImpl::isAtomic(const Arabica::DOM::Node<std::string>& state) {
	if (iequals("final", LOCALNAME(state)))
		return true;

	if (iequals("parallel", LOCALNAME(state)))
		return false;

	Arabica::DOM::NodeList<std::string> childs = state.getChildNodes();
	for (unsigned int i = 0; i < childs.getLength(); i++) {
		if (isState(childs.item(i)))
			return false;
	}
	return true;
}

bool InterpreterImpl::isHistory(const Arabica::DOM::Node<std::string>& state) {
	if (iequals("history", LOCALNAME(state)))
		return true;
	return false;
}

bool InterpreterImpl::isParallel(const Arabica::DOM::Node<std::string>& state) {
	if (!isState(state))
		return false;
	if (iequals("parallel", LOCALNAME(state)))
		return true;
	return false;
}


bool InterpreterImpl::isCompound(const Arabica::DOM::Node<std::string>& state) {
	if (!isState(state))
		return false;

	if (iequals(LOCALNAME(state), "parallel")) // parallel is no compound state
		return false;

	Arabica::DOM::NodeList<std::string> childs = state.getChildNodes();
	for (unsigned int i = 0; i < childs.getLength(); i++) {
		if (isState(childs.item(i)))
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
			if (!boost::equal(*nameIter, ioProcIter->first))
				_ioProcessors[*nameIter] = _ioProcessors[ioProcIter->first];
			nameIter++;
		}
#if 0
		if (_dataModel) {
			try {
				_dataModel.registerIOProcessor(ioProcIter->first, _ioProcessors[ioProcIter->first]);
			} catch (Event e) {
				LOG(ERROR) << "Syntax error when setting _ioprocessors:" << std::endl << e << std::endl;
			}
		} else {
			LOG(INFO) << "Not registering " << ioProcIter->first << " at _ioprocessors in datamodel, no datamodel specified";
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

bool InterpreterImpl::isLegalConfiguration(const std::vector<std::string>& config) {
	NodeSet<std::string> states;
	for (int i = 0; i < config.size(); i++) {
		Node<std::string> state = getState(config[i]);
		if (!state) {
			LOG(INFO) << "No state with id '" << config[i] << "'";
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

#if VERBOSE
	std::cout << "Checking whether {";
	std::string seperator;
	for (int i = 0; i < config.size(); i++) {
		std::cout << seperator << ATTR(config[i], "id");
		seperator = ", ";
	}
	std::cout << "} is legal" << std::endl;
#endif

	// The configuration contains exactly one child of the <scxml> element.
	NodeSet<std::string> scxmlChilds = getChildStates(_scxml);
	bool foundScxmlChild = false;
	for (int i = 0; i < scxmlChilds.size(); i++) {
		if (isMember(scxmlChilds[i], config)) {
			if (foundScxmlChild)
				return false;
			foundScxmlChild = true;
		}
	}
	if (!foundScxmlChild)
		return false;

	// The configuration contains one or more atomic states.
	bool foundAtomicState = false;
	for (int i = 0; i < config.size(); i++) {
		if (isAtomic(config[i])) {
			foundAtomicState = true;
			break;
		}
	}
	if (!foundAtomicState)
		return false;

	// When the configuration contains an atomic state, it contains all of its <state> and <parallel> ancestors.
	for (int i = 0; i < config.size(); i++) {
		if (isAtomic(config[i])) {
			Node<std::string> parent = config[i];
			while((parent = parent.getParentNode())) {
				if (isState(parent) &&
				        (iequals(LOCALNAME(parent), "state") ||
				         iequals(LOCALNAME(parent), "parallel"))) {
					if (!isMember(parent, config))
						return false;
				}
			}
		}
	}

	// When the configuration contains a non-atomic <state>, it contains one and only one of the state's children
	for (int i = 0; i < config.size(); i++) {
		if (!isAtomic(config[i]) && !isParallel(config[i])) {
			bool foundChildState = false;
			//std::cout << config[i] << std::endl;
			NodeSet<std::string> childs = getChildStates(config[i]);
			for (int j = 0; j < childs.size(); j++) {
				//std::cout << childs[j] << std::endl;
				if (isMember(childs[j], config)) {
					if (foundChildState)
						return false;
					foundChildState = true;
				}
			}
			if (!foundChildState)
				return false;
		}
	}

	// If the configuration contains a <parallel> state, it contains all of its children
	for (int i = 0; i < config.size(); i++) {
		if (isParallel(config[i])) {
			NodeSet<std::string> childs = getChildStates(config[i]);
			for (int j = 0; j < childs.size(); j++) {
				if (!isMember(childs[j], config) && !isHistory(childs[j])) {
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
		if (_configuration.size() > 0 && HAS_ATTR(_configuration[0], "id")) {
			// all states are encoded in the current statename
			std::string encStateList = ATTR(_configuration[0], "id");
			size_t startActive = encStateList.find_first_of("-");
			size_t endActive = encStateList.find_first_of(";");
			encStateList = encStateList.substr(startActive, endActive - startActive);
			std::stringstream ss(encStateList);
			std::string unencodedStateId;
			while(std::getline(ss, unencodedStateId, '-')) {
				if (unencodedStateId.length() == 0)
					continue;
				if (iequals(unencodedStateId, stateId)) {
					return true;
				}
			}
		}
		return false;
	} else {

		for (int i = 0; i < _configuration.size(); i++) {
			if (HAS_ATTR(_configuration[i], "id") &&
			        iequals(ATTR(_configuration[i], "id"), stateId)) {
				return true;
			}
		}
	}
	return false;
}

void InterpreterImpl::DOMEventListener::handleEvent(Arabica::DOM::Events::Event<std::string>& event) {
	// remove modified states from cache
	if (event.getType().compare("DOMAttrModified") == 0) // we do not care about attributes
		return;
	Node<std::string> target = Arabica::DOM::Node<std::string>(event.getTarget());
	NodeSet<std::string> childs = InterpreterImpl::filterChildElements(_interpreter->_nsInfo.xmlNSPrefix + "state", target);
	for (int i = 0; i < childs.size(); i++) {
		if (HAS_ATTR(childs[i], "id")) {
			_interpreter->_cachedStates.erase(ATTR(childs[i], "id"));
		}
	}
}

std::ostream& operator<< (std::ostream& os, const InterpreterState& interpreterState) {
	os << "[" << InterpreterState::stateToString(interpreterState.state) << "]:" << std::endl;
	os << interpreterState.msg;
	return os;
}

std::string InterpreterState::stateToString(int32_t state) {
	std::stringstream ss;

	switch(state & USCXML_INTERPRETER_MASK) {
	case USCXML_INSTANTIATED:
		ss << "INSTANTIATED";
		break;
	case USCXML_FAULTED:
		ss << "FAULTED";
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

	if (state & USCXML_THREAD_STARTED) {
		ss << ", " << "STARTED";
	} else {
		ss << ", " << "STOPPED";
	}
	if (state & USCXML_THREAD_RUNNING) {
		ss << ", " << "RUNNING";
	} else {
		ss << ", " << "JOINED";
	}

	return ss.str();
}


}
