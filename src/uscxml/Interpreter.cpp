#include "uscxml/Common.h"
#include "uscxml/Interpreter.h"
#include "uscxml/URL.h"
#include "uscxml/debug/SCXMLDotWriter.h"

#include "uscxml/plugins/invoker/http/HTTPServletInvoker.h"

#include <DOM/Simple/DOMImplementation.hpp>
#include <SAX/helpers/InputSourceResolver.hpp>

#include <boost/uuid/uuid.hpp>
#include <boost/uuid/uuid_generators.hpp>
#include <boost/uuid/uuid_io.hpp>
#include <boost/lexical_cast.hpp>
#include <boost/tokenizer.hpp>

#include <glog/logging.h>

#include <assert.h>
#include <algorithm>

#define VERBOSE 0

namespace uscxml {

using namespace Arabica::XPath;
using namespace Arabica::DOM;

boost::uuids::random_generator Interpreter::uuidGen;
const std::string Interpreter::getUUID() {
	return boost::lexical_cast<std::string>(uuidGen());
}

Interpreter::Interpreter() : Arabica::SAX2DOM::Parser<std::string>() {
	_lastRunOnMainThread = 0;
	_nsURL = "*";
	_thread = NULL;
	_sendQueue = NULL;
	_parentQueue = NULL;
	_running = false;
	_done = false;
	_isInitialized = false;
	_httpServlet = NULL;
	_capabilities = CAN_BASIC_HTTP | CAN_GENERIC_HTTP;

#ifdef _WIN32
	WSADATA wsaData;
	WSAStartup(MAKEWORD(2, 2), &wsaData);
#endif
}

Interpreter* Interpreter::fromDOM(const Arabica::DOM::Node<std::string>& node) {
	Arabica::DOM::DOMImplementation<std::string> domFactory = Arabica::SimpleDOM::DOMImplementation<std::string>::getDOMImplementation();
	Interpreter* interpreter = new Interpreter();
	interpreter->_document = domFactory.createDocument("http://www.w3.org/2005/07/scxml", "scxml", 0);
	interpreter->_document.appendChild(node);
	interpreter->init();

	return interpreter;
}

Interpreter* Interpreter::fromXML(const std::string& xml) {
	std::istringstream is(xml);
	is.seekg(0);
	Arabica::SAX::InputSource<std::string> inputSource;
	inputSource.setByteStream(is);
	return fromInputSource(inputSource);
}

Interpreter* Interpreter::fromURI(const std::string& uri) {
	URL absUrl(uri);
	if (!absUrl.isAbsolute()) {
		if (!absUrl.toAbsoluteCwd()) {
			LOG(ERROR) << "Given URL is not absolute or does not have file schema";
			return NULL;
		}
	}
	Arabica::SAX::InputSource<std::string> inputSource;

	// this is required for windows filenames and does not harm on unices
	if (boost::iequals(absUrl.scheme(), "file")) {
		inputSource.setSystemId(absUrl.path());
	} else if (boost::iequals(absUrl.scheme(), "http")) {
		// handle http per arabica
		inputSource.setSystemId(absUrl.asString());
	} else {
		// use curl for everything else
		std::stringstream ss;
		ss << absUrl;
		if (absUrl.downloadFailed()) {
			return NULL;
		}
		ss.seekg(0);
		inputSource.setByteStream(ss);
	}
	Interpreter* interpreter = fromInputSource(inputSource);

	// try to establish URI root for relative src attributes in document
	if (interpreter)
		interpreter->_baseURI = toBaseURI(absUrl);
	return interpreter;
}

void Interpreter::setName(const std::string& name) {
	if (!_running) {
		_name = name;
	} else {
		LOG(ERROR) << "Cannot change name of running interpreter";
	}
}

URL Interpreter::toBaseURI(const URL& uri) {
	std::stringstream ssBaseURI;
	if (uri.scheme().size() > 0) {
		ssBaseURI << uri.scheme() << "://";
	} else {
		ssBaseURI << "file://";
	}
	if (uri.host().size() > 0) {
		ssBaseURI << uri.host();
		if (!boost::iequals(uri.port(), "0"))
			ssBaseURI << ":" << uri.port();
	}
	if (uri.path().size() > 0) {
		std::string uriPath = uri.path();
		uriPath = uriPath.substr(0, uriPath.find_last_of("/\\") + 1);
		ssBaseURI << uriPath;
	}
	return URL(ssBaseURI.str());
}

bool Interpreter::toAbsoluteURI(URL& uri) {
	if (uri.isAbsolute())
		return true;

	if (_baseURI.asString().size() > 0) {
		if (uri.toAbsolute(_baseURI))
			return true;
		return false;
	}
	return false;
}

void Interpreter::startPrefixMapping(const std::string& prefix, const std::string& uri) {
#if 0
	std::cout << "starting prefix mapping " << prefix << ": " << uri << std::endl;
#endif
	if (boost::iequals(uri, "http://www.w3.org/2005/07/scxml")) {
		_nsURL = uri;
		if (prefix.size() == 0) {
			LOG(INFO) << "Mapped default namespace to 'scxml:'";
			_xpathPrefix = "scxml:";
			_nsContext.addNamespaceDeclaration(uri, "scxml");
			_nsToPrefix[uri] = "scxml";
		} else {
			_xpathPrefix = prefix + ":";
			_xmlNSPrefix = _xpathPrefix;
			_nsContext.addNamespaceDeclaration(uri, prefix);
			_nsToPrefix[uri] = prefix;
		}
	} else {
		_nsContext.addNamespaceDeclaration(uri, prefix);
		_nsToPrefix[uri] = prefix;
	}
}

Interpreter* Interpreter::fromInputSource(Arabica::SAX::InputSource<std::string>& source) {
	Interpreter* interpreter = new Interpreter();

	Arabica::SAX::CatchErrorHandler<std::string> errorHandler;
	interpreter->setErrorHandler(errorHandler);
	if(!interpreter->parse(source) || !interpreter->Arabica::SAX2DOM::Parser<std::string>::getDocument().hasChildNodes()) {
		if(errorHandler.errorsReported()) {
			LOG(ERROR) << "could not parse input:";
			LOG(ERROR) << errorHandler.errors() << std::endl;
		} else {
			Arabica::SAX::InputSourceResolver resolver(source, Arabica::default_string_adaptor<std::string>());
			if (!resolver.resolve()) {
				LOG(ERROR) << source.getSystemId() << ": no such file";
			}
		}
		delete interpreter;
		return NULL;
	} else {
		interpreter->_document = interpreter->Arabica::SAX2DOM::Parser<std::string>::getDocument();
	}
//	interpreter->init();
	return interpreter;
}

void Interpreter::init() {
	if (_document) {
		NodeList<std::string> scxmls = _document.getElementsByTagNameNS(_nsURL, "scxml");
		if (scxmls.getLength() > 0) {
			_scxml = (Arabica::DOM::Element<std::string>)scxmls.item(0);

			// setup xpath and check that it works
			_xpath.setNamespaceContext(_nsContext);
			Arabica::XPath::NodeSet<std::string> scxmls = _xpath.evaluate("/" + _xpathPrefix + "scxml", _document).asNodeSet();
			assert(scxmls.size() > 0);
			assert(scxmls[0] == _scxml);

			if (_name.length() == 0)
				_name = (HAS_ATTR(_scxml, "name") ? ATTR(_scxml, "name") : getUUID());

			normalize(_document);

			if (_capabilities & CAN_GENERIC_HTTP)
				_httpServlet = new HTTPServletInvoker(this);

			_sendQueue = new DelayedEventQueue();
			_sendQueue->start();

		} else {
			LOG(ERROR) << "Cannot find SCXML element" << std::endl;
		}
	}
	_isInitialized = true;
}

Interpreter::~Interpreter() {
	if (_thread) {
		_running = false;
		Event event;
		_externalQueue.push(event);
		_thread->join();
		delete(_thread);
	}
	if (_sendQueue)
		delete _sendQueue;
	if (_httpServlet)
		delete _httpServlet;
}

void Interpreter::start() {
	_done = false;
	_thread = new tthread::thread(Interpreter::run, this);
}

void Interpreter::run(void* instance) {
	((Interpreter*)instance)->interpret();
}

bool Interpreter::runOnMainThread(int fps, bool blocking) {
	if (_done)
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

	tthread::lock_guard<tthread::mutex> lock(_mutex);
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

	return (_thread != NULL);
}

// see: http://www.w3.org/TR/scxml/#AlgorithmforSCXMLInterpretation
void Interpreter::interpret() {
	if (!_isInitialized)
		init();

	if (!_scxml)
		return;
//  dump();
	
	_sessionId = getUUID();

	std::string datamodelName;
	if (datamodelName.length() == 0 && HAS_ATTR(_scxml, "datamodel"))
		datamodelName = ATTR(_scxml, "datamodel");
	if (datamodelName.length() == 0 && HAS_ATTR(_scxml, "profile")) // SCION SCXML uses profile to specify datamodel
		datamodelName = ATTR(_scxml, "profile");
	_dataModel = Factory::createDataModel(datamodelName, this);
	if(datamodelName.length() > 0  && !_dataModel) {
		LOG(ERROR) << "No datamodel for " << datamodelName << " registered";
	}

	if (_dataModel) {
		_dataModel.assign("_x.args", _cmdLineOptions);
		if (_httpServlet)
			_dataModel.assign("_ioprocessors['http']", _httpServlet->getDataModelVariables());
	}

	setupIOProcessors();

	_running = true;
	_binding = (HAS_ATTR(_scxml, "binding") && boost::iequals(ATTR(_scxml, "binding"), "late") ? LATE : EARLY);

	// @TODO: Reread http://www.w3.org/TR/scxml/#DataBinding

	if (_dataModel && _binding == EARLY) {
		// initialize all data elements
		NodeSet<std::string> dataElems = _xpath.evaluate("//" + _xpathPrefix + "data", _document).asNodeSet();
		for (unsigned int i = 0; i < dataElems.size(); i++) {
			initializeData(dataElems[i]);
		}
	} else if(_dataModel) {
		// initialize current data elements
		NodeSet<std::string> topDataElems = filterChildElements(_xmlNSPrefix + "data", filterChildElements(_xmlNSPrefix + "datamodel", _scxml));
		for (unsigned int i = 0; i < topDataElems.size(); i++) {
			initializeData(topDataElems[i]);
		}
	}

	// executeGlobalScriptElements
	NodeSet<std::string> globalScriptElems = _xpath.evaluate("/" + _xpathPrefix + "scxml/" + _xpathPrefix + "script", _document).asNodeSet();
	for (unsigned int i = 0; i < globalScriptElems.size(); i++) {
		if (_dataModel)
			executeContent(globalScriptElems[i]);
	}

	// initial transition might be implict
	NodeSet<std::string> initialTransitions = _xpath.evaluate("/" + _xpathPrefix + "scxml/" + _xpathPrefix + "initial/" + _xpathPrefix + "transition", _document).asNodeSet();
	if (initialTransitions.size() == 0) {
		Arabica::DOM::Element<std::string> initialState = (Arabica::DOM::Element<std::string>)getInitialState();
		Arabica::DOM::Element<std::string> initialElem = _document.createElementNS(_nsURL, "initial");
		initialElem.setAttribute("generated", "true");
		Arabica::DOM::Element<std::string> transitionElem = _document.createElementNS(_nsURL, "transition");
		transitionElem.setAttribute("target", initialState.getAttribute("id"));
		initialElem.appendChild(transitionElem);
		_scxml.appendChild(initialElem);
		initialTransitions.push_back(transitionElem);
	}
	enterStates(initialTransitions);

//  assert(hasLegalConfiguration());
	mainEventLoop();

	// set datamodel to null from this thread
	if(_dataModel)
		_dataModel = DataModel();

}

/**
 * Called with a single data element from the topmost datamodel element.
 */
void Interpreter::initializeData(const Arabica::DOM::Node<std::string>& data) {
	if (!_dataModel) {
		LOG(ERROR) << "Cannot initialize data when no datamodel is given!";
		return;
	}
	try {
		if (!HAS_ATTR(data, "id")) {
			LOG(ERROR) << "Data element has no id!";
			return;
		}

		if (HAS_ATTR(data, "expr")) {
			std::string value = ATTR(data, "expr");
			_dataModel.assign(ATTR(data, "id"), value);
		} else if (HAS_ATTR(data, "src")) {
			URL srcURL(ATTR(data, "src"));
			if (!srcURL.isAbsolute())
				toAbsoluteURI(srcURL);

			std::stringstream ss;
			if (_cachedURLs.find(srcURL.asString()) != _cachedURLs.end()) {
				ss << _cachedURLs[srcURL.asString()];
			} else {
				ss << srcURL;
				_cachedURLs[srcURL.asString()] = srcURL;
			}
			_dataModel.assign(ATTR(data, "id"), ss.str());

		} else if (data.hasChildNodes()) {
			// search for the text node with the actual script
			NodeList<std::string> dataChilds = data.getChildNodes();
			for (int i = 0; i < dataChilds.getLength(); i++) {
				if (dataChilds.item(i).getNodeType() == Node_base::TEXT_NODE) {
					Data value = Data(dataChilds.item(i).getNodeValue());
					_dataModel.assign(ATTR(data, "id"), value);
					break;
				}
			}
		}

	} catch (Event e) {
		LOG(ERROR) << "Syntax error in data element:" << std::endl << e << std::endl;
	}
}

void Interpreter::normalize(const Arabica::DOM::Document<std::string>& node) {
	// make sure every state has an id and set isFirstEntry to true
	Arabica::XPath::NodeSet<std::string> states = _xpath.evaluate("//" + _xpathPrefix + "state", _document).asNodeSet();
	for (int i = 0; i < states.size(); i++) {
		Arabica::DOM::Element<std::string> stateElem = Arabica::DOM::Element<std::string>(states[i]);
		stateElem.setAttribute("isFirstEntry", "true");
		if (!stateElem.hasAttribute("id")) {
			stateElem.setAttribute("id", getUUID());
		}
	}

	// make sure every invoke has an idlocation or id
	Arabica::XPath::NodeSet<std::string> invokes = _xpath.evaluate("//" + _xpathPrefix + "invoke", _document).asNodeSet();
	for (int i = 0; i < invokes.size(); i++) {
		Arabica::DOM::Element<std::string> invokeElem = Arabica::DOM::Element<std::string>(invokes[i]);
		if (!invokeElem.hasAttribute("id") && !invokeElem.hasAttribute("idlocation")) {
			invokeElem.setAttribute("id", getUUID());
		}
//    // make sure every finalize element contained has the invoke id as an attribute
//    Arabica::XPath::NodeSet<std::string> finalizes = _xpath.evaluate("" + _xpathPrefix + "finalize", invokeElem).asNodeSet();
//    for (int j = 0; j < finalizes.size(); j++) {
//      Arabica::DOM::Element<std::string> finalizeElem = Arabica::DOM::Element<std::string>(finalizes[j]);
//      finalizeElem.setAttribute("invokeid", invokeElem.getAttribute("id"));
//    }
	}

	Arabica::XPath::NodeSet<std::string> finals = _xpath.evaluate("//" + _xpathPrefix + "final", _document).asNodeSet();
	for (int i = 0; i < finals.size(); i++) {
		Arabica::DOM::Element<std::string> finalElem = Arabica::DOM::Element<std::string>(finals[i]);
		finalElem.setAttribute("isFirstEntry", "true");
		if (!finalElem.hasAttribute("id")) {
			finalElem.setAttribute("id", getUUID());
		}
	}

	Arabica::XPath::NodeSet<std::string> histories = _xpath.evaluate("//" + _xpathPrefix + "history", _document).asNodeSet();
	for (int i = 0; i < histories.size(); i++) {
		Arabica::DOM::Element<std::string> historyElem = Arabica::DOM::Element<std::string>(histories[i]);
		if (!historyElem.hasAttribute("id")) {
			historyElem.setAttribute("id", getUUID());
		}
	}

	Arabica::XPath::NodeSet<std::string> scxml = _xpath.evaluate("/" + _xpathPrefix + "scxml", _document).asNodeSet();
	if (!((Arabica::DOM::Element<std::string>)scxml[0]).hasAttribute("id")) {
		((Arabica::DOM::Element<std::string>)scxml[0]).setAttribute("id", getUUID());
	}

	// create a pseudo initial and transition element
#if 0
	Arabica::DOM::Element<std::string> initialState = (Arabica::DOM::Element<std::string>)getInitialState();
	Arabica::DOM::Element<std::string> initialElem = _document.createElement("initial");
	Arabica::DOM::Element<std::string> transitionElem = _document.createElement("transition");
	transitionElem.setAttribute("target", initialState.getAttribute("id"));
	initialElem.appendChild(transitionElem);
	_scxml.appendChild(initialElem);
	std::cout << _scxml <<std::endl;
#endif
}

void Interpreter::mainEventLoop() {
	std::set<InterpreterMonitor*>::iterator monIter;

	while(_running) {
		NodeSet<std::string> enabledTransitions;
		_stable = false;

		// Here we handle eventless transitions and transitions
		// triggered by internal events until machine is stable
		while(_running && !_stable) {
#if 0
			std::cout << "Configuration: ";
			for (int i = 0; i < _configuration.size(); i++) {
				std::cout << ATTR(_configuration[i], "id") << ", ";
			}
			std::cout << std::endl;
#endif
			monIter = _monitors.begin();
			while(monIter != _monitors.end()) {
				try {
					(*monIter)->beforeMicroStep(this);
				} catch (Event e) {
					LOG(ERROR) << "Syntax error when calling beforeMicroStep on monitors: " << std::endl << e << std::endl;
				} catch (...) {
					LOG(ERROR) << "An exception occured when calling beforeMicroStep on monitors";
				}
				monIter++;
			}

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
					if (_dataModel)
						_dataModel.setEvent(_currEvent);
					enabledTransitions = selectTransitions(_currEvent.name);
				}
			}
			if (!enabledTransitions.empty()) {
				monIter = _monitors.begin();
				while(monIter != _monitors.end()) {
					try {
						(*monIter)->beforeTakingTransitions(this, enabledTransitions);
					} catch (Event e) {
						LOG(ERROR) << "Syntax error when calling beforeTakingTransitions on monitors: " << std::endl << e << std::endl;
					} catch (...) {
						LOG(ERROR) << "An exception occured when calling beforeTakingTransitions on monitors";
					}
					monIter++;
				}
				microstep(enabledTransitions);
			}
		}

		for (unsigned int i = 0; i < _statesToInvoke.size(); i++) {
			NodeSet<std::string> invokes = filterChildElements(_xmlNSPrefix + "invoke", _statesToInvoke[i]);
			for (unsigned int j = 0; j < invokes.size(); j++) {
				invoke(invokes[j]);
			}
		}

		_statesToInvoke = NodeSet<std::string>();
		if (!_internalQueue.empty())
			continue;

		// assume that we have a legal configuration as soon as the internal queue is empty
//    assert(hasLegalConfiguration());

		monIter = _monitors.begin();
//    if (!_sendQueue || _sendQueue->isEmpty()) {
		while(monIter != _monitors.end()) {
			try {
				(*monIter)->onStableConfiguration(this);
			} catch (Event e) {
				LOG(ERROR) << "Syntax error when calling onStableConfiguration on monitors: " << std::endl << e << std::endl;
			} catch (...) {
				LOG(ERROR) << "An exception occured when calling onStableConfiguration on monitors";
			}
			monIter++;
		}
//    }

		// whenever we have a stable configuration, run the mainThread hooks with 200fps
		while(_externalQueue.isEmpty() && _thread == NULL) {
			runOnMainThread(200);
		}

		_currEvent = _externalQueue.pop();
#if VERBOSE
		std::cout << "Received externalEvent event " << _currEvent.name << std::endl;
#endif
		_currEvent.type = Event::EXTERNAL; // make sure it is set to external
		if (!_running)
			exitInterpreter();

		if (_dataModel && boost::iequals(_currEvent.name, "cancel.invoke." + _sessionId))
			break;

		if (_dataModel)
			try {
				_dataModel.setEvent(_currEvent);
			} catch (Event e) {
				LOG(ERROR) << "Syntax error while setting external event:" << std::endl << e << std::endl;
			}
		for (unsigned int i = 0; i < _configuration.size(); i++) {
			NodeSet<std::string> invokes = filterChildElements(_xmlNSPrefix + "invoke", _configuration[i]);
			for (unsigned int j = 0; j < invokes.size(); j++) {
				Arabica::DOM::Element<std::string> invokeElem = (Arabica::DOM::Element<std::string>)invokes[j];
				std::string invokeId;
				if (HAS_ATTR(invokeElem, "id"))
					invokeId = ATTR(invokeElem, "id");
				if (HAS_ATTR(invokeElem, "idlocation") && _dataModel)
					invokeId = _dataModel.evalAsString(ATTR(invokeElem, "idlocation"));

				std::string autoForward = invokeElem.getAttribute("autoforward");
				if (boost::iequals(invokeId, _currEvent.invokeid)) {

					Arabica::XPath::NodeSet<std::string> finalizes = filterChildElements(_xmlNSPrefix + "finalize", invokeElem);
					for (int k = 0; k < finalizes.size(); k++) {
						Arabica::DOM::Element<std::string> finalizeElem = Arabica::DOM::Element<std::string>(finalizes[k]);
						executeContent(finalizeElem);
					}

				}
				if (boost::iequals(autoForward, "true")) {
					try {
						_invokers[invokeId].send(_currEvent);
					} catch(...) {
						LOG(ERROR) << "Exception caught while sending event to invoker " << invokeId;
					}
				}
			}
		}
		enabledTransitions = selectTransitions(_currEvent.name);
		if (!enabledTransitions.empty())
			microstep(enabledTransitions);
	}
	monIter = _monitors.begin();
	while(monIter != _monitors.end()) {
		try {
			(*monIter)->beforeCompletion(this);
		} catch (Event e) {
			LOG(ERROR) << "Syntax error when calling beforeCompletion on monitors: " << std::endl << e << std::endl;
		} catch (...) {
			LOG(ERROR) << "An exception occured when calling beforeCompletion on monitors";
		}
		monIter++;
	}

	exitInterpreter();

	monIter = _monitors.begin();
	while(monIter != _monitors.end()) {
		try {
			(*monIter)->afterCompletion(this);
		} catch (Event e) {
			LOG(ERROR) << "Syntax error when calling afterCompletion on monitors: " << std::endl << e << std::endl;
		} catch (...) {
			LOG(ERROR) << "An exception occured when calling afterCompletion on monitors";
		}
		monIter++;
	}

}

void Interpreter::internalDoneSend(const Arabica::DOM::Node<std::string>& state) {
	if (!isState(state))
		return;

	Arabica::DOM::Element<std::string> stateElem = (Arabica::DOM::Element<std::string>)state;
	Arabica::DOM::Element<std::string> parent = (Arabica::DOM::Element<std::string>)stateElem.getParentNode();
	Event event;

	Arabica::XPath::NodeSet<std::string> doneDatas = filterChildElements(_xmlNSPrefix + "donedata", stateElem);
	if (doneDatas.size() > 0) {
		// only process first donedata element
		Arabica::DOM::Node<std::string> doneData = doneDatas[0];
		NodeList<std::string> doneChilds = doneData.getChildNodes();
		for (int i = 0; i < doneChilds.getLength(); i++) {
			if (!doneChilds.item(i).getNodeType() == Node_base::ELEMENT_NODE)
				continue;
			if (boost::iequals(TAGNAME(doneChilds.item(i)), _xmlNSPrefix + "param")) {
				if (!HAS_ATTR(doneChilds.item(i), "name")) {
					LOG(ERROR) << "param element is missing name attribut";
					continue;
				}
				std::string paramValue;
				if (HAS_ATTR(doneChilds.item(i), "expr") && _dataModel) {
					std::string location = _dataModel.evalAsString(ATTR(doneChilds.item(i), "expr"));
					paramValue = _dataModel.evalAsString(location);
				} else if(HAS_ATTR(doneChilds.item(i), "location") && _dataModel) {
					paramValue = _dataModel.evalAsString(ATTR(doneChilds.item(i), "location"));
				} else {
					LOG(ERROR) << "param element is missing expr or location or no datamodel is specified";
					continue;
				}
				event.data.compound[ATTR(doneChilds.item(i), "name")] = paramValue;
			}
			if (boost::iequals(TAGNAME(doneChilds.item(i)), _xmlNSPrefix + "content")) {
				if (HAS_ATTR(doneChilds.item(i), "expr")) {
					if (_dataModel) {
						event.data.compound["content"] = Data(_dataModel.evalAsString(ATTR(doneChilds.item(i), "expr")), Data::VERBATIM);
					} else {
						LOG(ERROR) << "content element has expr attribute but no datamodel is specified.";
					}
				} else if (doneChilds.item(i).hasChildNodes()) {
					event.data.compound["content"] = Data(doneChilds.item(i).getFirstChild().getNodeValue(), Data::VERBATIM);
				} else {
					LOG(ERROR) << "content element does not specify any content.";
				}

			}
		}
	}

	event.name = "done.state." + ATTR(stateElem.getParentNode(), "id"); // parent?!
	_internalQueue.push_back(event);

}

void Interpreter::send(const Arabica::DOM::Node<std::string>& element) {
	SendRequest sendReq;
	try {
		// event
		if (HAS_ATTR(element, "eventexpr") && _dataModel) {
			sendReq.name = _dataModel.evalAsString(ATTR(element, "eventexpr"));
		} else if (HAS_ATTR(element, "event")) {
			sendReq.name = ATTR(element, "event");
		}
	} catch (Event e) {
		LOG(ERROR) << "Syntax error in send element eventexpr:" << std::endl << e << std::endl;
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
		LOG(ERROR) << "Syntax error in send element targetexpr:" << std::endl << e << std::endl;
		return;
	}
	try {
		// type
		if (HAS_ATTR(element, "typeexpr") && _dataModel) {
			sendReq.type = _dataModel.evalAsString(ATTR(element, "typeexpr"));
		} else if (HAS_ATTR(element, "type")) {
			sendReq.type = ATTR(element, "type");
		} else {
			sendReq.type = "http://www.w3.org/TR/scxml/#SCXMLEventProcessor";
		}
	} catch (Event e) {
		LOG(ERROR) << "Syntax error in send element typeexpr:" << std::endl << e << std::endl;
		return;
	}
	try {
		// id
		if (HAS_ATTR(element, "idlocation") && _dataModel) {
			sendReq.sendid = _dataModel.evalAsString(ATTR(element, "idlocation"));
		} else if (HAS_ATTR(element, "id")) {
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
			sendReq.sendid = getUUID();
		}
		/** @TODO:
		 *
		 * If 'idlocation' is present, the SCXML Processor must generate an id when
		 * the parent <send> element is evaluated and store it in this location.
		 * See 3.14 IDs for details.
		 *
		 */
	} catch (Event e) {
		LOG(ERROR) << "Syntax error in send element idlocation:" << std::endl << e << std::endl;
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
			std::stringstream delayTime;
			if (delay.size() > 2 && boost::iequals("ms", delay.substr(delay.length() - 2, 2))) {
				delayTime << delay.substr(0, delay.size() - 2);
				delayTime >> sendReq.delayMs;
			} else if (delay.size() > 1 && boost::iequals("s", delay.substr(delay.length() - 1, 1))) {
				delayTime << delay.substr(0, delay.size() - 1);
				delayTime >> sendReq.delayMs;
				sendReq.delayMs *= 1000;
			} else {
				LOG(ERROR) << "Cannot make sense of delay value " << delay << ": does not end in 's' or 'ms'";
			}
		}
	} catch (Event e) {
		LOG(ERROR) << "Syntax error in send element delayexpr:" << std::endl << e << std::endl;
		return;
	}

	try {
		// namelist
		if (HAS_ATTR(element, "namelist")) {
			if (_dataModel) {
				std::vector<std::string> names = tokenizeIdRefs(ATTR(element, "namelist"));
				for (int i = 0; i < names.size(); i++) {
					std::string namelistValue = _dataModel.evalAsString(names[i]);
					sendReq.namelist[names[i]] = namelistValue;
					sendReq.data.compound[names[i]] = Data(namelistValue, Data::VERBATIM);
				}
			} else {
				LOG(ERROR) << "Namelist attribute at send requires datamodel to be defined";
			}
		}
	} catch (Event e) {
		LOG(ERROR) << "Syntax error in send element namelist:" << std::endl << e << std::endl;
		return;
	}

	try {
		// params
		NodeSet<std::string> params = filterChildElements(_xmlNSPrefix + "param", element);
		for (int i = 0; i < params.size(); i++) {
			if (!HAS_ATTR(params[i], "name")) {
				LOG(ERROR) << "param element is missing name attribute";
				continue;
			}
			std::string paramValue;
			if (HAS_ATTR(params[i], "expr") && _dataModel) {
				paramValue = _dataModel.evalAsString(ATTR(params[i], "expr"));
			} else if(HAS_ATTR(params[i], "location") && _dataModel) {
				paramValue = _dataModel.evalAsString(ATTR(params[i], "location"));
			} else {
				LOG(ERROR) << "param element is missing expr or location or no datamodel is specified";
				continue;
			}
			std::string paramKey = ATTR(params[i], "name");
			boost::algorithm::to_lower(paramKey);
			sendReq.params.insert(std::make_pair(paramKey, paramValue));
			sendReq.data.compound[paramKey] = Data(paramValue, Data::VERBATIM);
		}
	} catch (Event e) {
		LOG(ERROR) << "Syntax error in send element param expr:" << std::endl << e << std::endl;
		return;
	}
	try {

		// content
		NodeSet<std::string> contents = filterChildElements(_xmlNSPrefix + "content", element);
		if (contents.size() > 1)
			LOG(ERROR) << "Only a single content element is allowed for send elements - using first one";
		if (contents.size() > 0) {
			if (HAS_ATTR(contents[0], "expr")) {
				if (_dataModel) {
					std::string contentValue = _dataModel.evalAsString(ATTR(contents[0], "expr"));
					sendReq.content = contentValue;
//          sendReq.data.atom = contentValue;
//          sendReq.data.type = Data::VERBATIM;
				} else {
					LOG(ERROR) << "content element has expr attribute but no datamodel is specified.";
				}
			} else if (contents[0].hasChildNodes()) {
				sendReq.content = contents[0].getFirstChild().getNodeValue();
//        sendReq.data.atom = sendReq.content;
//        sendReq.data.type = Data::VERBATIM;
			} else {
				LOG(ERROR) << "content element does not specify any content.";
			}
		}
	} catch (Event e) {
		LOG(ERROR) << "Syntax error in send element content:" << std::endl << e << std::endl;
		return;
	}

	assert(_sendIds.find(sendReq.sendid) == _sendIds.end());
	_sendIds[sendReq.sendid] = std::make_pair(this, sendReq);
	if (sendReq.delayMs > 0) {
		_sendQueue->addEvent(sendReq.sendid, Interpreter::delayedSend, sendReq.delayMs, &_sendIds[sendReq.sendid]);
	} else {
		delayedSend(&_sendIds[sendReq.sendid], sendReq.name);
	}
}

void Interpreter::delayedSend(void* userdata, std::string eventName) {
	std::pair<Interpreter*, SendRequest>* data = (std::pair<Interpreter*, SendRequest>*)(userdata);

	Interpreter* INSTANCE = data->first;
	SendRequest sendReq = data->second;

	if (boost::iequals(sendReq.target, "#_parent")) {
		// send to parent scxml session
		if (INSTANCE->_parentQueue != NULL) {
			INSTANCE->_parentQueue->push(sendReq);
		} else {
			LOG(ERROR) << "Can not send to parent, we were not invoked" << std::endl;
		}
	} else if (boost::iequals(sendReq.target, "#_internal")) {
		INSTANCE->_internalQueue.push_back(sendReq);
	} else if (sendReq.target.find_first_of("#_") == 0) {
		// send to invoker
		std::string invokeId = sendReq.target.substr(2, sendReq.target.length() - 2);
		if (INSTANCE->_invokers.find(invokeId) != INSTANCE->_invokers.end()) {
			tthread::lock_guard<tthread::mutex> lock(INSTANCE->_mutex);
			try {
				INSTANCE->_invokers[invokeId].send(sendReq);
			} catch(...) {
				LOG(ERROR) << "Exception caught while sending event to invoker " << invokeId;
			}
		} else {
			LOG(ERROR) << "Can not send to invoked component '" << invokeId << "', no such invokeId" << std::endl;
		}
	} else if (sendReq.target.length() == 0) {
		INSTANCE->receive(sendReq);
	} else {
		IOProcessor ioProc = INSTANCE->getIOProcessor(sendReq.type);
		if (ioProc) {
			try {
				ioProc.send(sendReq);
			} catch(...) {
				LOG(ERROR) << "Exception caught while sending event to ioprocessor " << sendReq.type;
			}
		}
	}
	assert(INSTANCE->_sendIds.find(sendReq.sendid) != INSTANCE->_sendIds.end());
	INSTANCE->_sendIds.erase(sendReq.sendid);
}

void Interpreter::invoke(const Arabica::DOM::Node<std::string>& element) {
	InvokeRequest invokeReq;
	invokeReq.dom = element;

	try {
		// type
		if (HAS_ATTR(element, "typeexpr") && _dataModel) {
			invokeReq.type = _dataModel.evalAsString(ATTR(element, "typeexpr"));
		} else if (HAS_ATTR(element, "type")) {
			invokeReq.type = ATTR(element, "type");
		} else {
			LOG(ERROR) << "invoke element is missing expr or typeexpr or no datamodel is specified";
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
			if (!toAbsoluteURI(srcURI)) {
				LOG(ERROR) << "invoke element has relative src URI with no baseURI set.";
				return;
			}
			invokeReq.src = srcURI.asString();
		}

		// id
		if (HAS_ATTR(element, "idlocation") && _dataModel) {
			invokeReq.invokeid = _dataModel.evalAsString(ATTR(element, "idlocation"));
		} else if (HAS_ATTR(element, "id")) {
			invokeReq.invokeid = ATTR(element, "id");
		} else {
			assert(false);
		}

		// namelist
		if (HAS_ATTR(element, "namelist")) {
			std::vector<std::string> names = tokenizeIdRefs(ATTR(element, "namelist"));
			for (int i = 0; i < names.size(); i++) {
				invokeReq.namelist[names[i]] = _dataModel.evalAsString(names[i]);
			}
		}

		// autoforward
		if (HAS_ATTR(element, "autoforward")) {
			if (boost::iequals(ATTR(element, "autoforward"), "true")) {
				invokeReq.autoForward = true;
			}
		} else {
			invokeReq.autoForward = false;
		}

		// params
		NodeSet<std::string> params = filterChildElements(_xmlNSPrefix + "param", element);
		for (int i = 0; i < params.size(); i++) {
			if (!HAS_ATTR(params[i], "name")) {
				LOG(ERROR) << "param element is missing name attribut";
				continue;
			}
			std::string paramValue;
			if (HAS_ATTR(params[i], "expr")) {
				if (_dataModel) {
					paramValue = _dataModel.evalAsString(ATTR(params[i], "expr"));
				} else {
					LOG(ERROR) << "Cannot use param expr without a datamodel!";
				}
			} else if(HAS_ATTR(params[i], "location") && _dataModel) {
				paramValue = _dataModel.evalAsString(ATTR(params[i], "location"));
			} else {
				LOG(ERROR) << "param element is missing expr or location or no datamodel is specified";
				continue;
			}
			std::string paramKey = ATTR(params[i], "name");
			boost::algorithm::to_lower(paramKey);
			invokeReq.params.insert(std::make_pair(paramKey, paramValue));

		}

		// content
		NodeSet<std::string> contents = filterChildElements(_xmlNSPrefix + "content", element);
		if (contents.size() > 1)
			LOG(ERROR) << "Only a single content element is allowed for send elements - using first one";
		if (contents.size() > 0) {
			invokeReq.content = contents[0].getNodeValue();
		}

		Invoker invoker(Factory::createInvoker(invokeReq.type, this));
		if (invoker) {
			tthread::lock_guard<tthread::mutex> lock(_mutex);
			try {
				invoker.setInvokeId(invokeReq.invokeid);
				invoker.setType(invokeReq.type);
				invoker.setInterpreter(this);
				_invokers[invokeReq.invokeid] = invoker;
				LOG(INFO) << "Added invoker " << invokeReq.type << " at " << invokeReq.invokeid;
				try {
					invoker.invoke(invokeReq);
				} catch(...) {
					LOG(ERROR) << "Exception caught while sending invoke requst to invoker " << invokeReq.invokeid;
				}
				if (_dataModel) {
					try {
						_dataModel.assign("_invokers['" + invokeReq.invokeid + "']", invoker.getDataModelVariables());
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
		LOG(ERROR) << "Syntax error in invoke element:" << std::endl << e << std::endl;
	}
}

void Interpreter::cancelInvoke(const Arabica::DOM::Node<std::string>& element) {
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
				_dataModel.assign("_invokers['" + invokeId + "']", "''");
			} catch (Event e) {
				LOG(ERROR) << "Syntax when removing invoker:" << std::endl << e << std::endl;
			}

		}
		_invokers.erase(invokeId);
	} else {
		LOG(ERROR) << "Cannot cancel invoke for id " << invokeId << ": no soch invokation";
	}
}

Arabica::XPath::NodeSet<std::string> Interpreter::selectTransitions(const std::string& event) {
	Arabica::XPath::NodeSet<std::string> enabledTransitions;

	NodeSet<std::string> atomicStates;
	for (unsigned int i = 0; i < _configuration.size(); i++) {
		if (isAtomic(_configuration[i]))
			atomicStates.push_back(_configuration[i]);
	}
	atomicStates.to_document_order();

	for (unsigned int i = 0; i < atomicStates.size(); i++) {
		NodeSet<std::string> ancestors = getProperAncestors(atomicStates[i], Arabica::DOM::Node<std::string>());

		NodeSet<std::string> sortedAncestors;
		sortedAncestors.push_back(atomicStates[i]);
		sortedAncestors.insert(sortedAncestors.end(), ancestors.begin(), ancestors.end());

		for (unsigned int j = 0; j < sortedAncestors.size(); j++) {
			NodeSet<std::string> transitions = filterChildElements(_xmlNSPrefix + "transition", sortedAncestors[j]);
			for (unsigned int k = 0; k < transitions.size(); k++) {
				std::string eventName;
				if (HAS_ATTR(transitions[k], "event")) {
					eventName = ATTR(transitions[k], "event");
				} else if(HAS_ATTR(transitions[k], "eventexpr")) {
					if (_dataModel) {
						eventName = _dataModel.evalAsString(ATTR(transitions[k], "eventexpr"));
					} else {
						LOG(ERROR) << "Transition has eventexpr attribute with no datamodel defined";
						goto LOOP;
					}
				} else {
					goto LOOP;
				}

				if (eventName.length() > 0 &&
				        nameMatch(eventName, event) &&
				        hasConditionMatch(transitions[k])) {
					enabledTransitions.push_back(transitions[k]);
					goto LOOP;
				}
			}
		}
LOOP:
		;
	}

	enabledTransitions = filterPreempted(enabledTransitions);
	return enabledTransitions;
}

// see: http://www.w3.org/TR/scxml/#EventDescriptors
bool Interpreter::nameMatch(const std::string& transitionEvent, const std::string& event) {
	assert(transitionEvent.size() > 0);
	assert(event.size() > 0);

	// naive case of single descriptor and exact match
	if (boost::equals(transitionEvent, event))
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
		if (boost::equals(eventDesc, event))
			return true;

		// eventDesc has to be a real prefix of event now and therefore shorter
		if (eventDesc.size() >= event.size())
			continue;

		// it is a prefix of the event name and event continues with .something
		if (eventDesc.compare(event.substr(0, eventDesc.size())) == 0)
			if (event.find(".", eventDesc.size()) == eventDesc.size())
				return true;
	}
	return false;
}

Arabica::XPath::NodeSet<std::string> Interpreter::selectEventlessTransitions() {
	Arabica::XPath::NodeSet<std::string> enabledTransitions;

	NodeSet<std::string> atomicStates;
	for (unsigned int i = 0; i < _configuration.size(); i++) {
		if (isAtomic(_configuration[i]))
			atomicStates.push_back(_configuration[i]);
	}
	atomicStates.to_document_order();

	for (unsigned int i = 0; i < atomicStates.size(); i++) {
		NodeSet<std::string> ancestors = getProperAncestors(atomicStates[i], Arabica::DOM::Node<std::string>());
		ancestors.push_back(atomicStates[i]);
		for (unsigned int j = 0; j < ancestors.size(); j++) {
			NodeSet<std::string> transitions = filterChildElements(_xmlNSPrefix + "transition", ancestors[j]);
			for (unsigned int k = 0; k < transitions.size(); k++) {
				if (!HAS_ATTR(transitions[k], "event") && hasConditionMatch(transitions[k])) {
					enabledTransitions.push_back(transitions[k]);
					goto LOOP;
				}
			}

#if 0
			NodeSet<std::string> transitions = filterChildElements(_xmlNSPrefix + "transition", ancestors[j]);
			for (unsigned int k = 0; k < transitions.size(); k++) {
				if (!((Arabica::DOM::Element<std::string>)transitions[k]).hasAttribute("event") && hasConditionMatch(transitions[k])) {
					enabledTransitions.push_back(transitions[k]);
					goto LOOP;
				}
			}
#endif
		}
LOOP:
		;
	}

	enabledTransitions = filterPreempted(enabledTransitions);
	return enabledTransitions;
}

bool Interpreter::hasConditionMatch(const Arabica::DOM::Node<std::string>& conditional) {

	if (HAS_ATTR(conditional, "cond")) {
		if (!_dataModel) {
			LOG(ERROR) << "Cannot check a condition without a datamodel";
			return false;
		}
		try {
			return _dataModel.evalAsBool(ATTR(conditional, "cond"));
		} catch (Event e) {
			LOG(ERROR) << "Syntax error in cond attribute of " << TAGNAME(conditional) << " element:" << std::endl << e << std::endl;
			return false;
		}
	}
	return true; // no condition is always true
}

Arabica::XPath::NodeSet<std::string> Interpreter::filterPreempted(const Arabica::XPath::NodeSet<std::string>& enabledTransitions) {
	Arabica::XPath::NodeSet<std::string> filteredTransitions;
	for (unsigned int i = 0; i < enabledTransitions.size(); i++) {
		Arabica::DOM::Node<std::string> t = enabledTransitions[i];
		for (unsigned int j = i+1; j < enabledTransitions.size(); j++) {
			Arabica::DOM::Node<std::string> t2 = enabledTransitions[j];
			if (isPreemptingTransition(t2, t)) {
#if VERBOSE
				std::cout << "Transition preempted!: " << std::endl << t2 << std::endl << t << std::endl;
#endif
				goto LOOP;
			}
		}
		filteredTransitions.push_back(t);
LOOP:
		;
	}
	return filteredTransitions;
}

bool Interpreter::isPreemptingTransition(const Arabica::DOM::Node<std::string>& t1, const Arabica::DOM::Node<std::string>& t2) {
	assert(t1);
	assert(t2);

#if VERBOSE
	std::cout << "Checking preemption: " << std::endl << t1 << std::endl << t2 << std::endl;
#endif

#if 1
	if (t1 == t2)
		return false;
	if (isWithinSameChild(t1) && (!isTargetless(t2) && !isWithinSameChild(t2)))
		return true;
	if (!isTargetless(t1) && !isWithinSameChild(t1))
		return true;
	return false;
#endif

#if 0
	// isPreempted from chris nuernberger
	if (isTargetless(t1))
		return false;

	Arabica::DOM::Node<std::string> existingRoot = getTransitionSubgraph(t1);
	Arabica::DOM::Node<std::string> nextRoot = getTransitionSubgraph(t2);

	if (existingRoot == nextRoot || isDescendant(existingRoot, nextRoot) || isDescendant(nextRoot, existingRoot))
		return true;

	return false;
#endif
}

/**
 * filterPreempted approach from chris nuernberger
 */
#if 0
Arabica::DOM::Node<std::string> Interpreter::getTransitionSubgraph(const Arabica::DOM::Node<std::string>& transition) {
	Arabica::XPath::NodeSet<std::string> targets = getTargetStates(transition);
	Arabica::DOM::Node<std::string> source = getSourceState(transition);

	if (!targets.size() == 0)
		return source;

	if (boost::iequals(ATTR(transition, "type"), "internal") && isCompound(source)) {
		bool allDescendants = true;
		for (int i = 0; i < targets.size(); i++) {
			if (!isDescendant(targets[i], source)) {
				allDescendants = false;
				break;
			}
		}
		if (allDescendants)
			return source;
	}

	targets.push_back(source);
	return findLCCA(targets);
}
#endif

void Interpreter::microstep(const Arabica::XPath::NodeSet<std::string>& enabledTransitions) {
#if 0
	std::cout << "Transitions: ";
	for (int i = 0; i < enabledTransitions.size(); i++) {
		std::cout << ((Arabica::DOM::Element<std::string>)getSourceState(enabledTransitions[i])).getAttribute("id") << " -> " << std::endl;
		NodeSet<std::string> targetSet = getTargetStates(enabledTransitions[i]);
		for (int j = 0; j < targetSet.size(); j++) {
			std::cout << "    " << ((Arabica::DOM::Element<std::string>)targetSet[j]).getAttribute("id") << std::endl;
		}
	}
	std::cout << std::endl;
#endif

	exitStates(enabledTransitions);
	executeTransitionContent(enabledTransitions);
	enterStates(enabledTransitions);
}

void Interpreter::exitInterpreter() {
	NodeSet<std::string> statesToExit = _configuration;
	statesToExit.to_document_order();
	statesToExit.reverse();

	for (int i = 0; i < statesToExit.size(); i++) {
		Arabica::XPath::NodeSet<std::string> onExitElems = filterChildElements(_xmlNSPrefix + "onexit", statesToExit[i]);
		for (int j = 0; j < onExitElems.size(); j++) {
			executeContent(onExitElems[j]);
		}
		Arabica::XPath::NodeSet<std::string> invokeElems = filterChildElements(_xmlNSPrefix + "invoke", statesToExit[i]);
		for (int j = 0; j < invokeElems.size(); j++) {
			cancelInvoke(invokeElems[j]);
		}
		if (isFinal(statesToExit[i]) && parentIsScxmlState(statesToExit[i])) {
			returnDoneEvent(statesToExit[i]);
		}
	}
	_configuration = NodeSet<std::string>();
}

void Interpreter::executeTransitionContent(const Arabica::XPath::NodeSet<std::string>& enabledTransitions) {
	executeContent(enabledTransitions);
}

void Interpreter::executeContent(const NodeList<std::string>& content) {
	for (unsigned int i = 0; i < content.getLength(); i++) {
		if (content.item(i).getNodeType() != Node_base::ELEMENT_NODE)
			continue;
		executeContent(content.item(i));
	}
}

void Interpreter::executeContent(const NodeSet<std::string>& content) {
	for (unsigned int i = 0; i < content.size(); i++) {
		if (content[i].getNodeType() != Node_base::ELEMENT_NODE)
			continue;
		executeContent(content[i]);
	}
}

void Interpreter::executeContent(const Arabica::DOM::Node<std::string>& content) {
	if (content.getNodeType() != Node_base::ELEMENT_NODE)
		return;

	if (false) {
	} else if (boost::iequals(TAGNAME(content), _xmlNSPrefix + "onentry") ||
	           boost::iequals(TAGNAME(content), _xmlNSPrefix + "onexit") ||
	           boost::iequals(TAGNAME(content), _xmlNSPrefix + "finalize") ||
	           boost::iequals(TAGNAME(content), _xmlNSPrefix + "transition")) {
		// --- CONVENIENCE LOOP --------------------------
		NodeList<std::string> executable = content.getChildNodes();
		for (int i = 0; i < executable.getLength(); i++) {
			executeContent(executable.item(i));
		}
	} else if (boost::iequals(TAGNAME(content), _xmlNSPrefix + "raise")) {
		// --- RAISE --------------------------
		if (HAS_ATTR(content, "event")) {
			Event event;
			event.name = ATTR(content, "event");
			_internalQueue.push_back(event);
		}
	} else if (boost::iequals(TAGNAME(content), _xmlNSPrefix + "if")) {
		// --- IF / ELSEIF / ELSE --------------
		Arabica::DOM::Element<std::string> ifElem = (Arabica::DOM::Element<std::string>)content;
#if 0
		if (HAS_ATTR(ifElem, "cond"))
			std::cout << ATTR(ifElem, "cond") << std::endl;
#endif
		if(hasConditionMatch(ifElem)) {
			// condition is true, execute all content up to an elseif, else or end
			if (ifElem.hasChildNodes()) {
				NodeList<std::string> childs = ifElem.getChildNodes();
				for (unsigned int i = 0; i < childs.getLength(); i++) {
					if (childs.item(i).getNodeType() != Node_base::ELEMENT_NODE)
						continue;
					if (boost::iequals(TAGNAME(childs.item(i)), _xmlNSPrefix + "elseif") ||
					        boost::iequals(TAGNAME(childs.item(i)), _xmlNSPrefix + "else"))
						break;
					executeContent(childs.item(i));
				}
			}
		} else {
			// condition does not match - do we have an elsif?
			if (ifElem.hasChildNodes()) {
				NodeSet<std::string> elseifElem = filterChildElements(_xmlNSPrefix + "elseif", ifElem);
				for (unsigned int i = 0; i < elseifElem.size(); i++) {
#if 0
					if (HAS_ATTR(elseifElem[i], "cond"))
						std::cout << ATTR(elseifElem[i], "cond") << std::endl;
#endif
					if (hasConditionMatch(elseifElem[i])) {
						executeContent(elseifElem[i].getChildNodes());
						goto ELSIF_ELEM_MATCH;
					}
				}
				NodeSet<std::string> elseElem = filterChildElements(_xmlNSPrefix + "else", ifElem);
				if (elseElem.size() > 0)
					executeContent(elseElem[0].getChildNodes());
			}
		}
ELSIF_ELEM_MATCH:
		;
	} else if (boost::iequals(TAGNAME(content), _xmlNSPrefix + "elseif")) {
		std::cerr << "Found single elsif to evaluate!" << std::endl;
	} else if (boost::iequals(TAGNAME(content), _xmlNSPrefix + "else")) {
		std::cerr << "Found single else to evaluate!" << std::endl;
	} else if (boost::iequals(TAGNAME(content), _xmlNSPrefix + "foreach")) {
		// --- FOREACH --------------------------
		if (_dataModel) {
			if (HAS_ATTR(content, "array") && HAS_ATTR(content, "item")) {
				std::string array = ATTR(content, "array");
				std::string item = ATTR(content, "item");
				std::string index = (HAS_ATTR(content, "index") ? ATTR(content, "index") : "");
				uint32_t iterations = _dataModel.getLength(array);
				_dataModel.pushContext(); // copy old and enter new context
				for (uint32_t iteration = 0; iteration < iterations; iteration++) {
					{
						// assign array element to item
						std::stringstream ss;
						ss << array << "[" << iteration << "]";
						_dataModel.assign(item, ss.str());
					}
					if (index.length() > 0) {
						// assign iteration element to index
						std::stringstream ss;
						ss << iteration;
						_dataModel.assign(index,ss.str());
					}
					if (content.hasChildNodes())
						executeContent(content.getChildNodes());
				}
				_dataModel.popContext(); // leave stacked context
			} else {
				LOG(ERROR) << "Expected array and item attributes with foreach element!" << std::endl;
			}
		}
	} else if (boost::iequals(TAGNAME(content), _xmlNSPrefix + "log")) {
		// --- LOG --------------------------
		Arabica::DOM::Element<std::string> logElem = (Arabica::DOM::Element<std::string>)content;
		if (logElem.hasAttribute("expr")) {
			if (_dataModel) {
				try {
					std::cout << _dataModel.evalAsString(logElem.getAttribute("expr")) << std::endl;
				} catch (Event e) {
					LOG(ERROR) << "Syntax error in expr attribute of log element:" << std::endl << e << std::endl;
				}
			} else {
				std::cout << logElem.getAttribute("expr") << std::endl;
			}
		}
	} else if (boost::iequals(TAGNAME(content), _xmlNSPrefix + "assign")) {
		// --- ASSIGN --------------------------
		if (_dataModel && HAS_ATTR(content, "location") && HAS_ATTR(content, "expr")) {
			try {
				_dataModel.assign(ATTR(content, "location"), ATTR(content, "expr"));
			} catch (Event e) {
				LOG(ERROR) << "Syntax error in attributes of assign element:" << std::endl << e << std::endl;
			}
		}
	} else if (boost::iequals(TAGNAME(content), _xmlNSPrefix + "validate")) {
		// --- VALIDATE --------------------------
		if (_dataModel) {
			std::string location = (HAS_ATTR(content, "location") ? ATTR(content, "location") : "");
			std::string schema = (HAS_ATTR(content, "schema") ? ATTR(content, "schema") : "");
			_dataModel.validate(location, schema);
		}
	} else if (boost::iequals(TAGNAME(content), _xmlNSPrefix + "script")) {
		// --- SCRIPT --------------------------
		if (_dataModel) {
			if (HAS_ATTR(content, "src")) {
				URL scriptUrl(ATTR(content, "src"));
				if (!toAbsoluteURI(scriptUrl)) {
					LOG(ERROR) << "script element has relative URI " << ATTR(content, "src") <<  " with no base URI set for interpreter";
					return;
				}

				std::stringstream srcContent;
				if (_cachedURLs.find(scriptUrl.asString()) != _cachedURLs.end()) {
					srcContent << _cachedURLs[scriptUrl.asString()];
				} else {
					srcContent << scriptUrl;
					_cachedURLs[scriptUrl.asString()] = scriptUrl;
				}


				try {
					_dataModel.eval(srcContent.str());
				} catch (Event e) {
					LOG(ERROR) << "Syntax error while executing script element from '" << ATTR(content, "src") << "':" << std::endl << e << std::endl;
				}
			} else {
				if (content.hasChildNodes()) {
					// search for the text node with the actual script
					if (content.getFirstChild().getNodeType() == Node_base::TEXT_NODE) {
						try {
							_dataModel.eval(content.getFirstChild().getNodeValue());
						} catch (Event e) {
							LOG(ERROR) << "Syntax error while executing script element" << std::endl << e << std::endl;
						}
					}
				}
			}
		}
	} else if (boost::iequals(TAGNAME(content), _xmlNSPrefix + "send")) {
		// --- SEND --------------------------
		send(content);
	} else if (boost::iequals(TAGNAME(content), _xmlNSPrefix + "cancel")) {
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

		} catch (Event e) {
			LOG(ERROR) << "Syntax error while executing cancel element" << std::endl << e << std::endl;
		}

	} else if (boost::iequals(TAGNAME(content), _xmlNSPrefix + "invoke")) {
		// --- INVOKE --------------------------
	} else {
		// --- Custom Executable Content
		ExecutableContent execContent;
		if (_executableContent.find(content) == _executableContent.end()) {
			execContent = Factory::createExecutableContent(content.getLocalName(), content.getNamespaceURI(), this);
			if (!execContent) {
				LOG(ERROR) << "No custom executable content known for " << content.getLocalName() << " in " << content.getNamespaceURI();
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
				executeContent(executable.item(i));
			}
		}
		execContent.exitElement(content);
	}
}

void Interpreter::returnDoneEvent(const Arabica::DOM::Node<std::string>& state) {
}

void Interpreter::exitStates(const Arabica::XPath::NodeSet<std::string>& enabledTransitions) {
	NodeSet<std::string> statesToExit;
	std::set<InterpreterMonitor*>::iterator monIter;

#if VERBOSE
	std::cout << "Enabled exit transitions: " << std::endl;
	for (int i = 0; i < enabledTransitions.size(); i++) {
		std::cout << enabledTransitions[i] << std::endl;
	}
	std::cout << std::endl;
#endif

	for (int i = 0; i < enabledTransitions.size(); i++) {
		Arabica::DOM::Element<std::string> transition = ((Arabica::DOM::Element<std::string>)enabledTransitions[i]);
		if (!isTargetless(transition)) {
			std::string transitionType = (boost::iequals(transition.getAttribute("type"), "internal") ? "internal" : "external");
			NodeSet<std::string> tStates = getTargetStates(transition);
			Arabica::DOM::Node<std::string> ancestor;
			Arabica::DOM::Node<std::string> source = getSourceState(transition);

			bool allDescendants = true;
			for (int j = 0; j < tStates.size(); j++) {
				if (!isDescendant(tStates[j], source)) {
					allDescendants = false;
					break;
				}
			}
			if (boost::iequals(transitionType, "internal") &&
			        isCompound(source) &&
			        allDescendants) {
				ancestor = source;
			} else {
				NodeSet<std::string> tmpStates;
				tmpStates.push_back(source);
				tmpStates.insert(tmpStates.end(), tStates.begin(), tStates.end());

#if VERBOSE
				std::cout << "tmpStates: ";
				for (int i = 0; i < tmpStates.size(); i++) {
					std::cout << ATTR(tmpStates[i], "id") << ", ";
				}
				std::cout << std::endl;
#endif
				ancestor = findLCCA(tmpStates);
			}

#if VERBOSE
			std::cout << "Ancestor: " << ATTR(ancestor, "id") << std::endl;;
#endif

			for (int j = 0; j < _configuration.size(); j++) {
				if (isDescendant(_configuration[j], ancestor))
					statesToExit.push_back(_configuration[j]);
			}
		}
	}

#if VERBOSE
	std::cout << "States to exit: ";
	for (int i = 0; i < statesToExit.size(); i++) {
		std::cout << LOCALNAME(statesToExit[i]) << ":" << ATTR(statesToExit[i], "id") << ", ";
	}
	std::cout << std::endl;

#endif

	// remove statesToExit from _statesToInvoke
	std::list<Arabica::DOM::Node<std::string> > tmp;
	for (int i = 0; i < _statesToInvoke.size(); i++) {
		if (!isMember(_statesToInvoke[i], statesToExit)) {
			tmp.push_back(_statesToInvoke[i]);
		}
	}
	_statesToInvoke = NodeSet<std::string>();
	_statesToInvoke.insert(_statesToInvoke.end(), tmp.begin(), tmp.end());

	statesToExit.to_document_order();
	statesToExit.reverse();

	monIter = _monitors.begin();
	while(monIter != _monitors.end()) {
		try {
			(*monIter)->beforeExitingStates(this, statesToExit);
		} catch (Event e) {
			LOG(ERROR) << "Syntax error when calling beforeExitingStates on monitors: " << std::endl << e << std::endl;
		} catch (...) {
			LOG(ERROR) << "An exception occured when calling beforeExitingStates on monitors";
		}
		monIter++;
	}

	for (int i = 0; i < statesToExit.size(); i++) {
		NodeSet<std::string> histories = filterChildElements(_xmlNSPrefix + "history", statesToExit[i]);
		for (int j = 0; j < histories.size(); j++) {
			Arabica::DOM::Element<std::string> historyElem = (Arabica::DOM::Element<std::string>)histories[j];
			std::string historyType = (historyElem.hasAttribute("type") ? historyElem.getAttribute("type") : "shallow");
			NodeSet<std::string> historyNodes;
			for (int k = 0; k < _configuration.size(); k++) {
				if (boost::iequals(historyType, "deep")) {
					if (isAtomic(_configuration[k]) && isDescendant(_configuration[k], statesToExit[i]))
						historyNodes.push_back(_configuration[k]);
				} else {
					if (_configuration[k].getParentNode() == statesToExit[i])
						historyNodes.push_back(_configuration[k]);
				}
			}
			_historyValue[historyElem.getAttribute("id")] = historyNodes;
#if 0
			std::cout << "History node " << ATTR(historyElem, "id") << " contains: ";
			for (int i = 0; i < historyNodes.size(); i++) {
				std::cout << ATTR(historyNodes[i], "id") << ", ";
			}
			std::cout << std::endl;

#endif

		}
	}

	for (int i = 0; i < statesToExit.size(); i++) {
		NodeSet<std::string> onExits = filterChildElements(_xmlNSPrefix + "onExit", statesToExit[i]);
		for (int j = 0; j < onExits.size(); j++) {
			Arabica::DOM::Element<std::string> onExitElem = (Arabica::DOM::Element<std::string>)onExits[j];
			executeContent(onExitElem);
		}
		NodeSet<std::string> invokes = filterChildElements(_xmlNSPrefix + "invoke", statesToExit[i]);
		for (int j = 0; j < invokes.size(); j++) {
			Arabica::DOM::Element<std::string> invokeElem = (Arabica::DOM::Element<std::string>)invokes[j];
			cancelInvoke(invokeElem);
		}
	}

	// remove statesToExit from _configuration
	tmp.clear();
	for (int i = 0; i < _configuration.size(); i++) {
		if (!isMember(_configuration[i], statesToExit)) {
			tmp.push_back(_configuration[i]);
		}
	}
	_configuration = NodeSet<std::string>();
	_configuration.insert(_configuration.end(), tmp.begin(), tmp.end());

	monIter = _monitors.begin();
	while(monIter != _monitors.end()) {
		try {
			(*monIter)->afterExitingStates(this);
		} catch (Event e) {
			LOG(ERROR) << "Syntax error when calling afterExitingStates on monitors: " << std::endl << e << std::endl;
		} catch (...) {
			LOG(ERROR) << "An exception occured when calling afterExitingStates on monitors";
		}
		monIter++;
	}

}

#ifdef ORIG_ENTERSTATES
void Interpreter::enterStates(const Arabica::XPath::NodeSet<std::string>& enabledTransitions) {
	NodeSet<std::string> statesToEnter;
	NodeSet<std::string> statesForDefaultEntry;
	std::set<InterpreterMonitor*>::iterator monIter;

#if VERBOSE
	std::cout << "Enabled enter transitions: " << std::endl;
	for (int i = 0; i < enabledTransitions.size(); i++) {
		std::cout << enabledTransitions[i] << std::endl;
	}
	std::cout << std::endl;
#endif

	for (int i = 0; i < enabledTransitions.size(); i++) {
		Arabica::DOM::Element<std::string> transition = ((Arabica::DOM::Element<std::string>)enabledTransitions[i]);
		if (!isTargetless(transition)) {
			std::string transitionType = (boost::iequals(transition.getAttribute("type"), "internal") ? "internal" : "external");
			NodeSet<std::string> tStates = getTargetStates(transition);

#if VERBOSE
			std::cout << "Target States: ";
			for (int i = 0; i < tStates.size(); i++) {
				std::cout << ATTR(tStates[i], "id") << ", ";
			}
			std::cout << std::endl;
#endif

			Arabica::DOM::Node<std::string> ancestor;
			Arabica::DOM::Node<std::string> source = getSourceState(transition);
#if VERBOSE
			std::cout << "Source States: " << ATTR(source, "id") << std::endl;
#endif
			assert(source);

			bool allDescendants = true;
			for (int j = 0; j < tStates.size(); j++) {
				if (!isDescendant(tStates[j], source)) {
					allDescendants = false;
					break;
				}
			}
			if (boost::iequals(transitionType, "internal") &&
			        isCompound(source) &&
			        allDescendants) {
				ancestor = source;
			} else {
				NodeSet<std::string> tmpStates;
				tmpStates.push_back(source);
				tmpStates.insert(tmpStates.end(), tStates.begin(), tStates.end());

				ancestor = findLCCA(tmpStates);
			}

#if VERBOSE
			std::cout << "Ancestor: " << ATTR(ancestor, "id") << std::endl;
#endif

			for (int j = 0; j < tStates.size(); j++) {
				addStatesToEnter(tStates[j], statesToEnter, statesForDefaultEntry);
			}

#if VERBOSE
			std::cout << "States to enter: ";
			for (int i = 0; i < statesToEnter.size(); i++) {
				std::cout << LOCALNAME(statesToEnter[i]) << ":" << ATTR(statesToEnter[i], "id") << ", ";
			}
			std::cout << std::endl;
#endif

			for (int j = 0; j < tStates.size(); j++) {
				NodeSet<std::string> ancestors = getProperAncestors(tStates[j], ancestor);

#if VERBOSE
				std::cout << "Proper Ancestors of " << ATTR(tStates[j], "id") << " and " << ATTR(ancestor, "id") << ": ";
				for (int i = 0; i < ancestors.size(); i++) {
					std::cout << ATTR(ancestors[i], "id") << ", ";
				}
				std::cout << std::endl;
#endif

				for (int k = 0; k < ancestors.size(); k++) {
					statesToEnter.push_back(ancestors[k]);
					if(isParallel(ancestors[k])) {
						NodeSet<std::string> childs = getChildStates(ancestors[k]);
						for (int l = 0; l < childs.size(); l++) {
							bool someIsDescendant = false;
							for (int m = 0; m < statesToEnter.size(); m++) {
								if (isDescendant(statesToEnter[m], childs[l])) {
									someIsDescendant = true;
									break;
								}
							}
							if (!someIsDescendant) {
								addStatesToEnter(childs[l], statesToEnter, statesForDefaultEntry);
							}
						}
					}
				}
			}
		}
	}
	statesToEnter.to_document_order();

	monIter = _monitors.begin();
	while(monIter != _monitors.end()) {
		try {
			(*monIter)->beforeEnteringStates(this, statesToEnter);
		} catch (Event e) {
			LOG(ERROR) << "Syntax error when calling beforeEnteringStates on monitors: " << std::endl << e << std::endl;
		} catch (...) {
			LOG(ERROR) << "An exception occured when calling beforeEnteringStates on monitors";
		}
		monIter++;
	}

	for (int i = 0; i < statesToEnter.size(); i++) {
		Arabica::DOM::Element<std::string> stateElem = (Arabica::DOM::Element<std::string>)statesToEnter[i];
		_configuration.push_back(stateElem);
		_statesToInvoke.push_back(stateElem);
		if (_binding == LATE && stateElem.getAttribute("isFirstEntry").size() > 0) {
			NodeSet<std::string> dataModelElems = filterChildElements(_xmlNSPrefix + "datamodel", stateElem);
			if(dataModelElems.size() > 0 && _dataModel) {
				Arabica::XPath::NodeSet<std::string> dataElems = filterChildElements(_xmlNSPrefix + "data", dataModelElems[0]);
				for (int j = 0; j < dataElems.size(); j++) {
					initializeData(dataElems[j]);
				}
			}
			stateElem.setAttribute("isFirstEntry", "");
		}
		// execute onentry executable content
		NodeSet<std::string> onEntryElems = filterChildElements(_xmlNSPrefix + "onEntry", stateElem);
		executeContent(onEntryElems);

		if (isMember(stateElem, statesForDefaultEntry)) {
			// execute initial transition content for compund states
			Arabica::XPath::NodeSet<std::string> transitions = _xpath.evaluate("" + _xpathPrefix + "initial/" + _xpathPrefix + "transition", stateElem).asNodeSet();
			for (int j = 0; j < transitions.size(); j++) {
				executeContent(transitions[j]);
			}
		}

		if (isFinal(stateElem)) {
			internalDoneSend(stateElem);
			Arabica::DOM::Element<std::string> parent = (Arabica::DOM::Element<std::string>)stateElem.getParentNode();

			if (isParallel(parent.getParentNode())) {
				Arabica::DOM::Element<std::string> grandParent = (Arabica::DOM::Element<std::string>)parent.getParentNode();

				Arabica::XPath::NodeSet<std::string> childs = getChildStates(grandParent);
				bool inFinalState = true;
				for (int j = 0; j < childs.size(); j++) {
					if (!isInFinalState(childs[j])) {
						inFinalState = false;
						break;
					}
				}
				if (inFinalState) {
					internalDoneSend(parent);
				}
			}
		}
	}
	for (int i = 0; i < _configuration.size(); i++) {
		Arabica::DOM::Element<std::string> stateElem = (Arabica::DOM::Element<std::string>)_configuration[i];
		if (isFinal(stateElem) && parentIsScxmlState(stateElem)) {
			_running = false;
			_done = true;
		}
	}

	monIter = _monitors.begin();
	while(monIter != _monitors.end()) {
		try {
			(*monIter)->afterEnteringStates(this);
		} catch (Event e) {
			LOG(ERROR) << "Syntax error when calling afterEnteringStates on monitors: " << std::endl << e << std::endl;
		} catch (...) {
			LOG(ERROR) << "An exception occured when calling afterEnteringStates on monitors";
		}
		monIter++;
	}

}

void Interpreter::addStatesToEnter(const Arabica::DOM::Node<std::string>& state,
                                   Arabica::XPath::NodeSet<std::string>& statesToEnter,
                                   Arabica::XPath::NodeSet<std::string>& statesForDefaultEntry) {
	std::string stateId = ((Arabica::DOM::Element<std::string>)state).getAttribute("id");

#if VERBOSE
	std::cout << "Adding state to enter: " << stateId << std::endl;
#endif
	if (isHistory(state)) {
		if (_historyValue.find(stateId) != _historyValue.end()) {
			Arabica::XPath::NodeSet<std::string> historyValue = _historyValue[stateId];

#if VERBOSE
			std::cout << "History State " << ATTR(state, "id") << ": ";
			for (int i = 0; i < historyValue.size(); i++) {
				std::cout << ATTR(historyValue[i], "id") << ", ";
			}
			std::cout << std::endl;
#endif

			for (int i = 0; i < historyValue.size(); i++) {
				addStatesToEnter(historyValue[i], statesToEnter, statesForDefaultEntry);
				NodeSet<std::string> ancestors = getProperAncestors(historyValue[i], state);

#if VERBOSE
				std::cout << "Proper Ancestors: ";
				for (int i = 0; i < ancestors.size(); i++) {
					std::cout << ATTR(ancestors[i], "id") << ", ";
				}
				std::cout << std::endl;
#endif

				for (int j = 0; j < ancestors.size(); j++) {
					statesToEnter.push_back(ancestors[j]);
				}
			}
		} else {
			NodeSet<std::string> transitions = filterChildElements(_xmlNSPrefix + "transition", state);
			for (int i = 0; i < transitions.size(); i++) {
				NodeSet<std::string> targets = getTargetStates(transitions[i]);
				for (int j = 0; j < targets.size(); j++) {
					addStatesToEnter(targets[j], statesToEnter, statesForDefaultEntry);

					// Modifications from chris nuernberger
					NodeSet<std::string> ancestors = getProperAncestors(targets[j], state);
					for (int k = 0; k < ancestors.size(); k++) {
						statesToEnter.push_back(ancestors[k]);
					}
				}
			}
		}
	} else {
		statesToEnter.push_back(state);
		if (isCompound(state)) {
			statesForDefaultEntry.push_back(state);

			addStatesToEnter(getInitialState(state), statesToEnter, statesForDefaultEntry);

# if 0
			NodeSet<std::string> tStates = getTargetStates(getInitialState(state));
			for (int i = 0; i < tStates.size(); i++) {
				addStatesToEnter(tStates[i], statesToEnter, statesForDefaultEntry);
			}
# endif
			//			addStatesToEnter(getInitialState(state), statesToEnter, statesForDefaultEntry);
			//      NodeSet<std::string> tStates = getTargetStates(getInitialState(state));

		} else if(isParallel(state)) {
			NodeSet<std::string> childStates = getChildStates(state);
			for (int i = 0; i < childStates.size(); i++) {
				addStatesToEnter(childStates[i], statesToEnter, statesForDefaultEntry);
			}
		}
	}
}
#endif

#ifdef ENTERSTATES_02_2013
void Interpreter::enterStates(const Arabica::XPath::NodeSet<std::string>& enabledTransitions) {
	NodeSet<std::string> statesToEnter;
	NodeSet<std::string> statesForDefaultEntry;
	std::set<InterpreterMonitor*>::iterator monIter;

	computeEntrySet(enabledTransitions, statesToEnter, statesForDefaultEntry);
	statesToEnter.sort(); // entry order is document order
	for (int i = 0; i < statesToEnter.size(); i++) {
		Arabica::DOM::Element<std::string> s = (Arabica::DOM::Element<std::string>)statesToEnter[i];
		_configuration.push_back(s);
		_statesToInvoke.push_back(s);

		if (_binding == LATE && ATTR(s, "isFirstEntry").size() > 0) {
			NodeSet<std::string> dataModelElems = filterChildElements(_xmlNSPrefix + "datamodel", s);
			if(dataModelElems.size() > 0 && _dataModel) {
				Arabica::XPath::NodeSet<std::string> dataElems = filterChildElements(_xmlNSPrefix + "data", dataModelElems[0]);
				for (int j = 0; j < dataElems.size(); j++) {
					initializeData(dataElems[j]);
				}
			}
			s.setAttribute("isFirstEntry", "");
		}
		executeContent(filterChildElements(_xmlNSPrefix + "onEntry", s));
		if (isMember(s, statesForDefaultEntry)) {
			executeContent(getInitialState(s)); // TODO: This part is unclear
		}

#if VERBOSE
		std::cout << "Is state " << ATTR(s, "id") << " final?";
#endif
		if (isFinal(s)) {
			if (parentIsScxmlState(s)) {
				_running = false;
				_done = true;
			} else {
				Arabica::DOM::Element<std::string> parent = (Arabica::DOM::Element<std::string>)s.getParentNode();
				Arabica::DOM::Element<std::string> grandParent = (Arabica::DOM::Element<std::string>)parent.getParentNode();
				internalDoneSend(parent);

				if (isParallel(grandParent)) {
					Arabica::XPath::NodeSet<std::string> childs = getChildStates(grandParent);
					bool inFinalState = true;
					for (int j = 0; j < childs.size(); j++) {
						if (!isInFinalState(childs[j])) {
							inFinalState = false;
							break;
						}
					}
					if (inFinalState) {
						internalDoneSend(grandParent);
					}
				}
			}
		}
	}
}
void Interpreter::computeEntrySet(const Arabica::XPath::NodeSet<std::string>& transitions,
                                  Arabica::XPath::NodeSet<std::string>& statesToEnter,
                                  Arabica::XPath::NodeSet<std::string>& statesForDefaultEntry) {
	for (int i = 0; i < transitions.size(); i++) {
		NodeSet<std::string> targets = getTargetStates(transitions[i]);
		for (int j = 0; j < targets.size(); j++) {
			statesToEnter.push_back(targets[i]);
		}
	}
	for (int i = 0; i < transitions.size(); i++) {
		Arabica::DOM::Node<std::string> ancestor = getTransitionDomain(transitions[i]);
		NodeSet<std::string> targets = getTargetStates(transitions[i]);
		for (int j = 0; j < targets.size(); j++) {
			addAncestorStatesToEnter(targets[j], ancestor, statesToEnter, statesForDefaultEntry);
		}
	}
}
void Interpreter::addDescendentStatesToEnter(const Arabica::DOM::Node<std::string>& state,
        Arabica::XPath::NodeSet<std::string>& statesToEnter,
        Arabica::XPath::NodeSet<std::string>& statesForDefaultEntry) {
	if (isHistory(state)) {
		if (_historyValue.find(ATTR(state, "id")) != _historyValue.end()) {
			Arabica::XPath::NodeSet<std::string> history = _historyValue[ATTR(state, "id")];
			for (int i = 0; i < history.size(); i++) {
				addDescendentStatesToEnter(history[i], statesToEnter, statesForDefaultEntry);
				addAncestorStatesToEnter(history[i], state.getParentNode(), statesToEnter, statesForDefaultEntry);
			}
		} else {
			NodeSet<std::string> transitions = filterChildElements(_xmlNSPrefix + "transition", state);
			for (int i = 0; i < transitions.size(); i++) {
				NodeSet<std::string> targets = getTargetStates(transitions[i]);
				for (int j = 0; j < targets.size(); j++) {
					addDescendentStatesToEnter(targets[j],statesToEnter,statesForDefaultEntry);
					addAncestorStatesToEnter(targets[j], state.getParentNode(), statesToEnter, statesForDefaultEntry);
				}
			}
		}
	} else {
		statesToEnter.push_back(state);
		if (isCompound(state)) {
			statesForDefaultEntry.push_back(state);
			Node<std::string> initial = getInitialState(state);
			addDescendentStatesToEnter(initial, statesToEnter, statesForDefaultEntry);
			addAncestorStatesToEnter(initial, state.getParentNode(), statesToEnter, statesForDefaultEntry);
		} else if (isParallel(state)) {
			NodeSet<std::string> childs = getChildStates(state);
			for (int i = 0; i < childs.size(); i++) {
				bool someAreDescendants = false;
				for (int j = 0; i < statesToEnter.size(); j++) {
					if (isDescendant(statesToEnter[j], childs[i]))
						someAreDescendants = true;
				}
				if (!someAreDescendants) {
					addDescendentStatesToEnter(childs[i], statesToEnter, statesForDefaultEntry);
				}
			}
		}
	}
}

void Interpreter::addAncestorStatesToEnter(const Arabica::DOM::Node<std::string>& state,
        const Arabica::DOM::Node<std::string>& ancestor,
        Arabica::XPath::NodeSet<std::string>& statesToEnter,
        Arabica::XPath::NodeSet<std::string>& statesForDefaultEntry) {
	NodeSet<std::string> properAncs = getProperAncestors(state, ancestor);
	for (int k = 0; k < properAncs.size(); k++) {
		statesToEnter.push_back(properAncs[k]);
		if (isParallel(properAncs[k])) {
			NodeSet<std::string> childs = getChildStates(properAncs[k]);
			for (int i = 0; i < childs.size(); i++) {
				bool someAreDescendants = false;
				for (int j = 0; i < statesToEnter.size(); j++) {
					if (isDescendant(statesToEnter[j], childs[i]))
						someAreDescendants = true;
				}
				if (!someAreDescendants) {
					addDescendentStatesToEnter(childs[i], statesToEnter, statesForDefaultEntry);
				}
			}
		}
	}
}

Arabica::DOM::Node<std::string> Interpreter::getTransitionDomain(const Arabica::DOM::Node<std::string>& transition) {
	Arabica::DOM::Node<std::string> source = getSourceState(transition);
	if (isTargetless(transition)) {
		return source;
	}

	Arabica::XPath::NodeSet<std::string> targets = getTargetStates(transition);
	if (boost::iequals(ATTR(transition, "type"), "internal") && isCompound(source)) {
		bool allDescendants = true;
		for (int i = 0; i < targets.size(); i++) {
			if (!isDescendant(targets[i], source)) {
				allDescendants = false;
				break;
			}
		}
		if (allDescendants)
			return source;
	}

	targets.push_back(source);
	return findLCCA(targets);
}

#endif

bool Interpreter::parentIsScxmlState(Arabica::DOM::Node<std::string> state) {
	Arabica::DOM::Element<std::string> stateElem = (Arabica::DOM::Element<std::string>)state;
	Arabica::DOM::Element<std::string> parentElem = (Arabica::DOM::Element<std::string>)state.getParentNode();
	if (boost::iequals(TAGNAME(parentElem), _xmlNSPrefix + "scxml"))
		return true;
	return false;
}

bool Interpreter::isInFinalState(const Arabica::DOM::Node<std::string>& state) {
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

bool Interpreter::isMember(const Arabica::DOM::Node<std::string>& node, const Arabica::XPath::NodeSet<std::string>& set) {
	for (int i = 0; i < set.size(); i++) {
		if (set[i] == node)
			return true;
	}
	return false;
}

Arabica::XPath::NodeSet<std::string> Interpreter::getChildStates(const Arabica::DOM::Node<std::string>& state) {
	Arabica::XPath::NodeSet<std::string> childs;

	Arabica::DOM::NodeList<std::string> childElems = state.getChildNodes();
	for (int i = 0; i < childElems.getLength(); i++) {
		if (isState(childElems.item(i))) {
			childs.push_back(childElems.item(i));
		}
	}
	return childs;
}

/**
 See: http://www.w3.org/TR/scxml/#LCCA
 The Least Common Compound Ancestor is the <state> or <scxml> element s such that s is a proper ancestor
 of all states on stateList and no descendant of s has this property. Note that there is guaranteed to be
 such an element since the <scxml> wrapper element is a common ancestor of all states. Note also that since
 we are speaking of proper ancestor (parent or parent of a parent, etc.) the LCCA is never a member of stateList.
*/

Arabica::DOM::Node<std::string> Interpreter::findLCCA(const Arabica::XPath::NodeSet<std::string>& states) {
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

Arabica::DOM::Node<std::string> Interpreter::getState(const std::string& stateId) {

	if (_cachedStates.find(stateId) != _cachedStates.end()) {
		return _cachedStates[stateId];
	}

	// first try atomic and compund states
	NodeSet<std::string> target = _xpath.evaluate("//" + _xpathPrefix + "state[@id='" + stateId + "']", _document).asNodeSet();
	if (target.size() > 0)
		goto FOUND;

	// now parallel states
	target = _xpath.evaluate("//" + _xpathPrefix + "parallel[@id='" + stateId + "']", _document).asNodeSet();
	if (target.size() > 0)
		goto FOUND;

	// now final states
	target = _xpath.evaluate("//" + _xpathPrefix + "final[@id='" + stateId + "']", _document).asNodeSet();
	if (target.size() > 0)
		goto FOUND;

	// now history states
	target = _xpath.evaluate("//" + _xpathPrefix + "history[@id='" + stateId + "']", _document).asNodeSet();
	if (target.size() > 0)
		goto FOUND;

	LOG(ERROR) << "No state with id " << stateId << " found!";

FOUND:
	if (target.size() > 0) {
		assert(target.size() == 1);
		_cachedStates[stateId] = target[0];
		return target[0];
	}
	// return the empty node
	return Arabica::DOM::Node<std::string>();
}

Arabica::DOM::Node<std::string> Interpreter::getSourceState(const Arabica::DOM::Node<std::string>& transition) {
	if (boost::iequals(TAGNAME(transition.getParentNode()), _xmlNSPrefix + "initial"))
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
Arabica::DOM::Node<std::string> Interpreter::getInitialState(Arabica::DOM::Node<std::string> state) {
	if (!state) {
		state = _document.getFirstChild();
		while(state && !isState(state))
			state = state.getNextSibling();
	}

#if VERBOSE
	std::cout << "Getting initial state of " << TAGNAME(state) << " " << ATTR(state, "id") << std::endl;
#endif

	assert(isCompound(state) || isParallel(state));

	// initial attribute at element
	Arabica::DOM::Element<std::string> stateElem = (Arabica::DOM::Element<std::string>)state;
	if (stateElem.hasAttribute("initial")) {
		return getState(stateElem.getAttribute("initial"));
	}

	// initial element as child - but not the implicit generated one
	NodeSet<std::string> initialStates = filterChildElements(_xmlNSPrefix + "initial", state);
	if(initialStates.size() == 1 && !boost::iequals(ATTR(initialStates[0], "generated"), "true"))
		return initialStates[0];

	// first child state
	NodeList<std::string> childs = state.getChildNodes();
	for (int i = 0; i < childs.getLength(); i++) {
		if (isState(childs.item(i)))
			return childs.item(i);
	}
	// nothing found
	return Arabica::DOM::Node<std::string>();
}

NodeSet<std::string> Interpreter::getTargetStates(const Arabica::DOM::Node<std::string>& transition) {
	NodeSet<std::string> targetStates;

	assert(boost::iequals(LOCALNAME(transition), "transition"));

	// if we are called with a state, process all its transitions
	if (isState(transition) || (transition.getNodeType() == Node_base::ELEMENT_NODE && boost::iequals(_xmlNSPrefix + "initial", TAGNAME(transition)))) {
		NodeList<std::string> childs = transition.getChildNodes();
		for (int i = 0; i < childs.getLength(); i++) {
			if (childs.item(i).getNodeType() == Node_base::ELEMENT_NODE && boost::iequals(TAGNAME(childs.item(i)), _xmlNSPrefix + "transition")) {
				targetStates.push_back(getTargetStates(childs.item(i)));
			}
		}
		return targetStates;
	}

	std::string targetId = ((Arabica::DOM::Element<std::string>)transition).getAttribute("target");

	std::vector<std::string> targetIds = Interpreter::tokenizeIdRefs(ATTR(transition, "target"));
	for (int i = 0; i < targetIds.size(); i++) {
		Arabica::DOM::Node<std::string> state = getState(targetIds[i]);
		assert(HAS_ATTR(state, "id"));
		targetStates.push_back(state);
	}
	return targetStates;
}

std::vector<std::string> Interpreter::tokenizeIdRefs(const std::string& idRefs) {
	std::vector<std::string> ids;

	if (idRefs.length() > 0) {
		std::istringstream iss(idRefs);

		std::copy(std::istream_iterator<std::string>(iss),
		          std::istream_iterator<std::string>(),
		          std::back_inserter<std::vector<std::string> >(ids));
	}

	return ids;
}

NodeSet<std::string> Interpreter::filterChildElements(const std::string& tagName, const NodeSet<std::string>& nodeSet) {
	NodeSet<std::string> filteredChildElems;
	for (unsigned int i = 0; i < nodeSet.size(); i++) {
		filteredChildElems.push_back(filterChildElements(tagName, nodeSet[i]));
	}
	return filteredChildElems;
}

NodeSet<std::string> Interpreter::filterChildElements(const std::string& tagName, const Node<std::string>& node) {
	NodeSet<std::string> filteredChildElems;
	NodeList<std::string> childs = node.getChildNodes();
	for (unsigned int i = 0; i < childs.getLength(); i++) {
		if (childs.item(i).getNodeType() != Node_base::ELEMENT_NODE ||
		        !boost::iequals(TAGNAME(childs.item(i)), tagName))
			continue;
		filteredChildElems.push_back(childs.item(i));
	}
	return filteredChildElems;
}

NodeSet<std::string> Interpreter::getProperAncestors(const Arabica::DOM::Node<std::string>& s1,
        const Arabica::DOM::Node<std::string>& s2) {
	NodeSet<std::string> ancestors;
	if (isState(s1)) {
		Arabica::DOM::Node<std::string> node = s1;
		while((node = node.getParentNode())) {
			if (!isState(node))
				break;
			if (boost::iequals(TAGNAME(node), _xmlNSPrefix + "scxml")) // do not return scxml root itself - this is somewhat ill-defined
				break;
			if (!boost::iequals(TAGNAME(node), _xmlNSPrefix + "parallel") && !boost::iequals(TAGNAME(node), _xmlNSPrefix + "state") && !boost::iequals(TAGNAME(node), _xmlNSPrefix + "scxml"))
				break;
			if (node == s2)
				break;
			ancestors.push_back(node);
		}
	}
	return ancestors;
}

bool Interpreter::isDescendant(const Arabica::DOM::Node<std::string>& s1,
                               const Arabica::DOM::Node<std::string>& s2) {
	Arabica::DOM::Node<std::string> parent = s1.getParentNode();
	while(parent) {
		if (s2 == parent)
			return true;
		parent = parent.getParentNode();
	}
	return false;
}

bool Interpreter::isTargetless(const Arabica::DOM::Node<std::string>& transition) {
	if (transition.hasAttributes()) {
		if (((Arabica::DOM::Element<std::string>)transition).hasAttribute("target"))
			return false;
	}
	return true;
}

bool Interpreter::isWithinSameChild(const Arabica::DOM::Node<std::string>& transition) {
	if (!isTargetless(transition)) {
		std::string target = ((Arabica::DOM::Element<std::string>)transition).getAttribute("target");
		assert(transition.getParentNode());
		// @todo: do we need to look at parallel as well?
		if (_xpath.evaluate("" + _xpathPrefix + "state[id=\"" + target + "\"]", transition.getParentNode()).asNodeSet().size() > 0)
			return true;
		if (_xpath.evaluate("" + _xpathPrefix + "parallel[id=\"" + target + "\"]", transition.getParentNode()).asNodeSet().size() > 0)
			return true;
	}
	return false;
}

bool Interpreter::isState(const Arabica::DOM::Node<std::string>& state) {
	if (!state)
		return false;
	if (state.getNodeType() != Arabica::DOM::Node_base::ELEMENT_NODE)
		return false;

	std::string tagName = LOCALNAME(state);
	if (boost::iequals("state", tagName))
		return true;
	if (boost::iequals("scxml", tagName))
		return true;
	if (boost::iequals("parallel", tagName))
		return true;
//	if (boost::iequals("history", tagName)) // this is no state, see mail to W3C list
//		return true;
	if (boost::iequals("final", tagName))
		return true;
	return false;
}

bool Interpreter::isFinal(const Arabica::DOM::Node<std::string>& state) {
	std::string tagName = LOCALNAME(state);
	if (boost::iequals("final", tagName))
		return true;
	if (HAS_ATTR(state, "final") && boost::iequals("true", ATTR(state, "final")))
		return true;
	return false;
}

bool Interpreter::isInitial(const Arabica::DOM::Node<std::string>& state) {
	if (!isState(state))
		return false;

	Arabica::DOM::Node<std::string> parent = state.getParentNode();
	if (!isState(parent))
		return true; // scxml element

	if (getInitialState(parent) == state)
		return true; // every nested node

	return false;
}

bool Interpreter::isPseudoState(const Arabica::DOM::Node<std::string>& state) {
	std::string tagName = LOCALNAME(state);
	if (boost::iequals("initial", tagName))
		return true;
	if (boost::iequals("history", tagName))
		return true;
	return false;
}

bool Interpreter::isTransitionTarget(const Arabica::DOM::Node<std::string>& elem) {
	return (isState(elem) || boost::iequals(LOCALNAME(elem), "history")); // TODO: history is a state
}

bool Interpreter::isAtomic(const Arabica::DOM::Node<std::string>& state) {
	if (boost::iequals("final", LOCALNAME(state)))
		return true;

	// I will assume that parallel states are not meant to be atomic.
	if (boost::iequals("parallel", LOCALNAME(state)))
		return false;

	Arabica::DOM::NodeList<std::string> childs = state.getChildNodes();
	for (unsigned int i = 0; i < childs.getLength(); i++) {
		if (isState(childs.item(i)))
			return false;
	}
	return true;
}

bool Interpreter::isHistory(const Arabica::DOM::Node<std::string>& state) {
	if (boost::iequals("history", LOCALNAME(state)))
		return true;
	return false;
}

bool Interpreter::isParallel(const Arabica::DOM::Node<std::string>& state) {
	if (!isState(state))
		return false;
	if (boost::iequals("parallel", LOCALNAME(state)))
		return true;
	return false;
}


bool Interpreter::isCompound(const Arabica::DOM::Node<std::string>& state) {
	if (!isState(state))
		return false;

	if (boost::iequals(LOCALNAME(state), "parallel")) // parallel is no compound state
		return false;

	Arabica::DOM::NodeList<std::string> childs = state.getChildNodes();
	for (unsigned int i = 0; i < childs.getLength(); i++) {
		if (isState(childs.item(i)))
			return true;
	}
	return false;
}

void Interpreter::setupIOProcessors() {
	tthread::lock_guard<tthread::mutex> lock(_mutex);
	std::map<std::string, IOProcessorImpl*>::iterator ioProcIter = Factory::getInstance()->_ioProcessors.begin();
	while(ioProcIter != Factory::getInstance()->_ioProcessors.end()) {
		if (boost::iequals(ioProcIter->first, "basichttp") && !(_capabilities & CAN_BASIC_HTTP)) {
			ioProcIter++;
			continue;
		}
		
		_ioProcessors[ioProcIter->first] = Factory::createIOProcessor(ioProcIter->first, this);
		_ioProcessors[ioProcIter->first].setType(ioProcIter->first);
		_ioProcessors[ioProcIter->first].setInterpreter(this);

		if (_dataModel) {
			try {
				_dataModel.registerIOProcessor(ioProcIter->first, _ioProcessors[ioProcIter->first]);
			} catch (Event e) {
				LOG(ERROR) << "Syntax error when setting _ioprocessors:" << std::endl << e << std::endl;
			}
		} else {
			LOG(INFO) << "Not registering " << ioProcIter->first << " at _ioprocessors in datamodel, no datamodel specified";
		}
		ioProcIter++;
	}
}

IOProcessor Interpreter::getIOProcessor(const std::string& type) {
	tthread::lock_guard<tthread::mutex> lock(_mutex);
	if (_ioProcessors.find(type) == _ioProcessors.end()) {
		LOG(ERROR) << "No ioProcessor known for type " << type;
		return IOProcessor();
	}
	return _ioProcessors[type];
}

void Interpreter::setCmdLineOptions(int argc, char** argv) {
	char* key = NULL;
	char* value = NULL;
	for (int i = 0; i < argc; i++) {
		if (false) {
		} else if (strlen(argv[i]) > 2 && strncmp(&argv[i][0], "-", 1) == 0 && strncmp(&argv[i][1], "-", 1) == 0) {
			// longopt
			key = &argv[i][2];
		} else if (strlen(argv[i]) > 1 && strncmp(&argv[i][0], "-", 1) == 0 && strncmp(&argv[i][1], "-", 1) != 0) {
			// shortopt
			key = &argv[i][1];
		}
		if (key != NULL) {
			if (i + 1 < argc && strncmp(&argv[i + 1][0], "-", 1) != 0) {
				value = argv[++i];
				_cmdLineOptions.compound[key] = Data(value, Data::VERBATIM);
			} else {
				_cmdLineOptions.compound[key] = Data("true");
			}
		}
	}
}

/**
 * See: http://www.w3.org/TR/scxml/#LegalStateConfigurations
 */
bool Interpreter::hasLegalConfiguration() {

#if 0
	std::cout << "Checking whether {";
	std::string seperator;
	for (int i = 0; i < _configuration.size(); i++) {
		std::cout << seperator << ATTR(_configuration[i], "id");
		seperator = ", ";
	}
	std::cout << "} is legal" << std::endl;
#endif

	// The configuration contains exactly one child of the <scxml> element.
	NodeSet<std::string> scxmlChilds = getChildStates(_scxml);
	bool foundScxmlChild = false;
	for (int i = 0; i < scxmlChilds.size(); i++) {
		if (isMember(scxmlChilds[i], _configuration)) {
			if (foundScxmlChild)
				return false;
			foundScxmlChild = true;
		}
	}
	if (!foundScxmlChild)
		return false;

	// The configuration contains one or more atomic states.
	bool foundAtomicState = false;
	for (int i = 0; i < _configuration.size(); i++) {
		if (isAtomic(_configuration[i])) {
			foundAtomicState = true;
			break;
		}
	}
	if (!foundAtomicState)
		return false;

	// When the configuration contains an atomic state, it contains all of its <state> and <parallel> ancestors.
	for (int i = 0; i < _configuration.size(); i++) {
		if (isAtomic(_configuration[i])) {
			Node<std::string> parent = _configuration[i];
			while((parent = parent.getParentNode())) {
				if (isState(parent) &&
				        (boost::iequals(LOCALNAME(parent), "state") ||
				         boost::iequals(LOCALNAME(parent), "parallel"))) {
					if (!isMember(parent, _configuration))
						return false;
				}
			}
		}
	}

	// When the configuration contains a non-atomic <state>, it contains one and only one of the state's children
	for (int i = 0; i < _configuration.size(); i++) {
		if (!isAtomic(_configuration[i]) && !isParallel(_configuration[i])) {
			bool foundChildState = false;
			NodeSet<std::string> childs = getChildStates(_configuration[i]);
			for (int j = 0; j < childs.size(); j++) {
				if (isMember(childs[j], _configuration)) {
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
	for (int i = 0; i < _configuration.size(); i++) {
		if (isParallel(_configuration[i])) {
			NodeSet<std::string> childs = getChildStates(_configuration[i]);
			for (int j = 0; j < childs.size(); j++) {
				if (!isMember(childs[j], _configuration) && !isHistory(childs[j]))
					return false;
			}
		}
	}

	// everything worked out fine!
	return true;
}

void Interpreter::dump() {
	if (!_document)
		return;
	std::cout << _document;
}


}