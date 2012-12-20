#include "uscxml/Common.h"
#include "uscxml/Interpreter.h"
#include "uscxml/URL.h"
#include "uscxml/debug/SCXMLDotWriter.h"

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


namespace uscxml {

using namespace Arabica::XPath;
using namespace Arabica::DOM;

boost::uuids::random_generator Interpreter::uuidGen;
const std::string Interpreter::getUUID() {
	return boost::lexical_cast<std::string>(uuidGen());
}

Interpreter::Interpreter() {
#ifdef _WIN32
	WSADATA wsaData;
	WSAStartup(MAKEWORD(2, 2), &wsaData);
#endif
}

Interpreter* Interpreter::fromDOM(const Arabica::DOM::Node<std::string>& node) {
	Arabica::DOM::DOMImplementation<std::string> domFactory = Arabica::SimpleDOM::DOMImplementation<std::string>::getDOMImplementation();
	Interpreter* interpreter = new Interpreter();
	interpreter->_doc = domFactory.createDocument("http://www.w3.org/2005/07/scxml", "scxml", 0);
	interpreter->_doc.appendChild(node);
	interpreter->init();

	return interpreter;
}

Interpreter* Interpreter::fromXML(const std::string& xml) {
	std::istringstream is(xml);
	Arabica::SAX::InputSource<std::string> inputSource;
	return fromInputSource(inputSource);
}

Interpreter* Interpreter::fromURI(const std::string& uri) {
	Arabica::SAX::InputSource<std::string> inputSource(uri);
	Interpreter* interpreter = fromInputSource(inputSource);

	// try to establish URI root for relative src attributes in document
	interpreter->_baseURI = toBaseURI(Arabica::io::URI(uri));
	return interpreter;
}

Arabica::io::URI Interpreter::toBaseURI(const Arabica::io::URI& uri) {
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
		uriPath = uriPath.substr(0, uriPath.find_last_of("/\\"));
		ssBaseURI << uriPath;
	}
	return Arabica::io::URI(ssBaseURI.str());
}

bool Interpreter::makeAbsolute(Arabica::io::URI& uri) {
	if (uri.is_absolute())
		return true;

	if (_baseURI.as_string().size() > 0) {
		std::stringstream ssAbsoluteURI;
		if (_baseURI.scheme().size() > 0)
			ssAbsoluteURI << _baseURI.scheme() << "://";
		if (_baseURI.host().size() > 0) {
			ssAbsoluteURI << _baseURI.host();
			if (!boost::iequals(_baseURI.port(), "0"))
				ssAbsoluteURI << ":" << _baseURI.port();
		}
		if (_baseURI.path().size() > 0) {
			ssAbsoluteURI << _baseURI.path() << "/" << uri.path();
		}
		uri = Arabica::io::URI(ssAbsoluteURI.str());
		return true;
	}
	return false;
}

Interpreter* Interpreter::fromInputSource(Arabica::SAX::InputSource<std::string>& source) {
	Interpreter* interpreter = new Interpreter();

	Arabica::SAX2DOM::Parser<std::string> domParser;
	Arabica::SAX::CatchErrorHandler<std::string> errorHandler;
	domParser.setErrorHandler(errorHandler);
	if(!domParser.parse(source) || !domParser.getDocument().hasChildNodes()) {
		LOG(INFO) << "could not parse input:";
		if(errorHandler.errorsReported()) {
			LOG(ERROR) << errorHandler.errors() << std::endl;
		} else {
			Arabica::SAX::InputSourceResolver resolver(source, Arabica::default_string_adaptor<std::string>());
			if (!resolver.resolve()) {
				LOG(ERROR) << "no such file";
			}
		}
	} else {
		interpreter->_doc = domParser.getDocument();
	}
	interpreter->init();
	return interpreter;
}

void Interpreter::init() {
	_thread = NULL;
	_dataModel = NULL;
	_invoker = NULL;
	_running = false;
	_sendQueue = new DelayedEventQueue();
	_sendQueue->start();
	if (_doc) {
		// do we have a xmlns attribute?
		std::string ns = _doc.getDocumentElement().getNamespaceURI();
		if(ns.size() > 0) {
			_nsContext.addNamespaceDeclaration(ns, "sc");
			_xpath.setNamespaceContext(_nsContext);
			_nsPrefix = "sc:";
		}
		NodeList<std::string> scxmls = _doc.getElementsByTagName("scxml");
		if (scxmls.getLength() > 0) {
			_scxml = (Arabica::DOM::Element<std::string>)scxmls.item(0);
			normalize(_doc);
			_name = (HAS_ATTR(_scxml, "name") ? ATTR(_scxml, "name") : getUUID());
		} else {
			LOG(ERROR) << "Cannot find SCXML element" << std::endl;
		}
	}
}

Interpreter::~Interpreter() {
	std::map<std::string, IOProcessor*>::iterator ioProcessorIter = _ioProcessors.begin();
	while(ioProcessorIter != _ioProcessors.end()) {
		delete ioProcessorIter->second;
		ioProcessorIter++;
	}
	if (_thread) {
		_running = false;
		_externalQueue.push(Event());
		_thread->join();
		delete(_thread);
	}
	delete _dataModel;
	delete _sendQueue;
}

void Interpreter::start() {
	_thread = new tthread::thread(Interpreter::run, this);
}

void Interpreter::run(void* instance) {
	((Interpreter*)instance)->interpret();
}

void Interpreter::waitForStabilization() {
	tthread::lock_guard<tthread::mutex> lock(_mutex);
	_stabilized.wait(_mutex);
}

// see: http://www.w3.org/TR/scxml/#AlgorithmforSCXMLInterpretation
void Interpreter::interpret() {
	if (!_scxml)
		return;
//  dump();

	_sessionId = getUUID();

	if(HAS_ATTR(_scxml, "datamodel")) {
		_dataModel = Factory::getDataModel(ATTR(_scxml, "datamodel"), this);
		if(_dataModel == NULL) {
			LOG(ERROR) << "No datamodel for " << ATTR(_scxml, "datamodel") << " registered";
			return;
		}
	}

	setupIOProcessors();

	// executeGlobalScriptElements
	NodeSet<std::string> globalScriptElems = _xpath.evaluate("/" + _nsPrefix + "scxml/" + _nsPrefix + "script", _doc).asNodeSet();
	for (unsigned int i = 0; i < globalScriptElems.size(); i++) {
//    std::cout << globalScriptElems[i].getFirstChild().getNodeValue() << std::endl;
		if (_dataModel)
			executeContent(globalScriptElems[i]);
	}

	_running = true;

	std::string binding = _xpath.evaluate("/" + _nsPrefix + "scxml/@binding", _doc).asString();
	_binding = (boost::iequals(binding, "late") ? LATE : EARLY);

	// initialize all data elements
	if (_dataModel && _binding == EARLY) {
		NodeSet<std::string> dataElems = _xpath.evaluate("//" + _nsPrefix + "data", _doc).asNodeSet();
		for (unsigned int i = 0; i < dataElems.size(); i++) {
			initializeData(dataElems[i]);
		}
	} else if(_dataModel) {
		NodeSet<std::string> topDataElems = _xpath.evaluate("/" + _nsPrefix + "scxml/" + _nsPrefix + "datamodel/" + _nsPrefix + "data", _doc).asNodeSet();
		for (unsigned int i = 0; i < topDataElems.size(); i++) {
			initializeData(topDataElems[i]);
		}
	}

	// we made sure during normalization that this element exists
	NodeSet<std::string> initialTransitions = _xpath.evaluate("/" + _nsPrefix + "scxml/" + _nsPrefix + "initial/" + _nsPrefix + "transition", _doc).asNodeSet();
	assert(initialTransitions.size() > 0);
	initialTransitions.push_back(initialTransitions[0]);
	enterStates(initialTransitions);

	mainEventLoop();
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
		if (!HAS_ATTR(data, "id"))
			return;

		if (HAS_ATTR(data, "expr")) {
			std::string value = ATTR(data, "expr");
			_dataModel->assign(ATTR(data, "id"), value);
		} else if (HAS_ATTR(data, "src")) {
			Arabica::SAX::InputSourceResolver resolver(Arabica::SAX::InputSource<std::string>(ATTR(data, "src")),
			        Arabica::default_string_adaptor<std::string>());
			std::string value = std::string(std::istreambuf_iterator<char>(*resolver.resolve()), std::istreambuf_iterator<char>());
			_dataModel->assign(ATTR(data, "id"), value);
		} else if (data.hasChildNodes()) {
			// search for the text node with the actual script
			NodeList<std::string> dataChilds = data.getChildNodes();
			for (int i = 0; i < dataChilds.getLength(); i++) {
				if (dataChilds.item(i).getNodeType() == Node_base::TEXT_NODE) {
					Data value = Data(dataChilds.item(i).getNodeValue());
					_dataModel->assign(ATTR(data, "id"), value);
					break;
				}
			}
//      std::cout << value << std::endl;
		}

	} catch (Event e) {
		LOG(ERROR) << "Syntax error in send element:" << std::endl << e << std::endl;
	}
}

void Interpreter::normalize(const Arabica::DOM::Document<std::string>& node) {
	// make sure every state has an id and set isFirstEntry to true
	Arabica::XPath::NodeSet<std::string> states = _xpath.evaluate("//" + _nsPrefix + "state", _doc).asNodeSet();
	for (int i = 0; i < states.size(); i++) {
		Arabica::DOM::Element<std::string> stateElem = Arabica::DOM::Element<std::string>(states[i]);
		stateElem.setAttribute("isFirstEntry", "true");
		if (!stateElem.hasAttribute("id")) {
			stateElem.setAttribute("id", getUUID());
		}
	}

	// make sure every invoke has an idlocation or id
	Arabica::XPath::NodeSet<std::string> invokes = _xpath.evaluate("//" + _nsPrefix + "invoke", _doc).asNodeSet();
	for (int i = 0; i < invokes.size(); i++) {
		Arabica::DOM::Element<std::string> invokeElem = Arabica::DOM::Element<std::string>(invokes[i]);
		if (!invokeElem.hasAttribute("id") && !invokeElem.hasAttribute("idlocation")) {
			invokeElem.setAttribute("id", getUUID());
		}
//    // make sure every finalize element contained has the invoke id as an attribute
//    Arabica::XPath::NodeSet<std::string> finalizes = _xpath.evaluate("" + _nsPrefix + "finalize", invokeElem).asNodeSet();
//    for (int j = 0; j < finalizes.size(); j++) {
//      Arabica::DOM::Element<std::string> finalizeElem = Arabica::DOM::Element<std::string>(finalizes[j]);
//      finalizeElem.setAttribute("invokeid", invokeElem.getAttribute("id"));
//    }
	}

	Arabica::XPath::NodeSet<std::string> finals = _xpath.evaluate("//" + _nsPrefix + "final", _doc).asNodeSet();
	for (int i = 0; i < finals.size(); i++) {
		Arabica::DOM::Element<std::string> finalElem = Arabica::DOM::Element<std::string>(finals[i]);
		finalElem.setAttribute("isFirstEntry", "true");
		if (!finalElem.hasAttribute("id")) {
			finalElem.setAttribute("id", getUUID());
		}
	}

	Arabica::XPath::NodeSet<std::string> histories = _xpath.evaluate("//" + _nsPrefix + "history", _doc).asNodeSet();
	for (int i = 0; i < histories.size(); i++) {
		Arabica::DOM::Element<std::string> historyElem = Arabica::DOM::Element<std::string>(histories[i]);
		if (!historyElem.hasAttribute("id")) {
			historyElem.setAttribute("id", getUUID());
		}
	}

	Arabica::XPath::NodeSet<std::string> scxml = _xpath.evaluate("/" + _nsPrefix + "scxml", _doc).asNodeSet();
	if (!((Arabica::DOM::Element<std::string>)scxml[0]).hasAttribute("id")) {
		((Arabica::DOM::Element<std::string>)scxml[0]).setAttribute("id", getUUID());
	}

	// create a pseudo initial and transition element
	Arabica::DOM::Element<std::string> initialState = (Arabica::DOM::Element<std::string>)getInitialState();
	Arabica::DOM::Element<std::string> initialElem = _doc.createElement("initial");
	Arabica::DOM::Element<std::string> transitionElem = _doc.createElement("transition");
	transitionElem.setAttribute("target", initialState.getAttribute("id"));
	initialElem.appendChild(transitionElem);
	_scxml.appendChild(initialElem);

}

void Interpreter::mainEventLoop() {
	while(_running) {
		NodeSet<std::string> enabledTransitions;
		_stable = false;

		// Here we handle eventless transitions and transitions
		// triggered by internal events until machine is stable
		while(_running && !_stable) {
#if 0
			std::cout << "Configuration: ";
			for (int i = 0; i < _configuration.size(); i++) {
				std::cout << ((Arabica::DOM::Element<std::string>)_configuration[i]).getAttribute("id") << ", ";
			}
			std::cout << std::endl;
#endif
			enabledTransitions = selectEventlessTransitions();
			if (enabledTransitions.size() == 0) {
				if (_internalQueue.size() == 0) {
					_stable = true;
				} else {
					Event internalEvent = _internalQueue.front();
					_internalQueue.pop_front();
#if 0
					std::cout << "Received internal event " << internalEvent.name << std::endl;
#endif
					if (_dataModel)
						_dataModel->setEvent(internalEvent);
					enabledTransitions = selectTransitions(internalEvent.name);
				}
			}
			if (!enabledTransitions.empty())
				microstep(enabledTransitions);
		}

		for (unsigned int i = 0; i < _statesToInvoke.size(); i++) {
			NodeSet<std::string> invokes = _xpath.evaluate("" + _nsPrefix + "invoke", _statesToInvoke[i]).asNodeSet();
			for (unsigned int j = 0; j < invokes.size(); j++) {
				invoke(invokes[j]);
			}
		}

		_statesToInvoke = NodeSet<std::string>();
		if (!_internalQueue.empty())
			continue;

		{
			tthread::lock_guard<tthread::mutex> lock(_mutex);
			_stabilized.notify_all();
		}

		Event externalEvent = _externalQueue.pop();
		if (!_running)
			exitInterpreter();

		if (_dataModel && boost::iequals(externalEvent.name, "cancel.invoke." + _sessionId))
			break;

		if (_dataModel)
			try {
				_dataModel->setEvent(externalEvent);
			} catch (Event e) {
				LOG(ERROR) << "Syntax error while setting external event:" << std::endl << e << std::endl;
			}
		for (unsigned int i = 0; i < _configuration.size(); i++) {
			NodeSet<std::string> invokes = _xpath.evaluate("" + _nsPrefix + "invoke", _configuration[i]).asNodeSet();
			for (unsigned int j = 0; j < invokes.size(); j++) {
				Arabica::DOM::Element<std::string> invokeElem = (Arabica::DOM::Element<std::string>)invokes[j];
				std::string invokeId = invokeElem.getAttribute("id");
				std::string autoForward = invokeElem.getAttribute("autoforward");
				if (boost::iequals(invokeId, externalEvent.invokeid)) {

					Arabica::XPath::NodeSet<std::string> finalizes = _xpath.evaluate("" + _nsPrefix + "finalize", invokeElem).asNodeSet();
					for (int k = 0; k < finalizes.size(); k++) {
						Arabica::DOM::Element<std::string> finalizeElem = Arabica::DOM::Element<std::string>(finalizes[k]);
						executeContent(finalizeElem);
					}


				}
				if (autoForward.length() > 0) {
					// @TODO
//          send(invokeId, externalEvent);
				}
			}
		}
		enabledTransitions = selectTransitions(externalEvent.name);
		if (!enabledTransitions.empty())
			microstep(enabledTransitions);
	}
	exitInterpreter();
}

void Interpreter::internalDoneSend(const Arabica::DOM::Node<std::string>& state) {
	if (!isState(state))
		return;

	Arabica::DOM::Element<std::string> stateElem = (Arabica::DOM::Element<std::string>)state;
	Arabica::DOM::Element<std::string> parent = (Arabica::DOM::Element<std::string>)stateElem.getParentNode();
	Event event;

	Arabica::XPath::NodeSet<std::string> doneDatas = _xpath.evaluate("" + _nsPrefix + "donedata", stateElem).asNodeSet();
	if (doneDatas.size() > 0) {
		// only process first donedata element
		Arabica::DOM::Node<std::string> doneData = doneDatas[0];
		NodeList<std::string> doneChilds = doneData.getChildNodes();
		for (int i = 0; i < doneChilds.getLength(); i++) {
			if (!doneChilds.item(i).getNodeType() == Node_base::ELEMENT_NODE)
				continue;
			if (boost::iequals(TAGNAME(doneChilds.item(i)), "param")) {
				if (!HAS_ATTR(doneChilds.item(i), "name")) {
					LOG(ERROR) << "param element is missing name attribut";
					continue;
				}
				std::string paramValue;
				if (HAS_ATTR(doneChilds.item(i), "expr") && _dataModel) {
					std::string location = _dataModel->evalAsString(ATTR(doneChilds.item(i), "expr"));
					paramValue = _dataModel->evalAsString(location);
				} else if(HAS_ATTR(doneChilds.item(i), "location") && _dataModel) {
					paramValue = _dataModel->evalAsString(ATTR(doneChilds.item(i), "location"));
				} else {
					LOG(ERROR) << "param element is missing expr or location or no datamodel is specified";
					continue;
				}
				event.compound[ATTR(doneChilds.item(i), "name")] = paramValue;
			}
			if (boost::iequals(TAGNAME(doneChilds.item(i)), "content")) {
				if (HAS_ATTR(doneChilds.item(i), "expr")) {
					if (_dataModel) {
						event.compound["content"] = Data(_dataModel->evalAsString(ATTR(doneChilds.item(i), "expr")), Data::VERBATIM);
					} else {
						LOG(ERROR) << "content element has expr attribute but no datamodel is specified.";
					}
				} else if (doneChilds.item(i).hasChildNodes()) {
					event.compound["content"] = Data(doneChilds.item(i).getFirstChild().getNodeValue(), Data::VERBATIM);
				} else {
					LOG(ERROR) << "content element does not specify any content.";
				}

			}
		}
	}

	event.name = "done.state." + parent.getAttribute("id");
	_internalQueue.push_back(event);

}

void Interpreter::send(const Arabica::DOM::Node<std::string>& element) {
	SendRequest sendReq;
	try {
		// event
		if (HAS_ATTR(element, "eventexpr") && _dataModel) {
			sendReq.name = _dataModel->evalAsString(ATTR(element, "eventexpr"));
		} else if (HAS_ATTR(element, "event")) {
			sendReq.name = ATTR(element, "event");
		}
		// target
		if (HAS_ATTR(element, "targetexpr") && _dataModel) {
			sendReq.target = _dataModel->evalAsString(ATTR(element, "targetexpr"));
		} else if (HAS_ATTR(element, "target")) {
			sendReq.target = ATTR(element, "target");
		}
		// type
		if (HAS_ATTR(element, "typeexpr") && _dataModel) {
			sendReq.type = _dataModel->evalAsString(ATTR(element, "typeexpr"));
		} else if (HAS_ATTR(element, "type")) {
			sendReq.type = ATTR(element, "type");
		} else {
			sendReq.type = "http://www.w3.org/TR/scxml/#SCXMLEventProcessor";
		}
		// id
		if (HAS_ATTR(element, "idlocation") && _dataModel) {
			sendReq.sendid = _dataModel->evalAsString(ATTR(element, "idlocation"));
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

		// delay
		std::string delay;
		sendReq.delayMs = 0;
		if (HAS_ATTR(element, "delayexpr") && _dataModel) {
			delay = _dataModel->evalAsString(ATTR(element, "delayexpr"));
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
		// namelist
		if (HAS_ATTR(element, "namelist")) {
			std::vector<std::string> names = tokenizeIdRefs(ATTR(element, "namelist"));
			for (int i = 0; i < names.size(); i++) {
				sendReq.namelist[names[i]] = _dataModel->evalAsString(names[i]);
			}
		}

		// params
		NodeSet<std::string> params = _xpath.evaluate("" + _nsPrefix + "param", element).asNodeSet();
		for (int i = 0; i < params.size(); i++) {
			if (!HAS_ATTR(params[i], "name")) {
				LOG(ERROR) << "param element is missing name attribut";
				continue;
			}
			std::string paramValue;
			if (HAS_ATTR(params[i], "expr") && _dataModel) {
				paramValue = _dataModel->evalAsString(ATTR(params[i], "expr"));
			} else if(HAS_ATTR(params[i], "location") && _dataModel) {
				paramValue = _dataModel->evalAsString(ATTR(params[i], "location"));
			} else {
				LOG(ERROR) << "param element is missing expr or location or no datamodel is specified";
				continue;
			}
			sendReq.params.insert(std::make_pair(ATTR(params[i], "name"), paramValue));
		}

		// content
		NodeSet<std::string> contents = _xpath.evaluate("" + _nsPrefix + "content", element).asNodeSet();
		if (contents.size() > 1)
			LOG(ERROR) << "Only a single content element is allowed for send elements - using first one";
		if (contents.size() > 0) {
			if (HAS_ATTR(contents[0], "expr")) {
				if (_dataModel) {
					sendReq.content = _dataModel->evalAsString(ATTR(contents[0], "expr"));
				} else {
					LOG(ERROR) << "content element has expr attribute but no datamodel is specified.";
				}
			} else if (contents[0].hasChildNodes()) {
				sendReq.content = contents[0].getFirstChild().getNodeValue();
			} else {
				LOG(ERROR) << "content element does not specify any content.";
			}
		}

		assert(_sendIds.find(sendReq.sendid) == _sendIds.end());
		_sendIds[sendReq.sendid] = std::make_pair(this, sendReq);
		if (sendReq.delayMs > 0) {
			_sendQueue->addEvent(sendReq.sendid, Interpreter::delayedSend, sendReq.delayMs, &_sendIds[sendReq.sendid]);
		} else {
			delayedSend(&_sendIds[sendReq.sendid], sendReq.name);
		}

	} catch (Event e) {
		LOG(ERROR) << "Syntax error in send element:" << std::endl << e << std::endl;
	}
}

void Interpreter::delayedSend(void* userdata, std::string eventName) {
	std::pair<Interpreter*, SendRequest>* data = (std::pair<Interpreter*, SendRequest>*)(userdata);

	Interpreter* INSTANCE = data->first;
	SendRequest sendReq = data->second;

	if (boost::iequals(sendReq.target, "#_parent")) {
		// send to parent scxml session
		if (INSTANCE->_invoker != NULL) {
			INSTANCE->_invoker->sendToParent(sendReq);
		} else {
			LOG(ERROR) << "Can not send to parent, we were not invoked" << std::endl;
		}
	} else if (sendReq.target.find_first_of("#_") == 0) {
		// send to invoker
		std::string invokeId = sendReq.target.substr(2, sendReq.target.length() - 2);
		if (INSTANCE->_invokerIds.find(invokeId) != INSTANCE->_invokerIds.end()) {
			INSTANCE->_invokerIds[invokeId]->send(sendReq);
		} else {
			LOG(ERROR) << "Can not send to invoked component " << invokeId << ", no such invokeId" << std::endl;
		}
	} else if (sendReq.target.length() == 0) {
		INSTANCE->receive(sendReq);
	} else {
		IOProcessor* ioProc = INSTANCE->getIOProcessor(sendReq.type);
		if (ioProc != NULL) {
			ioProc->send(sendReq);
		}
	}
	assert(INSTANCE->_sendIds.find(sendReq.sendid) != INSTANCE->_sendIds.end());
	INSTANCE->_sendIds.erase(sendReq.sendid);
}

void Interpreter::invoke(const Arabica::DOM::Node<std::string>& element) {
	InvokeRequest invokeReq;
	try {
		// type
		if (HAS_ATTR(element, "typeexpr") && _dataModel) {
			invokeReq.type = _dataModel->evalAsString(ATTR(element, "typeexpr"));
		} else if (HAS_ATTR(element, "type")) {
			invokeReq.type = ATTR(element, "type");
		} else {
			LOG(ERROR) << "invoke element is missing expr or typeexpr or no datamodel is specified";
		}

		// src
		std::string source;
		if (HAS_ATTR(element, "srcexpr") && _dataModel) {
			source = _dataModel->evalAsString(ATTR(element, "srcexpr"));
		} else if (HAS_ATTR(element, "src")) {
			source = ATTR(element, "src");
		}
		if (source.length() > 0) {
			Arabica::io::URI srcURI(source);
			if (!makeAbsolute(srcURI)) {
				LOG(ERROR) << "invoke element has relative src URI with no baseURI set.";
				return;
			}
			invokeReq.src = srcURI.as_string();
		}

		// id
		if (HAS_ATTR(element, "idlocation") && _dataModel) {
			invokeReq.invokeid = _dataModel->evalAsString(ATTR(element, "idlocation"));
		} else if (HAS_ATTR(element, "id")) {
			invokeReq.invokeid = ATTR(element, "id");
		} else {
			assert(false);
		}

		// namelist
		if (HAS_ATTR(element, "namelist")) {
			invokeReq.namelist = ATTR(element, "namelist");
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
		NodeSet<std::string> params = _xpath.evaluate("" + _nsPrefix + "param", element).asNodeSet();
		for (int i = 0; i < params.size(); i++) {
			if (!HAS_ATTR(params[i], "name")) {
				LOG(ERROR) << "param element is missing name attribut";
				continue;
			}
			std::string paramValue;
			if (HAS_ATTR(params[i], "expr")) {
				if (_dataModel) {
					paramValue = _dataModel->evalAsString(ATTR(params[i], "expr"));
				} else {
					paramValue = ATTR(params[i], "expr");
				}
			} else if(HAS_ATTR(params[i], "location") && _dataModel) {
				paramValue = _dataModel->evalAsString(ATTR(params[i], "location"));
			} else {
				LOG(ERROR) << "param element is missing expr or location or no datamodel is specified";
				continue;
			}
//      invokeReq.params[ATTR(params[i], "name")].push_back(paramValue);
			invokeReq.params.insert(std::make_pair(ATTR(params[i], "name"), paramValue));

		}

		// content
		NodeSet<std::string> contents = _xpath.evaluate("" + _nsPrefix + "content", element).asNodeSet();
		if (contents.size() > 1)
			LOG(ERROR) << "Only a single content element is allowed for send elements - using first one";
		if (contents.size() > 0) {
			invokeReq.content = contents[0].getNodeValue();
		}

		Invoker* invoker = Factory::getInvoker(invokeReq.type, this);
		if (invoker != NULL) {
			_invokerIds[invokeReq.invokeid] = invoker;
			LOG(INFO) << "Added " << invokeReq.type << " at " << invokeReq.invokeid;
			invoker->invoke(invokeReq);
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
		invokeId = _dataModel->evalAsString(ATTR(element, "idlocation"));
	} else if (HAS_ATTR(element, "id")) {
		invokeId = ATTR(element, "id");
	} else {
		assert(false);
	}
	if (_invokerIds.find(invokeId) != _invokerIds.end()) {
		LOG(INFO) << "Removed invoker at " << invokeId;
		delete (_invokerIds[invokeId]);
		_invokerIds.erase(invokeId);
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
		ancestors.push_back(atomicStates[i]);
		for (unsigned int j = 0; j < ancestors.size(); j++) {
			NodeSet<std::string> transitions = _xpath.evaluate("" + _nsPrefix + "transition", ancestors[j]).asNodeSet();
			for (unsigned int k = 0; k < transitions.size(); k++) {
				if (((Arabica::DOM::Element<std::string>)transitions[k]).hasAttribute("event") &&
				        nameMatch(((Arabica::DOM::Element<std::string>)transitions[k]).getAttribute("event"), event) &&
				        hasConditionMatch(transitions[k])) {
					enabledTransitions.push_back(transitions[k]);
					goto LOOP;
				}
			}
		}
LOOP:
		;
	}
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
			NodeSet<std::string> transitions = _xpath.evaluate("" + _nsPrefix + "transition", ancestors[j]).asNodeSet();
			for (unsigned int k = 0; k < transitions.size(); k++) {
				if (!((Arabica::DOM::Element<std::string>)transitions[k]).hasAttribute("event") && hasConditionMatch(transitions[k])) {
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

bool Interpreter::hasConditionMatch(const Arabica::DOM::Node<std::string>& conditional) {
	try {
		if (_dataModel && HAS_ATTR(conditional, "cond"))
			return _dataModel->evalAsBool(ATTR(conditional, "cond"));
	} catch (Event e) {
		LOG(ERROR) << "Syntax error in cond attribute of " << TAGNAME(conditional) << " element:" << std::endl << e << std::endl;
		return false;
	}
	return true; // no condition is always true
}

Arabica::XPath::NodeSet<std::string> Interpreter::filterPreempted(const Arabica::XPath::NodeSet<std::string>& enabledTransitions) {
	Arabica::XPath::NodeSet<std::string> filteredTransitions;
	for (unsigned int i = 0; i < enabledTransitions.size(); i++) {
		Arabica::DOM::Node<std::string> t = enabledTransitions[i];
		for (unsigned int j = i+1; j < enabledTransitions.size(); j++) {
			Arabica::DOM::Node<std::string> t2 = enabledTransitions[j];
			if (isPreemptingTransition(t2, t))
				goto LOOP;
		}
		filteredTransitions.push_back(t);
LOOP:
		;
	}
	return filteredTransitions;
}

bool Interpreter::isPreemptingTransition(const Arabica::DOM::Node<std::string>& t1, const Arabica::DOM::Node<std::string>& t2) {
	if (t1 == t2)
		return false;
	if (isWithinSameChild(t1) && (!isTargetless(t2) && !isWithinSameChild(t2)))
		return true;
	if (!isTargetless(t1) && !isWithinSameChild(t1))
		return true;
	return false;
}

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
		Arabica::XPath::NodeSet<std::string> onExitElems = _xpath.evaluate("" + _nsPrefix + "onexit", statesToExit[i]).asNodeSet();
		for (int j = 0; j < onExitElems.size(); j++) {
			executeContent(onExitElems[j]);
		}
		Arabica::XPath::NodeSet<std::string> invokeElems = _xpath.evaluate("" + _nsPrefix + "invoke", statesToExit[i]).asNodeSet();
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
	for (int i = 0; i < enabledTransitions.size(); i++) {
		executeContent(enabledTransitions[i]);
	}
}

void Interpreter::executeContent(const NodeList<std::string>& content) {
	for (unsigned int i = 0; i < content.getLength(); i++) {
		if (content.item(i).getNodeType() != Node_base::ELEMENT_NODE)
			continue;
		executeContent(content.item(i));
	}
}

void Interpreter::executeContent(const Arabica::DOM::Node<std::string>& content) {
	if (content.getNodeType() != Node_base::ELEMENT_NODE)
		return;

	if (false) {
	} else if (boost::iequals(TAGNAME(content), "raise")) {
		// --- RAISE --------------------------
		if (HAS_ATTR(content, "event")) {
			Event event;
			event.name = ATTR(content, "event");
			_internalQueue.push_back(event);
		}
	} else if (boost::iequals(TAGNAME(content), "if")) {
		// --- IF / ELSEIF / ELSE --------------
		Arabica::DOM::Element<std::string> ifElem = (Arabica::DOM::Element<std::string>)content;
		if(hasConditionMatch(ifElem)) {
			// condition is true, execute all content up to an elseif, else or end
			if (ifElem.hasChildNodes()) {
				NodeList<std::string> childs = ifElem.getChildNodes();
				for (unsigned int i = 0; i < childs.getLength(); i++) {
					if (childs.item(i).getNodeType() != Node_base::ELEMENT_NODE)
						continue;
					if (boost::iequals(TAGNAME(childs.item(i)), "elsif") ||
					        boost::iequals(TAGNAME(childs.item(i)), "else"))
						break;
					executeContent(childs.item(i));
				}
			}
		} else {
			// condition does not match - do we have an elsif?
			if (ifElem.hasChildNodes()) {
				NodeList<std::string> elseifElem = ifElem.getElementsByTagName("elseif");
				for (unsigned int i = 0; i < elseifElem.getLength(); i++) {
					if (hasConditionMatch(elseifElem.item(i))) {
						executeContent(elseifElem.item(i).getChildNodes());
						goto ELSIF_ELEM_MATCH;
					}
				}
				NodeList<std::string> elseElem = ifElem.getElementsByTagName("else");
				if (elseElem.getLength() > 0)
					executeContent(elseElem.item(0).getChildNodes());
			}
		}
ELSIF_ELEM_MATCH:
		;
	} else if (boost::iequals(TAGNAME(content), "elseif")) {
		std::cerr << "Found single elsif to evaluate!" << std::endl;
	} else if (boost::iequals(TAGNAME(content), "else")) {
		std::cerr << "Found single else to evaluate!" << std::endl;
	} else if (boost::iequals(TAGNAME(content), "foreach")) {
		// --- FOREACH --------------------------
		if (_dataModel) {
			if (HAS_ATTR(content, "array") && HAS_ATTR(content, "item")) {
				std::string array = ATTR(content, "array");
				std::string item = ATTR(content, "item");
				std::string index = (HAS_ATTR(content, "index") ? ATTR(content, "index") : "");
				uint32_t iterations = _dataModel->getLength(array);
				_dataModel->pushContext(); // copy old and enter new context
				for (uint32_t iteration = 0; iteration < iterations; iteration++) {
					{
						// assign array element to item
						std::stringstream ss;
						ss << array << "[" << iteration << "]";
						_dataModel->assign(item, ss.str());
					}
					if (index.length() > 0) {
						// assign iteration element to index
						std::stringstream ss;
						ss << iteration;
						_dataModel->assign(index,ss.str());
					}
					if (content.hasChildNodes())
						executeContent(content.getChildNodes());
				}
				_dataModel->popContext(); // leave stacked context
			} else {
				LOG(ERROR) << "Expected array and item attributes with foreach element!" << std::endl;
			}
		}
	} else if (boost::iequals(TAGNAME(content), "log")) {
		// --- LOG --------------------------
		Arabica::DOM::Element<std::string> logElem = (Arabica::DOM::Element<std::string>)content;
		if (logElem.hasAttribute("expr")) {
			if (_dataModel) {
				try {
					std::cout << _dataModel->evalAsString(logElem.getAttribute("expr")) << std::endl;
				} catch (Event e) {
					LOG(ERROR) << "Syntax error in expr attribute of log element:" << std::endl << e << std::endl;
				}
			} else {
				std::cout << logElem.getAttribute("expr") << std::endl;
			}
		}
	} else if (boost::iequals(TAGNAME(content), "assign")) {
		// --- ASSIGN --------------------------
		if (_dataModel && HAS_ATTR(content, "location") && HAS_ATTR(content, "expr")) {
			try {
				_dataModel->assign(ATTR(content, "location"), ATTR(content, "expr"));
			} catch (Event e) {
				LOG(ERROR) << "Syntax error in attributes of assign element:" << std::endl << e << std::endl;
			}
		}
	} else if (boost::iequals(TAGNAME(content), "validate")) {
		// --- VALIDATE --------------------------
		if (_dataModel) {
			std::string location = (HAS_ATTR(content, "location") ? ATTR(content, "location") : "");
			std::string schema = (HAS_ATTR(content, "schema") ? ATTR(content, "schema") : "");
			_dataModel->validate(location, schema);
		}
	} else if (boost::iequals(TAGNAME(content), "script")) {
		// --- SCRIPT --------------------------
		if (_dataModel) {
			if (HAS_ATTR(content, "src")) {
				Arabica::io::URI url(ATTR(content, "src"));
				if (!makeAbsolute(url)) {
					LOG(ERROR) << "script element has relative URI " << ATTR(content, "src") <<  " with no base URI set for interpreter";
					return;
				}

				std::stringstream srcContent;
				URL scriptUrl(url.as_string());
				srcContent << scriptUrl;

				try {
					_dataModel->eval(srcContent.str());
				} catch (Event e) {
					LOG(ERROR) << "Syntax error while executing script element from '" << ATTR(content, "src") << "':" << std::endl << e << std::endl;
				}
			} else {
				if (content.hasChildNodes()) {
					// search for the text node with the actual script
					if (content.getFirstChild().getNodeType() == Node_base::TEXT_NODE) {
						try {
							_dataModel->eval(content.getFirstChild().getNodeValue());
						} catch (Event e) {
							LOG(ERROR) << "Syntax error while executing script element" << std::endl << e << std::endl;
						}
					}
				}
			}
		}
	} else if (boost::iequals(TAGNAME(content), "send")) {
		// --- SEND --------------------------
		send(content);
	} else if (boost::iequals(TAGNAME(content), "cancel")) {
		// --- CANCEL --------------------------
		std::string sendId;
		try {
			if (HAS_ATTR(content, "sendidexpr")) {
				sendId = _dataModel->evalAsString(ATTR(content, "sendidexpr"));
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

	} else if (boost::iequals(TAGNAME(content), "invoke")) {
		// --- INVOKE --------------------------
	} else {
		NodeList<std::string> executable = content.getChildNodes();
		for (int i = 0; i < executable.getLength(); i++) {
			executeContent(executable.item(i));
		}
	}
}

void Interpreter::returnDoneEvent(const Arabica::DOM::Node<std::string>& state) {
}

void Interpreter::exitStates(const Arabica::XPath::NodeSet<std::string>& enabledTransitions) {
	NodeSet<std::string> statesToExit;
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

				ancestor = findLCCA(tmpStates);
			}

			for (int j = 0; j < _configuration.size(); j++) {
				if (isDescendant(_configuration[j], ancestor))
					statesToExit.push_back(_configuration[j]);
			}
		}
	}
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

	for (int i = 0; i < statesToExit.size(); i++) {
		NodeSet<std::string> historyElems = _xpath.evaluate("" + _nsPrefix + "history", statesToExit[i]).asNodeSet();
		for (int j = 0; j < historyElems.size(); j++) {
			Arabica::DOM::Element<std::string> historyElem = (Arabica::DOM::Element<std::string>)historyElems[j];
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
		}
	}

	for (int i = 0; i < statesToExit.size(); i++) {
		Arabica::XPath::NodeSet<std::string> onExitElems = _xpath.evaluate("" + _nsPrefix + "onexit", statesToExit[i]).asNodeSet();
		for (int j = 0; j < onExitElems.size(); j++) {
			executeContent(onExitElems[j]);
		}
		Arabica::XPath::NodeSet<std::string> invokeElems = _xpath.evaluate("" + _nsPrefix + "invoke", statesToExit[i]).asNodeSet();
		for (int j = 0; j < invokeElems.size(); j++) {
			cancelInvoke(invokeElems[j]);
		}
	}

//  std::cout << "States to Exit: ";
//  for (int i = 0; i < statesToExit.size(); i++) {
//    std::cout << ((Arabica::DOM::Element<std::string>)statesToExit[i]).getAttribute("id") << ", ";
//  }
//  std::cout << std::endl;

	// remove statesToExit from _configuration
	tmp.clear();
	for (int i = 0; i < _configuration.size(); i++) {
		if (!isMember(_configuration[i], statesToExit)) {
			tmp.push_back(_configuration[i]);
		}
	}
	_configuration = NodeSet<std::string>();
	_configuration.insert(_configuration.end(), tmp.begin(), tmp.end());


}

void Interpreter::enterStates(const Arabica::XPath::NodeSet<std::string>& enabledTransitions) {
	NodeSet<std::string> statesToEnter;
	NodeSet<std::string> statesForDefaultEntry;

	for (int i = 0; i < enabledTransitions.size(); i++) {
		Arabica::DOM::Element<std::string> transition = ((Arabica::DOM::Element<std::string>)enabledTransitions[i]);
		if (!isTargetless(transition)) {
			std::string transitionType = (boost::iequals(transition.getAttribute("type"), "internal") ? "internal" : "external");
			NodeSet<std::string> tStates = getTargetStates(transition);
			Arabica::DOM::Node<std::string> ancestor;
			Arabica::DOM::Node<std::string> source = getSourceState(transition);
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

			for (int j = 0; j < tStates.size(); j++) {
				addStatesToEnter(tStates[j], statesToEnter, statesForDefaultEntry);
			}

			for (int j = 0; j < tStates.size(); j++) {
				NodeSet<std::string> ancestors = getProperAncestors(tStates[j], ancestor);
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
	for (int i = 0; i < statesToEnter.size(); i++) {
		Arabica::DOM::Element<std::string> stateElem = (Arabica::DOM::Element<std::string>)statesToEnter[i];
		_configuration.push_back(stateElem);
		_statesToInvoke.push_back(stateElem);
		if (_binding == LATE && stateElem.getAttribute("isFirstEntry").size() > 0) {
			Arabica::XPath::NodeSet<std::string> dataModelElems = _xpath.evaluate("" + _nsPrefix + "datamodel", stateElem).asNodeSet();
			if(dataModelElems.size() > 0 && _dataModel) {
				Arabica::XPath::NodeSet<std::string> dataElems = _xpath.evaluate("" + _nsPrefix + "data", dataModelElems[0]).asNodeSet();
				for (int j = 0; j < dataElems.size(); j++) {
					initializeData(dataElems[j]);
				}
			}
			stateElem.setAttribute("isFirstEntry", "");
		}
		// execute onentry executable content
		Arabica::XPath::NodeSet<std::string> onEntryElems = _xpath.evaluate("" + _nsPrefix + "onentry", stateElem).asNodeSet();
		for (int j = 0; j < onEntryElems.size(); j++) {
			executeContent(onEntryElems[j]);
		}
		if (isMember(stateElem, statesForDefaultEntry)) {
			// execute initial transition content for compund states
			Arabica::XPath::NodeSet<std::string> transitions = _xpath.evaluate("" + _nsPrefix + "initial/" + _nsPrefix + "transition", stateElem).asNodeSet();
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
		if (isFinal(stateElem) && parentIsScxmlState(stateElem))
			_running = false;
	}
}

bool Interpreter::parentIsScxmlState(Arabica::DOM::Node<std::string> state) {
	Arabica::DOM::Element<std::string> stateElem = (Arabica::DOM::Element<std::string>)state;
	Arabica::DOM::Element<std::string> parentElem = (Arabica::DOM::Element<std::string>)state.getParentNode();
	if (boost::iequals(parentElem.getTagName(), "scxml"))
		return true;
	return false;
}

bool Interpreter::isInFinalState(const Arabica::DOM::Node<std::string>& state) {
//  std::cout << ATTR(state, "id") << std::endl;
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

void Interpreter::addStatesToEnter(const Arabica::DOM::Node<std::string>& state,
                                   Arabica::XPath::NodeSet<std::string>& statesToEnter,
                                   Arabica::XPath::NodeSet<std::string>& statesForDefaultEntry) {
	std::string stateId = ((Arabica::DOM::Element<std::string>)state).getAttribute("id");
	if (isHistory(state)) {
		if (_historyValue.find(stateId) != _historyValue.end()) {
			Arabica::XPath::NodeSet<std::string> historyValue = _historyValue[stateId];
			for (int i = 0; i < historyValue.size(); i++) {
				addStatesToEnter(historyValue[i], statesToEnter, statesForDefaultEntry);
				NodeSet<std::string> ancestors = getProperAncestors(historyValue[i], state);
				for (int j = 0; j < ancestors.size(); j++) {
					statesToEnter.push_back(ancestors[j]);
				}
			}
		} else {
			NodeSet<std::string> transitions = _xpath.evaluate("" + _nsPrefix + "transition", state).asNodeSet();
			for (int i = 0; i < transitions.size(); i++) {
				NodeSet<std::string> targets = getTargetStates(transitions[i]);
				for (int j = 0; j < targets.size(); j++) {
					addStatesToEnter(targets[j], statesToEnter, statesForDefaultEntry);
				}
			}
		}
	} else {
		statesToEnter.push_back(state);
		if (isCompound(state)) {
			statesForDefaultEntry.push_back(state);
#if 0
			NodeSet<std::string> tStates = getTargetStates(getInitialState(state));
			for (int i = 0; i < tStates.size(); i++) {
				addStatesToEnter(tStates[i], statesToEnter, statesForDefaultEntry);
			}
#endif
			addStatesToEnter(getInitialState(state), statesToEnter, statesForDefaultEntry);
//      NodeSet<std::string> tStates = getTargetStates(getInitialState(state));

		} else if(isParallel(state)) {
			NodeSet<std::string> childStates = getChildStates(state);
			for (int i = 0; i < childStates.size(); i++) {
				addStatesToEnter(childStates[i], statesToEnter, statesForDefaultEntry);
			}
		}
	}
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

Arabica::DOM::Node<std::string> Interpreter::findLCCA(const Arabica::XPath::NodeSet<std::string>& states) {
//  std::cout << "findLCCA: ";
//  for (int i = 0; i < states.size(); i++) {
//    std::cout << ((Arabica::DOM::Element<std::string>)states[i]).getAttribute("id") << " - " << states[i].getLocalName() << ", ";
//  }
//  std::cout << std::flush;

	Arabica::XPath::NodeSet<std::string> ancestors = getProperAncestors(states[0], Arabica::DOM::Node<std::string>());
	ancestors.push_back(states[0]); // state[0] may already be the ancestor - bug in W3C spec?
	Arabica::DOM::Node<std::string> ancestor;
	for (int i = 0; i < ancestors.size(); i++) {
		for (int j = 0; j < states.size(); j++) {
//      std::cout << "Checking " << TAGNAME(state) << " and " << TAGNAME(ancestors[i]) << std::endl;
			if (!isDescendant(states[j], ancestors[i]) && (states[j] != ancestors[i]))
				goto NEXT_ANCESTOR;
		}
		ancestor = ancestors[i];
		break;
NEXT_ANCESTOR:
		;
	}
	assert(ancestor);
//  std::cout << " -> " << ((Arabica::DOM::Element<std::string>)ancestor).getAttribute("id") << " " << ancestor.getLocalName() << std::endl;
	return ancestor;
}

Arabica::DOM::Node<std::string> Interpreter::getState(const std::string& stateId) {
	// first try atomic and compund states
//  std::cout << _nsPrefix << stateId << std::endl;
	NodeSet<std::string> target = _xpath.evaluate("//" + _nsPrefix + "state[@id='" + stateId + "']", _doc).asNodeSet();
	if (target.size() > 0)
		goto FOUND;

	// now parallel states
	target = _xpath.evaluate("//" + _nsPrefix + "parallel[@id='" + stateId + "']", _doc).asNodeSet();
	if (target.size() > 0)
		goto FOUND;

	// now final states
	target = _xpath.evaluate("//" + _nsPrefix + "final[@id='" + stateId + "']", _doc).asNodeSet();
	if (target.size() > 0)
		goto FOUND;

FOUND:
	if (target.size() > 0) {
		assert(target.size() == 1);
		return target[0];
	}
	// return the empty node
	return Arabica::DOM::Node<std::string>();
}

Arabica::DOM::Node<std::string> Interpreter::getSourceState(const Arabica::DOM::Node<std::string>& transition) {
	if (boost::iequals(TAGNAME(transition.getParentNode()), "initial"))
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
		state = _doc.getFirstChild();
		while(!isState(state))
			state = state.getNextSibling();
	}

	assert(isCompound(state) || isParallel(state));

	// initial attribute at element
	Arabica::DOM::Element<std::string> stateElem = (Arabica::DOM::Element<std::string>)state;
	if (stateElem.hasAttribute("initial")) {
		return getState(stateElem.getAttribute("initial"));
	}

	// initial element as child
	NodeSet<std::string> initialStates = _xpath.evaluate("" + _nsPrefix + "initial", state).asNodeSet();
	if(initialStates.size() == 1)
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

	// if we are called with a state, process all its transitions
	if (isState(transition)) {
		NodeList<std::string> childs = transition.getChildNodes();
		for (int i = 0; i < childs.getLength(); i++) {
			if (childs.item(i).getNodeType() == Node_base::ELEMENT_NODE && boost::iequals(TAGNAME(childs.item(i)), "transition")) {
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

NodeSet<std::string> Interpreter::getProperAncestors(const Arabica::DOM::Node<std::string>& s1,
        const Arabica::DOM::Node<std::string>& s2) {
	NodeSet<std::string> ancestors;
	if (isState(s1)) {
		Arabica::DOM::Node<std::string> node = s1;
		while((node = node.getParentNode())) {
			if (!isState(node))
				break;
			if (!boost::iequals(TAGNAME(node), "parallel") && !boost::iequals(TAGNAME(node), "state") && !boost::iequals(TAGNAME(node), "scxml"))
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
		Arabica::XPath::XPath<std::string> xpath;
		// @todo: do we need to look at parallel as well?
		if (xpath.evaluate("" + _nsPrefix + "state[id=\"" + target + "\"]", transition.getParentNode()).asNodeSet().size() > 0)
			return true;
	}
	return false;
}

bool Interpreter::isState(const Arabica::DOM::Node<std::string>& state) {
	if (!state)
		return false;
	if (state.getNodeType() != Arabica::DOM::Node_base::ELEMENT_NODE)
		return false;

	std::string tagName = TAGNAME(state);
	if (boost::iequals("state", tagName))
		return true;
	if (boost::iequals("scxml", tagName))
		return true;
	if (boost::iequals("parallel", tagName))
		return true;
	if (boost::iequals("final", tagName))
		return true;
	return false;
}

bool Interpreter::isFinal(const Arabica::DOM::Node<std::string>& state) {
	std::string tagName = TAGNAME(state);
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
	std::string tagName = TAGNAME(state);
	if (boost::iequals("initial", tagName))
		return true;
	if (boost::iequals("history", tagName))
		return true;
	return false;
}

bool Interpreter::isTransitionTarget(const Arabica::DOM::Node<std::string>& elem) {
	return (isState(elem) || boost::iequals(TAGNAME(elem), "history"));
}

bool Interpreter::isAtomic(const Arabica::DOM::Node<std::string>& state) {
	if (boost::iequals("final", TAGNAME(state)))
		return true;

	// I will assume that parallel states are not meant to be atomic.
	if (boost::iequals("parallel", TAGNAME(state)))
		return false;

	Arabica::DOM::NodeList<std::string> childs = state.getChildNodes();
	for (unsigned int i = 0; i < childs.getLength(); i++) {
		if (isState(childs.item(i)))
			return false;
	}
	return true;
}

bool Interpreter::isHistory(const Arabica::DOM::Node<std::string>& state) {
	if (boost::iequals("history", TAGNAME(state)))
		return true;
	return false;
}

bool Interpreter::isParallel(const Arabica::DOM::Node<std::string>& state) {
	if (!isState(state))
		return false;
	if (boost::iequals("parallel", TAGNAME(state)))
		return true;
	return false;
}


bool Interpreter::isCompound(const Arabica::DOM::Node<std::string>& state) {
	if (!isState(state))
		return false;

	if (boost::iequals(TAGNAME(state), "parallel"))
		return false;

	Arabica::DOM::NodeList<std::string> childs = state.getChildNodes();
	for (unsigned int i = 0; i < childs.getLength(); i++) {
		if (isState(childs.item(i)))
			return true;
	}
	return false;
}

void Interpreter::setupIOProcessors() {
	std::map<std::string, IOProcessor*>::iterator ioProcIter = Factory::getInstance()->_ioProcessors.begin();
	while(ioProcIter != Factory::getInstance()->_ioProcessors.end()) {
		_ioProcessors[ioProcIter->first] = Factory::getIOProcessor(ioProcIter->first, this);
		if (_dataModel) {
			try {
				_dataModel->registerIOProcessor(ioProcIter->first, _ioProcessors[ioProcIter->first]);
			} catch (Event e) {
				LOG(ERROR) << "Syntax error when setting _ioprocessors:" << std::endl << e << std::endl;
			}
		} else {
			LOG(INFO) << "Not registering " << ioProcIter->first << " at _ioprocessors in datamodel, no datamodel specified";
		}
		ioProcIter++;
	}
}

IOProcessor* Interpreter::getIOProcessor(const std::string& type) {
	if (_ioProcessors.find(type) == _ioProcessors.end()) {
		LOG(ERROR) << "No ioProcessor known for type " << type;
		return NULL;
	}
	return _ioProcessors[type];
}

//IOProcessor* Interpreter::getIOProcessorForId(const std::string& sendId) {
//  if (_sendQueue.find(sendId) == _sendQueue.end()) {
//    LOG(ERROR) << "No ioProcessor with pending send id " << sendId << sendId;
//    return NULL;
//  }
//  return _ioProcessorsIds[sendId];
//}

bool Interpreter::validate() {
	bool validationErrors = false;

	if (!_doc) {
		LOG(ERROR) << "Document " << _baseURI.as_string() << " was not parsed successfully" << std::endl;
		return false;
	}

	// semantic issues ------------
	if ((_xpath.evaluate("/" + _nsPrefix + "scxml/@datamodel", _doc).asNodeSet().size() == 0) &&
	        _xpath.evaluate("/" + _nsPrefix + "scxml/" + _nsPrefix + "script", _doc).asNodeSet().size() > 0) {
		LOG(ERROR) << "Script elements used, but no datamodel specified" << std::endl;
	}

	// element issues ------------
	Arabica::XPath::NodeSet<std::string> scxmlElems = _xpath.evaluate(_nsPrefix + "scxml", _doc).asNodeSet();
	if (scxmlElems.size() > 0)
		LOG(ERROR) << "More than one scxml element found" << std::endl;
	for (unsigned int i = 0; i < scxmlElems.size(); i++) {
		if (!HAS_ATTR(scxmlElems[i], "xmlns"))
			LOG(ERROR) << "scxml element has no xmlns attribute" << std::endl;
		if (!HAS_ATTR(scxmlElems[i], "version"))
			LOG(ERROR) << "scxml element has no version attribute" << std::endl;
		NodeList<std::string> childs = scxmlElems[i].getChildNodes();
		for (unsigned int j = 0; j < childs.getLength(); j++) {
			if (childs.item(j).getNodeType() != Node_base::ELEMENT_NODE)
				continue;
			if (boost::iequals(TAGNAME(childs.item(j)), "state") ||
			        boost::iequals(TAGNAME(childs.item(j)), "parallel") ||
			        boost::iequals(TAGNAME(childs.item(j)), "final") ||
			        boost::iequals(TAGNAME(childs.item(j)), "datamodel") ||
			        boost::iequals(TAGNAME(childs.item(j)), "script")) {
				LOG(ERROR) << "scxml element has unspecified child " << TAGNAME(childs.item(j)) << std::endl;
			}
		}
	}

	Arabica::XPath::NodeSet<std::string> stateElems = _xpath.evaluate(_nsPrefix + "state", _doc).asNodeSet();
	for (unsigned int i = 0; i < stateElems.size(); i++) {
		NodeList<std::string> childs = stateElems[i].getChildNodes();
		for (unsigned int j = 0; j < childs.getLength(); j++) {
			if (childs.item(j).getNodeType() != Node_base::ELEMENT_NODE)
				continue;
			if (boost::iequals(TAGNAME(childs.item(j)), "onentry") ||
			        boost::iequals(TAGNAME(childs.item(j)), "onexit") ||
			        boost::iequals(TAGNAME(childs.item(j)), "transition") ||
			        boost::iequals(TAGNAME(childs.item(j)), "initial") ||
			        boost::iequals(TAGNAME(childs.item(j)), "state") ||
			        boost::iequals(TAGNAME(childs.item(j)), "parallel") ||
			        boost::iequals(TAGNAME(childs.item(j)), "final") ||
			        boost::iequals(TAGNAME(childs.item(j)), "history") ||
			        boost::iequals(TAGNAME(childs.item(j)), "datamodel") ||
			        boost::iequals(TAGNAME(childs.item(j)), "invoke")) {
				LOG(ERROR) << "state element has unspecified child " << TAGNAME(childs.item(j)) << std::endl;
			}
		}
	}

	Arabica::XPath::NodeSet<std::string> parallelElems = _xpath.evaluate(_nsPrefix + "parallel", _doc).asNodeSet();
	for (unsigned int i = 0; i < parallelElems.size(); i++) {
		NodeList<std::string> childs = parallelElems[i].getChildNodes();
		for (unsigned int j = 0; j < childs.getLength(); j++) {
			if (childs.item(j).getNodeType() != Node_base::ELEMENT_NODE)
				continue;
			if (boost::iequals(TAGNAME(childs.item(j)), "onentry") ||
			        boost::iequals(TAGNAME(childs.item(j)), "onexit") ||
			        boost::iequals(TAGNAME(childs.item(j)), "transition") ||
			        boost::iequals(TAGNAME(childs.item(j)), "state") ||
			        boost::iequals(TAGNAME(childs.item(j)), "parallel") ||
			        boost::iequals(TAGNAME(childs.item(j)), "history") ||
			        boost::iequals(TAGNAME(childs.item(j)), "datamodel") ||
			        boost::iequals(TAGNAME(childs.item(j)), "invoke")) {
				LOG(ERROR) << "parallel element has unspecified child " << TAGNAME(childs.item(j)) << std::endl;
			}
		}
	}

	Arabica::XPath::NodeSet<std::string> transitionElems = _xpath.evaluate(_nsPrefix + "transition", _doc).asNodeSet();
	for (unsigned int i = 0; i < transitionElems.size(); i++) {
		if (HAS_ATTR(transitionElems[i], "cond") &&
		        !HAS_ATTR(transitionElems[i], "event")) {
			LOG(ERROR) << "transition element with cond attribute but without event attribute not allowed" << std::endl;
		}
		NodeList<std::string> childs = scxmlElems[i].getChildNodes();
		for (unsigned int j = 0; j < childs.getLength(); j++) {
			if (childs.item(j).getNodeType() != Node_base::ELEMENT_NODE)
				continue;
		}
	}

	Arabica::XPath::NodeSet<std::string> initialElems = _xpath.evaluate(_nsPrefix + "initial", _doc).asNodeSet();
	for (unsigned int i = 0; i < initialElems.size(); i++) {
		NodeList<std::string> childs = initialElems[i].getChildNodes();
		for (unsigned int j = 0; j < childs.getLength(); j++) {
			if (childs.item(j).getNodeType() != Node_base::ELEMENT_NODE)
				continue;
			if (boost::iequals(TAGNAME(childs.item(j)), "transition")) {
				LOG(ERROR) << "initial element has unspecified child " << TAGNAME(childs.item(j)) << std::endl;
			}
		}
	}

	Arabica::XPath::NodeSet<std::string> finalElems = _xpath.evaluate(_nsPrefix + "final", _doc).asNodeSet();
	for (unsigned int i = 0; i < finalElems.size(); i++) {
		NodeList<std::string> childs = finalElems[i].getChildNodes();
		for (unsigned int j = 0; j < childs.getLength(); j++) {
			if (childs.item(j).getNodeType() != Node_base::ELEMENT_NODE)
				continue;
			if (!boost::iequals(TAGNAME(childs.item(j)), "onentry") ||
			        !boost::iequals(TAGNAME(childs.item(j)), "onexit") ||
			        !boost::iequals(TAGNAME(childs.item(j)), "donedata")) {
				LOG(ERROR) << "parallel element has unspecified child " << TAGNAME(childs.item(j)) << std::endl;
			}
		}
	}

	Arabica::XPath::NodeSet<std::string> historyElems = _xpath.evaluate(_nsPrefix + "history", _doc).asNodeSet();
	for (unsigned int i = 0; i < historyElems.size(); i++) {
		NodeList<std::string> childs = historyElems[i].getChildNodes();
		for (unsigned int j = 0; j < childs.getLength(); j++) {
			if (childs.item(j).getNodeType() != Node_base::ELEMENT_NODE)
				continue;
			if (boost::iequals(TAGNAME(childs.item(j)), "transition")) {
				LOG(ERROR) << "history element has unspecified child " << TAGNAME(childs.item(j)) << std::endl;
			}
		}
	}

	Arabica::XPath::NodeSet<std::string> datamodelElems = _xpath.evaluate(_nsPrefix + "datamodel", _doc).asNodeSet();
	for (unsigned int i = 0; i < datamodelElems.size(); i++) {
		NodeList<std::string> childs = datamodelElems[i].getChildNodes();
		for (unsigned int j = 0; j < childs.getLength(); j++) {
			if (childs.item(j).getNodeType() != Node_base::ELEMENT_NODE)
				continue;
			if (!boost::iequals(TAGNAME(childs.item(j)), "data")) {
				LOG(ERROR) << "datamodel element has unspecified child " << TAGNAME(childs.item(j)) << std::endl;
			}
		}
	}

	Arabica::XPath::NodeSet<std::string> dataElems = _xpath.evaluate(_nsPrefix + "data", _doc).asNodeSet();
	for (unsigned int i = 0; i < dataElems.size(); i++) {
		if (!HAS_ATTR(dataElems[i], "id"))
			LOG(ERROR) << "data element has no id attribute" << std::endl;
	}

	return validationErrors;
}

void Interpreter::dump() {
	if (!_doc)
		return;
	dump(_doc);
}

void Interpreter::dump(const Arabica::DOM::Node<std::string>& node, int lvl) {
	if (!node)
		return;

	std::string indent = "";
	for (unsigned int i = 0; i < lvl; i++)
		indent += "   ";

	std::cout << indent;
	switch(node.getNodeType()) {
	case Arabica::DOM::Node_base::ELEMENT_NODE: {
		std::cout << "ELEMENT_NODE: ";
		Arabica::DOM::Element<std::string> elem = (Arabica::DOM::Element<std::string>)node;
		break;
	}
	case Arabica::DOM::Node_base::ATTRIBUTE_NODE:
		std::cout << "ATTRIBUTE_NODE: ";
		break;
	case Arabica::DOM::Node_base::TEXT_NODE:
		std::cout << "TEXT_NODE: ";
		break;
	case Arabica::DOM::Node_base::CDATA_SECTION_NODE:
		std::cout << "CDATA_SECTION_NODE: ";
		break;
	case Arabica::DOM::Node_base::ENTITY_REFERENCE_NODE:
		std::cout << "ENTITY_REFERENCE_NODE: ";
		break;
	case Arabica::DOM::Node_base::ENTITY_NODE:
		std::cout << "ENTITY_NODE: ";
		break;
	case Arabica::DOM::Node_base::PROCESSING_INSTRUCTION_NODE:
		std::cout << "PROCESSING_INSTRUCTION_NODE: ";
		break;
	case Arabica::DOM::Node_base::COMMENT_NODE:
		std::cout << "COMMENT_NODE: ";
		break;
	case Arabica::DOM::Node_base::DOCUMENT_NODE:
		std::cout << "DOCUMENT_NODE: ";
		break;
	case Arabica::DOM::Node_base::DOCUMENT_TYPE_NODE:
		std::cout << "DOCUMENT_TYPE_NODE: ";
		break;
	case Arabica::DOM::Node_base::DOCUMENT_FRAGMENT_NODE:
		std::cout << "DOCUMENT_FRAGMENT_NODE: ";
		break;
	case Arabica::DOM::Node_base::NOTATION_NODE:
		std::cout << "NOTATION_NODE: ";
		break;
	case Arabica::DOM::Node_base::MAX_TYPE:
		std::cout << "MAX_TYPE: ";
		break;
	}
	std::cout << node.getNamespaceURI() << " " << node.getNodeName() << std::endl;

	if (node.getNodeValue().length() > 0 && node.getNodeValue().find_first_not_of(" \t\n") != std::string::npos)
		std::cout << indent << "Value: '" << node.getNodeValue() << "'" << std::endl;


	if (node.hasAttributes()) {
		Arabica::DOM::NamedNodeMap<std::string> attrs = node.getAttributes();
		for (unsigned int i = 0; i < attrs.getLength(); i++) {
			std::cout << indent << "   " << attrs.item(i).getLocalName() << " = " << attrs.item(i).getNodeValue() << " (" << std::endl;
			std::cout << indent << "     namespace: " << attrs.item(i).getNamespaceURI() << std::endl;
			std::cout << indent << "     nodeName: " << attrs.item(i).getNodeName() << std::endl;
			std::cout << indent << "     prefix: " << attrs.item(i).getPrefix() << std::endl;
			std::cout << indent << "   )" << std::endl;
		}
	}

	if (node.hasChildNodes()) {
		Arabica::DOM::NodeList<std::string> childs = node.getChildNodes();
		for (unsigned int i = 0; i < childs.getLength(); i++) {
			dump(childs.item(i), lvl+1);
		}
	}
}

}