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

#include "uscxml/interpreter/InterpreterDraft6.h"

#define VERBOSE 0

namespace uscxml {

using namespace Arabica::XPath;
using namespace Arabica::DOM;

boost::uuids::random_generator Interpreter::uuidGen;
const std::string Interpreter::getUUID() {
	return boost::lexical_cast<std::string>(uuidGen());
}

Interpreter::Interpreter() {
	_lastRunOnMainThread = 0;
	_nsURL = "*";
	_thread = NULL;
	_sendQueue = NULL;
	_parentQueue = NULL;
	_running = false;
	_done = true;
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
	Interpreter* interpreter = new InterpreterDraft6();
	interpreter->_document = domFactory.createDocument("http://www.w3.org/2005/07/scxml", "scxml", 0);
	interpreter->_document.appendChild(node);
	return interpreter;
}

Interpreter* Interpreter::fromXML(const std::string& xml) {
	std::stringstream* ss = new std::stringstream();
	(*ss) << xml;
	// we need an auto_ptr for arabica to assume ownership
	std::auto_ptr<std::istream> ssPtr(ss);
	Arabica::SAX::InputSource<std::string> inputSource;
	inputSource.setByteStream(ssPtr);
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

	Interpreter* interpreter = NULL;

	if (boost::iequals(absUrl.scheme(), "file")) {
		Arabica::SAX::InputSource<std::string> inputSource;
		inputSource.setSystemId(absUrl.path());
		interpreter = fromInputSource(inputSource);
	} else if (boost::iequals(absUrl.scheme(), "http")) {
		// handle http per arabica
		Arabica::SAX::InputSource<std::string> inputSource;
		inputSource.setSystemId(absUrl.asString());
		interpreter = fromInputSource(inputSource);
	} else {
		// use curl for everything else
		std::stringstream ss;
		ss << absUrl;
		if (absUrl.downloadFailed()) {
			LOG(ERROR) << "Downloading SCXML document from " << absUrl << " failed";
			return NULL;
		}
		interpreter = fromXML(ss.str());
	}

	// try to establish URI root for relative src attributes in document
	if (interpreter)
		interpreter->_baseURI = toBaseURI(absUrl);
	return interpreter;
}

Interpreter* Interpreter::fromInputSource(Arabica::SAX::InputSource<std::string>& source) {
	Interpreter* interpreter = new InterpreterDraft6();
	
	SCXMLParser* parser = new SCXMLParser(interpreter);
	if(!parser->parse(source) || !parser->getDocument().hasChildNodes()) {
		if(parser->_errorHandler.errorsReported()) {
			LOG(ERROR) << "could not parse input:";
			LOG(ERROR) << parser->_errorHandler.errors() << std::endl;
		} else {
			Arabica::SAX::InputSourceResolver resolver(source, Arabica::default_string_adaptor<std::string>());
			if (!resolver.resolve()) {
				LOG(ERROR) << source.getSystemId() << ": no such file";
			}
		}
		delete parser;
		delete interpreter;
		return NULL;
	} else {
		interpreter->_document = parser->getDocument();
	}
	//	interpreter->init();
	delete parser;
	return interpreter;
}

SCXMLParser::SCXMLParser(Interpreter* interpreter) : _interpreter(interpreter) {
	Arabica::SAX::CatchErrorHandler<std::string> errorHandler;
	setErrorHandler(errorHandler);
}

void SCXMLParser::startPrefixMapping(const std::string& prefix, const std::string& uri) {
#if 0
	std::cout << "starting prefix mapping " << prefix << ": " << uri << std::endl;
#endif
	if (boost::iequals(uri, "http://www.w3.org/2005/07/scxml")) {
		_interpreter->_nsURL = uri;
		if (prefix.size() == 0) {
			LOG(INFO) << "Mapped default namespace to 'scxml:'";
			_interpreter->_xpathPrefix = "scxml:";
			_interpreter->_nsContext.addNamespaceDeclaration(uri, "scxml");
			_interpreter->_nsToPrefix[uri] = "scxml";
		} else {
			_interpreter->_xpathPrefix = prefix + ":";
			_interpreter->_xmlNSPrefix = _interpreter->_xpathPrefix;
			_interpreter->_nsContext.addNamespaceDeclaration(uri, prefix);
			_interpreter->_nsToPrefix[uri] = prefix;
		}
	} else {
		_interpreter->_nsContext.addNamespaceDeclaration(uri, prefix);
		_interpreter->_nsToPrefix[uri] = prefix;
	}
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
				_httpServlet = new InterpreterServlet(this);
			
			_sendQueue = new DelayedEventQueue();
			_sendQueue->start();
			
		} else {
			LOG(ERROR) << "Cannot find SCXML element" << std::endl;
		}
	}
	_isInitialized = true;
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
//		  LOG(ERROR) << "Pushing into parent queue: " << INSTANCE->_parentQueue << std::endl;
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


bool Interpreter::hasConditionMatch(const Arabica::DOM::Node<std::string>& conditional) {

	if (HAS_ATTR(conditional, "cond") && ATTR(conditional, "cond").length() > 0) {
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
				if (boost::iequals(TAGNAME(childs.item(i)), _xmlNSPrefix + "elseif") ||
						boost::iequals(TAGNAME(childs.item(i)), _xmlNSPrefix + "else")) {
					if (blockIsTrue) {
						// last block was true, break here
						break;
					} else {
						// is this block the one to execute?
						blockIsTrue = hasConditionMatch(childs.item(i));
					}
				} else {
					if (blockIsTrue) {
						executeContent(childs.item(i));
					}
				}
			}
		}
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

Arabica::XPath::NodeSet<std::string> Interpreter::getStates(const std::vector<std::string>& stateIds) {
	Arabica::XPath::NodeSet<std::string> states;
	std::vector<std::string>::const_iterator tokenIter = stateIds.begin();
	while(tokenIter != stateIds.end()) {
		states.push_back(getState(*tokenIter));
		tokenIter++;
	}
	return states;
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
Arabica::XPath::NodeSet<std::string> Interpreter::getInitialStates(Arabica::DOM::Node<std::string> state) {
	if (!state) {
		state = _document.getFirstChild();
		while(state && !isState(state))
			state = state.getNextSibling();
	}

#if VERBOSE
	std::cout << "Getting initial state of " << TAGNAME(state) << " " << ATTR(state, "id") << std::endl;
#endif

	assert(isCompound(state) || isParallel(state));

	Arabica::XPath::NodeSet<std::string> initialStates;
	
	// initial attribute at element
	Arabica::DOM::Element<std::string> stateElem = (Arabica::DOM::Element<std::string>)state;
	if (stateElem.hasAttribute("initial")) {
		return getStates(tokenizeIdRefs(stateElem.getAttribute("initial")));
	}

	Arabica::XPath::NodeSet<std::string> initStates;
	
	// initial element as child - but not the implicit generated one
	NodeSet<std::string> initElems = filterChildElements(_xmlNSPrefix + "initial", state);
	if(initElems.size() == 1 && !boost::iequals(ATTR(initElems[0], "generated"), "true")) {
		initStates.push_back(initialStates[0]);
		return initStates;
	}

	// first child state
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

	if (isMember(state, getInitialStates(parent)))
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
