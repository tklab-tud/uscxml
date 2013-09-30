#include "uscxml/Common.h"
#include "uscxml/Interpreter.h"
#include "uscxml/URL.h"
#include "uscxml/UUID.h"
#include "uscxml/NameSpacingParser.h"
#include "uscxml/debug/SCXMLDotWriter.h"

#include "uscxml/plugins/invoker/http/HTTPServletInvoker.h"

#include <DOM/Simple/DOMImplementation.hpp>
#include <SAX/helpers/InputSourceResolver.hpp>

#include <boost/lexical_cast.hpp>
#include <boost/tokenizer.hpp>

#include <glog/logging.h>

#include <assert.h>
#include <algorithm>

#include "uscxml/interpreter/InterpreterDraft6.h"

#define VERBOSE 0

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

namespace uscxml {

using namespace Arabica::XPath;
using namespace Arabica::DOM;

std::map<std::string, boost::weak_ptr<InterpreterImpl> > Interpreter::_instances;
tthread::recursive_mutex Interpreter::_instanceMutex;

InterpreterImpl::InterpreterImpl() {
	_lastRunOnMainThread = 0;
	_nsURL = "*";
	_thread = NULL;
	_sendQueue = NULL;
	_parentQueue = NULL;
	_running = false;
	_done = true;
	_isInitialized = false;
	_httpServlet = NULL;
	_factory = NULL;
	_capabilities = CAN_BASIC_HTTP | CAN_GENERIC_HTTP;

#ifdef _WIN32
	WSADATA wsaData;
	WSAStartup(MAKEWORD(2, 2), &wsaData);
#endif
}

Interpreter Interpreter::fromDOM(const Arabica::DOM::Document<std::string>& dom) {
	tthread::lock_guard<tthread::recursive_mutex> lock(_instanceMutex);
	boost::shared_ptr<InterpreterDraft6> interpreterImpl = boost::shared_ptr<InterpreterDraft6>(new InterpreterDraft6);
	Interpreter interpreter(interpreterImpl);
	interpreterImpl->_document = dom;
	interpreterImpl->init();
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
			LOG(ERROR) << "Given URL is not absolute or does not have file schema";
			return Interpreter();
		}
	}

	Interpreter interpreter;

	if (boost::iequals(absUrl.scheme(), "file")) {
		Arabica::SAX::InputSource<std::string> inputSource;
		inputSource.setSystemId(absUrl.asString());
		interpreter = fromInputSource(inputSource);
#if 0
	} else if (boost::iequals(absUrl.scheme(), "http")) {
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
			LOG(ERROR) << "Downloading SCXML document from " << absUrl << " failed";
			return interpreter;
		}
		interpreter = fromXML(ss.str());
	}

	// try to establish URI root for relative src attributes in document
	if (interpreter) {
		interpreter._impl->_baseURI = URL::asBaseURL(absUrl);
	} else {
		LOG(ERROR) << "Cannot create interpreter from URI '" << absUrl.asString() << "'";
	}
	return interpreter;
}

Interpreter Interpreter::fromInputSource(Arabica::SAX::InputSource<std::string>& source) {
	tthread::lock_guard<tthread::recursive_mutex> lock(_instanceMutex);

	std::map<std::string, boost::weak_ptr<InterpreterImpl> >::iterator instIter = _instances.begin();
	while(instIter != _instances.end()) {
		if (!instIter->second.lock()) {
			_instances.erase(instIter++);
		} else {
			instIter++;
		}
	}

	boost::shared_ptr<InterpreterDraft6> interpreterImpl = boost::shared_ptr<InterpreterDraft6>(new InterpreterDraft6);
	Interpreter interpreter;
	NameSpacingParser parser;
	if (parser.parse(source) && parser.getDocument() && parser.getDocument().hasChildNodes()) {
		interpreterImpl->setNameSpaceInfo(parser.nameSpace);
		interpreterImpl->_document = parser.getDocument();
		interpreterImpl->init();
		interpreter = Interpreter(interpreterImpl);
		_instances[interpreterImpl->getSessionId()] = interpreterImpl;
	} else {
		if (parser.errorsReported()) {
			LOG(ERROR) << parser.errors();
		}
	}
	//	interpreter->init();
	return interpreter;
}

void InterpreterImpl::setNameSpaceInfo(const std::map<std::string, std::string> namespaceInfo) {
	_nameSpaceInfo = namespaceInfo;
	std::map<std::string, std::string>::const_iterator nsIter = namespaceInfo.begin();
	while(nsIter != namespaceInfo.end()) {
		std::string uri = nsIter->first;
		std::string prefix = nsIter->second;
		if (boost::iequals(uri, "http://www.w3.org/2005/07/scxml")) {
			_nsURL = uri;
			if (prefix.size() == 0) {
//				LOG(INFO) << "Mapped default namespace to 'scxml:'";
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
		nsIter++;
	}

}

void InterpreterImpl::setName(const std::string& name) {
	if (!_running) {
		_name = name;
	} else {
		LOG(ERROR) << "Cannot change name of running interpreter";
	}
}

InterpreterImpl::~InterpreterImpl() {
	_running = false;
//	tthread::lock_guard<tthread::recursive_mutex> lock(_mutex);
	if (_thread) {
		// unblock event queue
		Event event;
		event.name = "unblock.and.die";
		receive(event);
		_thread->join();
		delete(_thread);
	}
	if (_sendQueue)
		delete _sendQueue;

//	if (_httpServlet)
//		delete _httpServlet;
}

void InterpreterImpl::start() {
	_done = false;
	_thread = new tthread::thread(InterpreterImpl::run, this);
}

void InterpreterImpl::run(void* instance) {
	((InterpreterImpl*)instance)->interpret();
}

bool InterpreterImpl::runOnMainThread(int fps, bool blocking) {
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

void InterpreterImpl::init() {
	if (_document) {
		NodeList<std::string> scxmls = _document.getElementsByTagNameNS(_nsURL, "scxml");
		if (scxmls.getLength() > 0) {
			_scxml = (Arabica::DOM::Element<std::string>)scxmls.item(0);

			// setup xpath and check that it works
			_xpath.setNamespaceContext(_nsContext);

			if (_name.length() == 0)
				_name = (HAS_ATTR(_scxml, "name") ? ATTR(_scxml, "name") : UUID::getUUID());

			normalize(_scxml);

			// setup event queue for delayed send
			_sendQueue = new DelayedEventQueue();
			_sendQueue->start();

			if (_factory == NULL)
				_factory = Factory::getInstance();

		} else {
			LOG(ERROR) << "Cannot find SCXML element" << std::endl;
			_done = true;
			return;
		}
	} else {
		LOG(ERROR) << "Interpreter has no DOM at all!" << std::endl;
		_done = true;
	}

	if (_sessionId.length() == 0)
		_sessionId = UUID::getUUID();

	_isInitialized = true;
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
			LOG(ERROR) << "Syntax error when initializing data from parameters:" << std::endl << e << std::endl;
			receiveInternal(e);
		}
		return;
	}
	if (_invokeReq.namelist.find(ATTR(data, "id")) != _invokeReq.namelist.end()) {
		try {
			_dataModel.init(ATTR(data, "id"), _invokeReq.namelist.find(ATTR(data, "id"))->second);
		} catch (Event e) {
			LOG(ERROR) << "Syntax error when initializing data from namelist:" << std::endl << e << std::endl;
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
		LOG(ERROR) << "Syntax error when initializing data:" << std::endl << e << std::endl;
		receiveInternal(e);
	}
}

void InterpreterImpl::normalize(Arabica::DOM::Element<std::string>& scxml) {
	// TODO: Resolve XML includes

	// make sure every state has an id and set isFirstEntry to true
	Arabica::XPath::NodeSet<std::string> states = _xpath.evaluate("//" + _xpathPrefix + "state", _scxml).asNodeSet();
	for (int i = 0; i < states.size(); i++) {
		Arabica::DOM::Element<std::string> stateElem = Arabica::DOM::Element<std::string>(states[i]);
		stateElem.setAttribute("isFirstEntry", "true");
		if (!stateElem.hasAttribute("id")) {
			stateElem.setAttribute("id", UUID::getUUID());
		}
	}

	// make sure every invoke has an idlocation or id
	Arabica::XPath::NodeSet<std::string> invokes = _xpath.evaluate("//" + _xpathPrefix + "invoke", _scxml).asNodeSet();
	for (int i = 0; i < invokes.size(); i++) {
		Arabica::DOM::Element<std::string> invokeElem = Arabica::DOM::Element<std::string>(invokes[i]);
		if (!invokeElem.hasAttribute("id") && !invokeElem.hasAttribute("idlocation")) {
			invokeElem.setAttribute("id", UUID::getUUID());
		}
//    // make sure every finalize element contained has the invoke id as an attribute
//    Arabica::XPath::NodeSet<std::string> finalizes = _xpath.evaluate("" + _xpathPrefix + "finalize", invokeElem).asNodeSet();
//    for (int j = 0; j < finalizes.size(); j++) {
//      Arabica::DOM::Element<std::string> finalizeElem = Arabica::DOM::Element<std::string>(finalizes[j]);
//      finalizeElem.setAttribute("invokeid", invokeElem.getAttribute("id"));
//    }
	}

	Arabica::XPath::NodeSet<std::string> finals = _xpath.evaluate("//" + _xpathPrefix + "final", _scxml).asNodeSet();
	for (int i = 0; i < finals.size(); i++) {
		Arabica::DOM::Element<std::string> finalElem = Arabica::DOM::Element<std::string>(finals[i]);
		finalElem.setAttribute("isFirstEntry", "true");
		if (!finalElem.hasAttribute("id")) {
			finalElem.setAttribute("id", UUID::getUUID());
		}
	}

	Arabica::XPath::NodeSet<std::string> histories = _xpath.evaluate("//" + _xpathPrefix + "history", _scxml).asNodeSet();
	for (int i = 0; i < histories.size(); i++) {
		Arabica::DOM::Element<std::string> historyElem = Arabica::DOM::Element<std::string>(histories[i]);
		if (!historyElem.hasAttribute("id")) {
			historyElem.setAttribute("id", UUID::getUUID());
		}
	}

	if (!scxml.hasAttribute("id")) {
		scxml.setAttribute("id", UUID::getUUID());
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

void InterpreterImpl::receiveInternal(const Event& event) {
//	std::cout << _name << " receiveInternal: " << event.name << std::endl;
	_internalQueue.push_back(event);
//	_condVar.notify_all();
}

void InterpreterImpl::receive(const Event& event, bool toFront)   {
//	std::cout << _name << " receive: " << event.name << std::endl;
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

	Arabica::XPath::NodeSet<std::string> doneDatas = filterChildElements(_xmlNSPrefix + "donedata", stateElem);
	if (doneDatas.size() > 0) {
		// only process first donedata element
		Arabica::DOM::Node<std::string> doneData = doneDatas[0];
		processParamChilds(doneData, event.params);
		Arabica::XPath::NodeSet<std::string> contents = filterChildElements(_xmlNSPrefix + "content", doneDatas[0]);
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

//			parser.setFeature(Arabica::SAX::FeatureNames<std::string>().external_general, true);

			if (parser.parse(inputSource) && parser.getDocument()) {
				Document<std::string> doc = parser.getDocument();
				dom = doc.getDocumentElement();
#if 0
				Node<std::string> content = doc.getDocumentElement();
				assert(content.getNodeType() == Node_base::ELEMENT_NODE);
				Node<std::string> container = doc.createElement("container");
				dom.replaceChild(container, content);
				container.appendChild(content);
//				std::cout << dom << std::endl;
#endif
				return;
			} else {
				if (parser.errorsReported()) {
					LOG(ERROR) << parser.errors();
				}
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
	} else {
		LOG(ERROR) << LOCALNAME(element) << " has neither text nor element children.";
	}
}

void InterpreterImpl::processParamChilds(const Arabica::DOM::Node<std::string>& element, std::multimap<std::string, Data>& params) {
	NodeSet<std::string> paramElems = filterChildElements(_xmlNSPrefix + "param", element);
	try {
		for (int i = 0; i < paramElems.size(); i++) {
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
		}
	} catch(Event e) {
		LOG(ERROR) << "Syntax error while processing params:" << std::endl << e << std::endl;
		// test 343
		std::multimap<std::string, Data>::iterator paramIter = params.begin();
		while(paramIter != params.end()) {
			params.erase(paramIter++);
		}
		e.name = "error.execution";
		receiveInternal(e);
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
		}
	} catch (Event e) {
		LOG(ERROR) << "Syntax error in send element typeexpr:" << std::endl << e << std::endl;
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

			NumAttr delayAttr(delay);
			if (boost::iequals(delayAttr.unit, "ms")) {
				sendReq.delayMs = strTo<uint32_t>(delayAttr.value);
			} else if (boost::iequals(delayAttr.unit, "s")) {
				sendReq.delayMs = strTo<uint32_t>(delayAttr.value);
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
					Data namelistValue = _dataModel.getStringAsData(names[i]);
					sendReq.namelist[names[i]] = namelistValue;
					sendReq.data.compound[names[i]] = namelistValue;
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
		processParamChilds(element, sendReq.params);
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
			std::string expr;
			processContentElement(contents[0], sendReq.dom, sendReq.content, expr);
			if (expr.length() > 0 && _dataModel) {
				try {
					sendReq.content =_dataModel.evalAsString(expr);
				} catch (Event e) {
					e.name = "error.execution";
					receiveInternal(e);
				}
			} else if (sendReq.content.length() > 0) {
				sendReq.data = Data::fromJSON(sendReq.content);
			}
		}
	} catch (Event e) {
		LOG(ERROR) << "Syntax error in send element content:" << std::endl << e << std::endl;
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
		processParamChilds(element, invokeReq.params);

		// content
		try {
			NodeSet<std::string> contents = filterChildElements(_xmlNSPrefix + "content", element);
			if (contents.size() > 1)
				LOG(ERROR) << "Only a single content element is allowed for send elements - using first one";
			if (contents.size() > 0) {
				std::string expr;
				processContentElement(contents[0], invokeReq.dom, invokeReq.content, expr);
				if (expr.length() > 0 && _dataModel) {
					try {
						invokeReq.content =_dataModel.evalAsString(expr);
					} catch (Event e) {
						e.name = "error.execution";
						receiveInternal(e);
					}
				} else if (invokeReq.content.length() > 0) {
					invokeReq.data = Data::fromJSON(invokeReq.content);
				}

			}
		} catch (Event e) {
			LOG(ERROR) << "Syntax error in send element content:" << std::endl << e << std::endl;
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
				_invokers[invokeReq.invokeid] = invoker;
				LOG(INFO) << "Added invoker " << invokeReq.type << " at " << invokeReq.invokeid;
				try {
					invoker.invoke(invokeReq);
				} catch(...) {
					LOG(ERROR) << "Exception caught while sending invoke requst to invoker " << invokeReq.invokeid;
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
		LOG(ERROR) << "Syntax error in invoke element:" << std::endl << e << std::endl;
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
		_invokers.erase(invokeId);
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
	if (boost::iequals(transitionEvent, event))
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
		if (boost::iequals(eventDesc, event))
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
		if (!_dataModel) {
			LOG(ERROR) << "Cannot check a condition without a datamodel";
			return false;
		}
		try {
			return _dataModel.evalAsBool(ATTR(conditional, "cond"));
		} catch (Event e) {
			LOG(ERROR) << "Syntax error in cond attribute of " << TAGNAME(conditional) << " element:" << std::endl << e << std::endl;
			e.name = "error.execution";
			receiveInternal(e);
			return false;
		}
	}
	return true; // no condition is always true
}


void InterpreterImpl::executeContent(const NodeList<std::string>& content, bool rethrow) {
	for (unsigned int i = 0; i < content.getLength(); i++) {
		if (content.item(i).getNodeType() != Node_base::ELEMENT_NODE)
			continue;
		executeContent(content.item(i), rethrow);
	}
}

void InterpreterImpl::executeContent(const NodeSet<std::string>& content, bool rethrow) {
	for (unsigned int i = 0; i < content.size(); i++) {
		if (content[i].getNodeType() != Node_base::ELEMENT_NODE)
			continue;
		executeContent(content[i], rethrow);
	}
}

void InterpreterImpl::executeContent(const Arabica::DOM::Node<std::string>& content, bool rethrow) {
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
			executeContent(executable.item(i), rethrow);
		}
	} else if (boost::iequals(TAGNAME(content), _xmlNSPrefix + "raise")) {
		// --- RAISE --------------------------
		if (HAS_ATTR(content, "event")) {
			receiveInternal(Event(ATTR(content, "event")));
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
						executeContent(childs.item(i), rethrow);
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
				uint32_t iterations = 0;
				try {
					iterations = _dataModel.getLength(array);
				}
				CATCH_AND_DISTRIBUTE("Syntax error in array attribute of foreach element:")
				try {
					_dataModel.pushContext(); // copy old and enter new context
//					if (!_dataModel.isDeclared(item)) {
//						_dataModel.init(item, Data());
//					}
					for (uint32_t iteration = 0; iteration < iterations; iteration++) {
						_dataModel.setForeach(item, array, index, iteration);
						if (content.hasChildNodes())
							// execute content and have exception rethrown to break foreach
							executeContent(content.getChildNodes(), true);
					}
					_dataModel.popContext(); // leave stacked context
				}
				CATCH_AND_DISTRIBUTE("Syntax error in foreach element:")
			} else {
				LOG(ERROR) << "Expected array and item attributes with foreach element!" << std::endl;
			}
		}
	} else if (boost::iequals(TAGNAME(content), _xmlNSPrefix + "log")) {
		// --- LOG --------------------------
		Arabica::DOM::Element<std::string> logElem = (Arabica::DOM::Element<std::string>)content;
		if (logElem.hasAttribute("label"))
			std::cout << logElem.getAttribute("label") << ": ";
		if (logElem.hasAttribute("expr")) {
			try {
				std::cout << _dataModel.evalAsString(logElem.getAttribute("expr")) << std::endl;
			}
			CATCH_AND_DISTRIBUTE("Syntax error in expr attribute of log element:")
		} else {
			if (logElem.hasAttribute("label"))
				std::cout << std::endl;
		}
	} else if (boost::iequals(TAGNAME(content), _xmlNSPrefix + "assign")) {
		// --- ASSIGN --------------------------
		if (_dataModel && HAS_ATTR(content, "location")) {
			try {
//				if (!_dataModel.isDeclared(ATTR(content, "location"))) {
//					// test 286, 331
//					LOG(ERROR) << "Assigning to undeclared location '" << ATTR(content, "location") << "' not allowed." << std::endl;
//					throw Event("error.execution", Event::PLATFORM);
//				} else {
					Node<std::string> dom;
					std::string text;
					processDOMorText(content, dom, text);
					_dataModel.assign(Element<std::string>(content), dom, text);
//				}
			}
			CATCH_AND_DISTRIBUTE("Syntax error in attributes of assign element:")
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
				if (!scriptUrl.toAbsolute(_baseURI)) {
					LOG(ERROR) << "script element has relative URI " << ATTR(content, "src") <<  " with no base URI set for interpreter";
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
						CATCH_AND_DISTRIBUTE("Syntax error while executing script element")
					}
				}
			}
		}
	} else if (boost::iequals(TAGNAME(content), _xmlNSPrefix + "send")) {
		// --- SEND --------------------------
		try {
			send(content);
		}
		CATCH_AND_DISTRIBUTE("Error while sending content")
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

		}
		CATCH_AND_DISTRIBUTE("Syntax error while executing cancel element")
	} else if (boost::iequals(TAGNAME(content), _xmlNSPrefix + "invoke")) {
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
	if (boost::iequals(TAGNAME(parentElem), _xmlNSPrefix + "scxml"))
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
		        boost::iequals(TAGNAME(parent), tagName)) {
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

Arabica::XPath::NodeSet<std::string> InterpreterImpl::getStates(const std::vector<std::string>& stateIds) {
	Arabica::XPath::NodeSet<std::string> states;
	std::vector<std::string>::const_iterator tokenIter = stateIds.begin();
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
	NodeSet<std::string> target = _xpath.evaluate("//" + _xpathPrefix + "state[@id='" + stateId + "']", _scxml).asNodeSet();
	if (target.size() > 0)
		goto FOUND;

	// now parallel states
	target = _xpath.evaluate("//" + _xpathPrefix + "parallel[@id='" + stateId + "']", _scxml).asNodeSet();
	if (target.size() > 0)
		goto FOUND;

	// now final states
	target = _xpath.evaluate("//" + _xpathPrefix + "final[@id='" + stateId + "']", _scxml).asNodeSet();
	if (target.size() > 0)
		goto FOUND;

	// now history states
	target = _xpath.evaluate("//" + _xpathPrefix + "history[@id='" + stateId + "']", _scxml).asNodeSet();
	if (target.size() > 0)
		goto FOUND;

	LOG(ERROR) << "No state with id " << stateId << " found!";

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

Arabica::DOM::Node<std::string> InterpreterImpl::getSourceState(const Arabica::DOM::Node<std::string>& transition) {
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
	NodeSet<std::string> initElems = filterChildElements(_xmlNSPrefix + "initial", state);
	if(initElems.size() == 1 && !boost::iequals(ATTR(initElems[0], "generated"), "true")) {
		NodeSet<std::string> initTrans = filterChildElements(_xmlNSPrefix + "transition", initElems[0]);
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

	std::vector<std::string> targetIds = InterpreterImpl::tokenizeIdRefs(ATTR(transition, "target"));
	for (int i = 0; i < targetIds.size(); i++) {
		Arabica::DOM::Node<std::string> state = getState(targetIds[i]);
		assert(HAS_ATTR(state, "id"));
		targetStates.push_back(state);
	}
	return targetStates;
}

std::vector<std::string> InterpreterImpl::tokenizeIdRefs(const std::string& idRefs) {
	std::vector<std::string> ids;

	if (idRefs.length() > 0) {
		std::istringstream iss(idRefs);

		std::copy(std::istream_iterator<std::string>(iss),
		          std::istream_iterator<std::string>(),
		          std::back_inserter<std::vector<std::string> >(ids));
	}

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


NodeSet<std::string> InterpreterImpl::filterChildElements(const std::string& tagName, const NodeSet<std::string>& nodeSet) {
	NodeSet<std::string> filteredChildElems;
	for (unsigned int i = 0; i < nodeSet.size(); i++) {
		filteredChildElems.push_back(filterChildElements(tagName, nodeSet[i]));
	}
	return filteredChildElems;
}

NodeSet<std::string> InterpreterImpl::filterChildElements(const std::string& tagName, const Node<std::string>& node) {
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

NodeSet<std::string> InterpreterImpl::getProperAncestors(const Arabica::DOM::Node<std::string>& s1,
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

bool InterpreterImpl::isFinal(const Arabica::DOM::Node<std::string>& state) {
	std::string tagName = LOCALNAME(state);
	if (boost::iequals("final", tagName))
		return true;
	if (HAS_ATTR(state, "final") && boost::iequals("true", ATTR(state, "final")))
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
		if(boost::iequals(parent.getLocalName(), "content")) {
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
	if (boost::iequals("initial", tagName))
		return true;
	if (boost::iequals("history", tagName))
		return true;
	return false;
}

bool InterpreterImpl::isTransitionTarget(const Arabica::DOM::Node<std::string>& elem) {
	return (isState(elem) || boost::iequals(LOCALNAME(elem), "history"));
}

bool InterpreterImpl::isAtomic(const Arabica::DOM::Node<std::string>& state) {
	if (boost::iequals("final", LOCALNAME(state)))
		return true;

	if (boost::iequals("parallel", LOCALNAME(state)))
		return false;

	Arabica::DOM::NodeList<std::string> childs = state.getChildNodes();
	for (unsigned int i = 0; i < childs.getLength(); i++) {
		if (isState(childs.item(i)))
			return false;
	}
	return true;
}

bool InterpreterImpl::isHistory(const Arabica::DOM::Node<std::string>& state) {
	if (boost::iequals("history", LOCALNAME(state)))
		return true;
	return false;
}

bool InterpreterImpl::isParallel(const Arabica::DOM::Node<std::string>& state) {
	if (!isState(state))
		return false;
	if (boost::iequals("parallel", LOCALNAME(state)))
		return true;
	return false;
}


bool InterpreterImpl::isCompound(const Arabica::DOM::Node<std::string>& state) {
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

void InterpreterImpl::setupIOProcessors() {
	tthread::lock_guard<tthread::recursive_mutex> lock(_pluginMutex);
	std::map<std::string, IOProcessorImpl*> ioProcs = _factory->getIOProcessors();
	std::map<std::string, IOProcessorImpl*>::iterator ioProcIter = ioProcs.begin();
	while(ioProcIter != ioProcs.end()) {
		if (boost::iequals(ioProcIter->first, "basichttp") && !(_capabilities & CAN_BASIC_HTTP)) {
			ioProcIter++;
			continue;
		}
		if (boost::iequals(ioProcIter->first, "http") && !(_capabilities & CAN_GENERIC_HTTP)) {
			ioProcIter++;
			continue;
		}

		_ioProcessors[ioProcIter->first] = _factory->createIOProcessor(ioProcIter->first, this);
		_ioProcessors[ioProcIter->first].setType(ioProcIter->first);
		_ioProcessors[ioProcIter->first].setInterpreter(this);

		if (boost::iequals(ioProcIter->first, "http")) {
			// this is somewhat ugly
			_httpServlet = static_cast<InterpreterServlet*>(_ioProcessors[ioProcIter->first]._impl.get());
		}

		// register aliases
		std::set<std::string> names = _ioProcessors[ioProcIter->first].getNames();
		std::set<std::string>::iterator nameIter = names.begin();
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

void InterpreterImpl::setCmdLineOptions(int argc, char** argv) {
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
				        (boost::iequals(LOCALNAME(parent), "state") ||
				         boost::iequals(LOCALNAME(parent), "parallel"))) {
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

void InterpreterImpl::dump() {
	if (!_document)
		return;
	std::cout << _document;
}


}
