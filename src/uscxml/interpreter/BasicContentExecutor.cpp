/**
 *  @file
 *  @author     2016 Stefan Radomski (stefan.radomski@cs.tu-darmstadt.de)
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

#include "BasicContentExecutor.h"
#include "uscxml/Interpreter.h"
#include "uscxml/util/String.h"
#include "uscxml/util/Predicates.h"
#include "uscxml/util/UUID.h"
#include "uscxml/util/URL.h"

#include <xercesc/dom/DOM.hpp>
#include <xercesc/parsers/XercesDOMParser.hpp>
#include <xercesc/sax/HandlerBase.hpp>
#include <xercesc/framework/MemBufInputSource.hpp>

#include "uscxml/interpreter/Logging.h"

namespace uscxml {

using namespace XERCESC_NS;

std::shared_ptr<ContentExecutorImpl> BasicContentExecutor::create(ContentExecutorCallbacks* callbacks) {
	return std::shared_ptr<ContentExecutorImpl>(new BasicContentExecutor(callbacks));
}

void BasicContentExecutor::processRaise(XERCESC_NS::DOMElement* content) {
	Event raised(ATTR(content, "event"));
	_callbacks->enqueueInternal(raised);
}

void BasicContentExecutor::processSend(XERCESC_NS::DOMElement* element) {
	Event sendEvent;
	std::string target;
	std::string type = "http://www.w3.org/TR/scxml/#SCXMLEventProcessor"; // default
	uint32_t delayMs = 0;

	// test 331
	sendEvent.eventType = Event::EXTERNAL;

	// test 228
	std::string invokeId = _callbacks->getInvokeId();
	if (invokeId.size() > 0) {
		sendEvent.invokeid = invokeId;
	}

	try {
		// event
		if (HAS_ATTR(element, "eventexpr")) {
			sendEvent.name = _callbacks->evalAsData(ATTR(element, "eventexpr")).atom;
		} else if (HAS_ATTR(element, "event")) {
			sendEvent.name = ATTR(element, "event");
		}
	} catch (Event e) {
		ERROR_EXECUTION_THROW2("Syntax error in send element eventexpr", element);
	}

	try {
		// target
		if (HAS_ATTR(element, "targetexpr")) {
			target = _callbacks->evalAsData(ATTR(element, "targetexpr")).atom;
		} else if (HAS_ATTR(element, "target")) {
			target = ATTR(element, "target");
		}
	} catch (Event e) {
		ERROR_EXECUTION_THROW2("Syntax error in send element targetexpr", element);
	}

	try {
		// type
		if (HAS_ATTR(element, "typeexpr")) {
			type = _callbacks->evalAsData(ATTR(element, "typeexpr")).atom;
		} else if (HAS_ATTR(element, "type")) {
			type = ATTR(element, "type");
		}
	} catch (Event e) {
		ERROR_EXECUTION_THROW2("Syntax error in send element typeexpr", element);
	}

	try {
		// id
		if (HAS_ATTR(element, "id")) {
			sendEvent.sendid = ATTR(element, "id");
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
			sendEvent.sendid = ATTR(getParentState(element), "id") + "." + UUID::getUUID();
			if (HAS_ATTR(element, "idlocation")) {
				_callbacks->assign(ATTR(element, "idlocation"), Data(sendEvent.sendid, Data::VERBATIM));
			} else {
				sendEvent.hideSendId = true;
			}
		}
	} catch (Event e) {
		ERROR_EXECUTION_THROW2("Syntax error in send element idlocation", element);
	}

	try {
		// delay
		std::string delay;
		if (HAS_ATTR(element, "delayexpr")) {
			delay = _callbacks->evalAsData(ATTR(element, "delayexpr"));
		} else if (HAS_ATTR(element, "delay")) {
			delay = ATTR(element, "delay");
		}
		if (delay.size() > 0) {
			NumAttr delayAttr(delay);
			if (iequals(delayAttr.unit, "ms")) {
				delayMs = strTo<uint32_t>(delayAttr.value);
			} else if (iequals(delayAttr.unit, "s")) {
				delayMs = strTo<double>(delayAttr.value) * 1000;
			} else if (delayAttr.unit.length() == 0) { // unit less delay is interpreted as milliseconds
				delayMs = strTo<uint32_t>(delayAttr.value);
			} else {
				LOG(_callbacks->getLogger(), USCXML_ERROR) << "Cannot make sense of delay value " << delay << ": does not end in 's' or 'ms'";
			}
		}
	} catch (Event e) {
		ERROR_EXECUTION_THROW2("Syntax error in send element delayexpr", element);
	}

	try {
		// namelist
		processNameLists(sendEvent.namelist, element);
	} catch (Event e) {
		ERROR_EXECUTION_THROW2("Syntax error in send element namelist", element);
	}


	try {
		// params
		processParams(sendEvent.params, element);
	} catch (Event e) {
		ERROR_EXECUTION_THROW2("Syntax error in send element param expr", element);
	}

	try {
		// content
		std::list<DOMElement*> contents = DOMUtils::filterChildElements(XML_PREFIX(element).str() + "content", element);
		if (contents.size() > 0) {
			sendEvent.data = elementAsData(contents.front());
		}
	} catch (Event e) {
		ERROR_EXECUTION_THROW2("Syntax error in send element content", element);
	}

	//        if (sendReq->dom) {
	//            std::stringstream ss;
	//            ss << sendReq->dom;
	//            sendReq->xml = ss.str();
	//            _dataModel.replaceExpressions(sendReq->xml);
	//        }

	//        assert(_sendIds.find(sendReq->sendid) == _sendIds.end());
	//        _sendIds[sendReq->sendid] = std::make_pair(this, sendReq);

	try {
		_callbacks->checkValidSendType(type, target);
	} catch (ErrorEvent e) {
		e.data.compound["xpath"] = uscxml::Data(DOMUtils::xPathForNode(element), uscxml::Data::VERBATIM);
		// test 332
		e.sendid = sendEvent.sendid;
		throw e;
	}
	_callbacks->enqueue(type, target, delayMs, sendEvent);

}

void BasicContentExecutor::processCancel(XERCESC_NS::DOMElement* content) {
	std::string sendid;
	if (HAS_ATTR(content, "sendid")) {
		sendid = ATTR(content, "sendid");
	} else if (HAS_ATTR(content, "sendidexpr")) {
		sendid = _callbacks->evalAsData(ATTR(content, "sendidexpr")).atom;
	} else {
		ERROR_EXECUTION_THROW2("Cancel element has neither sendid nor sendidexpr attribute", content);

	}
	_callbacks->cancelDelayed(sendid);
}

void BasicContentExecutor::processIf(XERCESC_NS::DOMElement* content) {
	bool blockIsTrue = _callbacks->isTrue(ATTR(content, "cond"));

	for (auto childElem = content->getFirstElementChild(); childElem; childElem = childElem->getNextElementSibling()) {
		if (iequals(TAGNAME(childElem), XML_PREFIX(content).str() + "elseif")) {
			if (blockIsTrue) {
				// last block was true, break here
				break;
			}
			blockIsTrue = _callbacks->isTrue(ATTR(childElem, "cond"));
			continue;
		}
		if (iequals(TAGNAME(childElem), XML_PREFIX(content).str() + "else")) {
			if (blockIsTrue) {
				// last block was true, break here
				break;
			}
			blockIsTrue = true;
			continue;
		}

		// current block is true
		if (blockIsTrue) {
			// we do now that the prefix of content is correct
			process(childElem, XML_PREFIX(content));
		}
	}
}

void BasicContentExecutor::processAssign(XERCESC_NS::DOMElement* content) {
	std::string location = ATTR(content, "location");
	_callbacks->assign(location, elementAsData(content));
}

void BasicContentExecutor::processForeach(XERCESC_NS::DOMElement* content) {
	std::string array = ATTR(content, "array");
	std::string item = ATTR(content, "item");
	std::string index = (HAS_ATTR(content, "index") ? ATTR(content, "index") : "");

	uint32_t iterations = 0;
	iterations = _callbacks->getLength(array);

	for (uint32_t iteration = 0; iteration < iterations; iteration++) {
		_callbacks->setForeach(item, array, index, iteration);

		for (auto childElem = content->getFirstElementChild(); childElem; childElem = childElem->getNextElementSibling()) {
			process(childElem, XML_PREFIX(content));
		}
	}
}

void BasicContentExecutor::processLog(XERCESC_NS::DOMElement* content) {
	std::string label = ATTR(content, "label");
	std::string expr = ATTR(content, "expr");

	Data d = _callbacks->evalAsData(expr);
	if (label.size() > 0) {
		std::cout << label << ": ";
	}
	std::cout << d << std::endl;
}

void BasicContentExecutor::processScript(XERCESC_NS::DOMElement* content) {
	// download as necessary
	std::string scriptContent(X(content->getTextContent()));
	_callbacks->evalAsData(scriptContent);

}

void BasicContentExecutor::process(XERCESC_NS::DOMElement* block, const X& xmlPrefix) {
	std::string tagName = TAGNAME(block);


	if (iequals(tagName, xmlPrefix.str() + "onentry") ||
	        iequals(tagName, xmlPrefix.str() + "onexit") ||
	        iequals(tagName, xmlPrefix.str() + "transition")) {

		try {
			for (auto childElem = block->getFirstElementChild(); childElem; childElem = childElem->getNextElementSibling()) {
				// process any child eleents
				process(childElem, xmlPrefix);
			}
		} catch (Event e) {
			// there has been an error in an executable content block
			// we do not care - parent scope has to handle it!
			throw e;
		}
		return;
	}

	if (iequals(tagName, xmlPrefix.str() + "finalize")) {
		std::list<DOMNode*> childElems = DOMUtils::filterChildType(DOMNode::ELEMENT_NODE, block, false);
		if(childElems.size() > 0) {
			for(auto elemIter = childElems.begin(); elemIter != childElems.end(); elemIter++) {
				process(static_cast<DOMElement*>(*elemIter), xmlPrefix);
			}
		} else {
			// issue 67 - empty finalize element
			DOMNode* parent = block->getParentNode();
			if (parent && parent->getNodeType() == DOMNode::ELEMENT_NODE) {
				DOMElement* invokeElem = static_cast<DOMElement*>(parent);
				if (iequals(X(invokeElem->getTagName()).str(), xmlPrefix.str() + "invoke")) {
					// we are the empth finalize element of an invoke
					// Specification 6.5.2: http://www.w3.org/TR/scxml/#N110EF

					const Event& event = _callbacks->getCurrentEvent();
					std::list<std::string> names = tokenize(ATTR(invokeElem, "namelist"));
					for (std::list<std::string>::iterator nameIter = names.begin(); nameIter != names.end(); nameIter++) {
						if (event.namelist.find(*nameIter) != event.namelist.end()) {
							// scxml i/o proc keeps a dedicated namelist
							_callbacks->assign(*nameIter, event.namelist.at(*nameIter));
						} else if (event.data.compound.find(*nameIter) != event.data.compound.end()) {
							// this is where it would end up with non scxml i/o processors
							_callbacks->assign(*nameIter, event.data.compound.at(*nameIter));
						}
					}
				}
			}

		}
		return;
	}

	try {
		USCXML_MONITOR_CALLBACK1(_callbacks->getMonitors(), beforeExecutingContent, block);

		if (false) {
		} else if (iequals(tagName, xmlPrefix.str() + "raise")) {
			processRaise(block);
		} else if (iequals(tagName, xmlPrefix.str() + "send")) {
			processSend(block);
		} else if (iequals(tagName, xmlPrefix.str() + "cancel")) {
			processCancel(block);
		} else if (iequals(tagName, xmlPrefix.str() + "if")) {
			processIf(block);
		} else if (iequals(tagName, xmlPrefix.str() + "assign")) {
			processAssign(block);
		} else if (iequals(tagName, xmlPrefix.str() + "foreach")) {
			processForeach(block);
		} else if (iequals(tagName, xmlPrefix.str() + "log")) {
			processLog(block);
		} else if (iequals(tagName, xmlPrefix.str() + "script")) {
			processScript(block);
		} else {
			LOG(_callbacks->getLogger(), USCXML_ERROR) << tagName;
			assert(false);
		}
	} catch (ErrorEvent exc) {

		Event e(exc);
		_callbacks->enqueueInternal(e);
		LOG(_callbacks->getLogger(), USCXML_ERROR) << exc << std::endl;
		USCXML_MONITOR_CALLBACK1(_callbacks->getMonitors(), afterExecutingContent, block);

		throw e; // will be catched in microstepper

	}
	USCXML_MONITOR_CALLBACK1(_callbacks->getMonitors(), afterExecutingContent, block);

}

void BasicContentExecutor::invoke(XERCESC_NS::DOMElement* element) {
	std::string type;
	std::string source;
	bool autoForward = false;
	Event invokeEvent;

	// type
	if (HAS_ATTR(element, "typeexpr")) {
		type = _callbacks->evalAsData(ATTR(element, "typeexpr")).atom;
	} else if (HAS_ATTR(element, "type")) {
		type = ATTR(element, "type");
	} else {
		// test 422
		type = "http://www.w3.org/TR/scxml/";
	}

	// src
	if (HAS_ATTR(element, "srcexpr")) {
		source = _callbacks->evalAsData(ATTR(element, "srcexpr")).atom;
	} else if (HAS_ATTR(element, "src")) {
		source = ATTR(element, "src");
	}
	if (source.length() > 0) {
		// absolutize url
	}

	// id
	try {
		if (HAS_ATTR(element, "id")) {
			invokeEvent.invokeid = ATTR(element, "id");
		} else {
			invokeEvent.invokeid = ATTR(getParentState(element), "id") + "." + UUID::getUUID();
			if (HAS_ATTR(element, "idlocation")) {
				_callbacks->assign(ATTR(element, "idlocation"), Data(invokeEvent.invokeid, Data::VERBATIM));
			}
		}

		// we need the invokeid to uninvoke
		char* invokeId = (char*)malloc(invokeEvent.invokeid.size() + 1);
		memcpy(invokeId, invokeEvent.invokeid.c_str(), invokeEvent.invokeid.size());
		invokeId[invokeEvent.invokeid.size()] = 0;

		element->setUserData(X("invokeid"), (void*)invokeId, NULL);
	} catch (Event e) {
		ERROR_EXECUTION_THROW2("Syntax error in invoke element idlocation", element);
	}

	try {
		// namelist
		processNameLists(invokeEvent.namelist, element);
	} catch (Event e) {
		ERROR_EXECUTION_THROW2("Syntax error in send element namelist", element);
	}


	try {
		// params
		processParams(invokeEvent.params, element);
	} catch (Event e) {
		ERROR_EXECUTION_THROW2("Syntax error in send element param expr", element);
	}

	try {
		// content
		std::list<DOMElement*> contents = DOMUtils::filterChildElements(XML_PREFIX(element).str() + "content", element);
		if (contents.size() > 0) {
#if 1
			invokeEvent.data.node = contents.front();
#else
			Data d = elementAsData(contents.front());
			if (d.type == Data::INTERPRETED && d.atom.size() > 0) {
				// immediately evaluate!
				invokeEvent.data = _callbacks->evalAsData(d.atom);
			} else {
				invokeEvent.data = d;
			}
#endif
		}
	} catch (Event e) {
		ERROR_EXECUTION_THROW2("Syntax error in invoke element content", element);
	}

	// autoforward
	if (HAS_ATTR(element, "autoforward")) {
		if (iequals(ATTR(element, "autoforward"), "true")) {
			autoForward = true;
		}
	}

	// finalize
	DOMElement* finalize = NULL;
	std::list<DOMElement*> finalizes = DOMUtils::filterChildElements(XML_PREFIX(element).str() + "finalize", element);
	if (finalizes.size() > 0) {
		finalize = finalizes.front();
	}

	USCXML_MONITOR_CALLBACK2(_callbacks->getMonitors(), beforeUninvoking, element, invokeEvent.invokeid);
	_callbacks->invoke(type, source, autoForward, finalize, invokeEvent);
	USCXML_MONITOR_CALLBACK2(_callbacks->getMonitors(), afterUninvoking, element, invokeEvent.invokeid);
}

void BasicContentExecutor::uninvoke(XERCESC_NS::DOMElement* invoke) {
	char* invokeId = (char*)invoke->getUserData(X("invokeid"));
	assert(invokeId != NULL);

	USCXML_MONITOR_CALLBACK2(_callbacks->getMonitors(), beforeUninvoking, invoke, invokeId);
	_callbacks->uninvoke(invokeId);
	USCXML_MONITOR_CALLBACK2(_callbacks->getMonitors(), afterUninvoking, invoke, invokeId);

	invoke->setUserData(X("invokeid"), NULL, NULL);
	free(invokeId);
}

void BasicContentExecutor::raiseDoneEvent(XERCESC_NS::DOMElement* state, XERCESC_NS::DOMElement* doneData) {

	Event doneEvent;
	doneEvent.name = "done.state.";
	doneEvent.name += HAS_ATTR(state, "id") ? ATTR(state, "id") : DOMUtils::idForNode(state);

	if (doneData != NULL) {
		try {
			try {
				// namelist
				processNameLists(doneEvent.namelist, doneData);
			} catch (Event e) {
				ERROR_EXECUTION_THROW2("Syntax error in donedata element namelist", doneData);
			}


			try {
				// params
				processParams(doneEvent.params, doneData);
			} catch (Event e) {
				ERROR_EXECUTION_THROW2("Syntax error in donedata element param expr", doneData);
			}

			try {
				// content
				std::list<DOMElement*> contents = DOMUtils::filterChildElements(XML_PREFIX(doneData).str() + "content", doneData);
				if (contents.size() > 0) {
					doneEvent.data = elementAsData(contents.front());
				}
			} catch (Event e) {
				ERROR_EXECUTION_THROW2("Syntax error in donedata element content", doneData);
			}

		} catch (ErrorEvent exc) {
			// clean out data test488 (needed?)
			doneEvent.data = Data();

			Event e(exc);
			_callbacks->enqueueInternal(e);
			//        std::cout << exc << std::endl;
			//        throw e;
		}
	}

	_callbacks->enqueueInternal(doneEvent);

}

void BasicContentExecutor::processNameLists(std::map<std::string, Data>& nameMap, DOMElement* element) {
	if (HAS_ATTR(element, "namelist")) {
		std::list<std::string> names = tokenize(ATTR(element, "namelist"));
		for (std::list<std::string>::const_iterator nameIter = names.begin(); nameIter != names.end(); nameIter++) {
			nameMap[*nameIter] = _callbacks->evalAsData(*nameIter);
		}
	}
}

void BasicContentExecutor::processParams(std::multimap<std::string, Data>& paramMap, DOMElement* element) {
	std::list<DOMElement*> params = DOMUtils::filterChildElements(XML_PREFIX(element).str() + "param", element);
	for (auto paramIter = params.begin(); paramIter != params.end(); paramIter++) {
		std::string name = ATTR(*paramIter, "name");
		Data d;
		if (HAS_ATTR(*paramIter, "expr")) {
			d = _callbacks->evalAsData(ATTR(*paramIter, "expr"));
		} else if (HAS_ATTR(*paramIter, "location")) {
			d = _callbacks->evalAsData(ATTR(*paramIter, "location"));
		} else {
			d = elementAsData(*paramIter);
		}
		paramMap.insert(make_pair(name, d));
	}
}

Data BasicContentExecutor::elementAsData(XERCESC_NS::DOMElement* element) {
	if (HAS_ATTR(element, "expr")) {
//        return _callbacks->evalAsData(ATTR(element, "expr"));
#if 0
		if (LOCALNAME(element) == "content") {
			// test 528
			return _callbacks->evalAsData(ATTR(element, "expr"));
		} else {
			// test 326
			return Data(ATTR(element, "expr"), Data::INTERPRETED);
		}
#endif
		return _callbacks->evalAsData(ATTR(element, "expr"));
	}

	if (HAS_ATTR(element, "src")) {
		// remote content from URL

		// test 446, test 552, test 558
		std::string src = ATTR(element, "src");
		URL url(ATTR(element, "src"));
		if (!url.isAbsolute()) {
			url = URL::resolve(url, _callbacks->getBaseURL());
		}

		std::string content = url.getInContent();

		// make an attempt to parse as XML
		try {
			XERCESC_NS::XercesDOMParser parser;
			parser.setValidationScheme(XERCESC_NS::XercesDOMParser::Val_Never);
			parser.setDoNamespaces(true);
			parser.useScanner(XERCESC_NS::XMLUni::fgWFXMLScanner);

			XERCESC_NS::HandlerBase errHandler;
			parser.setErrorHandler(&errHandler);

			std::string tmp = url;
			XERCESC_NS::MemBufInputSource is((XMLByte*)content.c_str(), content.size(), X("fake"));

			parser.parse(is);

			Data d;
			XERCESC_NS::DOMDocument* doc = parser.adoptDocument();
			d.adoptedDoc = std::shared_ptr<XERCESC_NS::DOMDocument>(doc);
			d.node = doc->getDocumentElement();

			return d;

		} catch (...) {
			// just ignore and return as an interpreted string below
		}
		try {
			Data d = _callbacks->getAsData(content);
			if (!d.empty())
				return d;
		} catch(...) {}

		return Data(spaceNormalize(content), Data::VERBATIM);

	} else {
		// local content in document

		std::list<DOMNode*> elementChildren = DOMUtils::filterChildType(DOMNode::ELEMENT_NODE, element);
		if (elementChildren.size() == 1) {
			return Data(elementChildren.front());
		} else if (elementChildren.size() > 1) {
			return Data(element);
		}

		std::list<DOMNode*> textChildren = DOMUtils::filterChildType(DOMNode::TEXT_NODE, element);
		if (textChildren.size() > 0) {
			std::stringstream contentSS;
			for (auto textIter = textChildren.begin(); textIter != textChildren.end(); textIter++) {
				contentSS << X((*textIter)->getNodeValue());
			}
#if 0
			try {
				Data d = _callbacks->getAsData(contentSS.str());
				if (!d.empty())
					return d;
			} catch(...) {}
#endif
			// test294, test562
			return Data(spaceNormalize(contentSS.str()), Data::VERBATIM);
		}
	}

//	LOG(USCXML_WARN) << "Element " << DOMUtils::xPathForNode(element) << " did not yield any data";
	return Data();
}

}
