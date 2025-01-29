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
#include "uscxml/config.h"

namespace uscxml {

using namespace XERCESC_NS;

std::shared_ptr<ContentExecutorImpl> BasicContentExecutor::create(ContentExecutorCallbacks* callbacks) {
	return std::shared_ptr<ContentExecutorImpl>(new BasicContentExecutor(callbacks));
}

void BasicContentExecutor::processRaise(XERCESC_NS::DOMElement* content) {
	Event raised(ATTR(content, kXMLCharEvent));
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
		if (HAS_ATTR(element, kXMLCharEventExpr)) {
			sendEvent.name = _callbacks->evalAsData(ATTR(element, kXMLCharEventExpr)).atom;
		} else if (HAS_ATTR(element, kXMLCharEvent)) {
			sendEvent.name = ATTR(element, kXMLCharEvent);
		}
	} catch (ErrorEvent e) {
		ERROR_EXECUTION_RETHROW(e, "Syntax error in send element eventexpr", element);
	}

	try {
		// target
		if (HAS_ATTR(element, kXMLCharTargetExpr)) {
			target = _callbacks->evalAsData(ATTR(element, kXMLCharTargetExpr)).atom;
		} else if (HAS_ATTR(element, kXMLCharTarget)) {
			target = ATTR(element, kXMLCharTarget);
		}
	} catch (ErrorEvent e) {
		ERROR_EXECUTION_RETHROW(e,"Syntax error in send element targetexpr", element);
	}

	try {
		// type
		if (HAS_ATTR(element, kXMLCharTypeExpr)) {
			type = _callbacks->evalAsData(ATTR(element, kXMLCharTypeExpr)).atom;
		} else if (HAS_ATTR(element, kXMLCharType)) {
			type = ATTR(element, kXMLCharType);
		}
	} catch (ErrorEvent e) {
		ERROR_EXECUTION_RETHROW(e, "Syntax error in send element typeexpr", element);
	}

	try {
		// id
		if (HAS_ATTR(element, kXMLCharId)) {
			sendEvent.sendid = ATTR(element, kXMLCharId);
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
			sendEvent.sendid = ATTR(getParentState(element), kXMLCharId) + "." + UUID::getUUID();
			if (HAS_ATTR(element, kXMLCharIdLocation)) {
				_callbacks->assign(ATTR(element, kXMLCharIdLocation), Data(sendEvent.sendid, Data::VERBATIM), std::map<std::string, std::string>());
			} else {
				sendEvent.hideSendId = true;
			}
		}
	} catch (ErrorEvent e) {
		ERROR_EXECUTION_RETHROW(e, "Syntax error in send element idlocation", element);
	}

	try {
		// delay
		std::string delay;
		if (HAS_ATTR(element, kXMLCharDelayExpr)) {
			delay = _callbacks->evalAsData(ATTR(element, kXMLCharDelayExpr));
		} else if (HAS_ATTR(element, kXMLCharDelay)) {
			delay = ATTR(element, kXMLCharDelay);
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
				LOG(_callbacks->getLogger(), USCXML_ERROR) << "Cannot make sense of delay value " << delay << ": does not end in 's' or 'ms'" << std::endl;
			}
		}
	} catch (ErrorEvent e) {
		ERROR_EXECUTION_RETHROW(e, "Syntax error in send element delayexpr", element);
	}

	try {
		// namelist
		processNameLists(sendEvent.namelist, element);
	} catch (ErrorEvent e) {
		ERROR_EXECUTION_RETHROW(e, "Syntax error in send element namelist", element);
	}


	try {
		// params
		processParams(sendEvent.params, element);
	} catch (ErrorEvent e) {
		ERROR_EXECUTION_RETHROW(e, "Syntax error in send element param expr", element);
	}

	try {
		// content
		std::list<DOMElement*> contents = DOMUtils::filterChildElements(XML_PREFIX(element).str() + "content", element);
		if (contents.size() > 0) {
			sendEvent.data = elementAsData(contents.front());
		}
	} catch (ErrorEvent e) {
		ERROR_EXECUTION_RETHROW(e, "Syntax error in send element content", element);
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
	if (HAS_ATTR(content, kXMLCharSendId)) {
		sendid = ATTR(content, kXMLCharSendId);
	} else if (HAS_ATTR(content, kXMLCharSendIdExpr)) {
		sendid = _callbacks->evalAsData(ATTR(content, kXMLCharSendIdExpr)).atom;
	} else {
		ERROR_EXECUTION_THROW2("Cancel element has neither sendid nor sendidexpr attribute", content);

	}
	_callbacks->cancelDelayed(sendid);
}

void BasicContentExecutor::processIf(XERCESC_NS::DOMElement* content) {
	bool blockIsTrue = _callbacks->isTrue(ATTR(content, kXMLCharCond));

	for (auto childElem = content->getFirstElementChild(); childElem; childElem = childElem->getNextElementSibling()) {
		if (iequals(TAGNAME(childElem), XML_PREFIX(content).str() + "elseif")) {
			if (blockIsTrue) {
				// last block was true, break here
				break;
			}
			blockIsTrue = _callbacks->isTrue(ATTR(childElem, kXMLCharCond));
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
			process(childElem);
		}
	}
}

void BasicContentExecutor::processAssign(XERCESC_NS::DOMElement* content) {
	std::string location = ATTR(content, kXMLCharLocation);

	std::map<std::string, std::string> additionalAttr;
	auto xmlAttrs = content->getAttributes();
	size_t nrAttrs = xmlAttrs->getLength();
	for (size_t i = 0; i < nrAttrs; i++) {
		auto attr = xmlAttrs->item(i);
		additionalAttr[X(attr->getNodeName()).str()] = X(attr->getNodeValue()).str();
	}

	_callbacks->assign(location, elementAsData(content), additionalAttr);
}

void BasicContentExecutor::processForeach(XERCESC_NS::DOMElement* content) {
	std::string array = ATTR(content, kXMLCharArray);
	std::string item = ATTR(content, kXMLCharItem);
	std::string index = (HAS_ATTR(content, kXMLCharIndex) ? ATTR(content, kXMLCharIndex) : "");

	uint32_t iterations = 0;
	iterations = _callbacks->getLength(array);

	for (uint32_t iteration = 0; iteration < iterations; iteration++) {
		_callbacks->setForeach(item, array, index, iteration);

		for (auto childElem = content->getFirstElementChild(); childElem; childElem = childElem->getNextElementSibling()) {
			process(childElem);
		}
	}
}

void BasicContentExecutor::processLog(XERCESC_NS::DOMElement* content) {
	std::string label = ATTR(content, kXMLCharLabel);
	std::string expr = ATTR(content, kXMLCharExpr);

	Data d = _callbacks->evalAsData(expr);
#if 0
	if (label.size() > 0) {
		_callbacks->getLogger().log(USCXML_LOG) << label << ": ";
	}
	_callbacks->getLogger().log(USCXML_LOG) << d << std::endl;
#else
	// see issue113
	_callbacks->getLogger().log(USCXML_LOG) << (label.size() > 0 ? label + ": " : "") << d << std::endl;
#endif

}

void BasicContentExecutor::processScript(XERCESC_NS::DOMElement* content) {
	// contents were already downloaded in setupDOM, see to SCXML rec 5.8
	std::string scriptContent(X(content->getTextContent()));
	_callbacks->eval(scriptContent);

}

void BasicContentExecutor::process(XERCESC_NS::DOMElement* block) {
	std::string tagName = TAGNAME(block);
	std::string xmlPrefix = XML_PREFIX(block);

	if (iequals(tagName, xmlPrefix + "onentry") ||
	        iequals(tagName, xmlPrefix + "onexit") ||
	        iequals(tagName, xmlPrefix + "transition")) {

		try {
			for (auto childElem = block->getFirstElementChild(); childElem; childElem = childElem->getNextElementSibling()) {
				// process any child eleents
				process(childElem);
			}
		} catch (Event e) {
			// there has been an error in an executable content block
			// we do not care - parent scope has to handle it!
			throw e;
		}
		return;
	}

	if (iequals(tagName, xmlPrefix + "finalize")) {
		std::list<DOMNode*> childElems = DOMUtils::filterChildType(DOMNode::ELEMENT_NODE, block, false);
		if(childElems.size() > 0) {
			for(auto elemIter = childElems.begin(); elemIter != childElems.end(); elemIter++) {
				process(static_cast<DOMElement*>(*elemIter));
			}
		} else {
			// issue 67 - empty finalize element
			DOMNode* parent = block->getParentNode();
			if (parent && parent->getNodeType() == DOMNode::ELEMENT_NODE) {
				DOMElement* invokeElem = static_cast<DOMElement*>(parent);
				if (iequals(X(invokeElem->getTagName()).str(), xmlPrefix + "invoke")) {
					// we are the empth finalize element of an invoke
					// Specification 6.5.2: http://www.w3.org/TR/scxml/#N110EF

					const Event& event = _callbacks->getCurrentEvent();
					std::list<std::string> names = tokenize(ATTR(invokeElem, kXMLCharNameList));
					for (std::list<std::string>::iterator nameIter = names.begin(); nameIter != names.end(); nameIter++) {
						if (event.namelist.find(*nameIter) != event.namelist.end()) {
							// scxml i/o proc keeps a dedicated namelist
							_callbacks->assign(*nameIter, event.namelist.at(*nameIter), std::map<std::string, std::string>());
						} else if (event.data.compound.find(*nameIter) != event.data.compound.end()) {
							// this is where it would end up with non scxml i/o processors
							_callbacks->assign(*nameIter, event.data.compound.at(*nameIter), std::map<std::string, std::string>());
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
		} else if (iequals(tagName, xmlPrefix + "raise")) {
			processRaise(block);
		} else if (iequals(tagName, xmlPrefix + "send")) {
			processSend(block);
		} else if (iequals(tagName, xmlPrefix + "cancel")) {
			processCancel(block);
		} else if (iequals(tagName, xmlPrefix + "if")) {
			processIf(block);
		} else if (iequals(tagName, xmlPrefix + "assign")) {
			processAssign(block);
		} else if (iequals(tagName, xmlPrefix + "foreach")) {
			processForeach(block);
		} else if (iequals(tagName, xmlPrefix + "log")) {
			processLog(block);
		} else if (iequals(tagName, xmlPrefix + "script")) {
			processScript(block);
		} else if (Factory::getInstance()->hasExecutableContent(LOCALNAME(block), X(block->getNamespaceURI()))) {
			// custom executable content, ask the factory about it!
			if (_customExecContent.find(block) == _customExecContent.end()) {
				_customExecContent[block] = _callbacks->createExecutableContent(LOCALNAME(block), X(block->getNamespaceURI()));
			}
			_customExecContent[block].enterElement(block);

			// process custom element's children?
			if (_customExecContent[block].processChildren()) {
				std::list<DOMNode*> childElems = DOMUtils::filterChildType(DOMNode::ELEMENT_NODE, block, false);
				if(childElems.size() > 0) {
					for(auto elemIter = childElems.begin(); elemIter != childElems.end(); elemIter++) {
						process(static_cast<DOMElement*>(*elemIter));
					}
				}
			}
			_customExecContent[block].exitElement(block);
		} else {
			LOG(_callbacks->getLogger(), USCXML_ERROR) << tagName << std::endl;
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
	if (HAS_ATTR(element, kXMLCharTypeExpr)) {
		type = _callbacks->evalAsData(ATTR(element, kXMLCharTypeExpr)).atom;
	} else if (HAS_ATTR(element, kXMLCharType)) {
		type = ATTR(element, kXMLCharType);
	} else {
		// test 422
		type = "http://www.w3.org/TR/scxml/";
	}

	// src
	if (HAS_ATTR(element, kXMLCharSourceExpr)) {
		source = _callbacks->evalAsData(ATTR(element, kXMLCharSourceExpr)).atom;
	} else if (HAS_ATTR(element, kXMLCharSource)) {
		source = ATTR(element, kXMLCharSource);
	}
	if (source.length() > 0) {
		// absolutize url
	}

	// id
	try {
		if (HAS_ATTR(element, kXMLCharId)) {
			invokeEvent.invokeid = ATTR(element, kXMLCharId);
		} else {
			invokeEvent.invokeid = ATTR(getParentState(element), kXMLCharId) + "." + UUID::getUUID();
			if (HAS_ATTR(element, kXMLCharIdLocation)) {
				_callbacks->assign(ATTR(element, kXMLCharIdLocation), Data(invokeEvent.invokeid, Data::VERBATIM), std::map<std::string, std::string>());
			}
		}

		// we need the invokeid to uninvoke
		char* invokeId = (char*)malloc(invokeEvent.invokeid.size() + 1);
		memcpy(invokeId, invokeEvent.invokeid.c_str(), invokeEvent.invokeid.size());
		invokeId[invokeEvent.invokeid.size()] = 0;

		element->setUserData(kXMLCharInvokeId, (void*)invokeId, NULL);
	} catch (ErrorEvent e) {
		ERROR_EXECUTION_RETHROW(e, "Syntax error in invoke element idlocation", element);
	}

	try {
		// namelist
		processNameLists(invokeEvent.namelist, element);
	} catch (ErrorEvent e) {
		ERROR_EXECUTION_RETHROW(e, "Syntax error in send element namelist", element);
	}


	try {
		// params
		processParams(invokeEvent.params, element);
	} catch (ErrorEvent e) {
		ERROR_EXECUTION_RETHROW(e, "Syntax error in send element param expr", element);
	}

	try {
		// content
		std::list<DOMElement*> contents = DOMUtils::filterChildElements(XML_PREFIX(element).str() + "content", element);
		if (contents.size() > 0) {
#if 0
			invokeEvent.data.node = contents.front();
#else
			// test530
			Data d = elementAsData(contents.front());
			if (d.type == Data::INTERPRETED && d.atom.size() > 0) {
				// immediately evaluate!
				invokeEvent.data = _callbacks->evalAsData(d.atom);
			} else {
				invokeEvent.data = d;
			}
#endif
		}
	} catch (ErrorEvent e) {
		ERROR_EXECUTION_RETHROW(e, "Syntax error in invoke element content", element);
	}

	// autoforward
	if (HAS_ATTR(element, kXMLCharAutoForward)) {
		if (iequals(ATTR(element, kXMLCharAutoForward), "true")) {
			autoForward = true;
		}
	}

	// finalize
	DOMElement* finalize = NULL;
	std::list<DOMElement*> finalizes = DOMUtils::filterChildElements(XML_PREFIX(element).str() + "finalize", element);
	if (finalizes.size() > 0) {
		finalize = finalizes.front();
	}

	USCXML_MONITOR_CALLBACK2(_callbacks->getMonitors(), beforeInvoking, element, invokeEvent.invokeid);
	_callbacks->invoke(type, source, autoForward, finalize, invokeEvent);
	USCXML_MONITOR_CALLBACK2(_callbacks->getMonitors(), afterInvoking, element, invokeEvent.invokeid);
}

void BasicContentExecutor::uninvoke(XERCESC_NS::DOMElement* invoke) {
	char* invokeId = (char*)invoke->getUserData(X(kXMLCharInvokeId));
	assert(invokeId != NULL);

	USCXML_MONITOR_CALLBACK2(_callbacks->getMonitors(), beforeUninvoking, invoke, invokeId);
	_callbacks->uninvoke(invokeId);
	USCXML_MONITOR_CALLBACK2(_callbacks->getMonitors(), afterUninvoking, invoke, invokeId);

	invoke->setUserData(kXMLCharInvokeId, NULL, NULL);
	free(invokeId);
}

void BasicContentExecutor::raiseDoneEvent(XERCESC_NS::DOMElement* state, XERCESC_NS::DOMElement* doneData) {

	Event doneEvent;
	doneEvent.name = "done.state.";
	doneEvent.name += HAS_ATTR(state, kXMLCharId) ? ATTR(state, kXMLCharId) : DOMUtils::idForNode(state);

	if (doneData != NULL) {
		try {
			try {
				// namelist
				processNameLists(doneEvent.namelist, doneData);
			} catch (ErrorEvent e) {
				ERROR_EXECUTION_RETHROW(e, "Syntax error in donedata element namelist", doneData);
			}


			try {
				// params
				processParams(doneEvent.params, doneData);
			} catch (ErrorEvent e) {
				ERROR_EXECUTION_RETHROW(e, "Syntax error in donedata element param expr", doneData);
			}

			try {
				// content
				std::list<DOMElement*> contents = DOMUtils::filterChildElements(XML_PREFIX(doneData).str() + "content", doneData);
				if (contents.size() > 0) {
					if (HAS_ATTR(contents.front(), kXMLCharExpr) &&
					        !_callbacks->isLegalDataValue(ATTR(contents.front(), kXMLCharExpr))) {
						ERROR_EXECUTION_THROW2("Expression '" + ATTR(contents.front(), kXMLCharExpr) + "' is not a legal data value", contents.front());
					} else {
						doneEvent.data = elementAsData(contents.front());
					}
				}
			} catch (ErrorEvent e) {
				ERROR_EXECUTION_RETHROW(e, "Syntax error in donedata element content", doneData);
			}

		} catch (ErrorEvent exc) {
			// clean out data test488 (needed?)
			doneEvent.data = Data();

			Event e(exc);
			_callbacks->enqueueInternal(e);
			//        std::cout << exc << std::endl;
			//        throw e;
		} catch (Event e) {
			ERROR_EXECUTION_RETHROW(e, "Error in donedata element", doneData);
		}

	}

	_callbacks->enqueueInternal(doneEvent);

}

void BasicContentExecutor::processNameLists(std::map<std::string, Data>& nameMap, DOMElement* element) {
	if (HAS_ATTR(element, kXMLCharNameList)) {
		std::list<std::string> names = tokenize(ATTR(element, kXMLCharNameList));
		for (std::list<std::string>::const_iterator nameIter = names.begin(); nameIter != names.end(); nameIter++) {
			nameMap[*nameIter] = _callbacks->evalAsData(*nameIter);
		}
	}
}

void BasicContentExecutor::processParams(std::multimap<std::string, Data>& paramMap, DOMElement* element) {
	std::list<DOMElement*> params = DOMUtils::filterChildElements(XML_PREFIX(element).str() + "param", element);
	for (auto paramIter = params.begin(); paramIter != params.end(); paramIter++) {
		std::string name = ATTR(*paramIter, kXMLCharName);
		Data d;
		if (HAS_ATTR(*paramIter, kXMLCharExpr)) {
			d = _callbacks->evalAsData(ATTR(*paramIter, kXMLCharExpr));
		} else if (HAS_ATTR(*paramIter, kXMLCharLocation)) {
			d = _callbacks->evalAsData(ATTR(*paramIter, kXMLCharLocation));
		} else {
			d = elementAsData(*paramIter);
		}
		paramMap.insert(make_pair(name, d));
	}
}

Data BasicContentExecutor::elementAsData(XERCESC_NS::DOMElement* element) {
	// element with expr
	if (HAS_ATTR(element, kXMLCharExpr)) {
		// we cannot throw here:
		// - with init, we need to check in the datamodel
		// - with content, we need to invoke isLegalDataValue later
		// test 277, 528
		return Data(ATTR(element, kXMLCharExpr), Data::INTERPRETED);
	}

	// element with external src - this ought to behave just as with child nodes below
	if (HAS_ATTR(element, kXMLCharSource)) {

		// remove any old child elements
		while(element->getFirstElementChild() != NULL) {
			element->removeChild(element->getFirstElementChild());
		}

		std::string src = ATTR(element, kXMLCharSource);
		URL url(ATTR(element, kXMLCharSource));
		if (!url.isAbsolute()) {
			url = URL::resolve(url, _callbacks->getBaseURL());
		}
		std::string content = url.getInContent();

		// append as XML?
		try {
			std::unique_ptr<XERCESC_NS::XercesDOMParser> parser(new XERCESC_NS::XercesDOMParser());
			parser->setValidationScheme(XERCESC_NS::XercesDOMParser::Val_Always);
			parser->setDoNamespaces(true);
			parser->useScanner(XERCESC_NS::XMLUni::fgWFXMLScanner);

			std::unique_ptr<XERCESC_NS::ErrorHandler> errHandler(new XERCESC_NS::HandlerBase());
			parser->setErrorHandler(errHandler.get());

			XERCESC_NS::MemBufInputSource is((XMLByte*)content.c_str(), content.size(), X("fake"));
			is.setPublicId(X(url));

			parser->parse(is);
			XERCESC_NS::DOMNode* newNode = element->getOwnerDocument()->importNode(parser->getDocument()->getDocumentElement(), true);

			// we need to save the DOM somewhere .. Data::adoptedDoc was not good enough
			element->appendChild(newNode);
			goto SOURCE_APPEND_DONE;
		} catch (...) {
		}

		// append as text (are we leaking?)
		XERCESC_NS::DOMText* textNode = element->getOwnerDocument()->createTextNode(X(content));
		element->appendChild(textNode);
	}
SOURCE_APPEND_DONE:

	if (element->hasChildNodes()) {
		// XML elements e.g. for content with invoke
		std::list<DOMNode*> elementChildren = DOMUtils::filterChildType(DOMNode::ELEMENT_NODE, element);
		if (elementChildren.size() > 0) {
			// always return parent element, even with a single child node
			return Data(static_cast<DOMNode*>(element));
		}

		// expression in text element
		std::list<DOMNode*> textChildren = DOMUtils::filterChildType(DOMNode::TEXT_NODE, element);
		if (textChildren.size() > 0) {
			std::stringstream contentSS;
			for (auto textIter = textChildren.begin(); textIter != textChildren.end(); textIter++) {
				contentSS << X((*textIter)->getNodeValue());
			}

			try {
				Data d = _callbacks->getAsData(contentSS.str());
				if (!d.empty())
					return d;
			} catch(...) {}

			// anything else is considered verbatim - space normalize?
			return Data(spaceNormalize(contentSS.str()), Data::VERBATIM);
		}
	}

	return Data();
}

}
