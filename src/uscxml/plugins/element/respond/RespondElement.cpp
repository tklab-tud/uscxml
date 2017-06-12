/**
 *  @file
 *  @author     2017 Stefan Radomski (stefan.radomski@cs.tu-darmstadt.de)
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

#include "RespondElement.h"
#include "uscxml/util/DOM.h"
#include "uscxml/server/HTTPServer.h"
#include "uscxml/interpreter/LoggingImpl.h"
#include "uscxml/plugins/ioprocessor/http/HTTPIOProcessor.h"

#ifdef BUILD_AS_PLUGINS
#include <Pluma/Connector.hpp>
#endif

namespace uscxml {

using namespace XERCESC_NS;

void RespondElement::enterElement(XERCESC_NS::DOMElement* node) {
	// try to get the request id
	if (!HAS_ATTR(node, X("to"))) {
		ERROR_EXECUTION_THROW2("Respond element requires 'to' attribute", node);
	}
	if (HAS_ATTR(node, X("to")) && !_interpreter->getActionLanguage()->dataModel) {
		ERROR_EXECUTION_THROW2("Respond element with 'to' requires datamodel", node);
	}
	std::string requestId = _interpreter->getActionLanguage()->dataModel.evalAsData(ATTR(node, X("to"))).atom;

	auto ioProcs = _interpreter->getIOProcessors();
	if (ioProcs.find("http") == ioProcs.end()) {
		ERROR_EXECUTION_THROW2("No HTTP ioprocessor associated with interpreter", node);
	}

	// try to get the request object
	IOProcessor ioProc = ioProcs["http"];
	HTTPIOProcessor* http = (HTTPIOProcessor*)(ioProc.getImpl().operator->());


	if (http->getUnansweredRequests().find(requestId) == http->getUnansweredRequests().end()) {
		ERROR_EXECUTION_THROW2("No unanswered HTTP request with given id", node);
	}

	HTTPServer::Request httpReq = http->getUnansweredRequests()[requestId].second;

	assert(httpReq.evhttpReq != NULL);
	HTTPServer::Reply httpReply(httpReq);

	// get the status or default to 200
	std::string statusStr = (HAS_ATTR(node, X("status")) ? ATTR(node, X("status")) : "200");
	if (!isNumeric(statusStr.c_str(), 10)) {
		ERROR_EXECUTION_THROW2("Respond element with non-numeric status: " + statusStr, node);
	}
	httpReply.status = strTo<int>(statusStr);;

	// extract the content
	std::list<DOMElement*> contents = DOMUtils::filterChildElements(XML_PREFIX(node).str() + "content", node);
	if (contents.size() > 0) {
		DOMElement* contentElem = contents.front();
		if (HAS_ATTR(contentElem, kXMLCharExpr)) {
			// -- content is evaluated string from datamodel
			if (_interpreter->getActionLanguage()->dataModel) {
				try {
					Data contentData = _interpreter->getActionLanguage()->dataModel.evalAsData(ATTR(contentElem, kXMLCharExpr));
					if (contentData.atom.length() > 0) {
						httpReply.content = contentData.atom;
						httpReply.headers["Content-Type"] = "text/plain";
					} else if (contentData.binary) {
						httpReply.content = std::string(contentData.binary.getData(), contentData.binary.getSize());
						httpReply.headers["Content-Type"] = contentData.binary.getMimeType();
					} else if (contentData.node) {
						std::stringstream ss;
						ss << contentData.node;
						httpReply.content = ss.str();;
						httpReply.headers["Content-Type"] = "application/xml";
					} else {
						httpReply.content = Data::toJSON(contentData);
						httpReply.headers["Content-Type"] = "application/json";
					}
				} catch (Event e) {
					ERROR_EXECUTION_RETHROW(e, "Syntax error with expr in content child of respond element", node);
				}
			} else {
				ERROR_EXECUTION_THROW2("content element has expr attribute but no datamodel is specified", node);
			}
		} else if (HAS_ATTR(contentElem, X("file")) || HAS_ATTR(contents.front(), X("fileexpr"))) {
			// -- content is from file
			URL file;
			if (HAS_ATTR(contentElem, X("fileexpr"))) {
				if (_interpreter->getActionLanguage()->dataModel) {
					try {
						file = _interpreter->getActionLanguage()->dataModel.evalAsData(ATTR(contentElem, X("fileexpr"))).atom;
					} catch (Event e) {
						ERROR_EXECUTION_RETHROW(e, "Syntax error with fileexpr in content child of respond element", node);
					}
				}
			} else {
				file = ATTR(contentElem, X("file"));
			}
			if (file) {
				httpReply.content = file.getInContent();
				size_t lastDot;
				if ((lastDot = file.path().find_last_of(".")) != std::string::npos) {
					std::string extension = file.path().substr(lastDot + 1);
					std::string mimeType = URL::getMimeType(extension);
					if (mimeType.length() > 0) {
						httpReply.headers["Content-Type"] = mimeType;
					}
				}
			}
		} else if (contentElem->hasChildNodes()) {  // -- content embedded as child nodes ------
			httpReply.content = X(contentElem->getFirstChild()->getNodeValue()).str();
		} else {
			ERROR_EXECUTION_THROW2("content element does not specify any content", node);
		}
	}

	// process headers
	std::list<DOMElement*> headers = DOMUtils::filterChildElements(XML_PREFIX(node).str() + "header", node);
	for (auto headerElem : headers) {

		std::string name;
		if (HAS_ATTR(headerElem, kXMLCharName)) {
			name = ATTR(headerElem, kXMLCharName);
		} else if(HAS_ATTR(headerElem, X("nameexpr"))) {
			if (_interpreter->getActionLanguage()->dataModel) {
				try {
					name = _interpreter->getActionLanguage()->dataModel.evalAsData(ATTR(headerElem, X("nameexpr"))).atom;
				} catch (Event e) {
					ERROR_EXECUTION_RETHROW(e, "Syntax error with nameexpr in header child of Respond element", headerElem);
				}
			} else {
				ERROR_EXECUTION_THROW2("header element has nameexpr attribute but no datamodel is specified", headerElem);
			}
		} else {
			ERROR_EXECUTION_THROW2("header element has no name or nameexpr attribute", headerElem);
		}

		std::string value;
		if (HAS_ATTR(headerElem, X("value"))) {
			value = ATTR(headerElem, X("value"));
		} else if(HAS_ATTR(headerElem, X("valueexpr"))) {
			if (_interpreter->getActionLanguage()->dataModel) {
				try {
					value = _interpreter->getActionLanguage()->dataModel.evalAsData(ATTR(headerElem, X("valueexpr"))).atom;
				} catch (Event e) {
					ERROR_EXECUTION_RETHROW(e, "Syntax error with valueexpr in header child of Respond element", headerElem);
				}
			} else {
				ERROR_EXECUTION_THROW2("header element has valueexpr attribute but no datamodel is specified", headerElem);
			}
		} else {
			ERROR_EXECUTION_THROW2("header element has no value or valueexpr attribute", headerElem);
			return;
		}

		httpReply.headers[name] = value;
	}

	// send the reply
	HTTPServer::reply(httpReply);
	http->getUnansweredRequests().erase(requestId);
}

}
