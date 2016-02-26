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

#include "RespondElement.h"
#include "uscxml/plugins/invoker/http/HTTPServletInvoker.h"
#include "uscxml/server/InterpreterServlet.h"
#include "uscxml/dom/DOMUtils.h"
#include <glog/logging.h>

#ifdef BUILD_AS_PLUGINS
#include <Pluma/Connector.hpp>
#endif

namespace uscxml {

#ifdef BUILD_AS_PLUGINS
PLUMA_CONNECTOR
bool pluginConnect(pluma::Host& host) {
	host.add( new RespondElementProvider() );
	return true;
}
#endif

boost::shared_ptr<ExecutableContentImpl> RespondElement::create(InterpreterImpl* interpreter) {
	boost::shared_ptr<RespondElement> invoker = boost::shared_ptr<RespondElement>(new RespondElement());
	invoker->_interpreter = interpreter;
	return invoker;
}

void RespondElement::enterElement(const Arabica::DOM::Element<std::string>& node) {
	// try to get the request id
	if (!HAS_ATTR(node, "to")) {
		LOG(ERROR) << "Respond element requires to attribute";
		return;
	}
	if (HAS_ATTR(node, "to") && !_interpreter->getDataModel()) {
		LOG(ERROR) << "Respond element with to requires datamodel";
		return;
	}
	std::string requestId = _interpreter->getDataModel().evalAsString(ATTR(node, "to"));

	// try to get the request object
	InterpreterHTTPServlet* servlet = _interpreter->getHTTPServlet();
	tthread::lock_guard<tthread::recursive_mutex> lock(servlet->getMutex());

	if (servlet->getRequests().find(requestId) == servlet->getRequests().end()) {
		LOG(ERROR) << "No matching HTTP request for respond element";
		return;
	}

	assert(servlet->getRequests().find(requestId) != servlet->getRequests().end());
	HTTPServer::Request httpReq = servlet->getRequests()[requestId];
	assert(httpReq.evhttpReq != NULL);
	HTTPServer::Reply httpReply(httpReq);
	servlet->getRequests().erase(requestId);

	// get the status or default to 200
	std::string statusStr = (HAS_ATTR(node, "status") ? ATTR(node, "status") : "200");
	if (!isNumeric(statusStr.c_str(), 10)) {
		LOG(ERROR) << "Respond element with non-numeric status " << statusStr;
		return;
	}
	httpReply.status = strTo<int>(statusStr);;

	// extract the content
	Arabica::XPath::NodeSet<std::string> contents = DOMUtils::filterChildElements(_interpreter->getNameSpaceInfo().getXMLPrefixForNS(getNamespace()) + "content", node);
	if (contents.size() > 0) {
		Arabica::DOM::Element<std::string> contentElem = Arabica::DOM::Element<std::string>(contents[0]);
		if (HAS_ATTR(contentElem, "expr")) { // -- content is evaluated string from datamodel ------
			if (_interpreter->getDataModel()) {
				try {
					Data contentData = _interpreter->getDataModel().getStringAsData(ATTR(contentElem, "expr"));
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
					LOG(ERROR) << "Syntax error with expr in content child of Respond element:" << std::endl << e << std::endl;
					return;
				}
			} else {
				LOG(ERROR) << "content element has expr attribute but no datamodel is specified.";
				return;
			}
		} else if (HAS_ATTR(contentElem, "file") || HAS_ATTR(contentElem, "fileexpr")) { // -- content is from file ------
			URL file;
			if (HAS_ATTR(contentElem, "fileexpr")) {
				if (_interpreter->getDataModel()) {
					try {
						file = "file://" + _interpreter->getDataModel().evalAsString(ATTR(contentElem, "fileexpr"));
					} catch (Event e) {
						LOG(ERROR) << "Syntax error with fileexpr in content child of Respond element:" << std::endl << e << std::endl;
						return;
					}
				}
			} else {
				file = "file://" + ATTR(contentElem, "fileexpr");
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
		} else if (contents[0].hasChildNodes()) {  // -- content embedded as child nodes ------
			httpReply.content = contents[0].getFirstChild().getNodeValue();
		} else {
			LOG(ERROR) << "content element does not specify any content.";
			return;
		}
	}

	// process headers
	Arabica::XPath::NodeSet<std::string> headers = DOMUtils::filterChildElements(_interpreter->getNameSpaceInfo().getXMLPrefixForNS(getNamespace()) + "header", node);
	for (size_t i = 0; i < headers.size(); i++) {
		Arabica::DOM::Element<std::string> headerElem = Arabica::DOM::Element<std::string>(headers[i]);

		std::string name;
		if (HAS_ATTR(headerElem, "name")) {
			name = ATTR(headerElem, "name");
		} else if(HAS_ATTR(headerElem, "nameexpr")) {
			if (_interpreter->getDataModel()) {
				try {
					name = _interpreter->getDataModel().evalAsString(ATTR(headerElem, "nameexpr"));
				} catch (Event e) {
					LOG(ERROR) << "Syntax error with nameexpr in header child of Respond element:" << std::endl << e << std::endl;
					return;
				}
			} else {
				LOG(ERROR) << "header element has nameexpr attribute but no datamodel is specified.";
				return;
			}
		} else {
			LOG(ERROR) << "header element has no name or nameexpr attribute.";
			return;
		}

		std::string value;
		if (HAS_ATTR(headerElem, "value")) {
			value = ATTR(headerElem, "value");
		} else if(HAS_ATTR(headerElem, "valueexpr")) {
			if (_interpreter->getDataModel()) {
				try {
					value = _interpreter->getDataModel().evalAsString(ATTR(headerElem, "valueexpr"));
				} catch (Event e) {
					LOG(ERROR) << "Syntax error with valueexpr in header child of Respond element:" << std::endl << e << std::endl;
					return;
				}
			} else {
				LOG(ERROR) << "header element has valueexpr attribute but no datamodel is specified.";
				return;
			}
		} else {
			LOG(ERROR) << "header element has no value or valueexpr attribute.";
			return;
		}

		httpReply.headers[name] = value;
	}

	// send the reply
	HTTPServer::reply(httpReply);
	servlet->getRequests().erase(requestId);
}

void RespondElement::exitElement(const Arabica::DOM::Element<std::string>& node) {

}

}