#include "ResponseElement.h"
#include "uscxml/plugins/invoker/http/HTTPServletInvoker.h"
#include <glog/logging.h>

#ifdef BUILD_AS_PLUGINS
#include <Pluma/Connector.hpp>
#endif

namespace uscxml {

#ifdef BUILD_AS_PLUGINS
PLUMA_CONNECTOR
bool connect(pluma::Host& host) {
	host.add( new ResponseElementProvider() );
	return true;
}
#endif

boost::shared_ptr<ExecutableContentImpl> ResponseElement::create(Interpreter* interpreter) {
	boost::shared_ptr<ResponseElement> invoker = boost::shared_ptr<ResponseElement>(new ResponseElement());
	invoker->_interpreter = interpreter;
	return invoker;
}

void ResponseElement::enterElement(const Arabica::DOM::Node<std::string>& node) {
	// try to get the request id
	if (!HAS_ATTR(node, "request") && !HAS_ATTR(node, "requestexpr")) {
		LOG(ERROR) << "Response element requires request or requestexpr";
		return;
	}
	if (HAS_ATTR(node, "requestexpr") && !_interpreter->getDataModel()) {
		LOG(ERROR) << "Response element with requestexpr requires datamodel";
		return;
	}
	std::string requestId = (HAS_ATTR(node, "request") ? ATTR(node, "request") : _interpreter->getDataModel().evalAsString(ATTR(node, "requestexpr")));

	// try to get the request object
	HTTPServletInvoker* servlet = _interpreter->getHTTPServlet();
	tthread::lock_guard<tthread::recursive_mutex> lock(servlet->getMutex());

	if (servlet->getRequests().find(requestId) == servlet->getRequests().end()) {
		LOG(ERROR) << "No matching HTTP request for response element";
		return;
	}
	HTTPServer::Request httpReq = servlet->getRequests()[requestId];
	HTTPServer::Reply httpReply(httpReq);

	// get the status or default to 200
	std::string statusStr = (HAS_ATTR(node, "status") ? ATTR(node, "status") : "200");
	if (!isNumeric(statusStr.c_str(), 10)) {
		LOG(ERROR) << "Response element with non-numeric status " << statusStr;
		return;
	}
	httpReply.status = strTo<int>(statusStr);;
  
	// extract the content
	Arabica::XPath::NodeSet<std::string> contents = Interpreter::filterChildElements(_interpreter->getXMLPrefixForNS(getNamespace()) + "content", node);
	if (contents.size() > 0) {
		if (HAS_ATTR(contents[0], "expr")) { // -- content is evaluated string from datamodel ------
			if (_interpreter->getDataModel()) {
				try {
					std::string contentValue = _interpreter->getDataModel().evalAsString(ATTR(contents[0], "expr"));
					httpReply.content = contentValue;
				} catch (Event e) {
					LOG(ERROR) << "Syntax error with expr in content child of response element:" << std::endl << e << std::endl;
          return;
				}
			} else {
				LOG(ERROR) << "content element has expr attribute but no datamodel is specified.";
        return;
			}
		} else if (HAS_ATTR(contents[0], "file") || HAS_ATTR(contents[0], "fileexpr")) { // -- content is from file ------
      URL file;
			if (HAS_ATTR(contents[0], "fileexpr")) {
        if (_interpreter->getDataModel()) {
          try {
            file = "file://" + _interpreter->getDataModel().evalAsString(ATTR(contents[0], "fileexpr"));
          } catch (Event e) {
            LOG(ERROR) << "Syntax error with fileexpr in content child of response element:" << std::endl << e << std::endl;
            return;
          }
				}
			} else {
        file = "file://" + ATTR(contents[0], "fileexpr");
			}
      if (file) {
        httpReply.content = file.getInContent();
        size_t lastDot;
        if ((lastDot = file.path().find_last_of(".")) != std::string::npos) {
          std::string extension = file.path().substr(lastDot + 1);
          std::string mimeType = HTTPServer::mimeTypeForExtension(extension);
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
	Arabica::XPath::NodeSet<std::string> headers = Interpreter::filterChildElements(_interpreter->getXMLPrefixForNS(getNamespace()) + "header", node);
  for (int i = 0; i < headers.size(); i++) {
    std::string name;
    if (HAS_ATTR(headers[i], "name")) {
      name = ATTR(headers[i], "name");
    } else if(HAS_ATTR(headers[i], "nameexpr")) {
      if (_interpreter->getDataModel()) {
        try {
          name = _interpreter->getDataModel().evalAsString(ATTR(headers[i], "nameexpr"));
        } catch (Event e) {
          LOG(ERROR) << "Syntax error with nameexpr in header child of response element:" << std::endl << e << std::endl;
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
    if (HAS_ATTR(headers[i], "value")) {
      value = ATTR(headers[i], "value");
    } else if(HAS_ATTR(headers[i], "expr")) {
      if (_interpreter->getDataModel()) {
        try {
          value = _interpreter->getDataModel().evalAsString(ATTR(headers[i], "expr"));
        } catch (Event e) {
          LOG(ERROR) << "Syntax error with expr in header child of response element:" << std::endl << e << std::endl;
          return;
        }
      } else {
				LOG(ERROR) << "header element has expr attribute but no datamodel is specified.";
        return;
      }
    } else {
      LOG(ERROR) << "header element has no value or expr attribute.";
      return;
    }

    httpReply.headers[name] = value;
  }
  

	// send the reply
	HTTPServer::reply(httpReply);
	servlet->getRequests().erase(requestId);
}

void ResponseElement::exitElement(const Arabica::DOM::Node<std::string>& node) {

}

}