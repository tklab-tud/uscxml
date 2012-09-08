#include "uscxml/Message.h"
#include <DOM/SAX2DOM/SAX2DOM.hpp>
#include <SAX/helpers/CatchErrorHandler.hpp>

namespace uscxml {

static int _dataIndentation = 1;


Arabica::DOM::Document<std::string> Data::toDocument() {
  Arabica::DOM::DOMImplementation<std::string> domFactory = Arabica::SimpleDOM::DOMImplementation<std::string>::getDOMImplementation();
  Arabica::DOM::Document<std::string> document = domFactory.createDocument("http://www.w3.org/2005/07/scxml", "message", 0);
  Arabica::DOM::Element<std::string> scxmlMsg = document.getDocumentElement();
  scxmlMsg.setPrefix("scxml");
  scxmlMsg.setAttribute("version", "1.0");
  
  if (compound.size() > 0 || array.size() > 0) {
    Arabica::DOM::Element<std::string> payloadElem = document.createElementNS("http://www.w3.org/2005/07/scxml", "scxml:payload");
    scxmlMsg.appendChild(payloadElem);

    // we do not support nested attibutes
    if (compound.size() > 0) {
      std::map<std::string, Data>::iterator compoundIter = compound.begin();
      while(compoundIter != compound.end()) {
        if (compoundIter->second.atom.size() > 0) {
          Arabica::DOM::Element<std::string> propertyElem = document.createElementNS("http://www.w3.org/2005/07/scxml", "scxml:property");
          propertyElem.setAttribute("name", compoundIter->first);
          Arabica::DOM::Text<std::string> textElem = document.createTextNode(compoundIter->second.atom);
          propertyElem.appendChild(textElem);
          payloadElem.appendChild(propertyElem);
        }
        compoundIter++;
      }
  }
  }
  return document;
}

Arabica::DOM::Document<std::string> Event::toDocument() {
  Arabica::DOM::DOMImplementation<std::string> domFactory = Arabica::SimpleDOM::DOMImplementation<std::string>::getDOMImplementation();
  Arabica::DOM::Document<std::string> document = Data::toDocument();
  Arabica::DOM::Element<std::string> scxmlMsg = document.getDocumentElement();
  
  scxmlMsg.setAttribute("source", origin);
  scxmlMsg.setAttribute("name", name);
  
  return document;
}

Arabica::DOM::Document<std::string> SendRequest::toDocument() {
  Arabica::DOM::DOMImplementation<std::string> domFactory = Arabica::SimpleDOM::DOMImplementation<std::string>::getDOMImplementation();
  Arabica::DOM::Document<std::string> document = Event::toDocument();
  Arabica::DOM::Element<std::string> scxmlMsg = document.getDocumentElement();
  
  scxmlMsg.setAttribute("sendid", sendid);
  
  return document;
}

Arabica::DOM::Document<std::string> InvokeRequest::toDocument() {
  Arabica::DOM::DOMImplementation<std::string> domFactory = Arabica::SimpleDOM::DOMImplementation<std::string>::getDOMImplementation();
  Arabica::DOM::Document<std::string> document = Event::toDocument();
  Arabica::DOM::Element<std::string> scxmlMsg = document.getDocumentElement();
  
  scxmlMsg.setAttribute("invokeid", invokeid);
  
  return document;
}

Data Data::fromXML(const std::string& xmlString) {
}
  
Event Event::fromXML(const std::string& xmlString) {
  Arabica::SAX2DOM::Parser<std::string> eventParser;
  Arabica::SAX::CatchErrorHandler<std::string> errorHandler;
  eventParser.setErrorHandler(errorHandler);

  std::istringstream is(xmlString);
  Arabica::SAX::InputSource<std::string> inputSource;
  inputSource.setByteStream(is);
  
  Event event;
  if(eventParser.parse(inputSource) && eventParser.getDocument().hasChildNodes()) {
    Arabica::DOM::Element<std::string> scxmlMsg = eventParser.getDocument().getDocumentElement();
    if (HAS_ATTR(scxmlMsg, "name"))
      event.name = ATTR(scxmlMsg, "name");
    if (HAS_ATTR(scxmlMsg, "sendid"))
      event.sendid = ATTR(scxmlMsg, "sendid");
  }
  return event;
}

SendRequest SendRequest::fromXML(const std::string& xmlString) {
	Event::fromXML(xmlString);
}

InvokeRequest InvokeRequest::fromXML(const std::string& xmlString) {
	Event::fromXML(xmlString);
}

#ifndef SWIGJAVA
std::ostream& operator<< (std::ostream& os, const Event& event) {
  os << (event.type == Event::EXTERNAL ? "External" : "Internal") << " Event " << (event.dom ? "with DOM attached" : "") << std::endl;
  
  if (event.name.size() > 0)
    os << "  name: " << event.name << std::endl;
    if (event.origin.size() > 0)
    os << "  origin: " << event.origin << std::endl;
  if (event.origintype.size() > 0)
    os << "  origintype: " << event.origintype << std::endl;
  _dataIndentation++;
  os << "  data: " << (Data)event << std::endl;
  _dataIndentation--;
  return os;
}
#endif

#ifndef SWIGJAVA
std::ostream& operator<< (std::ostream& os, const Data& data) {
  std::string indent;
  for (int i = 0; i < _dataIndentation; i++) {
    indent += "  ";
  }
  if (false) {
  } else if (data.compound.size() > 0) {
    int longestKey = 0;
    std::map<std::string, Data>::const_iterator compoundIter = data.compound.begin();
    while(compoundIter != data.compound.end()) {
      if (compoundIter->first.size() > longestKey)
        longestKey = compoundIter->first.size();
      compoundIter++;
    }
    std::string keyPadding;
    for (unsigned int i = 0; i < longestKey; i++)
      keyPadding += " ";

    os << "{" << std::endl;
    compoundIter = data.compound.begin();
    while(compoundIter != data.compound.end()) {
      os << indent << "  \"" << compoundIter->first << "\" " << keyPadding.substr(0, longestKey - compoundIter->first.size()) << "= ";
      _dataIndentation += 2;
      os << compoundIter->second << "," << std::endl;
      _dataIndentation -= 2;
      compoundIter++;
    }
    os << indent << "}" << std::endl;
  } else if (data.array.size() > 0) {
    os << "[" << std::endl;
    std::map<std::string, Data>::const_iterator compoundIter = data.compound.begin();
    while(compoundIter != data.compound.end()) {
      _dataIndentation += 2;
      os << indent << "  " << compoundIter->second << "," << std::endl;
      _dataIndentation -= 2;
      compoundIter++;
    }
    os << indent << "]" << std::endl;
  } else if (data.atom.size() > 0) {
    if (data.type == Data::VERBATIM) {
      os << indent << "\"" << data.atom << "\"";
    } else {
      os << indent << data.atom;
    }
  }
  return os;
}
#endif

}