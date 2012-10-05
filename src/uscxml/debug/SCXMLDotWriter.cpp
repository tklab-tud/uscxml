#include "SCXMLDotWriter.h"
#include "uscxml/Interpreter.h"
#include <boost/algorithm/string.hpp> // replace_all

namespace uscxml {

using namespace Arabica::DOM;
  
int SCXMLDotWriter::_indentation = 0;
  
SCXMLDotWriter::SCXMLDotWriter(Interpreter* interpreter) {
	_interpreter = interpreter;
}

SCXMLDotWriter::~SCXMLDotWriter()	{
	
}

std::string SCXMLDotWriter::getPrefix() {
  std::string prefix = "";
  for (int i = 0; i < _indentation; i++)
    prefix += "  ";
  return prefix;
}
  
void SCXMLDotWriter::toDot(const std::string& filename, Interpreter* interpreter) {
  std::ofstream outfile(filename.c_str());
  NodeList<std::string > scxmlElems = interpreter->getDocument().getElementsByTagName("scxml");
  SCXMLDotWriter writer(interpreter);
	if (scxmlElems.getLength() > 0) {
    _indentation++;
    outfile << "digraph {" << std::endl;
    outfile << "rankdir=LR;" << std::endl;
    writer.writeSCXMLElement(outfile, (Arabica::DOM::Element<std::string>)scxmlElems.item(0));
    _indentation--;
    outfile << "}" << std::endl;
  }
  
}

void SCXMLDotWriter::writeSCXMLElement(std::ostream& os, const Arabica::DOM::Element<std::string>& elem) {
  writeStateElement(os, elem);

//  std::string elemId = idForNode(elem);
//  os << getPrefix() << "subgraph \"cluster" << elemId.substr(1, elemId.length() - 1) << " {" << std::endl;
//  _indentation++;
//  os << getPrefix() << "label=\"" << nameForNode(elem) << "\"" << std::endl;
//  writeStateElement(os, (Arabica::DOM::Element<std::string>)_interpreter->getInitialState());
//  os << getPrefix() << "} " << std::endl;

}

void SCXMLDotWriter::writeStateElement(std::ostream& os, const Arabica::DOM::Element<std::string>& elem) {

  std::string elemId = idForNode(elem);
  NodeList<std::string > childElems = elem.getChildNodes();

  if (_knownIds.find(elemId) != _knownIds.end())
    return;
  _knownIds.insert(elemId);
  
  bool subgraph = Interpreter::isCompound(elem) || Interpreter::isParallel(elem);
  if (subgraph) {
    _indentation++;
    os << getPrefix() << "subgraph \"cluster_" << elemId << "\" {" << std::endl;
    os << getPrefix() << "label=\"" << nameForNode(elem) << "\\l\"" << std::endl;
  }
  
  os << getPrefix() << "\"" << elemId << "\"[";
  os << "label=<<b>State</b><br />" << nameForNode(elem) << ">,";
  if (_interpreter->isInitial(elem))
    os << "style=filled,";
  if (_interpreter->isFinal(elem))
    os << "shape=doublecircle,";
  os << "];" << std::endl;
  
  std::string details = getDetailedLabel(elem);
//  std::cout << details << std::endl;
  
  if (details.size() > 0) {
    os << getPrefix() << "\"" << elemId << "Exec\"[";
//    os << "fontsize=10,";
    os << "shape=box,";
    os << "color=grey,";
    os << "label=<" << details << ">";
    os << "]" << std::endl;
    os << getPrefix() << "\"" << elemId << "\" -> \"" << elemId << "Exec\" [arrowhead=none, color=grey]" << std::endl;
  }
  
//  NodeList<std::string > childElems = elem.getChildNodes();
//  for (int i = 0; i < childElems.getLength(); i++) {
//    if (Interpreter::isState(childElems.item(i))) {
//      writeStateElement(os, (Arabica::DOM::Element<std::string>)childElems.item(i));
//    }
//  }

  for (int i = 0; i < childElems.getLength(); i++) {
    if (childElems.item(i).getNodeType() == Node_base::ELEMENT_NODE && boost::iequals(TAGNAME(childElems.item(i)), "transition")) {
      writeTransitionElement(os, (Arabica::DOM::Element<std::string>)childElems.item(i));
      os << getPrefix() << "\"" << elemId << "\" -> \"" << idForNode(childElems.item(i)) << "\"" << std::endl;
    }
    if (Interpreter::isState(childElems.item(i))) {
      writeStateElement(os, (Arabica::DOM::Element<std::string>)childElems.item(i));
    }
    if (childElems.item(i).getNodeType() == Node_base::ELEMENT_NODE && boost::iequals(TAGNAME(childElems.item(i)), "initial")) {
      NodeList<std::string > grandChildElems = childElems.item(i).getChildNodes();
      for (int j = 0; j < grandChildElems.getLength(); j++) {
        if (grandChildElems.item(j).getNodeType() == Node_base::ELEMENT_NODE && boost::iequals(TAGNAME(grandChildElems.item(j)), "transition")) {
          writeTransitionElement(os, (Arabica::DOM::Element<std::string>)grandChildElems.item(j));
          os << getPrefix() << "\"" << elemId << "\" -> \"" << idForNode(grandChildElems.item(j)) << "\"" << std::endl;
        }
      }
    }
  }

  if (subgraph) {
    _indentation--;
    os << getPrefix() << "} " << std::endl;
  }

}

void SCXMLDotWriter::writeTransitionElement(std::ostream& os, const Arabica::DOM::Element<std::string>& elem) {
  std::string elemId = idForNode(elem);
  
  Arabica::XPath::NodeSet<std::string> targetStates = _interpreter->getTargetStates(elem);

  std::string label;
  os << getPrefix() << "\"" << elemId << "\"[";
//  os << "fontsize=10,";
  os << "shape=box,";
  os << "label=<<b>Transition</b><br align=\"left\" />";
  if (HAS_ATTR(elem, "event"))
    os << "event: " << ATTR(elem, "event");
  if (HAS_ATTR(elem, "cond"))
    os << "cond: " << ATTR(elem, "cond");
  if (!HAS_ATTR(elem, "cond") && !HAS_ATTR(elem, "event"))
    os << "unconditional";
  os << ">";
  os << "]" << std::endl;

  for (int i = 0; i < targetStates.size(); i++) {
    os << getPrefix() << "\"" << elemId << "\" -> \"" << idForNode(targetStates[i]) << "\"" << std::endl;
    writeStateElement(os, (Arabica::DOM::Element<std::string>)targetStates[i]);
  }

}

std::string SCXMLDotWriter::getDetailedLabel(const Arabica::DOM::Element<std::string>& elem, int indentation) {

/*
 <table>
    <tr>
      <td colspan="2">onEntry</td>
    </tr>
    <tr>
      <td>Details</td>
      <td bgcolor="#eee">
        Nested Content
      </td>
    </tr>
  </table>
*/

  std::list<struct ElemDetails> content;
  
  NodeList<std::string > childElems = elem.getChildNodes();
  for (int i = 0; i < childElems.getLength(); i++) {
    if (childElems.item(i).getNodeType() != Node_base::ELEMENT_NODE)
      continue;
    
    if (Interpreter::isState(childElems.item(i)) ||
        boost::iequals(TAGNAME(childElems.item(i)), "transition") ||
        boost::iequals(TAGNAME(childElems.item(i)), "initial") ||
        false)
      continue;

    struct ElemDetails details;
    details.name = "<b>" + TAGNAME(childElems.item(i)) + "</b>";
    
    // provide details for special elements here
    
    // param ---------
    if (boost::iequals(TAGNAME(childElems.item(i)), "param")) {
      if (HAS_ATTR(childElems.item(i), "name"))
        details.name += " " + ATTR(childElems.item(i), "name") + " = ";
      if (HAS_ATTR(childElems.item(i), "expr"))
        details.name += ATTR(childElems.item(i), "expr");
      if (HAS_ATTR(childElems.item(i), "location"))
        details.name += ATTR(childElems.item(i), "location");
    }

    // data ---------
    if (boost::iequals(TAGNAME(childElems.item(i)), "data")) {
      if (HAS_ATTR(childElems.item(i), "id"))
        details.name += " " + ATTR(childElems.item(i), "id") + " = ";
      if (HAS_ATTR(childElems.item(i), "src"))
        details.name += ATTR(childElems.item(i), "src");
      if (HAS_ATTR(childElems.item(i), "expr"))
        details.name += ATTR(childElems.item(i), "expr");
      NodeList<std::string > grandChildElems = childElems.item(i).getChildNodes();
      for (int j = 0; j < grandChildElems.getLength(); j++) {
        if (grandChildElems.item(j).getNodeType() == Node_base::TEXT_NODE) {
          details.name += dotEscape(grandChildElems.item(j).getNodeValue());
        }
      }
    }

    // invoke ---------
    if (boost::iequals(TAGNAME(childElems.item(i)), "invoke")) {
      if (HAS_ATTR(childElems.item(i), "type"))
        details.name += "<br />type = " + ATTR(childElems.item(i), "type");
      if (HAS_ATTR(childElems.item(i), "typeexpr"))
        details.name += "<br />type = " + ATTR(childElems.item(i), "typeexpr");
      if (HAS_ATTR(childElems.item(i), "src"))
        details.name += "<br />src = " + ATTR(childElems.item(i), "src");
      if (HAS_ATTR(childElems.item(i), "srcexpr"))
        details.name += "<br />src = " + ATTR(childElems.item(i), "srcexpr");
      if (HAS_ATTR(childElems.item(i), "id"))
        details.name += "<br />id = " + ATTR(childElems.item(i), "id");
      if (HAS_ATTR(childElems.item(i), "idlocation"))
        details.name += "<br />id = " + ATTR(childElems.item(i), "idlocation");
    }

    // send ---------
    if (boost::iequals(TAGNAME(childElems.item(i)), "send")) {
      if (HAS_ATTR(childElems.item(i), "type"))
        details.name += "<br />type = " + ATTR(childElems.item(i), "type");
      if (HAS_ATTR(childElems.item(i), "typeexpr"))
        details.name += "<br />type = " + ATTR(childElems.item(i), "typeexpr");
      if (HAS_ATTR(childElems.item(i), "event"))
        details.name += "<br />event = " + ATTR(childElems.item(i), "event");
      if (HAS_ATTR(childElems.item(i), "eventexpr"))
        details.name += "<br />event = " + ATTR(childElems.item(i), "eventexpr");
      if (HAS_ATTR(childElems.item(i), "target"))
        details.name += "<br />target = " + ATTR(childElems.item(i), "target");
      if (HAS_ATTR(childElems.item(i), "targetexpr"))
        details.name += "<br />target = " + ATTR(childElems.item(i), "targetexpr");
      if (HAS_ATTR(childElems.item(i), "delay"))
        details.name += "<br />delay = " + ATTR(childElems.item(i), "delay");
      if (HAS_ATTR(childElems.item(i), "delayexpr"))
        details.name += "<br />delay = " + ATTR(childElems.item(i), "delayexpr");
    }

    // script ---------
    if (boost::iequals(TAGNAME(childElems.item(i)), "script")) {
      details.name += " ";
      if (HAS_ATTR(childElems.item(i), "src"))
        details.name += ATTR(childElems.item(i), "src");
      NodeList<std::string > grandChildElems = childElems.item(i).getChildNodes();
      for (int j = 0; j < grandChildElems.getLength(); j++) {
        if (grandChildElems.item(j).getNodeType() == Node_base::TEXT_NODE) {
          details.name += dotEscape(grandChildElems.item(j).getNodeValue());
        }
      }
    }

    // recurse
    details.content = getDetailedLabel((Arabica::DOM::Element<std::string>)childElems.item(i), indentation + 1);
    content.push_back(details);
  }
  
  std::stringstream ssContent;

  if (content.size() > 0) {
    ssContent << "<table cellspacing=\"2\" cellpadding=\"0\" border=\"0\">";
    
    std::list<struct ElemDetails>::iterator contentIter = content.begin();
    while(contentIter != content.end()) {
      ssContent << "<tr>";
//      ssContent << "<td align=\"left\" colspan=\"2\">" << contentIter->name << "</td>";
      ssContent << "<td balign=\"left\" align=\"left\">" << contentIter->name << "</td>";
      ssContent << "</tr>";

      if (contentIter->content.size() > 0) {
        ssContent << "<tr>";
//      ssContent << "<td>" << contentIter->details << "</td>";
        ssContent << "<td bgcolor=\"#" << colorForIndent(indentation + 1) << "\">" << contentIter->content << "</td>";
        ssContent << "</tr>";
      }
      contentIter++;

    }
    ssContent << "</table>";
  }
  return ssContent.str();
}

std::string SCXMLDotWriter::dotEscape(const std::string& text) {
  std::string escaped(text);
  boost::replace_all(escaped, "", "");
  
  return escaped;
}

std::string SCXMLDotWriter::colorForIndent(int indent) {
  int color = 255 - (16 * indent);
  std::stringstream ss;
  ss << std::hex << color;
  ss << std::hex << color;
  ss << std::hex << color;
  return ss.str();
}
  
std::string SCXMLDotWriter::nameForNode(const Arabica::DOM::Node<std::string>& node) {
  std::string elemName;
  if (node.getNodeType() == Node_base::ELEMENT_NODE) {
    Arabica::DOM::Element<std::string> elem = (Arabica::DOM::Element<std::string>)node;
    if (elem.hasAttribute("name")) {
      elemName = elem.getAttribute("name");
    } else if (elem.hasAttribute("id")) {
      elemName = elem.getAttribute("id");
    }
  }
  if (elemName.size() == 0)
    elemName = boost::lexical_cast<std::string>(node.getLocalName());
  
  return elemName;

}
  
std::string SCXMLDotWriter::idForNode(const Arabica::DOM::Node<std::string>& node) {
  std::string elemId;
  if (node.getNodeType() == Node_base::ELEMENT_NODE) {
    Arabica::DOM::Element<std::string> elem = (Arabica::DOM::Element<std::string>)node;
    if (elem.hasAttribute("name")) {
      elemId = elem.getAttribute("name");
    } else if (elem.hasAttribute("id")) {
      elemId = elem.getAttribute("id");
    }
  }
  if (elemId.size() == 0) {
    Arabica::DOM::Node<std::string> tmpParent = node;
    Arabica::DOM::Node<std::string> tmpIndex;
    do {
      if (tmpParent.getNodeType() != Node_base::ELEMENT_NODE)
        continue;
      
      tmpIndex = tmpParent;
      int index = 0;
      
      while((tmpIndex = tmpIndex.getPreviousSibling()))
        index++;

      std::stringstream ssElemId;
      ssElemId << TAGNAME(tmpParent) << index << ".";
      elemId = ssElemId.str() + elemId;
    } while ((tmpParent = tmpParent.getParentNode()));
//    elemId = ssElemId.str();
  }
  
  std::replace(elemId.begin(), elemId.end(), '-', '_');
//  std::replace(elemId.begin(), elemId.end(), '.', '_');

  return elemId;
}
  
}