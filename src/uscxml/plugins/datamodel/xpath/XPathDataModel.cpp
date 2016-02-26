/**
 *  @file
 *  @author     2012-2013 Stefan Radomski (stefan.radomski@cs.tu-darmstadt.de)
 *  @author	2013 Enrico Papi (enrico.papi@ajile.it)
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

#include "uscxml/Common.h"
#include "XPathDataModel.h"

#include "uscxml/Message.h"
#include "uscxml/util/String.h"
#include "uscxml/dom/DOMUtils.h"
#include <glog/logging.h>
#include <boost/algorithm/string.hpp>

#include <DOM/SAX2DOM/SAX2DOM.hpp>
//#include <SAX/helpers/CatchErrorHandler.hpp>
//#include <DOM/Events/EventTarget.hpp>
//#include <DOM/Events/EventListener.hpp>

#ifdef BUILD_AS_PLUGINS
#include <Pluma/Connector.hpp>
#endif

namespace uscxml {

using namespace Arabica::XPath;
using namespace Arabica::DOM;

#ifdef BUILD_AS_PLUGINS
PLUMA_CONNECTOR
bool pluginConnect(pluma::Host& host) {
	host.add( new XPathDataModelProvider() );
	return true;
}
#endif

XPathDataModel::XPathDataModel() {
}

boost::shared_ptr<DataModelImpl> XPathDataModel::create(InterpreterInfo* interpreter) {
	boost::shared_ptr<XPathDataModel> dm = boost::shared_ptr<XPathDataModel>(new XPathDataModel());
	dm->_interpreter = interpreter;

//	dm->_xpath->setVariableCompileTimeResolver(_varCTResolver);
//	dm->_xpath->setNamespaceContext(interpreter->getNSContext());

	dm->_funcResolver.setInterpreter(interpreter);
	dm->_xpath.setNamespaceContext(*interpreter->getNameSpaceInfo().getNSContext());
	dm->_xpath.setFunctionResolver(dm->_funcResolver);
	dm->_xpath.setVariableResolver(dm->_varResolver);

	dm->_domFactory = Arabica::SimpleDOM::DOMImplementation<std::string>::getDOMImplementation();
	dm->_doc = dm->_domFactory.createDocument("http://www.w3.org/2005/07/scxml", "", 0);
	dm->_datamodel = dm->_doc.createElement("datamodel");
	dm->_doc.appendChild(dm->_datamodel);

	Element<std::string> ioProcElem = dm->_doc.createElement("data");
	ioProcElem.setAttribute("id", "_ioprocessors");
	std::map<std::string, IOProcessor>::const_iterator ioProcIter = interpreter->getIOProcessors().begin();
	while(ioProcIter != interpreter->getIOProcessors().end()) {
		Element<std::string> ioProc = dm->_doc.createElement("processor");
		ioProc.setAttribute("name", ioProcIter->first);

		Data ioProcData = ioProcIter->second.getDataModelVariables();
		Element<std::string> ioProcLoc = dm->_doc.createElement("location");
		Text<std::string> ioProcLocText = dm->_doc.createTextNode(ioProcData.compound["location"].atom);
		ioProcLoc.appendChild(ioProcLocText);
		ioProc.appendChild(ioProcLoc);
		ioProcElem.appendChild(ioProc);

		ioProcIter++;
	}
	dm->_datamodel.appendChild(ioProcElem);

	NodeSet<std::string> ioProcNodeSet;
	ioProcNodeSet.push_back(ioProcElem);
	dm->_varResolver.setVariable("_ioprocessors", ioProcNodeSet);

	Element<std::string> sessIdElem = dm->_doc.createElement("data");
	sessIdElem.setAttribute("id", "_sessionid");
	Text<std::string> sessIdText = dm->_doc.createTextNode(interpreter->getSessionId());
	sessIdElem.appendChild(sessIdText);
	dm->_datamodel.appendChild(sessIdElem);

	NodeSet<std::string> sessIdNodeSet;
	sessIdNodeSet.push_back(sessIdText);
	dm->_varResolver.setVariable("_sessionid", sessIdNodeSet);


	Element<std::string> nameElem = dm->_doc.createElement("data");
	nameElem.setAttribute("id", "_name");
	Text<std::string> nameText = dm->_doc.createTextNode(interpreter->getName());
	nameElem.appendChild(nameText);
	dm->_datamodel.appendChild(nameElem);

	NodeSet<std::string> nameNodeSet;
	nameNodeSet.push_back(nameText);
	dm->_varResolver.setVariable("_name", nameNodeSet);

	return dm;
}

XPathDataModel::~XPathDataModel() {
}

void XPathDataModel::pushContext() {
}

void XPathDataModel::popContext() {
}

void XPathDataModel::initialize() {
}

void XPathDataModel::setEvent(const Event& event) {
	Element<std::string> eventElem = _doc.createElement("data");
	eventElem.setAttribute("id", "_event");

	Element<std::string> eventDataElem = _doc.createElement("data");
	NodeSet<std::string> eventNodeSet;

	{
		// -- name
		Element<std::string> eventNameElem = _doc.createElement("name");
		Text<std::string> eventName = _doc.createTextNode(event.name.c_str());
		eventNameElem.appendChild(eventName);
		eventElem.appendChild(eventNameElem);
	}
	{
		// -- origin
		Element<std::string> eventOriginElem = _doc.createElement("origin");
		Text<std::string> eventOrigin = _doc.createTextNode(event.origin.c_str());
		eventOriginElem.appendChild(eventOrigin);
		eventElem.appendChild(eventOriginElem);
	}
	{
		// -- type
		Element<std::string> eventTypeElem = _doc.createElement("type");
		Text<std::string> eventType;
		switch (event.eventType) {
		case Event::INTERNAL:
			eventType = _doc.createTextNode("internal");
			break;
		case Event::EXTERNAL:
			eventType = _doc.createTextNode("external");
			break;
		case Event::PLATFORM:
			eventType = _doc.createTextNode("platform");
			break;
		}
		eventTypeElem.appendChild(eventType);
		eventElem.appendChild(eventTypeElem);
	}

	if (event.params.size() > 0) {
		std::multimap<std::string, Data>::const_iterator paramIter = event.params.begin();
		while(paramIter != event.params.end()) {
			Element<std::string> eventParamElem = _doc.createElement("data");
			// this is simplified - Data might be more elaborate than a simple string atom
			Text<std::string> eventParamText = _doc.createTextNode(paramIter->second.atom);

			eventParamElem.setAttribute("id", paramIter->first);
			eventParamElem.appendChild(eventParamText);
			eventDataElem.appendChild(eventParamElem);
			paramIter++;
		}
	}
	if (event.namelist.size() > 0) {
		std::map<std::string, Data>::const_iterator namelistIter = event.namelist.begin();
		while(namelistIter != event.namelist.end()) {
			Element<std::string> eventNamelistElem = _doc.createElement("data");
			// this is simplified - Data might be more elaborate than a simple string atom
			Text<std::string> eventNamelistText = _doc.createTextNode(namelistIter->second.atom);

			eventNamelistElem.setAttribute("id", namelistIter->first);
			eventNamelistElem.appendChild(eventNamelistText);
			eventDataElem.appendChild(eventNamelistElem);
			namelistIter++;
		}
	}
	if (event.raw.size() > 0) {
		Element<std::string> eventRawElem = _doc.createElement("raw");
		Text<std::string> textNode = _doc.createTextNode(event.raw.c_str());
		eventRawElem.appendChild(textNode);
		eventElem.appendChild(eventRawElem);
	}

	if (event.content.size() > 0) {
		Text<std::string> textNode = _doc.createTextNode(spaceNormalize(event.content).c_str());
		eventDataElem.appendChild(textNode);
	}
	if (event.dom) {
		Node<std::string> importedNode = _doc.importNode(event.dom, true);
		eventDataElem.appendChild(importedNode);
	}
	if (event.data.array.size() == 1) {
		Text<std::string> textNode = _doc.createTextNode(event.data.array.front().atom.c_str());
		eventDataElem.appendChild(textNode);
	} else if (event.data.array.size() > 1) {
		std::list<uscxml::Data>::const_iterator ptr;
		unsigned int i;

		for( i = 0 , ptr = event.data.array.begin() ;
		        ((i < event.data.array.size()) && (ptr != event.data.array.end()));
		        i++ , ptr++ ) {
			Element<std::string> eventMESElem = _doc.createElement("data");
			Text<std::string> textNode = _doc.createTextNode(ptr->atom.c_str());
			std::stringstream ss;
			ss << i;
			eventMESElem.setAttribute("id", ss.str());
			eventMESElem.appendChild(textNode);
			eventDataElem.appendChild(eventMESElem);
		}
	}

	eventElem.appendChild(eventDataElem);
	eventNodeSet.push_back(eventElem);

	// do we need to replace an existing event?
	Node<std::string> oldEventElem = _datamodel.getFirstChild();
	while(oldEventElem) {
		if (oldEventElem.getNodeType() == Node_base::ELEMENT_NODE) {
			if (HAS_ATTR_CAST(oldEventElem, "id") && iequals(ATTR_CAST(oldEventElem, "id"), "_event"))
				break;
		}
		oldEventElem = oldEventElem.getNextSibling();
	}

	if (oldEventElem) {
		_datamodel.replaceChild(eventElem, oldEventElem);
	} else {
		_datamodel.appendChild(eventElem);
	}
	_varResolver.setVariable("_event", eventNodeSet);
}

Data XPathDataModel::getStringAsData(const std::string& content) {
	Data data;
	XPathValue<std::string> result = _xpath.evaluate_expr(content, _doc);

	std::stringstream ss;

	switch (result.type()) {
	case ANY:
		break;
	case Arabica::XPath::BOOL:
		ss << result.asBool();
		break;
	case NUMBER:
		ss << result.asNumber();
		break;
	case STRING:
		ss << result.asString();
		break;
	case NODE_SET:
		NodeSet<std::string> ns = result.asNodeSet();
		for (size_t i = 0; i < ns.size(); i++) {
			ss.str("");
			ss << i;
			std::string idx = ss.str();
			ss.str("");
			ss << ns[i];
			data.compound[idx] = Data(ss.str(), Data::INTERPRETED);
		}
		data.type = Data::INTERPRETED;
		return data;
		break;
	}

	data.atom = ss.str();
	data.type = Data::VERBATIM;
	return data;
}

bool XPathDataModel::validate(const std::string& location, const std::string& schema) {
	return true;
}

bool XPathDataModel::isLocation(const std::string& expr) {
	return true;
}

uint32_t XPathDataModel::getLength(const std::string& expr) {
//	std::cout << _datamodel << std::endl;
	XPathValue<std::string> result = _xpath.evaluate_expr(expr, _doc);
	switch(result.type()) {
	case NUMBER:
		return result.asNumber();
		break;
	case NODE_SET:
		return result.asNodeSet().size();
		break;
	default:
		ERROR_EXECUTION_THROW("'" + expr + "' does not evaluate to an array.");
	}
	return 0;
}

void XPathDataModel::setForeach(const std::string& item,
                                const std::string& array,
                                const std::string& index,
                                uint32_t iteration) {

	XPathValue<std::string> arrayResult = _xpath.evaluate_expr(array, _doc);
	assert(arrayResult.type() == NODE_SET);

#if 0
	std::cout << "Array Size: " << arrayResult.asNodeSet().size() << std::endl;
	for (size_t i = 0; i < arrayResult.asNodeSet().size(); i++) {
		std::cout << arrayResult.asNodeSet()[i] << std::endl;
	}
#endif

	assert(arrayResult.asNodeSet().size() >= iteration);


	NodeSet<std::string> arrayNodeSet;
	arrayNodeSet.push_back(arrayResult.asNodeSet()[iteration]);

	if (!isDeclared(item)) {
		if (!isValidIdentifier(item))
			ERROR_EXECUTION_THROW("Expression '" + item + "' not a valid identifier.");
		Element<std::string> container = _doc.createElement("data");
		container.setAttribute("id", item);
		container.appendChild(arrayResult.asNodeSet()[iteration].cloneNode(true));
		_datamodel.appendChild(container);
		_varResolver.setVariable(item, arrayNodeSet);
	}
	XPathValue<std::string> itemResult = _varResolver.resolveVariable("", item);
	assign(itemResult, arrayNodeSet, Element<std::string>());

	if (index.length() > 0) {
		NodeSet<std::string> indexNodeSet;
		Text<std::string> indexElem = _doc.createTextNode(toStr(iteration));
		indexNodeSet.push_back(indexElem);

		if (!isDeclared(index)) {
			Element<std::string> container = _doc.createElement("data");
			container.setAttribute("id", index);
			container.appendChild(indexElem);
			_datamodel.appendChild(container);

			NodeSet<std::string> indexVarNodeSet;
			indexVarNodeSet.push_back(container);
			_varResolver.setVariable(index, indexVarNodeSet);
		}
		XPathValue<std::string> indexResult = _varResolver.resolveVariable("", index);
		assign(indexResult, indexNodeSet, Element<std::string>());
	}


#if 0
	std::cout << _datamodel << std::endl << std::endl;
	std::cout << "Index: " << indexResult.asNodeSet().size() << std::endl;
	for (size_t i = 0; i < indexResult.asNodeSet().size(); i++) {
		std::cout << indexResult.asNodeSet()[i] << std::endl;
	}
	std::cout << std::endl;
#endif


}

bool XPathDataModel::isValidIdentifier(const std::string& identifier) {
	if(boost::starts_with(identifier, "."))
		return false;

	return true;
}


void XPathDataModel::eval(const Arabica::DOM::Element<std::string>& scriptElem,
                          const std::string& expr) {
	XPathValue<std::string> result = _xpath.evaluate_expr(expr, _doc);
}

bool XPathDataModel::isDeclared(const std::string& expr) {
	return true;
	try {
		return _varResolver.isDeclared(expr) || evalAsBool(expr);
	} catch(...) {
		return false;
	}
}

bool XPathDataModel::evalAsBool(const std::string& expr) {
	return evalAsBool(Arabica::DOM::Element<std::string>(), expr);
}

bool XPathDataModel::evalAsBool(const Arabica::DOM::Element<std::string>& node, const std::string& expr) {
//	std::cout << std::endl << evalAsString(expr);
	XPathValue<std::string> result;
	try {
		result = _xpath.evaluate_expr(expr, _doc);
	} catch(SyntaxException e) {
		ERROR_EXECUTION_THROW(e.what());
	} catch(std::runtime_error e) {
		ERROR_EXECUTION_THROW(e.what());
	}
	return result.asBool();
}

std::string XPathDataModel::evalAsString(const std::string& expr) {

	XPathValue<std::string> result;
	try {
		result = _xpath.evaluate_expr(expr, _doc);
	} catch(SyntaxException e) {
		ERROR_EXECUTION_THROW(e.what());
	} catch(std::runtime_error e) {
		ERROR_EXECUTION_THROW(e.what());
	}
	switch (result.type()) {
	case STRING:
		return result.asString();
		break;
	case Arabica::XPath::BOOL: // MSVC croaks with ambiguous symbol without qualified name
		return (result.asBool() ? "true" : "false");
		break;
	case NUMBER:
		return toStr(result.asNumber());
		break;
	case NODE_SET: {
		NodeSet<std::string> nodeSet = result.asNodeSet();
		std::stringstream ss;
		for (size_t i = 0; i < nodeSet.size(); i++) {
			ss << nodeSet[i];
			if (nodeSet[i].getNodeType() != Node_base::TEXT_NODE) {
				ss << std::endl;
			}
		}
		return ss.str();
		break;
	}
	case ANY:
		ERROR_EXECUTION_THROW("Type ANY not supported to evaluate as string");
		break;
	}
	return "undefined";
}

double XPathDataModel::evalAsNumber(const std::string& expr) {
	XPathValue<std::string> result = _xpath.evaluate_expr(expr, _doc);
	return result.asNumber();
}

void XPathDataModel::assign(const Element<std::string>& assignElem,
                            const Node<std::string>& node,
                            const std::string& content) {
	std::string location;
	if (HAS_ATTR(assignElem, "id")) {
		location = ATTR(assignElem, "id");
	} else if (HAS_ATTR(assignElem, "location")) {
		location = ATTR(assignElem, "location");
	}

	// test 326ff
	XPathValue<std::string> key = _xpath.evaluate_expr(location, _doc);
#ifdef VERBOSE
	LOG(INFO) << "Key XPath : " << key.asString();
#endif
#if 0
	if (key.type() == NODE_SET) {
		try {
			for (size_t i = 0; i < key.asNodeSet().size(); i++) {
				Node<std::string> node = key.asNodeSet()[i];
				if (node == _varResolver.resolveVariable("", "_ioprocessors").asNodeSet()[0])
					ERROR_EXECUTION_THROW("Cannot assign _ioProcessors");
				if (node == _varResolver.resolveVariable("", "_sessionid").asNodeSet()[0])
					ERROR_EXECUTION_THROW("Cannot assign _sessionid");
				if (node == _varResolver.resolveVariable("", "_name").asNodeSet()[0])
					ERROR_EXECUTION_THROW("Cannot assign _name");
				if (node == _varResolver.resolveVariable("", "_event").asNodeSet()[0])
					ERROR_EXECUTION_THROW("Cannot assign _event");
			}
		} catch (Event e) {}
	}
#endif
	NodeSet<std::string> nodeSet;
	if (node) {
		Node<std::string> data = node;
		while (data) {
			// do not add empty text as a node
			if (data.getNodeType() == Node_base::TEXT_NODE) {
				std::string trimmed = data.getNodeValue();
				boost::trim(trimmed);
				if (trimmed.length() == 0) {
					data = data.getNextSibling();
					continue;
				}
			}
			nodeSet.push_back(data);
			data = data.getNextSibling();
		}
		assign(key, nodeSet, assignElem);
	} else if (content.length() > 0) {
		Text<std::string> textNode = _doc.createTextNode(spaceNormalize(content));
		nodeSet.push_back(textNode);
		assign(key, nodeSet, assignElem);
	} else if (HAS_ATTR(assignElem, "expr")) {
		XPathValue<std::string> value = _xpath.evaluate_expr(ATTR(assignElem, "expr"), _doc);
#ifdef VERBOSE
		LOG(INFO) << "Value XPath : " << value.asString();
#endif
		assign(key, value, assignElem);
	} else {
		LOG(ERROR) << "assign element has no content";
	}

//	std::cout << _datamodel << std::endl;
}

void XPathDataModel::assign(const std::string& location, const Data& data) {
	XPathValue<std::string> locationResult = _xpath.evaluate_expr(location, _doc);
	NodeSet<std::string> dataNodeSet = dataToNodeSet(data);
	assign(locationResult, dataNodeSet, Element<std::string>());
//	std::cout << _datamodel << std::endl;
}

NodeSet<std::string> XPathDataModel::dataToNodeSet(const Data& data) {
	NodeSet<std::string> dataNodeSet;
	if (data.atom.length() > 0) {
		dataNodeSet.push_back(_doc.createTextNode(data.atom));
	}
	return dataNodeSet;
}

void XPathDataModel::init(const Element<std::string>& dataElem,
                          const Node<std::string>& node,
                          const std::string& content) {
	std::string location;
	if (HAS_ATTR(dataElem, "id")) {
		location = ATTR(dataElem, "id");
	} else if (HAS_ATTR(dataElem, "location")) {
		location = ATTR(dataElem, "location");
	}

	NodeSet<std::string> nodeSet;
	if (node || (content.length() > 0)) {
		_datamodel.appendChild(_doc.importNode(dataElem, true));
		nodeSet.push_back(dataElem);
	} else if (HAS_ATTR(dataElem, "expr")) {
		try {
			Element<std::string> container = _doc.createElement("data");
			container.setAttribute("id", location);
			XPathValue<std::string> expr = _xpath.evaluate_expr(ATTR(dataElem, "expr"), _doc);
			switch (expr.type()) {
			case NODE_SET: {
				for (size_t i = 0; i < expr.asNodeSet().size(); i++) {
					container.appendChild(expr.asNodeSet()[i].cloneNode(true));
					nodeSet.push_back(expr.asNodeSet()[i].cloneNode(true));
				}
				break;
			}
			case STRING:
				container.appendChild(_doc.createTextNode(expr.asString()));
				nodeSet.push_back(_doc.createTextNode(expr.asString()));
				break;
			case NUMBER: {
				container.appendChild(_doc.createTextNode(toStr(expr.asNumber())));
				nodeSet.push_back(_doc.createTextNode(toStr(expr.asNumber())));
				break;
			}
			case Arabica::XPath::BOOL:
			case ANY:
				ERROR_EXECUTION_THROW("expr evaluates to type ANY");
			}
			_datamodel.appendChild(container);
		} catch (SyntaxException e) {
			ERROR_EXECUTION_THROW(e.what());
		}
	} else {
		LOG(ERROR) << "data element has no content";
	}

	_varResolver.setVariable(location, nodeSet);
}

void XPathDataModel::init(const std::string& location, const Data& data) {
	NodeSet<std::string> nodeSet;
	_varResolver.setVariable(location, nodeSet);
}


void XPathDataModel::assign(const XPathValue<std::string>& key,
                            const XPathValue<std::string>& value,
                            const Element<std::string>& assignElem) {
	switch (key.type()) {
	case NODE_SET:
		if (key.asNodeSet().size() == 0) {
			ERROR_EXECUTION_THROW("key for assign is empty nodeset");
		}
		switch (value.type()) {
		case STRING:
			assign(key.asNodeSet(), value.asString(), assignElem);
			break;
		case Arabica::XPath::BOOL:
			assign(key.asNodeSet(), value.asBool(), assignElem);
			break;
		case NUMBER:
			assign(key.asNodeSet(), value.asNumber(), assignElem);
			break;
		case NODE_SET:
			assign(key.asNodeSet(), value.asNodeSet(), assignElem);
			break;
		case ANY:
			ERROR_EXECUTION_THROW("Type ANY as key for assign not supported");
		}
		break;
	case STRING:
	case Arabica::XPath::BOOL:
	case NUMBER:
	case ANY:
		ERROR_EXECUTION_THROW("Type ANY as key for assign not supported")
		break;
	}
}

void XPathDataModel::assign(const XPathValue<std::string>& key,
                            const NodeSet<std::string>& value,
                            const Element<std::string>& assignElem) {
	if (value.size() == 0 || !value[0])
		return;
	switch (key.type()) {
	case NODE_SET: {
		assign(key.asNodeSet(), value, assignElem);
		break;
	}
	case STRING:
	case Arabica::XPath::BOOL:
	case NUMBER:
	case ANY:
		ERROR_EXECUTION_THROW("Type ANY as key for assign not supported")
	}
}

void XPathDataModel::assign(const NodeSet<std::string>& key,
                            const std::string& value,
                            const Element<std::string>& assignElem) {
	if (key.size() == 0)
		return;
	for (size_t i = 0; i < key.size(); i++) {
		Node<std::string> node = key[i];
		switch (node.getNodeType()) {
		case Node_base::ATTRIBUTE_NODE: {
			Attr<std::string> attr(node);
			attr.setValue(value);
			break;
		}
		case Node_base::TEXT_NODE: {
			Text<std::string> text(node);
			text.setNodeValue(value);
			break;
		}
		case Node_base::ELEMENT_NODE: {
			Element<std::string> element(node);
			if (HAS_ATTR(assignElem, "type") && iequals(ATTR(assignElem, "type"), "addattribute")) {
				// addattribute: Add an attribute with the name specified by 'attr'
				// and value specified by 'expr' to the node specified by 'location'.
				if (!HAS_ATTR(assignElem, "attr"))
					ERROR_EXECUTION_THROW("Assign element is missing 'attr'");
				element.setAttribute(ATTR(assignElem, "attr"), value);
			} else {
				/// test 547
				while(element.hasChildNodes())
					element.removeChild(element.getChildNodes().item(0));
				Text<std::string> text = _doc.createTextNode(value);
				element.appendChild(text);
			}
			break;
		}
		default:
			ERROR_EXECUTION_THROW("Unsupported node type with assign");
			break;
		}
	}
}

void XPathDataModel::assign(const NodeSet<std::string>& key,
                            const double value,
                            const Element<std::string>& assignElem) {
	assign(key, toStr(value), assignElem);
}

void XPathDataModel::assign(const NodeSet<std::string>& key,
                            const bool value,
                            const Element<std::string>& assignElem) {
}

void XPathDataModel::assign(const NodeSet<std::string>& key,
                            const NodeSet<std::string>& value,
                            const Element<std::string>& assignElem) {
	if (key.size() == 0)
		return;
	if (value.size() == 0 || !value[0])
		return;

	for (size_t i = 0; i < key.size(); i++) {
		switch (key[i].getNodeType())
		case Node_base::ELEMENT_NODE: {
		assign(Element<std::string>(key[i]), value, assignElem);
		break;
		default:
//			std::cout << key[i].getNodeType() << std::endl;
			ERROR_EXECUTION_THROW("Unsupported node type for assign");
			break;
		}
	}
}

void XPathDataModel::assign(const Element<std::string>& key,
                            const NodeSet<std::string>& value,
                            const Element<std::string>& assignElem) {
	Element<std::string> element(key);
	if (value.size() == 0 || !value[0])
		return;

	if (false) {
	} else if (assignElem && HAS_ATTR(assignElem, "type") && iequals(ATTR(assignElem, "type"), "firstchild")) {
		// firstchild: Insert the value specified by 'expr' before all of the children at 'location'.
		for (size_t i = value.size(); i; i--) {
			Node<std::string> importedNode = (value[i-1].getOwnerDocument() == _doc ? value[i-1].cloneNode(true) : _doc.importNode(value[i-1], true));
			element.insertBefore(importedNode, element.getFirstChild());
		}
	} else if (assignElem && HAS_ATTR(assignElem, "type") && iequals(ATTR(assignElem, "type"), "lastchild")) {
		// lastchild: Insert the value specified by 'expr' after all of the children at 'location'.
		for (size_t i = 0; i < value.size(); i++) {
			Node<std::string> importedNode = (value[i].getOwnerDocument() == _doc ? value[i].cloneNode(true) : _doc.importNode(value[i], true));
			element.appendChild(importedNode);
		}
	} else if (assignElem && HAS_ATTR(assignElem, "type") && iequals(ATTR(assignElem, "type"), "previoussibling")) {
		// previoussibling: Insert the value specified by 'expr' before the
		// node specified by 'location', keeping the same parent.
		Node<std::string> parent = element.getParentNode();
		if (!parent)
			ERROR_EXECUTION_THROW("Node has no parent");
		for (size_t i = 0; i < value.size(); i++) {
			Node<std::string> importedNode = (value[i].getOwnerDocument() == _doc ? value[i].cloneNode(true) : _doc.importNode(value[i], true));
			parent.insertBefore(importedNode, element);
		}
	} else if (assignElem && HAS_ATTR(assignElem, "type") && iequals(ATTR(assignElem, "type"), "nextsibling")) {
		// nextsibling: Insert the value specified by 'expr' after the node
		// specified by 'location', keeping the same parent.
		Node<std::string> parent = element.getParentNode();
		if (!parent)
			ERROR_EXECUTION_THROW("Node has no parent");
		for (size_t i = value.size(); i; i--) {
			Node<std::string> importedNode = (value[i-1].getOwnerDocument() == _doc ? value[i-1].cloneNode(true) : _doc.importNode(value[i-1], true));
			Node<std::string> nextSibling = element.getNextSibling();
			if (nextSibling) {
				parent.insertBefore(importedNode, element.getNextSibling());
			} else {
				parent.appendChild(importedNode);
			}
		}
	} else if (assignElem && HAS_ATTR(assignElem, "type") && iequals(ATTR(assignElem, "type"), "replace")) {
		// replace: Replace the node specified by 'location' by the value specified by 'expr'.
		Node<std::string> parent = element.getParentNode();
		if (!parent)
			ERROR_EXECUTION_THROW("Node has no parent");
		if (value.size() != 1)
			ERROR_EXECUTION_THROW("Value not singular");
		Node<std::string> importedNode = (value[0].getOwnerDocument() == _doc ? value[0].cloneNode(true) : _doc.importNode(value[0], true));
		parent.replaceChild(importedNode, element);
	} else if (assignElem && HAS_ATTR(assignElem, "type") && iequals(ATTR(assignElem, "type"), "delete")) {
		// delete: Delete the node specified by 'location'. ('expr' is ignored.).
		Node<std::string> parent = element.getParentNode();
		if (!parent)
			ERROR_EXECUTION_THROW("Node has no parent");
		parent.removeChild(element);
	} else {
		// replacechildren: Replace all the children at 'location' with the value specified by 'expr'.
		while(element.hasChildNodes())
			element.removeChild(element.getChildNodes().item(0));
		for (size_t i = 0; i < value.size(); i++) {
			Node<std::string> importedNode = element.getOwnerDocument().importNode(value[i], true);
			element.appendChild(importedNode);
		}
	}
}

XPathValue<std::string>
NodeSetVariableResolver::resolveVariable(const std::string& namepaceUri,
        const std::string& name) const {
	std::map<std::string, NodeSet<std::string> >::const_iterator n = _variables.find(name);
	if(n == _variables.end()) {
		ERROR_EXECUTION_THROW("No variable named '" + name + "'");
	}
#if VERBOSE
	std::cout << std::endl << "Getting " << name << ":" << std::endl;
	for (size_t i = 0; i < n->second.size(); i++) {
		std::cout << n->second[i].getNodeType() << " | " << n->second[i] << std::endl;
	}
	std::cout << std::endl;
#endif
	return XPathValue<std::string>(new NodeSetValue<std::string>(n->second));
}

void NodeSetVariableResolver::setVariable(const std::string& name, const NodeSet<std::string>& value) {
#if VERBOSE
	std::cout << std::endl << "Setting " << name << ":" << std::endl;
	for (size_t i = 0; i < value.size(); i++) {
		std::cout << value[i].getNodeType() << " | " << value[i] << std::endl;
	}
	std::cout << std::endl;
#endif
	_variables[name] = value;
#if 0
	std::map<std::string, Arabica::XPath::NodeSet<std::string> >::iterator varIter =  _variables.begin();
	while (varIter != _variables.end()) {
		std::cout << varIter->first << ":" << std::endl;
		for (size_t i = 0; i < varIter->second.size(); i++) {
			std::cout << varIter->second[i].getNodeType() << " | " << varIter->second[i] << std::endl;
		}
		varIter++;
	}
#endif
}

bool NodeSetVariableResolver::isDeclared(const std::string& name) {
#if 0
	std::map<std::string, Arabica::XPath::NodeSet<std::string> >::iterator varIter =  _variables.begin();
	while (varIter != _variables.end()) {
		std::cout << varIter->first << std::endl;
		varIter++;
	}
#endif
	return _variables.find(name) != _variables.end();
}

XPathFunction<std::string>*
XPathFunctionResolver::resolveFunction(const std::string& namespace_uri,
                                       const std::string& name,
                                       const std::vector<XPathExpression<std::string> >& argExprs) const {
	if (iequals(name, "in")) {
		return new XPathFunctionIn(1, -1, argExprs, _interpreter);
	}
	return _xpathFuncRes.resolveFunction(namespace_uri, name, argExprs);
}

std::vector<std::pair<std::string, std::string> > XPathFunctionResolver::validNames() const {
	std::vector<std::pair<std::string, std::string> > names = _xpathFuncRes.validNames();
	names.push_back(std::make_pair("", "In"));
	return names;
}

bool XPathFunctionIn::doEvaluate(const Node<std::string>& context,
                                 const ExecutionContext<std::string>& executionContext) const {
	for (size_t i = 0; i < argCount(); i++) {
		XPathValue<std::string> stateName = arg(i, context, executionContext);
		if (stateName.type() == STRING) {
			if (_interpreter->isInState(stateName.asString())) {
				continue;
			}
		}
		return false;
	}
	return true;
}

}
