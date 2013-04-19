#include "uscxml/Common.h"
#include "XPathDataModel.h"

#include "uscxml/Message.h"
#include <glog/logging.h>

#ifdef BUILD_AS_PLUGINS
#include <Pluma/Connector.hpp>
#endif

namespace uscxml {

using namespace Arabica::XPath;
using namespace Arabica::DOM;

#ifdef BUILD_AS_PLUGINS
PLUMA_CONNECTOR
bool connect(pluma::Host& host) {
	host.add( new XPathDataModelProvider() );
	return true;
}
#endif

XPathDataModel::XPathDataModel() {
}

boost::shared_ptr<DataModelImpl> XPathDataModel::create(InterpreterImpl* interpreter) {
	boost::shared_ptr<XPathDataModel> dm = boost::shared_ptr<XPathDataModel>(new XPathDataModel());
	dm->_interpreter = interpreter;

//	dm->_xpath->setVariableCompileTimeResolver(_varCTResolver);
//	dm->_xpath->setNamespaceContext(interpreter->getNSContext());

	dm->_funcResolver.setInterpreter(interpreter);
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
	sessIdNodeSet.push_back(sessIdElem);
	dm->_varResolver.setVariable("_sessionid", sessIdNodeSet);


	Element<std::string> nameElem = dm->_doc.createElement("data");
	nameElem.setAttribute("id", "_name");
	Text<std::string> nameText = dm->_doc.createTextNode(interpreter->getName());
	nameElem.appendChild(nameText);
	dm->_datamodel.appendChild(nameElem);

	NodeSet<std::string> nameNodeSet;
	nameNodeSet.push_back(nameElem);
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
	if (event.params.size() > 0) {
		std::multimap<std::string, std::string>::const_iterator paramIter = event.params.begin();
		while(paramIter != event.params.end()) {
			Element<std::string> eventParamElem = _doc.createElement("data");
			Text<std::string> eventParamText = _doc.createTextNode(paramIter->second);

			eventParamElem.setAttribute("id", paramIter->first);
			eventParamElem.appendChild(eventParamText);
			eventDataElem.appendChild(eventParamElem);
			paramIter++;
		}
	}
	if (event.namelist.size() > 0) {
		std::map<std::string, std::string>::const_iterator namelistIter = event.namelist.begin();
		while(namelistIter != event.namelist.end()) {
			Element<std::string> eventNamelistElem = _doc.createElement("data");
			Text<std::string> eventNamelistText = _doc.createTextNode(namelistIter->second);

			eventNamelistElem.setAttribute("id", namelistIter->first);
			eventNamelistElem.appendChild(eventNamelistText);
			eventDataElem.appendChild(eventNamelistElem);
			namelistIter++;
		}
	}
	if (event.content.size() > 0) {
		Text<std::string> textNode = _doc.createTextNode(Interpreter::spaceNormalize(event.content).c_str());
		eventDataElem.appendChild(textNode);
	}
	if (event.dom) {
		Node<std::string> importedNode = _doc.importNode(event.dom.getFirstChild(), true);
		eventDataElem.appendChild(importedNode);
	}

	eventElem.appendChild(eventDataElem);
	eventNodeSet.push_back(eventElem);

	// do we need to replace an existing event?
	Node<std::string> oldEventElem = _datamodel.getFirstChild();
	while(oldEventElem) {
		if (oldEventElem.getNodeType() == Node_base::ELEMENT_NODE) {
			if (HAS_ATTR(oldEventElem, "id") && boost::iequals(ATTR(oldEventElem, "id"), "_event"))
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
	return data;
}

bool XPathDataModel::validate(const std::string& location, const std::string& schema) {
	return true;
}

uint32_t XPathDataModel::getLength(const std::string& expr) {
	std::cout << _datamodel << std::endl;
	XPathValue<std::string> result = _xpath.evaluate_expr(expr, _doc);
	switch(result.type()) {
		case NUMBER:
			return result.asNumber();
			break;
		case NODE_SET:
			return result.asNodeSet().size();
			break;
		default:
			throw Event("error.execution", Event::PLATFORM);
	}
	return 0;
}

void XPathDataModel::eval(const std::string& expr) {
	XPathValue<std::string> result = _xpath.evaluate_expr(expr, _doc);
}

bool XPathDataModel::isDeclared(const std::string& expr) {
	try {
		return evalAsBool(expr);
	} catch(...) {
		return false;
	}
}

bool XPathDataModel::evalAsBool(const std::string& expr) {
	XPathValue<std::string> result = _xpath.evaluate_expr(expr, _doc);
	return result.asBool();
}

std::string XPathDataModel::evalAsString(const std::string& expr) {
	XPathValue<std::string> result = _xpath.evaluate_expr(expr, _doc);
	switch (result.type()) {
	case STRING:
		return result.asString();
		break;
	case BOOL:
		return (result.asBool() ? "true" : "false");
		break;
	case NUMBER:
		return toStr(result.asNumber());
		break;
	case NODE_SET: {
		NodeSet<std::string> nodeSet = result.asNodeSet();
		std::stringstream ss;
		for (int i = 0; i < nodeSet.size(); i++) {
			ss << nodeSet[i] << std::endl;
		}
		return ss.str();
		break;
	}
	case ANY:
		throw Event("error.execution", Event::PLATFORM);
		break;
	}
	return "undefined";
}

double XPathDataModel::evalAsNumber(const std::string& expr) {
	XPathValue<std::string> result = _xpath.evaluate_expr(expr, _doc);
	return result.asNumber();
}

void XPathDataModel::assign(const Element<std::string>& assignElem,
                            const Document<std::string>& doc,
                            const std::string& content) {
	std::string location;
	if (HAS_ATTR(assignElem, "id")) {
		location = ATTR(assignElem, "id");
	} else if (HAS_ATTR(assignElem, "location")) {
		location = ATTR(assignElem, "location");
	}

	XPathValue<std::string> key = _xpath.evaluate_expr(location, _doc);
	NodeSet<std::string> nodeSet;
	if (doc) {
		nodeSet.push_back(doc.getDocumentElement());
		assign(key, nodeSet, assignElem);
	} else if (content.length() > 0) {
		Text<std::string> textNode = _doc.createTextNode(Interpreter::spaceNormalize(content));
		nodeSet.push_back(textNode);
		assign(key, nodeSet, assignElem);
	} else if (HAS_ATTR(assignElem, "expr")) {
		XPathValue<std::string> value = _xpath.evaluate_expr(ATTR(assignElem, "expr"), _doc);
		assign(key, value, assignElem);
	} else {
		LOG(ERROR) << "assign element has no content";
	}

//	std::cout << _datamodel << std::endl;
}

void XPathDataModel::assign(const std::string& location, const Data& data) {

}

void XPathDataModel::init(const Element<std::string>& dataElem,
                          const Document<std::string>& doc,
                          const std::string& content) {
	std::string location;
	if (HAS_ATTR(dataElem, "id")) {
		location = ATTR(dataElem, "id");
	} else if (HAS_ATTR(dataElem, "location")) {
		location = ATTR(dataElem, "location");
	}

	Element<std::string> container = _doc.createElement("data");
	container.setAttribute("id", location);
	if (doc) {
		if (doc.getDocumentElement()) {
			Node<std::string> data = doc.getDocumentElement().getFirstChild();
			while (data) {
				Node<std::string> dataClone = _doc.importNode(data, true);
				container.appendChild(dataClone);
				data = data.getNextSibling();
			}
		}
	} else if (content.length() > 0) {
		Text<std::string> textNode = _doc.createTextNode(Interpreter::spaceNormalize(content));
		container.appendChild(textNode);
	} else if (HAS_ATTR(dataElem, "expr")) {
		XPathValue<std::string> expr = _xpath.evaluate_expr(ATTR(dataElem, "expr"), _doc);
		XPathValue<std::string> key = _xpath.evaluate_expr(location, _doc);
		assign(key, expr, dataElem);
		for (int i = 0; expr.asNodeSet().size(); i++)
			container.appendChild(expr.asNodeSet()[i]);
	} else {
		LOG(ERROR) << "data element has no content";
	}
	_datamodel.appendChild(container);

	// put data element into nodeset and bind to xpath variable
	NodeSet<std::string> nodeSet;
	nodeSet.push_back(container);
	_varResolver.setVariable(location, nodeSet);

	std::cout << _datamodel << std::endl;
}

void XPathDataModel::init(const std::string& location, const Data& data) {
	NodeSet<std::string> nodeSet;
	_varResolver.setVariable(location, nodeSet);
}


void XPathDataModel::assign(const XPathValue<std::string>& key,
                            const XPathValue<std::string>& value,
                            const Element<std::string>& assignElem) {
	switch (key.type()) {
		case NODE_SET: {
			switch (value.type()) {
				case STRING:
					assign(key.asNodeSet(), value.asString(), assignElem);
					break;
				case BOOL:
					assign(key.asNodeSet(), value.asBool(), assignElem);
					break;
				case NUMBER:
					assign(key.asNodeSet(), value.asNumber(), assignElem);
					break;
				case NODE_SET:
					assign(key.asNodeSet(), value.asNodeSet(), assignElem);
					break;
				case ANY:
					throw Event("error.execution", Event::PLATFORM);
			}
			break;
		}
		case STRING:
		case BOOL:
		case NUMBER:
		case ANY:
			throw Event("error.execution", Event::PLATFORM);
	}
}

void XPathDataModel::assign(const XPathValue<std::string>& key,
														const NodeSet<std::string>& value,
														const Element<std::string>& assignElem) {
	switch (key.type()) {
		case NODE_SET: {
			assign(key.asNodeSet(), value, assignElem);
			break;
		}
		case STRING:
		case BOOL:
		case NUMBER:
		case ANY:
			throw Event("error.execution", Event::PLATFORM);
	}
}

void XPathDataModel::assign(const NodeSet<std::string>& key,
                            const std::string& value,
                            const Element<std::string>& assignElem) {
	if (key.size() == 0)
		return;
	for (int i = 0; i < key.size(); i++) {
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
			if (HAS_ATTR(assignElem, "type") && boost::iequals(ATTR(assignElem, "type"), "addattribute")) {
				// addattribute: Add an attribute with the name specified by 'attr'
				// and value specified by 'expr' to the node specified by 'location'.
				if (!HAS_ATTR(assignElem, "attr"))
					throw Event("error.execution", Event::PLATFORM);
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
			throw Event("error.execution", Event::PLATFORM);
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

	for (int i = 0; i < key.size(); i++) {
		switch (key[i].getNodeType()) {
		case Node_base::ELEMENT_NODE: {
			assign(Element<std::string>(key[i]), value, assignElem);
			break;
		}
		default:
			throw Event("error.execution", Event::PLATFORM);
			break;
		}
	}
}

void XPathDataModel::assign(const Element<std::string>& key,
														const NodeSet<std::string>& value,
														const Element<std::string>& assignElem) {
	Element<std::string> element(key);
	if (false) {
	} else if (HAS_ATTR(assignElem, "type") && boost::iequals(ATTR(assignElem, "type"), "firstchild")) {
		// firstchild: Insert the value specified by 'expr' before all of the children at 'location'.
		for (int i = value.size(); i; i--) {
			Node<std::string> importedNode = _doc.importNode(value[i-1], true);
			element.insertBefore(importedNode, element.getFirstChild());
		}
	} else if (HAS_ATTR(assignElem, "type") && boost::iequals(ATTR(assignElem, "type"), "lastchild")) {
		// lastchild: Insert the value specified by 'expr' after all of the children at 'location'.
		for (int i = 0; i < value.size(); i++) {
			Node<std::string> importedNode = _doc.importNode(value[i], true);
			element.appendChild(importedNode);
		}
	} else if (HAS_ATTR(assignElem, "type") && boost::iequals(ATTR(assignElem, "type"), "previoussibling")) {
		// previoussibling: Insert the value specified by 'expr' before the
		// node specified by 'location', keeping the same parent.
		Node<std::string> parent = element.getParentNode();
		if (!parent)
			throw Event("error.execution", Event::PLATFORM);
		for (int i = 0; i < value.size(); i++) {
			Node<std::string> importedNode = _doc.importNode(value[i], true);
			parent.insertBefore(importedNode, element);
		}
	} else if (HAS_ATTR(assignElem, "type") && boost::iequals(ATTR(assignElem, "type"), "nextsibling")) {
		// nextsibling: Insert the value specified by 'expr' after the node
		// specified by 'location', keeping the same parent.
		Node<std::string> parent = element.getParentNode();
		if (!parent)
			throw Event("error.execution", Event::PLATFORM);
		for (int i = value.size(); i; i--) {
			Node<std::string> importedNode = _doc.importNode(value[i-1], true);
			Node<std::string> nextSibling = element.getNextSibling();
			if (nextSibling) {
				parent.insertBefore(importedNode, element.getNextSibling());
			} else {
				parent.appendChild(importedNode);
			}
		}
	} else if (HAS_ATTR(assignElem, "type") && boost::iequals(ATTR(assignElem, "type"), "replace")) {
		// replace: Replace the node specified by 'location' by the value specified by 'expr'.
		Node<std::string> parent = element.getParentNode();
		if (!parent)
			throw Event("error.execution", Event::PLATFORM);
		if (value.size() != 1)
			throw Event("error.execution", Event::PLATFORM);
		Node<std::string> importedNode = _doc.importNode(value[0], true);
		parent.replaceChild(importedNode, element);
	} else if (HAS_ATTR(assignElem, "type") && boost::iequals(ATTR(assignElem, "type"), "delete")) {
		// delete: Delete the node specified by 'location'. ('expr' is ignored.).
		Node<std::string> parent = element.getParentNode();
		if (!parent)
			throw Event("error.execution", Event::PLATFORM);
		parent.removeChild(element);
	} else {
		// replacechildren: Replace all the children at 'location' with the value specified by 'expr'.
		while(element.hasChildNodes())
			element.removeChild(element.getChildNodes().item(0));
		for (int i = 0; i < value.size(); i++) {
			Node<std::string> importedNode = _doc.importNode(value[i], true);
			element.appendChild(importedNode);
		}
	}
}

XPathValue<std::string>
NodeSetVariableResolver::resolveVariable(const std::string& namepaceUri,
        const std::string& name) const {
	std::map<std::string, NodeSet<std::string> >::const_iterator n = _variables.find(name);
	if(n == _variables.end()) {
		throw Event("error.execution");
	}
	return XPathValue<std::string>(new NodeSetValue<std::string>(n->second));
}

XPathFunction<std::string>*
XPathFunctionResolver::resolveFunction(const std::string& namespace_uri,
                                       const std::string& name,
                                       const std::vector<XPathExpression<std::string> >& argExprs) const {
	if (boost::iequals(name, "in")) {
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
	for (int i = 0; i < argCount(); i++) {
		XPathValue<std::string> stateName = arg(i, context, executionContext);
		if (stateName.type() == STRING) {
			if (!Interpreter::isMember(_interpreter->getState(stateName.asString()), _interpreter->getConfiguration())) {
				return false;
			}
		}
	}
	return true;
}

}