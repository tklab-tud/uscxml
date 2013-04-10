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
//	dm->_xpath.setVariableResolver(_varResolver);
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
		eventDataElem.setNodeValue(event.content);
	}
	
	eventElem.appendChild(eventDataElem);
	eventNodeSet.push_back(eventElem);
	
//	std::cout << eventElem << std::endl;
	
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
  return 0;
}

void XPathDataModel::eval(const std::string& expr) {
	XPathValue<std::string> result = _xpath.evaluate_expr(expr, _doc);
}

bool XPathDataModel::isDeclared(const std::string& expr) {
	return true;
}

bool XPathDataModel::evalAsBool(const std::string& expr) {
	XPathValue<std::string> result = _xpath.evaluate_expr(expr, _doc);
	return result.asBool();
}

std::string XPathDataModel::evalAsString(const std::string& expr) {
	XPathValue<std::string> result = _xpath.evaluate_expr(expr, _doc);
	return result.asString();
}

double XPathDataModel::evalAsNumber(const std::string& expr) {
	XPathValue<std::string> result = _xpath.evaluate_expr(expr, _doc);
	return result.asNumber();
}

void XPathDataModel::assign(const std::string& location,
														const Document<std::string>& doc,
														const Arabica::DOM::Element<std::string>& dataElem) {
	XPathValue<std::string> key = _xpath.evaluate_expr(location, _doc);
	NodeSet<std::string> nodeSet;
	nodeSet.push_back(doc.getDocumentElement());
	assign(key, nodeSet, dataElem);
}

void XPathDataModel::assign(const std::string& location,
														const Data& data,
														const Arabica::DOM::Element<std::string>& dataElem) {
//	assert(false);
//	std::cout << location << " = " << data << std::endl;
}

void XPathDataModel::assign(const std::string& location,
														const std::string& expr,
														const Arabica::DOM::Element<std::string>& dataElem) {
	std::string realExpr = (HAS_ATTR(dataElem, "expr") ? ATTR(dataElem, "expr") : expr);
	XPathValue<std::string> key = _xpath.evaluate_expr(location, _doc);
	XPathValue<std::string> value = _xpath.evaluate_expr(realExpr, _doc);
	assign(key, value, dataElem);
}

void XPathDataModel::init(const std::string& location,
													const Document<std::string>& doc,
													const Arabica::DOM::Element<std::string>& dataElem) {
	Element<std::string> container = _doc.createElement("data");
	container.setAttribute("id", location);
	Element<std::string> data = doc.getDocumentElement();
	if (data.hasChildNodes()) {
		Node<std::string> dataClone = _doc.importNode(data, true);
		container.appendChild(dataClone);
	}
	_datamodel.appendChild(container);
	
	// put data element into nodeset and bind to xpath variable
	NodeSet<std::string> nodeSet;
	nodeSet.push_back(container);
	_varResolver.setVariable(location, nodeSet);
}

void XPathDataModel::init(const std::string& location,
													const std::string& expr,
													const Arabica::DOM::Element<std::string>& dataElem) {
	Element<std::string> data = _doc.createElement("data");
	data.setAttribute("id", location);
	
	if (expr.length() > 0) {
		Text<std::string> textNode = _doc.createTextNode(expr.c_str());
		data.appendChild(textNode);
		_datamodel.appendChild(data);
	}

	// put data element into nodeset and bind to xpath variable
	NodeSet<std::string> nodeSet;
	nodeSet.push_back(data);
	_varResolver.setVariable(location, nodeSet);
}

void XPathDataModel::init(const std::string& location,
													const Data& data,
													const Arabica::DOM::Element<std::string>& dataElem) {
	assert(false);
}

void XPathDataModel::assign(XPathValue<std::string>& key,
														const XPathValue<std::string>& value,
														const Arabica::DOM::Element<std::string>& assignElem) {
	switch (value.type()) {
		case STRING:
			assign(key, value.asString(), assignElem);
			break;
		case BOOL:
			assign(key, value.asBool(), assignElem);
			break;
		case NUMBER:
			assign(key, value.asNumber(), assignElem);
			break;
		case NODE_SET:
			assign(key, value.asNodeSet(), assignElem);
			break;
		case ANY:
			throw Event("error.execution", Event::PLATFORM);
	}
}

void XPathDataModel::assign(XPathValue<std::string>& key,
														const std::string& value,
														const Arabica::DOM::Element<std::string>& assignElem) {
	switch (key.type()) {
		case NODE_SET: {
			if (key.asNodeSet().size() == 0)
				return;
			Node<std::string> node = key.asNodeSet()[0];
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
					}
					break;
				}
				default:
					throw Event("error.execution", Event::PLATFORM);
					break;
			}
			break;
		}
		case STRING:
		case BOOL:
		case NUMBER:
		case ANY:
			throw Event("error.execution", Event::PLATFORM);
			break;
		default:
			break;
	}
}

void XPathDataModel::assign(XPathValue<std::string>& key,
														const double value,
														const Arabica::DOM::Element<std::string>& assignElem) {
}

void XPathDataModel::assign(XPathValue<std::string>& key,
														const bool value,
														const Arabica::DOM::Element<std::string>& assignElem) {
}

void XPathDataModel::assign(XPathValue<std::string>& key,
														const NodeSet<std::string>& value,
														const Arabica::DOM::Element<std::string>& assignElem) {
	switch (key.type()) {
		case NODE_SET: {
			if (key.asNodeSet().size() == 0)
				return;
			Node<std::string> node = key.asNodeSet()[0];
			switch (node.getNodeType()) {
				case Node_base::ELEMENT_NODE: {
					Element<std::string> element(node);
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
					break;
				}
				default:
					throw Event("error.execution", Event::PLATFORM);
					break;
			}
			break;
		}
		case STRING:
		case BOOL:
		case NUMBER:
		case ANY:
			throw Event("error.execution", Event::PLATFORM);
			break;
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