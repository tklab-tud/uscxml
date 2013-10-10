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
		while (namelistIter != event.namelist.end()) {
			if (namelistIter->second.type == Data::INTERPRETED) {
				NodeSet<std::string> xpathresult = namelistIter->second.xpathres;
				NodeSet<std::string>::const_iterator nodesetIter = xpathresult.begin();
				while(nodesetIter != xpathresult.end())
					eventDataElem.appendChild(*nodesetIter);
			} else {
				Element<std::string> eventNamelistElem = _doc.createElement("data");
				Text<std::string> eventNamelistText = _doc.createTextNode(namelistIter->second.atom);

				eventNamelistElem.setAttribute("id", namelistIter->first);
				eventNamelistElem.appendChild(eventNamelistText);
				eventDataElem.appendChild(eventNamelistElem);
				namelistIter++;
			}
		}
	}
	if (event.raw.size() > 0) {
		Element<std::string> eventRawElem = _doc.createElement("raw");
		Text<std::string> textNode = _doc.createTextNode(event.raw.c_str());
		eventRawElem.appendChild(textNode);
		eventElem.appendChild(eventRawElem);
	}

	if (event.content.size() > 0) {
		Text<std::string> textNode = _doc.createTextNode(Interpreter::spaceNormalize(event.content).c_str());
		eventDataElem.appendChild(textNode);
	}
	if (event.dom) {
//		Node<std::string> importedNode = _doc.importNode(event.getFirstDOMElement(), true);
		Node<std::string> importedNode = _doc.importNode(event.dom, true);
		eventDataElem.appendChild(importedNode);
	}
	if (!event.data.atom.empty()) {
		Element<std::string> eventNamelistElem = _doc.createElement("data");
		Text<std::string> eventNamelistText = _doc.createTextNode(event.data.atom);
		eventDataElem.appendChild(eventNamelistText);
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
	XPathValue<std::string> result = _xpath.evaluate_expr(content, _doc);
	std::stringstream ss;

	Data data;
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
		data.xpathres = result.asNodeSet();
		data.type = Data::INTERPRETED;
		return data;
	}

	data.atom = ss.str();
	data.type = Data::VERBATIM;
	return data;
}

bool XPathDataModel::validate(const std::string& location, const std::string& schema) {
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
		Event exceptionEvent("error.execution", Event::PLATFORM);
		exceptionEvent.data.compound["exception"] = Data("'" + expr + "' does not evaluate to an array.", Data::VERBATIM);
		throw(exceptionEvent);
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
	for (int i = 0; i < arrayResult.asNodeSet().size(); i++) {
		std::cout << arrayResult.asNodeSet()[i] << std::endl;
	}
#endif

	assert(arrayResult.asNodeSet().size() >= iteration);


	NodeSet<std::string> arrayNodeSet;
	arrayNodeSet.push_back(arrayResult.asNodeSet()[iteration]);

	if (!isDeclared(item)) {
		if (!isValidIdentifier(item))
			throw Event("error.execution", Event::PLATFORM);
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
	for (int i = 0; i < indexResult.asNodeSet().size(); i++) {
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
	try {
		return _varResolver.isDeclared(expr) || evalAsBool(expr);
	} catch(...) {
		return false;
	}
}

bool XPathDataModel::evalAsBool(const std::string& expr) {
	std::cout << std::endl << evalAsString(expr);
	XPathValue<std::string> result;
	try {
		std::cout << std::endl << "Documento Attuale : " << std::endl << _doc << std::endl;
		std::cout << std::endl << "Attuale Datamodel : " << std::endl << _datamodel << std::endl;
		result = _xpath.evaluate_expr(expr, _doc);
	} catch(SyntaxException e) {
		throw Event("error.execution", Event::PLATFORM);
	} catch(std::runtime_error e) {
		throw Event("error.execution", Event::PLATFORM);
	}
	return result.asBool();
}

std::string XPathDataModel::evalAsString(const std::string& expr) {

	XPathValue<std::string> result;
	try {
		result = _xpath.evaluate_expr(expr, _doc);
	} catch(SyntaxException e) {
		throw Event("error.execution", Event::PLATFORM);
	} catch(std::runtime_error e) {
		throw Event("error.execution", Event::PLATFORM);
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
		for (int i = 0; i < nodeSet.size(); i++) {
			ss << nodeSet[i];
			if (nodeSet[i].getNodeType() != Node_base::TEXT_NODE) {
				ss << std::endl;
			}
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
                            const Node<std::string>& node,
                            const std::string& content) {
	std::string location;
	if (HAS_ATTR(assignElem, "id")) {
		location = ATTR(assignElem, "id");
	} else if (HAS_ATTR(assignElem, "location")) {
		location = ATTR(assignElem, "location");
	}

	// test 326ff
	std::cout << std::endl <<  "!!!!!!! Current Datamodel!: " << _datamodel;
	XPathValue<std::string> key = _xpath.evaluate_expr(location, _datamodel);
#if 0
	if (key.type() == NODE_SET) {
		try {
			for (int i = 0; i < key.asNodeSet().size(); i++) {
				Node<std::string> node = key.asNodeSet()[i];
				if (node == _varResolver.resolveVariable("", "_ioprocessors").asNodeSet()[0])
					throw Event("error.execution", Event::PLATFORM);
				if (node == _varResolver.resolveVariable("", "_sessionid").asNodeSet()[0])
					throw Event("error.execution", Event::PLATFORM);
				if (node == _varResolver.resolveVariable("", "_name").asNodeSet()[0])
					throw Event("error.execution", Event::PLATFORM);
				if (node == _varResolver.resolveVariable("", "_event").asNodeSet()[0])
					throw Event("error.execution", Event::PLATFORM);
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
		Text<std::string> textNode = _doc.createTextNode(Interpreter::spaceNormalize(content));
		nodeSet.push_back(textNode);
		assign(key, nodeSet, assignElem);
	} else if (HAS_ATTR(assignElem, "expr")) {
		XPathValue<std::string> value = _xpath.evaluate_expr(ATTR(assignElem, "expr"), _datamodel);
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

	Element<std::string> container = _doc.createElement("data");
	container.setAttribute("id", location);

	if (node) {
		Node<std::string> data = node;
		while (data) {
			Node<std::string> dataClone = _doc.importNode(data, true);
			container.appendChild(dataClone);
			data = data.getNextSibling();
		}
	} else if (content.length() > 0) {
		Text<std::string> textNode = _doc.createTextNode(Interpreter::spaceNormalize(content));
		container.appendChild(textNode);
	} else if (HAS_ATTR(dataElem, "expr")) {
		try {
			XPathValue<std::string> expr = _xpath.evaluate_expr(ATTR(dataElem, "expr"), _doc);
			switch (expr.type()) {
			case NODE_SET: {
				for (int i = 0; i < expr.asNodeSet().size(); i++) {
					container.appendChild(expr.asNodeSet()[i].cloneNode(true));
				}
				break;
			}
			case STRING:
				container.appendChild(_doc.createTextNode(expr.asString()));
				break;
			case NUMBER: {
				container.appendChild(_doc.createTextNode(toStr(expr.asNumber())));
				break;
			}
			case Arabica::XPath::BOOL:
			case ANY:
				throw Event("error.execution", Event::PLATFORM);
			}
		} catch (SyntaxException e) {
			throw Event("error.execution", Event::PLATFORM);
		}
	} else {
		LOG(ERROR) << "data element has no content";
	}
	_datamodel.appendChild(container);

	// put data element into nodeset and bind to xpath variable
	NodeSet<std::string> nodeSet;
#if 0
	nodeSet.push_back(container);
#else
	Node<std::string> child = container.getFirstChild();
	while(child) {
		nodeSet.push_back(child);
		child = child.getNextSibling();
	}
#endif
	_varResolver.setVariable(location, nodeSet);

//	std::cout << _datamodel << std::endl;
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
		if (key.asNodeSet().size() == 0) {
			throw Event("error.execution", Event::PLATFORM);
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
			throw Event("error.execution", Event::PLATFORM);
		}
		break;
	}
	case STRING:
	case Arabica::XPath::BOOL:
	case NUMBER:
	case ANY:
		throw Event("error.execution", Event::PLATFORM);
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
	if (value.size() == 0 || !value[0])
		return;

	for (int i = 0; i < key.size(); i++) {
		switch (key[i].getNodeType()) {
		case Node_base::ELEMENT_NODE: {
			assign(Element<std::string>(key[i]), value, assignElem);
			break;
		}
		default:
//			std::cout << key[i].getNodeType() << std::endl;
			throw Event("error.execution", Event::PLATFORM);
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
	} else if (assignElem && HAS_ATTR(assignElem, "type") && boost::iequals(ATTR(assignElem, "type"), "firstchild")) {
		// firstchild: Insert the value specified by 'expr' before all of the children at 'location'.
		for (int i = value.size(); i; i--) {
			Node<std::string> importedNode = (value[i-1].getOwnerDocument() == _doc ? value[i-1].cloneNode(true) : _doc.importNode(value[i-1], true));
			element.insertBefore(importedNode, element.getFirstChild());
		}
	} else if (assignElem && HAS_ATTR(assignElem, "type") && boost::iequals(ATTR(assignElem, "type"), "lastchild")) {
		// lastchild: Insert the value specified by 'expr' after all of the children at 'location'.
		for (int i = 0; i < value.size(); i++) {
			Node<std::string> importedNode = (value[i].getOwnerDocument() == _doc ? value[i].cloneNode(true) : _doc.importNode(value[i], true));
			element.appendChild(importedNode);
		}
	} else if (assignElem && HAS_ATTR(assignElem, "type") && boost::iequals(ATTR(assignElem, "type"), "previoussibling")) {
		// previoussibling: Insert the value specified by 'expr' before the
		// node specified by 'location', keeping the same parent.
		Node<std::string> parent = element.getParentNode();
		if (!parent)
			throw Event("error.execution", Event::PLATFORM);
		for (int i = 0; i < value.size(); i++) {
			Node<std::string> importedNode = (value[i].getOwnerDocument() == _doc ? value[i].cloneNode(true) : _doc.importNode(value[i], true));
			parent.insertBefore(importedNode, element);
		}
	} else if (assignElem && HAS_ATTR(assignElem, "type") && boost::iequals(ATTR(assignElem, "type"), "nextsibling")) {
		// nextsibling: Insert the value specified by 'expr' after the node
		// specified by 'location', keeping the same parent.
		Node<std::string> parent = element.getParentNode();
		if (!parent)
			throw Event("error.execution", Event::PLATFORM);
		for (int i = value.size(); i; i--) {
			Node<std::string> importedNode = (value[i-1].getOwnerDocument() == _doc ? value[i-1].cloneNode(true) : _doc.importNode(value[i-1], true));
			Node<std::string> nextSibling = element.getNextSibling();
			if (nextSibling) {
				parent.insertBefore(importedNode, element.getNextSibling());
			} else {
				parent.appendChild(importedNode);
			}
		}
	} else if (assignElem && HAS_ATTR(assignElem, "type") && boost::iequals(ATTR(assignElem, "type"), "replace")) {
		// replace: Replace the node specified by 'location' by the value specified by 'expr'.
		Node<std::string> parent = element.getParentNode();
		if (!parent)
			throw Event("error.execution", Event::PLATFORM);
		if (value.size() != 1)
			throw Event("error.execution", Event::PLATFORM);
		Node<std::string> importedNode = (value[0].getOwnerDocument() == _doc ? value[0].cloneNode(true) : _doc.importNode(value[0], true));
		parent.replaceChild(importedNode, element);
	} else if (assignElem && HAS_ATTR(assignElem, "type") && boost::iequals(ATTR(assignElem, "type"), "delete")) {
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
			Node<std::string> importedNode = (value[i].getOwnerDocument() == _doc ? value[i].cloneNode(true) : _doc.importNode(value[i], true));
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
#if VERBOSE
	std::cout << std::endl << "Getting " << name << ":" << std::endl;
	for (int i = 0; i < n->second.size(); i++) {
		std::cout << n->second[i].getNodeType() << " | " << n->second[i] << std::endl;
	}
	std::cout << std::endl;
#endif
	return XPathValue<std::string>(new NodeSetValue<std::string>(n->second));
}

void NodeSetVariableResolver::setVariable(const std::string& name, const NodeSet<std::string>& value) {
#if VERBOSE
	std::cout << std::endl << "Setting " << name << ":" << std::endl;
	for (int i = 0; i < value.size(); i++) {
		std::cout << value[i].getNodeType() << " | " << value[i] << std::endl;
	}
	std::cout << std::endl;
#endif
	_variables[name] = value;
#if 0
	std::map<std::string, Arabica::XPath::NodeSet<std::string> >::iterator varIter =  _variables.begin();
	while (varIter != _variables.end()) {
		std::cout << varIter->first << ":" << std::endl;
		for (int i = 0; i < varIter->second.size(); i++) {
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