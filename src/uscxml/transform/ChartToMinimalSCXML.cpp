/**
 *  @file
 *  @author     2012-2014 Stefan Radomski (stefan.radomski@cs.tu-darmstadt.de)
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

#include "uscxml/transform/ChartToMinimalSCXML.h"
#include "uscxml/transform/FlatStateIdentifier.h"
#include "uscxml/Convenience.h"
#include "uscxml/Factory.h"

#include <DOM/io/Stream.hpp>
#include <glog/logging.h>

#include <iostream>

namespace uscxml {

using namespace Arabica::XPath;
using namespace Arabica::DOM;

Transformer ChartToMinimalSCXML::transform(const Interpreter& other) {
	return boost::shared_ptr<TransformerImpl>(new ChartToMinimalSCXML(other));
}

ChartToMinimalSCXML::ChartToMinimalSCXML(const Interpreter& other) : TransformerImpl(), _retainAsComments(false), _step(1) {
	cloneFrom(other.getImpl());

	// a bit messy but needed for SCXML IO Processor with session id target
	_selfPtr = boost::shared_ptr<InterpreterImpl>(this, Deleter());
	Interpreter::addInstance(_selfPtr);
}

void ChartToMinimalSCXML::writeTo(std::ostream& stream) {

	addMonitor(this);

	{
		NodeSet<std::string> allElements = DOMUtils::filterChildType(Node_base::ELEMENT_NODE, _scxml, true);
		size_t nrElements = 0;
		for (int i = 0; i < allElements.size(); i++) {
			if (!isInEmbeddedDocument(allElements[i]))
				nrElements++;
		}
		std::cerr << "Number of elements before reduction: " << nrElements + 1 << std::endl;
	}

	// test 278 - move embedded datas to topmost datamodel
	if (_binding == EARLY) {
		// move all data elements into topmost datamodel element
		NodeSet<std::string> datas = DOMUtils::filterChildElements(_nsInfo.xmlNSPrefix + "data", _scxml, true);

		if (datas.size() > 0) {
			Node<std::string> topMostDatamodel;
			NodeSet<std::string> datamodels = DOMUtils::filterChildElements(_nsInfo.xmlNSPrefix + "datamodel", _scxml, false);
			if (datamodels.size() > 0) {
				topMostDatamodel = datamodels[0];
			} else {
				topMostDatamodel = _document.createElementNS(_nsInfo.nsURL, "datamodel");
				_scxml.insertBefore(topMostDatamodel, _scxml.getFirstChild());
			}

			while(topMostDatamodel.hasChildNodes())
				topMostDatamodel.removeChild(topMostDatamodel.getFirstChild());

			for (int i = 0; i < datas.size(); i++) {
				if (!isInEmbeddedDocument(datas[i])) {
					topMostDatamodel.appendChild(datas[i]);
				}
			}
		}
	}

	char* waitForEnv = getenv("USCXML_MINIMIZE_WAIT_MS");
	_retainAsComments = envVarIsTrue("USCXML_MINIMIZE_RETAIN_AS_COMMENTS");

	long waitFor = -1;

	if (waitForEnv != NULL) {
		try {
			waitFor = strTo<long>(waitForEnv);
		} catch (...) {
			waitFor = 0;
		}
	}

	if (envVarIsTrue("USCXML_MINIMIZE_WAIT_FOR_COMPLETION")) {
		interpret();
	} else {
		start();
		if (waitFor < 0) {
			// wait for EOF / CTRL+D
			char c;
			while(true) {
				std::cin >> c;
				if(std::cin.eof())
					break;
			}
		} else {
			tthread::this_thread::sleep_for(tthread::chrono::milliseconds(waitFor));
		}
	}
	stop();

	removeUnvisited(_scxml);

	{
		NodeSet<std::string> allElements = DOMUtils::filterChildType(Node_base::ELEMENT_NODE, _scxml, true);
		size_t nrElements = 0;
		for (int i = 0; i < allElements.size(); i++) {
			if (!isInEmbeddedDocument(allElements[i]))
				nrElements++;
		}
		std::cerr << "Number of elements after reduction: " << nrElements + 1 << std::endl;
	}

	// unset data model
	_dmCopy = DataModel();

	stream << _scxml;
}

void ChartToMinimalSCXML::removeUnvisited(Arabica::DOM::Node<std::string>& node) {
	if (node.getNodeType() != Node_base::ELEMENT_NODE)
		return;

	Element<std::string> elem(node);

	if (isInEmbeddedDocument(elem) ||
	        (TAGNAME(elem) == _nsInfo.xmlNSPrefix + "param") ||
	        (TAGNAME(elem) == _nsInfo.xmlNSPrefix + "donedata") ||
	        (TAGNAME(elem) == _nsInfo.xmlNSPrefix + "datamodel") ||
	        (TAGNAME(elem) == _nsInfo.xmlNSPrefix + "data") ||
	        (TAGNAME(elem) == _nsInfo.xmlNSPrefix + "content")) {
		return;
	}

	// special handling for conditional blocks with if
	if (TAGNAME(elem) == _nsInfo.xmlNSPrefix + "if") {
		NodeSet<std::string> ifChilds = DOMUtils::filterChildType(Node_base::ELEMENT_NODE, elem, false);
		Element<std::string> lastConditional = elem;
		bool hadVisitedChild = false;
		for (int j = 0; j < ifChilds.size(); j++) {
			Element<std::string> ifChildElem(ifChilds[j]);
			if (TAGNAME(ifChildElem) == _nsInfo.xmlNSPrefix + "else" || TAGNAME(ifChildElem) == _nsInfo.xmlNSPrefix + "elseif") {
				if (!hadVisitedChild && HAS_ATTR(lastConditional, "cond")) {
					lastConditional.setAttribute("cond", "false");
				}
				lastConditional = ifChildElem;
				hadVisitedChild = false;
			}
			if (_visited.find(ifChildElem) != _visited.end()) {
				_visited.insert(lastConditional);
				hadVisitedChild = true;
			}
		}
	}

	// test344
	if (_dmCopy &&
	        TAGNAME(elem) == _nsInfo.xmlNSPrefix + "transition" &&
	        HAS_ATTR(elem, "cond") &&
	        !_dmCopy.isValidSyntax(ATTR(elem, "cond")))
		return;

	// detach unvisited nodes from DOM
	if (_visited.find(node) == _visited.end()) {
		std::cerr << DOMUtils::xPathForNode(node) << std::endl;
		if (_retainAsComments) {
			std::stringstream oldContent;
			oldContent << node;
			node.getParentNode().replaceChild(_document.createComment(boost::replace_all_copy(oldContent.str(),"--", "-")), node);
		} else {
			// removeChildren is not working as expected
//			node.getParentNode().replaceChild(_document.createTextNode(""), node);
			node.getParentNode().removeChild(node);
		}
		return;
	}

	// iterate and remove unvisited children
	NodeList<std::string> children = node.getChildNodes();
	for (int i = 0; i < children.getLength(); i++) {
		Node<std::string> child(children.item(i));
		removeUnvisited(child);
	}
}

void ChartToMinimalSCXML::markAsVisited(const Arabica::DOM::Element<std::string>& element) {
	if (_visited.find(element) != _visited.end())
		return;

	Arabica::DOM::Element<std::string> elem = const_cast<Arabica::DOM::Element<std::string>&>(element);

	_visited.insert(element);
	Node<std::string> parent = element.getParentNode();
	if (parent && parent.getNodeType() == Node_base::ELEMENT_NODE) {
		Arabica::DOM::Element<std::string> parentElem(parent);
		markAsVisited(parentElem);
	}
}

void ChartToMinimalSCXML::beforeExecutingContent(Interpreter interpreter, const Arabica::DOM::Element<std::string>& element) {
	markAsVisited(element);
	StateTransitionMonitor::beforeExecutingContent(interpreter, element);
}

void ChartToMinimalSCXML::beforeUninvoking(Interpreter interpreter, const Arabica::DOM::Element<std::string>& invokeElem, const std::string& invokeid) {
	markAsVisited(invokeElem);
}

void ChartToMinimalSCXML::beforeTakingTransition(Interpreter interpreter, const Arabica::DOM::Element<std::string>& transition, bool moreComing) {
	NodeSet<std::string> targets = getTargetStates(transition);
	// we need this for history pseudo states
	for (int i = 0; i < targets.size(); i++) {
		markAsVisited(Arabica::DOM::Element<std::string>(targets[i]));
	}
	markAsVisited(transition);

	std::stringstream commentSS;
	if (HAS_ATTR(transition, "event")) {
		commentSS << " Step #" << _step++ << " - transition taken for event '" << _currEvent.name << "' ";
	} else {
		commentSS << " Step #" << _step++ << " - spontaneous transition taken ";
	}
	if (envVarIsTrue("USCXML_ANNOTATE_PROGRESS"))
		transition.getParentNode().insertBefore(_document.createComment(commentSS.str()), transition);

	StateTransitionMonitor::beforeTakingTransition(interpreter, transition, moreComing);
}

void ChartToMinimalSCXML::beforeEnteringState(Interpreter interpreter, const Arabica::DOM::Element<std::string>& state, bool moreComing) {
	markAsVisited(state);

	std::stringstream commentSS;
	commentSS << " Step #" << _step++ << " - state entered ";

	Arabica::DOM::Element<std::string> ncState = const_cast<Arabica::DOM::Element<std::string>&>(state);
	if (envVarIsTrue("USCXML_ANNOTATE_PROGRESS"))
		ncState.insertBefore(_document.createComment(commentSS.str()), ncState.getFirstChild());

	StateTransitionMonitor::beforeEnteringState(interpreter, state, moreComing);
}

void ChartToMinimalSCXML::beforeInvoking(Interpreter interpreter, const Arabica::DOM::Element<std::string>& invokeElem, const std::string& invokeid) {
	markAsVisited(invokeElem);
}

void ChartToMinimalSCXML::beforeCompletion(Interpreter interpreter) {
	_dmCopy = _dataModel; // retain a copy;
}

void ChartToMinimalSCXML::executeContent(const Arabica::DOM::Element<std::string>& content, bool rethrow) {
	markAsVisited(content);
	InterpreterRC::executeContent(content, rethrow);
}

void ChartToMinimalSCXML::invoke(const Arabica::DOM::Element<std::string>& element) {
	markAsVisited(element);
	InterpreterRC::invoke(element);
}

void ChartToMinimalSCXML::cancelInvoke(const Arabica::DOM::Element<std::string>& element) {
	markAsVisited(element);
	InterpreterRC::cancelInvoke(element);
}

void ChartToMinimalSCXML::onStableConfiguration(uscxml::Interpreter interpreter) {
}

}