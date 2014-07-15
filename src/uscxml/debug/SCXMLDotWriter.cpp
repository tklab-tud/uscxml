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

#include "uscxml/Common.h"
#include "SCXMLDotWriter.h"
#include "uscxml/DOMUtils.h"
#include <boost/algorithm/string.hpp> // replace_all
#include <iomanip>

namespace uscxml {

using namespace Arabica::DOM;

SCXMLDotWriter::SCXMLDotWriter() {
	_iteration = 0;
	_indentation = 0;
}

SCXMLDotWriter::SCXMLDotWriter(Interpreter interpreter,
                               const std::list<SCXMLDotWriter::StateAnchor>& stateAnchors,
                               const Arabica::DOM::Element<std::string>& transition) {
	_interpreter = interpreter;
	_xmlNSPrefix = _interpreter.getNameSpaceInfo().xmlNSPrefix;
	_transition = transition;
	_anchors = stateAnchors;

	if (_anchors.size() == 0) {
		NodeList<std::string > scxmlElems = interpreter.getDocument().getElementsByTagName("scxml");

		StateAnchor anchor;
		anchor.element = (Arabica::DOM::Element<std::string>)scxmlElems.item(0);
		_anchors.push_back(anchor);
	}

	for (std::list<StateAnchor>::iterator anchIter = _anchors.begin(); anchIter != _anchors.end(); anchIter++) {
		if (!anchIter->element) {
			NodeList<std::string > scxmlElems = interpreter.getDocument().getElementsByTagName("scxml");
			anchIter->element = (Arabica::DOM::Element<std::string>)scxmlElems.item(0);
		}
		assembleGraph(anchIter->element, anchIter->depth);
	}

	_iteration = 0;
	_indentation = 0;
}

SCXMLDotWriter::~SCXMLDotWriter()	{

}

void SCXMLDotWriter::onStableConfiguration(Interpreter interpreter) {
	std::ostringstream fileSS;
	fileSS << interpreter.getName() << "." << std::setw(6) << std::setfill('0') << _iteration++ << ".dot";
	toDot(fileSS.str(), interpreter);
}

void SCXMLDotWriter::afterCompletion(Interpreter interpreter) {
	std::ostringstream fileSS;
	fileSS << interpreter.getName() << "." << std::setw(6) << std::setfill('0') << _iteration++ << ".dot";
	toDot(fileSS.str(), interpreter);
}

void SCXMLDotWriter::beforeMicroStep(Interpreter interpreter) {
//	std::ostringstream fileSS;
//	fileSS << interpreter.getName() << "." << std::setw(6) << std::setfill('0') << _iteration++ << ".dot";
//	toDot(fileSS.str(), interpreter);
}

void SCXMLDotWriter::beforeTakingTransition(Interpreter interpreter,
        const Arabica::DOM::Element<std::string>& transition,
        bool moreComing) {
	std::ostringstream fileSS;
	fileSS << interpreter.getName() << "." << std::setw(6) << std::setfill('0') << _iteration++ << ".dot";
	toDot(fileSS.str(), interpreter, transition);
}

std::string SCXMLDotWriter::getPrefix() {
	std::string prefix = "";
	for (int i = 0; i < _indentation; i++)
		prefix += "  ";
	return prefix;
}

void SCXMLDotWriter::writeTo(std::ostream& os) {
	os << "digraph {" << std::endl;
	os << "  rankdir=TB;" << std::endl;
	os << "  fontsize=10;" << std::endl;
	//		outfile << "  splines=ortho;" << std::endl;
	//		outfile << "  splines=false;" << std::endl;
	//		outfile << "  nodesep=1.0;" << std::endl;

	_indentation++;
	for (std::list<SCXMLDotWriter::StateAnchor>::iterator anchIter = _anchors.begin();
	        anchIter != _anchors.end(); anchIter++) {
		writeStateElement(os, _graph[idForNode(anchIter->element)]);
	}
	_indentation--;


	os << "}" << std::endl;

}

void SCXMLDotWriter::toDot(const std::string& filename,
                           Interpreter interpreter,
                           const std::list<SCXMLDotWriter::StateAnchor>& stateAnchors,
                           const Arabica::DOM::Element<std::string>& transition) {

	std::ofstream outfile(filename.c_str());
	SCXMLDotWriter writer(interpreter, stateAnchors, transition);
	writer.writeTo(outfile);

}

void SCXMLDotWriter::assembleGraph(const Arabica::DOM::Element<std::string>& state, uint32_t depth) {
	std::string nodeId = idForNode(state);

	// been here
	if (_graph.find(nodeId) != _graph.end())
		return;

	if (depth == 0) {
		_graph[nodeId].isBorder = true;
	}

	if (ATTR(state, "id") == "WiFiOff") {
		assert(true);
	}

	_graph[nodeId].node = state;

	if (depth == 0)
		return;

	Arabica::XPath::NodeSet<std::string> childElems = InterpreterImpl::filterChildType(Arabica::DOM::Node_base::ELEMENT_NODE, state);
	for (int i = 0; i < childElems.size(); i++) {
		Arabica::DOM::Element<std::string> childElem(childElems[i]);

		if (iequals(TAGNAME(childElem), "history")) {
			_histories[ATTR(childElem, "id")] = ATTR(state, "id") + ":" + ATTR(childElem, "id");
		}

		if (iequals(TAGNAME(childElem), "transition")) {
			Arabica::XPath::NodeSet<std::string> targetStates = _interpreter.getImpl()->getTargetStates(childElem);
			for (int j = 0; j < targetStates.size(); j++) {
				std::string remoteNodeId = idForNode(targetStates[j]);
				_graph[nodeId].targets.insert(std::make_pair(remoteNodeId, childElem));

				// recurse along the transition targets
				assembleGraph((Arabica::DOM::Element<std::string>)targetStates[j], depth - 1);
			}
			if (targetStates.size() == 0)
				_graph[nodeId].targets.insert(std::make_pair(nodeId, childElem));

			std::list<std::string> eventNames;
			if (HAS_ATTR(childElem, "event"))
				eventNames = InterpreterImpl::tokenizeIdRefs(ATTR(childElem, "event"));
			if (eventNames.size() == 0)
				_graph[nodeId].events.insert(std::make_pair("", childElem));
			for (std::list<std::string>::iterator evIter = eventNames.begin(); evIter != eventNames.end(); evIter++) {
				_graph[nodeId].events.insert(std::make_pair(*evIter, childElem));
			}
		}

		if (InterpreterImpl::isState(Element<std::string>(childElem))) {
			// add to initial states if it is initial
			if (_interpreter.getImpl()->isInitial(Element<std::string>(childElem))) {
				_graph[nodeId].initialchilds.insert(idForNode(childElem));
			} else if (_interpreter.getImpl()->isParallel(Element<std::string>(state))) {
				_graph[nodeId].initialchilds.insert(idForNode(childElem));
			}
			// in any case, it is a child state
			_graph[nodeId].childs.insert(idForNode(childElem));

			// recurse
			assembleGraph(childElem, depth - 1);
		}


	}
}

void SCXMLDotWriter::writeStateElement(std::ostream& os, const DotState& state) {
	const Arabica::DOM::Element<std::string>& stateElem = state.node;
	std::string stateId = idForNode(stateElem);

	if (_knownIds.find(stateId) != _knownIds.end())
		return;
	_knownIds.insert(stateId);

	bool subgraph = InterpreterImpl::isCompound(stateElem) || InterpreterImpl::isParallel(stateElem);
	if (subgraph) {
		_indentation++;
		os << std::endl;
		os << getPrefix() << "subgraph \"cluster_" << stateId << "\" {" << std::endl;
		_indentation++;
		os << getPrefix() << "fontsize=14" << std::endl;
		os << getPrefix() << "label=<<b>";
		if (InterpreterImpl::isCompound(stateElem)) {
			os << "Compound: ";
		} else {
			os << "Parallel: ";
		}
		os << nameForNode(stateElem) << "</b>>" << std::endl;
//		os << getPrefix() << "rank=\"same\"" << std::endl;
		os << getPrefix() << "labeljust=l" << std::endl;
//		os << getPrefix() << "ranksep=\"equally\"" << std::endl;

	}

	os << std::endl;
	os << getPrefix() << "\"" << stateId << "\" [" << std::endl;
	_indentation++;

	os << getPrefix() << "fontsize=10," << std::endl;
	os << getPrefix() << "shape=plaintext," << std::endl;

	// is the current state in the basic configuration?
	if (InterpreterImpl::isMember(stateElem, _interpreter.getBasicConfiguration()))
		os << getPrefix() << "color=red, penwidth=3," << std::endl;

	// is the current state in the basic configuration?
	if (state.isBorder)
		os << getPrefix() << "color=blue," << std::endl;

	// is this state final?
	if (_interpreter.getImpl()->isFinal(stateElem)) {
		os << getPrefix() << "shape=doublecircle," << std::endl;
		os << getPrefix() << "color=black," << std::endl;
		os << getPrefix() << "penwidth=2," << std::endl;
		os << getPrefix() << "label=<" << nameForNode(stateElem) << ">" << std::endl;
		_indentation--;
		os << getPrefix() << "];" << std::endl;
		return;
	}

	// is the state initial?
	bool isInitial = _interpreter.getImpl()->isInitial(stateElem);
//	if (isInitial)
//		os << getPrefix() << "style=filled, fillcolor=lightgrey, " << std::endl;

	DotState::mmap_s_e_t::const_iterator destIterF, destIterB;
	std::list<std::string> outPorts; // count unique keys
#if PER_EVENT_TRANS
	// count unique event names
	for(DotState::mmap_s_e_t::const_iterator it = state.events.begin(), end = state.events.end();
	        it != end;
	        it = state.events.upper_bound(it->first)) {
		outPorts.push_back(it->first);
	}
#else
	// count unique adjecent nodes
	for(DotState::mmap_s_e_t::const_iterator it = state.targets.begin(), end = state.targets.end();
	        it != end;
	        it = state.targets.upper_bound(it->first)) {
		outPorts.push_back(it->first);
	}
#endif

	os << getPrefix() << "label = < " << std::endl;

	/*
		<table cellborder="1" border="0" cellspacing="0" cellpadding="2" style="rounded">
			<tr><td port="name" rowspan="4"><b>step</b></td></tr>
			<tr><td port="foo.error.port" align="right">foo.error.port</td></tr>
			<tr><td port="bar" align="right">bar</td></tr>
			<tr><td port="baz" align="right">baz</td></tr>
		</table>
	 */

	std::string details = getDetailedLabel(stateElem);

	os << "<table " << (isInitial ? "bgcolor=\"orange\" " : "") << "cellborder=\"1\" border=\"0\" cellspacing=\"0\" cellpadding=\"2\" >" << std::endl;
	os << "  <tr><td port=\"__name\" rowspan=\"" << outPorts.size() + 1 << "\"><b>" << nameForNode(stateElem) << "</b></td></tr>" << std::endl;
	for(std::list<std::string>::iterator nameIter = outPorts.begin(); nameIter != outPorts.end(); nameIter++) {
#ifdef PER_EVENT_TRANS
		os << "  <tr><td port=\"" << portEscape(*nameIter) << "\" align=\"right\">" << *nameIter << "</td></tr>" << std::endl;
#else
		// gather all events that activate the transition
		std::string portName = *nameIter;

//		std::cout << ATTR(stateElem, "id") << std::endl;

		if (ATTR(stateElem, "id") == "ConfirmQuit") {
			assert(true);
		}

		std::multimap<std::string, std::string> eventConds; // event to condition
		std::pair <DotState::mmap_s_e_t::const_iterator, DotState::mmap_s_e_t::const_iterator> targetKeyRange = state.targets.equal_range(portName);
		for (destIterB = targetKeyRange.first;  destIterB != targetKeyRange.second;  ++destIterB) {
			const Arabica::DOM::Element<std::string>& transElem = destIterB->second;
			std::list<std::string> eventNames = InterpreterImpl::tokenizeIdRefs(ATTR(transElem, "event"));
			for (std::list<std::string>::iterator eventIter = eventNames.begin(); eventIter != eventNames.end(); eventIter++) {
				eventConds.insert(std::make_pair(*eventIter, ATTR(transElem, "cond")));
			}
			if (eventNames.size() == 0) {
				// spontaneous transition
				eventConds.insert(std::make_pair("&#8709;", ATTR(transElem, "cond")));
			}
		}

		typedef std::multimap<std::string, std::string>::iterator condIter_t;
		std::stringstream outPortSS;
		outPortSS << "<b>" << portName << "</b><br align=\"right\" />";

		std::string opener = "{";
		std::string closer;
		std::string seperator;
		condIter_t iterA, iterB;
		for(iterA = eventConds.begin(); iterA != eventConds.end(); iterA = iterB) {
			std::string eventName = iterA->first;
			bool hasCondition = false;

			std::pair <condIter_t, condIter_t> condRange = eventConds.equal_range(eventName);
			for (iterB = condRange.first;  iterB != condRange.second;  ++iterB) {
				hasCondition = true;
			}

			outPortSS << opener << seperator << eventName << (hasCondition ? "" : "");
			seperator = ", ";
			opener = "";
			closer = "}";
		}
		outPortSS << closer;

		os << "  <tr><td port=\"" << portEscape(portName) << "\" align=\"right\">" << outPortSS.str() << "</td></tr>" << std::endl;

#endif
	}

	if (details.size() > 0) {
		os << "  <tr><td colspan=\"" << (outPorts.size() == 0 ? 1 : 2) << "\">" << std::endl;
		os << details << std::endl;
		os << "  </td></tr>" << std::endl;
	}

	Arabica::XPath::NodeSet<std::string> histories = InterpreterImpl::filterChildElements(_xmlNSPrefix + "history", stateElem);
	for (int i = 0; i < histories.size(); i++) {
		os << "  <tr><td port=\"" << ATTR(histories[i], "id") << "\" colspan=\"" << (outPorts.size() == 0 ? 1 : 2) << "\"><b>history: </b>" << ATTR(histories[i], "id") << "</td></tr>" << std::endl;

	}

	os << "</table>" << std::endl << getPrefix() << ">" << std::endl;

	_indentation--;
	os << getPrefix() << "];" << std::endl;

	// always display childs up to the desired depth
	for (std::set<std::string>::iterator childIter = state.childs.begin(); childIter != state.childs.end(); childIter++) {
		if (_graph.find(*childIter) != _graph.end())
			writeStateElement(os, _graph[*childIter]);
	}

	if (subgraph) {
		_indentation--;
		os << getPrefix() << "} " << std::endl;
		_indentation--;
	}

#if 1
	std::string initialEdgeStyle = "style=\"dashed\", color=\"black\"";
	std::string transitionEdgeStyle = "color=black";

	for (std::set<std::string>::iterator initIter = state.initialchilds.begin(); initIter != state.initialchilds.end(); initIter++) {
		std::string destId = *initIter;
		if (_histories.find(destId) != _histories.end()) {
			os << getPrefix() << stateId << ":__name -> " << _histories[destId] << " [" << initialEdgeStyle << "]" << std::endl;
		} else if(InterpreterImpl::isFinal(_graph[destId].node)) {
			os << getPrefix() << stateId << ":__name -> " << destId << ":__name:nw [" << initialEdgeStyle << "]" << std::endl;
		} else {
			os << getPrefix() << stateId << ":__name -> " << destId << ":__name:nw [" << initialEdgeStyle << "]" << std::endl;
		}
	}

#if PER_EVENT_TRANS
	// iterate all events and make connections
	DotState::mmap_s_e_t::const_iterator destIterF, destIterB;
	for(destIterF = state.events.begin(); destIterF != state.events.end(); destIterF = destIterB) {
		std::string eventName = destIterF->first;

		// all these react to the same event
		std::pair <DotState::mmap_s_e_t::const_iterator,DotState::mmap_s_e_t::const_iterator> keyRange = state.events.equal_range(eventName);
		for (destIterB = keyRange.first;  destIterB != keyRange.second;  ++destIterB) {
			const Arabica::DOM::Element<std::string>& transElem = destIterB->second;
			Arabica::XPath::NodeSet<std::string> targetStates = _interpreter.getImpl()->getTargetStates(transElem);
			for (int i = 0; i < targetStates.size(); i++) {
				std::string destId = idForNode(targetStates[i]);
				if (_histories.find(destId) != _histories.end()) {
					os << getPrefix() << "" << stateId << ":\"" << portEscape(eventName) << "\" -> " << _histories[destId] << " [" << transitionEdgeStyle << "]" << std::endl;
				} else if(InterpreterImpl::isFinal(_graph[destId].node)) {
					os << getPrefix() << stateId << ":\"" << portEscape(eventName) << "\" -> " << destId << " [" << transitionEdgeStyle << "]" << std::endl;
				} else {
					os << getPrefix() << "" << stateId << ":\"" << portEscape(eventName) << "\" -> " << destId << ":__name [" << transitionEdgeStyle << "]" << std::endl;
				}
			}
		}
	}
#else
	// iterate all *targets* and make connections
	for(destIterF = state.targets.begin(); destIterF != state.targets.end(); destIterF = destIterB) {
		std::string eventName = destIterF->first;

		// all these react to the same event
		std::pair <DotState::mmap_s_e_t::const_iterator,DotState::mmap_s_e_t::const_iterator> keyRange = state.targets.equal_range(eventName);
		std::set<Arabica::DOM::Element<std::string> > targetSet;
		for (destIterB = keyRange.first;  destIterB != keyRange.second;  ++destIterB) {
			const Arabica::DOM::Element<std::string>& transElem = destIterB->second;
			Arabica::XPath::NodeSet<std::string> targetStates = _interpreter.getImpl()->getTargetStates(transElem);
			for (int i = 0; i < targetStates.size(); i++) {
				targetSet.insert(Arabica::DOM::Element<std::string>(targetStates[i]));
			}
		}
		for (std::set<Arabica::DOM::Element<std::string> >::iterator stateIter = targetSet.begin(); stateIter != targetSet.end(); stateIter++) {
			std::string destId = idForNode(*stateIter);
			if (_histories.find(destId) != _histories.end()) {
				os << getPrefix() << "" << stateId << ":\"" << portEscape(eventName) << "\" -> " << _histories[destId] << " [" << transitionEdgeStyle << "]" << std::endl;
			} else if(InterpreterImpl::isFinal(_graph[destId].node)) {
				os << getPrefix() << stateId << ":\"" << portEscape(eventName) << "\" -> " << destId << " [" << transitionEdgeStyle << "]" << std::endl;
			} else {
				os << getPrefix() << "" << stateId << ":\"" << portEscape(eventName) << "\" -> " << destId << ":__name [" << transitionEdgeStyle << "]" << std::endl;
			}
			writeStateElement(os, _graph[destId]);
		}
	}
#endif

#endif

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

		if (InterpreterImpl::isState(Element<std::string>(childElems.item(i))) ||
		        iequals(TAGNAME(childElems.item(i)), "transition") ||
		        iequals(TAGNAME(childElems.item(i)), "initial") ||
		        false)
			continue;

		struct ElemDetails details;
		details.name = "<b>" + TAGNAME(childElems.item(i)) + ":</b>";

		if (iequals(TAGNAME(childElems.item(i)), "history")) {
			continue;
		}

		// provide details for special elements here

		// param ---------
		if (iequals(TAGNAME(childElems.item(i)), "param")) {
			if (HAS_ATTR(childElems.item(i), "name"))
				details.name += " " + ATTR(childElems.item(i), "name") + " = ";
			if (HAS_ATTR(childElems.item(i), "expr"))
				details.name += ATTR(childElems.item(i), "expr");
			if (HAS_ATTR(childElems.item(i), "location"))
				details.name += ATTR(childElems.item(i), "location");
		}

		// data ---------
		if (iequals(TAGNAME(childElems.item(i)), "data")) {
			if (HAS_ATTR(childElems.item(i), "id"))
				details.name += " " + ATTR(childElems.item(i), "id");
			if (HAS_ATTR(childElems.item(i), "src"))
				details.name += ATTR(childElems.item(i), "src");
			if (HAS_ATTR(childElems.item(i), "expr"))
				details.name += " = " + ATTR(childElems.item(i), "expr");
			NodeList<std::string > grandChildElems = childElems.item(i).getChildNodes();
			for (int j = 0; j < grandChildElems.getLength(); j++) {
				if (grandChildElems.item(j).getNodeType() == Node_base::TEXT_NODE) {
					details.name += dotEscape(grandChildElems.item(j).getNodeValue());
				}
			}
		}

		// invoke ---------
		if (iequals(TAGNAME(childElems.item(i)), "invoke")) {
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
		if (iequals(TAGNAME(childElems.item(i)), "send")) {
			if (HAS_ATTR(childElems.item(i), "id"))
				details.name += "<br />id = " + ATTR(childElems.item(i), "id");
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

		// cancel ---------
		if (iequals(TAGNAME(childElems.item(i)), "cancel")) {
			if (HAS_ATTR(childElems.item(i), "sendid"))
				details.name += " " + ATTR(childElems.item(i), "sendid");
		}

		// script ---------
		if (iequals(TAGNAME(childElems.item(i)), "script")) {
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

		// if ---------
		if (iequals(TAGNAME(childElems.item(i)), "if")) {
			if (HAS_ATTR(childElems.item(i), "cond"))
				details.name += " cond = " + dotEscape(ATTR(childElems.item(i), "cond"));
		}

		// elseif ---------
		if (iequals(TAGNAME(childElems.item(i)), "elseif")) {
			if (HAS_ATTR(childElems.item(i), "cond"))
				details.name += " cond = " + dotEscape(ATTR(childElems.item(i), "cond"));
		}

		// log ---------
		if (iequals(TAGNAME(childElems.item(i)), "log")) {
			details.name += " ";
			if (HAS_ATTR(childElems.item(i), "label"))
				details.name += ATTR(childElems.item(i), "label") + " = ";
			if (HAS_ATTR(childElems.item(i), "expr"))
				details.name += ATTR(childElems.item(i), "expr");
		}

		// foreach ---------
		if (iequals(TAGNAME(childElems.item(i)), "foreach")) {
			if (HAS_ATTR(childElems.item(i), "item"))
				details.name += "<br />&nbsp;&nbsp;item = " + ATTR(childElems.item(i), "item");
			if (HAS_ATTR(childElems.item(i), "array"))
				details.name += "<br />&nbsp;&nbsp;array = " + ATTR(childElems.item(i), "array");
			if (HAS_ATTR(childElems.item(i), "index"))
				details.name += "<br />&nbsp;&nbsp;index = " + ATTR(childElems.item(i), "index");
		}

		// recurse
		details.content = getDetailedLabel((Arabica::DOM::Element<std::string>)childElems.item(i), indentation + 1);
		content.push_back(details);
	}

	std::stringstream ssContent;

	if (content.size() > 0) {
		ssContent << "<table cellspacing=\"2\" cellpadding=\"0\" border=\"0\" bgcolor=\"#" << colorForIndent(indentation + 1) << "\">";

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

std::string SCXMLDotWriter::portEscape(const std::string& text) {
	std::string escaped(text);
	boost::replace_all(escaped, ".", "-");

	return escaped;
}

std::string SCXMLDotWriter::dotEscape(const std::string& text) {
	std::string escaped(text);
	boost::replace_all(escaped, " ", "&nbsp;");
	boost::replace_all(escaped, "\t", "&nbsp;&nbsp;&nbsp;");
	boost::replace_all(escaped, "<", "&lt;");
	boost::replace_all(escaped, ">", "&gt;");
	boost::replace_all(escaped, "\"", "&quot;");
	boost::replace_all(escaped, "\n", "<br />");

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
		if (InterpreterImpl::isParallel(elem))
			elemName += "<i>Parallel</i><br />";
		if (elem.hasAttribute("name")) {
			elemName += elem.getAttribute("name");
		} else if (elem.hasAttribute("id")) {
			elemName += elem.getAttribute("id");
		}
	}
	if (elemName.size() == 0)
		elemName = boost::lexical_cast<std::string>(node.getLocalName());

	return elemName;

}

std::string SCXMLDotWriter::idForNode(const Arabica::DOM::Node<std::string>& node) {
	std::string elemId;

	// try to get the id as the name or id attribute
	if (node.getNodeType() == Node_base::ELEMENT_NODE) {
		Arabica::DOM::Element<std::string> elem = (Arabica::DOM::Element<std::string>)node;
		if (elem.hasAttribute("name")) {
			elemId = elem.getAttribute("name");
		} else if (elem.hasAttribute("id")) {
			elemId = elem.getAttribute("id");
		}
	}

	// no luck, create id from position in tree
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

	return elemId;
}

}