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
#include "uscxml/UUID.h"
#include "SCXMLDotWriter.h"
#include "../transform/FlatStateIdentifier.h"
#include "uscxml/DOMUtils.h"
#include <boost/algorithm/string.hpp> // replace_all
#include <iomanip>

namespace uscxml {

using namespace Arabica::DOM;
using namespace Arabica::XPath;

SCXMLDotWriter::SCXMLDotWriter() {
	_iteration = 0;
	_indentation = 0;
}

SCXMLDotWriter::SCXMLDotWriter(Interpreter interpreter,
                               const std::list<SCXMLDotWriter::StateAnchor>& stateAnchors,
                               const Element<std::string>& transition) {
	_interpreter = interpreter;
	_xmlNSPrefix = _interpreter.getNameSpaceInfo().xmlNSPrefix;
	_transition = transition;
	_anchors = stateAnchors;

	NodeList<std::string > scxmlElems = interpreter.getDocument().getElementsByTagName("scxml");
	_scxml = (Element<std::string>)scxmlElems.item(0);
	_isFlat = HAS_ATTR(_scxml, "flat") && DOMUtils::attributeIsTrue(ATTR(_scxml, "flat"));

	if (_anchors.size() == 0) {
		StateAnchor anchor;
		anchor.element = _scxml;
		_anchors.push_back(anchor);
	}

	for (std::list<StateAnchor>::iterator anchIter = _anchors.begin(); anchIter != _anchors.end(); anchIter++) {
		if (!anchIter->element)
			anchIter->element = _scxml;
		if (anchIter->childDepth >= 0 && anchIter->transDepth == -1)
			anchIter->transDepth = anchIter->childDepth;

		_portType = anchIter->type;
		assembleGraph(anchIter->element, anchIter->childDepth, anchIter->transDepth + 1);
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
        const Element<std::string>& transition,
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
	os << "  rankdir=LR;" << std::endl;
	os << "  fontsize=10;" << std::endl;
	//		outfile << "  splines=ortho;" << std::endl;
	//		outfile << "  splines=false;" << std::endl;
	//		outfile << "  nodesep=1.0;" << std::endl;

	_indentation++;
	writeStateElement(os, _scxml);

	// write edges at end of file
	for(std::set<DotEdge>::iterator edgeIter = _edges.begin(); edgeIter != _edges.end(); edgeIter++) {
		if (edgeIter->from == edgeIter->to)
			continue;
		if (_histories.find(edgeIter->to) != _histories.end()) {
			if (_histories.find(edgeIter->to)->second.from == _histories.find(edgeIter->to)->second.to)
				continue;
		}

		os << getPrefix() << "\"" << edgeIter->from << "\"";
		if (edgeIter->fromPort.size() > 0) {
			os << std::string(":\"") + edgeIter->fromPort + "\":e";
		} else {
			os << ":__name";
		}
		os << " -> ";

		if (_histories.find(edgeIter->to) != _histories.end()) {
			os << getPrefix() << "\"" << _histories.find(edgeIter->to)->second.to << "\"";
			if (_histories.find(edgeIter->to)->second.toPort.size() > 0) {
				os << std::string(":\"") + _histories.find(edgeIter->to)->second.toPort + "\"";
			} else {
				os << ":__name";
			}

		} else {
			os << getPrefix() << "\"" << edgeIter->to << "\"";
			if (edgeIter->toPort.size() > 0) {
				os << std::string(":\"") + edgeIter->toPort + "\"";
			} else {
				os << ":__name";
			}
		}

		if (edgeIter->type == EDGE_INITAL) {
			os << ":nw [style=\"dashed\", color=\"black\"]";
		} else {
			os << " [color=\"black\"]";
		}
		os << std::endl;

	}

	_indentation--;

	os << "}" << std::endl;

}

void SCXMLDotWriter::toDot(const std::string& filename,
                           Interpreter interpreter,
                           const std::list<SCXMLDotWriter::StateAnchor>& stateAnchors,
                           const Element<std::string>& transition) {

	std::ofstream outfile(filename.c_str());
	SCXMLDotWriter writer(interpreter, stateAnchors, transition);
	writer.writeTo(outfile);

}

/**
 * Walk the subset of the graph that is reachable and remember the nodes
 */
void SCXMLDotWriter::assembleGraph(const Element<std::string>& state, int32_t childDepth, int32_t transDepth) {
	std::string nodeId = idForNode(state);

	// this node is neither included per child, nor per transition
	if (childDepth <= 0 && transDepth <= 0) {
		return;
	}

	// been here
	if (_graph.find(nodeId) != _graph.end())
		return;

	_graph[nodeId].node = state;
	_graph[nodeId].portType = _portType;


	if (childDepth == 0 && transDepth == 0) {
		_graph[nodeId].isBorder = true;
	}


	NodeSet<std::string> childElems = InterpreterImpl::filterChildType(Node_base::ELEMENT_NODE, state);
	for (int i = 0; i < childElems.size(); i++) {
		Element<std::string> childElem(childElems[i]);

		// remember histories we passed
		if (iequals(TAGNAME(childElem), "history")) {
			_histories[ATTR(childElem, "id")].to = ATTR(state, "id");
			_histories[ATTR(childElem, "id")].toPort = ATTR(childElem, "id");
		}

		// follow transitions
		if (iequals(TAGNAME(childElem), "transition")) {
			_graph[nodeId].transitions.push_back(childElem);
			NodeSet<std::string> targetStates = _interpreter.getImpl()->getTargetStates(childElem);
			for (int j = 0; j < targetStates.size(); j++) {
				std::string remoteNodeId = idForNode(targetStates[j]);
				_graph[nodeId].targets.insert(std::make_pair(remoteNodeId, childElem));

				// recurse along the transition targets, no weight from child depth
				assembleGraph((Element<std::string>)targetStates[j], 0, transDepth - 1);
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

		// follow childs
		if (InterpreterImpl::isState(Element<std::string>(childElem))) {
			if (_interpreter.getImpl()->isInitial(Element<std::string>(childElem))) {
				// add to initial states if it is initial
				_graph[nodeId].initialchilds.insert(idForNode(childElem));
			} else if (_interpreter.getImpl()->isParallel(Element<std::string>(state))) {
				// add to initial states if we are parallel
				_graph[nodeId].initialchilds.insert(idForNode(childElem));
			}
			// in any case, it is a child state
			_graph[nodeId].childs.insert(idForNode(childElem));

			// recurse (do we really need to?)
			assembleGraph(childElem, childDepth - 1, transDepth);
		}

	}
}


/**
 * Walk the complete graph and draw reachable subset
 */
void SCXMLDotWriter::writeStateElement(std::ostream& os, const Element<std::string>& stateElem) {
	std::string stateId = idForNode(stateElem);

	if (_knownIds.find(stateId) != _knownIds.end())
		return;
	_knownIds.insert(stateId);

	std::list<Node<std::string> > invisParents;
	bool isVisible = (_graph.find(stateId) != _graph.end());

	bool subgraph = InterpreterImpl::isCompound(stateElem) || InterpreterImpl::isParallel(stateElem);
	bool fatherIsParallel = (stateElem.getParentNode() &&
	                         stateElem.getParentNode().getNodeType() == Node_base::ELEMENT_NODE &&
	                         InterpreterImpl::isParallel(Element<std::string>(stateElem.getParentNode())));

	if (subgraph) {
		_indentation++;
		os << std::endl;
		os << getPrefix() << "subgraph \"cluster_" << stateId << "\" {" << std::endl;
		_indentation++;
		os << getPrefix() << "fontsize=14" << std::endl;
		os << getPrefix() << "label=<" << nameForNode(stateElem) << ">" << std::endl;
		//		os << getPrefix() << "rank=\"same\"" << std::endl;
		os << getPrefix() << "labeljust=l" << std::endl;

		os << getPrefix() << (fatherIsParallel ? "style=dashed" : "style=solid") << std::endl;

		//		os << getPrefix() << "ranksep=\"equally\"" << std::endl;

	}

	if (isVisible) {
		// this state is visible!
		const DotState& dotState = _graph.find(stateId)->second;

		// is this a subgraph?

		os << std::endl;
		os << getPrefix() << "\"" << stateId << "\" [" << std::endl;
		_indentation++;

		os << getPrefix() << "fontsize=10," << std::endl;
		os << getPrefix() << "shape=plaintext," << std::endl;
		os << getPrefix() << (fatherIsParallel ? "style=dashed," : "style=solid,") << std::endl;

		// is the current state in the basic configuration?
		if (InterpreterImpl::isMember(stateElem, _interpreter.getBasicConfiguration()))
			os << getPrefix() << "color=red, penwidth=3," << std::endl;

		// is the current state in the basic configuration?
		if (dotState.isBorder)
			os << getPrefix() << "color=blue," << std::endl;

		// is this state final?
		if (_interpreter.getImpl()->isFinal(stateElem)) {
			os << getPrefix() << "shape=doublecircle," << std::endl;
			os << getPrefix() << "color=black," << std::endl;
			os << getPrefix() << "penwidth=2," << std::endl;
			os << getPrefix() << "label=< <table cellborder=\"0\" border=\"0\"><tr><td balign=\"left\">" << nameForNode(stateElem) << "</td></tr></table>>" << std::endl;
			_indentation--;
			os << getPrefix() << "];" << std::endl;

			return;
		}

		// is the state initial?
		bool isInitial = _interpreter.getImpl()->isInitial(stateElem);
		//	if (isInitial)
		//		os << getPrefix() << "style=filled, fillcolor=lightgrey, " << std::endl;

		DotState::mmap_s_e_t::const_iterator destIterF, destIterB;
		//std::list<std::string> outPorts; // count unique keys

		int nrOutPorts = 0;

		switch (dotState.portType) {
		case PORT_TARGET: // outports are per target
			for(DotState::mmap_s_e_t::const_iterator it = dotState.targets.begin(), end = dotState.targets.end();
			        it != end;
			        it = dotState.targets.upper_bound(it->first)) {
				nrOutPorts++;
			}
			break;
		case PORT_EVENT: // outports are per event
			for(DotState::mmap_s_e_t::const_iterator it = dotState.events.begin(), end = dotState.events.end();
			        it != end;
			        it = dotState.events.upper_bound(it->first)) {
				nrOutPorts++;
			}
			break;
		case PORT_TRANSITION:
			nrOutPorts = dotState.transitions.size();
//			for (int i = 0; i < dotState.transitions.size(); i++) {
//				outPorts.push_back(idForNode(dotState.transitions[i]));
//			}
			break;
		}

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
		std::string stateLabel = nameForNode(stateElem);
		int stateLines = 0;

		std::string::size_type start = 0;
		while ((start = stateLabel.find("<br", start)) != std::string::npos) {
			++stateLines;
			start += 3;
		}

		os << "<table " << (isInitial ? "bgcolor=\"orange\" " : "") << "valign=\"top\" align=\"left\" cellborder=\"1\" border=\"0\" cellspacing=\"0\" cellpadding=\"5\" >" << std::endl;
		os << "  <tr><td port=\"__name\" balign=\"left\" valign=\"top\" align=\"left\" rowspan=\"" << nrOutPorts + 1 << "\">" << stateLabel << "</td></tr>" << std::endl;

		switch (dotState.portType) {
		case PORT_TARGET: // outports are per target
			writePerTargetPorts(os, dotState, stateLines);
			break;
		case PORT_EVENT: // outports are per event
			writePerEventPorts(os, dotState, stateLines);
			break;
		case PORT_TRANSITION:
			writePerTransitionPorts(os, dotState, stateLines);
			break;
		}


		// write details of the state
		if (details.size() > 0) {
			os << "  <tr><td balign=\"left\" colspan=\"" << (nrOutPorts == 0 ? 1 : 2) << "\">" << std::endl;
			os << details << std::endl;
			os << "  </td></tr>" << std::endl;
		}

		// write history states
		NodeSet<std::string> histories = InterpreterImpl::filterChildElements(_xmlNSPrefix + "history", stateElem);
		for (int i = 0; i < histories.size(); i++) {
			os << "  <tr><td port=\"" << ATTR(histories[i], "id") << "\" balign=\"left\" colspan=\"" << (nrOutPorts == 0 ? 1 : 2) << "\"><b>history: </b>" << ATTR(histories[i], "id") << "</td></tr>" << std::endl;

		}

		os << "</table>" << std::endl << getPrefix() << ">" << std::endl;

		_indentation--;
		os << getPrefix() << "];" << std::endl;

		for (std::set<std::string>::iterator initIter = dotState.initialchilds.begin(); initIter != dotState.initialchilds.end(); initIter++) {
			std::string destId = *initIter;
			DotEdge edge(stateId, destId);
			edge.type = EDGE_INITAL;
			if (_graph.find(destId) != _graph.end())
				_edges.insert(edge);
		}

	}

	// recurse into children and search others to draw
	NodeSet<std::string> childElems = InterpreterImpl::filterChildType(Node_base::ELEMENT_NODE, stateElem);
	for (int i = 0; i < childElems.size(); i++) {
		Element<std::string> childElem(childElems[i]);
		if (InterpreterImpl::isState(Element<std::string>(childElem))) {
			writeStateElement(os, childElem);
		}
	}

	if (subgraph) {
		_indentation--;
		os << getPrefix() << "} #" << stateId << std::endl;
		_indentation--;
	}
}

void SCXMLDotWriter::writePerTransitionPorts(std::ostream& os, const DotState& dotState, int stateLines) {
	// TODO: Not implemented
}

void SCXMLDotWriter::writePerEventPorts(std::ostream& os, const DotState& dotState, int stateLines) {
	// std::multimap<std::string, Arabica::DOM::Element<std::string> > events; // key is event name, value is transitions that react

	std::string stateId = idForNode(dotState.node);
	DotState::mmap_s_e_t::const_iterator destIterF, destIterB;

	for(DotState::mmap_s_e_t::const_iterator it = dotState.events.begin(), end = dotState.events.end();
	        it != end;
	        it = dotState.events.upper_bound(it->first)) {
		os << "  <tr><td port=\"" << portEscape(it->first) << "\" align=\"right\">" << it->first << "</td></tr>" << std::endl;
	}

}

void SCXMLDotWriter::writePerTargetPorts(std::ostream& os, const DotState& dotState, int stateLines) {
	// std::multimap<std::string, Arabica::DOM::Element<std::string> > targets; // key is remote node, transition is element

	int nrOutports = 0;
	std::string stateId = idForNode(dotState.node);

	typedef DotState::mmap_s_e_t iter_t;

	// we need to count outports first for vertical padding
	for(iter_t::const_iterator targetIter = dotState.targets.begin(), end = dotState.targets.end();
	        targetIter != end;
	        targetIter = dotState.targets.upper_bound(targetIter->first)) {
		nrOutports++;
	}

	for(iter_t::const_iterator targetIter = dotState.targets.begin(), end = dotState.targets.end();
	        targetIter != end;
	        targetIter = dotState.targets.upper_bound(targetIter->first)) {

		// gather all events that activate the transition
		std::string targetId = targetIter->first;

		std::set<std::string> eventNames;

		DotEdge edge(stateId, targetId);
		edge.fromPort = targetId;

		std::pair <iter_t::const_iterator, iter_t::const_iterator> targetKeyRange = dotState.targets.equal_range(targetId);
		for (iter_t::const_iterator transIter = targetKeyRange.first; transIter != targetKeyRange.second;  ++transIter) {
			const Element<std::string>& transElem = transIter->second;

			std::list<std::string> events = InterpreterImpl::tokenizeIdRefs(ATTR(transElem, "event"));
			eventNames.insert(events.begin(), events.end());

			if (events.size() == 0) {
				// spontaneous transition
				eventNames.insert("&#35;");
				edge.type = EDGE_SPONTANEOUS;
			}
		}

		if (_graph.find(targetId) != _graph.end())
			_edges.insert(edge);

		std::stringstream outPortSS;
		outPortSS << (_isFlat ? FlatStateIdentifier::toHTMLLabel(targetId) : "<b>" + targetId + "</b>" );

		if (_isFlat) {
			outPortSS << "<br /><b>events: </b>{";
		} else {
			outPortSS << "<br />{";
		}

		std::string seperator;
		for (std::set<std::string>::const_iterator eventIter = eventNames.begin(); eventIter != eventNames.end(); eventIter++) {
			outPortSS << seperator << *eventIter << std::endl;
			seperator = ", ";
		}
		outPortSS << "}";

		if (nrOutports == 1) {
			int missing = stateLines - nrOutports;
			while (_isFlat && missing-- >= 1) {
				outPortSS << "<br /> ";
			}
		}

		os << "  <tr><td port=\"" << portEscape(targetId) << "\" balign=\"left\" align=\"left\">" << outPortSS.str() << "</td></tr>" << std::endl;

	}
}

std::string SCXMLDotWriter::getDetailedLabel(const Element<std::string>& elem, int indentation) {

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
		if (iequals(TAGNAME(childElems.item(i)), "raise")) {
			if (HAS_ATTR(childElems.item(i), "event "))
				details.name += "<br />event = " + ATTR(childElems.item(i), "event");
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
		details.content = getDetailedLabel((Element<std::string>)childElems.item(i), indentation + 1);
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
	return text;
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

std::string SCXMLDotWriter::nameForNode(const Node<std::string>& node) {
	std::string elemName;
	if (node.getNodeType() == Node_base::ELEMENT_NODE) {
		Element<std::string> elem = (Element<std::string>)node;

		if (InterpreterImpl::isFinal(elem) && _isFlat) {
			// ignore visited and history with final elements
			FlatStateIdentifier flatId(elem.getAttribute("id"));
			return "<b>" + flatId.active.front() + "</b>";
		}

		if (elem.hasAttribute("id") && _isFlat) {
			elemName = FlatStateIdentifier::toHTMLLabel(elem.getAttribute("id"));
			if (elemName.size() > 0)
				return elemName;
		} else if (elem.getTagName() == "scxml") {
			if (elem.hasAttribute("name") && !UUID::isUUID(elem.getAttribute("name"))) {
				elemName += elem.getAttribute("name");
			} else if (elem.hasAttribute("id") && !UUID::isUUID(elem.getAttribute("id"))) {
				elemName += elem.getAttribute("id");
			}
		} else if (InterpreterImpl::isCompound(elem)) {
			elemName = "<i>Compound: </i>" + elem.getAttribute("id");
		} else if (InterpreterImpl::isParallel(elem)) {
			elemName = "<i>Parallel: </i>" + elem.getAttribute("id");
		} else if (elem.hasAttribute("id")) {
			elemName += elem.getAttribute("id");
		}
	}

	if (elemName.size() == 0)
		elemName = boost::lexical_cast<std::string>(node.getLocalName());

	return "<b>" + elemName + "</b>";

}

std::string SCXMLDotWriter::idForNode(const Node<std::string>& node) {
	std::string elemId;

	// try to get the id as the name or id attribute
	if (node.getNodeType() == Node_base::ELEMENT_NODE) {
		Element<std::string> elem = (Element<std::string>)node;

		if (InterpreterImpl::isFinal(elem) && _isFlat) {
			// ignore visited and history with final elements
			FlatStateIdentifier flatId(elem.getAttribute("id"));
			return flatId.activeId();
		}

		if (elem.hasAttribute("name")) {
			elemId = elem.getAttribute("name");
		} else if (elem.hasAttribute("id")) {
			elemId = elem.getAttribute("id");
		}
	}

	// no luck, create id from position in tree
	if (elemId.size() == 0) {
		Node<std::string> tmpParent = node;
		Node<std::string> tmpIndex;
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
	return elemId;
}

}