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

#include "uscxml/transform/ChartToFSM.h"
#include "uscxml/transform/ChartToTex.h"
#include "uscxml/transform/FlatStateIdentifier.h"

#include <DOM/io/Stream.hpp>
#include <iostream>
#include "uscxml/UUID.h"
#include <math.h>
#include <boost/algorithm/string.hpp>
#include <glog/logging.h>


namespace uscxml {

using namespace Arabica::DOM;
using namespace Arabica::XPath;

ChartToTex::~ChartToTex() {
}

Transformer ChartToTex::transform(const Interpreter& other) {
	return boost::shared_ptr<TransformerImpl>(new ChartToTex(other));
}

void ChartToTex::writeTo(std::ostream& stream) {
	writeTex(stream);
}

void ChartToTex::writeTex(std::ostream& stream) {
	_keepInvalidTransitions = true;
	if (_start == NULL) {
		interpret();
	}

	bool wroteRowStart = false;
	std::string seperator;

	for (std::map<std::string, GlobalState*>::iterator stateIter = _globalConf.begin(); stateIter != _globalConf.end(); stateIter++) {
		assert(_indexToState.find(stateIter->second->index) == _indexToState.end());
		_indexToState[stateIter->second->index] = stateIter->second;
	}

	stream << "% " << _sourceURL.asString() << std::endl;

	stream << "%<*provideCommand>" << std::endl;
	stream << "\\providecommand{\\globalStateListCell}[2][c]{%" << std::endl;
	stream << "  \\begin{tabular}[#1]{@{}l@{}}#2\\end{tabular}}" << std::endl;
	stream << "%</provideCommand>" << std::endl;


	stream << std::endl;

//	stream << "\\begin{table}[H]" << std::endl;
//	stream << "\\centering" << std::endl;
//	stream << "\\begin{tabular}{r | l | L{12em} | l}" << std::endl;

	stream << "\\begin{longtable}{| r | l | l | l |}" << std::endl;

	for (std::map<unsigned long, GlobalState*>::iterator stateIter = _indexToState.begin(); stateIter != _indexToState.end(); stateIter++) {
		GlobalState* currState = stateIter->second;

		stream << "\\hline" << std::endl;

		if (!wroteRowStart) {
			stream << "%<*tableRows>" << std::endl;
			wroteRowStart = true;
		}

		stream << "%<*globalState" << currState->index << ">" << std::endl;

		// state index
		stream << "\\tikzmark{statename_" << currState->index << "}" << "$\\widetilde{s}(" << currState->index << ")$ & ";

		// members in active configuration
		FlatStateIdentifier flatId(currState->stateId);
		stream << "\\globalStateListCell[t]{";
		stream << "\\tikzmark{active_" << currState->index << "}";
		stream << "$\\widetilde{s}_a(" << currState->index << ")$: " << stateListToTex(flatId.getFlatActive(), flatId.getActive().size() == 0) << "\\\\";

		// already visited states
		stream << "\\tikzmark{visited_" << currState->index << "}";
		stream << "$\\widetilde{s}_d(" << currState->index << ")$: " << stateListToTex(flatId.getFlatVisited(), flatId.getVisited().size() == 0) << "\\\\";

		// history assignments
		stream << "\\tikzmark{history_" << currState->index << "}";
		stream << "$\\widetilde{s}_h(" << currState->index << ")$: " << stateListToTex(flatId.getFlatHistory(), flatId.getHistory().size() == 0) << "} & ";

		// all transitions
		std::set<std::string> origTransitions;
		for (std::list<GlobalTransition*>::iterator transIter = stateIter->second->sortedOutgoing.begin(); transIter != stateIter->second->sortedOutgoing.end(); transIter++) {
			GlobalTransition* currTrans = *transIter;
			Arabica::XPath::NodeSet<std::string> members = currTrans->getTransitions();
			for (size_t i = 0; i < members.size(); i++) {
				Element<std::string> transElem(members[i]);
				if (HAS_ATTR(transElem, "priority")) {
					origTransitions.insert(ATTR(transElem, "priority"));
				} else {
					origTransitions.insert("initial");
				}
			}
		}

		if (origTransitions.size() > 0) {
			stream << "$\\{ ";
			seperator = "";
			for (std::set<std::string>::reverse_iterator transIter = origTransitions.rbegin(); transIter != origTransitions.rend(); transIter++) {
				stream << seperator << "t_{" << *transIter << "}";
				seperator = ", ";
			}
			stream << " \\}$";
		} else {
			stream << "$\\emptyset$";
		}
		stream << "\\tikzmark{transitions_" << currState->index << "}";
		stream << "  & \\\\ \\hline" << std::endl;

		if (stateIter->second->sortedOutgoing.size() > 0) {
			stream << "$\\widetilde{\\mathcal{T}}(" << currState->index << ")$" << std::endl;

			size_t ecIndex = 0;
			for (std::list<GlobalTransition*>::iterator transIter = stateIter->second->sortedOutgoing.begin(); transIter != stateIter->second->sortedOutgoing.end(); transIter++, ecIndex++) {
				GlobalTransition* currTrans = *transIter;
				stream << "& ";
				stream << "\\tikzmark{trans_set" << currState->index << "_" << ecIndex << "}";

				if (!currTrans->isValid)
					stream << "\\sout{";

				Arabica::XPath::NodeSet<std::string> members = currTrans->getTransitions();
				if (members.size() > 0) {
					stream << "$\\{ ";
					seperator = "";
					for (size_t i = 0; i < members.size(); i++) {
						Element<std::string> transElem(members[i]);
						if (HAS_ATTR(transElem, "priority")) {
							stream << seperator << "t_{" << ATTR(transElem, "priority") << "}";
						} else {
							stream << seperator << "t_{initial}";
						}
						seperator = ", ";
					}
					stream << " \\}$";
				} else {
					stream << "$\\emptyset$";
				}
				//			stream << "& \\sout{$\\{ t_2, t_0 \\}$}, & \\emph{$Inv_4$: nested source states} \\\\" << std::endl;
				//			stream << "& $\\{ t_2 \\}$ &  & $\\widetilde{s}(2)$ \\\\" << std::endl;
				//			stream << "& $\\{ t_0 \\}$ &  & $\\widetilde{s}(4)$ \\\\" << std::endl;

				if (!currTrans->isValid) {
#if 1
					stream << " } & \\emph{";
					switch(currTrans->invalidReason) {
					case GlobalTransition::NO_COMMON_EVENT:
						stream << "$Inv_1$: ";
						break;
					case GlobalTransition::MIXES_EVENT_SPONTANEOUS:
						stream << "$Inv_2$: ";
						break;
					case GlobalTransition::SAME_SOURCE_STATE:
						stream << "$Inv_3$: ";
						break;
					case GlobalTransition::CHILD_ENABLED:
						stream << "$Inv_4$: ";
						break;
					case GlobalTransition::PREEMPTING_MEMBERS:
						stream << "$Inv_5$: ";
						break;
					case GlobalTransition::UNCONDITIONAL_MATCH:
						stream << "$Opt_1$: ";
						break;
					case GlobalTransition::UNCONDITIONAL_SUPERSET:
						stream << "$Opt_2$: ";
						break;
					}
					stream << currTrans->invalidMsg << "} ";
#endif
					stream << "\\tikzmark{exec_content" << currState->index << "_" << ecIndex << "}";
					stream << " & ";
				} else {
					stream << " & ";
					std::stringstream execContentSS;

					seperator = "";
					for (std::list<GlobalTransition::Action>::iterator actionIter = currTrans->actions.begin(); actionIter != currTrans->actions.end(); actionIter++) {
						Element<std::string> execContent;

						if (actionIter->onEntry)
							execContent = actionIter->onEntry;

						if (actionIter->raiseDone)
							execContent = actionIter->raiseDone;

						if (actionIter->onExit)
							execContent = actionIter->onExit;

						if (actionIter->transition)
							execContent = actionIter->transition;

						if (execContent) {
							if (HAS_ATTR(execContent, "line_start") && HAS_ATTR(execContent, "line_end")) {
								size_t lineStart = strTo<size_t>(ATTR(execContent, "line_start"));
								size_t lineEnd = strTo<size_t>(ATTR(execContent, "line_end"));
								lineStart++;
								lineEnd--;
								if (lineStart == lineEnd) {
									execContentSS << seperator << "l_{" << lineStart << "}";
								} else {
									execContentSS << seperator << "l_{" << lineStart << "-" << lineEnd << "}";
								}
							}
							seperator = ", ";
						}
					}

					if (execContentSS.str().size() > 0) {
						stream << "$\\mathcal{X} := (" << execContentSS.str() << ")$";
					} else {
						stream << "$\\emptyset$";
					}
					stream << "\\tikzmark{exec_content" << currState->index << "_" << ecIndex << "}";

					stream << " & $\\widetilde{s}(" << _globalConf[currTrans->destination]->index << ")$ ";
					stream << "\\tikzmark{target" << currState->index << "_" << ecIndex << "}";
				}

				stream << "\\\\" << std::endl;
			}
			if (stateIter->second->sortedOutgoing.size() == 0) {
				stream << " &  &  & \\\\" << std::endl;
			}

			stream << "\\hline" << std::endl;
		}
		stream << "%</globalState" << currState->index << ">" << std::endl;

	}
	if (wroteRowStart) {
		stream << "%</tableRows>" << std::endl;
	}

//	stream << "\\end{tabular}" << std::endl;
//	stream << "\\end{table}" << std::endl << std::endl;
	stream << "\\end{longtable}" << std::endl << std::endl;

}

std::string ChartToTex::stateListToTex(const std::string& input, bool isEmpty) {
	std::string statesTex;
	if (!isEmpty) {
		statesTex = input;
		boost::replace_all(statesTex, "active:", "");
		boost::replace_all(statesTex, "history:", "");
		boost::replace_all(statesTex, "visited:", "");
		statesTex = "\\texttt{" + texEscape(statesTex) + "}";
	} else {
		statesTex = "$\\emptyset$";
	}
	return statesTex;
}

std::string ChartToTex::texEscape(const std::string& input) {
	std::string texString(input);
	boost::replace_all(texString, "\\", "\\\\");
	boost::replace_all(texString, "{", "\\{");
	boost::replace_all(texString, "}", "\\}");
	boost::replace_all(texString, ",", ", ");
	return texString;
}


}