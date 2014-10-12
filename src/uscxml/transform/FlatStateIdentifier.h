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

#ifndef FLATSTATEIDENTIFIER_H_E9534AF9
#define FLATSTATEIDENTIFIER_H_E9534AF9

#include "uscxml/Common.h"
#include "uscxml/Convenience.h"
#include "uscxml/DOMUtils.h"

#include <XPath/XPath.hpp>

#include <sstream>
#include <string>
#include <list>
#include <map>

#include <boost/algorithm/string.hpp>

namespace uscxml {

class USCXML_API FlatStateIdentifier {
public:

	operator bool() const {
		return stateId.length() > 0;
	}

	FlatStateIdentifier(const Arabica::XPath::NodeSet<std::string>& activeStates,
	                    const Arabica::XPath::NodeSet<std::string>& alreadyEnteredStates,
	                    const std::map<std::string, Arabica::XPath::NodeSet<std::string> >& historyStates) {
		for (int i = 0; i < activeStates.size(); i++) {
			active.push_back(ATTR_CAST(activeStates[i], "id"));
		}

		for (int i = 0; i < alreadyEnteredStates.size(); i++) {
			const Arabica::DOM::NodeList<std::string>& children = alreadyEnteredStates[i].getChildNodes();
			bool isRelevant = false;
			for (int j = 0; j < children.getLength(); j++) {
				if (children.item(j).getNodeType() != Arabica::DOM::Node_base::ELEMENT_NODE)
					continue;
				if (iequals(LOCALNAME_CAST(children.item(j)), "data") || iequals(LOCALNAME_CAST(children.item(j)), "datamodel")) {
					isRelevant = true;
					break;
				}
			}
			if (isRelevant)
				visited.push_back(ATTR_CAST(alreadyEnteredStates[i], "id"));
		}

		std::map<std::string, Arabica::XPath::NodeSet<std::string> >::const_iterator histIter;
		for (histIter = historyStates.begin(); histIter != historyStates.end(); histIter++) {
			for (int i = 0; i < histIter->second.size(); i++) {
				histories[histIter->first].push_back(ATTR_CAST(histIter->second[i], "id"));
			}
		}

		initStateId();
	}


	FlatStateIdentifier(const std::list<std::string>& active,
	                    const std::list<std::string>& visited,
	                    const std::map<std::string, std::list<std::string> >& histories) : active(active), visited(visited), histories(histories) {
		initStateId();
	}

	static std::string toStateId(const std::list<std::string> active,
	                             const std::list<std::string> visited = std::list<std::string>(),
	                             const std::map<std::string, std::list<std::string> > histories = std::map<std::string, std::list<std::string> >()) {
		FlatStateIdentifier tmp(active, visited, histories);
		return tmp.getStateId();
	}

	FlatStateIdentifier(const std::string& identifier) : stateId(identifier) {
		std::string parsedName;
		// parse unique state identifier
		std::stringstream elemNameSS(identifier);
		std::string section;
		while(std::getline(elemNameSS, section, ';')) {
			if (boost::starts_with(section, "active:{")) {
				// active:{s0,s1,s2}
				std::stringstream stateSS(section.substr(8, section.size() - 9));
				std::string state;
				while(std::getline(stateSS, state, ',')) {
					size_t closingBracketPos = state.find("}");
					if (closingBracketPos != std::string::npos) {
						state = state.substr(0, closingBracketPos);
					}
					if (state.length() > 0) {
						active.push_back(state);
					}
				}
			} else if (boost::starts_with(section, "visited:{")) {
				// entered:{s0,s1,s2}
				std::stringstream stateSS(section.substr(9, section.size() - 10));
				std::string state;
				while(std::getline(stateSS, state, ',')) {
					size_t closingBracketPos = state.find("}");
					if (closingBracketPos != std::string::npos) {
						state = state.substr(0, closingBracketPos);
					}
					if (state.length() > 0) {
						visited.push_back(state);
					}
				}
			} else if (boost::starts_with(section, "history:{")) {
				// history:{h0:{s1,s2},h1:{s2,s3}}
				std::string histEntries(section.substr(9, section.length() - 10));

				std::string state;
				size_t start = 0;
				size_t history = 0;

				while((history = histEntries.find(":", start)) != std::string::npos) {
					std::string histName = histEntries.substr(start, history - start);
					history++;

					size_t end = histEntries.find("}", start);
					if (end == std::string::npos)
						continue;

					std::stringstream stateSS(histEntries.substr(history + 1, end - history - 1));
					std::string state;
					while(std::getline(stateSS, state, ',')) {
						size_t closingBracketPos = state.find("}");
						if (closingBracketPos != std::string::npos) {
							state = state.substr(0, closingBracketPos);
						}
						histories[histName].push_back(state);
					}

					start = end + 2;
				}
			}
		}
		initStateId();
	}

	const std::string& getStateId() {
		return stateId;
	}

	const std::list<std::string>& getActive() {
		return active;
	}
	const std::string& getFlatActive() {
		return flatActive;
	}

	const std::list<std::string>& getVisited() {
		return visited;
	}
	const std::string& getFlatVisited() {
		return flatVisited;
	}

	const std::map<std::string, std::list<std::string> > & getHistory() {
		return histories;
	}
	const std::string& getFlatHistory() {
		return flatHistories;
	}

protected:
	std::list<std::string> active;
	std::list<std::string> visited;
	std::map<std::string, std::list<std::string> > histories;

	std::string flatActive;
	std::string flatVisited;
	std::string flatHistories;

	std::string stateId;

	void initStateId() {
		std::stringstream stateIdSS;
		std::string seperator;

		std::stringstream flatActiveSS;
		flatActiveSS << "active:{";
		for (std::list<std::string>::const_iterator actIter = active.begin(); actIter != active.end(); actIter++) {
			flatActiveSS << seperator << *actIter;
			seperator = ",";
		}
		flatActiveSS << "}";
		flatActive = flatActiveSS.str();
		stateIdSS << flatActive;

		if (visited.size() > 0) {
			std::stringstream flatVisitedSS;
			seperator = "";
			flatVisitedSS << "visited:{";
			for (std::list<std::string>::const_iterator visitIter = visited.begin(); visitIter != visited.end(); visitIter++) {
				flatVisitedSS << seperator << *visitIter;
				seperator = ",";
			}
			flatVisitedSS << "}";
			flatVisited = flatVisitedSS.str();
			stateIdSS << ";" << flatVisited;
		}

		if (histories.size() > 0) {
			std::stringstream flatHistorySS;
			seperator = "";
			flatHistorySS << "history:{";
			for (std::map<std::string, std::list<std::string> >::const_iterator histIter = histories.begin(); histIter != histories.end(); histIter++) {
				flatHistorySS << seperator << histIter->first << ":{";
				seperator = ",";
				std::string itemSeperator;
				for (std::list<std::string>::const_iterator histItemIter = histIter->second.begin(); histItemIter != histIter->second.end(); histItemIter++) {
					flatHistorySS << itemSeperator << *histItemIter;
					itemSeperator = ",";
				}
				flatHistorySS << "}";
			}
			flatHistorySS << "}";
			flatHistories = flatHistorySS.str();
			stateIdSS << ";" << flatHistories;
		}

		stateId = stateIdSS.str();
	}

#if 0
	std::string activeId() {
		std::stringstream activeSS;
		activeSS << "active-";
		for (std::list<std::string>::const_iterator activeIter = active.begin(); activeIter != active.end(); activeIter++) {
			activeSS << *activeIter << "-";
		}
		return activeSS.str();
	}

#endif

};

}

#endif /* end of include guard: FLATSTATEIDENTIFIER_H_E9534AF9 */
