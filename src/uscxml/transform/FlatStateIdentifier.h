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
	FlatStateIdentifier(const Arabica::XPath::NodeSet<std::string>& activeStates,
											const Arabica::XPath::NodeSet<std::string>& alreadyEnteredStates,
											const std::map<std::string, Arabica::XPath::NodeSet<std::string> >& historyStates) {
		for (int i = 0; i < activeStates.size(); i++) {
			active.push_back(ATTR_CAST(activeStates[i], "id"));
		}

		for (int i = 0; i < alreadyEnteredStates.size(); i++) {
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
					if (state.length() > 0) {
						active.push_back(state);
					}
				}
			} else if (boost::starts_with(section, "entered:{")) {
				// entered:{s0,s1,s2}
				std::stringstream stateSS(section.substr(9, section.size() - 10));
				std::string state;
				while(std::getline(stateSS, state, ',')) {
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
						histories[histName].push_back(state);
					}
					
					start = end + 2;
				}
			}
		}
	}

	const std::string& getStateId() {
		return stateId;
	}
	
	const std::list<std::string>& getActive() {
		return active;
	}

	const std::list<std::string>& getVisited() {
		return visited;
	}

	const std::map<std::string, std::list<std::string> > & getHistory() {
		return histories;
	}

protected:
	std::list<std::string> active;
	std::list<std::string> visited;
	std::map<std::string, std::list<std::string> > histories;
	std::string stateId;

	void initStateId() {
		std::stringstream stateIdSS;
		
		std::string seperator;
		stateIdSS << "active:{";
		for (std::list<std::string>::const_iterator actIter = active.begin(); actIter != active.end(); actIter++) {
			stateIdSS << seperator << *actIter;
			seperator = ",";
		}
		stateIdSS << "};";
		
		seperator = "";
		stateIdSS << "entered:{";
		for (std::list<std::string>::const_iterator visitIter = visited.begin(); visitIter != visited.end(); visitIter++) {
			stateIdSS << seperator << *visitIter;
			seperator = ",";
		}
		stateIdSS << "};";
		
		seperator = "";
		stateIdSS << "history:{";
		for (std::map<std::string, std::list<std::string> >::const_iterator histIter = histories.begin(); histIter != histories.end(); histIter++) {
			stateIdSS << seperator << histIter->first << ":{";
			seperator = ",";
			std::string itemSeperator;
			for (std::list<std::string>::const_iterator histItemIter = histIter->second.begin(); histItemIter != histIter->second.end(); histItemIter++) {
				stateIdSS << itemSeperator << *histItemIter;
				itemSeperator = ",";
			}
			stateIdSS << "}";
		}
		stateIdSS << "}";
		
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
