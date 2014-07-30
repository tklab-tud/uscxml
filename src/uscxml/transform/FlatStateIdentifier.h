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


#include <sstream>
#include <string>
#include <list>
#include <map>

namespace uscxml {

class USCXML_API FlatStateIdentifier {
public:
	FlatStateIdentifier(const std::string& identifier) {
		std::string parsedName;
		// parse unique state identifier
		std::stringstream elemNameSS(identifier);
		std::string section;
		while(std::getline(elemNameSS, section, ';')) {
			if (boost::starts_with(section, "active-")) {
				std::stringstream stateSS(section.substr(7));
				std::string state;
				while(std::getline(stateSS, state, '-')) {
					if (state.length() > 0) {
						active.push_back(state);
					}
				}
			} else if (boost::starts_with(section, "entered-")) {
				std::stringstream stateSS(section.substr(8));
				std::string state;
				while(std::getline(stateSS, state, '-')) {
					if (state.length() > 0) {
						visited.push_back(state);
					}
				}
			} else if (boost::starts_with(section, "history-")) {
				std::stringstream stateSS(section.substr(8));
				std::string state;
				std::string history;
				while(std::getline(stateSS, state, '-')) {
					if (state.length() > 0) {
						if (history.size() == 0) {
							history = state;
						} else {
							histories[history].push_back(state);
						}
					} else {
						history = "";
					}
				}
			}
		}
	}

	std::string activeId() {
		std::stringstream activeSS;
		activeSS << "active-";
		for (std::list<std::string>::const_iterator activeIter = active.begin(); activeIter != active.end(); activeIter++) {
			activeSS << *activeIter << "-";
		}
		return activeSS.str();
	}

	std::list<std::string> active;
	std::list<std::string> visited;
	std::map<std::string, std::list<std::string> > histories;

	static std::string toHTMLLabel(const std::string& identifier, int minRows = 0) {
		FlatStateIdentifier flatId(identifier);

		std::list<std::string>::const_iterator listIter;
		std::stringstream labelSS;
		std::string seperator;

//		labelSS << "<table valign=\"top\" align=\"left\" cellborder=\"0\" border=\"0\" cellspacing=\"0\" cellpadding=\"2\">";
//		labelSS << "<tr>";
//		labelSS << "<td balign=\"left\" align=\"left\" valign=\"top\">";

		labelSS << "<b>active: </b>";
		labelSS << "{";
		for (listIter = flatId.active.begin(); listIter != flatId.active.end(); listIter++) {
			labelSS << seperator << *listIter;
			seperator = ", ";
		}
		labelSS << "}";

		if (flatId.visited.size() > 0) {
			minRows--;

			labelSS << "<br /><b>init: </b>";

			labelSS << "{";
			seperator = "";
			for (listIter = flatId.visited.begin(); listIter != flatId.visited.end(); listIter++) {
				labelSS << seperator << *listIter;
				seperator = ", ";
			}
			labelSS << "}";
		}

#if 1
		if (flatId.histories.size() > 0) {
			minRows--;

			seperator = "";
			std::string histSeperator = "<br />     ";

			labelSS << "<br /><b>history: </b>";

			std::map<std::string, std::list<std::string> >::const_iterator histIter;
			for (histIter = flatId.histories.begin(); histIter != flatId.histories.end(); histIter++) {
				labelSS << histSeperator << histIter->first << ": {";

				for (listIter = histIter->second.begin(); listIter != histIter->second.end(); listIter++) {
					labelSS << seperator << *listIter;
					seperator = ", ";
				}
				labelSS << "}";
				seperator = "";
			}
		}
#endif
//		while(minRows-- > 0)
//			labelSS << "<tr><td valign=\"top\"></td></tr>"; // eat up rest of space
//
//		labelSS << "</td>";
//		labelSS << "</tr>";
//		labelSS << "</table>";
		return labelSS.str();
	}

};

}

#endif /* end of include guard: FLATSTATEIDENTIFIER_H_E9534AF9 */
