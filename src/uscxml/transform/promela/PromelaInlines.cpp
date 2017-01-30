/**
 *  @file
 *  @author     2016 Stefan Radomski (stefan.radomski@cs.tu-darmstadt.de)
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

#include "PromelaInlines.h"
#include "uscxml/interpreter/Logging.h"
#include <boost/algorithm/string.hpp>


namespace uscxml {

using namespace XERCESC_NS;

void PromelaInline::dump() {
}

PromelaInline::PromelaInline(const XERCESC_NS::DOMNode* node) {
	if (node->getNodeType() != DOMNode::COMMENT_NODE && node->getNodeType() != DOMNode::TEXT_NODE)
		return; // nothing to do

	std::stringstream ssLine(X(node->getNodeValue()).str());
	std::string line;

	while(std::getline(ssLine, line)) {
		// skip to first promela line
		boost::trim(line);
		if (boost::starts_with(line, "promela"))
			break;
	}

	if (!boost::starts_with(line, "promela"))
		return;

	if (false) {
	} else if (boost::starts_with(line, "promela-code")) {
		type = PROMELA_CODE;
	} else if (boost::starts_with(line, "promela-ltl")) {
		type = PROMELA_LTL;
	} else if (boost::starts_with(line, "promela-event-all")) {
		type = PROMELA_EVENT_ALL_BUT;
	} else if (boost::starts_with(line, "promela-event")) {
		type = PROMELA_EVENT_ONLY;
	} else if (boost::starts_with(line, "promela-progress")) {
		type = PROMELA_PROGRESS_LABEL;
	} else if (boost::starts_with(line, "promela-accept")) {
		type = PROMELA_ACCEPT_LABEL;
	} else if (boost::starts_with(line, "promela-end")) {
		type = PROMELA_END_LABEL;
	}

	std::stringstream contentSS;
	size_t endType = line.find_first_of(": \n");

	std::string seperator;
	if (endType != std::string::npos && endType + 1 < line.size()) {
		contentSS << line.substr(endType + 1, line.size() - endType + 1);
		seperator = "\n";
	}

	while(std::getline(ssLine, line)) {
		boost::trim(line);
		if (boost::starts_with(line, "promela")) {
			LOGD(USCXML_ERROR) << "Split multiple #promela pragmas into multiple comments!" << std::endl;
			break;
		}
		contentSS << seperator << line;
		seperator = "\n";
	}
	content = contentSS.str();

}

PromelaInlines::PromelaInlines(const XERCESC_NS::DOMNode* node) {

	std::list<DOMNode*> levelNodes;
	levelNodes.push_back(const_cast<XERCESC_NS::DOMNode*>(node));

	size_t level = 0;
	while(levelNodes.size() > 0) {
		PromelaInline* predecessor = NULL;

		// iterate all nodes at given level
		for (auto levelNode : levelNodes) {

			// get all comments
			std::list<DOMNode*> comments = DOMUtils::filterChildType(DOMNode::COMMENT_NODE, levelNode);
			for (auto comment : comments) {

				PromelaInline* tmp = new PromelaInline(comment);
				if (tmp->type == PromelaInline::PROMELA_NIL) {
					delete tmp;
					continue;
				}

				if (predecessor != NULL) {
					tmp->prevSibling = predecessor;
					predecessor->nextSibling = tmp;
				}
				tmp->level = level;
				tmp->container = static_cast<DOMElement*>(levelNode);
				predecessor = tmp;
				inlines[levelNode].push_back(tmp);
				allInlines.push_back(tmp);
			}
		}

		levelNodes = DOMUtils::filterChildType(DOMNode::ELEMENT_NODE, levelNodes);
		level++;
	}

}

PromelaInlines::~PromelaInlines() {
}

std::list<PromelaInline*> PromelaInlines::getRelatedTo(const XERCESC_NS::DOMNode* node,
        PromelaInline::PromelaInlineType type) {
	std::list<PromelaInline*> related;

	auto inlIter = inlines.begin();
	while (inlIter != inlines.end()) {
		std::list<PromelaInline*>::iterator pmlIter = inlIter->second.begin();
		while (pmlIter != inlIter->second.end()) {
			if ((type != PromelaInline::PROMELA_NIL || (*pmlIter)->type == type) && (*pmlIter)->relatesTo(node)) {
				related.push_back(*pmlIter);
			}
			pmlIter++;
		}
		inlIter++;
	}
	return related;
}

std::list<PromelaInline*> PromelaInlines::getAllOfType(uint32_t type) {
	std::list<PromelaInline*> related;

	auto inlIter = inlines.begin();
	while (inlIter != inlines.end()) {
		std::list<PromelaInline*>::iterator pmlIter = inlIter->second.begin();
		while (pmlIter != inlIter->second.end()) {
			if ((*pmlIter)->type & type) {
				related.push_back(*pmlIter);
			}
			pmlIter++;
		}
		inlIter++;
	}
	return related;

}

}
