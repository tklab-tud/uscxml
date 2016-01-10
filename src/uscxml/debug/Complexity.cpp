/**
*  @file
*  @author     2012-2015 Stefan Radomski (stefan.radomski@cs.tu-darmstadt.de)
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

#include "Complexity.h"
#include "uscxml/DOMUtils.h"

#include <boost/algorithm/string.hpp>

namespace uscxml {

using namespace Arabica::DOM;
using namespace Arabica::XPath;

std::list<std::set<Element<std::string> > > Complexity::getAllConfigurations(const Arabica::DOM::Element<std::string>& root) {

	std::list<std::set<Element<std::string> > > allConfigurations;
	std::string nsPrefix = (root.getPrefix().size() > 0 ? root.getPrefix() + ":" : "");
	std::string localName = root.getLocalName();
	bool isAtomic = true;
	
	NodeList<std::string> children = root.getChildNodes();
	for (int i = 0; i < children.getLength(); i++) {
		if (children.item(i).getNodeType() != Node_base::ELEMENT_NODE)
			continue;
		Element<std::string> childElem(children.item(i));
		if (childElem.getTagName() == nsPrefix + "state" ||
				childElem.getTagName() == nsPrefix + "parallel" ||
				childElem.getTagName() == nsPrefix + "final") {
			// nested child state
			std::list<std::set<Element<std::string> > > nestedConfigurations = getAllConfigurations(childElem);
			isAtomic = false;
			if (localName == "parallel" && allConfigurations.size() > 0) {
				// for every nested configuration, every new nested is valid
				std::list<std::set<Element<std::string> > > combinedConfigurations;
				for (std::list<std::set<Element<std::string> > >::iterator existIter = allConfigurations.begin(); existIter != allConfigurations.end(); existIter++) {
					std::set<Element<std::string> > existingConfig = *existIter;
					
					for (std::list<std::set<Element<std::string> > >::iterator newIter = nestedConfigurations.begin(); newIter != nestedConfigurations.end(); newIter++) {

						std::set<Element<std::string> > newConfig = *newIter;
						std::set<Element<std::string> > combinedSet;
						combinedSet.insert(existingConfig.begin(), existingConfig.end());
						combinedSet.insert(newConfig.begin(), newConfig.end());

						combinedConfigurations.push_back(combinedSet);
					}
				}
				allConfigurations = combinedConfigurations;
			} else {
				// just add nested configurations and this
				for (std::list<std::set<Element<std::string> > >::iterator newIter = nestedConfigurations.begin(); newIter != nestedConfigurations.end(); newIter++) {
					std::set<Element<std::string> > newConfig = *newIter;
					if (localName != "scxml")
						newConfig.insert(root);
					allConfigurations.push_back(newConfig);
				}
			}
		}
	}

	if (isAtomic) {
		std::set<Element<std::string> > soleConfig;
		soleConfig.insert(root);
		allConfigurations.push_back(soleConfig);
	}
	return allConfigurations;
}
	
std::map<size_t, size_t> Complexity::getTransitionHistogramm(const Arabica::DOM::Element<std::string>& root) {
	std::map<size_t, size_t> histogram;
	std::string nameSpace;
    
	std::list<std::set<Element<std::string> > > allConfig = Complexity::getAllConfigurations(root);
	
	// for every legal configuration, count the transitions
	for (std::list<std::set<Element<std::string> > >::iterator confIter = allConfig.begin(); confIter != allConfig.end(); confIter++) {
		NodeSet<std::string> configNodeSet;
		std::set<Element<std::string> > config = *confIter;
		for (std::set<Element<std::string> >::iterator elemIter = config.begin(); elemIter != config.end(); elemIter++) {
			configNodeSet.push_back(*elemIter);
			if (nameSpace.size() == 0 && elemIter->getPrefix().size() > 0)
				nameSpace = elemIter->getPrefix() + ":";
		}
		NodeSet<std::string> transitions = InterpreterImpl::filterChildElements(nameSpace + "transition", configNodeSet);
		histogram[transitions.size()]++;
	}

	return histogram;
}


uint64_t Complexity::stateMachineComplexity(InterpreterImpl* interpreter, Variant variant) {
    Arabica::DOM::Element<std::string> root = interpreter->getDocument().getDocumentElement();

    Arabica::XPath::NodeSet<std::string> reachable;
    
    if (variant & IGNORE_UNREACHABLE) {
        reachable = interpreter->getReachableStates();
    }
    
    Complexity complexity = calculateStateMachineComplexity(root, reachable);
	uint64_t value = complexity.value;
	
    if (!(variant & IGNORE_HISTORY)) {
		for (std::list<uint64_t>::const_iterator histIter = complexity.history.begin(); histIter != complexity.history.end(); histIter++) {
			value *= *histIter;
		}
	}
	
    if (!(variant & IGNORE_NESTED_DATA)) {
		bool ignoreNestedData = false;
		if (root.getLocalName() == "scxml" && (!HAS_ATTR_CAST(root, "binding") || boost::to_lower_copy(ATTR_CAST(root, "binding")) == "early")) {
			ignoreNestedData = true;
		}
		
		if (!ignoreNestedData) {
			uint64_t power = complexity.nestedData;
			while(power--) {
				value *= 2;
			}
		}
	}
	
	return value;
}
	
Complexity Complexity::calculateStateMachineComplexity(const Arabica::DOM::Element<std::string>& root, const Arabica::XPath::NodeSet<std::string>& reachable) {
	Complexity complexity;

	bool hasFlatHistory = false;
	bool hasDeepHistory = false;
	bool hasNestedData = false;
	
	Arabica::DOM::NodeList<std::string> childElems = root.getChildNodes();
	for (int i = 0; i < childElems.getLength(); i++) {
		if (childElems.item(i).getNodeType() != Node_base::ELEMENT_NODE)
			continue;
		Element<std::string> childElem = Element<std::string>(childElems.item(i));
		if (InterpreterImpl::isHistory(childElem)) {
			if (HAS_ATTR(childElem, "type") && ATTR(childElem, "type") == "deep") {
				hasDeepHistory = true;
			} else {
				hasFlatHistory = true;
			}
		}
		if (!hasNestedData && childElem.getLocalName() == "datamodel") {
			Arabica::DOM::NodeList<std::string> dataElemChilds = childElem.getChildNodes();
			for (int j = 0; j < dataElemChilds.getLength(); j++) {
				if (dataElemChilds.item(j).getLocalName() == "data")
					hasNestedData = true;
			}
		}
	}

	if (hasNestedData)
		complexity.nestedData++;
	
    if (reachable.size() > 0 && !InterpreterImpl::isMember(root, reachable)) {
        return 0;
    } else if (InterpreterImpl::isCompound(root) || TAGNAME(root) == "scxml") {
		// compounds can be in any of the child state -> add
		NodeSet<std::string> childs = InterpreterImpl::getChildStates(root);
		for (int i = 0; i < childs.size(); i++) {
			complexity += calculateStateMachineComplexity(Element<std::string>(childs[i]), reachable);
		}
		if (hasFlatHistory) {
			complexity.history.push_back(childs.size());
		}
		if (hasDeepHistory) {
			complexity.history.push_back(complexity.value);
		}
	} else if (InterpreterImpl::isParallel(root)) {
		// parallels are in all states -> multiply
		NodeSet<std::string> childs = InterpreterImpl::getChildStates(root);
		complexity.value = 1;
		for (int i = 0; i < childs.size(); i++) {
			complexity *= calculateStateMachineComplexity(Element<std::string>(childs[i]), reachable);
		}
		if (hasDeepHistory) {
			complexity.history.push_back(complexity.value);
		}

	} else if (InterpreterImpl::isAtomic(root)) {
		return 1;
	}

	return complexity;
}

}