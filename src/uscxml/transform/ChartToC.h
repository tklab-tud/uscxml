/**
 *  @file
 *  @author     2012-2016 Stefan Radomski (stefan.radomski@cs.tu-darmstadt.de)
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

#ifndef FSMTOCPP_H_201672B0
#define FSMTOCPP_H_201672B0

#include "uscxml/util/DOM.h"
#include "uscxml/transform/Trie.h"
#include "Transformer.h"

#include <xercesc/dom/DOM.hpp>
#include <ostream>
#include <set>

namespace uscxml {

class USCXML_API ChartToC : public TransformerImpl {
public:

	virtual ~ChartToC();
	static Transformer transform(const Interpreter& other);

	void writeTo(std::ostream& stream);

protected:
	ChartToC(const Interpreter& other);

	void writeIncludes(std::ostream& stream);
	void writeMacros(std::ostream& stream);
	void writeTypes(std::ostream& stream);
	void writeHelpers(std::ostream& stream);
	void writeExecContent(std::ostream& stream);
	void writeExecContentFinalize(std::ostream& stream);
	void writeElementInfoInvocation(std::ostream& stream);
	void writeForwardDeclarations(std::ostream& stream);

	void writeElementInfo(std::ostream& stream);

	void writeMachineInfo(std::ostream& stream);
	void writeStates(std::ostream& stream);
	void writeTransitions(std::ostream& stream);
	void writeFSM(std::ostream& stream);
	void writeCharArrayInitList(std::ostream& stream, const std::string& boolString);

	void writeExecContent(std::ostream& stream, const XERCESC_NS::DOMNode* node, size_t indent = 0);

	void resortStates(XERCESC_NS::DOMNode* node);
	void setHistoryCompletion();
	void setStateCompletion();
	void prepare();

	void findNestedMachines();

	Interpreter interpreter;

	std::vector<XERCESC_NS::DOMElement*> _states;
	std::vector<XERCESC_NS::DOMElement*> _transitions;

	std::string _md5;
	std::string _prefix;
	std::set<std::string> _hasElement;

	size_t _transCharArraySize;
	std::string _transCharArrayInit;
	std::string _transDataType;

	size_t _stateCharArraySize;
	std::string _stateCharArrayInit;
	std::string _stateDataType;

	ChartToC* _topMostMachine;
	ChartToC* _parentMachine;
	std::list<ChartToC*> _nestedMachines;
	std::list<ChartToC*> _allMachines;

	std::list<std::string>* _prefixes;
};

}

#endif /* end of include guard: FSMTOCPP_H_201672B0 */
