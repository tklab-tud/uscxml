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

#ifndef FSMTOSCXML_H_DC0B5E09
#define FSMTOSCXML_H_DC0B5E09

#include "ChartToFSM.h"
#include "Transformer.h"

namespace uscxml {

class USCXML_API ChartToFlatSCXML : public TransformerImpl, public ChartToFSM {
public:
	virtual ~ChartToFlatSCXML() {}
	static Transformer transform(const Interpreter& other);

	operator Interpreter();

	Arabica::DOM::Document<std::string> getDocument() const {
		return _flatDoc;
	}

protected:
	void writeTo(std::ostream& stream);
	
	ChartToFlatSCXML(const Interpreter& other) : TransformerImpl(), ChartToFSM(other), _lastTransientStateId(0) {}
	void createDocument();
	
	void appendGlobalStateNode(GlobalState* globalState);
	Arabica::DOM::Node<std::string> globalTransitionToNode(GlobalTransition* globalTransition);
	static bool sortStatesByIndex(const std::pair<std::string,GlobalState*>& s1, const std::pair<std::string,GlobalState*>& s2);

	size_t _lastTransientStateId;

};

}
#endif /* end of include guard: FSMTOSCXML_H_DC0B5E09 */
