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

#ifndef CHARTTOTEX_H_2B7D5889
#define CHARTTOTEX_H_2B7D5889


#include "Transformer.h"
#include "ChartToFSM.h"
#include "uscxml/Interpreter.h"
#include "uscxml/DOMUtils.h"
#include "uscxml/util/Trie.h"

#include <DOM/Document.hpp>
#include <DOM/Node.hpp>
#include <XPath/XPath.hpp>
#include <ostream>

namespace uscxml {

class USCXML_API ChartToTex : public TransformerImpl, public ChartToFSM {
public:

	virtual ~ChartToTex();
	static Transformer transform(const Interpreter& other);

	void writeTo(std::ostream& stream);

protected:
	ChartToTex(const Interpreter& other)
		: TransformerImpl(),
		  ChartToFSM(other) {}

	void writeTex(std::ostream& stream);

	std::map<unsigned long, GlobalState*> _indexToState;

private:
	static std::string stateListToTex(const std::string& input, bool isEmpty);
	static std::string texEscape(const std::string& input);
};

}

#endif /* end of include guard: CHARTTOTEX_H_2B7D5889 */
