/**
 *  @file
 *  @author     2015-2016 Jens Heuschkel (heuschkel@tk.tu-darmstadt.de)
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

#ifndef CHARTOVHDL_H
#define CHARTOVHDL_H

#include "uscxml/interpreter/InterpreterDraft6.h"
#include "uscxml/DOMUtils.h"
#include "uscxml/util/Trie.h"
#include "Transformer.h"
#include "ChartToC.h"

#include <DOM/Document.hpp>
#include <DOM/Node.hpp>
#include <XPath/XPath.hpp>
#include <ostream>

namespace uscxml {

class USCXML_API ChartToVHDL : public ChartToC {
public:

	virtual ~ChartToVHDL();
	static Transformer transform(const Interpreter& other);

	void writeTo(std::ostream& stream);

protected:
	ChartToVHDL(const Interpreter& other);

	void checkDocument();
	void findEvents();

	void writeIncludes(std::ostream& stream);
	void writeTopDown(std::ostream& stream);

	void writeTypes(std::ostream& stream);

	void writeOptimalTransitionSetSelection(std::ostream& stream);
	void writeExitSet(std::ostream & stream);
	void writeEntrySet(std::ostream & stream);

	void writeNextStateLogic(std::ostream& stream);
	void writeOutputLogic(std::ostream& stream);
	void writeSignals(std::ostream& stream);
	void writeFiFo(std::ostream& stream);
	void writeModuleInstantiation(std::ostream& stream);
	void writeErrorHandler(std::ostream& stream);
	void writeFSM(std::ostream& stream);

	void writeTransitionSet(std::ostream & stream);

	Trie _eventTrie;

private:
	std::string eventNameEscape(const std::string& eventName);


};

}

#endif /* end of include guard: FSMTOCPP_H_201672B0 */
