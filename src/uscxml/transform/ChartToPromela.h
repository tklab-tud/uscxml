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

#ifndef CHARTTOPROMELA_H_RP48RFDJ
#define CHARTTOPROMELA_H_RP48RFDJ

#include "Transformer.h"
#include "ChartToC.h"
#include "uscxml/util/DOM.h"

#include "promela/PromelaInlines.h"
#include "promela/PromelaCodeAnalyzer.h"

#include <ostream>

namespace uscxml {

class USCXML_API ChartToPromela : public ChartToC {
public:
	virtual ~ChartToPromela();
	static Transformer transform(const Interpreter& other);

	void writeTo(std::ostream& stream);

protected:
	ChartToPromela(const Interpreter& other) : ChartToC(other) {
        _prefix = "U" + _md5.substr(0, 8) + "_";
    }

	void writeTransitions(std::ostream& stream);
	void writeStates(std::ostream& stream);
    void writeTypeDefs(std::ostream& stream);
	void writeTypes(std::ostream& stream);
	void writeMacros(std::ostream& stream);
	void writeHelpers(std::ostream& stream);
	void writeFSM(std::ostream& stream);
	void writeExecContent(std::ostream& stream, const XERCESC_NS::DOMNode* node, size_t indent = 0);
    void writeStrings(std::ostream& stream);

    void writeCancelEvents(std::ostream& stream, int indent = 0);

    void prepare();
    
	void bit_clear_all(std::ostream& stream,
	                   const std::string& identifier,
	                   size_t length,
	                   size_t indent = 0);

	void bit_copy(std::ostream& stream,
	              const std::string& from,
	              const std::string& to,
	              size_t length,
	              size_t indent = 0);

	void bit_or(std::ostream& stream,
	            const std::string& to,
	            const std::string& mask,
	            size_t length,
	            size_t indent = 0);

	void bit_and(std::ostream& stream,
	             const std::string& to,
	             const std::string& mask,
	             size_t length,
	             size_t indent = 0);

	void bit_and_not(std::ostream& stream,
	                 const std::string& to,
	                 const std::string& mask,
	                 size_t length,
	                 size_t indent = 0);

	void bit_has_and(std::ostream& stream,
	                 const std::string& a,
	                 const std::string& b,
	                 size_t length,
	                 size_t indent = 0);

	void printBitArray(std::ostream& stream,
	                   const std::string& array,
	                   size_t length,
	                   size_t indent = 0);

	PromelaCodeAnalyzer _analyzer;

	ChartToPromela* _parentTopMost;
	ChartToPromela* _parent;
	std::string _invokerid;

    size_t _internalQueueLength = 7;
    size_t _externalQueueLength = 7;
    bool _allowEventInterleaving = false;
    
	std::map<std::string, XERCESC_NS::DOMNode* > _machinesPerId;
	std::map<std::string, XERCESC_NS::DOMNode* >* _machinesAllPerId = NULL;
	std::map<XERCESC_NS::DOMNode*, ChartToPromela*> _machines;
	std::map<XERCESC_NS::DOMNode*, ChartToPromela*>* _machinesAll = NULL;

	std::set<std::string> _dataModelVars;
    std::list<std::string> _varInitializers; // pending initializations for arrays

	std::string beautifyIndentation(const std::string& code, size_t indent = 0);
	void writeIfBlock(std::ostream& stream, std::list<XERCESC_NS::DOMElement*>& condChain, size_t indent = 0);

	std::string dataToAssignments(const std::string& prefix, const Data& data);
	std::string sanitizeCode(const std::string& code);
	std::string declForRange(const std::string& identifier, long minValue, long maxValue, bool nativeOnly = false);

	friend class PromelaCodeAnalyzer;
};

}

#endif /* end of include guard: CHARTTOPROMELA_H_RP48RFDJ */
