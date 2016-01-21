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

#include <DOM/Document.hpp>
#include <DOM/Node.hpp>
#include <XPath/XPath.hpp>
#include <ostream>

namespace uscxml {

    class USCXML_API ChartToVHDL : public InterpreterRC, public TransformerImpl {
    public:

        virtual ~ChartToVHDL();
        static Transformer transform(const Interpreter& other);

        void writeTo(std::ostream& stream);

        static Arabica::XPath::NodeSet<std::string> inPostFixOrder(const std::set<std::string>& elements,
                const Arabica::DOM::Element<std::string>& root);
        static Arabica::XPath::NodeSet<std::string> inDocumentOrder(const std::set<std::string>& elements,
                const Arabica::DOM::Element<std::string>& root);
    protected:
        ChartToVHDL(const Interpreter& other);

        static void inPostFixOrder(const std::set<std::string>& elements,
                const Arabica::DOM::Element<std::string>& root,
                Arabica::XPath::NodeSet<std::string>& nodes);

        static void inDocumentOrder(const std::set<std::string>& elements,
                const Arabica::DOM::Element<std::string>& root,
                Arabica::XPath::NodeSet<std::string>& nodes);

        Arabica::XPath::NodeSet<std::string> computeExitSet(
                const Arabica::DOM::Element<std::string>& transition);

        void writeIncludes(std::ostream& stream);
        void writeTopDown(std::ostream& stream);

        void writeTypes(std::ostream& stream);
        void writeNextStateLogic(std::ostream& stream);
        void writeOutputLogic(std::ostream& stream);
        void writeSignals(std::ostream& stream);
        void writeFiFo(std::ostream& stream);
        void writeModuleInstantiation(std::ostream& stream);
        void writeErrorHandler(std::ostream& stream);
        void writeFSM(std::ostream& stream);
        void writeTestbench(std::ostream& stream);



        Interpreter interpreter;

        std::string _initState;
        Arabica::XPath::NodeSet<std::string> _states;
        std::map<std::string, Arabica::DOM::Element<std::string> > _stateNames;
        Arabica::XPath::NodeSet<std::string> _transitions;
        std::map<std::string, Arabica::DOM::Element<std::string> > _transitionNames;
        std::vector<std::string> _events;
        Arabica::XPath::NodeSet<std::string> _compoundStates;
        Arabica::XPath::NodeSet<std::string> _parallelStates;
        Arabica::XPath::NodeSet<std::string> _finalStates;
        Arabica::XPath::NodeSet<std::string> _superFinalStates;

        bool _hasGlobalScripts;
        bool _hasDoneData;

        size_t _transCharArraySize;
        std::string _transCharArrayInit;

        size_t _stateCharArraySize;
        std::string _stateCharArrayInit;
    };

}

#endif /* end of include guard: FSMTOCPP_H_201672B0 */
