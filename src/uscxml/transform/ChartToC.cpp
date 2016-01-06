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

#include "uscxml/transform/ChartToFSM.h"
#include "uscxml/transform/ChartToC.h"
#include "uscxml/debug/Complexity.h"
#include <DOM/io/Stream.hpp>
#include <iostream>
#include "uscxml/UUID.h"
#include "uscxml/DOMUtils.h"
#include <math.h>
#include <boost/algorithm/string.hpp>
#include <glog/logging.h>

#include <algorithm>
#include <iomanip>

namespace uscxml {

using namespace Arabica::DOM;
using namespace Arabica::XPath;
    
Transformer ChartToC::transform(const Interpreter& other) {
    ChartToC* c2c = new ChartToC(other);
    
    return boost::shared_ptr<TransformerImpl>(c2c);
}

ChartToC::ChartToC(const Interpreter& other) : TransformerImpl() {
    cloneFrom(other.getImpl());
}

void ChartToC::writeTo(std::ostream& stream) {
    _binding = (HAS_ATTR(_scxml, "binding") && iequals(ATTR(_scxml, "binding"), "late") ? LATE : EARLY);

    std::set<std::string> elements;
    elements.insert(_nsInfo.xmlNSPrefix + "scxml");
    elements.insert(_nsInfo.xmlNSPrefix + "state");
    elements.insert(_nsInfo.xmlNSPrefix + "final");
    elements.insert(_nsInfo.xmlNSPrefix + "parallel");
    elements.insert(_nsInfo.xmlNSPrefix + "history");
    elements.insert(_nsInfo.xmlNSPrefix + "initial");
    elements.insert(_nsInfo.xmlNSPrefix + "parallel");
    _states = inDocumentOrder(elements, _scxml);
    
    for (int i = 0; i < _states.size(); i++) {
        Element<std::string> state(_states[i]);
        state.setAttribute("documentOrder", toStr(i));
        if (HAS_ATTR(state, "id")) {
            _stateNames[ATTR(state, "id")] = state;
        }
    }

    elements.clear();
    elements.insert(_nsInfo.xmlNSPrefix + "transition");
    _transitions = inPostFixOrder(elements, _scxml);

    for (int i = 0; i < _transitions.size(); i++) {
        Element<std::string> transition(_transitions[i]);
        transition.setAttribute("postFixOrder", toStr(i));
    }
    
    // how many bits do we need to represent the state array?
    std::string seperator;
    _stateCharArraySize = ceil((float)_states.size() / (float)8);
    _stateCharArrayInit = "{";
    for (int i = 0; i < _stateCharArraySize; i++) {
        _stateCharArrayInit += seperator + "0";
        seperator = ", ";
    }
    _stateCharArrayInit += "}";

    seperator = "";
    _transCharArraySize = ceil((float)_transitions.size() / (float)8);
    _transCharArrayInit = "{";
    for (int i = 0; i < _transCharArraySize; i++) {
        _transCharArrayInit += seperator + "0";
        seperator = ", ";
    }
    _transCharArrayInit += "}";
    
    writeIncludes(stream);
    writeMacros(stream);
    writeTypes(stream);
    writeElementInfo(stream);
    writeExecContent(stream);
    writeStates(stream);
    writeTransitions(stream);
    writeHelpers(stream);
    writeFSM(stream);
    
    //    http://stackoverflow.com/questions/2525310/how-to-define-and-work-with-an-array-of-bits-in-c
    
}

void ChartToC::writeIncludes(std::ostream& stream) {
    stream << "#include <stdint.h> // explicit types" << std::endl;
    stream << "#include <stddef.h> // NULL" << std::endl;
    stream << std::endl;
}

void ChartToC::writeMacros(std::ostream& stream) {
    stream << "#define IS_SET(idx, bitset)   ((bitset[idx >> 3] &  (1 << (idx & 7))) != 0)" << std::endl;
    stream << "#define SET_BIT(idx, bitset)    bitset[idx >> 3] |= (1 << (idx & 7));" << std::endl;
    stream << "#define CLEARBIT(idx, bitset)   bitset[idx >> 3] &= (1 << (idx & 7)) ^ 0xFF;" << std::endl;
    stream << std::endl;
    
    stream << "// error return codes" << std::endl;
    stream << "#define SCXML_ERR_OK                0" << std::endl;
    stream << "#define SCXML_ERR_IDLE              1" << std::endl;
    stream << "#define SCXML_ERR_DONE              2" << std::endl;
    stream << "#define SCXML_ERR_MISSING_CALLBACK  3" << std::endl;
    stream << "#define SCXML_ERR_FOREACH_DONE      4" << std::endl;
    stream << "#define SCXML_ERR_EXEC_CONTENT      5" << std::endl;
    stream << "#define SCXML_ERR_INVALID_TARGET    6" << std::endl;
    stream << "#define SCXML_ERR_INVALID_TYPE      7" << std::endl;
    stream << std::endl;

    stream << "#define SCXML_NUMBER_STATES " << _states.size() << std::endl;
    stream << "#define SCXML_NUMBER_TRANSITIONS " << _transitions.size() << std::endl;
    stream << std::endl;
    
    stream << "#define SCXML_TRANS_SPONTANEOUS      0x01" << std::endl;
    stream << "#define SCXML_TRANS_TARGETLESS       0x02" << std::endl;
    stream << "#define SCXML_TRANS_INTERNAL         0x04" << std::endl;
    stream << std::endl;

    stream << "#define SCXML_STATE_ATOMIC           0x01" << std::endl;
    stream << "#define SCXML_STATE_PARALLEL         0x02" << std::endl;
    stream << "#define SCXML_STATE_COMPOUND         0x03" << std::endl;
    stream << "#define SCXML_STATE_FINAL            0x04" << std::endl;
    stream << "#define SCXML_STATE_HISTORY_DEEP     0x05" << std::endl;
    stream << "#define SCXML_STATE_HISTORY_SHALLOW  0x06" << std::endl;
    stream << "#define SCXML_STATE_INITIAL          0x07" << std::endl;

    stream << "" << std::endl;
    stream << "#define SCXML_CTX_PRISTINE           0x00" << std::endl;
    stream << "#define SCXML_CTX_SPONTANEOUS        0x01" << std::endl;
    stream << "#define SCXML_CTX_INITIALIZED        0x02" << std::endl;
    stream << "#define SCXML_CTX_TOP_LEVEL_FINAL    0x04" << std::endl;
    stream << "#define SCXML_CTX_TRANSITION_FOUND   0x08" << std::endl;
    stream << std::endl;

    stream << "#define ELEM_DATA_IS_SET(data) (data->id != NULL)" << std::endl;
    stream << "#define ELEM_PARAM_IS_SET(param) (param->name != NULL)" << std::endl;
    stream << std::endl;
}

void ChartToC::writeTypes(std::ostream& stream) {
    
    stream << std::endl;
    stream << "typedef struct scxml_transition scxml_transition;" << std::endl;
    stream << "typedef struct scxml_state scxml_state;" << std::endl;
    stream << "typedef struct scxml_ctx scxml_ctx;" << std::endl;
    stream << "typedef struct scxml_invoke scxml_invoke;" << std::endl;
    
    stream << std::endl;

    stream << "typedef struct scxml_elem_send scxml_elem_send;" << std::endl;
    stream << "typedef struct scxml_elem_param scxml_elem_param;" << std::endl;
    stream << "typedef struct scxml_elem_data scxml_elem_data;" << std::endl;
    stream << "typedef struct scxml_elem_foreach scxml_elem_foreach;" << std::endl;
    stream << std::endl;
    
    stream << "typedef void* (*dequeue_internal_cb_t)(const scxml_ctx* ctx);" << std::endl;
    stream << "typedef void* (*dequeue_external_cb_t)(const scxml_ctx* ctx);" << std::endl;
    stream << "typedef int (*is_enabled_cb_t)(const scxml_ctx* ctx, const scxml_transition* transition, const void* event);" << std::endl;
    stream << "typedef int (*is_true_cb_t)(const scxml_ctx* ctx, const char* expr);" << std::endl;
    stream << "typedef int (*exec_content_t)(const scxml_ctx* ctx, const scxml_state* state, const void* event);" << std::endl;
    stream << "typedef int (*raise_done_event_t)(const scxml_ctx* ctx, const scxml_state* state);" << std::endl;
    stream << "typedef int (*invoke_t)(const scxml_ctx* ctx, const scxml_state* s, const scxml_invoke* x);" << std::endl;
    stream << std::endl;

    stream << "typedef int (*exec_content_log_t)(const scxml_ctx* ctx, const char* label, const char* expr);" << std::endl;
    stream << "typedef int (*exec_content_raise_t)(const scxml_ctx* ctx, const char* event);" << std::endl;
    stream << "typedef int (*exec_content_send_t)(const scxml_ctx* ctx, const scxml_elem_send* send);" << std::endl;
    stream << "typedef int (*exec_content_foreach_init_t)(const scxml_ctx* ctx, const scxml_elem_foreach* foreach);" << std::endl;
    stream << "typedef int (*exec_content_foreach_next_t)(const scxml_ctx* ctx, const scxml_elem_foreach* foreach);" << std::endl;
    stream << "typedef int (*exec_content_foreach_done_t)(const scxml_ctx* ctx, const scxml_elem_foreach* foreach);" << std::endl;
    stream << "typedef int (*exec_content_assign_t)(const scxml_ctx* ctx, const char* location, const char* expr);" << std::endl;
    stream << "typedef int (*exec_content_init_t)(const scxml_ctx* ctx, const scxml_elem_data* data);" << std::endl;
    stream << "typedef int (*exec_content_cancel_t)(const scxml_ctx* ctx, const char* sendid, const char* sendidexpr);" << std::endl;
    stream << "typedef int (*exec_content_finalize_t)(const scxml_ctx* ctx, const scxml_invoke* invoker, const void* event);" << std::endl;
    stream << "typedef int (*exec_content_script_t)(const scxml_ctx* ctx, const char* src, const char* content);" << std::endl;
    stream << std::endl;

    stream << "struct scxml_elem_data {" << std::endl;
    stream << "    const char* id;" << std::endl;
    stream << "    const char* src;" << std::endl;
    stream << "    const char* expr;" << std::endl;
    stream << "    const char* content;" << std::endl;
    stream << "};" << std::endl;
    stream << std::endl;

    stream << "struct scxml_state {" << std::endl;
    stream << "    const char* name; // eventual name" << std::endl;
    stream << "    exec_content_t on_entry; // on entry handlers" << std::endl;
    stream << "    exec_content_t on_exit; // on exit handlers" << std::endl;
    stream << "    invoke_t invoke; // invocations" << std::endl;
    stream << "    char children[" << _stateCharArraySize << "]; // all children" << std::endl;
    stream << "    char completion[" << _stateCharArraySize << "]; // default completion" << std::endl;
    stream << "    char ancestors[" << _stateCharArraySize << "]; // all ancestors" << std::endl;
    stream << "    const scxml_elem_data* data;" << std::endl;
    stream << "    uint8_t type; // atomic, parallel, compound, final, history" << std::endl;
    stream << "};" << std::endl;
    stream << std::endl;
    
    stream << "struct scxml_transition {" << std::endl;
    stream << "    uint16_t source;" << std::endl;
    stream << "    char target[" << _stateCharArraySize << "];" << std::endl;
    stream << "    const char* event;" << std::endl;
    stream << "    const char* condition;" << std::endl;
    stream << "    exec_content_t on_transition;" << std::endl;
    stream << "    uint8_t type;" << std::endl;
    stream << "    char conflicts[" << _transCharArraySize << "];" << std::endl;
    stream << "    char exit_set[" << _stateCharArraySize << "];" << std::endl;
    stream << "};" << std::endl;
    stream << std::endl;
    
    stream << "struct scxml_elem_foreach {" << std::endl;
    stream << "    const char* array;" << std::endl;
    stream << "    const char* item;" << std::endl;
    stream << "    const char* index;" << std::endl;
    stream << "};" << std::endl;
    stream << std::endl;

    stream << "struct scxml_elem_param {" << std::endl;
    stream << "    const char* name;" << std::endl;
    stream << "    const char* expr;" << std::endl;
    stream << "    const char* location;" << std::endl;
    stream << "};" << std::endl;
    stream << std::endl;

    stream << "struct scxml_elem_invoke {" << std::endl;
    stream << "    const char* type;" << std::endl;
    stream << "    const char* typeexpr;" << std::endl;
    stream << "    const char* src;" << std::endl;
    stream << "    const char* srcexpr;" << std::endl;
    stream << "    const char* id;" << std::endl;
    stream << "    const char* idlocation;" << std::endl;
    stream << "    const char* namelist;" << std::endl;
    stream << "    uint8_t autoforward;" << std::endl;
    stream << "    const scxml_elem_param* params;" << std::endl;
    stream << "    const exec_content_finalize_t* finalize;" << std::endl;
    stream << "    const char* content;" << std::endl;
    stream << "    void* user_data;" << std::endl;
    stream << "};" << std::endl;
    stream << std::endl;

    stream << "struct scxml_elem_send {" << std::endl;
    stream << "    const char* event;" << std::endl;
    stream << "    const char* eventexpr;" << std::endl;
    stream << "    const char* target;" << std::endl;
    stream << "    const char* targetexpr;" << std::endl;
    stream << "    const char* type;" << std::endl;
    stream << "    const char* typeexpr;" << std::endl;
    stream << "    const char* id;" << std::endl;
    stream << "    const char* idlocation;" << std::endl;
    stream << "    const char* delay;" << std::endl;
    stream << "    const char* delayexpr;" << std::endl;
    stream << "    const char* namelist;" << std::endl;
    stream << "    const char* content;" << std::endl;
    stream << "    const scxml_elem_param* params;" << std::endl;
    stream << "    void* user_data;" << std::endl;
    stream << "};" << std::endl;
    stream << std::endl;

    stream << "struct scxml_ctx {" << std::endl;
    stream << "    uint8_t flags;" << std::endl;
    stream << std::endl;
    stream << "    char config[" << _stateCharArraySize << "];" << std::endl;
    stream << "    char history[" << _stateCharArraySize << "];" << std::endl;
    stream << "    char pending_invokes[" << _stateCharArraySize << "];" << std::endl;
    stream << "    char initialized_data[" << _stateCharArraySize << "];" << std::endl;
    stream << std::endl;
    stream << "    void* user_data;" << std::endl;
    stream << std::endl;
    stream << "    dequeue_internal_cb_t dequeue_internal;" << std::endl;
    stream << "    dequeue_external_cb_t dequeue_external;" << std::endl;
    stream << "    is_enabled_cb_t is_enabled;" << std::endl;
    stream << "    is_true_cb_t is_true;" << std::endl;
    stream << "    raise_done_event_t raise_done_event;" << std::endl;
    stream << std::endl;
    stream << "    exec_content_log_t exec_content_log;" << std::endl;
    stream << "    exec_content_raise_t exec_content_raise;" << std::endl;
    stream << "    exec_content_send_t exec_content_send;" << std::endl;
    stream << "    exec_content_foreach_init_t exec_content_foreach_init;" << std::endl;
    stream << "    exec_content_foreach_next_t exec_content_foreach_next;" << std::endl;
    stream << "    exec_content_foreach_done_t exec_content_foreach_done;" << std::endl;
    stream << "    exec_content_assign_t exec_content_assign;" << std::endl;
    stream << "    exec_content_init_t exec_content_init;" << std::endl;
    stream << "    exec_content_cancel_t exec_content_cancel;" << std::endl;
    stream << "    exec_content_script_t exec_content_script;" << std::endl;
    stream << "    invoke_t invoke;" << std::endl;
    stream << "};" << std::endl;
    stream << std::endl;
}

void ChartToC::writeHelpers(std::ostream& stream) {
    stream << "#ifdef SCXML_VERBOSE" << std::endl;
    stream << "void printStateNames(const char* a) {" << std::endl;
    stream << "    const char* seperator = \"\";" << std::endl;
    stream << "    for (int i = 0; i < SCXML_NUMBER_STATES; i++) {" << std::endl;
    stream << "        if (IS_SET(i, a)) {" << std::endl;
    stream << "            printf(\"%s%s\", seperator, (scxml_states[i].name != NULL ? scxml_states[i].name : \"UNK\"));" << std::endl;
    stream << "            seperator = \", \";" << std::endl;
    stream << "        }" << std::endl;
    stream << "    }" << std::endl;
    stream << "    printf(\"\\n\");" << std::endl;
    stream << "}" << std::endl;
    stream << std::endl;

    stream << "void printBitsetIndices(const char* a, size_t length) {" << std::endl;
    stream << "    const char* seperator = \"\";" << std::endl;
    stream << "    for (int i = 0; i < length; i++) {" << std::endl;
    stream << "        if (IS_SET(i, a)) {" << std::endl;
    stream << "            printf(\"%s%d\", seperator, i);" << std::endl;
    stream << "            seperator = \", \";" << std::endl;
    stream << "        }" << std::endl;
    stream << "    }" << std::endl;
    stream << "    printf(\"\\n\");" << std::endl;
    stream << "}" << std::endl;

    stream << "#endif" << std::endl;
    stream << std::endl;
    
    stream << "void bit_or(char* dest, const char* mask, size_t length) {" << std::endl;
    stream << "    for (int i = 0; i < length; ++i) {" << std::endl;
    stream << "        dest[i] |= mask[i];" << std::endl;
    stream << "    }" << std::endl;
    stream << "}" << std::endl;
    stream << std::endl;

    stream << "void bit_copy(char* dest, const char* source, size_t length) {" << std::endl;
    stream << "    for (int i = 0; i < length; ++i) {" << std::endl;
    stream << "        dest[i] = source[i];" << std::endl;
    stream << "    }" << std::endl;
    stream << "}" << std::endl;
    stream << std::endl;
    
    stream << "int bit_has_and(const char* a, const char* b, size_t length) {" << std::endl;
    stream << "    for (int i = 0; i < length; ++i) {" << std::endl;
    stream << "        if (a[i] & b[i])" << std::endl;
    stream << "            return true;" << std::endl;
    stream << "    }" << std::endl;
    stream << "    return false;" << std::endl;
    stream << "}" << std::endl;
    stream << std::endl;

    stream << "void bit_and_not(char* dest, const char* mask, size_t length) {" << std::endl;
    stream << "    for (int i = 0; i < length; ++i) {" << std::endl;
    stream << "        dest[i] &= ~mask[i];" << std::endl;
    stream << "    }" << std::endl;
    stream << "}" << std::endl;
    stream << std::endl;

    stream << "int bit_any_set(const char* a, size_t length) {" << std::endl;
    stream << "    for (int i = 0; i < length; ++i) {" << std::endl;
    stream << "        if (a[i] > 0)" << std::endl;
    stream << "            return true;" << std::endl;
    stream << "    }" << std::endl;
    stream << "    return false;" << std::endl;
    stream << "}" << std::endl;
    stream << std::endl;

}
    
void ChartToC::writeExecContent(std::ostream& stream) {
    for (int i = 0; i < _states.size(); i++) {
        Element<std::string> state(_states[i]);
        
        NodeSet<std::string> onexit = filterChildElements(_nsInfo.xmlNSPrefix + "onexit", state);
        for (int j = 0; j < onexit.size(); j++) {
            stream << "int " << DOMUtils::idForNode(state) << "_on_exit_" << toStr(j) << "(const scxml_ctx* ctx, const scxml_state* state, const void* event) {" << std::endl;
            stream << "    int err = SCXML_ERR_OK;" << std::endl;
            writeExecContent(stream, onexit[j], 1);
            stream << "    return SCXML_ERR_OK;" << std::endl;
            stream << "}" << std::endl;
            stream << std::endl;
        }

        if (onexit.size() > 0) {
            stream << "int " << DOMUtils::idForNode(state) << "_on_exit(const scxml_ctx* ctx, const scxml_state* state, const void* event) {" << std::endl;
            for (int j = 0; j < onexit.size(); j++) {
                stream << "    " << DOMUtils::idForNode(state) << "_on_exit_" << toStr(j) << "(ctx, state, event);" << std::endl;
            }
            stream << "    return SCXML_ERR_OK;" << std::endl;
            stream << "}" << std::endl;
            stream << std::endl;
        }
        
        
        NodeSet<std::string> onentry = filterChildElements(_nsInfo.xmlNSPrefix + "onentry", state);
        for (int j = 0; j < onentry.size(); j++) {
            stream << "int " << DOMUtils::idForNode(state) << "_on_entry_" << toStr(j) << "(const scxml_ctx* ctx, const scxml_state* state, const void* event) {" << std::endl;
            stream << "    int err = SCXML_ERR_OK;" << std::endl;
            writeExecContent(stream, onentry[j], 1);
            stream << "    return SCXML_ERR_OK;" << std::endl;
            stream << "}" << std::endl;
            stream << std::endl;
        }

        bool hasInitialState = false;
        NodeSet<std::string> initial = filterChildElements(_nsInfo.xmlNSPrefix + "initial", state);
        if (initial.size() > 0) {
            NodeSet<std::string> initialTransition = filterChildElements(_nsInfo.xmlNSPrefix + "transition", initial);
            if (initialTransition.size() > 0) {
                hasInitialState = true;
                stream << "int " << DOMUtils::idForNode(state) << "_initial" << "(const scxml_ctx* ctx, const scxml_state* state, const void* event) {" << std::endl;
                stream << "    int err = SCXML_ERR_OK;" << std::endl;
                writeExecContent(stream, initialTransition[0], 1);
                stream << "    return SCXML_ERR_OK;" << std::endl;
                stream << "}" << std::endl;
                stream << std::endl;
            }
        }
        
        
        if (onentry.size() > 0) {
            stream << "int " << DOMUtils::idForNode(state) << "_on_entry(const scxml_ctx* ctx, const scxml_state* state, const void* event) {" << std::endl;
            for (int j = 0; j < onentry.size(); j++) {
                stream << "    " << DOMUtils::idForNode(state) << "_on_entry_" << toStr(j) << "(ctx, state, event);" << std::endl;
            }
            if (hasInitialState) {
                stream << "    " << DOMUtils::idForNode(state) << "_initial" << "(ctx, state, event);" << std::endl;
            }
            
            stream << "    return SCXML_ERR_OK;" << std::endl;
            stream << "}" << std::endl;
            stream << std::endl;
        }


        NodeSet<std::string> invoke = filterChildElements(_nsInfo.xmlNSPrefix + "invoke", state);
        if (invoke.size() > 0) {
            stream << "int " << DOMUtils::idForNode(state) << "_invoke(const scxml_ctx* ctx, const scxml_state* s, const scxml_invoke* x) {" << std::endl;
            for (int j = 0; j < invoke.size(); j++) {
                stream << "    ctx->invoke(ctx, s, x);" << std::endl;
                stream << "    return SCXML_ERR_OK;" << std::endl;
                stream << std::endl;
            }
            stream << "}" << std::endl;
        }
    }
    
    for (int i = 0; i < _transitions.size(); i++) {
        Element<std::string> transition(_transitions[i]);
        if (iequals(TAGNAME_CAST(transition.getParentNode()), "initial"))
            continue;
        
        NodeSet<std::string> execContent = filterChildType(Node_base::ELEMENT_NODE, transition);

        if (execContent.size() > 0) {
            stream << "int " << DOMUtils::idForNode(transition) << "_on_trans(const scxml_ctx* ctx, const scxml_state* state, const void* event) {" << std::endl;
            stream << "    int err = SCXML_ERR_OK;" << std::endl;
            writeExecContent(stream, Element<std::string>(execContent[0]), 1);
            stream << "    return SCXML_ERR_OK;" << std::endl;
            stream << "}" << std::endl;
            stream << std::endl;
        }
    }
}

void ChartToC::writeExecContent(std::ostream& stream, const Arabica::DOM::Node<std::string>& node, int indent) {
    if (!node)
        return;
    
    if (node.getNodeType() == Node_base::TEXT_NODE) {
        if (boost::trim_copy(node.getNodeValue()).length() > 0) {
            std::string escaped = escape(node.getNodeValue());
            stream << escaped;
        }
        return;
    }

    std::string padding;
    for (int i = 0; i < indent; i++) {
        padding += "    ";
    }


    if (node.getNodeType() != Node_base::ELEMENT_NODE)
        return; // skip anything not an element

    Arabica::DOM::Element<std::string> elem = Arabica::DOM::Element<std::string>(node);
    
    if (false) {
    } else if(TAGNAME(elem) == "onentry" || TAGNAME(elem) == "onexit" || TAGNAME(elem) == "transition" || TAGNAME(elem) == "finalize") {
        // descent into childs and write their contents
        Arabica::DOM::Node<std::string> child = node.getFirstChild();
        while(child) {
            writeExecContent(stream, child, indent);
            child = child.getNextSibling();
        }
    } else if(TAGNAME(elem) == "script") {
        stream << padding;
        stream << "if (ctx->exec_content_script != NULL) {" << std::endl;
        stream << padding;
        stream << "    if ((err = ctx->exec_content_script(ctx, ";
        stream << (HAS_ATTR(elem, "src") ? "\"" + escape(ATTR(elem, "src")) + "\"" : "NULL") << ", ";

        NodeSet<std::string> scriptTexts = filterChildType(Node_base::TEXT_NODE, elem);
        if (scriptTexts.size() > 0) {
            stream << "\"";
            writeExecContent(stream, scriptTexts[0], 0);
            stream << "\"";
        } else {
            stream << "NULL";
        }

        stream << ")) != SCXML_ERR_OK) return err" << std::endl;
        stream << padding << "} else {" << std::endl;
        stream << padding << "    return SCXML_ERR_MISSING_CALLBACK;" << std::endl;
        stream << padding << "}" << std::endl;
        
    } else if(TAGNAME(elem) == "log") {
        stream << padding;
        stream << "if (ctx->exec_content_log != NULL) {" << std::endl;
        stream << padding;
        stream << "    if ((ctx->exec_content_log(ctx, ";
        stream << (HAS_ATTR(elem, "label") ? "\"" + escape(ATTR(elem, "label")) + "\"" : "NULL") << ", ";
        stream << (HAS_ATTR(elem, "expr") ? "\"" + escape(ATTR(elem, "expr")) + "\"" : "NULL");
        stream << ")) != SCXML_ERR_OK) return err;" << std::endl;
        stream << padding << "} else {" << std::endl;
        stream << padding << "    return SCXML_ERR_MISSING_CALLBACK;" << std::endl;
        stream << padding << "}" << std::endl;

    } else if(TAGNAME(elem) == "foreach") {
        stream << padding << "if (ctx->exec_content_foreach_init != NULL &&" << std::endl;
        stream << padding << "    ctx->exec_content_foreach_next != NULL &&" << std::endl;
        stream << padding << "    ctx->exec_content_foreach_done != NULL) {" << std::endl;
        stream << std::endl;

        stream << padding << "    if ((ctx->exec_content_foreach_init(ctx, &scxml_elem_foreachs[" << ATTR(elem, "documentOrder") << "])) != SCXML_ERR_OK) return err;" << std::endl;
        stream << padding << "    while (ctx->exec_content_foreach_next(ctx, &scxml_elem_foreachs[" << ATTR(elem, "documentOrder") << "]) == SCXML_ERR_OK) {" << std::endl;
        Arabica::DOM::Node<std::string> child = node.getFirstChild();
        while(child) {
            writeExecContent(stream, child, indent + 2);
            child = child.getNextSibling();
        }
        stream << padding << "    }" << std::endl;
        stream << padding << "    if ((ctx->exec_content_foreach_done(ctx, &scxml_elem_foreachs[" << ATTR(elem, "documentOrder") << "])) != SCXML_ERR_OK) return err;" << std::endl;
        stream << padding << "} else {" << std::endl;
        stream << padding << "    return SCXML_ERR_MISSING_CALLBACK;" << std::endl;
        stream << padding << "}" << std::endl;

    } else if(TAGNAME(elem) == "if") {
        stream << padding;
        stream << "if (ctx->is_true != NULL) {" << std::endl;
        stream << padding;
        stream << "    if (ctx->is_true(ctx, " << (HAS_ATTR(elem, "cond") ? "\"" + escape(ATTR(elem, "cond")) + "\"" : "NULL") << ")) {" << std::endl;
        Arabica::DOM::Node<std::string> child = elem.getFirstChild();
        while(child) {
            if (child.getNodeType() == Node_base::ELEMENT_NODE && TAGNAME_CAST(child) == "elseif") {
                stream << padding;
                stream << "    } else if (ctx->is_true(ctx, " << (HAS_ATTR_CAST(child, "cond") ? "\"" + escape(ATTR_CAST(child, "cond")) + "\"" : "NULL") << ")) {" << std::endl;
            } else if (child.getNodeType() == Node_base::ELEMENT_NODE && TAGNAME_CAST(child) == "else") {
                stream << padding;
                stream << "    } else {" << std::endl;
            } else {
                writeExecContent(stream, child, indent + 2);
            }
            child = child.getNextSibling();
        }
        stream << padding << "    }" << std::endl;
        stream << padding << "} else {" << std::endl;
        stream << padding << "    return SCXML_ERR_MISSING_CALLBACK;" << std::endl;
        stream << padding << "}" << std::endl;

    } else if(TAGNAME(elem) == "assign") {
        stream << padding;
        stream << "if (ctx->exec_content_assign != NULL) {" << std::endl;
        stream << padding;
        stream << "    if ((ctx->exec_content_assign(ctx, ";
        stream << (HAS_ATTR(elem, "location") ? "\"" + escape(ATTR(elem, "location")) + "\"" : "NULL") << ", ";
        if (HAS_ATTR(elem, "expr")) {
            stream << "\"" + escape(ATTR(elem, "expr")) + "\"";
        } else {
            NodeSet<std::string> assignTexts = filterChildType(Node_base::TEXT_NODE, elem);
            if (assignTexts.size() > 0) {
                stream << "\"";
                writeExecContent(stream, assignTexts[0], 0);
                stream << "\"";
            } else {
                stream << "NULL";
            }
        }
        stream << ")) != SCXML_ERR_OK) return err;" << std::endl;
        stream << padding << "} else {" << std::endl;
        stream << padding << "    return SCXML_ERR_MISSING_CALLBACK;" << std::endl;
        stream << padding << "}" << std::endl;

        
    } else if(TAGNAME(elem) == "raise") {
        stream << padding;
        stream << "if (ctx->exec_content_raise != NULL) {" << std::endl;
        stream << padding;
        stream << "    if ((ctx->exec_content_raise(ctx, ";
        stream << (HAS_ATTR(elem, "event") ? "\"" + escape(ATTR(elem, "event")) + "\"" : "NULL");
        stream << ")) != SCXML_ERR_OK) return err;" << std::endl;
        stream << padding << "} else {" << std::endl;
        stream << padding << "    return SCXML_ERR_MISSING_CALLBACK;" << std::endl;
        stream << padding << "}" << std::endl;

    } else if(TAGNAME(elem) == "send") {
        stream << padding;
        stream << "if (ctx->exec_content_send != NULL) {" << std::endl;
        stream << padding;
        stream << "    if ((ctx->exec_content_send(ctx, &scxml_elem_sends[" << ATTR(elem, "documentOrder") << "]";
        stream << ")) != SCXML_ERR_OK) return err;" << std::endl;
        stream << padding << "} else {" << std::endl;
        stream << padding << "    return SCXML_ERR_MISSING_CALLBACK;" << std::endl;
        stream << padding << "}" << std::endl;

    } else if(TAGNAME(elem) == "cancel") {
        stream << padding;
        stream << "if (ctx->exec_content_cancel != NULL) {" << std::endl;
        stream << padding;
        stream << "    if ((ctx->exec_content_cancel(ctx, ";
        stream << (HAS_ATTR(elem, "sendid") ? "\"" + escape(ATTR(elem, "sendid")) + "\"" : "NULL") << ", ";
        stream << (HAS_ATTR(elem, "sendidexpr") ? "\"" + escape(ATTR(elem, "sendidexpr")) + "\"" : "NULL");
        stream << ")) != SCXML_ERR_OK) return err;" << std::endl;
        stream << padding << "} else {" << std::endl;
        stream << padding << "    return SCXML_ERR_MISSING_CALLBACK;" << std::endl;
        stream << padding << "}" << std::endl;
        
    } else {
        std::cerr << "'" << TAGNAME(elem) << "'" << std::endl << elem << std::endl;
        assert(false);
    }

}

void ChartToC::writeElementInfo(std::ostream& stream) {
    NodeSet<std::string> foreachs = filterChildElements(_nsInfo.xmlNSPrefix + "foreach", _scxml, true);
    if (foreachs.size() > 0) {
        stream << "scxml_elem_foreach scxml_elem_foreachs[" << foreachs.size() << "] = {" << std::endl;
        for (int i = 0; i < foreachs.size(); i++) {
            Element<std::string> foreach(foreachs[i]);
            stream << "    { ";
            stream << (HAS_ATTR(foreach, "array") ? "\"" + escape(ATTR(foreach, "array")) + "\"" : "NULL") << ", ";
            stream << (HAS_ATTR(foreach, "item") ? "\"" + escape(ATTR(foreach, "item")) + "\"" : "NULL") << ", ";
            stream << (HAS_ATTR(foreach, "index") ? "\"" + escape(ATTR(foreach, "index")) + "\"" : "NULL");
            stream << " }" << (i + 1 < foreachs.size() ? ",": "") << std::endl;
            foreach.setAttribute("documentOrder", toStr(i));
        }
        stream << "};" << std::endl;
        stream << std::endl;
    }

    NodeSet<std::string> datas = filterChildElements(_nsInfo.xmlNSPrefix + "data", _scxml, true);
    if (datas.size() > 0) {
        if (_binding == InterpreterImpl::EARLY) {
            Element<std::string>(_states[0]).setAttribute("dataIndex", "0");
        }

        Node<std::string> parent;
        size_t distinctParents = 0;
        for (int i = 0; i < datas.size(); i++) {
            Element<std::string> data(datas[i]);
            if (data.getParentNode() != parent) {
                distinctParents++;
            }
        }
        parent = Node<std::string>();
        
        stream << "scxml_elem_data scxml_elem_datas[" << datas.size() + distinctParents << "] = {" << std::endl;
        for (int i = 0; i < datas.size(); i++) {
            Element<std::string> data(datas[i]);
            if (data.getParentNode().getParentNode() != parent) {
                if (_binding == InterpreterImpl::LATE) {
                    Element<std::string>(data.getParentNode().getParentNode()).setAttribute("dataIndex", toStr(i));
                    if (i > 0) {
                        stream << "    { NULL, NULL, NULL, NULL }," << std::endl;
                    }
                }
                parent = data.getParentNode().getParentNode();
            }
            stream << "    { ";
            stream << (HAS_ATTR(data, "id") ? "\"" + escape(ATTR(data, "id")) + "\"" : "NULL") << ", ";
            stream << (HAS_ATTR(data, "src") ? "\"" + escape(ATTR(data, "src")) + "\"" : "NULL") << ", ";
            stream << (HAS_ATTR(data, "expr") ? "\"" + escape(ATTR(data, "expr")) + "\"" : "NULL") << ", ";

            NodeSet<std::string> dataTexts = filterChildType(Node_base::TEXT_NODE, data);
            if (dataTexts.size() > 0) {
                if (boost::trim_copy(dataTexts[0].getNodeValue()).length() > 0) {
                    std::string escaped = escape(dataTexts[0].getNodeValue());
                    stream << "\"" << escaped << "\"" << std::endl;
                }
            } else {
                stream << "NULL";
            }

            stream << " }," << std::endl;
            
        }
        stream << "    { NULL, NULL, NULL, NULL }" << std::endl;
        stream << "};" << std::endl;
        stream << std::endl;
    }

    NodeSet<std::string> params = filterChildElements(_nsInfo.xmlNSPrefix + "param", _scxml, true);
    if (params.size() > 0) {
        Node<std::string> parent;
        size_t distinctParents = 0;
        for (int i = 0; i < params.size(); i++) {
            Element<std::string> param(params[i]);
            if (param.getParentNode() != parent) {
                distinctParents++;
            }
        }
        parent = Node<std::string>();

        stream << "scxml_elem_param scxml_elem_params[" << params.size() + distinctParents << "] = {" << std::endl;
        for (int i = 0; i < params.size(); i++) {
            Element<std::string> param(params[i]);
            if (param.getParentNode() != parent) {
                Element<std::string>(param.getParentNode()).setAttribute("paramIndex", toStr(i));
                if (i > 0) {
                    stream << "    { NULL, NULL, NULL }," << std::endl;
                }
                parent = param.getParentNode();
            }
            stream << "    { ";
            stream << (HAS_ATTR(param, "name") ? "\"" + escape(ATTR(param, "name")) + "\"" : "NULL") << ", ";
            stream << (HAS_ATTR(param, "expr") ? "\"" + escape(ATTR(param, "expr")) + "\"" : "NULL") << ", ";
            stream << (HAS_ATTR(param, "location") ? "\"" + escape(ATTR(param, "location")) + "\"" : "NULL");
            stream << " }," << std::endl;

        }
        stream << "    { NULL, NULL, NULL }" << std::endl;
        stream << "};" << std::endl;
        stream << std::endl;
    }
    
    NodeSet<std::string> sends = filterChildElements(_nsInfo.xmlNSPrefix + "send", _scxml, true);
    if (sends.size() > 0) {
        stream << "scxml_elem_send scxml_elem_sends[" << sends.size() << "] = {" << std::endl;
        for (int i = 0; i < sends.size(); i++) {
            Element<std::string> send(sends[i]);
            stream << "    { ";
            stream << (HAS_ATTR(send, "event") ? "\"" + escape(ATTR(send, "event")) + "\"" : "NULL") << ", ";
            stream << (HAS_ATTR(send, "eventexpr") ? "\"" + escape(ATTR(send, "eventexpr")) + "\"" : "NULL") << ", ";
            stream << (HAS_ATTR(send, "target") ? "\"" + escape(ATTR(send, "target")) + "\"" : "NULL") << ", ";
            stream << (HAS_ATTR(send, "targetexpr") ? "\"" + escape(ATTR(send, "targetexpr")) + "\"" : "NULL") << ", ";
            stream << (HAS_ATTR(send, "type") ? "\"" + escape(ATTR(send, "type")) + "\"" : "NULL") << ", ";
            stream << (HAS_ATTR(send, "typeexpr") ? "\"" + escape(ATTR(send, "typeexpr")) + "\"" : "NULL") << ", ";
            stream << (HAS_ATTR(send, "id") ? "\"" + escape(ATTR(send, "id")) + "\"" : "NULL") << ", ";
            stream << (HAS_ATTR(send, "idlocation") ? "\"" + escape(ATTR(send, "idlocation")) + "\"" : "NULL") << ", ";
            stream << (HAS_ATTR(send, "delay") ? "\"" + escape(ATTR(send, "delay")) + "\"" : "NULL") << ", ";
            stream << (HAS_ATTR(send, "delayexpr") ? "\"" + escape(ATTR(send, "delayexpr")) + "\"" : "NULL") << ", ";
            stream << (HAS_ATTR(send, "namelist") ? "\"" + escape(ATTR(send, "namelist")) + "\"" : "NULL") << ", ";
            
            NodeSet<std::string> contents = filterChildElements(_nsInfo.xmlNSPrefix + "content", send);
            if (contents.size() > 0) {
                std::stringstream ss;
                stream << "\"";
                NodeList<std::string> cChilds = contents[0].getChildNodes();
                for (int j = 0; j < cChilds.getLength(); j++) {
                    ss << cChilds.item(j);
                    stream << escape(ss.str());
                }
                stream << "\", ";
            } else {
                stream << "NULL, ";
            }
            
            
            if (HAS_ATTR(send, "paramIndex")) {
                stream << "(const scxml_elem_param*)&scxml_elem_params[" << escape(ATTR(send, "paramIndex")) << "], ";
            } else {
                stream << "NULL, ";
            }
            stream << "NULL";

            stream << " }" << (i + 1 < sends.size() ? ",": "") << std::endl;
            send.setAttribute("documentOrder", toStr(i));
        }
        stream << "};" << std::endl;
        stream << std::endl;
    }

}

void ChartToC::writeStates(std::ostream& stream) {
    stream << "scxml_state scxml_states[" << toStr(_states.size()) << "] = {" << std::endl;
    for (int i = 0; i < _states.size(); i++) {
        Element<std::string> state(_states[i]);
        stream << "    { ";
        
        // name
        stream << (HAS_ATTR(state, "id") ? "\"" + escape(ATTR(state, "id")) + "\"" : "NULL") << ", ";
        
        // onentry
        stream << (filterChildElements(_nsInfo.xmlNSPrefix + "onentry", state).size() > 0 ? DOMUtils::idForNode(state) + "_on_entry" : "NULL") << ", ";

        // onexit
        stream << (filterChildElements(_nsInfo.xmlNSPrefix + "onexit", state).size() > 0 ? DOMUtils::idForNode(state) + "_on_exit" : "NULL") << ", ";

        // invokers
        stream << (filterChildElements(_nsInfo.xmlNSPrefix + "invoke", state).size() > 0 ? DOMUtils::idForNode(state) + "_invoke" : "NULL") << ", ";

        // children
        std::string childBools;
        std::string childBoolsIdx;
        for (int j = 0; j < _states.size(); j++) {
            if (_states[j].getParentNode() == state) {
                childBools += "1";
                childBoolsIdx += " " + toStr(j);
            } else {
                childBools += "0";
            }
        }
        stream << "{ ";
        writeCharArrayInitList(stream, childBools);
        stream << " /* " << childBools << "," << childBoolsIdx << " */";
        stream << " }, ";

        // default completion
        NodeSet<std::string> completion;
        if (isParallel(state)) {
            completion = getChildStates(state);
        } else if (state.hasAttribute("initial")) {
            completion = getStates(tokenizeIdRefs(state.getAttribute("initial")));
        } else {
            NodeSet<std::string> initElems = filterChildElements(_nsInfo.xmlNSPrefix + "initial", state);
            if(initElems.size() > 0 && !iequals(ATTR_CAST(initElems[0], "generated"), "true")) {
                // initial element is first child
                completion.push_back(initElems[0]);
            } else {
                // first child state
                Arabica::XPath::NodeSet<std::string> initStates;
                NodeList<std::string> childs = state.getChildNodes();
                for (int i = 0; i < childs.getLength(); i++) {
                    if (childs.item(i).getNodeType() != Node_base::ELEMENT_NODE)
                        continue;
                    if (isState(Element<std::string>(childs.item(i)))) {
                        completion.push_back(childs.item(i));
                    }
                }
            }
        }
        
        std::string descBools;
        std::string descBoolsIdx;
        for (int j = 0; j < _states.size(); j++) {
            if (isMember(_states[j], completion)) {
                descBools += "1";
                descBoolsIdx += " " + toStr(j);
            } else {
                descBools += "0";
            }
        }
        stream << "{ ";
        writeCharArrayInitList(stream, descBools);
        stream << " /* " << descBools << "," << descBoolsIdx << " */";
        stream << " }, ";
        
        // ancestors
        std::string ancBools;
        std::string ancBoolsIdx;
        for (int j = 0; j < _states.size(); j++) {
            if (isDescendant(state, _states[j])) {
                ancBools += "1";
                ancBoolsIdx += " " + toStr(j);
            } else {
                ancBools += "0";
            }
        }
        stream << "{ ";
        writeCharArrayInitList(stream, ancBools);
        stream << " /* " << ancBools << "," << ancBoolsIdx << " */";
        stream << " }, ";
        
        if (HAS_ATTR(state, "dataIndex")) {
            stream << "(const scxml_elem_data*)&scxml_elem_datas[" << escape(ATTR(state, "dataIndex")) << "], ";
        } else {
            stream << "NULL, ";
        }

        if (false) {
        } else if (iequals(TAGNAME(state), "initial")) {
            stream << "SCXML_STATE_INITIAL";
        } else if (isFinal(state)) {
            stream << "SCXML_STATE_FINAL";
        } else if (isHistory(state)) {
            if (HAS_ATTR(state, "type") && iequals(ATTR(state, "type"), "deep")) {
                stream << "SCXML_STATE_HISTORY_DEEP";
            } else {
                stream << "SCXML_STATE_HISTORY_SHALLOW";
            }
        } else if (isAtomic(state)) {
            stream << "SCXML_STATE_ATOMIC";
        } else if (isParallel(state)) {
            stream << "SCXML_STATE_PARALLEL";
        } else if (isCompound(state)) {
            stream << "SCXML_STATE_COMPOUND";
        } else { // <scxml>
            stream << "SCXML_STATE_COMPOUND";
        }

        stream << " }" << (i + 1 < _states.size() ? ",": "") << std::endl;
    }
    stream << "};" << std::endl;
    stream << std::endl;
}
    
    
void ChartToC::writeTransitions(std::ostream& stream) {

    stream << "scxml_transition scxml_transitions[" << toStr(_transitions.size()) << "] = {" << std::endl;
    for (int i = 0; i < _transitions.size(); i++) {
        Element<std::string> transition(_transitions[i]);
        stream << "    { ";
        
        /**
         uint16_t source;
         target[SCXML_NUMBER_STATES / 8 + 1];
         const char* event;
         const char* condition;
         exec_content_t on_transition;
         uint8_t type;
         char conflicts[SCXML_NUMBER_STATES / 8 + 1];
         char exit_set[SCXML_NUMBER_STATES / 8 + 1];
        */

        // source
        stream << ATTR_CAST(transition.getParentNode(), "documentOrder") << ", ";

        // targets
        if (HAS_ATTR(transition, "target")) {
            std::list<std::string> targets = tokenize(ATTR(transition, "target"));

            std::string targetBools;
            for (int j = 0; j < _states.size(); j++) {
                Element<std::string> state(_states[j]);

                if (HAS_ATTR(state, "id") &&
                    std::find(targets.begin(), targets.end(), escape(ATTR(state, "id"))) != targets.end()) {
                   targetBools += "1";
                } else {
                    targetBools += "0";
                }
            }

            stream << "{ ";
            writeCharArrayInitList(stream, targetBools);
            stream << " /* " << targetBools << " */";
            stream << " }, ";

        } else {
            stream << "{ NULL }, ";
        }
        
        // event
        stream << (HAS_ATTR(transition, "event") ? "\"" + escape(ATTR(transition, "event")) + "\"" : "NULL") << ", ";

        // condition
        stream << (HAS_ATTR(transition, "cond") ? "\"" + escape(ATTR(transition, "cond")) + "\"" : "NULL") << ", ";
        
        // on transition handlers
        if (filterChildType(Arabica::DOM::Node_base::ELEMENT_NODE, transition).size() > 0 &&
            !iequals(TAGNAME_CAST(transition.getParentNode()), "initial")) {
            stream << DOMUtils::idForNode(transition) + "_on_trans, ";
        } else {
            stream << "NULL, ";
        }

        // type
        std::string seperator = "";
        if (!HAS_ATTR(transition, "target")) {
            stream << seperator << "SCXML_TRANS_TARGETLESS";
            seperator = " & ";
        }

        if (HAS_ATTR(transition, "type") && iequals(ATTR(transition, "type"), "internal")) {
            stream << seperator << "SCXML_TRANS_INTERNAL";
            seperator = " & ";
        }

        if (!HAS_ATTR(transition, "event")) {
            stream << seperator << "SCXML_TRANS_SPONTANEOUS";
            seperator = " & ";
        }

        if (seperator.size() == 0) {
            stream << "0";
        }
        stream << ", ";

        // conflicts
        std::string conflictBools;
        for (unsigned int j = 0; j < _transitions.size(); j++) {
            Element<std::string> t2(_transitions[j]);
            if (hasIntersection(computeExitSet(transition), computeExitSet(t2)) ||
                (getSourceState(transition) == getSourceState(t2)) ||
                (isDescendant(getSourceState(transition), getSourceState(t2))) ||
                (isDescendant(getSourceState(t2), getSourceState(transition)))) {
                conflictBools += "1";
            } else {
                conflictBools += "0";
            }
        }
        stream << "{ ";
        writeCharArrayInitList(stream, conflictBools);
        stream << " /* " << conflictBools << " */";
        stream << " }, ";

        // exit set
        std::string exitSetBools;
        NodeSet<std::string> exitSet = computeExitSet(transition);
        for (unsigned int j = 0; j < _states.size(); j++) {
            Element<std::string> state(_states[j]);
            if (isMember(state, exitSet)) {
                exitSetBools += "1";
            } else {
                exitSetBools += "0";
            }
        }
        stream << "{ ";
        writeCharArrayInitList(stream, exitSetBools);
        stream << " /* " << exitSetBools << " */";
        stream << " }";

        stream << " }" << (i + 1 < _transitions.size() ? ",": "") << std::endl;
    }
    stream << "};" << std::endl;
    stream << std::endl;
}

Arabica::XPath::NodeSet<std::string> ChartToC::computeExitSet(const Arabica::DOM::Element<std::string>& transition) {
    
    NodeSet<std::string> statesToExit;
    if (!isTargetless(transition)) {
        Arabica::DOM::Node<std::string> domain = getTransitionDomain(transition);
        if (!domain)
            return statesToExit;
        for (unsigned int j = 0; j < _states.size(); j++) {
            const Node<std::string>& s = _states[j];
            if (isDescendant(s, domain)) {
                statesToExit.push_back(s);
            }
        }
    }
    
    return statesToExit;
}

void ChartToC::writeCharArrayInitList(std::ostream& stream, const std::string& boolString) {
    /**
     * 0111 -> 0x08
     * 1111 -> 0x0f
     * 1111 1111 -> 0xff
     * 1111 1111 1110 -> 0x0f, 0xfd
     *
     * 76543210 fedcba98 ...
     */
    
    std::string charArray;
    size_t index = 0;
    char currChar = 0;
    
    for (std::string::const_iterator bIter = boolString.begin(); bIter != boolString.end(); bIter++) {
        
        if (*bIter == '1') {
            currChar |= 1 << index;
        }
        
        index++;
        if (index == 8) {
            charArray += currChar;
            currChar = 0;
            index = 0;
        }
    }
    
    if (index != 0) {
        charArray += currChar;
    }
    
    std::string seperator = "";
    for (std::string::const_iterator cIter = charArray.begin(); cIter != charArray.end(); cIter++) {
        stream << seperator << "0x" << std::setw(2) << std::setfill('0') << std::hex << int(*cIter & 0xFF);
        seperator = ", ";
    }
}

void ChartToC::writeFSM(std::ostream& stream) {
    stream << "int scxml_step(scxml_ctx* ctx) {" << std::endl;
    stream << std::endl;
    
    stream << "#ifdef SCXML_VERBOSE" << std::endl;
    stream << "    printStateNames(ctx->config);" << std::endl;
    stream << "#endif" << std::endl;
    stream << std::endl;

    stream << "MACRO_STEP:" << std::endl;
    stream << "    ctx->flags &= ~SCXML_CTX_TRANSITION_FOUND;" << std::endl;
    stream << std::endl;
    
    stream << "    if (ctx->flags & SCXML_CTX_TOP_LEVEL_FINAL) " << std::endl;
    stream << "        return SCXML_ERR_DONE; " << std::endl;
    stream << std::endl;

    stream << "    int err = SCXML_ERR_OK;" << std::endl;
    stream << "    char conflicts[" << _transCharArraySize << "] = " << _transCharArrayInit << ";" << std::endl;
    stream << "    char target_set[" << _stateCharArraySize << "] = " << _stateCharArrayInit << ";" << std::endl;
    stream << "    char exit_set[" << _stateCharArraySize << "] = " << _stateCharArrayInit << ";" << std::endl;
    stream << "    char trans_set[" << _transCharArraySize << "] = " << _transCharArrayInit << ";" << std::endl;
    stream << "    char entry_set[" << _stateCharArraySize << "] = " << _stateCharArrayInit << ";" << std::endl;
    stream << std::endl;

    stream << "    void* event;" << std::endl;
    stream << "    if (ctx->flags == SCXML_CTX_PRISTINE) {" << std::endl;
    stream << "        bit_or(target_set, scxml_states[0].completion, " << _stateCharArraySize << ");" << std::endl;
    stream << "        ctx->flags |= SCXML_CTX_SPONTANEOUS | SCXML_CTX_INITIALIZED;" << std::endl;
    stream << "        goto COMPLETE_CONFIG;" << std::endl;
    stream << "    }" << std::endl;
    stream << std::endl;

    stream << "    if (ctx->flags & SCXML_CTX_SPONTANEOUS) {" << std::endl;
    stream << "        event = NULL;" << std::endl;
    stream << "        goto SELECT_TRANSITIONS;" << std::endl;
    stream << "    }" << std::endl;
    stream << "    if ((event = ctx->dequeue_internal(ctx)) != NULL) {" << std::endl;
    stream << "        goto SELECT_TRANSITIONS;" << std::endl;
    stream << "    }" << std::endl;
    stream << "    if ((event = ctx->dequeue_external(ctx)) != NULL) {" << std::endl;

    stream << "        goto SELECT_TRANSITIONS;" << std::endl;
    stream << "    }" << std::endl;
    stream << std::endl;

    stream << "SELECT_TRANSITIONS:" << std::endl;
    stream << "    for (int i = 0; i < SCXML_NUMBER_TRANSITIONS; i++) {" << std::endl;
    stream << "        // is the transition active?" << std::endl;
    stream << "        if (IS_SET(scxml_transitions[i].source, ctx->config)) {" << std::endl;
    stream << "            // is it non-conflicting?" << std::endl;
    stream << "            if (!IS_SET(i, conflicts)) {" << std::endl;
    stream << "                // is it enabled?" << std::endl;
    stream << "                if (ctx->is_enabled(ctx, &scxml_transitions[i], event) > 0) {" << std::endl;
    stream << "                    // remember that we found a transition" << std::endl;
    stream << "                    ctx->flags |= SCXML_CTX_TRANSITION_FOUND;" << std::endl;
    stream << std::endl;

    stream << "                    // transitions that are pre-empted" << std::endl;
    stream << "                    bit_or(conflicts, scxml_transitions[i].conflicts, " << _transCharArraySize << ");" << std::endl;
    stream << std::endl;
    stream << "                    // states that are directly targeted (resolve as entry-set later)" << std::endl;
    stream << "                    bit_or(target_set, scxml_transitions[i].target, " << _stateCharArraySize << ");" << std::endl;
    stream << std::endl;
    stream << "                    // states that will be left" << std::endl;
    stream << "                    bit_or(exit_set, scxml_transitions[i].exit_set, " << _stateCharArraySize << ");" << std::endl;
    stream << std::endl;
    stream << "                    SET_BIT(i, trans_set);" << std::endl;
    stream << "                }" << std::endl;
    stream << "            }" << std::endl;
    stream << "        }" << std::endl;
    stream << "    }" << std::endl;
    stream << std::endl;

    stream << "    if (ctx->flags & SCXML_CTX_TRANSITION_FOUND) {" << std::endl;
    stream << "        ctx->flags |= SCXML_CTX_SPONTANEOUS;" << std::endl;
    stream << "    } else {" << std::endl;
    stream << "        ctx->flags &= ~SCXML_CTX_SPONTANEOUS;" << std::endl;
    stream << "        goto MACRO_STEP;" << std::endl;
    stream << "    }" << std::endl;
    stream << std::endl;
    
    stream << "REMEMBER_HISTORY:" << std::endl;
    stream << "    // are my ancestors in the exit set?" << std::endl;
    stream << "    for (int i = 0; i < SCXML_NUMBER_STATES; i++) {" << std::endl;
    stream << "        if (IS_SET(i, ctx->config) && bit_has_and(exit_set, scxml_states[i].ancestors, " << _stateCharArraySize << ")) {" << std::endl;
    stream << "            SET_BIT(i, ctx->history);" << std::endl;
    stream << "        }" << std::endl;
    stream << "    }" << std::endl;
    stream << std::endl;

    stream << "#ifdef SCXML_VERBOSE" << std::endl;
    stream << "    printf(\"Exiting: \");" << std::endl;
    stream << "    printStateNames(exit_set);" << std::endl;
    stream << "#endif" << std::endl;
    stream << std::endl;
    
    stream << "EXIT_STATES:" << std::endl;
    stream << "    for (int i = SCXML_NUMBER_STATES - 1; i >= 0; i--) {" << std::endl;
    stream << "        if (IS_SET(i, exit_set) && IS_SET(i, ctx->config)) {" << std::endl;
    stream << "            // call all on exit handlers" << std::endl;
    stream << "            if (scxml_states[i].on_exit != NULL) {" << std::endl;
    stream << "                if((err = scxml_states[i].on_exit(ctx, &scxml_states[i], event)) != SCXML_ERR_OK)" << std::endl;
    stream << "                    return err;" << std::endl;
    stream << "            }" << std::endl;
    stream << "            CLEARBIT(i, ctx->config);" << std::endl;
    stream << "        }" << std::endl;
    stream << "    }" << std::endl;
    stream << std::endl;

    stream << "COMPLETE_CONFIG:" << std::endl;
    stream << "    // calculate new entry set" << std::endl;
    stream << "    bit_copy(entry_set, target_set, " << _stateCharArraySize << ");" << std::endl;
    stream << std::endl;
    stream << "    // iterate for ancestors" << std::endl;
    stream << "    for (int i = 0; i < SCXML_NUMBER_STATES; i++) {" << std::endl;
    stream << "        if (IS_SET(i, entry_set)) {" << std::endl;
    stream << "            bit_or(entry_set, scxml_states[i].ancestors, " << _stateCharArraySize << ");" << std::endl;
    stream << "        }" << std::endl;
    stream << "    }" << std::endl;
    stream << std::endl;

    stream << "ADD_DESCENDANTS:" << std::endl;
    stream << "    // iterate for descendants" << std::endl;
    stream << "    for (int i = 0; i < SCXML_NUMBER_STATES; i++) {" << std::endl;
    stream << "        if (IS_SET(i, entry_set)) {" << std::endl;
    stream << "            switch (scxml_states[i].type) {" << std::endl;
    stream << "                case SCXML_STATE_PARALLEL: {" << std::endl;
    stream << "                    bit_or(entry_set, scxml_states[i].completion, " << _stateCharArraySize << ");" << std::endl;
    stream << "                    break;" << std::endl;
    stream << "                }" << std::endl;
    stream << "                case SCXML_STATE_INITIAL: {" << std::endl;
    stream << "                    for (int j = 0; j < SCXML_NUMBER_TRANSITIONS; j++) {" << std::endl;
    stream << "                        if (scxml_transitions[j].source == i) {" << std::endl;
    stream << "                            SET_BIT(j, trans_set);" << std::endl;
    stream << "                            CLEARBIT(i, entry_set);" << std::endl;
    stream << "                            bit_or(entry_set, scxml_transitions[j].target, " << _transCharArraySize << ");" << std::endl;
    stream << "                            // one target may have been above, reestablish completion" << std::endl;
    stream << "                            goto ADD_DESCENDANTS;" << std::endl;
    stream << "                        }" << std::endl;
    stream << "                    }" << std::endl;
    stream << "                    break;" << std::endl;
    stream << "                }" << std::endl;
    stream << "                case SCXML_STATE_COMPOUND: { // we need to check whether one child is already in entry_set" << std::endl;
    stream << "                    if (!bit_has_and(entry_set, scxml_states[i].children, " << _stateCharArraySize << ")) {" << std::endl;
    stream << "                        bit_or(entry_set, scxml_states[i].completion, " << _stateCharArraySize << ");" << std::endl;
    stream << "                    }" << std::endl;
    stream << "                    break;" << std::endl;
    stream << "                }" << std::endl;
    stream << "            }" << std::endl;
    stream << "        }" << std::endl;
    stream << "    }" << std::endl;
    stream << std::endl;

    stream << "#ifdef SCXML_VERBOSE" << std::endl;
    stream << "    printf(\"Transitions: \");" << std::endl;
    stream << "    printBitsetIndices(trans_set, sizeof(char) * 8 * " << _transCharArraySize << ");" << std::endl;
    stream << "#endif" << std::endl;
    stream << std::endl;

    stream << "TAKE_TRANSITIONS:" << std::endl;
    stream << "    for (int i = 0; i < SCXML_NUMBER_TRANSITIONS; i++) {" << std::endl;
    stream << "        if (IS_SET(i, trans_set)) {" << std::endl;
    stream << "            // call executable content in transition" << std::endl;
    stream << "            if (scxml_transitions[i].on_transition != NULL) {" << std::endl;
    stream << "                if((err = scxml_transitions[i].on_transition(ctx," << std::endl;
    stream << "                                                             &scxml_states[scxml_transitions[i].source]," << std::endl;
    stream << "                                                             event)) != SCXML_ERR_OK)" << std::endl;
    stream << "                    return err;" << std::endl;
    stream << "            }" << std::endl;
    stream << "        }" << std::endl;
    stream << "    }" << std::endl;
    stream << std::endl;

    stream << "#ifdef SCXML_VERBOSE" << std::endl;
    stream << "    printf(\"Entering: \");" << std::endl;
    stream << "    printStateNames(entry_set);" << std::endl;
    stream << "#endif" << std::endl;
    stream << std::endl;

    stream << "ENTER_STATES:" << std::endl;
    stream << "    for (int i = 0; i < SCXML_NUMBER_STATES; i++) {" << std::endl;
    stream << "        if (IS_SET(i, entry_set) && !IS_SET(i, ctx->config)) {" << std::endl;
    stream << "            SET_BIT(i, ctx->config);" << std::endl;
    stream << "            if (scxml_states[i].on_entry != NULL) {" << std::endl;
    stream << "                if((err = scxml_states[i].on_entry(ctx, &scxml_states[i], event)) != SCXML_ERR_OK)" << std::endl;
    stream << "                    return err;" << std::endl;
    stream << "            }" << std::endl;
    stream << std::endl;
    
    stream << "            // initialize data" << std::endl;
    stream << "            if(!IS_SET(i, ctx->initialized_data)) {" << std::endl;
    stream << "                if (scxml_states[i].data != NULL && ctx->exec_content_init != NULL) {" << std::endl;
    stream << "                    ctx->exec_content_init(ctx, scxml_states[i].data);" << std::endl;
    stream << "                }" << std::endl;
    stream << "                SET_BIT(i, ctx->initialized_data);" << std::endl;
    stream << "            }" << std::endl;
    stream << std::endl;

    stream << "            // handle final states" << std::endl;
    stream << "            if (scxml_states[i].type == SCXML_STATE_FINAL) {" << std::endl;
    stream << "                if (scxml_states[i].ancestors[0] == 0x01) {" << std::endl;
    stream << "                    ctx->flags |= SCXML_CTX_TOP_LEVEL_FINAL;" << std::endl;
    stream << "                } else {" << std::endl;
    stream << "                    // raise done event" << std::endl;
    stream << "                    size_t parent = 0;" << std::endl;
    stream << "                    for (int j = 0; j < SCXML_NUMBER_STATES; j++) {" << std::endl;
    stream << "                        // we could trade runtime for memory here by saving the parent index" << std::endl;
    stream << "                        if (!IS_SET(j, scxml_states[i].ancestors)) {" << std::endl;
    stream << "                            if (parent != 0) {" << std::endl;
    stream << "                                break;" << std::endl;
    stream << "                            }" << std::endl;
    stream << "                            continue;" << std::endl;
    stream << "                        } else {" << std::endl;
    stream << "                            parent = j;" << std::endl;
    stream << "                        }" << std::endl;
    stream << "                    }" << std::endl;
    stream << "                    ctx->raise_done_event(ctx, &scxml_states[parent]);" << std::endl;
    stream << "                }" << std::endl;
    stream << std::endl;

    stream << "                /**" << std::endl;
    stream << "                 * are we the last final state to leave a parallel state?:" << std::endl;
    stream << "                 * 1. Gather all parallel states in our ancestor chain" << std::endl;
    stream << "                 * 2. Find all states for which these parallels are ancestors" << std::endl;
    stream << "                 * 3. Iterate all active final states and remove their ancestors" << std::endl;
    stream << "                 * 4. If a state remains, not all children of a parallel are final" << std::endl;
    stream << "                 */" << std::endl;
    stream << "                for (int j = 0; j < SCXML_NUMBER_STATES; j++) {" << std::endl;
    stream << "                    if (scxml_states[j].type == SCXML_STATE_PARALLEL) {" << std::endl;
    stream << "                        char parallel_children[2] = {0, 0};" << std::endl;
    stream << "                        size_t parallel = j;" << std::endl;
    stream << "                        for (int k = 0; k < SCXML_NUMBER_STATES; k++) {" << std::endl;
    stream << "                            if (IS_SET(parallel, scxml_states[k].ancestors) && IS_SET(k, ctx->config)) {" << std::endl;
    stream << "                                if (scxml_states[k].type == SCXML_STATE_FINAL) {" << std::endl;
    stream << "                                    bit_and_not(parallel_children, scxml_states[k].ancestors, 2);" << std::endl;
    stream << "                                } else {" << std::endl;
    stream << "                                    SET_BIT(k, parallel_children);" << std::endl;
    stream << "                                }" << std::endl;
    stream << "                            }" << std::endl;
    stream << "                        }" << std::endl;
    stream << "                        if (!bit_any_set(parallel_children, 2)) {" << std::endl;
    stream << "                            ctx->raise_done_event(ctx, &scxml_states[parallel]);" << std::endl;
    stream << "                        }" << std::endl;
    stream << "                    }" << std::endl;
    stream << "                }" << std::endl;
    stream << std::endl;

    stream << "            }" << std::endl;
    stream << std::endl;
    
    stream << "        }" << std::endl;
    stream << "    }" << std::endl;
    stream << std::endl;

    stream << "    return SCXML_ERR_OK;" << std::endl;
    stream << "}" << std::endl;
    stream << std::endl;
}

NodeSet<std::string> ChartToC::inPostFixOrder(const std::set<std::string>& elements, const Element<std::string>& root) {
    NodeSet<std::string> nodes;
    inPostFixOrder(elements, root, nodes);
    return nodes;
}

void ChartToC::inPostFixOrder(const std::set<std::string>& elements, const Element<std::string>& root, NodeSet<std::string>& nodes) {
    NodeList<std::string> children = root.getChildNodes();
    for (int i = 0; i < children.getLength(); i++) {
        if (children.item(i).getNodeType() != Node_base::ELEMENT_NODE)
            continue;
        const Arabica::DOM::Element<std::string>& childElem(children.item(i));
        inPostFixOrder(elements, childElem, nodes);

    }
    for (int i = 0; i < children.getLength(); i++) {
        if (children.item(i).getNodeType() != Node_base::ELEMENT_NODE)
            continue;
        const Arabica::DOM::Element<std::string>& childElem(children.item(i));

        if (elements.find(TAGNAME(childElem)) != elements.end()) {
            nodes.push_back(childElem);
        }
    }
}

NodeSet<std::string> ChartToC::inDocumentOrder(const std::set<std::string>& elements, const Element<std::string>& root) {
    NodeSet<std::string> nodes;
    inDocumentOrder(elements, root, nodes);
    return nodes;
}

void ChartToC::inDocumentOrder(const std::set<std::string>& elements, const Element<std::string>& root, NodeSet<std::string>& nodes) {
    if (elements.find(TAGNAME(root)) != elements.end()) {
        nodes.push_back(root);
    }

    NodeList<std::string> children = root.getChildNodes();
    for (int i = 0; i < children.getLength(); i++) {
        if (children.item(i).getNodeType() != Node_base::ELEMENT_NODE)
            continue;
        const Arabica::DOM::Element<std::string>& childElem(children.item(i));
        inDocumentOrder(elements, childElem, nodes);
    }
}

ChartToC::~ChartToC() {
}
    
}