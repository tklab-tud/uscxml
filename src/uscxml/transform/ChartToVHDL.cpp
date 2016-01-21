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

#include "uscxml/transform/ChartToFSM.h"
#include "uscxml/transform/ChartToVHDL.h"
#include "uscxml/debug/Complexity.h"
#include <DOM/io/Stream.hpp>
#include <iostream>
#include "uscxml/UUID.h"
#include "uscxml/DOMUtils.h"
#include "DOM/NodeList.hpp"
#include <math.h>
#include <boost/algorithm/string.hpp>
#include <glog/logging.h>

#include <algorithm>
#include <iomanip>

#include <sstream>

#define CONST_TRANS_SPONTANEOUS "HWE_NOW"
#define CONST_EVENT_ANY "HWE_ANY"

namespace uscxml {

    using namespace Arabica::DOM;
    using namespace Arabica::XPath;

    Transformer ChartToVHDL::transform(const Interpreter& other) {
        ChartToVHDL* c2c = new ChartToVHDL(other);

        return boost::shared_ptr<TransformerImpl>(c2c);
    }

    ChartToVHDL::ChartToVHDL(const Interpreter& other) : TransformerImpl() {
        cloneFrom(other.getImpl());
    }

    ChartToVHDL::~ChartToVHDL() {
    }

    NodeSet<std::string> ChartToVHDL::inPostFixOrder(const std::set<std::string>& elements, const Element<std::string>& root) {
        NodeSet<std::string> nodes;
        inPostFixOrder(elements, root, nodes);
        return nodes;
    }

    void ChartToVHDL::inPostFixOrder(const std::set<std::string>& elements, const Element<std::string>& root, NodeSet<std::string>& nodes) {
        NodeList<std::string> children = root.getChildNodes();
        for (int i = 0; i < children.getLength(); i++) {
            if (children.item(i).getNodeType() != Node_base::ELEMENT_NODE)
                continue;
            Arabica::DOM::Element<std::string> childElem(children.item(i));
            inPostFixOrder(elements, childElem, nodes);

        }
        for (int i = 0; i < children.getLength(); i++) {
            if (children.item(i).getNodeType() != Node_base::ELEMENT_NODE)
                continue;
            Arabica::DOM::Element<std::string> childElem(children.item(i));

            if (elements.find(TAGNAME(childElem)) != elements.end()) {
                nodes.push_back(childElem);
            }
        }
    }

    void ChartToVHDL::inDocumentOrder(const std::set<std::string>& elements, const Element<std::string>& root, NodeSet<std::string>& nodes) {
        if (elements.find(TAGNAME(root)) != elements.end()) {
            nodes.push_back(root);
        }

        NodeList<std::string> children = root.getChildNodes();
        for (int i = 0; i < children.getLength(); i++) {
            if (children.item(i).getNodeType() != Node_base::ELEMENT_NODE)
                continue;
            Arabica::DOM::Element<std::string> childElem(children.item(i));
            inDocumentOrder(elements, childElem, nodes);
        }
    }

    NodeSet<std::string> ChartToVHDL::inDocumentOrder(const std::set<std::string>& elements, const Element<std::string>& root) {
        NodeSet<std::string> nodes;
        inDocumentOrder(elements, root, nodes);
        return nodes;
    }

    Arabica::XPath::NodeSet<std::string> ChartToVHDL::computeExitSet(const Arabica::DOM::Element<std::string>& transition) {

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


    // ASK Where does _scxml,_nsInfo come from

    void ChartToVHDL::writeTo(std::ostream& stream) {
        // ASK What is this ?
        _binding = (HAS_ATTR(_scxml, "binding") && iequals(ATTR(_scxml, "binding"), "late") ? LATE : EARLY);
        // ASK Name for whole state machine? Important ?
        _name = (HAS_ATTR(_scxml, "name") ? ATTR(_scxml, "name") : "no_name_machine");

        // filter unsupported stuff
        std::set<std::string> elements;
        elements.insert(_nsInfo.xmlNSPrefix + "datamodel");
        elements.insert(_nsInfo.xmlNSPrefix + "data");
        elements.insert(_nsInfo.xmlNSPrefix + "assign");
        elements.insert(_nsInfo.xmlNSPrefix + "donedata");
        elements.insert(_nsInfo.xmlNSPrefix + "content");
        elements.insert(_nsInfo.xmlNSPrefix + "param");
        elements.insert(_nsInfo.xmlNSPrefix + "script");

        elements.insert(_nsInfo.xmlNSPrefix + "parallel");
        elements.insert(_nsInfo.xmlNSPrefix + "inital");
        elements.insert(_nsInfo.xmlNSPrefix + "history");

        elements.insert(_nsInfo.xmlNSPrefix + "if"); //implizit elseif und else
        elements.insert(_nsInfo.xmlNSPrefix + "foreach");
        elements.insert(_nsInfo.xmlNSPrefix + "send");
        elements.insert(_nsInfo.xmlNSPrefix + "cancel");
        elements.insert(_nsInfo.xmlNSPrefix + "invoke");
        elements.insert(_nsInfo.xmlNSPrefix + "finalize");
        Arabica::XPath::NodeSet<std::string> unsupported = inDocumentOrder(elements, _scxml);

        if (unsupported.size() > 0) {
            stream << "contains unsupported elements:" << std::endl;
            for (int i = 0; i < unsupported.size(); i++) {
                Element<std::string> uElement(unsupported[i]);
                stream << TAGNAME(uElement) << std::endl;
            }
            stream << "ERROR" << std::endl;
            return;
        }

        elements.clear();
        elements.insert(_nsInfo.xmlNSPrefix + "transition");
        unsupported = inPostFixOrder(elements, _scxml);

        for (int i = 0; i < unsupported.size(); i++) {
            Element<std::string> transition(unsupported[i]);
            if (HAS_ATTR(transition, "cond")) {
                stream << transition << std::endl;
                stream << "transition has conditions (not supported)!" << std::endl;
                stream << "ERROR" << std::endl;
                return;
            }
            if (!HAS_ATTR(transition, "target")) { // filter never matches
                stream << transition << std::endl;
                stream << "transition has no target (not supported)!" << std::endl;
                stream << "ERROR" << std::endl;
                return;
            }
            //            if (!HAS_ATTR(transition, "event")) {
            //                stream << transition << std::endl;
            //                stream << "transition is spntaneous (not supported)!" << std::endl;
            //                stream << "ERROR" << std::endl;
            //                return;
            //            }
            //            if (transition.getChildNodes().getLength() > 0) {
            //                stream << transition << std::endl;
            //                stream << "transition executable code (not supported)!" << std::endl;
            //                stream << "ERROR" << std::endl;
            //                return;
            //            }
        }

        elements.clear();
        elements.insert(_nsInfo.xmlNSPrefix + "send");
        unsupported = inPostFixOrder(elements, _scxml);

        for (int i = 0; i < unsupported.size(); i++) {
            Element<std::string> send(unsupported[i]);
            if (HAS_ATTR(send, "target") && (ATTR(send, "target")[0] != '#' || ATTR(send, "target")[1] != '_')) {
                stream << send << std::endl;
                stream << "complex send tag (not supported)!" << std::endl;
                stream << "ERROR" << std::endl;
                return;
            }
        }

        // filter final states which are not terminating the fsm
        elements.clear();
        elements.insert(_nsInfo.xmlNSPrefix + "final");
        unsupported = inPostFixOrder(elements, _scxml);
        for (int i = 0; i < unsupported.size(); i++) {
            Element<std::string> state(unsupported[i]);
            if (TAGNAME_CAST(state.getParentNode()) != "scxml") {
                stream << "internal final stateds (not supported)" << std::endl;
                stream << "ERROR" << std::endl;
            }
        }

        // create states array
        elements.clear();
        //        elements.insert(_nsInfo.xmlNSPrefix + "scxml");
        elements.insert(_nsInfo.xmlNSPrefix + "state");
        elements.insert(_nsInfo.xmlNSPrefix + "final");
        elements.insert(_nsInfo.xmlNSPrefix + "parallel");
        elements.insert(_nsInfo.xmlNSPrefix + "history");
        elements.insert(_nsInfo.xmlNSPrefix + "initial");
        //        elements.insert(_nsInfo.xmlNSPrefix + "parallel");
        _states = inDocumentOrder(elements, _scxml);

        for (int i = 0; i < _states.size(); i++) {
            Element<std::string> state(_states[i]);
            state.setAttribute("documentOrder", toStr(i));
            if (!HAS_ATTR(state, "id")) {
                std::stringstream ss;
                ss << "HWS_" << toStr(i);
                state.setAttribute("id", ss.str());
            }
            _stateNames[ATTR(state, "id")] = state;
        }
        _initState = ATTR(_scxml, "initial");

        //create compount states array
        elements.clear();
        //        elements.insert(_nsInfo.xmlNSPrefix + "scxml");
        elements.insert(_nsInfo.xmlNSPrefix + "state");
        //        elements.insert(_nsInfo.xmlNSPrefix + "initial");
        //        elements.insert(_nsInfo.xmlNSPrefix + "parallel");
        Arabica::XPath::NodeSet<std::string> tmp_states = inDocumentOrder(elements, _scxml);

        for (int i = 0; i < tmp_states.size(); i++) {
            Element<std::string> state(tmp_states[i]);
            NodeList<std::string> children = state.getChildNodes();

            bool isCompound = false;
            for (int j = 0; j < children.getLength(); j++) {
                if (children.item(j).getNodeType() == Node_base::ELEMENT_NODE) {
                    Element<std::string> child(children.item(j));
                    if (TAGNAME(child) == "state" ||
                            //                            TAGNAME(child) == "initial"||
                            TAGNAME(child) == "final" ||
                            TAGNAME(child) == "parallel" ||
                            TAGNAME(child) == "history") {
                        // is compound state
                        _compoundStates.push_back(state);
                        isCompound = true;
                        break;
                    }
                }
            }

            // mark as explizit compount and
            // set initial state if not defined
            if (isCompound) {
                state.setAttribute("isCompound", "true");
                if (!HAS_ATTR(state, "initial")) {
                    // go to states in document order
                    // find the first child and set it as inital state
                    for (int j = 0; j < _states.size(); j++) {
                        if (isDescendant(_states[j], state)) {
                            Element<std::string> s2(_states[j]);
                            state.setAttribute("initial", ATTR(s2, "id"));
                            s2.setAttribute("defaultEntryFor", ATTR(state, "id"));
                        }
                    }
                } else {
                    // if state has initial attribute
                    // just mark the given child
                    for (int j = 0; j < _states.size(); j++) {
                        if (ATTR_CAST(_states[j], "id") == ATTR(state, "target")) {
                            Element<std::string> s2(_states[j]);
                            s2.setAttribute("defaultEntryFor", ATTR(state, "id"));
                        }
                    }
                }
            }
            //FIXME verschachtelte compound auflösen
        }

        // create final states array
        elements.clear();
        //        elements.insert(_nsInfo.xmlNSPrefix + "scxml");
        elements.insert(_nsInfo.xmlNSPrefix + "final");
        _finalStates = inDocumentOrder(elements, _scxml);
        for (int i = 0; i < _finalStates.size(); i++) {
            Element<std::string> state(_finalStates[i]);
            if (TAGNAME_CAST(state.getParentNode()) == "scxml") {
                _superFinalStates.push_back(state);
            }
        }

        // create parallel states array
        elements.clear();
        //        elements.insert(_nsInfo.xmlNSPrefix + "scxml");
        elements.insert(_nsInfo.xmlNSPrefix + "parallel");
        _parallelStates = inDocumentOrder(elements, _scxml);

        // create transitions array & event array
        // modify transitions for compound states
        elements.clear();
        elements.insert(_nsInfo.xmlNSPrefix + "transition");
        _transitions = inPostFixOrder(elements, _scxml);

        for (int i = 0; i < _transitions.size(); i++) {
            Element<std::string> transition(_transitions[i]);
            transition.setAttribute("postFixOrder", toStr(i));
            if (!HAS_ATTR(transition, "event")) {
                // spontaneous transition
                transition.setAttribute("event", CONST_TRANS_SPONTANEOUS);
            }
            std::stringstream ss;
            ss << "HWT" << toStr(i) << "_to_" << ATTR(transition, "target");
            transition.setAttribute("id", ss.str());
            _transitionNames[ss.str()] = transition;

            std::string event = ATTR(transition, "event");
            if (event == "*") {
                event = CONST_EVENT_ANY;
                transition.setAttribute("event", CONST_EVENT_ANY);
            }
            if (!(std::find(_events.begin(), _events.end(), event) != _events.end())) {
                // if eventname does not exist
                _events.push_back(event);
            }

        }

        //        stream << _scxml;
        // debug
        //        stream << _scxml;
        //        return;

        // how many bits do we need to represent the state array?
        //        std::string seperator;
        //        _stateCharArraySize = ceil((float) _states.size() / (float) 8);
        //        _stateCharArrayInit = "{";
        //        for (int i = 0; i < _stateCharArraySize; i++) {
        //            _stateCharArrayInit += seperator + "0";
        //            seperator = ", ";
        //        }
        //        _stateCharArrayInit += "}";
        //
        //        seperator = "";
        //        _transCharArraySize = ceil((float) _transitions.size() / (float) 8);
        //        _transCharArrayInit = "{";
        //        for (int i = 0; i < _transCharArraySize; i++) {
        //            _transCharArrayInit += seperator + "0";
        //            seperator = ", ";
        //        }
        //        _transCharArrayInit += "}";

        //        writeTopDown(stream);
        writeTypes(stream);
        writeFiFo(stream);
        writeFSM(stream);
        writeTestbench(stream);
    }

    void ChartToVHDL::writeFSM(std::ostream & stream) {

        // create hardware top level
        stream << "-- FSM Logic" << std::endl;
        writeIncludes(stream);
        stream << "entity fsm_scxml is" << std::endl;
        stream << "port(" << std::endl;
        stream << "    --inputs" << std::endl;
        stream << "    clk  :in    std_logic;" << std::endl;
        stream << "    rst  :in    std_logic;" << std::endl;
        stream << "    en   :in    std_logic;" << std::endl;
        stream << "    next_event_i    :in  event_type;" << std::endl;
        stream << "    next_event_int_en_i :in  std_logic;" << std::endl;
        stream << "    next_event_ext_en_i :in  std_logic;" << std::endl;
        stream << "    --outputs" << std::endl;
        stream << "    completed_o :out std_logic;" << std::endl;
        stream << "    error_o     :out std_logic;" << std::endl;

        for (int i = 0; i < _transitions.size(); i++) {
            Element<std::string> transition(_transitions[i]);
            //            if (transition.getChildNodes().getLength() > 0) {
            stream << "    " << ATTR(transition, "id") << "_o :out std_logic;" << std::endl;
            //            }
        }

        stream << "    current_state_o  :out state_type;" << std::endl;
        stream << "    entry_set_o  :out state_type;" << std::endl;
        stream << "    exit_set_o  :out state_type" << std::endl;
        stream << ");" << std::endl;
        stream << "end fsm_scxml; " << std::endl;

        stream << std::endl;
        stream << std::endl;
        stream << "architecture behavioral of fsm_scxml is " << std::endl;
        stream << std::endl;

        // Add signals and components
        writeSignals(stream);

        stream << std::endl;
        stream << "begin" << std::endl;
        stream << std::endl;
        // signal mapping
        writeModuleInstantiation(stream);

        // write fsm architecture
        writeNextStateLogic(stream);
        writeOutputLogic(stream);
        writeErrorHandler(stream);

        stream << std::endl;
        stream << "end behavioral; " << std::endl;
        stream << "-- END FSM Logic" << std::endl;
    }

    void ChartToVHDL::writeTopDown(std::ostream & stream) {
        // create hardware top level
        stream << "-- top level" << std::endl;
        writeIncludes(stream);
        stream << "entity top_scxml is" << std::endl;
        stream << "port(" << std::endl;
        stream << "    --inputs" << std::endl;
        stream << "    clk\t:in    std_logic;" << std::endl;
        stream << "    rst\t:in    std_logic;" << std::endl;
        stream << "    --outputs" << std::endl;
        stream << "    completed_o\t:out    std_logic;" << std::endl;
        stream << "    result_o\t:out    std_logic;" << std::endl;
        stream << "    error_o\t:out    std_logic" << std::endl;
        stream << ");" << std::endl;
        stream << "end top_scxml; " << std::endl;
        stream << std::endl;
        stream << std::endl;
        stream << "architecture behavioral of top_scxml is " << std::endl;
        stream << std::endl;

        // Add signals and components
        writeSignals(stream);

        stream << std::endl;
        stream << "begin" << std::endl;
        stream << std::endl;
        // signal mapping
        writeModuleInstantiation(stream);

        // write fsm architecture
        writeNextStateLogic(stream);
        writeOutputLogic(stream);

        stream << std::endl;
        stream << "end behavioral; " << std::endl;
    }

    void ChartToVHDL::writeTypes(std::ostream & stream) {
        std::string seperator = "";

        stream << "-- needed global types" << std::endl;
        stream << "library IEEE;" << std::endl;
        stream << "use IEEE.std_logic_1164.all;" << std::endl;
        stream << std::endl;
        stream << "package generated_p1 is" << std::endl;
        // create state type
        stream << "  subtype state_type is std_logic_vector(";
        stream << _states.size() - 1;
        stream << " downto 0);" << std::endl;

        //TODO complete
        // create event type
        stream << "  type event_type is (";
        seperator = "";
        for (int i = 0; i < _events.size(); i++) {
            stream << seperator;
            stream << _events[i];
            seperator = ", ";
        }
        if (seperator.size() == 0) {
            stream << "NO_EVENTS";
        }
        stream << ");" << std::endl;

        stream << "end generated_p1;" << std::endl;
        stream << std::endl;
        stream << "-- END needed global types" << std::endl;
    }

    void ChartToVHDL::writeIncludes(std::ostream & stream) {
        // Add controler specific stuff here
        stream << "library IEEE;" << std::endl;
        stream << "use IEEE.std_logic_1164.all;" << std::endl;
        stream << "use work.generated_p1.all;" << std::endl;
        stream << "use ieee.numeric_std.all;" << std::endl;
        stream << std::endl;
    }

    void ChartToVHDL::writeFiFo(std::ostream & stream) {
        // taken from: http://www.deathbylogic.com/2013/07/vhdl-standard-fifo/
        // alternativly take fifo logic for a ram device: http://www.eng.auburn.edu/~strouce/class/elec4200/vhdlmods.pdf
        stream << "-- standard FIFO buffer" << std::endl;
        writeIncludes(stream);
        stream << "" << std::endl;
        stream << "entity std_fifo is" << std::endl;
        stream << "generic (" << std::endl;
        stream << "  constant FIFO_DEPTH  : positive := 256" << std::endl;
        stream << ");" << std::endl;
        stream << "port ( " << std::endl;
        stream << "  clk      : in  std_logic;" << std::endl;
        stream << "  rst      : in  std_logic;" << std::endl;
        stream << "  write_en  : in  std_logic;" << std::endl;
        stream << "  read_en     : in  std_logic;" << std::endl;
        stream << "  data_in     : in  event_type;" << std::endl;
        stream << "  data_out  : out event_type;" << std::endl;
        stream << "  empty       : out std_logic;" << std::endl;
        stream << "  full        : out std_logic" << std::endl;
        stream << ");" << std::endl;
        stream << "end std_fifo;" << std::endl;
        stream << "" << std::endl;
        stream << "architecture behavioral of std_fifo is" << std::endl;
        stream << "begin" << std::endl;
        stream << "-- Memory Pointer Process" << std::endl;
        stream << "fifo_proc : process (clk)" << std::endl;
        stream << "  type FIFO_Memory is array (0 to FIFO_DEPTH - 1) of event_type;" << std::endl;
        stream << "  variable Memory : FIFO_Memory;" << std::endl;
        stream << "" << std::endl;
        stream << "  variable Head : natural range 0 to FIFO_DEPTH - 1;" << std::endl;
        stream << "  variable Tail : natural range 0 to FIFO_DEPTH - 1;" << std::endl;
        stream << "" << std::endl;
        stream << "  variable Looped : boolean;" << std::endl;
        stream << "begin" << std::endl;
        stream << "  if rising_edge(clk) then" << std::endl;
        stream << "    if rst = '1' then" << std::endl;
        stream << "      Head := 0;" << std::endl;
        stream << "      Tail := 0;" << std::endl;
        stream << "" << std::endl;
        stream << "      Looped := false;" << std::endl;
        stream << "" << std::endl;
        stream << "      full  <= '0';" << std::endl;
        stream << "      empty <= '1';" << std::endl;
        stream << "    else" << std::endl;
        stream << "      if (read_en = '1') then" << std::endl;
        stream << "        if ((Looped = true) or (Head /= Tail)) then" << std::endl;
        stream << "          -- Update data output" << std::endl;
        stream << "          data_out <= Memory(Tail);" << std::endl;
        stream << "          " << std::endl;
        stream << "          -- Update Tail pointer as needed" << std::endl;
        stream << "          if (Tail = FIFO_DEPTH - 1) then" << std::endl;
        stream << "            Tail := 0;" << std::endl;
        stream << "            " << std::endl;
        stream << "            Looped := false;" << std::endl;
        stream << "          else" << std::endl;
        stream << "            Tail := Tail + 1;" << std::endl;
        stream << "          end if;" << std::endl;
        stream << "" << std::endl;
        stream << "        end if;" << std::endl;
        stream << "      end if;" << std::endl;
        stream << "" << std::endl;
        stream << "      if (write_en = '1') then" << std::endl;
        stream << "        if ((Looped = false) or (Head /= Tail)) then" << std::endl;
        stream << "          -- Write Data to Memory" << std::endl;
        stream << "          Memory(Head) := data_in;" << std::endl;
        stream << "          " << std::endl;
        stream << "          -- Increment Head pointer as needed" << std::endl;
        stream << "          if (Head = FIFO_DEPTH - 1) then" << std::endl;
        stream << "            Head := 0;" << std::endl;
        stream << "            " << std::endl;
        stream << "            Looped := true;" << std::endl;
        stream << "          else" << std::endl;
        stream << "            Head := Head + 1;" << std::endl;
        stream << "          end if;" << std::endl;
        stream << "        end if;" << std::endl;
        stream << "      end if;" << std::endl;
        stream << "" << std::endl;
        stream << "      -- Update empty and full flags" << std::endl;
        stream << "      if (Head = Tail) then" << std::endl;
        stream << "        if Looped then" << std::endl;
        stream << "          full <= '1';" << std::endl;
        stream << "        else" << std::endl;
        stream << "          empty <= '1';" << std::endl;
        stream << "        end if;" << std::endl;
        stream << "      else" << std::endl;
        stream << "        empty  <= '0';" << std::endl;
        stream << "        full  <= '0';" << std::endl;
        stream << "      end if;" << std::endl;
        stream << "    end if;" << std::endl;
        stream << "  end if;" << std::endl;
        stream << "end process;" << std::endl;
        stream << "" << std::endl;
        stream << "end behavioral;" << std::endl;
        stream << "-- END standard FIFO buffer" << std::endl;
    }

    void ChartToVHDL::writeSignals(std::ostream & stream) {
        // create needed internal signals
        stream << "-- system signals" << std::endl;
        stream << "signal stall : std_logic;" << std::endl;
        stream << "signal completed : std_logic;" << std::endl;
        stream << "-- state signals" << std::endl;
        //        stream << "signal next_state : state_type;" << std::endl;
        //        stream << "signal current_state : state_type;" << std::endl;

        for (int i = 0; i < _states.size(); i++) {
            Element<std::string> state(_states[i]);
            stream << "signal " << ATTR(state, "id") << "_curr : std_logic;" << std::endl;
            stream << "signal " << ATTR(state, "id") << "_next : std_logic;" << std::endl;
            stream << "signal " << ATTR(state, "id") << "_exit : std_logic;" << std::endl;
            stream << "signal " << ATTR(state, "id") << "_entry : std_logic;" << std::endl;
        }
        stream << std::endl;
        stream << "-- event signals" << std::endl;
        stream << "signal int_event_write_en : std_logic;" << std::endl;
        stream << "signal int_event_read_en : std_logic;" << std::endl;
        stream << "signal int_event_empty : std_logic;" << std::endl;
        stream << "signal int_event_input : event_type;" << std::endl;
        stream << "signal int_event_output : event_type;" << std::endl;
        stream << "signal ext_event_write_en : std_logic;" << std::endl;
        stream << "signal ext_event_read_en : std_logic;" << std::endl;
        stream << "signal ext_event_empty : std_logic;" << std::endl;
        stream << "signal ext_event_input : event_type;" << std::endl;
        stream << "signal ext_event_output : event_type;" << std::endl;
        stream << "signal next_event_re : std_logic;" << std::endl;
        stream << "signal next_event : event_type;" << std::endl;
        stream << "signal event_consumed : std_logic;" << std::endl;
        for (int i = 0; i < _events.size(); i++) {
            stream << "signal " << _events[i] << "_sig : std_logic;" << std::endl;
        }
        stream << std::endl;
        stream << "-- transition signals" << std::endl;
        stream << "signal transition_spontaneous_en : std_logic;" << std::endl;

        for (int i = 0; i < _transitions.size(); i++) {
            Element<std::string> transition(_transitions[i]);
            stream << "signal " << ATTR(transition, "id") << "_sig : std_logic;"
                    << std::endl;
            stream << "signal " << ATTR(transition, "id") << "_sig_stage1 : std_logic;"
                    << std::endl;
        }

        stream << std::endl;
        stream << "-- error signals" << std::endl;
        stream << "signal reg_error_out : std_logic;" << std::endl;
        stream << "signal error_full_int_event_fifo : std_logic;" << std::endl;
        stream << std::endl;

        // add needed components
        stream << "-- event FIFO" << std::endl;
        stream << "component std_fifo is" << std::endl;
        stream << "port ( " << std::endl;
        stream << "	clk		: in  std_logic;" << std::endl;
        stream << "	rst		: in  std_logic;" << std::endl;
        stream << "	write_en	: in  std_logic;" << std::endl;
        stream << "	read_en         : in  std_logic;" << std::endl;
        stream << "	data_in         : in  event_type;" << std::endl;
        stream << "	data_out	: out event_type;" << std::endl;
        stream << "	empty           : out std_logic;" << std::endl;
        stream << "	full            : out std_logic" << std::endl; // we calculate how much we need
        stream << ");" << std::endl;
        stream << "end component;" << std::endl;
        stream << std::endl;
    }

    void ChartToVHDL::writeModuleInstantiation(std::ostream & stream) {
        // tmp mapping for events
        stream << "error_o <= reg_error_out; " << std::endl;
        stream << "stall <= not en or completed or rst; " << std::endl;
        stream << "completed_o <= completed; " << std::endl;
        stream << std::endl;

        stream << "next_event_re <= ( (not int_event_empty) or (not ext_event_empty) ) and not stall; " << std::endl;
        stream << "int_event_write_en <= next_event_int_en_i; " << std::endl;
        stream << "ext_event_write_en <= next_event_ext_en_i; " << std::endl;
        stream << "int_event_input <= next_event_i; " << std::endl;
        stream << "ext_event_input <= next_event_i; " << std::endl;
        stream << "int_event_read_en <= not transition_spontaneous_en and not stall; " << std::endl;
        stream << "ext_event_read_en <= not transition_spontaneous_en and not stall and int_event_empty; " << std::endl;
        stream << std::endl;

        for (int i = 0; i < _transitions.size(); i++) {
            Element<std::string> transition(_transitions[i]);
            //            if (transition.getChildNodes().getLength() > 0) {
            stream << ATTR(transition, "id") << "_o <= "
                    << ATTR(transition, "id") << "_sig;" << std::endl;
            //            }
        }
        stream << std::endl;

        for (int i = 0; i < _states.size(); i++) {
            Element<std::string> state(_states[i]);
            //            stream << "current_state(" << toStr(i) << ") <= " << ATTR(state, "id")
            //                    << "_curr;" << std::endl;
            //            stream << "next_state(" << toStr(i) << ") <= " << ATTR(state, "id")
            //                    << "_next;" << std::endl;
            stream << "current_state_o(" << toStr(i) << ") <= " << ATTR(state, "id")
                    << "_curr;" << std::endl;
            stream << "exit_set_o(" << toStr(i) << ") <= " << ATTR(state, "id")
                    << "_exit;" << std::endl;
            stream << "entry_set_o(" << toStr(i) << ") <= " << ATTR(state, "id")
                    << "_entry;" << std::endl;
        }
        stream << std::endl;

        // instantiate event fifo
        stream << "int_event_fifo : component std_fifo " << std::endl;
        stream << "port map ( " << std::endl;
        stream << "	clk         => clk," << std::endl;
        stream << "	rst         => rst," << std::endl;
        stream << "	write_en    => int_event_write_en," << std::endl;
        stream << "	read_en     => int_event_read_en," << std::endl;
        stream << "	data_in     => int_event_input," << std::endl;
        stream << "	data_out    => int_event_output," << std::endl;
        stream << "	empty       => int_event_empty," << std::endl;
        stream << "	full        => error_full_int_event_fifo" << std::endl; // we calculate how much we need
        stream << ");" << std::endl;
        stream << std::endl;

        stream << "ext_event_fifo : component std_fifo " << std::endl;
        stream << "port map ( " << std::endl;
        stream << "	clk         => clk," << std::endl;
        stream << "	rst         => rst," << std::endl;
        stream << "	write_en    => ext_event_write_en," << std::endl;
        stream << "	read_en     => ext_event_read_en," << std::endl;
        stream << "	data_in     => ext_event_input," << std::endl;
        stream << "	data_out    => ext_event_output," << std::endl;
        stream << "	empty       => ext_event_empty," << std::endl;
        stream << "	full        => error_full_int_event_fifo" << std::endl; // we calculate how much we need
        stream << ");" << std::endl;
        stream << std::endl;

        // event bus switch
        stream << "event_bus_switch: process (int_event_empty)" << std::endl;
        stream << "begin" << std::endl;
        stream << "  if int_event_empty = '1' then" << std::endl;
        stream << "    next_event <= ext_event_output;" << std::endl;
        stream << "  else" << std::endl;
        stream << "    next_event <= int_event_output;" << std::endl;
        stream << "  end if;" << std::endl;
        stream << "end process;" << std::endl << std::endl;

        // event signal set
        stream << "event_signal_set: process (next_event)" << std::endl;
        stream << "begin" << std::endl;
        stream << "  case next_event is" << std::endl;

        for (int i = 0; i < _events.size(); i++) {
            stream << "  when " << _events[i] << " =>" << std::endl;
            for (int j = 0; j < _events.size(); j++) {
                if (_events[j] == _events[i]) {
                    stream << _events[j] << "_sig <= '1';" << std::endl;
                } else {
                    stream << _events[j] << "_sig <= '0';" << std::endl;
                }
            }
        }

        stream << "  when others =>" << std::endl;
        for (int j = 0; j < _events.size(); j++) {
            stream << _events[j] << "_sig <= '0';" << std::endl;
        }
        stream << "  end case;" << std::endl;
        stream << "end process;" << std::endl << std::endl;

    }

    void ChartToVHDL::writeErrorHandler(std::ostream & stream) {
        // sets error output signal if an error occures somewhere
        stream << "-- error handler" << std::endl;
        stream << "-- sets error output signal if an error occures somewhere" << std::endl;
        stream << "error_handler : process (clk, rst) " << std::endl;
        stream << "begin" << std::endl;
        stream << "    if rst = '1' then" << std::endl;
        stream << "        reg_error_out <= '0';" << std::endl;
        stream << "    elsif rising_edge(clk) then" << std::endl;
        stream << "        reg_error_out <= error_full_int_event_fifo;" << std::endl;
        stream << "    end if;" << std::endl;
        stream << "end process;" << std::endl;
        stream << std::endl;
    }

    //TODO write event generator
    // wie die letzten beiden states erkennen
    // process bauen der bei fail 0 ausgibt und bei accept 1

    void ChartToVHDL::writeNextStateLogic(std::ostream & stream) {
        stream << "-- state logic" << std::endl;
        //        stream << "-- only gets active when state changes (microstep?) " << std::endl;
        //        stream << "state_decode_proc: process(";
        //
        //        for (int i = 0; i < _states.size(); i++) {
        //            Element<std::string> state(_states[i]);
        //            stream << ATTR(state, "id") << "_curr," << std::endl;
        //        }
        //
        //        stream << "next_event)" << std::endl;
        //        stream << "begin" << std::endl;

        std::stringstream nextStateBuffer;
        for (int i = 0; i < _states.size(); i++) {
            Element<std::string> state(_states[i]);

            // calculate event choises
            // _transitions is sorted in Postfix order
            // by stating with smalest index the most important
            // will be written first
            std::vector< Element<std::string> > choises;
            std::string spntaneous_trans_sig = "";
            for (int j = 0; j < _transitions.size(); j++) {
                Element<std::string> transition(_transitions[j]);
                if (ATTR_CAST(transition.getParentNode(), "id") == ATTR(state, "id")) {
                    choises.push_back(transition);
                    if (ATTR(transition, "event") == CONST_TRANS_SPONTANEOUS) {
                        spntaneous_trans_sig = ATTR(transition, "id");
                        // FIXME hofully there are just single spntaneous transitions allowed
                        // else we have to handle this
                    }
                }
            }

            // calculate incomming transitions (for later use)
            std::vector< Element<std::string> > incommingTransitions;
            for (int j = 0; j < _transitions.size(); j++) {
                Element<std::string> transition(_transitions[j]);
                if (ATTR(transition, "target") == ATTR(state, "id")) {
                    incommingTransitions.push_back(transition);
                }
            }

            if (choises.size() > 0) {// if no outgoing transitions (maybe final state :D) we don't write anything

                //                stream << "  if ( " << ATTR(state, "id") << "_curr = '1' ) then" << std::endl;
                //                stream << "    if ( transition_spontaneous_en = '1' ) then" << std::endl;

                // write transitions
                for (int j = 0; j < choises.size(); j++) {
                    Element<std::string> transition(choises[j]);
                    stream << ATTR(transition, "id") << "_sig_stage1 <= ( "
                            << ATTR(state, "id") << "_curr and ";
                    if (ATTR(transition, "id") == spntaneous_trans_sig) {
                        // spontaneous transitions
                        stream << "transition_spontaneous_en ";
                    } else {
                        // event driven transition
                        stream << "( not transition_spontaneous_en ) and " << std::endl
                                << "next_event_re" << std::endl;
                        // needed event
                        std::string eventName = ATTR(transition, "event");
                        if (eventName != CONST_EVENT_ANY) {
                            // if next_event_re is high, there is a valid event which matches to any
                            stream << " and  " << eventName << "_sig";
                        }
                    }
                    stream << ");" << std::endl;
                }

                //                    stream << "    elsif ( next_event_re = '1' ) then" << std::endl;
                //                    // if no spntaneous transition enables, look at events
                //                    // since there is just one event at a time, we use case statement
                //                    // to check transitions matching in postfix order
                //                    // FIXME hopefully there is just one transition per state and event at a time
                //                    stream << "    case next_event is" << std::endl;
                //                    bool hasWildcardTransition = false;
                //                    for (int j = 0; j < choises.size(); j++) {
                //                        Element<std::string> transition(choises[j]);
                //                        std::string eventName = ATTR(transition, "event");
                //                        if (eventName == CONST_EVENT_ANY) {
                //                            eventName = "others";
                //                            hasWildcardTransition = true;
                //                        }
                //                        stream << "      when " << eventName << " =>" << std::endl;
                //                        // activate transition and deactivete others
                //                        for (int k = 0; k < choises.size(); k++) {
                //                            Element<std::string> tmp_t(choises[k]);
                //                            if (ATTR(tmp_t, "event") == ATTR(transition, "event")) {
                //                                stream << "        " << ATTR(tmp_t, "id") << "_sig_stage1 <= '1';" << std::endl;
                //                            } else {
                //                                stream << "        " << ATTR(tmp_t, "id") << "_sig_stage1 <= '0';" << std::endl;
                //                            }
                //                        }
                //                    }
                //                    if (!hasWildcardTransition) {
                //                        // if there is no others we create one for deactivating everything
                //                        stream << "      when others =>" << std::endl;
                //                        for (int j = 0; j < choises.size(); j++) {
                //                            Element<std::string> tmp_t(choises[j]);
                //                            stream << "        " << ATTR(tmp_t, "id") << "_sig_stage1 <= '0';" << std::endl;
                //                        }
                //                    }
                //                    stream << "    end case;" << std::endl;
                //
                //
                //                    // no enabled event ? disable all transitions 
                //                    stream << "    else" << std::endl;
                //                    for (int j = 0; j < choises.size(); j++) {
                //                        Element<std::string> transition(choises[j]);
                //                        stream << "      " << ATTR(transition, "id") << "_sig_stage1 <= '0';" << std::endl;
                //                    }
                //                    stream << "    end if;" << std::endl;
                //
                //                    // state is not active? disable all transitions 
                //                    stream << "  else" << std::endl;
                //                    for (int j = 0; j < choises.size(); j++) {
                //                        Element<std::string> transition(choises[j]);
                //                        stream << "    " << ATTR(transition, "id") << "_sig_stage1 <= '0';" << std::endl;
                //                    }
                //                    stream << "  end if;" << std::endl;
                //                    stream << std::endl;
            }

            // write next state calculation in buffer for later use
            // for that we use unconflicted transition lines and
            // compute children for automatic (recursive) parent activation
            std::vector< Element<std::string> > stateChildren;
            for (int j = 0; j < _states.size(); j++) {
                Element<std::string> s(_states[j]);
                if (ATTR_CAST(s.getParentNode(), "id") == ATTR(state, "id")) {
                    stateChildren.push_back(s);
                }
            }

            // exit set
            std::string id = ATTR(state, "id");
            nextStateBuffer << ATTR(state, "id") << "_exit <= ( '0'";
            for (int j = 0; j < choises.size(); j++) {
                nextStateBuffer << " or "
                        << ATTR(choises[j], "id") << "_sig";
            }

            if (HAS_ATTR(state, "isCompound")) {
                // exit set of compound contains every transitions out of a child state
                for (int j = 0; j < _states.size(); j++) {
                    Element<std::string> s(_states[j]);
                    if (ATTR_CAST(s.getParentNode(), "id") == ATTR(state, "id")) {
                        nextStateBuffer << " or "
                                << ATTR(s, "id") << "_exit";
                    }
                }
            }
            nextStateBuffer << " );" << std::endl;

            // entry set
            nextStateBuffer << ATTR(state, "id") << "_entry <= ( '0'";
            for (int j = 0; j < incommingTransitions.size(); j++) {
                nextStateBuffer << " or "
                        << ATTR(incommingTransitions[j], "id") << "_sig";
            }
            nextStateBuffer << " );" << std::endl;

            // next round
            nextStateBuffer << ATTR(state, "id") << "_next <= ( ( '0'";
            if (!HAS_ATTR(state, "isCompound")) {
                // compount states will be entered through childs
                nextStateBuffer << " or " << ATTR(state, "id") << "_entry";
            }
            if (HAS_ATTR(state, "isDefaultFor")) {
                // default entry state for compound state
                nextStateBuffer << " or " << ATTR(state, "isDefaultFor") << "_entry";
            }
            nextStateBuffer << " ) or ";
            if (!HAS_ATTR(state, "isCompound")) {
                // compound state is just defined through child states
                // no relation to exit set or current state (holding state)
                nextStateBuffer << "( ( not ( '0'";
                nextStateBuffer << " or " << ATTR(state, "id") << "_exit";
                nextStateBuffer << " ) ) and " << ATTR(state, "id") << "_curr ) or";
            }
            nextStateBuffer << " ( '0' ";

            for (int j = 0; j < stateChildren.size(); j++) {
                nextStateBuffer << " or " << ATTR(stateChildren[j], "id")
                        << "_next";
            }

            nextStateBuffer << " ) );" << std::endl << std::endl;
        }
        //        stream << "end process;" << std::endl;
        stream << std::endl;
        // write outgoing transition buffer
        stream << nextStateBuffer.str() << std::endl;

        // calculate conflicts and write resolver
        std::string conflictBools;
        for (unsigned int j = 0; j < _transitions.size(); j++) {
            Element<std::string> transition(_transitions[j]);

            stream << ATTR(transition, "id") << "_sig <= ( "
                    << ATTR(transition, "id") << "_sig_stage1 ) and ( not ( '0' ";

            for (int k = 0; k < _transitions.size(); k++) {
                Element<std::string> t2(_transitions[k]);
                if (ATTR(transition, "id") != ATTR(t2, "id")) {
                    if (hasIntersection(computeExitSet(transition), computeExitSet(t2)) ||
                            (getSourceState(transition) == getSourceState(t2)) ||
                            (isDescendant(getSourceState(transition), getSourceState(t2))) ||
                            (isDescendant(getSourceState(t2), getSourceState(transition)))) {
                        stream << " or " << ATTR(t2, "id") << "_sig_stage1";
                    } else {
                        conflictBools += "0";
                    }
                }
            }

            stream << " ) );" << std::endl;
        }
        stream << std::endl;

        // updater for current state
        stream << "-- update current state" << std::endl;
        stream << "state_proc: process(clk, rst, stall)" << std::endl;
        stream << "begin" << std::endl;
        stream << "    if rst = '1' then" << std::endl;
        stream << "        " << _initState << "_curr <= '1';" << std::endl;

        for (int i = 0; i < _states.size(); i++) {
            Element<std::string> state(_states[i]);
            if (ATTR(state, "id") != _initState) {
                stream << "        " << ATTR(state, "id") << "_curr <= '0';" << std::endl;
            }
        }

        stream << "    elsif (rising_edge(clk) and stall = '0') then" << std::endl;
        for (int i = 0; i < _states.size(); i++) {
            Element<std::string> state(_states[i]);
            stream << "        " << ATTR(state, "id") << "_curr <= "
                    << ATTR(state, "id") << "_next;" << std::endl;
        }
        stream << "    end if;" << std::endl;
        stream << "end process;" << std::endl;
        stream << std::endl;
    }

    void ChartToVHDL::writeOutputLogic(std::ostream & stream) {
        stream << "-- output logic" << std::endl;
        stream << "-- spontaneous transition calculation" << std::endl;
        stream << "transition_spontaneous_en <= '0'";

        for (int i = 0; i < _states.size(); i++) {
            Element<std::string> state(_states[i]);

            for (int j = 0; j < _transitions.size(); j++) {
                Element<std::string> transition(_transitions[j]);
                if (ATTR_CAST(transition.getParentNode(), "id") == ATTR(state, "id")) {
                    if (ATTR(transition, "event") == CONST_TRANS_SPONTANEOUS) {
                        stream << " or " << ATTR(state, "id") << "_curr";
                    }
                }
            }
        }
        stream << ";" << std::endl;
        stream << "-- complete calculation" << std::endl;
        stream << "completed <= '0'";
        for (int i = 0; i < _superFinalStates.size(); i++) {
            Element<std::string> state(_superFinalStates[i]);
            stream << " or " << ATTR(state, "id") << "_curr";
        }
        stream << ";" << std::endl;
        stream << "-- END output logic" << std::endl;
        stream << std::endl;
    }

    void ChartToVHDL::writeTestbench(std::ostream & stream) {
        stream << "-- Testbench for SCXML Modul" << std::endl;
        stream << " " << std::endl;
        writeIncludes(stream);
        stream << " " << std::endl;
        stream << "-- empty entity for testbench" << std::endl;
        stream << "entity testbench is" << std::endl;
        stream << "end entity testbench;" << std::endl;
        stream << " " << std::endl;
        stream << "architecture bhv of testbench is" << std::endl;
        stream << " " << std::endl;
        stream << "  -- modul declaration" << std::endl;
        stream << "  component fsm_scxml is" << std::endl;
        stream << "  port (" << std::endl;
        stream << "    --inputs" << std::endl;
        stream << "    clk  :in    std_logic;" << std::endl;
        stream << "    rst  :in    std_logic;" << std::endl;
        stream << "    en   :in    std_logic;" << std::endl;
        stream << "    next_event_i    :in  event_type;" << std::endl;
        stream << "    next_event_int_en_i :in  std_logic;" << std::endl;
        stream << "    next_event_ext_en_i :in  std_logic;" << std::endl;
        stream << "    --outputs" << std::endl;
        stream << "    completed_o :out std_logic;" << std::endl;
        stream << "    error_o     :out std_logic;" << std::endl;

        for (int i = 0; i < _transitions.size(); i++) {
            Element<std::string> transition(_transitions[i]);
            //            if (transition.getChildNodes().getLength() > 0) {
            stream << "    " << ATTR(transition, "id") << "_o :out std_logic;" << std::endl;
            //            }
        }

        stream << "    current_state_o  :out state_type;" << std::endl;
        stream << "    entry_set_o  :out state_type;" << std::endl;
        stream << "    exit_set_o  :out state_type" << std::endl;
        stream << "  );" << std::endl;
        stream << "  end component;" << std::endl;
        stream << " " << std::endl;
        stream << "  -- input" << std::endl;
        stream << "  signal clk   : std_logic := '0';" << std::endl;
        stream << "  signal reset : std_logic;" << std::endl;
        stream << "  signal en    : std_logic;" << std::endl;
        stream << "  signal next_event_i : event_type;" << std::endl;
        stream << "  signal next_event_int_en_i :  std_logic;" << std::endl;
        stream << "  signal next_event_ext_en_i :  std_logic;" << std::endl;
        stream << " " << std::endl;
        stream << "  -- output" << std::endl;
        //        stream << "  signal result_o : std_logic;" << std::endl;
        stream << "  signal completed_o : std_logic;" << std::endl;
        stream << "  signal error_o : std_logic;" << std::endl;

        for (int i = 0; i < _transitions.size(); i++) {
            Element<std::string> transition(_transitions[i]);
            //            if (transition.getChildNodes().getLength() > 0) {
            stream << "  signal " << ATTR(transition, "id") << "_o : std_logic;" << std::endl;
            //            }
        }

        stream << "  signal current_state_o  : state_type;" << std::endl;
        stream << "  signal entry_set_o  : state_type;" << std::endl;
        stream << "  signal exit_set_o  : state_type;" << std::endl;
        stream << " " << std::endl;
        stream << "begin" << std::endl;
        stream << "  clk   <= not clk  after 20 ns;  -- 25 MHz " << std::endl;
        stream << "  reset <= '1', '0' after 100 ns; -- reset signal" << std::endl;
        stream << "  en <= '0', '1' after 50 ns; -- enable signal" << std::endl;
        stream << " " << std::endl;
        stream << "  -- modul instatciation" << std::endl;
        stream << "  dut : component fsm_scxml" << std::endl;
        stream << "    port map (" << std::endl;
        stream << "      clk       => clk," << std::endl;
        stream << "      rst       => reset," << std::endl;
        stream << "      en        => en," << std::endl;
        stream << "      next_event_i => next_event_i," << std::endl;
        stream << "      next_event_int_en_i => next_event_int_en_i," << std::endl;
        stream << "      next_event_ext_en_i => next_event_ext_en_i," << std::endl;
        stream << " " << std::endl;

        for (int i = 0; i < _transitions.size(); i++) {
            Element<std::string> transition(_transitions[i]);
            //            if (transition.getChildNodes().getLength() > 0) {
            stream << "       " << ATTR(transition, "id") << "_o  => "
                    << ATTR(transition, "id") << "_o," << std::endl;
            //            }
        }

        stream << "      current_state_o  =>  current_state_o," << std::endl;
        stream << "      entry_set_o  =>  entry_set_o," << std::endl;
        stream << "      exit_set_o  =>  exit_set_o," << std::endl;
        //        stream << "      result_o  => result_o," << std::endl;
        stream << "      completed_o => completed_o," << std::endl;
        stream << "      error_o => error_o" << std::endl;
        stream << "    );" << std::endl;
        stream << "" << std::endl;
        stream << "  -- stimulation code" << std::endl;
        stream << " " << std::endl;
        stream << "end architecture;" << std::endl;
        stream << "-- END Testbench" << std::endl;
        stream << std::endl;
    }

}