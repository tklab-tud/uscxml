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
#include <math.h>
#include <boost/algorithm/string.hpp>
#include <glog/logging.h>

#include <algorithm>
#include <iomanip>

#include <sstream>

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

        // filter states
        elements.clear();
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
            if (!HAS_ATTR(state, "id")) {
                std::stringstream ss;
                ss << "HWS_" << toStr(i);
                state.setAttribute("id", ss.str());
            }
            _stateNames[ATTR(state, "id")] = state;
        }
        _initState = ATTR(_scxml, "initial");

        // filter transitions
        elements.clear();
        elements.insert(_nsInfo.xmlNSPrefix + "transition");
        _transitions = inPostFixOrder(elements, _scxml);

        for (int i = 0; i < _transitions.size(); i++) {
            Element<std::string> transition(_transitions[i]);
            transition.setAttribute("postFixOrder", toStr(i));
        }

        // how many bits do we need to represent the state array?
        std::string seperator;
        _stateCharArraySize = ceil((float) _states.size() / (float) 8);
        _stateCharArrayInit = "{";
        for (int i = 0; i < _stateCharArraySize; i++) {
            _stateCharArrayInit += seperator + "0";
            seperator = ", ";
        }
        _stateCharArrayInit += "}";

        seperator = "";
        _transCharArraySize = ceil((float) _transitions.size() / (float) 8);
        _transCharArrayInit = "{";
        for (int i = 0; i < _transCharArraySize; i++) {
            _transCharArrayInit += seperator + "0";
            seperator = ", ";
        }
        _transCharArrayInit += "}";

        writeTopDown(stream);
    }

    void ChartToVHDL::writeTopDown(std::ostream& stream) {
        // write needed global types
        writeTypes(stream);
        writeFiFo(stream);
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

    void ChartToVHDL::writeTypes(std::ostream& stream) {
        std::string seperator = "";

        stream << "-- needed global types" << std::endl;
        stream << "library IEEE;" << std::endl;
        stream << "use IEEE.std_logic_1164.all;" << std::endl;
        stream << std::endl;
        stream << "package generated_p1 is" << std::endl;
        // create state type
        stream << "type state_type is (";
        seperator = "";
        for (int i = 0; i < _states.size(); i++) {
            Element<std::string> state(_states[i]);
            if (HAS_ATTR(state, "id")) {
                if (_initState.size() == 0) {
                    std::stringstream ss;
                    ss << "HWS_" << escape(ATTR(state, "id"));
                    _initState = ss.str();
                }
                stream << seperator << "HWS_";
                stream << escape(ATTR(state, "id"));
                seperator = ",";
            }
        }
        stream << ");" << std::endl;

        //TODO complete
        // create event type
        stream << "type event_type is (";
        seperator = "";
        std::vector<std::string> eventNames;
        for (int i = 0; i < _transitions.size(); i++) {
            Element<std::string> transition(_transitions[i]);
            if (HAS_ATTR(transition, "event")) {
                // create event name and check if it already exists
                std::string eventName = escape(ATTR(transition, "event"));
                if (eventName == "*") {
                    eventName = "ANY";
                }
                if (!(std::find(eventNames.begin(), eventNames.end(), eventName)
                        != eventNames.end())) {
                    eventNames.push_back(eventName);
                    stream << seperator << "HWE_";
                    stream << eventName;
                    seperator = ", ";
                }
            }
        }
        if (seperator.size() == 0) {
            stream << "NO_EVENTS";
        }
        stream << ");" << std::endl;

        stream << "end generated_p1;" << std::endl;
        stream << std::endl;
    }

    void ChartToVHDL::writeIncludes(std::ostream& stream) {
        // Add controler specific stuff here
        stream << "library IEEE;" << std::endl;
        stream << "use IEEE.std_logic_1164.all;" << std::endl;
        stream << "use work.generated_p1.all;" << std::endl;
        stream << std::endl;
    }

    void ChartToVHDL::writeFiFo(std::ostream& stream) {
        // taken from: http://www.deathbylogic.com/2013/07/vhdl-standard-fifo/
        // alternativly take fifo logic for a ram device: http://www.eng.auburn.edu/~strouce/class/elec4200/vhdlmods.pdf
        stream << "-- standard FIFO buffer" << std::endl;
        writeIncludes(stream);
        stream << "entity std_fifo is" << std::endl;
        stream << "generic (" << std::endl;
        stream << "	constant FIFO_DEPTH	: positive := 256" << std::endl;
        stream << ");" << std::endl;
        stream << "port ( " << std::endl;
        stream << "	clk			: in  std_logic;" << std::endl;
        stream << "	rst			: in  std_logic;" << std::endl;
        stream << "	write_en	: in  std_logic;" << std::endl;
        stream << "	read_en     : in  std_logic;" << std::endl;
        stream << "	data_in     : in  event_type;" << std::endl;
        stream << "	data_out	: out event_type;" << std::endl;
        stream << "	empty       : out std_logic;" << std::endl;
        stream << "	full        : out std_logic" << std::endl;
        stream << ");" << std::endl;
        stream << "end std_fifo;" << std::endl;
        stream << "" << std::endl;
        stream << "architecture behavioral of std_fifo is" << std::endl;
        stream << "begin" << std::endl;
        stream << "-- Memory Pointer Process" << std::endl;
        stream << "fifo_proc : process (clk)" << std::endl;
        stream << "	type FIFO_Memory is array (0 to FIFO_DEPTH - 1) of event_type;" << std::endl;
        stream << "	variable Memory : FIFO_Memory;" << std::endl;
        stream << std::endl;
        stream << "	variable Head : natural range 0 to FIFO_DEPTH - 1;" << std::endl;
        stream << "	variable Tail : natural range 0 to FIFO_DEPTH - 1;" << std::endl;
        stream << std::endl;
        stream << "	variable Looped : boolean;" << std::endl;
        stream << "begin" << std::endl;
        stream << "	if rising_edge(clk) then" << std::endl;
        stream << "		if rst = '1' then" << std::endl;
        stream << "			Head := 0;" << std::endl;
        stream << "			Tail := 0;" << std::endl;
        stream << std::endl;
        stream << "			Looped := false;" << std::endl;
        stream << std::endl;
        stream << "			full  <= '0';" << std::endl;
        stream << "			empty <= '1';" << std::endl;
        stream << "		else" << std::endl;
        stream << "			if (read_en = '1') then" << std::endl;
        stream << "				if ((Looped = true) or (Head /= Tail)) then" << std::endl;
        stream << "					-- Update data output" << std::endl;
        stream << "					data_out <= Memory(Tail);" << std::endl;
        stream << "					" << std::endl;
        stream << "					-- Update Tail pointer as needed" << std::endl;
        stream << "					if (Tail = FIFO_DEPTH - 1) then" << std::endl;
        stream << "						Tail := 0;" << std::endl;
        stream << "						" << std::endl;
        stream << "						Looped := false;" << std::endl;
        stream << "					else" << std::endl;
        stream << "						Tail := Tail + 1;" << std::endl;
        stream << "					end if;" << std::endl;
        stream << std::endl;
        stream << "				end if;" << std::endl;
        stream << "			end if;" << std::endl;
        stream << std::endl;
        stream << "			if (write_en = '1') then" << std::endl;
        stream << "				if ((Looped = false) or (Head /= Tail)) then" << std::endl;
        stream << "					-- Write Data to Memory" << std::endl;
        stream << "					Memory(Head) := data_in;" << std::endl;
        stream << "					" << std::endl;
        stream << "					-- Increment Head pointer as needed" << std::endl;
        stream << "					if (Head = FIFO_DEPTH - 1) then" << std::endl;
        stream << "						Head := 0;" << std::endl;
        stream << "						" << std::endl;
        stream << "						Looped := true;" << std::endl;
        stream << "					else" << std::endl;
        stream << "						Head := Head + 1;" << std::endl;
        stream << "					end if;" << std::endl;
        stream << "				end if;" << std::endl;
        stream << "			end if;" << std::endl;
        stream << std::endl;
        stream << "			-- Update empty and full flags" << std::endl;
        stream << "			if (Head = Tail) then" << std::endl;
        stream << "				if Looped then" << std::endl;
        stream << "					full <= '1';" << std::endl;
        stream << "				else" << std::endl;
        stream << "					empty <= '1';" << std::endl;
        stream << "				end if;" << std::endl;
        stream << "			else" << std::endl;
        stream << "				empty	<= '0';" << std::endl;
        stream << "				full	<= '0';" << std::endl;
        stream << "			end if;" << std::endl;
        stream << "		end if;" << std::endl;
        stream << "	end if;" << std::endl;
        stream << "end process;" << std::endl;
        stream << std::endl;
        stream << "end behavioral;" << std::endl;
        stream << std::endl;
    }

    void ChartToVHDL::writeSignals(std::ostream& stream) {
        // create needed internal signals
        stream << "-- system signals" << std::endl;
        stream << "signal stall : std_logic;" << std::endl;
        stream << "-- state signals" << std::endl;
        stream << "signal next_state : state_type;" << std::endl;
        stream << "signal current_state : state_type;" << std::endl;
        stream << std::endl;
        stream << "-- event signals" << std::endl;
        stream << "signal int_event_write_en : std_logic;" << std::endl;
        stream << "signal int_event_read_en : std_logic;" << std::endl;
        stream << "signal int_event_empty : std_logic;" << std::endl;
        stream << "signal int_event_input : event_type;" << std::endl;
        stream << "signal int_event_output : event_type;" << std::endl;
        stream << "signal next_event_valid : std_logic;" << std::endl;
        stream << "signal next_event : event_type;" << std::endl;
        stream << std::endl;
        stream << "-- error signals" << std::endl;
        stream << "signal reg_error_out : std_logic;" << std::endl;
        stream << "signal error_full_int_event_fifo : std_logic;" << std::endl;
        stream << std::endl;

        // add needed components
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

    void ChartToVHDL::writeModuleInstantiation(std::ostream& stream) {
        // tmp mapping for events
        stream << "error_o <= reg_error_out; " << std::endl;
        stream << "next_event_valid <= not int_event_empty; " << std::endl;
        stream << "next_event <= int_event_output; " << std::endl;
        stream << "stall <= '0'; " << std::endl;
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
    }

    void ChartToVHDL::writeErrorHandler(std::ostream& stream) {
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

    void ChartToVHDL::writeNextStateLogic(std::ostream& stream) {
        stream << "-- state logic" << std::endl;
        stream << "state_decode_proc: process(current_state, next_event, next_event_valid)" << std::endl;
        stream << "begin" << std::endl;
        stream << "    case current_state is" << std::endl;

        for (int i = 0; i < _states.size(); i++) {
            Element<std::string> state(_states[i]);
            if (HAS_ATTR(state, "id")) {

                std::vector<std::string> choises;
                for (int j = 0; j < _transitions.size(); j++) {
                    Element<std::string> transition(_transitions[j]);
                    if (ATTR_CAST(transition.getParentNode(), "id") == ATTR(state, "id")) {
                        std::string eventName = escape(ATTR(transition, "event"));
                        if (eventName == "*") {
                            eventName = "ANY";
                        }
                        std::stringstream ss;
                        ss << "if (next_event_valid = '1' and next_event = HWE_";
                        ss << eventName << ") then" << std::endl;
                        ss << "        next_state <= HWS_" << escape(ATTR(transition, "target")) << ";" << std::endl;
                        choises.push_back(ss.str());
                    }
                }
                // TODO do not produce empty statements

                if (choises.size() > 0) {
                    stream << "    when HWS_" << escape(ATTR(state, "id")) << " =>" << std::endl;
                    std::string seperator = "";
                    for (int j = 0; j < choises.size(); j++) {
                        stream << seperator;
                        stream << choises[j] << std::endl;
                        seperator = "els";
                    }

                    stream << "    else" << std::endl;
                    stream << "        next_state <= HWS_" << escape(ATTR(state, "id")) << ";" << std::endl;
                    stream << "    end if;" << std::endl;
                }
            }

        }

        stream << "    when others =>" << std::endl;
        stream << "     next_state <= current_state;" << std::endl;
        stream << "    end case;" << std::endl;
        stream << "end process;" << std::endl;
        stream << std::endl;

        // updater for current state
        stream << "-- update current state" << std::endl;
        stream << "state_proc: process(clk, rst, stall)" << std::endl;
        stream << "begin" << std::endl;
        stream << "    if rst = '1' then" << std::endl;
        stream << "        current_state <= " << _initState << ";" << std::endl;
        stream << "    elsif (rising_edge(clk) and stall = '0') then" << std::endl;
        stream << "        current_state <= next_state;" << std::endl;
        stream << "    end if;" << std::endl;
        stream << "end process;" << std::endl;
        stream << std::endl;
    }

    void ChartToVHDL::writeOutputLogic(std::ostream& stream) {
        stream << "-- output logic" << std::endl;
        stream << "output_proc: process(current_state)" << std::endl;
        stream << "begin" << std::endl;
        stream << "    case current_state is" << std::endl;

        for (int i = 0; i < _states.size(); i++) {
            //TODO
            // if end state set completed and result 
            // on entry events generated here
        }

        stream << "    when others =>" << std::endl;
        stream << "        completed_o <= '0';" << std::endl;
        stream << "        result_o <= '0';" << std::endl;

        stream << "end case;" << std::endl;
        stream << "end process;" << std::endl;
        stream << std::endl;
    }



}