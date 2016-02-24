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

#include "uscxml/transform/ChartToVHDL.h"
#include "uscxml/debug/Complexity.h"
#include <DOM/io/Stream.hpp>
#include <iostream>
#include "uscxml/UUID.h"
#include "uscxml/dom/DOMUtils.h"
#include <math.h>
#include <boost/algorithm/string.hpp>
#include <glog/logging.h>

#include <algorithm>
#include <iomanip>

#include <sstream>

#define CONST_TRANS_SPONTANIOUS "HWE_NOW"
#define CONST_EVENT_ANY "HWE_ANY"

namespace uscxml {

using namespace Arabica::DOM;
using namespace Arabica::XPath;

Transformer ChartToVHDL::transform(const Interpreter& other) {
	ChartToVHDL* c2c = new ChartToVHDL(other);

	return boost::shared_ptr<TransformerImpl>(c2c);
}

ChartToVHDL::ChartToVHDL(const Interpreter& other) : ChartToC(other), _eventTrie(".") {
}

ChartToVHDL::~ChartToVHDL() {
}

void ChartToVHDL::checkDocument() {
	// filter unsupported stuff
	Arabica::XPath::NodeSet<std::string> unsupported;

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

	elements.insert(_nsInfo.xmlNSPrefix + "if"); // implicit elseif und else
	elements.insert(_nsInfo.xmlNSPrefix + "foreach");
	elements.insert(_nsInfo.xmlNSPrefix + "send");
	elements.insert(_nsInfo.xmlNSPrefix + "cancel");
	elements.insert(_nsInfo.xmlNSPrefix + "invoke");
	elements.insert(_nsInfo.xmlNSPrefix + "finalize");
	unsupported = DOMUtils::inDocumentOrder(elements, _scxml);

	std::stringstream ss;
	if (unsupported.size() > 0) {
		for (size_t i = 0; i < unsupported.size(); i++) {
			ss << "  " << DOMUtils::xPathForNode(unsupported[i]) << " unsupported" << std::endl;
		}
		throw std::runtime_error("Unsupported elements found:\n" + ss.str());
	}

	elements.clear();
	elements.insert(_nsInfo.xmlNSPrefix + "transition");
	unsupported = DOMUtils::inDocumentOrder(elements, _scxml);

	for (size_t i = 0; i < unsupported.size(); i++) {
		Element<std::string> transition(unsupported[i]);
		if (HAS_ATTR(transition, "cond")) {
			ERROR_PLATFORM_THROW("transition with conditions not supported!");
		}
		if (!HAS_ATTR(transition, "target")) {
			ERROR_PLATFORM_THROW("targetless transition not supported!");
		}
	}

}

void ChartToVHDL::findEvents() {
	// elements with an event attribute
	NodeSet<std::string> withEvent;
	withEvent.push_back(DOMUtils::filterChildElements(_nsInfo.xmlNSPrefix + "raise", _scxml, true));
	withEvent.push_back(DOMUtils::filterChildElements(_nsInfo.xmlNSPrefix + "send", _scxml, true));
	withEvent.push_back(DOMUtils::filterChildElements(_nsInfo.xmlNSPrefix + "transition", _scxml, true));

	for (size_t i = 0; i < withEvent.size(); i++) {
		if (HAS_ATTR_CAST(withEvent[i], "event")) {
			// TODO: tokenize!
			if (ATTR_CAST(withEvent[i], "event") != "*")
				_eventTrie.addWord(ATTR_CAST(withEvent[i], "event"));
		}
	}
}

void ChartToVHDL::writeTo(std::ostream& stream) {
	// same preparations as the C transformation
	prepare();

//    checkDocument();
	findEvents();

	writeTypes(stream);
	writeFiFo(stream);
	writeFSM(stream);
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
	stream << "    next_event_en_i :in  std_logic;" << std::endl;
	stream << "    --outputs" << std::endl;
	stream << "    completed_o :out std_logic;" << std::endl;
	stream << "    error_o     :out std_logic;" << std::endl;
	stream << "    current_state_o  :out state_type" << std::endl;
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
//	writeNextStateLogic(stream);
    
    writeOptimalTransitionSetSelection(stream);
    writeExitSet(stream);
    writeEntrySet(stream);

	//        writeOutputLogic(stream);
	writeErrorHandler(stream);

    
	stream << std::endl;
	stream << "end behavioral; " << std::endl;
	stream << "-- END FSM Logic" << std::endl;
}

#if 0
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
#endif

void ChartToVHDL::writeTypes(std::ostream & stream) {
	std::string seperator = "";

	stream << "-- required global types" << std::endl;
	stream << "library IEEE;" << std::endl;
	stream << "use IEEE.std_logic_1164.all;" << std::endl;
	stream << std::endl;
	stream << "package machine" << _md5 << " is" << std::endl;
	// create state type
	stream << "  subtype state_type is std_logic_vector( ";
	stream << _states.size() - 1;
	stream << " downto 0);" << std::endl;

	//TODO complete
	// create event type
	stream << "  type event_type is (";
	seperator = "";
//	for (size_t i = 0; i < _events.size(); i++) {
//		stream << seperator;
//		stream << _events[i];
//		seperator = ", ";
//	}
	if (seperator.size() == 0) {
		stream << "NO_EVENTS";
	}
	stream << ");" << std::endl;

	stream << "end machine" << _md5 << ";" << std::endl;
	stream << std::endl;
	stream << "-- END needed global types" << std::endl;
}

void ChartToVHDL::writeIncludes(std::ostream & stream) {
	// Add controler specific stuff here
	stream << "library IEEE;" << std::endl;
	stream << "use IEEE.std_logic_1164.all;" << std::endl;
	stream << "use work.machine" << _md5 << ".all;" << std::endl;
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
	stream << "-- state signals" << std::endl;
//	stream << "signal next_state : state_type;" << std::endl;
//	stream << "signal current_state : state_type;" << std::endl;

	for (size_t i = 0; i < _states.size(); i++) {
		Element<std::string> state(_states[i]);
        stream << "signal " << DOMUtils::idForNode(state) << "_curr : std_logic;" << std::endl;
		stream << "signal " << DOMUtils::idForNode(state) << "_next : std_logic;" << std::endl;
	}
    for (size_t i = 0; i < _states.size(); i++) {
        Element<std::string> state(_states[i]);
        stream << "signal in_exit_set_" << ATTR(state, "documentOrder") << "_sig : std_logic;" << std::endl;
        stream << "signal in_complete_entry_set_up_" << ATTR(state, "documentOrder") << "_sig : std_logic;" << std::endl;
        stream << "signal in_complete_entry_set_" << ATTR(state, "documentOrder") << "_sig : std_logic;" << std::endl;
        stream << "signal state_active_" << ATTR(state, "documentOrder") << "_sig : std_logic;" << std::endl;
        stream << "signal default_completion_" << ATTR(state, "documentOrder") << "_sig : std_logic;" << std::endl;
    }

    stream << "-- transition signals" << std::endl;
    stream << "signal spontaneous_en : std_logic;" << std::endl;
    
    for (size_t i = 0; i < _transitions.size(); i++) {
        Element<std::string> transition(_transitions[i]);
        stream << "signal in_optimal_transition_set_" << ATTR(transition, "postFixOrder") << "_sig : std_logic;"
        << std::endl;
    }

	stream << std::endl;
	stream << "-- event signals" << std::endl;
	stream << "signal int_event_write_en : std_logic;" << std::endl;
	stream << "signal int_event_read_en : std_logic;" << std::endl;
	stream << "signal int_event_empty : std_logic;" << std::endl;
	stream << "signal int_event_input : event_type;" << std::endl;
	stream << "signal int_event_output : event_type;" << std::endl;
	stream << "signal next_event_re : std_logic;" << std::endl;
	stream << "signal next_event : event_type;" << std::endl;
	stream << "signal event_consumed : std_logic;" << std::endl;
	stream << std::endl;

    std::list<TrieNode*> eventNames = _eventTrie.getWordsWithPrefix("");
    for (std::list<TrieNode*>::iterator eventIter = eventNames.begin(); eventIter != eventNames.end(); eventIter++) {
        stream << "signal event_" << eventNameEscape((*eventIter)->value) << "_sig : std_logic;" << std::endl;
    }
    //    _eventTrie.dump();


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
	stream << "stall <= not en; " << std::endl;
	stream << std::endl;

	stream << "next_event_re <= not int_event_empty and not stall; " << std::endl;
	stream << "next_event <= int_event_output; " << std::endl;
	stream << "int_event_write_en <= next_event_en_i; " << std::endl;
	stream << "int_event_input <= next_event_i; " << std::endl;
	stream << "int_event_read_en <= not spontaneous_en and not stall; " << std::endl;
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

std::string ChartToVHDL::eventNameEscape(const std::string& eventName) {
	std::string escaped = escape(eventName);
	boost::replace_all(escaped, ".", "_");
	return escaped;
}

void ChartToVHDL::writeOptimalTransitionSetSelection(std::ostream & stream) {
	stream << "-- optimal transition set selection" << std::endl;
	for (size_t i = 0; i < _transitions.size(); i++) {
		Element<std::string> transition(_transitions[i]);
		std::string conflicts = ATTR(transition, "conflictBools");


        VContainer nameMatchers = VOR;
        if (HAS_ATTR(transition, "event")) {
            std::list<std::string> eventDescs = tokenize(ATTR(transition, "event"));
            for (std::list<std::string>::iterator descIter = eventDescs.begin(); descIter != eventDescs.end(); descIter++) {
                std::list<TrieNode*> eventNames = _eventTrie.getWordsWithPrefix((*descIter) == "*" ? "" : *descIter);
                for (std::list<TrieNode*>::iterator eventIter = eventNames.begin(); eventIter != eventNames.end(); eventIter++) {
                    *nameMatchers += VLINE("event_" + eventNameEscape((*eventIter)->value) + "_sig");
                }
            }
        } else {
            *nameMatchers += VLINE("'1'");
        }
        
        VContainer conflicters = VOR;
        for (size_t j = 0; j < i; j++) {
            if (conflicts[j] == '1') {
                *conflicters += VLINE("in_optimal_transition_set_" + toStr(j) + "_sig");
            }
        }
        
        VBranch* tree = (VASSIGN ,
                         VLINE("in_optimal_transition_set_" + ATTR(transition, "postFixOrder") + "_sig") ,
                         (VAND ,
                             (HAS_ATTR(transition, "event")
                              ? ( VNOT , VLINE("spontaneous_en") )
                              : ( VNOP , VLINE("spontaneous_en") ) ) ,
                          VLINE("state_active_" + ATTR(transition, "source") + "_sig"),
                          nameMatchers,
                         (VNOT , conflicters) ) );

        tree->print(stream);
        stream << ";" << std::endl;


#if 0
		stream << "in_optimal_transition_set_" << ATTR(transition, "postFixOrder") << "_sig "
		       << "<= " << (HAS_ATTR(transition, "event") ? "(not spontaneous_en)" : "spontaneous_en") << " and " << std::endl
		       << "  state_active_" << ATTR(transition, "source") << "_sig and not ( '0' " << std::endl;
		for (size_t j = 0; j < i; j++) {
			if (conflicts[j] == '1') {
				stream << "    or in_optimal_transition_set_" << toStr(j) << "_sig" << std::endl;
			}
		}
		stream << "  )";
		if (HAS_ATTR(transition, "event")) {
			stream << " and ( '0' " << std::endl;;

			// find all matching event literals
			std::list<std::string> eventDescs = tokenize(ATTR(transition, "event"));
			for (std::list<std::string>::iterator descIter = eventDescs.begin(); descIter != eventDescs.end(); descIter++) {
				std::list<TrieNode*> eventNames = _eventTrie.getWordsWithPrefix((*descIter) == "*" ? "" : *descIter);
				for (std::list<TrieNode*>::iterator eventIter = eventNames.begin(); eventIter != eventNames.end(); eventIter++) {
					stream << "    or event_" << eventNameEscape((*eventIter)->value) << "_sig" << std::endl;
				}
			}
			stream << "  )";

		}
		stream << ";" << std::endl;
#endif
	}
}

void ChartToVHDL::writeExitSet(std::ostream & stream) {
	stream << "-- exit set selection" << std::endl;

	for (size_t i = 0; i < _states.size(); i++) {
		Element<std::string> state(_states[i]);
		std::string completion = ATTR(state, "completionBools");
		std::string ancestors = ATTR(state, "ancBools");
		std::string children = ATTR(state, "childBools");
		std::string parent = ATTR(state, "parent");

        VContainer exitsetters = VOR;
        for (size_t j = 0; j < _transitions.size(); j++) {
            Element<std::string> transition(_transitions[j]);
            std::string exitSet = ATTR(transition, "exitSetBools");
            if (exitSet[i] == '1') {
                *exitsetters += VLINE("in_optimal_transition_set_" + toStr(j) + "_sig ");
            }
        }
        
        VBranch* tree = (VASSIGN ,
                         VLINE("in_exit_set_" + toStr(i) + "_sig"),
                         (VAND,
                          VLINE("state_active_" + toStr(i) + "_sig"),
                          exitsetters ));

        tree->print(stream);
        stream << ";" << std::endl;

#if 0
		stream << "in_exit_set_" << toStr(i) << "_sig "
		       << "<= state_active_" << toStr(i) << "_sig and ('0'" << std::endl;
		for (size_t j = 0; j < _transitions.size(); j++) {
			Element<std::string> transition(_transitions[j]);
			std::string exitSet = ATTR(transition, "exitSetBools");
			if (exitSet[i] == '1') {
				stream << "  or in_optimal_transition_set_" << toStr(j) << "_sig " << std::endl;
			}
		}

		stream << ")";
		stream << ";" << std::endl;
#endif
	}
}

void ChartToVHDL::writeEntrySet(std::ostream & stream) {
	stream << "-- entry set selection" << std::endl;

	for (size_t i = 0; i < _states.size(); i++) {
		Element<std::string> state(_states[i]);
		std::string completion = ATTR(state, "completionBools");
		std::string ancestors = ATTR(state, "ancBools");
		std::string children = ATTR(state, "childBools");
		std::string parent = ATTR(state, "parent");

        VContainer optimalEntrysetters = VOR;
        for (size_t j = 0; j < _transitions.size(); j++) {
            Element<std::string> transition(_transitions[j]);
            std::string targetSet = ATTR(transition, "targetBools");
            if (targetSet[i] == '1') {
                *optimalEntrysetters += VLINE("in_optimal_transition_set_" + toStr(j) + "_sig");
            }
        }

        VContainer completeEntrysetters = VOR;
        if (isCompound(state)) {
            for (size_t j = 0; j < _states.size(); j++) {
                if (children[j] != '1')
                    continue;
                *completeEntrysetters += VLINE("in_complete_entry_set_up_" + toStr(j) + "_sig");
            }
        }
        
        VBranch* tree = (VASSIGN ,
                         VLINE("in_complete_entry_set_up_" + toStr(i) + "_sig"),
                         optimalEntrysetters,
                         completeEntrysetters);

        tree->print(stream);
        stream << ";" << std::endl;

#if 0
		stream << "in_complete_entry_set_up_" << toStr(i) << "_sig <= ('0'" << std::endl;

		for (size_t j = 0; j < _transitions.size(); j++) {
			Element<std::string> transition(_transitions[j]);
//            std::cout << transition;
			std::string targetSet = ATTR(transition, "targetBools");
			if (targetSet[i] == '1') {
				stream << "  or in_optimal_transition_set_" << toStr(j) << std::endl;
			}
		}
		if (isCompound(state)) {
			for (size_t j = 0; j < _states.size(); j++) {
				if (children[j] != '1')
					continue;

				stream << "  or in_complete_entry_set_up_" << toStr(j) << "_sig" << std::endl;
			}

		}
		stream << ");" << std::endl;
#endif
	}

	for (size_t i = 0; i < _states.size(); i++) {
		Element<std::string> state(_states[i]);
		std::string completion = ATTR(state, "completionBools");
		std::string ancestors = ATTR(state, "ancBools");
		std::string children = ATTR(state, "childBools");
		std::string parent = ATTR(state, "parent");

		if (parent.size() == 0) {
			continue; // TODO: FixMe <scxml>
		}

        VContainer tmp1 = VAND;
        if (isCompound(Element<std::string>(_states[strTo<size_t>(parent)]))) {
            *tmp1 += VLINE("default_completion_" + toStr(parent) + "_sig");

            for (size_t j = 0; j < _states.size(); j++) {
                if (children[j] != '1')
                    continue;
                *tmp1 += ( VAND,
                          ( VNOT,
                           ( VAND,
                            VLINE("is_active" + toStr(j) + "_sig"),
                            ( VNOT,
                             VLINE("in_exit_set_" + toStr(j) + "_sig") ) ) ) );
                
            }

        }
        
        if (isParallel(Element<std::string>(_states[strTo<size_t>(parent)]))) {
            *tmp1 += VLINE("in_complete_entry_set_" + toStr(parent) + "_sig");
        }
        
        VBranch* tree = (VASSIGN ,
                         VLINE("in_complete_entry_set_" + toStr(i) + "_sig"), tmp1);

        tree->print(stream);
        stream << ";" << std::endl;

#if 0
		stream << "in_complete_entry_set_" << toStr(i) << "_sig <= (in_complete_entry_set_up_" << toStr(i) << "_sig or (" << std::endl;

		if (isParallel(Element<std::string>(_states[strTo<size_t>(parent)]))) {
			stream << "  in_complete_entry_set_" << toStr(parent) << "_sig" << std::endl;
		} else if (isCompound(Element<std::string>(_states[strTo<size_t>(parent)]))) {
			stream << "  default_completion_" << toStr(parent) << "_sig" << std::endl;

			for (size_t j = 0; j < _states.size(); j++) {
				if (children[j] != '1')
					continue;
				stream << "  and not (is_active" << toStr(j) << "_sig and not in_exit_set_" << toStr(j) << "_sig)" << std::endl;

			}
		}

		stream << ");" << std::endl;
#endif
	}
}

//TODO write event generator
// wie die letzten beiden states erkennen
// process bauen der bei fail 0 ausgibt und bei accept 1

void ChartToVHDL::writeNextStateLogic(std::ostream & stream) {
	stream << "-- state logic" << std::endl;
	stream << "-- only gets active when state changes (microstep?) " << std::endl;
	stream << "state_decode_proc: process(current_state)" << std::endl;
	stream << "begin" << std::endl;

	std::stringstream nextStateBuffer;
	for (size_t i = 0; i < _states.size(); i++) {
		Element<std::string> state(_states[i]);

		// calculate event choices
		// _transitions is sorted in Postfix order
		// by stating with smalest index the most important
		// will be written first
		std::vector< Element<std::string> > choices;
		std::string spntaneous_trans_sig = "";
		for (size_t j = 0; j < _transitions.size(); j++) {
			Element<std::string> transition(_transitions[j]);
			if (ATTR_CAST(transition.getParentNode(), "id") == ATTR(state, "id")) {
				choices.push_back(transition);
				if (ATTR(transition, "event") == CONST_TRANS_SPONTANIOUS) {
					spntaneous_trans_sig = ATTR(transition, "id");
					// FIXME hofully there are just single spntaneous transitions allowed
					// else we have to handle this
				}
			}
		}

		// calculate incomming transitions (for later use)
		std::vector< Element<std::string> > incommingTransitions;
		for (size_t j = 0; j < _transitions.size(); j++) {
			Element<std::string> transition(_transitions[j]);
			if (ATTR_CAST(transition, "target") == ATTR(state, "id")) {
				incommingTransitions.push_back(transition);
			}
		}

		if (choices.size() > 0) {// if no outgoing transitions (maybe final state :D) we don't write anything

			stream << "  if ( " << ATTR(state, "id") << " = '1' ) then" << std::endl;
			stream << "    if ( transition_spntaneous_en = '1' ) then" << std::endl;
			// enable spntaneous transition (if any) and disable all other
			for (size_t j = 0; j < choices.size(); j++) {
				Element<std::string> transition(choices[j]);
				if (ATTR(transition, "id") == spntaneous_trans_sig) {
					stream << "      " << ATTR(transition, "id") << "_sig <= '1';" << std::endl;
				} else {
					stream << "      " << ATTR(transition, "id") << "_sig <= '0';" << std::endl;
				}
			}

			stream << "    elsif ( next_event_re = '1' ) then" << std::endl;
			// if no spntaneous transition enables, look at events
			// since there is just one event at a time, we use case statement
			// to check transitions matching in postfix order
			// FIXME hopefully there is just one transition per state and event at a time
			stream << "    case next_event is" << std::endl;
			bool hasWildcardTransition = false;
			for (size_t j = 0; j < choices.size(); j++) {
				Element<std::string> transition(choices[j]);
				std::string eventName = ATTR(transition, "event");
				if (eventName == CONST_EVENT_ANY) {
					eventName = "others";
					hasWildcardTransition = true;
				}
				stream << "      when " << eventName << " =>" << std::endl;
				// activate transition and deactivete others
				for (size_t k = 0; k < choices.size(); k++) {
					Element<std::string> tmp_t(choices[k]);
					if (ATTR(tmp_t, "event") == ATTR(transition, "event")) {
						stream << "        " << ATTR(tmp_t, "id") << "_sig <= '1';" << std::endl;
					} else {
						stream << "        " << ATTR(tmp_t, "id") << "_sig <= '0';" << std::endl;
					}
				}
			}
			if (!hasWildcardTransition) {
				// if there is no others we create one for deactivating everything
				stream << "      when others =>" << std::endl;
				for (size_t j = 0; j < choices.size(); j++) {
					Element<std::string> tmp_t(choices[j]);
					stream << "        " << ATTR(tmp_t, "id") << "_sig <= '0';" << std::endl;
				}
			}
			stream << "    end case;" << std::endl;
			//TODO umkehren oder other abfangen
			//stream << "    when others =>" << std::endl;
			//stream << "     next_state <= current_state;" << std::endl;

			stream << "    else" << std::endl;
			// no enabled event ? disable all transitions (looks like we have to wait)
			for (size_t j = 0; j < choices.size(); j++) {
				Element<std::string> transition(choices[j]);
				stream << "      " << ATTR(transition, "id") << "_sig <= '0';" << std::endl;
			}
			stream << "    end if;" << std::endl;
			stream << "  end if;" << std::endl;
			stream << std::endl;
		}
		// write next state calculation in buffer for later use
		nextStateBuffer << ATTR(state, "id") << "_next <= ( ( '0'";
		std::string seperator = "  or  ";
		for (size_t j = 0; j < incommingTransitions.size(); j++) {
			nextStateBuffer << seperator
			                << ATTR(incommingTransitions[j], "id") << "_sig";
		}
		nextStateBuffer << " ) or ";
		nextStateBuffer << "( ( not ( '0'";
		seperator = "  or  ";
		for (size_t j = 0; j < choices.size(); j++) {
			nextStateBuffer << seperator
			                << ATTR(choices[j], "id") << "_sig";
		}
		nextStateBuffer << " ) ) and " << ATTR(state, "id")
		                << "_curr ));" << std::endl;
	}
	stream << "end process;" << std::endl;
	stream << std::endl;
	// write outgoing transition buffer
	stream << nextStateBuffer.str() << std::endl;

	// updater for current state
	stream << "-- update current state" << std::endl;
	stream << "state_proc: process(clk, rst, stall)" << std::endl;
	stream << "begin" << std::endl;
	stream << "    if rst = '1' then" << std::endl;
	stream << "        current_state <= (others => '0');" << std::endl;
//	stream << "        " << _initState << "_curr <= '1';" << std::endl;
	stream << "    elsif (rising_edge(clk) and stall = '0') then" << std::endl;
	stream << "        current_state <= next_state;" << std::endl;
	stream << "    end if;" << std::endl;
	stream << "end process;" << std::endl;
	stream << std::endl;
}

void ChartToVHDL::writeOutputLogic(std::ostream & stream) {
	stream << "-- output logic" << std::endl;
	stream << "output_proc: process(current_state)" << std::endl;
	stream << "begin" << std::endl;
	stream << "    case current_state is" << std::endl;

	for (size_t i = 0; i < _states.size(); i++) {
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