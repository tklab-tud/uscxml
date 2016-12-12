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
#include "uscxml/util/UUID.h"
#include "uscxml/util/String.h"
#include "uscxml/util/Predicates.h"

#include <math.h>
#include <boost/algorithm/string.hpp>
#include "uscxml/interpreter/Logging.h"

#include <iostream>
#include <algorithm>
#include <iomanip>

#include <sstream>

namespace uscxml {

using namespace XERCESC_NS;

Transformer ChartToVHDL::transform(const Interpreter &other) {
	ChartToVHDL *c2c = new ChartToVHDL(other);

	return std::shared_ptr<TransformerImpl>(c2c);
}

ChartToVHDL::ChartToVHDL(const Interpreter &other) : ChartToC(other), _eventTrie(".") {
}

ChartToVHDL::~ChartToVHDL() {
}

void ChartToVHDL::findEvents() {
	// elements with an event attribute
	std::list<DOMElement *> withEvents = DOMUtils::inDocumentOrder({
		XML_PREFIX(_scxml).str() + "raise",
		XML_PREFIX(_scxml).str() + "send",
		XML_PREFIX(_scxml).str() + "transition",
	}, _scxml);

	for (auto withEvent : withEvents) {
//            if (HAS_ATTR_CAST(withEvent, "event")) {
//                if (ATTR_CAST(withEvent, "event") != "*")
//                    _eventTrie.addWord(ATTR_CAST(withEvent, "event"));
//            }
		// Tokenized version below

		if (HAS_ATTR_CAST(withEvent, "event")) {
			std::string eventNames = ATTR_CAST(withEvent, "event");
			std::list<std::string> events = tokenize(eventNames);
			for (std::list<std::string>::iterator eventIter = events.begin();
			        eventIter != events.end(); eventIter++) {
				std::string eventName = *eventIter;
				if (boost::ends_with(eventName, "*"))
					eventName = eventName.substr(0, eventName.size() - 1);
				if (boost::ends_with(eventName, "."))
					eventName = eventName.substr(0, eventName.size() - 1);
				if (eventName.size() > 0)
					_eventTrie.addWord(eventName);
			}

			//TODO implement "done" event
			// --> enter a final from a compound state not <scxml> (also prevent setting completed_o)
			// --> all final children from a parallel are entered
			//TODO implement error events --> set by output logic to a signal line
		}

	}

	// preprocess event names since they are often used
	_eventNames = _eventTrie.getWordsWithPrefix("");
	// Calculate needed bit size for the event fifo
	// --> |log2(n)| +1 with n is number of events
	// we do not add +1 because the std_logic_vector startes with 0
	_eventBitSize = ceil(std::abs(log2(_eventNames.size())));

	_execContent = DOMUtils::inDocumentOrder({
		XML_PREFIX(_scxml).str() + "raise",
		XML_PREFIX(_scxml).str() + "send"
	}, _scxml);

}

bool ChartToVHDL::isSupportedExecContent(DOMElement *execContentElement) {
	return (TAGNAME(execContentElement) == XML_PREFIX(_scxml).str() + "raise" ||
	        TAGNAME(execContentElement) == XML_PREFIX(_scxml).str() + "send");
}

void ChartToVHDL::writeTo(std::ostream &stream) {
	findEvents();


	stream << "-- generated from " << std::string(_baseURL) << std::endl;
	stream << "-- run as " << std::endl;
	stream << "--   ghdl --clean && ghdl -a foo.vhdl && ghdl -e tb && ./tb --stop-time=10ms --vcd=tb.vcd" <<
	       std::endl;
	stream << "--   gtkwave tb.vcd" << std::endl;
	stream << std::endl;

	writeFiFo(stream);
	writeEventController(stream);
	writeMicroStepper(stream);
	writeConditionSolver(stream);
	writeTestbench(stream);
	//writeTopLevel(stream);
}


void ChartToVHDL::writeIncludes(std::ostream &stream) {
	// Add controler specific stuff here
	stream << "library IEEE;" << std::endl;
	stream << "use IEEE.std_logic_1164.all;" << std::endl;
//		stream << "use work.machine" << _md5 << ".all;" << std::endl;
	stream << std::endl;
}

void ChartToVHDL::writeTestbench(std::ostream &stream) {

	stream << "-- TESTBENCH" << std::endl;
	writeIncludes(stream);
	stream << "use std.env.all;" << std::endl;
	stream << std::endl;

	stream << "-- empty entity" << std::endl;
	stream << "entity tb is" << std::endl;
	stream << "end entity tb;" << std::endl;
	stream << std::endl;

	stream << "architecture behavioral of tb is" << std::endl;
	stream << std::endl;

	// modules
	//COMPONENT MS
	stream << "  -- Module declaration" << std::endl;
	stream << "  component micro_stepper is" << std::endl;
	stream << "    port (" << std::endl;
	stream << "    --inputs" << std::endl;
	stream << "    clk  :in    std_logic;" << std::endl;
	stream << "    rst_i  :in    std_logic;" << std::endl;
	stream << "    en   :in    std_logic;" << std::endl;
	stream << "    next_event_i    :in  std_logic_vector( " << _eventBitSize << " downto 0);" << std::endl;
	stream << "    next_event_we_i :in  std_logic;" << std::endl;

	for (auto transition : _transitions) {
		if (HAS_ATTR(transition, "cond")) { // create enable line if transition has conditions
			stream << "    transition_condition_fulfilled_" << ATTR(transition, "postFixOrder") <<
			       "_i : std_logic;"
			       << std::endl;
		}
	}

	stream << "    --outputs" << std::endl;
	stream << "    error_o     :out std_logic;" << std::endl;

	for (auto state : _states) {
		stream << "    state_active_" << ATTR(state, "documentOrder") << "_o :out std_logic;" << std::endl;

		if (DOMUtils::filterChildElements(XML_PREFIX(_scxml).str() + "onentry", state).size() > 0) {
			stream << "    entry_set_" << ATTR(state, "documentOrder") << "_o :out std_logic;" << std::endl;
		}

		if (DOMUtils::filterChildElements(XML_PREFIX(_scxml).str() + "onexit", state).size() > 0) {
			stream << "    exit_set_" << ATTR(state, "documentOrder") << "_o :out std_logic;" << std::endl;
		}
	}

	for (auto transition : _transitions) {
		if (DOMUtils::filterChildType(DOMNode::ELEMENT_NODE, transition).size() > 0) {
			stream << "    transition_set_" << ATTR(transition, "postFixOrder") << "_o :out std_logic;"
			       << std::endl;
		}
	}

	stream << "    completed_o :out std_logic" << std::endl;
	stream << "    );" << std::endl;
	stream << "  end component;" << std::endl;
	stream << std::endl;

	// COMPONENT EC
	stream << "  component event_controller is" << std::endl;
	stream << "  port(" << std::endl;
	stream << "    --inputs" << std::endl;
	stream << "    clk  :in    std_logic;" << std::endl;
	stream << "    rst_i  :in    std_logic;" << std::endl;

	for (auto state : _states) {
		stream << "    state_active_" << ATTR(state, "documentOrder")
		       << "_i :in std_logic;" << std::endl;

		if (DOMUtils::filterChildElements(XML_PREFIX(_scxml).str() + "onentry", state).size() > 0) {
			stream << "    entry_set_" << ATTR(state, "documentOrder")
			       << "_i :in std_logic;" << std::endl;
		}

		if (DOMUtils::filterChildElements(XML_PREFIX(_scxml).str() + "onexit", state).size() > 0) {
			stream << "    exit_set_" << ATTR(state, "documentOrder")
			       << "_i :in std_logic;" << std::endl;
		}
	}

	for (auto transition : _transitions) {
		if (DOMUtils::filterChildType(DOMNode::ELEMENT_NODE, transition).size() > 0) {
			stream << "    transition_set_" << ATTR(transition, "postFixOrder")
			       << "_i :in std_logic;" << std::endl;
		}
	}
	stream << "    --outputs" << std::endl;
	stream << "    micro_stepper_en_o :out  std_logic;" << std::endl;
	stream << "    event_o    :out  std_logic_vector( " << _eventBitSize << " downto 0);" << std::endl;
	stream << "    event_we_o :out  std_logic" << std::endl;
	//        stream << "    done_o :out std_logic" << std::endl;
	stream << ");" << std::endl;
	stream << "end component; " << std::endl;
	stream << std::endl;

	//COMPONENT CS
	stream << "component condition_solver is" << std::endl;
	stream << "port(" << std::endl;
	stream << "    --inputs" << std::endl;
	stream << "    clk  :in    std_logic;" << std::endl;
	stream << "    rst_i  :in    std_logic;" << std::endl;

	for (auto state : _states) {
		stream << "    state_active_" << ATTR(state, "documentOrder")
		       << "_i :in std_logic;" << std::endl;
	}

	stream << "    --outputs" << std::endl;

	for (auto transition : _transitions) {
		if (HAS_ATTR(transition, "cond")) {
			stream << "    transition_condition_fulfilled_" << ATTR(transition, "postFixOrder")
			       << "_o :out std_logic;" << std::endl;
		}
	}

	stream << "    micro_stepper_en_o :out  std_logic" << std::endl;
	stream << ");" << std::endl;
	stream << "end component; " << std::endl;

	// signals
	stream << "  -- input" << std::endl;
	stream << "  signal clk   : std_logic := '0';" << std::endl;
	stream << "  signal reset : std_logic;" << std::endl;
	stream << "  signal dut_enable : std_logic;" << std::endl;
	stream << "  signal ec_enable_out : std_logic;" << std::endl;
	stream << "  signal cs_enable_out : std_logic;" << std::endl;
	stream << "  signal next_event_we_i : std_logic;" << std::endl;
	stream << "  signal next_event_i : std_logic_vector( " << _eventBitSize << " downto 0);" << std::endl;
	stream << std::endl;

	stream << "  -- output" << std::endl;
	stream << "  signal error_o, completed_o : std_logic;" << std::endl;
	stream << std::endl;

	stream << "  -- wiring" << std::endl;
	for (auto state : _states) {
		stream << "  signal state_active_" << ATTR(state, "documentOrder")
		       << "_sig : std_logic;" << std::endl;

		if (DOMUtils::filterChildElements(XML_PREFIX(_scxml).str() + "onentry", state).size() > 0) {
			stream << "  signal entry_set_" << ATTR(state, "documentOrder")
			       << "_sig : std_logic;" << std::endl;
		}

		if (DOMUtils::filterChildElements(XML_PREFIX(_scxml).str() + "onexit", state).size() > 0) {
			stream << "  signal exit_set_" << ATTR(state, "documentOrder")
			       << "_sig : std_logic;" << std::endl;
		}
	}

	for (auto transition : _transitions) {
		if (DOMUtils::filterChildType(DOMNode::ELEMENT_NODE, transition).size() > 0) {
			stream << "  signal transition_set_" << ATTR(transition, "postFixOrder")
			       << "_sig : std_logic;" << std::endl;
		}
	}

	for (auto transition : _transitions) {
		if (HAS_ATTR(transition, "cond")) { // create enable line if transition has conditions
			stream << "  signal transition_condition_fulfilled_" << ATTR(transition, "postFixOrder") <<
			       "_sig : std_logic;"
			       << std::endl;
		}
	}
	stream << std::endl;

	// wiring
	stream << "begin" << std::endl;
	stream << "  clk   <= not clk  after 20 ns;  -- 25 MHz clock frequency" << std::endl;
	stream << "  reset <= '1', '0' after 100 ns; -- generates reset signal: --__" << std::endl;
	stream << "  dut_enable <= ec_enable_out and cs_enable_out; -- enable signal for microstepper" <<
	       std::endl;
	stream << std::endl;

	stream << "  -- Module instantiation" << std::endl;
	stream << "  dut : micro_stepper" << std::endl;
	stream << "    port map (" << std::endl;
	stream << "      clk       => clk," << std::endl;
	stream << "      rst_i     => reset," << std::endl;
	stream << "      en     => dut_enable," << std::endl;
	stream << std::endl;

	stream << "      next_event_i     => next_event_i," << std::endl;
	stream << "      next_event_we_i => next_event_we_i," << std::endl;
	stream << "      error_o  => error_o," << std::endl;

	for (auto state : _states) {
		stream << "      state_active_" << ATTR(state, "documentOrder")
		       << "_o => state_active_" << ATTR(state, "documentOrder")
		       << "_sig," << std::endl;

		if (DOMUtils::filterChildElements(XML_PREFIX(_scxml).str() + "onentry", state).size() > 0) {
			stream << "      entry_set_" << ATTR(state, "documentOrder")
			       << "_o => entry_set_" << ATTR(state, "documentOrder")
			       << "_sig," << std::endl;
		}

		if (DOMUtils::filterChildElements(XML_PREFIX(_scxml).str() + "onexit", state).size() > 0) {
			stream << "      exit_set_" << ATTR(state, "documentOrder")
			       << "_o => exit_set_" << ATTR(state, "documentOrder")
			       << "_sig," << std::endl;
		}
	}

	for (auto transition : _transitions) {
		if (DOMUtils::filterChildType(DOMNode::ELEMENT_NODE, transition).size() > 0) {
			stream << "      transition_set_" << ATTR(transition, "postFixOrder")
			       << "_o => transition_set_" << ATTR(transition, "postFixOrder")
			       << "_sig," << std::endl;
		}
	}

	for (auto transition : _transitions) {
		if (HAS_ATTR(transition, "cond")) { // create enable line if transition has conditions
			stream << "      transition_condition_fulfilled_" << ATTR(transition, "postFixOrder") <<
			       "_i => transition_condition_fulfilled_" << ATTR(transition, "postFixOrder") <<
			       "_sig," << std::endl;
		}
	}

	stream << "      completed_o  => completed_o" << std::endl;
	stream << "      );" << std::endl;
	stream << std::endl;

	stream << "  ec : event_controller" << std::endl;
	stream << "    port map (" << std::endl;
	stream << "      clk       => clk," << std::endl;
	stream << "      rst_i     => reset," << std::endl;
	stream << std::endl;

	stream << "      event_o     => next_event_i," << std::endl;
	stream << "      event_we_o => next_event_we_i," << std::endl;

	for (auto state : _states) {
		stream << "      state_active_" << ATTR(state, "documentOrder")
		       << "_i => state_active_" << ATTR(state, "documentOrder")
		       << "_sig," << std::endl;

		if (DOMUtils::filterChildElements(XML_PREFIX(_scxml).str() + "onentry", state).size() > 0) {
			stream << "      entry_set_" << ATTR(state, "documentOrder")
			       << "_i => entry_set_" << ATTR(state, "documentOrder")
			       << "_sig," << std::endl;
		}

		if (DOMUtils::filterChildElements(XML_PREFIX(_scxml).str() + "onexit", state).size() > 0) {
			stream << "      exit_set_" << ATTR(state, "documentOrder")
			       << "_i => exit_set_" << ATTR(state, "documentOrder")
			       << "_sig," << std::endl;
		}
	}

	for (auto transition : _transitions) {
		if (DOMUtils::filterChildType(DOMNode::ELEMENT_NODE, transition).size() > 0) {
			stream << "      transition_set_" << ATTR(transition, "postFixOrder")
			       << "_i => transition_set_" << ATTR(transition, "postFixOrder")
			       << "_sig," << std::endl;
		}
	}

	stream << "      micro_stepper_en_o  => ec_enable_out" << std::endl;
	//        stream << "      done_o  => open" << std::endl;
	stream << "      );" << std::endl;
	stream << std::endl;

	stream << "  cs : condition_solver" << std::endl;
	stream << "    port map(" << std::endl;
	stream << "      --inputs" << std::endl;
	stream << "      clk  => clk," << std::endl;
	stream << "      rst_i  => reset," << std::endl;

	for (auto state : _states) {
		stream << "      state_active_" << ATTR(state, "documentOrder")
		       << "_i => state_active_" << ATTR(state, "documentOrder")
		       << "_sig," << std::endl;
	}

	stream << "      --outputs" << std::endl;

	for (auto transition : _transitions) {
		if (HAS_ATTR(transition, "cond")) {
			stream << "      transition_condition_fulfilled_" << ATTR(transition, "postFixOrder")
			       << "_o => transition_condition_fulfilled_" << ATTR(transition, "postFixOrder") <<
			       "_sig," << std::endl;
		}
	}

	stream << "      micro_stepper_en_o => cs_enable_out" << std::endl;
	stream << "      );" << std::endl;
	stream << std::endl;

	// find pass state
	std::list<DOMElement *> topLevelFinal =
	    DOMUtils::filterChildElements(XML_PREFIX(_scxml).str() + "final", _scxml);

	std::string passStateNo = "";
	for (auto final : topLevelFinal) {
		if (ATTR(final, "id") == "pass") {
			passStateNo = ATTR(final, "documentOrder");
		}
	}

	// test observation and exit condition
	stream << "  -- Test observation" << std::endl;
	stream << "  process (clk)" << std::endl;
	stream << "  variable count_clk : integer := 0;" << std::endl;
	stream << "  begin" << std::endl;
	stream << "  if rising_edge(clk) then" << std::endl;
	stream << "    count_clk := count_clk + 1;" << std::endl;
	stream << "    if (completed_o = '1') then" << std::endl;
	if (!passStateNo.empty()) {
		stream << "      assert (state_active_" << passStateNo;
		stream << "_sig = '1') report \"Completed with errors\" severity error;" << std::endl;
	}
	stream << "      -- stop simulation" << std::endl;
	stream << "      finish(0);" << std::endl; // use 0 for ctest
//        -- For both STOP and FINISH the STATUS values are those used
//        -- in the Verilog $finish task
//        -- 0 prints nothing
//        -- 1 prints simulation time and location
//        -- 2 prints simulation time, location, and statistics about
//        --   the memory and CPU times used in simulation
	//stream << "      assert false report \"Simulation Finished\" severity failure;" << std::endl;
	stream << "    else" << std::endl;
	stream << "      -- state machine not completed" << std::endl;
	stream << "      -- check if it is time to stop waiting (100 clk per state+transition+excontent)" << std::endl;
	int tolleratedClocks = (_transitions.size() + _states.size() + _execContent.size()) * 100;
	stream << "      assert (count_clk < " << tolleratedClocks;
	stream << ") report \"Clock count exceed\" severity failure;" << std::endl;
	stream << "    end if;" << std::endl;
	stream << "  end if;" << std::endl;
	stream << "  end process;" << std::endl;

	stream << "end architecture;" << std::endl;
	stream << "-- END TESTBENCH" << std::endl;

}

void ChartToVHDL::writeTopLevel(std::ostream &stream) {
	stream << "-- TOP LEVEL entity for easy synthesis" << std::endl;
	writeIncludes(stream);
	stream << std::endl;

	stream << "-- empty entity" << std::endl;
	stream << "entity top_level_design is" << std::endl;
	stream << "port (" << std::endl;
	stream << "    --inputs" << std::endl;
	stream << "    clk  :in    std_logic;" << std::endl;
	stream << "    rst  :in    std_logic;" << std::endl;
	stream << "    --outputs" << std::endl;
	for (auto state : _states) {
		stream << "    state_active_" << ATTR(state, "documentOrder")
		       << "_o :out std_logic;" << std::endl;
	}
	stream << "    completed_o :out std_logic" << std::endl;
	stream << ");" << std::endl;
	stream << "end entity top_level_design;" << std::endl;
	stream << std::endl;

	stream << "architecture behavioral of top_level_design is" << std::endl;
	stream << std::endl;

	// modules
	stream << "  -- Module declaration" << std::endl;
	stream << "  component micro_stepper is" << std::endl;
	stream << "    port (" << std::endl;
	stream << "    --inputs" << std::endl;
	stream << "    clk  :in    std_logic;" << std::endl;
	stream << "    rst_i  :in    std_logic;" << std::endl;
	stream << "    en   :in    std_logic;" << std::endl;
	stream << "    next_event_i    :in  std_logic_vector( " << _eventBitSize << " downto 0);" << std::endl;
	stream << "    next_event_we_i :in  std_logic;" << std::endl;
	stream << "    --outputs" << std::endl;
	stream << "    error_o     :out std_logic;" << std::endl;

	for (auto state : _states) {
		stream << "    state_active_" << ATTR(state, "documentOrder") << "_o :out std_logic;" << std::endl;

		if (DOMUtils::filterChildElements(XML_PREFIX(_scxml).str() + "onentry", state).size() > 0) {
			stream << "    entry_set_" << ATTR(state, "documentOrder") << "_o :out std_logic;" << std::endl;
		}

		if (DOMUtils::filterChildElements(XML_PREFIX(_scxml).str() + "onexit", state).size() > 0) {
			stream << "    exit_set_" << ATTR(state, "documentOrder") << "_o :out std_logic;" << std::endl;
		}
	}

	for (auto transition : _transitions) {
		if (DOMUtils::filterChildType(DOMNode::ELEMENT_NODE, transition).size() > 0) {
			stream << "    transition_set_" << ATTR(transition, "postFixOrder") << "_o :out std_logic;"
			       << std::endl;
		}
	}

	stream << "    completed_o :out std_logic" << std::endl;
	stream << "    );" << std::endl;
	stream << "  end component;" << std::endl;
	stream << std::endl;

	stream << "  component event_controller is" << std::endl;
	stream << "  port(" << std::endl;
	stream << "    --inputs" << std::endl;
	stream << "    clk  :in    std_logic;" << std::endl;
	stream << "    rst_i  :in    std_logic;" << std::endl;

	for (auto state : _states) {
		stream << "    state_active_" << ATTR(state, "documentOrder")
		       << "_i :in std_logic;" << std::endl;

		if (DOMUtils::filterChildElements(XML_PREFIX(_scxml).str() + "onentry", state).size() > 0) {
			stream << "    entry_set_" << ATTR(state, "documentOrder")
			       << "_i :in std_logic;" << std::endl;
		}

		if (DOMUtils::filterChildElements(XML_PREFIX(_scxml).str() + "onexit", state).size() > 0) {
			stream << "    exit_set_" << ATTR(state, "documentOrder")
			       << "_i :in std_logic;" << std::endl;
		}
	}

	for (auto transition : _transitions) {
		if (DOMUtils::filterChildType(DOMNode::ELEMENT_NODE, transition).size() > 0) {
			stream << "    transition_set_" << ATTR(transition, "postFixOrder")
			       << "_i :in std_logic;" << std::endl;
		}
	}
	stream << "    --outputs" << std::endl;
	stream << "    micro_stepper_en_o :out  std_logic;" << std::endl;
	stream << "    event_o    :out  std_logic_vector( " << _eventBitSize << " downto 0);" << std::endl;
	stream << "    event_we_o :out  std_logic" << std::endl;
	//        stream << "    done_o :out std_logic" << std::endl;
	stream << ");" << std::endl;
	stream << "end component; " << std::endl;

	// signals
	stream << "  -- input" << std::endl;
	stream << "  signal reset : std_logic;" << std::endl;
	stream << "  signal dut_enable : std_logic;" << std::endl;
	stream << "  signal next_event_we_i : std_logic;" << std::endl;
	stream << "  signal next_event_i : std_logic_vector( " << _eventBitSize << " downto 0);" << std::endl;
	stream << std::endl;

	stream << "  -- output" << std::endl;
	stream << "  signal error_o : std_logic;" << std::endl;
	stream << std::endl;

	stream << "  -- wiring" << std::endl;
	for (auto state : _states) {
		stream << "  signal state_active_" << ATTR(state, "documentOrder")
		       << "_sig : std_logic;" << std::endl;

		if (DOMUtils::filterChildElements(XML_PREFIX(_scxml).str() + "onentry", state).size() > 0) {
			stream << "  signal entry_set_" << ATTR(state, "documentOrder")
			       << "_sig : std_logic;" << std::endl;
		}

		if (DOMUtils::filterChildElements(XML_PREFIX(_scxml).str() + "onexit", state).size() > 0) {
			stream << "  signal exit_set_" << ATTR(state, "documentOrder")
			       << "_sig : std_logic;" << std::endl;
		}
	}

	for (auto transition : _transitions) {
		if (DOMUtils::filterChildType(DOMNode::ELEMENT_NODE, transition).size() > 0) {
			stream << "  signal transition_set_" << ATTR(transition, "postFixOrder")
			       << "_sig : std_logic;" << std::endl;
		}
	}

	// wiring
	stream << "begin" << std::endl;
	stream << "  reset <= rst;" << std::endl;
	stream << std::endl;

	for (auto state : _states) {
		stream << "state_active_" << ATTR(state, "documentOrder")
		       << "_o <= state_active_" << ATTR(state, "documentOrder")
		       << "_sig;" << std::endl;
	}
	stream << std::endl;

	stream << "  -- Module instantiation" << std::endl;
	stream << "  dut : micro_stepper" << std::endl;
	stream << "    port map (" << std::endl;
	stream << "      clk       => clk," << std::endl;
	stream << "      rst_i     => reset," << std::endl;
	stream << "      en     => dut_enable," << std::endl;
	stream << std::endl;

	stream << "      next_event_i     => next_event_i," << std::endl;
	stream << "      next_event_we_i => next_event_we_i," << std::endl;
	stream << "      error_o  => error_o," << std::endl;

	for (auto state : _states) {
		stream << "      state_active_" << ATTR(state, "documentOrder")
		       << "_o => state_active_" << ATTR(state, "documentOrder")
		       << "_sig," << std::endl;

		if (DOMUtils::filterChildElements(XML_PREFIX(_scxml).str() + "onentry", state).size() > 0) {
			stream << "      entry_set_" << ATTR(state, "documentOrder")
			       << "_o => entry_set_" << ATTR(state, "documentOrder")
			       << "_sig," << std::endl;
		}

		if (DOMUtils::filterChildElements(XML_PREFIX(_scxml).str() + "onexit", state).size() > 0) {
			stream << "      exit_set_" << ATTR(state, "documentOrder")
			       << "_o => exit_set_" << ATTR(state, "documentOrder")
			       << "_sig," << std::endl;
		}
	}

	for (auto transition : _transitions) {
		if (DOMUtils::filterChildType(DOMNode::ELEMENT_NODE, transition).size() > 0) {
			stream << "      transition_set_" << ATTR(transition, "postFixOrder")
			       << "_o => transition_set_" << ATTR(transition, "postFixOrder")
			       << "_sig," << std::endl;
		}
	}

	stream << "      completed_o  => completed_o" << std::endl;
	stream << "      );" << std::endl;
	stream << std::endl;

	stream << "  ec : event_controller" << std::endl;
	stream << "    port map (" << std::endl;
	stream << "      clk       => clk," << std::endl;
	stream << "      rst_i     => reset," << std::endl;
	stream << std::endl;

	stream << "      event_o     => next_event_i," << std::endl;
	stream << "      event_we_o => next_event_we_i," << std::endl;

	for (auto state : _states) {
		stream << "      state_active_" << ATTR(state, "documentOrder")
		       << "_i => state_active_" << ATTR(state, "documentOrder")
		       << "_sig," << std::endl;

		if (DOMUtils::filterChildElements(XML_PREFIX(_scxml).str() + "onentry", state).size() > 0) {
			stream << "      entry_set_" << ATTR(state, "documentOrder")
			       << "_i => entry_set_" << ATTR(state, "documentOrder")
			       << "_sig," << std::endl;
		}

		if (DOMUtils::filterChildElements(XML_PREFIX(_scxml).str() + "onexit", state).size() > 0) {
			stream << "      exit_set_" << ATTR(state, "documentOrder")
			       << "_i => exit_set_" << ATTR(state, "documentOrder")
			       << "_sig," << std::endl;
		}
	}

	for (auto transition : _transitions) {
		if (DOMUtils::filterChildType(DOMNode::ELEMENT_NODE, transition).size() > 0) {
			stream << "      transition_set_" << ATTR(transition, "postFixOrder")
			       << "_i => transition_set_" << ATTR(transition, "postFixOrder")
			       << "_sig," << std::endl;
		}
	}

	stream << "      micro_stepper_en_o  => dut_enable" << std::endl;
	//        stream << "      done_o  => open" << std::endl;
	stream << "      );" << std::endl;
	stream << std::endl;

	// find pass state
	std::list<DOMElement *> topLevelFinal =
	    DOMUtils::filterChildElements(XML_PREFIX(_scxml).str() + "final", _scxml);

	std::string passStateNo = "";
	for (auto final : topLevelFinal) {
		if (ATTR(final, "id") == "pass") {
			passStateNo = ATTR(final, "documentOrder");
		}
	}
	stream << "end architecture;" << std::endl;
	stream << "-- END TOP LEVEL" << std::endl;
}

void ChartToVHDL::writeEventController(std::ostream &stream) {
	// Add controler specific stuff here
	// create hardware top level
	stream << "-- Event Controller Logic" << std::endl;
	writeIncludes(stream);
	stream << "entity event_controller is" << std::endl;
	stream << "port(" << std::endl;
	stream << "    --inputs" << std::endl;
	stream << "    clk  :in    std_logic;" << std::endl;
	stream << "    rst_i  :in    std_logic;" << std::endl;

	for (auto state : _states) {
		stream << "    state_active_" << ATTR(state, "documentOrder")
		       << "_i :in std_logic;" << std::endl;

		if (DOMUtils::filterChildElements(XML_PREFIX(_scxml).str() + "onentry", state).size() > 0) {
			stream << "    entry_set_" << ATTR(state, "documentOrder")
			       << "_i :in std_logic;" << std::endl;
		}

		if (DOMUtils::filterChildElements(XML_PREFIX(_scxml).str() + "onexit", state).size() > 0) {
			stream << "    exit_set_" << ATTR(state, "documentOrder")
			       << "_i :in std_logic;" << std::endl;
		}
	}

	for (auto transition : _transitions) {
		if (DOMUtils::filterChildType(DOMNode::ELEMENT_NODE, transition).size() > 0) {
			stream << "    transition_set_" << ATTR(transition, "postFixOrder")
			       << "_i :in std_logic;" << std::endl;
		}
	}

	stream << "    --outputs" << std::endl;
	stream << "    micro_stepper_en_o :out  std_logic;" << std::endl;
	stream << "    event_o    :out  std_logic_vector( " << _eventBitSize << " downto 0);" << std::endl;
	stream << "    event_we_o :out  std_logic" << std::endl;
	stream << ");" << std::endl;
	stream << "end event_controller; " << std::endl;

	stream << std::endl;
	stream << "architecture behavioral of event_controller is " << std::endl;
	stream << std::endl;


	// Add signals and components
	stream << "signal rst : std_logic;" << std::endl;
	stream << "signal micro_stepper_en : std_logic;" << std::endl;
	stream << "signal cmpl_buf : std_logic;" << std::endl;
	stream << "signal completed_sig : std_logic;" << std::endl;
	stream << "signal event_bus : std_logic_vector( " << _eventBitSize << " downto 0);" << std::endl;
	stream << "signal event_we  : std_logic;" << std::endl;

	for (int i = 0; i < _execContent.size(); i++) {
		stream << "signal done_" << toStr(i) << "_sig : std_logic;" << std::endl;
		stream << "signal start_" << toStr(i) << "_sig : std_logic;" << std::endl;
	}

	stream << "-- sequence input line" << std::endl;
	for (int i = 0; i < _execContent.size(); i++) {
		stream << "signal seq_" << toStr(i) << "_sig : std_logic;" << std::endl;
	}
	stream << std::endl;

	stream << "begin" << std::endl;
	stream << std::endl;

	// check if there is SUPPORTED executable content
	bool foundSupportedExecContent = false;
	for (auto exContentElem : _execContent) {
		if (isSupportedExecContent(exContentElem)) {
			foundSupportedExecContent = true;
			break;
		}
	}
	if (!foundSupportedExecContent) {
		// set output correct if there is no supported excontent

		if (_execContent.size() > 0) {
			// show warning if executable content is ignored
			stream << "-- no supported executable content found" << std::endl;
			stream << "-- state machine may not run correctly" << std::endl;
		}
		stream << "-- setting output lines to fulfil dummy functionality" << std::endl;
		stream << "micro_stepper_en_o <= '1';" << std::endl;
		stream << "event_o <= (others => '0');" << std::endl;
		stream << "event_we_o <= '0';" << std::endl;
		stream << std::endl;
	} else {
		// system signal mapping
		stream << "rst <= rst_i;" << std::endl;
		stream << "micro_stepper_en_o <= micro_stepper_en;" << std::endl;
		stream << "event_o <= event_bus;" << std::endl;
		stream << "event_we_o <= event_we;" << std::endl;
		stream << std::endl;

		// stall management
		stream << "-- stalling microstepper" << std::endl;
		stream << "micro_stepper_en <= completed_sig or not ( '0' ";
		for (auto state : _states) {

			if (DOMUtils::filterChildElements(XML_PREFIX(_scxml).str() + "onentry", state).size() > 0) {
				stream << std::endl << "      or entry_set_" << ATTR(state, "documentOrder")
				       << "_i";
			}

			if (DOMUtils::filterChildElements(XML_PREFIX(_scxml).str() + "onexit", state).size() > 0) {
				stream << std::endl << "      or exit_set_" << ATTR(state, "documentOrder")
				       << "_i";
			}
		}
		for (auto transition : _transitions) {
			if (DOMUtils::filterChildType(DOMNode::ELEMENT_NODE, transition).size() > 0) {
				stream << std::endl << "      or transition_set_" << ATTR(transition, "postFixOrder")
				       << "_i";
			}
		}
		stream << ");" << std::endl;
		stream << std::endl;

		// sequential code operation
		stream << "-- seq code block " << std::endl;
		stream << "ex_content_block : process (clk, rst) " << std::endl;
		stream << "begin" << std::endl;
		stream << "  if rst = '1' then" << std::endl;
		for (int i = 0; i < _execContent.size(); i++) {
			stream << "    done_" << toStr(i) << "_sig <= '0';" << std::endl;
		}
		stream << "    event_bus <= (others => '0');" << std::endl;
		stream << "    event_we <= '0';" << std::endl;
		stream << "    cmpl_buf <= '0';" << std::endl;
		stream << "    completed_sig <= '0';" << std::endl;
		stream << "  elsif rising_edge(clk) then" << std::endl;

		stream << "    if micro_stepper_en = '1' then" << std::endl;
		stream << "      cmpl_buf <= '0' ;" << std::endl;
		stream << "    else" << std::endl;
		stream << "      cmpl_buf <= seq_" << toStr(_execContent.size() - 1)
		       << "_sig;" << std::endl;
		stream << "    end if;" << std::endl;
		stream << "    completed_sig <= cmpl_buf;" << std::endl << std::endl;

		size_t i = 0;
		std::string seperator = "    ";
		for (auto ecIter = _execContent.begin(); ecIter != _execContent.end(); ecIter++, i++) {
			DOMElement *exContentElem = *ecIter;

			if (isSupportedExecContent(exContentElem)) {

				stream << seperator << "if start_" << toStr(i) << "_sig = '1' then"
				       << std::endl;

				size_t jj = 0;
				for (auto eventIter = _eventNames.begin(); eventIter != _eventNames.end(); eventIter++, jj++) {
					if (((*eventIter)->value) == ATTR(exContentElem, "event")) {
						break;
					}
				}
				stream << "      event_bus <= \"" << toBinStr(jj, _eventBitSize + 1) << "\";" << std::endl;
				stream << "      done_" << toStr(i) << "_sig <= '1';" << std::endl;
				stream << "      event_we <= '1';" << std::endl;
				seperator = "    els";
			}
		}
		stream << "    elsif micro_stepper_en = '1' then" << std::endl;
		i = 0;
		//for (auto exContentElem : _execContent) {
		for (auto ecIter = _execContent.begin(); ecIter != _execContent.end(); ecIter++, i++) {
			DOMElement *exContentElem = *ecIter;
			if (isSupportedExecContent(exContentElem)) {
				stream << "      done_" << toStr(i) << "_sig <= '0';" << std::endl;
			}
		}
		stream << "      event_we <= '0';" << std::endl;
		stream << "    end if;" << std::endl;
		stream << "  end if;" << std::endl;
		stream << "end process;" << std::endl;
		stream << std::endl;

		i = 0;
		for (auto ecIter = _execContent.begin(); ecIter != _execContent.end(); ecIter++, i++) {
			// start lines
			stream << "start_" << toStr(i) << "_sig <= "
			       << getLineForExecContent(*ecIter) << " and "
			       << "not done_" << toStr(i) << "_sig";

			// if not needed, since seq_0_sig is hard coded as '1'.
//		if (i != 0) { // if not first element
			stream << " and seq_" << toStr(i) << "_sig";
//		}

			stream << ";" << std::endl;

		}

		stream << "seq_0_sig <= '1';" << std::endl;

		if (_execContent.size() > 1) {
			i = 0;
			for (auto ecIter = _execContent.begin(); ecIter != _execContent.end(); ecIter++, i++) {
				// prevent writing seq_0_sig since this should be hardcoded to '1'
				if (i != 0) {
					// seq lines (input if process i is in seqence now)
					stream << "seq_" << toStr(i) << "_sig <= "
					       << "done_" << toStr(i - 1) << "_sig or "
					       << "( not "
					       << getLineForExecContent(*ecIter);
					stream << " and seq_" << toStr(i - 1) << "_sig";
					stream << " );" << std::endl;
				}
			}
		}
		stream << std::endl;
	}

	stream << "end behavioral; " <<
	       std::endl;
	stream << "-- END Event Controller Logic" <<
	       std::endl;
	stream <<
	       std::endl;
}


void ChartToVHDL::writeConditionSolver(std::ostream &stream) {
	// TODO implement
	// --> solves conditions given by ast
	// --> Level 1 support In(), >, <, =
	// --> Level 2 support +, -
	// --> Level 3 support *, /, mod <-- (just integer operations)

	// Add controler specific stuff here
	// create hardware top level
	stream << "-- Condition Solver Logic" << std::endl;
	writeIncludes(stream);
	stream << "entity condition_solver is" << std::endl;
	stream << "port(" << std::endl;
	stream << "    --inputs" << std::endl;
	stream << "    clk  :in    std_logic;" << std::endl;
	stream << "    rst_i  :in    std_logic;" << std::endl;

	for (auto state : _states) {
		stream << "    state_active_" << ATTR(state, "documentOrder")
		       << "_i :in std_logic;" << std::endl;
	}

	stream << "    --outputs" << std::endl;

	for (auto transition : _transitions) {
		if (HAS_ATTR(transition, "cond")) {
			stream << "    transition_condition_fulfilled_" << ATTR(transition, "postFixOrder")
			       << "_o :out std_logic;" << std::endl;
		}
	}

	stream << "    micro_stepper_en_o :out  std_logic" << std::endl;
	stream << ");" << std::endl;
	stream << "end condition_solver; " << std::endl;

	stream << std::endl;
	stream << "architecture behavioral of condition_solver is " << std::endl;
	stream << std::endl;


	// Add signals and components
	stream << "signal rst : std_logic;" << std::endl;
	stream << "signal micro_stepper_en : std_logic;" << std::endl;

	for (int i = 0; i < _execContent.size(); i++) {
		stream << "signal done_" << toStr(i) << "_sig : std_logic;" << std::endl;
		stream << "signal start_" << toStr(i) << "_sig : std_logic;" << std::endl;
	}

	for (auto transition : _transitions) {
		if (HAS_ATTR(transition, "cond")) {
			stream << "signal transition_condition_fulfilled_" << ATTR(transition, "postFixOrder")
			       << "_sig : std_logic;" << std::endl;
		}
	}
	stream << std::endl;

	stream << "begin" << std::endl;
	stream << std::endl;

	// system signal mapping
	stream << "rst <= rst_i;" << std::endl;
	stream << "micro_stepper_en_o <= micro_stepper_en;" << std::endl;
	stream << std::endl;

	for (auto transition : _transitions) {
		if (HAS_ATTR(transition, "cond")) {
			stream << "transition_condition_fulfilled_" << ATTR(transition, "postFixOrder")
			       << "_o <= transition_condition_fulfilled_" << ATTR(transition, "postFixOrder")
			       << "_sig;" << std::endl;
		}
	}

	// stall management
	stream << "-- stalling microstepper" << std::endl;
	stream << "micro_stepper_en <= '1';" << std::endl;
	stream << std::endl;

	// solve conditions
	stream << "-- solve conditions" << std::endl;
	for (auto transition : _transitions) {
		if (HAS_ATTR(transition, "cond")) {
			stream << "-- cond:"<< ATTR(transition, "cond") << std::endl;
			// TODO parse code here and generate hardware from AST
			stream << "transition_condition_fulfilled_" << ATTR(transition, "postFixOrder")
			       << "_sig <= '0';" << std::endl;
		}
	}


	stream << "end behavioral; " <<
	       std::endl;
	stream << "-- END Condition Solver Logic" <<
	       std::endl;
	stream <<
	       std::endl;
}


std::string ChartToVHDL::getLineForExecContent(const DOMNode *elem) {
	const DOMNode *ecBlock = elem;
	while (ecBlock) {
		if (ecBlock->getNodeType() == DOMNode::ELEMENT_NODE) {
			std::string localName = LOCALNAME_CAST(ecBlock);
			if (localName == XML_PREFIX(_scxml).str() + "transition") {
				return "transition_set_" + ATTR_CAST(ecBlock, "postFixOrder") + "_i";
			}

			if (localName == XML_PREFIX(_scxml).str() + "onentry") {
				return "entry_set_" + ATTR_CAST(ecBlock->getParentNode(), "documentOrder") + "_i";
			}

			if (localName == XML_PREFIX(_scxml).str() + "onexit") {
				return "exit_set_" + ATTR_CAST(ecBlock->getParentNode(), "documentOrder") + "_i";
			}

		}
		ecBlock = ecBlock->getParentNode();
	}

	return "";
}

void ChartToVHDL::writeMicroStepper(std::ostream &stream) {
	// create MicroStepper top level
	stream << "-- FSM Logic" << std::endl;
	writeIncludes(stream);
	stream << "entity micro_stepper is" << std::endl;
	stream << "port(" << std::endl;
	stream << "    --inputs" << std::endl;
	stream << "    clk  :in    std_logic;" << std::endl;
	stream << "    rst_i  :in    std_logic;" << std::endl;
	stream << "    en   :in    std_logic;" << std::endl;
	stream << "    next_event_i    :in  std_logic_vector( " << _eventBitSize << " downto 0);" << std::endl;
	stream << "    next_event_we_i :in  std_logic;" << std::endl;

	for (auto transition : _transitions) {
		if (HAS_ATTR(transition, "cond")) { // create enable line if transition has conditions
			stream << "signal transition_condition_fulfilled_" << ATTR(transition, "postFixOrder") <<
			       "_i : std_logic;"
			       << std::endl;
		}
	}

	stream << "    --outputs" << std::endl;
	stream << "    error_o     :out std_logic;" << std::endl;

	for (auto state : _states) {
		stream << "    state_active_" << ATTR(state, "documentOrder") << "_o :out std_logic;" << std::endl;

		if (DOMUtils::filterChildElements(XML_PREFIX(_scxml).str() + "onentry", state).size() > 0) {
			stream << "    entry_set_" << ATTR(state, "documentOrder") << "_o :out std_logic;" << std::endl;
		}

		if (DOMUtils::filterChildElements(XML_PREFIX(_scxml).str() + "onexit", state).size() > 0) {
			stream << "    exit_set_" << ATTR(state, "documentOrder") << "_o :out std_logic;" << std::endl;
		}
	}

	for (auto transition : _transitions) {
		if (DOMUtils::filterChildType(DOMNode::ELEMENT_NODE, transition).size() > 0) {
			stream << "    transition_set_" << ATTR(transition, "postFixOrder") << "_o :out std_logic;"
			       << std::endl;
		}
	}

	stream << "    completed_o :out std_logic" << std::endl;
	stream << ");" << std::endl;
	stream << "end micro_stepper; " << std::endl;

	stream << std::endl;
	stream << "architecture behavioral of micro_stepper is " << std::endl;
	stream << std::endl;

	// Add signals and components
	writeSignalsAndComponents(stream);

	stream << std::endl;
	stream << "begin" << std::endl;
	stream << std::endl;

	// signal mapping
	writeModuleInstantiation(stream);

	// signal handler
	writeSpontaneousHandler(stream);
	writeErrorHandler(stream);
	writeInternalEventHandler(stream);
	writeStateHandler(stream);
	writeResetHandler(stream);

	// combinatorial logic for Sn+1
	writeOptimalTransitionSetSelection(stream);
	writeExitSet(stream);
	writeCompleteEntrySet(stream);
	writeEntrySet(stream);
	//writeDefaultCompletions(stream);
	writeActiveStateNplusOne(stream);

	// connect output signals
	writeSystemSignalMapping(stream);


	stream << std::endl;
	stream << "end behavioral; " << std::endl;
	stream << "-- END FSM Logic" << std::endl;
}

void ChartToVHDL::writeFiFo(std::ostream &stream) {
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
	stream << "  data_in     : in  std_logic_vector( " << _eventBitSize << " downto 0);" << std::endl;
	stream << "  data_out  : out std_logic_vector( " << _eventBitSize << " downto 0);" << std::endl;
	stream << "  empty       : out std_logic;" << std::endl;
	stream << "  full        : out std_logic" << std::endl;
	stream << ");" << std::endl;
	stream << "end std_fifo;" << std::endl;
	stream << "" << std::endl;
	stream << "architecture behavioral of std_fifo is" << std::endl;
	stream << "begin" << std::endl;
	stream << "-- Memory Pointer Process" << std::endl;
	stream << "fifo_proc : process (clk)" << std::endl;
	stream << "  type FIFO_Memory is array (0 to FIFO_DEPTH - 1) of std_logic_vector( " << _eventBitSize <<
	       " downto 0);" << std::endl;
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

void ChartToVHDL::writeSignalsAndComponents(std::ostream &stream) {
	// create internal signals
	stream << "-- system signals" << std::endl;
	stream << "signal stall : std_logic;" << std::endl;
	stream << "signal completed_sig : std_logic;" << std::endl;
	stream << "signal rst : std_logic;" << std::endl;
	stream << std::endl;

	stream << "-- state signals" << std::endl;

	std::list<std::string> signalDecls;

	for (auto state : _states) {
		std::string parent = ATTR(state, "parent");

		signalDecls.push_back("signal state_active_" + ATTR(state, "documentOrder") + "_sig : std_logic;");
		signalDecls.push_back("signal state_next_" + ATTR(state, "documentOrder") + "_sig : std_logic;");
		signalDecls.push_back("signal in_entry_set_" + ATTR(state, "documentOrder") + "_sig : std_logic;");
		signalDecls.push_back("signal in_exit_set_" + ATTR(state, "documentOrder") + "_sig : std_logic;");
		signalDecls.push_back("signal in_complete_entry_set_" + ATTR(state, "documentOrder") + "_sig : std_logic;");

		// not needed for <scxml> state
		if (parent.size() != 0) {
			signalDecls.push_back(
			    "signal in_complete_entry_set_up_" + ATTR(state, "documentOrder") + "_sig : std_logic;");
		}
	}

	signalDecls.sort();
	for (std::list<std::string>::iterator iter = signalDecls.begin(); iter != signalDecls.end(); iter++) {
		stream << *iter << std::endl;
	}
	stream << std::endl;


	stream << "-- transition signals" << std::endl;
	stream << "signal spontaneous_en : std_logic;" << std::endl;
	stream << "signal spontaneous_active : std_logic;" << std::endl;
	stream << "signal optimal_transition_set_combined_sig : std_logic;" << std::endl;

	for (auto transition : _transitions) {
		stream << "signal in_optimal_transition_set_" << ATTR(transition, "postFixOrder") << "_sig : std_logic;"
		       << std::endl;
	}
	stream << std::endl;

	stream << "-- event signals" << std::endl;
	stream << "signal int_event_write_en : std_logic;" << std::endl;
	stream << "signal int_event_read_en : std_logic;" << std::endl;
	stream << "signal int_event_empty : std_logic;" << std::endl;
	stream << "signal int_event_input : std_logic_vector( " << _eventBitSize << " downto 0);" << std::endl;
	stream << "signal int_event_output : std_logic_vector( " << _eventBitSize << " downto 0);" << std::endl;
	stream << "signal next_event_re : std_logic;" << std::endl;
	stream << "signal event_dequeued : std_logic;" << std::endl;
	stream << "signal next_event : std_logic_vector( " << _eventBitSize << " downto 0);" << std::endl;
	stream << "signal event_consumed : std_logic;" << std::endl;
	stream << std::endl;

	for (std::list<TrieNode *>::iterator eventIter = _eventNames.begin();
	        eventIter != _eventNames.end(); eventIter++) {
		stream << "signal event_" << escapeMacro((*eventIter)->value) << "_sig : std_logic;" << std::endl;
	}
	stream << std::endl;

	stream << "-- error signals" << std::endl;
	stream << "signal reg_error_out : std_logic;" << std::endl;
	stream << "signal error_full_int_event_fifo : std_logic;" << std::endl;
	stream << std::endl;

	// add components
	stream << "-- event FIFO" << std::endl;
	stream << "component std_fifo is" << std::endl;
	stream << "port ( " << std::endl;
	stream << "	clk		: in  std_logic;" << std::endl;
	stream << "	rst		: in  std_logic;" << std::endl;
	stream << "	write_en	: in  std_logic;" << std::endl;
	stream << "	read_en         : in  std_logic;" << std::endl;
	stream << "	data_in         : in  std_logic_vector( " << _eventBitSize << " downto 0);" << std::endl;
	stream << "	data_out	: out std_logic_vector( " << _eventBitSize << " downto 0);" << std::endl;
	stream << "	empty           : out std_logic;" << std::endl;
	stream << "	full            : out std_logic" << std::endl; // we calculate how much we need
	stream << ");" << std::endl;
	stream << "end component;" << std::endl;
	stream << std::endl;
}

void ChartToVHDL::writeModuleInstantiation(std::ostream &stream) {
	// instantiate event fifo
	stream << "int_event_fifo : component std_fifo " << std::endl;
	stream << "port map ( " << std::endl;
	stream << "	clk         => clk," << std::endl;
	stream << "	rst         => rst_i," << std::endl;
	stream << "	write_en    => int_event_write_en," << std::endl;
	stream << "	read_en     => int_event_read_en," << std::endl;
	stream << "	data_in     => int_event_input," << std::endl;
	stream << "	data_out    => int_event_output," << std::endl;
	stream << "	empty       => int_event_empty," << std::endl;
	stream << "	full        => error_full_int_event_fifo" << std::endl; // we calculate how much we need
	stream << ");" << std::endl;
	stream << std::endl;
}

void ChartToVHDL::writeErrorHandler(std::ostream &stream) {
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

void ChartToVHDL::writeResetHandler(std::ostream &stream) {
	stream << "-- reset handler" << std::endl;
	stream << "rst <= rst_i;" << std::endl;
	stream << std::endl;
}

void ChartToVHDL::writeSpontaneousHandler(std::ostream &stream) {
	// sets spontaneous signal
	stream << "-- spontaneous handler" << std::endl;
	stream << "spontaneous_handler : process (clk, rst) " << std::endl;
	stream << "begin" << std::endl;
	stream << "    if rst = '1' then" << std::endl;
	stream << "        spontaneous_en <= '1';" << std::endl;
	stream << "    elsif rising_edge(clk) and stall = '0' then" << std::endl;
	stream << "        if spontaneous_en = '1' then" << std::endl;
	stream << "            spontaneous_en <= optimal_transition_set_combined_sig;" << std::endl;
	stream << "        else" << std::endl;
	//if new event is dequeued then 1 else stay 0 (but enable it when queue is empty -> spontaneous based state chart)
	stream << "            spontaneous_en <= event_dequeued or (not event_dequeued and int_event_empty);" <<
	       std::endl;
	stream << "        end if;" << std::endl;
	stream << "    end if;" << std::endl;
	stream << "end process;" << std::endl;
	stream << std::endl;
}

void ChartToVHDL::writeInternalEventHandler(std::ostream &stream) {
	// Add controler specific stuff here
	stream << "-- event handler" << std::endl;
	stream << "-- pops events and set event signals" << std::endl;
	stream << "event_handler : process (clk, rst) " << std::endl;
	stream << "begin" << std::endl;
	stream << "    if rst = '1' then" << std::endl;

	for (std::list<TrieNode *>::iterator eventIter = _eventNames.begin();
	        eventIter != _eventNames.end(); eventIter++) {
		stream << "        event_" << escapeMacro((*eventIter)->value) << "_sig <= '0';" << std::endl;
	}

	stream << "        event_dequeued <= '0';" << std::endl;
	stream << "        event_consumed <= '0';" << std::endl;

	stream << "    elsif falling_edge(clk) and stall = '0' then" << std::endl;

	VContainer eventConsumed = VOR;
	for (auto transition : _transitions) {

		if (HAS_ATTR(transition, "event") == true) {
			*eventConsumed += VLINE("in_optimal_transition_set_"
			                        + ATTR(transition, "postFixOrder") + "_sig");
		}
	}

	VBranch *tree = (VASSIGN,
	                 VLINE("       event_consumed"),
	                 eventConsumed);
	tree->print(stream);
	stream << ";" << std::endl;

	stream << "      if int_event_empty = '0' then " << std::endl;
	stream << "      case next_event is " << std::endl;

	size_t jj = 0;
	for (std::list<TrieNode *>::iterator eventIter = _eventNames.begin();
	        eventIter != _eventNames.end(); eventIter++, jj++) {

		stream << "      when \"" << toBinStr(jj, _eventBitSize + 1) << "\" =>" << std::endl;
		for (std::list<TrieNode *>::iterator eventIter2 = _eventNames.begin();
		        eventIter2 != _eventNames.end(); eventIter2++) {
			stream << "        event_" << escapeMacro((*eventIter2)->value);
			if (escapeMacro((*eventIter)->value) == escapeMacro((*eventIter2)->value)) {
				stream << "_sig <= '1';" << std::endl;
			} else {
				stream << "_sig <= '0';" << std::endl;
			}
		}
		stream << "        event_dequeued <= '1';" << std::endl;
	}
	stream << "      when others =>" << std::endl;
	for (std::list<TrieNode *>::iterator eventIter = _eventNames.begin();
	        eventIter != _eventNames.end(); eventIter++) {
		stream << "        event_" << escapeMacro((*eventIter)->value) << "_sig <= '0';" << std::endl;
	}
	stream << "        event_dequeued <= '0';" << std::endl;
	stream << "      end case;" << std::endl;
	stream << "      elsif int_event_empty = '1' and event_consumed = '1' then" << std::endl;

	for (std::list<TrieNode *>::iterator eventIter = _eventNames.begin();
	        eventIter != _eventNames.end(); eventIter++) {
		stream << "        event_" << escapeMacro((*eventIter)->value) << "_sig <= '0';" << std::endl;
	}
	stream << "        event_dequeued <= '0';" << std::endl;
	stream << "    end if;" << std::endl;
	stream << "    end if;" << std::endl;
	stream << "end process;" << std::endl;
	stream << std::endl;

	stream << "next_event_re <= not int_event_empty and not stall; " << std::endl;
	stream << "next_event <= int_event_output; " << std::endl;
	stream << "int_event_write_en <= next_event_we_i; " << std::endl;
	stream << "int_event_input <= next_event_i; " << std::endl;
	stream << "int_event_read_en <= not stall; --not spontaneous_en and  " << std::endl;
	stream << std::endl;
}

void ChartToVHDL::writeActiveStateNplusOne(std::ostream &stream) {
	stream << "-- active configuration" << std::endl;

	for (auto state : _states) {
		std::string parent = ATTR(state, "parent");

		// special case for <scxml> to start the state machine
		if (parent.size() == 0) {
			stream << "        state_next_" << ATTR(state, "documentOrder") << "_sig <= " <<
			       "not completed_sig;" << std::endl;
			continue;
		}

		VBranch *tree = (VASSIGN,
		                 VLINE("state_next_" + ATTR(state, "documentOrder") + "_sig"),
		                 (VOR,
		                  VLINE("in_complete_entry_set_" + ATTR(state, "documentOrder") + "_sig"),
		                  (VAND, (VNOT, VLINE("in_exit_set_" + ATTR(state, "documentOrder") + "_sig")),
		                   VLINE("state_active_" + ATTR(state, "documentOrder") + "_sig"))
		                 ));

		tree->print(stream);
		stream << ";" << std::endl;

	}
}

void ChartToVHDL::writeOptimalTransitionSetSelection(std::ostream &stream) {
	stream << "-- optimal transition set selection" << std::endl;
	VContainer optimalTransitions = VOR;
	VContainer spontaneoursActive = VOR;

	for (auto transIter = _transitions.begin(); transIter != _transitions.end(); transIter++) {
		DOMElement *transition = *transIter;
		std::string conflicts = ATTR(transition, "conflictBools");


		VContainer nameMatchers = VOR;
		if (HAS_ATTR(transition, "event")) {
			std::list<std::string> eventDescs = tokenize(ATTR(transition, "event"));
			for (std::list<std::string>::iterator descIter = eventDescs.begin();
			        descIter != eventDescs.end(); descIter++) {
				std::list<TrieNode *> eventNames = _eventTrie.getWordsWithPrefix(
				                                       (*descIter) == "*" ? "" : *descIter);
				for (std::list<TrieNode *>::iterator eventIter = eventNames.begin();
				        eventIter != eventNames.end(); eventIter++) {
					*nameMatchers += VLINE("event_" + escapeMacro((*eventIter)->value) + "_sig");
				}
			}
		} else {
			*nameMatchers += VLINE("'1'");
		}

		VContainer conflicters = VOR;
		for (size_t j = 0; j < strTo<size_t>(ATTR(transition, "postFixOrder")); j++) {
			if (conflicts[j] == '1') {
				*conflicters += VLINE("in_optimal_transition_set_" + toStr(j) + "_sig");
			}
		}

		VBranch *tree = (VASSIGN,
		                 VLINE("in_optimal_transition_set_" + ATTR(transition, "postFixOrder") + "_sig"),
		                 (VAND,
		                  (HAS_ATTR(transition, "event")
		                   ? (VNOT, VLINE("spontaneous_active"))
		                   : (VNOP, VLINE("spontaneous_en"))),

		                  HAS_ATTR(transition, "cond")
		                  ? (VNOP,
		                     VLINE("transition_condition_fulfilled_" + ATTR(transition, "postFixOrder") +
		                           "_i"))
		                  : (VNOP, VLINE("'1'")),

		                  VLINE("state_active_" + ATTR(transition, "source") + "_sig"),
		                  nameMatchers,
		                  (VNOT, conflicters)));

		tree->print(stream);
		stream << ";" << std::endl;

		*optimalTransitions += VLINE("in_optimal_transition_set_"
		                             + ATTR(transition, "postFixOrder") + "_sig");
		if (HAS_ATTR(transition, "event") == false) {
			*spontaneoursActive += VLINE("in_optimal_transition_set_"
			                             + ATTR(transition, "postFixOrder") + "_sig");
		}
	}

	VBranch *tree = (VASSIGN,
	                 VLINE("optimal_transition_set_combined_sig"),
	                 optimalTransitions);
	tree->print(stream);
	stream << ";" << std::endl;

	VBranch *tree2 = (VASSIGN,
	                  VLINE("spontaneous_active"),
	                  spontaneoursActive);
	tree2->print(stream);
	stream << ";" << std::endl;
}


void ChartToVHDL::writeExitSet(std::ostream &stream) {
	stream << "-- exit set selection" << std::endl;

	for (auto state : _states) {

		std::string completion = ATTR(state, "completionBools");
		std::string ancestors = ATTR(state, "ancBools");
		std::string children = ATTR(state, "childBools");
		std::string parent = ATTR(state, "parent");

		VContainer exitsetters = VOR;
		for (auto transition : _transitions) {
			std::string exitSet = ATTR(transition, "exitSetBools");
			if (exitSet.at(strTo<size_t>(ATTR(state, "documentOrder"))) == '1') {
				*exitsetters += VLINE("in_optimal_transition_set_" + ATTR(transition, "postFixOrder") + "_sig ");
			}
		}

		VBranch *tree = (VASSIGN,
		                 VLINE("in_exit_set_" + ATTR(state, "documentOrder") + "_sig"),
		                 (VAND,
		                  VLINE("state_active_" + ATTR(state, "documentOrder") + "_sig"),
		                  exitsetters));

		tree->print(stream);
		stream << ";" << std::endl;
	}
}

void ChartToVHDL::writeEntrySet(std::ostream &stream) {
	stream << "-- entry set selection" << std::endl;

	for (auto state : _states) {

		VBranch *tree = (VASSIGN,
		                 VLINE("in_entry_set_" + ATTR(state, "documentOrder") + "_sig"),
		                 (VAND,
		                  VLINE("in_complete_entry_set_" + ATTR(state, "documentOrder") + "_sig"),
		                  (VOR, VLINE("in_exit_set_" + ATTR(state, "documentOrder") + "_sig"),
		                   (VNOT, VLINE("state_active_" + ATTR(state, "documentOrder") + "_sig")))));

		tree->print(stream);
		stream << ";" << std::endl;
	}
}

void ChartToVHDL::writeCompleteEntrySet(std::ostream &stream) {
	stream << "-- complete entry set selection" << std::endl;

	for (auto state : _states) {
		std::string completion = ATTR(state, "completionBools");
		std::string ancestors = ATTR(state, "ancBools");
		std::string children = ATTR(state, "childBools");
		std::string parent = ATTR(state, "parent");

		if (parent.size() == 0) {
			continue; // skips <scxml> node
		}


		// EntrySet for every state types
		VContainer optimalEntrysetters = VOR;
		for (auto transition : _transitions) {
			// Is this state in TargetSet of the transition?
			std::string targetSet = ATTR(transition, "targetBools");
			if (targetSet[strTo<size_t>(ATTR(state, "documentOrder"))] == '1') {
				//yes? then add the transition to optimal entry set of the state
				*optimalEntrysetters +=
				    VLINE("in_optimal_transition_set_" + ATTR(transition, "postFixOrder") + "_sig");
			}
		}

		// if composite state (or root) we have to add ancestor completion
		VContainer completeEntrysetters = VOR;
		if (isCompound(state) || isParallel(state)) {
			for (auto tmp_state : _states) {
				// is tmp_state is child of state continue?
				if (children[strTo<size_t>(ATTR(state, "documentOrder"))] == '1') {
					// yes? then add its complete_entry_set_up as ancestor completion
					*completeEntrysetters +=
					    VLINE("in_complete_entry_set_up_" + ATTR(tmp_state, "documentOrder") + "_sig");
				}
			}
		}

		VBranch *tree = (VASSIGN,
		                 VLINE("in_complete_entry_set_up_" + ATTR(state, "documentOrder") + "_sig"),
		                 (VOR, optimalEntrysetters, completeEntrysetters)
		                );
		tree->print(stream);
		stream << ";" << std::endl;
	}


	// descendant completion
	for (auto state : _states) {
		std::string completion = ATTR(state, "completionBools");
		std::string ancestors = ATTR(state, "ancBools");
		std::string parent = ATTR(state, "parent"); //is it a int ?

		if (parent.size() == 0) {
			continue; // skips <scxml> node
		}

		VContainer descendantCompletion = VAND;
		// if parent is compound
		if (getParentState(state) != NULL &&
		        isCompound(getParentState(state))) {
			std::string children = ATTR_CAST(_states[strTo<size_t>(parent)],
			                                 "childBools");

			std::string parentInit = ATTR(getParentState(state), "initial");
			if (// if parent has init field an this state is inside --> add it as default completion
			    (!parentInit.empty()
			     && ATTR(state, "id").compare(parentInit) == 0) ||
			    // or add this state as default completion when parent has no init field and it is the first in document order
			    (parentInit.empty() &&
			     (strTo<size_t>(ATTR(getParentState(state), "documentOrder")) + 1) ==
			     strTo<size_t>(ATTR(state, "documentOrder")))) {
				*descendantCompletion +=
				    VLINE("in_entry_set_" + ATTR(getParentState(state), "documentOrder") + "_sig");

				// but only if compound parent is not already completed
				for (auto tmp_state : _states) {
					if (tmp_state == state) {
						// skip state itselve
						continue;
					}
					if (children[strTo<size_t>(ATTR(tmp_state, "documentOrder"))] == '1') {
						*descendantCompletion += (VNOT,
						                          (VAND,
						                           VLINE("state_active_" + ATTR(tmp_state, "documentOrder") + "_sig"),
						                           (VNOT,
						                            VLINE("in_exit_set_" + ATTR(tmp_state, "documentOrder") +
						                                  "_sig"))));
					}
				}
			} else {
				// disable this branche
				*descendantCompletion += VLINE("'0'");
			}
		} else
			// if parent is parallel
			if (getParentState(state) != NULL &&
			        isParallel(getParentState(state))) {
				*descendantCompletion +=
				    VLINE("in_complete_entry_set_" + ATTR(getParentState(state), "documentOrder") + "_sig");
			}

		VBranch *tree = (VASSIGN,
		                 VLINE("in_complete_entry_set_" + ATTR(state, "documentOrder") + "_sig"),
		                 (VOR,
		                  VLINE("in_complete_entry_set_up_" + ATTR(state, "documentOrder") + "_sig"),
		                  descendantCompletion));

		tree->print(stream);
		stream << ";" << std::endl;
	}
}

void ChartToVHDL::writeStateHandler(std::ostream &stream) {
	// updater for current state
	stream << "-- State Handler" << std::endl;
	stream << "-- updates current state" << std::endl;
	stream << "state_proc: process(clk, rst, stall)" << std::endl;
	stream << "begin" << std::endl;
	stream << "    if rst = '1' then" << std::endl;

	for (auto state : _states) {
		stream << "        state_active_" << ATTR(state, "documentOrder") << "_sig <= " << "'0';" << std::endl;
	}

	stream << "        in_complete_entry_set_0_sig <= '1';" << std::endl;
	stream << "    elsif (rising_edge(clk) and stall = '0') then" << std::endl;
	stream << "        in_complete_entry_set_0_sig <= '0';" << std::endl;

	for (auto state : _states) {
		stream << "        state_active_" << ATTR(state, "documentOrder") << "_sig <= " << "state_next_" <<
		       ATTR(state, "documentOrder") << "_sig;" << std::endl;
	}

	stream << "    end if;" << std::endl;
	stream << "end process;" << std::endl;
	stream << std::endl;
}

void ChartToVHDL::writeSystemSignalMapping(std::ostream &stream) {
	stream << "-- system signals" << std::endl;
	std::list<DOMElement *> topLevelFinal = DOMUtils::filterChildElements(XML_PREFIX(_scxml).str() + "final",
	                                        _scxml);

	VContainer tlf = VOR;
	for (auto final : topLevelFinal) {
		*tlf += VLINE("state_active_" + ATTR(final, "documentOrder") + "_sig");

	}

	VBranch *tree = (VASSIGN,
	                 VLINE("completed_sig"),
	                 tlf);

	tree->print(stream);
	stream << ";" << std::endl;

	// tmp mapping for events
//	stream << "stall_handler : process (clk, rst) " << std::endl;
//	stream << "begin" << std::endl;
//	stream << "    if rst = '1' then" << std::endl;
//	stream << "        stall <= '0';" << std::endl;
//	stream << "    elsif rising_edge(clk) then" << std::endl;
	// empty queue as stall source can arise some issues with state charts just based on spontaneous transitions
	stream << "        stall <= not en or completed_sig ; --or ( int_event_empty and not spontaneous_en); " <<
	       std::endl;
//	stream << "    end if;" << std::endl;
//	stream << "end process;" << std::endl;
//	stream << std::endl;

	// interface signals
	stream << "-- interface signals" << std::endl;
	for (auto state : _states) {
		stream << "state_active_" << ATTR(state, "documentOrder")
		       << "_o <= state_active_" << ATTR(state, "documentOrder")
		       << "_sig;" << std::endl;
		if (DOMUtils::filterChildElements(XML_PREFIX(_scxml).str() + "onexit", state).size() > 0) {
			stream << "exit_set_" << ATTR(state, "documentOrder")
			       << "_o <= in_exit_set_" << ATTR(state, "documentOrder")
			       << "_sig;" << std::endl;
		}

		if (DOMUtils::filterChildElements(XML_PREFIX(_scxml).str() + "onentry", state).size() > 0) {
			stream << "entry_set_" << ATTR(state, "documentOrder")
			       << "_o <= in_entry_set_" << ATTR(state, "documentOrder")
			       << "_sig;" << std::endl;
		}
	}

	for (auto transition : _transitions) {
		if (DOMUtils::filterChildType(DOMNode::ELEMENT_NODE, transition).size() > 0) {
			stream << "transition_set_" << ATTR(transition, "postFixOrder")
			       << "_o <= in_optimal_transition_set_" << ATTR(transition, "postFixOrder")
			       << "_sig;" << std::endl;
		}
	}

	stream << "completed_o <= completed_sig; " << std::endl;
	stream << "error_o <= reg_error_out; " << std::endl;
	stream << std::endl;
}


}
