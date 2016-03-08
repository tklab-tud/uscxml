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

    std::string ChartToVHDL::eventNameEscape(const std::string& eventName) {
        std::string escaped = escape(eventName);
        boost::replace_all(escaped, ".", "_");
        return escaped;
    }

    void ChartToVHDL::findEvents() {
        // elements with an event attribute
        NodeSet<std::string> withEvent;
        withEvent.push_back(DOMUtils::filterChildElements(_nsInfo.xmlNSPrefix + "raise", _scxml, true));
        withEvent.push_back(DOMUtils::filterChildElements(_nsInfo.xmlNSPrefix + "send", _scxml, true));
        withEvent.push_back(DOMUtils::filterChildElements(_nsInfo.xmlNSPrefix + "transition", _scxml, true)); // TODO was haben events da verloren???

        for (size_t i = 0; i < withEvent.size(); i++) {
            if (HAS_ATTR_CAST(withEvent[i], "event")) {
                // TODO: tokenize!
                if (ATTR_CAST(withEvent[i], "event") != "*")
                    _eventTrie.addWord(ATTR_CAST(withEvent[i], "event"));
            }
        }

        std::set<std::string> elements;
        elements.insert(_nsInfo.xmlNSPrefix + "raise");
        //        elements.insert(_nsInfo.xmlNSPrefix + "if");
        //        elements.insert(_nsInfo.xmlNSPrefix + "elseif");
        //        elements.insert(_nsInfo.xmlNSPrefix + "else");
        //        elements.insert(_nsInfo.xmlNSPrefix + "foreach");
        //        elements.insert(_nsInfo.xmlNSPrefix + "log");
        //        elements.insert(_nsInfo.xmlNSPrefix + "send");
        //        elements.insert(_nsInfo.xmlNSPrefix + "assign");
        //        elements.insert(_nsInfo.xmlNSPrefix + "script");
        //        elements.insert(_nsInfo.xmlNSPrefix + "cancel");
        _execContent = DOMUtils::inDocumentOrder(elements, _scxml);

    }

    void ChartToVHDL::writeTo(std::ostream& stream) {
        // same preparations as the C transformation
        prepare();

        //    checkDocument();
        findEvents();


        stream << "-- generated from " << _sourceURL.asString() << std::endl;
        stream << "-- run as " << std::endl;
        stream << "--   ghdl --clean && ghdl -a foo.vhdl && ghdl -e tb && ./tb --stop-time=10ms --vcd=foo.vcd" << std::endl;
        stream << std::endl;

        writeTypes(stream);
        writeFiFo(stream);
        writeEventController(stream);
        writeMicroStepper(stream);
        writeTestbench(stream);
    }

    void ChartToVHDL::writeTypes(std::ostream & stream) {
        std::string seperator;

        stream << "-- required global types" << std::endl;
        stream << "library IEEE;" << std::endl;
        stream << "use IEEE.std_logic_1164.all;" << std::endl;
        stream << std::endl;
        stream << "package machine" << _md5 << " is" << std::endl;
        // create state type
        stream << "  subtype state_type is std_logic_vector( ";
        stream << _states.size() - 1;
        stream << " downto 0);" << std::endl;

        std::list<TrieNode*> eventNames = _eventTrie.getWordsWithPrefix("");
        stream << "  type event_type is ( ";
        seperator = "";

        for (std::list<TrieNode*>::iterator eventIter = eventNames.begin(); eventIter != eventNames.end(); eventIter++) {
            stream << seperator << "hwe_" << eventNameEscape((*eventIter)->value);
            seperator = ", ";
        }
        stream << " );" << std::endl;

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

    void ChartToVHDL::writeTestbench(std::ostream& stream) {

        stream << "-- TESTBENCH" << std::endl;
        writeIncludes(stream);
        stream << std::endl;

        stream << "-- empty entity" << std::endl;
        stream << "entity tb is" << std::endl;
        stream << "end entity tb;" << std::endl;
        stream << std::endl;

        stream << "architecture bhv of tb is" << std::endl;
        stream << std::endl;

        stream << "  -- Module declaration" << std::endl;
        stream << "  component micro_stepper is" << std::endl;
        stream << "    port (" << std::endl;
        stream << "    --inputs" << std::endl;
        stream << "    clk  :in    std_logic;" << std::endl;
        stream << "    rst_i  :in    std_logic;" << std::endl;
        stream << "    en   :in    std_logic;" << std::endl;
        stream << "    next_event_i    :in  event_type;" << std::endl;
        stream << "    next_event_we_i :in  std_logic;" << std::endl;
        stream << "    --outputs" << std::endl;
        stream << "    error_o     :out std_logic;" << std::endl;

        for (size_t i = 0; i < _states.size(); i++) {
            Element<std::string> state(_states[i]);
            stream << "    state_active_" << ATTR(state, "documentOrder") << "_o :out std_logic;" << std::endl;
        }

        stream << "    completed_o :out std_logic" << std::endl;
        stream << "    );" << std::endl;
        stream << "  end component;" << std::endl;
        stream << std::endl;

        stream << "  -- input" << std::endl;
        stream << "  signal clk   : std_logic := '0';" << std::endl;
        stream << "  signal reset : std_logic;" << std::endl;
        stream << "  signal next_event_we_i : std_logic := '0';" << std::endl;
        stream << "  signal next_event_i : event_type;" << std::endl;
        stream << std::endl;

        stream << "  -- output" << std::endl;
        stream << "  signal error_o, completed_o : std_logic;" << std::endl;
        stream << std::endl;

        stream << "begin" << std::endl;
        stream << "  clk   <= not clk  after 20 ns;  -- 25 MHz clock frequency" << std::endl;
        stream << "  reset <= '1', '0' after 100 ns; -- generates reset signal: --__" << std::endl;
        stream << std::endl;

        stream << "  -- Module instantiation" << std::endl;
        stream << "  dut : micro_stepper" << std::endl;
        stream << "    port map (" << std::endl;
        stream << "      clk       => clk," << std::endl;
        stream << "      rst_i     => reset," << std::endl;
        stream << "      en     => '1'," << std::endl;
        stream << std::endl;

        stream << "      next_event_i     => next_event_i," << std::endl;
        stream << "      next_event_we_i => next_event_we_i," << std::endl;
        stream << "      error_o  => error_o," << std::endl;

        for (size_t i = 0; i < _states.size(); i++) {
            Element<std::string> state(_states[i]);
            stream << "      state_active_" << ATTR(state, "documentOrder") << "_o => open," << std::endl;
        }

        stream << "      completed_o  => completed_o" << std::endl;
        stream << "      );" << std::endl;
        stream << std::endl;

        stream << "end architecture;" << std::endl;
        stream << "-- END TESTBENCH" << std::endl;

    }

    void ChartToVHDL::writeExContentBlock(std::ostream & stream,
            std::string index, std::list< Element<std::string> > commandSequence) {
        // index should be [entry, transition, exit]_<index of state/transition>_<optional index for block>

        // write clock blocks
    }

    void ChartToVHDL::writeEventController(std::ostream & stream) {
        // Add controler specific stuff here
        // create hardware top level
        stream << "-- Event Controller Logic" << std::endl;
        writeIncludes(stream);
        stream << "entity event_controller is" << std::endl;
        stream << "port(" << std::endl;
        stream << "    --inputs" << std::endl;
        stream << "    clk  :in    std_logic;" << std::endl;
        stream << "    rst_i  :in    std_logic;" << std::endl;
        stream << "    en   :in    std_logic;" << std::endl;

        for (size_t i = 0; i < _states.size(); i++) {
            Element<std::string> state(_states[i]);
            stream << "    state_active_" << ATTR(state, "documentOrder")
                    << "_i :in std_logic;" << std::endl;
            //TODO if has ex content
            stream << "    entry_set_" << ATTR(state, "documentOrder")
                    << "_i :in std_logic;" << std::endl;
            //TODO if has ex content
            stream << "    exit_set_" << ATTR(state, "documentOrder")
                    << "_i :in std_logic;" << std::endl;
        }

        for (size_t i = 0; i < _transitions.size(); i++) {
            Element<std::string> transition(_transitions[i]);
            //TODO if has ex content
            stream << "    transition_set_" << ATTR(transition, "postFixOrder")
                    << "_i :in std_logic;" << std::endl;
        }

        stream << "    --outputs" << std::endl;
        stream << "    event_o    :out  event_type;" << std::endl;
        stream << "    event_we_o :out  std_logic;" << std::endl;
        stream << "    done_o :out std_logic" << std::endl;
        stream << ");" << std::endl;
        stream << "end event_controller; " << std::endl;

        stream << std::endl;
        stream << "architecture behavioral of event_controller is " << std::endl;
        stream << std::endl;

        // Add signals and components
        stream << "signal rst : std_logic;" << std::endl;
        stream << "signal event_bus : event_type;" << std::endl;
        stream << "signal event_we  : std_logic;" << std::endl;
        stream << "signal done  : std_logic;" << std::endl;

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
        // signal mapping
        stream << "rst <= rst_i;" << std::endl;
        stream << "event_o <= event_bus;" << std::endl;
        stream << "event_we_o <= event_we;" << std::endl;
        stream << "done_o <= done;" << std::endl;
        stream << std::endl;

        // sequential code operation
        stream << "ex_content_block : process (clk) " << std::endl;
        stream << "begin" << std::endl;
        stream << "  if rst = '1' then" << std::endl;
        for (int i = 0; i < _execContent.size(); i++) {
            stream << "    done_" << toStr(i) << "_sig <= '0';" << std::endl;
        }
        stream << "  elsif rising_edge(clk) then" << std::endl;
        std::string seperator = "    ";
        for (int i = 0; i < _execContent.size(); i++) {
            Element<std::string> exContentTag(_execContent[i]);
            // TODO if raise
            if (true) {
                stream << seperator << "if start_" << toStr(i) << "_sig = '1' "
                        << "and done_" << toStr(i) << "_sig = '0' then"
                        << std::endl;
                stream << "        event_bus <= hwe_" << ATTR(exContentTag, "event")
                        << ";" << std::endl;
                stream << "        done_" << toStr(i) << "_sig <= '1';" << std::endl;
                seperator = "    els";
            }
        }
        stream << "    end if;" << std::endl;
        stream << "  end if;" << std::endl;
        stream << "end process;" << std::endl;
        stream << std::endl;

        // start signal generation
        if (_execContent.size() > 0) {
            stream << "start_0_sig <= "
                    << /* TODO find enable line and put here */ "'1'"
                    << ";" << std::endl;
        }

        for (int i = 0; i < _execContent.size(); i++) {
            // start lines
            stream << "start_" << toStr(i) << "_sig <= "
                    << /* TODO find enable line and put here */ "'1' and "
                    << "(not done_" << toStr(i) << "_sig )";
            if (i != 0) { // if not first element
                stream << " and seq_" << toStr(i) << "_sig";
            }
            stream << ";" << std::endl;
            
        }
        
        for (int i = 1; i < _execContent.size(); i++) {
            // seq lines
             stream << "seq_" << toStr(i) << "_sig <= "
                    << "done_"<< toStr(i) << "_sig or "
                    << "( not "
                    << /* TODO find enable line and put here */ "'1' and "
                    << "seq_" << toStr(i-1) << "_sig )";
            stream << ";" << std::endl;
        }
        stream << std::endl;

        stream << "end behavioral; " << std::endl;
        stream << "-- END Event Controller Logic" << std::endl;
    }

    void ChartToVHDL::writeMicroStepper(std::ostream & stream) {
        // create MicroStepper top level
        stream << "-- FSM Logic" << std::endl;
        writeIncludes(stream);
        stream << "entity micro_stepper is" << std::endl;
        stream << "port(" << std::endl;
        stream << "    --inputs" << std::endl;
        stream << "    clk  :in    std_logic;" << std::endl;
        stream << "    rst_i  :in    std_logic;" << std::endl;
        stream << "    en   :in    std_logic;" << std::endl;
        stream << "    next_event_i    :in  event_type;" << std::endl;
        stream << "    next_event_we_i :in  std_logic;" << std::endl;
        stream << "    --outputs" << std::endl;
        stream << "    error_o     :out std_logic;" << std::endl;

        for (size_t i = 0; i < _states.size(); i++) {
            Element<std::string> state(_states[i]);
            stream << "    state_active_" << ATTR(state, "documentOrder") << "_o :out std_logic;" << std::endl;
            //TODO if has ex content
            stream << "    entry_set_" << ATTR(state, "documentOrder") << "_o :out std_logic;" << std::endl;
            //TODO if has ex content
            stream << "    exit_set_" << ATTR(state, "documentOrder") << "_o :out std_logic;" << std::endl;
        }

        for (size_t i = 0; i < _transitions.size(); i++) {
            Element<std::string> transition(_transitions[i]);
            //TODO if has ex content
            stream << "    transition_set_" << ATTR(transition, "postFixOrder") << "_o :out std_logic;"
                    << std::endl;
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
        writeDefaultCompletions(stream);
        writeActiveStateNplusOne(stream);

        // connect output signals
        writeSystemSignalMapping(stream);


        stream << std::endl;
        stream << "end behavioral; " << std::endl;
        stream << "-- END FSM Logic" << std::endl;
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

    void ChartToVHDL::writeSignalsAndComponents(std::ostream & stream) {
        // create internal signals
        stream << "-- system signals" << std::endl;
        stream << "signal stall : std_logic;" << std::endl;
        stream << "signal completed_sig : std_logic;" << std::endl;
        stream << "signal rst_2 : std_logic;" << std::endl;
        stream << "signal rst_1 : std_logic;" << std::endl;
        stream << "signal rst : std_logic;" << std::endl;
        stream << std::endl;

        stream << "-- state signals" << std::endl;

        std::list<std::string> signalDecls;

        for (size_t i = 0; i < _states.size(); i++) {
            Element<std::string> state(_states[i]);

            signalDecls.push_back("signal state_active_" + ATTR(state, "documentOrder") + "_sig : std_logic;");
            signalDecls.push_back("signal state_next_" + ATTR(state, "documentOrder") + "_sig : std_logic;");
            signalDecls.push_back("signal in_entry_set_" + ATTR(state, "documentOrder") + "_sig : std_logic;");
            signalDecls.push_back("signal in_exit_set_" + ATTR(state, "documentOrder") + "_sig : std_logic;");
            signalDecls.push_back("signal in_complete_entry_set_up_" + ATTR(state, "documentOrder") + "_sig : std_logic;");
            signalDecls.push_back("signal in_complete_entry_set_" + ATTR(state, "documentOrder") + "_sig : std_logic;");
            signalDecls.push_back("signal default_completion_" + ATTR(state, "documentOrder") + "_sig : std_logic;");
        }

        signalDecls.sort();
        for (std::list<std::string>::iterator iter = signalDecls.begin(); iter != signalDecls.end(); iter++) {
            stream << *iter << std::endl;
        }
        stream << std::endl;


        stream << "-- transition signals" << std::endl;
        stream << "signal spontaneous_en : std_logic;" << std::endl;
        stream << "signal optimal_transition_set_combined_sig : std_logic;" << std::endl;

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
        stream << "signal next_event_dequeued : std_logic;" << std::endl;
        stream << "signal next_event : event_type;" << std::endl;
        stream << "signal event_consumed : std_logic;" << std::endl;
        stream << std::endl;

        std::list<TrieNode*> eventNames = _eventTrie.getWordsWithPrefix("");
        for (std::list<TrieNode*>::iterator eventIter = eventNames.begin(); eventIter != eventNames.end(); eventIter++) {
            stream << "signal event_" << eventNameEscape((*eventIter)->value) << "_sig : std_logic;" << std::endl;
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
        stream << "	data_in         : in  event_type;" << std::endl;
        stream << "	data_out	: out event_type;" << std::endl;
        stream << "	empty           : out std_logic;" << std::endl;
        stream << "	full            : out std_logic" << std::endl; // we calculate how much we need
        stream << ");" << std::endl;
        stream << "end component;" << std::endl;
        stream << std::endl;
    }

    void ChartToVHDL::writeModuleInstantiation(std::ostream & stream) {
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

    void ChartToVHDL::writeResetHandler(std::ostream & stream) {
        stream << "-- reset handler" << std::endl;
        stream << "rst_proc: process(clk, rst_i)" << std::endl;
        stream << "begin" << std::endl;
        stream << "    if rst_i = '1' then" << std::endl;
        stream << "        rst_2 <= '1';" << std::endl;
        stream << "        rst_1 <= '1';" << std::endl;
        stream << "        rst <= '1';" << std::endl;
        stream << "    elsif (rising_edge(clk)) then" << std::endl;
        stream << "        rst_2 <= rst_i;" << std::endl;
        stream << "        rst_1 <= rst_i;" << std::endl;
        stream << "        rst <= rst_1;" << std::endl;
        stream << "    end if;" << std::endl;
        stream << "end process;" << std::endl;
        stream << std::endl;
    }

    void ChartToVHDL::writeSpontaneousHandler(std::ostream & stream) {
        // sets spontaneous signal
        stream << "-- spontaneous handler" << std::endl;
        stream << "spontaneous_handler : process (clk, rst) " << std::endl;
        stream << "begin" << std::endl;
        stream << "    if rst = '1' then" << std::endl;
        stream << "        spontaneous_en <= '1';" << std::endl;
        stream << "    elsif rising_edge(clk) then" << std::endl;
        stream << "        if spontaneous_en = '1' then" << std::endl;
        stream << "            spontaneous_en <= optimal_transition_set_combined_sig;" << std::endl;
        stream << "        else" << std::endl;
        //TODO if new event is dequeued then 1 else stay 0       
        stream << "            spontaneous_en <= next_event_dequeued;" << std::endl;
        stream << "        end if;" << std::endl;
        stream << "    end if;" << std::endl;
        stream << "end process;" << std::endl;
        stream << std::endl;
    }

    void ChartToVHDL::writeInternalEventHandler(std::ostream & stream) {
        // Add controler specific stuff here
        stream << "-- event handler" << std::endl;
        stream << "-- pops events and set event signals" << std::endl;
        stream << "event_handler : process (clk, rst) " << std::endl;
        stream << "begin" << std::endl;
        stream << "    if rst = '1' then" << std::endl;

        std::list<TrieNode*> eventNames = _eventTrie.getWordsWithPrefix("");
        for (std::list<TrieNode*>::iterator eventIter = eventNames.begin(); eventIter != eventNames.end(); eventIter++) {
            stream << "        event_" << eventNameEscape((*eventIter)->value) << "_sig <= '0';" << std::endl;
        }

        stream << "        next_event_dequeued <= '0';" << std::endl;

        stream << "    elsif rising_edge(clk) then" << std::endl;
        //TODO

        stream << "    end if;" << std::endl;
        stream << "end process;" << std::endl;
        stream << std::endl;

        stream << "next_event_re <= not int_event_empty and not stall; " << std::endl;
        stream << "next_event <= int_event_output; " << std::endl;
        stream << "int_event_write_en <= next_event_we_i; " << std::endl;
        stream << "int_event_input <= next_event_i; " << std::endl;
        stream << "int_event_read_en <= not spontaneous_en and not stall; " << std::endl;
        stream << std::endl;
    }

    void ChartToVHDL::writeActiveStateNplusOne(std::ostream & stream) {
        stream << "-- active configuration" << std::endl;

        for (size_t i = 0; i < _states.size(); i++) {

            VBranch* tree = (VASSIGN,
                    VLINE("state_next_" + toStr(i) + "_sig"),
                    (VAND,
                    VLINE("in_complete_entry_set_" + toStr(i) + "_sig"),
                    (VOR, VLINE("in_exit_set_" + toStr(i) + "_sig"), (VNOT, VLINE("state_active_" + toStr(i) + "_sig")))));

            tree->print(stream);
            stream << ";" << std::endl;

        }
    }

    void ChartToVHDL::writeOptimalTransitionSetSelection(std::ostream & stream) {
        stream << "-- optimal transition set selection" << std::endl;
        VContainer optimalTransitions = VOR;
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

            VBranch* tree = (VASSIGN,
                    VLINE("in_optimal_transition_set_" + ATTR(transition, "postFixOrder") + "_sig"),
                    (VAND,
                    (HAS_ATTR(transition, "event")
                    ? (VNOT, VLINE("spontaneous_en"))
                    : (VNOP, VLINE("spontaneous_en"))),
                    VLINE("state_active_" + ATTR(transition, "source") + "_sig"),
                    nameMatchers,
                    (VNOT, conflicters)));

            tree->print(stream);
            stream << ";" << std::endl;

            *optimalTransitions += VLINE("in_optimal_transition_set_" + ATTR(transition, "postFixOrder") + "_sig");
        }

        VBranch* tree = (VASSIGN,
                VLINE("optimal_transition_set_combined_sig"),
                optimalTransitions);

        tree->print(stream);
        stream << ";" << std::endl;
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

            VBranch* tree = (VASSIGN,
                    VLINE("in_exit_set_" + toStr(i) + "_sig"),
                    (VAND,
                    VLINE("state_active_" + toStr(i) + "_sig"),
                    exitsetters));

            tree->print(stream);
            stream << ";" << std::endl;
        }
    }

    void ChartToVHDL::writeEntrySet(std::ostream & stream) {
        stream << "-- entry set selection" << std::endl;

        for (size_t i = 0; i < _states.size(); i++) {

            VBranch* tree = (VASSIGN,
                    VLINE("in_entry_set_" + toStr(i) + "_sig"),
                    (VAND,
                    VLINE("in_complete_entry_set_" + toStr(i) + "_sig"),
                    (VOR, VLINE("state_active_" + toStr(i) + "_sig"), (VNOT, VLINE("in_exit_set_" + toStr(i) + "_sig")))));

            tree->print(stream);
            stream << ";" << std::endl;
        }
    }

    void ChartToVHDL::writeDefaultCompletions(std::ostream & stream) {
        stream << "-- default completion assignments" << std::endl;

        std::map<Element<std::string>, NodeSet<std::string> > completions;
        for (size_t i = 0; i < _states.size(); i++) {
            Element<std::string> state(_states[i]);
            completions[state]; // initialize other completions to 0

            std::string completion = ATTR(state, "completionBools");
            for (size_t j = 0; j < _states.size(); j++) {
                if (completion[j] == '1') {
                    completions[Element<std::string>(_states[j])].push_back(state);
                }
            }
        }

        std::map<Element<std::string>, NodeSet<std::string> >::const_iterator complIter = completions.begin();
        while (complIter != completions.end()) {
            const Element<std::string>& state(complIter->first);
            const NodeSet<std::string>& refs(complIter->second);

            std::string index = ATTR(state, "documentOrder");
            VContainer defaultCompleters = VOR;

            for (size_t i = 0; i < refs.size(); i++) {
                *defaultCompleters += VLINE("in_complete_entry_set_" + toStr(i) + "_sig ");
            }

            VBranch* tree = (VASSIGN,
                    VLINE("default_completion_" + index + "_sig"), defaultCompleters);

            tree->print(stream);
            stream << ";" << std::endl;

            complIter++;
        }


    }

    void ChartToVHDL::writeCompleteEntrySet(std::ostream & stream) {
        stream << "-- complete entry set selection" << std::endl;

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

            VBranch* tree = (VASSIGN,
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
                continue; // TODO: FixMe <scxml> <-- ?
            }

            VContainer tmp1 = VAND;
            if (isCompound(Element<std::string>(_states[strTo<size_t>(parent)]))) {
                *tmp1 += VLINE("default_completion_" + ATTR(state, "documentOrder") + "_sig");

                for (size_t j = 0; j < _states.size(); j++) {
                    if (children[j] != '1')
                        continue;
                    *tmp1 += (VAND,
                            (VNOT,
                            (VAND,
                            VLINE("state_active" + toStr(j) + "_sig"),
                            (VNOT,
                            VLINE("in_exit_set_" + toStr(j) + "_sig")))));

                }

            }

            if (isParallel(Element<std::string>(_states[strTo<size_t>(parent)]))) {
                *tmp1 += VLINE("in_complete_entry_set_" + toStr(parent) + "_sig");
            }

            VBranch* tree = (VASSIGN,
                    VLINE("in_complete_entry_set_" + toStr(i) + "_sig"),
                    (VOR,
                    VLINE("in_complete_entry_set_up_" + ATTR(state, "documentOrder") + "_sig"),
                    tmp1));

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

    void ChartToVHDL::writeStateHandler(std::ostream & stream) {
        // updater for current state
        stream << "-- State Handler" << std::endl;
        stream << "-- updates current state" << std::endl;
        stream << "state_proc: process(clk, rst, stall)" << std::endl;
        stream << "begin" << std::endl;
        stream << "    if rst = '1' then" << std::endl;

        for (size_t i = 0; i < _states.size(); i++) {
            Element<std::string> state(_states[i]);
            stream << "        state_active_" << toStr(i) << "_sig <= " << "'0';" << std::endl;
        }

        stream << "        in_complete_entry_set_0_sig <= '1';" << std::endl;
        stream << "    elsif (rising_edge(clk) and stall = '0') then" << std::endl;
        stream << "        in_complete_entry_set_0_sig <= '0';" << std::endl;

        for (size_t i = 0; i < _states.size(); i++) {
            Element<std::string> state(_states[i]);
            stream << "        state_active_" << toStr(i) << "_sig <= " << "state_next_" << toStr(i) << "_sig;" << std::endl;
        }

        stream << "    end if;" << std::endl;
        stream << "end process;" << std::endl;
        stream << std::endl;
    }

    void ChartToVHDL::writeSystemSignalMapping(std::ostream & stream) {
        stream << "-- system signals" << std::endl;
        NodeSet<std::string> topLevelFinal = DOMUtils::filterChildElements(_nsInfo.xmlNSPrefix + "final", _scxml);

        VContainer tlf = VOR;
        for (size_t i = 0; i < topLevelFinal.size(); i++) {
            Element<std::string> final(topLevelFinal[i]);
            *tlf += VLINE("state_active_" + ATTR(final, "documentOrder") + "_sig");

        }

        VBranch* tree = (VASSIGN,
                VLINE("completed_sig"),
                tlf);

        tree->print(stream);
        stream << ";" << std::endl;

        // tmp mapping for events
        stream << "stall <= not en or completed_sig or ( int_event_empty and not spontaneous_en ) ; " << std::endl;
        stream << std::endl;

        // interface signals
        stream << "-- interface signals" << std::endl;
        for (size_t i = 0; i < _states.size(); i++) {
            Element<std::string> state(_states[i]);
            stream << "state_active_" << ATTR(state, "documentOrder")
                    << "_o <= state_active_" << ATTR(state, "documentOrder")
                    << "_sig;" << std::endl;
            // TODO if has ex content
            stream << "entry_set_" << ATTR(state, "documentOrder")
                    << "_o <= in_exit_set_" << ATTR(state, "documentOrder")
                    << "_sig;" << std::endl;
            // TODO if has ex content
            stream << "exit_set_" << ATTR(state, "documentOrder")
                    << "_o <= in_entry_set_" << ATTR(state, "documentOrder")
                    << "_sig;" << std::endl;
        }

        for (size_t i = 0; i < _transitions.size(); i++) {
            Element<std::string> transition(_transitions[i]);
            //TODO if has ex content
            stream << "transition_set_" << ATTR(transition, "postFixOrder")
                    << "_o <= in_optimal_transition_set_" << ATTR(transition, "postFixOrder") //TODO I think optimal transition set is wrong ... ?
                    << "_sig;" << std::endl;
        }

        stream << "completed_o <= completed_sig; " << std::endl;
        stream << "error_o <= reg_error_out; " << std::endl;
        stream << std::endl;
    }

}