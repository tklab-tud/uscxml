#include "uscxml/Interpreter.h"

using namespace uscxml;

// -- Issue 56 on github
int main(int argc, char** argv) {
    std::deque<std::string> messageQueue;
    messageQueue.push_back("a");
    messageQueue.push_back("b");
    messageQueue.push_back("c");
    messageQueue.push_back("d");
    
    const char* scxmlContent =
    "<?xml version=\"1.0\" encoding=\"UTF-8\"?>"
    "<scxml xmlns=\"http://www.w3.org/2005/07/scxml\" version=\"1.0\" initial=\"initial_state\">"
    "    <state id=\"initial_state\">"
    "        <transition event=\"a\" target=\"parallel_state\"/>"
    "    </state>"
    "    <parallel id=\"parallel_state\">"
    "        <transition event=\"done.state.parallel_state\" target=\"join_state\"/>"
    "        <state id=\"p1out\" initial=\"p1\">"
    "            <state id=\"p1\">"
    "                <transition event=\"b\" target=\"p11\"/>"
    "            </state>"
    "            <final id=\"p11\"/>"
    "        </state>"
    "        <state id=\"p2out\" initial=\"p2\">"
    "            <state id=\"p2\">"
    "                <transition event=\"c\" target=\"p21\"/>"
    "            </state>"
    "            <final id=\"p21\"/>"
    "        </state>"
    "    </parallel>"
    "    <state id=\"join_state\">"
    "        <transition event=\"d\" target=\"final_state\"/>"
    "    </state>"
    "    <final id=\"final_state\"/>"
    "</scxml>";
    
    std::string msg;

    uscxml::Interpreter scxml = uscxml::Interpreter::fromXML(scxmlContent, "");
    scxml.addMonitor(new StateTransitionMonitor());
    
    uscxml::InterpreterState state;
    // assume initial stable configuration
    do { state = scxml.step(); } while(state > 0);

    while(state != uscxml::USCXML_FINISHED && !messageQueue.empty())
    {
        msg = messageQueue.front();
        messageQueue.pop_front();
        
        scxml.receive(uscxml::Event(msg, uscxml::Event::EXTERNAL));

        // step to next stable configuration
        do { state = scxml.step(); } while(state > 0);

    }
    
    return EXIT_SUCCESS;

}