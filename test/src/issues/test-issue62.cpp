#include "uscxml/Interpreter.h"
#include "glog/logging.h"

using namespace uscxml;

int main(int argc, char** argv) {
    google::LogToStderr();
    google::InitGoogleLogging(argv[0]);
    
    const char* scxmlContent =
    "<scxml datamodel=\"lua\" initial=\"init\" name=\"scxml_root\" version=\"1.0\" xmlns=\"http://www.w3.org/2005/07/scxml\">               "
    "   <state id=\"init\">                                                                                                                 "
    "       <transition target=\"InvokeParent\"/>                                                                                           "
    "   </state>                                                                                                                            "
    "   <final id=\"FinalShape1\"/>                                                                                                         "
    "   <state id=\"InvokeParent\">                                                                                                         "
    "       <invoke autoforward=\"true\" id=\"test_invoke\" type=\"scxml\">                                                                 "
    "           <content>                                                                                                                   "
    "               <scxml datamodel=\"lua\" initial=\"On\" name=\"ScxmlShape1\" version=\"1.0\" xmlns=\"http://www.w3.org/2005/07/scxml\"> "
    "                   <state id=\"On\">                                                                                                   "
    "                       <onentry>                                                                                                       "
    "                           <script>print('TEST LOGGING FROM INVOKE SOURCE')</script>                                                   "
    "                       </onentry>                                                                                                      "
    "                       <transition target=\"Off\"/>                                                                                    "
    "                   </state>                                                                                                            "
    "                   <state id=\"Off\">                                                                                                  "
    "                       <transition event=\"inside_invoke\" target=\"End\"/>                                                            "
    "                   </state>                                                                                                            "
    "                   <final id=\"End\"/>                                                                                                 "
    "               </scxml>                                                                                                                "
    "           </content>                                                                                                                  "
    "       </invoke>                                                                                                                       "
    "       <transition event=\"done.invoke.test_invoke\" target=\"FinalShape1\"/>                                                          "
    "       <transition event=\"move_here\" target=\"StateXXX\"/>                                                                           "
    "   </state>                                                                                                                            "
    "   <state id=\"StateXXX\">                                                                                                             "
    "       <transition target=\"FinalShape1\"/>                                                                                            "
    "   </state>                                                                                                                            "
    "</scxml>                                                                                                                               ";
    
    std::string msg;
    
    uscxml::Interpreter scxml = uscxml::Interpreter(uscxml::Interpreter::fromXML(scxmlContent, ""));
    std::list<InterpreterIssue> issues = scxml.validate();
    for (std::list<InterpreterIssue>::iterator issueIter = issues.begin(); issueIter != issues.end(); issueIter++) {
        std::cout << *issueIter;
    }
    
    scxml.addMonitor(new StateTransitionMonitor());
    
    uscxml::InterpreterState state;
    
    // assume initial stable configuration
    do {
        state = scxml.step();
    } while(state > 0);
    
    scxml.receive(Event("move_here"));
    scxml.receive(Event("inside_invoke"));

    while(state != uscxml::USCXML_FINISHED) {
        do {
            state = scxml.step(true);
        } while(state > 0);
    }
    
    std::cout << "************************************" << std::endl;
    std::cout << "Successfully finished state machine!" << std::endl;
    
    return EXIT_SUCCESS;
    
}