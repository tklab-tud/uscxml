#include "uscxml/Interpreter.h"

#include "glog/logging.h"

using namespace uscxml;

int main(int argc, char** argv) {
    google::LogToStderr();
    google::InitGoogleLogging(argv[0]);
    
    const char* scxmlContent =
    "<scxml datamodel=\"lua\" initial=\"init\" name=\"scxml_root\" version=\"1.0\" xmlns=\"http://www.w3.org/2005/07/scxml\">"
    "   <state id=\"init\">                                                                                                  "
    "       <onentry>  <script>             print('Hello, World!')                  </script>  </onentry>                    "
    "       <onentry>  <script>             print(\"Hello, World!\")                </script>  </onentry>                    "
    "       <onentry>  <script>             print('Hello, &quot;World&quot;')       </script>  </onentry>                    "
    "       <onentry>  <script><![CDATA[    print('Hello, \"World\"')            ]]></script>  </onentry>                    "
    "       <onentry>  <script>             print(&quot;Hello, world!&quot;)        </script>  </onentry>                    "
    "       <transition target=\"FinalShape1\"/>                                                                             "
    "       <transition cond=\"_event.data==&quot;string value&quot;\" event=\"test\" target=\"FinalShape1\"/>               "
    "   </state>                                                                                                             "
    "   <final id=\"FinalShape1\"/>                                                                                          "
    "</scxml>                                                                                                                ";
    
    std::string msg;
    
    uscxml::Interpreter scxml = uscxml::Interpreter(uscxml::Interpreter::fromXML(scxmlContent, ""));
    
    std::list<InterpreterIssue> issues = scxml.validate();
    for (std::list<InterpreterIssue>::iterator issueIter = issues.begin(); issueIter != issues.end(); issueIter++) {
        std::cout << *issueIter << std::endl;
    }

    scxml.addMonitor(new StateTransitionMonitor());
    
    uscxml::InterpreterState state;
    
    do {
        
        state = scxml.step();
    }   while(state != uscxml::USCXML_FINISHED && state != uscxml::USCXML_DESTROYED);
    
    std::cout << "************************************" << std::endl;
    std::cout << "Successfully finished state machine!" << std::endl;
    
    return EXIT_SUCCESS;
    
}