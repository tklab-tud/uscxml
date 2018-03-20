#include <iostream>
#include "uscxml/uscxml.h"

int main(int argc, char *argv[])
{
	std::string scxmlURL("https://raw.githubusercontent.com/tklab-tud/uscxml/master/test/w3c/null/test436.scxml");

	uscxml::Interpreter sc = uscxml::Interpreter::fromURL(scxmlURL);
	uscxml::InterpreterState state;

    sc.on().enterState([](const std::string& sessionId,
                          const std::string& stateName,
                          const xercesc_3_1::DOMElement* state) {
        std::cout << "Entered " << stateName << std::endl;
    });

    sc.on().exitState([](const std::string& sessionId,
                         const std::string& stateName,
                         const xercesc_3_1::DOMElement* state) {
        std::cout << "Exited " << stateName << std::endl;
    });

    sc.on().transition([](const std::string& sessionId,
                          const std::string& targetList,
                          const xercesc_3_1::DOMElement* transition) {
        std::cout << "Transition to " << targetList << std::endl;
    });

    sc.on().completion([](const std::string& sessionId){
        std::cout << "Completed!" << std::endl;
    });
    
    sc.on().executeContent([](const std::string& sessionId,
                              const xercesc_3_1::DOMElement* element){
        std::cout << "Executing content" << std::endl;

    });
    
	while ((state = sc.step()) != uscxml::USCXML_FINISHED) {
	}

	return 0;
}
