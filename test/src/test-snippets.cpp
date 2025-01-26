/**
 * This file contains all the snippets in the doxygen documentation.
 *
 * It is not actually a test as such, but makes sure that the snippets will
 * actually compile and do what we claim they do.
 */

#include "uscxml/config.h"
#include "uscxml/Interpreter.h"
#include "uscxml/interpreter/LoggingImpl.h"

#include <iostream>

using namespace uscxml;

void microstep_snippet() {

	Interpreter scxml = Interpreter::fromURL("https://raw.githubusercontent.com/tklab-tud/uscxml/master/test/w3c/null/test436.scxml");

//! [Performing a microstep]
	InterpreterState state = uscxml::USCXML_UNDEF;
	while((state = scxml.step()) != uscxml::USCXML_FINISHED) {
		switch (state) {
		case USCXML_MICROSTEPPED:
		case USCXML_MACROSTEPPED:
			/* Interpreter performed a microstep */
			break;
		default:
			break;
		}
	}
//! [Performing a microstep]

}

void lambda_snippet() {
	InterpreterState state = uscxml::USCXML_UNDEF;
	Interpreter scxml = Interpreter::fromURL("https://raw.githubusercontent.com/tklab-tud/uscxml/master/test/w3c/null/test436.scxml");

	scxml.on().enterState([](const std::string& sessionId,
	                         const std::string& stateName,
	const XERCESC_NS::DOMElement* state) {
		std::cout << "Entered " << stateName << std::endl;
	});

	scxml.on().exitState([](const std::string& sessionId,
	                        const std::string& stateName,
	const XERCESC_NS::DOMElement* state) {
		std::cout << "Exited " << stateName << std::endl;
	});


	while((state = scxml.step()) != uscxml::USCXML_FINISHED) {}

}

int main(int argc, char** argv) {
	try {
		lambda_snippet();
		microstep_snippet();
	} catch (...) {
		exit(EXIT_FAILURE);
	}
}
