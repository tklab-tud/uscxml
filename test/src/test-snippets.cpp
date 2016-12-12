/**
 * This file contains all the snippets in the doxygen documentation.
 *
 * It is not actually a test as such, but makes sure that the snippets will
 * actually compile and do what we claim they do.
 */

#include "uscxml/config.h"
#include "uscxml/Interpreter.h"
#include "uscxml/interpreter/LoggingImpl.h"

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

int main(int argc, char** argv) {
	Logger::getDefault().log(USCXML_FATAL) << "Foo!" << " BAR?";
	microstep_snippet();
}
