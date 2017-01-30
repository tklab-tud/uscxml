/**
 * This file contains all the snippets in the doxygen documentation.
 *
 * It is not actually a test as such, but makes sure that the snippets will
 * actually compile and do what we claim they do.
 */
//#define protected public

#include "uscxml/config.h"
#include "uscxml/Common.h"
#include "uscxml/Interpreter.h"
#include "uscxml/interpreter/InterpreterImpl.h"
#include "uscxml/util/DOM.h"

#include <iostream>

using namespace uscxml;
using namespace XERCESC_NS;

void testDOMUtils() {

	const char* xml =
	    "<scxml>"
	    "   <state doc=\"1\" post=\"1\">"
	    "		<transition doc=\"1\" post=\"1\" />"
	    "   </state>"
	    "   <state doc=\"2\" post=\"3\">"
	    "		<transition doc=\"2\" post=\"3\" />"
	    "       <state doc=\"3\" post=\"2\">"
	    "           <transition doc=\"2\" post=\"2\" />"
	    "       </state>"
	    "   </state>"
	    "   <final id=\"done\" />"
	    "</scxml>";

	size_t index = 1;

	Interpreter interpreter = Interpreter::fromXML(xml, "");
	interpreter.step();
	XERCESC_NS::DOMElement* scxml = interpreter.getImpl()->getDocument()->getDocumentElement();

	{
		// postfix
		std::list<DOMElement*> result;
		DOMUtils::filterElementGeneric({ "state" }, result, scxml, DOMUtils::POSTFIX, true, true);
		index = 1;
		for (auto trans : result) {
			assert(HAS_ATTR(trans, "post"));
			std::cout << "post: " << ATTR(trans, "post") << std::endl;
			assert(ATTR(trans, "post") == toStr(index));
			index++;
		}
	}

	{
		// document
		std::list<DOMElement*> result;
		DOMUtils::filterElementGeneric({ "state" }, result, scxml, DOMUtils::DOCUMENT, true, true);
		index = 1;
		for (auto trans : result) {
			assert(HAS_ATTR(trans, "doc"));
			std::cout << "doc: " << ATTR(trans, "doc") << std::endl;
			assert(ATTR(trans, "doc") == toStr(index));
			index++;
		}
	}

}

int main(int argc, char** argv) {
	try {
		testDOMUtils();
	} catch (ErrorEvent e) {
		std::cout << e;
	}
}
