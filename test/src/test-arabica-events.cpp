#include "uscxml/config.h"
#include "uscxml/Common.h"
#include <DOM/Document.hpp>
#include <XPath/XPath.hpp>
#include <DOM/SAX2DOM/SAX2DOM.hpp>
#include <SAX/helpers/CatchErrorHandler.hpp>
#include <DOM/Events/EventTarget.hpp>
#include <DOM/Events/EventListener.hpp>

using namespace Arabica::DOM;

class CapturingEventListener : public Events::EventListener<std::string> {
public:
	void handleEvent(Events::Event<std::string>& event) {
		std::cout << "Handling captured event " << event.getType() << std::endl;
	}
};

class BubblingEventListener : public Events::EventListener<std::string> {
public:
	void handleEvent(Events::Event<std::string>& event) {
		std::cout << "Handling bubbling event " << event.getType() << std::endl;
	}
};

int main(int argc, char** argv) {
	if (argc != 2) {
		std::cerr << "Expected path to test-arabica-events.xml" << std::endl;
		exit(EXIT_FAILURE);
	}

	Arabica::SAX::InputSource<std::string> inputSource(argv[1]);

	Arabica::SAX2DOM::Parser<std::string> domParser;
	Arabica::SAX::CatchErrorHandler<std::string> errorHandler;
	domParser.setErrorHandler(errorHandler);
	if(!domParser.parse(inputSource)) {
		return -1;
	}
	Document<std::string> doc = domParser.getDocument();
	Element<std::string> elem = doc.getDocumentElement();

	CapturingEventListener cel;
	BubblingEventListener bel;

	Events::EventTarget<std::string> eventTarget(elem);
	eventTarget.addEventListener("DOMNodeInserted", cel, true);
	eventTarget.addEventListener("DOMNodeInserted", bel, false);
	eventTarget.addEventListener("DOMNodeRemoved", cel, true);
	eventTarget.addEventListener("DOMNodeRemoved", bel, false);
	eventTarget.addEventListener("DOMAttrModified", cel, true);
	eventTarget.addEventListener("DOMAttrModified", bel, false);

	Arabica::XPath::XPath<std::string> xpath;
	Arabica::XPath::NodeSet<std::string> divs = xpath.evaluate("//div", doc).asNodeSet();

	for (int i = 0; i < divs.size(); i++) {
		Element<std::string> divElem = Element<std::string>(divs[i]);
		divElem.setAttribute("foo", "true");
		divElem.setAttribute("foo", "false");

		Element<std::string> fooElem = divElem.getOwnerDocument().createElement("foo");
		divElem.appendChild(fooElem);
		divElem.removeChild(fooElem);
	}


}