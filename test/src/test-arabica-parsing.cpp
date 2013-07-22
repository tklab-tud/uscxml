#include "uscxml/config.h"
#include "uscxml/Common.h"
#include <DOM/Document.hpp>
#include <XPath/XPath.hpp>
#include <DOM/SAX2DOM/SAX2DOM.hpp>
#include <DOM/io/Stream.hpp>
#include <SAX/helpers/CatchErrorHandler.hpp>
#include <DOM/Events/EventTarget.hpp>
#include <DOM/Events/EventListener.hpp>

using namespace Arabica::DOM;

int main(int argc, char** argv) {

	{
		std::stringstream* ss = new std::stringstream();
		(*ss) << "<root>\n<![CDATA[\n< \" ' < > &\n]]>\n</root>";
		// we need an auto_ptr for arabica to assume ownership
		std::auto_ptr<std::istream> ssPtr(ss);
		Arabica::SAX::InputSource<std::string> inputSource(ssPtr);

		Arabica::SAX2DOM::Parser<std::string> domParser;
		Arabica::SAX::CatchErrorHandler<std::string> errorHandler;
		domParser.setErrorHandler(errorHandler);
		
		if(!domParser.parse(inputSource)) {
			std::cout << errorHandler.errors();
			return -1;
		}
		std::cout << domParser.getDocument().getDocumentElement().getFirstChild().getNodeValue() << std::endl;
		std::cout << domParser.getDocument() << std::endl;
	}
	{
		Arabica::SAX::InputSource<std::string> inputSource;
		inputSource.setSystemId("/Users/sradomski/Documents/TK/Code/uscxml/test/samples/uscxml/arabica/test-arabica-parsing.xml");
		
		Arabica::SAX2DOM::Parser<std::string> domParser;
		Arabica::SAX::CatchErrorHandler<std::string> errorHandler;
		domParser.setErrorHandler(errorHandler);
		
		if(!domParser.parse(inputSource)) {
			std::cout << errorHandler.errors();
			return -1;
		}
		std::cout << domParser.getDocument() << std::endl;
	}

}