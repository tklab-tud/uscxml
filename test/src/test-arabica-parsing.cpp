#include <iostream>

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

    int age2;
    std::cin >> age2;

    {
        Arabica::SAX2DOM::Parser<std::string> domParser;
        Arabica::SAX::CatchErrorHandler<std::string> errorHandler;
        domParser.setErrorHandler(errorHandler);

        for (int j=0; j<1; j++) {
        {
            std::stringstream* ss = new std::stringstream();
            (*ss) << "<root>\n<![CDATA[\n< \" ' < > &\n]]>\n</root>";
            // we need an auto_ptr for arabica to assume ownership
            std::auto_ptr<std::istream> ssPtr(ss);
            Arabica::SAX::InputSource<std::string> inputSource(ssPtr);
            std::cout << "Encoding is " << inputSource.getEncoding();

            if(!domParser.parse(inputSource)) {
                std::cout << errorHandler.errors();
                return -1;
            }
            std::cout << domParser.getDocument().getDocumentElement().getFirstChild().getNodeValue() << std::endl;
            std::cout << domParser.getDocument() << std::endl;
        }
        {
            Arabica::SAX::InputSource<std::string> inputSource;
            std::cout << "Encoding is " << inputSource.getEncoding();
            inputSource.setSystemId("/home/sunkiss/_Projects/uscxml/autoware_tim_test.scxml.xml");
            inputSource.setEncoding("UTF-8");

            if(!domParser.parse(inputSource)) {
                std::cout << errorHandler.errors();
                return -1;
            }
            std::cout << domParser.getDocument() << std::endl;
        }
        }
    }

    int age;
    std::cin >> age;
}
