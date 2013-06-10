#include "NameSpacingParser.h"
#include <glog/logging.h>

namespace uscxml {
	
	NameSpacingParser* NameSpacingParser::fromXML(const std::string& xml) {
		if (xml.length() == 0)
			return NULL;
		std::stringstream* ss = new std::stringstream();
		(*ss) << xml;
		// we need an auto_ptr for arabica to assume ownership
		std::auto_ptr<std::istream> ssPtr(ss);
		Arabica::SAX::InputSource<std::string> inputSource;
		inputSource.setByteStream(ssPtr);
		return fromInputSource(inputSource);
	}

	NameSpacingParser* NameSpacingParser::fromInputSource(Arabica::SAX::InputSource<std::string>& source) {
		NameSpacingParser* parser = new NameSpacingParser();
		if(!parser->parse(source) || !parser->getDocument().hasChildNodes()) {
			if(parser->_errorHandler.errorsReported()) {
				LOG(ERROR) << "could not parse input:";
				LOG(ERROR) << parser->_errorHandler.errors() << std::endl;
			} else {
				Arabica::SAX::InputSourceResolver resolver(source, Arabica::default_string_adaptor<std::string>());
				if (!resolver.resolve()) {
					LOG(ERROR) << source.getSystemId() << ": no such file";
				}
			}
			delete parser;
		}
		return parser;
	}

  NameSpacingParser::NameSpacingParser() {
		Arabica::SAX::CatchErrorHandler<std::string> errorHandler;
		setErrorHandler(errorHandler);
	}
	
	void NameSpacingParser::startPrefixMapping(const std::string& prefix, const std::string& uri) {
		nameSpace.insert(std::make_pair(uri, prefix));
	}

}