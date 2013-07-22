#ifndef NAMESPACINGPARSER_H_1S91TNPM
#define NAMESPACINGPARSER_H_1S91TNPM

#include <DOM/SAX2DOM/SAX2DOM.hpp>
#include <SAX/helpers/CatchErrorHandler.hpp>

namespace uscxml {

class ScriptEntityResolver : public Arabica::SAX::EntityResolver<std::string> {
	virtual InputSourceT resolveEntity(const std::string& publicId, const std::string& systemId) {
		Arabica::SAX::InputSource<std::string> is;
		return is;
	}
};
	
class NameSpacingParser : public Arabica::SAX2DOM::Parser<std::string> {
public:
	NameSpacingParser();
	static NameSpacingParser fromXML(const std::string& xml);
	static NameSpacingParser fromInputSource(Arabica::SAX::InputSource<std::string>& source);

	void startPrefixMapping(const std::string& prefix, const std::string& uri);

	std::map<std::string, std::string> nameSpace;

	virtual bool errorsReported() {
		return _errorHandler.errorsReported();
	}

	virtual const std::string& errors() {
		return _errorHandler.errors();
	}

private:
	Arabica::SAX::CatchErrorHandler<std::string> _errorHandler;
	NameSpacingParser(const NameSpacingParser& other) {}
};

}

#endif /* end of include guard: NAMESPACINGPARSER_H_1S91TNPM */
