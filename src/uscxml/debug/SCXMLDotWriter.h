#ifndef SCXMLDOTWRITER_H_AOP0OHXX
#define SCXMLDOTWRITER_H_AOP0OHXX

#include <DOM/Document.hpp>
#include <fstream>
#include <set>

namespace uscxml {

class Interpreter;

class SCXMLDotWriter {
public:

	struct ElemDetails {
		std::string name;
		std::string details;
		std::string content;
	};

	SCXMLDotWriter(Interpreter* interpreter);
	~SCXMLDotWriter();

	static void toDot(const std::string& filename, Interpreter* interpreter);
	void writeSCXMLElement(std::ostream& os, const Arabica::DOM::Element<std::string>& elem);
	void writeStateElement(std::ostream& os, const Arabica::DOM::Element<std::string>& elem);
	void writeTransitionElement(std::ostream& os, const Arabica::DOM::Element<std::string>& elem);

	std::string getDetailedLabel(const Arabica::DOM::Element<std::string>& elem, int indentation = 0);
	std::string colorForIndent(int indent);

	std::string idForNode(const Arabica::DOM::Node<std::string>& node);
	std::string nameForNode(const Arabica::DOM::Node<std::string>& node);

	static std::string getPrefix();
	static std::string dotEscape(const std::string& text);

	Interpreter* _interpreter;
	std::set<std::string> _knownIds;
	static int _indentation;
};

}

#endif /* end of include guard: SCXMLDOTWRITER_H_AOP0OHXX */
