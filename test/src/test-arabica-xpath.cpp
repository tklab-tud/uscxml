#include <iostream>

#include <XPath/XPath.hpp>
#include <DOM/Simple/DOMImplementation.hpp>
#include <DOM/io/Stream.hpp>
#include <iostream>
#include <string>

#include <arabica/Arabica/StringAdaptor.hpp>
#include <arabica/DOM/Node.hpp>
#include <arabica/DOM/NodeList.hpp>
#include <arabica/DOM/Document.hpp>
#include <arabica/DOM/Element.hpp>
#include <arabica/DOM/Attr.hpp>
#include <arabica/XPath/XPath.hpp>
#include <arabica/XPath/impl/xpath_expression.hpp>



#define string_type std::string
#define string_adaptor Arabica::default_string_adaptor<std::string>

typedef string_adaptor SA;

class NodeSetVariableResolver : public Arabica::XPath::VariableResolver<string_type, string_adaptor> {
	//typedef string_adaptorstring_adaptor;
public:
	virtual Arabica::XPath::XPathValue<string_type, string_adaptor> resolveVariable(const string_type& /* namepace_uri */,
	        const string_type& name) const {
		using namespace Arabica::XPath;
		VarMap::const_iterator n = map_.find(name);
		if(n == map_.end())
			throw UnboundVariableException(string_adaptor::asStdString(name));
		return XPathValue<string_type, string_adaptor>(new NodeSetValue<string_type, string_adaptor>((*n).second));
	} // resolveVariable

	void setVariable(const string_type& name, const Arabica::XPath::NodeSet<string_type, string_adaptor>& value) {
		map_[name] = value;
	} // setVariable

private:
	typedef std::map<string_type, Arabica::XPath::NodeSet<string_type, string_adaptor> > VarMap;
	VarMap map_;
}; // class NodeSetVariableResolver

Arabica::XPath::XPath<string_type, string_adaptor> parser;
Arabica::DOM::DOMImplementation<string_type, string_adaptor> factory_;
Arabica::DOM::Document<string_type, string_adaptor> document_;

Arabica::DOM::Element<string_type, string_adaptor> root_;
Arabica::DOM::Element<string_type, string_adaptor> element1_;
Arabica::DOM::Element<string_type, string_adaptor> element2_;
Arabica::DOM::Element<string_type, string_adaptor> element3_;
Arabica::DOM::Element<string_type, string_adaptor> spinkle_;

Arabica::DOM::Attr<string_type, string_adaptor> attr_;
Arabica::DOM::Text<string_type, string_adaptor> text_;
Arabica::DOM::Comment<string_type, string_adaptor> comment_;
Arabica::DOM::ProcessingInstruction<string_type, string_adaptor> processingInstruction_;
Arabica::DOM::Document<string_type, string_adaptor> chapters_;
Arabica::DOM::Document<string_type, string_adaptor> numbers_;

class StringVariableResolver : public Arabica::XPath::VariableResolver<string_type, string_adaptor> {
public:
	virtual Arabica::XPath::XPathValue<string_type, string_adaptor> resolveVariable(const string_type& /* namespace_uri */,
	        const string_type& name) const {
		using namespace Arabica::XPath;
		VarMap::const_iterator n = map_.find(name);
		if(n == map_.end())
			throw UnboundVariableException(string_adaptor::asStdString(name));
		return XPathValue<string_type, string_adaptor>(new StringValue<string_type, string_adaptor>((*n).second));
	} // resolveVariable

	void setVariable(const string_type& name, const string_type& value) {
		map_[name] = value;
	} // setVariable

private:
	typedef std::map<string_type, string_type> VarMap;
	VarMap map_;
}; // StringVariableResolver


int main(int argc, char** argv) {

	factory_ = Arabica::SimpleDOM::DOMImplementation<string_type, string_adaptor>::getDOMImplementation();
	document_ = factory_.createDocument(SA::construct_from_utf8(""), SA::construct_from_utf8(""), 0);
	root_ = document_.createElement("root");
	document_.appendChild(root_);
	assert(root_);

	element1_ = document_.createElement(SA::construct_from_utf8("child1"));
	element2_ = document_.createElement(SA::construct_from_utf8("child2"));
	element3_ = document_.createElement(SA::construct_from_utf8("child3"));

	element1_.setAttribute(SA::construct_from_utf8("one"), SA::construct_from_utf8("1"));

	element2_.setAttribute(SA::construct_from_utf8("one"), SA::construct_from_utf8("1"));
	element2_.setAttribute(SA::construct_from_utf8("two"), SA::construct_from_utf8("1"));
	element2_.setAttribute(SA::construct_from_utf8("three"), SA::construct_from_utf8("1"));
	element2_.setAttribute(SA::construct_from_utf8("four"), SA::construct_from_utf8("1"));

	text_ = document_.createTextNode(SA::construct_from_utf8("data"));
	comment_ = document_.createComment(SA::construct_from_utf8("comment"));
	processingInstruction_ = document_.createProcessingInstruction(SA::construct_from_utf8("target"), SA::construct_from_utf8("data"));
	element2_.appendChild(text_);
	spinkle_ = document_.createElement(SA::construct_from_utf8("spinkle"));
	element2_.appendChild(spinkle_);
	element2_.appendChild(comment_);
	element2_.appendChild(processingInstruction_);

	attr_ = element1_.getAttributeNode(SA::construct_from_utf8("one"));

	root_.appendChild(element1_);
	root_.appendChild(element2_);
	root_.appendChild(element3_);

	chapters_ = factory_.createDocument(SA::construct_from_utf8(""), SA::construct_from_utf8(""), 0);
	chapters_.appendChild(chapters_.createElement(SA::construct_from_utf8("document")));
	chapters_.getFirstChild().appendChild(chapters_.createElement(SA::construct_from_utf8("chapter"))).appendChild(chapters_.createTextNode(SA::construct_from_utf8("one")));
	chapters_.getFirstChild().appendChild(chapters_.createElement(SA::construct_from_utf8("chapter"))).appendChild(chapters_.createTextNode(SA::construct_from_utf8("two")));
	chapters_.getFirstChild().appendChild(chapters_.createElement(SA::construct_from_utf8("chapter"))).appendChild(chapters_.createTextNode(SA::construct_from_utf8("three")));
	chapters_.getFirstChild().appendChild(chapters_.createElement(SA::construct_from_utf8("chapter"))).appendChild(chapters_.createTextNode(SA::construct_from_utf8("four")));
	chapters_.getFirstChild().appendChild(chapters_.createElement(SA::construct_from_utf8("chapter"))).appendChild(chapters_.createTextNode(SA::construct_from_utf8("five")));

	numbers_ = factory_.createDocument(SA::construct_from_utf8(""), SA::construct_from_utf8(""), 0);
	numbers_.appendChild(numbers_.createElement(SA::construct_from_utf8("doc")));
	numbers_.getFirstChild().appendChild(numbers_.createElement(SA::construct_from_utf8("number"))).appendChild(numbers_.createTextNode(SA::construct_from_utf8("1")));
	numbers_.getFirstChild().appendChild(numbers_.createElement(SA::construct_from_utf8("number"))).appendChild(numbers_.createTextNode(SA::construct_from_utf8("2")));
	numbers_.getFirstChild().appendChild(numbers_.createElement(SA::construct_from_utf8("number"))).appendChild(numbers_.createTextNode(SA::construct_from_utf8("3")));
	numbers_.getFirstChild().appendChild(numbers_.createElement(SA::construct_from_utf8("number"))).appendChild(numbers_.createTextNode(SA::construct_from_utf8("4")));
	numbers_.getFirstChild().appendChild(numbers_.createElement(SA::construct_from_utf8("number"))).appendChild(numbers_.createTextNode(SA::construct_from_utf8("5")));
	numbers_.getFirstChild().appendChild(numbers_.createElement(SA::construct_from_utf8("number"))).appendChild(numbers_.createTextNode(SA::construct_from_utf8("6")));
	numbers_.getFirstChild().appendChild(numbers_.createElement(SA::construct_from_utf8("number"))).appendChild(numbers_.createTextNode(SA::construct_from_utf8("7")));
	numbers_.getFirstChild().appendChild(numbers_.createElement(SA::construct_from_utf8("number"))).appendChild(numbers_.createTextNode(SA::construct_from_utf8("8")));
	numbers_.getFirstChild().appendChild(numbers_.createElement(SA::construct_from_utf8("number"))).appendChild(numbers_.createTextNode(SA::construct_from_utf8("9")));
	std::cout << document_ << std::endl;
	std::cout << numbers_ << std::endl;
	std::cout << chapters_ << std::endl;


	if (true) {
		using namespace Arabica::XPath;
		StringVariableResolver svr;
		svr.setVariable(SA::construct_from_utf8("index"), SA::construct_from_utf8("1"));

		parser.setVariableResolver(svr);
		XPathValue<string_type, string_adaptor> result = parser.evaluate(SA::construct_from_utf8("/root/*[@two = $index]"), document_);
		assert(NODE_SET == result.type());
		assert(element2_ == result.asNodeSet()[0]);

		parser.resetVariableResolver();
	} // test18

	if (true) {
		using namespace Arabica::XPath;
		XPathExpression<string_type, string_adaptor> xpath = parser.compile(SA::construct_from_utf8("root/*[position() = 2]"));
		XPathValue<string_type, string_adaptor> result = xpath.evaluate(document_);

		assert(NODE_SET == result.type());
		assert(1 == result.asNodeSet().size());
		Arabica::DOM::Node<string_type, string_adaptor> n = result.asNodeSet()[0];
		assert(element2_ == n);
	} // test19

	if (false) {
		using namespace Arabica::XPath;
		Arabica::DOM::DocumentFragment<string_type, string_adaptor> frag = document_.createDocumentFragment();
		document_.getFirstChild().appendChild(document_.createElement(SA::construct_from_utf8("foo"))).appendChild(document_.createElement(SA::construct_from_utf8("one")));

		std::cout << std::endl << document_ << std::endl << std::endl;

		NodeSetVariableResolver svr;
		NodeSet<string_type, string_adaptor> ns;
		ns.push_back(frag);
		svr.setVariable(SA::construct_from_utf8("fruit"), ns);
		parser.setVariableResolver(svr);

		XPathValue<string_type, string_adaptor> result = parser.evaluate_expr(SA::construct_from_utf8("$fruit/foo"), document_);
		assert(NODE_SET == result.type());
		assert(1 == result.asNodeSet().size());
		std::cout << std::endl << result.asString() << std::endl;
	} // testUnion11

if (true) {
    using namespace Arabica::XPath;
		NodeSetVariableResolver svr;
    NodeSet<string_type, string_adaptor> ns;
    ns.push_back(element1_);
    ns.push_back(element2_);
    ns.push_back(element3_);
    svr.setVariable(SA::construct_from_utf8("fruit"), ns);

    parser.setVariableResolver(svr);
    XPathValue<string_type, string_adaptor> result = parser.evaluate_expr(SA::construct_from_utf8("$fruit"), document_);
    assert(NODE_SET == result.type());
    assert(element1_ == result.asNodeSet()[0]);
    assert(element2_ == result.asNodeSet()[1]);
    assert(element3_ == result.asNodeSet()[2]);
		std::cout << std::endl << result.asString() << std::endl;

  } // testNodeSetVars1

if (true) {
    using namespace Arabica::XPath;
		NodeSetVariableResolver svr;
    NodeSet<string_type, string_adaptor> ns;
    ns.push_back(element1_);
    ns.push_back(element2_);
    ns.push_back(element3_);
    svr.setVariable(SA::construct_from_utf8("fruit"), ns);

    parser.setVariableResolver(svr);
    XPathValue<string_type, string_adaptor> result = parser.evaluate_expr(SA::construct_from_utf8("$fruit/spinkle"), document_);
    assert(NODE_SET == result.type());
    assert(spinkle_ == result.asNodeSet()[0]);
		std::cout << std::endl << result.asString() << std::endl;

  } // testNodeSetVars2

if (true) {
    using namespace Arabica::XPath;
		NodeSetVariableResolver svr;
    NodeSet<string_type, string_adaptor> ns;
    ns.push_back(element1_);
    ns.push_back(element2_);
    ns.push_back(element3_);
    svr.setVariable(SA::construct_from_utf8("fruit"), ns);

    parser.setVariableResolver(svr);
    XPathValue<string_type, string_adaptor> result = parser.evaluate_expr(SA::construct_from_utf8("$fruit[2]/*"), document_);
    assert(NODE_SET == result.type());
    assert(spinkle_ == result.asNodeSet()[0]);
		std::cout << std::endl << result.asString() << std::endl;

  } // testNodeSetVars3










	if (true) {
		using namespace Arabica::XPath;
		XPathValue<string_type, string_adaptor> result = parser.evaluate_expr(SA::construct_from_utf8("local-name(/root)"), document_);
		assert(STRING == result.type());
		assert(SA::construct_from_utf8("root") == result.asString());
	} // testLocalNameFn1

	{
		using namespace Arabica::XPath;
		Arabica::DOM::DocumentFragment<std::string> frag = document_.createDocumentFragment();
		frag.appendChild(document_.createElement("foo"));

		NodeSetVariableResolver svr;
		NodeSet<string_type, string_adaptor> ns;
		ns.push_back(frag);
		svr.setVariable("fruit", ns);
		parser.setVariableResolver(svr);

		XPathValue<string_type, string_adaptor> result = parser.evaluate(SA::construct_from_utf8("local-name($fruit/foo) = 'foo'"), document_);
		std::cout << result.asBool() << std::endl;
	}

}