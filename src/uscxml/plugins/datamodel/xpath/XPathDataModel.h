#ifndef XPATHDATAMODEL_H_KN8TWG0V
#define XPATHDATAMODEL_H_KN8TWG0V

#include "uscxml/Interpreter.h"
#include <list>

#ifdef BUILD_AS_PLUGINS
#include "uscxml/plugins/Plugins.h"
#endif

namespace uscxml {
class Event;
class Data;
}

namespace uscxml {

class XPathFunctionIn : public Arabica::XPath::BooleanXPathFunction<std::string> {
public:
	XPathFunctionIn(int minArgs,
	                int maxArgs,
	                const std::vector<Arabica::XPath::XPathExpression<std::string> >& args,
	                InterpreterImpl* interpreter) :
		Arabica::XPath::BooleanXPathFunction<std::string>(minArgs, maxArgs, args),
		_interpreter(interpreter) {}

protected:
	bool doEvaluate(const Arabica::DOM::Node<std::string>& context,
	                const Arabica::XPath::ExecutionContext<std::string>& executionContext) const;
	InterpreterImpl* _interpreter;
};

class XPathFunctionResolver : public Arabica::XPath::FunctionResolver<std::string> {
public:
	virtual ~XPathFunctionResolver() { }

	virtual Arabica::XPath::XPathFunction<std::string>*
	resolveFunction(const std::string& namespace_uri,
	                const std::string& name,
	                const std::vector<Arabica::XPath::XPathExpression<std::string> >& argExprs) const;

	virtual std::vector<std::pair<std::string, std::string> > validNames() const;
	void setInterpreter(InterpreterImpl* interpreter) {
		_interpreter = interpreter;
	}
protected:
	Arabica::XPath::StandardXPathFunctionResolver<std::string> _xpathFuncRes;
	InterpreterImpl* _interpreter;
};

class NodeSetVariableResolver : public Arabica::XPath::VariableResolver<std::string> {
public:
	Arabica::XPath::XPathValue<std::string> resolveVariable(const std::string& namepaceUri,
	        const std::string& name) const;
	void setVariable(const std::string& name, const Arabica::XPath::NodeSet<std::string>& value) {
		_variables[name] = value;
	}
	bool isDeclared(const std::string& name) {
		return _variables.find(name) != _variables.end();
	}
	
private:
	std::map<std::string, Arabica::XPath::NodeSet<std::string> > _variables;
	friend class XPathDataModel;
};

class XPathDataModel : public DataModelImpl {
public:
	XPathDataModel();
	virtual ~XPathDataModel();
	virtual boost::shared_ptr<DataModelImpl> create(InterpreterImpl* interpreter);

	virtual std::set<std::string> getNames() {
		std::set<std::string> names;
		names.insert("xpath");
		return names;
	}

	virtual void initialize();
	virtual void setEvent(const Event& event);

	virtual bool validate(const std::string& location, const std::string& schema);

	virtual uint32_t getLength(const std::string& expr);
	virtual void pushContext();
	virtual void popContext();

	virtual void eval(const std::string& expr);
	virtual void assign(const Arabica::DOM::Element<std::string>& assignElem,
	                    const Arabica::DOM::Document<std::string>& doc,
	                    const std::string& content);
	virtual void assign(const std::string& location, const Data& data);

	virtual void init(const Arabica::DOM::Element<std::string>& dataElem,
	                  const Arabica::DOM::Document<std::string>& doc,
	                  const std::string& content);
	virtual void init(const std::string& location, const Data& data);

	virtual Data getStringAsData(const std::string& content);
	virtual bool isDeclared(const std::string& expr);

	virtual std::string evalAsString(const std::string& expr);
	virtual bool evalAsBool(const std::string& expr);
	virtual double evalAsNumber(const std::string& expr);

protected:
	Arabica::XPath::XPath<std::string> _xpath;
	Arabica::DOM::DOMImplementation<std::string> _domFactory;
	Arabica::DOM::Element<std::string> _datamodel;
	Arabica::DOM::Document<std::string> _doc;

	// resolve value to its type
	void assign(const Arabica::XPath::XPathValue<std::string>& key,
	            const Arabica::XPath::XPathValue<std::string>& value,
	            const Arabica::DOM::Element<std::string>& assignElem);
	void assign(const Arabica::XPath::XPathValue<std::string>& key,
	            const Arabica::XPath::NodeSet<std::string>& value,
	            const Arabica::DOM::Element<std::string>& assignElem);
	
	// assign value to a nodeset key
	void assign(const Arabica::XPath::NodeSet<std::string>& key,
	            const std::string& value,
	            const Arabica::DOM::Element<std::string>& assignElem);
	void assign(const Arabica::XPath::NodeSet<std::string>& key,
	            const double value,
	            const Arabica::DOM::Element<std::string>& assignElem);
	void assign(const Arabica::XPath::NodeSet<std::string>& key,
	            const bool value,
	            const Arabica::DOM::Element<std::string>& assignElem);
	void assign(const Arabica::XPath::NodeSet<std::string>& key,
	            const Arabica::XPath::NodeSet<std::string>& value,
	            const Arabica::DOM::Element<std::string>& assignElem);
	
	// assign value to an element key (from nodeset)
	void assign(const Arabica::DOM::Element<std::string>& key,
	            const Arabica::XPath::NodeSet<std::string>& value,
	            const Arabica::DOM::Element<std::string>& assignElem);

	NodeSetVariableResolver _varResolver;
	XPathFunctionResolver _funcResolver;

};

#ifdef BUILD_AS_PLUGINS
PLUMA_INHERIT_PROVIDER(XPathDataModel, DataModelImpl);
#endif

}

#endif /* end of include guard: XPATHDATAMODEL_H_KN8TWG0V */
