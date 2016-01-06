/**
 *  @file
 *  @author     2012-2013 Stefan Radomski (stefan.radomski@cs.tu-darmstadt.de)
 *  @copyright  Simplified BSD
 *
 *  @cond
 *  This program is free software: you can redistribute it and/or modify
 *  it under the terms of the FreeBSD license as published by the FreeBSD
 *  project.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 *
 *  You should have received a copy of the FreeBSD license along with this
 *  program. If not, see <http://www.opensource.org/licenses/bsd-license>.
 *  @endcond
 */

#ifndef V8DATAMODEL_H_KN8TWG0V
#define V8DATAMODEL_H_KN8TWG0V

#include "uscxml/Interpreter.h"
#include <list>
#include <v8.h>
#include "V8DOM.h"

#ifdef BUILD_AS_PLUGINS
#include "uscxml/plugins/Plugins.h"
#endif

namespace uscxml {
class Event;
class Data;
class V8SCXMLDOM;
}

namespace uscxml {

class V8DataModel : public DataModelImpl {
public:
	V8DataModel();
	virtual ~V8DataModel();
	virtual boost::shared_ptr<DataModelImpl> create(InterpreterInfo* interpreter);

	virtual std::list<std::string> getNames() {
		std::list<std::string> names;
		names.push_back("ecmascript");
		return names;
	}

	virtual void initialize();
	virtual void setEvent(const Event& event);

	virtual bool validate(const std::string& location, const std::string& schema);
	virtual bool isLocation(const std::string& expr);
	virtual bool isValidSyntax(const std::string& expr);

	virtual uint32_t getLength(const std::string& expr);
	virtual void setForeach(const std::string& item,
	                        const std::string& array,
	                        const std::string& index,
	                        uint32_t iteration);
	virtual void pushContext();
	virtual void popContext();

	virtual bool supportsJSON() {
		return true;
	}

	virtual void eval(const Arabica::DOM::Element<std::string>& scriptElem,
	                  const std::string& expr);
	virtual void assign(const Arabica::DOM::Element<std::string>& assignElem,
	                    const Arabica::DOM::Node<std::string>& node,
	                    const std::string& content);
	virtual void assign(const std::string& location,
	                    const Data& data);

	virtual void init(const Arabica::DOM::Element<std::string>& dataElem,
	                  const Arabica::DOM::Node<std::string>& node,
	                  const std::string& content);
	virtual void init(const std::string& location,
	                  const Data& data);

	virtual std::string andExpressions(std::list<std::string>);

	virtual Data getStringAsData(const std::string& content);
	virtual Data getValueAsData(const v8::Handle<v8::Value>& value,
	                            std::set<v8::Value*>& alreadySeen);
	virtual Data getValueAsData(const v8::Handle<v8::Value>& value);

	virtual bool isDeclared(const std::string& expr);

	virtual std::string evalAsString(const std::string& expr);
	virtual bool evalAsBool(const Arabica::DOM::Element<std::string>& node, const std::string& expr);
	virtual bool evalAsBool(const std::string& expr);
	virtual double evalAsNumber(const std::string& expr);

	virtual void addExtension(DataModelExtension* ext);

	static v8::Handle<v8::Value> jsExtension(const v8::Arguments& args);
	static v8::Handle<v8::Value> jsIn(const v8::Arguments& args);
	static v8::Handle<v8::Value> jsPrint(const v8::Arguments& args);

protected:
	std::list<v8::Persistent<v8::Context> > _contexts;

	Arabica::DOM::V8DOM* _dom;

	bool _ioProcessorsAreSet;
	bool _invokersAreSet;
	v8::Persistent<v8::Object> _ioProcessors;
	v8::Persistent<v8::Object> _invokers;
	static v8::Handle<v8::Value> getIOProcessors(v8::Local<v8::String> property, const v8::AccessorInfo& info);
	static v8::Handle<v8::Value> getInvokers(v8::Local<v8::String> property, const v8::AccessorInfo& info);
	static v8::Handle<v8::Value> getAttribute(v8::Local<v8::String> property, const v8::AccessorInfo& info);
	static void setWithException(v8::Local<v8::String> property, v8::Local<v8::Value> value, const v8::AccessorInfo& info);

	v8::Handle<v8::Value> evalAsValue(const std::string& expr, bool dontThrow = false);
	v8::Handle<v8::Value> getDataAsValue(const Data& data);
	v8::Handle<v8::Value> getNodeAsValue(const Arabica::DOM::Node<std::string>& node);
	void throwExceptionEvent(const v8::TryCatch& tryCatch);

	std::set<DataModelExtension*> _extensions;
};

#ifdef BUILD_AS_PLUGINS
PLUMA_INHERIT_PROVIDER(V8DataModel, DataModelImpl);
#endif

}

#endif /* end of include guard: V8DATAMODEL_H_KN8TWG0V */
