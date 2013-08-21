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
	virtual boost::shared_ptr<DataModelImpl> create(InterpreterImpl* interpreter);

	virtual std::set<std::string> getNames() {
		std::set<std::string> names;
		names.insert("ecmascript");
		return names;
	}

	virtual void initialize();
	virtual void setEvent(const Event& event);

	virtual bool validate(const std::string& location, const std::string& schema);

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
	                    const Arabica::DOM::Document<std::string>& doc,
	                    const std::string& content);
	virtual void assign(const std::string& location,
	                    const Data& data);

	virtual void init(const Arabica::DOM::Element<std::string>& dataElem,
	                  const Arabica::DOM::Document<std::string>& doc,
	                  const std::string& content);
	virtual void init(const std::string& location,
	                  const Data& data);

	virtual Data getStringAsData(const std::string& content);
	virtual Data getValueAsData(const v8::Handle<v8::Value>& value,
	                            std::set<v8::Value*>& alreadySeen);
	virtual Data getValueAsData(const v8::Handle<v8::Value>& value);

	virtual bool isDeclared(const std::string& expr);

	virtual std::string evalAsString(const std::string& expr);
	virtual bool evalAsBool(const std::string& expr);
	virtual double evalAsNumber(const std::string& expr);

	static v8::Handle<v8::Value> jsIn(const v8::Arguments& args);
	static v8::Handle<v8::Value> jsPrint(const v8::Arguments& args);

protected:
	std::list<v8::Persistent<v8::Context> > _contexts;

	Arabica::DOM::V8DOM* _dom;

	v8::Persistent<v8::Object> _ioProcessors;
	static v8::Handle<v8::Value> getIOProcessors(v8::Local<v8::String> property, const v8::AccessorInfo& info);
	static v8::Handle<v8::Value> getAttribute(v8::Local<v8::String> property, const v8::AccessorInfo& info);
	static void setWithException(v8::Local<v8::String> property, v8::Local<v8::Value> value, const v8::AccessorInfo& info);

	v8::Handle<v8::Value> evalAsValue(const std::string& expr, bool dontThrow = false);
	v8::Handle<v8::Value> getDataAsValue(const Data& data);
	v8::Handle<v8::Value> getDocumentAsValue(const Arabica::DOM::Document<std::string>& doc);
	void throwExceptionEvent(const v8::TryCatch& tryCatch);

};

#ifdef BUILD_AS_PLUGINS
PLUMA_INHERIT_PROVIDER(V8DataModel, DataModelImpl);
#endif

}

#endif /* end of include guard: V8DATAMODEL_H_KN8TWG0V */
