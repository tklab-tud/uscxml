#ifndef V8DATAMODEL_H_KN8TWG0V
#define V8DATAMODEL_H_KN8TWG0V

#include "uscxml/Interpreter.h"
#include <list>
#include <v8.h>

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
	virtual DataModelImpl* create(Interpreter* interpreter);

	virtual std::set<std::string> getNames() {
		std::set<std::string> names;
		names.insert("ecmascript");
		return names;
	}

	virtual void initialize();
	virtual void setSessionId(const std::string& sessionId);
	virtual void setName(const std::string& name);
	virtual void setEvent(const Event& event);

	virtual void registerIOProcessor(const std::string& name, const IOProcessor& ioprocessor);

	virtual bool validate(const std::string& location, const std::string& schema);

	virtual uint32_t getLength(const std::string& expr);
	virtual void pushContext();
	virtual void popContext();

	virtual void eval(const std::string& expr);
	virtual void assign(const std::string& location, const std::string& expr);
	virtual void assign(const std::string& location, const Data& data);

	virtual Data getStringAsData(const std::string& content);
	virtual Data getValueAsData(const v8::Handle<v8::Value>& value);

	virtual std::string evalAsString(const std::string& expr);
	virtual bool evalAsBool(const std::string& expr);

	static v8::Handle<v8::Value> jsGetEventName(v8::Local<v8::String> property,
	        const v8::AccessorInfo &info);
	static v8::Handle<v8::Value> jsGetEventType(v8::Local<v8::String> property,
	        const v8::AccessorInfo &info);
	static v8::Handle<v8::Value> jsGetEventSendId(v8::Local<v8::String> property,
	        const v8::AccessorInfo &info);
	static v8::Handle<v8::Value> jsGetEventOrigin(v8::Local<v8::String> property,
	        const v8::AccessorInfo &info);
	static v8::Handle<v8::Value> jsGetEventOriginType(v8::Local<v8::String> property,
	        const v8::AccessorInfo &info);
	static v8::Handle<v8::Value> jsGetEventInvokeId(v8::Local<v8::String> property,
	        const v8::AccessorInfo &info);

	static v8::Handle<v8::Value> jsIn(const v8::Arguments& args);
	static v8::Handle<v8::Value> jsPrint(const v8::Arguments& args);


protected:
	std::list<v8::Persistent<v8::Context> > _contexts;
	Interpreter* _interpreter;

	std::string _sessionId;
	std::string _name;

	Event _event;
	v8::Persistent<v8::ObjectTemplate> _globalTemplate;
	v8::Persistent<v8::ObjectTemplate> _eventTemplate;

	v8::Handle<v8::Value> evalAsValue(const std::string& expr);
	virtual v8::Handle<v8::Value> getDataAsValue(const Data& data);

};

#ifdef BUILD_AS_PLUGINS
PLUMA_INHERIT_PROVIDER(V8DataModel, DataModel);
#endif

}

#endif /* end of include guard: V8DATAMODEL_H_KN8TWG0V */
