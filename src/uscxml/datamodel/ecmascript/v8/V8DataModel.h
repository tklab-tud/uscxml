#ifndef V8DATAMODEL_H_KN8TWG0V
#define V8DATAMODEL_H_KN8TWG0V

#include "uscxml/Interpreter.h"
#include <list>
#include <v8.h>

namespace uscxml {
  class Event;
  class Data;
  class V8SCXMLDOM;
}

namespace uscxml {

class V8DataModel : public DataModel {
public:
  V8DataModel();
  virtual ~V8DataModel();
  virtual DataModel* create(Interpreter* interpreter);
  
  virtual void initialize();
  virtual void setSessionId(const std::string& sessionId);
  virtual void setName(const std::string& name);
  virtual void setEvent(const Event& event);

  virtual bool validate(const std::string& location, const std::string& schema);

  virtual uint32_t getLength(const std::string& expr);
  virtual void pushContext();
  virtual void popContext();

  virtual void eval(const std::string& expr);
  virtual void assign(const std::string& location, const std::string& expr);
  virtual void assign(const std::string& location, const Data& data);

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


protected:
  std::list<v8::Persistent<v8::Context> > _contexts;
  Interpreter* _interpreter;

	std::string _sessionId;
	std::string _name;
  
  V8SCXMLDOM* _dom;
  
  Event _event;
  v8::Persistent<v8::ObjectTemplate> _globalTemplate;
  v8::Persistent<v8::ObjectTemplate> _eventTemplate;

  v8::Handle<v8::Value> evalAsValue(const std::string& expr);
  virtual v8::Handle<v8::Value> getDataAsValue(const Data& data);

};

}

#endif /* end of include guard: V8DATAMODEL_H_KN8TWG0V */
