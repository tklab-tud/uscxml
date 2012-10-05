#include "uscxml/datamodel/ecmascript/v8/V8DataModel.h"
#include "dom/V8SCXMLDOM.h"
#include "uscxml/Message.h"

namespace uscxml {

V8DataModel::V8DataModel() {
//  _contexts.push_back(v8::Context::New());
}

DataModel* V8DataModel::create(Interpreter* interpreter) {
  V8DataModel* dm = new V8DataModel();
  dm->_interpreter = interpreter;
  v8::Locker locker;
  v8::HandleScope scope;

  // see http://stackoverflow.com/questions/3171418/v8-functiontemplate-class-instance
//  dm->_globalTemplate = v8::Persistent<v8::ObjectTemplate>(v8::ObjectTemplate::New());
//  dm->_globalTemplate->Set(v8::String::New("In"), v8::FunctionTemplate::New(jsIn, v8::External::New(reinterpret_cast<void*>(this))));

  v8::Handle<v8::ObjectTemplate> global = v8::ObjectTemplate::New();
  global->Set(v8::String::New("In"), v8::FunctionTemplate::New(jsIn, v8::External::New(reinterpret_cast<void*>(dm))));

  dm->_dom = new V8SCXMLDOM(interpreter);
  global->Set(v8::String::New("document"), dm->_dom->getDocument());
  
  dm->_contexts.push_back(v8::Context::New(NULL, global));
  dm->setName(interpreter->getName());
  dm->setSessionId(interpreter->getSessionId());
  dm->eval("_ioprocessors = {};");
  
  return dm;
}

void V8DataModel::setSessionId(const std::string& sessionId) {
  _sessionId = sessionId;
  v8::Locker locker;
  v8::HandleScope handleScope;
  v8::Context::Scope contextScope(_contexts.front());
  v8::Handle<v8::Object> global = _contexts.front()->Global();

  global->Set(v8::String::New("_sessionid"), v8::String::New(sessionId.c_str()));
}

void V8DataModel::setName(const std::string& name) {
  _name = name;
  v8::HandleScope handleScope;
  v8::Context::Scope contextScope(_contexts.front());
  v8::Handle<v8::Object> global = _contexts.front()->Global();
  
  global->Set(v8::String::New("_name"), v8::String::New(name.c_str()));
}

V8DataModel::~V8DataModel() {
  while(_contexts.size() > 0) {
    _contexts.back().Dispose();
    _contexts.pop_back();
  }
}

void V8DataModel::pushContext() {
  _contexts.push_back(_contexts.back().New(_contexts.back()));
}

void V8DataModel::popContext() {
  if (_contexts.size() > 1) {
    _contexts.back().Dispose();
    _contexts.pop_back();
  }
}

void V8DataModel::initialize() {
}

void V8DataModel::setEvent(const Event& event) {
  _event = event;
  v8::Locker locker;
  v8::HandleScope handleScope;
  v8::Context::Scope contextScope(_contexts.front());
  v8::Handle<v8::Object> global = _contexts.front()->Global();

  // this is unfortunate - can't we store the template in the object?
  if (_eventTemplate.IsEmpty()) {
    v8::Handle<v8::ObjectTemplate> localEventTemplate = v8::ObjectTemplate::New();
    localEventTemplate->SetInternalFieldCount(1); // we only have a single C++ object
    localEventTemplate->SetAccessor(v8::String::New("name"), V8DataModel::jsGetEventName);
    localEventTemplate->SetAccessor(v8::String::New("type"), V8DataModel::jsGetEventType);
    localEventTemplate->SetAccessor(v8::String::New("sendid"), V8DataModel::jsGetEventSendId);
    localEventTemplate->SetAccessor(v8::String::New("origin"), V8DataModel::jsGetEventOrigin);
    localEventTemplate->SetAccessor(v8::String::New("origintype"), V8DataModel::jsGetEventOriginType);
    localEventTemplate->SetAccessor(v8::String::New("invokeid"), V8DataModel::jsGetEventInvokeId);
    _eventTemplate = v8::Persistent<v8::ObjectTemplate>::New(localEventTemplate);
  }
  
  assert(_eventTemplate->InternalFieldCount() == 1);
  v8::Handle<v8::Object> eventJS = _eventTemplate->NewInstance();
  eventJS->SetInternalField(0, v8::External::New(&_event));

  eventJS->Set(v8::String::New("data"), getDataAsValue(event)); // set data part of _event
  global->Set(v8::String::New("_event"), eventJS);
}

v8::Handle<v8::Value> V8DataModel::getDataAsValue(const Data& data) {
  if (data.compound.size() > 0) {
    v8::Handle<v8::Object> value = v8::Array::New();
    std::map<std::string, Data>::const_iterator compoundIter = data.compound.begin();
    while(compoundIter != data.compound.end()) {
      value->Set(v8::String::New(compoundIter->first.c_str()), getDataAsValue(compoundIter->second));
      compoundIter++;
    }
    return value;
  }
  if (data.array.size() > 0) {
    v8::Handle<v8::Object> value = v8::Array::New();
    std::list<Data>::const_iterator arrayIter = data.array.begin();
    uint32_t index = 0;
    while(arrayIter != data.array.end()) {
      value->Set(index++, getDataAsValue(*arrayIter));
      arrayIter++;
    }
    return value;
  }
  if (data.type == Data::VERBATIM) {
    return v8::String::New(data.atom.c_str());
  } else {
    return evalAsValue(data.atom);
  }
}
  
v8::Handle<v8::Value> V8DataModel::jsIn(const v8::Arguments& args) {
  V8DataModel* THIS = static_cast<V8DataModel*>(v8::External::Unwrap(args.Data()));
  for (unsigned int i = 0; i < args.Length(); i++) {
    if (args[i]->IsString()) {
      std::string stateName(*v8::String::AsciiValue(args[i]->ToString()));
      if (Interpreter::isMember(THIS->_interpreter->getState(stateName), THIS->_interpreter->getConfiguration())) {
        continue;
      }
    }
    return v8::Boolean::New(false);
  }
  return v8::Boolean::New(true);
}

v8::Handle<v8::Value> V8DataModel::jsGetEventName(v8::Local<v8::String> property,
                                                const v8::AccessorInfo &info) {
  Event* event = static_cast<Event*>(v8::Local<v8::External>::Cast(info.Holder()->GetInternalField(0))->Value());
  return v8::String::New(event->name.c_str());
}

v8::Handle<v8::Value> V8DataModel::jsGetEventType(v8::Local<v8::String> property,
                                                const v8::AccessorInfo &info) {
  Event* event = static_cast<Event*>(v8::Local<v8::External>::Cast(info.Holder()->GetInternalField(0))->Value());
  switch (event->type) {
    case Event::PLATFORM:
      return v8::String::New("platform");
      break;
    case Event::INTERNAL:
      return v8::String::New("internal");
      break;
    case Event::EXTERNAL:
      return v8::String::New("external");
      break;
    default:
      return v8::String::New("");
      break;
  }
}

v8::Handle<v8::Value> V8DataModel::jsGetEventSendId(v8::Local<v8::String> property,
                                                  const v8::AccessorInfo &info) {
  Event* event = static_cast<Event*>(v8::Local<v8::External>::Cast(info.Holder()->GetInternalField(0))->Value());
  return v8::String::New(event->sendid.c_str());
  
}

v8::Handle<v8::Value> V8DataModel::jsGetEventOrigin(v8::Local<v8::String> property,
                                                  const v8::AccessorInfo &info) {
  Event* event = static_cast<Event*>(v8::Local<v8::External>::Cast(info.Holder()->GetInternalField(0))->Value());
  return v8::String::New(event->origin.c_str());
}

v8::Handle<v8::Value> V8DataModel::jsGetEventOriginType(v8::Local<v8::String> property,
                                                      const v8::AccessorInfo &info) {
  Event* event = static_cast<Event*>(v8::Local<v8::External>::Cast(info.Holder()->GetInternalField(0))->Value());
  return v8::String::New(event->origintype.c_str());
}

v8::Handle<v8::Value> V8DataModel::jsGetEventInvokeId(v8::Local<v8::String> property,
                                                    const v8::AccessorInfo &info) {
  Event* event = static_cast<Event*>(v8::Local<v8::External>::Cast(info.Holder()->GetInternalField(0))->Value());
  return v8::String::New(event->invokeid.c_str());
}

bool V8DataModel::validate(const std::string& location, const std::string& schema) {
  return true;
}

uint32_t V8DataModel::getLength(const std::string& expr) {
  v8::Locker locker;
  v8::HandleScope handleScope;
  v8::Context::Scope contextScope(_contexts.back());
  v8::Handle<v8::Array> result = evalAsValue(expr).As<v8::Array>();
  return result->Length();
}

void V8DataModel::eval(const std::string& expr) {
  v8::Locker locker;
  v8::HandleScope handleScope;
  v8::Context::Scope contextScope(_contexts.back());
  evalAsValue(expr);
}

bool V8DataModel::evalAsBool(const std::string& expr) {
  v8::Locker locker;
  v8::HandleScope handleScope;
  v8::Context::Scope contextScope(_contexts.back());
  v8::Handle<v8::Value> result = evalAsValue(expr);
  return(result->ToBoolean()->BooleanValue());
}

std::string V8DataModel::evalAsString(const std::string& expr) {
  v8::Locker locker;
  v8::HandleScope handleScope;
  v8::Context::Scope contextScope(_contexts.back());
  v8::Handle<v8::Value> result = evalAsValue(expr);
  v8::String::AsciiValue data(result->ToString());
  return std::string(*data);
}

void V8DataModel::assign(const std::string& location, const Data& data) {
  v8::Locker locker;
  v8::HandleScope handleScope;
  v8::Context::Scope contextScope(_contexts.front());
  
  std::stringstream ssJSON;
  ssJSON << data;
  assign(location, ssJSON.str());
//  v8::Handle<v8::Object> variable = evalAsValue(location).As<v8::Object>();
//  assert(!variable.IsEmpty());
//  if (data.compound.size() > 0) {
//    std::map<std::string, Data>::const_iterator compoundIter = data.compound.begin();
//    while(compoundIter != data.compound.end()) {
//      variable->Set(v8::String::New(compoundIter->first.c_str()), getDataAsValue(compoundIter->second));
//      compoundIter++;
//    }
//    return;
//  } else if (data.array.size() > 0) {
//    std::list<Data>::const_iterator arrayIter = data.array.begin();
//    uint32_t index = 0;
//    while(arrayIter != data.array.end()) {
//      variable->Set(index++, getDataAsValue(*arrayIter));
//      arrayIter++;
//    }
//  } else if (data.type == Data::VERBATIM) {
//    assign(location, "'" + data.atom + "'");
//  } else {
//    assign(location, data.atom);
//  }

}

void V8DataModel::assign(const std::string& location, const std::string& expr) {
  v8::Locker locker;
  v8::HandleScope handleScope;
  v8::Context::Scope contextScope(_contexts.back());
  evalAsValue((location + " = " + expr).c_str());
}

v8::Handle<v8::Value> V8DataModel::evalAsValue(const std::string& expr) {
  v8::TryCatch tryCatch;
  v8::Handle<v8::String> source = v8::String::New(expr.c_str());
  v8::Handle<v8::Script> script = v8::Script::Compile(source);

  v8::Handle<v8::Value> result;
  if (!script.IsEmpty())
    result = script->Run();

  if (script.IsEmpty() || result.IsEmpty()) {
    // throw an exception
    assert(tryCatch.HasCaught());
    Event exceptionEvent;
    exceptionEvent.name = "error.execution";
    
    std::string exceptionString(*v8::String::AsciiValue(tryCatch.Exception()));
    exceptionEvent.compound["exception"] = Data(exceptionString, Data::VERBATIM);;

    v8::Handle<v8::Message> message = tryCatch.Message();
    if (!message.IsEmpty()) {
      std::string filename(*v8::String::AsciiValue(message->GetScriptResourceName()));
      exceptionEvent.compound["filename"] = Data(filename, Data::VERBATIM);

      std::string sourceLine(*v8::String::AsciiValue(message->GetSourceLine()));
      exceptionEvent.compound["sourceline"] = Data(sourceLine, Data::VERBATIM);
      
      std::stringstream ssLineNumber;
      int lineNumber = message->GetLineNumber();
      ssLineNumber << lineNumber;
      exceptionEvent.compound["linenumber"] = Data(ssLineNumber.str());

      int startColumn = message->GetStartColumn();
      int endColumn = message->GetEndColumn();
      std::stringstream ssUnderline;
      for (int i = 0; i < startColumn; i++)
        ssUnderline << " ";
      for (int i = startColumn; i < endColumn; i++)
        ssUnderline << "^";
      exceptionEvent.compound["sourcemark"] = Data(ssUnderline.str(), Data::VERBATIM);
      
      std::string stackTrace(*v8::String::AsciiValue(tryCatch.StackTrace()));
      exceptionEvent.compound["stacktrace"] = Data(stackTrace, Data::VERBATIM);

    }

    _interpreter->receiveInternal(exceptionEvent);
    throw(exceptionEvent);
  }
  
  return result;
}

}