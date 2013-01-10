#ifndef V8DOM_H_LKE1HKJK
#define V8DOM_H_LKE1HKJK

#include "uscxml/Interpreter.h"
#include <v8.h>

#define V8_DESTRUCTOR(type) \
static void jsDestructor(v8::Persistent<v8::Value> object, void* data) { \
v8::HandleScope handleScope; \
type* thing = static_cast<type*>(v8::Local<v8::External>::Cast(object->ToObject()->GetInternalField(0))->Value()); \
delete thing; \
object.Dispose(); \
object.Clear(); \
}

#define ASSERT_ARGS1(args, type1) \
assert(args.Length() == 1); \
assert(args[0]->type1());

#define ASSERT_ARGS2(args, type1, type2) \
assert(args.Length() == 2); \
assert(args[0]->type1()); \
assert(args[1]->type2());

namespace uscxml {

class V8DOM {
public:
	V8DOM();
	virtual ~V8DOM() { };

  template <typename T>
  static T* toClassPtr(v8::Local<v8::Value> data) {
    if(data.IsEmpty())
      return NULL;
    else if(!data->IsExternal())
      return NULL;
    else
      return static_cast<T *>(v8::External::Unwrap(data));
    return NULL;
  }
  static v8::Local<v8::External> toExternal(void* pointer) {
	  v8::HandleScope scope;
	  return scope.Close(v8::External::New(pointer));
	}

  Interpreter* interpreter;
  Arabica::XPath::XPath<std::string>* xpath;
};

}

#endif /* end of include guard: V8DOM_H_LKE1HKJK */
