#ifndef V8DOM_H_LKE1HKJK
#define V8DOM_H_LKE1HKJK

#include "uscxml/Common.h"
#include "uscxml/Interpreter.h"
#include <v8.h>
#include <XPath/XPath.hpp>
#include "../Storage.h"

#define V8_DESTRUCTOR(type) \
static void jsDestructor(v8::Persistent<v8::Value> object, void* data) { \
  v8::HandleScope handleScope; \
  type* thing = static_cast<type*>(v8::Local<v8::External>::Cast(object->ToObject()->GetInternalField(0))->Value()); \
  delete thing->nativeObj; \
  delete thing; \
  object.Dispose(); \
  object.Clear(); \
}

#define V8_DESTRUCTOR_KEEP_WRAPPED(type) \
static void jsDestructor(v8::Persistent<v8::Value> object, void* data) { \
v8::HandleScope handleScope; \
type* thing = static_cast<type*>(v8::Local<v8::External>::Cast(object->ToObject()->GetInternalField(0))->Value()); \
delete thing; \
object.Dispose(); \
object.Clear(); \
}

namespace Arabica {
namespace DOM {

class V8DOM {
public:
	V8DOM();
	virtual ~V8DOM();

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

	Arabica::XPath::XPath<std::string>* xpath;
	uscxml::Storage* storage;
};

class V8Exception : public std::runtime_error {
public:

	V8Exception(const std::string& reason) :
		std::runtime_error("DOMException") {
	} // V8Exception

	V8Exception(const V8Exception& rhs) :
		std::runtime_error(rhs),
		reason_(rhs.reason_) {
	} // DOMException

	virtual ~V8Exception() throw() {
	} // DOMBadCast

	virtual const char* what() const throw() {
		return reason_.c_str();
	} // what

private:
	DOMBadCast& operator=(const DOMBadCast&);
	bool operator==(const DOMBadCast&) const;

	std::string reason_;
}; // class DOMException

}
}
#endif /* end of include guard: V8DOM_H_LKE1HKJK */
