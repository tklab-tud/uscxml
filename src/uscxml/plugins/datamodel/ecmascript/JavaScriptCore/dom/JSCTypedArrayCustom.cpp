#include "../../TypedArray.h"
#include "JSCArrayBuffer.h"
#include "JSCInt8Array.h"
#include "JSCUint8Array.h"
#include "JSCUint8ClampedArray.h"
#include "JSCInt16Array.h"
#include "JSCUint16Array.h"
#include "JSCInt32Array.h"
#include "JSCUint32Array.h"
#include "JSCFloat32Array.h"
#include "JSCFloat64Array.h"
#include "JSCDataView.h"

#define JSC_VALUE_TO_STRING(name, stringName)\
size_t name##MaxSize = JSStringGetMaximumUTF8CStringSize(name);\
char* name##Buffer = new char[name##MaxSize];\
JSStringGetUTF8CString(name, name##Buffer, name##MaxSize);\
std::string stringName(name##Buffer);\
free(name##Buffer);\
 

#define JSC_TYPED_ARRAY_GET_PROP_RETURN(type)\
size_t propMaxSize = JSStringGetMaximumUTF8CStringSize(propertyName);\
char* propBuffer = new char[propMaxSize];\
JSStringGetUTF8CString(propertyName, propBuffer, propMaxSize);\
std::string propName(propBuffer);\
free(propBuffer);\
if (strcmp(propName.c_str(), "prototype") == 0) {\
	JSStringRef prototypeName = JSStringCreateWithUTF8CString(#type);\
	JSValueRef prototype = JSObjectGetProperty(ctx, JSContextGetGlobalObject(ctx), prototypeName, exception);\
	assert(!JSValueIsUndefined(ctx, prototype) && !JSValueIsNull(ctx, prototype));\
	JSStringRelease(prototypeName);\
	return prototype;\
}\
JSStaticValue* prop = JSC##type::staticValues;\
while(prop->name) {\
	if (strcmp(propName.c_str(), prop->name) == 0) {\
		return (prop->getProperty)(ctx, object, propertyName, exception);\
	}\
	prop++;\
}\
\
JSC##type::JSC##type##Private* privObj = (JSC##type::JSC##type##Private*)JSObjectGetPrivate(object);\
if (!privObj)\
	return JSValueMakeUndefined(ctx);\
\
uscxml::type* array = ((JSC##type::JSC##type##Private*)JSObjectGetPrivate(object))->nativeObj;\
std::string base = "0123456789";\
if (propName.find_first_not_of(base) != std::string::npos) {\
	return JSValueMakeUndefined(ctx);\
}\
unsigned long index = boost::lexical_cast<unsigned long>(propName);\
return JSValueMakeNumber(ctx, array->get(index));



#define JSC_TYPED_ARRAY_SET_PROP_RETURN(type)\
if (!JSValueIsNumber(ctx, value)) {\
	return false;\
}\
size_t propMaxSize = JSStringGetMaximumUTF8CStringSize(propertyName);\
char* propBuffer = new char[propMaxSize];\
JSStringGetUTF8CString(propertyName, propBuffer, propMaxSize);\
std::string propName(propBuffer);\
free(propBuffer);\
uscxml::type* array = ((JSC##type::JSC##type##Private*)JSObjectGetPrivate(object))->nativeObj;\
std::string base = "0123456789";\
if (propName.find_first_not_of(base) != std::string::npos) {\
	return JSValueMakeUndefined(ctx);\
}\
unsigned long index = boost::lexical_cast<unsigned long>(propName);\
if (index >= array->getLength()) {\
	return false;\
}\
array->set(index, JSValueToNumber(ctx, value, exception));\
return true;


#define JSC_TYPED_ARRAY_HAS_PROP_RETURN(type)\
size_t propertyNameMaxSize = JSStringGetMaximumUTF8CStringSize(propertyName);\
char* propertyNameBuffer = new char[propertyNameMaxSize];\
JSStringGetUTF8CString(propertyName, propertyNameBuffer, propertyNameMaxSize);\
std::string propName(propertyNameBuffer);\
free(propertyNameBuffer);\
\
if (strcmp(propName.c_str(), "prototype") == 0)\
	return true;\
\
if (strcmp(propName.c_str(), "length") == 0)\
	return true;\
\
JSStaticValue* prop = JSC##type::staticValues;\
while(prop->name) {\
	if (strcmp(propName.c_str(), prop->name) == 0) {\
		return true;\
	}\
	prop++;\
}\
\
JSC##type::JSC##type##Private* privObj = (JSC##type::JSC##type##Private*)JSObjectGetPrivate(object);\
if (!privObj)\
	return false;\
\
uscxml::type* array = ((JSC##type::JSC##type##Private*)JSObjectGetPrivate(object))->nativeObj;\
std::string base = "0123456789";\
if (propName.find_first_not_of(base) != std::string::npos) {\
	return false;\
}\
unsigned long index = boost::lexical_cast<unsigned long>(propName);\
if (array->getLength() > index)\
	return true;\
return false;\
 
namespace Arabica {
namespace DOM {

bool JSCInt8Array::hasPropertyCustomCallback(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName) {
	JSC_TYPED_ARRAY_HAS_PROP_RETURN(Int8Array);
}

bool JSCInt16Array::hasPropertyCustomCallback(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName) {
	JSC_TYPED_ARRAY_HAS_PROP_RETURN(Int16Array);
}

bool JSCInt32Array::hasPropertyCustomCallback(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName) {
	JSC_TYPED_ARRAY_HAS_PROP_RETURN(Int32Array);
}

bool JSCUint8Array::hasPropertyCustomCallback(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName) {
	JSC_TYPED_ARRAY_HAS_PROP_RETURN(Uint8Array);
}

bool JSCUint16Array::hasPropertyCustomCallback(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName) {
	JSC_TYPED_ARRAY_HAS_PROP_RETURN(Uint16Array);
}

bool JSCUint32Array::hasPropertyCustomCallback(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName) {
	JSC_TYPED_ARRAY_HAS_PROP_RETURN(Uint32Array);
}

bool JSCFloat32Array::hasPropertyCustomCallback(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName) {
	JSC_TYPED_ARRAY_HAS_PROP_RETURN(Float32Array);
}

bool JSCFloat64Array::hasPropertyCustomCallback(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName) {
	JSC_TYPED_ARRAY_HAS_PROP_RETURN(Float64Array);
}

bool JSCUint8ClampedArray::hasPropertyCustomCallback(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName) {
	JSC_TYPED_ARRAY_HAS_PROP_RETURN(Uint8ClampedArray);
}

bool JSCArrayBuffer::hasPropertyCustomCallback(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName) {
	JSC_TYPED_ARRAY_HAS_PROP_RETURN(ArrayBuffer);
}

// -----------------

JSValueRef JSCInt8Array::getPropertyCustomCallback(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName, JSValueRef* exception) {
	JSC_TYPED_ARRAY_GET_PROP_RETURN(Int8Array);
}

JSValueRef JSCInt16Array::getPropertyCustomCallback(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName, JSValueRef* exception) {
	JSC_TYPED_ARRAY_GET_PROP_RETURN(Int16Array);
}

JSValueRef JSCInt32Array::getPropertyCustomCallback(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName, JSValueRef* exception) {
	JSC_TYPED_ARRAY_GET_PROP_RETURN(Int32Array);
}

JSValueRef JSCUint8Array::getPropertyCustomCallback(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName, JSValueRef* exception) {
	JSC_TYPED_ARRAY_GET_PROP_RETURN(Uint8Array);
}

JSValueRef JSCUint16Array::getPropertyCustomCallback(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName, JSValueRef* exception) {
	JSC_TYPED_ARRAY_GET_PROP_RETURN(Uint16Array);
}

JSValueRef JSCUint32Array::getPropertyCustomCallback(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName, JSValueRef* exception) {
	JSC_TYPED_ARRAY_GET_PROP_RETURN(Uint32Array);
}

JSValueRef JSCFloat32Array::getPropertyCustomCallback(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName, JSValueRef* exception) {
	JSC_TYPED_ARRAY_GET_PROP_RETURN(Float32Array);
}

JSValueRef JSCFloat64Array::getPropertyCustomCallback(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName, JSValueRef* exception) {
	JSC_TYPED_ARRAY_GET_PROP_RETURN(Float64Array);
}

JSValueRef JSCUint8ClampedArray::getPropertyCustomCallback(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName, JSValueRef* exception) {
	JSC_TYPED_ARRAY_GET_PROP_RETURN(Uint8ClampedArray);
}

JSValueRef JSCArrayBuffer::getPropertyCustomCallback(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName, JSValueRef* exception) {
	JSC_TYPED_ARRAY_GET_PROP_RETURN(ArrayBuffer);
}

// ----------------

bool JSCInt8Array::setPropertyCustomCallback(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName, JSValueRef value, JSValueRef* exception) {
	JSC_TYPED_ARRAY_SET_PROP_RETURN(Int8Array);
}

bool JSCInt16Array::setPropertyCustomCallback(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName, JSValueRef value, JSValueRef* exception) {
	JSC_TYPED_ARRAY_SET_PROP_RETURN(Int16Array);
}

bool JSCInt32Array::setPropertyCustomCallback(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName, JSValueRef value, JSValueRef* exception) {
	JSC_TYPED_ARRAY_SET_PROP_RETURN(Int32Array);
}

bool JSCUint8Array::setPropertyCustomCallback(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName, JSValueRef value, JSValueRef* exception) {
	JSC_TYPED_ARRAY_SET_PROP_RETURN(Uint8Array);
}

bool JSCUint16Array::setPropertyCustomCallback(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName, JSValueRef value, JSValueRef* exception) {
	JSC_TYPED_ARRAY_SET_PROP_RETURN(Uint16Array);
}

bool JSCUint32Array::setPropertyCustomCallback(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName, JSValueRef value, JSValueRef* exception) {
	JSC_TYPED_ARRAY_SET_PROP_RETURN(Uint32Array);
}

bool JSCFloat32Array::setPropertyCustomCallback(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName, JSValueRef value, JSValueRef* exception) {
	JSC_TYPED_ARRAY_SET_PROP_RETURN(Float32Array);
}

bool JSCFloat64Array::setPropertyCustomCallback(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName, JSValueRef value, JSValueRef* exception) {
	JSC_TYPED_ARRAY_SET_PROP_RETURN(Float64Array);
}

bool JSCUint8ClampedArray::setPropertyCustomCallback(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName, JSValueRef value, JSValueRef* exception) {
	JSC_TYPED_ARRAY_SET_PROP_RETURN(Uint8ClampedArray);
}

bool JSCArrayBuffer::setPropertyCustomCallback(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName, JSValueRef value, JSValueRef* exception) {
	JSC_TYPED_ARRAY_SET_PROP_RETURN(ArrayBuffer);
}


}
}