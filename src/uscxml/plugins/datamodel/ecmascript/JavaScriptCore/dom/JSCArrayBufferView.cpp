#include "JSCArrayBuffer.h"
#include "JSCArrayBufferView.h"

namespace Arabica {
namespace DOM {

JSClassRef JSCArrayBufferView::Tmpl;

JSStaticValue JSCArrayBufferView::staticValues[] = {
	{ "buffer", bufferAttrGetter, 0, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },
	{ "byteOffset", byteOffsetAttrGetter, 0, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },
	{ "byteLength", byteLengthAttrGetter, 0, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },

	{ 0, 0, 0, 0 }
};

JSStaticFunction JSCArrayBufferView::staticFunctions[] = {
	{ 0, 0, 0 }
};

JSValueRef JSCArrayBufferView::bufferAttrGetter(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName, JSValueRef *exception) {
	struct JSCArrayBufferViewPrivate* privData = (struct JSCArrayBufferViewPrivate*)JSObjectGetPrivate(object);

	if (!privData->nativeObj->getBuffer()) return JSValueMakeUndefined(ctx);
	uscxml::ArrayBuffer* arabicaRet = new uscxml::ArrayBuffer(privData->nativeObj->getBuffer());

	JSClassRef arbaicaRetClass = JSCArrayBuffer::getTmpl();

	struct JSCArrayBuffer::JSCArrayBufferPrivate* retPrivData = new JSCArrayBuffer::JSCArrayBufferPrivate();
	retPrivData->dom = privData->dom;
	retPrivData->nativeObj = arabicaRet;

	JSObjectRef arbaicaRetObj = JSObjectMake(ctx, arbaicaRetClass, arabicaRet);
	return arbaicaRetObj;
}


JSValueRef JSCArrayBufferView::byteOffsetAttrGetter(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName, JSValueRef *exception) {
	struct JSCArrayBufferViewPrivate* privData = (struct JSCArrayBufferViewPrivate*)JSObjectGetPrivate(object);

	return JSValueMakeNumber(ctx, privData->nativeObj->getByteOffset());
}


JSValueRef JSCArrayBufferView::byteLengthAttrGetter(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName, JSValueRef *exception) {
	struct JSCArrayBufferViewPrivate* privData = (struct JSCArrayBufferViewPrivate*)JSObjectGetPrivate(object);

	return JSValueMakeNumber(ctx, privData->nativeObj->getByteLength());
}


}
}
