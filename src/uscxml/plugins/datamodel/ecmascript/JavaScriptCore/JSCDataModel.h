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

#ifndef JSCDATAMODEL_H_KN8TWG0V
#define JSCDATAMODEL_H_KN8TWG0V

#include "uscxml/config.h"
#include "uscxml/plugins/DataModelImpl.h"
#include <list>
#include <set>

#if defined(HAS_JSC_JAVASCRIPTCORE_H)
#include <JavaScriptCore/JavaScriptCore.h>
#elif defined(HAS_JSC_JAVASCRIPT_H)
#include <JavaScriptCore/JavaScript.h>
#else
#error "Did not find header for JSC?"
#endif

#ifdef BUILD_AS_PLUGINS
#include "uscxml/plugins/Plugins.h"
#endif

namespace uscxml {
class Event;
class Data;
}

namespace uscxml {

/**
 * @ingroup datamodel
 *
 * ECMAScript data-model via JavaScriptCore.
 */
class JSCDataModel : public DataModelImpl {
public:
	JSCDataModel();
	virtual ~JSCDataModel();
	virtual std::shared_ptr<DataModelImpl> create(DataModelCallbacks* callbacks);

	virtual void addExtension(DataModelExtension* ext);

	virtual std::list<std::string> getNames() {
		std::list<std::string> names;
		names.push_back("ecmascript");
		return names;
	}

	virtual bool isValidSyntax(const std::string& expr);

	virtual void setEvent(const Event& event);

	// foreach
	virtual uint32_t getLength(const std::string& expr);
	virtual void setForeach(const std::string& item,
	                        const std::string& array,
	                        const std::string& index,
	                        uint32_t iteration);

	virtual Data getAsData(const std::string& content);
	virtual Data evalAsData(const std::string& expr);
	virtual bool evalAsBool(const std::string& expr);

	virtual bool isDeclared(const std::string& expr);

	virtual void assign(const std::string& location,
	                    const Data& data,
	                    const std::map<std::string, std::string>& attr = std::map<std::string, std::string>());
	virtual void init(const std::string& location,
	                  const Data& data,
	                  const std::map<std::string, std::string>& attr = std::map<std::string, std::string>());

protected:

	static JSClassDefinition jsInClassDef;
	static JSValueRef jsIn(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObject, size_t argumentCount, const JSValueRef arguments[], JSValueRef* exception);
	static JSClassDefinition jsPrintClassDef;
	static JSValueRef jsPrint(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObject, size_t argumentCount, const JSValueRef arguments[], JSValueRef* exception);
	static JSClassDefinition jsExtensionClassDef;
	static JSValueRef jsExtension(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObject, size_t argumentCount, const JSValueRef arguments[], JSValueRef* exception);

	static JSClassDefinition jsIOProcessorsClassDef;
	static bool jsIOProcessorHasProp(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName);
	static JSValueRef jsIOProcessorGetProp(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName, JSValueRef* exception);
	static void jsIOProcessorListProps(JSContextRef ctx, JSObjectRef object, JSPropertyNameAccumulatorRef propertyNames);

	static JSClassDefinition jsInvokersClassDef;
	static bool jsInvokerHasProp(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName);
	static JSValueRef jsInvokerGetProp(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName, JSValueRef* exception);
	static void jsInvokerListProps(JSContextRef ctx, JSObjectRef object, JSPropertyNameAccumulatorRef propertyNames);

	JSValueRef getNodeAsValue(const XERCESC_NS::DOMNode* node);
	JSValueRef getDataAsValue(const Data& data);
	Data getValueAsData(const JSValueRef value);
	JSValueRef evalAsValue(const std::string& expr, bool dontThrow = false);

	void handleException(JSValueRef exception);

	std::string _sessionId;
	std::string _name;

	std::set<DataModelExtension*> _extensions;

	Event _event;
	JSGlobalContextRef _ctx;

	static std::mutex _initMutex;

};

#ifdef BUILD_AS_PLUGINS
PLUMA_INHERIT_PROVIDER(JSCDataModel, DataModelImpl)
#endif

}

#endif /* end of include guard: JSCDATAMODEL_H_KN8TWG0V */
