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

#include "uscxml/InterpreterInfo.h"
#include "uscxml/plugins/DataModel.h"
#include <list>
#include <JavaScriptCore/JavaScriptCore.h>
#include "JSCDOM.h"

#ifdef BUILD_AS_PLUGINS
#include "uscxml/plugins/Plugins.h"
#endif

namespace uscxml {
class Event;
class Data;
}

namespace uscxml {

class JSCDataModel : public DataModelImpl {
public:
	JSCDataModel();
	virtual ~JSCDataModel();
	virtual boost::shared_ptr<DataModelImpl> create(InterpreterInfo* interpreter);

	virtual void addExtension(DataModelExtension* ext);

	virtual std::list<std::string> getNames() {
		std::list<std::string> names;
		names.push_back("ecmascript");
		return names;
	}

	virtual bool validate(const std::string& location, const std::string& schema);
	virtual bool isLocation(const std::string& expr);
	virtual bool isValidSyntax(const std::string& expr);

	virtual void setEvent(const Event& event);
	virtual Data getStringAsData(const std::string& content);

	// foreach
	virtual uint32_t getLength(const std::string& expr);
	virtual void setForeach(const std::string& item,
	                        const std::string& array,
	                        const std::string& index,
	                        uint32_t iteration);
	virtual void pushContext();
	virtual void popContext();

	virtual void eval(const Arabica::DOM::Element<std::string>& scriptElem,
	                  const std::string& expr);
	virtual std::string evalAsString(const std::string& expr);

	virtual bool evalAsBool(const Arabica::DOM::Element<std::string>& node, const std::string& expr);

	virtual bool isDeclared(const std::string& expr);

	virtual void assign(const Arabica::DOM::Element<std::string>& assignElem,
	                    const Arabica::DOM::Node<std::string>& node,
	                    const std::string& content);
	virtual void assign(const std::string& location, const Data& data);

	virtual void init(const Arabica::DOM::Element<std::string>& dataElem,
	                  const Arabica::DOM::Node<std::string>& node,
	                  const std::string& content);
	virtual void init(const std::string& location, const Data& data);

	virtual std::string andExpressions(std::list<std::string>);

protected:
	Arabica::DOM::JSCDOM* _dom;

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

	JSValueRef getNodeAsValue(const Arabica::DOM::Node<std::string>& node);
	JSValueRef getDataAsValue(const Data& data);
	Data getValueAsData(const JSValueRef value);
	JSValueRef evalAsValue(const std::string& expr, bool dontThrow = false);

	void handleException(JSValueRef exception);

	std::string _sessionId;
	std::string _name;

	std::set<DataModelExtension*> _extensions;

	Event _event;
	JSGlobalContextRef _ctx;

};

#ifdef BUILD_AS_PLUGINS
PLUMA_INHERIT_PROVIDER(JSCDataModel, DataModelImpl);
#endif

}

#endif /* end of include guard: JSCDATAMODEL_H_KN8TWG0V */
