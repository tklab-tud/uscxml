#ifndef JSCDATAMODEL_H_KN8TWG0V
#define JSCDATAMODEL_H_KN8TWG0V

#include "uscxml/Interpreter.h"
#include <list>
#include <JavaScriptCore/JavaScriptCore.h>
#include "dom/JSCDOM.h"

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
	virtual boost::shared_ptr<DataModelImpl> create(InterpreterImpl* interpreter);

	virtual std::set<std::string> getNames() {
		std::set<std::string> names;
		names.insert("ecmascript");
		return names;
	}

	virtual bool validate(const std::string& location, const std::string& schema);
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

	virtual void eval(const std::string& expr);
	virtual std::string evalAsString(const std::string& expr);
	virtual bool evalAsBool(const std::string& expr);

	virtual bool isDeclared(const std::string& expr);

	virtual void assign(const Arabica::DOM::Element<std::string>& assignElem,
	                    const Arabica::DOM::Document<std::string>& doc,
	                    const std::string& content);
	virtual void assign(const std::string& location, const Data& data);

	virtual void init(const Arabica::DOM::Element<std::string>& dataElem,
	                  const Arabica::DOM::Document<std::string>& doc,
	                  const std::string& content);
	virtual void init(const std::string& location, const Data& data);

protected:
	Arabica::DOM::JSCDOM* _dom;

	static JSClassDefinition jsInClassDef;
	static JSValueRef jsIn(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObject, size_t argumentCount, const JSValueRef arguments[], JSValueRef* exception);
	static JSClassDefinition jsPrintClassDef;
	static JSValueRef jsPrint(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObject, size_t argumentCount, const JSValueRef arguments[], JSValueRef* exception);

	static JSClassDefinition jsIOProcessorsClassDef;
	static bool jsIOProcessorHasProp(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName);
	static JSValueRef jsIOProcessorGetProp(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName, JSValueRef* exception);
	static void jsIOProcessorListProps(JSContextRef ctx, JSObjectRef object, JSPropertyNameAccumulatorRef propertyNames);
	
	JSValueRef getDocumentAsValue(const Arabica::DOM::Document<std::string>& doc);
	JSValueRef getDataAsValue(const Data& data);
	Data getValueAsData(const JSValueRef value);
	JSValueRef evalAsValue(const std::string& expr, bool dontThrow = false);

	void handleException(JSValueRef exception);

	std::string _sessionId;
	std::string _name;

	Event _event;
	JSGlobalContextRef _ctx;
};

#ifdef BUILD_AS_PLUGINS
PLUMA_INHERIT_PROVIDER(JSCDataModel, DataModelImpl);
#endif

}

#endif /* end of include guard: JSCDATAMODEL_H_KN8TWG0V */
