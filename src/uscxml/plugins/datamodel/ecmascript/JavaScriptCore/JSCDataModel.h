#ifndef JSCDATAMODEL_H_KN8TWG0V
#define JSCDATAMODEL_H_KN8TWG0V

#include "uscxml/Interpreter.h"
#include <list>
#include <JavaScriptCore/JavaScriptCore.h>

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
	virtual boost::shared_ptr<DataModelImpl> create(Interpreter* interpreter);

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
	virtual Data getValueAsData(const JSValueRef value);

	virtual std::string evalAsString(const std::string& expr);
	virtual bool evalAsBool(const std::string& expr);
	virtual JSValueRef evalAsValue(const std::string& expr);


protected:
	void handleException(JSValueRef exception);

	Interpreter* _interpreter;

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
