#ifndef SWIDATAMODEL_H_KN8TWG0V
#define SWIDATAMODEL_H_KN8TWG0V

#include "uscxml/Interpreter.h"
#include <list>
#include <SWI-cpp.h>

#ifdef BUILD_AS_PLUGINS
#include "uscxml/plugins/Plugins.h"
#endif

namespace uscxml {

class SWIDataModel : public DataModelImpl {
public:
	SWIDataModel();
	virtual ~SWIDataModel();
	virtual boost::shared_ptr<DataModelImpl> create(Interpreter* interpreter);

	virtual std::set<std::string> getNames() {
		std::set<std::string> names;
		names.insert("prolog");
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

	virtual std::string evalAsString(const std::string& expr);
	virtual bool evalAsBool(const std::string& expr);


protected:
	Interpreter* _interpreter;

	std::string _sessionId;
	std::string _name;

	Event _event;
	PlEngine* _plEngine;

};

#ifdef BUILD_AS_PLUGINS
PLUMA_INHERIT_PROVIDER(SWIDataModel, DataModel);
#endif

}

#endif /* end of include guard: SWIDATAMODEL_H_KN8TWG0V */
