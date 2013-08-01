#ifndef NULLDATAMODEL_H_KN8TWG0V
#define NULLDATAMODEL_H_KN8TWG0V

#include "uscxml/Interpreter.h"
#include <list>

#ifdef BUILD_AS_PLUGINS
#include "uscxml/plugins/Plugins.h"
#endif

namespace uscxml {
class Event;
class Data;
}

namespace uscxml {

class NULLDataModel : public DataModelImpl {
public:
	NULLDataModel();
	virtual ~NULLDataModel();
	virtual boost::shared_ptr<DataModelImpl> create(InterpreterImpl* interpreter);

	virtual std::set<std::string> getNames() {
		std::set<std::string> names;
		names.insert("null");
		return names;
	}

	virtual void initialize();
	virtual void setEvent(const Event& event);

	virtual bool validate(const std::string& location, const std::string& schema);

	virtual uint32_t getLength(const std::string& expr);
	virtual void setForeach(const std::string& item,
	                        const std::string& array,
	                        const std::string& index,
	                        uint32_t iteration);

	virtual void pushContext();
	virtual void popContext();

	virtual void assign(const Arabica::DOM::Element<std::string>& assignElem,
	                    const Arabica::DOM::Document<std::string>& doc,
	                    const std::string& content) {}
	virtual void assign(const std::string& location, const Data& data) {}

	virtual void init(const Arabica::DOM::Element<std::string>& dataElem,
	                  const Arabica::DOM::Document<std::string>& doc,
	                  const std::string& content) {}
	virtual void init(const std::string& location, const Data& data) {}

	virtual Data getStringAsData(const std::string& content);
	virtual bool isDeclared(const std::string& expr);

	virtual void eval(const Arabica::DOM::Element<std::string>& scriptElem,
	                  const std::string& expr);
	virtual std::string evalAsString(const std::string& expr);
	virtual bool evalAsBool(const std::string& expr);
	virtual double evalAsNumber(const std::string& expr);

protected:

};

#ifdef BUILD_AS_PLUGINS
PLUMA_INHERIT_PROVIDER(NULLDataModel, DataModelImpl);
#endif

}

#endif /* end of include guard: NULLDATAMODEL_H_KN8TWG0V */
