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
	virtual boost::shared_ptr<DataModelImpl> create(InterpreterImpl* interpreter);

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
	virtual void setForeach(const std::string& item,
	                        const std::string& array,
	                        const std::string& index,
	                        uint32_t iteration);

	virtual void pushContext();
	virtual void popContext();

	virtual void assign(const Arabica::DOM::Element<std::string>& assignElem,
	                    const Arabica::DOM::Document<std::string>& doc,
	                    const std::string& content);
	virtual void assign(const std::string& location, const Data& data);

	virtual void init(const Arabica::DOM::Element<std::string>& dataElem,
	                  const Arabica::DOM::Document<std::string>& doc,
	                  const std::string& content);
	virtual void init(const std::string& location, const Data& data);

	virtual void eval(const Arabica::DOM::Element<std::string>& scriptElem,
	                  const std::string& expr);

	virtual bool isDeclared(const std::string& expr);

	virtual Data getStringAsData(const std::string& content);

	virtual std::string evalAsString(const std::string& expr);
	virtual bool evalAsBool(const std::string& expr);

	static foreign_t inPredicate(term_t a0, int arity, void* context);
protected:
	std::map<std::string, PlTerm> resolveAtoms(PlTerm& term, PlTerm& orig);

	Event _event;

	std::string _plModule;
	std::string _name;
	std::string _sessionId;
};

#ifdef BUILD_AS_PLUGINS
PLUMA_INHERIT_PROVIDER(SWIDataModel, DataModelImpl);
#endif

}

#endif /* end of include guard: SWIDATAMODEL_H_KN8TWG0V */
