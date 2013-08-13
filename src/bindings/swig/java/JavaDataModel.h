#ifndef JAVADataModel_H_7U446XJQ
#define JAVADataModel_H_7U446XJQ

#include "../../../uscxml/Message.h"
#include "../../../uscxml/Factory.h"
#include "../../../uscxml/Interpreter.h"

namespace uscxml {

class JavaDataModel : public DataModelImpl {
public:
	JavaDataModel();
	virtual ~JavaDataModel();

	virtual JavaDataModel* create(Interpreter interpreter) {
		return new JavaDataModel();
	}

	virtual boost::shared_ptr<DataModelImpl> create(InterpreterImpl* interpreter) {
		return boost::shared_ptr<DataModelImpl>(create(interpreter->shared_from_this()));
	}
	virtual std::set<std::string> getNames() {
		return std::set<std::string>();
	};

	virtual bool validate(const std::string& location, const std::string& schema) {
		return true;
	}
	virtual void setEvent(const Event& event) {}
	virtual Data getStringAsData(const std::string& content) {
		Data data;
		return data;
	}

	// foreach
	virtual uint32_t getLength(const std::string& expr) {
		return 0;
	}
	virtual void setForeach(const std::string& item,
	                        const std::string& array,
	                        const std::string& index,
	                        uint32_t iteration) {}
	virtual void pushContext() {}
	virtual void popContext() {}

	virtual void eval(const Arabica::DOM::Element<std::string>& scriptElem,
	                  const std::string& expr) {}

	virtual std::string evalAsString(const std::string& expr) {
		return "";
	}
	virtual bool evalAsBool(const std::string& expr) {
		return false;
	}

	virtual bool isDeclared(const std::string& expr) {
		return false;
	}

	virtual void assign(const Arabica::DOM::Element<std::string>& assignElem,
	                    const Arabica::DOM::Document<std::string>& doc,
	                    const std::string& content) {}
	virtual void assign(const std::string& location, const Data& data) {}

	virtual void init(const Arabica::DOM::Element<std::string>& dataElem,
	                  const Arabica::DOM::Document<std::string>& doc,
	                  const std::string& content) {}
	virtual void init(const std::string& location, const Data& data) {}


};

}

#endif /* end of include guard: JAVADataModel_H_7U446XJQ */
