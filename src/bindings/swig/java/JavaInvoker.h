#ifndef JAVAINVOKER_H_WDV9B5F6
#define JAVAINVOKER_H_WDV9B5F6

#include "../../../uscxml/Message.h"
#include "../../../uscxml/Factory.h"
#include "../../../uscxml/Interpreter.h"

namespace uscxml {

class JavaInvoker : public InvokerImpl {
public:
	JavaInvoker();
	virtual ~JavaInvoker();
	
	virtual std::set<std::string> getNames() {
		return std::set<std::string>();
	};
	
	virtual Data getDataModelVariables() {
		Data data;
		return data;
	}
	
	virtual void send(const SendRequest& req) {}
	virtual void invoke(const InvokeRequest& req) {}
	
	virtual JavaInvoker* create(Interpreter interpreter) {
		return new JavaInvoker();
	}
	
	virtual boost::shared_ptr<InvokerImpl> create(InterpreterImpl* interpreter) {
		return boost::shared_ptr<InvokerImpl>(create(interpreter->shared_from_this()));
	}

};

}

#endif /* end of include guard: JAVAINVOKER_H_WDV9B5F6 */
