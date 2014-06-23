#ifndef WRAPPEDINVOKER_H_F9725D47
#define WRAPPEDINVOKER_H_F9725D47

#include "../../../uscxml/Message.h"
#include "../../../uscxml/Factory.h"
#include "../../../uscxml/Interpreter.h"

namespace uscxml {

class WrappedInvoker : public InvokerImpl {
public:
	WrappedInvoker();
	virtual ~WrappedInvoker();

	virtual std::list<std::string> getNames() {
		return std::list<std::string>();
	};

	virtual Data getDataModelVariables() {
		Data data;
		return data;
	}

	virtual void send(const SendRequest& req) {}
	virtual void invoke(const InvokeRequest& req) {}

	virtual WrappedInvoker* create(Interpreter interpreter) {
		return new WrappedInvoker();
	}

	virtual boost::shared_ptr<InvokerImpl> create(InterpreterImpl* interpreter) {
		return boost::shared_ptr<InvokerImpl>(create(interpreter->shared_from_this()));
	}

};

}

#endif /* end of include guard: WRAPPEDINVOKER_H_F9725D47 */
