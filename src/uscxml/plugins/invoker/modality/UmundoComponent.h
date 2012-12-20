#ifndef UMUNDOCOMPONENT_H_VMW54W1R
#define UMUNDOCOMPONENT_H_VMW54W1R

#include "MMIComponent.h"

namespace uscxml {

class Interpreter;

class UmundoComponent : public MMIComponent {
public:
	UmundoComponent();
	virtual ~UmundoComponent();
	virtual Invoker* create(Interpreter* interpreter);

	virtual Data getDataModelVariables();
	virtual void send(SendRequest& req);
	virtual void cancel(const std::string sendId);
	virtual void invoke(InvokeRequest& req);
	virtual void sendToParent(SendRequest& req);

protected:
	std::string _invokeId;
	Interpreter* _invokedInterpreter;
	Interpreter* _parentInterpreter;
};

}

#endif /* end of include guard: UMUNDOCOMPONENT_H_VMW54W1R */
