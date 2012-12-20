#include "UmundoComponent.h"
#include "uscxml/Interpreter.h"

namespace uscxml {

UmundoComponent::UmundoComponent() {
}


UmundoComponent::~UmundoComponent() {
	delete _invokedInterpreter;
};

Invoker* UmundoComponent::create(Interpreter* interpreter) {
	UmundoComponent* invoker = new UmundoComponent();
	invoker->_parentInterpreter = interpreter;
	return invoker;
}

Data UmundoComponent::getDataModelVariables() {
	Data data;
	return data;
}

void UmundoComponent::send(SendRequest& req) {
	assert(false);
}

void UmundoComponent::cancel(const std::string sendId) {
	assert(false);
}

void UmundoComponent::sendToParent(SendRequest& req) {
	req.invokeid = _invokeId;
	_parentInterpreter->receive(req);
}

void UmundoComponent::invoke(InvokeRequest& req) {
	_invokeId = req.invokeid;
	_invokedInterpreter = Interpreter::fromURI(req.src);
	DataModel* dataModel = _invokedInterpreter->getDataModel();
	if (dataModel != NULL) {

	}
	_invokedInterpreter->setInvoker(this);
	_invokedInterpreter->start();
}

}