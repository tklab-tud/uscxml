#include "MMIComponent.h"
#include "uscxml/Interpreter.h"

namespace uscxml {

MMIComponent::MMIComponent() {
}


MMIComponent::~MMIComponent() {
};

Invoker* MMIComponent::create(Interpreter* interpreter) {
	MMIComponent* invoker = new MMIComponent();
	invoker->_interpreter = interpreter;
	return invoker;
}

Data MMIComponent::getDataModelVariables() {
	Data data;
	return data;
}

void MMIComponent::send(SendRequest& req) {

}

void MMIComponent::cancel(const std::string sendId) {
	assert(false);
}

void MMIComponent::sendToParent(SendRequest& req) {
	req.invokeid = _invokeId;
	assert(false);
}

void MMIComponent::invoke(InvokeRequest& req) {
	_invokeId = req.invokeid;

}

}