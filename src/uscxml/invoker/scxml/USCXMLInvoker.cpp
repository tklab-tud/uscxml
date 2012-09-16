#include "USCXMLInvoker.h"
#include "uscxml/Interpreter.h"

namespace uscxml {
	
USCXMLInvoker::USCXMLInvoker() {
	
}

  
USCXMLInvoker::~USCXMLInvoker() {
  delete _invokedInterpreter;
};
  
Invoker* USCXMLInvoker::create(Interpreter* interpreter) {
  USCXMLInvoker* invoker = new USCXMLInvoker();
  invoker->_parentInterpreter = interpreter;
  return invoker;
}

Data USCXMLInvoker::getDataModelVariables() {
  Data data;
  return data;
}

void USCXMLInvoker::send(SendRequest& req) {
  
}

void USCXMLInvoker::cancel(const std::string sendId) {
  
}

void USCXMLInvoker::sendToParent(SendRequest& req) {
  _parentInterpreter->receive(req);
}

void USCXMLInvoker::invoke(InvokeRequest& req) {
  _invokedInterpreter = Interpreter::fromURI(req.src);
  DataModel* dataModel = _invokedInterpreter->getDataModel();
  if (dataModel != NULL) {
    
  }
  _invokedInterpreter->setInvoker(this);
  _invokedInterpreter->start();
}

}