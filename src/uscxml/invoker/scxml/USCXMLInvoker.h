#ifndef USCXMLINVOKER_H_OQFA21IO
#define USCXMLINVOKER_H_OQFA21IO

#include "uscxml/Factory.h"

namespace uscxml {

class Interpreter;
  
class USCXMLInvoker : public Invoker {
public:
	USCXMLInvoker();
  virtual ~USCXMLInvoker();
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

#endif /* end of include guard: USCXMLINVOKER_H_OQFA21IO */
