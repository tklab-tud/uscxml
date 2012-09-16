#ifndef FACTORY_H_5WKLGPRB
#define FACTORY_H_5WKLGPRB

#include "uscxml/Message.h"

#include <string>

namespace uscxml {

	class Interpreter;

  class ExecutableContent {
  public:
    ExecutableContent() {};
    virtual ExecutableContent* create(Interpreter* interpreter) = 0;
  };
  
  class IOProcessor {
  public:
    IOProcessor() {};
    virtual ~IOProcessor() {};
    virtual IOProcessor* create(Interpreter* interpreter) = 0;

    virtual Data getDataModelVariables() = 0;
    virtual void send(SendRequest& req) = 0;
  };

  class Invoker : public IOProcessor {
  public:
    virtual void invoke(InvokeRequest& req) = 0;
    virtual void sendToParent(SendRequest& req) = 0;
  };

  class DataModel {
	public:
    virtual DataModel* create(Interpreter* interpreter) = 0;
    virtual ~DataModel() {}
    
    virtual bool validate(const std::string& location, const std::string& schema) = 0;
    virtual void setEvent(const Event& event) = 0;

    // foreach
    virtual uint32_t getLength(const std::string& expr) = 0;
    virtual void pushContext() = 0;
    virtual void popContext() = 0;
    
    virtual void eval(const std::string& expr) = 0;
    virtual std::string evalAsString(const std::string& expr) = 0;
    virtual bool evalAsBool(const std::string& expr) = 0;
    virtual void assign(const std::string& location, const std::string& expr) = 0;
    virtual void assign(const std::string& location, const Data& data) = 0;
  };
  
  class Factory {
  public:
    static void registerIOProcessor(const std::string type, IOProcessor* ioProcessor);
    static void registerDataModel(const std::string type, DataModel* dataModel);
    static void registerExecutableContent(const std::string tag, ExecutableContent* executableContent);
    static void registerInvoker(const std::string type, Invoker* invoker);
    
    static DataModel* getDataModel(const std::string type, Interpreter* interpreter);
    static IOProcessor* getIOProcessor(const std::string type, Interpreter* interpreter);
    static ExecutableContent* getExecutableContent(const std::string tag, Interpreter* interpreter);
    static Invoker* getInvoker(const std::string type, Interpreter* interpreter);

    static Factory* getInstance();

		std::map<std::string, DataModel*> _dataModels;
		std::map<std::string, IOProcessor*> _ioProcessors;
		std::map<std::string, Invoker*> _invoker;
		std::map<std::string, ExecutableContent*> _executableContent;

  protected:
    Factory();
    static Factory* _instance;

  };


}

#endif /* end of include guard: FACTORY_H_5WKLGPRB */
