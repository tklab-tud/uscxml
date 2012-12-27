#ifndef FACTORY_H_5WKLGPRB
#define FACTORY_H_5WKLGPRB

#include "uscxml/Message.h"

#ifdef BUILD_AS_PLUGINS
#include "Pluma/Pluma.hpp"
#endif

#include <string>
#include <set>

namespace uscxml {

// see http://stackoverflow.com/questions/228005/alternative-to-itoa-for-converting-integer-to-string-c
template <typename T> std::string toStr(T tmp) {
	std::ostringstream out;
	out << tmp;
	return out.str();
}

template <typename T> T strTo(std::string tmp) {
	T output;
	std::istringstream in(tmp);
	in >> output;
	return output;
}

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
	virtual std::set<std::string> getNames() = 0;

	virtual void setInterpreter(Interpreter* interpreter) {
		_interpreter = interpreter;
	}
  
	virtual Data getDataModelVariables() = 0;
	virtual void send(SendRequest& req) = 0;

  virtual void runOnMainThread() {};

protected:
	Interpreter* _interpreter;
};

class Invoker : public IOProcessor {
public:
	virtual void invoke(InvokeRequest& req) = 0;
	virtual void sendToParent(SendRequest& req) = 0;
};

class DataModel {
public:
	virtual ~DataModel() {}
	virtual DataModel* create(Interpreter* interpreter) = 0;
	virtual std::set<std::string> getNames() = 0;

	virtual bool validate(const std::string& location, const std::string& schema) = 0;
	virtual void setEvent(const Event& event) = 0;
	virtual Data getStringAsData(const std::string& content) = 0;

	virtual void registerIOProcessor(const std::string& name, IOProcessor* ioprocessor) = 0;

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
	void registerIOProcessor(IOProcessor* ioProcessor);
	void registerDataModel(DataModel* dataModel);
	void registerInvoker(Invoker* invoker);
	void registerExecutableContent(const std::string tag, ExecutableContent* executableContent);

	static DataModel* getDataModel(const std::string type, Interpreter* interpreter);
	static IOProcessor* getIOProcessor(const std::string type, Interpreter* interpreter);
	static ExecutableContent* getExecutableContent(const std::string tag, Interpreter* interpreter);
	static Invoker* getInvoker(const std::string type, Interpreter* interpreter);

	static Factory* getInstance();

	std::map<std::string, DataModel*> _dataModels;
	std::map<std::string, IOProcessor*> _ioProcessors;
	std::map<std::string, Invoker*> _invokers;
	std::map<std::string, ExecutableContent*> _executableContent;

	static std::string pluginPath;

protected:
#ifdef BUILD_AS_PLUGINS
	pluma::Pluma pluma;
#endif

	Factory();
	~Factory();
	static Factory* _instance;

};


}

#endif /* end of include guard: FACTORY_H_5WKLGPRB */
