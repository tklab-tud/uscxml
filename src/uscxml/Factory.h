/**
 *  @file
 *  @author     2012-2013 Stefan Radomski (stefan.radomski@cs.tu-darmstadt.de)
 *  @copyright  Simplified BSD
 *
 *  @cond
 *  This program is free software: you can redistribute it and/or modify
 *  it under the terms of the FreeBSD license as published by the FreeBSD
 *  project.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 *
 *  You should have received a copy of the FreeBSD license along with this
 *  program. If not, see <http://www.opensource.org/licenses/bsd-license>.
 *  @endcond
 */

#ifndef FACTORY_H_5WKLGPRB
#define FACTORY_H_5WKLGPRB

#include "uscxml/Common.h"
#include "uscxml/Message.h"
#include "uscxml/Convenience.h"

#ifdef BUILD_AS_PLUGINS
#include "Pluma/Pluma.hpp"
#endif

#include <string>
#include <set>
#include <boost/shared_ptr.hpp>
#include <limits>

namespace uscxml {

class InterpreterImpl;

class USCXML_API ExecutableContentImpl {
public:
	ExecutableContentImpl() {};
	virtual ~ExecutableContentImpl() {};
	virtual boost::shared_ptr<ExecutableContentImpl> create(InterpreterImpl* interpreter) = 0;

	virtual void setInterpreter(InterpreterImpl* interpreter) {
		_interpreter = interpreter;
	}

	virtual std::string getLocalName() = 0; ///< The name of the element.
	virtual std::string getNamespace() {
		return "http://www.w3.org/2005/07/scxml";    ///< The namespace of the element.
	}
	virtual void enterElement(const Arabica::DOM::Node<std::string>& node) = 0; ///< Invoked when entering the element as part of evaluating executable content.
	virtual void exitElement(const Arabica::DOM::Node<std::string>& node) = 0; ///< Invoked when exiting the element as part of evaluating executable content.
	virtual bool processChildren() = 0; ///< Whether or not the interpreter should process this elements children.

protected:
	InterpreterImpl* _interpreter;
};

class USCXML_API ExecutableContent {
public:
	ExecutableContent() : _impl() {}
	ExecutableContent(boost::shared_ptr<ExecutableContentImpl> const impl) : _impl(impl) { }
	ExecutableContent(const ExecutableContent& other) : _impl(other._impl) { }
	virtual ~ExecutableContent() {};

	operator bool() const {
		return _impl;
	}
	bool operator< (const ExecutableContent& other) const     {
		return _impl < other._impl;
	}
	bool operator==(const ExecutableContent& other) const     {
		return _impl == other._impl;
	}
	bool operator!=(const ExecutableContent& other) const     {
		return _impl != other._impl;
	}
	ExecutableContent& operator= (const ExecutableContent& other)   {
		_impl = other._impl;
		return *this;
	}

	void setInterpreter(InterpreterImpl* interpreter) {
		_impl->setInterpreter(interpreter);
	}

	std::string getLocalName() {
		return _impl->getLocalName();
	}
	std::string getNamespace() {
		return _impl->getNamespace();
	}
	void enterElement(const Arabica::DOM::Node<std::string>& node) {
		return _impl->enterElement(node);
	}
	void exitElement(const Arabica::DOM::Node<std::string>& node) {
		return _impl->exitElement(node);
	}
	bool processChildren() {
		return _impl->processChildren();
	}
protected:
	boost::shared_ptr<ExecutableContentImpl> _impl;

};

class USCXML_API EventHandlerImpl {
public:
	virtual ~EventHandlerImpl() {}

	virtual std::set<std::string> getNames() = 0;

	virtual void setInterpreter(InterpreterImpl* interpreter) {
		_interpreter = interpreter;
	}
	void setInvokeId(const std::string& invokeId) {
		_invokeId = invokeId;
	}
	void setType(const std::string& type) {
		_type = type;
	}

	void setElement(const Arabica::DOM::Element<std::string>& element) {
		_element = element;
	}
	
	Arabica::DOM::Element<std::string> getElement() {
		return _element;
	}

	virtual Data getDataModelVariables() = 0;
	virtual void send(const SendRequest& req) = 0;

	virtual void runOnMainThread() {};
	void returnEvent(Event& event);
	void returnErrorExecution(const std::string&);
	void returnErrorPlatform(const std::string&);

protected:
	InterpreterImpl* _interpreter;
	Arabica::DOM::Element<std::string> _element;
	std::string _invokeId;
	std::string _type;

};

class USCXML_API EventHandler {
public:
	EventHandler() : _impl() {}
	EventHandler(boost::shared_ptr<EventHandlerImpl> const impl) : _impl(impl) { }
	EventHandler(const EventHandler& other) : _impl(other._impl) { }
	virtual ~EventHandler() {};

	virtual std::set<std::string> getNames()   {
		return _impl->getNames();
	}

	virtual Data getDataModelVariables() const {
		return _impl->getDataModelVariables();
	};
	virtual void send(const SendRequest& req)  {
		return _impl->send(req);
	};
	virtual void runOnMainThread()             {
		return _impl->runOnMainThread();
	}

	void setInterpreter(InterpreterImpl* interpreter) {
		_impl->setInterpreter(interpreter);
	}
	void setInvokeId(const std::string& invokeId) {
		_impl->setInvokeId(invokeId);
	}
	void setType(const std::string& type) {
		_impl->setType(type);
	}

	void setElement(const Arabica::DOM::Element<std::string>& element) {
		_impl->setElement(element);
	}
	
	Arabica::DOM::Element<std::string> getElement() {
		return _impl->getElement();
	}

protected:
	boost::shared_ptr<EventHandlerImpl> _impl;
	friend class InterpreterImpl;
};

class USCXML_API IOProcessorImpl : public EventHandlerImpl {
public:
	IOProcessorImpl() {};
	virtual ~IOProcessorImpl() {};
	virtual boost::shared_ptr<IOProcessorImpl> create(InterpreterImpl* interpreter) = 0;
};

class USCXML_API IOProcessor : public EventHandler {
public:
	IOProcessor() : _impl() {}
	IOProcessor(boost::shared_ptr<IOProcessorImpl> const impl) : EventHandler(impl), _impl(impl) { }
	IOProcessor(const IOProcessor& other) : EventHandler(other._impl), _impl(other._impl) { }
	virtual ~IOProcessor() {};

	operator bool()                           const     {
		return _impl;
	}
	bool operator< (const IOProcessor& other) const     {
		return _impl < other._impl;
	}
	bool operator==(const IOProcessor& other) const     {
		return _impl == other._impl;
	}
	bool operator!=(const IOProcessor& other) const     {
		return _impl != other._impl;
	}
	IOProcessor& operator= (const IOProcessor& other)   {
		_impl = other._impl;
		EventHandler::_impl = _impl;
		return *this;
	}

protected:
	boost::shared_ptr<IOProcessorImpl> _impl;
	friend class InterpreterImpl;
};

class USCXML_API InvokerImpl : public EventHandlerImpl {
public:
	virtual ~InvokerImpl() {}
	virtual void invoke(const InvokeRequest& req) = 0;
	virtual boost::shared_ptr<InvokerImpl> create(InterpreterImpl* interpreter) = 0;
};

class USCXML_API Invoker : public EventHandler {
public:
	Invoker() : _impl() {}
	Invoker(boost::shared_ptr<InvokerImpl> const impl) : EventHandler(impl), _impl(impl) { }
	Invoker(const Invoker& other) : EventHandler(other._impl), _impl(other._impl) { }
	virtual ~Invoker() {};

	operator bool()                       const {
		return _impl;
	}
	bool operator< (const Invoker& other) const {
		return _impl < other._impl;
	}
	bool operator==(const Invoker& other) const {
		return _impl == other._impl;
	}
	bool operator!=(const Invoker& other) const {
		return _impl != other._impl;
	}
	Invoker& operator= (const Invoker& other)   {
		_impl = other._impl;
		EventHandler::_impl = _impl;
		return *this;
	}

	virtual void invoke(InvokeRequest& req)     {
		_impl->invoke(req);
	}

protected:
	boost::shared_ptr<InvokerImpl> _impl;
};

class USCXML_API DataModelImpl {
public:
	virtual ~DataModelImpl() {}
	virtual boost::shared_ptr<DataModelImpl> create(InterpreterImpl* interpreter) = 0;
	virtual std::set<std::string> getNames() = 0;

	virtual bool validate(const std::string& location, const std::string& schema) = 0;
	virtual void setEvent(const Event& event) = 0;
	virtual Data getStringAsData(const std::string& content) = 0;

	size_t replaceExpressions(std::string& content);

	// foreach
	virtual uint32_t getLength(const std::string& expr) = 0;
	virtual void setForeach(const std::string& item,
	                        const std::string& array,
	                        const std::string& index,
	                        uint32_t iteration) = 0;
	virtual void pushContext() = 0;
	virtual void popContext() = 0;

	virtual void eval(const Arabica::DOM::Element<std::string>& scriptElem,
	                  const std::string& expr) = 0;

	virtual std::string evalAsString(const std::string& expr) = 0;

	virtual bool evalAsBool(const Arabica::DOM::Node<std::string>& scriptNode,
	                        const std::string& expr) = 0;
	virtual bool evalAsBool(const std::string& expr) {
		return evalAsBool(Arabica::DOM::Node<std::string>(), expr);
	}

	virtual bool isDeclared(const std::string& expr) = 0;

	virtual void assign(const Arabica::DOM::Element<std::string>& assignElem,
	                    const Arabica::DOM::Node<std::string>& node,
	                    const std::string& content) = 0;
	virtual void assign(const std::string& location, const Data& data) = 0;

	virtual void init(const Arabica::DOM::Element<std::string>& dataElem,
	                  const Arabica::DOM::Node<std::string>& node,
	                  const std::string& content) = 0;
	virtual void init(const std::string& location, const Data& data) = 0;

	virtual void setInterpreter(InterpreterImpl* interpreter) {
		_interpreter = interpreter;
	}

	virtual std::string andExpressions(std::list<std::string>) { return ""; }
	
	// we need it public for various static functions
	InterpreterImpl* _interpreter;
};

class USCXML_API DataModel {
public:
	DataModel() : _impl() {}
	DataModel(const boost::shared_ptr<DataModelImpl> impl) : _impl(impl) { }
	DataModel(const DataModel& other) : _impl(other._impl) { }
	virtual ~DataModel() {};

	operator bool()                         const     {
		return _impl;
	}
	bool operator< (const DataModel& other) const     {
		return _impl < other._impl;
	}
	bool operator==(const DataModel& other) const     {
		return _impl == other._impl;
	}
	bool operator!=(const DataModel& other) const     {
		return _impl != other._impl;
	}
	DataModel& operator= (const DataModel& other)     {
		_impl = other._impl;
		return *this;
	}

	virtual std::set<std::string> getNames() {
		return _impl->getNames();
	}

	virtual bool validate(const std::string& location, const std::string& schema) {
		return _impl->validate(location, schema);
	}
	virtual void setEvent(const Event& event) {
		return _impl->setEvent(event);
	}
	virtual Data getStringAsData(const std::string& content) {
		return _impl->getStringAsData(content);
	}

	virtual void pushContext() {
		return _impl->pushContext();
	}
	virtual void popContext() {
		return _impl->popContext();
	}

	virtual void eval(const Arabica::DOM::Element<std::string>& scriptElem,
	                  const std::string& expr) {
		return _impl->eval(scriptElem, expr);
	}
	virtual std::string evalAsString(const std::string& expr) {
		return _impl->evalAsString(expr);
	}
	virtual bool evalAsBool(const std::string& expr) {
		return _impl->evalAsBool(expr);
	}
	virtual bool evalAsBool(const Arabica::DOM::Node<std::string>& scriptNode,
	                        const std::string& expr) {
		return _impl->evalAsBool(scriptNode, expr);
	}

	virtual uint32_t getLength(const std::string& expr) {
		return _impl->getLength(expr);
	}
	virtual void setForeach(const std::string& item,
	                        const std::string& array,
	                        const std::string& index,
	                        uint32_t iteration) {
		return _impl->setForeach(item, array, index, iteration);
	}

	virtual void assign(const Arabica::DOM::Element<std::string>& assignElem,
	                    const Arabica::DOM::Node<std::string>& node,
	                    const std::string& content) {
		return _impl->assign(assignElem, node, content);
	}
	virtual void assign(const std::string& location, const Data& data) {
		return _impl->assign(location, data);
	}

	virtual void init(const Arabica::DOM::Element<std::string>& dataElem,
	                  const Arabica::DOM::Node<std::string>& node,
	                  const std::string& content) {
		return _impl->init(dataElem, node, content);
	}
	virtual void init(const std::string& location, const Data& data) {
		return _impl->init(location, data);
	}

	virtual bool isDeclared(const std::string& expr) {
		return _impl->isDeclared(expr);
	}

	size_t replaceExpressions(std::string& content) {
		return _impl->replaceExpressions(content);
	}

	std::string andExpressions(std::list<std::string> expressions) {
		return _impl->andExpressions(expressions);
	}

	virtual void setInterpreter(InterpreterImpl* interpreter) {
		_impl->setInterpreter(interpreter);
	}

protected:
	boost::shared_ptr<DataModelImpl> _impl;
};

class USCXML_API Factory {
public:
	Factory(Factory* parentFactory);

	void registerIOProcessor(IOProcessorImpl* ioProcessor);
	void registerDataModel(DataModelImpl* dataModel);
	void registerInvoker(InvokerImpl* invoker);
	void registerExecutableContent(ExecutableContentImpl* executableContent);

	boost::shared_ptr<DataModelImpl> createDataModel(const std::string& type, InterpreterImpl* interpreter);
	boost::shared_ptr<IOProcessorImpl> createIOProcessor(const std::string& type, InterpreterImpl* interpreter);
	boost::shared_ptr<InvokerImpl> createInvoker(const std::string& type, InterpreterImpl* interpreter);
	boost::shared_ptr<ExecutableContentImpl> createExecutableContent(const std::string& localName, const std::string& nameSpace, InterpreterImpl* interpreter);

	std::map<std::string, IOProcessorImpl*> getIOProcessors();

	static Factory* getInstance();

	std::map<std::string, DataModelImpl*> _dataModels;
	std::map<std::string, std::string> _dataModelAliases;
	std::map<std::string, IOProcessorImpl*> _ioProcessors;
	std::map<std::string, std::string> _ioProcessorAliases;
	std::map<std::string, InvokerImpl*> _invokers;
	std::map<std::string, std::string> _invokerAliases;
	std::map<std::pair<std::string, std::string>, ExecutableContentImpl*> _executableContent;

	static std::string pluginPath;

protected:
#ifdef BUILD_AS_PLUGINS
	pluma::Pluma pluma;
#endif

	Factory();
	~Factory();
	Factory* _parentFactory;
	static Factory* _instance;

};


}

#endif /* end of include guard: FACTORY_H_5WKLGPRB */
