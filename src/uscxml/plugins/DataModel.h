/**
 *  @file
 *  @author     2012-2014 Stefan Radomski (stefan.radomski@cs.tu-darmstadt.de)
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

#ifndef DATAMODEL_H_F1F776F9
#define DATAMODEL_H_F1F776F9

#include "uscxml/Common.h"
#include "uscxml/plugins/EventHandler.h"

#include <list>
#include <boost/shared_ptr.hpp>
#include <string>
#include <sstream>

#include "DOM/Document.hpp"

namespace uscxml {

class InterpreterImpl;

class USCXML_API DataModelImpl {
public:
	virtual ~DataModelImpl() {}
	virtual boost::shared_ptr<DataModelImpl> create(InterpreterImpl* interpreter) = 0;
	virtual std::list<std::string> getNames() = 0;

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

	virtual std::string andExpressions(std::list<std::string>) {
		return "";
	}

protected:
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

	virtual std::list<std::string> getNames() {
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


}


#endif /* end of include guard: DATAMODEL_H_F1F776F9 */
