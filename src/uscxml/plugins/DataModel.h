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

#include "uscxml/config.h"
#include "uscxml/Common.h"
#include "uscxml/InterpreterInfo.h"
#include "uscxml/plugins/EventHandler.h"

#ifndef TIME_BLOCK
#	ifdef BUILD_PROFILING
#		include "uscxml/concurrency/Timer.h"
#		define TIME_BLOCK Measurement msm(&timer);
#	else
#		define TIME_BLOCK
#	endif
#endif

#include <list>
#include <boost/shared_ptr.hpp>
#include <string>
#include <sstream>

#include "DOM/Document.hpp"

namespace uscxml {

class InterpreterImpl;
class DataModelImpl;

class USCXML_API DataModelExtension {
public:
	DataModelExtension() : dm(NULL) {}
	virtual ~DataModelExtension() {}
	virtual std::string provides() = 0;
	virtual Data getValueOf(const std::string& member) = 0;
	virtual void setValueOf(const std::string& member, const Data& data) = 0;
	DataModelImpl* dm;
};

class USCXML_API DataModelImpl {
public:
	virtual ~DataModelImpl() {}
	virtual boost::shared_ptr<DataModelImpl> create(InterpreterInfo* interpreter) = 0;
	virtual std::list<std::string> getNames() = 0;

	virtual bool validate(const std::string& location, const std::string& schema) = 0;
	virtual bool isLocation(const std::string& expr) = 0;
	virtual bool isValidSyntax(const std::string& expr) {
		return true; // overwrite when datamodel supports it
	}
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

	virtual bool evalAsBool(const Arabica::DOM::Element<std::string>& scriptNode,
	                        const std::string& expr) = 0;
	virtual bool evalAsBool(const std::string& expr) {
		return evalAsBool(Arabica::DOM::Element<std::string>(), expr);
	}

	virtual bool isDeclared(const std::string& expr) = 0;

	/**
	 * test147:
	 *     <data id="Var1" expr="0"/>
	 *
	 * test150:
	 *  <data id="Var3">
	 *    [1,2,3]
	 *  </data>
	 *
	 * test277:
	 *  <data id="Var1" expr="return"/>
	 *
	 */
	virtual void assign(const Arabica::DOM::Element<std::string>& assignElem,
	                    const Arabica::DOM::Node<std::string>& node,
	                    const std::string& content) = 0;
	virtual void assign(const std::string& location, const Data& data) = 0;

	virtual void init(const Arabica::DOM::Element<std::string>& dataElem,
	                  const Arabica::DOM::Node<std::string>& node,
	                  const std::string& content) = 0;
	virtual void init(const std::string& location, const Data& data) = 0;

	virtual void setInterpreter(InterpreterInfo* interpreter) {
		_interpreter = interpreter;
	}

	virtual void addExtension(DataModelExtension* ext);
	virtual std::string andExpressions(std::list<std::string>) {
		return "";
	}

protected:
	InterpreterInfo* _interpreter;
};

class USCXML_API DataModel {
public:

	DataModel() : _impl() {}
	DataModel(const boost::shared_ptr<DataModelImpl> impl) : _impl(impl) { }
	DataModel(const DataModel& other) : _impl(other._impl) { }
	virtual ~DataModel() {};

	operator bool()                         const     {
		return !!_impl;
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
		TIME_BLOCK
		return _impl->getNames();
	}

	virtual bool validate(const std::string& location, const std::string& schema) {
		TIME_BLOCK
		return _impl->validate(location, schema);
	}
	virtual bool isLocation(const std::string& expr) {
		TIME_BLOCK
		return _impl->isLocation(expr);
	}
	virtual bool isValidSyntax(const std::string& expr) {
		TIME_BLOCK
		return _impl->isValidSyntax(expr);
	}

	virtual void setEvent(const Event& event) {
		TIME_BLOCK
		return _impl->setEvent(event);
	}
	virtual Data getStringAsData(const std::string& content) {
		TIME_BLOCK
		return _impl->getStringAsData(content);
	}

	virtual void pushContext() {
		TIME_BLOCK
		return _impl->pushContext();
	}
	virtual void popContext() {
		TIME_BLOCK
		return _impl->popContext();
	}

	virtual void eval(const Arabica::DOM::Element<std::string>& scriptElem,
	                  const std::string& expr) {
		TIME_BLOCK
		return _impl->eval(scriptElem, expr);
	}
	virtual std::string evalAsString(const std::string& expr) {
		TIME_BLOCK
		return _impl->evalAsString(expr);
	}
	virtual bool evalAsBool(const std::string& expr) {
		TIME_BLOCK
		return _impl->evalAsBool(expr);
	}
	virtual bool evalAsBool(const Arabica::DOM::Element<std::string>& scriptNode,
	                        const std::string& expr) {
		TIME_BLOCK
		return _impl->evalAsBool(scriptNode, expr);
	}

	virtual uint32_t getLength(const std::string& expr) {
		TIME_BLOCK
		return _impl->getLength(expr);
	}
	virtual void setForeach(const std::string& item,
	                        const std::string& array,
	                        const std::string& index,
	                        uint32_t iteration) {
		TIME_BLOCK
		return _impl->setForeach(item, array, index, iteration);
	}

	virtual void assign(const Arabica::DOM::Element<std::string>& assignElem,
	                    const Arabica::DOM::Node<std::string>& node,
	                    const std::string& content) {
		TIME_BLOCK
		return _impl->assign(assignElem, node, content);
	}
	virtual void assign(const std::string& location, const Data& data) {
		TIME_BLOCK
		return _impl->assign(location, data);
	}

	virtual void init(const Arabica::DOM::Element<std::string>& dataElem,
	                  const Arabica::DOM::Node<std::string>& node,
	                  const std::string& content) {
		TIME_BLOCK
		return _impl->init(dataElem, node, content);
	}
	virtual void init(const std::string& location, const Data& data) {
		TIME_BLOCK
		return _impl->init(location, data);
	}

	virtual bool isDeclared(const std::string& expr) {
		TIME_BLOCK
		return _impl->isDeclared(expr);
	}

	size_t replaceExpressions(std::string& content) {
		TIME_BLOCK
		return _impl->replaceExpressions(content);
	}

	std::string andExpressions(std::list<std::string> expressions) {
		TIME_BLOCK
		return _impl->andExpressions(expressions);
	}

	virtual void setInterpreter(InterpreterInfo* interpreter) {
		TIME_BLOCK
		_impl->setInterpreter(interpreter);
	}

	virtual void addExtension(DataModelExtension* ext) {
		TIME_BLOCK
		_impl->addExtension(ext);
	}

#ifdef BUILD_PROFILING
	Timer timer;
#endif

protected:
	boost::shared_ptr<DataModelImpl> _impl;
};


}


#endif /* end of include guard: DATAMODEL_H_F1F776F9 */
