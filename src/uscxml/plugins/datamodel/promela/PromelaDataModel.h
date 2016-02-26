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

#ifndef PROMELADATAMODEL_H_4VG0TDMU
#define PROMELADATAMODEL_H_4VG0TDMU

#include "uscxml/InterpreterInfo.h"
#include "uscxml/plugins/DataModel.h"
#include <list>

#ifdef BUILD_AS_PLUGINS
#include "uscxml/plugins/Plugins.h"
#endif

namespace uscxml {

class PromelaDataModel : public DataModelImpl {
public:
	PromelaDataModel();
	virtual ~PromelaDataModel();
	virtual boost::shared_ptr<DataModelImpl> create(InterpreterInfo* interpreter);

	virtual std::list<std::string> getNames() {
		std::list<std::string> names;
		names.push_back("promela");
		return names;
	}

	virtual void setEvent(const Event& event);

	virtual void registerIOProcessor(const std::string& name, const IOProcessor& ioprocessor);

	virtual bool validate(const std::string& location, const std::string& schema);
	virtual bool isLocation(const std::string& expr);
	virtual bool isValidSyntax(const std::string& expr);

	virtual uint32_t getLength(const std::string& expr);
	virtual void setForeach(const std::string& item,
	                        const std::string& array,
	                        const std::string& index,
	                        uint32_t iteration);

	virtual void pushContext();
	virtual void popContext();

	virtual void assign(const Arabica::DOM::Element<std::string>& assignElem,
	                    const Arabica::DOM::Node<std::string>& node,
	                    const std::string& content);
	virtual void assign(const std::string& location, const Data& data);

	virtual void init(const Arabica::DOM::Element<std::string>& dataElem,
	                  const Arabica::DOM::Node<std::string>& node,
	                  const std::string& content);
	virtual void init(const std::string& location, const Data& data);

	virtual void eval(const Arabica::DOM::Element<std::string>& scriptElem,
	                  const std::string& expr);

	virtual bool isDeclared(const std::string& expr);

	virtual Data getStringAsData(const std::string& content);

	virtual std::string evalAsString(const std::string& expr);
	virtual bool evalAsBool(const Arabica::DOM::Element<std::string>& node, const std::string& expr);
	virtual bool evalAsBool(const std::string& expr);

	virtual std::string andExpressions(std::list<std::string> expressions);

protected:

	int dataToInt(const Data& data);
	bool dataToBool(const Data& data);

	void evaluateDecl(void* ast);
	Data evaluateExpr(void* ast);
	void evaluateStmnt(void* ast);

	void evaluateDecl(const std::string& expr);
	Data evaluateExpr(const std::string& expr);
	void evaluateStmnt(const std::string& expr);

	void setVariable(void* ast, const Data& value);
	Data getVariable(void* ast);

	void adaptType(Data& data);

	int _lastMType;

	Event _event;
	std::string _name;
	std::string _sessionId;

	Data _variables;

};

#ifdef BUILD_AS_PLUGINS
PLUMA_INHERIT_PROVIDER(PromelaDataModel, DataModelImpl);
#endif

}

#endif /* end of include guard: PROMELADATAMODEL_H_4VG0TDMU */
