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

#include "uscxml/config.h"
#include "uscxml/plugins/DataModelImpl.h"
#include <list>

#ifdef BUILD_AS_PLUGINS
#include "uscxml/plugins/Plugins.h"
#endif

namespace uscxml {

class PromelaDataModel : public DataModelImpl {
public:
	PromelaDataModel();
	virtual ~PromelaDataModel();
	virtual std::shared_ptr<DataModelImpl> create(DataModelCallbacks* callbacks);

	virtual std::list<std::string> getNames() {
		std::list<std::string> names;
		names.push_back("promela");
		return names;
	}

	virtual void addExtension(DataModelExtension* ext);

	virtual bool isValidSyntax(const std::string& expr);

	virtual void setEvent(const Event& event);

	// foreach
	virtual uint32_t getLength(const std::string& expr);
	virtual void setForeach(const std::string& item,
	                        const std::string& array,
	                        const std::string& index,
	                        uint32_t iteration);

	virtual bool evalAsBool(const std::string& expr);
	virtual Data evalAsData(const std::string& expr);
	virtual Data getAsData(const std::string& content);

	virtual bool isDeclared(const std::string& expr);

	virtual void assign(const std::string& location,
	                    const Data& data,
	                    const std::map<std::string, std::string>& attr = std::map<std::string, std::string>());
	virtual void init(const std::string& location,
	                  const Data& data,
	                  const std::map<std::string, std::string>& attr = std::map<std::string, std::string>());

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
PLUMA_INHERIT_PROVIDER(PromelaDataModel, DataModelImpl)
#endif

}

#endif /* end of include guard: PROMELADATAMODEL_H_4VG0TDMU */
