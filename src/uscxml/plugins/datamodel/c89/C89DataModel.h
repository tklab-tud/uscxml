/**
 *  @file
 *  @author     2016 Stefan Radomski (stefan.radomski@cs.tu-darmstadt.de)
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

#ifndef C89DATAMODEL_H_A0FF45FA
#define C89DATAMODEL_H_A0FF45FA

#include "uscxml/plugins/DataModelImpl.h"
#include <list>

#define UNIX_HOST
#define PICOC_STACK_SIZE (128*1024)              /* space for the the stack */

extern "C" {
#include "picoc.h"
#undef min
}

#ifdef BUILD_AS_PLUGINS
#include "uscxml/plugins/Plugins.h"
#endif


namespace uscxml {
class Event;
class Data;
}

namespace uscxml {

/**
 * @ingroup datamodel
 * C89 (ANSI-C) data-model.
 */

class C89DataModel : public DataModelImpl {
public:
	C89DataModel();
	virtual ~C89DataModel();
	virtual std::shared_ptr<DataModelImpl> create(DataModelCallbacks* callbacks);

	virtual void addExtension(DataModelExtension* ext);

	virtual std::list<std::string> getNames() {
		std::list<std::string> names;
		names.push_back("c89");
		names.push_back("ansi-c");
		return names;
	}

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

	virtual void assign(const std::string& location, const Data& data);
	virtual void init(const std::string& location, const Data& data);

	virtual std::string andExpressions(std::list<std::string>);

protected:
	Picoc _pc;
};

#ifdef BUILD_AS_PLUGINS
PLUMA_INHERIT_PROVIDER(C89DataModel, DataModelImpl);
#endif

}

#endif /* end of include guard: C89DATAMODEL_H_A0FF45FA */
