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

#ifndef NULLDATAMODEL_H_KN8TWG0V
#define NULLDATAMODEL_H_KN8TWG0V

#include "uscxml/config.h"
#include "uscxml/plugins/DataModelImpl.h"
#include <list>

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
 * NULL data-model.
 */
class NullDataModel : public DataModelImpl {
public:
	NullDataModel();
	virtual ~NullDataModel();
	virtual std::shared_ptr<DataModelImpl> create(DataModelCallbacks* callbacks);

	virtual std::list<std::string> getNames() {
		std::list<std::string> names;
		names.push_back("null");
		return names;
	}

	virtual bool validate(const std::string& location, const std::string& schema) {
		return true;
	}
	virtual bool isValidSyntax(const std::string& expr) {
		return true; // overwrite when datamodel supports it
	}
	virtual void setEvent(const Event& event) {}

	size_t replaceExpressions(std::string& content) {
		return 0;
	}

	// foreach
	virtual uint32_t getLength(const std::string& expr) {
		return 0;
	}
	virtual void setForeach(const std::string& item,
	                        const std::string& array,
	                        const std::string& index,
	                        uint32_t iteration) {}

	virtual Data getAsData(const std::string& content);

	virtual Data evalAsData(const std::string& content) {
		return getAsData(content);
	}
	virtual std::string evalAsString(const std::string& expr) {
		return expr;
	}

	virtual bool evalAsBool(const XERCESC_NS::DOMElement* scriptNode,
	                        const std::string& expr);
	virtual bool evalAsBool(const std::string& expr) {
		return evalAsBool(NULL, expr);
	}

	virtual bool isDeclared(const std::string& expr) {
		return true;
	}

	virtual void assign(const std::string& location, const Data& data, const std::map<std::string, std::string>& attr) {}
	virtual void init(const std::string& location, const Data& data, const std::map<std::string, std::string>& attr) {}

	virtual void setCallbacks(DataModelCallbacks* callbacks) {
		_callbacks = callbacks;
	}

	virtual void addExtension(DataModelExtension* ext) {}

protected:

};

#ifdef BUILD_AS_PLUGINS
PLUMA_INHERIT_PROVIDER(NullDataModel, DataModelImpl)
#endif

}

#endif /* end of include guard: NULLDATAMODEL_H_KN8TWG0V */
