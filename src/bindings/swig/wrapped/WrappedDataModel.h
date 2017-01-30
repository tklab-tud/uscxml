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

#ifndef WRAPPEDDATAMODEL_H_DBAAD6AF
#define WRAPPEDDATAMODEL_H_DBAAD6AF

#include <vector>
#include <list>
#include <ostream>
#include <string>

#include <xercesc/dom/DOM.hpp>

#include "../../../uscxml/plugins/DataModelImpl.h"

namespace uscxml {

class WrappedDataModel : public DataModelImpl {
public:

	WrappedDataModel();
	virtual ~WrappedDataModel();

	virtual std::shared_ptr<DataModelImpl> create(DataModelCallbacks* callbacks) {
		std::shared_ptr<WrappedDataModel> dm(create());
		dm->callbacks = callbacks;
		return dm;
	}

	virtual std::list<std::string> getNames() {
		return std::list<std::string>();
	}

	virtual WrappedDataModel* create() {
		return new WrappedDataModel();
	}

	virtual bool isValidSyntax(const std::string& expr) {
		return true;
	}

	virtual void setEvent(const Event& event) {}

	// foreach
	virtual uint32_t getLength(const std::string& expr) {
		return 0;
	}

	virtual void setForeach(const std::string& item,
	                        const std::string& array,
	                        const std::string& index,
	                        uint32_t iteration) {}

	virtual Data getAsData(const std::string& content) {
		return Data();
	}
	virtual Data evalAsData(const std::string& expr) {
		return Data();
	}
	virtual bool evalAsBool(const std::string& expr) {
		return true;
	}

	virtual bool isDeclared(const std::string& expr) {
		return true;
	}

	virtual void assign(const std::string& location,
	                    const Data& data,
	                    const std::map<std::string, std::string>& attr) {}
	virtual void init(const std::string& location,
	                  const Data& data,
	                  const std::map<std::string, std::string>& attr) {}

	virtual void addExtension(DataModelExtension* ext) {
	}

protected:
	DataModelCallbacks* callbacks;
};

}

#endif /* end of include guard: WRAPPEDDATAMODEL_H_DBAAD6AF */
