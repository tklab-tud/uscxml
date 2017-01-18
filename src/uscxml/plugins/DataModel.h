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
#include "uscxml/messages/Event.h"

#include <list>
#include <string>
#include <memory>

namespace uscxml {

class DataModelImpl;
class DataModelExtension;

/**
 * @ingroup datamodel
 * @ingroup facade
 * The facade for data-models.
 */
class USCXML_API DataModel {
public:

	PIMPL_OPERATORS(DataModel);

	/// @copydoc DataModelImpl::getNames()
	virtual std::list<std::string> getNames();
	/// @copydoc DataModelImpl::isValidSyntax()
	virtual bool isValidSyntax(const std::string& expr);

	/// @copydoc DataModelImpl::setEvent()
	virtual void setEvent(const Event& event);

	/// @copydoc DataModelImpl::getAsData()
	virtual Data getAsData(const std::string& content);
	/// @copydoc DataModelImpl::evalAsData()
	virtual Data evalAsData(const std::string& content);
	/// @copydoc DataModelImpl::evalAsBool()
	virtual bool evalAsBool(const std::string& expr);

	/// @copydoc DataModelImpl::getLength()
	virtual uint32_t getLength(const std::string& expr);
	/// @copydoc DataModelImpl::setForeach()
	virtual void setForeach(const std::string& item,
	                        const std::string& array,
	                        const std::string& index,
	                        uint32_t iteration);

	/// @copydoc DataModelImpl::assign()
	virtual void assign(const std::string& location,
	                    const Data& data,
	                    const std::map<std::string, std::string>& attr = std::map<std::string, std::string>());
	/// @copydoc DataModelImpl::init()
	virtual void init(const std::string& location,
	                  const Data& data,
	                  const std::map<std::string, std::string>& attr = std::map<std::string, std::string>());

	/// @copydoc DataModelImpl::isDeclared()
	virtual bool isDeclared(const std::string& expr);

	/// @copydoc DataModelImpl::replaceExpressions()
	size_t replaceExpressions(std::string& content);

	/// @copydoc DataModelImpl::addExtension()
	virtual void addExtension(DataModelExtension* ext);

protected:
	std::shared_ptr<DataModelImpl> _impl;
};


}


#endif /* end of include guard: DATAMODEL_H_F1F776F9 */
