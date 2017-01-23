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

#ifndef IOPROCESSOR_H_CF4F4135
#define IOPROCESSOR_H_CF4F4135

#include "uscxml/Common.h"
#include "uscxml/plugins/EventHandler.h"
#include "uscxml/messages/Event.h"

namespace uscxml {

class IOProcessorImpl;
class InterpreterImpl;

/**
 * @ingroup ioproc
 * @ingroup facade
 * Facade for I/O processors.
 */
class USCXML_API IOProcessor : public EventHandler {
public:

	PIMPL_OPERATORS_INHERIT(IOProcessor, EventHandler)

	/// @copydoc IOProcessorImpl::eventFromSCXML
	virtual void eventFromSCXML(const std::string& target, const Event& event);

	/// @copydoc IOProcessorImpl::isValidTarget
	virtual bool isValidTarget(const std::string& target);


protected:
	std::shared_ptr<IOProcessorImpl> _impl;
	friend class InterpreterImpl;
};


}


#endif /* end of include guard: IOPROCESSOR_H_CF4F4135 */
