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

#ifndef EXECUTABLECONTENT_H_1E028A2D
#define EXECUTABLECONTENT_H_1E028A2D

#include "uscxml/Common.h"

#include <string>
#include <memory>
#include <sstream>

// forward declare
namespace XERCESC_NS {
class DOMElement;
}

namespace uscxml {

class ExecutableContentImpl;

/**
 * @ingroup element
 * @ingroup facade
 * Facade for all executable content implementations.
 */
class USCXML_API ExecutableContent {
public:
	PIMPL_OPERATORS(ExecutableContent);

	std::string getLocalName();
	std::string getNamespace();
	void enterElement(XERCESC_NS::DOMElement* node);
	void exitElement(XERCESC_NS::DOMElement* node);
	bool processChildren();

protected:
	std::shared_ptr<ExecutableContentImpl> _impl;

};

}

#endif /* end of include guard: EXECUTABLECONTENT_H_1E028A2D */
