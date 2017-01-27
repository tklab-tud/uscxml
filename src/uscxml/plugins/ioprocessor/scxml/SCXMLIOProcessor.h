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

#ifndef SCXMLIOProcessor_H_2CUY93KU
#define SCXMLIOProcessor_H_2CUY93KU

#include "uscxml/config.h"
#include "uscxml/plugins/IOProcessorImpl.h"

#ifdef BUILD_AS_PLUGINS
#include "uscxml/plugins/Plugins.h"
#endif

namespace uscxml {

/**
 * @ingroup ioproc
 * The scxml I/O processor as per standard.
 */
class SCXMLIOProcessor : public IOProcessorImpl {
public:
	SCXMLIOProcessor();
	virtual ~SCXMLIOProcessor();
	virtual std::shared_ptr<IOProcessorImpl> create(uscxml::IOProcessorCallbacks* callbacks);

	virtual std::list<std::string> getNames() {
		std::list<std::string> names;
		names.push_back("scxml");
		names.push_back("http://www.w3.org/TR/scxml/#SCXMLEventProcessor");
		return names;
	}

	virtual void eventFromSCXML(const std::string& target, const Event& event);
	virtual bool isValidTarget(const std::string& target);

	Data getDataModelVariables();
};

#ifdef BUILD_AS_PLUGINS
PLUMA_INHERIT_PROVIDER(SCXMLIOProcessor, IOProcessorImpl)
#endif

}

#endif /* end of include guard: SCXMLIOProcessor_H_2CUY93KU */
