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

#ifndef SAMPLEIOPROCESSOR_H_2CUY93KU
#define SAMPLEIOPROCESSOR_H_2CUY93KU

#include "uscxml/Factory.h"

#ifdef BUILD_AS_PLUGINS
#include "uscxml/plugins/Plugins.h"
#endif

#if defined(_WIN32) && !defined(USCXML_STATIC)
#	if (defined ioprocessor_sample_EXPORTS || defined USCXML_EXPORT)
#		define USCXML_PLUGIN_API __declspec(dllexport)
#	else
#		define USCXML_PLUGIN_API __declspec(dllimport)
#	endif
#else
#	define USCXML_PLUGIN_API
#endif

namespace uscxml {

class USCXML_PLUGIN_API SampleIOProcessor : public IOProcessorImpl {
public:
	SampleIOProcessor();
	virtual ~SampleIOProcessor();
	virtual boost::shared_ptr<IOProcessorImpl> create(uscxml::InterpreterImpl* interpreter);

	virtual std::list<std::string> getNames() {
		std::list<std::string> names;
		names.push_back("sample");
		names.push_back("http://www.w3.org/TR/scxml/#SampleEventProcessor");
		return names;
	}

	virtual void send(const SendRequest& req);
	Data getDataModelVariables();

protected:
};

#ifdef BUILD_AS_PLUGINS
PLUMA_INHERIT_PROVIDER(SampleIOProcessor, IOProcessorImpl);
#endif

}

#endif /* end of include guard: SAMPLEIOPROCESSOR_H_2CUY93KU */