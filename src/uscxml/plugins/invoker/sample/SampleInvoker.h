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

#ifndef SAMPLEINVOKER_H_W09J90F0
#define SAMPLEINVOKER_H_W09J90F0

#include <uscxml/Interpreter.h>

#ifdef BUILD_AS_PLUGINS
#include "uscxml/plugins/Plugins.h"
#endif

namespace uscxml {

class SampleInvoker : public InvokerImpl {
public:
	SampleInvoker();
	virtual ~SampleInvoker();
	virtual boost::shared_ptr<InvokerImpl> create(InterpreterImpl* interpreter);

	virtual std::list<std::string> getNames() {
		std::list<std::string> names;
		names.push_back("sample");
		names.push_back("http://uscxml.tk.informatik.tu-darmstadt.de/#sample");
		return names;
	}

	virtual Data getDataModelVariables();
	virtual void send(const SendRequest& req);
	virtual void cancel(const std::string sendId);
	virtual void invoke(const InvokeRequest& req);

protected:
};

#ifdef BUILD_AS_PLUGINS
PLUMA_INHERIT_PROVIDER(SampleInvoker, InvokerImpl);
#endif

}


#endif /* end of include guard: SAMPLEINVOKER_H_W09J90F0 */
