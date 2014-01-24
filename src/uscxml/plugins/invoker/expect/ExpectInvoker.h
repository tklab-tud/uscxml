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

#ifndef EXPECTINVOKER_H_W02590F0
#define EXPECTINVOKER_H_W02590F0

#include <uscxml/Interpreter.h>

#ifdef BUILD_AS_PLUGINS
#include "uscxml/plugins/Plugins.h"
#endif

#include <tcl.h>
#include <expect_tcl.h>
#include <expect.h>

namespace uscxml {

class ExpectInvoker : public InvokerImpl {
public:
	struct EventContext {
		InvokeRequest invokeReq;
		SendRequest sendReq;
		ExpectInvoker* instance;
	};

	ExpectInvoker();
	virtual ~ExpectInvoker();
	virtual boost::shared_ptr<InvokerImpl> create(InterpreterImpl* interpreter);

	virtual std::set<std::string> getNames() {
		std::set<std::string> names;
		names.insert("expect");
		names.insert("http://uscxml.tk.informatik.tu-darmstadt.de/#expect");
		return names;
	}

	virtual Data getDataModelVariables();
	virtual void send(const SendRequest& req);
	virtual void cancel(const std::string sendId);
	virtual void invoke(const InvokeRequest& req);

protected:

	static void send(void *userdata, const std::string event);
	static void invoke(void *userdata, const std::string event);

	static Tcl_Interp* _tcl;
	FILE* _cmdFP;
	int _cmdFD;

	DelayedEventQueue* _eventQueue;

};

#ifdef BUILD_AS_PLUGINS
PLUMA_INHERIT_PROVIDER(ExpectInvoker, InvokerImpl);
#endif

}


#endif /* end of include guard: EXPECTINVOKER_H_W02590F0 */
