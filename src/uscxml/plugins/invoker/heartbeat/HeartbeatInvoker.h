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

#ifndef HEARTBEATINVOKER_H_W09J90F0
#define HEARTBEATINVOKER_H_W09J90F0

#include <uscxml/Interpreter.h>

#ifdef BUILD_AS_PLUGINS
#include "uscxml/plugins/Plugins.h"
#endif

namespace uscxml {

class HeartbeatInvoker : public InvokerImpl {
public:
	HeartbeatInvoker();
	virtual ~HeartbeatInvoker();
	virtual boost::shared_ptr<InvokerImpl> create(InterpreterImpl* interpreter);

	virtual std::set<std::string> getNames() {
		std::set<std::string> names;
		names.insert("heartbeat");
		names.insert("http://uscxml.tk.informatik.tu-darmstadt.de/#heartbeat");
		return names;
	}

	virtual Data getDataModelVariables();
	virtual void send(const SendRequest& req);
	virtual void cancel(const std::string sendId);
	virtual void invoke(const InvokeRequest& req);

	static void dispatch(void* instance, std::string name);

protected:
	Event _event;

};

class HeartbeatDispatcher : public DelayedEventQueue {
public:
	static HeartbeatDispatcher* getInstance();
protected:
	static HeartbeatDispatcher* _instance;
	HeartbeatDispatcher();
};

#ifdef BUILD_AS_PLUGINS
PLUMA_INHERIT_PROVIDER(HeartbeatInvoker, InvokerImpl);
#endif

}


#endif /* end of include guard: HEARTBEATINVOKER_H_W09J90F0 */
