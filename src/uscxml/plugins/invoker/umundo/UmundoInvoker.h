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

#ifndef UMUNDOINVOKER_H_77YXQGU7
#define UMUNDOINVOKER_H_77YXQGU7

#include <uscxml/Interpreter.h>
#include <google/protobuf/message.h>
#include <umundo/core.h>
#include <umundo/s11n.h>
#include <umundo/rpc.h>
#include <umundo/s11n/protobuf/PBSerializer.h>

#include "JSON.pb.h"

#ifdef BUILD_AS_PLUGINS
#include "uscxml/plugins/Plugins.h"
#endif

namespace uscxml {

class Interpreter;

class UmundoInvoker : public InvokerImpl, public umundo::TypedReceiver, public umundo::ResultSet<umundo::ServiceDescription>, public umundo::TypedGreeter {
public:
	UmundoInvoker();
	virtual ~UmundoInvoker();
	virtual boost::shared_ptr<InvokerImpl> create(InterpreterImpl* interpreter);

	virtual std::set<std::string> getNames() {
		std::set<std::string> names;
		names.insert("umundo");
		names.insert("http://umundo.tk.informatik.tu-darmstadt.de/");
		names.insert("http://umundo.tk.informatik.tu-darmstadt.de");
		return names;
	}

	virtual Data getDataModelVariables();
	virtual void send(const SendRequest& req);
	virtual void cancel(const std::string sendId);
	virtual void invoke(const InvokeRequest& req);

	virtual void receive(void* object, umundo::Message* msg);

	virtual void added(umundo::ServiceDescription);
	virtual void removed(umundo::ServiceDescription);
	virtual void changed(umundo::ServiceDescription);

	virtual void welcome(umundo::TypedPublisher atPub, const umundo::SubscriberStub& sub);
	virtual void farewell(umundo::TypedPublisher fromPub, const umundo::SubscriberStub& sub);

protected:
	bool _isService;

	bool dataToJSONbuf(JSONProto* msg, Data& data);
	bool dataToProtobuf(google::protobuf::Message* msg, Data& data);

	bool jsonbufToData(Data& data, const JSONProto& json);
	bool protobufToData(Data& data, const google::protobuf::Message& msg);

	umundo::Node* _node;
	umundo::Discovery* _discovery;
	umundo::TypedPublisher* _pub;
	umundo::TypedSubscriber* _sub;

	umundo::ServiceFilter* _svcFilter;
	umundo::ServiceManager* _svcMgr;
	std::map<umundo::ServiceDescription, umundo::ServiceStub*> _svcs;
};

#ifdef BUILD_AS_PLUGINS
PLUMA_INHERIT_PROVIDER(UmundoInvoker, InvokerImpl);
#endif

}


#endif /* end of include guard: UMUNDOINVOKER_H_77YXQGU7 */
