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

	virtual void welcome(umundo::TypedPublisher, const std::string& nodeId, const std::string& subId);
	virtual void farewell(umundo::TypedPublisher, const std::string& nodeId, const std::string& subId);

protected:
	bool _isService;

	bool dataToJSONbuf(JSONProto* msg, Data& data);
	bool dataToProtobuf(google::protobuf::Message* msg, Data& data);

	bool jsonbufToData(Data& data, const JSONProto& json);
	bool protobufToData(Data& data, const google::protobuf::Message& msg);

	boost::shared_ptr<umundo::Node> _node;
	umundo::TypedPublisher* _pub;
	umundo::TypedSubscriber* _sub;

	umundo::ServiceFilter* _svcFilter;
	umundo::ServiceManager* _svcMgr;
	std::map<umundo::ServiceDescription, umundo::ServiceStub*> _svcs;

	static std::multimap<std::string, std::pair<std::string, boost::weak_ptr<umundo::Node> > > _nodes;
	typedef std::multimap<std::string, std::pair<std::string, boost::weak_ptr<umundo::Node> > > _nodes_t;
	static boost::shared_ptr<umundo::Node> getNode(InterpreterImpl* interpreter, const std::string& domain);
};

#ifdef BUILD_AS_PLUGINS
PLUMA_INHERIT_PROVIDER(UmundoInvoker, InvokerImpl);
#endif

}


#endif /* end of include guard: UMUNDOINVOKER_H_77YXQGU7 */
