#ifndef UMUNDOINVOKER_H_77YXQGU7
#define UMUNDOINVOKER_H_77YXQGU7

#include <umundo/core.h>
#include <umundo/s11n.h>
#include <umundo/rpc.h>
#include <umundo/s11n/protobuf/PBSerializer.h>
#include <uscxml/Interpreter.h>
#include <google/protobuf/message.h>

#ifdef BUILD_AS_PLUGINS
#include "uscxml/plugins/Plugins.h"
#endif

namespace uscxml {

class Interpreter;

class UmundoInvoker : public InvokerImpl, public umundo::TypedReceiver, public umundo::ResultSet<umundo::ServiceDescription> {
public:
	UmundoInvoker();
	virtual ~UmundoInvoker();
	virtual boost::shared_ptr<IOProcessorImpl> create(Interpreter* interpreter);

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
	virtual void sendToParent(const SendRequest& req);

	virtual void receive(void* object, umundo::Message* msg);

	virtual void added(umundo::ServiceDescription);
	virtual void removed(umundo::ServiceDescription);
	virtual void changed(umundo::ServiceDescription);

protected:
	std::string _invokeId;
	bool _isService;

	bool dataToProtobuf(google::protobuf::Message* msg, Data& data);
	bool protobufToData(Data& data, const google::protobuf::Message& msg);

	umundo::Node* _node;
	umundo::TypedPublisher* _pub;
	umundo::TypedSubscriber* _sub;

	umundo::ServiceFilter _svcFilter;
	umundo::ServiceManager _svcMgr;
	std::map<umundo::ServiceDescription, umundo::ServiceStub*> _svcs;

	static std::multimap<std::string, std::pair<std::string, umundo::Node*> > _nodes;
	typedef std::multimap<std::string, std::pair<std::string, umundo::Node*> > _nodes_t;
	static umundo::Node* getNode(Interpreter* interpreter, const std::string& domain);
};

#ifdef BUILD_AS_PLUGINS
PLUMA_INHERIT_PROVIDER(UmundoInvoker, InvokerImpl);
#endif

}


#endif /* end of include guard: UMUNDOINVOKER_H_77YXQGU7 */
