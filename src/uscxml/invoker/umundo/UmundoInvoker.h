#ifndef UMUNDOINVOKER_H_77YXQGU7
#define UMUNDOINVOKER_H_77YXQGU7

#include <umundo/core.h>
#include <umundo/s11n.h>
#include <umundo/rpc.h>
#include <umundo/s11n/protobuf/PBSerializer.h>
#include <google/protobuf/message.h>
#include "uscxml/Factory.h"

namespace uscxml {

class Interpreter;
  
class UmundoInvoker : public Invoker, public umundo::TypedReceiver, public umundo::ResultSet<umundo::ServiceDescription> {
public:
	UmundoInvoker();
  virtual ~UmundoInvoker();
  virtual Invoker* create(Interpreter* interpreter);
  
  virtual Data getDataModelVariables();
  virtual void send(SendRequest& req);
  virtual void cancel(const std::string sendId);
  virtual void invoke(InvokeRequest& req);
  virtual void sendToParent(SendRequest& req);

  virtual void receive(void* object, umundo::Message* msg);

  virtual void added(boost::shared_ptr<umundo::ServiceDescription>);
	virtual void removed(boost::shared_ptr<umundo::ServiceDescription>);
	virtual void changed(boost::shared_ptr<umundo::ServiceDescription>);
  
protected:
  std::string _invokeId;
  Interpreter* _interpreter;
  bool _isService;
  
  bool dataToProtobuf(google::protobuf::Message* msg, Data& data);
  bool protobufToData(Data& data, const google::protobuf::Message& msg);

  umundo::TypedPublisher* _pub;
  umundo::TypedSubscriber* _sub;
  boost::shared_ptr<umundo::Node> _node;
    
  umundo::ServiceFilter* _svcFilter;
  umundo::ServiceManager* _svcMgr;
  std::map<boost::shared_ptr<umundo::ServiceDescription>, umundo::ServiceStub*> _svcs;
  
  static std::map<std::string, boost::weak_ptr<umundo::Node> > _nodes;
  static boost::shared_ptr<umundo::Node> getNode(Interpreter* interpreter);
};
	
}


#endif /* end of include guard: UMUNDOINVOKER_H_77YXQGU7 */
