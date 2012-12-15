#include "uscxml/config.h"
#include "uscxml/Common.h"
#include "UmundoInvoker.h"
#include "uscxml/Interpreter.h"
#include <glog/logging.h>

#ifdef BUILD_AS_PLUGINS
#include <Pluma/Connector.hpp>
#endif

namespace uscxml {

#ifdef BUILD_AS_PLUGINS
PLUMA_CONNECTOR
bool connect(pluma::Host& host){
    host.add( new UmundoInvokerProvider() );
    return true;
}
#endif

UmundoInvoker::UmundoInvoker() {
}

UmundoInvoker::~UmundoInvoker() {
  _node.removeSubscriber(_sub);
  _node.removePublisher(_pub);
};

Invoker* UmundoInvoker::create(Interpreter* interpreter) {
  UmundoInvoker* invoker = new UmundoInvoker();
  invoker->_interpreter = interpreter;
  return invoker;
}

Data UmundoInvoker::getDataModelVariables() {
  Data data;
  return data;
}

void UmundoInvoker::send(SendRequest& req) {
  umundo::Message* msg = new umundo::Message();

  if (req.name.length() > 0) {
    msg->putMeta("event", req.name);
  } else {
    msg->putMeta("event", "umundo");  
  }
  
  if (req.params.find("type") != req.params.end()) {
    // assume JSON in content to transform to protobuf object
    if (req.content.length() > 0 && _interpreter->getDataModel() != NULL) {
      std::string type = req.params["type"].front();
      const google::protobuf::Message* protoMsg = umundo::PBSerializer::getProto(type);
      if (protoMsg == NULL) {
        LOG(ERROR) << "No type " << type << " is known, pass a directory with proto .desc files via types param when invoking";
        return;
      }
      try {
        Data data = _interpreter->getDataModel()->getStringAsData(req.content);
        google::protobuf::Message* pbMsg = protoMsg->New();
        if (!dataToProtobuf(pbMsg, data)) {
          LOG(ERROR) << "Cannot create message from JSON - not sending";
        } else {
          // add all s11n properties
          if (!_isService) {
            _pub.prepareMsg(msg, type, pbMsg);
            _pub.send(msg);
          } else {
            std::map<umundo::ServiceDescription, umundo::ServiceStub*>::iterator svcIter = _svcs.begin();
            while(svcIter != _svcs.end()) {
              umundo::ServiceStub* stub = svcIter->second;
              Event event;
              void* rv = NULL;
              stub->callStubMethod(req.name, pbMsg, type, rv, "");
              protobufToData(event, *(const google::protobuf::Message*)rv);

              event.name = _invokeId + ".reply." + req.name;
              event.invokeid = _invokeId;
              event.origin = msg->getMeta("um.channel");
              event.origintype = "umundo";
              event.type = Event::EXTERNAL;

              _interpreter->receive(event);
              svcIter++;
            }
          }
        }
      } catch (Event e) {
        LOG(ERROR) << "Syntax error when invoking umundo:" << std::endl << e << std::endl;
        return;
      }
    } else {
      LOG(ERROR) << "Required JSON object in content" << std::endl;
      return;
    }
  }
}

void UmundoInvoker::cancel(const std::string sendId) {
  assert(false);
}

void UmundoInvoker::sendToParent(SendRequest& req) {
  assert(false);
}

void UmundoInvoker::invoke(InvokeRequest& req) {
  _invokeId = req.invokeid;
  
  std::string channelName;
  std::string serviceName;
  
  if (req.params.find("channel") != req.params.end()) {
    channelName = req.params["channel"].front();
    _isService = false;
  } else if (req.params.find("service") != req.params.end()) {
    serviceName = req.params["service"].front();
    _isService = true;
  } else {
    LOG(ERROR) << "Invoking umundo needs a service or a channel param";
    return;
  }
  
  _node = getNode(_interpreter);
  
  // add types from .proto or .desc files
  if (req.params.find("types") != req.params.end()) {
    std::list<std::string>::iterator typeIter = req.params["types"].begin();
    while(typeIter != req.params["types"].end()) {
      Arabica::io::URI srcURI(*typeIter);
      // if (!_interpreter->makeAbsolute(srcURI)) {
      //   LOG(ERROR) << "Relative URI for types in umundo invoker " << *typeIter <<  " with no base URI set for interpreter";
      //   return;
      // }
      umundo::PBSerializer::addProto(srcURI.path());
      typeIter++;
    }
  }

  if (!_isService) {
    // use umundo to publish objects on a channel
    _pub = umundo::TypedPublisher(channelName);
    _sub = umundo::TypedSubscriber(channelName, this);
    
    _node.addPublisher(_pub);
    _node.addSubscriber(_sub);
    
  } else if (serviceName.length() > 0) {
    // use umundo to access services
    _svcFilter = umundo::ServiceFilter(serviceName);
    _node.connect(&_svcMgr);
    _svcMgr.startQuery(_svcFilter, this);
  }
}

void UmundoInvoker::receive(void* object, umundo::Message* msg) {
  uscxml::Event event;
  if (msg->getMeta().find("event") != msg->getMeta().end()) {
    event.name = msg->getMeta("event");
  } else {
    event.name = "umundo.rcvd";
  }
  
  event.invokeid = _invokeId;
  event.origin = msg->getMeta("um.channel");
  event.origintype = "umundo";
  event.type = Event::EXTERNAL;
  
//  if (msg->getMeta().find("um.s11n.type") != msg->getMeta().end())
//    event.compound["class"] = msg->getMeta("um.s11n.type");
  
  if (object != NULL)
    protobufToData(event, *(const google::protobuf::Message*)object);
  
  // get meta fields into event
  std::map<std::string, std::string>::const_iterator metaIter = msg->getMeta().begin();
  while(metaIter != msg->getMeta().end()) {
    if (metaIter->first.substr(0,3).compare("um.") != 0)
      event.compound[metaIter->first] = Data(metaIter->second, Data::VERBATIM);
    metaIter++;
  }
  
  _interpreter->receive(event);
}

void UmundoInvoker::added(umundo::ServiceDescription desc) {
  LOG(ERROR) << "Service found!";

  umundo::ServiceStub* stub = new umundo::ServiceStub(desc);
  _svcs[desc] = stub;

  Event addedEvent;
  addedEvent.invokeid = _invokeId;
  addedEvent.origin = desc.getName();
  addedEvent.origintype = "umundo";
  addedEvent.type = Event::EXTERNAL;
  addedEvent.name = _invokeId + ".added";
  
  std::map<std::string, std::string>::const_iterator propIter = desc.getProperties().begin();
  while(propIter != desc.getProperties().end()) {
    addedEvent.compound[propIter->first] = Data(propIter->second, Data::VERBATIM);
    propIter++;
  }

  _interpreter->receive(addedEvent);
}

void UmundoInvoker::removed(umundo::ServiceDescription desc) {
  LOG(ERROR) << "Service lost!";

  if (_svcs.find(desc) == _svcs.end()) {
    return;
  }
  
  delete _svcs[desc];
  _svcs.erase(desc);

  Event addedEvent;
  addedEvent.invokeid = _invokeId;
  addedEvent.origin = desc.getName();
  addedEvent.origintype = "umundo";
  addedEvent.type = Event::EXTERNAL;
  addedEvent.name = _invokeId + ".removed";
  
  std::map<std::string, std::string>::const_iterator propIter = desc.getProperties().begin();
  while(propIter != desc.getProperties().end()) {
    addedEvent.compound[propIter->first] = Data(propIter->second, Data::VERBATIM);
    propIter++;
  }
  
  _interpreter->receive(addedEvent);
}

void UmundoInvoker::changed(umundo::ServiceDescription desc) {
}

std::map<std::string, umundo::Node> UmundoInvoker::_nodes;
umundo::Node UmundoInvoker::getNode(Interpreter* interpreter) {
  if ((_nodes.find(interpreter->getName()) == _nodes.end())) {
    _nodes[interpreter->getName()] = umundo::Node();
  }
  return _nodes[interpreter->getName()];
}

bool UmundoInvoker::protobufToData(Data& data, const google::protobuf::Message& msg) {
  const google::protobuf::Descriptor* desc = msg.GetDescriptor();
  const google::protobuf::Reflection* reflect = msg.GetReflection();
  
  data.compound["type"] = Data(desc->name(), Data::VERBATIM);
  
  for (int i = 0; i < desc->field_count(); i++) {
    const google::protobuf::FieldDescriptor* fieldDesc = desc->field(i);
    std::string key = fieldDesc->name();
    
    if (!fieldDesc->is_repeated() && !reflect->HasField(msg, fieldDesc))
      continue;
    
    switch(fieldDesc->type()) {
      case google::protobuf::FieldDescriptor::TYPE_BOOL:
        if (fieldDesc->is_repeated()) {
          for (int j = 0; j < reflect->FieldSize(msg, fieldDesc); j++) {
            data.compound[key].array.push_back(Data(reflect->GetRepeatedBool(msg, fieldDesc, j) ? "true" : "false"));
          }
        } else {
          data.compound[key].atom = (reflect->GetBool(msg, fieldDesc) ? "true" : "false");
        }
        break;
      case google::protobuf::FieldDescriptor::TYPE_BYTES:
      case google::protobuf::FieldDescriptor::TYPE_STRING:
        if (fieldDesc->is_repeated()) {
          for (int j = 0; j < reflect->FieldSize(msg, fieldDesc); j++) {
            data.compound[key].array.push_back(Data(toStr(reflect->GetRepeatedString(msg, fieldDesc, j)), Data::VERBATIM));
          }
        } else {
          data.compound[key].atom = toStr(reflect->GetString(msg, fieldDesc));
          data.compound[key].type = Data::VERBATIM;
        }
        break;
      case google::protobuf::FieldDescriptor::TYPE_DOUBLE:
        if (fieldDesc->is_repeated()) {
          for (int j = 0; j < reflect->FieldSize(msg, fieldDesc); j++) {
            data.compound[key].array.push_back(Data(toStr(reflect->GetRepeatedDouble(msg, fieldDesc, j))));
          }
        } else {
          data.compound[key].atom = toStr(reflect->GetDouble(msg, fieldDesc));
        }
        break;
      case google::protobuf::FieldDescriptor::TYPE_ENUM:
        LOG(ERROR) << "TYPE_ENUM is unimplemented" << std::endl;
        break;
      case google::protobuf::FieldDescriptor::TYPE_FIXED32:
      case google::protobuf::FieldDescriptor::TYPE_UINT32:
        if (fieldDesc->is_repeated()) {
          for (int j = 0; j < reflect->FieldSize(msg, fieldDesc); j++) {
            data.compound[key].array.push_back(Data(toStr(reflect->GetRepeatedUInt32(msg, fieldDesc, j))));
          }
        } else {
          data.compound[key].atom = toStr(reflect->GetUInt32(msg, fieldDesc));
        }
        break;
      case google::protobuf::FieldDescriptor::TYPE_FIXED64:
      case google::protobuf::FieldDescriptor::TYPE_UINT64:
        if (fieldDesc->is_repeated()) {
          for (int j = 0; j < reflect->FieldSize(msg, fieldDesc); j++) {
            data.compound[key].array.push_back(Data(toStr(reflect->GetRepeatedUInt64(msg, fieldDesc, j))));
          }
        } else {
          data.compound[key].atom = toStr(reflect->GetUInt64(msg, fieldDesc));
        }
        break;
      case google::protobuf::FieldDescriptor::TYPE_FLOAT:
        if (fieldDesc->is_repeated()) {
          for (int j = 0; j < reflect->FieldSize(msg, fieldDesc); j++) {
            data.compound[key].array.push_back(Data(toStr(reflect->GetRepeatedFloat(msg, fieldDesc, j))));
          }
        } else {
          data.compound[key].atom = toStr(reflect->GetFloat(msg, fieldDesc));
        }
        break;
      case google::protobuf::FieldDescriptor::TYPE_GROUP:
        LOG(ERROR) << "TYPE_GROUP is unimplemented" << std::endl;
        break;
      case google::protobuf::FieldDescriptor::TYPE_INT32:
      case google::protobuf::FieldDescriptor::TYPE_SINT32:
      case google::protobuf::FieldDescriptor::TYPE_SFIXED32:
        if (fieldDesc->is_repeated()) {
          for (int j = 0; j < reflect->FieldSize(msg, fieldDesc); j++) {
            data.compound[key].array.push_back(Data(toStr(reflect->GetRepeatedInt32(msg, fieldDesc, j))));
          }
        } else {
          data.compound[key].atom = toStr(reflect->GetInt32(msg, fieldDesc));
        }
        break;
      case google::protobuf::FieldDescriptor::TYPE_INT64:
      case google::protobuf::FieldDescriptor::TYPE_SINT64:
      case google::protobuf::FieldDescriptor::TYPE_SFIXED64:
        if (fieldDesc->is_repeated()) {
          for (int j = 0; j < reflect->FieldSize(msg, fieldDesc); j++) {
            data.compound[key].array.push_back(Data(toStr(reflect->GetRepeatedInt64(msg, fieldDesc, j))));
          }
        } else {
          data.compound[key].atom = toStr(reflect->GetInt64(msg, fieldDesc));
        }
        break;
      case google::protobuf::FieldDescriptor::TYPE_MESSAGE:
        if (fieldDesc->is_repeated()) {
          for (int j = 0; j < reflect->FieldSize(msg, fieldDesc); j++) {
            data.compound[key].array.push_back(Data());
            protobufToData(data.compound[key].array.back(), reflect->GetRepeatedMessage(msg, fieldDesc, j));
          }
        } else {
          protobufToData(data.compound[key], reflect->GetMessage(msg, fieldDesc));
        }
        break;
    }
  }
  return true;
}

bool UmundoInvoker::dataToProtobuf(google::protobuf::Message* msg, Data& data) {
  const google::protobuf::Descriptor* desc = msg->GetDescriptor();
  const google::protobuf::Reflection* reflect = msg->GetReflection();
  
  for (int i = 0; i < desc->field_count(); i++) {
    const google::protobuf::FieldDescriptor* fieldDesc = desc->field(i);
    std::string key = fieldDesc->name();
    
    if (data.compound.find(key) == data.compound.end()) {
      if (fieldDesc->is_required()) {
        LOG(ERROR) << "required field " << key << " not given in JSON";
        return false;
      }
      continue;
    }
    
    std::list<Data>::iterator arrayIter = data.compound[key].array.begin();
    
    switch(fieldDesc->type()) {
      case google::protobuf::FieldDescriptor::TYPE_BOOL:
        if (fieldDesc->is_repeated()) {
          while(arrayIter != data.compound[key].array.end()) {
            reflect->AddBool(msg, fieldDesc, arrayIter->atom.compare("false") == 0 ? false : true);
            arrayIter++;
          }
        } else {
          reflect->SetBool(msg, fieldDesc, (data.compound[key].atom.compare("false") == 0 ? false : true));
        }
        break;
      case google::protobuf::FieldDescriptor::TYPE_BYTES:
      case google::protobuf::FieldDescriptor::TYPE_STRING:
        if (fieldDesc->is_repeated()) {
          while(arrayIter != data.compound[key].array.end()) {
            reflect->AddString(msg, fieldDesc, arrayIter->atom);
            arrayIter++;
          }
        } else {
          reflect->SetString(msg, fieldDesc, data.compound[key].atom);
        }
        break;
      case google::protobuf::FieldDescriptor::TYPE_DOUBLE:
        if (fieldDesc->is_repeated()) {
          while(arrayIter != data.compound[key].array.end()) {
            reflect->AddDouble(msg, fieldDesc, strTo<double>(arrayIter->atom));
            arrayIter++;
          }
        } else {
          reflect->SetDouble(msg, fieldDesc, strTo<double>(data.compound[key].atom));
        }
        break;
      case google::protobuf::FieldDescriptor::TYPE_ENUM:
        LOG(ERROR) << "TYPE_ENUM is unimplemented" << std::endl;
        break;
      case google::protobuf::FieldDescriptor::TYPE_FIXED32:
      case google::protobuf::FieldDescriptor::TYPE_UINT32:
        if (fieldDesc->is_repeated()) {
          while(arrayIter != data.compound[key].array.end()) {
            reflect->AddUInt32(msg, fieldDesc, strTo<uint32_t>(arrayIter->atom));
            arrayIter++;
          }
        } else {
          reflect->SetUInt32(msg, fieldDesc, strTo<uint32_t>(data.compound[key].atom));
        }
        break;
      case google::protobuf::FieldDescriptor::TYPE_FIXED64:
      case google::protobuf::FieldDescriptor::TYPE_UINT64:
        if (fieldDesc->is_repeated()) {
          while(arrayIter != data.compound[key].array.end()) {
            reflect->AddUInt64(msg, fieldDesc, strTo<uint64_t>(arrayIter->atom));
            arrayIter++;
          }
        } else {
          reflect->SetUInt64(msg, fieldDesc, strTo<uint64_t>(data.compound[key].atom));
        }
        break;
      case google::protobuf::FieldDescriptor::TYPE_FLOAT:
        if (fieldDesc->is_repeated()) {
          while(arrayIter != data.compound[key].array.end()) {
            reflect->AddFloat(msg, fieldDesc, strTo<float>(arrayIter->atom));
            arrayIter++;
          }
        } else {
          reflect->SetFloat(msg, fieldDesc, strTo<float>(data.compound[key].atom));
        }
        break;
      case google::protobuf::FieldDescriptor::TYPE_GROUP:
        LOG(ERROR) << "TYPE_GROUP is unimplemented" << std::endl;
        break;
      case google::protobuf::FieldDescriptor::TYPE_INT32:
      case google::protobuf::FieldDescriptor::TYPE_SINT32:
      case google::protobuf::FieldDescriptor::TYPE_SFIXED32:
        if (fieldDesc->is_repeated()) {
          while(arrayIter != data.compound[key].array.end()) {
            reflect->AddInt32(msg, fieldDesc, strTo<int32_t>(arrayIter->atom));
            arrayIter++;
          }
        } else {
          reflect->SetInt32(msg, fieldDesc, strTo<int32_t>(data.compound[key].atom));
        }
        break;
      case google::protobuf::FieldDescriptor::TYPE_INT64:
      case google::protobuf::FieldDescriptor::TYPE_SINT64:
      case google::protobuf::FieldDescriptor::TYPE_SFIXED64:
        if (fieldDesc->is_repeated()) {
          while(arrayIter != data.compound[key].array.end()) {
            reflect->AddInt64(msg, fieldDesc, strTo<int64_t>(arrayIter->atom));
            arrayIter++;
          }
        } else {
          reflect->SetInt64(msg, fieldDesc, strTo<int64_t>(data.compound[key].atom));
        }
        break;
      case google::protobuf::FieldDescriptor::TYPE_MESSAGE:
        if (fieldDesc->is_repeated()) {
          while(arrayIter != data.compound[key].array.end()) {
            dataToProtobuf(reflect->AddMessage(msg, fieldDesc), *arrayIter);
            arrayIter++;
          }
        } else {
          dataToProtobuf(reflect->MutableMessage(msg, fieldDesc), data.compound[key]);
        }
        break;
    }
  }
  return true;
}

}