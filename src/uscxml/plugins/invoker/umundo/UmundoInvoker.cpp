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

#include <boost/algorithm/string.hpp>

#include "UmundoInvoker.h"
#include <glog/logging.h>
#include "uscxml/URL.h"

#ifdef BUILD_AS_PLUGINS
#include <Pluma/Connector.hpp>
#endif

namespace uscxml {

#ifdef BUILD_AS_PLUGINS
PLUMA_CONNECTOR
bool pluginConnect(pluma::Host& host) {
	host.add( new UmundoInvokerProvider() );
	return true;
}
#endif

UmundoInvoker::UmundoInvoker() : _node(NULL), _discovery(NULL), _pub(NULL), _sub(NULL) {
}

UmundoInvoker::~UmundoInvoker() {
	if (_node) {
		if (_sub) {
			_node->removeSubscriber(*_sub);
			delete _sub;
		}
		if (_pub) {
			_node->removePublisher(*_pub);
			delete _pub;
		}
		delete(_node);
	}
};

boost::shared_ptr<InvokerImpl> UmundoInvoker::create(InterpreterImpl* interpreter) {
	boost::shared_ptr<UmundoInvoker> invoker = boost::shared_ptr<UmundoInvoker>(new UmundoInvoker());
	invoker->_interpreter = interpreter;
	return invoker;
}

Data UmundoInvoker::getDataModelVariables() {
	Data data;
	return data;
}

void UmundoInvoker::send(const SendRequest& req) {
	umundo::Message msg;

	if (req.name.length() > 0) {
		msg.putMeta("event", req.name);
	} else {
		msg.putMeta("event", "umundo");
	}

	try {
		Data data = req.data;

		if (data.empty() && req.content.length())
			data = _interpreter->getDataModel().getStringAsData(req.content);

		if (data.empty()) {
			LOG(ERROR) << "Cannot transform content to data object per datamodel or no data given";
			return;
		}

//		std::cout << Data::toJSON(data) << std::endl;

		std::string type;
		if (req.params.find("type") != req.params.end()) {
			// we are supposed to build a typed object
			type = req.params.find("type")->second.atom;

			const google::protobuf::Message* protoMsg = umundo::PBSerializer::getProto(type);
			if (protoMsg == NULL) {
				LOG(ERROR) << "No type '" << type << "' is known, pass a directory with proto .desc files via types param when invoking";
				return;
			}

			google::protobuf::Message* pbMsg = protoMsg->New();
			if (!dataToProtobuf(pbMsg, data)) {
				LOG(ERROR) << "Cannot create message from JSON - not sending";
				return;
			}

			if (!_isService) {
				// add all s11n properties
				_pub->prepareMsg(&msg, type, pbMsg);
				_pub->send(&msg);
			} else {
				// invoke as service
				std::map<umundo::ServiceDescription, umundo::ServiceStub*>::iterator svcIter = _svcs.begin();
				while(svcIter != _svcs.end()) {
					umundo::ServiceStub* stub = svcIter->second;
					Event event;
					void* rv = NULL;
					stub->callStubMethod(req.name, pbMsg, type, rv, "");
					protobufToData(event.data, *(const google::protobuf::Message*)rv);

					event.name = _invokeId + ".reply." + req.name;
					event.origin = msg.getMeta("um.channel");
					event.origintype = "umundo";
					event.eventType = Event::EXTERNAL;

					returnEvent(event);
					svcIter++;
				}
			}
		} else {
			// just encode JSON
			JSONProto* jsonProtoMsg = new JSONProto();
			if (!dataToJSONbuf(jsonProtoMsg, data)) {
				LOG(ERROR) << "Cannot create message from JSON - not sending";
				return;
			}

			if (!_isService) {
				// add all s11n properties
				_pub->prepareMsg(&msg, "JSON", jsonProtoMsg);
				_pub->send(&msg);
			} else {
				LOG(ERROR) << "Cannot invoke services with untyped JSON";
				return;
			}

		}
	} catch (Event e) {
		LOG(ERROR) << "Syntax error when invoking umundo:" << std::endl << e << std::endl;
		return;
	}
}

void UmundoInvoker::cancel(const std::string sendId) {
	assert(false);
}

void UmundoInvoker::invoke(const InvokeRequest& req) {

	std::string domain;
	std::string channelName;
	std::string serviceName;

	if (req.params.find("channel") != req.params.end()) {
		channelName = req.params.find("channel")->second.atom;
		_isService = false;
	} else if (req.params.find("service") != req.params.end()) {
		serviceName = req.params.find("service")->second.atom;
		_isService = true;
	} else {
		LOG(ERROR) << "Invoking umundo needs a service or a channel param";
		return;
	}
	if (req.params.find("domain") != req.params.end()) {
		domain = req.params.find("domain")->second.atom;
	}
	_node = new umundo::Node();

	umundo::DiscoveryConfigMDNS discOpts;
	_discovery = new umundo::Discovery(&discOpts);

	_discovery->add(*_node);

	// add type from .proto or .desc files
	std::list<std::string> type;
	Event::getParam(req.params, "type", type);
	std::list<std::string>::const_iterator typeIter = type.begin();
	while(typeIter != type.end()) {
		URL typeURI(*typeIter);
		if (typeURI.toAbsolute(_interpreter->getBaseURL(req.elem))) {
			std::string filename = typeURI.asLocalFile(".proto");
			umundo::PBSerializer::addProto(filename);
		} else {
			LOG(ERROR) << "umundo invoker has relative type src but no baseURI set with interpreter.";
		}
		typeIter++;
	}

	// add directory with .proto or .desc files
	std::list<std::string> types;
	Event::getParam(req.params, "type", types);
	std::list<std::string>::const_iterator typesIter = types.begin();
	while(typesIter != types.end()) {
		URL typeURI(*typesIter);
		if (typeURI.toAbsolute(_interpreter->getBaseURL(req.elem))) {
			umundo::PBSerializer::addProto(typeURI.path());
		} else {
			LOG(ERROR) << "invoke element has relative src URI with no baseURI set.";
		}
		typesIter++;
	}

	if (!_isService) {
		// use umundo to publish objects on a channel
		_pub = new umundo::TypedPublisher(channelName);
		_sub = new umundo::TypedSubscriber(channelName, this);

		_pub->setGreeter(this);
		_sub->registerType("JSON", new JSONProto());

		_node->addPublisher(*_pub);
		_node->addSubscriber(*_sub);

	} else if (serviceName.length() > 0) {
		// use umundo to access services
		_svcFilter = new umundo::ServiceFilter(serviceName);
		_node->connect(_svcMgr);
		_svcMgr->startQuery(*_svcFilter, this);
	}
}

void UmundoInvoker::welcome(umundo::TypedPublisher atPub, const umundo::SubscriberStub& sub) {
	Event event;
	event.name = "umundo.sub.added";
	event.data.compound["subId"] = Data(sub.getUUID(), Data::VERBATIM);
	event.data.compound["channel"] = Data(atPub.getChannelName(), Data::VERBATIM);
	event.data.compound["totalSubs"] = Data(toStr(atPub.waitForSubscribers(0)), Data::VERBATIM);
	returnEvent(event);
}

void UmundoInvoker::farewell(umundo::TypedPublisher fromPub, const umundo::SubscriberStub& sub) {
	Event event;
	event.name = "umundo.sub.removed";
	event.data.compound["subId"] = Data(sub.getUUID(), Data::VERBATIM);
	event.data.compound["channel"] = Data(fromPub.getChannelName(), Data::VERBATIM);
	event.data.compound["totalSubs"] = Data(toStr(fromPub.waitForSubscribers(0)), Data::VERBATIM);
	returnEvent(event);
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
	event.eventType = Event::EXTERNAL;

	if (object != NULL) {
		if (msg->getMeta().find("um.s11n.type") != msg->getMeta().end() &&
		        boost::equals(msg->getMeta().find("um.s11n.type")->second, "JSON")) {
			jsonbufToData(event.data, *(JSONProto*)object);
		} else {
			protobufToData(event.data, *(const google::protobuf::Message*)object);
		}
	}

	// get meta fields into event
	std::map<std::string, std::string>::const_iterator metaIter = msg->getMeta().begin();
	while(metaIter != msg->getMeta().end()) {
		if (isNumeric(metaIter->second.c_str(), 10)) {
			event.data.compound[metaIter->first] = Data(metaIter->second, Data::INTERPRETED);
		} else {
			event.data.compound[metaIter->first] = Data(metaIter->second, Data::VERBATIM);
		}
		metaIter++;
	}

	if (msg->size() > 0) {
		event.data.compound["protobuf"] = Data(msg->data(), msg->size(), "application/x-protobuf");
	}

	returnEvent(event);
}

void UmundoInvoker::added(umundo::ServiceDescription desc) {
	LOG(ERROR) << "Service found!";

	umundo::ServiceStub* stub = new umundo::ServiceStub(desc);
	_svcs[desc] = stub;

	Event addedEvent;
	addedEvent.invokeid = _invokeId;
	addedEvent.origin = desc.getName();
	addedEvent.origintype = "umundo";
	addedEvent.eventType = Event::EXTERNAL;
	addedEvent.name = _invokeId + ".added";

	std::map<std::string, std::string>::const_iterator propIter = desc.getProperties().begin();
	while(propIter != desc.getProperties().end()) {
		addedEvent.data.compound[propIter->first] = Data(propIter->second, Data::VERBATIM);
		propIter++;
	}

	returnEvent(addedEvent);
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
	addedEvent.eventType = Event::EXTERNAL;
	addedEvent.name = _invokeId + ".removed";

	std::map<std::string, std::string>::const_iterator propIter = desc.getProperties().begin();
	while(propIter != desc.getProperties().end()) {
		addedEvent.data.compound[propIter->first] = Data(propIter->second, Data::VERBATIM);
		propIter++;
	}

	returnEvent(addedEvent);
}

void UmundoInvoker::changed(umundo::ServiceDescription desc, uint64_t what) {
}

bool UmundoInvoker::jsonbufToData(Data& data, const JSONProto& json) {
	if (json.compound_size() > 0) {
		if (json.compound(0).key().size() > 0) {
			// compound
			for (int i = 0; i < json.compound_size(); i++) {
				jsonbufToData(data.compound[json.compound(i).key()], json.compound(i));
			}
		} else {
			// array
			for (int i = 0; i < json.compound_size(); i++) {
				Data arrayData;
				data.array.push_back(arrayData);
				jsonbufToData(data.array.back(), json.compound(i));
			}
		}
	} else if (json.atom().size() > 0) {
		data.atom = json.atom();
		if (json.verbatim()) {
			data.type = Data::VERBATIM;
		} else {
			data.type = Data::INTERPRETED;
		}
	}

	return true;
}

bool UmundoInvoker::protobufToData(Data& data, const google::protobuf::Message& msg) {
	const google::protobuf::Descriptor* desc = msg.GetDescriptor();
	const google::protobuf::Reflection* reflect = msg.GetReflection();

	data.compound["protobufType"] = Data(desc->name(), Data::VERBATIM);

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
					data.compound[key].array.push_back(Data(toStr(reflect->GetRepeatedDouble(msg, fieldDesc, j)), Data::INTERPRETED));
				}
			} else {
				data.compound[key].atom = toStr(reflect->GetDouble(msg, fieldDesc));
			}
			break;
		case google::protobuf::FieldDescriptor::TYPE_ENUM:
			if (fieldDesc->is_repeated()) {
				for (int j = 0; j < reflect->FieldSize(msg, fieldDesc); j++) {
					const google::protobuf::EnumValueDescriptor* enumDesc = reflect->GetRepeatedEnum(msg, fieldDesc, j);
					data.compound[key].array.push_back(Data(toStr(enumDesc->name()),  Data::VERBATIM));
				}
			} else {
				const google::protobuf::EnumValueDescriptor* enumDesc = reflect->GetEnum(msg, fieldDesc);
				data.compound[key] = Data(enumDesc->name(), Data::VERBATIM);
			}
			break;
		case google::protobuf::FieldDescriptor::TYPE_FIXED32:
		case google::protobuf::FieldDescriptor::TYPE_UINT32:
			if (fieldDesc->is_repeated()) {
				for (int j = 0; j < reflect->FieldSize(msg, fieldDesc); j++) {
					data.compound[key].array.push_back(Data(toStr(reflect->GetRepeatedUInt32(msg, fieldDesc, j)), Data::INTERPRETED));
				}
			} else {
				data.compound[key].atom = toStr(reflect->GetUInt32(msg, fieldDesc));
			}
			break;
		case google::protobuf::FieldDescriptor::TYPE_FIXED64:
		case google::protobuf::FieldDescriptor::TYPE_UINT64:
			if (fieldDesc->is_repeated()) {
				for (int j = 0; j < reflect->FieldSize(msg, fieldDesc); j++) {
					data.compound[key].array.push_back(Data(toStr(reflect->GetRepeatedUInt64(msg, fieldDesc, j)), Data::INTERPRETED));
				}
			} else {
				data.compound[key].atom = toStr(reflect->GetUInt64(msg, fieldDesc));
			}
			break;
		case google::protobuf::FieldDescriptor::TYPE_FLOAT:
			if (fieldDesc->is_repeated()) {
				for (int j = 0; j < reflect->FieldSize(msg, fieldDesc); j++) {
					data.compound[key].array.push_back(Data(toStr(reflect->GetRepeatedFloat(msg, fieldDesc, j)), Data::INTERPRETED));
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
					data.compound[key].array.push_back(Data(toStr(reflect->GetRepeatedInt32(msg, fieldDesc, j)), Data::INTERPRETED));
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
					data.compound[key].array.push_back(Data(toStr(reflect->GetRepeatedInt64(msg, fieldDesc, j)), Data::INTERPRETED));
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

bool UmundoInvoker::dataToJSONbuf(JSONProto* msg, Data& data) {
	const google::protobuf::Descriptor* desc = msg->GetDescriptor();
	const google::protobuf::Reflection* reflect = msg->GetReflection();

	if (!data.compound.empty()) {
		const google::protobuf::FieldDescriptor* fieldDesc = desc->FindFieldByName("compound");

		std::map<std::string, Data>::iterator compoundIter = data.compound.begin();
		while(compoundIter != data.compound.end()) {
			JSONProto* compoundMsg = (JSONProto*)reflect->AddMessage(msg, fieldDesc);
			dataToJSONbuf(compoundMsg, compoundIter->second);
			compoundMsg->set_key(compoundIter->first);
			compoundIter++;
		}
	} else if (!data.array.empty()) {
		const google::protobuf::FieldDescriptor* fieldDesc = desc->FindFieldByName("compound");

		std::list<Data>::iterator arrayIter = data.array.begin();
		while(arrayIter != data.array.end()) {
			JSONProto* arrayMsg = (JSONProto*)reflect->AddMessage(msg, fieldDesc);
			dataToJSONbuf(arrayMsg, *arrayIter);
			arrayIter++;
		}
	} else if (!data.atom.empty()) {
		const google::protobuf::FieldDescriptor* atomDesc = desc->FindFieldByName("atom");
		const google::protobuf::FieldDescriptor* verbDesc = desc->FindFieldByName("verbatim");

		if (data.type == Data::VERBATIM) {
			reflect->SetBool(msg, verbDesc, true);
		} else {
			reflect->SetBool(msg, verbDesc, false);
		}
		reflect->SetString(msg, atomDesc, data.atom);
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
				LOG(ERROR) << "required field " << key << " not given";
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