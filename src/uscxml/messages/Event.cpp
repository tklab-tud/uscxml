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

#include "uscxml/messages/Event.h"

namespace uscxml {

Event Event::fromData(const Data& data) {
	Event e;
	if (data.hasKey("data"))
		e.data = Data(data["data"]);
	if (data.hasKey("raw"))
		e.raw = data["raw"].atom;
	if (data.hasKey("name"))
		e.name = data["name"].atom;
	if (data.hasKey("eventType"))
		e.eventType = (Type)strTo<size_t>(data["eventType"].atom);
	if (data.hasKey("origin"))
		e.origin = data["origin"].atom;
	if (data.hasKey("origintype"))
		e.origintype = data["origintype"].atom;
	if (data.hasKey("sendid"))
		e.sendid = data["sendid"].atom;
	if (data.hasKey("hideSendId"))
		e.hideSendId = strTo<bool>(data["hideSendId"].atom);
	if (data.hasKey("invokeid"))
		e.invokeid = data["invokeid"].atom;
	if (data.hasKey("uuid"))
		e.uuid = data["uuid"].atom;
	if (data.hasKey("namelist"))
		e.namelist = data["namelist"].compound;

	if (data.hasKey("params")) {
		for (auto param : data["params"].array) {
			e.params.insert(std::make_pair(param.second.compound.begin()->first, param.second.compound.begin()->second));
		}
	}
	return e;
}

Event::operator Data() {
	Data data;
	data["data"] = data;
	data["raw"] = Data(raw, Data::VERBATIM);
	data["name"] = Data(name, Data::VERBATIM);
	data["eventType"] = Data(eventType, Data::VERBATIM);
	data["origin"] = Data(origin, Data::VERBATIM);
	data["origintype"] = Data(origintype, Data::VERBATIM);
	data["sendid"] = Data(sendid, Data::VERBATIM);
	data["hideSendId"] = Data(hideSendId, Data::VERBATIM);
	data["invokeid"] = Data(invokeid, Data::VERBATIM);
	data["uuid"] = Data(uuid, Data::VERBATIM);
	data["namelist"].compound = namelist;

	int index=0;
	for (auto param : params) {
		Data entry;
		entry.compound[param.first] = param.second;
		data["params"].array.insert(std::make_pair(index++,entry));
	}

	return data;
}

std::ostream& operator<< (std::ostream& os, const Event& event) {
	std::string indent;
	for (size_t i = 0; i < _dataIndentation; i++) {
		indent += "  ";
	}

	os << indent
	   << (event.eventType == Event::INTERNAL ? "Internal" : "")
	   << (event.eventType == Event::EXTERNAL ? "External" : "")
	   << (event.eventType == Event::PLATFORM ? "Platform" : "") << " Event " << std::endl;

	if (event.name.size() > 0)
		os << indent << "  \"name\": " << event.name << std::endl;
	if (event.origin.size() > 0)
		os << indent << "  \"origin\": " << event.origin << std::endl;
	if (event.origintype.size() > 0)
		os << indent << "  \"origintype\": " << event.origintype << std::endl;
//    if (event.content.size() > 0)
//        os << indent << "  content: '" << event.content << "'" << std::endl;
	if (event.params.size() > 0) {
		std::multimap<std::string, Data>::const_iterator paramIter = event.params.begin();
		os << indent << "  \"params\":" << std::endl;
		_dataIndentation++;
		while(paramIter != event.params.end()) {
			os << indent << "    \"" << paramIter->first << "\": ";
			os << indent << paramIter->second << std::endl;
			paramIter++;
		}
		_dataIndentation--;
	}
	if (event.namelist.size() > 0) {
		std::map<std::string, Data>::const_iterator namelistIter = event.namelist.begin();
		os << indent << "  \"namelist\":" << std::endl;
		_dataIndentation++;
		while(namelistIter != event.namelist.end()) {
			os << indent << "    \"" << namelistIter->first << "\": ";
			os << indent << namelistIter->second << std::endl;
			namelistIter++;
		}
		_dataIndentation--;

	}
	_dataIndentation += 2;
	os << indent << "  \"data\": " << event.data;
	_dataIndentation -= 2;
	return os;
}

}
