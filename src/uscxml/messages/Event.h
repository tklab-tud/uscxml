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

#ifndef EVENT_H_6174D929
#define EVENT_H_6174D929

#include "uscxml/messages/Data.h"
#include "uscxml/util/UUID.h"

#define ERROR_PLATFORM_THROW(msg) \
	ErrorEvent e; \
	e.name = "error.platform"; \
	e.data.compound["cause"] = Data(msg, Data::VERBATIM); \
	throw e; \

#define ERROR_EXECUTION(identifier, cause) \
	uscxml::ErrorEvent identifier; \
	identifier.data.compound["cause"] = uscxml::Data(cause, uscxml::Data::VERBATIM); \
	identifier.name = "error.execution"; \
	identifier.eventType = uscxml::Event::PLATFORM;

#define ERROR_EXECUTION2(identifier, cause, node) \
	uscxml::ErrorEvent identifier; \
	identifier.data.compound["cause"] = uscxml::Data(cause, uscxml::Data::VERBATIM); \
	identifier.name = "error.execution"; \
	identifier.data.compound["xpath"] = uscxml::Data(DOMUtils::xPathForNode(node), uscxml::Data::VERBATIM); \
	identifier.eventType = uscxml::Event::PLATFORM;

#define ERROR_COMMUNICATION(identifier, cause) \
	uscxml::ErrorEvent identifier; \
	identifier.data.compound["cause"] = uscxml::Data(cause, uscxml::Data::VERBATIM); \
	identifier.name = "error.communication"; \
	identifier.eventType = uscxml::Event::PLATFORM;

#define ERROR_COMMUNICATION2(identifier, cause, node) \
	uscxml::ErrorEvent identifier; \
	identifier.data.compound["cause"] = uscxml::Data(cause, uscxml::Data::VERBATIM); \
	identifier.name = "error.communication"; \
	identifier.data.compound["xpath"] = uscxml::Data(DOMUtils::xPathForNode(node), uscxml::Data::VERBATIM); \
	identifier.eventType = uscxml::Event::PLATFORM;

#define ERROR_EXECUTION_THROW(cause) \
{\
	ERROR_EXECUTION(exc, cause); \
	throw exc;\
}

#define ERROR_EXECUTION_THROW2(cause, node) \
{\
	ERROR_EXECUTION2(exc, cause, node); \
	throw exc;\
}

#define ERROR_COMMUNICATION_THROW(cause) \
{\
	ERROR_COMMUNICATION(exc, cause); \
	throw exc;\
}

#define ERROR_COMMUNICATION_THROW2(cause, node) \
{\
	ERROR_COMMUNICATION(exc, cause, node); \
	throw exc;\
}

namespace uscxml {

class USCXML_API Event {
public:
	enum Type {
		INTERNAL = 1,
		EXTERNAL = 2,
		PLATFORM = 3
	};

	Event() : eventType(INTERNAL), hideSendId(false), uuid(UUID::getUUID()) {}
	explicit Event(const std::string& name, Type type = INTERNAL) : name(name), eventType(type), hideSendId(false) {}
	bool operator< (const Event& other) const     {
		return this < &other;
	}

	bool operator==(const Event& other) const     {
		return (this->name == other.name &&
		        this->sendid == other.sendid &&
		        this->invokeid == other.invokeid &&
		        this->data == other.data);
	}
	bool operator!=(const Event& other) const     {
		return !(*this == other);
	}

	operator bool() {
		return name.size() > 0;
	}

	operator std::string() {
		std::stringstream ss;
		ss << *this;
		return ss.str();
	}

	typedef std::multimap<std::string, Data> params_t;
	typedef std::map<std::string, Data> namelist_t;

	static bool getParam(const params_t& params, const std::string& name, Data& target) {
		if (params.find(name) != params.end()) {
			target = params.find(name)->second;
			return true;
		}
		return false;
	}

	static bool getParam(const params_t& params, const std::string& name, std::list<Data>& target) {
		if (params.find(name) != params.end()) {
			std::pair<params_t::const_iterator, params_t::const_iterator> rangeIter = params.equal_range(name);
			while(rangeIter.first != rangeIter.second) {
				target.push_back(rangeIter.first->second);
				rangeIter.first++;
			}
			return true;
		}
		return false;
	}

	template <typename T> static bool getParam(const params_t& params, const std::string& name, T& target) {
		if (params.find(name) != params.end()) {
			target = strTo<T>(params.find(name)->second.atom);
			return true;
		}
		return false;
	}

	static bool getParam(const params_t& params, const std::string& name, bool& target) {
		if (params.find(name) != params.end()) {
			target = true;
			if (iequals(params.find(name)->second.atom, "false")) {
				target = false;
			} else if(iequals(params.find(name)->second.atom, "off")) {
				target = false;
			} else if(iequals(params.find(name)->second.atom, "no")) {
				target = false;
			} else if(iequals(params.find(name)->second.atom, "0")) {
				target = false;
			}
			return true;
		}
		return false;
	}

	template <typename T> static bool getParam(const params_t& params, const std::string& name, std::list<T>& target) {
		if (params.find(name) != params.end()) {
			std::pair<params_t::const_iterator, params_t::const_iterator> rangeIter = params.equal_range(name);
			while(rangeIter.first != rangeIter.second) {
				target.push_back(strTo<T>(rangeIter.first->second.atom));
				rangeIter.first++;
			}
			return true;
		}
		return false;
	}

	std::string raw;
	std::string name;
	Type eventType;
	std::string origin;
	std::string origintype;
	std::string sendid;
	bool hideSendId; // sendid is assumed to be undef with some ecma tests
	std::string invokeid;
	Data data;
	std::map<std::string, Data> namelist;
	std::multimap<std::string, Data> params;
	std::string uuid; // the sendid is not necessarily unique!

	friend USCXML_API std::ostream& operator<< (std::ostream& os, const Event& event);
};

USCXML_API std::ostream& operator<< (std::ostream& os, const Event& event);


class USCXML_API ErrorEvent : public Event {
public:
	ErrorEvent() : Event() {}
	ErrorEvent(const std::string& msg) : Event("error.platform") {
		data.compound["msg"] = Data(msg, Data::VERBATIM);
	}
};

}



#endif /* end of include guard: EVENT_H_6174D929 */
