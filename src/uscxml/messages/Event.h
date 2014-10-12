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

#define ERROR_EXECUTION(identifier, cause) \
	uscxml::Event identifier; \
	identifier.data.compound["cause"] = uscxml::Data(cause, uscxml::Data::VERBATIM); \
	identifier.name = "error.execution"; \
	identifier.eventType = uscxml::Event::PLATFORM;

#define ERROR_EXECUTION2(identifier, cause, node) \
	uscxml::Event identifier; \
	identifier.data.compound["cause"] = uscxml::Data(cause, uscxml::Data::VERBATIM); \
	identifier.name = "error.execution"; \
	identifier.data.compound["xpath"] = uscxml::Data(DOMUtils::xPathForNode(node), uscxml::Data::VERBATIM); \
	identifier.eventType = uscxml::Event::PLATFORM;

#define ERROR_COMMUNICATION(identifier, cause) \
	uscxml::Event identifier; \
	identifier.data.compound["cause"] = uscxml::Data(cause, uscxml::Data::VERBATIM); \
	identifier.name = "error.communication"; \
	identifier.eventType = uscxml::Event::PLATFORM;

#define ERROR_COMMUNICATION2(identifier, cause, node) \
	uscxml::Event identifier; \
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

	Event() : eventType(INTERNAL), hideSendId(false) {}
	Event(const std::string& name, Type type = INTERNAL) : name(name), eventType(type), hideSendId(false) {}
	Event(const Arabica::DOM::Node<std::string>& xmlString) : eventType(INTERNAL), hideSendId(false) {};
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

	std::string getName() const {
		return name;
	}
	void setName(const std::string& name) {
		this->name = name;
	}

	Type getEventType() const {
		return eventType;
	}
	void setEventType(const Type type) {
		this->eventType = type;
	}

	std::string getOrigin() const {
		return origin;
	}
	void setOrigin(const std::string& origin) {
		this->origin = origin;
	}

	std::string getOriginType() const {
		return origintype;
	}
	void setOriginType(const std::string& originType) {
		this->origintype = originType;
	}

	Arabica::DOM::Node<std::string> getDOM() const {
		return dom;
	}
	void setDOM(const Arabica::DOM::Node<std::string>& dom) {
		this->dom = dom;
	}

//	Arabica::DOM::Node<std::string> getFirstDOMElement() const;
//	Arabica::DOM::Document<std::string> getStrippedDOM() const;
//
//	static Arabica::DOM::Node<std::string> getFirstDOMElement(const Arabica::DOM::Document<std::string> dom);
//	static Arabica::DOM::Document<std::string> getStrippedDOM(const Arabica::DOM::Document<std::string> dom);

	std::string getRaw() const {
		return raw;
	}
	void setRaw(const std::string& raw) {
		this->raw = raw;
	}

	std::string getContent() const {
		return content;
	}
	void setContent(const std::string& content) {
		this->content = content;
	}

	std::string getXML() const {
		return xml;
	}
	void setXML(const std::string& xml) {
		this->xml = xml;
	}

	std::string getSendId() const {
		return sendid;
	}
	void setSendId(const std::string& sendId) {
		this->sendid = sendId;
	}

	std::string getInvokeId() const {
		return invokeid;
	}
	void setInvokeId(const std::string& invokeId) {
		this->invokeid = invokeId;
	}

	Data getData() const {
		return data;
	}
	void setData(const Data& data) {
		this->data = data;
	}

	static Event fromXML(const std::string& xmlString);
	Arabica::DOM::Document<std::string> toDocument();
	std::string toXMLString();

	std::map<std::string, Data>& getNameList() {
		return namelist;
	}
	std::multimap<std::string, Data>& getParams() {
		return params;
	}

	void setNameList(const std::map<std::string, Data>& nameList) {
		this->namelist = nameList;
	}
	void setParams(const std::multimap<std::string, Data>& params) {
		this->params = params;
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
			target = boost::lexical_cast<T>(params.find(name)->second.atom);
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
				target.push_back(boost::lexical_cast<T>(rangeIter.first->second.atom));
				rangeIter.first++;
			}
			return true;
		}
		return false;
	}


#ifdef SWIGIMPORTED
protected:
#endif

	std::string raw;
	std::string xml;
	std::string name;
	Type eventType;
	std::string origin;
	std::string origintype;
	Arabica::DOM::Node<std::string> dom;
	std::string sendid;
	bool hideSendId;
	std::string invokeid;
	Data data;
	std::string content;
	std::map<std::string, Data> namelist;
	std::multimap<std::string, Data> params;

	friend USCXML_API std::ostream& operator<< (std::ostream& os, const Event& event);
};

USCXML_API std::ostream& operator<< (std::ostream& os, const Event& event);

}

#endif /* end of include guard: EVENT_H_6174D929 */
