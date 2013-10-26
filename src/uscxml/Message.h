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

#ifndef EVENT_H_XZAQ4HR
#define EVENT_H_XZAQ4HR

#include <map>
#include <list>
#include <set>
#include <vector>
#include <string>

#include <DOM/Document.hpp>
#include <DOM/io/Stream.hpp>

#include <boost/shared_ptr.hpp>
#include <boost/lexical_cast.hpp>
#include <inttypes.h>

#include "uscxml/Common.h"

#include "uscxml/Convenience.h"

#include "uscxml/util/MD5.h"
#include "uscxml/util/Base64.h"

#define TAGNAME(elem) ((Arabica::DOM::Element<std::string>)elem).getTagName()
#define LOCALNAME(elem) ((Arabica::DOM::Element<std::string>)elem).getLocalName()
#define ATTR(elem, attr) ((Arabica::DOM::Element<std::string>)elem).getAttribute(attr)
#define HAS_ATTR(elem, attr) ((Arabica::DOM::Element<std::string>)elem).hasAttribute(attr)

namespace uscxml {

class USCXML_API Blob {
public:
	~Blob();
	Blob(size_t size);
	Blob(void* data, size_t size, const std::string& mimeType, bool adopt = false);
	char* data;
	size_t size;
	std::string mimeType;

	std::string md5() {
		return uscxml::md5(data, size);
	}

	std::string base64() {
		return base64_encode((char* const)data, size);
	}

	Blob* fromBase64(const std::string base64) {
		std::string decoded = base64_decode(base64);
		return new Blob((void*)decoded.c_str(), decoded.length(), mimeType);
	}
};

class USCXML_API Data {
public:
	enum Type {
	    VERBATIM,
	    INTERPRETED,
	};

	Data() : type(INTERPRETED) {}
	Data(const std::string& atom_, Type type_ = INTERPRETED) : atom(atom_), type(type_) {}
	Data(const char* data, size_t size, const std::string& mimeType, bool adopt);
	Data(bool atom_) : type(INTERPRETED) {
		if (atom_) {
			atom = "true";
		} else {
			atom = "false";
		}
	}
	template <typename T> Data(T value) : atom(toStr(value)), type(INTERPRETED) {}

	explicit Data(const Arabica::DOM::Node<std::string>& dom);
	virtual ~Data() {}

	operator bool() const {
		return (atom.length() > 0 || !compound.empty() || !array.empty() || binary);
	}

	bool hasKey(const std::string& key) const {
		return (!compound.empty() && compound.find(key) != compound.end());
	}

	const Data operator[](const std::string& key) const {
		return operator[](key.c_str());
	}

	const Data operator[](const char* key) const {
		if (hasKey(key))
			return compound.at(key);
		Data data;
		return data;
	}

	operator std::string() const {
		return atom;
	}

	operator std::map<std::string, Data>() {
		return compound;
	}

	operator std::list<Data>() {
		return array;
	}

	static Data fromJSON(const std::string& jsonString);
	static std::string toJSON(const Data& data);
	static Data fromXML(const std::string& xmlString);
	Arabica::DOM::Document<std::string> toDocument();
	std::string toXMLString() {
		std::stringstream ss;
		ss << toDocument();
		return ss.str();
	}

	std::map<std::string, Data> getCompound() {
		return compound;
	}
	void setCompound(const std::map<std::string, Data>& compound) {
		this->compound = compound;
	}

	std::list<Data> getArray() {
		return array;
	}
	void setArray(const std::list<Data>& array) {
		this->array = array;
	}

	std::string getAtom() {
		return atom;
	}
	void setAtom(const std::string& atom) {
		this->atom = atom;
	}

	Type getType() {
		return type;
	}
	void setType(const Type type) {
		this->type = type;
	}


#ifdef SWIGIMPORTED
protected:
#endif

	Arabica::DOM::Node<std::string> node;
	std::map<std::string, Data> compound;
	std::list<Data> array;
	std::string atom;
	boost::shared_ptr<Blob> binary;
	Type type;

protected:
	Arabica::DOM::Document<std::string> toNode(const Arabica::DOM::Document<std::string>& factory, const Data& data);
	friend USCXML_API std::ostream& operator<< (std::ostream& os, const Data& data);
};

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

	std::string getName() {
		return name;
	}
	void setName(const std::string& name) {
		this->name = name;
	}

	Type getEventType() {
		return eventType;
	}
	void setEventType(const Type type) {
		this->eventType = type;
	}

	std::string getOrigin() {
		return origin;
	}
	void setOrigin(const std::string& origin) {
		this->origin = origin;
	}

	std::string getOriginType() {
		return origintype;
	}
	void setOriginType(const std::string& originType) {
		this->origintype = originType;
	}

	Arabica::DOM::Node<std::string> getDOM() {
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

	std::string getRaw() {
		return raw;
	}
	void setRaw(const std::string& raw) {
		this->raw = raw;
	}

	std::string getContent() {
		return content;
	}
	void setContent(const std::string& content) {
		this->content = content;
	}

	std::string getXML() {
		return xml;
	}
	void setXML(const std::string& xml) {
		this->xml = xml;
	}

	std::string getSendId() {
		return sendid;
	}
	void setSendId(const std::string& sendId) {
		this->sendid = sendId;
	}

	std::string getInvokeId() {
		return invokeid;
	}
	void setInvokeId(const std::string& invokeId) {
		this->invokeid = invokeId;
	}

	Data getData() {
		return data;
	}
	void setData(const Data& data) {
		this->data = data;
	}

	void initContent(const std::string& content);

	static Event fromXML(const std::string& xmlString);
	Arabica::DOM::Document<std::string> toDocument();
	std::string toXMLString() {
		std::stringstream ss;
		ss << toDocument();
		return ss.str();
	}

	std::map<std::string, Data>& getNameList() {
		return namelist;
	}
	std::multimap<std::string, Data>& getParams() {
		return params;
	}

	typedef std::multimap<std::string, Data> params_t;
	typedef std::map<std::string, Data> namelist_t;

	static bool getParam(params_t params, const std::string& name, Data& target) {
		if (params.find(name) != params.end()) {
			target = params.find(name)->second;
			return true;
		}
		return false;
	}

	static bool getParam(params_t params, const std::string& name, std::list<Data>& target) {
		if (params.find(name) != params.end()) {
			std::pair<params_t::iterator, params_t::iterator> rangeIter = params.equal_range(name);
			while(rangeIter.first != rangeIter.second) {
				target.push_back(rangeIter.first->second);
				rangeIter.first++;
			}
			return true;
		}
		return false;
	}

	template <typename T> static bool getParam(params_t params, const std::string& name, T& target) {
		if (params.find(name) != params.end()) {
			target = boost::lexical_cast<T>(params.find(name)->second.atom);
			return true;
		}
		return false;
	}

	template <typename T> static bool getParam(params_t params, const std::string& name, std::list<T>& target) {
		if (params.find(name) != params.end()) {
			std::pair<params_t::iterator, params_t::iterator> rangeIter = params.equal_range(name);
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

class USCXML_API InvokeRequest : public Event {
public:
	InvokeRequest(Event event) : Event(event) {}
	InvokeRequest() {}

	std::string getType() {
		return type;
	}
	void setType(const std::string& type) {
		this->type = type;
	}

	std::string getSource() {
		return src;
	}
	void setSource(const std::string& src) {
		this->src = src;
	}

	bool isAutoForwarded() {
		return autoForward;
	}
	void setAutoForwarded(bool autoForward) {
		this->autoForward = autoForward;
	}

	static InvokeRequest fromXML(const std::string& xmlString);
	Arabica::DOM::Document<std::string> toDocument();
	std::string toXMLString() {
		std::stringstream ss;
		ss << toDocument();
		return ss.str();
	}

#ifdef SWIGIMPORTED
protected:
#endif
	std::string type;
	std::string src;
	bool autoForward;

	friend USCXML_API std::ostream& operator<< (std::ostream& os, const InvokeRequest& sendReq);

};

class USCXML_API SendRequest : public Event {
public:
	SendRequest() {}
	SendRequest(Event event) : Event(event) {}

	std::string getTarget() {
		return target;
	}
	void setTarget(const std::string& target) {
		this->target = target;
	}

	std::string getType() {
		return type;
	}
	void setType(const std::string& type) {
		this->type = type;
	}

	uint32_t getDelayMs() {
		return delayMs;
	}
	void setDelayMs(uint32_t delayMs) {
		this->delayMs = delayMs;
	}

	static SendRequest fromXML(const std::string& xmlString);
	Arabica::DOM::Document<std::string> toDocument();
	std::string toXMLString() {
		std::stringstream ss;
		ss << toDocument();
		//    std::cout << ss.str() << std::endl;
		return ss.str();
	}

#ifdef SWIGIMPORTED
protected:
#endif
	std::string target;
	std::string type;
	uint32_t delayMs;

	friend USCXML_API std::ostream& operator<< (std::ostream& os, const SendRequest& sendReq);

};

USCXML_API std::ostream& operator<< (std::ostream& os, const InvokeRequest& invokeReq);
USCXML_API std::ostream& operator<< (std::ostream& os, const SendRequest& sendReq);
USCXML_API std::ostream& operator<< (std::ostream& os, const Event& event);
USCXML_API std::ostream& operator<< (std::ostream& os, const Data& data);

}


#endif /* end of include guard: EVENT_H_XZAQ4HR */
