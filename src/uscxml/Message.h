#ifndef EVENT_H_XZAQ4HR
#define EVENT_H_XZAQ4HR

#include <map>
#include <list>
#include <vector>
#include <string>

#include <DOM/Document.hpp>
#include <DOM/io/Stream.hpp>

#include <inttypes.h>

#define TAGNAME(elem) ((Arabica::DOM::Element<std::string>)elem).getTagName()
#define ATTR(elem, attr) ((Arabica::DOM::Element<std::string>)elem).getAttribute(attr)
#define HAS_ATTR(elem, attr) ((Arabica::DOM::Element<std::string>)elem).hasAttribute(attr)

namespace uscxml {

class Data {
public:
	enum Type {
	    VERBATIM,
	    INTERPRETED
	};

	Data() {}
	Data(const std::string& atom_, Type type_ = INTERPRETED) : atom(atom_), type(type_) {}
	Data(const Arabica::DOM::Node<std::string>& dom);
	virtual ~Data() {}

	static Data fromXML(const std::string& xmlString);
	Arabica::DOM::Document<std::string> toDocument();
	std::string toXMLString() {
		std::stringstream ss;
		ss << toDocument();
		return ss.str();
	}

	std::map<std::string, Data> compound;
	std::list<Data> array;
	std::string atom;
	Type type;

protected:
	Arabica::DOM::Document<std::string> toNode(const Arabica::DOM::Document<std::string>& factory, const Data& data);

#ifndef SWIGJAVA
	friend std::ostream& operator<< (std::ostream& os, const Data& data);
#endif
};

class Event : public Data {
public:
	enum Type {
	    PLATFORM,
	    INTERNAL,
	    EXTERNAL
	};

	Event() : type(INTERNAL) {}
	Event(const Arabica::DOM::Node<std::string>& xmlString) : type(INTERNAL) {};

	std::string name;
	Type type;
	std::string origin;
	std::string origintype;
//  Arabica::DOM::Node<std::string> dom;
	std::string sendid;
	std::string invokeid;

	static Event fromXML(const std::string& xmlString);
	Arabica::DOM::Document<std::string> toDocument();
	std::string toXMLString() {
		std::stringstream ss;
		ss << toDocument();
		return ss.str();
	}

#ifndef SWIGJAVA
	friend std::ostream& operator<< (std::ostream& os, const Event& event);
#endif
};

class InvokeRequest : public Event {
public:
	std::string type;
	std::string src;
	std::string namelist;
	typedef std::map<std::string, std::string> namelist_t;
	bool autoForward;
	std::multimap<std::string, std::string> params;
	typedef std::multimap<std::string, std::string> params_t;

	std::string content;

	static InvokeRequest fromXML(const std::string& xmlString);
	Arabica::DOM::Document<std::string> toDocument();
	std::string toXMLString() {
		std::stringstream ss;
		ss << toDocument();
		return ss.str();
	}

};

class SendRequest : public Event {
public:
	std::string target;
	std::string type;
	uint32_t delayMs;
	std::map<std::string, std::string> namelist;
	typedef std::map<std::string, std::string> namelist_t;
	std::multimap<std::string, std::string> params;
	typedef std::multimap<std::string, std::string> params_t;
	std::string content;

	static SendRequest fromXML(const std::string& xmlString);
	Arabica::DOM::Document<std::string> toDocument();
	std::string toXMLString() {
		std::stringstream ss;
		ss << toDocument();
//    std::cout << ss.str() << std::endl;
		return ss.str();
	}

};

}


#endif /* end of include guard: EVENT_H_XZAQ4HR */
