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
#include <inttypes.h>

#define TAGNAME(elem) ((Arabica::DOM::Element<std::string>)elem).getTagName()
#define LOCALNAME(elem) ((Arabica::DOM::Element<std::string>)elem).getLocalName()
#define ATTR(elem, attr) ((Arabica::DOM::Element<std::string>)elem).getAttribute(attr)
#define HAS_ATTR(elem, attr) ((Arabica::DOM::Element<std::string>)elem).hasAttribute(attr)

namespace uscxml {

class Blob {
public:
	~Blob();
	Blob(size_t size);
	Blob(void* data, size_t size, bool adopt = false);
	char* _data;
	size_t _size;
};
	
class Data {
public:
	enum Type {
	    VERBATIM,
	    INTERPRETED,
	};

	Data() : type(INTERPRETED) {}
	Data(const std::string& atom_, Type type_ = INTERPRETED) : atom(atom_), type(type_) {}
	Data(const char* data, size_t size, bool adopt);
	explicit Data(const Arabica::DOM::Node<std::string>& dom);
	virtual ~Data() {}

	operator bool() const {
		return (atom.length() > 0 || !compound.empty() || !array.empty());
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

	operator std::string() {
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

	std::map<std::string, Data> compound;
	std::list<Data> array;
	std::string atom;
	boost::shared_ptr<Blob> binary;
	Type type;

protected:
	Arabica::DOM::Document<std::string> toNode(const Arabica::DOM::Document<std::string>& factory, const Data& data);
	friend std::ostream& operator<< (std::ostream& os, const Data& data);
};

class Event {
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

	std::map<std::string, std::string>& getNameList() {
		return namelist;
	}
	std::multimap<std::string, std::string>& getParams() {
		return params;
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
	std::map<std::string, std::string> namelist;
	std::multimap<std::string, std::string> params;

	typedef std::multimap<std::string, std::string> params_t;
	typedef std::map<std::string, std::string> namelist_t;

	friend std::ostream& operator<< (std::ostream& os, const Event& event);
};

class InvokeRequest : public Event {
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

	friend std::ostream& operator<< (std::ostream& os, const InvokeRequest& sendReq);

};

class SendRequest : public Event {
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

	friend std::ostream& operator<< (std::ostream& os, const SendRequest& sendReq);

};

}


#endif /* end of include guard: EVENT_H_XZAQ4HR */
