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

#ifndef INVOKEREQUEST_H_BAF058E2
#define INVOKEREQUEST_H_BAF058E2

#include "uscxml/messages/Event.h"

namespace uscxml {

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
	std::string toXMLString();

#ifdef SWIGIMPORTED
protected:
#endif
	std::string type;
	std::string src;
	bool autoForward;

	friend USCXML_API std::ostream& operator<< (std::ostream& os, const InvokeRequest& sendReq);

};

USCXML_API std::ostream& operator<< (std::ostream& os, const InvokeRequest& invokeReq);

}

#endif /* end of include guard: INVOKEREQUEST_H_BAF058E2 */
