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

#ifndef SENDREQUEST_H_86B0F6A0
#define SENDREQUEST_H_86B0F6A0

#include "uscxml/messages/Event.h"

namespace uscxml {

class USCXML_API SendRequest : public Event {
public:
	SendRequest() : delayMs(0) {}
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
	std::string toXMLString();

#ifdef SWIGIMPORTED
protected:
#endif
	std::string target;
	std::string type;
	uint32_t delayMs;

	friend USCXML_API std::ostream& operator<< (std::ostream& os, const SendRequest& sendReq);

};

USCXML_API std::ostream& operator<< (std::ostream& os, const SendRequest& sendReq);

}

#endif /* end of include guard: SENDREQUEST_H_86B0F6A0 */
