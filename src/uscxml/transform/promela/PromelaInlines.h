/**
 *  @file
 *  @author     2016 Stefan Radomski (stefan.radomski@cs.tu-darmstadt.de)
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

#ifndef PROMELAINLINES_H_29BF8EF3
#define PROMELAINLINES_H_29BF8EF3

#include "uscxml/config.h"
#include "uscxml/Common.h"
#include "uscxml/messages/Data.h"
#include "uscxml/util/DOM.h"

#include <xercesc/dom/DOM.hpp>
#include <list>
#include <string>

namespace uscxml {

class USCXML_API PromelaInline {
public:
	enum PromelaInlineType {
		PROMELA_NIL             = 0x0000,
		PROMELA_LTL             = 0x0001,
		PROMELA_CODE            = 0x0002,
		PROMELA_EVENT_ALL_BUT   = 0x0004,
		PROMELA_EVENT_ONLY      = 0x0008,
		PROMELA_PROGRESS_LABEL  = 0x0010,
		PROMELA_ACCEPT_LABEL    = 0x0020,
		PROMELA_END_LABEL       = 0x0040
	};

	PromelaInline(const XERCESC_NS::DOMNode* node);
	virtual ~PromelaInline() {}

	operator bool() {
		return (type != PROMELA_NIL);
	}

	std::list<PromelaInline*> children;
	PromelaInline* prevSibling;
	PromelaInline* nextSibling;

	virtual void dump();

	virtual bool relatesTo(const XERCESC_NS::DOMNode* node) {
		return container == node;
	}

	size_t level;
	std::string content;
	const XERCESC_NS::DOMElement* container;
	PromelaInlineType type;

protected:
	PromelaInline() : prevSibling(NULL), nextSibling(NULL), type(PROMELA_NIL) {};
};


class USCXML_API PromelaEventSource : public PromelaInline {
public:
	PromelaEventSource(const PromelaInline& pmlInline) {
		type = pmlInline.type;
		container = pmlInline.container;
		content = pmlInline.content;
		events = Data::fromJSON(pmlInline.content);
	}

	virtual bool relatesTo(const XERCESC_NS::DOMNode* node) {
		return container == node || DOMUtils::isDescendant(node, container);
	}

	Data events;
};


class USCXML_API PromelaInlines {
public:

	PromelaInlines(const XERCESC_NS::DOMNode* node);
	PromelaInlines() {}

	virtual ~PromelaInlines();

	std::list<PromelaInline*> getRelatedTo(const XERCESC_NS::DOMNode* node, PromelaInline::PromelaInlineType type);
	std::list<PromelaInline*> getAllOfType(uint32_t type);

	std::map<const XERCESC_NS::DOMNode*, std::list<PromelaInline*> > inlines;
	std::list<PromelaInline*> allInlines;

	static std::list<std::string> getStringLiterals(const Data& data);
	static std::list<std::string> getEventNames(const Data& data);


};

}

#endif /* end of include guard: PROMELAINLINES_H_29BF8EF3 */
