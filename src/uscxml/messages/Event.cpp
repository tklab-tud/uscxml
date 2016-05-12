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
#include "uscxml/util/DOM.h"

namespace uscxml {

std::ostream& operator<< (std::ostream& os, const Event& event) {
	std::string indent;
	for (size_t i = 0; i < _dataIndentation; i++) {
		indent += "  ";
	}

//    os << indent << (event.eventType == Event::EXTERNAL ? "External" : "Internal") << " Event " << (event.dom ? "with DOM attached" : "") << std::endl;

	if (event.name.size() > 0)
		os << indent << "  name: " << event.name << std::endl;
	if (event.origin.size() > 0)
		os << indent << "  origin: " << event.origin << std::endl;
	if (event.origintype.size() > 0)
		os << indent << "  origintype: " << event.origintype << std::endl;
//    if (event.content.size() > 0)
//        os << indent << "  content: '" << event.content << "'" << std::endl;
	if (event.params.size() > 0) {
		std::multimap<std::string, Data>::const_iterator paramIter = event.params.begin();
		os << indent << "  params:" << std::endl;
		_dataIndentation++;
		while(paramIter != event.params.end()) {
			os << indent << "    " << paramIter->first << ": ";
			os << indent << paramIter->second << std::endl;
			paramIter++;
		}
		_dataIndentation--;
	}
	if (event.namelist.size() > 0) {
		std::map<std::string, Data>::const_iterator namelistIter = event.namelist.begin();
		os << indent << "  namelist:" << std::endl;
		_dataIndentation++;
		while(namelistIter != event.namelist.end()) {
			os << indent << "    " << namelistIter->first << ": ";
			os << indent << namelistIter->second << std::endl;
			namelistIter++;
		}
		_dataIndentation--;

	}
	_dataIndentation++;
	os << indent << "  data: " << event.data << std::endl;
	_dataIndentation--;
	return os;
}

}