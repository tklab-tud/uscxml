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

#include "uscxml/transform/ChartToJava.h"
#include "uscxml/util/Predicates.h"
#include "uscxml/util/String.h"

#include <boost/algorithm/string.hpp>
#include <easylogging++.h>
#include <algorithm>

namespace uscxml {

using namespace XERCESC_NS;


Transformer ChartToJava::transform(const Interpreter& other) {
	return std::shared_ptr<TransformerImpl>(new ChartToJava(other));
}

ChartToJava::ChartToJava(const Interpreter& other) : ChartToC(other) {
	_prefix = "U" + _md5.substr(0, 8) + "_";
}

ChartToJava::~ChartToJava() {
}

void ChartToJava::writeTo(std::ostream& stream) {
}

}