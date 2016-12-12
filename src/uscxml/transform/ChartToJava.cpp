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
#include "uscxml/interpreter/Logging.h"
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
	std::string className;
	std::string packageName = "org.uscxml.gen";

	if (_extensions.find("packageName") != _extensions.end()) {
		packageName = _extensions.equal_range("packageName").first->second;
	}

	if (_extensions.find("outputFile") != _extensions.end()) {
		URL outputFileURL(_extensions.equal_range("outputFile").first->second);
		className = outputFileURL.pathComponents().back();
	} else if (_baseURL.pathComponents().size() > 0) {
		className = _baseURL.pathComponents().back();
	} else {
		className = "StateChartBase";
	}

	std::string javaVersion = "5";
	if (_extensions.find("javaVersion") != _extensions.end()) {
		javaVersion = _extensions.equal_range("javaVersion").first->second;
	}
	std::string baseClass = "StateChartJava" + javaVersion + "Impl";


	size_t dotPos = std::string::npos;
	if ((dotPos = className.find(".")) != std::string::npos) {
		className = className.substr(0, dotPos);
	}

	stream << "package " << packageName << ";" << std::endl;
	stream << std::endl;

	stream << "/**" << std::endl;
	stream << "  Generated from source:" << std::endl;
	stream << "  " << (std::string)_baseURL << std::endl;
	stream << "*/" << std::endl;
	stream << std::endl;


	stream << std::endl;
	stream << "import java.util.ArrayList;" << std::endl;
	stream << "import java.util.HashMap;" << std::endl;
	stream << "import org.uscxml.*;" << std::endl;
	stream << std::endl;
	stream << "public abstract class " << className << " extends " << baseClass << " {" << std::endl;
	stream << std::endl;
	stream << "    public " << className << "() {" << std::endl;
	stream << "        transitions = new ArrayList<Transition>();" << std::endl;
	stream << "        states = new ArrayList<State>();" << std::endl;
	stream << "        stateNamesToIndex = new HashMap<String, Integer>();" << std::endl;
	stream << "        /* TODO: initialize all members */" << std::endl;
	stream << "    }" << std::endl;
	stream << "}" << std::endl;

}

}
