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

#ifndef CHARTTOJAVA_H_FD78FFC1
#define CHARTTOJAVA_H_FD78FFC1

#include "Transformer.h"
#include "ChartToC.h"
#include "uscxml/util/DOM.h"

#include "promela/PromelaInlines.h"
#include "promela/PromelaCodeAnalyzer.h"

#include <ostream>

namespace uscxml {

class USCXML_API ChartToJava : public ChartToC {
public:
	virtual ~ChartToJava();
	static Transformer transform(const Interpreter& other);

	void writeTo(std::ostream& stream);

protected:
	ChartToJava(const Interpreter& other);

};

}


#endif /* end of include guard: CHARTTOJAVA_H_FD78FFC1 */
