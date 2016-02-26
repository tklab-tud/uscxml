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

#ifndef INTERPRETERFAST_H_224A5F07
#define INTERPRETERFAST_H_224A5F07

#include "uscxml/Interpreter.h"

namespace uscxml {

class InterpreterFast : public InterpreterImpl {
protected:
	virtual void setupSets();
	virtual void handleDOMEvent(Arabica::DOM::Events::Event<std::string>& event);

private:

	/* TODO: use post-order and document-order per STL comparator (sorted std::set?) */

	std::vector<Arabica::XPath::NodeSet<std::string> > _states;
	std::vector<Arabica::XPath::NodeSet<std::string> > _transitions;

	std::vector<std::vector<bool> > _conflictingTransitions;
	std::vector<std::vector<bool> > _exitSets;
	std::vector<std::vector<bool> > _targetSets;

};

}

#endif /* end of include guard: INTERPRETERFAST_H_224A5F07 */
