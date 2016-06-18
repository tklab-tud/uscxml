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

#ifndef WRAPPEDINTERPRETERMONITOR_H_F5C83A0D
#define WRAPPEDINTERPRETERMONITOR_H_F5C83A0D

#include <vector>
#include <list>
#include <ostream>
#include <string>

#include <xercesc/dom/DOM.hpp>

#include "uscxml/config.h"
#include "../../../uscxml/messages/Event.h"
#include "../../../uscxml/interpreter/InterpreterMonitor.h"
#include "../../../uscxml/util/DOM.h"

// forward declare
namespace XERCESC_NS {
    class DOMElement;
}

namespace uscxml {

class WrappedInterpreterMonitor : public InterpreterMonitor {
public:
	WrappedInterpreterMonitor();
	virtual ~WrappedInterpreterMonitor();

    void beforeExitingState(InterpreterImpl* impl, const XERCESC_NS::DOMElement* state);
    virtual void beforeExitingState(const std::string& stateId,
	                                const std::string& xpath,
	                                const std::string& stateXML) {}


    void afterExitingState(InterpreterImpl* impl, const XERCESC_NS::DOMElement* state);
    virtual void afterExitingState(const std::string& stateId,
                                   const std::string& xpath,
                                   const std::string& stateXML) {}


    void beforeExecutingContent(InterpreterImpl* impl, const XERCESC_NS::DOMElement* content);
    virtual void beforeExecutingContent(const std::string& tagName,
	                                    const std::string& xpath,
	                                    const std::string& contentXML) {}


    void afterExecutingContent(InterpreterImpl* impl, const XERCESC_NS::DOMElement* content);
    virtual void afterExecutingContent(const std::string& tagName,
	                                   const std::string& xpath,
	                                   const std::string& contentXML) {}


	void beforeUninvoking(InterpreterImpl* impl,
                          const XERCESC_NS::DOMElement* invoker,
                          const std::string& invokeid);
	virtual void beforeUninvoking(const std::string& xpath,
	                              const std::string& invokeid,
	                              const std::string& invokerXML) {}


	void afterUninvoking(InterpreterImpl* impl,
                         const XERCESC_NS::DOMElement* invoker,
                         const std::string& invokeid);
    virtual void afterUninvoking(const std::string& xpath,
	                             const std::string& invokeid,
	                             const std::string& invokerXML) {}


    void beforeTakingTransition(InterpreterImpl* impl,
                                const XERCESC_NS::DOMElement* transition);
	virtual void beforeTakingTransition(const std::string& xpath,
	                                    const std::string& source,
	                                    const std::list<std::string>& targets,
	                                    const std::string& transitionXML) {}

    void afterTakingTransition(InterpreterImpl* impl,
                               const XERCESC_NS::DOMElement* transition);
    virtual void afterTakingTransition(const std::string& xpath,
	                                   const std::string& source,
	                                   const std::list<std::string>& targets,
	                                   const std::string& transitionXML) {}


    void beforeEnteringState(InterpreterImpl* impl,
                             const XERCESC_NS::DOMElement* state);
    virtual void beforeEnteringState(const std::string& stateId,
	                                 const std::string& xpath,
	                                 const std::string& stateXML) {}


    void afterEnteringState(InterpreterImpl* impl,
                            const XERCESC_NS::DOMElement* state);
    virtual void afterEnteringState(const std::string& stateId,
	                                const std::string& xpath,
	                                const std::string& stateXML) {}


	void beforeInvoking(InterpreterImpl* impl,
                        const XERCESC_NS::DOMElement* invoker,
                        const std::string& invokeid);
    virtual void beforeInvoking(const std::string& xpath,
	                            const std::string& invokeid,
	                            const std::string& invokerXML) {}

    void afterInvoking(InterpreterImpl* impl,
                       const XERCESC_NS::DOMElement* invoker,
                       const std::string& invokeid);
    virtual void afterInvoking(const std::string& xpath,
	                           const std::string& invokeid,
	                           const std::string& invokerXML) {}

	virtual void reportIssue(InterpreterImpl* impl,
                             const InterpreterIssue& issue) {}
};

}


#endif /* end of include guard: WRAPPEDINTERPRETERMONITOR_H_F5C83A0D */
