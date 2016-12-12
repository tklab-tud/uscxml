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

#ifndef BASICCONTENTEXECUTOR_H_B873199D
#define BASICCONTENTEXECUTOR_H_B873199D

#include "ContentExecutorImpl.h"

namespace uscxml {

using namespace XERCESC_NS;

/**
 * @ingroup execcontent
 * @ingroup impl
 */
class USCXML_API BasicContentExecutor : public ContentExecutorImpl {
public:
	BasicContentExecutor(ContentExecutorCallbacks* callbacks) : ContentExecutorImpl(callbacks) {}
	virtual ~BasicContentExecutor() {}

	virtual std::shared_ptr<ContentExecutorImpl> create(ContentExecutorCallbacks* callbacks);

	void processRaise(XERCESC_NS::DOMElement* content);
	void processSend(XERCESC_NS::DOMElement* element);
	void processCancel(XERCESC_NS::DOMElement* content);
	void processIf(XERCESC_NS::DOMElement* content);
	void processAssign(XERCESC_NS::DOMElement* content);
	void processForeach(XERCESC_NS::DOMElement* content);
	void processLog(XERCESC_NS::DOMElement* content);
	void processScript(XERCESC_NS::DOMElement* content);

	virtual void process(XERCESC_NS::DOMElement* block, const X& xmlPrefix);

	virtual void invoke(XERCESC_NS::DOMElement* invoke);
	virtual void uninvoke(XERCESC_NS::DOMElement* invoke);
	virtual void raiseDoneEvent(XERCESC_NS::DOMElement* state, XERCESC_NS::DOMElement* doneData);

	virtual Data elementAsData(XERCESC_NS::DOMElement* element);

protected:
	void processNameLists(std::map<std::string, Data>& nameMap, XERCESC_NS::DOMElement* element);
	void processParams(std::multimap<std::string, Data>& paramMap, XERCESC_NS::DOMElement* element);

};

}

#endif /* end of include guard: BASICCONTENTEXECUTOR_H_B873199D */
