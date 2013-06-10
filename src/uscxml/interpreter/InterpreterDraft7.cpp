#include "InterpreterDraft7.h"

#include <glog/logging.h>

namespace uscxml {

using namespace Arabica::XPath;
using namespace Arabica::DOM;

/**
procedure interpret(doc):
    if not valid(doc): failWithError()
    expandScxmlSource(doc)
    configuration = new OrderedSet()
    statesToInvoke = new OrderedSet()
    internalQueue = new Queue()
    externalQueue = new BlockingQueue()
    historyValue = new HashTable()
    datamodel = new Datamodel(doc)
    if doc.binding == "early":
        initializeDatamodel(datamodel, doc)
    running = true
    executeGlobalScriptElement(doc)
    enterStates([doc.initial.transition])
    mainEventLoop()
 */
void InterpreterDraft7::interpret() {
	if (!_isInitialized)
		init();

	if (!_scxml)
		return;

	_sessionId = getUUID();

	std::string datamodelName;
	if (datamodelName.length() == 0 && HAS_ATTR(_scxml, "datamodel"))
		datamodelName = ATTR(_scxml, "datamodel");
	if (datamodelName.length() == 0 && HAS_ATTR(_scxml, "profile")) // SCION SCXML uses profile to specify datamodel
		datamodelName = ATTR(_scxml, "profile");
	if(datamodelName.length() > 0) {
		_dataModel = _factory->createDataModel(datamodelName, this);
	} else {
		_dataModel = _factory->createDataModel("null", this);
	}
	if(datamodelName.length() > 0  && !_dataModel) {
		LOG(ERROR) << "No datamodel for " << datamodelName << " registered";
	}

	if (_dataModel) {
		_dataModel.assign("_x.args", _cmdLineOptions);
	}

	setupIOProcessors();

	_running = true;
	_binding = (HAS_ATTR(_scxml, "binding") && boost::iequals(ATTR(_scxml, "binding"), "late") ? LATE : EARLY);

	// @TODO: Reread http://www.w3.org/TR/scxml/#DataBinding

	if (_dataModel && _binding == EARLY) {
		// initialize all data elements
		NodeSet<std::string> dataElems = _xpath.evaluate("//" + _xpathPrefix + "data", _document).asNodeSet();
		for (unsigned int i = 0; i < dataElems.size(); i++) {
			if (dataElems[i].getNodeType() == Node_base::ELEMENT_NODE)
				initializeData(Element<std::string>(dataElems[i]));
		}
	} else if(_dataModel) {
		// initialize current data elements
		NodeSet<std::string> topDataElems = filterChildElements(_xmlNSPrefix + "data", filterChildElements(_xmlNSPrefix + "datamodel", _scxml));
		for (unsigned int i = 0; i < topDataElems.size(); i++) {
			if (topDataElems[i].getNodeType() == Node_base::ELEMENT_NODE)
				initializeData(Element<std::string>(topDataElems[i]));
		}
	}

	// executeGlobalScriptElements
	NodeSet<std::string> globalScriptElems = _xpath.evaluate("/" + _xpathPrefix + "scxml/" + _xpathPrefix + "script", _document).asNodeSet();
	for (unsigned int i = 0; i < globalScriptElems.size(); i++) {
		if (_dataModel)
			executeContent(globalScriptElems[i]);
	}

	// initial transition might be implict
	NodeSet<std::string> initialTransitions = _xpath.evaluate("/" + _xpathPrefix + "scxml/" + _xpathPrefix + "initial/" + _xpathPrefix + "transition", _document).asNodeSet();
	if (initialTransitions.size() == 0) {
		Arabica::XPath::NodeSet<std::string> initialStates = getInitialStates();

		for (int i = 0; i < initialStates.size(); i++) {
			Arabica::DOM::Element<std::string> initialElem = _document.createElementNS(_nsURL, "initial");
			initialElem.setAttribute("generated", "true");
			Arabica::DOM::Element<std::string> transitionElem = _document.createElementNS(_nsURL, "transition");
			transitionElem.setAttribute("target", ATTR(initialStates[i], "id"));
			initialElem.appendChild(transitionElem);
			_scxml.appendChild(initialElem);
			initialTransitions.push_back(transitionElem);
		}
	}
	enterStates(initialTransitions);

	//  assert(hasLegalConfiguration());
	mainEventLoop();

	if (_parentQueue) {
		// send one final event to unblock eventual listeners
		Event quit;
		quit.name = "done.state.scxml";
		_parentQueue->push(quit);
	}

	// set datamodel to null from this thread
	if(_dataModel)
		_dataModel = DataModel();

}

/**
procedure mainEventLoop():
    while running:
        enabledTransitions = null
        macrostepDone = false
        # Here we handle eventless transitions and transitions
        # triggered by internal events until macrostep is complete
        while running and not macrostepDone:
            enabledTransitions = selectEventlessTransitions()
            if enabledTransitions.isEmpty():
                if internalQueue.isEmpty():
                    macrostepDone = true
                else:
                    internalEvent = internalQueue.dequeue()
                    datamodel["_event"] = internalEvent
                    enabledTransitions = selectTransitions(internalEvent)
            if not enabledTransitions.isEmpty():
                microstep(enabledTransitions.toList())
        # either we're in a final state, and we break out of the loop
        if not running:
            break;
        # or we've completed a macrostep, so we start a new macrostep by waiting for an external event
        # Here we invoke whatever needs to be invoked. The implementation of 'invoke' is platform-specific
        for state in statesToInvoke:
            for inv in state.invoke:
                invoke(inv)
        statesToInvoke.clear()
        # Invoking may have raised internal error events and we iterate to handle them
        if not internalQueue.isEmpty():
            continue
       # A blocking wait for an external event.  Alternatively, if we have been invoked
       # our parent session also might cancel us.  The mechanism for this is platform specific,
       # but here we assume it’s a special event we receive
       externalEvent = externalQueue.dequeue()
       if isCancelEvent(externalEvent):
           running = false
           continue
       datamodel["_event"] = externalEvent
       for state in configuration:
           for inv in state.invoke:
              if inv.invokeid == externalEvent.invokeid:
                  applyFinalize(inv, externalEvent)
              if inv.autoforward:
                  send(inv.id, externalEvent)
       enabledTransitions = selectTransitions(externalEvent)
       if not enabledTransitions.isEmpty():
           microstep(enabledTransitions.toList())
    # End of outer while running loop.  If we get here, we have reached a top-level final state or have been cancelled
    exitInterpreter()
 */
void InterpreterDraft7::mainEventLoop() {
}

/**
procedure exitInterpreter():
    statesToExit = configuration.toList().sort(exitOrder)
    for s in statesToExit:
        for content in s.onexit:
            executeContent(content)
        for inv in s.invoke:
            cancelInvoke(inv)
        configuration.delete(s)
        if isFinalState(s) and isScxmlState(s.parent):
            returnDoneEvent(s.donedata)
 */
void InterpreterDraft7::exitInterpreter() {
}

/**
procedure microstep(enabledTransitions):
    exitStates(enabledTransitions)
    executeTransitionContent(enabledTransitions)
    enterStates(enabledTransitions)
 */
void InterpreterDraft7::microstep(const Arabica::XPath::NodeSet<std::string>& enabledTransitions) {
}

/**
function selectEventlessTransitions():
    enabledTransitions = new OrderedSet()
    atomicStates = configuration.toList().filter(isAtomicState).sort(documentOrder)
    for state in atomicStates:
        loop: for s in [state].append(getProperAncestors(state, null)):
            for t in s.transition:
                if not t.event and conditionMatch(t):
                    enabledTransitions.add(t)
                    break loop
    enabledTransitions = filterPreempted(enabledTransitions)
    return enabledTransitions
 */
Arabica::XPath::NodeSet<std::string> InterpreterDraft7::selectEventlessTransitions() {
	return Arabica::XPath::NodeSet<std::string>();
}

/**
function selectTransitions(event):
    enabledTransitions = new OrderedSet()
    atomicStates = configuration.toList().filter(isAtomicState).sort(documentOrder)
    for state in atomicStates:
        loop: for s in [state].append(getProperAncestors(state, null)):
            for t in s.transition:
                if t.event and nameMatch(t.event, event.name) and conditionMatch(t):
                    enabledTransitions.add(t)
                    break loop
    enabledTransitions = removeConflictingTransitions(enabledTransitions)
    return enabledTransitions
 */
Arabica::XPath::NodeSet<std::string> InterpreterDraft7::selectTransitions(const std::string& event) {
	return Arabica::XPath::NodeSet<std::string>();
}

/**
procedure enterStates(enabledTransitions):
    statesToEnter = new OrderedSet()
    statesForDefaultEntry = new OrderedSet()
    computeEntrySet(enabledTransitions, statesToEnter, statesForDefaultEntry)
    for s in statesToEnter.toList().sort(entryOrder):
        configuration.add(s)
        statesToInvoke.add(s)
        if binding == "late" and s.isFirstEntry:
            initializeDataModel(datamodel.s,doc.s)
            s.isFirstEntry = false
        for content in s.onentry:
            executeContent(content)
        if statesForDefaultEntry.isMember(s):
            executeContent(s.initial.transition)
        if isFinalState(s):
            if isSCXMLElement(s.parent):
                running = false
            else:
                parent = s.parent
                grandparent = parent.parent
                internalQueue.enqueue(new Event("done.state." + parent.id, s.donedata))
                if isParallelState(grandparent):
                    if getChildStates(grandparent).every(isInFinalState):
                        internalQueue.enqueue(new Event("done.state." + grandparent.id))
 */
void InterpreterDraft7::enterStates(const Arabica::XPath::NodeSet<std::string>& enabledTransitions) {
}

/**
procedure exitStates(enabledTransitions):
   statesToExit = computeExitSet(enabledTransitions)
   for s in statesToExit:
       statesToInvoke.delete(s)
   statesToExit = statesToExit.toList().sort(exitOrder)
   for s in statesToExit:
       for h in s.history:
           if h.type == "deep":
               f = lambda s0: isAtomicState(s0) and isDescendant(s0,s)
           else:
               f = lambda s0: s0.parent == s
            historyValue[h.id] = configuration.toList().filter(f)
   for s in statesToExit:
       for content in s.onexit:
           executeContent(content)
       for inv in s.invoke:
           cancelInvoke(inv)
       configuration.delete(s)
 */
void InterpreterDraft7::exitStates(const Arabica::XPath::NodeSet<std::string>& enabledTransitions) {
}

/**
function computeExitSet(transitions)
   statesToExit = new OrderedSet
         for t in transitions:
             domain = getTransitionDomain(t)
       for s in configuration:
           if isDescendant(s,domain):
               statesToExit.add(s)
   return statesToExit
 */
Arabica::XPath::NodeSet<std::string> InterpreterDraft7::computeExitSet(const Arabica::XPath::NodeSet<std::string>& enabledTransitions,
        const Arabica::XPath::NodeSet<std::string>& statesToExit) {
	return Arabica::XPath::NodeSet<std::string>();
}

/**
 procedure computeEntrySet(transitions, statesToEnter, statesForDefaultEntry)
    for t in transitions:
         statesToEnter.union(getTargetStates(t.target))
     for s in statesToEnter:
         addDescendentStatesToEnter(s,statesToEnter,statesForDefaultEntry)
     for t in transitions:
         ancestor = getTransitionDomain(t)
         for s in getTargetStates(t.target)):
             addAncestorStatesToEnter(s, ancestor, statesToEnter, statesForDefaultEntry)
 */
Arabica::XPath::NodeSet<std::string> InterpreterDraft7::computeEntrySet(const Arabica::XPath::NodeSet<std::string>& transitions,
        const Arabica::XPath::NodeSet<std::string>& statesToEnter,
        const Arabica::XPath::NodeSet<std::string>& statesForDefaultEntry) {
	return Arabica::XPath::NodeSet<std::string>();
}

/**
function removeConflictingTransitions(enabledTransitions):
    filteredTransitions = new OrderedSet()
 // toList sorts the transitions in the order of the states that selected them
    for t1 in enabledTransitions.toList():
        t1Preempted = false;
        transitionsToRemove = new OrderedSet()
        for t2 in filteredTransitions.toList():
            if computeExitSet(t1).hasIntersection(computeExitSet(t2)):
                if isDescendent(t1.source, t2.source):
                    transitionsToRemove.add(t2)
                else:
                    t1Preempted = true
                    break
        if not t1Preempted:
            for t3 in transitionsToRemove.toList():
                filteredTransitions.delete(t3)
            filteredTransitions.add(t1)

    return filteredTransitions
 */
Arabica::XPath::NodeSet<std::string> InterpreterDraft7::removeConflictingTransitions(const Arabica::XPath::NodeSet<std::string>& enabledTransitions) {
	return Arabica::XPath::NodeSet<std::string>();
}

/**
 function getTransitionDomain(t)
   tstates = getTargetStates(t.target)
   if not tstates
       return t.source
         elif t.type == "internal" and isCompoundState(t.source) and tstates.every(lambda s: isDescendant(s,t.source)):
       return t.source
   else:
       return findLCCA([t.source].append(tstates))
 */
Arabica::DOM::Node<std::string> InterpreterDraft7::getTransitionDomain(const Arabica::DOM::Node<std::string>& transition) {
	return Arabica::DOM::Node<std::string>();
}

/**
 procedure addDescendentStatesToEnter(state,statesToEnter,statesForDefaultEntry):
     if isHistoryState(state):
         if historyValue[state.id]:
             for s in historyValue[state.id]:
                 addDescendentStatesToEnter(s,statesToEnter,statesForDefaultEntry)
                 addAncestorStatesToEnter(s, state.parent, statesToEnter, statesForDefaultEntry)
         else:
             for t in state.transition:
                 for s in getTargetStates(t.target):
                     addDescendentStatesToEnter(s,statesToEnter,statesForDefaultEntry)
                     addAncestorStatesToEnter(s, state.parent, statesToEnter, statesForDefaultEntry)
     else:
         statesToEnter.add(state)
         if isCompoundState(state):
             statesForDefaultEntry.add(state)
             for s in getTargetStates(state.initial):
                 addDescendentStatesToEnter(s,statesToEnter,statesForDefaultEntry)
                 addAncestorStatesToEnter(s, state, statesToEnter, statesForDefaultEntry)
         else:
             if isParallelState(state):
                 for child in getChildStates(state):
                     if not statesToEnter.some(lambda s: isDescendant(s,child)):
                         addDescendentStatesToEnter(child,statesToEnter,statesForDefaultEntry)
 */
Arabica::XPath::NodeSet<std::string> InterpreterDraft7::addDescendentStatesToEnter(const Arabica::DOM::Node<std::string>& state,
        const Arabica::XPath::NodeSet<std::string>& statesToEnter,
        const Arabica::XPath::NodeSet<std::string>& statesForDefaultEntry) {
	return Arabica::XPath::NodeSet<std::string>();
}

/**
 procedure addAncestorsToEnter(state, ancestor, statesToEnter, statesForDefaultEntry)
    for anc in getProperAncestors(state,ancestor):
        statesToEnter.add(anc)
        if isParallelState(anc):
            for child in getChildStates(anc):
                if not statesToEnter.some(lambda s: isDescendant(s,child)):
                    addStatesToEnter(child,statesToEnter,statesForDefaultEntry)
 */
Arabica::XPath::NodeSet<std::string> InterpreterDraft7::addAncestorsStatesToEnter(const Arabica::DOM::Node<std::string>& state,
        const Arabica::DOM::Node<std::string>& ancestor,
        const Arabica::XPath::NodeSet<std::string>& statesToEnter,
        const Arabica::XPath::NodeSet<std::string>& statesForDefaultEntry) {
	return Arabica::XPath::NodeSet<std::string>();
}

}