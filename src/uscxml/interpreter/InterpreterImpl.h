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

#ifndef INTERPRETERIMPL_H_2A79C83D
#define INTERPRETERIMPL_H_2A79C83D

#include <memory>
#include <mutex>
#include <list>
#include <map>
#include <string>
#include <limits>

#include "uscxml/Common.h"
#include "uscxml/util/URL.h"
#include "uscxml/plugins/Factory.h"
#include "uscxml/plugins/DataModelImpl.h"
#include "uscxml/interpreter/MicroStepImpl.h"
#include "uscxml/interpreter/ContentExecutorImpl.h"
#include "uscxml/interpreter/EventQueue.h"
#include "uscxml/interpreter/EventQueueImpl.h"
#include "uscxml/util/DOM.h"

namespace uscxml {

class InterpreterMonitor;
class InterpreterIssue;

/**
 * @ingroup interpreter
 * @ingroup impl
 */
class USCXML_API InterpreterImpl :
	public MicroStepCallbacks,
	public DataModelCallbacks,
	public ContentExecutorCallbacks,
	public DelayedEventQueueCallbacks,
	public std::enable_shared_from_this<InterpreterImpl> {
public:
	enum Binding {
		EARLY = 0,
		LATE = 1
	};

	InterpreterImpl();
	virtual ~InterpreterImpl();

	void cloneFrom(InterpreterImpl* other);
	void cloneFrom(std::shared_ptr<InterpreterImpl> other);

	virtual InterpreterState step(size_t blockMs) {
		if (!_isInitialized) {
			init();
			_state = USCXML_INITIALIZED;
		} else {
			_state = _microStepper.step(blockMs);
		}
		return _state;
	}

	virtual void reset() {///< Reset state machine
		if (_microStepper)
			_microStepper.reset();

		_isInitialized = false;
		_state = USCXML_INSTANTIATED;
//        _dataModel.reset();
		if (_delayQueue)
			_delayQueue.reset();
//        _contentExecutor.reset();
	}

	virtual void cancel(); ///< Cancel and finalize state machine

	InterpreterState getState() {
		return _state;
	}

	std::list<XERCESC_NS::DOMElement*> getConfiguration() {
		return _microStepper.getConfiguration();
	}

	void addMonitor(InterpreterMonitor* monitor) {
		_monitors.insert(monitor);
	}

	void removeMonitor(InterpreterMonitor* monitor) {
		_monitors.erase(monitor);
	}

	/**
	 MicrostepCallbacks
	 */
	virtual Event dequeueInternal() {
		_currEvent = _internalQueue.dequeue(0);
		if (_currEvent)
			_dataModel.setEvent(_currEvent);
		return _currEvent;
	}
	virtual Event dequeueExternal(size_t blockMs);
	virtual bool isTrue(const std::string& expr);

	virtual void raiseDoneEvent(XERCESC_NS::DOMElement* state, XERCESC_NS::DOMElement* doneData) {
		_execContent.raiseDoneEvent(state, doneData);
	}

	virtual void process(XERCESC_NS::DOMElement* block) {
		_execContent.process(block, _xmlPrefix);
	}

	virtual bool isMatched(const Event& event, const std::string& eventDesc);
	virtual void initData(XERCESC_NS::DOMElement* element);

	virtual void invoke(XERCESC_NS::DOMElement* invoke) {
		_execContent.invoke(invoke);
	}

	virtual void uninvoke(XERCESC_NS::DOMElement* invoke) {
		_execContent.uninvoke(invoke);
	}

	virtual std::set<InterpreterMonitor*> getMonitors() {
		return _monitors;
	}

	virtual Interpreter getInterpreter() {
		return Interpreter(shared_from_this());
	}

	/**
	 DataModelCallbacks
	 */
	virtual const std::string& getName() {
		return _name;
	}
	virtual const std::string& getSessionId() {
		return _sessionId;
	}
	virtual const std::map<std::string, IOProcessor>& getIOProcessors() {
		return _ioProcs;
	}
	virtual const std::map<std::string, Invoker>& getInvokers() {
		return _invokers;
	}

	virtual bool isInState(const std::string& stateId) {
		return _microStepper.isInState(stateId);
	}
	virtual XERCESC_NS::DOMDocument* getDocument() const {
		return _document;
	}

	/**
	 ContentExecutorCallbacks
	 */

	virtual void enqueueInternal(const Event& event) {
		return _internalQueue.enqueue(event);
	}
	virtual void enqueueExternal(const Event& event) {
		return _externalQueue.enqueue(event);
	}
	virtual void enqueueExternalDelayed(const Event& event, size_t delayMs, const std::string& eventUUID) {
		return _delayQueue.enqueueDelayed(event, delayMs, eventUUID);
	}
	virtual void cancelDelayed(const std::string& eventId);

	virtual size_t getLength(const std::string& expr) {
		return _dataModel.getLength(expr);
	}

	virtual void setForeach(const std::string& item,
	                        const std::string& array,
	                        const std::string& index,
	                        uint32_t iteration) {
		return _dataModel.setForeach(item, array, index, iteration);
	}
	virtual Data evalAsData(const std::string& expr) {
		return _dataModel.evalAsData(expr);
	}

	virtual Data getAsData(const std::string& expr) {
		return _dataModel.getAsData(expr);
	}

	virtual void assign(const std::string& location, const Data& data);

	virtual std::string getInvokeId() {
		return _invokeId;
	}
	virtual std::string getBaseURL() {
		return _baseURL;
	}

	virtual bool checkValidSendType(const std::string& type, const std::string& target);
	virtual void invoke(const std::string& type, const std::string& src, bool autoForward, XERCESC_NS::DOMElement* finalize, const Event& invokeEvent);
	virtual void uninvoke(const std::string& invokeId);
	virtual void enqueue(const std::string& type, const std::string& target, size_t delayMs, const Event& sendEvent);

	virtual const Event& getCurrentEvent() {
		return _currEvent;
	}

	/**
	 DelayedEventQueueCallbacks
	 */

	virtual void eventReady(Event& event, const std::string& eventUUID);

	/** --- */

	void setActionLanguage(const ActionLanguage& al) {
		if (al.logger) // we intialized _logger as the default logger already
			_logger = al.logger;
		_execContent = al.execContent;
		_microStepper = al.microStepper;
		_dataModel = al.dataModel;
		_internalQueue = al.internalQueue;
		_externalQueue = al.externalQueue;
		_delayQueue = al.delayedQueue;
	}

	void setFactory(Factory* factory) {
		_factory = factory;
	}

	virtual Logger getLogger() {
		return _logger;
	}

	static std::map<std::string, std::weak_ptr<InterpreterImpl> > getInstances();

	virtual XERCESC_NS::DOMDocument* getDocument() {
		return _document;
	}

protected:
	static void addInstance(std::shared_ptr<InterpreterImpl> instance);

	Binding _binding;

	std::string _sessionId;
	std::string _name;
	std::string _invokeId; // TODO: Never set!

	bool _isInitialized;
	XERCESC_NS::DOMDocument* _document;
	XERCESC_NS::DOMElement* _scxml;

	std::map<std::string, std::tuple<std::string, std::string, std::string> > _delayedEventTargets;

	virtual void init();

	static std::map<std::string, std::weak_ptr<InterpreterImpl> > _instances;
	static std::recursive_mutex _instanceMutex;
	std::recursive_mutex _delayMutex;

	friend class Interpreter;
	friend class InterpreterIssue;
	friend class TransformerImpl;
	friend class USCXMLInvoker;
	friend class SCXMLIOProcessor;
	friend class DebugSession;
	friend class Debugger;

	X _xmlPrefix;
	X _xmlNS;
	Factory* _factory;

	URL _baseURL;

	MicroStep _microStepper;
	DataModel _dataModel;
	ContentExecutor _execContent;
	Logger _logger = Logger::getDefault();

	InterpreterState _state;

	EventQueue _internalQueue;
	EventQueue _externalQueue;
	EventQueue _parentQueue;
	DelayedEventQueue _delayQueue;

	Event _currEvent;
	Event _invokeReq;

	std::map<std::string, IOProcessor> _ioProcs;
	std::map<std::string, Invoker> _invokers;
	std::set<std::string> _autoForwarders;
	std::set<InterpreterMonitor*> _monitors;

private:
	void setupDOM();
};

}

#endif /* end of include guard: INTERPRETERIMPL_H_2A79C83D */
