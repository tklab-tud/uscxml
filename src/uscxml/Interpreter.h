/**
 *  @file
 *  @author     2012-2013 Stefan Radomski (stefan.radomski@cs.tu-darmstadt.de)
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

#ifndef RUNTIME_H_SQ1MBKGN
#define RUNTIME_H_SQ1MBKGN

// this has to be the first include or MSVC will run amok
#include "uscxml/config.h"
#include "uscxml/Common.h"
#include "uscxml/util/String.h"

#include <iostream> // arabica xpath uses cerr without iostream
#include <boost/shared_ptr.hpp>
#include <set>
#include <map>

#include "uscxml/InterpreterInfo.h"

#include <XPath/XPath.hpp>
#include <DOM/Document.hpp>

#include "uscxml/concurrency/BlockingQueue.h"
#include "uscxml/messages/Data.h"
#include "uscxml/messages/SendRequest.h"
#include "uscxml/debug/InterpreterIssue.h"
#include "uscxml/URL.h"

#include "uscxml/plugins/DataModel.h"
#include "uscxml/plugins/IOProcessor.h"
#include "uscxml/plugins/Invoker.h"
#include "uscxml/plugins/ExecutableContent.h"

#include "dom/DOMUtils.h"

#ifndef TIME_BLOCK
#	ifdef BUILD_PROFILING
#		include "uscxml/concurrency/Timer.h"
#		define TIME_BLOCK Measurement msm(&timer);
#	else
#		define TIME_BLOCK
#	endif
#endif

#define ERROR_PLATFORM_THROW(msg) \
	Event e; \
	e.name = "error.platform"; \
	e.data.compound["cause"] = Data(msg, Data::VERBATIM); \
	throw e; \
 

#define USCXML_MONITOR_CATCH(callback) \
catch (Event e) { \
	LOG(ERROR) << "Syntax error when calling " #callback " on monitors: " << std::endl << e << std::endl; \
} catch (boost::bad_weak_ptr e) { \
	LOG(ERROR) << "Unclean shutdown " << std::endl << std::endl; \
} catch (...) { \
	LOG(ERROR) << "An exception occured when calling " #callback " on monitors"; \
} \
if (_state == USCXML_DESTROYED) { \
	throw boost::bad_weak_ptr(); \
} \
 

#define USCXML_MONITOR_CALLBACK(callback)\
for(monIter_t monIter = _monitors.begin(); monIter != _monitors.end(); monIter++) { \
	try { \
		(*monIter)->callback(shared_from_this()); \
	} \
	USCXML_MONITOR_CATCH(callback) \
}

#define USCXML_MONITOR_CALLBACK2(callback, arg1)\
for(monIter_t monIter = _monitors.begin(); monIter != _monitors.end(); monIter++) { \
	try { \
		(*monIter)->callback(shared_from_this(), arg1); \
	} \
	USCXML_MONITOR_CATCH(callback) \
}

#define USCXML_MONITOR_CALLBACK3(callback, arg1, arg2)\
for(monIter_t monIter = _monitors.begin(); monIter != _monitors.end(); monIter++) { \
	try { \
		(*monIter)->callback(shared_from_this(), arg1, arg2); \
	} \
	USCXML_MONITOR_CATCH(callback) \
}

namespace uscxml {

class HTTPServletInvoker;
class InterpreterMonitor;
class InterpreterHTTPServlet;
class InterpreterWebSocketServlet;
class Factory;
class DelayedEventQueue;

enum Capabilities {
	CAN_NOTHING = 0,
	CAN_BASIC_HTTP = 1,
	CAN_GENERIC_HTTP = 2,
};

class USCXML_API InterpreterOptions {
public:
	InterpreterOptions() :
		withDebugger(false),
		verbose(false),
		checking(false),
		withHTTP(true),
		withHTTPS(true),
		withWS(true),
		logLevel(0),
		httpPort(5080),
		httpsPort(5443),
		wsPort(5081) {
	}

	bool withDebugger;
	bool verbose;
	bool checking;
	bool withHTTP;
	bool withHTTPS;
	bool withWS;
	int logLevel;
	unsigned short httpPort;
	unsigned short httpsPort;
	unsigned short wsPort;
	std::string pluginPath;
	std::string certificate;
	std::string privateKey;
	std::string publicKey;
	std::vector<std::pair<std::string, InterpreterOptions*> > interpreters;
	std::map<std::string, std::string> additionalParameters;

	std::string error;

	operator bool() {
		return error.length() == 0;
	}

	static void printUsageAndExit(const char* progName);
	static InterpreterOptions fromCmdLine(int argc, char** argv);
	unsigned int getCapabilities();

};

enum InterpreterState {
	USCXML_DESTROYED      = -2,  ///< destructor ran - users should never see this one
	USCXML_FINISHED       = -1,  ///< machine reached a final configuration and is done
	USCXML_IDLE           = 0,   ///< stable configuration and queues empty
	USCXML_INITIALIZED    = 1,    ///< DOM is setup and all external components instantiated
	USCXML_INSTANTIATED   = 2,   ///< nothing really, just instantiated
	USCXML_MICROSTEPPED   = 3,   ///< processed one transition set
	USCXML_MACROSTEPPED   = 4,   ///< processed all transition sets and reached a stable configuration
};
USCXML_API std::ostream& operator<< (std::ostream& os, const InterpreterState& interpreterState);

class USCXML_API InterpreterImpl : public InterpreterInfo, public boost::enable_shared_from_this<InterpreterImpl> {
public:

	typedef std::set<InterpreterMonitor*>::iterator monIter_t;

	enum Binding {
		EARLY = 0,
		LATE = 1
	};

	virtual ~InterpreterImpl();

	void cloneFrom(InterpreterImpl* other);
	void cloneFrom(boost::shared_ptr<InterpreterImpl> other);
	virtual void writeTo(std::ostream& stream);

	// TODO: We need to move the destructor to the implementations to make these pure virtual
	virtual InterpreterState interpret();
	virtual InterpreterState step(int waitForMS = 0);

	void start(); ///< Start interpretation in a thread
	void stop(); ///< Stop interpreter thread
	void reset(); ///< Reset state machine
	void join();
	bool isRunning();

	InterpreterState getInterpreterState();

	void addMonitor(InterpreterMonitor* monitor)             {
		_monitors.insert(monitor);
	}

	void removeMonitor(InterpreterMonitor* monitor)          {
		_monitors.erase(monitor);
	}

	void setSourceURL(std::string sourceURL)                 {
		_sourceURL = URL(sourceURL);
		if (_scxml) {
			URL baseURL(sourceURL);
			URL::toBaseURL(baseURL);
			_baseURL[_scxml] = baseURL;
		}
	}

	std::string getSourceURL()                                       {
		return _sourceURL.asString();
	}

	std::string getBaseURL()                                       {
		return getBaseURLForNode(_scxml);
	}

	std::string getBaseURL(const Arabica::DOM::Node<std::string>& refNode)                                       {
		return getBaseURLForNode(refNode);
	}

	std::string getBaseURL(const std::string& xpathExpr)                                       {
		Arabica::XPath::NodeSet<std::string> roots = _xpath.evaluate(xpathExpr, _scxml).asNodeSet();
		if (roots.size() > 0) {
			return getBaseURLForNode(roots[0]);
		}
		return "";
	}

	void setCmdLineOptions(std::map<std::string, std::string> params);
	Data getCmdLineOptions() {
		return _cmdLineOptions;
	}

	InterpreterHTTPServlet* getHTTPServlet() {
		return _httpServlet;
	}

	void setParentQueue(uscxml::concurrency::BlockingQueue<SendRequest>* parentQueue) {
		_parentQueue = parentQueue;
	}

	void setFactory(Factory* factory) {
		_factory = factory;
	}
	Factory* getFactory() {
		return _factory;
	}

	Arabica::XPath::NodeSet<std::string> getNodeSetForXPath(const std::string& xpathExpr) {
		return _xpath.evaluate(xpathExpr, _scxml).asNodeSet();
	}

	void setNameSpaceInfo(const NameSpaceInfo& nsInfo) {
		_nsInfo = nsInfo;
		_xpath.setNamespaceContext(*_nsInfo.getNSContext());
	}
	NameSpaceInfo getNameSpaceInfo() const {
		return _nsInfo;
	}

	void receiveInternal(const Event& event);
	void receive(const Event& event, bool toFront = false);

	Event getCurrentEvent() {
		tthread::lock_guard<tthread::recursive_mutex> lock(_mutex);
		return _currEvent;
	}

	virtual bool isInState(const std::string& stateId);

	Arabica::XPath::NodeSet<std::string> getConfiguration()  {
		tthread::lock_guard<tthread::recursive_mutex> lock(_mutex);
		return _configuration;
	}

	Arabica::XPath::NodeSet<std::string> getBasicConfiguration()  {
		tthread::lock_guard<tthread::recursive_mutex> lock(_mutex);
		Arabica::XPath::NodeSet<std::string> basicConfig;
		for (size_t i = 0; i < _configuration.size(); i++) {
			if (isAtomic(Arabica::DOM::Element<std::string>(_configuration[i])))
				basicConfig.push_back(_configuration[i]);
		}
		return basicConfig;
	}

	void setInitalConfiguration(const std::list<std::string>& states) {
		_startConfiguration = states;
	}
	void setInvokeRequest(const InvokeRequest& req) {
		_invokeReq = req;
	}

	virtual Arabica::DOM::Document<std::string> getDocument() const {
		return _document;
	}

	void setCapabilities(unsigned int capabilities)          {
		_capabilities = capabilities;
	}

	void setName(const std::string& name);
	const std::string& getName()                             {
		return _name;
	}
	const std::string& getSessionId()                        {
		return _sessionId;
	}

	DelayedEventQueue* getDelayQueue()                       {
		return _sendQueue;
	}

	void addIOProcessor(IOProcessor ioProc)   {
		std::list<std::string> names = ioProc.getNames();

		std::list<std::string>::iterator nameIter = names.begin();
		while(nameIter != names.end()) {
			_ioProcessors[*nameIter] = ioProc;
			_ioProcessors[*nameIter].setType(names.front());
			_ioProcessors[*nameIter].setInterpreter(this);

			nameIter++;
		}
	}

	const std::map<std::string, IOProcessor>& getIOProcessors() {
		return _ioProcessors;
	}

	void setDataModel(const DataModel& dataModel)            {
		_userSuppliedDataModel = true;
		_dataModel = dataModel;
	}
	DataModel getDataModel()                                 {
		return _dataModel;
	}

	void addDataModelExtension(DataModelExtension* ext) {
		_dataModelExtensions.insert(ext);
	}

	void setInvoker(const std::string& invokeId, Invoker invoker) {
		_dontDestructOnUninvoke.insert(invokeId);
		_invokers[invokeId] = invoker;
		_invokers[invokeId].setInterpreter(this);
		_invokers[invokeId].setInvokeId(invokeId);
	}

	const std::map<std::string, Invoker>& getInvokers() {
		return _invokers;
	}

	bool runOnMainThread(int fps, bool blocking = true);

	static bool isMember(const Arabica::DOM::Node<std::string>& node, const Arabica::XPath::NodeSet<std::string>& set);

	bool hasLegalConfiguration();
	bool isLegalConfiguration(const Arabica::XPath::NodeSet<std::string>&);
	bool isLegalConfiguration(const std::list<std::string>&);

	static bool isState(const Arabica::DOM::Element<std::string>& state);
	static bool isPseudoState(const Arabica::DOM::Element<std::string>& state);
	static bool isTransitionTarget(const Arabica::DOM::Element<std::string>& elem);
	static bool isTargetless(const Arabica::DOM::Element<std::string>& transition);
	static bool isAtomic(const Arabica::DOM::Element<std::string>& state);
	static bool isFinal(const Arabica::DOM::Element<std::string>& state);
	static bool isHistory(const Arabica::DOM::Element<std::string>& state);
	static bool isParallel(const Arabica::DOM::Element<std::string>& state);
	static bool isCompound(const Arabica::DOM::Element<std::string>& state);
	static bool isDescendant(const Arabica::DOM::Node<std::string>& s1, const Arabica::DOM::Node<std::string>& s2);
	static bool isInEmbeddedDocument(const Arabica::DOM::Node<std::string>& node);
	bool isInitial(const Arabica::DOM::Element<std::string>& state);

	static std::string stateToString(InterpreterState state);

	Arabica::DOM::Element<std::string> getState(const std::string& stateId);
	Arabica::XPath::NodeSet<std::string> getStates(const std::list<std::string>& stateIds);
	Arabica::XPath::NodeSet<std::string> getAllStates();

	Arabica::XPath::NodeSet<std::string> getDocumentInitialTransitions();
	Arabica::XPath::NodeSet<std::string> getInitialStates(Arabica::DOM::Element<std::string> state = Arabica::DOM::Element<std::string>());
	Arabica::XPath::NodeSet<std::string> getReachableStates();

	static Arabica::XPath::NodeSet<std::string> getChildStates(const Arabica::DOM::Node<std::string>& state);
	static Arabica::XPath::NodeSet<std::string> getChildStates(const Arabica::XPath::NodeSet<std::string>& state);
	static Arabica::DOM::Element<std::string> getParentState(const Arabica::DOM::Node<std::string>& element);
	static Arabica::DOM::Node<std::string> getAncestorElement(const Arabica::DOM::Node<std::string>& node, const std::string tagName);
	virtual Arabica::XPath::NodeSet<std::string> getTargetStates(const Arabica::DOM::Element<std::string>& transition);
	virtual Arabica::XPath::NodeSet<std::string> getTargetStates(const Arabica::XPath::NodeSet<std::string>& transitions);
	virtual Arabica::DOM::Node<std::string> getSourceState(const Arabica::DOM::Element<std::string>& transition);

	Arabica::DOM::Node<std::string> findLCCA(const Arabica::XPath::NodeSet<std::string>& states);
	virtual Arabica::XPath::NodeSet<std::string> getProperAncestors(const Arabica::DOM::Node<std::string>& s1, const Arabica::DOM::Node<std::string>& s2);

	virtual void handleDOMEvent(Arabica::DOM::Events::Event<std::string>& event);

  std::vector<std::string> getReachableTargets() {

    std::vector<std::string> e;
		tthread::lock_guard<tthread::recursive_mutex> lock(_mutex);
    Arabica::XPath::NodeSet<std::string> possibleTransitions = DOMUtils::filterChildElements( "transition", _configuration, false);

    for( size_t i = 0; i < possibleTransitions.size(); i++ ) {
        Arabica::DOM::Node<std::string>         transitions = possibleTransitions[ i ];
        Arabica::DOM::NamedNodeMap<std::string> attributes  = transitions.getAttributes();
        Arabica::DOM::Node<std::string>         events      = attributes.getNamedItem("target");
        e.push_back( std::string( events.getNodeValue() ) );
    }
    return e;

  }

  std::vector<std::string> getValidEvents() {

    std::vector<std::string> e;
		tthread::lock_guard<tthread::recursive_mutex> lock(_mutex);
    Arabica::XPath::NodeSet<std::string> possibleTransitions = DOMUtils::filterChildElements( "transition", _configuration, false);

    for( size_t i = 0; i < possibleTransitions.size(); i++ ) {
        Arabica::DOM::Node<std::string>         transitions  = possibleTransitions[ i ];
        Arabica::DOM::NamedNodeMap<std::string> attributes   = transitions.getAttributes();
        Arabica::DOM::Node<std::string>         events       = attributes.getNamedItem("event");
        e.push_back( std::string( events.getNodeValue() ) );
    }
    return e;

  }

protected:
	static void run(void*); // static method for thread to run

	class DOMEventListener : public Arabica::DOM::Events::EventListener<std::string> {
	public:
		DOMEventListener() : _interpreter(NULL) {}
		void handleEvent(Arabica::DOM::Events::Event<std::string>& event);
		InterpreterImpl* _interpreter;
	};

	InterpreterImpl();
	void init();
	void setupDOM();
	void resolveXIncludes();
	void resolveXIncludes(std::list<std::string> includeChain,
	                      std::map<std::string, std::string>& mergedNS,
	                      const std::string& xIncludeNS,
	                      const URL& baseURL,
	                      const Arabica::DOM::Element<std::string>& xinclude);
	virtual void setupIOProcessors();

	std::list<InterpreterIssue> validate();

	void initializeData(const Arabica::DOM::Element<std::string>& data);
	void finalizeAndAutoForwardCurrentEvent();
	void stabilize();
	void microstep(const Arabica::XPath::NodeSet<std::string>& enabledTransitions);
	void exitInterpreter();

	virtual Arabica::XPath::NodeSet<std::string> selectEventlessTransitions();
	virtual Arabica::XPath::NodeSet<std::string> selectTransitions(const std::string& event);
	virtual bool isEnabledTransition(const Arabica::DOM::Element<std::string>& transition, const std::string& event);

	void setInterpreterState(InterpreterState newState);

	bool _stable;
	tthread::thread* _thread;
	tthread::recursive_mutex _mutex;
	tthread::condition_variable _condVar;
	tthread::recursive_mutex _pluginMutex;

	// to be overwritten by implementations - these ought to be pure, but impl destructor runs first
	virtual void enterStates(const Arabica::XPath::NodeSet<std::string>& enabledTransitions) {}
	virtual void exitStates(const Arabica::XPath::NodeSet<std::string>& enabledTransitions) {}
	virtual Arabica::XPath::NodeSet<std::string> removeConflictingTransitions(const Arabica::XPath::NodeSet<std::string>& enabledTransitions) {
		return enabledTransitions;
	}

	InterpreterState _state;

	URL _sourceURL;
	std::map<Arabica::DOM::Node<std::string>, URL> _baseURL; // with xi:include, we might have different base URLs
	Arabica::DOM::Document<std::string> _document;
	Arabica::DOM::Element<std::string> _scxml;
	Arabica::XPath::XPath<std::string> _xpath;
	NameSpaceInfo _nsInfo;

	bool _topLevelFinalReached;
	bool _isInitialized;
	bool _domIsSetup;
	bool _userSuppliedDataModel;
	std::set<std::string> _dontDestructOnUninvoke;

	bool _isStarted;
	bool _isRunning;

	InterpreterImpl::Binding _binding;
	Arabica::XPath::NodeSet<std::string> _configuration;
	Arabica::XPath::NodeSet<std::string> _alreadyEntered;
	Arabica::XPath::NodeSet<std::string> _statesToInvoke;
	std::list<std::string> _startConfiguration;
	InvokeRequest _invokeReq;

	DataModel _dataModel;
	std::map<std::string, Arabica::XPath::NodeSet<std::string> > _historyValue;

	std::list<Event > _internalQueue;
	uscxml::concurrency::BlockingQueue<Event> _externalQueue;
	uscxml::concurrency::BlockingQueue<SendRequest>* _parentQueue;
	DelayedEventQueue* _sendQueue;

	DOMEventListener _domEventListener;

	Event _currEvent;
	Factory* _factory;
	InterpreterHTTPServlet* _httpServlet;
	InterpreterWebSocketServlet* _wsServlet;
	std::set<InterpreterMonitor*> _monitors;
	std::set<std::string> _microstepConfigurations;

	long _lastRunOnMainThread;
	std::string _name;
	std::string _sessionId;
	unsigned int _capabilities;

	Data _cmdLineOptions;

	virtual void executeContent(const Arabica::DOM::Element<std::string>& content, bool rethrow = false);
	virtual void executeContent(const Arabica::DOM::NodeList<std::string>& content, bool rethrow = false);
	virtual void executeContent(const Arabica::XPath::NodeSet<std::string>& content, bool rethrow = false);

	void processContentElement(const Arabica::DOM::Element<std::string>& element,
	                           Arabica::DOM::Node<std::string>& dom,
	                           std::string& text,
	                           std::string& expr);
	void processParamChilds(const Arabica::DOM::Element<std::string>& element,
	                        std::multimap<std::string, Data>& params);
	void processDOMorText(const Arabica::DOM::Element<std::string>& element,
	                      Arabica::DOM::Node<std::string>& dom,
	                      std::string& text);

	virtual void send(const Arabica::DOM::Element<std::string>& element);
	virtual void invoke(const Arabica::DOM::Element<std::string>& element);
	virtual void cancelInvoke(const Arabica::DOM::Element<std::string>& element);
	virtual void internalDoneSend(const Arabica::DOM::Element<std::string>& state, const Arabica::DOM::Element<std::string>& doneData);
	static void delayedSend(void* userdata, std::string eventName);
	void returnDoneEvent(const Arabica::DOM::Node<std::string>& state);

	bool hasConditionMatch(const Arabica::DOM::Element<std::string>& conditional);
	bool isInFinalState(const Arabica::DOM::Element<std::string>& state);
	bool parentIsScxmlState(const Arabica::DOM::Element<std::string>& state);

	IOProcessor getIOProcessor(const std::string& type);
	const URL& getBaseURLForNode(const Arabica::DOM::Node<std::string>& node);

	std::map<std::string, IOProcessor> _ioProcessors;
	std::map<std::string, std::pair<InterpreterImpl*, SendRequest> > _sendIds;
	std::map<std::string, Invoker> _invokers;
	std::map<Arabica::DOM::Node<std::string>, ExecutableContent> _executableContent;
	std::set<DataModelExtension*> _dataModelExtensions;

	std::map<std::pair<Arabica::DOM::Node<std::string>, Arabica::DOM::Node<std::string> >, Arabica::XPath::NodeSet<std::string> >  _cachedProperAncestors;
	std::map<Arabica::DOM::Element<std::string>, Arabica::XPath::NodeSet<std::string> > _cachedTargets;
	std::map<std::string, Arabica::DOM::Element<std::string> > _cachedStates;
	std::map<std::string, URL> _cachedURLs;

	friend class USCXMLInvoker;
	friend class SCXMLIOProcessor;
	friend class Interpreter;
	friend class InterpreterIssue;

};

class USCXML_API Interpreter {
public:
	static Interpreter fromDOM(const Arabica::DOM::Document<std::string>& dom,
	                           const NameSpaceInfo& nameSpaceInfo,
	                           const std::string& sourceURL);
	static Interpreter fromXML(const std::string& xml,
	                           const std::string& sourceURL);
	static Interpreter fromURL(const std::string& URL);
	static Interpreter fromClone(const Interpreter& other);

	Interpreter() : _impl() {} // the empty, invalid interpreter
	Interpreter(boost::shared_ptr<InterpreterImpl> const impl) : _impl(impl) { }
	Interpreter(const Interpreter& other) : _impl(other._impl) { }
	virtual ~Interpreter() {};

	operator bool() const {
		return (!!_impl && _impl->_state != USCXML_DESTROYED);
	}
	bool operator< (const Interpreter& other) const     {
		return _impl < other._impl;
	}
	bool operator==(const Interpreter& other) const     {
		return _impl == other._impl;
	}
	bool operator!=(const Interpreter& other) const     {
		return _impl != other._impl;
	}
	Interpreter& operator= (const Interpreter& other)   {
		_impl = other._impl;
		return *this;
	}

	virtual void writeTo(std::ostream& stream) {
		TIME_BLOCK
		return _impl->writeTo(stream);
	}

	void reset() {
#ifdef BUILD_PROFILING
		timer = Timer();
#endif
		return _impl->reset();
	}

  std::vector<std::string> getReachableTargets() {
    return _impl->getReachableTargets();
  }

  std::vector<std::string> getValidEvents() {
    return _impl->getValidEvents();
  }

	void start() {
		return _impl->start();
	}
	void stop() {
		return _impl->stop();
	}
//	void join() {
//		return _impl->join();
//	};
	bool isRunning() {
		return _impl->isRunning();
	}

	void interpret() {
		_impl->interpret();
	};

	InterpreterState step(int waitForMS = 0) {
		TIME_BLOCK
		return _impl->step(waitForMS);
	};

	InterpreterState step(bool blocking) {
		TIME_BLOCK
		if (blocking)
			return _impl->step(-1);
		return _impl->step(0);
	};

	std::list<InterpreterIssue> validate() {
		TIME_BLOCK
		return _impl->validate();
	}

	InterpreterState getState() {
		return _impl->getInterpreterState();
	}

	void addMonitor(InterpreterMonitor* monitor) {
		return _impl->addMonitor(monitor);
	}

	void removeMonitor(InterpreterMonitor* monitor) {
		return _impl->removeMonitor(monitor);
	}

	void setSourceURL(std::string sourceURL) {
		return _impl->setSourceURL(sourceURL);
	}
	std::string getSourceURL() {
		return _impl->getSourceURL();
	}

	std::string getBaseURL() {
		return _impl->getBaseURL();
	}
	std::string getBaseURL(const std::string& xpathExpr) {
		return _impl->getBaseURL(xpathExpr);
	}
	std::string getBaseURL(const Arabica::DOM::Node<std::string>& refNode) {
		return _impl->getBaseURL(refNode);
	}

	void setNameSpaceInfo(const NameSpaceInfo& nsInfo) {
		_impl->setNameSpaceInfo(nsInfo);
	}
	NameSpaceInfo getNameSpaceInfo() const {
		return _impl->getNameSpaceInfo();
	}

	void setCmdLineOptions(std::map<std::string, std::string> params) {
		return _impl->setCmdLineOptions(params);
	}
	Data getCmdLineOptions() {
		return _impl->getCmdLineOptions();
	}

	InterpreterHTTPServlet* getHTTPServlet() {
		return _impl->getHTTPServlet();
	}

	void setDataModel(const DataModel& dataModel) {
		_impl->setDataModel(dataModel);
	}
	DataModel getDataModel() {
		return _impl->getDataModel();
	}

	void addIOProcessor(IOProcessor ioProc) {
		_impl->addIOProcessor(ioProc);
	}
	const std::map<std::string, IOProcessor>& getIOProcessors() {
		return _impl->getIOProcessors();
	}

	void setInvoker(const std::string& invokeId, Invoker invoker) {
		_impl->setInvoker(invokeId, invoker);
	}
	const std::map<std::string, Invoker>& getInvokers() {
		return _impl->getInvokers();
	}

	void addDataModelExtension(DataModelExtension* ext) {
		_impl->addDataModelExtension(ext);
	}


	void setParentQueue(uscxml::concurrency::BlockingQueue<SendRequest>* parentQueue) {
		return _impl->setParentQueue(parentQueue);
	}
	void setFactory(Factory* factory) {
		return _impl->setFactory(factory);
	}
	Factory* getFactory() {
		return _impl->getFactory();
	}
	Arabica::XPath::NodeSet<std::string> getNodeSetForXPath(const std::string& xpathExpr) {
		TIME_BLOCK
		return _impl->getNodeSetForXPath(xpathExpr);
	}

	void inline receiveInternal(const Event& event) {
		TIME_BLOCK
		return _impl->receiveInternal(event);
	}
	void receive(const Event& event, bool toFront = false) {
		TIME_BLOCK
		return _impl->receive(event, toFront);
	}

	Event getCurrentEvent() {
		TIME_BLOCK
		return _impl->getCurrentEvent();
	}

	bool isInState(const std::string& stateId) {
		TIME_BLOCK
		return _impl->isInState(stateId);
	}

	Arabica::XPath::NodeSet<std::string> getConfiguration() {
		TIME_BLOCK
		return _impl->getConfiguration();
	}

	Arabica::XPath::NodeSet<std::string> getBasicConfiguration() {
		TIME_BLOCK
		return _impl->getBasicConfiguration();
	}

	void setInitalConfiguration(const std::list<std::string>& states) {
		TIME_BLOCK
		return _impl->setInitalConfiguration(states);
	}

//	Arabica::DOM::Node<std::string> getState(const std::string& stateId) {
//		return _impl->getState(stateId);
//	}
//	Arabica::XPath::NodeSet<std::string> getStates(const std::list<std::string>& stateIds) {
//		return _impl->getStates(stateIds);
//	}
//	Arabica::XPath::NodeSet<std::string> getAllStates() {
//		return _impl->getAllStates();
//	}

	Arabica::DOM::Document<std::string> getDocument() const {
		return _impl->getDocument();
	}

	void setCapabilities(unsigned int capabilities) {
		return _impl->setCapabilities(capabilities);
	}

	void setName(const std::string& name) {
		return _impl->setName(name);
	}

	const std::string& getName() {
		return _impl->getName();
	}
	const std::string& getSessionId() {
		return _impl->getSessionId();
	}
	DelayedEventQueue* getDelayQueue() {
		return _impl->getDelayQueue();
	}

	bool runOnMainThread(int fps, bool blocking = true) {
		TIME_BLOCK
		return _impl->runOnMainThread(fps, blocking);
	}

	bool hasLegalConfiguration() {
		TIME_BLOCK
		return _impl->hasLegalConfiguration();
	}

	bool isLegalConfiguration(const Arabica::XPath::NodeSet<std::string>& config) {
		TIME_BLOCK
		return _impl->isLegalConfiguration(config);
	}

	bool isLegalConfiguration(const std::list<std::string>& config) {
		TIME_BLOCK
		return _impl->isLegalConfiguration(config);
	}

	boost::shared_ptr<InterpreterImpl> getImpl() const {
		return _impl;
	}

	static std::map<std::string, boost::weak_ptr<InterpreterImpl> > getInstances();
	static void addInstance(boost::shared_ptr<InterpreterImpl> instance);

#ifdef BUILD_PROFILING
	Timer timer;
#endif


protected:

	void setInvokeRequest(const InvokeRequest& req) {
		return _impl->setInvokeRequest(req);
	}

	// we use a void ptr here as Arabica::SAX::InputSource complicates includes
	static Interpreter fromInputSource(void* source, const std::string& sourceURL);

	boost::shared_ptr<InterpreterImpl> _impl;
	static std::map<std::string, boost::weak_ptr<InterpreterImpl> > _instances;
	static tthread::recursive_mutex _instanceMutex;
};

class USCXML_API InterpreterMonitor {
public:
	InterpreterMonitor() : _copyToInvokers(false) {}
	virtual ~InterpreterMonitor() {}

	virtual void beforeProcessingEvent(Interpreter interpreter, const Event& event) {}
	virtual void beforeMicroStep(Interpreter interpreter) {}

	virtual void beforeExitingState(Interpreter interpreter, const Arabica::DOM::Element<std::string>& state, bool moreComing) {}
	virtual void afterExitingState(Interpreter interpreter, const Arabica::DOM::Element<std::string>& state, bool moreComing) {}

	virtual void beforeExecutingContent(Interpreter interpreter, const Arabica::DOM::Element<std::string>& element) {}
	virtual void afterExecutingContent(Interpreter interpreter, const Arabica::DOM::Element<std::string>& element) {}

	virtual void beforeUninvoking(Interpreter interpreter, const Arabica::DOM::Element<std::string>& invokeElem, const std::string& invokeid) {}
	virtual void afterUninvoking(Interpreter interpreter, const Arabica::DOM::Element<std::string>& invokeElem, const std::string& invokeid) {}

	virtual void beforeTakingTransition(Interpreter interpreter, const Arabica::DOM::Element<std::string>& transition, bool moreComing) {}
	virtual void afterTakingTransition(Interpreter interpreter, const Arabica::DOM::Element<std::string>& transition, bool moreComing) {}

	virtual void beforeEnteringState(Interpreter interpreter, const Arabica::DOM::Element<std::string>& state, bool moreComing) {}
	virtual void afterEnteringState(Interpreter interpreter, const Arabica::DOM::Element<std::string>& state, bool moreComing) {}

	virtual void beforeInvoking(Interpreter interpreter, const Arabica::DOM::Element<std::string>& invokeElem, const std::string& invokeid) {}
	virtual void afterInvoking(Interpreter interpreter, const Arabica::DOM::Element<std::string>& invokeElem, const std::string& invokeid) {}

	virtual void afterMicroStep(Interpreter interpreter) {}

	virtual void onStableConfiguration(Interpreter interpreter) {}

	virtual void beforeCompletion(Interpreter interpreter) {}
	virtual void afterCompletion(Interpreter interpreter) {}

	virtual void reportIssue(Interpreter interpreter, const InterpreterIssue& issue) {}

	void copyToInvokers(bool copy) {
		_copyToInvokers = copy;
	}

	bool copyToInvokers() {
		return _copyToInvokers;
	}

protected:
	bool _copyToInvokers;

};

class StateTransitionMonitor : public uscxml::InterpreterMonitor {
public:
	virtual void beforeTakingTransition(uscxml::Interpreter interpreter, const Arabica::DOM::Element<std::string>& transition, bool moreComing);
	virtual void beforeExecutingContent(Interpreter interpreter, const Arabica::DOM::Element<std::string>& element);
	virtual void onStableConfiguration(uscxml::Interpreter interpreter);
	virtual void beforeProcessingEvent(uscxml::Interpreter interpreter, const uscxml::Event& event);
	virtual void beforeExitingState(uscxml::Interpreter interpreter, const Arabica::DOM::Element<std::string>& state, bool moreComing);
	virtual void beforeEnteringState(uscxml::Interpreter interpreter, const Arabica::DOM::Element<std::string>& state, bool moreComing);
	virtual void beforeMicroStep(uscxml::Interpreter interpreter);

protected:
	static tthread::recursive_mutex _mutex;
	void printNodeSet(const Arabica::XPath::NodeSet<std::string>& config);
	Arabica::XPath::NodeSet<std::string> exitingStates;
	Arabica::XPath::NodeSet<std::string> enteringStates;
};

}

#endif
