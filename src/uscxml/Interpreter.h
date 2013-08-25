#ifndef RUNTIME_H_SQ1MBKGN
#define RUNTIME_H_SQ1MBKGN

#include "uscxml/Common.h"
#include "uscxml/URL.h"

#include <boost/uuid/uuid_generators.hpp>
#include <boost/algorithm/string.hpp>

#include <iostream>
#include <set>
#include <map>

#include <XPath/XPath.hpp>
#include <DOM/Document.hpp>
#include <io/uri.hpp>

#include <DOM/SAX2DOM/SAX2DOM.hpp>
#include <SAX/helpers/CatchErrorHandler.hpp>

#include "uscxml/concurrency/tinythread.h"
#include "uscxml/concurrency/eventqueue/DelayedEventQueue.h"
#include "uscxml/concurrency/BlockingQueue.h"
#include "uscxml/Message.h"
#include "uscxml/Factory.h"

#include "uscxml/server/InterpreterServlet.h"

namespace uscxml {

class HTTPServletInvoker;
class InterpreterMonitor;

class NumAttr {
public:
	NumAttr(const std::string& str) {
		size_t valueStart = str.find_first_of("0123456789.");
		if (valueStart != std::string::npos) {
			size_t valueEnd = str.find_last_of("0123456789.");
			if (valueEnd != std::string::npos) {
				value = str.substr(valueStart, (valueEnd - valueStart) + 1);
				size_t unitStart = str.find_first_not_of(" \t", valueEnd + 1);
				if (unitStart != std::string::npos) {
					size_t unitEnd = str.find_last_of(" \t");
					if (unitEnd != std::string::npos && unitEnd > unitStart) {
						unit = str.substr(unitStart, unitEnd - unitStart);
					} else {
						unit = str.substr(unitStart, str.length() - unitStart);
					}
				}
			}
		}
	}

	std::string value;
	std::string unit;
};

enum Capabilities {
    CAN_NOTHING = 0,
    CAN_BASIC_HTTP = 1,
    CAN_GENERIC_HTTP = 2,
};

class InterpreterImpl : public boost::enable_shared_from_this<InterpreterImpl> {
public:

	typedef std::set<InterpreterMonitor*>::iterator monIter_t;

	enum Binding {
	    EARLY = 0,
	    LATE = 1
	};

	virtual ~InterpreterImpl();

	void start();
	static void run(void*);
	void join() {
		if (_thread != NULL) _thread->join();
	};
	bool isRunning() {
		return _running || !_done;
	}

	/// This one ought to be pure, but SWIG will generate gibberish if it is
	virtual void interpret() {};

	void addMonitor(InterpreterMonitor* monitor)             {
		_monitors.insert(monitor);
	}

	void removeMonitor(InterpreterMonitor* monitor)          {
		_monitors.erase(monitor);
	}

	void setBaseURI(std::string baseURI)                     {
		_baseURI = URL(baseURI);
	}
	URL getBaseURI()                                         {
		return _baseURI;
	}

	void setCmdLineOptions(int argc, char** argv);
	Data getCmdLineOptions() {
		return _cmdLineOptions;
	}

	InterpreterServlet* getHTTPServlet() {
		return _httpServlet;
	}

	DataModel getDataModel()                                 {
		return _dataModel;
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
	std::string getXPathPrefix()                             {
		return _xpathPrefix;
	}
	std::string getXMLPrefix()                               {
		return _xmlNSPrefix;
	}
	Arabica::XPath::StandardNamespaceContext<std::string>& getNSContext() {
		return _nsContext;
	}
	std::string getXMLPrefixForNS(const std::string& ns)     {
		if (_nsToPrefix.find(ns) != _nsToPrefix.end())
			return _nsToPrefix[ns] + ":";
		return "";
	}
	void setNameSpaceInfo(const std::map<std::string, std::string> nameSpaceInfo);
	std::map<std::string, std::string> getNameSpaceInfo() {
		return _nameSpaceInfo;
	}

	void receiveInternal(const Event& event);
	void receive(const Event& event, bool toFront = false);

	Event getCurrentEvent() {
		tthread::lock_guard<tthread::recursive_mutex> lock(_mutex);
		return _currEvent;
	}

	Arabica::XPath::NodeSet<std::string> getConfiguration()  {
		tthread::lock_guard<tthread::recursive_mutex> lock(_mutex);
		return _configuration;
	}

	Arabica::XPath::NodeSet<std::string> getBasicConfiguration()  {
		tthread::lock_guard<tthread::recursive_mutex> lock(_mutex);
		Arabica::XPath::NodeSet<std::string> basicConfig;
		for (int i = 0; i < _configuration.size(); i++) {
			if (isAtomic(_configuration[i]))
				basicConfig.push_back(_configuration[i]);
		}
		return basicConfig;
	}

	void setConfiguration(const std::vector<std::string>& states) {
		_userDefinedStartConfiguration = states;
	}
	void setInvokeRequest(const InvokeRequest& req) {
		_invokeReq = req;
	}

	Arabica::DOM::Node<std::string> getState(const std::string& stateId);
	Arabica::XPath::NodeSet<std::string> getStates(const std::vector<std::string>& stateIds);

	Arabica::DOM::Document<std::string>& getDocument()       {
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

	const std::map<std::string, IOProcessor>& getIOProcessors() {
		return _ioProcessors;
	}

	const std::map<std::string, Invoker>& getInvokers() {
		return _invokers;
	}

	bool runOnMainThread(int fps, bool blocking = true);

	static bool isMember(const Arabica::DOM::Node<std::string>& node, const Arabica::XPath::NodeSet<std::string>& set);

	void dump();
	bool hasLegalConfiguration();
	bool isLegalConfiguration(const Arabica::XPath::NodeSet<std::string>&);
	bool isLegalConfiguration(const std::vector<std::string>&);

	static bool isState(const Arabica::DOM::Node<std::string>& state);
	static bool isPseudoState(const Arabica::DOM::Node<std::string>& state);
	static bool isTransitionTarget(const Arabica::DOM::Node<std::string>& elem);
	static bool isTargetless(const Arabica::DOM::Node<std::string>& transition);
	static bool isAtomic(const Arabica::DOM::Node<std::string>& state);
	static bool isFinal(const Arabica::DOM::Node<std::string>& state);
	static bool isHistory(const Arabica::DOM::Node<std::string>& state);
	static bool isParallel(const Arabica::DOM::Node<std::string>& state);
	static bool isCompound(const Arabica::DOM::Node<std::string>& state);
	static bool isDescendant(const Arabica::DOM::Node<std::string>& s1, const Arabica::DOM::Node<std::string>& s2);

	static std::vector<std::string> tokenizeIdRefs(const std::string& idRefs);
	static std::string spaceNormalize(const std::string& text);

	bool isInEmbeddedDocument(const Arabica::DOM::Node<std::string>& node);
	bool isInitial(const Arabica::DOM::Node<std::string>& state);
	Arabica::XPath::NodeSet<std::string> getInitialStates(Arabica::DOM::Node<std::string> state = Arabica::DOM::Node<std::string>());
	static Arabica::XPath::NodeSet<std::string> getChildStates(const Arabica::DOM::Node<std::string>& state);
	static Arabica::DOM::Node<std::string> getParentState(const Arabica::DOM::Node<std::string>& element);
	static Arabica::DOM::Node<std::string> getAncestorElement(const Arabica::DOM::Node<std::string>& node, const std::string tagName);
	Arabica::XPath::NodeSet<std::string> getTargetStates(const Arabica::DOM::Node<std::string>& transition);
	Arabica::DOM::Node<std::string> getSourceState(const Arabica::DOM::Node<std::string>& transition);

	static Arabica::XPath::NodeSet<std::string> filterChildElements(const std::string& tagname, const Arabica::DOM::Node<std::string>& node);
	static Arabica::XPath::NodeSet<std::string> filterChildElements(const std::string& tagName, const Arabica::XPath::NodeSet<std::string>& nodeSet);
	Arabica::DOM::Node<std::string> findLCCA(const Arabica::XPath::NodeSet<std::string>& states);
	Arabica::XPath::NodeSet<std::string> getProperAncestors(const Arabica::DOM::Node<std::string>& s1, const Arabica::DOM::Node<std::string>& s2);
	static std::string getUUID();

protected:
	InterpreterImpl();
	void init();

	void normalize(Arabica::DOM::Element<std::string>& scxml);
	void initializeData(const Arabica::DOM::Element<std::string>& data);
	void setupIOProcessors();

	bool _stable;
	tthread::thread* _thread;
	tthread::recursive_mutex _mutex;
	tthread::condition_variable _condVar;
	tthread::recursive_mutex _pluginMutex;

	URL _baseURI;
	Arabica::DOM::Document<std::string> _document;
	Arabica::DOM::Element<std::string> _scxml;
	Arabica::XPath::XPath<std::string> _xpath;
	Arabica::XPath::StandardNamespaceContext<std::string> _nsContext;
	std::string _xmlNSPrefix; // the actual prefix for elements in the xml file
	std::string _xpathPrefix; // prefix mapped for xpath, "scxml" is _xmlNSPrefix is empty but _nsURL set
	std::string _nsURL;       // ough to be "http://www.w3.org/2005/07/scxml"
	std::map<std::string, std::string> _nsToPrefix;
	std::map<std::string, std::string> _nameSpaceInfo;

	bool _running;
	bool _done;
	bool _isInitialized;
	InterpreterImpl::Binding _binding;
	Arabica::XPath::NodeSet<std::string> _configuration;
	Arabica::XPath::NodeSet<std::string> _statesToInvoke;
	std::vector<std::string> _userDefinedStartConfiguration;
	InvokeRequest _invokeReq;

	DataModel _dataModel;
	std::map<std::string, Arabica::XPath::NodeSet<std::string> > _historyValue;

	std::list<Event > _internalQueue;
	uscxml::concurrency::BlockingQueue<Event> _externalQueue;
	uscxml::concurrency::BlockingQueue<SendRequest>* _parentQueue;
	DelayedEventQueue* _sendQueue;

	Event _currEvent;
	Factory* _factory;
	InterpreterServlet* _httpServlet;
	std::set<InterpreterMonitor*> _monitors;

	void executeContent(const Arabica::DOM::Node<std::string>& content, bool rethrow = false);
	void executeContent(const Arabica::DOM::NodeList<std::string>& content, bool rethrow = false);
	void executeContent(const Arabica::XPath::NodeSet<std::string>& content, bool rethrow = false);

	void processContentElement(const Arabica::DOM::Node<std::string>& element,
	                           Arabica::DOM::Node<std::string>& dom,
	                           std::string& text,
	                           std::string& expr);
	void processParamChilds(const Arabica::DOM::Node<std::string>& element,
	                        std::multimap<std::string, std::string>& params);
	void processDOMorText(const Arabica::DOM::Node<std::string>& element,
	                      Arabica::DOM::Node<std::string>& dom,
	                      std::string& text);

	void send(const Arabica::DOM::Node<std::string>& element);
	void invoke(const Arabica::DOM::Node<std::string>& element);
	void cancelInvoke(const Arabica::DOM::Node<std::string>& element);
	void returnDoneEvent(const Arabica::DOM::Node<std::string>& state);
	void internalDoneSend(const Arabica::DOM::Node<std::string>& state);
	static void delayedSend(void* userdata, std::string eventName);

	static bool nameMatch(const std::string& transitionEvent, const std::string& event);
	bool hasConditionMatch(const Arabica::DOM::Node<std::string>& conditional);
	bool isInFinalState(const Arabica::DOM::Node<std::string>& state);
	bool parentIsScxmlState(const Arabica::DOM::Node<std::string>& state);

	static boost::uuids::random_generator uuidGen;

	long _lastRunOnMainThread;
	std::string _name;
	std::string _sessionId;
	unsigned int _capabilities;

	Data _cmdLineOptions;

	IOProcessor getIOProcessor(const std::string& type);

	std::map<std::string, IOProcessor> _ioProcessors;
	std::map<std::string, std::pair<InterpreterImpl*, SendRequest> > _sendIds;
	std::map<std::string, Invoker> _invokers;
	std::map<std::string, Invoker> _autoForwardees;
	std::map<Arabica::DOM::Node<std::string>, ExecutableContent> _executableContent;

	/// TODO: We need to remember to adapt them when the DOM is operated upon
	std::map<std::string, Arabica::DOM::Node<std::string> > _cachedStates;
	std::map<std::string, URL> _cachedURLs;

	friend class USCXMLInvoker;
	friend class SCXMLIOProcessor;
	friend class Interpreter;
};

class Interpreter {
public:
	static Interpreter fromDOM(const Arabica::DOM::Document<std::string>& dom);
	static Interpreter fromXML(const std::string& xml);
	static Interpreter fromURI(const std::string& uri);
	static Interpreter fromInputSource(Arabica::SAX::InputSource<std::string>& source);

	Interpreter() : _impl() {}
	Interpreter(boost::shared_ptr<InterpreterImpl> const impl) : _impl(impl) { }
	Interpreter(const Interpreter& other) : _impl(other._impl) { }
	virtual ~Interpreter() {};

	operator bool() const {
		return _impl;
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

	void start() {
		return _impl->start();
	}
	void join() {
		return _impl->join();
	};
	bool isRunning() {
		return _impl->isRunning();
	}

	void interpret() {
		_impl->interpret();
	};

	void addMonitor(InterpreterMonitor* monitor)             {
		return _impl->addMonitor(monitor);
	}

	void removeMonitor(InterpreterMonitor* monitor)          {
		return _impl->removeMonitor(monitor);
	}

	void setBaseURI(std::string baseURI)                     {
		return _impl->setBaseURI(baseURI);
	}
	URL getBaseURI()                                         {
		return _impl->getBaseURI();
	}

	void setNameSpaceInfo(const std::map<std::string, std::string> namespaceInfo) {
		_impl->setNameSpaceInfo(namespaceInfo);
	}
	std::map<std::string, std::string> getNameSpaceInfo() {
		return _impl->getNameSpaceInfo();
	}

	void setCmdLineOptions(int argc, char** argv) {
		return _impl->setCmdLineOptions(argc, argv);
	}
	Data getCmdLineOptions() {
		return _impl->getCmdLineOptions();
	}

	InterpreterServlet* getHTTPServlet() {
		return _impl->getHTTPServlet();
	}

	DataModel getDataModel()                                 {
		return _impl->getDataModel();
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
	std::string getXPathPrefix()                             {
		return _impl->getXPathPrefix();
	}
	std::string getXMLPrefix()                               {
		return _impl->getXMLPrefix();
	}
	Arabica::XPath::StandardNamespaceContext<std::string>& getNSContext() {
		return _impl->getNSContext();
	}
	std::string getXMLPrefixForNS(const std::string& ns)     {
		return _impl->getXMLPrefixForNS(ns);
	}

	void inline receiveInternal(const Event& event) {
		return _impl->receiveInternal(event);
	}
	void receive(const Event& event, bool toFront = false)   {
		return _impl->receive(event, toFront);
	}

	Event getCurrentEvent() {
		return _impl->getCurrentEvent();
	}

	Arabica::XPath::NodeSet<std::string> getConfiguration()  {
		return _impl->getConfiguration();
	}

	Arabica::XPath::NodeSet<std::string> getBasicConfiguration()  {
		return _impl->getBasicConfiguration();
	}

	void setConfiguration(const std::vector<std::string>& states) {
		return _impl->setConfiguration(states);
	}
	void setInvokeRequest(const InvokeRequest& req) {
		return _impl->setInvokeRequest(req);
	}

	Arabica::DOM::Node<std::string> getState(const std::string& stateId) {
		return _impl->getState(stateId);
	}
	Arabica::XPath::NodeSet<std::string> getStates(const std::vector<std::string>& stateIds) {
		return _impl->getStates(stateIds);
	}

	Arabica::DOM::Document<std::string>& getDocument()       {
		return _impl->getDocument();
	}

	void setCapabilities(unsigned int capabilities)          {
		return _impl->setCapabilities(capabilities);
	}

	void setName(const std::string& name) {
		return _impl->setName(name);
	}

	const std::string& getName()                             {
		return _impl->getName();
	}
	const std::string& getSessionId()                        {
		return _impl->getSessionId();
	}
	DelayedEventQueue* getDelayQueue()                       {
		return _impl->getDelayQueue();
	}

	const std::map<std::string, IOProcessor>& getIOProcessors() {
		return _impl->getIOProcessors();
	}

	const std::map<std::string, Invoker>& getInvokers() {
		return _impl->getInvokers();
	}

	bool runOnMainThread(int fps, bool blocking = true) {
		return _impl->runOnMainThread(fps, blocking);
	}

	static bool isMember(const Arabica::DOM::Node<std::string>& node, const Arabica::XPath::NodeSet<std::string>& set) {
		return InterpreterImpl::isMember(node, set);
	}

	void dump() {
		return _impl->dump();
	}
	bool hasLegalConfiguration() {
		return _impl->hasLegalConfiguration();
	}

	bool isLegalConfiguration(const Arabica::XPath::NodeSet<std::string>& config) {
		return _impl->isLegalConfiguration(config);
	}

	bool isLegalConfiguration(const std::vector<std::string>& config) {
		return _impl->isLegalConfiguration(config);
	}

	static bool isState(const Arabica::DOM::Node<std::string>& state) {
		return InterpreterImpl::isState(state);
	}
	static bool isPseudoState(const Arabica::DOM::Node<std::string>& state) {
		return InterpreterImpl::isPseudoState(state);
	}
	static bool isTransitionTarget(const Arabica::DOM::Node<std::string>& elem) {
		return InterpreterImpl::isTransitionTarget(elem);
	}
	static bool isTargetless(const Arabica::DOM::Node<std::string>& transition) {
		return InterpreterImpl::isTargetless(transition);
	}
	static bool isAtomic(const Arabica::DOM::Node<std::string>& state) {
		return InterpreterImpl::isAtomic(state);
	}
	static bool isFinal(const Arabica::DOM::Node<std::string>& state) {
		return InterpreterImpl::isFinal(state);
	}
	static bool isHistory(const Arabica::DOM::Node<std::string>& state) {
		return InterpreterImpl::isHistory(state);
	}
	static bool isParallel(const Arabica::DOM::Node<std::string>& state) {
		return InterpreterImpl::isParallel(state);
	}
	static bool isCompound(const Arabica::DOM::Node<std::string>& state) {
		return InterpreterImpl::isCompound(state);
	}
	static bool isDescendant(const Arabica::DOM::Node<std::string>& s1, const Arabica::DOM::Node<std::string>& s2) {
		return InterpreterImpl::isDescendant(s1, s2);
	}

	static std::vector<std::string> tokenizeIdRefs(const std::string& idRefs) {
		return InterpreterImpl::tokenizeIdRefs(idRefs);
	}
	static std::string spaceNormalize(const std::string& text) {
		return InterpreterImpl::spaceNormalize(text);
	}

	bool isInitial(const Arabica::DOM::Node<std::string>& state) {
		return _impl->isInitial(state);
	}
	Arabica::XPath::NodeSet<std::string> getInitialStates(Arabica::DOM::Node<std::string> state = Arabica::DOM::Node<std::string>()) {
		return _impl->getInitialStates(state);
	}
	static Arabica::XPath::NodeSet<std::string> getChildStates(const Arabica::DOM::Node<std::string>& state) {
		return InterpreterImpl::getChildStates(state);
	}
	static Arabica::DOM::Node<std::string> getParentState(const Arabica::DOM::Node<std::string>& element) {
		return InterpreterImpl::getParentState(element);
	}
	static Arabica::DOM::Node<std::string> getAncestorElement(const Arabica::DOM::Node<std::string>& node, const std::string tagName) {
		return InterpreterImpl::getAncestorElement(node, tagName);
	}
	Arabica::XPath::NodeSet<std::string> getTargetStates(const Arabica::DOM::Node<std::string>& transition) {
		return _impl->getTargetStates(transition);
	}
	Arabica::DOM::Node<std::string> getSourceState(const Arabica::DOM::Node<std::string>& transition) {
		return _impl->getSourceState(transition);
	}

	static Arabica::XPath::NodeSet<std::string> filterChildElements(const std::string& tagname, const Arabica::DOM::Node<std::string>& node) {
		return InterpreterImpl::filterChildElements(tagname, node);
	}
	static Arabica::XPath::NodeSet<std::string> filterChildElements(const std::string& tagName, const Arabica::XPath::NodeSet<std::string>& nodeSet) {
		return InterpreterImpl::filterChildElements(tagName, nodeSet);
	}
	Arabica::DOM::Node<std::string> findLCCA(const Arabica::XPath::NodeSet<std::string>& states) {
		return _impl->findLCCA(states);
	}
	Arabica::XPath::NodeSet<std::string> getProperAncestors(const Arabica::DOM::Node<std::string>& s1, const Arabica::DOM::Node<std::string>& s2) {
		return _impl->getProperAncestors(s1, s2);
	}
	static std::string getUUID() {
		return InterpreterImpl::getUUID();
	}

	boost::shared_ptr<InterpreterImpl> getImpl() {
		return _impl;
	}

	static std::map<std::string, boost::weak_ptr<InterpreterImpl> > getInstances() {
		tthread::lock_guard<tthread::recursive_mutex> lock(_instanceMutex);
		std::map<std::string, boost::weak_ptr<InterpreterImpl> >::iterator instIter = _instances.begin();
		while(instIter != _instances.end()) {
			if (!instIter->second.lock()) {
				_instances.erase(instIter++);
			} else {
				instIter++;
			}
		}
		return _instances;
	}

protected:
	boost::shared_ptr<InterpreterImpl> _impl;
	static std::map<std::string, boost::weak_ptr<InterpreterImpl> > _instances;
	static tthread::recursive_mutex _instanceMutex;
};

class InterpreterMonitor {
public:
	virtual ~InterpreterMonitor() {}
	virtual void onStableConfiguration(Interpreter interpreter) {}
	virtual void beforeCompletion(Interpreter interpreter) {}
	virtual void afterCompletion(Interpreter interpreter) {}
	virtual void beforeMicroStep(Interpreter interpreter) {}
	virtual void beforeTakingTransitions(Interpreter interpreter, const Arabica::XPath::NodeSet<std::string>& transitions) {}
	virtual void beforeEnteringStates(Interpreter interpreter, const Arabica::XPath::NodeSet<std::string>& statesToEnter) {}
	virtual void afterEnteringStates(Interpreter interpreter) {}
	virtual void beforeExitingStates(Interpreter interpreter, const Arabica::XPath::NodeSet<std::string>& statesToExit) {}
	virtual void afterExitingStates(Interpreter interpreter) {}
};

}

#endif
