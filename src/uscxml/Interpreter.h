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
#include "uscxml/Common.h"
#include "getopt.h"

#include "uscxml/URL.h"

#include <boost/shared_ptr.hpp>
#include <iostream>
#include <set>
#include <map>

#include <XPath/XPath.hpp>
#include <DOM/Document.hpp>
#include <io/uri.hpp>

#include <DOM/SAX2DOM/SAX2DOM.hpp>
#include <SAX/helpers/CatchErrorHandler.hpp>
#include <DOM/Events/EventTarget.hpp>
#include <DOM/Events/EventListener.hpp>

#include "uscxml/concurrency/tinythread.h"
#include "uscxml/concurrency/eventqueue/DelayedEventQueue.h"
#include "uscxml/concurrency/BlockingQueue.h"
#include "uscxml/Message.h"
#include "uscxml/Factory.h"

#include "uscxml/server/InterpreterServlet.h"

#define USCXML_MONITOR_CATCH_BLOCK(callback)\
catch (Event e) {\
	LOG(ERROR) << "Syntax error when calling " #callback " on monitors: " << std::endl << e << std::endl;\
} catch (boost::bad_weak_ptr e) {\
	LOG(ERROR) << "Unclean shutdown " << std::endl << std::endl;\
} catch (...) {\
	LOG(ERROR) << "An exception occured when calling " #callback " on monitors";\
}\
if (_destroyed) {\
	throw boost::bad_weak_ptr();\
}

namespace uscxml {

class HTTPServletInvoker;
class InterpreterMonitor;

class USCXML_API NumAttr {
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

class USCXML_API InterpreterOptions {
public:
	InterpreterOptions() :
		withDebugger(false),
		verbose(false),
		withHTTP(true),
		withHTTPS(true),
		withWS(true),
		logLevel(0),
		httpPort(0),
		httpsPort(0),
		wsPort(0)
	{}
	
	bool withDebugger;
	bool verbose;
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
	std::map<std::string, InterpreterOptions*> interpreters;
	std::map<std::string, std::string> additionalParameters;

	std::string error;

	operator bool() {
		return error.length() == 0;
	}

	static void printUsageAndExit(const char* progName);
	static InterpreterOptions fromCmdLine(int argc, char** argv);
	unsigned int getCapabilities();

};

class NameSpaceInfo {
public:
	NameSpaceInfo() : nsContext(NULL) {
		init(std::map<std::string, std::string>());
	}

	NameSpaceInfo(const std::map<std::string, std::string>& nsInfo) : nsContext(NULL) {
		init(nsInfo);
	}

	NameSpaceInfo(const NameSpaceInfo& other) : nsContext(NULL) {
		init(other.nsInfo);
	}

	virtual ~NameSpaceInfo() {
		if (nsContext)
			delete nsContext;
	}

	NameSpaceInfo& operator=( const NameSpaceInfo& other ) {
		init(other.nsInfo);
		return *this;
	}

	void setPrefix(Arabica::DOM::Element<std::string> element) {
		if (nsURL.size() > 0)
			element.setPrefix(nsToPrefix[nsURL]);
	}

	void setPrefix(Arabica::DOM::Attr<std::string> attribute) {
		if (nsURL.size() > 0)
			attribute.setPrefix(nsToPrefix[nsURL]);
	}

	const Arabica::XPath::StandardNamespaceContext<std::string>* getNSContext() {
		return nsContext;
	}
	
	std::string nsURL;         // ough to be "http://www.w3.org/2005/07/scxml" but maybe empty
	std::string xpathPrefix;   // prefix mapped for xpath, "scxml" is _xmlNSPrefix is empty but _nsURL set
	std::string xmlNSPrefix;   // the actual prefix for elements in the xml file
	std::map<std::string, std::string> nsToPrefix;  // prefixes for a given namespace
	std::map<std::string, std::string> nsInfo;      // all xmlns mappings

private:
	Arabica::XPath::StandardNamespaceContext<std::string>* nsContext;

	void init(const std::map<std::string, std::string>& nsInfo);
};

class USCXML_API InterpreterImpl : public boost::enable_shared_from_this<InterpreterImpl> {
public:

	typedef std::set<InterpreterMonitor*>::iterator monIter_t;

	enum Binding {
	    EARLY = 0,
	    LATE = 1
	};

	virtual ~InterpreterImpl();

	void copyTo(InterpreterImpl* other);
	void copyTo(boost::shared_ptr<InterpreterImpl> other);

	void start();
	void stop();
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

	void setSourceURI(std::string sourceURI)                 {
		_sourceURI = URL(sourceURI);

		URL baseURI(sourceURI);
		URL::toBaseURL(baseURI);
		_baseURI = baseURI;
	}
	URL getBaseURI()                                         {
		return _baseURI;
	}
	URL getSourceURI()                                       {
		return _sourceURI;
	}

	void setCmdLineOptions(std::map<std::string, std::string> params);
	Data getCmdLineOptions() {
		return _cmdLineOptions;
	}

	InterpreterHTTPServlet* getHTTPServlet() {
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

	Arabica::XPath::NodeSet<std::string> getNodeSetForXPath(const std::string& xpathExpr) {
		return _xpath.evaluate(xpathExpr, _scxml).asNodeSet();
	}

	std::string getXMLPrefixForNS(const std::string& ns) const {
		if (_nsInfo.nsToPrefix.find(ns) != _nsInfo.nsToPrefix.end() && _nsInfo.nsToPrefix.at(ns).size())
			return _nsInfo.nsToPrefix.at(ns) + ":";
		return "";
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
	Arabica::XPath::NodeSet<std::string> getStates(const std::list<std::string>& stateIds);
	Arabica::XPath::NodeSet<std::string> getAllStates();

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

	static std::list<std::string> tokenizeIdRefs(const std::string& idRefs);
	static std::string spaceNormalize(const std::string& text);
	static bool nameMatch(const std::string& transitionEvent, const std::string& event);

	bool isInEmbeddedDocument(const Arabica::DOM::Node<std::string>& node);
	bool isInitial(const Arabica::DOM::Node<std::string>& state);
	Arabica::XPath::NodeSet<std::string> getInitialStates(Arabica::DOM::Node<std::string> state = Arabica::DOM::Node<std::string>());
	static Arabica::XPath::NodeSet<std::string> getChildStates(const Arabica::DOM::Node<std::string>& state);
	static Arabica::XPath::NodeSet<std::string> getChildStates(const Arabica::XPath::NodeSet<std::string>& state);
	static Arabica::DOM::Node<std::string> getParentState(const Arabica::DOM::Node<std::string>& element);
	static Arabica::DOM::Node<std::string> getAncestorElement(const Arabica::DOM::Node<std::string>& node, const std::string tagName);
	virtual Arabica::XPath::NodeSet<std::string> getTargetStates(const Arabica::DOM::Node<std::string>& transition);
	virtual Arabica::XPath::NodeSet<std::string> getTargetStates(const Arabica::XPath::NodeSet<std::string>& transitions);
	virtual Arabica::DOM::Node<std::string> getSourceState(const Arabica::DOM::Node<std::string>& transition);

	static Arabica::XPath::NodeSet<std::string> filterChildElements(const std::string& tagname, const Arabica::DOM::Node<std::string>& node, bool recurse = false);
	static Arabica::XPath::NodeSet<std::string> filterChildElements(const std::string& tagName, const Arabica::XPath::NodeSet<std::string>& nodeSet, bool recurse = false);
	static Arabica::XPath::NodeSet<std::string> filterChildType(const Arabica::DOM::Node_base::Type type, const Arabica::DOM::Node<std::string>& node, bool recurse = false);
	static Arabica::XPath::NodeSet<std::string> filterChildType(const Arabica::DOM::Node_base::Type type, const Arabica::XPath::NodeSet<std::string>& nodeSet, bool recurse = false);
	Arabica::DOM::Node<std::string> findLCCA(const Arabica::XPath::NodeSet<std::string>& states);
	virtual Arabica::XPath::NodeSet<std::string> getProperAncestors(const Arabica::DOM::Node<std::string>& s1, const Arabica::DOM::Node<std::string>& s2);

protected:

	class DOMEventListener : public Arabica::DOM::Events::EventListener<std::string> {
	public:
		void handleEvent(Arabica::DOM::Events::Event<std::string>& event);
		InterpreterImpl* _interpreter;
	};

	InterpreterImpl();
	void init();

	void normalize(Arabica::DOM::Element<std::string>& scxml);
	void initializeData(const Arabica::DOM::Element<std::string>& data);
	virtual void setupIOProcessors();

	bool _stable;
	tthread::thread* _thread;
	tthread::recursive_mutex _mutex;
	tthread::condition_variable _condVar;
	tthread::recursive_mutex _pluginMutex;

	URL _baseURI;
	URL _sourceURI;
	Arabica::DOM::Document<std::string> _document;
	Arabica::DOM::Element<std::string> _scxml;
	Arabica::XPath::XPath<std::string> _xpath;
	NameSpaceInfo _nsInfo;

	bool _running;
	bool _done;
	bool _destroyed; // see comment in destructor
	bool _isInitialized;
	InterpreterImpl::Binding _binding;
	Arabica::XPath::NodeSet<std::string> _configuration;
	Arabica::XPath::NodeSet<std::string> _alreadyEntered;
	Arabica::XPath::NodeSet<std::string> _statesToInvoke;
	std::vector<std::string> _userDefinedStartConfiguration;
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

	virtual void executeContent(const Arabica::DOM::Node<std::string>& content, bool rethrow = false);
	virtual void executeContent(const Arabica::DOM::NodeList<std::string>& content, bool rethrow = false);
	virtual void executeContent(const Arabica::XPath::NodeSet<std::string>& content, bool rethrow = false);

	void processContentElement(const Arabica::DOM::Node<std::string>& element,
	                           Arabica::DOM::Node<std::string>& dom,
	                           std::string& text,
	                           std::string& expr);
	void processParamChilds(const Arabica::DOM::Node<std::string>& element,
	                        std::multimap<std::string, Data>& params);
	void processDOMorText(const Arabica::DOM::Node<std::string>& element,
	                      Arabica::DOM::Node<std::string>& dom,
	                      std::string& text);

	virtual void send(const Arabica::DOM::Node<std::string>& element);
	virtual void invoke(const Arabica::DOM::Node<std::string>& element);
	virtual void cancelInvoke(const Arabica::DOM::Node<std::string>& element);
	virtual void internalDoneSend(const Arabica::DOM::Node<std::string>& state);
	static void delayedSend(void* userdata, std::string eventName);
	void returnDoneEvent(const Arabica::DOM::Node<std::string>& state);

	bool hasConditionMatch(const Arabica::DOM::Node<std::string>& conditional);
	bool isInFinalState(const Arabica::DOM::Node<std::string>& state);
	bool parentIsScxmlState(const Arabica::DOM::Node<std::string>& state);

	long _lastRunOnMainThread;
	std::string _name;
	std::string _sessionId;
	unsigned int _capabilities;

	Data _cmdLineOptions;

	IOProcessor getIOProcessor(const std::string& type);

	std::map<std::string, IOProcessor> _ioProcessors;
	std::map<std::string, std::pair<InterpreterImpl*, SendRequest> > _sendIds;
	std::map<std::string, Invoker> _invokers;
	std::map<Arabica::DOM::Node<std::string>, ExecutableContent> _executableContent;

	/// TODO: We need to remember to adapt them when the DOM is operated upon
	std::map<std::string, Arabica::DOM::Node<std::string> > _cachedStates;
	std::map<std::string, URL> _cachedURLs;

	friend class USCXMLInvoker;
	friend class SCXMLIOProcessor;
	friend class Interpreter;
};

class USCXML_API Interpreter {
public:
	static Interpreter fromDOM(const Arabica::DOM::Document<std::string>& dom,
	                           const NameSpaceInfo& nameSpaceInfo);
	static Interpreter fromXML(const std::string& xml);
	static Interpreter fromURI(const std::string& uri);
	static Interpreter fromInputSource(Arabica::SAX::InputSource<std::string>& source);
	static Interpreter fromClone(const Interpreter& other);

	Interpreter() : _impl() {} // the empty, invalid interpreter
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
	void stop() {
		return _impl->stop();
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

	void addMonitor(InterpreterMonitor* monitor) {
		return _impl->addMonitor(monitor);
	}

	void removeMonitor(InterpreterMonitor* monitor) {
		return _impl->removeMonitor(monitor);
	}

	void setSourceURI(std::string sourceURI) {
		return _impl->setSourceURI(sourceURI);
	}
	URL getSourceURI() {
		return _impl->getSourceURI();
	}
	URL getBaseURI() {
		return _impl->getBaseURI();
	}

	std::string getXMLPrefixForNS(const std::string& ns) const   {
		return _impl->getXMLPrefixForNS(ns);
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

	DataModel getDataModel() {
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
	Arabica::XPath::NodeSet<std::string> getNodeSetForXPath(const std::string& xpathExpr) {
		return _impl->getNodeSetForXPath(xpathExpr);
	}

	void inline receiveInternal(const Event& event) {
		return _impl->receiveInternal(event);
	}
	void receive(const Event& event, bool toFront = false) {
		return _impl->receive(event, toFront);
	}

	Event getCurrentEvent() {
		return _impl->getCurrentEvent();
	}

	bool isInState(const std::string& stateId) {
		return _impl->isInState(stateId);
	}

	Arabica::XPath::NodeSet<std::string> getConfiguration() {
		return _impl->getConfiguration();
	}

	Arabica::XPath::NodeSet<std::string> getBasicConfiguration() {
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
	Arabica::XPath::NodeSet<std::string> getStates(const std::list<std::string>& stateIds) {
		return _impl->getStates(stateIds);
	}
	Arabica::XPath::NodeSet<std::string> getAllStates() {
		return _impl->getAllStates();
	}

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

	static std::list<std::string> tokenizeIdRefs(const std::string& idRefs) {
		return InterpreterImpl::tokenizeIdRefs(idRefs);
	}
	static bool nameMatch(const std::string& transitionEvent, const std::string& event) {
		return InterpreterImpl::nameMatch(transitionEvent, event);
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
	static Arabica::XPath::NodeSet<std::string> getChildStates(const Arabica::XPath::NodeSet<std::string>& state) {
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
	Arabica::XPath::NodeSet<std::string> getTargetStates(const Arabica::XPath::NodeSet<std::string>& transitions) {
		return _impl->getTargetStates(transitions);
	}
	Arabica::DOM::Node<std::string> getSourceState(const Arabica::DOM::Node<std::string>& transition) {
		return _impl->getSourceState(transition);
	}

	static Arabica::XPath::NodeSet<std::string> filterChildElements(const std::string& tagname, const Arabica::DOM::Node<std::string>& node, bool recurse = false) {
		return InterpreterImpl::filterChildElements(tagname, node, recurse);
	}
	static Arabica::XPath::NodeSet<std::string> filterChildElements(const std::string& tagName, const Arabica::XPath::NodeSet<std::string>& nodeSet, bool recurse = false) {
		return InterpreterImpl::filterChildElements(tagName, nodeSet, recurse);
	}
	static Arabica::XPath::NodeSet<std::string> filterChildType(const Arabica::DOM::Node_base::Type type, const Arabica::DOM::Node<std::string>& node, bool recurse = false) {
		return InterpreterImpl::filterChildType(type, node, recurse);
	}
	static Arabica::XPath::NodeSet<std::string> filterChildType(const Arabica::DOM::Node_base::Type type, const Arabica::XPath::NodeSet<std::string>& nodeSet, bool recurse = false) {
		return InterpreterImpl::filterChildType(type, nodeSet, recurse);
	}

	Arabica::DOM::Node<std::string> findLCCA(const Arabica::XPath::NodeSet<std::string>& states) {
		return _impl->findLCCA(states);
	}
	Arabica::XPath::NodeSet<std::string> getProperAncestors(const Arabica::DOM::Node<std::string>& s1, const Arabica::DOM::Node<std::string>& s2) {
		return _impl->getProperAncestors(s1, s2);
	}

	boost::shared_ptr<InterpreterImpl> getImpl() const {
		return _impl;
	}

	static std::map<std::string, boost::weak_ptr<InterpreterImpl> > getInstances();

protected:
	boost::shared_ptr<InterpreterImpl> _impl;
	static std::map<std::string, boost::weak_ptr<InterpreterImpl> > _instances;
	static tthread::recursive_mutex _instanceMutex;
};

class USCXML_API InterpreterMonitor {
public:
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

};

}

#endif
