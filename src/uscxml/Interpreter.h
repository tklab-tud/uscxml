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

namespace uscxml {

class InterpreterMonitor {
public:
  virtual ~InterpreterMonitor() {}
  virtual void onStableConfiguration(Interpreter* interpreter) {}
  virtual void beforeCompletion(Interpreter* interpreter) {}
  virtual void afterCompletion(Interpreter* interpreter) {}
  virtual void beforeMicroStep(Interpreter* interpreter) {}
  virtual void beforeTakingTransitions(Interpreter* interpreter, const Arabica::XPath::NodeSet<std::string>& transitions) {}
  virtual void beforeEnteringStates(Interpreter* interpreter, const Arabica::XPath::NodeSet<std::string>& statesToEnter) {}
  virtual void afterEnteringStates(Interpreter* interpreter) {}
  virtual void beforeExitingStates(Interpreter* interpreter, const Arabica::XPath::NodeSet<std::string>& statesToExit) {}
  virtual void afterExitingStates(Interpreter* interpreter) {}
};
  
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

class Interpreter : protected Arabica::SAX2DOM::Parser<std::string> {
public:
	enum Binding {
	    EARLY = 0,
	    LATE = 1
	};

	virtual ~Interpreter();

	static Interpreter* fromDOM(const Arabica::DOM::Node<std::string>& node);
	static Interpreter* fromXML(const std::string& xml);
	static Interpreter* fromURI(const std::string& uri);
	static Interpreter* fromInputSource(Arabica::SAX::InputSource<std::string>& source);

	virtual void startPrefixMapping(const std::string& /* prefix */, const std::string& /* uri */);

	void start();
	static void run(void*);
	void join() {
		if (_thread != NULL) _thread->join();
	};

	void interpret();

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
	bool toAbsoluteURI(URL& uri);

  void setCmdLineOptions(int argc, char** argv);
  Data getCmdLineOptions() { return _cmdLineOptions; }
  
	DataModel getDataModel()                                 {
		return _dataModel;
	}
	void setParentQueue(uscxml::concurrency::BlockingQueue<Event>* parentQueue) {
		_parentQueue = parentQueue;
	}
	std::string getXPathPrefix()                                {
		return _xpathPrefix;
	}
	std::string getXMLPrefix()                                {
		return _xmlNSPrefix;
	}
	Arabica::XPath::StandardNamespaceContext<std::string>& getNSContext() {
		return _nsContext;
	}

	void receive(Event& event)                               {
		_externalQueue.push(event);
	}
	void receiveInternal(Event& event)                       {
		_internalQueue.push_back(event);
	}
	Arabica::XPath::NodeSet<std::string> getConfiguration()  {
		return _configuration;
	}
	Arabica::DOM::Node<std::string> getState(const std::string& stateId);
	Arabica::DOM::Document<std::string>& getDocument()       {
		return _document;
	}

  void setName(const std::string& name);
	const std::string& getName()                             {
		return _name;
	}
	const std::string& getSessionId()                        {
		return _sessionId;
	}

	bool runOnMainThread(int fps, bool blocking = true);

	static bool isMember(const Arabica::DOM::Node<std::string>& node, const Arabica::XPath::NodeSet<std::string>& set);

	void dump();

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

	bool isInitial(const Arabica::DOM::Node<std::string>& state);
	Arabica::DOM::Node<std::string> getInitialState(Arabica::DOM::Node<std::string> state = Arabica::DOM::Node<std::string>());
	static Arabica::XPath::NodeSet<std::string> getChildStates(const Arabica::DOM::Node<std::string>& state);
	Arabica::XPath::NodeSet<std::string> getTargetStates(const Arabica::DOM::Node<std::string>& transition);

	static Arabica::XPath::NodeSet<std::string> filterChildElements(const std::string& tagname, const Arabica::DOM::Node<std::string>& node);
	static Arabica::XPath::NodeSet<std::string> filterChildElements(const std::string& tagName, const Arabica::XPath::NodeSet<std::string>& nodeSet);
	static const std::string getUUID();

protected:
	Interpreter();
	void init();

	void normalize(const Arabica::DOM::Document<std::string>& node);
	void setupIOProcessors();

	void mainEventLoop();

	bool _stable;
	tthread::thread* _thread;
	tthread::mutex _mutex;

	URL _baseURI;
	Arabica::DOM::Document<std::string> _document;
	Arabica::DOM::Element<std::string> _scxml;
	Arabica::XPath::XPath<std::string> _xpath;
	Arabica::XPath::StandardNamespaceContext<std::string> _nsContext;
	std::string _xmlNSPrefix; // the actual prefix for elements in the xml file
	std::string _xpathPrefix;    // prefix mapped for xpath, "scxml" is _xmlNSPrefix is empty but _nsURL set
	std::string _nsURL;       // ough to be "http://www.w3.org/2005/07/scxml"

	bool _running;
	bool _done;
	Binding _binding;
	Arabica::XPath::NodeSet<std::string> _configuration;
	Arabica::XPath::NodeSet<std::string> _statesToInvoke;

	DataModel _dataModel;
	std::map<std::string, Arabica::XPath::NodeSet<std::string> > _historyValue;

	std::list<Event > _internalQueue;
	uscxml::concurrency::BlockingQueue<Event> _externalQueue;
	uscxml::concurrency::BlockingQueue<Event>* _parentQueue;
	DelayedEventQueue* _sendQueue;

  std::set<InterpreterMonitor*> _monitors;
  
	static URL toBaseURI(const URL& url);

	void microstep(const Arabica::XPath::NodeSet<std::string>& enabledTransitions);
	void exitStates(const Arabica::XPath::NodeSet<std::string>& enabledTransitions);
	void enterStates(const Arabica::XPath::NodeSet<std::string>& enabledTransitions);
	void executeTransitionContent(const Arabica::XPath::NodeSet<std::string>& enabledTransitions);
	void executeContent(const Arabica::DOM::Node<std::string>& content);
	void executeContent(const Arabica::DOM::NodeList<std::string>& content);
	void initializeData(const Arabica::DOM::Node<std::string>& data);
	void exitInterpreter();

	void addStatesToEnter(const Arabica::DOM::Node<std::string>& state,
	                      Arabica::XPath::NodeSet<std::string>& statesToEnter,
	                      Arabica::XPath::NodeSet<std::string>& statesForDefaultEntry);

	Arabica::XPath::NodeSet<std::string> selectEventlessTransitions();
	Arabica::XPath::NodeSet<std::string> selectTransitions(const std::string& event);
	Arabica::DOM::Node<std::string> getSourceState(const Arabica::DOM::Node<std::string>& transition);
	Arabica::DOM::Node<std::string> findLCCA(const Arabica::XPath::NodeSet<std::string>& states);
  Arabica::XPath::NodeSet<std::string> getProperAncestors(const Arabica::DOM::Node<std::string>& s1, const Arabica::DOM::Node<std::string>& s2);


	void send(const Arabica::DOM::Node<std::string>& element);
	void invoke(const Arabica::DOM::Node<std::string>& element);
	void cancelInvoke(const Arabica::DOM::Node<std::string>& element);
	void returnDoneEvent(const Arabica::DOM::Node<std::string>& state);
	void internalDoneSend(const Arabica::DOM::Node<std::string>& state);
	static void delayedSend(void* userdata, std::string eventName);

	static bool nameMatch(const std::string& transitionEvent, const std::string& event);
	Arabica::XPath::NodeSet<std::string> filterPreempted(const Arabica::XPath::NodeSet<std::string>& enabledTransitions);
	bool hasConditionMatch(const Arabica::DOM::Node<std::string>& conditional);
	bool isPreemptingTransition(const Arabica::DOM::Node<std::string>& t1, const Arabica::DOM::Node<std::string>& t2);
	bool isInFinalState(const Arabica::DOM::Node<std::string>& state);
	bool isWithinSameChild(const Arabica::DOM::Node<std::string>& transition);
	bool parentIsScxmlState(Arabica::DOM::Node<std::string> state);

	static std::vector<std::string> tokenizeIdRefs(const std::string& idRefs);

	static boost::uuids::random_generator uuidGen;

	long _lastRunOnMainThread;
	std::string _name;
	std::string _sessionId;

  Data _cmdLineOptions;

	IOProcessor getIOProcessor(const std::string& type);
//    IOProcessor* getIOProcessorForId(const std::string& sendId);

	std::map<std::string, IOProcessor> _ioProcessors;
	std::map<std::string, std::pair<Interpreter*, SendRequest> > _sendIds;
	std::map<std::string, Invoker> _invokers;
	std::map<std::string, Invoker> _autoForwardees;

	/// We need to remember to adapt them when the DOM is operated upon
	std::map<std::string, Arabica::DOM::Node<std::string> > _cachedStates;
};

}

#endif
