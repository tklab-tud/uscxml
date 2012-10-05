#ifndef RUNTIME_H_SQ1MBKGN
#define RUNTIME_H_SQ1MBKGN

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
#include "uscxml/concurrency/eventqueue/libevent/DelayedEventQueue.h"
#include "uscxml/concurrency/BlockingQueue.h"
#include "uscxml/Message.h"
#include "uscxml/Factory.h"

namespace uscxml {

  class Interpreter {
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
    
		void start();
		static void run(void*);
    void join() { if (_thread != NULL) _thread->join(); };
    
    void interpret();
    bool validate();
    
    void setBaseURI(std::string baseURI)                     { _baseURI = Arabica::io::URI(baseURI); }
    DataModel* getDataModel()                                { return _dataModel; }
    Invoker* getInvoker()                                    { return _invoker; }
    void setInvoker(Invoker* invoker)                        { _invoker = invoker; }
    std::string getNSPrefix()                                { return _nsPrefix; }
    Arabica::XPath::XPath<std::string>& getXPath()           { return _xpath; }
    
    void waitForStabilization();
    
    void receive(Event& event)                               { _externalQueue.push(event); }
    void receiveInternal(Event& event)                       { _internalQueue.push_back(event); }
    Arabica::XPath::NodeSet<std::string> getConfiguration()  { return _configuration; }
    Arabica::DOM::Node<std::string> getState(const std::string& stateId);
    Arabica::DOM::Document<std::string>& getDocument()       { return _doc; }
    
    const std::string& getName()                             { return _name; }
    const std::string& getSessionId()                        { return _sessionId; }
    
    static bool isMember(const Arabica::DOM::Node<std::string>& node, const Arabica::XPath::NodeSet<std::string>& set);

    void dump();
    static void dump(const Arabica::DOM::Node<std::string>& node, int lvl = 0);

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

  protected:
    Interpreter();
    void init();
    
    void normalize(const Arabica::DOM::Document<std::string>& node);
    void setupIOProcessors();
    
    void mainEventLoop();
    
    bool _stable;
    tthread::thread* _thread;
    tthread::mutex _mutex;
    tthread::condition_variable _stabilized;
    
    Arabica::io::URI _baseURI;
    Arabica::DOM::Document<std::string> _doc;
    Arabica::DOM::Element<std::string> _scxml;
    Arabica::XPath::XPath<std::string> _xpath;
    Arabica::XPath::StandardNamespaceContext<std::string> _nsContext;
    std::string _nsPrefix;
    
    bool _running;
    Binding _binding;
    Arabica::XPath::NodeSet<std::string> _configuration;
    Arabica::XPath::NodeSet<std::string> _statesToInvoke;
    
    DataModel* _dataModel;
    std::map<std::string, Arabica::XPath::NodeSet<std::string> > _historyValue;
    
    std::list<Event > _internalQueue;
    uscxml::concurrency::BlockingQueue<Event> _externalQueue;
    DelayedEventQueue* _sendQueue;
    Invoker* _invoker;
    
    static Arabica::io::URI toBaseURI(const Arabica::io::URI& uri);
    static Arabica::io::URI toAbsoluteURI(const Arabica::io::URI& uri, const Arabica::io::URI& baseURI);
    
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
    static Arabica::XPath::NodeSet<std::string> getProperAncestors(const Arabica::DOM::Node<std::string>& s1, const Arabica::DOM::Node<std::string>& s2);
    
    
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
    static const std::string getUUID();
    
    std::string _name;
    std::string _sessionId;
    
    IOProcessor* getIOProcessor(const std::string& type);
//    IOProcessor* getIOProcessorForId(const std::string& sendId);
    
		std::map<std::string, IOProcessor*> _ioProcessors;
    std::map<std::string, std::pair<Interpreter*, SendRequest> > _sendIds;
    std::map<std::string, Invoker*> _invokerIds;
		std::map<std::string, Invoker*> _invokers;

  };
  
#if 0
  class SCXMLParseHandler :
  public Arabica::SAX::EntityResolver<std::string>,
  public Arabica::SAX::DTDHandler<std::string>,
  public Arabica::SAX::ContentHandler<std::string>,
  public Arabica::SAX::CatchErrorHandler<std::string>,
  public Arabica::SAX::LexicalHandler<std::string>,
  public Arabica::SAX::DeclHandler<std::string>
  {
  public:
    SCXMLParseHandler() { }
    virtual ~SCXMLParseHandler() { }
    
    // EntityResolver
    virtual InputSourceT resolveEntity(const std::string& publicId , const std::string& systemId) {
      return InputSourceT();
    }
    
    // DTDHandler
    virtual void notationDecl(const std::string& name,
                              const std::string& publicId,
                              const std::string& systemId) {
      std::cout << "notationDecl" << std::endl;
      std::cout << "  name:" << name << std::endl;
      std::cout << "  publicId:" << publicId << std::endl;
      std::cout << "  systemId:" << systemId << std::endl;
    }
    virtual void unparsedEntityDecl(const std::string& name,
                                    const std::string& publicId,
                                    const std::string& systemId,
                                    const std::string& notationName) {
      std::cout << "unparsedEntityDecl" << std::endl;
      std::cout << "  name:" << name << std::endl;
      std::cout << "  publicId:" << publicId << std::endl;
      std::cout << "  systemId:" << systemId << std::endl;
      std::cout << "  notationName:" << notationName << std::endl;
    }
    
    // ContentHandler
    virtual void setDocumentLocator(const LocatorT& locator) {
      std::cout << "setDocumentLocator" << std::endl;
    }
    virtual void startDocument() {
      std::cout << "startDocument" << std::endl;
    }
    virtual void endDocument() {
      std::cout << "endDocument" << std::endl;
    }
    virtual void startPrefixMapping(const std::string& prefix, const std::string& uri) {
      std::cout << "startPrefixMapping" << std::endl;
      std::cout << "  prefix:" << prefix << std::endl;
      std::cout << "  uri:" << uri << std::endl;
    }
    virtual void endPrefixMapping(const std::string& prefix) {
      std::cout << "endPrefixMapping" << std::endl;
      std::cout << "  prefix:" << prefix << std::endl;
    }
    virtual void startElement(const std::string& namespaceURI, const std::string& localName,
                              const std::string& qName, const AttributesT& atts) {
      std::cout << "startElement" << std::endl;
      std::cout << "  namespaceURI:" << namespaceURI << std::endl;
      std::cout << "  localName:" << localName << std::endl;
      std::cout << "  qName:" << qName << std::endl;
      std::cout << "  atts:" << atts.getLength() << std::endl;
    }
    virtual void endElement(const std::string& namespaceURI, const std::string& localName,
                            const std::string& qName) {
      std::cout << "endElement" << std::endl;
      std::cout << "  namespaceURI:" << namespaceURI << std::endl;
      std::cout << "  localName:" << localName << std::endl;
      std::cout << "  qName:" << qName << std::endl;
    }
    virtual void characters(const std::string& ch) {
      std::cout << "characters" << std::endl;
      std::cout << "  ch:" << ch << std::endl;
    }
    virtual void ignorableWhitespace(const std::string& ch) {
      std::cout << "ignorableWhitespace" << std::endl;
      std::cout << "  ch:" << ch << std::endl;
    }
    virtual void processingInstruction(const std::string& target, const std::string& data) {
      std::cout << "processingInstruction" << std::endl;
      std::cout << "  target:" << target << std::endl;
      std::cout << "  data:" << data << std::endl;
    }
    virtual void skippedEntity(const std::string& name) {
      std::cout << "skippedEntity" << std::endl;
      std::cout << "  name:" << name << std::endl;
    }
    
    // ErrorHandler
    virtual void warning(const SAXParseExceptionT& e) { Arabica::SAX::CatchErrorHandler<std::string>::warning(e); }
    virtual void error(const SAXParseExceptionT& e) { Arabica::SAX::CatchErrorHandler<std::string>::error(e); }
    virtual void fatalError(const SAXParseExceptionT& e) {
      Arabica::SAX::CatchErrorHandler<std::string>::fatalError(e);
    }
    
    // LexicalHandler
    virtual void startDTD(const std::string& name,
                          const std::string& publicId,
                          const std::string& systemId) {
      std::cout << "startDTD" << std::endl;
      std::cout << "  name:" << name << std::endl;
      std::cout << "  publicId:" << publicId << std::endl;
      std::cout << "  systemId:" << systemId << std::endl;
    }
    
    virtual void endDTD() {
      std::cout << "endDTD" << std::endl;
    }
    virtual void startEntity(const std::string& name) {
      std::cout << "startEntity" << std::endl;
      std::cout << "  name:" << name << std::endl;
    }
    virtual void endEntity(const std::string& name) {
      std::cout << "endEntity" << std::endl;
      std::cout << "  name:" << name << std::endl;
    }
    virtual void startCDATA() {
      std::cout << "startCDATA" << std::endl;
    }
    virtual void endCDATA() {
      std::cout << "endCDATA" << std::endl;
    }
    virtual void comment(const std::string& text) {
      std::cout << "comment" << std::endl;
      std::cout << "  text:" << text << std::endl;
    }
    
    // DeclHandler
    virtual void elementDecl(const std::string& name, const std::string& model) {
      std::cout << "elementDecl" << std::endl;
      std::cout << "  name:" << name << std::endl;
      std::cout << "  model:" << model << std::endl;
    }
    virtual void attributeDecl(const std::string& elementName,
                               const std::string& attributeName,
                               const std::string& type,
                               const std::string& valueDefault,
                               const std::string& value) {
      std::cout << "attributeDecl" << std::endl;
      std::cout << "  elementName:" << elementName << std::endl;
      std::cout << "  attributeName:" << attributeName << std::endl;
      std::cout << "  type:" << type << std::endl;
      std::cout << "  valueDefault:" << valueDefault << std::endl;
      std::cout << "  value:" << value << std::endl;
    }
    virtual void internalEntityDecl(const std::string& name, const std::string& value) {
      std::cout << "internalEntityDecl" << std::endl;
      std::cout << "  name:" << name << std::endl;
      std::cout << "  value:" << value << std::endl;
    }
    virtual void externalEntityDecl(const std::string& name,
                                    const std::string& publicId,
                                    const std::string& systemId) {
      std::cout << "externalEntityDecl" << std::endl;
      std::cout << "  name:" << name << std::endl;
      std::cout << "  publicId:" << publicId << std::endl;
      std::cout << "  systemId:" << systemId << std::endl;
    }
    
  };
#endif
}

#endif
