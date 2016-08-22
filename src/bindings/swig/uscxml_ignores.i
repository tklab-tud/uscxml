%ignore uscxml::NumAttr;
%ignore uscxml::SCXMLParser;
%ignore uscxml::InterpreterImpl;
%ignore uscxml::BlobImpl;
%ignore uscxml::StateTransitionMonitor;

#if 0
%ignore uscxml::EventHandlerImpl;
#endif

%ignore uscxml::EventHandlerImpl::setInterpreter(InterpreterImpl*);
%ignore uscxml::EventHandlerImpl::getInterpreter;
%ignore uscxml::EventHandlerImpl::getElement;
%ignore uscxml::EventHandlerImpl::runOnMainThread;

%ignore uscxml::EventHandler::EventHandler(const std::shared_ptr<EventHandlerImpl>);
%ignore uscxml::EventHandler::EventHandler(EventHandler&);
%ignore uscxml::EventHandler::setInterpreter(InterpreterImpl*);
%ignore uscxml::EventHandler::getInterpreter;
%ignore uscxml::EventHandler::getElement;
%ignore uscxml::EventHandler::runOnMainThread;

// interpreter

%ignore uscxml::Interpreter::Interpreter(const std::shared_ptr<InterpreterImpl>);
%ignore uscxml::Interpreter::Interpreter(const Interpreter&);
%ignore uscxml::Interpreter::fromDocument;
%ignore uscxml::Interpreter::fromElement;
%ignore uscxml::Interpreter::fromClone;
%ignore uscxml::Interpreter::getImpl();

%ignore uscxml::InterpreterOptions;

// InterpreterIssues
%ignore uscxml::InterpreterIssue::node;


// InterpreterMonitor

%ignore uscxml::InterpreterMonitor::beforeExitingState(const XERCESC_NS::DOMElement*);
%ignore uscxml::InterpreterMonitor::afterExitingState(const XERCESC_NS::DOMElement*);
%ignore uscxml::InterpreterMonitor::beforeEnteringState(const XERCESC_NS::DOMElement*);
%ignore uscxml::InterpreterMonitor::afterEnteringState(const XERCESC_NS::DOMElement*);

%ignore uscxml::InterpreterMonitor::beforeUninvoking(const XERCESC_NS::DOMElement*, const std::string&);
%ignore uscxml::InterpreterMonitor::afterUninvoking(const XERCESC_NS::DOMElement*, const std::string&);
%ignore uscxml::InterpreterMonitor::beforeInvoking(const XERCESC_NS::DOMElement*, const std::string&);
%ignore uscxml::InterpreterMonitor::afterInvoking(const XERCESC_NS::DOMElement*, const std::string&);

%ignore uscxml::InterpreterMonitor::beforeTakingTransition(const XERCESC_NS::DOMElement*);
%ignore uscxml::InterpreterMonitor::afterTakingTransition(const XERCESC_NS::DOMElement*);

%ignore uscxml::InterpreterMonitor::beforeExecutingContent(const XERCESC_NS::DOMElement*);
%ignore uscxml::InterpreterMonitor::afterExecutingContent(const XERCESC_NS::DOMElement*);


%ignore uscxml::InterpreterOptions::fromCmdLine(int, char**);
%ignore uscxml::InterpreterOptions::additionalParameters;
%ignore uscxml::InterpreterOptions::interpreters;

// Invoker

%ignore uscxml::Invoker::Invoker(const std::shared_ptr<InvokerImpl>);
%ignore uscxml::Invoker::setInterpreter(InterpreterImpl*);
%ignore uscxml::Invoker::getInterpreter;

%ignore uscxml::InvokerImpl::create(InterpreterImpl*);
%ignore uscxml::InvokerImpl::setInterpreter(InterpreterImpl*);
%ignore uscxml::InvokerImpl::getInterpreter;


// DataModel

%ignore uscxml::DataModel::DataModel(const std::shared_ptr<DataModelImpl>);
%ignore uscxml::DataModel::DataModel(const DataModel&);


%ignore uscxml::WrappedDataModel::create(DataModelCallbacks*);
%ignore uscxml::DataModelExtension::dm;

// Executable Content

%ignore uscxml::ExecutableContent::ExecutableContent(const std::shared_ptr<ExecutableContentImpl>);
%ignore uscxml::ExecutableContent::ExecutableContent(const ExecutableContent&);
%ignore uscxml::ExecutableContent::setInterpreter(InterpreterImpl*);
%ignore uscxml::ExecutableContent::getInterpreter;
%ignore uscxml::ExecutableContent::enterElement(const XERCESC_NS::DOMElement*);
%ignore uscxml::ExecutableContent::exitElement(const XERCESC_NS::DOMElement*s);

%ignore uscxml::ExecutableContentImpl::create(InterpreterImpl*);
%ignore uscxml::ExecutableContentImpl::enterElement(const XERCESC_NS::DOMElement*);
%ignore uscxml::ExecutableContentImpl::exitElement(const XERCESC_NS::DOMElement*);
%ignore uscxml::ExecutableContentImpl::setInterpreter(InterpreterImpl*);
%ignore uscxml::ExecutableContentImpl::getInterpreter;

%ignore uscxml::WrappedExecutableContent::create(InterpreterImpl*);
%ignore uscxml::WrappedExecutableContent::enterElement(const XERCESC_NS::DOMElement*);
%ignore uscxml::WrappedExecutableContent::exitElement(const XERCESC_NS::DOMElement*);


// IOProcessor

%ignore uscxml::IOProcessorImpl::create(InterpreterImpl*);

%ignore uscxml::IOProcessor::IOProcessor(const std::shared_ptr<IOProcessorImpl>);
%ignore uscxml::IOProcessor::IOProcessor(const IOProcessor&);

%ignore uscxml::WrappedIOProcessor::create(InterpreterImpl*);


// Factory

%ignore uscxml::Factory::createDataModel;
%ignore uscxml::Factory::createIOProcessor;
%ignore uscxml::Factory::createInvoker;
%ignore uscxml::Factory::createExecutableContent;
%ignore uscxml::Factory::getIOProcessors;

// Event

%ignore uscxml::Event::getParams();
%ignore uscxml::Event::getParam;
%ignore uscxml::Event::setParams;

// HTTPServer

%ignore uscxml::HTTPServer::wsSend;
%ignore uscxml::HTTPServer::wsBroadcast;
%ignore uscxml::HTTPServer::reply;


// Data

%ignore uscxml::Data::toDocument;
%ignore uscxml::Data::Data(const XERCESC_NS::DOMElement*);
%ignore uscxml::Data::Data(const char* data, size_t size, const std::string& mimeType, bool adopt);
%ignore uscxml::Data::Data(const char* data, size_t size, const std::string& mimeType);

// Blob

%ignore uscxml::Blob::Blob(size_t size);
%ignore uscxml::Blob::Blob(const char* data, size_t size, const std::string& mimeType, bool adopt);
%ignore uscxml::Blob::Blob(const std::shared_ptr<BlobImpl>);


%ignore operator!=;
%ignore operator<;
%ignore operator=;
%ignore operator[];
%ignore operator std::list<Data>;
%ignore operator std::string;
%ignore operator std::map<std::string,Data>;
%ignore operator<<;

