%ignore uscxml::NumAttr;
%ignore uscxml::SCXMLParser;
%ignore uscxml::InterpreterImpl;
%ignore uscxml::BlobImpl;
#if 0
%ignore uscxml::EventHandlerImpl;
#endif

%ignore create();

%ignore uscxml::EventHandlerImpl::setInterpreter(InterpreterImpl*);
%ignore uscxml::EventHandlerImpl::getInterpreter;
%ignore uscxml::EventHandlerImpl::setElement(const Arabica::DOM::Element<std::string>&);
%ignore uscxml::EventHandlerImpl::getElement;
%ignore uscxml::EventHandlerImpl::runOnMainThread;

%ignore uscxml::EventHandler::EventHandler(const boost::shared_ptr<EventHandlerImpl>);
%ignore uscxml::EventHandler::EventHandler(EventHandler&);
%ignore uscxml::EventHandler::setInterpreter(InterpreterImpl*);
%ignore uscxml::EventHandler::getInterpreter;
%ignore uscxml::EventHandler::setElement(const Arabica::DOM::Element<std::string>&);
%ignore uscxml::EventHandler::getElement;
%ignore uscxml::EventHandler::runOnMainThread;

%ignore uscxml::NameSpaceInfo::NameSpaceInfo(const std::map<std::string, std::string>&);
%ignore uscxml::NameSpaceInfo::NameSpaceInfo(const NameSpaceInfo&);
%ignore uscxml::NameSpaceInfo::setPrefix(Arabica::DOM::Element<std::string>);
%ignore uscxml::NameSpaceInfo::setPrefix(Arabica::DOM::Attr<std::string>);
%ignore uscxml::NameSpaceInfo::getNSContext;
%ignore uscxml::NameSpaceInfo::nsURL;
%ignore uscxml::NameSpaceInfo::xpathPrefix;
%ignore uscxml::NameSpaceInfo::xmlNSPrefix;
%ignore uscxml::NameSpaceInfo::nsToPrefix;
%ignore uscxml::NameSpaceInfo::nsInfo;

// interpreter

%ignore uscxml::Interpreter::Interpreter(const boost::shared_ptr<InterpreterImpl>);
%ignore uscxml::Interpreter::Interpreter(const Interpreter&);
%ignore uscxml::Interpreter::getDelayQueue();
%ignore uscxml::Interpreter::fromURI(const URL&);
%ignore uscxml::Interpreter::fromDOM;
%ignore uscxml::Interpreter::fromClone;
%ignore uscxml::Interpreter::start();
%ignore uscxml::Interpreter::stop();
%ignore uscxml::Interpreter::isRunning();
%ignore uscxml::Interpreter::setCmdLineOptions(std::map<std::string, std::string>);
%ignore uscxml::Interpreter::setDataModel(const DataModel& dataModel);
%ignore uscxml::Interpreter::addIOProcessor(IOProcessor ioProc);
%ignore uscxml::Interpreter::setInvoker(const std::string& invokeId, Invoker invoker);
%ignore uscxml::Interpreter::getDocument;
%ignore uscxml::Interpreter::getImpl;
%ignore uscxml::Interpreter::runOnMainThread;
%ignore uscxml::Interpreter::getHTTPServlet();
%ignore uscxml::Interpreter::getNodeSetForXPath(const std::string&);
%ignore uscxml::Interpreter::isLegalConfiguration(const Arabica::XPath::NodeSet<std::string>&);
%ignore uscxml::Interpreter::getInstances();

// InterpreterIssues
%ignore uscxml::InterpreterIssue::node;

// InterpreterMonitor

%ignore uscxml::InterpreterMonitor::beforeExitingState(Interpreter, const Arabica::DOM::Element<std::string>&, bool);
%ignore uscxml::InterpreterMonitor::afterExitingState(Interpreter, const Arabica::DOM::Element<std::string>&, bool);
%ignore uscxml::InterpreterMonitor::beforeEnteringState(Interpreter, const Arabica::DOM::Element<std::string>&, bool);
%ignore uscxml::InterpreterMonitor::afterEnteringState(Interpreter, const Arabica::DOM::Element<std::string>&, bool);

%ignore uscxml::InterpreterMonitor::beforeUninvoking(Interpreter, const Arabica::DOM::Element<std::string>&, const std::string&);
%ignore uscxml::InterpreterMonitor::afterUninvoking(Interpreter, const Arabica::DOM::Element<std::string>&, const std::string&);
%ignore uscxml::InterpreterMonitor::beforeInvoking(Interpreter, const Arabica::DOM::Element<std::string>&, const std::string&);
%ignore uscxml::InterpreterMonitor::afterInvoking(Interpreter, const Arabica::DOM::Element<std::string>&, const std::string&);

%ignore uscxml::InterpreterMonitor::beforeTakingTransition(Interpreter, const Arabica::DOM::Element<std::string>&, bool);
%ignore uscxml::InterpreterMonitor::afterTakingTransition(Interpreter, const Arabica::DOM::Element<std::string>&, bool);

%ignore uscxml::InterpreterMonitor::beforeExecutingContent(Interpreter, const Arabica::DOM::Element<std::string>&);
%ignore uscxml::InterpreterMonitor::afterExecutingContent(Interpreter, const Arabica::DOM::Element<std::string>&);


%ignore uscxml::InterpreterOptions::fromCmdLine(int, char**);
%ignore uscxml::InterpreterOptions::additionalParameters;
%ignore uscxml::InterpreterOptions::interpreters;

// Invoker

%ignore uscxml::Invoker::Invoker(const boost::shared_ptr<InvokerImpl>);
%ignore uscxml::Invoker::setInterpreter(InterpreterImpl*);
%ignore uscxml::Invoker::getInterpreter;

%ignore uscxml::InvokerImpl::create(InterpreterImpl*);
%ignore uscxml::WrappedInvoker::create(InterpreterImpl*);
%ignore uscxml::InvokerImpl::setInterpreter(InterpreterImpl*);
%ignore uscxml::InvokerImpl::getInterpreter;


// DataModel

%ignore uscxml::DataModel::DataModel(const boost::shared_ptr<DataModelImpl>);
%ignore uscxml::DataModel::DataModel(const DataModel&);
%ignore uscxml::DataModel::eval(const Arabica::DOM::Element<std::string>&, const std::string&);
%ignore uscxml::DataModel::evalAsBool(const Arabica::DOM::Node<std::string>&, const std::string&);
%ignore uscxml::DataModel::evalAsBool(const std::string&);
%ignore uscxml::DataModel::throwErrorExecution(const std::string&);
%ignore uscxml::DataModel::throwErrorPlatform(const std::string&);
%ignore uscxml::DataModel::init(const Arabica::DOM::Element<std::string>&, const Arabica::DOM::Document<std::string>&, const std::string&);
%ignore uscxml::DataModel::init(const Arabica::DOM::Element<std::string>&, const Arabica::DOM::Node<std::string>&, const std::string&);
%ignore uscxml::DataModel::assign(const Arabica::DOM::Element<std::string>&, const Arabica::DOM::Document<std::string>&, const std::string&);
%ignore uscxml::DataModel::assign(const Arabica::DOM::Element<std::string>&, const Arabica::DOM::Node<std::string>&, const std::string&);
%ignore uscxml::DataModel::replaceExpressions(std::string&);
%ignore uscxml::DataModel::setInterpreter(InterpreterImpl*);
%ignore uscxml::DataModel::getInterpreter;

%ignore uscxml::DataModelImpl::create(InterpreterImpl*);
%ignore uscxml::DataModelImpl::throwErrorExecution(const std::string&);
%ignore uscxml::DataModelImpl::throwErrorPlatform(const std::string&);
%ignore uscxml::DataModelImpl::setInterpreter(InterpreterImpl*);
%ignore uscxml::DataModelImpl::getInterpreter;
%ignore uscxml::DataModelImpl::replaceExpressions(std::string&);
%ignore uscxml::DataModelImpl::init(const Arabica::DOM::Element<std::string>&, const Arabica::DOM::Document<std::string>&, const std::string&);
%ignore uscxml::DataModelImpl::init(const Arabica::DOM::Element<std::string>&, const Arabica::DOM::Node<std::string>&, const std::string&);
%ignore uscxml::DataModelImpl::init(const std::string&, const Data&);
%ignore uscxml::DataModelImpl::assign(const Arabica::DOM::Element<std::string>&, const Arabica::DOM::Document<std::string>&, const std::string&);
%ignore uscxml::DataModelImpl::assign(const Arabica::DOM::Element<std::string>&, const Arabica::DOM::Node<std::string>&, const std::string&);
%ignore uscxml::DataModelImpl::assign(const std::string&, const Data&);
%ignore uscxml::DataModelImpl::eval(const Arabica::DOM::Element<std::string>&, const std::string&);
%ignore uscxml::DataModelImpl::evalAsBool(const Arabica::DOM::Node<std::string>&, const std::string&);

%ignore uscxml::WrappedDataModel::create(InterpreterImpl*);
%ignore uscxml::WrappedDataModel::init(const Arabica::DOM::Element<std::string>&, const Arabica::DOM::Document<std::string>&, const std::string&);
%ignore uscxml::WrappedDataModel::init(const Arabica::DOM::Element<std::string>&, const Arabica::DOM::Node<std::string>&, const std::string&);
%ignore uscxml::WrappedDataModel::init(const std::string&, const Data&);
%ignore uscxml::WrappedDataModel::assign(const Arabica::DOM::Element<std::string>&, const Arabica::DOM::Document<std::string>&, const std::string&);
%ignore uscxml::WrappedDataModel::assign(const Arabica::DOM::Element<std::string>&, const Arabica::DOM::Node<std::string>&, const std::string&);
%ignore uscxml::WrappedDataModel::assign(const std::string&, const Data&);
%ignore uscxml::WrappedDataModel::eval(const Arabica::DOM::Element<std::string>&, const std::string&);
%ignore uscxml::WrappedDataModel::evalAsBool(const Arabica::DOM::Node<std::string>&, const std::string&);


// Executable Content

%ignore uscxml::ExecutableContent::ExecutableContent(const boost::shared_ptr<ExecutableContentImpl>);
%ignore uscxml::ExecutableContent::ExecutableContent(const ExecutableContent&);
%ignore uscxml::ExecutableContent::setInterpreter(InterpreterImpl*);
%ignore uscxml::ExecutableContent::getInterpreter;
%ignore uscxml::ExecutableContent::enterElement(const Arabica::DOM::Node<std::string>&);
%ignore uscxml::ExecutableContent::exitElement(const Arabica::DOM::Node<std::string>&);

%ignore uscxml::ExecutableContentImpl::create(InterpreterImpl*);
%ignore uscxml::ExecutableContentImpl::enterElement(const Arabica::DOM::Node<std::string>&);
%ignore uscxml::ExecutableContentImpl::exitElement(const Arabica::DOM::Node<std::string>&);
%ignore uscxml::ExecutableContentImpl::setInterpreter(InterpreterImpl*);
%ignore uscxml::ExecutableContentImpl::getInterpreter;

%ignore uscxml::WrappedExecutableContent::create(InterpreterImpl*);
%ignore uscxml::WrappedExecutableContent::enterElement(const Arabica::DOM::Node<std::string>&);
%ignore uscxml::WrappedExecutableContent::exitElement(const Arabica::DOM::Node<std::string>&);


// IOProcessor

%ignore uscxml::IOProcessorImpl::create(InterpreterImpl*);

%ignore uscxml::IOProcessor::IOProcessor(const boost::shared_ptr<IOProcessorImpl>);
%ignore uscxml::IOProcessor::IOProcessor(const IOProcessor&);

%ignore uscxml::WrappedIOProcessor::create(InterpreterImpl*);


// Factory

%ignore uscxml::Factory::createDataModel;
%ignore uscxml::Factory::createIOProcessor;
%ignore uscxml::Factory::createInvoker;
%ignore uscxml::Factory::createExecutableContent;
%ignore uscxml::Factory::getIOProcessors;

// Event

%ignore uscxml::Event::Event(const Arabica::DOM::Node<std::string>&);
%ignore uscxml::Event::getStrippedDOM;
%ignore uscxml::Event::getFirstDOMElement;
%ignore uscxml::Event::dom;
%ignore uscxml::Event::getDOM();
%ignore uscxml::Event::setDOM(const Arabica::DOM::Node<std::string>&);
%ignore uscxml::Event::setDOM(const Arabica::DOM::Document<std::string>&);
%ignore uscxml::Event::toDocument();
%ignore uscxml::Event::getParams();
%ignore uscxml::Event::getParam;
%ignore uscxml::Event::setParams;

%ignore uscxml::SendRequest::fromXML;
%ignore uscxml::InvokeRequest::fromXML;

// HTTPServer

%ignore uscxml::HTTPServer::wsSend;
%ignore uscxml::HTTPServer::wsBroadcast;
%ignore uscxml::HTTPServer::reply;


// Data

%ignore uscxml::Data::toDocument;
%ignore uscxml::Data::Data(const Arabica::DOM::Node<std::string>&);
%ignore uscxml::Data::Data(const char* data, size_t size, const std::string& mimeType, bool adopt);
%ignore uscxml::Data::Data(const char* data, size_t size, const std::string& mimeType);

// Blob

%ignore uscxml::Blob::Blob(size_t size);
%ignore uscxml::Blob::Blob(const char* data, size_t size, const std::string& mimeType, bool adopt);
%ignore uscxml::Blob::Blob(const boost::shared_ptr<BlobImpl>);


%ignore operator!=;
%ignore operator<;
%ignore operator=;
%ignore operator[];
%ignore operator std::list<Data>;
%ignore operator std::string;
%ignore operator std::map<std::string,Data>;
%ignore operator<<;

