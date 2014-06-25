%ignore uscxml::NumAttr;
%ignore uscxml::SCXMLParser;
%ignore uscxml::InterpreterImpl;

%ignore create();

%ignore uscxml::Interpreter::getDelayQueue();
%ignore uscxml::Interpreter::fromDOM;
%ignore uscxml::Interpreter::fromClone;
%ignore uscxml::Interpreter::start();
%ignore uscxml::Interpreter::stop();
%ignore uscxml::Interpreter::setCmdLineOptions(std::map<std::string, std::string>);
%ignore uscxml::Interpreter::getDocument;
%ignore uscxml::Interpreter::getImpl;
%ignore uscxml::Interpreter::runOnMainThread;
%ignore uscxml::Interpreter::getHTTPServlet();
%ignore uscxml::Interpreter::getNodeSetForXPath(const std::string&);
%ignore uscxml::Interpreter::isLegalConfiguration(const Arabica::XPath::NodeSet<std::string>&);
%ignore uscxml::Interpreter::getInstances();

%ignore uscxml::WrappedInvoker::create(InterpreterImpl*);

%ignore uscxml::WrappedDataModel::create(InterpreterImpl*);
%ignore uscxml::WrappedDataModel::init(const Arabica::DOM::Element<std::string>&, const Arabica::DOM::Document<std::string>&, const std::string&);
%ignore uscxml::WrappedDataModel::init(const Arabica::DOM::Element<std::string>&, const Arabica::DOM::Node<std::string>&, const std::string&);
%ignore uscxml::WrappedDataModel::init(const std::string&, const Data&);
%ignore uscxml::WrappedDataModel::assign(const Arabica::DOM::Element<std::string>&, const Arabica::DOM::Document<std::string>&, const std::string&);
%ignore uscxml::WrappedDataModel::assign(const Arabica::DOM::Element<std::string>&, const Arabica::DOM::Node<std::string>&, const std::string&);
%ignore uscxml::WrappedDataModel::assign(const std::string&, const Data&);
%ignore uscxml::WrappedDataModel::eval(const Arabica::DOM::Element<std::string>&, const std::string&);
%ignore uscxml::WrappedDataModel::evalAsBool(const Arabica::DOM::Node<std::string>&, const std::string&);

%ignore uscxml::WrappedExecutableContent::create(InterpreterImpl*);
%ignore uscxml::WrappedExecutableContent::enterElement(const Arabica::DOM::Node<std::string>&);
%ignore uscxml::WrappedExecutableContent::exitElement(const Arabica::DOM::Node<std::string>&);

%ignore uscxml::WrappedIOProcessor::create(InterpreterImpl*);

%ignore uscxml::Event::Event(const Arabica::DOM::Node<std::string>&);
%ignore uscxml::Event::getStrippedDOM;
%ignore uscxml::Event::getFirstDOMElement;
%ignore uscxml::Event::getDOM();
%ignore uscxml::Event::setDOM(const Arabica::DOM::Document<std::string>&);
%ignore uscxml::Event::toDocument();

%ignore operator!=;
%ignore operator<;
%ignore operator=;
%ignore operator[];
%ignore operator std::list<Data>;
%ignore operator std::string;
%ignore operator std::map<std::string,Data>;
%ignore operator<<;

