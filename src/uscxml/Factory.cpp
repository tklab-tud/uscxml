#include "uscxml/Common.h"
#include "uscxml/config.h"

#include "uscxml/Factory.h"
#include "uscxml/Message.h"
#include "uscxml/Interpreter.h"
#include <glog/logging.h>

#ifdef BUILD_AS_PLUGINS
# include "uscxml/plugins/Plugins.h"
#else

# include "uscxml/plugins/ioprocessor/basichttp/BasicHTTPIOProcessor.h"
# include "uscxml/plugins/ioprocessor/scxml/SCXMLIOProcessor.h"
# include "uscxml/plugins/invoker/scxml/USCXMLInvoker.h"
# include "uscxml/plugins/invoker/http/HTTPServletInvoker.h"
# include "uscxml/plugins/invoker/heartbeat/HeartbeatInvoker.h"
# include "uscxml/plugins/invoker/filesystem/dirmon/DirMonInvoker.h"
# include "uscxml/plugins/invoker/system/SystemInvoker.h"

# ifdef UMUNDO_FOUND
#   include "uscxml/plugins/invoker/umundo/UmundoInvoker.h"
# endif

# ifdef OPENSCENEGRAPH_FOUND
#   include "uscxml/plugins/invoker/graphics/openscenegraph/OSGInvoker.h"
#   include "uscxml/plugins/invoker/graphics/openscenegraph/converter/OSGConverter.h"
# endif

# ifdef MILES_FOUND
#   include "uscxml/plugins/invoker/miles/MilesSessionInvoker.h"
# endif

# ifdef FFMPEG_FOUND
#   include "uscxml/plugins/invoker/ffmpeg/FFMPEGInvoker.h"
# endif

# ifdef V8_FOUND
#   include "uscxml/plugins/datamodel/ecmascript/v8/V8DataModel.h"
# endif

# ifdef JSC_FOUND
#   include "uscxml/plugins/datamodel/ecmascript/JavaScriptCore/JSCDataModel.h"
# endif

# ifdef SWI_FOUND
#   include "uscxml/plugins/datamodel/prolog/swi/SWIDataModel.h"
# endif

#include "uscxml/plugins/datamodel/null/NULLDataModel.h"
#include "uscxml/plugins/datamodel/xpath/XPathDataModel.h"


# include "uscxml/plugins/element/fetch/FetchElement.h"
# include "uscxml/plugins/element/respond/RespondElement.h"
# include "uscxml/plugins/element/postpone/PostponeElement.h"


#endif

namespace uscxml {

Factory::Factory() {
#ifdef BUILD_AS_PLUGINS
	if (pluginPath.length() == 0) {
		// try to read USCXML_PLUGIN_PATH environment variable
		pluginPath = (getenv("USCXML_PLUGIN_PATH") != NULL ? getenv("USCXML_PLUGIN_PATH") : "");
	}
	if (pluginPath.length() > 0) {
		pluma.acceptProviderType<InvokerImplProvider>();
		pluma.acceptProviderType<IOProcessorImplProvider>();
		pluma.acceptProviderType<DataModelImplProvider>();
		pluma.acceptProviderType<ExecutableContentImplProvider>();
		pluma.loadFromFolder(pluginPath);

		std::vector<InvokerImplProvider*> invokerProviders;
		pluma.getProviders(invokerProviders);
		for (std::vector<InvokerImplProvider*>::iterator it = invokerProviders.begin() ; it != invokerProviders.end() ; ++it) {
			InvokerImpl* invoker = (*it)->create();
			registerInvoker(invoker);
		}

		std::vector<IOProcessorImplProvider*> ioProcessorProviders;
		pluma.getProviders(ioProcessorProviders);
		for (std::vector<IOProcessorImplProvider*>::iterator it = ioProcessorProviders.begin() ; it != ioProcessorProviders.end() ; ++it) {
			IOProcessorImpl* ioProcessor = (*it)->create();
			registerIOProcessor(ioProcessor);
		}

		std::vector<DataModelImplProvider*> dataModelProviders;
		pluma.getProviders(dataModelProviders);
		for (std::vector<DataModelImplProvider*>::iterator it = dataModelProviders.begin() ; it != dataModelProviders.end() ; ++it) {
			DataModelImpl* dataModel = (*it)->create();
			registerDataModel(dataModel);
		}
	}
#else
#ifdef UMUNDO_FOUND
	{
		UmundoInvoker* invoker = new UmundoInvoker();
		registerInvoker(invoker);
	}
#endif

#ifdef MILES_FOUND
	{
//		MilesSessionInvoker* invoker = new MilesSessionInvoker();
//		registerInvoker(invoker);
	}
#endif

#ifdef FFMPEG_FOUND
	{
		FFMPEGInvoker* invoker = new FFMPEGInvoker();
		registerInvoker(invoker);
	}
#endif

#ifdef OPENSCENEGRAPH_FOUND
	{
		OSGInvoker* invoker = new OSGInvoker();
		registerInvoker(invoker);
	}
	{
		OSGConverter* invoker = new OSGConverter();
		registerInvoker(invoker);
	}
#endif

#ifdef V8_FOUND
	{
		V8DataModel* dataModel = new V8DataModel();
		registerDataModel(dataModel);
	}
#endif

#ifdef JSC_FOUND
	{
		JSCDataModel* dataModel = new JSCDataModel();
		registerDataModel(dataModel);
	}
#endif

#ifdef SWI_FOUND
	{
		SWIDataModel* dataModel = new SWIDataModel();
		registerDataModel(dataModel);
	}
#endif

	// these are always available
	{
		NULLDataModel* dataModel = new NULLDataModel();
		registerDataModel(dataModel);
	}
	{
		XPathDataModel* dataModel = new XPathDataModel();
		registerDataModel(dataModel);
	}
	{
		USCXMLInvoker* invoker = new USCXMLInvoker();
		registerInvoker(invoker);
	}
	{
		HTTPServletInvoker* invoker = new HTTPServletInvoker();
		registerInvoker(invoker);
	}
	{
		HeartbeatInvoker* invoker = new HeartbeatInvoker();
		registerInvoker(invoker);
	}
	{
		DirMonInvoker* invoker = new DirMonInvoker();
		registerInvoker(invoker);
	}
	{
		SystemInvoker* invoker = new SystemInvoker();
		registerInvoker(invoker);
	}
	{
		BasicHTTPIOProcessor* ioProcessor = new BasicHTTPIOProcessor();
		registerIOProcessor(ioProcessor);
	}
	{
		SCXMLIOProcessor* ioProcessor = new SCXMLIOProcessor();
		registerIOProcessor(ioProcessor);
	}
	{
		InterpreterServlet* ioProcessor = new InterpreterServlet();
		registerIOProcessor(ioProcessor);
	}
	{
		FetchElement* element = new FetchElement();
		registerExecutableContent(element);
	}
	{
		RespondElement* element = new RespondElement();
		registerExecutableContent(element);
	}
	{
		PostponeElement* element = new PostponeElement();
		registerExecutableContent(element);
	}

#endif
}

Factory::~Factory() {
#ifdef BUILD_AS_PLUGINS
	pluma.unloadAll();
#endif
}

void Factory::registerIOProcessor(IOProcessorImpl* ioProcessor) {
	std::set<std::string> names = ioProcessor->getNames();
	std::set<std::string>::iterator nameIter = names.begin();
	if (nameIter != names.end()) {
		std::string canonicalName = *nameIter;
		_ioProcessors[canonicalName] = ioProcessor;
		while(nameIter != names.end()) {
			_ioProcessorAliases[*nameIter] = canonicalName;
			nameIter++;
		}
	}
}

void Factory::registerDataModel(DataModelImpl* dataModel) {
	std::set<std::string> names = dataModel->getNames();
	std::set<std::string>::iterator nameIter = names.begin();
	if (nameIter != names.end()) {
		std::string canonicalName = *nameIter;
		_dataModels[canonicalName] = dataModel;
		while(nameIter != names.end()) {
			_dataModelAliases[*nameIter] = canonicalName;
			nameIter++;
		}
	}
}

void Factory::registerInvoker(InvokerImpl* invoker) {
	std::set<std::string> names = invoker->getNames();
	std::set<std::string>::iterator nameIter = names.begin();
	if (nameIter != names.end()) {
		std::string canonicalName = *nameIter;
		_invokers[canonicalName] = invoker;
		while(nameIter != names.end()) {
			_invokerAliases[*nameIter] = canonicalName;
			nameIter++;
		}
	}
}

void Factory::registerExecutableContent(ExecutableContentImpl* executableContent) {
	std::string localName = executableContent->getLocalName();
	std::string nameSpace = executableContent->getNamespace();
	_executableContent[std::make_pair(localName, nameSpace)] = executableContent;
}


boost::shared_ptr<InvokerImpl> Factory::createInvoker(const std::string& type, InterpreterImpl* interpreter) {
	Factory* factory = getInstance();
	if (factory->_invokerAliases.find(type) == factory->_invokerAliases.end()) {
		LOG(ERROR) << "No " << type << " Invoker known";
		return boost::shared_ptr<InvokerImpl>();
	}

	std::string canonicalName = factory->_invokerAliases[type];
	if (factory->_invokers.find(canonicalName) == factory->_invokers.end()) {
		LOG(ERROR) << "Invoker " << type << " known as " << canonicalName << " but no prototype is available in factory";
		return boost::shared_ptr<InvokerImpl>();
	}

	return boost::static_pointer_cast<InvokerImpl>(factory->_invokers[canonicalName]->create(interpreter));
}

boost::shared_ptr<DataModelImpl> Factory::createDataModel(const std::string& type, InterpreterImpl* interpreter) {
	Factory* factory = getInstance();
	if (factory->_dataModelAliases.find(type) == factory->_dataModelAliases.end()) {
		LOG(ERROR) << "No " << type << " DataModel known";
		return boost::shared_ptr<DataModelImpl>();
	}

	std::string canonicalName = factory->_dataModelAliases[type];
	if (factory->_dataModels.find(canonicalName) == factory->_dataModels.end()) {
		LOG(ERROR) << "DataModel " << type << " known as " << canonicalName << " but no prototype is available in factory";
		return boost::shared_ptr<DataModelImpl>();
	}

	return factory->_dataModels[canonicalName]->create(interpreter);
}

boost::shared_ptr<IOProcessorImpl> Factory::createIOProcessor(const std::string& type, InterpreterImpl* interpreter) {
	Factory* factory = getInstance();
	if (factory->_ioProcessorAliases.find(type) == factory->_ioProcessorAliases.end()) {
		LOG(ERROR) << "No " << type << " IOProcessor known";
		return boost::shared_ptr<IOProcessorImpl>();
	}

	std::string canonicalName = factory->_ioProcessorAliases[type];
	if (factory->_ioProcessors.find(canonicalName) == factory->_ioProcessors.end()) {
		LOG(ERROR) << "IOProcessor " << type << " known as " << canonicalName << " but no prototype is available in factory";
		return boost::shared_ptr<IOProcessorImpl>();
	}

	return factory->_ioProcessors[canonicalName]->create(interpreter);
}

boost::shared_ptr<ExecutableContentImpl> Factory::createExecutableContent(const std::string& localName, const std::string& nameSpace, InterpreterImpl* interpreter) {
	Factory* factory = getInstance();
	std::string actualNameSpace = (nameSpace.length() == 0 ? "http://www.w3.org/2005/07/scxml" : nameSpace);
	if (factory->_executableContent.find(std::make_pair(localName, actualNameSpace)) == factory->_executableContent.end()) {
		LOG(ERROR) << "Executable content " << localName << " in " << actualNameSpace << " not available in factory";
		return boost::shared_ptr<ExecutableContentImpl>();
	}
	return factory->_executableContent[std::make_pair(localName, actualNameSpace)]->create(interpreter);
}


Factory* Factory::getInstance() {
	if (_instance == NULL) {
		_instance = new Factory();
	}
	return _instance;
}

void IOProcessorImpl::returnEvent(Event& event) {
	if (event.invokeid.length() == 0)
		event.invokeid = _invokeId;
	if (event.type == 0)
		event.type = Event::EXTERNAL;
	if (event.origin.length() == 0)
		event.origin = "#_" + _invokeId;
	if (event.origintype.length() == 0)
		event.origintype = _type;

	_interpreter->receive(event);
}

Factory* Factory::_instance = NULL;
std::string Factory::pluginPath;
}