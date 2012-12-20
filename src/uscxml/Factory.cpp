#include "uscxml/Common.h"
#include "uscxml/config.h"

#include "uscxml/Factory.h"
#include "uscxml/Message.h"

#ifdef BUILD_AS_PLUGINS
# include "uscxml/plugins/Plugins.h"
#else

# include "uscxml/plugins/ioprocessor/basichttp/libevent/EventIOProcessor.h"
# include "uscxml/plugins/invoker/scxml/USCXMLInvoker.h"

# ifdef UMUNDO_FOUND
#   include "uscxml/plugins/invoker/umundo/UmundoInvoker.h"
# endif

# ifdef MILES_FOUND
#   include "uscxml/plugins/invoker/modality/miles/SpatialAudio.h"
# endif

# ifdef V8_FOUND
#   include "uscxml/plugins/datamodel/ecmascript/v8/V8DataModel.h"
# endif

# ifdef SWI_FOUND
#   include "uscxml/plugins/datamodel/prolog/swi/SWIDataModel.h"
# endif

#endif

namespace uscxml {

Factory::Factory() {
#ifdef BUILD_AS_PLUGINS
	if (pluginPath.length() == 0) {
		// try to read USCXML_PLUGIN_PATH environment variable
		pluginPath = (getenv("USCXML_PLUGIN_PATH") != NULL ? getenv("USCXML_PLUGIN_PATH") : "");
	}
	if (pluginPath.length() > 0) {
		pluma.acceptProviderType<InvokerProvider>();
		pluma.acceptProviderType<IOProcessorProvider>();
		pluma.acceptProviderType<DataModelProvider>();
		pluma.loadFromFolder(pluginPath);

		std::vector<InvokerProvider*> invokerProviders;
		pluma.getProviders(invokerProviders);
		for (std::vector<InvokerProvider*>::iterator it = invokerProviders.begin() ; it != invokerProviders.end() ; ++it) {
			Invoker* invoker = (*it)->create();
			registerInvoker(invoker);
		}

		std::vector<IOProcessorProvider*> ioProcessorProviders;
		pluma.getProviders(ioProcessorProviders);
		for (std::vector<IOProcessorProvider*>::iterator it = ioProcessorProviders.begin() ; it != ioProcessorProviders.end() ; ++it) {
			IOProcessor* ioProcessor = (*it)->create();
			registerIOProcessor(ioProcessor);
		}

		std::vector<DataModelProvider*> dataModelProviders;
		pluma.getProviders(dataModelProviders);
		for (std::vector<DataModelProvider*>::iterator it = dataModelProviders.begin() ; it != dataModelProviders.end() ; ++it) {
			DataModel* dataModel = (*it)->create();
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
		SpatialAudio* invoker = new SpatialAudio();
		registerInvoker(invoker);
	}
#endif

#ifdef V8_FOUND
	{
		V8DataModel* dataModel = new V8DataModel();
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
		USCXMLInvoker* invoker = new USCXMLInvoker();
		registerInvoker(invoker);
	}
	{
		EventIOProcessor* ioProcessor = new EventIOProcessor();
		registerIOProcessor(ioProcessor);
	}
#endif
}

Factory::~Factory() {
#ifdef BUILD_AS_PLUGINS
	pluma.unloadAll();
#endif
}

void Factory::registerIOProcessor(IOProcessor* ioProcessor) {
	std::set<std::string> names = ioProcessor->getNames();
	std::set<std::string>::iterator nameIter = names.begin();
	while(nameIter != names.end()) {
		_ioProcessors[*nameIter] = ioProcessor;
		nameIter++;
	}
}

void Factory::registerDataModel(DataModel* dataModel) {
	std::set<std::string> names = dataModel->getNames();
	std::set<std::string>::iterator nameIter = names.begin();
	while(nameIter != names.end()) {
		_dataModels[*nameIter] = dataModel;
		nameIter++;
	}
}

void Factory::registerInvoker(Invoker* invoker) {
	std::set<std::string> names = invoker->getNames();
	std::set<std::string>::iterator nameIter = names.begin();
	while(nameIter != names.end()) {
		_invokers[*nameIter] = invoker;
		nameIter++;
	}
}

void Factory::registerExecutableContent(const std::string tag, ExecutableContent* executableContent) {
	_executableContent[tag] = executableContent;
}

Invoker* Factory::getInvoker(const std::string type, Interpreter* interpreter) {
	Factory* factory = getInstance();
	if (factory->_invokers.find(type) != factory->_invokers.end()) {
		return (Invoker*)factory->_invokers[type]->create(interpreter);
	}
	return NULL;
}

DataModel* Factory::getDataModel(const std::string type, Interpreter* interpreter) {
	Factory* factory = getInstance();
	if (factory->_dataModels.find(type) != factory->_dataModels.end()) {
		return factory->_dataModels[type]->create(interpreter);
	}
	return NULL;
}

IOProcessor* Factory::getIOProcessor(const std::string type, Interpreter* interpreter) {
	Factory* factory = getInstance();
	if (factory->_ioProcessors.find(type) != factory->_ioProcessors.end()) {
		return factory->_ioProcessors[type]->create(interpreter);
	}
	return NULL;
}

ExecutableContent* Factory::getExecutableContent(const std::string tag, Interpreter* interpreter) {
	Factory* factory = getInstance();
	if (factory->_executableContent.find(tag) != factory->_executableContent.end()) {
		return factory->_executableContent[tag]->create(interpreter);
	}
	return NULL;
}

Factory* Factory::getInstance() {
	if (_instance == NULL) {
		_instance = new Factory();
	}
	return _instance;
}

Factory* Factory::_instance = NULL;
std::string Factory::pluginPath;
}