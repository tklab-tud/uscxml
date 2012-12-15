#include "uscxml/Common.h"
#include "uscxml/config.h"

#include "uscxml/Factory.h"
#include "uscxml/plugins/ioprocessor/basichttp/libevent/EventIOProcessor.h"
#include "uscxml/plugins/invoker/scxml/USCXMLInvoker.h"

#ifdef UMUNDO_FOUND
#include "uscxml/plugins/invoker/umundo/UmundoInvoker.h"
#endif

#ifdef MILES_FOUND
#include "uscxml/plugins/invoker/modality/miles/SpatialAudio.h"
#endif

#ifdef V8_FOUND
#include "uscxml/plugins/datamodel/ecmascript/v8/V8DataModel.h"
#endif

namespace uscxml {

  Factory::Factory() {
#ifdef BUILD_AS_PLUGINS
		pluma.acceptProviderType<InvokerProvider>();
		pluma.acceptProviderType<IOProcessorProvider>();
		pluma.acceptProviderType<DataModelProvider>();
		pluma.loadFromFolder("/Users/sradomski/Documents/TK/Code/uscxml/build/xcode/lib");

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
    
    pluma.unloadAll();

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
    if (Factory::getInstance()->_invokers.find(type) != getInstance()->_invokers.end()) {
      return (Invoker*)getInstance()->_invokers[type]->create(interpreter);
    }
    return NULL;
  }

  DataModel* Factory::getDataModel(const std::string type, Interpreter* interpreter) {
    if (Factory::getInstance()->_dataModels.find(type) != getInstance()->_dataModels.end()) {
      return getInstance()->_dataModels[type]->create(interpreter);
    }
    return NULL;
  }
  
  IOProcessor* Factory::getIOProcessor(const std::string type, Interpreter* interpreter) {
    if (getInstance()->_ioProcessors.find(type) != getInstance()->_ioProcessors.end()) {
      return getInstance()->_ioProcessors[type]->create(interpreter);
    }
    return NULL;
  }
  
  ExecutableContent* Factory::getExecutableContent(const std::string tag, Interpreter* interpreter) {
    if (getInstance()->_executableContent.find(tag) != getInstance()->_executableContent.end()) {
      return getInstance()->_executableContent[tag]->create(interpreter);
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

}