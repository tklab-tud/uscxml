#include "uscxml/Common.h"
#include "uscxml/config.h"

#include "uscxml/Factory.h"
#include "uscxml/datamodel/ecmascript/v8/V8DataModel.h"
#include "uscxml/ioprocessor/basichttp/libevent/EventIOProcessor.h"
#include "uscxml/invoker/scxml/USCXMLInvoker.h"

#ifdef UMUNDO_FOUND
#include "uscxml/invoker/umundo/UmundoInvoker.h"
#endif

#ifdef MILES_FOUND
#include "uscxml/invoker/modality/miles/SpatialAudio.h"
#endif

namespace uscxml {

  Factory::Factory() {
    _dataModels["ecmascript"] = new V8DataModel();

    // use basichttp for transporting to/from scxml sessions as well
    _ioProcessors["basichttp"] = new EventIOProcessor();
    _ioProcessors["http://www.w3.org/TR/scxml/#SCXMLEventProcessor"] = _ioProcessors["basichttp"];

    _invoker["scxml"] = new USCXMLInvoker();
    _invoker["http://www.w3.org/TR/scxml/"] = _invoker["scxml"];

#ifdef UMUNDO_FOUND
    _invoker["umundo"] = new UmundoInvoker();
    _invoker["http://umundo.tk.informatik.tu-darmstadt.de/"] = _invoker["umundo"];
#endif

#ifdef MILES_FOUND
		_invoker["spatial-audio"] = new SpatialAudio();
		_invoker["audio"] = _invoker["spatial-audio"];
		_invoker["http://www.smartvortex.eu/mmi/spatial-audio/"] = _invoker["spatial-audio"];
#endif
  }
  
  void Factory::registerIOProcessor(const std::string type, IOProcessor* ioProcessor) {
    getInstance()->_ioProcessors[type] = ioProcessor;
  }
  
  void Factory::registerDataModel(const std::string type, DataModel* dataModel) {
    getInstance()->_dataModels[type] = dataModel;
  }
  
  void Factory::registerExecutableContent(const std::string tag, ExecutableContent* executableContent) {
    getInstance()->_executableContent[tag] = executableContent;
  }
  
  void Factory::registerInvoker(const std::string type, Invoker* invoker) {
    getInstance()->_invoker[type] = invoker;
  }

  Invoker* Factory::getInvoker(const std::string type, Interpreter* interpreter) {
    if (Factory::getInstance()->_invoker.find(type) != getInstance()->_invoker.end()) {
      return (Invoker*)getInstance()->_invoker[type]->create(interpreter);
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