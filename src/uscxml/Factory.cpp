#include "uscxml/Factory.h"
#include "uscxml/datamodel/ecmascript/v8/V8DataModel.h"
//#include "uscxml/ioprocessor/basichttp/pion/PionIOProcessor.h"
#include "uscxml/ioprocessor/basichttp/libevent/EventIOProcessor.h"

namespace uscxml {

  Factory::Factory() {
    _dataModels["ecmascript"] = new V8DataModel();
//    _ioProcessors["basichttp"] = new PionIOProcessor();
    _ioProcessors["basichttp"] = new io::libevent::EventIOProcessor();
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