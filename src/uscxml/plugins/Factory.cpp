/**
 *  @file
 *  @author     2012-2013 Stefan Radomski (stefan.radomski@cs.tu-darmstadt.de)
 *  @copyright  Simplified BSD
 *
 *  @cond
 *  This program is free software: you can redistribute it and/or modify
 *  it under the terms of the FreeBSD license as published by the FreeBSD
 *  project.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 *
 *  You should have received a copy of the FreeBSD license along with this
 *  program. If not, see <http://www.opensource.org/licenses/bsd-license>.
 *  @endcond
 */

#include "uscxml/config.h"

#include "uscxml/plugins/Factory.h"
#include "uscxml/messages/Data.h"
#include "uscxml/Interpreter.h"
#include "uscxml/interpreter/Logging.h"

#include "uscxml/plugins/ExecutableContent.h"
#include "uscxml/plugins/ExecutableContentImpl.h"
#include "uscxml/plugins/EventHandler.h"
#include "uscxml/plugins/IOProcessor.h"
#include "uscxml/plugins/IOProcessorImpl.h"
#include "uscxml/plugins/Invoker.h"
#include "uscxml/plugins/InvokerImpl.h"
#include "uscxml/plugins/DataModelImpl.h"

#ifndef FEATS_ON_CMD
#include "uscxml/interpreter/LargeMicroStep.h"
#include "uscxml/interpreter/FastMicroStep.h"
#endif

#undef WITH_DM_ECMA_V8

#if 0
#include <xercesc/dom/DOM.hpp>
#include <xercesc/util/PlatformUtils.hpp>
#include "uscxml/util/DOM.h"
#endif

// see http://nadeausoftware.com/articles/2012/01/c_c_tip_how_use_compiler_predefined_macros_detect_operating_system


/*** BEGIN PLUGINS ***/

#ifdef BUILD_AS_PLUGINS
# include "uscxml/plugins/Plugins.h"
#else

#ifdef WITH_IOPROC_SCXML
#   include "uscxml/plugins/ioprocessor/scxml/SCXMLIOProcessor.h"
#endif

#ifdef WITH_IOPROC_BASICHTTP
#   include "uscxml/plugins/ioprocessor/basichttp/BasicHTTPIOProcessor.h"
#endif

#ifdef WITH_IOPROC_HTTP
#   include "uscxml/plugins/ioprocessor/http/HTTPIOProcessor.h"
#endif

#ifdef WITH_ELEMENT_RESPOND
#   include "uscxml/plugins/element/respond/RespondElement.h"
#endif

#include "uscxml/plugins/datamodel/null/NullDataModel.h"

#if defined WITH_DM_ECMA_V8
#   if (V8_VERSION == 032317)
#       include "uscxml/plugins/datamodel/ecmascript/v8/032317/V8DataModel.h"
#   endif
#   if (V8_VERSION == 031405)
#       include "uscxml/plugins/datamodel/ecmascript/v8/031405/V8DataModel.h"
#   endif

#elif defined(WITH_DM_ECMA_JSC)
#   include "uscxml/plugins/datamodel/ecmascript/JavaScriptCore/JSCDataModel.h"
#endif

#ifdef WITH_DM_LUA
#   include "uscxml/plugins/datamodel/lua/LuaDataModel.h"
#endif

#ifdef WITH_DM_C89
#   include "uscxml/plugins/datamodel/c89/C89DataModel.h"
#endif

#ifdef WITH_DM_PROMELA
#   include "uscxml/plugins/datamodel/promela/PromelaDataModel.h"
#endif


#ifdef WITH_INV_SCXML
#   include "uscxml/plugins/invoker/scxml/USCXMLInvoker.h"
#endif

#ifdef WITH_INV_DIRMON
#   include "uscxml/plugins/invoker/dirmon/DirMonInvoker.h"
#endif

#endif
/*** END PLUGINS ***/


namespace uscxml {

Factory::Factory(Factory* parentFactory) : _parentFactory(parentFactory) {
}

Factory::Factory(const std::string& pluginPath, Factory* parentFactory) : _parentFactory(parentFactory), _pluginPath(pluginPath) {
	registerPlugins();
}

Factory::Factory(const std::string& pluginPath) : _parentFactory(NULL), _pluginPath(pluginPath) {
	registerPlugins();
}

void Factory::setDefaultPluginPath(const std::string& path) {
	_defaultPluginPath = path;
}
std::string Factory::getDefaultPluginPath() {
	return _defaultPluginPath;
}

Factory::~Factory() {
#ifdef BUILD_AS_PLUGINS
	pluma.unloadAll();
#endif
}

void Factory::registerPlugins() {

#ifndef FEATS_ON_CMD
	registerMicrostepper(new LargeMicroStep());
	registerMicrostepper(new FastMicroStep());
#endif

	/*** PLUGINS ***/
#ifdef BUILD_AS_PLUGINS

	if (_pluginPath.length() == 0) {
		// try to read USCXML_PLUGIN_PATH environment variable
		_pluginPath = (getenv("USCXML_PLUGIN_PATH") != NULL ? getenv("USCXML_PLUGIN_PATH") : "");
	}
	if (_pluginPath.length() > 0) {
		pluma.acceptProviderType<InvokerImplProvider>();
		pluma.acceptProviderType<IOProcessorImplProvider>();
		pluma.acceptProviderType<DataModelImplProvider>();
		pluma.acceptProviderType<ExecutableContentImplProvider>();
		pluma.loadFromFolder(_pluginPath, true);

		std::vector<InvokerImplProvider*> invokerProviders;
		pluma.getProviders(invokerProviders);
		for (auto provider : invokerProviders) {
			InvokerImpl* invoker = provider->create();
			registerInvoker(invoker);
		}

		std::vector<IOProcessorImplProvider*> ioProcessorProviders;
		pluma.getProviders(ioProcessorProviders);
		for (auto provider : ioProcessorProviders) {
			IOProcessorImpl* ioProcessor = provider->create();
			registerIOProcessor(ioProcessor);
		}

		std::vector<DataModelImplProvider*> dataModelProviders;
		pluma.getProviders(dataModelProviders);
		for (auto provider : dataModelProviders) {
			DataModelImpl* dataModel = provider->create();
			registerDataModel(dataModel);
		}

		std::vector<ExecutableContentImplProvider*> execContentProviders;
		pluma.getProviders(execContentProviders);
		for (auto provider : execContentProviders) {
			ExecutableContentImpl* execContent = provider->create();
			registerExecutableContent(execContent);
		}

	} else {
		ERROR_EXECUTION_THROW("No path to plugins known, export USCXML_PLUGIN_PATH or pass path as parameter");
	}

#else

#ifdef WITH_IOPROC_SCXML
	{
		SCXMLIOProcessor* ioProcessor = new SCXMLIOProcessor();
		registerIOProcessor(ioProcessor);
	}
#endif

#ifdef WITH_IOPROC_BASICHTTP
	{
		BasicHTTPIOProcessor* ioProcessor = new BasicHTTPIOProcessor();
		registerIOProcessor(ioProcessor);
	}
#endif

#ifdef WITH_IOPROC_HTTP
	{
		HTTPIOProcessor* ioProcessor = new HTTPIOProcessor();
		registerIOProcessor(ioProcessor);
	}
#endif

#ifdef WITH_ELEMENT_RESPOND
	{
		RespondElement* element = new RespondElement();
		registerExecutableContent(element);
	}

#endif

#ifdef WITH_DM_ECMA_V8
	{
		V8DataModel* dataModel = new V8DataModel();
		registerDataModel(dataModel);
	}

#elif defined(WITH_DM_ECMA_JSC)
	{
		JSCDataModel* dataModel = new JSCDataModel();
		registerDataModel(dataModel);
	}
#endif


#ifdef WITH_DM_LUA
	{
		LuaDataModel* dataModel = new LuaDataModel();
		registerDataModel(dataModel);
	}
#endif

#ifdef WITH_DM_C89
	{
		C89DataModel* dataModel = new C89DataModel();
		registerDataModel(dataModel);
	}
#endif

#ifdef WITH_DM_PROMELA
	{
		PromelaDataModel* dataModel = new PromelaDataModel();
		registerDataModel(dataModel);
	}
#endif

	{
		NullDataModel* dataModel = new NullDataModel();
		registerDataModel(dataModel);
	}

#ifdef WITH_INV_SCXML
	{
		USCXMLInvoker* invoker = new USCXMLInvoker();
		registerInvoker(invoker);
	}
#endif

#ifdef WITH_INV_DIRMON
	{
		DirMonInvoker* inv = new DirMonInvoker();
		registerInvoker(inv);
	}
#endif

#endif
	/*** PLUGINS ***/

}

#define LIST_COMPONENTS(type, name) \
std::map<std::string, type*>::iterator iter = name.begin(); \
while(iter != name.end()) { \
	std::list<std::string> names = iter->second->getNames(); \
	std::list<std::string>::iterator nameIter = names.begin(); \
	if (nameIter != names.end()) { \
		LOGD(USCXML_VERBATIM) << "\t" << *nameIter; \
		nameIter++; \
		std::string seperator = ""; \
		if (nameIter != names.end()) { \
			LOGD(USCXML_VERBATIM) << "\t("; \
			while(nameIter != names.end()) { \
				LOGD(USCXML_VERBATIM) << seperator << *nameIter; \
				seperator = ", "; \
				nameIter++; \
			} \
			LOGD(USCXML_VERBATIM) << ")"; \
		} \
		LOGD(USCXML_VERBATIM) << "\n"; \
	} \
	iter++; \
}


void Factory::listComponents() {
	{
		LOGD(USCXML_VERBATIM) << "Available Datamodels:" << std::endl;
		LIST_COMPONENTS(DataModelImpl, _dataModels);
		LOGD(USCXML_VERBATIM) << "\n";
	}
	{
		LOGD(USCXML_VERBATIM) << "Available Invokers:" << std::endl;
		LIST_COMPONENTS(InvokerImpl, _invokers);
		LOGD(USCXML_VERBATIM) << "\n";
	}
	{
		LOGD(USCXML_VERBATIM) << "Available I/O Processors:" << std::endl;
		LIST_COMPONENTS(IOProcessorImpl, _ioProcessors);
		LOGD(USCXML_VERBATIM) << "\n";
	}
	{
		LOGD(USCXML_VERBATIM) << "Available Elements:" << std::endl;
		std::map<std::pair<std::string, std::string>, ExecutableContentImpl*>::iterator iter = _executableContent.begin();
		while(iter != _executableContent.end()) {
			LOGD(USCXML_VERBATIM) << "\t" << iter->second->getNamespace() << " / " << iter->second->getLocalName() << std::endl;
			iter++;
		}
		LOGD(USCXML_VERBATIM) << "\n";
	}
}

void Factory::registerIOProcessor(IOProcessorImpl* ioProcessor) {
	std::list<std::string> names = ioProcessor->getNames();
	std::list<std::string>::iterator nameIter = names.begin();
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
	std::list<std::string> names = dataModel->getNames();
	std::list<std::string>::iterator nameIter = names.begin();
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
	std::list<std::string> names = invoker->getNames();
	std::list<std::string>::iterator nameIter = names.begin();
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

std::map<std::string, IOProcessorImpl*> Factory::getIOProcessors() {
	std::map<std::string, IOProcessorImpl*> ioProcs;
	if (_parentFactory) {
		ioProcs = _parentFactory->getIOProcessors();
	}

	std::map<std::string, IOProcessorImpl*>::iterator ioProcIter = _ioProcessors.begin();
	while(ioProcIter != _ioProcessors.end()) {
		ioProcs.insert(std::make_pair(ioProcIter->first, ioProcIter->second));
		ioProcIter++;
	}

	return ioProcs;
}

bool Factory::hasInvoker(const std::string& type) {
	if (_invokerAliases.find(type) != _invokerAliases.end()) {
		return true;
	} else if(_parentFactory) {
		return _parentFactory->hasInvoker(type);
	}
	return false;
}

std::shared_ptr<InvokerImpl> Factory::createInvoker(const std::string& type, InvokerCallbacks* callbacks) {

	// do we have this type ourself?
	if (_invokerAliases.find(type) != _invokerAliases.end()) {
		std::string canonicalName = _invokerAliases[type];
		if (_invokers.find(canonicalName) != _invokers.end()) {
			std::shared_ptr<InvokerImpl> invoker = _invokers[canonicalName]->create(callbacks);
			return invoker;
		}
	}

	// lookup in parent factory
	if (_parentFactory) {
		return _parentFactory->createInvoker(type, callbacks);
	} else {
		ERROR_EXECUTION_THROW("No Invoker named '" + type + "' known");
	}

	return std::shared_ptr<InvokerImpl>();
}


bool Factory::hasDataModel(const std::string& type) {
	if (_dataModelAliases.find(type) != _dataModelAliases.end()) {
		return true;
	} else if(_parentFactory) {
		return _parentFactory->hasDataModel(type);
	}
	return false;
}

std::shared_ptr<DataModelImpl> Factory::createDataModel(const std::string& type, DataModelCallbacks* callbacks) {

	// do we have this type ourself?
	if (_dataModelAliases.find(type) != _dataModelAliases.end()) {
		std::string canonicalName = _dataModelAliases[type];
		if (_dataModels.find(canonicalName) != _dataModels.end()) {
			std::shared_ptr<DataModelImpl> dataModel = _dataModels[canonicalName]->create(callbacks);
			return dataModel;
		}
	}

	// lookup in parent factory
	if (_parentFactory) {
		return _parentFactory->createDataModel(type, callbacks);
	} else {
		ERROR_EXECUTION_THROW("No Datamodel name '" + type + "' known");
	}

	return std::shared_ptr<DataModelImpl>();
}

bool Factory::hasIOProcessor(const std::string& type) {
	if (_ioProcessorAliases.find(type) != _ioProcessorAliases.end()) {
		return true;
	} else if(_parentFactory) {
		return _parentFactory->hasIOProcessor(type);
	}
	return false;
}

std::shared_ptr<IOProcessorImpl> Factory::createIOProcessor(const std::string& type, IOProcessorCallbacks* callbacks) {
	// do we have this type ourself?
	if (_ioProcessorAliases.find(type) != _ioProcessorAliases.end()) {
		std::string canonicalName = _ioProcessorAliases[type];
		if (_ioProcessors.find(canonicalName) != _ioProcessors.end()) {
			std::shared_ptr<IOProcessorImpl> ioProc = _ioProcessors[canonicalName]->create(callbacks);
//			ioProc->setInterpreter(interpreter);
			return ioProc;
		}
	}

	// lookup in parent factory
	if (_parentFactory) {
		return _parentFactory->createIOProcessor(type, callbacks);
	} else {
		ERROR_EXECUTION_THROW("No IOProcessor named '" + type + "' known");
	}

	return std::shared_ptr<IOProcessorImpl>();
}

bool Factory::hasExecutableContent(const std::string& localName, const std::string& nameSpace) {
	std::string actualNameSpace = (nameSpace.length() == 0 ? "http://www.w3.org/2005/07/scxml" : nameSpace);
	if (_executableContent.find(std::make_pair(localName, actualNameSpace)) != _executableContent.end()) {
		return true;
	} else if(_parentFactory) {
		return _parentFactory->hasExecutableContent(localName, nameSpace);
	}
	return false;
}

std::shared_ptr<ExecutableContentImpl> Factory::createExecutableContent(const std::string& localName, const std::string& nameSpace, InterpreterImpl* interpreter) {
	// do we have this type in this factory?
	std::string actualNameSpace = (nameSpace.length() == 0 ? "http://www.w3.org/2005/07/scxml" : nameSpace);
	if (_executableContent.find(std::make_pair(localName, actualNameSpace)) != _executableContent.end()) {
		std::shared_ptr<ExecutableContentImpl> execContent = _executableContent[std::make_pair(localName, actualNameSpace)]->create(interpreter);
		return execContent;
	}

	// lookup in parent factory
	if (_parentFactory) {
		return _parentFactory->createExecutableContent(localName, nameSpace, interpreter);
	} else {
		ERROR_EXECUTION_THROW("No Executable content name '" + localName + "' in namespace '" + actualNameSpace + "' known");
	}

	return std::shared_ptr<ExecutableContentImpl>();

}

#ifndef FEATS_ON_CMD

bool Factory::hasMicroStepper(const std::string& name) {
	if (_microSteppers.find(name) != _microSteppers.end()) {
		return true;
	} else if(_parentFactory) {
		return _parentFactory->hasMicroStepper(name);
	}
	return false;
}


void Factory::registerMicrostepper(MicroStepImpl* microStepper) {
	_microSteppers[microStepper->getName()] = microStepper;
}

std::shared_ptr<MicroStepImpl> Factory::createMicroStepper(const std::string& name, MicroStepCallbacks* callbacks) {
	if (_microSteppers.find(name) != _microSteppers.end()) {
		std::shared_ptr<MicroStepImpl> microStepper = _microSteppers[name]->create(callbacks);
		return microStepper;
	}

	if (_parentFactory) {
		return _parentFactory->createMicroStepper(name, callbacks);
	} else {
		ERROR_EXECUTION_THROW("No Microstepper '" + name + "' known");
	}

	return std::shared_ptr<MicroStepImpl>();

}
#endif

void DataModelImpl::addExtension(DataModelExtension* ext) {
	ERROR_EXECUTION_THROW("DataModel does not support extensions");
}

size_t DataModelImpl::replaceExpressions(std::string& content) {
	std::stringstream ss;
	size_t replacements = 0;
	size_t indent = 0;
	size_t pos = 0;
	size_t start = std::string::npos;
	size_t end = 0;
	while (true) {
		// find any of ${}
		pos = content.find_first_of("${}", pos);
		if (pos == std::string::npos) {
			ss << content.substr(end, content.length() - end);
			break;
		}
		if (content[pos] == '$') {
			if (content.size() > pos && content[pos+1] == '{') {
				pos++;
				start = pos + 1;
				// copy everything in between
				ss << content.substr(end, (start - 2) - end);
			}
		} else if (content[pos] == '{' && start != std::string::npos) {
			indent++;
		} else if (content[pos] == '}' && start != std::string::npos) {
			if (!indent) {
				end = pos;
				// we found a token to substitute
				std::string expr = content.substr(start, end - start);
				end++;
				try {
					Data data = getAsData(expr);
//					if (data.type == Data::VERBATIM) {
//						ss << "\"" << data.atom << "\"";
//					} else {
//						ss << data.atom;
//					}
					if (data.atom.length() > 0) {
						ss << data.atom;
					} else {
						ss << Data::toJSON(data);
					}
					replacements++;
				} catch (Event e) {
					// insert unsubstituted
					start -= 2;
					ss << content.substr(start, end - start);
				}
				start = std::string::npos;
			} else {
				indent--;
			}
		}
		pos++;
	}
	if (replacements)
		content = ss.str();

	return replacements;
}


Factory* Factory::getInstance() {
#if 0
	// this needs to be here as some plugins use xercesc, now in X::X in DOM.h
	try {
		::XERCESC_NS::XMLPlatformUtils::Initialize();
	} catch (const XERCESC_NS::XMLException& toCatch) {
		ERROR_PLATFORM_THROW("Cannot initialize XercesC: " + X(toCatch.getMessage()).str());
	}
#endif
	if (_instance == NULL) {
		_instance = new Factory(Factory::_defaultPluginPath);
	}
	return _instance;
}

//void EventHandlerImpl::returnErrorExecution(const std::string& cause) {
//	ERROR_EXECUTION(exc, cause);
//	returnEvent(exc);
//}
//
//void EventHandlerImpl::returnErrorCommunication(const std::string& cause) {
//	ERROR_COMMUNICATION(exc, cause);
//	returnEvent(exc);
//}

void IOProcessorImpl::eventToSCXML(Event& event,
                                   const std::string& type,
                                   const std::string& origin,
                                   bool internal) {
	if (event.eventType == 0)
		event.eventType = (internal ? Event::INTERNAL : Event::EXTERNAL);
	if (event.origin.length() == 0 && origin.length() > 0)
		event.origin = origin;
	if (event.origintype.length() == 0)
		event.origintype = type;

	if (internal) {
		_callbacks->enqueueInternal(event);
	} else {
		_callbacks->enqueueExternal(event);
	}
}

void InvokerImpl::eventToSCXML(Event& event,
                               const std::string& type,
                               const std::string& invokeId,
                               bool internal) {
	if (event.invokeid.length() == 0)
		event.invokeid = invokeId;
	if (event.eventType == 0)
		event.eventType = (internal ? Event::INTERNAL : Event::EXTERNAL);
	if (event.origin.length() == 0 && invokeId.length() > 0)
		event.origin = "#_" + invokeId;
	if (event.origintype.length() == 0)
		event.origintype = type;

	if (internal) {
		_callbacks->enqueueInternal(event);
	} else {
		_callbacks->enqueueExternal(event);
	}
}

std::string Factory::_defaultPluginPath;
Factory* Factory::_instance = NULL;
}
