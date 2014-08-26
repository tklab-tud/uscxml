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

#include "uscxml/Factory.h"
#include "uscxml/Message.h"
#include "uscxml/Interpreter.h"
#include <glog/logging.h>

#include "uscxml/server/InterpreterServlet.h"

#include "uscxml/plugins/datamodel/null/NULLDataModel.h"

// see http://nadeausoftware.com/articles/2012/01/c_c_tip_how_use_compiler_predefined_macros_detect_operating_system

#ifdef BUILD_AS_PLUGINS
# include "uscxml/plugins/Plugins.h"
#else

# include "uscxml/plugins/ioprocessor/basichttp/BasicHTTPIOProcessor.h"
# include "uscxml/plugins/ioprocessor/scxml/SCXMLIOProcessor.h"
# include "uscxml/plugins/invoker/scxml/USCXMLInvoker.h"

#	ifndef BUILD_MINIMAL
#		include "uscxml/plugins/invoker/imap/IMAPInvoker.h"
#		ifdef CURL_HAS_SMTP
#			include "uscxml/plugins/invoker/smtp/SMTPInvoker.h"
#		endif
#		include "uscxml/plugins/invoker/xhtml/XHTMLInvoker.h"
#		include "uscxml/plugins/invoker/filesystem/dirmon/DirMonInvoker.h"
#		include "uscxml/plugins/invoker/system/SystemInvoker.h"
#		include "uscxml/plugins/invoker/http/HTTPServletInvoker.h"
#		include "uscxml/plugins/invoker/heartbeat/HeartbeatInvoker.h"

#		include "uscxml/plugins/datamodel/xpath/XPathDataModel.h"
#		include "uscxml/plugins/datamodel/promela/PromelaDataModel.h"

#		include "uscxml/plugins/element/file/FileElement.h"
#		include "uscxml/plugins/element/fetch/FetchElement.h"
#		include "uscxml/plugins/element/respond/RespondElement.h"
#		include "uscxml/plugins/element/postpone/PostponeElement.h"

#		include "uscxml/plugins/ioprocessor/comet/CometIOProcessor.h"
#   include "uscxml/plugins/invoker/vxml/VoiceXMLInvoker.h"

#	endif


#ifdef PROTOBUF_FOUND
//# include "uscxml/plugins/ioprocessor/modality/MMIHTTPIOProcessor.h"
#endif

# if (defined UMUNDO_FOUND && defined PROTOBUF_FOUND)
#   include "uscxml/plugins/invoker/umundo/UmundoInvoker.h"
#endif

# ifdef OPENSCENEGRAPH_FOUND
#   include "uscxml/plugins/invoker/graphics/openscenegraph/OSGInvoker.h"
#   include "uscxml/plugins/invoker/graphics/openscenegraph/converter/OSGConverter.h"
# endif

# ifdef MILES_FOUND
#   include "uscxml/plugins/invoker/miles/MilesSessionInvoker.h"
//#   include "uscxml/plugins/invoker/miles/SpatialAudio.h"
# endif

# ifdef FFMPEG_FOUND
#   include "uscxml/plugins/invoker/ffmpeg/FFMPEGInvoker.h"
# endif

# ifdef LIBICAL_FOUND
#   include "uscxml/plugins/invoker/calendar/CalendarInvoker.h"
# endif

# ifdef LIBPURPLE_FOUND
#   include "uscxml/plugins/invoker/im/IMInvoker.h"
# endif

# if (defined EXPECT_FOUND && defined TCL_FOUND)
#   include "uscxml/plugins/invoker/expect/ExpectInvoker.h"
# endif

#ifdef OPENAL_FOUND
#   include "uscxml/plugins/invoker/audio/OpenALInvoker.h"
#endif

# ifdef CORELOCATION_FOUND
#   include "uscxml/plugins/invoker/location/CoreLocation/LocationInvoker.h"
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

# ifdef LUA_FOUND
#   include "uscxml/plugins/datamodel/lua/LuaDataModel.h"
# endif

# if 0
#		include "uscxml/plugins/element/mmi/MMIEvents.h"
# endif

#endif

#define ELEMENT_MMI_REGISTER(class)\
class##Element* class = new class##Element(); \
registerExecutableContent(class);


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

void Factory::registerPlugins() {
	{
		InterpreterHTTPServlet* ioProcessor = new InterpreterHTTPServlet();
		registerIOProcessor(ioProcessor);
	}
	{
		InterpreterWebSocketServlet* ioProcessor = new InterpreterWebSocketServlet();
		registerIOProcessor(ioProcessor);
	}
	{
		NULLDataModel* dataModel = new NULLDataModel();
		registerDataModel(dataModel);
	}

#ifdef BUILD_AS_PLUGINS
	// these are part of core

	if (_pluginPath.length() == 0) {
		// try to read USCXML_PLUGIN_PATH environment variable
		_pluginPath = (getenv("USCXML_PLUGIN_PATH") != NULL ? getenv("USCXML_PLUGIN_PATH") : "");
	}
	if (_pluginPath.length() > 0) {
		pluma.acceptProviderType<InvokerImplProvider>();
		pluma.acceptProviderType<IOProcessorImplProvider>();
		pluma.acceptProviderType<DataModelImplProvider>();
		pluma.acceptProviderType<ExecutableContentImplProvider>();
		pluma.loadFromFolder(_pluginPath);

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

		std::vector<ExecutableContentImplProvider*> execContentProviders;
		pluma.getProviders(execContentProviders);
		for (std::vector<ExecutableContentImplProvider*>::iterator it = execContentProviders.begin() ; it != execContentProviders.end() ; ++it) {
			ExecutableContentImpl* execContent = (*it)->create();
			registerExecutableContent(execContent);
		}

	} else {
		LOG(WARNING) << "No path to plugins known, export USCXML_PLUGIN_PATH or pass path as parameter";
	}
#else
	if (_pluginPath.length() > 0)
		LOG(WARNING) << "Plugin path is given, but uscxml is compiled without support";

#ifndef BUILD_MINIMAL

# if (defined UMUNDO_FOUND && defined PROTOBUF_FOUND)
	{
		UmundoInvoker* invoker = new UmundoInvoker();
		registerInvoker(invoker);
	}
#if 0
	{
		VoiceXMLInvoker* invoker = new VoiceXMLInvoker();
		registerInvoker(invoker);
	}
#endif
#endif

#ifdef MILES_FOUND
	{
		MilesSessionInvoker* invoker = new MilesSessionInvoker();
		registerInvoker(invoker);
	}
	// {
	//  SpatialAudio* invoker = new SpatialAudio();
	//  registerInvoker(invoker);
	// }
#endif

#ifdef FFMPEG_FOUND
	{
		FFMPEGInvoker* invoker = new FFMPEGInvoker();
		registerInvoker(invoker);
	}
#endif

#ifdef LIBICAL_FOUND
	{
		CalendarInvoker* invoker = new CalendarInvoker();
		registerInvoker(invoker);
	}
#endif

#ifdef LIBPURPLE_FOUND
	{
		IMInvoker* invoker = new IMInvoker();
		registerInvoker(invoker);
	}
#endif

#if (defined EXPECT_FOUND && defined TCL_FOUND)
	{
		ExpectInvoker* invoker = new ExpectInvoker();
		registerInvoker(invoker);
	}
#endif

#if (defined OPENAL_FOUND && (defined LIBSNDFILE_FOUND || defined AUDIOTOOLBOX_FOUND))
	{
		OpenALInvoker* invoker = new OpenALInvoker();
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

#if (defined V8_FOUND && defined BUILD_DM_ECMA)
	{
		V8DataModel* dataModel = new V8DataModel();
		registerDataModel(dataModel);
	}
#endif

#if (defined JSC_FOUND && defined BUILD_DM_ECMA)
	{
		JSCDataModel* dataModel = new JSCDataModel();
		registerDataModel(dataModel);
	}
#endif

#if (defined SWI_FOUND && defined BUILD_DM_PROLOG)
	{
		SWIDataModel* dataModel = new SWIDataModel();
		registerDataModel(dataModel);
	}
#endif

#if (defined LUA_FOUND && defined BUILD_DM_LUA)
	{
		LuaDataModel* dataModel = new LuaDataModel();
		registerDataModel(dataModel);
	}
#endif

#if (defined BUILD_DM_PROMELA)
	{
		PromelaDataModel* dataModel = new PromelaDataModel();
		registerDataModel(dataModel);
	}
#endif

#ifdef BUILD_DM_XPATH
	{
		XPathDataModel* dataModel = new XPathDataModel();
		registerDataModel(dataModel);
	}
#endif

#ifdef PROTOBUF_FOUND
	{
		// MMIHTTPIOProcessor* ioProcessor = new MMIHTTPIOProcessor();
		// registerIOProcessor(ioProcessor);
	}
#endif

#ifdef CURL_HAS_SMTP
	{
		SMTPInvoker* invoker = new SMTPInvoker();
		registerInvoker(invoker);
	}
#endif


	// these are always available when not building minimal
	{
		XHTMLInvoker* invoker = new XHTMLInvoker();
		registerInvoker(invoker);
	}
	{
		IMAPInvoker* invoker = new IMAPInvoker();
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
		VoiceXMLInvoker* invoker = new VoiceXMLInvoker();
		registerInvoker(invoker);
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
	{
		FileElement* element = new FileElement();
		registerExecutableContent(element);
	}

#endif

	{
		USCXMLInvoker* invoker = new USCXMLInvoker();
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

#endif
}

Factory::~Factory() {
#ifdef BUILD_AS_PLUGINS
	pluma.unloadAll();
#endif
}

#define LIST_COMPONENTS(type, name) \
std::map<std::string, type*>::iterator iter = name.begin(); \
while(iter != name.end()) { \
	std::list<std::string> names = iter->second->getNames(); \
	std::list<std::string>::iterator nameIter = names.begin(); \
	if (nameIter != names.end()) { \
		std::cout << "\t" << *nameIter; \
		nameIter++; \
		std::string seperator = ""; \
		if (nameIter != names.end()) { \
			std::cout << "\t("; \
			while(nameIter != names.end()) { \
				std::cout << seperator << *nameIter; \
				seperator = ", "; \
				nameIter++; \
			} \
			std::cout << ")"; \
		} \
		std::cout << std::endl; \
	} \
	iter++; \
}


void Factory::listComponents() {
	{
		std::cout << "Available Datamodels:" << std::endl;
		LIST_COMPONENTS(DataModelImpl, _dataModels);
		std::cout << std::endl;
	}
	{
		std::cout << "Available Invokers:" << std::endl;
		LIST_COMPONENTS(InvokerImpl, _invokers);
		std::cout << std::endl;
	}
	{
		std::cout << "Available I/O Processors:" << std::endl;
		LIST_COMPONENTS(IOProcessorImpl, _ioProcessors);
		std::cout << std::endl;
	}
	{
		std::cout << "Available Elements:" << std::endl;
		std::map<std::pair<std::string, std::string>, ExecutableContentImpl*>::iterator iter = _executableContent.begin();
		while(iter != _executableContent.end()) {
			std::cout << "\t" << iter->second->getNamespace() << " / " << iter->second->getLocalName() << std::endl;
			iter++;
		}
		std::cout << std::endl;
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
	
boost::shared_ptr<InvokerImpl> Factory::createInvoker(const std::string& type, InterpreterImpl* interpreter) {

	// do we have this type ourself?
	if (_invokerAliases.find(type) != _invokerAliases.end()) {
		std::string canonicalName = _invokerAliases[type];
		if (_invokers.find(canonicalName) != _invokers.end()) {
			boost::shared_ptr<InvokerImpl> invoker = _invokers[canonicalName]->create(interpreter);
			invoker->setInterpreter(interpreter);
			return invoker;
		}
	}

	// lookup in parent factory
	if (_parentFactory) {
		return _parentFactory->createInvoker(type, interpreter);
	} else {
		ERROR_EXECUTION_THROW("No Invoker named '" + type + "' known");
	}

	return boost::shared_ptr<InvokerImpl>();
}


bool Factory::hasDataModel(const std::string& type) {
	if (_dataModelAliases.find(type) != _dataModelAliases.end()) {
		return true;
	} else if(_parentFactory) {
		return _parentFactory->hasDataModel(type);
	}
	return false;
}

boost::shared_ptr<DataModelImpl> Factory::createDataModel(const std::string& type, InterpreterImpl* interpreter) {

	// do we have this type ourself?
	if (_dataModelAliases.find(type) != _dataModelAliases.end()) {
		std::string canonicalName = _dataModelAliases[type];
		if (_dataModels.find(canonicalName) != _dataModels.end()) {
			boost::shared_ptr<DataModelImpl> dataModel = _dataModels[canonicalName]->create(interpreter);
			dataModel->setInterpreter(interpreter);
			return dataModel;
		}
	}

	// lookup in parent factory
	if (_parentFactory) {
		return _parentFactory->createDataModel(type, interpreter);
	} else {
		ERROR_EXECUTION_THROW("No Datamodel name '" + type + "' known");
	}

	return boost::shared_ptr<DataModelImpl>();
}

	
bool Factory::hasIOProcessor(const std::string& type) {
	if (_ioProcessorAliases.find(type) != _ioProcessorAliases.end()) {
		return true;
	} else if(_parentFactory) {
		return _parentFactory->hasIOProcessor(type);
	}
	return false;
}

boost::shared_ptr<IOProcessorImpl> Factory::createIOProcessor(const std::string& type, InterpreterImpl* interpreter) {
	// do we have this type ourself?
	if (_ioProcessorAliases.find(type) != _ioProcessorAliases.end()) {
		std::string canonicalName = _ioProcessorAliases[type];
		if (_ioProcessors.find(canonicalName) != _ioProcessors.end()) {
			boost::shared_ptr<IOProcessorImpl> ioProc = _ioProcessors[canonicalName]->create(interpreter);
			ioProc->setInterpreter(interpreter);
			return ioProc;
		}
	}

	// lookup in parent factory
	if (_parentFactory) {
		return _parentFactory->createIOProcessor(type, interpreter);
	} else {
		ERROR_EXECUTION_THROW("No IOProcessor named '" + type + "' known");
	}

	return boost::shared_ptr<IOProcessorImpl>();
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

boost::shared_ptr<ExecutableContentImpl> Factory::createExecutableContent(const std::string& localName, const std::string& nameSpace, InterpreterImpl* interpreter) {
	// do we have this type in this factory?
	std::string actualNameSpace = (nameSpace.length() == 0 ? "http://www.w3.org/2005/07/scxml" : nameSpace);
	if (_executableContent.find(std::make_pair(localName, actualNameSpace)) != _executableContent.end()) {
		boost::shared_ptr<ExecutableContentImpl> execContent = _executableContent[std::make_pair(localName, actualNameSpace)]->create(interpreter);
		execContent->setInterpreter(interpreter);
		return execContent;
	}

	// lookup in parent factory
	if (_parentFactory) {
		return _parentFactory->createExecutableContent(localName, nameSpace, interpreter);
	} else {
		ERROR_EXECUTION_THROW("No Executable content name '" + localName + "' in namespace '" + actualNameSpace + "' known");
	}

	return boost::shared_ptr<ExecutableContentImpl>();

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
					Data data = getStringAsData(expr);
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
	if (_instance == NULL) {
		_instance = new Factory(Factory::_defaultPluginPath);
	}
	return _instance;
}

void EventHandlerImpl::returnErrorExecution(const std::string& cause) {
	ERROR_EXECUTION(exc, cause);
	returnEvent(exc);
}

void EventHandlerImpl::returnErrorCommunication(const std::string& cause) {
	ERROR_COMMUNICATION(exc, cause);
	returnEvent(exc);
}

void EventHandlerImpl::returnEvent(Event& event, bool internal) {
	if (event.invokeid.length() == 0)
		event.invokeid = _invokeId;
	if (event.eventType == 0)
		event.eventType = (internal ? Event::INTERNAL : Event::EXTERNAL);
	if (event.origin.length() == 0)
		event.origin = "#_" + _invokeId;
	if (event.origintype.length() == 0)
		event.origintype = _type;

	if (internal) {
		_interpreter->receiveInternal(event);
	} else {
		_interpreter->receive(event);
	}
}

Factory* Factory::_instance = NULL;
std::string Factory::_defaultPluginPath;
}