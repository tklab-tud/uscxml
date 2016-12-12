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

#ifndef FACTORY_H_5WKLGPRB
#define FACTORY_H_5WKLGPRB

#include "uscxml/Common.h"

#include "uscxml/plugins/ExecutableContent.h"
#include "uscxml/plugins/EventHandler.h"
#include "uscxml/plugins/IOProcessor.h"
#include "uscxml/plugins/Invoker.h"
#include "uscxml/plugins/DataModelImpl.h"

#include <string.h>

#ifdef BUILD_AS_PLUGINS
#include "Pluma/Pluma.hpp"
#endif

#include <memory>
#include <set>
#include <limits>

namespace uscxml {

class InterpreterImpl;

class USCXML_API Factory {
public:
	Factory(Factory* parentFactory);
	Factory(const std::string& pluginPath, Factory* parentFactory);

	void registerIOProcessor(IOProcessorImpl* ioProcessor);
	void registerDataModel(DataModelImpl* dataModel);
	void registerInvoker(InvokerImpl* invoker);
	void registerExecutableContent(ExecutableContentImpl* executableContent);

	std::shared_ptr<DataModelImpl> createDataModel(const std::string& type, DataModelCallbacks* callbacks);
	std::shared_ptr<IOProcessorImpl> createIOProcessor(const std::string& type, InterpreterImpl* interpreter);
	std::shared_ptr<InvokerImpl> createInvoker(const std::string& type, InterpreterImpl* interpreter);
	std::shared_ptr<ExecutableContentImpl> createExecutableContent(const std::string& localName, const std::string& nameSpace, InterpreterImpl* interpreter);

	bool hasDataModel(const std::string& type);
	bool hasIOProcessor(const std::string& type);
	bool hasInvoker(const std::string& type);
	bool hasExecutableContent(const std::string& localName, const std::string& nameSpace);

	std::map<std::string, IOProcessorImpl*> getIOProcessors();

	void listComponents();

	static Factory* getInstance();

	static void setDefaultPluginPath(const std::string& path);
	static std::string getDefaultPluginPath();

protected:
	std::map<std::string, DataModelImpl*> _dataModels;
	std::map<std::string, std::string> _dataModelAliases;
	std::map<std::string, IOProcessorImpl*> _ioProcessors;
	std::map<std::string, std::string> _ioProcessorAliases;
	std::map<std::string, InvokerImpl*> _invokers;
	std::map<std::string, std::string> _invokerAliases;
	std::map<std::pair<std::string, std::string>, ExecutableContentImpl*> _executableContent;

#ifdef BUILD_AS_PLUGINS
	pluma::Pluma pluma;
#endif

	void registerPlugins();

	Factory(const std::string&);
	~Factory();
	Factory* _parentFactory;
	std::string _pluginPath;
	static Factory* _instance;
	static std::string _defaultPluginPath;

};


}

#endif /* end of include guard: FACTORY_H_5WKLGPRB */
