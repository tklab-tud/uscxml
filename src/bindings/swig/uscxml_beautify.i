%rename(NativeDataModel) DataModel;
%rename(DataModel) WrappedDataModel;
%rename(NativeDataModelExtension) DataModelExtension;
%rename(DataModelExtension) WrappedDataModelExtension;
%rename(NativeExecutableContent) ExecutableContent;
%rename(ExecutableContent) WrappedExecutableContent;
%rename(NativeInvoker) Invoker;
%rename(Invoker) WrappedInvoker;
%rename(NativeIOProcessor) IOProcessor;
%rename(IOProcessor) WrappedIOProcessor;
%rename(NativeInterpreterMonitor) InterpreterMonitor;
%rename(InterpreterMonitor) WrappedInterpreterMonitor;

%rename(getInvokersNative) uscxml::Interpreter::getInvokers();
%rename(getIOProcessorsNative) uscxml::Interpreter::getIOProcessors();

%extend uscxml::Event {	
	std::map<std::string, std::list<uscxml::Data> > getParamMap() {
		std::map<std::string, std::list<uscxml::Data> > paramMap;
    std::multimap<std::string, Data>::const_iterator paramPairIter = self->getParams().begin();
		while(paramPairIter != self->getParams().end()) {
			paramMap[paramPairIter->first].push_back(paramPairIter->second);
			paramPairIter++;
		}
		return paramMap;
	}

	std::vector<std::string> getParamMapKeys() {
		std::vector<std::string> keys;
		for(std::multimap<std::string, Data>::const_iterator iter = self->getParams().begin(); 
				iter != self->getParams().end(); 
				iter = self->getParams().upper_bound(iter->first)) {
			keys.push_back(iter->first);
		}
		return keys;
	}
	
	void setParamMap(const std::map<std::string, std::list<uscxml::Data> >& paramMap) {
		std::multimap<std::string, Data> params;
		std::map<std::string, std::list<uscxml::Data> >::const_iterator mapIter = paramMap.begin();
		while(mapIter != paramMap.end()) {
			std::list<uscxml::Data>::const_iterator dataIter = mapIter->second.begin();
			while(dataIter != mapIter->second.end()) {
				params.insert(std::make_pair(mapIter->first, *dataIter));
				dataIter++;
			}
			mapIter++;
		}
		self->setParams(params);
	}
	
	std::vector<std::string> getNameListKeys() {
		std::vector<std::string> keys;
    std::map<std::string, Data>::const_iterator iter = self->getNameList().begin();
		while(iter != self->getNameList().end()) {
			keys.push_back(iter->first);
			iter++;
		}
		return keys;
	}
};

%extend uscxml::Interpreter {
	
	void addIOProcessor(uscxml::WrappedIOProcessor* ioProc) {
		self->addIOProcessor(boost::shared_ptr<IOProcessorImpl>(ioProc));
	}

	void setDataModel(uscxml::WrappedDataModel* dataModel) {
		self->setDataModel(boost::shared_ptr<DataModelImpl>(dataModel));
	}

	void setInvoker(const std::string invokeId, uscxml::WrappedInvoker* invoker) {
		self->setInvoker(invokeId, boost::shared_ptr<InvokerImpl>(invoker));
	}
	
	std::vector<std::string> getBasicConfiguration() {
		Arabica::XPath::NodeSet<std::string> nativeConfig = self->getBasicConfiguration();
		std::vector<std::string> config;
		for (int i = 0; i < nativeConfig.size(); i++) {
			Arabica::DOM::Element<std::string> elem(nativeConfig[i]);
			config.push_back(elem.getAttribute("id"));
		}
		return config;
	}

	std::vector<std::string> getConfiguration() {
		Arabica::XPath::NodeSet<std::string> nativeConfig = self->getConfiguration();
		std::vector<std::string> config;
		for (int i = 0; i < nativeConfig.size(); i++) {
			Arabica::DOM::Element<std::string> elem(nativeConfig[i]);
			config.push_back(elem.getAttribute("id"));
		}
		return config;
	}
		
	std::vector<std::string> getIOProcessorKeys() {
		std::vector<std::string> keys;
    std::map<std::string, IOProcessor>::const_iterator iter = self->getIOProcessors().begin();
		while(iter != self->getIOProcessors().end()) {
			keys.push_back(iter->first);
			iter++;
		}
		return keys;
	}

	std::vector<std::string> getInvokerKeys() {
		std::vector<std::string> keys;
    std::map<std::string, Invoker>::const_iterator iter = self->getInvokers().begin();
		while(iter != self->getInvokers().end()) {
			keys.push_back(iter->first);
			iter++;
		}
		return keys;
	}

};

%{
	#include <glog/logging.h>
%}

%extend uscxml::Data {
	std::vector<std::string> getCompoundKeys() {
		std::vector<std::string> keys;
    std::map<std::string, Data>::const_iterator iter = self->compound.begin();
		while(iter != self->compound.end()) {
			keys.push_back(iter->first);
			iter++;
		}
		return keys;
	}
	
	std::string getXML() {
		if (!self->node)
			return "";
			
		std::stringstream ss;
		ss << self->node;
		return ss.str();
	}
	
	void setXML(const std::string& xml) {
		NameSpacingParser parser = NameSpacingParser::fromXML(xml);
		if (!parser.errorsReported()) {
			self->node = parser.getDocument();
		} else {
			LOG(ERROR) << "Cannot parse message as XML: " << parser.errors();
		}
	}
};
