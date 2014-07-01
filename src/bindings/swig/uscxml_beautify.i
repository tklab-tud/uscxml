%rename(NativeDataModel) DataModel;
%rename(DataModel) WrappedDataModel;
%rename(NativeExecutableContent) ExecutableContent;
%rename(ExecutableContent) WrappedExecutableContent;
%rename(NativeInvoker) Invoker;
%rename(Invoker) WrappedInvoker;
%rename(NativeIOProcessor) IOProcessor;
%rename(IOProcessor) WrappedIOProcessor;
%rename(NativeInterpreterMonitor) InterpreterMonitor;
%rename(InterpreterMonitor) WrappedInterpreterMonitor;

%extend uscxml::Event {	
/*		std::vector<std::pair<std::string, uscxml::Data> > getParamPairs() {
			std::vector<std::pair<std::string, Data> > pairs;
	    std::multimap<std::string, Data>::iterator paramPairIter = self->getParams().begin();
			while(paramPairIter != self->getParams().end()) {
				pairs.push_back(*paramPairIter);
				paramPairIter++;
			}
			return pairs;
		}

		void setParamPairs(const std::vector<std::pair<std::string, uscxml::Data> >& pairs) {
			std::multimap<std::string, Data> params;
			std::vector<std::pair<std::string, Data> >::const_iterator pairIter = pairs.begin();
			while(pairIter != pairs.end()) {
				params.insert(std::make_pair(pairIter->first, pairIter->second));
				pairIter++;
			}
			self->setParams(params);
		}
*/
	
	std::string toString() {
		std::stringstream ss;
		ss << *self;
		return ss.str();
	}
	
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

%extend uscxml::Data {
	std::string toString() {
		std::stringstream ss;
		ss << *self;
		return ss.str();
	}
	
	std::vector<std::string> getCompoundKeys() {
		std::vector<std::string> keys;
    std::map<std::string, Data>::const_iterator iter = self->compound.begin();
		while(iter != self->compound.end()) {
			keys.push_back(iter->first);
			iter++;
		}
		return keys;
	}
};

%extend uscxml::SendRequest {
	std::string toString() {
		std::stringstream ss;
		ss << *self;
		return ss.str();
	}
};

%extend uscxml::InvokeRequest {
	std::string toString() {
		std::stringstream ss;
		ss << *self;
		return ss.str();
	}
};