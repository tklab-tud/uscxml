%extend uscxml::Event {
	std::vector<std::pair<std::string, Data> > getParamPairs() {
		std::vector<std::pair<std::string, Data> > pairs;
    std::multimap<std::string, Data>::iterator paramPairIter = self->getParams().begin();
		while(paramPairIter != self->getParams().end()) {
			pairs.push_back(*paramPairIter);
			paramPairIter++;
		}
		return pairs;
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
	std::vector<std::string> getCompundKeys() {
		std::vector<std::string> keys;
    std::map<std::string, Data>::const_iterator iter = self->compound.begin();
		while(iter != self->compound.end()) {
			keys.push_back(iter->first);
			iter++;
		}
		return keys;
	}
};
