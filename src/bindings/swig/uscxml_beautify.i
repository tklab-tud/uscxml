%rename(NativeActionLanguage) ActionLanguage;
%rename(ActionLanguage) WrappedActionLanguage;
%rename(NativeDataModel) DataModel;
%rename(DataModel) WrappedDataModel;
//%rename(NativeDataModelExtension) DataModelExtension;
//%rename(DataModelExtension) WrappedDataModelExtension;
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

%extend uscxml::ErrorEvent {	
	std::string toString() {
		std::stringstream ss;
		ss << *self;
		return ss.str();
	}
};

%extend uscxml::Interpreter {
		
	std::vector<std::string> getConfiguration() {
		std::list<XERCESC_NS::DOMElement*> nativeConfig = self->getConfiguration();
		std::vector<std::string> config;
		for (auto state : nativeConfig) {
			if (HAS_ATTR(state, "id"))
				config.push_back(ATTR(state, "id"));
		}
		return config;
	}
		
};

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
	
};
