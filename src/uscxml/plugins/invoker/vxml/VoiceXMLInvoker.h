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

#ifndef VOICEXMLINVOKER_H_W09J90F0
#define VOICEXMLINVOKER_H_W09J90F0

#include <uscxml/Interpreter.h>
#include <uscxml/plugins/ioprocessor/modality/MMIMessages.h>
#include <uscxml/plugins/ioprocessor/modality/MMIProtoBridge.h>

#include <umundo/core.h>
#include <umundo/s11n.h>

#ifdef BUILD_AS_PLUGINS
#include "uscxml/plugins/Plugins.h"
#endif

namespace uscxml {

class VoiceXMLInvoker : public InvokerImpl, public umundo::TypedReceiver {
public:
	VoiceXMLInvoker();
	virtual ~VoiceXMLInvoker();
	virtual boost::shared_ptr<InvokerImpl> create(InterpreterImpl* interpreter);

	virtual std::set<std::string> getNames() {
		std::set<std::string> names;
		names.insert("vxml");
		names.insert("voicexml");
		names.insert("http://www.w3.org/TR/voicexml21/");
		return names;
	}

	virtual void receive(void* object, umundo::Message* msg);

	virtual Data getDataModelVariables();
	virtual void send(const SendRequest& req);
	virtual void invoke(const InvokeRequest& req);


protected:
	umundo::Node _node;
	umundo::TypedPublisher _pub;
	umundo::TypedSubscriber _sub;
};

#ifdef BUILD_AS_PLUGINS
PLUMA_INHERIT_PROVIDER(VoiceXMLInvoker, InvokerImpl);
#endif

}


#endif /* end of include guard: VOICEXMLINVOKER_H_W09J90F0 */
