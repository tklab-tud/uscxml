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

#ifndef SMTPINVOKER_H_W09J90F0
#define SMTPINVOKER_H_W09J90F0

#include <uscxml/Interpreter.h>

#ifdef BUILD_AS_PLUGINS
#include "uscxml/plugins/Plugins.h"
#endif

#include <curl/curl.h>

namespace uscxml {

class SMTPInvoker : public InvokerImpl {
public:
	SMTPInvoker();
	virtual ~SMTPInvoker();
	virtual boost::shared_ptr<InvokerImpl> create(InterpreterImpl* interpreter);

	virtual std::set<std::string> getNames() {
		std::set<std::string> names;
		names.insert("smtp");
		names.insert("http://uscxml.tk.informatik.tu-darmstadt.de/#smtp");
		return names;
	}

	virtual Data getDataModelVariables();
	virtual void send(const SendRequest& req);
	virtual void cancel(const std::string sendId);
	virtual void invoke(const InvokeRequest& req);

protected:

	class SMTPContext {
	public:
		SMTPContext() : readPtr(0) {}
		std::string content;
		size_t readPtr;
		SMTPInvoker* invoker;
	};

	CURL* _curl;
	std::string _username;
	std::string _password;
	std::string _server;

	std::list<std::string> getAtoms(std::list<Data> list);
	void getAttachments(std::list<Data> list, std::list<Data>& attachments);
	static size_t writeCurlData(void *ptr, size_t size, size_t nmemb, void *userdata);
};

#ifdef BUILD_AS_PLUGINS
PLUMA_INHERIT_PROVIDER(SMTPInvoker, InvokerImpl);
#endif

}


#endif /* end of include guard: SMTPINVOKER_H_W09J90F0 */
