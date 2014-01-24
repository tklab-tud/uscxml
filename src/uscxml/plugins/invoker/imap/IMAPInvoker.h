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

#ifndef IMAPINVOKER_H_W09JFED0
#define IMAPINVOKER_H_W09JFED0

#include <uscxml/Interpreter.h>
#include <uscxml/concurrency/BlockingQueue.h>

#ifdef BUILD_AS_PLUGINS
#include "uscxml/plugins/Plugins.h"
#endif

#include <curl/curl.h>

namespace uscxml {

class IMAPInvoker : public InvokerImpl {
public:
	IMAPInvoker();
	virtual ~IMAPInvoker();
	virtual boost::shared_ptr<InvokerImpl> create(InterpreterImpl* interpreter);

	virtual std::set<std::string> getNames() {
		std::set<std::string> names;
		names.insert("imap");
		names.insert("http://uscxml.tk.informatik.tu-darmstadt.de/#imap");
		return names;
	}

	virtual Data getDataModelVariables();
	virtual void send(const SendRequest& req);
	virtual void cancel(const std::string sendId);
	virtual void invoke(const InvokeRequest& req);

protected:

	class IMAPContext {
		
	public:
		enum Cmd {
			// valid in authenticated state
			SELECT,
			EXAMINE,
			CREATE,
			DELETE,
			RENAME,
			SUBSCRIBE,
			UNSUBSCRIBE,
			LIST,
			LSUB,
			STATUS,
			APPEND,
			// valid in selected state
			CHECK,
			CLOSE,
			EXPUNGE,
			SEARCH,
			FETCH,
			STORE,
			COPY,
			UID,
			XEXTENSION,
		};

		struct MailboxOp {
			std::string mailbox;
		};
		
		struct Select : MailboxOp {};
		struct Examine : MailboxOp {};
		struct Create : MailboxOp {};
		struct Delete : MailboxOp {};
		struct Rename : MailboxOp {
			std::string newName;
		};
		struct Subscribe : MailboxOp {};
		struct Unsubscribe : MailboxOp {};
		struct List : MailboxOp {
			std::string refName;
		};
		struct LSub : List {};
		struct Status : MailboxOp {
			std::string dataItems;
		};
		struct Append : MailboxOp {
			std::string flags;
			std::string dateTime;
			std::string literal;
		};
		struct Check {};
		struct Close {};
		struct Expunge {};
		struct Search {
			std::string charSet;
			std::string criteria;
		};
		struct Fetch {
			std::string sequence;
			std::string itemNames;
		};
		struct Store : Fetch {
			std::string values;
		};
		struct Copy : MailboxOp {
			std::string sequence;
		};
		struct UId {
			std::string command;
			std::string arguments;
		};
		struct XExtension : UId {};

		
		IMAPContext() : readPtr(0) {}

		void* arguments;
		Cmd command;
		
		IMAPInvoker* invoker;
		SendRequest sendReq;
		std::stringstream inContent;
		std::string outContent;
		size_t readPtr;
		bool verbose;
		bool useSSL;

	};

protected:
	std::string _username;
	std::string _password;
	std::string _server;

	static void run(void*);
	
	tthread::thread* _thread;
	uscxml::concurrency::BlockingQueue<IMAPContext*> _workQueue;
	bool _isRunning;

	void process(IMAPContext* ctx);
	static size_t writeCurlData(void *ptr, size_t size, size_t nmemb, void *userdata);
	static size_t readCurlData(void *ptr, size_t size, size_t nmemb, void *userdata);

//	Data parseListReponse(const std::string& response);
};

#ifdef BUILD_AS_PLUGINS
PLUMA_INHERIT_PROVIDER(IMAPInvoker, InvokerImpl);
#endif

}


#endif /* end of include guard: IMAPINVOKER_H_W09JFED0 */
