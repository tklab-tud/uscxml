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

#define NOMINMAX // and have MSVC die in a fire for defining min macro
#include "IMAPInvoker.h"
#include <glog/logging.h>

#ifdef BUILD_AS_PLUGINS
#include <Pluma/Connector.hpp>
#endif

#include <boost/algorithm/string.hpp>
#include "uscxml/UUID.h"

namespace uscxml {

#ifdef BUILD_AS_PLUGINS
PLUMA_CONNECTOR
bool pluginConnect(pluma::Host& host) {
	host.add( new IMAPInvokerProvider() );
	return true;
}
#endif

IMAPInvoker::IMAPInvoker() {
}

IMAPInvoker::~IMAPInvoker() {
};

boost::shared_ptr<InvokerImpl> IMAPInvoker::create(InterpreterImpl* interpreter) {
	boost::shared_ptr<IMAPInvoker> invoker = boost::shared_ptr<IMAPInvoker>(new IMAPInvoker());
	return invoker;
}

Data IMAPInvoker::getDataModelVariables() {
	Data data;
	return data;
}

void IMAPInvoker::run(void* instance) {
	IMAPInvoker* INSTANCE = (IMAPInvoker*)instance;
	while(true) {
		IMAPContext* req = INSTANCE->_workQueue.pop();
		if (INSTANCE->_isRunning) {
			INSTANCE->process(req);
		} else {
			return;
		}
	}
}

size_t IMAPInvoker::writeCurlData(void *ptr, size_t size, size_t nmemb, void *userdata) {
	if (!userdata)
		return 0;

	IMAPContext* ctx = (IMAPContext*)userdata;

	size_t toWrite = (std::min)(ctx->outContent.length() - ctx->readPtr, size * nmemb);
	if (toWrite > 0) {
		memcpy (ptr, ctx->outContent.c_str() + ctx->readPtr, toWrite);
		ctx->readPtr += toWrite;
	}

	return toWrite;
}

size_t IMAPInvoker::readCurlData(void *ptr, size_t size, size_t nmemb, void *userdata) {
	if (!userdata)
		return 0;

	IMAPContext* ctx = (IMAPContext*)userdata;
	ctx->inContent << std::string((char*)ptr, size * nmemb);

	return size * nmemb;
}


void IMAPInvoker::send(const SendRequest& req) {
	IMAPContext* ctx = NULL;

	if (false) {
	} else if (iequals(req.name, "select")) {
		IMAPContext::Select* args = new IMAPContext::Select();
		Event::getParam(req.params, "mailbox", args->mailbox);

		ctx = new IMAPContext();
		ctx->command = IMAPContext::IMAP_SELECT;
		ctx->arguments = args;

	} else if (iequals(req.name, "examine")) {
		IMAPContext::Examine* args = new IMAPContext::Examine();
		Event::getParam(req.params, "mailbox", args->mailbox);

		ctx = new IMAPContext();
		ctx->command = IMAPContext::IMAP_EXAMINE;
		ctx->arguments = args;

	} else if (iequals(req.name, "delete")) {
		IMAPContext::Delete* args = new IMAPContext::Delete();
		Event::getParam(req.params, "mailbox", args->mailbox);

		ctx = new IMAPContext();
		ctx->command = IMAPContext::IMAP_DELETE;
		ctx->arguments = args;

	} else if (iequals(req.name, "rename")) {
		IMAPContext::Rename* args = new IMAPContext::Rename();
		Event::getParam(req.params, "mailbox", args->mailbox);
		Event::getParam(req.params, "name", args->newName);

		ctx = new IMAPContext();
		ctx->command = IMAPContext::IMAP_RENAME;
		ctx->arguments = args;

	} else if (iequals(req.name, "subscribe")) {
		IMAPContext::Subscribe* args = new IMAPContext::Subscribe();
		Event::getParam(req.params, "mailbox", args->mailbox);

		ctx = new IMAPContext();
		ctx->command = IMAPContext::IMAP_SUBSCRIBE;
		ctx->arguments = args;

	} else if (iequals(req.name, "unsubscribe")) {
		IMAPContext::Unsubscribe* args = new IMAPContext::Unsubscribe();
		Event::getParam(req.params, "mailbox", args->mailbox);

		ctx = new IMAPContext();
		ctx->command = IMAPContext::IMAP_UNSUBSCRIBE;
		ctx->arguments = args;

	} else if (iequals(req.name, "list")) {
		IMAPContext::List* args = new IMAPContext::List();
		Event::getParam(req.params, "mailbox", args->mailbox);
		Event::getParam(req.params, "reference", args->refName);

		ctx = new IMAPContext();
		ctx->command = IMAPContext::IMAP_LIST;
		ctx->arguments = args;

	} else if (iequals(req.name, "lsub")) {
		IMAPContext::LSub* args = new IMAPContext::LSub();
		Event::getParam(req.params, "mailbox", args->mailbox);
		Event::getParam(req.params, "reference", args->refName);

		ctx = new IMAPContext();
		ctx->command = IMAPContext::IMAP_LSUB;
		ctx->arguments = args;

	} else if (iequals(req.name, "status")) {
		IMAPContext::Status* args = new IMAPContext::Status();
		Event::getParam(req.params, "mailbox", args->mailbox);
		Event::getParam(req.params, "dataitems", args->dataItems);

		ctx = new IMAPContext();
		ctx->command = IMAPContext::IMAP_STATUS;
		ctx->arguments = args;

	} else if (iequals(req.name, "append")) {
		IMAPContext::Append* args = new IMAPContext::Append();
		Event::getParam(req.params, "mailbox", args->mailbox);
		Event::getParam(req.params, "flags", args->flags);
		Event::getParam(req.params, "datetime", args->dateTime);

		if (!Event::getParam(req.params, "message", args->literal)) {
			args->literal = req.content;
		}

		ctx = new IMAPContext();
		ctx->command = IMAPContext::IMAP_APPEND;
		ctx->arguments = args;

	} else if (iequals(req.name, "check")) {
		IMAPContext::Check* args = new IMAPContext::Check();

		ctx = new IMAPContext();
		ctx->command = IMAPContext::IMAP_CHECK;
		ctx->arguments = args;

	} else if (iequals(req.name, "close")) {
		IMAPContext::Close* args = new IMAPContext::Close();

		ctx = new IMAPContext();
		ctx->command = IMAPContext::IMAP_CLOSE;
		ctx->arguments = args;

	} else if (iequals(req.name, "expunge")) {
		IMAPContext::Expunge* args = new IMAPContext::Expunge();

		ctx = new IMAPContext();
		ctx->command = IMAPContext::IMAP_EXPUNGE;
		ctx->arguments = args;

	} else if (iequals(req.name, "search")) {
		IMAPContext::Search* args = new IMAPContext::Search();
		Event::getParam(req.params, "charset", args->charSet);
		Event::getParam(req.params, "criteria", args->criteria);

		ctx = new IMAPContext();
		ctx->command = IMAPContext::IMAP_SEARCH;
		ctx->arguments = args;

	} else if (iequals(req.name, "fetch")) {
		IMAPContext::Fetch* args = new IMAPContext::Fetch();
		Event::getParam(req.params, "sequence", args->sequence);
		Event::getParam(req.params, "itemnames", args->itemNames);

		ctx = new IMAPContext();
		ctx->command = IMAPContext::IMAP_FETCH;
		ctx->arguments = args;

	} else if (iequals(req.name, "store")) {
		IMAPContext::Store* args = new IMAPContext::Store();
		Event::getParam(req.params, "sequence", args->sequence);
		Event::getParam(req.params, "itemnames", args->itemNames);
		Event::getParam(req.params, "values", args->values);

		ctx = new IMAPContext();
		ctx->command = IMAPContext::IMAP_STORE;
		ctx->arguments = args;

	} else if (iequals(req.name, "copy")) {
		IMAPContext::Copy* args = new IMAPContext::Copy();
		Event::getParam(req.params, "mailbox", args->mailbox);
		Event::getParam(req.params, "sequence", args->sequence);

		ctx = new IMAPContext();
		ctx->command = IMAPContext::IMAP_COPY;
		ctx->arguments = args;

	} else if (iequals(req.name, "uid")) {
		IMAPContext::UId* args = new IMAPContext::UId();
		Event::getParam(req.params, "command", args->command);
		Event::getParam(req.params, "arguments", args->arguments);

		ctx = new IMAPContext();
		ctx->command = IMAPContext::IMAP_UID;
		ctx->arguments = args;

	} else if (boost::istarts_with(req.name, "x")) {
		IMAPContext::XExtension* args = new IMAPContext::XExtension();
		args->command = req.name;
		Event::getParam(req.params, "arguments", args->arguments);

		ctx = new IMAPContext();
		ctx->command = IMAPContext::IMAP_XEXTENSION;
		ctx->arguments = args;

	}

	if (ctx == NULL) {
		returnErrorExecution("Event '" + req.name + "' not known");
		return;
	}

	Event::getParam(req.params, "verbose", ctx->verbose);
	Event::getParam(req.params, "ssl", ctx->useSSL);

	ctx->invoker = this;
	ctx->sendReq = req;

	_workQueue.push(ctx);
}

void IMAPInvoker::process(IMAPContext* ctx) {
	CURL* _curl;
	CURLcode curlError;

	// see http://curl.haxx.se/libcurl/c/imap-tls.html
	_curl = curl_easy_init();
	if(_curl) {
		(curlError = curl_easy_setopt(_curl, CURLOPT_USERNAME, _username.c_str())) == CURLE_OK ||
		LOG(ERROR) << "Cannot set username: " << curl_easy_strerror(curlError);
		(curlError = curl_easy_setopt(_curl, CURLOPT_PASSWORD, _password.c_str())) == CURLE_OK ||
		LOG(ERROR) << "Cannot set password: " << curl_easy_strerror(curlError);
		(curlError = curl_easy_setopt(_curl, CURLOPT_URL, _server.c_str())) == CURLE_OK ||
		LOG(ERROR) << "Cannot set server string: " << curl_easy_strerror(curlError);

		if (ctx->useSSL) {
			(curlError = curl_easy_setopt(_curl, CURLOPT_USE_SSL, (long)CURLUSESSL_ALL)) == CURLE_OK ||
			LOG(ERROR) << "Cannot use SSL: " << curl_easy_strerror(curlError);
#if 1
			(curlError = curl_easy_setopt(_curl, CURLOPT_SSL_VERIFYPEER, 0L)) == CURLE_OK ||
			LOG(ERROR) << "Cannot unset verify peer with SSL: " << curl_easy_strerror(curlError);
			(curlError = curl_easy_setopt(_curl, CURLOPT_SSL_VERIFYHOST, 0L)) == CURLE_OK ||
			LOG(ERROR) << "Cannot unset verify host with SSL: " << curl_easy_strerror(curlError);
#else
			(curlError = curl_easy_setopt(_curl, CURLOPT_CAINFO, "/path/to/certificate.pem")) == CURLE_OK ||
			LOG(ERROR) << "Cannot set CA info path: " << curl_easy_strerror(curlError);
#endif

		}

		(curlError = curl_easy_setopt(_curl, CURLOPT_READFUNCTION, IMAPInvoker::writeCurlData)) == CURLE_OK ||
		LOG(ERROR) << "Cannot register read function: " << curl_easy_strerror(curlError);
		(curlError = curl_easy_setopt(_curl, CURLOPT_READDATA, ctx)) == CURLE_OK ||
		LOG(ERROR) << "Cannot register userdata for read function: " << curl_easy_strerror(curlError);
		(curlError = curl_easy_setopt(_curl, CURLOPT_WRITEFUNCTION, IMAPInvoker::readCurlData)) == CURLE_OK ||
		LOG(ERROR) << "Cannot register read function: " << curl_easy_strerror(curlError);
		(curlError = curl_easy_setopt(_curl, CURLOPT_WRITEDATA, ctx)) == CURLE_OK ||
		LOG(ERROR) << "Cannot register userdata for write function: " << curl_easy_strerror(curlError);

		if (ctx->verbose) {
			(curlError = curl_easy_setopt(_curl, CURLOPT_VERBOSE, 1L)) == CURLE_OK ||
			LOG(ERROR) << "Cannot set curl to verbose: " << curl_easy_strerror(curlError);
		}

		std::stringstream cmdSS;
		switch (ctx->command) {
		case IMAPContext::IMAP_SELECT: {
			IMAPContext::Select* cmd = (IMAPContext::Select*)ctx->arguments;
			cmdSS << "SELECT " << "\"" << cmd->mailbox << "\"";
			break;
		}
		case IMAPContext::IMAP_EXAMINE: {
			IMAPContext::Examine* cmd = (IMAPContext::Examine*)ctx->arguments;
			cmdSS << "EXAMINE " << "\"" << cmd->mailbox << "\"";
			break;
		}
		case IMAPContext::IMAP_CREATE: {
			IMAPContext::Create* cmd = (IMAPContext::Create*)ctx->arguments;
			cmdSS << "CREATE " << "\"" << cmd->mailbox << "\"";
			break;
		}
		case IMAPContext::IMAP_DELETE: {
			IMAPContext::Delete* cmd = (IMAPContext::Delete*)ctx->arguments;
			cmdSS << "DELETE " << "\"" << cmd->mailbox << "\"";
			break;
		}
		case IMAPContext::IMAP_RENAME: {
			IMAPContext::Rename* cmd = (IMAPContext::Rename*)ctx->arguments;
			cmdSS << "RENAME " << "\"" << cmd->mailbox << "\" \"" << cmd->newName << "\"";
			break;
		}
		case IMAPContext::IMAP_SUBSCRIBE: {
			IMAPContext::Subscribe* cmd = (IMAPContext::Subscribe*)ctx->arguments;
			cmdSS << "SUBSCRIBE " << "\"" << cmd->mailbox << "\"";
			break;
		}
		case IMAPContext::IMAP_UNSUBSCRIBE: {
			IMAPContext::Unsubscribe* cmd = (IMAPContext::Unsubscribe*)ctx->arguments;
			cmdSS << "UNSUBSCRIBE " << "\"" << cmd->mailbox << "\"";
			break;
		}
		case IMAPContext::IMAP_LIST: {
			IMAPContext::List* cmd = (IMAPContext::List*)ctx->arguments;
			cmdSS << "LIST " << "\"" << cmd->mailbox << "\" \"" << cmd->refName << "\"";
			break;
		}
		case IMAPContext::IMAP_LSUB: {
			IMAPContext::LSub* cmd = (IMAPContext::LSub*)ctx->arguments;
			cmdSS << "LSUB " << "\"" << cmd->mailbox << "\" \"" << cmd->refName << "\"";
			break;
		}
		case IMAPContext::IMAP_STATUS: {
			IMAPContext::Status* cmd = (IMAPContext::Status*)ctx->arguments;
			cmdSS << "STATUS " << "\"" << cmd->mailbox << "\" (" << cmd->dataItems << ")";
			break;
		}
		case IMAPContext::IMAP_APPEND: {
			IMAPContext::Append* cmd = (IMAPContext::Append*)ctx->arguments;
			cmdSS << "APPEND " << "\"" << cmd->mailbox << "\" (" << cmd->flags << ") {" << cmd->dateTime << "}";
			break;
		}
		case IMAPContext::IMAP_CHECK: {
			cmdSS << "CHECK";
			break;
		}
		case IMAPContext::IMAP_CLOSE: {
			cmdSS << "CLOSE";
			break;
		}
		case IMAPContext::IMAP_EXPUNGE: {
			cmdSS << "EXPUNGE";
			break;
		}
		case IMAPContext::IMAP_SEARCH: {
			IMAPContext::Search* cmd = (IMAPContext::Search*)ctx->arguments;
			cmdSS << "SEARCH ";
			if (cmd->charSet.size() > 0) {
				cmdSS << "CHARSET " << cmd->charSet << " ";
			}
			cmdSS << cmd->criteria;
			break;
		}
		case IMAPContext::IMAP_FETCH: {
			IMAPContext::Fetch* cmd = (IMAPContext::Fetch*)ctx->arguments;
			cmdSS << "FETCH " << cmd->sequence << " " << cmd->itemNames;
			break;
		}
		case IMAPContext::IMAP_STORE: {
			IMAPContext::Store* cmd = (IMAPContext::Store*)ctx->arguments;
			cmdSS << "STORE " << cmd->sequence << " " << cmd->itemNames << " " << cmd->values;
			break;
		}
		case IMAPContext::IMAP_COPY: {
			IMAPContext::Copy* cmd = (IMAPContext::Copy*)ctx->arguments;
			cmdSS << "COPY " << "\"" << cmd->mailbox << "\" " << cmd->sequence;
			break;
		}
		case IMAPContext::IMAP_UID: {
			IMAPContext::UId* cmd = (IMAPContext::UId*)ctx->arguments;
			cmdSS << "UID " << cmd->command << " " << cmd->arguments;
			break;
		}
		case IMAPContext::IMAP_XEXTENSION: {
			IMAPContext::XExtension* cmd = (IMAPContext::XExtension*)ctx->arguments;
			cmdSS << cmd->command << " " << cmd->arguments;
			break;
		}
		default:
			break;
		}
		curl_easy_setopt(_curl, CURLOPT_CUSTOMREQUEST, cmdSS.str().c_str());

		CURLcode res = curl_easy_perform(_curl);

		/* Check for errors */
		if(res != CURLE_OK) {
			LOG(ERROR) << "curl_easy_perform() failed: " << curl_easy_strerror(res);
			returnErrorExecution("error.mail.send");
		} else {

			Event e;

#if 0
			switch (ctx->command) {
			case IMAPContext::LIST:
				e.data = parseListReponse(ctx->inContent.str());
				break;
			default:
				break;
			}
#endif

			e.name = ctx->sendReq.name + ".success";
			e.data.compound["raw"] = Data(ctx->inContent.str(), Data::VERBATIM);

			returnEvent(e);
		}

		/* Always cleanup */
		curl_easy_cleanup(_curl);

	}
}

#if 0
Data IMAPInvoker::parseListReponse(const std::string& response) {
	Data data;

	std::string line;
	std::istringstream inSS(response);

	while(std::getline(inSS, line, '\n')) {
		// individual lines
		size_t lastSep = line.find_last_of("\" ");
		if (lastSep != std::string::npos) {

		}
	}

	return data;
}
#endif

void IMAPInvoker::cancel(const std::string sendId) {
}

void IMAPInvoker::invoke(const InvokeRequest& req) {
	Event::getParam(req.params, "username", _username);
	Event::getParam(req.params, "password", _password);
	Event::getParam(req.params, "server", _server);

	_isRunning = true;
	_thread = new tthread::thread(IMAPInvoker::run, this);
}

}