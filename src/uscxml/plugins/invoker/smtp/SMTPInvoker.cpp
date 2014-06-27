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

#include "SMTPInvoker.h"
#include <glog/logging.h>

#ifdef BUILD_AS_PLUGINS
#include <Pluma/Connector.hpp>
#endif

#include <boost/algorithm/string.hpp>
#include "uscxml/UUID.h"
#include "uscxml/messages/Blob.h"

namespace uscxml {

#ifdef BUILD_AS_PLUGINS
PLUMA_CONNECTOR
bool pluginConnect(pluma::Host& host) {
	host.add( new SMTPInvokerProvider() );
	return true;
}
#endif

SMTPInvoker::SMTPInvoker() {
}

SMTPInvoker::~SMTPInvoker() {
};

boost::shared_ptr<InvokerImpl> SMTPInvoker::create(InterpreterImpl* interpreter) {
	boost::shared_ptr<SMTPInvoker> invoker = boost::shared_ptr<SMTPInvoker>(new SMTPInvoker());
	return invoker;
}

Data SMTPInvoker::getDataModelVariables() {
	Data data;
	return data;
}

size_t SMTPInvoker::writeCurlData(void *ptr, size_t size, size_t nmemb, void *userdata) {
	if (!userdata)
		return 0;

	SMTPContext* ctx = (SMTPContext*)userdata;

	size_t toWrite = (std::min)(ctx->content.length() - ctx->readPtr, size * nmemb);
	if (toWrite > 0) {
		memcpy (ptr, ctx->content.c_str() + ctx->readPtr, toWrite);
		ctx->readPtr += toWrite;
	}

	return toWrite;
}

std::list<std::string> SMTPInvoker::getAtoms(std::list<Data> list) {
	std::list<std::string> atoms;

	std::list<Data>::const_iterator iter = list.begin();
	while(iter != list.end()) {
		const Data& data = *iter;
		if (data.atom.size() > 0) {
			atoms.push_back(data.atom);
		} else if (data.array.size() > 0) {
			std::list<Data>::const_iterator arrIter = data.array.begin();
			while(arrIter != data.array.end()) {
				if (arrIter->atom.size() > 0) {
					atoms.push_back(arrIter->atom);
					arrIter++;
				}
			}
		}
		iter++;
	}
	return atoms;
}

void SMTPInvoker::getAttachments(std::list<Data> list, std::list<Data>& attachments) {
	// accumulate attachments with filename, mimetype and data
	std::list<Data>::const_iterator iter = list.begin();
	while(iter != list.end()) {
		const Data& data = *iter;
		if (data.hasKey("data")) {
			// compound structure with all information
			Data att = data;

			if (!att.hasKey("mimetype")) {
				if (att["data"].binary && att["data"].binary->mimeType.size() > 0) {
					att.compound["mimetype"] = Data(att["data"].binary->mimeType, Data::VERBATIM);
				} else {
					att.compound["mimetype"] = Data("text/plain", Data::VERBATIM);
				}
			}

			if (!att.hasKey("filename")) {
				std::stringstream filenameSS;
				filenameSS << "attachment" << attachments.size() + 1;
				if (boost::starts_with(att.compound["mimetype"].atom, "text")) {
					filenameSS << ".txt";
				} else {
					filenameSS << ".bin";
				}
				att.compound["filename"] = Data(filenameSS.str(), Data::VERBATIM);
			}

			attachments.push_back(att);

		} else if (data.binary) {
			// a single binary blob
			Data att;

			att.compound["data"].binary = data.binary;

			if (data.binary->mimeType.size() > 0) {
				att.compound["mimetype"] = Data(attachments.back()["data"].binary->mimeType, Data::VERBATIM);
			} else {
				att.compound["mimetype"] = Data("application/octet-stream", Data::VERBATIM);
			}

			std::stringstream filenameSS;
			filenameSS << "attachment" << attachments.size() + 1;
			if (boost::starts_with(att.compound["mimetype"].atom, "text")) {
				filenameSS << ".txt";
			} else {
				filenameSS << ".bin";
			}
			att.compound["filename"] = Data(filenameSS.str(), Data::VERBATIM);

			attachments.push_back(att);

		} else if (data.compound.size() > 0) {
			// data is some compound, descent to find attachment structures or binaries
			std::map<std::string, Data>::const_iterator compIter = data.compound.begin();
			while(compIter != data.compound.end()) {
				std::list<Data> tmp;
				tmp.push_back(compIter->second);
				getAttachments(tmp, attachments);
				compIter++;
			}
		} else if (data.array.size() > 0) {
			// descent into array
			getAttachments(data.array, attachments);
		}
		iter++;
	}
}

void SMTPInvoker::send(const SendRequest& req) {
	if (iequals(req.name, "mail.send")) {

		struct curl_slist* recipients = NULL;
		CURLcode curlError;
		std::string multipartSep;

		bool verbose;
		std::string from;
		std::string subject;
		std::string contentType;
		std::list<Data> headerParams;
		std::list<Data> toParams;
		std::list<Data> ccParams;
		std::list<Data> bccParams;
		std::list<Data> attachmentParams;

		Event::getParam(req.params, "verbose", verbose);
		Event::getParam(req.params, "Content-Type", contentType);
		Event::getParam(req.params, "attachment", attachmentParams);
		Event::getParam(req.params, "from", from);
		Event::getParam(req.params, "subject", subject);
		Event::getParam(req.params, "header", headerParams);
		Event::getParam(req.params, "to", toParams);
		Event::getParam(req.params, "cc", ccParams);
		Event::getParam(req.params, "bcc", bccParams);

		if (contentType.size() == 0)
			contentType = "text/plain; charset=\"UTF-8\"";

		SMTPContext* ctx = new SMTPContext();
		std::stringstream contentSS;

		std::list<std::string>::const_iterator recIter;
		std::list<std::string> to = getAtoms(toParams);
		std::list<std::string> cc = getAtoms(ccParams);
		std::list<std::string> bcc = getAtoms(bccParams);
		std::list<std::string> headers = getAtoms(headerParams);
		std::list<Data> attachments;
		getAttachments(attachmentParams, attachments);

		if (to.size() == 0)
			return;

		recIter = to.begin();
		recIter++; // skip first as we need it in CURLOPT_MAIL_RCPT
		while(recIter != to.end()) {
			contentSS << "TO: " << *recIter << std::endl;
			recIter++;
		}
		recIter = cc.begin();
		while(recIter != cc.end()) {
			contentSS << "CC: " << *recIter << std::endl;
			recIter++;
		}
		recIter = bcc.begin();
		while(recIter != bcc.end()) {
			contentSS << "BCC: " << *recIter << std::endl;
			recIter++;
		}

		recIter = headers.begin();
		while(recIter != headers.end()) {
			contentSS << *recIter << std::endl;
			recIter++;
		}

		if (subject.length() > 0) {
			boost::replace_all(subject, "\n\r", " ");
			boost::replace_all(subject, "\r\n", " ");
			boost::replace_all(subject, "\n", " ");
			boost::replace_all(subject, "\r", " ");
			contentSS << "Subject: " << subject << "\n";
		}

		// content type is different when we have attachments
		if (attachments.size() > 0) {
			multipartSep = UUID::getUUID();
			boost::replace_all(multipartSep, "-", "");
			contentSS << "Content-Type: multipart/mixed; boundary=\"" << multipartSep << "\"\n";
			contentSS << "MIME-Version: 1.0\n";
			contentSS << "\n";
			contentSS << "--" << multipartSep << "\n";
			contentSS << "Content-Type: " << contentType << "\n";
		} else {
			// when we have no attachment, respect user-defined or use text/plain
			contentSS << "Content-Type: " << contentType << "\n";
		}

		contentSS << "\n";
		contentSS << req.content;

		std::list<Data>::iterator attIter = attachments.begin();
		while(attIter != attachments.end()) {
			// only send valid attachments
			if(!attIter->hasKey("filename") || !attIter->hasKey("mimetype") || !attIter->hasKey("data")) {
				LOG(ERROR) << "Not sending attachment as filename, mimetype or data is missing: " << *attIter;
			} else {
				contentSS << "\n\n";
				contentSS << "--" << multipartSep << "\n";
				contentSS << "Content-Disposition: attachment; filename=\"" << attIter->compound["filename"].atom << "\"";
				contentSS << "\n";

				contentSS << "Content-Type: " << attIter->compound["mimetype"].atom << "; ";
				contentSS << "name=\"" << attIter->compound["filename"].atom << "\"";
				contentSS << "\n";

				if (attIter->compound["data"].binary) {
					contentSS << "Content-Transfer-Encoding: base64";
					contentSS << "\n\n";
					contentSS << attIter->compound["data"].binary->base64();
				} else {
					contentSS << "Content-Transfer-Encoding: 7Bit";
					contentSS << "\n\n";
					contentSS << attIter->compound["data"].atom;
				}
			}
			attIter++;
		}

		ctx->content = contentSS.str();
		ctx->invoker = this;


		// see http://curl.haxx.se/libcurl/c/smtp-tls.html
		_curl = curl_easy_init();
		if(_curl) {
			(curlError = curl_easy_setopt(_curl, CURLOPT_USERNAME, _username.c_str())) == CURLE_OK ||
			LOG(ERROR) << "Cannot set username: " << curl_easy_strerror(curlError);
			(curlError = curl_easy_setopt(_curl, CURLOPT_PASSWORD, _password.c_str())) == CURLE_OK ||
			LOG(ERROR) << "Cannot set password: " << curl_easy_strerror(curlError);
			(curlError = curl_easy_setopt(_curl, CURLOPT_URL, _server.c_str())) == CURLE_OK ||
			LOG(ERROR) << "Cannot set server string: " << curl_easy_strerror(curlError);
			(curlError = curl_easy_setopt(_curl, CURLOPT_USE_SSL, (long)CURLUSESSL_ALL)) == CURLE_OK ||
			LOG(ERROR) << "Cannot use SSL: " << curl_easy_strerror(curlError);

			// this is needed, even if we have a callback function
			recipients = curl_slist_append(recipients, to.begin()->c_str());
			(curlError = curl_easy_setopt(_curl, CURLOPT_MAIL_RCPT, recipients)) == CURLE_OK ||
			LOG(ERROR) << "Cannot set mail recipient: " << curl_easy_strerror(curlError);

			(curlError = curl_easy_setopt(_curl, CURLOPT_READFUNCTION, SMTPInvoker::writeCurlData)) == CURLE_OK ||
			LOG(ERROR) << "Cannot register read function: " << curl_easy_strerror(curlError);
			(curlError = curl_easy_setopt(_curl, CURLOPT_READDATA, ctx)) == CURLE_OK ||
			LOG(ERROR) << "Cannot register userdata for read function: " << curl_easy_strerror(curlError);
			(curlError = curl_easy_setopt(_curl, CURLOPT_UPLOAD, 1L)) == CURLE_OK ||
			LOG(ERROR) << "Cannot set upload parameter: " << curl_easy_strerror(curlError);

#if 1
			(curlError = curl_easy_setopt(_curl, CURLOPT_SSL_VERIFYPEER, 0L)) == CURLE_OK ||
			LOG(ERROR) << "Cannot unset verify peer with SSL: " << curl_easy_strerror(curlError);
			(curlError = curl_easy_setopt(_curl, CURLOPT_SSL_VERIFYHOST, 0L)) == CURLE_OK ||
			LOG(ERROR) << "Cannot unset verify host with SSL: " << curl_easy_strerror(curlError);
#else
			(curlError = curl_easy_setopt(_curl, CURLOPT_CAINFO, "/path/to/certificate.pem")) == CURLE_OK ||
			LOG(ERROR) << "Cannot set CA info path: " << curl_easy_strerror(curlError);
#endif

			if (from.length() > 0) {
				(curlError = curl_easy_setopt(_curl, CURLOPT_MAIL_FROM, from.c_str())) == CURLE_OK ||
				LOG(ERROR) << "Cannot set from parameter: " << curl_easy_strerror(curlError);
			}

			if (verbose) {
				(curlError = curl_easy_setopt(_curl, CURLOPT_VERBOSE, 1L)) == CURLE_OK ||
				LOG(ERROR) << "Cannot set curl to verbose: " << curl_easy_strerror(curlError);
			}

			CURLcode res = curl_easy_perform(_curl);

			/* Check for errors */
			if(res != CURLE_OK) {
				LOG(ERROR) << "curl_easy_perform() failed: " << curl_easy_strerror(res);
				returnErrorExecution("error.mail.send");
			} else {
				returnErrorExecution("success.mail.send");
			}
			/* Free the list of recipients */
			if (recipients)
				curl_slist_free_all(recipients);

			/* Always cleanup */
			curl_easy_cleanup(_curl);

		}

	}
}

void SMTPInvoker::cancel(const std::string sendId) {
}

void SMTPInvoker::invoke(const InvokeRequest& req) {
	Event::getParam(req.params, "username", _username);
	Event::getParam(req.params, "password", _password);
	Event::getParam(req.params, "server", _server);
}

}