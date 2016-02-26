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

#include "FileElement.h"
#include <glog/logging.h>
#include <stdio.h>
#include <vector>
#include <boost/algorithm/string.hpp>
#include "uscxml/messages/Blob.h"

#include "uscxml/dom/DOMUtils.h"
#include "uscxml/dom/NameSpacingParser.h"

#ifdef BUILD_AS_PLUGINS
#include <Pluma/Connector.hpp>
#endif

namespace uscxml {

#ifdef BUILD_AS_PLUGINS
PLUMA_CONNECTOR
bool pluginConnect(pluma::Host& host) {
	host.add( new FileElementProvider() );
	return true;
}
#endif

boost::shared_ptr<ExecutableContentImpl> FileElement::create(InterpreterImpl* interpreter) {
	boost::shared_ptr<FileElement> element = boost::shared_ptr<FileElement>(new FileElement());
	return element;
}

FileElement::~FileElement() {
}

void FileElement::enterElement(const Arabica::DOM::Element<std::string>& node) {
	if (!HAS_ATTR(node, "url") && !HAS_ATTR(node, "urlexpr")) {
		LOG(ERROR) << "File element requires url or urlexpr";
		return;
	}
	_givenUrl = (HAS_ATTR(node, "url") ? ATTR(node, "url") : _interpreter->getDataModel().evalAsString(ATTR(node, "urlexpr")));

	std::string sandBoxStr = (HAS_ATTR(node, "sandbox") ? ATTR(node, "sandbox") : "on");
	if (iequals(sandBoxStr, "off") || iequals(sandBoxStr, "false") || iequals(sandBoxStr, "no")) {
		_sandBoxed = false;
	}

	if (HAS_ATTR(node, "operation")) {
		std::string operation = ATTR(node, "operation");
		if (iequals(operation, "read") || iequals(operation, "load")) {
			_operation = READ;
		} else if(iequals(operation, "write")) {
			_operation = WRITE;
		} else if(iequals(operation, "append")) {
			_operation = APPEND;
		} else {
			LOG(ERROR) << "File element operation attribute not one of read, write or append.";
			return;
		}
	} else {
		_operation = READ;
	}

	// callback is only needed for reading
	std::string callback;
	if (_operation == READ) {
		if (!HAS_ATTR(node, "callback") && !HAS_ATTR(node, "callbackexpr")) {
			LOG(ERROR) << "File element requires callback or callbackexpr";
			return;
		}
		callback = (HAS_ATTR(node, "callback") ? ATTR(node, "callback") : _interpreter->getDataModel().evalAsString(ATTR(node, "callbackexpr")));
	}

	std::string contentStr;
	char* content = NULL;
	size_t contentSize = 0;
	if (_operation == WRITE || _operation == APPEND) {
		if (!HAS_ATTR(node, "content") && !HAS_ATTR(node, "contentexpr")) {
			LOG(ERROR) << "File element requires content or contentexpr";
			return;
		}
		if (HAS_ATTR(node, "content")) {
			contentStr = ATTR(node, "content");
		} else {
			Data data = _interpreter->getDataModel().getStringAsData(ATTR(node, "contentexpr"));
			if (data.binary) {
				content = data.binary.getData();
				contentSize = data.binary.getSize();
			} else if (data.atom.length() > 0) {
				contentStr = data.atom;
			}
		}
	}

	std::string type = "text";
	if (HAS_ATTR(node, "type")) {
		type = ATTR(node, "type");
	} else if(HAS_ATTR(node, "typeexpr")) {
		type = _interpreter->getDataModel().evalAsString(ATTR(node, "typeexpr"));
	}
	if (iequals(type, "text")) {
		_type = TEXT;
	} else if (iequals(type, "json")) {
		_type = JSON;
	} else if (iequals(type, "binary")) {
		_type = BINARY;
	} else if(iequals(type, "xml")) {
		_type = XML;
	} else {
		LOG(ERROR) << "File element type attribute not one of text, json, xml or binary.";
		return;
	}

	_actualUrl = URL(_givenUrl);
	if (_sandBoxed && _actualUrl.isAbsolute()) {
		LOG(ERROR) << "Given URL is absolute with sandboxing enabled.";
		return;
	}

	if (_sandBoxed)
		_actualUrl.toAbsolute(URL::getResourceDir());

	_filepath = _actualUrl.path();


	std::string writeMode;
	switch (_operation) {
	case APPEND:
		writeMode = "a+";
	case WRITE: {
		if (writeMode.length() == 0)
			writeMode = "w+";

		FILE *fp;
		fp = fopen(_filepath.c_str(), writeMode.c_str());
		if (fp == NULL) {
			LOG(ERROR) << "Error opening '" << _filepath << "' for writing: " << strerror(errno);
		}

		if (content && contentSize > 0) {
			size_t written = fwrite(content, 1, contentSize, fp);
			if (written != contentSize) {
				LOG(ERROR) << "Error writing to '" << _filepath << "': " << strerror(errno);
				return;
			}
		} else if (contentStr.length() > 0) {
			size_t written = fwrite(contentStr.c_str(), contentStr.length(), 1, fp);
			if (written < 1) {
				LOG(ERROR) << "Error writing to '" << _filepath << "': " << strerror(errno);
			}
		} else {
			LOG(WARNING) << "Nothing to write to '" << _filepath;
		}
		fclose(fp);
		break;
	}
	case READ: {
		struct stat fileStat;
		int err = stat(_filepath.c_str(), &fileStat);
		if (err < 0) {
			LOG(ERROR) << "Cannot stat file '" << _filepath << "': " << strerror(errno);
			return;
		}

		Event event;
		event.name = callback;

		std::string filename = _actualUrl.pathComponents()[_actualUrl.pathComponents().size() - 1];

		event.data.compound["file"].compound["name"] = Data(filename, Data::VERBATIM);
		event.data.compound["file"].compound["path"] = Data(_filepath, Data::VERBATIM);
		event.data.compound["file"].compound["mtime"] = Data(toStr(fileStat.st_mtime), Data::INTERPRETED);
		event.data.compound["file"].compound["ctime"] = Data(toStr(fileStat.st_ctime), Data::INTERPRETED);
		event.data.compound["file"].compound["atime"] = Data(toStr(fileStat.st_atime), Data::INTERPRETED);
		event.data.compound["file"].compound["size"]  = Data(toStr(fileStat.st_size), Data::INTERPRETED);


		FILE *fp;
		fp = fopen(_filepath.c_str(), "r");

		fseek (fp, 0, SEEK_END);
		size_t filesize = ftell(fp);
		rewind (fp);

		char* fileContents = (char*)malloc(filesize);
		size_t read = fread(fileContents, 1, filesize, fp);
		fclose(fp);
		if (read != filesize) {
			LOG(ERROR) << "Error reading from '" << _filepath << "': " << strerror(errno);
			return;
		}

		switch (_type) {
		case BINARY: {
			std::string mimetype = "application/octet-stream";
			if (HAS_ATTR(node, "mimetype")) {
				mimetype = ATTR(node, "mimetype");
			} else if(HAS_ATTR(node, "mimetypeexpr")) {
				mimetype = _interpreter->getDataModel().evalAsString(ATTR(node, "mimetypeexpr"));
			}

			event.data.compound["content"] = Data(fileContents, fileStat.st_size, mimetype, true);
			break;
		}
		case TEXT:
			event.data.compound["content"] = Data(fileContents, Data::VERBATIM);
			free(fileContents);
			break;
		case JSON: {
			Data json = Data::fromJSON(fileContents);
			free(fileContents);
			if (json.empty()) {
				LOG(ERROR) << "Cannot parse contents of " << _filepath << " as JSON";
				return;
			}
			event.data.compound["content"] = json;
			break;
		}
		case XML: {
			NameSpacingParser parser = NameSpacingParser::fromXML(fileContents);
			if (parser.errorsReported()) {
				LOG(ERROR) << "Cannot parse contents of " << _filepath << " as XML";
				return;
			}
			event.dom = parser.getDocument().getDocumentElement();
			break;
		}
		}
		_interpreter->receive(event);
		break;
	}
	}




}

void FileElement::exitElement(const Arabica::DOM::Element<std::string>& node) {

}

}