#include "FileElement.h"
#include <glog/logging.h>
#include <stdio.h>
#include <vector>

#include "uscxml/NameSpacingParser.h"

#ifdef BUILD_AS_PLUGINS
#include <Pluma/Connector.hpp>
#endif

namespace uscxml {

#ifdef BUILD_AS_PLUGINS
PLUMA_CONNECTOR
bool connect(pluma::Host& host) {
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

void FileElement::enterElement(const Arabica::DOM::Node<std::string>& node) {
	if (!HAS_ATTR(node, "url") && !HAS_ATTR(node, "urlexpr")) {
		LOG(ERROR) << "File element requires url or urlexpr";
		return;
	}
	_givenUrl = (HAS_ATTR(node, "url") ? ATTR(node, "url") : _interpreter->getDataModel().evalAsString(ATTR(node, "urlexpr")));

  std::string sandBoxStr = (HAS_ATTR(node, "sandbox") ? ATTR(node, "sandbox") : "on");
  if (boost::iequals(sandBoxStr, "off") || boost::iequals(sandBoxStr, "false") || boost::iequals(sandBoxStr, "no")) {
    _sandBoxed = false;
  }
	
	if (HAS_ATTR(node, "operation")) {
		std::string operation = ATTR(node, "operation");
		if (boost::iequals(operation, "read") || boost::iequals(operation, "load")) {
			_operation = READ;
		} else if(boost::iequals(operation, "write")) {
			_operation = WRITE;
		} else if(boost::iequals(operation, "append")) {
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
	size_t contentSize;
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
				content = data.binary->data;
				contentSize = data.binary->size;
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
	if (boost::iequals(type, "text")) {
		_type = TEXT;
	} else if (boost::iequals(type, "json")) {
		_type = JSON;
	} else if (boost::iequals(type, "binary")) {
		_type = BINARY;
	} else if(boost::iequals(type, "xml")) {
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
		
	_filename = _actualUrl.path();
	
	std::string writeMode;
	switch (_operation) {
		case APPEND:
			writeMode = "a+";
		case WRITE: {
			if (writeMode.length() == 0)
				writeMode = "w+";
			
			FILE *fp;
			fp = fopen(_filename.c_str(), writeMode.c_str());
			if (fp == NULL) {
				LOG(ERROR) << "Error opening '" << _filename << "' for writing: " << strerror(errno);
			}
			
			if (content && contentSize > 0) {
				size_t written = fwrite(content, 1, contentSize, fp);
				if (written != contentSize) {
					LOG(ERROR) << "Error writing to '" << _filename << "': " << strerror(errno);
					return;
				}
			} else if (contentStr.length() > 0) {
				size_t written = fwrite(contentStr.c_str(), contentStr.length(), 1, fp);
				if (written < 1) {
					LOG(ERROR) << "Error writing to '" << _filename << "': " << strerror(errno);
				}
			} else {
				LOG(WARNING) << "Nothing to write to '" << _filename;
			}
			fclose(fp);
			break;
		}
		case READ: {
			struct stat fileStat;
			int err = stat(_filename.c_str(), &fileStat);
			if (err < 0) {
				LOG(ERROR) << "Cannot stat file '" << _filename << "': " << strerror(errno);
				return;
			}
			
			Event event;
			event.name = callback;
			event.data.compound["file"].compound["name"] = Data(_filename, Data::VERBATIM);
			event.data.compound["file"].compound["mtime"] = toStr(fileStat.st_mtime);
			event.data.compound["file"].compound["ctime"] = toStr(fileStat.st_ctime);
			event.data.compound["file"].compound["atime"] = toStr(fileStat.st_atime);
			event.data.compound["file"].compound["size"]  = toStr(fileStat.st_size);
			

			FILE *fp;
			fp = fopen(_filename.c_str(), "r");

			fseek (fp, 0, SEEK_END);
			size_t filesize = ftell(fp);
			rewind (fp);

			char* fileContents = (char*)malloc(filesize);
			size_t read = fread(fileContents, 1, filesize, fp);
			fclose(fp);
			if (read != filesize) {
				LOG(ERROR) << "Error reading from '" << _filename << "': " << strerror(errno);
				return;
			}
			
			switch (_type) {
				case BINARY:
					event.data.compound["content"] = Data(fileContents, fileStat.st_size, 1);
					break;
				case TEXT:
					event.data.compound["content"] = Data(fileContents, Data::VERBATIM);
					free(fileContents);
					break;
				case JSON: {
					Data json = Data::fromJSON(fileContents);
					free(fileContents);
					if (!json) {
						LOG(ERROR) << "Cannot parse contents of " << _filename << " as JSON";
						return;
					}
					event.data.compound["content"] = json;
					break;
				}
				case XML: {
					NameSpacingParser parser = NameSpacingParser::fromXML(fileContents);
					if (parser.errorsReported()) {
						LOG(ERROR) << "Cannot parse contents of " << _filename << " as XML";
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

void FileElement::exitElement(const Arabica::DOM::Node<std::string>& node) {

}

}