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

#include "URL.h"
#include "uscxml/messages/Event.h"

#include <string>
#include <cassert>

#include "uscxml/interpreter/Logging.h"
#include "uscxml/config.h"

#include <curl/curl.h>
#include <uriparser/Uri.h>

#include <sys/types.h>
#include <sys/stat.h>

#ifdef _WIN32
#include <direct.h>
#include <Shlobj.h>

#define getcwd _getcwd
#else
#include <unistd.h> // getcwd
#include <pwd.h> // getpwuid
#endif

#define DOWNLOAD_IF_NECESSARY if (!_isDownloaded) { download(true); }
#define USCXML_URI_STRING(obj, field) std::string(obj.field.first, (obj.field.afterLast - obj.field.first))

namespace uscxml {

std::string URL::currTmpDir;

std::string URL::getTempDir(bool shared) {

#ifdef _WIN32
	struct stat st = { 0 };
	TCHAR tmpPrefix [MAX_PATH];

	// retrieve and optionally create temporary directory
	if (!GetTempPath(MAX_PATH, tmpPrefix)) {
		ERROR_EXECUTION_THROW(std::string("Cannot retrieve temporary directory"));
	}
	if (stat(tmpPrefix, &st) == -1) {
		CreateDirectory(tmpPrefix, NULL);
		if (GetLastError() == ERROR_PATH_NOT_FOUND) {
			ERROR_EXECUTION_THROW(std::string("Cannot create a temporary directory at '") + tmpPrefix + "'");
		}
	}

	if (shared) {
		// create uscxml folder in temporary directory
		std::string sharedTmpDir = std::string(tmpPrefix) + PATH_SEPERATOR + "uscxml";

		if (stat(sharedTmpDir.c_str(), &st) == -1) {
			CreateDirectory (sharedTmpDir.c_str(), NULL);
			if (GetLastError() == ERROR_PATH_NOT_FOUND) {
				ERROR_EXECUTION_THROW(std::string("Cannot create a temporary directory at '") + sharedTmpDir + "'");
			}
		}
		return sharedTmpDir;

	} else {
		if (currTmpDir.size() == 0) {
			// create random folder in temporary directory
			// http://stackoverflow.com/questions/6287475/creating-a-unique-temporary-directory-from-pure-c-in-windows
			// https://msdn.microsoft.com/en-us/library/windows/desktop/aa363875(v=vs.85).aspx
			TCHAR tempFileName[MAX_PATH];
			if (GetTempFileName(tmpPrefix, // directory for tmp files
			                    TEXT("uscxml."),     // temp file name prefix
			                    0,                // create unique name
			                    tempFileName)) {
				DeleteFile(tempFileName);

				if (stat(tempFileName, &st) == -1) {
					CreateDirectory(tempFileName, NULL);
					if (GetLastError() == ERROR_PATH_NOT_FOUND) {
						ERROR_EXECUTION_THROW(std::string("Cannot create a temporary directory at '") + tempFileName + "'");
					}
				}

				currTmpDir = tempFileName;
			} else {
				ERROR_EXECUTION_THROW(std::string("Cannot create a temporary directory at '") + tmpPrefix + "'");
			}
		}
		return currTmpDir;
	}

#else
	std::string tmpPrefix = "/tmp";
	const char* tmpEnv = getenv("TMPDIR");
	if (tmpEnv != NULL)
		tmpPrefix = tmpEnv;

	if (tmpPrefix[tmpPrefix.size() - 1] != PATH_SEPERATOR)
		tmpPrefix += PATH_SEPERATOR;

	if (shared) {
		struct stat st = {0};

		std::string sharedTmpDir = tmpPrefix + "uscxml";
		if (stat(sharedTmpDir.c_str(), &st) == -1) {
			int err = mkdir(sharedTmpDir.c_str(), S_IRWXU | S_IRWXG | S_IRWXO); // 777
			if (err)
				ERROR_EXECUTION_THROW(std::string("Cannot create a temporary directory at '") + sharedTmpDir + "':" + strerror(errno));

		}
		return sharedTmpDir;

	} else {
		if (currTmpDir.size() == 0) {
			std::string tmpPrefix = "/tmp";
			const char* tmpEnv = getenv("TMPDIR");
			if (tmpEnv != NULL)
				tmpPrefix = tmpEnv;
			const char* tmpName = mkdtemp((char*)std::string(tmpPrefix + "uscxml.XXXXXX").c_str()); // can we merely drop the constness?
			if (tmpName != NULL) {
				currTmpDir = tmpName;
			} else {
				ERROR_EXECUTION_THROW(std::string("Cannot create a temporary directory:") + strerror(errno));
			}
		}
		return currTmpDir;
	}
#endif
}

// Version for MacOSX in URL.mm
#if (!defined APPLE && !defined IOS)
std::string URL::getResourceDir() {
#ifdef _WIN32
	TCHAR szPath[MAX_PATH];
	std::string resourceDir;
	if (SHGetFolderPath(NULL, CSIDL_APPDATA, NULL, 0, szPath) == S_OK) {
		resourceDir = std::string(szPath) + PATH_SEPERATOR + "uscxml";
	} else {
		char* envData = getenv("APPDATA");
		if (envData) {
			resourceDir = std::string(envData) + PATH_SEPERATOR + "uscxml";
		} else {
			ERROR_EXECUTION_THROW("Could not get resource directory");
		}
	}

	struct stat st = { 0 };

	if (stat(resourceDir.c_str(), &st) == -1) {
		CreateDirectory(resourceDir.c_str(), NULL);
		if (GetLastError() == ERROR_PATH_NOT_FOUND) {
			ERROR_EXECUTION_THROW(std::string("Cannot create a resource directory at '") + resourceDir + "'");
		}
	}
	return resourceDir;

#else
	struct passwd* pw = getpwuid(getuid());
	std::string homedir(pw->pw_dir);
	struct stat dirStat;
	int err = 0;

	err = stat(std::string(homedir + PATH_SEPERATOR + ".config").c_str(), &dirStat);
	if (err == ENOENT) {
		err = mkdir(std::string(homedir + PATH_SEPERATOR + ".config").c_str(), S_IWUSR | S_IRUSR | S_IROTH);
	}

	err = stat(std::string(homedir + PATH_SEPERATOR + ".config" + PATH_SEPERATOR + "uscxml").c_str(), &dirStat);
	if (err != 0) {
		// std::cout << std::string(homedir + PATH_SEPERATOR + ".config" + PATH_SEPERATOR + "uscxml") << std::endl;
		err = mkdir(std::string(homedir + PATH_SEPERATOR + ".config" + PATH_SEPERATOR + "uscxml").c_str(),
		            S_IWUSR | S_IRUSR | S_IROTH | S_IRGRP | S_IXUSR | S_IXOTH | S_IXGRP);
	}

	err = stat(std::string(homedir + PATH_SEPERATOR + ".config" + PATH_SEPERATOR + "uscxml").c_str(), &dirStat);
	if (err == 0) {
		return homedir + PATH_SEPERATOR + ".config" + PATH_SEPERATOR + "uscxml";
	}
	return "";
#endif
}
#endif

void URLImpl::prepareException(ErrorEvent& exception, int errorCode, const std::string& origUri, void* parser) {
	exception.data.compound["uri"].atom = origUri;

	if (parser != NULL && ((UriParserStateA*)parser)->errorPos != NULL) {
		const char* startPtr = origUri.c_str();
		while(startPtr != ((UriParserStateA*)parser)->errorPos && *startPtr != '\0') {
			exception.data.compound["urk"].atom += " ";
			startPtr++;
		}
		exception.data.compound["urk"].atom += "^";
	}

	switch (errorCode) {
	case URI_ERROR_SYNTAX:
		exception.data.compound["cause"].atom = "Parsed text violates expected format";
		break;
	case URI_ERROR_NULL:
		exception.data.compound["cause"].atom = "One of the params passed was NULL although it mustn't be";
		break;
	case URI_ERROR_MALLOC:
		exception.data.compound["cause"].atom = "Requested memory could not be allocated";
		break;
	case URI_ERROR_OUTPUT_TOO_LARGE:
		exception.data.compound["cause"].atom = "Some output is to large for the receiving buffer";
		break;
	case URI_ERROR_NOT_IMPLEMENTED:
		exception.data.compound["cause"].atom = "The called function is not implemented yet";
		break;
	case URI_ERROR_RANGE_INVALID:
		exception.data.compound["cause"].atom = "The parameters passed contained invalid ranges";
		break;
	case URI_ERROR_ADDBASE_REL_BASE:
		exception.data.compound["cause"].atom = "Given base is not absolute";
		break;
	case URI_ERROR_REMOVEBASE_REL_SOURCE:
		exception.data.compound["cause"].atom = "Given base is not absolute";
		break;

	default:
		break;
	}
}

URLImpl::URLImpl() : _handle(NULL), _requestType(GET), _isDownloaded(false), _hasFailed(false) {
	_uri = malloc(sizeof(UriUriA));
}

URLImpl::URLImpl(const std::string& url) : _orig(url), _handle(NULL), _requestType(GET), _isDownloaded(false), _hasFailed(false) {
	UriParserStateA state;
	_uri = malloc(sizeof(UriUriA));
	state.uri = (UriUriA*)_uri;

	int err = uriParseUriA(&state, _orig.c_str());
	if (err != URI_SUCCESS) {
		UriParserStateA state2;
		state2.uri = (UriUriA*)_uri;

		char* tmp = (char*)malloc(8 + 3 * _orig.size() + 1);
		uriWindowsFilenameToUriStringA(_orig.c_str(), tmp);
		_orig = std::string(tmp);
		err = uriParseUriA(&state2, _orig.c_str());
		free(tmp);
	}

	if (err != URI_SUCCESS) {
		UriParserStateA state2;
		state2.uri = (UriUriA*)_uri;

		char* tmp = (char*)malloc(7 + 3 * _orig.size() + 1 );
		uriUnixFilenameToUriStringA(_orig.c_str(), tmp);
		_orig = std::string(tmp);
		err = uriParseUriA(&state2, _orig.c_str());
		free(tmp);
	}

	if (err != URI_SUCCESS) {
		ErrorEvent exc;
		prepareException(exc, err, _orig, &state);
		throw exc;
	}
}

URLImpl::~URLImpl() {
	uriFreeUriMembersA((UriUriA*)_uri);
	if (_handle != NULL)
		curl_easy_cleanup(_handle);
	free(_uri);
}

URL URLImpl::resolve(URLImpl* relative, URLImpl* absolute) {
	std::shared_ptr<URLImpl> dest(new URLImpl());
	int err = uriAddBaseUriExA(((UriUriA*)dest->_uri),
	                           ((UriUriA*)relative->_uri),
	                           ((UriUriA*)absolute->_uri), URI_RESOLVE_IDENTICAL_SCHEME_COMPAT);
	if (err != URI_SUCCESS) {
		ErrorEvent exc("Cannot resolve " + (std::string)(*relative) + " with " + (std::string)(*absolute));
		prepareException(exc, err, "", NULL);
		throw exc;
	}

	// serialize as string and reparse to mantain string in _orig
	return URL((std::string)(*dest.get()));
}

URL URLImpl::resolveWithCWD(URLImpl* relative) {
	char currPath[FILENAME_MAX];
	if (!getcwd(currPath, sizeof(currPath))) {
		ERROR_PLATFORM_THROW("Cannot get current working directory");
	}
	currPath[sizeof(currPath) - 1] = '\0'; /* not really required? */

	// without the trailing slash, last component is assumed a file
#if WIN32
	std::shared_ptr<URLImpl> cwdURL(new URLImpl(std::string(currPath)));
#else
	std::shared_ptr<URLImpl> cwdURL(new URLImpl(std::string("file://") + currPath + PATH_SEPERATOR));
#endif

	return resolve(relative, cwdURL.get());
}

URL URLImpl::refer(URLImpl* absoluteSource, URLImpl* absoluteBase) {
	std::shared_ptr<URLImpl> dest(new URLImpl());
	int err = uriRemoveBaseUriA(((UriUriA*)dest->_uri),
	                            ((UriUriA*)absoluteSource->_uri),
	                            ((UriUriA*)absoluteBase->_uri), URI_FALSE);
	if (err != URI_SUCCESS) {
		ErrorEvent exc("Cannot make a relative reference for " + (std::string)(*absoluteSource) + " with " + (std::string)(*absoluteBase));
		prepareException(exc, err, "", NULL);
		throw exc;
	}

	// serialize as string and reparse to mantain string in _orig
	return URL((std::string)(*dest.get()));
}

void URLImpl::normalize() {
	int err = uriNormalizeSyntaxA((UriUriA*)_uri);
	if (err != URI_SUCCESS) {
		ErrorEvent exc("Cannot normalize URL " + (std::string)*this);
		prepareException(exc, err, _orig, NULL);
		throw exc;
	}
}

bool URLImpl::isAbsolute() const {
	// see https://sourceforge.net/p/uriparser/bugs/3/
	return ((UriUriA*)_uri)->absolutePath || ((((UriUriA*)_uri)->hostText.first != nullptr) && (((UriUriA*)_uri)->pathHead != nullptr));
}

std::string URLImpl::scheme() const {
	return USCXML_URI_STRING((*(UriUriA*)_uri), scheme);
}

std::string URLImpl::userInfo() const {
	return USCXML_URI_STRING((*(UriUriA*)_uri), userInfo);
}

std::string URLImpl::host() const {
	return USCXML_URI_STRING((*(UriUriA*)_uri), hostText);
}

std::string URLImpl::port() const {
	return USCXML_URI_STRING((*(UriUriA*)_uri), portText);
}

std::string URLImpl::fragment() const {
	return USCXML_URI_STRING((*(UriUriA*)_uri), fragment);
}

std::string URLImpl::path() const {
	UriPathSegmentA* firstSeg = ((UriUriA*)_uri)->pathHead;
	UriPathSegmentA* lastSeg = firstSeg;
	while(lastSeg->next) {
		lastSeg = lastSeg->next;
	}

	std::string path;

	// what a mess!
	if (((UriUriA*)_uri)->absolutePath ||
	        (((UriUriA*)_uri)->pathHead != NULL &&
	         (((UriUriA*)_uri)->hostText.first != NULL ||
	          ((UriUriA*)_uri)->hostData.ip4 != NULL ||
	          ((UriUriA*)_uri)->hostData.ip6 != NULL ||
	          ((UriUriA*)_uri)->hostData.ipFuture.first != NULL))) {
		path += "/";
	}
	path += std::string(firstSeg->text.first, lastSeg->text.afterLast - firstSeg->text.first);
	return path;
}

std::list<std::string> URLImpl::pathComponents() const {
	std::list<std::string> pathList;

	UriPathSegmentA* currSeg = ((UriUriA*)_uri)->pathHead;
	while(currSeg != NULL) {
		pathList.push_back(USCXML_URI_STRING((*currSeg), text));
		currSeg = currSeg->next;
	}

	return pathList;
}

std::map<std::string, std::string> URLImpl::query() const {
	UriQueryListA * queryList;
	UriQueryListA * currList;
	std::map<std::string, std::string> queryMap;
	int itemCount;

	int err = uriDissectQueryMallocA(&queryList, &itemCount, (*(UriUriA*)_uri).query.first, (*(UriUriA*)_uri).query.afterLast);
	if (err != URI_SUCCESS) {
		ErrorEvent exc("Cannot get query from URL " + (std::string)*this);
		prepareException(exc, err, _orig, NULL);
		throw exc;
	}

	currList = queryList;
	while(currList != NULL) {
		queryMap[currList->key] = currList->value != NULL ? currList->value : "";
		currList = currList->next;
	}

	uriFreeQueryListA(queryList);

	return queryMap;
}

CURL* URLImpl::getCurlHandle() {
	if (_handle == NULL) {
		_handle = curl_easy_init();
		if (_handle == NULL)
			throw ErrorEvent("curl_easy_init returned NULL, this is bad!");
	}
	return _handle;
}

size_t URLImpl::writeHandler(void *ptr, size_t size, size_t nmemb, void *userdata) {
	URLImpl* url = (URLImpl*)userdata;
	url->_rawInContent.write((char*)ptr, size * nmemb);

	std::set<URLMonitor*>::iterator monIter = url->_monitors.begin();
	while(monIter != url->_monitors.end()) {
		(*monIter)->contentChunkReceived(URL(url->shared_from_this()), std::string((char*)ptr, size * nmemb));
		monIter++;
	}

	return size * nmemb;
}

size_t URLImpl::headerHandler(void *ptr, size_t size, size_t nmemb, void *userdata) {
	URLImpl* url = (URLImpl*)userdata;
	url->_rawInHeader.write((char*)ptr, size * nmemb);

	std::set<URLMonitor*>::iterator monIter = url->_monitors.begin();
	while(monIter != url->_monitors.end()) {
		(*monIter)->headerChunkReceived(URL(url->shared_from_this()), std::string((char*)ptr, size * nmemb));
		monIter++;
	}

	return size * nmemb;
}

void URLImpl::downloadStarted() {
	//	LOG(USCXML_INFO) << "Starting download of " << asString() << std::endl;
	_rawInContent.str("");
	_rawInContent.clear();
	_rawInHeader.str("");
	_rawInHeader.clear();

	_statusMsg = "";
	_statusCode = "";

	std::set<URLMonitor*>::iterator monIter = _monitors.begin();
	while(monIter != _monitors.end()) {
		(*monIter)->downloadStarted(URL(shared_from_this()));
		monIter++;
	}
}

void URLImpl::downloadCompleted() {
	std::lock_guard<std::recursive_mutex> lock(_mutex);

	if (iequals(scheme(), "http")) {
		// process header fields
		std::string line;
		while (std::getline(_rawInHeader, line)) {
			size_t colon = line.find_first_of(":");
			size_t newline = line.find_first_of("\r\n");
			if (newline == std::string::npos)
				newline = line.size();

			if (colon == std::string::npos) {
				_statusMsg = line.substr(0, newline);
				if (_statusMsg.length() >= 11)
					_statusCode = _statusMsg.substr(9, 3);
			} else {
				std::string key = line.substr(0, colon);
				size_t firstChar = line.find_first_not_of(": ", colon, 2);
				if (firstChar == std::string::npos) {
					// nothing but spaces?
					_inHeaders[line.substr(0, newline)] = "";
				} else {
					std::string value = line.substr(firstChar, newline - firstChar);
					_inHeaders[key] = value;
				}
			}
		}
	}

	_hasFailed = false;
	_isDownloaded = true;
	_condVar.notify_all();

	std::set<URLMonitor*>::iterator monIter = _monitors.begin();
	while(monIter != _monitors.end()) {
		(*monIter)->downloadCompleted(URL(shared_from_this()));
		monIter++;
	}
}

void URLImpl::downloadFailed(int errorCode) {
	std::lock_guard<std::recursive_mutex> lock(_mutex);

	_error = curl_easy_strerror((CURLcode)errorCode);
	_hasFailed = true;
	_isDownloaded = false;
	_condVar.notify_all();

	std::set<URLMonitor*>::iterator monIter = _monitors.begin();
	while(monIter != _monitors.end()) {
		(*monIter)->downloadFailed(URL(shared_from_this()), errorCode);
		monIter++;
	}

}

void URLImpl::addOutHeader(const std::string& key, const std::string& value) {
	_outHeader[key] = value;
}
void URLImpl::setOutContent(const std::string& content) {
	_outContent = content;
	_requestType = URLRequestType::POST;
}
void URLImpl::setRequestType(URLRequestType requestType) {
	_requestType = requestType;

}

const std::map<std::string, std::string> URLImpl::getInHeaderFields() {
	DOWNLOAD_IF_NECESSARY
	return _inHeaders;
}

const std::string URLImpl::getInHeaderField(const std::string& key) {
	DOWNLOAD_IF_NECESSARY
	if (_inHeaders.find(key) != _inHeaders.end()) {
		return _inHeaders[key];
	}
	return "";
}

const std::string URLImpl::getStatusCode() const {
	//        DOWNLOAD_IF_NECESSARY
	return _statusCode;
}

const std::string URLImpl::getStatusMessage() const {
	//        DOWNLOAD_IF_NECESSARY
	return _statusMsg;
}

const std::string URLImpl::getInContent(bool forceReload) {
	if (forceReload)
		_isDownloaded = false;
	DOWNLOAD_IF_NECESSARY
	return _rawInContent.str();
}

const void URLImpl::download(bool blocking) {
	std::lock_guard<std::recursive_mutex> lock(_mutex);

	if (_isDownloaded)
		return;

	URL url(shared_from_this());
	URLFetcher::fetchURL(url);

	if (blocking) {
		while(!_isDownloaded && !_hasFailed) {
			_condVar.wait(_mutex); // wait for notification
		}
		if (_hasFailed) {
			ERROR_COMMUNICATION(exc, _error);
//            exc.data = URL(shared_from_this());
			throw exc;
		}
		if (iequals(scheme(), "http")) {
			if (_statusCode.size() > 0 && strTo<int>(_statusCode) > 400) {
				ERROR_COMMUNICATION(exc, _error);
//                exc.data = URL(shared_from_this());
				if (_error.length() > 0)
					exc.data.compound["cause"] = Data(_error, Data::VERBATIM);
				throw exc;
			}
		}
	}
}

URLImpl::operator Data() const {
	Data data;
	data.compound["url"] = Data(std::string(*this), Data::VERBATIM);
	data.compound["host"] = Data(host(), Data::VERBATIM);
	data.compound["scheme"] = Data(scheme(), Data::VERBATIM);
	data.compound["path"] = Data(path(), Data::VERBATIM);
	data.compound["port"] = Data(port(), Data::INTERPRETED);
	data.compound["isAbsolute"] = Data(isAbsolute());
	if (_statusCode.length() > 0)
		data.compound["statusCode"] = Data(_statusCode, Data::VERBATIM);
	if (_statusMsg.length() > 0)
		data.compound["statusMsg"] = Data(_statusMsg, Data::VERBATIM);

	std::list<std::string> pathComps = pathComponents();
	std::list<std::string>::const_iterator pathIter = pathComps.begin();
	int index = 0;
	while(pathIter != pathComps.end()) {
		data.compound["pathComponent"].array.insert(std::make_pair(index++,Data(*pathIter, Data::VERBATIM)));
		pathIter++;
	}

	return data;
}


URLImpl::operator std::string() const {
	int charsRequired = 0;
	if (uriToStringCharsRequiredA((UriUriA*)_uri, &charsRequired) != URI_SUCCESS) {
		throw ErrorEvent("Cannot recompose URL");
	}
	charsRequired++;

	char * uriString;
	uriString = (char*)malloc(charsRequired * sizeof(char));
	if (uriString == NULL) {
		throw ErrorEvent("Malloc failed");
	}

	if (uriToStringA(uriString, (UriUriA*)_uri, charsRequired, NULL) != URI_SUCCESS) {
		free(uriString);
		throw ErrorEvent("Cannot recompose URL");
	}

	std::string recomposed(uriString);
	free(uriString);
	return recomposed;

}

URLFetcher::URLFetcher() {
	_isStarted = false;
	_envProxy = NULL;
	_multiHandle = curl_multi_init();

	// read proxy information from environment
	//	CURLOPT_PROXY;
	//	CURLOPT_PROXY_TRANSFER_MODE;
	//	CURLOPT_PROXYAUTH;
	//	CURLOPT_PROXYHEADER;
	//	CURLOPT_PROXYPASSWORD;
	//	CURLOPT_PROXYPORT;
	//	CURLOPT_PROXYTYPE;
	//	CURLOPT_PROXYUSERNAME;
	//	CURLOPT_PROXYUSERPWD;

	/*
	 see http://curl.haxx.se/libcurl/c/CURLOPT_PROXY.html
	 e.g. 'socks5://bob:marley@localhost:12345'
	 */
	_envProxy = getenv("USCXML_PROXY");

#if 0
	bool unsupported = false;
	CURLcode curlError;

	// exposed just in case
	char* envProxyTransferMode = getenv("USCXML_PROXY_TRANSFER_MODE");
	char* envProxyAuth = getenv("USCXML_PROXYAUTH");
	//	char* envProxyHeader = getenv("USCXML_PROXYHEADER"); // not available in older curl
	char* envProxyPassword = getenv("USCXML_PROXYPASSWORD");
	char* envProxyPort = getenv("USCXML_PROXYPORT");
	//	char* envProxyType = getenv("USCXML_PROXYTYPE"); // takes an int, have another look if needed
	char* envProxyUsername = getenv("USCXML_PROXYUSERNAME");
	char* envProxyUserPwd = getenv("USCXML_PROXYUSERPWD");

	/* Name of proxy to use. */
	if (envProxy)
		(curlError = curl_easy_setopt(_multiHandle, CURLOPT_PROXY, envProxy)) == CURLE_OK ||
		LOG(USCXML_ERROR) << "Cannot set curl proxy: " << curl_easy_strerror(curlError) << std::endl;

	/* set transfer mode (;type=<a|i>) when doing FTP via an HTTP proxy */
	if (envProxyTransferMode)
		(curlError = curl_easy_setopt(_multiHandle, CURLOPT_PROXY_TRANSFER_MODE, envProxyTransferMode)) == CURLE_OK ||
		LOG(USCXML_ERROR) << "Cannot set curl proxy transfer mode: " << curl_easy_strerror(curlError) << std::endl;

	/* Set this to a bitmask value to enable the particular authentications
	 methods you like. Use this in combination with CURLOPT_PROXYUSERPWD.
	 Note that setting multiple bits may cause extra network round-trips. */
	if (envProxyAuth)
		(curlError = curl_easy_setopt(_multiHandle, CURLOPT_PROXYAUTH, envProxyAuth)) == CURLE_OK ||
		LOG(USCXML_ERROR) << "Cannot set curl proxy authentication: " << curl_easy_strerror(curlError) << std::endl;

#if 0
	/* This points to a linked list of headers used for proxy requests only,
	 struct curl_slist kind */
	if (envProxyHeader && unsupported)
		(curlError = curl_easy_setopt(_multiHandle, CURLOPT_PROXYHEADER, envProxyHeader)) == CURLE_OK ||
		LOG(USCXML_ERROR) << "Cannot set curl proxy header: " << curl_easy_strerror(curlError) << std::endl;
#endif

	/* "name" and "pwd" to use with Proxy when fetching. */
	if (envProxyUsername)
		(curlError = curl_easy_setopt(_multiHandle, CURLOPT_PROXYUSERNAME, envProxyUsername)) == CURLE_OK ||
		LOG(USCXML_ERROR) << "Cannot set curl proxy username: " << curl_easy_strerror(curlError) << std::endl;
	if (envProxyPassword)
		(curlError = curl_easy_setopt(_multiHandle, CURLOPT_PROXYPASSWORD, envProxyPassword)) == CURLE_OK ||
		LOG(USCXML_ERROR) << "Cannot set curl proxy password: " << curl_easy_strerror(curlError) << std::endl;

	/* Port of the proxy, can be set in the proxy string as well with:
	 "[host]:[port]" */
	if (envProxyPort)
		(curlError = curl_easy_setopt(_multiHandle, CURLOPT_PROXYPORT, envProxyPort)) == CURLE_OK ||
		LOG(USCXML_ERROR) << "Cannot set curl proxy port: " << curl_easy_strerror(curlError) << std::endl;

#if 0
	/* indicates type of proxy. accepted values are CURLPROXY_HTTP (default),
	 CURLPROXY_SOCKS4, CURLPROXY_SOCKS4A and CURLPROXY_SOCKS5. */
	if (envProxyType && unsupported)
		(curlError = curl_easy_setopt(_multiHandle, CURLOPT_PROXYTYPE, envProxyType)) == CURLE_OK ||
		LOG(USCXML_ERROR) << "Cannot set curl proxy type: " << curl_easy_strerror(curlError) << std::endl;
#endif

	/* "user:password" to use with proxy. */
	if (envProxyUserPwd)
		(curlError = curl_easy_setopt(_multiHandle, CURLOPT_PROXYUSERPWD, envProxyUserPwd)) == CURLE_OK ||
		LOG(USCXML_ERROR) << "Cannot set curl proxy user password: " << curl_easy_strerror(curlError) << std::endl;
#endif

	start();
}

URLFetcher::~URLFetcher() {
	stop();
	curl_multi_cleanup(_multiHandle);
}

void URLFetcher::fetchURL(URL& url) {
	URLFetcher* instance = getInstance();
	std::lock_guard<std::recursive_mutex> lock(instance->_mutex);

	CURL* handle = url._impl->getCurlHandle();
	assert(handle != NULL);
	if (handle == NULL)
		return;

	if (instance->_handlesToURLs.find(handle) == instance->_handlesToURLs.end()) {
		CURLcode curlError;

		std::string fromURL(url);

		(curlError = curl_easy_setopt(handle, CURLOPT_URL, fromURL.c_str())) == CURLE_OK ||
		LOGD(USCXML_ERROR) << "Cannot set url to " << std::string(url) << ": " << curl_easy_strerror(curlError) << std::endl;

		//		(curlError = curl_easy_setopt(handle, CURLOPT_NOSIGNAL, 1)) == CURLE_OK ||
		//		LOG(USCXML_ERROR) << "Cannot set curl to ignore signals: " << curl_easy_strerror(curlError);

		//		(curlError = curl_easy_setopt(handle, CURLOPT_FORBID_REUSE, 1)) == CURLE_OK ||
		//		LOG(USCXML_ERROR) << "Cannot force noreuse: " << curl_easy_strerror(curlError);

		//		(curlError = curl_easy_setopt(handle, CURLOPT_VERBOSE, 1)) == CURLE_OK ||
		//		LOG(USCXML_ERROR) << "Cannot set verbose: " << curl_easy_strerror(curlError);

		(curlError = curl_easy_setopt(handle, CURLOPT_WRITEDATA, url._impl.get())) == CURLE_OK ||
		LOGD(USCXML_ERROR) << "Cannot register this as write userdata: " << curl_easy_strerror(curlError) << std::endl;

		(curlError = curl_easy_setopt(handle, CURLOPT_WRITEFUNCTION, URLImpl::writeHandler)) == CURLE_OK ||
		LOGD(USCXML_ERROR) << "Cannot set write callback: " << curl_easy_strerror(curlError) << std::endl;

		(curlError = curl_easy_setopt(handle, CURLOPT_HEADERFUNCTION, URLImpl::headerHandler)) == CURLE_OK ||
		LOGD(USCXML_ERROR) << "Cannot request header from curl: " << curl_easy_strerror(curlError) << std::endl;

		(curlError = curl_easy_setopt(handle, CURLOPT_HEADERDATA, url._impl.get())) == CURLE_OK ||
		LOGD(USCXML_ERROR) << "Cannot register this as header userdata: " << curl_easy_strerror(curlError) << std::endl;

		(curlError = curl_easy_setopt(handle, CURLOPT_SSL_VERIFYPEER, false)) == CURLE_OK ||
		LOGD(USCXML_ERROR) << "Cannot forfeit peer verification: " << curl_easy_strerror(curlError) << std::endl;

		(curlError = curl_easy_setopt(handle, CURLOPT_USERAGENT, "uscxml/" USCXML_VERSION)) == CURLE_OK ||
		LOGD(USCXML_ERROR) << "Cannot set our user agent string: " << curl_easy_strerror(curlError) << std::endl;

		(curlError = curl_easy_setopt(handle, CURLOPT_FOLLOWLOCATION, true)) == CURLE_OK ||
		LOGD(USCXML_ERROR) << "Cannot enable follow redirects: " << curl_easy_strerror(curlError) << std::endl;

		if (instance->_envProxy)
			(curlError = curl_easy_setopt(handle, CURLOPT_PROXY, instance->_envProxy)) == CURLE_OK ||
			LOGD(USCXML_ERROR) << "Cannot set curl proxy: " << curl_easy_strerror(curlError) << std::endl;

		if (url._impl->_requestType == URLRequestType::POST) {

			(curlError = curl_easy_setopt(handle, CURLOPT_POST, 1)) == CURLE_OK ||
			LOGD(USCXML_ERROR) << "Cannot set request type to post for " << std::string(url) << ": " << curl_easy_strerror(curlError) << std::endl;

			(curlError = curl_easy_setopt(handle, CURLOPT_COPYPOSTFIELDS, url._impl->_outContent.c_str())) == CURLE_OK ||
			LOGD(USCXML_ERROR) << "Cannot set post data " << std::string(url) << ": " << curl_easy_strerror(curlError) << std::endl;

			// Disable "Expect: 100-continue"
			//			curl_slist* disallowed_headers = 0;
			//			disallowed_headers = curl_slist_append(disallowed_headers, "Expect:");
			//			(curlError = curl_easy_setopt(handle, CURLOPT_HTTPHEADER, disallowed_headers)) == CURLE_OK ||
			//			LOG(USCXML_ERROR) << "Cannot disable Expect 100 header: " << curl_easy_strerror(curlError);

			struct curl_slist* headers = NULL;
			std::map<std::string, std::string>::iterator paramIter = url._impl->_outHeader.begin();
			while(paramIter != url._impl->_outHeader.end()) {
				//				char* key = curl_easy_escape(handle, paramIter->first.c_str(), paramIter->first.length());
				//				char* value = curl_easy_escape(handle, paramIter->second.c_str(), paramIter->second.length());

				const char* value = paramIter->second.c_str();

				char* header = (char*)malloc(paramIter->first.size() + strlen(value) + 3);
				sprintf(header,"%s: %s", paramIter->first.c_str(), value);
				headers = curl_slist_append(headers, header);
				free(header);
				//				curl_free(key);
				//				curl_free(value);
				paramIter++;
			}

			// Disable "Expect: 100-continue"
			headers = curl_slist_append(headers, "Expect:");
			instance->_handlesToHeaders[handle] = headers;

			(curlError = curl_easy_setopt(handle, CURLOPT_HTTPHEADER, headers)) == CURLE_OK ||
			LOGD(USCXML_ERROR) << "Cannot headers for " << std::string(url) << ": " << curl_easy_strerror(curlError) << std::endl;

//			curl_slist_free_all(headers);


		} else if (url._impl->_requestType == URLRequestType::GET) {
			(curlError = curl_easy_setopt(handle, CURLOPT_HTTPGET, 1)) == CURLE_OK ||
			LOGD(USCXML_ERROR) << "Cannot set request type to get for " << std::string(url) << ": " << curl_easy_strerror(curlError) << std::endl;
		}

		url._impl->downloadStarted();
		instance->_handlesToURLs[handle] = url;
		assert(instance->_handlesToURLs.size() > 0);

		curl_multi_add_handle(instance->_multiHandle, handle);
		instance->_condVar.notify_all();
	}
}

void URLFetcher::breakURL(URL& url) {
	URLFetcher* instance = getInstance();
	CURL* handle = url._impl->getCurlHandle();

	std::lock_guard<std::recursive_mutex> lock(instance->_mutex);
	if (instance->_handlesToURLs.find(handle) != instance->_handlesToURLs.end()) {
		url._impl->downloadFailed(CURLE_OK);
		curl_multi_remove_handle(instance->_multiHandle, handle);
		instance->_handlesToURLs.erase(handle);
	}
	if (instance->_handlesToHeaders.find(handle) != instance->_handlesToHeaders.end()) {
		curl_slist_free_all((struct curl_slist *)instance->_handlesToHeaders[handle]);
		instance->_handlesToHeaders.erase(handle);
	}
}

void URLFetcher::start() {
	std::lock_guard<std::recursive_mutex> lock(_mutex);
	if (!_isStarted) {
		_isStarted = true;
		_thread = new std::thread(URLFetcher::run, this);
	}
}

void URLFetcher::stop() {
	std::lock_guard<std::recursive_mutex> lock(_mutex);
	if (_isStarted) {
		_isStarted = false;
		_thread->join();
		delete _thread;
	}
}

void URLFetcher::run(void* instance) {
	URLFetcher* fetcher = (URLFetcher*)instance;
	while(fetcher->_isStarted) {
		fetcher->perform();
	}
	LOGD(USCXML_ERROR) << "URLFetcher thread stopped!" << std::endl;
}

void URLFetcher::perform() {

	CURLMsg *msg; /* for picking up messages with the transfer status */
	int msgsLeft; /* how many messages are left */
	int stillRunning;
	CURLMcode err;

	{
		std::lock_guard<std::recursive_mutex> lock(_mutex);
		if (_handlesToURLs.empty()) {
			_condVar.wait(_mutex);
		}
		err = curl_multi_perform(_multiHandle, &stillRunning);
		if (err != CURLM_OK) {
			LOGD(USCXML_WARN) << "curl_multi_perform: " << curl_multi_strerror(err) << std::endl;
		}
	}

	do {
		struct timeval timeout;
		int rc; /* select() return code */

		fd_set fdread, fdwrite, fdexcep;
		FD_ZERO(&fdread);
		FD_ZERO(&fdwrite);
		FD_ZERO(&fdexcep);

		int maxfd = -1;
		long curlTimeOut = -1;

		/* set a suitable timeout to play around with */
		timeout.tv_sec = 1;
		timeout.tv_usec = 0;

		{
			std::lock_guard<std::recursive_mutex> lock(_mutex);
			err = curl_multi_timeout(_multiHandle, &curlTimeOut);
			if (err != CURLM_OK) {
				LOGD(USCXML_WARN) << "curl_multi_timeout: " << curl_multi_strerror(err) << std::endl;
			}
			// select on windows return -1, but this will make progress, see
			// https://curl.haxx.se/mail/lib-2006-10/0100.html
			while(CURLM_CALL_MULTI_PERFORM == curl_multi_perform(_multiHandle, &stillRunning));
		}

		if(curlTimeOut >= 0) {
			timeout.tv_sec = curlTimeOut / 1000;
			if(timeout.tv_sec > 1) {
				timeout.tv_sec = 1;
			} else {
				timeout.tv_usec = (curlTimeOut % 1000) * 1000;
			}
		}

		/* get file descriptors from the transfers */
		{
			std::lock_guard<std::recursive_mutex> lock(_mutex);
			err = curl_multi_fdset(_multiHandle, &fdread, &fdwrite, &fdexcep, &maxfd);
			if (err != CURLM_OK) {
				LOGD(USCXML_WARN) << "curl_multi_fdset: " << curl_multi_strerror(err) << std::endl;
			}
		}

		rc = select(maxfd+1, &fdread, &fdwrite, &fdexcep, &timeout);

		switch(rc) {
		case -1: {
			/* select error */
#if 0
            // this is not an actual error - there was just nothing to process
#ifdef _WIN32
			char *s = NULL;
			FormatMessage(FORMAT_MESSAGE_ALLOCATE_BUFFER | FORMAT_MESSAGE_FROM_SYSTEM | FORMAT_MESSAGE_IGNORE_INSERTS,
			              NULL, WSAGetLastError(),
			              MAKELANGID(LANG_NEUTRAL, SUBLANG_DEFAULT),
			              (LPSTR)&s, 0, NULL);
			LOGD(USCXML_WARN) << "select: " << s << std::endl;
			LocalFree(s);
#endif
#endif
			break;
		}
		case 0: /* timeout */
		default: { /* action */
			std::lock_guard<std::recursive_mutex> lock(_mutex);
			err = curl_multi_perform(_multiHandle, &stillRunning);
			if (err != CURLM_OK) {
				LOGD(USCXML_WARN) << "curl_multi_perform: " << curl_multi_strerror(err) << std::endl;
			}
			break;
		}
		}

		{
			std::lock_guard<std::recursive_mutex> lock(_mutex);
			while ((msg = curl_multi_info_read(_multiHandle, &msgsLeft))) {
				if (msg->msg == CURLMSG_DONE) {
					switch (msg->data.result) {
					case CURLE_OK:
						_handlesToURLs[msg->easy_handle]._impl->downloadCompleted();
						err = curl_multi_remove_handle(_multiHandle, msg->easy_handle);
						if (err != CURLM_OK) {
							LOGD(USCXML_WARN) << "curl_multi_remove_handle: " << curl_multi_strerror(err) << std::endl;
						}

						break;
					default:
						_handlesToURLs[msg->easy_handle]._impl->downloadFailed(msg->data.result);
						err = curl_multi_remove_handle(_multiHandle, msg->easy_handle);
						if (err != CURLM_OK) {
							LOGD(USCXML_WARN) << "curl_multi_remove_handle: " << curl_multi_strerror(err) << std::endl;
						}
						break;

					}
					_handlesToURLs.erase(msg->easy_handle);
					curl_slist_free_all((struct curl_slist *)_handlesToHeaders[msg->easy_handle]);
					_handlesToHeaders.erase(msg->easy_handle);

				} else {
					LOGD(USCXML_ERROR) << "Curl reports info on unfinished download?!" << std::endl;
				}
			}
		}
	} while(stillRunning && _isStarted);
}

URLFetcher* URLFetcher::_instance = NULL;

URLFetcher* URLFetcher::getInstance() {
	if (_instance == NULL) {
		_instance = new URLFetcher();
	}
	return _instance;
}


}
