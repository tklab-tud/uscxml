#include <algorithm>
#include <assert.h>
#include <iostream>
#include <fstream>

#include <glog/logging.h>
#include <boost/algorithm/string.hpp>

#include <stdio.h>
#include <string.h>
#ifndef WIN32
#include <sys/time.h>
#endif
#include <stdlib.h>
#include <errno.h>

#include "uscxml/Common.h"
#include "URL.h"

#include "uscxml/config.h"

#include <stdio.h>  /* defines FILENAME_MAX */
#ifdef _WIN32
#include <fcntl.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <io.h>
#include <direct.h>
#define getcwd _getcwd
#else
#include <unistd.h>
#endif

#include <cstdlib> // mkstemp
#ifdef HAS_UNISTD_H
#include <unistd.h>  // mkstemp legacy
#endif

namespace uscxml {

URLImpl::~URLImpl() {
	if (_localFile.length() > 0)
		remove(_localFile.c_str());
}

const bool URLImpl::toAbsoluteCwd() {
	char currPath[FILENAME_MAX];
	if (!getcwd(currPath, sizeof(currPath))) {
		return false;
	}
	currPath[sizeof(currPath) - 1] = '\0'; /* not really required */
	return toAbsolute(std::string("file://" + std::string(currPath) + "/"));
}

std::string URLImpl::getLocalFilename(const std::string& suffix) {
	if (_localFile.length() > 0)
		return _localFile;

	if (_uri.scheme().compare("file") == 0)
		return _uri.path();

	// try hard to find a temporary directory
	const char* tmpDir = NULL;
	if (tmpDir == NULL)
		tmpDir = getenv("TMPDIR");
	if (tmpDir == NULL)
		tmpDir = getenv("TMP");
	if (tmpDir == NULL)
		tmpDir = getenv("TEMP");
	if (tmpDir == NULL)
		tmpDir = getenv("USERPROFILE");
	if (tmpDir == NULL)
		tmpDir = "/tmp";

	char* tmpl = (char*)malloc(strlen(tmpDir) + 11 + suffix.length());
	char* writePtr = tmpl;
	memcpy(writePtr, tmpDir, strlen(tmpDir));
	writePtr += strlen(tmpDir);
	memcpy(writePtr, "scxmlXXXXXX", 11);
	writePtr += 11;
	memcpy(writePtr, suffix.c_str(), suffix.length());
	writePtr += suffix.length();
	tmpl[writePtr - tmpl] = 0;

#ifdef _WIN32
	_mktemp_s(tmpl, strlen(tmpl) + 1);
	int fd = _open(tmpl, _O_CREAT, _S_IREAD | _S_IWRITE);
#else
	int fd = mkstemps(tmpl, suffix.length());
#endif
	if (fd < 0) {
		LOG(ERROR) << "mkstemp: " << strerror(errno) << std::endl;
		return "";
	}
#ifdef WIN32
	_close(fd);
#else
	close(fd);
#endif
	return std::string(tmpl);
}

boost::shared_ptr<URLImpl> URLImpl::toLocalFile(const std::string& content, const std::string& suffix) {
	boost::shared_ptr<URLImpl> urlImpl = boost::shared_ptr<URLImpl>(new URLImpl());
	urlImpl->_localFile = urlImpl->getLocalFilename(suffix);
	urlImpl->_uri = std::string("file://") + urlImpl->_localFile;

	std::ofstream file(urlImpl->_localFile.c_str(), std::ios_base::out);
	if(file.is_open()) {
		file << content;
		file.close();
	} else {
		return boost::shared_ptr<URLImpl>();
	}

	return urlImpl;
}

const bool URLImpl::toAbsolute(const std::string& baseUrl) {
	if (_uri.is_absolute())
		return true;
	_uri = Arabica::io::URI(baseUrl, _uri.as_string());
	if (!_uri.is_absolute())
		return false;
	return true;
}

const std::string URLImpl::asLocalFile(const std::string& suffix, bool reload) {
	// this is already a local file
	if (_uri.scheme().compare("file") == 0)
		return _uri.path();

	if (_localFile.length() > 0 && !reload)
		return _localFile;

	if (_localFile.length() > 0)
		remove(_localFile.c_str());

	_localFile = getLocalFilename(suffix);

	std::ofstream file(_localFile.c_str(), std::ios_base::out);
	if(file.is_open()) {
		file << URL(this->shared_from_this());
		file.close();
	} else {
		_localFile = "";
	}

	return _localFile;
}

std::ostream & operator<<(std::ostream & stream, const URL& url) {

	std::string urlString = url.asString();
	std::string fileURL = "file://";

	// strip file:// to support relative filenames
	if(urlString.substr(0, fileURL.size()) == fileURL) {
		urlString = urlString.substr(fileURL.size());
#ifdef _WIN32
		urlString = urlString.substr(0,1) + ":" + urlString.substr(1);
//		std::replace( urlString.begin(), urlString.end(), '/', '\\');
#endif
	}
//	LOG(ERROR) << "Trying to open " << urlString;
	URL_FILE *handle = url_fopen(urlString.c_str(), "r");

	if(!handle) {
		LOG(ERROR) << "Cannot open URL " << url.asString();
		return stream;
	}

	int nread;
	char buffer[256];

	do {
		nread = url_fread(buffer, 1,sizeof(buffer), handle);
		stream.write(buffer, nread);
	} while(nread);

	url_fclose(handle);
	return stream;
}

/* we use a global one for convenience */
CURLM *multi_handle;

/* curl calls this routine to get more data */
static size_t write_callback(char *buffer,
                             size_t size,
                             size_t nitems,
                             void *userp) {
	char *newbuff;
	size_t rembuff;

	URL_FILE *url = (URL_FILE *)userp;
	size *= nitems;

	rembuff=url->buffer_len - url->buffer_pos; /* remaining space in buffer */

	if(size > rembuff) {
		/* not enough space in buffer */
		newbuff=(char*)realloc(url->buffer,url->buffer_len + (size - rembuff));
		if(newbuff==NULL) {
			fprintf(stderr,"callback buffer grow failed\n");
			size=rembuff;
		} else {
			/* realloc suceeded increase buffer size*/
			url->buffer_len+=size - rembuff;
			url->buffer=newbuff;
		}
	}

	memcpy(&url->buffer[url->buffer_pos], buffer, size);
	url->buffer_pos += size;

	return size;
}

/* use to attempt to fill the read buffer up to requested number of bytes */
static int fill_buffer(URL_FILE *file, size_t want) {
	fd_set fdread;
	fd_set fdwrite;
	fd_set fdexcep;
	struct timeval timeout;
	int rc;

	/* only attempt to fill buffer if transactions still running and buffer
	 * doesnt exceed required size already
	 */
	if((!file->still_running) || (file->buffer_pos > want))
		return 0;

	/* attempt to fill buffer */
	do {
		int maxfd = -1;
		long curl_timeo = -1;

		FD_ZERO(&fdread);
		FD_ZERO(&fdwrite);
		FD_ZERO(&fdexcep);

		/* set a suitable timeout to fail on */
		timeout.tv_sec = 60; /* 1 minute */
		timeout.tv_usec = 0;

		curl_multi_timeout(multi_handle, &curl_timeo);
		if(curl_timeo >= 0) {
			timeout.tv_sec = curl_timeo / 1000;
			if(timeout.tv_sec > 1)
				timeout.tv_sec = 1;
			else
				timeout.tv_usec = (curl_timeo % 1000) * 1000;
		}

		/* get file descriptors from the transfers */
		curl_multi_fdset(multi_handle, &fdread, &fdwrite, &fdexcep, &maxfd);

		/* In a real-world program you OF COURSE check the return code of the
		   function calls.  On success, the value of maxfd is guaranteed to be
		   greater or equal than -1.  We call select(maxfd + 1, ...), specially
		   in case of (maxfd == -1), we call select(0, ...), which is basically
		   equal to sleep. */

		rc = select(maxfd+1, &fdread, &fdwrite, &fdexcep, &timeout);

		switch(rc) {
		case -1:
			/* select error */
			break;

		case 0:
		default:
			/* timeout or readable/writable sockets */
			curl_multi_perform(multi_handle, &file->still_running);
			break;
		}
	} while(file->still_running && (file->buffer_pos < want));
	return 1;
}

/* use to remove want bytes from the front of a files buffer */
static int use_buffer(URL_FILE *file,int want) {
	/* sort out buffer */
	if((file->buffer_pos - want) <=0) {
		/* ditch buffer - write will recreate */
		if(file->buffer)
			free(file->buffer);

		file->buffer=NULL;
		file->buffer_pos=0;
		file->buffer_len=0;
	} else {
		/* move rest down make it available for later */
		memmove(file->buffer,
		        &file->buffer[want],
		        (file->buffer_pos - want));

		file->buffer_pos -= want;
	}
	return 0;
}

URL_FILE *url_fopen(const char *url,const char *operation) {
	/* this code could check for URLs or types in the 'url' and
	   basicly use the real fopen() for standard files */

	URL_FILE *file;
	(void)operation;

	file = (URL_FILE*)malloc(sizeof(URL_FILE));
	if(!file)
		return NULL;

	memset(file, 0, sizeof(URL_FILE));

	if((file->handle.file=fopen(url,operation)))
		file->type = CFTYPE_FILE; /* marked as URL */

	else {
		file->type = CFTYPE_CURL; /* marked as URL */
		file->handle.curl = curl_easy_init();

		curl_easy_setopt(file->handle.curl, CURLOPT_URL, url);
		curl_easy_setopt(file->handle.curl, CURLOPT_WRITEDATA, file);
		curl_easy_setopt(file->handle.curl, CURLOPT_VERBOSE, 0L);
		curl_easy_setopt(file->handle.curl, CURLOPT_WRITEFUNCTION, write_callback);

		if(!multi_handle)
			multi_handle = curl_multi_init();

		curl_multi_add_handle(multi_handle, file->handle.curl);

		/* lets start the fetch */
		curl_multi_perform(multi_handle, &file->still_running);

		if((file->buffer_pos == 0) && (!file->still_running)) {
			/* if still_running is 0 now, we should return NULL */

			/* make sure the easy handle is not in the multi handle anymore */
			curl_multi_remove_handle(multi_handle, file->handle.curl);

			/* cleanup */
			curl_easy_cleanup(file->handle.curl);

			free(file);

			file = NULL;
		}
	}
	return file;
}

int url_fclose(URL_FILE *file) {
	int ret=0;/* default is good return */

	switch(file->type) {
	case CFTYPE_FILE:
		ret=fclose(file->handle.file); /* passthrough */
		break;

	case CFTYPE_CURL:
		/* make sure the easy handle is not in the multi handle anymore */
		curl_multi_remove_handle(multi_handle, file->handle.curl);

		/* cleanup */
		curl_easy_cleanup(file->handle.curl);
		break;

	default: /* unknown or supported type - oh dear */
		ret=EOF;
		errno=EBADF;
		break;
	}

	if(file->buffer)
		free(file->buffer);/* free any allocated buffer space */

	free(file);

	return ret;
}

int url_feof(URL_FILE *file) {
	int ret=0;

	switch(file->type) {
	case CFTYPE_FILE:
		ret=feof(file->handle.file);
		break;

	case CFTYPE_CURL:
		if((file->buffer_pos == 0) && (!file->still_running))
			ret = 1;
		break;

	default: /* unknown or supported type - oh dear */
		ret=-1;
		errno=EBADF;
		break;
	}
	return ret;
}

size_t url_fread(void *ptr, size_t size, size_t nmemb, URL_FILE *file) {
	size_t want;

	switch(file->type) {
	case CFTYPE_FILE:
		want=fread(ptr,size,nmemb,file->handle.file);
		break;

	case CFTYPE_CURL:
		want = nmemb * size;

		fill_buffer(file,want);

		/* check if theres data in the buffer - if not fill_buffer()
		 * either errored or EOF */
		if(!file->buffer_pos)
			return 0;

		/* ensure only available data is considered */
		if(file->buffer_pos < want)
			want = file->buffer_pos;

		/* xfer data to caller */
		memcpy(ptr, file->buffer, want);

		use_buffer(file,want);

		want = want / size;     /* number of items */
		break;

	default: /* unknown or supported type - oh dear */
		want=0;
		errno=EBADF;
		break;

	}
	return want;
}

char *url_fgets(char *ptr, size_t size, URL_FILE *file) {
	size_t want = size - 1;/* always need to leave room for zero termination */
	size_t loop;

	switch(file->type) {
	case CFTYPE_FILE:
		ptr = fgets(ptr,size,file->handle.file);
		break;

	case CFTYPE_CURL:
		fill_buffer(file,want);

		/* check if theres data in the buffer - if not fill either errored or
		 * EOF */
		if(!file->buffer_pos)
			return NULL;

		/* ensure only available data is considered */
		if(file->buffer_pos < want)
			want = file->buffer_pos;

		/*buffer contains data */
		/* look for newline or eof */
		for(loop=0; loop < want; loop++) {
			if(file->buffer[loop] == '\n') {
				want=loop+1;/* include newline */
				break;
			}
		}

		/* xfer data to caller */
		memcpy(ptr, file->buffer, want);
		ptr[want]=0;/* allways null terminate */

		use_buffer(file,want);

		break;

	default: /* unknown or supported type - oh dear */
		ptr=NULL;
		errno=EBADF;
		break;
	}

	return ptr;/*success */
}

void url_rewind(URL_FILE *file) {
	switch(file->type) {
	case CFTYPE_FILE:
		rewind(file->handle.file); /* passthrough */
		break;

	case CFTYPE_CURL:
		/* halt transaction */
		curl_multi_remove_handle(multi_handle, file->handle.curl);

		/* restart */
		curl_multi_add_handle(multi_handle, file->handle.curl);

		/* ditch buffer - write will recreate - resets stream pos*/
		if(file->buffer)
			free(file->buffer);

		file->buffer=NULL;
		file->buffer_pos=0;
		file->buffer_len=0;

		break;

	default: /* unknown or supported type - oh dear */
		break;
	}
}

}