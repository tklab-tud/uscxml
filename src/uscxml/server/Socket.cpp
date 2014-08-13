/**
 *  @file
 *  @author     2012-2014 Stefan Radomski (stefan.radomski@cs.tu-darmstadt.de)
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

#include "Socket.h"

#include "uscxml/Message.h"             // for Data, Event
#include "uscxml/config.h"              // for OPENSSL_FOUND

#ifndef _WIN32
#include <sys/socket.h> /* For socket functions */
#include <arpa/inet.h> // inet_addr
#endif

#include <fcntl.h> /* For fcntl */
#include <iostream>

namespace uscxml {

// see: http://codepad.org/XRJAVg5m
Socket::Socket(int domain, int type, int protocol) {

	_base = EventBase::get("sockets");
	_blockSizeRead = 1024;

	if (!_base)
		throw std::runtime_error("Cannot get eventbase");

	_sin.sin_family = domain;
	_socketFD = socket(domain, type, protocol);

	if (_socketFD == -1)
		throw std::runtime_error(std::string("socket: ") + strerror(errno));
#ifndef WIN32
	{
		int one = 1;
		if (setsockopt(_socketFD, SOL_SOCKET, SO_REUSEADDR, &one, sizeof(one)) != 0) {
			throw std::runtime_error(std::string("setsockopt: ") + strerror(errno));
		}
	}
#endif

}

Socket::~Socket() {
	if (_socketFD > 0)
#ifdef WIN32
		closesocket(_socketFD);
#else
		close(_socketFD);
#endif
}

void Socket::setupSockAddr(const std::string& address, int port) {

	if (address == "*") {
		_sin.sin_addr.s_addr = 0;
	} else {
		struct hostent *he = NULL;
		if ( (he = gethostbyname(address.c_str()) ) != NULL ) {
			memcpy(&_sin.sin_addr, he->h_addr_list[0], he->h_length);
		} else {
			_sin.sin_addr.s_addr = inet_addr(address.c_str());
		}
		if (_sin.sin_addr.s_addr == INADDR_NONE)
			throw std::runtime_error(std::string("inet_addr: ") + strerror(errno));
	}

	_sin.sin_port = htons(port);
}

void Socket::setBlockSizeRead(size_t size) {
//	tthread::lock_guard<tthread::recursive_mutex> lock(_mutex);
	_blockSizeRead = size;
}

void Socket::parseAddress(const std::string& address, std::string& protocol, std::string& hostName, uint16_t& port) {
	// tcp://hostname:port
	size_t protEnd = address.find("://");
	if (protEnd != std::string::npos) {
		protocol = address.substr(0, protEnd);
		protEnd += 3;
	} else {
		protocol = "tcp";
		protEnd = 0;
	}
	
	size_t hostEnd = address.find(":", protEnd);
	if (hostEnd != std::string::npos) {
		hostName = address.substr(protEnd, hostEnd - protEnd);
		hostEnd += 1;
	} else {
		hostName = "127.0.0.1";
		hostEnd = protEnd;
	}

	if (hostEnd < address.size()) {
		port = strTo<uint16_t>(address.substr(hostEnd));
	} else {
		port = 0;
	}
}

	
ClientSocket::ClientSocket(int domain, int type, int protocol) : Socket(domain, type, protocol), _clientEvent(NULL) {
}


ClientSocket::~ClientSocket() {
	if (_clientEvent) {
		bufferevent_enable(_clientEvent, 0);
		bufferevent_free(_clientEvent);
	}
}

void ClientSocket::errorCallback(struct bufferevent *bev, short error, void *ctx) {
//	ClientSocket* instance = (ClientSocket*)ctx;
	//	tthread::lock_guard<tthread::recursive_mutex> lock(instance->_mutex);

	if (error & BEV_EVENT_READING) {
		std::cout << "ClientSocket: error encountered while reading" << std::endl;
	} else if (error & BEV_EVENT_WRITING) {
		std::cout << "ClientSocket: error encountered while writing" << std::endl;
	} else if (error & BEV_EVENT_EOF) {
		std::cout << "ClientSocket: eof file reached" << std::endl;
	} else if (error & BEV_EVENT_ERROR) {
		std::cout << "ClientSocket: unrecoverable error encountered" << std::endl;
	} else if (error & BEV_EVENT_TIMEOUT) {
		std::cout << "ClientSocket: user-specified timeout reached" << std::endl;
	} else if (error & BEV_EVENT_CONNECTED) {
		std::cout << "ClientSocket: connect operation finished" << std::endl;
	}

	//	bufferevent_free(bev);
}

void ClientSocket::connect(const std::string& address) {
	std::string _prot;
	std::string _address;
	uint16_t _port;
	parseAddress(address, _prot, _address, _port);
	connect(_address, _port);
}
	
void ClientSocket::connect(const std::string& address, int port) {
//	tthread::lock_guard<tthread::recursive_mutex> lock(_mutex);

	setupSockAddr(address, port);
	if(::connect(_socketFD, (struct sockaddr *)&_sin, sizeof _sin) != 0) {
		throw std::runtime_error(std::string("connect: ") + strerror(errno));
	}

	_clientEvent = bufferevent_socket_new(_base->base, _socketFD, BEV_OPT_THREADSAFE); //BEV_OPT_THREADSAFE);
	bufferevent_setcb(_clientEvent, ClientSocket::readCallback, NULL, ClientSocket::errorCallback, this);
	bufferevent_enable(_clientEvent, EV_READ|EV_WRITE);
}

int ClientSocket::write(const std::string& data) {
	return write(data.data(), data.size());
}
	
int ClientSocket::write(const char* data, size_t size) {
//	tthread::lock_guard<tthread::recursive_mutex> lock(_mutex);
	bufferevent_write(_clientEvent, data, size);
	return size;
}

void ClientSocket::readCallback(struct bufferevent *bev, void *ctx) {
	ClientSocket* instance = (ClientSocket*)ctx;
//	tthread::lock_guard<tthread::recursive_mutex> lock(instance->_mutex);

	int n;
	struct evbuffer* input;
	char* data = (char*)malloc(instance->_blockSizeRead);

	input = bufferevent_get_input(bev);
	
	while((n = evbuffer_remove(input, data, instance->_blockSizeRead)) > 0) {
		instance->readCallback(data, n);
	}
	free(data);
}

std::set<ServerSocket*> ServerSocket::_instances;

ServerSocket::ServerSocket(int domain, int type, int protocol) : Socket(domain, type, protocol), _listenerEvent(NULL) {
	_instances.insert(this);
}

ServerSocket::~ServerSocket() {
	tthread::lock_guard<tthread::recursive_mutex> lock(_mutex);

	std::map<struct bufferevent*, Connection>::iterator connIter = _connections.begin();
	while(connIter != _connections.end()) {
		bufferevent_enable(connIter->second.bufferEvent, 0);
		bufferevent_setcb(connIter->second.bufferEvent, NULL, NULL, NULL, 0);

		bufferevent_free(connIter->second.bufferEvent);
#ifdef WIN32
		closesocket(connIter->second.fd);
#else
		close(connIter->second.fd);
#endif

		connIter++;
	}

	if (_listenerEvent) {
		event_del(_listenerEvent);
		event_free(_listenerEvent);
	}

	_instances.erase(this);

}

void ServerSocket::errorCallback(struct bufferevent *bev, short error, void *ctx) {
	ServerSocket* instance = (ServerSocket*)ctx;
	tthread::lock_guard<tthread::recursive_mutex> lock(instance->_mutex);

	if (_instances.find(instance) == _instances.end())
		return;

	if (error & BEV_EVENT_READING || error & BEV_EVENT_WRITING) {
		// remote end close the connection
		tthread::lock_guard<tthread::recursive_mutex> lock(instance->_mutex);
		std::map<struct bufferevent*, Connection>::iterator conn = instance->_connections.find(bev);
		if (conn != instance->_connections.end()) {
			bufferevent_enable(conn->second.bufferEvent, 0);
			bufferevent_free(conn->second.bufferEvent);
#ifdef WIN32
			closesocket(conn->second.fd);
#else
			close(conn->second.fd);
#endif
			instance->_connections.erase(conn);
		}
	} else if (error & BEV_EVENT_EOF) {
		std::cout << "ServerSocket: eof file reached" << std::endl;
	} else if (error & BEV_EVENT_ERROR) {
		std::cout << "ServerSocket: unrecoverable error encountered" << std::endl;
	} else if (error & BEV_EVENT_TIMEOUT) {
		std::cout << "ServerSocket: user-specified timeout reached" << std::endl;
	} else if (error & BEV_EVENT_CONNECTED) {
		std::cout << "ServerSocket: connect operation finished" << std::endl;
	}
	//	bufferevent_free(bev);
}

void ServerSocket::readCallback(struct bufferevent *bev, void *ctx) {
	ServerSocket* instance = (ServerSocket*)ctx;
	tthread::lock_guard<tthread::recursive_mutex> lock(instance->_mutex);

	// instance is already gone
	if (_instances.find(instance) == _instances.end())
		return;

	size_t n;
	struct evbuffer* input;
	char* data = (char*)malloc(instance->_blockSizeRead);

	input = bufferevent_get_input(bev);
	while((n = evbuffer_remove(input, data, instance->_blockSizeRead)) > 0) {
		instance->readCallback(data, n, instance->_connections[bev]);
	}
	free(data);
}

void ServerSocket::bind() {
	if (::bind(_socketFD, (struct sockaddr*)&_sin, sizeof(_sin)) < 0) {
		throw std::runtime_error(std::string("bind: ") + strerror(errno));
	}
}

void ServerSocket::listen(const std::string& address) {
	std::string _prot;
	std::string _address;
	uint16_t _port;
	parseAddress(address, _prot, _address, _port);
	listen(_address, _port);
}

void ServerSocket::listen(const std::string& address, int port) {
//	tthread::lock_guard<tthread::recursive_mutex> lock(_mutex);
	setupSockAddr(address, port);
	bind();

	int reuseaddr_on = 1;
	setsockopt(_socketFD, SOL_SOCKET, SO_REUSEADDR, &reuseaddr_on, sizeof(reuseaddr_on));

	int flags = fcntl(_socketFD, F_GETFL);
	if (flags >= 0) {
		flags |= O_NONBLOCK;
		if (fcntl(_socketFD, F_SETFL, flags) < 0) {
			// could not set to non-blocj
		}
	}

	_listenerEvent = event_new(_base->base, _socketFD, EV_READ|EV_PERSIST, acceptCallback, (void*)this);
	/*XXX check it */
	event_add(_listenerEvent, NULL);

	if (::listen(_socketFD, 16)<0) {
		throw std::runtime_error(std::string("listen: ") + strerror(errno));
	}
}

void ServerSocket::acceptCallback(evutil_socket_t listener, short event, void *ctx) {
	ServerSocket* instance = (ServerSocket*)ctx;
//	tthread::lock_guard<tthread::recursive_mutex> lock(instance->_mutex);

	struct sockaddr_storage ss;
	socklen_t slen = sizeof(ss);
	int fd = accept(listener, (struct sockaddr*)&ss, &slen);
	if (fd < 0) {
		throw std::runtime_error(std::string("accept: ") + strerror(errno));
	} else if (fd > FD_SETSIZE) {
#ifdef WIN32
		closesocket(fd);
#else
		close(fd);
#endif

		throw std::runtime_error(std::string("accept: ") + strerror(errno));
	} else {
		struct bufferevent *bev;
		evutil_make_socket_nonblocking(fd);
		bev = bufferevent_socket_new(instance->_base->base, fd, BEV_OPT_THREADSAFE); //BEV_OPT_THREADSAFE
		bufferevent_setcb(bev, ServerSocket::readCallback, NULL, ServerSocket::errorCallback, ctx);
		bufferevent_enable(bev, EV_READ|EV_WRITE);

		instance->_connections[bev].bufferEvent = bev;
		instance->_connections[bev].fd = fd;
	}
}

void ServerSocket::Connection::reply(const char* data, size_t size) {
	bufferevent_write(bufferEvent, data, size);
}

void PacketServerSocket::readCallback(const char* data, size_t size, Connection& conn) {
	std::stringstream& fragment = _fragments[conn];
	fragment << std::string(data, size);
	
	size_t startPos = 0;
	size_t endPos;
	const std::string& buffer = fragment.str();
	while((endPos = buffer.find(_sep, startPos)) != std::string::npos) {
//		std::cout << ">" << buffer.substr(startPos, endPos - startPos) << "<" << std::endl;
		readCallback(buffer.substr(startPos, endPos - startPos), conn);
		startPos = endPos + _sep.size();
	}
	if (startPos != 0 && startPos < buffer.size() + 1) {
		std::string rest = buffer.substr(startPos);
		fragment.str(std::string());
		fragment.clear();
		fragment << rest;
	}
}

}
