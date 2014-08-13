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

#ifndef SOCKETCLIENT_H_9A0B2A88
#define SOCKETCLIENT_H_9A0B2A88

#include "uscxml/Common.h"              // for USCXML_API
#include "uscxml/concurrency/EventBase.h"
#include <string>
#include <sstream>
#include <map>
#include <set>

#ifdef _WIN32
#	include <winsock2.h>
#else
#	include <netinet/in.h> /* For sockaddr_in */
#endif
#include <cerrno>

#include "uscxml/concurrency/tinythread.h"  // for recursive_mutex, etc

extern "C" {
#include <event2/event.h>
#include <event2/buffer.h>
#include <event2/bufferevent.h>
}

namespace uscxml {

class USCXML_API Socket {
public:
	Socket(int domain, int type, int protocol);
	virtual ~Socket();

	void setBlockSizeRead(size_t size);
	static void parseAddress(const std::string& address, std::string& protocol, std::string& hostName, uint16_t& port);

protected:

	void setupSockAddr(const std::string& address, int port);

	evutil_socket_t _socketFD;

	tthread::recursive_mutex _mutex;
	size_t _blockSizeRead;
	struct sockaddr_in _sin;

	boost::shared_ptr<EventBase> _base;
};

class USCXML_API ServerSocket : public Socket {
public:
	class Connection {
	public:
		bool operator<(const Connection& other) const {
			return bufferEvent < other.bufferEvent;
		}

		struct bufferevent* bufferEvent;
		int fd;

		void reply(const char* data, size_t size);
	};

	ServerSocket(int domain, int type, int protocol);
	virtual ~ServerSocket();

	void listen(const std::string& address, int port);
	void listen(const std::string& address);
	virtual void readCallback(const char* data, size_t size, Connection& conn) {};


protected:
	void bind();
	static void acceptCallback(evutil_socket_t listener, short event, void *ctx);
	static void errorCallback(struct bufferevent *bev, short error, void *ctx);
	static void readCallback(struct bufferevent *bev, void *ctx);

	std::map<struct bufferevent*, Connection> _connections;
	struct event* _listenerEvent;

	static std::set<ServerSocket*> _instances;

};

class USCXML_API PacketServerSocket : public ServerSocket {
public:
	PacketServerSocket(int domain, int type, int protocol, const std::string& sep) : ServerSocket(domain, type, protocol), _sep(sep) {}
	virtual ~PacketServerSocket();

	void readCallback(const char* data, size_t size, Connection& conn);
	virtual void readCallback(const std::string& packet, Connection& conn) = 0;

protected:
	std::string _sep;
	std::map<Connection, std::stringstream*> _fragments;
};
	
class USCXML_API ClientSocket : public Socket {
public:
	ClientSocket(int domain, int type, int protocol);
	virtual ~ClientSocket();

	virtual void readCallback(const char* data, size_t size) {};
	void connect(const std::string& address, int port);
	void connect(const std::string& address);
	int write(const std::string& data);
	int write(const char* data, size_t size);


protected:
	static void readCallback(struct bufferevent *bev, void *ctx);
	static void errorCallback(struct bufferevent *bev, short error, void *ctx);

	struct bufferevent* _clientEvent;

};


}

#endif /* end of include guard: SOCKETCLIENT_H_9A0B2A88 */
