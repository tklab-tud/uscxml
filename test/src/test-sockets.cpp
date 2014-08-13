#include "uscxml/config.h"
#include "uscxml/Convenience.h"
#include "uscxml/server/Socket.h"
#include <iostream>
#include <stdexcept>

#include <event2/event.h>
#include "event2/thread.h"

#ifdef HAS_SIGNAL_H
#include <signal.h>
#endif

#include "uscxml/concurrency/tinythread.h"

using namespace uscxml;

class TestServer : public ServerSocket {
public:
	TestServer(int domain, int type, int protocol) : ServerSocket(domain, type, protocol) {}
	virtual void readCallback(const char* data, size_t size, Connection& conn) {
		std::string content(data, size);
//		std::cout << "Server got: " << content << std::endl;
		std::string urghs("hi!");
		conn.reply(urghs.data(), urghs.size());
	};
};

int packetSeq = 0;

class LogServer : public ServerSocket {
public:
	LogServer(int domain, int type, int protocol) : ServerSocket(domain, type, protocol) {}
	virtual void readCallback(const char* data, size_t size, Connection& conn) {
		std::string content(data, size);
		std::cout << "Server got: " << content << std::endl;
	};
};

class CountingPacketServer : public PacketServerSocket {
public:
	CountingPacketServer(int domain, int type, int protocol, const std::string& sep) : PacketServerSocket(domain, type, protocol, sep) {}
	virtual void readCallback(const std::string& packet, Connection& conn) {
//		std::cout << "-- " << packet << std::endl;
		size_t seq = strTo<size_t>(packet);
		assert(seq == packetSeq);
		packetSeq++;
	};
};

class TestClient : public ClientSocket {
public:
	TestClient(int domain, int type, int protocol) : ClientSocket(domain, type, protocol) {}
	virtual void readCallback(const char* data, size_t size) {
		std::string content(data, size);
	};
};

int main(int argc, char** argv) {

#if defined(HAS_SIGNAL_H) && !defined(WIN32)
	signal(SIGPIPE, SIG_IGN);
#endif

#ifndef _WIN32
	evthread_use_pthreads();
#else
	evthread_use_windows_threads();
#endif

	if (1) {
		packetSeq = 0;
		CountingPacketServer server(PF_INET, SOCK_STREAM, 0, std::string("tadaa!"));
//		LogServer server(PF_INET, SOCK_STREAM, 0);
		server.listen("*", 1235);
		server.setBlockSizeRead(1);
		
		TestClient client(PF_INET, SOCK_STREAM, 0);
		client.connect("127.0.0.1", 1235);
		
		int iterations = 1000;
		std::stringstream contentSS;
		for (int i = 0; i < iterations; i++) {
			contentSS << toStr(i);
			contentSS << "tadaa!";
		}
		client.write(contentSS.str());

		while(packetSeq != iterations)
			tthread::this_thread::sleep_for(tthread::chrono::milliseconds(20));
	}

	if (1) {
		packetSeq = 0;
		CountingPacketServer server(PF_INET, SOCK_STREAM, 0, std::string("\0", 1));
		server.listen("*", 1235);
		
		TestClient client(PF_INET, SOCK_STREAM, 0);
		client.connect("127.0.0.1", 1235);

		int iterations = 1000;
		for (int i = 0; i < iterations; i++) {
			client.write(toStr(i));
			client.write("\0", 1);
		}

		while(packetSeq != iterations)
			tthread::this_thread::sleep_for(tthread::chrono::milliseconds(20));
	}
	
	exit(0);
	
	if (1) {
		// start server socket and connect
		int iterations = 100;

		TestServer server(PF_INET, SOCK_STREAM, 0);
		try {
			server.listen("*", 1234);

			while(iterations--) {
				std::cout << iterations << std::endl;
				TestClient client(PF_INET, SOCK_STREAM, 0);
				client.connect("127.0.0.1", 1234);

				std::string hello("hello");
				client.write(hello.data(), hello.size());

				tthread::this_thread::sleep_for(tthread::chrono::milliseconds(20));
			}

		} catch (std::runtime_error e) {
			std::cout << e.what() << std::endl;
		}
	}

	{
		// connect client to server and kill server
		int iterations = 100;

		try {

			while(iterations--) {
				std::cout << iterations << std::endl;
				TestServer* server = new TestServer(PF_INET, SOCK_STREAM, 0);
				server->listen("*", 1236 + iterations);

				TestClient client(PF_INET, SOCK_STREAM, 0);
				client.connect("127.0.0.1", 1236 + iterations);

				std::string hello("hello");
				client.write(hello.data(), hello.size());

				delete server;

				tthread::this_thread::sleep_for(tthread::chrono::milliseconds(20));
			}

		} catch (std::runtime_error e) {
			std::cout << e.what() << std::endl;
		}

	}
}