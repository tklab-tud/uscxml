#include "uscxml/config.h"
#include "uscxml/server/Socket.h"
#include <iostream>

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

	if (0) {
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