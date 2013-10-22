#ifndef TIMIO_H
#define TIMIO_H

#include <iostream>
#include <cstring>
#include <queue>
#include <sys/socket.h>
#include <netdb.h>
#include <bsd/string.h>
#include "uscxml/concurrency/tinythread.h"

namespace uscxml {

#define MAXTIMREPLYSIZE		2000
#define DEF_TIMADDR		"127.0.0.1"
#define DEF_TIMPORT		"3200"

class TimIO
{
public:
	TimIO(std::string ipaddr, std::string port);
	~TimIO();

	std::queue<std::string> _timCmds;
	std::queue<char> _timCmdIds;

	tthread::thread* _thread;

	static void client(void *instance);
private:
	char* _reply;
	int _socketfd ; // The socket descriptor
	struct addrinfo *_servinfo;

	tthread::recursive_mutex _mutex;
};

}
#endif // TIMIO_H
