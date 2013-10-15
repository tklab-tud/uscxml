#ifndef TIMIO_H
#define TIMIO_H

#include <iostream>
#include <cstring>
#include <queue>
#include <sys/socket.h>
#include <netdb.h>
#include <bsd/string.h>

#include "XmlBridgeInvoker.h"

namespace uscxml {

#define MAXDATASIZE	2000
#define DEF_TIMADDR	"127.0.0.1"
#define DEF_TIMPORT	3200

class TimIO
{
public:
	TimIO(std::string ipaddr, std::string port);
	~TimIO();

private:
	static void client(void *instance);

	std::queue<std::string> _timCmds;
	std::queue<char> _timCmdIds;

	char * _reply;

	int _socketfd ; // The socket descriptor

	tthread::thread* _thread;
	tthread::recursive_mutex _mutex;
};

}
#endif // TIMIO_H
