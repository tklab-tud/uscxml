#include "timio.h"
#include "uscxml/plugins/invoker/system/XmlBridgeInvoker.h"

namespace uscxml {

TimIO::TimIO(std::string ipaddr, std::string port) :
	_timCmds(), _timCmdIds(), _thread(NULL), _reply(NULL)
{
	if (ipaddr.empty() || port.empty())
		exit(EXIT_FAILURE);

	struct addrinfo hints, *servinfo, *p;
	int rv;

	memset(&hints, 0, sizeof hints);
	hints.ai_family = PF_INET;
	hints.ai_socktype = SOCK_STREAM;

	if ((rv = getaddrinfo(ipaddr.c_str(), port.c_str(), &hints, &servinfo)) != 0) {
		LOG(ERROR) << "Getaddrinfo: " << gai_strerror(rv);
		exit(EXIT_FAILURE);
	}

	// loop through all the results and connect to the first we can
	for (p = servinfo; p != NULL; p = p->ai_next) {
		if ((_socketfd = socket(p->ai_family, p->ai_socktype,
				p->ai_protocol)) == -1) {
			perror("client: socket");
			continue;
		}

		if (connect(_socketfd, p->ai_addr, p->ai_addrlen) == -1) {
			close(_socketfd);
			perror("client: connect");
			continue;
		}
		break;
	}

	if (p == NULL) {
		LOG(ERROR) << "client: failed to connect: " << gai_strerror(rv);
		exit(EXIT_FAILURE);
	}

	freeaddrinfo(servinfo);

	_reply = (char*)calloc(1, MAXDATASIZE);
	if (_reply == NULL) {
		LOG(ERROR) << "client: failed to allocate _reply memory";
		exit(EXIT_FAILURE);
	}

	XmlBridgeInputEvents& bridgeInstance = XmlBridgeInputEvents::getInstance();
	bridgeInstance.registerTimio(this);
}

TimIO::~TimIO()
{
	close(_socketfd);
	free(_reply);
	if (_thread) {
		_thread->join();
		delete _thread;
	}
}

void TimIO::client(void *instance) {
	TimIO* myobj = (TimIO*)instance;
	tthread::lock_guard<tthread::recursive_mutex> lock(myobj->_mutex);

	int numbytes;

	LOG(INFO) << "Sending to socket " << myobj->_socketfd
		<< " the string: '" << myobj->_timCmds.front().c_str()
		<< "' with length " << myobj->_timCmds.front().length();

	/**  TODO: Check if connection is still alive and the server had not closed it
	 *	If yes, set a timeout end reconnect */

	/** Potential blocking call */
	if ((numbytes = send(myobj->_socketfd, myobj->_timCmds.front().c_str(),
			myobj->_timCmds.front().length(), 0)) == -1) {
		perror("TIM client: send error");
		LOG(ERROR) << "TIM client: send error";
		return;
	}

	if (numbytes != myobj->_timCmds.front().length()) {
		LOG(ERROR) << "TIM client: sent an incomplete message";
		return;
	}

	/**
	 * Function block until the full amount of message data can be returned
	 *
	 * Should we close the stream after recv?
	 */
	int replylen;
	memset(myobj->_reply, 0, MAXDATASIZE);
	if ((replylen = recv(myobj->_socketfd, myobj->_reply, MAXDATASIZE, MSG_WAITALL)) == -1) {
		perror("TIM client: recv error");
		LOG(ERROR) << "TIM client: recv error";
		return;
	}

	if (replylen == 0) {
		LOG(ERROR) << "TIM client: received zero-length message";
		return;
	}

	LOG(INFO) << "Received reply : " << myobj->_reply;

	XmlBridgeInputEvents& bridgeInstance = XmlBridgeInputEvents::getInstance();
	bridgeInstance.handleTIMreply(myobj->_timCmdIds.front(), std::string(myobj->_reply));
}

}