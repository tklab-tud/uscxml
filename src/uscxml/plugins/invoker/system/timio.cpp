#include "timio.h"
#include "uscxml/plugins/invoker/system/XmlBridgeInvoker.h"

namespace uscxml {

TimIO::TimIO(std::string ipaddr, std::string port) :
	_timCmds(), _timCmdIds()
{
	if (ipaddr.empty() || port.empty())
		exit(EXIT_FAILURE);

	struct addrinfo hints, *p;
	int rv;

	memset(&hints, 0, sizeof hints);
	hints.ai_family = PF_INET;
	hints.ai_socktype = SOCK_STREAM;

	if ((rv = getaddrinfo(ipaddr.c_str(), port.c_str(), &hints, &_servinfo)) != 0) {
		LOG(ERROR) << "Getaddrinfo: " << gai_strerror(rv);
		perror("Getaddrinfo:");
		exit(EXIT_FAILURE);
	}

	// loop through all the results and connect to the first we can
	for (p = _servinfo; p != NULL; p = p->ai_next) {
		if ((_socketfd = socket(p->ai_family, p->ai_socktype,
				p->ai_protocol)) == -1) {
			perror("TIM Client: socket");
			continue;
		}

		if (connect(_socketfd, p->ai_addr, p->ai_addrlen) == -1) {
			close(_socketfd);
			perror("TIM Client: connect");
			continue;
		}
		break;
	}

	if (p == NULL) {
		freeaddrinfo(_servinfo);
		LOG(ERROR) << "TIM Client: failed to connect";
		exit(EXIT_FAILURE);
	}

	_reply = (char*)calloc(1, MAXTIMREPLYSIZE);
	if (_reply == NULL) {
		freeaddrinfo(_servinfo);
		LOG(ERROR) << "TIM Client: failed to allocate _reply memory";
		exit(EXIT_FAILURE);
	}

	XmlBridgeInputEvents& bridgeInstance = XmlBridgeInputEvents::getInstance();
	bridgeInstance.registerTimio(this);
}

TimIO::~TimIO()
{
	freeaddrinfo(_servinfo);
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

	/** Potential blocking call */
	while ((numbytes = send(myobj->_socketfd, myobj->_timCmds.front().c_str(),
			myobj->_timCmds.front().length(), MSG_MORE | MSG_NOSIGNAL)) == -1) {
		perror("TIM client: send error");
		if (errno == EPIPE) {
			if (connect(myobj->_socketfd, myobj->_servinfo->ai_addr,
				myobj->_servinfo->ai_addrlen) == -1) {
					close(myobj->_socketfd);
					perror("TIM Client: connect");
					return;
			}
			continue;
		} else {
			LOG(ERROR) << "client: failed to connect: ";
			return;
		}
	}
	if (numbytes != myobj->_timCmds.front().length()) {
		perror("TIM client: sent incomplete message");
		LOG(ERROR) << "TIM client: ignoring SCXML send event";
		return;
	}

	/**
	 * Function blocks until the full amount of message data can be returned
	 *
	 * Should we close the stream after recv?
	 */
	int replylen;
	memset(myobj->_reply, 0, MAXTIMREPLYSIZE);
	if ((replylen = recv(myobj->_socketfd, myobj->_reply, MAXTIMREPLYSIZE, MSG_WAITALL)) == -1) {
		perror("TIM client: recv error");
		LOG(ERROR) << "TIM client: ignoring SCXML send event";
		return;
	}
	if (replylen == 0) {
		LOG(ERROR) << "TIM client: received zero-length message";
		LOG(ERROR) << "TIM client: ignoring SCXML send event";
		return;
	}

	LOG(INFO) << "Received reply from TIM: " << myobj->_reply;

	XmlBridgeInputEvents& bridgeInstance = XmlBridgeInputEvents::getInstance();
	bridgeInstance.handleTIMreply(myobj->_timCmdIds.front(), std::string(myobj->_reply));
}

}