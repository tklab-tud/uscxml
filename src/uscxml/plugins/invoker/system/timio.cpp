#include "timio.h"
#include "uscxml/plugins/invoker/system/XmlBridgeInvoker.h"

namespace uscxml {

bool TimIO::connect2TIM() {
	struct addrinfo hints, *p;
	int rv;

	memset(&hints, 0, sizeof hints);
	hints.ai_family = PF_INET;
	hints.ai_socktype = SOCK_STREAM;

	if ((rv = getaddrinfo(_TIMaddr.c_str(), _TIMport.c_str(), &hints, &_servinfo)) != 0) {
		LOG(ERROR) << "Getaddrinfo: " << gai_strerror(rv);
		perror("Getaddrinfo:");
		return false;
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
		return false;
	}

	return true;
}

TimIO::TimIO(std::string ipaddr, std::string port) :
	_timCmd(), _timCmdId(), _timCmdWrite(), _TIMaddr(ipaddr), _TIMport(port)
{
	if (ipaddr.empty() || port.empty())
		exit(EXIT_FAILURE);

	if (!connect2TIM()) {
		LOG(ERROR) << "TIM Client: failed to connect to " << ipaddr << ":" << port;
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
	XmlBridgeInputEvents& bridgeInstance = XmlBridgeInputEvents::getInstance();

	tthread::lock_guard<tthread::recursive_mutex> lock(myobj->_mutex);

	struct timeval tv;
	tv.tv_sec = myobj->_defTimeout;
	tv.tv_usec = 0;  // Not init'ing this can cause strange errors
	setsockopt(myobj->_socketfd, SOL_SOCKET, SO_SNDTIMEO, &tv, sizeof(struct timeval));
	setsockopt(myobj->_socketfd, SOL_SOCKET, SO_RCVTIMEO, &tv, sizeof(struct timeval));

	int numbytes;

	LOG(INFO) << "Sending to socket " << myobj->_socketfd
		<< " the string: '" << myobj->_timCmd.front()
		<< "' with length " << myobj->_timCmd.front().length();

	while ((numbytes = send(myobj->_socketfd, myobj->_timCmd.front().c_str(),
			myobj->_timCmd.front().length(),
			MSG_MORE | MSG_NOSIGNAL)) != myobj->_timCmd.front().length()) {

		perror("TIM client: send error");
		if (errno == EPIPE) {
			if (!connect2TIM()) {
				bridgeInstance.handleTIMexception(TIM_ERROR);
				return;
			}
			/** If we lost the TCP connection we retry the send of data */
			continue;
		} else if (errno == EAGAIN || errno == EWOULDBLOCK) {
			LOG(ERROR) << "TIM client: command timeout";
			bridgeInstance.handleTIMexception(TIM_TIMEOUT);
			return;
		}
		bridgeInstance.handleTIMexception(TIM_ERROR);
		LOG(ERROR) << "TIM client: failed to send";
		return;
	}

	errno = 0;

	/**
	 * Function blocks until the full amount of message data can be returned
	 */
	int replylen;
	memset(myobj->_reply, 0, MAXTIMREPLYSIZE);
	if ((replylen = recv(myobj->_socketfd, myobj->_reply, MAXTIMREPLYSIZE, MSG_WAITALL)) == -1) {
		if (errno == EAGAIN || errno == EWOULDBLOCK) {
			LOG(ERROR) << "TIM client: command timeout";
			bridgeInstance.handleTIMexception(TIM_TIMEOUT);
			return;
		}
		perror("TIM client: recv error");
		LOG(ERROR) << "TIM client: ignoring SCXML send event";
		bridgeInstance.handleTIMexception(TIM_ERROR);
		return;
	}
	if (replylen == 0) {
		LOG(ERROR) << "TIM client: received zero-length message";
		bridgeInstance.handleTIMexception(TIM_ERROR);
		return;
	}

	LOG(INFO) << "Received reply from TIM: " << myobj->_reply;

	/** This function logs and reports errors internally */
	bridgeInstance.handleTIMreply(std::string(myobj->_reply));
}

}