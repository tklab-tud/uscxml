/*
 * Use is subject to license terms.
 * Copyright (c) 2013, Ajile di Antonio Iudici. All rights reserved.
 *	<antonio.iudici@ajile.it>
 *	<enrico.papi@ajile.it>
 */

#ifndef TIMIO_H
#define TIMIO_H

#include <iostream>
#include <cstring>
#include <queue>
#include <sys/socket.h>
#include <netdb.h>
#include "uscxml/concurrency/tinythread.h"

namespace uscxml {

#define MAXTIMREPLYSIZE     20000
#define DEF_TIMADDR         "127.0.0.1"
#define DEF_TIMPORT         "3000"

/**
 * @brief Implementa un TCP client in comunicazione con il TIM
 */
class TimIO
{
public:
	TimIO(std::string ipaddr, std::string port);
	~TimIO();

	std::queue<std::string> _timCmd;	/**< Coda FIFO del contenuto dei comandi da inviare al TIM */
	std::queue<unsigned int> _timCmdId;	/**< Coda FIFO degli id dei comandi da inviare al TIM */
	std::queue<bool> _timCmdWrite;		/**< Coda FIFO del tipo di comando da inviare al TIM */
	unsigned int _defTimeout;		/**< Timeout di default da applicare nelle interazioni col TIM */

	tthread::thread* _thread;	/**< Thread del client TCP */

	static void client(void *instance);

private:
	bool connect2TIM();

	std::string _TIMport;	/**< Porta TCP del server TIM */
	std::string _TIMaddr;	/**< Indirizzo del server TIM */
	char* _reply;		/**< Buffer di ricezione del client TIM */
	int _socketfd;		/**< Socket descriptor del client TIM */
	struct addrinfo *_servinfo;	/**< Informazioni di sessione del server TIM */

	tthread::recursive_mutex _mutex; /**< Mutex del thread del client TIM */
};

}
#endif // TIMIO_H
