/**
 *  @file
 *  @author     Pawel Zubrycki <paw.zubr@gmail.com>
 *  @author     2013 Stefan Radomski (stefan.radomski@cs.tu-darmstadt.de)
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

#include "evws.h"
#include <stdlib.h>
#include <string.h>
#include <event2/buffer.h>
#include <event2/bufferevent.h>
#include "uscxml/util/SHA1.h"
#include "uscxml/util/Base64.h"

#ifdef _WIN32

char* strsep(char** stringp, const char* delim) {
  char* start = *stringp;
  char* p;
	
  p = (start != NULL) ? strpbrk(start, delim) : NULL;
	
  if (p == NULL)
  {
    *stringp = NULL;
  }
  else
  {
    *p = '\0';
    *stringp = p + 1;
  }
	
  return start;
}

#define strdup _strdup

#endif

static int evws_parse_first_line(struct evws_connection *conn, char *line);
static int evws_parse_header_line(char *line, char **skey, char **svalue);

// Callbacks
static void cb_accept(struct evconnlistener *listener, evutil_socket_t fd, struct sockaddr *address, int socklen, void *ctx); 
static void cb_read_handshake(struct bufferevent *bev, void *arg);
static void cb_read_frame(struct bufferevent *bev, void *arg);

#define WS_GUID "258EAFA5-E914-47DA-95CA-C5AB0DC85B11"

struct evws *evws_new(struct event_base *base) {
	struct evws *ret_obj = (struct evws*)calloc(1, sizeof(struct evws));
	ret_obj->base = base;
	ret_obj->listener = NULL;

	(&ret_obj->connections)->tqh_first = NULL;
	(&ret_obj->connections)->tqh_last = &((&ret_obj->connections)->tqh_first);
	
	(&ret_obj->callbacks)->tqh_first = NULL;
	(&ret_obj->callbacks)->tqh_last = &((&ret_obj->callbacks)->tqh_first);

	return ret_obj;
}

void evws_free(struct evws *ptr) {
	// Tu wiecej czyszczenia
	free(ptr);
}

evutil_socket_t evws_bind_socket(struct evws * ws, unsigned short port) {
	struct sockaddr_in sin;

	// Creating serverside socket
	memset(&sin, 0, sizeof(sin));
	sin.sin_family = AF_INET;
	sin.sin_addr.s_addr = htonl(0);
	sin.sin_port = htons(port);

	if(!(ws->listener = evconnlistener_new_bind(ws->base,
																							cb_accept,
																							ws,
																							LEV_OPT_CLOSE_ON_FREE|LEV_OPT_REUSEABLE|LEV_OPT_THREADSAFE,
																							-1,
																							(struct sockaddr*)&sin, sizeof(sin)))
		 ) {
		return 0;
	}
	return evconnlistener_get_fd(ws->listener);
}

int evws_set_cb(struct evws * ws, const char * uri, cb_frame_type message_cb, cb_type connect_cb, void * arg) {
	struct evws_cb *ws_cb = NULL;

	for (ws_cb = (&ws->callbacks)->tqh_first; ws_cb; ws_cb = ws_cb->next.tqe_next) {
		if (strcmp(ws_cb->uri, uri) == 0)
			return (-1);
	}

	if((ws_cb = (struct evws_cb*)calloc(1, sizeof(struct evws_cb))) == NULL) {
		return (-2);
	}

	ws_cb->uri = (char*)strdup(uri);
	ws_cb->msg_cb = message_cb;
	ws_cb->conn_cb = connect_cb;
	ws_cb->cb_arg = arg;

	// TAILQ_INSERT_TAIL
	ws_cb->next.tqe_next = NULL;
	ws_cb->next.tqe_prev = (&ws->callbacks)->tqh_last;
	*(&ws->callbacks)->tqh_last = ws_cb;
	(&ws->callbacks)->tqh_last = &(ws_cb->next.tqe_next);

	return (0);
}

cb_frame_type evws_set_gencb(struct evws *ws, cb_frame_type cb, void * arg) {
	cb_frame_type old_cb = ws->gencb;
	ws->gencb = cb;
	ws->gencb_arg = arg;
	return old_cb;
}

// Broadcast data to all buffers associated with pattern
void evws_broadcast(struct evws *ws, const char *uri, enum evws_opcode opcode, const char *data, uint64_t length) {
	struct evws_connection *ws_connection;
	for ((ws_connection) = (&ws->connections)->tqh_first; ws_connection; ws_connection = ws_connection->next.tqe_next) {
		if (strcmp(ws_connection->uri, uri) == 0)
			evws_send_data(ws_connection, opcode, data, length);
	}
}

int evws_is_valid_connection(struct evws *ws, struct evws_connection *conn) {
	struct evws_connection *ws_connection;
	for ((ws_connection) = (&ws->connections)->tqh_first; ws_connection; ws_connection = ws_connection->next.tqe_next) {
		if (ws_connection == conn)
			return 1;
	}
	return 0;
}


// Error callback
static void cb_error(struct bufferevent *bev, short what, void *ctx) {
	struct evws_connection *conn = ctx;
	if (conn->next.tqe_next != NULL) {
		conn->next.tqe_next->next.tqe_prev = conn->next.tqe_prev;
	} else {
		(&(conn->ws->connections))->tqh_last = conn->next.tqe_prev;
	}
	*(conn)->next.tqe_prev = conn->next.tqe_next;
	
	evws_connection_free(conn);
}

//Callback to accept
static void cb_accept(struct evconnlistener *listener, evutil_socket_t fd, struct sockaddr *address, int socklen, void *arg) {
	struct evws *ws = arg;
	struct evws_connection *ws_conn = evws_connection_new(ws, fd);
	
	bufferevent_setcb(ws_conn->bufev, cb_read_handshake, NULL, cb_error, ws_conn);
	bufferevent_enable(ws_conn->bufev, EV_READ);
}

int evws_parse_first_line(struct evws_connection *conn, char *line) {
	char *method;
	char *uri;
	char *version;

	/* Parse the request line */
	method = strsep(&line, " ");
	if (line == NULL)
		return (-1);
	uri = strsep(&line, " ");
	if (line == NULL)
		return (-1);
	version = strsep(&line, " ");
	if (line != NULL)
		return (-1);

	(void)method;
	(void)version;
	
	if ((conn->uri = strdup(uri)) == NULL) {
		return (-1);
	}

	return (0);
}

// Callback to read handshake
void cb_read_handshake(struct bufferevent *bev, void *arg) {
	struct evws_connection *ws_conn = arg;
	char *line, *skey, *svalue;
	struct evbuffer *buffer = bufferevent_get_input(bev);
	struct evws_header *header = NULL;
	size_t line_length;
	char *key = NULL;
	char *host = NULL;
	char *origin = NULL;
	SHA1Context sha1;
	char chksumSha1[21];
  int i;
	int md5End = 0;
	char chksumBase64[200];
	base64_encodestate* base64Ctx = NULL;
	
	switch(ws_conn->state) {
	case 0:
		line = evbuffer_readln(buffer, &line_length, EVBUFFER_EOL_CRLF);
		evws_parse_first_line(ws_conn, line);
		ws_conn->state = EVWS_FIRSTLINE_READ;
		free(line);
	case EVWS_FIRSTLINE_READ:
		while ((line = evbuffer_readln(buffer, &line_length, EVBUFFER_EOL_CRLF)) != NULL) {
			if (*line == '\0') { /* Last header - Done */
				free(line);
				ws_conn->state = EVWS_HEADER_READ;
				break;
			}
			evws_parse_header_line(line, &skey, &svalue);
			if(strcmp(skey, "Sec-WebSocket-Key") == 0) {
				key = strdup(svalue);
			} else if(strcmp(skey, "Host") == 0) {
				host = strdup(svalue);
			} else if(strcmp(skey, "Origin") == 0) {
				origin = strdup(svalue);
			}
			header = evws_header_new(skey, svalue);
			
			// TAILQ_INSERT_TAIL
			header->next.tqe_next = NULL;
			header->next.tqe_prev = (&ws_conn->headers)->tqh_last;
			*(&ws_conn->headers)->tqh_last = header;
			(&ws_conn->headers)->tqh_last = &(header->next.tqe_next);

			free(line);
		}
	default:
		break;
	};

	if (key == NULL)
		return;
	
	// -- SHA1
	
	SHA1Reset(&sha1);
	SHA1Input(&sha1, (const unsigned char*)key, 24);
	SHA1Input(&sha1, (const unsigned char*)WS_GUID, 36);
	SHA1Result(&sha1);
	
	for (i = 0; i < 5; i++) {
		chksumSha1[i * 4 + 0] = (sha1.Message_Digest[i] >> 24) & 0xff;
		chksumSha1[i * 4 + 1] = (sha1.Message_Digest[i] >> 16) & 0xff;
		chksumSha1[i * 4 + 2] = (sha1.Message_Digest[i] >> 8) & 0xff;
		chksumSha1[i * 4 + 3] = (sha1.Message_Digest[i] >> 0) & 0xff;
	}
//	printf("%s\n", chksumSha1);

	// -- BASE64
	
	base64Ctx = malloc(sizeof(base64_encodestate));
	base64_init_encodestate(base64Ctx);
	md5End += base64_encode_block(chksumSha1, 20, chksumBase64, base64Ctx);
	md5End += base64_encode_blockend(&chksumBase64[md5End], base64Ctx);
	// blockend writes unneccessary \n
	chksumBase64[md5End - 1] = 0;

	free(base64Ctx);
	free(key);
	free(host);
	free(origin);
	evbuffer_add_printf(bufferevent_get_output(ws_conn->bufev),
											"HTTP/1.1 101 Web Socket Protocol Handshake\r\n"
											"Upgrade: WebSocket\r\n"
											"Connection: Upgrade\r\n"
											"Sec-WebSocket-Accept: %s\r\n"
											"Server: uSCXML\r\n"
											"Access-Control-Allow-Origin: *\r\n"
											"Access-Control-Allow-Credentials: true\r\n"
											"Access-Control-Allow-Headers: content-type\r\n"
											"Access-Control-Allow-Headers: authorization\r\n"
											"Access-Control-Allow-Headers: x-websocket-extensions\r\n"
											"Access-Control-Allow-Headers: x-websocket-version\r\n"
											"Access-Control-Allow-Headers: x-websocket-protocol\r\n"
											"\r\n",
											chksumBase64
	);
	bufferevent_setcb(ws_conn->bufev, cb_read_frame, ((void*)0), cb_error, ws_conn);
	
	ws_conn->next.tqe_next = NULL;
	ws_conn->next.tqe_prev = (&(ws_conn->ws->connections))->tqh_last;
	*(&(ws_conn->ws->connections))->tqh_last = ws_conn;
	(&(ws_conn->ws->connections))->tqh_last = &(ws_conn->next.tqe_next);

	{
		struct evws_cb *ws_cb;
		for (ws_cb = ((&ws_conn->ws->callbacks))->tqh_first; ws_cb; ws_cb = ws_cb->next.tqe_next) {
			if (strcmp(ws_cb->uri, ws_conn->uri) == 0) {
				if(ws_cb->conn_cb != ((void*)0))
					ws_cb->conn_cb(ws_conn, ((void*)0), 0, ws_cb->cb_arg);
				return;
			}
		}
	}

}

int evws_parse_header_line(char *line, char **skey, char **svalue)
{
	*svalue = line;
	*skey = strsep(svalue, ":");
	if (*svalue == NULL)
		return -1;

	*svalue += strspn(*svalue, " ");

	return (0);
}

// Callback to read sent data
void cb_read_frame(struct bufferevent *bev, void *arg)
{
	struct evws_connection *conn = arg;
	struct evws *ws = conn->ws;
	char readbuf[2048]; // make sure a MTU fits
	int size = 0;
	struct evbuffer *buffer = bufferevent_get_input(bev);
	while ((size = evbuffer_remove(buffer, readbuf, sizeof(readbuf))) > 0) {
		char* dataPtr = readbuf;

NEXT_FRAME:
		if (conn->frame == NULL) {
			// data starts with the first byte of a new frame
			conn->frame = evws_frame_new();
			conn->frame->fin = (dataPtr[0] >> 7) & 1;
			conn->frame->rsv = (dataPtr[0] >> 4) & 7;
			conn->frame->opcode = dataPtr[0] & 0xfu;
			conn->frame->state = EVWS_OPCODE_READ;
			dataPtr++;
		}

		if (size - (dataPtr - readbuf) == 0)
			continue;
		
		if (conn->frame->state == EVWS_OPCODE_READ) { // we already read the first byte
			conn->frame->has_mask = (dataPtr[0] >> 7) & 1;
			if (conn->frame->has_mask)
				conn->frame->mask_bytes = 4;
			conn->frame->size = dataPtr[0] & 0x7fu;
			dataPtr++;
			
			if(conn->frame->size == 126) {
				conn->frame->payload_bytes = 2;
				conn->frame->size = 0;
			} else if(conn->frame->size == 127) {
				conn->frame->payload_bytes = 8;
				conn->frame->size = 0;
			} else {
				conn->frame->payload_bytes = 0;
			}
			conn->frame->state = EVWS_PAYLOAD_LENGTH_LENGTH_READ;
		}
		
		if (size - (dataPtr - readbuf) == 0)
			continue;
		
		if (conn->frame->state == EVWS_PAYLOAD_LENGTH_LENGTH_READ) { // we already read the first byte
			
			while(conn->frame->payload_bytes > 0 && // need to add more bytes to the payload length
						(size - (dataPtr - readbuf) > 0)) { // and bytes still available
				// length is in MSB network order - shift to left and add
				conn->frame->size = (conn->frame->size << 8) + (uint8_t)dataPtr[0];
				conn->frame->payload_bytes--;
				dataPtr++;
			}
			if (conn->frame->payload_bytes == 0) {
				conn->frame->state = EVWS_PAYLOAD_LENGTH_READ;
				if (!conn->frame->has_mask)
					conn->frame->state = EVWS_MASKING_KEY_READ;
			}
			conn->frame->data = (char*)malloc(conn->frame->size);
		}
		
		if (size - (dataPtr - readbuf) == 0)
			continue;
		
		if (conn->frame->state == EVWS_PAYLOAD_LENGTH_READ && // we already read the complete payload
				conn->frame->has_mask) {
			while (conn->frame->mask_bytes > 0 && // bytes for the frame mask
						 (size - (dataPtr - readbuf) > 0)) { // still some available
				conn->frame->mask[4 - conn->frame->mask_bytes] = dataPtr[0];
				conn->frame->mask_bytes--;
				dataPtr++;
				if (conn->frame->mask_bytes == 0)
					conn->frame->state = EVWS_MASKING_KEY_READ;
			}
		}
		
		if (size - (dataPtr - readbuf) == 0)
			continue;
		
		if (conn->frame->state == EVWS_MASKING_KEY_READ) { // we read all of the header
			size_t remaining = size - (dataPtr - readbuf);
			remaining = (remaining > conn->frame->size - conn->frame->payload_read ? conn->frame->size - conn->frame->payload_read : remaining);
			
			if (conn->frame->has_mask) {
        int i;
				for (i = 0; i < remaining; i++) {
					dataPtr[i] = dataPtr[i] ^ conn->frame->mask[conn->frame->mask_index];
					conn->frame->mask_index++;
					conn->frame->mask_index = conn->frame->mask_index % 4;
				}
			}
			memcpy(conn->frame->data + conn->frame->payload_read, dataPtr, remaining);
			conn->frame->payload_read += remaining;
			dataPtr += remaining;
		}

		if (conn->frame->payload_read == conn->frame->size) {
			// done reading this frame - invoke callbacks
			struct evws_cb *ws_cb;
			// TAILQ_FOREACH
			for (ws_cb = ((&ws->callbacks))->tqh_first; ws_cb; ws_cb = (ws_cb->next.tqe_next)) {
				if (strcmp(ws_cb->uri, conn->uri) == 0) {
					if(ws_cb->msg_cb != ((void*)0)) {
						ws_cb->msg_cb(conn, conn->frame, ws_cb->cb_arg);
					}
				}
			}
			ws->gencb(conn, conn->frame, ws->gencb_arg);
			
			evws_frame_free(conn->frame);
			conn->frame = NULL;
			if (size - (dataPtr - readbuf) != 0) // there is more data in this packet
				goto NEXT_FRAME;
		}
	}
}

void evws_send_data(struct evws_connection *conn, enum evws_opcode opcode, const char *data, uint64_t length) {
	char* writePtr = NULL;
	char *sendbuf = NULL;
	struct evbuffer *buffer = NULL;
	
	sendbuf = malloc(length + 10); // payload + header without masking key
	if(sendbuf == NULL)
		return;
	
	writePtr = sendbuf;
	
	writePtr[0] = (1 << 7); // set fin header and zero out RSV
	writePtr[0] += opcode; // set opcode
	writePtr++;
	writePtr[0] = (0 << 7); // we don't mask replies
	
	if (length < 126) {
		writePtr[0] += (uint8_t)length;
		writePtr++;
	} else if(length < (1 << 16)) {
		writePtr[0] = 126;
		writePtr[1] = (((uint16_t)length) >> 8) & 0xff;
		writePtr[2] = ((uint16_t)length) & 0xff;
		writePtr += 3;
	} else if(length < (1ull << 63)) {
		writePtr[0] = 126;
		// integer division and bitmask ought to be endian agnostic
		writePtr[1] = (length / 0x0100000000000000) & 0xff;
		writePtr[2] = (length / 0x0001000000000000) & 0xff;
		writePtr[3] = (length / 0x0000010000000000) & 0xff;
		writePtr[4] = (length / 0x0000000100000000) & 0xff;
		writePtr[5] = (length / 0x0000000001000000) & 0xff;
		writePtr[6] = (length / 0x0000000000010000) & 0xff;
		writePtr[7] = (length / 0x0000000000000100) & 0xff;
		writePtr[8] = (length / 0x0000000000000001) & 0xff;
		writePtr += 9;
	}
	
	memcpy(writePtr, data, length);
	writePtr += length;
	
	buffer = bufferevent_get_output(conn->bufev);
	evbuffer_add(buffer, sendbuf, writePtr - sendbuf);
	free(sendbuf);
}


// --- new and free pairs ---

struct evws_connection* evws_connection_new(struct evws *ws, evutil_socket_t fd) {
	struct evws_connection* conn = calloc(1, sizeof(struct evws_connection));
	conn->ws = ws;
	conn->fd = fd;
	conn->uri = ((void*)0);
	
	conn->bufev = bufferevent_socket_new(ws->base, fd, BEV_OPT_CLOSE_ON_FREE);
	conn->state = 0;
	conn->frame = ((void*)0);
	
	(&conn->headers)->tqh_first = NULL;
	(&conn->headers)->tqh_last = &(((&conn->headers))->tqh_first);
	
	return conn;
}

#if 0
struct evws_connection* evws_connection_upgrade(struct evws *ws, struct bufferevent *bufev) {
	struct evws_connection* conn = calloc(1, sizeof(struct evws_connection));
	conn->ws = ws;
	conn->fd = 0;
	conn->uri = ((void*)0);
	
//	conn->bufev = bufferevent_socket_new(ws->base, fd, BEV_OPT_CLOSE_ON_FREE);
	conn->bufev = bufev;
	conn->state = 0;
	conn->frame = ((void*)0);
	
	(&conn->headers)->tqh_first = NULL;
	(&conn->headers)->tqh_last = &(((&conn->headers))->tqh_first);
	
	return conn;
}
#endif

void evws_connection_free(struct evws_connection *conn) {
	struct evws_header *header;
	bufferevent_free(conn->bufev);
	if(conn->uri != ((void*)0))
		free(conn->uri);
	
	for (header = (&conn->headers)->tqh_first; header; header = header->next.tqe_next) {
		evws_header_free(header);
	}
	
	free(conn);
}

struct evws_frame *evws_frame_new() {
	struct evws_frame *frame = calloc(1, sizeof(struct evws_frame));
	return frame;
}

void evws_frame_free(struct evws_frame *frame) {
	if (frame->data)
		free(frame->data);
	free(frame);
}

struct evws_header *evws_header_new(char *key, char *value)
{
	struct evws_header *head = calloc(1, sizeof(struct evws_header));
	head->key = strdup(key);
	head->value = strdup(value);
	return head;
}

void evws_header_free(struct evws_header *header) {
	if(header->key != NULL)
		free(header->key);
	if(header->value != NULL)
		free(header->value);
	free(header);
}

char *evws_find_header(const struct wsheadersq *q, const char *key) {
	struct evws_header *hdr;
	char * ret = ((void*)0);
	
	for (hdr = q->tqh_first; hdr; hdr = hdr->next.tqe_next) {
		if(strcmp(hdr->key, key) == 0) {
			ret = hdr->value;
			break;
		}
	}
	return ret;
}

