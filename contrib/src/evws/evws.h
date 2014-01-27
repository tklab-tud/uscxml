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

#ifndef EVWS_H
#define EVWS_H

#include <event2/event.h>
#include <event2/bufferevent.h>
#include <event2/listener.h>
#ifndef _WIN32
#	include <sys/queue.h>
#endif
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

struct evws;
struct evws_header;
struct evws_frame;
struct evws_connection;
struct evwsconq;
	
enum evws_opcode {
	EVWS_CONTINUATION_FRAME = 0x0,
	EVWS_TEXT_FRAME = 0x1,
	EVWS_BINARY_FRAME = 0x2,
	EVWS_CONNECTION_CLOSE = 0x8,
	EVWS_PING = 0x9,
	EVWS_PONG = 0xa
};

enum evws_conn_state {
	EVWS_NULL = 0x0,
	EVWS_FIRSTLINE_READ = 0x1,
	EVWS_HEADER_READ = 0x2,
	EVWS_CONNECTED = 0x3,
	EVWS_CLOSED = 0x4,
	EVWS_READING_FRAME = 0x5,
};

enum evws_frame_state {
	EVWS_OPCODE_READ = 0x0,
	EVWS_PAYLOAD_LENGTH_LENGTH_READ = 0x1,
	EVWS_PAYLOAD_LENGTH_READ = 0x2,
	EVWS_MASKING_KEY_READ = 0x3,
	EVWS_EXTENSION_READ = 0x4,
};

struct evws_header {
	struct {
		struct evws_header *tqe_next;
		struct evws_header **tqe_prev;
	} next;
	char *key;
	char *value;
};

struct evws_frame {
	/**
	 * Indicates that this is the final fragment in a message.  The first
	 * fragment MAY also be the final fragment.
	 */
	uint8_t fin;
	
	/**
	 * MUST be 0 unless an extension is negotiated that defines meanings
	 * for non-zero values.  If a nonzero value is received and none of
	 * the negotiated extensions defines the meaning of such a nonzero
	 * value, the receiving endpoint MUST _Fail the WebSocket
	 * Connection_.
	 */
	uint8_t rsv;
	
	/**
	 *  %x0 denotes a continuation frame
	 *  %x1 denotes a text frame
	 *  %x2 denotes a binary frame
	 *  %x3-7 are reserved for further non-control frames
	 *  %x8 denotes a connection close
	 *  %x9 denotes a ping
	 *  %xA denotes a pong
	 *  %xB-F are reserved for further control frames
	 */
	enum evws_opcode opcode;
	
	/**
	 * Defines whether the "Payload data" is masked.
	 */
	uint8_t has_mask;
	
	/**
	 * The length of the "Payload data", in bytes: if 0-125, that is the
	 * payload length.  If 126, the following 2 bytes interpreted as a
	 * 16-bit unsigned integer are the payload length.  If 127, the
	 * following 8 bytes interpreted as a 64-bit unsigned integer (the
	 * most significant bit MUST be 0) are the payload length.
	 */
	uint64_t size;
	uint64_t payload_read;
	uint8_t payload_bytes;

	/**
	 * The content or payload of the frame
	 */
	char* data;
	
	/**
	 * All frames sent from the client to the server are masked by a
	 * 32-bit value that is contained within the frame.  This field is
	 * present if the mask bit is set to 1 and is absent if the mask bit
	 * is set to 0.
	 */
	uint8_t mask[4];
	uint8_t mask_bytes;
	uint8_t mask_index;
	
	uint8_t state;
};

struct evws_connection {
	struct {
		struct evws_connection *tqe_next;
		struct evws_connection **tqe_prev;
	} next;
	struct evws *ws;
	struct evws_frame *frame;
	char *uri;
	struct bufferevent *bufev;
	int state;
	int fd;

	// headers
	struct wsheadersq {
		struct evws_header *tqh_first;
		struct evws_header **tqh_last;
	} headers;

};

typedef void (*cb_type)(struct evws_connection *, const char *, size_t, void *);
typedef void (*cb_frame_type)(struct evws_connection *, struct evws_frame *, void *);

struct evws_cb {
	struct {
		struct evws_cb *tqe_next;
		struct evws_cb **tqe_prev;
	} next;
	
	char * uri;
	cb_frame_type msg_cb;
	cb_type conn_cb;
	void * cb_arg;
};


struct evwsconq {
	struct evws_connection *tqh_first;
	struct evws_connection **tqh_last;
};

struct evws {
	struct evconnlistener *listener;
	struct wscbq {
		struct evws_cb *tqh_first;
		struct evws_cb **tqh_last;
	} callbacks;
	
	struct evwsconq connections;

	// generic callback
	cb_frame_type gencb;
	void * gencb_arg;
	struct event_base *base;
};

struct evws_connection *evws_connection_new(struct evws *ws, evutil_socket_t fd);
void evws_connection_free(struct evws_connection *conn);
int evws_is_valid_connection(struct evws *ws, struct evws_connection *conn);

struct evws_frame *evws_frame_new();
void evws_frame_free(struct evws_frame *frame);

struct evws *evws_new(struct event_base *base);
void evws_free(struct evws *ptr);

struct evws_header *evws_header_new(char *key, char *value);
void evws_header_free(struct evws_header *header);

char *evws_find_header(const struct wsheadersq *q, const char *key);
evutil_socket_t evws_bind_socket(struct evws * ws, unsigned short port);
int evws_set_cb(struct evws * ws, const char * pattern, cb_frame_type message_cb, cb_type connect_cb, void * arg);
cb_frame_type evws_set_gencb(struct evws *ws, cb_frame_type cb, void * arg);
void evws_broadcast(struct evws *ws, const char *uri, enum evws_opcode opcode, const char *data, uint64_t length);
void evws_send_data(struct evws_connection *conn, enum evws_opcode opcode, const char *data, uint64_t length);

#ifdef __cplusplus
}
#endif

#endif
