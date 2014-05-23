/**
 *  @file
 *  @author     2012-2013 Stefan Radomski (stefan.radomski@cs.tu-darmstadt.de)
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

#include <boost/algorithm/string.hpp>

#include "MilesSessionInvoker.h"
#include "uscxml/server/HTTPServer.h"
#include <glog/logging.h>

#ifdef BUILD_AS_PLUGINS
#include <Pluma/Connector.hpp>
#endif

#include <inttypes.h>
#include <stdlib.h> /* srand, rand */

#ifdef _WIN32
#define strdup _strdup
#endif

namespace uscxml {

#ifdef BUILD_AS_PLUGINS
PLUMA_CONNECTOR
bool pluginConnect(pluma::Host& host) {
	host.add( new MilesSessionInvokerProvider() );
	return true;
}
#endif

MilesSessionInvoker::MilesSessionInvoker() {
	/* Initialize Miles */
	miles_init();

	_isRunning = false;
	num_connected = 0;
}

MilesSessionInvoker::~MilesSessionInvoker() {
	free_media_buffers();
};

boost::shared_ptr<InvokerImpl> MilesSessionInvoker::create(InterpreterImpl* interpreter) {
	boost::shared_ptr<MilesSessionInvoker> invoker = boost::shared_ptr<MilesSessionInvoker>(new MilesSessionInvoker());
	invoker->_interpreter = interpreter;
	return invoker;
}

Data MilesSessionInvoker::getDataModelVariables() {
	Data data;
	return data;
}

void MilesSessionInvoker::init_media_buffers() {
	video_out_buf = NULL;
	video_conv_buf = NULL;
	encoded_out_img = NULL;
	audio_in_buf = NULL;
	render_img = NULL;
	render_img_size = 0;
	audio_data = NULL;
	encoded_out_audio = NULL;
	audio_read_buf = NULL;
	video_data = (char *)malloc(1000000);
	text_msg_buf = (char *)malloc(1000);
	text_msg_available = 0;
}

void MilesSessionInvoker::free_media_buffers() {
	if(video_out_buf)
		free(video_out_buf);
	video_out_buf = NULL;
	if(video_conv_buf)
		free(video_conv_buf);
	video_conv_buf = NULL;
	if(encoded_out_img)
		free(encoded_out_img);
	encoded_out_img = NULL;
	if(audio_in_buf)
		free(audio_in_buf);
	audio_in_buf = NULL;
	if(render_img)
		free(render_img);
	render_img = NULL;
	render_img_size = 0;
	if(audio_data)
		free(audio_data);
	audio_data = NULL;
	if(video_data)
		free(video_data);
	video_data = NULL;
	if(encoded_out_audio)
		free(encoded_out_audio);
	encoded_out_audio = NULL;
	if(audio_read_buf)
		free(audio_read_buf);
	audio_read_buf = NULL;
	if(text_msg_buf)
		free(text_msg_buf);
	text_msg_buf = NULL;
	text_msg_available = 0;
}

void MilesSessionInvoker::free_video_buffers() {
	if(video_out_buf)
		free(video_out_buf);
	video_out_buf = NULL;
	if(video_conv_buf)
		free(video_conv_buf);
	video_conv_buf = NULL;
	if(encoded_out_img)
		free(encoded_out_img);
	encoded_out_img = NULL;
	if(render_img)
		free(render_img);
	render_img = NULL;
	render_img_size = 0;
	if(video_data)
		free(video_data);
	video_data = NULL;
}

void MilesSessionInvoker::free_audio_buffers() {
	if(audio_in_buf)
		free(audio_in_buf);
	audio_in_buf = NULL;
	if(audio_data)
		free(audio_data);
	audio_data = NULL;
	video_data = NULL;
	if(encoded_out_audio)
		free(encoded_out_audio);
	encoded_out_audio = NULL;
	if(audio_read_buf)
		free(audio_read_buf);
	audio_read_buf = NULL;
}

void MilesSessionInvoker::free_text_buffers() {
	if(text_msg_buf)
		free(text_msg_buf);
	text_msg_buf = NULL;
	text_msg_available = 0;
}

// Yes, sort of ugly...
char confero_text_msg_buf[1000];
int confero_text_msg_available = 0;

int receive_text_message_callback(u_int32_t ssrc, char *pkt, int length) {
	char cname[100];
	int i=0, j;

	while(pkt[i]) {
		cname[i] = pkt[i];
		i++;
	}
	cname[i++] = 0;
	j = i;
	while(pkt[j] && j<length) {
		if(pkt[j]=='<' || pkt[j]=='>' || pkt[j]=='\r' || pkt[j]=='\n')
			pkt[j] = ' ';
		j++;
	}
	memcpy(confero_text_msg_buf, pkt+i, length-i);
	//printf("RTCP app depacketizer called, cname = %s, msg = %s\n", cname, confero_text_msg_buf);
	confero_text_msg_available = 1;
	return length;
}

void MilesSessionInvoker::send(const SendRequest& req) {
//	std::cout << req;
	std::string origin;
	Event::getParam(req.params, "origin", origin);

	if (false) {
	} else if (iequals(req.name, "start")) {

		std::string userId, reflector, session;
		Event::getParam(req.params, "userid", userId);
		Event::getParam(req.params, "reflector", reflector);
		Event::getParam(req.params, "session", session);
		processEventStart(origin, userId, reflector, session);

	} else if (iequals(req.name, "stop")) {

		processEventStop(origin);

	} else if (iequals(req.name, "participants")) {

		processEventParticipants(origin);

	} else if (iequals(req.name, "thumbnail")) {

		std::string userId;
		Event::getParam(req.params, "userid", userId);
		processEventThumbnail(origin, userId);

	} else if (iequals(req.name, "videoon")) {

		std::string userId;
		Event::getParam(req.params, "userid", userId);
		processEventVideoOn(origin, userId);

	} else if (iequals(req.name, "videooff")) {

		std::string userId;
		Event::getParam(req.params, "userid", userId);
		processEventVideoOff(origin, userId);

	} else if (iequals(req.name, "audioon")) {

		std::string userId;
		Event::getParam(req.params, "userid", userId);
		processEventAudioOn(origin, userId);

	} else if (iequals(req.name, "audiooff")) {

		std::string userId;
		Event::getParam(req.params, "userid", userId);
		processEventAudioOff(origin, userId);

	} else if (iequals(req.name, "sendvideo")) {

		std::string userId, compression;
		size_t height, width, framerate;
		Event::getParam(req.params, "userid", userId);
		Event::getParam(req.params, "height", height);
		Event::getParam(req.params, "width", width);
		Event::getParam(req.params, "framerate", framerate);
		processEventSendVideo(origin, width, height, framerate, compression);

	} else if (iequals(req.name, "sendvideooff")) {

		processEventSendVideoOff(origin);

	} else if (iequals(req.name, "sendaudio")) {

		std::string userId, encoding;
		Event::getParam(req.params, "userid", userId);
		Event::getParam(req.params, "encoding", encoding);
		processEventSendAudio(origin, encoding);

	} else if (iequals(req.name, "sendaudiooff")) {

		processEventSendAudioOff(origin);

	} else if (iequals(req.name, "gettext")) {

		processEventGetText(origin);

	} else if (iequals(req.name, "posttext")) {

		std::string userId, message;
		Event::getParam(req.params, "userid", userId);
		Event::getParam(req.params, "message", message);
		processEventPostText(origin, userId, message);

	} else {
		LOG(ERROR) << "Do not know how to handle event " << req.name;
	}

}

void MilesSessionInvoker::processEventStart(const std::string& origin, const std::string& userid, const std::string& reflector, const std::string& session) {

	Event ev;
	ev.data.compound["origin"] = origin;
	//std::cout << req;
	if(num_connected>0) {
		num_connected++;
		ev.name = "start.reply";
		returnEvent(ev);
		return;
	}

	LOG(ERROR) << "miles/start called, reflector ip = " << reflector << " session name = " << session << " userid = " << userid;

	int rv;
	rv = miles_connect_reflector_session((char*)reflector.c_str(), (char*)session.c_str());
	if (!rv) {
		LOG(ERROR) << "Could not setup reflector session";
		ev.name = "start.error";
		returnEvent(ev);
		return;
	}
	LOG(ERROR) << "session set up";

	/* set up media buffers */
	init_media_buffers();

	/* Set up audio and video RTP sockets */
	video_rtp_in_socket = miles_net_setup_udp_socket((char*)reflector.c_str(), video_port, video_port, 10, 16000);
	audio_rtp_in_socket = miles_net_setup_udp_socket((char*)reflector.c_str(), audio_port, audio_port, 10, 16000);
	video_rtp_out_socket = video_rtp_in_socket;
	audio_rtp_out_socket = audio_rtp_in_socket;


	/* Set up audio and video RTCP sockets */
	video_rtcp_in_socket = miles_net_setup_udp_socket((char*)reflector.c_str(), video_port+1, video_port+1, 10, 16000);
	audio_rtcp_in_socket = miles_net_setup_udp_socket((char*)reflector.c_str(), audio_port+1, audio_port+1, 10, 16000);
	video_rtcp_out_socket = video_rtcp_in_socket;
	audio_rtcp_out_socket = audio_rtcp_in_socket;

	/* Set up RTP audio and video sessions */
	video_session = miles_rtp_setup_session(video_rtp_in_socket, MILES_RTP_MEDIA_TYPE_VIDEO);
	audio_session = miles_rtp_setup_session(audio_rtp_in_socket, MILES_RTP_MEDIA_TYPE_AUDIO);

	/* Set up RTCP audio and video sessions */
	video_session->rtcp_session = miles_rtp_setup_rtcp_session(video_session, video_rtcp_in_socket);
	audio_session->rtcp_session = miles_rtp_setup_rtcp_session(audio_session, audio_rtcp_in_socket);

	/* Set up video capture */
	video_grabber_available = setup_video_grabber();
	if(video_grabber_available)
		sendvideo_enabled = 1;

	/* Set up audio capture/playback */
	audio_available = setup_audio();
	if(audio_available)
		sendaudio_enabled = 1;

	/* Set up outgoing RTP stream for video */
	if(video_grabber_available) {
		out_rtp_video_stream = miles_rtp_setup_outgoing_stream(video_session, video_rtp_out_socket, 0, MILES_RTP_PAYLOAD_TYPE_JPEG);
		out_rtp_video_stream->codec_ctx = video_encoder;
		out_rtcp_video_stream = miles_rtp_setup_outgoing_rtcp_stream(video_session->rtcp_session, video_rtcp_out_socket, out_rtp_video_stream->ssrc);
		if(out_rtp_video_stream->sdes.cname)
			free(out_rtp_video_stream->sdes.cname);
		out_rtp_video_stream->sdes.cname = strdup(userid.c_str());
	}

	/* Set up outgoing RTP stream for audio */
	if(audio_available) {
		out_rtp_audio_stream = miles_rtp_setup_outgoing_stream(audio_session, audio_rtp_out_socket, 0, MILES_RTP_PAYLOAD_TYPE_L16);
		if(out_rtp_audio_stream->sdes.cname)
			free(out_rtp_audio_stream->sdes.cname);
		out_rtp_audio_stream->sdes.cname = strdup(userid.c_str());

		/* Associate RTP stream with codec context */
		out_rtp_audio_stream->codec_ctx = audio_encoder;

		/* Set up outgoing RTCP streams for audio */
		out_rtcp_audio_stream = miles_rtp_setup_outgoing_rtcp_stream(audio_session->rtcp_session, audio_rtcp_out_socket, out_rtp_audio_stream->ssrc);
	}

	/* Register RTCP APP handler for text messages */
	rv = miles_rtp_register_rtcp_app_handler("text", NULL, receive_text_message_callback, 0);
	if(rv==0) {
		LOG(ERROR) << "Error registering text message callback";
	}
	memset(confero_text_msg_buf, 0, 1000);

	_isRunning = true;
	num_connected=1;
	_reflector = reflector;
	_userId = userid;
	_session = session;

	if(audio_available)
		_audioThread = new tthread::thread(MilesSessionInvoker::runAudio, this);
	_videoThread = new tthread::thread(MilesSessionInvoker::runVideo, this);
	ev.name = "start.reply";
	returnEvent(ev);
}

void MilesSessionInvoker::processEventStop(const std::string& origin) {
	Event ev;
	ev.data.compound["origin"] = origin;

	if(num_connected==0) {
		LOG(ERROR) << "not connected";
		ev.name = "stop.error";
		returnEvent(ev);
		return;
	}
	num_connected--;
	if(num_connected>0) {
		ev.name = "stop.reply";
		returnEvent(ev);
		return;
	}
	int rv = miles_disconnect_reflector_session((char*)_reflector.c_str(), (char*)_session.c_str());
	if (!rv) {
		LOG(ERROR) << "Could not disconnect from reflector session";
		ev.name = "stop.error";
		returnEvent(ev);
		return;
	}
	/* Unregister RTCP APP handler for text messages */
	rv = miles_rtp_unregister_rtcp_app_handler("text");
	if(rv==0) {
		LOG(ERROR) << "Error registering text message callback";
	}
	_isRunning = false;
	free_text_buffers();
	ev.name = "stop.reply";
	returnEvent(ev);
	LOG(ERROR) << "disconnected from reflector session";
}

void MilesSessionInvoker::processEventParticipants(const std::string& origin) {

	Event ev;
	ev.data.compound["origin"] = origin;
	if(num_connected==0) {
		LOG(ERROR) << "not connected";
		ev.name = "participants.error";
		returnEvent(ev);
		return;
	}
	// create an array with objects inside
	for (int i = 0; i < 5; i++) {
		Data userInfo;
		userInfo.compound["name"] = Data("username" + toStr(i), Data::VERBATIM);
		userInfo.compound["email"] = Data("usermail" + toStr(i), Data::VERBATIM);
		ev.data.compound["participants"].array.push_back(userInfo);
	}

	ev.name = "participants.reply";
	returnEvent(ev);
}

void MilesSessionInvoker::processEventThumbnail(const std::string& origin, const std::string& userid) {
	Event ev;
	ev.data.compound["origin"] = origin;
	if(num_connected==0) {
		LOG(ERROR) << "not connected";
		ev.name = "thumbnail.error";
		returnEvent(ev);
		return;
	}
	URL imageURL("emptyface.jpg");
	imageURL.toAbsolute(_interpreter->getBaseURI());
	std::stringstream ssImage;
	ssImage << imageURL;
	std::string imageContent = ssImage.str();

	ev.name = "thumbnail.reply";

	struct thumb_entry *use_thumb = NULL;
	struct miles_list *p;
	struct thumb_entry *te;
	_mutex.lock();
	// Find thumbnail of user
	p = thumb_list;
	while(p) {
		te = (struct thumb_entry *)p->item;
		if(te->userid && strcmp(te->userid, userid.c_str()) == 0) {
			use_thumb = te;
			break;
		}
		if(te->userid==NULL && use_thumb == NULL) {
			use_thumb = te;
		}
		p = p->next;
	}
	if(!p && use_thumb)
		use_thumb->userid = strdup(userid.c_str());
	if(use_thumb) {
		ev.data.compound["image"] = Data(use_thumb->img_buf, use_thumb->img_size, "image/jpeg");
	} else {
		// Return empty face image
		ev.data.compound["image"] = Data(imageContent.data(), imageContent.size(), "image/jpeg");
	}
	_mutex.unlock();

	returnEvent(ev);
}

void MilesSessionInvoker::processEventVideoOn(const std::string& origin, const std::string& userid) {
	Event ev;
	ev.name = "videoon.reply";
	ev.data.compound["origin"] = origin;
	returnEvent(ev);
}
void MilesSessionInvoker::processEventVideoOff(const std::string& origin, const std::string& userid) {
	Event ev;
	ev.name = "videooff.reply";
	ev.data.compound["origin"] = origin;
	returnEvent(ev);
}
void MilesSessionInvoker::processEventAudioOn(const std::string& origin, const std::string& userid) {
	Event ev;
	ev.name = "audioon.reply";
	ev.data.compound["origin"] = origin;
	returnEvent(ev);
}
void MilesSessionInvoker::processEventAudioOff(const std::string& origin, const std::string& userid) {
	Event ev;
	ev.name = "audiooff.reply";
	ev.data.compound["origin"] = origin;
	returnEvent(ev);
}
void MilesSessionInvoker::processEventSendVideo(const std::string& origin, size_t width, size_t height, size_t framerate, const std::string& compression) {
	Event ev;
	ev.name = "sendvideo.reply";
	ev.data.compound["origin"] = origin;
	sendvideo_enabled = 1;
	returnEvent(ev);
}
void MilesSessionInvoker::processEventSendVideoOff(const std::string& origin) {
	Event ev;
	ev.name = "sendvideooff.reply";
	ev.data.compound["origin"] = origin;
	returnEvent(ev);
	sendvideo_enabled = 0;
}
void MilesSessionInvoker::processEventSendAudio(const std::string& origin, const std::string& encoding) {
	Event ev;
	ev.name = "sendaudio.reply";
	ev.data.compound["origin"] = origin;
	returnEvent(ev);
	sendaudio_enabled = 1;
}
void MilesSessionInvoker::processEventSendAudioOff(const std::string& origin) {
	Event ev;
	ev.name = "sendaudiooff.reply";
	ev.data.compound["origin"] = origin;
	returnEvent(ev);
	sendaudio_enabled = 0;
}
void MilesSessionInvoker::processEventPostText(const std::string& origin, const std::string& userid, const std::string& message) {
	char msgbuf[1000];
	char pkt[1000];
	char *cname = "user@all"; // for now
	int n, length;
	Event ev;

	ev.data.compound["origin"] = origin;
	if(num_connected==0) {
		LOG(ERROR) << "not connected";
		ev.name = "posttext.error";
		returnEvent(ev);
		return;
	}
	ev.name = "posttext.reply";
	returnEvent(ev);
	if(out_rtcp_video_stream==NULL)
		return;
	//printf("sending message %s\n", message.c_str());
	memcpy(msgbuf, cname, strlen(cname)+1);
	sprintf(msgbuf+strlen(cname)+1, "<%s>: %s", userid.c_str(), message.c_str());
	n = strlen(cname)+1 + userid.length() + 4 + message.length();
	length = miles_rtp_make_rtcp_app(pkt, out_rtcp_video_stream->ssrc, "text", n, msgbuf);
	if(length>0 && out_rtcp_video_stream)
		out_rtcp_video_stream->send_packet(out_rtcp_video_stream->socket, pkt, length, 0);
}

void MilesSessionInvoker::processEventGetText(const std::string& origin) {
	Event ev;
	ev.data.compound["origin"] = origin;
	if(num_connected==0) {
		LOG(ERROR) << "not connected";
		ev.name = "gettext.error";
		returnEvent(ev);
		return;
	}

	ev.name = "gettext.reply";
	if(confero_text_msg_available) {
		strcpy(text_msg_buf, confero_text_msg_buf);
		ev.data.compound["message"] = Data(text_msg_buf, Data::VERBATIM);
		//ev.data.compound["message"] = Data(base64_encode(text_msg_buf, strlen(text_msg_buf)), Data::VERBATIM);
		ev.data.compound["user"] = Data("username1", Data::VERBATIM);
		memset(confero_text_msg_buf, 0, 1000);
		confero_text_msg_available = 0;
	}

	returnEvent(ev);
}

void MilesSessionInvoker::runAudio(void* instance) {
	((MilesSessionInvoker*)instance)->processAudio();
}

void MilesSessionInvoker::runVideo(void* instance) {
	((MilesSessionInvoker*)instance)->processVideo();
}

void MilesSessionInvoker::processVideo() {
	while(_isRunning) {
		rtp_video_receiver(video_session);
		if(video_grabber_available && sendvideo_enabled)
			video_transmitter(video_grabber, video_encoder, out_rtp_video_stream, out_rtcp_video_stream);
	}
	/* done, clean up */
	if(video_grabber_available) {
		miles_rtp_destroy_out_stream(out_rtp_video_stream);
		miles_video_grabber_destroy(video_grabber);
		miles_video_codec_destroy_encoder(video_encoder);
		video_grabber_available = 0;
		sendvideo_enabled = 0;
	}
	miles_rtp_destroy_session(video_session);
	miles_list_destroy(thumb_list);
	thumb_list = NULL;
	miles_net_socket_close(video_rtp_in_socket);
	miles_net_socket_close(video_rtcp_in_socket);

	free_video_buffers();
}

void MilesSessionInvoker::processAudio() {
	while(_isRunning) {
		rtp_audio_receiver(audio_session);
		if(audio_available && sendaudio_enabled)
			audio_transmitter(audio_dev, audio_encoder, out_rtp_audio_stream, out_rtcp_audio_stream);
	}
	/* done, clean up */
	if(audio_available) {
		miles_rtp_destroy_out_stream(out_rtp_audio_stream);
		if(audio_dev_playback)
			miles_audio_device_close(MILES_AUDIO_IO_OPENAL, audio_dev_playback, 0);
		if(audio_dev)
			miles_audio_device_close(MILES_AUDIO_IO_OPENAL, audio_dev, 1);
		miles_audio_codec_destroy_encoder(audio_encoder);
		audio_available = 0;
		sendaudio_enabled = 0;
	}
	miles_rtp_destroy_session(audio_session);
	miles_net_socket_close(audio_rtp_in_socket);
	miles_net_socket_close(audio_rtcp_in_socket);

	free_video_buffers();
}

int MilesSessionInvoker::setup_audio() {
	/* Check that we have OpeanAL audio */
	if(!miles_audio_io_is_supported(MILES_AUDIO_IO_OPENAL)) {
		fprintf(stderr, "OpenAL audio i/o not supported on this platform.\n");
		return 0;
	}

	/* Initialize and configure audio encoder */
	audio_encoder = miles_audio_codec_init_encoder();
	audio_encoder->codec_id = miles_audio_codec_get_encoder_for_rtp_payload_type(MILES_RTP_PAYLOAD_TYPE_L16);
	audio_encoder->sample_rate = 16000;
	audio_encoder->bytes_per_sample = 2;
	audio_encoder->chunk_size = 320; /* 20 ms */
	audio_encoder->input_format = MILES_AUDIO_FORMAT_PCM;
	int rv = miles_audio_codec_setup_encoder(audio_encoder);
	if(rv == 0) {
		/* Couldn't set up audio codec */
		LOG(ERROR) << "Couldn't set up audio codec";
		return 0;
	}

	/* Set up audio grabber */
	int n = miles_audio_device_get_supported_devices(MILES_AUDIO_IO_OPENAL, &supported_audio_devices);
	if(n<=0) {
		/* No audio device available */
		LOG(ERROR) << "No audio device available";
		return 0;
	}
	/* Use first device that supports capture */
	for(int i=0; i<n; i++) {
		audio_dev = miles_audio_device_open(MILES_AUDIO_IO_OPENAL, supported_audio_devices[i].id, MILES_AUDIO_FORMAT_PCM, 16000, 2, 1, 640, 1);
		if(audio_dev)
			break;
	}
	if(audio_dev == NULL) {
		LOG(ERROR) << "No audio device supporting capture available";
		return 0;
	}

	/* Find first audio device that supports playback */
	for(int i=0; i<n; i++) {
		audio_dev_playback = miles_audio_device_open(MILES_AUDIO_IO_OPENAL, supported_audio_devices[i].id, MILES_AUDIO_FORMAT_PCM, 16000, 2, 1, 640, 0);
		if(audio_dev_playback) {
			audio_dev_playback_id = supported_audio_devices[i].id;
			break;
		}
	}
	if(audio_dev_playback == NULL) {
		LOG(ERROR) << "No audio device supporting playback available";
		return 0;
	}

	audio_in_buf = (char *)malloc(audio_encoder->sample_rate*audio_encoder->bytes_per_sample);
	encoded_out_audio = (char *)malloc(audio_encoder->sample_rate*audio_encoder->bytes_per_sample);
	audio_read_buf = (char *)malloc(audio_encoder->sample_rate*audio_encoder->bytes_per_sample);
	audio_data = (char *)malloc(1000000);

	LOG(ERROR) << "audio device set up";
	return 1;
}

int MilesSessionInvoker::setup_video_grabber() {
	struct miles_video_grabber_description *grabber_description;

	/* Set up video grabber */
	int n = miles_video_grabber_get_supported_grabbers(&supported_video_grabbers);
	if(n<=0) {
		/* No video grabber available */
		LOG(ERROR) << "No video grabber available";
		return 0;
	}
	int use_grabber = 0;
	if(n>1) {
		/* If more than one grabber, select one that is not 'Test' */
		for(int i=0; i<n; i++) {
			grabber_description = miles_video_grabber_get_description(supported_video_grabbers[i]);
			if(strcmp(grabber_description->name, "Test") != 0) {
				/* Make sure there is a device */
				if(grabber_description->devices != NULL) {
					use_grabber = i;
					free(grabber_description);
					break;
				}
			}
			free(grabber_description);
		}
	}
	grabber_description = miles_video_grabber_get_description(supported_video_grabbers[use_grabber]);
	printf("Using video grabber %s\n", grabber_description->name);
	video_grabber = miles_video_grabber_create_context(supported_video_grabbers[use_grabber]);
	video_grabber->width = 320;
	video_grabber->height = 240;
	video_grabber->frame_rate = 25*100;
	/* Select first supported image format */
	struct miles_video_grabber_device *dev;
	dev = (struct miles_video_grabber_device *)grabber_description->devices->item;
	struct miles_int_struct *img_format;
	img_format = (struct miles_int_struct *)dev->capabilities->formats->item;
	video_grabber->image_format = img_format->value;
	miles_video_grabber_setup(video_grabber);
	free(supported_video_grabbers);
	free(grabber_description);

	/* Initialize and configure video encoder */
	video_encoder = miles_video_codec_init_encoder();
	video_encoder->codec_id = miles_video_codec_get_encoder_for_rtp_payload_type(MILES_RTP_PAYLOAD_TYPE_JPEG);
	video_encoder->width = video_grabber->width = 320;
	video_encoder->height = video_grabber->height = 240;
	video_encoder->qfactor = 50;
	//video_encoder->input_format = MILES_IMAGE_RGB; //video_grabber->image_format;
	int rv = miles_video_codec_setup_encoder(video_encoder);
	if (!rv) {
		LOG(ERROR) << "Could not setup video encoder";
		return 0;
	}

	video_out_buf = (char *)malloc(video_encoder->width*video_encoder->height*4);
	encoded_out_img = (char *)malloc(video_encoder->width*video_encoder->height*4);

	return 1;
}

void MilesSessionInvoker::cancel(const std::string sendId) {
}

void MilesSessionInvoker::invoke(const InvokeRequest& req) {
	video_port = 5566;
	audio_port = 5568;
	thumb_list = NULL;
	save_image = 0;
}

/**
 * Render video image in a window
 */
void MilesSessionInvoker::render_video_image(char *img, int width, int height, int img_format) {
	char *img_buf_ptr;

	if(img_format != MILES_IMAGE_RGB) {
		if(render_img==NULL || render_img_size < width*height*4) {
			if(render_img)
				free(render_img);
			render_img_size = width*height*4;
			render_img = (char *)malloc(render_img_size);
		}
		miles_image_convert(img, render_img, img_format, MILES_IMAGE_RGB, width, height);
		img_buf_ptr = render_img;
	} else {
		img_buf_ptr = img;
	}

	/* save image to disk */
	if(save_image)
		miles_image_file_write(MILES_IMAGE_FILE_FORMAT_PNG, MILES_IMAGE_RGB, "image.png", width, height, img_buf_ptr);

	/* render image in window... to be implementd. */
}


/**
 * Send an audio chunk decoded from an RTP stream to an audio device
 */
void MilesSessionInvoker::playback_audio(u_int32_t ssrc, char *buf, int sample_rate, int bps, int audio_format, int size) {

	if(size<0)
		return;

	/* re-configure audio device, if needed */
	if(audio_dev_playback == NULL || audio_dev_playback->chunk_size != size || audio_dev_playback->sample_rate != sample_rate ||
	        audio_dev_playback->format != audio_format ||	audio_dev_playback->bytes_per_sample != bps) {
		if(audio_dev_playback)
			miles_audio_device_close(MILES_AUDIO_IO_OPENAL, audio_dev_playback, 0);
		audio_dev_playback = miles_audio_device_open(MILES_AUDIO_IO_OPENAL, audio_dev_playback_id, audio_format, sample_rate, bps, 1, size, 0);
		if(audio_dev_playback == NULL)
			return;
	}

	/* play audio */
	miles_audio_device_write(MILES_AUDIO_IO_OPENAL, audio_dev_playback, buf, size);
}

/**
 * Handle incoming video streams
 */

int MilesSessionInvoker::video_receiver(struct miles_rtp_in_stream *rtp_stream, char *data, int bytes_read) {
	int status, n;
	struct miles_video_codec_decode_context *codec_ctx;
	char *codec_name;
	struct miles_list *p;
	struct thumb_entry *te;

	codec_ctx = (struct miles_video_codec_decode_context *)rtp_stream->codec_ctx;

	if(codec_ctx == NULL || !miles_video_codec_decoder_supports_rtp_payload_type(codec_ctx, rtp_stream->payload_type)) {
		if(codec_ctx)
			miles_video_codec_destroy_decoder(codec_ctx);
		codec_ctx = miles_video_codec_init_decoder();
		codec_ctx->codec_id = miles_video_codec_get_decoder_for_rtp_payload_type(rtp_stream->payload_type);
		if(codec_ctx->codec_id == MILES_VIDEO_CODEC_UNKNOWN) {
			/* Cannot decode the video stream */
			return 0;
		}

		status = miles_video_codec_setup_decoder(codec_ctx);
		if(status == 0) {
			/* Cannot decode the video stream */
			return 0;
		}
		rtp_stream->codec_ctx = (void *)codec_ctx;
		return 0;
	}

	/* Find thumbnail list entry of the stream */
	_mutex.lock();
	p = thumb_list;
	while(p) {
		te = (struct thumb_entry *)p->item;
		if(te->ssrc == rtp_stream->ssrc) {
			break;
		}
		p = p->next;
	}
	if(p==NULL) {
		// Create new thumbnail list entry
		te = (struct thumb_entry *)malloc(sizeof(struct thumb_entry));
		if(thumb_list==NULL)
			p = thumb_list = miles_list_create(te);
		else
			p = miles_list_append(thumb_list, te);
		te->ssrc = rtp_stream->ssrc;
		te->window_ctx = NULL;
		te->userid = NULL;
		te->img_buf = (char *)malloc(bytes_read);
		te->buf_size = bytes_read;
		te->img_size = 0;
		te->decode_buf = NULL;
	}
	if(te->buf_size < bytes_read) {
		// Need bigger image buffer
		free(te->img_buf);
		te->img_buf = (char *)malloc(bytes_read);
		te->buf_size = bytes_read;
	}
	/*
	 * If codec is JPEG, thumbnail image can be saved without decoding
	 */
	codec_name = miles_video_codec_get_codec_name(codec_ctx->codec_id);
	if(codec_name==NULL) {
		_mutex.unlock();
		return 0;
	}
	if(strcmp(codec_name, "JPEG")==0) {
		memcpy(te->img_buf, data, bytes_read);
		te->img_size = bytes_read;
		te->img_format = WEBCONFERO_THUMB_JPEG;
		//miles_image_file_write(MILES_IMAGE_FILE_FORMAT_JPG, MILES_IMAGE_JPEG, "test.jpg", bytes_read, 1, data);
		// If we're not going to render the video in a window, we're done now
		if(te->window_ctx==NULL) {
			_mutex.unlock();
			return 0;
		}
	} else {
		te->img_format = WEBCONFERO_THUMB_PNG;
	}
	free(codec_name);

	if(te->decode_buf==NULL) {
		te->decode_buf = (char *)malloc(1920*1080*4);
	}
	n = miles_video_codec_decode(codec_ctx, data, te->decode_buf, bytes_read);
	if(n > 0) {
		if(te->img_format==WEBCONFERO_THUMB_PNG) {
			if(n > te->buf_size) {
				free(te->img_buf);
				te->img_buf = (char *)malloc(n);
				te->buf_size = n;
			}
			// Need to insert a PNG header here...
			memcpy(te->img_buf, te->decode_buf, n);
			te->img_size = n;
		}
		if(te->window_ctx)
			render_video_image(te->decode_buf, codec_ctx->width, codec_ctx->height, codec_ctx->output_format);
	}
	_mutex.unlock();

	return n;
}

/**
 * Handle incoming audio streams
 */

int MilesSessionInvoker::audio_receiver(struct miles_rtp_in_stream *rtp_stream, char *data, int bytes_read) {
	int status, size;
	struct miles_audio_codec_decode_context *codec_ctx;

	codec_ctx = (struct miles_audio_codec_decode_context *)rtp_stream->codec_ctx;

	if(codec_ctx == NULL || !miles_audio_codec_decoder_supports_rtp_payload_type(codec_ctx, rtp_stream->payload_type)) {
		if(codec_ctx)
			miles_audio_codec_destroy_decoder(codec_ctx);
		codec_ctx = miles_audio_codec_init_decoder();
		codec_ctx->codec_id = miles_audio_codec_get_decoder_for_rtp_payload_type(rtp_stream->payload_type);
		if(codec_ctx->codec_id == MILES_AUDIO_CODEC_UNKNOWN) {
			/* Cannot decode the audio stream */
			return 0;
		}
		status = miles_audio_codec_setup_decoder(codec_ctx);
		if(status == 0) {
			/* Cannot decode the audio stream */
			return 0;
		}
		rtp_stream->codec_ctx = (void *)codec_ctx;
	}
	size = miles_audio_codec_decode(codec_ctx, data, audio_in_buf);
	if(size > 0) {
		playback_audio(rtp_stream->ssrc, audio_in_buf, codec_ctx->sample_rate, codec_ctx->bytes_per_sample, codec_ctx->output_format, size);
	}
	return size;
}

/**
 * Read and depacketize incoming RTP streams
 */

void MilesSessionInvoker::rtp_audio_receiver(struct miles_rtp_session *rtp_session) {
	int n;
	struct miles_rtp_in_stream *rtp_stream;

	/* Poll RTP socket, read all available RTP packets */
	while (1) {
		n = miles_net_wait_socket(rtp_session->socket, 10);
		if(n<=0) return;

		/* Read RTP data */
		n = miles_rtp_recv(rtp_session, &rtp_stream, audio_data);
		if(n>0) {
			audio_receiver(rtp_stream, audio_data, n);
		}

		/* Poll RTCP socket */
		n = miles_net_poll_socket(rtp_session->rtcp_session->socket);
		if(n>0) {
			/* Do RTCP packet processEventing */
			n = miles_rtp_recv_rtcp(rtp_session->rtcp_session);
		}
	}
}

void MilesSessionInvoker::rtp_video_receiver(struct miles_rtp_session *rtp_session) {
	int n;
	struct miles_rtp_in_stream *rtp_stream;

	/* Poll RTP socket, read all available RTP packets */
	while (1) {
		n = miles_net_wait_socket(rtp_session->socket, 10);
		if(n<=0) return;

		/* Read RTP data */
		n = miles_rtp_recv(rtp_session, &rtp_stream, video_data);
		if(n>0) {
			video_receiver(rtp_stream, video_data, n);
		}

		/* Poll RTCP socket */
		n = miles_net_poll_socket(rtp_session->rtcp_session->socket);
		if(n>0) {
			/* Do RTCP packet processEventing */
			n = miles_rtp_recv_rtcp(rtp_session->rtcp_session);
		}
	}
}

/**
 * Send RTP video stream
 */
int MilesSessionInvoker::video_transmitter(struct miles_video_grabber_context *grabber, struct miles_video_codec_encode_context *codec_ctx, struct miles_rtp_out_stream *rtp_stream, struct miles_rtcp_out_stream *out_rtcp_stream) {
	int n;
	static struct timeval last_time;
	static int first_time=1;
	struct timeval now;
	int tbf;
	char *video_buf_ptr;

#ifndef WIN32
	// Need to fix gettimeofday() on Win
	if (first_time) {
		gettimeofday(&last_time, 0);
		first_time = 0;
	}
	gettimeofday(&now, 0);
	tbf = 100000 / grabber->frame_rate;
	if (miles_elapsed_time(&last_time, &now) < tbf)
		return 0;

	last_time = now;
#endif

	/* Send RTCP packets, if due */
	miles_rtp_send_rtcp(out_rtcp_stream);

	n = miles_video_grabber_grab(grabber, video_out_buf);
	if(n <= 0)
		return 0;
	if(grabber->image_format != codec_ctx->input_format) {
		/* image conversion ... */
		if(video_conv_buf==NULL)
			video_conv_buf = (char *)malloc(codec_ctx->width*codec_ctx->height*4);
		printf("converting video...\n");
		miles_image_convert(video_out_buf, video_conv_buf, grabber->image_format, codec_ctx->input_format, codec_ctx->width, codec_ctx->height);
		video_buf_ptr = video_conv_buf;
	} else {
		video_buf_ptr = video_out_buf;
	}
	n = miles_video_codec_encode(codec_ctx, video_buf_ptr, encoded_out_img);
	if(n<=0)
		return 0;
	return miles_rtp_send(rtp_stream, encoded_out_img, n);
}

/**
 * Send RTP audio stream
 */
int MilesSessionInvoker::audio_transmitter(struct miles_audio_device *dev, struct miles_audio_codec_encode_context *codec_ctx, struct miles_rtp_out_stream *rtp_stream, struct miles_rtcp_out_stream *out_rtcp_audio_stream) {
	int n;

	/* Send RTCP packets, if due */
	miles_rtp_send_rtcp(out_rtcp_audio_stream);

	n = miles_audio_device_read(MILES_AUDIO_IO_OPENAL, dev, audio_read_buf, codec_ctx->chunk_size);
	if(n <= 0)
		return 0;
	if(dev->format != codec_ctx->input_format) {
		/* audio conversion needed ... */
	}
	n = miles_audio_codec_encode(codec_ctx, audio_read_buf, encoded_out_audio);
	if(n<=0)
		return 0;
	return miles_rtp_send(rtp_stream, encoded_out_audio, n);
}


}
