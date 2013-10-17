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

#include "MilesSessionInvoker.h"
#include <glog/logging.h>

#ifdef BUILD_AS_PLUGINS
#include <Pluma/Connector.hpp>
#endif

#include <inttypes.h>

namespace uscxml {

#ifdef BUILD_AS_PLUGINS
PLUMA_CONNECTOR
bool pluginConnect(pluma::Host& host) {
	host.add( new MilesSessionInvokerProvider() );
	return true;
}
#endif

MilesSessionInvoker::MilesSessionInvoker() {
	/* Initalize Miles */
	miles_init();
}

MilesSessionInvoker::~MilesSessionInvoker() {
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

void MilesSessionInvoker::send(const SendRequest& req) {
//	std::cout << req;
	if (boost::iequals(req.name, "disconnect")) {
		std::string reflectorIP = "127.0.0.1";
		Event::getParam(req.params, "reflectorip", reflectorIP);

		std::string problemName = "Generic";
		Event::getParam(req.params, "problemname", problemName);

		int rv;
		rv = miles_disconnect_reflector_session((char*)reflectorIP.c_str(), (char*)problemName.c_str());
		if (!rv) {
			LOG(ERROR) << "Could not disconnect from reflector session";
			return;
		}
	} else if (boost::iequals(req.name, "image")) {
		// client wants an image
		URL imageURL1("test1.jpeg");
		URL imageURL2("test2.jpeg");

		imageURL1.toAbsolute(_interpreter->getBaseURI());
		imageURL2.toAbsolute(_interpreter->getBaseURI());

		std::stringstream ssImage;

		if (alternate) {
			ssImage << imageURL1;
		} else {
			ssImage << imageURL2;
		}
		alternate = !alternate;

		std::string imageContent = ssImage.str();

		Event retEv;
		retEv.data.compound["base64"] = Data(base64_encode(imageContent.data(), imageContent.size()), Data::VERBATIM);

		std::string origin;
		Event::getParam(req.params, "origin", origin);
		retEv.data.compound["origin"] = origin;

		tthread::this_thread::sleep_for(tthread::chrono::milliseconds(20));

		returnEvent(retEv);

	} else if (boost::iequals(req.name, "connect")) {
		std::string email = "someSaneDefault";
		Event::getParam(req.params, "email", email);

		std::string reflectorIP = "127.0.0.1";
		Event::getParam(req.params, "reflectorip", reflectorIP);

		std::string problemName = "Generic";
		Event::getParam(req.params, "problemname", problemName);

		return;

		int rv;
		rv = miles_connect_reflector_session((char*)reflectorIP.c_str(), (char*)problemName.c_str());
		if (!rv) {
			LOG(ERROR) << "Could not setup reflector session";
			return;
		}

		/* Set up audio and video RTP sockets */
		video_rtp_in_socket = miles_net_setup_udp_socket((char*)reflectorIP.c_str(), video_port, video_port, 10, 16000);
		audio_rtp_in_socket = miles_net_setup_udp_socket((char*)reflectorIP.c_str(), audio_port, audio_port, 10, 16000);
		video_rtp_out_socket = video_rtp_in_socket; //miles_net_setup_udp_socket((char*)reflectorIP.c_str(), video_port, 0, 10, 16000);
		audio_rtp_out_socket = audio_rtp_in_socket; //miles_net_setup_udp_socket((char*)reflectorIP.c_str(), audio_port, 0, 10, 16000);

		/* Set up audio and video RTCP sockets */
		video_rtcp_in_socket = miles_net_setup_udp_socket((char*)reflectorIP.c_str(), video_port+1, video_port+1, 10, 16000);
		audio_rtcp_in_socket = miles_net_setup_udp_socket((char*)reflectorIP.c_str(), audio_port+1, audio_port+1, 10, 16000);
		video_rtcp_out_socket = video_rtcp_in_socket; //miles_net_setup_udp_socket((char*)reflectorIP.c_str(), video_port+1, 0, 10, 16000);
		audio_rtcp_out_socket = audio_rtcp_in_socket; //miles_net_setup_udp_socket((char*)reflectorIP.c_str(), audio_port+1, 0, 10, 16000);

		/* Set up RTP audio and video sessions */
		video_session = miles_rtp_setup_session(video_rtp_in_socket, MILES_RTP_MEDIA_TYPE_VIDEO);
		audio_session = miles_rtp_setup_session(audio_rtp_in_socket, MILES_RTP_MEDIA_TYPE_AUDIO);

		/* Set up RTCP audio and video sessions */
		video_session->rtcp_session = miles_rtp_setup_rtcp_session(video_session, video_rtcp_in_socket);
		audio_session->rtcp_session = miles_rtp_setup_rtcp_session(audio_session, audio_rtcp_in_socket);

		/* Initialize and configure video encoder */
		video_encoder = miles_video_codec_init_encoder();
		video_encoder->codec_id = miles_video_codec_get_encoder_for_rtp_payload_type(MILES_RTP_PAYLOAD_TYPE_JPEG);
		video_encoder->width = 320;
		video_encoder->height = 240;
		video_encoder->qfactor = 50;
		rv = miles_video_codec_setup_encoder(video_encoder);
		if (!rv) {
			LOG(ERROR) << "Could not setup video encoder";
			return;
		}

		/* Set up video grabber */
		rv = miles_video_grabber_get_supported_grabbers(&supported_video_grabbers);
		if(rv<=0) {
			/* No video grabber available */
			exit(-1);
		}
		video_grabber = miles_video_grabber_create_context(supported_video_grabbers[0]);
		video_grabber->width = video_encoder->width;
		video_grabber->height = video_encoder->height;
		miles_video_grabber_setup(video_grabber);
		free(supported_video_grabbers);

		/* Set up outgoing RTP stream for video */
		out_rtp_video_stream = miles_rtp_setup_outgoing_stream(video_session, video_rtp_out_socket, 0, MILES_RTP_PAYLOAD_TYPE_JPEG);

		/* Initialize and configure audio encoder */
		audio_encoder = miles_audio_codec_init_encoder();
		audio_encoder->codec_id = miles_audio_codec_get_encoder_for_rtp_payload_type(MILES_RTP_PAYLOAD_TYPE_L16);
		audio_encoder->sample_rate = 16000;
		audio_encoder->bytes_per_sample = 2;
		audio_encoder->chunk_size = 320; /* 20 ms */
		audio_encoder->input_format = MILES_AUDIO_FORMAT_PCM;
		rv = miles_audio_codec_setup_encoder(audio_encoder);
		if(rv == 0) {
			/* Couldn't set up audio codec */
			exit(-1);
		}


		/* Set up audio grabber */
		int n = miles_audio_device_get_supported_devices(MILES_AUDIO_DEVICE_OPENAL, &supported_audio_devices);
		if(n<=0) {
			/* No audio device available */
			exit(-1);
		}
		/* Use first device that supports capture */
		for(int i=0; i<n; i++) {
			audio_dev = miles_audio_device_open(MILES_AUDIO_DEVICE_OPENAL, supported_audio_devices[i].id, MILES_AUDIO_FORMAT_PCM, 16000, 2, 1, 640, 1);
			if(audio_dev)
				break;
		}
		if(audio_dev == NULL)
			exit(-1);

		/* Find first audio device that supports playback */
		for(int i=0; i<n; i++) {
			audio_dev_playback = miles_audio_device_open(MILES_AUDIO_DEVICE_OPENAL, supported_audio_devices[i].id, MILES_AUDIO_FORMAT_PCM, 16000, 2, 1, 640, 0);
			if(audio_dev_playback) {
				audio_dev_playback_id = supported_audio_devices[i].id;
				break;
			}
		}
		if(audio_dev_playback == NULL)
			exit(-1);

		/* Set up outgoing RTP stream for audio */
		out_rtp_audio_stream = miles_rtp_setup_outgoing_stream(audio_session, audio_rtp_out_socket, 0, MILES_RTP_PAYLOAD_TYPE_L16);

		/* Associate RTP stream with codec context */
		out_rtp_audio_stream->codec_ctx = audio_encoder;
		out_rtp_video_stream->codec_ctx = video_encoder;

		/* Set up outgoing RTCP streams for audio and video */
		out_rtcp_audio_stream = miles_rtp_setup_outgoing_rtcp_stream(audio_session->rtcp_session, audio_rtcp_out_socket, out_rtp_audio_stream->ssrc);
		out_rtcp_video_stream = miles_rtp_setup_outgoing_rtcp_stream(video_session->rtcp_session, video_rtcp_out_socket, out_rtp_video_stream->ssrc);

		_isRunning = true;

//		while(true) {
//			rtp_video_receiver(video_session);
//			video_transmitter(video_grabber, video_encoder, out_rtp_video_stream, out_rtcp_video_stream);
//			rtp_audio_receiver(audio_session);
//			audio_transmitter(audio_dev, audio_encoder, out_rtp_audio_stream, out_rtcp_audio_stream);
//		}

		// don't start threads for mockup
//		_audioThread = new tthread::thread(MilesSessionInvoker::runAudio, this);
//		_videoThread = new tthread::thread(MilesSessionInvoker::runVideo, this);
	}
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
		video_transmitter(video_grabber, video_encoder, out_rtp_video_stream, out_rtcp_video_stream);
	}
}

void MilesSessionInvoker::processAudio() {
	while(_isRunning) {
		rtp_audio_receiver(audio_session);
		audio_transmitter(audio_dev, audio_encoder, out_rtp_audio_stream, out_rtcp_audio_stream);
	}
}

void MilesSessionInvoker::cancel(const std::string sendId) {
}

void MilesSessionInvoker::invoke(const InvokeRequest& req) {
	video_port = 5566;
	audio_port = 5568;
}

/**
 * Do something with an image decoded from an RTP stream (e.g. render to screen)
 */
void MilesSessionInvoker::render_video_image(u_int32_t ssrc, char *img, int width, int height, int img_format) {

	if(img_format != MILES_IMAGE_RGBA) {
		miles_image_convert(img, render_img, img_format, MILES_IMAGE_RGBA, width, height);
		stbi_write_png("/Users/sradomski/Desktop/image.png", width, height, 3, render_img, width * 3);
	} else {
		stbi_write_png("/Users/sradomski/Desktop/image.png", width, height, 3, img, width * 3);
	}

	/* render image... */
}

/**
 * Send an audio chunk decoded from an RTP stream to an audio device
 */
void MilesSessionInvoker::playback_audio(u_int32_t ssrc, char *buf, int sample_rate, int bps, int audio_format, int size) {
	int n;

	if(size<0)
		return;

	/* re-configure audio device, if needed */
	if(audio_dev_playback == NULL || audio_dev_playback->chunk_size != size || audio_dev_playback->sample_rate != sample_rate ||
	        audio_dev_playback->format != audio_format ||	audio_dev_playback->bytes_per_sample != bps) {
		if(audio_dev_playback)
			miles_audio_device_close(MILES_AUDIO_DEVICE_OPENAL, audio_dev_playback, 0);
		audio_dev_playback = miles_audio_device_open(MILES_AUDIO_DEVICE_OPENAL, audio_dev_playback_id, audio_format, sample_rate, bps, 1, size, 0);
		if(audio_dev_playback == NULL)
			return;
	}

	/* play audio */
	n = miles_audio_device_write(MILES_AUDIO_DEVICE_OPENAL, audio_dev_playback, buf, size);
}

/**
 * Handle incoming video streams
 */

int MilesSessionInvoker::video_receiver(struct miles_rtp_in_stream *rtp_stream, char *data, int bytes_read) {
	int status, n;
	struct miles_video_codec_decode_context *codec_ctx;

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
	n = miles_video_codec_decode(codec_ctx, data, decoded_in_img, bytes_read);
	if(n > 0) {
		render_video_image(rtp_stream->ssrc, decoded_in_img, codec_ctx->width, codec_ctx->height, codec_ctx->output_format);
	}
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
	int n, m=0;
	struct miles_rtp_in_stream *rtp_stream;

	/* Poll RTP socket, read all available RTP packets */
	while (1) {
		n = miles_net_poll_socket(rtp_session->socket);
		if(n<=0) return;

		/* Read RTP data */
		n = miles_rtp_recv(rtp_session, &rtp_stream, audio_data);
		if(n>0) {
			m = audio_receiver(rtp_stream, audio_data, n);
		}

		/* Poll RTCP socket */
		n = miles_net_poll_socket(rtp_session->rtcp_session->socket);
		if(n>0) {
			/* Do RTCP packet processing */
			n = miles_rtp_recv_rtcp(rtp_session->rtcp_session);
		}
	}
}

void MilesSessionInvoker::rtp_video_receiver(struct miles_rtp_session *rtp_session) {
	int n, m=0;
	struct miles_rtp_in_stream *rtp_stream;

	/* Poll RTP socket, read all available RTP packets */
	while (1) {
		n = miles_net_poll_socket(rtp_session->socket);
		if(n<=0) return;

		/* Read RTP data */
		n = miles_rtp_recv(rtp_session, &rtp_stream, video_data);
		if(n>0) {
			m = video_receiver(rtp_stream, video_data, n);
		}

		/* Poll RTCP socket */
		n = miles_net_poll_socket(rtp_session->rtcp_session->socket);
		if(n>0) {
			/* Do RTCP packet processing */
			n = miles_rtp_recv_rtcp(rtp_session->rtcp_session);
		}
	}
}

/**
 * Send RTP video stream
 */
int MilesSessionInvoker::video_transmitter(struct miles_video_grabber_context *grabber, struct miles_video_codec_encode_context *codec_ctx, struct miles_rtp_out_stream *rtp_stream, struct miles_rtcp_out_stream *out_rtcp_stream) {
	int n;

	/* Send RTCP packets, if due */
	miles_rtp_send_rtcp(out_rtcp_stream);

	n = miles_video_grabber_grab(grabber, video_out_buf);
	if(n <= 0)
		return 0;
	if(grabber->image_format != codec_ctx->input_format) {
		/* image conversion ... */
	}
	n = miles_video_codec_encode(codec_ctx, video_out_buf, encoded_out_img);
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

	n = miles_audio_device_read(MILES_AUDIO_DEVICE_OPENAL, dev, audio_read_buf, codec_ctx->chunk_size);
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