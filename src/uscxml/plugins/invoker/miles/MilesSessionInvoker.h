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

#ifndef MILESSESIONINVOKER_H_W09J90F0
#define MILESSESIONINVOKER_H_W09J90F0

#include <uscxml/Interpreter.h>

extern "C" {
#include "miles/miles.h"
#include "miles/network.h"
#include "miles/rtp.h"
#include "miles/audio_codec.h"
#include "miles/audio_device.h"
#include "miles/video_codec.h"
#include "miles/video_grabber.h"
#include "miles/session.h"
#include "miles/image.h"
}
#ifdef BUILD_AS_PLUGINS
#include "uscxml/plugins/Plugins.h"
#endif

namespace uscxml {

class MilesSessionInvoker : public InvokerImpl {
public:
	MilesSessionInvoker();
	virtual ~MilesSessionInvoker();
	virtual boost::shared_ptr<InvokerImpl> create(InterpreterImpl* interpreter);

	virtual std::set<std::string> getNames() {
		std::set<std::string> names;
		names.insert("miles");
		names.insert("http://uscxml.tk.informatik.tu-darmstadt.de/#miles");
		return names;
	}

	virtual Data getDataModelVariables();
	virtual void send(const SendRequest& req);
	virtual void cancel(const std::string sendId);
	virtual void invoke(const InvokeRequest& req);

protected:
	bool alternate; // this is to alternate test1 an test2.jpeg and has no other use! remove me later ..

	int video_rtp_in_socket, audio_rtp_in_socket;
	int video_rtp_out_socket, audio_rtp_out_socket;
	int video_rtcp_in_socket, audio_rtcp_in_socket;
	int video_rtcp_out_socket, audio_rtcp_out_socket;
	struct miles_rtp_session *video_session, *audio_session;
	struct miles_video_codec_encode_context *video_encoder;
	struct miles_audio_codec_encode_context *audio_encoder;
	int *supported_video_grabbers;
	struct miles_video_grabber_context *video_grabber;
	struct miles_rtp_out_stream *out_rtp_video_stream, *out_rtp_audio_stream;
	struct miles_rtcp_out_stream *out_rtcp_video_stream, *out_rtcp_audio_stream;
	struct miles_audio_device *audio_dev;
	struct miles_audio_device_description *supported_audio_devices;
	int video_port, audio_port;
	std::string ip_address;

	char video_out_buf[1000000];
	char encoded_out_img[1000000];
	char decoded_in_img[1000000];
	char audio_in_buf[1000000];
	char render_img[1000000];
	char audio_data[1000000];
	char video_data[1000000];

	char encoded_out_audio[1000000];
	char audio_read_buf[1000000];

	struct miles_audio_device *audio_dev_playback;
	int audio_dev_playback_id;

	static void runAudio(void* instance);
	static void runVideo(void* instance);
	void processVideo();
	void processAudio();

	void render_video_image(u_int32_t ssrc, char *img, int width, int height, int img_format);
	void playback_audio(u_int32_t ssrc, char *buf, int sample_rate, int bps, int audio_format, int size);
	int video_receiver(struct miles_rtp_in_stream *rtp_stream, char *data, int bytes_read);
	int audio_receiver(struct miles_rtp_in_stream *rtp_stream, char *data, int bytes_read);
	void rtp_audio_receiver(struct miles_rtp_session *rtp_session);
	void rtp_video_receiver(struct miles_rtp_session *rtp_session);
	int video_transmitter(struct miles_video_grabber_context *grabber, struct miles_video_codec_encode_context *codec_ctx, struct miles_rtp_out_stream *rtp_stream, struct miles_rtcp_out_stream *out_rtcp_stream);
	int audio_transmitter(struct miles_audio_device *dev, struct miles_audio_codec_encode_context *codec_ctx, struct miles_rtp_out_stream *rtp_stream, struct miles_rtcp_out_stream *out_rtcp_audio_stream);


	bool _isRunning;
	tthread::thread* _videoThread;
	tthread::thread* _audioThread;
	tthread::recursive_mutex _mutex;
};

#ifdef BUILD_AS_PLUGINS
PLUMA_INHERIT_PROVIDER(MilesSessionInvoker, InvokerImpl);
#endif

}


#endif /* end of include guard: MILESSESIONINVOKER_H_W09J90F0 */
