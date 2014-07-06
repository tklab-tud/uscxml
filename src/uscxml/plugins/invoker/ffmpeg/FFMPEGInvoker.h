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

#ifndef FFMPEGINVOKER_H_VQD1V1C2
#define FFMPEGINVOKER_H_VQD1V1C2

#include <uscxml/Interpreter.h>

extern "C" {
#include <libavutil/avutil.h>
#include <libavformat/avformat.h>
#include <libswscale/swscale.h>
}

#ifdef BUILD_AS_PLUGINS
#include "uscxml/plugins/Plugins.h"
#endif

namespace uscxml {

class FFMPEGInvoker : public InvokerImpl {
public:
	FFMPEGInvoker();
	virtual ~FFMPEGInvoker();
	virtual boost::shared_ptr<InvokerImpl> create(InterpreterImpl* interpreter);

	virtual std::list<std::string> getNames() {
		std::list<std::string> names;
		names.push_back("ffmpeg");
		names.push_back("http://uscxml.tk.informatik.tu-darmstadt.de/#ffmpeg");
		return names;
	}

	virtual Data getDataModelVariables();
	virtual void send(const SendRequest& req);
	virtual void cancel(const std::string sendId);
	virtual void invoke(const InvokeRequest& req);

protected:
	class EncodingContext {
	public:
		EncodingContext() :
			format(NULL),
			formatCtx(NULL),
			audioStream(NULL), videoStream(NULL),
			audioCodec(NULL), videoCodec(NULL),
			audioTime(0), videoTime(0),
			frame(NULL),
			frame_count(0),
			width(0),
			height(0),
			sws_flags(SWS_BICUBIC),
			sws_ctx(NULL) {}

		virtual ~EncodingContext() {
			if (sws_ctx)
				sws_freeContext(sws_ctx);
		}

		tthread::recursive_mutex mutex;
		PixelFormat videoPixFmt;
		std::string filename;
		AVOutputFormat* format;
		AVFormatContext* formatCtx;
		AVStream *audioStream, *videoStream;
		AVCodec *audioCodec, *videoCodec, *imageCodec;
		double audioTime, videoTime;
		AVFrame *frame;
		AVPicture src_picture, dst_picture;
		int frame_count;
		size_t width, height;
		int sws_flags;
		SwsContext *sws_ctx;
		std::string extension;
	};

	AVStream* addStream(EncodingContext* ctx, AVFormatContext *oc, AVCodec **codec, enum AVCodecID codec_id);
	void openVideo(EncodingContext* ctx, AVFormatContext *oc, AVCodec *codec, AVStream *st);
	void writeVideoFrame(EncodingContext* ctx, AVFormatContext *oc, AVStream *st, Blob image);
	void closeVideo(EncodingContext* ctx, AVFormatContext *oc, AVStream *st);

	static void run(void*);
	void finish(EncodingContext* ctx, const SendRequest& req);
	void process(const SendRequest& req);

	std::set<tthread::thread*> _threads;
	uscxml::concurrency::BlockingQueue<SendRequest> _workQueue;
	bool _isRunning;
	std::map<std::string, EncodingContext*> _encoders;
};

#ifdef BUILD_AS_PLUGINS
PLUMA_INHERIT_PROVIDER(FFMPEGInvoker, InvokerImpl);
#endif

}


#endif /* end of include guard: FFMPEGINVOKER_H_VQD1V1C2 */
