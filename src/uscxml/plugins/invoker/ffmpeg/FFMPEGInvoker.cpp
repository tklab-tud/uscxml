#include "FFMPEGInvoker.h"
#include <glog/logging.h>

#include <libavutil/imgutils.h>
#include <libavcodec/avcodec.h>
#include <fstream>

#ifdef BUILD_AS_PLUGINS
#include <Pluma/Connector.hpp>
#endif

#define STREAM_FRAME_RATE 25 /* 25 images/s */
#define BMP_FORMAT        PIX_FMT_BGR24

namespace uscxml {

#ifdef BUILD_AS_PLUGINS
PLUMA_CONNECTOR
bool connect(pluma::Host& host) {
	host.add( new FFMPEGInvokerProvider() );
	return true;
}
#endif

FFMPEGInvoker::FFMPEGInvoker() {
}

FFMPEGInvoker::~FFMPEGInvoker() {
};

boost::shared_ptr<InvokerImpl> FFMPEGInvoker::create(InterpreterImpl* interpreter) {
	boost::shared_ptr<FFMPEGInvoker> invoker = boost::shared_ptr<FFMPEGInvoker>(new FFMPEGInvoker());
	// Register all formats and codecs - this ought to be done just once
	av_register_all();
	return invoker;
}

Data FFMPEGInvoker::getDataModelVariables() {
	Data data;

	AVCodec* codec = NULL;
	while((codec = av_codec_next(codec))) {
		AVCodec* codecInst = avcodec_find_encoder(codec->id);
		if (!codecInst)
			continue;
		
		switch (codec->type) {
			case AVMEDIA_TYPE_VIDEO: {
				Data codecData;
				codecData.compound["name"] = Data(codec->name, Data::VERBATIM);
				codecData.compound["longName"] = Data(codec->long_name, Data::VERBATIM);
				data.compound["video"].compound[codec->name] = codecData;
				break;
			}
			case AVMEDIA_TYPE_AUDIO: {
				Data codecData;
				codecData.compound["name"] = Data(codec->name, Data::VERBATIM);
				codecData.compound["longName"] = Data(codec->long_name, Data::VERBATIM);
				data.compound["audio"].compound[codec->name] = codecData;
				break;
			}
			default:
				break;
		}
	}
	
	return data;
}

void FFMPEGInvoker::invoke(const InvokeRequest& req) {
	int nrThreads = 1;
	Event::getParam(req.params, "threads", nrThreads);
	
	_isRunning = true;
	for (int i = 0; i < nrThreads; i++) {
		_threads.insert(new tthread::thread(FFMPEGInvoker::run, this));
	}
}
	
void FFMPEGInvoker::send(const SendRequest& req) {
	SendRequest reqCopy = req;
	
	if (boost::iequals(req.name, "render.start")) {
		// create a new encoding context
		int ret;
		EncodingContext* ctx = new EncodingContext();
		tthread::lock_guard<tthread::recursive_mutex> lock(ctx->mutex);

		std::string context;
		Event::getParam(req.params, "context", context);

		ctx->extension = "mpeg";
		Event::getParam(req.params, "format", ctx->extension);

		Event::getParam(req.params, "width", ctx->width);
		Event::getParam(req.params, "height", ctx->height);

		if (!ctx->width || !ctx->height)
			return;
		
		ctx->filename = URL::getTmpFilename();
				
    /* allocate the output media context */
    avformat_alloc_output_context2(&ctx->formatCtx, NULL, ctx->extension.c_str(), ctx->filename.c_str());
    if (!ctx->formatCtx) {
			printf("Could not deduce output format from file extension: using MPEG.\n");
			avformat_alloc_output_context2(&ctx->formatCtx, NULL, "mpeg", ctx->filename.c_str());
    }
    if (!ctx->formatCtx) {
			return;
    }
    ctx->format = ctx->formatCtx->oformat;
		
    /* Add the audio and video streams using the default format codecs
     * and initialize the codecs. */
    ctx->videoStream = NULL;
		
    if (ctx->format->video_codec != AV_CODEC_ID_NONE) {
			ctx->videoStream = addStream(ctx, ctx->formatCtx, &ctx->videoCodec, ctx->format->video_codec);
    }
		
    /* Now that all the parameters are set, we can open the audio and
     * video codecs and allocate the necessary encode buffers. */
    if (ctx->videoStream)
			openVideo(ctx, ctx->formatCtx, ctx->videoCodec, ctx->videoStream);
		
    /* open the output file, if needed */
    if (!(ctx->format->flags & AVFMT_NOFILE)) {
			ret = avio_open(&ctx->formatCtx->pb, ctx->filename.c_str(), AVIO_FLAG_WRITE);
			if (ret < 0) {
        // fprintf(stderr, "Could not open '%s': %s\n", ctx->filename.c_str(),
        //        av_err2str(ret));
				return;
			}
    }
		
    /* Write the stream header, if any. */
    ret = avformat_write_header(ctx->formatCtx, NULL);
    if (ret < 0) {
      // fprintf(stderr, "Error occurred when opening output file: %s\n",
      //        av_err2str(ret));
			return;
    }
		
    if (ctx->frame)
			ctx->frame->pts = 0;

		_encoders[context] = ctx;
	} else if(boost::iequals(req.name, "render.frame")) {
		_workQueue.push(req);
	} else if(boost::iequals(req.name, "render.end")) {
		_workQueue.push(req);
	}
}

void FFMPEGInvoker::cancel(const std::string sendId) {
}

void FFMPEGInvoker::run(void* instance) {
	FFMPEGInvoker* INSTANCE = (FFMPEGInvoker*)instance;
	while(true) {
		SendRequest req = INSTANCE->_workQueue.pop();
		if (INSTANCE->_isRunning) {
			INSTANCE->process(req);
		} else {
			return;
		}
	}
}

void FFMPEGInvoker::finish(EncodingContext* ctx, const SendRequest& req) {
	av_write_trailer(ctx->formatCtx);
	
	/* Close each codec. */
	if (ctx->videoStream)
		closeVideo(ctx, ctx->formatCtx, ctx->videoStream);
	
	if (!(ctx->formatCtx->oformat->flags & AVFMT_NOFILE))
	/* Close the output file. */
		avio_close(ctx->formatCtx->pb);
	
	/* free the stream */
	avformat_free_context(ctx->formatCtx);
	
	// read file
	std::ifstream movieFile(ctx->filename.c_str());
	movieFile.seekg(0, std::ios::end);
	size_t length = movieFile.tellg();
	movieFile.seekg(0, std::ios::beg);
	
	char* movieBuffer = (char*)malloc(length);
	movieFile.read(movieBuffer, length);
	
	// move to desktop for checking
//	int err = rename(ctx->filename.c_str(), "/Users/sradomski/Desktop/foo.mpg");
//	if (err) {
//		printf("%s", strerror(errno));
//	}
	
	std::string context;
	Event::getParam(req.params, "context", context);

	Event event;
	event.name = "render.done";
	event.data.compound["context"] = context;
	event.data.compound["movie"] = Data(movieBuffer, length, true);
	event.data.compound["mimetype"] = Data("video/mpeg", Data::VERBATIM);
	event.data.compound["filename"] = Data(std::string("movie.") + ctx->extension, Data::VERBATIM);
	
	returnEvent(event);
}

void FFMPEGInvoker::process(const SendRequest& req) {

	std::string context;
	Event::getParam(req.params, "context", context);
	if (_encoders.find(context) == _encoders.end()) {
		return;
	}
	
	EncodingContext* ctx = _encoders[context];
	tthread::lock_guard<tthread::recursive_mutex> lock(ctx->mutex);

	// finish encoding and return
	if(boost::iequals(req.name, "render.end")) {
		finish(ctx, req);
		delete _encoders[context];
		_encoders.erase(context);
	}
	
	Data image;
	Event::getParam(req.params, "frame", image);
	if (!image) {
		return;
	}

	std::string format = "bmp";
	Event::getParam(req.params, "format", format);
	
	writeVideoFrame(ctx, ctx->formatCtx, ctx->videoStream, image.binary);
	ctx->frame->pts += av_rescale_q(1, ctx->videoStream->codec->time_base, ctx->videoStream->time_base);

}
	
AVStream* FFMPEGInvoker::addStream(EncodingContext* ctx, AVFormatContext *oc, AVCodec **codec,
																						 enum AVCodecID codec_id) {
	AVCodecContext *c;
	AVStream *st;
	
	/* find the encoder */
	*codec = avcodec_find_encoder(codec_id);
	if (!(*codec)) {
		fprintf(stderr, "Could not find encoder for '%s'\n",
						avcodec_get_name(codec_id));
		return NULL;
	}
	
	st = avformat_new_stream(oc, *codec);
	ctx->videoPixFmt = (*codec)->pix_fmts[0];
	if (!st) {
		fprintf(stderr, "Could not allocate stream\n");
		return NULL;
	}
	st->id = oc->nb_streams-1;
	c = st->codec;
	
	switch ((*codec)->type) {
    case AVMEDIA_TYPE_AUDIO:
			c->sample_fmt  = AV_SAMPLE_FMT_FLTP;
			c->bit_rate    = 64000;
			c->sample_rate = 44100;
			c->channels    = 2;
			break;
			
    case AVMEDIA_TYPE_VIDEO:
			c->codec_id = codec_id;
						
			c->bit_rate = 800000;
			/* Resolution must be a multiple of two. */
			c->width    = ctx->width;
			c->height   = ctx->height;
			/* timebase: This is the fundamental unit of time (in seconds) in terms
			 * of which frame timestamps are represented. For fixed-fps content,
			 * timebase should be 1/framerate and timestamp increments should be
			 * identical to 1. */
			c->time_base.den = STREAM_FRAME_RATE;
			c->time_base.num = 1;
			c->gop_size      = 12; /* emit one intra frame every twelve frames at most */
			c->pix_fmt       = ctx->videoPixFmt;
			if (c->codec_id == AV_CODEC_ID_MPEG2VIDEO) {
				/* just for testing, we also add B frames */
				c->max_b_frames = 2;
			}
			if (c->codec_id == AV_CODEC_ID_MPEG1VIDEO) {
				/* Needed to avoid using macroblocks in which some coeffs overflow.
				 * This does not happen with normal video, it just happens here as
				 * the motion of the chroma plane does not match the luma plane. */
				c->mb_decision = 2;
			}
			break;
			
    default:
			break;
	}
	
	/* Some formats want stream headers to be separate. */
	if (oc->oformat->flags & AVFMT_GLOBALHEADER)
		c->flags |= CODEC_FLAG_GLOBAL_HEADER;
	
	return st;
}

void FFMPEGInvoker::openVideo(EncodingContext* ctx, AVFormatContext *oc, AVCodec *codec, AVStream *st) {
	int ret;
	AVCodecContext *c = st->codec;

	/* open the codec */
	ret = avcodec_open2(c, codec, NULL);
	if (ret < 0) {
    // fprintf(stderr, "Could not open video codec: %s\n", av_err2str(ret));
		return;
	}

	/* allocate and init a re-usable frame */
	ctx->frame = avcodec_alloc_frame();
	if (!ctx->frame) {
		fprintf(stderr, "Could not allocate video frame\n");
		return;
	}

	/* Allocate the encoded raw picture. */
	ret = avpicture_alloc(&ctx->dst_picture, c->pix_fmt, c->width, c->height);
	if (ret < 0) {
//		fprintf(stderr, "Could not allocate picture: %s\n", av_err2str(ret));
		return;
	}

	/* If the output format is not YUV420P, then a temporary YUV420P
	 * picture is needed too. It is then converted to the required
	 * output format. */
	if (c->pix_fmt != BMP_FORMAT) {
		ret = avpicture_alloc(&ctx->src_picture, BMP_FORMAT, c->width, c->height);
		if (ret < 0) {
      // fprintf(stderr, "Could not allocate temporary picture: %s\n",
      //         av_err2str(ret));
			return;
		}
	}

	/* copy data and linesize picture pointers to frame */
	*((AVPicture *)ctx->frame) = ctx->dst_picture;
}
	
void FFMPEGInvoker::writeVideoFrame(EncodingContext* ctx, AVFormatContext *oc, AVStream *st, boost::shared_ptr<Blob> image) {
	int ret;
	AVCodecContext *c = st->codec;

	if (c->pix_fmt != BMP_FORMAT) {
		/* as we only generate a YUV420P picture, we must convert it
		 * to the codec pixel format if needed */
		if (!ctx->sws_ctx) {
			ctx->sws_ctx = sws_getContext(c->width, c->height, BMP_FORMAT,
															 c->width, c->height, c->pix_fmt,
															 ctx->sws_flags, NULL, NULL, NULL);
			if (!ctx->sws_ctx) {
				fprintf(stderr,
								"Could not initialize the conversion context\n");
				return;
			}
		}

		uint32_t headerOffset = 0;
		headerOffset += image->_data[10] << 0;
		headerOffset += image->_data[11] << 8;
		headerOffset += image->_data[12] << 16;
		headerOffset += image->_data[13] << 24;

//		std::cout << headerOffset + (c->width * c->height) << " / " << image->_size << std::endl;
		
		ret = avpicture_fill(&ctx->src_picture, (uint8_t*)(image->_data + headerOffset), BMP_FORMAT, c->width, c->height);
		if (ret < 0) {
			fprintf(stderr,
							"Could not fill image from given bitmap\n");
		}
		sws_scale(ctx->sws_ctx,
							(const uint8_t * const *)ctx->src_picture.data, ctx->src_picture.linesize,
							0, c->height, ctx->dst_picture.data, ctx->dst_picture.linesize);
	} else {
		avpicture_fill(&ctx->dst_picture, (uint8_t*)image->_data, c->pix_fmt, c->width, c->height);
	}

	if (oc->oformat->flags & AVFMT_RAWPICTURE) {
		/* Raw video case - directly store the picture in the packet */
		AVPacket pkt;
		av_init_packet(&pkt);

		pkt.flags        |= AV_PKT_FLAG_KEY;
		pkt.stream_index  = st->index;
		pkt.data          = ctx->dst_picture.data[0];
		pkt.size          = sizeof(AVPicture);

		ret = av_interleaved_write_frame(oc, &pkt);
	} else {
		AVPacket pkt = { 0 };
		int got_packet;
		av_init_packet(&pkt);

		/* encode the image */
		ret = avcodec_encode_video2(c, &pkt, ctx->frame, &got_packet);
		if (ret < 0) {
      // fprintf(stderr, "Error encoding video frame: %s\n", av_err2str(ret));
			return;
		}
		/* If size is zero, it means the image was buffered. */

		if (!ret && got_packet && pkt.size) {
			pkt.stream_index = st->index;

			/* Write the compressed frame to the media file. */
//			ret = av_write_frame(oc, &pkt);
			ret = av_interleaved_write_frame(oc, &pkt);
		} else {
			ret = 0;
		}
	}
	if (ret != 0) {
//		fprintf(stderr, "Error while writing video frame: %s\n", av_err2str(ret));
		return;
	}
	ctx->frame_count++;
}

void FFMPEGInvoker::closeVideo(EncodingContext* ctx, AVFormatContext *oc, AVStream *st) {
	avcodec_close(st->codec);
//	av_free(ctx->src_picture.data[0]);
	av_free(ctx->dst_picture.data[0]);
	av_free(ctx->frame);
}


}