find_path(LIBJINGLE_INCLUDE_DIR 
	NAMES 
		talk/app/webrtc/peerconnectioninterface.h
	HINTS
		${LIBJINGLE_ROOT_DIR}
		ENV LIBJINGLE_ROOT_DIR
	DOC
		"libjingle include directory path"
)

find_path(LIBJINGLE_THIRD_PARTY_INCLUDE_DIR 
	NAMES 
		webrtc/common_types.h
	HINTS
		${LIBJINGLE_ROOT_DIR}
		ENV LIBJINGLE_ROOT_DIR
	PATH_SUFFIXES
		third_party
	DOC
		"libjingle/third_party include directory path"
)

find_path(LIBJINGLE_WEBRTC_INCLUDE_DIR 
	NAMES 
		common_types.h
	HINTS
		${LIBJINGLE_ROOT_DIR}
		ENV LIBJINGLE_ROOT_DIR
	PATH_SUFFIXES
		third_party/webrtc
		webrtc
	DOC
		"libjingle/third_party/webrtc include directory path"
)

set(REQUIRED_VARS LIBJINGLE_INCLUDE_DIR LIBJINGLE_THIRD_PARTY_INCLUDE_DIR LIBJINGLE_WEBRTC_INCLUDE_DIR)

if(WIN32)
	set(LIBJINGLE_SYSTEM_LIBS
		wininet  
		dnsapi  
		version  
		msimg32  
		ws2_32  
		usp10  
		psapi  
		dbghelp  
		winmm  
		shlwapi  
		kernel32  
		gdi32  
		winspool  
		comdlg32  
		advapi32  
		shell32  
		ole32  
		oleaut32  
		user32  
		uuid  
		odbc32  
		odbccp32  
		delayimp  
		Strmiids  
		dmoguids  
		wmcodecdspuuid  
		amstrmid  
		msdmo
	)
	macro(set_libjingle_libs VARNAME CONFIGURATION)
		set(${VARNAME}
			${LIBJINGLE_SYSTEM_LIBS}
			${LIBJINGLE_ROOT_DIR}/build/${CONFIGURATION}/lib/jsoncpp.lib 
			${LIBJINGLE_ROOT_DIR}/build/${CONFIGURATION}/lib/libjingle_peerconnection.lib 
			${LIBJINGLE_ROOT_DIR}/build/${CONFIGURATION}/lib/libjingle.lib 
			${LIBJINGLE_ROOT_DIR}/build/${CONFIGURATION}/lib/expat.lib 
			${LIBJINGLE_ROOT_DIR}/build/${CONFIGURATION}/lib/crnss.lib 
			${LIBJINGLE_ROOT_DIR}/build/${CONFIGURATION}/lib/nss_static.lib 
			${LIBJINGLE_ROOT_DIR}/build/${CONFIGURATION}/lib/crnspr.lib 
			${LIBJINGLE_ROOT_DIR}/build/${CONFIGURATION}/lib/sqlite3.lib 
			${LIBJINGLE_ROOT_DIR}/build/${CONFIGURATION}/lib/icui18n.lib 
			${LIBJINGLE_ROOT_DIR}/build/${CONFIGURATION}/lib/icuuc.lib 
			${LIBJINGLE_ROOT_DIR}/build/${CONFIGURATION}/lib/libjingle_media.lib 
			${LIBJINGLE_ROOT_DIR}/build/${CONFIGURATION}/lib/libyuv.lib 
			${LIBJINGLE_ROOT_DIR}/build/${CONFIGURATION}/lib/libjpeg.lib 
			${LIBJINGLE_ROOT_DIR}/build/${CONFIGURATION}/lib/video_capture_module.lib 
			${LIBJINGLE_ROOT_DIR}/build/${CONFIGURATION}/lib/webrtc_utility.lib 
			${LIBJINGLE_ROOT_DIR}/build/${CONFIGURATION}/lib/audio_coding_module.lib 
			${LIBJINGLE_ROOT_DIR}/build/${CONFIGURATION}/lib/CNG.lib 
			${LIBJINGLE_ROOT_DIR}/build/${CONFIGURATION}/lib/signal_processing.lib 
			${LIBJINGLE_ROOT_DIR}/build/${CONFIGURATION}/lib/system_wrappers.lib 
			${LIBJINGLE_ROOT_DIR}/build/${CONFIGURATION}/lib/G711.lib 
			${LIBJINGLE_ROOT_DIR}/build/${CONFIGURATION}/lib/G722.lib 
			${LIBJINGLE_ROOT_DIR}/build/${CONFIGURATION}/lib/iLBC.lib 
			${LIBJINGLE_ROOT_DIR}/build/${CONFIGURATION}/lib/iSAC.lib 
			${LIBJINGLE_ROOT_DIR}/build/${CONFIGURATION}/lib/iSACFix.lib 
			${LIBJINGLE_ROOT_DIR}/build/${CONFIGURATION}/lib/PCM16B.lib 
			${LIBJINGLE_ROOT_DIR}/build/${CONFIGURATION}/lib/NetEq.lib 
			${LIBJINGLE_ROOT_DIR}/build/${CONFIGURATION}/lib/resampler.lib 
			${LIBJINGLE_ROOT_DIR}/build/${CONFIGURATION}/lib/vad.lib 
			${LIBJINGLE_ROOT_DIR}/build/${CONFIGURATION}/lib/webrtc_opus.lib 
			${LIBJINGLE_ROOT_DIR}/build/${CONFIGURATION}/lib/opus.lib 
			${LIBJINGLE_ROOT_DIR}/build/${CONFIGURATION}/lib/webrtc_video_coding.lib 
			${LIBJINGLE_ROOT_DIR}/build/${CONFIGURATION}/lib/webrtc_i420.lib 
			${LIBJINGLE_ROOT_DIR}/build/${CONFIGURATION}/lib/common_video.lib 
			${LIBJINGLE_ROOT_DIR}/build/${CONFIGURATION}/lib/video_coding_utility.lib 
			${LIBJINGLE_ROOT_DIR}/build/${CONFIGURATION}/lib/webrtc_vp8.lib 
			${LIBJINGLE_ROOT_DIR}/build/${CONFIGURATION}/lib/libvpx.lib 
			${LIBJINGLE_ROOT_DIR}/build/${CONFIGURATION}/lib/libvpx_asm_offsets.lib 
			${LIBJINGLE_ROOT_DIR}/build/${CONFIGURATION}/lib/libvpx_asm_offsets_vp9.lib 
			${LIBJINGLE_ROOT_DIR}/build/${CONFIGURATION}/lib/libvpx_intrinsics.lib 
			${LIBJINGLE_ROOT_DIR}/build/${CONFIGURATION}/lib/directshow_baseclasses.lib 
			${LIBJINGLE_ROOT_DIR}/build/${CONFIGURATION}/lib/video_render_module.lib 
			${LIBJINGLE_ROOT_DIR}/build/${CONFIGURATION}/lib/video_engine_core.lib 
			${LIBJINGLE_ROOT_DIR}/build/${CONFIGURATION}/lib/media_file.lib 
			${LIBJINGLE_ROOT_DIR}/build/${CONFIGURATION}/lib/rtp_rtcp.lib 
			${LIBJINGLE_ROOT_DIR}/build/${CONFIGURATION}/lib/remote_bitrate_estimator.lib 
			${LIBJINGLE_ROOT_DIR}/build/${CONFIGURATION}/lib/paced_sender.lib 
			${LIBJINGLE_ROOT_DIR}/build/${CONFIGURATION}/lib/udp_transport.lib 
			${LIBJINGLE_ROOT_DIR}/build/${CONFIGURATION}/lib/bitrate_controller.lib 
			${LIBJINGLE_ROOT_DIR}/build/${CONFIGURATION}/lib/video_processing.lib 
			${LIBJINGLE_ROOT_DIR}/build/${CONFIGURATION}/lib/video_processing_sse2.lib 
			${LIBJINGLE_ROOT_DIR}/build/${CONFIGURATION}/lib/voice_engine_core.lib 
			${LIBJINGLE_ROOT_DIR}/build/${CONFIGURATION}/lib/audio_conference_mixer.lib 
			${LIBJINGLE_ROOT_DIR}/build/${CONFIGURATION}/lib/audio_processing.lib 
			${LIBJINGLE_ROOT_DIR}/build/${CONFIGURATION}/lib/audioproc_debug_proto.lib 
			${LIBJINGLE_ROOT_DIR}/build/${CONFIGURATION}/lib/protobuf_lite.lib 
			${LIBJINGLE_ROOT_DIR}/build/${CONFIGURATION}/lib/audio_processing_sse2.lib 
			${LIBJINGLE_ROOT_DIR}/build/${CONFIGURATION}/lib/audio_device.lib 
			${LIBJINGLE_ROOT_DIR}/build/${CONFIGURATION}/lib/libjingle_sound.lib 
			${LIBJINGLE_ROOT_DIR}/build/${CONFIGURATION}/lib/libjingle_p2p.lib 
			${LIBJINGLE_ROOT_DIR}/build/${CONFIGURATION}/lib/libsrtp.lib
		)
	endmacro()
	set_libjingle_libs(LIBJINGLE_LIBRARIES_RELEASE Release)
	set_libjingle_libs(LIBJINGLE_LIBRARIES_DEBUG Debug)
	set_libjingle_libs(LIBJINGLE_LIBRARIES ${CMAKE_BUILD_TYPE})
endif()

# handle the QUIETLY and REQUIRED arguments and set SOFIA_SIP_UA_FOUND to TRUE if
# all listed variables are TRUE
include(FindPackageHandleStandardArgs)
FIND_PACKAGE_HANDLE_STANDARD_ARGS(LIBJINGLE
                                  REQUIRED_VARS ${REQUIRED_VARS})

# Copy the results to the output variables.
if(LIBJINGLE_FOUND)
  set(LIBJINGLE_INCLUDE_DIRS ${LIBJINGLE_INCLUDE_DIR} ${LIBJINGLE_THIRD_PARTY_INCLUDE_DIR} ${LIBJINGLE_WEBRTC_INCLUDE_DIR})
endif()

mark_as_advanced(${REQUIRED_VARS})