#include "uscxml/plugins/ioprocessor/modality/MMIMessages.h"

#include <SAX/helpers/InputSourceResolver.hpp>
#include <DOM/SAX2DOM/SAX2DOM.hpp>
#include <DOM/io/Stream.hpp>

#include <assert.h>
#include <boost/algorithm/string.hpp>
#include <iostream>

using namespace uscxml;
using namespace boost;

Arabica::DOM::Document<std::string> xmlToDoc(const std::string& xml) {
	std::stringstream* ss = new std::stringstream();
	(*ss) << xml;
	std::auto_ptr<std::istream> ssPtr(ss);
	Arabica::SAX::InputSource<std::string> inputSource;
	inputSource.setByteStream(ssPtr);

	Arabica::SAX2DOM::Parser<std::string> parser;
	parser.parse(inputSource);
	return parser.getDocument();
}

int main(int argc, char** argv) {
	{
		// --- NewContextRequest
		std::stringstream ss;
		ss << "<mmi:mmi xmlns:mmi=\"http://www.w3.org/2008/04/mmi-arch\" version=\"1.0\"><mmi:NewContextRequest mmi:Source=\"someURI\" mmi:Target=\"someOtherURI\" mmi:RequestID=\"request-1\"></mmi:NewContextRequest></mmi:mmi>";
		NewContextRequest msg = NewContextRequest::fromXML(xmlToDoc(ss.str()));
		assert(boost::iequals(msg.tagName, "NewContextRequest"));
		assert(boost::iequals(msg.source, "someURI"));
		assert(boost::iequals(msg.target, "someOtherURI"));
		assert(boost::iequals(msg.requestId, "request-1"));
		assert(boost::iequals(msg.data, ""));

		NewContextRequest msg2 = NewContextRequest::fromXML(msg.toXML());
		assert(boost::iequals(msg2.tagName, "NewContextRequest"));
		assert(boost::iequals(msg2.source, "someURI"));
		assert(boost::iequals(msg2.target, "someOtherURI"));
		assert(boost::iequals(msg2.requestId, "request-1"));
		assert(boost::iequals(msg2.data, ""));
	}

	{
		// --- NewContextResponse
		std::stringstream ss;
		ss << "<mmi:mmi xmlns:mmi=\"http://www.w3.org/2008/04/mmi-arch\" version=\"1.0\"> <mmi:NewContextResponse mmi:Source=\"someURI\" mmi:Target=\"someOtherURI\" mmi:RequestID=\"request-1\" mmi:Status=\"success\" mmi:Context=\"URI-1\"> </mmi:NewContextResponse></mmi:mmi>";
		NewContextResponse msg = NewContextResponse::fromXML(xmlToDoc(ss.str()));
		assert(boost::iequals(msg.tagName, "NewContextResponse"));
		assert(boost::iequals(msg.source, "someURI"));
		assert(boost::iequals(msg.target, "someOtherURI"));
		assert(boost::iequals(msg.requestId, "request-1"));
		assert(msg.status == StatusResponse::SUCCESS);
		assert(boost::iequals(msg.statusInfo, ""));
		assert(boost::iequals(msg.context, "URI-1"));
		assert(boost::iequals(msg.data, ""));

		NewContextResponse msg2 = NewContextResponse::fromXML(msg.toXML());
		assert(boost::iequals(msg2.tagName, "NewContextResponse"));
		assert(boost::iequals(msg2.source, "someURI"));
		assert(boost::iequals(msg2.target, "someOtherURI"));
		assert(boost::iequals(msg2.requestId, "request-1"));
		assert(msg2.status == StatusResponse::SUCCESS);
		assert(boost::iequals(msg2.statusInfo, ""));
		assert(boost::iequals(msg2.context, "URI-1"));
		assert(boost::iequals(msg2.data, ""));

	}

	{
		// --- PrepareRequest
		std::stringstream ss;
		ss << "<mmi:mmi xmlns:mmi=\"http://www.w3.org/2008/04/mmi-arch\" version=\"1.0\"> <mmi:PrepareRequest mmi:Source=\"someURI\" mmi:Target=\"someOtherURI\"  mmi:Context=\"URI-1\" mmi:RequestID=\"request-1\"> <mmi:ContentURL mmi:href=\"someContentURI\" mmi:max-age=\"\" mmi:fetchtimeout=\"1s\"/> </mmi:PrepareRequest></mmi:mmi>";
		PrepareRequest msg = PrepareRequest::fromXML(xmlToDoc(ss.str()));
		assert(boost::iequals(msg.tagName, "PrepareRequest"));
		assert(boost::iequals(msg.source, "someURI"));
		assert(boost::iequals(msg.target, "someOtherURI"));
		assert(boost::iequals(msg.requestId, "request-1"));
		assert(boost::iequals(msg.context, "URI-1"));
		assert(boost::iequals(msg.data, ""));
		assert(boost::iequals(msg.content, ""));
		assert(boost::iequals(msg.contentURL.href, "someContentURI"));
		assert(boost::iequals(msg.contentURL.maxAge, ""));
		assert(boost::iequals(msg.contentURL.fetchTimeout, "1s"));

		PrepareRequest msg2 = PrepareRequest::fromXML(msg.toXML());
		assert(boost::iequals(msg2.tagName, "PrepareRequest"));
		assert(boost::iequals(msg2.source, "someURI"));
		assert(boost::iequals(msg2.target, "someOtherURI"));
		assert(boost::iequals(msg2.requestId, "request-1"));
		assert(boost::iequals(msg2.context, "URI-1"));
		assert(boost::iequals(msg2.data, ""));
		assert(boost::iequals(msg2.content, ""));
		assert(boost::iequals(msg2.contentURL.href, "someContentURI"));
		assert(boost::iequals(msg2.contentURL.maxAge, ""));
		assert(boost::iequals(msg2.contentURL.fetchTimeout, "1s"));

	}

	{
		// --- PrepareRequest
		std::stringstream ss;
		ss << "<mmi:mmi xmlns:mmi=\"http://www.w3.org/2008/04/mmi-arch\" version=\"1.0\" xmlns:vxml=\"http://www.w3.org/2001/vxml\"> <mmi:PrepareRequest mmi:Source=\"someURI\" mmi:Target=\"someOtherURI\"  mmi:Context=\"URI-1\" mmi:RequestID=\"request-1\" > <mmi:content> <vxml:vxml version=\"2.0\"> <vxml:form> <vxml:block>Hello World!</vxml:block> </vxml:form> </vxml:vxml> </mmi:content> </mmi:PrepareRequest></mmi:mmi>";
		PrepareRequest msg = PrepareRequest::fromXML(xmlToDoc(ss.str()));
		assert(boost::iequals(msg.tagName, "PrepareRequest"));
		assert(boost::iequals(msg.source, "someURI"));
		assert(boost::iequals(msg.target, "someOtherURI"));
		assert(boost::iequals(msg.requestId, "request-1"));
		assert(boost::iequals(msg.context, "URI-1"));
		assert(msg.content.size() > 0);

		PrepareRequest msg2 = PrepareRequest::fromXML(msg.toXML());
		assert(boost::iequals(msg2.tagName, "PrepareRequest"));
		assert(boost::iequals(msg2.source, "someURI"));
		assert(boost::iequals(msg2.target, "someOtherURI"));
		assert(boost::iequals(msg2.requestId, "request-1"));
		assert(boost::iequals(msg2.context, "URI-1"));
		assert(msg2.content.size() > 0);

	}

	{
		// --- PrepareResponse
		std::stringstream ss;
		ss << "<mmi:mmi xmlns:mmi=\"http://www.w3.org/2008/04/mmi-arch\" version=\"1.0\"> <mmi:PrepareResponse mmi:Source=\"someURI\" mmi:Target=\"someOtherURI\" mmi:Context=\"someURI\"  mmi:RequestID=\"request-1\" mmi:Status=\"success\"/></mmi:mmi>";
		PrepareResponse msg = PrepareResponse::fromXML(xmlToDoc(ss.str()));
		assert(boost::iequals(msg.tagName, "PrepareResponse"));
		assert(boost::iequals(msg.source, "someURI"));
		assert(boost::iequals(msg.target, "someOtherURI"));
		assert(boost::iequals(msg.requestId, "request-1"));
		assert(boost::iequals(msg.context, "someURI"));
		assert(msg.status == StatusResponse::SUCCESS);

		PrepareResponse msg2 = PrepareResponse::fromXML(msg.toXML());
		assert(boost::iequals(msg2.tagName, "PrepareResponse"));
		assert(boost::iequals(msg2.source, "someURI"));
		assert(boost::iequals(msg2.target, "someOtherURI"));
		assert(boost::iequals(msg2.requestId, "request-1"));
		assert(boost::iequals(msg2.context, "someURI"));
		assert(msg2.status == StatusResponse::SUCCESS);

	}

	{
		// --- PrepareResponse
		std::stringstream ss;
		ss << "<mmi:mmi xmlns:mmi=\"http://www.w3.org/2008/04/mmi-arch\" version=\"1.0\"> <mmi:PrepareResponse mmi:Source=\"someURI\" mmi:Target=\"someOtherURI\" mmi:Context=\"someURI\"  mmi:RequestID=\"request-1\" mmi:Status=\"failure\"> <mmi:statusInfo> NotAuthorized </mmi:statusInfo> </mmi:PrepareResponse></mmi:mmi>";
		PrepareResponse msg = PrepareResponse::fromXML(xmlToDoc(ss.str()));
		assert(boost::iequals(msg.tagName, "PrepareResponse"));
		assert(boost::iequals(msg.source, "someURI"));
		assert(boost::iequals(msg.target, "someOtherURI"));
		assert(boost::iequals(msg.requestId, "request-1"));
		assert(boost::iequals(msg.context, "someURI"));
		assert(boost::iequals(msg.statusInfo, " NotAuthorized "));
		assert(msg.status == StatusResponse::FAILURE);

		PrepareResponse msg2 = PrepareResponse::fromXML(msg.toXML());
		assert(boost::iequals(msg2.tagName, "PrepareResponse"));
		assert(boost::iequals(msg2.source, "someURI"));
		assert(boost::iequals(msg2.target, "someOtherURI"));
		assert(boost::iequals(msg2.requestId, "request-1"));
		assert(boost::iequals(msg2.context, "someURI"));
		assert(boost::iequals(msg2.statusInfo, " NotAuthorized "));
		assert(msg2.status == StatusResponse::FAILURE);

	}

	{
		// --- StartRequest
		std::stringstream ss;
		ss << "<mmi:mmi xmlns:mmi=\"http://www.w3.org/2008/04/mmi-arch\" version=\"1.0\"> <mmi:StartRequest mmi:Source=\"someURI\" mmi:Target=\"someOtherURI\" mmi:Context=\"URI-1\" mmi:RequestID=\"request-1\"> <mmi:ContentURL mmi:href=\"someContentURI\" mmi:max-age=\"\" mmi:fetchtimeout=\"1s\"/> </mmi:StartRequest></mmi:mmi>";
		StartRequest msg = StartRequest::fromXML(xmlToDoc(ss.str()));
		assert(boost::iequals(msg.tagName, "StartRequest"));
		assert(boost::iequals(msg.source, "someURI"));
		assert(boost::iequals(msg.target, "someOtherURI"));
		assert(boost::iequals(msg.requestId, "request-1"));
		assert(boost::iequals(msg.context, "URI-1"));

		StartRequest msg2 = StartRequest::fromXML(msg.toXML());
		assert(boost::iequals(msg2.tagName, "StartRequest"));
		assert(boost::iequals(msg2.source, "someURI"));
		assert(boost::iequals(msg2.target, "someOtherURI"));
		assert(boost::iequals(msg2.requestId, "request-1"));
		assert(boost::iequals(msg2.context, "URI-1"));

	}

	{
		// --- StartResponse
		std::stringstream ss;
		ss << "<mmi:mmi xmlns:mmi=\"http://www.w3.org/2008/04/mmi-arch\" version=\"1.0\"> <mmi:StartResponse mmi:Source=\"someURI\" mmi:Target=\"someOtherURI\" mmi:Context=\"someURI\" mmi:RequestID=\"request-1\"  mmi:Status=\"failure\"> <mmi:statusInfo> NotAuthorized </mmi:statusInfo> </mmi:StartResponse></mmi:mmi>";
		StartResponse msg = StartResponse::fromXML(xmlToDoc(ss.str()));
		assert(boost::iequals(msg.tagName, "StartResponse"));
		assert(boost::iequals(msg.source, "someURI"));
		assert(boost::iequals(msg.target, "someOtherURI"));
		assert(boost::iequals(msg.requestId, "request-1"));
		assert(boost::iequals(msg.context, "someURI"));
		assert(boost::iequals(msg.statusInfo, " NotAuthorized "));
		assert(msg.status == StatusResponse::FAILURE);

		StartResponse msg2 = StartResponse::fromXML(msg.toXML());
		assert(boost::iequals(msg2.tagName, "StartResponse"));
		assert(boost::iequals(msg2.source, "someURI"));
		assert(boost::iequals(msg2.target, "someOtherURI"));
		assert(boost::iequals(msg2.requestId, "request-1"));
		assert(boost::iequals(msg2.context, "someURI"));
		assert(boost::iequals(msg2.statusInfo, " NotAuthorized "));
		assert(msg2.status == StatusResponse::FAILURE);

	}

	{
		// --- DoneNotification
		std::stringstream ss;
		ss << "<mmi:mmi xmlns:mmi=\"http://www.w3.org/2008/04/mmi-arch\" version=\"1.0\" xmlns:emma=\"http://www.w3.org/2003/04/emma\"> <mmi:DoneNotification mmi:Source=\"someURI\" mmi:Target=\"someOtherURI\" mmi:Context=\"someURI\"  mmi:Status=\"success\" mmi:RequestID=\"request-1\" mmi:Confidential=\"true\"> <mmi:Data> <emma:emma version=\"1.0\"> <emma:interpretation id=\"int1\" emma:medium=\"acoustic\" emma:confidence=\".75\"  emma:mode=\"voice\" emma:tokens=\"flights from boston to denver\"> <origin>Boston</origin> <destination>Denver</destination> </emma:interpretation> </emma:emma> </mmi:Data> </mmi:DoneNotification></mmi:mmi>";
		DoneNotification msg = DoneNotification::fromXML(xmlToDoc(ss.str()));
		assert(boost::iequals(msg.tagName, "DoneNotification"));
		assert(boost::iequals(msg.source, "someURI"));
		assert(boost::iequals(msg.target, "someOtherURI"));
		assert(boost::iequals(msg.requestId, "request-1"));
		assert(boost::iequals(msg.context, "someURI"));
		assert(msg.data.size() > 0);
		assert(msg.status == StatusResponse::SUCCESS);

		DoneNotification msg2 = DoneNotification::fromXML(msg.toXML());
		assert(boost::iequals(msg2.tagName, "DoneNotification"));
		assert(boost::iequals(msg2.source, "someURI"));
		assert(boost::iequals(msg2.target, "someOtherURI"));
		assert(boost::iequals(msg2.requestId, "request-1"));
		assert(boost::iequals(msg2.context, "someURI"));
		assert(msg2.data.size() > 0);
		assert(msg2.status == StatusResponse::SUCCESS);

	}

	{
		// --- DoneNotification
		std::stringstream ss;
		ss << "<mmi:mmi xmlns:mmi=\"http://www.w3.org/2008/04/mmi-arch\" version=\"1.0\" xmlns:emma=\"http://www.w3.org/2003/04/emma\"> <mmi:DoneNotification mmi:Source=\"someURI\" mmi:Target=\"someOtherURI\" mmi:Context=\"someURI\"  mmi:Status=\"success\" mmi:RequestID=\"request-1\" > <mmi:Data> <emma:emma version=\"1.0\"> <emma:interpretation id=\"int1\" emma:no-input=\"true\"/> </emma:emma> </mmi:Data> </mmi:DoneNotification></mmi:mmi>";
		DoneNotification msg = DoneNotification::fromXML(xmlToDoc(ss.str()));
		assert(boost::iequals(msg.tagName, "DoneNotification"));
		assert(boost::iequals(msg.source, "someURI"));
		assert(boost::iequals(msg.target, "someOtherURI"));
		assert(boost::iequals(msg.requestId, "request-1"));
		assert(boost::iequals(msg.context, "someURI"));
		assert(msg.data.size() > 0);
		assert(msg.status == StatusResponse::SUCCESS);

		DoneNotification msg2 = DoneNotification::fromXML(msg.toXML());
		assert(boost::iequals(msg2.tagName, "DoneNotification"));
		assert(boost::iequals(msg2.source, "someURI"));
		assert(boost::iequals(msg2.target, "someOtherURI"));
		assert(boost::iequals(msg2.requestId, "request-1"));
		assert(boost::iequals(msg2.context, "someURI"));
		assert(msg2.data.size() > 0);
		assert(msg2.status == StatusResponse::SUCCESS);

	}

	{
		// --- CancelRequest
		std::stringstream ss;
		ss << "<mmi:mmi xmlns:mmi=\"http://www.w3.org/2008/04/mmi-arch\" version=\"1.0\"> <mmi:CancelRequest mmi:Source=\"someURI\" mmi:Target=\"someOtherURI\" mmi:Context=\"someURI\"  mmi:RequestID=\"request-1\"/></mmi:mmi>";
		CancelRequest msg = CancelRequest::fromXML(xmlToDoc(ss.str()));
		assert(boost::iequals(msg.tagName, "CancelRequest"));
		assert(boost::iequals(msg.source, "someURI"));
		assert(boost::iequals(msg.target, "someOtherURI"));
		assert(boost::iequals(msg.requestId, "request-1"));
		assert(boost::iequals(msg.context, "someURI"));

		CancelRequest msg2 = CancelRequest::fromXML(msg.toXML());
		assert(boost::iequals(msg2.tagName, "CancelRequest"));
		assert(boost::iequals(msg2.source, "someURI"));
		assert(boost::iequals(msg2.target, "someOtherURI"));
		assert(boost::iequals(msg2.requestId, "request-1"));
		assert(boost::iequals(msg2.context, "someURI"));

	}

	{
		// --- CancelResponse
		std::stringstream ss;
		ss << "<mmi:mmi xmlns:mmi=\"http://www.w3.org/2008/04/mmi-arch\" version=\"1.0\"> <mmi:CancelResponse mmi:Source=\"someURI\" mmi:Target=\"someOtherURI\" mmi:Context=\"someURI\" mmi:RequestID=\"request-1\"  mmi:Status=\"success\"/></mmi:mmi>";
		CancelResponse msg = CancelResponse::fromXML(xmlToDoc(ss.str()));
		assert(boost::iequals(msg.tagName, "CancelResponse"));
		assert(boost::iequals(msg.source, "someURI"));
		assert(boost::iequals(msg.target, "someOtherURI"));
		assert(boost::iequals(msg.requestId, "request-1"));
		assert(boost::iequals(msg.context, "someURI"));
		assert(msg.status == StatusResponse::SUCCESS);

		CancelResponse msg2 = CancelResponse::fromXML(msg.toXML());
		assert(boost::iequals(msg2.tagName, "CancelResponse"));
		assert(boost::iequals(msg2.source, "someURI"));
		assert(boost::iequals(msg2.target, "someOtherURI"));
		assert(boost::iequals(msg2.requestId, "request-1"));
		assert(boost::iequals(msg2.context, "someURI"));
		assert(msg2.status == StatusResponse::SUCCESS);

	}

	{
		// --- PauseRequest
		std::stringstream ss;
		ss << "<mmi:mmi xmlns:mmi=\"http://www.w3.org/2008/04/mmi-arch\" version=\"1.0\"> <mmi:PauseRequest mmi:Context=\"someURI\" mmi:Source=\"someURI\" mmi:Target=\"someOtherURI\"  mmi:RequestID=\"request-1\"/></mmi:mmi>";
		PauseRequest msg = PauseRequest::fromXML(xmlToDoc(ss.str()));
		assert(boost::iequals(msg.tagName, "PauseRequest"));
		assert(boost::iequals(msg.source, "someURI"));
		assert(boost::iequals(msg.target, "someOtherURI"));
		assert(boost::iequals(msg.requestId, "request-1"));
		assert(boost::iequals(msg.context, "someURI"));

		PauseRequest msg2 = PauseRequest::fromXML(msg.toXML());
		assert(boost::iequals(msg2.tagName, "PauseRequest"));
		assert(boost::iequals(msg2.source, "someURI"));
		assert(boost::iequals(msg2.target, "someOtherURI"));
		assert(boost::iequals(msg2.requestId, "request-1"));
		assert(boost::iequals(msg2.context, "someURI"));

	}

	{
		// --- PauseResponse
		std::stringstream ss;
		ss << "<mmi:mmi xmlns:mmi=\"http://www.w3.org/2008/04/mmi-arch\" version=\"1.0\"> <mmi:PauseResponse mmi:Source=\"someURI\" mmi:Target=\"someOtherURI\" mmi:Context=\"someURI\" mmi:RequestID=\"request-1\"  mmi:Status=\"success\"/></mmi:mmi>";
		PauseResponse msg = PauseResponse::fromXML(xmlToDoc(ss.str()));
		assert(boost::iequals(msg.tagName, "PauseResponse"));
		assert(boost::iequals(msg.source, "someURI"));
		assert(boost::iequals(msg.target, "someOtherURI"));
		assert(boost::iequals(msg.requestId, "request-1"));
		assert(boost::iequals(msg.context, "someURI"));
		assert(msg.status == StatusResponse::SUCCESS);

		PauseResponse msg2 = PauseResponse::fromXML(msg.toXML());
		assert(boost::iequals(msg2.tagName, "PauseResponse"));
		assert(boost::iequals(msg2.source, "someURI"));
		assert(boost::iequals(msg2.target, "someOtherURI"));
		assert(boost::iequals(msg2.requestId, "request-1"));
		assert(boost::iequals(msg2.context, "someURI"));
		assert(msg2.status == StatusResponse::SUCCESS);

	}

	{
		// --- ResumeRequest
		std::stringstream ss;
		ss << "<mmi:mmi xmlns:mmi=\"http://www.w3.org/2008/04/mmi-arch\" version=\"1.0\"> <mmi:ResumeRequest mmi:Context=\"someURI\" mmi:Source=\"someURI\" mmi:Target=\"someOtherURI\"  mmi:RequestID=\"request-1\"/></mmi:mmi>";
		ResumeRequest msg = ResumeRequest::fromXML(xmlToDoc(ss.str()));
		assert(boost::iequals(msg.tagName, "ResumeRequest"));
		assert(boost::iequals(msg.source, "someURI"));
		assert(boost::iequals(msg.target, "someOtherURI"));
		assert(boost::iequals(msg.requestId, "request-1"));
		assert(boost::iequals(msg.context, "someURI"));

		ResumeRequest msg2 = ResumeRequest::fromXML(msg.toXML());
		assert(boost::iequals(msg2.tagName, "ResumeRequest"));
		assert(boost::iequals(msg2.source, "someURI"));
		assert(boost::iequals(msg2.target, "someOtherURI"));
		assert(boost::iequals(msg2.requestId, "request-1"));
		assert(boost::iequals(msg2.context, "someURI"));

	}

	{
		// --- ResumeResponse
		std::stringstream ss;
		ss << "<mmi:mmi xmlns:mmi=\"http://www.w3.org/2008/04/mmi-arch\" version=\"1.0\"> <mmi:ResumeResponse mmi:Source=\"someURI\" mmi:Target=\"someOtherURI\" mmi:Context=\"someURI\" mmi:RequestID=\"request-1\"  mmi:Status=\"success\"/></mmi:mmi>";
		ResumeResponse msg = ResumeResponse::fromXML(xmlToDoc(ss.str()));
		assert(boost::iequals(msg.tagName, "ResumeResponse"));
		assert(boost::iequals(msg.source, "someURI"));
		assert(boost::iequals(msg.target, "someOtherURI"));
		assert(boost::iequals(msg.requestId, "request-1"));
		assert(boost::iequals(msg.context, "someURI"));
		assert(msg.status == StatusResponse::SUCCESS);

		ResumeResponse msg2 = ResumeResponse::fromXML(msg.toXML());
		assert(boost::iequals(msg2.tagName, "ResumeResponse"));
		assert(boost::iequals(msg2.source, "someURI"));
		assert(boost::iequals(msg2.target, "someOtherURI"));
		assert(boost::iequals(msg2.requestId, "request-1"));
		assert(boost::iequals(msg2.context, "someURI"));
		assert(msg2.status == StatusResponse::SUCCESS);

	}

	{
		// --- ExtensionNotification
		std::stringstream ss;
		ss << "<mmi:mmi xmlns:mmi=\"http://www.w3.org/2008/04/mmi-arch\" version=\"1.0\"> <mmi:ExtensionNotification mmi:Name=\"appEvent\" mmi:Source=\"someURI\"  mmi:Target=\"someOtherURI\" mmi:Context=\"someURI\" mmi:RequestID=\"request-1\"> </mmi:ExtensionNotification></mmi:mmi>";
		ExtensionNotification msg = ExtensionNotification::fromXML(xmlToDoc(ss.str()));
		assert(boost::iequals(msg.tagName, "ExtensionNotification"));
		assert(boost::iequals(msg.source, "someURI"));
		assert(boost::iequals(msg.target, "someOtherURI"));
		assert(boost::iequals(msg.requestId, "request-1"));
		assert(boost::iequals(msg.context, "someURI"));
		assert(boost::iequals(msg.name, "appEvent"));

		ExtensionNotification msg2 = ExtensionNotification::fromXML(msg.toXML());
		assert(boost::iequals(msg2.tagName, "ExtensionNotification"));
		assert(boost::iequals(msg2.source, "someURI"));
		assert(boost::iequals(msg2.target, "someOtherURI"));
		assert(boost::iequals(msg2.requestId, "request-1"));
		assert(boost::iequals(msg2.context, "someURI"));
		assert(boost::iequals(msg2.name, "appEvent"));

	}

	{
		// --- ClearContextRequest
		std::stringstream ss;
		ss << "<mmi:mmi xmlns:mmi=\"http://www.w3.org/2008/04/mmi-arch\" version=\"1.0\"> <mmi:ClearContextRequest mmi:Source=\"someURI\" mmi:Target=\"someOtherURI\" mmi:Context=\"someURI\"  mmi:RequestID=\"request-2\"/></mmi:mmi>";
		ClearContextRequest msg = ClearContextRequest::fromXML(xmlToDoc(ss.str()));
		assert(boost::iequals(msg.tagName, "ClearContextRequest"));
		assert(boost::iequals(msg.source, "someURI"));
		assert(boost::iequals(msg.target, "someOtherURI"));
		assert(boost::iequals(msg.requestId, "request-2"));
		assert(boost::iequals(msg.context, "someURI"));

		ClearContextRequest msg2 = ClearContextRequest::fromXML(msg.toXML());
		assert(boost::iequals(msg2.tagName, "ClearContextRequest"));
		assert(boost::iequals(msg2.source, "someURI"));
		assert(boost::iequals(msg2.target, "someOtherURI"));
		assert(boost::iequals(msg2.requestId, "request-2"));
		assert(boost::iequals(msg2.context, "someURI"));

	}

	{
		// --- ClearContextResponse
		std::stringstream ss;
		ss << "<mmi:mmi xmlns:mmi=\"http://www.w3.org/2008/04/mmi-arch\" version=\"1.0\"> <mmi:ClearContextResponse mmi:Source=\"someURI\" mmi:Target=\"someOtherURI\" mmi:Context=\"someURI\"  mmi:RequestID=\"request-2\" mmi:Status=\"success\"/></mmi:mmi>";
		ClearContextResponse msg = ClearContextResponse::fromXML(xmlToDoc(ss.str()));
		assert(boost::iequals(msg.tagName, "ClearContextResponse"));
		assert(boost::iequals(msg.source, "someURI"));
		assert(boost::iequals(msg.target, "someOtherURI"));
		assert(boost::iequals(msg.requestId, "request-2"));
		assert(boost::iequals(msg.context, "someURI"));
		assert(msg.status == StatusResponse::SUCCESS);

		ClearContextResponse msg2 = ClearContextResponse::fromXML(msg.toXML());
		assert(boost::iequals(msg2.tagName, "ClearContextResponse"));
		assert(boost::iequals(msg2.source, "someURI"));
		assert(boost::iequals(msg2.target, "someOtherURI"));
		assert(boost::iequals(msg2.requestId, "request-2"));
		assert(boost::iequals(msg2.context, "someURI"));
		assert(msg2.status == StatusResponse::SUCCESS);

	}

	{
		// --- StatusRequest
		std::stringstream ss;
		ss << "<mmi:mmi xmlns:mmi=\"http://www.w3.org/2008/04/mmi-arch\" version=\"1.0\"> <mmi:StatusRequest mmi:RequestAutomaticUpdate=\"true\" mmi:Source=\"someURI\"  mmi:Target=\"someOtherURI\" mmi:RequestID=\"request-3\" mmi:Context=\"aToken\"/></mmi:mmi>";
		StatusRequest msg = StatusRequest::fromXML(xmlToDoc(ss.str()));
		assert(boost::iequals(msg.tagName, "StatusRequest"));
		assert(boost::iequals(msg.source, "someURI"));
		assert(boost::iequals(msg.target, "someOtherURI"));
		assert(boost::iequals(msg.requestId, "request-3"));
		assert(boost::iequals(msg.context, "aToken"));
		assert(msg.automaticUpdate);

		StatusRequest msg2 = StatusRequest::fromXML(msg.toXML());
		assert(boost::iequals(msg2.tagName, "StatusRequest"));
		assert(boost::iequals(msg2.source, "someURI"));
		assert(boost::iequals(msg2.target, "someOtherURI"));
		assert(boost::iequals(msg2.requestId, "request-3"));
		assert(boost::iequals(msg2.context, "aToken"));
		assert(msg2.automaticUpdate);

	}

	{
		// --- StatusResponse
		std::stringstream ss;
		ss << "<mmi:mmi xmlns:mmi=\"http://www.w3.org/2008/04/mmi-arch\" version=\"1.0\"> <mmi:StatusResponse mmi:AutomaticUpdate=\"true\" mmi:Status=\"alive\"  mmi:Source=\"someURI\" mmi:Target=\"someOtherURI\" mmi:RequestID=\"request-3\" mmi:Context=\"aToken\"/> </mmi:mmi>";
		StatusResponse msg = StatusResponse::fromXML(xmlToDoc(ss.str()));
		assert(boost::iequals(msg.tagName, "StatusResponse"));
		assert(boost::iequals(msg.source, "someURI"));
		assert(boost::iequals(msg.target, "someOtherURI"));
		assert(boost::iequals(msg.requestId, "request-3"));
		assert(boost::iequals(msg.context, "aToken"));
		assert(msg.status == StatusResponse::ALIVE);

		StatusResponse msg2 = StatusResponse::fromXML(msg.toXML());
		assert(boost::iequals(msg2.tagName, "StatusResponse"));
		assert(boost::iequals(msg2.source, "someURI"));
		assert(boost::iequals(msg2.target, "someOtherURI"));
		assert(boost::iequals(msg2.requestId, "request-3"));
		assert(boost::iequals(msg2.context, "aToken"));
		assert(msg2.status == StatusResponse::ALIVE);

	}

}