#include <iostream>

#include "uscxml/config.h"
#include "uscxml/Common.h"
#include <DOM/Document.hpp>
#include <XPath/XPath.hpp>
#include <DOM/SAX2DOM/SAX2DOM.hpp>
#include <DOM/io/Stream.hpp>
#include "uscxml/Interpreter.h"
#include "uscxml/dom/DOMUtils.h"
#include "uscxml/dom/NameSpacingParser.h"

using namespace Arabica::DOM;
using namespace Arabica::XPath;
using namespace uscxml;

#define VALIDATE \
std::pair<Document<std::string>, NameSpaceInfo> parsed = parse(xmlSS.str());\
Document<std::string> origDoc = parsed.first;\
NameSpaceInfo origNS = parsed.second;\
validateRootFoo(parsed);\
insertBar(parsed);\
std::cout << parsed.first << std::endl;\
validateRootFooBar(parsed);\
parsed = cloneDocument(parsed);\
insertBaz(parsed);\
std::cout << parsed.first << std::endl;\
validateRootFooBarBaz(parsed);\
assert(DOMUtils::filterChildElements(origNS.xmlNSPrefix + "bar", origDoc.getDocumentElement()).size() == 3);\
assert(DOMUtils::filterChildElements(origNS.xmlNSPrefix + "baz", origDoc.getDocumentElement()).size() == 0);


/**
 Test DOM manipulations and document cloning with different namespace scenarios
 */

static Arabica::XPath::XPath<std::string> _xpath;

std::pair<Document<std::string>, NameSpaceInfo> parse(const std::string xmlString) {
	NameSpacingParser parser = NameSpacingParser::fromXML(xmlString);
	if (parser.errorsReported())
		assert(false);
	return std::make_pair(parser.getDocument(), parser.nameSpace);
}

std::pair<Document<std::string>, NameSpaceInfo> cloneDocument(std::pair<Document<std::string>, NameSpaceInfo>& parsed) {

	NameSpaceInfo nsInfo = parsed.second;
	Document<std::string> document = parsed.first;

	Document<std::string> clonedDocument;
	DOMImplementation<std::string> domFactory = Arabica::SimpleDOM::DOMImplementation<std::string>::getDOMImplementation();
	clonedDocument = domFactory.createDocument(document.getNamespaceURI(), "", 0);

	Node<std::string> child = document.getFirstChild();
	while (child) {
		Node<std::string> newNode = clonedDocument.importNode(child, true);
		clonedDocument.appendChild(newNode);
		child = child.getNextSibling();
	}

	return std::make_pair(clonedDocument, nsInfo);
}

void insertBar(std::pair<Document<std::string>, NameSpaceInfo>& parsed) {
	NameSpaceInfo nsInfo = parsed.second;
	Document<std::string> document = parsed.first;

	Node<std::string> root = document.getDocumentElement();
	for (size_t i = 0; i < 3; i++) {
		Element<std::string> bar = document.createElementNS(nsInfo.nsURL, "bar");
//		if (nsInfo.nsToPrefix.find(nsInfo.nsURL) != nsInfo.nsToPrefix.end())
		nsInfo.setPrefix(bar);
		root.appendChild(bar);
	}
}

void insertBaz(std::pair<Document<std::string>, NameSpaceInfo>& parsed) {
	NameSpaceInfo nsInfo = parsed.second;
	Document<std::string> document = parsed.first;

	Node<std::string> root = document.getDocumentElement();
	for (size_t i = 0; i < 3; i++) {
		Element<std::string> baz = document.createElementNS(nsInfo.nsURL, "baz");
		nsInfo.setPrefix(baz);
		root.appendChild(baz);
	}
}

static void validateRootFoo(std::pair<Document<std::string>, NameSpaceInfo>& parsed) {

	NameSpaceInfo nsInfo = parsed.second;
	Document<std::string> document = parsed.first;

	Node<std::string> root = document.getDocumentElement();
	_xpath.setNamespaceContext(*nsInfo.getNSContext());

	assert(TAGNAME_CAST(root) == nsInfo.xmlNSPrefix + "root");
	assert(LOCALNAME_CAST(root) == "root");
	NodeSet<std::string> foosFiltered = DOMUtils::filterChildElements(nsInfo.xmlNSPrefix + "foo", root);
	assert(foosFiltered.size() == 3);
	NodeSet<std::string> foosXPath = _xpath.evaluate("//" + nsInfo.xpathPrefix + "foo", root).asNodeSet();
	assert(foosXPath.size() == 3);

	for (size_t i = 0; i < 3; i++) {
		assert(foosFiltered[i] == foosXPath[i]);
		assert(TAGNAME_CAST(foosFiltered[i]) == nsInfo.xmlNSPrefix + "foo");
		assert(LOCALNAME_CAST(foosFiltered[i]) == "foo");
	}

}

static void validateRootFooBar(std::pair<Document<std::string>, NameSpaceInfo>& parsed) {
	validateRootFoo(parsed);

	NameSpaceInfo nsInfo = parsed.second;
	Document<std::string> document = parsed.first;

	Node<std::string> root = document.getDocumentElement();
	_xpath.setNamespaceContext(*nsInfo.getNSContext());

	NodeSet<std::string> barsFiltered = DOMUtils::filterChildElements(nsInfo.xmlNSPrefix + "bar", root);
	assert(barsFiltered.size() == 3);
	NodeSet<std::string> barsXPath = _xpath.evaluate("//" + nsInfo.xpathPrefix + "bar", root).asNodeSet();
	assert(barsXPath.size() == 3);

	for (size_t i = 0; i < 3; i++) {
		assert(barsFiltered[i] == barsXPath[i]);
		assert(TAGNAME_CAST(barsFiltered[i]) == nsInfo.xmlNSPrefix + "bar");
		assert(LOCALNAME_CAST(barsFiltered[i]) == "bar");
	}

}

static void validateRootFooBarBaz(std::pair<Document<std::string>, NameSpaceInfo>& parsed) {
	validateRootFooBar(parsed);

	NameSpaceInfo nsInfo = parsed.second;
	Document<std::string> document = parsed.first;

	Node<std::string> root = document.getDocumentElement();
	_xpath.setNamespaceContext(*nsInfo.getNSContext());

	assert(TAGNAME_CAST(root) == nsInfo.xmlNSPrefix + "root");
	assert(LOCALNAME_CAST(root) == "root");

	NodeSet<std::string> bazsFiltered = DOMUtils::filterChildElements(nsInfo.xmlNSPrefix + "baz", root);
	assert(bazsFiltered.size() == 3);
	NodeSet<std::string> bazsXPath = _xpath.evaluate("//" + nsInfo.xpathPrefix + "baz", root).asNodeSet();
	assert(bazsXPath.size() == 3);

	for (size_t i = 0; i < 3; i++) {
		assert(bazsFiltered[i] == bazsXPath[i]);
		assert(TAGNAME_CAST(bazsFiltered[i]) == nsInfo.xmlNSPrefix + "baz");
		assert(LOCALNAME_CAST(bazsFiltered[i]) == "baz");
	}

}

int main(int argc, char** argv) {

	// No namespaces at all
	{
		std::stringstream xmlSS;
		xmlSS << "<root><foo /><foo /><foo /></root>" << std::endl;
		VALIDATE
	}

	// default namespace
	{
		std::stringstream xmlSS;
		xmlSS << "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\
		<root xmlns=\"http://www.w3.org/2005/07/scxml\">\
			<foo /><foo /><foo />\
		</root>\
		" << std::endl;
		VALIDATE
	}

	// explicit namespaces
	{
		std::stringstream xmlSS;
		xmlSS << "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\
		<scxml:root xmlns:scxml=\"http://www.w3.org/2005/07/scxml\">\
			<scxml:foo /><scxml:foo /><scxml:foo />\
		</scxml:root>\
		" << std::endl;
		VALIDATE
	}

	// mixed namespaces
	{
		std::stringstream xmlSS;
		xmlSS << "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\
		<scxml:root xmlns:scxml=\"http://www.w3.org/2005/07/scxml\" xmlns:xhtml=\"http://www.w3.org/1999/xhtml\">\
		<xhtml:foo /><xhtml:foo /><xhtml:foo />\
		<scxml:foo /><scxml:foo /><scxml:foo />\
		</scxml:root>\
		" << std::endl;
		VALIDATE
	}

	// mixed namespaces with different default NS
	{
		std::stringstream xmlSS;
		xmlSS << "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\
		<scxml:root xmlns:scxml=\"http://www.w3.org/2005/07/scxml\" xmlns=\"http://www.w3.org/1999/xhtml\">\
		<foo /><foo /><foo />\
		<scxml:foo /><scxml:foo /><scxml:foo />\
		</scxml:root>\
		" << std::endl;
		VALIDATE
	}

}