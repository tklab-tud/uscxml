#!/usr/bin/perl -w

use strict;
use File::Spec;
use File::Basename;
use XML::LibXML;
use Data::Dumper;

my $xmlIn = shift or die("Expected *.xml file as input");

# absolutize and split into components
$xmlIn = File::Spec->rel2abs($xmlIn) or die($!);
my($filename, $dirs, $suffix) = fileparse($xmlIn) or die($!);

my $parser = XML::LibXML->new({'line_numbers' => 1 });
# my $xml = $parser->parse_file($xmlIn);
my $doc = $parser->load_xml('location' => $xmlIn, 'line_numbers' => 1) ;

my $lineOffset = 0;

sub lineNoNodes {
	my $node = shift;
	
	if ($node->nodeType == XML_ELEMENT_NODE) {
		$node->setAttribute("line_start", $node->line_number() + $lineOffset);
	}

	my $prevElem;
	for my $child ($node->childNodes()) {
		lineNoNodes($child);
		if ($prevElem) {
			$prevElem->setAttribute("line_end", $child->line_number() - 1 + $lineOffset);
			undef($prevElem);
		}
		if ($child->nodeType == XML_ELEMENT_NODE) {
			$prevElem = $child;
		}
	}
}

&lineNoNodes($doc->getDocumentElement());

print $doc->toString();