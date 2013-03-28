#!/opt/local/bin/perl -w

use strict;

use XML::LibXSLT;
use XML::LibXML;
use Data::Dumper;

my $xslt = XML::LibXSLT->new();
my $xsl = shift || 'confEcma.xsl';

opendir(my $testDir, "tests") or die($!);
opendir(my $txmlDir, "txml") or die($!);
while(readdir $txmlDir) {
  next unless /txml$/;
  my $baseName = $_;
  my $txmlFile = 'txml/'.$_;
  
  my $source = XML::LibXML->load_xml(location => $txmlFile) or die($!);
  my $style_doc = XML::LibXML->load_xml(location => $xsl, no_cdata=>1) or die($!);
  
  my $stylesheet = $xslt->parse_stylesheet($style_doc) or die($!);
  my $results = $stylesheet->transform($source) or die($!);
    
  open(my $json, '>', "tests/".$baseName.".json") or die($!);
  print $json <<EOF;
{
    "initialConfiguration" : ["pass"],
    "events" : []
}
EOF
  close($json);

  open(my $scxml, '>', "tests/".$baseName.".scxml") or die($!);
  print $scxml $stylesheet->output_as_bytes($results);
  close($scxml);
}
