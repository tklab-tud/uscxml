#!/usr/bin/perl

use strict;
use Data::Dumper;
use XML::Simple;


my $manifest = XMLin("./manifest.xml");
# print Dumper($manifest->{'assert'});

my $perSpecId;

my @allTests;
my @ecmaTests;
my @xpathTests;
my @agnosticTests;
my @nullTests;
my @manualTests;

for my $testNr (keys $manifest->{'assert'}) {
	my @tests;
	my $thisTest = $manifest->{'assert'}->{$testNr};
	if (ref($thisTest->{'test'}->{'start'}) eq "ARRAY") {
		push (@tests, @{$thisTest->{'test'}->{'start'}});
	} else {
		push (@tests, $thisTest->{'test'}->{'start'});
	}
	$perSpecId->{$thisTest->{'specnum'}.':'.$thisTest->{'specid'}}->{'total'} += @tests;
	if ($thisTest->{'test'}->{'manual'} eq "true") {
		$perSpecId->{$thisTest->{'specnum'}.':'.$thisTest->{'specid'}}->{'manual'} += @tests;
		push @manualTests,  @tests;
		
	}
	
	if ($thisTest->{'specid'} eq "#minimal-profile" || $thisTest->{'specid'} !~ /profile$/) {
		push @nullTests,  @tests;
	}

	if ($thisTest->{'specid'} eq "#ecma-profile" || $thisTest->{'specid'} !~ /profile$/) {
		push @ecmaTests,  @tests;
	}

	if ($thisTest->{'specid'} eq "#xpath-profile" || $thisTest->{'specid'} !~ /profile$/) {
		push @xpathTests,  @tests;
	}
	
	push (@allTests, @tests);
	push @agnosticTests, @tests if ($thisTest->{'specid'} !~ /profile$/);
}

# print Dumper(@ecmaTests);

my %datamodels = (
	"ecma" => \@ecmaTests,
	"xpath" => \@xpathTests,
	"promela" => \@agnosticTests,
	"prolog" => \@agnosticTests,
	"lua" => \@ecmaTests
);

for my $datamodel (keys %datamodels) {
	# every scxml file is a test
	for (`ls $datamodel/*.scxml`) {
		my $filename = $_;
		chomp($filename);
		if ($filename =~ /\/test(\d+\w?)\.scxml/) {
			print("${filename} is not in mainfest\n") if (! grep $_->{'uri'} == "${1}/test${1}.scxml", @{$datamodels{$datamodel}});
		}
	}
	# every test is given
	for my $testURI (@{$datamodels{$datamodel}}) {
		if ($testURI->{'uri'} =~ /^(\d+)\/(test\d+\w?)\.(txt|txml)$/) {
			my $name = $2;
			my $suffix = ($3 eq "txml" ? "scxml" : $3);
			if (! -e "${datamodel}/${name}.${suffix}") {
				print("${datamodel}/${name}.${suffix} is missing\n");
			}
		} else {
			die ($testURI->{'uri'});
		}
	}
}

# print Dumper(@manualTests);

print "NULL : ".@nullTests."\n";
print "ECMA : ".@ecmaTests."\n";
print "XPATH: ".@xpathTests."\n";
print "\n";
print "MAN  : ".@manualTests."\n";
print "ANY  : ".@agnosticTests."\n";
print "TOTAL: ".@allTests."\n";
