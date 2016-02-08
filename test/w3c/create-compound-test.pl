#!/usr/bin/perl -w

use strict;
use Data::Dumper;
use XML::Simple;
use List::MoreUtils qw(apply);

#
# Create a huge compound test for performance measurements
#

my $datamodel = $ARGV[0];

my @failed = qw/239 226 216 199 301 302 304 452 309 344 277 156 312 313 314 487 528 488 230 178 557 558 446 552 276 280 307 319 324 415/;
# my @withDelay = qw /175 185 186 187 190 191 192 193 207 208 210 215 216 220 223 224 225 226 228 229 230 232 233 234 235 236 237 239 240 241 242 243 244 245 247 250 252 253 298 311 338 347 350 351 352 354 364 372 387 388 399 402 403a 403c 405 406 409 411 412 416 417 422 423 501 509 510 518 519 520 522 530 531 532 534 553 554 567 570 576 579 580/;
my @withDelay = qw/175 185 187 208 210 224 236 250 252 347 350 351 352 354 403a 403c 409 422 553/;

my $perSpecId;

my @allTests;
my @ecmaTests;
my @xpathTests;
my @agnosticTests;
my @nullTests;
my @manualTests;

my $manifest = XMLin("./manifest.xml");

TESTS: for my $testNr (keys $manifest->{'assert'}) {
	my @tests;
	my $thisTest = $manifest->{'assert'}->{$testNr};
	if (ref($thisTest->{'test'}->{'start'}) eq "ARRAY") {
		push (@tests, @{$thisTest->{'test'}->{'start'}});
	} else {
		push (@tests, $thisTest->{'test'}->{'start'});
	}
	for my $t (@tests) {
		if ($t->{'uri'} =~ /\/test(.*)\.[txml|txt]/) {
			next TESTS if ( grep /^$1$/, @failed );
			next TESTS if ( grep /^$1$/, @withDelay );
			$perSpecId->{$thisTest->{'specnum'}.':'.$thisTest->{'specid'}}->{'tests'} .= $1." ";
		} else {
			die(Dumper($t));
		}
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

my %datamodels = (
	"ecma" => \@ecmaTests,
	"xpath" => \@xpathTests,
	"promela" => \@agnosticTests,
	"prolog" => \@agnosticTests,
	"lua" => \@ecmaTests
);

# print Dumper(
# 	apply { s/(\d+)/${datamodel}/ }
# 	apply { s/txml/scxml/g }
# 	map {$_->{'uri'}}
# 	@{$datamodels{$datamodel}});
# exit;

print '<scxml datamodel="'.($datamodel eq "ecma" ? "ecmascript" : $datamodel).'">'."\n";

my @allFiles = 
	apply { s/(\d+\w?)/${datamodel}/ } 
	apply { s/txml/scxml/g } 
	map {$_->{'uri'}} 
	@{$datamodels{$datamodel}};

@allFiles = sort @allFiles;

for (my $i = 0; $i <= $#allFiles; ++$i) {
	my $filename = $allFiles[$i];
	my $nextId = 0;
	my $lookAhead = 1;
	my $nextFilename;
	while (!$nextId && $i < $#allFiles) {
		$nextFilename = $allFiles[$i+$lookAhead];
		chomp($nextFilename);
		$nextFilename =~ /\/test(\d+\w?)\.scxml/;
		$nextId = $1;
		$lookAhead++;
	}
	chomp($filename);
	if ($filename =~ /\/test(\d+\w?)\.scxml/) {
		my $testId = $1;
		if (grep $_->{'uri'} eq "${testId}/test${testId}.txml", @{$datamodels{$datamodel}}) {
			my $testContent;
			my $testDOM = XMLin($filename);
			{
			    open(F, $filename);
			    local $/ = undef;
			    $testContent = <F>;
			}
			# remove xml header
			$testContent =~ s/\<\?xml .*\n/\n/; 
			
			# replace <scxml> as compound state
			$testContent =~ s/<scxml/<state id="start"/; 
			$testContent =~ s/scxml\>\W?$/state\>\n/;
			
			# die($testContent);
			# remove datamodel attribute
			$testContent =~ s/ datamodel="\w+"//; 

			# remove version attribute
			$testContent =~ s/ version="\S+"//g; 
			
			# remove xmlns attribute
			$testContent =~ s/ xmlns:conf="\S+"//; 
			$testContent =~ s/ xmlns="\S+"//; 
			
			# reindent
			$testContent =~ s/\n/\n  /g; 

			# replace all ids with prefixed identifiers
			$testContent =~ s/state id="(\S+)"/state id="${testId}${1}"/g; 
			$testContent =~ s/parallel id="(\S+)"/parallel id="${testId}${1}"/g; 
			$testContent =~ s/final id="(\S+)"/final id="${testId}${1}"/g; 
			$testContent =~ s/history id="(\S+)"/history id="${testId}${1}"/g; 
			$testContent =~ s/history( type=\S+) id="(\S+)"/history${1} id="${testId}${2}"/g; 
			$testContent =~ s/state initial="(\w+) (\w+)"/state initial="${testId}${1} ${testId}${2}"/g; 
			$testContent =~ s/state initial="(\S+)"/state initial="${testId}${1}"/g; 
			$testContent =~ s/state( id=".*") initial="(\S+)"/state${1} initial="${testId}${2}"/g; 
			$testContent =~ s/state( id=".*") initial="(\w+) (\w+)"/state${1} initial="${testId}${2} ${testId}${3}"/g; 
			$testContent =~ s/scxml initial="(\w+) (\w+)"/scxml initial="${testId}${1} ${testId}${2}"/g; 
			$testContent =~ s/scxml initial="(\S+)"/scxml initial="${testId}${1}"/g; 
			
			# replace all target ids with prefixed identifiers
			$testContent =~ s/transition( cond=".*") ( event=".*") target="(\S+)"/transition${1}${2} target="${testId}${3}"/g;
			$testContent =~ s/transition( event=".*") target="(\S+)"/transition${1} target="${testId}${2}"/g;
			$testContent =~ s/transition( cond=".*") target="(\S+)"/transition${1} target="${testId}${2}"/g;
			$testContent =~ s/transition target="(\S+)"/transition target="${testId}${1}"/g;
			
			$testContent =~ s/transition( cond=".*") ( event=".*") target="(\S+) (\S+)"/transition${1}${2} target="${testId}${3} ${testId}${4}"/g;
			$testContent =~ s/transition( event=".*") target="(\S+) (\S+)"/transition${1} target="${testId}${2} ${testId}${3}"/g;
			$testContent =~ s/transition( cond=".*") target="(\S+) (\S+)"/transition${1} target="${testId}${2} ${testId}${3}"/g;
			$testContent =~ s/transition target="(\S+) (\S+)"/transition target="${testId}${1} ${testId}${2}"/g;
			
			# replace done.state.ID
			$testContent =~ s/event="done.state.(\w+)"/event="done.state.${testId}${1}"/g; 

			# set all delays to 0
			$testContent =~ s/delay="(\S+)"/delay="0ms"/g;
			$testContent =~ s/delayexpr="(\S+)"/delayexpr="'0ms'"/g;

			# remove timeout events
			$testContent =~ s/\<send event="timeout" delay="0ms"\/\>//g;
			$testContent =~ s/\<send event="timeout" delayexpr="'0ms'"\/\>//g;
			
			# replace all variables with prefixed identifiers
			$testContent =~ s/Var(\d+)/Var${testId}${1}/g; 
			$testContent =~ s/var(\d+)/var${testId}${1}/g; 
					
			# replace In predicate
			$testContent =~ s/In\('(\S+)'\)/In\('${testId}${1}'\)/g; 
			
				
			# connect to next test
			my $transDoneEvent;
			if ($nextId) {
				$transDoneEvent = '    <transition event="test.'.$testId.'.done" target="'.${nextId}.'start" />';
			} else {
				$transDoneEvent = '    <transition event="test.'.$testId.'.done" target="pass" />';
			}
			my $sendDoneEvent = 
				'<onentry>'."\n".
				'      <send event="test.'.$testId.'.done" />'."\n".
				'    </onentry>';
			$testContent =~ s/\<final id="${testId}pass"\>/\<state id="${testId}pass"\>\n      ${sendDoneEvent}\n${transDoneEvent}/;
			$testContent =~ s/(log label="Outcome" expr="'pass'"\/\>\n\s+\<\/onentry\>\n\s+\<\/)final/${1}state/;
			
			# die $testContent;
			print $testContent;
			
		}
	}
}
print "\n".'  <final id="pass" />';
print "\n".'</scxml>'."\n";
