#!/usr/bin/perl

use strict;
use Data::Dumper;
use XML::Simple;
use File::Basename;
use File::Find;
use Cwd 'abs_path';

my $ctest = 'ctest'; # we assume it to be in the path

my $possibleBuildDir = "../../build/cli";
if (@ARGV>0) {
    $possibleBuildDir = $ARGV[0];
}
#print $possibleBuildDir;
chdir dirname(abs_path($0)) or die($!);
my $manifest = XMLin("manifest.xml");

#if (-d $possibleBuildDir) {
	chdir $possibleBuildDir or die($!);
#}

my %testClasses = (
'w3c/ecma' => 'ECMA',
'w3c/lua' => 'Lua',
'w3c/namespace' => 'NS',
'w3c/promela' => 'Promela',
# 'w3c/c89' => 'C89',
'w3c/gen/c/ecma' => 'C (ECMA)',
'w3c/gen/c/lua' => 'C (Lua)',
'w3c/binding/java/jexl' => 'Java (JEXL)',
# 'w3c/spin/promela' => 'Spin'
'w3c/gen/vhdl/promela' => 'VHDL Promela',
# 'w3c/gen/vhdl/ecma' => 'VHDL ECMA',
);

my %specClass = (
'3' => 'Core Constructs',
'4' => 'Executable Content',
'5' => 'Data Model and Manipulation',
'6' => 'External Communications',
'C' => 'Data Models',
'D' => 'Event I/O Processor'	
);

my %specName = (
'C.1' => 'The Null Data Model',
'D.2' => 'Basic HTTP Event I/O Processor',
'C.2' => 'The ECMAScript Data Model',
'C.3' => 'The XPath Data Model',
'D.1' => 'SCXML Event I/O Processor',
'3.10' => '<history>',
'3.12' => 'SCXML Events',
'3.13' => 'Selecting and Executing Transitions',
'3.2' => '<scxml>',
'3.3' => '<state>',
'3.7' => '<final>',
'3.8' => '<onentry>',
'3.9' => '<onexit>',
'4.2' => '<raise>',
'4.3' => '<if>',
'4.6' => '<foreach>',
'4.9' => 'Evaluation of Executable Content',
'5.10' => 'System Variables',
'5.3' => '<data>',
'5.4' => '<assign>',
'5.5' => '<donedata>',
'5.6' => '<content>',
'5.7' => '<param>',
'5.8' => '<script>',
'5.9' => 'Expressions',
'6.2' => '<send>',
'6.3' => '<cancel>',
'6.4' => '<invoke>'
);

my %specLink = (
);

my $perSpecId;

TESTS: for my $testNr (keys $manifest->{'assert'}) {
	my @tests;
	my $thisTest = $manifest->{'assert'}->{$testNr};
	if (ref($thisTest->{'test'}->{'start'}) eq "ARRAY") {
		push (@tests, @{$thisTest->{'test'}->{'start'}});
	} else {
		push (@tests, $thisTest->{'test'}->{'start'});
	}
	
	$specLink{$thisTest->{'specnum'}} = $thisTest->{'specid'};
	
	for my $t (@tests) {
		if ($t->{'uri'} =~ /\/test(.*)\.[txml|txt]/) {
			# $perSpecId->{$thisTest->{'specnum'}}->{$1}->{'specid'} = $thisTest->{'specid'}
			$perSpecId->{$thisTest->{'specnum'}}->{$1}->{'content'} = $thisTest->{'content'};
			$perSpecId->{$thisTest->{'specnum'}}->{$1}->{'required'} = $thisTest->{'test'}->{'conformance'};
			$perSpecId->{$thisTest->{'specnum'}}->{$1}->{'manual'} = $thisTest->{'test'}->{'manual'};
		} else {
			die(Dumper($t));
		}
	}	

}

# print Dumper($perSpecId);

print << "EOF";
<table>

	<thead>
		<tr>
			<th colspan="3">Test (Req. / Man.)</th>
EOF

for my $testClass (values %testClasses) {
	print << "EOF";
			<th>${testClass}</th>
EOF
	
}

print << "EOF";
		</tr>
	</thead>
	<tbody>
EOF

# print '| Test |  | ECMA   | Lua |' . "\n";
# print '|-----:|--|:------:|:---:|' . "\n";
my $nrCols = 0;
my $lastSpecClass = "";
for my $specid (sort { $a cmp $b } keys $perSpecId) {
	my $specName = $specName{$specid};
	my $specClass = $specClass{substr($specid, 0, 1)};
	if ($specName =~ s/^<(.*)>$/ucfirst($1)/eg) {
		# $specName = join " ", map {ucfirst} split " ", $specName;
		$specName = 'The ' .$specName. ' Element';
	}
	$specName =~ s/scxml/SCXML/ig;
	
	# print "| <br> |   |   |  |  |\n";
	
	$nrCols = 3 + (keys %testClasses);
	if ($specClass ne $lastSpecClass) {
		print << "EOF";
		<tr>
			<td colspan="${nrCols}"><b><big>${specClass}</big></b></td>
		</tr>
EOF
		$lastSpecClass = $specClass;
	}
	
	my $link = "http://www.w3.org/TR/2015/REC-scxml-20150901/" . ${specLink{${specid}}};
	
	$nrCols = 2 + (keys %testClasses);
	print << "EOF";
		<tr>
			<td><b><a href="${link}">&sect;${specid}</a></b></td>
			<td colspan="${nrCols}"><sub>&nbsp;</sub><b>${specName}</b><sup>&nbsp;</sup></td>
		</tr>
EOF
	
	
	# print "| **[&sect;${specid}](http://www.w3.org/TR/2015/REC-scxml-20150901/${specLink{${specid}}})** | **${specName}** | <br><br> |  |\n";
	
	for my $test (sort {$a<=>$b} keys $perSpecId->{$specid}) {
		
		print STDERR "\n${test} ";
		
		my $content = $perSpecId->{$specid}->{$test}->{'content'};
		$content =~ s/^\s+|\s+$//g ; # trim
		$content =~ s/[\n]//g; # remove special chars
		$content =~ s/\]/\)/g; # substitute brackets
		$content =~ s/\[/\(/g; # substitute brackets
		$content =~ s/([`_\*\\])/\\$1/g; # escaping
		$content =~ s/"/&quot;/g; # escaping
		$content =~ s/'(\S+)'/`$1`/g; # remove special chars
		
		$content =~ s/^\s+In the XPath data\s?model,?\s*(\S)/uc($1)/ieg;
		$content =~ s/^\s+In the ECMAScript data\s?model,?\s*(\S)/uc($1)/ieg;
		$content =~ s/^\s+The SCXML processor MUST\s*(\S)/uc($1)/ieg;
		$content =~ s/^\s+The Processor MUST\s*(\S)/uc($1)/ieg;
		$content =~ s/^\s+To execute a microstep, the SCXML Processor MUST\s*(\S)/uc($1)/ieg;
		$content =~ s/^\s+In the foreach element,?\s*(\S)/uc($1)/ieg;
		$content =~ s/^\s+If the location expression of an assign\s*(\S)/uc($1)/ieg;
		
		# $content = substr($content, 0, 120);
		
		my $required = $perSpecId->{$specid}->{$test}->{'required'};
		my $manual = $perSpecId->{$specid}->{$test}->{'manual'};
		$required =~ s/optional//g;
		$required =~ s/mandatory/X/g;
		
		$manual =~ s/true/X/g;
		$manual =~ s/false//g;
		
		my $output;
		
		my $pass = '<code>OK</code>';
		my $fail = '<code><mark><b>FAIL</b></mark></code>';
		
		$link = "https://github.com/tklab-tud/uscxml/tree/master/test/w3c/txml/test${test}.txml";
		
		print << "EOF";
		<tr>
			<td>&nbsp;&nbsp;&nbsp;<b><a href="${link}" alt="${content}">${test}</a></b></td>
			<td>${required}</td>
			<td>${manual}</td>
EOF

		for my $testClass (keys %testClasses) {
			my $testPass = $fail;
			my $testName = "${testClass}/test${test}.scxml";
			print STDERR "$testClasses{$testClass}";
			$output = `$ctest -L $testName 2>&1 /dev/null`;
			if ($output =~ /No tests were found!!!/) {
				$testPass = '<code>N/A</code>';
				print STDERR "? ";
			} elsif ($output =~ /Passed/) {
				$testPass = $pass;
				print STDERR "+ ";
			} else {
				print STDERR "! ";
			}
			
			print << "EOF";
			<td>${testPass}</td>
EOF
			
		}		
		
		print << "EOF";
		</tr>
EOF
		
		# print "|[**`${test}`**](https://github.com/tklab-tud/uscxml/tree/master/test/w3c/txml/test${test}.txml \"$content\") | <sub>${required}&nbsp;/&nbsp;$manual</sub> | $ecmaPass | $luaPass |\n";
		
	}
}

		print << "EOF";
	</tbody>
</table>
EOF
