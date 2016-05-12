#!/usr/bin/perl -w

use strict;
use Data::Dumper;
use XML::Simple;

my $manifest = XMLin("./manifest.xml");
# print Dumper($manifest->{'assert'});

my $perSpecId;

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
		<th>NameSpace</th>
		<th>ECMA</th>
		<th>Lua</th>
		<th>PROMELA</th>
		<th>Prolog</th>
	</tr>
</thead>
EOF

# print '| Test |  | ECMA   | Lua |' . "\n";
# print '|-----:|--|:------:|:---:|' . "\n";

for my $specid (sort { $a cmp $b } keys $perSpecId) {
	my $specName = $specName{$specid};
	if ($specName =~ s/^<(.*)>$/ucfirst($1)/eg) {
		# $specName = join " ", map {ucfirst} split " ", $specName;
		$specName = 'The ' .$specName. ' Element';
	}
	$specName =~ s/scxml/SCXML/ig;
	
	# print "| <br> |   |   |  |  |\n";
	
	my $link = "http://www.w3.org/TR/2015/REC-scxml-20150901/" . ${specLink{${specid}}};
	
	print << "EOF";
	<tr>
		<td>**<a href="${link}">&sect;${specid}</a>**</td>
		<td colspan="7"><sub>&nbsp;</sub>**${specName}**<sup>&nbsp;</sup></td>
	</tr>
EOF
	
	
	# print "| **[&sect;${specid}](http://www.w3.org/TR/2015/REC-scxml-20150901/${specLink{${specid}}})** | **${specName}** | <br><br> |  |\n";
	
	for my $test (sort {$a<=>$b} keys $perSpecId->{$specid}) {
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
		
		
		my $pass = '`pass`';
		my $fail = '**`FAIL`**';
		
		my $ecmaPass = $fail;
		my $ecmaFile = "/Users/sradomski/Documents/TK/Code/uscxml2/test/w3c/ecma/test${test}.scxml";
		$output = `../../build/cli/bin/test-w3c $ecmaFile 2>&1 /dev/null`;
		$ecmaPass = $pass if $? == 0;

		my $luaPass = $fail;
		my $luaFile = "/Users/sradomski/Documents/TK/Code/uscxml2/test/w3c/lua/test${test}.scxml";
		$output = `../../build/cli/bin/test-w3c $luaFile 2>&1 /dev/null`;
		$luaPass = $pass if $? == 0;

		my $nsPass = $fail;
		my $nsFile = "/Users/sradomski/Documents/TK/Code/uscxml2/test/w3c/namespace/test${test}.scxml";
		$output = `../../build/cli/bin/test-w3c $nsFile 2>&1 /dev/null`;
		$nsPass = $pass if $? == 0;
		
		$link = "https://github.com/tklab-tud/uscxml/tree/master/test/w3c/txml/test${test}.txml";
		
		print << "EOF";
		<tr>
			<td>&nbsp;&nbsp;&nbsp;**<a href="${link}" alt="${content}">`${test}`</a>**</td>
			<td>${required}</td>
			<td>${manual}</td>
			<td>${nsPass}</td>
			<td>${ecmaPass}</td>
			<td>${luaPass}</td>
			<td>`N/A`</td>
			<td>`N/A`</td>
		</tr>
EOF
		
		# print "|[**`${test}`**](https://github.com/tklab-tud/uscxml/tree/master/test/w3c/txml/test${test}.txml \"$content\") | <sub>${required}&nbsp;/&nbsp;$manual</sub> | $ecmaPass | $luaPass |\n";
		
	}
}

print '</table>'
