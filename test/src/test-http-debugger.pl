#!/usr/bin/perl

use lib './perl';
use strict;
use File::Spec;
use File::Basename;
use Cwd 'abs_path';
use JSON qw(from_json to_json);
use LWP;
use HTTP::Request::Common qw(POST GET);
use Data::Dumper;

my $scxmlBin = abs_path(shift);
die ("First argument needs to be path to uscxml-browser binary") if (!$scxmlBin);
die("'" . $scxmlBin . "' is not an executable file") if (! -x $scxmlBin);

my $baseDir = File::Spec->canonpath(dirname($0));
chdir $baseDir;

my $ua = LWP::UserAgent->new;
my $request;
my $response;
my $data;
my @breakpointSeq;

my $pid = fork;

if (!$pid) {
	exec("$scxmlBin -t4088 -d");
	exit;
}

my $baseURL = 'http://localhost:4088/debug';
# my $baseURL = 'http://localhost:5080/debug';

sub assertSuccess {
	my $response = shift;
	my $message = shift;
	print "-----\n";
	print $response->content();
	print "-----\n";
	from_json($response->content())->{'status'} eq "success" or die($message);
}

sub prepareSession {
	my $xml = shift;

	### Get a session
	my $request = GET $baseURL.'/connect';
	$response = $ua->request($request);
	assertSuccess($response, "Could not connect");

	my $session = from_json($response->content())->{'session'};
	die("Cannot acquire session from server") if (!$session);

	### Prepare an SCXML interpreter
	$request = POST $baseURL.'/prepare', 
		[
			'session' => $session,
			'url' => 'http://localhost/anonymous.scxml',
			'xml' => $xml
		];
	$response = $ua->request($request);
	assertSuccess($response, "Could not prepare SCXML");
	
	return $session;
}

sub finishSession {
	my $session = shift;
	
	### Prepare an SCXML interpreter
	$request = POST $baseURL.'/disconnect', 
		[
			'session' => $session,
		];
	$response = $ua->request($request);
	assertSuccess($response, "Could not disconnect session");
}

sub popAndCompare {
	my $qualified = shift;
	my $bp = shift(@breakpointSeq);
	for my $key (keys %{$bp}) {
		if (! exists($qualified->{$key}) || $qualified->{$key} ne $bp->{$key}) {
			print Dumper($qualified);
			print Dumper($bp);
			die("Expected different breakpoint");
		}
	}
	print "SUCCESS\n";
}

sub testSimpleStepping {

	my $xml = << 'END_SCXML';
	<scxml>
		<state id='s1'>
			<onentry>
				<log label="'foo'" />
			</onentry>
			<transition target='s2' />
		</state>
		<state id='s2'>
			<transition target='pass' />
		</state>
		<final id='pass' />
	</scxml>
END_SCXML

	@breakpointSeq = (
		{ subject => "microstep",  when => "before" },
		{ subject => "state",      when => "before", action => "enter" },
		{ subject => "state",      when => "after",  action => "enter"  },
		{ subject => "state",      when => "before", action => "enter", stateId => "s1" },
		{ subject => "executable", when => "before", execName => "log" },
		{ subject => "executable", when => "after", execName => "log" },
		{ subject => "state",      when => "after",  action => "enter", stateId => "s1" },
		{ subject => "microstep",  when => "after"  },
		{ subject => "microstep",  when => "before" },
		{ subject => "state",      when => "before", action => "exit",  stateId => "s1" },
		{ subject => "state",      when => "after",  action => "exit",  stateId => "s1" },
		{ subject => "transition", when => "before", source => "s1",    target => "s2"},
		{ subject => "transition", when => "after",  source => "s1",    target => "s2"},
		{ subject => "state",      when => "before", action => "enter", stateId => "s2" },
		{ subject => "state",      when => "after",  action => "enter", stateId => "s2" },
		{ subject => "microstep",  when => "after"  },
		{ subject => "microstep",  when => "before" },
		{ subject => "state",      when => "before", action => "exit",  stateId => "s2" },
		{ subject => "state",      when => "after",  action => "exit",  stateId => "s2" },
		{ subject => "transition", when => "before", source => "s2",    target => "pass"},
		{ subject => "transition", when => "after",  source => "s2",    target => "pass"},
		{ subject => "state",      when => "before", action => "enter", stateId => "pass" },
		{ subject => "state",      when => "after",  action => "enter", stateId => "pass" },
		{ subject => "microstep",  when => "after"  },
		
	);

	my $session = &prepareSession($xml);
	
	while(@breakpointSeq > 0) {
		### Take a step
		$request = POST $baseURL.'/step', ['session' => $session];
		$response = $ua->request($request);
		assertSuccess($response, "Could not step");
		# this will cause the interpreter to pause execution

		### Get the pending messages
		$request = POST $baseURL.'/poll', ['session' => $session];
		$response = $ua->request($request);
		assertSuccess($response, "Could not get breakpoint after step");

		# compare to what we expect
		$data = from_json($response->content());
		popAndCompare($data->{'qualified'});
	}
	
	### last step will finalize the interpreter
	$request = POST $baseURL.'/step', ['session' => $session];
	$response = $ua->request($request);
	assertSuccess($response, "Could not get breakpoint after step");

	### get the pending server push reply
	$request = POST $baseURL.'/poll', ['session' => $session];
	$response = $ua->request($request);
	assertSuccess($response, "Could not get breakpoint after step");

	$data = from_json($response->content());
	die("Machine not yet finished") if ($data->{'replyType'} ne "finished");

	&finishSession($session);
}

sub testBreakpoint {
	my $xml = << 'END_SCXML';
	<scxml>
		<state id='s1'>
			<onentry>
				<log label="'foo'" />
			</onentry>
			<transition target='s2' />
		</state>
		<state id='s2'>
			<transition target='pass' />
		</state>
		<final id='pass' />
	</scxml>
END_SCXML
	
	my $session = prepareSession($xml);
	
	### Skip to breakpoint
	$request = POST $baseURL.'/breakpoint/skipto', 
		[
			'session' => $session,
			'when' => 'after',
			'action' => 'enter',
			'subject' => 'state',
			'stateId' => 's1'
		];
	$response = $ua->request($request);
	assertSuccess($response, "Could not add breakpoint");
	
	### get the pending server push reply
	$request = POST $baseURL.'/poll', ['session' => $session];
	$response = $ua->request($request);
	assertSuccess($response, "Could not get breakpoint after step");
	
	$data = from_json($response->content());
	print Dumper($data);
	
	&finishSession($session);
}

sub testIssueReporting {
	my $xml = << 'END_SCXML';
	<scxml>
		<state id='s1'>
			<onentry>
				<log label="'foo'" />
			</onentry>
			<transition target='s2' />
		</state>
		<state id='s2'>
			<transition target='pass' />
		</state>
		<state id='s3'>
			<onentry>
				<log label="'Unreachable!'" />
			</onentry>
		</state>
		<final id='pass' />
	</scxml>
END_SCXML

	my $session = prepareSession($xml);
	
	### Get a list of issues
	$request = POST $baseURL.'/issues', 
		[
			'session' => $session
		];
	$response = $ua->request($request);
	assertSuccess($response, "Could not get issues for prepared SCXML document");
	
	$data = from_json($response->content());
	print Dumper($data);
	
	&finishSession($session);
	
}

&testSimpleStepping();
&testBreakpoint();
&testIssueReporting();

kill('TERM', $pid);