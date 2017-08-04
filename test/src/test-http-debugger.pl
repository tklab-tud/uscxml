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
use Term::ANSIColor 4.00 qw(RESET :constants);

my $scxmlBin = shift;
die ("First argument needs to be path to uscxml-browser binary") if (!$scxmlBin);
die("'" . $scxmlBin . "' is not an executable file") if (! -x $scxmlBin || ! -f $scxmlBin);

my $baseDir = File::Spec->canonpath(dirname($0));
chdir $baseDir;

my $ua = LWP::UserAgent->new;
my $request;
my $response;
my $data;
my @breakpointSeq;

my $pid = fork;

# child process to run the interpreter
if (!$pid) {
	open STDOUT, ">",  "/dev/null" or die "$0: open: $!";
	open STDERR, ">&", \*STDOUT    or exit 1;
	exec("$scxmlBin -t4088 -d test-http-debugger.scxml");
	exit;
}

my $baseURL = 'http://localhost:4088/debug';
# my $baseURL = 'http://localhost:5080/debug';
sleep(1);

sub dumpRequest {
	# http://search.cpan.org/~oalders/HTTP-Message-6.13/lib/HTTP/Request.pm
	my $request = shift;
	return 
		"\tURI:     " . $request->uri() . "\n" .
		"\tCONTENT: " . $request->content() . "\n";
}

sub dumpResponse {
	# http://search.cpan.org/~oalders/HTTP-Message-6.13/lib/HTTP/Response.pm
	my $response = shift;
	return
		"\tCONTENT: " . $response->content() . "\n";
}

sub post {
	my $path = shift;
	my $session = shift;
	my $data = shift || {};

	$data->{'session'} = $session;

	my $response;

	# read reply until we have something other than a log message from the server
	while(1) {
		my $request = POST $baseURL.$path, $data;
		print RED . "-> SEND === line:" . __LINE__ . "\n" . dumpRequest($request) . RESET . "\n";
		$response = $ua->request($request);
		print CYAN . "<- RCVD === line:" . __LINE__ . "\n" . dumpResponse($response) . RESET . "\n";
		
		# skip log messages
		last if ($path ne '/poll');
		last if (!exists from_json($response->content())->{'severity'});

	}
	return $response;
}

sub assertSuccess {
	my $response = shift;
	my $message = shift;
	from_json($response->content())->{'status'} eq "success" or die($message);
}

sub assertFailure {
	my $response = shift;
	my $message = shift;
	from_json($response->content())->{'status'} eq "failure" or die($message);
}

sub attachSession {
	my $docName = shift;

	$request = POST $baseURL.'/instances';
	print FAINT RED . "-> SEND === line:" . __LINE__ . "\n" . dumpRequest($request) . RESET . "\n";
	$response = $ua->request($request);
	print FAINT CYAN . "<- RCVD === line:" . __LINE__ . "\n" . dumpResponse($response) . RESET . "\n";
	assertSuccess($response, "Could not get running sessions");

	my $attach = "";
	my $sessions = from_json($response->content())->{'instances'};
	foreach my $instance (@{$sessions}) {
		if ($instance->{'name'} eq $docName) {
			$attach = $instance->{'id'};
			last;
		}
	}
	$attach or die("Could not attach to instance named $docName\n");

	### Get a session
	my $request = GET $baseURL.'/connect';
	print FAINT RED . "-> SEND === line:" . __LINE__ . "\n" . dumpRequest($request) . RESET . "\n";
	$response = $ua->request($request);
	print FAINT CYAN . "<- RCVD === line:" . __LINE__ . "\n" . dumpResponse($response) . RESET . "\n";
	assertSuccess($response, "Could not connect");

	my $session = from_json($response->content())->{'session'};
	die("Cannot acquire session from server") if (!$session);

	$request = POST $baseURL.'/attach', 
		[
			'attach' => $attach,
			'session' => $session,
		];
	print FAINT RED . "-> SEND === line:" . __LINE__ . "\n" . dumpRequest($request) . RESET . "\n";
	$response = $ua->request($request);
	print FAINT CYAN . "<- RCVD === line:" . __LINE__ . "\n" . dumpResponse($response) . RESET . "\n";
	assertSuccess($response, "Could not get attach to session");
	print BOLD BLACK . "Session attached!" . RESET . "\n\n";
	return $session;
}

sub prepareSession {
	my $source = shift;

	### Get a session
	my $request = GET $baseURL.'/connect';
	print FAINT RED . "-> SEND === line:" . __LINE__ . "\n" . dumpRequest($request) . RESET . "\n";
	$response = $ua->request($request);
	print FAINT CYAN . "<- RCVD === line:" . __LINE__ . "\n" . dumpResponse($response) . RESET . "\n";
	assertSuccess($response, "Could not connect");

	my $session = from_json($response->content())->{'session'};
	die("Cannot acquire session from server") if (!$session);

	$source->{'session'} = $session;

	### Prepare an SCXML interpreter
	$request = POST $baseURL.'/prepare', $source;
	print FAINT RED . "-> SEND === line:" . __LINE__ . "\n" . dumpRequest($request) . RESET . "\n";
	$response = $ua->request($request);
	print FAINT CYAN . "<- RCVD === line:" . __LINE__ . "\n" . dumpResponse($response) . RESET . "\n";
	assertSuccess($response, "Could not prepare SCXML");
	print BOLD BLACK . "Session prepared!" . RESET . "\n\n";
	return $session;
}

sub finishSession {
	my $session = shift;
	
	### Prepare an SCXML interpreter
	$request = POST $baseURL.'/disconnect', 
		[
			'session' => $session,
		];
	print FAINT RED . "-> SEND === line:" . __LINE__ . "\n" . dumpRequest($request) . RESET . "\n";
	$response = $ua->request($request);
	print FAINT CYAN . "<- RCVD === line:" . __LINE__ . "\n" . dumpResponse($response) . RESET . "\n";
	assertSuccess($response, "Could not disconnect session");
	print BOLD BLACK . "Session terminated!" . RESET . "\n\n";
}

sub popAndCompare {
	my $qualified = shift;
	my $bp = shift(@breakpointSeq);
	for my $key (keys %{$bp}) {
		if (! exists($qualified->{$key}) || $qualified->{$key} ne $bp->{$key}) {
			print "found:    ".Dumper($qualified);
			print "expected: ".Dumper($bp);
			die("Expected different breakpoint");
		}
	}
	print BOLD BLACK . "OK!" . RESET . "\n\n";
}

sub testSimpleStepping {

	print BOLD WHITE ON_RED . "                      " . RESET ."\n";
	print BOLD WHITE ON_RED . "  testSimpleStepping  " . RESET ."\n";
	print BOLD WHITE ON_RED . "                      " . RESET ."\n\n";

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
		{ subject => "state",      when => "after",  action => "enter" },
		{ subject => "state",      when => "before", action => "enter", stateId => "s1" },
		{ subject => "executable", when => "before", execName => "log" },
		{ subject => "executable", when => "after",  execName => "log" },
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

	my $session = &prepareSession({'xml' => $xml});
	
	print BOLD . "Testing sequence of breakpoints being raised via step". RESET . "\n";

	while(@breakpointSeq > 0) {
		### Take a step

		$response = post('/step', $session);
		assertSuccess($response, "Could not step");

		### Get the pending messages
		$response = post('/poll', $session);
		assertSuccess($response, "Could not get breakpoint after step");

		# compare to what we expect
		$data = from_json($response->content());
		popAndCompare($data->{'qualified'});
	}
	
	### last step will finalize the interpreter
	$response = post('/step', $session);
	assertSuccess($response, "Could not step");

	### get the pending server push reply
	$response = post('/poll', $session);
	assertSuccess($response, "Could not get breakpoint after step");

	$data = from_json($response->content());
	die("Machine not yet finished") if ($data->{'replyType'} ne "finished");

	&finishSession($session);
}

sub testBreakpoint {

	print BOLD WHITE ON_RED . "                  " . RESET ."\n";
	print BOLD WHITE ON_RED . "  testBreakpoint  " . RESET ."\n";
	print BOLD WHITE ON_RED . "                  " . RESET ."\n\n";

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
	
	my $session = &prepareSession({'xml' => $xml});
	
	print BOLD . "Adding a dedicated breakpoint". RESET . "\n";
	$response = post('/breakpoint/add', $session, {
		'session' => $session,
		'when' => 'after',
		'action' => 'enter',
		'subject' => 'state',
		'stateId' => 's1'
	});
	assertSuccess($response, "Could not add breakpoint");

	print BOLD . "Starting interpretation (will run into breakpoint)". RESET . "\n";
	$response = post('/start', $session);
	assertSuccess($response, "Could not start interpreter");

	print BOLD . "Polling asynchronously for breakpoint hit by interpreter". RESET . "\n";
	$response = post('/poll', $session);
	assertSuccess($response, "Could not poll for breakpoint");

	print BOLD . "Skipping to implicit breakpoint". RESET . "\n";
	$response = post('/breakpoint/skipto', $session, {
		'session' => $session,
		'when' => 'before',
		'action' => 'enter',
		'subject' => 'state',
		'stateId' => 's2'
	});
	assertSuccess($response, "Could not skip to breakpoint");

	print BOLD . "Polling asynchronously for breakpoint hit by interpreter". RESET . "\n";
	$response = post('/poll', $session);
	assertSuccess($response, "Could not poll for breakpoint");
	
	$data = from_json($response->content());
	print Dumper($data);
	
	&finishSession($session);
}

sub testIssueReporting {

	print BOLD WHITE ON_RED . "                      " . RESET ."\n";
	print BOLD WHITE ON_RED . "  testIssueReporting  " . RESET ."\n";
	print BOLD WHITE ON_RED . "                      " . RESET ."\n\n";

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

	my $session = prepareSession({'xml' => $xml});
	
	print BOLD . "Getting a list of issues with the document". RESET . "\n";

	### Get a list of issues
	$response = post('/issues', $session);
	assertSuccess($response, "Could not get issues for prepared SCXML document");
	
	$data = from_json($response->content());
	print Dumper($data);
	
	&finishSession($session);
	
}

sub testDataModelInspection {

	print BOLD WHITE ON_RED . "                           " . RESET ."\n";
	print BOLD WHITE ON_RED . "  testDataModelInspection  " . RESET ."\n";
	print BOLD WHITE ON_RED . "                           " . RESET ."\n\n";

	my $session = prepareSession({'url' => 'https://raw.githubusercontent.com/tklab-tud/uscxml/master/test/w3c/ecma/test144.scxml'});

	print BOLD . "Skipping to first transition". RESET . "\n";
	$response = post('/breakpoint/skipto', $session, {
		'when' => 'before',
		'subject' => 'transition',
		'target' => 's1'
	});
	assertSuccess($response, "Could not add breakpoint");

	print BOLD . "Polling asynchronously for breakpoint hit by interpreter". RESET . "\n";
	$response = post('/poll', $session);
	assertSuccess($response, "Could not get breakpoint after step");


	print BOLD . "Evaluating expression '_event' on the datamodel". RESET . "\n";
	$response = post('/eval', $session, {
		'expression' => '_event'
	});
	assertSuccess($response, "Could not evaluate expression");

	print BOLD . "Evaluating expression '_event' on the datamodel". RESET . "\n";
	$response = post('/eval', $session, {
		'expression' => '_ioprocessors'
	});
	assertSuccess($response, "Could not evaluate expression");


	&finishSession($session);

}

sub testSessionAttaching {

	print BOLD WHITE ON_RED . "                        " . RESET ."\n";
	print BOLD WHITE ON_RED . "  testSessionAttaching  " . RESET ."\n";
	print BOLD WHITE ON_RED . "                        " . RESET ."\n\n";

	my $session = attachSession("test-http-debugger.scxml");

	print BOLD . "Skipping to first transition". RESET . "\n";
	$response = post('/breakpoint/skipto', $session, {
		'when' => 'before',
		'subject' => 'transition',
		'target' => 's1'
	});
	assertSuccess($response, "Could not add breakpoint");

	print BOLD . "Polling asynchronously for breakpoint hit by interpreter". RESET . "\n";
	$response = post('/poll', $session);
	assertSuccess($response, "Could not get breakpoint after step");

	&finishSession($session);

}

sub testEventInsertion {

	print BOLD WHITE ON_RED . "                      " . RESET ."\n";
	print BOLD WHITE ON_RED . "  testEventInsertion  " . RESET ."\n";
	print BOLD WHITE ON_RED . "                      " . RESET ."\n\n";

	my $xml = << 'END_SCXML';
	<scxml>
		<state id='s1'>
			<onentry>
				<log label="'foo'" />
			</onentry>
			<transition target='pass' event='bar' />
		</state>
		<final id='pass' />
	</scxml>
END_SCXML

	my $session = prepareSession({'xml' => $xml});

	print BOLD . "Sending event" . RESET . "\n";
	$response = post('/event', $session, {
		'name' => 'foo',
	});
	assertSuccess($response, "Could not send event");

	&finishSession($session);

}


sub testRunningStates {

	print BOLD WHITE ON_RED . "                      " . RESET ."\n";
	print BOLD WHITE ON_RED . "  testEventInsertion  " . RESET ."\n";
	print BOLD WHITE ON_RED . "                      " . RESET ."\n\n";

	my $session = attachSession("test-http-debugger.scxml");

	print BOLD . "Stopping the intepreter". RESET . "\n";
	$response = post('/stop', $session);
	assertFailure($response, "Should not be able to stop attached interpreter");

	print BOLD . "Starting the intepreter". RESET . "\n";
	$response = post('/start', $session);
	assertFailure($response, "Should not be able to start attached interpreter");

	print BOLD . "Pausing the intepreter". RESET . "\n";
	$response = post('/pause', $session);
	assertSuccess($response, "Could not pause the attached interpreter");

	print BOLD . "Polling state of paused interpreter". RESET . "\n";
	$response = post('/poll', $session);
	assertSuccess($response, "Could not poll state of paused interpreter");

	print BOLD . "Pausing the intepreter again". RESET . "\n";
	$response = post('/pause', $session);
	assertFailure($response, "Should not be able to pause attached interpreter twice");

	print BOLD . "Resuming the intepreter". RESET . "\n";
	$response = post('/resume', $session);
	assertSuccess($response, "Could not resume the attached interpreter");

	print BOLD . "Resuming the intepreter again". RESET . "\n";
	$response = post('/resume', $session);
	assertFailure($response, "Should not be able to resume attached interpreter twice");

	&finishSession($session);

}

sub testLogReception {

	print BOLD WHITE ON_RED . "                    " . RESET ."\n";
	print BOLD WHITE ON_RED . "  testLogReception  " . RESET ."\n";
	print BOLD WHITE ON_RED . "                    " . RESET ."\n\n";

	my $session = prepareSession({'url' => abs_path($baseDir).'/test-http-debugger.scxml'});

	print BOLD . "Starting the intepreter". RESET . "\n";
	$response = post('/start', $session);
	assertSuccess($response, "Could not start interpreter");

	for (my $i = 0; $i < 5; $i++) {
		print BOLD . "Polling interpreter for messages". RESET . "\n";
		# the trailing /# is only for poll above not to disregard the message
		# You would just use /poll to get any pending message from the server
		$response = post('/poll/#', $session);
		assertSuccess($response, "Could not poll for messages");
	}

	&finishSession($session);

}

&testSimpleStepping();
&testBreakpoint();
&testIssueReporting();
&testDataModelInspection();
&testSessionAttaching();
&testEventInsertion();
&testRunningStates();
&testLogReception();

kill('TERM', $pid);