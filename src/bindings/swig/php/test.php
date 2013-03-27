<?php

require_once('uscxmlNativePHP.php');

// $exts = get_loaded_extensions();	
// foreach ($exts as $e)
// {
// 	echo "Name: ".$e." --";
// 	print_r(get_extension_funcs($e));
// }

class MyMonitor extends InterpreterMonitor {
	function beforeExitingStates($interpreter,$statesToExit) {
		print "MyMonitor.beforeExitingStates()\n";
	}
	function afterExitingStates($interpreter) {
		print "MyMonitor.afterExitingStates()\n";
	}
	function beforeEnteringStates($interpreter,$statesToEnter) {
		print "MyMonitor.beforeEnteringStates()\n";
	}
	function afterEnteringStates($interpreter) {
		print "MyMonitor.afterEnteringStates()\n";
	}
	function onStableConfiguration($interpreter) {
		print "MyMonitor.onStableConfiguration()\n";
	}
	function beforeCompletion($interpreter) {
		print "MyMonitor.beforeCompletion()\n";
	}
	function afterCompletion($interpreter) {
		print "MyMonitor.afterCompletion()\n";
	}
	function beforeMicroStep($interpreter) {
		print "MyMonitor.beforeMicroStep()\n";
	}
	function beforeTakingTransitions($interpreter,$transitions) {
		print "MyMonitor.beforeTakingTransitions()\n";
	}
}

$monitor = new MyMonitor();

// run interpreter in blocking mode
$interpreter = Interpreter::fromURI('https://raw.github.com/tklab-tud/uscxml/master/test/samples/uscxml/test-ecmascript.scxml');
$interpreter->addMonitor($monitor);
$interpreter->interpret();

// start interpreter as a thread
$interpreter = Interpreter::fromURI('/Users/sradomski/Documents/TK/Code/uscxml/test/samples/uscxml/test-invoked.scxml');
$parentQueue = new ParentQueue();
$interpreter->setParentQueue($parentQueue);
$interpreter->start();

while($interpreter->isRunning()) {
	$event = $parentQueue->pop();
	print("Name: " . $event->getName() . "\n");
	print("Type: " . $event->getType() . "\n");
	print("Origin: " . $event->getOrigin() . "\n");
	print("OriginType: " . $event->getOriginType() . "\n");
	print("Content " . strlen($event->getContent()) . "bytes: \n'" . $event->getContent() . "'\n");

	$namelist = $event->getNameList();
	print("Namelist ".$namelist->size()." elements: \n");
	$keys = $event->getNameListKeys();
	for ($i = 0; $i < $keys->size(); $i++) {
		print($keys->get($i) . "\t" . $namelist->get($keys->get($i)) . "\n");
	}

	$params = $event->getParams();
	print("Params ". $params->size() ." elements: \n");
	$keys = $event->getParamKeys();
	for ($i = 0; $i < $keys->size(); $i++) {
		print($keys->get($i)."\n");
		$paramList = $params->get($keys->get($i));
		for ($j = 0; $j < $paramList->size(); $j++) {
			print("\t" . $paramList->get($i) . "\n");
		}
	}
	
}

?>