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
	function afterMicroStep($interpreter) {
		print "MyMonitor.afterMicroStep()\n";
	}
	function beforeTakingTransitions($interpreter,$transitions) {
		print "MyMonitor.beforeTakingTransitions()\n";
	}
}

$monitor = new MyMonitor();

// run interpreter in blocking mode
$interpreter = Interpreter::fromURL('https://raw.githubusercontent.com/tklab-tud/uscxml/master/test/uscxml/test-invoked.scxml');
$interpreter->addMonitor($monitor);
$interpreter->interpret();

// interleave interpreter execution with this thread
$interpreter = Interpreter::fromURL('https://raw.githubusercontent.com/tklab-tud/uscxml/master/test/uscxml/test-invoked.scxml');
$parentQueue = new ParentQueue();
$interpreter->setParentQueue($parentQueue);

while($interpreter->step() > 0) {
	$event = $parentQueue->pop();
	print("Name: " . $event->getName() . "\n");
	print("Type: " . $event->getType() . "\n");
	print("Origin: " . $event->getOrigin() . "\n");
	print("OriginType: " . $event->getOriginType() . "\n");
	print("Content " . strlen($event->getContent()) . " bytes: \n'" . $event->getContent() . "'\n");

	$namelist = $event->getNameList();
	print("Namelist ".$namelist->size()." elements: \n");
	$keys = $event->getNameListKeys();
	for ($i = 0; $i < $keys->size(); $i++) {
		print($keys->get($i) . "\t" . Data::toJSON($namelist->get($keys->get($i))) . "\n");
	}

	$params = $event->getParamMap();
	print("Params ". $params->size() ." elements: \n");
	$keys = $event->getParamMapKeys();
	for ($i = 0; $i < $keys->size(); $i++) {
		print($keys->get($i)."\n");
		$paramList = $params->get($keys->get($i));
		for ($j = 0; $j < $paramList->size(); $j++) {
			print("\t" . Data::toJSON($paramList->get($i)) . "\n");
		}
	}
	
}

?>