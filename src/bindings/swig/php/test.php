<?php

require_once('uscxmlNativePHP.php');

$exts = get_loaded_extensions();	
foreach ($exts as $e)
{
	echo "Name: ".$e." --";
	print_r(get_extension_funcs($e));
}

class MyMonitor extends InterpreterMonitor {
	function onStableConfiguration($interpreter) {
    print "MyMonitor.onStableConfiguration()\n";
  }
	function beforeCompletion($interpreter) {
    print "MyMonitor.beforeCompletion()\n";
	}
	function afterCompletion($interpreter) {
    print "MyMonitor.afterCompletion()\n";
	}
};

$monitor = new MyMonitor();

$interpreter = Interpreter::fromURI('https://raw.github.com/tklab-tud/uscxml/master/test/samples/uscxml/test-ecmascript.scxml');
$interpreter->addMonitor($monitor);
$interpreter->interpret();

?>