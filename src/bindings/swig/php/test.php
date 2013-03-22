<?php
$exts = get_loaded_extensions();	
foreach ($exts as $e)
{
	echo "Name: ".$e." --";
	print_r(get_extension_funcs($e));
}

$interpreter = interpreter_fromuri('https://raw.github.com/tklab-tud/uscxml/master/test/samples/uscxml/test-ecmascript.scxml');
interpreter_interpret($interpreter);

?>