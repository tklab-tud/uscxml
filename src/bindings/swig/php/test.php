<?php
$exts = get_loaded_extensions();	
foreach ($exts as $e)
{
	echo "Name: ".$e." --";
	print_r(get_extension_funcs($e));
}

$interpreter = interpreter_fromuri('/Users/sradomski/Documents/TK/Code/uscxml/test/samples/uscxml/test-ecmascript.scxml');

?>