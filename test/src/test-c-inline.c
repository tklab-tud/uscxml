#include <stdlib.h> // EXIT_SUCCESS
#include <stdio.h> // printf
#include <string.h> // memset

/**
 * Preprocess:
 * uscxml-transform -tc -i ./test-c-inline.c -o ./test-c-inline.c.scxml.c
 */

/** INLINE SCXML BEGIN
<scxml name="test-inline" datamodel="native">
	<state id="foo">
		<onentry>
			enteredFoo();
		</onentry>
	</state>
</scxml>
INLINE SCXML END */ 

/** 
 * These function can be called from within executable content
 */
void enteredFoo() {
	printf("Entered Foo!\n");
}

#include "test-c-inline.c.scxml.c"

int main(int argc, char** argv) {
	uscxml_ctx ctx;
	memset(&ctx, 0, sizeof(uscxml_ctx));
	ctx.machine = &USCXML_MACHINE_TEST_INLINE;
	
	int err = USCXML_ERR_OK;
	while(err != USCXML_ERR_DONE) {
		err = uscxml_step(&ctx);
	}
	
	return EXIT_SUCCESS;
}