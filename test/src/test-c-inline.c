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
        <transition target="done" cond="UD->foo == 3" />
		<onentry>
			enteredFoo();
		</onentry>
	</state>
    <final id="done">
        <onentry>
            enteredDone();
        </onentry>
    </final>
</scxml>
INLINE SCXML END */ 

/** 
 * These function can be called from within executable content
 */
void enteredFoo() {
	printf("Entered Foo!\n");
}

void enteredDone() {
    printf("Entered Done!\n");
}

struct userData {
    int foo;
};

#define UD ((struct userData*)ctx->user_data)
#include "test-c-inline.c.scxml.c"


int main(int argc, char** argv) {
    struct userData ud;
    uscxml_ctx ctx;
	int err = USCXML_ERR_OK;
    
	memset(&ctx, 0, sizeof(uscxml_ctx));
	ctx.machine = &USCXML_MACHINE_TEST_INLINE;
    ctx.user_data = &ud;
    ud.foo = 3;
    
	while(err != USCXML_ERR_DONE) {
		err = uscxml_step(&ctx);
	}
	
	return EXIT_SUCCESS;
}