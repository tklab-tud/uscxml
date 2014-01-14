#include <tcl.h>
#include <expect_tcl.h>
#include <expect.h>
#include <stdlib.h>

int main(int argc, char** argv) {
	int rc = 0;

	Tcl_Interp *interp = Tcl_CreateInterp();
	Tcl_FindExecutable(argv[0]);

	if (Tcl_Init(interp) == TCL_ERROR) {
	    fprintf(stderr,"Tcl_Init failed: %s\n",Tcl_GetStringResult (interp));
	    (void) exit(1);
	}

	if (Expect_Init(interp) == TCL_ERROR) {
	    fprintf(stderr,"Expect_Init failed: %s\n",Tcl_GetStringResult (interp));
	    (void) exit(1);
	}
  
	exp_loguser = 1;
	exp_is_debugging = 1;
	exp_timeout = 3;
	
	FILE *fp;
	int ec;
//	char* program = "/usr/bin/telnet localhost 80";
//	if (0 > (ec = exp_spawnl("sh","sh","-c",program,(char *)0)))
//		exit(0);
//	if (NULL == (fp = fdopen(ec,"r+")))
//		exit(0);
//	setbuf(fp,(char *)0);

	if (0 > (ec = exp_spawnl("/usr/bin/telnet", "/usr/bin/telnet","localhost", "80", (char *)0)))
		exit(0);
	if (NULL == (fp = fdopen(ec,"r+")))
		exit(0);
	setbuf(fp,(char *)0);

	switch (exp_fexpectl(fp,
											 exp_glob, "qConnected to", 1,
											 exp_glob, "qConnection failed", 2,
											 exp_end)) {
		case 1:
			printf("SUCCESS!");
			fprintf(fp, "%s\r", "GET /");

			break;
		case 2:
			printf("FAIL!");
			break;
			
		default:
			break;
	}
  exit(EXIT_SUCCESS);
}