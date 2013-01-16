#include <iostream>
#include <SWI-Prolog.h>
#include <SWI-cpp.h>
#include "uscxml/config.h"

using namespace std;

int main(void){
  const char* swibin = getenv("SWI_BINARY");
  if (swibin == NULL)
    swibin = SWI_BINARY;
  
  static char * av[] = {
    (char*)swibin,
//    "--quiet",
//    "-s",
//    "/Users/sradomski/Documents/TK/Code/pl-devel/demo/likes.pl",
    NULL};
  if( ! PL_initialise(1,av)){
    cout<<"error initializing"<<endl;
    PL_halt(1);
  }else {
    cout<<"success initializing!"<<endl;
  }
  
//  unsigned long fid = PL_open_foreign_frame();

  int rval;
  PlFrame frame;
  rval = PlCall("user", "load_files", PlTermv("/Users/sradomski/Documents/TK/Code/pl-devel/demo/likes.pl"));

//  PlCompound compound("likes(sam, X)");
  PlCompound compound("listing");
  PlTermv termv(compound.arity());
//  termv[0] = PlTerm();
  for (int i = 0; i < compound.arity(); i++) {
    termv[i] = compound[i + 1];
  }

  PlQuery q(compound.name(), termv);
  bool solutionExists = false;
  while( q.next_solution() ) {
    solutionExists = true;
    for (int i = 0; i < compound.arity(); i++) {
      switch (compound[i + 1].type()) {
        case PL_VARIABLE:
          std::cout << (char *)termv[i] << ", ";
          break;
        case PL_FLOAT:
          std::cout << (double)termv[i] << ", ";
          break;
        case PL_ATOM:
          std::cout << (PlAtom)termv[i] << ", ";
          break;
        case PL_STRING:
          std::cout << (char *)termv[i] << ", ";
          break;
        case PL_TERM:
          std::cout << (char *)termv[i] << ", ";
          break;
        default: ;
      }
    }
    std::cout << std::endl;
  }

  
//  PlQuery query2(compound.name(), PlTermv(compound));
//  if (query2.next_solution() > 0) {
//    std::cout << "Yes!" << std::endl;
//  } else {
//    std::cout << "No!" << std::endl;
//  }
  
//  std::cout << compound.name() << std::endl;
//  PlTermv filename("/Users/sradomski/Documents/TK/Code/pl-devel/demo/likes.pl");
//  PlQuery loadFiles("system", "load_files", filename);
  
//  predicate_t loadFiles = PL_predicate("load_files",1,"system");
//  term_t h0 = PL_new_term_refs(1);
  
//  int rval;
//  const char * expression = "/Users/sradomski/Documents/TK/Code/pl-devel/demo/likes.pl";
//  PL_put_atom_chars(h0,expression);
//  rval = PL_call_predicate(NULL, PL_Q_NORMAL, loadFiles, h0);

//  PL_halt( rval ? 0 : 1 );
  
//  PL_close_foreign_frame(fid);
  return 0;
}
