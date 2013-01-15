#include <iostream>
#include <SWI-Prolog.h>
#include <SWI-cpp.h>

using namespace std;

int main(void){
  
  static char * av[] = {
    "/Users/sradomski/Documents/TK/Code/uscxml/contrib/prebuilt/darwin-i386/clang/lib/swipl-6.3.5/bin/x86_64-darwin12.2.0/swipl",
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
  rval = PlCall("system", "load_files", PlTermv("/Users/sradomski/Documents/TK/Code/pl-devel/demo/likes.pl"));
  PlQuery query("user", "likes", PlTermv("sam", "chips"));
  if (query.next_solution() > 0) {
    std::cout << "Yes!" << std::endl;
  } else {
    std::cout << "No!" << std::endl;
  }

  PlQuery q("call", PlTermv(PlCompound("likes(sam,curry)."))
  
//  PlCompound compound("likes(sam,curry).");
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
