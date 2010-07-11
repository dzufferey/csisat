#include <stdio.h>
#include <stdlib.h>
#include <string.h>
  
#include <caml/alloc.h>
#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <caml/callback.h>

static const char * interpolate_string(const char * s) {
  CAMLparam0();
  CAMLlocal1(ostr);
  
  ostr = caml_copy_string(s);
  
  value *func = caml_named_value("interpolate_string");

  if (NULL == func) {
    puts("caml_named_value failed!");
    return NULL;
  } else {
    return strdup(String_val(caml_callback(*func, ostr)));
  }
}
  
int main(int argc, char **argv) { 
  caml_startup(argv);
  puts(interpolate_string("blablabla"));
  return 0;
}
