/* Force-included into every C file of this package (lakefile.lean). Lake compiles each module
   twice: with LEAN_EXPORTING for shared libraries and the interpreter, and without it for the
   objects that executables link (the library's `nativeFacets`). In the second build every
   declaration is hidden, so that the globals of other modules (the float constants of the
   hot loops) are read directly rather than through the global offset table; the objects stay
   position-independent. The C library's functions stay default: they live in shared libraries.
   Lake does not track this file: after editing it, rebuild the C objects (`lake clean`). */
#ifndef LEAN_EXPORTING
double exp(double) __attribute__((visibility("default")));
double log(double) __attribute__((visibility("default")));
#pragma GCC visibility push(hidden)
#endif
