
/*
 * For naive unit-testing where Cilk is not available (Cilk is part of Icc).
 */
 
#include <sys/time.h>

#define _mm_malloc(SZ,ALIGN) malloc(SZ)
#define _mm_free(PTR) free(PTR)

#define cilk_for for
#define cilk_spawn
#define cilk_sync

