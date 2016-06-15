
/*
 * For naive unit-testing where Cilk is not available (Cilk is part of Icc).
 */

#if defined __unix__ || defined __APPLE__
#include <sys/time.h>
#define _mm_malloc(SZ,ALIGN) malloc(SZ)
#define _mm_free(PTR) free(PTR)
#else
#include <Windows.h>
#endif



#define cilk_for for
#define cilk_spawn
#define cilk_sync

