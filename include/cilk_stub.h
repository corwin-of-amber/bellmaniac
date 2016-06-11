
/*
 * For naive unit-testing where Cilk is not available (Cilk is part of Icc).
 */
 
#include <sys/time.h>
#define _mm_malloc(SZ,ALIGN) malloc(SZ)
#define _mm_free(PTR) free(PTR)
#define cilk_for for
inline unsigned long long cilk_getticks() {
	struct timeval tp;
	gettimeofday(&tp, NULL);
	return tp.tv_sec * 1000000 + tp.tv_usec; //get current timestamp in usec
}
inline double cilk_ticks_to_seconds(unsigned long long ticks) { return double(ticks) / 1000000.0; }
