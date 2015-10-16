/* Library functions to convert row major to Z morton and vice versa*/
#include <stdio.h>
#include <cilk/cilk.h>

long long N, NPDQ, NP;
int B;

#ifndef TYPE
#define TYPE int
#endif

/* Min Max and Weight Function */
#define min(a,b) (a<b?a:b)
#define max(a,b) (a>b?a:b)

void conv_RM_2_ZM_RM(TYPE *ZM, TYPE *RM, int ix, int jx, int ilen, int jlen) {
	if (ilen <= 0 || jlen <= 0)
		return;
	if (ilen <= B && jlen <= B) {
		for (int i = ix; i < ix + ilen; i++) {
#pragma ivdep
			for (int j = jx; j < jx + jlen; j++) {
				(*ZM++) = RM[(i) * N + j];
			}
		}
	} else {
		long long n = (ilen > jlen) ? ilen : jlen;
		long long c = 1;
		while (c < n)
			c = (c << 1);
		c = c >> 1;

		long long ni, nii, nj, njj;

		ni = min(c, ilen);
		nj = min(c, jlen);
		nii = max(0, ilen - c);
		njj = max(0, jlen - c);

		TYPE *x12, *x21, *x22;
		cilk_spawn conv_RM_2_ZM_RM(ZM, RM, ix, jx, ni, nj);

		x12 = ZM + ni * nj;
		cilk_spawn conv_RM_2_ZM_RM(x12, RM, ix, jx + nj, ni, njj);

		x21 = x12 + (ni * njj);

		cilk_spawn conv_RM_2_ZM_RM(x21, RM, ix + ni, jx, nii, nj);

		x22 = x21 + (nii * nj);

		conv_RM_2_ZM_RM(x22, RM, ix + ni, jx + nj, nii, njj);
		cilk_sync;
	}
}
void conv_ZM_2_RM_RM(TYPE *ZM, TYPE *RM, int ix, int jx, int ilen, int jlen) {
	if (ilen <= 0 || jlen <= 0)
		return;
	if (ilen <= B && jlen <= B) {
		for (int i = ix; i < ix + ilen; i++) {
#pragma ivdep
			for (int j = jx; j < jx + jlen; j++) {
				RM[(i) * N + j] = (*ZM++);
			}
		}
	} else {
		long long n = (ilen > jlen) ? ilen : jlen;
		long long c = 1;
		while (c < n)
			c = (c << 1);
		c = c >> 1;

		long long ni, nii, nj, njj;

		ni = min(c, ilen);
		nj = min(c, jlen);
		nii = max(0, ilen - c);
		njj = max(0, jlen - c);

		TYPE *x12, *x21, *x22;
		cilk_spawn conv_ZM_2_RM_RM(ZM, RM, ix, jx, ni, nj);

		x12 = ZM + ni * nj;
		cilk_spawn conv_ZM_2_RM_RM(x12, RM, ix, jx + nj, ni, njj);

		x21 = x12 + (ni * njj);

		cilk_spawn conv_ZM_2_RM_RM(x21, RM, ix + ni, jx, nii, nj);

		x22 = x21 + (nii * nj);

		conv_ZM_2_RM_RM(x22, RM, ix + ni, jx + nj, nii, njj);

		cilk_sync;
	}
}
