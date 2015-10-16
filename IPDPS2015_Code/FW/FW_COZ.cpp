//@Copyright: Jesmin Jahan Tithi, Rezaul Chowdhury, Department of Computer
// Science, Stony Brook University, Ny-11790
// Contact: jtithi@cs.stonybrook.edu,

// compile with :icpc -O3 -AVX  -xhost -o  fwr FW_rec.cpp  -ansi-alias -ip
// -opt-subscript-in-range -opt-prefetch=4 -fomit-frame-pointer
// -funroll-all-loops -vec-report  -parallel -restrict

#include <time.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/timeb.h>
#include <iostream>
#include <pthread.h>
#include <cilk/cilk.h>
#include <cilk/cilk_api.h>
#include <math.h>
#include <immintrin.h>
#include "cilktime.h"

using namespace std;
#ifdef USE_PAPI
#include "papilib.h"
#endif
#ifndef TYPE
#define TYPE int
#endif

#ifndef ALIGNMENT
#define ALIGNMENT 64
#endif

int N, B, NP;
TYPE *dist, *X, *D;

#define min(a, b) (a < b ? a : b)
#define max(a, b) (a > b ? a : b)

void conv_RM_2_ZM_RM(TYPE *x, int ix, int jx, int ilen, int jlen) {
	if (ilen <= 0 || jlen <= 0)
		return;
	if (ilen <= B && jlen <= B) {
		for (int i = ix; i < ix + ilen; i++) {
#pragma ivdep
			for (int j = jx; j < jx + jlen; j++) {
				(*x++) = dist[(i) * (N) + j];
			}
		}
	} else {
		int n = (ilen > jlen) ? ilen : jlen;
		int c = 1;
		while (c < n)
			c = (c << 1);
		register int nn = c >> 1;

		int n11, n12, n21;
		int ni, nii, nj, njj;

		ni = min(nn, ilen);
		nj = min(nn, jlen);
		nii = max(0, ilen - nn);
		njj = max(0, jlen - nn);

		n11 = ni * nj;
		n12 = ni * njj;
		n21 = nii * nj;

		TYPE *x12, *x21, *x22;
		cilk_spawn conv_RM_2_ZM_RM(x, ix, jx, ni, nj);

		x12 = x + n11;
		cilk_spawn conv_RM_2_ZM_RM(x12, ix, jx + nj, ni, njj);

		x21 = x12 + (n12);

		cilk_spawn conv_RM_2_ZM_RM(x21, ix + ni, jx, nii, nj);

		x22 = x21 + (n21);

		conv_RM_2_ZM_RM(x22, ix + ni, jx + nj, nii, njj);

		cilk_sync;
	}
}
void conv_ZM_2_RM_RM(TYPE *x, TYPE *V, int ix, int jx, int ilen, int jlen) {
	if (ilen <= 0 || jlen <= 0)
		return;
	if (ilen <= B && jlen <= B) {
		for (int i = ix; i < ix + ilen; i++) {
#pragma ivdep
			for (int j = jx; j < jx + jlen; j++) {
				V[(i) * (N) + j] = (*x++);
			}
		}
	} else {
		int n = (ilen > jlen) ? ilen : jlen;
		int c = 1;
		while (c < n)
			c = (c << 1);
		register int nn = c >> 1;

		int n11, n12, n21;
		int ni, nii, nj, njj;

		ni = min(nn, ilen);
		nj = min(nn, jlen);
		nii = max(0, ilen - nn);
		njj = max(0, jlen - nn);

		n11 = ni * nj;
		n12 = ni * njj;
		n21 = nii * nj;

		TYPE *x12, *x21, *x22;
		cilk_spawn conv_ZM_2_RM_RM(x, V, ix, jx, ni, nj);

		x12 = x + n11;
		cilk_spawn conv_ZM_2_RM_RM(x12, V, ix, jx + nj, ni, njj);

		x21 = x12 + (n12);

		cilk_spawn conv_ZM_2_RM_RM(x21, V, ix + ni, jx, nii, nj);

		x22 = x21 + (n21);

		conv_ZM_2_RM_RM(x22, V, ix + ni, jx + nj, nii, njj);

		cilk_sync;
	}
}

/* Only for power of 2*/

void func_D(TYPE *x, TYPE *u, TYPE *v, int n) {
	if (n <= B) {
#ifdef USE_PAPI
		int id = tid();
		int retval = 0;
		papi_for_thread(id);
		if ((retval = PAPI_start(EventSet[id])) != PAPI_OK) ERROR_RETURN(retval);
#endif
		__declspec(align(64)) TYPE V[n * n];

		int uin = 0;

#pragma parallel
		for (int i = 0; i < n; i++) {
			int in = i * n;
#pragma ivdep
			for (int j = 0; j < n; j++) {
				V[j * n + i] = v[in + j];
			}
		}

		TYPE *uu, *vv;
		int in = 0;
		uin = 0;
#pragma parallel
		for (int i = 0; i < n; i++) {
			for (int j = 0; j < n; j++) {
				TYPE x_ij = x[in + j];

				uu = u + uin;
				vv = V + j * n;
#pragma ivdep
				for (int k = 0; k < n; k++) {
					x_ij = min(x_ij, (*uu + *vv));
					uu++;
					vv++;
				}
				x[in + j] = x_ij;
			}
			in = in + n;
			uin = uin + n;
		}
#ifdef USE_PAPI
		countMisses(id);
#endif
		return;

	} else {
		int nn = (n >> 1);
		int nn2 = nn * nn;

		const int m11 = 0;
		int m12 = m11 + nn2;
		int m21 = m12 + nn2;
		int m22 = m21 + nn2;

		cilk_spawn func_D(x + m11, u + m11, v + m11, nn);
		cilk_spawn func_D(x + m12, u + m11, v + m12, nn);
		cilk_spawn func_D(x + m21, u + m21, v + m11, nn);
		func_D(x + m22, u + m21, v + m12, nn);

		cilk_sync;

		cilk_spawn func_D(x + m11, u + m12, v + m21, nn);
		cilk_spawn func_D(x + m12, u + m12, v + m22, nn);
		cilk_spawn func_D(x + m21, u + m22, v + m21, nn);
		func_D(x + m22, u + m22, v + m22, nn);

		cilk_sync;
	}
}

void func_C(TYPE *x, TYPE *u, TYPE *v, int n) {
	if (n <= B) {
#ifdef USE_PAPI
		int id = tid();
		int retval = 0;
		papi_for_thread(id);
		if ((retval = PAPI_start(EventSet[id])) != PAPI_OK) ERROR_RETURN(retval);
#endif
		register TYPE uv;
		TYPE *xx, *uu, *vv;

		xx = x;
		uu = u;
		vv = v;

		for (int k = 0; k < n; k++) {
#pragma parallel
			for (int i = 0; i < n; i++) {
#pragma ivdep
				for (int j = 0; j < n; j++) {
					uv = (*uu) + (*vv++);
					*xx = min(uv, *xx);
					xx++;
				}
				vv = vv - B;
				uu = uu + B;
			}
			xx = x;
			vv = vv + B;
			uu = u + k + 1;
		}
#ifdef USE_PAPI
		countMisses(id);
#endif
		return;
	} else {
		int nn = (n >> 1);
		int nn2 = nn * nn;

		const int m11 = 0;
		int m12 = m11 + nn2;
		int m21 = m12 + nn2;
		int m22 = m21 + nn2;

		cilk_spawn func_C(x + m11, u + m11, v + m11, nn);
		func_C(x + m21, u + m21, v + m11, nn);
		cilk_sync;
		cilk_spawn func_D(x + m12, u + m11, v + m12, nn);
		func_D(x + m22, u + m21, v + m12, nn);

		cilk_sync;

		cilk_spawn func_C(x + m12, u + m12, v + m22, nn);
		func_C(x + m22, u + m22, v + m22, nn);
		cilk_sync;

		cilk_spawn func_D(x + m11, u + m12, v + m21, nn);
		func_D(x + m21, u + m22, v + m21, nn);

		cilk_sync;
	}
}

void func_B(TYPE *x, TYPE *u, TYPE *v, int n) {
	if (n <= B) {
#ifdef USE_PAPI
		int id = tid();
		int retval = 0;
		papi_for_thread(id);
		if ((retval = PAPI_start(EventSet[id])) != PAPI_OK) ERROR_RETURN(retval);
#endif
		register TYPE uv;
		TYPE *xx, *uu, *vv;

		xx = x;
		uu = u;
		vv = v;

		for (int k = 0; k < n; k++) {
#pragma parallel
			for (int i = 0; i < n; i++) {
#pragma ivdep
				for (int j = 0; j < n; j++) {
					uv = (*uu) + (*vv++);

					*xx = min(uv, *xx);
					xx++;
				}
				vv = vv - B;
				uu = uu + B;
			}
			xx = x;
			vv = vv + B;
			uu = u + k + 1;
		}
#ifdef USE_PAPI
		countMisses(id);
#endif
		return;

	} else {
		int nn = (n >> 1);
		int nn2 = nn * nn;

		const int m11 = 0;
		int m12 = m11 + nn2;
		int m21 = m12 + nn2;
		int m22 = m21 + nn2;

		cilk_spawn func_B(x + m11, u + m11, v + m11, nn);
		func_B(x + m12, u + m11, v + m12, nn);
		cilk_sync;

		cilk_spawn func_D(x + m21, u + m21, v + m11, nn);
		func_D(x + m22, u + m21, v + m12, nn);
		cilk_sync;

		cilk_spawn func_B(x + m21, u + m22, v + m21, nn);
		func_B(x + m22, u + m22, v + m22, nn);

		cilk_sync;
		cilk_spawn func_D(x + m11, u + m12, v + m21, nn);
		func_D(x + m12, u + m12, v + m22, nn);
		cilk_sync;
	}
}

void func_A(TYPE *x, TYPE *u, TYPE *v, int n) {
	if (n <= B) {
#ifdef USE_PAPI
		int id = tid();
		int retval = 0;
		papi_for_thread(id);
		if ((retval = PAPI_start(EventSet[id])) != PAPI_OK) ERROR_RETURN(retval);
#endif
		register TYPE uv;
		TYPE *xx, *uu, *vv;

		xx = x;
		uu = u;
		vv = v;

		for (int k = 0; k < n; k++) {
#pragma parallel
			for (int i = 0; i < n; i++) {
#pragma ivdep
				for (int j = 0; j < n; j++) {
					uv = (*uu) + (*vv++);
					*xx = min(uv, *xx);
					xx++;
				}
				vv = vv - B;
				uu = uu + B;
			}
			xx = x;
			vv = vv + B;
			uu = u + k + 1;
		}
#ifdef USE_PAPI
		countMisses(id);
#endif
		return;

	} else {
		int nn = (n >> 1);
		int nn2 = nn * nn;

		const int m11 = 0;
		int m12 = m11 + nn2;
		int m21 = m12 + nn2;
		int m22 = m21 + nn2;

		func_A(x + m11, u + m11, v + m11, nn);

		cilk_spawn func_B(x + m12, u + m11, v + m12, nn);
		cilk_spawn func_C(x + m21, u + m21, v + m11, nn);
		cilk_sync;

		func_D(x + m22, u + m21, v + m12, nn);

		func_A(x + m22, u + m22, v + m22, nn);
		cilk_spawn func_B(x + m21, u + m22, v + m21, nn);
		cilk_spawn func_C(x + m12, u + m12, v + m22, nn);
		cilk_sync;
		func_D(x + m11, u + m12, v + m21, nn);
	}
}
void funcD(TYPE *x, TYPE *u, TYPE *v, int xilen, int xjlen, int ujlen) {
	if (ujlen <= 0 || xilen <= 0 || xjlen <= 0)
		return;
	if (xilen <= B && xjlen <= B && ujlen <= B) {
#ifdef USE_PAPI
		int id = tid();
		int retval = 0;
		papi_for_thread(id);
		if ((retval = PAPI_start(EventSet[id])) != PAPI_OK) ERROR_RETURN(retval);
#endif
		__declspec(align(64)) TYPE V[ujlen * xjlen];

		int uin = 0;

#pragma parallel
		for (int i = 0; i < ujlen; i++) {
			int in = i * xjlen;
#pragma ivdep
			for (int j = 0; j < xjlen; j++) {
				V[j * ujlen + i] = v[in + j];
			}
		}

		TYPE *uu, *vv;
		int in = 0;
		uin = 0;
#pragma parallel
		for (int i = 0; i < xilen; i++) {
			for (int j = 0; j < xjlen; j++) {
				TYPE x_ij = x[in + j];

				uu = u + uin;
				vv = V + j * ujlen;
#pragma ivdep
				for (int k = 0; k < ujlen; k++) {
					x_ij = min(x_ij, (*uu + *vv));
					uu++;
					vv++;
				}
				x[in + j] = x_ij;
			}
			in = in + xjlen;
			uin = uin + ujlen;
		}
#ifdef USE_PAPI
		countMisses(id);
#endif
		return;

	} else {
		// Do I need vi too?
		int n = (xilen > xjlen) ? xilen : xjlen;
		n = max(n, ujlen);
		int c = 1;
		while (c < n)
			c = (c << 1);

		if ((c == xilen) && (xilen == xjlen) && (xjlen == ujlen)) {
			int nn = c >> 1;

			int nn2 = nn * nn;

			const int m11 = 0;
			int m12 = m11 + nn2;
			int m21 = m12 + nn2;
			int m22 = m21 + nn2;

			cilk_spawn func_D(x + m11, u + m11, v + m11, nn);
			cilk_spawn func_D(x + m12, u + m11, v + m12, nn);
			cilk_spawn func_D(x + m21, u + m21, v + m11, nn);
			func_D(x + m22, u + m21, v + m12, nn);

			cilk_sync;

			cilk_spawn func_D(x + m11, u + m12, v + m21, nn);
			cilk_spawn func_D(x + m12, u + m12, v + m22, nn);
			cilk_spawn func_D(x + m21, u + m22, v + m21, nn);
			func_D(x + m22, u + m22, v + m22, nn);

			cilk_sync;
		} else {
			c = c >> 1;

			int ni, nii, nj, njj;

			ni = min(c, xilen);
			nj = min(c, xjlen);
			nii = max(0, xilen - c);
			njj = max(0, xjlen - c);

			const int m11 = 0;
			int m12 = m11 + ni * nj;
			int m21 = m12 + ni * njj;
			int m22 = m21 + nii * nj;

			/////////////For u////////////////
			int unj, unjj;

			// uni  = min(c, xilen  );
			unj = min(c, ujlen);
			// unii = max(0, xilen-c);
			unjj = max(0, ujlen - c);

			int um12 = m11 + ni * unj;
			int um21 = um12 + ni * unjj;
			int um22 = um21 + nii * unj;

			//////////////For v/////////////////

			int vm12 = m11 + unj * nj;
			int vm21 = vm12 + unj * njj;
			int vm22 = vm21 + unjj * nj;

			cilk_spawn funcD(x + m11, u + m11, v + m11, ni, nj, unj);
			cilk_spawn funcD(x + m12, u + m11, v + vm12, ni, njj, unj);
			cilk_spawn funcD(x + m21, u + um21, v + m11, nii, nj, unj);
			funcD(x + m22, u + um21, v + vm12, nii, njj, unj);

			cilk_sync;

			cilk_spawn funcD(x + m11, u + um12, v + vm21, ni, nj, unjj);
			cilk_spawn funcD(x + m12, u + um12, v + vm22, ni, njj, unjj);
			cilk_spawn funcD(x + m21, u + um22, v + vm21, nii, nj, unjj);
			funcD(x + m22, u + um22, v + vm22, nii, njj, unjj);

			cilk_sync;
		}
	}
}

void funcC(TYPE *x, TYPE *u, TYPE *v, int xilen, int xjlen, int ujlen) {
	if (ujlen <= 0 || xilen <= 0 || xjlen <= 0)
		return;
	if (xilen <= B && xjlen <= B && ujlen <= B) {
#ifdef USE_PAPI
		int id = tid();
		int retval = 0;
		papi_for_thread(id);
		if ((retval = PAPI_start(EventSet[id])) != PAPI_OK) ERROR_RETURN(retval);
#endif
		register TYPE uv;
		TYPE *xx, *uu, *vv;
		xx = x;
		uu = u;
		vv = v;

		for (int k = 0; k < ujlen; k++) {
#pragma parallel
			for (int i = 0; i < xilen; i++) {
				xx = x + i * xjlen;
#pragma ivdep
				for (int j = 0; j < xjlen; j++) {
					uv = (*uu) + (*vv++);
					*xx = min(uv, *xx);
					xx++;
				}
				vv = vv - xjlen;
				uu = uu + ujlen;
			}
			xx = x;
			vv = vv + xjlen;
			uu = u + k + 1;
		}
#ifdef USE_PAPI
		countMisses(id);
#endif
		return;
	} else {
		int n = (xilen > xjlen) ? xilen : xjlen;
		n = max(n, ujlen);
		int c = 1;
		while (c < n)
			c = (c << 1);

		if ((c == n) && (xilen == xjlen) && (xjlen == ujlen)) {
			int nn = c >> 1;

			int nn2 = nn * nn;

			const int m11 = 0;
			int m12 = m11 + nn2;
			int m21 = m12 + nn2;
			int m22 = m21 + nn2;

			cilk_spawn func_C(x + m11, u + m11, v + m11, nn);
			func_C(x + m21, u + m21, v + m11, nn);
			cilk_sync;
			cilk_spawn func_D(x + m12, u + m11, v + m12, nn);
			func_D(x + m22, u + m21, v + m12, nn);

			cilk_sync;
			cilk_spawn func_C(x + m12, u + m12, v + m22, nn);
			func_C(x + m22, u + m22, v + m22, nn);
			cilk_sync;

			cilk_spawn func_D(x + m11, u + m12, v + m21, nn);
			func_D(x + m21, u + m22, v + m21, nn);

			cilk_sync;
		} else {
			c = c >> 1;
			int ni, nii, nj, njj;

			ni = min(c, xilen);
			nj = min(c, xjlen);
			nii = max(0, xilen - c);
			njj = max(0, xjlen - c);

			const int m11 = 0;
			int m12 = m11 + ni * nj;
			int m21 = m12 + ni * njj;
			int m22 = m21 + nii * nj;

			/////////////For u////////////////
			int unj, unjj;

			// uni  = min(c, xilen  );
			unj = min(c, ujlen);
			// unii = max(0, xilen-c);
			unjj = max(0, ujlen - c);

			int um12 = m11 + ni * unj;
			int um21 = um12 + ni * unjj;
			int um22 = um21 + nii * unj;

			//////////////For v/////////////////

			int vm12 = m11 + unj * nj;
			int vm21 = vm12 + unj * njj;
			int vm22 = vm21 + unjj * nj;

			// if(nj>0 && unj>0)
			{
				// if(ni>0)
				cilk_spawn funcC(x + m11, u + m11, v + m11, ni, nj, unj);
				// if(nii>0)
				funcC(x + m21, u + um21, v + m11, nii, nj, unj);
			}
			cilk_sync;

			// if(njj>0 && unj>0)
			{
				// if(ni>0)
				cilk_spawn funcD(x + m12, u + m11, v + vm12, ni, njj, unj);
				// if(nii>0)
				funcD(x + m22, u + um21, v + vm12, nii, njj, unj);
			}
			cilk_sync;

			// if(njj>0 && unjj>0)
			{
				//       if(ni>0)
				cilk_spawn funcC(x + m12, u + um12, v + vm22, ni, njj, unjj);
				// if(nii>0)
				funcC(x + m22, u + um22, v + vm22, nii, njj, unjj);
			}
			cilk_sync;

			// if(nj>0 && unjj>0)
			{
				// if(ni>0)
				cilk_spawn funcD(x + m11, u + um12, v + vm21, ni, nj, unjj);
				// if(nii>0)
				funcD(x + m21, u + um22, v + vm21, nii, nj, unjj);
			}
			cilk_sync;
		}
	}
}

void funcB(TYPE *x, TYPE *u, TYPE *v, int xilen, int xjlen, int ujlen) {
	if (ujlen <= 0 || xilen <= 0 || xjlen <= 0)
		return;
	if (xilen <= B && xjlen <= B && ujlen <= B) {
#ifdef USE_PAPI
		int id = tid();
		int retval = 0;
		papi_for_thread(id);
		if ((retval = PAPI_start(EventSet[id])) != PAPI_OK) ERROR_RETURN(retval);
#endif
		register TYPE uv;
		TYPE *xx, *uu, *vv;

		xx = x;
		uu = u;
		vv = v;

		for (int k = 0; k < ujlen; k++) {
			//    #pragma parallel
			for (int i = 0; i < xilen; i++) {
				xx = x + i * xjlen;
#pragma ivdep
				for (int j = 0; j < xjlen; j++) {
					uv = (*uu) + (*vv++);
					*xx = min(uv, *xx);
					xx++;
				}
				vv = vv - xjlen;
				uu = uu + ujlen;
			}
			xx = x;
			vv = vv + xjlen;
			uu = u + k + 1;
		}
#ifdef USE_PAPI
		countMisses(id);
#endif
		return;

	} else {
		int n = (xilen > xjlen) ? xilen : xjlen;
		n = max(n, ujlen);
		int c = 1;
		while (c < n)
			c = (c << 1);

		if ((c == xilen) && (xilen == xjlen) && (xjlen == ujlen)) {
			int nn = c >> 1;

			int nn2 = nn * nn;

			const int m11 = 0;
			int m12 = m11 + nn2;
			int m21 = m12 + nn2;
			int m22 = m21 + nn2;

			cilk_spawn func_B(x + m11, u + m11, v + m11, nn);
			func_B(x + m12, u + m11, v + m12, nn);
			cilk_sync;

			cilk_spawn func_D(x + m21, u + m21, v + m11, nn);
			func_D(x + m22, u + m21, v + m12, nn);
			cilk_sync;

			cilk_spawn func_B(x + m21, u + m22, v + m21, nn);
			func_B(x + m22, u + m22, v + m22, nn);

			cilk_sync;
			cilk_spawn func_D(x + m11, u + m12, v + m21, nn);
			func_D(x + m12, u + m12, v + m22, nn);
			cilk_sync;
		}

		else {
			c = c >> 1;

			int ni, nii, nj, njj;

			ni = min(c, xilen);
			nj = min(c, xjlen);
			nii = max(0, xilen - c);
			njj = max(0, xjlen - c);

			const int m11 = 0;
			int m12 = m11 + ni * nj;
			int m21 = m12 + ni * njj;
			int m22 = m21 + nii * nj;

			/////////////For u////////////////
			int unj, unjj;

			// uni  = min(c, xilen  );
			unj = min(c, ujlen);
			// unii = max(0, xilen-c);
			unjj = max(0, ujlen - c);

			int um12 = m11 + ni * unj;
			int um21 = um12 + ni * unjj;
			int um22 = um21 + nii * unj;

			//////////////For v/////////////////

			int vm12 = m11 + unj * nj;
			int vm21 = vm12 + unj * njj;
			int vm22 = vm21 + unjj * nj;

			cilk_spawn funcB(x + m11, u + m11, v + m11, ni, nj, unj);
			funcB(x + m12, u + m11, v + vm12, ni, njj, unj);
			cilk_sync;

			cilk_spawn funcD(x + m21, u + um21, v + m11, nii, nj, unj);
			funcD(x + m22, u + um21, v + vm12, nii, njj, unj);
			cilk_sync;

			cilk_spawn funcB(x + m21, u + um22, v + vm21, nii, nj, unjj);
			funcB(x + m22, u + um22, v + vm22, nii, njj, unjj);

			cilk_sync;
			cilk_spawn funcD(x + m11, u + um12, v + vm21, ni, nj, unjj);
			funcD(x + m12, u + um12, v + vm22, ni, njj, unjj);
			cilk_sync;
		}
	}
}

void funcA(TYPE *x, TYPE *u, TYPE *v, int xilen, int xjlen, int ujlen) {
	if (ujlen <= 0 || xilen <= 0 || xjlen <= 0)
		return;
	if (xilen <= B && xjlen <= B && ujlen <= B) {
#ifdef USE_PAPI
		int id = tid();
		int retval = 0;
		papi_for_thread(id);
		if ((retval = PAPI_start(EventSet[id])) != PAPI_OK) ERROR_RETURN(retval);
#endif
		register TYPE uv;
		TYPE *xx, *uu, *vv;

		xx = x;
		uu = u;
		vv = v;

		for (int k = 0; k < ujlen; k++) {
			//#pragma parallel
			for (int i = 0; i < xilen; i++) {
				xx = x + i * xjlen;
				// #pragma ivdep
				for (int j = 0; j < xjlen; j++) {
					uv = (*uu) + (*vv++);
					*xx = min(uv, *xx);
					xx++;
				}
				vv = vv - xjlen;
				uu = uu + ujlen;
			}
			xx = x;
			vv = vv + xjlen;
			uu = u + k + 1;
		}
#ifdef USE_PAPI
		countMisses(id);
#endif
		return;
	} else {
		int n = (xilen > xjlen) ? xilen : xjlen;
		n = max(n, ujlen);
		int c = 1;
		while (c < n)
			c = (c << 1);

		if ((c == xilen) && (xilen == xjlen) && (xjlen == ujlen)) {
			int nn = c >> 1;

			int nn2 = nn * nn;
			const int m11 = 0;
			int m12 = m11 + nn2;
			int m21 = m12 + nn2;
			int m22 = m21 + nn2;

			func_A(x + m11, u + m11, v + m11, nn);

			cilk_spawn func_B(x + m12, u + m11, v + m12, nn);
			cilk_spawn func_C(x + m21, u + m21, v + m11, nn);
			cilk_sync;

			func_D(x + m22, u + m21, v + m12, nn);

			func_A(x + m22, u + m22, v + m22, nn);
			cilk_spawn func_B(x + m21, u + m22, v + m21, nn);
			cilk_spawn func_C(x + m12, u + m12, v + m22, nn);
			cilk_sync;
			func_D(x + m11, u + m12, v + m21, nn);
		} else {
			c = c >> 1;

			int ni, nii, nj, njj;

			ni = min(c, xilen);
			nj = min(c, xjlen);
			nii = max(0, xilen - c);
			njj = max(0, xjlen - c);

			const int m11 = 0;
			int m12 = m11 + ni * nj;
			int m21 = m12 + ni * njj;
			int m22 = m21 + nii * nj;

			/////////////For u////////////////
			int unj, unjj;

			// uni  = min(c, xilen  );
			unj = min(c, ujlen);
			// unii = max(0, xilen-c);
			unjj = max(0, ujlen - c);

			int um12 = m11 + ni * unj;
			int um21 = um12 + ni * unjj;
			int um22 = um21 + nii * unj;

			//////////////For v/////////////////

			int vm12 = m11 + unj * nj;
			int vm21 = vm12 + unj * njj;
			int vm22 = vm21 + unjj * nj;

			funcA(x + m11, u + m11, v + m11, ni, nj, unj);

			cilk_spawn funcB(x + m12, u + m11, v + vm12, ni, njj, unj);
			funcC(x + m21, u + um21, v + m11, nii, nj, unj);
			cilk_sync;

			/*

			 for(int i = 0; i< xilen;i++)
			 {
			 for(int j = 0; j< xjlen; j++)
			 {
			 cout<<*(x+i*xjlen+j)<<" ";
			 }
			 cout<<endl;
			 }
			 */
			funcD(x + m22, u + um21, v + vm12, nii, njj, unj);
			funcA(x + m22, u + um22, v + vm22, nii, njj, unjj);
			cilk_spawn funcB(x + m21, u + um22, v + vm21, nii, nj, unjj);
			funcC(x + m12, u + um12, v + vm22, ni, njj, unjj);
			cilk_sync;
			funcD(x + m11, u + um12, v + vm21, ni, nj, unjj);
		}
	}
}

#ifdef LOOPDP

void FloydWarshall(int n) {
	for (int k = 0; k < n; k++) {
		int ink = k * NP;
// #pragma cilk grainsize = 256
		cilk_for(int i = 0; i < n; i++) {
#ifdef USE_PAPI
			int id = tid();
			int retval = 0;
			papi_for_thread(id);
			if ((retval = PAPI_start(EventSet[id])) != PAPI_OK) ERROR_RETURN(retval);
#endif
			int in = i * NP;
			int *d = D + in;
			int v = D[in + k];
			int *dk = D + ink;

#pragma ivdep
			for (int j = 0; j < n; j++) {
				{
					*d = min(*d, v + *dk);
					dk++;
					d++;
				}
			}
#ifdef USE_PAPI
			countMisses(id);
#endif
		}
	}
}

void Do(int start, int end, int k, int n) {
#ifdef USE_PAPI
	int id = tid();
	int retval = 0;
	papi_for_thread(id);
	if ((retval = PAPI_start(EventSet[id])) != PAPI_OK) ERROR_RETURN(retval);
#endif
	int ink = k * NP;
	for (int i = start; i <= end; i++) {
		int in = i * NP;
		int *d = D + in;
		int v = D[in + k];
		int *dk = D + ink;

#pragma ivdep
		for (int j = 0; j < n; j++) {
			{
				*d = min(*d, v + *dk);
				dk++;
				d++;
			}
		}
	}
#ifdef USE_PAPI
	countMisses(id);
#endif
}
void FloydWarshall2(int n) {
	int chunk, startQ, endQ, rem, other;
	chunk = n / 32;
	rem = n % 32;
	other = 32 - rem;
	for (int k = 0; k < n; k++) {
		for (int i = 0; i < 32; i++) {
			if (i < other) {
				startQ = i * chunk;  // start node id
				endQ = startQ + chunk - 1;

			} else {
				int v = i - other;
				startQ = (i)*chunk + (v);
				endQ = startQ + chunk;
			}

			cilk_spawn Do(startQ, endQ, k, n);
		}

		cilk_sync;
	}
}
#endif

int main(int argc, char *argv[]) {
	N = 1;
	if (argc > 1)
		N = atoi(argv[1]);
	if (argc > 2)
		B = atoi(argv[2]);
	if (argc > 3) {
        	if (0!= __cilkrts_set_param("nworkers",argv[3])) {
            		cout<<"Failed to set worker count\n"<<endl;
            		return 1;
        	}
    	}
	cout<<"the actual worker count is "<<__cilkrts_get_nworkers()<<endl;
	if (B > N)
		B = N;
#ifdef USE_PAPI
	papi_init();
#endif

	NP = N;
	int NN = 2;

	while (NN < N)
		NN = NN << 1;

	if (NN == N) {
		NP = N + 1;
	}
#ifdef CO
	dist = (TYPE *)_mm_malloc(N * N * sizeof(TYPE), ALIGNMENT);

	X = (TYPE *)_mm_malloc(N * N * sizeof(TYPE), ALIGNMENT);

#endif

#ifdef LOOPDP
	D = (TYPE *)_mm_malloc(NP * NP * sizeof(TYPE), ALIGNMENT);
#endif

	cilk_for(int i = 0; i < N;
			i++
			) {
				cilk_for(int j = 0; j < N; j++) {
					if (i == j) {
#ifdef CO
						dist[i * N + j] = 0;
#endif
#ifdef LOOPDP
						D[i * NP + j] = 0;
#endif
					} else {
#ifdef CO
						dist[i * N + j] = abs((j - i) % 4) + 1;
#endif

#ifdef LOOPDP
						D[i * NP + j] = abs((j - i) % 4) + 1;
#endif
					}
				}
			}
#ifdef CO
			conv_RM_2_ZM_RM(X, 0, 0, (N), (N));
			unsigned long long tstart1 = cilk_getticks();

			funcA(X, X, X, N, N, N);

			unsigned long long tend1 = cilk_getticks();

			conv_ZM_2_RM_RM(X, dist, 0, 0, (N), (N));

			cout << "CO," << N << "," << cilk_ticks_to_seconds(tend1 - tstart1) << ",";
#ifdef pdebug
			cout << "recursive version\n";
			for (int i = 0; i < N; i++) {
				for (int j = 0; j < N; j++) {
					cout << dist[i * N + j] << " ";
				}
				cout << "\n";
			}
#endif

			_mm_free(X);
#endif

#ifdef LOOPDP
			unsigned long long tstart = cilk_getticks();
			FloydWarshall(N);
			//FloydWarshall2(N);
			unsigned long long tend = cilk_getticks();
			cout << N << "," << cilk_ticks_to_seconds(tend - tstart) << ",";

#ifdef pdebug
			cout << "loop version\n";
			for (int i = 0; i < N; i++) {
				for (int j = 0; j < N; j++) {
					cout << D[i * NP + j] << " ";
				}
				cout << "\n";
			}
#endif
#ifdef CO
			for (int i = 0; i < N; i++) {
				for (int j = 0; j < N; j++)  //
				{
					if (D[i * NP + j] != dist[i * N + j]) {
						cout << "Wrong at" << i << j << endl;
						break;
					}
				}
			}
#endif
			_mm_free(D);

#endif

			_mm_free(dist);

#ifdef USE_PAPI
			countTotalMiss(p);
			cout << endl;
			PAPI_shutdown();
			delete threadcounter;
			for (int i = 0; i < p; i++) delete l2miss[i];
			delete l2miss;
			delete errstring;
			delete EventSet;
			delete eventCode;

#endif
			return 0;
		}
