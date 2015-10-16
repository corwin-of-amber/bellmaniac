//@Copyright: Jesmin Jahan Tithi, Rezaul Chowdhury, Department of Computer Science, Stony Brook University, Ny-11790.

#include <iostream>
#include <string>
#include <time.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/timeb.h>
#include <cstring>
#include <pthread.h>
#include <cilk/cilk.h>
#include <cilk/cilk_api.h>
#include <math.h>
#include <immintrin.h>
#include "cilktime.h"

#ifdef USE_PAPI
#include "papilib.h"
#endif

using namespace std;

int N, B;
int *SOF, *S_dp, *S;
int *Z;
int *F;
string proteinSeq;

#define min(a, b) (a<b?a:b)
#define max(a, b) (a>b?a:b)

void conv_RM_2_ZM_RM(int *x, int ix, int jx, int ilen, int jlen) {
	if (ilen <= 0 || jlen <= 0)
		return;
	if (ilen <= B && jlen <= B) {
		for (int i = ix; i < ix + ilen; i++) {
#pragma ivdep
			for (int j = jx; j < jx + jlen; j++) {
				(*x++) = SOF[(i) * (N) + j];
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

		int *x12, *x21, *x22;
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
void conv_ZM_2_RM_RM(int *x, int* V, int ix, int jx, int ilen, int jlen) {
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
		//n22 = nii * njj;

		int *x12, *x21, *x22;
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
//shifted everything by 1 to consider start in index 1
void SCORE_ONE_FOLD(int n) {
	for (int j = 1; j < n - 1; j++) {
		for (int k = j + 2; k < n; k++) {
			if (k > 2 * j) {
				SOF[j * N + k] = SOF[j * N + 2 * j];
			} else {
				SOF[j * N + k] = SOF[j * N + (k - 1)];
				if ((2 * j - k - 1 >= 0)
						&& (proteinSeq[2 * j - k - 1] == proteinSeq[k])
						&& (proteinSeq[k] == '1')) { // should 2*j-k-1 > 0 or >=0??
					++SOF[j * N + k];
				}

			}

		}
	}
}
#ifdef LOOPDP
int LOOP_PROTEIN_FOLDING (int n)
{
	int in = (n-2)*N;
	for(int i = n-2; i>=0;i--)
	{	int ii = 1-i;
#pragma cilk grainsize = 256
		cilk_for(int j = n-3; j>i; j--)
		{

#ifdef USE_PAPI
			int id = tid();
			int retval = 0;
			papi_for_thread(id);
			if ( (retval=PAPI_start(EventSet[id])) != PAPI_OK)
			ERROR_RETURN(retval);
#endif
			int val = S_dp[in+j];
			//I have observed that these 2 optimizations does not matter really!
			int j2 = (j<<1)+ii;
			int inj = (j+1)*N;
			int *sdp = S_dp + inj;
			int *sof = SOF+ inj;
#pragma ivdep
			for(int k = n-1; k>=j+2; k--)
			{
				val = max(val, *(sdp+k) + *(sof+min(k, j2)));

			}
			S_dp[in+j]= val;
#ifdef USE_PAPI
			countMisses(id );
#endif

		}
		in = in - N;
	}

	//find the maximum value
	int final = 0;
#pragma ivdep
	for(int j = 0; j<n-1; j++)
	{
		final = max(final, S_dp[j]);

	}
	return final;

}
#endif
//Question: can the 2j-i+1 be outside block?
void D_PF(int *x, int*v, int *DN, int *sof, int *sofdn, int xi, int xj, int vj,
		int xilen, int xjlen, int vilen, int vjlen, int vdnilen) {
	if (xi > N || xj > N || vj > N)
		return;
	if (xilen <= B && xjlen <= B && vjlen <= B) //D_loop
			{
#ifdef USE_PAPI
		int id = tid();
		int retval = 0;
		papi_for_thread(id);
		if ( (retval=PAPI_start(EventSet[id])) != PAPI_OK)
		ERROR_RETURN(retval);
#endif
		int endi = (xi + xilen >= N) ? (N - xi - 1) : xilen;
		int endj = (xj + xjlen >= N) ? (N - xj - 2) : xjlen;
		int endk = (vj + vjlen >= N) ? (N - vj) : vjlen;
		int *vv;
		register int ini = 0;
		for (int i = 0; i < endi; i++) {
			int ii = xi + i;
			int inj = vjlen;
#pragma parallel
			for (int j = 0; j < endj - 1; j++) {

				int jj = xj + j;
				int inii = ini + j;

				register int j2 = jj + jj - ii + 1 - vj;

				int start = max(vj, jj+2) - vj;

				int val = x[inii];
				vv = v + inj + start;
				if (j2 < start) {
					int c = 0;
#pragma ivdep
					for (int k = start; k < endk; k++) {
#ifdef pDEBUG
						cout<<"("<<ii<<","<<jj<<") ("<<jj+1<<","<<k+vj<<") ("<<jj+1<<","<<j2+vj<<")"<<endl;
#endif
						c = max(c, *vv); //I need to change for any N
						vv++;
					}
					val = max(val, c + SOF[(jj + 1) * N + j2 + vj]);

				} else {
					//possibly this can be optimized
#pragma ivdep
					for (int k = start; k < endk; k++) {
#ifdef pDEBUG
						cout<<"("<<ii<<","<<jj<<") ("<<jj+1<<","<<k+vj<<") ("<<jj+1<<","<<vj+min(k, j2)<<")"<<endl;
#endif
						val = max(val, *vv + sof[inj+min(k, j2)]);
						vv++;
					}
				}
				x[inii] = val;
				inj = inj + vjlen;

			}
			if (endj == xjlen) {
				int j = endj - 1;
				int jj = xj + j;

				int inii = ini + j;

				register int j2 = jj + jj - ii + 1 - vj;

				int val = x[inii];
				int start = max(vj, jj+2) - vj;
				vv = DN + start;
				if (j2 < start) {

					int c = 0;
#pragma ivdep
					for (int k = start; k < endk; k++) {
#ifdef pDEBUG
						cout<<"("<<ii<<","<<jj<<") ("<<jj+1<<","<<k+vj<<") ("<<jj+1<<","<<j2+vj<<")"<<endl;
#endif
						c = max(c, *vv); //I need to change for any N
						vv++;
					}
					val = max(val, c + SOF[(jj + 1) * N + j2 + vj]);

				} else {
					vv = DN + start;
#pragma ivdep
					for (int k = start; k < endk; k++) {
#ifdef pDEBUG
						cout<<"("<<ii<<","<<jj<<") ("<<jj+1<<","<<k+vj<<") ("<<jj+1<<","<<vj+min(k, j2)<<")"<<endl;
#endif
						val = max(val, *vv + sofdn[min(k, j2)]);
						vv++;
					}
				}
				x[inii] = val;

			} else {
				int j = endj - 1;
				int jj = xj + j;

				int inii = ini + j;
				int inj = (endj) * vjlen;

				int val = x[inii];
				register int j2 = jj + jj - ii + 1 - vj;

				int start = max(vj, jj+2) - vj;
				if (j2 < start) {
					int c = 0;
					int *vv = v + inj + start;
#pragma ivdep
					for (int k = start; k < endk; k++) {
#ifdef pDEBUG
						cout<<"("<<ii<<","<<jj<<") ("<<jj+1<<","<<k+vj<<") ("<<jj+1<<","<<j2+vj<<")"<<endl;
#endif
						c = max(c, *vv); //I need to change for any N
						vv++;
					}
					val = max(val, c + SOF[(jj + 1) * N + j2 + vj]);

				} else {
					int *vv = v + inj + start;
#pragma ivdep
					for (int k = start; k < endk; k++) {
#ifdef pDEBUG
						cout<<"("<<ii<<","<<jj<<") ("<<jj+1<<","<<k+vj<<") ("<<jj+1<<","<<vj+min(k, j2)<<")"<<endl;
#endif
						val = max(val, *vv + sof[inj+min(k, j2)]);
						vv++;
					}
				}
				x[inii] = val;

			}
			ini = ini + xjlen;
		}

#ifdef USE_PAPI
		countMisses(id );
#endif
		return;
	} else {

		int n = (xilen > xjlen) ? xilen : xjlen;
		n = max(n, vjlen);
		// I do not need this??
		n = max(n, vilen);
		n = max(n, vdnilen);
		//
		int c = 1;
		while (c < n)
			c = (c << 1);

		c = c >> 1;
		int ni, nii, nj, njj;

		ni = min(c, xilen);
		nj = min(c, xjlen);
		nii = max(0, xilen - c);
		njj = max(0, xjlen - c);

		int vni = min(c, vilen);
		int vnj = min(c, vjlen);
		int vnii = max(0, vilen - c);
		int vnjj = max(0, vjlen - c);

		int vdni = min(c, vdnilen);

		const int m11 = 0;
		int m12 = m11 + ni * nj;
		int m21 = m12 + ni * njj;
		int m22 = m21 + nii * nj;

		int vm12 = vni * vnj;
		int vm21 = vm12 + vni * vnjj;
		int vm22 = vm21 + vnii * vnj;
		int vdnm22 = vdni * vnj;

		register int vj22 = vj + vnj;
		register int xi22 = xi + ni;
		register int xj22 = xj + nj;

		//void D_PF(int *x, int*v, int *DN, int *sof, int *sofdn, int xi, int xj, int vj, int xilen, int xjlen, int vilen, int vjlen, int vdnilen)

		cilk_spawn D_PF(x, v, v + vm21, sof, sof + vm21, xi, xj, vj, ni, nj,
				vni, vnj, vnii);
		cilk_spawn D_PF(x + m12, v + vm21, DN, sof + vm21, sofdn, xi, xj22, vj,
				ni, njj, vnii, vnj, vdni);
		cilk_spawn D_PF(x + m21, v, v + vm21, sof, sof + vm21, xi22, xj, vj,
				nii, nj, vni, vnj, vnii);
		D_PF(x + m22, v + vm21, DN, sof + vm21, sofdn, xi22, xj22, vj, nii, njj,
				vnii, vnj, vdni);
		cilk_sync;

		cilk_spawn D_PF(x, v + vm12, v + vm22, sof + vm12, sof + vm22, xi, xj,
				vj22, ni, nj, vni, vnjj, vnii);
		cilk_spawn D_PF(x + m12, v + vm22, DN + vdnm22, sof + vm22,
				sofdn + vdnm22, xi, xj22, vj22, ni, njj, vnii, vnjj, vdni);
		cilk_spawn D_PF(x + m21, v + vm12, v + vm22, sof + vm12, sof + vm22,
				xi22, xj, vj22, nii, nj, vni, vnjj, vnii);
		D_PF(x + m22, v + vm22, DN + vdnm22, sof + vm22, sofdn + vdnm22, xi22,
				xj22, vj22, nii, njj, vnii, vnjj, vdni);
		cilk_sync;

	}

}
//void D_PF(int *x, int*v, int *DN, int *sof, int *sofdn, int xi, int xj, int vj, int xilen, int xjlen, int vilen, int vjlen, int vdnilen)
void C_PF(int *x, int *u, int *DN, int *sof, int *sofdn, int xi, int xj, int uj,
		int xilen, int xjlen, int ujlen, int udnilen) {
	if (xi > N || xj > N || uj > N)
		return;
	if (xilen <= B && xjlen <= B && ujlen <= B) //C_loop
			{
#ifdef USE_PAPI
		int id = tid();
		int retval = 0;
		papi_for_thread(id);
		if ( (retval=PAPI_start(EventSet[id])) != PAPI_OK)
		ERROR_RETURN(retval);
#endif
		int endi = (xi + xilen >= N) ? (N - xi - 1) : xilen;
		int endj = (xj + xjlen >= N) ? (N - xj - 2) : xjlen;
		int endk = (uj + ujlen >= N) ? (N - uj) : ujlen;
		int inii = (endi - 1) * xjlen;
		for (int i = endi - 1; i >= 0; i--) {
			int ii = xi + i;
			//int inii = i*B;
			//	int inj = (endj-1)*ujlen;
			for (int j = endj - 2; j > i; j--) {

				int jj = xj + j;
				int inj = (j + 1) * ujlen;
				int ini = inii + j;

				register int j2 = jj + jj - ii + 1 - uj;

				int val = x[ini];

				int start = max(uj, jj+2) - uj;
				if (j2 < start) {
					int c = 0;
					int *uu = u + start + inj;
					for (int k = start; k < endk; k++) {
#ifdef pDEBUG
						cout<<"("<<ii<<","<<jj<<") ("<<jj+1<<","<<k+uj<<") ("<<jj+1<<","<<(j2+uj)<<")"<<endl;
#endif
						c = max(c, *uu);
						uu++;
					}

					val = max(val, SOF[(jj + 1) * N + (j2 + uj)] + c);

				} else {
					for (int k = start; k < endk; k++) {
#ifdef pDEBUG
						cout<<"("<<ii<<","<<jj<<") ("<<jj+1<<","<<k+uj<<") ("<<jj+1<<","<<uj+min(k, j2)<<")"<<endl;
#endif
						val = max(val, u[inj+k] + sof[inj+min(k, j2)]);
					}
				}
				x[ini] = val;
				//inj = inj - B;
			}
			int j = endj - 1;
			if (endj == xjlen && j > i) {

				int jj = xj + j;

				int inj = (endj) * ujlen;
				int ini = inii + j;

				register int j2 = jj + jj - ii + 1 - uj;

				int val = x[ini];

				int start = max(uj, jj+2) - uj;
				if (j2 < start) {
					int c = 0;
					int *uu = DN + start;
#pragma ivdep
					for (int k = start; k < endk; k++) {
#ifdef pDEBUG
						cout<<"("<<ii<<","<<jj<<") ("<<jj+1<<","<<k+uj<<") ("<<jj+1<<","<<(j2+uj)<<")"<<endl;
#endif
						c = max(c, *uu);
						uu++;
					}

					val = max(val, SOF[(jj + 1) * N + (j2 + uj)] + c);

				} else {
					int *uu = DN + start;
#pragma ivdep
					for (int k = start; k < endk; k++) {

#ifdef pDEBUG
						cout<<"("<<ii<<","<<jj<<") ("<<jj+1<<","<<k+uj<<") ("<<jj+1<<","<<uj+min(k, j2)<<")"<<endl;
#endif
						val = max(val, *uu + sofdn[min(k, j2)]);
						uu++;
					}
				}
				x[ini] = val;
			} else if (j > i) {
				int jj = xj + j;
				int inj = (j + 1) * ujlen;
				int ini = inii + j;

				register int j2 = jj + jj - ii + 1 - uj;

				int val = x[ini];

				int start = max(uj, jj+2) - uj;
				if (j2 < start) {
					int c = 0;
					int *uu = u + inj + start;
#pragma ivdep
					for (int k = start; k < endk; k++) {
#ifdef pDEBUG
						cout<<"("<<ii<<","<<jj<<") ("<<jj+1<<","<<k+uj<<") ("<<jj+1<<","<<(j2+uj)<<")"<<endl;
#endif
						c = max(c, *uu);
						uu++;
					}

					val = max(val, SOF[(jj + 1) * N + (j2 + uj)] + c);

				} else {
					int *uu = u + inj + start;
#pragma ivdep		
					for (int k = start; k < endk; k++) {
#ifdef pDEBUG
						cout<<"("<<ii<<","<<jj<<") ("<<jj+1<<","<<k+uj<<") ("<<jj+1<<","<<min(k+uj, uj+j2)<<")"<<endl;
#endif
						val = max(val, *uu + sof[inj+min(k, j2)]);
						uu++;
					}
				}
				x[ini] = val;

			}
			inii = inii - xjlen;
		}
#ifdef USE_PAPI
		countMisses(id );
#endif
		return;
	} else {

		int n = (xilen > xjlen) ? xilen : xjlen;
		n = max(n, ujlen);
		//
		n = max(n, udnilen);
		int c = 1;
		while (c < n)
			c = (c << 1);

		c = c >> 1;
		int ni, nii, nj, njj;

		ni = min(c, xilen);
		nj = min(c, xjlen);
		nii = max(0, xilen - c);
		njj = max(0, xjlen - c);

		//int vni = min(c, vilen  );
		int unj = min(c, ujlen);
		//int vnii = max(0, vilen-c);
		int unjj = max(0, ujlen - c);

		int udni = min(c, udnilen);
		const int m11 = 0;
		int m12 = m11 + ni * nj;
		int m21 = m12 + ni * njj;
		int m22 = m21 + nii * nj;

		int um12 = ni * unj;
		int um21 = um12 + ni * unjj;
		int um22 = um21 + nii * unj;

		int udnm22 = udni * unj;
		register int uj22 = uj + unj;
		register int xi22 = xi + ni;
		register int xj22 = xj + nj;

		//void D_PF(int *x, int*v, int *DN, int *sof, int *sofdn, int xi, int xj, int vj, int xilen, int xjlen, int vilen, int vjlen, int vdnilen)
		//void C_PF(int *x, int *u, int *DN, int *sof, int *sofdn, int n, int xi, int xj, int uj, int xilen, int xjlen, int ujlen, int udnilen)
		cilk_spawn C_PF(x, u, u + um21, sof, sof + um21, xi, xj, uj, ni, nj,
				unj, nii);
		cilk_spawn D_PF(x + m12, u + um21, DN, sof + um21, sofdn, xi, xj22, uj,
				ni, njj, nii, unj, udni);
		C_PF(x + m22, u + um21, DN, sof + um21, sofdn, xi + ni, xj22, uj, nii,
				njj, unj, udni);
		cilk_sync;
		//void C_PF(int *x, int *u, int *DN, int *sof, int *sofdn, int n, int xi, int xj, int uj, int xilen, int xjlen, int ujlen, int udnilen)
		cilk_spawn C_PF(x, u + um12, u + um22, sof + um12, sof + um22, xi, xj,
				uj22, ni, nj, unjj, nii);
		cilk_spawn D_PF(x + m12, u + um22, DN + udnm22, sof + um22,
				sofdn + udnm22, xi, xj22, uj22, ni, njj, nii, unjj, udni);
		C_PF(x + m22, u + um22, DN + udnm22, sof + um22, sofdn + udnm22,
				xi + ni, xj22, uj22, nii, njj, unjj, udni);
		cilk_sync;

	}

}
//a square depending on a triangle
//May be for function B, we do not need the down pointer
void B_PF(int *x, int *v, int *sof, int xi, int xj, int vj, int xilen,
		int xjlen, int vilen) {
	if (xi > N || xj > N || vj > N)
		return;
	if (xilen <= B && xjlen <= B && vilen <= B)        //B_loop
			{
#ifdef USE_PAPI
		int id = tid();
		int retval = 0;
		papi_for_thread(id);
		if ( (retval=PAPI_start(EventSet[id])) != PAPI_OK)
		ERROR_RETURN(retval);
#endif
		int endi = (xi + xilen >= N) ? (N - xi - 1) : xilen;
		int endj = (xj + xjlen >= N) ? (N - xj - 2) : xjlen;
		int endk = (vj + xjlen >= N) ? (N - vj) : xjlen;

#pragma parallel
		for (int i = 0; i < endi; i++) {
			int ini = i * xjlen;
			int ii = xi + i;
#pragma parallel
			for (int j = 0; j < endj; j++) {
				int j1 = j + 1;
				int jj = xj + j;

				int inj = (j + 1) * xjlen;
				int inii = ini + j;
				register int j2 = jj + jj - ii + 1 - vj;

				int val = x[inii];

				int start = max(vj, jj+2) - vj;
				int *vv = v + inj + start;
#pragma ivdep
				for (int k = start; k < endk; k++) {
#ifdef pDEBUG
					cout<<"("<<ii<<","<<jj<<") ("<<jj+1<<","<<k+vj<<") ("<<jj+1<<","<<min(k+vj, vj+j2)<<")"<<endl;
#endif
					val = max(val, *vv+ sof[inj+min(k, j2)]);
					vv++;
				}
				x[inii] = val;
			}
		}
#ifdef USE_PAPI
		countMisses(id );
#endif
		return;
	} else {

		int n = (xilen > xjlen) ? xilen : xjlen;
		n = max(n, vilen);
		int c = 1;
		while (c < n)
			c = (c << 1);

		c = c >> 1;
		int ni, nii, nj, njj;

		ni = min(c, xilen);
		nj = min(c, xjlen);
		nii = max(0, xilen - c);
		njj = max(0, xjlen - c);

		int vni = min(c, vilen);
		//int vni  = min(c, ujlen  );
		int vnii = max(0, vilen - c);
		//int unjj = max(0, ujlen-c);

		const int m11 = 0;
		int m12 = m11 + ni * nj;
		int m21 = m12 + ni * njj;
		int m22 = m21 + nii * nj;

		int vm12 = vni * nj;
		int vm21 = vm12 + vni * njj;
		int vm22 = vm21 + vnii * nj;

		int vj22 = vj + nj;

		//These need to be changed for any N
		//void B_PF(int *x, int *v, int *sof, int n, int xi, int xj, int vj, int xilen, int xjlen, int vilen)
		cilk_spawn B_PF(x, v, sof, xi, xj, vj, ni, nj, vni);

		cilk_spawn B_PF(x + m12, v + vm22, sof + vm22, xi, xj + nj, vj22, ni,
				njj, vnii);
		cilk_spawn B_PF(x + m21, v, sof, xi + ni, xj, vj, nii, nj, vni);
		B_PF(x + m22, v + vm22, sof + vm22, xi + ni, xj + nj, vj22, nii, njj,
				vnii);
		cilk_sync;

		//void D_PF(int *x, int*v, int *DN, int *sof, int *sofdn, int xi, int xj, int vj, int xilen, int xjlen, int vilen, int vjlen, int vdnilen)
		cilk_spawn D_PF(x, v + vm12, v + vm22, sof + vm12, sof + vm22, xi, xj,
				vj22, ni, nj, vni, njj, vnii);
		D_PF(x + m21, v + vm12, v + vm22, sof + vm12, sof + vm22, xi + ni, xj,
				vj22, nii, nj, vni, njj, vnii);
		cilk_sync;

	}

}

void A_PF(int *x, int *DN, int *sof, int *sofdn, int xi, int xj, int xilen,
		int xjlen, int xdnilen) {
	if (xi > N || xj > N)
		return;
	if (xilen <= B && xjlen <= B && xdnilen <= B) //A_loop
			{
#ifdef USE_PAPI
		int id = tid();
		int retval = 0;
		papi_for_thread(id);
		if ( (retval=PAPI_start(EventSet[id])) != PAPI_OK)
		ERROR_RETURN(retval);
#endif
		//next question: should I always start from 1? even for the inner triangles?
		int endi = (xi + xilen >= N) ? (N - xi - 1) : xilen;
		int endj = (xj + xjlen >= N) ? (N - xj - 2) : xjlen;
		int endk = (xj + xjlen >= N) ? (N - xj) : xjlen;

		for (int i = endi - 1; i >= 0; i--) {

			int ini = i * xjlen;

			//first do it for all columns except the last one
			for (int j = endj - 2; j > i; j--) {

				int inj = (j + 1) * xjlen;
				int inii = ini + j;

				register int j2 = j + j - i + 1;

				int val = x[inii];

				for (int k = j + 2; k < endk; k++) {
#ifdef pDEBUG
					cout<<"("<<xi+i<<","<<xj+j<<") ("<<xj+j+1<<","<<k+xj<<") ("<<xj+j+1<<","<<xj+min(k, j2)<<")"<<endl;
#endif
					val = max(val, x[inj+k]+sof[inj+min(k, j2)]);
				}
				x[inii] = val;

			}
			//now if it is not the N-2th column, the use the down pointer
			//else use the current one!
			int j = endj - 1;
			if (endj == xjlen && j > i) {

				int inj = (j + 1) * xjlen;
				int inii = ini + j;

				register int j2 = j + j - i + 1;

				int val = x[inii];

				for (int k = j + 2; k < endk; k++) {
					val = max(val, DN[k] + sofdn[min(k, j2)]);
				}
				x[inii] = val;

			} else if (j > i) {

				int inj = (j + 1) * xjlen;
				int inii = ini + j;

				register int j2 = j + j - i + 1;

				int val = x[inii];

				for (int k = j + 2; k < endk; k++) {
#ifdef pDEBUG
					cout<<"("<<i+xi<<","<<j+xj<<") ("<<xj+j+1<<","<<k+xj<<") ("<<xj+j+1<<","<<min(k+xj, xj+j2)<<endl;
#endif
					val = max(val, x[inj+k]+sof[inj+min(k, j2)]);
				}
				x[inii] = val;

			}

		}
#ifdef USE_PAPI
		countMisses(id );
#endif
		return;
	}

	else {
		int n = (xilen > xjlen) ? xilen : xjlen;
		//
		n = max(n, xdnilen);
		int c = 1;
		while (c < n)
			c = (c << 1);

		c = c >> 1;
		int ni, nii, nj, njj;

		ni = min(c, xilen);
		nj = min(c, xjlen);
		nii = max(0, xilen - c);
		njj = max(0, xjlen - c);

		int dni = min(c, xdnilen);
		const int m11 = 0;
		int m12 = m11 + ni * nj;
		int m21 = m12 + ni * njj;
		int m22 = m21 + nii * nj;
		int xj22 = xj + nj;
		A_PF(x + m22, DN + dni * nj, sof + m22, sofdn + dni * nj, xi + ni, xj22,
				nii, njj, dni);

		B_PF(x + m12, x + m22, sof + m22, xi, xj22, xj22, ni, njj, nii);

		C_PF(x, x + m12, x + m22, sof + m12, sof + m22, xi, xj, xj22, ni, nj,
				njj, nii);

		// for(int i = 0; i<nn2;i++)
		//	cout<<x[i]<<" ";
		A_PF(x, x + m21, sof, sof + m21, xi, xj, ni, nj, nii);
	}
}
int CO_PROTEIN_FOLDING(int n) {

	//array, size, starting point x, starting point y
	A_PF(S, S, F, F, 0, 0, n, n, n);

	conv_ZM_2_RM_RM(S, Z, 0, 0, N, N);
	int final = 0;
#pragma ivdep
	for (int j = 0; j < n - 1; j++) {
		final = max(final, Z[j]);

	}
	return final;

}
/*
 void makeProteinSeq(int n)
 {
 //generating random sequence. here 1 means hydrophobic and 0 means hydrophilic
 for(int i = 0; i <=n; ++i){
 int val = (rand() % 10);
 if(val < 5) proteinSeq = proteinSeq + '1';
 else proteinSeq = proteinSeq + '0';
 }

 }*/
void makeProteinSeq(int n) {
	//generating random sequence. here 1 means hydrophobic and 0 means hydrophilic
	for (int i = 0; i < n; ++i) {
		/*int val = (rand() % 10);
		 if(val < 5) proteinSeq = proteinSeq + '1';
		 else proteinSeq = proteinSeq + '0';*/
		proteinSeq = proteinSeq + '1';
	}
	/*
	 for(int i=1;i<=N; i++)
	 {
	 cout<<proteinSeq[i]<<" ";
	 }
	 cout<<endl;
	 */
}
int main(int argc, char ** argv) {
	N = 16;
	B = N / 2;
	if (argc > 1)
		N = atoi(argv[1]);
	if (argc > 2)
		B = atoi(argv[2]);
	if (argc > 3) {
		 if (0!= __cilkrts_set_param("nworkers",argv[3])) {
    			printf("Failed to set worker count\n");
    			return 1;
 		}
	}	


	N = N;
	cout << N << "," << B << ",";
	if (B > N)
		B = N;

	SOF = (int *) _mm_malloc(N * N * sizeof(int), 64); //stores score-one-fold
#ifdef CO
			F = ( int *) _mm_malloc( N * N * sizeof( int ), 64); //stores score-one-fold
#endif
	//clearing the SOF array
	for (int i = 0; i < N; i++) {
	SOF[i*N:N] = 0;
}

//create arbitary protein seq

makeProteinSeq(N);

//compute SOF

SCORE_ONE_FOLD(N);

//allocate for the score array
#ifdef USE_PAPI
papi_init();
#endif

#ifdef LOOPDP
S_dp = ( int *) _mm_malloc( N * N * sizeof( int ), 64); //stores score-one-fold
//clearing the S array
for(int i = 0; i<N; i++)
{
	S_dp[i*N:N] = 0;
}
cout<<"LOOPDP";
unsigned long long tstart1 = cilk_getticks();
int final = LOOP_PROTEIN_FOLDING(N);
unsigned long long tend1 = cilk_getticks();
cout<<","<<cilk_ticks_to_seconds(tend1-tstart1)<<",";
#endif

#ifdef CO
S = ( int *) _mm_malloc( N * N * sizeof( int ), 64);
//clearing the S array
for(int i = 0; i<N; i++)
{
	S[i*N:N] = 0;
}
conv_RM_2_ZM_RM(F, 0, 0, N, N);
cout<<"CO:";
Z = ( int *) _mm_malloc( N * N * sizeof( int ), 64); //stores score-one-fold
for(int i = 0; i<N; i++)
{
	Z[i*N:N] = 0;
}

unsigned long long tstart = cilk_getticks();

int finalc=CO_PROTEIN_FOLDING(N);

unsigned long long tend = cilk_getticks();
cout<<","<<cilk_ticks_to_seconds(tend-tstart)<<",";

#ifdef DEBUG
#ifdef LOOPDP
#ifdef pdebug
cout<<"CO\n";
for(int i=0;i<N; i++)
{
	for(int j=0;j<N; j++)
	{
		cout<<Z[i*N+j]<<" ";
	}
	cout<<endl;
}
cout<<endl<<"LOOPDP"<<endl;
for(int i=0;i<N; i++)
{
	for(int j=0;j<N; j++)
	{
		cout<<S_dp[i*N+j]<<" ";
	}
	cout<<endl;
}
cout<<endl;
#endif

for(int i=0;i<N; i++)
{
	for(int j=0;j<N; j++)
	{
		if(Z[i*N+j]!=S_dp[i*N+j])
		cout<<"Wrong at"<<i<<" "<<j<<endl;
		assert(Z[i*N+j]==S_dp[i*N+j]);
	}

}
#endif
#endif
#endif

#ifdef LOOPDP
_mm_free(S_dp);
#endif

_mm_free(S);
_mm_free(Z);
_mm_free(SOF);
_mm_free(F);

#ifdef USE_PAPI
countTotalMiss(p);
cout<<endl;
PAPI_shutdown();

#endif
return 0;
}
