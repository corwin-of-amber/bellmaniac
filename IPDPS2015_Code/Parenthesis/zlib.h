/* Library functions to convert row major to Z morton and vice versa*/
#include <stdio.h>
#include <cilk/cilk.h>

/*
 N = matrix dimension.
 NP = matrix dimension after padding (if needed) for LOOPDP. Padding is required to reduce set associative cache miss.
 NPDQ = matrix dimension after padding (if needed) for Recursive. Padding is required to reduce set associative cache miss.
 B = base-case size or switching point to iterative algorithm.
 
 Pointers are used to improve running time for all the basecase kernels. In the basecases. Pointer xx used to point to x, uu used to point to u and vv used to point to v.
 
 */
long long N, NPDQ, NP;
int B;

#ifndef TYPE
#define TYPE int
#endif

/* Min Max and Weight Function */
#define min(a,b) (a<b?a:b)
#define max(a,b) (a>b?a:b)

/*Function to convert a row major matrix to Z-morton row major matrix. RM is the row major, ZM is Z-morton row major, ix, jx are the indices of the top left corner. ilen and jlen are the lengths of the x and y dimensions.
 */
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

/*Function to convert a Z-morton row major matrix back to row major matrix. RM is the row major, ZM is Z-morton row major matrix, ix, jx are the indices of the top left corner. ilen and jlen are the lengths of the x and y dimensions.
 Pointers are used to improve running time all around.
 */
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
