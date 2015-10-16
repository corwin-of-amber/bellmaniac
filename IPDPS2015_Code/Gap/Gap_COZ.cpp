//@Copyright: Jesmin Jahan Tithi, Rezaul Chowdhury, Department of Computer Science, Stony Brook University, Ny-11790
//Contact: jtithi@cs.stonybrook.edu,

//compile with :icpc -O3 -o gap Gap_DQ.cpp  -vec-report -parallel -xhost -AVX  -ansi-alias -restrict -ip -I$TACC_PAPI_INC -L$TACC_PAPI_LIB -DUSE_PAPI -lpapi  -lpfm -DUSE_PAPI -DCO -DLOOPDP
#include <stdio.h>
#include <math.h>

// C++ libraries
#include <iostream>
#include <algorithm>

// Cilk libraries
#include<cilk/cilk.h>
#include<cilk/cilk_api.h>

// User defined libraries
#include "cilktime.h" // tiMINg library

#ifdef USE_PAPI
#include "papilib.h"
#endif

using namespace std;

#ifndef TYPE
#define TYPE int
#endif

#ifndef ALIGNMENT
#define ALIGNMENT 64
#endif

int N, B, NP;
TYPE *Gap;
TYPE *G, *GG;
int *X, *Y;

#ifdef profile
int funcA_1=0, funcA_2 = 0, funcB_1 = 0, funcB_2 = 0, funcC_1=0, funcC_2 = 0;

int timeC=0, timeB=0, timeA=0;
#endif

#define w1(q, j) (j+q)
#define w2(p, i) (i+p)
#define Sn(x, y) ((x==y)?0:1)

#define min(a,b) (a<b?a:b)
#define max(a,b) (a>b?a:b)

void conv_RM_2_ZM_RM(TYPE *x, int ix, int jx, int ilen, int jlen) {
    if (ilen <= 0 || jlen <= 0)
        return;
    if (ilen <= B && jlen <= B) {
        for (int i = ix; i < ix + ilen; i++) {
#pragma ivdep
            for (int j = jx; j < jx + jlen; j++) {
                (*x++) = Gap[(i) * (N + 1) + j];
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
void conv_ZM_2_RM_RM(TYPE *x, TYPE* V, int ix, int jx, int ilen, int jlen) {
    if (ilen <= 0 || jlen <= 0)
        return;
    if (ilen <= B && jlen <= B) {
        for (int i = ix; i < ix + ilen; i++) {
#pragma ivdep
            for (int j = jx; j < jx + jlen; j++) {
                V[(i) * (N + 1) + j] = (*x++);
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

#ifdef LOOPDP
void LoopGAP(int n) {
    
    for (int t = 2; t <= n; t++) {
        
        cilk_for(int i = 1; i<t; i++)
        {
#ifdef USE_PAPI
            int id = tid();
            int retval = 0;
            papi_for_thread(id);
            if ( (retval=PAPI_start(EventSet[id])) != PAPI_OK)
                ERROR_RETURN(retval);
#endif
            
            int j = t - i;
            int in = i*(NP);
            TYPE G_ij = G[in - (NP) + (j - 1)] + Sn(X[i], Y[j]);
            TYPE *uu = G+in;
#pragma ivdep
            for (int q = 0; q<j; q++)
            {
                G_ij = min(G_ij, *uu + w1(q, j));
                uu++;
            }
#pragma ivdep
            for (int p = 0; p<i; p++)
            {
                G_ij = min(G_ij, G[p*(NP) + j] + w2(p, i));
            }
            G[in + j] = G_ij;
            
#ifdef USE_PAPI
            countMisses(id );
#endif
        }
        
    }
    int end = n + n + 1;
    for (int t = n + 1; t<end; t++) {
        
        cilk_for(int i = n; i >= t - n; i--)
        {
            
#ifdef USE_PAPI
            int id = tid();
            int retval = 0;
            papi_for_thread(id);
            if ( (retval=PAPI_start(EventSet[id])) != PAPI_OK)
                ERROR_RETURN(retval);
#endif
            int j = t - i;
            int in = i*NP;
            TYPE G_ij = G[in-(NP) + (j - 1)] + Sn(X[i], Y[j]);
            TYPE *uu = G +in;
#pragma ivdep
            for (int q = 0; q<j; q++)
            {
                G_ij = min(G_ij, *uu+ w1(q, j));
                uu++;
            }
#pragma ivdep
            for (int p = 0; p<i; p++)
            {
                G_ij = min(G_ij, G[p*(NP) + j] + w2(p, i));
            }
            
            G[in + j] = G_ij;
            
#ifdef USE_PAPI
            countMisses(id );
#endif
        }
        
    }
}
#endif

/*Generate Random Input*/

void genRandInput(int *X, int *Y, int n) {
    char a = 'A';
    for (int i = 0; i < n; i++) {
        X[i] = rand() % 4 + a;
        
    }
    for (int i = 0; i < n; i++) {
        Y[i] = rand() % 4 + a;
        
    }
    
}


void funcC_S( TYPE* x, TYPE* v, int x1, int y1, int x2, int Xilen, int Xjlen,
             int Tilen) {
    
    if (Tilen <= 0 || Xilen <= 0 || Xjlen <= 0)
        return;
#ifdef profile
    funcC_1++;
#endif
    if (Xilen <= B && Xjlen <= B) {
        //#if N>2047
        if (Tilen > B) {
            
            int n = (Tilen > Xjlen) ? Tilen : Xjlen;
            int c = 1;
            while (c < n)
                c = (c << 1);
            c = c >> 1;
            
            int tni, tnii;
            
            tni = min(c, Tilen);
            tnii = max(0, Tilen - c);
            
            funcC_S(x, v, x1, y1, x2, Xilen, Xjlen, tni);
            funcC_S(x, v + tni * Xjlen, x1, y1, x2 + tni, Xilen, Xjlen, tnii);
        } else {
#ifdef USE_PAPI
            int id = tid();
            int retval = 0;
            papi_for_thread(id);
            if ( (retval=PAPI_start(EventSet[id])) != PAPI_OK)
                ERROR_RETURN(retval);
#endif
            __declspec(align(64)) TYPE V[Tilen * Xjlen];
            TYPE *xx, *vv;
            
#pragma parallel
            for (int i = 0; i < Tilen; i++) {
                int in = i * Xjlen;
#pragma ivdep
                for (int j = 0; j < Xjlen; j++) {
                    V[j * Tilen + i] = v[in + j];
                }
            }
            int in;
            for (int i = (x1 == 0) ? 1 : 0; i < Xilen; i++) {
                
                int ii = x1 + i;
                int js = (y1 == 0) ? 1 : 0;
                xx = x + i * (Xjlen) + js;
                
                in = js * (Tilen);
                for (int j = js; j < Xjlen; j++) {
                    int jj = y1 + j;
                    
                    TYPE G_ij = *xx;
                    //in = j*(Tilen);
                    vv = V + in;
                    
#pragma ivdep
                    for (int p = 0; p < Tilen; p++) {
                        //#if N>2047
                        //G_ij = min (G_ij, V[in+p] + w2(x2+p, ii));
                        G_ij = min(G_ij, *vv + w2(x2+p, ii));
                        vv++;
                    }
                    
                    *xx = G_ij;
                    xx++;
                    in = in + Tilen;
                }
                
            }
#ifdef USE_PAPI
            countMisses(id );
#endif
            return;
        }
    } else {
        
        int n = (Xilen > Xjlen) ? Xilen : Xjlen;
        n = max(n, Tilen);
        int c = 1;
        while (c < n)
            c = (c << 1);
        c = c >> 1;
        
        int ni, nii, nj, njj;
        
        ni = min(c, Xilen);
        nj = min(c, Xjlen);
        nii = max(0, Xilen - c);
        njj = max(0, Xjlen - c);
        
        const int m11 = 0;
        int m12 = m11 + ni * nj;
        int m21 = m12 + ni * njj;
        int m22 = m21 + nii * nj;
        
        int tni, tnii;
        
        tni = min(c, Tilen);
        tnii = max(0, Tilen - c);
        int tm12 = m11 + tni * nj;
        int tm21 = tm12 + tni * njj;
        int tm22 = tm21 + tnii * nj;
        
        //if(ni>0 && nj>0 && tni>0)
        cilk_spawn funcC_S(x, v, x1, y1, x2, ni, nj, tni);
        cilk_spawn funcC_S(x + m12, v + tm12, x1, y1 + nj, x2, ni, njj, tni);
        cilk_spawn funcC_S(x + m21, v, x1 + ni, y1, x2, nii, nj, tni);
        funcC_S(x + m22, v + tm12, x1 + ni, y1 + nj, x2, nii, njj, tni);
        cilk_sync;
        
        cilk_spawn funcC_S(x, v + tm21, x1, y1, x2 + tni, ni, nj, tnii);
        cilk_spawn funcC_S(x + m12, v + tm22, x1, y1 + nj, x2 + tni, ni, njj,
                           tnii);
        cilk_spawn funcC_S(x + m21, v + tm21, x1 + ni, y1, x2 + tni, nii, nj,
                           tnii);
        funcC_S(x + m22, v + tm22, x1 + ni, y1 + nj, x2 + tni, nii, njj, tnii);
        
        cilk_sync;
    }
}

void funcB_S( TYPE*x, TYPE*u, int x1, int y1, int y2, int Xilen, int Xjlen,
             int Ljlen) {
    
    if (Xilen <= 0 || Xjlen <= 0 || Ljlen <= 0)
        return;
#ifdef profile
    funcB_1++;
#endif
    
    if (Xilen <= B && Xjlen <= B) {
        if (Ljlen > B) // Then further divide it
        {
            int n = (Xilen > Ljlen) ? Xilen : Ljlen;
            int c = 1;
            while (c < n)
                c = (c << 1);
            c = c >> 1;
            
            int lnj, lnjj;
            
            lnj = min(c, Ljlen);
            
            lnjj = max(0, Ljlen - c);
            
            //1st quad
            funcB_S(x, u, x1, y1, y2, Xilen, Xjlen, lnj);
            //1st quad
            funcB_S(x, u + Xilen * lnj, x1, y1, y2 + lnj, Xilen, Xjlen, lnjj);
            
        } else {
#ifdef USE_PAPI
            int id = tid();
            int retval = 0;
            papi_for_thread(id);
            if ( (retval=PAPI_start(EventSet[id])) != PAPI_OK)
                ERROR_RETURN(retval);
#endif
            TYPE *uu;
            int js = (y1 == 0) ? 1 : 0;
            register int ii, jj;
            int in;
            for (int i = (x1 == 0) ? 1 : 0; i < Xilen; i++) {
                ii = x1 + i;
                // TYPE *xx=x+i*(B)+js;
                in = i * Xjlen;
                for (int j = js; j < Xjlen; j++) {
                    jj = y1 + j;
                    
                    TYPE G_ij = x[in + j];
                    //*xx;
                    uu = u + i * (Ljlen);
#pragma ivdep
                    for (int q = 0; q < Ljlen; q++) {
                        //G_ij = min (G_ij, u[i*(Ljlen)+q] + w1(y2+q, jj));
                        G_ij = min(G_ij, *uu + w1(y2+q, jj));
                        uu++;
                    }
                    
                    //*xx= G_ij;
                    x[in + j] = G_ij;
                    //xx++;
                }
            }
            
            /*		  __declspec(align(64)) TYPE U[Xilen*Ljlen];
             #pragma parallel
             for(int i = 0; i<Xilen; i++)
             {
             int in = (i)*Ljlen;
             #pragma ivdep
             for(int j = 0; j<Ljlen; j++)
             {
             U[i*Ljlen+j]=u[in+j];
             
             }
             }
             // TYPE *uu;
             int js = (y1==0)?1:0;
             register int ii, jj;
             int in;
             for(int i = (x1==0)?1:0; i <Xilen; i++)
             {
             ii = x1+i;
             // TYPE *xx=x+i*(B)+js;
             in = i*Xjlen;
             for(int j = js; j< Xjlen ; j++ )
             {
             jj = y1+j;
             
             TYPE G_ij = x[in+j];
             //*xx;
             // uu = u + i*(Ljlen);
             #pragma ivdep
             for(int q = 0 ; q<Ljlen; q++)
             {
             G_ij = min (G_ij, U[i*(Ljlen)+q] + w1(y2+q, jj));
             //G_ij = min (G_ij, *uu + w1(y2+q, jj));
             //uu++;
             }
             
             //*xx= G_ij;
             x[in+j] = G_ij;
             //xx++;
             }
             }*/
#ifdef USE_PAPI
            countMisses(id );
#endif
            return;
        }
    } else {
        
        int n = (Xilen > Xjlen) ? Xilen : Xjlen;
        n = max(n, Ljlen);
        int c = 1;
        while (c < n)
            c = (c << 1);
        c = c >> 1;
        
        int ni, nii, nj, njj;
        
        ni = min(c, Xilen);
        nj = min(c, Xjlen);
        nii = max(0, Xilen - c);
        njj = max(0, Xjlen - c);
        
        const int m11 = 0;
        int m12 = m11 + ni * nj;
        int m21 = m12 + ni * njj;
        int m22 = m21 + nii * nj;
        
        int lnj, lnjj;
        
        lnj = min(c, Ljlen);
        lnjj = max(0, Ljlen - c);
        
        int lm12 = m11 + ni * lnj;
        int lm21 = lm12 + ni * lnjj;
        int lm22 = lm21 + nii * lnj;
        
        //1st quad
        cilk_spawn funcB_S(x, u, x1, y1, y2, ni, nj, lnj);
        
        //2nd Quad
        cilk_spawn funcB_S(x + m12, u, x1, y1 + nj, y2, ni, njj, lnj);
        
        //3rd Quad
        cilk_spawn funcB_S(x + m21, u + lm21, x1 + ni, y1, y2, nii, nj, lnj);
        
        //4th quad
        funcB_S(x + m22, u + lm21, x1 + ni, y1 + nj, y2, nii, njj, lnj);
        cilk_sync;
        
        //1st quad
        cilk_spawn funcB_S(x, u + lm12, x1, y1, y2 + lnj, ni, nj, lnjj);
        
        //2nd Quad
        cilk_spawn funcB_S(x + m12, u + lm12, x1, y1 + nj, y2 + lnj, ni, njj,
                           lnjj);
        
        //3rd quad
        cilk_spawn funcB_S(x + m21, u + lm22, x1 + ni, y1, y2 + lnj, nii, nj,
                           lnjj);
        
        //4th quad
        funcB_S(x + m22, u + lm22, x1 + ni, y1 + nj, y2 + lnj, nii, njj, lnjj);
        cilk_sync;
        
    }
}

void funcA_S(TYPE *x, TYPE*D, TYPE* T, TYPE* L, int Dilen, int Djlen, int Xilen,
             int Xjlen, int x1, int y1) {
    if (Xilen <= 0 || Xjlen <= 0 || x1 > N + 1 || y1 > N + 1)
        return;
    
#ifdef profile
    funcA_1++;
    
    int t0;
    if (xilen==N+1)
        t0= getMilliCount();
#endif
    if (Xilen <= B && Xjlen <= B) {
        
        //further divide it
        if (Dilen > B || Djlen > B) {
            
            int n = (Dilen > Djlen) ? Dilen : Djlen;
            int c = 1;
            while (c < n)
                c = (c << 1);
            c = c >> 1;
            
            int dni, dnii, dnj, dnjj;
            
            dni = min(c, Dilen);
            dnj = min(c, Djlen);
            dnii = max(0, Dilen - c);
            dnjj = max(0, Djlen - c);
            
            //	int dm12 =  dni*dnj;
            int dm21 = dni * dnj + dni * dnjj;
            int dm22 = dm21 + dnii * dnj;
            
            int tnj, tnjj;
            //tni = dni;
            tnj = min(c, Xjlen);
            //tnii = dnii;
            tnjj = max(0, Xjlen - c);
            
            //int tm12 = dni*tnj;
            int tm21 = dni * tnj + dni * tnjj;
            //int tm22 = tm21 + dnii*tnj;
            
            int lni, lnii;
            
            lni = min(c, Xilen);
            //lnj  = dnj;
            lnii = max(0, Xilen - c);
            //lnjj = dnjj;
            
            int lm12 = lni * dnj;
            //int lm21 = lm12 + lni*dnjj;
            //int lm22 = lm21 + lnii*dnj;
            
            funcA_S(x, D + dm22, T + tm21, L + lm12, dnii, dnjj, Xilen, Xjlen,
                    x1, y1);
        } else
            //compute base case in 3 steps
            //CASE1: i = 0; j varies from 0 to n
        {
#ifdef USE_PAPI
            int id = tid();
            int retval = 0;
            papi_for_thread(id);
            if ( (retval=PAPI_start(EventSet[id])) != PAPI_OK)
                ERROR_RETURN(retval);
#endif
            int in;
            if (x1 != 0) {
                
                //For 0,0
                
                if (y1 != 0) {
                    TYPE G_ij = D[Dilen * Djlen - 1] + Sn(X[x1], Y[y1]);
                    x[0] = min(x[0], G_ij);
                }
                
                //For 0, [1..n-1]
                TYPE *xx;
                in = (Dilen - 1) * Xjlen;
                for (int j = 1; j < Xjlen; j++) {
                    
                    int jj = y1 + j;
                    
                    TYPE G_ij = T[in + (j - 1)] + Sn(X[x1], Y[jj]);
                    
                    G_ij = min(x[j], G_ij);
                    xx = x;
#pragma ivdep
                    for (int q = 0; q < j; q++) {
                        G_ij = min(G_ij, *xx+ w1(y1 + q, jj));
                        xx++;
                    }
                    
                    x[j] = G_ij;
                    
                }
                
            }
            
            //CASE2: j = 0, i varies from 0 to n
            ///////////////////////////////////////////////////
            //For 1, 0..n
            
            __declspec(align(64)) TYPE V[Xilen * Xjlen];
#pragma parallel
            for (int i = 0; i < Xilen; i++) {
                int in = (i) * Xjlen;
#pragma ivdep
                for (int j = 0; j < Xjlen; j++) {
                    V[j * Xilen + i] = x[in + j];
                    
                }
            }
            if (y1 != 0) {
                in = (Xjlen);
                for (int i = 1; i < Xilen; i++) {
                    int ii = x1 + i;
                    
                    TYPE G_ij = L[i * Djlen - 1] + Sn(X[ii], Y[y1]);
                    
                    G_ij = min(x[in], G_ij);
#pragma ivdep
                    for (int p = 0; p < i; p++) {
                        //	G_ij = min(G_ij, x[p*(Xjlen)] + w2(x1 + p, ii));
                        G_ij = min(G_ij, V[p] + w2(x1 + p, ii));
                    }
                    
                    x[in] = G_ij;
                    in = in + (Xjlen);
                }
            }
            
            //CASE3: both i and j starts from 1 ends at n
            in = Xjlen;
            int inj;
            for (int i = 1; i < Xilen; i++) {
                int ii = x1 + i;
                
                for (int j = 1; j < Xjlen; j++) {
                    int jj = y1 + j;
                    
                    TYPE G_ij = x[(in) - (Xjlen) + (j - 1)] + Sn(X[ii], Y[jj]);
                    
                    G_ij = min(x[in + j], G_ij);
#pragma ivdep
                    for (int q = 0; q < j; q++) {
                        G_ij = min(G_ij, x[in+q] + w1(y1 + q, jj));
                    }
                    inj = j * Xilen;
#pragma vector
#pragma ivdep
                    for (int p = 0; p < i; p++) {
                        G_ij = min(G_ij, V[inj+p]+ w2(x1 + p, ii));
                    }
                    
                    x[in + j] = G_ij;
                    
                }
                
                in = in + Xjlen;
            }
#ifdef USE_PAPI
            countMisses(id );
#endif
            return;
        }
    } else {
        
        int n = (Xilen > Xjlen) ? Xilen : Xjlen;
        n = max(n, Dilen);
        n = max(n, Djlen);
        
        int c = 1;
        while (c < n)
            c = (c << 1);
        c = c >> 1;
        
        int ni, nii, nj, njj;
        
        ni = min(c, Xilen);
        nj = min(c, Xjlen);
        nii = max(0, Xilen - c);
        njj = max(0, Xjlen - c);
        
        const int m11 = 0;
        int m12 = m11 + ni * nj;
        int m21 = m12 + ni * njj;
        int m22 = m21 + nii * nj;
        
        int dni, dnii, dnj, dnjj;
        
        dni = min(c, Dilen);
        dnj = min(c, Djlen);
        dnii = max(0, Dilen - c);
        dnjj = max(0, Djlen - c);
        
        int dm12 = dni * dnj;
        int dm21 = dm12 + dni * dnjj;
        int dm22 = dm21 + dnii * dnj;
        
        int tm12 = dni * nj;
        int tm21 = tm12 + dni * njj;
        int tm22 = tm21 + dnii * nj;
        
        int lm12 = ni * dnj;
        int lm21 = lm12 + ni * dnjj;
        int lm22 = lm21 + nii * dnj;
        
        funcA_S(x + m11, D + dm22, T + tm21, L + lm12, dnii, dnjj, ni, nj, x1,
                y1);
        
#ifdef profile
        int tB = getMilliCount();
#endif
        
        //if(ni>0 && nj>0 && njj>0)
        cilk_spawn funcB_S(x + m12, x, x1, y1 + nj, y1, ni, njj, nj);
#ifdef profile
        timeB+= getMilliSpan(tB);
#endif
        
#ifdef profile
        int tc = getMilliCount();
#endif
        
        funcC_S(x + m21, x + m11, x1 + ni, y1, x1, nii, nj, ni);
#ifdef profile
        timeC+= getMilliSpan(tc);;
#endif
        cilk_sync;
        
        cilk_spawn funcA_S(x + m12, T + tm21, T + tm22, x + m11, dnii, nj, ni,
                           njj, x1, y1 + nj);
        
        funcA_S(x + m21, L + lm12, x + m11, L + lm22, ni, dnjj, nii, nj,
                x1 + ni, y1);
        cilk_sync;
        
#ifdef profile
        tB = getMilliCount();
#endif
        {
            funcB_S(x + m22, x + m21, x1 + ni, y1 + nj, y1, nii, njj, nj);
            
#ifdef profile
            timeB+= getMilliSpan(tB);;
#endif
            
#ifdef profile
            tc = getMilliCount();
#endif
            
            funcC_S(x + m22, x + m12, x1 + ni, y1 + nj, x1, nii, njj, ni);
            
#ifdef profile
            timeC+= getMilliSpan(tc);;
#endif
            //(x22, x11, x12, x21, nn)
            funcA_S(x + m22, x + m11, x + m12, x + m21, ni, nj, nii, njj,
                    x1 + ni, y1 + nj);
        }
        
    }
#ifdef profile
    if (n==N+1)
        timeA+= getMilliSpan(t0);
#endif
    return;
}

int main(int argc, char *argv[]) {
    N = 0;
    B = 0;
    
    //cout<<argv[0]<<endl;
    
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
    //B = 32;
    //printf( "Original N = %d , B = %d \n", N, B );
    
    int NN = 2;
    NP = N + 1;
    while (NN < (N + 1))
        NN = (NN << 1); //find the next power of two
    
    if (B > NN) {
        B = N;
    }
    
    if (NN == N + 1)
        NP = N + 2;
    X = (int *) _mm_malloc((N + 1) * sizeof(int), ALIGNMENT);
    Y = (int *) _mm_malloc((N + 1) * sizeof(int), ALIGNMENT);
    
    X[0] = Y[0] = 32;
    genRandInput(X, Y, N + 1);
    
#ifdef USE_PAPI
    papi_init();
#endif
    
#ifdef CO
    Gap = (TYPE *)_mm_malloc((N + 1) * (N + 1) * sizeof(TYPE), ALIGNMENT);
    GG = (TYPE *)_mm_malloc((N + 1) * (N + 1) * sizeof(TYPE), ALIGNMENT);
    Gap[0] = 0;
#endif
    
#ifdef LOOPDP
    G = (TYPE *)_mm_malloc((NP) * (NP) * sizeof(TYPE), ALIGNMENT);
    G[0] = 0;
    
#endif
    
    TYPE inf = (TYPE) (1e9);
    for (int i = 0; i < N + 1; i++) {
        int in = i * (N + 1);
#ifdef CO
        Gap[in] = w1(i, 0);
#endif
        
#ifdef LOOPDP
        G[i*NP] = w1(i, 0);
#endif
    }
    
    for (int i = 0; i < N + 1; i++) {
#ifdef CO
        Gap[i] = w2(0, i);
#endif
        
#ifdef LOOPDP
        G[i] = w2(0, i);;
#endif
    }
    
    for (int i = 1; i < N + 1; i++)
        for (int j = 1; j < N + 1; j++) {
            int in = i * (N + 1) + j;
#ifdef CO
            Gap[in] = inf;
#endif
            
#ifdef LOOPDP
            G[i * (NP) + j] = inf;
#endif
        }
    
#ifdef LOOPDP
    unsigned long long tstart1 = cilk_getticks();
    LoopGAP(N);
    unsigned long long tend1 = cilk_getticks();
    cout<<"LOOPDP,"<<N<<","<<__cilkrts_get_nworkers()<<","<<cilk_ticks_to_seconds(tend1-tstart1)<<",";
#ifdef USE_PAPI
    countTotalMiss(p);
    cout<<",";
#endif
    
#ifdef pdeBug
    for (int i = 0; i< N + 1; i++)
    {
        cout << (char)X[i];
    }
    cout << endl;
    for (int i = 0; i< N + 1; i++)
    {
        cout << (char)Y[i];
    }
    cout << endl;
    for (int i = 0; i<N + 1; i++)
    {
        for (int j = 0; j< N + 1; j++)
        {
            cout << G[i * (NP) + j] << " ";
            
        }
        cout << endl;
    }
    
#endif
    
#endif
    
#ifdef CO
    
    conv_RM_2_ZM_RM(GG, 0, 0, (N + 1), (N + 1));
#ifdef USE_PAPI
    papi_reset();
#endif
    unsigned long long tstart = cilk_getticks();
    funcA_S(GG, GG, GG, GG, N+1, N+1, N+1, N+1, 0, 0); //send NN instead of N
    unsigned long long tend = cilk_getticks();
    cout<<"CO,"<<N<<","<<__cilkrts_get_nworkers()<<","<<B<<","<<cilk_ticks_to_seconds(tend-tstart)<<",";
#ifdef USE_PAPI
    countTotalMiss(p);
    cout<<",";
#endif
    conv_ZM_2_RM_RM(GG, Gap, 0, 0, (N + 1), (N + 1));
    _mm_free(GG);
    
#endif
#ifdef LOOPDP
#ifdef CO
#ifdef pdeBug
    cout << "CO matrix:" << endl;
    for (int i = 0; i<N + 1; i++)
    {
        for (int j = 0; j< N + 1; j++)
        {
            
            cout << Gap[i*(N + 1) + j] << " ";
            
        }
        cout << endl;
    }
#endif
    for (int i = 0; i<N + 1; i++)
    {
        for (int j = 0; j< N + 1; j++)
        {
            if(Gap[i*(N+1)+j]!=G[i * (NP) + j])
            {
                cout<<"wrong at"<<i<<","<<j<<endl;
                fflush(stdout);
            }
            assert(Gap[i*(N + 1) + j] == G[i * (NP) + j]);
        }
    }
#endif
    
    _mm_free(G);
#endif
    
#ifdef profile
    cout<<funcA_1<<","<<funcA_2<<","<<funcB_1<<","<<funcB_2<<","<<funcC_1<<","<<funcC_2<<",";
    cout<<timeA-(timeB+timeC)<<endl;
    cout<<timeA<<","<<timeB<<","<<timeC<<endl;
#endif
    _mm_free(Gap);
    _mm_free(X);
    _mm_free(Y);
#ifdef USE_PAPI
    papi_end();
#endif
    cout<<endl;
    return 0;
}
