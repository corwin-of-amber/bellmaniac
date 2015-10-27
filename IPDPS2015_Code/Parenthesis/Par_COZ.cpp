//@Copyright: Jesmin Jahan Tithi,  Rezaul Chowdhury, Department of Computer Science, Stony Brook University, Ny-11790
//Contact: jtithi@cs.stonybrook.edu,

/*compile with :icc -O3 -o parCOZ Par_COZ.cpp -DCO -xhost  -ansi-alias -ip -opt-subscript-in-range -opt-prefetch=4 -fomit-frame-pointer
 -funroll-all-loops -vec-report  -parallel -restrict*/

/*
 This program implements recursive divide and conquer algorithms for the Parenthesis Problem
 It uses Z morton lay out to store the data. This program works for any n.
 When running the program, it takes input size, base case, number of cores as input.
 
 If you want you can compile only the standard iterative version by compiling with Flag -DLOOPDP.
 Or you can only compile the recursive version by compiling it with -DCO.
 
 If you use both -DLOOPDP and -DCO at the same time, it will automatically test the resultant matrices for correctness.
 
 You can see the actual values stored in the matrices, use -Dpdebug during compilation.
 
 To get cache misses, compile with -DUSE_PAPI -lpapi -I/path to papi include -L/path to papi lib
 
 compile with :icpc -O3 -AVX  -xhost -o  fwr FW_COZ.cpp  -ansi-alias -ip -opt-subscript-in-range -opt-prefetch=4 -fomit-frame-pointer -funroll-all-loops -vec-report  -parallel -restrict
 
 However, these parameters are not guaranteed to give the best running times. You may need to check several of them.
 
 
 Naming convension: All functions with name func[A,B,C,D]_S only works on power of 2.
 All functions with name func[A,B,C,D] only works for any n.
 
 */

#include <stdio.h>
#include <stdlib.h>
#include <iostream>
#include <cilk/cilk.h>
#include <cilk/cilk_api.h>
#include <math.h>
#include "cilktime.h"
#include "zlib.h"
#ifdef USE_PAPI
#include "papilib.h"
#endif

using namespace std;

#ifndef ALIGNMENT
#define ALIGNMENT 64
#endif

/*
 dist is the initial matrix for recursive.
 X is used to store the Z morton conversion of dist and then used for the actual computation.
 D is used for iterative/LOOPDP computation.
 Pointers are used to improve running time for all the basecase kernels. In the basecases. Pointer xx used to point to x, uu used to point to u and vv used to point to v.
 */
TYPE *dist, *X;

#define w(i, j, k) (((i*j*k)&7)) // Weight function

/* Parallel LOOPDP/Iterative function for parenthesis problem. Follows directly for the standard algorithm, except it uses pointer arithmatics for improved running times.
 It solves the cells in diagonal by diagonal manner.
 */

#ifdef LOOPDP
TYPE* D;
void parenthesis( long long n ) {
    for(int t = 2 ; t <n; t++){
        cilk_for(int i = 0 ; i< n-t; i++ )
        {
#ifdef USE_PAPI
            // start papi counter.
            int id = tid();
            int retval = 0;
            papi_for_thread(id);
            if ( (retval=PAPI_start(EventSet[id])) != PAPI_OK)
                ERROR_RETURN(retval);
#endif
            
            int j = t+i;
            int in = i*NP;
            int D_ij = D[in+j];
            TYPE *uu=D+in+i+1;
            TYPE *vv=D+in+NP+j;
#pragma ivdep
            for(int k = i+1 ; k<=j; k++)
            {
                D_ij = min (D_ij, *uu + *vv + w(i,j,k));
                uu++;
                vv = vv + NP;
            }
            D[in+j] = D_ij;
#ifdef USE_PAPI
            // end papi counter
            countMisses(id );
#endif
        }
    }
    return;
}
#endif


/*
 Function C for Parenthesis problem recursive algorithm. x is output, u and v are inputs. n is the size.
 Works and called only for power of 2.
 xi, xj = top left corner of matrix x;
 xi, uj = top left corner for u.
 vi, xj = top left corner for v.
 Pointers arithmatics are used to improve running time all around.
 */

void funcC_S( TYPE *x, TYPE *u, TYPE *v, long long n, int xi, int xj, int uj, int vi) {
    // Basecase
    if (n <= B) {
        
#ifdef USE_PAPI
        // Start papi counter
        int id = tid();
        int retval = 0;
        papi_for_thread(id);
        if ( (retval=PAPI_start(EventSet[id])) != PAPI_OK)
            ERROR_RETURN(retval);
#endif
        register int in = 0;
        register int I, J, K;
        __declspec(align(64)) TYPE V[B * B];
#pragma parallel
        for (int i = 0; i < B; i++) {
            int in = i * B;
#pragma ivdep
            for (int j = 0; j < B; j++) {
                V[in + j] = v[j * B + i];
            }
        }
        TYPE *uu, *vv;
        int inj;
        //#pragma parallel
        for (int i = 0; i < n; i++) {
            inj = 0;
            for (int j = 0; j < n; j++) {
                TYPE x_ij = x[in + j];
                
                I = xi + i;
                J = xj + j;
                uu = u + in;
                K = uj;
                vv = V + inj;
#pragma ivdep
                for (int k = 0; k < n; k++) {
                    x_ij = min(x_ij, (*uu + *vv) + w((I), (J), (K)));
                    K++;
                    uu++;
                    vv++;
                }
                inj = inj + B;
                x[in + j] = x_ij;
            }
            in = in + B;
        }
#ifdef USE_PAPI
        countMisses(id );
#endif
        return;
    } else {
        long long nn = (n >> 1);
        long long nn2 = nn * nn;
        
        const long long m11 = 0;
        long long m12 = m11 + nn2;
        long long m21 = m12 + nn2;
        long long m22 = m21 + nn2;
        
        cilk_spawn funcC_S(x + m11, u + m11, v + m11, nn, xi, xj, uj, vi);
        cilk_spawn funcC_S(x + m12, u + m11, v + m12, nn, xi, xj + nn, uj, vi);
        cilk_spawn funcC_S(x + m21, u + m21, v + m11, nn, xi + nn, xj, uj, vi);
        funcC_S(x + m22, u + m21, v + m12, nn, xi + nn, xj + nn, uj, vi);
        cilk_sync;
        
        cilk_spawn funcC_S(x + m11, u + m12, v + m21, nn, xi, xj, uj + nn,
                           vi + nn);
        cilk_spawn funcC_S(x + m12, u + m12, v + m22, nn, xi, xj + nn, uj + nn,
                           vi + nn);
        cilk_spawn funcC_S(x + m21, u + m22, v + m21, nn, xi + nn, xj, uj + nn,
                           vi + nn);
        funcC_S(x + m22, u + m22, v + m22, nn, xi + nn, xj + nn, uj + nn,
                vi + nn);
    }
}

/*
 Function B for Parenthesis problem recursive algorithm. x is output, u and v are inputs. n is the size.
 Works and called only for power of 2.
 xi, xj = top left corner of matrix x;
 xi, uj = top left corner for u.
 vi, xj = top left corner for v.
 Pointers arithmatics are used to improve running time all around.
 */
void funcB_S( TYPE *x, TYPE *u, TYPE *v, long long n, int xi, int xj, int uj,
             int vi) {
    // basecase
    if (n <= B) {
        
#ifdef USE_PAPI
        // Starts papi counter
        int id = tid();
        int retval = 0;
        papi_for_thread(id);
        if ( (retval=PAPI_start(EventSet[id])) != PAPI_OK)
            ERROR_RETURN(retval);
#endif
        
        // Copy optimizations
        __declspec(align(64)) TYPE V[B * B];
        
#pragma parallel
        for (int i = 0; i < B; i++) {
            int in = i * B;
#pragma ivdep
            for (int j = 0; j < B; j++) {
                V[in + j] = v[j * B + i];
            }
        }
        
        // Actual basecase
        TYPE *uu, *vv;
        register int I, J, K;
        
        for (int t = n - 1; t >= 0; t--) {
            register int in = t * B;
            
            for (int i = t; i < n; i++) {
                
                int j = i - t;
                
                TYPE x_ij = x[in + j];
                I = xi + i;
                J = xj + j;
                K = uj + i;
                
                uu = u + in + i;
                vv = x + in + j;
                
#pragma ivdep
                for (int k = i; k < n; k++) {
                    x_ij = min(x_ij, *uu + *vv + w((I), (J), (K)));
                    uu++;
                    K++;
                    vv = vv + B;
                }
                
                uu = x + in;
                vv = V + j * B;
                K = vi;
                
#pragma ivdep
                for (int k = 0; k <= j; k++) {
                    x_ij = min(x_ij, *uu+*vv+w((I), (J), (K)));
                    uu++;
                    K++;
                    vv++;
                }
                x[in + j] = x_ij;
                in = in + B;
            }
        }
        
        for (int t = 1; t < n; t++) {
            
            register int in = 0;
            for (int i = 0; i < n - t; i++) {
                int j = t + i;
                int x_ij = x[in + j];
                
                uu = u + in + i;
                
                vv = x + in + j;
                
                I = xi + i;
                J = xj + j;
                K = uj + i;
                
#pragma ivdep
                for (int k = i; k < n; k++) {
                    x_ij = min(x_ij, *uu + *vv+w((I), (J), (K)));
                    uu++;
                    K++;
                    vv = vv + B;
                }
                
                // #pragma simd
                
                uu = x + in;
                vv = V + j * B;
                K = vi;
#pragma ivdep
                for (int k = 0; k <= j; k++) {
                    x_ij = min(x_ij, *uu + *vv + w((I), (J), (K)));
                    uu++;
                    K++;
                    vv++;
                    //vv = vv + B;
                }
                x[in + j] = x_ij;
                in = in + B;
            }
        }
#ifdef USE_PAPI
        //Stops papi counter
        countMisses(id );
#endif
        return;
    } else {
        long long nn = (n >> 1);
        long long nn2 = nn * nn;
        const long long m11 = 0;
        long long m12 = m11 + nn2;
        long long m21 = m12 + nn2;
        long long m22 = m21 + nn2;
        
        funcB_S(x + m21, u + m22, v + m11, nn, xi + nn, xj, uj + nn, vi);
        
        cilk_spawn funcC_S(x + m11, u + m12, x + m21, nn, xi, xj, uj + nn,
                           xi + nn);
        funcC_S(x + m22, x + m21, v + m12, nn, xi + nn, xj + nn, xj, vi);
        cilk_sync;
        
        cilk_spawn funcB_S(x + m11, u + m11, v + m11, nn, xi, xj, uj, vi);
        funcB_S(x + m22, u + m22, v + m22, nn, xi + nn, xj + nn, uj + nn,
                vi + nn);
        cilk_sync;
        funcC_S(x + m12, u + m12, x + m22, nn, xi, xj + nn, uj + nn, xi + nn);
        funcC_S(x + m12, x + m11, v + m12, nn, xi, xj + nn, xj, vi);
        funcB_S(x + m12, u + m11, v + m22, nn, xi, xj + nn, uj, vi + nn);
    }
}

/*
 Function A for Parenthesis problem recursive algorithm. x is output and input matrix. n is the size.
 Works and called only for power of 2.
 xi, xj = top left corner of matrix x;
 Pointers arithmatics are used to improve running time all around.
 */

void funcA_S( TYPE * x, long long n, int xi, int xj) {
    // Basecase
    if (n <= B) {
        // Papi counters start
#ifdef USE_PAPI
        int id = tid();
        int retval = 0;
        papi_for_thread(id);
        if ( (retval=PAPI_start(EventSet[id])) != PAPI_OK)
            ERROR_RETURN(retval);
#endif
        
        // Basecase kernel
        TYPE *u, *v;
        register int I, J, K;
        for (int t = 2; t < n; t++) {
            int in = 0;
            
            for (int i = 0; i < n - t; i++) {
                int j = t + i;
                
                int x_ij = x[in + j];
                
                I = xi + i;
                J = xj + j;
                u = x + in + i + 1;
                
                v = x + in + B + j;
                K = xj + i + 1;
#pragma ivdep
                for (int k = i + 1; k <= j; k++) {
                    
                    x_ij = min(x_ij, (*u + *v)+w((I), (J), (K)));
                    u++;
                    K++;
                    v = v + B;
                }
                x[in + j] = x_ij;
                in = in + B;
            }
        }
#ifdef USE_PAPI
        //stop papi
        countMisses(id );
#endif
        return;
    } else {
        long long nn = (n >> 1);
        long long nn2 = nn * nn;
        
        const long long m11 = 0;
        long long m12 = m11 + nn2;
        long long m21 = m12 + nn2;
        long long m22 = m21 + nn2;
        
        cilk_spawn funcA_S(x + m11, nn, xi, xj);
        funcA_S(x + m22, nn, xi + nn, xj + nn);
        cilk_sync;
        
        funcB_S(x + m12, x + m11, x + m22, nn, xi, xj + nn, xj, xi + nn);
    }
}

/*
 Function C for Parenthesis problem recursive algorithm. x is output, u and v are inputs. n is the size.
 Works for any n.
 xi, xj = top left corner of matrix x;
 xi, uj = top left corner for u.
 vi, xj = top left corner for v.
 xilen = length of row dimension for matrix x
 xjlen = length of column dimension for matrix x
 ujlen = length of column dimension for matrix u
 vilen = length of row dimension for matrix v
 Pointers arithmatics are used to improve running time all around.
 */

void funcC( TYPE *x, TYPE *u, TYPE *v, int xilen, int xjlen, int ujlen,
           int vilen, int xi, int xj, int uj, int vi) {
    if (xilen <= 0 || xjlen <= 0 || ujlen <= 0 || vilen <= 0)
        return;
    
    // If all dimensions are equal/square
    if ((xilen == xjlen) && (xjlen == ujlen) && (ujlen == vilen)) {
        // Basecase
        if (xilen <= B) {
#ifdef USE_PAPI
            int id = tid();
            int retval = 0;
            papi_for_thread(id);
            if ( (retval=PAPI_start(EventSet[id])) != PAPI_OK)
                ERROR_RETURN(retval);
#endif
            register int in = 0;
            register int I, J, K;
            
            __declspec(align(64)) TYPE V[B * B];
            
#pragma parallel
            for (int i = 0; i < vilen; i++) {
                int in = i * vilen;
#pragma ivdep
                for (int j = 0; j < xjlen; j++) {
                    V[in + j] = v[j * xjlen + i];
                }
            }
            
            TYPE *uu, *vv;
            int inj = 0;
            //#pragma parallel
            for (int i = 0; i < xilen; i++) {
                inj = 0;
                for (int j = 0; j < xilen; j++) {
                    TYPE x_ij = x[in + j];
                    
                    I = xi + i;
                    J = xj + j;
                    uu = u + in;
                    vv = V + inj;
                    K = uj;
#pragma ivdep
                    for (int k = 0; k < xilen; k++) {
                        x_ij = min(x_ij, (*uu + *vv)+w((I), (J), (K)));
                        K++;
                        uu++;
                        vv++;
                    }
                    inj = inj + vilen;
                    x[in + j] = x_ij;
                }
                in = in + xilen;
            }
#ifdef USE_PAPI
            countMisses(id );
#endif
            return;
        }
        else {
            // Recursion case.
            long long nn = (xilen >> 1);
            long long nn2 = nn * nn;
            
            const long long m11 = 0;
            long long m12 = m11 + nn2;
            long long m21 = m12 + nn2;
            long long m22 = m21 + nn2;
            
            cilk_spawn funcC_S(x + m11, u + m11, v + m11, nn, xi, xj, uj, vi);
            cilk_spawn funcC_S(x + m12, u + m11, v + m12, nn, xi, xj + nn, uj,
                               vi);
            cilk_spawn funcC_S(x + m21, u + m21, v + m11, nn, xi + nn, xj, uj,
                               vi);
            funcC_S(x + m22, u + m21, v + m12, nn, xi + nn, xj + nn, uj, vi);
            cilk_sync;
            
            cilk_spawn funcC_S(x + m11, u + m12, v + m21, nn, xi, xj, uj + nn,
                               vi + nn);
            cilk_spawn funcC_S(x + m12, u + m12, v + m22, nn, xi, xj + nn,
                               uj + nn, vi + nn);
            cilk_spawn funcC_S(x + m21, u + m22, v + m21, nn, xi + nn, xj,
                               uj + nn, vi + nn);
            funcC_S(x + m22, u + m22, v + m22, nn, xi + nn, xj + nn, uj + nn,
                    vi + nn);
        }
    } else {
        // Otherwise, if all dimensions are not the same
        if (xilen <= B && xjlen <= B) {
            
            //basecase
#ifdef USE_PAPI
            // start papi counter
            int id = tid();
            int retval = 0;
            papi_for_thread(id);
            if ( (retval=PAPI_start(EventSet[id])) != PAPI_OK)
                ERROR_RETURN(retval);
#endif
            register int in = 0;
            register int uin = 0;
            register int I, J, K;
            
            // Copy optimization
            __declspec(align(64)) TYPE V[vilen * xjlen];
            
#pragma parallel
            for (int i = 0; i < vilen; i++) {
                int in = i * xjlen;
#pragma ivdep
                for (int j = 0; j < xjlen; j++) {
                    V[j * vilen + i] = v[in + j];
                }
            }
            
            //Base case computation
            TYPE *uu, *vv;
            int inj = 0;
#pragma parallel
            for (int i = 0; i < xilen; i++) {
                inj = 0;
                for (int j = 0; j < xjlen; j++) {
                    TYPE x_ij = x[in + j];
                    
                    I = xi + i;
                    J = xj + j;
                    uu = u + uin;
                    vv = V + inj;
                    K = uj;
#pragma ivdep
                    for (int k = 0; k < ujlen; k++) {
                        x_ij = min(x_ij, (*uu + *vv)+w((I), (J), (K)));
                        K++;
                        uu++;
                        vv++;
                    }
                    inj = inj + vilen;
                    x[in + j] = x_ij;
                }
                in = in + xjlen;
                uin = uin + ujlen;
            }
#ifdef USE_PAPI
            countMisses(id );
#endif
            return;
        } else {
            
            // recursive case.
            long long n = (xilen > xjlen) ? xilen : xjlen;
            long long c = 1;
            while (c < n)
                c = (c << 1);
            c = c >> 1;
            
            long long ni, nii, nj, njj;
            
            ni = min(c, xilen);
            nj = min(c, xjlen);
            nii = max(0, xilen - c);
            njj = max(0, xjlen - c);
            
            long long unj, unjj; //uni and unii are the same as ni and nii
            
            //uni = ni;
            unj = min(c, ujlen);
            //unii = nii;
            unjj = max(0, ujlen - c);
            
            //necessary values for V
            long long vni, vnii; //vnj and vnjj are the same as nj and njj
            
            vni = min(c, vilen);
            
            vnii = max(0, vilen - c);
            
            TYPE *x12, *x21, *x22, *u12, *u21, *u22, *v12, *v21, *v22;
            
            x12 = x + ni * nj;
            u12 = u + ni * unj;
            v12 = v + vni * nj;
            
            x21 = x12 + ni * njj;
            u21 = u12 + ni * unjj;
            v21 = v12 + vni * njj;
            
            x22 = x21 + nii * nj;
            u22 = u21 + nii * unj;
            v22 = v21 + vnii * nj;
            
            if (unj > 0 && vni > 0) {
                
                //if(ni>0 && nj >0)
                cilk_spawn funcC(x, u, v, ni, nj, unj, vni, xi, xj, uj, vi);
                
                //if(ni>0 && njj >0)
                cilk_spawn funcC(x12, u, v12, ni, njj, unj, vni, xi, xj + nj,
                                 uj, vi);
                
                //if(nii>0 && nj >0)
                cilk_spawn funcC(x21, u21, v, nii, nj, unj, vni, xi + ni, xj,
                                 uj, vi);
                
                if (nii > 0 && njj > 0)
                    funcC(x22, u21, v12, nii, njj, unj, vni, xi + ni, xj + nj,
                          uj, vi);
                cilk_sync;
            }
            
            if (unjj > 0 && vnii > 0) {
                
                //	if(ni>0 && nj >0)
                cilk_spawn funcC(x, u12, v21, ni, nj, unjj, vnii, xi, xj,
                                 uj + unj, vi + vni);
                
                //	if(ni>0 && njj >0)
                cilk_spawn funcC(x12, u12, v22, ni, njj, unjj, vnii, xi,
                                 xj + nj, uj + unj, vi + vni);
                
                //	if(nii>0 && nj >0)
                cilk_spawn funcC(x21, u22, v21, nii, nj, unjj, vnii, xi + ni,
                                 xj, uj + unj, vi + vni);
                
                if (nii > 0 && njj > 0)
                    funcC(x22, u22, v22, nii, njj, unjj, vnii, xi + ni, xj + nj,
                          uj + unj, vi + vni);
                cilk_sync;
            }
        }
    }
}

/*
 Function B for Parenthesis problem recursive algorithm. x is output, u and v are inputs. n is the size.
 Works for any n.
 xi, xj = top left corner of matrix x;
 xi, uj = top left corner for u.
 vi, xj = top left corner for v.
 xilen = length of row dimension for matrix x
 xjlen = length of column dimension for matrix x
 ujlen = length of column dimension for matrix u
 vilen = length of row dimension for matrix v
 Pointers arithmatics are used to improve running time all around.
 */
void funcB( TYPE *x, TYPE *u, TYPE *v, int xilen, int xjlen, int ujlen,
           int vilen, int xi, int xj, int uj, int vi)
//void funcB( TYPE *x, TYPE *u, TYPE *v, long long n, int xi, int xj, int uj, int vi )
{
    if (xilen <= 0 || xjlen <= 0 || ujlen <= 0 || vilen <= 0)
        return;
    // If all matrices are of the same size and square
    if ((xilen == xjlen) && (xjlen == ujlen) && (ujlen == vilen)) {
        
        // Basecase kernel
        if (xilen <= B) {
            
#ifdef USE_PAPI
            int id = tid();
            int retval = 0;
            papi_for_thread(id);
            if ( (retval=PAPI_start(EventSet[id])) != PAPI_OK)
                ERROR_RETURN(retval);
#endif
            TYPE *uu, *vv;
            register int I, J, K;
            
            //copy optimization.
            __declspec(align(64)) TYPE V[vilen * xjlen];
            
#pragma parallel
            for (int i = 0; i < vilen; i++) {
                int in = i * xjlen;
#pragma ivdep
                for (int j = 0; j < xjlen; j++) {
                    V[j * vilen + i] = v[in + j];
                }
            }
            register int in;
            for (int t = xilen - 1; t >= 0; t--) {
                in = t * B;
                for (int i = t; i < xilen; i++) {
                    
                    int j = i - t;
                    
                    TYPE x_ij = x[in + j];
                    //#pragma simd
                    
                    I = xi + i;
                    J = xj + j;
                    K = uj + i;
                    
                    uu = u + in + i;
                    vv = x + in + j;
                    
#pragma ivdep
                    for (int k = i; k < xilen; k++) {
                        x_ij = min(x_ij, *uu+*vv+w((I), (J), (K)));
                        uu++;
                        K++;
                        vv = vv + B;
                    }
                    
                    //#pragma simd
                    
                    uu = x + in;
                    vv = V + j * vilen;
                    K = vi;
#pragma ivdep
                    for (int k = 0; k <= j; k++) {
                        
                        x_ij = min(x_ij, *uu+*vv+w((I), (J), (K)));
                        uu++;
                        K++;
                        vv++;
                        //vv = vv + B;
                    }
                    x[in + j] = x_ij;
                    in = in + B;
                }
            }
            
            for (int t = 1; t < xilen; t++) {
                
                register int in = 0;
                for (int i = 0; i < xilen - t; i++) {
                    int j = t + i;
                    int x_ij = x[in + j];
                    
                    uu = u + in + i;
                    
                    vv = x + in + j;
                    
                    I = xi + i;
                    J = xj + j;
                    K = uj + i;
                    
#pragma ivdep
                    for (int k = i; k < xilen; k++) {
                        
                        x_ij = min(x_ij, *uu + *vv+w((I), (J), (K)));
                        uu++;
                        K++;
                        vv = vv + B;
                    }
                    uu = x + in;
                    vv = V + j * vilen;
                    K = vi;
#pragma ivdep
                    
                    for (int k = 0; k <= j; k++) {
                        x_ij = min(x_ij, *uu + *vv+w((I), (J), (K)));
                        uu++;
                        K++;
                        //vv = vv + B;
                        vv++;
                    }
                    x[in + j] = x_ij;
                    in = in + B;
                }
            }
#ifdef USE_PAPI
            countMisses(id );
#endif
            return;
        } else {
            // Recursive case
            long long nn = (xilen >> 1);
            long long nn2 = nn * nn;
            const long long m11 = 0;
            long long m12 = m11 + nn2;
            long long m21 = m12 + nn2;
            long long m22 = m21 + nn2;
            
            funcB_S(x + m21, u + m22, v + m11, nn, xi + nn, xj, uj + nn, vi);
            
            cilk_spawn funcC_S(x + m11, u + m12, x + m21, nn, xi, xj, uj + nn,
                               xi + nn);
            funcC_S(x + m22, x + m21, v + m12, nn, xi + nn, xj + nn, xj, vi);
            cilk_sync;
            
            cilk_spawn funcB_S(x + m11, u + m11, v + m11, nn, xi, xj, uj, vi);
            funcB_S(x + m22, u + m22, v + m22, nn, xi + nn, xj + nn, uj + nn,
                    vi + nn);
            cilk_sync;
            funcC_S(x + m12, u + m12, x + m22, nn, xi, xj + nn, uj + nn,
                    xi + nn);
            funcC_S(x + m12, x + m11, v + m12, nn, xi, xj + nn, xj, vi);
            funcB_S(x + m12, u + m11, v + m22, nn, xi, xj + nn, uj, vi + nn);
        }
        
    } else {
        // Otherwise, if all of them are not of the same size
        // Base case
        if (xilen <= B && xjlen <= B) {
#ifdef USE_PAPI
            int id = tid();
            int retval = 0;
            papi_for_thread(id);
            if ( (retval=PAPI_start(EventSet[id])) != PAPI_OK)
                ERROR_RETURN(retval);
#endif
            register int I, J, K;
            TYPE *uu, *vv, *xx;
            {
                //#pragma parallel
                
                __declspec(align(64)) TYPE V[vilen * xjlen];
                
#pragma parallel
                for (int i = 0; i < vilen; i++) {
                    //int in = i*vilen;
#pragma ivdep
                    for (int j = 0; j < xjlen; j++) {
                        V[j * vilen + i] = v[i * xjlen + j];
                    }
                }
                for (int i = xilen - 1; i >= 0; i--) {
                    for (int j = 0; j < xjlen; j++) {
                        int x_ij = x[i * xjlen + j];
                        I = xi + i;
                        J = xj + j;
                        K = uj + i;
                        uu = u + i * ujlen + i;
#pragma ivdep
                        for (int k = i; k < ujlen; k++) {
                            x_ij = min(x_ij,
                                       *uu + x[k*xjlen+j]+ w((I), (J), (K)));
                            uu++;
                            K++;
                        }
                        K = vi;
                        uu = x + i * xjlen;
                        vv = V + j * vilen;
#pragma ivdep
                        for (int k = 0; k <= j; k++) {
                            
                            //x_ij = min (x_ij, *uu + v[k*xjlen+j]+ w((I), (J), (K)));
                            x_ij = min(x_ij, *uu + *vv+ w((I), (J), (K)));
                            uu++;
                            K++;
                            vv++;
                        }
                        x[i * xjlen + j] = x_ij;
                    }
                    
                }
                
            }
#ifdef USE_PAPI
            countMisses(id );
#endif
            return;
        }
        // recursive case.
        else {
            long long n = (xilen > xjlen) ? xilen : xjlen;
            long long c = 1;
            while (c < n)
                c = (c << 1);
            c = c >> 1;
            
            long long ni, nii, nj, njj;
            
            ni = min(c, xilen);
            nj = min(c, xjlen);
            nii = max(0, xilen - c);
            njj = max(0, xjlen - c);
            
            long long unj, unjj; //uni and unii are the same as ni and nii
            
            //uni = ni;
            unj = min(c, ujlen);
            //unii = nii;
            unjj = max(0, ujlen - c);
            
            //necessary values for V
            long long vni, vnii; //vnj and vnjj are the same as nj and njj
            
            vni = min(c, vilen);
            
            vnii = max(0, vilen - c);
            
            TYPE *x12, *x21, *x22, *u12, *u21, *u22, *v12, *v21, *v22;
            
            x12 = x + ni * nj;
            u12 = u + ni * unj;
            v12 = v + vni * nj;
            
            x21 = x12 + ni * njj;
            u21 = u12 + ni * unjj;
            v21 = v12 + vni * njj;
            
            x22 = x21 + nii * nj;
            u22 = u21 + nii * unj;
            v22 = v21 + vnii * nj;
            
            //if(nii>0 && nj>0 && unjj>0 && vni>0)
            funcB(x21, u22, v, nii, nj, unjj, vni, xi + ni, xj, uj + unj, vi);
            
            //if(ni>0 && nj>0 && unjj>0 && nii>0)
            cilk_spawn funcC(x, u12, x21, ni, nj, unjj, nii, xi, xj, uj + unj,
                             xi + ni);
            
            //if(nii>0 && njj>0 && nj>0 && vni>0)
            funcC(x22, x21, v12, nii, njj, nj, vni, xi + ni, xj + nj, xj, vi);
            cilk_sync;
            
            //if(ni > 0 && nj > 0 && unj>0 && vni>0)
            cilk_spawn funcB(x, u, v, ni, nj, unj, vni, xi, xj, uj, vi);
            
            //if(nii>0 && njj>0 && unjj>0 && vnii>0)
            funcB(x22, u22, v22, nii, njj, unjj, vnii, xi + ni, xj + nj,
                  uj + unj, vi + vni);
            cilk_sync;
            
            //if(ni>0 && njj>0 && unjj>0 && nii>0)
            funcC(x12, u12, x22, ni, njj, unjj, nii, xi, xj + nj, uj + unj,
                  xi + ni);
            
            //if(ni>0 && njj>0 && nj>0 && vni>0)
            funcC(x12, x, v12, ni, njj, nj, vni, xi, xj + nj, xj, vi);
            //if(ni>0 && njj>0 && unj>0 && vnii>0)
            funcB(x12, u, v22, ni, njj, unj, vnii, xi, xj + nj, uj, vi + vni);
        }
    }
}

/*
 Function A for Parenthesis problem recursive algorithm. x is output and input matrix. n is the size.
 Works for any n.
 xi, xj = top left corner of matrix x;
 xilen = length of row dimension for matrix x
 xjlen = length of column dimension for matrix x
 Pointers arithmatics are used to improve running time all around.
 */
void funcA( TYPE *x, int xilen, int xjlen, int xi, int xj) {
    if (xilen <= 0 || xjlen <= 0)
        return;
    
    // base case
    if (xilen <= B || xjlen <= B) {
#ifdef USE_PAPI
        int id = tid();
        int retval = 0;
        papi_for_thread(id);
        if ( (retval=PAPI_start(EventSet[id])) != PAPI_OK)
            ERROR_RETURN(retval);
#endif
        TYPE *u, *v;
        register int I, J, K;
        
        for (int t = 2; t < xilen; t++) {
            int in = 0;
            for (int i = 0; i < xilen - t; i++) {
                int j = t + i;
                
                int x_ij = x[in + j];
                
                I = xi + i;
                J = xj + j;
                u = x + in + i + 1;
                
                v = x + in + xjlen + j;
                K = xj + i + 1;
#pragma ivdep
                for (int k = i + 1; k <= j; k++) {
                    x_ij = min(x_ij, (*u + *v) + w((I), (J), (K)));
                    u++;
                    K++;
                    v = v + xjlen;
                }
                x[in + j] = x_ij;
                in = in + xjlen;
            }
        }
#ifdef USE_PAPI
        countMisses(id );
#endif
        return;
    } else {
        long long n = max(xilen, xjlen);
        long long c = 1;
        while (c < n)
            c = (c << 1);
        c = c >> 1;
        long long ni, nii, nj, njj;
        
        ni = min(c, xilen);
        nj = min(c, xjlen);
        nii = max(0, xilen - c);
        njj = max(0, xjlen - c);
        
        TYPE *x12, *x21, *x22;
        
        x12 = x + ni * nj;
        
        x21 = x12 + (ni * njj);
        
        x22 = x21 + (nii * nj);
        
        cilk_spawn funcA(x, ni, nj, xi, xj);
        
        funcA(x22, nii, njj, xi + ni, xj + nj);
        cilk_sync;
        
        funcB(x12, x, x22, ni, njj, nj, nii, xi, xj + nj, xj, xi + ni);
        
    }
    
}

int main(int argc, char *argv[]) {
    N = 0;
    B = 0;
    
    if (argc > 1)
        N = atoi(argv[1]);
    if (argc > 2)
        B = atoi(argv[2]);
    
    if (argc > 3) {
        cout<<"Worker count changed"<<endl; 
        if (0!= __cilkrts_set_param("nworkers",argv[3])) {
            cout<<"Failed to set worker count\n";
            return 1;
        }
    }		
    cout<< "p= "<<__cilkrts_get_nworkers()<<endl;
    
    long long NN = 2;
    NP = N;
    
    // Find the powers of 2 >=N.
    while (NN < N)
        NN = NN << 1;
    
#ifdef USE_PAPI
    papi_init();
#endif
    
    // Allocate for Recursive algo
#ifdef CO
    dist = ( TYPE * ) _mm_malloc( N * N * sizeof( TYPE ), ALIGNMENT );
    X = ( TYPE * ) _mm_malloc( N * N * sizeof( TYPE ), ALIGNMENT );
    
    if ( ( dist == NULL ) || ( X == NULL ) )
    {
        printf( "\nError: Allocation failed!\n\n" );
        
        if ( dist != NULL ) _mm_free( dist );
        if ( X != NULL ) _mm_free( X );
        
        exit( 1 );
    }
#endif
    
    // Allocate for iterative algo
#ifdef LOOPDP
    if(NN==N) NP=N+1; //padding
    D = (TYPE *) _mm_malloc( NP * NP * sizeof( TYPE ), ALIGNMENT );
#endif
    
    srand (time(NULL) );
    
    //initialize the input
    int 	inf = int(1e9);
    
     // Setup initial values.
    for (int i = 0; i < N; i++)
        for (int j = 0; j < N; j++) {
            if (j != (i + 1)) {
#ifdef CO
                dist[ i * N + j ] = inf;
#endif
#ifdef LOOPDP
                D[i*NP+j] = inf;
#endif
            } else {
#ifdef CO
                dist[ i * N +j ] = (i+1);
#endif
#ifdef LOOPDP
                D[i*NP+j] = (i+1);
#endif
            }
        }
    
#ifdef CO
    X[ 0:(N*N) ] = 0;
    // Convert row major to z-morton row major
    conv_RM_2_ZM_RM( X, dist, 0, 0, N, N );
#endif
    
#ifdef LOOPDP
    unsigned long long tstart = cilk_getticks();
    parenthesis(N);
    unsigned long long tend = cilk_getticks();
    cout<<N<<","<<cilk_ticks_to_seconds(tend-tstart);
#endif
    
#ifdef CO
    // If N is power of 2, call function that was written for power of 2
    if(NN==N)
    {
        
        unsigned long long tstart = cilk_getticks();
        funcA_S ( X, N, 0, 0 );
        unsigned long long tend = cilk_getticks();
        
        cout<<"CO,"<<N<<","<<cilk_ticks_to_seconds(tend-tstart);
    }
    else
    {
        unsigned long long tstart = cilk_getticks();
        funcA ( X, N, N, 0, 0 );
        unsigned long long tend = cilk_getticks();
        
        cout<<"CO,"<<N<<","<<cilk_ticks_to_seconds(tend-tstart);
    }
    // Convert from Z morton to row major back.
    conv_ZM_2_RM_RM( X, dist, 0, 0, N, N );
    
#endif
    
#ifdef pdebug
    cout<<"Results from loop DP"<<endl;
    for ( int i = 0; i < N; i++ ) {
        for(int j =i+1; j< N; j++)
        {
            cout<<D[ i*NP+j ]<<" ";
        }
        cout<<"\n";
    }
    
    cout<<"Results from CO"<<endl;
    for(int i=0;i<N;i++) {
        for(int j=i+1;j<N;j++)
        {
            cout<<dist[i*N+j]<<" ";
            
        }
        cout<<endl;
    }
    
#endif
    
#ifdef LOOPDP
#ifdef CO
    for(int i=0;i<N;i++)
    {
        for(int j=0;j<N;j++)
        {
            assert(D[i*NP+j]==dist[i*N+j]);
            
        }
    }
    
#endif
    _mm_free(D);
#endif
    
#ifdef USE_PAPI
    cout<<",";
    countTotalMiss(p);
    cout<<endl;
    papi_end();
#endif
    return 0;
}
