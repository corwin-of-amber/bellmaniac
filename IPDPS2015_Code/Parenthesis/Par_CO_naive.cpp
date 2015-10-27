//@Copyright: Jesmin Jahan Tithi,  Rezaul Chowdhury, Department of Computer Science, Stony Brook University, Ny-11790
//Contact: jtithi@cs.stonybrook.edu,

/*compile with :icc -O3 -o parCOZ Par_COZ.cpp -DCO -xhost  -ansi-alias -ip -opt-subscript-in-range -opt-prefetch=4 -fomit-frame-pointer
 -funroll-all-loops -vec-report  -parallel -restrict*/

/*
 This program implements recursive divide and conquer algorithms for the Parenthesis Problem.
 It uses row major lay out to store the data. This program works for any n.
 When running the program, it takes input size, base case, number of cores as input.
 
 If you want you can compile only the standard iterative version by compiling with Flag -DLOOPDP.
 Or you can only compile the recursive version by compiling it with -DCO.
 
 If you use both -DLOOPDP and -DCO at the same time, it will automatically test the resultant matrices for correctness.
 
 You can see the actual values stored in the matrices, use -Dpdebug during compilation.
 
 To get cache misses, compile with -DUSE_PAPI -lpapi -I/path to papi include -L/path to papi lib
 
 compile with :icpc -O3 -AVX  -xhost -o  fwr FW_COZ.cpp  -ansi-alias -ip -opt-subscript-in-range -opt-prefetch=4 -fomit-frame-pointer -funroll-all-loops -vec-report  -parallel -restrict
 
 However, these parameters are not guaranteed to give the best running times. You may need to check several of them.
 */

#include <stdio.h>
#include <stdlib.h>
#include <iostream>
#include <cilk/cilk.h>
#include <cilk/cilk_api.h>
#include <math.h>
#include "cilktime.h"
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


/*
 dist is the initial matrix for recursive.
 X is used to store the Z morton conversion of dist and then used for the actual computation.
 D is used for iterative/LOOPDP computation.
 Pointers are used to improve running time for all the basecase kernels. In the basecases. Pointer xx used to point to x, uu used to point to u and vv used to point to v.
 
 N = matrix dimension.
 NP = matrix dimension after padding (if needed) for LOOPDP. Padding is required to reduce set associative cache miss.
 NPDQ = matrix dimension after padding (if needed) for Recursive. Padding is required to reduce set associative cache miss.
 B = base-case size or switching point to iterative algorithm.
 */
long long N, NPDQ, NP;
int B;
TYPE *dist, *X;

/* Min Max and Weight Function */
#define min(a,b) (a<b?a:b)
#define max(a,b) (a>b?a:b)
#define w(i, j, k) (((i*j*k)&7)) //weight function

/* Parallel LOOPDP/Iterative function for parenthesis problem. Follows directly for the standard algorithm, except it uses pointer arithmatics for improved running times.
 It solves the cells in diagonal by diagonal manner.
 */
#ifdef LOOPDP
TYPE* D;
void parenthesis( long long n ) {
    for(int t = 2; t <n; t++) {
        cilk_for(int i = 0; i< n-t; i++ )
        {
            int j = t+i;
            int D_ij = D[i*NP+j];
            TYPE *uu=D+i*NP+i+1;
            TYPE *vv=D+(i+1)*NP+j;
#pragma ivdep
            for(int k = i+1; k<=j; k++)
            {
                D_ij = min (D_ij, *uu + *vv + w(i,j,k));
                uu++;
                vv = vv + NP;
            }
            D[i*NP+j] = D_ij;
            
        }
    }
    
    return;
}
#endif



/*
 Function C for Parenthesis problem recursive algorithm. x is output, u and v are inputs. n is the size.
 Works for any n.
 xi, xj = top left corner of matrix x;
 xi, uj = top left corner for u.
 vi, xj = top left corner for v.
 Pointers arithmatics are used to improve running time all around.
 */

void funcC( TYPE *x, TYPE *u, TYPE *v, long long n, int xi, int xj, int uj,
           int vi) {
    //if indices are outside the range, return.
    if (xi >= N || xj >= N || uj >= N || vi >= N)
        return;
    //basecase
    if (n <= B) {
#ifdef USE_PAPI
        //start papi counters.
        int id = tid();
        int retval = 0;
        papi_for_thread(id);
        if ( (retval=PAPI_start(EventSet[id])) != PAPI_OK)
            ERROR_RETURN(retval);
#endif
        register int I, J, K;
        
        //find range with valid data
        int endi = (xi + n >= N) ? (N - xi) : n;
        int endj = (xj + n >= N) ? (N - xj) : n;
        int endu = (uj + n >= N) ? (N - uj) : n;
        
        TYPE *uu, *vv;
        
        // Copy optimization
        __declspec(align(64)) TYPE V[n * n];
        for (int i = 0; i < n; i++) {
#pragma ivdep
            for (int j = 0; j < n; j++) {
                V[i * n + j] = v[(j) * NPDQ + (i)];
                
            }
            
        }
        
        register int in = 0;
        for (int i = 0; i < endi; i++) {
            
            TYPE *xx = x + in;
            for (int j = 0; j < endj; j++) {
                //TYPE x_ij = x[in+j];
                TYPE x_ij = *xx;
                
                I = xi + i;
                J = xj + j;
                uu = u + in;
                vv = &V[j * n];
                K = uj;
#pragma ivdep
                for (int k = 0; k < endu; k++) {
                    x_ij = min(x_ij, (*uu + *vv + w((I), (J), (K))));
                    K++;
                    uu++;
                    vv++;
                }
                *xx = x_ij;
                xx++;
            }
            in = in + NPDQ;
        }
        
#ifdef USE_PAPI
        //stops papi cpunter
        countMisses(id );
#endif
        return;
    } else {
        //recursive case
        long long nn = (n >> 1);
        const long long m11 = 0;
        long long m12 = m11 + nn;
        long long m21 = nn * NPDQ;
        long long m22 = m21 + nn;
        
        cilk_spawn funcC(x + m11, u + m11, v + m11, nn, xi, xj, uj, vi);
        cilk_spawn funcC(x + m12, u + m11, v + m12, nn, xi, xj + nn, uj, vi);
        cilk_spawn funcC(x + m21, u + m21, v + m11, nn, xi + nn, xj, uj, vi);
        funcC(x + m22, u + m21, v + m12, nn, xi + nn, xj + nn, uj, vi);
        cilk_sync;
        
        cilk_spawn funcC(x + m11, u + m12, v + m21, nn, xi, xj, uj + nn,
                         vi + nn);
        cilk_spawn funcC(x + m12, u + m12, v + m22, nn, xi, xj + nn, uj + nn,
                         vi + nn);
        cilk_spawn funcC(x + m21, u + m22, v + m21, nn, xi + nn, xj, uj + nn,
                         vi + nn);
        funcC(x + m22, u + m22, v + m22, nn, xi + nn, xj + nn, uj + nn,
              vi + nn);
        
        cilk_sync;
    }
}

/*
 Function B for Parenthesis problem recursive algorithm. x is output, u and v are inputs. n is the size.
 Works for any n.
 xi, xj = top left corner of matrix x;
 xi, uj = top left corner for u.
 vi, xj = top left corner for v.
 Pointers arithmatics are used to improve running time all around.
 */
void funcB( TYPE *x, TYPE *u, TYPE *v, long long n, int xi, int xj, int uj,
           int vi) {
    // outside the range, return.
    if (xi >= N || xj >= N || uj >= N || vi >= N)
        return;
    
    //basecase
    
    if (n <= B) {
        
#ifdef USE_PAPI
        //papi counter start
        int id = tid();
        int retval = 0;
        papi_for_thread(id);
        if ( (retval=PAPI_start(EventSet[id])) != PAPI_OK)
            ERROR_RETURN(retval);
#endif
        
        TYPE *uu, *vv;
        register int I, J, K;
        
        // finds actual end with the valid data
        int endi = (xi + n >= N) ? (N - xi) : n;
        int endj = (xj + n >= N) ? (N - xj) : n;
        int endu = (uj + n >= N) ? (N - uj) : n;
        
        // base case code
        int in = 0;
        for (int i = endi - 1; i >= 0; i--) {
            in = i * NPDQ;
            for (int j = 0; j < endj; j++) {
                int x_ij = x[in + j];
                I = xi + i;
                J = xj + j;
                K = uj + i;
                uu = u + in + i;
#pragma ivdep
                for (int k = i; k < endu; k++) {
                    
                    x_ij = min(x_ij, *uu + x[k*NPDQ+j]+ w((I), (J), (K)));
                    K++;
                    uu++;
                }
                K = vi;
                uu = x + in;
#pragma ivdep
                for (int k = 0; k <= j; k++) {
                    
                    x_ij = min(x_ij, *uu + v[k*NPDQ+j]+ w((I), (J), (K)));
                    K++;
                    uu++;
                }
                x[in + j] = x_ij;
            }
            
        }
#ifdef USE_PAPI
        //end papi counter
        countMisses(id );
#endif
        return;
    } else {
        
        //recursive case
        long long nn = (n >> 1);
        const long long m11 = 0;
        long long m12 = m11 + nn;
        long long m21 = nn * NPDQ;
        long long m22 = m21 + nn;
        funcB(x + m21, u + m22, v + m11, nn, xi + nn, xj, uj + nn, vi);
        
        cilk_spawn funcC(x + m11, u + m12, x + m21, nn, xi, xj, uj + nn,
                         xi + nn);
        funcC(x + m22, x + m21, v + m12, nn, xi + nn, xj + nn, xj, vi);
        cilk_sync;
        
        cilk_spawn funcB(x + m11, u + m11, v + m11, nn, xi, xj, uj, vi);
        funcB(x + m22, u + m22, v + m22, nn, xi + nn, xj + nn, uj + nn,
              vi + nn);
        cilk_sync;
        funcC(x + m12, u + m12, x + m22, nn, xi, xj + nn, uj + nn, xi + nn);
        funcC(x + m12, x + m11, v + m12, nn, xi, xj + nn, xj, vi);
        funcB(x + m12, u + m11, v + m22, nn, xi, xj + nn, uj, vi + nn);
        
    }
}

/*
 Function A for Parenthesis problem recursive algorithm. x is output and input matrix. n is the size.
 Works for any n.
 xi, xj = top left corner of matrix x;
 Pointers arithmatics are used to improve running time all around.
 */

void funcA( TYPE * x, long long n, int xi, int xj) {
    
    // if outside the range return
    if (xi >= N || xj >= N)
        return;

    //basecase
    if (n <= B) {
        
#ifdef USE_PAPI
        // start papi counter
        int id = tid();
        int retval = 0;
        papi_for_thread(id);
        if ( (retval=PAPI_start(EventSet[id])) != PAPI_OK)
            ERROR_RETURN(retval);
#endif
        
        TYPE *u, *v;
        register int I, J, K;
        
        // finds actual end with valid data
        int endi = (xi + n >= N) ? (N - xi) : n;
        for (int t = 2; t < endi; t++) {
            
            int in = 0;
            
            for (int i = 0; i < endi - t; i++) {
                int j = t + i;
                
                int x_ij = x[in + j];
                
                I = xi + i;
                J = xj + j;
                u = x + in + i + 1;
                
                v = x + in + NPDQ + j;
                K = xj + i + 1;
#pragma ivdep
                for (int k = i + 1; k <= j; k++) {
                    x_ij = min(x_ij, (*u + *v) + w((I), (J), (K)));
                    u++;
                    K++;
                    v = v + NPDQ;
                }
                x[in + j] = x_ij;
                in = in + NPDQ;
            }
        }
#ifdef USE_PAPI
        //end papi counter
        countMisses(id );
#endif
        return;
    } else {
        
        //recursive case
        long long nn = (n >> 1);
        const long long m11 = 0;
        long long m12 = m11 + nn;
        long long m21 = nn * NPDQ;
        long long m22 = m21 + nn;
        cilk_spawn funcA(x + m11, nn, xi, xj);
        funcA(x + m22, nn, xi + nn, xj + nn);
        cilk_sync;
        
        funcB(x + m12, x + m11, x + m22, nn, xi, xj + nn, xj, xi + nn);
    }
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
            cout<<"Failed to set worker count\n";
            return 1;
        }
        cout<<"Worker count changed to "<< __cilkrts_get_nworkers() <<endl;
    }
    
    //printf( "N = %d , B = %d \n", N, B );
    //fflush( stdout );
    
#ifdef USE_PAPI
    papi_init();
#endif
    NP = NPDQ = N;
    long long NN = 2;
    
    // Find the powers of 2 >=N.
    while (NN < N)
        NN = NN << 1;
    
   if (B > NN) {
        B = NN ;
    }
    
    if (NN == N)
        NP = N + 1; //padding
    
    // Allocate for Recursive algo
    X = ( TYPE *) _mm_malloc(NPDQ * NPDQ * sizeof( TYPE ), ALIGNMENT);
    
    // Allocate for Iterative algo
#ifdef LOOPDP
    D = (TYPE *) _mm_malloc( NP * NP * sizeof( TYPE ), ALIGNMENT );
#endif
    
    if ((X == NULL)) {
        printf("\nError: Allocation failed!\n\n");
        if (X != NULL)
            _mm_free(X);
        
        exit(1);
    }
    
    // Setup initial values.
    int inf = int(1e9);
    //TYPE inf = (TYPE)(N*N);
    for (int i = 0; i < N; i++)
        for (int j = 0; j < N; j++) {
            if (j != (i + 1)) {
#ifdef CO
                X[ i * NPDQ + j ] = inf;
#endif
#ifdef LOOPDP
                D[i*NP+j] = inf;
#endif
            } else {
#ifdef CO
                X[ i * NPDQ +j ] = (i+1);
#endif
#ifdef LOOPDP
                D[i*NP+j] = (i+1);
#endif
            }
        }
    
    //iterative algorithm
#ifdef LOOPDP
    unsigned long long tstart1 = cilk_getticks();

    parenthesis(N);
    
    unsigned long long tend1 = cilk_getticks();
    cout<<N<<","<<cilk_ticks_to_seconds(tend1-tstart1);
    cout<<endl;
#endif
    
    //recursive algorithm
#ifdef CO
    unsigned long long tstart = cilk_getticks();
    
    funcA ( X, NN , 0, 0);
    
    unsigned long long tend = cilk_getticks();
    
    cout<<"CO,"<<N<<","<<cilk_ticks_to_seconds(tend-tstart);
    
#endif
#ifdef pdebug
    for(int i=0;i<N;i++)
    {
        for(int j=i;j<N;j++)
        {
            
            cout<<D[i*NP+j]<<" ";
            
        }
        cout<<endl;
        
    }
    cout<<endl;
    for(int i=0;i<N;i++)
    {
        for(int j=i;j<N;j++)
        {
            cout<<X[i*NPDQ+j]<<" ";
            
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
            assert(D[i*NP+j]==X[i*NPDQ+j]);
            
        }
    }
#endif
    _mm_free(D);
#endif
    _mm_free(X);
#ifdef USE_PAPI
#ifdef CO
    cout<<",";
    countTotalMiss(p);
    cout<<endl;
#endif
    papi_end();
#else
    cout << endl;
#endif
    return 0;
}
