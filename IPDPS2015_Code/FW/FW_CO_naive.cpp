//@Copyright: Jesmin Jahan Tithi, Rezaul Chowdhury, Department of Computer Science, Stony Brook University, Ny-11790
//Contact: jtithi@cs.stonybrook.edu,

//Aakrati Talati : Modified to accept any N and any Basecase (Row Major layout)

//Optimized: Jesmin Jahan Tithi, Date: Dec 20, 2013

/*
 This program implements recursive divide and conquer algorithms for the FW all pairs shortest path.
 This program works for any n.
 When running the program, it takes input size, base case, number of cores as input.
 
 If you want you can compile only the standard iterative version by compiling with Flag -DLOOPDP.
 Or you can only compile the recursive version by compiling it with -DCO.
 
 If you use both -DLOOPDP and -DCO at the same time, it will automatically test the resultant matrices for correctness.
 
 You can see the actual values stored in the matrices, use -Dpdebug during compilation.
 
 compile with :icpc -O3 -AVX  -xhost -o  fwr FW_COZ.cpp  -ansi-alias -ip -opt-subscript-in-range -opt-prefetch=4 -fomit-frame-pointer -funroll-all-loops -vec-report  -parallel -restrict
 
 However, these parameters are not guaranteed to give the best running times. You may need to check several of them.
 
 
 */

#include <stdio.h>
#include <stdlib.h>
#include <iostream>
#include <cilk/cilk.h>
#include <cilk/cilk_api.h>
#include <math.h>
#include "cilktime.h" // Timing library.

using namespace std;


#ifdef USE_PAPI
#include "papilib.h"  // Papi library.
#endif

#ifdef ENERGY
#include "energylib.h"
#endif

#ifndef TYPE
#define TYPE int
#endif

#ifndef ALIGNMENT
#define ALIGNMENT 64
#endif


/*
 N = matrix dimension.
 NP = matrix dimension after padding (if needed) for LOOPDP. Padding is required to reduce set associative cache miss.
 NPDQ = matrix dimension after padding (if needed) for Iterative. Padding is required to reduce set associative cache miss.
 B = base-case size or switching point to iterative algorithm.
 
 X the initial matrix for recursive.
 D is used for iterative/LOOPDP computation.
 
 Pointers are used to improve running time for all the basecase kernels. In the basecases. Pointer xx used to point to x, uu used to point to u and vv used to point to v.
 
 */
int N, B, NP, NPDQ;
TYPE  *X, *D;

#define MIN(a, b) (a<b?a:b)
#define MAX(a, b) (a>b?a:b)



/*
 Function D for FW_APSP Algo. X is output, U and V are inputs. n is the size.
 xi, xj = index of the top-left corner of x.
 xi, uj = index of the top left corner of u.
 and
 uj, xj = index of the top left corner of v
 Pointers arithmatics are used to improve running time all around.
 */
void funcD( TYPE *x, TYPE *u, TYPE *v, int n, int xi, int xj, int uj) {
    if (xi >= N || xj >= N || uj >= N)
        return;
    
    //basecase
    if (n <= B) {
        
#ifdef USE_PAPI
        //Starts papi counter
        int id = tid();
        int retval = 0;
        papi_for_thread(id);
        if ( (retval=PAPI_start(EventSet[id])) != PAPI_OK)
            ERROR_RETURN(retval);
#endif
        //Finds actual size where there is any valid data.
        int endi = (xi + n >= N) ? (N - xi) : n;
        int endj = (xj + n >= N) ? (N - xj) : n;
        int endu = (uj + n >= N) ? (N - uj) : n;
        
        // Copy Optimization.
        __declspec(align(64)) TYPE V[endu * endj];
#pragma parallel
        for (int i = 0; i < endu; i++) {
#pragma ivdep
            for (int j = 0; j < endj; j++) {
                V[j * endu + i] = v[i * endj + j];
            }
        }
        //Actual basecase execution
#pragma parallel
        for (int i = 0; i < endi; i++) {
            for (int j = 0; j < endj; j++) {
                TYPE x_ij = x[i*NPDQ + j];
#pragma ivdep
                for (int k = 0; k < endu; k++) {
                    x_ij = MIN(x_ij, (u[i*NPDQ+k] + V[j*endu+k]));
                }
                x[i*NPDQ + j] = x_ij;
            }
        }
#ifdef USE_PAPI
        //Stops papi counters.
        countMisses(id );
#endif
        return;
        
    } else {
        
        // Recursive case.
        int nn = (n >> 1);
        
        int nn2 = nn * nn;
        
        const int m11 = 0;
        int m12 = m11 + nn;
        int m21 = nn * NPDQ;
        int m22 = m21 + nn;
        
        cilk_spawn funcD(x + m11, u + m11, v + m11, nn, xi, xj, uj);
        cilk_spawn funcD(x + m12, u + m11, v + m12, nn, xi, xj + nn, uj);
        cilk_spawn funcD(x + m21, u + m21, v + m11, nn, xi + nn, xj, uj);
        funcD(x + m22, u + m21, v + m12, nn, xi + nn, xj + nn, uj);
        
        cilk_sync;
        
        cilk_spawn funcD(x + m11, u + m12, v + m21, nn, xi, xj, uj + nn);
        cilk_spawn funcD(x + m12, u + m12, v + m22, nn, xi, xj + nn, uj + nn);
        cilk_spawn funcD(x + m21, u + m22, v + m21, nn, xi + nn, xj, uj + nn);
        funcD(x + m22, u + m22, v + m22, nn, xi + nn, xj + nn, uj + nn);
        
        cilk_sync;
    }
}

/*
 Function C for FW_APSP Algo. X is output, U and V are inputs. n is the size.
 xi, xj = index of the top-left corner of x.
 xi, uj = index of the top left corner of u.
 and
 uj, xj = index of the top left corner of v
 Pointers arithmatics are used to improve running time all around.
 */
void funcC( TYPE *x, TYPE *u, TYPE *v, int n, int xi, int xj, int uj) {
    if (xi >= N || xj >= N || uj >= N)
        return;
    
    if (n <= B) {
#ifdef USE_PAPI
        int id = tid();
        int retval = 0;
        papi_for_thread(id);
        if ( (retval=PAPI_start(EventSet[id])) != PAPI_OK)
            ERROR_RETURN(retval);
#endif
        int endi = (xi + n >= N) ? (N - xi) : n;
        int endj = (xj + n >= N) ? (N - xj) : n;
        int endu = (uj + n >= N) ? (N - uj) : n;
        
        for (int k = 0; k < endu; k++) {
#pragma parallel
            for (int i = 0; i < endi; i++) {
#pragma ivdep
                for (int j = 0; j < endj; j++) {
                    x[i*NPDQ+j] = MIN((u[i*NPDQ+k]) + (v[k*NP+j]), x[i*NPDQ+j]);
                }
            }
        }
#ifdef USE_PAPI
        countMisses(id );
#endif
        return;
    } else {
        int nn = (n >> 1);
        int nn2 = nn * nn;
        
        const int m11 = 0;
        int m12 = m11 + nn;
        int m21 = nn * NPDQ;
        int m22 = m21 + nn;
        
        cilk_spawn funcC(x + m11, u + m11, v + m11, nn, xi, xj, uj);
        funcC(x + m21, u + m21, v + m11, nn, xi + nn, xj, uj);
        cilk_sync;
        cilk_spawn funcD(x + m12, u + m11, v + m12, nn, xi, xj + nn, uj);
        funcD(x + m22, u + m21, v + m12, nn, xi + nn, xj + nn, uj);
        cilk_sync;
        
        cilk_spawn funcC(x + m12, u + m12, v + m22, nn, xi, xj + nn, uj + nn);
        funcC(x + m22, u + m22, v + m22, nn, xi + nn, xj + nn, uj + nn);
        cilk_sync;
        
        cilk_spawn funcD(x + m11, u + m12, v + m21, nn, xi, xj, uj + nn);
        funcD(x + m21, u + m22, v + m21, nn, xi + nn, xj, uj + nn);
        cilk_sync;
    }
}

/*
 Function B for FW_APSP Algo. X is output, U and V are inputs. n is the size.
 xi, xj = index of the top-left corner of x.
 xi, uj = index of the top left corner of u.
 and
 uj, xj = index of the top left corner of v
 Pointers arithmatics are used to improve running time all around.
 */
void funcB( TYPE *x, TYPE *u, TYPE *v, int n, int xi, int xj, int uj) {
    if (xi >= N || xj >= N || uj >= N)
        return;
    // Basecase
    if (n <= B) {
#ifdef USE_PAPI
        int id = tid();
        int retval = 0;
        papi_for_thread(id);
        if ( (retval=PAPI_start(EventSet[id])) != PAPI_OK)
            ERROR_RETURN(retval);
#endif
        
        int endi = (xi + n >= N) ? (N - xi) : n;
        int endj = (xj + n >= N) ? (N - xj) : n;
        int endu = (uj + n >= N) ? (N - uj) : n;
        
        for (int k = 0; k < endu; k++) {
#pragma parallel
            for (int i = 0; i < endi; i++) {
#pragma ivdep
                for (int j = 0; j < endj; j++) {
                    x[i*NPDQ+j] = MIN(x[i*NPDQ+j], (u[i*NPDQ+k]) + (v[k*NP+j]));
                }
            }
        }
#ifdef USE_PAPI
        countMisses(id );
#endif
        return;
    } else {
        int nn = (n >> 1);
        int nn2 = nn * nn;
        
        const int m11 = 0;
        int m12 = m11 + nn;
        int m21 = nn * NPDQ;
        int m22 = m21 + nn;
        
        cilk_spawn funcB(x + m11, u + m11, v + m11, nn, xi, xj, uj);
        funcB(x + m12, u + m11, v + m12, nn, xi, xj + nn, uj);
        cilk_sync;
        
        cilk_spawn funcD(x + m21, u + m21, v + m11, nn, xi + nn, xj, uj);
        funcD(x + m22, u + m21, v + m12, nn, xi + nn, xj + nn, uj);
        cilk_sync;
        
        cilk_spawn funcB(x + m21, u + m22, v + m21, nn, xi + nn, xj, uj + nn);
        funcB(x + m22, u + m22, v + m22, nn, xi + nn, xj + nn, uj + nn);
        cilk_sync;
        cilk_spawn funcD(x + m11, u + m12, v + m21, nn, xi, xj, uj + nn);
        funcD(x + m12, u + m12, v + m22, nn, xi, xj + nn, uj + nn);
        cilk_sync;
    }
}

/*
 Function A for FW_APSP Algo. X is output, U and V are inputs. n is the size.
 xi, xj = index of the top-left corner of x.
 xi, uj = index of the top left corner of u.
 and
 uj, xj = index of the top left corner of v
 Pointers arithmatics are used to improve running time all around.
 */
void funcA( TYPE *x, TYPE *u, TYPE *v, int n, int xi, int xj, int uj) {
    if (xi >= N || xj >= N || uj >= N)
        return;
    //basecase
    if (n <= B) {
        //Start PAPI counter
#ifdef USE_PAPI
        int id = tid();
        int retval = 0;
        papi_for_thread(id);
        if ( (retval=PAPI_start(EventSet[id])) != PAPI_OK)
            ERROR_RETURN(retval);
#endif
        
        int endi = (xi + n >= N) ? (N - xi) : n;
        int endj = (xj + n >= N) ? (N - xj) : n;
        int endu = (uj + n >= N) ? (N - uj) : n;
        
        for (int k = 0; k < endu; k++) {
#pragma parallel
            for (int i = 0; i < endi; i++) {
#pragma ivdep
                for (int j = 0; j < endj; j++) {
                    x[i*NPDQ+j] = MIN(x[i*NPDQ+j], (u[i*NPDQ+k]) + (v[k*NP+j]));
                    
                }
            }
        }
#ifdef USE_PAPI
        countMisses(id );
#endif
        return;
        
    } else {
        int nn = (n >> 1);
        int nn2 = nn * nn;
        
        const int m11 = 0;
        int m12 = m11 + nn;
        int m21 = nn * NPDQ;
        int m22 = m21 + nn;
        
        funcA(x + m11, u + m11, v + m11, nn, xi, xj, uj);
        
        cilk_spawn funcB(x + m12, u + m11, v + m12, nn, xi, xj + nn, uj);
        funcC(x + m21, u + m21, v + m11, nn, xi + nn, xj, uj);
        cilk_sync;
        
        funcD(x + m22, u + m21, v + m12, nn, xi + nn, xj + nn, uj);
        
        funcA(x + m22, u + m22, v + m22, nn, xi + nn, xj + nn, uj + nn);
        cilk_spawn funcB(x + m21, u + m22, v + m21, nn, xi + nn, xj, uj + nn);
        funcC(x + m12, u + m12, v + m22, nn, xi, xj + nn, uj + nn);
        cilk_sync;
        funcD(x + m11, u + m12, v + m21, nn, xi, xj, uj + nn);
    }
}

#ifdef LOOPDP
/*
 Iterative implementation. Just for verifications. Not optimized.
 */
void FloydWarshall( int n)
{
    
    for(int k=0;k<n;k++)
    {
        cilk_for(int i=0;i<n;i++)
        {
            int in = i*NP;
#pragma ivdep
            for(int j=0;j<n;j++)
            {
                {
                    D[in+j] = MIN(D[in+j],D[in+k]+D[k*NP+j]);
                }
                
            }
        }
    }
}
#endif

int main(int argc, char *argv[]) {
    N = 1;
    B = 1;
    
    // Takes N, B and Number of threads.
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
    NP = NPDQ = N;
    int NN = 2;
    // Find the powers of 2 >=N.
    while (NN < N)
        NN = NN << 1;
    
#ifdef USE_PAPI
    //initialize papi counter
    papi_init();
#endif
    
    if (B > N)
        B = N;
    
    // Allocate for Recursive algo
#ifdef CO
    X = ( TYPE * ) _mm_malloc( NPDQ * NPDQ * sizeof( TYPE ), ALIGNMENT );
#endif
    // Allocate for iterative algo
#ifdef LOOPDP
    D = (TYPE *) _mm_malloc( NP * NP * sizeof( TYPE ), ALIGNMENT );
#endif
    // Setup initial values.
    cilk_for(int i = 0; i < N;
             i++
             )
    {
        cilk_for(int j = 0; j< N; j++ )
        {
            
            if( i == j )
            {
#ifdef CO
                X[i*NPDQ+j] = 0;
#endif
#ifdef LOOPDP
                D[i*NP+j]=0;
#endif
            }
            else
            {
#ifdef CO
                X[i*NPDQ+j]=abs( (j-i)%4 + 1 ) % 1;
#endif
#ifdef LOOPDP
                D[i*NP+j]=abs( (j-i)%4 + 1 ) % 1;;
#endif
            }
        }
    }
    
    // Recursive divide and conquer
    unsigned long long tstart, tend;
    
    // Energy library
#ifdef ENERGY
    energy_lib_init();
#endif
    
#ifdef CO
#ifdef ENERGY
    start_energy_measurement();
#endif
    
    tstart = cilk_getticks();
    
    funcA(X, X, X, NN,0,0,0);
    
    tend = cilk_getticks();
    cout<<"CO,"<<N<<","<<cilk_ticks_to_seconds(tend-tstart)<<",";
    
#ifdef ENERGY
    stop_energy_measurement();
#endif
    
#ifdef pdebug
    cout<<"loop version\n";
    for(int i=0;i<N;i++) {
        for(int j=0;j<N;j++) {
            cout<<D[i*NP+j]<<" ";
        }
        cout<<"\n";
    }
#endif
#endif
#ifdef LOOPDP
    
    tstart = cilk_getticks();
    FloydWarshall(N);
    tend = cilk_getticks();
    cout<<"LOOPDP,"<<N<<","<<cilk_ticks_to_seconds(tend-tstart);
    
#ifdef pdebug
    cout<<"recursive version\n";
    for(int i=0;i<N;i++) {
        for(int j=0;j<N;j++) {
            cout<<X[i*NPDQ+j]<<" ";
        }
        cout<<"\n";
    }
#endif
    
#ifdef CO
    cout<<",";
    for(int i = 0; i <N; i++ )
    {
        for(int j = 0; j<N;j++ )	//
        {
            if(D[i*NP+j]!=X[i*NPDQ+j])
            {
                cout<<"Wrong at"<<i<<j<<endl;
                break;
            }
            
        }
    }
#endif
    _mm_free(D);
    
#endif
    
    //cout<<endl;
    
#ifdef CO
    _mm_free(X);
#endif
    
#ifdef USE_PAPI
#ifdef CO
    countTotalMiss(p);
#endif
    PAPI_shutdown();
    
#endif
 			cout<<endl;
    
#ifdef ENERGY
    clear_energy_measurement();
#endif
    return 0;
}
