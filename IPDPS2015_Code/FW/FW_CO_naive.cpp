//@Copyright: JesMIN Jahan Tithi, Rezaul Chowdhury, Department of Computer Science, Stony Brook University, Ny-11790
//Contact: jtithi@cs.stonybrook.edu, 

//Aakrati Talati : Modified to accept any N and any Basecase (Row Major layout)

//Optimized: JesMIN Jahan Tithi, Date: Dec 20, 2013

//compile with :icpc -O3 -AVX  -xhost -o  fwr FW_rec.cpp  -ansi-alias -ip -opt-subscript-in-range -opt-prefetch=4 -fomit-frame-pointer -funroll-all-loops -vec-report  -parallel -restrict

#include <time.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/timeb.h>
#include <iostream>
#include <pthread.h>
#include <cilk/cilk.h>
#include <cilk/cilk_api.h>
#include <math.h>
#include "cilktime.h"
using namespace std;

#ifdef USE_PAPI
#include "papilib.h"
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

int N, B, NP, NPDQ;
TYPE *dist, *X, *D;

#define MIN(a, b) (a<b?a:b)
#define MAX(a, b) (a>b?a:b)


void funcD( TYPE *x, TYPE *u, TYPE *v, int n, int xi, int xj, int uj) {
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

		// Copy Optimization.
		__declspec(align(64)) TYPE V[endu * endj];
#pragma parallel
		for (int i = 0; i < endu; i++) {
#pragma ivdep
			for (int j = 0; j < endj; j++) {
				V[j * endu + i] = v[i * endj + j];
			}
		}
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

void funcB( TYPE *x, TYPE *u, TYPE *v, int n, int xi, int xj, int uj) {
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

void funcA( TYPE *x, TYPE *u, TYPE *v, int n, int xi, int xj, int uj) {
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
	N = 0;
	B = 0;
	if (argc > 1)
		N = atoi(argv[1]);
	if (argc > 2)
		B = atoi(argv[2]);

	NP = NPDQ = N;
	int NN = 2;

	while (NN < N)
		NN = NN << 1;

#ifdef USE_PAPI
	papi_init();
#ifdef LOOPDP
	long long int dpmiss[NUM_EVENTS]= {0};
#endif
#endif

	if (B > N)
		B = N;
#ifdef CO
	X = ( TYPE * ) _mm_malloc( NPDQ * NPDQ * sizeof( TYPE ), ALIGNMENT );
#endif

#ifdef LOOPDP
	D = (TYPE *) _mm_malloc( NP * NP * sizeof( TYPE ), ALIGNMENT );
#endif

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
	unsigned long long tstart, tend;
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
#ifdef USE_PAPI
			int rval;
			papi_for_thread(0);
			if (rval=PAPI_start(EventSet[0]) != PAPI_OK) ERROR_RETURN(rval);
#endif
			FloydWarshall(N);
			tend = cilk_getticks();

			cout<<"LOOPDP,"<<N<<","<<cilk_ticks_to_seconds(tend-tstart);
#ifdef USE_PAPI
			if (rval=PAPI_stop(EventSet[0], dpmiss) != PAPI_OK) ERROR_RETURN(rval);
			cout<<","<<dpmiss[0]<<","<<dpmiss[1]<<endl;
#endif

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
