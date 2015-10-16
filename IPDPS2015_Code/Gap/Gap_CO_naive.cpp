//@Copyright: Jesmin Jahan Tithi, Rezaul Chowdhury, Department of Computer Science, Stony Brook University, Ny-11790
//Contact: jtithi@cs.stonybrook.edu, 

//compile with :icpc -O3 -o gap Gap_DQ.cpp  -vec-report -parallel -xhost -AVX  -ansi-alias -restrict -ip -I$TACC_PAPI_INC -L$TACC_PAPI_LIB -DUSE_PAPI -lpapi  -lpfm -DUSEPAPI -DCO -DLOOPDP

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

#ifdef ENERGY
#include "energylib.h"
#endif
using namespace std;

#ifndef TYPE
#define TYPE int
#endif

#ifndef ALIGNMENT
#define ALIGNMENT 64
#endif

int N, B, NP_DQ;
TYPE *Gap;
TYPE* G;
int *X, *Y;

#define w1(q, j) (q+j)
#define w2(p, i) (p+i)
#define Sn(x, y) ((x==y)?0:1)

#ifdef LOOPDP
int NP;

void LoopGAP(int n) {
	TYPE *uu;
	for (int t = 2; t <= n; t++) {
		cilk_for(int i = 1; i<t; i++)
		{
			int j = t - i;
			TYPE G_ij = G[(i - 1)*(NP) + (j - 1)] + Sn(X[i], Y[j]);
			uu = G+i*(NP);
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
			G[i*(NP) + j] = G_ij;
		}

	}
	int end = n + n + 1;
	for (int t = n + 1; t<end; t++) {

		cilk_for(int i = n; i >= t - n; i--)
		{
			int j = t - i;
			TYPE G_ij = G[(i - 1)*(NP) + (j - 1)] + Sn(X[i], Y[j]);
			uu = G +i*(NP);
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

			G[i*(NP) + j] = G_ij;
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


//For any N
void funcC(int x1, int y1, int x2, int n) {

	//if outsize of actual N, then return
	if (x1 > N || y1 > N || x2 > N)
		return;

	//if current size is less than base case, use loop based approach
	if (n <= B) {
#ifdef USE_PAPI
		int id = tid();
		int retval = 0;
		papi_for_thread(id);
		if ( (retval=PAPI_start(EventSet[id])) != PAPI_OK)
		ERROR_RETURN(retval);
#endif

		int endi = (x1 + n) > N ? (N + 1 - x1) : n;

		const int endj = (y1 + n) > N ? (N + 1 - y1) : n;

		const int endp = (x2 + n) > N ? (N + 1 - x2) : n;

		 // copy optimization
		__declspec(align(64)) TYPE V[endp * endj];
		
		for (int i = 0; i < endp; i++) {
			#pragma ivdep
			for (int j = 0; j < endj; j++) {
				V[j * endp + i] = Gap[(x2 + i) * NP_DQ + (y1 + j)];

			}

		}
#pragma parallel
		for (int i = x1; i < (x1 + endi); i++) {
			for (int j = y1, k=0; j < (y1 + endj); j++, k++) {
				TYPE G_ij = Gap[i*NP_DQ + j];
				
#pragma ivdep
				for (int p = 0; p < endp; p++) {
					G_ij = min(G_ij, V[k*endp+p] + w2(p+x2, i));
				}

				Gap[i*NP_DQ + j] = G_ij;
			}
		}
#ifdef USE_PAPI
		countMisses(id );
#endif
		return;
	}
	//else divide it further and call recursively
	else {

		//divide into 4 parts
		int nn = (n >> 1);

		//before calling you may check whether a quadrant is empty or not, however,
		//its not necessary as we also have guard condition at the begining of the function, however, it seems to reduce total overhead function call

		// call on first quadrant
		cilk_spawn funcC(x1, y1, x2, nn);
		// 2nd quad
		//if(x1<=N && y1+nn<=N)
		cilk_spawn funcC(x1, y1 + nn, x2, nn);
		//3rd quad
		//if(x1+nn<=N && y1<=N)
		cilk_spawn funcC(x1 + nn, y1, x2, nn);
		//4th quad
		//if(x1+nn<=N && y1+nn<=N)
		funcC(x1 + nn, y1 + nn, x2, nn);
		cilk_sync;

		//1st quad
		//if(x1<=N && y1<=N)
		cilk_spawn funcC(x1, y1, x2 + nn, nn);

		//2nd quad
		//if(x1<=N && y1+nn<=N)
		cilk_spawn funcC(x1, y1 + nn, x2 + nn, nn);

		//3rd quad
		//if(x1+nn<=N && y1<=N)
		cilk_spawn funcC(x1 + nn, y1, x2 + nn, nn);

		//4th quad
		//if(x1+nn<=N && y1+nn<=N)
		funcC(x1 + nn, y1 + nn, x2 + nn, nn);

		cilk_sync;
	}
}

//in function B, x1, x2 are the same
void funcB(int x1, int y1, int y2, int n) {
	//if outsize the range, return;
	if (x1 > N || y1 > N || y2 > N)
		return;

	//if less than base case size, use loop based version
	if (n <= B) {
#ifdef USE_PAPI
		int id = tid();
		int retval = 0;
		papi_for_thread(id);
		if ( (retval=PAPI_start(EventSet[id])) != PAPI_OK)
		ERROR_RETURN(retval);
#endif

		int endi = (x1 + n) > N ? (N + 1 - x1) : n;

		int endj = (y1 + n) > N ? (N + 1 - y1) : n;

		int endq = (y2 + n) > N ? (N + 1 - y2) : n;
		
#pragma parallel
		for (int i = x1; i < x1+endi; i++) {
			for (int j = y1; j < y1+endj; j++) {
				
				TYPE G_ij = Gap[i*NP_DQ+ j];
#pragma ivdep
				for (int q = y2; q < y2+endq; q++) {
					G_ij = min(G_ij, Gap[i*NP_DQ + q] + w1(q, j));
				}

				Gap[i*NP_DQ + j] = G_ij;
			}
		}
#ifdef USE_PAPI
		countMisses(id );
#endif
		return;
	}
	//else divide further and call recursively
	else {

		//divide each dimension into half
		int nn = (n >> 1);

		//before calling you may check whether a quadrant is empty or not
		//1st quad
		cilk_spawn funcB(x1, y1, y2, nn);

		//2nd Quad
		cilk_spawn funcB(x1, y1 + nn, y2, nn);

		//3rd Quad
		cilk_spawn funcB(x1 + nn, y1, y2, nn);

		//4th quad
		//if(x1+nn<=N && y1 + nn<=N)
		funcB(x1 + nn, y1 + nn, y2, nn);
		cilk_sync;

		//1st quad
		cilk_spawn funcB(x1, y1, y2 + nn, nn);

		//2nd Quad
		cilk_spawn funcB(x1, y1 + nn, y2 + nn, nn);

		//3rd quad
		cilk_spawn funcB(x1 + nn, y1, y2 + nn, nn);

		//4th quad
		//if(x1+nn<=N && y1 + nn<=N)
		funcB(x1 + nn, y1 + nn, y2 + nn, nn);
		cilk_sync;

	}
}

void funcA(int n, int x1, int y1) {
	//if the block is outside the range, just return
	if (x1 > N || y1 > N)
		return;

	//else if the size is less than the base case size, compute using the look based version
	if (n <= B) {
#ifdef USE_PAPI
		int id = tid();
		int retval = 0;
		papi_for_thread(id);
		if ( (retval=PAPI_start(EventSet[id])) != PAPI_OK)
		ERROR_RETURN(retval);
#endif
		int endi = (x1 + n) > N ? (N + 1 - x1) : n;

		int endj = (y1 + n) > N ? (N + 1 - y1) : n;

		for (int i = x1; i < x1+endi; i++) {

			for (int j = y1; j < y1+endj; j++) {

				TYPE G_ij = Gap[(i-1)*NP_DQ + (j - 1)] + Sn(X[i], Y[j]);
#pragma ivdep
				for (int q = y1; q < j; q++) {
					G_ij = min(G_ij, Gap[i*NP_DQ + q] + w1(q, j));
				}
#pragma ivdep
				for (int p = x1; p < i; p++) {
					G_ij = min(G_ij, Gap[p * (NP_DQ) + j] + w2(p, i));
				}
				Gap[i*NP_DQ + j] = min(Gap[i*NP_DQ + j] , G_ij );

			}
		}
#ifdef USE_PAPI
		countMisses(id );
#endif
	}
	//otherwise divide it even further and call recursively
	else {
		//divide each dimention into half

		int nn = (n >> 1);

		//1st quad
		funcA(nn, x1, y1);
		//2nd quad
		cilk_spawn funcB(x1, y1 + nn, y1, nn);
		//3rd quad
		funcC(x1 + nn, y1, x1, nn);
		cilk_sync;

		//2nd quad
		cilk_spawn funcA(nn, x1, y1 + nn);

		//3rd quad
		funcA(nn, x1 + nn, y1);
		cilk_sync;

		//4th quad
		//   if(x1+nn<=N && y1+nn<=N)

		funcB(x1 + nn, y1 + nn, y1, nn);
		funcC(x1 + nn, y1 + nn, x1, nn);
		funcA(nn, x1 + nn, y1 + nn);

	}
}

int main(int argc, char *argv[]) {
	N = 32;
    B = 32;
	if (argc > 1)
		N = atoi(argv[1]);
	if (argc > 2)
		B = atoi(argv[2]);

	
	//printf( "Original N = %d , B = %d \n", N, B );

	int NN = 2;
	while (NN < N)
		NN = (NN << 1); //find the next power of two

	NP_DQ = (N + 1);

	if (B > NN) {
		B = NN / 4;
	}
	X = (int *) _mm_malloc((N + 1) * sizeof(int), ALIGNMENT);
	Y = (int *) _mm_malloc((N + 1) * sizeof(int), ALIGNMENT);

	X[0] = Y[0] = 32;
	genRandInput(X, Y, N + 1);

	#ifdef CO
	Gap = ( TYPE * ) _mm_malloc( (NP_DQ) * (NP_DQ) * sizeof( TYPE ), ALIGNMENT );
	Gap[0] = 0;
    #endif

#ifdef LOOPDP
	NP = N+1;
	if(NN==N+1) NP = N+2;
	G = (TYPE *)_mm_malloc((NP) * (NP) * sizeof(TYPE), ALIGNMENT);
	G[0] = 0;

#endif

	TYPE inf = (TYPE) (1e9);

	for (int i = 0; i < N + 1; i++) {
		//int in = i*(NP_DQ);
#ifdef CO
		Gap[i*(NP_DQ)] = w1(i, 0);
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
#ifdef CO
			Gap[ i * (NP_DQ) + j ] = inf;
#endif

#ifdef LOOPDP
			G[i * (NP) + j] = inf;
#endif
		}
#ifdef USE_PAPI
	papi_init();
#ifdef LOOPDP
	long long int dpmiss[NUM_EVENTS]= {0};
#endif
#endif

#ifdef LOOPDP
#ifdef pdeBug
	for (int i = 0; i< N+1; i++)
	{
		cout<<(char)X[i];
	}
	cout<<endl;
	for (int i = 0; i< N+1; i++)
	{
		cout<<(char)Y[i];
	}
	cout<<endl;
#endif
	//cout<<endl;
	
		unsigned long long tstart1 = cilk_getticks();
#ifdef USE_PAPI
	int rval;
	papi_for_thread(0);
	if (rval=PAPI_start(EventSet[0]) != PAPI_OK) ERROR_RETURN(rval);
#endif
	LoopGAP(N);
	unsigned long long tend1 = cilk_getticks();
	cout<< "LOOP,"<<N<<","<<cilk_ticks_to_seconds(tend1-tstart1)<<",";
#ifdef USE_PAPI
	if (rval=PAPI_stop(EventSet[0], dpmiss) != PAPI_OK) ERROR_RETURN(rval);
	cout<<","<<dpmiss[0]<<","<<dpmiss[1];

#endif

#ifdef USE_PAPI
	cout<<endl;
#endif
#ifdef pdeBug
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

#ifdef ENERGY
	energy_lib_init();
#endif


#ifdef CO
#ifdef ENERGY
	 reset_energy_measurement();
     start_energy_measurement();
#endif


	{

		unsigned long long tstart = cilk_getticks();

		funcA (NN, 1, 1); //send NN instead of N

		unsigned long long tend = cilk_getticks();

		cout<< "CO,"<<N<<","<<cilk_ticks_to_seconds(tend-tstart)<<",";
	}
#ifdef ENERGY
	 stop_energy_measurement();
#endif
#ifdef pdeBug
	cout<<"CO matrix:"<<endl;
	for (int i = 0; i<N+1; i++)
	{
		for(int j = 0; j< N+1; j++)
		{

			cout<<Gap[i*(NP_DQ)+j]<<" ";

		}
		cout<<endl;
	}
#endif

#endif
	// printf( "p = %d, T_p = %.0lf ( ms )\n", __cilkrts_get_nworkers( ), tend);

#ifdef LOOPDP
#ifdef CO
	for (int i = 0; i<N + 1; i++)
	{
		for (int j = 0; j< N + 1; j++)
		{
			if(Gap[i*(NP_DQ)+j]!=G[i * (NP) + j])
			{
				cout<<"wrong at"<<i<<","<<j<<endl;
				fflush(stdout);
			}
			assert(Gap[i*(NP_DQ) + j] == G[i * (NP) + j]);
		}
	}
	
#endif
	_mm_free(G);
#endif

	_mm_free(X);
	_mm_free(Y);
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
	if (Gap!=NULL) _mm_free(Gap);
	return 0;
}
