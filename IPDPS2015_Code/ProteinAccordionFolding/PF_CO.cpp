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
string proteinSeq;

#define min(a, b) (a<b?a:b)
#define max(a, b) (a>b?a:b)

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

	for(int i = n-2; i>=0;i--)
	{
		cilk_for(int j = n-3; j>i; j--)
		{
#ifdef USE_PAPI
			int id = tid();
			int retval = 0;
			papi_for_thread(id);
			if ( (retval=PAPI_start(EventSet[id])) != PAPI_OK)
			ERROR_RETURN(retval);
#endif
			int val = S_dp[i*N+j];
			//I have observed that these 2 optimizations does not matter really!
			int j2 = 2*j-i+1;
			int inj = (j+1)*N;
			for(int k = n-1; k>=j+2; k--)
			{
#ifdef pDEBUG
				cout<<"("<<i<<","<<j<<") ("<<j+1<<","<<k<<") ("<<j+1<<","<<min(k, j2)<<")"<<endl;
#endif
				val = max(val, S_dp[inj+k] + SOF[inj+min(k, j2)]);

			}
			S_dp[i*N+j]= val;

#ifdef USE_PAPI
			countMisses(id );
#endif

		}

	}

	//find the maximum value
	int final = 0;
	for(int j = 0; j<n-1; j++)
	{
		final = max(final, S_dp[j]);

	}
	return final;

}
#endif

void D_PF(int n, int xi, int xj, int vj) {
	if (vj > N || xi > N || xj > N)
		return;
	if (n <= B) //D_loop
			{
#ifdef USE_PAPI
		int id = tid();
		int retval = 0;
		papi_for_thread(id);
		if ( (retval=PAPI_start(EventSet[id])) != PAPI_OK)
		ERROR_RETURN(retval);
#endif
		int endi = (xi + n >= N) ? (N - xi - 1) : n;
		int endj = (xj + n >= N) ? (N - xj - 2) : n;
		int endk = (vj + n >= N) ? (N - vj) : n;

		int jj = xj + 1;
		__declspec(align(64)) int V[endk * endj];
		__declspec(align(64)) int F[endk * endj];

		__declspec(align(64)) int X[endi * endj];

		int in = jj * N + vj;
		int idx = 0;
		for (int i = 0; i < endj; i++) {
			V[idx:endk] = S[in:endk];
			F[idx:endk] = SOF[in:endk];
			in = in + N;
			idx = idx + endk;
		}
		idx = 0;
		in = (xi) * N + xj;
		for (int i = 0; i < endi; i++) {
			X[idx:endj] = S[in:endj];
			in = in + N;
			idx = idx + endj;
		}
		//endi = xi+endi;
		in = 0;
		for (int i = 0, ii = xi; i < endi; i++, ii++) {
			idx = 0;
#pragma parallel
			for (int j = 0, jj = xj; j < endj; j++, jj++) {
				int j2 = jj + jj - ii + 1; //2*j-i+1
				int val = X[in + j];
				//why does splitting increases running time?
				int start = max(vj, jj + 2);
				if (j2 < start) {
					int c = 0;
					start = start - vj;
					int *vv = V + idx + start;
#pragma ivdep
					for (int k = start; k < endk; k++) //again the same problem?? what should be the bounday of k??
							{

#ifdef pDEBUG
						cout<<"("<<i<<","<<j<<") ("<<j+1<<","<<k<<") ("<<j+1<<","<<min(k, j2)<<")"<<endl;
#endif				
						c = max(c, *vv);
						vv++;
					}
					X[in + j] = max(val, c + SOF[(jj + 1) * N + j2]);

				} else {
					j2 = j2 - vj;
					start = start - vj;
					int *vv = V + idx + start;
					int *sof = F + idx;
#pragma ivdep
					for (int k = start; k < endk; k++) //again the same problem?? what should be the bounday of k??
							{
#ifdef pDEBUG
						cout<<"("<<i<<","<<j<<") ("<<j+1<<","<<k<<") ("<<j+1<<","<<min(k, j2)<<")"<<endl;
#endif		
						val = max(val, *vv + *(sof+min(k, j2)));
						vv++;
					}
					X[in + j] = val;
				}
				idx = idx + endk;
			}
			in = in + endj;
		}

		idx = 0;
		in = (xi) * N + xj;
		for (int i = 0; i < endi; i++) {
			S[in:endj]=X[idx:endj];
			in = in + N;
			idx = idx + endj;
		}
#ifdef USE_PAPI
		countMisses(id );
#endif
		return;
	} else {

		int nn = (n >> 1);

		cilk_spawn D_PF(nn, xi, xj, vj);
		cilk_spawn D_PF(nn, xi, xj + nn, vj);
		cilk_spawn D_PF(nn, xi + nn, xj, vj);
		D_PF(nn, xi + nn, xj + nn, vj);
		cilk_sync;

		cilk_spawn D_PF(nn, xi, xj, vj + nn);
		cilk_spawn D_PF(nn, xi, xj + nn, vj + nn);
		cilk_spawn D_PF(nn, xi + nn, xj, vj + nn);
		D_PF(nn, xi + nn, xj + nn, vj + nn);
		cilk_sync;

	}

}

void C_PF(int n, int xi, int xj, int uj) {
	if (uj > N || xi > N || xj > N)
		return;
	if (n <= B) //C_loop
			{
#ifdef USE_PAPI
		int id = tid();
		int retval = 0;
		papi_for_thread(id);
		if ( (retval=PAPI_start(EventSet[id])) != PAPI_OK)
		ERROR_RETURN(retval);
#endif
		int endi = (xi + n >= N) ? (N - xi - 1) : n;
		int endj = (xj + n >= N) ? (N - xj - 2) : n;
		int endk = (uj + n >= N) ? (N - uj) : n;

		endk = uj + endk;

		int in = (xi + endi - 1) * N;
		for (int i = endi - 1; i >= 0; i--) {
			int ii = xi + i;
			int inj = (xj + endj) * N;
#pragma parallel
			for (int j = endj - 1; j > i; j--) {
				int jj = xj + j;
				//int inj = (jj+1)*N;
				int ini = in + jj;
				//int j2 = 2*jj-ii+1;
				int j2 = jj + jj - ii + 1;
				int val = S[ini];
				int start = max(uj, jj + 2);
				int *Sk = S + inj + start;
#pragma ivdep
				for (int k = start; k < endk; k++) {
#ifdef pDEBUG
					cout<<"("<<ii<<","<<jj<<") ("<<jj+1<<","<<k<<") ("<<jj+1<<","<<min(k, j2)<<")"<<endl;
#endif	
					val = max(val, *Sk + SOF[inj+min(k, j2)]);
					Sk++;

				}
				S[ini] = val;
				inj = inj - N;
			}
			in = in - N;
		}
#ifdef USE_PAPI
		countMisses(id );
#endif
		return;
	} else {

		int nn = (n >> 1);

		cilk_spawn C_PF(nn, xi, xj, uj);
		cilk_spawn D_PF(nn, xi, xj + nn, uj);
		C_PF(nn, xi + nn, xj + nn, uj);
		cilk_sync;

		cilk_spawn C_PF(nn, xi, xj, uj + nn);
		cilk_spawn D_PF(nn, xi, xj + nn, uj + nn);
		C_PF(nn, xi + nn, xj + nn, uj + nn);
		cilk_sync;

	}

}
//a square depending on a triangle
void B_PF(int n, int xi, int xj, int vj) {
	if (xi > N || xj > N || vj > N)
		return;
	if (n <= B) //B_loop
			{
#ifdef USE_PAPI
		int id = tid();
		int retval = 0;
		papi_for_thread(id);
		if ( (retval=PAPI_start(EventSet[id])) != PAPI_OK)
		ERROR_RETURN(retval);
#endif
		int endi = (xi + n >= N) ? (N - xi - 1) : n;
		int endj = (xj + n >= N) ? (N - xj - 2) : n;
		int endk = (vj + n >= N) ? (N - vj) : n;
		endk = vj + endk;

		int in = xi * N;
		for (int i = 0; i < endi; i++) {
			int ii = xi + i;
			int ini = in + xj;
			int inj = (xj + 1) * N;
#pragma parallel
			for (int j = 0; j < endj; j++) {
				int jj = xj + j;

				int inj = (jj + 1) * N;

				int j2 = jj + jj - ii + 1;
				int val = S[ini];
				int start = max(vj, jj + 2);
				int * Sk = S + inj + start;
#pragma ivdep
				for (int k = start; k < endk; k++) //again the same problem?? what should be the bounday of k??
						{
#ifdef pDEBUG
					cout<<"("<<ii<<","<<jj<<") ("<<jj+1<<","<<k<<") ("<<jj+1<<","<<min(k, j2)<<")"<<endl;
#endif
					val = max(val, *Sk+ SOF[inj+min(k, j2)]);
					Sk++;
				}

				S[ini++] = val;
				inj = inj + N;

			}
			in = in + N;

		}
#ifdef USE_PAPI
		countMisses(id );
#endif
		return;
	} else {

		int nn = (n >> 1);

		cilk_spawn B_PF(nn, xi, xj, vj);
		cilk_spawn B_PF(nn, xi, xj + nn, vj + nn);
		cilk_spawn B_PF(nn, xi + nn, xj, vj);
		B_PF(nn, xi + nn, xj + nn, vj + nn);
		cilk_sync;

		cilk_spawn D_PF(nn, xi, xj, vj + nn);
		D_PF(nn, xi + nn, xj, vj + nn);
		cilk_sync;

	}

}
void A_PF(int n, int xi, int xj) {
	if (xi > N || xj > N)
		return;
	if (n <= B) //A_loop
			{
#ifdef USE_PAPI
		int id = tid();
		int retval = 0;
		papi_for_thread(id);
		if ( (retval=PAPI_start(EventSet[id])) != PAPI_OK)
		ERROR_RETURN(retval);
#endif
		//next question: should I always start from 1? even for the inner triangles?
		int endi = (xi + n >= N) ? (N - xi - 1) : n;
		int endj = (xj + n >= N) ? (N - xj - 2) : n;
		int endk = (xj + n >= N) ? (N - xj) : n;
		int kk = xj + endk - 1;
		for (int i = endi - 1; i >= 0; i--) {
			int ii = xi + i;
			int inii = ii * N;
			for (int j = endj - 1; j > i; j--) {
				int jj = xj + j;

				int inj = (jj + 1) * N;
				int ini = inii + jj;
				//int j2 = 2*jj-ii+1;
				int j2 = jj + 1 + jj - ii;
				int val = S[ini];
				int *Sk = S + inj + kk;
#pragma ivdep
				for (int k = kk; k >= jj + 2; k--) //again the same problem?? what should be the bounday of k??
						{
					//int kk = xj+k;	
#ifdef pDEBUG
					cout<<"("<<ii<<","<<jj<<") ("<<jj+1<<","<<k<<") ("<<jj+1<<","<<min(k, j2)<<")"<<endl;
#endif
					val = max(val, *Sk+SOF[inj+min(k, j2)]);
					Sk--;
				}
				S[ini] = val;

			}

		}
#ifdef USE_PAPI
		countMisses(id );
#endif
		return;
	}

	else {
		int nn = (n >> 1);

		A_PF(nn, xi + nn, xj + nn);
		B_PF(nn, xi, xj + nn, xj + nn);
		C_PF(nn, xi, xj, xj + nn);
		A_PF(nn, xi, xj);
	}
}
int CO_PROTEIN_FOLDING(int n) {

	//array, size, starting point x, starting point y
	A_PF(n, 0, 0);
	int final = 0;

	for (int j = 0; j < n - 1; j++) {
		final = max(final, S[j]);

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

#ifdef USE_PAPI
	papi_init();
#endif
	int NN = 2;

	while (NN < N)
		NN = NN << 1;
	SOF = (int *) _mm_malloc(N * N * sizeof(int), 64); //stores score-one-fold
	//clearing the SOF array
	for (int i = 0; i < N; i++) {
	SOF[i*N:N] = 0;
}

//create arbitary protein seq

makeProteinSeq(N);
//compute SOF

SCORE_ONE_FOLD(N);

//allocate for the score array
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

S = (int *) _mm_malloc(N * N * sizeof(int), 64);
//clearing the S array
for (int i = 0; i < N; i++) {
S[i*N:N] = 0;
}

cout << "CO:";

unsigned long long tstart = cilk_getticks();

int finalc = CO_PROTEIN_FOLDING(N);

unsigned long long tend = cilk_getticks();
cout << "," << cilk_ticks_to_seconds(tend - tstart) << ",";
#ifdef DEBUG
#ifdef LOOPDP
#ifdef pdebug
cout<<"CO\n";
for(int i=0;i<N; i++)
{
for(int j=0;j<N; j++)
{
	cout<<S[i*N+j]<<" ";
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
	if(S[i*N+j]!=S_dp[i*N+j])
	cout<<i<<" "<<j<<endl;
	assert(S[i*N+j]==S_dp[i*N+j]);
}

}
#endif
#endif
#ifdef LOOPDP
_mm_free(S_dp);
#endif
_mm_free(S);
_mm_free(SOF);
#ifdef USE_PAPI
countTotalMiss(p);
cout<<endl;
PAPI_shutdown();

#endif
return 0;
}
