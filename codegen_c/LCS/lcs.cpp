/*
* g++ -o lcs -D N=5000 -D M=1000 -D B=16 -O3 lcs-a.cpp  && ./lcs
* g++ -o lcs -D N=7000 -D M=12000 -D B=256 -O3 lcs-a.cpp  && ./lcs
*/
#include <cstdio>
#include <cstdlib>
#include <ctime>
#include <cassert>
#include <iostream>
#include<string>
#include <cilk/cilk.h>
#include <cilk/cilk_api.h>
#include "cilktime.h"
//#include "timerclass.h"
using namespace std;
#ifndef TYPE
#define TYPE int
#endif

#ifdef INTINTERVAL
#define DEFINTERVALFUNC(I) TYPE I##_begin, TYPE I##_end
#define DEFINTERVALSTMT(I) TYPE I##_begin, I##_end
#define DEFBEGIN(I) I##_begin
#define DEFEND(I) I##_end
#define PARAM(I) I##_begin, I##_end
#else
#define DEFINTERVALFUNC(I) interval I
#define DEFINTERVALSTMT(I) interval I
#define DEFBEGIN(I) I.begin
#define DEFEND(I) I.end
#define PARAM(I) I
#endif
#define MAXVAL 100000
#define UNDEF -1
#define IS_UNDEF(a) (a == UNDEF)
/* Min Max and Weight Function */
//#define min(a,b) (a<b?a:b)
//#define max(a,b) (a>b?a:b)
#define OMAX(a,b) max(a,b)
//#define OMAX(a,b) ((IS_UNDEF(a) || IS_UNDEF(b))?UNDEF:max(a,b))
#define w(i, j, k) (((i*j*k)&7)) //weight function
#define INSET(i,I) (i >= DEFBEGIN(I) && i < DEFEND(I))
#define GETDEF(a,b) ((!IS_UNDEF(a))?a:b)
#define LET(i,v) TYPE i = v

long long N;
#define M N
#ifndef B
#define B 64
#endif
#define ALIGNMENT 64
TYPE* dist;

int* X;
int* Y; //actual length of sequence is M-1 from index 1 to M-1
struct interval {
	TYPE begin;TYPE end;
};
#define FOR_VAR_FWD(i,n,m) for(TYPE i=n;i<m;i++)
#define FOR_VAR_BWD(i,n,m) for(TYPE i=m-1;i>=n;i--)

#define SIZE(I) (DEFEND(I)-DEFBEGIN(I))
#define FOR_FORWARD(i,K) for(TYPE i=DEFBEGIN(K);i<DEFEND(K);i++)
#define FOR_BACKWARD(i,K) for(TYPE i=DEFEND(K)-1;i>=DEFBEGIN(K);i--)

#define BASE_CONSTRAINT(a) ((DEFEND(a)-DEFBEGIN(a)) <= B)
#define BASE_CONSTRAINT_A(a,b) (BASE_CONSTRAINT(a) || BASE_CONSTRAINT(b))

#define FOR_A_loop_1(i,n,m) FOR_VAR_FWD(i,n,m)
#define FOR_A_loop_2(i,n,m) FOR_VAR_FWD(i,n,m)
#define FOR_A_rec_1(i,n,m) FOR_VAR_FWD(i,n,m)
#define FOR_A_rec_2(i,n,m) FOR_VAR_FWD(i,n,m)
#define FOR_A_rec_3(i,n,m) FOR_VAR_FWD(i,n,m)
#define FOR_A_rec_4(i,n,m) FOR_VAR_FWD(i,n,m)
#define FOR_A_rec_5(i,n,m) FOR_VAR_FWD(i,n,m)
#define FOR_A_rec_6(i,n,m) FOR_VAR_FWD(i,n,m)
#define FOR_A_rec_7(i,n,m) FOR_VAR_FWD(i,n,m)
#define FOR_A_rec_8(i,n,m) FOR_VAR_FWD(i,n,m)
#define FOR_A_rec_9(i,n,m) FOR_VAR_FWD(i,n,m)
#define FOR_A_rec_10(i,n,m) FOR_VAR_FWD(i,n,m)
#define Ddist(i,j) dist[(i)*N+(j)]
#define DCLdist(i,j) Ddist(i,j)
#define DBLdist(i,j) Ddist(i,j)
#define DALdist(i,j) Ddist(i,j)
#define DELTA(i,j) (X[i] == Y[j])
#include "../lcs-all.cpp"

/*
* Testing Code
*/





#ifdef LOOPDP
TYPE* dloop;
#define DdistLoop(i,j) dloop[(i)*N+(j)]
void LCS_orig() {
	for (int sum=2;sum<=2*N-2;sum++){
		cilk_for(int i=min(N-1,(long long)(sum-1)); i>=max((long long)1,sum-N+1) ;i--){
			int j =sum-i;
			//cout<<i<<" "<<j<<endl;
			if (IS_UNDEF(DdistLoop(i,j))) {
				if (DELTA(i, j)) {
					DdistLoop(i,j) = DdistLoop((i - 1),(j - 1)) + 1;
				}
				else {
					DdistLoop(i,j) = max(DdistLoop(i,(j - 1)), DdistLoop((i - 1),j));
				}
			}
		}
	}
/*	for(int i = 1; i< N;i++)
	{
		//RTODO: PARALLEL cilk_for?
		for(int j = 1; j< N;j++)
		{
			
		}
	}
	*/
}


void fillDistLoop() {
	for (int i = 0; i < N; i++) {
		for (int j = 0; j < M; j++) {
			DdistLoop(i,j) = UNDEF;
			if (i == 1 || j == 1) {
				DdistLoop(i,j) = 0;
			}
		}
	}

}
#endif
#ifdef CO
void fillDist() {
	for (int i = 0; i < N; i++) {
		for (int j = 0; j < M; j++) {
			Ddist(i,j) = UNDEF;
			if (i == 1 || j == 1) {
				Ddist(i,j) = 0;
			}
		}
	}

}
#endif


void getRandSeq() {
	char a = 'A';
	if (N<120) cout << "X: ";
	for (int i = 0; i < N; i++) {
		X[i] = rand() % 4 + a;
		if (N<120)
			cout << (char) X[i];
	}
	if (N<120)cout << endl;
	if (N<120)cout << "Y: ";
	for (int i = 0; i < M; i++) {
		Y[i] = rand() % 4 + a;
		if (N<120)
			cout << (char) Y[i];
	}
	if (N<120) cout << endl;

}


int main(int argc, char* argv[]){
	int p = __cilkrts_get_nworkers(); // number of threads/processors.
	if (argc < 2){
		cout<<"not enough arguments"<<endl;
		exit(1);
	}
	if (argc > 1){
		N = atoi(argv[1]);
	}

#ifdef _DEBUG
	if (0!= __cilkrts_set_param("nworkers","1")) {
		cout<<"Failed to set worker count\n";
		return 1;
	}
#endif 

	srand ((unsigned int)time(NULL));
#ifdef LOOPDP
	dloop = ( TYPE* ) _mm_malloc(N * N * sizeof( TYPE ),ALIGNMENT);
#endif
#ifdef CO
	dist = ( TYPE* ) _mm_malloc(N * N * sizeof( TYPE ),ALIGNMENT);
#endif
	X = ( TYPE* ) _mm_malloc(N * sizeof( TYPE ),ALIGNMENT);
	Y = ( TYPE* ) _mm_malloc(N * sizeof( TYPE ),ALIGNMENT);


	getRandSeq();
	DEFINTERVALSTMT(I);
	DEFBEGIN(I) = 1;
	DEFEND(I) = N;
	DEFINTERVALSTMT(J);
	DEFBEGIN(J) = 1;
	DEFEND(J) = N;
	cout<<"VERSION\tN\tM\tB\tTime(s)\tLCS-Value"<<endl;
#ifdef LOOPDP
	{
		fillDistLoop();

		unsigned long long tstart = cilk_getticks();
		LCS_orig();
		unsigned long long tend = cilk_getticks();
		cout<<"LOOPDP\t"<<N<<"\t"<<M<<"\t"<<B<<"\t"<<cilk_ticks_to_seconds(tend-tstart)<<"\t"<<DdistLoop(N-1,N-1)<<endl;

	}
#endif
#ifdef CO
	{
		fillDist();
		unsigned long long tstart = cilk_getticks();
		funcA_rec(PARAM(I),PARAM(J));
		unsigned long long tend = cilk_getticks();
		cout<<"funcA\t"<<N<<"\t"<<M<<"\t"<<B<<"\t"<<cilk_ticks_to_seconds(tend-tstart)<<"\t"<<Ddist(N-1,N-1)<<endl;

	}
#endif
#ifdef TEST
	FOR_FORWARD(i,I){
		FOR_FORWARD(j,J){
			if (Ddist(i,j) != DdistLoop(i,j)){
				cout<<i<<" "<<j<<" "<<Ddist(i,j)<<" "<<DdistLoop(i,j)<<" "<<Ddist(N-1,N-1)<<endl;
			}
			assert (Ddist(i,j) == DdistLoop(i,j));
		}
	}
#endif
	return 0;
}

