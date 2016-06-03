/*
* Compilation using icc on windows RTODO
* -D DEBUG = debug mode - runs original parenthesis function and compares the recursive version with this
* -D RANDOMDIST = random original values in dist array
* -D B=64 = hardcoding B 
*/
#include <cstdio>
#include <cstdlib>
#include <ctime>
#include <string>
#include <cassert>
#include <iostream>
#include <cilk/cilk.h>
#include <cilk/cilk_api.h>
#include "cilktime.h"
using namespace std;
#ifndef TYPE
#define TYPE int
#endif
#define ALIGNMENT 64
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
#define MAXVAL int(1e9)
#define INITMIN MAXVAL
/* Min Max and Weight Function */
//#define min(a,b) (a<b?a:b)
//#define max(a,b) (a>b?a:b)
#define w(i, j, k) (((i*j*k)&7)) //weight function

#ifndef NNUM
#define NNEEDED 1
long long N = 1000;
TYPE *dist;
#else
#define NNEEDED 0
#define N NNUM
TYPE dist[((long long)N)*N];
#endif

#ifndef B
#define BNEEDED 1
long long B = 64;
#else
#define BNEEDED 0
#endif

#define Ddist(i,j) dist[i*N + j]
#define DCLdist(i,j) Ddist(i,j)
#define DBLdist(i,j) Ddist(i,j)
#define DALdist(i,j) Ddist(i,j)
#define psi(i,j) Ddist(i,j)
#define theta(i,j) Ddist(i,j)


struct interval {
	TYPE begin;TYPE end;
};
#define FOR_VAR_FWD(i,n,m) for(TYPE i=n;i<m;i++)
#define FOR_VAR_BWD(i,n,m) for(TYPE i=m-1;i>=n;i--)

#define SIZE(I) (DEFEND(I)-DEFBEGIN(I))
#define FOR_FORWARD(i,K) for(TYPE i=DEFBEGIN(K);i<DEFEND(K);i++)
#define FOR_BACKWARD(i,K) for(TYPE i=DEFEND(K)-1;i>=DEFBEGIN(K);i--)
#define FOR_FWD(i,b,e) for(TYPE i=b;i<e;i++)
#define FOR_BWD(i,b,e) for(TYPE i=e-1;i>=b;i--)
#define FOR_FWD_FWD(i,j,I,J,ZZ) FOR_FORWARD(i,I){FOR_FORWARD(j,J){ZZ}}
#define FOR_FWD_BWD(i,j,I,J,ZZ) FOR_FORWARD(i,I){FOR_BACKWARD(j,J){ZZ}}
#define FOR_BWD_FWD(i,j,I,J,ZZ) FOR_BACKWARD(i,I){FOR_FORWARD(j,J){ZZ}}
#define FOR_BWD_BWD(i,j,I,J,ZZ) FOR_BACKWARD(i,I){FOR_BACKWARD(j,J){ZZ}}

//SIZE(I) == SIZE(J)
//#define FOR_DIAG_I_LT_J_FWD_FWD(i,j,I,J,ZZ) FOR_VAR_FWD(of,0,SIZE(I)){FOR_VAR_FWD(ci,0,SIZE(J)-of){TYPE i = ci+DEFBEGIN(I); TYPE j = DEFBEGIN(J)+ci+of; ZZ}}

//#define FOR_A_loop_2(i,j,I,J,ZZ) FOR_BWD_FWD(i,j,I,J,ZZ)
#define FOR_A_loop_1(i,n,m) FOR_VAR_FWD(i,n,m)
#define FOR_A_loop_2(i,n,m) FOR_VAR_BWD(i,n,m)
#define FOR_A_loop_3(i,n,m) FOR_VAR_FWD(i,n,m)
#define FOR(i,J) 
#define PSI(i,j) 
#define FOR_B_loop_3(i,n,m) FOR_VAR_BWD(i,n,m)
#define FOR_B_loop_4(i,n,m) FOR_VAR_FWD(i,n,m)
#define FOR_B_loop_2(i,n,m) FOR_VAR_FWD(i,n,m)
#define FOR_B_loop_1(i,n,m) FOR_VAR_FWD(i,n,m)
//#define FOR_B_loop_1(i,j,I,J,ZZ) FOR_BWD_FWD(i,j,I,J,ZZ)

#define FOR_C_loop_1(i,n,m) FOR_VAR_FWD(i,n,m)
#define FOR_C_loop_2(i,n,m) FOR_VAR_FWD(i,n,m)
#define FOR_C_loop_3(i,n,m) FOR_VAR_FWD(i,n,m)
//#define FOR_C_loop_2(i,j,I,J,ZZ) FOR_FWD_FWD(i,j,I,J,ZZ)

#define FORUNION(i,nK,mK,nL,mL,ZZ) FOR_VAR_FWD(i,nK,mK){ZZ};FOR_VAR_FWD(i,nL,mL){ZZ}

#define BASE_CONSTRAINT_A(a) ((DEFEND(a)-DEFBEGIN(a)) <= B)
#define BASE_CONSTRAINT_B(a,b) (BASE_CONSTRAINT_A(a) || BASE_CONSTRAINT_A(b))
#define BASE_CONSTRAINT_C(a,b,c) (BASE_CONSTRAINT_B(a,b) || BASE_CONSTRAINT_A(c))

#define DdistCO(i,j,I,J) V[((j)-DEFBEGIN(J))*B + ((i)-DEFBEGIN(I))]

inline void copy_dist_part(TYPE* V,DEFINTERVALFUNC(II),DEFINTERVALFUNC(JJ)){
	for(int i=DEFBEGIN(II);i<DEFEND(II);i++){
		for(int j=DEFBEGIN(JJ);j<DEFEND(JJ);j++){
			//cout<<i<<" "<<j<<" "<<(j)-DEFBEGIN(JJ)<<" "<<((i)-DEFBEGIN(II))<<endl;
			DdistCO(i,j,II,JJ) = Ddist(i,j);

		}
	}
}

/*
* Auto-generated Code
*/

#include "../paren-scala.cpp"

#ifdef DEBUG
void parenthesis() {
	for (int t = 2; t < N; t++) {
		cilk_for (int i = 0; i < N - t; i++) {
			int j = t + i;
			TYPE D_ij = Ddist(i,j);
			for (int k = i + 1; k <= j; k++) {
				D_ij = min(D_ij, Ddist(i,k) + Ddist(k,j) + w(i,k,j));
			}
			Ddist(i,j) = D_ij;
		}
	}
}

TYPE *drec;
TYPE *dorig;
void dcopy(TYPE *from, TYPE *to) {
	for (int i = 0; i < N*N; i++) {
		to[i] = from[i];
	}
}
void printError(string msg, int i, int j) {
	cout << "ERROR: " << msg << "\ni\tj\trec\tparen\n" << i << "\t"
		<< j << "\t" << drec[i*N + j] << '\t' << Ddist(i,j) << endl;
	exit(1);
}
void checkForError(string func) {
	int ctr = 0;
	for (int i = 0; i < N; i++) {
		for (int j = 0; j < N; j++) {
			if (N<20 && i < j){
				cout << i << "\t"
					<< j << "\t" << drec[i*N + j] << '\t' << Ddist(i,j) << endl;
			}
			if (drec[i*N + j] != dorig[i*N + j]) ctr++;
			if (drec[i*N + j] != Ddist(i,j)) {
				printError("rec vs paren: values not the same", i, j);
			}
		}
	}
	cout << func << " " << ctr << " values updated correctly." << endl;
	//cout << "DONE" << endl;
}
#endif

inline void init_dist(){
	//cout<<"Standard dist "<<endl;
#ifndef RANDOMDIST
	for (int i=0;i<N;i++) {
		for (int j=0;j<N;j++) {
			if (j == i+1) {
				Ddist(i,j) = i+1;
				if (N < 20) {
					cout<<i<<'\t'<<j<<'\t'<<Ddist(i,j)<<endl;
				}
			}
			else Ddist(i,j) = MAXVAL;
		}
	}
#else
	for (int i=0;i<N;i++) {
		for (int j=0;j<N;j++) {
			if (i < j) {
				Ddist(i,j) = rand()%40 - 20;
				if (N < 20) {
					cout<<i<<'\t'<<j<<'\t'<<Ddist(i,j)<<endl;
				}
			}
			else Ddist(i,j) = MAXVAL;
		}
	}
#endif
}
int main(int argc, char *argv[]) {

	if (argc < BNEEDED + NNEEDED + 1){
		cout<<"not enough arguments"<<endl;
		exit(1);
	}
	argv++;
	argc--;
#ifndef NNUM
	if (argc > 0){
		N = atoi(argv[0]);
		argv++;
		argc--;
	}
#endif
#ifndef B
	if (argc > 0){
		B = atoi(argv[0]);
	}
#endif

#ifdef _DEBUG
	if (0!= __cilkrts_set_param("nworkers","1")) {
		cout<<"Failed to set worker count\n";
		return 1;
	}
#endif 
	long long NN = 2;

	// Find the powers of 2 >=N.
	while (NN < N)
		NN = NN << 1;
	long long NP = N;

	srand ((unsigned int)time(NULL));
#ifndef NNUM
	dist = ( TYPE* ) _mm_malloc(NP * NP * sizeof( TYPE ),ALIGNMENT);
#endif
	init_dist();
#ifdef DEBUG
#ifdef RANDOMDIST
	dorig = ( TYPE* ) _mm_malloc(N * N * sizeof( TYPE ),ALIGNMENT);
	dcopy(dist,dorig);
#endif
#endif 
	DEFINTERVALSTMT(K0);
	DEFBEGIN(K0) = 0;
	DEFEND(K0) = N;

	unsigned long long tstart = cilk_getticks();
	funcA_rec(PARAM(K0));
	unsigned long long tend = cilk_getticks();
	cout<<N<<" "<<B<<" "<<cilk_ticks_to_seconds(tend-tstart);
	//cout<<"REC\t"<<N<<"\t"<<cilk_ticks_to_seconds(tend-tstart)<<endl;
#ifdef DEBUG
	{
		drec = ( TYPE* ) _mm_malloc(N * N * sizeof( TYPE ),ALIGNMENT);
		dcopy(dist,drec);
#ifndef RANDOMDIST
		dorig = ( TYPE* ) _mm_malloc(N * N * sizeof( TYPE ),ALIGNMENT);		
		init_dist();
		dcopy(dist,dorig);
#else
		dcopy(dorig,dist);
#endif
		unsigned long long tstart = cilk_getticks();
		parenthesis();
		unsigned long long tend = cilk_getticks();
		cout<<"PAREN\t"<<N<<"\t"<<cilk_ticks_to_seconds(tend-tstart)<<endl;
		checkForError("rec vs paren");
	}
	_mm_free(dorig);
	_mm_free(drec);

#endif
#ifndef NNUM
	_mm_free(dist);
#endif
	exit(0);
}


