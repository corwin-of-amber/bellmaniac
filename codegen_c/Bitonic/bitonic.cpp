/*
*/
#include <cstdio>
#include <cstdlib>
#include <ctime>
#include <cmath>
#include <string>
#include <cassert>
#include <iostream>
#include <cilk/cilk.h>
#include <cilk/cilk_api.h>
#include "cilktime.h"
using namespace std;
#ifndef TYPE
#define TYPE double
#endif
#define ALIGNMENT 64
#ifdef INTINTERVAL
#define DEFINTERVALFUNC(I) int I##_begin, int I##_end
#define DEFINTERVALSTMT(I) int I##_begin, I##_end
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
#ifdef ICC
#include <mathimf.h>
#endif
int N;
TYPE* px;
TYPE* py;
TYPE *BTSP;
#ifndef B
#define B 64
#endif

#define Ddist(i,j) BTSP[((i)-1)*N + ((j)-1)]
#define DCLdist(i,j) Ddist(i,j)
#define DBLdist(i,j) Ddist(i,j)
#define DALdist(i,j) Ddist(i,j)
#define d(i,j) sqrt((px[(i)-1] -px[(j)-1])*(px[(i)-1] -px[(j)-1]) + (py[(i)-1] -py[(j)-1])*(py[(i)-1] -py[(j)-1]))

struct interval {
	int begin;int end;
};
DEFINTERVALSTMT(BOTTOMJ);
#define FOR_VAR_FWD(i,n,m) for(int i=n;i<m;i++)
#define FOR_VAR_BWD(i,n,m) for(int i=m-1;i>=n;i--)
#define LET(i,v) int i = v;
#define EQ(i,j) ((i) == (j))
#define INSET(i,I) ((i) >= DEFBEGIN(I) && (i) < DEFEND(I)) 
#define SIZE(I) (DEFEND(I)-DEFBEGIN(I))
#define FOR_FORWARD(i,K) for(int i=DEFBEGIN(K);i<DEFEND(K);i++)
#define FOR_BACKWARD(i,K) for(int i=DEFEND(K)-1;i>=DEFBEGIN(K);i--)
#define FOR_FWD_FWD(i,j,I,J,ZZ) FOR_FORWARD(i,I){FOR_FORWARD(j,J){ZZ}}
#define FOR_FWD_BWD(i,j,I,J,ZZ) FOR_FORWARD(i,I){FOR_BACKWARD(j,J){ZZ}}
#define FOR_BWD_FWD(i,j,I,J,ZZ) FOR_BACKWARD(i,I){FOR_FORWARD(j,J){ZZ}}
#define FOR_BWD_BWD(i,j,I,J,ZZ) FOR_BACKWARD(i,I){FOR_BACKWARD(j,J){ZZ}}

//SIZE(I) == SIZE(J)

#define FOR_A_loop_1(i,n,m) FOR_VAR_FWD(i,n,m)
#define FOR_A_loop_2(i,n,m) FOR_VAR_FWD(i,n,m)
#define FOR_A_loop_3(i,n,m) FOR_VAR_FWD(i,n,m)
#define FOR_A_rec_1(i,n,m) FOR_VAR_FWD(i,n,m)
#define FOR_A_rec_2(i,n,m) FOR_VAR_FWD(i,n,m)
#define FOR_A_rec_3(i,n,m) FOR_VAR_FWD(i,n,m)

#define FOR_B_loop_3(i,n,m) FOR_VAR_FWD(i,n,m)
#define FOR_B_loop_4(i,n,m) FOR_VAR_FWD(i,n,m)
#define FOR_B_loop_2(i,n,m) FOR_VAR_FWD(i,n,m)
#define FOR_B_loop_1(i,n,m) FOR_VAR_FWD(i,n,m)

#define FOR_B_rec_3(i,n,m) FOR_VAR_FWD(i,n,m)
#define FOR_B_rec_4(i,n,m) FOR_VAR_FWD(i,n,m)
#define FOR_B_rec_2(i,n,m) FOR_VAR_FWD(i,n,m)
#define FOR_B_rec_1(i,n,m) FOR_VAR_FWD(i,n,m)
#define FOR_B_rec_5(i,n,m) FOR_VAR_FWD(i,n,m)
#define FOR_B_rec_6(i,n,m) FOR_VAR_FWD(i,n,m)
#define FOR_B_rec_7(i,n,m) FOR_VAR_FWD(i,n,m)
#define FOR_B_rec_8(i,n,m) FOR_VAR_FWD(i,n,m)


#define FOR_C_loop_1(i,n,m) FOR_VAR_FWD(i,n,m)
#define FOR_C_loop_2(i,n,m) FOR_VAR_FWD(i,n,m)
#define FOR_C_loop_3(i,n,m) FOR_VAR_FWD(i,n,m)

#define FOR_C_rec_1(i,n,m) FOR_VAR_FWD(i,n,m)
#define FOR_C_rec_2(i,n,m) FOR_VAR_FWD(i,n,m)
#define FOR_C_rec_3(i,n,m) FOR_VAR_FWD(i,n,m)
#define FOR_C_rec_4(i,n,m) FOR_VAR_FWD(i,n,m)
#define FOR_C_rec_5(i,n,m) FOR_VAR_FWD(i,n,m)

#define FORUNION(i,nK,mK,nL,mL,ZZ) FOR_VAR_FWD(i,nK,mK){ZZ};FOR_VAR_FWD(i,nL,mL){ZZ}
#define BASE_CONSTRAINT1(a) ((DEFEND(a)-DEFBEGIN(a)) <= B)
#define BASE_CONSTRAINT2(a,b) (BASE_CONSTRAINT1(a) || BASE_CONSTRAINT1(b))
#define BASE_CONSTRAINT3(a,b,c) (BASE_CONSTRAINT2(a,b) || BASE_CONSTRAINT1(c))
#define BASE_CONSTRAINT_A(a) BASE_CONSTRAINT1(a)
#define BASE_CONSTRAINT_C(a,b) BASE_CONSTRAINT2(a,b)
#define BASE_CONSTRAINT_B(a,b) BASE_CONSTRAINT2(a,b)


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

#include "../bitonic-all.cpp"



inline void init_px_py_btsp(){
	//cout<<"Standard dist "<<endl;
	px[0] = (TYPE)(rand()%10-19);
	py[0] = (TYPE)(rand()%10-19);
	for (int i=2;i<=N;i++) {
		px[i-1] = (TYPE)(px[i-2] + rand()%5+1);
		py[i-1] = (TYPE)(rand()%20-40);
	}
	for(int i=1;i<=N;i++){
		for(int j=1;j<=N;j++){
			Ddist(i,j) = MAXVAL;
		}		
	}
	Ddist(1,2) = d(1,2);
}

#define BL(i,j) BTSPL[((i)-1)*N+((j)-1)]
void bitonicLoop(TYPE* BTSPL){
	for(int i=1;i<=N;i++){
		for(int j=1;j<=N;j++){
			BL(i,j) = MAXVAL;
		}
	}
	BL(1,2) = d(1,2);
	for(int j=2;j<=N;j++){
		cilk_for( int i=1 ; i<=j-1 ; i++ ){
			if (i<j-1){
				BL(i,j) = BL(i,j-1) + d(i,j-1);
			}
			if(i==j-1){

				for(int k=1;k<i;k++){
					BL(i,j) = min(BL(i,j),BL(k,i)+d(k,i));
				}
			}
		}
	}
}
#ifdef DEBUG
#define pp(x) ((x>MAXVAL/2)?-1:x)
void printBTSP(TYPE* btsp){
	cout<<endl;
	if (N>20) return;
	cout.precision(4);
	for(int i=1;i<=N;i++){
		for(int j=1;j<=N;j++){
			cout<<(pp(btsp[(i-1)*N+(j-1)]))<<"\t";
		}
		cout<<endl;
	}
}

void checkError(TYPE* BTSPL){
	for(int i=1;i<=N;i++){
		for(int j=1;j<=N;j++){
			if (abs(BL(i,j) - Ddist(i,j)) > 0.0001){
				cout<<i<<"\t"<<j<<"\t"<<BL(i,j)<<"\t"<<Ddist(i,j)<<endl;
				exit(1);
			}
		}
	}
	cout<<"Checked "<<N*N<<" Values."<<endl;
}

void bitonicCheck() {
	//Use px,py to re-compute BitonicTSP locally and check if rec version is correct
	//printBTSP(BTSP);
	TYPE* BTSPL = ( TYPE* ) _mm_malloc(N * N * sizeof( TYPE ),ALIGNMENT);
	unsigned long long tstart1 = cilk_getticks();
	bitonicLoop(BTSPL);
	unsigned long long tend1 = cilk_getticks();
	//printBTSP(BTSPL);
	cout<<"LOOPDP\t"<<N<<"\t"<<B<<"\t"<<cilk_ticks_to_seconds(tend1-tstart1)<<endl;
	checkError(BTSPL);
	_mm_free(BTSPL);
}

#endif

int main(int argc, char *argv[]) {

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
	BTSP = ( TYPE* ) _mm_malloc(N * N * sizeof( TYPE ),ALIGNMENT);
	px = ( TYPE* ) _mm_malloc(N * sizeof( TYPE ),ALIGNMENT);
	py = ( TYPE* ) _mm_malloc(N * sizeof( TYPE ),ALIGNMENT);
	init_px_py_btsp();

	DEFBEGIN(BOTTOMJ) = 0;
	DEFEND(BOTTOMJ) =0;
	DEFINTERVALSTMT(K0);
	DEFBEGIN(K0) = 1;
	DEFEND(K0) = N+1;
	cout<<"VERSION\tN\tB\tTime(s)"<<endl;
	unsigned long long tstart;
	unsigned long long tend;
#ifdef CO
	tstart = cilk_getticks();
	funcA_rec(PARAM(K0));
	tend = cilk_getticks();
	cout<<"AUTO\t"<<N<<"\t"<<B<<"\t"<<cilk_ticks_to_seconds(tend-tstart)<<endl;
#endif

	//May check LOOPDP later here
#ifdef DEBUG
	bitonicCheck();
#else
#ifdef LOOPDP
	tstart = cilk_getticks();
	bitonicLoop(BTSP);
	tend = cilk_getticks();
	cout<<"LOOPDP\t"<<N<<"\t"<<B<<"\t"<<cilk_ticks_to_seconds(tend-tstart)<<endl;
#endif
#endif
#ifndef NNUM
	_mm_free(BTSP);
	_mm_free(px);
	_mm_free(py);

#endif
	exit(0);
}


