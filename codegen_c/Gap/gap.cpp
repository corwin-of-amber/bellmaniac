/*
* Compilation using icc on windows RTODO
*/
#include <cstdio>
#include <cstdlib>
#include <string>
#include <ctime>
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
#define UNDEF MAXVAL

/* Min Max and Weight Function */
//#define min(a,b) (a<b?a:b)
//#define max(a,b) (a>b?a:b)
#define w(q, j) (q+j) // weight function for delete
#define w_prime(p, i) (p+i) // weight function for insert
#define Sn(x, y) ((x==y)?0:1) // match or substitute cost
int *X, *Y;
#define Gap dist
#define S(i,j) Sn(X[i], Y[j])
#define LET(i,v) int i = v;
#define NOP 
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


struct interval {
	TYPE begin;TYPE end;
};
#define FOR_VAR_FWD(i,n,m) for(TYPE i=n;i<m;i++)
#define FOR_VAR_BWD(i,n,m) for(TYPE i=m-1;i>=n;i--)

#define SIZE(I) (DEFEND(I)-DEFBEGIN(I))
#define FOR_FORWARD(i,K) for(TYPE i=DEFBEGIN(K);i<DEFEND(K);i++)
#define FOR_BACKWARD(i,K) for(TYPE i=DEFEND(K)-1;i>=DEFBEGIN(K);i--)
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
#define FOR_A_loop_4(i,n,m) FOR_VAR_FWD(i,n,m)

#define FOR_A_rec_1(i,n,m) FOR_VAR_FWD(i,n,m)
#define FOR_A_rec_2(i,n,m) FOR_VAR_FWD(i,n,m)

#define FOR_B_loop_3(i,n,m) FOR_VAR_BWD(i,n,m)
#define FOR_B_loop_4(i,n,m) FOR_VAR_FWD(i,n,m)
#define FOR_B_loop_2(i,n,m) FOR_VAR_FWD(i,n,m)
#define FOR_B_loop_1(i,n,m) FOR_VAR_FWD(i,n,m)
//#define FOR_B_loop_1(i,j,I,J,ZZ) FOR_BWD_FWD(i,j,I,J,ZZ)

#define FOR_B_rec_1(i,n,m) FOR_VAR_FWD(i,n,m)
#define FOR_B_rec_2(i,n,m) FOR_VAR_FWD(i,n,m)
#define FOR_B_rec_3(i,n,m) FOR_VAR_FWD(i,n,m)
#define FOR_B_rec_4(i,n,m) FOR_VAR_FWD(i,n,m)

#define FOR_C_loop_1(i,n,m) FOR_VAR_FWD(i,n,m)
#define FOR_C_loop_2(i,n,m) FOR_VAR_FWD(i,n,m)
#define FOR_C_loop_3(i,n,m) FOR_VAR_FWD(i,n,m)

#define FOR_C_rec_1(i,n,m) FOR_VAR_FWD(i,n,m)
#define FOR_C_rec_2(i,n,m) FOR_VAR_FWD(i,n,m)
#define FOR_C_rec_3(i,n,m) FOR_VAR_FWD(i,n,m)
#define FOR_C_rec_4(i,n,m) FOR_VAR_FWD(i,n,m)
//#define FOR_C_loop_2(i,j,I,J,ZZ) FOR_FWD_FWD(i,j,I,J,ZZ)

#define FORUNION(i,nK,mK,nL,mL,ZZ) FOR_VAR_FWD(i,nK,mK){ZZ};FOR_VAR_FWD(i,nL,mL){ZZ}

#define BASE_CONSTRAINT1(a) ((DEFEND(a)-DEFBEGIN(a)) <= B)
#define BASE_CONSTRAINT2(a,b) (BASE_CONSTRAINT1(a) || BASE_CONSTRAINT1(b))
#define BASE_CONSTRAINT3(a,b,c) (BASE_CONSTRAINT2(a,b) || BASE_CONSTRAINT1(c))
#define BASE_CONSTRAINT_A(a,b) BASE_CONSTRAINT2(a,b)
#define BASE_CONSTRAINT_C(a,b,c) BASE_CONSTRAINT3(a,b,c)
#define BASE_CONSTRAINT_B(a,b,c) BASE_CONSTRAINT_C(a,b,c)
#define INSET(i,I) ((i) >= DEFBEGIN(I) && (i) < DEFEND(I)) 
/*
* Auto-generated Code
*/

#include "..\gap-all.cpp"

#ifdef DEBUG
void print_problem(){
	cout<<"X:";
	for(int i=0;i<N;i++) cout<<((char)X[i]);
	cout<<endl;
	cout<<"Y:";
	for(int i=0;i<N;i++) cout<<((char)Y[i]);
	cout<<endl;
	cout<<"dist:"<<endl;
	for (int i=0;i<N;i++){
		for (int j=0;j<N;j++){
			if (dist[i*N+j] == UNDEF){
				cout<<"I"<<" ";
			}
			else cout<<dist[i*N+j]<<" ";
		}
		cout<<endl;
	}
	cout<<"S(i,j):"<<endl;
	for (int i=0;i<N;i++){
		for (int j=0;j<N;j++){
			cout<<S(i,j)<<" ";
		}
		cout<<endl;
	}


}
void gaploop() {
	int n = N-1;
	TYPE* G = dist;
	int NP = N;
	for (int t = 2; t <= n; t++) {
        // Solving upper triangle
#ifdef _DEBUG
		for(int i = 1; i<t; i++)
#else
		cilk_for(int i = 1; i<t; i++)
#endif
		{
            int j = t - i;
            TYPE G_ij = G[(i - 1)*(NP) + (j - 1)] + Sn(X[i], Y[j]);
            TYPE *uu = G+i*(NP);
#pragma ivdep
            for (int q = 0; q<j; q++)
            {
                G_ij = min(G_ij, *uu + w(q, j));
                uu++;
            }
#pragma ivdep
            for (int p = 0; p<i; p++)
            {
                G_ij = min(G_ij, G[p*(NP) + j] + w_prime(p, i));
            }
            G[i*(NP) + j] = G_ij;
        }
        
    }
    //Solving lower triangle
    int end = n + n + 1;
    for (int t = n + 1; t<end; t++) {
#ifdef _DEBUG
		for(int i = n; i >= t - n; i--)
#else
		cilk_for(int i = n; i >= t - n; i--)
#endif
        {
            int j = t - i;
            TYPE G_ij = G[(i - 1)*(NP) + (j - 1)] + Sn(X[i], Y[j]);
            TYPE *uu = G +i*(NP);
#pragma ivdep
            for (int q = 0; q<j; q++)
            {
                G_ij = min(G_ij, *uu+ w(q, j));
                uu++;
            }
#pragma ivdep
            for (int p = 0; p<i; p++)
            {
                G_ij = min(G_ij, G[p*(NP) + j] + w_prime(p, i));
            }
            
            G[i*(NP) + j] = G_ij;
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
	cout << "ERROR: " << msg << "\ni\tj\trec\tgap\n" << i << "\t"
		<< j << "\t" << drec[i*N + j] << '\t' << Ddist(i,j) << endl;
	exit(1);
}
void checkForError(string func) {
	int ctr = 0;
	for (int i = 0; i < N; i++) {
		for (int j = 0; j < N; j++) {
			if (N<20 && (drec[i*N + j] != dorig[i*N + j])){
				cout << i << "\t"
					<< j << "\t"<< dorig[i*N + j]<<"\t" << drec[i*N + j] << '\t' << Ddist(i,j) << endl;
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
inline void init_xy(){
	char a = 'A';
	int n = N;
    for (int i = 0; i < n; i++) {
        X[i] = rand() % 4 + a;
        
    }
    for (int i = 0; i < n; i++) {
        Y[i] = rand() % 4 + a;
        
    }
	if (N==2){
		X[0] = 'A';
		X[1] = 'C';
		Y[0] = 'C';
		Y[1] = 'C';
	}
}
inline void init_dist(){
	for (int i = 1; i < N; i++) {
		for (int j = 1; j < N; j++) {
			Ddist(i,j) = UNDEF;
		}
	}
	for (int i = 1; i < N; i++) {
        Ddist(i,0) = w(i, 0);
		Ddist(0,i) = w_prime(0,i);
    }
	Ddist(0,0) = 0;

#ifdef RANDOMDIST
	for (int i=0;i<N;i++) {
		for (int j=0;j<N;j++) {
				Ddist(i,j) = rand()%40;
				if (N < 20) {
					cout<<i<<'\t'<<j<<'\t'<<Ddist(i,j)<<endl;
				}
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
	

	srand ((unsigned int)time(NULL));
#ifndef NNUM
	dist = ( TYPE* ) _mm_malloc(N * N * sizeof( TYPE ),ALIGNMENT);
	X = ( TYPE* ) _mm_malloc(N * sizeof( TYPE ),ALIGNMENT);
	Y = ( TYPE* ) _mm_malloc(N * sizeof( TYPE ),ALIGNMENT);
#endif
	cout<< "p="<<__cilkrts_get_nworkers()<<",N="<<N<<",B="<<B<<endl;
	init_xy();
	init_dist();
#ifdef DEBUG
#ifdef RANDOMDIST
	dorig = ( TYPE* ) _mm_malloc(N * N * sizeof( TYPE ),ALIGNMENT);
	dcopy(dist,dorig);
#endif
	
	if (N<20)
	print_problem();
	
#endif 
	DEFINTERVALSTMT(J);
	DEFBEGIN(J) = 0;
	DEFEND(J) = N;


	DEFINTERVALSTMT(K);
	DEFBEGIN(K) = 0;
	DEFEND(K) = N/2;

	DEFINTERVALSTMT(L);
	DEFBEGIN(L) = N/2;
	DEFEND(L) = N;

	
	unsigned long long tstart = cilk_getticks();
	funcA_rec(PARAM(J),PARAM(J));
	unsigned long long tend = cilk_getticks();
	cout<<"REC\t"<<N<<"\t"<<cilk_ticks_to_seconds(tend-tstart)<<endl;
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
		//TODO: gaploop(); //change this back for A
		gaploop();
		unsigned long long tend = cilk_getticks();
		cout<<"gap\t"<<N<<"\t"<<cilk_ticks_to_seconds(tend-tstart)<<endl;
		checkForError("loop vs gap");
	}
	_mm_free(dorig);
	_mm_free(drec);

#endif
#ifndef NNUM
	_mm_free(dist);
	_mm_free(X);
	_mm_free(Y);
#endif
	exit(0);
}


