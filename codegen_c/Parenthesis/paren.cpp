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
#define DEFINEVARS
#include "preface.h"
#include "input.h"

/*
* Auto-generated Code
*/

//#include "../paren-scala.cpp"
void funcA_rec(DEFINTERVALFUNC(J));

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
	cout<<"VERSION\tN\tB\tTime(s)"<<endl;
	cout<<"AUTO\t"<<N<<"\t"<<B<<"\t"<<cilk_ticks_to_seconds(tend-tstart)<<endl;
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
		cout<<"LOOPDP\t"<<N<<"\t"<<B<<"\t"<<cilk_ticks_to_seconds(tend-tstart)<<endl;
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


