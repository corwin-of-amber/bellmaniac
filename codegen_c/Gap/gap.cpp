/*
* Compilation using icc on windows RTODO
*/
#include <cstdio>
#include <cstdlib>
#include <string>
#include <ctime>
#include <cassert>
#include <iostream>
#define DEFINEVARS
#include "preface.h"
#include "input.h"

int *X, *Y;

void funcA_rec(DEFINTERVALFUNC(I), DEFINTERVALFUNC(J));


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
#ifndef _DEBUG
	if (argc > 1){
		if (0!= __cilkrts_set_param("nworkers",argv[1])) {
			cout<<"Failed to set worker count\n";
			return 1;
		}
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
	cout<<"VERSION\tN\tB\tTime(s)"<<endl;
	cout<<"AUTO\t"<<N<<"\t"<<B<<"\t"<<cilk_ticks_to_seconds(tend-tstart)<<endl;
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
		cout<<"LOOPDP\t"<<N<<"\t"<<B<<"\t"<<cilk_ticks_to_seconds(tend-tstart)<<endl;
		checkForError("AUTO vs LOOPDP");
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


