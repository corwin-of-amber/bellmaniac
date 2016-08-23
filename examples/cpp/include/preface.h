
#include <cstdio>
#include <cstdlib>
#include <ctime>
#include <string>
#include <cassert>
#include <iostream>

#if defined __ICC || defined __ICL 
#define CILK
#endif

#ifdef CILK
#include <cilk/cilk.h>
#include <cilk/cilk_api.h>
#else
#include "cilk_stub.h"
#endif
#include "cilktime.h"
using namespace std;
#ifndef TYPE
#define TYPE int
#endif
#define ALIGNMENT 64

#ifdef STRUCTINTERVAL
struct interval {
	int begin;int end;
};
#define DEFINTERVALFUNC(I) interval I
#define DEFINTERVALSTMT(I) interval I
#define DEFBEGIN(I) I.begin
#define DEFEND(I) I.end
#define PARAM(I) I
#else
#define DEFINTERVALFUNC(I) int I##_begin, int I##_end
#define DEFINTERVALSTMT(I) int I##_begin, I##_end
#define DEFBEGIN(I) I##_begin
#define DEFEND(I) I##_end
#define PARAM(I) I##_begin, I##_end

#endif

#ifndef MAXVAL
#define MAXVAL int(1e9)
#endif

#define INITMIN MAXVAL

#define MINVAL -MAXVAL
#define INITMAX MINVAL



inline bool In(DEFINTERVALFUNC(I), int val) {
	return ((val) >= DEFBEGIN(I) && (val) < DEFEND(I));
}
#ifndef UNDEFINED
#define UNDEFINED MAXVAL
#endif
#define IS_UNDEFINED(x) ((x) == UNDEFINED) 
#define GUARDED(cond,val) ((cond) ? (val) : UNDEFINED) 
//inline int GUARDED(bool cond, int val) { return ((cond) ? (val) : UNDEFINED); }
inline int SLASH(int x, int y) { return (x != UNDEFINED) ? x : y; }

#define DEFINTERVALSTMT_LOWER(J0, J)   DEFINTERVALSTMT(J0); DEFBEGIN(J0) = DEFBEGIN(J); DEFEND(J0) = (DEFEND(J) + DEFBEGIN(J))/2;
#define DEFINTERVALSTMT_UPPER(J1, J)   DEFINTERVALSTMT(J1); DEFBEGIN(J1) = (DEFEND(J) + DEFBEGIN(J))/2; DEFEND(J1) = DEFEND(J);

#define DEFINTERVALSTMT_UNION(J, J0, J1)   DEFINTERVALSTMT(J); DEFBEGIN(J) = DEFBEGIN(J0); DEFEND(J) = DEFEND(J1);


#ifndef NNUM
#define NNEEDED 1
#ifndef DEFINEVARS
long long N = 1000;
TYPE *dist;
#else
extern long long N;
extern TYPE *dist;
#endif
#else
#define NNEEDED 0
#define N NNUM
#ifndef DEFINEVARS
TYPE dist[((long long)N)*N];
#else
extern TYPE dist[((long long)N)*N];
#endif
#endif

#ifndef B
#define BNEEDED 1
#ifndef DEFINEVARS
long long B = 64;
#else
extern long long B;
#endif
#else
#define BNEEDED 0
#endif
#ifndef Ddist
#define Ddist(i,j) dist[(i)*N + (j)]
#endif
#define psi(i,j) Ddist(i,j)
#define theta(i,j) Ddist(i,j)


#define LET(i,v) int i = v;

#define SIZE(I) (DEFEND(I)-DEFBEGIN(I))
#define FOR_FWD(i,b,e) for(int i=b;i<e;i++)
#define FOR_BWD(i,b,e) for(int i=e-1;i>=b;i--)


#define FORUNION(i,nK,mK,nL,mL,ZZ) FOR_VAR_FWD(i,nK,mK){ZZ};FOR_VAR_FWD(i,nL,mL){ZZ}

inline bool BASE_CONSTRAINT(DEFINTERVALFUNC(a)) {
	return ((DEFEND(a)-DEFBEGIN(a)) <= B);
}
inline bool BASE_CONSTRAINT(DEFINTERVALFUNC(a),DEFINTERVALFUNC(b)) {
	return (BASE_CONSTRAINT(PARAM(a)) || BASE_CONSTRAINT(PARAM(b)));
}
inline bool BASE_CONSTRAINT(DEFINTERVALFUNC(a),DEFINTERVALFUNC(b),DEFINTERVALFUNC(c)) {
	return (BASE_CONSTRAINT(PARAM(a)) || BASE_CONSTRAINT(PARAM(b)) || BASE_CONSTRAINT(PARAM(c)));
}

#define psiCopyOpt(i,j,I,J) V[((j)-DEFBEGIN(J))*B + ((i)-DEFBEGIN(I))]

inline void copy_dist_part(TYPE* V,DEFINTERVALFUNC(II),DEFINTERVALFUNC(JJ)){
	for(int i=DEFBEGIN(II);i<DEFEND(II);i++){
		for(int j=DEFBEGIN(JJ);j<DEFEND(JJ);j++){
			psiCopyOpt(i,j,II,JJ) = psi(i,j);
		}
	}
}

//Plain Copy Optimization is without transpose
#define psiCopyOptPlain(i,j,I,J) V[((j)-DEFBEGIN(J)) + ((i)-DEFBEGIN(I))*B]

inline void copy_dist_part_plain(TYPE* V,DEFINTERVALFUNC(II),DEFINTERVALFUNC(JJ)){
	for(int i=DEFBEGIN(II);i<DEFEND(II);i++){
		for(int j=DEFBEGIN(JJ);j<DEFEND(JJ);j++){
			psiCopyOptPlain(i,j,II,JJ) = Ddist(i,j);

		}
	}
}

#define succ(i,j) ((j) == (i+1))

inline void argParser(int argc, char *argv[]){
	argv++;
	argc--;
	if (argc > 0){
		N = atoi(argv[0]);
	}
#ifndef B
	if (argc > 1){
		B = atoi(argv[1]);
	}
#else
	if (B != atoi(argv[1])){
		cout<<"B has been pre-set to "<<B<<endl;
		exit(1);
	}
#endif
	if (argc > 2){
		if (0!= __cilkrts_set_param("nworkers",argv[2])) {
            cout<<"Failed to set worker count\n";
            exit(1);
		}
	}

}