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
/*
#include <cilk/cilk.h>
#include <cilk/cilk_api.h>
#include "cilktime.h"
*/
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
struct interval {
	TYPE begin;TYPE end;
};
#define DEFINTERVALFUNC(I) interval I
#define DEFINTERVALSTMT(I) interval I
#define DEFBEGIN(I) I.begin
#define DEFEND(I) I.end
#define PARAM(I) I
#endif

#define MAXVAL int(1e9)
#define INITMIN MAXVAL
#define UNDEFINED MAXVAL

inline bool IN(DEFINTERVALFUNC(I), int val) {
	return ((val) >= DEFBEGIN(I) && (val) < DEFEND(I));
}

#define GUARDED(cond, val) ((cond) ? (val) : UNDEFINED)

#define DEFINTERVALSTMT_LOWER(J0, J)   DEFINTERVALSTMT(J0); DEFBEGIN(J0) = DEFBEGIN(J); DEFEND(J0) = (DEFEND(J) + DEFBEGIN(J))/2;
#define DEFINTERVALSTMT_UPPER(J1, J)   DEFINTERVALSTMT(J1); DEFBEGIN(J1) = (DEFEND(J) + DEFBEGIN(J))/2; DEFEND(J1) = DEFEND(J);

#define DEFINTERVALSTMT_UNION(J, J0, J1)   DEFINTERVALSTMT(J); DEFBEGIN(J) = DEFBEGIN(J0); DEFEND(J) = DEFEND(J1);


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
