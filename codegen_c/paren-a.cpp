/*
 * g++ -O3 -D N=2000 -D B=16 -o parena paren-a.cpp  && ./parena standard A-rec-debug
 *
 */
#include <cstdio>
#include <cstdlib>
#include <ctime>
#include <cassert>
#include <iostream>
#include "timerclass.h"
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

/* Min Max and Weight Function */
#define min(a,b) (a<b?a:b)
#define max(a,b) (a>b?a:b)
#define w(i, j, k) (((i*j*k)&7)) //weight function

#ifndef N
#define N 1000
#endif

#ifndef B
#define B 1
#endif
TYPE dist[N][N];

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
#define FOR_DIAG_I_LT_J_FWD_FWD(i,j,I,J,ZZ) FOR_VAR_FWD(of,0,SIZE(I)){FOR_VAR_FWD(ci,0,SIZE(J)-of){TYPE i = ci+DEFBEGIN(I); TYPE j = DEFBEGIN(J)+ci+of; ZZ}}

#define FOR_A_loop_1(i,K) FOR_FORWARD(i,K)
#define FOR_A_loop_2(i,j,I,J,ZZ) FOR_DIAG_I_LT_J_FWD_FWD(i,j,I,J,ZZ)
//FOR_FWD_FWD(i,j,I,J,ZZ) //needs to be upper_diag
#define FOR_A_loop_3(i,K) FOR_FORWARD(i,K)
#define FOR_B_loop_1(i,j,I,J,ZZ) FOR_BWD_FWD(i,j,I,J,ZZ)
#define FOR_C_loop_1(i,K) FOR_FORWARD(i,K)
#define FOR_C_loop_2(i,j,I,J,ZZ) FOR_FWD_FWD(i,j,I,J,ZZ)

#define FORUNION(i,K,L,ZZ) FOR_FORWARD(i,K){ZZ};FOR_FORWARD(i,L){ZZ}
#define BASE_CONSTRAINT_A(a) ((DEFEND(a)-DEFBEGIN(a)) <= B)
#define BASE_CONSTRAINT_B(a,b) (BASE_CONSTRAINT_A(a) || BASE_CONSTRAINT_A(b))
#define BASE_CONSTRAINT_C(a,b,c) (BASE_CONSTRAINT_B(a,b) || BASE_CONSTRAINT_A(c))
string distType = "";
string runType = "";
/*
 * Auto-generated Code
 */
void funcC_loop(DEFINTERVALFUNC(K0), DEFINTERVALFUNC(K1), DEFINTERVALFUNC(K2)) {

	FOR_C_loop_2(i, j, K0, K2,

			TYPE t310= MAXVAL; FOR_C_loop_1(k,K1){ if (i<k && k<j){ t310 = min(t310,dist[i][k]+dist[k][j]+w(i,k,j)); } }

			dist[i][j] = min(t310,dist[i][j]);)

}
void funcC_rec(DEFINTERVALFUNC(K0), DEFINTERVALFUNC(K1), DEFINTERVALFUNC(K2)) {
	if (BASE_CONSTRAINT_C(K0, K1, K2)) {
		funcC_loop(PARAM(K0), PARAM(K1), PARAM(K2));
		return;
	}
	DEFINTERVALSTMT(L4);
	DEFBEGIN(L4) = DEFBEGIN(K2);
	DEFEND(L4) = (DEFEND(K2) + DEFBEGIN(K2)) / 2;
	DEFINTERVALSTMT(L5);
	DEFBEGIN(L5) = DEFEND(L4);
	DEFEND(L5) = DEFEND(K2);
	DEFINTERVALSTMT(L2);
	DEFBEGIN(L2) = DEFBEGIN(K1);
	DEFEND(L2) = (DEFEND(K1) + DEFBEGIN(K1)) / 2;
	DEFINTERVALSTMT(L3);
	DEFBEGIN(L3) = DEFEND(L2);
	DEFEND(L3) = DEFEND(K1);
	DEFINTERVALSTMT(L0);
	DEFBEGIN(L0) = DEFBEGIN(K0);
	DEFEND(L0) = (DEFEND(K0) + DEFBEGIN(K0)) / 2;
	DEFINTERVALSTMT(L1);
	DEFBEGIN(L1) = DEFEND(L0);
	DEFEND(L1) = DEFEND(K0);

	funcC_rec(PARAM(L0), PARAM(L2), PARAM(L4));
	funcC_rec(PARAM(L0), PARAM(L3), PARAM(L4));
	funcC_rec(PARAM(L0), PARAM(L2), PARAM(L5));
	funcC_rec(PARAM(L0), PARAM(L3), PARAM(L5));
	funcC_rec(PARAM(L1), PARAM(L2), PARAM(L4));
	funcC_rec(PARAM(L1), PARAM(L3), PARAM(L4));
	funcC_rec(PARAM(L1), PARAM(L2), PARAM(L5));
	funcC_rec(PARAM(L1), PARAM(L3), PARAM(L5));
}

void funcB_loop(DEFINTERVALFUNC(J0), DEFINTERVALFUNC(J1)) {

	FOR_B_loop_1(i, j, J0, J1,

			TYPE t21= MAXVAL; FORUNION(k,J0,J1, if (i<k && k<j){ t21 = min(t21,dist[i][k]+dist[k][j]+w(i,k,j)); } )

			dist[i][j] = min(t21,dist[i][j]);)

}
void funcB_rec(DEFINTERVALFUNC(J0), DEFINTERVALFUNC(J1)) {
	if (BASE_CONSTRAINT_B(J0, J1)) {
		funcB_loop(PARAM(J0), PARAM(J1));
		return;
	}
	DEFINTERVALSTMT(K0);
	DEFBEGIN(K0) = DEFBEGIN(J0);
	DEFEND(K0) = (DEFEND(J0) + DEFBEGIN(J0)) / 2;
	DEFINTERVALSTMT(K1);
	DEFBEGIN(K1) = DEFEND(K0);
	DEFEND(K1) = DEFEND(J0);
	DEFINTERVALSTMT(K2);
	DEFBEGIN(K2) = DEFBEGIN(J1);
	DEFEND(K2) = (DEFEND(J1) + DEFBEGIN(J1)) / 2;
	DEFINTERVALSTMT(K3);
	DEFBEGIN(K3) = DEFEND(K2);
	DEFEND(K3) = DEFEND(J1);

	funcB_rec(PARAM(K1), PARAM(K2));
	funcC_rec(PARAM(K0), PARAM(K1), PARAM(K2));
	funcB_rec(PARAM(K0), PARAM(K2));
	funcC_rec(PARAM(K1), PARAM(K2), PARAM(K3));
	funcB_rec(PARAM(K1), PARAM(K3));
	funcC_rec(PARAM(K0), PARAM(K1), PARAM(K3));
	funcC_rec(PARAM(K0), PARAM(K2), PARAM(K3));
	funcB_rec(PARAM(K0), PARAM(K3));
}

void funcA_loop(DEFINTERVALFUNC(J)) {

	FOR_A_loop_2(i, j, J, J,

			TYPE t504= MAXVAL; FOR_A_loop_1(k,J){ if (i<k && k<j){ t504 = min(t504,dist[i][k]+dist[k][j]+w(i,k,j)); } }

			dist[i][j] = min(t504,dist[i][j]);)

}
void funcA_rec(DEFINTERVALFUNC(J)) {
	if (BASE_CONSTRAINT_A(J)) {
		funcA_loop(PARAM(J));
		return;
	}
	DEFINTERVALSTMT(J0);
	DEFBEGIN(J0) = DEFBEGIN(J);
	DEFEND(J0) = (DEFEND(J) + DEFBEGIN(J)) / 2;
	DEFINTERVALSTMT(J1);
	DEFBEGIN(J1) = DEFEND(J0);
	DEFEND(J1) = DEFEND(J);

	funcA_rec(PARAM(J0));
	funcA_rec(PARAM(J1));
	funcB_rec(PARAM(J0), PARAM(J1));
}

void parenthesis() {
	for (int t = 2; t < N; t++) {
		for (int i = 0; i < N - t; i++) {
			int j = t + i;
			TYPE D_ij = dist[i][j];
			for (int k = i + 1; k <= j; k++) {
				D_ij = min(D_ij, dist[i][k] + dist[k][j] + w(i,k,j));
			}
			dist[i][j] = D_ij;
		}
	}
}

/*
 * Testing infrastructure
 *
 */
TYPE dorig[N][N];
TYPE dloop[N][N];
TYPE drec[N][N];
TYPE dparen[N][N];
void print_dist(TYPE comp[N][N], bool PRINTALL = false) {
	cout << "dist[" << N << "][" << N << "]" << endl;
	int ctr = 0;
	for (int i = 0; i < N; i++) {
		for (int j = 0; j < N; j++) {
			if (PRINTALL || dist[i][j] != comp[i][j]) {
				cout << i << "\t" << j << "\t" << dist[i][j] << "\t"
						<< comp[i][j] << endl;
				ctr++;
			}
		}
		//cout<<endl;
	}
	cout << ctr << " Values changed here." << endl;
}
void dcopy(TYPE from[N][N], TYPE to[N][N]) {
	for (int i = 0; i < N; i++) {
		for (int j = 0; j < N; j++) {
			to[i][j] = from[i][j];
		}
	}
}

void printError(string msg, int i, int j) {
	cout << "ERROR: " << msg << "\ni\tj\torig\tloop\trec\tparen\n" << i << "\t"
			<< j << "\t" << dorig[i][j] << "\t" << dloop[i][j] << "\t"
			<< drec[i][j] << '\t' << dparen[i][j] << endl;
	exit(1);
}
void checkLoopRec(string func) {
	int ctr = 0;
	for (int i = 0; i < N; i++) {
		for (int j = 0; j < N; j++) {
			if (i >= j && dloop[i][j] != MAXVAL) {
				printError("loop didn't maintain MAXVAL", i, j);
			} else if (i >= j && drec[i][j] != MAXVAL) {
				printError("rec didn't maintain MAXVAL", i, j);
			} else if (dloop[i][j] != drec[i][j]) {
				printError("loop vs rec: values not the same", i, j);
			} else if (func == "funcA" && dloop[i][j] != dparen[i][j]) {
				printError("loop vs paren: values not the same", i, j);
			}
			if (dloop[i][j] != dorig[i][j])
				ctr++;
		}
	}
	cout << func << " " << ctr << " values updated correctly." << endl;
	//cout << "DONE" << endl;
}

void testC() {

	DEFINTERVALSTMT(K0);
	DEFBEGIN(K0) = 0;
	DEFEND(K0) = N / 3;
	DEFINTERVALSTMT(K1);
	DEFBEGIN(K1) = DEFEND(K0);
	DEFEND(K1) = (2 * N) / 3;
	DEFINTERVALSTMT(K2);
	DEFBEGIN(K2) = DEFEND(K1);
	DEFEND(K2) = N;
	dcopy(dorig, dist);
	funcC_loop(PARAM(K0), PARAM(K1), PARAM(K2));
	if (N < 20)
		print_dist(dorig);
	dcopy(dist, dloop);

	dcopy(dorig, dist);
	funcC_rec(PARAM(K0), PARAM(K1), PARAM(K2));
	if (N < 20)
		print_dist(dorig);
	dcopy(dist, drec);
	checkLoopRec("funcC");
}

void testB() {

	DEFINTERVALSTMT(K0);
	DEFBEGIN(K0) = 0;
	DEFEND(K0) = N / 2;
	DEFINTERVALSTMT(K1);
	DEFBEGIN(K1) = DEFEND(K0);
	DEFEND(K1) = N;
	dcopy(dorig, dist);
	funcB_loop(PARAM(K0), PARAM(K1));
	if (N < 20)
		print_dist(dorig);
	dcopy(dist, dloop);

	dcopy(dorig, dist);
	funcB_rec(PARAM(K0), PARAM(K1));
	if (N < 20)
		print_dist(dorig);
	dcopy(dist, drec);
	checkLoopRec("funcB");
}

void testA() {

	DEFINTERVALSTMT(K0);
	DEFBEGIN(K0) = 0;
	DEFEND(K0) = N;
	if (N < 20)
		cout << "loop run:" << endl;
	dcopy(dorig, dist);
	timerclass tc;
	tc.start();
	funcA_loop(PARAM(K0));
	tc.stop();
	tc.print("A-loop");
	if (N < 20)
		print_dist(dorig);
	dcopy(dist, dloop);
	if (N < 20)
		cout << "rec run:" << endl;
	dcopy(dorig, dist);
	tc.restart();
	funcA_rec(PARAM(K0));
	tc.stop();
	tc.print("A-rec");
	if (N < 20)
		print_dist(dorig);
	dcopy(dist, drec);
	if (N < 20)
		cout << "paren run:" << endl;
	dcopy(dorig, dist);
	parenthesis();
	if (N < 20)
		print_dist(dorig);
	dcopy(dist, dparen);

	checkLoopRec("funcA");
}

inline void testArec(bool debug) {
	DEFINTERVALSTMT(K0);
	DEFBEGIN(K0) = 0;
	DEFEND(K0) = N;
	dcopy(dorig, dist);
	timerclass tc;
	tc.start();
	funcA_rec(PARAM(K0));
	tc.stop();
	tc.print("A-rec");
	if (debug) {
		dcopy(dist, drec);
		dcopy(dorig, dist);
		timerclass tc;
		tc.start();
		parenthesis();
		tc.stop();
		tc.print("paren");
		dcopy(dist, dparen);

		dcopy(drec, dloop);
		checkLoopRec("DEBUG A-rec vs paren");
	}
}
int main(int argc, char *argv[]) {
	srand (time(NULL));if (argc != 3) {
		cout<<"Need two arguments: distType{random,standard} runType{A,B,C,A-rec}"<<endl;
	}
	distType = argv[1];
	runType = argv[2];
	if (distType == "random") {
		cout<<"Random dist "<<endl;
		for (int i=0;i<N;i++) {
			for (int j=0;j<N;j++) {
				if (i<j) {
					dorig[i][j] = (rand()%40)-20;
					if (N < 20) {
						cout<<i<<'\t'<<j<<'\t'<<dorig[i][j]<<endl;
					}
				}
				else dorig[i][j] = MAXVAL;
			}
		}
	}
	else if (distType == "standard") {
		cout<<"Standard dist "<<endl;

		for (int i=0;i<N;i++) {
			for (int j=0;j<N;j++) {
				if (j == i+1) {
					dorig[i][j] = i+1;
					if (N < 20) {
						cout<<i<<'\t'<<j<<'\t'<<dorig[i][j]<<endl;
					}
				}
				else dorig[i][j] = MAXVAL;
			}
		}
	}
	else {
		cout<<"Error: Invalid distType: "<<distType<<endl;
		exit(1);
	}

	if (runType == "C") {
		cout<<"funcC test: "<<endl;
		testC();
	}
	else if (runType == "B") {
		cout<<"funcB test: "<<endl;
		testB();
	}
	else if (runType == "A") {
		cout<<"funcA test: "<<endl;
		testA();
	}
	else if (runType == "A-rec") {
		testArec(false);
	}
	else if (runType == "A-rec-debug") {
		testArec(true);
	}
	else {
		cout<<"Invalid testType: "<<runType<<endl;
		exit(1);
	}
}
