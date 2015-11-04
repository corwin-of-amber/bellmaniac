/*
 * Run as: g++ -D N=100 -D B=5 -o parena paren-a.cpp
 * ./parena random
 * ./parena optimal
 */
#include <cstdio>
#include <cstdlib>
#include <ctime>
#include <cassert>
#include <iostream>
using namespace std;
#ifndef TYPE
#define TYPE int
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

#define SIZE(I) (I.end-I.begin)
#define FOR_FORWARD(i,K) for(TYPE i=K.begin;i<K.end;i++)
#define FOR_BACKWARD(i,K) for(TYPE i=K.end-1;i>=K.begin;i--)
#define FOR_FWD_FWD(i,j,I,J,ZZ) FOR_FORWARD(i,I){FOR_FORWARD(j,J){ZZ}}
#define FOR_FWD_BWD(i,j,I,J,ZZ) FOR_FORWARD(i,I){FOR_BACKWARD(j,J){ZZ}}
#define FOR_BWD_FWD(i,j,I,J,ZZ) FOR_BACKWARD(i,I){FOR_FORWARD(j,J){ZZ}}
#define FOR_BWD_BWD(i,j,I,J,ZZ) FOR_BACKWARD(i,I){FOR_BACKWARD(j,J){ZZ}}

//SIZE(I) == SIZE(J)
#define FOR_DIAG_I_LT_J_FWD_FWD(i,j,I,J,ZZ) FOR_VAR_FWD(of,0,SIZE(I)){FOR_VAR_FWD(ci,0,SIZE(J)-of){TYPE i = ci+I.begin; TYPE j = J.begin+ci+of; ZZ}}

#define FOR_A_loop_1(i,K) FOR_FORWARD(i,K)
#define FOR_A_loop_2(i,j,I,J,ZZ) FOR_DIAG_I_LT_J_FWD_FWD(i,j,I,J,ZZ)
//FOR_FWD_FWD(i,j,I,J,ZZ) //needs to be upper_diag
#define FOR_A_loop_3(i,K) FOR_FORWARD(i,K)
#define FOR_B_loop_1(i,j,I,J,ZZ) FOR_BWD_FWD(i,j,I,J,ZZ)
#define FOR_C_loop_1(i,K) FOR_FORWARD(i,K)
#define FOR_C_loop_2(i,j,I,J,ZZ) FOR_FWD_FWD(i,j,I,J,ZZ)

#define FORUNION(i,K,L,ZZ) FOR_FORWARD(i,K){ZZ};FOR_FORWARD(i,L){ZZ}
#define BASE_CONSTRAINT_A(a) ((a.end-a.begin) <= B)
#define BASE_CONSTRAINT_B(a,b) (BASE_CONSTRAINT_A(a) || BASE_CONSTRAINT_A(b))
#define BASE_CONSTRAINT_C(a,b,c) (BASE_CONSTRAINT_B(a,b) || BASE_CONSTRAINT_A(c))
string distType = "random";

/*
 * Auto-generated Code
 */

void funcC_loop(interval K0, interval K1, interval K2) {

	FOR_C_loop_2(i, j, K0, K2,

			TYPE t14= MAXVAL; FOR_C_loop_1(k,K1){ if (i<k && k<j){ t14 = min(t14,dist[i][k]+dist[k][j]+w(i,k,j)); } }

			dist[i][j] = min(t14,dist[i][j]);

			)

}
void funcC_rec(interval K0, interval K1, interval K2) {
	if (BASE_CONSTRAINT_C(K0, K1, K2)) {
		funcC_loop(K0, K1, K2);
		return;
	}
	interval L4 = { K2.begin, (K2.end + K2.begin) / 2 };
	interval L5 = { L4.end, K2.end };
	interval L2 = { K1.begin, (K1.end + K1.begin) / 2 };
	interval L3 = { L2.end, K1.end };
	interval L0 = { K0.begin, (K0.end + K0.begin) / 2 };
	interval L1 = { L0.end, K0.end };

	funcC_rec(L0, L2, L4);
	funcC_rec(L0, L3, L4);
	funcC_rec(L0, L2, L5);
	funcC_rec(L0, L3, L5);
	funcC_rec(L1, L2, L4);
	funcC_rec(L1, L3, L4);
	funcC_rec(L1, L2, L5);
	funcC_rec(L1, L3, L5);
}

void funcB_loop(interval J0, interval J1) {

	FOR_B_loop_1(i, j, J0, J1,

			TYPE t21= MAXVAL; FORUNION(k,J0,J1, if (i<k && k<j){ t21 = min(t21,dist[i][k]+dist[k][j]+w(i,k,j)); } )

			dist[i][j] = min(t21,dist[i][j]);

			)

}
void funcB_rec(interval J0, interval J1) {
	if (BASE_CONSTRAINT_B(J0, J1)) {
		funcB_loop(J0, J1);
		return;
	}
	interval K0 = { J0.begin, (J0.end + J0.begin) / 2 };
	interval K1 = { K0.end, J0.end };
	interval K2 = { J1.begin, (J1.end + J1.begin) / 2 };
	interval K3 = { K2.end, J1.end };

	funcB_rec(K1, K2);
	funcC_rec(K0, K1, K2);
	funcB_rec(K0, K2);
	funcC_rec(K1, K2, K3);
	funcB_rec(K1, K3);
	funcC_rec(K0, K1, K3);
	funcC_rec(K0, K2, K3);
	funcB_rec(K0, K3);
}

void funcA_loop(interval J) {

	FOR_A_loop_2(i, j, J, J,

			TYPE t16= MAXVAL;

			FOR_A_loop_1(k,J){ if (i<k && k<j){ t16 = min(t16,dist[i][k]+dist[k][j]+w(i,k,j)); } }

			dist[i][j] = min(t16,dist[i][j]);)

}
void funcA_rec(interval J) {
	//cout<<"recA:\t["<<J.begin<<"\t"<<J.end<<")"<<endl;
	if (BASE_CONSTRAINT_A(J)) {
		//cout<<"recA calling loopA:\t["<<J.begin<<"\t"<<J.end<<")"<<endl;

		funcA_loop(J);
		return;
	}
	interval J0 = { J.begin, (J.end + J.begin) / 2 };
	interval J1 = { J0.end, J.end };

	funcA_rec(J0);
	funcA_rec(J1);
	funcB_rec(J0, J1);
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
	cout << ctr << " values updated by both " << func << " functions correctly."
			<< endl;
	//cout << "DONE" << endl;
}

void testC() {

	interval K0 = { 0, N / 3 };
	interval K1 = { K0.end, (2 * N) / 3 };
	interval K2 = { K1.end, N };
	dcopy(dorig, dist);
	funcC_loop(K0, K1, K2);
	if (N < 20)
		print_dist(dorig);
	dcopy(dist, dloop);

	dcopy(dorig, dist);
	funcC_rec(K0, K1, K2);
	if (N < 20)
		print_dist(dorig);
	dcopy(dist, drec);
	checkLoopRec("funcC");
}

void testB() {

	interval K0 = { 0, N / 2 };
	interval K1 = { K0.end, N };
	dcopy(dorig, dist);
	funcB_loop(K0, K1);
	if (N < 20)
		print_dist(dorig);
	dcopy(dist, dloop);

	dcopy(dorig, dist);
	funcB_rec(K0, K1);
	if (N < 20)
		print_dist(dorig);
	dcopy(dist, drec);
	checkLoopRec("funcB");
}

void testA() {

	interval K0 = { 0, N };
	if (N < 20)
		cout << "loop run:" << endl;
	dcopy(dorig, dist);
	funcA_loop(K0);
	if (N < 20)
		print_dist(dorig);
	dcopy(dist, dloop);
	if (N < 20)
		cout << "rec run:" << endl;
	dcopy(dorig, dist);
	funcA_rec(K0);
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

int main(int argc, char *argv[]) {
	srand (time(NULL));

if	(argc > 1) {
		distType = argv[1];
	}
	if (distType == "random") {
		cout<<"Random dist: "<<endl;

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
	else if (distType == "optimal") {
		cout<<"Optimal dist: "<<endl;

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
	else if (distType == "fixed5") {
		cout<<"Fixed dist: "<<endl;
		if (N!=5) {
			cout<<"Error: N must be 5!"<<endl;
			exit(1);
		}
		for (int i=0;i<N;i++) {
			for (int j=0;j<N;j++) {
				dorig[i][j] = MAXVAL;
			}
		}
		dorig[0][1]=19;
		dorig[0][2]=0;
		dorig[0][3]=14;
		dorig[0][4]=-14;
		dorig[1][2]=-10;
		dorig[1][3]=5;
		dorig[1][4]=-12;
		dorig[2][3]=-7;
		dorig[2][4]=14;
		dorig[3][4]=-12;
		for (int i=0;i<N;i++) {
			for (int j=0;j<N;j++) {
				if (i<j) cout<<i<<'\t'<<j<<'\t'<<dorig[i][j]<<endl;
			}
		}
	}
	else {
		cout<<"Error: Invalid distType"<<endl;
		exit(1);
	}

	if (distType != "fixed5") {
		cout<<"funcC test: "<<endl;
		testC();
		cout<<"funcB test: "<<endl;
		testB();
	}
	cout<<"funcA test: "<<endl;
	testA();
}
