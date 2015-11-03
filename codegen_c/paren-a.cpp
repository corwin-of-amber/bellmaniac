//g++ -D N=1000
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

#define B 1
TYPE dist[N][N];

struct interval {
	TYPE begin;TYPE end;
};

#define FOR_FORWARD(i,K) for(TYPE i=K.begin;i<K.end;i++)
#define FOR_BACKWARD(i,K) for(TYPE i=K.end-1;i>=K.begin;i--)

#define FOR_A_loop_1(i,K) FOR_FORWARD(i,K)
#define FOR_A_loop_2(i,K) FOR_FORWARD(i,K)
#define FOR_A_loop_3(i,K) FOR_FORWARD(i,K)
#define FOR_B_loop_1(i,K) FOR_BACKWARD(i,K)
#define FOR_B_loop_2(i,K) FOR_FORWARD(i,K)
#define FOR_C_loop_1(i,K) FOR_FORWARD(i,K)
#define FOR_C_loop_2(i,K) FOR_FORWARD(i,K)
#define FOR_C_loop_3(i,K) FOR_FORWARD(i,K)

#define FORUNION(i,K,L,ZZ) for(TYPE i=K.begin;i<K.end;i++){ZZ};for(TYPE i=L.begin;i<L.end;i++){ZZ}
#define BASE_CONSTRAINT_A(a) (a.end-a.begin <= B)
#define BASE_CONSTRAINT_B(a,b) (BASE_CONSTRAINT_A(a) || BASE_CONSTRAINT_A(b))
#define BASE_CONSTRAINT_C(a,b,c) (BASE_CONSTRAINT_B(a,b) || BASE_CONSTRAINT_A(c))

void funcC_loop(interval K0, interval K1, interval K2) {

	FOR_C_loop_2(i, K0)
	{
		FOR_C_loop_3(j, K2)
		{

			TYPE t14 = MAXVAL;
			FOR_C_loop_1(k, K1)
			{
				if (i < k && k < j) {
					t14 = min(t14, dist[i][k]+dist[k][j]+w(i,k,j));
				}
			}

			dist[i][j] = min(t14, dist[i][j]);
		}
	}

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

	FOR_B_loop_1(i,J0)
	{
		FOR_B_loop_2(j,J1)
		{

			TYPE t21 = MAXVAL;
			FORUNION(k, J0, J1,
					if (i<k && k<j){ t21 = min(t21,dist[i][k]+dist[k][j]+w(i,k,j)); })

			dist[i][j] = min(t21, dist[i][j]);
		}
	}

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

	FOR_A_loop_2(i, J)
	{
		FOR_A_loop_3(j, J)
		{

			TYPE t16 = MAXVAL;
			FOR_A_loop_1(k, J)
			{
				if (i < k && k < j) {
					t16 = min(t16, dist[i][k]+dist[k][j]+w(i,k,j));
				}
			}

			dist[i][j] = min(t16, dist[i][j]);
		}
	}

}
void funcA_rec(interval J) {
	if (BASE_CONSTRAINT_A(J)) {
		funcA_loop(J);
		return;
	}
	interval J0 = { J.begin, (J.end + J.begin) / 2 };
	interval J1 = { J0.end, J.end };

	funcA_rec(J0);
	funcA_rec(J1);
	funcB_rec(J0, J1);
}

TYPE dorig[N][N];
TYPE dloop[N][N];
TYPE drec[N][N];
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
	cout << "ERROR: " << msg << "\ni\tj\torig\tloop\trec\n" << i << "\t" << j
			<< "\t" << dorig[i][j] << "\t" << dloop[i][j] << "\t" << drec[i][j]
			<< endl;
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
				printError("Values not the same", i, j);
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

	interval K0 = { 0 / N / 3 };
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
	dcopy(dorig, dist);
	funcA_loop(K0);
	if (N < 20)
		print_dist(dorig);
	dcopy(dist, dloop);

	dcopy(dorig, dist);
	funcA_rec(K0);
	if (N < 20)
		print_dist(dorig);
	dcopy(dist, drec);
	checkLoopRec("funcA");
}

int main(int argc, char *argv[]) {
	srand (time(NULL));cout<<"Random dist: "<<endl;

	for (int i=0;i<N;i++) {
		for (int j=0;j<N;j++) {
			if (i<j) {
				dorig[i][j] = (rand()%40)-20;
				cout<<i<<'\t'<<j<<'\t'<<dorig[i][j]<<endl;
			}
			else dorig[i][j] = MAXVAL;
		}
	}
	cout<<"funcC test: "<<endl;
	testC();
	cout<<"funcB test: "<<endl;
	testB();
	cout<<"funcA test: "<<endl;
	testA();
}
