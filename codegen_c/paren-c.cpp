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

#define FOR(i,K) for(TYPE i=K.begin;i<K.end;i++)
#define BASE_CONSTRAINT(a,b,c) (a.end-a.begin <= B || b.end-b.begin <= B || c.end-c.begin <= B)


void funcC_loop(interval K0, interval K1, interval K2) {
	interval L4 = { K2.begin, (K2.end + K2.begin) / 2 };
	interval L5 = { L4.end, K2.end };
	interval L2 = { K1.begin, (K1.end + K1.begin) / 2 };
	interval L3 = { L2.end, K1.end };
	interval L0 = { K0.begin, (K0.end + K0.begin) / 2 };
	interval L1 = { L0.end, K0.end };

	FOR(i,K0)
	{
		FOR(j,K2)
		{

			TYPE t148 = MAXVAL;
			FOR(k,K1)
			{
				t148 = min(t148, dist[i][k]+dist[k][j]+w(i,k,j));
			}

			dist[i][j] = min(t148, dist[i][j]);
		}
	}

}

void funcC_rec(interval K0, interval K1, interval K2) {
	if (BASE_CONSTRAINT(K0, K1, K2)) {
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
	cout<<ctr<<" Values changed."<<endl;
}
void dcopy(TYPE from[N][N], TYPE to[N][N]) {
	for (int i = 0; i < N; i++) {
		for (int j = 0; j < N; j++) {
			to[i][j] = from[i][j];
		}
	}
}
void testC(){

	srand (time(NULL));for (int i=0;i<N;i++) {
		for (int j=0;j<N;j++) {
			dorig[i][j] = (rand()%40)-20;
		}
	}
	interval K0,K1,K2;
	K0.begin = 0; K0.end = N/3;
	K1.begin = K0.end; K1.end = (2*N)/3;
	K2.begin = K1.end; K2.end = N;
	dcopy(dorig,dist);
	//if (N<20) print_dist(dist,true);
	funcC_loop(K0,K1,K2);
	if (N<20) print_dist(dorig);
	dcopy(dist,dloop);

	dcopy(dorig,dist);
	funcC_rec(K0,K1,K2);
	if (N<20) print_dist(dorig);
	dcopy(dist,drec);
	int ctr = 0;
	for (int i=0;i<N;i++) {
		for (int j=0;j<N;j++) {
			if(dloop[i][j] != drec[i][j]) {
				cout<<"Not the same: "<<i<<" "<<j<<endl;
				exit(1);
			}
			if (dloop[i][j] != dorig[i][j]) ctr++;
		}
	}
	cout<<ctr<<" values updated by both functions correctly."<<endl;
	cout<<"DONE"<<endl;
}


int main(int argc, char *argv[]) {
	testC();
}
