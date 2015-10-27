#include <cstdio>
#include <cstdlib>
#ifndef TYPE
#define TYPE int
#endif

#define MAXVAL 1000000

/* Min Max and Weight Function */
#define min(a,b) (a<b?a:b)
#define max(a,b) (a>b?a:b)
#define w(i, j, k) (((i*j*k)&7)) //weight function

#define N 100

int B;
int dist[N][N];

#define FOR(i,n,m) for(int i=n;i<m;i++)
#define BASE_CONSTRAINT(a,b,c,d,e,f) (b-a <= B && d-c<= B && f-e <= B)
//DEFINITIONS and HEADERS
void funcC_loop(int K0_start, int K0_end, int K1_start, int K1_end,
		int K2_start, int K2_end) {

	FOR(i, K0_start, K0_end)
	{
		FOR(j, K2_start, K2_end)
		{

			TYPE t14 = MAXVAL;
			FOR(k, K1_start, K1_end)
			{
				t14 = min(t14, dist[i][k] + dist[k][j] + w(i, k, j));
			}

			dist[i][j] = min(t14, dist[i][j]);
		}
	}

}

void funcC_rec(int K0_start, int K0_end, int K1_start, int K1_end, int K2_start,
		int K2_end) {
	if (BASE_CONSTRAINT(K0_start, K0_end, K1_start, K1_end, K2_start, K2_end)) {
		funcC_loop(K0_start, K0_end, K1_start, K1_end, K2_start, K2_end);
		return;
	}
	int L0_start;
	int L0_end;
	int L1_start;
	int L1_end;
	int L2_start;
	int L2_end;
	int L3_start;
	int L3_end;
	int L4_start;
	int L4_end;
	int L5_start;
	int L5_end;
	L4_start = K2_start;
	L4_end = (K2_end - K2_start) / 2;
	L5_start = L4_end;
	L5_end = K2_end;
	L2_start = K1_start;
	L2_end = (K1_end - K1_start) / 2;
	L3_start = L2_end;
	L3_end = K1_end;
	L0_start = K0_start;
	L0_end = (K0_end - K0_start) / 2;
	L1_start = L0_end;
	L1_end = K0_end;

	funcC_rec(L0_start, L0_end, L2_start, L2_end, L4_start, L4_end);
	funcC_rec(L0_start, L0_end, L3_start, L3_end, L4_start, L4_end);
	funcC_rec(L0_start, L0_end, L2_start, L2_end, L5_start, L5_end);
	funcC_rec(L0_start, L0_end, L3_start, L3_end, L5_start, L5_end);
	funcC_rec(L1_start, L1_end, L2_start, L2_end, L4_start, L4_end);
	funcC_rec(L1_start, L1_end, L3_start, L3_end, L4_start, L4_end);
	funcC_rec(L1_start, L1_end, L2_start, L2_end, L5_start, L5_end);
	funcC_rec(L1_start, L1_end, L3_start, L3_end, L5_start, L5_end);
}

int main(int argc, char *argv[]) {
	B=0;
}

