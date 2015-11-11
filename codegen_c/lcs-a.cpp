/*
 * g++ -o lcs -D N=15 -D M=15 -D B=4 -O3 lcs-a.cpp  && ./lcs
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
#define UNDEF (-MAXVAL)
#define IS_UNDEF(a) (a < -50000)
/* Min Max and Weight Function */
#define min(a,b) (a<b?a:b)
#define max(a,b) (a>b?a:b)
#define OMAX(a,b) ((IS_UNDEF(a) || IS_UNDEF(b))?UNDEF:max(a,b))
#define w(i, j, k) (((i*j*k)&7)) //weight function
#define INSET(i,I) (i >= DEFBEGIN(I) && i < DEFEND(I))
#define GETDEF(a,b) ((!IS_UNDEF(a))?a:b)

#ifndef N
#define N 100
#endif

#ifndef M
#define M 100
#endif

#ifndef B
#define B 16
#endif

TYPE dist[N][M];
bool delta[N][M];
#define DELTA(i,j) (delta[i][j])

struct interval {
	TYPE begin;TYPE end;
};
#define FOR_VAR_FWD(i,n,m) for(TYPE i=n;i<m;i++)
#define FOR_VAR_BWD(i,n,m) for(TYPE i=m-1;i>=n;i--)

#define SIZE(I) (DEFEND(I)-DEFBEGIN(I))
#define FOR_FORWARD(i,K) for(TYPE i=DEFBEGIN(K);i<DEFEND(K);i++)
#define FOR_BACKWARD(i,K) for(TYPE i=DEFEND(K)-1;i>=DEFBEGIN(K);i--)

#define BASE_CONSTRAINT(a) ((DEFEND(a)-DEFBEGIN(a)) <= B)
#define BASE_CONSTRAINT_A(a,b) (BASE_CONSTRAINT(a) || BASE_CONSTRAINT(b))

#define FOR_A_loop_1(i, I) FOR_FORWARD(i,I)
#define FOR_A_loop_2(i, I) FOR_FORWARD(i,I)
#define FOR_A_rec_1(i, I) FOR_FORWARD(i,I)
#define FOR_A_rec_2(i, I) FOR_FORWARD(i,I)
#define FOR_A_rec_3(i, I) FOR_FORWARD(i,I)
#define FOR_A_rec_4(i, I) FOR_FORWARD(i,I)
#define FOR_A_rec_5(i, I) FOR_FORWARD(i,I)
#define FOR_A_rec_6(i, I) FOR_FORWARD(i,I)
#define FOR_A_rec_7(i, I) FOR_FORWARD(i,I)
#define FOR_A_rec_8(i, I) FOR_FORWARD(i,I)
#define FOR_A_rec_9(i, I) FOR_FORWARD(i,I)
#define FOR_A_rec_10(i, I) FOR_FORWARD(i,I)

void funcA_loop(DEFINTERVALFUNC(I), DEFINTERVALFUNC(J)) {

	FOR_A_loop_1(i,I)
	{
		FOR_A_loop_2(j,J)
		{
			dist[i][j] =
					GETDEF(
							GETDEF(dist[i][j],((DELTA(i,j))?(dist[(i-1)][(j-1)]+1):UNDEF)),
							(((!DELTA(i,j)))?(OMAX(dist[i][(j-1)],dist[(i-1)][j])):UNDEF));
		}
	}

}
void funcA_rec(DEFINTERVALFUNC(I), DEFINTERVALFUNC(J)) {
	if (BASE_CONSTRAINT_A(I, J)) {
		funcA_loop(PARAM(I), PARAM(J));
		return;
	}
	DEFINTERVALSTMT(I0);
	DEFBEGIN(I0) = DEFBEGIN(I);
	DEFEND(I0) = (DEFEND(I) + DEFBEGIN(I)) / 2;
	DEFINTERVALSTMT(I1);
	DEFBEGIN(I1) = DEFEND(I0);
	DEFEND(I1) = DEFEND(I);
	DEFINTERVALSTMT(J0);
	DEFBEGIN(J0) = DEFBEGIN(J);
	DEFEND(J0) = (DEFEND(J) + DEFBEGIN(J)) / 2;
	DEFINTERVALSTMT(J1);
	DEFBEGIN(J1) = DEFEND(J0);
	DEFEND(J1) = DEFEND(J);

	funcA_rec(PARAM(I0), PARAM(J0));
	FOR_A_rec_1(i,I0)
	{
		FOR_A_rec_2(j,J1)
		{
			dist[i][j] =
					GETDEF(
							GETDEF(dist[i][j],((DELTA(i,j) && INSET((j-1),J0))?(dist[(i-1)][(j-1)]+1):UNDEF)),
							(((!DELTA(i,j)) && INSET((j-1),J0))?(OMAX(dist[i][(j-1)],dist[(i-1)][j])):UNDEF));
		}
	};
	funcA_rec(PARAM(I0), PARAM(J1));
	FOR_A_rec_3(i,I1)
	{
		FOR_A_rec_4(j,J0)
		{
			dist[i][j] =
					GETDEF(
							GETDEF(dist[i][j],((DELTA(i,j) && INSET((i-1),I0))?(dist[(i-1)][(j-1)]+1):UNDEF)),
							(((!DELTA(i,j)) && INSET((i-1),I0))?(OMAX(dist[i][(j-1)],dist[(i-1)][j])):UNDEF));
		}
	};
	funcA_rec(PARAM(I1), PARAM(J0));
	FOR_A_rec_5(i,I1)
	{
		FOR_A_rec_6(j,J1)
		{
			dist[i][j] =
					GETDEF(
							GETDEF(dist[i][j],((DELTA(i,j) && INSET((i-1),I0) && INSET((j-1),J0))?(dist[(i-1)][(j-1)]+1):UNDEF)),
							(((!DELTA(i,j)) && INSET((j-1),J0) && INSET((i-1),I0))?(OMAX(dist[i][(j-1)],dist[(i-1)][j])):UNDEF));
		}
	};
	FOR_A_rec_7(i,I1)
	{
		FOR_A_rec_8(j,J1)
		{
			dist[i][j] =
					GETDEF(
							GETDEF(dist[i][j],((DELTA(i,j) && INSET((i-1),I0) && INSET((j-1),J1))?(dist[(i-1)][(j-1)]+1):UNDEF)),
							(((!DELTA(i,j)) && INSET((j-1),J1) && INSET((i-1),I0))?(OMAX(dist[i][(j-1)],dist[(i-1)][j])):UNDEF));
		}
	};
	FOR_A_rec_9(i,I1)
	{
		FOR_A_rec_10(j,J1)
		{
			dist[i][j] =
					GETDEF(
							GETDEF(dist[i][j],((DELTA(i,j) && INSET((i-1),I1) && INSET((j-1),J0))?(dist[(i-1)][(j-1)]+1):UNDEF)),
							(((!DELTA(i,j)) && INSET((j-1),J0) && INSET((i-1),I1))?(OMAX(dist[i][(j-1)],dist[(i-1)][j])):UNDEF));
		}
	};
	funcA_rec(PARAM(I1), PARAM(J1));
}

/*
 * Testing Code
 */
int X[N];
int Y[M]; //actual length of sequence is M-1 from index 1 to M-1
int dloop[N][M];
int dorig[N][M];
int drec[N][M];
void getRandSeq() {
	char a = 'A';
	cout << "X: ";
	for (int i = 0; i < N; i++) {
		X[i] = rand() % 4 + a;
		cout << (char) X[i];
	}
	cout << endl;
	cout << "Y: ";
	for (int i = 0; i < M; i++) {
		Y[i] = rand() % 4 + a;
		cout << (char) Y[i];
	}
	cout << endl;

}

void fillDeltaAndDist() {
	for (int i = 0; i < N; i++) {
		for (int j = 0; j < M; j++) {
			delta[i][j] = (X[i] == Y[j]);
			dist[i][j] = UNDEF;
			if (i == 1 || j == 1) {
				dist[i][j] = 0;
			}
		}
	}

}

void dcopy(int from[N][M], int to[N][M]) {
	for (int i = 0; i < N; i++) {
		for (int j = 0; j < M; j++) {
			to[i][j] = from[i][j];
		}
	}
}

void checkEq(int a[N][M], int b[N][M], string msg, bool debug) {
	if (N < 20 && M < 20 && debug)
		cout << "i\tj\tdloop\tdrec" << endl;
	for (int i = 1; i < N; i++) {
		for (int j = 1; j < M; j++) {
			if (a[i][j] != b[i][j]) {
				cout << "ERROR: " << msg << " | Not the save values for (" << i
						<< "," << j << "): " << a[i][j] << " " << b[i][j]
						<< endl;
				exit(1);
			}
			if (N < 20 && M < 20 && debug)
				cout << i << '\t' << j << '\t' << a[i][j] << '\t' << b[i][j]
						<< endl;
		}
	}
}

int main() {
	srand (time(NULL));getRandSeq();
	fillDeltaAndDist();
	dcopy(dist,dorig);
	DEFINTERVALSTMT(I);
	DEFBEGIN(I) = 1;
	DEFEND(I) = N;
	DEFINTERVALSTMT(J);
	DEFBEGIN(J) = 1;
	DEFEND(J) = M;

	funcA_loop(PARAM(I),PARAM(J));
	dcopy(dist,dloop);
	dcopy(dorig,dist);
	funcA_rec(PARAM(I),PARAM(J));
	dcopy(dist,drec);
	checkEq(dloop,drec,"loop-vs-rec",false);
	cout<<"LCS: "<<dist[N-1][M-1]<<endl;
	return 0;
}

