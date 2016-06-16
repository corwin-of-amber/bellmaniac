#include <iostream>
#include <string>
#include <time.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/timeb.h>
#include <cstring>
#include <cilk/cilk.h>
#include <cilk/cilk_api.h>
#include <math.h>
#include <immintrin.h>
#include "cilktime.h"


using namespace std;
int N;
#ifndef B
int B
#endif
int *SOF, *S_dp, *S;
string proteinSeq;
#define ALIGNMENT 64
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
struct interval {
	int begin;int end;
};
#endif

//HACK
#ifdef HACKJ
#ifdef INTINTERVAL
TYPE DEFBEGIN(J) = 0;
TYPE DEFEND(J) = 0;
#else
interval J;
#endif
#endif

#define MAXVAL int(1e9)
#define UNDEF MAXVAL
#define NOP 



#define LET(i,v) int i = v;
#define INSET(i,I) ((i) >= DEFBEGIN(I) && (i) < DEFEND(I)) 
#define FOR_VAR_FWD(i,n,m) for(TYPE i=n;i<m;i++)
#define FOR_VAR_BWD(i,n,m) for(TYPE i=m-1;i>=n;i--)

#define SIZE(I) (DEFEND(I)-DEFBEGIN(I))
#define FOR_FORWARD(i,K) for(TYPE i=DEFBEGIN(K);i<DEFEND(K);i++)
#define FOR_BACKWARD(i,K) for(TYPE i=DEFEND(K)-1;i>=DEFBEGIN(K);i--)

#define BASE_CONSTRAINT1(a) ((DEFEND(a)-DEFBEGIN(a)) <= B)
#define BASE_CONSTRAINT2(a,b) (BASE_CONSTRAINT1(a) || BASE_CONSTRAINT1(b))
#define BASE_CONSTRAINT3(a,b,c) (BASE_CONSTRAINT2(a,b) || BASE_CONSTRAINT1(c))

#define FOR_A_loop_1(i,n,m) FOR_VAR_BWD(i,n,m)
#define FOR_A_loop_2(i,n,m) FOR_VAR_BWD(i,n,m)
#define FOR_A_loop_3(i,n,m) FOR_VAR_BWD(i,n,m)
#define FOR_A_loop_4(i,n,m) FOR_VAR_BWD(i,n,m)

#define FOR_A_rec_1(i,n,m) FOR_VAR_BWD(i,n,m)
#define FOR_A_rec_2(i,n,m) FOR_VAR_BWD(i,n,m)
#define FOR_A_rec_3(i,n,m) FOR_VAR_BWD(i,n,m)

#define FOR_B_loop_3(i,n,m) FOR_VAR_BWD(i,n,m)
#define FOR_B_loop_4(i,n,m) FOR_VAR_BWD(i,n,m)
#define FOR_B_loop_2(i,n,m) FOR_VAR_BWD(i,n,m)
#define FOR_B_loop_1(i,n,m) FOR_VAR_BWD(i,n,m)
//#define FOR_B_loop_1(i,j,I,J,ZZ) FOR_BWD_FWD(i,j,I,J,ZZ)

#define FOR_B_rec_1(i,n,m) FOR_VAR_BWD(i,n,m)
#define FOR_B_rec_2(i,n,m) FOR_VAR_BWD(i,n,m)
#define FOR_B_rec_3(i,n,m) FOR_VAR_BWD(i,n,m)
#define FOR_B_rec_4(i,n,m) FOR_VAR_BWD(i,n,m)
#define FOR_B_rec_5(i,n,m) FOR_VAR_BWD(i,n,m)
#define FOR_B_rec_6(i,n,m) FOR_VAR_BWD(i,n,m)

#define FOR_C_loop_1(i,n,m) FOR_VAR_BWD(i,n,m)
#define FOR_C_loop_2(i,n,m) FOR_VAR_BWD(i,n,m)
#define FOR_C_loop_3(i,n,m) FOR_VAR_BWD(i,n,m)

#define FOR_D_loop_1(i,n,m) FOR_VAR_BWD(i,n,m)
#define FOR_D_loop_2(i,n,m) FOR_VAR_BWD(i,n,m)
#define FOR_D_loop_3(i,n,m) FOR_VAR_BWD(i,n,m)

#define FOR_C_rec_1(i,n,m) FOR_VAR_BWD(i,n,m)
#define FOR_C_rec_2(i,n,m) FOR_VAR_BWD(i,n,m)
#define FOR_C_rec_3(i,n,m) FOR_VAR_BWD(i,n,m)
#define FOR_C_rec_4(i,n,m) FOR_VAR_BWD(i,n,m)

#define FOR_D_rec_1(i,n,m) FOR_VAR_BWD(i,n,m)
#define FOR_D_rec_2(i,n,m) FOR_VAR_BWD(i,n,m)
#define FOR_D_rec_3(i,n,m) FOR_VAR_BWD(i,n,m)
#define FOR_D_rec_4(i,n,m) FOR_VAR_BWD(i,n,m)
#define FOR_D_rec_5(i,n,m) FOR_VAR_BWD(i,n,m)
#define FOR_D_rec_6(i,n,m) FOR_VAR_BWD(i,n,m)


#define DELTA(i,j,k) SOF[ ((j)+1)*N + min((k),(2*(j)-(i)+1))]
#define Ddist(i,j) S[(i)*N + (j)]
#define DCLdist(i,j) Ddist(i,j)
#define DBLdist(i,j) Ddist(i,j)
#define DALdist(i,j) Ddist(i,j)
#define DDLdist(i,j) Ddist(i,j)



#define BASE_CONSTRAINT_A(a) BASE_CONSTRAINT1(a)
#define BASE_CONSTRAINT_C(a,b) BASE_CONSTRAINT2(a,b)
#define BASE_CONSTRAINT_B(a,b) BASE_CONSTRAINT2(a,b)
#define BASE_CONSTRAINT_D(a,b,c) BASE_CONSTRAINT3(a,b,c)

#define DdistCO(i,j,I,J) V[((j)-DEFBEGIN(J))*B + ((i)-DEFBEGIN(I))]
#define DdistSimpleV(i,j,I,J) V[((j)-DEFBEGIN(J)) + ((i)-DEFBEGIN(I))*B]
#define DdistSimpleW(i,j,I,J) W[((j)-DEFBEGIN(J)) + ((i)-DEFBEGIN(I))*B]
inline void copy_dist_part(TYPE* V,DEFINTERVALFUNC(II),DEFINTERVALFUNC(JJ)){
	for(int i=DEFBEGIN(II);i<DEFEND(II);i++){
		for(int j=DEFBEGIN(JJ);j<DEFEND(JJ);j++){
			//cout<<i<<" "<<j<<" "<<(j)-DEFBEGIN(JJ)<<" "<<((i)-DEFBEGIN(II))<<endl;
			DdistSimpleV(i,j,II,JJ) = Ddist(i,j);

		}
	}
}

inline void copy_to_dist(TYPE* W,DEFINTERVALFUNC(II),DEFINTERVALFUNC(JJ)){
	for(int i=DEFBEGIN(II);i<DEFEND(II);i++){
		for(int j=DEFBEGIN(JJ);j<DEFEND(JJ);j++){
			//cout<<i<<" "<<j<<" "<<(j)-DEFBEGIN(JJ)<<" "<<((i)-DEFBEGIN(II))<<endl;
			Ddist(i,j)=DdistSimpleW(i,j,II,JJ);

		}
	}
}

//shifted everything by 1 to consider start in index 1

void SCORE_ONE_FOLD(int n) {
	for (int j = 1; j < n - 1; j++) {
		for (int k = j + 2; k < n; k++) {
			if (k > 2 * j) {
				SOF[j * N + k] = SOF[j * N + 2 * j];
			} else {
				SOF[j * N + k] = SOF[j * N + (k - 1)];
				if ((2 * j - k - 1 >= 0)
					&& (proteinSeq[2 * j - k - 1] == proteinSeq[k])
					&& (proteinSeq[k] == '1')) { // should 2*j-k-1 > 0 or >=0??
						++SOF[j * N + k];
				}

			}

		}
	}
}

#include "../accordion-new-all.cpp"


int CO_PROTEIN_FOLDING(int n) {

	//array, size, starting point x, starting point y
	DEFINTERVALSTMT(K0);
	DEFBEGIN(K0) = 0;
	DEFEND(K0) = n;
	funcA_rec(PARAM(K0));
	int final = 0;

	for (int j = 0; j < n - 1; j++) {
		final = max(final, S[j]);

	}
	return final;

}
/*
void makeProteinSeq(int n)
{
//generating random sequence. here 1 means hydrophobic and 0 means hydrophilic
for(int i = 0; i <=n; ++i){
int val = (rand() % 10);
if(val < 5) proteinSeq = proteinSeq + '1';
else proteinSeq = proteinSeq + '0';
}

}*/
void makeProteinSeq(int n) {
	//generating random sequence. here 1 means hydrophobic and 0 means hydrophilic
	for (int i = 0; i < n; ++i) {
		/*int val = (rand() % 10);
		if(val < 5) proteinSeq = proteinSeq + '1';
		else proteinSeq = proteinSeq + '0';*/
		proteinSeq = proteinSeq + '1';
	}
	/*
	for(int i=1;i<=N; i++)
	{
	cout<<proteinSeq[i]<<" ";
	}
	cout<<endl;
	*/
}

#ifdef DEBUG
int LOOP_PROTEIN_FOLDING (int n)
{

	for(int i = n-2; i>=0;i--)
	{
		cilk_for(int j = n-3; j>i; j--)
		{

			int val = S_dp[i*N+j];
			//I have observed that these 2 optimizations does not matter really!
			int j2 = 2*j-i+1;
			int inj = (j+1)*N;
			for(int k = n-1; k>=j+2; k--)
			{
				val = max(val, S_dp[inj+k] + SOF[inj+min(k, j2)]);

			}
			S_dp[i*N+j]= val;
		}

	}

	//find the maximum value
	int final = 0;
	for(int j = 0; j<n-1; j++)
	{
		final = max(final, S_dp[j]);

	}
	return final;
}
#endif
void printArr(TYPE* a,string msg){
	cout<<msg<<":"<<endl;
	for(int i=0;i<N; i++)
	{
		for(int j=0;j<N; j++)
		{
			cout<<a[i*N+j]<<" ";
		}
		cout<<endl;
	}
}
int main(int argc, char ** argv) {

	N = 16;
	
	if (argc > 1)
		N = atoi(argv[1]);
#ifndef B
	B = N / 2;
	if (argc > 2)
		B = atoi(argv[2]);
	if (B > N)
		B = N;
	N = N;
#endif
	
#ifdef HACKJ
	//HACK
	DEFBEGIN(J) = 0;
	DEFEND(J) = N;
#endif
	int NN = 2;

	while (NN < N)
		NN = NN << 1;
	SOF = (int *) _mm_malloc(N * N * sizeof(int), 64); //stores score-one-fold
	//clearing the SOF array
	for (int i = 0; i < N; i++) {
		SOF[i*N:N] = 0;
	}

	//create arbitary protein seq

	makeProteinSeq(N);
	//compute SOF

	SCORE_ONE_FOLD(N);

	//allocate for the score array

	S = (int *) _mm_malloc(N * N * sizeof(int), 64);

	//clearing the S array
	for (int i = 0; i < N; i++) {
		S[i*N:N] = 0;
	}

	

	unsigned long long tstart = cilk_getticks();

	int finalc = CO_PROTEIN_FOLDING(N);

	unsigned long long tend = cilk_getticks();
	cout<<"VERSION\tN\tB\tTime(s)"<<endl;
	cout<<"AUTO\t"<<N<<"\t"<<B<<"\t"<<cilk_ticks_to_seconds(tend-tstart)<<endl;
#ifdef DEBUG
	S_dp = (int *) _mm_malloc(N * N * sizeof(int), 64);
	for(int i = 0; i<N; i++)
	{
		S_dp[i*N:N] = 0;
	}
	unsigned long long tstart1 = cilk_getticks();
	int final = LOOP_PROTEIN_FOLDING(N);
	unsigned long long tend1 = cilk_getticks();
	cout<<"LOOPDP\t"<<N<<"\t"<<B<<"\t"<<cilk_ticks_to_seconds(tend1-tstart1)<<endl;
	if (N<20){
		printArr(SOF,"SOF:");
		printArr(S,"AUTO_LOOP:");
		printArr(S_dp,"LOOPDP:");
		cout<<endl;
	}
	int ctr = 0;
	for(int i=0;i<N; i++)
	{
		for(int j=0;j<N; j++)
		{
			if(S[i*N+j]!=S_dp[i*N+j]){
				cout<<i<<" "<<j<<" "<<S[i*N+j]<<" "<<S_dp[i*N+j]<<endl;
			}
			ctr++;
			assert(S[i*N+j]==S_dp[i*N+j]);
		}

	}
	cout<<"Checked "<<ctr<<" values."<<endl;
	_mm_free(S_dp);
#endif
	_mm_free(S);
	_mm_free(SOF);

	return 0;
}
