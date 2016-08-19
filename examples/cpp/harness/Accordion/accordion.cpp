#define DEFINEVARS
#include "input.h"
#include "preface.h"

using namespace std;
int *SOF;
string proteinSeq;

//HACK
#ifdef HACKJ
#ifdef INTINTERVAL
TYPE DEFBEGIN(J) = 0;
TYPE DEFEND(J) = 0;
#else
interval J;
#endif
#endif






#define DdistCO(i,j,I,J) V[((j)-DEFBEGIN(J))*B + ((i)-DEFBEGIN(I))]
#define DdistSimpleV(i,j,I,J) V[((j)-DEFBEGIN(J)) + ((i)-DEFBEGIN(I))*B]
#define DdistSimpleW(i,j,I,J) W[((j)-DEFBEGIN(J)) + ((i)-DEFBEGIN(I))*B]

void funcA_rec(DEFINTERVALFUNC(J));

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



int CO_PROTEIN_FOLDING(int n) {

	//array, size, starting point x, starting point y
	DEFINTERVALSTMT(K0);
	DEFBEGIN(K0) = 0;
	DEFEND(K0) = n;
	funcA_rec(PARAM(K0));
	int final = 0;

	for (int j = 0; j < n - 1; j++) {
		final = max(final, dist[j]);

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


int LOOP_PROTEIN_FOLDING (TYPE* S_dp, int n)
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

	argParser(argc,argv);
	
	
#ifdef HACKJ
	//HACK
	DEFBEGIN(J) = 0;
	DEFEND(J) = N;
#endif

	/*int NN = 2;

	while (NN < N)
		NN = NN << 1;
		*/

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

	dist = (int *) _mm_malloc(N * N * sizeof(int), 64);

	//clearing the S array
	for (int i = 0; i < N; i++) {
		dist[i*N:N] = 0;
	}

	

	unsigned long long tstart = cilk_getticks();

	int finalc = CO_PROTEIN_FOLDING(N);

	unsigned long long tend = cilk_getticks();
	cout<<"VERSION\tN\tB\tTime(s)"<<endl;
	cout<<"AUTO\t"<<N<<"\t"<<B<<"\t"<<cilk_ticks_to_seconds(tend-tstart)<<endl;
#ifdef DEBUG
	int *S_dp = (int *) _mm_malloc(N * N * sizeof(int), 64);
	for(int i = 0; i<N; i++)
	{
		S_dp[i*N:N] = 0;
	}
	unsigned long long tstart1 = cilk_getticks();
	int final = LOOP_PROTEIN_FOLDING(S_dp,N);
	unsigned long long tend1 = cilk_getticks();
	cout<<"LOOPDP\t"<<N<<"\t"<<B<<"\t"<<cilk_ticks_to_seconds(tend1-tstart1)<<endl;
	if (N<20){
		printArr(SOF,"SOF:");
		printArr(dist,"AUTO_LOOP:");
		printArr(S_dp,"LOOPDP:");
		cout<<endl;
	}
	int ctr = 0;
	for(int i=0;i<N; i++)
	{
		for(int j=0;j<N; j++)
		{
			if(dist[i*N+j]!=S_dp[i*N+j]){
				cout<<i<<" "<<j<<" "<<dist[i*N+j]<<" "<<S_dp[i*N+j]<<endl;
				exit(1);
			}
			ctr++;
			//assert(dist[i*N+j]==S_dp[i*N+j]);
		}

	}
	cout<<"Checked "<<ctr<<" values."<<endl;
	_mm_free(S_dp);
#elif LOOPDP
	for(int i = 0; i<N; i++)
	{
		dist[i*N:N] = 0;
	}
	unsigned long long tstart1 = cilk_getticks();
	int final = LOOP_PROTEIN_FOLDING(dist,N);
	unsigned long long tend1 = cilk_getticks();
	cout<<"LOOPDP\t"<<N<<"\t"<<B<<"\t"<<cilk_ticks_to_seconds(tend1-tstart1)<<endl;
	
#endif
	_mm_free(dist);
	_mm_free(SOF);

	return 0;
}
