#include "input.h"
#define DEFINEVARS
#include "preface.h"
using namespace std;

long long M;
int* X;
int* Y; //actual length of sequence is M-1 from index 1 to M-1

/*void funcA_loop(DEFINTERVALFUNC(I),DEFINTERVALFUNC(J)){

	FOR_FWD(i,DEFBEGIN(I),DEFEND(I)){
		FOR_FWD(j,DEFBEGIN(J),DEFEND(J)){
			if (psi(i,j) == UNDEFINED){
				if(delta(i,j)){
					psi(i,j)=psi((i-1),(j-1))+1;
				}
				if((!delta(i,j))){
					psi(i,j)=oplus(psi(i,(j-1)),psi((i-1),j));
				}

			}
		}
	}

}*/

void funcA_rec(DEFINTERVALFUNC(I),DEFINTERVALFUNC(J));

TYPE* dloop;
#define DdistLoop(i,j) dloop[(i)*N+(j)]

void LCS_orig() {
	for (int sum=2;sum<=2*N-2;sum++){
		cilk_for(int i=min(N-1,(long long)(sum-1)); i>=max((long long)1,sum-N+1) ;i--){
			int j =sum-i;
			//cout<<i<<" "<<j<<endl;
			if ((DdistLoop(i,j)) == UNDEFINED) {
				if (delta(i, j)) {
					DdistLoop(i,j) = DdistLoop((i - 1),(j - 1)) + 1;
				}
				else {
					DdistLoop(i,j) = max(DdistLoop(i,(j - 1)), DdistLoop((i - 1),j));
				}
			}
		}
	}
/*	for(int i = 1; i< N;i++)
	{
		//RTODO: PARALLEL cilk_for?
		for(int j = 1; j< N;j++)
		{
			
		}
	}
	*/
}


void fillDistLoop() {
	for (int i = 0; i < N; i++) {
		for (int j = 0; j < M; j++) {
			DdistLoop(i,j) = UNDEFINED;
			if (i == 1 || j == 1) {
				DdistLoop(i,j) = 0;
			}
		}
	}

}

#ifdef CO
void fillDist() {
	for (int i = 0; i < N; i++) {
		for (int j = 0; j < M; j++) {
			Ddist(i,j) = UNDEFINED;
			if (i == 1 || j == 1) {
				Ddist(i,j) = 0;
			}
		}
	}

}
#endif


void getRandSeq() {
	char a = 'A';
	if (N<120) cout << "X: ";
	for (int i = 0; i < N; i++) {
		X[i] = rand() % 4 + a;
		if (N<120)
			cout << (char) X[i];
	}
	if (N<120)cout << endl;
	if (N<120)cout << "Y: ";
	for (int i = 0; i < M; i++) {
		Y[i] = rand() % 4 + a;
		if (N<120)
			cout << (char) Y[i];
	}
	if (N<120) cout << endl;

}


int main(int argc, char* argv[]){
	
	argParser(argc, argv);
	M=N;
	srand ((unsigned int)time(NULL));
#ifdef DEBUG
	dloop = ( TYPE* ) _mm_malloc(N * N * sizeof( TYPE ),ALIGNMENT);
#endif
#ifdef CO
	dist = ( TYPE* ) _mm_malloc(N * N * sizeof( TYPE ),ALIGNMENT);
#endif
	X = ( TYPE* ) _mm_malloc(N * sizeof( TYPE ),ALIGNMENT);
	Y = ( TYPE* ) _mm_malloc(N * sizeof( TYPE ),ALIGNMENT);


	getRandSeq();
	DEFINTERVALSTMT(I);
	DEFBEGIN(I) = 1;
	DEFEND(I) = N;
	DEFINTERVALSTMT(J);
	DEFBEGIN(J) = 1;
	DEFEND(J) = N;
	cout<<"VERSION\tN\tM\tB\tTime(s)\tLCS-Value"<<endl;
#ifdef CO
	{
		fillDist();
		unsigned long long tstart = cilk_getticks();
		funcA_rec(PARAM(I),PARAM(J));
		unsigned long long tend = cilk_getticks();
		cout<<"AUTO\t"<<N<<"\t"<<M<<"\t"<<B<<"\t"<<cilk_ticks_to_seconds(tend-tstart)<<"\t"<<Ddist(N-1,N-1)<<endl;

	}
#endif
#ifdef DEBUG
	{
		fillDistLoop();

		unsigned long long tstart = cilk_getticks();
		LCS_orig();
		unsigned long long tend = cilk_getticks();
		cout<<"LOOPDP\t"<<N<<"\t"<<M<<"\t"<<B<<"\t"<<cilk_ticks_to_seconds(tend-tstart)<<"\t"<<DdistLoop(N-1,N-1)<<endl;

	}

	FOR_FWD(i,DEFBEGIN(I),DEFEND(I)){
		FOR_FWD(j,DEFBEGIN(J),DEFEND(J)){
			if (psi(i,j) != DdistLoop(i,j)){
				cout<<i<<" "<<j<<" "<<psi(i,j)<<" "<<DdistLoop(i,j)<<" "<<psi(N-1,N-1)<<endl;
			}
			assert (psi(i,j) == DdistLoop(i,j));
		}
	}
#endif
	return 0;
}

