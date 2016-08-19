
#define DEFINEVARS
#include "input.h" //Fix Compiler here
#include "preface.h"
TYPE* px;
TYPE* py;

void funcA_rec(DEFINTERVALFUNC(J));

inline void init_px_py_btsp(){
	//cout<<"Standard dist "<<endl;
	px[0] = (TYPE)(rand()%10-19);
	py[0] = (TYPE)(rand()%10-19);
	for (int i=2;i<=N;i++) {
		px[i-1] = (TYPE)(px[i-2] + rand()%5+1);
		py[i-1] = (TYPE)(rand()%20-40);
	}
	for(int i=1;i<=N;i++){
		for(int j=1;j<=N;j++){
			Ddist(i,j) = MAXVAL;
		}		
	}
	Ddist(1,2) = d(1,2);
}

#define BL(i,j) BTSPL[((i)-1)*N+((j)-1)]
void bitonicLoop(TYPE* BTSPL){
	for(int i=1;i<=N;i++){
		for(int j=1;j<=N;j++){
			BL(i,j) = MAXVAL;
		}
	}
	BL(1,2) = d(1,2);
	for(int j=2;j<=N;j++){
		for(int i=1;i<=j-1;i++){
			if (i<j-1){
				BL(i,j) = BL(i,j-1) + d(i,j-1);
			}
			if(i==j-1){

				for(int k=1;k<i;k++){
					BL(i,j) = min(BL(i,j),BL(k,i)+d(k,i));
				}
			}
		}
	}
}
#ifdef DEBUG
#define pp(x) ((x>MAXVAL/2)?-1:x)
void printBTSP(TYPE* btsp){
	cout<<endl;
	if (N>20) return;
	cout.precision(4);
	for(int i=1;i<=N;i++){
		for(int j=1;j<=N;j++){
			cout<<(pp(btsp[(i-1)*N+(j-1)]))<<"\t";
		}
		cout<<endl;
	}
}

void checkError(TYPE* BTSPL){
	for(int i=1;i<=N;i++){
		for(int j=1;j<=N;j++){
			if (abs(BL(i,j) - Ddist(i,j)) > 0.0001){
				cout<<i<<"\t"<<j<<"\t"<<BL(i,j)<<"\t"<<Ddist(i,j)<<endl;
				exit(1);
			}
		}
	}
	cout<<"Checked "<<N*N<<" Values."<<endl;
}

void bitonicCheck() {
	//Use px,py to re-compute BitonicTSP locally and check if rec version is correct
	printBTSP(dist);
	TYPE* BTSPL = ( TYPE* ) _mm_malloc(N * N * sizeof( TYPE ),ALIGNMENT);
	unsigned long long tstart1 = cilk_getticks();
	bitonicLoop(BTSPL);
	unsigned long long tend1 = cilk_getticks();
	printBTSP(BTSPL);
	cout<<"LOOPDP\t"<<N<<"\t"<<B<<"\t"<<cilk_ticks_to_seconds(tend1-tstart1)<<endl;
	checkError(BTSPL);
	_mm_free(BTSPL);
}

#endif

int main(int argc, char *argv[]) {

	argParser(argc, argv);
	
#ifdef _DEBUG
	if (0!= __cilkrts_set_param("nworkers","1")) {
		cout<<"Failed to set worker count\n";
		return 1;
	}
#endif 

	srand ((unsigned int)time(NULL));
	dist = ( TYPE* ) _mm_malloc(N * N * sizeof( TYPE ),ALIGNMENT);
	px = ( TYPE* ) _mm_malloc(N * sizeof( TYPE ),ALIGNMENT);
	py = ( TYPE* ) _mm_malloc(N * sizeof( TYPE ),ALIGNMENT);
	

	//DEFBEGIN(BOTTOMJ) = 0;
	//DEFEND(BOTTOMJ) =0;
	DEFINTERVALSTMT(K0);
	DEFBEGIN(K0) = 1;
	DEFEND(K0) = N+1;
	cout<<"VERSION\tN\tB\tTime(s)"<<endl;
	unsigned long long tstart;
	unsigned long long tend;
#ifdef CO
	init_px_py_btsp();
	tstart = cilk_getticks();
	funcA_rec(PARAM(K0));
	tend = cilk_getticks();
	cout<<"AUTO\t"<<N<<"\t"<<B<<"\t"<<cilk_ticks_to_seconds(tend-tstart)<<endl;
	//May check LOOPDP later here
#endif

#ifdef DEBUG
	bitonicCheck();
#else
#ifdef LOOPDP
	init_px_py_btsp();
	tstart = cilk_getticks();
	bitonicLoop(dist);
	tend = cilk_getticks();
	cout<<"LOOPDP\t"<<N<<"\t"<<B<<"\t"<<cilk_ticks_to_seconds(tend-tstart)<<endl;
#endif
#endif
#ifndef NNUM
	_mm_free(dist);
	_mm_free(px);
	_mm_free(py);

#endif
	exit(0);
}

