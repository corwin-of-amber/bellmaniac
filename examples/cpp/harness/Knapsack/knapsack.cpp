
#define DEFINEVARS
#include "input.h" //Fix Compiler here
#include "preface.h"

long long W; 
//?dist = KS
int* WT;
int* VL; //actual length of sequence is M-1 from index 1 to M-1


void funcA_rec(DEFINTERVALFUNC(I),DEFINTERVALFUNC(J));

std::atomic_int  cMaxRec, cMaxLoop;


void KnapsackLoop(TYPE* dist) {

	for(int i = 1; i<= N;i++)
	{
		
		cilk_for(int j = 1; j<= W;j++)
		{
			if (w(i) > j){
				Ddist(i,j) = Ddist(i-1,j);
			}
			else{
				Ddist(i,j) = max(Ddist(i-1,j),Ddist(i-1,j-w(i)) +v(i));
				//cMaxLoop++;
			}
			
		}
	}
}

void initKnapsack(TYPE* dist) {
	for (int i = 0; i <= N; i++) {
		for (int j = 0; j <= W; j++) {
			Ddist(i,j) = MINVAL;
			if (i == 0 || j == 0) {
				Ddist(i,j) = 0;
			}
		}
	}

}

void printArr(TYPE * dist){
	if (N>20) return;
	for(int i=0;i<=N;i++){
		for(int j=0;j<=W;j++){
			cout<<Ddist(i,j)<<"\t";
		}
		cout<<endl;
	}
}

void generateRandSeq() {
	//generate N items and set their weights and values
	long long sumW = 0;
	for(int i=0;i<=N;i++){
		//WT, VL arrays
		WT[i] = rand()%4+1;
		VL[i] = rand()%4+1;
		sumW += WT[i];
		if (N<20) cout<<i<<": w="<<WT[i]<<" v="<<VL[i]<<endl;
	}
	//W = ((sumW*3)/4);
}


int main(int argc, char *argv[]) {
	cMaxRec = 0; 
	cMaxLoop = 0;
	argParser(argc, argv);
	
#ifdef _DEBUG
	if (0!= __cilkrts_set_param("nworkers","1")) {
		cout<<"Failed to set worker count\n";
		return 1;
	}
#endif 

	//srand ((unsigned int)time(NULL));
	srand((unsigned int)0);//Temorary for debugging

	WT = ( TYPE* ) _mm_malloc((N+1) * sizeof( TYPE ),ALIGNMENT);
	VL = ( TYPE* ) _mm_malloc((N+1) * sizeof( TYPE ),ALIGNMENT);
	generateRandSeq();
	W=N; //For now
#ifdef DEBUG
	TYPE * dloop = ( TYPE* ) _mm_malloc((N+1) * (W+1) * sizeof( TYPE ),ALIGNMENT);
#endif
#ifdef CO
	dist = ( TYPE* ) _mm_malloc((N+1) * (W+1) * sizeof( TYPE ),ALIGNMENT);
#endif
	DEFINTERVALSTMT(I);
	DEFBEGIN(I) = 0;
	DEFEND(I) = N+1;

	DEFINTERVALSTMT(J);
	DEFBEGIN(J) = 0;
	DEFEND(J) = W+1;
#ifdef DEBUG
	{
		initKnapsack(dloop);
		unsigned long long tstart = cilk_getticks();
		KnapsackLoop(dloop);
		unsigned long long tend = cilk_getticks();
		cout<<"LOOPDP\t"<<N<<"\t"<<B<<"\t"<<cilk_ticks_to_seconds(tend-tstart)<<endl;
		printArr(dloop);
	}
#endif
#ifdef CO
	{
		initKnapsack(dist);
		unsigned long long tstart = cilk_getticks();
		funcA_rec(PARAM(I),PARAM(J));
		unsigned long long tend = cilk_getticks();
		cout<<"AUTO\t"<<N<<"\t"<<B<<"\t"<<cilk_ticks_to_seconds(tend-tstart)<<endl;
		printArr(dist);
	}
#endif
#ifdef DEBUG
	FOR_FWD(i,0,N+1){
		FOR_FWD(j,0,W+1){
			if (Ddist(i,j) != tableAccess(dloop,i,j,N+1)){
				cout<<i<<" "<<j<<" "<<Ddist(i,j)<<" "<<tableAccess(dloop,i,j,N+1)<<endl;
				exit(1);
			}
		}
	}
	cout<<"Checked "<<(N+1)*(W+1)<<" values correctly."<<endl;
	//cout<<"Counts of Maxes: Rec="<<cMaxRec<<" Loop="<<cMaxLoop<<endl;
	_mm_free(dloop);
#endif

	_mm_free(dist);
	_mm_free(WT);
	_mm_free(VL);
	return 0;
}

