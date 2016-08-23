
#include <cmath>
#include<atomic>
#define v(i) (VL[i])
#define w(i) (WT[i])
//#define Ddist(i,j) dist[((i)-1)*N + ((j)-1)]
#define tableAccess(arr,i,j,n) (arr)[(i)*(n) + (j)]
#define Ddist(i,j) tableAccess(dist,i,j,N+1)
extern int* WT;
extern int* VL; //actual length of sequence is M-1 from index 1 to M-1
extern std::atomic_int cMaxRec, cMaxLoop;