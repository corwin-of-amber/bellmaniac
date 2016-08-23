#ifndef TYPE
#define TYPE double
#endif
#ifndef MAXVAL
#define MAXVAL 1.0e100
#endif
#include <cmath>
extern TYPE* px;
extern TYPE* py;
#define Ddist(i,j) dist[((i)-1)*N + ((j)-1)]
#define d(i,j) sqrt((px[(i)-1] -px[(j)-1])*(px[(i)-1] -px[(j)-1]) + (py[(i)-1] -py[(j)-1])*(py[(i)-1] -py[(j)-1]))

