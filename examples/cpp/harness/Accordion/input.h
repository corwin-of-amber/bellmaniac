#include<string>
#define UNDEFINED MINVAL
#define INITMAX MINVAL
extern int *SOF;
extern std::string proteinSeq;
#define delta(i,j,k) SOF[ ((j)+1)*N + min((k),(2*(j)-(i)+1))]

