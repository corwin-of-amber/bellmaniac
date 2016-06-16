
/* Min Max and Weight Function */
#define w(q, j) (q+j) // weight function for delete
#define w_prime(p, i) (p+i) // weight function for insert
#define Sn(x, y) ((x==y)?0:1) // match or substitute cost
extern int *X, *Y;
#define Gap dist
#define S(i,j) Sn(X[i], Y[j])
#define UNDEF MAXVAL
#define w_ w_prime
