#include <stdlib.h>
#include <stdio.h>
#include <assert.h>
#include <time.h>

typedef bool bit;

struct scalar { bool supp; int val; };

typedef scalar (*fun0)(int, int);
typedef scalar (*fun1)(int);
typedef bool   (*fun1b)(int);
typedef bool   (*fun2b)(int, int);
//typedef scalar (*fun3)(scalar, scalar);

scalar mk_scalar(bool supp, int val) { scalar sc; sc.val = val; sc.supp = supp; return sc; }
bool eq(scalar a, scalar b) { return (a.supp == b.supp) && (a.val == b.val); }

scalar some(int val) { return mk_scalar(true, val); }
scalar when(bit guard, int val) { return mk_scalar(guard, guard?val:0); }
scalar only(bit guard, scalar val) { return when(guard && val.supp, val.val); /* guard ? val : bot;*/ }
scalar slash(scalar a, scalar b) { if (!a.supp) return b; else return a; }


scalar apply2(fun0 op, scalar a, scalar b) { return only(a.supp && b.supp, op(a.val, b.val)); }
bit    applyb1(fun1b op, scalar a) { return a.supp && op(a.val); }
bit    applyb2(fun2b op, scalar a, scalar b) { return a.supp && b.supp && op(a.val, b.val); }


scalar plus(int a, int b) { return some(a+b); }

scalar min_acc(scalar acc, int n, fun1 seq) {
  for (int i = 0; i < n; i++) {
    scalar v = seq(i);
    if (v.supp && (!acc.supp || v.val < acc.val)) acc = v;
  }
  return acc;
}



int d0 = 4;
int d1 = 2;
int d2 = 6;
int d3 = 1;
int d4 = 3;
int d5 = 5;

bool J0(int i) { return i < d0; }
bool J1(int i) { return i >= d0; }
bool K0(int i) { return i < d1; }
bool K1(int i) { return i >= d1 && i < d0; }
bool K2(int i) { return i >= d0 && i < d2; }
bool K3(int i) { return i >= d2; }
bool L0(int i) { return i < d3; }
bool L1(int i) { return i >= d3 && i < d1; }
bool L2(int i) { return i >= d1 && i < d4; }
bool L3(int i) { return i >= d4 && i < d0; }
bool L4(int i) { return i >= d0 && i < d5; }
bool L5(int i) { return i >= d5 && i < d2; }

bool X(int i, int j) { return K0(i) && K3(j); }

int a1, a2, a3;
bit b1[2], b2[2], b3[2];

bool subsort(int t, int i) {
    switch (t) {
        case 0:  return L0(i); case 1:  return L1(i); case 2:  return L2(i); case 3: return L3(i); case 4: return L4(i); case 5: return L5(i);
        case 6:  return K0(i); case 7:  return K1(i); case 8:  return K2(i); case 9: return K3(i);
        case 10: return J0(i); case 11: return J1(i); default: return true; 
    } 
}

bool subsort_with_offsets(int t, bit b[2], int i) {
    return subsort(t, i) || (b[0] && subsort(t, i + 1)) || (b[1] && subsort(t, i-1));
}

const int W = 13;

bool P1(int i) { return subsort(a1, i); }
bool P2(int i) { return subsort(a2, i); }
bool P3(int i) { return subsort(a3, i); }

bool param(int t, int i) {
    switch (t) { case 0: return P1(i); case 1: return P2(i); case 2: return P3(i); default: return false; }
}

scalar w(int a, int b, int c) { return some(a*b*c); }

const int SZ = 8;

scalar _psi[SZ][SZ];
scalar psi(int a, int b) { return _psi[a][b]; }

scalar _theta[SZ][SZ];
scalar theta(int a, int b) { return _theta[a][b]; }

int a4;

bool Q(int i, int j) {
    bool acc = false;
    for (int p = 0; p < 3; ++p)
        for (int q = 0; q < 3; ++q)
            if ((a4 >> (p*3+q)) & 1) acc = acc || (param(p, i) && param(q, j));
    return acc || X(i,j);
}

//bool Q(int i, int j) { return (P1(i) && P1(j)) || (P2(i) && P2(j)) || X(i,j); }

scalar thetaQ(int a, int b) { return only(Q(a,b), theta(a,b)); }


class closure_h {
public:
    static int i;
    static int j;
    static fun0 theta;

    /* this is for A */
    static scalar f(int k) {
        return apply2(plus, apply2(plus, only((i < k), theta(i, k)), only((k < j), theta(k, j))), w(i, k, j)); 
    }

    /* this is for B */
    static scalar fb0(int k) {
        return only(K3(k), apply2(plus, apply2(plus, only((i < k), theta(i, k)), only((k < j), theta(k, j))), w(i, k, j)));
    }
    static scalar fb1(int k) { 
        return only(K0(k), apply2(plus, apply2(plus, only((i < k), theta(i, k)), only((k < j), theta(k, j))), w(i, k, j))); 
    }
};

int closure_h::i; int closure_h::j; fun0 closure_h::theta;

scalar h(int n, fun0 theta, int i, int j) {
    closure_h::i = i;
    closure_h::j = j;
    closure_h::theta = theta;

    /* A quadrant [4] */
    //return only((i < j), slash(slash(only((J0(i) && J0(j)), psi(i, j)), only((J0(i) && J1(j)), psi(i, j))), only((J1(i) && J1(j)), min_acc(psi(i, j), n, closure_h::f))));

    /* A quadrant [2] */
    //return only((i < j), slash(slash(only((J0(i) && J0(j)), psi(i, j)), only((J0(i) && J1(j)), min_acc(psi(i, j), n, closure_h::f))), only((J1(i) && J1(j)), psi(i, j))));

    /* B quadrant [2] */
    return slash(slash(only((J0(i) && J0(j)), psi(i, j)), only((J0(i) && J1(j)), slash(slash(slash(only((K0(i) && K2(j)), psi(i, j)), only((K0(i) && K3(j)), min_acc(min_acc(psi(i, j), n, closure_h::fb0), n, closure_h::fb1))), only((K1(i) && K2(j)), psi(i, j))), only((K1(i) && K3(j)), psi(i, j))))), only((J1(i) && J1(j)), psi(i, j)));
}

class closure_A {
public:
    static int i;
    static int j;
    static fun0 psi0;
    static fun0 theta;
    static scalar f(int k) {
      return apply2(plus, apply2(plus, only((P1(k) && (i < k)), theta(i, k)), only((P1(k) && (k < j)), theta(k, j))), w(i, k, j)); 
    }
};

int closure_A::i; int closure_A::j; fun0 closure_A::psi0; fun0 closure_A::theta;

scalar A(int n, fun0 psi0, fun0 theta, int i, int j) {
    closure_A::i = i;
    closure_A::j = j;
    closure_A::psi0 = psi0;
    closure_A::theta = theta;

    return only(((P1(i) && P1(j)) && (i < j)), min_acc(psi0(i, j), n, closure_A::f));
}

class closure_B {
public:
    static int i;
    static int j;
    static fun0 psi0;
    static fun0 theta;
    static scalar f(int k) {
        return apply2(plus, apply2(plus, only((i < k), theta(i, k)), only((k < j), theta(k, j))), w(i, k, j));
    }
};

int closure_B::i; int closure_B::j; fun0 closure_B::psi0; fun0 closure_B::theta;

scalar B(int n, fun0 psi0, fun0 theta, int i, int j) {
    closure_B::i = i;
    closure_B::j = j;
    closure_B::psi0 = psi0;
    closure_B::theta = theta;

    return slash(slash(only((P1(i) && P1(j)), psi0(i, j)), only((P1(i) && P2(j)), min_acc(psi0(i, j), n, closure_B::f))), only((P2(i) && P2(j)), psi0(i, j)));
}

class closure_C {
public:
    static int i;
    static int j;
    static fun0 psi0;
    static fun0 theta;
    static scalar f(int k) {
        return only(P2(k), apply2(plus, apply2(plus, psi0(i, k), psi0(k, j)), w(i, k, j)));
    }
};

int closure_C::i; int closure_C::j; fun0 closure_C::psi0; fun0 closure_C::theta;

scalar C(int n, fun0 psi0, fun0 theta, int i, int j) {
    closure_C::i = i;
    closure_C::j = j;
    closure_C::psi0 = psi0;
    closure_C::theta = theta;

    return slash(slash(only((P1(i) && P2(j)), psi0(i, j)), only((P1(i) && P3(j)), min_acc(psi0(i, j), n, closure_C::f))), only((P2(i) && P3(j)), psi0(i, j)));
}


template <int SZ>
void fill_array(scalar arr[SZ][SZ]) {
  for (int i = 0; i < SZ; i++)
    for (int j = 0; j < SZ; j++) {
      arr[i][j].supp = rand() & 1;
      arr[i][j].val = rand();
    }
}

void randomize_inputs(int n) {
    d0 = rand() % n;
    d1 = rand() % (d0 + 1);
    d2 = d0 + rand() % (n - d0);
    d3 = rand() % (d1 + 1);
    d4 = d1 + rand() % (d0 - d1 + 1);
    d5 = d0 + rand() % (d2 - d0 + 1);

    fill_array(_psi);
    fill_array(_theta);
}


int main(int argc, char *argv[]) {
    
    int n = SZ;

    int i, j;

    srand(time(0));

    const int SIMITER = 1000;

    for (a1 = 0; a1 < W; a1++) {
    for (a2 = 0; a2 < W; a2++) {
    for (int b123 = 0; b123 < 0x10; b123++) {
    b1[0] = (b123 & 1); b1[1] = (b123 & 2); b2[0] = (b123 & 4); b2[1] = (b123 & 8);
    bool correct = false;
    for (a4 = 0; a4 < (1 << 9); a4++) {
    int c;
    for (c = 0; c < SIMITER; ++c) {
        randomize_inputs(n);
        i = rand() % n;
        j = rand() % n;

        if (X(i,j)) {
            if (!eq(h(n, theta, i, j), h(n, thetaQ, i, j))) break;
            if (!eq(h(n, thetaQ, i, j), B(n, psi, thetaQ, i, j))) break;
        }
    }
    correct = correct || (c == SIMITER);
    }
    printf("%d ", correct ? 1 : 0);
    }
    }
    printf("\n");
    }

    for (a1 = 0; a1 < W; a1++) {
    for (a3 = 0; a3 < W; a3++) {
    for (a2 = 0; a2 < W; a2++) {
    for (int b123 = 0; b123 < 0x40; b123++) {
    b1[0] = (b123 & 1); b1[1] = (b123 & 2); b2[0] = (b123 & 4); b2[1] = (b123 & 8);
    b3[0] = (b123 & 10); b3[1] = (b123 & 0x20);
    bool correct = false;
    for (a4 = 0; a4 < (1 << 9); a4++) {
    int c;
    for (c = 0; c < SIMITER; ++c) {
        randomize_inputs(n);
        i = rand() % n;
        j = rand() % n;

        if (X(i,j)) {
            if (!eq(h(n, theta, i, j), h(n, thetaQ, i, j))) break;
            if (!eq(h(n, thetaQ, i, j), C(n, psi, thetaQ, i, j))) break;
        }
    }
    correct = correct || (c == SIMITER);
    }
    printf("%d ", correct ? 1 : 0);
    }
    }
    printf("\t");
    }
    printf("\n");
    }
}

