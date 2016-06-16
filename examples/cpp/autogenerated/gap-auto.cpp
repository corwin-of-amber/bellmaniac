
#include "preface.h"
#include "input.h"


void funcA_loop(DEFINTERVALFUNC(I),DEFINTERVALFUNC(J)){
	__declspec(align(ALIGNMENT)) TYPE V[B * B];

	copy_dist_part(V,PARAM(I),PARAM(J));
	FOR_FWD(i,DEFBEGIN(I),DEFEND(I)){
		FOR_FWD(j,DEFBEGIN(J),DEFEND(J)){
			int tmp1;
			tmp1 = INITMIN;
			FOR_FWD(q,DEFBEGIN(J),min(j,DEFEND(J))){
				tmp1 = min(tmp1,(psi(i,q) + w(q,j)));
			}
			int tmp2;
			tmp2 = INITMIN;
			FOR_FWD(p,DEFBEGIN(I),min(i,DEFEND(I))){
				tmp2 = min(tmp2,(psiCopyOpt(p,j,I,J) + w_(p,i)));
			}
			tmp2 = min(tmp1,tmp2);
			tmp2 = min(GUARDED((In(PARAM(I),(i - 1)) && In(PARAM(J),(j - 1))),(psi((i - 1),(j - 1)) + S(i,j))),tmp2);
			tmp2 = min(psi(i,j),tmp2);
			psi(i,j) = tmp2;
		}
	}    /*bazinga 0*/
}

void funcB_loop(DEFINTERVALFUNC(I),DEFINTERVALFUNC(J0),DEFINTERVALFUNC(J1)){
	DEFINTERVALSTMT_UNION(J, J0, J1);
	DEFINTERVALSTMT_LOWER(I0, I);
	DEFINTERVALSTMT_UPPER(I1, I);
	FOR_FWD(i,DEFBEGIN(I),DEFEND(I)){
		FOR_FWD(j,max(DEFBEGIN(J1),DEFBEGIN(J1)),min(DEFEND(J1),DEFEND(J1))){
			int tmp3;
			tmp3 = INITMIN;
			FOR_FWD(q,max(DEFBEGIN(J0),DEFBEGIN(J0)),min(DEFEND(J0),DEFEND(J0))){
				tmp3 = min(tmp3,(psi(i,q) + w(q,j)));
			}
			tmp3 = min(GUARDED((In(PARAM(J0),(j - 1)) && In(PARAM(I),(i - 1))),(psi((i - 1),(j - 1)) + S(i,j))),tmp3);
			tmp3 = min(psi(i,j),tmp3);
			psi(i,j) = tmp3;
		}
	}    /*bazinga 0*/
}

void funcC_loop(DEFINTERVALFUNC(I0),DEFINTERVALFUNC(I1),DEFINTERVALFUNC(J)){
	DEFINTERVALSTMT_UNION(I, I0, I1);
	DEFINTERVALSTMT_LOWER(J0, J);
	DEFINTERVALSTMT_UPPER(J1, J);
	__declspec(align(ALIGNMENT)) TYPE V[B * B];

	copy_dist_part(V,PARAM(I0),PARAM(J));
	FOR_FWD(i,max(DEFBEGIN(I1),DEFBEGIN(I1)),min(DEFEND(I1),DEFEND(I1))){
		FOR_FWD(j,DEFBEGIN(J),DEFEND(J)){
			int tmp4;
			tmp4 = INITMIN;
			FOR_FWD(p,max(DEFBEGIN(I0),DEFBEGIN(I0)),min(DEFEND(I0),DEFEND(I0))){
				tmp4 = min(tmp4,(psiCopyOpt(p,j,I0,J) + w_(p,i)));
			}
			tmp4 = min(GUARDED((In(PARAM(I0),(i - 1)) && In(PARAM(J),(j - 1))),(psi((i - 1),(j - 1)) + S(i,j))),tmp4);
			tmp4 = min(psi(i,j),tmp4);
			psi(i,j) = tmp4;
		}
	}    /*bazinga 0*/
}

void func(DEFINTERVALFUNC(I0),DEFINTERVALFUNC(K2),DEFINTERVALFUNC(J0),DEFINTERVALFUNC(J1)){
	FOR_FWD(i,max((DEFBEGIN(I0) + 1),DEFBEGIN(K2)),min((DEFEND(I0) + 1),DEFEND(K2))){
		FOR_FWD(j,max((DEFBEGIN(J0) + 1),max(DEFBEGIN(J1),DEFBEGIN(J1))),min((DEFEND(J0) + 1),min(DEFEND(J1),DEFEND(J1)))){
			psi(i,j) = min(psi(i,j),(psi((i - 1),(j - 1)) + S(i,j)));
		}
	}
}
void func0(DEFINTERVALFUNC(I0),DEFINTERVALFUNC(K3),DEFINTERVALFUNC(J0),DEFINTERVALFUNC(J1)){
	FOR_FWD(i,max((DEFBEGIN(I0) + 1),DEFBEGIN(K3)),min((DEFEND(I0) + 1),DEFEND(K3))){
		FOR_FWD(j,max((DEFBEGIN(J0) + 1),max(DEFBEGIN(J1),DEFBEGIN(J1))),min((DEFEND(J0) + 1),min(DEFEND(J1),DEFEND(J1)))){
			psi(i,j) = min(psi(i,j),(psi((i - 1),(j - 1)) + S(i,j)));
		}
	}
}
void funcC_rec(DEFINTERVALFUNC(I0),DEFINTERVALFUNC(I1),DEFINTERVALFUNC(J)){
	if(BASE_CONSTRAINT(PARAM(I0),PARAM(I1),PARAM(J))){
		funcC_loop(PARAM(I0),PARAM(I1),PARAM(J));
	} else {
		DEFINTERVALSTMT_UNION(I, I0, I1);
		DEFINTERVALSTMT_LOWER(K0, I0);
		DEFINTERVALSTMT_UPPER(K1, I0);
		DEFINTERVALSTMT_LOWER(K2, I1);
		DEFINTERVALSTMT_UPPER(K3, I1);
		DEFINTERVALSTMT_LOWER(J0, J);
		DEFINTERVALSTMT_UPPER(J1, J);
		cilk_spawn funcC_rec(PARAM(K0),PARAM(K2),PARAM(J0));;
		cilk_spawn func(PARAM(I0),PARAM(K2),PARAM(J0),PARAM(J1));;
		cilk_spawn funcC_rec(PARAM(K0),PARAM(K3),PARAM(J0));;
		func0(PARAM(I0),PARAM(K3),PARAM(J0),PARAM(J1));
		cilk_sync;

		cilk_spawn funcC_rec(PARAM(K1),PARAM(K2),PARAM(J0));;
		cilk_spawn funcC_rec(PARAM(K0),PARAM(K2),PARAM(J1));;
		cilk_spawn funcC_rec(PARAM(K1),PARAM(K3),PARAM(J0));;
		funcC_rec(PARAM(K0),PARAM(K3),PARAM(J1));
		cilk_sync;

		cilk_spawn funcC_rec(PARAM(K1),PARAM(K2),PARAM(J1));;
		funcC_rec(PARAM(K1),PARAM(K3),PARAM(J1));
		cilk_sync;

	}

}

void func1(DEFINTERVALFUNC(I0),DEFINTERVALFUNC(I1),DEFINTERVALFUNC(J0),DEFINTERVALFUNC(L2)){
	FOR_FWD(i,max((DEFBEGIN(I0) + 1),DEFBEGIN(I1)),min((DEFEND(I0) + 1),DEFEND(I1))){
		FOR_FWD(j,max((DEFBEGIN(J0) + 1),max(DEFBEGIN(L2),DEFBEGIN(L2))),min((DEFEND(J0) + 1),min(DEFEND(L2),DEFEND(L2)))){
			psi(i,j) = min(psi(i,j),(psi((i - 1),(j - 1)) + S(i,j)));
		}
	}
}
void func2(DEFINTERVALFUNC(I0),DEFINTERVALFUNC(I1),DEFINTERVALFUNC(J0),DEFINTERVALFUNC(L3)){
	FOR_FWD(i,max((DEFBEGIN(I0) + 1),DEFBEGIN(I1)),min((DEFEND(I0) + 1),DEFEND(I1))){
		FOR_FWD(j,max((DEFBEGIN(J0) + 1),max(DEFBEGIN(L3),DEFBEGIN(L3))),min((DEFEND(J0) + 1),min(DEFEND(L3),DEFEND(L3)))){
			psi(i,j) = min(psi(i,j),(psi((i - 1),(j - 1)) + S(i,j)));
		}
	}
}
void funcB_rec(DEFINTERVALFUNC(I),DEFINTERVALFUNC(J0),DEFINTERVALFUNC(J1)){
	if(BASE_CONSTRAINT(PARAM(I),PARAM(J0),PARAM(J1))){
		funcB_loop(PARAM(I),PARAM(J0),PARAM(J1));
	} else {
		DEFINTERVALSTMT_UNION(J, J0, J1);
		DEFINTERVALSTMT_LOWER(I0, I);
		DEFINTERVALSTMT_UPPER(I1, I);
		DEFINTERVALSTMT_LOWER(L0, J0);
		DEFINTERVALSTMT_UPPER(L1, J0);
		DEFINTERVALSTMT_LOWER(L2, J1);
		DEFINTERVALSTMT_UPPER(L3, J1);
		cilk_spawn funcB_rec(PARAM(I0),PARAM(L0),PARAM(L2));;
		cilk_spawn funcB_rec(PARAM(I0),PARAM(L0),PARAM(J1));;
		cilk_spawn func1(PARAM(I0),PARAM(I1),PARAM(J0),PARAM(L2));;
		func2(PARAM(I0),PARAM(I1),PARAM(J0),PARAM(L3));
		cilk_sync;

		cilk_spawn funcB_rec(PARAM(I0),PARAM(L1),PARAM(L2));;
		cilk_spawn funcB_rec(PARAM(I0),PARAM(L1),PARAM(L3));;
		cilk_spawn funcB_rec(PARAM(I1),PARAM(L0),PARAM(L2));;
		funcB_rec(PARAM(I1),PARAM(L0),PARAM(L3));
		cilk_sync;

		cilk_spawn funcB_rec(PARAM(I1),PARAM(L1),PARAM(L2));;
		funcB_rec(PARAM(I1),PARAM(L1),PARAM(J1));
		cilk_sync;

	}

}

void func3(DEFINTERVALFUNC(I0),DEFINTERVALFUNC(I1),DEFINTERVALFUNC(J0),DEFINTERVALFUNC(J1)){
	FOR_FWD(i,max((DEFBEGIN(I0) + 1),DEFBEGIN(I1)),min((DEFEND(I0) + 1),DEFEND(I1))){
		FOR_FWD(j,max((DEFBEGIN(J0) + 1),max(DEFBEGIN(J1),DEFBEGIN(J1))),min((DEFEND(J0) + 1),min(DEFEND(J1),DEFEND(J1)))){
			psi(i,j) = min(psi(i,j),(psi((i - 1),(j - 1)) + S(i,j)));
		}
	}
}
void funcA_rec(DEFINTERVALFUNC(I),DEFINTERVALFUNC(J)){
	if(BASE_CONSTRAINT(PARAM(I),PARAM(J))){
		funcA_loop(PARAM(I),PARAM(J));
	} else {
		DEFINTERVALSTMT_LOWER(I0, I);
		DEFINTERVALSTMT_UPPER(I1, I);
		DEFINTERVALSTMT_LOWER(J0, J);
		DEFINTERVALSTMT_UPPER(J1, J);
		funcA_rec(PARAM(I0),PARAM(J0));
		cilk_sync;

		cilk_spawn funcB_rec(PARAM(I0),PARAM(J0),PARAM(J1));;
		cilk_spawn funcC_rec(PARAM(I0),PARAM(I1),PARAM(J0));;
		func3(PARAM(I0),PARAM(I1),PARAM(J0),PARAM(J1));
		cilk_sync;

		cilk_spawn funcA_rec(PARAM(I0),PARAM(J1));;
		funcA_rec(PARAM(I1),PARAM(J0));
		cilk_sync;

		funcC_rec(PARAM(I0),PARAM(I1),PARAM(J1));
		cilk_sync;

		funcB_rec(PARAM(I1),PARAM(J0),PARAM(J1));
		cilk_sync;

		funcA_rec(PARAM(I1),PARAM(J1));
		cilk_sync;

	}

}
