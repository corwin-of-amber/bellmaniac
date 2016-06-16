
#include "preface.h"
#include "input.h"


void funcA_loop(DEFINTERVALFUNC(J)){
	FOR_BWD(i,DEFBEGIN(J),DEFEND(J)){
		FOR_FWD(j,max((i + 1),DEFBEGIN(J)),DEFEND(J)){
			int tmp1;
			tmp1 = INITMIN;
			FOR_FWD(k,max((i + 1),DEFBEGIN(J)),min(j,DEFEND(J))){
				tmp1 = min(tmp1,((theta(i,k) + theta(k,j)) + w(i,k,j)));
			}
			psi(i,j) = min(psi(i,j),tmp1);
		}
	}    /*bazinga 0*/
}

void funcB_loop(DEFINTERVALFUNC(J0),DEFINTERVALFUNC(J1)){
	DEFINTERVALSTMT_UNION(J, J0, J1);
	FOR_BWD(i,DEFBEGIN(J0),DEFEND(J0)){
		FOR_FWD(j,max(DEFBEGIN(J1),DEFBEGIN(J1)),min(DEFEND(J1),DEFEND(J1))){
			int tmp2;
			tmp2 = INITMIN;
			FOR_FWD(k,max(max((i + 1),DEFBEGIN(J0)),DEFBEGIN(J)),min(min(DEFEND(J0),j),DEFEND(J))){
				tmp2 = min(tmp2,((theta(i,k) + theta(k,j)) + w(i,k,j)));
			}
			FOR_FWD(k,max(max((i + 1),DEFBEGIN(J1)),DEFBEGIN(J)),min(min(DEFEND(J1),j),DEFEND(J))){
				tmp2 = min(tmp2,((theta(i,k) + theta(k,j)) + w(i,k,j)));
			}
			psi(i,j) = min(psi(i,j),tmp2);
		}
	}    /*bazinga 0*/
}

void funcC_loop(DEFINTERVALFUNC(K0),DEFINTERVALFUNC(K1),DEFINTERVALFUNC(K2)){
	__declspec(align(ALIGNMENT)) TYPE V[B * B];

	copy_dist_part(V,PARAM(K1),PARAM(K2));
	FOR_FWD(i,DEFBEGIN(K0),DEFEND(K0)){
		FOR_FWD(j,max(DEFBEGIN(K2),DEFBEGIN(K2)),min(DEFEND(K2),DEFEND(K2))){
			int tmp3;
			tmp3 = INITMIN;
			FOR_FWD(k,max(DEFBEGIN(K1),DEFBEGIN(K1)),min(DEFEND(K1),DEFEND(K1))){
				tmp3 = min(tmp3,((psi(i,k) + psiCopyOpt(k,j,K1,K2)) + w(i,k,j)));
			}
			psi(i,j) = min(psi(i,j),tmp3);
		}
	}    /*bazinga 0*/
}


void funcC_rec(DEFINTERVALFUNC(K0),DEFINTERVALFUNC(K1),DEFINTERVALFUNC(K2)){
	if(BASE_CONSTRAINT(PARAM(K0),PARAM(K1),PARAM(K2))){
		funcC_loop(PARAM(K0),PARAM(K1),PARAM(K2));
	} else {
		DEFINTERVALSTMT_LOWER(L0, K0);
		DEFINTERVALSTMT_UPPER(L1, K0);
		DEFINTERVALSTMT_LOWER(L2, K1);
		DEFINTERVALSTMT_UPPER(L3, K1);
		DEFINTERVALSTMT_LOWER(L4, K2);
		DEFINTERVALSTMT_UPPER(L5, K2);
		cilk_spawn funcC_rec(PARAM(L0),PARAM(L3),PARAM(L4));;
		cilk_spawn funcC_rec(PARAM(L0),PARAM(L3),PARAM(L5));;
		cilk_spawn funcC_rec(PARAM(L1),PARAM(L3),PARAM(L4));;
		funcC_rec(PARAM(L1),PARAM(L3),PARAM(L5));
		cilk_sync;

		cilk_spawn funcC_rec(PARAM(L0),PARAM(L2),PARAM(L4));;
		cilk_spawn funcC_rec(PARAM(L0),PARAM(L2),PARAM(L5));;
		cilk_spawn funcC_rec(PARAM(L1),PARAM(L2),PARAM(L4));;
		funcC_rec(PARAM(L1),PARAM(L2),PARAM(L5));
		cilk_sync;

	}

}


void funcB_rec(DEFINTERVALFUNC(J0),DEFINTERVALFUNC(J1)){
	if(BASE_CONSTRAINT(PARAM(J0),PARAM(J1))){
		funcB_loop(PARAM(J0),PARAM(J1));
	} else {
		DEFINTERVALSTMT_UNION(J, J0, J1);
		DEFINTERVALSTMT_LOWER(K0, J0);
		DEFINTERVALSTMT_UPPER(K1, J0);
		DEFINTERVALSTMT_LOWER(K2, J1);
		DEFINTERVALSTMT_UPPER(K3, J1);
		funcB_rec(PARAM(K1),PARAM(K2));
		cilk_sync;

		cilk_spawn funcC_rec(PARAM(K0),PARAM(K1),PARAM(K2));;
		funcC_rec(PARAM(K1),PARAM(K2),PARAM(K3));
		cilk_sync;

		cilk_spawn funcB_rec(PARAM(K0),PARAM(K2));;
		funcB_rec(PARAM(K1),PARAM(K3));
		cilk_sync;

		funcC_rec(PARAM(K0),PARAM(K1),PARAM(K3));
		cilk_sync;

		funcC_rec(PARAM(K0),PARAM(K2),PARAM(K3));
		cilk_sync;

		funcB_rec(PARAM(K0),PARAM(K3));
		cilk_sync;

	}

}


void funcA_rec(DEFINTERVALFUNC(J)){
	if(BASE_CONSTRAINT(PARAM(J))){
		funcA_loop(PARAM(J));
	} else {
		DEFINTERVALSTMT_LOWER(J0, J);
		DEFINTERVALSTMT_UPPER(J1, J);
		cilk_spawn funcA_rec(PARAM(J0));;
		funcA_rec(PARAM(J1));
		cilk_sync;

		funcB_rec(PARAM(J0),PARAM(J1));
		cilk_sync;

	}

}