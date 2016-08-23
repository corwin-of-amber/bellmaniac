
#include "input.h"
#include "preface.h"


void funcA_loop(DEFINTERVALFUNC(I),DEFINTERVALFUNC(J)){
	FOR_FWD(i,DEFBEGIN(I),DEFEND(I)){
		FOR_FWD(j,DEFBEGIN(J),DEFEND(J)){
			TYPE tmp1;
			tmp1 = INITMIN;
			FOR_FWD(q,DEFBEGIN(J),min(j,DEFEND(J))){
				tmp1 = min(tmp1,(psi(i,q) + w(q,j)));
			}
			TYPE tmp2;
			tmp2 = INITMIN;
			FOR_FWD(p,DEFBEGIN(I),min(i,DEFEND(I))){
				tmp2 = min(tmp2,(psi(p,j) + w_(p,i)));
			}
			tmp2 = min(tmp1,tmp2);
			if((In(PARAM(I),(i - 1)) && In(PARAM(J),(j - 1)))){
				tmp2 = min((psi((i - 1),(j - 1)) + S(i,j)),tmp2);
			}

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
		FOR_FWD(j,DEFBEGIN(J1),DEFEND(J1)){
			TYPE tmp3;
			tmp3 = INITMIN;
			FOR_FWD(q,DEFBEGIN(J0),DEFEND(J0)){
				tmp3 = min(tmp3,(psi(i,q) + w(q,j)));
			}
			if((In(PARAM(J0),(j - 1)) && In(PARAM(I),(i - 1)))){
				tmp3 = min((psi((i - 1),(j - 1)) + S(i,j)),tmp3);
			}

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
	FOR_FWD(i,DEFBEGIN(I1),DEFEND(I1)){
		FOR_FWD(j,DEFBEGIN(J),DEFEND(J)){
			TYPE tmp4;
			tmp4 = INITMIN;
			FOR_FWD(p,DEFBEGIN(I0),DEFEND(I0)){
				tmp4 = min(tmp4,(psiCopyOpt(p,j,I0,J) + w_(p,i)));
			}
			if((In(PARAM(I0),(i - 1)) && In(PARAM(J),(j - 1)))){
				tmp4 = min((psi((i - 1),(j - 1)) + S(i,j)),tmp4);
			}

			tmp4 = min(psi(i,j),tmp4);
			psi(i,j) = tmp4;
		}
	}    /*bazinga 0*/
}

void func(DEFINTERVALFUNC(I0),DEFINTERVALFUNC(K2),DEFINTERVALFUNC(J0),DEFINTERVALFUNC(J1)){
	FOR_FWD(i,max((DEFBEGIN(I0) + 1),DEFBEGIN(K2)),min((DEFEND(I0) + 1),DEFEND(K2))){
		FOR_FWD(j,max((DEFBEGIN(J0) + 1),DEFBEGIN(J1)),min((DEFEND(J0) + 1),DEFEND(J1))){
			TYPE tmp5;
			tmp5 = psi(i,j);
			tmp5 = min(tmp5,(psi((i - 1),(j - 1)) + S(i,j)));
			psi(i,j) = tmp5;
		}
	}
}
void func0(DEFINTERVALFUNC(I0),DEFINTERVALFUNC(K3),DEFINTERVALFUNC(J0),DEFINTERVALFUNC(J1)){
	FOR_FWD(i,max((DEFBEGIN(I0) + 1),DEFBEGIN(K3)),min((DEFEND(I0) + 1),DEFEND(K3))){
		FOR_FWD(j,max((DEFBEGIN(J0) + 1),DEFBEGIN(J1)),min((DEFEND(J0) + 1),DEFEND(J1))){
			TYPE tmp6;
			tmp6 = psi(i,j);
			tmp6 = min(tmp6,(psi((i - 1),(j - 1)) + S(i,j)));
			psi(i,j) = tmp6;
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
		FOR_FWD(j,max((DEFBEGIN(J0) + 1),DEFBEGIN(L2)),min((DEFEND(J0) + 1),DEFEND(L2))){
			TYPE tmp7;
			tmp7 = psi(i,j);
			tmp7 = min(tmp7,(psi((i - 1),(j - 1)) + S(i,j)));
			psi(i,j) = tmp7;
		}
	}
}
void func2(DEFINTERVALFUNC(I0),DEFINTERVALFUNC(I1),DEFINTERVALFUNC(J0),DEFINTERVALFUNC(L3)){
	FOR_FWD(i,max((DEFBEGIN(I0) + 1),DEFBEGIN(I1)),min((DEFEND(I0) + 1),DEFEND(I1))){
		FOR_FWD(j,max((DEFBEGIN(J0) + 1),DEFBEGIN(L3)),min((DEFEND(J0) + 1),DEFEND(L3))){
			TYPE tmp8;
			tmp8 = psi(i,j);
			tmp8 = min(tmp8,(psi((i - 1),(j - 1)) + S(i,j)));
			psi(i,j) = tmp8;
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
		FOR_FWD(j,max((DEFBEGIN(J0) + 1),DEFBEGIN(J1)),min((DEFEND(J0) + 1),DEFEND(J1))){
			TYPE tmp9;
			tmp9 = psi(i,j);
			tmp9 = min(tmp9,(psi((i - 1),(j - 1)) + S(i,j)));
			psi(i,j) = tmp9;
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
		cilk_spawn funcB_rec(PARAM(I0),PARAM(J0),PARAM(J1));;
		cilk_spawn funcC_rec(PARAM(I0),PARAM(I1),PARAM(J0));;
		func3(PARAM(I0),PARAM(I1),PARAM(J0),PARAM(J1));
		cilk_sync;

		cilk_spawn funcA_rec(PARAM(I0),PARAM(J1));;
		funcA_rec(PARAM(I1),PARAM(J0));
		cilk_sync;

		funcC_rec(PARAM(I0),PARAM(I1),PARAM(J1));
		funcB_rec(PARAM(I1),PARAM(J0),PARAM(J1));
		funcA_rec(PARAM(I1),PARAM(J1));
	}

}
