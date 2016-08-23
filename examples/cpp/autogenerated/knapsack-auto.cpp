
#include "input.h"
#include "preface.h"


void funcA_loop(DEFINTERVALFUNC(I),DEFINTERVALFUNC(J)){
	FOR_FWD(i,DEFBEGIN(I)+1,DEFEND(I)){
		FOR_FWD(j,DEFBEGIN(J),DEFEND(J)){
			TYPE tmp1;
			tmp1 = psi(i,j);
			tmp1 = max(tmp1,psi((i - 1),j));
			//cMaxRec++;
			if( In(PARAM(J),(j - w(i)))){
				tmp1 = max(tmp1,(psi((i - 1),(j - w(i))) + v(i)));
				//cMaxRec++;
			}

			psi(i,j) = tmp1;
		}
	}    /*bazinga 0*/
}

void funcB_loop(DEFINTERVALFUNC(I),DEFINTERVALFUNC(J0),DEFINTERVALFUNC(J1)){
	//DEFINTERVALSTMT_UNION(J, J0, J1);
	FOR_FWD(i,DEFBEGIN(I)+1,DEFEND(I)){
		FOR_FWD(j,DEFBEGIN(J1),DEFEND(J1)){
			if(In(PARAM(J0),(j - w(i)))){
				TYPE tmp2;
				tmp2 = psi(i,j);
				tmp2 = max(tmp2,(psi((i - 1),(j - w(i))) + v(i)));
				//cMaxRec++;
				psi(i,j) = tmp2;
			}

		}
	}    /*bazinga 0*/
}

void func(DEFINTERVALFUNC(I0),DEFINTERVALFUNC(I1),DEFINTERVALFUNC(J),DEFINTERVALFUNC(J0),DEFINTERVALFUNC(K2)){
	{
		//if (DEFBEGIN(I1) != DEFEND(I0)) return;
		LET(i,DEFBEGIN(I1));
	//FOR_FWD(i,DEFBEGIN(I1),DEFEND(I1)){
		FOR_FWD(j,DEFBEGIN(K2),DEFEND(K2)){
			if(In(PARAM(J0),(j - w(i)))){
				TYPE tmp3;
				tmp3 = psi(i,j);
				tmp3 = max(tmp3,(psi((i - 1),(j - w(i))) + v(i)));
				//cMaxRec++;
				psi(i,j) = tmp3;
			}

		}
	}
}
void func0(DEFINTERVALFUNC(I0),DEFINTERVALFUNC(I1),DEFINTERVALFUNC(J),DEFINTERVALFUNC(J0),DEFINTERVALFUNC(K3)){
	{
		//if (DEFBEGIN(I1) != DEFEND(I0)) return;
		LET(i,DEFBEGIN(I1));
	//FOR_FWD(i,DEFBEGIN(I1),DEFEND(I1)){
		FOR_FWD(j,DEFBEGIN(K3),DEFEND(K3)){
			if(In(PARAM(J0),(j - w(i)))){
				TYPE tmp4;
				tmp4 = psi(i,j);
				tmp4 = max(tmp4,(psi((i - 1),(j - w(i))) + v(i)));
				//cMaxRec++;
				psi(i,j) = tmp4;
			}

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
		DEFINTERVALSTMT_LOWER(K0, J0);
		DEFINTERVALSTMT_UPPER(K1, J0);
		DEFINTERVALSTMT_LOWER(K2, J1);
		DEFINTERVALSTMT_UPPER(K3, J1);
		cilk_spawn funcB_rec(PARAM(I0),PARAM(K0),PARAM(K2));;
		cilk_spawn funcB_rec(PARAM(I0),PARAM(K0),PARAM(K3));;
		cilk_spawn func(PARAM(I0),PARAM(I1),PARAM(J),PARAM(J0),PARAM(K2));;
		func0(PARAM(I0),PARAM(I1),PARAM(J),PARAM(J0),PARAM(K3));
		cilk_sync;

		cilk_spawn funcB_rec(PARAM(I0),PARAM(K1),PARAM(K2));;
		cilk_spawn funcB_rec(PARAM(I0),PARAM(K1),PARAM(K3));;
		cilk_spawn funcB_rec(PARAM(I1),PARAM(K0),PARAM(K2));;
		funcB_rec(PARAM(I1),PARAM(K0),PARAM(K3));
		cilk_sync;

		cilk_spawn funcB_rec(PARAM(I1),PARAM(K1),PARAM(K2));;
		funcB_rec(PARAM(I1),PARAM(K1),PARAM(K3));
		cilk_sync;

	}

}

void func1(DEFINTERVALFUNC(I0),DEFINTERVALFUNC(I1),DEFINTERVALFUNC(J),DEFINTERVALFUNC(J0),DEFINTERVALFUNC(J1)){
	{
		if (DEFBEGIN(I1) != DEFEND(I0)) return;
		LET(i,DEFBEGIN(I1));

		FOR_FWD(j,DEFBEGIN(J0),DEFEND(J0)){
			TYPE tmp6;
			tmp6 = psi(i,j);
			tmp6 = max(tmp6,psi((i - 1),j));
			//cMaxRec++;
			if(In(PARAM(J),(j - w(i)))){
				tmp6 = max(tmp6,(psi((i - 1),(j - w(i))) + v(i)));
				//cMaxRec++;
			}

			psi(i,j) = tmp6;
		}
	}
}
void func2(DEFINTERVALFUNC(I0),DEFINTERVALFUNC(I1),DEFINTERVALFUNC(J),DEFINTERVALFUNC(J0),DEFINTERVALFUNC(J1)){
	{
		//if (DEFBEGIN(I1) != DEFEND(I0)) return;
		LET(i,DEFBEGIN(I1));

		FOR_FWD(j,DEFBEGIN(J1),DEFEND(J1)){
			TYPE tmp6;
			tmp6 = psi(i,j);
			tmp6 = max(tmp6,psi((i - 1),j));
			//cMaxRec++;
			if(In(PARAM(J),(j - w(i)))){
				tmp6 = max(tmp6,(psi((i - 1),(j - w(i))) + v(i)));
				//cMaxRec++;
			}

			psi(i,j) = tmp6;
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
		funcB_rec(PARAM(I0),PARAM(J0),PARAM(J1));
		funcA_rec(PARAM(I0),PARAM(J1));
		cilk_spawn func1(PARAM(I0),PARAM(I1),PARAM(J),PARAM(J0),PARAM(J1));;
		func2(PARAM(I0),PARAM(I1),PARAM(J),PARAM(J0),PARAM(J1));
		cilk_sync;

		funcA_rec(PARAM(I1),PARAM(J0));
		funcB_rec(PARAM(I1),PARAM(J0),PARAM(J1));
		funcA_rec(PARAM(I1),PARAM(J1));
	}

}
