
#include "input.h"
#include "preface.h"


void funcA_loop(DEFINTERVALFUNC(I),DEFINTERVALFUNC(J)){
	FOR_FWD(i,max((DEFBEGIN(I) + 1),DEFBEGIN(I)),min((DEFEND(I) + 1),DEFEND(I))){
		FOR_FWD(j,max((DEFBEGIN(J) + 1),DEFBEGIN(J)),min((DEFEND(J) + 1),DEFEND(J))){
			TYPE _slash_tmp1;
			_slash_tmp1 = psi(i,j);
			if(IS_UNDEFINED(_slash_tmp1)){
				if(delta(i,j)){
					_slash_tmp1 = (psi((i - 1),(j - 1)) + 1);
				}

				if((IS_UNDEFINED(_slash_tmp1) && (!delta(i,j)))){
					_slash_tmp1 = oplus(psi(i,(j - 1)),psi((i - 1),j));
				}

			}

			psi(i,j) = _slash_tmp1;
		}
	}    /*bazinga 0*/
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
		funcA_rec(PARAM(I0),PARAM(J___J1_J1minus1));
		funcA_rec(PARAM(I___I1_I1minus1),PARAM(J0));
		funcA_rec(PARAM(I___I1_I1minus1),PARAM(J___J1_J1minus1));
	}

}
