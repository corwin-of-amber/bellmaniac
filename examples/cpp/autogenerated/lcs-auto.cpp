
#include "preface.h"
#include "input.h"


void funcA_loop(DEFINTERVALFUNC(I),DEFINTERVALFUNC(J)){
	FOR_FWD(i,DEFBEGIN(I),DEFEND(I)){
		FOR_FWD(j,DEFBEGIN(J),DEFEND(J)){
			psi(i,j) = SLASH(SLASH(psi(i,j), GUARDED(((delta(i,j) && In(PARAM(I),(i - 1))) && In(PARAM(J),(j - 1))),(psi((i - 1),(j - 1)) + 1))), GUARDED((((!delta(i,j)) && In(PARAM(J),(j - 1))) && In(PARAM(I),(i - 1))),oplus(psi(i,(j - 1)),psi((i - 1),j))));
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
		cilk_sync;

		funcA_rec(PARAM(I0),PARAM(J___J1_J1minus1));
		cilk_sync;

		funcA_rec(PARAM(I___I1_I1minus1),PARAM(J0));
		cilk_sync;

		funcA_rec(PARAM(I___I1_I1minus1),PARAM(J___J1_J1minus1));
		cilk_sync;

	}

}
