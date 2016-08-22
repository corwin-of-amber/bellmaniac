
#include "input.h"
#include "preface.h"


void funcA_loop(DEFINTERVALFUNC(J)){
	FOR_FWD(i,DEFBEGIN(J),DEFEND(J)){
		FOR_FWD(j,max((i + 1),DEFBEGIN(J)),DEFEND(J)){
			TYPE tmp1;
			tmp1 = INITMIN;
			if(((i < j) && succ(i,j))){
				FOR_FWD(k,DEFBEGIN(J),min(i,DEFEND(J))){
					tmp1 = min(tmp1,(psi(k,i) + d(k,i)));
				}
			}

			TYPE tmp2;
			tmp2 = psi(i,j);
			if(((i < (j - 1)) && In(PARAM(J),(j - 1)))){
				tmp2 = min(tmp2,(psi(i,(j - 1)) + d(i,(j - 1))));
			}

			if(succ(i,j)){
				tmp2 = min(tmp2,tmp1);
			}

			psi(i,j) = tmp2;
		}
	}    /*bazinga 0*/
}

void funcB_loop(DEFINTERVALFUNC(J0),DEFINTERVALFUNC(J1)){
	DEFINTERVALSTMT_UNION(J, J0, J1);
	FOR_FWD(i,DEFBEGIN(J0),DEFEND(J0)){
		FOR_FWD(j,max((DEFBEGIN(J1) + 1),max((i + 1),DEFBEGIN(J1))),min((DEFEND(J1) + 1),DEFEND(J1))){
			if((i < (j - 1))){
				TYPE tmp3;
				tmp3 = psi(i,j);
				tmp3 = min(tmp3,(psi(i,(j - 1)) + d(i,(j - 1))));
				psi(i,j) = tmp3;
			}

		}
	}    /*bazinga 0*/
}

void funcC_loop(DEFINTERVALFUNC(J0),DEFINTERVALFUNC(J1)){
	DEFINTERVALSTMT_UNION(J, J0, J1);
	DEFINTERVALSTMT_LOWER(K0, J0);
	DEFINTERVALSTMT_UPPER(K1, J0);
	DEFINTERVALSTMT_LOWER(K2, J1);
	DEFINTERVALSTMT_UPPER(K3, J1);
	__declspec(align(ALIGNMENT)) TYPE V[B * B];

	copy_dist_part(V,PARAM(J0),PARAM(J1));
	FOR_FWD(i,DEFBEGIN(J1),DEFEND(J1)){
		FOR_FWD(j,max((i + 1),DEFBEGIN(J1)),DEFEND(J1)){
			TYPE tmp4;
			tmp4 = INITMIN;
			if(((i < j) && succ(i,j))){
				FOR_FWD(k,DEFBEGIN(J0),DEFEND(J0)){
					tmp4 = min(tmp4,(psiCopyOpt(k,i,J0,J1) + d(k,i)));
				}
			}

			if(succ(i,j)){
				TYPE tmp5;
				tmp5 = psi(i,j);
				tmp5 = min(tmp5,tmp4);
				psi(i,j) = tmp5;
			}

		}
	}    /*bazinga 0*/
}

void func(DEFINTERVALFUNC(K2),DEFINTERVALFUNC(K3),DEFINTERVALFUNC(K0),DEFINTERVALFUNC(J0)){
	FOR_FWD(i,DEFBEGIN(K2),DEFEND(K2)){
		FOR_FWD(j,max((i + 1),DEFBEGIN(K3)),DEFEND(K3)){
			TYPE tmp6;
			tmp6 = INITMIN;
			if(((i < j) && succ(i,j))){
				FOR_FWD(k,DEFBEGIN(K0),min(min(DEFEND(K0),i),DEFEND(J0))){
					tmp6 = min(tmp6,(psi(k,i) + d(k,i)));
				}
			}

			if(succ(i,j)){
				TYPE tmp8;
				tmp8 = psi(i,j);
				tmp8 = min(tmp8,tmp6);
				psi(i,j) = tmp8;
			}

		}
	}
}
void func0(DEFINTERVALFUNC(K2),DEFINTERVALFUNC(K3),DEFINTERVALFUNC(K1),DEFINTERVALFUNC(J0)){
	FOR_FWD(i,DEFBEGIN(K2),DEFEND(K2)){
		FOR_FWD(j,max((i + 1),DEFBEGIN(K3)),DEFEND(K3)){
			TYPE tmp7;
			tmp7 = INITMIN;
			if(((i < j) && succ(i,j))){
				FOR_FWD(k,DEFBEGIN(K1),min(min(DEFEND(K1),i),DEFEND(J0))){
					tmp7 = min(tmp7,(psi(k,i) + d(k,i)));
				}
			}

			if(succ(i,j)){
				TYPE tmp9;
				tmp9 = psi(i,j);
				tmp9 = min(tmp9,tmp7);
				psi(i,j) = tmp9;
			}

		}
	}
}
void funcC_rec(DEFINTERVALFUNC(J0),DEFINTERVALFUNC(J1)){
	if(BASE_CONSTRAINT(PARAM(J0),PARAM(J1))){
		funcC_loop(PARAM(J0),PARAM(J1));
	} else {
		DEFINTERVALSTMT_UNION(J, J0, J1);
		DEFINTERVALSTMT_LOWER(K0, J0);
		DEFINTERVALSTMT_UPPER(K1, J0);
		DEFINTERVALSTMT_LOWER(K2, J1);
		DEFINTERVALSTMT_UPPER(K3, J1);
		cilk_spawn funcC_rec(PARAM(K0),PARAM(K2));;
		cilk_spawn func(PARAM(K2),PARAM(K3),PARAM(K0),PARAM(J0));;
		funcC_rec(PARAM(K0),PARAM(K3));
		cilk_sync;

		cilk_spawn funcC_rec(PARAM(K1),PARAM(K2));;
		cilk_spawn func0(PARAM(K2),PARAM(K3),PARAM(K1),PARAM(J0));;
		funcC_rec(PARAM(K1),PARAM(K3));
		cilk_sync;

	}

}

void func1(DEFINTERVALFUNC(K0),DEFINTERVALFUNC(K2),DEFINTERVALFUNC(K3)){
	FOR_FWD(i,DEFBEGIN(K0),DEFEND(K0)){
		FOR_FWD(j,max((DEFBEGIN(K2) + 1),max((i + 1),DEFBEGIN(K3))),min((DEFEND(K2) + 1),DEFEND(K3))){
			if((i < (j - 1))){
				TYPE tmp10;
				tmp10 = psi(i,j);
				tmp10 = min(tmp10,(psi(i,(j - 1)) + d(i,(j - 1))));
				psi(i,j) = tmp10;
			}

		}
	}
}
void func2(DEFINTERVALFUNC(K1),DEFINTERVALFUNC(K2),DEFINTERVALFUNC(K3)){
	FOR_FWD(i,DEFBEGIN(K1),DEFEND(K1)){
		FOR_FWD(j,max((DEFBEGIN(K2) + 1),max((i + 1),DEFBEGIN(K3))),min((DEFEND(K2) + 1),DEFEND(K3))){
			if((i < (j - 1))){
				TYPE tmp11;
				tmp11 = psi(i,j);
				tmp11 = min(tmp11,(psi(i,(j - 1)) + d(i,(j - 1))));
				psi(i,j) = tmp11;
			}

		}
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
		cilk_spawn funcB_rec(PARAM(K0),PARAM(K2));;
		funcB_rec(PARAM(K1),PARAM(K2));
		cilk_sync;

		cilk_spawn func1(PARAM(K0),PARAM(K2),PARAM(K3));;
		func2(PARAM(K1),PARAM(K2),PARAM(K3));
		cilk_sync;

		cilk_spawn funcB_rec(PARAM(K0),PARAM(K3));;
		funcB_rec(PARAM(K1),PARAM(K3));
		cilk_sync;

	}

}

void func3(DEFINTERVALFUNC(J0),DEFINTERVALFUNC(J1),DEFINTERVALFUNC(J)){
	FOR_FWD(i,DEFBEGIN(J0),DEFEND(J0)){
		FOR_FWD(j,max((i + 1),DEFBEGIN(J1)),DEFEND(J1)){
			TYPE tmp12;
			tmp12 = INITMIN;
			if(((i < j) && succ(i,j))){
				FOR_FWD(k,DEFBEGIN(J0),min(min(i,DEFEND(J0)),DEFEND(J))){
					tmp12 = min(tmp12,(psi(k,i) + d(k,i)));
				}
			}

			TYPE tmp13;
			tmp13 = psi(i,j);
			if((In(PARAM(J0),(j - 1)) && (i < (j - 1)))){
				tmp13 = min(tmp13,(psi(i,(j - 1)) + d(i,(j - 1))));
			}

			if(succ(i,j)){
				tmp13 = min(tmp13,tmp12);
			}

			psi(i,j) = tmp13;
		}
	}
}
void funcA_rec(DEFINTERVALFUNC(J)){
	if(BASE_CONSTRAINT(PARAM(J))){
		funcA_loop(PARAM(J));
	} else {
		DEFINTERVALSTMT_LOWER(J0, J);
		DEFINTERVALSTMT_UPPER(J1, J);
		funcA_rec(PARAM(J0));
		func3(PARAM(J0),PARAM(J1),PARAM(J));
		funcB_rec(PARAM(J0),PARAM(J1));
		funcC_rec(PARAM(J0),PARAM(J1));
		funcA_rec(PARAM(J1));
	}

}
