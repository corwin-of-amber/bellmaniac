
#include "input.h"
#include "preface.h"


void funcA_loop(DEFINTERVALFUNC(J)){
	FOR_BWD(i,DEFBEGIN(J),DEFEND(J)){
		FOR_BWD(j,max((i + 1),DEFBEGIN(J)),DEFEND(J)){
			TYPE tmp1;
			tmp1 = INITMAX;
			if((i < j)){
				if(In(PARAM(J),(j + 1))){
					FOR_BWD(k,max(((j + 1) + 1),DEFBEGIN(J)),DEFEND(J)){
						tmp1 = max(tmp1,(psi((j + 1),k) + delta(i,j,k)));
					}
				}

			}

			TYPE tmp2;
			tmp2 = psi(i,j);
			tmp2 = max(tmp2,tmp1);
			psi(i,j) = tmp2;
		}
	}    /*bazinga 0*/
}

void funcB_loop(DEFINTERVALFUNC(J0),DEFINTERVALFUNC(J1)){
	DEFINTERVALSTMT_UNION(J, J0, J1);
	DEFINTERVALSTMT_LOWER(K0, J0);
	DEFINTERVALSTMT_UPPER(K1, J0);
	DEFINTERVALSTMT_LOWER(K2, J1);
	DEFINTERVALSTMT_UPPER(K3, J1);
	FOR_BWD(i,DEFBEGIN(J0),DEFEND(J0)){
		FOR_BWD(j,DEFBEGIN(J1),DEFEND(J1)){
			TYPE tmp3;
			tmp3 = INITMAX;
			if((In(PARAM(J0),i) && In(PARAM(J1),j))){
				if(In(PARAM(J1),(j + 1))){
					FOR_BWD(k,max(max(DEFBEGIN(J1),((j + 1) + 1)),DEFBEGIN(J)),DEFEND(J1)){
						tmp3 = max(tmp3,(psi((j + 1),k) + delta(i,j,k)));
					}
				}

			}

			psi(i,j) = max(GUARDED((i < j),psi(i,j)),tmp3);
		}
	}    /*bazinga 0*/
}

void funcC_loop(DEFINTERVALFUNC(J0),DEFINTERVALFUNC(J1)){
	DEFINTERVALSTMT_UNION(J, J0, J1);
	DEFINTERVALSTMT_LOWER(K0, J0);
	DEFINTERVALSTMT_UPPER(K1, J0);
	DEFINTERVALSTMT_LOWER(K2, J1);
	DEFINTERVALSTMT_UPPER(K3, J1);
	FOR_BWD(i,DEFBEGIN(J0),DEFEND(J0)){
		FOR_BWD(j,max(DEFBEGIN(J0),(i + 1)),DEFEND(J0)){
			TYPE tmp4;
			tmp4 = INITMAX;
			if(((In(PARAM(J0),i) && In(PARAM(J0),j)) && (i < j))){
				if(In(PARAM(J0),(j + 1))){
					FOR_BWD(k,max(max(DEFBEGIN(J1),((j + 1) + 1)),DEFBEGIN(J)),DEFEND(J1)){
						tmp4 = max(tmp4,(psi((j + 1),k) + delta(i,j,k)));
					}
				}

			}

			TYPE tmp5;
			tmp5 = psi(i,j);
			tmp5 = max(tmp5,tmp4);
			psi(i,j) = tmp5;
		}
	}    /*bazinga 0*/
}

#define DdistSimpleV(i,j,I,J) V[((j)-DEFBEGIN(J)) + ((i)-DEFBEGIN(I))*B]

inline void copy_dist_part_simple(TYPE* V,DEFINTERVALFUNC(II),DEFINTERVALFUNC(JJ)){
	for(int i=DEFBEGIN(II);i<DEFEND(II);i++){
		for(int j=DEFBEGIN(JJ);j<DEFEND(JJ);j++){
			//cout<<i<<" "<<j<<" "<<(j)-DEFBEGIN(JJ)<<" "<<((i)-DEFBEGIN(II))<<endl;
			DdistSimpleV(i,j,II,JJ) = Ddist(i,j);

		}
	}
}

void funcD_loop(DEFINTERVALFUNC(K0),DEFINTERVALFUNC(K1),DEFINTERVALFUNC(K2)){
	__declspec(align(ALIGNMENT)) TYPE V[B * B];
	copy_dist_part_plain(V,PARAM(K1),PARAM(K2));
	
	FOR_BWD(i,DEFBEGIN(K0),DEFEND(K0)){
		FOR_BWD(j,DEFBEGIN(K1),DEFEND(K1)){
			TYPE tmp6;
			tmp6 = INITMAX;
			if((In(PARAM(K0),i) && In(PARAM(K1),j))){
				if(In(PARAM(K1),(j + 1))){
					FOR_BWD(k,DEFBEGIN(K2),DEFEND(K2)){
						tmp6 = max(tmp6,(psiCopyOptPlain((j + 1),k,K1,K2) + delta(i,j,k)));
					}
				}

			}

			TYPE tmp7;
			tmp7 = psi(i,j);
			tmp7 = max(tmp7,tmp6);
			psi(i,j) = tmp7;
		}
	}    /*bazinga 0*/
}

void func(DEFINTERVALFUNC(L0),DEFINTERVALFUNC(L2),DEFINTERVALFUNC(L3),DEFINTERVALFUNC(K2)){
	FOR_BWD(i,DEFBEGIN(L0),DEFEND(L0)){
		FOR_BWD(j,DEFBEGIN(L2),DEFEND(L2)){
			TYPE tmp8;
			tmp8 = INITMAX;
			if((In(PARAM(L0),i) && In(PARAM(L2),j))){
				if(In(PARAM(L3),(j + 1))){
					FOR_BWD(k,DEFBEGIN(K2),DEFEND(K2)){
						tmp8 = max(tmp8,(psi((j + 1),k) + delta(i,j,k)));
					}
				}

			}

			TYPE tmp10;
			tmp10 = psi(i,j);
			tmp10 = max(tmp10,tmp8);
			psi(i,j) = tmp10;
		}
	}
}
void func0(DEFINTERVALFUNC(L1),DEFINTERVALFUNC(L2),DEFINTERVALFUNC(L3),DEFINTERVALFUNC(K2)){
	FOR_BWD(i,DEFBEGIN(L1),DEFEND(L1)){
		FOR_BWD(j,DEFBEGIN(L2),DEFEND(L2)){
			TYPE tmp9;
			tmp9 = INITMAX;
			if((In(PARAM(L1),i) && In(PARAM(L2),j))){
				if(In(PARAM(L3),(j + 1))){
					FOR_BWD(k,DEFBEGIN(K2),DEFEND(K2)){
						tmp9 = max(tmp9,(psi((j + 1),k) + delta(i,j,k)));
					}
				}

			}

			TYPE tmp11;
			tmp11 = psi(i,j);
			tmp11 = max(tmp11,tmp9);
			psi(i,j) = tmp11;
		}
	}
}
void funcD_rec(DEFINTERVALFUNC(K0),DEFINTERVALFUNC(K1),DEFINTERVALFUNC(K2)){
	if(BASE_CONSTRAINT(PARAM(K0),PARAM(K1),PARAM(K2))){
		funcD_loop(PARAM(K0),PARAM(K1),PARAM(K2));
	} else {
		DEFINTERVALSTMT_LOWER(L0, K0);
		DEFINTERVALSTMT_UPPER(L1, K0);
		DEFINTERVALSTMT_LOWER(L2, K1);
		DEFINTERVALSTMT_UPPER(L3, K1);
		DEFINTERVALSTMT_LOWER(L4, K2);
		DEFINTERVALSTMT_UPPER(L5, K2);
		cilk_spawn func(PARAM(L0),PARAM(L2),PARAM(L3),PARAM(K2));;
		cilk_spawn funcD_rec(PARAM(L0),PARAM(L3),PARAM(L4));;
		cilk_spawn func0(PARAM(L1),PARAM(L2),PARAM(L3),PARAM(K2));;
		funcD_rec(PARAM(L1),PARAM(L3),PARAM(L4));
		cilk_sync;

		cilk_spawn funcD_rec(PARAM(L0),PARAM(L2),PARAM(L4));;
		cilk_spawn funcD_rec(PARAM(L0),PARAM(L3),PARAM(L5));;
		cilk_spawn funcD_rec(PARAM(L1),PARAM(L2),PARAM(L4));;
		funcD_rec(PARAM(L1),PARAM(L3),PARAM(L5));
		cilk_sync;

		cilk_spawn funcD_rec(PARAM(L0),PARAM(L2),PARAM(L5));;
		funcD_rec(PARAM(L1),PARAM(L2),PARAM(L5));
		cilk_sync;

	}

}

void func1(DEFINTERVALFUNC(K0),DEFINTERVALFUNC(K1),DEFINTERVALFUNC(J1),DEFINTERVALFUNC(J)){
	FOR_BWD(i,DEFBEGIN(K0),DEFEND(K0)){
		FOR_BWD(j,max(DEFBEGIN(K0),(i + 1)),DEFEND(K0)){
			TYPE tmp12;
			tmp12 = INITMAX;
			if(((In(PARAM(K0),i) && In(PARAM(K0),j)) && (i < j))){
				if(In(PARAM(K1),(j + 1))){
					FOR_BWD(k,max(max(DEFBEGIN(J1),((j + 1) + 1)),DEFBEGIN(J)),DEFEND(J1)){
						tmp12 = max(tmp12,(psi((j + 1),k) + delta(i,j,k)));
					}
				}

			}

			TYPE tmp13;
			tmp13 = psi(i,j);
			tmp13 = max(tmp13,tmp12);
			psi(i,j) = tmp13;
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
		cilk_spawn func1(PARAM(K0),PARAM(K1),PARAM(J1),PARAM(J));;
		cilk_spawn funcD_rec(PARAM(K0),PARAM(K1),PARAM(K2));;
		funcC_rec(PARAM(K1),PARAM(K2));
		cilk_sync;

		cilk_spawn funcC_rec(PARAM(K0),PARAM(K2));;
		cilk_spawn funcD_rec(PARAM(K0),PARAM(K1),PARAM(K3));;
		funcC_rec(PARAM(K1),PARAM(K3));
		cilk_sync;

		funcC_rec(PARAM(K0),PARAM(K3));
	}

}

void func2(DEFINTERVALFUNC(K0),DEFINTERVALFUNC(K2),DEFINTERVALFUNC(K3),DEFINTERVALFUNC(J)){
	FOR_BWD(i,DEFBEGIN(K0),DEFEND(K0)){
		FOR_BWD(j,max(DEFBEGIN(K2),(i + 1)),DEFEND(K2)){
			TYPE tmp14;
			tmp14 = INITMAX;
			if(((In(PARAM(K0),i) && In(PARAM(K2),j)) && (i < j))){
				if(In(PARAM(K3),(j + 1))){
					FOR_BWD(k,max(max(DEFBEGIN(K3),((j + 1) + 1)),DEFBEGIN(J)),DEFEND(K3)){
						tmp14 = max(tmp14,(psi((j + 1),k) + delta(i,j,k)));
					}
				}

			}

			TYPE tmp16;
			tmp16 = psi(i,j);
			tmp16 = max(tmp16,tmp14);
			psi(i,j) = tmp16;
		}
	}
}
void func3(DEFINTERVALFUNC(K1),DEFINTERVALFUNC(K2),DEFINTERVALFUNC(K3),DEFINTERVALFUNC(J)){
	FOR_BWD(i,DEFBEGIN(K1),DEFEND(K1)){
		FOR_BWD(j,max(DEFBEGIN(K2),(i + 1)),DEFEND(K2)){
			TYPE tmp15;
			tmp15 = INITMAX;
			if(((In(PARAM(K1),i) && In(PARAM(K2),j)) && (i < j))){
				if(In(PARAM(K3),(j + 1))){
					FOR_BWD(k,max(max(DEFBEGIN(K3),((j + 1) + 1)),DEFBEGIN(J)),DEFEND(K3)){
						tmp15 = max(tmp15,(psi((j + 1),k) + delta(i,j,k)));
					}
				}

			}

			TYPE tmp17;
			tmp17 = psi(i,j);
			tmp17 = max(tmp17,tmp15);
			psi(i,j) = tmp17;
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
		cilk_spawn funcB_rec(PARAM(K0),PARAM(K3));;
		cilk_spawn funcB_rec(PARAM(K1),PARAM(K2));;
		funcB_rec(PARAM(K1),PARAM(K3));
		cilk_sync;

		cilk_spawn funcD_rec(PARAM(K0),PARAM(K2),PARAM(K3));;
		funcD_rec(PARAM(K1),PARAM(K2),PARAM(K3));
		cilk_sync;

		cilk_spawn func2(PARAM(K0),PARAM(K2),PARAM(K3),PARAM(J));;
		func3(PARAM(K1),PARAM(K2),PARAM(K3),PARAM(J));
		cilk_sync;

	}

}

void func4(DEFINTERVALFUNC(J0),DEFINTERVALFUNC(J1)){
	FOR_BWD(i,DEFBEGIN(J0),DEFEND(J0)){
		FOR_BWD(j,max(DEFBEGIN(J0),(i + 1)),DEFEND(J0)){
			TYPE tmp18;
			tmp18 = INITMAX;
			if(((In(PARAM(J0),i) && In(PARAM(J0),j)) && (i < j))){
				if(In(PARAM(J1),(j + 1))){
					FOR_BWD(k,max(DEFBEGIN(J1),((j + 1) + 1)),DEFEND(J1)){
						tmp18 = max(tmp18,(psi((j + 1),k) + delta(i,j,k)));
					}
				}

			}

			TYPE tmp19;
			tmp19 = psi(i,j);
			tmp19 = max(tmp19,tmp18);
			psi(i,j) = tmp19;
		}
	}
}
void funcA_rec(DEFINTERVALFUNC(J)){
	if(BASE_CONSTRAINT(PARAM(J))){
		funcA_loop(PARAM(J));
	} else {
		DEFINTERVALSTMT_LOWER(J0, J);
		DEFINTERVALSTMT_UPPER(J1, J);
		funcA_rec(PARAM(J1));
		funcB_rec(PARAM(J0),PARAM(J1));
		funcC_rec(PARAM(J0),PARAM(J1));
		func4(PARAM(J0),PARAM(J1));
		funcA_rec(PARAM(J0));
	}

}
