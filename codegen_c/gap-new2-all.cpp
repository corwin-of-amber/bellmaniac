
void funcC_loop(DEFINTERVALFUNC(J0),DEFINTERVALFUNC(J1),DEFINTERVALFUNC(K)){
	__declspec(align(ALIGNMENT)) TYPE V[B * B];
	copy_dist_part(V,PARAM(J0),PARAM(K));

	FOR_C_loop_2(i,DEFBEGIN(J1),DEFEND(J1)){
		FOR_C_loop_3(j,DEFBEGIN(K),DEFEND(K)){
			TYPE t22 = DCLdist(i,j);
			if(INSET((i-1),J0) && INSET((j-1),K)){
				t22 = min(t22,DCLdist((i-1),(j-1))+S(i,j));
			}

			FOR_C_loop_1(p,DEFBEGIN(J0),DEFEND(J0)){
				t22 = min(t22,DdistCO(p,j,J0,K)+w_prime(p,i)/* INSET(p,J0) */);
			}

			DCLdist(i,j) = t22/* INSET((i-1),J0) && INSET((j-1),K) *//* INSET(i,J1) */;
		}
	}

}
void funcC_1(DEFINTERVALFUNC(J0),DEFINTERVALFUNC(K1),DEFINTERVALFUNC(K0),DEFINTERVALFUNC(L2)){
	FOR_C_rec_1(i,max(DEFBEGIN(L2),DEFBEGIN(J0)+1),min(DEFEND(L2),DEFEND(J0)+1)){
		FOR_C_rec_2(j,max(DEFBEGIN(K1),DEFBEGIN(K0)+1),min(DEFEND(K1),DEFEND(K0)+1)){
			Ddist(i,j) = min(Ddist(i,j),Ddist((i-1),(j-1))+S(i,j)/* INSET((i-1),J0) && INSET((j-1),K0) */)/* INSET(i,L2) && INSET(j,K1) */;
		}
	}
}

void funcC_2(DEFINTERVALFUNC(K1),DEFINTERVALFUNC(K0),DEFINTERVALFUNC(J0),DEFINTERVALFUNC(L3)){
	FOR_C_rec_3(i,max(DEFBEGIN(L3),DEFBEGIN(J0)+1),min(DEFEND(L3),DEFEND(J0)+1)){
		FOR_C_rec_4(j,max(DEFBEGIN(K1),DEFBEGIN(K0)+1),min(DEFEND(K1),DEFEND(K0)+1)){
			Ddist(i,j) = min(Ddist(i,j),Ddist((i-1),(j-1))+S(i,j)/* INSET((i-1),J0) && INSET((j-1),K0) */)/* INSET(i,L3) && INSET(j,K1) */;
		}
	}
}

void funcC_rec(DEFINTERVALFUNC(J0),DEFINTERVALFUNC(J1),DEFINTERVALFUNC(K)){
	if (BASE_CONSTRAINT_C(J0,J1,K)){
		funcC_loop(PARAM(J0),PARAM(J1),PARAM(K));
		return;
	}
	DEFINTERVALSTMT(K0);
	DEFBEGIN(K0) = DEFBEGIN(K);
	DEFEND(K0) = (DEFEND(K) + DEFBEGIN(K))/2;
	DEFINTERVALSTMT(K1);
	DEFBEGIN(K1) = DEFEND(K0);
	DEFEND(K1) = DEFEND(K);
	DEFINTERVALSTMT(L0);
	DEFBEGIN(L0) = DEFBEGIN(J0);
	DEFEND(L0) = (DEFEND(J0) + DEFBEGIN(J0))/2;
	DEFINTERVALSTMT(L1);
	DEFBEGIN(L1) = DEFEND(L0);
	DEFEND(L1) = DEFEND(J0);
	DEFINTERVALSTMT(L2);
	DEFBEGIN(L2) = DEFBEGIN(J1);
	DEFEND(L2) = (DEFEND(J1) + DEFBEGIN(J1))/2;
	DEFINTERVALSTMT(L3);
	DEFBEGIN(L3) = DEFEND(L2);
	DEFEND(L3) = DEFEND(J1);



	cilk_spawn /* PARLEVEL 0 */ funcC_rec(PARAM(L0),PARAM(L2),PARAM(K0));
	cilk_spawn /* PARLEVEL 0 */ funcC_1(PARAM(J0),PARAM(K1),PARAM(K0),PARAM(L2));
	cilk_spawn /* PARLEVEL 0 */ funcC_rec(PARAM(L0),PARAM(L3),PARAM(K0));
	/* PARLEVEL 0 */ funcC_2(PARAM(K1),PARAM(K0),PARAM(J0),PARAM(L3));
	cilk_sync;
	cilk_spawn /* PARLEVEL 1 */ funcC_rec(PARAM(L1),PARAM(L2),PARAM(K0));
	cilk_spawn /* PARLEVEL 1 */ funcC_rec(PARAM(L0),PARAM(L2),PARAM(K1));
	cilk_spawn /* PARLEVEL 1 */ funcC_rec(PARAM(L1),PARAM(L3),PARAM(K0));
	/* PARLEVEL 1 */ funcC_rec(PARAM(L0),PARAM(L3),PARAM(K1));
	cilk_sync;
	cilk_spawn /* PARLEVEL 2 */ funcC_rec(PARAM(L1),PARAM(L2),PARAM(K1));
	/* PARLEVEL 2 */ funcC_rec(PARAM(L1),PARAM(L3),PARAM(K1));
	cilk_sync;
}

void funcB_loop(DEFINTERVALFUNC(J),DEFINTERVALFUNC(K0),DEFINTERVALFUNC(K1)){

	FOR_B_loop_2(i,DEFBEGIN(J),DEFEND(J)){
		FOR_B_loop_3(j,DEFBEGIN(K1),DEFEND(K1)){
			TYPE t370 = DBLdist(i,j);
			if(INSET((j-1),K0) && INSET((i-1),J)){
				t370 = min(t370,DBLdist((i-1),(j-1))+S(i,j));
			}

			FOR_B_loop_1(q,DEFBEGIN(K0),DEFEND(K0)){
				t370 = min(t370,DBLdist(i,q)+w(q,j)/* INSET(q,K0) */);
			}

			DBLdist(i,j) = t370/* INSET((j-1),K0) && INSET((i-1),J) *//* INSET(j,K1) */;
		}
	}

}
void funcB_1(DEFINTERVALFUNC(K0),DEFINTERVALFUNC(J0),DEFINTERVALFUNC(J1),DEFINTERVALFUNC(M2)){
	FOR_B_rec_1(i,max(DEFBEGIN(J1),DEFBEGIN(J0)+1),min(DEFEND(J1),DEFEND(J0)+1)){
		FOR_B_rec_2(j,max(DEFBEGIN(M2),DEFBEGIN(K0)+1),min(DEFEND(M2),DEFEND(K0)+1)){
			Ddist(i,j) = min(Ddist(i,j),Ddist((i-1),(j-1))+S(i,j)/* INSET((i-1),J0) && INSET((j-1),K0) */)/* INSET(i,J1) && INSET(j,M2) */;
		}
	}
}

void funcB_2(DEFINTERVALFUNC(K0),DEFINTERVALFUNC(J0),DEFINTERVALFUNC(J1),DEFINTERVALFUNC(M3)){
	FOR_B_rec_3(i,max(DEFBEGIN(J1),DEFBEGIN(J0)+1),min(DEFEND(J1),DEFEND(J0)+1)){
		FOR_B_rec_4(j,max(DEFBEGIN(M3),DEFBEGIN(K0)+1),min(DEFEND(M3),DEFEND(K0)+1)){
			Ddist(i,j) = min(Ddist(i,j),Ddist((i-1),(j-1))+S(i,j)/* INSET((i-1),J0) && INSET((j-1),K0) */)/* INSET(i,J1) && INSET(j,M3) */;
		}
	}
}

void funcB_rec(DEFINTERVALFUNC(J),DEFINTERVALFUNC(K0),DEFINTERVALFUNC(K1)){
	if (BASE_CONSTRAINT_B(J,K0,K1)){
		funcB_loop(PARAM(J),PARAM(K0),PARAM(K1));
		return;
	}
	DEFINTERVALSTMT(M0);
	DEFBEGIN(M0) = DEFBEGIN(K0);
	DEFEND(M0) = (DEFEND(K0) + DEFBEGIN(K0))/2;
	DEFINTERVALSTMT(M1);
	DEFBEGIN(M1) = DEFEND(M0);
	DEFEND(M1) = DEFEND(K0);
	DEFINTERVALSTMT(M2);
	DEFBEGIN(M2) = DEFBEGIN(K1);
	DEFEND(M2) = (DEFEND(K1) + DEFBEGIN(K1))/2;
	DEFINTERVALSTMT(M3);
	DEFBEGIN(M3) = DEFEND(M2);
	DEFEND(M3) = DEFEND(K1);
	DEFINTERVALSTMT(J0);
	DEFBEGIN(J0) = DEFBEGIN(J);
	DEFEND(J0) = (DEFEND(J) + DEFBEGIN(J))/2;
	DEFINTERVALSTMT(J1);
	DEFBEGIN(J1) = DEFEND(J0);
	DEFEND(J1) = DEFEND(J);



	cilk_spawn /* PARLEVEL 0 */ funcB_rec(PARAM(J0),PARAM(M0),PARAM(M2));
	cilk_spawn /* PARLEVEL 0 */ funcB_rec(PARAM(J0),PARAM(M0),PARAM(M3));
	cilk_spawn /* PARLEVEL 0 */ funcB_1(PARAM(K0),PARAM(J0),PARAM(J1),PARAM(M2));
	/* PARLEVEL 0 */ funcB_2(PARAM(K0),PARAM(J0),PARAM(J1),PARAM(M3));
	cilk_sync;
	cilk_spawn /* PARLEVEL 1 */ funcB_rec(PARAM(J0),PARAM(M1),PARAM(M2));
	cilk_spawn /* PARLEVEL 1 */ funcB_rec(PARAM(J0),PARAM(M1),PARAM(M3));
	cilk_spawn /* PARLEVEL 1 */ funcB_rec(PARAM(J1),PARAM(M0),PARAM(M2));
	/* PARLEVEL 1 */ funcB_rec(PARAM(J1),PARAM(M0),PARAM(M3));
	cilk_sync;
	cilk_spawn /* PARLEVEL 2 */ funcB_rec(PARAM(J1),PARAM(M1),PARAM(M2));
	/* PARLEVEL 2 */ funcB_rec(PARAM(J1),PARAM(M1),PARAM(M3));
	cilk_sync;
}

void funcA_loop(DEFINTERVALFUNC(J),DEFINTERVALFUNC(K)){

	FOR_A_loop_3(i,DEFBEGIN(J),DEFEND(J)){
		FOR_A_loop_4(j,DEFBEGIN(K),DEFEND(K)){
			TYPE t719 = DALdist(i,j);
			if(INSET((i-1),J) && INSET((j-1),K)){
				t719 = min(t719,DALdist((i-1),(j-1))+S(i,j));
			}

			FOR_A_loop_1(q,DEFBEGIN(K),j){
				t719 = min(t719,DALdist(i,q)+w(q,j)/* q<j */);
			}

			FOR_A_loop_2(p,DEFBEGIN(J),i){
				t719 = min(t719,DALdist(p,j)+w_prime(p,i)/* p<i */);
			}

			DALdist(i,j) = t719/* INSET((i-1),J) && INSET((j-1),K) */;
		}
	}

}
void funcA_1(DEFINTERVALFUNC(K1),DEFINTERVALFUNC(K0),DEFINTERVALFUNC(J0),DEFINTERVALFUNC(J1)){
	FOR_A_rec_1(i,max(DEFBEGIN(J1),DEFBEGIN(J0)+1),min(DEFEND(J1),DEFEND(J0)+1)){
		FOR_A_rec_2(j,max(DEFBEGIN(K1),DEFBEGIN(K0)+1),min(DEFEND(K1),DEFEND(K0)+1)){
			Ddist(i,j) = min(Ddist(i,j),Ddist((i-1),(j-1))+S(i,j)/* INSET((i-1),J0) && INSET((j-1),K0) */)/* INSET(i,J1) && INSET(j,K1) */;
		}
	}
}

void funcA_rec(DEFINTERVALFUNC(J),DEFINTERVALFUNC(K)){
	if (BASE_CONSTRAINT_A(J,K)){
		funcA_loop(PARAM(J),PARAM(K));
		return;
	}
	DEFINTERVALSTMT(K0);
	DEFBEGIN(K0) = DEFBEGIN(K);
	DEFEND(K0) = (DEFEND(K) + DEFBEGIN(K))/2;
	DEFINTERVALSTMT(K1);
	DEFBEGIN(K1) = DEFEND(K0);
	DEFEND(K1) = DEFEND(K);
	DEFINTERVALSTMT(J0);
	DEFBEGIN(J0) = DEFBEGIN(J);
	DEFEND(J0) = (DEFEND(J) + DEFBEGIN(J))/2;
	DEFINTERVALSTMT(J1);
	DEFBEGIN(J1) = DEFEND(J0);
	DEFEND(J1) = DEFEND(J);



	/* PARLEVEL 0 */ funcA_rec(PARAM(J0),PARAM(K0));
	cilk_spawn /* PARLEVEL 1 */ funcB_rec(PARAM(J0),PARAM(K0),PARAM(K1));
	cilk_spawn /* PARLEVEL 1 */ funcC_rec(PARAM(J0),PARAM(J1),PARAM(K0));
	/* PARLEVEL 1 */ funcA_1(PARAM(K1),PARAM(K0),PARAM(J0),PARAM(J1));
	cilk_sync;
	cilk_spawn /* PARLEVEL 2 */ funcA_rec(PARAM(J0),PARAM(K1));
	/* PARLEVEL 2 */ funcA_rec(PARAM(J1),PARAM(K0));
	cilk_sync;
	/* PARLEVEL 3 */ funcC_rec(PARAM(J0),PARAM(J1),PARAM(K1));
	/* PARLEVEL 4 */ funcB_rec(PARAM(J1),PARAM(K0),PARAM(K1));
	/* PARLEVEL 5 */ funcA_rec(PARAM(J1),PARAM(K1));
}
