
void funcC_loop(DEFINTERVALFUNC(K0),DEFINTERVALFUNC(K1),DEFINTERVALFUNC(K2)){
	__declspec(align(ALIGNMENT)) TYPE V[B * B];
	copy_dist_part(V,PARAM(K1),PARAM(K2));

	FOR_C_loop_2(i,DEFBEGIN(K0),DEFEND(K0)){
		FOR_C_loop_3(j,DEFBEGIN(K2),DEFEND(K2)){

			TYPE t14= DCLdist(i,j);
			FOR_C_loop_1(k,DEFBEGIN(K1),DEFEND(K1)){
				t14 = min(t14,DCLdist(i,k)+DdistCO(k,j,K1,K2)+w(i,k,j)/* INSET(k,K1) */);
			}

			DCLdist(i,j) = t14/* INSET(i,K0) && INSET(j,K2) */;
		}
	}

}

void funcC_rec(DEFINTERVALFUNC(K0),DEFINTERVALFUNC(K1),DEFINTERVALFUNC(K2)){
	if (BASE_CONSTRAINT_C(K0,K1,K2)){
		funcC_loop(PARAM(K0),PARAM(K1),PARAM(K2));
		return;
	}
	DEFINTERVALSTMT(L4);
	DEFBEGIN(L4) = DEFBEGIN(K2);
	DEFEND(L4) = (DEFEND(K2) + DEFBEGIN(K2))/2;
	DEFINTERVALSTMT(L5);
	DEFBEGIN(L5) = DEFEND(L4);
	DEFEND(L5) = DEFEND(K2);
	DEFINTERVALSTMT(L2);
	DEFBEGIN(L2) = DEFBEGIN(K1);
	DEFEND(L2) = (DEFEND(K1) + DEFBEGIN(K1))/2;
	DEFINTERVALSTMT(L3);
	DEFBEGIN(L3) = DEFEND(L2);
	DEFEND(L3) = DEFEND(K1);
	DEFINTERVALSTMT(L0);
	DEFBEGIN(L0) = DEFBEGIN(K0);
	DEFEND(L0) = (DEFEND(K0) + DEFBEGIN(K0))/2;
	DEFINTERVALSTMT(L1);
	DEFBEGIN(L1) = DEFEND(L0);
	DEFEND(L1) = DEFEND(K0);



	cilk_spawn /* PARLEVEL 0 */ funcC_rec(PARAM(L0),PARAM(L2),PARAM(L4));
	cilk_spawn /* PARLEVEL 0 */ funcC_rec(PARAM(L0),PARAM(L2),PARAM(L5));
	cilk_spawn /* PARLEVEL 0 */ funcC_rec(PARAM(L1),PARAM(L2),PARAM(L4));
	/* PARLEVEL 0 */ funcC_rec(PARAM(L1),PARAM(L2),PARAM(L5));
	cilk_sync;
	cilk_spawn /* PARLEVEL 1 */ funcC_rec(PARAM(L0),PARAM(L3),PARAM(L4));
	cilk_spawn /* PARLEVEL 1 */ funcC_rec(PARAM(L0),PARAM(L3),PARAM(L5));
	cilk_spawn /* PARLEVEL 1 */ funcC_rec(PARAM(L1),PARAM(L3),PARAM(L4));
	/* PARLEVEL 1 */ funcC_rec(PARAM(L1),PARAM(L3),PARAM(L5));
	cilk_sync;
}

void funcB_loop(DEFINTERVALFUNC(J0),DEFINTERVALFUNC(J1)){

	FOR_B_loop_3(i,DEFBEGIN(J0),DEFEND(J0)){
		FOR_B_loop_4(j,DEFBEGIN(J1),DEFEND(J1)){

			TYPE t221= DBLdist(i,j);
			FOR_B_loop_1(k,i+1,DEFEND(J0)){
				t221 = min(t221,DBLdist(i,k)+DBLdist(k,j)+w(i,k,j)/* i<k && k<j */);

			}
			FOR_B_loop_2(k,DEFBEGIN(J1),j){
				t221 = min(t221,DBLdist(i,k)+DBLdist(k,j)+w(i,k,j)/* i<k && k<j */);

			}

			DBLdist(i,j) = t221/* INSET(i,J0) && INSET(j,J1) */;
		}
	}

}

void funcB_rec(DEFINTERVALFUNC(J0),DEFINTERVALFUNC(J1)){
	if (BASE_CONSTRAINT_B(J0,J1)){
		funcB_loop(PARAM(J0),PARAM(J1));
		return;
	}
	DEFINTERVALSTMT(K0);
	DEFBEGIN(K0) = DEFBEGIN(J0);
	DEFEND(K0) = (DEFEND(J0) + DEFBEGIN(J0))/2;
	DEFINTERVALSTMT(K1);
	DEFBEGIN(K1) = DEFEND(K0);
	DEFEND(K1) = DEFEND(J0);
	DEFINTERVALSTMT(K2);
	DEFBEGIN(K2) = DEFBEGIN(J1);
	DEFEND(K2) = (DEFEND(J1) + DEFBEGIN(J1))/2;
	DEFINTERVALSTMT(K3);
	DEFBEGIN(K3) = DEFEND(K2);
	DEFEND(K3) = DEFEND(J1);



	/* PARLEVEL 0 */ funcB_rec(PARAM(K1),PARAM(K2));
	cilk_spawn /* PARLEVEL 1 */ funcC_rec(PARAM(K0),PARAM(K1),PARAM(K2));
	/* PARLEVEL 1 */ funcC_rec(PARAM(K1),PARAM(K2),PARAM(K3));
	cilk_sync;
	cilk_spawn /* PARLEVEL 2 */ funcB_rec(PARAM(K0),PARAM(K2));
	/* PARLEVEL 2 */ funcB_rec(PARAM(K1),PARAM(K3));
	cilk_sync;
	/* PARLEVEL 3 */ funcC_rec(PARAM(K0),PARAM(K1),PARAM(K3));
	/* PARLEVEL 4 */ funcC_rec(PARAM(K0),PARAM(K2),PARAM(K3));
	/* PARLEVEL 5 */ funcB_rec(PARAM(K0),PARAM(K3));
}

void funcA_loop(DEFINTERVALFUNC(J)){

	FOR_A_loop_2(i,DEFBEGIN(J),DEFEND(J)){
		FOR_A_loop_3(j,i+1,DEFEND(J)){

			TYPE t520= DALdist(i,j);
			FOR_A_loop_1(k,i+1,j){
				t520 = min(t520,DALdist(i,k)+DALdist(k,j)+w(i,k,j)/* i<k && k<j */);
			}

			DALdist(i,j) = t520/* i<j */;
		}
	}
	
}

void funcA_rec(DEFINTERVALFUNC(J)){
	if (BASE_CONSTRAINT_A(J)){
		funcA_loop(PARAM(J));
		return;
	}
	DEFINTERVALSTMT(J0);
	DEFBEGIN(J0) = DEFBEGIN(J);
	DEFEND(J0) = (DEFEND(J) + DEFBEGIN(J))/2;
	DEFINTERVALSTMT(J1);
	DEFBEGIN(J1) = DEFEND(J0);
	DEFEND(J1) = DEFEND(J);



	cilk_spawn /* PARLEVEL 0 */ funcA_rec(PARAM(J0));
	/* PARLEVEL 0 */ funcA_rec(PARAM(J1));
	cilk_sync;
	/* PARLEVEL 1 */ funcB_rec(PARAM(J0),PARAM(J1));
}
