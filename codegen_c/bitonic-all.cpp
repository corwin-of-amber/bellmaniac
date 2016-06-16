//GUARDS:  [u'INSET(i,J1)', u'INSET(j,J1)', u'i<j', u'EQ(i+1,j)']
//GUARDS:  [u'INSET(k,J0)']

void funcC_loop(DEFINTERVALFUNC(J0),DEFINTERVALFUNC(J1)){
	__declspec(align(ALIGNMENT)) TYPE V[B * B];
	copy_dist_part(V,PARAM(J0),PARAM(J1));

	FOR_C_loop_2(i,DEFBEGIN(J1),DEFEND(J1)-1){
		{
			LET(j,i+1);

			TYPE t21= DCLdist(i,j);
			FOR_C_loop_1(k,DEFBEGIN(J0),DEFEND(J0)){
				t21 = min(t21,DdistCO(k,i,J0,J1)+d(k,i));
			}

			DCLdist(i,j) = t21;
		}
	}

}
//GUARDS:  [u'INSET(i,K2)', u'INSET(j,K3)', u'i<j', u'EQ(i+1,j)']
//GUARDS:  [u'INSET(k,K0)', u'k<i']
//GUARDS:  [u'INSET(i,K2)', u'INSET(j,K3)', u'i<j', u'EQ(i+1,j)']
//GUARDS:  [u'INSET(k,K1)', u'k<i']
void funcC_1(DEFINTERVALFUNC(K3),DEFINTERVALFUNC(K2),DEFINTERVALFUNC(K0)){
	{
		LET(i,DEFEND(K2)-1);
		{
			LET(j,DEFBEGIN(K3));

			TYPE t181= Ddist(i,j);
			FOR_C_rec_1(k,DEFBEGIN(K0),DEFEND(K0)){
				t181 = min(t181,Ddist(k,i)+d(k,i));
			}

			Ddist(i,j) = t181;
		}
	}
}

void funcC_2(DEFINTERVALFUNC(K3),DEFINTERVALFUNC(K2),DEFINTERVALFUNC(K1)){
	{
		LET(i,DEFEND(K2)-1);
		{
			LET(j,DEFBEGIN(K3));

			TYPE t116= Ddist(i,j);
			FOR_C_rec_2(k,DEFBEGIN(K1),DEFEND(K1)){
				t116 = min(t116,Ddist(k,i)+d(k,i));
			}

			Ddist(i,j) = t116;
		}
	}
}

void funcC_rec(DEFINTERVALFUNC(J0),DEFINTERVALFUNC(J1)){
	if (BASE_CONSTRAINT_C(J0,J1)){
		funcC_loop(PARAM(J0),PARAM(J1));
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



	cilk_spawn /* PARLEVEL 0 */ funcC_rec(PARAM(K0),PARAM(K2));
	cilk_spawn /* PARLEVEL 0 */ funcC_1(PARAM(K3),PARAM(K2),PARAM(K0));
	/* PARLEVEL 0 */ funcC_rec(PARAM(K0),PARAM(K3));
	cilk_sync;
	cilk_spawn /* PARLEVEL 1 */ funcC_rec(PARAM(K1),PARAM(K2));
	cilk_spawn /* PARLEVEL 1 */ funcC_2(PARAM(K3),PARAM(K2),PARAM(K1));
	/* PARLEVEL 1 */ funcC_rec(PARAM(K1),PARAM(K3));
	cilk_sync;
}
//GUARDS:  [u'INSET(i,J0)', u'INSET(j,J1)', u'i<j', u'INSET((j-1),J1)', u'i+1<j']
//(DEFBEGIN(J1)+1,DEFEND(J1)) -> (i+2,DEFEND(J1))

void funcB_loop(DEFINTERVALFUNC(J0),DEFINTERVALFUNC(J1)){

	FOR_B_loop_1(i,DEFBEGIN(J0),DEFEND(J0)){
		FOR_B_loop_2(j,max(DEFBEGIN(J1)+1,i+2),DEFEND(J1)){
			DBLdist(i,j) = min(DBLdist(i,j),DBLdist(i,(j-1))+d(i,(j-1)));
		}
	}

}
//GUARDS:  [u'INSET(i,K0)', u'INSET(j,K3)', u'i<j', u'INSET((j-1),K2)', u'i+1<j', u'INSET((j-1),J)']
//(DEFBEGIN(K3),DEFEND(K3)) -> (DEFBEGIN(K2)+1,DEFEND(K2)+1)
//(max(DEFBEGIN(K3),DEFBEGIN(K2)+1),min(DEFEND(K3),DEFEND(K2)+1)) -> (i+2,min(DEFEND(K3),DEFEND(K2)+1))
//GUARDS:  [u'INSET(i,K1)', u'INSET(j,K3)', u'i<j', u'INSET((j-1),K2)', u'i+1<j', u'INSET((j-1),J)']
//(DEFBEGIN(K3),DEFEND(K3)) -> (DEFBEGIN(K2)+1,DEFEND(K2)+1)
//(max(DEFBEGIN(K3),DEFBEGIN(K2)+1),min(DEFEND(K3),DEFEND(K2)+1)) -> (i+2,min(DEFEND(K3),DEFEND(K2)+1))
void funcB_1(DEFINTERVALFUNC(K3),DEFINTERVALFUNC(K2),DEFINTERVALFUNC(K0)){
	FOR_B_rec_1(i,DEFBEGIN(K0),DEFEND(K0)){
		FOR_B_rec_2(j,max(max(DEFBEGIN(K3),DEFBEGIN(K2)+1),i+2),min(DEFEND(K3),DEFEND(K2)+1)){
			Ddist(i,j) = min(Ddist(i,j),Ddist(i,(j-1))+d(i,(j-1)));
		}
	}
}

void funcB_2(DEFINTERVALFUNC(K3),DEFINTERVALFUNC(K2),DEFINTERVALFUNC(K1)){
	FOR_B_rec_3(i,DEFBEGIN(K1),DEFEND(K1)){
		FOR_B_rec_4(j,max(max(DEFBEGIN(K3),DEFBEGIN(K2)+1),i+2),min(DEFEND(K3),DEFEND(K2)+1)){
			Ddist(i,j) = min(Ddist(i,j),Ddist(i,(j-1))+d(i,(j-1)));
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



	cilk_spawn /* PARLEVEL 0 */ funcB_rec(PARAM(K0),PARAM(K2));
	/* PARLEVEL 0 */ funcB_rec(PARAM(K1),PARAM(K2));
	cilk_sync;
	cilk_spawn /* PARLEVEL 1 */ funcB_1(PARAM(K3),PARAM(K2),PARAM(K0));
	/* PARLEVEL 1 */ funcB_2(PARAM(K3),PARAM(K2),PARAM(K1));
	cilk_sync;
	cilk_spawn /* PARLEVEL 2 */ funcB_rec(PARAM(K0),PARAM(K3));
	/* PARLEVEL 2 */ funcB_rec(PARAM(K1),PARAM(K3));
	cilk_sync;
}
//GUARDS:  [u'i<j', u'INSET((j-1),J)']
//(i+1,DEFEND(J)) -> (DEFBEGIN(J)+1,DEFEND(J))
//GUARDS:  [u'k<i']

void funcA_loop(DEFINTERVALFUNC(J)){

	FOR_A_loop_2(i,DEFBEGIN(J),DEFEND(J)){
		FOR_A_loop_3(j,max(i+1,DEFBEGIN(J)+1),DEFEND(J)){

			TYPE t586= DALdist(i,j);
			if (i+1<j) {
				t586 = min(t586,DALdist(i,(j-1))+d(i,(j-1)));
			}
			if(EQ(i+1,j))
			{
				FOR_A_loop_1(k,DEFBEGIN(J),i){
					t586 = min(t586,DALdist(k,i)+d(k,i));
				}

			}
			DALdist(i,j) = t586;
		}
	}

}
//GUARDS:  [u'INSET(i,J0)', u'INSET(j,J1)', u'i<j']
//GUARDS:  [u'k<i']
void funcA_1(DEFINTERVALFUNC(J),DEFINTERVALFUNC(J0),DEFINTERVALFUNC(J1)){
	FOR_A_rec_2(i,DEFBEGIN(J0),DEFEND(J0)){
		FOR_A_rec_3(j,DEFBEGIN(J1),DEFEND(J1)){

			TYPE t740= Ddist(i,j);
			if (INSET((j-1),J0) && i+1<j) {
				t740 = min(t740,Ddist(i,(j-1))+d(i,(j-1)));
			}
			if(EQ(i+1,j))
			{
				FOR_A_rec_1(k,DEFBEGIN(J),i){
					t740 = min(t740,Ddist(k,i)+d(k,i));
				}

			}
			Ddist(i,j) = t740;
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



	/* PARLEVEL 0 */ funcA_rec(PARAM(J0));
	/* PARLEVEL 1 */ funcA_1(PARAM(J),PARAM(J0),PARAM(J1));
	/* PARLEVEL 2 */ funcB_rec(PARAM(J0),PARAM(J1));
	/* PARLEVEL 3 */ funcC_rec(PARAM(J0),PARAM(J1));
	/* PARLEVEL 4 */ funcA_rec(PARAM(J1));
}
