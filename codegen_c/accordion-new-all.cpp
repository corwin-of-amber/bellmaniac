
/*
 * CAPTAIN'S LOG
 *
 * funcD has been hand-tweaked to try and match the performance of PF_CO from IPDPS2015.
 * The most important optimization is case-splitting by 2*j-i+1 < max(DEFBEGIN(K2), j+2).
 * If the condition is true, min(k,2*j-i+1) can be replaced with 2*j-i+1.
 * Consequently, the expression SOF[j+1, 2*j-i+1] can be factored out of the loop (I think
 * icc is doing it for us).
 *
 * Copy optimization gives another small improvement; to test the effect of different
 * layers of optimization, three flags control whether to copy the read-region of 'dist',
 * the read-region of 'SOF', or the write-region of 'dist' (and then copy it back at the end).
 * The first is the most important, other two give another ~5%.
 *
 * Copy optimization without case splitting does not seem to help that much.
 *
 * Parallelization and vectorization directives have no effect in this case.
 */

#define D_CO_read
#define D_CO_SOF
#define D_CO_write

void funcD_loop(DEFINTERVALFUNC(K0),DEFINTERVALFUNC(K1),DEFINTERVALFUNC(K2)){
#ifdef D_CO_read
	__declspec(align(ALIGNMENT)) TYPE V[B * B];
	copy_dist_part(V,PARAM(K1),PARAM(K2));
#define Ddist_read(i,j) DdistSimpleV(i,j,K1,K2)
#else
#define Ddist_read DDLdist
#endif
#ifdef D_CO_SOF
	__declspec(align(ALIGNMENT)) TYPE F[B * B];
	copy_SOF_part(F,PARAM(K1),PARAM(K2));
#define DDELTA(i,j,k) F[((j)+1 - DEFBEGIN(K1))*B + min((k),2*(j)-(i)+1) - DEFBEGIN(K2) ]
#else
#define DDELTA DELTA
#endif
#define DSOF2(i,j) SOF[(i)*N + (j)] // cannot use CO for this (will go outside K1 x K2)
#ifdef D_CO_write
	__declspec(align(ALIGNMENT)) TYPE X[B * B];
	copy_dist_part(X,PARAM(K0),PARAM(K1));
#define Ddist_write(i,j) DdistSimpleX(i,j,K0,K1)
#else
#define Ddist_write DDLdist
#endif

	FOR_D_loop_2(i,DEFBEGIN(K0),DEFEND(K0)){
//#pragma parallel
		FOR_D_loop_3(j,DEFBEGIN(K1),DEFEND(K1)-1){

			TYPE t21= /*DdistSimpleX(i,j,K0,K1)*/Ddist_write(i,j);
            if (2*j-i+1 < max(DEFBEGIN(K2), j+2)) {
                //TYPE tval = 0;
//#pragma ivdep
                FOR_D_loop_1(k,DEFBEGIN(K2),DEFEND(K2)) {
                    // optimization; k > 2*j-i+1, so min(k,2*j-i+1)=2*j-i+1
                    t21 = max(t21, /*DdistSimpleV((j+1),k,K1,K2*)*/Ddist_read(j+1,k) + DSOF2(j+1, 2*j-i+1));
                }
                //t21 = max(t21, tval);  
            }
            else {
//#pragma ivdep
                FOR_D_loop_1(k,DEFBEGIN(K2),DEFEND(K2)){
                /*
                    assert(DEFBEGIN(K1) <= j+1 && j+1 < DEFEND(K1));
                    assert(DEFBEGIN(K2) <= min((k),2*(j)-(i)+1) && min((k),2*(j)-(i)+1) < DEFEND(K2));
                    assert(DDELTA(i,j,k) == DELTA(i,j,k));
                    */
                    t21 = max(t21,Ddist_read(j+1,k)/*DdistSimpleV((j+1),k,K1,K2)*/+DDELTA(i,j,k)/* INSET(j+1,K1) && INSET(k,K2) */);
                }
            }

			/*DdistSimpleX(i,j,K0,K1)*/Ddist_write(i,j) = t21/* INSET(i,K0) && INSET(j,K1) */;
		}
	}

#ifdef D_CO_write
    copy_to_dist(X, PARAM(K0), PARAM(K1));
#endif

}
void funcD_1(DEFINTERVALFUNC(K2),DEFINTERVALFUNC(L2),DEFINTERVALFUNC(L3),DEFINTERVALFUNC(L0)){
	FOR_D_rec_2(i,DEFBEGIN(L0),DEFEND(L0)){
		{
			LET(j,DEFEND(L2)-1);

			TYPE t278= Ddist(i,j);
			FOR_D_rec_1(k,DEFBEGIN(K2),DEFEND(K2)){
				t278 = max(t278,Ddist(j+1,k)+DELTA(i,j,k)/* INSET(j+1,L3) && INSET(k,K2) */);
			}

			Ddist(i,j) = t278/* INSET(i,L0) && INSET(j,L2) */;
		}
	}
}

void funcD_2(DEFINTERVALFUNC(K2),DEFINTERVALFUNC(L2),DEFINTERVALFUNC(L3),DEFINTERVALFUNC(L1)){
	FOR_D_rec_4(i,DEFBEGIN(L1),DEFEND(L1)){
		{
			LET(j,DEFEND(L2)-1);

			TYPE t158= Ddist(i,j);
			FOR_D_rec_3(k,DEFBEGIN(K2),DEFEND(K2)){
				t158 = max(t158,Ddist(j+1,k)+DELTA(i,j,k)/* INSET(j+1,L3) && INSET(k,K2) */);
			}

			Ddist(i,j) = t158/* INSET(i,L1) && INSET(j,L2) */;
		}
	}
}

void funcD_rec(DEFINTERVALFUNC(K0),DEFINTERVALFUNC(K1),DEFINTERVALFUNC(K2)){
	if (BASE_CONSTRAINT_D(K0,K1,K2)){
		funcD_loop(PARAM(K0),PARAM(K1),PARAM(K2));
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



	cilk_spawn /* PARLEVEL 0 */ funcD_1(PARAM(K2),PARAM(L2),PARAM(L3),PARAM(L0));
	cilk_spawn /* PARLEVEL 0 */ funcD_rec(PARAM(L0),PARAM(L3),PARAM(L4));
	cilk_spawn /* PARLEVEL 0 */ funcD_2(PARAM(K2),PARAM(L2),PARAM(L3),PARAM(L1));
	/* PARLEVEL 0 */ funcD_rec(PARAM(L1),PARAM(L3),PARAM(L4));
	cilk_sync;
	cilk_spawn /* PARLEVEL 1 */ funcD_rec(PARAM(L0),PARAM(L2),PARAM(L4));
	cilk_spawn /* PARLEVEL 1 */ funcD_rec(PARAM(L0),PARAM(L3),PARAM(L5));
	cilk_spawn /* PARLEVEL 1 */ funcD_rec(PARAM(L1),PARAM(L2),PARAM(L4));
	/* PARLEVEL 1 */ funcD_rec(PARAM(L1),PARAM(L3),PARAM(L5));
	cilk_sync;
	cilk_spawn /* PARLEVEL 2 */ funcD_rec(PARAM(L0),PARAM(L2),PARAM(L5));
	/* PARLEVEL 2 */ funcD_rec(PARAM(L1),PARAM(L2),PARAM(L5));
	cilk_sync;
}

void funcC_loop(DEFINTERVALFUNC(J0),DEFINTERVALFUNC(J1)){

	FOR_C_loop_2(i,DEFBEGIN(J0),DEFEND(J0)){
		FOR_C_loop_3(j,i+1,DEFEND(J0)-1){

			TYPE t342= DCLdist(i,j);
			FOR_C_loop_1(k,max(DEFBEGIN(J1),j+2),DEFEND(J1)){
				t342 = max(t342,DCLdist(j+1,k)+DELTA(i,j,k)/* INSET(k,J1) && INSET(j+1,J0) && j+1<k */);
			}

			DCLdist(i,j) = t342/* INSET(i,J0) && INSET(j,J0) && i<j */;
		}
	}

}
//SPL CASE: i K0 j K0 j+1
void funcC_1(DEFINTERVALFUNC(K1),DEFINTERVALFUNC(K0),DEFINTERVALFUNC(J1)){
	FOR_C_rec_2(i,DEFBEGIN(K0),DEFEND(K0)-1){
		{
			LET(j,DEFEND(K0)-1);

			TYPE t499= Ddist(i,j);
			FOR_C_rec_1(k,max(DEFBEGIN(J1),j+2),DEFEND(J1)){
				t499 = max(t499,Ddist(j+1,k)+DELTA(i,j,k)/* INSET(k,J1) && INSET(j+1,K1) && j+1<k */);
			}

			Ddist(i,j) = t499/* INSET(i,K0) && INSET(j,K0) && i<j */;
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



	cilk_spawn /* PARLEVEL 0 */ funcC_1(PARAM(K1),PARAM(K0),PARAM(J1));
	cilk_spawn /* PARLEVEL 0 */ funcD_rec(PARAM(K0),PARAM(K1),PARAM(K2));
	/* PARLEVEL 0 */ funcC_rec(PARAM(K1),PARAM(K2));
	cilk_sync;
	cilk_spawn /* PARLEVEL 1 */ funcC_rec(PARAM(K0),PARAM(K2));
	cilk_spawn /* PARLEVEL 1 */ funcD_rec(PARAM(K0),PARAM(K1),PARAM(K3));
	/* PARLEVEL 1 */ funcC_rec(PARAM(K1),PARAM(K3));
	cilk_sync;
	/* PARLEVEL 2 */ funcC_rec(PARAM(K0),PARAM(K3));
}

void funcB_loop(DEFINTERVALFUNC(J0),DEFINTERVALFUNC(J1)){

	FOR_B_loop_2(i,DEFBEGIN(J0),DEFEND(J0)){
		FOR_B_loop_3(j,DEFBEGIN(J1),DEFEND(J1)-1){

			TYPE t572= DBLdist(i,j);
			FOR_B_loop_1(k,max(DEFBEGIN(J1),j+2),DEFEND(J1)){
				t572 = max(t572,DBLdist(j+1,k)+DELTA(i,j,k)/* INSET(j+1,J1) && INSET(k,J1) && j+1<k */);
			}

			DBLdist(i,j) = t572/* INSET(i,J0) && INSET(j,J1) && i<j */;
		}
	}

}
void funcB_1(DEFINTERVALFUNC(K3),DEFINTERVALFUNC(K2),DEFINTERVALFUNC(K0)){
	FOR_B_rec_2(i,DEFBEGIN(K0),DEFEND(K0)){
		{
			LET(j,DEFEND(K2)-1);

			TYPE t797= Ddist(i,j);
			FOR_B_rec_1(k,max(DEFBEGIN(K3),j+2),DEFEND(K3)){
				t797 = max(t797,Ddist(j+1,k)+DELTA(i,j,k)/* INSET(j+1,K3) && INSET(k,K3) && j+1<k */);
			}

			Ddist(i,j) = t797/* INSET(i,K0) && INSET(j,K2) && i<j */;
		}
	}
}

void funcB_2(DEFINTERVALFUNC(K3),DEFINTERVALFUNC(K2),DEFINTERVALFUNC(K1)){
	FOR_B_rec_4(i,DEFBEGIN(K1),DEFEND(K1)){
		{
			LET(j,DEFEND(K2)-1);

			TYPE t681= Ddist(i,j);
			FOR_B_rec_3(k,max(DEFBEGIN(K3),j+2),DEFEND(K3)){
				t681 = max(t681,Ddist(j+1,k)+DELTA(i,j,k)/* INSET(j+1,K3) && INSET(k,K3) && j+1<k */);
			}

			Ddist(i,j) = t681/* INSET(i,K1) && INSET(j,K2) && i<j */;
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
	cilk_spawn /* PARLEVEL 0 */ funcB_rec(PARAM(K0),PARAM(K3));
	cilk_spawn /* PARLEVEL 0 */ funcB_rec(PARAM(K1),PARAM(K2));
	/* PARLEVEL 0 */ funcB_rec(PARAM(K1),PARAM(K3));
	cilk_sync;
	cilk_spawn /* PARLEVEL 1 */ funcD_rec(PARAM(K0),PARAM(K2),PARAM(K3));
	/* PARLEVEL 1 */ funcD_rec(PARAM(K1),PARAM(K2),PARAM(K3));
	cilk_sync;
	cilk_spawn /* PARLEVEL 2 */ funcB_1(PARAM(K3),PARAM(K2),PARAM(K0));
	/* PARLEVEL 2 */ funcB_2(PARAM(K3),PARAM(K2),PARAM(K1));
	cilk_sync;
}

void funcA_loop(DEFINTERVALFUNC(J)){

	FOR_A_loop_2(i,DEFBEGIN(J),DEFEND(J)){
		FOR_A_loop_3(j,i+1,DEFEND(J)-1){

			TYPE t899= DALdist(i,j);
			FOR_A_loop_1(k,j+2,DEFEND(J)){
				t899 = max(t899,DALdist(j+1,k)+DELTA(i,j,k)/* j+1<k && INSET(j+1,J) */);
			}

			DALdist(i,j) = t899/* i<j */;
		}
	}

}
//SPL CASE: i J0 j J0 j+1
void funcA_1(DEFINTERVALFUNC(J0),DEFINTERVALFUNC(J1)){
	FOR_A_rec_2(i,DEFBEGIN(J0),DEFEND(J0)-1){
		{
			LET(j,DEFEND(J0)-1);

			TYPE t992= Ddist(i,j);
			FOR_A_rec_1(k,max(DEFBEGIN(J1),j+2),DEFEND(J1)){
				t992 = max(t992,Ddist(j+1,k)+DELTA(i,j,k)/* INSET(k,J1) && INSET(j+1,J1) && j+1<k */);
			}

			Ddist(i,j) = t992/* INSET(i,J0) && INSET(j,J0) && i<j */;
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



	/* PARLEVEL 0 */ funcA_rec(PARAM(J1));
	/* PARLEVEL 1 */ funcB_rec(PARAM(J0),PARAM(J1));
	/* PARLEVEL 2 */ funcC_rec(PARAM(J0),PARAM(J1));
	/* PARLEVEL 3 */ funcA_1(PARAM(J0),PARAM(J1));
	/* PARLEVEL 4 */ funcA_rec(PARAM(J0));
}
