
void funcA_loop(DEFINTERVALFUNC(I),DEFINTERVALFUNC(J)){

	FOR_A_loop_1(i,DEFBEGIN(I),DEFEND(I)){
		FOR_A_loop_2(j,DEFBEGIN(J),DEFEND(J)){
			if (IS_UNDEF(DALdist(i,j))){
				if(DELTA(i,j)){
					DALdist(i,j)=DALdist((i-1),(j-1))+1;}
				if((!DELTA(i,j))){
					DALdist(i,j)=OMAX(DALdist(i,(j-1)),DALdist((i-1),j));}

			}
		}
	}

}
//GUARDS:  [u'INSET(i,I0)', u'INSET(j,J1)', u'INSET((j-1),J0)']
//GUARDS:  [u'INSET(i,I1)', u'INSET(j,J0)', u'INSET((i-1),I0)']
//GUARDS:  [u'INSET(i,I1)', u'INSET(j,J1)', u'INSET((i-1),I0)', u'INSET((j-1),J0)']
//GUARDS:  [u'INSET(i,I1)', u'INSET(j,J1)', u'INSET((i-1),I0)', u'INSET((j-1),J1)']
//GUARDS:  [u'INSET(i,I1)', u'INSET(j,J1)', u'INSET((j-1),J0)', u'INSET((i-1),I1)']

void funcA_rec(DEFINTERVALFUNC(I),DEFINTERVALFUNC(J)){
	if (BASE_CONSTRAINT_A(I,J)){
		funcA_loop(PARAM(I),PARAM(J));
		return;
	}
	DEFINTERVALSTMT(I0);
	DEFBEGIN(I0) = DEFBEGIN(I);
	DEFEND(I0) = (DEFEND(I) + DEFBEGIN(I))/2;
	DEFINTERVALSTMT(I1);
	DEFBEGIN(I1) = DEFEND(I0);
	DEFEND(I1) = DEFEND(I);
	DEFINTERVALSTMT(J0);
	DEFBEGIN(J0) = DEFBEGIN(J);
	DEFEND(J0) = (DEFEND(J) + DEFBEGIN(J))/2;
	DEFINTERVALSTMT(J1);
	DEFBEGIN(J1) = DEFEND(J0);
	DEFEND(J1) = DEFEND(J);

	funcA_rec(PARAM(I0),PARAM(J0));
	FOR_A_rec_1(i,DEFBEGIN(I0),DEFEND(I0)){
		FOR_A_rec_2(j,DEFBEGIN(J1),DEFEND(J0)+1){
			if (IS_UNDEF(Ddist(i,j))){
				if(DELTA(i,j)){
					Ddist(i,j)=Ddist((i-1),(j-1))+1;}
				if((!DELTA(i,j))){
					Ddist(i,j)=OMAX(Ddist(i,(j-1)),Ddist((i-1),j));}

			}
		}
	}

	funcA_rec(PARAM(I0),PARAM(J1));
	FOR_A_rec_3(i,DEFBEGIN(I1),DEFEND(I0)+1){
		FOR_A_rec_4(j,DEFBEGIN(J0),DEFEND(J0)){
			if (IS_UNDEF(Ddist(i,j))){
				if(DELTA(i,j)){
					Ddist(i,j)=Ddist((i-1),(j-1))+1;}
				if((!DELTA(i,j))){
					Ddist(i,j)=OMAX(Ddist(i,(j-1)),Ddist((i-1),j));}

			}
		}
	}

	funcA_rec(PARAM(I1),PARAM(J0));
	FOR_A_rec_5(i,DEFBEGIN(I1),DEFEND(I0)+1){
		FOR_A_rec_6(j,DEFBEGIN(J1),DEFEND(J0)+1){
			if (IS_UNDEF(Ddist(i,j))){
				if(DELTA(i,j)){
					Ddist(i,j)=Ddist((i-1),(j-1))+1;}
				if((!DELTA(i,j))){
					Ddist(i,j)=OMAX(Ddist(i,(j-1)),Ddist((i-1),j));}

			}
		}
	}

	FOR_A_rec_7(i,DEFBEGIN(I1),DEFEND(I0)+1){
		FOR_A_rec_8(j,DEFBEGIN(J1)+1,DEFEND(J1)){
			if (IS_UNDEF(Ddist(i,j))){
				if(DELTA(i,j)){
					Ddist(i,j)=Ddist((i-1),(j-1))+1;}
				if((!DELTA(i,j))){
					Ddist(i,j)=OMAX(Ddist(i,(j-1)),Ddist((i-1),j));}

			}
		}
	}

	FOR_A_rec_9(i,DEFBEGIN(I1)+1,DEFEND(I1)){
		FOR_A_rec_10(j,DEFBEGIN(J1),DEFEND(J0)+1){
			if (IS_UNDEF(Ddist(i,j))){
				if(DELTA(i,j)){
					Ddist(i,j)=Ddist((i-1),(j-1))+1;}
				if((!DELTA(i,j))){
					Ddist(i,j)=OMAX(Ddist(i,(j-1)),Ddist((i-1),j));}

			}
		}
	}

	funcA_rec(PARAM(I1),PARAM(J1));
}
