make:
	icc -O3 -o gapCOZ Gap_COZ.cpp -DCO -O3 -xhost -AVX -ipo -unroll
	icc -O3 -o gapCO Gap_CO_naive.cpp -DCO  -O3 -xhost -AVX -ipo -unroll
	icc -O3 -o gapLOOPDP Gap_CO_naive.cpp -DLOOPDP  -O3 -xhost -AVX -ipo -unroll

