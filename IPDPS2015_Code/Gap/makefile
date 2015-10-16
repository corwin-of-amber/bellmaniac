make:
	icc -O3 -o gapCOZ Gap_COZ.cpp -DCO -DUSE_PAPI -xhost -AVX -lpapi -I/usr/include/x86_64-linux-gnu/c++/4.8 -ipo -unroll
	icc -O3 -o gapCOZLoop Gap_COZ.cpp -DLOOPDP -DUSE_PAPI -xhost -AVX -lpapi -I/usr/include/x86_64-linux-gnu/c++/4.8 -ipo -unroll
