all: coz co loop

coz: 
	icc -O3 -o parCOZ Par_COZ.cpp -DCO  -AVX -xhost  -ansi-alias -ip -qopt-subscript-in-range -qopt-prefetch=4 -fomit-frame-pointer -funroll-all-loops  -parallel -restrict

co:
	icc -O3 -o parCO Par_CO_naive.cpp -DCO  -AVX -xhost  -ansi-alias -ip -qopt-subscript-in-range -qopt-prefetch=4 -fomit-frame-pointer -funroll-all-loops  -parallel -restrict

loop:
	icc -O3 -o parLOOPDP Par_CO_naive.cpp -DLOOPDP  -AVX -xhost  -ansi-alias -ip -qopt-subscript-in-range -qopt-prefetch=4 -fomit-frame-pointer -funroll-all-loops  -parallel -restrict


