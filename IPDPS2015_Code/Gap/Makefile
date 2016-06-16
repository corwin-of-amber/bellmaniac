make:
	icc -O3 -o gapCOZ Gap_COZ.cpp -DCO -xhost  -ansi-alias -ip -qopt-subscript-in-range -qopt-prefetch=4 -fomit-frame-pointer -funroll-all-loops  -parallel -restrict
	icc -O3 -o gapCO Gap_CO_naive.cpp -DCO  -xhost  -ansi-alias -ip -qopt-subscript-in-range -qopt-prefetch=4 -fomit-frame-pointer -funroll-all-loops  -parallel -restrict
	icc -O3 -o gapLOOPDP Gap_CO_naive.cpp -DLOOPDP  -xhost  -ansi-alias -ip -qopt-subscript-in-range -qopt-prefetch=4 -fomit-frame-pointer -funroll-all-loops  -parallel -restrict

