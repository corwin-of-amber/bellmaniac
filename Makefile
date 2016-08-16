CC=icc
CCFLAGS=-O3

CCFLAGS=-DCO -xhost  -ansi-alias -ip -qopt-subscript-in-range -qopt-prefetch=4 -fomit-frame-pointer \
 -funroll-all-loops  -parallel -restrict

CCFLAGS_accordion= -O3  -DCO  -xhost -AVX

paren: paren.cpp codegen_c/Parenthesis/paren.cpp
	$(CC) $(CCFLAGS) -o $@ -DDEBUG -DB=64 -I include -I codegen_c/Parenthesis $+

paren-fast: paren.cpp codegen_c/Parenthesis/paren.cpp
	$(CC) $(CCFLAGS) -o $@ -DB=64 -I include -I codegen_c/Parenthesis $+

paren-auto: codegen_c/paren.cpp  codegen_c/Parenthesis/paren.cpp 
	 $(CC) $(CCFLAGS) -o $@ -DDEBUG -DB=64 -I include -I codegen_c/Parenthesis $+

gap-auto: codegen_c/gap.cpp  codegen_c/Gap/gap.cpp
	$(CC) $(CCFLAGS) -o $@ -DDEBUG -DB=64 -I include -I codegen_c/Gap $+

gap: gap.cpp codegen_c/Gap/gap.cpp
	$(CC) $(CCFLAGS) -o $@ -DDEBUG -DB=64 -I include -I codegen_c/Gap $+

gap-fast: gap.cpp codegen_c/Gap/gap.cpp
	$(CC) $(CCFLAGS) -o $@ -DB=64 -I include -I codegen_c/Gap $+

accordion: codegen_c/Accordion/accordion.cpp codegen_c/accordion-new-all.cpp
	$(CC) $(CCFLAGS_accordion) -o $@ -DDEBUG -DB=64 -I include codegen_c/Accordion/accordion.cpp

lcs: codegen_c/LCS/lcs.cpp codegen_c/lcs-all.cpp
	$(CC) $(CCFLAGS) -DLOOPDP -o $@ -DDEBUG -DB=64 -I include codegen_c/LCS/lcs.cpp

bitonic: codegen_c/Bitonic/bitonic.cpp codegen_c/bitonic-all.cpp
	$(CC) $(CCFLAGS) -o $@ -DDEBUG -DB=64 -I include codegen_c/Bitonic/bitonic.cpp

clean:
	rm -f paren gap paren-fast gap-fast *~

