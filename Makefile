CC=icc
CCFLAGS=-O3

#CCFLAGS=-DCO -xhost  -ansi-alias -ip -qopt-subscript-in-range -qopt-prefetch=4 -fomit-frame-pointer \
# -funroll-all-loops  -parallel -restrict

INCFLAGS= -I examples/cpp/include

all: paren gap accordion lcs bitonic

paren: paren-auto paren-co paren-coz paren-loop

gap: gap-auto gap-co gap-coz gap-loop

accordion: accordion-auto accordion-co accordion-coz accordion-loop

lcs: lcs-auto-loop

bitonic: bitonic-auto-loop

PAREN_CCFLAGS=  -O3 -ip -parallel -AVX -xHost
paren-auto: examples/cpp/autogenerated/paren-auto.cpp  examples/cpp/harness/Parenthesis/paren.cpp
	$(CC) $(PAREN_CCFLAGS) -o ./bin/$@ -DCO  -DB=64 -Iexamples/cpp/harness/Parenthesis $(INCFLAGS) $+
paren-loop: IPDPS2015_Code/Parenthesis/Par_COZ.cpp
	$(CC) $(PAREN_CCFLAGS) -o ./bin/$@ -DLOOPDP $+
paren-coz: IPDPS2015_Code/Parenthesis/Par_COZ.cpp
	$(CC) $(PAREN_CCFLAGS) -o ./bin/$@ -DCO $+
paren-co: IPDPS2015_Code/Parenthesis/Par_CO_naive.cpp
	$(CC) $(PAREN_CCFLAGS) -o ./bin/$@ -DCO $+
    
    
GAP_CCFLAGS= -O3 -xhost -AVX -ipo -unroll
gap-auto: examples/cpp/autogenerated/gap-auto.cpp  examples/cpp/harness/Gap/gap.cpp
	$(CC) $(GAP_CCFLAGS) -o ./bin/$@ -DCO  -DB=64 -Iexamples/cpp/harness/Gap $(INCFLAGS) $+
gap-loop: IPDPS2015_Code/Gap/Gap_COZ.cpp
	$(CC) $(GAP_CCFLAGS) -o ./bin/$@ -DLOOPDP $+
gap-coz: IPDPS2015_Code/Gap/Gap_COZ.cpp
	$(CC) $(GAP_CCFLAGS) -o ./bin/$@ -DCO $+
gap-co: IPDPS2015_Code/Gap/Gap_CO_naive.cpp
	$(CC) $(GAP_CCFLAGS) -o ./bin/$@ -DCO $+
    
ACCORDION_CCFLAGS= -O3 -xhost -AVX   
accordion-auto: examples/cpp/autogenerated/accordion-auto.cpp  examples/cpp/harness/Accordion/accordion.cpp
	$(CC) $(ACCORDION_CCFLAGS) -o ./bin/$@ -DCO  -DB=64 -Iexamples/cpp/harness/Accordion $(INCFLAGS) $+
accordion-loop: IPDPS2015_Code/ProteinAccordionFolding/PF_COZ.cpp
	$(CC) $(ACCORDION_CCFLAGS) -o ./bin/$@ -DLOOPDP $+
accordion-coz: IPDPS2015_Code/ProteinAccordionFolding/PF_COZ.cpp
	$(CC) $(ACCORDION_CCFLAGS) -o ./bin/$@ -DCO $+
accordion-co: IPDPS2015_Code/ProteinAccordionFolding/PF_CO.cpp
	$(CC) $(ACCORDION_CCFLAGS) -o ./bin/$@ -DCO $+
    
LCS_CCFLAGS= -O3 -xhost -AVX
lcs-auto-loop: examples/cpp/autogenerated/lcs-auto.cpp  examples/cpp/harness/LCS/lcs.cpp
	$(CC) $(LCS_CCFLAGS) -o ./bin/$@ -DCO  -DDEBUG -DB=64 -Iexamples/cpp/harness/LCS $(INCFLAGS) $+

BITONIC_CCFLAGS= -O3 -xhost -AVX   
bitonic-auto-loop: examples/cpp/autogenerated/bitonic-auto.cpp  examples/cpp/harness/Bitonic/bitonic.cpp
	$(CC) $(BITONIC_CCFLAGS) -o ./bin/$@ -DCO  -DDEBUG -DB=64 -Iexamples/cpp/harness/Bitonic $(INCFLAGS) $+

clean:
	rm -f bin/*-auto bin/*-loop bin/*-co bin/*-coz bin/*~ *~

