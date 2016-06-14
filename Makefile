CC=g++
CCFLAGS=-O3

paren: output.cpp codegen_c/Parenthesis/paren.cpp
	$(CC) $(CCFLAGS) -o $@ -DDEBUG -DB=64 -I include -I codegen_c/Parenthesis $+

gap: output.cpp codegen_c/Gap/gap.cpp
	$(CC) $(CCFLAGS) -o $@ -DDEBUG -DB=64 -I include -I codegen_c/Gap $+


paren-ref: codegen_c/paren-all.cpp codegen_c/Parenthesis/paren.cpp
	$(CC) $(CCFLAGS) -o $@ -DDEBUG -DB=64 -I include -I codegen_c/Parenthesis $+

