COMPILER=ocamlc
 
all: clean
	$(COMPILER) -c ast.ml
	ocamlyacc parse.mly
	$(COMPILER) -c parse.mli
	$(COMPILER) -c parse.ml
	ocamllex lex.mll
	$(COMPILER) -c lex.ml
	$(COMPILER) -c eval.ml
	$(COMPILER) -c word32.ml
	$(COMPILER) -c mips.ml
	$(COMPILER) -c compile.ml
	$(COMPILER) -c cish.ml
	$(COMPILER) -o ps4 ast.cmo parse.cmo lex.cmo eval.cmo word32.cmo mips.cmo compile.cmo cish.cmo

clean:
	-rm *.cmo *.cmi ps4 parse.ml parse.mli lex.ml
