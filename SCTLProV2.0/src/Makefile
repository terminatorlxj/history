all:
	make -C utils opt
	ocamlopt -c ast.ml
	menhir --infer --explain parser.mly
	ocamllex lexer.mll
	ocamlfind ocamlopt -thread -I utils -o sctl2 utils.cmxa -package yojson -linkpkg -g ast.cmx print.ml parser.mli parser.ml lexer.ml \
	  typechecker.ml expr.ml formula.ml dep.ml interp.ml prover.ml communicate.ml prover_visualization.ml main.ml
	

lib:
	make -C utils all

lib-opt:
	make -C utils opt

parser: 
	menhir --infer --explain parser.mly

clean:
	make -C utils clean
	rm -f *.cm[ioxa]
	rm -f *.o
	rm -f sctl2
	rm -f sctl2.exe
	rm -f ./examples/*.typed
	rm -f ./examples/*.origin
	rm -f .origin
	rm -f .typed
	rm -f *.origin
	rm -f *.typed
	rm -f *.conflicts