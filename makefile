all: delete

	ocamllex miniLEX.mll
	ocamlyacc miniYACC.mly
	ocamlc -c astTree.ml
	ocamlc -c miniYACC.mli
	ocamlc -c miniLEX.ml
	ocamlc -c miniYACC.ml
	ocamlc -c interpreter.ml

	ocamlc -o interpreter astTree.cmo miniLEX.cmo miniYACC.cmo interpreter.cmo

delete:
	#/bin/rm -f calculator calculator.cmi calculator.cmo miniLEX.cmi miniLEX.cmo miniLEX.ml miniYACC.cmi miniYACC.cmo miniYACC.ml miniYACC.mli makefile~
