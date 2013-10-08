TARGETS = misc.cmx general_ast.cmx communication.cmx \
          ast_writer.cmx ast_reader.cmx annotation_type_checker.cmx \
          java_frontend.cmx ast_translator.cmx

OCAML_INCL = str.cmxa nums.cmxa unix.cmxa

VERIFAST = ..

all: ${TARGETS}

misc.cmx: misc.ml
	${OCAMLOPTOPT} -c misc.ml

general_ast.cmx: general_ast.ml misc.cmx
	${OCAMLOPTOPT} -c general_ast.ml

ast_writer.cmx: ast_writer.ml general_ast.cmx
	${OCAMLOPTOPT} -c ast_writer.ml

ast_reader.cmx: ast_reader.ml general_ast.cmx
	${OCAMLOPTOPT} -pp ${CAMLP4O} -c ast_reader.ml

communication.cmx: communication.ml ast_reader.cmx
	${OCAMLOPTOPT} -thread -c communication.ml

annotation_type_checker.cmi: annotation_type_checker.mli communication.cmx
	${OCAMLOPTOPT} -c annotation_type_checker.mli

annotation_type_checker.cmx: annotation_type_checker.ml annotation_type_checker.cmi general_ast.cmx
	${OCAMLOPTOPT} -c annotation_type_checker.ml

java_frontend.cmi: java_frontend.mli annotation_type_checker.cmx general_ast.cmx
	${OCAMLOPTOPT} -c java_frontend.mli

java_frontend.cmx: java_frontend.ml java_frontend.cmi ast_reader.cmx communication.cmx
	${OCAMLOPTOPT} -c java_frontend.ml

ast_translator.cmx: ast_translator.ml general_ast.cmx
	${OCAMLOPTOPT} -pp ${CAMLP4O} -annot -w p -c -I ./linux -I ${VERIFAST} ast_translator.ml

clean:
	rm -f *.cm*
	rm -f *.o *.a *.annot
	rm -f ${EXEC_NAME}
