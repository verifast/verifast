# You probably don't want to use this makefile, you probably want
# /src/GNUmakefile.

# If you really want to use this makefile, just use /src/GNUmakefile and
# provide a target of this makefile, e.g. "make java_frontend"

# Note: there are dependencies to the outer Makefile (/src/GNUMakefile).

java_frontend: java_frontend/misc.cmx java_frontend/general_ast.cmx java_frontend/communication.cmx \
          java_frontend/ast_writer.cmx java_frontend/ast_reader.cmx java_frontend/annotation_type_checker.cmx \
          java_frontend/java_frontend.cmx java_frontend/ast_translator.cmx

java_frontend/misc.cmx: java_frontend/misc.ml
java_frontend/general_ast.cmx: java_frontend/general_ast.ml java_frontend/misc.cmx
java_frontend/ast_writer.cmx: java_frontend/ast_writer.ml java_frontend/general_ast.cmx
java_frontend/ast_reader.cmx: java_frontend/ast_reader.ml java_frontend/general_ast.cmx
java_frontend/communication.cmx: java_frontend/communication.ml java_frontend/ast_reader.cmx
java_frontend/annotation_type_checker.cmi: java_frontend/annotation_type_checker.mli java_frontend/communication.cmx
java_frontend/annotation_type_checker.cmx: java_frontend/annotation_type_checker.ml java_frontend/annotation_type_checker.cmi java_frontend/general_ast.cmx
java_frontend/java_frontend.cmi: java_frontend/java_frontend.mli java_frontend/annotation_type_checker.cmx java_frontend/general_ast.cmx
java_frontend/java_frontend.cmx: java_frontend/java_frontend.ml java_frontend/java_frontend.cmi java_frontend/ast_reader.cmx java_frontend/communication.cmx
java_frontend/ast_translator.cmx: java_frontend/ast_translator.ml java_frontend/general_ast.cmx ast.cmx parser.cmx

# Note: only 1 CPU allowed for this test because ASTServer currently can only
#       hande one request at a time
test_java_front: build test_plugin
	$(SET_ENV); \
	cd ../examples/java/frontend; ../../../bin/mysh -cpus 1 < frontend.mysh

JAVA_FE_INCLS = -thread threads.cmxa misc.cmx general_ast.cmx ast_reader.cmx \
  communication.cmx annotation_type_checker.cmx java_frontend.cmx \
  ast_translator.cmx

clean::
	rm -f java_frontend/*.cm*
	rm -f java_frontend/*.o java_frontend/*.a java_frontend/*.annot

