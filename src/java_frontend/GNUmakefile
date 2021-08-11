# You probably don't want to use this makefile, you probably want
# /src/GNUmakefile.

# If you really want to use this makefile, just use /src/GNUmakefile and
# provide a target of this makefile, e.g. "make java_frontend"

# Note: only 1 CPU allowed for this test because ASTServer currently can only
#       hande one request at a time
test_java_front: build test_plugin
	$(SET_ENV); \
	cd ../examples/java/frontend; ../../../bin/mysh -cpus 1 < frontend.mysh

# TODO: get rid of SExpressions.cmx SExpressionEmitter.cmx, what are they doing here?
# TODO: get rid of including JAVA_FE_DEPS in JAVA_FE_INCLS?
JAVA_FE_DEPS = java_frontend/misc.cmx java_frontend/general_ast.cmx \
  java_frontend/ast_reader.cmx java_frontend/ast_writer.cmx \
  java_frontend/communication.cmx java_frontend/annotation_type_checker.cmx \
  java_frontend/java_frontend.cmx java_frontend/ast_translator.cmx \
  java_frontend/java_frontend_bridge.cmx SExpressions.cmx SExpressionEmitter.cmx
JAVA_FE_INCLS = -thread -package threads $(JAVA_FE_DEPS)

clean::
	rm -f java_frontend/*.cm*
	rm -f java_frontend/*.o java_frontend/*.a java_frontend/*.annot

