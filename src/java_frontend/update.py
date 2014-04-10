#!/usr/bin/python

import subprocess

ocaml_files = [
         #Used OCaml source files
         "annotation_type_checker.ml",  
         "annotation_type_checker.mli",
         "ast_reader.ml",
         "ast_writer.ml",
         "communication.ml",
         "general_ast.ml",
         "internal_java_frontend.ml",
         "java_frontend.ml",
         "java_frontend.mli",
         "misc.ml",
         
         #Unsed OCaml source files
         #"ast_value.ml",
         #"main.ml",
         #"test.ml"
         #"GNUmakefile"
         ]

for file in ocaml_files:
  subprocess.call(['wget', '-N', 'http://bitbucket.org/gijsv/stance-java-frontend/raw/tip/java_frontend/'+file])
