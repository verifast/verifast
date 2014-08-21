#!/usr/bin/python

import os
import optparse
import subprocess

parser = optparse.OptionParser() 

parser.add_option("-r", "--repo", help="update from repository", 
            dest="repo", default=False, action="store_true")
parser.add_option("-l", "--local", help="update from local files", 
            dest="local", default=False, action="store_true")

(options, args) = parser.parse_args()

localdir = "../../../stance/java_frontend/"

ocaml_files = [
         #Used OCaml source files
         "annotation_type_checker.ml",  
         "annotation_type_checker.mli",
         "ast_reader.ml",
         "ast_writer.ml",
         "communication.ml",
         "general_ast.ml",
         "java_frontend.ml",
         "java_frontend.mli",
         "misc.ml",
         
         #Unsed OCaml source files
         #"internal_java_frontend.ml",
         #"ast_value.ml",
         #"main.ml",
         #"test.ml"
         #"GNUmakefile"
         ]

if options.repo:
  for file in ocaml_files:
    subprocess.call(['wget', '-N', 'http://bitbucket.org/gijsv/stance-java-frontend/raw/tip/java_frontend/'+file])

if options.local:
  dir = os.getcwd()
  os.chdir(localdir)
  subprocess.call(['./frontend.py', '-j'])
  os.chdir(dir)
  for file in ocaml_files:
    subprocess.call(['cp', localdir + "java_frontend/" + file, "."])
  subprocess.call(['cp', localdir + "java_frontend/" + "ast_server.jar", "."])