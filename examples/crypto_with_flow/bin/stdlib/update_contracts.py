#!/usr/bin/python

def insert_part(path, line, s):
  f1 = open(path,'r').readlines()
  f2 = open(path,'w')
  f1.insert(line - 1, s)
  f2.write("".join(f1))
  f2.close()

def update_part(path, old, new):
  f1 = open(path,'r').read()
  f2 = open(path,'w')
  m = f1.replace(old, new)
  f2.write(m)
  f2.close()

insert_part("string.h", 5, "//@ #include <crypto.gh>\r\n")
insert_part("string.h", 7, "#define MINIMAL_STRING_SIZE 4\r\n\n")
update_part(
  "string.h",
  "    //@ requires chars(array, count, ?cs) &*& [?f]chars(array0, count, ?cs0);\r\n"
  "    //@ ensures chars(array, count, cs0) &*& [f]chars(array0, count, cs0);\r\n",
  "    /*@ requires chars(array, count, ?cs) &*&\r\n"
  "                 [?f]optional_crypto_chars(?cc, array0, count, ?cs0) &*&\r\n"
  "                 cc ? count >= MINIMAL_STRING_SIZE : true; @*/\r\n"
  "    /*@ ensures  optional_crypto_chars(cc, array, count, cs0) &*&\r\n"
  "                 [f]optional_crypto_chars(cc, array0, count, cs0); @*/\r\n"
)

update_part(
  "string.h",
  "    //@ requires [?f]chars(array, ?n, ?cs) &*& [?f0]chars(array0, ?n0, ?cs0) &*& "
       "count <= n &*& count <= n0;\r\n"
  "    //@ ensures [f]chars(array, n, cs) &*& [f0]chars(array0, n0, cs0) &*& "
       "true == ((result == 0) == (take(count, cs) == take(count, cs0)));\r\n",
  "    /*@ requires principal(?principal, ?values_count) &*&\r\n"
  "                 [?f1]optional_crypto_chars(?cc, array, ?n, ?cs) &*&\r\n"
  "                 [?f2]optional_crypto_chars(?cc0, array0, ?n0, ?cs0) &*& \r\n"
  "                 count <= n &*& count <= n0 &*&\r\n"
  "                 cc || cc0 ? count >= MINIMAL_STRING_SIZE : true; @*/\r\n"
  "    /*@ ensures  [f1]optional_crypto_chars(cc, array, n, cs) &*&\r\n"
  "                 [f2]optional_crypto_chars(cc0, array0, n0, cs0) &*&\r\n"
  "                 cc || cc0 ?\r\n"
  "                   (result == 0 ?\r\n"
  "                      principal(principal, values_count) &*&\r\n"
  "                      (take(count, cs) == take(count, cs0))\r\n"
  "                    : \r\n"
  "                      true\r\n"
  "                   )\r\n"
  "                 :\r\n"
  "                   principal(principal, values_count) &*&\r\n"
  "                   true == ((result == 0) == (take(count, cs) == take(count, cs0))); @*/\r\n"
)

insert_part("crt.dll.vfmanifest", 1,
  ".predicate @./crypto.gh#crypto_chars\r\n"
  ".predicate @./crypto.gh#optional_crypto_chars\r\n"
  ".predicate @./crypto.gh#principal\r\n"
)
