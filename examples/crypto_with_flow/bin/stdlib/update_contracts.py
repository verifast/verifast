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
update_part(
  "string.h",
  "    //@ requires chars(array, count, ?cs) &*& [?f]chars(array0, count, ?cs0);\r\n"
  "    //@ ensures chars(array, count, cs0) &*& [f]chars(array0, count, cs0);\r\n",
  "    /*@ requires chars(array, count, ?cs) &*&\r\n"
  "                 [?f]crypto_chars(?kind, array0, count, ?cs0) &*&\r\n"
  "                 //minimum size prevents comparing sequence of same byte (see memcmp)\r\n"
  "                 //otherwise guessing would become easier complexity wise\r\n"
  "                 kind == normal || count >= MINIMAL_STRING_SIZE; @*/\r\n"
  "    /*@ ensures  crypto_chars(kind, array, count, cs0) &*&\r\n"
  "                 [f]crypto_chars(kind, array0, count, cs0); @*/\r\n"
)

update_part(
  "string.h",
  "    //@ requires [?f]chars(array, ?n, ?cs) &*& [?f0]chars(array0, ?n0, ?cs0) &*& "
       "count <= n &*& count <= n0;\r\n"
  "    //@ ensures [f]chars(array, n, cs) &*& [f0]chars(array0, n0, cs0) &*& "
       "true == ((result == 0) == (take(count, cs) == take(count, cs0)));\r\n",
  "    /*@ requires principal(?principal, ?values_count) &*&\r\n"
  "                 [?f1]crypto_chars(?kind1, array, ?n1, ?cs) &*&\r\n"
  "                 [?f2]crypto_chars(?kind2, array0, ?n2, ?cs0) &*& \r\n"
  "                 count <= n1 &*& count <= n2 &*& \r\n"
  "                 kind1 == normal && kind2 == normal ?\r\n"
  "                   true : count >= MINIMAL_STRING_SIZE; @*/\r\n"
  "    /*@ ensures  [f1]crypto_chars(?kind1_, array, n1, cs) &*&\r\n"
  "                 [f2]crypto_chars(?kind2_, array0, n2, cs0) &*&\r\n"
  "                 true == ((result == 0) == (take(count, cs) == take(count, cs0))) &*&\r\n"
  "                 (\r\n"
  "                   //if guessing a secret value failed, network permissions are revoked\r\n"
  "                   // *otherwise one could keep guessing untill success\r\n"
  "                   // *MINIMAL_STRING_SIZE ensures correct guess is unlikely\r\n"
  "                   result != 0 && (kind1 == secret || kind2 == secret) ?\r\n"
  "                       true : principal(principal, values_count)\r\n"
  "                 ) &*&\r\n"
  "                 result != 0 ? \r\n"
  "                   //if comparison failed kinds remain\r\n"
  "                   kind1_ == kind1 && kind2_ == kind2\r\n"
  "                 : \r\n"
  "                   //if comparison succeeded kinds become the same\r\n"
  "                   kind1_ == kind2_ &*&\r\n"
  "                   //the resulting kind follows the rules of memcmp_kinds\r\n"
  "                   kind1_ == memcmp_kinds(kind1, n1, kind2, n2) &*&\r\n"
  "                   //comparing a garbage value successfully to a non-garbage value results in a collision\r\n"
  "                   kind1 == kind2 || (kind1 != garbage && kind2 != garbage) || col; @*/\r\n"
)

insert_part("crt.dll.vfmanifest", 1,
  ".predicate @./crypto.gh#principal\r\n"
  ".predicate @./crypto.gh#crypto_chars\r\n"
  ".provides ./crypto.gh#crypto_chars_to_chars\r\n"
  ".provides ./crypto.gh#chars_to_crypto_chars\r\n"
  ".provides ./crypto.gh#chars_to_secret_crypto_chars\r\n"
  ".provides ./crypto.gh#crypto_chars_inv\r\n"
  ".provides ./crypto.gh#crypto_chars_limits\r\n"
  ".provides ./crypto.gh#crypto_chars_split\r\n"
  ".provides ./crypto.gh#crypto_chars_join\r\n"
)
