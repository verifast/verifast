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
insert_part("string.h", 37,
  "/*@\r\n"
  "predicate memcmp_secret(char* buffer, int count, list<char> cs, cryptogram cg) =\r\n"
  "  count == length(cs) && cs == chars_for_cg(cg) && cg_is_generated(cg) \r\n"
  ";\r\n"
  "@*/\r\n\n"
)

update_part(
  "string.h",
  "    //@ requires chars(arr, count, ?cs) &*& [?f]chars(arr0, count, ?cs0);\r\n"
  "    //@ ensures chars(arr, count, cs0) &*& [f]chars(arr0, count, cs0);\r\n",
  "    /*@ requires chars(arr, count, ?cs) &*&\r\n"
  "                 [?f]crypto_chars(?kind, arr0, count, ?cs0); @*/\r\n"
  "    /*@ ensures  crypto_chars(kind, arr, count, cs0) &*&\r\n"
  "                 [f]crypto_chars(kind, arr0, count, cs0); @*/\r\n"
)

update_part(
  "string.h",
  "    //@ requires [?f]chars(arr, ?n, ?cs) &*& [?f0]chars(arr0, ?n0, ?cs0) &*& "
       "count <= n &*& count <= n0;\r\n"
  "    //@ ensures [f]chars(arr, n, cs) &*& [f0]chars(arr0, n0, cs0) &*& "
       "true == ((result == 0) == (take(count, cs) == take(count, cs0)));\r\n",
  "    /*@ requires network_permission(?principal) &*& \r\n"
  "                 [?f1]crypto_chars(?kind1, arr, ?n1, ?cs1) &*&\r\n"
  "                   (kind1 == normal ? true : \r\n"
  "                      memcmp_secret(arr, count, cs1, _)) &*&\r\n"
  "                 [?f2]crypto_chars(?kind2, arr0, ?n2, ?cs2) &*& \r\n"
  "                   (kind2 == normal ? true : \r\n"
  "                      memcmp_secret(arr0, count, cs2, _)) &*&\r\n"
  "                 count <= n1 &*& count <= n2; @*/\r\n"
  "    /*@ ensures  [f1]crypto_chars(kind1, arr, n1, cs1) &*&\r\n"
  "                 [f2]crypto_chars(kind2, arr0, n2, cs2) &*&\r\n"
  "                 true == ((result == 0) == (take(count, cs1) == take(count, cs2))) &*&\r\n"
  "                 (\r\n"
  "                   //if guessing a secret value failed, network permissions are revoked\r\n"
  "                   // *otherwise one could keep guessing untill success\r\n"
  "                   result != 0 && (kind1 == secret || kind2 == secret) ?\r\n"
  "                       true : network_permission(principal)\r\n"
  "                 ); @*/\r\n"
)

insert_part("crt.dll.vfmanifest", 1,
  ".predicate @./crypto.gh#network_permission\r\n"
  ".predicate @./crypto.gh#crypto_chars\r\n"
  ".provides ./crypto.gh#crypto_chars_to_chars\r\n"
  ".provides ./crypto.gh#chars_to_crypto_chars\r\n"
  ".provides ./crypto.gh#chars_to_secret_crypto_chars\r\n"
  ".provides ./crypto.gh#crypto_chars_inv\r\n"
  ".provides ./crypto.gh#crypto_chars_limits\r\n"
  ".provides ./crypto.gh#crypto_chars_distinct\r\n"
  ".provides ./crypto.gh#crypto_chars_split\r\n"
  ".provides ./crypto.gh#crypto_chars_join\r\n"
)
