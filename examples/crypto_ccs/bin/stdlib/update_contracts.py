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
  "predicate memcmp_secret(char* buffer, int count, list<crypto_char> ccs, cryptogram cg) =\r\n"
  "  count == length(ccs) && ccs == ccs_for_cg(cg) && cg_is_gen_or_pub(cg) \r\n"
  ";\r\n"
  "@*/\r\n\n"
)

update_part(
  "string.h",
  "    //@ requires chars(array, count, ?cs) &*& [?f]chars(array0, count, ?cs0);\r\n"
  "    //@ ensures chars(array, count, cs0) &*& [f]chars(array0, count, cs0);\r\n",
  "    /*@ requires chars(array, count, _) &*&\r\n"
  "                 [?f]crypto_chars(?kind, array0, count, ?ccs0); @*/\r\n"
  "    /*@ ensures  crypto_chars(kind, array, count, ccs0) &*&\r\n"
  "                 [f]crypto_chars(kind, array0, count, ccs0); @*/\r\n"
)

update_part(
  "string.h",
  "    //@ requires [?f]chars(array, ?n, ?cs) &*& [?f0]chars(array0, ?n0, ?cs0) &*& "
       "count <= n &*& count <= n0;\r\n"
  "    //@ ensures [f]chars(array, n, cs) &*& [f0]chars(array0, n0, cs0) &*& "
       "true == ((result == 0) == (take(count, cs) == take(count, cs0)));\r\n",
  "    /*@ requires network_permission(?principal) &*& \r\n"
  "                 [?f1]crypto_chars(?kind1, array, ?n1, ?ccs1) &*&\r\n"
  "                   (kind1 == normal ? true : \r\n"
  "                      memcmp_secret(array, count, ccs1, _)) &*&\r\n"
  "                 [?f2]crypto_chars(?kind2, array0, ?n2, ?ccs2) &*& \r\n"
  "                   (kind2 == normal ? true : \r\n"
  "                      memcmp_secret(array0, count, ccs2, _)) &*&\r\n"
  "                 count <= n1 &*& count <= n2; @*/\r\n"
  "    /*@ ensures  [f1]crypto_chars(kind1, array, n1, ccs1) &*&\r\n"
  "                 [f2]crypto_chars(kind2, array0, n2, ccs2) &*&\r\n"
  "                 true == ((result == 0) == (take(count, ccs1) == take(count, ccs2))) &*&\r\n"
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
