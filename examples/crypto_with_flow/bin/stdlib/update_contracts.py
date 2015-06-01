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

insert_part("malloc.h", 4, "//@ #include <crypto.gh>\r\n\r\n")
update_part(
  "malloc.h",
  "    //@ requires malloc_block(array, ?size) &*& chars(array, size, ?cs);\r\n"
  "    //@ ensures emp;\r\n",
  "    /*@ requires malloc_block(array, ?size) &*&\r\n"
  "                 optional_crypto_chars(_, array, size, ?cs); @*/\r\n"
  "    //@ ensures  emp;\r\n"
)

insert_part("string.h", 5, "//@ #include <crypto.gh>\r\n")
update_part(
  "string.h",
  "    //@ requires chars(array, count, ?cs) &*& [?f]chars(array0, count, ?cs0);\r\n"
  "    //@ ensures chars(array, count, cs0) &*& [f]chars(array0, count, cs0);\r\n",
  "    /*@ requires chars(array, count, ?cs) &*&\r\n"
  "                 [?f]optional_crypto_chars(?cc, array0, count, ?cs0); @*/\r\n"
  "    /*@ ensures  optional_crypto_chars(cc, array, count, cs0) &*&\r\n"
  "                 [f]optional_crypto_chars(cc, array0, count, cs0); @*/\r\n"
)

insert_part("string.h", 39, "//@ predicate memcpm_hmac(cryptogram cg) = true;\r\n\r\n\r\n")
update_part(
  "string.h",
  "    //@ requires [?f]chars(array, ?n, ?cs) &*& "
       "[?f0]chars(array0, ?n0, ?cs0) &*& n <= length(cs) &*& n0 <= length(cs0);\r\n"
  "    //@ ensures [f]chars(array, n, cs) &*& [f0]chars(array0, n0, cs0) &*& "
       "true == ((result == 0) == (take(count, cs) == take(count, cs0)));\r\n",
  "    /*@ requires [?f1]chars(array, ?n, ?cs) &*&\r\n"
  "                 [?f2]optional_crypto_chars(?cc, array0, ?n0, ?cs0) &*&\r\n"
  "                 n <= length(cs) &*& n0 <= length(cs0) &*&\r\n"
  "                 //only allowed for checking sha512 hmac\r\n"
  "                 cc ?\r\n"
  "                   memcpm_hmac(?hmac_cg) &*&\r\n"
  "                   n0 == n &*& (n0 == 48 || n0 == 64) &*&\r\n"
  "                   cs0 == chars_for_cg(hmac_cg) &*&\r\n"
  "                   hmac_cg == cg_hmac(?p, ?c, ?pay)\r\n"
  "                 :\r\n"
  "                   true; @*/\r\n"
  "    /*@ ensures  [f1]chars(array, n, cs) &*&\r\n"
  "                 [f2]optional_crypto_chars(cc, array0, n0, cs0) &*&\r\n"
  "                 true == ((result == 0) == (take(count, cs) == take(count, cs0))); @*/\r\n",
)

insert_part("crt.dll.vfmanifest", 1,
  ".predicate @./crypto.gh#crypto_chars\r\n"
  ".predicate @./crypto.gh#optional_crypto_chars\r\n"
)