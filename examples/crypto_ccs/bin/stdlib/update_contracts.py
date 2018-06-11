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

insert_part("stdlib.h", 6, "#include \"crypto.h\"\r\n")
insert_part("string.h", 6, "//@ #include \"crypto/memcmp.gh\"\r\n\r\n")

update_part(
  "string.h",
  "    //@ requires chars(arr, count, ?cs) &*& [?f]chars(arr0, count, ?cs0);\r\n"
  "    //@ ensures chars(arr, count, cs0) &*& [f]chars(arr0, count, cs0);\r\n",
  "    /*@ requires crypto_chars(_, arr, count, _) &*&\r\n"
  "                 [?f]crypto_chars(?kind, arr0, count, ?ccs0); @*/\r\n"
  "    /*@ ensures  crypto_chars(kind, arr, count, ccs0) &*&\r\n"
  "                 [f]crypto_chars(kind, arr0, count, ccs0); @*/\r\n"
)

update_part(
  "string.h",
  "    //@ requires [?f]chars(arr, ?n, ?cs) &*& [?f0]chars(arr0, ?n0, ?cs0) &*& "
       "count <= n &*& count <= n0;\r\n"
  "    //@ ensures [f]chars(arr, n, cs) &*& [f0]chars(arr0, n0, cs0) &*& "
       "(result == 0) == (take(count, cs) == take(count, cs0));\r\n",
  "    /*@ requires [?f1]crypto_chars(?kind1, arr, ?n1, ?ccs1) &*&\r\n"
  "                 [_]memcmp_region(?l1, take(count, ccs1)) &*& \r\n"
  "                 [?f2]crypto_chars(?kind2, arr0, ?n2, ?ccs2) &*& \r\n"
  "                 [_]memcmp_region(?l2, take(count, ccs2)) &*& \r\n"
  "                 memcmp_match(l1, l2) && count <= n1 && count <= n2; @*/\r\n"
  "    /*@ ensures  [f1]crypto_chars(kind1, arr, n1, ccs1) &*&\r\n"
  "                 [f2]crypto_chars(kind2, arr0, n2, ccs2) &*&\r\n"
  "                 true == ((result == 0) == (take(count, ccs1) == take(count, ccs2))); @*/\r\n"
)
