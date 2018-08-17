#!/usr/bin/python

import re
import sys
import subprocess

name = "switch_primitives"
depth = 9

def write_to_file(macros):
  file = open(name + ".gh", "w+");
  guard = name.upper() + "_GH";
  file.write("#ifndef " + guard + "\n");
  file.write("#define " + guard + "\n");
  file.write("\n\n");
  file.write(macros);
  file.write("\n\n");
  file.write("#endif\n");
  file.close;

general_case = ("#define SWITCH_CRYPTO_PRIMITIVES(ITEM, DUMMY, DEPTH) \\\n"
                "  assert item(ITEM, ?item_##DUMMY, _) &*& \\\n"
                "  SWITCH_CRYPTO_PRIMITIVES_##DEPTH(item_##DUMMY) \\\n")

base_case = ("#define SWITCH_CRYPTO_PRIMITIVES_1(INDUCTIVE) \\\n"
             "  SWITCH_CRYPTO_PRIMITIVES_DOWN_I(INDUCTIVE, I, I) \\\n")

base_down_case = ("#define SWITCH_CRYPTO_PRIMITIVES_DOWN_I(INDUCTIVE, LEVEL, NESTED) \\\n"
                  "  switch (INDUCTIVE) \\\n"
                  "  { \\\n"
                  "    case data_item(d_dummy##LEVEL): return \\\n"
                  "      SWITCH_CRYPTO_PRIMITIVES_UP_##NESTED(INDUCTIVE); \\\n"
                  "    case pair_item(f_dummy##LEVEL, s_dummy##LEVEL): return \\\n"
                  "      SWITCH_CRYPTO_PRIMITIVES_UP_##NESTED(INDUCTIVE); \\\n"
                  "    case nonce_item(p_dummy##LEVEL, c_dummy##LEVEL, inc_dummy##LEVEL): return \\\n"
                  "      SWITCH_CRYPTO_PRIMITIVES_UP_##NESTED(INDUCTIVE); \\\n"
                  "    case hash_item(pay_dummy##LEVEL): return \\\n"
                  "      SWITCH_CRYPTO_PRIMITIVES_UP_##NESTED(INDUCTIVE); \\\n"                  
                  "    case symmetric_key_item(p_dummy##LEVEL, c_dummy##LEVEL): return \\\n"
                  "      SWITCH_CRYPTO_PRIMITIVES_UP_##NESTED(INDUCTIVE); \\\n"
                  "    case public_key_item(p_dummy##LEVEL, c_dummy##LEVEL): return \\\n"
                  "      SWITCH_CRYPTO_PRIMITIVES_UP_##NESTED(INDUCTIVE); \\\n"
                  "    case private_key_item(p_dummy##LEVEL, c_dummy##LEVEL): return \\\n"
                  "      SWITCH_CRYPTO_PRIMITIVES_UP_##NESTED(INDUCTIVE); \\\n"
                  "    case hmac_item(p_dummy##LEVEL, c_dummy##LEVEL, pay_dummy##LEVEL): return \\\n"
                  "      SWITCH_CRYPTO_PRIMITIVES_UP_##NESTED(INDUCTIVE); \\\n"
                  "    case symmetric_encrypted_item(p_dummy##LEVEL, c_dummy##LEVEL, pay_dummy##LEVEL, ent_dummy##LEVEL): return \\\n"
                  "      SWITCH_CRYPTO_PRIMITIVES_UP_##NESTED(INDUCTIVE); \\\n"
                  "    case asymmetric_encrypted_item(p_dummy##LEVEL, c_dummy##LEVEL, pay_dummy##LEVEL, ent_dummy##LEVEL): return \\\n"
                  "      SWITCH_CRYPTO_PRIMITIVES_UP_##NESTED(INDUCTIVE); \\\n"
                  "    case asymmetric_signature_item(p_dummy##LEVEL, c_dummy##LEVEL, pay_dummy##LEVEL, ent_dummy##LEVEL): return \\\n"
                  "      SWITCH_CRYPTO_PRIMITIVES_UP_##NESTED(INDUCTIVE); \\\n"
                  "  } \\\n")

base_up_case = ("#define SWITCH_CRYPTO_PRIMITIVES_UP_I(INDUCTIVE) \\\n"
                "  INDUCTIVE == INDUCTIVE \\\n")

generic_case = ("#define SWITCH_CRYPTO_PRIMITIVES___LNUM__(INDUCTIVE) \\\n"
                "  SWITCH_CRYPTO_PRIMITIVES_DOWN___NUM__(INDUCTIVE, I, I) \\\n")

generic_down_case = ("#define SWITCH_CRYPTO_PRIMITIVES_DOWN___NUM__(INDUCTIVE, LEVEL, NESTED) \\\n"
                     "  switch (INDUCTIVE) \\\n"
                     "  { \\\n"
                     "    case data_item(d_dummy##LEVEL): return \\\n"
                     "      SWITCH_CRYPTO_PRIMITIVES_UP_##NESTED(INDUCTIVE); \\\n"
                     "    case pair_item(first##NESTED, second##NESTED): return \\\n"
                     "      SWITCH_CRYPTO_PRIMITIVES_DOWN___PNUM__(second##NESTED, LEVEL ## I, NESTED ## I); \\\n"
                     "    case nonce_item(s_dummy##LEVEL, c_dummy##LEVEL, inc_dummy##LEVEL): return \\\n"
                     "      SWITCH_CRYPTO_PRIMITIVES_UP_##NESTED(INDUCTIVE); \\\n"
                     "    case hash_item(pay_dummy##LEVEL): return \\\n"
                     "      SWITCH_CRYPTO_PRIMITIVES_UP_##NESTED(INDUCTIVE); \\\n"                     
                     "    case symmetric_key_item(p_dummy##LEVEL, c_dummy##LEVEL): return \\\n"
                     "      SWITCH_CRYPTO_PRIMITIVES_UP_##NESTED(INDUCTIVE); \\\n"
                     "    case public_key_item(p_dummy##LEVEL, c_dummy##LEVEL): return \\\n"
                     "      SWITCH_CRYPTO_PRIMITIVES_UP_##NESTED(INDUCTIVE); \\\n"
                     "    case private_key_item(p_dummy##LEVEL, c_dummy##LEVEL): return \\\n"
                     "      SWITCH_CRYPTO_PRIMITIVES_UP_##NESTED(INDUCTIVE); \\\n"
                     "    case hmac_item(p_dummy##LEVEL, c_dummy##LEVEL, pay_dummy##LEVEL): return \\\n"
                     "      SWITCH_CRYPTO_PRIMITIVES_UP_##NESTED(INDUCTIVE); \\\n"
                     "    case symmetric_encrypted_item(p_dummy##LEVEL, c_dummy##LEVEL, pay_dummy##LEVEL, ent##LEVEL): return \\\n"
                     "      SWITCH_CRYPTO_PRIMITIVES_UP_##NESTED(INDUCTIVE); \\\n"
                     "    case asymmetric_encrypted_item(p_dummy##LEVEL, c_dummy##LEVEL, pay_dummy##LEVEL, ent##LEVEL): return \\\n"
                     "      SWITCH_CRYPTO_PRIMITIVES_UP_##NESTED(INDUCTIVE); \\\n"
                     "    case asymmetric_signature_item(p_dummy##LEVEL, c_dummy##LEVEL, pay_dummy##LEVEL, ent##LEVEL): return \\\n"
                     "      SWITCH_CRYPTO_PRIMITIVES_UP_##NESTED(INDUCTIVE); \\\n"
                     "  } \\\n")

generic_up_case = ("#define SWITCH_CRYPTO_PRIMITIVES_UP___NUM__(INDUCTIVE) \\\n"
                     "  switch (first__PNUM__) \\\n"
                     "  { \\\n"
                     "    case data_item(d_ddummy__NUM__): return \\\n"
                     "      SWITCH_CRYPTO_PRIMITIVES_UP___PNUM__(INDUCTIVE); \\\n"
                     "    case pair_item(f_ddummy__NUM__, s_ddummy__NUM__): return \\\n"
                     "      SWITCH_CRYPTO_PRIMITIVES_UP___PNUM__(INDUCTIVE); \\\n"
                     "    case nonce_item(s_ddummy__NUM__, c_ddummy__NUM__, inc_ddummy__NUM__): return \\\n"
                     "      SWITCH_CRYPTO_PRIMITIVES_UP___PNUM__(INDUCTIVE); \\\n"
                     "    case hash_item(pay_ddummy__NUM__): return \\\n"
                     "      SWITCH_CRYPTO_PRIMITIVES_UP___PNUM__(INDUCTIVE); \\\n"                     
                     "    case symmetric_key_item(p_ddummy__NUM__, c_ddummy__NUM__): return \\\n"
                     "      SWITCH_CRYPTO_PRIMITIVES_UP___PNUM__(INDUCTIVE); \\\n"
                     "    case public_key_item(p_ddummy__NUM__, c_ddummy__NUM__): return \\\n"
                     "      SWITCH_CRYPTO_PRIMITIVES_UP___PNUM__(INDUCTIVE); \\\n"
                     "    case private_key_item(p_ddummy__NUM__, c_ddummy__NUM__): return \\\n"
                     "      SWITCH_CRYPTO_PRIMITIVES_UP___PNUM__(INDUCTIVE); \\\n"
                     "    case hmac_item(pl_dummy___NUM__, cl_dummy___NUM__, pay_ddummy__NUM__): return \\\n"
                     "      SWITCH_CRYPTO_PRIMITIVES_UP___PNUM__(INDUCTIVE); \\\n"
                     "    case symmetric_encrypted_item(pl_dummy___NUM__, cl_dummy___NUM__, pay_ddummy__NUM__, ent__NUM__): return \\\n"
                     "      SWITCH_CRYPTO_PRIMITIVES_UP___PNUM__(INDUCTIVE); \\\n"
                     "    case asymmetric_encrypted_item(pl_dummy___NUM__, cl_dummy___NUM__, pay_ddummy__NUM__, ent__NUM__): return \\\n"
                     "      SWITCH_CRYPTO_PRIMITIVES_UP___PNUM__(INDUCTIVE); \\\n"
                     "    case asymmetric_signature_item(pl_dummy___NUM__, cl_dummy___NUM__, pay_ddummy__NUM__, ent__NUM__): return \\\n"
                     "      SWITCH_CRYPTO_PRIMITIVES_UP___PNUM__(INDUCTIVE); \\\n"
                     "  } \\\n")

def inductive_case(level):
  temp = generic_case
  temp = temp.replace("__LNUM__", str(level));
  temp = temp.replace("__NUM__", "I" * (level));
  return temp
def inductive_down_case(level):
  temp = generic_down_case
  temp = temp.replace("__NUM__", "I" * (level));
  temp = temp.replace("__PNUM__", "I" * (level - 1));
  return temp
def inductive_up_case(level):
  temp = generic_up_case
  temp = temp.replace("__NUM__", "I" * (level));
  temp = temp.replace("__PNUM__", "I" * (level - 1));
  return temp;

def create_macro_file():
  macros = general_case
  macros += "\n\n";
  macros += base_down_case;
  macros += "\n\n";
  macros += base_case;
  macros += "\n\n";
  macros += base_up_case;
  for i in range(depth):
    macros += "\n\n";
    macros += inductive_case(i + 2);
    macros += "\n\n";
    macros += inductive_down_case(i + 2);
    macros += "\n\n";
    macros += inductive_up_case(i + 2);
  write_to_file(macros);

create_macro_file();
