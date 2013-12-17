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
                "  assert item(ITEM, ?item_##DUMMY) &*& \\\n"
                "  SWITCH_CRYPTO_PRIMITIVES_##DEPTH(item_##DUMMY) \\\n")

base_case = ("#define SWITCH_CRYPTO_PRIMITIVES_1(INDUCTIVE) \\\n"
             "  SWITCH_CRYPTO_PRIMITIVES_DOWN_I(INDUCTIVE, I, I) \\\n")

base_down_case = ("#define SWITCH_CRYPTO_PRIMITIVES_DOWN_I(INDUCTIVE, LEVEL, NESTED) \\\n"
                  "  switch (INDUCTIVE) \\\n"
                  "  { \\\n"
                  "    case nonce_item(s_dummy##LEVEL, c_dummy##LEVEL, i_dummy##LEVEL): return \\\n"
                  "      SWITCH_CRYPTO_PRIMITIVES_UP_##NESTED(INDUCTIVE); \\\n"
                  "    case key_item(p_dummy##LEVEL, c_dummy##LEVEL, k_dummy##LEVEL, i_dummy##LEVEL): return \\\n"
                  "      SWITCH_CRYPTO_PRIMITIVES_UP_##NESTED(INDUCTIVE); \\\n"
                  "    case data_item(d_dummy##LEVEL): return \\\n"
                  "      SWITCH_CRYPTO_PRIMITIVES_UP_##NESTED(INDUCTIVE); \\\n"
                  "    case hmac_item(p_dummy##LEVEL, c_dummy##LEVEL, i_dummy##LEVEL, payload_dummy##LEVEL): return \\\n"
                  "      SWITCH_CRYPTO_PRIMITIVES_UP_##NESTED(INDUCTIVE); \\\n"
                  "    case encrypted_item(s_dummy##LEVEL, c_dummy##LEVEL, k_dummy##LEVEL, i_dummy##LEVEL, p_dummy##LEVEL, e_dummy##LEVEL): return \\\n"
                  "      SWITCH_CRYPTO_PRIMITIVES_UP_##NESTED(INDUCTIVE); \\\n"
                  "    case pair_item(first##NESTED, second##NESTED): return \\\n"
                  "      SWITCH_CRYPTO_PRIMITIVES_UP_##NESTED(INDUCTIVE); \\\n"
                  "  } \\\n")

base_up_case = ("#define SWITCH_CRYPTO_PRIMITIVES_UP_I(INDUCTIVE) \\\n"
                "  INDUCTIVE == INDUCTIVE \\\n")

generic_case = ("#define SWITCH_CRYPTO_PRIMITIVES___LNUM__(INDUCTIVE) \\\n"
                "  SWITCH_CRYPTO_PRIMITIVES_DOWN___NUM__(INDUCTIVE, I, I) \\\n")

generic_down_case = ("#define SWITCH_CRYPTO_PRIMITIVES_DOWN___NUM__(INDUCTIVE, LEVEL, NESTED) \\\n"
                     "  switch (INDUCTIVE) \\\n"
                     "  { \\\n"
                     "    case nonce_item(s_dummy##LEVEL, c_dummy##LEVEL, i_dummy##LEVEL): return \\\n"
                     "      SWITCH_CRYPTO_PRIMITIVES_UP_##NESTED(INDUCTIVE); \\\n"
                     "    case key_item(p_dummy##LEVEL, c_dummy##LEVEL, k_dummy##LEVEL, i_dummy##LEVEL): return \\\n"
                     "      SWITCH_CRYPTO_PRIMITIVES_UP_##NESTED(INDUCTIVE); \\\n"
                     "    case data_item(d_dummy##LEVEL): return \\\n"
                     "      SWITCH_CRYPTO_PRIMITIVES_UP_##NESTED(INDUCTIVE); \\\n"
                     "    case hmac_item(p_dummy##LEVEL, c_dummy##LEVEL, i_dummy##LEVEL, pay_dummy##LEVEL): return \\\n"
                     "      SWITCH_CRYPTO_PRIMITIVES_UP_##NESTED(INDUCTIVE); \\\n"
                     "    case encrypted_item(s_dummy##LEVEL, c_dummy##LEVEL, k_dummy##LEVEL, i_dummy##LEVEL, p_dummy##LEVEL, e_dummy##LEVEL): return \\\n"
                     "      SWITCH_CRYPTO_PRIMITIVES_DOWN___PNUM__(p_dummy##LEVEL, LEVEL ## I, NESTED); \\\n"
                     "    case pair_item(first##NESTED, second##NESTED): return \\\n"
                     "      SWITCH_CRYPTO_PRIMITIVES_DOWN___PNUM__(second##NESTED, LEVEL ## I, NESTED ## I); \\\n"
                     "  } \\\n")

generic_up_case = ("#define SWITCH_CRYPTO_PRIMITIVES_UP___NUM__(INDUCTIVE) \\\n"
                     "  switch (first__PNUM__) \\\n"
                     "  { \\\n"
                     "    case nonce_item(s_ddummy__NUM__, c_ddummy__NUM__, i_ddummy__NUM__): return \\\n"
                     "      SWITCH_CRYPTO_PRIMITIVES_UP___PNUM__(INDUCTIVE); \\\n"
                     "    case key_item(p_ddummy__NUM__, c_ddummy__NUM__, k_ddummy__NUM__, i_ddummy__NUM__): return \\\n"
                     "      SWITCH_CRYPTO_PRIMITIVES_UP___PNUM__(INDUCTIVE); \\\n"
                     "    case data_item(d_ddummy__NUM__): return \\\n"
                     "      SWITCH_CRYPTO_PRIMITIVES_UP___PNUM__(INDUCTIVE); \\\n"
                     "    case hmac_item(p_ddummy__NUM__, c_ddummy__NUM__, i_dummy___NUM__, pay_ddummy__NUM__): return \\\n"
                     "      SWITCH_CRYPTO_PRIMITIVES_UP___PNUM__(INDUCTIVE); \\\n"
                     "    case encrypted_item(s_ddummy__NUM__, c_ddummy__NUM__, k_ddummy__NUM__, i_ddummy__NUM__, p_ddummy__NUM__, e_ddummy__NUM__): return \\\n"
                     "      SWITCH_CRYPTO_PRIMITIVES_UP___PNUM__(INDUCTIVE); \\\n"
                     "    case pair_item(f_ddummy__NUM__, s_ddummy__NUM__): return \\\n"
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
