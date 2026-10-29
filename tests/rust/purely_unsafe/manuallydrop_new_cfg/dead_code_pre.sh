#!/bin/sh
# Native Windows mysh starts commands through cmd.exe; use explicit sh here.
verifast dead_code_pre.rs 2>&1
case_exit=$?
printf 'EXIT:%s\n' "$case_exit"
