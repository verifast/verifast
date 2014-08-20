#ifndef TESTS_H
#define TESTS_H

#include <stdlib.h>
#include <stdio.h>

#include "../include/cryptolib.h"

struct score;
struct score* start_test();
void update_test(bool result, struct score *s);
void finish_test(char* name, struct score *s);

void test_nonce_items();
void test_key_items();
void test_data_items();
void test_hmac_items();
void test_pair_items();
void test_encrypted_items();
void test_networking();

#endif
