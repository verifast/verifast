#ifndef ZEROIZE_H
#define ZEROIZE_H

//@ #include "crypto_chars.gh"

void zeroize(char *buffer, int size);
  //@ requires crypto_chars(_, buffer, size, _);
  //@ ensures  chars(buffer, size, _);

#endif
