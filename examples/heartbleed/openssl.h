// This is not OpenSSL.
// Quick mockup; not a serious effort.
// Constants and specs are not sound w.r.t. the real OpenSSL codebase.

#ifndef OPENSSL_H
#define OPENSSL_H

unsigned int n2s_(unsigned char *p);
    //@ requires *p |-> ?v1 &*& *(p + 1) |-> ?v2;
    //@ ensures *p |-> v1 &*& *(p + 1) |-> v2 &*& result <= 0xffff;

void s2n_(unsigned char *p, unsigned int value);
    //@ requires *p |-> _ &*& *(p + 1) |-> _ &*& value <= 0xffff;
    //@ ensures  *p |-> ?v1 &*& *(p + 1) |-> ?v2;

#define n2s(p, x) { x = n2s_(p); p += 2; }
#define s2n(p, x) { s2n_(p, x); p += 2; }

struct rrec {
    unsigned char data[10000];
    unsigned int length;
};

struct SSL3 {
    struct rrec rrec;
};

struct SSL {
    struct SSL3 *s3;
};
typedef struct SSL SSL;

#define TLS1_HB_REQUEST 100
#define TLS1_HB_RESPONSE 101
#define TLS1_RT_HEARTBEAT 10

//@ predicate OPENSSL_malloc_block(unsigned char *p, unsigned int size);

unsigned char *OPENSSL_malloc(unsigned int size);
    //@ requires true;
    //@ ensures result[0..size] |-> _ &*& OPENSSL_malloc_block(result, size);

void OPENSSL_free(unsigned char *buffer);
    //@ requires OPENSSL_malloc_block(buffer, ?size) &*& buffer[..size] |-> _;
    //@ ensures true;

void memcpy(unsigned char *dest, unsigned char *src, unsigned size);
    //@ requires dest[..size] |-> _ &*& src[..size] |-> ?cs;
    //@ ensures dest[..size] |-> cs &*& src[..size] |-> cs;

void RAND_pseudo_bytes(unsigned char *buffer, unsigned size);
    //@ requires buffer[..size] |-> _;
    //@ ensures buffer[..size] |-> ?bytes;

int ssl3_write_bytes(SSL *s, int rt, unsigned char *buffer, unsigned size);
    //@ requires SSL(s) &*& buffer[..size] |-> ?cs;
    //@ ensures SSL(s) &*& buffer[..size] |-> cs;

//@ predicate SSL(SSL *s;) = s->s3 |-> ?s3 &*& s3->rrec.length |-> ?length &*& s3->rrec.data[0..10000] |-> ?data &*& length <= 10000;

#endif
