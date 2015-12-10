
#define __SANCUS_SIM
//#define __SANCUS_LOAD

#include <msp430.h>
#include <stdio.h>
#include <stdlib.h>
#include <sancus/sm_support.h>

#ifdef __SANCUS_LOAD
#include <sancus_support/uart.h>
#endif

#include "uint_prelude.h"


typedef unsigned int nonce_data;

typedef unsigned int sensor_data;

struct ReaderOutput_s
{
  nonce_data nonce;
  sensor_data cipher;
  char tag[SANCUS_TAG_SIZE];
};

typedef struct ReaderOutput_s ReaderOutput;


void print_bytes(const void* bytes, size_t n)
/*@ requires [?f_bytes]chars(bytes, ?n_bytes, ?cs_bytes)
      &*& 1 <= n &*& n <= n_bytes &*& n <= INT_MAX;
  @*/
//@ ensures [f_bytes]chars(bytes, n_bytes, cs_bytes);
{
  int i = 0;
  for (i = 0; i < (int) n; i++)
  /*@ invariant [f_bytes]chars(bytes, n_bytes, cs_bytes)
        &*& 0 <= i &*& i <= n_bytes;
    @*/
  {
    printf("%x-", (unsigned int) (((char*)bytes)[i] & 0xff));
  }

  return;
}

void printf_wrapper_0 (unsigned int i)
/*@ requires true;
  @*/
/*@ ensures true;
  @*/
{
  printf("%u", i);
  putchar('\n');
}



/* ----- SM sensor ---------------------------------------------------- */

DECLARE_SM(sensor, 0x1234);

static sensor_data SM_DATA(sensor) sm_sensor_data = 42;

/*@
  predicate sm_sensor_pred()
    requires SancusModule_sm_tag(&sensor, 2)
    &*& u_integer(&sm_sensor_data, _);
  @*/

sensor_data SM_FUNC(sensor) read_sensor(void)
/*@ requires
          [?f]SancusModule_sm_tag(&sensor, ?sm_tag)
      &*& u_integer(&sm_sensor_data, _);
  @*/
/*@ ensures
          [f]SancusModule_sm_tag(&sensor, sm_tag)
      &*& u_integer(&sm_sensor_data, _);
  @*/
{

  // interaction with unprotected code
  printf_wrapper_0(sm_sensor_data); // valid: passed by value;
                                    // may be leaking confidential information

// ERROR:
//  printf("%u", sm_sensor_data);     // invalid: uses stack for paprameter
                                    // passing; detected at compile time

// ERROR:
//@ u_integer_to_chars(&sm_sensor_data);
//  print_bytes(&sm_sensor_data, sizeof(sensor_data)); // invalid: passes
                                    // reference; runtime error
//@ chars_to_u_integer(&sm_sensor_data);

  return(sm_sensor_data);
}

sensor_data SM_ENTRY(sensor) read_sensor_data(void)
/*@ requires
          lockset(currentThread, ?caller_locks)
      &*& [?f_sensor_lock]u_integer(&(sensor.lock), ?sensor_lock)
      &*& [f_sensor_lock]sancus_lock(&(sensor.lock), sensor_lock,
          sm_sensor_pred)
      &*& lock_below_top_x(sensor_lock, caller_locks) == true;
  @*/
/*@ ensures
          lockset(currentThread, caller_locks)
      &*& [f_sensor_lock]u_integer(&(sensor.lock), sensor_lock)
      &*& [f_sensor_lock]sancus_lock(&(sensor.lock), sensor_lock,
          sm_sensor_pred);
  @*/
{
//@ sancus_lock(&(sensor.lock));
//@ open sm_sensor_pred();
  return(read_sensor());
//@ close sm_sensor_pred();
//@ sancus_unlock(&(sensor.lock));
}


/* ----- SM reader ---------------------------------------------------- */

DECLARE_SM(reader, 0x1234);

/*@
  predicate sm_reader_pred()
    requires SancusModule_sm_tag(&reader, 1);
  @*/

void SM_ENTRY(reader) get_readings(ReaderOutput* out)
/*@ requires
          lockset(currentThread, nil)
      &*& [?f_reader_lock]u_integer(&(reader.lock), ?reader_lock)
      &*& [f_reader_lock]sancus_lock(&(reader.lock), reader_lock,
          sm_reader_pred)
      &*& [?f_sensor_lock]u_integer(&(sensor.lock), ?sensor_lock)
      &*& [f_sensor_lock]sancus_lock(&(sensor.lock), sensor_lock,
          sm_sensor_pred)
      &*& ReaderOutput_s_nonce(out, ?nonce)
      &*& ReaderOutput_s_cipher(out, ?cipher)
      &*& chars(out->tag, SANCUS_TAG_SIZE, _);
  @*/
/*@ ensures
          lockset(currentThread, nil)
      &*& [f_reader_lock]u_integer(&(reader.lock), reader_lock)
      &*& [f_reader_lock]sancus_lock(&(reader.lock), reader_lock,
          sm_reader_pred)
      &*& [f_sensor_lock]u_integer(&(sensor.lock), sensor_lock)
      &*& [f_sensor_lock]sancus_lock(&(sensor.lock), sensor_lock,
          sm_sensor_pred)
      &*& ReaderOutput_s_nonce(out, 0xbabe)
      &*& ReaderOutput_s_cipher(out, _)
      &*& chars(out->tag, SANCUS_TAG_SIZE, _);
  @*/
{
//@ sancus_lock(&(reader.lock));
//@ open sm_reader_pred();

// ERROR:
//  sm_sensor_data = 39; // fails; state of SM "sensor" is inaccessible.

// ERROR:
//  sensor_data reading = read_sensor(); // fails; "sensor" tag is inaccessible.

//@ assert (lockset(currentThread, ?locks));
//@ assert (lock_below_top_x(sensor_lock, locks) == true);
  sensor_data reading = read_sensor_data();

  out->nonce = 0xbabe;
//@ my_u_integer_to_chars(&out->nonce);
//@ my_u_integer_to_chars(&reading);
//@ chars_limits((void *) &reading);
//@ my_u_integer_to_chars(&out->cipher);
//@ assert(SancusModule_sm_tag(&reader, ?sm_tag));
//@ assert(sm_tag != 0);
  int res = sancus_wrap(&out->nonce, sizeof(nonce_data),
                        &reading, sizeof(sensor_data),
                        &out->cipher, out->tag);
//@ my_chars_to_u_integer(&out->nonce);
//@ my_chars_to_u_integer(&out->cipher);

  if (!res) {
    puts("Wrapping failed");
  }

//@ close sm_reader_pred();
//@ sancus_unlock(&(reader.lock));
  return;
}


/* ----- SM main ------------------------------------------------------ */

int main(int argc, char** argv)
/*@ requires
        module(example, true)
    &*& lockset(currentThread, nil);
  @*/
/*@ ensures
        lockset(currentThread, nil);
  @*/
{
//@ open_module();
//@ drop_P1OUT_();
//@ close (SancusState(0));
  ReaderOutput out;
  sm_id ret;

  WDTCTL = WDTPW | WDTHOLD;
#ifdef __SANCUS_LOAD
  uart_init();
#endif

  puts("main() started");

  sm_sensor_data = 41; // this works because protection is not yet enabled;

//@ int SM_DATA("sensor") sancus_sm_sensor_tag = 0;
  ret = sancus_enable(&reader);
  if (! ret) { puts("\n*** main() failed."); abort(); }
//@ assert (ProtectionDomain(&reader, ?sm_reader_id, 0x1234, _, _, _, _, _));
//@ assert (sm_reader_id == 1);
//@ assert (reader.lock == sm_reader_id);
//@ close sm_reader_pred();
//@ close create_lock_ghost_args(sm_reader_pred, nil, nil);
//@ sancus_sm_init(&(reader.lock), 0);

  sm_sensor_data = 40; // this works because protection is not yet enabled;

  ret = sancus_enable(&sensor);
  if (! ret) { puts("\n*** main() failed."); abort(); }
//@ assert (ProtectionDomain(&sensor, ?sm_sensor_id, 0x1234, _, _, _, _, _));
//@ assert (sm_sensor_id == 2);
//@ assert (sensor.lock == sm_sensor_id);
//@ close sm_sensor_pred();
//@ close create_lock_ghost_args(sm_sensor_pred, nil, nil);
//@ sancus_sm_init(&(sensor.lock), 0);

// ERROR:
//  sm_sensor_data = 39; // fails; protection is enabled.

  puts("Reading sensor");
  out.nonce = 0;
  get_readings(&out);

  printf("Nonce: ");
//@ u_integer_to_chars(&(out.nonce));
  print_bytes(&(out.nonce), sizeof(nonce_data));
//@ chars_to_u_integer(&(out.nonce));

  printf("\nCipher: ");
//@ u_integer_to_chars(&(out.cipher));
  print_bytes(&(out.cipher), sizeof(sensor_data));
//@ chars_to_u_integer(&(out.cipher));

  printf("\nTag: ");
  print_bytes(out.tag, SANCUS_TAG_SIZE);

  puts("\nmain() done");
  return(0);
//@ open (SancusState(_));
//@ leak integer(&WDTCTL, _);
//@ leak (ProtectionDomain(&reader, 1, 0x1234, _, _, _, _, _));
//@ leak (ProtectionDomain(&sensor, 2, 0x1234, _, _, _, _, _));
//@ leak sancus_lock(&(reader.lock), _, _);
//@ leak u_integer(&(reader.lock), _);
//@ leak sancus_lock(&(sensor.lock), _, _);
//@ leak u_integer(&(sensor.lock), _);
//@ leak struct_SancusModule_padding(&reader);
//@ leak struct_SancusModule_padding(&sensor);
}


int putchar(int c)
//@ requires true;
//@ ensures c == result || EOF == result;
{
#ifdef __SANCUS_SIM
//@ get_P1OUT_();
  P1OUT = c;
  P1OUT |= 0x80;
//@ drop_P1OUT_();
#endif
#ifdef __SANCUS_LOAD
  if (c == '\n') {
    uart2_write_byte('\r'); }
  uart2_write_byte(c);
#endif
  return(c);
}

