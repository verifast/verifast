#ifndef MSP430_H
#define MSP430_H


// The MSP430 is a single-address-space architecture. All code may access
// globals defined here at all times. Mechanisms such as disabling
// interrupts are used to ensure thread-safe operation.


int P1OUT_;

/*@
lemma void get_P1OUT_();
    requires true;
    ensures integer(&P1OUT_, _);

lemma void drop_P1OUT_();
    requires integer(&P1OUT_, _);
    ensures true;
  @*/

int WDTCTL_;


#define P1OUT  (P1OUT_)
#define WDTCTL (WDTCTL_)

#define WDTPW    0
#define WDTHOLD  0


#endif

