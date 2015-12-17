#ifndef ATTACKER_H
#define ATTACKER_H

#include "../general_definitions/general_definitions.h"

void attacker();
  /*@ requires [_]public_invar(?pub) &*&
               public_invariant_constraints(pub, ?proof_pred) &*&
               proof_pred() &*&
               principals(?count); @*/
  /*@ ensures  public_invariant_constraints(pub, proof_pred) &*&
               proof_pred() &*&
               principals(count + 1); @*/

#endif
