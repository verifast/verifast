#ifndef ATTACKER_H
#define ATTACKER_H

//@ #include "../general_definitions/general_definitions.gh"

void attacker();
  /*@ requires [_]public_invar(?pub) &*&
               public_invariant_constraints(pub, ?proof_pred) &*& 
               proof_pred() &*&
               principals(?count1); @*/
  /*@ ensures  public_invariant_constraints(pub, proof_pred) &*& 
               proof_pred() &*&
               principals(?count2) &*& count2 > count1; @*/

#endif
