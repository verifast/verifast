#ifndef ATTACKER_H
#define ATTACKER_H

#include "../general_definitions/general_definitions.h"

#include <pthread.h>

void attacker();
  /*@ requires [_]public_invar(?pub) &*&
               [_]decryption_key_classifier(?classifier) &*&
               public_invariant_constraints(pub, ?proof_pred) &*&
               proof_pred() &*& principal(?bad_one, _) &*& true == bad(bad_one) &*&
               is_public_key_classifier(_, pub, classifier, proof_pred); @*/
  /*@ ensures  public_invariant_constraints(pub, proof_pred) &*&
               proof_pred() &*& principal(bad_one, _) &*&
               is_public_key_classifier(_, pub, classifier, proof_pred); @*/

#endif
