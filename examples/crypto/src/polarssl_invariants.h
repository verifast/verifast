#ifndef POLARSSL_INVARIANTS_H
#define POLARSSL_INVARIANTS_H

#include "general.h"
#include "item.h"
#include "serialization.h"

/*@

fixpoint bool polarssl_pub_core(fixpoint(item, bool) pub, item i, list<char> cs)
{
  return pub(i) && serialization_constraints(i, cs);
}

fixpoint fixpoint(item, list<char>, bool) polarssl_pub(fixpoint(item, bool) pub)
{
  return (polarssl_pub_core)(pub);
}

@*/

#endif
