#include "hash_item.h"

#include "principal_ids.h"
#include "item_constraints.h"
#include "serialization.h"

/*@

#define HASH_ITEM_PAYLOAD_CG \
  OPEN_ITEM_CONSTRAINTS(i, ccs, pub); \
  assert [_]ic_parts(i)(?ccs_tag, ?ccs_cont); \
  assert [_]ic_cg(i)(?cg_ccs, ?cg); \
  assert ccs == append(ccs_tag, ccs_cont); \
  assert ccs_cont == ccs_for_cg(cg); \
  sublist_append(ccs_tag, ccs_for_cg(cg), nil); \
  return cg;

lemma cryptogram hash_item_payload_cg(item i)
  nonghost_callers_only
  requires [_]item_constraints(i, ?ccs, ?pub) &*&
           !col && item_with_entropy(i);
  ensures  cg_with_entropy(result) &&
           sublist(ccs_for_cg(result), ccs);
{
  switch(i)
  {
    case data_item(cs0):
      assert false;
    case pair_item(f0, s0):
      cryptogram cg;
      OPEN_ITEM_CONSTRAINTS(i, ccs, pub);
      assert [_]ic_parts(i)(?ccs_tag, ?ccs_cont);
      assert [_]ic_pair(i)(?ccs_f0, ?ccs_s0);
      list<crypto_char> fccs = cs_to_ccs(chars_of_unbounded_int(length(ccs_f0)));
      assert ccs_cont == append(fccs, append(ccs_f0, ccs_s0));
      if (item_with_entropy(f0))
      {
        cg = hash_item_payload_cg(f0);
        sublist_append(fccs, ccs_f0, ccs_s0);
        sublist_trans(ccs_for_cg(cg), ccs_f0, ccs_cont);
      }
      else
      {
        cg = hash_item_payload_cg(s0);
        sublist_append(append(fccs, ccs_f0), ccs_s0, nil);
        append_assoc(fccs, ccs_f0, append(ccs_s0, nil));
        sublist_trans(ccs_for_cg(cg), ccs_s0, ccs_cont);
      }
      assert true == sublist(ccs_for_cg(cg), ccs_cont);
      sublist_append(ccs_tag, ccs_cont, nil);
      sublist_trans(ccs_for_cg(cg), ccs_cont, ccs);
      return cg;
    case nonce_item(p0, c0, inc0):
      OPEN_ITEM_CONSTRAINTS(i, ccs, pub);
      assert [_]ic_parts(i)(?ccs_tag, ?ccs_cont);
      assert [_]ic_cg(i)(?cg_ccs, ?cg);
      append_assoc(ccs_tag, cons(c_to_cc(inc0), nil), append(cg_ccs, nil));
      sublist_append(append(ccs_tag, cons(c_to_cc(inc0), nil)), cg_ccs, nil);
      return cg;
    case hash_item(pay0):
      assert false;
    case symmetric_key_item(p0, c0):
      HASH_ITEM_PAYLOAD_CG
    case public_key_item(p0, c0):
      HASH_ITEM_PAYLOAD_CG
    case private_key_item(p0, c0):
      HASH_ITEM_PAYLOAD_CG
    case hmac_item(p0, c0, pay0):
      assert false;
    case symmetric_encrypted_item(p0, c0, pay0, ent0):
      OPEN_ITEM_CONSTRAINTS(i, ccs, pub);
      assert [_]ic_parts(i)(?ccs_tag, ?ccs_cont);
      assert [_]ic_cg(i)(?cg_ccs, ?cg);
      append_assoc(ccs_tag, take(GCM_IV_SIZE, ent0), append(cg_ccs, nil));
      sublist_append(append(ccs_tag, take(GCM_IV_SIZE, ent0)), cg_ccs, nil);
      return cg;
    case asymmetric_encrypted_item(p0, c0, pay0, ent0):
      HASH_ITEM_PAYLOAD_CG
    case asymmetric_signature_item(p0, c0, pay0, ent0):
      HASH_ITEM_PAYLOAD_CG
  }
}

lemma void hash_item_payload(item i)
  nonghost_callers_only
  requires [?f]world(?pub, ?key_clsfy) &*&
           [_]item_constraints(i, ?ccs, pub) &*&
           [_]hash_item_payload(pub, ?public, i);
  ensures  [f]world(pub, key_clsfy) &*&
           [_]hash_payload(_, ccs);
{
  retreive_proof_obligations();
  open [f]world(pub, key_clsfy);
  open [_]item_constraints(i, ccs, pub);
  open [_]hash_item_payload(pub, public, i);
  if (public || col)
  {
    if (col)
    {
      open [1]proof_obligations(pub);
      assert [1]is_public_collision(?proof, pub);
      proof(i);
      close proof_obligations(pub);
    }
    serialize_item(i);
    close hash_payload(true, ccs);
    leak hash_payload(true, ccs);
  }
  else
  {
    option<item> ii;
    switch(i)
    {
      case data_item(cs0):
        close hash_payload(true, ccs);
        leak hash_payload(true, ccs);
        close [f]world(pub, key_clsfy);
        leak proof_obligations(pub);
        return;
      case pair_item(f0, s0):
      case nonce_item(p0, c0, inc0):
      case hash_item(pay0):
      case symmetric_key_item(p0, c0):
      case public_key_item(p0, c0):
      case private_key_item(p0, c0):
      case hmac_item(p0, c0, pay0):
      case symmetric_encrypted_item(p0, c0, pay0, ent0):
      case asymmetric_encrypted_item(p0, c0, pay0, ent0):
      case asymmetric_signature_item(p0, c0, pay0, ent0):
    }

    cryptogram cg = hash_item_payload_cg(i);
    close exists(cg);
    leak exists(cg);
    close hash_payload(false, ccs);
    leak hash_payload(false, ccs);
  }
  close [f]world(pub, key_clsfy);
  leak proof_obligations(pub);
}

@*/

bool is_hash(struct item *item)
  //@ requires [?f]world(?pub, ?key_clsfy) &*& item(item, ?i, pub);
  /*@ ensures  [f]world(pub, key_clsfy) &*& item(item, i, pub) &*&
               result ? i == hash_item(_) : true; @*/
{
  //@ open [f]world(pub, key_clsfy);
  //@ open item(item, i, pub);
  //@ open [_]item_constraints(i, ?cs, pub);
  return item_tag(item->content, item->size) == TAG_HASH;
  //@ close item(item, i, pub);
  //@ close [f]world(pub, key_clsfy);
}

void check_is_hash(struct item *item)
  //@ requires [?f]world(?pub, ?key_clsfy) &*& item(item, ?i, pub);
  //@ ensures  [f]world(pub, key_clsfy) &*& item(item, i, pub) &*& i == hash_item(_);
{
  if (!is_hash(item))
    abort_crypto_lib("Presented item is not a hash");
}

struct item *create_hash(struct item *payload)
  /*@ requires [?f0]world(?pub, ?key_clsfy) &*&
               [?f1]item(payload, ?pay, pub) &*&
               [_]hash_item_payload(pub, _, pay); @*/
  /*@ ensures  [f0]world(pub, key_clsfy) &*&
               [f1]item(payload, pay, pub) &*& item(result, ?hash, pub) &*&
               col || hash == hash_item(some(pay)); @*/
{
  //@ open [f1]item(payload, pay, pub);
  //@ open [_]item_constraints(pay, ?pay_ccs, pub);
  //@ assert [f1]payload->content |-> ?p_cont &*& [f1]payload->size |-> ?p_size;
  struct item* hash = malloc(sizeof(struct item));
  if (hash == 0){abort_crypto_lib("malloc of item failed");}

  hash->size = TAG_LENGTH + HASH_SIZE;
  hash->content = malloc_wrapper(hash->size);
  write_tag(hash->content, TAG_HASH);

  if (payload->size < MINIMAL_STRING_SIZE)
    {abort_crypto_lib("Payload of hash was to small");}
  //@ hash_item_payload(pay);
  sha512(payload->content, (unsigned int) payload->size, hash->content + TAG_LENGTH, 0);

  //@ open [f0]world(pub, key_clsfy);
  //@ assert hash->content |-> ?cont &*& hash->size |-> ?size;
  //@ open cryptogram(cont + TAG_LENGTH, HASH_SIZE, ?ccs_cont, ?h_cg);
  //@ item h = hash_item(some(pay));
  //@ close ic_cg(h)(ccs_cont, h_cg);
  //@ close [f0]world(pub, key_clsfy);
  //@ close well_formed_item_ccs(h)(pay_ccs);
  //@ leak well_formed_item_ccs(h)(pay_ccs);
  //@ CLOSE_ITEM_CONSTRAINTS(cont, TAG_HASH, size, h)
  //@ close item(hash, h, pub);

  return hash;
  //@ close [f1]item(payload, pay, pub);
}
