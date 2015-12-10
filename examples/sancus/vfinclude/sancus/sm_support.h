#ifndef SM_SUPPORT_H
#define SM_SUPPORT_H

#include <stddef.h>

#include <threading.h> // VF header

typedef unsigned int sm_lock; //VF: Lock type

typedef unsigned int sm_id;
typedef unsigned int vendor_id;

struct SancusModule
{
  sm_id       id;
  vendor_id   vendor_id;
  const char* name;
  void*       public_start;
  void*       public_end;
  void*       secret_start;
  void*       secret_end;
  sm_lock     lock;   // VF: protection domain lock handle
  sm_id       sm_tag; // VF: a tag to be locked and to be passed on to SM_FUNCs
};

#define DECLARE_SM(name, vendor_id) \
  struct SancusModule name = {0, vendor_id, NULL, NULL, NULL, NULL, NULL, 0, 0}
 

#define SM_DATA(name)

#define SM_ENTRY(name)

#define SM_FUNC(name)


/*@

// This ensures that we do not reuse an /sm_id/.
  predicate SancusState(
    sm_id last_sm) =
    true;


// A ProtectionDomain essentially encapsulates a /SancusModule/ struct,
// exposing only the /lock/ as a handle for the lock/unlock mechanisms.
  predicate ProtectionDomain(
    struct SancusModule *sm,
    sm_id id, vendor_id vendor_id, const char* name,
    void* public_start, void* public_end,
    void* secret_start, void* secret_end) =
        sm->id           |-> id
    &*& sm->vendor_id    |-> vendor_id
    &*& sm->name         |-> name
    &*& sm->public_start |-> public_start
    &*& sm->public_end   |-> public_end
    &*& sm->secret_start |-> secret_start
    &*& sm->secret_end   |-> secret_end;


predicate sancus_lock(sm_id *lock; int lockId, predicate() p);


predicate sancus_lock_locked(sm_id *lock, int lockId, predicate() p, int threadId, real frac);


fixpoint bool lock_below_top_x(int l, list<int> ls) {
    switch (ls) {
        case nil: return true;
        case cons(l0, ls0): return lock_below_top_x(l, ls0);
    }
}


lemma void sancus_sm_init(sm_id *lock, int pshared);
 requires
        create_lock_ghost_args(?p, ?ls, ?us) &*& p()
    &*& lock_all_below_all(ls, us) == true &*& u_integer(lock, _)
    &*& pshared == 0;
 ensures
        sancus_lock(lock, ?lockId, p)
    &*& lock_above_all(lockId, ls) == true
    &*& lock_below_all(lockId, us) == true
    &*& u_integer(lock, lockId);


lemma void sancus_lock(sm_id *lock);
 requires
        [?f]sancus_lock(lock, ?lockId, ?p)
    &*& lockset(currentThread, ?locks)
    &*& lock_below_top_x(lockId, locks) == true;
 ensures
        sancus_lock_locked(lock, lockId, p, currentThread, f)
    &*& p() &*& lockset(currentThread, cons(lockId, locks));


lemma void sancus_unlock(sm_id *lock);
 requires
        sancus_lock_locked(lock, ?lockId, ?p, currentThread, ?f)
    &*& p() &*& lockset(currentThread, ?locks);
 ensures
        [f]sancus_lock(lock, lockId, p)
    &*& lockset(currentThread, remove(lockId, locks));

  @*/


sm_id sancus_enable(struct SancusModule* sm);
/*@ requires 
        SancusState(?last_sm)
    &*& SancusModule_id(sm, ?sm_id)
    &*& SancusModule_vendor_id(sm, ?sm_vendor_id)
    &*& SancusModule_name(sm, ?sm_name)
    &*& SancusModule_public_start(sm, ?sm_public_start)
    &*& SancusModule_public_end(sm, ?sm_public_end)
    &*& SancusModule_secret_start(sm, ?sm_secret_start)
    &*& SancusModule_secret_end(sm, ?sm_secret_end)
    &*& SancusModule_lock(sm, ?sm_lock)
    &*& SancusModule_sm_tag(sm, ?sm_tag);
  @*/
/*@ ensures 
    0 == result || last_sm > 2
      ? ( 0 == result
          &*& SancusState(last_sm)
          &*& SancusModule_id(sm, sm_id)
          &*& SancusModule_vendor_id(sm, sm_vendor_id)
          &*& SancusModule_name(sm, sm_name)
          &*& SancusModule_public_start(sm, sm_public_start)
          &*& SancusModule_public_end(sm, sm_public_end)
          &*& SancusModule_secret_start(sm, sm_secret_start)
          &*& SancusModule_secret_end(sm, sm_secret_end)
          &*& SancusModule_lock(sm, sm_lock)
          &*& SancusModule_sm_tag(sm, sm_tag))
      : ( 0 <= result
          &*& SancusState(last_sm + 1)
          &*& ProtectionDomain(sm, last_sm + 1, sm_vendor_id, sm_name,
                sm_public_start, sm_public_end,
                sm_secret_start, sm_secret_end)
          &*& SancusModule_lock(sm, last_sm + 1)
          &*& SancusModule_sm_tag(sm, last_sm + 1)
          &*& result == (last_sm + 1) );
  @*/


#define SANCUS_SECURITY 64
#define SANCUS_TAG_SIZE  8  // (SANCUS_SECURITY / 8)

int sancus_wrap(const void* ad, size_t ad_len,
                  const void* body, size_t body_len,
                  void* cipher, void* tag);
/*@ requires [?f_ad]chars(ad, ?n_ad, ?cs_ad)
      &*& 1 <= ad_len &*& ad_len <= n_ad &*& ad_len <= INT_MAX
      &*& [?f_body]chars(body, ?n_body, ?cs_body)
      &*& 1 <= body_len &*& body_len <= n_body &*& body_len <= INT_MAX
      &*& chars(cipher, ?n_cipher, _)
      &*& 1 <= n_cipher &*& body_len <= n_cipher &*& n_cipher <= INT_MAX
      &*& chars(tag, ?n_tag, _)
      &*& SANCUS_TAG_SIZE <= n_tag &*& n_tag <= INT_MAX
      &*& [?f_sm_tag]SancusModule_sm_tag(?sm_struct, ?sm_tag);
  @*/
/*@ ensures [f_ad]chars(ad, n_ad, cs_ad)
      &*& [f_body]chars(body, n_body, cs_body)
      &*& chars(cipher, n_cipher, _)
      &*& chars(tag, n_tag, _)
      &*& [f_sm_tag]SancusModule_sm_tag(sm_struct, sm_tag)
      &*& 0 == result || 1 == result;
  @*/


#endif

