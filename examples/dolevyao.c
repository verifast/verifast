// Dolev-Yao security verification of a simple secure storage protocol
// Uses an invariant-based approach inspired by the work of Cohen and the work of Gordon et al.

struct item;

/*@

inductive item =
  | key_item(int creator, int id)
  | data_item(int id)
  | hmacsha1_item(int keyCreator, int id, item payload)
  | pair_item(item first, item second);

predicate item(struct item *item, item i);

predicate key(struct item *item, int creator, int id) = item(item, key_item(creator, id));

predicate world(fixpoint(item, bool) pub);

predicate principal(int id, int keyCount);

predicate principals(int count);

lemma void create_principal();
    requires principals(?count);
    ensures principals(count + 1) &*& principal(count, 0);

@*/

struct item *create_key();
    //@ requires principal(?principal, ?keyCount);
    //@ ensures principal(principal, keyCount + 1) &*& key(result, principal, keyCount);

void check_is_key(struct item *item);
    //@ requires item(item, ?i);
    /*@
    ensures
        switch (i) {
            case key_item(creator, id): return key(item, creator, id);
            case data_item(d): return false;
            case hmacsha1_item(c, id, p): return false;
            case pair_item(f, s): return false;
        };
    @*/

struct item *create_data_item(int data);
    //@ requires true;
    //@ ensures item(result, data_item(data));

struct item *hmacsha1(struct item *key, struct item *payload);
    //@ requires key(key, ?creator, ?id) &*& item(payload, ?p);
    //@ ensures key(key, creator, id) &*& item(payload, p) &*& item(result, hmacsha1_item(creator, id, p));

struct item *create_pair(struct item *hash, struct item *message);
    //@ requires item(hash, ?h) &*& item(message, ?m);
    //@ ensures item(hash, h) &*& item(message, m) &*& item(result, pair_item(h, m));

void net_send(struct item *datagram);
    //@ requires world(?pub) &*& item(datagram, ?d) &*& pub(d) == true;
    //@ ensures world(pub) &*& item(datagram, d);

struct item *net_receive();
    //@ requires world(?pub);
    //@ ensures world(pub) &*& item(result, ?d) &*& pub(d) == true;

struct item *pair_get_first(struct item *pair);
    //@ requires item(pair, ?p);
    /*@
    ensures
        item(pair, p) &*&
        switch (p) {
            case key_item(o, k): return false;
            case data_item(d): return false;
            case hmacsha1_item(creator, id, pl): return false;
            case pair_item(f, s): return item(result, f);
        };
    @*/

struct item *pair_get_second(struct item *pair);
    //@ requires item(pair, ?p);
    /*@
    ensures
        item(pair, p) &*&
        switch (p) {
            case key_item(o, k): return false;
            case data_item(d): return false;
            case hmacsha1_item(creator, id, pl): return false;
            case pair_item(f, s): return item(result, s);
        };
    @*/

void hmacsha1_verify(struct item *hash, struct item *key, struct item *payload);
    //@ requires item(hash, ?h) &*& key(key, ?creator, ?id) &*& item(payload, ?p);
    //@ ensures item(hash, h) &*& key(key, creator, id) &*& item(payload, p) &*& h == hmacsha1_item(creator, id, p);

void item_free(struct item *item);
    //@ requires item(item, _);
    //@ ensures true;

/*@

fixpoint bool bad(int principal);

fixpoint bool app_send_event(int sender, item message);

fixpoint bool mypub(item i) {
    switch (i) {
        case key_item(o, k): return bad(o);
        case data_item(d): return true;
        case hmacsha1_item(creator, id, m): return bad(creator) || app_send_event(creator, m);
        case pair_item(i1, i2): return mypub(i1) && mypub(i2);
    }
}

@*/

void app_send(struct item *key, struct item *message)
    //@ requires world(mypub) &*& key(key, ?creator, ?id) &*& item(message, ?msg) &*& mypub(msg) == true &*& app_send_event(creator, msg) == true;
    //@ ensures world(mypub) &*& key(key, creator, id) &*& item(message, msg);
{
    struct item *hash = hmacsha1(key, message);
    struct item *m = create_pair(hash, message);
    item_free(hash);
    net_send(m);
    item_free(m);
}

struct item *app_receive(struct item *key)
    //@ requires world(mypub) &*& key(key, ?creator, ?id);
    //@ ensures world(mypub) &*& key(key, creator, id) &*& item(result, ?msg) &*& bad(creator) || app_send_event(creator, msg);
{
    struct item *m = net_receive();
    struct item *hash = pair_get_first(m);
    struct item *message = pair_get_second(m);
    item_free(m);
    hmacsha1_verify(hash, key, message);
    item_free(hash);
    return message;
}

int choose();
    //@ requires true;
    //@ ensures true;

void attacker()
    //@ requires world(mypub) &*& principals(0);
    //@ ensures false;
{
    for (;;)
        //@ invariant world(mypub) &*& principals(?principalCount);
    {
        //@ create_principal();
        int action = choose();
        switch (action) {
            case 0:
                //@ assume(bad(principalCount));
                struct item *item = create_key();
                //@ open key(item, _, _);
                net_send(item);
                item_free(item);
                break;
            case 1:
                int data = choose();
                struct item *item = create_data_item(data);
                net_send(item);
                item_free(item);
                break;
            case 2:
                struct item *first = net_receive();
                struct item *second = net_receive();
                struct item *pair = create_pair(first, second);
                item_free(first);
                item_free(second);
                net_send(pair);
                item_free(pair);
                break;
            case 3:
                struct item *key = net_receive();
                struct item *payload = net_receive();
                check_is_key(key);
                struct item *hash = hmacsha1(key, payload);
                //@ open key(key, _, _);
                item_free(key);
                item_free(payload);
                net_send(hash);
                item_free(hash);
                break;
            case 4:
                struct item *pair = net_receive();
                struct item *first = pair_get_first(pair);
                struct item *second = pair_get_second(pair);
                item_free(pair);
                net_send(first);
                item_free(first);
                net_send(second);
                item_free(second);
                break;
        }
        //@ leak principal(_, _);
    }
}