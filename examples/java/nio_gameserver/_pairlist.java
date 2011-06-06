package gameserver;

import java.util.*;

/*@
lemma void fst_snd_equal_pair<t, u>(t key, u value, pair<t, u> val)
 requires fst(val) == key &*& snd(val) == value;
 ensures val == pair(key,value);
{
	switch(val) {
		case pair(a, b): a == key && b == value;
	}
}

lemma void mem_pair_in_map<t, u>(t key, u value, list<pair<t, u> > vals)
 requires mem(key, fst_list(vals)) == true  &*& value == in_map(key, vals);
 ensures mem(pair(key, value), vals) == true;
{
	switch (vals) {
		case nil:
		case cons(val0, vals0):
			if(fst(val0) == key && snd(val0) == value) {
				fst_snd_equal_pair(key, value, val0);		
			}
			else {
				mem_pair_in_map(key, value, vals0);		
			}
			
	}
}

lemma void mem_pair_split<t, u>(t key, u value, list<pair<t, u> > vals)
 requires mem(pair(key, value), vals) == true;
 ensures mem(key, fst_list(vals)) == true &*& mem(value, snd_list(vals)) == true;
{
	switch (vals) {
		case nil:
		case cons(val0, vals0):
			if(fst(val0) == key && snd(val0) == value) {
			}
			else {
				mem_pair_split(key, value, vals0);		
			}
	}
}

lemma void contains_key_to_mem<t, u>(boolean b, t key, list<pair<t, u> > vals)
requires contains_key(key, vals) == b;
ensures mem(key, fst_list(vals)) == b;
{
	switch (vals) {
		case nil:
		case cons(val0, vals0):
			if(fst(val0) == key) {							
			}
			else {
				contains_key_to_mem(b, key, vals0);
			}			
	}
}

lemma void remove_pair_from_list<t, u>(t key, u value, list<pair<t, u> > vals)
 requires mem(key, fst_list(vals)) == true &*& value == in_map(key, vals);
 ensures remove_pair(key, vals) == remove(pair(key, value), vals);
{
	switch (vals) {
		case nil:
		case cons(val0, vals0):
			if(fst(val0) == key && snd(val0) == value) {
				fst_snd_equal_pair(key, value, val0);		
			}
			else {
				remove_pair_from_list(key, value, vals0);		
			}
	}
}

lemma void mem_fst_list<t, u>(pair<t, u> key, list<pair<t, u> > keys)
    requires mem(key, keys) == true;
    ensures mem(fst(key), fst_list(keys)) == true;
{
	switch (keys) {
		case nil:
		case cons(key0, keys0):
		if(key0 == key) {
		}
		else {
			mem_fst_list(key, keys0);
		}	
	}
}

lemma void mem_snd_list<t, u>(pair<t, u> key, list<pair<t, u> > keys)
    requires mem(key, keys) == true;
    ensures mem(snd(key), snd_list(keys)) == true;
{
	switch (keys) {
		case nil:
		case cons(key0, keys0):
		if(key0 == key) {
		}
		else {
			mem_snd_list(key, keys0);
		}
			
	}
}

lemma void mem_fst_to_mem_snd<t, u>(t key, u value, list<pair<t, u> > vals)
requires mem(key, fst_list(vals)) == true &*& value == in_map(key, vals) ;
ensures mem(value, snd_list(vals)) == true;
{
	switch (vals) {
		case nil:
		case cons(val0, vals0):
			if(fst(val0) == key && snd(val0) == value) {

			}
			else {
				mem_fst_to_mem_snd(key, value, vals0);
			}
				
			
	}
}
@*/