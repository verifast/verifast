package gameserver;

import java.util.*;

/*@

lemma void list_not_null(int n, list<Object> xs)
	requires not_null(xs) == true && 0 <= n && n < length(xs);
	ensures nth(n, xs) != null;
{
	switch (xs) {
		case nil:
		case cons(x0, xs0):
			if (n == 0) {
			} else {
				list_not_null(n-1, xs0);
			}
	}
}
	
lemma void element_not_null(Object o, list<Object> xs)
	requires not_null(xs) == true &*& mem(o, xs) == true;
	ensures o != null;
{
	switch (xs) {
		case nil:
		case cons(x0, xs0):
			if (o == x0) {
			} else {
				element_not_null(o, xs0);
			}
	}
}
	
lemma_auto(remove_nth(i, xs)) void still_not_null_remove_nth(int i, list<Object> xs)
 requires not_null(xs) == true && 0 <= i && i < length(xs);
 ensures not_null(remove_nth(i, xs)) == true;
{
	switch (xs) {
		case nil:
		case cons(x0, xs0):
			if (i == 0) {
			} else {
				still_not_null_remove_nth(i-1, xs0);
			}
	}
}
 
lemma_auto(remove(o, xs)) void still_not_null_remove(Object o, list<Object> xs)
 requires not_null(xs) == true && mem(o, xs) == true;
 ensures not_null(remove(o, xs)) == true;
{
	switch (xs) {
		case nil:
		case cons(x0, xs0):
			if (o == x0) {
			} else {
				still_not_null_remove(o, xs0);
			}
	}
}

lemma_auto(append(xs, ys)) void still_not_null_append(list<Object> xs, list<Object> ys)
 requires not_null(xs) == true && not_null(ys) == true;
 ensures not_null(append(xs, ys)) == true;
{
	switch (xs) {
		case nil:
		case cons(x0, xs0):
			if (x0 == null) {
			} else {
				still_not_null_append(xs0, ys);
			}
	}
}

@*/