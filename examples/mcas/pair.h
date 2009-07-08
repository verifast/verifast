#ifndef PAIR_H
#define PAIR_H

/*@

inductive pair<a, b> = pair(a, b);

fixpoint a fst<a, b>(pair<a, b> p) {
    switch (p) {
        case pair(x, y): return x;
    }
}

fixpoint b snd<a, b>(pair<a, b> p) {
    switch (p) {
        case pair(x, y): return y;
    }
}

@*/

#endif