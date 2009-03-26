/*@
inductive a = a1;

inductive b = b1 | b2;

predicate absurd() =
    switch (b1) {
        case a1:  //~ should fail
            return
                switch (b2) {
                    case a1: return true;
                };
    };

@*/
