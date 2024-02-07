struct Point {
    x: i32,
    y: i32
}

struct Value {
    v: i32
}

/*@

fix flip(p: Point) -> Point {
    Point { x: p.y, y: p.x }
}

lem flip_def(x: i32, y: i32)
    req true;
    ens flip(Point { x, y }) == Point { x: y, y: x };
{
}

lem test_if_parse(Value: Value, v: i32)
    req true;
    ens true;
{
    if Value == Value {
    }
    let w = if Value == Value { v } else { 0 };
    assert Value { v } == Value { v: w };
}

@*/
