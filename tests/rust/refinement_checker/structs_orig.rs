struct Point { x: i32, y: i32 }

fn foo(p: Point) -> Point {
    Point { x: p.y, y: p.x }
}
