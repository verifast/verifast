struct Point { x: i32, y: i32 }

fn foo(p: Point) -> Point {
    let y = p.y;
    let x = p.x;
    let r = Point { x, y };
    r
}
