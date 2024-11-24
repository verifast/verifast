use std::alloc::{alloc, Layout, handle_alloc_error, dealloc};

unsafe fn assert(b: bool)
//@ req b;
//@ ens true;
{}

struct Point {
    x: i32,
    y: i32,
}

impl Point {

    unsafe fn new() -> Point
    //@ req true;
    //@ ens result == Point { x: 0, y: 0 };
    {
        return Point { x: 0, y: 0 };
    }
    
    unsafe fn init(point_ptr: *mut Point)
    //@ req *point_ptr |-> _;
    //@ ens *point_ptr |-> Point { x: 0, y: 0 };
    {
        (*point_ptr).x = 0;
        (*point_ptr).y = 0;
    }

    unsafe fn get_x(point_ptr: *mut Point) -> i32
    //@ req *point_ptr |-> ?point;
    //@ ens *point_ptr |-> point &*& result == point.x;
    {
        return (*point_ptr).x;
    }

    unsafe fn set_x(point_ptr: *mut Point, new_x: i32)
    //@ req *point_ptr |-> ?point;
    //@ ens *point_ptr |-> Point { x: new_x, y: point.y };
    {
        (*point_ptr).x = new_x;
    }
    
    unsafe fn drop_in_place(point_ptr: *mut Point)
    //@ req *point_ptr |-> ?_;
    //@ ens *point_ptr |-> _;
    {}

}

fn main1() {
    unsafe {
        let mut point = Point::new();
        Point::set_x(&raw mut point, 1000);
        assert(Point::get_x(&raw mut point) == 1000);
    }
}

fn main2() {
    unsafe {
        let point_ptr = alloc(Layout::new::<Point>()) as *mut Point;
        if point_ptr.is_null() {
            handle_alloc_error(Layout::new::<Point>());
        }
        //@ close_struct(point_ptr);
        Point::init(point_ptr);
        Point::set_x(point_ptr, 1000);
        assert(Point::get_x(point_ptr) == 1000);
        Point::drop_in_place(point_ptr);
        //@ open_struct(point_ptr);
        dealloc(point_ptr as *mut u8, Layout::new::<Point>());
    }
}

fn main() {
    main1();
    main2();
}
