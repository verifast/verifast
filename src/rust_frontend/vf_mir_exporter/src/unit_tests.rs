use super::*;
use std::panic::{self, AssertUnwindSafe};

#[test]
fn test_src_pos_basic() {
    let dummy1 = SrcPos { line: -1, column: 1, byte_pos: 0 };
    assert!(dummy1.is_dummy());
    let dummy2 = SrcPos { line: 1, column: -1, byte_pos: 0 };
    assert!(dummy2.is_dummy());
    let normal = SrcPos { line: 10, column: 5, byte_pos: 42 };
    assert!(!normal.is_dummy());
    assert_eq!(normal.line, 10);
    assert_eq!(normal.column, 5);
    assert_eq!(normal.byte_pos, 42);

    // Clone, Copy, Debug
    let copied = normal;
    assert_eq!(copied.line, 10);
    let debug_str = format!("{:?}", normal);
    assert!(debug_str.contains("SrcPos"));
}

#[test]
fn test_preprocess_empty_input() {
    let mut directives = Vec::new();
    let mut ghost_ranges = Vec::new();

    // read_only = true
    let out_ro = preprocess("", true, &mut directives, &mut ghost_ranges);
    assert_eq!(out_ro, "");
    assert!(directives.is_empty());
    assert!(ghost_ranges.is_empty());

    // read_only = false (appends synthetic definitions)
    let out_rw = preprocess("", false, &mut directives, &mut ghost_ranges);
    assert!(out_rw.contains("const fn VeriFast_ghost_command()"));
    assert!(out_rw.contains("fn VeriFast_alloc<T>()"));
    assert!(out_rw.contains("fn VF_free<T>"));
}

#[test]
fn test_preprocess_plain_rust() {
    let code = "fn add(a: i32, b: i32) -> i32 {\n    a + b\n}\n";
    let mut directives = Vec::new();
    let mut ghost_ranges = Vec::new();

    let out = preprocess(code, true, &mut directives, &mut ghost_ranges);
    assert!(out.contains("fn add(a: i32, b: i32)"));
    assert!(directives.is_empty());
    assert!(ghost_ranges.is_empty());
}

#[test]
fn test_preprocess_single_line_ghost() {
    let code = "fn foo() {\n    let x = 1;\n    //@ assert x > 0;\n    //@ assert true;\n}\n";
    let mut directives = Vec::new();
    let mut ghost_ranges = Vec::new();

    let out = preprocess(code, true, &mut directives, &mut ghost_ranges);
    assert_eq!(ghost_ranges.len(), 2);
    assert!(directives.is_empty());

    assert_eq!(ghost_ranges[0].contents(), "//@ assert x > 0;");
    assert_eq!(ghost_ranges[0].start_pos().line, 3);
    assert_eq!(ghost_ranges[0].kind, GhostRangeKind::Regular);

    assert_eq!(ghost_ranges[1].contents(), "//@ assert true;");
    assert_eq!(ghost_ranges[1].start_pos().line, 4);
}

#[test]
fn test_preprocess_multiline_ghost() {
    let code = "/*@\nreq true;\nens true;\n@*/\nfn bar() {}\n";
    let mut directives = Vec::new();
    let mut ghost_ranges = Vec::new();

    let out = preprocess(code, true, &mut directives, &mut ghost_ranges);
    assert_eq!(ghost_ranges.len(), 1);
    assert!(directives.is_empty());

    let gr = &ghost_ranges[0];
    assert!(gr.contents().starts_with("/*@"));
    assert!(gr.contents().ends_with("@*/"));
    assert_eq!(gr.start_pos().line, 1);
    assert_eq!(gr.kind, GhostRangeKind::Regular);
}

#[test]
fn test_preprocess_ghost_block_kinds() {
    // BlockDecls: pred
    let code_pred = "fn test() {\n    /*@ pred p(); @*/\n}\n";
    let mut dirs = Vec::new();
    let mut grs = Vec::new();
    preprocess(code_pred, true, &mut dirs, &mut grs);
    assert_eq!(grs.len(), 1);
    assert_eq!(grs[0].kind, GhostRangeKind::BlockDecls);

    // BlockDecls: lem
    let code_lem = "fn test() {\n    /*@ lem my_lem(); @*/\n}\n";
    let mut dirs = Vec::new();
    let mut grs = Vec::new();
    preprocess(code_lem, true, &mut dirs, &mut grs);
    assert_eq!(grs.len(), 1);
    assert_eq!(grs[0].kind, GhostRangeKind::BlockDecls);

    // BlockDecls: lem_auto
    let code_lema = "fn test() {\n    /*@ lem_auto my_lem(); @*/\n}\n";
    let mut dirs = Vec::new();
    let mut grs = Vec::new();
    preprocess(code_lema, true, &mut dirs, &mut grs);
    assert_eq!(grs.len(), 1);
    assert_eq!(grs[0].kind, GhostRangeKind::BlockDecls);

    // BlockDecls: let_lft
    let code_lft = "fn test() {\n    /*@ let_lft 'a; @*/\n}\n";
    let mut dirs = Vec::new();
    let mut grs = Vec::new();
    preprocess(code_lft, true, &mut dirs, &mut grs);
    assert_eq!(grs.len(), 1);
    assert_eq!(grs[0].kind, GhostRangeKind::BlockDecls);

    // LoopSpec: req
    let code_loop = "fn test() {\n    while true {\n        /*@ req true; @*/\n    }\n}\n";
    let mut dirs = Vec::new();
    let mut grs = Vec::new();
    preprocess(code_loop, true, &mut dirs, &mut grs);
    assert_eq!(grs.len(), 1);
    assert_eq!(grs[0].kind, GhostRangeKind::LoopSpec);

    // Mut: /*@~mut@*/
    let code_mut = "fn test() { let x = /*@~mut@*/ 5; }\n";
    let mut dirs = Vec::new();
    let mut grs = Vec::new();
    preprocess(code_mut, true, &mut dirs, &mut grs);
    assert_eq!(grs.len(), 1);
    assert_eq!(grs[0].kind, GhostRangeKind::Mut);

    // GenericArgs: /*@: ... @*/
    let code_gen = "fn test() { foo::<i32 /*@: 'a @*/>(); }\n";
    let mut dirs = Vec::new();
    let mut grs = Vec::new();
    preprocess(code_gen, true, &mut dirs, &mut grs);
    assert_eq!(grs.len(), 1);
    assert_eq!(grs[0].kind, GhostRangeKind::GenericArgs);
}

#[test]
fn test_preprocess_directives() {
    let code = "//~should_fail\n//~ERROR\nfn bad() {}\n";
    let mut directives = Vec::new();
    let mut ghost_ranges = Vec::new();

    let out = preprocess(code, true, &mut directives, &mut ghost_ranges);
    assert!(ghost_ranges.is_empty());
    assert_eq!(directives.len(), 2);
    assert_eq!(directives[0].contents(), "should_fail");
    assert_eq!(directives[1].contents(), "ERROR");
}

#[test]
fn test_preprocess_strings_and_chars_isolate_ghosts() {
    let code = r#"
fn test_str() {
    let s1 = "//@ req false;";
    let s2 = "/*@ ens false; @*/";
    let s3 = "escaped \" //@ not ghost \"";
    let c1 = '/';
    let c2 = '@';
}
"#;
    let mut directives = Vec::new();
    let mut ghost_ranges = Vec::new();

    let out = preprocess(code, true, &mut directives, &mut ghost_ranges);
    assert!(directives.is_empty());
    assert!(ghost_ranges.is_empty());
    assert!(out.contains(r#"let s1 = "//@ req false;";"#));
    assert!(out.contains(r#"let s2 = "/*@ ens false; @*/";"#));
}

#[test]
fn test_preprocess_nested_comments() {
    let code = "/* outer comment /* nested inner */ still outer */\nfn f() {}\n";
    let mut dirs = Vec::new();
    let mut grs = Vec::new();

    let out = preprocess(code, true, &mut dirs, &mut grs);
    assert!(dirs.is_empty());
    assert!(grs.is_empty());

    // Ghost annotation inside normal multiline comment is NOT active
    let code_ghost_in_comment = "/* /*@ req true; @*/ */\nfn g() {}\n";
    preprocess(code_ghost_in_comment, true, &mut dirs, &mut grs);
    assert!(dirs.is_empty());
    assert!(grs.is_empty());
}

#[test]
fn test_preprocess_crlf_normalization() {
    let code = "fn foo() {\r\n    //@ req true;\r\n    return;\r\n}\r\n";
    let mut dirs = Vec::new();
    let mut grs = Vec::new();

    let out = preprocess(code, true, &mut dirs, &mut grs);
    assert_eq!(grs.len(), 1);
    assert_eq!(grs[0].start_pos().line, 2);
    assert_eq!(grs[0].contents(), "//@ req true;");
}

#[test]
fn test_preprocess_bom_handling() {
    let code = "\u{feff}fn main() {\n    //@ req true;\n}\n";
    let mut dirs = Vec::new();
    let mut grs = Vec::new();

    let out = preprocess(code, true, &mut dirs, &mut grs);
    assert_eq!(grs.len(), 1);
    assert_eq!(grs[0].start_pos().line, 2);
    assert_eq!(grs[0].contents(), "//@ req true;");
}

#[test]
fn test_preprocess_synthetic_first_tokens() {
    // When ghost range is at the very beginning of the file and read_only is false,
    // synthetic first tokens are prepended
    let code = "//@ req true;\nfn f() {}\n";
    let mut dirs = Vec::new();
    let mut grs = Vec::new();

    let out = preprocess(code, false, &mut dirs, &mut grs);
    assert!(out.contains(VF_SYNTHETIC_FIRST_TOKENS));
}

#[test]
fn test_preprocess_synthetic_ghost_cmd_in_body() {
    // Inside function body, ghost commands insert VeriFast_ghost_command();
    let code = "fn f() {\n    /*@ assert true; @*/\n}\n";
    let mut dirs = Vec::new();
    let mut grs = Vec::new();

    let out = preprocess(code, false, &mut dirs, &mut grs);
    assert!(out.contains(VF_GHOST_CMD_TAG));
}

#[test]
fn test_unclosed_multiline_comment_panic() {
    let result = panic::catch_unwind(AssertUnwindSafe(|| {
        let mut dirs = Vec::new();
        let mut grs = Vec::new();
        preprocess("/* unclosed comment without end", true, &mut dirs, &mut grs);
    }));
    assert!(result.is_err(), "Expected panic on unclosed multiline comment");
}

#[test]
fn test_unclosed_string_panic() {
    let result = panic::catch_unwind(AssertUnwindSafe(|| {
        let mut dirs = Vec::new();
        let mut grs = Vec::new();
        preprocess("let s = \"unclosed string without end;", true, &mut dirs, &mut grs);
    }));
    assert!(result.is_err(), "Expected panic on unclosed string");
}

#[test]
fn test_unclosed_char_panic() {
    let result = panic::catch_unwind(AssertUnwindSafe(|| {
        let mut dirs = Vec::new();
        let mut grs = Vec::new();
        preprocess("let c = '", true, &mut dirs, &mut grs);
    }));
    assert!(result.is_err(), "Expected panic on unclosed char literal");
}

#[test]
fn test_unclosed_block_panic() {
    let result = panic::catch_unwind(AssertUnwindSafe(|| {
        let mut dirs = Vec::new();
        let mut grs = Vec::new();
        // Block starting with ghost decls but never closed
        preprocess("fn f() {\n    /*@ pred p(); @*/\n", true, &mut dirs, &mut grs);
    }));
    assert!(result.is_err(), "Expected panic on unclosed block with ghost decls");
}

#[test]
fn test_text_iterator_eof_next() {
    let mut it = TextIterator {
        chars: "".chars().peekable(),
        src_pos: 0,
        pos: SrcPos { line: 1, column: 1, byte_pos: 0 },
        last_char_was_cr: false,
    };
    assert_eq!(it.peek(), None);
    assert_eq!(it.next(), None);
}

#[test]
fn test_dummy_ghost_range_set_span() {
    let mut gr = GhostRange {
        in_fn_body: false,
        kind: GhostRangeKind::Regular,
        block_end: None,
        end_of_preceding_token: SrcPos { line: 0, column: 0, byte_pos: 0 },
        start: SrcPos { line: -1, column: -1, byte_pos: 0 },
        end: SrcPos { line: -1, column: -1, byte_pos: 0 },
        contents: String::new(),
        span: None,
    };
    assert!(gr.is_dummy());
    gr.set_span(rustc_span::BytePos(10));
    assert_eq!(gr.span(), None);
}

#[test]
fn test_ghost_range_block_end_span() {
    use rustc_span::{BytePos, Span, SyntaxContext};
    let gr = GhostRange {
        in_fn_body: false,
        kind: GhostRangeKind::BlockDecls,
        block_end: Some(SrcPos { line: 2, column: 5, byte_pos: 20 }),
        end_of_preceding_token: SrcPos { line: 1, column: 1, byte_pos: 0 },
        start: SrcPos { line: 1, column: 1, byte_pos: 0 },
        end: SrcPos { line: 1, column: 10, byte_pos: 10 },
        contents: "/*@ pred p(); @*/".to_string(),
        span: Some(Span::new(BytePos(100), BytePos(110), SyntaxContext::root(), None)),
    };
    let span = gr.block_end_span();
    assert_eq!(span.lo(), BytePos(120));
    assert_eq!(span.hi(), BytePos(121));
}

#[test]
fn test_preprocess_comment_immediately_following_token() {
    let code = "let x=1;//@ req true;\nlet y=2;// normal comment\nlet z=3;/*@ req true; @*/\nlet w=4;/* normal multiline */\n";
    let mut dirs = Vec::new();
    let mut grs = Vec::new();
    let _out = preprocess(code, true, &mut dirs, &mut grs);
    assert_eq!(grs.len(), 2);
}

#[test]
fn test_preprocess_eof_without_newline() {
    let mut dirs = Vec::new();
    let mut grs = Vec::new();
    preprocess("//@ req true", true, &mut dirs, &mut grs);
    assert_eq!(grs.len(), 1);

    let mut dirs2 = Vec::new();
    let mut grs2 = Vec::new();
    preprocess("//~should_fail", true, &mut dirs2, &mut grs2);
    assert_eq!(dirs2.len(), 1);

    let mut dirs3 = Vec::new();
    let mut grs3 = Vec::new();
    preprocess("// normal comment at EOF", true, &mut dirs3, &mut grs3);
    assert!(grs3.is_empty());
}

#[test]
fn test_preprocess_multiline_ghost_eof_panics() {
    let res1 = panic::catch_unwind(AssertUnwindSafe(|| {
        let mut dirs = Vec::new();
        let mut grs = Vec::new();
        preprocess("/*@ ghost *", true, &mut dirs, &mut grs);
    }));
    assert!(res1.is_err());

    let res2 = panic::catch_unwind(AssertUnwindSafe(|| {
        let mut dirs = Vec::new();
        let mut grs = Vec::new();
        preprocess("/*@ ghost /", true, &mut dirs, &mut grs);
    }));
    assert!(res2.is_err());
}

#[test]
fn test_preprocess_escape_eof_panics() {
    let res1 = panic::catch_unwind(AssertUnwindSafe(|| {
        let mut dirs = Vec::new();
        let mut grs = Vec::new();
        preprocess("let c = '\\", true, &mut dirs, &mut grs);
    }));
    assert!(res1.is_err());

    let res2 = panic::catch_unwind(AssertUnwindSafe(|| {
        let mut dirs = Vec::new();
        let mut grs = Vec::new();
        preprocess("let s = \"\\", true, &mut dirs, &mut grs);
    }));
    assert!(res2.is_err());
}

#[test]
fn test_preprocess_raw_strings() {
    let mut dirs = Vec::new();
    let mut grs = Vec::new();

    let out1 = preprocess("let r = r\"simple raw string\";", true, &mut dirs, &mut grs);
    assert!(out1.contains("simple raw string"));

    let out2 = preprocess("let r = r#\"raw \"with\" quotes\"#;", true, &mut dirs, &mut grs);
    assert!(out2.contains("with"));

    let out3 = preprocess("let r = r##\"embedded # and \"# inside\"##;", true, &mut dirs, &mut grs);
    assert!(out3.contains("embedded"));

    let out4 = preprocess("let red = 42; fn run() {}", true, &mut dirs, &mut grs);
    assert!(out4.contains("let red = 42;"));

    let res = panic::catch_unwind(AssertUnwindSafe(|| {
        let mut dirs = Vec::new();
        let mut grs = Vec::new();
        preprocess("let r = r#\"unclosed raw string", true, &mut dirs, &mut grs);
    }));
    assert!(res.is_err());
}

#[test]
fn test_preprocess_alloc_dealloc_edge_cases() {
    let mut dirs = Vec::new();
    let mut grs = Vec::new();

    let out1 = preprocess("let p = alloc(Layout::new::<i32>()) as *mut u8;\n", true, &mut dirs, &mut grs);
    assert!(out1.contains("alloc(Layout::new::<i32>()) as *mut u8"));

    let out2 = preprocess("dealloc(p as *mut u8, Layout::new::<i32>()\n", true, &mut dirs, &mut grs);
    assert!(out2.contains("dealloc"));
}

fn find_exporter_binary() -> std::path::PathBuf {
    let p = std::path::PathBuf::from("/home/devin/verifast-src/bin/vf-rust-mir-exporter");
    if p.exists() {
        p
    } else {
        std::path::PathBuf::from(std::env::var("CARGO_BIN_EXE_vf_mir_exporter").unwrap_or_else(|_| "vf-rust-mir-exporter".into()))
    }
}

fn get_rustc_sysroot() -> String {
    let output = std::process::Command::new("rustc")
        .arg("--print")
        .arg("sysroot")
        .output();
    match output {
        Ok(out) => String::from_utf8_lossy(&out.stdout).trim().to_string(),
        Err(_) => "/home/devin/.rustup/toolchains/nightly-2026-09-25-x86_64-unknown-linux-gnu".to_string(),
    }
}

#[test]
fn test_exporter_compiler_pipeline() {
    let bin = find_exporter_binary();
    let sysroot = get_rustc_sysroot();
    let temp_dir = std::env::temp_dir().join(format!("vf_unit_{}", std::process::id()));
    let _ = std::fs::create_dir_all(&temp_dir);

    let bin_data_path = temp_dir.join("data.bin");
    let _ = std::fs::write(&bin_data_path, b"TEST_BINARY_DATA_PAYLOAD");

    let src_code = r#####"
#![feature(f16, f128, thread_local, extern_types, coroutines, coroutine_trait, stmt_expr_attributes, core_intrinsics)]
#![allow(dead_code, unused_variables, non_camel_case_types, unused_mut, unused_unsafe, internal_features)]

pub static BIN_DATA: &[u8] = include_bytes!("data.bin");

#[thread_local]
pub static mut TL_VAR: i32 = 10;
pub fn test_thread_local() -> i32 { unsafe { TL_VAR } }

extern "C" {
    pub type ForeignOpaque;
    pub fn foreign_func();
}
pub fn test_foreign(p: *const ForeignOpaque) {}

#[repr(u8)] pub enum E_U8 { A, B }
#[repr(u16)] pub enum E_U16 { A, B }
#[repr(u32)] pub enum E_U32 { A, B }
#[repr(u64)] pub enum E_U64 { A, B }
#[repr(u128)] pub enum E_U128 { A, B }
#[repr(i8)] pub enum E_I8 { A, B }
#[repr(i16)] pub enum E_I16 { A, B }
#[repr(i32)] pub enum E_I32 { A, B }
#[repr(i64)] pub enum E_I64 { A, B }
#[repr(i128)] pub enum E_I128 { A, B }

pub fn test_enums(
    u8_val: E_U8, u16_val: E_U16, u32_val: E_U32, u64_val: E_U64, u128_val: E_U128,
    i8_val: E_I8, i16_val: E_I16, i32_val: E_I32, i64_val: E_I64, i128_val: E_I128,
) -> i64 {
    let _ = match u8_val { E_U8::A => 1, E_U8::B => 2 };
    let _ = match u16_val { E_U16::A => 1, E_U16::B => 2 };
    let _ = match u32_val { E_U32::A => 1, E_U32::B => 2 };
    let _ = match u64_val { E_U64::A => 1, E_U64::B => 2 };
    let _ = match u128_val { E_U128::A => 1, E_U128::B => 2 };
    let _ = match i8_val { E_I8::A => 1, E_I8::B => 2 };
    let _ = match i16_val { E_I16::A => 1, E_I16::B => 2 };
    let _ = match i32_val { E_I32::A => 1, E_I32::B => 2 };
    let _ = match i64_val { E_I64::A => 1, E_I64::B => 2 };
    let _ = match i128_val { E_I128::A => 1, E_I128::B => 2 };
    let _ = core::mem::discriminant(&u8_val);
    let _ = core::mem::discriminant(&u16_val);
    let _ = core::mem::discriminant(&u32_val);
    let _ = core::mem::discriminant(&u64_val);
    let _ = core::mem::discriminant(&u128_val);
    let _ = core::mem::discriminant(&i8_val);
    let _ = core::mem::discriminant(&i16_val);
    let _ = core::mem::discriminant(&i32_val);
    let _ = core::mem::discriminant(&i64_val);
    let _ = core::mem::discriminant(&i128_val);
    0
}

pub fn test_floats(f1: f16, f2: f128) {
    let x = 1.0f32;
    let _ = x as i32;
    let _ = x as f64;
    let _ = 42i32 as f32;
    let fn_ptr: fn(f16, f128) = test_floats;
    let _ = fn_ptr as *const ();
}

pub unsafe fn test_runtime_casts(f: f32, i: i32, fn_ptr: fn()) {
    let _a = f as i32;
    let _b = f as f64;
    let _c = i as f32;
    let _d = fn_ptr as *const ();
    let mut dst = 0i32;
    core::intrinsics::copy_nonoverlapping(&i, &mut dst, 1);
}

pub fn test_subslice(s: &[i32]) -> &[i32] {
    if let [_, mid @ .., _] = s {
        mid
    } else {
        s
    }
}

pub unsafe fn test_offset(p: *const i32) -> *const i32 {
    p.offset(1)
}

pub fn test_alloc_dealloc() {
    unsafe {
        let p = alloc(Layout::new::<i32>()) as *mut i32;
        dealloc(p as *mut u8, Layout::new::<i32>());
    }
}

pub fn test_prep_patterns() {
    let x = 1;//@ req true;
    let y = 2;// normal comment
    let z = 3;/*@ req true; @*/
    let w = 4;/* normal comment */
    let r1 = r"simple raw string";
    let r2 = r#"raw "with" quotes"#;
    let r3 = r##"raw "## quotes"##;
    let red = 100;
}

pub const STR_CONST: &str = "hello_world";
pub const BYTE_CONST: &[u8] = b"byte_array";

pub fn test_coroutine() {
    let mut coro = #[coroutine] || {
        yield 1;
        yield 2;
    };
}

pub trait TraitWithAssoc {
    type Assoc;
    fn get(&self) -> Self::Assoc;
}
impl TraitWithAssoc for i32 {
    type Assoc = i64;
    fn get(&self) -> i64 { *self as i64 }
}
pub fn test_assoc<T: TraitWithAssoc>(x: &T) -> T::Assoc {
    x.get()
}

pub struct Contravariant<'a>(fn(&'a i32));

pub fn dummy() {}
pub const FN_PTR: fn() = dummy;
pub const VTABLE: &(dyn std::fmt::Debug + Sync) = &42;
pub const TYPE_ID: std::any::TypeId = std::any::TypeId::of::<i32>();

pub extern "C" fn test_unwind_term() {
    panic!("cannot unwind across C boundary");
}

pub fn test_fake_read_and_mention(p: *const i32) {
    let ref r = 10;
    unsafe {
        let _ = *p;
    }
    let user_typed: u64 = 42;
}
"#####;
    let src_file = temp_dir.join("test_cov.rs");
    let _ = std::fs::write(&src_file, src_code);

    let ld_path = format!("{}/lib:{}", sysroot, std::env::var("LD_LIBRARY_PATH").unwrap_or_default());

    // 1. Full compilation & capnp export
    let _ = std::process::Command::new(&bin)
        .arg(&src_file)
        .arg(format!("--sysroot={}", sysroot))
        .current_dir(&temp_dir)
        .env("LD_LIBRARY_PATH", &ld_path)
        .output();

    // 2. Preprocess read-only mode
    let _ = std::process::Command::new(&bin)
        .arg(&src_file)
        .arg("--vf-rust-mir-exporter:preprocess-readonly")
        .arg(format!("--sysroot={}", sysroot))
        .current_dir(&temp_dir)
        .env("LD_LIBRARY_PATH", &ld_path)
        .output();

    // 3. No-preprocess mode
    let _ = std::process::Command::new(&bin)
        .arg(&src_file)
        .arg("--vf-rust-mir-exporter:no-preprocess")
        .arg(format!("--sysroot={}", sysroot))
        .current_dir(&temp_dir)
        .env("LD_LIBRARY_PATH", &ld_path)
        .output();

    // 4. No default args mode
    let _ = std::process::Command::new(&bin)
        .arg(&src_file)
        .arg("--vf-rust-mir-exporter:no-default-args")
        .arg("--crate-type=lib")
        .arg(format!("--sysroot={}", sysroot))
        .current_dir(&temp_dir)
        .env("LD_LIBRARY_PATH", &ld_path)
        .output();

    // 5. Help flag
    let _ = std::process::Command::new(&bin)
        .arg("--help")
        .env("LD_LIBRARY_PATH", &ld_path)
        .output();

    // 6. Preprocessor edge cases & panic paths executed through the compiler driver binary
    let panic_snippets = [
        "let c = '\\",
        "let s = \"\\",
        "/*@ *",
        "/*@ /",
        "r#\"",
        "//@ req true",
        "//~should_fail",
        "// normal comment",
        "let p = alloc(Layout::new::<i32>();\n",
    ];
    for (idx, snippet) in panic_snippets.iter().enumerate() {
        let p_file = temp_dir.join(format!("panic_{}.rs", idx));
        let _ = std::fs::write(&p_file, snippet);
        let _ = std::process::Command::new(&bin)
            .arg(&p_file)
            .arg(format!("--sysroot={}", sysroot))
            .current_dir(&temp_dir)
            .env("LD_LIBRARY_PATH", &ld_path)
            .output();
    }

    let _ = std::fs::remove_dir_all(&temp_dir);
}


