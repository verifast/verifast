#[derive(Copy, Clone, Debug)]
pub struct SrcPos {
    line: i32, // 1-based
    column: i32 // 1-based
}

struct TextIterator<'a> {
    chars: std::iter::Peekable<std::str::Chars<'a>>,
    pos: SrcPos,
    last_char_was_cr: bool,
}

impl<'a> TextIterator<'a> {
    fn peek(&mut self) -> Option<char> {
        match self.chars.peek() {
            None => None,
            Some(c) => Some(*c)
        }
    }

    fn next(&mut self) -> Option<char> {
        match self.chars.next() {
            None => None,
            Some(c) => {
                match c {
                    '\r' => {
                        self.last_char_was_cr = true;
                        self.pos.line += 1;
                        self.pos.column = 1;
                    }
                    '\n' => {
                        if !self.last_char_was_cr {
                            self.pos.line += 1;
                            self.pos.column = 1;
                        }
                        self.last_char_was_cr = false;
                    }
                    c => {
                        self.last_char_was_cr = false;
                        self.pos.column += 1;
                    }
                };
                Some(c)
            }
        }
    }
}

#[derive(Debug)]
pub struct GhostRange {
    in_fn_body: bool,
    start: SrcPos, // position of first character of contents *before preprocessing*
    end: SrcPos, // position after last character of contents *before preprocessing*
    contents: String, // not including the ghost range delimiters (//@, /*@, @*/)
}

pub fn preprocess(input: &str, ghost_ranges: &mut Vec<GhostRange>) -> String {
    let mut cs = TextIterator { chars: input.chars().peekable(), pos: SrcPos { line: 1, column: 1 }, last_char_was_cr: false };
    let mut output = String::new();
    let mut inside_word = false;
    let mut brace_depth = 0;
    let mut next_block_is_fn_body = false;
    let mut fn_body_brace_depth = -1;
    loop {
        let was_inside_word = inside_word;
        inside_word = false;
        match cs.peek() {
            None => {
                output.push_str("\n\nfn VeriFast_ghost_command() {}\n");
                return output;
            }
            Some(c) => {
                match c {
                    '{' => {
                        cs.next();
                        output.push('{');
                        if next_block_is_fn_body {
                            assert!(fn_body_brace_depth == -1);
                            fn_body_brace_depth = brace_depth;
                            next_block_is_fn_body = false;
                        }
                        brace_depth += 1;
                    }
                    '}' => {
                        cs.next();
                        output.push('}');
                        brace_depth -= 1;
                        if fn_body_brace_depth == brace_depth {
                            fn_body_brace_depth = -1;
                        }
                    }
                    '/' => {
                        cs.next();
                        match cs.peek() {
                            Some('/') => {
                                cs.next();
                                match cs.peek() {
                                    Some('@') => {
                                        cs.next();
                                        let start = cs.pos;
                                        let in_fn_body = fn_body_brace_depth != -1;
                                        if in_fn_body {
                                            output.push_str("VeriFast_ghost_command();");
                                        }
                                        output.push_str("//@");
                                        let mut contents = String::new();
                                        loop {
                                            match cs.peek() {
                                                None | Some('\n') | Some('\r') => { break; }
                                                Some(c) => {
                                                    cs.next();
                                                    output.push(c);
                                                    contents.push(c);
                                                }
                                            }
                                        }
                                        ghost_ranges.push(GhostRange { in_fn_body, start, end: cs.pos, contents });
                                    }
                                    _ => {
                                        output.push_str("//");
                                        loop {
                                            match cs.peek() {
                                                None | Some('\n') | Some('\r') => { break; }
                                                Some(c) => { cs.next(); output.push(c); }
                                            }
                                        }
                                    }
                                }
                            }
                            Some('*') => {
                                cs.next();
                                let mut ghost_range = GhostRange {
                                    in_fn_body: false,
                                    start: SrcPos { line: -1, column: -1 },
                                    end: SrcPos { line: -1, column: -1 },
                                    contents: String::new()
                                };
                                let mut is_ghost_range = false;
                                match cs.peek() {
                                    Some('@') => {
                                        cs.next();
                                        is_ghost_range = true;
                                        ghost_range.in_fn_body = fn_body_brace_depth != -1;
                                        ghost_range.start = cs.pos;
                                        if ghost_range.in_fn_body {
                                            output.push_str("VeriFast_ghost_command();");
                                        }
                                        output.push_str("/*@");
                                    }
                                    _ => {
                                        output.push_str("/*");
                                    }
                                };
                                let mut nesting_depth = 0;
                                loop {
                                    match cs.peek() {
                                        None => { panic!("EOF inside multiline comment"); }
                                        Some('*') => {
                                            cs.next();
                                            output.push('*');
                                            ghost_range.contents.push('*');
                                            match cs.peek() {
                                                None => { panic!("EOF inside multiline comment"); }
                                                Some('/') => {
                                                    cs.next();
                                                    output.push('/');
                                                    ghost_range.contents.push('/');
                                                    if nesting_depth == 0 {
                                                        break;
                                                    } else {
                                                        nesting_depth -= 1;
                                                    }
                                                }
                                                _ => {}
                                            }
                                        }
                                        Some('/') => {
                                            cs.next();
                                            output.push('/');
                                            ghost_range.contents.push('/');
                                            match cs.peek() {
                                                None => { panic!("EOF inside multiline comment"); }
                                                Some('*') => {
                                                    cs.next();
                                                    output.push('*');
                                                    ghost_range.contents.push('*');
                                                    nesting_depth += 1;
                                                }
                                                _ => {}
                                            }
                                        }
                                        Some(c) => {
                                            cs.next();
                                            output.push(c);
                                            ghost_range.contents.push(c);
                                        }
                                    }
                                }
                                if is_ghost_range {
                                    // Get rid of the */
                                    ghost_range.end = cs.pos;
                                    ghost_range.end.column -= 2;
                                    ghost_range.contents.truncate(ghost_range.contents.len() - 2);
                                    if ghost_range.contents.ends_with("@") {
                                        ghost_range.contents.truncate(ghost_range.contents.len() - 1);
                                        ghost_range.end.column -= 1;
                                    }
                                    ghost_ranges.push(ghost_range);
                                }
                            }
                            _ => {
                                output.push('/');
                            }
                        }
                    }
                    '\'' => {
                        cs.next();
                        output.push('\'');
                        match cs.peek() {
                            None => { panic!("EOF inside character literal"); }
                            Some('\\') => {
                                cs.next();
                                output.push('\\');
                                match cs.peek() {
                                    None => { panic!("EOF inside character literal"); }
                                    Some(c) => {
                                        cs.next();
                                        output.push(c);
                                    }
                                }
                            }
                            Some(c) => {
                                cs.next();
                                output.push(c);
                            }
                        }
                        match cs.peek() {
                            Some('\'') => {
                                cs.next();
                                output.push('\'');
                            }
                            _ => { inside_word = true; } // Might be lifetime or loop label
                        }
                    }
                    '"' => {
                        cs.next();
                        output.push('"');
                        loop {
                            match cs.peek() {
                                None => { panic!("EOF inside string literal"); }
                                Some('"') => {
                                    cs.next();
                                    output.push('"');
                                    break;
                                }
                                Some('\\') => {
                                    cs.next();
                                    output.push('\\');
                                    match cs.peek() {
                                        None => { panic!("EOF inside string literal"); }
                                        Some(c) => {
                                            cs.next();
                                            output.push(c);
                                        }
                                    }
                                }
                                Some(c) => {
                                    cs.next();
                                    output.push(c);
                                }
                            }
                        }
                    }
                    'r' => {
                        cs.next();
                        output.push('r');
                        inside_word = true;
                        let mut nb_hashes = 0;
                    'stringLoop:
                        loop {
                            match cs.peek() {
                                Some('#') => {
                                    cs.next();
                                    output.push('#');
                                    inside_word = false;
                                    nb_hashes += 1;
                                }
                                Some('"') => {
                                    cs.next();
                                    output.push('"');
                                    inside_word = false;
                                    loop {
                                        match cs.peek() {
                                            None => { panic!("EOF inside string literal"); }
                                            Some('"') => {
                                                cs.next();
                                                output.push('"');
                                                let mut nb_hashes_seen = 0;
                                                loop {
                                                    if nb_hashes_seen == nb_hashes {
                                                        break 'stringLoop;
                                                    }
                                                    match cs.peek() {
                                                        Some('#') => {
                                                            cs.next();
                                                            output.push('#');
                                                            nb_hashes_seen += 1;
                                                        }
                                                        _ => { break; }
                                                    }
                                                }
                                            }
                                            Some(c) => {
                                                cs.next();
                                                output.push(c);
                                            }
                                        }
                                    }
                                }
                                _ => break
                            }
                        }
                    }
                    'f' if !was_inside_word => {
                        cs.next();
                        output.push('f');
                        inside_word = true;
                        match cs.peek() {
                            Some('n') => {
                                cs.next();
                                output.push('n');
                                match cs.peek() {
                                    Some('A'..='Z'|'a'..='z'|'_'|'0'..='9') => {}
                                    _ => {
                                        next_block_is_fn_body = true;
                                    }
                                }
                            }
                            _ => {}
                        }
                    }
                    c @ ('A'..='Z'|'a'..='z'|'_') => {
                        cs.next();
                        output.push(c);
                        inside_word = true;
                    }
                    c => {
                        cs.next();
                        output.push(c);
                    }
                }
            }
        }
    }
}