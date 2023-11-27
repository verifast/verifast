#[derive(Copy, Clone, Debug)]
pub struct SrcPos {
    pub line: i32,   // 1-based
    pub column: i32, // 1-based
    byte_pos: u32,   // 0-based
}

impl SrcPos {
    pub fn is_dummy(&self) -> bool {
        self.line == -1 || self.column == -1
    }
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
            Some(c) => Some(*c),
        }
    }

    fn next(&mut self) -> Option<char> {
        match self.chars.next() {
            None => None,
            Some(c) => {
                self.pos.byte_pos += 1;
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
    start: SrcPos,    // position of first character of contents *before preprocessing*
    end: SrcPos,      // position after last character of contents *before preprocessing*
    contents: String, // not including the ghost range delimiters (//@, /*@, @*/)
}

impl GhostRange {
    pub fn is_dummy(&self) -> bool {
        self.start.is_dummy() || self.end.is_dummy()
    }
    pub fn span(&self) -> Option<rustc_span::Span> {
        use rustc_span::{BytePos, Span, SyntaxContext};
        if self.is_dummy() {
            None
        } else {
            Some(Span::new(
                BytePos(self.start.byte_pos),
                BytePos(self.end.byte_pos),
                SyntaxContext::root(),
                None,
            ))
        }
    }
    pub fn contents(&self) -> &str {
        &self.contents
    }
    pub fn start_pos(&self) -> SrcPos {
        self.start
    }
    pub fn end_pos(&self) -> SrcPos {
        self.end
    }
}

pub fn preprocess(input: &str, ghost_ranges: &mut Vec<GhostRange>) -> String {
    let mut cs = TextIterator {
        chars: input.chars().peekable(),
        pos: SrcPos {
            line: 1,
            column: 1,
            byte_pos: 0,
        },
        last_char_was_cr: false,
    };
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
                                        cs.pos.byte_pos -= 3;
                                        cs.pos.column -= 3;
                                        let start = cs.pos;
                                        let in_fn_body = fn_body_brace_depth != -1;
                                        if in_fn_body {
                                            output.push_str("VeriFast_ghost_command();");
                                            cs.pos.byte_pos += 25;
                                        }
                                        let mut contents = String::new();
                                        output.push_str("//@");
                                        contents.push_str("//@");
                                        cs.pos.byte_pos += 3;
                                        cs.pos.column += 3;
                                        let end;
                                        loop {
                                            match cs.peek() {
                                                None => {
                                                    end = cs.pos;
                                                    break;
                                                }
                                                Some(c) => {
                                                    output.push(c);

                                                    if (c == '\r' || c == '\n') {
                                                        end = SrcPos {
                                                            byte_pos: cs.pos.byte_pos - 1,
                                                            ..cs.pos
                                                        };
                                                        cs.next();
                                                        break;
                                                    } else {
                                                        contents.push(c);
                                                        cs.next();
                                                    }
                                                }
                                            }
                                        }
                                        ghost_ranges.push(GhostRange {
                                            in_fn_body,
                                            start,
                                            end,
                                            contents,
                                        });
                                    }
                                    _ => {
                                        output.push_str("//");
                                        loop {
                                            match cs.peek() {
                                                None => {
                                                    break;
                                                }
                                                Some(c) => {
                                                    cs.next();
                                                    output.push(c);
                                                    if c == '\n' || c == '\r' {
                                                        break;
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                            Some('*') => {
                                cs.next();
                                let mut ghost_range = GhostRange {
                                    in_fn_body: false,
                                    start: SrcPos {
                                        line: -1,
                                        column: -1,
                                        byte_pos: 0,
                                    },
                                    end: SrcPos {
                                        line: -1,
                                        column: -1,
                                        byte_pos: 0,
                                    },
                                    contents: String::new(),
                                };
                                let mut is_ghost_range = false;
                                match cs.peek() {
                                    Some('@') => {
                                        cs.next();
                                        cs.pos.column -= 3;
                                        cs.pos.byte_pos -= 3;
                                        is_ghost_range = true;
                                        ghost_range.in_fn_body = fn_body_brace_depth != -1;
                                        ghost_range.start = cs.pos;
                                        if ghost_range.in_fn_body {
                                            output.push_str("VeriFast_ghost_command();");
                                            cs.pos.byte_pos += 25;
                                        }
                                        output.push_str("/*@");
                                        ghost_range.contents.push_str("/*@");
                                        cs.pos.column += 3;
                                        cs.pos.byte_pos += 3;
                                    }
                                    _ => {
                                        output.push_str("/*");
                                    }
                                };
                                let mut nesting_depth = 0;
                                loop {
                                    match cs.peek() {
                                        None => {
                                            panic!("EOF inside multiline comment");
                                        }
                                        Some('*') => {
                                            cs.next();
                                            output.push('*');
                                            ghost_range.contents.push('*');
                                            match cs.peek() {
                                                None => {
                                                    panic!("EOF inside multiline comment");
                                                }
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
                                                None => {
                                                    panic!("EOF inside multiline comment");
                                                }
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
                                    // ghost_range.end.column -= 2;
                                    // ghost_range
                                    //     .contents
                                    //     .truncate(ghost_range.contents.len() - 2);
                                    // if ghost_range.contents.ends_with("@") {
                                    //     ghost_range
                                    //         .contents
                                    //         .truncate(ghost_range.contents.len() - 1);
                                    //     ghost_range.end.column -= 1;
                                    // }
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
                            None => {
                                panic!("EOF inside character literal");
                            }
                            Some('\\') => {
                                cs.next();
                                output.push('\\');
                                match cs.peek() {
                                    None => {
                                        panic!("EOF inside character literal");
                                    }
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
                            _ => {
                                inside_word = true;
                            } // Might be lifetime or loop label
                        }
                    }
                    '"' => {
                        cs.next();
                        output.push('"');
                        loop {
                            match cs.peek() {
                                None => {
                                    panic!("EOF inside string literal");
                                }
                                Some('"') => {
                                    cs.next();
                                    output.push('"');
                                    break;
                                }
                                Some('\\') => {
                                    cs.next();
                                    output.push('\\');
                                    match cs.peek() {
                                        None => {
                                            panic!("EOF inside string literal");
                                        }
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
                        'stringLoop: loop {
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
                                            None => {
                                                panic!("EOF inside string literal");
                                            }
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
                                                        _ => {
                                                            break;
                                                        }
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
                                _ => break,
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
                                    Some('A'..='Z' | 'a'..='z' | '_' | '0'..='9') => {}
                                    _ => {
                                        next_block_is_fn_body = true;
                                    }
                                }
                            }
                            _ => {}
                        }
                    }
                    c @ ('A'..='Z' | 'a'..='z' | '_') => {
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
