#[derive(Copy, Clone, Debug)]
pub struct SrcPos {
    pub line: i32,     // 1-based
    pub column: i32,   // 1-based
    pub byte_pos: u32, // 0-based
}

impl SrcPos {
    pub fn is_dummy(&self) -> bool {
        self.line == -1 || self.column == -1
    }
}

struct TextIterator<'a> {
    chars: std::iter::Peekable<std::str::Chars<'a>>,
    src_pos: u32,
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
                let len: u32 = c.len_utf8().try_into().unwrap();
                self.src_pos += len;
                self.pos.byte_pos += len;
                match c {
                    '\r' => {
                        self.last_char_was_cr = true;
                        self.pos.line += 1;
                        self.pos.column = 1;
                    }
                    '\n' => {
                        if self.last_char_was_cr {
                            self.pos.byte_pos -= 1; // rustc normalizes CRLF to LF
                        } else {
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

#[derive(Copy, Clone, PartialEq, Debug)]
pub enum GhostRangeKind {
    Regular,
    BlockDecls, // This ghost range contains the ghost decls of a block with ghost decls.
    GenericArgs,
    Mut,
}

#[derive(Debug)]
pub struct GhostRange {
    in_fn_body: bool,
    pub kind: GhostRangeKind,
    pub block_end: Option<SrcPos>, // The position of the closing brace of the block with ghost decls.
    pub end_of_preceding_token: SrcPos,
    start: SrcPos,
    end: SrcPos,
    contents: String,
    span: Option<rustc_span::Span>,
}

impl GhostRange {
    pub fn is_dummy(&self) -> bool {
        self.start.is_dummy() || self.end.is_dummy()
    }
    pub fn set_span(&mut self, source_file_start_pos: rustc_span::BytePos) {
        use rustc_span::{BytePos, Span, SyntaxContext};
        self.span = if self.is_dummy() {
            None
        } else {
            Some(Span::new(
                source_file_start_pos + BytePos(self.start.byte_pos),
                source_file_start_pos + BytePos(self.end.byte_pos),
                SyntaxContext::root(),
                None,
            ))
        };
    }
    pub fn block_end_span(&self) -> rustc_span::Span {
        let start_span = self.span.unwrap();
        let end_byte_pos = self.block_end.unwrap().byte_pos;
        use rustc_span::{BytePos, Span, SyntaxContext};
        let source_file_start_pos = start_span.lo() - BytePos(self.start.byte_pos);
        Span::new(
            source_file_start_pos + BytePos(end_byte_pos),
            source_file_start_pos + BytePos(end_byte_pos + 1),
            SyntaxContext::root(),
            None,
        )
    }
    pub fn span(&self) -> Option<rustc_span::Span> {
        self.span
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

fn ghost_range_contents_is_block_decls(contents: &str) -> bool {
    let trimmed_contents = contents.trim_ascii_start();
    trimmed_contents.starts_with("pred ")
        || trimmed_contents.starts_with("lem ")
        || trimmed_contents.starts_with("lem_auto ")
        || trimmed_contents.starts_with("lem_auto(")
        || trimmed_contents.starts_with("let_lft ")
}

/// If a ghost range occurs at the toplevel before the first token in a file,
/// the preprocessor inserts `#[allow(warnings)]`. This is necessary, in case
/// the file is a module, to ensure that the module's body span includes the
/// ghost range. (The body span extends from the first to the last token in
/// the file.)
const VF_SYNTHETIC_FIRST_TOKENS: &str = "#[allow(warnings)]";
const VF_SYNTHETIC_FIRST_TOKENS_LEN: u32 = VF_SYNTHETIC_FIRST_TOKENS.len() as u32;
const VF_GHOST_CMD_TAG: &str = "crate::VeriFast_ghost_command();";
const VF_GHOST_CMD_TAG_LEN: u32 = VF_GHOST_CMD_TAG.len() as u32;

pub fn preprocess(
    input: &str,
    read_only: bool,
    directives: &mut Vec<Box<GhostRange>>,
    ghost_ranges: &mut Vec<Box<GhostRange>>,
) -> String {
    let input_starts_with_bom = input.starts_with("\u{feff}");
    let mut cs = TextIterator {
        chars: input.chars().peekable(),
        src_pos: 0,
        pos: SrcPos {
            line: 1,
            column: 1,
            byte_pos: 0,
        },
        last_char_was_cr: false,
    };
    if input_starts_with_bom {
        cs.chars.next(); // rustc removes BOM; we need to skip it to keep the byte positions correct
    }
    let mut output = String::new();
    let mut inside_word = false;
    let mut brace_depth = 0;
    let mut bracket_depth = 0;
    let mut last_token_was_fn = false;
    let mut next_block_is_fn_body = false;
    let mut fn_body_brace_depth = -1;
    let mut inside_whitespace = true;
    let mut start_of_whitespace = cs.pos; // Only meaningful when inside whitespace. Note: comments
                                          // count as whitespace.
    let mut ghost_range_seen_since_last_token = false;
    let mut start_of_block: SrcPos = cs.pos; // Only meaningful when inside a block.
    struct OpenBlock {
        start_ghost_range_index: usize, // An index into `ghost_ranges`
        brace_depth: i32,               // The number of *enclosing* blocks.
    }
    let mut open_blocks: Vec<OpenBlock> = Vec::new();
    loop {
        let was_inside_word = inside_word;
        inside_word = false;
        let was_inside_whitespace = inside_whitespace;
        inside_whitespace = false;
        let old_last_token_was_fn = last_token_was_fn;
        last_token_was_fn = false;
        match cs.peek() {
            None => {
                if !open_blocks.is_empty() {
                    let last = open_blocks.last().unwrap();
                    panic!(
                        "EOF inside block starting at {}:{}",
                        ghost_ranges[last.start_ghost_range_index].start.line,
                        ghost_ranges[last.start_ghost_range_index].start.column
                    );
                }
                if !read_only {
                    output.push_str("\n\nconst fn VeriFast_ghost_command() {}\nfn VeriFast_alloc<T>() -> *mut T { VeriFast_alloc() }\nfn VF_free<T>(_ptr: *mut T) {}\n");
                }
                return output;
            }
            Some(c) => {
                match c {
                    ';' => {
                        cs.next();
                        output.push(c);
                        if bracket_depth == 0 { // We are not inside an array type [T; N].
                            next_block_is_fn_body = false;
                        }
                    }
                    '{' => {
                        start_of_block = cs.pos;
                        cs.next();
                        output.push('{');
                        if next_block_is_fn_body {
                            if fn_body_brace_depth == -1 {
                                fn_body_brace_depth = brace_depth;
                            }
                            next_block_is_fn_body = false;
                        }
                        brace_depth += 1;
                    }
                    '}' => {
                        if let Some(last) = open_blocks.last() {
                            if last.brace_depth == brace_depth {
                                ghost_ranges[last.start_ghost_range_index].block_end = Some(cs.pos);
                                open_blocks.pop();
                                if !read_only {
                                    output.push_str(VF_GHOST_CMD_TAG);
                                    cs.pos.byte_pos += VF_GHOST_CMD_TAG_LEN;
                                }
                            }
                        }
                        cs.next();
                        brace_depth -= 1;
                        if fn_body_brace_depth == brace_depth {
                            fn_body_brace_depth = -1;
                        }
                        output.push('}');
                    }
                    '[' => {
                        cs.next();
                        output.push('[');
                        bracket_depth += 1;
                    }
                    ']' => {
                        cs.next();
                        output.push(']');
                        bracket_depth -= 1;
                    }
                    '/' => {
                        cs.next();
                        match cs.peek() {
                            Some('/') => {
                                cs.next();
                                last_token_was_fn = old_last_token_was_fn;
                                inside_whitespace = true;
                                if !was_inside_whitespace {
                                    start_of_whitespace = cs.pos;
                                    start_of_whitespace.byte_pos -= 2;
                                    start_of_whitespace.column -= 2;
                                    ghost_range_seen_since_last_token = false;
                                }
                                match cs.peek() {
                                    Some('@') => {
                                        cs.next();
                                        cs.pos.byte_pos -= 3;
                                        cs.pos.column -= 3;
                                        let start = cs.pos;
                                        let in_fn_body = fn_body_brace_depth != -1;
                                        if !read_only {
                                            if in_fn_body {
                                                output.push_str(VF_GHOST_CMD_TAG);
                                                cs.pos.byte_pos += VF_GHOST_CMD_TAG_LEN;
                                            } else if start_of_whitespace.byte_pos == 0 {
                                                output.push_str(VF_SYNTHETIC_FIRST_TOKENS);
                                                cs.pos.byte_pos += VF_SYNTHETIC_FIRST_TOKENS_LEN;
                                            }
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

                                                    if c == '\r' || c == '\n' {
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
                                        let is_block_decls = in_fn_body
                                            && start_of_whitespace.byte_pos
                                                == start_of_block.byte_pos + 1
                                            && !ghost_range_seen_since_last_token
                                            && ghost_range_contents_is_block_decls(
                                                contents.strip_prefix("//@").unwrap(),
                                            );
                                            if is_block_decls {
                                                open_blocks.push(OpenBlock {
                                                    start_ghost_range_index: ghost_ranges.len(),
                                                    brace_depth: brace_depth,
                                                });
                                        }
                                        ghost_ranges.push(Box::new(GhostRange {
                                            in_fn_body,
                                            end_of_preceding_token: start_of_whitespace,
                                            start,
                                            end,
                                            contents,
                                            span: None,
                                            kind: if is_block_decls {
                                                GhostRangeKind::BlockDecls
                                            } else {
                                                GhostRangeKind::Regular
                                            },
                                            block_end: None,
                                        }));
                                        ghost_range_seen_since_last_token = true;
                                    }
                                    Some('~') => {
                                        cs.next();
                                        cs.pos.byte_pos -= 3;
                                        cs.pos.column -= 3;
                                        let start = cs.pos;
                                        let in_fn_body = fn_body_brace_depth != -1;
                                        let mut contents = String::new();
                                        output.push_str("//~");
                                        cs.pos.byte_pos += 3;
                                        cs.pos.column += 3;
                                        let end;
                                        loop {
                                            match cs.peek() {
                                                Some(c @ ('A'..='Z' | 'a'..='z' | '_')) => {
                                                    output.push(c);

                                                    contents.push(c);
                                                    cs.next();
                                                }
                                                _ => {
                                                    end = cs.pos;
                                                    break;
                                                }
                                            }
                                        }
                                        directives.push(Box::new(GhostRange {
                                            in_fn_body,
                                            end_of_preceding_token: start_of_whitespace,
                                            start,
                                            end,
                                            contents,
                                            span: None,
                                            kind: GhostRangeKind::Regular,
                                            block_end: None,
                                        }));
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
                                let mut start_of_comment = cs.pos;
                                start_of_comment.byte_pos -= 1;
                                start_of_comment.column -= 1;
                                cs.next();
                                last_token_was_fn = old_last_token_was_fn;
                                inside_whitespace = true;
                                if !was_inside_whitespace {
                                    start_of_whitespace = cs.pos;
                                    start_of_whitespace.byte_pos -= 2;
                                    start_of_whitespace.column -= 2;
                                    ghost_range_seen_since_last_token = false;
                                }
                                let mut ghost_range = Box::new(GhostRange {
                                    in_fn_body: false,
                                    end_of_preceding_token: start_of_whitespace,
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
                                    span: None,
                                    kind: GhostRangeKind::Regular,
                                    block_end: None,
                                });
                                let mut is_ghost_range = false;
                                let is_ghost_cmd;
                                let mut is_generic_args = false;
                                match cs.peek() {
                                    Some('@') => {
                                        cs.next();
                                        cs.pos.column -= 3;
                                        cs.pos.byte_pos -= 3;
                                        is_ghost_range = true;
                                        ghost_range.in_fn_body = fn_body_brace_depth != -1;
                                        ghost_range.start = cs.pos;
                                        if ghost_range.in_fn_body {
                                            is_ghost_cmd = match cs.peek() {
                                                Some(':'|'~') => false,
                                                _ => true,
                                            };
                                            if is_ghost_cmd {
                                                if !read_only {
                                                    output.push_str(VF_GHOST_CMD_TAG);
                                                    cs.pos.byte_pos += VF_GHOST_CMD_TAG_LEN;
                                                }
                                            } else {
                                                is_generic_args = match cs.peek() {
                                                    Some(':') => true,
                                                    _ => false,
                                                };
                                            }
                                        } else if start_of_whitespace.byte_pos == 0 {
                                            if !read_only {
                                                output.push_str(VF_SYNTHETIC_FIRST_TOKENS);
                                                cs.pos.byte_pos += VF_SYNTHETIC_FIRST_TOKENS_LEN;
                                            }
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
                                            panic!("EOF inside multiline comment starting at {}:{}", start_of_comment.line, start_of_comment.column);
                                        }
                                        Some('*') => {
                                            cs.next();
                                            output.push('*');
                                            ghost_range.contents.push('*');
                                            match cs.peek() {
                                                None => {
                                                    panic!("EOF inside multiline comment starting at {}:{}", start_of_comment.line, start_of_comment.column);
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
                                                    panic!("EOF inside multiline comment starting at {}:{}", start_of_comment.line, start_of_comment.column);
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
                                    ghost_range.end = cs.pos;
                                    ghost_range.kind = if is_generic_args {
                                        GhostRangeKind::GenericArgs
                                    } else if fn_body_brace_depth != -1
                                        && start_of_whitespace.byte_pos
                                            == start_of_block.byte_pos + 1
                                        && !ghost_range_seen_since_last_token
                                        && ghost_range_contents_is_block_decls(
                                            ghost_range.contents.strip_prefix("/*@").unwrap(),
                                        )
                                    {
                                        GhostRangeKind::BlockDecls
                                    } else if ghost_range.contents == "/*@~mut@*/" {
                                        GhostRangeKind::Mut
                                    } else {
                                        GhostRangeKind::Regular
                                    };
                                    if ghost_range.kind == GhostRangeKind::BlockDecls {
                                        open_blocks.push(OpenBlock {
                                            start_ghost_range_index: ghost_ranges.len(),
                                            brace_depth: brace_depth,
                                        });
                                    }
                                    ghost_ranges.push(ghost_range);
                                    ghost_range_seen_since_last_token = true;
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
                                _ => {
                                    next_block_is_fn_body |= old_last_token_was_fn;
                                    break;
                                }
                            }
                        }
                    }
                    'f' if !was_inside_word => {
                        cs.next();
                        output.push('f');
                        next_block_is_fn_body |= old_last_token_was_fn;
                        inside_word = true;
                        match cs.peek() {
                            Some('n') => {
                                cs.next();
                                output.push('n');
                                match cs.peek() {
                                    Some('A'..='Z' | 'a'..='z' | '_' | '0'..='9') => {}
                                    _ => {
                                        last_token_was_fn = true;
                                    }
                                }
                            }
                            _ => {}
                        }
                    }
                    c @ ('A'..='Z' | 'a'..='z' | '_') => {
                        loop {
                            if c == 'a' && !was_inside_word {
                                // Check for 'alloc(Layout::new::<T>()) as *mut T'
                                let byte_pos = cs.pos.byte_pos;
                                let rest = &input[cs.src_pos as usize..];
                                if rest.starts_with("alloc(Layout::new::<") {
                                    let rest = &rest["alloc(Layout::new::<".len()..];
                                    // Find out where the next newline is
                                    let eol = rest.find(&['\n', '\r'][..]).unwrap_or(rest.len());
                                    let rest_of_line = &rest[..eol];
                                    if let Some(pos) = rest_of_line.find(">()) as *mut ") {
                                        let type_expr = &rest_of_line[..pos];
                                        let after = &rest_of_line[pos + ">()) as *mut ".len()..];
                                        if after.starts_with(type_expr) {
                                            // We have a match!
                                            let src_len = "alloc(Layout::new::<".len() + type_expr.len() + ">()) as *mut ".len() + type_expr.len();
                                            for _ in 0..src_len {
                                                cs.next();
                                            }
                                            cs.pos.byte_pos -= src_len as u32;
                                            output.push_str("VeriFast_alloc ::  <");
                                            output.push_str(type_expr);
                                            output.push_str(">(");
                                            let output_len = "VeriFast_alloc ::  <".len() + type_expr.len() + ">()".len();
                                            cs.pos.byte_pos += output_len as u32;
                                            for _ in 0..src_len as i32 - output_len as i32 {
                                                output.push(' '); // Keep the output length the same for simplicity
                                                cs.pos.byte_pos += 1;
                                            }
                                            output.push(')');
                                            inside_word = false;
                                            break;
                                        }
                                    }
                                }
                            } else if c == 'd' && !was_inside_word {
                                // Check for 'dealloc(ptr as *mut u8, Layout::new::<T>())'
                                let rest = &input[cs.src_pos as usize..];
                                if rest.starts_with("dealloc(") {
                                    let byte_pos = cs.pos.byte_pos;
                                    let rest = &rest["dealloc(".len()..];
                                    // Find out where the next newline is
                                    let eol = rest.find(&['\n', '\r'][..]).unwrap_or(rest.len());
                                    let rest_of_line = &rest[..eol];
                                    if let Some(pos) = rest_of_line.find(" as *mut u8, Layout::new::<") {
                                        let ptr_expr = &rest_of_line[..pos];
                                        let after = &rest_of_line[pos + " as *mut u8, Layout::new::<".len()..];
                                        if let Some(end_pos) = after.find(">())") {
                                            let type_expr = &after[..end_pos];
                                            // We have a match!
                                            let src_len = "dealloc(".len() + ptr_expr.len() + " as *mut u8, Layout::new::<".len() + type_expr.len() + ">())".len();
                                            for _ in 0..src_len {
                                                cs.next();
                                            }
                                            output.push_str("VF_free(");
                                            output.push_str(ptr_expr);
                                            // " as *mut u8, Layout::new::<"
                                            // " as *mut u8 as *mut        "
                                            output.push_str(" as *mut u8 as *mut        ");
                                            output.push_str(type_expr);
                                            output.push_str("   )");
                                            inside_word = false;
                                            break;
                                        }
                                    }
                                }
                            }
                            cs.next();
                            output.push(c);
                            next_block_is_fn_body |= old_last_token_was_fn;
                            inside_word = true;
                            break;
                        }
                    }
                    '(' => {
                        cs.next();
                        output.push(c);
                    }
                    c @ (' ' | '\n' | '\r' | '\t') => {
                        inside_whitespace = true;
                        if !was_inside_whitespace {
                            start_of_whitespace = cs.pos;
                            ghost_range_seen_since_last_token = false;
                        }
                        cs.next();
                        output.push(c);
                        last_token_was_fn = old_last_token_was_fn;
                    }
                    c => {
                        cs.next();
                        output.push(c);
                        next_block_is_fn_body |= old_last_token_was_fn;
                    }
                }
            }
        }
    }
}
