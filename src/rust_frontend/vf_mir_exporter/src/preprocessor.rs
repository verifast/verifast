pub fn preprocess(input: &str) -> String {
    let mut cs = input.chars().peekable();
    let mut output = String::new();
    let mut inside_word = false;
    let mut brace_depth = 0;
    let mut next_block_is_fn_body = false;
    let mut fn_body_brace_depth = -1;
    loop {
        let was_inside_word = inside_word;
        inside_word = false;
        fn peek(cs: &mut std::iter::Peekable<std::str::Chars>) -> Option<char> {
            match cs.peek() {
                None => None,
                Some(c) => Some(*c)
            }
        }
        match peek(&mut cs) {
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
                        match peek(&mut cs) {
                            Some('/') => {
                                cs.next();
                                match peek(&mut cs) {
                                    Some('@') if fn_body_brace_depth != -1 => {
                                        cs.next();
                                        output.push_str("VeriFast_ghost_command();//@");
                                    }
                                    _ => {
                                        output.push_str("//");
                                    }
                                };
                                loop {
                                    match peek(&mut cs) {
                                        None | Some('\n') | Some('\r') => { break; }
                                        Some(c) => { cs.next(); output.push(c); }
                                    }
                                }
                            }
                            Some('*') => {
                                cs.next();
                                match peek(&mut cs) {
                                    Some('@') if fn_body_brace_depth != -1 => {
                                        cs.next();
                                        output.push_str("VeriFast_ghost_command();/*@");
                                    }
                                    _ => {
                                        output.push_str("/*");
                                    }
                                };
                                let mut nesting_depth = 0;
                                loop {
                                    match peek(&mut cs) {
                                        None => { panic!("EOF inside multiline comment"); }
                                        Some('*') => {
                                            cs.next();
                                            output.push('*');
                                            match peek(&mut cs) {
                                                None => { panic!("EOF inside multiline comment"); }
                                                Some('/') => {
                                                    cs.next();
                                                    output.push('/');
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
                                            match peek(&mut cs) {
                                                None => { panic!("EOF inside multiline comment"); }
                                                Some('*') => {
                                                    cs.next();
                                                    output.push('*');
                                                    nesting_depth += 1;
                                                }
                                                _ => {}
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
                                output.push('/');
                            }
                        }
                    }
                    '\'' => {
                        cs.next();
                        output.push('\'');
                        match peek(&mut cs) {
                            None => { panic!("EOF inside character literal"); }
                            Some('\\') => {
                                cs.next();
                                output.push('\\');
                                match peek(&mut cs) {
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
                        match peek(&mut cs) {
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
                            match peek(&mut cs) {
                                None => { panic!("EOF inside string literal"); }
                                Some('"') => {
                                    cs.next();
                                    output.push('"');
                                    break;
                                }
                                Some('\\') => {
                                    cs.next();
                                    output.push('\\');
                                    match peek(&mut cs) {
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
                            match peek(&mut cs) {
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
                                        match peek(&mut cs) {
                                            None => { panic!("EOF inside string literal"); }
                                            Some('"') => {
                                                cs.next();
                                                output.push('"');
                                                let mut nb_hashes_seen = 0;
                                                loop {
                                                    if nb_hashes_seen == nb_hashes {
                                                        break 'stringLoop;
                                                    }
                                                    match peek(&mut cs) {
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
                        match peek(&mut cs) {
                            Some('n') => {
                                cs.next();
                                output.push('n');
                                match peek(&mut cs) {
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