open Json

let () =
  assert(parse_json "[null, true, false, 10, -5, \"Hello\", \"Bye\", \"This \\\\is a \\\"NUL\\\": \\u0000\\r\\n\", {\"This\": [\"is an\"], \"object\": \"!\"}]" =
    A [Null; B true; B false; I 10; I (-5); S "Hello"; S "Bye"; S "This \\is a \"NUL\": \x00\r\n"; O ["This", A [S "is an"]; "object", S "!"]])

let () =
  assert(parse_json "\"\\u00E9\"" = S "é"); (* LATIN SMALL LETTER E WITH ACUTE *)
  assert(parse_json "\"\\u20AC\"" = S "€"); (* EURO SIGN *)
  assert(parse_json "\"\\uFFFD\"" = S "�"); (* REPLACEMENT CHARACTER *)
  assert(parse_json "\"\\uD83C\\uDF89\"" = S "🎉") (* PARTY POPPER *)
