open Prelude
open Regexp_parser
open Regexp_syntax
open Lexing
open Parsing

module RegexpTest = struct
  let parse_regexp str =
    let lexbuf = Lexing.from_string str in
    Regexp_parser.pattern Regexp_lexer.token lexbuf

  let tests = [
    ("Should parse beginning only", "^", [[Assertion (Beginning)]]);
    ("Should parse end only", "$", [[Assertion (End)]]);
    ("Should parse \\b", "\\b", [[Assertion (Word)]]);

    ("Should parse ^$^", "^$^",
      [[Assertion(Beginning);
        Assertion(End);
        Assertion(Beginning)]]);
    ("Should parse \\b\\b\\b", "\\b\\b\\b",
      [[Assertion (Word);
        Assertion (Word);
        Assertion (Word)]]);

    ("Should parse (?=$)", "(?=$)",
      [[Assertion (QuestionEquals ([[Assertion(End)]]))]]);
    ("Should parse (?!$)", "(?!$)",
      [[Assertion (QuestionBang ([[Assertion(End)]]))]]);
    ("Should parse (?!$|^)", "(?!$|^)",
      [[Assertion (QuestionBang ([[Assertion(End)];
                                  [Assertion(Beginning)]]))]]);

    ("Should parse .", ".", [[Atom (Dot, None)]]);
    ("Should parse a", "a", [[Atom (PatternCharacter "a", None)]]);
    ("Should parse a.$|^.b", "a.$|^.b",
      [[Atom (PatternCharacter "a", None);
        Atom (Dot, None);
        Assertion (End)];
       [Assertion (Beginning);
        Atom (Dot, None);
        Atom (PatternCharacter "b", None)]]);

    ("Should parse \\43", "\\43",
      [[Atom (EscapedAtom (DecimalEscape(43)), None)]]);
    ("Should parse \\b\\43", "\\b\\43",
      [[Assertion (Word);
        Atom (EscapedAtom (DecimalEscape(43)), None)]]);

    ("Should parse \\n", "\\n",
      [[Atom (EscapedAtom (CharacterEscape (ControlEscape ("\\n"))), None)]]);
    ("Should parse \\t", "\\t",
      [[Atom (EscapedAtom (CharacterEscape (ControlEscape ("\\t"))), None)]]);
    ("Should parse \\ca", "\\ca",
      [[Atom (EscapedAtom (CharacterEscape (ControlLetter ("\\ca"))), None)]]);

    ("Should parse \\xab", "\\xab",
      [[Atom (EscapedAtom (CharacterEscape (HexEscape ("xab"))), None)]]);
    (* TODO(joe): Why don't single integers work? *)
    ("Should parse \\5", "\\5",
      [[Atom (EscapedAtom (DecimalEscape 5), None)]]);
    ("Should parse \\xabc", "\\xabc",
      [[Atom (EscapedAtom (CharacterEscape (HexEscape ("xab"))), None);
        Atom (PatternCharacter "c", None)]]);
    ("Should parse \\xabd", "\\xabd",
      [[Atom (EscapedAtom (CharacterEscape (HexEscape ("xab"))), None);
        Atom (PatternCharacter "d", None)]]);

    ("Should parse \\uabde", "\\uabde",
      [[Atom (EscapedAtom (CharacterEscape (UnicodeEscape ("uabde"))), None)]]);
    ("Should parse \\u000f", "\\u000f",
      [[Atom (EscapedAtom (CharacterEscape (UnicodeEscape ("u000f"))), None)]]);
    ("Should parse \\u000fa", "\\u000fa",
      [[Atom (EscapedAtom (CharacterEscape (UnicodeEscape ("u000f"))), None);
        Atom (PatternCharacter "a", None)]]);

    ("Should parse \\]", "\\]",
      [[Atom (EscapedAtom (CharacterEscape (IdentityEscape ("\\]"))), None)]]);
    ("Should parse \\\\", "\\\\",
      [[Atom (EscapedAtom (CharacterEscape (IdentityEscape ("\\\\"))), None)]]);
    ("Should parse \\.\\&", "\\.\\&",
      [[Atom (EscapedAtom (CharacterEscape (IdentityEscape ("\\."))), None);
        Atom (EscapedAtom (CharacterEscape (IdentityEscape ("\\&"))), None)]]);

    ("SES 1: foo", "foo",
      [[Atom (PatternCharacter "f", None);
        Atom (PatternCharacter "o", None);
        Atom (PatternCharacter "o", None)]]);

    ("SES 2: Chrome", "Chrome\\\\/(\\\\d*)\\\\.", [])
  ]

  let run_test test = match test with
    | (description, regexp, expected) ->
      try
        let result = parse_regexp regexp in
          if result = expected then
            (true, description)
          else
            (false, sprintf "%s (%s) failed, got %s" description regexp
              (Regexp_syntax.string_of_re result))
      with
        | Failure err ->
          (false, sprintf "%s: Failed to parse %s, because %s" description regexp err)
       | Parse_error ->
          (false, sprintf "%s: Failed to parse %s, because of a parse error" description regexp)
(*        | _ ->
          (false, sprintf "%s: Failed to parse %s, unknown error" description regexp) *)

  let print_result (result : bool * string) : unit = match result with
    | (true, desc) -> printf "PASSED: %s\n" desc
    | (false, desc) -> printf "FAILED: %s\n" desc

  let main _ =
    List.iter print_result (List.map run_test tests)
end;;

RegexpTest.main ()

