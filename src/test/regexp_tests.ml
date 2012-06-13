open Prelude
open Regexp_parser
open Regexp_syntax
open Lexing

module RegexpTest = struct
  let parse_regexp str =
    let lexbuf = Lexing.from_string str in
    Regexp_parser.pattern Regexp_lexer.token lexbuf

  let tests = [
    ("Should parse beginning only", "^", [[AssertionTerm (Beginning)]]);
    ("Should parse end only", "$", [[AssertionTerm (End)]]);
    ("Should parse \\b", "\\b", [[AssertionTerm (Word)]]);

    ("Should parse \\b\\b\\b", "\\b\\b\\b",
      [[AssertionTerm (Word)];
       [AssertionTerm (Word)];
       [AssertionTerm (Word)]]);

    ("SES 1: foo", "foo", []);
    ("SES 2: Chrome", "Chrome\\\\/(\\\\d*)\\\\.", [])
  ]

  let run_test (test : string * string * Regexp_syntax.pattern) : bool * string = match test with
    | (description, regexp, expected) ->
      try
        let result = parse_regexp regexp in
          if result = expected then
            (true, description)
          else
            (false, sprintf "%s (%s) failed" description regexp)
      with
        | Failure err ->
          (false, sprintf "%s: Failed to parse %s, because %s" description regexp err)
        | _ ->
          (false, sprintf "%s: Failed to parse %s, unknown error" description regexp)

  let print_result (result : bool * string) : unit = match result with
    | (true, desc) -> printf "PASSED: %s\n" desc
    | (false, desc) -> printf "FAILED: %s\n" desc

  let main _ =
    List.iter print_result (List.map run_test tests)
end;;

RegexpTest.main ()

