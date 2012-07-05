open Format
open FormatExt
open Prelude

(* http://es5.github.com/#x15.10 *)
type pattern = disjunction

(* alternative list cannot be empty *)
and disjunction = alternative list

and alternative = term list

and term =
  | Assertion of assertion
  | Atom of atom * quantifier option

and assertion =
  | Beginning
  | End
  | Word
  | NotWord
  | QuestionEquals of disjunction
  | QuestionBang of disjunction

and quantifier =
  | JustPrefix of quantifier_prefix
  | WithQuestion of quantifier_prefix

and quantifier_prefix =
  | Times
  | Plus
  | Question
  | ExactLength of int
  | LowBound of int
  | ExactRange of int * int

and atom =
  | PatternCharacter of string
  | Dot
  | EscapedAtom of atom_escape
  | CharacterClass of character_class
  | EqualsDisjunction of disjunction
  | QuestionDisjunction of disjunction

and atom_escape =
  | DecimalEscape of int
  | CharacterEscape of character_escape
  | CharacterClassEscape of char (* one of d D s S w W *)

and character_escape =
  | ControlEscape of string (* one of f n r t v *)
  | ControlLetter of string (* alphanumeric, lower or upper *)
  | HexEscape of string
  | UnicodeEscape of string
  | IdentityEscape of string

and character_class =
  | BeginningClass of class_range list
  | NormalClass of class_range list

and class_range =
  | ClassSingle of class_atom
  | ClassPair of class_atom * class_atom

and class_atom =
  | ClassAtom of string
  | ClassEscape of class_escape

and class_escape =
  | ClassDecimalEscape of int
  | ClassBEscape
  | ClassCharacterEscape of character_escape
  | ClassCharacterClassEscape of char (* one of d D s S w W *)


let rec fmt_disjunction disjunction = squish (intersperse (text "|") (map fmt_alternative disjunction))

and fmt_alternative alternative = squish (map fmt_term alternative)

and fmt_term term = match term with
  | Assertion (assertion) -> fmt_assertion assertion
  | Atom (atom, quantifier) ->
    let formatted_a = fmt_atom atom in
    match quantifier with
      | Some quantifier -> squish [formatted_a; fmt_quantifier quantifier]
      | None -> formatted_a

and fmt_assertion assertion = match assertion with
  | Beginning -> text "^"
  | End -> text "$"
  | Word -> text "\\b"
  | NotWord -> text "\\B"
  | QuestionEquals d ->
    squish [text "(?="; fmt_disjunction d; text ")"]
  | QuestionBang d ->
    squish [text "(?!"; fmt_disjunction d; text ")"]

and fmt_atom atom = match atom with
  | _ -> text "Unimplemented atom"
(*
  | PatternCharacter of string
  | Dot
  | EscapedAtom of atom_escape
  | CharacterClass of character_class
  | EqualsDisjunction of disjunction
  | QuestionDisjunction of disjunction
*)

and fmt_quantifier quantifier = match quantifier with
  | JustPrefix (q) -> fmt_quantifier_prefix q
  | WithQuestion (q) -> squish [fmt_quantifier_prefix q; text "?"]

and fmt_quantifier_prefix qp = match qp with
  | Times -> text "*"
  | Plus -> text "+"
  | Question -> text "?"
  | ExactLength (i) -> squish [text "{"; text (string_of_int i); text "}"]
  | LowBound (i) -> squish [text "{"; text (string_of_int i); text ",}"]
  | ExactRange (l, h) ->
    squish [text "{"; text (string_of_int l); text ",";
            text (string_of_int h); text "}"]

let fmt_pattern = fmt_disjunction

let string_of_re = FormatExt.to_string fmt_pattern