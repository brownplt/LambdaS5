
(* http://es5.github.com/#x15.10 *)
type pattern = disjunction

(* alternative list cannot be empty *)
and disjunction = alternative list

and alternative = term list

and term =
  | AssertionTerm of assertion
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
  | ControlEscape of char (* one of f n r t v *)
  | ControlLetter of char (* alphanumeric, lower or upper *)
  | HexEscapeSequence of string
  | UnicodeEscapeSequence of string
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


