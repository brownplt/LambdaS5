
type html
type html_document

(* tagName, attrList, children *)
val tag : string -> (string * string) list -> html list -> html

val style : string -> html -> html

val text : string -> html

val pre : string -> html

val header : int -> string -> html

val div : html list -> html

val cell : html list -> html

val row : html list -> html

val table : html list -> html

val defns : (string * html) list -> html

val anchor : string -> html list -> html

val link : string -> html list -> html

val anchor_link : string -> html list -> html

(* title, stylesheets, scripts, body *)
val document : string -> string list -> string list -> html list -> html_document

val string_of_html : html -> string

val string_of_document : html_document -> string

(* Useful when your html is longer than Sys.max_string_length *)
val print_html : html -> unit

val print_document : html_document -> unit
