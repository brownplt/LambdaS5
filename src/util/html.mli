
type html

(* tagName, attrList, children *)
val tag : string -> (string * string) list -> html list -> html

val style : string -> html -> html

val text : string -> html

val pre : string -> html

val cell : html list -> html

val row : html list -> html

val table : html list -> html

val anchor : string -> html list -> html

val link : string -> html list -> html

val anchor_link : string -> html list -> html

(* title, styleSheets, body *)
val html_document : string -> string list -> html list -> string
