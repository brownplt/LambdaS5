
(* Very simple functions to work with html.
   I haven't found anything in the standard libraries to help with this. *)

let doctype = "<!DOCTYPE html PUBLIC \"-//W3C//DTD XHTML 1.0 Strict//EN\" \"http://www.w3.org/TR/xhtml1/DTD/xhtml1-strict.dtd\">"

let rec compose funcs = match funcs with
  | [] -> fun x -> x
  | (func :: funcs) -> fun x -> func ((compose funcs) x)

let escape_pre =
  let replace pattern template str =
	  Str.global_replace (Str.regexp pattern) template str in
  compose [replace "<" "&lt;"; replace ">" "&gt;"]

let escape_html =
  let replace pattern template str =
	  Str.global_replace (Str.regexp pattern) template str in
  compose [replace "&" "&amp;"; replace "<" "&lt;";
		   replace ">" "&gt;"; replace "\"" "&quot;"; replace "'" "&#39;"]

type attrs = (string * string) list

type html =
  | Text of string
  | Pre of attrs * string (* attributes, inner-text *)
  | Tag of string * attrs * html list (* tag-name, attributes, children *)

let rec string_of_html html =
  let string_of_attr (attr, value) =
	  " " ^ escape_html attr ^ "=\"" ^ escape_html value ^ "\"" in
  let string_of_attrs attrs =
    String.concat "" (List.map string_of_attr attrs) in
  let string_of_tag tag attrs body_text =
	  let open_tag = "<" ^ escape_html tag ^ string_of_attrs attrs ^ ">" in
	  let close_tag = "</" ^ escape_html tag ^ ">" in
    open_tag ^ body_text ^ close_tag in
  match html with
  | Text text -> escape_html text
  | Pre (attrs, text) -> string_of_tag "pre" attrs (escape_pre text)
  | Tag (tag, attrs, children) ->
	  let body = String.concat "\n" (List.map string_of_html children) in
    string_of_tag tag attrs body

(* Html elements *)

let tag tag_name attrs children = Tag (tag_name, attrs, children)

let text str = Text str

let pre str = Pre ([], str)

let style (css_class: string) (html: html) : html =
  let class_attr = ("class", css_class) in
  match html with
  | Text text -> tag "span" [class_attr] [html]
  | Pre (attrs, text) -> Pre (class_attr :: attrs, text)
  | Tag (name, attrs, children) -> tag name (class_attr :: attrs) children

let cell (children: html list) : html =
  tag "td" [] children

let row (cells: html list) : html =
  tag "tr" [] cells

let table (rows: html list) : html =
  tag "table" [] rows

let anchor (id: string) (children: html list) : html =
  tag "a" [("name", id)] children

let link (id: string) (children: html list) : html =
  tag "a" [("href", id)] children

let anchor_link id children = link ("#" ^ id) children


(* Document construction *)

let html_document (title: string) (style_sheets: string list) (body: html list) : string =
  let stylesheet id = tag "link" [("rel", "stylesheet");
								                  ("type", "text/css");
								                  ("href", id)] [] in
  let stylesheets = List.map stylesheet style_sheets in
  let head = tag "head" [] (tag "title" [] [text title] :: stylesheets) in
  let body = tag "body" [] body in
  doctype ^ "\n" ^ string_of_html (tag "html" [] [head; body])
