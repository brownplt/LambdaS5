open Prelude

(* Very simple functions to work with html.
   I haven't found anything in the standard libraries to help with this,
   and bringing in a web framework would likely be overkill. *)


let doctype = "<!DOCTYPE html PUBLIC \"-//W3C//DTD XHTML 1.0 Strict//EN\" \"http://www.w3.org/TR/xhtml1/DTD/xhtml1-strict.dtd\">"

type attrs = (string * string) list

type html =
  | Text of string (* inner text *)
  | Tag of string * attrs * html list (* attributes, inner text *)

type html_document = Document of html


(* Escaping *)

type replacer = Str.regexp * string
  
let lt_replacement = (Str.regexp "<", "&lt;")
let gt_replacement = (Str.regexp ">", "&gt;")
let quot_replacement = (Str.regexp "\"", "&quot;")
let apo_replacement = (Str.regexp "'", "&#39;")
  
let replace (regex, replacement) string =
  Str.global_replace regex replacement string
    
let escape_pre = apply replace [lt_replacement; gt_replacement]
let escape_html = apply replace [lt_replacement; gt_replacement;
                                 quot_replacement; apo_replacement]


(* Constructors *)

let tag tag_name attrs children =
  let tag_name = escape_html tag_name in
  let attrs = List.map (fun (a, v) -> (escape_html a, escape_html v)) attrs in
  Tag (tag_name, attrs, children)
    
let text str = Text (escape_html str)
  
let pre str = tag "pre" [] [Text (escape_pre str)]

let style (css_class: string) (html: html) : html =
  let class_attr = ("class", css_class) in
  match html with
  | Text text -> tag "span" [class_attr] [html]
  | Tag (name, attrs, children) -> tag name (class_attr :: attrs) children


(* Printing *)

let generic_print_html print html =
  let print_tag tag attrs print_body =
    let print_open_tag =
      let print_attr (attr, value) =
        print (" " ^ attr ^ "=\"" ^ value ^ "\"") in
      compose [print ("<" ^ escape_html tag);
               apply print_attr attrs;
               print ">"] in
    let print_close_tag = print ("</" ^ tag ^ ">") in
    compose [print_open_tag; print_body; print_close_tag] in
  let rec print_html html =
    match html with
    | Text text -> print text
    | Tag (tag, attrs, children) ->
      print_tag tag attrs (apply print_html children) in  
  print_html html

let generic_print_document print (Document html) =
  compose [print (doctype ^ "\n");
           generic_print_html print html]


let print = fun str () -> print_string str

let string_of_html html = generic_print_html (^) html ""
let string_of_document doc = generic_print_document (^) doc ""
let print_html html = generic_print_html print html ()
let print_document doc = generic_print_document print doc ()


(* Html Elements *)
(* DONT PATTERN MATCH! *)

let header (n: int) (string: string) : html =
  tag ("h" ^ string_of_int n) [] [text string]

let div (children: html list) : html =
  tag "div" [] children

let cell (children: html list) : html =
  tag "td" [] children

let row (cells: html list) : html =
  tag "tr" [] cells

let table (rows: html list) : html =
  tag "table" [] rows

let defns (definitions: (string * html) list) : html =
  let defn (word, definition) =
    [tag "dt" [] [tag "strong" [] [text word]];
     tag "dd" [] [definition]] in
  tag "dl" [] (List.concat (List.map defn definitions))

let anchor (id: string) (children: html list) : html =
  tag "a" [("name", id)] children

let link (id: string) (children: html list) : html =
  tag "a" [("href", id)] children

let anchor_link id children = link ("#" ^ id) children

let document title stylesheets scripts body =
  let stylesheet link = tag "link" [("rel", "stylesheet");
								                    ("type", "text/css");
								                    ("href", link)] [] in
  let script link = tag "script" [("type", "text/javascript");
                                  ("src", link)] [] in
  let stylesheets = List.map stylesheet stylesheets in
  let scripts = List.map script scripts in
  let title = tag "title" [] [text title] in
  let head = tag "head" [] (title :: stylesheets @ scripts) in
  let body = tag "body" [] body in
  Document (tag "html" [] [head; body])
