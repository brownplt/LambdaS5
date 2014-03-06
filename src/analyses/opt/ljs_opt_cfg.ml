open Ljs_syntax

type Ljs_node = {
  block : Ljs_syntax.expr;
  edgesIn : ref (Ljs_node list);
  edgesOut : ref (Ljs_node list);
}

module Node = struct
  type t = Ljs_node;;
  let compare (n1 : Ljs_node) (n2 : Ljs_node) =
    ...
end

module NodeMap = Map.Make(Node);;

let build_graph (m : Ljs_syntax.expr NodeMap) (e : Ljs_syntax.expr) : Ljs_node =
