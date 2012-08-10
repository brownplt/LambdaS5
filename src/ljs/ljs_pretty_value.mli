
val string_of_obj : Ljs_values.objectv -> Ljs_values.store -> string

val string_of_value : Ljs_values.value -> Ljs_values.store -> string

val string_of_env : Ljs_values.env -> string

val print_values : Ljs_values.store -> unit

val print_objects : Ljs_values.store -> unit
