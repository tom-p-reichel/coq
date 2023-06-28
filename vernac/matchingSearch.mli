open Names
open Pattern

type binding_bound_vars1 = Id.Set.t
val matches_search : Environ.env -> Evd.evar_map ->
    bool ->
    binding_bound_vars1 * constr_pattern ->
    Evd.econstr ->
    (patvar Id.Map.t * binding_bound_vars1)
    * (patvar list * Evd.econstr) Id.Map.t