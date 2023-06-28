open Pp
open CErrors
open Util
open Names
open Constr
open Context
open Termops
open EConstr
open Vars
open Pattern
open Patternops
open Context.Rel.Declaration


type binding_bound_vars1 = Id.Set.t


let warn_meta_collision =
  CWarnings.create ~name:"meta-collision" ~category:CWarnings.CoreCategories.ltac
         (fun name ->
          strbrk "Collision between bound variable " ++ Id.print name ++
            strbrk " and a metavariable of same name.")


let constrain sigma n (ids, m) ((names,seen as names_seen), terms as subst) =
  let open EConstr in
  try
    let (ids', m') = Id.Map.find n terms in
    if List.equal Id.equal ids ids' && eq_constr sigma m m' then subst
    else raise Constr_matching.PatternMatchingFailure
  with Not_found ->
    let () = if Id.Map.mem n names then warn_meta_collision n in
    (names_seen, Id.Map.add n (ids, m) terms)

let add_binders na1 na2 binding_vars ((names,seen), terms as subst) =
  match na1, na2.binder_name with
  | Name id1, Name id2 when Id.Set.mem id1 binding_vars ->
    if Id.Map.mem id1 names then
      let () = Glob_ops.warn_variable_collision id1 in
      subst
    else
      let id2 = Namegen.next_ident_away id2 seen in
      let names = Id.Map.add id1 id2 names in
      let seen = Id.Set.add id2 seen in
      let () = if Id.Map.mem id1 terms then
        warn_meta_collision id1 in
      ((names,seen), terms)
  | _ -> subst

let rec build_lambda sigma vars ctx m = match vars with
| [] ->
  if Vars.closed0 sigma m then m else raise Constr_matching.PatternMatchingFailure
| n :: vars ->
  (* change [ x1 ... xn y z1 ... zm |- t ] into
     [ x1 ... xn z1 ... zm |- lam y. t ] *)
  let pre, suf = List.chop (pred n) ctx in
  let (na, t, suf) = match suf with
  | [] -> assert false
  | (_, id, t) :: suf ->
     (map_annot Name.mk_name id, t, suf)
  in
  (* Check that the abstraction is legal by generating a transitive closure of
     its dependencies. *)
  let is_nondep t clear = match clear with
  | [] -> true
  | _ ->
    let rels = free_rels sigma t in
    let check i b = b || not (Int.Set.mem i rels) in
    List.for_all_i check 1 clear
  in
  let fold (_, _, t) clear = is_nondep t clear :: clear in
  (* Produce a list of booleans: true iff we keep the hypothesis *)
  let clear = List.fold_right fold pre [false] in
  let clear = List.drop_last clear in
  (* If the conclusion depends on a variable we cleared, failure *)
  let () = if not (is_nondep m clear) then raise Constr_matching.PatternMatchingFailure in
  (* Create the abstracted term *)
  let fold (k, accu) keep =
    if keep then
      let k = succ k in
      (k, Some k :: accu)
    else (k, None :: accu)
  in
  let keep, shift = List.fold_left fold (0, []) clear in
  let shift = List.rev shift in
  let map = function
  | None -> mkProp (* dummy term *)
  | Some i -> mkRel (i + 1)
  in
  (* [x1 ... xn y z1 ... zm] -> [x1 ... xn f(z1) ... f(zm) y] *)
  let subst =
    List.map map shift @
    mkRel 1 ::
    List.mapi (fun i _ -> mkRel (i + keep + 2)) suf
  in
  let map i (na, id, c) =
    let i = succ i in
    let subst = List.skipn i subst in
    let subst = List.map (fun c -> Vars.lift (- i) c) subst in
    (na, id, substl subst c)
  in
  let pre = List.mapi map pre in
  let pre = List.filter_with clear pre in
  let m = substl subst m in
  let map i =
    if i > n then i - n + keep
    else match List.nth shift (i - 1) with
    | None ->
      (* We cleared a variable that we wanted to abstract! *)
      raise Constr_matching.PatternMatchingFailure
    | Some k -> k
  in
  let vars = List.map map vars in
  (* Create the abstraction *)
  let m = mkLambda (na, Vars.lift keep t, m) in
  build_lambda sigma vars (pre @ suf) m

let rec extract_bound_aux k accu frels ctx = match ctx with
| [] -> accu
| (na, _, _) :: ctx ->
  if Int.Set.mem k frels then
    begin match na with
    | Name id ->
      let () = if Id.Set.mem id accu then raise Constr_matching.PatternMatchingFailure in
      extract_bound_aux (k + 1) (Id.Set.add id accu) frels ctx
    | Anonymous -> raise Constr_matching.PatternMatchingFailure
    end
  else extract_bound_aux (k + 1) accu frels ctx

let extract_bound_vars frels ctx =
  extract_bound_aux 1 Id.Set.empty frels ctx

let dummy_constr = EConstr.mkProp

let make_renaming ids = function
| (Name id, _, _) ->
  begin
    try EConstr.mkRel (List.index Id.equal id ids)
    with Not_found -> dummy_constr
  end
| _ -> dummy_constr

let push_binder na1 na2 t ctx =
  let id2 = map_annot (function
      | Name id2 -> id2
      | Anonymous ->
        let avoid = Id.Set.of_list (List.map (fun (_,id,_) -> id.binder_name) ctx) in
        Namegen.next_ident_away Namegen.default_non_dependent_ident avoid) na2
  in
  (na1, id2, t) :: ctx

(* This is an optimization of the main pattern-matching which shares
   the longest common prefix of the body and type of a fixpoint. The
   only practical effect at the time of writing is in binding variable
   names: these variable names must be bound only once since the user
   view at a fix displays only a (maximal) shared common prefix *)

let rec match_under_common_fix_binders sorec sigma binding_vars ctx ctx' env env' subst t1 t2 b1 b2 =
  match t1, EConstr.kind sigma t2, b1, EConstr.kind sigma b2 with
  | PProd(na1,c1,t1'), Prod(na2,c2,t2'), PLambda (_,c1',b1'), Lambda (na2',c2',b2') ->
     let ctx = push_binder na1 na2 c2 ctx in
     let ctx' = push_binder na1 na2' c2' ctx' in
     let env = EConstr.push_rel (LocalAssum (na2,c2)) env in
     let subst = sorec ctx env subst c1 c2 in
     let subst = sorec ctx env subst c1' c2' in
     let subst = add_binders na1 na2 binding_vars subst in
     match_under_common_fix_binders sorec sigma binding_vars
       ctx ctx' env env' subst t1' t2' b1' b2'
  | PLetIn(na1,c1,u1,t1), LetIn(na2,c2,u2,t2), PLetIn(_,c1',u1',b1), LetIn(na2',c2',u2',b2) ->
     let ctx = push_binder na1 na2 u2 ctx in
     let ctx' = push_binder na1 na2' u2' ctx' in
     let env = EConstr.push_rel (LocalDef (na2,c2,t2)) env in
     let subst = sorec ctx env subst c1 c2 in
     let subst = sorec ctx env subst c1' c2' in
     let subst = Option.fold_left (fun subst u1 -> sorec ctx env subst u1 u2) subst u1 in
     let subst = Option.fold_left (fun subst u1' -> sorec ctx env subst u1' u2') subst u1' in
     let subst = add_binders na1 na2 binding_vars subst in
     match_under_common_fix_binders sorec sigma binding_vars
       ctx ctx' env env' subst t1 t2 b1 b2
  | _ ->
     sorec ctx' env' (sorec ctx env subst t1 t2) b1 b2

let merge_binding sigma allow_bound_rels ctx n cT subst =
  let c = match ctx with
  | [] -> (* Optimization *)
    ([], cT)
  | _ ->
    let frels = free_rels sigma cT in
    if allow_bound_rels then
      let vars = extract_bound_vars frels ctx in
      let ordered_vars = Id.Set.elements vars in
      let rename binding = make_renaming ordered_vars binding in
      let renaming = List.map rename ctx in
      (ordered_vars, Vars.substl renaming cT)
    else
      let depth = List.length ctx in
      let min_elt = try Int.Set.min_elt frels with Not_found -> succ depth in
      if depth < min_elt then
        ([], Vars.lift (- depth) cT)
      else raise Constr_matching.PatternMatchingFailure
  in
  constrain sigma n c subst
let matches_search env sigma allow_bound_rels
  (binding_vars,pat) c =
let open EConstr in
let convref ref c =
  let open GlobRef in
  match ref, EConstr.kind sigma c with
  | VarRef id, Var id' -> Names.Id.equal id id'
  | ConstRef c, Const (c',_) -> Environ.QConstant.equal env c c'
  | IndRef i, Ind (i', _) -> Environ.QInd.equal env i i'
  | ConstructRef c, Construct (c',u) -> Environ.QConstruct.equal env c c'
  | _, _ -> false
in
let rec sorec ctx env subst p t =
  let cT = strip_outer_cast sigma t in
  match p, EConstr.kind sigma cT with
    | PSoApp (n,args),m ->
      let fold (ans, seen) = function
      | PRel n ->
        let () = if Int.Set.mem n seen then user_err (str "Non linear second-order pattern") in
        (n :: ans, Int.Set.add n seen)
      | _ -> user_err (str "Only bound indices allowed in second order pattern matching.")
      in
      let relargs, relset = List.fold_left fold ([], Int.Set.empty) args in
      let frels = free_rels sigma cT in
      if Int.Set.subset frels relset then
        constrain sigma n ([], build_lambda sigma relargs ctx cT) subst
      else
        raise Constr_matching.PatternMatchingFailure

    | PMeta (Some n), m -> merge_binding sigma allow_bound_rels ctx n cT subst

    | PMeta None, m -> subst

    | PRef (GlobRef.VarRef v1), Var v2 when Id.equal v1 v2 -> subst

    | PVar v1, Var v2 when Id.equal v1 v2 -> subst

    | PRef ref, _ when convref ref cT -> subst

    | PRel n1, Rel n2 when Int.equal n1 n2 -> subst

    | PSort ps, Sort s ->
      if Sorts.family_equal ps (ESorts.family sigma s)
      then subst else raise Constr_matching.PatternMatchingFailure

    | PApp (p, [||]), _ -> sorec ctx env subst p t

    | PApp (PApp (h, a1), a2), _ ->
        sorec ctx env subst (PApp(h,Array.append a1 a2)) t

    | PApp (PMeta meta,args1), App (c2,args2) ->
       (let diff = Array.length args2 - Array.length args1 in
        if diff >= 0 then
          let args21, args22 = Array.chop diff args2 in
          let c = mkApp(c2,args21) in
          let subst =
            match meta with
            | None -> subst
            | Some n -> merge_binding sigma allow_bound_rels ctx n c subst in
          Array.fold_left2 (sorec ctx env) subst args1 args22
        else (* Might be a projection on the right *)
          match EConstr.kind sigma c2 with
          | Proj (pr, c) ->
            (try let term = Retyping.expand_projection env sigma pr c (Array.to_list args2) in
                   sorec ctx env subst p term
             with Retyping.RetypeError _ -> raise Constr_matching.PatternMatchingFailure)
          | _ -> raise Constr_matching.PatternMatchingFailure)

    | PApp (c1,arg1), App (c2,arg2) ->
      (match c1, EConstr.kind sigma c2 with
       | PRef (GlobRef.ConstRef r), Proj (pr,c)
         when not (Environ.QConstant.equal env r (Projection.constant pr)) ->
         raise Constr_matching.PatternMatchingFailure
      | PProj (pr1,c1), Proj (pr,c) ->
        if Environ.QProjection.equal env pr1 pr then
          try Array.fold_left2 (sorec ctx env) (sorec ctx env subst c1 c) arg1 arg2
          with Invalid_argument _ -> raise Constr_matching.PatternMatchingFailure
        else raise Constr_matching.PatternMatchingFailure
      | _, Proj (pr,c) ->
        (try let term = Retyping.expand_projection env sigma pr c (Array.to_list arg2) in
               sorec ctx env subst p term
         with Retyping.RetypeError _ -> raise Constr_matching.PatternMatchingFailure)
      | _, _ ->
        try Array.fold_left2 (sorec ctx env) (sorec ctx env subst c1 c2) arg1 arg2
        with Invalid_argument _ -> raise Constr_matching.PatternMatchingFailure)

    | PApp (PRef (GlobRef.ConstRef c1), _), Proj (pr, c2)
      when not (Environ.QConstant.equal env c1 (Projection.constant pr)) ->
      raise Constr_matching.PatternMatchingFailure

    | PApp (c, args), Proj (pr, c2) ->
      (try let term = Retyping.expand_projection env sigma pr c2 [] in
             sorec ctx env subst p term
       with Retyping.RetypeError _ -> raise Constr_matching.PatternMatchingFailure)

    | PProj (p1,c1), Proj (p2,c2) when Environ.QProjection.equal env p1 p2 ->
        sorec ctx env subst c1 c2

    | PProd (na1,c1,d1), Prod(na2,c2,d2) ->
        sorec (push_binder na1 na2 c2 ctx) (EConstr.push_rel (LocalAssum (na2,c2)) env)
          (add_binders na1 na2 binding_vars (sorec ctx env subst c1 c2)) d1 d2

    | PLambda (na1,c1,d1), Lambda(na2,c2,d2) ->
        sorec (push_binder na1 na2 c2 ctx) (EConstr.push_rel (LocalAssum (na2,c2)) env)
          (add_binders na1 na2 binding_vars (sorec ctx env subst c1 c2)) d1 d2

    | PLetIn (na1,c1,Some t1,d1), LetIn(na2,c2,t2,d2) ->
        sorec (push_binder na1 na2 t2 ctx) (EConstr.push_rel (LocalDef (na2,c2,t2)) env)
          (add_binders na1 na2 binding_vars (sorec ctx env (sorec ctx env subst c1 c2) t1 t2)) d1 d2

    | PLetIn (na1,c1,None,d1), LetIn(na2,c2,t2,d2) ->
        sorec (push_binder na1 na2 t2 ctx) (EConstr.push_rel (LocalDef (na2,c2,t2)) env)
          (add_binders na1 na2 binding_vars (sorec ctx env subst c1 c2)) d1 d2

    | PIf (a1,b1,b1'), Case (ci, u2, pms2, p2, iv, a2, ([|b2;b2'|] as br2)) ->
        let (_, _, _, p2, _, _, br2) = EConstr.annotate_case env sigma (ci, u2, pms2, p2, iv, a2, br2) in
        let ctx_b2,b2 = br2.(0) in
        let ctx_b2',b2' = br2.(1) in
        let n = Context.Rel.length ctx_b2 in
        let n' = Context.Rel.length ctx_b2' in
        if Vars.noccur_between sigma 1 n b2 && Vars.noccur_between sigma 1 n' b2' then
          let f l (LocalAssum (na,t) | LocalDef (na,_,t)) = push_binder Anonymous na t l in
          let ctx_br = List.fold_left f ctx ctx_b2 in
          let ctx_br' = List.fold_left f ctx ctx_b2' in
          let b1 = lift_pattern n b1 and b1' = lift_pattern n' b1' in
          sorec ctx_br' (push_rel_context ctx_b2' env)
            (sorec ctx_br (push_rel_context ctx_b2 env)
               (sorec ctx env subst a1 a2) b1 b2) b1' b2'
        else
          raise Constr_matching.PatternMatchingFailure

    | PCase (ci1, p1, a1, br1), Case (ci2, u2, pms2, p2, iv, a2, br2) ->
        let (_, _, _, p2, _, _, br2) = EConstr.annotate_case env sigma (ci2, u2, pms2, p2, iv, a2, br2) in
        let n2 = Array.length br2 in
        let () = match ci1.cip_ind with
        | None -> ()
        | Some ind1 ->
          (* ppedrot: Something spooky going here. The comparison used to be
             the generic one, so I may have broken something. *)
          if not (Environ.QInd.equal env ind1 ci2.ci_ind) then raise Constr_matching.PatternMatchingFailure
        in
        let () =
          if not ci1.cip_extensible && not (Int.equal (List.length br1) n2)
          then raise Constr_matching.PatternMatchingFailure
        in
        let sorec_under_ctx subst (n, c1) (decls, c2) =
          let env = push_rel_context decls env in
          let rec fold (ctx, subst) nas decls = match nas, decls with
          | [], _ ->
            (* Historical corner case: less bound variables are allowed in
              destructuring let-bindings. See #13735. *)
              (ctx, subst)
          | na1 :: nas, d :: decls ->
            let na2 = Context.Rel.Declaration.get_annot d in
            let t = Context.Rel.Declaration.get_type d in
            let ctx = push_binder na1 na2 t ctx in
            let subst = add_binders na1 na2 binding_vars subst in
            fold (ctx, subst) nas decls
          | _, [] ->
            assert false
          in
          let ctx, subst = fold (ctx, subst) (Array.to_list n) (List.rev decls) in
          sorec ctx env subst c1 c2
        in
        let chk_branch subst (j,n,c) =
          (* (ind,j+1) is normally known to be a correct constructor
             and br2 a correct match over the same inductive *)
          assert (j < n2);
          sorec_under_ctx subst (n, c) br2.(j)
        in
        let subst = sorec ctx env subst a1 a2 in
        let subst = match p1 with
        | None -> subst
        | Some p1 -> sorec_under_ctx subst p1 p2
        in
        List.fold_left chk_branch subst br1

    |	PFix ((ln1,i1),(lna1,tl1,bl1)), Fix ((ln2,i2),(lna2,tl2,bl2))
         when Array.equal Int.equal ln1 ln2 && i1 = i2 ->
        let ctx' = Array.fold_left3 (fun ctx na1 na2 t2 -> push_binder na1 na2 t2 ctx) ctx lna1 lna2 tl2 in
        let env' = Array.fold_left2 (fun env na2 c2 -> EConstr.push_rel (LocalAssum (na2,c2)) env) env lna2 tl2 in
        let subst = Array.fold_left4 (match_under_common_fix_binders sorec sigma binding_vars ctx ctx' env env') subst tl1 tl2 bl1 bl2 in
        Array.fold_left2 (fun subst na1 na2 -> add_binders na1 na2 binding_vars subst) subst lna1 lna2

    |	PCoFix (i1,(lna1,tl1,bl1)), CoFix (i2,(lna2,tl2,bl2))
         when i1 = i2 ->
        let ctx' = Array.fold_left3 (fun ctx na1 na2 t2 -> push_binder na1 na2 t2 ctx) ctx lna1 lna2 tl2 in
        let env' = Array.fold_left2 (fun env na2 c2 -> EConstr.push_rel (LocalAssum (na2,c2)) env) env lna2 tl2 in
        let subst = Array.fold_left4 (match_under_common_fix_binders sorec sigma binding_vars ctx ctx' env env') subst tl1 tl2 bl1 bl2 in
        Array.fold_left2 (fun subst na1 na2 -> add_binders na1 na2 binding_vars subst) subst lna1 lna2

    | PEvar (c1,args1), Evar (c2,args2) when Evar.equal c1 c2 ->
      let args2 = Evd.expand_existential sigma (c2, args2) in
       List.fold_left2 (sorec ctx env) subst args1 args2
    | PInt i1, Int i2 when Uint63.equal i1 i2 -> subst

    | PFloat f1, Float f2 when Float64.equal f1 f2 -> subst

    | PArray(pt,pdef,pty), Array(_u,t,def,ty)
           when Array.length pt = Array.length t ->
       sorec ctx env (sorec ctx env (Array.fold_left2 (sorec ctx env) subst pt t) pdef def) pty ty

    | (PRef _ | PVar _ | PRel _ | PApp _ | PProj _ | PLambda _
       | PProd _ | PLetIn _ | PSort _ | PIf _ | PCase _
       | PFix _ | PCoFix _| PEvar _ | PInt _ | PFloat _ | PArray _), _ -> raise Constr_matching.PatternMatchingFailure

in
sorec [] env ((Id.Map.empty,Id.Set.empty), Id.Map.empty) pat c
