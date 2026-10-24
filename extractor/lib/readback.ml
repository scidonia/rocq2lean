(** Reading finished declarations back out of the global environment.

    Everything here runs *after* the whole input file has been interpreted, so
    a constant declared inside a section is read in its discharged form: the
    section hypotheses are already products in its type, and nothing depends on
    the order in which the section was closed. *)

open Names

let obj fields = Jsonw.Obj fields
let str s = Jsonw.Str s
let int i = Jsonw.Int i
let list xs = Jsonw.List xs

let const_body_kind (cb : Declarations.constant_body) =
  match cb.Declarations.const_body with
  | Declarations.Undef _ -> `Axiom
  | Declarations.Def _ -> `Transparent
  | Declarations.OpaqueDef _ -> `Opaque
  | Declarations.Primitive _ -> `Primitive
  | Declarations.Symbol _ -> `Symbol

let constant_body (cb : Declarations.constant_body) =
  match cb.Declarations.const_body with
  | Declarations.Undef _ -> None
  | Declarations.Def b -> Some b
  | Declarations.OpaqueDef _ -> (
      (* Reading a [Qed] proof's term after the fact is precisely the
         "opaque access" the deprecation warns about; the kernel keeps the term,
         and a translator has no other way to obtain it. *)
      let accessor = (Library.indirect_accessor [@alert "-deprecated"]) in
      match Global.body_of_constant_body accessor cb with
      | Some (b, _, _) -> Some b
      | None -> None)
  | Declarations.Primitive _ -> None
  | Declarations.Symbol _ -> None

(** The projection constants of a primitive record are reconstructed by Lean's
    own `structure`; emitting the kernel's primitive symbols as well would only
    duplicate them. *)
let projection_constant_names (mind : MutInd.t) : string list =
  match Environ.get_projections (Global.env ()) (mind, 0) with
  | None -> []
  | Some projections ->
      Array.to_list
        (Array.map
           (fun (repr, _) -> Constant.to_string (Projection.Repr.constant repr))
           projections)

let is_proposition (ty : Constr.types) =
  try
    let env = Global.env () in
    let sigma = Evd.from_env env in
    let sort = Retyping.get_sort_of env sigma (EConstr.of_constr ty) in
    Sorts.is_prop (EConstr.ESorts.kind sigma sort)
  with _ -> false

let constant_json ~loc ~form:(supplied_form : string) ~(include_proof : bool)
    (c : Constant.t) : Jsonw.t =
  let cb = Global.lookup_constant c in
  let is_prop = is_proposition cb.Declarations.const_type in
  (* A proof term is erased at run time and, for a compatibility layer, its
     body is exactly what the translation may choose to assume instead. Dropping
     it here keeps a stdlib module's JSON to its statements. *)
  let body =
    if is_prop && not include_proof then None else constant_body cb
  in
  let kind = const_body_kind cb in
  let form =
    match kind with
    | `Axiom -> "axiom"
    | `Primitive -> "primitive"
    | `Symbol -> "symbol"
    | `Transparent | `Opaque -> if is_prop then "theorem" else supplied_form
  in
  obj
    [ ("kind", str "constant");
      ("name", str (Constant.to_string c));
      ("short", str (Label.to_string (Constant.label c)));
      ("loc", Ir.loc_json loc);
      ("form", str form);
      ("isProp", Jsonw.Bool is_prop);
      ("bodyAvailable", Jsonw.Bool (body <> None));
      ("hyps", Ir.named_context_json cb.Declarations.const_hyps);
      ("type", Ir.term cb.Declarations.const_type);
      ("body", match body with None -> Jsonw.Null | Some b -> Ir.term b) ]

let build_arity (realdecls : Constr.rel_context) (sort : Sorts.t) : Constr.types =
  List.fold_left
    (fun acc d ->
      match d with
      | Context.Rel.Declaration.LocalAssum (annot, ty) -> Constr.mkProd (annot, ty, acc)
      | Context.Rel.Declaration.LocalDef (annot, value, ty) ->
          Constr.mkLetIn (annot, value, ty, acc))
    (Constr.mkSort sort) realdecls

(** Drop the leading binders that the parameters contribute. Returns [None] when
    the type does not start with exactly that many products, which is the case
    for a let-bound (non-uniform) parameter: substituting it is a different
    translation, and silently shifting de Bruijn indices would be worse than
    saying so. *)
let drop_param_binders (n : int) (ty : Constr.constr) : Constr.constr option =
  let rec go n c =
    if n = 0 then Some c
    else
      match Constr.kind c with
      | Constr.Prod (_, _, cod) -> go (n - 1) cod
      | _ -> None
  in
  go n ty

let constructor_binders (ty : Constr.constr) : (Name.t * Constr.types) list option =
  let rec go acc c =
    match Constr.kind c with
    | Constr.Prod (annot, dom, cod) ->
        go ((Context.binder_name annot, dom) :: acc) cod
    | Constr.LetIn _ -> None
    | _ -> Some (List.rev acc)
  in
  go [] ty

let inductive_json ~loc (mind : MutInd.t) : Jsonw.t =
  let mb = Global.lookup_mind mind in
  let env = Global.env () in
  let params = mb.Declarations.mind_params_ctxt in
  let nparams = List.length params in
  let finite =
    match mb.Declarations.mind_finite with
    | Declarations.Finite -> "inductive"
    | Declarations.CoFinite -> "coinductive"
    | Declarations.BiFinite -> "nonrecursive"
  in
  let is_record =
    match mb.Declarations.mind_record with
    | Declarations.NotRecord -> false
    | Declarations.FakeRecord | Declarations.PrimRecord _ -> true
  in
  let types =
    Array.to_list
      (Array.mapi
         (fun type_index packet ->
           let arity_length = List.length packet.Declarations.mind_arity_ctxt - nparams in
           let realdecls =
             List.filteri (fun i _ -> i < arity_length) packet.Declarations.mind_arity_ctxt
           in
           let arity = build_arity realdecls packet.Declarations.mind_sort in
           let projection_labels =
             if not is_record then [||]
             else
               match Environ.get_projections env (mind, type_index) with
               | None -> [||]
               | Some projections ->
                   Array.map (fun (repr, _) -> Projection.Repr.label repr) projections
           in
           let ctors =
             List.mapi
               (fun ctor_index ctor_name ->
                 let user_type = packet.Declarations.mind_user_lc.(ctor_index) in
                 let stripped =
                   if nparams = 0 then Some user_type
                   else drop_param_binders nparams user_type
                 in
                 let fields =
                   if not is_record then []
                   else
                     match Option.bind stripped constructor_binders with
                     | None -> []
                     | Some binders ->
                         List.mapi
                           (fun i (name, dom) ->
                             let label =
                               if i < Array.length projection_labels then
                                 Label.to_string projection_labels.(i)
                               else match name with
                                 | Name.Name id -> Id.to_string id
                                 | Name.Anonymous -> Printf.sprintf "field%d" i
                             in
                             obj [ ("name", str label); ("type", Ir.term dom) ])
                           binders
                 in
                 obj
                   [ ("name", str (Id.to_string ctor_name));
                     ("type",
                      match stripped with
                      | None -> Jsonw.Null
                      | Some ty -> Ir.term ty);
                     ("fields", list fields) ])
               (Array.to_list packet.Declarations.mind_consnames)
           in
           obj
             [ ("name", str (Id.to_string packet.Declarations.mind_typename));
               ("arity", Ir.term arity);
               ("ctors", list ctors) ])
         mb.Declarations.mind_packets)
  in
  obj
    [ ("kind", str "inductive");
      ("name", str (MutInd.to_string mind));
      ("loc", Ir.loc_json loc);
      ("finite", str finite);
      ("mutual", Jsonw.Bool (Array.length mb.Declarations.mind_packets > 1));
      ("record", Jsonw.Bool is_record);
      ("params", Ir.rel_context_json params);
      ("types", list types) ]
