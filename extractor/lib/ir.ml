(** Serialisation of the Rocq kernel representation into the JSON intermediate.

    This module is deliberately mechanical: it records what the kernel holds and
    never decides whether Lean can express it. A constructor we cannot carry
    faithfully becomes an ["unsupported"] node, and the Lean half turns that
    into a visible marker rather than a guess. *)

open Names

let obj fields = Jsonw.Obj fields
let str s = Jsonw.Str s
let int i = Jsonw.Int i
let list xs = Jsonw.List xs

let name_json (n : Name.t) =
  match n with
  | Name.Anonymous -> Jsonw.Null
  | Name.Name id -> str (Id.to_string id)

let relevance_json (r : Sorts.relevance) =
  match r with
  | Sorts.Relevant -> str "relevant"
  | Sorts.Irrelevant -> str "irrelevant"
  | Sorts.RelevanceVar _ -> str "relevance-variable"

let sort_json (s : Sorts.t) =
  match s with
  | Sorts.Prop -> obj [ ("s", str "prop") ]
  | Sorts.SProp -> obj [ ("s", str "sprop") ]
  | Sorts.Set -> obj [ ("s", str "set") ]
  | Sorts.Type u ->
      obj
        [ ("s", str "type");
          ("level", str (Pp.string_of_ppcmds (Univ.Universe.pr Univ.Level.raw_pr u))) ]
  | Sorts.QSort _ -> obj [ ("s", str "qsort") ]

let cast_kind_name = function
  | Constr.VMcast -> "vm"
  | Constr.NATIVEcast -> "native"
  | Constr.DEFAULTcast -> "default"

let rec term (c : Constr.t) : Jsonw.t =
  match Constr.kind c with
  | Constr.Rel n -> obj [ ("t", str "rel"); ("n", int n) ]
  | Constr.Var id -> obj [ ("t", str "var"); ("id", str (Id.to_string id)) ]
  | Constr.Meta _ -> obj [ ("t", str "unsupported"); ("what", str "metavariable") ]
  | Constr.Evar _ -> obj [ ("t", str "unsupported"); ("what", str "evar") ]
  | Constr.Sort s -> obj [ ("t", str "sort"); ("sort", sort_json s) ]
  | Constr.Cast (inner, k, _) ->
      obj [ ("t", str "cast"); ("kind", str (cast_kind_name k)); ("term", term inner) ]
  | Constr.Prod (annot, dom, cod) ->
      obj
        [ ("t", str "prod");
          ("name", name_json (Context.binder_name annot));
          ("relevance", relevance_json (Context.binder_relevance annot));
          ("dom", term dom);
          ("cod", term cod) ]
  | Constr.Lambda (annot, dom, body) ->
      obj
        [ ("t", str "lambda");
          ("name", name_json (Context.binder_name annot));
          ("relevance", relevance_json (Context.binder_relevance annot));
          ("dom", term dom);
          ("body", term body) ]
  | Constr.LetIn (annot, value, ty, body) ->
      obj
        [ ("t", str "let");
          ("name", name_json (Context.binder_name annot));
          ("relevance", relevance_json (Context.binder_relevance annot));
          ("value", term value);
          ("type", term ty);
          ("body", term body) ]
  | Constr.App (fn, args) ->
      obj
        [ ("t", str "app");
          ("fn", term fn);
          ("args", list (Array.to_list (Array.map term args))) ]
  | Constr.Const (cst, _) ->
      obj [ ("t", str "const"); ("name", str (Constant.to_string cst)) ]
  | Constr.Ind ((mind, idx), _) ->
      obj
        [ ("t", str "ind");
          ("name", str (MutInd.to_string mind));
          ("index", int idx) ]
  | Constr.Construct (((mind, idx), ctor), _) ->
      obj
        [ ("t", str "ctor");
          ("name", str (MutInd.to_string mind));
          ("index", int idx);
          ("ctor", int (ctor - 1)) ]
  | Constr.Case (ci, _, params, ((return_binders, motive), _), invert, scrutinee, branches) ->
      let binder_names annots =
        list (Array.to_list (Array.map (fun a -> name_json (Context.binder_name a)) annots))
      in
      obj
        [ ("t", str "case");
          ("inductiveName", str (MutInd.to_string (fst ci.Constr.ci_ind)));
          ("inductiveIndex", int (snd ci.Constr.ci_ind));
          ("nparams", int ci.Constr.ci_npar);
          ("params", list (Array.to_list (Array.map term params)));
          ("returnBinders", binder_names return_binders);
          ("motive", term motive);
          ("invert", Jsonw.Bool (match invert with Constr.CaseInvert _ -> true | Constr.NoInvert -> false));
          ("scrutinee", term scrutinee);
          ("branches",
           list
             (Array.to_list
                (Array.map
                   (fun (binders, body) ->
                     obj
                       [ ("binders", binder_names binders);
                         ("body", term body) ])
                   branches))) ]
  | Constr.Fix ((recargs, selected), (names, types, bodies)) ->
      let n = Array.length names in
      let functions =
        List.init n (fun i ->
            obj
              [ ("name", name_json (Context.binder_name names.(i)));
                ("recArg", int recargs.(i));
                ("type", term types.(i));
                ("body", term bodies.(i)) ])
      in
      obj [ ("t", str "fix"); ("selected", int selected); ("functions", list functions) ]
  | Constr.CoFix ((selected, (names, types, bodies))) ->
      let n = Array.length names in
      let functions =
        List.init n (fun i ->
            obj
              [ ("name", name_json (Context.binder_name names.(i)));
                ("type", term types.(i));
                ("body", term bodies.(i)) ])
      in
      obj [ ("t", str "cofix"); ("selected", int selected); ("functions", list functions) ]
  | Constr.Proj (p, _, inner) ->
      obj
        [ ("t", str "proj");
          ("recordName", str (MutInd.to_string (fst (Projection.inductive p))));
          ("recordIndex", int (snd (Projection.inductive p)));
          ("field", str (Label.to_string (Projection.label p)));
          ("nparams", int (Projection.npars p));
          ("arg", int (Projection.arg p));
          ("term", term inner) ]
  | Constr.Int i -> obj [ ("t", str "int"); ("value", str (Uint63.to_string i)) ]
  | Constr.Float _ -> obj [ ("t", str "unsupported"); ("what", str "float") ]
  | Constr.String s -> obj [ ("t", str "string"); ("value", str (Pstring.to_string s)) ]
  | Constr.Array _ -> obj [ ("t", str "unsupported"); ("what", str "array") ]

(** A binder in declaration order (outermost first), with the type and optional
    let-value both written in the context of the binders before it. *)
let rel_declaration_json (d : Constr.rel_declaration) =
  obj
    [ ("name", name_json (Context.Rel.Declaration.get_name d));
      ("type", term (Context.Rel.Declaration.get_type d));
      ("value",
       match Context.Rel.Declaration.get_value d with
       | None -> Jsonw.Null
       | Some v -> term v) ]

let rel_context_json (ctx : Constr.rel_context) =
  (* The kernel stores contexts innermost first; Lean binders are written
     outermost first. *)
  list (List.rev_map rel_declaration_json ctx)

let named_declaration_json (d : Constr.named_declaration) =
  obj
    [ ("name", name_json (Name.Name (Context.Named.Declaration.get_id d)));
      ("type", term (Context.Named.Declaration.get_type d));
      ("value",
       match Context.Named.Declaration.get_value d with
       | None -> Jsonw.Null
       | Some v -> term v) ]

let named_context_json (ctx : Constr.named_context) =
  list (List.rev_map named_declaration_json ctx)

let loc_json (l : Loc.t option) =
  match l with
  | None -> Jsonw.Null
  | Some l ->
      let file =
        match l.Loc.fname with
        | Loc.InFile { file; _ } -> file
        | Loc.ToplevelInput -> "<toplevel>"
      in
      obj
        [ ("file", str file);
          ("line", int l.Loc.line_nb);
          ("column", int (l.Loc.bp - l.Loc.bol_pos)) ]
