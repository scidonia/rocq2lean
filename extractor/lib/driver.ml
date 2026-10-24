(** Drive a Rocq session sentence by sentence, remember what it declared, and
    read those declarations back once the file is done. *)

open Names

type decl_ref =
  | Constant of Constant.t
  | Mind of MutInd.t

type recorded = {
  reference : decl_ref;
  loc : Loc.t option;
  form : string;
}

let read_file path =
  let ic = open_in_bin path in
  Fun.protect
    ~finally:(fun () -> close_in_noerr ic)
    (fun () ->
      let n = in_channel_length ic in
      really_input_string ic n)

let source_of_path path =
  Loc.InFile
    { dirpath = Some (Filename.dirname path);
      file = Filename.basename path }

let expr_of_command (cmd : Vernacexpr.vernac_control) =
  cmd.CAst.v.Vernacexpr.expr

(** Commands whose constants come from somewhere else. They must not be emitted:
    the file did not define them. *)
let imports_library (cmd : Vernacexpr.vernac_control) =
  match expr_of_command cmd with
  | Vernacexpr.VernacSynterp (Vernacexpr.VernacRequire _)
  | Vernacexpr.VernacSynterp (Vernacexpr.VernacImport _)
  | Vernacexpr.VernacSynterp (Vernacexpr.VernacLoad _) ->
      true
  | _ -> false

(** A proof's constant only appears at [Qed]; attribute it to the sentence that
    started the proof, which is where a reader looks for it. The form follows
    the source command: `Theorem`/`Lemma` become Lean `theorem`s, a
    `Definition` proved by tactics stays a `def`. *)
let proof_start_form (cmd : Vernacexpr.vernac_control) =
  match expr_of_command cmd with
  | Vernacexpr.VernacSynPure (Vernacexpr.VernacStartTheoremProof _) -> Some "theorem"
  | Vernacexpr.VernacSynPure
      (Vernacexpr.VernacDefinition (_, _, Vernacexpr.ProveBody _)) ->
      Some "definition"
  | _ -> None

let constant_name c = Constant.to_string c
let mind_name m = MutInd.to_string m

let process ~path ?(include_proofs = true) (state : Vernac.State.t) : Jsonw.t =
  let text = read_file path in
  let parsable =
    Procq.Parsable.make
      ~loc:(Loc.initial (source_of_path path))
      (Gramlib.Stream.of_string text)
  in
  (* Everything already in the environment came from a [Require] of ours or
     from the prelude; only names that appear later are this file's. *)
  let known_constants = Hashtbl.create 4096 in
  let known_minds = Hashtbl.create 256 in
  Environ.fold_constants
    (fun c _ () -> Hashtbl.replace known_constants (constant_name c) ())
    (Global.env ()) ();
  Environ.fold_inductives
    (fun m _ () -> Hashtbl.replace known_minds (mind_name m) ())
    (Global.env ()) ();

  let recorded = ref [] in
  let record reference loc form = recorded := { reference; loc; form } :: !recorded in

  let rec loop (state : Vernac.State.t) pending =
    match
      Stm.parse_sentence ~doc:state.Vernac.State.doc state.Vernac.State.sid
        ~entry:Pvernac.main_entry parsable
    with
    | None -> ()
    | Some cmd ->
        (* [Vernac.process_expr] raises on a Rocq error (a failed proof at [Qed]
           included) and returns the state the sentence produced, so
           [Global.env ()] is the environment to diff. *)
        let state = Vernac.process_expr ~state cmd in
        let pending =
          match proof_start_form cmd with
          | Some form ->
              (match cmd.CAst.loc with
              | Some loc -> Some (loc, form)
              | None -> pending)
          | None -> pending
        in
        let new_constants = ref [] in
        let new_minds = ref [] in
        Environ.fold_constants
          (fun c _ () ->
            let n = constant_name c in
            if Hashtbl.mem known_constants n then ()
            else begin
              Hashtbl.add known_constants n ();
              new_constants := c :: !new_constants
            end)
          (Global.env ()) ();
        Environ.fold_inductives
          (fun m _ () ->
            let n = mind_name m in
            if Hashtbl.mem known_minds n then ()
            else begin
              Hashtbl.add known_minds n ();
              new_minds := m :: !new_minds
            end)
          (Global.env ()) ();
        (* An inductive block must be emitted before the constants derived from
           it (its eliminators), because Lean has no forward references. *)
        let introduced =
          List.sort (fun a b -> String.compare (mind_name a) (mind_name b)) !new_minds
          |> List.map (fun m -> Mind m)
          |> fun ms ->
          List.sort (fun a b -> String.compare (constant_name a) (constant_name b)) !new_constants
          |> List.map (fun c -> Constant c)
          |> fun cs -> ms @ cs
        in
        if not (imports_library cmd) then begin
          let loc, form =
            match pending with
            | Some (loc, form) -> (Some loc, form)
            | None -> (cmd.CAst.loc, "definition")
          in
          List.iter (fun reference -> record reference loc form) introduced
        end;
        let pending = if introduced = [] then pending else None in
        loop state pending
  in
  loop state None;

  (* A constant declared inside a functor is a template, not a global: it is
     gone from the environment once the functor ends. Only what survives can be
     translated; an applied module elsewhere instantiates it and its constants
     appear in that file instead. *)
  let final_constants = Hashtbl.create 4096 in
  let final_minds = Hashtbl.create 256 in
  Environ.fold_constants
    (fun c _ () -> Hashtbl.replace final_constants (constant_name c) ())
    (Global.env ()) ();
  Environ.fold_inductives
    (fun m _ () -> Hashtbl.replace final_minds (mind_name m) ())
    (Global.env ()) ();
  let survives r =
    match r.reference with
    | Constant c -> Hashtbl.mem final_constants (constant_name c)
    | Mind m -> Hashtbl.mem final_minds (mind_name m)
  in
  let recorded_final = List.filter survives !recorded in
  let dropped_module_locals = List.length !recorded - List.length recorded_final in

  (* A primitive record's projections are supplied by Lean's `structure`; the
     kernel symbols would duplicate them. *)
  let skipped_constants = Hashtbl.create 16 in
  List.iter
    (fun r ->
      match r.reference with
      | Mind m ->
          List.iter
            (fun name -> Hashtbl.replace skipped_constants name ())
            (Readback.projection_constant_names m)
      | Constant _ -> ())
    recorded_final;

  let declarations =
    List.rev_map
      (fun r ->
        try
          match r.reference with
          | Mind m -> Readback.inductive_json ~loc:r.loc m
          | Constant c ->
              if Hashtbl.mem skipped_constants (constant_name c) then
                Jsonw.Obj
                  [ ("kind", Jsonw.Str "absorbed");
                    ("name", Jsonw.Str (constant_name c));
                    ("loc", Ir.loc_json r.loc);
                    ("why", Jsonw.Str "primitive record projection") ]
              else
                Readback.constant_json ~loc:r.loc ~form:r.form
                  ~include_proof:include_proofs c
        with e ->
          let why =
            try Pp.string_of_ppcmds (CErrors.print e) with _ -> Printexc.to_string e
          in
          Jsonw.Obj
            [ ("kind", Jsonw.Str "error");
              ("name",
               Jsonw.Str
                 (match r.reference with
                 | Constant c -> constant_name c
                 | Mind m -> mind_name m));
              ("loc", Ir.loc_json r.loc);
              ("why", Jsonw.Str why) ])
      recorded_final
  in
  Jsonw.Obj
    [ ("schema", Jsonw.Int 1);
      ("source", Jsonw.Str path);
      ("rocqVersion", Jsonw.Str Coq_config.version);
      ("droppedModuleLocals", Jsonw.Int dropped_module_locals);
      ("declarations", Jsonw.List declarations) ]
