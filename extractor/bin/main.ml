(** Command line: everything before `--` is Rocq's (so `-Q`, `-R`, `-include`
    keep working); everything after it is ours. *)

let split_args args =
  let rec go acc = function
    | "--" :: rest -> (List.rev acc, rest)
    | arg :: rest -> go (arg :: acc) rest
    | [] -> (List.rev acc, [])
  in
  go [] args

let parse_extra (opts : Coqargs.t) (args : string list) =
  let coq_args, ours = split_args args in
  let stm_opts, leftovers = Stmargs.parse_args opts coq_args in
  ((ours, stm_opts), leftovers)

let specific_usage =
  Boot.Usage.
    { executable_name = "rocq2lean-extract";
      extra_args = " -- <input.v> <output.json>";
      extra_options = "" }

(* The document's logical name is what makes a file's constants refer to
   themselves the way every other file sees them. `VoDoc` derives it from the
   output path and the `-R`/`-Q` loadpath, exactly as `rocq compile` does; with
   the interactive `Top` document every declaration would be called `Top.foo`
   and nothing would line up across files. *)
let init_extra ((ours, stm_opts) : string list * Stm.AsyncOpts.stm_opt)
    (injections : Coqargs.injection_command list) ~opts =
  match ours with
  | input :: _ -> (
      let output =
        try Filename.chop_extension input ^ ".vo"
        with Invalid_argument _ -> input ^ ".vo"
      in
      (* Rocq derives the library name from the output path. A file whose name
         is not a valid Rocq identifier (`mutual-fix.v`) cannot be a library,
         so fall back to an interactive document; its constants are then
         `Top.*`, which is fine for a file that is translated on its own. *)
      try
        let doc, sid = Stm.new_doc Stm.{ doc_type = VoDoc output; injections } in
        let state : Vernac.State.t = { doc; sid; proof = None; time = None } in
        Load.load_init_vernaculars opts ~state
      with _ -> Coqtop.init_toploop opts stm_opts injections)
  | [] -> Coqtop.init_toploop opts stm_opts injections

let run ((ours, _) : string list * Stm.AsyncOpts.stm_opt) ~opts:_ state =
  match ours with
  | input :: output :: rest
    when (rest = [] || rest = [ "--no-proof-bodies" ]) -> (
      let include_proofs = rest = [] in
      try
        let json = Driver.process ~path:input ~include_proofs state in
        let channel = open_out_bin output in
        Fun.protect
          ~finally:(fun () -> close_out_noerr channel)
          (fun () -> output_string channel (Jsonw.to_string json))
      with e ->
        (* Rocq errors carry a location and a formatted message; an OCaml
           backtrace would drop both. *)
        let message =
          try Pp.string_of_ppcmds (CErrors.print e) with _ -> Printexc.to_string e
        in
        Printf.eprintf "rocq2lean-extract: %s\n" message;
        exit 1)
  | _ ->
      prerr_endline "usage: rocq2lean-extract [rocq flags] -- <input.v> <output.json>";
      exit 2

let () =
  let custom =
    { Coqtop.parse_extra;
      usage = specific_usage;
      init_extra;
      initial_args = Coqargs.default;
      run }
  in
  Coqtop.start_coq custom (List.tl (Array.to_list Sys.argv))
