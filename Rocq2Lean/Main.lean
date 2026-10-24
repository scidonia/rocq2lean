import Rocq2Lean

open Rocq2Lean

/-- `rocq2lean <ir.json> <out.lean> [--strict-scripts]`. The IR is produced by
`rocq2lean-extract` (see `extractor/`), which owns the Rocq session.

`--strict-scripts` removes the `first | … | exact <term>` safety net, so a file
that elaborates proves the generated scripts themselves succeed. -/
def readFiles (paths : List String) : IO (Except String (Array File)) := do
  let mut files := #[]
  for path in paths do
    let text ← IO.FS.readFile path
    match File.parse text with
    | .ok file => files := files.push file
    | .error e => return .error s!"cannot read `{path}`: {e}"
  return .ok files

def merge (files : Array File) : File :=
  let declarations := files.foldl (fun acc f => acc ++ f.declarations) #[]
  let source := String.intercalate ", " (files.toList.map (·.source))
  let rocqVersion := files[0]!.rocqVersion
  { source, rocqVersion, declarations }

def report (f : File) (result : EmitResult) : IO Unit := do
  IO.eprintln s!"rocq2lean: {f.declarations.size} declaration(s) from `{f.source}`; \
    {result.markers.size} untranslated; {result.unresolved.size} unresolved reference(s); \
    {result.assumptions.size} motive inference(s); {result.axioms.size} stdlib axiom(s)"
  for marker in result.markers do
    IO.eprintln s!"  untranslated: {marker}"
  for name in result.unresolved do
    IO.eprintln s!"  unresolved:   {name}"
  for assumption in result.assumptions do
    IO.eprintln s!"  assumption:   {assumption}"

def parseRoots : List String → List String × List String × List String
  | "--root" :: p :: rest =>
      let (ps, as, xs) := parseRoots rest; (p :: ps, as, xs)
  | "--axiomatise-prefix" :: p :: rest =>
      let (ps, as, xs) := parseRoots rest; (ps, p :: as, xs)
  | x :: rest => let (ps, as, xs) := parseRoots rest; (ps, as, x :: xs)
  | [] => ([], [], [])

def main (args : List String) : IO UInt32 := do
  let strict := args.contains "--strict-scripts"
  let statementsOnly := args.contains "--statements-only"
  let axiomatise := args.contains "--axiomatise-theorems"
  let args := args.filter (fun a => a != "--strict-scripts" && a != "--statements-only" && a != "--axiomatise-theorems")
  match args with
  | "--join" :: output :: rest =>
      let (roots, assumePrefixes, inputs) := parseRoots rest
      if inputs.isEmpty then
        IO.eprintln "usage: rocq2lean --join <out.lean> [--root <prefix>]… <ir.json> …"
        return 2
      else
        match ← readFiles inputs with
        | .error e => IO.eprintln s!"rocq2lean: {e}"; return 1
        | .ok files => do
            let file := merge files
            let file := { file with declarations := selectClosure file.declarations roots.toArray }
            match emitFile file strict statementsOnly axiomatise assumePrefixes.toArray with
            | .error e => IO.eprintln s!"rocq2lean: {e}"; return 1
            | .ok result => do
                IO.FS.writeFile output result.text
                report file result
                return 0
  | [input, output] => do
      let text ← IO.FS.readFile input
      match File.parse text with
      | .error e =>
          IO.eprintln s!"rocq2lean: cannot read `{input}`: {e}"
          return 1
      | .ok file => do
          match emitFile file strict statementsOnly axiomatise with
          | .error e =>
              IO.eprintln s!"rocq2lean: {e}"
              return 1
          | .ok result => do
              IO.FS.writeFile output result.text
              report file result
              return 0
  | _ =>
      IO.eprintln "usage: rocq2lean <ir.json> <out.lean> [--strict-scripts] [--statements-only] [--axiomatise-theorems]\n       rocq2lean --join <out.lean> <ir.json> … [flags]"
      return 2
