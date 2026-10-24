import Lake
open Lake DSL

package rocq2lean where
  version := v!"0.1.0"
  description := "Translate the automatically translatable fragment of Rocq (Gallina) to Lean 4, marking everything it cannot carry."
  keywords := #["rocq", "coq", "lean", "translation", "metaprogramming"]
  license := "Apache-2.0"
  licenseFiles := #["LICENSE", "NOTICE"]
  fixedToolchain := true

/-- The translator and the prelude. Generated files import `Rocq2Lean.Prelude`
and are elaborated against this library. -/
@[default_target]
lean_lib Rocq2Lean where
  globs := #[.one `Rocq2Lean, .submodules `Rocq2Lean]

/-- `rocq2lean <file.vo.json> <out.lean>`: the second half of the pipeline. The
first half is the OCaml extractor in `extractor/`, which owns the Rocq session
and writes the JSON intermediate. -/
lean_exe rocq2lean where
  root := `Rocq2Lean.Main
