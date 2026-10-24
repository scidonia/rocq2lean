# Notes for agents working in this repository

## Toolchain

Everything that needs the toolchain runs through the dev shell:

```console
$ nix develop -c <command>
$ ./tests/run.sh            # re-enters the shell itself
```

Never require an activated shell, `direnv allow`, or inherited `OCAMLPATH`.
`tests/run.sh` is the end-to-end gate; a change is not done until it passes.

* Lean is pinned by `lean-toolchain` (4.35.0) and comes from nixpkgs.
* Rocq is `pkgs.rocqPackages.rocq-core` (9.1.1) and is an **OCaml 4.14** build.
  The extractor links `rocq-runtime.*` with that compiler; do not add OCaml
  dependencies without adding them to `flake.nix` in the matching package set.
* The standard library is `pkgs.rocqPackages.stdlib`, reached through
  `ROCQPATH`. Sources name it `Stdlib.*` (`From Stdlib Require Import …`); the
  `Coq.*` spelling is a compatibility alias that needs extra plugins.

## What must not change silently

* **The marker token.** `ROCQ2LEAN-UNTRANSLATED` is the contract with the
  reader. Tests assert it in `basic`, `poly`, `mutual`, `mutual-fix`,
  `propositions`, `untranslatable`, and `coinductive`, and assert its absence in
  fully translatable cases.
* **A translated proof must not depend on an axiom.** `tests/run.sh` runs
  `#print axioms` on every generated theorem. Do not satisfy the check by
  weakening it.
* **No guessed defaults.** A term that cannot be expressed produces a marker,
  not a plausible-looking substitute. Do not add a catch that returns `True`,
  a stub axiom, or a declared-but-undefined name to keep a file compiling.

## Translation invariants

* Binder names must be unique in a scope (`binderFor`). Rocq allows shadowing;
  printing two shadowed binders with the same Lean name would make every
  occurrence resolve to the innermost one.
* A global in application position is written with `@` so that Lean's implicit
  binders line up with the kernel's explicit arguments. This is correct because
  the kernel's application always matches the full binder list it was applied
  to; the same reason is why `Prelude.lean` keeps Rocq's argument order.
* A kernel `Fix` body lives in `Γ, f₁ … fₖ, args`, while its type lives in `Γ`.
  `translateFixBlock` reflects that asymmetry; do not "simplify" it to one scope.
* `Case` branches are in the context extended by the constructor arguments, and
  two arguments can carry the same name. Patterns are de-duplicated.
* Emitted terms contain no newlines. Lean's layout rules make a multi-line
  `match` inside a `let` ambiguous; do not reintroduce multi-line terms without
  a layout-aware indentation scheme.
* A mutually recursive `Fix` block is refused with a marker: Lean's
  `let rec … and …` does not survive nesting in an expression.
* Script reduction (`proofLines`) may only replace a theorem's body with a
  script it can build structurally; every other shape stays `exact <term>`.
  Emitted scripts are wrapped in `first | <script> | exact <term>`, so the
  fallback is machine-checked at elaboration time. `--strict-scripts` removes
  the wrapper and `tests/run.sh` elaborates both forms; a script that only
  compiles because of the fallback therefore fails the suite.
* `scriptTerm` takes `fuel`; recursion into rewrites and branches decrements it
  and zero falls back to `exact`. Do not remove the bound: the equality rule
  duplicates its hypothesis script, so unbounded recursion grows the output.
* `betaStrip` is sound only when every argument is a variable already in scope;
  it substitutes by extending the translation scope. Do not generalise it to
  arbitrary arguments without a real substitution. `caseScript` handles one
  constructor and one branch only; multiple goals need bullets and are left as
  the `match` term.
* Rocq interleaves branch argument and hypothesis binders; Lean's `induction`
  pattern wants arguments first. Reorder in `inductionScript`, and keep the
  body scope in Rocq's order because that is what its de Bruijn indices mean.
* `induction … with` alternatives use the constructor's short name. Strip the
  namespace; `Nat.zero` is rejected in favour of `zero`.
* Declarations are registered before translation and emitted in a stable
  topological order, because Rocq's derived eliminators can appear in any order
  while Lean has no forward references.

## The mapping table is the trusted boundary

Adding a `mappedTypes` / `mappedCtors` / `mappedConstants` entry is a claim that
the Rocq global and the Lean global are interchangeable for translation. Add the
Lean definition to `Prelude.lean` with Rocq's argument order, and add a case that
elaborates a use of it. A mapping is not demonstrated by the table alone.

## Generated output

`build/` is scratch and is ignored. Generated `.lean` files are never edited by
hand and never committed.

## Interpreting a file

The extractor interprets sentences with `Vernac.process_expr`, which raises on a
Rocq error (a `Qed` with open goals included). `Stm.add`/`Stm.observe` do not:
they report the error and leave a usable document, which once produced a
successful extraction of a file that Rocq had rejected.

## CompCert-driven invariants

* A document is created as `VoDoc <input>.vo` so Rocq derives the file's logical
  name from the `-R`/`-Q` flags. Without that, every declaration is `Top.foo`
  and nothing lines up with how other files name it. Keep the interactive
  fallback only for names Rocq cannot accept as libraries.
* Constants declared inside a functor are templates, not globals: they vanish
  from the environment when the functor ends. `driver.ml` drops recorded names
  that do not survive in the final environment; an applied instance is emitted
  in the file that applies it.
* `--statements-only` replaces **theorem proofs** with `sorry`. Definition
  bodies are terms and must stay; making them opaque breaks every definitional
  equality that CompCert relies on (`PTree.t` vs `PTree.tree`).
* Mapped constructor indices follow Rocq's declaration order, which is not the
  intuitive one: `option` declares `Some` before `None`. Check the inductive in
  Rocq before adding a mapping.
* `flatten` quotes the final joined identifier. Composing names must use
  `flattenRaw`/`sanitizeComponent`; `«mutual»_expr` is not an identifier.

## Compatibility-layer invariants

* A unit is selected with `--root <prefix>`; `selectClosure` keeps declarations
  reachable from those names. Do not grow the compat layer by translating whole
  stdlib modules: the closure is what keeps 4,800 declarations down to 476.
* Proof-valued constants are recognised by the kernel sort (`isProp`), not by
  the Rocq command. `--statements-only` must never drop a definition body.
* `--axiomatise-theorems` emits `ROCQ2LEAN-ASSUMED` axioms; the file's
  `## Assumed declarations` section is the trusted base and must stay accurate.
* Coq `Type`/`Set` are emitted as Lean `Type _`: a fixed `Type` rejects a term
  whose type lives at a higher level.
* A `Case` on a non-recursive indexed inductive (`comparison`, `sumbool`) is
  emitted as its recursor with an explicit motive built from `returnBinders`;
  a `match` would have to infer that motive. The kernel motive is a type under
  the binders, not a lambda.
* A mutually recursive fixpoint body is emitted as a top-level `mutual` block
  with a unique local prefix per constant; Lean has no expression-level
  `let rec … and …` that survives nesting.
* `tests/compcert-a1.sh` and `tests/compcert-a2.sh` are the external milestone
  checks. They build from the nixpkgs CompCert source, so they are not part of
  `tests/run.sh`; keep them working when changing naming, closure selection, or
  the assumed-declaration modes. A2 uses CompCert's Makefile, which needs
  `coqdep` (the shell appends the caller's PATH); three proof-only Flocq `Prop`
  modules fail extraction as libraries and are skipped because AST never
  references them.

## Module names

`extractor/lib/` is unwrapped (`(wrapped false)`), so its module names share the
namespace with Rocq's. `readback.ml` was named `decls.ml` once and collided with
Rocq's `Decls`; keep new modules named after this project's concepts.
