import Rocq2Lean.IR
import Rocq2Lean.Names

/-!
# Kernel term → Lean term

The translation is structural and total on the fragment it claims: every kernel
constructor either becomes Lean syntax or fails with a reason. Failure is a
value, not a silent correction — the caller turns it into a visible marker.

Names are resolved through `Rocq2Lean.Names`; a global reference that is neither
declared by the file nor in the mapping table is emitted as its flattened name
and recorded as unresolved, so Lean reports it at the use site.

Deliberate omissions, recorded here rather than hidden:

* universe instances are erased and Lean re-infers them, because carrying
  Rocq's quality/level algebra into Lean's universe syntax is a separate
  decision;
* a `match`'s return predicate is not emitted (Lean infers the motive).

Both are assumptions, not semantics-preserving by construction.
-/

namespace Rocq2Lean

/-- What a proof-term eliminator needs to become an `induction` script. -/
structure ElimBranch where
  ctor : Nat
  args : Nat
  ihs : Nat
  /-- One flag per constructor argument: does it carry an induction hypothesis?
  Rocq's branch telescope interleaves argument and hypothesis (`l IHl r IHr`);
  Lean's `induction` pattern takes all arguments first (`l r IHl IHr`). -/
  recursive : Array Bool
  deriving Inhabited, Repr

structure ElimInfo where
  block : String
  indIndex : Nat
  params : Nat
  indices : Nat
  branches : Array ElimBranch
  deriving Inhabited, Repr

/-- Eliminators from the mapped prelude. Their Rocq names, parameter counts and
branch shapes are fixed by the standard library; a local inductive registers the
same information from its own kernel declaration. -/
def builtinEliminators : List (String × ElimInfo) :=
  let natInfo (name : String) :=
    (name, { block := "Corelib.Init.Datatypes.nat", indIndex := 0, params := 0, indices := 0,
             branches := #[⟨0, 0, 0, #[]⟩, ⟨1, 1, 1, #[true]⟩] : ElimInfo })
  let boolInfo (name : String) :=
    (name, { block := "Corelib.Init.Datatypes.bool", indIndex := 0, params := 0, indices := 0,
             branches := #[⟨0, 0, 0, #[]⟩, ⟨1, 0, 0, #[]⟩] : ElimInfo })
  let listInfo (name : String) :=
    (name, { block := "Corelib.Init.Datatypes.list", indIndex := 0, params := 1, indices := 0,
             branches := #[⟨0, 0, 0, #[]⟩, ⟨1, 2, 1, #[false, true]⟩] : ElimInfo })
  let optionInfo (name : String) :=
    (name, { block := "Corelib.Init.Datatypes.option", indIndex := 0, params := 1, indices := 0,
             branches := #[⟨0, 0, 0, #[]⟩, ⟨1, 1, 0, #[false]⟩] : ElimInfo })
  let andInfo :=
    ("Corelib.Init.Logic.and_ind",
     { block := "Corelib.Init.Logic.and", indIndex := 0, params := 2, indices := 0,
       branches := #[⟨0, 2, 0, #[false, false]⟩] : ElimInfo })
  let orInfo :=
    ("Corelib.Init.Logic.or_ind",
     { block := "Corelib.Init.Logic.or", indIndex := 0, params := 2, indices := 0,
       branches := #[⟨0, 1, 0, #[false]⟩, ⟨1, 1, 0, #[false]⟩] : ElimInfo })
  let exInfo :=
    ("Corelib.Init.Logic.ex_ind",
     { block := "Corelib.Init.Logic.ex", indIndex := 0, params := 2, indices := 0,
       branches := #[⟨0, 2, 0, #[false, false]⟩] : ElimInfo })
  [ andInfo, orInfo, exInfo
  , natInfo "Corelib.Init.Datatypes.nat_ind"
  , natInfo "Corelib.Init.Datatypes.nat_rect"
  , natInfo "Corelib.Init.Datatypes.nat_rec"
  , boolInfo "Corelib.Init.Datatypes.bool_ind"
  , boolInfo "Corelib.Init.Datatypes.bool_rect"
  , boolInfo "Corelib.Init.Datatypes.bool_rec"
  , listInfo "Corelib.Init.Datatypes.list_ind"
  , listInfo "Corelib.Init.Datatypes.list_rect"
  , listInfo "Corelib.Init.Datatypes.list_rec"
  , optionInfo "Corelib.Init.Datatypes.option_ind"
  , optionInfo "Corelib.Init.Datatypes.option_rect"
  , optionInfo "Corelib.Init.Datatypes.option_rec" ]

def builtinEliminator (name : String) : Option ElimInfo :=
  (builtinEliminators.find? fun (n, _) => n == name).map Prod.snd

/-- Translation state: what this unit declared, what it could not resolve, and
what it refused to translate. -/
structure TrState where
  declared : Std.HashMap String String := {}
  eliminators : Std.HashMap String ElimInfo := {}
  indTypes : Std.HashMap (String × Nat) String := {}
  ctors : Std.HashMap (String × Nat × Nat) String := {}
  unresolved : Array String := #[]
  markers : Array String := #[]
  assumptions : Array String := #[]
  axioms : Array String := #[]
  /-- Strict mode omits the `first | … | exact term` safety net, so a test can
  prove that the script itself succeeds rather than silently falling back. -/
  strict : Bool := false
  /-- Emit statements and `sorry` instead of proof terms. This is how a file
  whose proofs are out of reach (for now) still yields a usable interface. -/
  statementsOnly : Bool := false
  /-- Turn proof-valued declarations into axioms instead of `sorry` theorems,
  under the `ROCQ2LEAN-STDLIB-AXIOM` marker. -/
  axiomatise : Bool := false
  /-- Declarations whose Rocq name starts with one of these are assumed, not
  translated, even when they are definitions. Used for stdlib modules whose
  definitions are not needed for computation in the target. -/
  assumePrefixes : Array String := #[]
  current : String := ""
  fresh : Nat := 0

abbrev TrM := StateT TrState (Except String)

namespace TrM

def fail (msg : String) : TrM α :=
  throw msg

def freshName : TrM String := do
  let st ← get
  set { st with fresh := st.fresh + 1 }
  return s!"_a{st.fresh}"

def freshNameAvoiding (scope : Array String) : TrM String := do
  let mut n ← freshName
  while scope.contains n do
    n ← freshName
  return n

def addUnresolved (n : String) : TrM Unit := do
  let st ← get
  unless st.unresolved.contains n do
    set { st with unresolved := st.unresolved.push n }

def addMarker (m : String) : TrM Unit := do
  let st ← get
  set { st with markers := st.markers.push m }

/-- Record a place where the output relies on Lean inferring something this
translation does not write down. -/
def addAssumption (m : String) : TrM Unit := do
  let st ← get
  let entry := if st.current.isEmpty then m else s!"{st.current}: {m}"
  unless st.assumptions.contains entry do
    set { st with assumptions := st.assumptions.push entry }

def strictEnabled : TrM Bool := do
  return (← get).strict

def statementsOnly : TrM Bool := do
  return (← get).statementsOnly

def axiomatiseEnabled : TrM Bool := do
  return (← get).axiomatise

def addAxiom (m : String) : TrM Unit := do
  let st ← get
  set { st with axioms := st.axioms.push m }

def declare (rocq lean : String) : TrM Unit := do
  let st ← get
  set { st with declared := st.declared.insert rocq lean }

/-- Run to completion, returning the value and the final state. -/
def run (comp : TrM α) (st : TrState := {}) : Except String (α × TrState) :=
  StateT.run comp st

end TrM

/-- A binder name that is unique in `scope`. Rocq allows shadowing, and two
shadowed Rocq binders printed with the same Lean name would make every
occurrence resolve to the innermost one, silently changing the term. -/
def binderFor (scope : Array String) (name : Option String) : TrM String := do
  match name with
  | some s =>
      let n := identOf s
      if scope.contains n then TrM.freshNameAvoiding scope else return n
  | none => TrM.freshNameAvoiding scope

/-- Free occurrence of `Rel n` in `t`, where `n` is relative to the binder
outside `t`. `usesInnermost` is the special case that decides whether an
anonymous product needs a written binder. -/
partial def usesRel (n : Nat) : Term → Bool
  | .rel k => k == n
  | .var _ | .const _ | .ind _ _ | .ctor _ _ _ | .intLit _ | .strLit _ | .unsupported _ =>
      false
  | .sort _ => false
  | .cast _ t => usesRel n t
  | .prod _ dom cod | .lam _ dom cod => usesRel n dom || usesRel (n + 1) cod
  | .letIn _ value ty body => usesRel n value || usesRel n ty || usesRel (n + 1) body
  | .app fn args => usesRel n fn || args.any (usesRel n)
  | .caseExpr _ _ _ _ _binders motive scrutinee branches =>
      usesRel n motive || usesRel n scrutinee ||
        branches.any fun b => usesRel (n + b.binders.size) b.body
  | .fix _ functions | .cofix _ functions =>
      functions.any fun f => usesRel n f.type || usesRel n f.body
  | .proj _ _ _ t => usesRel n t

def usesInnermost (t : Term) : Bool :=
  usesRel 1 t

def resolveConst (rocq : String) : TrM (String × Bool) := do
  let st ← get
  match st.declared.get? rocq with
  | some lean => return (lean, false)
  | none =>
      match mappedConstant rocq with
      | some lean => return (lean, true)
      | none => do
          TrM.addUnresolved rocq
          return (flatten rocq, false)

def resolveInd (block : String) (index : Nat) : TrM (String × Bool) := do
  let st ← get
  match st.indTypes.get? (block, index) with
  | some lean => return (lean, false)
  | none =>
      match mappedInd block index with
      | some lean => return (lean, true)
      | none => do
          TrM.addUnresolved s!"{block}#{index}"
          return (flatten block, false)

def resolveCtor (block : String) (index ctor : Nat) : TrM (String × Bool) := do
  let st ← get
  match st.ctors.get? (block, index, ctor) with
  | some lean => return (lean, false)
  | none =>
      match mappedCtor block index ctor with
      | some lean => return (lean, true)
      | none => do
          TrM.addUnresolved s!"{block}#{index}.{ctor}"
          return (flatten block ++ ".c" ++ toString ctor, false)

/-- Parenthesise anything that is not a single token. -/
def arg (s : String) : String :=
  if s.contains ' ' || s.contains '\n' then "(" ++ s ++ ")" else s

def escapeString (s : String) : String :=
  let buf := s.toList.map fun c =>
    match c with
    | '"' => "\\\""
    | '\\' => "\\\\"
    | '\n' => "\\n"
    | '\r' => "\\r"
    | '\t' => "\\t"
    | c => c.toString
  "\"" ++ String.join buf ++ "\""

mutual

/-- Translate one kernel term in a scope of binder names (innermost last). -/
partial def translate (scope : Array String) : Term → TrM String
  | .rel n =>
      if n ≥ 1 && n ≤ scope.size then
        return scope[scope.size - n]!
      else
        TrM.fail s!"de Bruijn index {n} is outside the {scope.size}-binder scope"
  | .var id => return identOf id
  | .sort k =>
      match k with
      | .prop => return "Prop"
      -- Coq's `Set` and `Type` are cumulative over universes; a fixed Lean
      -- `Type` (level 0) rejects a term whose type is `Type` at a higher level.
      | .set => return "Type _"
      | .type => return "Type _"
      | .sprop => TrM.fail "Rocq's SProp has no Lean counterpart"
      | .other s => TrM.fail s!"unknown sort '{s}'"
  | .cast _ t => translate scope t
  | .prod name dom cod => do
      let d ← translate scope dom
      let n ← binderFor scope name
      let c ← translate (scope.push n) cod
      if name.isNone && !usesInnermost cod then
        return s!"{arg d} → {c}"
      else
        return s!"({n} : {d}) → {c}"
  | .lam name dom body => do
      let d ← translate scope dom
      let n ← binderFor scope name
      let b ← translate (scope.push n) body
      return s!"fun {n} : {d} => {b}"
  | .letIn name value ty body => do
      let v ← translate scope value
      let t ← translate scope ty
      let n ← binderFor scope name
      let b ← translate (scope.push n) body
      return s!"let {n} : {t} := {v}; {b}"
  | .app (.const n) args => do
      let (head, _) ← resolveConst n
      let argTexts ← args.mapM (translate scope)
      return String.intercalate " " (("@" ++ head) :: argTexts.toList.map arg)
  | .app (.ind n i) args => do
      let (head, _) ← resolveInd n i
      let argTexts ← args.mapM (translate scope)
      return String.intercalate " " (("@" ++ head) :: argTexts.toList.map arg)
  | .app (.ctor n i c) args => do
      let (head, _) ← resolveCtor n i c
      let argTexts ← args.mapM (translate scope)
      -- Constructor parameters are implicit in Lean, so every argument the
      -- kernel carries has to be written out with `@`.
      return String.intercalate " " (("@" ++ head) :: argTexts.toList.map arg)
  | .app fn args => do
      let head ← translate scope fn
      let argTexts ← args.mapM (translate scope)
      return String.intercalate " " (arg head :: argTexts.toList.map arg)
  | .const n => return (← resolveConst n).1
  | .ind n i => return (← resolveInd n i).1
  | .ctor n i c => return (← resolveCtor n i c).1
  | .caseExpr block index params _nparams returnBinders motive scrutinee branches => do
      -- A non-recursive inductive's recursor has exactly the kernel `Case`
      -- branches as its arguments, so it can carry a dependent motive that a
      -- `match` would have to infer. `comparison` and `sumbool` are the two
      -- this compatibility layer needs.
      let recursor? : Option String :=
        if block == "Corelib.Init.Datatypes.comparison" && index == 0 then
          some "Rocq2Lean.Comparison.rec"
        else if block == "Corelib.Init.Specif.sumbool" && index == 0 then
          some "Rocq2Lean.Sumbool.rec"
        else none
      match recursor? with
      | some recName => do
          let mut pieces := #[]
          for p in params do
            pieces := pieces.push (arg (← translate scope p))
          -- The kernel motive is a *type under* the return binders, not a
          -- lambda; Lean's recursor wants the function.
          let mut motiveNames := #[]
          for n in returnBinders do
            motiveNames := motiveNames.push (← binderFor (scope ++ motiveNames) n)
          let motiveBody ← translate (scope ++ motiveNames) motive
          let motiveFn := motiveNames.foldr (fun n acc => s!"fun {n} => {acc}") motiveBody
          pieces := pieces.push (arg motiveFn)
          for branch in branches do
            let mut names := #[]
            for n in branch.binders do
              names := names.push (← binderFor (scope ++ names) n)
            let body ← translate (scope ++ names) branch.body
            let body := if body.contains '|' then s!"({body})" else body
            let fn := names.foldr (fun n acc => s!"fun {n} => {acc}") body
            pieces := pieces.push (arg fn)
          pieces := pieces.push (arg (← translate scope scrutinee))
          return s!"@{recName} " ++ String.intercalate " " pieces.toList
      | none => do
          if returnBinders.size > 1 && usesRel 2 motive then
            TrM.addAssumption "indexed `match`: Lean infers the return motive"
          let s ← translate scope scrutinee
          if branches.isEmpty then
            return s!"nomatch {arg s}"
          else do
            let mut arms := #[]
            for i in [0:branches.size] do
              let branch := branches[i]!
              let (ctor, mapped) ← resolveCtor block index i
              let head :=
                if mapped then (mappedCtorPattern block index i).getD ctor else ctor
              let mut names := #[]
              let mut used : Std.HashSet String := {}
              for name in branch.binders do
                let n ← binderFor (scope ++ names) name
                let n ← if used.contains n then TrM.freshNameAvoiding (scope ++ names) else pure n
                used := used.insert n
                names := names.push n
              let body ← translate (scope ++ names) branch.body
              let body := if body.contains '|' then s!"({body})" else body
              let pattern := String.intercalate " " (head :: names.toList)
              arms := arms.push s!"| {pattern} => {body}"
            return s!"match {arg s} with " ++ String.intercalate " " arms.toList
  | .proj recordName recordIndex field inner => do
      let (record, _) ← resolveInd recordName recordIndex
      let inner ← translate scope inner
      return s!"{record}.{fieldName field} {arg inner}"
  | .fix selected functions => do
      let (body, names) ← translateFixBlock scope functions
      return s!"(let rec {body}; {names[selected]!})"
  | .cofix _ _ =>
      TrM.fail "coinductive definitions have no Lean counterpart"
  | .intLit v =>
      TrM.fail s!"Rocq primitive integer {v} (Uint63) is not carried"
  | .strLit s => return escapeString s
  | .unsupported what => TrM.fail s!"Rocq construct not carried: {what}"

/-- Emit a `let rec ... and ...` block for a kernel fixpoint.

The kernel's scopes are asymmetric: a function's *type* lives in the outer
context only, while its *body* lives in `Γ, f₁ … fₖ, args` — the block's own
functions sit between the outer context and the lambda binders, and that is what
a recursive `Rel` points at. The type is therefore written as the full product
(rather than split into binders), and only the body's scope gains the names. -/
partial def translateFixBlock (scope : Array String) (functions : Array FixFunction) :
    TrM (String × Array String) := do
  -- Lean's `let rec ... and ...` is layout-sensitive in a way that breaks as
  -- soon as the block sits inside another expression. Rather than emit syntax
  -- that parses only at top level, a mutually recursive block is marked.
  if functions.size != 1 then
    TrM.fail "mutually recursive fixed point (Lean `let rec` with `and` is not emitted)"
  let mut names := #[]
  for fn in functions do
    let name ←
      match fn.name with
      | some n =>
          let lean := identOf n
          if scope.contains lean then TrM.freshNameAvoiding scope else pure lean
      | none => TrM.freshNameAvoiding scope
    names := names.push name
  let blockScope := scope ++ names
  let mut definitions := #[]
  for i in [0:functions.size] do
    let fn := functions[i]!
    let tyText ← translate scope fn.type
    let bodyText ← translate blockScope fn.body
    definitions := definitions.push s!"{names[i]!} : {tyText} := {bodyText}"
  return (String.intercalate " " definitions.toList, names)
end

end Rocq2Lean
