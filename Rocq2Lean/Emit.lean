import Rocq2Lean.IR
import Rocq2Lean.Names
import Rocq2Lean.Translate

/-!
# Emitting Lean declarations

One rule governs this file: a declaration is either translated whole or it is
visibly marked. There is no third path where a body is guessed, a type is
weakened, or a name is invented to keep the file compiling.

Two orderings matter and are handled before anything is written:

* every declaration's Lean name is registered first, so a reference to a later
  declaration resolves rather than being reported as unresolved;
* declarations are emitted in a stable topological order of their kernel
  references, because Rocq lets the derived eliminators of a block appear in any
  order while Lean has no forward references.

Markers are the token `ROCQ2LEAN-UNTRANSLATED` in a doc comment (for a whole
declaration) or in a comment above `sorry` (for a body), plus the same message in
the file's translation report at the end.
-/

namespace Rocq2Lean

structure EmitResult where
  text : String
  unresolved : Array String
  markers : Array String
  assumptions : Array String
  axioms : Array String

/-! ## References -/

partial def termGlobals : Term → Array String
  | .rel _ | .var _ | .sort _ | .intLit _ | .strLit _ | .unsupported _ => #[]
  | .cast _ t => termGlobals t
  | .const n => #[n]
  | .ind n _ => #[n]
  | .ctor n _ _ => #[n]
  | .prod _ dom cod => termGlobals dom ++ termGlobals cod
  | .lam _ dom body => termGlobals dom ++ termGlobals body
  | .letIn _ value ty body => termGlobals value ++ termGlobals ty ++ termGlobals body
  | .app fn args => termGlobals fn ++ args.foldl (fun acc a => acc ++ termGlobals a) #[]
  | .caseExpr _ _ _ _ _ motive scrutinee branches =>
      termGlobals motive ++ termGlobals scrutinee ++
        branches.foldl (fun acc b => acc ++ termGlobals b.body) #[]
  | .fix _ functions | .cofix _ functions =>
      functions.foldl (fun acc f => acc ++ termGlobals f.type ++ termGlobals f.body) #[]
  | .proj recordName _ _ t => #[recordName] ++ termGlobals t

def binderGlobals (b : Binder) : Array String :=
  termGlobals b.type ++ (match b.value with | some v => termGlobals v | none => #[])

def indTypeGlobals (t : IndType) : Array String :=
  termGlobals t.arity ++
    t.ctors.foldl (fun acc c =>
      acc ++ termGlobals c.type ++ c.fields.foldl (fun a f => a ++ termGlobals f.type) #[]) #[]

def declPrimaryName : Decl → Option String
  | .constant name .. => some name
  | .inductiveDecl name .. => some name
  | _ => none

def declGlobals : Decl → Array String
  | .constant _ _ _ _ hyps ty body =>
      hyps.foldl (fun acc h => acc ++ binderGlobals h) #[] ++ termGlobals ty ++
        (match body with | some b => termGlobals b | none => #[])
  | .inductiveDecl _ _ _ _ _ params types =>
      params.foldl (fun acc p => acc ++ binderGlobals p) #[] ++
        types.foldl (fun acc t => acc ++ indTypeGlobals t) #[]
  | _ => #[]

/-- Stable topological order: dependencies first, ties broken by source order. A
remaining cycle is emitted in source order — Lean will reject it at the cycle,
which is the honest outcome for a cycle the kernel does not have. -/
def stableTopo (decls : Array Decl) : Array Decl :=
  let n := decls.size
  let index : Std.HashMap String Nat :=
    (List.range n).foldl
      (fun m i =>
        match declPrimaryName decls[i]! with
        | some name => m.insert name i
        | none => m)
      {}
  let deps : Array (Array Nat) :=
    (Array.range n).map fun i =>
      (declGlobals decls[i]!).toList.filterMap (fun g => index.get? g)
        |>.filter (fun j => j != i) |>.toArray
  let (adj, indegree) :=
    (List.range n).foldl
      (fun (adj, indegree) i =>
        (deps[i]!).foldl
          (fun (adj, indegree) j =>
            (adj.set! j ((adj[j]!).push i), indegree.set! i (indegree[i]! + 1)))
          (adj, indegree))
      (Array.replicate n (#[] : Array Nat), Array.replicate n 0)
  let rec loop (fuel : Nat) (indegree : Array Nat) (emitted : Array Bool)
      (order : Array Nat) : Array Nat :=
    match fuel with
    | 0 => order
    | fuel + 1 =>
      let ready := (List.range n).find? fun i => emitted[i]! == false && indegree[i]! == 0
      let chosen :=
        match ready with
        | some i => i
        | none => ((List.range n).find? fun i => emitted[i]! == false).getD 0
      let order := order.push chosen
      let emitted := emitted.set! chosen true
      let indegree :=
        (adj[chosen]!).foldl (fun indegree k => indegree.set! k (indegree[k]! - 1)) indegree
      loop fuel indegree emitted order
  let order := loop n indegree (Array.replicate n false) #[]
  order.map fun i => decls[i]!

/-! ## Names -/

/-- The Lean name of the `i`th type of an inductive block. A single-type block is
flat; a mutual block keeps the module prefix and replaces the block's last
component with the type's own name. -/
def typeLeanName (block : String) (types : Array IndType) (i : Nat) : String :=
  if types.size == 1 then flatten block
  else
    let parts := block.splitOn "."
    let modPrefix := String.intercalate "." parts.dropLast
    if modPrefix.isEmpty then identOf types[i]!.name
    else finalizeIdent (flattenRaw modPrefix ++ "_" ++ sanitizeComponent types[i]!.name)

/-- A record becomes a Lean `structure` only when it is a single, non-indexed
type with one constructor and named fields; anything else keeps the inductive
form, which is always expressible. -/
def isStructureShape (record : Bool) (types : Array IndType) : Bool :=
  record && types.size == 1 &&
    (let t := types[0]!
     t.ctors.size == 1 && t.ctors[0]!.fields.isEmpty == false &&
       (match t.arity with | .sort _ => true | _ => false))

def registerInductiveNames (name : String) (record : Bool) (types : Array IndType) : TrM Unit := do
  let mut typeNames := #[]
  for i in [0:types.size] do
    let lean := typeLeanName name types i
    typeNames := typeNames.push lean
    let st ← get
    set { st with indTypes := st.indTypes.insert (name, i) lean }
  if isStructureShape record types then
    let st ← get
    set { st with ctors := st.ctors.insert (name, 0, 0) (typeNames[0]! ++ ".mk") }
  else
    for i in [0:types.size] do
      for j in [0:types[i]!.ctors.size] do
        let ctorLean := typeNames[i]! ++ "." ++ identOf types[i]!.ctors[j]!.name
        let st ← get
        set { st with ctors := st.ctors.insert (name, i, j) ctorLean }

/-- Leading products of a term (an arity's indices, in practice). -/
partial def prodDepth : Term → Nat
  | .prod _ _ cod => 1 + prodDepth cod
  | _ => 0

/-- Constructor arguments, induction-hypothesis count, and the per-argument
recursive flags. A hypothesis is counted for an argument whose type has the
inductive at its head; nested occurrences are not counted, which makes the
branch arity disagree with Lean and sends the declaration down the `exact`
path. -/
partial def ctorShape (c : Ctor) : Nat × Nat × Array Bool :=
  let rec go (args ihs : Nat) (flags : Array Bool) : Term → Nat × Nat × Array Bool
    | .prod _ dom cod =>
        let recursive :=
          match dom with
          | .ind _ _ | .app (.ind _ _) _ => true
          | _ => false
        go (args + 1) (if recursive then ihs + 1 else ihs) (flags.push recursive) cod
    | _ => (args, ihs, flags)
  go 0 0 #[] c.type

/-- A local inductive's own eliminators (`_ind`, `_rect`, `_rec`) can become
`induction`, provided it has one type, no indices and is not mutual. -/
def registerEliminators (block : String) (params : Array Binder) (types : Array IndType) : TrM Unit := do
  if types.size != 1 then return ()
  let t := types[0]!
  if prodDepth t.arity != 0 then return ()
  let mut branches := #[]
  for i in [0:t.ctors.size] do
    let (args, ihs, flags) := ctorShape t.ctors[i]!
    branches := branches.push ({ ctor := i, args, ihs, recursive := flags } : ElimBranch)
  let info : ElimInfo :=
    { block, indIndex := 0, params := params.size, indices := 0, branches }
  for suffix in ["_ind", "_rect", "_rec"] do
    let st ← get
    set { st with eliminators := st.eliminators.insert (block ++ suffix) info }

/-- A declaration whose Rocq name is in the trusted mapping is already provided
by the Lean prelude; translating it again would give the same name a second,
incompatible definition. -/
def mappedTypeBlock (block : String) : Bool :=
  mappedTypes.any fun (b, _, _) => b == block

def mappedConst (name : String) : Bool :=
  (mappedConstant name).isSome

def preRegister : Decl → TrM Unit
  | .constant name .. => if mappedConst name then pure () else TrM.declare name (flatten name)
  | .inductiveDecl name _ _ _ record params types =>
      if mappedTypeBlock name then pure ()
      else do
        registerInductiveNames name record types
        registerEliminators name params types
  | _ => pure ()

/-! ## Text -/

def locText (l : Option SrcLoc) : String :=
  match l with
  | some l => s!"`{l.file}:{l.line}`"
  | none => "an unknown location"

def sectionHeader (rocq : String) (l : Option SrcLoc) : String :=
  s!"\n/-! ### `{rocq}` ({locText l}) -/\n"

def untranslatedDoc (what rocq reason : String) (l : Option SrcLoc) : String :=
  s!"/- ROCQ2LEAN-UNTRANSLATED ({what})\n\
     `{rocq}` — from {locText l}: {reason}\n\
     Hand translation required. -/"

/-- Try a translation, keeping the error message instead of aborting the file. -/
def attempt (comp : TrM α) : TrM (Except String α) := do
  try
    return .ok (← comp)
  catch e =>
    return .error e

/-- The binders a constant is declared over: its section hypotheses, in order. -/
def hypsText (hyps : Array Binder) : TrM (String × Array String) := do
  let mut text := #[]
  let mut scope : Array String := #[]
  for h in hyps do
    match h.value with
    | some _ => TrM.fail "let-bound section hypothesis in a discharged constant"
    | none => pure ()
    let t ← translate scope h.type
    let n ← binderFor scope h.name
    text := text.push s!"({n} : {t})"
    scope := scope.push n
  return (String.intercalate " " text.toList, scope)

def emitInductive (name : String) (loc : Option SrcLoc) (finite : String) (isMutual : Bool)
    (record : Bool) (params : Array Binder) (types : Array IndType) : TrM (Array String) := do
  if finite == "coinductive" then
    TrM.fail "coinductive types have no Lean counterpart"
  else do
    let mut typeNames := #[]
    for i in [0:types.size] do
      typeNames := typeNames.push (typeLeanName name types i)
    if isStructureShape record types then
      let lean := typeNames[0]!
      let t := types[0]!
      let (binderText, scope) ← hypsText params
      let head := if binderText.isEmpty then lean else s!"{lean} {binderText}"
      let arity ← translate scope t.arity
      let mut lines := #[]
      let mut scope := scope
      for field in t.ctors[0]!.fields do
        let fty ← translate scope field.type
        let fname := fieldName field.name
        lines := lines.push s!"  {fname} : {fty}"
        scope := scope.push fname
      return #[sectionHeader name loc, s!"structure {head} : {arity} where",
              String.intercalate "\n" lines.toList]
    else
      let mut declarations := #[]
      for i in [0:types.size] do
        let t := types[i]!
        let lean := typeNames[i]!
        let (binderText, scope) ← hypsText params
        let head := if binderText.isEmpty then lean else s!"{lean} {binderText}"
        let arity ← translate scope t.arity
        let mut ctorLines := #[]
        for j in [0:t.ctors.size] do
          let c := t.ctors[j]!
          let tyText ← translate scope c.type
          ctorLines := ctorLines.push s!"  | {identOf c.name} : {tyText}"
        declarations := declarations.push
          (s!"inductive {head} : {arity} where\n" ++
            String.intercalate "\n" ctorLines.toList)
      let body := String.intercalate "\n\n" declarations.toList
      if isMutual || types.size > 1 then
        return #[sectionHeader name loc, "mutual", body, "end"]
      else
        return #[sectionHeader name loc, body]

/-- Split a product type into written binders and its result. -/
partial def splitType (scope : Array String) (ty : Term) (acc : Array String) :
    TrM (Array String × Term × Array String) := do
  match ty with
  | .prod name dom cod => do
      let d ← translate scope dom
      let n ← binderFor scope name
      splitType (scope.push n) cod (acc.push s!"({n} : {d})")
  | _ => return (acc, ty, scope)

/-- Peel exactly `n` lambdas, for a fixpoint body paired with its type. -/
partial def peelArgs (scope : Array String) (n : Nat) (t : Term) (acc : Array String) :
    TrM (Array String × Array String × Term) := do
  if n == 0 then return (acc, scope, t)
  else
    match t with
    | .lam name _ rest =>
        let nm ← binderFor scope name
        peelArgs (scope.push nm) (n - 1) rest (acc.push nm)
    | _ => TrM.fail "fixpoint body is not a lambda telescope of its type's arity"

/-- Emit a kernel fixpoint block with more than one function as a `mutual`
block. Lean has no expression-level `let rec … and …` that survives nesting, so
a top-level body is expanded into mutually recursive definitions and the
constant becomes an alias for the selected one. -/
def emitMutualFix (name binderText : String) (scope : Array String) (tyText : String)
    (functions : Array FixFunction) (selected : Nat) : TrM (Array String) := do
  let locals : Array String :=
    functions.mapIdx fun i fn =>
      match fn.name with
      | some n => flattenRaw name ++ "_fix_" ++ sanitizeComponent n
      | none => flattenRaw name ++ "_fix_" ++ toString i
  let blockScope := scope ++ locals
  let mut defs := #[]
  for i in [0:functions.size] do
    let fn := functions[i]!
    let (binders, retTerm, retScope) ← splitType scope fn.type #[]
    let retText ← translate retScope retTerm
    let (_, bodyScope, core) ← peelArgs blockScope binders.size fn.body #[]
    let coreText ← translate bodyScope core
    let hyps := if binderText.isEmpty then "" else binderText ++ " "
    defs := defs.push
      (s!"def {locals[i]!} {hyps}{String.intercalate " " binders.toList} : {retText} :=\n  {coreText}")
  let applied := String.intercalate " " (locals[selected]! :: scope.toList)
  return #[ "mutual" ] ++ defs ++ #[ "end", s!"def {flatten name}{if binderText.isEmpty then "" else " " ++ binderText} : {tyText} := {applied}" ]

def isRefl : Term → Bool
  | .cast _ t => isRefl t
  | .ctor "Corelib.Init.Logic.eq" 0 0 => true
  | .app (.ctor "Corelib.Init.Logic.eq" 0 0) _ => true
  | _ => false

def exactTactic (scope : Array String) (t : Term) : TrM String := do
  return s!"exact {← translate scope t}"

/-- The two equality eliminators, which are rewrites rather than inductions. -/
def isEqEliminator (name : String) : Bool :=
  name == "Corelib.Init.Logic.eq_ind" || name == "Corelib.Init.Logic.eq_rect"
    || name == "Corelib.Init.Logic.eq_rec" || name == "Corelib.Init.Logic.eq_ind_r"
    || name == "Corelib.Init.Logic.eq_rect_r" || name == "Corelib.Init.Logic.eq_rec_r"

def eqEliminatorIsRight (name : String) : Bool :=
  name.endsWith "_ind_r" || name.endsWith "_rect_r" || name.endsWith "_rec_r"

/-- A term that is a variable in the current scope, as the name a tactic would
use. -/
def varName (scope : Array String) : Term → Option String
  | .rel n => if n ≥ 1 && n ≤ scope.size then some scope[scope.size - n]! else none
  | .var id => some (identOf id)
  | .cast _ t => varName scope t
  | _ => none

partial def lamDepth : Term → Nat × Term
  | .lam _ _ body => let (n, b) := lamDepth body; (n + 1, b)
  | t => (0, t)

/-- A beta-redex with variable arguments — `(fun x y => body) a b` where `a` and
`b` are already in scope — is not translated as an application: extending the
scope substitutes the variables, which is exactly the reduction. -/
def betaStrip (scope : Array String) (t : Term) : Option (Array String × Term) :=
  match t with
  | .app fn args =>
      let (n, body) := lamDepth fn
      if n != 0 && n == args.size then
        match args.toList.mapM (varName scope) with
        | some names => some (scope ++ names.toArray, body)
        | none => none
      else none
  | _ => none

mutual

/-- Peel the proof term's leading lambdas into `intro` names. -/
partial def peelIntros (scope : Array String) (t : Term) (acc : Array String) :
    TrM (Array String × Array String × Term) := do
  match t with
  | .lam name _ rest =>
      let n ← binderFor scope name
      peelIntros (scope.push n) rest (acc.push n)
  | _ => return (acc, scope, t)

/-- Peel exactly `n` lambdas (a branch's constructor arguments and hypotheses). -/
partial def peelExactly (scope : Array String) (n : Nat) (t : Term) (acc : Array String) :
    TrM (Array String × Array String × Term) := do
  if n == 0 then return (acc, scope, t)
  else
    match t with
    | .lam name _ rest =>
        let nm ← binderFor scope name
        peelExactly (scope.push nm) (n - 1) rest (acc.push nm)
    | _ => TrM.fail "branch is not a lambda telescope of the expected arity"

/-- One tactic that proves the current goal from a term. `fuel` bounds the
recursion so that a chain of rewrites cannot multiply the output without limit;
at zero the term itself is emitted. -/
partial def scriptTerm (fuel : Nat) (scope : Array String) (t : Term) : TrM String := do
  if fuel == 0 then exactTactic scope t
  else if isRefl t then return "rfl"
  else
    match betaStrip scope t with
    | some (scope, body) => scriptTerm (fuel - 1) scope body
    | none =>
      match t with
      | .cast _ inner => scriptTerm fuel scope inner
      | .caseExpr block index _params _nparams returnBinders _ scrutinee branches =>
          caseScript (fuel - 1) scope block index returnBinders scrutinee branches t
      | .app (.const name) args => do
          if isEqEliminator name then eqElimScript (fuel - 1) scope name args t
          else
            match (← get).eliminators.get? name with
            | some info => inductionScript (fuel - 1) scope info args t
            | none =>
                match builtinEliminator name with
                | some info => inductionScript (fuel - 1) scope info args t
                | none => exactTactic scope t
      | _ => exactTactic scope t

/-- `(induction <scrutinee> with | <ctor> <binders> => <script> …)`. Every shape
is checked before anything is emitted; a mismatch returns the term instead. -/
partial def inductionScript (fuel : Nat) (scope : Array String) (info : ElimInfo)
    (args : Array Term) (whole : Term) : TrM String := do
  let expected := info.params + 1 + info.branches.size + info.indices + 1
  if info.indices != 0 || args.size != expected then
    exactTactic scope whole
  else
    let scrutinee := args[args.size - 1]!
    let scrutineeText ← translate scope scrutinee
    let mut arms := #[]
    for i in [0:info.branches.size] do
      let branch := info.branches[i]!
      let branchTerm := args[info.params + 1 + i]!
      let total := branch.args + branch.ihs
      let (names, branchScope, core) ← peelExactly scope total branchTerm #[]
      -- Rocq interleaves argument and hypothesis; Lean's pattern wants the
      -- arguments first. The body scope keeps Rocq's order, since that is what
      -- its de Bruijn indices refer to.
      let mut ctorArgs : Array String := #[]
      let mut ihNames : Array String := #[]
      let mut k := 0
      for isRec in branch.recursive do
        ctorArgs := ctorArgs.push names[k]!
        k := k + 1
        if isRec then
          ihNames := ihNames.push names[k]!
          k := k + 1
      if k != names.size then
        TrM.fail "branch telescope does not match the constructor's recursive arguments"
      let patternNames := ctorArgs ++ ihNames
      let (ctor, _) ← resolveCtor info.block info.indIndex branch.ctor
      -- `induction … with` names alternatives by the constructor's short name
      -- (`zero`, not `Nat.zero`), so the namespace is dropped here.
      let alt := (ctor.splitOn ".").getLast!
      let sub ← scriptTerm fuel branchScope core
      -- A script containing tactic alternatives must be grouped, or its `|`
      -- would be read as an arm of the enclosing `induction`.
      let sub := if sub.contains '|' && !sub.startsWith "(" then s!"({sub})" else sub
      arms := arms.push s!"| {alt} {String.intercalate " " patternNames.toList} => {sub}"
    let body := s!"induction {arg scrutineeText} with {String.intercalate " " arms.toList}"
    if (← TrM.strictEnabled) then return s!"({body})"
    else return s!"(first | ({body}) | exact {← translate scope whole})"

/-- `eq_ind A x P h y e` proves `P y` from `h : P x` and `e : x = y`;
`eq_ind_r` reads the equation the other way. Both become a rewrite followed by
the transported hypothesis, with the original term as the last alternative so a
goal whose syntax does not match the rewrite still succeeds. The hypothesis is
scripted recursively, which turns a chain of equalities into a chain of rewrites
ending in `rfl`. -/
partial def eqElimScript (fuel : Nat) (scope : Array String) (name : String) (args : Array Term)
    (whole : Term) : TrM String := do
  if args.size != 6 then exactTactic scope whole
  else
    let e ← translate scope args[5]!
    let wholeText ← translate scope whole
    let h ← scriptTerm fuel scope args[3]!
    let h := if h.contains '|' && !h.startsWith "(" then s!"({h})" else h
    let rule := if eqEliminatorIsRight name then e else "← " ++ e
    if (← TrM.strictEnabled) then return s!"rw [{rule}]; {h}"
    else return s!"(first | rw [{rule}]; {h} | exact {wholeText})"

/-- A single-constructor `Case` on a hypothesis becomes `rcases`. Multi-branch
cases keep the `match` term: focusing several generated goals in one inline
script needs bullets, and the fallback is already correct. -/
partial def caseScript (fuel : Nat) (scope : Array String) (block : String) (index : Nat)
    (returnBinders : Array (Option String)) (scrutinee : Term) (branches : Array Branch)
    (whole : Term) : TrM String := do
  let some hyp := varName scope scrutinee | exactTactic scope whole
  if returnBinders.size != 1 || branches.size != 1 then exactTactic scope whole
  else
    let branch := branches[0]!
    let mut names := #[]
    for name in branch.binders do
      names := names.push (← binderFor scope name)
    let sub ← scriptTerm fuel (scope ++ names) branch.body
    let sub := if sub.contains '|' && !sub.startsWith "(" then s!"({sub})" else sub
    let pattern := if names.isEmpty then "⟨⟩" else s!"⟨{String.intercalate ", " names.toList}⟩"
    let body := s!"rcases {hyp} with {pattern}; {sub}"
    if (← TrM.strictEnabled) then return s!"({body})"
    else return s!"(first | ({body}) | exact {← translate scope whole})"

end

/-- The tactic script for a theorem body: introductions, then a terminal step.
The fallback is always `exact <term>`, so a shape this reducer does not know is
still proved by the term the kernel checked. -/
def proofLines (scope : Array String) (body : Term) : TrM (Array String) := do
  let (intros, scope, rest) ← peelIntros scope body #[]
  let terminal ← scriptTerm 5 scope rest
  if intros.isEmpty then return #[terminal]
  else return #[s!"intro {String.intercalate " " intros.toList}", terminal]

def emitConstant (name : String) (loc : Option SrcLoc) (form : String) (isProp : Bool)
    (hyps : Array Binder) (ty : Term) (body : Option Term) :
    TrM (Array String) := do
  let lean := flatten name
  let (binderText, scope) ← hypsText hyps
  let head := if binderText.isEmpty then lean else s!"{lean} {binderText}"
  match form with
  | "primitive" | "symbol" =>
      TrM.addMarker s!"{name} ({locText loc}): primitive kernel constant"
      return #[sectionHeader name loc, untranslatedDoc "primitive constant" name
        "the kernel stores this as a primitive operation, not as a term" loc]
  | "axiom" =>
      let tyR ← attempt (translate scope ty)
      match tyR with
      | .error e =>
          TrM.addMarker s!"{name} ({locText loc}): type not translated: {e}"
          return #[sectionHeader name loc, untranslatedDoc "type" name e loc]
      | .ok tyText => return #[sectionHeader name loc, s!"axiom {head} : {tyText}"]
  | _ =>
      -- A proof-valued `Definition` is a theorem in Lean's sense; the kernel
      -- sort is the authority, not the Rocq command that introduced it.
      let keyword := if isProp then "theorem" else "def"
      let tyR ← attempt (translate scope ty)
      match tyR with
      | .error e =>
          TrM.addMarker s!"{name} ({locText loc}): type not translated: {e}"
          return #[sectionHeader name loc, untranslatedDoc "type" name e loc,
                  s!"-- Declaration omitted: `{name}` could not be typed."]
      | .ok tyText =>
          -- A mutually recursive fixed point is a `mutual` block at the top
          -- level; the constant itself becomes an alias.
          let fixBlock : Option (Nat × Array FixFunction) :=
            match body with
            | some (.fix selected functions) =>
                if functions.size > 1 then some (selected, functions) else none
            | _ => none
          match fixBlock with
          | some (selected, functions) => do
              let lines ← attempt (emitMutualFix name binderText scope tyText functions selected)
              match lines with
              | .ok ls => return #[sectionHeader name loc] ++ ls
              | .error _ => pure ()
          | none => pure ()
          let assume ← TrM.axiomatiseEnabled
          let st ← get
          let demoted := st.assumePrefixes.any (fun p => name.startsWith p)
          if assume && (keyword == "theorem" || demoted) then do
            TrM.addAxiom s!"{name} ({locText loc})"
            return #[sectionHeader name loc,
                    s!"/- ROCQ2LEAN-ASSUMED\n`{name}` — from {locText loc}: stdlib lemma assumed, not proved. -/",
                    s!"axiom {head} : {tyText}"]
          else
          match body with
          | none =>
              TrM.addMarker s!"{name} ({locText loc}): body is not available in the kernel"
              return #[sectionHeader name loc,
                      untranslatedDoc "body" name
                        "the kernel holds no term for this declaration" loc,
                      s!"{keyword} {head} : {tyText} := by",
                      "  sorry"]
          | some b =>
              let only ← TrM.statementsOnly
              -- A definition's body is a term, not a proof: statements-only
              -- keeps it. Only theorems lose their proofs.
              if only && keyword == "theorem" then
                TrM.addMarker s!"{name} ({locText loc}): statement only (proof omitted)"
                return #[sectionHeader name loc,
                        s!"{keyword} {head} : {tyText} := by",
                        "  -- ROCQ2LEAN-UNTRANSLATED: statement only; proof omitted",
                        "  sorry"]
              else
              let bodyR ← attempt (translate scope b)
              match bodyR with
              | .ok bodyText =>
                  let scripted ←
                    if keyword == "theorem" then
                      match ← attempt (proofLines scope b) with
                      | .ok lines => pure (some lines)
                      | .error _ => pure none
                    else pure none
                  match scripted with
                  | some lines =>
                      if lines.size == 1 && lines[0]!.startsWith "exact " then
                        return #[sectionHeader name loc,
                                s!"{keyword} {head} : {tyText} :=\n  {bodyText}"]
                      else
                        let indent (l : String) := s!"  {l}"
                        return #[sectionHeader name loc,
                                s!"{keyword} {head} : {tyText} := by"] ++
                          lines.map indent
                  | none =>
                      return #[sectionHeader name loc,
                              s!"{keyword} {head} : {tyText} :=\n  {bodyText}"]
              | .error e =>
                  TrM.addMarker s!"{name} ({locText loc}): body not translated: {e}"
                  return #[sectionHeader name loc, untranslatedDoc "body" name e loc,
                          s!"{keyword} {head} : {tyText} := by",
                          s!"  -- ROCQ2LEAN-UNTRANSLATED: {e}",
                          "  sorry"]

def emitDecl (d : Decl) : TrM (Array String) := do
  let name := (declPrimaryName d).getD ""
  let st ← get
  set { st with current := name }
  match d with
  | .inductiveDecl name loc finite isMutual record params types =>
      if mappedTypeBlock name then return #[] else
      try
        emitInductive name loc finite isMutual record params types
      catch e =>
        TrM.addMarker s!"{name} ({locText loc}): {e}"
        return #[sectionHeader name loc, untranslatedDoc "inductive" name e loc]
  | .constant name loc form isProp hyps ty body =>
      if mappedConst name then return #[] else
      try
        emitConstant name loc form isProp hyps ty body
      catch e =>
        TrM.addMarker s!"{name} ({locText loc}): {e}"
        return #[sectionHeader name loc, untranslatedDoc "declaration" name e loc]
  | .absorbed _ _ _ => return #[]
  | .error name loc why =>
      TrM.addMarker s!"{name} ({locText loc}): extractor error: {why}"
      return #[sectionHeader name loc, untranslatedDoc "extractor error" name why loc]

def header (f : File) : String :=
  s!"/-\nGenerated by rocq2lean from `{f.source}` (Rocq {f.rocqVersion}).\n\
     Do not edit: regenerate instead. `ROCQ2LEAN-UNTRANSLATED` marks what the\n\
     translation refused to carry.\n-/\n\n\
     import Rocq2Lean.Prelude\n\n\
     set_option autoImplicit false\n\
     set_option linter.defProp false\n\
     set_option linter.unusedVariables false\n\n\
     noncomputable section\n"

def report (unresolved : Array String) (markers : Array String)
    (assumptions : Array String) (axioms : Array String) : String :=
  let unresolvedSection :=
    if unresolved.isEmpty then ""
    else
      "\n/-! ## Unresolved references\n\
        These Rocq globals were referenced but neither declared by this file nor\n\
        mapped in `Rocq2Lean.Names.mappedTypes`/`mappedCtors`/`mappedConstants`.\n\
        Lean will report them at their use sites.\n\n" ++
      String.intercalate "\n" (unresolved.toList.map fun n => s!"* `{n}`") ++ "\n-/\n"
  let markerSection :=
    if markers.isEmpty then ""
    else
      "\n/-! ## Untranslated declarations\n" ++
      String.intercalate "\n" (markers.toList.map fun m => s!"* {m}") ++ "\n-/\n"
  let assumptionSection :=
    if assumptions.isEmpty then ""
    else
      "\n/-! ## Assumptions\n\
        These declarations were emitted, but rely on Lean inferring a `match`\n\
        motive that the translation does not write down. If Lean rejects one,\n\
        it needs a hand translation.\n\n" ++
      String.intercalate "\n" (assumptions.toList.map fun a => s!"* {a}") ++ "\n-/\n"
  let axiomSection :=
    if axioms.isEmpty then ""
    else
      "\n/-! ## Assumed declarations\n\
        These declarations are assumptions: their Rocq definition or proof was not translated. The\n\
        list is the trusted base of the translation.\n\n" ++
      String.intercalate "\n" (axioms.toList.map fun a => s!"* {a}") ++ "\n-/\n"
  unresolvedSection ++ markerSection ++ assumptionSection ++ axiomSection

/-- Keep only declarations reachable from those whose Rocq name starts with one
of `roots`. A compatibility layer should contain the stdlib declarations the
target uses, not every lemma of every module that was loaded. -/
def selectClosure (decls : Array Decl) (roots : Array String) : Array Decl :=
  if roots.isEmpty then decls
  else
    let n := decls.size
    let nameIdx : Std.HashMap String Nat :=
      (List.range n).foldl
        (fun m i =>
          match declPrimaryName decls[i]! with
          | some name => m.insert name i
          | none => m)
        {}
    let deps : Array (Array String) := decls.map declGlobals
    let isRoot : Array Bool :=
      (Array.range n).map fun i =>
        match declPrimaryName decls[i]! with
        | some name => roots.any (fun p => name.startsWith p)
        | none => false
    let rec bfs (fuel : Nat) (keep : Array Bool) (queue : List Nat) : Array Bool :=
      match fuel with
      | 0 => keep
      | fuel + 1 =>
          match queue with
          | [] => keep
          | i :: rest =>
              let (keep, rest) :=
                (deps[i]!).foldl
                  (fun (keep, rest) g =>
                    match nameIdx.get? g with
                    | some j => if keep[j]! then (keep, rest) else (keep.set! j true, j :: rest)
                    | none => (keep, rest))
                  (keep, rest)
              bfs fuel keep rest
    let queue : List Nat :=
      (List.range n).filter (fun i => isRoot[i]!) |>.reverse
    let keep := bfs n isRoot queue
    (Array.range n).foldl (fun acc i => if keep[i]! then acc.push decls[i]! else acc) #[]

def emitFile (f : File) (strict := false) (statementsOnly := false) (axiomatise := false)
    (assumePrefixes : Array String := #[]) : Except String EmitResult := do
  let ordered := stableTopo f.declarations
  let (_, pre) ← TrM.run (ordered.mapM preRegister) { strict, statementsOnly, axiomatise, assumePrefixes }
  let (chunks, st) ← TrM.run (ordered.mapM emitDecl) pre
  let body := String.intercalate "\n" (chunks.toList.map fun c => String.intercalate "\n" c.toList)
  return { text := header f ++ body ++ report st.unresolved st.markers st.assumptions st.axioms ++ "\nend\n",
           unresolved := st.unresolved,
           markers := st.markers,
           assumptions := st.assumptions,
           axioms := st.axioms }

end Rocq2Lean
