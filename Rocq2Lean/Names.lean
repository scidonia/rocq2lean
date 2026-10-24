/-!
# Rocq names, Lean names, and the trusted mapping

A Rocq global name is hierarchical (`Corelib.Init.Datatypes.nat`); a Lean
identifier is a single segment. The translation therefore flattens every name
deterministically and keeps a table for the handful of Rocq globals that are
deliberately rendered as Lean's own equivalents. Everything in that table is a
trusted, hand-written decision: the kernel gives no reason to believe that
Rocq's `nat` and Lean's `Nat` agree, only that the fragment we place in the
table is the fragment we are willing to treat as shared.

The table is deliberately small. A name that is not in it and not declared by
the file being translated is emitted as its flattened form and reported as
unresolved, so the generated Lean fails loudly at the use site instead of
silently inventing a declaration.
-/

namespace Rocq2Lean

/-- Lean 4 keywords. A Rocq identifier that collides with one is quoted in the
generated source, so the same string works for declarations and references. -/
def leanKeywords : List String :=
  [ "def", "theorem", "lemma", "example", "axiom", "opaque", "abbrev", "instance"
  , "class", "structure", "inductive", "coinductive", "universe", "variable"
  , "namespace", "section", "end", "open", "export", "import", "mutual", "where"
  , "with", "fun", "let", "in", "match", "do", "if", "then", "else", "have"
  , "show", "from", "by", "at", "syntax", "macro", "elab", "deriving", "partial"
  , "unsafe", "private", "protected", "noncomputable", "attribute", "set_option"
  , "rec", "this", "include", "omit", "using", "ext", "init", "default"
  , "termination_by", "decreasing_by", "macro_rules", "notation", "infix"
  , "prefix", "postfix", "local", "scoped", "initialize", "builtin_initialize"
  , "forall", "exists", "sort", "calc", "suffices", "obtain", "unless", "defer"
  , "Type", "Prop", "Sort" ]

def isKeyword (s : String) : Bool :=
  leanKeywords.elem s

/-- One path component, reduced to the characters a Lean identifier may contain.
No quoting: quoting applies to a whole identifier, and a component is about to
be joined into a longer one (`«section»_twice` is not an identifier). -/
def sanitizeComponent (s : String) : String :=
  let cleaned : String :=
    String.ofList (s.toList.map fun c => if c.isAlphanum || c == '_' || c == '\'' then c else '_')
  if cleaned.isEmpty then "x" else cleaned

/-- A single identifier: sanitised, then quoted if Lean would reject it. -/
def identOf (s : String) : String :=
  let cleaned := sanitizeComponent s
  let cleaned :=
    match cleaned.toList with
    | c :: _ => if c.isDigit then "x" ++ cleaned else cleaned
    | [] => cleaned
  if isKeyword cleaned then "«" ++ cleaned ++ "»" else cleaned

/-- Quote a whole identifier if Lean would reject it bare. -/
def finalizeIdent (s : String) : String :=
  let s :=
    match s.toList with
    | c :: _ => if c.isDigit then "x" ++ s else s
    | [] => "x"
  if isKeyword s then "«" ++ s ++ "»" else s

/-- Flatten without quoting. Composing names (`prefix_typename`,
`record.field`) must use this form; quoting a part and then appending to it
produces `«mutual»_expr`, which is not an identifier. -/
def flattenRaw (rocq : String) : String :=
  String.intercalate "_" ((rocq.splitOn ".").map sanitizeComponent)

/-- Flatten a Rocq global name into one Lean identifier. Deterministic, and
used both where a name is declared and where it is referenced. Quoting happens
once, on the joined identifier. -/
def flatten (rocq : String) : String :=
  finalizeIdent (flattenRaw rocq)

/-! ## The trusted mapping

Every entry below asserts that the Rocq global and the Lean global are the same
theory for the purposes of translation. That is an assumption, not a theorem.
-/

/-- Rocq inductives that are rendered as a Lean type constructor. -/
def mappedTypes : List (String × Nat × String) :=
  [ ("Corelib.Init.Datatypes.nat", 0, "Nat")
  , ("Corelib.Init.Datatypes.bool", 0, "Bool")
  , ("Corelib.Init.Datatypes.unit", 0, "PUnit")
  , ("Corelib.Init.Datatypes.prod", 0, "Prod")
  , ("Corelib.Init.Datatypes.sum", 0, "Sum")
  , ("Corelib.Init.Datatypes.list", 0, "List")
  , ("Corelib.Init.Datatypes.option", 0, "Option")
  , ("Corelib.Init.Logic.True", 0, "True")
  , ("Corelib.Init.Logic.False", 0, "False")
  , ("Corelib.Init.Logic.and", 0, "And")
  , ("Corelib.Init.Logic.or", 0, "Or")
  , ("Corelib.Init.Logic.eq", 0, "Eq")
  , ("Corelib.Init.Logic.ex", 0, "Exists")
  , ("Corelib.Init.Datatypes.comparison", 0, "Rocq2Lean.Comparison")
  , ("Corelib.Init.Specif.sumbool", 0, "Rocq2Lean.Sumbool")
  ]

/-- Rocq constructors that are rendered as a Lean constructor. The second number
is the type's index in its mutual block, the third the constructor's index. -/
def mappedCtors : List (String × Nat × Nat × String) :=
  [ ("Corelib.Init.Datatypes.nat", 0, 0, "Nat.zero")
  , ("Corelib.Init.Datatypes.nat", 0, 1, "Nat.succ")
  , ("Corelib.Init.Datatypes.bool", 0, 0, "Bool.true")
  , ("Corelib.Init.Datatypes.bool", 0, 1, "Bool.false")
  , ("Corelib.Init.Datatypes.unit", 0, 0, "PUnit.unit")
  , ("Corelib.Init.Datatypes.prod", 0, 0, "Prod.mk")
  , ("Corelib.Init.Datatypes.sum", 0, 0, "Sum.inl")
  , ("Corelib.Init.Datatypes.sum", 0, 1, "Sum.inr")
  , ("Corelib.Init.Datatypes.list", 0, 0, "List.nil")
  , ("Corelib.Init.Datatypes.list", 0, 1, "List.cons")
  -- Rocq declares `Some` first and `None` second.
  , ("Corelib.Init.Datatypes.option", 0, 0, "Option.some")
  , ("Corelib.Init.Datatypes.option", 0, 1, "Option.none")
  , ("Corelib.Init.Logic.True", 0, 0, "True.intro")
  , ("Corelib.Init.Logic.and", 0, 0, "And.intro")
  , ("Corelib.Init.Logic.or", 0, 0, "Or.inl")
  , ("Corelib.Init.Logic.or", 0, 1, "Or.inr")
  , ("Corelib.Init.Logic.eq", 0, 0, "Eq.refl")
  , ("Corelib.Init.Logic.ex", 0, 0, "Exists.intro")
  , ("Corelib.Init.Datatypes.comparison", 0, 0, "Rocq2Lean.Comparison.eq")
  , ("Corelib.Init.Datatypes.comparison", 0, 1, "Rocq2Lean.Comparison.lt")
  , ("Corelib.Init.Datatypes.comparison", 0, 2, "Rocq2Lean.Comparison.gt")
  , ("Corelib.Init.Specif.sumbool", 0, 0, "Rocq2Lean.Sumbool.left")
  , ("Corelib.Init.Specif.sumbool", 0, 1, "Rocq2Lean.Sumbool.right")
  ]

/-- Mapped constructors whose *pattern* form differs from their name. Rocq's
`eq_refl` has no non-parameter arguments (the value is a parameter of `eq`),
while Lean's `Eq.refl` takes the value explicitly, so a pattern must leave room
for it. -/
def mappedCtorPatterns : List (String × Nat × Nat × String) :=
  [ ("Corelib.Init.Logic.eq", 0, 0, "Eq.refl _") ]

/-- Rocq constants that are rendered as a Lean constant with the same argument
order. The Lean side lives in `Rocq2Lean.Prelude` and keeps Rocq's explicit
binders, which is what makes kernel applications line up. -/
def mappedConstants : List (String × String) :=
  [ ("Corelib.Init.Logic.not", "Not")
  , ("Corelib.Init.Logic.iff", "Iff")
  , ("Corelib.Init.Logic.eq_ind", "Rocq2Lean.eq_ind")
  , ("Corelib.Init.Logic.eq_ind_r", "Rocq2Lean.eq_ind_r")
  , ("Corelib.Init.Logic.eq_rect_r", "Rocq2Lean.eq_rect_r")
  , ("Corelib.Init.Logic.eq_rec_r", "Rocq2Lean.eq_rec_r")
  , ("Corelib.Init.Logic.eq_rect", "Rocq2Lean.eq_rect")
  , ("Corelib.Init.Logic.eq_rec", "Rocq2Lean.eq_rec")
  , ("Corelib.Init.Logic.eq_sym", "Rocq2Lean.eq_sym")
  , ("Corelib.Init.Logic.eq_trans", "Rocq2Lean.eq_trans")
  , ("Corelib.Init.Logic.True_ind", "Rocq2Lean.True_ind")
  , ("Corelib.Init.Logic.False_ind", "Rocq2Lean.False_ind")
  , ("Corelib.Init.Logic.and_ind", "Rocq2Lean.and_ind")
  , ("Corelib.Init.Logic.or_ind", "Rocq2Lean.or_ind")
  , ("Corelib.Init.Logic.ex_ind", "Rocq2Lean.ex_ind")
  , ("Corelib.Init.Logic.iff_mp", "Rocq2Lean.iff_mp")
  , ("Corelib.Init.Logic.iff_mpr", "Rocq2Lean.iff_mpr")
  , ("Corelib.Init.Logic.proj1", "Rocq2Lean.proj1")
  , ("Corelib.Init.Logic.proj2", "Rocq2Lean.proj2")
  , ("Corelib.Init.Logic.f_equal", "Rocq2Lean.f_equal")
  , ("Corelib.Init.Datatypes.nat_ind", "Rocq2Lean.nat_ind")
  , ("Corelib.Init.Datatypes.nat_rect", "Rocq2Lean.nat_rect")
  , ("Corelib.Init.Datatypes.nat_rec", "Rocq2Lean.nat_rec")
  , ("Corelib.Init.Nat.add", "Rocq2Lean.add")
  , ("Corelib.Init.Nat.mul", "Rocq2Lean.mul")
  , ("Corelib.Init.Datatypes.andb", "Bool.and")
  , ("Corelib.Init.Datatypes.negb", "Bool.not")
  , ("Corelib.Init.Datatypes.fst", "Prod.fst")
  , ("Corelib.Init.Datatypes.snd", "Prod.snd")
  , ("Corelib.Init.Datatypes.app", "List.append")
  , ("Corelib.Init.Datatypes.length", "List.length")
  , ("Corelib.Init.Datatypes.list_rect", "List.rec")
  , ("Corelib.Init.Datatypes.list_ind", "List.rec")
  , ("Corelib.Init.Datatypes.list_rec", "List.rec")
  , ("Corelib.Init.Datatypes.option_rect", "Option.rec")
  , ("Corelib.Init.Datatypes.option_ind", "Option.rec")
  , ("Corelib.Init.Datatypes.option_rec", "Option.rec")
  , ("Corelib.Init.Datatypes.bool_rect", "Bool.rec")
  , ("Corelib.Init.Datatypes.bool_ind", "Bool.rec")
  , ("Corelib.Init.Datatypes.bool_rec", "Bool.rec")
  , ("Corelib.Init.Datatypes.comparison_rect", "Rocq2Lean.Comparison.rec")
  , ("Corelib.Init.Datatypes.comparison_ind", "Rocq2Lean.Comparison.rec")
  , ("Corelib.Init.Datatypes.comparison_rec", "Rocq2Lean.Comparison.rec")
  , ("Corelib.Init.Specif.sumbool_rect", "Rocq2Lean.Sumbool.rec")
  , ("Corelib.Init.Specif.sumbool_ind", "Rocq2Lean.Sumbool.rec")
  , ("Corelib.Init.Specif.sumbool_rec", "Rocq2Lean.Sumbool.rec")
  , ("Corelib.Init.Peano.lt", "Nat.lt")
  , ("Corelib.Init.Wf.well_founded", "WellFounded")
  , ("Corelib.Init.Wf.Fix", "Rocq2Lean.WfFix")
  , ("Corelib.Init.Datatypes.orb", "Bool.or")
  , ("Corelib.Init.Datatypes.CompOpp", "Rocq2Lean.CompOpp")
  , ("Corelib.Program.Basics.impl", "Rocq2Lean.impl")
  , ("Corelib.Program.Basics.flip", "Rocq2Lean.flip")
  ]

def mappedInd (block : String) (index : Nat) : Option String :=
  (mappedTypes.find? fun (b, i, _) => b == block && i == index).map fun (_, _, n) => n

def mappedCtor (block : String) (index ctor : Nat) : Option String :=
  (mappedCtors.find? fun (b, i, c, _) => b == block && i == index && c == ctor).map
    fun (_, _, _, n) => n

def mappedCtorPattern (block : String) (index ctor : Nat) : Option String :=
  (mappedCtorPatterns.find? fun (b, i, c, _) => b == block && i == index && c == ctor).map
    fun (_, _, _, p) => p

def mappedConstant (name : String) : Option String :=
  (mappedConstants.find? fun (n, _) => n == name).map fun (_, lean) => lean

/-- A record's projection is a field of the Lean `structure`; Lean namespaces it
under the structure, and field identifiers are escaped the same way as any other
component. -/
def fieldName (label : String) : String := identOf label

end Rocq2Lean
