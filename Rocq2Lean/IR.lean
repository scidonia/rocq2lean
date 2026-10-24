import Lean.Data.Json

/-!
# The intermediate representation

The extractor (OCaml, `extractor/`) writes one JSON document per Rocq file: the
kernel terms of every declaration, plus source locations. These types are the
typed view of that document. Parsing is strict: a field the extractor does not
write is an error here, not a silent default, because a translation that has to
guess is worse than one that stops.
-/

namespace Rocq2Lean

open Lean (Json)

structure SrcLoc where
  file : String := ""
  line : Nat := 0
  column : Nat := 0
  deriving Inhabited, Repr

inductive SortKind where
  | prop
  | set
  | type
  | sprop
  | other (raw : String)
  deriving Inhabited, Repr

mutual
  /-- A kernel term, as the extractor serialised it. -/
  inductive Term where
    | rel (n : Nat)
    | var (id : String)
    | sort (kind : SortKind)
    | cast (kind : String) (term : Term)
    | prod (name : Option String) (dom cod : Term)
    | lam (name : Option String) (dom body : Term)
    | letIn (name : Option String) (value ty body : Term)
    | app (fn : Term) (args : Array Term)
    | const (name : String)
    | ind (name : String) (index : Nat)
    | ctor (name : String) (index ctor : Nat)
    | caseExpr (indName : String) (indIndex : Nat) (params : Array Term) (nParams : Nat)
        (returnBinders : Array (Option String)) (motive : Term) (scrutinee : Term)
        (branches : Array Branch)
    | fix (selected : Nat) (functions : Array FixFunction)
    | cofix (selected : Nat) (functions : Array FixFunction)
    | proj (recordName : String) (recordIndex : Nat) (field : String) (term : Term)
    | intLit (value : String)
    | strLit (value : String)
    | unsupported (what : String)
    deriving Inhabited, Repr

  structure Branch where
    binders : Array (Option String)
    body : Term
    deriving Inhabited, Repr

  structure FixFunction where
    name : Option String
    recArg : Nat
    type : Term
    body : Term
    deriving Inhabited, Repr
end

structure Binder where
  name : Option String
  type : Term
  value : Option Term
  deriving Inhabited, Repr

structure Field where
  name : String
  type : Term
  deriving Inhabited, Repr

structure Ctor where
  name : String
  type : Term
  fields : Array Field
  deriving Inhabited, Repr

structure IndType where
  name : String
  arity : Term
  ctors : Array Ctor
  deriving Inhabited, Repr

/-- One declaration of the source file, in source order. -/
inductive Decl where
  | constant (name : String) (loc : Option SrcLoc) (form : String) (isProp : Bool)
      (hyps : Array Binder) (ty : Term) (body : Option Term)
  | inductiveDecl (name : String) (loc : Option SrcLoc) (finite : String) (isMutual : Bool)
      (record : Bool) (params : Array Binder) (types : Array IndType)
  | absorbed (name : String) (loc : Option SrcLoc) (why : String)
  | error (name : String) (loc : Option SrcLoc) (why : String)
  deriving Inhabited, Repr

structure File where
  source : String
  rocqVersion : String
  declarations : Array Decl
  deriving Inhabited, Repr

/-! ## Parsing -/

abbrev P := Except String

namespace Parse

def field (j : Json) (k : String) : P Json := do
  let fields ← j.getObj?
  match fields.get? k with
  | some v => pure v
  | none => throw s!"missing field '{k}'"

def str (j : Json) (k : String) : P String := do
  (← field j k).getStr?

def nat (j : Json) (k : String) : P Nat := do
  (← field j k).getNat?

def bool (j : Json) (k : String) : P Bool := do
  (← field j k).getBool?

def arr (j : Json) (k : String) : P (Array Json) := do
  (← field j k).getArr?

def optStr (j : Json) (k : String) : P (Option String) := do
  let v ← field j k
  match v with
  | .null => pure none
  | .str s => pure (some s)
  | other => throw s!"expected string or null in '{k}', got {other.compress}"

def optName (j : Json) (k : String) : P (Option String) := optStr j k

def optNameArray (j : Json) (k : String) : P (Array (Option String)) := do
  let xs ← arr j k
  xs.mapM fun x =>
    match x with
    | .null => pure none
    | .str s => pure (some s)
    | other => throw s!"expected string or null in '{k}', got {other.compress}"

def loc (j : Json) (k : String) : P (Option SrcLoc) := do
  let v ← field j k
  match v with
  | .null => pure none
  | .obj _ =>
      let file ← str v "file"
      let line ← nat v "line"
      let column ← nat v "column"
      pure (some { file, line, column })
  | other => throw s!"expected location object in '{k}', got {other.compress}"

partial def term (j : Json) : P Term := do
  let tag ← str j "t"
  match tag with
  | "rel" => return .rel (← nat j "n")
  | "var" => return .var (← str j "id")
  | "sort" => do
      let s ← field j "sort"
      let kind ← str s "s"
      match kind with
      | "prop" => return .sort .prop
      | "set" => return .sort .set
      | "type" => return .sort .type
      | "sprop" => return .sort .sprop
      | other => return .sort (.other other)
  | "cast" => return .cast (← str j "kind") (← term (← field j "term"))
  | "prod" => do
      return .prod (← optName j "name") (← term (← field j "dom")) (← term (← field j "cod"))
  | "lambda" => do
      return .lam (← optName j "name") (← term (← field j "dom")) (← term (← field j "body"))
  | "let" => do
      let name ← optName j "name"
      let value ← term (← field j "value")
      let ty ← term (← field j "type")
      let body ← term (← field j "body")
      return .letIn name value ty body
  | "app" => do
      let fn ← term (← field j "fn")
      let args ← arr j "args"
      return .app fn (← args.mapM term)
  | "const" => return .const (← str j "name")
  | "ind" => return .ind (← str j "name") (← nat j "index")
  | "ctor" => do
      let name ← str j "name"
      let index ← nat j "index"
      let ctor ← nat j "ctor"
      return .ctor name index ctor
  | "case" => do
      let indName ← str j "inductiveName"
      let indIndex ← nat j "inductiveIndex"
      let params ← (← arr j "params").mapM term
      let nParams ← nat j "nparams"
      let returnBinders ← optNameArray j "returnBinders"
      let motive ← term (← field j "motive")
      let scrutinee ← term (← field j "scrutinee")
      let branchesJson ← arr j "branches"
      let branches ← branchesJson.mapM fun b => do
        let binders ← optNameArray b "binders"
        let body ← term (← field b "body")
        return ({ binders, body } : Branch)
      return .caseExpr indName indIndex params nParams returnBinders motive scrutinee branches
  | "fix" => do
      let selected ← nat j "selected"
      let functions ← (← arr j "functions").mapM parseFunction
      return .fix selected functions
  | "cofix" => do
      let selected ← nat j "selected"
      let functions ← (← arr j "functions").mapM parseFunction
      return .cofix selected functions
  | "proj" => do
      let recordName ← str j "recordName"
      let recordIndex ← nat j "recordIndex"
      let fieldLabel ← str j "field"
      return .proj recordName recordIndex fieldLabel (← term (← field j "term"))
  | "int" => return .intLit (← str j "value")
  | "string" => return .strLit (← str j "value")
  | "unsupported" => return .unsupported (← str j "what")
  | other => throw s!"unknown term tag '{other}'"
where
  parseFunction (j : Json) : P FixFunction := do
    let name ← optName j "name"
    let recArg ← nat j "recArg"
    let type ← term (← field j "type")
    let body ← term (← field j "body")
    return { name, recArg, type, body }

def binder (j : Json) : P Binder := do
  let name ← optName j "name"
  let ty ← term (← field j "type")
  let value ←
    match ← field j "value" with
    | .null => pure none
    | v => some <$> term v
  return { name, type := ty, value }

def binders (j : Json) (k : String) : P (Array Binder) := do
  (← arr j k).mapM binder

def field' (j : Json) : P Field := do
  let name ← str j "name"
  let ty ← term (← field j "type")
  return { name, type := ty }

def ctor (j : Json) : P Ctor := do
  let name ← str j "name"
  let ty ← term (← field j "type")
  let fields ← (← arr j "fields").mapM field'
  return { name, type := ty, fields }

def indType (j : Json) : P IndType := do
  let name ← str j "name"
  let arity ← term (← field j "arity")
  let ctors ← (← arr j "ctors").mapM ctor
  return { name, arity, ctors }

def decl (j : Json) : P Decl := do
  let kind ← str j "kind"
  match kind with
  | "constant" => do
      let name ← str j "name"
      let loc ← loc j "loc"
      let form ← str j "form"
      let isProp ← bool j "isProp"
      let hyps ← binders j "hyps"
      let ty ← term (← field j "type")
      let body ←
        match ← field j "body" with
        | .null => pure none
        | v => some <$> term v
      return .constant name loc form isProp hyps ty body
  | "inductive" => do
      let name ← str j "name"
      let loc ← loc j "loc"
      let finite ← str j "finite"
      let isMutual ← bool j "mutual"
      let record ← bool j "record"
      let params ← binders j "params"
      let types ← (← arr j "types").mapM indType
      return .inductiveDecl name loc finite isMutual record params types
  | "absorbed" => return .absorbed (← str j "name") (← loc j "loc") (← str j "why")
  | "error" => return .error (← str j "name") (← loc j "loc") (← str j "why")
  | other => throw s!"unknown declaration kind '{other}'"

def file (j : Json) : P File := do
  let schema ← nat j "schema"
  if schema != 1 then throw s!"unsupported IR schema {schema}; this build reads schema 1"
  let source ← str j "source"
  let rocqVersion ← str j "rocqVersion"
  let declarations ← (← arr j "declarations").mapM decl
  return { source, rocqVersion, declarations }

end Parse

def File.parse (s : String) : P File := do
  let json ← Json.parse s
  Parse.file json

end Rocq2Lean
