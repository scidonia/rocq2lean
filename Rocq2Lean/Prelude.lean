/-!
# Rocq-shaped prelude

This module holds the Lean side of every entry in `Rocq2Lean.Names.mappedConstants`.
Each definition keeps Rocq's *argument order and explicitness*, because the
translation feeds kernel applications straight through: a binder that Lean would
normally make implicit has to appear exactly where the kernel puts it, or the
generated term stops type checking.

Nothing here is proved correct against Rocq. The mapping is the trusted boundary
of the translation: `nat` means Lean's `Nat`, `add` below is Rocq's recursion
scheme rather than Lean's, and a proof term may only be carried across when the
definition it unfolds is carried across with the same shape.
-/

namespace Rocq2Lean

set_option linter.defProp false

universe u v

/-! ## `Corelib.Init.Logic` -/

/-- Rocq's `eq_ind`: `forall A x (P : A -> Prop), P x -> forall y, x = y -> P y`. -/
def eq_ind (A : Type u) (x : A) (P : A → Prop) (h : P x) (y : A) (e : x = y) : P y :=
  e ▸ h

/-- Rocq's `eq_rect`. -/
def eq_rect (A : Type u) (x : A) (P : A → Type v) (h : P x) (y : A) (e : x = y) : P y :=
  e ▸ h

/-- Rocq's `eq_ind_r`: the same elimination with the equality read right-to-left. -/
def eq_ind_r (A : Type u) (x : A) (P : A → Prop) (h : P x) (y : A) (e : y = x) : P y :=
  e.symm ▸ h

def eq_rect_r (A : Type u) (x : A) (P : A → Type v) (h : P x) (y : A) (e : y = x) : P y :=
  e.symm ▸ h

def eq_rec_r (A : Type u) (x : A) (P : A → Type v) (h : P x) (y : A) (e : y = x) : P y :=
  e.symm ▸ h

/-- Rocq's `eq_rec` (`P : A -> Set`, which is `Type` here). -/
def eq_rec (A : Type u) (x : A) (P : A → Type v) (h : P x) (y : A) (e : x = y) : P y :=
  e ▸ h

def eq_sym (A : Type u) (x y : A) (e : x = y) : y = x :=
  e.symm

def eq_trans (A : Type u) (x y z : A) (exy : x = y) (eyz : y = z) : x = z :=
  exy.trans eyz

/-- Rocq's `True_ind`: `forall P : Prop, P -> True -> P`. -/
def True_ind (P : Prop) (h : P) (_ : True) : P :=
  h

/-- Rocq's `False_ind`: `forall P : Prop, False -> P`. -/
def False_ind (P : Prop) (h : False) : P :=
  False.elim h

def and_ind (A B P : Prop) (f : A → B → P) (h : A ∧ B) : P :=
  f h.1 h.2

def or_ind (A B P : Prop) (f : A → P) (g : B → P) (h : A ∨ B) : P :=
  h.elim f g

def ex_ind (A : Type u) (P : A → Prop) (Q : Prop) (f : ∀ x, P x → Q)
    (h : ∃ x, P x) : Q :=
  h.elim f

def iff_mp (A B : Prop) (h : A ↔ B) : A → B :=
  h.1

def iff_mpr (A B : Prop) (h : A ↔ B) : B → A :=
  h.2

def proj1 (A B : Prop) (h : A ∧ B) : A :=
  h.1

def proj2 (A B : Prop) (h : A ∧ B) : B :=
  h.2

/-- Rocq's `f_equal`: `forall A B (f : A -> B) x y, x = y -> f x = f y`. -/
def f_equal (A : Type u) (B : Type v) (f : A → B) (x y : A) (e : x = y) : f x = f y :=
  congrArg f e

/-! ## Datatypes that are not Lean's own

`comparison` and `sumbool` are Rocq inductives with no Lean native counterpart;
they are defined here with the same constructors and names, so patterns and
eliminators line up. -/

inductive Comparison where
  | eq
  | lt
  | gt

inductive Sumbool (A B : Prop) : Type where
  | left (a : A)
  | right (b : B)

/-- Rocq's `Program.Basics.impl`. -/
def impl (A B : Prop) : Prop := A → B

/-- Rocq's `Program.Basics.flip`. -/
def flip (A B C : Type u) (f : A → B → C) (b : B) (a : A) : C := f a b

/-- Rocq's `CompOpp`: the opposite ordering. -/
def CompOpp : Comparison → Comparison
  | .eq => .eq
  | .lt => .gt
  | .gt => .lt

/-- Rocq's well-founded fixpoint, with Rocq's argument order. Lean's
`WellFounded.fix` has the motive implicit; the adapter keeps the shape a kernel
application expects. -/
def WfFix (A : Type u) (R : A → A → Prop) (WF : WellFounded R) (P : A → Type v)
    (f : ∀ x, (∀ y, R y x → P y) → P x) (x : A) : P x :=
  WellFounded.fix WF f x

/-! ## `Corelib.Init.Nat`

Rocq recurses on the first argument; Lean's `Nat.add` recurses on the second.
Mapping one to the other would carry proof terms across a definition they do not
match, so these are Rocq's definitions written in Lean. -/

def add : Nat → Nat → Nat
  | 0, m => m
  | n + 1, m => Nat.succ (add n m)

def mul : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, m => add m (mul n m)

/-! ## Eliminators

Proof terms produced by `induction` name these constants, so they must exist even
when the translation turns the surrounding proof into a script. -/

def nat_ind (P : Nat → Prop) (h0 : P 0) (hs : ∀ n, P n → P (Nat.succ n)) : ∀ n, P n
  | 0 => h0
  | n + 1 => hs n (nat_ind P h0 hs n)

def nat_rect (P : Nat → Sort u) (h0 : P 0) (hs : ∀ n, P n → P (Nat.succ n)) : ∀ n, P n
  | 0 => h0
  | n + 1 => hs n (nat_rect P h0 hs n)

def nat_rec (P : Nat → Sort u) (h0 : P 0) (hs : ∀ n, P n → P (Nat.succ n)) : ∀ n, P n
  | 0 => h0
  | n + 1 => hs n (nat_rec P h0 hs n)

end Rocq2Lean
