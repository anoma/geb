/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.Triage.Syntax

set_option doc.verso true in
/-!
# Decoding constructor symbols of triage calculus

The concrete encoding has a fixed prefix code for each constructor. A reverse
preorder stack decoder checks the grammar as it builds expressions. In particular,
the stem and value-fork cases accept only values as their children.

## Main definitions

* {lit}`Symbol.code` is the bit prefix introduced by each constructor.
* {lit}`Expr.symbols` lists constructors in preorder.
* {lit}`build` and {lit}`runSymbols` decode using a stack of completed expressions.

## Main statements

* {lit}`Expr.encode_eq_symbols` connects symbols to the existing bit-tree serialization.
* {lit}`runSymbols_expr` is the decoder's round trip.
* {lit}`runSymbols_sound` reconstructs the consumed symbols from a successful decode.

## Tags

tree calculus, prefix code, parser, stack, serialization
-/

set_option doc.verso true

@[expose] public section

namespace Geb.Triage

/-- Constructor tokens, distinguishing applications from value forks. -/
inductive Symbol
  | leaf | stem | fork | app
  deriving DecidableEq, Repr

/-- The prefix contributed by a constructor to its binary-tree serialization. -/
def Symbol.code : Symbol → List Bool
  | .leaf => [false, false]
  | .stem => [true, false, true, false, false]
  | .fork => [true, false, true, true, false, true]
  | .app => [true, false, true, false, true, false, false, true]

/-- Preorder constructor symbols of a value. -/
def Value.symbols : Value → List Symbol := WType.elim (List Symbol) fun x ↦
  match x with
  | ⟨.leaf, _⟩ => [.leaf]
  | ⟨.stem, f⟩ => .stem :: f ()
  | ⟨.fork, f⟩ => .fork :: (f false ++ f true)

@[simp] theorem Value.symbols_leaf : Value.leaf.symbols = [.leaf] := rfl

@[simp] theorem Value.symbols_stem (v : Value) :
    (Value.stem v).symbols = .stem :: v.symbols := rfl

@[simp] theorem Value.symbols_fork (v w : Value) :
    (Value.fork v w).symbols = .fork :: (v.symbols ++ w.symbols) := rfl

/-- Preorder constructor symbols of an expression. -/
def Expr.symbols : Expr → List Symbol := WType.elim (List Symbol) fun x ↦
  match x with
  | ⟨some v, _⟩ => v.symbols
  | ⟨none, f⟩ => .app :: (f false ++ f true)

@[simp] theorem Expr.symbols_value (v : Value) : (Expr.value v).symbols = v.symbols := rfl

@[simp] theorem Expr.symbols_app (f x : Expr) :
    (Expr.app f x).symbols = .app :: (f.symbols ++ x.symbols) := rfl

/-- Value token spelling is exactly its binary-tree encoding. -/
theorem Value.encode_eq_symbols (v : Value) :
    BitTree.encode v.toTree = v.symbols.flatMap Symbol.code :=
  Value.value_ind (P := fun v ↦ BitTree.encode v.toTree = v.symbols.flatMap Symbol.code)
    rfl (fun v hv ↦ by simp [hv, Symbol.code])
    (fun v w hv hw ↦ by simp [hv, hw, Symbol.code]) v

/-- Expression token spelling is exactly its binary-tree encoding. -/
theorem Expr.encode_eq_symbols (e : Expr) : e.encode = e.symbols.flatMap Symbol.code :=
  Expr.expr_ind (P := fun e ↦ e.encode = e.symbols.flatMap Symbol.code)
    Value.encode_eq_symbols
    (fun f x hf hx ↦ by
      change BitTree.encode (Expr.app f x).toTree = _
      change BitTree.encode f.toTree = _ at hf
      change BitTree.encode x.toTree = _ at hx
      simp [hf, hx, Symbol.code]) e

/-- Reduce one reverse-preorder symbol against a stack of already decoded expressions. -/
def build : Symbol → List Expr → Option (List Expr)
  | .leaf, st => some (Expr.value Value.leaf :: st)
  | .stem, x :: st => x.getValue.map fun v ↦ Expr.value (Value.stem v) :: st
  | .fork, x :: y :: st => do
    let v ← x.getValue
    let w ← y.getValue
    pure (Expr.value (Value.fork v w) :: st)
  | .app, x :: y :: st => some (Expr.app x y :: st)
  | _, _ => none

/-- Decode a prefix token sequence right-to-left, retaining an arbitrary suffix stack. -/
def runSymbols (ss : List Symbol) (st : List Expr) : Option (List Expr) :=
  ss.foldr (fun s acc ↦ acc.bind (build s)) (some st)

@[simp] theorem runSymbols_nil (st : List Expr) : runSymbols [] st = some st := rfl

@[simp] theorem runSymbols_cons (s : Symbol) (ss : List Symbol) (st : List Expr) :
    runSymbols (s :: ss) st = (runSymbols ss st).bind (build s) := rfl

/-- Concatenation processes the right token sequence first. -/
theorem runSymbols_append (ss ts : List Symbol) (st : List Expr) :
    runSymbols (ss ++ ts) st = (runSymbols ts st).bind (runSymbols ss) :=
  List.rec (by rw [List.nil_append]; cases runSymbols ts st <;> rfl) (fun s ss ih ↦ by
    rw [List.cons_append, runSymbols_cons, ih]
    cases runSymbols ts st <;> rfl) ss

/-- Every value's symbols decode on top of any already decoded suffix. -/
theorem runSymbols_value (v : Value) : ∀ st,
    runSymbols v.symbols st = some (Expr.value v :: st) :=
  Value.value_ind (P := fun v ↦ ∀ st,
    runSymbols v.symbols st = some (Expr.value v :: st))
    (fun _ ↦ rfl)
    (fun v hv st ↦ by simp [hv, build])
    (fun v w hv hw st ↦ by simp [runSymbols_append, hv, hw, build]) v

/-- Every expression's symbols decode on top of any already decoded suffix. -/
theorem runSymbols_expr (e : Expr) : ∀ st,
    runSymbols e.symbols st = some (e :: st) :=
  Expr.expr_ind (P := fun e ↦ ∀ st, runSymbols e.symbols st = some (e :: st))
    runSymbols_value
    (fun f x hf hx st ↦ by simp [runSymbols_append, hf, hx, build]) e

/-- The token sequence represented by a stack of completed expressions. -/
def stackSymbols (st : List Expr) : List Symbol := st.flatMap Expr.symbols

/-- A successful constructor operation accounts for exactly one new token. -/
theorem build_sound (s : Symbol) (st st' : List Expr) (h : build s st = some st') :
    stackSymbols st' = s :: stackSymbols st := by
  cases s with
  | leaf =>
    cases h
    rfl
  | stem =>
    cases st with
    | nil => cases h
    | cons x st =>
      cases hx : x.getValue with
      | none => simp [build, hx] at h
      | some v =>
        have he := (Expr.getValue_eq_some_iff x v).mp hx
        subst x
        cases h
        simp [stackSymbols]
  | fork =>
    cases st with
    | nil => cases h
    | cons x st =>
      cases st with
      | nil => cases h
      | cons y st =>
        cases hx : x.getValue with
        | none => simp [build, hx] at h
        | some v =>
          cases hy : y.getValue with
          | none => simp [build, hx, hy] at h
          | some w =>
            have he := (Expr.getValue_eq_some_iff x v).mp hx
            have he' := (Expr.getValue_eq_some_iff y w).mp hy
            subst x y
            cases h
            simp [stackSymbols, List.append_assoc]
  | app =>
    cases st with
    | nil => cases h
    | cons x st =>
      cases st with
      | nil => cases h
      | cons y st =>
        cases h
        simp [stackSymbols, List.append_assoc]

/-- A successful stack decode accounts for the entire token sequence. -/
theorem runSymbols_sound (ss : List Symbol) : ∀ st st', runSymbols ss st = some st' →
    stackSymbols st' = ss ++ stackSymbols st := by
  refine List.rec ?_ ?_ ss
  · intro st st' h
    cases h
    rfl
  · intro s ss ih st st' h
    cases hr : runSymbols ss st with
    | none => simp [hr] at h
    | some mid =>
      have hb : build s mid = some st' := by simpa [hr] using h
      rw [build_sound s mid st' hb, ih st mid hr]
      rfl

end Geb.Triage
