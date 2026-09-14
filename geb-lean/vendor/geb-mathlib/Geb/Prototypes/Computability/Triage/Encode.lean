/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.Triage.Code

set_option doc.verso true

/-!
# Serialization without repeatedly copying subtrees

An encoding continuation prepends each constructor's fixed header exactly once.
The two-child cases thread the suffix through both child continuations, avoiding
concatenation of already materialized subtree encodings.

## Main definitions

* {lit}`Value.encodeInto` and {lit}`Expr.encodeInto` serialize in front of a suffix.
* {lit}`Expr.encodeFast` is the executable serializer used by the reducer.

## Main statements

* {lit}`Expr.encodeFast_eq` identifies this implementation with the established encoding.

## Tags

tree calculus, serialization, difference list, bitstring
-/

@[expose] public section

namespace Geb.Triage

/-- Serialize a value in front of a supplied suffix, copying only fixed-size headers. -/
def Value.encodeInto : Value → List Bool → List Bool :=
  WType.elim (List Bool → List Bool) fun x ↦ match x with
  | ⟨.leaf, _⟩ => fun tail ↦ Symbol.code .leaf ++ tail
  | ⟨.stem, f⟩ => fun tail ↦ Symbol.code .stem ++ f () tail
  | ⟨.fork, f⟩ => fun tail ↦ Symbol.code .fork ++ f false (f true tail)

/-- Continuation serialization agrees with the value's token spelling. -/
theorem Value.encodeInto_eq (v : Value) : ∀ tail,
    v.encodeInto tail = v.symbols.flatMap Symbol.code ++ tail :=
  Value.value_ind (P := fun v ↦ ∀ tail,
    v.encodeInto tail = v.symbols.flatMap Symbol.code ++ tail)
    (fun _ ↦ rfl)
    (fun v hv tail ↦ by
      change Symbol.code .stem ++ v.encodeInto tail = _
      simp [hv, List.append_assoc])
    (fun v w hv hw tail ↦ by
      change Symbol.code .fork ++ v.encodeInto (w.encodeInto tail) = _
      simp [hv, hw, List.append_assoc]) v

/-- Serialize an expression in front of a supplied suffix. -/
def Expr.encodeInto : Expr → List Bool → List Bool :=
  WType.elim (List Bool → List Bool) fun x ↦ match x with
  | ⟨some v, _⟩ => v.encodeInto
  | ⟨none, f⟩ => fun tail ↦ Symbol.code .app ++ f false (f true tail)

/-- Continuation serialization agrees with the expression's token spelling. -/
theorem Expr.encodeInto_eq (e : Expr) : ∀ tail,
    e.encodeInto tail = e.symbols.flatMap Symbol.code ++ tail :=
  Expr.expr_ind (P := fun e ↦ ∀ tail,
    e.encodeInto tail = e.symbols.flatMap Symbol.code ++ tail)
    Value.encodeInto_eq
    (fun f x hf hx tail ↦ by
      change Symbol.code .app ++ f.encodeInto (x.encodeInto tail) = _
      simp [hf, hx, List.append_assoc]) e

/-- Materialize the expression's bitstring with one fixed-header emission per constructor. -/
def Expr.encodeFast (e : Expr) : List Bool := e.encodeInto []

/-- The executable serializer has exactly the established binary-tree representation. -/
@[simp] theorem Expr.encodeFast_eq (e : Expr) : e.encodeFast = e.encode := by
  simp [encodeFast, encodeInto_eq, encode_eq_symbols]

end Geb.Triage
