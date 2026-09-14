/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.Triage.Reduction

set_option doc.verso true

/-!
# Serialized size of one visual triage step

Sizes count actual bits of the tagged, unshared binary-tree encoding. In
particular, both occurrences of a duplicated argument count in the output.

## Main definitions

* {lit}`Value.bits` and {lit}`Expr.bits` compute serialized bit lengths.

## Main statements

* {lit}`Expr.length_encode` identifies the structural measure with concrete length.
* {lit}`contract_bits_le` and {lit}`step_bits_le` bound a successor by twice its input.

## Tags

tree calculus, bitstring, output size, duplication
-/

@[expose] public section

namespace Geb.Triage

/-- Bit length of a value, with the constructor tags charged explicitly. -/
def Value.bits : Value → ℕ := WType.elim ℕ fun x ↦
  match x with
  | ⟨.leaf, _⟩ => 2
  | ⟨.stem, f⟩ => 5 + f ()
  | ⟨.fork, f⟩ => 6 + f false + f true

@[simp] theorem Value.bits_leaf : Value.leaf.bits = 2 := rfl

@[simp] theorem Value.bits_stem (v : Value) : (Value.stem v).bits = 5 + v.bits := rfl

@[simp] theorem Value.bits_fork (v w : Value) :
    (Value.fork v w).bits = 6 + v.bits + w.bits := rfl

/-- Bit length of an expression, including all application tags and embedded values. -/
def Expr.bits : Expr → ℕ := WType.elim ℕ fun x ↦
  match x with
  | ⟨some v, _⟩ => v.bits
  | ⟨none, f⟩ => 8 + f false + f true

@[simp] theorem Expr.bits_value (v : Value) : (Expr.value v).bits = v.bits := rfl

@[simp] theorem Expr.bits_app (f x : Expr) : (Expr.app f x).bits = 8 + f.bits + x.bits := rfl

/-- The structural value measure is the length of its actual bitstring encoding. -/
theorem Value.length_encode (v : Value) : (BitTree.encode v.toTree).length = v.bits :=
  Value.value_ind (P := fun v ↦ (BitTree.encode v.toTree).length = v.bits)
    rfl (fun v hv ↦ by simp [hv]; omega) (fun v w hv hw ↦ by simp [hv, hw]; omega) v

/-- The structural expression measure is the length of its actual bitstring encoding. -/
@[simp] theorem Expr.length_encode (e : Expr) : e.encode.length = e.bits :=
  Expr.expr_ind (P := fun e ↦ e.encode.length = e.bits) Value.length_encode
    (fun f x hf hx ↦ by
      change (BitTree.encode f.toTree).length = _ at hf
      change (BitTree.encode x.toTree).length = _ at hx
      simp [Expr.encode, hf, hx]; omega) e

/-- Each value has a nonempty, at least two-bit representation. -/
theorem Value.two_le_bits (v : Value) : 2 ≤ v.bits :=
  Value.value_ind (P := fun v ↦ 2 ≤ v.bits) (by rfl)
    (fun _ _ ↦ by simp; omega) (fun _ _ _ _ ↦ by simp; omega) v

/-- Each expression has a nonempty, at least two-bit representation. -/
theorem Expr.two_le_bits (e : Expr) : 2 ≤ e.bits :=
  Expr.expr_ind (P := fun e ↦ 2 ≤ e.bits) Value.two_le_bits
    (fun _ _ _ _ ↦ by simp; omega) e

/-- Every root rule, including duplication, uses at most twice the input bits. -/
theorem contract_bits_le (f x : Value) :
    (contract f x).bits ≤ 2 * (Expr.app (Expr.value f) (Expr.value x)).bits := by
  refine Value.value_ind (P := fun f ↦
    (contract f x).bits ≤ 2 * (Expr.app (Expr.value f) (Expr.value x)).bits) ?_ ?_ ?_ f
  · simp; omega
  · intro a _
    simp; omega
  · intro a b _ _
    refine Value.value_ind (P := fun a ↦
      (contract (Value.fork a b) x).bits ≤
        2 * (Expr.app (Expr.value (Value.fork a b)) (Expr.value x)).bits) ?_ ?_ ?_ a
    · simp; omega
    · intro u _
      simp; omega
    · intro u v _ _
      refine Value.value_ind (P := fun x ↦
        (contract (Value.fork (Value.fork u v) b) x).bits ≤
          2 * (Expr.app (Expr.value (Value.fork (Value.fork u v) b)) (Expr.value x)).bits)
        ?_ ?_ ?_ x
      · simp; omega
      · intro z _
        simp; omega
      · intro z w _ _
        simp; omega

/-- Replacing one redex in an application context preserves the factor-two size bound. -/
theorem step_bits_le (e : Expr) : ∀ e', step e = some e' → e'.bits ≤ 2 * e.bits := by
  refine Expr.expr_ind (P := fun e ↦ ∀ e', step e = some e' → e'.bits ≤ 2 * e.bits) ?_ ?_ e
  · intro v e' h
    simp at h
  · intro f x hf hx e' h
    rw [step_app] at h
    cases hsx : step x with
    | some x' =>
      simp only [hsx, Option.some.injEq] at h
      subst e'
      have hb := hx x' hsx
      simp only [Expr.bits_app]
      omega
    | none =>
      obtain ⟨xv, rfl⟩ := (step_eq_none_iff x).mp hsx
      cases hsf : step f with
      | some f' =>
        simp [hsf] at h
        subst e'
        have hb := hf f' hsf
        simp only [Expr.bits_app]
        omega
      | none =>
        obtain ⟨fv, rfl⟩ := (step_eq_none_iff f).mp hsf
        have he : contract fv xv = e' := by simpa using h
        subst e'
        exact contract_bits_le fv xv

end Geb.Triage
