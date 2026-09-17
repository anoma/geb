/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.Triage.Machine
public import Geb.Prototypes.Computability.Triage.Decode

set_option doc.verso true in
/-!
# Traversal resources and concrete serialized storage

The traversal machine terminates within a linear number of abstract transitions.
Its configurations have actual bitstring representations of linear length,
counting both copies of duplicated subtrees. The tokenizer retains a bounded
header, and successful stack decoding conserves the spelling of the tokens.

## Main definitions

* {lit}`Machine.stateCode` serializes the retained machine data.
* {lit}`Machine.work` accumulates an explicitly supplied per-transition cost.

## Main statements

* {lit}`Machine.stateCode_run_length_le` bounds all intermediate serialized states.
* {lit}`Machine.work_run_bound` gives a quadratic bound provided each transition
  has a linear implementation cost in the retained state size.
* {lit}`tokenStep_buffer_lt` bounds the tokenizer's incomplete header.
* {lit}`decoded_stack_bits` bounds the stored decoded expressions exactly by their spelling.

## Implementation notes

The work theorem has an explicit cost hypothesis. It does not certify a
multitape Turing-machine implementation of an abstract transition, nor the
end-to-end parser and serializer runtime. Establishing those refinements is
necessary before claiming {lit}`ComputableInTimeAndSpace` for the bitstring reducer.

## Tags

tree calculus, space complexity, cost semantics, abstract machine
-/

set_option doc.verso true

@[expose] public section

namespace Geb.Triage

/-- A live tokenizer never retains an eight-bit incomplete header. -/
theorem tokenStep_buffer_lt (st : TokenState) (b : Bool) (ss : List Symbol) (buf : List Bool)
    (h : tokenStep st b = some (ss, buf)) : buf.length < 8 := by
  cases st with
  | none => cases h
  | some pair =>
    obtain ⟨ts, pending⟩ := pair
    simp only [tokenStep, bind, Option.bind] at h
    cases hr : readSymbol (pending ++ [b]) with
    | some s =>
      simp only [hr] at h
      cases h
      decide
    | none =>
      simp only [hr] at h
      split at h
      · cases h
        assumption
      · cases h

/-- Serialized bits in a stack are exactly the spelling length of its tokens. -/
theorem stack_bits_eq (st : List Expr) :
    (st.map Expr.bits).sum = ((stackSymbols st).flatMap Symbol.code).length := by
  refine List.rec ?_ ?_ st
  · rfl
  · intro e st ih
    simp only [List.map_cons, List.sum_cons, stackSymbols, List.flatMap_cons,
      List.flatMap_append, List.length_append] at ih ⊢
    rw [← e.encode_eq_symbols, e.length_encode, ih]

/-- A successful decode retains exactly the consumed spelling plus the initial stack. -/
theorem decoded_stack_bits (ss : List Symbol) (st st' : List Expr)
    (h : runSymbols ss st = some st') :
    (st'.map Expr.bits).sum = (ss.flatMap Symbol.code).length + (st.map Expr.bits).sum := by
  rw [stack_bits_eq, runSymbols_sound ss st st' h, List.flatMap_append,
    List.length_append, ← stack_bits_eq]

namespace Machine

/-- A frame uses one direction bit followed by its sibling expression. -/
def frameCode : Frame → List Bool
  | .inl x => false :: x.encode
  | .inr f => true :: f.encode

/-- A phase prefix followed by the focus and self-delimiting sibling encodings. -/
def stateCode : Cfg → List Bool
  | .seek e ctx => [false, false] ++ e.encode ++ ctx.flatMap frameCode
  | .rebuild e ctx => [false, true] ++ e.encode ++ ctx.flatMap frameCode
  | .done none => [true, false]
  | .done (some e) => [true, true] ++ e.encode

/-- The frame list requires only a single direction bit per retained sibling. -/
theorem length_frameCode (ctx : List Frame) :
    (ctx.flatMap frameCode).length = (ctx.map frameBits).sum + ctx.length :=
  List.rec rfl (fun frame ctx ih ↦ by
    cases frame <;> simp [frameCode, frameBits, ih] <;> omega) ctx

/-- The actual state encoding fits its accounted data footprint and a two-bit phase tag. -/
theorem length_stateCode_le (cfg : Cfg) : (stateCode cfg).length ≤ footprint cfg + 2 := by
  cases cfg with
  | seek e ctx =>
    simp only [stateCode, footprint, contextBits, List.length_append, length_frameCode,
      Expr.length_encode, List.length_cons, List.length_nil]
    omega
  | rebuild e ctx =>
    simp only [stateCode, footprint, contextBits, List.length_append, length_frameCode,
      Expr.length_encode, List.length_cons, List.length_nil]
    omega
  | done result => cases result <;> simp [stateCode, footprint]

/-- Every intermediate state has a concrete encoding of length at most twice the input plus two. -/
theorem stateCode_run_length_le (e : Expr) (n : ℕ) :
    (stateCode (run n (.seek e []))).length ≤ 2 * e.encode.length + 2 := by
  have h₁ := length_stateCode_le (run n (.seek e []))
  have h₂ := footprint_run_le e n
  rw [Expr.length_encode]
  omega

/-- Accumulated transition cost, with terminal configurations charged zero. -/
def work (charge : Cfg → ℕ) : ℕ → Cfg → ℕ :=
  Nat.rec (fun _ ↦ 0) (fun _ rec cfg ↦
    (if halted cfg then 0 else charge cfg) + rec (next cfg))

/-- A uniform linear transition-cost bound composes along the nonincreasing reserve. -/
theorem work_le (charge : Cfg → ℕ) (c : ℕ)
    (hc : ∀ cfg, charge cfg ≤ c * (footprint cfg + 1)) (n : ℕ) :
    ∀ cfg, work charge n cfg ≤ n * (c * (reserve cfg + 1)) := by
  refine Nat.rec ?_ ?_ n
  · intro cfg
    simp [work]
  · intro n ih cfg
    have h₁ := hc cfg
    have h₂ := footprint_le_reserve cfg
    have h₃ := ih (next cfg)
    have h₄ := reserve_next_le cfg
    have hmono := Nat.mul_le_mul_left n
      (Nat.mul_le_mul_left c (Nat.add_le_add_right h₄ 1))
    have hcharge : (if halted cfg then 0 else charge cfg) ≤ c * (reserve cfg + 1) := by
      split
      · exact Nat.zero_le _
      · exact h₁.trans (Nat.mul_le_mul_left c (Nat.add_le_add_right h₂ 1))
    change (if halted cfg then 0 else charge cfg) + work charge n (next cfg) ≤ _
    calc
      _ ≤ c * (reserve cfg + 1) + n * (c * (reserve cfg + 1)) :=
        Nat.add_le_add hcharge (h₃.trans hmono)
      _ = (n + 1) * (c * (reserve cfg + 1)) := by rw [Nat.add_mul]; omega

/-- Linear-cost implementations of traversal transitions give a quadratic total cost.
The hypothesis must be established for the chosen concrete machine implementation. -/
theorem work_run_bound (charge : Cfg → ℕ) (c : ℕ)
    (hc : ∀ cfg, charge cfg ≤ c * (footprint cfg + 1)) (e : Expr) :
    work charge (4 * e.bits + 2) (.seek e []) ≤ (4 * e.bits + 2) * (c * (2 * e.bits + 1)) := by
  simpa [reserve, contextBits] using work_le charge c hc (4 * e.bits + 2) (.seek e [])

end Machine

end Geb.Triage
