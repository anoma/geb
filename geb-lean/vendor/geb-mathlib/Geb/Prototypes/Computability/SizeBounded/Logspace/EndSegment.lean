/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Prototypes.Computability.SizeBounded.Logspace.Basic

set_option doc.verso true in
/-!
# The end-segment lemma

\[Kristiansen2005\] Lemma 4.5: for every function of the algebra
{lit}`[I, C_W; comp, simn]` there is a constant {lit}`m`, the length of its
longest constant, such that every value longer than {lit}`m` is an end
segment, a suffix, of one of the arguments. The paper's proof fixes the least
set containing the constants and the arguments and closed under end segments
and shows by induction on the expression that every value lies in it. The
proof here takes any predicate closed under tails and holding of every word
no longer than {lit}`m`, which the set of words that are short or a suffix of
an argument is, and shows that every expression whose constants are within
{lit}`m` preserves it, the constant {name}`Geb.SizeBounded.nsiConst` read off
the syntax being the length of the longest constant on a successor-free tree.

# Main definitions

* {lit}`SuffixClosed` — a predicate on words holding of the tail of every word
  it holds of.
* {lit}`Preserves` — a function carries environments satisfying a predicate to
  values satisfying it.

# Main statements

* {lit}`preserves_transport`, {lit}`preserves_srn`, {lit}`preserves_evalValue`,
  {lit}`preserves_eval` — the property transports along an equality of
  arities, simultaneous recursion on notation preserves it, one node preserves
  it when its children do, and every successor-free expression preserves it.
* {lit}`length_le_or_suffix` — every value of an expression of the subalgebra
  is no longer than the expression's constant or a suffix of an argument.
* {lit}`suffix_of_lt_length` — Lemma 4.5 as the paper states it.

# References

* \[Kristiansen2005\]

# Tags

logspace, end segment, suffix, simultaneous recursion on notation
-/

set_option doc.verso true

namespace Geb.SizeBounded.Logspace

open Cobham (Sem transport)

public section

/-- A predicate on words holding of the tail of every word it holds of. -/
@[expose] def SuffixClosed (P : List Bool → Prop) : Prop :=
  ∀ (c : Bool) (w : List Bool), P (c :: w) → P w

/-- A function carries environments satisfying {lit}`P` to values satisfying
{lit}`P`. -/
@[expose] def Preserves {n : ℕ} (P : List Bool → Prop) (f : Sem n) : Prop :=
  ∀ y : Fin n → List Bool, (∀ i, P (y i)) → P (f y)

/-- The property transports along an equality of arities. -/
theorem preserves_transport {P : List Bool → Prop} {i j : ℕ} (h : i = j) {f : Sem i}
    (hf : Preserves P f) : Preserves P (transport h f) := by
  subst h
  exact hf

/-- Every slot of a step environment satisfies {lit}`P` when its three parts do. -/
theorem stepEnv_prop {P : List Bool → Prop} {a b : ℕ} (v : List Bool) (vals : Fin b → List Bool)
    (x : Fin a → List Bool) (hv : P v) (hvals : ∀ l, P (vals l)) (hx : ∀ i, P (x i)) :
    ∀ s, P (stepEnv v vals x s) :=
  Fin.cases hv (fun s ↦
    Fin.addCases (motive := fun s ↦ P (stepEnv v vals x s.succ))
      (fun l ↦ by beta_reduce; unfold stepEnv; rw [Fin.cons_succ, Fin.append_left]; exact hvals l)
      (fun i ↦ by beta_reduce; unfold stepEnv; rw [Fin.cons_succ, Fin.append_right]; exact hx i) s)

/-- Simultaneous recursion on notation preserves a suffix-closed property its
bases and steps preserve: the recursion variable's suffixes satisfy it, so each
step's environment does. -/
theorem preserves_srn {P : List Bool → Prop} (hP : SuffixClosed P) {a b : ℕ} {g : Fin b → Sem a}
    {h : Bool → Fin b → Sem (b + a + 1)} (hg : ∀ l, Preserves P (g l))
    (hh : ∀ i l, Preserves P (h i l)) (j : Fin b) :
    Preserves P (fun x : Fin (a + 1) → List Bool ↦ evalSRN g h (x 0) j (Fin.tail x)) := by
  intro x hx
  have hy : ∀ i, P (Fin.tail x i) := fun i ↦ hx i.succ
  have key : ∀ (w : List Bool), P w → ∀ l, P (evalSRN g h w l (Fin.tail x)) := by
    refine List.rec (fun _ l ↦ hg l _ hy) (fun i v ih hw l ↦ ?_)
    have hv : P v := hP i v hw
    exact hh i l (stepEnv v (fun l ↦ evalSRN g h v l (Fin.tail x)) (Fin.tail x))
      (stepEnv_prop _ _ _ hv (ih hv) hy)
  exact key (x 0) (hx 0) j

/-- One successor-free node preserves a suffix-closed property holding of every
word within its constant when each child does. -/
theorem preserves_evalValue {P : List Bool → Prop} (hP : SuffixClosed P) {m : ℕ}
    (hm : ∀ w : List Bool, w.length ≤ m → P w) (a : Shape) (c : Direction a → Σ i, Sem i)
    (h : ∀ b, (c b).1 = rc a b) (kb : Direction a → Bool) (hkb : sbsFreeValue a kb = true)
    (k : Direction a → ℕ) (hk : nsiValue a k ≤ m)
    (hc : ∀ b, kb b = true → k b ≤ m → Preserves P (c b).2) :
    Preserves P (evalValue a c h) := by
  cases a with
  | const n w => exact fun _ _ ↦ hm w hk
  | proj n i => exact fun y hy ↦ hy i
  | sbs b => exact absurd hkb Bool.false_ne_true
  | comp n m' =>
    change Preserves P (fun x : Fin n → List Bool ↦ transport (h (.inl ())) (c (.inl ())).2
      (fun i ↦ transport (h (.inr i)) (c (.inr i)).2 x))
    change (kb (.inl ()) && finAll m' fun i ↦ kb (.inr i)) = true at hkb
    rw [Bool.and_eq_true, finAll_eq_true_iff] at hkb
    change max (k (.inl ())) (finMax m' fun i ↦ k (.inr i)) ≤ m at hk
    intro y hy
    refine preserves_transport _ (hc _ hkb.1 (by omega)) _ fun i ↦ ?_
    have := le_finMax m' (fun i ↦ k (.inr i)) i
    exact preserves_transport _ (hc _ (hkb.2 i) (by omega)) _ hy
  | srn a b j =>
    change (finAll b (fun l ↦ kb (.inl l)) &&
      (finAll b (fun l ↦ kb (.inr (.inl l))) && finAll b fun l ↦ kb (.inr (.inr l)))) = true
      at hkb
    rw [Bool.and_eq_true, Bool.and_eq_true, finAll_eq_true_iff, finAll_eq_true_iff,
      finAll_eq_true_iff] at hkb
    change max (finMax b fun l ↦ k (.inl l))
      (max (finMax b fun l ↦ k (.inr (.inl l))) (finMax b fun l ↦ k (.inr (.inr l)))) ≤ m at hk
    refine preserves_srn hP (fun l ↦ ?_) (fun i l ↦ ?_) j
    · have := le_finMax b (fun l ↦ k (.inl l)) l
      exact preserves_transport _ (hc _ (hkb.1 l) (by omega))
    · cases i
      · have := le_finMax b (fun l ↦ k (.inr (.inl l))) l
        exact preserves_transport _ (hc (.inr (.inl l)) (hkb.2.1 l) (by omega))
      · have := le_finMax b (fun l ↦ k (.inr (.inr l))) l
        exact preserves_transport _ (hc (.inr (.inr l)) (hkb.2.2 l) (by omega))

/-- Every successor-free expression whose constants are within {lit}`m`
preserves a suffix-closed property holding of every word within {lit}`m`: the
form of \[Kristiansen2005\] Lemma 4.5's induction. -/
theorem preserves_eval {P : List Bool → Prop} (hP : SuffixClosed P) {m : ℕ}
    (hm : ∀ w : List Bool, w.length ≤ m → P w) :
    ∀ e : S, sbsFree e.1 = true → nsiConst e.1 ≤ m → Preserves P (eval e).2 :=
  SlicePFunctor.W.induction fun x ih hfree hk ↦
    preserves_evalValue hP hm x.1.1 (fun b ↦ eval (x.1.2 b)) _ (fun b ↦ sbsFree (x.1.2 b).1)
      hfree (fun b ↦ nsiConst (x.1.2 b).1) hk ih

/-- Every value of an expression of the subalgebra is no longer than the
expression's constant or a suffix of one of the arguments. -/
theorem length_le_or_suffix {n : ℕ} (e : LOf n) (x : Fin n → List Bool) :
    (e.sem x).length ≤ nsiConst e.1.1.1 ∨ ∃ i, e.sem x <:+ x i := by
  have hP : SuffixClosed fun w ↦ w.length ≤ nsiConst e.1.1.1 ∨ ∃ i, w <:+ x i := by
    intro c w hw
    cases hw with
    | inl hl => exact Or.inl (by rw [List.length_cons] at hl; omega)
    | inr hs =>
      obtain ⟨i, hi⟩ := hs
      exact Or.inr ⟨i, (List.suffix_cons c w).trans hi⟩
  have hx : ∀ i, (fun w ↦ w.length ≤ nsiConst e.1.1.1 ∨ ∃ i, w <:+ x i) (x i) :=
    fun i ↦ Or.inr ⟨i, List.suffix_refl _⟩
  exact preserves_transport _ (preserves_eval hP (fun _ h ↦ Or.inl h) e.1.1 e.2 (Nat.le_refl _))
    x hx

/-- \[Kristiansen2005\] Lemma 4.5: a value longer than the expression's
constant is a suffix of one of the arguments. -/
theorem suffix_of_lt_length {n : ℕ} (e : LOf n) (x : Fin n → List Bool)
    (h : nsiConst e.1.1.1 < (e.sem x).length) : ∃ i, e.sem x <:+ x i := by
  cases length_le_or_suffix e x with
  | inl hl => omega
  | inr hs => exact hs

end

end Geb.SizeBounded.Logspace
