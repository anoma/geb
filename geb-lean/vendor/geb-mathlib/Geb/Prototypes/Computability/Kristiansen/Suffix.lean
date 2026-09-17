/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.Kristiansen.Basic

set_option doc.verso true in
/-!
# The suffix invariant

Lemma 4.5 of \[Kristiansen2005\]: a word computed by the algebra is either
bounded in length by an expression-dependent constant or is a suffix of an input.
The proof follows the paper's invariant (4.6), preservation of a suffix-closed
set containing the constants and the inputs.

## Main definitions

* {lit}`Preserves` states this closure property for a semantic function.

## Main statements

* {lit}`preserves_sem` establishes the invariant for every expression.
* {lit}`short_or_suffix` states Lemma 4.5 as a disjunction.
* {lit}`suffix_of_length_gt` gives the paper's implication.

## References

* \[Kristiansen2005\], Lemma 4.5 and equation (4.6).

## Tags

function algebra, suffix, simultaneous recursion on notation, logspace
-/

set_option doc.verso true

namespace Geb.Kristiansen

open SizeBounded
open Cobham (Sem transport)

public section

/-- A function preserves every tail-closed set containing all words of length at most
{lit}`K`. Such a set contains the constants of an expression bounded by {lit}`K`. -/
@[expose] def Preserves {n : ℕ} (K : ℕ) (f : Sem n) : Prop :=
  ∀ E : List Bool → Prop, (∀ w, w.length ≤ K → E w) →
    (∀ i v, E (i :: v) → E v) → ∀ x, (∀ i, E (x i)) → E (f x)

/-- Increasing the bound reduces the collection of sets required to be preserved. -/
theorem preserves_mono {n K K' : ℕ} {f : Sem n} (hK : K ≤ K') (hf : Preserves K f) :
    Preserves K' f :=
  fun E hc ht ↦ hf E (fun w hw ↦ hc w (hw.trans hK)) ht

/-- Preservation is invariant under transport of the arity. -/
theorem preserves_transport {i j K : ℕ} (h : i = j) {f : Sem i} (hf : Preserves K f) :
    Preserves K (transport h f) := by
  subst h
  exact hf

/-- Composition preserves a tail-closed set when its head and arguments do. -/
theorem preserves_comp {n m Kh Kg : ℕ} {h : Sem m} {g : Fin m → Sem n}
    (hh : Preserves Kh h) (hg : ∀ i, Preserves Kg (g i)) :
    Preserves (max Kh Kg) (fun x ↦ h (fun i ↦ g i x)) := by
  intro E hc ht x hx
  exact hh E (fun w hw ↦ hc w (hw.trans (Nat.le_max_left _ _))) ht _
    (fun i ↦ hg i E (fun w hw ↦ hc w (hw.trans (Nat.le_max_right _ _))) ht x hx)

/-- Simultaneous recursion preserves the invariant for all components together. -/
theorem preserves_srn {a b Kg Kh : ℕ} {g : Fin b → Sem a}
    {h : Bool → Fin b → Sem (b + a + 1)}
    (hg : ∀ l, Preserves Kg (g l)) (hh : ∀ i l, Preserves Kh (h i l)) (j : Fin b) :
    Preserves (max Kg Kh)
      (fun x : Fin (a + 1) → List Bool ↦ evalSRN g h (x 0) j (Fin.tail x)) := by
  intro E hc ht x hx
  have hp : ∀ i, E (Fin.tail x i) := fun i ↦ hx i.succ
  have key : ∀ v : List Bool, E v → ∀ l, E (evalSRN g h v l (Fin.tail x)) := by
    refine List.rec (fun _ l ↦ ?_) (fun i v ih hv l ↦ ?_)
    · exact hg l E (fun w hw ↦ hc w (hw.trans (Nat.le_max_left _ _))) ht _ hp
    · have hv' := ht i v hv
      apply hh i l E (fun w hw ↦ hc w (hw.trans (Nat.le_max_right _ _))) ht
      refine Fin.cases hv' (fun s ↦ Fin.addCases ?_ ?_ s)
      · intro l
        simpa only [Fin.cons_succ, Fin.append_left, evalSRN] using ih hv' l
      · intro l
        simpa only [Fin.cons_succ, Fin.append_right] using hp l
  exact key (x 0) (hx 0) j

/-- An allowed node preserves the invariant when its children do. -/
theorem preserves_evalValue (a : Shape) (ha : AllowedShape a)
    (c : Direction a → Σ i, Sem i) (h : ∀ d, (c d).1 = rc a d)
    (K : Direction a → ℕ) (hk : ∀ d, Preserves (K d) (c d).2) :
    Preserves (nsiValue a K) (evalValue a c h) := by
  cases a with
  | const n w => exact fun E hc _ _ _ ↦ hc w (Nat.le_refl _)
  | proj n i => exact fun _ _ _ _ hx ↦ hx i
  | sbs b => exact ha.elim
  | comp n m =>
    change Preserves (max (K (.inl ())) (finMax m fun i ↦ K (.inr i)))
      (fun x : Fin n → List Bool ↦ transport (h (.inl ())) (c (.inl ())).2
        (fun i ↦ transport (h (.inr i)) (c (.inr i)).2 x))
    exact preserves_comp (preserves_transport _ (hk (.inl ())))
      (fun i ↦ preserves_mono (le_finMax m (fun i ↦ K (.inr i)) i)
        (preserves_transport _ (hk (.inr i))))
  | srn a b j =>
    refine preserves_srn (fun l ↦ preserves_mono (le_finMax b (fun l ↦ K (.inl l)) l)
      (preserves_transport _ (hk (.inl l)))) (fun i l ↦ ?_) j
    cases i
    · exact preserves_mono ((le_finMax b (fun l ↦ K (.inr (.inl l))) l).trans
        (Nat.le_max_left _ _)) (preserves_transport _ (hk (.inr (.inl l))))
    · exact preserves_mono ((le_finMax b (fun l ↦ K (.inr (.inr l))) l).trans
        (Nat.le_max_right _ _)) (preserves_transport _ (hk (.inr (.inr l))))

/-- Every allowed expression preserves the invariant, with its syntactic constant bound. -/
theorem preserves_eval : ∀ e : S, Allowed e.1 → Preserves (nsiConst e.1) (eval e).2 :=
  SlicePFunctor.W.induction fun x ih ha ↦
    preserves_evalValue x.1.1 ha.1 (fun d ↦ eval (x.1.2 d)) _ _ (fun d ↦ ih d (ha.2 d))

/-- Equation (4.6) of \[Kristiansen2005\], with the constants bounded by their maximum. -/
theorem preserves_sem {n : ℕ} (e : LOf n) : Preserves (nsiConst e.1.1.1) e.sem :=
  preserves_transport _ (preserves_eval e.1.1 e.2)

/-- Lemma 4.5 of \[Kristiansen2005\]: every output is short or an input suffix. -/
theorem short_or_suffix {n : ℕ} (e : LOf n) (x : Fin n → List Bool) :
    (e.sem x).length ≤ nsiConst e.1.1.1 ∨ ∃ i, e.sem x <:+ x i := by
  apply preserves_sem e (fun w ↦ w.length ≤ nsiConst e.1.1.1 ∨ ∃ i, w <:+ x i)
  · exact fun _ hw ↦ Or.inl hw
  · intro b v hv
    rcases hv with hv | ⟨i, hi⟩
    · exact Or.inl (by simp only [List.length_cons] at hv; omega)
    · exact Or.inr ⟨i, (List.suffix_cons b v).trans hi⟩
  · exact fun i ↦ Or.inr ⟨i, List.suffix_rfl⟩

/-- Above the expression's constant bound, its output is a suffix of an input word. -/
theorem suffix_of_length_gt {n : ℕ} (e : LOf n) (x : Fin n → List Bool)
    (h : nsiConst e.1.1.1 < (e.sem x).length) : ∃ i, e.sem x <:+ x i :=
  (short_or_suffix e x).resolve_left (Nat.not_le_of_gt h)

end

end Geb.Kristiansen
