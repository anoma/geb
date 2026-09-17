/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Combinators

set_option doc.verso true in
/-!
# Kristiansen's logspace algebra as the successor-free subalgebra

The function algebra {lit}`[I, C_W; comp, simn]` of \[Kristiansen2005\] § 4:
the projections and the word constants, closed under composition and
simultaneous recursion on notation, with no successor of any kind. Its
signature is that of \[Mazzanti2016\]'s algebra {name}`Geb.SizeBounded.S`
without the size-bounded successor, so its expressions are defined here as the
expressions of that algebra in which no {name}`Geb.SizeBounded.Shape.sbs` node
occurs, {lit}`sbsFree` folded over the tree, rather than as the admissible
trees of a second signature. The interpretation is inherited: an expression of
the subalgebra means what it means in {name}`Geb.SizeBounded.S`.

The paper's Corollary 4.8 characterizes the languages decidable in logarithmic
space as those decided by a unary function of this algebra, a function
deciding the language of the words it sends to the empty word. The
soundness half, that every such function is computable in logarithmic space,
rests on the paper's Lemma 4.5, stated in
{lit}`Geb.Prototypes.Computability.SizeBounded.Logspace.EndSegment`.

# Main definitions

* {lit}`finAll` — the conjunction of a finite family of booleans.
* {lit}`sbsFreeValue`, {lit}`sbsFree` — whether one node and its children, and
  a whole tree, contain no successor node.
* {lit}`LOf` — the expressions of the subalgebra of a given arity.
* {lit}`constL`, {lit}`projL`, {lit}`compL`, {lit}`srnL` — the constructors of
  the subalgebra, each carrying its successor-freeness.

# Main statements

* {lit}`finAll_eq_true_iff` — the conjunction holds exactly when every member
  does.
* {lit}`sbsFree_mk` — the fold's computation rule.
* {lit}`sbsFree_comp_iff`, {lit}`sbsFree_srn_iff` — a substitution or a
  recursion is successor-free exactly when its children are.

# References

* \[Kristiansen2005\]
* \[Mazzanti2016\]

# Tags

logspace, function algebra, simultaneous recursion on notation, W-type
-/

set_option doc.verso true

namespace Geb.SizeBounded.Logspace

public section

/-- The conjunction of a finite family, by recursion on its length. -/
@[expose] def finAll : (m : ℕ) → (Fin m → Bool) → Bool :=
  Nat.rec (fun _ ↦ true) fun m ih f ↦ ih (fun i ↦ f i.castSucc) && f (Fin.last m)

/-- The conjunction holds exactly when every member does. -/
theorem finAll_eq_true_iff : ∀ (m : ℕ) (f : Fin m → Bool), finAll m f = true ↔ ∀ i, f i = true :=
  Nat.rec (fun _ ↦ ⟨fun _ i ↦ i.elim0, fun _ ↦ rfl⟩) fun m ih f ↦ by
    change (finAll m (fun i ↦ f i.castSucc) && f (Fin.last m)) = true ↔ _
    rw [Bool.and_eq_true, ih]
    constructor
    · intro h i
      exact Fin.lastCases (motive := fun i ↦ f i = true) h.2 h.1 i
    · intro h
      exact ⟨fun i ↦ h _, h _⟩

/-- One node contains no successor when it is not one and its children contain
none. -/
@[expose] def sbsFreeValue : (a : Shape) → (Direction a → Bool) → Bool
  | .const _ _, _ => true
  | .proj _ _, _ => true
  | .sbs _, _ => false
  | .comp _ m, k => k (.inl ()) && finAll m fun i ↦ k (.inr i)
  | .srn _ b _, k =>
      finAll b (fun l ↦ k (.inl l)) &&
        (finAll b (fun l ↦ k (.inr (.inl l))) && finAll b fun l ↦ k (.inr (.inr l)))

/-- Whether a tree contains no successor node, by folding {name}`sbsFreeValue`
over it. -/
@[expose] def sbsFree : sig.toPFunctor.W → Bool :=
  WType.elim Bool fun x ↦ sbsFreeValue x.1 x.2

/-- The fold's computation rule. -/
theorem sbsFree_mk (a : Shape) (f : Direction a → sig.toPFunctor.W) :
    sbsFree (WType.mk a f) = sbsFreeValue a fun d ↦ sbsFree (f d) := rfl

/-- The expressions of the subalgebra {lit}`[I, C_W; comp, simn]` of
\[Kristiansen2005\] of a given arity: the successor-free expressions of
{name}`Geb.SizeBounded.S` of that arity. -/
@[expose] def LOf (n : ℕ) : Type := { e : SOf n // sbsFree e.1.1 = true }

/-- The meaning of an expression of the subalgebra: its meaning in
{name}`Geb.SizeBounded.S`. -/
@[expose] def LOf.sem {n : ℕ} (e : LOf n) : Cobham.Sem n := e.1.sem

/-- The constant word {lit}`w` at arity {lit}`n`. -/
@[expose] def constL (n : ℕ) (w : List Bool) : LOf n := ⟨constOf n w, rfl⟩

/-- The {lit}`i`th of {lit}`n` variables. -/
@[expose] def projL (n : ℕ) (i : Fin n) : LOf n := ⟨projOf n i, rfl⟩

/-- A substitution is successor-free exactly when its head and its arguments are. -/
theorem sbsFree_comp_iff {n m : ℕ} (h : SOf m) (g : Fin m → SOf n) :
    sbsFree (compOf h g).1.1 = true ↔ sbsFree h.1.1 = true ∧ ∀ i, sbsFree (g i).1.1 = true := by
  change (sbsFree h.1.1 && finAll m fun i ↦ sbsFree (g i).1.1) = true ↔ _
  rw [Bool.and_eq_true, finAll_eq_true_iff]

/-- A recursion is successor-free exactly when its bases and its steps are. -/
theorem sbsFree_srn_iff {a b : ℕ} (g : Fin b → SOf a) (h : Bool → Fin b → SOf (b + a + 1))
    (j : Fin b) :
    sbsFree (srnOf g h j).1.1 = true ↔
      (∀ l, sbsFree (g l).1.1 = true) ∧ ∀ i l, sbsFree (h i l).1.1 = true := by
  change (finAll b (fun l ↦ sbsFree (g l).1.1) &&
    (finAll b (fun l ↦ sbsFree (h false l).1.1) &&
      finAll b fun l ↦ sbsFree (h true l).1.1)) = true ↔ _
  rw [Bool.and_eq_true, Bool.and_eq_true, finAll_eq_true_iff, finAll_eq_true_iff,
    finAll_eq_true_iff]
  constructor
  · rintro ⟨hg, hf, ht⟩
    refine ⟨hg, fun i ↦ ?_⟩
    cases i
    · exact hf
    · exact ht
  · rintro ⟨hg, hh⟩
    exact ⟨hg, hh false, hh true⟩

/-- The substitution of {lit}`m` expressions of arity {lit}`n` into one of arity
{lit}`m`. -/
@[expose] def compL {n m : ℕ} (h : LOf m) (g : Fin m → LOf n) : LOf n :=
  ⟨compOf h.1 fun i ↦ (g i).1, (sbsFree_comp_iff _ _).mpr ⟨h.2, fun i ↦ (g i).2⟩⟩

/-- The {lit}`j`th of the {lit}`b` functions defined by simultaneous recursion on
notation from the bases {lit}`g` and the steps {lit}`h`, with {lit}`a`
parameters. -/
@[expose] def srnL {a b : ℕ} (g : Fin b → LOf a) (h : Bool → Fin b → LOf (b + a + 1))
    (j : Fin b) : LOf (a + 1) :=
  ⟨srnOf (fun l ↦ (g l).1) (fun i l ↦ (h i l).1) j,
    (sbsFree_srn_iff _ _ _).mpr ⟨fun l ↦ (g l).2, fun i l ↦ (h i l).2⟩⟩

end

end Geb.SizeBounded.Logspace
