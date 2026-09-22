/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.Data.PFunctor.Presheaf.Decidable

set_option doc.verso true in
/-!
# Local tests for presheaf W-tree recognition

Hereditary naturality can be checked by visiting the nodes of the input tree.
Each visit compares a child with a root-restricted child. Such a comparison
requires only the restricted root shape and equalities between original input
subtrees: it does not require constructing the restricted tree.

The results here isolate this mathematical reduction from any encoding or
complexity bound. The list of occurrences specifies which tests a positional
scanner must perform; constructing this list is not proposed as a logspace
implementation. An implementation on words can revisit subtree spans instead.

## Main definitions

* {lit}`occurrences` lists all nodes as rooted subtrees, retaining duplicates.
* {lit}`localNaturality` is the native checker's test at one node.
* {lit}`restrictedEq` compares a root restriction through original subtrees.

## Main statements

* {lit}`native_eq_scan` expresses the native checker as a conjunction of local tests.
* {lit}`restrictedEq_eq_true_iff` proves the root comparison correct.
* {lit}`positions_eq_native` transfers a correct node-position test to the native checker.

## Tags

presheaf, W-type, recognizer, hereditary naturality, subtree
-/

set_option doc.verso true

@[expose] public section

open CategoryTheory

universe uA uB uI vI

namespace Geb.PresheafRecognition

/-- All occurrences of rooted subtrees, with multiplicity, in preorder. -/
def occurrences {A : Type uA} {B : A → Type uB} (feB : ∀ a, FinEnum (B a)) :
    WType B → List (WType B) :=
  WType.para (List (WType B)) fun x ↦
    WType.mk x.1 (fun b ↦ (x.2 b).1) ::
      (feB x.1).toList.flatMap fun b ↦ (x.2 b).2

/-- Scanning the occurrences has the same value as conjoining each node's test
with the children's accumulated verdicts. -/
theorem all_occurrences {A : Type uA} {B : A → Type uB} (feB : ∀ a, FinEnum (B a))
    (test : WType B → Bool) (w : WType B) :
    (occurrences feB w).all test =
      WType.para Bool (fun x ↦ test (WType.mk x.1 fun b ↦ (x.2 b).1) &&
        (feB x.1).toList.all fun b ↦ (x.2 b).2) w := by
  refine WType.rec (motive := fun w ↦ (occurrences feB w).all test = _) ?_ w
  intro a f ih
  simp only [occurrences, WType.para_mk, List.all_cons, List.all_flatMap]
  congr 1
  exact congrArg (List.all (feB a).toList) (funext ih)

variable {I : Type uI} [Category.{vI} I]
  (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I)

/-- The test at one raw node in the native hereditary-naturality checker. -/
def localNaturality (decI : DecidableEq I) (feI : FinEnum I)
    (feHom : ∀ i i' : I, FinEnum (i' ⟶ i)) (feB : ∀ a, FinEnum (F.toPFunctor.B a))
    (decEqW : DecidableEq (WType F.toPFunctor.B)) : WType F.toPFunctor.B → Bool
  | WType.mk a f =>
      feI.toList.all fun i ↦ feI.toList.all fun i' ↦
        (feHom i i').toList.all fun g ↦ (feB a).toList.all fun b ↦
          match decI (F.rCurried a b) i with
          | isFalse _ => true
          | isTrue hb =>
              match decI (F.q (PFunctor.W.head (f b))) i with
              | isFalse _ => true
              | isTrue hq =>
                  (decEqW (f (F.directionRestr a g ⟨b, hb⟩).1)
                    (F.wRestrTreeRaw g (f b) hq)).decide

/-- The native checker is precisely the scan of its local tests, on all raw trees. -/
theorem native_eq_scan (decI : DecidableEq I) (feI : FinEnum I)
    (feHom : ∀ i i' : I, FinEnum (i' ⟶ i)) (feB : ∀ a, FinEnum (F.toPFunctor.B a))
    (decEqW : DecidableEq (WType F.toPFunctor.B)) (w : WType F.toPFunctor.B) :
    F.isHereditarilyNaturalBoolCore decI feI feHom feB decEqW w =
      (occurrences feB w).all (localNaturality F decI feI feHom feB decEqW) := by
  rw [all_occurrences]
  unfold PresheafPFunctor.isHereditarilyNaturalBoolCore
  congr 1
  funext x
  obtain ⟨a, f⟩ := x
  simp only [localNaturality]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, List.all_eq_true, FinEnum.mem_toList, forall_const]
  congr! 5
  rename_i i i' g b
  cases decI (F.rCurried a b) i with
  | isFalse h => rfl
  | isTrue h =>
    cases decI (F.q (PFunctor.W.head (f b).1)) i <;> simp only [decide_eq_true_iff]

/-- The positional specification agrees with hereditary naturality on slice-valid trees. -/
theorem scan_eq_true_iff (decI : DecidableEq I) (feI : FinEnum I)
    (feHom : ∀ i i' : I, FinEnum (i' ⟶ i)) (feB : ∀ a, FinEnum (F.toPFunctor.B a))
    (decEqW : DecidableEq (WType F.toPFunctor.B)) (z : F.toSlicePFunctor.W) :
    (occurrences feB z.1).all (localNaturality F decI feI feHom feB decEqW) = true ↔
      F.IsHereditarilyNatural z := by
  exact (congrArg (fun b ↦ b = true)
    (native_eq_scan F decI feI feHom feB decEqW z.1).symm).to_iff.trans
      (F.isHereditarilyNaturalBoolCore_eq_true_iff decI feI feHom feB decEqW z)

/-- A suffix scan agrees with the native checker when positions enumerate all input
nodes and the supplied test checks local naturality, accepting non-node positions. -/
theorem positions_eq_native (decI : DecidableEq I) (feI : FinEnum I)
    (feHom : ∀ i i' : I, FinEnum (i' ⟶ i)) (feB : ∀ a, FinEnum (F.toPFunctor.B a))
    (decEqW : DecidableEq (WType F.toPFunctor.B)) (w : List Bool)
    (tree : WType F.toPFunctor.B) (nodeAt : List Bool → Option (WType F.toPFunctor.B))
    (sound : ∀ v ∈ w.tails, ∀ t, nodeAt v = some t → t ∈ occurrences feB tree)
    (complete : ∀ t ∈ occurrences feB tree, ∃ v ∈ w.tails, nodeAt v = some t)
    (test : List Bool → Bool)
    (hlocal : ∀ v ∈ w.tails, test v =
      (nodeAt v).all (localNaturality F decI feI feHom feB decEqW)) :
    w.tails.all test = F.isHereditarilyNaturalBoolCore decI feI feHom feB decEqW tree := by
  rw [native_eq_scan]
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true]
  constructor
  · intro h t ht
    obtain ⟨v, hv, hnode⟩ := complete t ht
    have hvtest := h v hv
    rw [hlocal v hv, hnode] at hvtest
    exact hvtest
  · intro h v hv
    rw [hlocal v hv]
    cases hnode : nodeAt v with
    | none => rfl
    | some t => exact h t (sound v hv t hnode)

/-- Compare the restricted root shape, then compare only original subtrees.
The supplied equality test can operate on their codes or their input spans. -/
def restrictedEq (decA : DecidableEq F.A) (feB : ∀ a, FinEnum (F.toPFunctor.B a))
    (eq : WType F.toPFunctor.B → WType F.toPFunctor.B → Bool) ⦃j j' : I⦄ (g : j' ⟶ j)
    (t u : WType F.toPFunctor.B) (hq : F.q (PFunctor.W.head u) = j) : Bool :=
  match t, u, hq with
  | WType.mk a f, WType.mk a' f', hq =>
      match decA a (F.shapeRestr g ⟨a', hq⟩).1 with
      | isFalse _ => false
      | isTrue h =>
          (feB a).toList.all fun b ↦
            eq (f b) (f' (F.reindex g ⟨a', hq⟩
              (i := F.rCurried (F.shapeRestr g ⟨a', hq⟩).1 (h ▸ b)) ⟨h ▸ b, rfl⟩).1)

/-- The root comparison tests exactly equality with the root-restricted tree. -/
theorem restrictedEq_eq_true_iff (decA : DecidableEq F.A)
    (feB : ∀ a, FinEnum (F.toPFunctor.B a))
    (eq : WType F.toPFunctor.B → WType F.toPFunctor.B → Bool)
    (heq : ∀ t u, eq t u = true ↔ t = u) ⦃j j' : I⦄ (g : j' ⟶ j)
    (t u : WType F.toPFunctor.B) (hq : F.q (PFunctor.W.head u) = j) :
    restrictedEq F decA feB eq g t u hq = true ↔ t = F.wRestrTreeRaw g u hq := by
  cases t with | mk a f =>
    cases u with | mk a' f' =>
      simp only [restrictedEq, PresheafPFunctor.wRestrTreeRaw]
      split
      · rename_i h _
        exact ⟨fun hfalse ↦ Bool.noConfusion hfalse,
          fun htree ↦ (h (WType.mk.inj htree).1).elim⟩
      · rename_i h
        subst a
        simp only [List.all_eq_true, FinEnum.mem_toList, forall_const, heq]
        exact ⟨fun hchildren ↦ congrArg (WType.mk _) (funext hchildren),
          fun htree b ↦ congrFun (eq_of_heq (WType.mk.inj htree).2) b⟩

end Geb.PresheafRecognition
