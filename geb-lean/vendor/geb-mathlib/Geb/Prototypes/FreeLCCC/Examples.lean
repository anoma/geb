/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeLCCC.Category

set_option doc.verso true in
/-!
# Objects and equations in the syntactic category

Closed terms become objects and morphisms after supplying derivations of their definedness
and endpoints. The examples construct the terminal object, the natural numbers object, zero,
successor, and a dependent product along zero. Recursion with zero and successor is proved to
be the identity by the uniqueness rule for the NNO.

Proof certificates are ordinary rose trees. Each certificate used here is checked by kernel
reduction, so a malformed application of a rule cannot introduce an equation. These examples
also illustrate working directly with {name}`Geb.FreeLCCC.Derives`, before passing to classes
with {name}`Geb.FreeLCCC.ofTerm`.

## Main definitions

* {lit}`terminalObject`, {lit}`natObject` — closed objects.
* {lit}`zeroHom`, {lit}`succHom` — morphisms with categorical types.
* {lit}`productAlongZero` — dependent product of the natural numbers over the terminal object
  along zero, as a syntactic arrow over the natural numbers.

## Main statements

* {lit}`nat_id_rec` — recursion with zero and successor is the identity.

## Tags

syntactic category, natural numbers object, dependent product, proof certificate
-/

set_option doc.verso true

@[expose] public section

namespace Geb.FreeLCCC.Examples

open PartialHorn FreeTopos.Sorts CategoryTheory

/-- A certificate for a closed axiom of the natural numbers block. -/
private def natAx (k : ℕ) : Tree := Cert.ax (finiteAxioms.length + k) [] [] []

/-- A certificate that the natural numbers object is defined. -/
private def natDfd : Tree := Cert.trans (Cert.symm (natAx 1)) (natAx 1)

/-- A certificate that zero is defined. -/
private def zeroDfd : Tree := Cert.strict 0 (natAx 0)

/-- A certificate that successor is defined. -/
private def succDfd : Tree := Cert.strict 0 (natAx 2)

/-- The terminal object is a defined term. -/
theorem one_defined : Derives [] [] (dfd one) :=
  ⟨Cert.ax FreeTopos.categoryAxioms.length [] [] [], by decide⟩

/-- The natural numbers object is a defined term. -/
theorem nat_defined : Derives [] [] (dfd nat) := ⟨natDfd, by decide⟩

/-- Zero has domain the terminal object. -/
theorem dom_zeroN : Derives [] [] ⟨dom zeroN, one⟩ := ⟨natAx 0, by decide⟩

/-- Zero has codomain the natural numbers object. -/
theorem cod_zeroN : Derives [] [] ⟨cod zeroN, nat⟩ := ⟨natAx 1, by decide⟩

/-- Successor has domain the natural numbers object. -/
theorem dom_succ : Derives [] [] ⟨dom succ, nat⟩ := ⟨natAx 2, by decide⟩

/-- Successor has codomain the natural numbers object. -/
theorem cod_succ : Derives [] [] ⟨cod succ, nat⟩ := ⟨natAx 3, by decide⟩

/-- Zero is a defined term. -/
theorem zeroN_defined : Derives [] [] (dfd zeroN) := ⟨zeroDfd, by decide⟩

/-- Successor is a defined term. -/
theorem succ_defined : Derives [] [] (dfd succ) := ⟨succDfd, by decide⟩

/-- The terminal object as an object of the syntactic category. -/
def terminalObject : syntacticModel.Cat := objOfTerm one (by decide) one_defined

/-- The natural numbers object as an object of the syntactic category. -/
def natObject : syntacticModel.Cat := objOfTerm nat (by decide) nat_defined

/-- Zero as a categorical morphism. -/
def zeroHom : terminalObject ⟶ natObject :=
  homOfTerm (by decide) (by decide) (by decide) one_defined nat_defined zeroN_defined
    dom_zeroN cod_zeroN

/-- Successor as a categorical endomorphism. -/
def succHom : natObject ⟶ natObject :=
  homOfTerm (by decide) (by decide) (by decide) nat_defined nat_defined succ_defined
    dom_succ cod_succ

/-- The left identity law at an explicitly identified codomain. -/
private theorem left_id {f b : Tree} (hs : sortOf sig [] f = some arr)
    (hf : Derives [] [] (dfd f)) (hc : Derives [] [] ⟨cod f, b⟩) :
    Derives [] [] ⟨comp (idt b) f, f⟩ := by
  have law : Derives [] [] ⟨comp (idt (cod f)) f, f⟩ := by
    change Derivable theory #[] [] [] ((FreeTopos.categoryAxioms[11]'(by decide)).concl.subst
      [f])
    apply Derivable.ax (j := 11) rfl (by decide)
    · change [sortOf sig [] f] = [some arr]
      rw [hs]
    · intro t ht
      obtain rfl := List.mem_singleton.mp ht
      exact hf
    · simp [FreeTopos.categoryAxioms]
  have hi := Derivable.cong_of_forall₂ (.cons hc .nil) (law.strict (j := 0) rfl)
  exact (Derivable.cong_of_forall₂ (.cons hi (.cons hf .nil)) law.left).symm.trans law

/-- The right identity law at an explicitly identified domain. -/
private theorem right_id {f a : Tree} (hs : sortOf sig [] f = some arr)
    (hf : Derives [] [] (dfd f)) (hd : Derives [] [] ⟨dom f, a⟩) :
    Derives [] [] ⟨comp f (idt a), f⟩ := by
  have law : Derives [] [] ⟨comp f (idt (dom f)), f⟩ := by
    change Derivable theory #[] [] [] ((FreeTopos.categoryAxioms[10]'(by decide)).concl.subst
      [f])
    apply Derivable.ax (j := 10) rfl (by decide)
    · change [sortOf sig [] f] = [some arr]
      rw [hs]
    · intro t ht
      obtain rfl := List.mem_singleton.mp ht
      exact hf
    · simp [FreeTopos.categoryAxioms]
  have hi := Derivable.cong_of_forall₂ (.cons hd .nil) (law.strict (j := 1) rfl)
  exact (Derivable.cong_of_forall₂ (.cons hf (.cons hi .nil)) law.left).symm.trans law

/-- Recursion with zero and successor is defined. -/
theorem natRec_defined : Derives [] [] (dfd (natRec zeroN succ)) := by
  change Derivable theory #[] [] [] ((natAxioms[4]'(by decide)).concl.subst [zeroN, succ])
  apply Derivable.ax (j := finiteAxioms.length + 4) rfl (by decide) (by decide)
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact zeroN_defined
    · exact succ_defined
  · intro h hh
    change h ∈ [⟨dom (x 0), one⟩, ⟨cod (x 0), dom (x 1)⟩,
      ⟨dom (x 1), cod (x 1)⟩] at hh
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
    rcases hh with rfl | rfl | rfl
    · exact dom_zeroN
    · exact cod_zeroN.trans dom_succ.symm
    · exact dom_succ.trans cod_succ.symm

/-- Recursion with zero and successor is the identity, by uniqueness of NNO recursion. -/
theorem nat_id_rec : Derives [] [] ⟨idt nat, natRec zeroN succ⟩ := by
  have hz := left_id (by decide) zeroN_defined cod_zeroN
  have hs := left_id (by decide) succ_defined cod_succ
  have hs' := right_id (by decide) succ_defined dom_succ
  change Derivable theory #[] [] [] ((natAxioms[12]'(by decide)).concl.subst
    [zeroN, succ, idt nat])
  apply Derivable.ax (j := finiteAxioms.length + 12) rfl (by decide) (by decide)
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · exact zeroN_defined
    · exact succ_defined
    · exact ⟨Cert.ax 2 [nat] [natDfd] [], by decide⟩
  · intro h hh
    change h ∈ [dfd (natRec (x 0) (x 1)), ⟨dom (x 2), nat⟩,
      ⟨comp (x 2) zeroN, x 0⟩,
      ⟨comp (x 2) succ, comp (x 1) (x 2)⟩] at hh
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
    rcases hh with rfl | rfl | rfl | rfl
    · exact natRec_defined
    · exact ⟨Cert.ax 8 [nat] [natDfd] [], by decide⟩
    · exact hz
    · exact hs.trans hs'.symm

/-- The arrow representing a dependent product along zero. -/
def productAlongZero : Tree := pi zeroN (bang nat)

/-- The dependent product along zero is defined: {lit}`bang nat` lies over its domain. -/
theorem productAlongZero_defined : Derives [] [] (dfd productAlongZero) := by
  let bangDom := Cert.ax (FreeTopos.categoryAxioms.length + 1) [nat] [natDfd] []
  let bangCod := Cert.ax (FreeTopos.categoryAxioms.length + 2) [nat] [natDfd] []
  refine ⟨Cert.ax (finiteAxioms.length + natAxioms.length) [zeroN, bang nat]
    [zeroDfd, Cert.strict 0 bangDom] [Cert.trans bangCod (Cert.symm (natAx 0))], ?_⟩
  decide

/-- The dependent product along zero, as an arrow in the model's arrow sort. -/
def productAlongZeroArrow : syntacticModel.Ar :=
  ofTerm productAlongZero (by decide) productAlongZero_defined

end Geb.FreeLCCC.Examples

end
