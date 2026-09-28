/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Recursion

set_option doc.verso true in
/-!
# The coproducts and the initial object of a model of the theory

The binary coproducts and the initial object of a model of the theory of an elementary topos,
stated of the values of terms at an assignment, as {lit}`Geb.Prototypes.FreeTopos.Arrows` states the
cartesian closed structure: the typings of the injections, the copairing and the arrows from the
initial object, and the equations of their universal properties.

In a cartesian closed category the product with an object preserves coproducts, being a left
adjoint, so that an arrow from the product of {lit}`X` and a coproduct is determined by its
composites with the products of {lit}`X` and the injections ({lit}`prod_coprod_ext`), and any two
such composites are those of one arrow, the copairing in the context {lit}`X`
({lit}`copairIn`): the category is distributive (\[CarboniLackWalters1993\]). For the same
reason an object with an arrow to the initial object is initial ({lit}`eq_of_hom_zero`): the
initial object is strict, as it is in every distributive category
(\[CarboniLackWalters1993\], Proposition 3.4). The case analysis of a coproduct
is an arrow ({lit}`caseArr`), the transpose of the copairing, in the context of a pair of
functions, of their evaluations: an application of the case analysis of a pair of functions to
an injection of an argument is the application of the corresponding function to it.

## Main definitions

* {lit}`copairIn` — the copairing in the context of an object.
* {lit}`caseArr` — the case analysis of a coproduct, from the product of two exponentials.

## Main statements

* {lit}`inl_hom`, {lit}`inr_hom`, {lit}`copair_hom`, {lit}`absurd_hom` — the typings.
* {lit}`copair_inl`, {lit}`copair_inr`, {lit}`copair_eta`, {lit}`absurd_unique` — the universal
  properties of the coproduct and the initial object.
* {lit}`copairIn_inl`, {lit}`copairIn_inr`, {lit}`prod_coprod_ext` — the copairing in a context,
  and the uniqueness of an arrow from the product of an object and a coproduct.
* {lit}`caseArr_inl`, {lit}`caseArr_inr` — the computation of the case analysis.
* {lit}`eq_of_hom_zero` — an object with an arrow to the initial object is initial.

## References

* \[CarboniLackWalters1993\] for distributive categories and their strict initial objects.

## Tags

elementary topos, coproduct, initial object, distributive category, model
-/

set_option doc.verso true

@[expose] public section

namespace Geb.FreeTopos

open PartialHorn Sorts

universe v

/-- The copairing, in the context {lit}`X`, of {lit}`F` from the product of {lit}`X` and
{lit}`A` and {lit}`G` from the product of {lit}`X` and {lit}`B`, both to {lit}`C`: the arrow from
the product of {lit}`X` and the coproduct of {lit}`A` and {lit}`B` that is evaluation after the
pairing of the copairing of the transposes of the two arrows, into the exponential of {lit}`X`
and {lit}`C`, with the projection to {lit}`X`. -/
def copairIn (X A B C F G : Tree) : Tree :=
  comp (ev X C) (pair (comp (copair (curry A X (comp F (pair (snd A X) (fst A X))))
    (curry B X (comp G (pair (snd B X) (fst B X))))) (snd X (coprod A B))) (fst X (coprod A B)))

/-- The case analysis of the coproduct of {lit}`A` and {lit}`B` into {lit}`C`: the arrow from
the product of the exponentials of {lit}`A` and of {lit}`B` into {lit}`C` to the exponential of
their coproduct into {lit}`C` that is the transpose of the copairing, in the context of that
product, of the evaluations of its components. -/
def caseArr (A B C : Tree) : Tree :=
  curry (prod (exp A C) (exp B C)) (coprod A B) (copairIn (prod (exp A C) (exp B C)) A B C
    (comp (ev A C) (pair (comp (fst (exp A C) (exp B C)) (fst (prod (exp A C) (exp B C)) A))
      (snd (prod (exp A C) (exp B C)) A)))
    (comp (ev B C) (pair (comp (snd (exp A C) (exp B C)) (fst (prod (exp A C) (exp B C)) B))
      (snd (prod (exp A C) (exp B C)) B))))

variable {defs : List Defn} {M : Model.{v} (ext defs).sig} {ρ : List M.Val}
variable (hM : IsModel (ext defs) M)
include hM

section Objects

/-- The initial object. -/
theorem isObj_zero : IsObj M ρ zero := by
  obtain ⟨w, hw, -⟩ := ax_holds (ρ := ρ) hM 43 rfl (by decide) (ts := []) (ws := []) rfl rfl rfl
    trivial (q := ⟨zero, zero⟩) rfl
  exact ⟨w, hw, sort_of_eval_op rfl hw⟩

/-- The coproduct of two objects. -/
theorem isObj_coprod {A B : Tree} (hA : IsObj M ρ A) (hB : IsObj M ρ B) :
    IsObj M ρ (coprod A B) := by
  obtain ⟨a, ha, has⟩ := hA
  obtain ⟨b, hb, hbs⟩ := hB
  obtain ⟨w, hw, -⟩ := ax_holds (ρ := ρ) hM 47 rfl (by decide) (ts := [A, B]) (ws := [a, b])
    (by simp [ha, hb]) (by simp [has, hbs]) rfl trivial (q := ⟨coprod A B, coprod A B⟩) rfl
  exact ⟨w, hw, sort_of_eval_op rfl hw⟩

end Objects

section Typings

/-- The arrow from the initial object to an object. -/
theorem absurd_hom {C : Tree} (hC : IsObj M ρ C) : Hom M ρ (absurd C) zero C := by
  obtain ⟨c, hc, hcs⟩ := hC
  have hts : [C].map (eval M ρ) = [c].map Part.some := by simp [hc]
  have hs : [c].map Sigma.fst = [obj] := by simp [hcs]
  obtain ⟨z, hz, -⟩ := isObj_zero hM (ρ := ρ)
  have hd := eval_eq_of_holds (ax_holds hM 44 rfl (by decide) hts hs rfl trivial
    (q := ⟨dom (absurd C), zero⟩) rfl)
  obtain ⟨w, hw⟩ := exists_eval_of_dom (hd.trans hz)
  exact ⟨w, hw, sort_of_eval_op rfl hw, isObj_zero hM, ⟨c, hc, hcs⟩, hd,
    eval_eq_of_holds (ax_holds hM 45 rfl (by decide) hts hs rfl trivial
      (q := ⟨cod (absurd C), C⟩) rfl)⟩

/-- The left injection into a coproduct. -/
theorem inl_hom {A B : Tree} (hA : IsObj M ρ A) (hB : IsObj M ρ B) :
    Hom M ρ (inl A B) A (coprod A B) := by
  obtain ⟨a, ha, has⟩ := hA
  obtain ⟨b, hb, hbs⟩ := hB
  have hts : [A, B].map (eval M ρ) = [a, b].map Part.some := by simp [ha, hb]
  have hs : [a, b].map Sigma.fst = [obj, obj] := by simp [has, hbs]
  have hd := eval_eq_of_holds (ax_holds hM 48 rfl (by decide) hts hs rfl trivial
    (q := ⟨dom (inl A B), A⟩) rfl)
  obtain ⟨w, hw⟩ := exists_eval_of_dom (hd.trans ha)
  exact ⟨w, hw, sort_of_eval_op rfl hw, ⟨a, ha, has⟩,
    isObj_coprod hM ⟨a, ha, has⟩ ⟨b, hb, hbs⟩, hd,
    eval_eq_of_holds (ax_holds hM 49 rfl (by decide) hts hs rfl trivial
      (q := ⟨cod (inl A B), coprod A B⟩) rfl)⟩

/-- The right injection into a coproduct. -/
theorem inr_hom {A B : Tree} (hA : IsObj M ρ A) (hB : IsObj M ρ B) :
    Hom M ρ (inr A B) B (coprod A B) := by
  obtain ⟨a, ha, has⟩ := hA
  obtain ⟨b, hb, hbs⟩ := hB
  have hts : [A, B].map (eval M ρ) = [a, b].map Part.some := by simp [ha, hb]
  have hs : [a, b].map Sigma.fst = [obj, obj] := by simp [has, hbs]
  have hd := eval_eq_of_holds (ax_holds hM 50 rfl (by decide) hts hs rfl trivial
    (q := ⟨dom (inr A B), B⟩) rfl)
  obtain ⟨w, hw⟩ := exists_eval_of_dom (hd.trans hb)
  exact ⟨w, hw, sort_of_eval_op rfl hw, ⟨b, hb, hbs⟩,
    isObj_coprod hM ⟨a, ha, has⟩ ⟨b, hb, hbs⟩, hd,
    eval_eq_of_holds (ax_holds hM 51 rfl (by decide) hts hs rfl trivial
      (q := ⟨cod (inr A B), coprod A B⟩) rfl)⟩

/-- The copairing of two arrows of one codomain. -/
theorem copair_hom {f g A B C : Tree} (hf : Hom M ρ f A C) (hg : Hom M ρ g B C) :
    Hom M ρ (copair f g) (coprod A B) C := by
  obtain ⟨wf, hwf, hfs, hA, hC, hdf, hcf⟩ := hf
  obtain ⟨wg, hwg, hgs, hB, ⟨c, hc, -⟩, hdg, hcg⟩ := hg
  have hts : [f, g].map (eval M ρ) = [wf, wg].map Part.some := by simp [hwf, hwg]
  have hs : [wf, wg].map Sigma.fst = [arr, arr] := by simp [hfs, hgs]
  obtain ⟨w, hw, -⟩ := ax_holds hM 53 rfl (by decide) hts hs (hs' := [⟨cod f, cod g⟩]) rfl
    (holds_of_eval_eq (hcf.trans hcg.symm) (hcg.trans hc)) (q := ⟨copair f g, copair f g⟩) rfl
  have hd : Eqn.Holds M ρ ⟨copair f g, copair f g⟩ := ⟨w, hw, hw⟩
  refine ⟨w, hw, sort_of_eval_op rfl hw, isObj_coprod hM hA hB, hC, ?_, ?_⟩
  · exact (eval_eq_of_holds (ax_holds hM 54 rfl (by decide) hts hs
      (hs' := [⟨copair f g, copair f g⟩]) rfl hd
      (q := ⟨dom (copair f g), coprod (dom f) (dom g)⟩) rfl)).trans (eval_op₂_congr 15 hdf hdg)
  · exact (eval_eq_of_holds (ax_holds hM 55 rfl (by decide) hts hs
      (hs' := [⟨copair f g, copair f g⟩]) rfl hd (q := ⟨cod (copair f g), cod f⟩) rfl)).trans hcf

/-- The copairing in a context. -/
theorem copairIn_hom {F G X A B C : Tree} (hX : IsObj M ρ X) (hA : IsObj M ρ A)
    (hB : IsObj M ρ B) (hF : Hom M ρ F (prod X A) C) (hG : Hom M ρ G (prod X B) C) :
    Hom M ρ (copairIn X A B C F G) (prod X (coprod A B)) C := by
  have hC := hF.isObj_cod
  have hD := isObj_coprod hM hA hB
  have hΦ := copair_hom hM
    (curry_hom hM hA hX (comp_hom hM (pair_hom hM (snd_hom hM hA hX) (fst_hom hM hA hX)) hF))
    (curry_hom hM hB hX (comp_hom hM (pair_hom hM (snd_hom hM hB hX) (fst_hom hM hB hX)) hG))
  exact comp_hom hM (pair_hom hM (comp_hom hM (snd_hom hM hX hD) hΦ) (fst_hom hM hX hD))
    (ev_hom hM hX hC)

/-- The case analysis of a coproduct. -/
theorem caseArr_hom {A B C : Tree} (hA : IsObj M ρ A) (hB : IsObj M ρ B) (hC : IsObj M ρ C) :
    Hom M ρ (caseArr A B C) (prod (exp A C) (exp B C)) (exp (coprod A B) C) := by
  have hEA := isObj_exp hM hA hC
  have hEB := isObj_exp hM hB hC
  have hP := isObj_prod hM hEA hEB
  exact curry_hom hM hP (isObj_coprod hM hA hB) (copairIn_hom hM hP hA hB
    (comp_hom hM (pair_hom hM (comp_hom hM (fst_hom hM hP hA) (fst_hom hM hEA hEB))
      (snd_hom hM hP hA)) (ev_hom hM hA hC))
    (comp_hom hM (pair_hom hM (comp_hom hM (fst_hom hM hP hB) (snd_hom hM hEA hEB))
      (snd_hom hM hP hB)) (ev_hom hM hB hC)))

end Typings

section Equations

/-- The copairing after the left injection is the first arrow. -/
theorem copair_inl {f g A B C : Tree} (hf : Hom M ρ f A C) (hg : Hom M ρ g B C) :
    eval M ρ (comp (copair f g) (inl A B)) = eval M ρ f := by
  obtain ⟨wf, hwf, hfs⟩ := hf.exists_eval
  obtain ⟨wg, hwg, hgs⟩ := hg.exists_eval
  obtain ⟨w, hw, -⟩ := copair_hom hM hf hg
  refine (eval_op₂_congr 3 rfl (eval_op₂_congr 16 hf.eval_dom.symm hg.eval_dom.symm)).trans ?_
  exact eval_eq_of_holds (ax_holds hM 56 rfl (by decide) (ts := [f, g]) (ws := [wf, wg])
    (by simp [hwf, hwg]) (by simp [hfs, hgs]) (hs' := [⟨copair f g, copair f g⟩]) rfl ⟨w, hw, hw⟩
    (q := ⟨comp (copair f g) (inl (dom f) (dom g)), f⟩) rfl)

/-- The copairing after the right injection is the second arrow. -/
theorem copair_inr {f g A B C : Tree} (hf : Hom M ρ f A C) (hg : Hom M ρ g B C) :
    eval M ρ (comp (copair f g) (inr A B)) = eval M ρ g := by
  obtain ⟨wf, hwf, hfs⟩ := hf.exists_eval
  obtain ⟨wg, hwg, hgs⟩ := hg.exists_eval
  obtain ⟨w, hw, -⟩ := copair_hom hM hf hg
  refine (eval_op₂_congr 3 rfl (eval_op₂_congr 17 hf.eval_dom.symm hg.eval_dom.symm)).trans ?_
  exact eval_eq_of_holds (ax_holds hM 57 rfl (by decide) (ts := [f, g]) (ws := [wf, wg])
    (by simp [hwf, hwg]) (by simp [hfs, hgs]) (hs' := [⟨copair f g, copair f g⟩]) rfl ⟨w, hw, hw⟩
    (q := ⟨comp (copair f g) (inr (dom f) (dom g)), g⟩) rfl)

/-- An arrow from a coproduct is the copairing of its composites with the injections. -/
theorem copair_eta {h A B C : Tree} (hA : IsObj M ρ A) (hB : IsObj M ρ B)
    (hh : Hom M ρ h (coprod A B) C) :
    eval M ρ (copair (comp h (inl A B)) (comp h (inr A B))) = eval M ρ h := by
  obtain ⟨wh, hwh, hhs⟩ := hh.exists_eval
  obtain ⟨a, ha, has⟩ := hA
  obtain ⟨b, hb, hbs⟩ := hB
  obtain ⟨p, hp, -⟩ := hh.isObj_dom
  exact eval_eq_of_holds (ax_holds hM 58 rfl (by decide) (ts := [h, A, B]) (ws := [wh, a, b])
    (by simp [hwh, ha, hb]) (by simp [hhs, has, hbs]) (hs' := [⟨dom h, coprod A B⟩]) rfl
    (holds_of_eval_eq hh.eval_dom hp)
    (q := ⟨copair (comp h (inl A B)) (comp h (inr A B)), h⟩) rfl)

/-- An arrow from the initial object is the arrow from it to the arrow's codomain. -/
theorem absurd_unique {h C : Tree} (hh : Hom M ρ h zero C) :
    eval M ρ h = eval M ρ (absurd C) := by
  obtain ⟨wh, hwh, hhs⟩ := hh.exists_eval
  obtain ⟨z, hz, -⟩ := hh.isObj_dom
  exact (eval_eq_of_holds (ax_holds hM 46 rfl (by decide) (ts := [h]) (ws := [wh])
    (by simp [hwh]) (by simp [hhs]) (hs' := [⟨dom h, zero⟩]) rfl
    (holds_of_eval_eq hh.eval_dom hz) (q := ⟨h, absurd (cod h)⟩) rfl)).trans
    (eval_op₁_congr 14 hh.eval_cod)

/-- Evaluation after the pairing of a currying after an arrow with an arrow is the curried arrow
after the pairing of the two arrows. -/
theorem ev_pair_comp_curry {T k m Y Z A B : Tree} (hT : Hom M ρ T (prod Z A) B)
    (hk : Hom M ρ k Y Z) (hm : Hom M ρ m Y A) :
    eval M ρ (comp (ev A B) (pair (comp (curry Z A T) k) m)) = eval M ρ (comp T (pair k m)) := by
  have hZ := hk.isObj_cod
  have hA := hm.isObj_cod
  have hc := curry_hom hM hZ hA hT
  have hfZ := fst_hom hM hZ hA
  have hsZ := snd_hom hM hZ hA
  have hkm := pair_hom hM hk hm
  have hcf := comp_hom hM hfZ hc
  have e₁ : eval M ρ (pair (comp (curry Z A T) k) m) = eval M ρ
      (comp (pair (comp (curry Z A T) (fst Z A)) (snd Z A)) (pair k m)) :=
    ((pair_comp hM hcf hsZ hkm).trans (eval_op₂_congr 9
      ((comp_assoc hM hkm hfZ hc).symm.trans (eval_op₂_congr 3 rfl (fst_pair hM hk hm)))
      (snd_pair hM hk hm))).symm
  exact (eval_op₂_congr 3 rfl e₁).trans ((comp_assoc hM hkm (pair_hom hM hcf hsZ)
    (ev_hom hM hA hT.isObj_cod)).trans (eval_op₂_congr 3 (ev_curry hM hZ hA hT) rfl))

/-- Two arrows from the product of an object and a coproduct are equal when their composites
with the products of the object and the injections are. -/
theorem prod_coprod_ext {k k' X A B C : Tree} (hX : IsObj M ρ X) (hA : IsObj M ρ A)
    (hB : IsObj M ρ B) (hk : Hom M ρ k (prod X (coprod A B)) C)
    (hk' : Hom M ρ k' (prod X (coprod A B)) C)
    (hl : eval M ρ (comp k (pair (fst X A) (comp (inl A B) (snd X A)))) =
      eval M ρ (comp k' (pair (fst X A) (comp (inl A B) (snd X A)))))
    (hr : eval M ρ (comp k (pair (fst X B) (comp (inr A B) (snd X B)))) =
      eval M ρ (comp k' (pair (fst X B) (comp (inr A B) (snd X B))))) :
    eval M ρ k = eval M ρ k' := by
  have hD := isObj_coprod hM hA hB
  have hil := inl_hom hM hA hB
  have hir := inr_hom hM hA hB
  have ht : ∀ {k}, Hom M ρ k (prod X (coprod A B)) C → Hom M ρ
      (curry (coprod A B) X (comp k (pair (snd (coprod A B) X) (fst (coprod A B) X))))
      (coprod A B) (exp X C) := fun hk ↦ curry_hom hM hD hX
    (comp_hom hM (pair_hom hM (snd_hom hM hD hX) (fst_hom hM hD hX)) hk)
  -- an arrow after the product with an arrow into the coproduct, its factors exchanged, is the
  -- arrow after the product, after the exchange
  have hre : ∀ {k i E}, Hom M ρ k (prod X (coprod A B)) C → Hom M ρ i E (coprod A B) →
      eval M ρ (comp k (pair (snd E X) (comp i (fst E X)))) =
        eval M ρ (comp (comp k (pair (fst X E) (comp i (snd X E)))) (pair (snd E X) (fst E X))) :=
    fun {k i E} hk hi ↦ by
      have hE := hi.isObj_dom
      have hsE := snd_hom hM hE hX
      have hfE := fst_hom hM hE hX
      have hsX := snd_hom hM hX hE
      have hfX := fst_hom hM hX hE
      have his := comp_hom hM hsX hi
      have hsw := pair_hom hM hsE hfE
      exact Eq.symm ((comp_assoc hM hsw (pair_hom hM hfX his) hk).symm.trans
        (eval_op₂_congr 3 rfl ((pair_comp hM hfX his hsw).trans (eval_op₂_congr 9
          (fst_pair hM hsE hfE) ((comp_assoc hM hsw hsX hi).symm.trans
            (eval_op₂_congr 3 rfl (snd_pair hM hsE hfE)))))))
  -- the transposes are equal, having equal composites with the injections
  refine eq_of_curry_swap hM hX hD hk hk' ((copair_eta hM hA hB (ht hk)).symm.trans
    (Eq.trans (eval_op₂_congr 18 ?_ ?_) (copair_eta hM hA hB (ht hk'))))
  · exact (curry_swap_comp hM hX hk hil).trans ((eval_op₃_congr 24 rfl rfl ((hre hk hil).trans
      ((eval_op₂_congr 3 hl rfl).trans (hre hk' hil).symm))).trans
      (curry_swap_comp hM hX hk' hil).symm)
  · exact (curry_swap_comp hM hX hk hir).trans ((eval_op₃_congr 24 rfl rfl ((hre hk hir).trans
      ((eval_op₂_congr 3 hr rfl).trans (hre hk' hir).symm))).trans
      (curry_swap_comp hM hX hk' hir).symm)

/-- The copairing in a context after the pairing of an arrow with the left injection after an
arrow is the first arrow after the pairing of the two arrows. -/
theorem copairIn_inl {F G X A B C u v Y : Tree} (hB : IsObj M ρ B)
    (hF : Hom M ρ F (prod X A) C) (hG : Hom M ρ G (prod X B) C) (hu : Hom M ρ u Y X)
    (hv : Hom M ρ v Y A) :
    eval M ρ (comp (copairIn X A B C F G) (pair u (comp (inl A B) v))) =
      eval M ρ (comp F (pair u v)) := by
  have hX := hu.isObj_cod
  have hA := hv.isObj_cod
  have hD := isObj_coprod hM hA hB
  have hwA := pair_hom hM (snd_hom hM hA hX) (fst_hom hM hA hX)
  have hwB := pair_hom hM (snd_hom hM hB hX) (fst_hom hM hB hX)
  have hsl := comp_hom hM hwA hF
  have hcl := curry_hom hM hA hX hsl
  have hcr := curry_hom hM hB hX (comp_hom hM hwB hG)
  have hΦ := copair_hom hM hcl hcr
  have hil := comp_hom hM hv (inl_hom hM hA hB)
  have hp := pair_hom hM hu hil
  have hsD := snd_hom hM hX hD
  have hfD := fst_hom hM hX hD
  have hΦs := comp_hom hM hsD hΦ
  have e₁ : eval M ρ (comp (comp (copair (curry A X (comp F (pair (snd A X) (fst A X))))
      (curry B X (comp G (pair (snd B X) (fst B X))))) (snd X (coprod A B)))
      (pair u (comp (inl A B) v))) =
      eval M ρ (comp (curry A X (comp F (pair (snd A X) (fst A X)))) v) :=
    ((comp_assoc hM hp hsD hΦ).symm.trans (eval_op₂_congr 3 rfl (snd_pair hM hu hil))).trans
      ((comp_assoc hM hv (inl_hom hM hA hB) hΦ).trans
        (eval_op₂_congr 3 (copair_inl hM hcl hcr) rfl))
  refine (comp_assoc hM hp (pair_hom hM hΦs hfD) (ev_hom hM hX hF.isObj_cod)).symm.trans ?_
  refine (eval_op₂_congr 3 rfl ((pair_comp hM hΦs hfD hp).trans
    (eval_op₂_congr 9 e₁ (fst_pair hM hu hil)))).trans ?_
  exact (ev_pair_comp_curry hM hsl hv hu).trans ((comp_assoc hM (pair_hom hM hv hu) hwA
    hF).symm.trans (eval_op₂_congr 3 rfl (swap_pair hM hv hu)))

/-- The copairing in a context after the pairing of an arrow with the right injection after an
arrow is the second arrow after the pairing of the two arrows. -/
theorem copairIn_inr {F G X A B C u v Y : Tree} (hA : IsObj M ρ A)
    (hF : Hom M ρ F (prod X A) C) (hG : Hom M ρ G (prod X B) C) (hu : Hom M ρ u Y X)
    (hv : Hom M ρ v Y B) :
    eval M ρ (comp (copairIn X A B C F G) (pair u (comp (inr A B) v))) =
      eval M ρ (comp G (pair u v)) := by
  have hX := hu.isObj_cod
  have hB := hv.isObj_cod
  have hD := isObj_coprod hM hA hB
  have hwA := pair_hom hM (snd_hom hM hA hX) (fst_hom hM hA hX)
  have hwB := pair_hom hM (snd_hom hM hB hX) (fst_hom hM hB hX)
  have hsr := comp_hom hM hwB hG
  have hcl := curry_hom hM hA hX (comp_hom hM hwA hF)
  have hcr := curry_hom hM hB hX hsr
  have hΦ := copair_hom hM hcl hcr
  have hir := comp_hom hM hv (inr_hom hM hA hB)
  have hp := pair_hom hM hu hir
  have hsD := snd_hom hM hX hD
  have hfD := fst_hom hM hX hD
  have hΦs := comp_hom hM hsD hΦ
  have e₁ : eval M ρ (comp (comp (copair (curry A X (comp F (pair (snd A X) (fst A X))))
      (curry B X (comp G (pair (snd B X) (fst B X))))) (snd X (coprod A B)))
      (pair u (comp (inr A B) v))) =
      eval M ρ (comp (curry B X (comp G (pair (snd B X) (fst B X)))) v) :=
    ((comp_assoc hM hp hsD hΦ).symm.trans (eval_op₂_congr 3 rfl (snd_pair hM hu hir))).trans
      ((comp_assoc hM hv (inr_hom hM hA hB) hΦ).trans
        (eval_op₂_congr 3 (copair_inr hM hcl hcr) rfl))
  refine (comp_assoc hM hp (pair_hom hM hΦs hfD) (ev_hom hM hX hF.isObj_cod)).symm.trans ?_
  refine (eval_op₂_congr 3 rfl ((pair_comp hM hΦs hfD hp).trans
    (eval_op₂_congr 9 e₁ (fst_pair hM hu hir)))).trans ?_
  exact (ev_pair_comp_curry hM hsr hv hu).trans ((comp_assoc hM (pair_hom hM hv hu) hwB
    hG).symm.trans (eval_op₂_congr 3 rfl (swap_pair hM hv hu)))

/-- Evaluation after the pairing of the case analysis after a pair of functions with the left
injection after an argument is evaluation after the pairing of the first function with the
argument. -/
theorem caseArr_inl {p u Y A B C : Tree} (hB : IsObj M ρ B) (hC : IsObj M ρ C)
    (hp : Hom M ρ p Y (prod (exp A C) (exp B C))) (hu : Hom M ρ u Y A) :
    eval M ρ (comp (ev (coprod A B) C) (pair (comp (caseArr A B C) p) (comp (inl A B) u))) =
      eval M ρ (comp (ev A C) (pair (comp (fst (exp A C) (exp B C)) p) u)) := by
  have hA := hu.isObj_cod
  have hEA := isObj_exp hM hA hC
  have hEB := isObj_exp hM hB hC
  have hP := isObj_prod hM hEA hEB
  have hfP := fst_hom hM hP hA
  have hsP := snd_hom hM hP hA
  have hfE := comp_hom hM hfP (fst_hom hM hEA hEB)
  have hφ := comp_hom hM (pair_hom hM hfE hsP) (ev_hom hM hA hC)
  have hψ := comp_hom hM (pair_hom hM (comp_hom hM (fst_hom hM hP hB) (snd_hom hM hEA hEB))
    (snd_hom hM hP hB)) (ev_hom hM hB hC)
  refine (ev_pair_comp_curry hM (copairIn_hom hM hP hA hB hφ hψ) hp
    (comp_hom hM hu (inl_hom hM hA hB))).trans ((copairIn_inl hM hB hφ hψ hp hu).trans ?_)
  have hpu := pair_hom hM hp hu
  refine (comp_assoc hM hpu (pair_hom hM hfE hsP) (ev_hom hM hA hC)).symm.trans
    (eval_op₂_congr 3 rfl ((pair_comp hM hfE hsP hpu).trans (eval_op₂_congr 9 ?_
      (snd_pair hM hp hu))))
  exact (comp_assoc hM hpu hfP (fst_hom hM hEA hEB)).symm.trans
    (eval_op₂_congr 3 rfl (fst_pair hM hp hu))

/-- Evaluation after the pairing of the case analysis after a pair of functions with the right
injection after an argument is evaluation after the pairing of the second function with the
argument. -/
theorem caseArr_inr {p u Y A B C : Tree} (hA : IsObj M ρ A) (hC : IsObj M ρ C)
    (hp : Hom M ρ p Y (prod (exp A C) (exp B C))) (hu : Hom M ρ u Y B) :
    eval M ρ (comp (ev (coprod A B) C) (pair (comp (caseArr A B C) p) (comp (inr A B) u))) =
      eval M ρ (comp (ev B C) (pair (comp (snd (exp A C) (exp B C)) p) u)) := by
  have hB := hu.isObj_cod
  have hEA := isObj_exp hM hA hC
  have hEB := isObj_exp hM hB hC
  have hP := isObj_prod hM hEA hEB
  have hfP := fst_hom hM hP hB
  have hsP := snd_hom hM hP hB
  have hsE := comp_hom hM hfP (snd_hom hM hEA hEB)
  have hφ := comp_hom hM (pair_hom hM (comp_hom hM (fst_hom hM hP hA) (fst_hom hM hEA hEB))
    (snd_hom hM hP hA)) (ev_hom hM hA hC)
  have hψ := comp_hom hM (pair_hom hM hsE hsP) (ev_hom hM hB hC)
  refine (ev_pair_comp_curry hM (copairIn_hom hM hP hA hB hφ hψ) hp
    (comp_hom hM hu (inr_hom hM hA hB))).trans ((copairIn_inr hM hA hφ hψ hp hu).trans ?_)
  have hpu := pair_hom hM hp hu
  refine (comp_assoc hM hpu (pair_hom hM hsE hsP) (ev_hom hM hB hC)).symm.trans
    (eval_op₂_congr 3 rfl ((pair_comp hM hsE hsP hpu).trans (eval_op₂_congr 9 ?_
      (snd_pair hM hp hu))))
  exact (comp_assoc hM hpu hfP (snd_hom hM hEA hEB)).symm.trans
    (eval_op₂_congr 3 rfl (fst_pair hM hp hu))

/-- Two arrows of one domain, which has an arrow to the initial object, are equal: the initial
object is strict. -/
theorem eq_of_hom_zero {z f g X C : Tree} (hz : Hom M ρ z X zero) (hf : Hom M ρ f X C)
    (hg : Hom M ρ g X C) : eval M ρ f = eval M ρ g := by
  have hX := hz.isObj_dom
  have h0 := isObj_zero hM (ρ := ρ)
  have hs := snd_hom hM h0 hX
  have hf0 := fst_hom hM h0 hX
  -- an arrow from the product of the initial object and the domain is determined
  have hdet : ∀ {k}, Hom M ρ k (prod zero X) C → eval M ρ k =
      eval M ρ (comp (ev X C) (pair (comp (absurd (exp X C)) (fst zero X)) (snd zero X))) :=
    fun hk ↦ (ev_curry hM h0 hX hk).symm.trans (eval_op₂_congr 3 rfl (eval_op₂_congr 9
      (eval_op₂_congr 3 (absurd_unique hM (curry_hom hM h0 hX hk)) rfl) rfl))
  have hi := idt_hom hM hX
  have hp := pair_hom hM hz hi
  have hback : ∀ {k}, Hom M ρ k X C →
      eval M ρ k = eval M ρ (comp (comp k (snd zero X)) (pair z (idt X))) :=
    fun hk ↦ (comp_idt hM hk).symm.trans ((eval_op₂_congr 3 rfl (snd_pair hM hz hi).symm).trans
      (comp_assoc hM hp hs hk))
  exact (hback hf).trans ((eval_op₂_congr 3 ((hdet (comp_hom hM hs hf)).trans
    (hdet (comp_hom hM hs hg)).symm) rfl).trans (hback hg).symm)

end Equations

end Geb.FreeTopos

end
