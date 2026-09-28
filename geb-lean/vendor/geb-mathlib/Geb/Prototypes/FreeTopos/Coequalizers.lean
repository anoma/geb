/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Recursion

set_option doc.verso true in
/-!
# The coequalizers of a model of the theory

The coequalizers of a model of the theory of an elementary topos, stated of the values of terms
at an assignment, as {lit}`Geb.Prototypes.FreeTopos.Arrows` states the cartesian closed
structure: the typings of the coequalizer of two parallel arrows, of its projection and of the
descent of an arrow that coequalizes them, and the equations of the universal property.

The projection is an epimorphism: two arrows from the coequalizer with equal composites with it
are the descents of one arrow ({lit}`coeqProj_epi`). In a cartesian closed category the product
with an object preserves coequalizers, being a left adjoint, so that two arrows from the product
of an object and a coequalizer are equal when their composites with the product of the object
and the projection are ({lit}`prod_coeq_ext`): their transposes have equal composites with the
projection.

## Main statements

* {lit}`isObj_coeqz`, {lit}`coeqProj_hom`, {lit}`coeqDesc_hom` — the typings.
* {lit}`coeqProj_comp`, {lit}`coeqDesc_proj`, {lit}`coeqDesc_unique` — the universal property.
* {lit}`coeqProj_epi`, {lit}`prod_coeq_ext` — the projection is an epimorphism, and so is its
  product with an object.
* {lit}`coeqProj_parallel` — an arrow that is the projection of the coequalizer of two composites
  coequalizes two parallel arrows into the coequalizer.

## Tags

elementary topos, coequalizer, epimorphism, model
-/

set_option doc.verso true

@[expose] public section

namespace Geb.FreeTopos

open PartialHorn Sorts

universe v

variable {defs : List Defn} {M : Model.{v} (ext defs).sig} {ρ : List M.Val}
variable (hM : IsModel (ext defs) M)
include hM

section Coequalizers

variable {f g A B : Tree} (hf : Hom M ρ f A B) (hg : Hom M ρ g A B)
include hf hg

/-- The coequalizer of two parallel arrows is an object. -/
theorem isObj_coeqz : IsObj M ρ (coeqz f g) := by
  obtain ⟨wf, hwf, hfs⟩ := hf.exists_eval
  obtain ⟨wg, hwg, hgs⟩ := hg.exists_eval
  obtain ⟨a, ha, -⟩ := hf.isObj_dom
  obtain ⟨b, hb, -⟩ := hf.isObj_cod
  have hts : [f, g].map (eval M ρ) = [wf, wg].map Part.some := by simp [hwf, hwg]
  have hs : [wf, wg].map Sigma.fst = [arr, arr] := by simp [hfs, hgs]
  obtain ⟨w, hw, -⟩ := ax_holds hM 61 rfl (by decide) hts hs
    (hs' := [⟨dom f, dom g⟩, ⟨cod f, cod g⟩]) rfl
    ⟨holds_of_eval_eq (hf.eval_dom.trans hg.eval_dom.symm) (hg.eval_dom.trans ha),
      holds_of_eval_eq (hf.eval_cod.trans hg.eval_cod.symm) (hg.eval_cod.trans hb)⟩
    (q := ⟨coeqz f g, coeqz f g⟩) rfl
  exact ⟨w, hw, sort_of_eval_op rfl hw⟩

/-- The projection to the coequalizer of two parallel arrows. -/
theorem coeqProj_hom : Hom M ρ (coeqProj f g) B (coeqz f g) := by
  obtain ⟨wf, hwf, hfs⟩ := hf.exists_eval
  obtain ⟨wg, hwg, hgs⟩ := hg.exists_eval
  have hts : [f, g].map (eval M ρ) = [wf, wg].map Part.some := by simp [hwf, hwg]
  have hs : [wf, wg].map Sigma.fst = [arr, arr] := by simp [hfs, hgs]
  obtain ⟨q, hq, hqs⟩ := isObj_coeqz hM hf hg
  have hQ : Eqn.Holds M ρ ⟨coeqz f g, coeqz f g⟩ := ⟨q, hq, hq⟩
  obtain ⟨w, hw, -⟩ := ax_holds hM 63 rfl (by decide) hts hs
    (hs' := [⟨coeqz f g, coeqz f g⟩]) rfl hQ (q := ⟨coeqProj f g, coeqProj f g⟩) rfl
  exact ⟨w, hw, sort_of_eval_op rfl hw, hf.isObj_cod, ⟨q, hq, hqs⟩,
    (eval_eq_of_holds (ax_holds hM 64 rfl (by decide) hts hs
      (hs' := [⟨coeqz f g, coeqz f g⟩]) rfl hQ (q := ⟨dom (coeqProj f g), cod f⟩) rfl)).trans
      hf.eval_cod,
    eval_eq_of_holds (ax_holds hM 65 rfl (by decide) hts hs
      (hs' := [⟨coeqz f g, coeqz f g⟩]) rfl hQ (q := ⟨cod (coeqProj f g), coeqz f g⟩) rfl)⟩

/-- The projection to the coequalizer coequalizes the two arrows. -/
theorem coeqProj_comp :
    eval M ρ (comp (coeqProj f g) f) = eval M ρ (comp (coeqProj f g) g) := by
  obtain ⟨wf, hwf, hfs⟩ := hf.exists_eval
  obtain ⟨wg, hwg, hgs⟩ := hg.exists_eval
  have hts : [f, g].map (eval M ρ) = [wf, wg].map Part.some := by simp [hwf, hwg]
  have hs : [wf, wg].map Sigma.fst = [arr, arr] := by simp [hfs, hgs]
  obtain ⟨q, hq, -⟩ := isObj_coeqz hM hf hg
  exact eval_eq_of_holds (ax_holds hM 66 rfl (by decide) hts hs
    (hs' := [⟨coeqz f g, coeqz f g⟩]) rfl ⟨q, hq, hq⟩
    (q := ⟨comp (coeqProj f g) f, comp (coeqProj f g) g⟩) rfl)

/-- The descent of an arrow that coequalizes the two arrows is an arrow from their
coequalizer. -/
theorem coeqDesc_hom {h C : Tree} (hh : Hom M ρ h B C)
    (heq : eval M ρ (comp h f) = eval M ρ (comp h g)) :
    Hom M ρ (coeqDesc f g h) (coeqz f g) C := by
  obtain ⟨wf, hwf, hfs⟩ := hf.exists_eval
  obtain ⟨wg, hwg, hgs⟩ := hg.exists_eval
  obtain ⟨wh, hwh, hhs⟩ := hh.exists_eval
  have hts : [f, g, h].map (eval M ρ) = [wf, wg, wh].map Part.some := by simp [hwf, hwg, hwh]
  have hs : [wf, wg, wh].map Sigma.fst = [arr, arr, arr] := by simp [hfs, hgs, hhs]
  obtain ⟨q, hq, hqs⟩ := isObj_coeqz hM hf hg
  obtain ⟨v, hv, -⟩ := (comp_hom hM hf hh).exists_eval
  obtain ⟨w, hw, -⟩ := ax_holds hM 69 rfl (by decide) hts hs
    (hs' := [⟨coeqz f g, coeqz f g⟩, ⟨comp h f, comp h g⟩]) rfl
    ⟨⟨q, hq, hq⟩, holds_of_eval_eq heq (heq.symm.trans hv)⟩
    (q := ⟨coeqDesc f g h, coeqDesc f g h⟩) rfl
  have hD : Eqn.Holds M ρ ⟨coeqDesc f g h, coeqDesc f g h⟩ := ⟨w, hw, hw⟩
  exact ⟨w, hw, sort_of_eval_op rfl hw, ⟨q, hq, hqs⟩, hh.isObj_cod,
    eval_eq_of_holds (ax_holds hM 70 rfl (by decide) hts hs
      (hs' := [⟨coeqDesc f g h, coeqDesc f g h⟩]) rfl hD
      (q := ⟨dom (coeqDesc f g h), coeqz f g⟩) rfl),
    (eval_eq_of_holds (ax_holds hM 71 rfl (by decide) hts hs
      (hs' := [⟨coeqDesc f g h, coeqDesc f g h⟩]) rfl hD
      (q := ⟨cod (coeqDesc f g h), cod h⟩) rfl)).trans hh.eval_cod⟩

/-- The descent of an arrow after the projection is the arrow. -/
theorem coeqDesc_proj {h C : Tree} (hh : Hom M ρ h B C)
    (heq : eval M ρ (comp h f) = eval M ρ (comp h g)) :
    eval M ρ (comp (coeqDesc f g h) (coeqProj f g)) = eval M ρ h := by
  obtain ⟨wf, hwf, hfs⟩ := hf.exists_eval
  obtain ⟨wg, hwg, hgs⟩ := hg.exists_eval
  obtain ⟨wh, hwh, hhs⟩ := hh.exists_eval
  have hts : [f, g, h].map (eval M ρ) = [wf, wg, wh].map Part.some := by simp [hwf, hwg, hwh]
  have hs : [wf, wg, wh].map Sigma.fst = [arr, arr, arr] := by simp [hfs, hgs, hhs]
  obtain ⟨w, hw, -⟩ := (coeqDesc_hom hM hf hg hh heq).exists_eval
  exact eval_eq_of_holds (ax_holds hM 72 rfl (by decide) hts hs
    (hs' := [⟨coeqDesc f g h, coeqDesc f g h⟩]) rfl ⟨w, hw, hw⟩
    (q := ⟨comp (coeqDesc f g h) (coeqProj f g), h⟩) rfl)

/-- An arrow from the coequalizer is the descent of its composite with the projection. -/
theorem coeqDesc_unique {k C : Tree} (hk : Hom M ρ k (coeqz f g) C) :
    eval M ρ (coeqDesc f g (comp k (coeqProj f g))) = eval M ρ k := by
  obtain ⟨wf, hwf, hfs⟩ := hf.exists_eval
  obtain ⟨wg, hwg, hgs⟩ := hg.exists_eval
  obtain ⟨wk, hwk, hks⟩ := hk.exists_eval
  have hts : [f, g, k].map (eval M ρ) = [wf, wg, wk].map Part.some := by simp [hwf, hwg, hwk]
  have hs : [wf, wg, wk].map Sigma.fst = [arr, arr, arr] := by simp [hfs, hgs, hks]
  obtain ⟨q, hq, -⟩ := isObj_coeqz hM hf hg
  exact eval_eq_of_holds (ax_holds hM 73 rfl (by decide) hts hs
    (hs' := [⟨coeqz f g, coeqz f g⟩, ⟨dom k, coeqz f g⟩]) rfl
    ⟨⟨q, hq, hq⟩, holds_of_eval_eq hk.eval_dom hq⟩
    (q := ⟨coeqDesc f g (comp k (coeqProj f g)), k⟩) rfl)

/-- The projection to the coequalizer is an epimorphism: two arrows from the coequalizer with
equal composites with it are equal. -/
theorem coeqProj_epi {k k' C : Tree} (hk : Hom M ρ k (coeqz f g) C)
    (hk' : Hom M ρ k' (coeqz f g) C)
    (h : eval M ρ (comp k (coeqProj f g)) = eval M ρ (comp k' (coeqProj f g))) :
    eval M ρ k = eval M ρ k' :=
  (coeqDesc_unique hM hf hg hk).symm.trans
    ((eval_op₃_congr 21 rfl rfl h).trans (coeqDesc_unique hM hf hg hk'))

/-- Two arrows from the product of an object and the coequalizer are equal when their composites
with the product of the object and the projection are. -/
theorem prod_coeq_ext {k k' X C : Tree} (hX : IsObj M ρ X)
    (hk : Hom M ρ k (prod X (coeqz f g)) C) (hk' : Hom M ρ k' (prod X (coeqz f g)) C)
    (h : eval M ρ (comp k (pair (fst X B) (comp (coeqProj f g) (snd X B)))) =
      eval M ρ (comp k' (pair (fst X B) (comp (coeqProj f g) (snd X B))))) :
    eval M ρ k = eval M ρ k' := by
  have hQ := isObj_coeqz hM hf hg
  have hp := coeqProj_hom hM hf hg
  have ht : ∀ {k}, Hom M ρ k (prod X (coeqz f g)) C → Hom M ρ
      (curry (coeqz f g) X (comp k (pair (snd (coeqz f g) X) (fst (coeqz f g) X))))
      (coeqz f g) (exp X C) := fun hk ↦ curry_hom hM hQ hX
    (comp_hom hM (pair_hom hM (snd_hom hM hQ hX) (fst_hom hM hQ hX)) hk)
  -- an arrow after the product with an arrow into the coequalizer, its factors exchanged, is
  -- the arrow after the product, after the exchange
  have hre : ∀ {k i E}, Hom M ρ k (prod X (coeqz f g)) C → Hom M ρ i E (coeqz f g) →
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
  -- the transposes are equal, having equal composites with the projection
  refine eq_of_curry_swap hM hX hQ hk hk' (coeqProj_epi hM hf hg (ht hk) (ht hk') ?_)
  exact (curry_swap_comp hM hX hk hp).trans ((eval_op₃_congr 24 rfl rfl ((hre hk hp).trans
    ((eval_op₂_congr 3 h rfl).trans (hre hk' hp).symm))).trans
    (curry_swap_comp hM hX hk' hp).symm)

end Coequalizers

/-- The projection of the coequalizer of two composites, an arrow, coequalizes two parallel arrows
into its domain, and its codomain has the value of their coequalizer. -/
theorem coeqProj_parallel {f g B D : Tree} (hf : ∃ a b, f = comp a b) (hg : ∃ c d, g = comp c d)
    (hi : Hom M ρ (coeqProj f g) B D) :
    ∃ A, Hom M ρ f A B ∧ Hom M ρ g A B ∧ eval M ρ D = eval M ρ (coeqz f g) := by
  obtain ⟨a, b, rfl⟩ := hf
  obtain ⟨c, d, rfl⟩ := hg
  obtain ⟨w, hw, -⟩ := hi.exists_eval
  obtain ⟨wf, hwf⟩ := exists_eval_of_eval_op hw (comp a b) (by simp)
  obtain ⟨wg, hwg⟩ := exists_eval_of_eval_op hw (comp c d) (by simp)
  have hfs : wf.1 = arr := sort_of_eval_op rfl hwf
  have hgs : wg.1 = arr := sort_of_eval_op rfl hwg
  have hts : [comp a b, comp c d].map (eval M ρ) = [wf, wg].map Part.some := by simp [hwf, hwg]
  have hs : [wf, wg].map Sigma.fst = [arr, arr] := by simp [hfs, hgs]
  have hP : Eqn.Holds M ρ ⟨coeqProj (comp a b) (comp c d), coeqProj (comp a b) (comp c d)⟩ :=
    ⟨w, hw, hw⟩
  obtain ⟨z, hz, -⟩ := ax_holds hM 62 rfl (by decide) hts hs
    (hs' := [⟨coeqProj (comp a b) (comp c d), coeqProj (comp a b) (comp c d)⟩]) rfl hP
    (q := ⟨coeqz (comp a b) (comp c d), coeqz (comp a b) (comp c d)⟩) rfl
  have hZ : Eqn.Holds M ρ ⟨coeqz (comp a b) (comp c d), coeqz (comp a b) (comp c d)⟩ :=
    ⟨z, hz, hz⟩
  have hdom := eval_eq_of_holds (ax_holds hM 59 rfl (by decide) hts hs
    (hs' := [⟨coeqz (comp a b) (comp c d), coeqz (comp a b) (comp c d)⟩]) rfl hZ
    (q := ⟨dom (comp a b), dom (comp c d)⟩) rfl)
  have hcod := eval_eq_of_holds (ax_holds hM 60 rfl (by decide) hts hs
    (hs' := [⟨coeqz (comp a b) (comp c d), coeqz (comp a b) (comp c d)⟩]) rfl hZ
    (q := ⟨cod (comp a b), cod (comp c d)⟩) rfl)
  have hpd := eval_eq_of_holds (ax_holds hM 64 rfl (by decide) hts hs
    (hs' := [⟨coeqz (comp a b) (comp c d), coeqz (comp a b) (comp c d)⟩]) rfl hZ
    (q := ⟨dom (coeqProj (comp a b) (comp c d)), cod (comp a b)⟩) rfl)
  have hpc := eval_eq_of_holds (ax_holds hM 65 rfl (by decide) hts hs
    (hs' := [⟨coeqz (comp a b) (comp c d), coeqz (comp a b) (comp c d)⟩]) rfl hZ
    (q := ⟨cod (coeqProj (comp a b) (comp c d)), coeqz (comp a b) (comp c d)⟩) rfl)
  -- the domain of the first arrow is an object
  obtain ⟨u, hu, -⟩ := ax_holds (ρ := ρ) hM 0 rfl (by decide) (ts := [comp a b]) (ws := [wf])
    (by simp only [List.map_cons, List.map_nil, hwf]) (by simp [hfs]) rfl trivial
    (q := ⟨dom (comp a b), dom (comp a b)⟩) rfl
  have hA : IsObj M ρ (dom (comp a b)) := ⟨u, hu, sort_of_eval_op rfl hu⟩
  have hB := hi.isObj_dom
  have hcf : eval M ρ (cod (comp a b)) = eval M ρ B := hpd.symm.trans hi.eval_dom
  exact ⟨dom (comp a b), ⟨wf, hwf, hfs, hA, hB, rfl, hcf⟩,
    ⟨wg, hwg, hgs, hA, hB, hdom.symm, hcod.symm.trans hcf⟩, hi.eval_cod.symm.trans hpc⟩

end Geb.FreeTopos

end
