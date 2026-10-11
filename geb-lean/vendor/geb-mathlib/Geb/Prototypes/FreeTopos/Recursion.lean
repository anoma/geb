/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Arrows

set_option doc.verso true in
/-!
# The folds of a model of the theory

The natural numbers object, the list objects and the rose-tree objects of a model of the theory
of an elementary topos, stated of the values of terms at an assignment: the typings of zero, the
successor, the empty list, construction and the structure maps of rose trees, and the computation
and the uniqueness of the folds, each an instance of an axiom. A fold is determined, in a
cartesian closed category, by its equations with a parameter (\[EscardoSimpson2025\],
Proposition 2.3): two arrows from the product of an
object of parameters with the natural numbers object that agree at zero and satisfy the
recursion equation of one step are equal ({lit}`natRec_param_unique`), and likewise from its
product with a list object ({lit}`listRec_param_unique`). The proof curries the two arrows
into arrows from the natural numbers object, or from the list object, into the exponential of
the parameters, which satisfy the equations of one fold without parameters. Such an arrow is the
fold into the exponential of the parameters, evaluated at the parameter
({name}`Geb.FreeTopos.natRecP`, {name}`Geb.FreeTopos.listRecP`).

## Main statements

* {lit}`natRec_zero`, {lit}`natRec_succ`, {lit}`natRec_unique` — the fold of the natural numbers
  object.
* {lit}`listRec_nil`, {lit}`listRec_cons`, {lit}`listRec_unique` — the fold of a list object.
* {lit}`roseRec_node`, {lit}`lroseRec_node`, {lit}`lroseRec_unique` — the folds of the rose-tree
  objects.
* {lit}`eval_listMap` — the action of a list object on an arrow is a fold.
* {lit}`listMap_comp`, {lit}`listMap_idt` — the action of a list object is functorial.
* {lit}`natRec_param_unique`, {lit}`listRec_param_unique` — the uniqueness of the folds with a
  parameter.
* {lit}`natRecP_spec`, {lit}`listRecP_spec` — the folds with a parameter.
* {lit}`natRec_param_exists`, {lit}`listRec_param_exists` — the existence of the folds with a
  parameter.

## References

* \[EscardoSimpson2025\]

## Tags

elementary topos, natural numbers object, list object, parametrised recursion
-/

set_option doc.verso true

@[expose] public section

namespace Geb.FreeTopos

open PartialHorn Sorts
open scoped FinEnum

universe v

variable {defs : List Defn} {M : Model.{v} (ext defs).sig} {ρ : List M.Val}

/-- The product of an object with an arrow, stated at the arrow's domain. -/
theorem eval_prodMapRight {h L C : Tree} (A : Tree) (hh : Hom M ρ h L C) :
    eval M ρ (prodMapRight A h) = eval M ρ (pair (fst A L) (comp h (snd A L))) :=
  eval_op₂_congr 9 (eval_op₂_congr 7 rfl hh.eval_dom)
    (eval_op₂_congr 3 rfl (eval_op₂_congr 8 rfl hh.eval_dom))

/-- The fold of the natural numbers object with a parameter respects the values of its start and
step. -/
theorem eval_natRecP_congr (P C : Tree) {z z' S S' : Tree} (hz : eval M ρ z = eval M ρ z')
    (hS : eval M ρ S = eval M ρ S') : eval M ρ (natRecP P C z S) = eval M ρ (natRecP P C z' S') :=
  eval_op₂_congr 3 rfl (eval_op₂_congr 9 (eval_op₂_congr 3 (eval_op₂_congr 32
    (eval_op₃_congr 24 rfl rfl (eval_op₂_congr 3 hz rfl))
    (eval_op₃_congr 24 rfl rfl (eval_op₂_congr 3 hS rfl))) rfl) rfl)

/-- The fold of a list object with a parameter respects the values of its start and step. -/
theorem eval_listRecP_congr (P A C : Tree) {z z' S S' : Tree} (hz : eval M ρ z = eval M ρ z')
    (hS : eval M ρ S = eval M ρ S') :
    eval M ρ (listRecP P A C z S) = eval M ρ (listRecP P A C z' S') :=
  eval_op₂_congr 3 rfl (eval_op₂_congr 9 (eval_op₂_congr 3 (eval_op₃_congr 36 rfl
    (eval_op₃_congr 24 rfl rfl (eval_op₂_congr 3 hz rfl))
    (eval_op₃_congr 24 rfl rfl (eval_op₂_congr 3 hS rfl))) rfl) rfl)

section Folds

variable (hM : IsModel (ext defs) M)
include hM

/-- Zero is an arrow from the terminal object to the natural numbers object. -/
theorem zeroN_hom : Hom M ρ zeroN one nat := by
  have hd := eval_eq_of_holds (ax_holds (ρ := ρ) hM 98 rfl (by decide) (ts := []) (ws := []) rfl
    rfl rfl trivial (q := ⟨dom zeroN, one⟩) rfl)
  obtain ⟨o, ho, -⟩ := isObj_one (ρ := ρ) hM
  obtain ⟨w, hw⟩ := exists_eval_of_dom (hd.trans ho)
  exact ⟨w, hw, sort_of_eval_op rfl hw, isObj_one hM, isObj_nat hM, hd,
    eval_eq_of_holds (ax_holds (ρ := ρ) hM 99 rfl (by decide) (ts := []) (ws := []) rfl rfl rfl
      trivial (q := ⟨cod zeroN, nat⟩) rfl)⟩

/-- The successor is an arrow from the natural numbers object to itself. -/
theorem succ_hom : Hom M ρ succ nat nat := by
  have hd := eval_eq_of_holds (ax_holds (ρ := ρ) hM 100 rfl (by decide) (ts := []) (ws := [])
    rfl rfl rfl trivial (q := ⟨dom succ, nat⟩) rfl)
  obtain ⟨o, ho, -⟩ := isObj_nat (ρ := ρ) hM
  obtain ⟨w, hw⟩ := exists_eval_of_dom (hd.trans ho)
  exact ⟨w, hw, sort_of_eval_op rfl hw, isObj_nat hM, isObj_nat hM, hd,
    eval_eq_of_holds (ax_holds (ρ := ρ) hM 101 rfl (by decide) (ts := []) (ws := []) rfl rfl rfl
      trivial (q := ⟨cod succ, nat⟩) rfl)⟩

/-- The empty list is an arrow from the terminal object to the list object. -/
theorem nil_hom {A : Tree} (hA : IsObj M ρ A) : Hom M ρ (nil A) one (list A) := by
  obtain ⟨a, ha, has⟩ := hA
  have hts : [A].map (eval M ρ) = [a].map Part.some := by simp [ha]
  have hs : [a].map Sigma.fst = [obj] := by simp [has]
  have hd := eval_eq_of_holds (ax_holds hM 112 rfl (by decide) hts hs rfl trivial
    (q := ⟨dom (nil A), one⟩) rfl)
  obtain ⟨o, ho, -⟩ := isObj_one (ρ := ρ) hM
  obtain ⟨w, hw⟩ := exists_eval_of_dom (hd.trans ho)
  exact ⟨w, hw, sort_of_eval_op rfl hw, isObj_one hM, isObj_list hM ⟨a, ha, has⟩, hd,
    eval_eq_of_holds (ax_holds hM 113 rfl (by decide) hts hs rfl trivial
      (q := ⟨cod (nil A), list A⟩) rfl)⟩

/-- Construction is an arrow from the product of the element object and the list object to the
list object. -/
theorem cons_hom {A : Tree} (hA : IsObj M ρ A) : Hom M ρ (cons A) (prod A (list A)) (list A) := by
  have hL := isObj_list hM hA
  have hP := isObj_prod hM hA hL
  obtain ⟨a, ha, has⟩ := hA
  have hts : [A].map (eval M ρ) = [a].map Part.some := by simp [ha]
  have hs : [a].map Sigma.fst = [obj] := by simp [has]
  have hd := eval_eq_of_holds (ax_holds hM 114 rfl (by decide) hts hs rfl trivial
    (q := ⟨dom (cons A), prod A (list A)⟩) rfl)
  obtain ⟨p, hp, -⟩ := hP
  obtain ⟨w, hw⟩ := exists_eval_of_dom (hd.trans hp)
  exact ⟨w, hw, sort_of_eval_op rfl hw, isObj_prod hM ⟨a, ha, has⟩ hL, hL, hd,
    eval_eq_of_holds (ax_holds hM 115 rfl (by decide) hts hs rfl trivial
      (q := ⟨cod (cons A), list A⟩) rfl)⟩

/-- The fold of the natural numbers object at zero is the start. -/
theorem natRec_zero {z s C : Tree} (hz : Hom M ρ z one C) (hs : Hom M ρ s C C) :
    eval M ρ (comp (natRec z s) zeroN) = eval M ρ z := by
  obtain ⟨wz, hwz, hzs⟩ := hz.exists_eval
  obtain ⟨ws, hws, hss⟩ := hs.exists_eval
  obtain ⟨w, hw, -⟩ := (natRec_hom hM hz hs).exists_eval
  exact eval_eq_of_holds (ax_holds hM 108 rfl (by decide) (ts := [z, s]) (ws := [wz, ws])
    (by simp [hwz, hws]) (by simp [hzs, hss]) (hs' := [⟨natRec z s, natRec z s⟩]) rfl
    ⟨w, hw, hw⟩ (q := ⟨comp (natRec z s) zeroN, z⟩) rfl)

/-- The fold of the natural numbers object after the successor is the step after the fold. -/
theorem natRec_succ {z s C : Tree} (hz : Hom M ρ z one C) (hs : Hom M ρ s C C) :
    eval M ρ (comp (natRec z s) succ) = eval M ρ (comp s (natRec z s)) := by
  obtain ⟨wz, hwz, hzs⟩ := hz.exists_eval
  obtain ⟨ws, hws, hss⟩ := hs.exists_eval
  obtain ⟨w, hw, -⟩ := (natRec_hom hM hz hs).exists_eval
  exact eval_eq_of_holds (ax_holds hM 109 rfl (by decide) (ts := [z, s]) (ws := [wz, ws])
    (by simp [hwz, hws]) (by simp [hzs, hss]) (hs' := [⟨natRec z s, natRec z s⟩]) rfl
    ⟨w, hw, hw⟩ (q := ⟨comp (natRec z s) succ, comp s (natRec z s)⟩) rfl)

/-- An arrow from the natural numbers object that is the start at zero and the step after
itself at the successor is the fold. -/
theorem natRec_unique {h z s C : Tree} (hz : Hom M ρ z one C) (hs : Hom M ρ s C C)
    (hh : Hom M ρ h nat C) (h₀ : eval M ρ (comp h zeroN) = eval M ρ z)
    (h₁ : eval M ρ (comp h succ) = eval M ρ (comp s h)) :
    eval M ρ h = eval M ρ (natRec z s) := by
  obtain ⟨wz, hwz, hzs⟩ := hz.exists_eval
  obtain ⟨ws, hws, hss⟩ := hs.exists_eval
  obtain ⟨wh, hwh, hhs⟩ := hh.exists_eval
  obtain ⟨w, hw, -⟩ := (natRec_hom hM hz hs).exists_eval
  obtain ⟨n, hn, -⟩ := isObj_nat (ρ := ρ) hM
  obtain ⟨c, hc, -⟩ := (comp_hom hM hh hs).exists_eval
  exact eval_eq_of_holds (ax_holds hM 110 rfl (by decide) (ts := [z, s, h])
    (ws := [wz, ws, wh]) (by simp [hwz, hws, hwh]) (by simp [hzs, hss, hhs])
    (hs' := [⟨natRec z s, natRec z s⟩, ⟨dom h, nat⟩, ⟨comp h zeroN, z⟩,
      ⟨comp h succ, comp s h⟩]) rfl
    ⟨⟨w, hw, hw⟩, holds_of_eval_eq hh.eval_dom hn, holds_of_eval_eq h₀ hwz,
      holds_of_eval_eq h₁ hc⟩ (q := ⟨h, natRec z s⟩) rfl)

/-- The fold of a list object at the empty list is the start. -/
theorem listRec_nil {A z s C : Tree} (hA : IsObj M ρ A) (hz : Hom M ρ z one C)
    (hs : Hom M ρ s (prod A C) C) : eval M ρ (comp (listRec A z s) (nil A)) = eval M ρ z := by
  obtain ⟨a, ha, has⟩ := hA
  obtain ⟨wz, hwz, hzs⟩ := hz.exists_eval
  obtain ⟨ws, hws, hss⟩ := hs.exists_eval
  obtain ⟨w, hw, -⟩ := (listRec_hom hM ⟨a, ha, has⟩ hz hs).exists_eval
  exact eval_eq_of_holds (ax_holds hM 122 rfl (by decide) (ts := [A, z, s]) (ws := [a, wz, ws])
    (by simp [ha, hwz, hws]) (by simp [has, hzs, hss])
    (hs' := [⟨listRec A z s, listRec A z s⟩]) rfl ⟨w, hw, hw⟩
    (q := ⟨comp (listRec A z s) (nil A), z⟩) rfl)

/-- The fold of a list object after construction is the step after the element paired with the
fold of the tail. -/
theorem listRec_cons {A z s C : Tree} (hA : IsObj M ρ A) (hz : Hom M ρ z one C)
    (hs : Hom M ρ s (prod A C) C) :
    eval M ρ (comp (listRec A z s) (cons A)) =
      eval M ρ (comp s (pair (fst A (list A)) (comp (listRec A z s) (snd A (list A))))) := by
  have hr := listRec_hom hM hA hz hs
  obtain ⟨a, ha, has⟩ := hA
  obtain ⟨wz, hwz, hzs⟩ := hz.exists_eval
  obtain ⟨ws, hws, hss⟩ := hs.exists_eval
  obtain ⟨w, hw, -⟩ := hr.exists_eval
  refine (eval_eq_of_holds (ax_holds hM 123 rfl (by decide) (ts := [A, z, s])
    (ws := [a, wz, ws]) (by simp [ha, hwz, hws]) (by simp [has, hzs, hss])
    (hs' := [⟨listRec A z s, listRec A z s⟩]) rfl ⟨w, hw, hw⟩
    (q := ⟨comp (listRec A z s) (cons A), comp s (prodMapRight A (listRec A z s))⟩) rfl)).trans
    ?_
  exact eval_op₂_congr 3 rfl (eval_prodMapRight A hr)

/-- An arrow from a list object that is the start at the empty list and the step after the
element paired with itself at construction is the fold. -/
theorem listRec_unique {h A z s C : Tree} (hA : IsObj M ρ A) (hz : Hom M ρ z one C)
    (hs : Hom M ρ s (prod A C) C) (hh : Hom M ρ h (list A) C)
    (h₀ : eval M ρ (comp h (nil A)) = eval M ρ z)
    (h₁ : eval M ρ (comp h (cons A)) =
      eval M ρ (comp s (pair (fst A (list A)) (comp h (snd A (list A)))))) :
    eval M ρ h = eval M ρ (listRec A z s) := by
  have hL := isObj_list hM hA
  have hc := comp_hom hM (pair_hom hM (fst_hom hM hA hL) (comp_hom hM (snd_hom hM hA hL) hh)) hs
  obtain ⟨a, ha, has⟩ := hA
  obtain ⟨wz, hwz, hzs⟩ := hz.exists_eval
  obtain ⟨ws, hws, hss⟩ := hs.exists_eval
  obtain ⟨wh, hwh, hhs⟩ := hh.exists_eval
  obtain ⟨w, hw, -⟩ := (listRec_hom hM ⟨a, ha, has⟩ hz hs).exists_eval
  obtain ⟨l, hl, -⟩ := hL
  obtain ⟨c, hcv, -⟩ := hc.exists_eval
  exact eval_eq_of_holds (ax_holds hM 124 rfl (by decide) (ts := [A, z, s, h])
    (ws := [a, wz, ws, wh]) (by simp [ha, hwz, hws, hwh]) (by simp [has, hzs, hss, hhs])
    (hs' := [⟨listRec A z s, listRec A z s⟩, ⟨dom h, list A⟩, ⟨comp h (nil A), z⟩,
      ⟨comp h (cons A), comp s (prodMapRight A h)⟩]) rfl
    ⟨⟨w, hw, hw⟩, holds_of_eval_eq hh.eval_dom hl, holds_of_eval_eq h₀ hwz,
      holds_of_eval_eq (h₁.trans (eval_op₂_congr 3 rfl (eval_prodMapRight A hh)).symm)
        ((eval_op₂_congr 3 rfl (eval_prodMapRight A hh)).trans hcv)⟩
    (q := ⟨h, listRec A z s⟩) rfl)

/-- The structure map of the rose-tree object is an arrow from the product of the natural
numbers object and the list object of the rose-tree object. -/
theorem node_hom : Hom M ρ node (prod nat (list rose)) rose := by
  have hP := isObj_prod hM (isObj_nat hM) (isObj_list hM (isObj_rose (ρ := ρ) hM))
  obtain ⟨p, hp, -⟩ := id hP
  have hd := eval_eq_of_holds (ax_holds (ρ := ρ) hM 125 rfl (by decide) (ts := []) (ws := []) rfl
    rfl rfl trivial (q := ⟨dom node, prod nat (list rose)⟩) rfl)
  obtain ⟨w, hw⟩ := exists_eval_of_dom (hd.trans hp)
  exact ⟨w, hw, sort_of_eval_op rfl hw, hP, isObj_rose hM, hd,
    eval_eq_of_holds (ax_holds (ρ := ρ) hM 126 rfl (by decide) (ts := []) (ws := []) rfl rfl rfl
      trivial (q := ⟨cod node, rose⟩) rfl)⟩

/-- The fold of the rose-tree object after the structure map is the step after the product of
the natural numbers object with the fold's action on the children. -/
theorem roseRec_node {s C : Tree} (hs : Hom M ρ s (prod nat (list C)) C) :
    eval M ρ (comp (roseRec s) node) =
      eval M ρ (comp s (prodMapRight nat (listMap (roseRec s)))) := by
  obtain ⟨w, hw, -⟩ := (roseRec_hom hM hs).exists_eval
  obtain ⟨ws, hws, hss⟩ := hs.exists_eval
  exact eval_eq_of_holds (ax_holds hM 131 rfl (by decide) (ts := [s]) (ws := [ws])
    (by simp [hws]) (by simp [hss]) (hs' := [⟨roseRec s, roseRec s⟩]) rfl ⟨w, hw, hw⟩
    (q := ⟨comp (roseRec s) node, comp s (prodMapRight nat (listMap (roseRec s)))⟩) rfl)

/-- An arrow from the rose-tree object whose composite with the structure map is the step after
the product of the natural numbers object with its action on the children is the fold. -/
theorem roseRec_unique {h s C : Tree} (hs : Hom M ρ s (prod nat (list C)) C)
    (hh : Hom M ρ h rose C)
    (h₁ : eval M ρ (comp h node) = eval M ρ (comp s (prodMapRight nat (listMap h)))) :
    eval M ρ h = eval M ρ (roseRec s) := by
  obtain ⟨w, hw, -⟩ := (roseRec_hom hM hs).exists_eval
  obtain ⟨c, hcv, -⟩ := (comp_hom hM (node_hom hM) hh).exists_eval
  obtain ⟨r, hr, -⟩ := isObj_rose (ρ := ρ) hM
  obtain ⟨ws, hws, hss⟩ := hs.exists_eval
  obtain ⟨wh, hwh, hhs⟩ := hh.exists_eval
  exact eval_eq_of_holds (ax_holds hM 132 rfl (by decide) (ts := [s, h]) (ws := [ws, wh])
    (by simp [hws, hwh]) (by simp [hss, hhs])
    (hs' := [⟨roseRec s, roseRec s⟩, ⟨dom h, rose⟩,
      ⟨comp h node, comp s (prodMapRight nat (listMap h))⟩]) rfl
    ⟨⟨w, hw, hw⟩, holds_of_eval_eq hh.eval_dom hr, holds_of_eval_eq h₁ (h₁.symm.trans hcv)⟩
    (q := ⟨h, roseRec s⟩) rfl)

/-- The action of the list object on an arrow is an arrow between the list objects. -/
theorem listMap_hom {f A B : Tree} (hf : Hom M ρ f A B) :
    Hom M ρ (listMap f) (list A) (list B) := by
  have hf' : Hom M ρ f (dom f) (cod f) := hf.congr rfl hf.eval_dom hf.eval_cod
  have hA := hf'.isObj_dom
  have hB := hf'.isObj_cod
  have hLB := isObj_list hM hB
  exact (listRec_hom hM hA (nil_hom hM hB) (comp_hom hM
    (pair_hom hM (comp_hom hM (fst_hom hM hA hLB) hf') (snd_hom hM hA hLB))
    (cons_hom hM hB))).congr rfl (eval_op₁_congr 33 hf.eval_dom.symm)
    (eval_op₁_congr 33 hf.eval_cod.symm)

/-- The action of the list object on an arrow is the fold from the empty list by construction
after the product of the arrow with the identity. -/
theorem eval_listMap {h T C : Tree} (hh : Hom M ρ h T C) :
    eval M ρ (listMap h) = eval M ρ (listRec T (comp (nil C) (bang one))
      (comp (cons C) (pair (comp h (fst T (list C))) (snd T (list C))))) := by
  have hdom := hh.eval_dom
  have hcod := hh.eval_cod
  refine Eq.symm (eval_op₃_congr 36 hdom.symm ?_ ?_)
  · exact ((eval_op₂_congr 3 rfl (bang_unique hM (idt_hom hM (isObj_one hM))).symm).trans
      (comp_idt hM (nil_hom hM hh.isObj_cod))).trans (eval_op₁_congr 34 hcod.symm)
  · exact eval_op₂_congr 3 (eval_op₁_congr 35 hcod.symm) (eval_op₂_congr 9
      (eval_op₂_congr 3 rfl (eval_op₂_congr 7 hdom.symm (eval_op₁_congr 33 hcod.symm)))
      (eval_op₂_congr 8 hdom.symm (eval_op₁_congr 33 hcod.symm)))

/-- The product of an object with an arrow after a pairing is the pairing of the first arrow with
the arrow after the second. -/
theorem prodMapRight_pair {f g h X A L N : Tree} (hf : Hom M ρ f X A) (hg : Hom M ρ g X L)
    (hh : Hom M ρ h L N) :
    eval M ρ (comp (prodMapRight A h) (pair f g)) = eval M ρ (pair f (comp h g)) := by
  have hA := hf.isObj_cod
  have hL := hg.isObj_cod
  have hfA := fst_hom hM hA hL
  have hsA := snd_hom hM hA hL
  have hfg := pair_hom hM hf hg
  exact (eval_op₂_congr 3 (eval_prodMapRight A hh) rfl).trans
    ((pair_comp hM hfA (comp_hom hM hsA hh) hfg).trans (eval_op₂_congr 9 (fst_pair hM hf hg)
      ((comp_assoc hM hfg hsA hh).symm.trans (eval_op₂_congr 3 rfl (snd_pair hM hf hg)))))

/-- The structure map of the rose-tree object over an object of labels is an arrow from the
product of the object of labels and the list object of the rose-tree object. -/
theorem lnode_hom {A : Tree} (hA : IsObj M ρ A) :
    Hom M ρ (lnode A) (prod A (list (lrose A))) (lrose A) := by
  have hR := isObj_lrose hM hA
  have hP := isObj_prod hM hA (isObj_list hM hR)
  obtain ⟨p, hp, -⟩ := id hP
  obtain ⟨a, ha, has⟩ := hA
  have hts : [A].map (eval M ρ) = [a].map Part.some := by simp [ha]
  have hs : [a].map Sigma.fst = [obj] := by simp [has]
  have hd := eval_eq_of_holds (ax_holds hM 134 rfl (by decide) hts hs rfl trivial
    (q := ⟨dom (lnode A), prod A (list (lrose A))⟩) rfl)
  obtain ⟨w, hw⟩ := exists_eval_of_dom (hd.trans hp)
  exact ⟨w, hw, sort_of_eval_op rfl hw, hP, hR, hd,
    eval_eq_of_holds (ax_holds hM 135 rfl (by decide) hts hs rfl trivial
      (q := ⟨cod (lnode A), lrose A⟩) rfl)⟩

/-- The fold of the rose-tree object over an object of labels by a step. -/
theorem lroseRec_hom {A s C : Tree} (hA : IsObj M ρ A) (hs : Hom M ρ s (prod A (list C)) C) :
    Hom M ρ (lroseRec A s) (lrose A) C := by
  have hR := isObj_lrose hM hA
  obtain ⟨a, ha, has⟩ := hA
  obtain ⟨ws, hws, hss, ⟨p, hp, -⟩, hC, hds, hcs⟩ := hs
  have hts : [A, s].map (eval M ρ) = [a, ws].map Part.some := by simp [ha, hws]
  have hsr : [a, ws].map Sigma.fst = [obj, arr] := by simp [has, hss]
  have hpc : eval M ρ (prod A (list (cod s))) = eval M ρ (prod A (list C)) :=
    eval_op₂_congr 6 rfl (eval_op₁_congr 33 hcs)
  obtain ⟨w, hw, -⟩ := ax_holds hM 137 rfl (by decide) hts hsr
    (hs' := [⟨dom s, prod A (list (cod s))⟩]) rfl
    (holds_of_eval_eq (hds.trans hpc.symm) (hpc.trans hp))
    (q := ⟨lroseRec A s, lroseRec A s⟩) rfl
  have hr : Eqn.Holds M ρ ⟨lroseRec A s, lroseRec A s⟩ := ⟨w, hw, hw⟩
  exact ⟨w, hw, sort_of_eval_op rfl hw, hR, hC,
    eval_eq_of_holds (ax_holds hM 138 rfl (by decide) hts hsr
      (hs' := [⟨lroseRec A s, lroseRec A s⟩]) rfl hr (q := ⟨dom (lroseRec A s), lrose A⟩) rfl),
    (eval_eq_of_holds (ax_holds hM 139 rfl (by decide) hts hsr
      (hs' := [⟨lroseRec A s, lroseRec A s⟩]) rfl hr
      (q := ⟨cod (lroseRec A s), cod s⟩) rfl)).trans hcs⟩

/-- The fold of the rose-tree object over an object of labels after the structure map is the
step after the product of the object of labels with the fold's action on the children. -/
theorem lroseRec_node {A s C : Tree} (hA : IsObj M ρ A) (hs : Hom M ρ s (prod A (list C)) C) :
    eval M ρ (comp (lroseRec A s) (lnode A)) =
      eval M ρ (comp s (prodMapRight A (listMap (lroseRec A s)))) := by
  obtain ⟨w, hw, -⟩ := (lroseRec_hom hM hA hs).exists_eval
  obtain ⟨a, ha, has⟩ := hA
  obtain ⟨ws, hws, hss⟩ := hs.exists_eval
  exact eval_eq_of_holds (ax_holds hM 140 rfl (by decide) (ts := [A, s]) (ws := [a, ws])
    (by simp [ha, hws]) (by simp [has, hss]) (hs' := [⟨lroseRec A s, lroseRec A s⟩]) rfl
    ⟨w, hw, hw⟩ (q := ⟨comp (lroseRec A s) (lnode A),
      comp s (prodMapRight A (listMap (lroseRec A s)))⟩) rfl)

/-- An arrow from the rose-tree object over an object of labels whose composite with the
structure map is the step after the product of the object of labels with its action on the
children is the fold. -/
theorem lroseRec_unique {h A s C : Tree} (hA : IsObj M ρ A) (hs : Hom M ρ s (prod A (list C)) C)
    (hh : Hom M ρ h (lrose A) C)
    (h₁ : eval M ρ (comp h (lnode A)) = eval M ρ (comp s (prodMapRight A (listMap h)))) :
    eval M ρ h = eval M ρ (lroseRec A s) := by
  obtain ⟨w, hw, -⟩ := (lroseRec_hom hM hA hs).exists_eval
  obtain ⟨c, hcv, -⟩ := (comp_hom hM (lnode_hom hM hA) hh).exists_eval
  obtain ⟨r, hr, -⟩ := isObj_lrose hM hA
  obtain ⟨a, ha, has⟩ := hA
  obtain ⟨ws, hws, hss⟩ := hs.exists_eval
  obtain ⟨wh, hwh, hhs⟩ := hh.exists_eval
  exact eval_eq_of_holds (ax_holds hM 141 rfl (by decide) (ts := [A, s, h]) (ws := [a, ws, wh])
    (by simp [ha, hws, hwh]) (by simp [has, hss, hhs])
    (hs' := [⟨lroseRec A s, lroseRec A s⟩, ⟨dom h, lrose A⟩,
      ⟨comp h (lnode A), comp s (prodMapRight A (listMap h))⟩]) rfl
    ⟨⟨w, hw, hw⟩, holds_of_eval_eq hh.eval_dom hr, holds_of_eval_eq h₁ (h₁.symm.trans hcv)⟩
    (q := ⟨h, lroseRec A s⟩) rfl)

end Folds

section Parameters

variable (hM : IsModel (ext defs) M)
include hM

/-- The pairing of a product's projections is its identity. -/
theorem pair_fst_snd {A B : Tree} (hA : IsObj M ρ A) (hB : IsObj M ρ B) :
    eval M ρ (pair (fst A B) (snd A B)) = eval M ρ (idt (prod A B)) :=
  (eval_op₂_congr 9 (comp_idt hM (fst_hom hM hA hB)).symm
    (comp_idt hM (snd_hom hM hA hB)).symm).trans
    (pair_eta hM hA hB (idt_hom hM (isObj_prod hM hA hB)))

/-- The product of an object with an arrow is an arrow between the products. -/
theorem prodMapRight_hom {h L N : Tree} (A : Tree) (hA : IsObj M ρ A) (hh : Hom M ρ h L N) :
    Hom M ρ (prodMapRight A h) (prod A L) (prod A N) :=
  (pair_hom hM (fst_hom hM hA hh.isObj_dom) (comp_hom hM (snd_hom hM hA hh.isObj_dom) hh)).congr
    (eval_prodMapRight A hh) rfl rfl

/-- The product of an object with an arrow after its product with another is its product with
the composite. -/
theorem prodMapRight_comp {f g L N P : Tree} (A : Tree) (hA : IsObj M ρ A) (hf : Hom M ρ f L N)
    (hg : Hom M ρ g N P) :
    eval M ρ (comp (prodMapRight A g) (prodMapRight A f)) =
      eval M ρ (prodMapRight A (comp g f)) := by
  have hL := hf.isObj_dom
  have hfA := fst_hom hM hA hL
  have hsA := snd_hom hM hA hL
  refine (eval_op₂_congr 3 rfl (eval_prodMapRight A hf)).trans ((prodMapRight_pair hM hfA
    (comp_hom hM hsA hf) hg).trans ((eval_op₂_congr 9 rfl (comp_assoc hM hsA hf hg)).trans ?_))
  exact (eval_prodMapRight A (comp_hom hM hf hg)).symm

/-- The product of an object with an identity is the identity of the product. -/
theorem prodMapRight_idt {B : Tree} (A : Tree) (hA : IsObj M ρ A) (hB : IsObj M ρ B) :
    eval M ρ (prodMapRight A (idt B)) = eval M ρ (idt (prod A B)) :=
  (eval_prodMapRight A (idt_hom hM hB)).trans ((eval_op₂_congr 9 rfl
    (idt_comp hM (snd_hom hM hA hB))).trans (pair_fst_snd hM hA hB))

/-- An arrow after a pairing whose components are arrows after the projections is the arrow
after the pairing of their composites with the pairing's components. -/
theorem comp_pair_proj {c u v a b P L X W Y Z : Tree} (hc : Hom M ρ c (prod X W) Z)
    (hu : Hom M ρ u P X) (hv : Hom M ρ v L W) (ha : Hom M ρ a Y P) (hb : Hom M ρ b Y L) :
    eval M ρ (comp (comp c (pair (comp u (fst P L)) (comp v (snd P L)))) (pair a b)) =
      eval M ρ (comp c (pair (comp u a) (comp v b))) := by
  have hP := hu.isObj_dom
  have hL := hv.isObj_dom
  have hf := fst_hom hM hP hL
  have hs := snd_hom hM hP hL
  have hab := pair_hom hM ha hb
  have hp := pair_hom hM (comp_hom hM hf hu) (comp_hom hM hs hv)
  refine (comp_assoc hM hab hp hc).symm.trans (eval_op₂_congr 3 rfl ?_)
  refine (pair_comp hM (comp_hom hM hf hu) (comp_hom hM hs hv) hab).trans
    (eval_op₂_congr 9 ?_ ?_)
  · exact (comp_assoc hM hab hf hu).symm.trans (eval_op₂_congr 3 rfl (fst_pair hM ha hb))
  · exact (comp_assoc hM hab hs hv).symm.trans (eval_op₂_congr 3 rfl (snd_pair hM ha hb))

/-- The action of the list object on an arrow after construction is the construction of the
arrow at the element onto the action at the tail. -/
theorem listMap_cons {f A B : Tree} (hf : Hom M ρ f A B) :
    eval M ρ (comp (listMap f) (cons A)) =
      eval M ρ (comp (cons B) (pair (comp f (fst A (list A)))
        (comp (listMap f) (snd A (list A))))) := by
  have hA := hf.isObj_dom
  have hB := hf.isObj_cod
  have hLA := isObj_list hM hA
  have hLB := isObj_list hM hB
  have hz := comp_hom hM (bang_hom hM (isObj_one hM)) (nil_hom hM hB)
  have hsL := snd_hom hM hA hLB
  have hs := comp_hom hM (pair_hom hM (comp_hom hM (fst_hom hM hA hLB) hf) hsL) (cons_hom hM hB)
  have hLf := listMap_hom hM hf
  refine (eval_op₂_congr 3 (eval_listMap hM hf) rfl).trans ((listRec_cons hM hA hz hs).trans ?_)
  refine (eval_op₂_congr 3 rfl (eval_op₂_congr 9 rfl (eval_op₂_congr 3
    (eval_listMap hM hf).symm rfl))).trans ?_
  refine (eval_op₂_congr 3 (eval_op₂_congr 3 rfl (eval_op₂_congr 9 rfl
    (idt_comp hM hsL).symm)) rfl).trans ?_
  refine (comp_pair_proj hM (cons_hom hM hB) hf (idt_hom hM hLB) (fst_hom hM hA hLA)
    (comp_hom hM (snd_hom hM hA hLA) hLf)).trans ?_
  exact eval_op₂_congr 3 rfl (eval_op₂_congr 9 rfl (idt_comp hM (comp_hom hM
    (snd_hom hM hA hLA) hLf)))

/-- The action of the list object on an arrow at the empty list is the empty list. -/
theorem listMap_nil {f A B : Tree} (hf : Hom M ρ f A B) :
    eval M ρ (comp (listMap f) (nil A)) = eval M ρ (nil B) := by
  have hA := hf.isObj_dom
  have hB := hf.isObj_cod
  have h1 := isObj_one (ρ := ρ) hM
  have hz := comp_hom hM (bang_hom hM h1) (nil_hom hM hB)
  have hs := comp_hom hM (pair_hom hM (comp_hom hM (fst_hom hM hA (isObj_list hM hB)) hf)
    (snd_hom hM hA (isObj_list hM hB))) (cons_hom hM hB)
  refine (eval_op₂_congr 3 (eval_listMap hM hf) rfl).trans ((listRec_nil hM hA hz hs).trans ?_)
  exact (eval_op₂_congr 3 rfl (bang_unique hM (idt_hom hM h1)).symm).trans
    (comp_idt hM (nil_hom hM hB))

/-- The action of the list object on arrows of equal value has one value. -/
theorem listMap_congr {f f' A B : Tree} (hf : Hom M ρ f A B) (hf' : Hom M ρ f' A B)
    (h : eval M ρ f = eval M ρ f') : eval M ρ (listMap f) = eval M ρ (listMap f') :=
  (eval_listMap hM hf).trans ((eval_op₃_congr 36 rfl rfl (eval_op₂_congr 3 rfl
    (eval_op₂_congr 9 (eval_op₂_congr 3 h rfl) rfl))).trans (eval_listMap hM hf').symm)

/-- The action of the list object on a composite is the composite of the actions. -/
theorem listMap_comp {f g A B C : Tree} (hf : Hom M ρ f A B) (hg : Hom M ρ g B C) :
    eval M ρ (comp (listMap g) (listMap f)) = eval M ρ (listMap (comp g f)) := by
  have hA := hf.isObj_dom
  have hB := hf.isObj_cod
  have hC := hg.isObj_cod
  have hLA := isObj_list hM hA
  have hLC := isObj_list hM hC
  have h1 := isObj_one (ρ := ρ) hM
  have hgf := comp_hom hM hf hg
  have hLf := listMap_hom hM hf
  have hLg := listMap_hom hM hg
  have hh := comp_hom hM hLf hLg
  have hz := comp_hom hM (bang_hom hM h1) (nil_hom hM hC)
  have hsL := snd_hom hM hA hLC
  have hs := comp_hom hM (pair_hom hM (comp_hom hM (fst_hom hM hA hLC) hgf) hsL)
    (cons_hom hM hC)
  have hfA := fst_hom hM hA hLA
  have hsA := snd_hom hM hA hLA
  refine Eq.trans ?_ (eval_listMap hM hgf).symm
  refine listRec_unique hM hA hz hs hh ?_ ?_
  · -- at the empty list
    refine (comp_assoc hM (nil_hom hM hA) hLf hLg).symm.trans ?_
    refine (eval_op₂_congr 3 rfl (listMap_nil hM hf)).trans ((listMap_nil hM hg).trans ?_)
    exact ((eval_op₂_congr 3 rfl (bang_unique hM (idt_hom hM h1)).symm).trans
      (comp_idt hM (nil_hom hM hC))).symm
  · -- at a construction
    refine (comp_assoc hM (cons_hom hM hA) hLf hLg).symm.trans ?_
    refine (eval_op₂_congr 3 rfl (listMap_cons hM hf)).trans ?_
    refine (comp_assoc hM (pair_hom hM (comp_hom hM hfA hf) (comp_hom hM hsA hLf))
      (cons_hom hM hB) hLg).trans ?_
    refine (eval_op₂_congr 3 (listMap_cons hM hg) rfl).trans ?_
    refine (comp_pair_proj hM (cons_hom hM hC) hg hLg (comp_hom hM hfA hf)
      (comp_hom hM hsA hLf)).trans ?_
    refine Eq.trans ?_ (eval_op₂_congr 3 (eval_op₂_congr 3 rfl (eval_op₂_congr 9 rfl
      (idt_comp hM hsL))) rfl)
    refine Eq.trans ?_ (comp_pair_proj hM (cons_hom hM hC) hgf (idt_hom hM hLC) hfA
      (comp_hom hM hsA hh)).symm
    exact eval_op₂_congr 3 rfl (eval_op₂_congr 9 (comp_assoc hM hfA hf hg)
      ((comp_assoc hM hsA hLf hLg).trans (idt_comp hM (comp_hom hM hsA hh)).symm))

/-- The action of the list object on an identity is the identity of the list object. -/
theorem listMap_idt {A : Tree} (hA : IsObj M ρ A) :
    eval M ρ (listMap (idt A)) = eval M ρ (idt (list A)) := by
  have hLA := isObj_list hM hA
  have h1 := isObj_one (ρ := ρ) hM
  have hi := idt_hom hM hA
  have hz := comp_hom hM (bang_hom hM h1) (nil_hom hM hA)
  have hsL := snd_hom hM hA hLA
  have hfA := fst_hom hM hA hLA
  have hs := comp_hom hM (pair_hom hM (comp_hom hM hfA hi) hsL) (cons_hom hM hA)
  refine (eval_listMap hM hi).trans (listRec_unique hM hA hz hs (idt_hom hM hLA) ?_ ?_).symm
  · exact (idt_comp hM (nil_hom hM hA)).trans ((eval_op₂_congr 3 rfl
      (bang_unique hM (idt_hom hM h1)).symm).trans (comp_idt hM (nil_hom hM hA))).symm
  · have hi' := idt_hom hM hLA
    refine (idt_comp hM (cons_hom hM hA)).trans ((comp_idt hM (cons_hom hM hA)).symm.trans ?_)
    refine (eval_op₂_congr 3 rfl (pair_fst_snd hM hA hLA).symm).trans ?_
    refine Eq.trans ?_ (eval_op₂_congr 3 (eval_op₂_congr 3 rfl (eval_op₂_congr 9 rfl
      (idt_comp hM hsL))) rfl)
    refine Eq.trans ?_ (comp_pair_proj hM (cons_hom hM hA) hi hi' hfA
      (comp_hom hM hsL hi')).symm
    exact eval_op₂_congr 3 rfl (eval_op₂_congr 9 (idt_comp hM hfA).symm
      ((idt_comp hM hsL).symm.trans (idt_comp hM (comp_hom hM hsL hi')).symm))

/-- The exchange of a product's factors after a pairing is the exchanged pairing. -/
theorem swap_pair {f g X A B : Tree} (hf : Hom M ρ f X A) (hg : Hom M ρ g X B) :
    eval M ρ (comp (pair (snd A B) (fst A B)) (pair f g)) = eval M ρ (pair g f) :=
  (pair_comp hM (snd_hom hM hf.isObj_cod hg.isObj_cod) (fst_hom hM hf.isObj_cod hg.isObj_cod)
    (pair_hom hM hf hg)).trans (eval_op₂_congr 9 (snd_pair hM hf hg) (fst_pair hM hf hg))

/-- Two arrows from a product that agree after the exchange of its factors are equal. -/
theorem eq_of_comp_swap {F G A B C : Tree} (hA : IsObj M ρ A) (hB : IsObj M ρ B)
    (hF : Hom M ρ F (prod A B) C) (hG : Hom M ρ G (prod A B) C)
    (h : eval M ρ (comp F (pair (snd B A) (fst B A))) =
      eval M ρ (comp G (pair (snd B A) (fst B A)))) :
    eval M ρ F = eval M ρ G := by
  have hsw := pair_hom hM (snd_hom hM hB hA) (fst_hom hM hB hA)
  have hsw' := pair_hom hM (snd_hom hM hA hB) (fst_hom hM hA hB)
  have hid := (swap_pair hM (snd_hom hM hA hB) (fst_hom hM hA hB)).trans (pair_fst_snd hM hA hB)
  have key : ∀ {H : Tree}, Hom M ρ H (prod A B) C → eval M ρ H =
      eval M ρ (comp (comp H (pair (snd B A) (fst B A))) (pair (snd A B) (fst A B))) :=
    fun hH ↦ (comp_idt hM hH).symm.trans
      ((eval_op₂_congr 3 rfl hid.symm).trans (comp_assoc hM hsw' hsw hH))
  exact (key hF).trans ((eval_op₂_congr 3 h rfl).trans (key hG).symm)

/-- The currying, over the second factor, of an arrow from a product with its factors exchanged,
after an arrow into the first factor, is the currying of the arrow after the pairing of the
second factor with the arrow. -/
theorem curry_swap_comp {F h P D Y C : Tree} (hP : IsObj M ρ P) (hF : Hom M ρ F (prod P D) C)
    (hh : Hom M ρ h Y D) :
    eval M ρ (comp (curry D P (comp F (pair (snd D P) (fst D P)))) h) =
      eval M ρ (curry Y P (comp F (pair (snd Y P) (comp h (fst Y P))))) := by
  have hD := hh.isObj_cod
  have hY := hh.isObj_dom
  have hsw := pair_hom hM (snd_hom hM hD hP) (fst_hom hM hD hP)
  have hhf := comp_hom hM (fst_hom hM hY hP) hh
  have hk := pair_hom hM hhf (snd_hom hM hY hP)
  refine (curry_comp hM hP (comp_hom hM hsw hF) hh).trans (eval_op₃_congr 24 rfl rfl ?_)
  exact (comp_assoc hM hk hsw hF).symm.trans
    (eval_op₂_congr 3 rfl (swap_pair hM hhf (snd_hom hM hY hP)))

/-- Two arrows from a product whose curryings over its first factor, with the factors exchanged,
are equal are equal. -/
theorem eq_of_curry_swap {F G P D C : Tree} (hP : IsObj M ρ P) (hD : IsObj M ρ D)
    (hF : Hom M ρ F (prod P D) C) (hG : Hom M ρ G (prod P D) C)
    (h : eval M ρ (curry D P (comp F (pair (snd D P) (fst D P)))) =
      eval M ρ (curry D P (comp G (pair (snd D P) (fst D P))))) :
    eval M ρ F = eval M ρ G := by
  have hsw := pair_hom hM (snd_hom hM hD hP) (fst_hom hM hD hP)
  refine eq_of_comp_swap hM hP hD hF hG ?_
  exact (ev_curry hM hD hP (comp_hom hM hsw hF)).symm.trans
    ((eval_op₂_congr 3 rfl (eval_op₂_congr 9 (eval_op₂_congr 3 h rfl) rfl)).trans
      (ev_curry hM hD hP (comp_hom hM hsw hG)))

/-- The uniqueness of the fold of the natural numbers object with a parameter: two arrows from
the product of an object of parameters with the natural numbers object that agree at zero, and
each of which is at a successor the step after the parameter paired with its value, are
equal. -/
theorem natRec_param_unique {F G S P C : Tree} (hP : IsObj M ρ P)
    (hF : Hom M ρ F (prod P nat) C) (hG : Hom M ρ G (prod P nat) C)
    (hS : Hom M ρ S (prod P C) C)
    (h₀ : eval M ρ (comp F (pair (idt P) (comp zeroN (bang P)))) =
      eval M ρ (comp G (pair (idt P) (comp zeroN (bang P)))))
    (hF₁ : eval M ρ (comp F (pair (fst P nat) (comp succ (snd P nat)))) =
      eval M ρ (comp S (pair (fst P nat) F)))
    (hG₁ : eval M ρ (comp G (pair (fst P nat) (comp succ (snd P nat)))) =
      eval M ρ (comp S (pair (fst P nat) G))) :
    eval M ρ F = eval M ρ G := by
  have hN := isObj_nat (ρ := ρ) hM
  have h1 := isObj_one (ρ := ρ) hM
  have hC := hF.isObj_cod
  have hE := isObj_exp hM hP hC
  have hs1 := snd_hom hM h1 hP
  have hfN := fst_hom hM hN hP
  have hsN := snd_hom hM hN hP
  have hfP := fst_hom hM hP hN
  have hsP := snd_hom hM hP hN
  have hsw := pair_hom hM hsN hfN
  have hzb := comp_hom hM (bang_hom hM hP) (zeroN_hom hM)
  have hz0 := pair_hom hM (idt_hom hM hP) hzb
  have hsc := comp_hom hM hsP (succ_hom hM)
  have hstep := pair_hom hM hfP hsc
  have hsE := snd_hom hM hE hP
  have hev := ev_hom hM hP hC
  have hSb := comp_hom hM (pair_hom hM hsE hev) hS
  have hZ := curry_hom hM h1 hP (comp_hom hM hs1 (comp_hom hM hz0 hF))
  have hStep := curry_hom hM hE hP hSb
  -- the pairing of the successor with the parameter is the step after the exchange
  have e₁ : eval M ρ (pair (snd nat P) (comp succ (fst nat P))) =
      eval M ρ (comp (pair (fst P nat) (comp succ (snd P nat))) (pair (snd nat P) (fst nat P))) :=
    ((pair_comp hM hfP hsc hsw).trans (eval_op₂_congr 9 (fst_pair hM hsN hfN)
      ((comp_assoc hM hsw hsP (succ_hom hM)).symm.trans
        (eval_op₂_congr 3 rfl (snd_pair hM hsN hfN))))).symm
  -- the pairing of zero with the parameter is the start after the second projection
  have e₀ : eval M ρ (pair (snd one P) (comp zeroN (fst one P))) =
      eval M ρ (comp (pair (idt P) (comp zeroN (bang P))) (snd one P)) :=
    ((pair_comp hM (idt_hom hM hP) hzb hs1).trans (eval_op₂_congr 9 (idt_comp hM hs1)
      ((comp_assoc hM hs1 (bang_hom hM hP) (zeroN_hom hM)).symm.trans (eval_op₂_congr 3 rfl
        ((comp_bang hM hs1).trans (bang_unique hM (fst_hom hM h1 hP)).symm))))).symm
  -- the currying of each arrow is the fold
  have key : ∀ {H : Tree}, Hom M ρ H (prod P nat) C →
      eval M ρ (comp H (pair (idt P) (comp zeroN (bang P)))) =
        eval M ρ (comp F (pair (idt P) (comp zeroN (bang P)))) →
      eval M ρ (comp H (pair (fst P nat) (comp succ (snd P nat)))) =
        eval M ρ (comp S (pair (fst P nat) H)) →
      eval M ρ (curry nat P (comp H (pair (snd nat P) (fst nat P)))) =
        eval M ρ (natRec (curry one P (comp (comp F (pair (idt P) (comp zeroN (bang P))))
          (snd one P))) (curry (exp P C) P (comp S (pair (snd (exp P C) P) (ev P C))))) := by
    intro H hH hH₀ hH₁
    have hHsw := comp_hom hM hsw hH
    have hc := curry_hom hM hN hP hHsw
    have hcf := comp_hom hM hfN hc
    have hk := pair_hom hM hcf hsN
    refine natRec_unique hM hZ hStep hc ?_ ?_
    · refine (curry_swap_comp hM hP hH (zeroN_hom hM)).trans (eval_op₃_congr 24 rfl rfl ?_)
      exact (eval_op₂_congr 3 rfl e₀).trans
        ((comp_assoc hM hs1 hz0 hH).trans (eval_op₂_congr 3 hH₀ rfl))
    · refine (curry_swap_comp hM hP hH (succ_hom hM)).trans
        (Eq.trans ?_ (curry_comp hM hP hSb hc).symm)
      refine eval_op₃_congr 24 rfl rfl ?_
      refine ((eval_op₂_congr 3 rfl e₁).trans ((comp_assoc hM hsw hstep hH).trans
        ((eval_op₂_congr 3 hH₁ rfl).trans ((comp_assoc hM hsw (pair_hom hM hfP hH) hS).symm.trans
          (eval_op₂_congr 3 rfl ((pair_comp hM hfP hH hsw).trans
            (eval_op₂_congr 9 (fst_pair hM hsN hfN) rfl))))))).trans ?_
      exact Eq.symm ((comp_assoc hM hk (pair_hom hM hsE hev) hS).symm.trans
        (eval_op₂_congr 3 rfl ((pair_comp hM hsE hev hk).trans
          (eval_op₂_congr 9 (snd_pair hM hcf hsN) (ev_curry hM hN hP hHsw)))))
  exact eq_of_curry_swap hM hP hN hF hG ((key hF rfl hF₁).trans (key hG h₀.symm hG₁).symm)

/-- The uniqueness of the fold of a list object with a parameter: two arrows from the product of
an object of parameters with the list object that agree at the empty list, and each of which is
at a construction the step after the parameter and the element paired with its value at the
tail, are equal. -/
theorem listRec_param_unique {F G S P A C : Tree} (hP : IsObj M ρ P) (hA : IsObj M ρ A)
    (hF : Hom M ρ F (prod P (list A)) C) (hG : Hom M ρ G (prod P (list A)) C)
    (hS : Hom M ρ S (prod (prod P A) C) C)
    (h₀ : eval M ρ (comp F (pair (idt P) (comp (nil A) (bang P)))) =
      eval M ρ (comp G (pair (idt P) (comp (nil A) (bang P)))))
    (hF₁ : eval M ρ (comp F (pair (comp (fst P A) (fst (prod P A) (list A)))
        (comp (cons A) (pair (comp (snd P A) (fst (prod P A) (list A)))
          (snd (prod P A) (list A)))))) =
      eval M ρ (comp S (pair (fst (prod P A) (list A))
        (comp F (pair (comp (fst P A) (fst (prod P A) (list A))) (snd (prod P A) (list A)))))))
    (hG₁ : eval M ρ (comp G (pair (comp (fst P A) (fst (prod P A) (list A)))
        (comp (cons A) (pair (comp (snd P A) (fst (prod P A) (list A)))
          (snd (prod P A) (list A)))))) =
      eval M ρ (comp S (pair (fst (prod P A) (list A))
        (comp G (pair (comp (fst P A) (fst (prod P A) (list A))) (snd (prod P A) (list A))))))) :
    eval M ρ F = eval M ρ G := by
  have h1 := isObj_one (ρ := ρ) hM
  have hL := isObj_list hM hA
  have hC := hF.isObj_cod
  have hE := isObj_exp hM hP hC
  have hPA := isObj_prod hM hP hA
  have hR := isObj_prod hM hA hL
  have hAE := isObj_prod hM hA hE
  have hs1 := snd_hom hM h1 hP
  have hfPA := fst_hom hM hP hA
  have hsPA := snd_hom hM hP hA
  have hfQ := fst_hom hM hPA hL
  have hsQ := snd_hom hM hPA hL
  have hfAL := fst_hom hM hA hL
  have hsAL := snd_hom hM hA hL
  have hfRP := fst_hom hM hR hP
  have hsRP := snd_hom hM hR hP
  have hfLP := fst_hom hM hL hP
  have hsLP := snd_hom hM hL hP
  have hswL := pair_hom hM hsLP hfLP
  have hfE := fst_hom hM hAE hP
  have hsE := snd_hom hM hAE hP
  have hfAE := fst_hom hM hA hE
  have hsAE := snd_hom hM hA hE
  have hev := ev_hom hM hP hC
  have hcons := cons_hom hM hA
  have hnb := comp_hom hM (bang_hom hM hP) (nil_hom hM hA)
  have hn0 := pair_hom hM (idt_hom hM hP) hnb
  have hq := pair_hom hM (comp_hom hM hfQ hsPA) hsQ
  have hk₁ := pair_hom hM (comp_hom hM hfQ hfPA) (comp_hom hM hq hcons)
  have hk₂ := pair_hom hM (comp_hom hM hfQ hfPA) hsQ
  have hpe := pair_hom hM (comp_hom hM hfE hsAE) hsE
  have hbody := pair_hom hM (pair_hom hM hsE (comp_hom hM hfE hfAE)) (comp_hom hM hpe hev)
  have hSb := comp_hom hM hbody hS
  have hZ := curry_hom hM h1 hP (comp_hom hM hs1 (comp_hom hM hn0 hF))
  have hStep := curry_hom hM hAE hP hSb
  have hfr := pair_hom hM hsRP (comp_hom hM hfRP hfAL)
  have hr := pair_hom hM hfr (comp_hom hM hfRP hsAL)
  -- the arrow into the step's domain from the curried domain, and its components
  have fr := fst_pair hM hfr (comp_hom hM hfRP hsAL)
  have sr := snd_pair hM hfr (comp_hom hM hfRP hsAL)
  have pr : eval M ρ (comp (comp (fst P A) (fst (prod P A) (list A)))
      (pair (pair (snd (prod A (list A)) P) (comp (fst A (list A)) (fst (prod A (list A)) P)))
        (comp (snd A (list A)) (fst (prod A (list A)) P)))) =
      eval M ρ (snd (prod A (list A)) P) :=
    (comp_assoc hM hr hfQ hfPA).symm.trans
      ((eval_op₂_congr 3 rfl fr).trans (fst_pair hM hsRP (comp_hom hM hfRP hfAL)))
  have er : eval M ρ (comp (comp (snd P A) (fst (prod P A) (list A)))
      (pair (pair (snd (prod A (list A)) P) (comp (fst A (list A)) (fst (prod A (list A)) P)))
        (comp (snd A (list A)) (fst (prod A (list A)) P)))) =
      eval M ρ (comp (fst A (list A)) (fst (prod A (list A)) P)) :=
    (comp_assoc hM hr hfQ hsPA).symm.trans
      ((eval_op₂_congr 3 rfl fr).trans (snd_pair hM hsRP (comp_hom hM hfRP hfAL)))
  have k₁r := (pair_comp hM (comp_hom hM hfQ hfPA) (comp_hom hM hq hcons) hr).trans
    (eval_op₂_congr 9 pr ((comp_assoc hM hr hq hcons).symm.trans (eval_op₂_congr 3 rfl
      ((pair_comp hM (comp_hom hM hfQ hsPA) hsQ hr).trans
        ((eval_op₂_congr 9 er sr).trans (pair_eta hM hA hL hfRP))))))
  have k₂r := (pair_comp hM (comp_hom hM hfQ hfPA) hsQ hr).trans (eval_op₂_congr 9 pr sr)
  -- the pairing of the empty list with the parameter is the start after the second projection
  have e₀ : eval M ρ (pair (snd one P) (comp (nil A) (fst one P))) =
      eval M ρ (comp (pair (idt P) (comp (nil A) (bang P))) (snd one P)) :=
    ((pair_comp hM (idt_hom hM hP) hnb hs1).trans (eval_op₂_congr 9 (idt_comp hM hs1)
      ((comp_assoc hM hs1 (bang_hom hM hP) (nil_hom hM hA)).symm.trans (eval_op₂_congr 3 rfl
        ((comp_bang hM hs1).trans (bang_unique hM (fst_hom hM h1 hP)).symm))))).symm
  -- the currying of each arrow is the fold
  have key : ∀ {H : Tree}, Hom M ρ H (prod P (list A)) C →
      eval M ρ (comp H (pair (idt P) (comp (nil A) (bang P)))) =
        eval M ρ (comp F (pair (idt P) (comp (nil A) (bang P)))) →
      eval M ρ (comp H (pair (comp (fst P A) (fst (prod P A) (list A)))
          (comp (cons A) (pair (comp (snd P A) (fst (prod P A) (list A)))
            (snd (prod P A) (list A)))))) =
        eval M ρ (comp S (pair (fst (prod P A) (list A))
          (comp H (pair (comp (fst P A) (fst (prod P A) (list A)))
            (snd (prod P A) (list A)))))) →
      eval M ρ (curry (list A) P (comp H (pair (snd (list A) P) (fst (list A) P)))) =
        eval M ρ (listRec A (curry one P (comp (comp F (pair (idt P) (comp (nil A) (bang P))))
          (snd one P))) (curry (prod A (exp P C)) P (comp S
            (pair (pair (snd (prod A (exp P C)) P)
                (comp (fst A (exp P C)) (fst (prod A (exp P C)) P)))
              (comp (ev P C) (pair (comp (snd A (exp P C)) (fst (prod A (exp P C)) P))
                (snd (prod A (exp P C)) P))))))) := by
    intro H hH hH₀ hH₁
    have hHsw := comp_hom hM hswL hH
    have hc := curry_hom hM hL hP hHsw
    have hm := pair_hom hM hfAL (comp_hom hM hsAL hc)
    have hn := pair_hom hM (comp_hom hM hfRP hm) hsRP
    have ht := pair_hom hM (comp_hom hM hfRP hsAL) hsRP
    have hpc := pair_hom hM (comp_hom hM hfLP hc) hsLP
    refine listRec_unique hM hA hZ hStep hc ?_ ?_
    · refine (curry_swap_comp hM hP hH (nil_hom hM hA)).trans (eval_op₃_congr 24 rfl rfl ?_)
      exact (eval_op₂_congr 3 rfl e₀).trans
        ((comp_assoc hM hs1 hn0 hH).trans (eval_op₂_congr 3 hH₀ rfl))
    · refine (curry_swap_comp hM hP hH hcons).trans
        (Eq.trans ?_ (curry_comp hM hP hSb hm).symm)
      refine eval_op₃_congr 24 rfl rfl ?_
      -- the step's equation, after the arrow into its domain
      refine ((eval_op₂_congr 3 rfl k₁r.symm).trans ((comp_assoc hM hr hk₁ hH).trans
        ((eval_op₂_congr 3 hH₁ rfl).trans
          ((comp_assoc hM hr (pair_hom hM hfQ (comp_hom hM hk₂ hH)) hS).symm.trans
            (eval_op₂_congr 3 rfl ((pair_comp hM hfQ (comp_hom hM hk₂ hH) hr).trans
              (eval_op₂_congr 9 fr ((comp_assoc hM hr hk₂ hH).symm.trans
                (eval_op₂_congr 3 rfl k₂r))))))))).trans ?_
      -- the curried step, after the curried arrow paired with the element
      have f1n := fst_pair hM (comp_hom hM hfRP hm) hsRP
      have s1n := snd_pair hM (comp_hom hM hfRP hm) hsRP
      have an := (pair_comp hM hsE (comp_hom hM hfE hfAE) hn).trans (eval_op₂_congr 9 s1n
        ((comp_assoc hM hn hfE hfAE).symm.trans ((eval_op₂_congr 3 rfl f1n).trans
          ((comp_assoc hM hfRP hm hfAE).trans
            (eval_op₂_congr 3 (fst_pair hM hfAL (comp_hom hM hsAL hc)) rfl)))))
      have hx : eval M ρ (comp (pair (comp (snd A (exp P C)) (fst (prod A (exp P C)) P))
            (snd (prod A (exp P C)) P))
          (pair (comp (pair (fst A (list A)) (comp (curry (list A) P
              (comp H (pair (snd (list A) P) (fst (list A) P)))) (snd A (list A))))
            (fst (prod A (list A)) P)) (snd (prod A (list A)) P))) =
          eval M ρ (comp (pair (comp (curry (list A) P
              (comp H (pair (snd (list A) P) (fst (list A) P)))) (fst (list A) P))
            (snd (list A) P))
            (pair (comp (snd A (list A)) (fst (prod A (list A)) P)) (snd (prod A (list A)) P))) :=
        ((pair_comp hM (comp_hom hM hfE hsAE) hsE hn).trans (eval_op₂_congr 9
          ((comp_assoc hM hn hfE hsAE).symm.trans ((eval_op₂_congr 3 rfl f1n).trans
            ((comp_assoc hM hfRP hm hsAE).trans ((eval_op₂_congr 3
              (snd_pair hM hfAL (comp_hom hM hsAL hc)) rfl).trans
                (comp_assoc hM hfRP hsAL hc).symm))))
          s1n)).trans ((pair_comp hM (comp_hom hM hfLP hc) hsLP ht).trans (eval_op₂_congr 9
            ((comp_assoc hM ht hfLP hc).symm.trans (eval_op₂_congr 3 rfl
              (fst_pair hM (comp_hom hM hfRP hsAL) hsRP)))
            (snd_pair hM (comp_hom hM hfRP hsAL) hsRP))).symm
      have evn := (comp_assoc hM hn hpe hev).symm.trans ((eval_op₂_congr 3 rfl hx).trans
        ((comp_assoc hM ht hpc hev).trans ((eval_op₂_congr 3 (ev_curry hM hL hP hHsw) rfl).trans
          ((comp_assoc hM ht hswL hH).symm.trans (eval_op₂_congr 3 rfl
            (swap_pair hM (comp_hom hM hfRP hsAL) hsRP))))))
      exact Eq.symm ((comp_assoc hM hn hbody hS).symm.trans (eval_op₂_congr 3 rfl
        ((pair_comp hM (pair_hom hM hsE (comp_hom hM hfE hfAE)) (comp_hom hM hpe hev) hn).trans
          (eval_op₂_congr 9 an evn))))
  exact eq_of_curry_swap hM hP hL hF hG ((key hF rfl hF₁).trans (key hG h₀.symm hG₁).symm)

/-- Evaluation after the pairing of a currying after an arrow with another arrow is the curried
arrow after their pairing. -/
theorem ev_curry_pair {T h k X A B Y : Tree} (hX : IsObj M ρ X) (hA : IsObj M ρ A)
    (hT : Hom M ρ T (prod X A) B) (hh : Hom M ρ h Y X) (hk : Hom M ρ k Y A) :
    eval M ρ (comp (ev A B) (pair (comp (curry X A T) h) k)) =
      eval M ρ (comp T (pair h k)) := by
  have hc := curry_hom hM hX hA hT
  have hfX := fst_hom hM hX hA
  have hsX := snd_hom hM hX hA
  have hP := pair_hom hM (comp_hom hM hfX hc) hsX
  have hhk := pair_hom hM hh hk
  have e₁ : eval M ρ (pair (comp (curry X A T) h) k) =
      eval M ρ (comp (pair (comp (curry X A T) (fst X A)) (snd X A)) (pair h k)) :=
    ((pair_comp hM (comp_hom hM hfX hc) hsX hhk).trans (eval_op₂_congr 9
      ((comp_assoc hM hhk hfX hc).symm.trans (eval_op₂_congr 3 rfl (fst_pair hM hh hk)))
      (snd_pair hM hh hk))).symm
  exact (eval_op₂_congr 3 rfl e₁).trans ((comp_assoc hM hhk hP (ev_hom hM hA hT.isObj_cod)).trans
    (eval_op₂_congr 3 (ev_curry hM hX hA hT) rfl))

/-- The fold of the natural numbers object with a parameter is an arrow from the product of the
object of parameters with the natural numbers object that is its start at zero and, at a
successor, its step after the parameter paired with its value (\[EscardoSimpson2025\],
Proposition 2.3). -/
theorem natRecP_spec {z S P C : Tree} (hP : IsObj M ρ P) (hz : Hom M ρ z P C)
    (hS : Hom M ρ S (prod P C) C) :
    Hom M ρ (natRecP P C z S) (prod P nat) C ∧
      eval M ρ (comp (natRecP P C z S) (pair (idt P) (comp zeroN (bang P)))) = eval M ρ z ∧
      eval M ρ (comp (natRecP P C z S) (pair (fst P nat) (comp succ (snd P nat)))) =
        eval M ρ (comp S (pair (fst P nat) (natRecP P C z S))) := by
  unfold natRecP
  have hN := isObj_nat (ρ := ρ) hM
  have h1 := isObj_one (ρ := ρ) hM
  have hC := hz.isObj_cod
  have hE := isObj_exp hM hP hC
  have hs1 := snd_hom hM h1 hP
  have hsE := snd_hom hM hE hP
  have hev := ev_hom hM hP hC
  have hZ := curry_hom hM h1 hP (comp_hom hM hs1 hz)
  have hT := comp_hom hM (pair_hom hM hsE hev) hS
  have hStepC := curry_hom hM hE hP hT
  have hR := natRec_hom hM hZ hStepC
  have hfN := fst_hom hM hP hN
  have hsN := snd_hom hM hP hN
  have hRs := comp_hom hM hsN hR
  have hq := pair_hom hM hRs hfN
  refine ⟨comp_hom hM hq hev, ?_, ?_⟩
  · -- at zero, the curried start's evaluation at the parameter
    have hb := bang_hom hM hP
    have hzb := comp_hom hM hb (zeroN_hom hM)
    have hid := idt_hom hM hP
    have hz0 := pair_hom hM hid hzb
    have e₁ : eval M ρ (comp (pair (comp (natRec (curry one P (comp z (snd one P)))
        (curry (exp P C) P (comp S (pair (snd (exp P C) P) (ev P C))))) (snd P nat))
        (fst P nat)) (pair (idt P) (comp zeroN (bang P)))) = eval M ρ
        (pair (comp (curry one P (comp z (snd one P))) (bang P)) (idt P)) :=
      (pair_comp hM hRs hfN hz0).trans (eval_op₂_congr 9
        ((comp_assoc hM hz0 hsN hR).symm.trans ((eval_op₂_congr 3 rfl (snd_pair hM hid hzb)).trans
          ((comp_assoc hM hb (zeroN_hom hM) hR).trans
            (eval_op₂_congr 3 (natRec_zero hM hZ hStepC) rfl))))
        (fst_pair hM hid hzb))
    exact (comp_assoc hM hz0 hq hev).symm.trans ((eval_op₂_congr 3 rfl e₁).trans
      ((ev_curry_pair hM h1 hP (comp_hom hM hs1 hz) hb hid).trans
        ((comp_assoc hM (pair_hom hM hb hid) hs1 hz).symm.trans
          ((eval_op₂_congr 3 rfl (snd_pair hM hb hid)).trans (comp_idt hM hz)))))
  · -- at a successor, the curried step's evaluation at the parameter and the value
    have hsc := comp_hom hM hsN (succ_hom hM)
    have hk₁ := pair_hom hM hfN hsc
    have e₁ : eval M ρ (comp (pair (comp (natRec (curry one P (comp z (snd one P)))
        (curry (exp P C) P (comp S (pair (snd (exp P C) P) (ev P C))))) (snd P nat))
        (fst P nat)) (pair (fst P nat) (comp succ (snd P nat)))) = eval M ρ
        (pair (comp (curry (exp P C) P (comp S (pair (snd (exp P C) P) (ev P C))))
          (comp (natRec (curry one P (comp z (snd one P)))
            (curry (exp P C) P (comp S (pair (snd (exp P C) P) (ev P C))))) (snd P nat)))
          (fst P nat)) :=
      (pair_comp hM hRs hfN hk₁).trans (eval_op₂_congr 9
        ((comp_assoc hM hk₁ hsN hR).symm.trans ((eval_op₂_congr 3 rfl (snd_pair hM hfN hsc)).trans
          ((comp_assoc hM hsN (succ_hom hM) hR).trans ((eval_op₂_congr 3
            (natRec_succ hM hZ hStepC) rfl).trans (comp_assoc hM hsN hR hStepC).symm))))
        (fst_pair hM hfN hsc))
    exact (comp_assoc hM hk₁ hq hev).symm.trans ((eval_op₂_congr 3 rfl e₁).trans
      ((ev_curry_pair hM hE hP hT hRs hfN).trans
        ((comp_assoc hM hq (pair_hom hM hsE hev) hS).symm.trans (eval_op₂_congr 3 rfl
          ((pair_comp hM hsE hev hq).trans (eval_op₂_congr 9 (snd_pair hM hRs hfN) rfl))))))

/-- The fold of a list object with a parameter is an arrow from the product of the object of
parameters with the list object that is its start at the empty list and, at a construction, its
step after the parameter and the element paired with its value at the tail. -/
theorem listRecP_spec {z S P A C : Tree} (hP : IsObj M ρ P) (hA : IsObj M ρ A)
    (hz : Hom M ρ z P C) (hS : Hom M ρ S (prod (prod P A) C) C) :
    Hom M ρ (listRecP P A C z S) (prod P (list A)) C ∧
      eval M ρ (comp (listRecP P A C z S) (pair (idt P) (comp (nil A) (bang P)))) =
        eval M ρ z ∧
      eval M ρ (comp (listRecP P A C z S) (pair (comp (fst P A) (fst (prod P A) (list A)))
          (comp (cons A) (pair (comp (snd P A) (fst (prod P A) (list A)))
            (snd (prod P A) (list A)))))) =
        eval M ρ (comp S (pair (fst (prod P A) (list A))
          (comp (listRecP P A C z S) (pair (comp (fst P A) (fst (prod P A) (list A)))
            (snd (prod P A) (list A)))))) := by
  unfold listRecP
  have h1 := isObj_one (ρ := ρ) hM
  have hL := isObj_list hM hA
  have hC := hz.isObj_cod
  have hE := isObj_exp hM hP hC
  have hPA := isObj_prod hM hP hA
  have hAE := isObj_prod hM hA hE
  have hAL := isObj_prod hM hA hL
  have hs1 := snd_hom hM h1 hP
  have hev := ev_hom hM hP hC
  have hfE := fst_hom hM hAE hP
  have hsE := snd_hom hM hAE hP
  have hfAE := fst_hom hM hA hE
  have hsAE := snd_hom hM hA hE
  have hpe := pair_hom hM (comp_hom hM hfE hsAE) hsE
  have hbody := pair_hom hM (pair_hom hM hsE (comp_hom hM hfE hfAE)) (comp_hom hM hpe hev)
  have hT := comp_hom hM hbody hS
  have hZ := curry_hom hM h1 hP (comp_hom hM hs1 hz)
  have hStepC := curry_hom hM hAE hP hT
  have hR := listRec_hom hM hA hZ hStepC
  have hfL := fst_hom hM hP hL
  have hsL := snd_hom hM hP hL
  have hRs := comp_hom hM hsL hR
  have hq := pair_hom hM hRs hfL
  refine ⟨comp_hom hM hq hev, ?_, ?_⟩
  · -- at the empty list, the curried start's evaluation at the parameter
    have hb := bang_hom hM hP
    have hnb := comp_hom hM hb (nil_hom hM hA)
    have hid := idt_hom hM hP
    have hn0 := pair_hom hM hid hnb
    have e₁ : eval M ρ (comp (pair (comp (listRec A (curry one P (comp z (snd one P)))
        (curry (prod A (exp P C)) P (comp S
          (pair (pair (snd (prod A (exp P C)) P)
              (comp (fst A (exp P C)) (fst (prod A (exp P C)) P)))
            (comp (ev P C) (pair (comp (snd A (exp P C)) (fst (prod A (exp P C)) P))
              (snd (prod A (exp P C)) P))))))) (snd P (list A)))
        (fst P (list A))) (pair (idt P) (comp (nil A) (bang P)))) = eval M ρ
        (pair (comp (curry one P (comp z (snd one P))) (bang P)) (idt P)) :=
      (pair_comp hM hRs hfL hn0).trans (eval_op₂_congr 9
        ((comp_assoc hM hn0 hsL hR).symm.trans ((eval_op₂_congr 3 rfl (snd_pair hM hid hnb)).trans
          ((comp_assoc hM hb (nil_hom hM hA) hR).trans
            (eval_op₂_congr 3 (listRec_nil hM hA hZ hStepC) rfl))))
        (fst_pair hM hid hnb))
    exact (comp_assoc hM hn0 hq hev).symm.trans ((eval_op₂_congr 3 rfl e₁).trans
      ((ev_curry_pair hM h1 hP (comp_hom hM hs1 hz) hb hid).trans
        ((comp_assoc hM (pair_hom hM hb hid) hs1 hz).symm.trans
          ((eval_op₂_congr 3 rfl (snd_pair hM hb hid)).trans (comp_idt hM hz)))))
  · -- at a construction, the curried step's evaluation at the parameter
    have hfQ := fst_hom hM hPA hL
    have hsQ := snd_hom hM hPA hL
    have hfPA := fst_hom hM hP hA
    have hsPA := snd_hom hM hP hA
    have hfAL := fst_hom hM hA hL
    have hsAL := snd_hom hM hA hL
    have hff := comp_hom hM hfQ hfPA
    have hsf := comp_hom hM hfQ hsPA
    have hel := pair_hom hM hsf hsQ
    have hcel := comp_hom hM hel (cons_hom hM hA)
    have hk₁ := pair_hom hM hff hcel
    have hk₂ := pair_hom hM hff hsQ
    have hRsQ := comp_hom hM hsQ hR
    have hn := pair_hom hM hsf hRsQ
    have hpm := pair_hom hM hfAL (comp_hom hM hsAL hR)
    -- the fold at a construction is the curried step at the element and the tail's fold
    have eR : eval M ρ (comp (listRec A (curry one P (comp z (snd one P)))
          (curry (prod A (exp P C)) P (comp S
            (pair (pair (snd (prod A (exp P C)) P)
                (comp (fst A (exp P C)) (fst (prod A (exp P C)) P)))
              (comp (ev P C) (pair (comp (snd A (exp P C)) (fst (prod A (exp P C)) P))
                (snd (prod A (exp P C)) P)))))))
        (comp (cons A) (pair (comp (snd P A) (fst (prod P A) (list A)))
          (snd (prod P A) (list A))))) = eval M ρ
        (comp (curry (prod A (exp P C)) P (comp S
            (pair (pair (snd (prod A (exp P C)) P)
                (comp (fst A (exp P C)) (fst (prod A (exp P C)) P)))
              (comp (ev P C) (pair (comp (snd A (exp P C)) (fst (prod A (exp P C)) P))
                (snd (prod A (exp P C)) P))))))
          (pair (comp (snd P A) (fst (prod P A) (list A)))
            (comp (listRec A (curry one P (comp z (snd one P)))
              (curry (prod A (exp P C)) P (comp S
                (pair (pair (snd (prod A (exp P C)) P)
                    (comp (fst A (exp P C)) (fst (prod A (exp P C)) P)))
                  (comp (ev P C) (pair (comp (snd A (exp P C)) (fst (prod A (exp P C)) P))
                    (snd (prod A (exp P C)) P)))))))
              (snd (prod P A) (list A))))) :=
      (comp_assoc hM hel (cons_hom hM hA) hR).trans ((eval_op₂_congr 3
        (listRec_cons hM hA hZ hStepC) rfl).trans ((comp_assoc hM hel hpm hStepC).symm.trans
          (eval_op₂_congr 3 rfl ((pair_comp hM hfAL (comp_hom hM hsAL hR) hel).trans
            (eval_op₂_congr 9 (fst_pair hM hsf hsQ) ((comp_assoc hM hel hsAL hR).symm.trans
              (eval_op₂_congr 3 rfl (snd_pair hM hsf hsQ))))))))
    -- the arrow at the tail
    have eT : eval M ρ (comp (comp (ev P C) (pair (comp (listRec A
          (curry one P (comp z (snd one P)))
          (curry (prod A (exp P C)) P (comp S
            (pair (pair (snd (prod A (exp P C)) P)
                (comp (fst A (exp P C)) (fst (prod A (exp P C)) P)))
              (comp (ev P C) (pair (comp (snd A (exp P C)) (fst (prod A (exp P C)) P))
                (snd (prod A (exp P C)) P))))))) (snd P (list A))) (fst P (list A))))
        (pair (comp (fst P A) (fst (prod P A) (list A))) (snd (prod P A) (list A)))) =
        eval M ρ (comp (ev P C) (pair (comp (listRec A (curry one P (comp z (snd one P)))
          (curry (prod A (exp P C)) P (comp S
            (pair (pair (snd (prod A (exp P C)) P)
                (comp (fst A (exp P C)) (fst (prod A (exp P C)) P)))
              (comp (ev P C) (pair (comp (snd A (exp P C)) (fst (prod A (exp P C)) P))
                (snd (prod A (exp P C)) P))))))) (snd (prod P A) (list A)))
          (comp (fst P A) (fst (prod P A) (list A))))) :=
      (comp_assoc hM hk₂ hq hev).symm.trans (eval_op₂_congr 3 rfl
        ((pair_comp hM hRs hfL hk₂).trans (eval_op₂_congr 9
          ((comp_assoc hM hk₂ hsL hR).symm.trans (eval_op₂_congr 3 rfl (snd_pair hM hff hsQ)))
          (fst_pair hM hff hsQ))))
    -- the step's body after the element, the tail's fold and the parameter
    have hm := pair_hom hM hn hff
    have eB : eval M ρ (comp (pair (pair (snd (prod A (exp P C)) P)
          (comp (fst A (exp P C)) (fst (prod A (exp P C)) P)))
        (comp (ev P C) (pair (comp (snd A (exp P C)) (fst (prod A (exp P C)) P))
          (snd (prod A (exp P C)) P))))
        (pair (pair (comp (snd P A) (fst (prod P A) (list A)))
          (comp (listRec A (curry one P (comp z (snd one P)))
            (curry (prod A (exp P C)) P (comp S
              (pair (pair (snd (prod A (exp P C)) P)
                  (comp (fst A (exp P C)) (fst (prod A (exp P C)) P)))
                (comp (ev P C) (pair (comp (snd A (exp P C)) (fst (prod A (exp P C)) P))
                  (snd (prod A (exp P C)) P)))))))
            (snd (prod P A) (list A))))
          (comp (fst P A) (fst (prod P A) (list A))))) =
        eval M ρ (pair (fst (prod P A) (list A))
          (comp (ev P C) (pair (comp (listRec A (curry one P (comp z (snd one P)))
            (curry (prod A (exp P C)) P (comp S
              (pair (pair (snd (prod A (exp P C)) P)
                  (comp (fst A (exp P C)) (fst (prod A (exp P C)) P)))
                (comp (ev P C) (pair (comp (snd A (exp P C)) (fst (prod A (exp P C)) P))
                  (snd (prod A (exp P C)) P))))))) (snd (prod P A) (list A)))
            (comp (fst P A) (fst (prod P A) (list A)))))) := by
      have f1m := fst_pair hM hn hff
      have s1m := snd_pair hM hn hff
      refine (pair_comp hM (pair_hom hM hsE (comp_hom hM hfE hfAE)) (comp_hom hM hpe hev) hm).trans
        (eval_op₂_congr 9 ?_ ?_)
      · refine ((pair_comp hM hsE (comp_hom hM hfE hfAE) hm).trans (eval_op₂_congr 9 s1m
          ((comp_assoc hM hm hfE hfAE).symm.trans ((eval_op₂_congr 3 rfl f1m).trans
            (fst_pair hM hsf hRsQ))))).trans (pair_eta hM hP hA hfQ)
      · refine (comp_assoc hM hm hpe hev).symm.trans (eval_op₂_congr 3 rfl ?_)
        exact (pair_comp hM (comp_hom hM hfE hsAE) hsE hm).trans (eval_op₂_congr 9
          ((comp_assoc hM hm hfE hsAE).symm.trans ((eval_op₂_congr 3 rfl f1m).trans
            (snd_pair hM hsf hRsQ))) s1m)
    refine (comp_assoc hM hk₁ hq hev).symm.trans (Eq.trans ?_ (eval_op₂_congr 3 rfl
      (eval_op₂_congr 9 rfl eT)).symm)
    refine (eval_op₂_congr 3 rfl ((pair_comp hM hRs hfL hk₁).trans (eval_op₂_congr 9
      ((comp_assoc hM hk₁ hsL hR).symm.trans ((eval_op₂_congr 3 rfl (snd_pair hM hff hcel)).trans
        eR)) (fst_pair hM hff hcel)))).trans ?_
    exact (ev_curry_pair hM hAE hP hT hn hff).trans ((comp_assoc hM hm hbody hS).symm.trans
      (eval_op₂_congr 3 rfl eB))

/-- The pairing of an arrow after the first projection with the second projection, after a
pairing, is the pairing of the arrow after the first component with the second. -/
theorem prodMapLeft_pair {h a b P Y X B : Tree} (hh : Hom M ρ h Y P) (ha : Hom M ρ a X Y)
    (hb : Hom M ρ b X B) :
    eval M ρ (comp (pair (comp h (fst Y B)) (snd Y B)) (pair a b)) =
      eval M ρ (pair (comp h a) b) := by
  have hf := fst_hom hM hh.isObj_dom hb.isObj_cod
  have hs := snd_hom hM hh.isObj_dom hb.isObj_cod
  have hab := pair_hom hM ha hb
  exact (pair_comp hM (comp_hom hM hf hh) hs hab).trans (eval_op₂_congr 9
    ((comp_assoc hM hab hf hh).symm.trans (eval_op₂_congr 3 rfl (fst_pair hM ha hb)))
    (snd_pair hM ha hb))

/-- The pairing of the identity with an arrow, after an arrow, is the pairing of the arrow with
the composite. -/
theorem pair_idt_comp {m h X Y N : Tree} (hm : Hom M ρ m X N) (hh : Hom M ρ h Y X) :
    eval M ρ (comp (pair (idt X) m) h) = eval M ρ (pair h (comp m h)) :=
  (pair_comp hM (idt_hom hM hm.isObj_dom) hm hh).trans (eval_op₂_congr 9 (idt_comp hM hh) rfl)

/-- The fold of the natural numbers object with a parameter is natural in the parameter: after
the product of an arrow into the object of parameters with the identity, it is the fold whose
start is after the arrow and whose step is after its product with the identity. -/
theorem natRecP_comp {z S P Y C h : Tree} (hP : IsObj M ρ P) (hz : Hom M ρ z P C)
    (hS : Hom M ρ S (prod P C) C) (hh : Hom M ρ h Y P) :
    eval M ρ (comp (natRecP P C z S) (pair (comp h (fst Y nat)) (snd Y nat))) =
      eval M ρ (natRecP Y C (comp z h) (comp S (pair (comp h (fst Y C)) (snd Y C)))) := by
  have hY := hh.isObj_dom
  have hN := isObj_nat (ρ := ρ) hM
  have hC := hz.isObj_cod
  obtain ⟨hR, hR₀, hR₁⟩ := natRecP_spec hM hP hz hS
  have hz' := comp_hom hM hh hz
  have hk := pair_hom hM (comp_hom hM (fst_hom hM hY hC) hh) (snd_hom hM hY hC)
  have hS' := comp_hom hM hk hS
  obtain ⟨hR', hR'₀, hR'₁⟩ := natRecP_spec hM hY hz' hS'
  have hfY := fst_hom hM hY hN
  have hsY := snd_hom hM hY hN
  have hkN := pair_hom hM (comp_hom hM hfY hh) hsY
  have hF := comp_hom hM hkN hR
  refine natRec_param_unique hM hY hF hR' hS' ?_ ?_ hR'₁
  · -- at zero, both are the start after the arrow
    have h0Y := comp_hom hM (bang_hom hM hY) (zeroN_hom hM)
    have h0P := comp_hom hM (bang_hom hM hP) (zeroN_hom hM)
    have hp0 := pair_hom hM (idt_hom hM hY) h0Y
    have hp0P := pair_hom hM (idt_hom hM hP) h0P
    have e₁ : eval M ρ (comp (pair (comp h (fst Y nat)) (snd Y nat))
        (pair (idt Y) (comp zeroN (bang Y)))) =
        eval M ρ (comp (pair (idt P) (comp zeroN (bang P))) h) :=
      (prodMapLeft_pair hM hh (idt_hom hM hY) h0Y).trans ((eval_op₂_congr 9 (comp_idt hM hh)
        ((eval_op₂_congr 3 rfl (comp_bang hM hh).symm).trans
          (comp_assoc hM hh (bang_hom hM hP) (zeroN_hom hM)))).trans
        (pair_idt_comp hM h0P hh).symm)
    exact (comp_assoc hM hp0 hkN hR).symm.trans ((eval_op₂_congr 3 rfl e₁).trans
      ((comp_assoc hM hh hp0P hR).trans ((eval_op₂_congr 3 hR₀ rfl).trans hR'₀.symm)))
  · -- at a successor, both are the step after the arrow at the parameter and the value
    have hsc := comp_hom hM hsY (succ_hom hM)
    have hq := pair_hom hM hfY hsc
    have hfP := fst_hom hM hP hN
    have hsP := snd_hom hM hP hN
    have hqP := pair_hom hM hfP (comp_hom hM hsP (succ_hom hM))
    have e₂ : eval M ρ (comp (pair (comp h (fst Y nat)) (snd Y nat))
        (pair (fst Y nat) (comp succ (snd Y nat)))) =
        eval M ρ (comp (pair (fst P nat) (comp succ (snd P nat)))
          (pair (comp h (fst Y nat)) (snd Y nat))) :=
      (prodMapLeft_pair hM hh hfY hsc).trans ((pair_comp hM hfP
        (comp_hom hM hsP (succ_hom hM)) hkN).trans (eval_op₂_congr 9
          (fst_pair hM (comp_hom hM hfY hh) hsY) ((comp_assoc hM hkN hsP (succ_hom hM)).symm.trans
            (eval_op₂_congr 3 rfl (snd_pair hM (comp_hom hM hfY hh) hsY))))).symm
    have hpR := pair_hom hM hfP hR
    refine (comp_assoc hM hq hkN hR).symm.trans ((eval_op₂_congr 3 rfl e₂).trans
      ((comp_assoc hM hkN hqP hR).trans ((eval_op₂_congr 3 hR₁ rfl).trans
        ((comp_assoc hM hkN hpR hS).symm.trans ((eval_op₂_congr 3 rfl
          ((pair_comp hM hfP hR hkN).trans (eval_op₂_congr 9
            (fst_pair hM (comp_hom hM hfY hh) hsY) rfl))).trans ?_)))))
    exact ((comp_assoc hM (pair_hom hM hfY hF) hk hS).symm.trans (eval_op₂_congr 3 rfl
      (prodMapLeft_pair hM hh hfY hF))).symm

/-- The fold of a list object with a parameter is natural in the parameter: after the product of
an arrow into the object of parameters with the identity, it is the fold whose start is after the
arrow and whose step is after its product with the identities. -/
theorem listRecP_comp {z S P Y A C h : Tree} (hP : IsObj M ρ P) (hA : IsObj M ρ A)
    (hz : Hom M ρ z P C) (hS : Hom M ρ S (prod (prod P A) C) C) (hh : Hom M ρ h Y P) :
    eval M ρ (comp (listRecP P A C z S) (pair (comp h (fst Y (list A))) (snd Y (list A)))) =
      eval M ρ (listRecP Y A C (comp z h) (comp S (pair (comp (pair (comp h (fst Y A))
        (snd Y A)) (fst (prod Y A) C)) (snd (prod Y A) C)))) := by
  have hY := hh.isObj_dom
  have hL := isObj_list hM hA
  have hC := hz.isObj_cod
  have hYA := isObj_prod hM hY hA
  have hPA := isObj_prod hM hP hA
  obtain ⟨hR, hR₀, hR₁⟩ := listRecP_spec hM hP hA hz hS
  have hfYA := fst_hom hM hY hA
  have hsYA := snd_hom hM hY hA
  have hkA := pair_hom hM (comp_hom hM hfYA hh) hsYA
  have hk := pair_hom hM (comp_hom hM (fst_hom hM hYA hC) hkA) (snd_hom hM hYA hC)
  have hS' := comp_hom hM hk hS
  have hz' := comp_hom hM hh hz
  obtain ⟨hR', hR'₀, hR'₁⟩ := listRecP_spec hM hY hA hz' hS'
  have hfYL := fst_hom hM hY hL
  have hsYL := snd_hom hM hY hL
  have hkL := pair_hom hM (comp_hom hM hfYL hh) hsYL
  have hF := comp_hom hM hkL hR
  refine listRec_param_unique hM hY hA hF hR' hS' ?_ ?_ hR'₁
  · -- at the empty list, both are the start after the arrow
    have h0Y := comp_hom hM (bang_hom hM hY) (nil_hom hM hA)
    have h0P := comp_hom hM (bang_hom hM hP) (nil_hom hM hA)
    have hp0 := pair_hom hM (idt_hom hM hY) h0Y
    have hp0P := pair_hom hM (idt_hom hM hP) h0P
    have e₁ : eval M ρ (comp (pair (comp h (fst Y (list A))) (snd Y (list A)))
        (pair (idt Y) (comp (nil A) (bang Y)))) =
        eval M ρ (comp (pair (idt P) (comp (nil A) (bang P))) h) :=
      (prodMapLeft_pair hM hh (idt_hom hM hY) h0Y).trans ((eval_op₂_congr 9 (comp_idt hM hh)
        ((eval_op₂_congr 3 rfl (comp_bang hM hh).symm).trans
          (comp_assoc hM hh (bang_hom hM hP) (nil_hom hM hA)))).trans
        (pair_idt_comp hM h0P hh).symm)
    exact (comp_assoc hM hp0 hkL hR).symm.trans ((eval_op₂_congr 3 rfl e₁).trans
      ((comp_assoc hM hh hp0P hR).trans ((eval_op₂_congr 3 hR₀ rfl).trans hR'₀.symm)))
  · -- at a construction, both are the step after the arrow at the parameter, the element and
    -- the value at the tail
    have hfQ := fst_hom hM hYA hL
    have hsQ := snd_hom hM hYA hL
    have hfQP := fst_hom hM hPA hL
    have hsQP := snd_hom hM hPA hL
    have hfPA := fst_hom hM hP hA
    have hsPA := snd_hom hM hP hA
    have hkAf := comp_hom hM hfQ hkA
    have hkAL := pair_hom hM hkAf hsQ
    have hff := comp_hom hM hfQ hfYA
    have hsf := comp_hom hM hfQ hsYA
    have hffP := comp_hom hM hfQP hfPA
    have hsfP := comp_hom hM hfQP hsPA
    have ef := fst_pair hM hkAf hsQ
    have es := snd_pair hM hkAf hsQ
    have hh₁ := comp_hom hM hfYA hh
    have eff : eval M ρ (comp (comp (fst P A) (fst (prod P A) (list A)))
        (pair (comp (pair (comp h (fst Y A)) (snd Y A)) (fst (prod Y A) (list A)))
          (snd (prod Y A) (list A)))) =
        eval M ρ (comp h (comp (fst Y A) (fst (prod Y A) (list A)))) :=
      (comp_assoc hM hkAL hfQP hfPA).symm.trans ((eval_op₂_congr 3 rfl ef).trans
        ((comp_assoc hM hfQ hkA hfPA).trans ((eval_op₂_congr 3 (fst_pair hM hh₁ hsYA) rfl).trans
          (comp_assoc hM hfQ hfYA hh).symm)))
    have esf : eval M ρ (comp (comp (snd P A) (fst (prod P A) (list A)))
        (pair (comp (pair (comp h (fst Y A)) (snd Y A)) (fst (prod Y A) (list A)))
          (snd (prod Y A) (list A)))) =
        eval M ρ (comp (snd Y A) (fst (prod Y A) (list A))) :=
      (comp_assoc hM hkAL hfQP hsPA).symm.trans ((eval_op₂_congr 3 rfl ef).trans
        ((comp_assoc hM hfQ hkA hsPA).trans (eval_op₂_congr 3 (snd_pair hM hh₁ hsYA) rfl)))
    have hpe := pair_hom hM hsf hsQ
    have hpeP := pair_hom hM hsfP hsQP
    have hcY := comp_hom hM hpe (cons_hom hM hA)
    have hcP := comp_hom hM hpeP (cons_hom hM hA)
    have hqP := pair_hom hM hffP hcP
    have htP := pair_hom hM hffP hsQP
    have htY := pair_hom hM hff hsQ
    -- the construction and the tail after the products with the arrow
    have ec : eval M ρ (comp (pair (comp h (fst Y (list A))) (snd Y (list A)))
        (pair (comp (fst Y A) (fst (prod Y A) (list A)))
          (comp (cons A) (pair (comp (snd Y A) (fst (prod Y A) (list A)))
            (snd (prod Y A) (list A)))))) =
        eval M ρ (comp (pair (comp (fst P A) (fst (prod P A) (list A)))
          (comp (cons A) (pair (comp (snd P A) (fst (prod P A) (list A)))
            (snd (prod P A) (list A)))))
          (pair (comp (pair (comp h (fst Y A)) (snd Y A)) (fst (prod Y A) (list A)))
            (snd (prod Y A) (list A)))) :=
      (prodMapLeft_pair hM hh hff hcY).trans ((pair_comp hM hffP hcP hkAL).trans
        (eval_op₂_congr 9 eff ((comp_assoc hM hkAL hpeP (cons_hom hM hA)).symm.trans
          (eval_op₂_congr 3 rfl ((pair_comp hM hsfP hsQP hkAL).trans
            (eval_op₂_congr 9 esf es)))))).symm
    have et : eval M ρ (comp (pair (comp h (fst Y (list A))) (snd Y (list A)))
        (pair (comp (fst Y A) (fst (prod Y A) (list A))) (snd (prod Y A) (list A)))) =
        eval M ρ (comp (pair (comp (fst P A) (fst (prod P A) (list A)))
          (snd (prod P A) (list A)))
          (pair (comp (pair (comp h (fst Y A)) (snd Y A)) (fst (prod Y A) (list A)))
            (snd (prod Y A) (list A)))) :=
      (prodMapLeft_pair hM hh hff hsQ).trans ((pair_comp hM hffP hsQP hkAL).trans
        (eval_op₂_congr 9 eff es)).symm
    have hRt := comp_hom hM htP hR
    have hpR := pair_hom hM hfQP hRt
    refine (comp_assoc hM (pair_hom hM hff hcY) hkL hR).symm.trans
      ((eval_op₂_congr 3 rfl ec).trans ((comp_assoc hM hkAL hqP hR).trans
        ((eval_op₂_congr 3 hR₁ rfl).trans ((comp_assoc hM hkAL hpR hS).symm.trans
          ((eval_op₂_congr 3 rfl ((pair_comp hM hfQP hRt hkAL).trans (eval_op₂_congr 9 ef
            ((comp_assoc hM hkAL htP hR).symm.trans ((eval_op₂_congr 3 rfl et.symm).trans
              (comp_assoc hM htY hkL hR)))))).trans ?_)))))
    exact ((comp_assoc hM (pair_hom hM hfQ (comp_hom hM htY hF)) hk hS).symm.trans
      (eval_op₂_congr 3 rfl (prodMapLeft_pair hM hkA hfQ (comp_hom hM htY hF)))).symm

/-- The fold of the natural numbers object with a parameter, at the identity paired with a
successor, is the step at the identity paired with the fold at the number. -/
theorem natRecP_succ_at {z S P C g : Tree} (hP : IsObj M ρ P) (hz : Hom M ρ z P C)
    (hS : Hom M ρ S (prod P C) C) (hg : Hom M ρ g P nat) :
    eval M ρ (comp (natRecP P C z S) (pair (idt P) (comp succ g))) =
      eval M ρ (comp S (pair (idt P) (comp (natRecP P C z S) (pair (idt P) g)))) := by
  have hN := isObj_nat (ρ := ρ) hM
  obtain ⟨hR, -, hR₁⟩ := natRecP_spec hM hP hz hS
  have hi := idt_hom hM hP
  have hq := pair_hom hM hi hg
  have hf := fst_hom hM hP hN
  have hs := snd_hom hM hP hN
  have hc := comp_hom hM hs (succ_hom hM)
  have eQ : eval M ρ (comp (pair (fst P nat) (comp succ (snd P nat))) (pair (idt P) g)) =
      eval M ρ (pair (idt P) (comp succ g)) :=
    (pair_comp hM hf hc hq).trans (eval_op₂_congr 9 (fst_pair hM hi hg)
      ((comp_assoc hM hq hs (succ_hom hM)).symm.trans
        (eval_op₂_congr 3 rfl (snd_pair hM hi hg))))
  exact (eval_op₂_congr 3 rfl eQ.symm).trans ((comp_assoc hM hq (pair_hom hM hf hc) hR).trans
    ((eval_op₂_congr 3 hR₁ rfl).trans ((comp_assoc hM hq (pair_hom hM hf hR) hS).symm.trans
      (eval_op₂_congr 3 rfl ((pair_comp hM hf hR hq).trans
        (eval_op₂_congr 9 (fst_pair hM hi hg) rfl))))))

/-- The fold of a list object with a parameter, at the identity paired with a construction, is
the step at the identity paired with the element, paired with the fold at the tail. -/
theorem listRecP_cons_at {z S P A C gh gt : Tree} (hP : IsObj M ρ P) (hA : IsObj M ρ A)
    (hz : Hom M ρ z P C) (hS : Hom M ρ S (prod (prod P A) C) C) (hgh : Hom M ρ gh P A)
    (hgt : Hom M ρ gt P (list A)) :
    eval M ρ (comp (listRecP P A C z S) (pair (idt P) (comp (cons A) (pair gh gt)))) =
      eval M ρ (comp S (pair (pair (idt P) gh)
        (comp (listRecP P A C z S) (pair (idt P) gt)))) := by
  have hL := isObj_list hM hA
  have hPA := isObj_prod hM hP hA
  obtain ⟨hR, -, hR₁⟩ := listRecP_spec hM hP hA hz hS
  have hi := idt_hom hM hP
  have hpg := pair_hom hM hi hgh
  have hq := pair_hom hM hpg hgt
  have hf := fst_hom hM hPA hL
  have hF1 := comp_hom hM hf (fst_hom hM hP hA)
  have hF2 := comp_hom hM hf (snd_hom hM hP hA)
  have hF3 := snd_hom hM hPA hL
  have hp23 := pair_hom hM hF2 hF3
  have hp13 := pair_hom hM hF1 hF3
  have hcF := comp_hom hM hp23 (cons_hom hM hA)
  have e0 := fst_pair hM hpg hgt
  have e3 := snd_pair hM hpg hgt
  have e1 : eval M ρ (comp (comp (fst P A) (fst (prod P A) (list A)))
      (pair (pair (idt P) gh) gt)) = eval M ρ (idt P) :=
    (comp_assoc hM hq hf (fst_hom hM hP hA)).symm.trans
      ((eval_op₂_congr 3 rfl e0).trans (fst_pair hM hi hgh))
  have e2 : eval M ρ (comp (comp (snd P A) (fst (prod P A) (list A)))
      (pair (pair (idt P) gh) gt)) = eval M ρ gh :=
    (comp_assoc hM hq hf (snd_hom hM hP hA)).symm.trans
      ((eval_op₂_congr 3 rfl e0).trans (snd_pair hM hi hgh))
  have eQ := (pair_comp hM hF1 hcF hq).trans (eval_op₂_congr 9 e1
    ((comp_assoc hM hq hp23 (cons_hom hM hA)).symm.trans
      (eval_op₂_congr 3 rfl ((pair_comp hM hF2 hF3 hq).trans (eval_op₂_congr 9 e2 e3)))))
  have eT := (pair_comp hM hf (comp_hom hM hp13 hR) hq).trans (eval_op₂_congr 9 e0
    ((comp_assoc hM hq hp13 hR).symm.trans
      (eval_op₂_congr 3 rfl ((pair_comp hM hF1 hF3 hq).trans (eval_op₂_congr 9 e1 e3)))))
  exact (eval_op₂_congr 3 rfl eQ.symm).trans ((comp_assoc hM hq (pair_hom hM hF1 hcF) hR).trans
    ((eval_op₂_congr 3 hR₁ rfl).trans
      ((comp_assoc hM hq (pair_hom hM hf (comp_hom hM hp13 hR)) hS).symm.trans
        (eval_op₂_congr 3 rfl eT))))

/-- The fold of the natural numbers object with a parameter, whose start and step do not depend
on the parameter, is the fold of the natural numbers object after the number. -/
theorem natRecP_const {z S P C m : Tree} (hP : IsObj M ρ P) (hz : Hom M ρ z one C)
    (hS : Hom M ρ S C C) (hm : Hom M ρ m P nat) :
    eval M ρ (comp (natRecP P C (comp z (bang P)) (comp S (snd P C))) (pair (idt P) m)) =
      eval M ρ (comp (natRec z S) m) := by
  have hN := isObj_nat (ρ := ρ) hM
  have hC := hz.isObj_cod
  have hi := idt_hom hM hP
  have hR := natRec_hom hM hz hS
  have hsPN := snd_hom hM hP hN
  have hG := comp_hom hM hsPN hR
  have hS' := comp_hom hM (snd_hom hM hP hC) hS
  obtain ⟨hF, hF₀, hF₁⟩ := natRecP_spec hM hP (comp_hom hM (bang_hom hM hP) hz) hS'
  -- at zero, both are the start
  have h0 := comp_hom hM (bang_hom hM hP) (zeroN_hom hM)
  have h₀ := hF₀.trans (((comp_assoc hM (pair_hom hM hi h0) hsPN hR).symm.trans
    ((eval_op₂_congr 3 rfl (snd_pair hM hi h0)).trans
      ((comp_assoc hM (bang_hom hM hP) (zeroN_hom hM) hR).trans
        (eval_op₂_congr 3 (natRec_zero hM hz hS) rfl)))).symm)
  -- at a successor, both are the step at the value at the predecessor
  have hfPN := fst_hom hM hP hN
  have hc := comp_hom hM hsPN (succ_hom hM)
  have hpG := pair_hom hM hfPN hG
  have eL : eval M ρ (comp (comp (natRec z S) (snd P nat))
      (pair (fst P nat) (comp succ (snd P nat)))) =
      eval M ρ (comp S (comp (natRec z S) (snd P nat))) :=
    (comp_assoc hM (pair_hom hM hfPN hc) hsPN hR).symm.trans
      ((eval_op₂_congr 3 rfl (snd_pair hM hfPN hc)).trans
        ((comp_assoc hM hsPN (succ_hom hM) hR).trans
          ((eval_op₂_congr 3 (natRec_succ hM hz hS) rfl).trans
            (comp_assoc hM hsPN hR hS).symm)))
  have eR : eval M ρ (comp (comp S (snd P C)) (pair (fst P nat)
      (comp (natRec z S) (snd P nat)))) = eval M ρ (comp S (comp (natRec z S) (snd P nat))) :=
    (comp_assoc hM hpG (snd_hom hM hP hC) hS).symm.trans
      (eval_op₂_congr 3 rfl (snd_pair hM hfPN hG))
  have hFG := natRec_param_unique hM hP hF hG hS' h₀ hF₁ (eL.trans eR.symm)
  exact (eval_op₂_congr 3 hFG rfl).trans ((comp_assoc hM (pair_hom hM hi hm) hsPN hR).symm.trans
    (eval_op₂_congr 3 rfl (snd_pair hM hi hm)))

/-- The fold of a list object with a parameter, whose start and step do not depend on the
parameter, is the fold of the list object after the list. -/
theorem listRecP_const {z S P A C m : Tree} (hP : IsObj M ρ P) (hA : IsObj M ρ A)
    (hz : Hom M ρ z one C) (hS : Hom M ρ S (prod A C) C) (hm : Hom M ρ m P (list A)) :
    eval M ρ (comp (listRecP P A C (comp z (bang P))
      (comp S (pair (comp (snd P A) (fst (prod P A) C)) (snd (prod P A) C)))) (pair (idt P) m)) =
      eval M ρ (comp (listRec A z S) m) := by
  have hL := isObj_list hM hA
  have hC := hz.isObj_cod
  have hPA := isObj_prod hM hP hA
  have hi := idt_hom hM hP
  have hLR := listRec_hom hM hA hz hS
  have hsPL := snd_hom hM hP hL
  have hG := comp_hom hM hsPL hLR
  have hg1 := comp_hom hM (fst_hom hM hPA hC) (snd_hom hM hP hA)
  have hg2 := snd_hom hM hPA hC
  have hg := pair_hom hM hg1 hg2
  have hS' := comp_hom hM hg hS
  obtain ⟨hR, hR₀, hR₁⟩ := listRecP_spec hM hP hA (comp_hom hM (bang_hom hM hP) hz) hS'
  -- at the empty list, both are the start
  have h0 := comp_hom hM (bang_hom hM hP) (nil_hom hM hA)
  have hp0 := pair_hom hM hi h0
  have h₀ := hR₀.trans (((comp_assoc hM hp0 hsPL hLR).symm.trans ((eval_op₂_congr 3 rfl
    (snd_pair hM hi h0)).trans ((comp_assoc hM (bang_hom hM hP) (nil_hom hM hA) hLR).trans
      (eval_op₂_congr 3 (listRec_nil hM hA hz hS) rfl)))).symm)
  -- at a construction, both are the step at the element and the value at the tail
  have hfPAL := fst_hom hM hPA hL
  have hF1 := comp_hom hM hfPAL (fst_hom hM hP hA)
  have hF2 := comp_hom hM hfPAL (snd_hom hM hP hA)
  have hF3 := snd_hom hM hPA hL
  have hp23 := pair_hom hM hF2 hF3
  have hp13 := pair_hom hM hF1 hF3
  have hc := comp_hom hM hp23 (cons_hom hM hA)
  have hQ := pair_hom hM hF1 hc
  have hfAL := fst_hom hM hA hL
  have hsAL := snd_hom hM hA hL
  have hpAL := pair_hom hM hfAL (comp_hom hM hsAL hLR)
  have eL : eval M ρ (comp (comp (listRec A z S) (snd P (list A)))
      (pair (comp (fst P A) (fst (prod P A) (list A)))
        (comp (cons A) (pair (comp (snd P A) (fst (prod P A) (list A)))
          (snd (prod P A) (list A)))))) =
      eval M ρ (comp S (pair (comp (snd P A) (fst (prod P A) (list A)))
        (comp (listRec A z S) (snd (prod P A) (list A))))) :=
    (comp_assoc hM hQ hsPL hLR).symm.trans ((eval_op₂_congr 3 rfl (snd_pair hM hF1 hc)).trans
      ((comp_assoc hM hp23 (cons_hom hM hA) hLR).trans
        ((eval_op₂_congr 3 (listRec_cons hM hA hz hS) rfl).trans
          ((comp_assoc hM hp23 hpAL hS).symm.trans (eval_op₂_congr 3 rfl
            ((pair_comp hM hfAL (comp_hom hM hsAL hLR) hp23).trans (eval_op₂_congr 9
              (fst_pair hM hF2 hF3) ((comp_assoc hM hp23 hsAL hLR).symm.trans
                (eval_op₂_congr 3 rfl (snd_pair hM hF2 hF3))))))))))
  have hGG := comp_hom hM hp13 hG
  have hpr := pair_hom hM hfPAL hGG
  have eR : eval M ρ (comp (comp S (pair (comp (snd P A) (fst (prod P A) C)) (snd (prod P A) C)))
      (pair (fst (prod P A) (list A)) (comp (comp (listRec A z S) (snd P (list A)))
        (pair (comp (fst P A) (fst (prod P A) (list A))) (snd (prod P A) (list A)))))) =
      eval M ρ (comp S (pair (comp (snd P A) (fst (prod P A) (list A)))
        (comp (listRec A z S) (snd (prod P A) (list A))))) :=
    (comp_assoc hM hpr hg hS).symm.trans (eval_op₂_congr 3 rfl ((pair_comp hM hg1 hg2 hpr).trans
      (eval_op₂_congr 9 ((comp_assoc hM hpr (fst_hom hM hPA hC) (snd_hom hM hP hA)).symm.trans
        (eval_op₂_congr 3 rfl (fst_pair hM hfPAL hGG))) ((snd_pair hM hfPAL hGG).trans
          ((comp_assoc hM hp13 hsPL hLR).symm.trans
            (eval_op₂_congr 3 rfl (snd_pair hM hF1 hF3)))))))
  have hFG := listRec_param_unique hM hP hA hR hG hS' h₀ hR₁ (eL.trans eR.symm)
  exact (eval_op₂_congr 3 hFG rfl).trans ((comp_assoc hM (pair_hom hM hi hm) hsPL hLR).symm.trans
    (eval_op₂_congr 3 rfl (snd_pair hM hi hm)))

/-- The fold of a list object with a parameter, from the empty list, whose step constructs the
image of the element under an arrow onto the value, is the list object's action on the arrow
after the list. -/
theorem listRecP_map {f P A C m : Tree} (hP : IsObj M ρ P) (hf : Hom M ρ f A C)
    (hm : Hom M ρ m P (list A)) :
    eval M ρ (comp (listRecP P A (list C) (comp (nil C) (bang P))
      (comp (cons C) (pair (comp f (comp (snd P A) (fst (prod P A) (list C))))
        (snd (prod P A) (list C))))) (pair (idt P) m)) = eval M ρ (comp (listMap f) m) := by
  have hA := hf.isObj_dom
  have hC := hf.isObj_cod
  have h1 := isObj_one (ρ := ρ) hM
  have hLc := isObj_list hM hC
  have hPA := isObj_prod hM hP hA
  have hfA := fst_hom hM hA hLc
  have hsA := snd_hom hM hA hLc
  have hff := comp_hom hM hfA hf
  have hp := pair_hom hM hff hsA
  have hg1 := comp_hom hM (fst_hom hM hPA hLc) (snd_hom hM hP hA)
  have hg2 := snd_hom hM hPA hLc
  have hq := pair_hom hM hg1 hg2
  exact (eval_op₂_congr 3 (eval_listRecP_congr P A (list C)
    ((eval_op₂_congr 3 rfl (comp_bang hM (bang_hom hM hP)).symm).trans
      (comp_assoc hM (bang_hom hM hP) (bang_hom hM h1) (nil_hom hM hC)))
    ((comp_assoc hM hq hp (cons_hom hM hC)).symm.trans (eval_op₂_congr 3 rfl
      ((pair_comp hM hff hsA hq).trans (eval_op₂_congr 9
        ((comp_assoc hM hq hfA hf).symm.trans (eval_op₂_congr 3 rfl (fst_pair hM hg1 hg2)))
        (snd_pair hM hg1 hg2))))).symm) rfl).trans
    ((listRecP_const hM hP hA (comp_hom hM (bang_hom hM h1) (nil_hom hM hC))
      (comp_hom hM hp (cons_hom hM hC)) hm).trans (eval_op₂_congr 3 (eval_listMap hM hf).symm rfl))

/-- The fold of the natural numbers object with a parameter at an arrow into the parameters and a
number is the fold with the arrow's domain as parameter, its start and step after the arrow, at
the identity and the number. -/
theorem natRecP_pair {z S P X C t m : Tree} (hP : IsObj M ρ P) (hz : Hom M ρ z P C)
    (hS : Hom M ρ S (prod P C) C) (ht : Hom M ρ t X P) (hm : Hom M ρ m X nat) :
    eval M ρ (comp (natRecP P C z S) (pair t m)) =
      eval M ρ (comp (natRecP X C (comp z t) (comp S (pair (comp t (fst X C)) (snd X C))))
        (pair (idt X) m)) := by
  have hX := ht.isObj_dom
  have hN := isObj_nat (ρ := ρ) hM
  have hq := pair_hom hM (comp_hom hM (fst_hom hM hX hN) ht) (snd_hom hM hX hN)
  have hR := (natRecP_spec hM hP hz hS).1
  exact (eval_op₂_congr 3 rfl ((eval_op₂_congr 9 (comp_idt hM ht).symm rfl).trans
    (prodMapLeft_pair hM ht (idt_hom hM hX) hm).symm)).trans
    ((comp_assoc hM (pair_hom hM (idt_hom hM hX) hm) hq hR).trans
      (eval_op₂_congr 3 (natRecP_comp hM hP hz hS ht) rfl))

/-- The fold of a list object with a parameter at an arrow into the parameters and a list is the
fold with the arrow's domain as parameter, its start and step after the arrow, at the identity and
the list. -/
theorem listRecP_pair {z S P X A C t m : Tree} (hP : IsObj M ρ P) (hA : IsObj M ρ A)
    (hz : Hom M ρ z P C) (hS : Hom M ρ S (prod (prod P A) C) C) (ht : Hom M ρ t X P)
    (hm : Hom M ρ m X (list A)) :
    eval M ρ (comp (listRecP P A C z S) (pair t m)) =
      eval M ρ (comp (listRecP X A C (comp z t) (comp S (pair (comp (pair (comp t (fst X A))
        (snd X A)) (fst (prod X A) C)) (snd (prod X A) C)))) (pair (idt X) m)) := by
  have hX := ht.isObj_dom
  have hL := isObj_list hM hA
  have hq := pair_hom hM (comp_hom hM (fst_hom hM hX hL) ht) (snd_hom hM hX hL)
  have hR := (listRecP_spec hM hP hA hz hS).1
  exact (eval_op₂_congr 3 rfl ((eval_op₂_congr 9 (comp_idt hM ht).symm rfl).trans
    (prodMapLeft_pair hM ht (idt_hom hM hX) hm).symm)).trans
    ((comp_assoc hM (pair_hom hM (idt_hom hM hX) hm) hq hR).trans
      (eval_op₂_congr 3 (listRecP_comp hM hP hA hz hS ht) rfl))

/-- The existence of the fold of the natural numbers object with a parameter. -/
theorem natRec_param_exists {z S P C : Tree} (hP : IsObj M ρ P) (hz : Hom M ρ z P C)
    (hS : Hom M ρ S (prod P C) C) :
    ∃ f, Hom M ρ f (prod P nat) C ∧
      eval M ρ (comp f (pair (idt P) (comp zeroN (bang P)))) = eval M ρ z ∧
      eval M ρ (comp f (pair (fst P nat) (comp succ (snd P nat)))) =
        eval M ρ (comp S (pair (fst P nat) f)) :=
  ⟨_, natRecP_spec hM hP hz hS⟩

/-- The existence of the fold of a list object with a parameter. -/
theorem listRec_param_exists {z S P A C : Tree} (hP : IsObj M ρ P) (hA : IsObj M ρ A)
    (hz : Hom M ρ z P C) (hS : Hom M ρ S (prod (prod P A) C) C) :
    ∃ f, Hom M ρ f (prod P (list A)) C ∧
      eval M ρ (comp f (pair (idt P) (comp (nil A) (bang P)))) = eval M ρ z ∧
      eval M ρ (comp f (pair (comp (fst P A) (fst (prod P A) (list A)))
          (comp (cons A) (pair (comp (snd P A) (fst (prod P A) (list A)))
            (snd (prod P A) (list A)))))) =
        eval M ρ (comp S (pair (fst (prod P A) (list A))
          (comp f (pair (comp (fst P A) (fst (prod P A) (list A)))
            (snd (prod P A) (list A)))))) :=
  ⟨_, listRecP_spec hM hP hA hz hS⟩

end Parameters

end Geb.FreeTopos

end
