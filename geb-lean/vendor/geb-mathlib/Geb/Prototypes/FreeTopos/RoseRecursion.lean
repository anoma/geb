/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Recursion

set_option doc.verso true in
/-!
# The folds of rose trees with a parameter

The fold of a rose-tree object with a parameter in a model of the theory of an elementary topos
({name}`Geb.FreeTopos.roseRecP`): from the product of an object of parameters with the rose-tree
object, the fold into the exponential of the parameters, evaluated at the parameter. The
rose-tree functor, the product of the object of labels with the list object, is strong, so in a
cartesian closed category its initial algebra admits folds with a parameter
(\[GoncharovMiliusSchroderTsampasUrbat2022\], the appendix's induction with parameters):
the fold's step sees the parameter and the label paired with the list of the children's values,
which the step of the fold into the exponential computes by evaluating each child's function at
the parameter, a map of the list object with the parameter ({name}`Geb.FreeTopos.listMapP`).

The statements hold of every fold with the rose-tree object's laws ({lit}`RoseFold`), the folds
of the rose-tree object and of the rose-tree object over an object of labels among them, and are
stated at generalized elements: arrows from any object into the parameters, the labels and the
lists.

## Main definitions

* {lit}`RoseFold` — a fold with the computation and the uniqueness of the folds of a rose-tree
  object.

## Main statements

* {lit}`listMapP_nil_at`, {lit}`listMapP_cons_at`, {lit}`listMapP_map` — the action of the
  list object with a parameter, and its composite with the action without one.
* {lit}`listMapP_unique`, {lit}`listMapP_snd`, {lit}`listMapP_comp` — its uniqueness, its
  action on an arrow that ignores the parameter, and its naturality in the parameter.
* {lit}`roseRecP_hom`, {lit}`roseRecP_node_at` — the fold of a rose-tree object with a
  parameter at a construction.
* {lit}`roseRecP_unique` — the uniqueness of the fold with a parameter.
* {lit}`roseRecP_const`, {lit}`roseRecP_comp`, {lit}`roseRecP_pair` — the fold whose step
  ignores the parameter, and the fold's naturality in the parameter.

## References

* \[GoncharovMiliusSchroderTsampasUrbat2022\]

## Tags

elementary topos, rose tree, initial algebra, strong functor, parametrised recursion
-/

set_option doc.verso true

@[expose] public section

namespace Geb.FreeTopos

open PartialHorn Sorts
open scoped FinEnum

universe v

variable {defs : List Defn} {M : Model.{v} (ext defs).sig} {ρ : List M.Val}

variable (M ρ) in
/-- A fold {lit}`F` of the rose-tree object {lit}`t` over the object of labels {lit}`a`, whose
structure map is {lit}`nd`: at each step, an arrow from {lit}`t` whose composite with the
structure map is the step after the product of the labels with its action on the children, and
the only such arrow. -/
structure RoseFold (F : Tree → Tree) (nd t a : Tree) : Prop where
  /-- The object of labels is an object. -/
  isObj_lab : IsObj M ρ a
  /-- The structure map is an arrow from the product of the labels with the list of trees. -/
  node_hom : Hom M ρ nd (prod a (list t)) t
  /-- The fold by a step is an arrow from the rose-tree object. -/
  hom {S C : Tree} : Hom M ρ S (prod a (list C)) C → Hom M ρ (F S) t C
  /-- The fold after the structure map is the step after its action on the children. -/
  node {S C : Tree} : Hom M ρ S (prod a (list C)) C →
    eval M ρ (comp (F S) nd) = eval M ρ (comp S (prodMapRight a (listMap (F S))))
  /-- An arrow whose composite with the structure map is the step after its action on the
  children is the fold. -/
  unique {h S C : Tree} : Hom M ρ S (prod a (list C)) C → Hom M ρ h t C →
    eval M ρ (comp h nd) = eval M ρ (comp S (prodMapRight a (listMap h))) →
    eval M ρ h = eval M ρ (F S)

section Parameters

variable (hM : IsModel (ext defs) M)
include hM

/-- The fold of the rose-tree object has the laws of a fold of a rose-tree object. -/
theorem roseFold_rose : RoseFold M ρ roseRec node rose nat :=
  ⟨isObj_nat hM, node_hom hM, roseRec_hom hM, roseRec_node hM,
    fun hs hh h₁ ↦ roseRec_unique hM hs hh h₁⟩

/-- The fold of the rose-tree object over an object of labels has the laws of a fold of a
rose-tree object. -/
theorem roseFold_lrose {A : Tree} (hA : IsObj M ρ A) :
    RoseFold M ρ (lroseRec A) (lnode A) (lrose A) A :=
  ⟨hA, lnode_hom hM hA, lroseRec_hom hM hA, lroseRec_node hM hA,
    fun hs hh h₁ ↦ lroseRec_unique hM hA hs hh h₁⟩

/-- The fold of a list object with a parameter, at an arrow into the parameters paired with the
empty list, is the start after the arrow. -/
theorem listRecP_nil_pair {z S P A C X x : Tree} (hP : IsObj M ρ P) (hA : IsObj M ρ A)
    (hz : Hom M ρ z P C) (hS : Hom M ρ S (prod (prod P A) C) C) (hx : Hom M ρ x X P) :
    eval M ρ (comp (listRecP P A C z S) (pair x (comp (nil A) (bang X)))) =
      eval M ρ (comp z x) := by
  have hX := hx.isObj_dom
  obtain ⟨hR, hR₀, -⟩ := listRecP_spec hM hP hA hz hS
  have hnP := comp_hom hM (bang_hom hM hP) (nil_hom hM hA)
  have hi := idt_hom hM hP
  have e : eval M ρ (pair x (comp (nil A) (bang X))) =
      eval M ρ (comp (pair (idt P) (comp (nil A) (bang P))) x) :=
    ((pair_comp hM hi hnP hx).trans (eval_op₂_congr 9 (idt_comp hM hx)
      ((comp_assoc hM hx (bang_hom hM hP) (nil_hom hM hA)).symm.trans
        (eval_op₂_congr 3 rfl (comp_bang hM hx))))).symm
  exact (eval_op₂_congr 3 rfl e).trans ((comp_assoc hM hx (pair_hom hM hi hnP) hR).trans
    (eval_op₂_congr 3 hR₀ rfl))

/-- The fold of a list object with a parameter, at an arrow into the parameters paired with a
construction, is the step at the parameter and the element paired with the fold at the tail. -/
theorem listRecP_cons_pair {z S P A C X x y w : Tree} (hP : IsObj M ρ P) (hA : IsObj M ρ A)
    (hz : Hom M ρ z P C) (hS : Hom M ρ S (prod (prod P A) C) C) (hx : Hom M ρ x X P)
    (hy : Hom M ρ y X A) (hw : Hom M ρ w X (list A)) :
    eval M ρ (comp (listRecP P A C z S) (pair x (comp (cons A) (pair y w)))) =
      eval M ρ (comp S (pair (pair x y) (comp (listRecP P A C z S) (pair x w)))) := by
  have hL := isObj_list hM hA
  have hPA := isObj_prod hM hP hA
  obtain ⟨hR, -, hR₁⟩ := listRecP_spec hM hP hA hz hS
  have hpg := pair_hom hM hx hy
  have hq := pair_hom hM hpg hw
  have hf := fst_hom hM hPA hL
  have hF1 := comp_hom hM hf (fst_hom hM hP hA)
  have hF2 := comp_hom hM hf (snd_hom hM hP hA)
  have hF3 := snd_hom hM hPA hL
  have hp23 := pair_hom hM hF2 hF3
  have hp13 := pair_hom hM hF1 hF3
  have hcF := comp_hom hM hp23 (cons_hom hM hA)
  have e0 := fst_pair hM hpg hw
  have e3 := snd_pair hM hpg hw
  have e1 : eval M ρ (comp (comp (fst P A) (fst (prod P A) (list A))) (pair (pair x y) w)) =
      eval M ρ x :=
    (comp_assoc hM hq hf (fst_hom hM hP hA)).symm.trans
      ((eval_op₂_congr 3 rfl e0).trans (fst_pair hM hx hy))
  have e2 : eval M ρ (comp (comp (snd P A) (fst (prod P A) (list A))) (pair (pair x y) w)) =
      eval M ρ y :=
    (comp_assoc hM hq hf (snd_hom hM hP hA)).symm.trans
      ((eval_op₂_congr 3 rfl e0).trans (snd_pair hM hx hy))
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

/-- The step of the action of a list object with a parameter after a pairing of a pair with a
list is construction after the arrow at the pair paired with the list. -/
theorem listMapP_step_pair {f P A C u v X : Tree} (hf : Hom M ρ f (prod P A) C)
    (hu : Hom M ρ u X (prod P A)) (hv : Hom M ρ v X (list C)) :
    eval M ρ (comp (comp (cons C) (pair (comp f (fst (prod P A) (list C)))
        (snd (prod P A) (list C)))) (pair u v)) =
      eval M ρ (comp (cons C) (pair (comp f u) v)) := by
  have hQ := hu.isObj_cod
  have hL := hv.isObj_cod
  have hC := hf.isObj_cod
  have hfQ := fst_hom hM hQ hL
  have hsQ := snd_hom hM hQ hL
  have huv := pair_hom hM hu hv
  exact (comp_assoc hM huv (pair_hom hM (comp_hom hM hfQ hf) hsQ) (cons_hom hM hC)).symm.trans
    (eval_op₂_congr 3 rfl ((pair_comp hM (comp_hom hM hfQ hf) hsQ huv).trans
      (eval_op₂_congr 9 ((comp_assoc hM huv hfQ hf).symm.trans
        (eval_op₂_congr 3 rfl (fst_pair hM hu hv))) (snd_pair hM hu hv))))

/-- The action of a list object with a parameter is an arrow from the product of the parameters
with the list object into the list object of the codomain. -/
theorem listMapP_hom {f P A C : Tree} (hP : IsObj M ρ P) (hA : IsObj M ρ A)
    (hf : Hom M ρ f (prod P A) C) : Hom M ρ (listMapP P A C f) (prod P (list A)) (list C) := by
  have hC := hf.isObj_cod
  have hPA := isObj_prod hM hP hA
  have hL := isObj_list hM hC
  exact (listRecP_spec hM hP hA (comp_hom hM (bang_hom hM hP) (nil_hom hM hC))
    (comp_hom hM (pair_hom hM (comp_hom hM (fst_hom hM hPA hL) hf) (snd_hom hM hPA hL))
      (cons_hom hM hC))).1

/-- The action of a list object with a parameter at the empty list is the empty list. -/
theorem listMapP_nil_at {f P A C X x : Tree} (hP : IsObj M ρ P) (hA : IsObj M ρ A)
    (hf : Hom M ρ f (prod P A) C) (hx : Hom M ρ x X P) :
    eval M ρ (comp (listMapP P A C f) (pair x (comp (nil A) (bang X)))) =
      eval M ρ (comp (nil C) (bang X)) := by
  have hC := hf.isObj_cod
  have hPA := isObj_prod hM hP hA
  have hL := isObj_list hM hC
  exact (listRecP_nil_pair hM hP hA (comp_hom hM (bang_hom hM hP) (nil_hom hM hC))
    (comp_hom hM (pair_hom hM (comp_hom hM (fst_hom hM hPA hL) hf) (snd_hom hM hPA hL))
      (cons_hom hM hC)) hx).trans ((comp_assoc hM hx (bang_hom hM hP) (nil_hom hM hC)).symm.trans
        (eval_op₂_congr 3 rfl (comp_bang hM hx)))

/-- The action of a list object with a parameter at a construction is the construction of the
arrow at the parameter and the element onto the action at the tail. -/
theorem listMapP_cons_at {f P A C X x y w : Tree} (hP : IsObj M ρ P) (hA : IsObj M ρ A)
    (hf : Hom M ρ f (prod P A) C) (hx : Hom M ρ x X P) (hy : Hom M ρ y X A)
    (hw : Hom M ρ w X (list A)) :
    eval M ρ (comp (listMapP P A C f) (pair x (comp (cons A) (pair y w)))) =
      eval M ρ (comp (cons C) (pair (comp f (pair x y))
        (comp (listMapP P A C f) (pair x w)))) := by
  have hC := hf.isObj_cod
  have hPA := isObj_prod hM hP hA
  have hL := isObj_list hM hC
  have hR := listMapP_hom hM hP hA hf
  exact (listRecP_cons_pair hM hP hA (comp_hom hM (bang_hom hM hP) (nil_hom hM hC))
    (comp_hom hM (pair_hom hM (comp_hom hM (fst_hom hM hPA hL) hf) (snd_hom hM hPA hL))
      (cons_hom hM hC)) hx hy hw).trans
    (listMapP_step_pair hM hf (pair_hom hM hx hy) (comp_hom hM (pair_hom hM hx hw) hR))

omit hM in
/-- The action of a list object with a parameter respects the value of its arrow. -/
theorem eval_listMapP_congr (P A C : Tree) {f f' : Tree} (hf : eval M ρ f = eval M ρ f') :
    eval M ρ (listMapP P A C f) = eval M ρ (listMapP P A C f') :=
  eval_listRecP_congr P A (list C) rfl (eval_op₂_congr 3 rfl (eval_op₂_congr 9
    (eval_op₂_congr 3 hf rfl) rfl))

/-- The action of a list object on an arrow at the empty list is the empty list. -/
theorem listMap_nil_at {g B A X : Tree} (hg : Hom M ρ g B A) (hX : IsObj M ρ X) :
    eval M ρ (comp (listMap g) (comp (nil B) (bang X))) = eval M ρ (comp (nil A) (bang X)) :=
  (comp_assoc hM (bang_hom hM hX) (nil_hom hM hg.isObj_dom) (listMap_hom hM hg)).trans
    (eval_op₂_congr 3 (listMap_nil hM hg) rfl)

/-- The action of a list object on an arrow at a construction is the construction of the arrow
at the element onto the action at the tail. -/
theorem listMap_cons_at {g B A X y w : Tree} (hg : Hom M ρ g B A) (hy : Hom M ρ y X B)
    (hw : Hom M ρ w X (list B)) :
    eval M ρ (comp (listMap g) (comp (cons B) (pair y w))) =
      eval M ρ (comp (cons A) (pair (comp g y) (comp (listMap g) w))) := by
  have hB := hg.isObj_dom
  have hL := isObj_list hM hB
  have hm := listMap_hom hM hg
  have hyw := pair_hom hM hy hw
  exact (comp_assoc hM hyw (cons_hom hM hB) hm).trans ((eval_op₂_congr 3 (listMap_cons hM hg)
    rfl).trans (comp_pair_proj hM (cons_hom hM hg.isObj_cod) hg hm hy hw))

/-- The uniqueness of the action of a list object with a parameter: an arrow from the product of
the parameters with the list object that is the empty list at the empty list and, at a
construction, the construction of the arrow at the parameter and the element onto its value at
the tail, is the action. -/
theorem listMapP_unique {H f P A C : Tree} (hP : IsObj M ρ P) (hA : IsObj M ρ A)
    (hf : Hom M ρ f (prod P A) C) (hH : Hom M ρ H (prod P (list A)) (list C))
    (h₀ : eval M ρ (comp H (pair (idt P) (comp (nil A) (bang P)))) =
      eval M ρ (comp (nil C) (bang P)))
    (h₁ : ∀ {X x y w : Tree}, Hom M ρ x X P → Hom M ρ y X A → Hom M ρ w X (list A) →
      eval M ρ (comp H (pair x (comp (cons A) (pair y w)))) =
        eval M ρ (comp (cons C) (pair (comp f (pair x y)) (comp H (pair x w))))) :
    eval M ρ H = eval M ρ (listMapP P A C f) := by
  have hC := hf.isObj_cod
  have hL := isObj_list hM hA
  have hLC := isObj_list hM hC
  have hPA := isObj_prod hM hP hA
  have hR := listMapP_hom hM hP hA hf
  have hS := comp_hom hM (pair_hom hM (comp_hom hM (fst_hom hM hPA hLC) hf)
    (snd_hom hM hPA hLC)) (cons_hom hM hC)
  have hfQ := fst_hom hM hPA hL
  have hx := comp_hom hM hfQ (fst_hom hM hP hA)
  have hy := comp_hom hM hfQ (snd_hom hM hP hA)
  have hw := snd_hom hM hPA hL
  -- the parameter paired with the element is the pair's projection
  have exy : eval M ρ (pair (comp (fst P A) (fst (prod P A) (list A)))
      (comp (snd P A) (fst (prod P A) (list A)))) = eval M ρ (fst (prod P A) (list A)) :=
    pair_eta hM hP hA hfQ
  -- each arrow with the property satisfies the fold's equation with a parameter
  have step : ∀ {K : Tree}, Hom M ρ K (prod P (list A)) (list C) →
      (∀ {X x y w : Tree}, Hom M ρ x X P → Hom M ρ y X A → Hom M ρ w X (list A) →
        eval M ρ (comp K (pair x (comp (cons A) (pair y w)))) =
          eval M ρ (comp (cons C) (pair (comp f (pair x y)) (comp K (pair x w))))) →
      eval M ρ (comp K (pair (comp (fst P A) (fst (prod P A) (list A)))
          (comp (cons A) (pair (comp (snd P A) (fst (prod P A) (list A)))
            (snd (prod P A) (list A)))))) =
        eval M ρ (comp (comp (cons C) (pair (comp f (fst (prod P A) (list C)))
          (snd (prod P A) (list C)))) (pair (fst (prod P A) (list A))
            (comp K (pair (comp (fst P A) (fst (prod P A) (list A)))
              (snd (prod P A) (list A)))))) := fun {K} hK hK₁ ↦
    (hK₁ hx hy hw).trans (Eq.trans (eval_op₂_congr 3 rfl (eval_op₂_congr 9
      (eval_op₂_congr 3 rfl exy) rfl)) (listMapP_step_pair hM hf hfQ
        (comp_hom hM (pair_hom hM hx hw) hK)).symm)
  have hR₀ := listMapP_nil_at hM hP hA hf (idt_hom hM hP)
  have hR₁ := fun {X x y w : Tree} (hx : Hom M ρ x X P) (hy : Hom M ρ y X A)
    (hw : Hom M ρ w X (list A)) ↦ listMapP_cons_at hM hP hA hf hx hy hw
  exact listRec_param_unique hM hP hA hH hR hS (h₀.trans hR₀.symm) (step hH h₁) (step hR hR₁)

/-- The action of a list object with a parameter after the product of the parameters with the
action of the list object on an arrow is the action on the composite of the arrows. -/
theorem listMapP_map {f g P A B C : Tree} (hP : IsObj M ρ P) (hf : Hom M ρ f (prod P A) C)
    (hg : Hom M ρ g B A) :
    eval M ρ (comp (listMapP P A C f) (prodMapRight P (listMap g))) =
      eval M ρ (listMapP P B C (comp f (prodMapRight P g))) := by
  have hA := hg.isObj_cod
  have hB := hg.isObj_dom
  have hLA := isObj_list hM hA
  have hLB := isObj_list hM hB
  have hC := hf.isObj_cod
  have hm := listMap_hom hM hg
  have hR := listMapP_hom hM hP hA hf
  have hpm : Hom M ρ (prodMapRight P (listMap g)) (prod P (list B)) (prod P (list A)) :=
    (pair_hom hM (fst_hom hM hP hLB) (comp_hom hM (snd_hom hM hP hLB) hm)).congr
      (eval_prodMapRight P hm) rfl rfl
  have hpg : Hom M ρ (prodMapRight P g) (prod P B) (prod P A) :=
    (pair_hom hM (fst_hom hM hP hB) (comp_hom hM (snd_hom hM hP hB) hg)).congr
      (eval_prodMapRight P hg) rfl rfl
  have hf' := comp_hom hM hpg hf
  refine listMapP_unique hM hP hB hf' (comp_hom hM hpm hR) ?_ ?_
  · have hnb := comp_hom hM (bang_hom hM hP) (nil_hom hM hB)
    exact (comp_assoc hM (pair_hom hM (idt_hom hM hP) hnb) hpm hR).symm.trans
      ((eval_op₂_congr 3 rfl ((prodMapRight_pair hM (idt_hom hM hP) hnb hm).trans
        (eval_op₂_congr 9 rfl (listMap_nil_at hM hg hP)))).trans
          (listMapP_nil_at hM hP hA hf (idt_hom hM hP)))
  · intro X x y w hx hy hw
    have hcw := comp_hom hM (pair_hom hM hy hw) (cons_hom hM hB)
    refine (comp_assoc hM (pair_hom hM hx hcw) hpm hR).symm.trans ((eval_op₂_congr 3 rfl
      ((prodMapRight_pair hM hx hcw hm).trans (eval_op₂_congr 9 rfl
        (listMap_cons_at hM hg hy hw)))).trans ?_)
    refine (listMapP_cons_at hM hP hA hf hx (comp_hom hM hy hg) (comp_hom hM hw hm)).trans ?_
    refine eval_op₂_congr 3 rfl (eval_op₂_congr 9 ?_ ?_)
    · exact (eval_op₂_congr 3 rfl (prodMapRight_pair hM hx hy hg).symm).trans
        (comp_assoc hM (pair_hom hM hx hy) hpg hf)
    · exact (eval_op₂_congr 3 rfl (prodMapRight_pair hM hx hw hm).symm).trans
        (comp_assoc hM (pair_hom hM hx hw) hpm hR)

/-- The action of a list object with a parameter on an arrow that ignores the parameter is the
action of the list object after the list. -/
theorem listMapP_snd {g P A C : Tree} (hP : IsObj M ρ P) (hg : Hom M ρ g A C) :
    eval M ρ (listMapP P A C (comp g (snd P A))) =
      eval M ρ (comp (listMap g) (snd P (list A))) := by
  have hA := hg.isObj_dom
  have hL := isObj_list hM hA
  have hm := listMap_hom hM hg
  have hsL := snd_hom hM hP hL
  have hsA := snd_hom hM hP hA
  refine (listMapP_unique hM hP hA (comp_hom hM hsA hg) (comp_hom hM hsL hm) ?_ ?_).symm
  · have hnb := comp_hom hM (bang_hom hM hP) (nil_hom hM hA)
    have hq := pair_hom hM (idt_hom hM hP) hnb
    exact (comp_assoc hM hq hsL hm).symm.trans ((eval_op₂_congr 3 rfl
      (snd_pair hM (idt_hom hM hP) hnb)).trans (listMap_nil_at hM hg hP))
  · intro X x y w hx hy hw
    have hcw := comp_hom hM (pair_hom hM hy hw) (cons_hom hM hA)
    refine (comp_assoc hM (pair_hom hM hx hcw) hsL hm).symm.trans ((eval_op₂_congr 3 rfl
      (snd_pair hM hx hcw)).trans ((listMap_cons_at hM hg hy hw).trans ?_))
    refine eval_op₂_congr 3 rfl (eval_op₂_congr 9 ?_ ?_)
    · exact (eval_op₂_congr 3 rfl (snd_pair hM hx hy)).symm.trans
        (comp_assoc hM (pair_hom hM hx hy) hsA hg)
    · exact (eval_op₂_congr 3 rfl (snd_pair hM hx hw)).symm.trans
        (comp_assoc hM (pair_hom hM hx hw) hsL hm)

/-- The action of a list object with a parameter is natural in the parameter: after the product
of an arrow into the parameters with the identity, it is the action on the arrow after the
product of the arrow with the identity. -/
theorem listMapP_comp {f h P Y A C : Tree} (hP : IsObj M ρ P) (hA : IsObj M ρ A)
    (hf : Hom M ρ f (prod P A) C) (hh : Hom M ρ h Y P) :
    eval M ρ (comp (listMapP P A C f) (pair (comp h (fst Y (list A))) (snd Y (list A)))) =
      eval M ρ (listMapP Y A C (comp f (pair (comp h (fst Y A)) (snd Y A)))) := by
  have hY := hh.isObj_dom
  have hL := isObj_list hM hA
  have hR := listMapP_hom hM hP hA hf
  have hk := pair_hom hM (comp_hom hM (fst_hom hM hY hL) hh) (snd_hom hM hY hL)
  have hkA := pair_hom hM (comp_hom hM (fst_hom hM hY hA) hh) (snd_hom hM hY hA)
  refine listMapP_unique hM hY hA (comp_hom hM hkA hf) (comp_hom hM hk hR) ?_ ?_
  · have hnb := comp_hom hM (bang_hom hM hY) (nil_hom hM hA)
    have hq := pair_hom hM (idt_hom hM hY) hnb
    exact (comp_assoc hM hq hk hR).symm.trans ((eval_op₂_congr 3 rfl
      ((prodMapLeft_pair hM hh (idt_hom hM hY) hnb).trans
        (eval_op₂_congr 9 (comp_idt hM hh) rfl))).trans (listMapP_nil_at hM hP hA hf hh))
  · intro X x y w hx hy hw
    have hcw := comp_hom hM (pair_hom hM hy hw) (cons_hom hM hA)
    have hhx := comp_hom hM hx hh
    refine (comp_assoc hM (pair_hom hM hx hcw) hk hR).symm.trans ((eval_op₂_congr 3 rfl
      (prodMapLeft_pair hM hh hx hcw)).trans ((listMapP_cons_at hM hP hA hf hhx hy hw).trans ?_))
    refine eval_op₂_congr 3 rfl (eval_op₂_congr 9 ?_ ?_)
    · exact (eval_op₂_congr 3 rfl (prodMapLeft_pair hM hh hx hy).symm).trans
        (comp_assoc hM (pair_hom hM hx hy) hkA hf)
    · exact (eval_op₂_congr 3 rfl (prodMapLeft_pair hM hh hx hw).symm).trans
        (comp_assoc hM (pair_hom hM hx hw) hk hR)

/-- Evaluation after the exchanged pairing is the evaluation arrow of the parameters' product
with their exponential. -/
theorem evSwap_hom {P C : Tree} (hP : IsObj M ρ P) (hC : IsObj M ρ C) :
    Hom M ρ (comp (ev P C) (pair (snd P (exp P C)) (fst P (exp P C)))) (prod P (exp P C)) C :=
  comp_hom hM (pair_hom hM (snd_hom hM hP (isObj_exp hM hP hC))
    (fst_hom hM hP (isObj_exp hM hP hC))) (ev_hom hM hP hC)

/-- The uncurried step of the fold of a rose-tree object with a parameter is an arrow from the
product of a label and a list of functions on the parameters with the parameters. -/
theorem roseStepP_hom {P a C S : Tree} (hP : IsObj M ρ P) (ha : IsObj M ρ a)
    (hS : Hom M ρ S (prod P (prod a (list C))) C) :
    Hom M ρ (roseStepP P a C S) (prod (prod a (list (exp P C))) P) C := by
  have hC := hS.isObj_cod
  have hE := isObj_exp hM hP hC
  have hLE := isObj_list hM hE
  have hQ := isObj_prod hM ha hLE
  have hfQ := fst_hom hM hQ hP
  have hsQ := snd_hom hM hQ hP
  exact comp_hom hM (pair_hom hM hsQ (pair_hom hM (comp_hom hM hfQ (fst_hom hM ha hLE))
    (comp_hom hM (pair_hom hM hsQ (comp_hom hM hfQ (snd_hom hM ha hLE)))
      (listMapP_hom hM hP hE (evSwap_hom hM hP hC))))) hS

/-- The uncurried step of the fold of a rose-tree object with a parameter, at a label and a list
of functions paired with a parameter, is the step at the parameter, the label and the list of
the functions evaluated at the parameter. -/
theorem roseStepP_at {P a C S X l fs x : Tree} (hP : IsObj M ρ P) (ha : IsObj M ρ a)
    (hS : Hom M ρ S (prod P (prod a (list C))) C) (hl : Hom M ρ l X a)
    (hfs : Hom M ρ fs X (list (exp P C))) (hx : Hom M ρ x X P) :
    eval M ρ (comp (roseStepP P a C S) (pair (pair l fs) x)) =
      eval M ρ (comp S (pair x (pair l (comp (listMapP P (exp P C) C
        (comp (ev P C) (pair (snd P (exp P C)) (fst P (exp P C))))) (pair x fs))))) := by
  have hC := hS.isObj_cod
  have hE := isObj_exp hM hP hC
  have hLE := isObj_list hM hE
  have hQ := isObj_prod hM ha hLE
  have hfQ := fst_hom hM hQ hP
  have hsQ := snd_hom hM hQ hP
  have hfa := fst_hom hM ha hLE
  have hsa := snd_hom hM ha hLE
  have hLM := listMapP_hom hM hP hE (evSwap_hom hM hP hC)
  have hlf := pair_hom hM hl hfs
  have hq := pair_hom hM hlf hx
  have hps := pair_hom hM hsQ (comp_hom hM hfQ hsa)
  have hin := pair_hom hM (comp_hom hM hfQ hfa) (comp_hom hM hps hLM)
  have e₁ := fst_pair hM hlf hx
  have e₂ := snd_pair hM hlf hx
  have eP : eval M ρ (comp (pair (snd (prod a (list (exp P C))) P)
      (comp (snd a (list (exp P C))) (fst (prod a (list (exp P C))) P))) (pair (pair l fs) x)) =
      eval M ρ (pair x fs) :=
    (pair_comp hM hsQ (comp_hom hM hfQ hsa) hq).trans (eval_op₂_congr 9 e₂
      ((comp_assoc hM hq hfQ hsa).symm.trans ((eval_op₂_congr 3 rfl e₁).trans
        (snd_pair hM hl hfs))))
  refine (comp_assoc hM hq (pair_hom hM hsQ hin) hS).symm.trans (eval_op₂_congr 3 rfl ?_)
  refine (pair_comp hM hsQ hin hq).trans (eval_op₂_congr 9 e₂ ?_)
  refine (pair_comp hM (comp_hom hM hfQ hfa) (comp_hom hM hps hLM) hq).trans
    (eval_op₂_congr 9 ?_ ?_)
  · exact (comp_assoc hM hq hfQ hfa).symm.trans ((eval_op₂_congr 3 rfl e₁).trans
      (fst_pair hM hl hfs))
  · exact (comp_assoc hM hq hps hLM).symm.trans (eval_op₂_congr 3 rfl eP)

/-- Two arrows into the exponential of the parameters whose uncurryings are equal are equal. -/
theorem eq_of_uncurry {k₁ k₂ D P C : Tree} (hP : IsObj M ρ P) (hC : IsObj M ρ C)
    (hk₁ : Hom M ρ k₁ D (exp P C)) (hk₂ : Hom M ρ k₂ D (exp P C))
    (h : eval M ρ (comp (ev P C) (pair (comp k₁ (fst D P)) (snd D P))) =
      eval M ρ (comp (ev P C) (pair (comp k₂ (fst D P)) (snd D P)))) :
    eval M ρ k₁ = eval M ρ k₂ :=
  (curry_eta hM hP hC hk₁).symm.trans ((eval_op₃_congr 24 rfl rfl h).trans (curry_eta hM hP hC hk₂))

/-- An arrow from the product of the parameters with an object is the uncurrying of its
currying over the parameters with the factors exchanged. -/
theorem uncurry_curry_swap {H P D C : Tree} (hP : IsObj M ρ P) (hD : IsObj M ρ D)
    (hH : Hom M ρ H (prod P D) C) :
    eval M ρ (comp (ev P C) (pair (comp (curry D P (comp H (pair (snd D P) (fst D P))))
      (snd P D)) (fst P D))) = eval M ρ H := by
  have hsw := pair_hom hM (snd_hom hM hD hP) (fst_hom hM hD hP)
  have hfP := fst_hom hM hP hD
  have hsP := snd_hom hM hP hD
  have hq := pair_hom hM hsP hfP
  exact (ev_curry_pair hM hD hP (comp_hom hM hsw hH) hsP hfP).trans
    ((comp_assoc hM hq hsw hH).symm.trans ((eval_op₂_congr 3 rfl
      ((swap_pair hM hsP hfP).trans (pair_fst_snd hM hP hD))).trans (comp_idt hM hH)))

omit hM in
/-- The fold of a rose-tree object with a parameter respects the value of its step, where the fold
without the parameter does. -/
theorem eval_roseRecP_congr {F : Tree → Tree}
    (hFc : ∀ {s s' : Tree}, eval M ρ s = eval M ρ s' → eval M ρ (F s) = eval M ρ (F s'))
    (P a t C : Tree) {S S' : Tree} (h : eval M ρ S = eval M ρ S') :
    eval M ρ (roseRecP F P a t C S) = eval M ρ (roseRecP F P a t C S') :=
  eval_op₂_congr 3 rfl (eval_op₂_congr 9 (eval_op₂_congr 3
    (hFc (eval_op₃_congr 24 rfl rfl (eval_op₂_congr 3 h rfl))) rfl) rfl)

section RoseFold

variable {F : Tree → Tree} {nd t a : Tree} (hF : RoseFold M ρ F nd t a)
include hF

/-- The curried step of the fold of a rose-tree object with a parameter is an arrow into the
exponential of the parameters. -/
theorem roseStepP_curry_hom {P C S : Tree} (hP : IsObj M ρ P)
    (hS : Hom M ρ S (prod P (prod a (list C))) C) :
    Hom M ρ (curry (prod a (list (exp P C))) P (roseStepP P a C S))
      (prod a (list (exp P C))) (exp P C) :=
  curry_hom hM (isObj_prod hM hF.isObj_lab (isObj_list hM (isObj_exp hM hP hS.isObj_cod))) hP
    (roseStepP_hom hM hP hF.isObj_lab hS)

/-- The fold of a rose-tree object with a parameter is an arrow from the product of the
parameters with the rose-tree object. -/
theorem roseRecP_hom {P C S : Tree} (hP : IsObj M ρ P)
    (hS : Hom M ρ S (prod P (prod a (list C))) C) :
    Hom M ρ (roseRecP F P a t C S) (prod P t) C := by
  have hC := hS.isObj_cod
  have ht := hF.node_hom.isObj_cod
  have hFc := hF.hom (roseStepP_curry_hom hM hF hP hS)
  exact comp_hom hM (pair_hom hM (comp_hom hM (snd_hom hM hP ht) hFc) (fst_hom hM hP ht))
    (ev_hom hM hP hC)

/-- The fold of a rose-tree object with a parameter, at a parameter paired with a tree, is the
fold into the exponential at the tree evaluated at the parameter. -/
theorem roseRecP_at {P C S X x v : Tree} (hP : IsObj M ρ P)
    (hS : Hom M ρ S (prod P (prod a (list C))) C) (hx : Hom M ρ x X P) (hv : Hom M ρ v X t) :
    eval M ρ (comp (roseRecP F P a t C S) (pair x v)) =
      eval M ρ (comp (ev P C) (pair (comp (F (curry (prod a (list (exp P C))) P
        (roseStepP P a C S))) v) x)) := by
  have hC := hS.isObj_cod
  have ht := hF.node_hom.isObj_cod
  have hFc := hF.hom (roseStepP_curry_hom hM hF hP hS)
  have hsP := snd_hom hM hP ht
  have hfP := fst_hom hM hP ht
  have hxv := pair_hom hM hx hv
  exact (comp_assoc hM hxv (pair_hom hM (comp_hom hM hsP hFc) hfP) (ev_hom hM hP hC)).symm.trans
    (eval_op₂_congr 3 rfl ((pair_comp hM (comp_hom hM hsP hFc) hfP hxv).trans
      (eval_op₂_congr 9 ((comp_assoc hM hxv hsP hFc).symm.trans
        (eval_op₂_congr 3 rfl (snd_pair hM hx hv))) (fst_pair hM hx hv))))

/-- Evaluation, after the exchanged pairing, after the product of the parameters with an arrow
into their exponential, is the arrow's uncurrying. -/
theorem evSwap_prodMapRight {P C k : Tree} (hP : IsObj M ρ P) (hC : IsObj M ρ C)
    (hk : Hom M ρ k t (exp P C)) :
    eval M ρ (comp (comp (ev P C) (pair (snd P (exp P C)) (fst P (exp P C))))
      (prodMapRight P k)) = eval M ρ (comp (ev P C) (pair (comp k (snd P t)) (fst P t))) := by
  have ht := hF.node_hom.isObj_cod
  have hE := hk.isObj_cod
  have hfP := fst_hom hM hP ht
  have hks := comp_hom hM (snd_hom hM hP ht) hk
  have hsw := pair_hom hM (snd_hom hM hP hE) (fst_hom hM hP hE)
  have hev := ev_hom hM hP hC
  exact (eval_op₂_congr 3 rfl (eval_prodMapRight P hk)).trans
    ((comp_assoc hM (pair_hom hM hfP hks) hsw hev).symm.trans
      (eval_op₂_congr 3 rfl (swap_pair hM hfP hks)))

/-- The list of the functions an arrow into the parameters' exponential gives the trees of a list,
each evaluated at a parameter, is the action with the parameter of the arrow's uncurrying. -/
theorem listMapP_evSwap {P C k X x cs : Tree} (hP : IsObj M ρ P) (hC : IsObj M ρ C)
    (hk : Hom M ρ k t (exp P C)) (hx : Hom M ρ x X P) (hcs : Hom M ρ cs X (list t)) :
    eval M ρ (comp (listMapP P (exp P C) C
      (comp (ev P C) (pair (snd P (exp P C)) (fst P (exp P C))))) (pair x (comp (listMap k) cs))) =
      eval M ρ (comp (listMapP P t C (comp (ev P C) (pair (comp k (snd P t)) (fst P t))))
        (pair x cs)) := by
  have ht := hF.node_hom.isObj_cod
  have hE := isObj_exp hM hP hC
  have hm := listMap_hom hM hk
  have hLM := listMapP_hom hM hP hE (evSwap_hom hM hP hC)
  have hpP : Hom M ρ (prodMapRight P (listMap k)) (prod P (list t)) (prod P (list (exp P C))) :=
    (pair_hom hM (fst_hom hM hP (isObj_list hM ht))
      (comp_hom hM (snd_hom hM hP (isObj_list hM ht)) hm)).congr
      (eval_prodMapRight P hm) rfl rfl
  exact (eval_op₂_congr 3 rfl (prodMapRight_pair hM hx hcs hm).symm).trans
    ((comp_assoc hM (pair_hom hM hx hcs) hpP hLM).trans (eval_op₂_congr 3
      ((listMapP_map hM hP (evSwap_hom hM hP hC) hk).trans
        (eval_listMapP_congr P t C (evSwap_prodMapRight hM hF hP hC hk))) rfl))

/-- The fold of a rose-tree object with a parameter, at a parameter paired with a construction,
is the step at the parameter, the label and the list of the fold's values at the children. -/
theorem roseRecP_node_at {P C S X x l cs : Tree} (hP : IsObj M ρ P)
    (hS : Hom M ρ S (prod P (prod a (list C))) C) (hx : Hom M ρ x X P) (hl : Hom M ρ l X a)
    (hcs : Hom M ρ cs X (list t)) :
    eval M ρ (comp (roseRecP F P a t C S) (pair x (comp nd (pair l cs)))) =
      eval M ρ (comp S (pair x (pair l
        (comp (listMapP P t C (roseRecP F P a t C S)) (pair x cs))))) := by
  have hC := hS.isObj_cod
  have ha := hF.isObj_lab
  have ht := hF.node_hom.isObj_cod
  have hE := isObj_exp hM hP hC
  have hLE := isObj_list hM hE
  have hQ := isObj_prod hM ha hLE
  have hT := roseStepP_hom hM hP ha hS
  have hSt := roseStepP_curry_hom hM hF hP hS
  have hFc := hF.hom hSt
  have hm := listMap_hom hM hFc
  have hlc := pair_hom hM hl hcs
  have hmc := comp_hom hM hcs hm
  have hlm := pair_hom hM hl hmc
  have hLM := listMapP_hom hM hP hE (evSwap_hom hM hP hC)
  have hpm : Hom M ρ (prodMapRight a (listMap (F (curry (prod a (list (exp P C))) P
      (roseStepP P a C S))))) (prod a (list t)) (prod a (list (exp P C))) :=
    (pair_hom hM (fst_hom hM ha (isObj_list hM ht))
      (comp_hom hM (snd_hom hM ha (isObj_list hM ht)) hm)).congr
      (eval_prodMapRight a hm) rfl rfl
  -- the fold into the exponential at a construction is the curried step at its action on the
  -- children
  have eF : eval M ρ (comp (F (curry (prod a (list (exp P C))) P (roseStepP P a C S)))
      (comp nd (pair l cs))) = eval M ρ (comp (curry (prod a (list (exp P C))) P
        (roseStepP P a C S)) (pair l (comp (listMap (F (curry (prod a (list (exp P C))) P
          (roseStepP P a C S)))) cs))) :=
    (comp_assoc hM hlc hF.node_hom hFc).trans ((eval_op₂_congr 3 (hF.node hSt) rfl).trans
      ((comp_assoc hM hlc hpm hSt).symm.trans
        (eval_op₂_congr 3 rfl (prodMapRight_pair hM hl hcs hm))))
  -- the list of the children's functions evaluated at the parameter is the fold's action
  have eL := listMapP_evSwap hM hF hP hC hFc hx hcs
  refine (roseRecP_at hM hF hP hS hx (comp_hom hM hlc hF.node_hom)).trans ?_
  refine (eval_op₂_congr 3 rfl (eval_op₂_congr 9 eF rfl)).trans ?_
  refine (ev_curry_pair hM hQ hP hT hlm hx).trans ?_
  refine (roseStepP_at hM hP ha hS hl (comp_hom hM hcs hm) hx).trans ?_
  exact eval_op₂_congr 3 rfl (eval_op₂_congr 9 rfl (eval_op₂_congr 9 rfl eL))


/-- The uniqueness of the fold of a rose-tree object with a parameter: an arrow from the product of
the parameters with the rose-tree object that is, at a construction, the step at the parameter,
the label and the list of its values at the children, is the fold with the parameter. -/
theorem roseRecP_unique {H P C S : Tree} (hP : IsObj M ρ P)
    (hS : Hom M ρ S (prod P (prod a (list C))) C) (hH : Hom M ρ H (prod P t) C)
    (h₁ : ∀ {X x l cs : Tree}, Hom M ρ x X P → Hom M ρ l X a → Hom M ρ cs X (list t) →
      eval M ρ (comp H (pair x (comp nd (pair l cs)))) =
        eval M ρ (comp S (pair x (pair l (comp (listMapP P t C H) (pair x cs)))))) :
    eval M ρ H = eval M ρ (roseRecP F P a t C S) := by
  have hC := hS.isObj_cod
  have ha := hF.isObj_lab
  have ht := hF.node_hom.isObj_cod
  have hLt := isObj_list hM ht
  have hD := isObj_prod hM ha hLt
  have hE := isObj_exp hM hP hC
  have hQ := isObj_prod hM ha (isObj_list hM hE)
  have hT := roseStepP_hom hM hP ha hS
  have hSt := roseStepP_curry_hom hM hF hP hS
  have hsw := pair_hom hM (snd_hom hM ht hP) (fst_hom hM ht hP)
  have hHsw := comp_hom hM hsw hH
  have hK := curry_hom hM ht hP hHsw
  have eH := uncurry_curry_swap hM hP ht hH
  have hm := listMap_hom hM hK
  have hfD := fst_hom hM hD hP
  have hx := snd_hom hM hD hP
  have hl := comp_hom hM hfD (fst_hom hM ha hLt)
  have hcs := comp_hom hM hfD (snd_hom hM ha hLt)
  have elc : eval M ρ (pair (comp (fst a (list t)) (fst (prod a (list t)) P))
      (comp (snd a (list t)) (fst (prod a (list t)) P))) = eval M ρ (fst (prod a (list t)) P) :=
    pair_eta hM ha hLt hfD
  have hpm : Hom M ρ (prodMapRight a (listMap (curry t P (comp H (pair (snd t P) (fst t P))))))
      (prod a (list t)) (prod a (list (exp P C))) :=
    (pair_hom hM (fst_hom hM ha hLt) (comp_hom hM (snd_hom hM ha hLt) hm)).congr
      (eval_prodMapRight a hm) rfl rfl
  -- the currying of the arrow satisfies the fold's equation
  have hnode : eval M ρ (comp (curry t P (comp H (pair (snd t P) (fst t P)))) nd) =
      eval M ρ (comp (curry (prod a (list (exp P C))) P (roseStepP P a C S))
        (prodMapRight a (listMap (curry t P (comp H (pair (snd t P) (fst t P))))))) := by
    have hk₁ := comp_hom hM hF.node_hom hK
    have hk₂ := comp_hom hM hpm hSt
    refine eq_of_uncurry hM hP hC hk₁ hk₂ ?_
    have hnf := comp_hom hM hfD hF.node_hom
    have hpf := comp_hom hM hfD hpm
    have eL : eval M ρ (comp (ev P C) (pair (comp (comp (curry t P
        (comp H (pair (snd t P) (fst t P)))) nd) (fst (prod a (list t)) P))
        (snd (prod a (list t)) P))) = eval M ρ (comp S (pair (snd (prod a (list t)) P)
          (pair (comp (fst a (list t)) (fst (prod a (list t)) P))
            (comp (listMapP P t C H) (pair (snd (prod a (list t)) P)
              (comp (snd a (list t)) (fst (prod a (list t)) P))))))) := by
      refine (eval_op₂_congr 3 rfl (eval_op₂_congr 9
        (comp_assoc hM hfD hF.node_hom hK).symm rfl)).trans ?_
      refine (ev_curry_pair hM ht hP hHsw hnf hx).trans ?_
      refine (comp_assoc hM (pair_hom hM hnf hx) hsw hH).symm.trans ?_
      refine (eval_op₂_congr 3 rfl (swap_pair hM hnf hx)).trans ?_
      refine (eval_op₂_congr 3 rfl (eval_op₂_congr 9 rfl
        (eval_op₂_congr 3 rfl elc.symm))).trans ?_
      exact h₁ hx hl hcs
    refine eL.trans (Eq.symm ?_)
    refine (eval_op₂_congr 3 rfl (eval_op₂_congr 9 (comp_assoc hM hfD hpm hSt).symm rfl)).trans ?_
    refine (ev_curry_pair hM hQ hP hT hpf hx).trans ?_
    refine (eval_op₂_congr 3 rfl (eval_op₂_congr 9 ((eval_op₂_congr 3 rfl elc.symm).trans
      (prodMapRight_pair hM hl hcs hm)) rfl)).trans ?_
    refine (roseStepP_at hM hP ha hS hl (comp_hom hM hcs hm) hx).trans ?_
    exact eval_op₂_congr 3 rfl (eval_op₂_congr 9 rfl (eval_op₂_congr 9 rfl
      ((listMapP_evSwap hM hF hP hC hK hx hcs).trans
        (eval_op₂_congr 3 (eval_listMapP_congr P t C eH) rfl))))
  have hKF := hF.unique hSt hK hnode
  exact eH.symm.trans (eval_op₂_congr 3 rfl (eval_op₂_congr 9 (eval_op₂_congr 3 hKF rfl) rfl))

/-- The fold of a rose-tree object with a parameter, whose step does not depend on the parameter,
is the fold without the parameter after the tree. -/
theorem roseRecP_const {S P C X x v : Tree} (hP : IsObj M ρ P)
    (hS : Hom M ρ S (prod a (list C)) C) (hx : Hom M ρ x X P) (hv : Hom M ρ v X t) :
    eval M ρ (comp (roseRecP F P a t C (comp S (snd P (prod a (list C))))) (pair x v)) =
      eval M ρ (comp (F S) v) := by
  have hC := hS.isObj_cod
  have ha := hF.isObj_lab
  have ht := hF.node_hom.isObj_cod
  have hD := isObj_prod hM ha (isObj_list hM hC)
  have hsD := snd_hom hM hP hD
  have hS' := comp_hom hM hsD hS
  have hFS := hF.hom hS
  have hst := snd_hom hM hP ht
  have hH := comp_hom hM hst hFS
  have hm := listMap_hom hM hFS
  have hR := roseRecP_hom hM hF hP hS'
  have hRH := roseRecP_unique hM hF hP hS' hH fun {X x l cs} hx hl hcs ↦ by
    have hlc := pair_hom hM hl hcs
    have hv := comp_hom hM hlc hF.node_hom
    have hpm : Hom M ρ (prodMapRight a (listMap (F S))) (prod a (list t)) (prod a (list C)) :=
      (pair_hom hM (fst_hom hM ha (isObj_list hM ht))
        (comp_hom hM (snd_hom hM ha (isObj_list hM ht)) hm)).congr
        (eval_prodMapRight a hm) rfl rfl
    have hLM := listMapP_hom hM hP ht hH
    have hlm := pair_hom hM hl (comp_hom hM (pair_hom hM hx hcs) hLM)
    refine (comp_assoc hM (pair_hom hM hx hv) hst hFS).symm.trans ?_
    refine (eval_op₂_congr 3 rfl (snd_pair hM hx hv)).trans ?_
    refine (comp_assoc hM hlc hF.node_hom hFS).trans ?_
    refine (eval_op₂_congr 3 (hF.node hS) rfl).trans ?_
    refine (comp_assoc hM hlc hpm hS).symm.trans ?_
    refine (eval_op₂_congr 3 rfl (prodMapRight_pair hM hl hcs hm)).trans ?_
    refine Eq.symm ((comp_assoc hM (pair_hom hM hx hlm) hsD hS).symm.trans
      ((eval_op₂_congr 3 rfl (snd_pair hM hx hlm)).trans (eval_op₂_congr 3 rfl
        (eval_op₂_congr 9 rfl ?_))))
    exact (eval_op₂_congr 3 (listMapP_snd hM hP hFS) rfl).trans
      ((comp_assoc hM (pair_hom hM hx hcs) (snd_hom hM hP (isObj_list hM ht)) hm).symm.trans
        (eval_op₂_congr 3 rfl (snd_pair hM hx hcs)))
  exact (eval_op₂_congr 3 hRH.symm rfl).trans
    ((comp_assoc hM (pair_hom hM hx hv) hst hFS).symm.trans
      (eval_op₂_congr 3 rfl (snd_pair hM hx hv)))

/-- The fold of a rose-tree object with a parameter is natural in the parameter: after the
product of an arrow into the parameters with the identity, it is the fold whose step is after
the product of the arrow with the identity. -/
theorem roseRecP_comp {S P Y C h : Tree} (hP : IsObj M ρ P)
    (hS : Hom M ρ S (prod P (prod a (list C))) C) (hh : Hom M ρ h Y P) :
    eval M ρ (comp (roseRecP F P a t C S) (pair (comp h (fst Y t)) (snd Y t))) =
      eval M ρ (roseRecP F Y a t C (comp S (pair (comp h (fst Y (prod a (list C))))
        (snd Y (prod a (list C)))))) := by
  have hC := hS.isObj_cod
  have ha := hF.isObj_lab
  have ht := hF.node_hom.isObj_cod
  have hY := hh.isObj_dom
  have hD := isObj_prod hM ha (isObj_list hM hC)
  have hR := roseRecP_hom hM hF hP hS
  have hk := pair_hom hM (comp_hom hM (fst_hom hM hY ht) hh) (snd_hom hM hY ht)
  have hkD := pair_hom hM (comp_hom hM (fst_hom hM hY hD) hh) (snd_hom hM hY hD)
  have hS' := comp_hom hM hkD hS
  refine roseRecP_unique hM hF hY hS' (comp_hom hM hk hR) fun {X x l cs} hx hl hcs ↦ ?_
  have hlc := pair_hom hM hl hcs
  have hv := comp_hom hM hlc hF.node_hom
  have hhx := comp_hom hM hx hh
  have hLM := listMapP_hom hM hY ht (comp_hom hM hk hR)
  have hlm := pair_hom hM hl (comp_hom hM (pair_hom hM hx hcs) hLM)
  refine (comp_assoc hM (pair_hom hM hx hv) hk hR).symm.trans ((eval_op₂_congr 3 rfl
    (prodMapLeft_pair hM hh hx hv)).trans ((roseRecP_node_at hM hF hP hS hhx hl hcs).trans ?_))
  refine Eq.symm ((comp_assoc hM (pair_hom hM hx hlm) hkD hS).symm.trans
    ((eval_op₂_congr 3 rfl (prodMapLeft_pair hM hh hx hlm)).trans (eval_op₂_congr 3 rfl
      (eval_op₂_congr 9 rfl (eval_op₂_congr 9 rfl ?_)))))
  have hLMP := listMapP_hom hM hP ht hR
  have hkL := pair_hom hM (comp_hom hM (fst_hom hM hY (isObj_list hM ht)) hh)
    (snd_hom hM hY (isObj_list hM ht))
  exact (eval_op₂_congr 3 (listMapP_comp hM hP ht hR hh).symm rfl).trans
    ((comp_assoc hM (pair_hom hM hx hcs) hkL hLMP).symm.trans
      (eval_op₂_congr 3 rfl (prodMapLeft_pair hM hh hx hcs)))

/-- The fold of a rose-tree object with a parameter at an arrow into the parameters and a tree is
the fold with the arrow's domain as parameter, its step after the arrow, at the identity and the
tree. -/
theorem roseRecP_pair {S P X C u m : Tree} (hP : IsObj M ρ P)
    (hS : Hom M ρ S (prod P (prod a (list C))) C) (hu : Hom M ρ u X P) (hm : Hom M ρ m X t) :
    eval M ρ (comp (roseRecP F P a t C S) (pair u m)) =
      eval M ρ (comp (roseRecP F X a t C (comp S (pair (comp u (fst X (prod a (list C))))
        (snd X (prod a (list C)))))) (pair (idt X) m)) := by
  have hX := hu.isObj_dom
  have ht := hF.node_hom.isObj_cod
  have hq := pair_hom hM (comp_hom hM (fst_hom hM hX ht) hu) (snd_hom hM hX ht)
  have hR := roseRecP_hom hM hF hP hS
  exact (eval_op₂_congr 3 rfl ((eval_op₂_congr 9 (comp_idt hM hu).symm rfl).trans
    (prodMapLeft_pair hM hu (idt_hom hM hX) hm).symm)).trans
    ((comp_assoc hM (pair_hom hM (idt_hom hM hX) hm) hq hR).trans
      (eval_op₂_congr 3 (roseRecP_comp hM hF hP hS hu) rfl))

end RoseFold

end Parameters

end Geb.FreeTopos

end
