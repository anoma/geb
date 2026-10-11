/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.PartialHorn.Completeness

set_option doc.verso true in
/-!
# Initiality of the closed term model

The interpretation of a closed, derivably defined term in a model descends to its class modulo
derivable equality. This is the unique homomorphism from the closed term model to that model,
the initial-model theorem of \[PalmgrenVickers2007\], Theorem 22.

## Main definitions

* {lit}`ModelHom` — sort-preserving maps preserving defined operations.
* {lit}`TermModel.interpret` — interpretation of closed term classes.

## Main statements

* {lit}`TermModel.existsUnique_hom` — the closed term model has a unique homomorphism
  to each model of the theory.

## References

* \[PalmgrenVickers2007\], Theorem 22.

## Tags

partial Horn logic, initial model, term model
-/

set_option doc.verso true

@[expose] public section

namespace Geb.PartialHorn

universe u v

variable {S : Sig}

/-- A homomorphism preserves sorts and the values of defined operations. -/
@[ext] structure ModelHom (M : Model.{u} S) (N : Model.{v} S) : Type (max u v) where
  /-- The map of sorted values. -/
  toFun : M.Val → N.Val
  /-- The map preserves each sort. -/
  sort_eq : ∀ w, (toFun w).1 = w.1
  /-- The map preserves every defined application of an operation. -/
  map_op : ∀ k args w, M.op k args = Part.some w →
    N.op k (args.map toFun) = Part.some (toFun w)

namespace ModelHom

variable {M : Model.{u} S} {N : Model.{v} S} (f : ModelHom M N)

/-- The action of a homomorphism on one sort. -/
def app (s : ℕ) (a : M.Car s) : N.Car s :=
  cast (congrArg N.Car (f.sort_eq ⟨s, a⟩)) (f.toFun ⟨s, a⟩).2

/-- The sorted-value map agrees with the map on each sort. -/
theorem toFun_mk (s : ℕ) (a : M.Car s) : f.toFun ⟨s, a⟩ = ⟨s, f.app s a⟩ :=
  Sigma.ext (f.sort_eq ⟨s, a⟩) (cast_heq _ _).symm

/-- Homomorphisms preserve the evaluation of defined closed terms. -/
theorem map_closed : ∀ t : Tree, ∀ w, eval M [] t = Part.some w →
    eval N [] t = Part.some (f.toFun w) :=
  RoseTree.ind fun l cs ih w hw ↦ by
    rcases l with _ | k
    · rcases cs with _ | ⟨i, _ | ⟨j, cs⟩⟩
      · simp [eval, RoseTree.para_node] at hw
      · obtain ⟨-, h⟩ := eval_node_zero_eq_some.mp hw
        simp at h
      · simp [eval, RoseTree.para_node] at hw
    · rw [eval_node_succ] at hw ⊢
      obtain ⟨vs, hvs, hop⟩ := part_bind_eq_some_iff.mp hw
      have hs := (mapM_part_eq_some_iff _ _).mp hvs
      have hlen : cs.length = vs.length := by simpa using congrArg List.length hs
      have hv : cs.map (eval N []) = (vs.map f.toFun).map Part.some := by
        refine List.ext_getElem (by simp [hlen]) fun i hi hj ↦ ?_
        have hi' : i < cs.length := by simpa using hi
        have hj' : i < vs.length := hlen ▸ hi'
        have he := congrArg (·[i]?) hs
        simp only [List.getElem?_map, List.getElem?_eq_getElem hi',
          List.getElem?_eq_getElem hj', Option.map_some, Option.some.injEq] at he
        simp only [List.getElem_map]
        exact ih _ (List.getElem_mem hi') _ he
      rw [(mapM_part_eq_some_iff _ _).mpr hv, Part.bind_some]
      exact f.map_op k vs w hop

end ModelHom

namespace TermModel

variable {T : Theory} (M : Model.{v} T.sig) (hM : IsModel T M)

include hM

/-- A derivable closed equation holds in every model. -/
theorem holds_closed {q : Eqn} (h : Derivable T #[] [] [] q) : q.Holds M [] := by
  obtain ⟨c, hc⟩ := h
  exact check_sound (List.prefix_refl _) hM (by simp) c [] [] q hc [] rfl (by simp)

/-- A derivably defined closed term is defined in every model. -/
theorem dom_closed {t : Tree} (h : Derivable T #[] [] [] ⟨t, t⟩) : (eval M [] t).Dom := by
  obtain ⟨w, hw, -⟩ := holds_closed M hM h
  exact (Part.eq_some_iff.mp hw).1

/-- Interpretation of a representative of the closed term model. -/
def interpretRep (r : Rep T #[] [] []) : M.Val :=
  (eval M [] r.1.2).get (dom_closed M hM r.2.2)

/-- A representative evaluates to its interpretation. -/
theorem eval_interpretRep (r : Rep T #[] [] []) :
    eval M [] r.1.2 = Part.some (interpretRep M hM r) := (Part.some_get _).symm

/-- Interpretation preserves the sort of a representative. -/
theorem interpretRep_sort (r : Rep T #[] [] []) : (interpretRep M hM r).1 = r.1.1 := by
  exact sort_eval (M := M) (ρ := []) rfl r.1.2 r.2.1 (eval_interpretRep M hM r)

/-- Derivably equal representatives have equal interpretations. -/
theorem interpretRep_respects (r s : Rep T #[] [] []) (h : r ≈ s) :
    interpretRep M hM r = interpretRep M hM s := by
  obtain ⟨w, hr, hs⟩ := holds_closed M hM h.2
  exact Part.some_inj.mp ((eval_interpretRep M hM r).symm.trans
    (hr.trans (hs.symm.trans (eval_interpretRep M hM s))))

/-- Interpretation on classes of closed, defined terms. -/
def interpretCls : Cls T #[] [] [] → M.Val :=
  Quotient.lift (interpretRep M hM) (interpretRep_respects M hM)

/-- Interpretation preserves the sort of a term class. -/
theorem interpretCls_sort (w : Cls T #[] [] []) : (interpretCls M hM w).1 = w.sort :=
  Quotient.inductionOn w (interpretRep_sort M hM)

/-- Interpretation on sorted values of the closed term model. -/
def interpret (w : (termModel T #[] [] []).Val) : M.Val := interpretCls M hM w.2.1

/-- Interpretation preserves sorts. -/
theorem interpret_sort (w : (termModel T #[] [] []).Val) : (interpret M hM w).1 = w.1 :=
  (interpretCls_sort M hM w.2.1).trans w.2.2

/-- Interpretation of a class presented as a sorted value. -/
theorem interpret_val (r : Rep T #[] [] []) :
    interpret M hM (val ⟦r⟧) = interpretRep M hM r := rfl

/-- Interpretation commutes with the evaluation of closed terms in the term model. -/
theorem eval_interpret {t : Tree} {w : (termModel T #[] [] []).Val}
    (hw : eval (termModel T #[] [] []) [] t = Part.some w) :
    eval M [] t = Part.some (interpret M hM w) := by
  change eval (termModel T #[] [] []) (generic T #[] [] []) t = Part.some w at hw
  obtain ⟨s, hs, hd, rfl⟩ := eq_of_eval_generic t hw
  exact eval_interpretRep M hM ⟨(s, t), hs, hd⟩

/-- Interpretation preserves all defined operations. -/
theorem interpret_op (k : ℕ) (args : List (termModel T #[] [] []).Val)
    (w : (termModel T #[] [] []).Val) (hw : (termModel T #[] [] []).op k args = Part.some w) :
    M.op k (args.map (interpret M hM)) = Part.some (interpret M hM w) := by
  obtain ⟨rs, rfl⟩ := exists_reps args
  have hs : (terms rs).map (eval (termModel T #[] [] []) []) =
      (rs.map fun r ↦ val ⟦r⟧).map Part.some := by
    simp only [terms, List.map_map]
    exact List.map_congr_left fun r _ ↦ eval_generic _ r.2.1 r.2.2
  have ht : (terms rs).map (eval M []) =
      ((rs.map fun r ↦ val ⟦r⟧).map (interpret M hM)).map Part.some := by
    simp only [terms, List.map_map]
    exact List.map_congr_left fun r _ ↦ eval_interpretRep M hM r
  have he : eval (termModel T #[] [] []) [] (op k (terms rs)) = Part.some w := by
    rw [eval_op, (mapM_part_eq_some_iff _ _).mpr hs, Part.bind_some]
    exact hw
  have he' := eval_interpret M hM he
  rwa [eval_op, (mapM_part_eq_some_iff _ _).mpr ht, Part.bind_some] at he'

/-- The homomorphism interpreting closed syntax in a model. -/
def interpretHom : ModelHom (termModel T #[] [] []) M where
  toFun := interpret M hM
  sort_eq := interpret_sort M hM
  map_op := interpret_op M hM

/-- Every homomorphism from closed syntax is its interpretation. -/
theorem interpretHom_unique (f : ModelHom (termModel T #[] [] []) M) :
    f = interpretHom M hM := by
  apply ModelHom.ext
  funext w
  obtain ⟨s, c, hc⟩ := w
  subst s
  change f.toFun (val c) = interpret M hM (val c)
  refine Quotient.inductionOn c fun r ↦ ?_
  have he : eval (termModel T #[] [] []) [] r.1.2 = Part.some (val ⟦r⟧) :=
    eval_generic _ r.2.1 r.2.2
  exact Part.some_inj.mp ((f.map_closed _ _ he).symm.trans (eval_interpretRep M hM r))

/-- The closed term model admits exactly one homomorphism into every model of its theory. -/
theorem existsUnique_hom : ∃! _f : ModelHom (termModel T #[] [] []) M, True :=
  ⟨interpretHom M hM, trivial, fun f _ ↦ interpretHom_unique M hM f⟩

end TermModel

end Geb.PartialHorn

end
