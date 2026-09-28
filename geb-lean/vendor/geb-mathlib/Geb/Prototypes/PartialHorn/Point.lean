/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.PartialHorn.Definitional

set_option doc.verso true in
/-!
# The one-point model

The model of a signature with one value of each sort, at which every operation of the signature
is defined, with its result sort: the terminal model. A well-sorted term's value in it is the
value of its sort ({lit}`eval_point`), so that every equation between two terms of one sort
holds in it, and it is a model of every theory whose axioms' conclusions equate terms of one sort
({lit}`isModel_point`). Every extension of such a theory by well-formed definitions is one
({lit}`sidesSorted_extendAll`).

## Main definitions

* {lit}`pointModel` — the one-point model of a signature.
* {lit}`SidesSorted` — a sequent's conclusion equates two terms of one sort.

## Main statements

* {lit}`eval_point` — a well-sorted term's value is its sort's.
* {lit}`isModel_point` — the one-point model is a model of a theory of such axioms.
* {lit}`sidesSorted_extendAll` — the extensions by well-formed definitions keep the property.

## Tags

partial Horn logic, terminal model, many-sorted signature
-/

set_option doc.verso true

@[expose] public section

namespace Geb.PartialHorn

open scoped FinEnum

/-- The one-point model of a signature: one value of each sort, and each operation of the
signature defined everywhere, with its result sort. -/
def pointModel (S : Sig) : Model.{0} S where
  Car _ := Unit
  op k _ := match S[k]? with
    | some o => Part.some ⟨o.2, ()⟩
    | none => Part.none
  op_sort {k _ w} hw := by
    split at hw
    · rename_i o ho
      rw [ho, Option.map_some, Part.mem_some_iff.mp hw]
    · exact absurd hw (Part.notMem_none w)

/-- A term of a sort in the one-point model's signature has the value of its sort, at every
assignment of the context's sorts. -/
theorem eval_point {S : Sig} {Γ : List ℕ} {ρ : List (pointModel S).Val}
    (hρ : ρ.map Sigma.fst = Γ) :
    ∀ t : Tree, ∀ {s : ℕ}, sortOf S Γ t = some s → eval (pointModel S) ρ t = Part.some ⟨s, ()⟩ :=
  RoseTree.ind fun l cs ih s hs ↦ by
    rcases l with _ | k
    · rcases cs with _ | ⟨i, _ | ⟨j, cs⟩⟩
      · simp [sortOf] at hs
      rotate_left
      · simp [sortOf] at hs
      obtain ⟨hc, hs⟩ := sortOf_node_zero_eq_some.mp hs
      rw [eval_node_zero hc]
      have h := congrArg (·[i.label]?) hρ
      simp only [List.getElem?_map, hs, Option.map_eq_some_iff] at h
      obtain ⟨⟨s', _⟩, hw, rfl⟩ := h
      rw [hw]
      rfl
    · rw [sortOf_node_succ] at hs
      obtain ⟨o, ho, hs⟩ := Option.bind_eq_some_iff.mp hs
      split_ifs at hs with hcs
      obtain rfl := Option.some_inj.mp hs
      have hlen : cs.length = o.1.length := by simpa using congrArg List.length hcs
      have hvals : cs.map (eval (pointModel S) ρ) =
          (o.1.map fun s ↦ (⟨s, ()⟩ : (pointModel S).Val)).map Part.some := by
        refine List.ext_getElem (by simp [hlen]) fun j h₁ h₂ ↦ ?_
        have hj₁ : j < cs.length := by simpa using h₁
        have hj₂ : j < o.1.length := hlen ▸ hj₁
        have hj : sortOf S Γ cs[j] = some o.1[j] := by
          have := congrArg (·[j]?) hcs
          simp only [List.getElem?_map, List.getElem?_eq_getElem hj₁,
            List.getElem?_eq_getElem hj₂, Option.map_some] at this
          exact Option.some_inj.mp this
        simp only [List.getElem_map]
        exact ih _ (List.getElem_mem _) hj
      rw [eval_node_succ, (mapM_part_eq_some_iff cs _).mpr hvals, Part.bind_some]
      simp [pointModel, ho]

/-- A sequent's conclusion equates two terms of one sort, in its context. -/
def SidesSorted (S : Sig) (a : Seq) : Prop :=
  ∃ s, sortOf S a.ctx a.concl.lhs = some s ∧ sortOf S a.ctx a.concl.rhs = some s

/-- The one-point model is a model of every theory whose axioms' conclusions equate terms of one
sort. -/
theorem isModel_point {T : Theory} (h : ∀ a ∈ T.axioms, SidesSorted T.sig a) :
    IsModel T (pointModel T.sig) := fun a ha _ hρ _ ↦ by
  obtain ⟨s, h₁, h₂⟩ := h a ha
  exact ⟨⟨s, ()⟩, eval_point hρ _ h₁, eval_point hρ _ h₂⟩

/-- The extensions of a theory by well-formed definitions keep its axioms' conclusions
equations between terms of one sort, and the definitions' own are such equations. -/
theorem sidesSorted_extendAll (ds : List Defn) :
    ∀ T : Theory, (∀ a ∈ T.axioms, SidesSorted T.sig a) → DefnsWF T.sig ds →
      ∀ a ∈ (T.extendAll ds).axioms, SidesSorted (T.extendAll ds).sig a :=
  ds.rec (fun _ h _ ↦ h) fun d ds ih T h hds ↦ by
    refine ih (T.extend d) (fun a ha ↦ ?_) hds.2
    obtain ⟨hsort, hocc⟩ := hds.1
    have hmono : ∀ {t : Tree} {Γ : List ℕ} {s : ℕ}, sortOf T.sig Γ t = some s →
        sortOf (T.extend d).sig Γ t = some s := fun h' ↦ sortOf_append _ _ h'
    rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨s, h₁, h₂⟩ := h a ha
      exact ⟨s, hmono h₁, hmono h₂⟩
    · have hop : sortOf (T.extend d).sig d.ctx (opVars T.sig.length d.ctx.length) =
          some d.sort := by
        rw [opVars, op, sortOf_node_succ]
        change (T.sig.extend d)[T.sig.length]?.bind _ = _
        rw [getElem?_extend_self, Option.bind_some]
        have hv : ((List.range d.ctx.length).map var).map (sortOf (T.extend d).sig d.ctx) =
            d.ctx.map some := by
          refine List.ext_getElem (by simp) fun j h₁ h₂ ↦ ?_
          simp only [List.length_map, List.length_range] at h₁
          simp [var, sortOf_node_zero, h₁]
        simp [hv]
      simp only [Defn.axioms, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · exact ⟨d.sort, hop, hmono hsort⟩
      · exact ⟨d.sort, hmono hsort, hmono hsort⟩

end Geb.PartialHorn

end
