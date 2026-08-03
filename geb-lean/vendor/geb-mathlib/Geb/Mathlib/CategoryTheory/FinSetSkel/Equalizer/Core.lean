/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.CategoryTheory.FinSetSkel.Basic
public import Geb.Mathlib.Data.Vector.OfFn
public import Geb.Mathlib.Data.Vector.Scatter
public import Mathlib.Data.List.Nodup

/-!
# Binary equalizers of `FinSetSkel`

The equalizer of `f g : X ⟶ Y` is the sub-object on the indices at
which they agree: the list `(List.finRange X.len).filter p` for the
decidable predicate `p i = decide (f.toVec.get i = g.toVec.get i)`,
and the object of its length.

## Main definitions

* `FinSetSkel.Equalizer.agree` — the indices at which a parallel
  pair agrees.
* `FinSetSkel.Equalizer.obj`, `FinSetSkel.Equalizer.ι` — the
  equalizer object and its injection.
* `FinSetSkel.Equalizer.invVec` — the inverse of the injection,
  written in one pass.
* `FinSetSkel.Equalizer.lift` — the factorisation.

## Main statements

* `FinSetSkel.Equalizer.invVec_get`,
  `FinSetSkel.Equalizer.injVec_get_invVec` — the inverse of the
  injection.
* `FinSetSkel.Equalizer.injVec_injective`,
  `FinSetSkel.Equalizer.agreePred_get_of_comp_eq` — the two
  properties the universal property rests on.
* `FinSetSkel.Equalizer.ι_comp`, `FinSetSkel.Equalizer.lift_ι`,
  `FinSetSkel.Equalizer.lift_uniq` — the universal property.

## Implementation notes

The inverse of the injection is built as a vector of `ℕ`, not of
`Fin k`: `Vector (Fin k) X.len` is uninhabited whenever `k = 0` and
`X.len > 0`, and that case is reachable — any `f g : mk 3 ⟶ mk 2`
differing at every index gives `k = 0`. `Vector.replicate` needs an
inhabitant, and `0 : ℕ` is one where no `Fin k` is. The `Fin k` is
built at the lift site, where the agreement of the index is
available and the bound lemma applies.

The agreement list and the inverse vector are bound outside anything
function-valued. A definition whose result is a function re-runs a
`let` above its lambda on every application of the partially applied
function, while the same `let` in a definition returning a value runs
once; the constraint is invisible in the source, and a refactor
lifting the vector construction into a function-returning helper
would break it silently.

## Tags

finite sets, skeleton, equalizer, choice-free
-/

@[expose] public section

universe u

open CategoryTheory

namespace FinSetSkel.Equalizer

variable {X Y : FinSetSkel.{u}}

/-- The predicate deciding where a parallel pair agrees. -/
def agreePred (f g : X ⟶ Y) (i : Fin X.len) : Bool :=
  decide (f.toVec.get i = g.toVec.get i)

/-- The indices at which a parallel pair agrees, in order. -/
def agree (f g : X ⟶ Y) : List (Fin X.len) :=
  (List.finRange X.len).filter (agreePred f g)

/-- The agreement list has no repetitions. -/
theorem agree_nodup (f g : X ⟶ Y) : (agree f g).Nodup :=
  (List.nodup_finRange X.len).filter _

/-- Membership in the agreement list is agreement. -/
theorem mem_agree_iff (f g : X ⟶ Y) (j : Fin X.len) :
    j ∈ agree f g ↔ agreePred f g j = true := by
  simp [agree, List.mem_filter, List.mem_finRange]

/-- A morphism equalising the pair takes every index to an agreeing
index. -/
theorem agreePred_get_of_comp_eq (f g : X ⟶ Y) {Z : FinSetSkel.{u}} (h : Z ⟶ X)
    (w : h ≫ f = h ≫ g) (t : Fin Z.len) : agreePred f g (h.toVec.get t) = true := by
  simp only [agreePred, decide_eq_true_eq]
  simpa using congrArg (fun m ↦ (m : Z ⟶ Y).toVec.get t) w

/-- The equalizer object: the length of the agreement list. -/
def obj (f g : X ⟶ Y) : FinSetSkel.{u} := mk (agree f g).length

/-- The injection vector, the agreement list as a vector. -/
def injVec (f g : X ⟶ Y) : Vector (Fin X.len) (obj f g).len :=
  ⟨(agree f g).toArray, by simp [obj]⟩

/-- The injection morphism. -/
def ι (f g : X ⟶ Y) : obj f g ⟶ X := Hom.ofVec (injVec f g)

/-- Every entry of the injection is an agreeing index. -/
theorem injVec_get_mem (f g : X ⟶ Y) (i : Fin (obj f g).len) :
    (injVec f g).get i ∈ agree f g := by
  simp [injVec, Vector.get_eq_getElem]

/-- Distinct positions of the injection carry distinct indices. -/
theorem injVec_injective (f g : X ⟶ Y) : Function.Injective (injVec f g).get := by
  intro a b hab
  simp only [injVec, Vector.get_eq_getElem, Vector.getElem_mk, List.getElem_toArray] at hab
  exact Fin.ext ((agree_nodup f g).getElem_inj_iff.mp hab)

/-- The injection equalises the pair. -/
theorem ι_comp (f g : X ⟶ Y) : ι f g ≫ f = ι f g ≫ g :=
  hom_ext fun i ↦ by
    have h := (mem_agree_iff f g _).mp (injVec_get_mem f g i)
    simpa [ι] using of_decide_eq_true h

/-- The inverse of the injection, as positions in the agreement
list; entries at non-agreeing indices are unconstrained. -/
def invVec (f g : X ⟶ Y) : Vector ℕ X.len :=
  Vector.scatter ((agree f g).zipIdx 0) (Vector.replicate X.len 0)

/-- The inverse's entry at a listed index is that index's position in
the agreement list. -/
theorem invVec_get (f g : X ⟶ Y) (j : Fin X.len) (k : ℕ)
    (hk : k < (agree f g).length) (hget : (agree f g)[k] = j) :
    (invVec f g).get j = k := by
  have hm : (j, k) ∈ (agree f g).zipIdx 0 :=
    (List.mk_mem_zipIdx_iff_getElem?).mpr (by rw [List.getElem?_eq_getElem hk, hget])
  have hnd : (((agree f g).zipIdx 0).map Prod.fst).Nodup := by
    rw [List.zipIdx_map_fst]; exact agree_nodup f g
  exact Vector.get_scatter_of_mem _ _ _ _ hm
    fun b hb ↦ congrArg Prod.snd (List.inj_on_of_nodup_map hnd hb hm rfl)

/-- At an agreeing index the inverse is a position in the agreement
list. -/
theorem invVec_lt (f g : X ⟶ Y) (j : Fin X.len)
    (hj : agreePred f g j = true) : (invVec f g).get j < (obj f g).len := by
  obtain ⟨k, hk, hget⟩ := List.getElem_of_mem ((mem_agree_iff f g j).mpr hj)
  rw [invVec_get f g j k hk hget]
  exact hk

/-- At an agreeing index, the injection recovers the index from its
position. -/
theorem injVec_get_invVec (f g : X ⟶ Y) (j : Fin X.len)
    (hj : agreePred f g j = true) :
    (injVec f g).get ⟨(invVec f g).get j, invVec_lt f g j hj⟩ = j := by
  obtain ⟨k, hk, hget⟩ := List.getElem_of_mem ((mem_agree_iff f g j).mpr hj)
  have hidx : (⟨(invVec f g).get j, invVec_lt f g j hj⟩ : Fin (obj f g).len) = ⟨k, hk⟩ :=
    Fin.ext (invVec_get f g j k hk hget)
  rw [hidx]
  simpa [injVec, Vector.get_eq_getElem] using hget

/-- The factorisation of a morphism equalising the pair. -/
def lift (f g : X ⟶ Y) {Z : FinSetSkel.{u}} (h : Z ⟶ X)
    (w : h ≫ f = h ≫ g) : Z ⟶ obj f g :=
  let inv := invVec f g
  Hom.ofVec (Vector.ofFnC fun t ↦
    ⟨inv.get (h.toVec.get t), invVec_lt f g _ (agreePred_get_of_comp_eq f g h w t)⟩)

/-- The lift followed by the injection is the original morphism. -/
@[simp] theorem lift_ι (f g : X ⟶ Y) {Z : FinSetSkel.{u}} (h : Z ⟶ X)
    (w : h ≫ f = h ≫ g) : lift f g h w ≫ ι f g = h :=
  hom_ext fun t ↦ by
    simp only [comp_get, ι, lift, Hom.toVec_ofVec, Vector.get_ofFnC]
    exact injVec_get_invVec f g (h.toVec.get t) (agreePred_get_of_comp_eq f g h w t)

/-- Any morphism factoring through the injection is the lift. -/
theorem lift_uniq (f g : X ⟶ Y) {Z : FinSetSkel.{u}} (h : Z ⟶ X)
    (w : h ≫ f = h ≫ g) (m : Z ⟶ obj f g) (hm : m ≫ ι f g = h) :
    m = lift f g h w :=
  hom_ext fun t ↦ injVec_injective f g (by
    have hl : (m ≫ ι f g).toVec.get t = (lift f g h w ≫ ι f g).toVec.get t := by
      rw [hm, lift_ι]
    simpa [ι] using hl)

end FinSetSkel.Equalizer
