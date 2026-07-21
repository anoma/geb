import Geb.Mathlib.Data.PFunctor.Slice.W
import Mathlib.Logic.Equiv.Defs

/-!
# Base change of a slice endofunctor along an index equivalence

Given a slice endofunctor `F` over `I` and an equivalence `e : I ≃ J`, the
base change `reindex e F` is the slice endofunctor over `J` with the same
underlying `PFunctor` and with the shape-output map `q` and the
direction-input map `r` conjugated by `e`. The associated slice W-types are
equivalent: since `reindex` leaves the underlying `PFunctor` untouched, a
`PFunctor.W` tree admissible for `F` is, without any rebuilding, admissible
for `reindex e F` once its indices are read through `e`, and conversely
through `e.symm`. This is base change along an index equivalence, in the
sense of Gambino–Kock 2013, section 1.

## Main definitions

* `SlicePFunctor.reindex` — the base change of a slice endofunctor along an
  index equivalence.
* `SlicePFunctor.reindex.wMap` — the induced map on W-types: the identity on
  underlying trees, with admissibility transferred.
* `SlicePFunctor.reindex.wEquiv` — the induced equivalence of W-types.
* `SlicePFunctor.reindex.wEquivFiber` — the induced equivalence of W-type
  fibres over indices related by `e`.

## Main statements

* `SlicePFunctor.reindex_A`, `reindex_B`, `reindex_q`, `reindex_r` — the
  characterization of each field of `reindex e F`.
* `SlicePFunctor.reindex.wIndex_wMap` — `wMap` conjugates `wIndex` by `e`.
* `SlicePFunctor.reindex.wMap_mk` — `wMap` is a morphism of constructors.

## Implementation notes

`reindex` leaves the underlying `PFunctor` untouched, so `F.W` and
`(reindex e F).W` are both subtypes of the same `F.toPFunctor.W`; `wMap` is
the identity on the underlying tree, with admissibility transferred by the
`Prop`-valued inductions `reindex_wValid` / `reindex_wValid_symm`. `wEquiv`'s
round trips are consequently `Subtype.ext rfl`, with no induction needed at
that level; `wEquivFiber` reuses `wEquiv` and the index law
`reindex.wIndex_wEquiv_symm`, whose orientation is fixed by
`Equiv.apply_symm_apply` and `Equiv.symm_apply_apply`.

## References

N. Gambino and J. Kock, "Polynomial functors and polynomial monads",
Mathematical Proceedings of the Cambridge Philosophical Society 154 (2013)
153-192, DOI `10.1017/S0305004112000394`.

## Tags

polynomial functor, W-type, initial algebra, base change, slice category,
PFunctor
-/

namespace SlicePFunctor

universe uA uB uI

/-- Base change of a slice endofunctor along an index equivalence: the
underlying `PFunctor` is unchanged; the shape-output map `q` and the
direction-input map `r` are conjugated by `e`. -/
def reindex {I J : Type uI} (e : I ≃ J) (F : SlicePFunctor.{uA, uB, uI, uI} I I) :
    SlicePFunctor.{uA, uB, uI, uI} J J where
  toPFunctor := F.toPFunctor
  r := e ∘ F.r
  q := e ∘ F.q

variable {I J : Type uI} (e : I ≃ J) (F : SlicePFunctor.{uA, uB, uI, uI} I I)

/-- The shape type of `reindex e F` is unchanged. -/
@[simp] theorem reindex_A : (reindex e F).A = F.A := rfl

/-- The position type of `reindex e F` at a shape `a` is unchanged. -/
@[simp] theorem reindex_B (a : F.A) : (reindex e F).B a = F.B a := rfl

/-- The shape-output map of `reindex e F` is `F`'s conjugated by `e`. -/
@[simp] theorem reindex_q (a : F.A) : (reindex e F).q a = e (F.q a) := rfl

/-- The direction-input map of `reindex e F` is `F`'s conjugated by `e`. -/
@[simp] theorem reindex_r (a : F.A) (b : F.B a) :
    (reindex e F).r ⟨a, b⟩ = e (F.r ⟨a, b⟩) := rfl

/-- Admissibility transfers from `F` to `reindex e F`: the underlying
`PFunctor.W` trees coincide, and each node's compatibility with the
direction-input map is the image of `F`'s under `congrArg e`. A
`Prop`-valued `W.induction`. -/
theorem reindex_wValid (z : F.W) : (reindex e F).WValid z.1 :=
  W.induction (F := F) (motive := fun z => (reindex e F).WValid z.1)
    (fun x ih => ((reindex e F).wValid_mk x.1.1 (Subtype.val ∘ x.1.2)).mpr
      ⟨ih, funext fun b => congrArg e
        ((F.toSliceDomPFunctor.compatible_iff F.wIndex x.1.1 x.1.2).mp x.2 b)⟩)
    z

/-- Admissibility transfers from `reindex e F` back to `F`, stripping the
conjugation by `e.injective`. -/
theorem reindex_wValid_symm (z : (reindex e F).W) : F.WValid z.1 :=
  W.induction (F := reindex e F) (motive := fun z => F.WValid z.1)
    (fun x ih => (F.wValid_mk x.1.1 (Subtype.val ∘ x.1.2)).mpr
      ⟨ih, funext fun b => e.injective
        (((reindex e F).toSliceDomPFunctor.compatible_iff
          (reindex e F).wIndex x.1.1 x.1.2).mp x.2 b)⟩)
    z

/-- The map on W-types induced by `reindex`: the identity on underlying
trees, with admissibility transferred by `reindex_wValid`. -/
def reindex.wMap : F.W → (reindex e F).W :=
  fun z => ⟨z.1, reindex_wValid e F z⟩

/-- `wMap` conjugates `wIndex` by `e`. -/
theorem reindex.wIndex_wMap (z : F.W) :
    (reindex e F).wIndex (reindex.wMap e F z) = e (F.wIndex z) := rfl

/-- `wMap` is a morphism of constructors: it carries `W.mk` at a shape with
children `c` to `W.mk` at the same shape with children mapped by `wMap`. -/
@[simp]
theorem reindex.wMap_mk (x : F.toSliceDomPFunctor.Obj F.wIndex) :
    reindex.wMap e F (W.mk x) =
      W.mk (F := reindex e F) ⟨⟨x.1.1, fun b => reindex.wMap e F (x.1.2 b)⟩,
        ((reindex e F).toSliceDomPFunctor.compatible_iff (reindex e F).wIndex x.1.1 _).mpr
          (fun b => (reindex.wIndex_wMap e F (x.1.2 b)).trans
            (congrArg e ((F.toSliceDomPFunctor.compatible_iff F.wIndex x.1.1 x.1.2).mp x.2 b)))⟩ :=
  rfl

/-- The equivalence of W-types induced by `reindex`: the identity on
underlying trees, with admissibility transferred each way. -/
def reindex.wEquiv : F.W ≃ (reindex e F).W where
  toFun := reindex.wMap e F
  invFun z := ⟨z.1, reindex_wValid_symm e F z⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

/-- `wEquiv.symm` conjugates `wIndex` by `e.symm`. -/
theorem reindex.wIndex_wEquiv_symm (z : (reindex e F).W) :
    F.wIndex ((reindex.wEquiv e F).symm z) = e.symm ((reindex e F).wIndex z) := by
  have h : (reindex e F).wIndex z = e (F.wIndex ((reindex.wEquiv e F).symm z)) := by
    conv_lhs => rw [← (reindex.wEquiv e F).apply_symm_apply z]
    exact reindex.wIndex_wMap e F ((reindex.wEquiv e F).symm z)
  rw [h, e.symm_apply_apply]

/-- The induced equivalence of W-type fibres over indices related by `e`. -/
def reindex.wEquivFiber (j : J) :
    { w : F.W // F.wIndex w = e.symm j } ≃
      { w' : (reindex e F).W // (reindex e F).wIndex w' = j } where
  toFun w := ⟨reindex.wEquiv e F w.1, by
    have h := reindex.wIndex_wMap e F w.1
    rw [w.2, e.apply_symm_apply] at h
    exact h⟩
  invFun w' := ⟨(reindex.wEquiv e F).symm w'.1,
    (reindex.wIndex_wEquiv_symm e F w'.1).trans (congrArg e.symm w'.2)⟩
  left_inv w := Subtype.ext ((reindex.wEquiv e F).left_inv w.1)
  right_inv w' := Subtype.ext ((reindex.wEquiv e F).right_inv w'.1)

end SlicePFunctor
