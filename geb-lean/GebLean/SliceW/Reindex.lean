import Geb.Mathlib.Data.PFunctor.Slice.W
import Mathlib.Logic.Equiv.Defs

/-!
# Reindexing a slice polynomial functor along maps of its domain and codomain

A `SlicePFunctor D C` is the polynomial diagram
`D ◀ r ─ Idx ─ fst ▶ A ─ q ▶ C`, interpreted as the composite
`Σ_q ∘ Π_fst ∘ Δ_r : Type/D → Type/C`. The two index maps sit at opposite
ends of that composite, so composing each with a function has a different
meaning. Composing the direction-input map `r` with `g : D → D'` replaces
`Δ_r` by `Δ_r ∘ Δ_g`, that is, pre-composes the functor with the base change
`Δ_g : Type/D' → Type/D` (`domReindex`). Composing the shape-output map `q`
with `f : C → C'` replaces `Σ_q` by `Σ_f ∘ Σ_q`, that is, post-composes the
functor with the dependent sum `Σ_f : Type/C → Type/C'` (`codReindex`). The
two touch disjoint fields; `reindexMap` performs both at once. Neither
operation requires its map to be invertible.

When the domain and the codomain coincide and the two maps are one and the
same equivalence `e : I ≃ J`, the result `reindex e F` is again a slice
endofunctor, and the associated slice W-types are equivalent: since
reindexing leaves the underlying `PFunctor` untouched, a `PFunctor.W` tree
admissible for `F` is, without any rebuilding, admissible for `reindex e F`
once its indices are read through `e`, and conversely through `e.symm`. Base
change is in the sense of Gambino–Kock 2013, section 1.

## Main definitions

* `SlicePFunctor.domReindex` — pre-composition with the base change along a
  map of domains.
* `SlicePFunctor.codReindex` — post-composition with the dependent sum along
  a map of codomains.
* `SlicePFunctor.reindexMap` — both at once.
* `SlicePFunctor.reindex` — the endofunctor special case: one index
  equivalence used on both sides.
* `SlicePFunctor.reindex.wMap` — the induced map on W-types: the identity on
  underlying trees, with admissibility transferred.
* `SlicePFunctor.reindex.wEquiv` — the induced equivalence of W-types.
* `SlicePFunctor.reindex.wEquivFiber` — the induced equivalence of W-type
  fibres over indices related by `e`.

## Main statements

* `SlicePFunctor.domReindex_A`, `domReindex_B`, `domReindex_q`,
  `domReindex_r`, and the corresponding `codReindex_*` and `reindex_*` — the
  characterization of each field.
* `SlicePFunctor.reindex.wIndex_wMap` — `wMap` conjugates `wIndex` by `e`.
* `SlicePFunctor.reindex.wMap_mk` — `wMap` is a morphism of constructors.

## Implementation notes

Reindexing leaves the underlying `PFunctor` untouched, so `F.W` and
`(reindex e F).W` are both subtypes of the same `F.toPFunctor.W`; `wMap` is
the identity on the underlying tree, with admissibility transferred by the
`Prop`-valued inductions `reindex_wValid` / `reindex_wValid_symm`. Those
inductions are where the endofunctor hypothesis and the invertibility of `e`
enter: admissibility compares a child's `q`-index against its parent's
`r`-index, so it transfers forwards only when both fields are composed with
the same map, and backwards only when that map is injective. `wEquiv`'s
round trips are consequently `Subtype.ext rfl`, with no induction needed at
that level; `wEquivFiber` reuses `wEquiv` and the index law
`reindex.wIndex_wEquiv_symm`, whose orientation is fixed by
`Equiv.apply_symm_apply` and `Equiv.symm_apply_apply`.

## References

N. Gambino and J. Kock, "Polynomial functors and polynomial monads",
Mathematical Proceedings of the Cambridge Philosophical Society 154 (2013)
153-192, DOI `10.1017/S0305004112000394`.

## Tags

polynomial functor, W-type, initial algebra, base change, dependent sum,
slice category, PFunctor
-/

namespace SlicePFunctor

universe uA uB uD uD' uC uC'

section Reindex

variable {D : Type uD} {D' : Type uD'} {C : Type uC} {C' : Type uC'}

/-- Pre-composition of a slice polynomial functor with the base change
`Δ_g : Type/D' → Type/D` along `g : D → D'`: the underlying `PFunctor` and
the shape-output map `q` are unchanged; the direction-input map `r` is
composed with `g`. -/
def domReindex (g : D → D') (F : SlicePFunctor.{uA, uB, uD, uC} D C) :
    SlicePFunctor.{uA, uB, uD', uC} D' C where
  toPFunctor := F.toPFunctor
  r := g ∘ F.r
  q := F.q

/-- Post-composition of a slice polynomial functor with the dependent sum
`Σ_f : Type/C → Type/C'` along `f : C → C'`: the underlying
`SliceDomPFunctor` is unchanged; the shape-output map `q` is composed with
`f`. -/
def codReindex (f : C → C') (F : SlicePFunctor.{uA, uB, uD, uC} D C) :
    SlicePFunctor.{uA, uB, uD, uC'} D C' where
  toSliceDomPFunctor := F.toSliceDomPFunctor
  q := f ∘ F.q

/-- Reindexing on both sides at once: `Σ_f ∘ F ∘ Δ_g`. The two constituents
act on disjoint fields, so the order in which they are applied is
immaterial. -/
def reindexMap (g : D → D') (f : C → C') (F : SlicePFunctor.{uA, uB, uD, uC} D C) :
    SlicePFunctor.{uA, uB, uD', uC'} D' C' :=
  codReindex f (domReindex g F)

variable (g : D → D') (f : C → C') (F : SlicePFunctor.{uA, uB, uD, uC} D C)

/-- The shape type of `domReindex g F` is unchanged. -/
theorem domReindex_A : (domReindex g F).A = F.A := rfl

/-- The position type of `domReindex g F` at a shape `a` is unchanged. -/
theorem domReindex_B (a : F.A) : (domReindex g F).B a = F.B a := rfl

/-- The shape-output map of `domReindex g F` is unchanged. -/
@[simp] theorem domReindex_q (a : F.A) : (domReindex g F).q a = F.q a := rfl

/-- The direction-input map of `domReindex g F` is `F`'s composed with `g`. -/
@[simp] theorem domReindex_r (a : F.A) (b : F.B a) :
    (domReindex g F).r ⟨a, b⟩ = g (F.r ⟨a, b⟩) := rfl

/-- The shape type of `codReindex f F` is unchanged. -/
theorem codReindex_A : (codReindex f F).A = F.A := rfl

/-- The position type of `codReindex f F` at a shape `a` is unchanged. -/
theorem codReindex_B (a : F.A) : (codReindex f F).B a = F.B a := rfl

/-- The shape-output map of `codReindex f F` is `F`'s composed with `f`. -/
@[simp] theorem codReindex_q (a : F.A) : (codReindex f F).q a = f (F.q a) := rfl

/-- The direction-input map of `codReindex f F` is unchanged. -/
@[simp] theorem codReindex_r (a : F.A) (b : F.B a) :
    (codReindex f F).r ⟨a, b⟩ = F.r ⟨a, b⟩ := rfl

end Reindex

universe uI uJ

/-- Base change of a slice endofunctor along an index equivalence: the
special case of `reindexMap` in which the domain and the codomain coincide
and both are reindexed by the same equivalence. This is the case in which
the W-types transport. -/
def reindex {I : Type uI} {J : Type uJ} (e : I ≃ J) (F : SlicePFunctor.{uA, uB, uI, uI} I I) :
    SlicePFunctor.{uA, uB, uJ, uJ} J J :=
  reindexMap e e F

variable {I : Type uI} {J : Type uJ} (e : I ≃ J) (F : SlicePFunctor.{uA, uB, uI, uI} I I)

/-- The shape type of `reindex e F` is unchanged. -/
theorem reindex_A : (reindex e F).A = F.A := rfl

/-- The position type of `reindex e F` at a shape `a` is unchanged. -/
theorem reindex_B (a : F.A) : (reindex e F).B a = F.B a := rfl

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
