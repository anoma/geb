import Geb.Mathlib.Data.PFunctor.Slice.W
import GebLean.SliceW.Translate

/-!
# The free-monad carrier and constructors on a slice endofunctor

The free monad on a slice endofunctor `F` over `I`, with leaves `Y` glued in
along `v : Y → I`, is the W-type of the translate augmentation
`translate v F` (Gambino–Kock 2013), restricted to a fixed index `i` by its
fiber. `FreeM v F i` is that fiber; `pure` and `node` are the two shapes of
`translate v F` read back as the free monad's leaf and node constructors.

## Main definitions

* `SlicePFunctor.FreeM` — the free-monad carrier: the fiber of
  `(translate v F).wIndex` over `i`.
* `SlicePFunctor.FreeM.pure` — the leaf constructor, from a leaf datum lying
  over `i`.
* `SlicePFunctor.FreeM.node` — the node constructor, from an `F`-shape and a
  family of subtrees indexed by its positions.

## Main statements

* `SlicePFunctor.FreeM.val_pure` / `SlicePFunctor.FreeM.val_node` — the
  underlying-tree characterization of `pure` and `node`, as `W.mk` on the
  corresponding summand of `translate v F`.

## References

N. Gambino and J. Kock, "Polynomial functors and polynomial monads",
Mathematical Proceedings of the Cambridge Philosophical Society 154 (2013)
153-192, DOI `10.1017/S0305004112000394`.

## Tags

free monad, W-type, initial algebra, polynomial functor, slice category,
container, PFunctor
-/

namespace SlicePFunctor

universe uY uA uB uI

variable {I : Type uI} {Y : Type uY} {v : Y → I} {F : SlicePFunctor.{uA, uB, uI, uI} I I}

/-- The free-monad carrier at `i`: the fiber of `(translate v F).wIndex` over
`i`, i.e. the `translate v F`-trees indexed at `i`. -/
def FreeM (v : Y → I) (F : SlicePFunctor.{uA, uB, uI, uI} I I) (i : I) :=
  { w : (translate v F).W // (translate v F).wIndex w = i }

namespace FreeM

/-- The leaf constructor: a leaf datum `a` lying over `i` (i.e. `v a.1 = i`)
gives the nullary `Sum.inl` node of `translate v F`. -/
def pure {i : I} (a : { y : Y // v y = i }) : FreeM v F i :=
  ⟨W.mk ⟨⟨Sum.inl a.1, fun e => e.elim⟩, funext fun e => e.elim⟩, by
    rw [W.wIndex_mk]
    exact a.2⟩

/-- The node constructor: an `F`-shape `a` together with a family of subtrees
`c`, one per position of `a`, each lying over the direction-input map's value
at that position, gives the `Sum.inr` node of `translate v F`. -/
def node (a : F.A) (c : (b : F.B a) → FreeM v F (F.rCurried a b)) : FreeM v F (F.q a) :=
  ⟨W.mk ⟨⟨Sum.inr a, fun b => (c b).1⟩,
      (SliceDomPFunctor.compatible_iff _ _ _ _).mpr fun b => (c b).2⟩, by
    rw [W.wIndex_mk]
    exact translate_q_inr a⟩

/-- The underlying tree of `pure a` is the `Sum.inl` node of `translate v F`
at `a.1`, with vacuous (`PEmpty`) children. -/
@[simp]
theorem val_pure {i : I} (a : { y : Y // v y = i }) :
    (pure a).1 = W.mk (F := translate v F) ⟨⟨Sum.inl a.1, fun e => e.elim⟩,
      funext fun e => e.elim⟩ :=
  rfl

/-- The underlying tree of `node a c` is the `Sum.inr` node of `translate v F`
at `a`, with children `c` reduced to their underlying trees. -/
@[simp]
theorem val_node (a : F.A) (c : (b : F.B a) → FreeM v F (F.rCurried a b)) :
    (node a c).1 = W.mk (F := translate v F) ⟨⟨Sum.inr a, fun b => (c b).1⟩,
      (SliceDomPFunctor.compatible_iff _ _ _ _).mpr fun b => (c b).2⟩ :=
  rfl

end FreeM

end SlicePFunctor
