import GebLean.PolyBridge.Slice
import Geb.Mathlib.Data.PFunctor.Slice.W

/-!
# Fiberwise equivalence `PolyFix P` and the slice W-type

Relates this development's initial-algebra carrier `PolyFix P`
(`GebLean/PolyAlg.lean`) to the W-type `(toSlice P).W` of the translated
slice polynomial functor (`Geb.Mathlib.Data.PFunctor.Slice.W`). Both present
the initial algebra of one polynomial endofunctor, in the sense of
Gambino–Kock, equivalently the least fixed point of a container in the sense
of Abbott–Altenkirch–Ghani; the translation `toSlice`
(`GebLean/PolyBridge/Slice.lean`) identifies the two functors, and this module
carries that identification to their initial algebras.

The comparison is fiberwise: `PolyFix P x` is indexed by a codomain point
`x : X`, while a slice W-tree `w : (toSlice P).W` carries its index through the
structure map `wIndex`. The equivalence `polyFixSliceEquiv` matches `PolyFix P x`
with the trees whose index is `x`. The forward map `toSliceFib` is a fold over
`PolyFix.ind` into the fiber `{ w // wIndex w = x }` — the fiber, not the bare
W-type, because reconstructing a node requires each child's index-compatibility;
the backward map `ofSliceW` is the slice-W eliminator `SlicePFunctor.W.elim`
into `Σ x, PolyFix P x`.

## Main definitions

* `toSliceFib` — the forward map into the index fiber, by `PolyFix.ind`.
* `toSliceW` — the underlying slice W-tree of `toSliceFib`.
* `ofSliceW` — the backward map, by `SlicePFunctor.W.elim` into `Σ x, PolyFix P x`.
* `polyFixSliceEquiv` — the fiberwise equivalence
  `PolyFix P x ≃ { w : (toSlice P).W // wIndex w = x }`.

## Main statements

* `wIndex_toSliceW` — the underlying tree of `toSliceFib t` has index `x`.
* `ofSliceW_fst` — the index component of `ofSliceW P w` is `wIndex w`.
* `ofSliceW_toSliceW`, `toSliceW_ofSliceW` — the two round-trips.
* `polyFixSliceEquiv_mk` — the equivalence carries `PolyFix.mk` to the
  corresponding `SlicePFunctor.W.mk` node.

## Implementation notes

`transport_snd` and `toSliceW_transport` are generic transport lemmas used to
discharge the `Eq.rec` reindexings introduced by the backward map's fiber
transports.

## References

N. Gambino and J. Kock, "Polynomial functors and polynomial monads",
Mathematical Proceedings of the Cambridge Philosophical Society 154 (2013)
153-192, DOI `10.1017/S0305004112000394`.

M. Abbott, T. Altenkirch, N. Ghani, "Containers: Constructing strictly
positive types", Theoretical Computer Science 342 (2005) 3-27, DOI
`10.1016/j.tcs.2005.06.002`.

## Tags

polynomial functor, W-type, initial algebra, container, PFunctor, slice category
-/

namespace GebLean.PolyBridge

universe u

/-- The forward map from `PolyFix P x` into the fiber of slice W-trees over
`x`: a fold by `PolyFix.ind` into `{ w : (toSlice P).W // wIndex w = x }`. The
fiber, not the bare W-type, is the fold's target because building the
`SlicePFunctor.W.mk` node at each step needs the children's index-compatibility,
which only the fiber component `.2` supplies. -/
def toSliceFib {X : Type u} {P : PolyEndo X} {x : X} (t : PolyFix P x) :
    { w : (toSlice P).W // SlicePFunctor.wIndex (toSlice P) w = x } :=
  PolyFix.ind (P := P)
    (motive := fun {x} _ => { w : (toSlice P).W // SlicePFunctor.wIndex (toSlice P) w = x })
    (fun {x} i children ih =>
      ⟨SlicePFunctor.W.mk
          ⟨⟨⟨x, i⟩, fun e => (ih e).1⟩, by
            funext e; exact (ih e).2⟩,
        by rw [SlicePFunctor.W.wIndex_mk]; rfl⟩)
    t

/-- The underlying slice W-tree of `toSliceFib t`. -/
def toSliceW {X : Type u} {P : PolyEndo X} {x : X} (t : PolyFix P x) : (toSlice P).W :=
  (toSliceFib t).1

/-- The underlying tree of `toSliceFib t` has index `x`; the fiber component
of `toSliceFib`. -/
theorem wIndex_toSliceW {X : Type u} {P : PolyEndo X} {x : X} (t : PolyFix P x) :
    SlicePFunctor.wIndex (toSlice P) (toSliceW t) = x :=
  (toSliceFib t).2

/-- The backward map: the slice-W eliminator `SlicePFunctor.W.elim` into
`Σ x : X, PolyFix P x`, projecting the index by `Sigma.fst`. Each node
reconstructs a `PolyFix.mk`, transporting every child value along the node's
direction-input compatibility. -/
def ofSliceW {X : Type u} (P : PolyEndo X) :
    (toSlice P).W → Σ x : X, PolyFix P x :=
  SlicePFunctor.W.elim (toSlice P) (Σ x : X, PolyFix P x) Sigma.fst
    (fun node =>
      ⟨node.1.1.1,
        PolyFix.mk node.1.1.1 node.1.1.2
          (fun e =>
            (show (node.1.2 e).1 = (polyBetweenFamily X X P node.1.1.1 node.1.1.2).hom e
              from congrFun node.2 e) ▸ (node.1.2 e).2)⟩)
    (funext fun _ => rfl)

/-- A dependent-pair transport lemma: transporting the second component of a
pair `s` along an equality `s.1 = b`, given `s = ⟨b, c⟩`, yields `c`. -/
theorem transport_snd {X : Type u} {Q : X → Type u} {b : X}
    (s : Σ x, Q x) (c : Q b) (h : s.1 = b) (hs : s = ⟨b, c⟩) : h ▸ s.2 = c := by
  subst hs; rfl

/-- `toSliceW` is invariant under reindexing along an equality of indices. -/
theorem toSliceW_transport {X : Type u} {P : PolyEndo X} {a b : X} (h : a = b)
    (t : PolyFix P a) : toSliceW (h ▸ t) = toSliceW t := by
  subst h; rfl

/-- The index component of `ofSliceW P w` is the slice W-tree's index; the
`over-I` law of the slice-W eliminator. -/
theorem ofSliceW_fst {X : Type u} (P : PolyEndo X) (w : (toSlice P).W) :
    (ofSliceW P w).1 = SlicePFunctor.wIndex (toSlice P) w :=
  congrFun (SlicePFunctor.W.comp_elim (toSlice P) (Σ x : X, PolyFix P x)
    Sigma.fst _ _) w

/-- Backward after forward is the identity, in the fiber over `x`. -/
theorem ofSliceW_toSliceW {X : Type u} {P : PolyEndo X} {x : X} (t : PolyFix P x) :
    ofSliceW P (toSliceW t) = ⟨x, t⟩ :=
  PolyFix.ind (P := P)
    (motive := fun {x} t => ofSliceW P (toSliceW t) = ⟨x, t⟩)
    (fun {x} i children ih => by
      change ofSliceW P (toSliceW (PolyFix.mk x i children)) = ⟨x, PolyFix.mk x i children⟩
      refine Sigma.ext rfl (heq_of_eq (congrArg (PolyFix.mk x i) ?_))
      funext e
      exact transport_snd _ _ _ (ih e))
    t

/-- Forward after backward is the identity on slice W-trees. -/
theorem toSliceW_ofSliceW {X : Type u} {P : PolyEndo X} (w : (toSlice P).W) :
    toSliceW (ofSliceW P w).2 = w :=
  SlicePFunctor.W.induction (F := toSlice P)
    (motive := fun w => toSliceW (ofSliceW P w).2 = w)
    (fun node ih => by
      change toSliceW (ofSliceW P (SlicePFunctor.W.mk node)).2 = SlicePFunctor.W.mk node
      refine congrArg SlicePFunctor.W.mk (Subtype.ext (Sigma.ext rfl (heq_of_eq ?_)))
      funext e
      exact (toSliceW_transport _ _).trans (ih e))
    w

/-- The fiberwise equivalence between `PolyFix P x` and the slice W-trees of
`toSlice P` indexed by `x`. The forward map is `toSliceFib`; the backward map
reindexes `ofSliceW` along the tree's index equality. -/
def polyFixSliceEquiv {X : Type u} (P : PolyEndo X) (x : X) :
    PolyFix P x ≃ { w : (toSlice P).W // SlicePFunctor.wIndex (toSlice P) w = x } where
  toFun := toSliceFib
  invFun w := ((ofSliceW_fst P w.1).trans w.2) ▸ (ofSliceW P w.1).2
  left_inv t := transport_snd _ t _ (ofSliceW_toSliceW t)
  right_inv w := Subtype.ext ((toSliceW_transport _ _).trans (toSliceW_ofSliceW w.1))

/-- The equivalence carries a `PolyFix.mk` node to the corresponding
`SlicePFunctor.W.mk` node whose children are the images of the original
children. Definitional, via the `PolyFix.ind` computation step of
`toSliceFib`. -/
theorem polyFixSliceEquiv_mk {X : Type u} (P : PolyEndo X) (x : X)
    (i : polyBetweenIndex X X P x)
    (children : ∀ e : (polyBetweenFamily X X P x i).left,
      PolyFix P ((polyBetweenFamily X X P x i).hom e)) :
    polyFixSliceEquiv P x (PolyFix.mk x i children) =
      ⟨SlicePFunctor.W.mk
          ⟨⟨⟨x, i⟩, fun e => (polyFixSliceEquiv P _ (children e)).1⟩, by
            funext e; exact (polyFixSliceEquiv P _ (children e)).2⟩,
        by rw [SlicePFunctor.W.wIndex_mk]; rfl⟩ :=
  rfl

end GebLean.PolyBridge
