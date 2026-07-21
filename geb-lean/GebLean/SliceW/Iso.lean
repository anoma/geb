import Geb.Mathlib.Data.PFunctor.Slice.W
import Mathlib.Logic.Equiv.Defs

/-!
# Isomorphisms of slice polynomial functors and W-type transport

An isomorphism `SlicePFunctor.Iso F G` of slice functors from `D` to `C` is a
container isomorphism: a shape equivalence `F.A ≃ G.A`, a fibrewise position
equivalence `F.B a ≃ G.B (shapeEquiv a)`, and the compatibility of the
shape-output and direction-input maps. For endofunctors, such an isomorphism
induces an equivalence of the associated W-types (initial algebras), fibrewise
over the shared (co)domain.  The transport `wMap` is a single slice-W
eliminator; the inverse is the `wMap` of the reversed isomorphism, and the two
round trips are structural inductions.

## Main definitions

* `SlicePFunctor.Iso` — the container isomorphism of slice endofunctors.
* `SlicePFunctor.Iso.symm` — the reversed isomorphism.
* `SlicePFunctor.Iso.wMap` — the induced map on W-types, by `W.elim`.
* `SlicePFunctor.Iso.wEquiv` — the induced equivalence of W-types.
* `SlicePFunctor.Iso.wEquivFiber` — the induced equivalence of W-type fibres
  over a fixed index.

## Main statements

* `SlicePFunctor.Iso.wIndex_wMap` — `wMap` lies over `I`.
* `SlicePFunctor.Iso.wMap_mk` — `wMap` is a morphism of constructors.
* `SlicePFunctor.Iso.symm_wMap_wMap`, `SlicePFunctor.Iso.wMap_symm_wMap` — the
  two round trips.

## Implementation notes

`symm`'s position field is the reversed forward equivalence composed with an
`Equiv.cast` re-typing its domain along `shapeEquiv.apply_symm_apply`. The
round trips therefore reduce, at each node, to transport identities for the
position composites (`posEquiv_symm_comp` / `posEquiv_symm_comp'`), proved
through the `HEq` helpers `posEquiv_heq_cast` and `symm_posEquiv_symm_heq`.

## References

M. Abbott, T. Altenkirch, N. Ghani, "Containers: Constructing strictly
positive types", Theoretical Computer Science 342 (2005) 3-27, DOI
`10.1016/j.tcs.2005.06.002`.

N. Gambino and J. Kock, "Polynomial functors and polynomial monads",
Mathematical Proceedings of the Cambridge Philosophical Society 154 (2013)
153-192, DOI `10.1017/S0305004112000394`.

## Tags

polynomial functor, W-type, initial algebra, container, isomorphism, slice
category, PFunctor
-/

namespace SlicePFunctor

universe uA uB uD uC

/-- A container isomorphism of slice functors `D` to `C`: a shape
equivalence, a fibrewise position equivalence, and the compatibility of the
shape-output map `q` and the direction-input map `r`. -/
structure Iso {D : Type uD} {C : Type uC} (F G : SlicePFunctor.{uA, uB, uD, uC} D C) where
  /-- The equivalence of shapes. -/
  shapeEquiv : F.A ≃ G.A
  /-- The fibrewise equivalence of positions, over each shape. -/
  posEquiv : ∀ a, F.B a ≃ G.B (shapeEquiv a)
  /-- The shape-output maps agree along the shape equivalence. -/
  q_comm : ∀ a, G.q (shapeEquiv a) = F.q a
  /-- The direction-input maps agree along the shape and position
  equivalences. -/
  r_comm : ∀ a b, G.r ⟨shapeEquiv a, posEquiv a b⟩ = F.r ⟨a, b⟩

namespace Iso

variable {D : Type uD} {C : Type uC} {F G : SlicePFunctor.{uA, uB, uD, uC} D C}

/-- The reversed isomorphism. The position field at `a'` reverses the forward
position equivalence at `shapeEquiv.symm a'` and re-types its domain from
`G.B (shapeEquiv (shapeEquiv.symm a'))` to `G.B a'`. -/
def symm (e : Iso F G) : Iso G F where
  shapeEquiv := e.shapeEquiv.symm
  posEquiv := fun a' =>
    (Equiv.cast (congrArg G.B (e.shapeEquiv.apply_symm_apply a')).symm).trans
      (e.posEquiv (e.shapeEquiv.symm a')).symm
  q_comm := fun a' => by
    rw [← e.q_comm (e.shapeEquiv.symm a'), e.shapeEquiv.apply_symm_apply]
  r_comm := fun a' b' => by
    rw [← e.r_comm (e.shapeEquiv.symm a')]
    simp only [Equiv.trans_apply, Equiv.apply_symm_apply]
    exact congrArg G.r (Sigma.ext (e.shapeEquiv.apply_symm_apply a')
      (Equiv.cast_apply _ b' ▸ cast_heq _ b'))

/-- `HEq` congruence for `posEquiv` along a shape equality. -/
theorem posEquiv_heq_cast (e : Iso F G) {a₀ a : F.A} (h : a₀ = a) (b : F.B a₀) :
    e.posEquiv a₀ b ≍ e.posEquiv a (cast (congrArg F.B h) b) := by
  subst h
  rfl

/-- The reversed position equivalence is a position equivalence in the
reversed direction. -/
theorem symm_posEquiv_symm_heq (e : Iso F G) (a' : G.A)
    (b' : F.B (e.shapeEquiv.symm a')) :
    (e.symm.posEquiv a').symm b' ≍ e.posEquiv (e.shapeEquiv.symm a') b' := by
  simp only [symm]
  exact cast_heq _ _

/-- The reversed-then-forward position composite is the cast induced by
`shapeEquiv.symm_apply_apply`; a transport identity used in the round trips. -/
theorem posEquiv_symm_comp (e : Iso F G) (a : F.A)
    (b' : F.B (e.shapeEquiv.symm (e.shapeEquiv a))) :
    (e.posEquiv a).symm ((e.symm.posEquiv (e.shapeEquiv a)).symm b')
      = cast (congrArg F.B (e.shapeEquiv.symm_apply_apply a)) b' := by
  rw [Equiv.symm_apply_eq]
  apply eq_of_heq
  refine (symm_posEquiv_symm_heq e (e.shapeEquiv a) b').trans ?_
  exact posEquiv_heq_cast e (e.shapeEquiv.symm_apply_apply a) b'

/-- The forward-then-reversed position composite is the cast induced by
`shapeEquiv.apply_symm_apply`; the transport identity for the other round
trip. The reversed equivalence's cast cancels the introduced one. -/
theorem posEquiv_symm_comp' (e : Iso F G) (a' : G.A)
    (b'' : G.B (e.shapeEquiv (e.shapeEquiv.symm a'))) :
    (e.symm.posEquiv a').symm ((e.posEquiv (e.shapeEquiv.symm a')).symm b'')
      = cast (congrArg G.B (e.shapeEquiv.apply_symm_apply a')) b'' := by
  apply eq_of_heq
  exact ((symm_posEquiv_symm_heq e a' ((e.posEquiv (e.shapeEquiv.symm a')).symm b'')).trans
    (heq_of_eq (Equiv.apply_symm_apply _ b''))).trans (cast_heq _ b'').symm

end Iso

namespace Iso

universe uI

variable {I : Type uI} {F G : SlicePFunctor.{uA, uB, uI, uI} I I}

/-- The map on W-types induced by an isomorphism, a single slice-W eliminator
into the algebra `(G.W, G.wIndex)`: each node re-indexes its shape by
`shapeEquiv` and its children by `(posEquiv a).symm`. -/
def wMap (e : Iso F G) : F.W → G.W :=
  W.elim F G.W G.wIndex
    (fun z =>
      W.mk ⟨⟨e.shapeEquiv z.1.1, fun b' => z.1.2 ((e.posEquiv z.1.1).symm b')⟩,
        (G.toSliceDomPFunctor.compatible_iff G.wIndex _ _).mpr (fun b' => by
          dsimp only
          rw [(F.toSliceDomPFunctor.compatible_iff G.wIndex z.1.1 z.1.2).mp z.2
            ((e.posEquiv z.1.1).symm b'), ← e.r_comm z.1.1 ((e.posEquiv z.1.1).symm b'),
            Equiv.apply_symm_apply])⟩)
    (by
      funext z
      rw [Function.comp_apply, W.wIndex_mk]
      exact e.q_comm z.1.1)

/-- `wMap` lies over `I`: its index is that of its argument. -/
theorem wIndex_wMap (e : Iso F G) (z : F.W) : G.wIndex (e.wMap z) = F.wIndex z :=
  congrFun (W.comp_elim F G.W G.wIndex _ _) z

/-- `wMap` is a morphism of constructors: it carries `W.mk` at `a` to `W.mk` at
`shapeEquiv a` with the children re-indexed and mapped. -/
@[simp]
theorem wMap_mk (e : Iso F G) (x : F.toSliceDomPFunctor.Obj F.wIndex) :
    e.wMap (W.mk x) =
      W.mk ⟨⟨e.shapeEquiv x.1.1,
          fun b' => e.wMap (x.1.2 ((e.posEquiv x.1.1).symm b'))⟩,
        (G.toSliceDomPFunctor.compatible_iff G.wIndex _ _).mpr (fun b' => by
          rw [e.wIndex_wMap,
            (F.toSliceDomPFunctor.compatible_iff F.wIndex x.1.1 x.1.2).mp x.2
              ((e.posEquiv x.1.1).symm b'),
            ← e.r_comm x.1.1 ((e.posEquiv x.1.1).symm b'), Equiv.apply_symm_apply])⟩ :=
  rfl

/-- `symm.wMap` after `wMap` is the identity. -/
theorem symm_wMap_wMap (e : Iso F G) (z : F.W) : e.symm.wMap (e.wMap z) = z :=
  W.induction (F := F)
    (motive := fun z => e.symm.wMap (e.wMap z) = z)
    (fun x ih => by
      change e.symm.wMap (e.wMap (W.mk x)) = W.mk x
      rw [wMap_mk, wMap_mk]
      refine congrArg W.mk (Subtype.ext (Sigma.ext ?_ ?_))
      · exact e.shapeEquiv.symm_apply_apply x.1.1
      · refine Function.hfunext (congrArg F.B (e.shapeEquiv.symm_apply_apply x.1.1)) ?_
        intro b' b hb
        apply heq_of_eq
        dsimp only
        rw [ih ((e.posEquiv x.1.1).symm ((e.symm.posEquiv (e.shapeEquiv x.1.1)).symm b')),
          posEquiv_symm_comp]
        exact congrArg _ (cast_eq_iff_heq.mpr hb))
    z

/-- `wMap` after `symm.wMap` is the identity. -/
theorem wMap_symm_wMap (e : Iso F G) (z : G.W) : e.wMap (e.symm.wMap z) = z :=
  W.induction (F := G)
    (motive := fun z => e.wMap (e.symm.wMap z) = z)
    (fun x ih => by
      change e.wMap (e.symm.wMap (W.mk x)) = W.mk x
      rw [wMap_mk, wMap_mk]
      refine congrArg W.mk (Subtype.ext (Sigma.ext ?_ ?_))
      · exact e.shapeEquiv.apply_symm_apply x.1.1
      · refine Function.hfunext (congrArg G.B (e.shapeEquiv.apply_symm_apply x.1.1)) ?_
        intro b'' b hb
        apply heq_of_eq
        dsimp only
        rw [ih ((e.symm.posEquiv x.1.1).symm ((e.posEquiv (e.symm.shapeEquiv x.1.1)).symm b''))]
        exact congrArg _ ((posEquiv_symm_comp' e x.1.1 b'').trans (cast_eq_iff_heq.mpr hb)))
    z

/-- The equivalence of W-types induced by an isomorphism. -/
def wEquiv (e : Iso F G) : F.W ≃ G.W where
  toFun := e.wMap
  invFun := e.symm.wMap
  left_inv := e.symm_wMap_wMap
  right_inv := e.wMap_symm_wMap

/-- The induced equivalence of W-type fibres over a fixed index `i`. -/
def wEquivFiber (e : Iso F G) (i : I) :
    { w : F.W // F.wIndex w = i } ≃ { w' : G.W // G.wIndex w' = i } where
  toFun w := ⟨e.wMap w.1, (e.wIndex_wMap w.1).trans w.2⟩
  invFun w' := ⟨e.symm.wMap w'.1, (e.symm.wIndex_wMap w'.1).trans w'.2⟩
  left_inv w := Subtype.ext (e.symm_wMap_wMap w.1)
  right_inv w' := Subtype.ext (e.wMap_symm_wMap w'.1)

end Iso

end SlicePFunctor
