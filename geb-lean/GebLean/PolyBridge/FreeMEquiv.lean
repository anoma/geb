import GebLean.PolyBridge.WEquiv
import GebLean.SliceW.Iso
import GebLean.SliceW.FreeM
import Mathlib.Logic.Equiv.Sum

/-!
# The translate augmentation isomorphism and the free-monad equivalence

Relates this development's free monad `PolyFreeM V P` (`GebLean/PolyAlg.lean`),
built as the initial algebra of the translate polynomial `V + P(-)`, to the
slice free monad `SlicePFunctor.FreeM V.hom (toSlice P)` (`GebLean/SliceW/`),
built as the fiber of the W-type of the slice augmentation
`SlicePFunctor.translate V.hom (toSlice P)`. Both present the free monad on
the polynomial endofunctor `P` with leaves `V`, in the sense of Gambino–Kock;
the two augmentations are the same slice endofunctor `V + P(-)` under the
translation `toSlice` (`GebLean/PolyBridge/Slice.lean`), and `translateSliceIso`
is that identification as a container isomorphism.

The isomorphism's shape equivalence distributes the sigma of the augmented
index over its coproduct
(`Σ x, ({ a // V.hom a = x } ⊕ polyBetweenIndex X X P x)`) into
`V.left ⊕ Σ x, polyBetweenIndex X X P x` and contracts the leaf summand along
`Equiv.sigmaFiberEquiv V.hom`. Positions and the two structure maps agree at
node shapes definitionally; at leaf shapes positions are empty and the
shape-output map agrees by the leaf's stored fiber witness. The free-monad
equivalence then composes the initial-algebra comparison `polyFixSliceEquiv`
with the W-type transport `Iso.wEquivFiber` of this isomorphism.

## Main definitions

* `translateSliceIso` — the container isomorphism
  `toSlice (polyTranslate V P) ≅ SlicePFunctor.translate V.hom (toSlice P)`.
* `polyFreeMSliceEquiv` — the fiberwise equivalence
  `PolyFreeM V P x ≃ SlicePFunctor.FreeM V.hom (toSlice P) x`.

## References

N. Gambino and J. Kock, "Polynomial functors and polynomial monads",
Mathematical Proceedings of the Cambridge Philosophical Society 154 (2013)
153-192, DOI `10.1017/S0305004112000394`.

M. Abbott, T. Altenkirch, N. Ghani, "Containers: Constructing strictly
positive types", Theoretical Computer Science 342 (2005) 3-27, DOI
`10.1016/j.tcs.2005.06.002`.

## Tags

free monad, W-type, initial algebra, container, slice category, PFunctor,
polynomial functor
-/

namespace GebLean.PolyBridge

open CategoryTheory

universe u

/-- The container isomorphism identifying the translation of the legacy
translate polynomial `polyTranslate V P` with the slice augmentation
`SlicePFunctor.translate V.hom (toSlice P)`. The shape equivalence distributes
the sigma of the augmented index over its coproduct via `Equiv.sigmaSumDistrib`
and contracts the leaf summand `Σ x, { a // V.hom a = x }` to `V.left` via
`Equiv.sigmaFiberEquiv V.hom`. Positions coincide at every shape (empty at
leaves, `P`'s positions at nodes); the shape-output map agrees by the leaf's
fiber witness at leaf shapes and definitionally at nodes; the direction-input
map agrees vacuously at leaves and definitionally at nodes. -/
def translateSliceIso {X : Type u} (V : Over X) (P : PolyEndo X) :
    SlicePFunctor.Iso (toSlice (polyTranslate V P))
      (SlicePFunctor.translate V.hom (toSlice P)) where
  shapeEquiv :=
    (Equiv.sigmaSumDistrib (fun x => { a : V.left // V.hom a = x })
        (fun x => polyBetweenIndex X X P x)).trans
      (Equiv.sumCongr (Equiv.sigmaFiberEquiv V.hom) (Equiv.refl _))
  posEquiv := fun a => match a with
    | ⟨_, Sum.inl _⟩ => Equiv.refl _
    | ⟨_, Sum.inr _⟩ => Equiv.refl _
  q_comm := fun a => match a with
    | ⟨_, Sum.inl ⟨_, hv⟩⟩ => hv
    | ⟨_, Sum.inr _⟩ => rfl
  r_comm := fun a b => match a, b with
    | ⟨_, Sum.inl _⟩, b => b.elim
    | ⟨_, Sum.inr _⟩, _ => rfl

/-- The fiberwise equivalence between the legacy free monad `PolyFreeM V P x`
and the slice free monad `SlicePFunctor.FreeM V.hom (toSlice P) x`. It composes
the initial-algebra comparison `polyFixSliceEquiv` for the translate polynomial
with the W-type transport `Iso.wEquivFiber` of `translateSliceIso`. -/
def polyFreeMSliceEquiv {X : Type u} (V : Over X) (P : PolyEndo X) (x : X) :
    PolyFreeM V P x ≃ SlicePFunctor.FreeM V.hom (toSlice P) x :=
  (polyFixSliceEquiv (polyTranslate V P) x).trans ((translateSliceIso V P).wEquivFiber x)

end GebLean.PolyBridge
