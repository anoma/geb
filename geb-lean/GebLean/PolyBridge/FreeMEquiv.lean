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

## Main statements

* `polyFreeMSliceEquiv_transport` — the equivalence commutes with reindexing a
  tree along an equality of indices.
* `polyFreeMSliceEquiv_pure` — the equivalence carries the legacy leaf
  `polyFreeMPure` to the slice free monad's `pure`.
* `polyFreeMSliceEquiv_node` — the equivalence carries a legacy node to the
  slice free monad's `node`.
* `polyFreeMSliceEquiv_bind` — the equivalence intertwines the legacy free-monad
  bind with the slice free monad's `bind`.

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

/-- Transport naturality: `polyFreeMSliceEquiv` commutes with reindexing a tree
along an equality of indices. Mirrors Phase A's `toSliceW_transport`. -/
theorem polyFreeMSliceEquiv_transport {X : Type u} (V : Over X) (P : PolyEndo X)
    {x x' : X} (h : x = x') (t : PolyFreeM V P x) :
    polyFreeMSliceEquiv V P x' (h ▸ t) = h ▸ polyFreeMSliceEquiv V P x t := by
  subst h
  rfl

/-- Pure naturality: `polyFreeMSliceEquiv` carries the legacy leaf
`polyFreeMPure V P a` to the slice free monad's `pure a`. -/
theorem polyFreeMSliceEquiv_pure {X : Type u} (V : Over X) (P : PolyEndo X) (x : X)
    (a : { v : V.left // V.hom v = x }) :
    polyFreeMSliceEquiv V P x (polyFreeMPure V P a) = SlicePFunctor.FreeM.pure a :=
  Subtype.ext
    (congrArg SlicePFunctor.W.mk
      (Subtype.ext (Sigma.ext rfl (heq_of_eq (funext fun e => e.elim)))))

/-- Node naturality: `polyFreeMSliceEquiv` carries a legacy node
`PolyFix.mk x (Sum.inr p) ch` to the slice free monad's `node ⟨x, p⟩` with the
children mapped through the equivalence. -/
theorem polyFreeMSliceEquiv_node {X : Type u} (V : Over X) (P : PolyEndo X) (x : X)
    (p : polyBetweenIndex X X P x)
    (ch : ∀ e : (polyBetweenFamily X X (polyTranslate V P) x (Sum.inr p)).left,
      PolyFreeM V P ((polyBetweenFamily X X (polyTranslate V P) x (Sum.inr p)).hom e)) :
    polyFreeMSliceEquiv V P x (PolyFix.mk x (Sum.inr p) ch) =
      SlicePFunctor.FreeM.node (F := toSlice P) (v := V.hom) ⟨x, p⟩
        (fun e => polyFreeMSliceEquiv V P _ (ch e)) :=
  rfl

/-- Bind naturality: `polyFreeMSliceEquiv` intertwines the legacy free-monad
bind `polyFreeMBind` with the slice free monad's `bind`. Proved by `PolyFix.ind`
on the legacy tree, the only place where legacy elimination is admitted. -/
theorem polyFreeMSliceEquiv_bind {X : Type u} (V B : Over X) (P : PolyEndo X) (x : X)
    (t : PolyFreeM V P x)
    (f : ∀ y, { a : V.left // V.hom a = y } → PolyFreeM B P y) :
    polyFreeMSliceEquiv B P x (polyFreeMBind V B P t f) =
      (polyFreeMSliceEquiv V P x t).bind
        (fun y a => polyFreeMSliceEquiv B P y (f y a)) :=
  PolyFix.ind (P := polyTranslate V P)
    (motive := fun {y} t =>
      polyFreeMSliceEquiv B P y (polyFreeMBind V B P t f) =
        (polyFreeMSliceEquiv V P y t).bind
          (fun z a => polyFreeMSliceEquiv B P z (f z a)))
    (fun {y} i children ih => by
      match i with
      | Sum.inl a =>
          have hpure :
              polyFreeMSliceEquiv V P y
                  (@PolyFix.mk X (polyTranslate V P) y (Sum.inl a) children) =
                SlicePFunctor.FreeM.pure a :=
            Subtype.ext (congrArg SlicePFunctor.W.mk
              (Subtype.ext (Sigma.ext rfl (heq_of_eq (funext fun e => e.elim)))))
          change polyFreeMSliceEquiv B P y (f y a) =
              (polyFreeMSliceEquiv V P y
                  (@PolyFix.mk X (polyTranslate V P) y (Sum.inl a) children)).bind
                (fun z a => polyFreeMSliceEquiv B P z (f z a))
          rw [hpure]
          exact (SlicePFunctor.FreeM.pure_bind a
            (fun z a => polyFreeMSliceEquiv B P z (f z a))).symm
      | Sum.inr p =>
          simp only [polyFreeMBind]
          rw [polyFreeMSliceEquiv_node, polyFreeMSliceEquiv_node]
          refine Eq.trans ?_ (SlicePFunctor.FreeM.bind_node (F := toSlice P) (v := V.hom)
            ⟨y, p⟩ _ (fun z a => polyFreeMSliceEquiv B P z (f z a))).symm
          exact congrArg (SlicePFunctor.FreeM.node (F := toSlice P) (v := B.hom) ⟨y, p⟩)
            (funext fun e => ih e))
    t

end GebLean.PolyBridge
