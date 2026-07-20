import GebLean.Polynomial
import GebLean.PolyAlg
import Geb.Mathlib.Data.PFunctor.Slice.Basic

/-!
# Translating `PolyEndo` to `SlicePFunctor`

Translates this development's Grothendieck-construction presentation of a
polynomial endofunctor (`PolyEndo X`, `GebLean/PolyAlg.lean`) to the
vendored `geb-mathlib` `SlicePFunctor` presentation
(`Geb.Mathlib.Data.PFunctor.Slice.Basic`), both dependent polynomial
functors on `Type X` in the sense of Gambino–Kock, equivalently containers
in the sense of Abbott–Altenkirch–Ghani. The two presentations differ only
in packaging: `PolyEndo X` names its shapes and their positions through a
coproduct-of-representables family indexed by the codomain point, while
`SlicePFunctor` names the same data through a single shape type with a
shape-output map `q` and a direction-input map `r`. `toSlice` re-packages
one into the other without altering the functor.

## Main definitions

* `toSlice` — the translation `PolyEndo X → SlicePFunctor X X`: shapes are
  pairs of a codomain point and a position there, positions at a shape are
  the corresponding representable's carrier, the shape-output map recovers
  the codomain point, and the direction-input map is the representable's
  structure map.

## Main statements

* `toSlice_A`, `toSlice_B`, `toSlice_q`, `toSlice_r` — the characterization
  of each field of `toSlice P` in terms of `P`'s data.

## References

N. Gambino and J. Kock, "Polynomial functors and polynomial monads",
Mathematical Proceedings of the Cambridge Philosophical Society 154 (2013)
153-192, DOI `10.1017/S0305004112000394`.

M. Abbott, T. Altenkirch, N. Ghani, "Containers: Constructing strictly
positive types", Theoretical Computer Science 342 (2005) 3-27, DOI
`10.1016/j.tcs.2005.06.002`.

## Tags

polynomial functor, slice category, container, PFunctor
-/

namespace GebLean.PolyBridge

universe u

/-- Translate a `PolyEndo X` (the coproduct-of-representables presentation
of a polynomial endofunctor on `Over X`) to a `SlicePFunctor X X` (the
shape/position presentation with explicit shape-output and direction-input
maps). Shapes are pairs `⟨x, i⟩` of a codomain point `x` and a position `i`
of `P` there; positions at such a shape are the carrier of the
representable `P` assigns to `⟨x, i⟩`; the shape-output map recovers `x`;
the direction-input map is that representable's structure map into `X`. -/
def toSlice {X : Type u} (P : PolyEndo X) : SlicePFunctor.{u, u, u, u} X X where
  A := Σ x : X, polyBetweenIndex X X P x
  B := fun z => (polyBetweenFamily X X P z.1 z.2).left
  r := fun z => (polyBetweenFamily X X P z.1.1 z.1.2).hom z.2
  q := fun z => z.1

/-- The shape type of `toSlice P` is pairs of a codomain point and a
position of `P` there. -/
@[simp]
theorem toSlice_A {X : Type u} (P : PolyEndo X) :
    (toSlice P).A = Σ x : X, polyBetweenIndex X X P x :=
  rfl

/-- The position type of `toSlice P` at a shape `⟨x, i⟩` is the carrier of
the representable `P` assigns to `⟨x, i⟩`. -/
@[simp]
theorem toSlice_B {X : Type u} (P : PolyEndo X) (z : (toSlice P).A) :
    (toSlice P).B z = (polyBetweenFamily X X P z.1 z.2).left :=
  rfl

/-- The shape-output map of `toSlice P` recovers the codomain point of the
shape. -/
@[simp]
theorem toSlice_q {X : Type u} (P : PolyEndo X) (z : (toSlice P).A) :
    (toSlice P).q z = z.1 :=
  rfl

/-- The direction-input map of `toSlice P` at a position `e` of shape
`z = ⟨x, i⟩` is the structure map of the representable `P` assigns to
`⟨x, i⟩`, applied to `e`. -/
@[simp]
theorem toSlice_r {X : Type u} (P : PolyEndo X) (z : (toSlice P).A)
    (e : (toSlice P).B z) :
    (toSlice P).r ⟨z, e⟩ = (polyBetweenFamily X X P z.1 z.2).hom e :=
  rfl

end GebLean.PolyBridge
