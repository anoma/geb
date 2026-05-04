import GebLean.PolyAlg
import GebLean.PolyUMorph
import GebLean.Utilities.Slice

/-!
# Polynomial Combinators

Generic combinators for constructing polynomial
functors between slice categories.

Every function `f : X → Y` induces three functors
between slice categories, forming an adjoint triple:

  `Σ_f ⊣ f* ⊣ Π_f`

where `Σ_f : Over X → Over Y` is the dependent sum
(postcomposition with `f`), `f* : Over Y → Over X`
is base change (pullback along `f`), and
`Π_f : Over X → Over Y` is the dependent product.
Each of these is representable as a polynomial functor.
Every polynomial functor decomposes as `Σ_t ∘ Π_p ∘ s*`
for a suitable diagram (Gambino-Kock).

The existing left Kan extension adjunction
`polyBetweenLKanAdj` in `PolyUMorph.lean` provides
the `Σ ⊣ f*` adjunction at the level of polynomial
functor categories.
-/

namespace GebLean

open CategoryTheory

universe u

/--
Base change (pullback) along `f : X → Y`, as a
polynomial `PolyBetween Y X`.

At fiber `x : X`, one position (`PUnit`) with one
direction (`PUnit`) mapping to `f x : Y`.  Evaluation
at `(A →^g Y) : Over Y` yields the pullback:
the fiber of `A` over `f x`.

This is the polynomial representation of `f*` in the
adjoint triple `Σ_f ⊣ f* ⊣ Π_f`.
-/
def polyBaseChange {X : Type u} {Y : Type u}
    (f : X → Y) :
    PolyFunctorBetweenCat Y X :=
  fun x => ccrObjMk
    (fun _ : PUnit.{u + 1} =>
      Over.mk
        (fun _ : PUnit.{u + 1} => f x))

/--
Dependent sum along `f : X → Y`, as a polynomial
`PolyBetween X Y`.

At fiber `y : Y`, positions are elements of the
preimage `{ x : X // f x = y }`, each with a single
direction (`PUnit`) mapping to `x`.  Evaluation at
`(A →^g X) : Over X` yields the dependent sum:
`Σ (x : X) (f x = y), A_x`.

This is the polynomial representation of `Σ_f` in
the adjoint triple `Σ_f ⊣ f* ⊣ Π_f`.  The left Kan
extension `polyBetweenLKanObj (polySigma f)` provides
the functorial action of `Σ_f` on polynomial
functors.
-/
def polySigma {X : Type u} {Y : Type u}
    (f : X → Y) :
    PolyFunctorBetweenCat X Y :=
  fun y => ccrObjMk
    (fun (xp : { x : X // f x = y }) =>
      Over.mk
        (fun _ : PUnit.{u + 1} => xp.val))

/--
Reindex a polynomial endofunctor along `f : X → Y`.

Defined as `Σ_f ∘ Lan_{Σ_f}(P)`: the left Kan
extension of `P` along `Σ_f` (changing the domain
from `X` to `Y`), followed by composition with `Σ_f`
(changing the codomain from `X` to `Y`).
-/
def polyFiberReindex {X : Type u} {Y : Type u}
    (f : X → Y)
    (P : PolyFunctorBetweenCat X X) :
    PolyFunctorBetweenCat Y Y :=
  polyBetweenComp (polySigma f)
    (polyBetweenLKanObj (polySigma f) P)

/--
Restrict a polynomial to a single fiber.

At fiber `x = j`, the result is `P x`. At all other
fibers, the result has no positions.
-/
def polyAtFiber {X : Type u} [DecidableEq X]
    (j : X)
    (P : PolyFunctorBetweenCat X X) :
    PolyFunctorBetweenCat X X :=
  fun x =>
    if _ : x = j then
      P x
    else
      ccrObjMk
        (fun (e : PEmpty.{u + 1}) =>
          PEmpty.elim e)

/--
A polynomial with `Nat`-indexed positions at every
fiber, where position `n` has `Fin n` directions, each
mapping to `target`.
-/
def polyNatDirs {X : Type u} {Y : Type u}
    (target : X) :
    PolyFunctorBetweenCat X Y :=
  fun _ => ccrObjMk
    (fun (n : ULift.{u} Nat) =>
      Over.mk
        (fun (_ : ULift.{u} (Fin n.down)) =>
          target))

end GebLean
