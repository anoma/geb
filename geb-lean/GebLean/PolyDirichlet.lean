import GebLean.Polynomial
import GebLean.Utilities.Equalities

/-!
# Dirichlet Product of Polynomial Functors

The Dirichlet product (parallel product) is a monoidal
structure on polynomial functors distinct from composition
and the categorical product. Given polynomials
`P, Q : PolyFunctorBetweenCat X Y`, the Dirichlet product
`P ⊗ Q` pairs positions and takes fiberwise products
(pullbacks in `Over X`) of directions.

The Dirichlet product is the Day convolution on
`Poly ≅ Σ(Set^op)` with respect to the cartesian monoidal
structure on `Set^op`. It is determined by its values on
representables: `y^A ⊗ y^B ≅ y^(A × B)`.

## Main definitions

* `overPullback` - Binary pullback (fiber product) in
  `Over X`
* `polyBetweenDirichlet` - Dirichlet product of
  polynomial functors
* `polyBetweenDirichletUnit` - Unit for the Dirichlet
  product
* `polyBetweenDirichletMap` - Bifunctorial action
* `polyBetweenDirichletClosure` - Internal hom for the
  Dirichlet monoidal structure
* `polyBetweenDirichletEval` - Evaluation morphism
* `polyBetweenDirichletCurry` - Currying
-/

namespace GebLean

open CategoryTheory

universe u

/-! ## Binary pullback in Over X

The binary pullback of `A, B : Over X` is the fiber
product `{ (a, b) | A.hom a = B.hom b }` with the common
projection to `X`.
-/

section OverPullback

variable {X : Type u}

/--
The underlying type of the binary pullback in `Over X`:
pairs `(a, b)` whose projections to `X` agree.
-/
def overPullbackType (A B : Over X) : Type u :=
  { ab : A.left × B.left // A.hom ab.1 = B.hom ab.2 }

/--
The binary pullback (fiber product) in `Over X`.
-/
def overPullback (A B : Over X) : Over X :=
  Over.mk (fun (p : overPullbackType A B) =>
    A.hom p.val.1)

/--
First projection from the pullback.
-/
def overPullbackFst (A B : Over X) :
    overPullback A B ⟶ A :=
  Over.homMk (fun p => p.val.1) rfl

/--
Second projection from the pullback.
-/
def overPullbackSnd (A B : Over X) :
    overPullback A B ⟶ B :=
  Over.homMk (fun p => p.val.2)
    (by funext p; exact p.property.symm)

end OverPullback

/-! ## Dirichlet product

For polynomial functors `P, Q : PolyFunctorBetweenCat X Y`,
the Dirichlet product has paired positions and pullback
(fiber product) directions.
-/

section DirichletProduct

variable {X Y : Type u}

/--
The position type of the Dirichlet product at `y`.
-/
def polyBetweenDirichletPos
    (P Q : PolyFunctorBetweenCat X Y) (y : Y) :=
  polyBetweenIndex X Y P y × polyBetweenIndex X Y Q y

/--
The family (directions) of the Dirichlet product at
position `(ip, iq)`: the pullback of the two families
in `Over X`.
-/
def polyBetweenDirichletFamily
    (P Q : PolyFunctorBetweenCat X Y) (y : Y)
    (p : polyBetweenDirichletPos P Q y) : Over X :=
  overPullback
    (polyBetweenFamily X Y P y p.1)
    (polyBetweenFamily X Y Q y p.2)

/--
The Dirichlet product of polynomial functors.
-/
def polyBetweenDirichlet
    (P Q : PolyFunctorBetweenCat X Y) :
    PolyFunctorBetweenCat X Y :=
  fun y => ccrObjMk (polyBetweenDirichletFamily P Q y)

end DirichletProduct

/-! ## Functoriality of the pullback and Dirichlet product

The pullback is functorial in both arguments. Given
morphisms `fA : A ⟶ A'` and `fB : B ⟶ B'` in `Over X`,
the induced map sends `(a, b, proof)` to
`(fA a, fB b, proof')`.

The Dirichlet product is bifunctorial: given morphisms
`α : P ⟶ P'` and `β : Q ⟶ Q'`, the induced morphism
reindexes positions and maps pullback directions via the
universal property.
-/

section Functoriality

variable {X Y : Type u}

/--
Functorial action of the pullback on morphisms in
`Over X`.
-/
def overPullbackMap {A A' B B' : Over X}
    (fA : A ⟶ A') (fB : B ⟶ B') :
    overPullback A B ⟶ overPullback A' B' :=
  Over.homMk
    (fun p =>
      let a' := fA.left p.val.1
      let b' := fB.left p.val.2
      let hA := congrFun (Over.w fA) p.val.1
      let hB := congrFun (Over.w fB) p.val.2
      ⟨(a', b'), hA.trans (p.property.trans hB.symm)⟩)
    (by funext p; exact congrFun (Over.w fA) p.val.1)

/--
The Dirichlet product's reindexing action at a fixed
`y`: pairs the reindexing functions of `α` and `β`.
-/
def polyBetweenDirichletMapReindex
    {P P' Q Q' : PolyFunctorBetweenCat X Y}
    (α : P ⟶ P') (β : Q ⟶ Q') (y : Y)
    (p : polyBetweenDirichletPos P Q y) :
    polyBetweenDirichletPos P' Q' y :=
  (ccrReindex (α y) p.1, ccrReindex (β y) p.2)

/--
The Dirichlet product's fiber morphism at a fixed
`y` and position: the pullback of the two fiber morphisms.
-/
def polyBetweenDirichletMapFiber
    {P P' Q Q' : PolyFunctorBetweenCat X Y}
    (α : P ⟶ P') (β : Q ⟶ Q') (y : Y)
    (p : polyBetweenDirichletPos P Q y) :
    polyBetweenDirichletFamily P' Q' y
      (polyBetweenDirichletMapReindex α β y p) ⟶
    polyBetweenDirichletFamily P Q y p :=
  overPullbackMap
    (ccrFiberMor (α y) p.1)
    (ccrFiberMor (β y) p.2)

/--
Bifunctorial action of the Dirichlet product on
morphisms of polynomial functors.
-/
def polyBetweenDirichletMap
    {P P' Q Q' : PolyFunctorBetweenCat X Y}
    (α : P ⟶ P') (β : Q ⟶ Q') :
    polyBetweenDirichlet P Q ⟶
    polyBetweenDirichlet P' Q' :=
  fun y => ccrHomMk
    (polyBetweenDirichletMapReindex α β y)
    (polyBetweenDirichletMapFiber α β y)

end Functoriality

/-! ## Dirichlet unit

The unit for the Dirichlet product has a single position
(per codomain point) and the terminal object
`Over.mk (id : X → X)` as its family. The pullback of
`id : X → X` with any `f : A → X` is isomorphic to `A`,
making this a left and right unit up to isomorphism.
-/

section DirichletUnit

variable {X Y : Type u}

/--
The unit for the Dirichlet product.
-/
def polyBetweenDirichletUnit :
    PolyFunctorBetweenCat X Y :=
  fun _ => ccrObjMk (fun (_ : PUnit) => Over.mk id)

end DirichletUnit

/-! ## Dirichlet closure (internal hom)

The Dirichlet closure `[P, Q]` is the internal hom for the
Dirichlet monoidal structure. It is characterized by the
adjunction `Hom(R ⊗ P, Q) ≅ Hom(R, [P, Q])`.

Concretely, `[P, Q]` is the categorical product
`Π_{ip} [y^{P.fam(ip)}, Q]` of representable Dirichlet
closures. The representable closure `[y^A, Q]` has
positions `Σ (iq : Pos_Q), (Q.fam(iq) ⟶ A)` and family
`Q.fam(iq)`.

Unfolding the categorical product, the combined closure
has:
- Positions: `(α : Pos_P → Pos_Q) ×
  (∀ ip, Q.fam(α ip) ⟶ P.fam(ip))`
- Family at `(α, g)`: `∐' (fun ip => Q.fam(α ip))`
-/

section DirichletClosure

variable {X Y : Type u}

/--
The position type of the Dirichlet closure at `y`:
a function from `P`-positions to `Q`-positions together
with a family of `Over X` morphisms from `Q`-directions
to `P`-directions.
-/
def polyBetweenDirichletClosurePos
    (P Q : PolyFunctorBetweenCat X Y) (y : Y) :=
  (α : polyBetweenIndex X Y P y →
       polyBetweenIndex X Y Q y) ×
  (∀ (ip : polyBetweenIndex X Y P y),
    polyBetweenFamily X Y Q y (α ip) ⟶
    polyBetweenFamily X Y P y ip)

/--
The family (directions) of the Dirichlet closure at
position `(α, g)`: the coproduct over `P`-positions of
`Q`-directions at the corresponding `Q`-position.
-/
def polyBetweenDirichletClosureFamily
    (P Q : PolyFunctorBetweenCat X Y) (y : Y)
    (p : polyBetweenDirichletClosurePos P Q y) :
    Over X :=
  ∐' (fun (ip : polyBetweenIndex X Y P y) =>
    polyBetweenFamily X Y Q y (p.1 ip))

/--
The Dirichlet closure (internal hom) of polynomial
functors.
-/
def polyBetweenDirichletClosure
    (P Q : PolyFunctorBetweenCat X Y) :
    PolyFunctorBetweenCat X Y :=
  fun y => ccrObjMk
    (polyBetweenDirichletClosureFamily P Q y)

end DirichletClosure

/-! ## Evaluation and currying

The evaluation morphism
`eval : [P, Q] ⊗ P ⟶ Q`
and currying
`curry : (R ⊗ P ⟶ Q) → (R ⟶ [P, Q])`
witness the adjunction
`Hom(R ⊗ P, Q) ≅ Hom(R, [P, Q])`.
-/

section EvalAndCurry

variable {X Y : Type u}

/--
The evaluation morphism's reindexing: applies the
position function to the `P`-position.
-/
def polyBetweenDirichletEvalReindex
    (P Q : PolyFunctorBetweenCat X Y) (y : Y)
    (p : polyBetweenDirichletPos
      (polyBetweenDirichletClosure P Q) P y) :
    polyBetweenIndex X Y Q y :=
  p.1.1 p.2

/--
The evaluation morphism's fiber map: given
`q ∈ Q.fam(α(ip))`, inject `q` into the closure family's
coproduct at component `ip`, and apply the fiber morphism
`g(ip)` to produce the `P`-family element, forming a
pullback pair.
-/
def polyBetweenDirichletEvalFiber
    (P Q : PolyFunctorBetweenCat X Y) (y : Y)
    (p : polyBetweenDirichletPos
      (polyBetweenDirichletClosure P Q) P y) :
    polyBetweenFamily X Y Q y
      (polyBetweenDirichletEvalReindex P Q y p) ⟶
    polyBetweenDirichletFamily
      (polyBetweenDirichletClosure P Q) P y p :=
  Over.homMk
    (fun q =>
      let ip := p.2
      let g := p.1.2
      ⟨(⟨ip, q⟩, (g ip).left q),
        (congrFun (Over.w (g ip)) q).symm⟩)
    rfl

/--
The evaluation morphism
`[P, Q] ⊗ P ⟶ Q`.
-/
def polyBetweenDirichletEval
    (P Q : PolyFunctorBetweenCat X Y) :
    polyBetweenDirichlet
      (polyBetweenDirichletClosure P Q) P ⟶ Q :=
  fun y => ccrHomMk
    (polyBetweenDirichletEvalReindex P Q y)
    (polyBetweenDirichletEvalFiber P Q y)

/--
The currying operation's reindexing: given
`f : R ⊗ P ⟶ Q` and a position `ir` of `R`, produce
a closure position `(α, g)` where `α(ip) = f.reindex(ir, ip)`
and `g(ip)` is the `P`-projection of `f`'s fiber map.
-/
def polyBetweenDirichletCurryReindex
    (P Q R : PolyFunctorBetweenCat X Y)
    (f : polyBetweenDirichlet R P ⟶ Q)
    (y : Y)
    (ir : polyBetweenIndex X Y R y) :
    polyBetweenDirichletClosurePos P Q y :=
  ⟨fun ip => ccrReindex (f y) ⟨ir, ip⟩,
   fun ip =>
     ccrFiberMor (f y) ⟨ir, ip⟩ ≫
       overPullbackSnd _ _⟩

/--
The currying operation's fiber map: given
`(ip, q)` in the closure family's coproduct, apply `f`'s
fiber map to `q` and project to the `R`-family.
-/
def polyBetweenDirichletCurryFiber
    (P Q R : PolyFunctorBetweenCat X Y)
    (f : polyBetweenDirichlet R P ⟶ Q)
    (y : Y)
    (ir : polyBetweenIndex X Y R y) :
    polyBetweenDirichletClosureFamily P Q y
      (polyBetweenDirichletCurryReindex P Q R f y ir) ⟶
    polyBetweenFamily X Y R y ir :=
  Over.homMk
    (fun ⟨ip, q⟩ =>
      (ccrFiberMor (f y) ⟨ir, ip⟩ ≫
        overPullbackFst _ _).left q)
    (by
      funext ⟨ip, q⟩
      exact congrFun
        (Over.w (ccrFiberMor (f y) ⟨ir, ip⟩ ≫
          overPullbackFst _ _)) q)

/--
Currying: given `f : R ⊗ P ⟶ Q`, produce
`R ⟶ [P, Q]`.
-/
def polyBetweenDirichletCurry
    (P Q R : PolyFunctorBetweenCat X Y)
    (f : polyBetweenDirichlet R P ⟶ Q) :
    R ⟶ polyBetweenDirichletClosure P Q :=
  fun y => ccrHomMk
    (polyBetweenDirichletCurryReindex P Q R f y)
    (polyBetweenDirichletCurryFiber P Q R f y)

end EvalAndCurry

end GebLean
