import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.Data.PFunctor.Univariate.Basic
import GebLean.Paranatural
import GebLean.ParanatAlg
import GebLean.Polynomial
import GebLean.PolyAlg

/-!
# Polynomial Profunctors

This module defines polynomial profunctors and their algebras. A polynomial
profunctor is the bivariant generalization of a polynomial functor, with both
contravariant and covariant occurrences of the variable.

## Main definitions

* `PolyProf` - A polynomial profunctor on `Type`, specified by a type of
  positions and two arity families (negative and positive).

* `PolyProf.eval` - Evaluation of a polynomial profunctor at types V and W.

* `PolyProf.DiagElem` - Diagonal elements of a polynomial profunctor, which
  generalize algebras for endofunctors.

## References

* https://ncatlab.org/nlab/show/polynomial+functor
* https://ncatlab.org/nlab/show/profunctor
-/

namespace GebLean

open CategoryTheory

universe u

/-! ## Polynomial Profunctors

A polynomial profunctor P : Type^op × Type → Type is specified by:
- A type B of positions (constructors)
- For each b : B, a type of negative directions (contravariant inputs)
- For each b : B, a type of positive directions (covariant outputs)

The evaluation is:
```
P(V,W) = Σ_{b : B} ((arity_neg b → V) → (arity_pos b → W))
```
-/

/--
A polynomial profunctor on Type.

This is determined by:
- A type B of positions (constructors)
- For each b : B, a type of negative directions (contravariant inputs)
- For each b : B, a type of positive directions (covariant outputs)

The evaluation formula is `P(V,W) = Σ_b ((arity_neg b → V) → (arity_pos b → W))`.
-/
structure PolyProf where
  /-- The type of positions (constructors) -/
  B : Type u
  /-- The arity of negative (contravariant) directions at each position -/
  arity_neg : B → Type u
  /-- The arity of positive (covariant) directions at each position -/
  arity_pos : B → Type u

namespace PolyProf

variable (P : PolyProf.{u})

/--
Evaluate a polynomial profunctor at types V and W.

`P.eval V W = Σ_{b : P.B} ((P.arity_neg b → V) → (P.arity_pos b → W))`
-/
def eval (V W : Type u) : Type u :=
  Σ (b : P.B), ((P.arity_neg b → V) → (P.arity_pos b → W))

/--
Extract the position from an evaluation element.
-/
def evalPos {V W : Type u} (x : P.eval V W) : P.B := x.1

/--
Extract the morphism from an evaluation element.
-/
def evalMor {V W : Type u} (x : P.eval V W) :
    (P.arity_neg (P.evalPos x) → V) → (P.arity_pos (P.evalPos x) → W) := x.2

/--
Construct an evaluation element from position and morphism.
-/
def evalMk {V W : Type u} (b : P.B)
    (f : (P.arity_neg b → V) → (P.arity_pos b → W)) : P.eval V W := ⟨b, f⟩

/--
The covariant action of a polynomial profunctor.
Given `g : W → W'`, maps `P.eval V W → P.eval V W'` by postcomposing.
-/
def covAction {V W W' : Type u} (g : W → W') :
    P.eval V W → P.eval V W' :=
  fun ⟨b, h⟩ => ⟨b, fun k => g ∘ h k⟩

/--
The contravariant action of a polynomial profunctor.
Given `f : V → V'`, maps `P.eval V' W → P.eval V W` by precomposing.
-/
def contravAction {V V' W : Type u} (f : V → V') :
    P.eval V' W → P.eval V W :=
  fun ⟨b, h⟩ => ⟨b, fun k => h (f ∘ k)⟩

@[simp]
lemma covAction_id (V W : Type u) :
    P.covAction (id : W → W) = (id : P.eval V W → P.eval V W) := by
  funext ⟨b, h⟩
  simp only [covAction, id_eq]
  rfl

@[simp]
lemma contravAction_id (V W : Type u) :
    P.contravAction (id : V → V) = (id : P.eval V W → P.eval V W) := by
  funext ⟨b, h⟩
  simp only [contravAction, id_eq]
  rfl

@[simp]
lemma covAction_comp {V W W' W'' : Type u} (g : W → W') (g' : W' → W'') :
    P.covAction (g' ∘ g) = P.covAction g' ∘ P.covAction (V := V) g := by
  funext ⟨b, h⟩
  rfl

@[simp]
lemma contravAction_comp {V V' V'' W : Type u} (f : V → V') (f' : V' → V'') :
    P.contravAction (f' ∘ f) = P.contravAction f ∘ P.contravAction (W := W) f' := by
  funext ⟨b, h⟩
  simp only [contravAction, Function.comp_apply, Function.comp_assoc]

/--
The interchange law: covariant and contravariant actions commute.

This is the naturality condition that makes composition of diagonal element
morphisms work correctly.
-/
@[simp]
lemma covAction_contravAction_comm {V V' W W' : Type u} (f : V → V') (g : W → W')
    (x : P.eval V' W) :
    P.covAction g (P.contravAction f x) = P.contravAction f (P.covAction g x) := by
  obtain ⟨b, h⟩ := x
  simp only [covAction, contravAction]

/-! ### The hom-profunctor

The identity polynomial profunctor represents `Hom(V,W) = V → W`.
-/

/--
The identity polynomial profunctor representing `Hom(V,W) = V → W`.

- Single position (Unit)
- Single negative direction (Unit)
- Single positive direction (Unit)

Evaluation: `(Unit → V) → (Unit → W) ≃ V → W`
-/
def hom : PolyProf.{u} where
  B := PUnit.{u+1}
  arity_neg := fun _ => PUnit.{u+1}
  arity_pos := fun _ => PUnit.{u+1}

/--
The evaluation of the hom-profunctor is isomorphic to the function type.
-/
def homEvalEquiv (V W : Type u) : hom.eval V W ≃ (V → W) where
  toFun := fun ⟨_, f⟩ => fun v => f (fun _ => v) PUnit.unit
  invFun := fun f => ⟨PUnit.unit, fun g _ => f (g PUnit.unit)⟩
  left_inv := fun ⟨PUnit.unit, _⟩ => rfl
  right_inv := fun _ => rfl

/-! ### Coproducts of polynomial profunctors

Polynomial profunctors are closed under coproducts (disjoint union of
positions).
-/

/--
The coproduct of two polynomial profunctors.
-/
def coprod (Q : PolyProf.{u}) : PolyProf.{u} where
  B := P.B ⊕ Q.B
  arity_neg := Sum.elim P.arity_neg Q.arity_neg
  arity_pos := Sum.elim P.arity_pos Q.arity_pos

/--
The evaluation of a coproduct is the coproduct of evaluations.
-/
def coprodEvalEquiv (Q : PolyProf.{u}) (V W : Type u) :
    (P.coprod Q).eval V W ≃ (P.eval V W ⊕ Q.eval V W) where
  toFun := fun ⟨b, f⟩ => match b with
    | Sum.inl bl => Sum.inl ⟨bl, f⟩
    | Sum.inr br => Sum.inr ⟨br, f⟩
  invFun := fun
    | Sum.inl ⟨b, f⟩ => ⟨Sum.inl b, f⟩
    | Sum.inr ⟨b, f⟩ => ⟨Sum.inr b, f⟩
  left_inv := fun ⟨b, f⟩ => by cases b <;> rfl
  right_inv := fun
    | Sum.inl _ => rfl
    | Sum.inr _ => rfl

/-! ### Bifunctor structure

A polynomial profunctor can be viewed as a bifunctor `Type^op × Type → Type`.
The curried form is compatible with `DiagElem` from `Paranatural.lean`.
-/

/--
The bifunctorial action of a polynomial profunctor.
Given `f : V' → V` (contravariant) and `g : W → W'` (covariant),
maps `P.eval V W → P.eval V' W'`.
-/
def bimap {V V' W W' : Type u} (f : V' → V) (g : W → W') :
    P.eval V W → P.eval V' W' :=
  fun ⟨b, h⟩ => ⟨b, fun k => g ∘ h (f ∘ k)⟩

@[simp]
lemma bimap_id (V W : Type u) :
    P.bimap (id : V → V) (id : W → W) = (id : P.eval V W → P.eval V W) := by
  funext ⟨b, h⟩
  simp only [bimap, Function.id_comp, id_eq]

@[simp]
lemma bimap_comp {V V' V'' W W' W'' : Type u}
    (f : V' → V) (f' : V'' → V') (g : W → W') (g' : W' → W'') :
    P.bimap (f ∘ f') (g' ∘ g) = P.bimap f' g' ∘ P.bimap f g := by
  funext ⟨b, h⟩
  simp only [bimap, Function.comp_apply, Function.comp_assoc]

/--
The uncurried bifunctor corresponding to a polynomial profunctor.
-/
def toFunctor : (Type u)ᵒᵖ × Type u ⥤ Type u where
  obj := fun ⟨V, W⟩ => P.eval V.unop W
  map := fun {_ _} ⟨f, g⟩ => P.bimap f.unop g
  map_id := fun ⟨V, W⟩ => P.bimap_id V.unop W
  map_comp := fun {_ _ _} ⟨f, g⟩ ⟨f', g'⟩ => P.bimap_comp f.unop f'.unop g g'

/--
The curried bifunctor corresponding to a polynomial profunctor.
This is compatible with `DiagElem` from `Paranatural.lean`.
Uses mathlib's `Functor.curry` for the currying.
-/
abbrev toCurriedFunctor : (Type u)ᵒᵖ ⥤ Type u ⥤ Type u :=
  Functor.curry.obj P.toFunctor

/-! ### Diagonal elements

A diagonal element of a polynomial profunctor P is a pair (A, α) where
A is a type and α : P.eval A A. This generalizes algebras for endofunctors.

We use `DiagElem` from `Paranatural.lean` applied to `P.toCurriedFunctor`.
The field accessors are:
- `.base : Type u` - the carrier type
- `.elem : P.eval x.base x.base` - the algebra structure
-/

/--
The diagonal element type for a polynomial profunctor.
Uses `DiagElem` from `Paranatural.lean` applied to the curried functor.
-/
abbrev DiagElem : Type (u + 1) := GebLean.DiagElem P.toCurriedFunctor

/--
Morphisms of diagonal elements use `DiagElem.Hom` from `Paranatural.lean`.
A morphism consists of a function on carriers satisfying the compatibility
condition that the covariant action on the source equals the contravariant
action on the target.
-/
abbrev DiagElemHom (x y : P.DiagElem) : Type u :=
  GebLean.DiagElem.Hom P.toCurriedFunctor x y

/--
The category of diagonal elements uses `diagElemCategory` from
`Paranatural.lean`.
-/
instance diagElemCategory : Category P.DiagElem :=
  GebLean.DiagElem.diagElemCategory P.toCurriedFunctor

/--
The diagonal compatibility condition for a polynomial profunctor.

For a morphism `f : V → W` and diagonal elements `d₀ ∈ P.eval V V` and
`d₁ ∈ P.eval W W`, the condition asserts that the covariant action of `f`
on `d₀` equals the contravariant action of `f` on `d₁`.

When instantiated with `toCurriedFunctor`, this is equivalent to
`DiagCompat` from `Paranatural.lean`.
-/
abbrev DiagCompat {V W : Type u} (f : V → W)
    (d₀ : P.eval V V) (d₁ : P.eval W W) : Prop :=
  P.covAction f d₀ = P.contravAction f d₁

/--
The compatibility condition for `toCurriedFunctor` equals our `DiagCompat`.
-/
theorem diagCompat_eq_paranatural {V W : Type u} (f : V → W)
    (d₀ : P.eval V V) (d₁ : P.eval W W) :
    GebLean.DiagCompat P.toCurriedFunctor V W f d₀ d₁ ↔ P.DiagCompat f d₀ d₁ := by
  rfl

end PolyProf

/-! ## PHOAS Example

The Parametric Higher-Order Abstract Syntax (PHOAS) example demonstrates
polynomial profunctors for representing lambda calculus terms with variable
binding.

```haskell
data Expr v = Var v | App (Expr v) (Expr v) | Lam (v -> Expr v)
```

As a profunctor: `P(V,W) = W + W×W + (V → W)`
- Var: arity_neg = Empty, arity_pos = Unit (just W)
- App: arity_neg = Empty, arity_pos = Bool (W × W ≅ (Bool → W))
- Lam: arity_neg = Unit, arity_pos = Unit (V → W)
-/

section PHOAS

/--
Constructors for PHOAS expressions.
-/
inductive PHOASConstructor : Type where
  | var : PHOASConstructor
  | app : PHOASConstructor
  | lam : PHOASConstructor
  deriving DecidableEq, Repr

/--
The PHOAS polynomial profunctor at universe 0.
-/
def phoas : PolyProf.{0} where
  B := PHOASConstructor
  arity_neg := fun
    | .var => PEmpty
    | .app => PEmpty
    | .lam => PUnit
  arity_pos := fun
    | .var => PUnit
    | .app => Bool
    | .lam => PUnit

/--
The PHOAS expression type, defined as a recursive type.

This is intended to be an initial diagonal element of the `phoas` profunctor.
-/
inductive PHOASExpr (V : Type) : Type where
  | var : V → PHOASExpr V
  | app : PHOASExpr V → PHOASExpr V → PHOASExpr V
  | lam : (V → PHOASExpr V) → PHOASExpr V

/--
The algebra structure map for PHOASExpr.

For each constructor, we show how to build a PHOASExpr from the appropriate
inputs:
- Var: from a function `Empty → V` (trivially) and output `() ↦ v`
- App: from a function `Empty → V` (trivially) and output `b ↦ (e₁ if b, e₂ if ¬b)`
- Lam: from a function `() ↦ f` and output `() ↦ lam f`
-/
def phoasAlgMap (V : Type) : phoas.eval (PHOASExpr V) (PHOASExpr V) →
    PHOASExpr V
  | ⟨.var, f⟩ => f PEmpty.elim PUnit.unit
  | ⟨.app, f⟩ => PHOASExpr.app (f PEmpty.elim true) (f PEmpty.elim false)
  | ⟨.lam, f⟩ => PHOASExpr.lam (fun v => f (fun _ => PHOASExpr.var v) PUnit.unit)

end PHOAS

/-! ## Initial and Terminal Diagonal Elements

A diagonal element (A, α) is initial if there is a unique morphism from it
to any other diagonal element. Dually, it is terminal if there is a unique
morphism to it from any other diagonal element.

We use mathlib's `CategoryTheory.Limits.IsInitial` and `IsTerminal` directly.
-/

section InitialTerminalDiagElem

open CategoryTheory.Limits

variable (P : PolyProf.{u})

/--
A diagonal element is initial in the category sense: there exists a unique
morphism from it to any other diagonal element.
-/
abbrev PolyProf.diagElemIsInitial (x : P.DiagElem) : Prop :=
  Nonempty (IsInitial x)

/--
A diagonal element is terminal in the category sense: there exists a unique
morphism to it from any other diagonal element.
-/
abbrev PolyProf.diagElemIsTerminal (x : P.DiagElem) : Prop :=
  Nonempty (IsTerminal x)

end InitialTerminalDiagElem

/-! ## The Empty Diagonal Element

For a polynomial profunctor P with a position b where the positive arity is
empty, the empty type forms a diagonal element at position b.
-/

section EmptyDiagElem

variable (P : PolyProf.{u})

/--
A position with empty positive arity allows an empty-carrier diagonal element.
The negative arity can be anything since the function from empty pos arity is
vacuously defined.
-/
def PolyProf.emptyDiagElem
    (b : P.B) (hpos : IsEmpty (P.arity_pos b)) : P.DiagElem where
  base := PEmpty.{u+1}
  elem := ⟨b, fun _ p => hpos.elim p⟩

/--
There is a morphism from an empty-carrier diagonal element to any other
diagonal element whose element has the same position.
-/
def PolyProf.emptyDiagElemHom
    (b : P.B) (hpos : IsEmpty (P.arity_pos b)) (y : P.DiagElem)
    (hb : y.elem.1 = b) :
    P.DiagElemHom (P.emptyDiagElem b hpos) y where
  base := PEmpty.elim
  compat := by
    rw [P.diagCompat_eq_paranatural]
    simp only [DiagCompat, emptyDiagElem, covAction, contravAction]
    congr 1
    · exact hb.symm
    · subst hb
      apply heq_of_eq
      funext k p
      exact (hpos.false p).elim

/--
The morphism from empty carrier is unique.
-/
theorem PolyProf.emptyDiagElemHom_unique
    (b : P.B) (hpos : IsEmpty (P.arity_pos b)) (y : P.DiagElem)
    (hb : y.elem.1 = b)
    (f : P.DiagElemHom (P.emptyDiagElem b hpos) y) :
    f = P.emptyDiagElemHom b hpos y hb := by
  ext (x : (P.emptyDiagElem b hpos).base)
  exact PEmpty.elim x

end EmptyDiagElem

/-! ## Purely Covariant Polynomial Profunctors

A polynomial profunctor is purely covariant if all negative arities are empty.
In this case, it reduces to a polynomial functor, and diagonal elements
correspond to algebras.
-/

section PurelyCovariant

/--
A polynomial profunctor is purely covariant if all negative arities are empty.
-/
def PolyProf.IsPurelyCovariant (P : PolyProf.{u}) : Prop :=
  ∀ b : P.B, IsEmpty (P.arity_neg b)

/--
For a purely covariant polynomial profunctor, the evaluation simplifies to
a coproduct of representables.
-/
def PolyProf.purelyCovariantEvalEquiv (P : PolyProf.{u})
    (hP : P.IsPurelyCovariant) (V W : Type u) :
    P.eval V W ≃ Σ (b : P.B), (P.arity_pos b → W) where
  toFun := fun ⟨b, f⟩ => ⟨b, f (fun x => (hP b).elim x)⟩
  invFun := fun ⟨b, g⟩ => ⟨b, fun _ => g⟩
  left_inv := fun ⟨b, f⟩ => by
    simp only
    congr
    funext k
    congr
    funext x
    exact (hP b).elim x
  right_inv := fun ⟨b, g⟩ => rfl

/--
Convert a purely covariant polynomial profunctor to a polynomial functor.
This uses mathlib's `PFunctor` type.
-/
def PolyProf.toPFunctor (P : PolyProf.{u}) (_ : P.IsPurelyCovariant) :
    PFunctor.{u, u} where
  A := P.B
  B := fun b => P.arity_pos b

end PurelyCovariant

/-! ## Generalized Polynomial Profunctors

A generalized polynomial profunctor has a two-layer structure:
1. An outer Dirichlet layer with positions `A` and arities `S : A → Type`
2. An inner exponential layer with positions `B : A → Type` and arities
   `N, T : (a : A) → B a → Type`

The evaluation formula is:
```
P(V, W) = Σ (a : A), (V → S a) × Σ (b : B a), ((N a b → V) → (T a b → W))
```

This generalizes both:
- The original `PolyProf` (when `A = Unit` and `S = Unit`)
- Pure Dirichlet functors as profunctors (when `B a = Unit`, `N = Empty`)
-/

section GenPolyProf

/--
A generalized polynomial profunctor with both Dirichlet and exponential layers.

The evaluation formula combines:
- Dirichlet structure: `Σ_a (V → S a)` for contravariance via direct function types
- Exponential structure: `((N → V) → (T → W))` for contravariance via nesting
-/
structure GenPolyProf where
  /-- Dirichlet positions -/
  A : Type u
  /-- Dirichlet arities: for each position a, the type that V maps into -/
  S : A → Type u
  /-- Exponential positions: for each Dirichlet position, a type of inner positions -/
  B : A → Type u
  /-- Negative exponential arities -/
  N : (a : A) → B a → Type u
  /-- Positive exponential arities -/
  T : (a : A) → B a → Type u

namespace GenPolyProf

variable (P : GenPolyProf.{u})

/--
The inner exponential part of the evaluation at a fixed Dirichlet position.
-/
def innerEval (a : P.A) (V W : Type u) : Type u :=
  Σ (b : P.B a), ((P.N a b → V) → (P.T a b → W))

/--
Evaluate a generalized polynomial profunctor at types V and W.

`P.eval V W = Σ (a : A), (V → S a) × Σ (b : B a), ((N a b → V) → (T a b → W))`
-/
def eval (V W : Type u) : Type u :=
  Σ (a : P.A), (V → P.S a) × P.innerEval a V W

/--
The covariant action on the inner exponential part.
-/
def innerCovAction {a : P.A} {V W W' : Type u} (g : W → W') :
    P.innerEval a V W → P.innerEval a V W' :=
  fun ⟨b, h⟩ => ⟨b, fun k => g ∘ h k⟩

/--
The contravariant action on the inner exponential part.
-/
def innerContravAction {a : P.A} {V V' W : Type u} (f : V → V') :
    P.innerEval a V' W → P.innerEval a V W :=
  fun ⟨b, h⟩ => ⟨b, fun k => h (f ∘ k)⟩

/--
The covariant action of a generalized polynomial profunctor.
Given `g : W → W'`, maps `P.eval V W → P.eval V W'`.
-/
def covAction {V W W' : Type u} (g : W → W') :
    P.eval V W → P.eval V W' :=
  fun ⟨a, f, inner⟩ => ⟨a, f, P.innerCovAction g inner⟩

/--
The contravariant action of a generalized polynomial profunctor.
Given `f : V → V'`, maps `P.eval V' W → P.eval V W`.

This acts on both layers:
- Dirichlet layer: postcompose `f` with the function `V' → S a`
- Exponential layer: precompose with `f` in the `(N → V') → ...` part
-/
def contravAction {V V' W : Type u} (f : V → V') :
    P.eval V' W → P.eval V W :=
  fun ⟨a, s, inner⟩ => ⟨a, s ∘ f, P.innerContravAction f inner⟩

@[simp]
lemma covAction_id (V W : Type u) :
    P.covAction (id : W → W) = (id : P.eval V W → P.eval V W) := by
  funext ⟨a, f, b, h⟩
  simp only [covAction, innerCovAction, id_eq]
  rfl

@[simp]
lemma contravAction_id (V W : Type u) :
    P.contravAction (id : V → V) = (id : P.eval V W → P.eval V W) := by
  funext ⟨a, f, b, h⟩
  simp only [contravAction, innerContravAction, id_eq]
  rfl

@[simp]
lemma covAction_comp {V W W' W'' : Type u} (g : W → W') (g' : W' → W'') :
    P.covAction (g' ∘ g) = P.covAction g' ∘ P.covAction (V := V) g := by
  funext ⟨a, f, b, h⟩
  rfl

@[simp]
lemma contravAction_comp {V V' V'' W : Type u} (f : V → V') (f' : V' → V'') :
    P.contravAction (f' ∘ f) =
    P.contravAction f ∘ P.contravAction (W := W) f' := by
  funext ⟨a, s, b, h⟩
  simp only [contravAction, innerContravAction, Function.comp_apply,
    Function.comp_assoc]

/--
The interchange law: covariant and contravariant actions commute.
-/
@[simp]
lemma covAction_contravAction_comm {V V' W W' : Type u}
    (f : V → V') (g : W → W') (x : P.eval V' W) :
    P.covAction g (P.contravAction f x) =
    P.contravAction f (P.covAction g x) := by
  obtain ⟨a, s, b, h⟩ := x
  simp only [covAction, contravAction, innerCovAction, innerContravAction]

/--
The bifunctorial action of a generalized polynomial profunctor.
-/
def bimap {V V' W W' : Type u} (f : V' → V) (g : W → W') :
    P.eval V W → P.eval V' W' :=
  fun ⟨a, s, b, h⟩ => ⟨a, s ∘ f, b, fun k => g ∘ h (f ∘ k)⟩

end GenPolyProf

/-! ### Natural Transformations between GenPolyProf

A natural transformation between generalized polynomial profunctors is a
family of functions `η_{V,W} : P.eval V W → Q.eval V W` that is natural in
both arguments: contravariant in V and covariant in W.
-/

/--
A natural transformation between two generalized polynomial profunctors.

The naturality conditions are:
- `η ∘ P.contravAction f = Q.contravAction f ∘ η` (contravariant naturality)
- `η ∘ P.covAction g = Q.covAction g ∘ η` (covariant naturality)
-/
structure GenPolyProf.Hom (P Q : GenPolyProf.{u}) where
  /-- The component maps -/
  app : ∀ (V W : Type u), P.eval V W → Q.eval V W
  /-- Naturality in the contravariant argument -/
  naturality_contrav : ∀ {V V' W : Type u} (f : V → V') (x : P.eval V' W),
    app V W (P.contravAction f x) = Q.contravAction f (app V' W x)
  /-- Naturality in the covariant argument -/
  naturality_cov : ∀ {V W W' : Type u} (g : W → W') (x : P.eval V W),
    app V W' (P.covAction g x) = Q.covAction g (app V W x)

namespace GenPolyProf.Hom

variable {P Q R : GenPolyProf.{u}}

/--
The identity natural transformation.
-/
@[simps]
def id (P : GenPolyProf.{u}) : P.Hom P where
  app := fun _ _ => _root_.id
  naturality_contrav := fun _ _ => rfl
  naturality_cov := fun _ _ => rfl

/--
Composition of natural transformations.
-/
@[simps]
def comp (η : P.Hom Q) (θ : Q.Hom R) : P.Hom R where
  app := fun V W => θ.app V W ∘ η.app V W
  naturality_contrav := fun f x => by
    simp only [Function.comp_apply]
    rw [η.naturality_contrav, θ.naturality_contrav]
  naturality_cov := fun g x => by
    simp only [Function.comp_apply]
    rw [η.naturality_cov, θ.naturality_cov]

end GenPolyProf.Hom

/--
The category of generalized polynomial profunctors.
-/
instance : Category GenPolyProf.{u} where
  Hom := GenPolyProf.Hom
  id := GenPolyProf.Hom.id
  comp := fun f g => GenPolyProf.Hom.comp f g
  id_comp := fun f => by
    cases f
    simp only [GenPolyProf.Hom.id, GenPolyProf.Hom.comp]
    rfl
  comp_id := fun f => by
    cases f
    simp only [GenPolyProf.Hom.id, GenPolyProf.Hom.comp]
    rfl
  assoc := fun f g h => by
    cases f; cases g; cases h
    simp only [GenPolyProf.Hom.comp]
    rfl

/-! ### Embedding PolyProf into GenPolyProf

The original `PolyProf` embeds into `GenPolyProf` by setting:
- `A = Unit` (single Dirichlet position)
- `S () = PUnit` (trivial Dirichlet arity)
- `B () = P.B` (positions become exponential positions)
- `N () = P.arity_neg` (negative arities)
- `T () = P.arity_pos` (positive arities)
-/

/--
Embed a polynomial profunctor into the generalized form.
-/
def PolyProf.toGen (P : PolyProf.{u}) : GenPolyProf.{u} where
  A := PUnit.{u+1}
  S := fun _ => PUnit.{u+1}
  B := fun _ => P.B
  N := fun _ => P.arity_neg
  T := fun _ => P.arity_pos

/--
The evaluation of a generalized polynomial profunctor arising from `PolyProf`
is equivalent to the original evaluation.
-/
def PolyProf.toGenEvalEquiv (P : PolyProf.{u}) (V W : Type u) :
    P.toGen.eval V W ≃ P.eval V W where
  toFun := fun ⟨_, _, b, h⟩ => ⟨b, h⟩
  invFun := fun ⟨b, h⟩ => ⟨PUnit.unit, fun _ => PUnit.unit, b, h⟩
  left_inv := fun ⟨a, f, b, h⟩ => by simp only; congr
  right_inv := fun ⟨b, h⟩ => rfl

/-! ### Dirichlet Profunctors

A Dirichlet functor `D(V) = Σ_a (V → S a)` can be viewed as a profunctor
`P(V, W) = D(V) × W = Σ_a (V → S a) × W`.

This embeds into `GenPolyProf` by setting:
- `A` = the Dirichlet positions
- `S` = the Dirichlet arities
- `B a = Unit` (single exponential position per Dirichlet position)
- `N a () = Empty` (no negative exponential arity)
- `T a () = Unit` (trivial positive exponential arity, giving `Unit → W ≃ W`)
-/

/--
A Dirichlet functor on Type.

`D(V) = Σ (a : A), (V → S a)`

This is the free coproduct completion by contravariant representables.
-/
structure DirichletFunctor where
  /-- Positions -/
  A : Type u
  /-- Arities at each position -/
  S : A → Type u

namespace DirichletFunctor

variable (D : DirichletFunctor.{u})

/--
Evaluate a Dirichlet functor at a type V.
-/
def eval (V : Type u) : Type u :=
  Σ (a : D.A), (V → D.S a)

/--
The contravariant action of a Dirichlet functor.
-/
def contravAction {V V' : Type u} (f : V → V') :
    D.eval V' → D.eval V :=
  fun ⟨a, g⟩ => ⟨a, g ∘ f⟩

/--
View a Dirichlet functor as a profunctor `P(V, W) = D(V) × W`.
-/
def toGenPolyProf : GenPolyProf.{u} where
  A := D.A
  S := D.S
  B := fun _ => PUnit.{u+1}
  N := fun _ _ => PEmpty.{u+1}
  T := fun _ _ => PUnit.{u+1}

/--
The evaluation of the Dirichlet profunctor is `D(V) × W`.
-/
def toGenEvalEquiv (V W : Type u) :
    D.toGenPolyProf.eval V W ≃ D.eval V × W where
  toFun := fun ⟨a, f, _, h⟩ => (⟨a, f⟩, h (fun e => PEmpty.elim e) PUnit.unit)
  invFun := fun (⟨a, f⟩, w) => ⟨a, f, PUnit.unit, fun _ _ => w⟩
  left_inv := fun ⟨a, f, _, h⟩ => by
    simp only
    congr
    funext k p
    cases p
    congr
    funext e
    exact PEmpty.elim e
  right_inv := fun (⟨a, f⟩, w) => rfl

end DirichletFunctor

end GenPolyProf

end GebLean
