/-
Dependent Polynomial Functors

This module defines dependent polynomial functors, which consist of:
1. An outer polynomial functor J : Type → Type
2. A coproduct of representables on the category of elements of J × id

This structure captures a notion of "polynomial copresheaf" on the category
of elements of a polynomial functor.

## Structure

The category of elements ∫(J × id) for a polynomial J = (I, D) has:
- Objects: (T, j, d, t) where T : Type, j : I, d : D(j) → T, t : T
- Morphisms: (T, j, d, t) → (T', j', d', t') are functions f : T → T'
  such that j = j', d' = f ∘ d, and t' = f(t)

A coproduct of representables on ∫(J × id) is given by an index type K and
a K-indexed family of objects of ∫(J × id). The evaluation at an object
(Y, j, d, y) gives the type of morphisms from representing objects to
(Y, j, d, y).
-/

import GebLean.Polynomial
import GebLean.Utilities.TwistedArrow

namespace GebLean

open CategoryTheory

/-! ## Polynomial × Id

For a polynomial functor `J` with positions `I` and directions `D : I → Type`,
the product `J × id` has the same positions but with one additional direction
at each position. This corresponds to the functor `Y ↦ J(Y) × Y`.

Concretely, if `J(Y) = Σ i : I, (D i → Y)`, then
`(J × id)(Y) = (Σ i : I, (D i → Y)) × Y ≅ Σ i : I, ((D i ⊕ Unit) → Y)`.

The extra `Unit` direction at each position corresponds to the `id` factor.
-/

/-- The `× id` operation on polynomial functors.

Given a polynomial with positions `I` and directions `D : I → C`, produces
a polynomial with the same positions and directions `fun i => D i ⊕ Unit`.
This corresponds to the product of the polynomial functor with the identity. -/
def ccrProdId {C : Type*} [Category C] (P : CoprodCovarRepCat' C) :
    CoprodCovarRepCat' (C × Type) :=
  ccrObjMk (fun i => (ccrFamily P i, Unit))

/-- The `× id` operation on polynomials over `Type`.

This is the special case where the base category is `Type`, producing a new
polynomial over `Type` with directions extended by `Unit`. -/
def ccrProdIdType (P : CoprodCovarRepCat' Type) : CoprodCovarRepCat' Type :=
  ccrObjMk (fun i => ccrFamily P i ⊕ Unit)

/-- A dependent polynomial functor.

The structure consists of:
- An outer polynomial J, represented as an object of `CoprodCovarRepCat' Type`
- A coproduct of representables on ∫(J × id), specified by:
  - An index type `innerIdx`
  - For each index i, a representing object of ∫(J × id):
    - `reprType i` : the base type T
    - `reprPos i` : a position j in the outer polynomial
    - `reprDir i` : a map d : outerDir j → T
    - `reprElem i` : an element t : T (from the "id" factor)
-/
structure DepPolyFunctor where
  /-- The outer polynomial J as a coproduct of covariant representables -/
  outerPoly : CoprodCovarRepCat' Type
  /-- Index type for the inner coproduct of representables -/
  innerIdx : Type
  /-- Base type for each representing object -/
  reprType : innerIdx → Type
  /-- Position in J for each representing object -/
  reprPos : innerIdx → ccrIndex outerPoly
  /-- Direction map for each representing object -/
  reprDir : (i : innerIdx) → ccrFamily outerPoly (reprPos i) → reprType i
  /-- Distinguished element for each representing object (from id factor) -/
  reprElem : (i : innerIdx) → reprType i

namespace DepPolyFunctor

variable (P : DepPolyFunctor)

/-- Positions of the outer polynomial J (derived from `outerPoly`). -/
def outerPos : Type := ccrIndex P.outerPoly

/-- Directions of the outer polynomial J (derived from `outerPoly`). -/
def outerDir (j : P.outerPos) : Type := ccrFamily P.outerPoly j

/-- The outer polynomial × id.

This is the polynomial with the same positions as `outerPoly` but with
directions extended by `Unit` at each position. The directions at position
`j` become `outerDir j ⊕ Unit`. -/
def outerPolyProdId : CoprodCovarRepCat' Type := ccrProdIdType P.outerPoly

/-- Positions of outerPolyProdId (same as outerPos). -/
def outerPolyProdIdPos : Type := ccrIndex P.outerPolyProdId

/-- Directions of outerPolyProdId at position j. -/
def outerPolyProdIdDir (j : P.outerPolyProdIdPos) : Type :=
  ccrFamily P.outerPolyProdId j

/-- The positions of outerPolyProdId are definitionally equal to outerPos. -/
lemma outerPolyProdIdPos_eq : P.outerPolyProdIdPos = P.outerPos := rfl

/-- The directions of outerPolyProdId are the sum of outerDir with Unit. -/
lemma outerPolyProdIdDir_eq (j : P.outerPolyProdIdPos) :
    P.outerPolyProdIdDir j = (P.outerDir j ⊕ Unit) := rfl

/-! ## Objects of the Category of Elements

An object of ∫(J × id) is a 4-tuple (T, j, d, t), which corresponds to an
object of the category of elements of `outerPolyProdId`.

The direction type `outerDir j ⊕ Unit` packages both the direction map
`d : outerDir j → T` (via `Sum.inl`) and the element `t : T` (via `Sum.inr ()`).
-/

/-- An object of the category of elements of J × id.

This is an alias for `ccrElementsObj outerPolyProdId`, which consists of:
- A type T (the base)
- A position j in the outer polynomial
- A function `(outerDir j ⊕ Unit) → T` packaging both the direction map and element
-/
abbrev ElemCatObj : Type _ := ccrElementsObj P.outerPolyProdId

/-- The base type of an element category object. -/
def ElemCatObj.baseType (X : P.ElemCatObj) : Type := X.fst

/-- The position of an element category object. -/
def ElemCatObj.pos (X : P.ElemCatObj) : P.outerPos := X.snd.fst

/-- The combined direction-and-element map. -/
def ElemCatObj.dirElemMap (X : P.ElemCatObj) :
    P.outerDir X.pos ⊕ Unit → X.baseType :=
  X.snd.snd

/-- The direction map of an element category object. -/
def ElemCatObj.dirMap (X : P.ElemCatObj) : P.outerDir X.pos → X.baseType :=
  ElemCatObj.dirElemMap P X ∘ Sum.inl

/-- The distinguished element of an element category object. -/
def ElemCatObj.elem (X : P.ElemCatObj) : X.baseType :=
  X.snd.snd (Sum.inr ())

/-- Construct an element category object from its components. -/
def ElemCatObj.mk (T : Type) (j : P.outerPos) (d : P.outerDir j → T) (t : T) :
    P.ElemCatObj :=
  ⟨T, j, Sum.elim d (fun _ => t)⟩

@[simp]
lemma ElemCatObj.mk_baseType (T : Type) (j : P.outerPos) (d : P.outerDir j → T)
    (t : T) : (ElemCatObj.mk P T j d t).baseType = T := rfl

@[simp]
lemma ElemCatObj.mk_pos (T : Type) (j : P.outerPos) (d : P.outerDir j → T)
    (t : T) : (ElemCatObj.mk P T j d t).pos = j := rfl

@[simp]
lemma ElemCatObj.mk_dirMap (T : Type) (j : P.outerPos) (d : P.outerDir j → T)
    (t : T) : (ElemCatObj.mk P T j d t).dirMap = d := rfl

@[simp]
lemma ElemCatObj.mk_elem (T : Type) (j : P.outerPos) (d : P.outerDir j → T)
    (t : T) : (ElemCatObj.mk P T j d t).elem = t := rfl

/-- The representing object at index i, as an object of ∫(J × id). -/
def reprObj (i : P.innerIdx) : P.ElemCatObj :=
  ElemCatObj.mk P (P.reprType i) (P.reprPos i) (P.reprDir i) (P.reprElem i)

/-! ## Morphisms in the Category of Elements

A morphism (T, j, d, t) → (T', j', d', t') in ∫(J × id) is a morphism in the
category of elements of `outerPolyProdId`, which is a function f : T → T'
such that j = j', d' = f ∘ d, and t' = f(t).

Since j = j' is required, morphisms only exist between objects at the
same position.
-/

/-- A morphism in the category of elements of J × id.

This is an alias for morphisms in `ccrElements outerPolyProdId`. -/
abbrev ElemCatMor (X Y : P.ElemCatObj) : Type _ := ccrElementsMor X Y

/-- The underlying function of a morphism in ∫(J × id). -/
def ElemCatMor.func {X Y : P.ElemCatObj} (m : P.ElemCatMor X Y) :
    X.baseType → Y.baseType :=
  m.val

/-- Positions are equal for a morphism in ∫(J × id). -/
def ElemCatMor.posEq {X Y : P.ElemCatObj} (m : P.ElemCatMor X Y) :
    ElemCatObj.pos P X = ElemCatObj.pos P Y :=
  congrArg Sigma.fst m.property

/-- Direction maps are compatible for a morphism in ∫(J × id). -/
def ElemCatMor.dirCompat {X Y : P.ElemCatObj} (m : P.ElemCatMor X Y)
    (x : P.outerDir (ElemCatObj.pos P X)) :
    ElemCatObj.dirMap P Y (ElemCatMor.posEq P m ▸ x) =
      m.val (ElemCatObj.dirMap P X x) := by
  obtain ⟨Yt, Ysnd⟩ := Y
  obtain ⟨Yfst, Ysnd⟩ := Ysnd
  have h : (⟨Yfst, Ysnd⟩ : Σ j, P.outerDir j ⊕ Unit → Yt) =
           ⟨X.snd.fst, m.val ∘ X.snd.snd⟩ := m.property.symm
  simp only [Sigma.mk.injEq] at h
  obtain ⟨hfst, hsnd⟩ := h
  subst hfst
  simp only [heq_eq_eq] at hsnd
  simp only [ElemCatObj.dirMap, ElemCatObj.dirElemMap, ElemCatObj.pos,
    Function.comp_apply, hsnd]

/-- Elements are compatible for a morphism in ∫(J × id). -/
def ElemCatMor.elemCompat {X Y : P.ElemCatObj} (m : P.ElemCatMor X Y) :
    ElemCatObj.elem P Y = m.val (ElemCatObj.elem P X) := by
  obtain ⟨Yt, Ysnd⟩ := Y
  obtain ⟨Yfst, Ysnd⟩ := Ysnd
  obtain ⟨Xt, Xsnd⟩ := X
  obtain ⟨Xfst, Xsnd⟩ := Xsnd
  have h := m.property
  simp only [ElemCatObj.elem]
  simp only [ccrToFunctor, ccrEvalMap, CategoryTheory.types_comp] at h
  rw [Sigma.mk.injEq] at h
  obtain ⟨hfst, hsnd⟩ := h
  subst hfst
  simp only [heq_eq_eq] at hsnd
  exact (congrFun hsnd (Sum.inr ())).symm

/-! ## Evaluation

The evaluation of the coproduct of representables at an object (Y, j, d, y)
of ∫(J × id) is:

  Σ i : innerIdx, Hom_{∫(J×id)}(reprObj i, (Y, j, d, y))

A morphism from a representing object to (Y, j, d, y) consists of:
- The positions must match: reprPos i = j
- A function f : reprType i → Y
- Direction compatibility: d = f ∘ reprDir i (up to transport)
- Element compatibility: y = f (reprElem i)
-/

/-- An element of the evaluation at an object of ∫(J × id).

This is a morphism from some representing object to the target object. -/
structure Eval (target : P.ElemCatObj) where
  /-- Which representing object -/
  idx : P.innerIdx
  /-- The underlying function -/
  func : P.reprType idx → ElemCatObj.baseType P target
  /-- Positions match -/
  posEq : P.reprPos idx = ElemCatObj.pos P target
  /-- Direction maps are compatible -/
  dirCompat : ∀ x : P.outerDir (P.reprPos idx),
    ElemCatObj.dirMap P target (posEq ▸ x) = func (P.reprDir idx x)
  /-- Elements are compatible -/
  elemCompat : ElemCatObj.elem P target = func (P.reprElem idx)

/-! ## Evaluation at a Type

For a simpler interface, we can evaluate at a type Y with a position j,
direction map d, and element y directly.
-/

/-- Evaluation at explicit data (Y, j, d, y) without bundling into ElemCatObj. -/
structure EvalAt (Y : Type) (j : P.outerPos) (d : P.outerDir j → Y) (y : Y) where
  /-- Which representing object -/
  idx : P.innerIdx
  /-- The underlying function -/
  func : P.reprType idx → Y
  /-- Positions match -/
  posEq : P.reprPos idx = j
  /-- Direction maps are compatible -/
  dirCompat : ∀ x : P.outerDir (P.reprPos idx), d (posEq ▸ x) = func (P.reprDir idx x)
  /-- Elements are compatible -/
  elemCompat : y = func (P.reprElem idx)

/-! ## Functoriality

Given a morphism in ∫(J × id) from X to Y, we get a map Eval X → Eval Y
by composition.
-/

/-- Functorial action: morphisms in ∫(J × id) induce maps on evaluations. -/
def evalMap {X Y : P.ElemCatObj} (m : P.ElemCatMor X Y) (e : P.Eval X) :
    P.Eval Y where
  idx := e.idx
  func := m.func ∘ e.func
  posEq := e.posEq.trans m.posEq
  dirCompat := fun x => by
    simp only [Function.comp_apply, ElemCatMor.func]
    have transport_trans : ∀ {A : Type} {B : A → Type} {a b c : A}
        (p : a = b) (q : b = c) (x : B a),
        (p.trans q) ▸ x = q ▸ (p ▸ x) := by
      intro A B a b c p q x
      subst q
      subst p
      rfl
    rw [transport_trans e.posEq (ElemCatMor.posEq P m) x]
    rw [ElemCatMor.dirCompat]
    rw [e.dirCompat]
  elemCompat := by
    simp only [Function.comp_apply]
    rw [← e.elemCompat]
    exact m.elemCompat

end DepPolyFunctor

/-! ## Twisted Arrow Evaluation (Structured)

The evaluation of a `DepPolyFunctor` on twisted arrows proceeds in two stages:

1. **Outer evaluation**: Compute an index `(pos, dir, elem)` in `(J × id)(Y)`.
   This depends only on `Y` (covariant).

2. **Inner Dirichlet evaluation**: For each outer index, evaluate a Dirichlet
   functor (coproduct of representables) at the slice object `(X, p) ∈ Over Y`.
   This depends on `X` and `p` (contravariant in X).

The total evaluation is: `Σ idx : OuterIdx(Y), InnerEval(idx, X, p)`

This separation clarifies the roles:
- The outer polynomial generates INDICES (one per element of `(J × id)(Y)`)
- Each index determines a Dirichlet functor on the slice category
- For polynomial functors, the Dirichlet functor is trivial (terminal)
- For Dirichlet functors, the outer polynomial is trivial
-/

/-- An index for the inner Dirichlet functor, computed from Y alone.

This is an element of `(J × id)(Y)`, the evaluation of the outer polynomial
(with id factor) at Y. Each such index determines which Dirichlet functor
to evaluate at the slice object `(X, p)`. -/
structure DepPolyFunctor.OuterIdx (P : DepPolyFunctor) (Y : Type) where
  /-- Position in outer polynomial -/
  pos : P.outerPos
  /-- Direction map to Y -/
  dir : P.outerDir pos → Y
  /-- Element of Y (from id factor) -/
  elem : Y

/-! ### Inner Dirichlet Functor (Coproduct of Contravariant Representables)

For each outer index `idx : OuterIdx Y`, we construct a Dirichlet functor
(coproduct of contravariant representables / presheaf) on `Over Y`. The
evaluation is contravariant in the slice object, matching the twisted arrow
structure where `X` varies contravariantly.

The positions of this Dirichlet functor are pairs `(i, toY)` where:
- `i : innerIdx` with `reprPos i = idx.pos`
- `toY : reprType i → Y` satisfying `dirCompat` and `elemCompat`

The representing object at position `(i, toY)` is `Over.mk toY : Over Y`.
The evaluation at slice object `(X, p)` is `Hom_{Over Y}((X, p), (T, toY))`.
-/

/-- A position in the inner Dirichlet functor at outer index `idx`.

This packages an inner index `i` together with a compatible projection `toY`. -/
structure DepPolyFunctor.DirichletPos (P : DepPolyFunctor) {Y : Type}
    (idx : P.OuterIdx Y) where
  /-- Which inner representable -/
  reprIdx : P.innerIdx
  /-- Position matches the outer index -/
  posMatch : P.reprPos reprIdx = idx.pos
  /-- Projection to Y -/
  toY : P.reprType reprIdx → Y
  /-- Direction compatibility: outer dir factors through inner repr -/
  dirCompat : ∀ x : P.outerDir (P.reprPos reprIdx),
    idx.dir (posMatch ▸ x) = toY (P.reprDir reprIdx x)
  /-- Element compatibility: elem equals toY applied to reprElem -/
  elemCompat : idx.elem = toY (P.reprElem reprIdx)

/-- The representing object in `Over Y` at a Dirichlet position.

For position `(i, toY)`, the representing object is `(reprType i, toY)`. -/
def DepPolyFunctor.dirichletRepr (P : DepPolyFunctor) {Y : Type}
    {idx : P.OuterIdx Y} (pos : P.DirichletPos idx) : Over Y :=
  Over.mk pos.toY

/-- Evaluation of the inner Dirichlet functor at a slice object.

This is the type of morphisms in `Over Y` from `(X, p)` to a representing
object, summed over all Dirichlet positions. This is contravariant in `X`,
matching the twisted arrow structure. -/
def DepPolyFunctor.evalDirichlet (P : DepPolyFunctor) {Y : Type}
    (idx : P.OuterIdx Y) (A : Over Y) : Type _ :=
  Σ pos : P.DirichletPos idx, (A ⟶ P.dirichletRepr pos)

/-- The inner Dirichlet functor as an object of
`FreeCoprodCompletionCat (Over Y)`.

Given an outer index, this packages the
`(DirichletPos, dirichletRepr)` pair as a coproduct
of contravariant representables, which can then be
evaluated using `fcEval`. -/
def DepPolyFunctor.innerDirichlet
    (P : DepPolyFunctor) {Y : Type}
    (idx : P.OuterIdx Y) :
    FreeCoprodCompletionCat (Over Y) :=
  fcObjMk (fun pos : P.DirichletPos idx =>
    P.dirichletRepr pos)

/-- `evalDirichlet` is definitionally equal to
`fcEval` of the inner Dirichlet functor. -/
lemma DepPolyFunctor.evalDirichlet_eq_fcEval
    (P : DepPolyFunctor)
    {Y : Type} (idx : P.OuterIdx Y)
    (A : Over Y) :
    P.evalDirichlet idx A =
      fcEval (P.innerDirichlet idx) A :=
  rfl

/-- Evaluation of the inner Dirichlet functor at an outer index.

For a fixed outer index `(pos, dir, elem)`, this evaluates the coproduct of
representables (restricted to that position) at the slice object `(X, p)`.

This is a morphism in `Over Y` from `(X, p)` to some representing object
`(reprType i, toY)` that is compatible with the outer index.

This structure is isomorphic to `polyEval Y (evalDirichlet P idx) (Over.mk p)`:
- `DirichletPos` packages `(reprIdx, posMatch, toY, dirCompat, elemCompat)`
- The slice morphism `(fromX, triangle)` is an `Over.Hom` to the representing object -/
structure DepPolyFunctor.InnerEval (P : DepPolyFunctor) {Y : Type}
    (idx : P.OuterIdx Y) (X : Type) (p : X → Y) where
  /-- Which inner representable -/
  reprIdx : P.innerIdx
  /-- Position matches the outer index -/
  posMatch : P.reprPos reprIdx = idx.pos
  /-- Realization of representing type in Y -/
  toY : P.reprType reprIdx → Y
  /-- Direction compatibility -/
  dirCompat : ∀ x : P.outerDir (P.reprPos reprIdx),
    idx.dir (posMatch ▸ x) = toY (P.reprDir reprIdx x)
  /-- Element compatibility -/
  elemCompat : idx.elem = toY (P.reprElem reprIdx)
  /-- Slice morphism from (X, p) to (reprType, toY) -/
  fromX : X → P.reprType reprIdx
  /-- Triangle commutes in Over Y -/
  triangle : p = toY ∘ fromX

/-- Extract the Dirichlet position from an inner evaluation. -/
def DepPolyFunctor.InnerEval.toDirichletPos {P : DepPolyFunctor} {Y : Type}
    {idx : P.OuterIdx Y} {X : Type} {p : X → Y}
    (e : P.InnerEval idx X p) : P.DirichletPos idx where
  reprIdx := e.reprIdx
  posMatch := e.posMatch
  toY := e.toY
  dirCompat := e.dirCompat
  elemCompat := e.elemCompat

/-- Extract the Over morphism from an inner evaluation.

The morphism goes from `(X, p)` to the representing object `(reprType, toY)`,
matching the contravariant structure of a Dirichlet functor (presheaf). -/
def DepPolyFunctor.InnerEval.toOverHom {P : DepPolyFunctor} {Y : Type}
    {idx : P.OuterIdx Y} {X : Type} {p : X → Y}
    (e : P.InnerEval idx X p) :
    Over.mk p ⟶ P.dirichletRepr e.toDirichletPos :=
  Over.homMk e.fromX e.triangle.symm

/-- Evaluation via `evalDirichlet`.

This is definitionally equal to `P.evalDirichlet idx (Over.mk p)`,
which is `Σ pos : DirichletPos idx, Over.Hom (Over.mk p) (dirichletRepr pos)`. -/
def DepPolyFunctor.innerEvalViaDirichlet (P : DepPolyFunctor) {Y : Type}
    (idx : P.OuterIdx Y) (X : Type) (p : X → Y) : Type _ :=
  P.evalDirichlet idx (Over.mk p)

/-- Convert an inner evaluation to the Dirichlet form. -/
def DepPolyFunctor.InnerEval.toDirichletEval {P : DepPolyFunctor} {Y : Type}
    {idx : P.OuterIdx Y} {X : Type} {p : X → Y}
    (e : P.InnerEval idx X p) : P.innerEvalViaDirichlet idx X p :=
  ⟨e.toDirichletPos, e.toOverHom⟩

/-- Convert from Dirichlet evaluation form to inner evaluation. -/
def DepPolyFunctor.InnerEval.fromDirichletEval {P : DepPolyFunctor} {Y : Type}
    {idx : P.OuterIdx Y} {X : Type} {p : X → Y}
    (e : P.innerEvalViaDirichlet idx X p) : P.InnerEval idx X p where
  reprIdx := e.1.reprIdx
  posMatch := e.1.posMatch
  toY := e.1.toY
  dirCompat := e.1.dirCompat
  elemCompat := e.1.elemCompat
  fromX := e.2.left
  triangle := (Over.w e.2).symm

/-- Inner evaluation is equivalent to evaluation of the Dirichlet functor. -/
def DepPolyFunctor.innerEvalEquivDirichlet (P : DepPolyFunctor) {Y : Type}
    (idx : P.OuterIdx Y) (X : Type) (p : X → Y) :
    P.InnerEval idx X p ≃ P.innerEvalViaDirichlet idx X p where
  toFun := InnerEval.toDirichletEval
  invFun := InnerEval.fromDirichletEval
  left_inv := fun e => by
    simp only [InnerEval.toDirichletEval, InnerEval.fromDirichletEval,
      InnerEval.toDirichletPos, InnerEval.toOverHom]
    rfl
  right_inv := fun ⟨pos, mor⟩ => rfl

/-- Total twisted arrow evaluation as outer index + inner Dirichlet.

The evaluation is structured as:
- The outer index is computed from Y alone (covariant)
- The inner evaluation depends on X, p, and the choice of outer index -/
def DepPolyFunctor.TwEval (P : DepPolyFunctor) (Y X : Type) (p : X → Y) : Type :=
  Σ idx : P.OuterIdx Y, P.InnerEval idx X p

namespace DepPolyFunctor

variable (P : DepPolyFunctor)

/-! ### Functoriality on Twisted Arrow Category

Given a twisted arrow morphism `(Y, X, p) → (Y', X', p')` consisting of
`h : Y → Y'` and `g : X' → X` with `h ∘ p ∘ g = p'`, we get an induced map
on evaluations.
-/

/-- Functorial action on outer indices (covariant in Y). -/
def outerIdxMap {Y Y' : Type} (h : Y → Y') (idx : P.OuterIdx Y) : P.OuterIdx Y' where
  pos := idx.pos
  dir := h ∘ idx.dir
  elem := h idx.elem

/-- Functorial action on inner evaluations. -/
def innerEvalMap {Y Y' X X' : Type} {p : X → Y} {p' : X' → Y'}
    {idx : P.OuterIdx Y}
    (h : Y → Y') (g : X' → X)
    (coherence : p' = h ∘ p ∘ g)
    (e : P.InnerEval idx X p) : P.InnerEval (P.outerIdxMap h idx) X' p' where
  reprIdx := e.reprIdx
  posMatch := e.posMatch
  toY := h ∘ e.toY
  dirCompat := fun x => by
    simp only [Function.comp_apply, outerIdxMap]
    rw [e.dirCompat x]
  elemCompat := by
    simp only [Function.comp_apply, outerIdxMap]
    rw [e.elemCompat]
  fromX := e.fromX ∘ g
  triangle := by
    rw [coherence]
    ext x'
    simp only [Function.comp_apply]
    congr 1
    rw [← Function.comp_apply (f := e.toY), ← e.triangle]

/-- Functorial action of a twisted arrow morphism on evaluations.

Given:
- `h : Y → Y'` (covariant)
- `g : X' → X` (contravariant)
- `coherence : h ∘ p ∘ g = p'`

We transform an evaluation at `(Y, X, p)` to one at `(Y', X', p')`.
-/
def twEvalMap {Y Y' X X' : Type} {p : X → Y} {p' : X' → Y'}
    (h : Y → Y') (g : X' → X)
    (coherence : p' = h ∘ p ∘ g)
    (e : P.TwEval Y X p) : P.TwEval Y' X' p' :=
  ⟨P.outerIdxMap h e.1, P.innerEvalMap h g coherence e.2⟩

/-! ### Functor Laws

We verify that `twEvalMap` satisfies the functor laws:
1. Identity: mapping by `(id, id)` is the identity
2. Composition: mapping by `(h' ∘ h, g ∘ g')` equals composing the individual maps
-/

/-- Identity law for outer index map. -/
theorem outerIdxMap_id {Y : Type} (idx : P.OuterIdx Y) :
    P.outerIdxMap id idx = idx := by
  simp only [outerIdxMap, Function.id_comp]
  rfl

/-- Composition law for outer index map. -/
theorem outerIdxMap_comp {Y Y' Y'' : Type} (h : Y → Y') (h' : Y' → Y'')
    (idx : P.OuterIdx Y) :
    P.outerIdxMap h' (P.outerIdxMap h idx) = P.outerIdxMap (h' ∘ h) idx := by
  simp only [outerIdxMap, Function.comp_assoc]
  rfl

/-- Identity law: mapping by identity morphisms gives identity. -/
theorem twEvalMap_id {Y X : Type} {p : X → Y} (e : P.TwEval Y X p) :
    P.twEvalMap id id rfl e = e := by
  simp only [twEvalMap, outerIdxMap, innerEvalMap, Function.comp_id, Function.id_comp]
  rfl

/-- Composition law for twisted arrow morphisms.

Given morphisms `(h, g)` and `(h', g')`, composing the maps equals mapping by
the composite `(h' ∘ h, g ∘ g')`.
-/
theorem twEvalMap_comp {Y Y' Y'' X X' X'' : Type}
    {p : X → Y} {p' : X' → Y'} {p'' : X'' → Y''}
    (h : Y → Y') (g : X' → X)
    (h' : Y' → Y'') (g' : X'' → X')
    (coh : p' = h ∘ p ∘ g)
    (coh' : p'' = h' ∘ p' ∘ g')
    (e : P.TwEval Y X p) :
    P.twEvalMap h' g' coh' (P.twEvalMap h g coh e) =
    P.twEvalMap (h' ∘ h) (g ∘ g') (by rw [coh', coh]; ext; simp [Function.comp]) e := by
  simp only [twEvalMap, outerIdxMap, innerEvalMap, Function.comp_assoc]
  rfl

/-! ### Functor Instance

We assemble `TwEval` and `twEvalMap` into a proper `CategoryTheory.Functor`
from the twisted arrow category to `Type`.
-/

/-- The evaluation functor from the twisted arrow category to Type.

For a dependent polynomial functor P, this sends each twisted arrow
`(X, Y, p : X → Y)` to the type `P.TwEval Y X p`.

We use the twisted arrow category `TwistedArrow' Type` from TwistedArrow.lean,
where objects are triples `(dom, cod, arr : dom → cod)` and morphisms have:
- `twDomArr'` going backwards (contravariant in domain)
- `twCodArr'` going forwards (covariant in codomain)
-/
def twEvalFunctor : TwistedArrow' Type ⥤ Type where
  obj A := P.TwEval (twCod' A) (twDom' A) (twArr' A)
  map {A B} f := P.twEvalMap (twCodArr' f) (twDomArr' f) (twHomComm' f).symm
  map_id A := by
    ext e
    simp only [types_id_apply]
    exact P.twEvalMap_id e
  map_comp {A B C} f g := by
    ext e
    simp only [types_comp_apply]
    rw [P.twEvalMap_comp (twCodArr' f) (twDomArr' f) (twCodArr' g) (twDomArr' g)
      (twHomComm' f).symm (twHomComm' g).symm e]
    rfl

/-! ## Embedding Polynomial Functors

A polynomial functor `P = (I, D)` where `I` is positions and `D : I → Type` gives
directions can be embedded into `DepPolyFunctor`.

The embedding uses:
- Outer polynomial: positions `I`, directions `D`
- Inner representables indexed by `Σ i : I, D i` (position-direction pairs)
- Each inner representable `⟨i, d⟩` has representing type `D i` with element `d`
- The inner direction map `reprDir ⟨i, d⟩ = id : D i → D i`

This approach handles empty direction types naturally: if `D i = Empty` for some
position `i`, there are simply no inner indices with first component `i`.

With this embedding, the inner evaluation is uniquely determined:
- `toY` equals the outer direction map `idx.dir`
- `elemCompat` constrains which inner indices match: only `⟨i, d⟩` where
  `idx.elem = idx.dir d`
- The valid outer indices are those where `elem` is in the image of `dir`
-/

/-- Embed a polynomial functor `(I, D)` into `DepPolyFunctor`.

The outer polynomial is `(I, D)` itself. Inner indices are pairs `⟨i, d⟩` where
`i : I` is a position and `d : D i` is a direction element. This naturally
handles empty `D i` - such positions have no corresponding inner indices.

The inner evaluation is essentially trivial: `toY = idx.dir` and the only
remaining data is the slice factorization `fromX`. -/
def polyToDepPoly {I : Type} (D : I → Type) : DepPolyFunctor where
  outerPoly := ccrObjMk D
  innerIdx := Σ i : I, D i
  reprType := fun ⟨i, _⟩ => D i
  reprPos := fun ⟨i, _⟩ => i
  reprDir := fun _ => id
  reprElem := fun ⟨_, d⟩ => d

namespace polyToDepPoly

variable {I : Type} {D : I → Type}

/-- The constraint that makes an outer index compatible with an inner index. -/
def compatibleIdx {Y : Type} (idx : (polyToDepPoly D).OuterIdx Y)
    (inner : Σ i : I, D i) : Prop :=
  match inner with
  | ⟨i, d⟩ => ∃ h : i = idx.pos, idx.elem = idx.dir (h ▸ d)

/-- An outer index is valid if `elem` is in the image of `dir`. -/
def validIdx {Y : Type} (idx : (polyToDepPoly D).OuterIdx Y) : Prop :=
  ∃ d : D idx.pos, idx.elem = idx.dir d

/-- Construct an inner evaluation from a direction element and factorization.

Given `d : D idx.pos` with `idx.elem = idx.dir d`, and a factorization
`fromX : X → D idx.pos` with `p = idx.dir ∘ fromX`, we construct the inner
evaluation using inner index `⟨idx.pos, d⟩`. -/
def mkInnerEval {Y X : Type} {p : X → Y}
    (idx : (polyToDepPoly D).OuterIdx Y)
    (d : D idx.pos) (elemEq : idx.elem = idx.dir d)
    (fromX : X → D idx.pos) (factor : p = idx.dir ∘ fromX) :
    (polyToDepPoly D).InnerEval idx X p where
  reprIdx := ⟨idx.pos, d⟩
  posMatch := rfl
  toY := idx.dir
  dirCompat := fun _ => rfl
  elemCompat := elemEq
  fromX := fromX
  triangle := factor

/-- Transport of a dependent function along an equality. -/
theorem transport_dep_fun {A : Type} {P : A → Type} (f : ∀ i, P i)
    {a b : A} (h : a = b) : h ▸ f a = f b := by
  cases h
  rfl

/-- The `toY` map in any inner evaluation equals `idx.dir` (up to transport). -/
theorem innerEval_toY_eq {Y X : Type} {p : X → Y}
    (idx : (polyToDepPoly D).OuterIdx Y)
    (e : (polyToDepPoly D).InnerEval idx X p)
    (x : D e.reprIdx.1) :
    e.toY x = idx.dir (e.posMatch ▸ x) := by
  have dirCompat := e.dirCompat x
  simp only [polyToDepPoly, id_eq] at dirCompat
  exact dirCompat.symm

/-- Every inner evaluation implies the outer index is valid. -/
theorem innerEval_valid {Y X : Type} {p : X → Y}
    (idx : (polyToDepPoly D).OuterIdx Y)
    (e : (polyToDepPoly D).InnerEval idx X p) :
    validIdx idx := by
  use e.posMatch ▸ e.reprIdx.2
  simp only [polyToDepPoly] at e ⊢
  rw [e.elemCompat]
  rw [innerEval_toY_eq idx e e.reprIdx.2]

end polyToDepPoly

/-! ## Embedding Dirichlet Functors

A Dirichlet functor on `Over Y` is a coproduct of representables in the slice category.
It consists of:
- Positions `I : Type`
- For each `i : I`, a representing object `(T_i, p_i : T_i → Y)` in `Over Y`

The evaluation at a slice object `(X, p : X → Y)` is:
```
D(X, p) = Σ i : I, Hom_{Over Y}((X, p), (T_i, p_i))
        = Σ i : I, { f : X → T_i | p = p_i ∘ f }
```

To embed this into `DepPolyFunctor`:
- Outer polynomial is trivial: `(Unit, fun _ => Empty)`
- Inner indices are pairs `⟨i, t⟩` where `i : I` and `t : T_i`
- Each inner representable `⟨i, t⟩` has representing type `T_i` with element `t`

This handles empty representing types naturally: if `T_i = Empty`, there are
simply no inner indices with first component `i`.

`OuterIdx Y = Unit × (Empty → Y) × Y ≅ Y`, so outer indices are just elements
of `Y`. The `elemCompat` constraint then selects inner indices `⟨i, t⟩` where
`proj i t = elem`.
-/

/-- A Dirichlet functor on the slice category, given by positions and
representing objects. -/
structure DirichletFunctor (Y : Type) where
  /-- Position type -/
  pos : Type
  /-- Representing type at each position -/
  reprType : pos → Type
  /-- Projection to Y for each representing object -/
  proj : (i : pos) → reprType i → Y

/-- Embed a Dirichlet functor into `DepPolyFunctor`.

The outer polynomial is trivial `(Unit, Empty)`. Inner indices are pairs
`⟨i, t⟩` where `i : D.pos` and `t : D.reprType i`. This naturally handles
empty representing types.

The `elemCompat` constraint partitions inner indices by the outer `elem`:
at outer index with `elem = y`, only inner indices `⟨i, t⟩` with
`D.proj i t = y` are accessible. -/
def dirichletToDepPoly {Y : Type} (D : DirichletFunctor Y) : DepPolyFunctor where
  outerPoly := ccrObjMk (fun (_ : Unit) => Empty)
  innerIdx := Σ i : D.pos, D.reprType i
  reprType := fun ⟨i, _⟩ => D.reprType i
  reprPos := fun _ => ()
  reprDir := fun _ e => Empty.elim e
  reprElem := fun ⟨_, t⟩ => t

namespace dirichletToDepPoly

variable {Y : Type} {D : DirichletFunctor Y}

/-- The outer index for a Dirichlet embedding is essentially just an element
of Y. -/
def outerIdxOfElem (y : Y) : (dirichletToDepPoly D).OuterIdx Y where
  pos := ()
  dir := Empty.elim
  elem := y

/-- Extract the element from an outer index. -/
def elemOfOuterIdx (idx : (dirichletToDepPoly D).OuterIdx Y) : Y :=
  idx.elem

/-- Construct an inner evaluation from position, element, and factorization.

Given `i : D.pos`, `t : D.reprType i` with `idx.elem = D.proj i t`, and a
factorization `fromX : X → D.reprType i` with `p = D.proj i ∘ fromX`, we
construct the inner evaluation using inner index `⟨i, t⟩`. -/
def mkInnerEval {X : Type} {p : X → Y}
    (idx : (dirichletToDepPoly D).OuterIdx Y)
    (i : D.pos) (t : D.reprType i)
    (elemEq : idx.elem = D.proj i t)
    (fromX : X → D.reprType i)
    (factor : p = D.proj i ∘ fromX) :
    (dirichletToDepPoly D).InnerEval idx X p where
  reprIdx := ⟨i, t⟩
  posMatch := rfl
  toY := D.proj i
  dirCompat := fun e => Empty.elim e
  elemCompat := elemEq
  fromX := fromX
  triangle := factor

/-- For inner evaluations constructed via `mkInnerEval`, `toY` equals
`D.proj`. -/
theorem mkInnerEval_toY {X : Type} {p : X → Y}
    (idx : (dirichletToDepPoly D).OuterIdx Y)
    (i : D.pos) (t : D.reprType i) (elemEq : idx.elem = D.proj i t)
    (fromX : X → D.reprType i) (factor : p = D.proj i ∘ fromX) :
    (mkInnerEval idx i t elemEq fromX factor).toY = D.proj i := by
  rfl

/-- The `elemCompat` field shows `idx.elem` equals `toY` applied to the
inner element. -/
theorem innerEval_elem_toY {X : Type} {p : X → Y}
    (idx : (dirichletToDepPoly D).OuterIdx Y)
    (e : (dirichletToDepPoly D).InnerEval idx X p) :
    idx.elem = e.toY e.reprIdx.2 := by
  simp only [dirichletToDepPoly] at e ⊢
  exact e.elemCompat

end dirichletToDepPoly

end DepPolyFunctor

end GebLean
