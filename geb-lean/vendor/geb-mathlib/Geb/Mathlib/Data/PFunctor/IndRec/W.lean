/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Mathlib.Data.PFunctor.IndRec.Slice
public import Geb.Mathlib.Data.PFunctor.Slice.W

/-!
# The data type and decoder described by an IR code

An endo-code `γ : IR I I` denotes an endofunctor of `Type/I`, and the data
type it describes is that endofunctor's initial algebra, carrying its
decoder as the algebra's structure map into `I` — the `µ γ` and
`decode γ` of [HancockMcBrideGhaniMalatestaAltenkirch2013], Section 3.
It is obtained here from the translation `IR.toSlicePFunctor` of the code
to a slice polynomial functor (`Geb/Mathlib/Data/PFunctor/IndRec/Slice.lean`)
and the W-type of that functor (`Geb/Mathlib/Data/PFunctor/Slice/W.lean`).
Routing through the translation is what makes the fixed point available at
all: `IR.interpObj` computes by recursion on the code, so a data type
defined directly as the fixed point of `IR.interpObj γ` would be rejected
for the code variable `γ`, whereas `SlicePFunctor.W` is a subtype of an
ordinary `WType`.

The algebra structure map — the constructor `IR.W.mk`, the `in` of
Section 3 — needs a node of the direct interpretation to be presented as a
node of the translated polynomial. That presentation is one direction of
the agreement of the two semantics established by Lemma 2 of
[HancockMcBrideGhaniMalatestaAltenkirch2013]. Its type mentions both
semantics, so on its own it has no carrier to be folded into; it is
computed instead as the third component of `IR.posSlice`, a fold whose
other two components are the interpretation and the slice polynomial
functor themselves.

## Main definitions

* `IR.PosToSliceSig` — the signature of the presentation of a node of an
  interpretation as a node of a slice polynomial functor.
* `IR.posToSliceIota`, `IR.posToSliceSigma`, `IR.posToSliceDelta` — the
  per-shape steps of that presentation.
* `IR.PosSlice`, `IR.posSliceIota`, `IR.posSliceSigma`,
  `IR.posSliceDelta`, `IR.posSliceAlg`, `IR.posSlice` — the three
  components folded together, the per-shape cases, the algebra assembling
  them, and the fold.
* `IR.W`, `IR.wDecode` — the data type an endo-code describes and its
  decoder (`µ γ` and `decode γ`), with `IR.wObj` the object of `Type/I`
  they form.
* `IR.W.mk` — the constructor, the `in` of Section 3.

## Main statements

* `IR.posSlice_interp`, `IR.posSlice_spf` — the first two components of
  `IR.posSlice` are `IR.interpObj` and `IR.toSlicePFunctor`.
* `IR.wDecode_mk` — the decoder of a constructed element is the
  interpretation's decoding of the node it was constructed from: the
  algebra law of `IR.W.mk`.

## Implementation notes

`IR.W` is stated for codes at `IR.{max uA uI, uB, uI, uI}`. The index
universe must not exceed the code's arity universes: the objects of
`Type/I` that `IR.interpObj` accepts have their carriers at
`Type (max uA uB)`, while the carrier of the W-type is at
`Type (max uA uB uI)`, so the two agree exactly when `uI ≤ max uA uB`.

`IR.posSlice` is a fold by `IR.elim`, whose computation rule is
definitional, and not by the recursor `IR.rec`, whose computation rule is
not. The difference is what lets everything built on it reduce on a
closed code, so that a value equation about a concrete data type is
`rfl`. It is bought by defining `IR.W` and `IR.W.mk` in terms of the
fold's components rather than of `IR.interpObj` and `IR.toSlicePFunctor`,
which `IR.posSlice_interp` and `IR.posSlice_spf` identify them with.

## References

* [HancockMcBrideGhaniMalatestaAltenkirch2013]

## Tags

inductive-recursive, initial algebra, W-type, polynomial functor,
slice category
-/

@[expose] public section

universe uA uB uI uO

namespace IndRec

open CategoryTheory

namespace IR

variable (I : Type uI) (O : Type uO)

/-- The signature of the presentation of a node of an interpretation `α`
as a node of a slice polynomial functor `F`, at the same output index: a
node of `α` at an object `X` of `Type/I` yields a node of `F` at `X` whose
shape-output index is the node's decoding. -/
@[nolint checkUnivs]
def PosToSliceSig (α : FreeCoprodCompDisc.Map.{max uA uB, uI, uO} I O)
    (F : SlicePFunctor.{max uA uB uI, uB, uI, uO} I O) :
    Type (max (uA + 1) (uB + 1) uI) :=
  (X : FreeCoprodCompDisc.{max uA uB, uI} I) → (z : (α X).1) →
    { y : F.toSliceDomPFunctor.Obj X.2 // F.q y.1.1 = (α X).2 z }

/-- The constant (`iota`) step of `IR.posToSlice`: the one shape of
`IR.toSlicePFunctorIota`, with the empty direction assignment. -/
@[nolint checkUnivs]
def posToSliceIota (o : O) :
    PosToSliceSig I O (interpObjIota.{uA, uB, uI, uO} I O o)
      (toSlicePFunctorIota.{uA, uB, uI, uO} I O o) :=
  fun _ _ ↦ ⟨⟨⟨PUnit.unit, PEmpty.elim⟩, funext fun b ↦ PEmpty.elim b⟩, rfl⟩

/-- The dependent sum (`sigma`) step of `IR.posToSlice`: the node's arity
element tags the subcode's shape into the coproduct of shapes. -/
@[nolint checkUnivs]
def posToSliceSigma (A : Type uA)
    (α : A → FreeCoprodCompDisc.Map.{max uA uB, uI, uO} I O)
    (F : A → SlicePFunctor.{max uA uB uI, uB, uI, uO} I O)
    (m : (a : A) → PosToSliceSig I O (α a) (F a)) :
    PosToSliceSig I O (interpObjSigma I O A α)
      (toSlicePFunctorSigma.{uA, uB, uI, uO} I O A F) :=
  fun X z ↦
    let w := m z.1 X z.2
    ⟨⟨⟨⟨z.1, w.1.1.1⟩, w.1.1.2⟩, w.1.2⟩, w.2⟩

/-- The dependent product (`delta`) step of `IR.posToSlice`: the node's
recursive fields become the directions of the representable factor of the
summand at the assignment they induce, and the subcode's node the other
factor. -/
@[nolint checkUnivs]
def posToSliceDelta (B : Type uB)
    (α : (B → I) → FreeCoprodCompDisc.Map.{max uA uB, uI, uO} I O)
    (F : (B → I) → SlicePFunctor.{max uA uB uI, uB, uI, uO} I O)
    (m : (f : B → I) → PosToSliceSig I O (α f) (F f)) :
    PosToSliceSig I O (interpObjDelta I O B α)
      (toSlicePFunctorDelta.{uA, uB, uI, uO} I O B F) :=
  fun X z ↦
    let w := m (X.2 ∘ z.1) X z.2
    ⟨⟨⟨⟨X.2 ∘ z.1, ⟨PUnit.unit, w.1.1.1⟩⟩, Sum.elim z.1 w.1.1.2⟩,
        funext fun b ↦ match b with
          | Sum.inl _ => rfl
          | Sum.inr d => congrFun w.1.2 d⟩,
      w.2⟩

/-- The interpretation of a code, the code's slice polynomial functor, and
the presentation of the former's nodes as the latter's, folded together.
Folding the three together is what makes the presentation computable by
`IR.elim`, whose computation rule is definitional, rather than by the
recursor `IR.rec`, whose computation rule is not: the presentation's type
mentions the other two components, so alone it has no fixed carrier. -/
@[nolint checkUnivs]
structure PosSlice : Type (max (uA + 1) (uB + 1) (uI + 1) uO) where
  /-- The interpretation's object map. -/
  interp : FreeCoprodCompDisc.Map.{max uA uB, uI, uO} I O
  /-- The slice polynomial functor. -/
  spf : SlicePFunctor.{max uA uB uI, uB, uI, uO} I O
  /-- The presentation of an interpretation node as a functor node. -/
  tr : PosToSliceSig I O interp spf

/-- The constant (`iota`) case of `IR.posSlice`. -/
@[nolint checkUnivs]
def posSliceIota (o : O) : PosSlice.{uA, uB, uI, uO} I O :=
  ⟨interpObjIota.{uA, uB, uI, uO} I O o, toSlicePFunctorIota.{uA, uB, uI, uO} I O o,
    posToSliceIota.{uA, uB, uI, uO} I O o⟩

/-- The dependent sum (`sigma`) case of `IR.posSlice`. -/
@[nolint checkUnivs]
def posSliceSigma (A : Type uA) (sub : A → PosSlice.{uA, uB, uI, uO} I O) :
    PosSlice.{uA, uB, uI, uO} I O :=
  ⟨interpObjSigma I O A fun a ↦ (sub a).interp,
    toSlicePFunctorSigma.{uA, uB, uI, uO} I O A fun a ↦ (sub a).spf,
    posToSliceSigma I O A _ _ fun a ↦ (sub a).tr⟩

/-- The dependent product (`delta`) case of `IR.posSlice`. -/
@[nolint checkUnivs]
def posSliceDelta (B : Type uB) (sub : (B → I) → PosSlice.{uA, uB, uI, uO} I O) :
    PosSlice.{uA, uB, uI, uO} I O :=
  ⟨interpObjDelta I O B fun f ↦ (sub f).interp,
    toSlicePFunctorDelta.{uA, uB, uI, uO} I O B fun f ↦ (sub f).spf,
    posToSliceDelta I O B _ _ fun f ↦ (sub f).tr⟩

/-- The algebra which computes one step of `IR.posSlice`. -/
@[nolint checkUnivs]
def posSliceAlg :
    Alg.{uA, uB, uI, uO, max (uA + 1) (uB + 1) (uI + 1) uO} I O (PosSlice.{uA, uB, uI, uO} I O) :=
  ⟨posSliceIota.{uA, uB, uI, uO} I O, posSliceSigma I O, posSliceDelta I O⟩

/-- A code's interpretation, slice polynomial functor, and the
presentation of the former's nodes as the latter's — one direction of the
agreement of the two semantics established by Lemma 2 of
[HancockMcBrideGhaniMalatestaAltenkirch2013]. -/
@[nolint checkUnivs]
def posSlice (γ : IR.{uA, uB, uI, uO} I O) : PosSlice.{uA, uB, uI, uO} I O :=
  elimAlg I O (PosSlice.{uA, uB, uI, uO} I O) (posSliceAlg I O) γ

/-- The interpretation component of `IR.posSlice` is `IR.interpObj`. -/
@[nolint checkUnivs]
theorem posSlice_interp (γ : IR.{uA, uB, uI, uO} I O) :
    (posSlice I O γ).interp = interpObj I O γ :=
  induction I O (motive := fun γ ↦ (posSlice I O γ).interp = interpObj I O γ)
    (fun s _ ih ↦ match s with
      | Sum.inl _ => rfl
      | Sum.inr (Sum.inl A) =>
          congrArg (interpObjSigma I O A) (funext fun a ↦ ih (ULift.up a))
      | Sum.inr (Sum.inr B) =>
          congrArg (interpObjDelta I O B) (funext fun f ↦ ih (ULift.up f)))
    γ

/-- The functor component of `IR.posSlice` is `IR.toSlicePFunctor`. -/
@[nolint checkUnivs]
theorem posSlice_spf (γ : IR.{uA, uB, uI, uO} I O) :
    (posSlice I O γ).spf = toSlicePFunctor I O γ :=
  induction I O (motive := fun γ ↦ (posSlice I O γ).spf = toSlicePFunctor I O γ)
    (fun s _ ih ↦ match s with
      | Sum.inl _ => rfl
      | Sum.inr (Sum.inl A) =>
          congrArg (toSlicePFunctorSigma.{uA, uB, uI, uO} I O A)
            (funext fun a ↦ ih (ULift.up a))
      | Sum.inr (Sum.inr B) =>
          congrArg (toSlicePFunctorDelta.{uA, uB, uI, uO} I O B)
            (funext fun f ↦ ih (ULift.up f)))
    γ

end IR

namespace IR

variable (I : Type uI)

/-- The data type an endo-code describes (the `µ γ` of
[HancockMcBrideGhaniMalatestaAltenkirch2013], Section 3): the W-type of
the code's slice-polynomial translation. -/
@[nolint checkUnivs]
def W (γ : IR.{max uA uI, uB, uI, uI} I I) : Type (max uA uB uI) :=
  SlicePFunctor.W (posSlice.{max uA uI, uB, uI, uI} I I γ).spf

/-- The decoder of the data type an endo-code describes (the `decode γ` of
[HancockMcBrideGhaniMalatestaAltenkirch2013], Section 3): the slice
W-type's structure map. -/
@[nolint checkUnivs]
def wDecode (γ : IR.{max uA uI, uB, uI, uI} I I) : W.{uA, uB, uI} I γ → I :=
  SlicePFunctor.wIndex (posSlice.{max uA uI, uB, uI, uI} I I γ).spf

/-- The data type and its decoder read as an object of `Type/I`, the
object at which the code's interpretation is taken to obtain the nodes
`IR.W.mk` accepts. -/
@[nolint checkUnivs]
def wObj (γ : IR.{max uA uI, uB, uI, uI} I I) :
    FreeCoprodCompDisc.{max uA uB uI, uI} I :=
  ⟨W.{uA, uB, uI} I γ, wDecode I γ⟩

/-- The constructor of the data type an endo-code describes (the `in` of
[HancockMcBrideGhaniMalatestaAltenkirch2013], Section 3): a node of the
interpretation at `IR.wObj`, presented through `IR.posSlice` as a node of
the translated polynomial. `IR.posSlice_interp` identifies the domain
with `IR.interpObj γ (IR.wObj I γ)`. -/
@[nolint checkUnivs]
def W.mk (γ : IR.{max uA uI, uB, uI, uI} I I)
    (z : ((posSlice.{max uA uI, uB, uI, uI} I I γ).interp (wObj.{uA, uB, uI} I γ)).1) :
    W.{uA, uB, uI} I γ :=
  SlicePFunctor.W.mk ((posSlice.{max uA uI, uB, uI, uI} I I γ).tr (wObj I γ) z).1

/-- The decoder of a constructed element is the interpretation's decoding
of the node it was constructed from: the algebra law of `IR.W.mk`. -/
@[nolint checkUnivs]
theorem wDecode_mk (γ : IR.{max uA uI, uB, uI, uI} I I)
    (z : ((posSlice.{max uA uI, uB, uI, uI} I I γ).interp (wObj.{uA, uB, uI} I γ)).1) :
    wDecode I γ (W.mk.{uA, uB, uI} I γ z) =
      ((posSlice I I γ).interp (wObj I γ)).2 z :=
  ((posSlice I I γ).tr (wObj I γ) z).2

end IR

end IndRec
