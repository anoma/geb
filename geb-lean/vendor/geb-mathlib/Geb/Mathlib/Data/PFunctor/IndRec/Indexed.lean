/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Mathlib.Data.PFunctor.IndRec.W

/-!
# Codes for small indexed induction-recursion

`IIR I D J E` is the type of codes for small indexed inductive-recursive
definitions, Section 6 of
[HancockMcBrideGhaniMalatestaAltenkirch2013]. Where an `IR` code
describes one inductive-recursive definition, an `IIR` code describes a
family of them, indexed by `I` on the way in and `J` on the way out, with
`D` and `E` the type each decodes into at each index. Two things change
from `IR`: the constant code `IIR.iota` names the output index it lands
at as well as the value it decodes to, and the dependent product code
`IIR.delta` carries an index assignment `ix`, choosing the input index of
each of its recursive fields. `IR` is the fragment in which `I` and `J`
are singletons.

Codes are presented as the W-type of a polynomial functor `IIR.pFunctor`,
following `IR` (`Geb/Mathlib/Data/PFunctor/IndRec/Basic.lean`).

The reduction of small indexed induction-recursion to small
induction-recursion is `IIR.toIR`, the `⌊·⌋` of Section 6: a code over
`I`/`J` with decodings `D`/`E` becomes a plain code over the total spaces
`Σ i, D i` and `Σ j, E j`. Through it, the data type and decoder an
endo-code describes are derived from those of an `IR` code
(`Geb/Mathlib/Data/PFunctor/IndRec/W.lean`) by cutting into fibres over
the index.

## Main definitions

* `IIR.pFunctor` — the polynomial functor whose W-type defines codes:
  shapes `IIR.Shape`, directions `IIR.Direction`.
* `IIR`, `IIR.mk` — the type of codes and its constructor.
* `IIR.iota`, `IIR.sigma`, `IIR.delta` — the code constructors, one per
  shape, and `IIR.delta1` the single-recursive-field special case of
  `IIR.delta` (the `δ₁` of Section 6).
* `IIR.Obj`, `IIR.Alg`, `IIR.Alg.toHom`, `IIR.elim`, `IIR.elimAlg` — the
  polynomial functor's interpretation, the pattern-matched form of an
  algebra of it, and the eliminator.
* `IIR.FamSlice` — the base category's objects: a family, over the index
  type, of objects of the slice over that index's decoding type.
* `IIR.interpAlg`, `IIR.interp` — the direct interpretation of a code as
  a functor between such families, the `⟦·⟧_IIR` of Section 6.
* `IIR.toIRAlg`, `IIR.toIR` — the reduction to `IR` codes, the `⌊·⌋` of
  Section 6.
* `IIR.W`, `IIR.wDecode` — the indexed family of data types an endo-code
  describes and their decoders, cut out of `IR.W` and `IR.wDecode` of the
  reduced code.

## Main statements

* `IIR.elimAlg_iota`, `IIR.elimAlg_sigma`, `IIR.elimAlg_delta` — the
  computation rules of `IIR.elimAlg`, all definitional.

## Implementation notes

`IIR.delta`'s shape carries the index assignment as well as the arity,
since the directions — the tuples of decodings the continuation receives
— depend on it; the shape type's third summand is accordingly
`Σ P : Type uB, P → I` rather than `Type uB`.

The reduction `IIR.toIR` carries `IIR.iota` and `IIR.sigma` across
unchanged. Its work is in the `IIR.delta` clause: a recursive field of
the reduced code decodes to a pair of an index and a value, so the
reduction cannot ask for a field at a chosen index. It takes the fields
wherever they land and adds an `IR.sigma` over the proof that they landed
at the indices `ix` demands — the `σ (i ≡ π₀ ∘ iD)` of Section 6 — which
is then what transports the values into the types the continuation
expects. The condition is stated pointwise rather than as an equality of
the two index assignments, so that building one needs no functional
extensionality. It is embedded into `Type uA` as
`ULift (PLift ...)`, following `IR.sliceCode`.

`IIR.W` is stated for codes at
`IIR.{max uA uI uD, uB, uI, uD, uI, uD}`, the instance at which the
reduced code meets the universe condition of `IR.W`. It carries no
constructor of its own: an element is an element of the reduced code's
data type, built by `IR.W.mk`, together with the proof that it decoded to
the index of the fibre. The index constraints the reduction introduces
appear there as data — the proof that each recursive field landed where
the index assignment demands.

The correspondence between `IIR.interp` and the interpretation of
`IIR.toIR` — Section 6's remark that the two agree up to the
equivalences among `(i : I) → Set/(D i)`, `Σ D → Set` and `Set/Σ D` — is
not formalized here.

## References

* [HancockMcBrideGhaniMalatestaAltenkirch2013]

## Tags

indexed induction-recursion, inductive-recursive, polynomial functor,
W-type, initial algebra
-/

@[expose] public section

universe uA uB uI uD uJ uE

namespace IndRec

open CategoryTheory

variable (I : Type uI) (D : I → Type uD) (J : Type uJ) (E : J → Type uE)

namespace IIR

/-- The shape type of the polynomial functor whose W-type defines codes
for small indexed inductive-recursive types: an output index paired with
a decoding, a non-recursive arity, or a recursive arity with an index
assignment. -/
@[nolint checkUnivs]
def Shape : Type (max (uA + 1) (uB + 1) uI uJ uE) :=
  (Σ j : J, E j) ⊕ Type uA ⊕ (Σ P : Type uB, P → I)

/-- The direction type of the polynomial functor whose W-type defines
codes for small indexed inductive-recursive types. A `delta` shape's
directions are the tuples of decodings its recursive fields deliver, at
the input indices its index assignment chooses. -/
@[nolint checkUnivs]
def Direction : Shape.{uA, uB, uI, uJ, uE} I J E → Type (max uA uB uD) :=
  Sum.elim (fun _ ↦ PEmpty)
    (Sum.elim (fun A ↦ ULift.{max uB uD} A)
      (fun x ↦ ULift.{uA} ((p : x.1) → D (x.2 p))))

/-- The polynomial functor whose W-type defines codes for small indexed
inductive-recursive types. -/
@[nolint checkUnivs]
def pFunctor :
    PFunctor.{max (uA + 1) (uB + 1) uI uJ uE, max uA uB uD} :=
  ⟨Shape.{uA, uB, uI, uJ, uE} I J E, Direction I D J E⟩

/-- The value at `V` of the interpretation of `IIR.pFunctor` as an
endofunctor on `Type`. -/
@[nolint checkUnivs]
def Obj.{v} (V : Type v) : Type (max (uA + 1) (uB + 1) uI uD uJ uE v) :=
  PFunctor.Obj (pFunctor.{uA, uB, uI, uD, uJ, uE} I D J E) V

/-- A pattern-matched form of an algebra of `IIR.pFunctor`: one clause
per code constructor. -/
@[nolint checkUnivs]
def Alg.{v} (V : Type v) : Type (max (uA + 1) (uB + 1) uI uD uJ uE v) :=
  ((Σ j : J, E j) → V) × ((A : Type uA) → (A → V) → V) ×
    ((P : Type uB) → (ix : P → I) → (((p : P) → D (ix p)) → V) → V)

/-- Convert `IIR.Alg` to the morphism form of an algebra of
`IIR.pFunctor`. -/
@[nolint checkUnivs]
def Alg.toHom.{v} (V : Type v)
    (alg : Alg.{uA, uB, uI, uD, uJ, uE, v} I D J E V) :
    Obj.{uA, uB, uI, uD, uJ, uE, v} I D J E V → V :=
  fun ⟨s, ds⟩ ↦ match s with
  | Sum.inl je => alg.1 je
  | Sum.inr (Sum.inl (A : Type uA)) => alg.2.1 A (ds ∘ ULift.up)
  | Sum.inr (Sum.inr x) => alg.2.2 x.1 x.2 (ds ∘ ULift.up)

end IIR

/-- The type of codes for small indexed inductive-recursive definitions
(Section 6 of [HancockMcBrideGhaniMalatestaAltenkirch2013]): the W-type
of `IIR.pFunctor`. -/
@[nolint checkUnivs]
def IIR : Type (max (uA + 1) (uB + 1) uI uD uJ uE) :=
  PFunctor.W (IIR.pFunctor.{uA, uB, uI, uD, uJ, uE} I D J E)

namespace IIR

/-- The constructor for `IIR`. -/
def mk (s : Shape.{uA, uB, uI, uJ, uE} I J E)
    (d : Direction I D J E s → IIR.{uA, uB, uI, uD, uJ, uE} I D J E) :
    IIR.{uA, uB, uI, uD, uJ, uE} I D J E :=
  WType.mk s d

/-- The constant (`iota`) code: no subcodes; the node lands at the output
index `m` and decodes to `ev`. -/
def iota (m : J) (ev : E m) : IIR.{uA, uB, uI, uD, uJ, uE} I D J E :=
  mk I D J E (Sum.inl ⟨m, ev⟩) PEmpty.elim

/-- The dependent sum (`sigma`) code: a non-recursive field of type `A`,
then the subcode it selects. -/
def sigma (A : Type uA) (c : A → IIR.{uA, uB, uI, uD, uJ, uE} I D J E) :
    IIR.{uA, uB, uI, uD, uJ, uE} I D J E :=
  mk I D J E (Sum.inr (Sum.inl A)) (c ∘ ULift.down)

/-- The dependent product (`delta`) code: a `P`-indexed family of
recursive fields, the field at `p` taken at input index `ix p`, whose
decodings the subcode assignment `c` receives. -/
def delta (P : Type uB) (ix : P → I)
    (c : ((p : P) → D (ix p)) → IIR.{uA, uB, uI, uD, uJ, uE} I D J E) :
    IIR.{uA, uB, uI, uD, uJ, uE} I D J E :=
  mk I D J E (Sum.inr (Sum.inr ⟨P, ix⟩)) (c ∘ ULift.down)

/-- A single recursive field at the input index `n`, presented as a
`PUnit`-indexed family: the `δ₁` of Section 6 of
[HancockMcBrideGhaniMalatestaAltenkirch2013]. Its continuation receives
that field's decoded value, which is what lets the shape of the rest of
the node depend on it. -/
def delta1 (n : I) (c : D n → IIR.{uA, uB, uI, uD, uJ, uE} I D J E) :
    IIR.{uA, uB, uI, uD, uJ, uE} I D J E :=
  delta I D J E PUnit (fun _ ↦ n) fun dv ↦ c (dv PUnit.unit)

/-- The eliminator (the algebra morphism from the initial algebra) for
`IIR`, taking the algebra in morphism form. -/
def elim.{v} (V : Type v)
    (alg : Obj.{uA, uB, uI, uD, uJ, uE, v} I D J E V → V) :
    IIR.{uA, uB, uI, uD, uJ, uE} I D J E → V :=
  WType.elim V alg

/-- The eliminator for `IIR`, taking the algebra in the `IIR.Alg`
form. -/
def elimAlg.{v} (V : Type v)
    (alg : Alg.{uA, uB, uI, uD, uJ, uE, v} I D J E V) :
    IIR.{uA, uB, uI, uD, uJ, uE} I D J E → V :=
  elim I D J E V (Alg.toHom I D J E V alg)

/-- Computation rule for `IIR.elimAlg` at `IIR.iota` (definitional). -/
theorem elimAlg_iota.{v} (V : Type v)
    (alg : Alg.{uA, uB, uI, uD, uJ, uE, v} I D J E V) (m : J) (ev : E m) :
    elimAlg I D J E V alg (iota I D J E m ev) = alg.1 ⟨m, ev⟩ := rfl

/-- Computation rule for `IIR.elimAlg` at `IIR.sigma` (definitional). -/
theorem elimAlg_sigma.{v} (V : Type v)
    (alg : Alg.{uA, uB, uI, uD, uJ, uE, v} I D J E V) (A : Type uA)
    (c : A → IIR.{uA, uB, uI, uD, uJ, uE} I D J E) :
    elimAlg I D J E V alg (sigma I D J E A c) =
      alg.2.1 A fun a ↦ elimAlg I D J E V alg (c a) := rfl

/-- Computation rule for `IIR.elimAlg` at `IIR.delta` (definitional). -/
theorem elimAlg_delta.{v} (V : Type v)
    (alg : Alg.{uA, uB, uI, uD, uJ, uE, v} I D J E V) (P : Type uB)
    (ix : P → I)
    (c : ((p : P) → D (ix p)) → IIR.{uA, uB, uI, uD, uJ, uE} I D J E) :
    elimAlg I D J E V alg (delta I D J E P ix c) =
      alg.2.2 P ix fun dv ↦ elimAlg I D J E V alg (c dv) := rfl

/-- The objects of the base category of small indexed
induction-recursion: a family, over the index type `I`, of objects of the
slice over that index's decoding type `D i`. -/
@[nolint checkUnivs]
def FamSlice : Type (max (uA + 1) (uB + 1) uI uD) :=
  (n : I) → FreeCoprodCompDisc.{max uA uB, uD} (D n)

/-- The algebra which computes one step of the direct interpretation of
an `IIR` code as a functor between families of slices (the `⟦·⟧_IIR` of
Section 6 of [HancockMcBrideGhaniMalatestaAltenkirch2013]). A constant
code contributes only the proof that it landed at the index asked for,
and decodes by transporting its value along that proof. -/
@[nolint checkUnivs]
def interpAlg :
    Alg.{uA, uB, uI, uD, uJ, uE, max (uA + 1) (uB + 1) uI uD uJ uE} I D J E
      (FamSlice.{uA, uB, uI, uD} I D → FamSlice.{uA, uB, uJ, uE} J E) :=
  ⟨fun je _ n ↦
      ⟨ULift.{max uA uB} (PLift (je.1 = n)), fun q ↦ q.down.down ▸ je.2⟩,
    fun A sub G n ↦
      FreeCoprodCompDisc.coprod (E n) A fun a ↦ sub a G n,
    fun P ix sub G n ↦
      FreeCoprodCompDisc.coprod (E n) ((p : P) → (G (ix p)).1) fun ig ↦
        sub (fun p ↦ (G (ix p)).2 (ig p)) G n⟩

/-- The direct interpretation of an `IIR` code as a functor between
families of slices: the `⟦·⟧_IIR` of Section 6 of
[HancockMcBrideGhaniMalatestaAltenkirch2013]. -/
@[nolint checkUnivs]
def interp (c : IIR.{uA, uB, uI, uD, uJ, uE} I D J E) :
    FamSlice.{uA, uB, uI, uD} I D → FamSlice.{uA, uB, uJ, uE} J E :=
  elimAlg I D J E _ (interpAlg I D J E) c

/-- The algebra which computes one step of the reduction of `IIR` codes
to `IR` codes over the total spaces (the `⌊·⌋` of Section 6 of
[HancockMcBrideGhaniMalatestaAltenkirch2013]). -/
@[nolint checkUnivs]
def toIRAlg :
    Alg.{uA, uB, uI, uD, uJ, uE, max (uA + 1) (uB + 1) uI uD uJ uE} I D J E
      (IR.{uA, uB, max uI uD, max uJ uE} (Σ i, D i) (Σ j, E j)) :=
  ⟨IR.iota (Σ i, D i) (Σ j, E j),
    IR.sigma (Σ i, D i) (Σ j, E j),
    fun P ix c ↦
      IR.delta (Σ i, D i) (Σ j, E j) P fun iD ↦
        IR.sigma (Σ i, D i) (Σ j, E j)
          (ULift.{uA} (PLift (∀ p, (iD p).1 = ix p))) fun h ↦
            c fun p ↦ h.down.down p ▸ (iD p).2⟩

/-- The reduction of an `IIR` code to an `IR` code over the total spaces:
the `⌊·⌋` of Section 6 of
[HancockMcBrideGhaniMalatestaAltenkirch2013]. -/
@[nolint checkUnivs]
def toIR (c : IIR.{uA, uB, uI, uD, uJ, uE} I D J E) :
    IR.{uA, uB, max uI uD, max uJ uE} (Σ i, D i) (Σ j, E j) :=
  elimAlg I D J E _ (toIRAlg I D J E) c

end IIR

namespace IIR

/-- The indexed family of data types an endo-code describes: the data
type of the reduced `IR` code, cut into fibres over the index. -/
@[nolint checkUnivs]
def W (c : IIR.{max uA uI uD, uB, uI, uD, uI, uD} I D I D) (n : I) :
    Type (max uA uB uI uD) :=
  { x : IR.W.{uA, uB, max uI uD} (Σ i, D i) (toIR I D I D c) //
      (IR.wDecode (Σ i, D i) (toIR I D I D c) x).1 = n }

/-- The decoders of the indexed family of data types an endo-code
describes: the value component of the reduced code's decoding,
transported along the fibre's index proof. -/
@[nolint checkUnivs]
def wDecode (c : IIR.{max uA uI uD, uB, uI, uD, uI, uD} I D I D) (n : I)
    (x : W.{uA, uB, uI, uD} I D c n) : D n :=
  x.2 ▸ (IR.wDecode (Σ i, D i) (toIR I D I D c) x.1).2

end IIR

end IndRec
