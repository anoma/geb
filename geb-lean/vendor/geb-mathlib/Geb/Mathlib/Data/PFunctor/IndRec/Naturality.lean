/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.CategoryTheory.FreeCoprodCompDisc.NatTrans
public import Geb.Mathlib.Data.PFunctor.IndRec.Functor
public import Geb.Mathlib.Data.PFunctor.IndRec.Hom

/-!
# Naturality of the IR interpretation and Theorem 3

Theorem 3 of [HancockMcBrideGhaniMalatestaAltenkirch2013]: the
homset between two `IR` codes is equivalent to the space of
natural transformations between their interpretations
(`IR.interpHomEquiv`), by `IR.rec` on the domain code. The
supporting development comprises the per-summand decomposition at
a `delta` code (the naturality upgrade of the paper's Lemma 3),
the naturality upgrade of Lemma 4, the ∅-evaluation and `InnerHom`
fiber equivalences of the `ι`-case, and the plus-lift bridge.

## Main definitions

* `IR.deltaInto`, `IR.deltaDesc` — the natural inclusions of the
  copower summands into the `delta` interpretation and their
  cotuple ([HancockMcBrideGhaniMalatestaAltenkirch2013], Lemma 3,
  upgraded to per-summand natural form).
* `IR.natDeltaEquiv` — the per-summand decomposition of
  transformation spaces at a `delta` code.
* `IR.natIotaEquiv` — the ∅-evaluation equivalence at an `ι`
  domain: transformations out of `⟦ι o⟧` correspond to their
  components at the initial object.
* `IR.innerHomEquiv` — the homset from an `ι`-code as the fiber,
  over the index, of the decoding of the codomain's interpretation
  at the initial object
  ([HancockMcBrideGhaniMalatestaAltenkirch2013], Definition 8's
  `ι`-clauses, in the form Theorem 3's `ι`-case consumes).
* `IR.plusLiftBridgeNat`, `IR.plusLiftBridgeNatInv` — the inverse
  pair of transformations bridging the `plus`-precomposed
  interpretation at the lifted summand and the Lemma 4 right-hand
  map.
* `IR.interpHomEquiv` — Theorem 3 of
  [HancockMcBrideGhaniMalatestaAltenkirch2013]: `Hom γ γ'` is
  equivalent to the transformation space between the
  interpretations, with the directions `IR.interpHom` and
  `IR.natToHom`.

## Main statements

* `IR.deltaInto_desc`, `IR.deltaDesc_eta`, `IR.deltaHom_ext` — the
  computation and uniqueness laws of the cotuple, and joint
  epicness of the inclusions.
* `IR.deltaInto_natural` — naturality of the inclusions in the
  interpreted object.
* `IR.interpPrecompIso_natural` — naturality of the Lemma 4
  isomorphism family
  ([HancockMcBrideGhaniMalatestaAltenkirch2013], Lemma 4, upgraded
  from the pointwise statement), with the characterizing equation
  `IR.interpPrecompIso_mk`.
* `IR.interpHom_natToHom`, `IR.natToHom_interpHom` — the
  round-trip laws of `IR.interpHomEquiv` (fullness and
  faithfulness of the interpretation on morphisms).

## Implementation notes

The total coproduct of Lemma 3 has an index type exceeding the
uniform index universe, so it never appears as a
`FreeCoprodCompDisc.Map`; the decomposition is per summand. The
`delta`-side morphism map is rewritten by `IR.interpMor_delta`,
and transports of names along equalities of direction assignments
are eliminated by the cast lemmas `IR.interpObj_snd_cast` and
`IR.interpMor_cast`, with `Eq.rec` motives at projection-reduced
types and dependent `rfl`-proofs quantified inside the motive.
The Lemma 4 upgrade rewrites the isomorphism family to step form
before eliminating the morphism's commutation equality and
splitting on the shape; the precomposed code is a stuck match
until the shape is known, after which the per-constructor
`IR.interpMor` equations apply to it.

## References

* [HancockMcBrideGhaniMalatestaAltenkirch2013]

## Tags

inductive-recursive, interpretation, natural transformation
-/

@[expose] public section

universe uA uB uI uO

namespace IndRec

open CategoryTheory

variable (I : Type uI) (O : Type uO)

namespace IR

/-- Decoding of interpretation names commutes with transport along an
equality of direction assignments. -/
theorem interpObj_snd_cast (B : Type uB)
    (c : (B → I) → IR.{max uA uB, uB, uI, uO} I O)
    (X : FreeCoprodCompDisc.{max uA uB, uI} I) {i j : B → I}
    (e : i = j) (n : (interpObj I O (c i) X).1) :
    (interpObj I O (c j) X).2
        (cast (congrArg (fun t ↦ (interpObj I O (c t) X).1) e) n) =
      (interpObj I O (c i) X).2 n :=
  Eq.rec (motive := fun j' e' ↦
      (interpObj I O (c j') X).2
          (cast (congrArg (fun t ↦ (interpObj I O (c t) X).1) e') n) =
        (interpObj I O (c i) X).2 n)
    rfl e

/-- The injection of the `i`-th copower summand into the `delta`
interpretation: a copower name `⟨e, n⟩` maps to the delta name whose
direction is `e.1` restricted along `ULift.up`, with `n` transported
along the induced equality of direction assignments. -/
def deltaInto (B : Type uB)
    (c : (B → I) → IR.{max uA uB, uB, uI, uO} I O)
    (i : B → I) (X : FreeCoprodCompDisc.{max uA uB, uI} I) :
    FreeCoprodCompDisc.Hom O
      (FreeCoprodCompDisc.copowerHomMap
        (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩)
        (interpObj I O (c i)) X)
      (interpObj I O (delta I O B c) X) :=
  ⟨fun p ↦ ⟨p.1.1 ∘ ULift.up,
      cast (congrArg (fun t ↦ (interpObj I O (c t) X).1)
        (congrArg (· ∘ ULift.up) p.1.2).symm) p.2⟩,
    funext (fun p ↦
      interpObj_snd_cast I O B c X
        (congrArg (· ∘ ULift.up) p.1.2).symm p.2)⟩

/-- The cotuple out of the `delta` interpretation: a delta name
`⟨g, n⟩` is dispatched to the component of `m` at the direction
assignment `X.2 ∘ g`, at the copower name pairing the lifted
direction with `n`. -/
def deltaDesc (B : Type uB)
    (c : (B → I) → IR.{max uA uB, uB, uI, uO} I O)
    (X : FreeCoprodCompDisc.{max uA uB, uI} I)
    (Z : FreeCoprodCompDisc.{max uA uB, uO} O)
    (m : (i : B → I) → FreeCoprodCompDisc.Hom O
      (FreeCoprodCompDisc.copowerHomMap
        (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩)
        (interpObj I O (c i)) X) Z) :
    FreeCoprodCompDisc.Hom O (interpObj I O (delta I O B c) X) Z :=
  ⟨fun q ↦ (m (X.2 ∘ q.1)).1 ⟨⟨q.1 ∘ ULift.down, rfl⟩, q.2⟩,
    funext (fun q ↦
      congrFun (m (X.2 ∘ q.1)).2 ⟨⟨q.1 ∘ ULift.down, rfl⟩, q.2⟩)⟩

/-- The transport-elimination step of `IR.deltaInto_desc`: the target
direction assignment is generalized together with the transport
equality and the inner commutation proof, so the base case is
definitional. -/
theorem deltaInto_desc_aux (B : Type uB)
    (c : (B → I) → IR.{max uA uB, uB, uI, uO} I O) (i : B → I)
    (X : FreeCoprodCompDisc.{max uA uB, uI} I)
    (Z : FreeCoprodCompDisc.{max uA uB, uO} O)
    (m : (i' : B → I) → FreeCoprodCompDisc.Hom O
      (FreeCoprodCompDisc.copowerHomMap
        (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i'⟩)
        (interpObj I O (c i')) X) Z)
    (e : FreeCoprodCompDisc.Hom I
      (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) X)
    (n : (interpObj I O (c i) X).1) (j : B → I) (h : i = j)
    (pf : X.2 ∘ ((e.1 ∘ ULift.up) ∘ ULift.down) =
      (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, j⟩).2) :
    (m j).1 ⟨⟨(e.1 ∘ ULift.up) ∘ ULift.down, pf⟩,
        cast (congrArg (fun t ↦ (interpObj I O (c t) X).1) h) n⟩ =
      (m i).1 ⟨e, n⟩ :=
  Eq.rec (motive := fun j' h' ↦
      ∀ pf' : X.2 ∘ ((e.1 ∘ ULift.up) ∘ ULift.down) =
        (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, j'⟩).2,
      (m j').1 ⟨⟨(e.1 ∘ ULift.up) ∘ ULift.down, pf'⟩,
          cast (congrArg (fun t ↦ (interpObj I O (c t) X).1) h') n⟩ =
        (m i).1 ⟨e, n⟩)
    (fun _ ↦ rfl) h pf

/-- Restricting the delta cotuple along the `i`-th injection recovers
the component. -/
theorem deltaInto_desc (B : Type uB)
    (c : (B → I) → IR.{max uA uB, uB, uI, uO} I O) (i : B → I)
    (X : FreeCoprodCompDisc.{max uA uB, uI} I)
    (Z : FreeCoprodCompDisc.{max uA uB, uO} O)
    (m : (i' : B → I) → FreeCoprodCompDisc.Hom O
      (FreeCoprodCompDisc.copowerHomMap
        (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i'⟩)
        (interpObj I O (c i')) X) Z) :
    FreeCoprodCompDisc.Hom.comp O (deltaInto I O B c i X)
      (deltaDesc I O B c X Z m) = m i :=
  Subtype.ext (funext (fun p ↦
    deltaInto_desc_aux I O B c i X Z m p.1 p.2
      (X.2 ∘ (p.1.1 ∘ ULift.up))
      ((congrArg (· ∘ ULift.up) p.1.2).symm) rfl))

/-- Every morphism out of the delta interpretation is the cotuple of
its restrictions along the injections. -/
theorem deltaDesc_eta (B : Type uB)
    (c : (B → I) → IR.{max uA uB, uB, uI, uO} I O)
    (X : FreeCoprodCompDisc.{max uA uB, uI} I)
    (Z : FreeCoprodCompDisc.{max uA uB, uO} O)
    (h : FreeCoprodCompDisc.Hom O (interpObj I O (delta I O B c) X) Z) :
    deltaDesc I O B c X Z
        (fun i ↦ FreeCoprodCompDisc.Hom.comp O (deltaInto I O B c i X) h) =
      h :=
  Subtype.ext (funext (fun _ ↦ rfl))

/-- The `IR.deltaInto` family is jointly epic: two morphisms out of
the delta interpretation agree when their restrictions along every
injection agree. -/
theorem deltaHom_ext (B : Type uB)
    (c : (B → I) → IR.{max uA uB, uB, uI, uO} I O)
    (X : FreeCoprodCompDisc.{max uA uB, uI} I)
    (Z : FreeCoprodCompDisc.{max uA uB, uO} O)
    (f g : FreeCoprodCompDisc.Hom O (interpObj I O (delta I O B c) X) Z)
    (hfg : ∀ i : B → I,
      FreeCoprodCompDisc.Hom.comp O (deltaInto I O B c i X) f =
        FreeCoprodCompDisc.Hom.comp O (deltaInto I O B c i X) g) :
    f = g :=
  (deltaDesc_eta I O B c X Z f).symm.trans
    ((congrArg (deltaDesc I O B c X Z) (funext hfg)).trans
      (deltaDesc_eta I O B c X Z g))

/-- `IR.interpMor` commutes with transport of names along an equality
of direction assignments. -/
theorem interpMor_cast (B : Type uB)
    (c : (B → I) → IR.{max uA uB, uB, uI, uO} I O)
    (X Y : FreeCoprodCompDisc.{max uA uB, uI} I)
    (h : FreeCoprodCompDisc.Hom I X Y) {i j : B → I} (e : i = j)
    (n : (interpObj I O (c i) X).1) :
    cast (congrArg (fun t ↦ (interpObj I O (c t) Y).1) e)
        ((interpMor I O (c i) X Y h).1 n) =
      (interpMor I O (c j) X Y h).1
        (cast (congrArg (fun t ↦ (interpObj I O (c t) X).1) e) n) :=
  Eq.rec (motive := fun j' e' ↦
      cast (congrArg (fun t ↦ (interpObj I O (c t) Y).1) e')
          ((interpMor I O (c i) X Y h).1 n) =
        (interpMor I O (c j') X Y h).1
          (cast (congrArg (fun t ↦ (interpObj I O (c t) X).1) e') n))
    rfl e

/-- The motive of the commutation-equality elimination in
`IR.deltaInto_natural`: the domain decoding is generalized together
with the morphism's commutation proof, and the delta-side morphism
map appears in its `IR.interpMorDelta` form. -/
def DeltaIntoNaturalMotive (B : Type uB)
    (c : (B → I) → IR.{max uA uB, uB, uI, uO} I O) (i : B → I)
    (X1 : Type (max uA uB)) (Y : FreeCoprodCompDisc.{max uA uB, uI} I)
    (h1 : X1 → Y.1) (x2 : X1 → I) (hcomm : Y.2 ∘ h1 = x2) : Prop :=
  FreeCoprodCompDisc.Hom.comp O
      (FreeCoprodCompDisc.copowerHomMapMor
        (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩)
        (interpMor I O (c i)) ⟨X1, x2⟩ Y ⟨h1, hcomm⟩)
      (deltaInto I O B c i Y) =
    FreeCoprodCompDisc.Hom.comp O (deltaInto I O B c i ⟨X1, x2⟩)
      (interpMorDelta I O B (fun f ↦ interpObj I O (c f))
        (fun f ↦ interpMor I O (c f)) ⟨X1, x2⟩ Y ⟨h1, hcomm⟩)

/-- The base case of `IR.deltaInto_natural`: at a factored domain
decoding with reflexive commutation proof, the `homOfEq` transport in
`IR.interpMorDelta` reduces definitionally and the square reduces to
`IR.interpMor_cast` componentwise. -/
theorem deltaInto_natural_base (B : Type uB)
    (c : (B → I) → IR.{max uA uB, uB, uI, uO} I O) (i : B → I)
    (X1 : Type (max uA uB)) (Y : FreeCoprodCompDisc.{max uA uB, uI} I)
    (h1 : X1 → Y.1) :
    DeltaIntoNaturalMotive I O B c i X1 Y h1 (Y.2 ∘ h1) rfl :=
  Subtype.ext (funext (fun p ↦
    congrArg
      (fun t ↦ (⟨h1 ∘ (p.1.1 ∘ ULift.up), t⟩ :
        Σ g : B → Y.1, (interpObj I O (c (Y.2 ∘ g)) Y).1))
      (interpMor_cast I O B c ⟨X1, Y.2 ∘ h1⟩ Y ⟨h1, rfl⟩
        ((congrArg (· ∘ ULift.up) p.1.2).symm) p.2)))

/-- Naturality of `IR.deltaInto` in the object. -/
theorem deltaInto_natural (B : Type uB)
    (c : (B → I) → IR.{max uA uB, uB, uI, uO} I O) (i : B → I) :
    FreeCoprodCompDisc.IsNatTrans I O
      (FreeCoprodCompDisc.copowerHomMap
        (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩)
        (interpObj I O (c i)))
      (interpObj I O (delta I O B c))
      (FreeCoprodCompDisc.copowerHomMapMor
        (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩)
        (interpMor I O (c i)))
      (interpMor I O (delta I O B c))
      (deltaInto I O B c i) :=
  fun X Y h ↦
    match X, h with
    | ⟨X1, x2⟩, ⟨h1, hcomm⟩ =>
      (Eq.rec (motive := fun x2' hcomm' ↦
          DeltaIntoNaturalMotive I O B c i X1 Y h1 x2' hcomm')
        (deltaInto_natural_base I O B c i X1 Y h1) hcomm).trans
        (congrArg
          (fun t ↦ FreeCoprodCompDisc.Hom.comp O
            (deltaInto I O B c i ⟨X1, x2⟩) (t ⟨X1, x2⟩ Y ⟨h1, hcomm⟩))
          (interpMor_delta I O B c).symm)

/-- The per-summand decomposition of transformation spaces at a
`delta` code: transformations out of the `delta` interpretation
correspond to families, over the direction assignments, of
transformations out of the copower summands. -/
def natDeltaEquiv (B : Type uB)
    (c : (B → I) → IR.{max uA uB, uB, uI, uO} I O)
    {G : FreeCoprodCompDisc.Map.{max uA uB, uI, uO} I O}
    (mG : FreeCoprodCompDisc.MapMor I O G) :
    FreeCoprodCompDisc.NatTrans I O (interpObj I O (delta I O B c)) G
        (interpMor I O (delta I O B c)) mG ≃
      ((i : B → I) → FreeCoprodCompDisc.NatTrans I O
        (FreeCoprodCompDisc.copowerHomMap
          (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩)
          (interpObj I O (c i))) G
        (FreeCoprodCompDisc.copowerHomMapMor
          (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩)
          (interpMor I O (c i))) mG) :=
  { toFun := fun η i ↦
      ⟨fun X ↦
        FreeCoprodCompDisc.Hom.comp O (deltaInto I O B c i X) (η.1 X),
        fun X Y h ↦
          (congrArg
              (fun t ↦ FreeCoprodCompDisc.Hom.comp O t (η.1 Y))
              (deltaInto_natural I O B c i X Y h)).trans
            (congrArg
              (FreeCoprodCompDisc.Hom.comp O (deltaInto I O B c i X))
              (η.2 X Y h))⟩,
    invFun := fun θ ↦
      ⟨fun X ↦ deltaDesc I O B c X (G X) (fun i ↦ (θ i).1 X),
        fun X Y h ↦
          deltaHom_ext I O B c X (G Y) _ _ (fun i ↦
            (((congrArg
                  (fun t ↦ FreeCoprodCompDisc.Hom.comp O t
                    (deltaDesc I O B c Y (G Y) (fun i' ↦ (θ i').1 Y)))
                  (deltaInto_natural I O B c i X Y h)).symm.trans
              ((congrArg
                  (FreeCoprodCompDisc.Hom.comp O
                    (FreeCoprodCompDisc.copowerHomMapMor
                      (FreeCoprodCompDisc.lift.{uB, uI, max uA uB}
                        I ⟨B, i⟩)
                      (interpMor I O (c i)) X Y h))
                  (deltaInto_desc I O B c i Y (G Y)
                    (fun i' ↦ (θ i').1 Y))).trans
                ((θ i).2 X Y h))).trans
            (congrArg
              (fun t ↦ FreeCoprodCompDisc.Hom.comp O t (mG X Y h))
              (deltaInto_desc I O B c i X (G X)
                (fun i' ↦ (θ i').1 X)).symm)))⟩,
    left_inv := fun η ↦ Subtype.ext (funext (fun X ↦
      deltaDesc_eta I O B c X (G X) (η.1 X))),
    right_inv := fun θ ↦ funext (fun i ↦ Subtype.ext (funext (fun X ↦
      deltaInto_desc I O B c i X (G X) (fun i' ↦ (θ i').1 X)))) }

/-- The right-hand object map of the Lemma 4 naturality square: the
direct interpretation of `γ` at the coproduct of `⟨Q, i⟩` with the
argument object. -/
def precompRhsMap (Q : Type uB) (i : Q → I)
    (γ : IR.{max uA uB, uB, uI, uO} I O) :
    FreeCoprodCompDisc.Map.{max uA uB, uI, uO} I O :=
  fun k ↦ interpObj I O γ (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Q, i⟩ k)

/-- The morphism-map component of `IR.precompRhsMap`: the direct
interpretation's morphism map at the coproduct of the identity on
`⟨Q, i⟩` with the argument morphism. -/
def precompRhsMapMor (Q : Type uB) (i : Q → I)
    (γ : IR.{max uA uB, uB, uI, uO} I O) :
    FreeCoprodCompDisc.MapMor I O (precompRhsMap I O Q i γ) :=
  fun X Y h ↦ interpMor I O γ
    (FreeCoprodCompDisc.plus I ⟨Q, i⟩ X) (FreeCoprodCompDisc.plus I ⟨Q, i⟩ Y)
    (FreeCoprodCompDisc.coprodPairMor I (FreeCoprodCompDisc.Hom.id I ⟨Q, i⟩) h)

/-- The characterizing equation of `IR.interpPrecompIso` at `IR.mk`:
the isomorphism family computes by one step of
`IR.interpPrecompIsoStep`. -/
theorem interpPrecompIso_mk (s : Shape.{max uA uB, uB, uO} O)
    (d : Direction I O s → IR.{max uA uB, uB, uI, uO} I O) :
    interpPrecompIso I O (mk I O s d) =
      interpPrecompIsoStep I O s d (fun x ↦ interpPrecompIso I O (d x)) :=
  rec_mk I O (interpPrecompIsoStep I O) s d

/-- Postcomposing the values of a merged assignment commutes with the
merge, pointwise: case analysis on the classifier at each element. -/
theorem arrowSumMerge_map {B : Type uB} {X : Type uB}
    {Y Z : Type (max uA uB)} (c : ArrowSumClassifier.{uB, uB, uB} B X)
    (j : ArrowSumUnresolved c → Y) (h : Y → Z) (b : B) :
    Sum.map _root_.id h (arrowSumMerge c j b) = arrowSumMerge c (h ∘ j) b :=
  Sum.casesOn (motive := fun t ↦ c b = t →
      Sum.map _root_.id h (arrowSumMerge c j b) = arrowSumMerge c (h ∘ j) b)
    (c b)
    (fun x hx ↦
      (congrArg (Sum.map _root_.id h) (arrowSumMerge_eq c j b (Sum.inl x) hx)).trans
        (arrowSumMerge_eq c (h ∘ j) b (Sum.inl x) hx).symm)
    (fun u hu ↦
      (congrArg (Sum.map _root_.id h) (arrowSumMerge_eq c j b (Sum.inr u) hu)).trans
        (arrowSumMerge_eq c (h ∘ j) b (Sum.inr u) hu).symm)
    rfl

/-- `IR.interpMor` commutes with `FreeCoprodCompDisc.isoOfEq`
transport of names along an equality of direction assignments (the
`IR.interpMor_cast` companion at object-equality transports). -/
theorem interpMor_isoOfEq (B : Type uB)
    (c : (B → I) → IR.{max uA uB, uB, uI, uO} I O)
    (V W : FreeCoprodCompDisc.{max uA uB, uI} I)
    (pm : FreeCoprodCompDisc.Hom I V W) {m₀ m₁ : B → I} (e : m₀ = m₁)
    (u : (interpObj I O (c m₀) V).1) :
    (FreeCoprodCompDisc.isoOfEq O
        (congrArg (fun m ↦ interpObj I O (c m) W) e)).1
        ((interpMor I O (c m₀) V W pm).1 u) =
      (interpMor I O (c m₁) V W pm).1
        ((FreeCoprodCompDisc.isoOfEq O
          (congrArg (fun m ↦ interpObj I O (c m) V) e)).1 u) :=
  Eq.rec (motive := fun m' e' ↦
      (FreeCoprodCompDisc.isoOfEq O
          (congrArg (fun m ↦ interpObj I O (c m) W) e')).1
          ((interpMor I O (c m₀) V W pm).1 u) =
        (interpMor I O (c m') V W pm).1
          ((FreeCoprodCompDisc.isoOfEq O
            (congrArg (fun m ↦ interpObj I O (c m) V) e')).1 u))
    rfl e

/-- The motive of the commutation-proof elimination in
`IR.precompNatDeltaPair`: the domain decoding of the coproduct
morphism is generalized together with its commutation proof, and the
assignment equalities (whose types depend on it) are quantified
inside. -/
def PrecompNatDeltaPairMotive (B : Type uB)
    (c : (B → I) → IR.{max uA uB, uB, uI, uO} I O)
    (V1 : Type (max uA uB)) (W : FreeCoprodCompDisc.{max uA uB, uI} I)
    (p1 : V1 → W.1) (gx : B → V1) (m₀ : B → I)
    (v2 : V1 → I) (p2 : W.2 ∘ p1 = v2) : Prop :=
  ∀ (gy : B → W.1), p1 ∘ gx = gy →
    ∀ (eX : m₀ = v2 ∘ gx) (eY : m₀ = W.2 ∘ gy)
      (u : (interpObj I O (c m₀) ⟨V1, v2⟩).1),
    (⟨gy, (FreeCoprodCompDisc.isoOfEq O
        (congrArg (fun m ↦ interpObj I O (c m) W) eY)).1
        ((interpMor I O (c m₀) ⟨V1, v2⟩ W ⟨p1, p2⟩).1 u)⟩ :
      (interpObj I O (delta I O B c) W).1) =
    ⟨p1 ∘ gx,
      (FreeCoprodCompDisc.homOfEq O
          (congrArg (fun t ↦ interpObj I O (c (t ∘ gx)) W) p2.symm)
          (interpMor I O (c (v2 ∘ gx)) ⟨V1, v2⟩ W ⟨p1, p2⟩)).1
        ((FreeCoprodCompDisc.isoOfEq O
          (congrArg (fun m ↦ interpObj I O (c m) ⟨V1, v2⟩) eX)).1 u)⟩

/-- The motive of the reassembled-assignment elimination inside the
base case of `IR.precompNatDeltaPair`: the codomain-side assignment is
generalized together with its factoring through the coproduct
morphism, at the already-factored domain decoding (where the
`homOfEq` transport has reduced definitionally). -/
def PrecompNatDeltaPairInnerMotive (B : Type uB)
    (c : (B → I) → IR.{max uA uB, uB, uI, uO} I O)
    (V1 : Type (max uA uB)) (W : FreeCoprodCompDisc.{max uA uB, uI} I)
    (p1 : V1 → W.1) (gx : B → V1) (m₀ : B → I) (gy : B → W.1) : Prop :=
  ∀ (eX : m₀ = (W.2 ∘ p1) ∘ gx) (eY : m₀ = W.2 ∘ gy)
    (u : (interpObj I O (c m₀) ⟨V1, W.2 ∘ p1⟩).1),
  (⟨gy, (FreeCoprodCompDisc.isoOfEq O
      (congrArg (fun m ↦ interpObj I O (c m) W) eY)).1
      ((interpMor I O (c m₀) ⟨V1, W.2 ∘ p1⟩ W ⟨p1, rfl⟩).1 u)⟩ :
    (interpObj I O (delta I O B c) W).1) =
  ⟨p1 ∘ gx,
    (interpMor I O (c ((W.2 ∘ p1) ∘ gx)) ⟨V1, W.2 ∘ p1⟩ W ⟨p1, rfl⟩).1
      ((FreeCoprodCompDisc.isoOfEq O
        (congrArg (fun m ↦ interpObj I O (c m) ⟨V1, W.2 ∘ p1⟩) eX)).1 u)⟩

/-- The base case of both eliminations in `IR.precompNatDeltaPair`:
at the factored assignment `p1 ∘ gx`, the two assignment-equality
transports commute with the morphism map by `IR.interpMor_isoOfEq`
under the common first component. -/
theorem precompNatDeltaPair_inner (B : Type uB)
    (c : (B → I) → IR.{max uA uB, uB, uI, uO} I O)
    (V1 : Type (max uA uB)) (W : FreeCoprodCompDisc.{max uA uB, uI} I)
    (p1 : V1 → W.1) (gx : B → V1) (m₀ : B → I) :
    PrecompNatDeltaPairInnerMotive I O B c V1 W p1 gx m₀ (p1 ∘ gx) :=
  fun eX _ u ↦
    congrArg (fun t ↦ (⟨p1 ∘ gx, t⟩ : (interpObj I O (delta I O B c) W).1))
      (interpMor_isoOfEq I O B c ⟨V1, W.2 ∘ p1⟩ W ⟨p1, rfl⟩ eX u)

/-- The transport-commutation square of the `delta` case of the
naturality upgrade: relabeling a merged assignment on both sides of
the morphism map (by `FreeCoprodCompDisc.isoOfEq` at the domain and
codomain objects) agrees with the `homOfEq`-transported component of
`IR.interpMorDelta`, as elements of the direct `delta` interpretation
at the codomain. -/
theorem precompNatDeltaPair (B : Type uB)
    (c : (B → I) → IR.{max uA uB, uB, uI, uO} I O)
    (V1 : Type (max uA uB)) (W : FreeCoprodCompDisc.{max uA uB, uI} I)
    (p1 : V1 → W.1) (gx : B → V1) (m₀ : B → I)
    (v2 : V1 → I) (p2 : W.2 ∘ p1 = v2) :
    PrecompNatDeltaPairMotive I O B c V1 W p1 gx m₀ v2 p2 :=
  Eq.rec (motive := fun v2' p2' ↦
      PrecompNatDeltaPairMotive I O B c V1 W p1 gx m₀ v2' p2')
    (fun _gy e1 ↦
      Eq.rec (motive := fun gy' _ ↦
          PrecompNatDeltaPairInnerMotive I O B c V1 W p1 gx m₀ gy')
        (precompNatDeltaPair_inner I O B c V1 W p1 gx m₀) e1)
    p2

/-- The motive of the naturality upgrade of Lemma 4
([HancockMcBrideGhaniMalatestaAltenkirch2013]): for each code, at
every precomposition datum, the `IR.interpPrecompIso` family is
natural between the precomposed interpretation and the direct
interpretation at the coproduct object. -/
def PrecompNatMotive (γ : IR.{max uA uB, uB, uI, uO} I O) : Prop :=
  ∀ (Q : Type uB) (i : Q → I),
    FreeCoprodCompDisc.IsNatTrans I O
      (interpObj I O (precomp I O Q i γ)) (precompRhsMap I O Q i γ)
      (interpMor I O (precomp I O Q i γ)) (precompRhsMapMor I O Q i γ)
      (fun k ↦ FreeCoprodCompDisc.Iso.hom O (interpPrecompIso I O γ Q i k))

/-- The motive of the commutation-equality elimination in the
inductive step of the naturality upgrade: the domain decoding is
generalized together with the morphism's commutation proof, at the
`IR.interpPrecompIsoStep` form of the isomorphism family. -/
def PrecompNatMkMotive (s : Shape.{max uA uB, uB, uO} O)
    (d : Direction I O s → IR.{max uA uB, uB, uI, uO} I O)
    (Q : Type uB) (i : Q → I) (X1 : Type (max uA uB))
    (Y : FreeCoprodCompDisc.{max uA uB, uI} I) (h1 : X1 → Y.1)
    (x2 : X1 → I) (hcomm : Y.2 ∘ h1 = x2) : Prop :=
  FreeCoprodCompDisc.Hom.comp O
      (interpMor I O (precomp I O Q i (mk I O s d)) ⟨X1, x2⟩ Y ⟨h1, hcomm⟩)
      (FreeCoprodCompDisc.Iso.hom O
        (interpPrecompIsoStep I O s d
          (fun x ↦ interpPrecompIso I O (d x)) Q i Y)) =
    FreeCoprodCompDisc.Hom.comp O
      (FreeCoprodCompDisc.Iso.hom O
        (interpPrecompIsoStep I O s d
          (fun x ↦ interpPrecompIso I O (d x)) Q i ⟨X1, x2⟩))
      (interpMor I O (mk I O s d)
        (FreeCoprodCompDisc.plus I ⟨Q, i⟩ ⟨X1, x2⟩)
        (FreeCoprodCompDisc.plus I ⟨Q, i⟩ Y)
        (FreeCoprodCompDisc.coprodPairMor I
          (FreeCoprodCompDisc.Hom.id I ⟨Q, i⟩) ⟨h1, hcomm⟩))

/-- The `iota` case of the naturality upgrade: after the
characterizing equations, both legs of the square are identities on
the constant singleton interpretation. -/
theorem precompNat_mk_iota (o : O)
    (d : Direction I O (Sum.inl o : Shape.{max uA uB, uB, uO} O) →
      IR.{max uA uB, uB, uI, uO} I O)
    (Q : Type uB) (i : Q → I) (X1 : Type (max uA uB))
    (Y : FreeCoprodCompDisc.{max uA uB, uI} I) (h1 : X1 → Y.1) :
    PrecompNatMkMotive I O (Sum.inl o) d Q i X1 Y h1 (Y.2 ∘ h1) rfl :=
  (congrArg
      (fun (t : MorMapSig I O (iota I O o)) ↦
        FreeCoprodCompDisc.Hom.comp O (t ⟨X1, Y.2 ∘ h1⟩ Y ⟨h1, rfl⟩)
          (FreeCoprodCompDisc.Iso.hom O
            (interpPrecompIsoStep I O (Sum.inl o) d
              (fun x ↦ interpPrecompIso I O (d x)) Q i Y)))
      (interpMor_iota I O o)).trans
    (congrArg
      (fun (t : MorMapSig I O (mk I O (Sum.inl o) d)) ↦
        FreeCoprodCompDisc.Hom.comp O
          (FreeCoprodCompDisc.Iso.hom O
            (interpPrecompIsoStep I O (Sum.inl o) d
              (fun x ↦ interpPrecompIso I O (d x)) Q i ⟨X1, Y.2 ∘ h1⟩))
          (t (FreeCoprodCompDisc.plus I ⟨Q, i⟩ ⟨X1, Y.2 ∘ h1⟩)
            (FreeCoprodCompDisc.plus I ⟨Q, i⟩ Y)
            (FreeCoprodCompDisc.coprodPairMor I
              (FreeCoprodCompDisc.Hom.id I ⟨Q, i⟩) ⟨h1, rfl⟩)))
      (interpMor_mk I O (Sum.inl o) d).symm)

/-- The `sigma` case of the naturality upgrade: after the
characterizing equations, both paths around the square compute
componentwise, and each summand's square is the inductive hypothesis
at the summand's subcode. -/
theorem precompNat_mk_sigma (A : Type (max uA uB))
    (d : Direction I O (Sum.inr (Sum.inl A) : Shape.{max uA uB, uB, uO} O) →
      IR.{max uA uB, uB, uI, uO} I O)
    (ih : (x : Direction I O (Sum.inr (Sum.inl A) : Shape.{max uA uB, uB, uO} O)) →
      PrecompNatMotive I O (d x))
    (Q : Type uB) (i : Q → I) (X1 : Type (max uA uB))
    (Y : FreeCoprodCompDisc.{max uA uB, uI} I) (h1 : X1 → Y.1) :
    PrecompNatMkMotive I O (Sum.inr (Sum.inl A)) d Q i X1 Y h1 (Y.2 ∘ h1) rfl :=
  Subtype.ext (funext (fun p ↦
    ((congrArg
        (FreeCoprodCompDisc.Iso.hom O
          (interpPrecompIsoStep I O (Sum.inr (Sum.inl A)) d
            (fun x ↦ interpPrecompIso I O (d x)) Q i Y)).1
        (congrFun (congrArg Subtype.val
            (congrFun (congrFun (congrFun
              (interpMor_sigma I O (ULift.{uB} A)
                (fun a ↦ precomp I O Q i (d (ULift.up a.down))))
              ⟨X1, Y.2 ∘ h1⟩) Y) ⟨h1, rfl⟩))
          p)).trans
      (congrArg
        (fun t ↦ (⟨p.1.down, t⟩ :
          (interpObj I O (mk I O (Sum.inr (Sum.inl A)) d)
            (FreeCoprodCompDisc.plus I ⟨Q, i⟩ Y)).1))
        (congrFun (congrArg Subtype.val
            (ih (ULift.up p.1.down) Q i ⟨X1, Y.2 ∘ h1⟩ Y ⟨h1, rfl⟩))
          p.2))).trans
    (congrFun (congrArg Subtype.val
        (congrFun (congrFun (congrFun
          (interpMor_mk I O (Sum.inr (Sum.inl A)) d)
          (FreeCoprodCompDisc.plus I ⟨Q, i⟩ ⟨X1, Y.2 ∘ h1⟩))
          (FreeCoprodCompDisc.plus I ⟨Q, i⟩ Y))
          (FreeCoprodCompDisc.coprodPairMor I
            (FreeCoprodCompDisc.Hom.id I ⟨Q, i⟩) ⟨h1, rfl⟩)))
      ((FreeCoprodCompDisc.Iso.hom O
        (interpPrecompIsoStep I O (Sum.inr (Sum.inl A)) d
          (fun x ↦ interpPrecompIso I O (d x)) Q i ⟨X1, Y.2 ∘ h1⟩)).1 p)).symm))

/-- The `delta` case of the naturality upgrade: after the
characterizing equations, a name of the precomposed `delta`
interpretation is chased componentwise through both paths of the
square — the classifier component is preserved, the summand's square
is the inductive hypothesis at the merged assignment, and the
remaining transports commute by `IR.precompNatDeltaPair`. -/
theorem precompNat_mk_delta (B : Type uB)
    (d : Direction I O (Sum.inr (Sum.inr B) : Shape.{max uA uB, uB, uO} O) →
      IR.{max uA uB, uB, uI, uO} I O)
    (ih : (x : Direction I O (Sum.inr (Sum.inr B) : Shape.{max uA uB, uB, uO} O)) →
      PrecompNatMotive I O (d x))
    (Q : Type uB) (i : Q → I) (X1 : Type (max uA uB))
    (Y : FreeCoprodCompDisc.{max uA uB, uI} I) (h1 : X1 → Y.1) :
    PrecompNatMkMotive I O (Sum.inr (Sum.inr B)) d Q i X1 Y h1 (Y.2 ∘ h1) rfl :=
  Subtype.ext (funext (fun p ↦
    ((congrArg
        (FreeCoprodCompDisc.Iso.hom O
          (interpPrecompIsoStep I O (Sum.inr (Sum.inr B)) d
            (fun x ↦ interpPrecompIso I O (d x)) Q i Y)).1
        (congrFun (congrArg Subtype.val
            (congrFun (congrFun (congrFun
              (interpMor_sigma I O
                (ULift.{max uA uB} (ArrowSumClassifier.{uB, uB, uB} B Q))
                (fun cl ↦ delta I O (ArrowSumUnresolved cl.down)
                  (fun j ↦ precomp I O Q i
                    (d (ULift.up (precompMerge I Q i cl.down j))))))
              ⟨X1, Y.2 ∘ h1⟩) Y) ⟨h1, rfl⟩))
          p)).trans
      ((congrArg
          (fun t ↦ (FreeCoprodCompDisc.Iso.hom O
            (interpPrecompIsoStep I O (Sum.inr (Sum.inr B)) d
              (fun x ↦ interpPrecompIso I O (d x)) Q i Y)).1
            (⟨p.1, t⟩ :
              (interpObj I O
                (precomp I O Q i (mk I O (Sum.inr (Sum.inr B)) d)) Y).1))
          (congrFun (congrArg Subtype.val
              (congrFun (congrFun (congrFun
                (interpMor_delta I O (ArrowSumUnresolved p.1.down)
                  (fun j ↦ precomp I O Q i
                    (d (ULift.up (precompMerge I Q i p.1.down j)))))
                ⟨X1, Y.2 ∘ h1⟩) Y) ⟨h1, rfl⟩))
            p.2)).trans
        ((congrArg
            (fun t ↦ (⟨arrowSumMerge p.1.down (h1 ∘ p.2.1),
              (FreeCoprodCompDisc.isoOfEq O
                (congrArg
                  (fun m ↦ interpObj I O (d (ULift.up m))
                    (FreeCoprodCompDisc.plus I ⟨Q, i⟩ Y))
                  (precompMerge_elim I Q i Y B p.1.down (h1 ∘ p.2.1)))).1 t⟩ :
              (interpObj I O (mk I O (Sum.inr (Sum.inr B)) d)
                (FreeCoprodCompDisc.plus I ⟨Q, i⟩ Y)).1))
            (congrFun (congrArg Subtype.val
                (ih (ULift.up
                    (precompMerge I Q i p.1.down ((Y.2 ∘ h1) ∘ p.2.1))) Q i
                  ⟨X1, Y.2 ∘ h1⟩ Y ⟨h1, rfl⟩))
              p.2.2)).trans
          (precompNatDeltaPair I O B (fun m ↦ d (ULift.up m)) (Q ⊕ X1)
            (FreeCoprodCompDisc.plus I ⟨Q, i⟩ Y) (Sum.map _root_.id h1)
            (arrowSumMerge p.1.down p.2.1)
            (precompMerge I Q i p.1.down ((Y.2 ∘ h1) ∘ p.2.1))
            (Sum.elim i (Y.2 ∘ h1))
            (FreeCoprodCompDisc.coprodPairMor I
              (FreeCoprodCompDisc.Hom.id I ⟨Q, i⟩)
              (⟨h1, rfl⟩ :
                FreeCoprodCompDisc.Hom I ⟨X1, Y.2 ∘ h1⟩ Y)).2
            (arrowSumMerge p.1.down (h1 ∘ p.2.1))
            (funext (fun b ↦ arrowSumMerge_map p.1.down p.2.1 h1 b))
            (precompMerge_elim I Q i ⟨X1, Y.2 ∘ h1⟩ B p.1.down p.2.1)
            (precompMerge_elim I Q i Y B p.1.down (h1 ∘ p.2.1))
            ((FreeCoprodCompDisc.Iso.hom O
              (interpPrecompIso I O
                (d (ULift.up
                  (precompMerge I Q i p.1.down ((Y.2 ∘ h1) ∘ p.2.1)))) Q i
                ⟨X1, Y.2 ∘ h1⟩)).1 p.2.2))))).trans
    (congrFun (congrArg Subtype.val
        (congrFun (congrFun (congrFun
          (interpMor_mk I O (Sum.inr (Sum.inr B)) d)
          (FreeCoprodCompDisc.plus I ⟨Q, i⟩ ⟨X1, Y.2 ∘ h1⟩))
          (FreeCoprodCompDisc.plus I ⟨Q, i⟩ Y))
          (FreeCoprodCompDisc.coprodPairMor I
            (FreeCoprodCompDisc.Hom.id I ⟨Q, i⟩) ⟨h1, rfl⟩)))
      ((FreeCoprodCompDisc.Iso.hom O
        (interpPrecompIsoStep I O (Sum.inr (Sum.inr B)) d
          (fun x ↦ interpPrecompIso I O (d x)) Q i ⟨X1, Y.2 ∘ h1⟩)).1 p)).symm))

/-- The per-shape dispatch of the naturality upgrade's base case. -/
theorem precompNat_mk_base (s : Shape.{max uA uB, uB, uO} O)
    (d : Direction I O s → IR.{max uA uB, uB, uI, uO} I O)
    (ih : (x : Direction I O s) → PrecompNatMotive I O (d x))
    (Q : Type uB) (i : Q → I) (X1 : Type (max uA uB))
    (Y : FreeCoprodCompDisc.{max uA uB, uI} I) (h1 : X1 → Y.1) :
    PrecompNatMkMotive I O s d Q i X1 Y h1 (Y.2 ∘ h1) rfl :=
  match s, d, ih with
  | Sum.inl o, d, _ => precompNat_mk_iota I O o d Q i X1 Y h1
  | Sum.inr (Sum.inl A), d, ih => precompNat_mk_sigma I O A d ih Q i X1 Y h1
  | Sum.inr (Sum.inr B), d, ih => precompNat_mk_delta I O B d ih Q i X1 Y h1

/-- The inductive step of the naturality upgrade: rewrite the
isomorphism family by its characterizing equation
`IR.interpPrecompIso_mk`, eliminate the morphism's commutation
equality, and dispatch on the shape. -/
theorem interpPrecompIso_natural_step :
    InductionStep.{max uA uB, uB, uI, uO} I O (PrecompNatMotive I O) :=
  fun s d ih Q i X Y h ↦
    match X, h with
    | ⟨X1, x2⟩, ⟨h1, hcomm⟩ =>
      Eq.mpr
        (congrArg
          (fun t ↦ FreeCoprodCompDisc.Hom.comp O
              (interpMor I O (precomp I O Q i (mk I O s d)) ⟨X1, x2⟩ Y
                ⟨h1, hcomm⟩)
              (FreeCoprodCompDisc.Iso.hom O (t Q i Y)) =
            FreeCoprodCompDisc.Hom.comp O
              (FreeCoprodCompDisc.Iso.hom O (t Q i ⟨X1, x2⟩))
              (precompRhsMapMor I O Q i (mk I O s d) ⟨X1, x2⟩ Y ⟨h1, hcomm⟩))
          (interpPrecompIso_mk I O s d))
        (Eq.rec (motive := fun x2' hcomm' ↦
            PrecompNatMkMotive I O s d Q i X1 Y h1 x2' hcomm')
          (precompNat_mk_base I O s d ih Q i X1 Y h1) hcomm)

/-- Naturality of the Lemma 4 isomorphism family
([HancockMcBrideGhaniMalatestaAltenkirch2013]): at every code and
every precomposition datum, `IR.interpPrecompIso` is natural in the
interpreted object, between the precomposed interpretation and the
direct interpretation at the coproduct object. -/
theorem interpPrecompIso_natural (γ : IR.{max uA uB, uB, uI, uO} I O)
    (Q : Type uB) (i : Q → I) :
    FreeCoprodCompDisc.IsNatTrans I O
      (interpObj I O (precomp I O Q i γ)) (precompRhsMap I O Q i γ)
      (interpMor I O (precomp I O Q i γ)) (precompRhsMapMor I O Q i γ)
      (fun k ↦ FreeCoprodCompDisc.Iso.hom O (interpPrecompIso I O γ Q i k)) :=
  induction I O (PrecompNatMotive I O) (interpPrecompIso_natural_step I O)
    γ Q i

/-- The interpretation's cocone over the initial object: the image of
the unique morphism out of `∅` followed by the image of any morphism
is the image of the unique morphism. -/
theorem interpMor_emptyDesc_comp (γ' : IR.{max uA uB, uB, uI, uO} I O)
    (X Y : FreeCoprodCompDisc.{max uA uB, uI} I)
    (h : FreeCoprodCompDisc.Hom I X Y) :
    FreeCoprodCompDisc.Hom.comp O
        (interpMor I O γ' (FreeCoprodCompDisc.emptyObj I) X
          (FreeCoprodCompDisc.emptyDesc I X))
        (interpMor I O γ' X Y h) =
      interpMor I O γ' (FreeCoprodCompDisc.emptyObj I) Y
        (FreeCoprodCompDisc.emptyDesc I Y) :=
  (interpMor_comp I O γ' (FreeCoprodCompDisc.emptyObj I) X Y
      (FreeCoprodCompDisc.emptyDesc I X) h).symm.trans
    (congrArg (interpMor I O γ' (FreeCoprodCompDisc.emptyObj I) Y)
      (FreeCoprodCompDisc.emptyDesc_unique I Y
        (FreeCoprodCompDisc.Hom.comp I (FreeCoprodCompDisc.emptyDesc I X) h)))

/-- The backward direction of `IR.natIotaEquiv`: extend a morphism at
the initial object to a transformation by composing with the images of
the unique morphisms out of `∅`. -/
def natIotaInvFun (o : O) (γ' : IR.{max uA uB, uB, uI, uO} I O)
    (f : FreeCoprodCompDisc.Hom O
      (interpObj I O (iota.{max uA uB, uB, uI, uO} I O o) (FreeCoprodCompDisc.emptyObj I))
      (interpObj I O γ' (FreeCoprodCompDisc.emptyObj I))) :
    FreeCoprodCompDisc.NatTrans I O (interpObj I O (iota.{max uA uB, uB, uI, uO} I O o))
      (interpObj I O γ') (interpMor I O (iota.{max uA uB, uB, uI, uO} I O o)) (interpMor I O γ') :=
  ⟨fun X ↦ FreeCoprodCompDisc.Hom.comp O f
      (interpMor I O γ' (FreeCoprodCompDisc.emptyObj I) X
        (FreeCoprodCompDisc.emptyDesc I X)),
    fun X Y h ↦
      (congrArg
          (fun (t : MorMapSig I O (iota.{max uA uB, uB, uI, uO} I O o)) ↦
            FreeCoprodCompDisc.Hom.comp O (t X Y h)
              (FreeCoprodCompDisc.Hom.comp O f
                (interpMor I O γ' (FreeCoprodCompDisc.emptyObj I) Y
                  (FreeCoprodCompDisc.emptyDesc I Y))))
          (interpMor_iota.{max uA uB, uB, uI, uO} I O o)).trans
        ((congrArg (FreeCoprodCompDisc.Hom.comp O f)
            (interpMor_emptyDesc_comp I O γ' X Y h).symm).trans
          (FreeCoprodCompDisc.Hom.comp_assoc O f
            (interpMor I O γ' (FreeCoprodCompDisc.emptyObj I) X
              (FreeCoprodCompDisc.emptyDesc I X))
            (interpMor I O γ' X Y h)).symm)⟩

/-- The ∅-evaluation equivalence at an `iota` domain: transformations
out of the interpretation of `iota o` correspond to their components
at the initial object. -/
def natIotaEquiv (o : O) (γ' : IR.{max uA uB, uB, uI, uO} I O) :
    FreeCoprodCompDisc.NatTrans I O (interpObj I O (iota.{max uA uB, uB, uI, uO} I O o))
        (interpObj I O γ') (interpMor I O (iota.{max uA uB, uB, uI, uO} I O o)) (interpMor I O γ') ≃
      FreeCoprodCompDisc.Hom O
        (interpObj I O (iota.{max uA uB, uB, uI, uO} I O o) (FreeCoprodCompDisc.emptyObj I))
        (interpObj I O γ' (FreeCoprodCompDisc.emptyObj I)) :=
  { toFun := fun η ↦ η.1 (FreeCoprodCompDisc.emptyObj I),
    invFun := natIotaInvFun I O o γ',
    left_inv := fun η ↦ Subtype.ext (funext (fun X ↦
      (η.2 (FreeCoprodCompDisc.emptyObj I) X
          (FreeCoprodCompDisc.emptyDesc I X)).symm.trans
        (congrArg
          (fun (t : MorMapSig I O (iota.{max uA uB, uB, uI, uO} I O o)) ↦
            FreeCoprodCompDisc.Hom.comp O
              (t (FreeCoprodCompDisc.emptyObj I) X
                (FreeCoprodCompDisc.emptyDesc I X))
              (η.1 X))
          (interpMor_iota.{max uA uB, uB, uI, uO} I O o)))),
    right_inv := fun f ↦
      (congrArg
          (fun t ↦ FreeCoprodCompDisc.Hom.comp O f
            (interpMor I O γ' (FreeCoprodCompDisc.emptyObj I)
              (FreeCoprodCompDisc.emptyObj I) t))
          (FreeCoprodCompDisc.emptyDesc_unique I
            (FreeCoprodCompDisc.emptyObj I)
            (FreeCoprodCompDisc.Hom.id I
              (FreeCoprodCompDisc.emptyObj I))).symm).trans
        ((congrArg (FreeCoprodCompDisc.Hom.comp O f)
            (interpMor_id I O γ' (FreeCoprodCompDisc.emptyObj I))).trans
          (FreeCoprodCompDisc.Hom.comp_id O f)) }

/-- The motive of `IR.innerHomEquiv`: the homset from an `ι`-code to a
code is the fiber, over the index, of the decoding of the code's
interpretation at the initial object. -/
def InnerHomEquivMotive (o : O) (γ' : IR.{max uA uB, uB, uI, uO} I O) :
    Type (max uA uB uI) :=
  InnerHom.{uA, uB, uI, uO} I O o γ' ≃
    {z : (interpObj I O γ' (FreeCoprodCompDisc.emptyObj I)).1 //
      (interpObj I O γ' (FreeCoprodCompDisc.emptyObj I)).2 z = o}

/-- Transport the fiber equivalence of a `δ`-subcode along an equality
of direction assignments, keeping the equivalence's source at the
original assignment. -/
def innerHomEquivCast (o : O) (B : Type uB)
    (c : ULift.{max uA uB} (B → I) → IR.{max uA uB, uB, uI, uO} I O)
    (m : (x : ULift.{max uA uB} (B → I)) → InnerHomEquivMotive I O o (c x))
    (i j : B → I) (e : i = j) :
    InnerHom.{uA, uB, uI, uO} I O o (c (ULift.up i)) ≃
      {n : (interpObj I O (c (ULift.up j)) (FreeCoprodCompDisc.emptyObj I)).1 //
        (interpObj I O (c (ULift.up j)) (FreeCoprodCompDisc.emptyObj I)).2 n = o} :=
  Eq.rec (motive := fun j' _ ↦
      InnerHom.{uA, uB, uI, uO} I O o (c (ULift.up i)) ≃
        {n : (interpObj I O (c (ULift.up j'))
            (FreeCoprodCompDisc.emptyObj I)).1 //
          (interpObj I O (c (ULift.up j'))
            (FreeCoprodCompDisc.emptyObj I)).2 n = o})
    (m (ULift.up i)) e

/-- The step of `IR.innerHomEquiv`: per shape, the homset clause and
the ∅-fiber of the interpretation are matched componentwise, with the
inductive hypotheses supplying the subcode equivalences. -/
def innerHomEquivStep (o : O) :
    RecStep.{max uA uB, uB, uI, uO, max uA uB uI} I O
      (InnerHomEquivMotive I O o) :=
  fun s c m ↦ match s, c, m with
  | Sum.inl _, _, _ =>
      { toFun := fun h ↦ ⟨ULift.up Unit.unit, h.down.down.symm⟩,
        invFun := fun z ↦ ULift.up (PLift.up z.2.symm),
        left_inv := fun _ ↦ rfl,
        right_inv := fun _ ↦ rfl }
  | Sum.inr (Sum.inl _), c, m =>
      (sigmaCongrRight' (fun a ↦ m (ULift.up a))).trans
        (sigmaSubtypeEquiv
          (fun a ↦
            (interpObj I O (c (ULift.up a))
              (FreeCoprodCompDisc.emptyObj I)).1)
          (fun a n ↦
            (interpObj I O (c (ULift.up a))
              (FreeCoprodCompDisc.emptyObj I)).2 n = o))
  | Sum.inr (Sum.inr B), c, m =>
      (sigmaCongrRight' (fun (e : B → PEmpty.{1}) ↦
          innerHomEquivCast I O o B c m (fun b ↦ (e b).elim)
            ((FreeCoprodCompDisc.emptyObj I).2 ∘ (fun b ↦ (e b).elim))
            (funext (fun b ↦ (e b).elim)))).trans
        ((Equiv.sigmaCongrLeft
            (β := fun g ↦
              {n : (interpObj I O
                  (c (ULift.up ((FreeCoprodCompDisc.emptyObj I).2 ∘ g)))
                  (FreeCoprodCompDisc.emptyObj I)).1 //
                (interpObj I O
                  (c (ULift.up ((FreeCoprodCompDisc.emptyObj I).2 ∘ g)))
                  (FreeCoprodCompDisc.emptyObj I)).2 n = o})
            (arrowPEmptyEquiv.{0, max uA uB, uB} B)).trans
          (sigmaSubtypeEquiv
            (fun g ↦
              (interpObj I O
                (c (ULift.up ((FreeCoprodCompDisc.emptyObj I).2 ∘ g)))
                (FreeCoprodCompDisc.emptyObj I)).1)
            (fun g n ↦
              (interpObj I O
                (c (ULift.up ((FreeCoprodCompDisc.emptyObj I).2 ∘ g)))
                (FreeCoprodCompDisc.emptyObj I)).2 n = o)))

/-- The homset from an `ι`-code to a code is the fiber, over the
index, of the decoding of the code's interpretation at the initial
object, by `IR.rec` on the code. -/
def innerHomEquiv (o : O) (γ' : IR.{max uA uB, uB, uI, uO} I O) :
    InnerHom.{uA, uB, uI, uO} I O o γ' ≃
      {z : (interpObj I O γ' (FreeCoprodCompDisc.emptyObj I)).1 //
        (interpObj I O γ' (FreeCoprodCompDisc.emptyObj I)).2 z = o} :=
  rec I O (motive := InnerHomEquivMotive I O o) (innerHomEquivStep I O o) γ'

/-- The bridge from the lifted-summand binary coproduct to the direct
one: lower the left names, keep the right names. -/
def plusLiftBridgeHom (Q : Type uB) (i : Q → I)
    (X : FreeCoprodCompDisc.{max uA uB, uI} I) :
    FreeCoprodCompDisc.Hom I
      (FreeCoprodCompDisc.plus I
        (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Q, i⟩) X)
      (FreeCoprodCompDisc.plus I ⟨Q, i⟩ X) :=
  ⟨Sum.map ULift.down _root_.id,
    funext (fun s ↦ Sum.casesOn s (fun _ ↦ rfl) (fun _ ↦ rfl))⟩

/-- The bridge from the direct binary coproduct to the lifted-summand
one: raise the left names, keep the right names. -/
def plusLiftBridgeInvHom (Q : Type uB) (i : Q → I)
    (X : FreeCoprodCompDisc.{max uA uB, uI} I) :
    FreeCoprodCompDisc.Hom I (FreeCoprodCompDisc.plus I ⟨Q, i⟩ X)
      (FreeCoprodCompDisc.plus I
        (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Q, i⟩) X) :=
  ⟨Sum.map ULift.up _root_.id,
    funext (fun s ↦ Sum.casesOn s (fun _ ↦ rfl) (fun _ ↦ rfl))⟩

/-- The forward bridge followed by the backward bridge is the
identity. -/
theorem plusLiftBridge_hom_invHom (Q : Type uB) (i : Q → I)
    (X : FreeCoprodCompDisc.{max uA uB, uI} I) :
    FreeCoprodCompDisc.Hom.comp I (plusLiftBridgeHom I Q i X)
        (plusLiftBridgeInvHom I Q i X) =
      FreeCoprodCompDisc.Hom.id I
        (FreeCoprodCompDisc.plus I
          (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Q, i⟩) X) :=
  Subtype.ext (funext (fun s ↦ Sum.casesOn s (fun _ ↦ rfl) (fun _ ↦ rfl)))

/-- The backward bridge followed by the forward bridge is the
identity. -/
theorem plusLiftBridge_invHom_hom (Q : Type uB) (i : Q → I)
    (X : FreeCoprodCompDisc.{max uA uB, uI} I) :
    FreeCoprodCompDisc.Hom.comp I (plusLiftBridgeInvHom I Q i X)
        (plusLiftBridgeHom I Q i X) =
      FreeCoprodCompDisc.Hom.id I (FreeCoprodCompDisc.plus I ⟨Q, i⟩ X) :=
  Subtype.ext (funext (fun s ↦ Sum.casesOn s (fun _ ↦ rfl) (fun _ ↦ rfl)))

/-- The forward bridge is natural in the right summand. -/
theorem plusLiftBridge_square (Q : Type uB) (i : Q → I)
    (X Y : FreeCoprodCompDisc.{max uA uB, uI} I)
    (h : FreeCoprodCompDisc.Hom I X Y) :
    FreeCoprodCompDisc.Hom.comp I
        (FreeCoprodCompDisc.coprodPairMor I
          (FreeCoprodCompDisc.Hom.id I
            (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Q, i⟩)) h)
        (plusLiftBridgeHom I Q i Y) =
      FreeCoprodCompDisc.Hom.comp I (plusLiftBridgeHom I Q i X)
        (FreeCoprodCompDisc.coprodPairMor I
          (FreeCoprodCompDisc.Hom.id I ⟨Q, i⟩) h) :=
  Subtype.ext (funext (fun s ↦ Sum.casesOn s (fun _ ↦ rfl) (fun _ ↦ rfl)))

/-- The backward bridge is natural in the right summand. -/
theorem plusLiftBridge_square_inv (Q : Type uB) (i : Q → I)
    (X Y : FreeCoprodCompDisc.{max uA uB, uI} I)
    (h : FreeCoprodCompDisc.Hom I X Y) :
    FreeCoprodCompDisc.Hom.comp I
        (FreeCoprodCompDisc.coprodPairMor I
          (FreeCoprodCompDisc.Hom.id I ⟨Q, i⟩) h)
        (plusLiftBridgeInvHom I Q i Y) =
      FreeCoprodCompDisc.Hom.comp I (plusLiftBridgeInvHom I Q i X)
        (FreeCoprodCompDisc.coprodPairMor I
          (FreeCoprodCompDisc.Hom.id I
            (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Q, i⟩)) h) :=
  Subtype.ext (funext (fun s ↦ Sum.casesOn s (fun _ ↦ rfl) (fun _ ↦ rfl)))

/-- The interpretation's image of the forward bridge, as a natural
transformation from the `plus`-precomposed interpretation at the
lifted summand to the Lemma 4 right-hand map. -/
def plusLiftBridgeNat (Q : Type uB) (i : Q → I)
    (γ' : IR.{max uA uB, uB, uI, uO} I O) :
    FreeCoprodCompDisc.NatTrans I O
      (FreeCoprodCompDisc.mapComp
        (FreeCoprodCompDisc.plusMap
          (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Q, i⟩))
        (interpObj I O γ'))
      (precompRhsMap I O Q i γ')
      (FreeCoprodCompDisc.mapMorComp
        (FreeCoprodCompDisc.plusMapMor
          (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Q, i⟩))
        (interpMor I O γ'))
      (precompRhsMapMor I O Q i γ') :=
  ⟨fun X ↦ interpMor I O γ'
      (FreeCoprodCompDisc.plus I
        (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Q, i⟩) X)
      (FreeCoprodCompDisc.plus I ⟨Q, i⟩ X)
      (plusLiftBridgeHom I Q i X),
    fun X Y h ↦
      (interpMor_comp I O γ'
          (FreeCoprodCompDisc.plus I
            (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Q, i⟩) X)
          (FreeCoprodCompDisc.plus I
            (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Q, i⟩) Y)
          (FreeCoprodCompDisc.plus I ⟨Q, i⟩ Y)
          (FreeCoprodCompDisc.coprodPairMor I
            (FreeCoprodCompDisc.Hom.id I
              (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Q, i⟩)) h)
          (plusLiftBridgeHom I Q i Y)).symm.trans
        ((congrArg
            (interpMor I O γ'
              (FreeCoprodCompDisc.plus I
                (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Q, i⟩) X)
              (FreeCoprodCompDisc.plus I ⟨Q, i⟩ Y))
            (plusLiftBridge_square I Q i X Y h)).trans
          (interpMor_comp I O γ'
            (FreeCoprodCompDisc.plus I
              (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Q, i⟩) X)
            (FreeCoprodCompDisc.plus I ⟨Q, i⟩ X)
            (FreeCoprodCompDisc.plus I ⟨Q, i⟩ Y)
            (plusLiftBridgeHom I Q i X)
            (FreeCoprodCompDisc.coprodPairMor I
              (FreeCoprodCompDisc.Hom.id I ⟨Q, i⟩) h)))⟩

/-- The interpretation's image of the backward bridge, as a natural
transformation from the Lemma 4 right-hand map to the
`plus`-precomposed interpretation at the lifted summand. -/
def plusLiftBridgeNatInv (Q : Type uB) (i : Q → I)
    (γ' : IR.{max uA uB, uB, uI, uO} I O) :
    FreeCoprodCompDisc.NatTrans I O (precompRhsMap I O Q i γ')
      (FreeCoprodCompDisc.mapComp
        (FreeCoprodCompDisc.plusMap
          (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Q, i⟩))
        (interpObj I O γ'))
      (precompRhsMapMor I O Q i γ')
      (FreeCoprodCompDisc.mapMorComp
        (FreeCoprodCompDisc.plusMapMor
          (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Q, i⟩))
        (interpMor I O γ')) :=
  ⟨fun X ↦ interpMor I O γ' (FreeCoprodCompDisc.plus I ⟨Q, i⟩ X)
      (FreeCoprodCompDisc.plus I
        (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Q, i⟩) X)
      (plusLiftBridgeInvHom I Q i X),
    fun X Y h ↦
      (interpMor_comp I O γ' (FreeCoprodCompDisc.plus I ⟨Q, i⟩ X)
          (FreeCoprodCompDisc.plus I ⟨Q, i⟩ Y)
          (FreeCoprodCompDisc.plus I
            (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Q, i⟩) Y)
          (FreeCoprodCompDisc.coprodPairMor I
            (FreeCoprodCompDisc.Hom.id I ⟨Q, i⟩) h)
          (plusLiftBridgeInvHom I Q i Y)).symm.trans
        ((congrArg
            (interpMor I O γ' (FreeCoprodCompDisc.plus I ⟨Q, i⟩ X)
              (FreeCoprodCompDisc.plus I
                (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Q, i⟩) Y))
            (plusLiftBridge_square_inv I Q i X Y h)).trans
          (interpMor_comp I O γ' (FreeCoprodCompDisc.plus I ⟨Q, i⟩ X)
            (FreeCoprodCompDisc.plus I
              (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Q, i⟩) X)
            (FreeCoprodCompDisc.plus I
              (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Q, i⟩) Y)
            (plusLiftBridgeInvHom I Q i X)
            (FreeCoprodCompDisc.coprodPairMor I
              (FreeCoprodCompDisc.Hom.id I
                (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Q, i⟩))
              h)))⟩

/-- The two bridge transformations are inverse. -/
theorem plusLiftBridgeNat_isInverse (Q : Type uB) (i : Q → I)
    (γ' : IR.{max uA uB, uB, uI, uO} I O) :
    FreeCoprodCompDisc.NatTrans.IsInverse (plusLiftBridgeNat I O Q i γ')
      (plusLiftBridgeNatInv I O Q i γ') :=
  ⟨Subtype.ext (funext (fun X ↦
      (interpMor_comp I O γ'
          (FreeCoprodCompDisc.plus I
            (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Q, i⟩) X)
          (FreeCoprodCompDisc.plus I ⟨Q, i⟩ X)
          (FreeCoprodCompDisc.plus I
            (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Q, i⟩) X)
          (plusLiftBridgeHom I Q i X)
          (plusLiftBridgeInvHom I Q i X)).symm.trans
        ((congrArg
            (interpMor I O γ'
              (FreeCoprodCompDisc.plus I
                (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Q, i⟩) X)
              (FreeCoprodCompDisc.plus I
                (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Q, i⟩) X))
            (plusLiftBridge_hom_invHom I Q i X)).trans
          (interpMor_id I O γ'
            (FreeCoprodCompDisc.plus I
              (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Q, i⟩) X))))),
    Subtype.ext (funext (fun X ↦
      (interpMor_comp I O γ' (FreeCoprodCompDisc.plus I ⟨Q, i⟩ X)
          (FreeCoprodCompDisc.plus I
            (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Q, i⟩) X)
          (FreeCoprodCompDisc.plus I ⟨Q, i⟩ X)
          (plusLiftBridgeInvHom I Q i X)
          (plusLiftBridgeHom I Q i X)).symm.trans
        ((congrArg
            (interpMor I O γ' (FreeCoprodCompDisc.plus I ⟨Q, i⟩ X)
              (FreeCoprodCompDisc.plus I ⟨Q, i⟩ X))
            (plusLiftBridge_invHom_hom I Q i X)).trans
          (interpMor_id I O γ'
            (FreeCoprodCompDisc.plus I ⟨Q, i⟩ X)))))⟩

/-- The motive of `IR.interpHomEquiv`: for each code, the homset to
every codomain code is equivalent to the space of natural
transformations between the interpretations. -/
def InterpHomEquivMotive (γ : IR.{max uA uB, uB, uI, uO} I O) :
    Type (max (max uA uB + 1) uI uO) :=
  (γ' : IR.{max uA uB, uB, uI, uO} I O) →
    Hom.{uA, uB, uI, uO} I O γ γ' ≃
      FreeCoprodCompDisc.NatTrans I O (interpObj I O γ) (interpObj I O γ')
        (interpMor I O γ) (interpMor I O γ')

/-- The step of `IR.interpHomEquiv`: per shape, the homset clause and
the transformation space are matched by the corresponding
decomposition equivalence, with the inductive hypotheses supplying the
subcode equivalences. -/
def interpHomEquivStep :
    RecStep.{max uA uB, uB, uI, uO, max (max uA uB + 1) uI uO} I O
      (InterpHomEquivMotive I O) :=
  fun s c m ↦ match s, c, m with
  | Sum.inl o, c, _ => fun γ' ↦
      Eq.rec (motive := fun ir _ ↦
          InnerHom.{uA, uB, uI, uO} I O o γ' ≃
            FreeCoprodCompDisc.NatTrans I O (interpObj I O ir)
              (interpObj I O γ') (interpMor I O ir) (interpMor I O γ'))
        ((innerHomEquiv I O o γ').trans
          ((FreeCoprodCompDisc.homSingletonEquiv O o
              (interpObj I O γ' (FreeCoprodCompDisc.emptyObj I))).symm.trans
            (natIotaEquiv I O o γ').symm))
        (mk_congr I O (Sum.inl o) (funext (fun x ↦ nomatch x)) :
          mk I O (Sum.inl o) c = iota.{max uA uB, uB, uI, uO} I O o).symm
  | Sum.inr (Sum.inl A), c, m => fun γ' ↦
      (Equiv.piCongrRight (fun a ↦ m (ULift.up a) γ')).trans
        ((FreeCoprodCompDisc.natCoprodEquiv A
            (fun a ↦ interpObj I O (c (ULift.up a)))
            (fun a ↦ interpMor I O (c (ULift.up a)))
            (interpObj I O γ') (interpMor I O γ')).symm.trans
          (FreeCoprodCompDisc.NatTrans.congrSource
            (interpMor_sigma I O A (fun a ↦ c (ULift.up a)))
            (interpMor I O γ')).symm)
  | Sum.inr (Sum.inr Q), c, m => fun γ' ↦
      (Equiv.piCongrRight (fun i ↦
          (((m (ULift.up i) (precomp I O Q i γ')).trans
            (FreeCoprodCompDisc.NatTrans.equivOfInverseTarget
              (FreeCoprodCompDisc.NatTrans.ofIsoFamily
                (fun k ↦ interpPrecompIso I O γ' Q i k)
                (interpPrecompIso_natural I O γ' Q i))
              (FreeCoprodCompDisc.NatTrans.invOfIsoFamily
                (fun k ↦ interpPrecompIso I O γ' Q i k)
                (interpPrecompIso_natural I O γ' Q i))
              (FreeCoprodCompDisc.NatTrans.ofIsoFamily_isInverse
                (fun k ↦ interpPrecompIso I O γ' Q i k)
                (interpPrecompIso_natural I O γ' Q i)))).trans
            (FreeCoprodCompDisc.NatTrans.equivOfInverseTarget
              (plusLiftBridgeNatInv I O Q i γ')
              (plusLiftBridgeNat I O Q i γ')
              ⟨(plusLiftBridgeNat_isInverse I O Q i γ').2,
                (plusLiftBridgeNat_isInverse I O Q i γ').1⟩)).trans
            (FreeCoprodCompDisc.natCopowerPlusEquiv
              (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Q, i⟩)
              (interpMor I O (c (ULift.up i))) (interpMor I O γ')
              (interpMor_id I O (c (ULift.up i)))
              (interpMor_comp I O (c (ULift.up i)))
              (interpMor_id I O γ') (interpMor_comp I O γ')).symm)).trans
        (natDeltaEquiv I O Q (fun i ↦ c (ULift.up i)) (interpMor I O γ')).symm

/-- Theorem 3 of [HancockMcBrideGhaniMalatestaAltenkirch2013]: the
homset between two codes is equivalent to the space of natural
transformations between their interpretations, by `IR.rec` on the
domain code. -/
def interpHomEquiv (γ γ' : IR.{max uA uB, uB, uI, uO} I O) :
    Hom.{uA, uB, uI, uO} I O γ γ' ≃
      FreeCoprodCompDisc.NatTrans I O (interpObj I O γ) (interpObj I O γ')
        (interpMor I O γ) (interpMor I O γ') :=
  rec I O (interpHomEquivStep I O) γ γ'

/-- The interpretation of a code morphism as a natural transformation
(the forward direction of `IR.interpHomEquiv`). -/
def interpHom (γ γ' : IR.{max uA uB, uB, uI, uO} I O)
    (f : Hom.{uA, uB, uI, uO} I O γ γ') :
    FreeCoprodCompDisc.NatTrans I O (interpObj I O γ) (interpObj I O γ')
      (interpMor I O γ) (interpMor I O γ') :=
  interpHomEquiv I O γ γ' f

/-- The code morphism carried by a natural transformation between
interpretations (the backward direction of `IR.interpHomEquiv`). -/
def natToHom (γ γ' : IR.{max uA uB, uB, uI, uO} I O)
    (η : FreeCoprodCompDisc.NatTrans I O (interpObj I O γ)
      (interpObj I O γ') (interpMor I O γ) (interpMor I O γ')) :
    Hom.{uA, uB, uI, uO} I O γ γ' :=
  (interpHomEquiv I O γ γ').symm η

/-- `IR.interpHom` inverts `IR.natToHom`. -/
theorem interpHom_natToHom (γ γ' : IR.{max uA uB, uB, uI, uO} I O)
    (η : FreeCoprodCompDisc.NatTrans I O (interpObj I O γ)
      (interpObj I O γ') (interpMor I O γ) (interpMor I O γ')) :
    interpHom I O γ γ' (natToHom I O γ γ' η) = η :=
  Equiv.apply_symm_apply (interpHomEquiv I O γ γ') η

/-- `IR.natToHom` inverts `IR.interpHom`. -/
theorem natToHom_interpHom (γ γ' : IR.{max uA uB, uB, uI, uO} I O)
    (f : Hom.{uA, uB, uI, uO} I O γ γ') :
    natToHom I O γ γ' (interpHom I O γ γ' f) = f :=
  Equiv.symm_apply_apply (interpHomEquiv I O γ γ') f

end IR

end IndRec
