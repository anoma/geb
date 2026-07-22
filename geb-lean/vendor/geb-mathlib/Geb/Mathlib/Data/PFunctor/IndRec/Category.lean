/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.Data.PFunctor.IndRec.Naturality

/-!
# The category of IR codes

Corollary 2 of [HancockMcBrideGhaniMalatestaAltenkirch2013]: `IR`
codes and the homsets of Definition 8 form a category. Composition
is transferred through the full-and-faithful interpretation of
Theorem 3 — the code morphism carried by the vertical composite of
the interpreted transformations — and the category laws follow from
the vertical laws together with the round-trip laws of the Theorem 3
equivalence. The identity laws additionally consume the
identity-image equation `IR.interpHom_id`, proved by induction on
the domain code over the stack of `IR.preUnitStack`, against the
semantic counterpart of that stack: an iterated coproduct tower with
its iterated Lemma 4 isomorphism.

## Main definitions

* `IR.mplus`, `IR.mplusInj`, `IR.mplusMorMap` — the iterated
  coproduct object of a stack of superscripts, its iterated
  injection, and its action on morphisms.
* `IR.mprecompIso` — the iterated Lemma 4 isomorphism between the
  interpretation of an iterated precomposition and the
  interpretation at `IR.mplus`.
* `IR.preUnitComponent` — the semantic pre-unit component: the
  interpretation image of `IR.mplusInj`, composed with the inverse
  of `IR.mprecompIso`.
* `IR.interpHomDeltaSummand` — the per-summand transport of the
  `δ`-domain case of `IR.interpHomEquiv`.
* `IR.interpHomIotaComposite`, `IR.interpHomIotaCast` — the
  `ι`-branch equivalence of the Theorem 3 step and its transport
  along a code equality.
* `IR.deltaEmptyWeight`, `IR.deltaEmptyInj` — the canonical weight
  out of the lift of an empty-witnessed family, and the semantic
  inclusion of the empty-witnessed summand into the `δ`
  interpretation.
* `IR.deltaEmptySummandHom` — the transported summand isomorphism
  of the Lemma 4 `δ`-square at that inclusion.
* `IR.navWeight`, `IR.navReindex` — the tower navigation weight,
  and the reindexing of a lifted direction family along the
  inclusion of the all-unresolved classifier's subtype.
* `IR.navInj` — the tower-conjugated navigation inclusion.
* `IR.navBridgeMor` — the tower morphism induced by a weight at a
  right-appended superscript.
* `IR.comp` — composition of code morphisms: the code morphism
  carried by the vertical composite of the interpreted
  transformations.

## Main statements

* `IR.mprecompIso_natural` — naturality of the tower isomorphism in
  the interpreted object.
* `IR.interpHom_sigmaPush` — `IR.interpHom` sends `IR.sigmaPush` to
  composition with the semantic `σ`-injection.
* `IR.interpHom_deltaEmptyPush` — `IR.interpHom` sends
  `IR.deltaEmptyPush` to composition with the semantic
  empty-summand inclusion.
* `IR.interpHom_msigmaPush`, `IR.interpHom_deltaNav` —
  `IR.interpHom` sends the stack `σ`-push and the tower navigation
  to composition with the corresponding semantic inclusion.
* `IR.interpHom_preUnitStack` — `IR.interpHom` sends
  `IR.preUnitStack` to the semantic pre-unit component, by
  `IR.induction` on the domain code.
* `IR.interpHom_comp`, `IR.interpHom_id` — `IR.interpHom` sends
  `IR.comp` to the vertical composite and `IR.id` to the identity
  transformation: the interpretation is functorial on morphisms.
* `IR.id_comp`, `IR.comp_id`, `IR.comp_assoc` — the category laws
  of Corollary 2 of [HancockMcBrideGhaniMalatestaAltenkirch2013].

## Implementation notes

The tower constructions recurse on the stack through `List.rec`, not
on codes; the snoc lemmas are the corresponding `List.rec`
inductions, with the motive quantified over the code where the
recursion changes it (`IR.mprecompIso` and its snoc lemmas). Object
equalities entering the tower (`IR.mplus_snoc`, `IR.mprecomp_snoc`)
are carried as `FreeCoprodCompDisc.isoOfEq` transports and commuted
across the Lemma 4 isomorphism by elimination of the generalized
equality.

## References

* [HancockMcBrideGhaniMalatestaAltenkirch2013]

## Tags

inductive-recursive, morphism, category
-/

@[expose] public section

universe u uA uB uI uO

namespace IndRec

open CategoryTheory

variable (I : Type uI) (O : Type uO)

namespace IR

/-! ### The semantic tower -/

/-- The iterated coproduct object: fold `plus` over the stack. -/
def mplus (L : List (SupObj.{uB, uI} I)) (X : FreeCoprodCompDisc.{max uA uB, uI} I) :
    FreeCoprodCompDisc.{max uA uB, uI} I :=
  L.rec X (fun b _L ih ↦ FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b ih)

/-- `mplus` at a right-appended superscript feeds the coproduct at the
inner position. -/
theorem mplus_snoc (L : List (SupObj.{uB, uI} I)) (b : SupObj.{uB, uI} I)
    (X : FreeCoprodCompDisc.{max uA uB, uI} I) :
    mplus.{uA, uB, uI} I (L ++ [b]) X =
      mplus.{uA, uB, uI} I L (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b X) :=
  L.rec (motive := fun L ↦ mplus.{uA, uB, uI} I (L ++ [b]) X =
      mplus.{uA, uB, uI} I L (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b X))
    rfl
    (fun a _L ih ↦ congrArg (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I a) ih)

/-- The iterated right injection into `mplus`. -/
def mplusInj (L : List (SupObj.{uB, uI} I)) (X : FreeCoprodCompDisc.{max uA uB, uI} I) :
    FreeCoprodCompDisc.Hom I X (mplus.{uA, uB, uI} I L X) :=
  L.rec (motive := fun L ↦ FreeCoprodCompDisc.Hom I X (mplus.{uA, uB, uI} I L X))
    (FreeCoprodCompDisc.Hom.id I X)
    (fun b _L ih ↦ FreeCoprodCompDisc.Hom.comp I ih
      (FreeCoprodCompDisc.coprodPairInr I b (mplus.{uA, uB, uI} I _L X)))

/-- The iterated Lemma 4 isomorphism between the interpretation of an
iterated precomposition and the interpretation at `mplus`. -/
def mprecompIso (L : List (SupObj.{uB, uI} I)) :
    ∀ (γ : IR.{max uA uB, uB, uI, uO} I O) (X : FreeCoprodCompDisc.{max uA uB, uI} I),
      FreeCoprodCompDisc.Iso O (interpObj I O (mprecomp I O L γ) X)
        (interpObj I O γ (mplus.{uA, uB, uI} I L X)) :=
  L.rec (motive := fun L ↦ ∀ γ X,
      FreeCoprodCompDisc.Iso O (interpObj I O (mprecomp I O L γ) X)
        (interpObj I O γ (mplus.{uA, uB, uI} I L X)))
    (fun γ X ↦ FreeCoprodCompDisc.Iso.refl O (interpObj I O γ X))
    (fun b _L ih γ X ↦
      FreeCoprodCompDisc.Iso.trans O (ih (precomp I O b.1 b.2 γ) X)
        (interpPrecompIso I O γ b.1 b.2 (mplus.{uA, uB, uI} I _L X)))

/-- The semantic pre-unit component: the interpretation image of the
iterated injection, composed with the inverse of the iterated Lemma 4
isomorphism. -/
def preUnitComponent (γ : IR.{max uA uB, uB, uI, uO} I O)
    (L : List (SupObj.{uB, uI} I)) (X : FreeCoprodCompDisc.{max uA uB, uI} I) :
    FreeCoprodCompDisc.Hom O (interpObj I O γ X)
      (interpObj I O (mprecomp I O L γ) X) :=
  FreeCoprodCompDisc.Hom.comp O
    (interpMor I O γ X (mplus.{uA, uB, uI} I L X) (mplusInj.{uA, uB, uI} I L X))
    (FreeCoprodCompDisc.Iso.invHom O (mprecompIso.{uA, uB, uI, uO} I O L γ X))

/-- At the empty stack the semantic pre-unit component is the
identity. -/
theorem preUnitComponent_nil (γ : IR.{max uA uB, uB, uI, uO} I O)
    (X : FreeCoprodCompDisc.{max uA uB, uI} I) :
    preUnitComponent I O γ [] X = FreeCoprodCompDisc.Hom.id O (interpObj I O γ X) :=
  (congrArg (fun t ↦ FreeCoprodCompDisc.Hom.comp O t
      (FreeCoprodCompDisc.Iso.invHom O (mprecompIso.{uA, uB, uI, uO} I O [] γ X)))
    (interpMor_id I O γ X)).trans
    (FreeCoprodCompDisc.Hom.id_comp O
      (FreeCoprodCompDisc.Iso.invHom O (mprecompIso.{uA, uB, uI, uO} I O [] γ X)))

/-- Transport of a composite with a fresh right injection along an
equality of the inner object, by elimination of the generalized
equality: the cast passes to the left factor. -/
theorem comp_coprodPairInr_cast (a : SupObj.{uB, uI} I)
    (X : FreeCoprodCompDisc.{max uA uB, uI} I) :
    ∀ (W W' : FreeCoprodCompDisc.{max uA uB, uI} I) (e : W = W')
      (u : FreeCoprodCompDisc.Hom I X W),
      cast (congrArg (FreeCoprodCompDisc.Hom I X)
          (congrArg (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I a) e))
        (FreeCoprodCompDisc.Hom.comp I u
          (FreeCoprodCompDisc.coprodPairInr.{uI, uB, max uA uB} I a W)) =
      FreeCoprodCompDisc.Hom.comp I
        (cast (congrArg (FreeCoprodCompDisc.Hom I X) e) u)
        (FreeCoprodCompDisc.coprodPairInr.{uI, uB, max uA uB} I a W') :=
  fun W _W' e ↦
    Eq.rec (motive := fun W'' e' ↦ ∀ u : FreeCoprodCompDisc.Hom I X W,
        cast (congrArg (FreeCoprodCompDisc.Hom I X)
            (congrArg (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I a) e'))
          (FreeCoprodCompDisc.Hom.comp I u
            (FreeCoprodCompDisc.coprodPairInr.{uI, uB, max uA uB} I a W)) =
        FreeCoprodCompDisc.Hom.comp I
          (cast (congrArg (FreeCoprodCompDisc.Hom I X) e') u)
          (FreeCoprodCompDisc.coprodPairInr.{uI, uB, max uA uB} I a W''))
      (fun _ ↦ rfl) e

/-- `IR.mplusInj` at a right-appended superscript, transported along
`IR.mplus_snoc`: the fresh inner injection followed by the tower
injection at the enlarged base. -/
theorem mplusInj_snoc (L : List (SupObj.{uB, uI} I)) (b : SupObj.{uB, uI} I)
    (X : FreeCoprodCompDisc.{max uA uB, uI} I) :
    cast (congrArg (FreeCoprodCompDisc.Hom I X) (mplus_snoc.{uA, uB, uI} I L b X))
        (mplusInj.{uA, uB, uI} I (L ++ [b]) X) =
      FreeCoprodCompDisc.Hom.comp I
        (FreeCoprodCompDisc.coprodPairInr.{uI, uB, max uA uB} I b X)
        (mplusInj.{uA, uB, uI} I L (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b X)) :=
  L.rec (motive := fun L' ↦
      cast (congrArg (FreeCoprodCompDisc.Hom I X) (mplus_snoc.{uA, uB, uI} I L' b X))
          (mplusInj.{uA, uB, uI} I (L' ++ [b]) X) =
        FreeCoprodCompDisc.Hom.comp I
          (FreeCoprodCompDisc.coprodPairInr.{uI, uB, max uA uB} I b X)
          (mplusInj.{uA, uB, uI} I L'
            (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b X)))
    ((FreeCoprodCompDisc.Hom.id_comp I
        (FreeCoprodCompDisc.coprodPairInr.{uI, uB, max uA uB} I b X)).trans
      (FreeCoprodCompDisc.Hom.comp_id I
        (FreeCoprodCompDisc.coprodPairInr.{uI, uB, max uA uB} I b X)).symm)
    (fun a _L ih ↦
      (comp_coprodPairInr_cast I a X (mplus.{uA, uB, uI} I (_L ++ [b]) X)
          (mplus.{uA, uB, uI} I _L (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b X))
          (mplus_snoc.{uA, uB, uI} I _L b X)
          (mplusInj.{uA, uB, uI} I (_L ++ [b]) X)).trans
        ((congrArg
            (fun t ↦ FreeCoprodCompDisc.Hom.comp I t
              (FreeCoprodCompDisc.coprodPairInr.{uI, uB, max uA uB} I a
                (mplus.{uA, uB, uI} I _L
                  (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b X))))
            ih).trans
          (FreeCoprodCompDisc.Hom.comp_assoc I
            (FreeCoprodCompDisc.coprodPairInr.{uI, uB, max uA uB} I b X)
            (mplusInj.{uA, uB, uI} I _L
              (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b X))
            (FreeCoprodCompDisc.coprodPairInr.{uI, uB, max uA uB} I a
              (mplus.{uA, uB, uI} I _L
                (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b X))))))

/-- The Lemma 4 isomorphism commutes object-equality transports across
its two sides (forward direction), by elimination of the generalized
equality. -/
theorem interpPrecompIso_hom_isoOfEq (γ : IR.{max uA uB, uB, uI, uO} I O)
    (Q : Type uB) (q : Q → I) :
    ∀ (W W' : FreeCoprodCompDisc.{max uA uB, uI} I) (e : W = W'),
      FreeCoprodCompDisc.Hom.comp O
          (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
            (congrArg (interpObj I O (precomp I O Q q γ)) e)))
          (FreeCoprodCompDisc.Iso.hom O (interpPrecompIso I O γ Q q W')) =
        FreeCoprodCompDisc.Hom.comp O
          (FreeCoprodCompDisc.Iso.hom O (interpPrecompIso I O γ Q q W))
          (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
            (congrArg
              (fun w ↦ interpObj I O γ
                (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Q, q⟩ w))
              e))) :=
  fun W _W' e ↦
    Eq.rec (motive := fun W'' e' ↦
        FreeCoprodCompDisc.Hom.comp O
            (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
              (congrArg (interpObj I O (precomp I O Q q γ)) e')))
            (FreeCoprodCompDisc.Iso.hom O (interpPrecompIso I O γ Q q W'')) =
          FreeCoprodCompDisc.Hom.comp O
            (FreeCoprodCompDisc.Iso.hom O (interpPrecompIso I O γ Q q W))
            (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
              (congrArg
                (fun w ↦ interpObj I O γ
                  (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Q, q⟩ w))
                e'))))
      rfl e

/-- The Lemma 4 isomorphism commutes object-equality transports across
its two sides (inverse direction), by elimination of the generalized
equality. -/
theorem interpPrecompIso_invHom_isoOfEq (γ : IR.{max uA uB, uB, uI, uO} I O)
    (Q : Type uB) (q : Q → I) :
    ∀ (W W' : FreeCoprodCompDisc.{max uA uB, uI} I) (e : W = W'),
      FreeCoprodCompDisc.Hom.comp O
          (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
            (congrArg
              (fun w ↦ interpObj I O γ
                (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Q, q⟩ w))
              e)))
          (FreeCoprodCompDisc.Iso.invHom O (interpPrecompIso I O γ Q q W')) =
        FreeCoprodCompDisc.Hom.comp O
          (FreeCoprodCompDisc.Iso.invHom O (interpPrecompIso I O γ Q q W))
          (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
            (congrArg (interpObj I O (precomp I O Q q γ)) e))) :=
  fun W _W' e ↦
    Eq.rec (motive := fun W'' e' ↦
        FreeCoprodCompDisc.Hom.comp O
            (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
              (congrArg
                (fun w ↦ interpObj I O γ
                  (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Q, q⟩ w))
                e')))
            (FreeCoprodCompDisc.Iso.invHom O (interpPrecompIso I O γ Q q W'')) =
          FreeCoprodCompDisc.Hom.comp O
            (FreeCoprodCompDisc.Iso.invHom O (interpPrecompIso I O γ Q q W))
            (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
              (congrArg (interpObj I O (precomp I O Q q γ)) e'))))
      rfl e

/-- The forward component of `IR.mprecompIso` at a right-appended
superscript: one Lemma 4 layer at the base of the tower, conjugated by
the `IR.mprecomp_snoc` and `IR.mplus_snoc` transports. -/
theorem mprecompIso_snoc_hom (L : List (SupObj.{uB, uI} I)) (b : SupObj.{uB, uI} I)
    (γ : IR.{max uA uB, uB, uI, uO} I O) (X : FreeCoprodCompDisc.{max uA uB, uI} I) :
    FreeCoprodCompDisc.Iso.hom O (mprecompIso.{uA, uB, uI, uO} I O (L ++ [b]) γ X) =
      FreeCoprodCompDisc.Hom.comp O
        (FreeCoprodCompDisc.Hom.comp O
          (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
            (congrArg (fun c ↦ interpObj I O c X) (mprecomp_snoc I O L b γ))))
          (FreeCoprodCompDisc.Iso.hom O
            (interpPrecompIso I O (mprecomp I O L γ) b.1 b.2 X)))
        (FreeCoprodCompDisc.Hom.comp O
          (FreeCoprodCompDisc.Iso.hom O (mprecompIso.{uA, uB, uI, uO} I O L γ
            (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b X)))
          (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
            (congrArg (interpObj I O γ) (mplus_snoc.{uA, uB, uI} I L b X).symm)))) :=
  L.rec (motive := fun L' ↦ ∀ γ' : IR.{max uA uB, uB, uI, uO} I O,
      FreeCoprodCompDisc.Iso.hom O
          (mprecompIso.{uA, uB, uI, uO} I O (L' ++ [b]) γ' X) =
        FreeCoprodCompDisc.Hom.comp O
          (FreeCoprodCompDisc.Hom.comp O
            (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
              (congrArg (fun c ↦ interpObj I O c X) (mprecomp_snoc I O L' b γ'))))
            (FreeCoprodCompDisc.Iso.hom O
              (interpPrecompIso I O (mprecomp I O L' γ') b.1 b.2 X)))
          (FreeCoprodCompDisc.Hom.comp O
            (FreeCoprodCompDisc.Iso.hom O (mprecompIso.{uA, uB, uI, uO} I O L' γ'
              (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b X)))
            (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
              (congrArg (interpObj I O γ')
                (mplus_snoc.{uA, uB, uI} I L' b X).symm)))))
    (fun _ ↦ rfl)
    (fun a _L ih γ' ↦
      (congrArg
          (fun t ↦ FreeCoprodCompDisc.Hom.comp O t
            (FreeCoprodCompDisc.Iso.hom O
              (interpPrecompIso I O γ' a.1 a.2
                (mplus.{uA, uB, uI} I (_L ++ [b]) X))))
          (ih (precomp I O a.1 a.2 γ'))).trans
        ((FreeCoprodCompDisc.Hom.comp_assoc O
            (FreeCoprodCompDisc.Hom.comp O
              (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
                (congrArg (fun c ↦ interpObj I O c X)
                  (mprecomp_snoc I O _L b (precomp I O a.1 a.2 γ')))))
              (FreeCoprodCompDisc.Iso.hom O
                (interpPrecompIso I O (mprecomp I O _L (precomp I O a.1 a.2 γ'))
                  b.1 b.2 X)))
            (FreeCoprodCompDisc.Hom.comp O
              (FreeCoprodCompDisc.Iso.hom O
                (mprecompIso.{uA, uB, uI, uO} I O _L (precomp I O a.1 a.2 γ')
                  (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b X)))
              (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
                (congrArg (interpObj I O (precomp I O a.1 a.2 γ'))
                  (mplus_snoc.{uA, uB, uI} I _L b X).symm))))
            (FreeCoprodCompDisc.Iso.hom O
              (interpPrecompIso I O γ' a.1 a.2
                (mplus.{uA, uB, uI} I (_L ++ [b]) X)))).trans
          (congrArg
            (FreeCoprodCompDisc.Hom.comp O
              (FreeCoprodCompDisc.Hom.comp O
                (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
                  (congrArg (fun c ↦ interpObj I O c X)
                    (mprecomp_snoc I O _L b (precomp I O a.1 a.2 γ')))))
                (FreeCoprodCompDisc.Iso.hom O
                  (interpPrecompIso I O
                    (mprecomp I O _L (precomp I O a.1 a.2 γ')) b.1 b.2 X))))
            ((FreeCoprodCompDisc.Hom.comp_assoc O
                (FreeCoprodCompDisc.Iso.hom O
                  (mprecompIso.{uA, uB, uI, uO} I O _L (precomp I O a.1 a.2 γ')
                    (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b X)))
                (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
                  (congrArg (interpObj I O (precomp I O a.1 a.2 γ'))
                    (mplus_snoc.{uA, uB, uI} I _L b X).symm)))
                (FreeCoprodCompDisc.Iso.hom O
                  (interpPrecompIso I O γ' a.1 a.2
                    (mplus.{uA, uB, uI} I (_L ++ [b]) X)))).trans
              ((congrArg
                  (FreeCoprodCompDisc.Hom.comp O
                    (FreeCoprodCompDisc.Iso.hom O
                      (mprecompIso.{uA, uB, uI, uO} I O _L
                        (precomp I O a.1 a.2 γ')
                        (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b X))))
                  (interpPrecompIso_hom_isoOfEq I O γ' a.1 a.2
                    (mplus.{uA, uB, uI} I _L
                      (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b X))
                    (mplus.{uA, uB, uI} I (_L ++ [b]) X)
                    (mplus_snoc.{uA, uB, uI} I _L b X).symm)).trans
                (FreeCoprodCompDisc.Hom.comp_assoc O
                  (FreeCoprodCompDisc.Iso.hom O
                    (mprecompIso.{uA, uB, uI, uO} I O _L (precomp I O a.1 a.2 γ')
                      (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b X)))
                  (FreeCoprodCompDisc.Iso.hom O
                    (interpPrecompIso I O γ' a.1 a.2
                      (mplus.{uA, uB, uI} I _L
                        (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b X))))
                  (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
                    (congrArg
                      (fun w ↦ interpObj I O γ'
                        (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I a w))
                      (mplus_snoc.{uA, uB, uI} I _L b X).symm)))).symm)))))
    γ

/-- The inverse component of `IR.mprecompIso` at a right-appended
superscript: the inverse of one Lemma 4 layer at the base of the
tower, conjugated by the `IR.mplus_snoc` and `IR.mprecomp_snoc`
transports. -/
theorem mprecompIso_snoc_invHom (L : List (SupObj.{uB, uI} I)) (b : SupObj.{uB, uI} I)
    (γ : IR.{max uA uB, uB, uI, uO} I O) (X : FreeCoprodCompDisc.{max uA uB, uI} I) :
    FreeCoprodCompDisc.Iso.invHom O
        (mprecompIso.{uA, uB, uI, uO} I O (L ++ [b]) γ X) =
      FreeCoprodCompDisc.Hom.comp O
        (FreeCoprodCompDisc.Hom.comp O
          (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
            (congrArg (interpObj I O γ) (mplus_snoc.{uA, uB, uI} I L b X))))
          (FreeCoprodCompDisc.Iso.invHom O (mprecompIso.{uA, uB, uI, uO} I O L γ
            (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b X))))
        (FreeCoprodCompDisc.Hom.comp O
          (FreeCoprodCompDisc.Iso.invHom O
            (interpPrecompIso I O (mprecomp I O L γ) b.1 b.2 X))
          (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
            (congrArg (fun c ↦ interpObj I O c X)
              (mprecomp_snoc I O L b γ).symm)))) :=
  L.rec (motive := fun L' ↦ ∀ γ' : IR.{max uA uB, uB, uI, uO} I O,
      FreeCoprodCompDisc.Iso.invHom O
          (mprecompIso.{uA, uB, uI, uO} I O (L' ++ [b]) γ' X) =
        FreeCoprodCompDisc.Hom.comp O
          (FreeCoprodCompDisc.Hom.comp O
            (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
              (congrArg (interpObj I O γ') (mplus_snoc.{uA, uB, uI} I L' b X))))
            (FreeCoprodCompDisc.Iso.invHom O
              (mprecompIso.{uA, uB, uI, uO} I O L' γ'
                (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b X))))
          (FreeCoprodCompDisc.Hom.comp O
            (FreeCoprodCompDisc.Iso.invHom O
              (interpPrecompIso I O (mprecomp I O L' γ') b.1 b.2 X))
            (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
              (congrArg (fun c ↦ interpObj I O c X)
                (mprecomp_snoc I O L' b γ').symm)))))
    (fun _ ↦ rfl)
    (fun a _L ih γ' ↦
      (congrArg
          (FreeCoprodCompDisc.Hom.comp O
            (FreeCoprodCompDisc.Iso.invHom O
              (interpPrecompIso I O γ' a.1 a.2
                (mplus.{uA, uB, uI} I (_L ++ [b]) X))))
          (ih (precomp I O a.1 a.2 γ'))).trans
        ((congrArg
            (FreeCoprodCompDisc.Hom.comp O
              (FreeCoprodCompDisc.Iso.invHom O
                (interpPrecompIso I O γ' a.1 a.2
                  (mplus.{uA, uB, uI} I (_L ++ [b]) X))))
            (FreeCoprodCompDisc.Hom.comp_assoc O
              (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
                (congrArg (interpObj I O (precomp I O a.1 a.2 γ'))
                  (mplus_snoc.{uA, uB, uI} I _L b X))))
              (FreeCoprodCompDisc.Iso.invHom O
                (mprecompIso.{uA, uB, uI, uO} I O _L (precomp I O a.1 a.2 γ')
                  (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b X)))
              (FreeCoprodCompDisc.Hom.comp O
                (FreeCoprodCompDisc.Iso.invHom O
                  (interpPrecompIso I O
                    (mprecomp I O _L (precomp I O a.1 a.2 γ')) b.1 b.2 X))
                (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
                  (congrArg (fun c ↦ interpObj I O c X)
                    (mprecomp_snoc I O _L b (precomp I O a.1 a.2 γ')).symm)))))).trans
          ((FreeCoprodCompDisc.Hom.comp_assoc O
              (FreeCoprodCompDisc.Iso.invHom O
                (interpPrecompIso I O γ' a.1 a.2
                  (mplus.{uA, uB, uI} I (_L ++ [b]) X)))
              (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
                (congrArg (interpObj I O (precomp I O a.1 a.2 γ'))
                  (mplus_snoc.{uA, uB, uI} I _L b X))))
              (FreeCoprodCompDisc.Hom.comp O
                (FreeCoprodCompDisc.Iso.invHom O
                  (mprecompIso.{uA, uB, uI, uO} I O _L (precomp I O a.1 a.2 γ')
                    (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b X)))
                (FreeCoprodCompDisc.Hom.comp O
                  (FreeCoprodCompDisc.Iso.invHom O
                    (interpPrecompIso I O
                      (mprecomp I O _L (precomp I O a.1 a.2 γ')) b.1 b.2 X))
                  (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
                    (congrArg (fun c ↦ interpObj I O c X)
                      (mprecomp_snoc I O _L b
                        (precomp I O a.1 a.2 γ')).symm)))))).symm.trans
            ((congrArg
                (fun t ↦ FreeCoprodCompDisc.Hom.comp O t
                  (FreeCoprodCompDisc.Hom.comp O
                    (FreeCoprodCompDisc.Iso.invHom O
                      (mprecompIso.{uA, uB, uI, uO} I O _L
                        (precomp I O a.1 a.2 γ')
                        (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b X)))
                    (FreeCoprodCompDisc.Hom.comp O
                      (FreeCoprodCompDisc.Iso.invHom O
                        (interpPrecompIso I O
                          (mprecomp I O _L (precomp I O a.1 a.2 γ'))
                          b.1 b.2 X))
                      (FreeCoprodCompDisc.Iso.hom O
                        (FreeCoprodCompDisc.isoOfEq O
                          (congrArg (fun c ↦ interpObj I O c X)
                            (mprecomp_snoc I O _L b
                              (precomp I O a.1 a.2 γ')).symm))))))
                (interpPrecompIso_invHom_isoOfEq I O γ' a.1 a.2
                  (mplus.{uA, uB, uI} I (_L ++ [b]) X)
                  (mplus.{uA, uB, uI} I _L
                    (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b X))
                  (mplus_snoc.{uA, uB, uI} I _L b X)).symm).trans
              ((FreeCoprodCompDisc.Hom.comp_assoc O
                  (FreeCoprodCompDisc.Hom.comp O
                    (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
                      (congrArg
                        (fun w ↦ interpObj I O γ'
                          (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I a w))
                        (mplus_snoc.{uA, uB, uI} I _L b X))))
                    (FreeCoprodCompDisc.Iso.invHom O
                      (interpPrecompIso I O γ' a.1 a.2
                        (mplus.{uA, uB, uI} I _L
                          (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b X)))))
                  (FreeCoprodCompDisc.Iso.invHom O
                    (mprecompIso.{uA, uB, uI, uO} I O _L
                      (precomp I O a.1 a.2 γ')
                      (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b X)))
                  (FreeCoprodCompDisc.Hom.comp O
                    (FreeCoprodCompDisc.Iso.invHom O
                      (interpPrecompIso I O
                        (mprecomp I O _L (precomp I O a.1 a.2 γ'))
                        b.1 b.2 X))
                    (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
                      (congrArg (fun c ↦ interpObj I O c X)
                        (mprecomp_snoc I O _L b
                          (precomp I O a.1 a.2 γ')).symm))))).trans
                ((congrArg
                    (FreeCoprodCompDisc.Hom.comp O
                      (FreeCoprodCompDisc.Iso.hom O
                        (FreeCoprodCompDisc.isoOfEq O
                          (congrArg
                            (fun w ↦ interpObj I O γ'
                              (FreeCoprodCompDisc.plus.{uI, uB, max uA uB}
                                I a w))
                            (mplus_snoc.{uA, uB, uI} I _L b X)))))
                    (FreeCoprodCompDisc.Hom.comp_assoc O
                      (FreeCoprodCompDisc.Iso.invHom O
                        (interpPrecompIso I O γ' a.1 a.2
                          (mplus.{uA, uB, uI} I _L
                            (FreeCoprodCompDisc.plus.{uI, uB, max uA uB}
                              I b X))))
                      (FreeCoprodCompDisc.Iso.invHom O
                        (mprecompIso.{uA, uB, uI, uO} I O _L
                          (precomp I O a.1 a.2 γ')
                          (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b X)))
                      (FreeCoprodCompDisc.Hom.comp O
                        (FreeCoprodCompDisc.Iso.invHom O
                          (interpPrecompIso I O
                            (mprecomp I O _L (precomp I O a.1 a.2 γ'))
                            b.1 b.2 X))
                        (FreeCoprodCompDisc.Iso.hom O
                          (FreeCoprodCompDisc.isoOfEq O
                            (congrArg (fun c ↦ interpObj I O c X)
                              (mprecomp_snoc I O _L b
                                (precomp I O a.1 a.2 γ')).symm)))))).symm.trans
                  (FreeCoprodCompDisc.Hom.comp_assoc O
                    (FreeCoprodCompDisc.Hom.comp O
                      (FreeCoprodCompDisc.Iso.hom O
                        (FreeCoprodCompDisc.isoOfEq O
                          (congrArg
                            (fun w ↦ interpObj I O γ'
                              (FreeCoprodCompDisc.plus.{uI, uB, max uA uB}
                                I a w))
                            (mplus_snoc.{uA, uB, uI} I _L b X))))
                      (FreeCoprodCompDisc.Hom.comp O
                        (FreeCoprodCompDisc.Iso.invHom O
                          (interpPrecompIso I O γ' a.1 a.2
                            (mplus.{uA, uB, uI} I _L
                              (FreeCoprodCompDisc.plus.{uI, uB, max uA uB}
                                I b X))))
                        (FreeCoprodCompDisc.Iso.invHom O
                          (mprecompIso.{uA, uB, uI, uO} I O _L
                            (precomp I O a.1 a.2 γ')
                            (FreeCoprodCompDisc.plus.{uI, uB, max uA uB}
                              I b X)))))
                    (FreeCoprodCompDisc.Iso.invHom O
                      (interpPrecompIso I O
                        (mprecomp I O _L (precomp I O a.1 a.2 γ'))
                        b.1 b.2 X))
                    (FreeCoprodCompDisc.Iso.hom O
                      (FreeCoprodCompDisc.isoOfEq O
                        (congrArg (fun c ↦ interpObj I O c X)
                          (mprecomp_snoc I O _L b
                            (precomp I O a.1 a.2 γ')).symm))))))))))
    γ

/-- The tower action on morphisms: the identity on every stacked
superscript, the given morphism at the base. -/
def mplusMorMap (L : List (SupObj.{uB, uI} I))
    (X Y : FreeCoprodCompDisc.{max uA uB, uI} I) (h : FreeCoprodCompDisc.Hom I X Y) :
    FreeCoprodCompDisc.Hom I (mplus.{uA, uB, uI} I L X) (mplus.{uA, uB, uI} I L Y) :=
  L.rec (motive := fun L' ↦
      FreeCoprodCompDisc.Hom I (mplus.{uA, uB, uI} I L' X) (mplus.{uA, uB, uI} I L' Y))
    h
    (fun b _L ih ↦
      FreeCoprodCompDisc.coprodPairMor I (FreeCoprodCompDisc.Hom.id I b) ih)

/-- The iterated Lemma 4 naturality: `IR.mprecompIso` is natural in the
interpreted object, between the tower interpretation's morphism map and
the direct interpretation's at the `IR.mplusMorMap` image. -/
theorem mprecompIso_natural (L : List (SupObj.{uB, uI} I))
    (γ : IR.{max uA uB, uB, uI, uO} I O)
    (X Y : FreeCoprodCompDisc.{max uA uB, uI} I) (h : FreeCoprodCompDisc.Hom I X Y) :
    FreeCoprodCompDisc.Hom.comp O
        (interpMor I O (mprecomp I O L γ) X Y h)
        (FreeCoprodCompDisc.Iso.hom O (mprecompIso.{uA, uB, uI, uO} I O L γ Y)) =
      FreeCoprodCompDisc.Hom.comp O
        (FreeCoprodCompDisc.Iso.hom O (mprecompIso.{uA, uB, uI, uO} I O L γ X))
        (interpMor I O γ (mplus.{uA, uB, uI} I L X) (mplus.{uA, uB, uI} I L Y)
          (mplusMorMap.{uA, uB, uI} I L X Y h)) :=
  L.rec (motive := fun L' ↦ ∀ γ' : IR.{max uA uB, uB, uI, uO} I O,
      FreeCoprodCompDisc.Hom.comp O
          (interpMor I O (mprecomp I O L' γ') X Y h)
          (FreeCoprodCompDisc.Iso.hom O
            (mprecompIso.{uA, uB, uI, uO} I O L' γ' Y)) =
        FreeCoprodCompDisc.Hom.comp O
          (FreeCoprodCompDisc.Iso.hom O
            (mprecompIso.{uA, uB, uI, uO} I O L' γ' X))
          (interpMor I O γ' (mplus.{uA, uB, uI} I L' X)
            (mplus.{uA, uB, uI} I L' Y) (mplusMorMap.{uA, uB, uI} I L' X Y h)))
    (fun γ' ↦
      (FreeCoprodCompDisc.Hom.comp_id O (interpMor I O γ' X Y h)).trans
        (FreeCoprodCompDisc.Hom.id_comp O (interpMor I O γ' X Y h)).symm)
    (fun a _L ih γ' ↦
      (FreeCoprodCompDisc.Hom.comp_assoc O
          (interpMor I O (mprecomp I O _L (precomp I O a.1 a.2 γ')) X Y h)
          (FreeCoprodCompDisc.Iso.hom O
            (mprecompIso.{uA, uB, uI, uO} I O _L (precomp I O a.1 a.2 γ') Y))
          (FreeCoprodCompDisc.Iso.hom O
            (interpPrecompIso I O γ' a.1 a.2
              (mplus.{uA, uB, uI} I _L Y)))).symm.trans
        ((congrArg
            (fun t ↦ FreeCoprodCompDisc.Hom.comp O t
              (FreeCoprodCompDisc.Iso.hom O
                (interpPrecompIso I O γ' a.1 a.2 (mplus.{uA, uB, uI} I _L Y))))
            (ih (precomp I O a.1 a.2 γ'))).trans
          ((FreeCoprodCompDisc.Hom.comp_assoc O
              (FreeCoprodCompDisc.Iso.hom O
                (mprecompIso.{uA, uB, uI, uO} I O _L (precomp I O a.1 a.2 γ') X))
              (interpMor I O (precomp I O a.1 a.2 γ') (mplus.{uA, uB, uI} I _L X)
                (mplus.{uA, uB, uI} I _L Y) (mplusMorMap.{uA, uB, uI} I _L X Y h))
              (FreeCoprodCompDisc.Iso.hom O
                (interpPrecompIso I O γ' a.1 a.2
                  (mplus.{uA, uB, uI} I _L Y)))).trans
            ((congrArg
                (FreeCoprodCompDisc.Hom.comp O
                  (FreeCoprodCompDisc.Iso.hom O
                    (mprecompIso.{uA, uB, uI, uO} I O _L
                      (precomp I O a.1 a.2 γ') X)))
                (interpPrecompIso_natural I O γ' a.1 a.2
                  (mplus.{uA, uB, uI} I _L X) (mplus.{uA, uB, uI} I _L Y)
                  (mplusMorMap.{uA, uB, uI} I _L X Y h))).trans
              (FreeCoprodCompDisc.Hom.comp_assoc O
                (FreeCoprodCompDisc.Iso.hom O
                  (mprecompIso.{uA, uB, uI, uO} I O _L
                    (precomp I O a.1 a.2 γ') X))
                (FreeCoprodCompDisc.Iso.hom O
                  (interpPrecompIso I O γ' a.1 a.2 (mplus.{uA, uB, uI} I _L X)))
                (interpMor I O γ'
                  (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I a
                    (mplus.{uA, uB, uI} I _L X))
                  (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I a
                    (mplus.{uA, uB, uI} I _L Y))
                  (FreeCoprodCompDisc.coprodPairMor I
                    (FreeCoprodCompDisc.Hom.id I a)
                    (mplusMorMap.{uA, uB, uI} I _L X Y h)))).symm))))
    γ

/-! ### The `interpHom` characterizing equations -/

/-- Components pass through `NatTrans.congrSource` unchanged. -/
theorem congrSource_symm_fst {F G : FreeCoprodCompDisc.Map.{uA, uI, uO} I O}
    {mF mF' : FreeCoprodCompDisc.MapMor I O F} (e : mF = mF')
    (mG : FreeCoprodCompDisc.MapMor I O G)
    (η : FreeCoprodCompDisc.NatTrans I O F G mF' mG) :
    ((FreeCoprodCompDisc.NatTrans.congrSource e mG).symm η).1 = η.1 :=
  Eq.rec (motive := fun mF'' e' ↦
      ∀ η' : FreeCoprodCompDisc.NatTrans I O F G mF'' mG,
        ((FreeCoprodCompDisc.NatTrans.congrSource e' mG).symm η').1 = η'.1)
    (fun _ ↦ rfl) e η

/-- The characterizing equation of `IR.interpHomEquiv` at `IR.mk`. -/
theorem interpHomEquiv_mk (s : Shape.{max uA uB, uB, uO} O)
    (d : Direction I O s → IR.{max uA uB, uB, uI, uO} I O)
    (γ' : IR.{max uA uB, uB, uI, uO} I O) :
    interpHomEquiv I O (mk I O s d) γ' =
      interpHomEquivStep I O s d (fun x ↦ interpHomEquiv I O (d x)) γ' :=
  congrFun (rec_mk I O (interpHomEquivStep I O) s d) γ'

/-- The component of `IR.interpHom` at an `ι`-domain: the singleton
morphism carried by the inner hom, composed with the codomain's image
of the unique morphism out of the initial object. -/
theorem interpHom_iota (o : O) (γ' : IR.{max uA uB, uB, uI, uO} I O)
    (f : InnerHom.{uA, uB, uI, uO} I O o γ')
    (X : FreeCoprodCompDisc.{max uA uB, uI} I) :
    (interpHom I O (iota.{max uA uB, uB, uI, uO} I O o) γ' f).1 X =
      FreeCoprodCompDisc.Hom.comp O
        ((FreeCoprodCompDisc.homSingletonEquiv O o
            (interpObj I O γ' (FreeCoprodCompDisc.emptyObj I))).symm
          (innerHomEquiv I O o γ' f))
        (interpMor I O γ' (FreeCoprodCompDisc.emptyObj I) X
          (FreeCoprodCompDisc.emptyDesc I X)) :=
  congrArg (fun e ↦ (e f).1 X)
    (interpHomEquiv_mk I O (Sum.inl o) PEmpty.elim γ')

/-- The component of `IR.interpHom` at a `σ`-domain: the cotuple of the
subcode components. -/
theorem interpHom_sigma (A : Type (max uA uB))
    (K : A → IR.{max uA uB, uB, uI, uO} I O)
    (γ' : IR.{max uA uB, uB, uI, uO} I O)
    (f : Hom.{uA, uB, uI, uO} I O (sigma I O A K) γ')
    (X : FreeCoprodCompDisc.{max uA uB, uI} I) :
    (interpHom I O (sigma I O A K) γ' f).1 X =
      FreeCoprodCompDisc.coprodDesc O A (fun a ↦ interpObj I O (K a) X)
        (interpObj I O γ' X)
        (fun a ↦ (interpHom I O (K a) γ' (f a)).1 X) :=
  (congrArg (fun e ↦ (e f).1 X)
      (interpHomEquiv_mk I O (Sum.inr (Sum.inl A)) (K ∘ ULift.down) γ')).trans
    (congrFun
      (congrSource_symm_fst.{max uA uB, uI, uO} I O
        (interpMor_sigma.{max uA uB, uB, uI, uO} I O A K) _
        (FreeCoprodCompDisc.natCoprodEquiv.{max uA uB, uI, uO} A
            (fun a ↦ interpObj I O (K a))
            (fun a ↦ interpMor I O (K a)) (interpObj I O γ')
            (interpMor I O γ')
          |>.symm (fun a ↦ interpHomEquiv I O (K a) γ' (f a))))
      X)

/-- The per-summand transport of the `δ`-domain case of
`IR.interpHomEquiv`: the interpretation of a clause 3 component,
transported to a transformation out of the copower summand by the
Lemma 4 pair, the bridge pair, and the copower adjunction. -/
def interpHomDeltaSummand (B : Type uB)
    (c : (B → I) → IR.{max uA uB, uB, uI, uO} I O)
    (γ' : IR.{max uA uB, uB, uI, uO} I O) (i : B → I)
    (g : Hom.{uA, uB, uI, uO} I O (c i) (precomp I O B i γ')) :
    FreeCoprodCompDisc.NatTrans I O
      (FreeCoprodCompDisc.copowerHomMap
        (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩)
        (interpObj I O (c i)))
      (interpObj I O γ')
      (FreeCoprodCompDisc.copowerHomMapMor
        (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩)
        (interpMor I O (c i)))
      (interpMor I O γ') :=
  (FreeCoprodCompDisc.natCopowerPlusEquiv
      (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩)
      (interpMor I O (c i)) (interpMor I O γ')
      (interpMor_id I O (c i)) (interpMor_comp I O (c i))
      (interpMor_id I O γ') (interpMor_comp I O γ')).symm
    (FreeCoprodCompDisc.NatTrans.vcomp
      (FreeCoprodCompDisc.NatTrans.vcomp
        (interpHom I O (c i) (precomp I O B i γ') g)
        (FreeCoprodCompDisc.NatTrans.ofIsoFamily
          (fun k ↦ interpPrecompIso I O γ' B i k)
          (interpPrecompIso_natural I O γ' B i)))
      (plusLiftBridgeNatInv I O B i γ'))

/-- The component of `IR.interpHom` at a `δ`-domain: the cotuple of the
transported subcode components. -/
theorem interpHom_delta (B : Type uB)
    (c : (B → I) → IR.{max uA uB, uB, uI, uO} I O)
    (γ' : IR.{max uA uB, uB, uI, uO} I O)
    (f : Hom.{uA, uB, uI, uO} I O (delta I O B c) γ')
    (X : FreeCoprodCompDisc.{max uA uB, uI} I) :
    (interpHom I O (delta I O B c) γ' f).1 X =
      deltaDesc I O B c X (interpObj I O γ' X)
        (fun i ↦ (interpHomDeltaSummand I O B c γ' i (f i)).1 X) :=
  congrArg (fun e ↦ (e f).1 X)
    (interpHomEquiv_mk I O (Sum.inr (Sum.inr B)) (c ∘ ULift.down) γ')

/-- `IR.deltaDesc` composes on the right componentwise. -/
theorem deltaDesc_comp (B : Type uB)
    (c : (B → I) → IR.{max uA uB, uB, uI, uO} I O)
    (X : FreeCoprodCompDisc.{max uA uB, uI} I)
    (Z W : FreeCoprodCompDisc.{max uA uB, uO} O)
    (m : (i : B → I) → FreeCoprodCompDisc.Hom O
      (FreeCoprodCompDisc.copowerHomMap
        (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩)
        (interpObj I O (c i)) X) Z)
    (g : FreeCoprodCompDisc.Hom O Z W) :
    FreeCoprodCompDisc.Hom.comp O (deltaDesc I O B c X Z m) g =
      deltaDesc I O B c X W (fun i ↦ FreeCoprodCompDisc.Hom.comp O (m i) g) :=
  deltaHom_ext I O B c X W _ _ (fun i ↦
    ((FreeCoprodCompDisc.Hom.comp_assoc O (deltaInto I O B c i X)
        (deltaDesc I O B c X Z m) g).symm.trans
      (congrArg (fun t ↦ FreeCoprodCompDisc.Hom.comp O t g)
        (deltaInto_desc I O B c i X Z m))).trans
    (deltaInto_desc I O B c i X W
      (fun i' ↦ FreeCoprodCompDisc.Hom.comp O (m i') g)).symm)

/-- The `σ`-injection square: a semantic `σ`-injection commutes the
morphism map of a `σ`-interpretation with the summand's. -/
theorem interpMor_sigma_inj (A' : Type (max uA uB))
    (K' : A' → IR.{max uA uB, uB, uI, uO} I O) (a' : A')
    (Z W : FreeCoprodCompDisc.{max uA uB, uI} I)
    (h : FreeCoprodCompDisc.Hom I Z W) :
    FreeCoprodCompDisc.Hom.comp O
        (FreeCoprodCompDisc.coprodInj O A' (fun a ↦ interpObj I O (K' a) Z) a')
        (interpMor I O (sigma I O A' K') Z W h) =
      FreeCoprodCompDisc.Hom.comp O (interpMor I O (K' a') Z W h)
        (FreeCoprodCompDisc.coprodInj O A' (fun a ↦ interpObj I O (K' a) W) a') :=
  (congrArg
      (fun (t : MorMapSig I O (sigma I O A' K')) ↦
        FreeCoprodCompDisc.Hom.comp O
          (FreeCoprodCompDisc.coprodInj O A' (fun a ↦ interpObj I O (K' a) Z) a')
          (t Z W h))
      (interpMor_sigma.{max uA uB, uB, uI, uO} I O A' K')).trans
    (FreeCoprodCompDisc.coprodInj_mor O A' A' _root_.id
        (fun a ↦ interpObj I O (K' a) Z) (fun a ↦ interpObj I O (K' a) W)
        (fun a ↦ interpMor I O (K' a) Z W h) a').symm

/-- The characterizing equation of `IR.innerHomEquiv` at `IR.mk`. -/
theorem innerHomEquiv_mk (o : O) (s : Shape.{max uA uB, uB, uO} O)
    (d : Direction I O s → IR.{max uA uB, uB, uI, uO} I O) :
    innerHomEquiv I O o (mk I O s d) =
      innerHomEquivStep I O o s d (fun x ↦ innerHomEquiv I O o (d x)) :=
  rec_mk I O (innerHomEquivStep I O o) s d

/-! ### The `σ`-push characterization -/

/-- The statement of the `IR.sigmaPush` characterization at one code:
`IR.interpHom` sends a pushed morphism to the composite with the
semantic `σ`-injection. -/
def InterpHomSigmaPushMotive (γ : IR.{max uA uB, uB, uI, uO} I O) : Prop :=
  ∀ (A' : Type (max uA uB)) (K' : A' → IR.{max uA uB, uB, uI, uO} I O)
    (a' : A') (f : Hom.{uA, uB, uI, uO} I O γ (K' a'))
    (X : FreeCoprodCompDisc.{max uA uB, uI} I),
    (interpHom I O γ (sigma I O A' K') (sigmaPush I O γ A' K' a' f)).1 X =
      FreeCoprodCompDisc.Hom.comp O ((interpHom I O γ (K' a') f).1 X)
        (FreeCoprodCompDisc.coprodInj O A' (fun a ↦ interpObj I O (K' a) X) a')

/-- The `ι`-composite of the Theorem 3 step at codomain `γ'`
(definitionally the equivalence the step transports). -/
def interpHomIotaComposite (o : O) (γ' : IR.{max uA uB, uB, uI, uO} I O) :
    InnerHom.{uA, uB, uI, uO} I O o γ' ≃
      FreeCoprodCompDisc.NatTrans I O
        (interpObj I O (iota.{max uA uB, uB, uI, uO} I O o)) (interpObj I O γ')
        (interpMor I O (iota.{max uA uB, uB, uI, uO} I O o)) (interpMor I O γ') :=
  (innerHomEquiv I O o γ').trans
    ((FreeCoprodCompDisc.homSingletonEquiv O o
        (interpObj I O γ' (FreeCoprodCompDisc.emptyObj I))).symm.trans
      (natIotaEquiv I O o γ').symm)

/-- The transport of `IR.interpHomIotaComposite` along a code equality
(definitionally the `ι`-branch of `IR.interpHomEquivStep`). -/
def interpHomIotaCast (o : O) (γ' : IR.{max uA uB, uB, uI, uO} I O)
    (ir : IR.{max uA uB, uB, uI, uO} I O)
    (e : iota.{max uA uB, uB, uI, uO} I O o = ir) :
    InnerHom.{uA, uB, uI, uO} I O o γ' ≃
      FreeCoprodCompDisc.NatTrans I O (interpObj I O ir) (interpObj I O γ')
        (interpMor I O ir) (interpMor I O γ') :=
  Eq.rec (motive := fun ir' _ ↦
      InnerHom.{uA, uB, uI, uO} I O o γ' ≃
        FreeCoprodCompDisc.NatTrans I O (interpObj I O ir') (interpObj I O γ')
          (interpMor I O ir') (interpMor I O γ'))
    (interpHomIotaComposite I O o γ') e

/-- The singleton morphism at a `σ`-summand name factors through the
semantic `σ`-injection. -/
theorem homSingletonEquiv_symm_inj (o : O) (A' : Type (max uA uB))
    (K' : A' → IR.{max uA uB, uB, uI, uO} I O) (a' : A')
    (z : {z : (interpObj I O (K' a') (FreeCoprodCompDisc.emptyObj I)).1 //
      (interpObj I O (K' a') (FreeCoprodCompDisc.emptyObj I)).2 z = o}) :
    (FreeCoprodCompDisc.homSingletonEquiv O o
        (interpObj I O (sigma I O A' K') (FreeCoprodCompDisc.emptyObj I))).symm
        ⟨⟨a', z.1⟩, z.2⟩ =
      FreeCoprodCompDisc.Hom.comp O
        ((FreeCoprodCompDisc.homSingletonEquiv O o
            (interpObj I O (K' a') (FreeCoprodCompDisc.emptyObj I))).symm z)
        (FreeCoprodCompDisc.coprodInj O A'
          (fun a ↦ interpObj I O (K' a) (FreeCoprodCompDisc.emptyObj I)) a') :=
  Subtype.ext (funext (fun _ ↦ rfl))

/-- The `σ`-push equation for the transported `ι`-composite, by
elimination of the code equality: at the reflexive instance both sides
compute to singleton morphisms into the initial-object fiber, related
by `IR.homSingletonEquiv_symm_inj` and the `σ`-injection square. -/
theorem interpHomIotaCast_sigmaPush (o : O) (A' : Type (max uA uB))
    (K' : A' → IR.{max uA uB, uB, uI, uO} I O) (a' : A')
    (f : InnerHom.{uA, uB, uI, uO} I O o (K' a'))
    (X : FreeCoprodCompDisc.{max uA uB, uI} I)
    (ir : IR.{max uA uB, uB, uI, uO} I O)
    (e : iota.{max uA uB, uB, uI, uO} I O o = ir) :
    ((interpHomIotaCast I O o (sigma I O A' K') ir e) ⟨a', f⟩).1 X =
      FreeCoprodCompDisc.Hom.comp O
        (((interpHomIotaCast I O o (K' a') ir e) f).1 X)
        (FreeCoprodCompDisc.coprodInj O A' (fun a ↦ interpObj I O (K' a) X) a') :=
  Eq.rec (motive := fun ir' e' ↦
      ((interpHomIotaCast I O o (sigma I O A' K') ir' e') ⟨a', f⟩).1 X =
        FreeCoprodCompDisc.Hom.comp O
          (((interpHomIotaCast I O o (K' a') ir' e') f).1 X)
          (FreeCoprodCompDisc.coprodInj O A'
            (fun a ↦ interpObj I O (K' a) X) a'))
    ((congrArg
        (fun t ↦ FreeCoprodCompDisc.Hom.comp O
          ((FreeCoprodCompDisc.homSingletonEquiv O o
              (interpObj I O (sigma I O A' K')
                (FreeCoprodCompDisc.emptyObj I))).symm (t ⟨a', f⟩))
          (interpMor I O (sigma I O A' K') (FreeCoprodCompDisc.emptyObj I) X
            (FreeCoprodCompDisc.emptyDesc I X)))
        (innerHomEquiv_mk I O o (Sum.inr (Sum.inl A')) (K' ∘ ULift.down))).trans
      ((congrArg
          (fun t ↦ FreeCoprodCompDisc.Hom.comp O t
            (interpMor I O (sigma I O A' K') (FreeCoprodCompDisc.emptyObj I) X
              (FreeCoprodCompDisc.emptyDesc I X)))
          (homSingletonEquiv_symm_inj I O o A' K' a'
            (innerHomEquiv I O o (K' a') f))).trans
        ((FreeCoprodCompDisc.Hom.comp_assoc O
            ((FreeCoprodCompDisc.homSingletonEquiv O o
                (interpObj I O (K' a') (FreeCoprodCompDisc.emptyObj I))).symm
              (innerHomEquiv I O o (K' a') f))
            (FreeCoprodCompDisc.coprodInj O A'
              (fun a ↦ interpObj I O (K' a) (FreeCoprodCompDisc.emptyObj I)) a')
            (interpMor I O (sigma I O A' K') (FreeCoprodCompDisc.emptyObj I) X
              (FreeCoprodCompDisc.emptyDesc I X))).trans
          ((congrArg
              (FreeCoprodCompDisc.Hom.comp O
                ((FreeCoprodCompDisc.homSingletonEquiv O o
                    (interpObj I O (K' a')
                      (FreeCoprodCompDisc.emptyObj I))).symm
                  (innerHomEquiv I O o (K' a') f)))
              (interpMor_sigma_inj I O A' K' a'
                (FreeCoprodCompDisc.emptyObj I) X
                (FreeCoprodCompDisc.emptyDesc I X))).trans
            (FreeCoprodCompDisc.Hom.comp_assoc O
              ((FreeCoprodCompDisc.homSingletonEquiv O o
                  (interpObj I O (K' a')
                    (FreeCoprodCompDisc.emptyObj I))).symm
                (innerHomEquiv I O o (K' a') f))
              (interpMor I O (K' a') (FreeCoprodCompDisc.emptyObj I) X
                (FreeCoprodCompDisc.emptyDesc I X))
              (FreeCoprodCompDisc.coprodInj O A'
                (fun a ↦ interpObj I O (K' a) X) a')).symm))))
    e

/-- The `ι`-case of the `IR.sigmaPush` characterization. -/
theorem interpHom_sigmaPush_mk_iota (o : O)
    (d : Direction I O (Sum.inl o : Shape.{max uA uB, uB, uO} O) →
      IR.{max uA uB, uB, uI, uO} I O) :
    InterpHomSigmaPushMotive I O (mk I O (Sum.inl o) d) :=
  fun A' K' a' f X ↦
    (congrArg
        (fun t ↦ (interpHom I O (mk I O (Sum.inl o) d)
          (sigma I O A' K') t).1 X)
        (sigmaPush_mk_iota I O o d A' K' a' f)).trans
      ((congrArg (fun e ↦ (e (⟨a', f⟩ :
            InnerHom.{uA, uB, uI, uO} I O o (sigma I O A' K'))).1 X)
          (interpHomEquiv_mk I O (Sum.inl o) d (sigma I O A' K'))).trans
        ((interpHomIotaCast_sigmaPush I O o A' K' a' f X
            (mk I O (Sum.inl o) d)
            (mk_congr I O (Sum.inl o)
              (funext (fun x ↦ nomatch x)) :
                mk I O (Sum.inl o) PEmpty.elim = mk I O (Sum.inl o) d)).trans
          (congrArg
            (fun t ↦ FreeCoprodCompDisc.Hom.comp O t
              (FreeCoprodCompDisc.coprodInj O A'
                (fun a ↦ interpObj I O (K' a) X) a'))
            (congrArg (fun e ↦ (e f).1 X)
              (interpHomEquiv_mk I O (Sum.inl o) d (K' a'))).symm)))

/-- The `σ`-domain case of the `IR.sigmaPush` characterization:
componentwise by the inductive hypotheses, then the cotuple
compatibility. -/
theorem interpHom_sigmaPush_mk_sigma (A : Type (max uA uB))
    (d : Direction I O (Sum.inr (Sum.inl A) : Shape.{max uA uB, uB, uO} O) →
      IR.{max uA uB, uB, uI, uO} I O)
    (ih : (x : Direction I O (Sum.inr (Sum.inl A) : Shape.{max uA uB, uB, uO} O)) →
      InterpHomSigmaPushMotive I O (d x)) :
    InterpHomSigmaPushMotive I O (mk I O (Sum.inr (Sum.inl A)) d) :=
  fun A' K' a' f X ↦
    (congrArg
        (fun t ↦ (interpHom I O (mk I O (Sum.inr (Sum.inl A)) d)
          (sigma I O A' K') t).1 X)
        (sigmaPush_mk_sigma I O A d A' K' a' f)).trans
      ((interpHom_sigma I O A (fun a ↦ d (ULift.up a)) (sigma I O A' K')
          (fun b ↦ sigmaPush I O (d (ULift.up b)) A' K' a' (f b)) X).trans
        ((congrArg
            (FreeCoprodCompDisc.coprodDesc O A
              (fun a ↦ interpObj I O (d (ULift.up a)) X)
              (interpObj I O (sigma I O A' K') X))
            (funext (fun b ↦ ih (ULift.up b) A' K' a' (f b) X))).trans
          ((FreeCoprodCompDisc.coprodDesc_comp O A
              (fun a ↦ interpObj I O (d (ULift.up a)) X)
              (interpObj I O (K' a') X) (interpObj I O (sigma I O A' K') X)
              (fun b ↦ (interpHom I O (d (ULift.up b)) (K' a') (f b)).1 X)
              (FreeCoprodCompDisc.coprodInj O A'
                (fun a ↦ interpObj I O (K' a) X) a')).symm.trans
            (congrArg
              (fun t ↦ FreeCoprodCompDisc.Hom.comp O t
                (FreeCoprodCompDisc.coprodInj O A'
                  (fun a ↦ interpObj I O (K' a) X) a'))
              (interpHom_sigma I O A (fun a ↦ d (ULift.up a))
                (K' a') f X).symm))))

/-- The Lemma 4 `σ`-square: the isomorphism of `IR.interpPrecompIso`
at a `σ`-code commutes the lifted-summand injection with the direct
summand injection. -/
theorem interpPrecompIso_sigma_inj (A' : Type (max uA uB))
    (K' : A' → IR.{max uA uB, uB, uI, uO} I O) (a' : A')
    (Q : Type uB) (q : Q → I) (k : FreeCoprodCompDisc.{max uA uB, uI} I) :
    FreeCoprodCompDisc.Hom.comp O
        (FreeCoprodCompDisc.coprodInj O (ULift.{uB} A')
          (fun x ↦ interpObj I O (precomp I O Q q (K' x.down)) k)
          (ULift.up a'))
        (FreeCoprodCompDisc.Iso.hom O
          (interpPrecompIso I O (sigma I O A' K') Q q k)) =
      FreeCoprodCompDisc.Hom.comp O
        (FreeCoprodCompDisc.Iso.hom O (interpPrecompIso I O (K' a') Q q k))
        (FreeCoprodCompDisc.coprodInj O A'
          (fun a ↦ interpObj I O (K' a)
            (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Q, q⟩ k)) a') :=
  (congrArg
      (fun t ↦ FreeCoprodCompDisc.Hom.comp O
        (FreeCoprodCompDisc.coprodInj O (ULift.{uB} A')
          (fun x ↦ interpObj I O (precomp I O Q q (K' x.down)) k)
          (ULift.up a'))
        (FreeCoprodCompDisc.Iso.hom O (t Q q k)))
      (interpPrecompIso_mk I O (Sum.inr (Sum.inl A')) (K' ∘ ULift.down))).trans
    (Subtype.ext (funext (fun _ ↦ rfl)))

/-- The transported-composite equation behind the `δ`-domain case: a
`σ`-injection pushed through the Lemma 4 isomorphism and the bridge
factors out of the transported composite. -/
theorem interpHomDeltaSummand_theta (B : Type uB)
    (c : (B → I) → IR.{max uA uB, uB, uI, uO} I O)
    (A' : Type (max uA uB)) (K' : A' → IR.{max uA uB, uB, uI, uO} I O)
    (a' : A') (i : B → I)
    (u : Hom.{uA, uB, uI, uO} I O (c i) (precomp I O B i (sigma I O A' K')))
    (v : Hom.{uA, uB, uI, uO} I O (c i) (precomp I O B i (K' a')))
    (X : FreeCoprodCompDisc.{max uA uB, uI} I)
    (hu : (interpHom I O (c i) (precomp I O B i (sigma I O A' K')) u).1 X =
      FreeCoprodCompDisc.Hom.comp O
        ((interpHom I O (c i) (precomp I O B i (K' a')) v).1 X)
        (FreeCoprodCompDisc.coprodInj O (ULift.{uB} A')
          (fun x ↦ interpObj I O (precomp I O B i (K' x.down)) X)
          (ULift.up a'))) :
    FreeCoprodCompDisc.Hom.comp O
        (FreeCoprodCompDisc.Hom.comp O
          ((interpHom I O (c i) (precomp I O B i (sigma I O A' K')) u).1 X)
          (FreeCoprodCompDisc.Iso.hom O
            (interpPrecompIso I O (sigma I O A' K') B i X)))
        ((plusLiftBridgeNatInv I O B i (sigma I O A' K')).1 X) =
      FreeCoprodCompDisc.Hom.comp O
        (FreeCoprodCompDisc.Hom.comp O
          (FreeCoprodCompDisc.Hom.comp O
            ((interpHom I O (c i) (precomp I O B i (K' a')) v).1 X)
            (FreeCoprodCompDisc.Iso.hom O
              (interpPrecompIso I O (K' a') B i X)))
          ((plusLiftBridgeNatInv I O B i (K' a')).1 X))
        (FreeCoprodCompDisc.coprodInj O A'
          (fun a ↦ interpObj I O (K' a)
            (FreeCoprodCompDisc.plus I
              (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) X))
          a') :=
  (congrArg
      (fun t ↦ FreeCoprodCompDisc.Hom.comp O
        (FreeCoprodCompDisc.Hom.comp O t
          (FreeCoprodCompDisc.Iso.hom O
            (interpPrecompIso I O (sigma I O A' K') B i X)))
        ((plusLiftBridgeNatInv I O B i (sigma I O A' K')).1 X))
      hu).trans
    ((congrArg
        (fun t ↦ FreeCoprodCompDisc.Hom.comp O t
          ((plusLiftBridgeNatInv I O B i (sigma I O A' K')).1 X))
        ((FreeCoprodCompDisc.Hom.comp_assoc O
            ((interpHom I O (c i) (precomp I O B i (K' a')) v).1 X)
            (FreeCoprodCompDisc.coprodInj O (ULift.{uB} A')
              (fun x ↦ interpObj I O (precomp I O B i (K' x.down)) X)
              (ULift.up a'))
            (FreeCoprodCompDisc.Iso.hom O
              (interpPrecompIso I O (sigma I O A' K') B i X))).trans
          ((congrArg
              (FreeCoprodCompDisc.Hom.comp O
                ((interpHom I O (c i) (precomp I O B i (K' a')) v).1 X))
              (interpPrecompIso_sigma_inj I O A' K' a' B i X)).trans
            (FreeCoprodCompDisc.Hom.comp_assoc O
              ((interpHom I O (c i) (precomp I O B i (K' a')) v).1 X)
              (FreeCoprodCompDisc.Iso.hom O
                (interpPrecompIso I O (K' a') B i X))
              (FreeCoprodCompDisc.coprodInj O A'
                (fun a ↦ interpObj I O (K' a)
                  (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨B, i⟩ X))
                a')).symm))).trans
      ((FreeCoprodCompDisc.Hom.comp_assoc O
          (FreeCoprodCompDisc.Hom.comp O
            ((interpHom I O (c i) (precomp I O B i (K' a')) v).1 X)
            (FreeCoprodCompDisc.Iso.hom O
              (interpPrecompIso I O (K' a') B i X)))
          (FreeCoprodCompDisc.coprodInj O A'
            (fun a ↦ interpObj I O (K' a)
              (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨B, i⟩ X)) a')
          ((plusLiftBridgeNatInv I O B i (sigma I O A' K')).1 X)).trans
        ((congrArg
            (FreeCoprodCompDisc.Hom.comp O
              (FreeCoprodCompDisc.Hom.comp O
                ((interpHom I O (c i) (precomp I O B i (K' a')) v).1 X)
                (FreeCoprodCompDisc.Iso.hom O
                  (interpPrecompIso I O (K' a') B i X))))
            (interpMor_sigma_inj I O A' K' a'
              (FreeCoprodCompDisc.plus I ⟨B, i⟩ X)
              (FreeCoprodCompDisc.plus I
                (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) X)
              (plusLiftBridgeInvHom I B i X))).trans
          (FreeCoprodCompDisc.Hom.comp_assoc O
            (FreeCoprodCompDisc.Hom.comp O
              ((interpHom I O (c i) (precomp I O B i (K' a')) v).1 X)
              (FreeCoprodCompDisc.Iso.hom O
                (interpPrecompIso I O (K' a') B i X)))
            ((plusLiftBridgeNatInv I O B i (K' a')).1 X)
            (FreeCoprodCompDisc.coprodInj O A'
              (fun a ↦ interpObj I O (K' a)
                (FreeCoprodCompDisc.plus I
                  (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) X))
              a')).symm)))

/-- The per-summand transport of a `σ`-injection through the `δ`-case
target transports, given the summand's own push equation. -/
theorem interpHomDeltaSummand_inj (B : Type uB)
    (c : (B → I) → IR.{max uA uB, uB, uI, uO} I O)
    (A' : Type (max uA uB)) (K' : A' → IR.{max uA uB, uB, uI, uO} I O)
    (a' : A') (i : B → I)
    (u : Hom.{uA, uB, uI, uO} I O (c i) (precomp I O B i (sigma I O A' K')))
    (v : Hom.{uA, uB, uI, uO} I O (c i) (precomp I O B i (K' a')))
    (X : FreeCoprodCompDisc.{max uA uB, uI} I)
    (hu : (interpHom I O (c i) (precomp I O B i (sigma I O A' K')) u).1 X =
      FreeCoprodCompDisc.Hom.comp O
        ((interpHom I O (c i) (precomp I O B i (K' a')) v).1 X)
        (FreeCoprodCompDisc.coprodInj O (ULift.{uB} A')
          (fun x ↦ interpObj I O (precomp I O B i (K' x.down)) X)
          (ULift.up a'))) :
    (interpHomDeltaSummand I O B c (sigma I O A' K') i u).1 X =
      FreeCoprodCompDisc.Hom.comp O
        ((interpHomDeltaSummand I O B c (K' a') i v).1 X)
        (FreeCoprodCompDisc.coprodInj O A'
          (fun a ↦ interpObj I O (K' a) X) a') :=
  (congrArg
      (FreeCoprodCompDisc.coprodDesc O
        (FreeCoprodCompDisc.Hom I
          (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) X)
        (fun _ ↦ interpObj I O (c i) X)
        (interpObj I O (sigma I O A' K') X))
      (funext (fun e ↦
        (congrArg
            (fun t ↦ FreeCoprodCompDisc.Hom.comp O t
              (interpMor I O (sigma I O A' K')
                (FreeCoprodCompDisc.plus I
                  (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) X)
                X
                (FreeCoprodCompDisc.coprodPairDesc I e
                  (FreeCoprodCompDisc.Hom.id I X))))
            (interpHomDeltaSummand_theta I O B c A' K' a' i u v X hu)).trans
          ((FreeCoprodCompDisc.Hom.comp_assoc O
              (FreeCoprodCompDisc.Hom.comp O
                (FreeCoprodCompDisc.Hom.comp O
                  ((interpHom I O (c i) (precomp I O B i (K' a')) v).1 X)
                  (FreeCoprodCompDisc.Iso.hom O
                    (interpPrecompIso I O (K' a') B i X)))
                ((plusLiftBridgeNatInv I O B i (K' a')).1 X))
              (FreeCoprodCompDisc.coprodInj O A'
                (fun a ↦ interpObj I O (K' a)
                  (FreeCoprodCompDisc.plus I
                    (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) X))
                a')
              (interpMor I O (sigma I O A' K')
                (FreeCoprodCompDisc.plus I
                  (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) X)
                X
                (FreeCoprodCompDisc.coprodPairDesc I e
                  (FreeCoprodCompDisc.Hom.id I X)))).trans
            ((congrArg
                (FreeCoprodCompDisc.Hom.comp O
                  (FreeCoprodCompDisc.Hom.comp O
                    (FreeCoprodCompDisc.Hom.comp O
                      ((interpHom I O (c i) (precomp I O B i (K' a')) v).1 X)
                      (FreeCoprodCompDisc.Iso.hom O
                        (interpPrecompIso I O (K' a') B i X)))
                    ((plusLiftBridgeNatInv I O B i (K' a')).1 X)))
                (interpMor_sigma_inj I O A' K' a'
                  (FreeCoprodCompDisc.plus I
                    (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) X)
                  X
                  (FreeCoprodCompDisc.coprodPairDesc I e
                    (FreeCoprodCompDisc.Hom.id I X)))).trans
              (FreeCoprodCompDisc.Hom.comp_assoc O
                (FreeCoprodCompDisc.Hom.comp O
                  (FreeCoprodCompDisc.Hom.comp O
                    ((interpHom I O (c i) (precomp I O B i (K' a')) v).1 X)
                    (FreeCoprodCompDisc.Iso.hom O
                      (interpPrecompIso I O (K' a') B i X)))
                  ((plusLiftBridgeNatInv I O B i (K' a')).1 X))
                (interpMor I O (K' a')
                  (FreeCoprodCompDisc.plus I
                    (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) X)
                  X
                  (FreeCoprodCompDisc.coprodPairDesc I e
                    (FreeCoprodCompDisc.Hom.id I X)))
                (FreeCoprodCompDisc.coprodInj O A'
                  (fun a ↦ interpObj I O (K' a) X) a')).symm))))).trans
    (FreeCoprodCompDisc.coprodDesc_comp O
        (FreeCoprodCompDisc.Hom I
          (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) X)
        (fun _ ↦ interpObj I O (c i) X) (interpObj I O (K' a') X)
        (interpObj I O (sigma I O A' K') X)
        (fun e ↦ FreeCoprodCompDisc.Hom.comp O
          (FreeCoprodCompDisc.Hom.comp O
            (FreeCoprodCompDisc.Hom.comp O
              ((interpHom I O (c i) (precomp I O B i (K' a')) v).1 X)
              (FreeCoprodCompDisc.Iso.hom O
                (interpPrecompIso I O (K' a') B i X)))
            ((plusLiftBridgeNatInv I O B i (K' a')).1 X))
          (interpMor I O (K' a')
            (FreeCoprodCompDisc.plus I
              (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) X) X
            (FreeCoprodCompDisc.coprodPairDesc I e
              (FreeCoprodCompDisc.Hom.id I X))))
        (FreeCoprodCompDisc.coprodInj O A'
          (fun a ↦ interpObj I O (K' a) X) a')).symm

/-- The `δ`-domain case of the `IR.sigmaPush` characterization. -/
theorem interpHom_sigmaPush_mk_delta (B : Type uB)
    (d : Direction I O (Sum.inr (Sum.inr B) : Shape.{max uA uB, uB, uO} O) →
      IR.{max uA uB, uB, uI, uO} I O)
    (ih : (x : Direction I O (Sum.inr (Sum.inr B) : Shape.{max uA uB, uB, uO} O)) →
      InterpHomSigmaPushMotive I O (d x)) :
    InterpHomSigmaPushMotive I O (mk I O (Sum.inr (Sum.inr B)) d) :=
  fun A' K' a' f X ↦
    (congrArg
        (fun t ↦ (interpHom I O (mk I O (Sum.inr (Sum.inr B)) d)
          (sigma I O A' K') t).1 X)
        (sigmaPush_mk_delta I O B d A' K' a' f)).trans
      ((interpHom_delta I O B (fun j ↦ d (ULift.up j)) (sigma I O A' K')
          (fun i ↦ sigmaPush I O (d (ULift.up i)) (ULift.{uB} A')
            (fun x ↦ precomp I O B i (K' x.down)) (ULift.up a') (f i)) X).trans
        ((congrArg
            (deltaDesc I O B (fun j ↦ d (ULift.up j)) X
              (interpObj I O (sigma I O A' K') X))
            (funext (fun i ↦
              interpHomDeltaSummand_inj I O B (fun j ↦ d (ULift.up j))
                A' K' a' i
                (sigmaPush I O (d (ULift.up i)) (ULift.{uB} A')
                  (fun x ↦ precomp I O B i (K' x.down)) (ULift.up a') (f i))
                (f i) X
                (ih (ULift.up i) (ULift.{uB} A')
                  (fun x ↦ precomp I O B i (K' x.down)) (ULift.up a')
                  (f i) X)))).trans
          ((deltaDesc_comp I O B (fun j ↦ d (ULift.up j)) X
              (interpObj I O (K' a') X) (interpObj I O (sigma I O A' K') X)
              (fun i ↦ (interpHomDeltaSummand I O B (fun j ↦ d (ULift.up j))
                (K' a') i (f i)).1 X)
              (FreeCoprodCompDisc.coprodInj O A'
                (fun a ↦ interpObj I O (K' a) X) a')).symm.trans
            (congrArg
              (fun t ↦ FreeCoprodCompDisc.Hom.comp O t
                (FreeCoprodCompDisc.coprodInj O A'
                  (fun a ↦ interpObj I O (K' a) X) a'))
              (interpHom_delta I O B (fun j ↦ d (ULift.up j))
                (K' a') f X).symm))))

/-- `IR.interpHom` sends `IR.sigmaPush` to composition with the
semantic `σ`-injection, by `IR.induction`. -/
theorem interpHom_sigmaPush (γ : IR.{max uA uB, uB, uI, uO} I O) :
    InterpHomSigmaPushMotive I O γ :=
  induction I O (InterpHomSigmaPushMotive I O)
    (fun s ↦ match s with
      | Sum.inl o => fun d _ ↦ interpHom_sigmaPush_mk_iota I O o d
      | Sum.inr (Sum.inl A) => fun d ih ↦ interpHom_sigmaPush_mk_sigma I O A d ih
      | Sum.inr (Sum.inr B) => fun d ih ↦ interpHom_sigmaPush_mk_delta I O B d ih)
    γ

/-! ### The empty-`δ`-push characterization -/

/-- The canonical weight: the morphism out of the lift of an
empty-witnessed family given by elimination at every name. -/
def deltaEmptyWeight (E : Type uB) (e : E → PEmpty.{1})
    (X : FreeCoprodCompDisc.{max uA uB, uI} I) :
    FreeCoprodCompDisc.Hom I
      (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨E, fun x ↦ (e x).elim⟩) X :=
  ⟨fun z ↦ (e z.down).elim, funext (fun z ↦ (e z.down).elim)⟩

/-- The semantic inclusion of the empty-witnessed summand into the
`delta` interpretation: the copower injection at the canonical weight
followed by the summand inclusion `IR.deltaInto`. -/
def deltaEmptyInj (E : Type uB) (e : E → PEmpty.{1})
    (M : (E → I) → IR.{max uA uB, uB, uI, uO} I O)
    (X : FreeCoprodCompDisc.{max uA uB, uI} I) :
    FreeCoprodCompDisc.Hom O (interpObj I O (M (fun x ↦ (e x).elim)) X)
      (interpObj I O (delta I O E M) X) :=
  FreeCoprodCompDisc.Hom.comp O
    (FreeCoprodCompDisc.coprodInj O
      (FreeCoprodCompDisc.Hom I
        (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨E, fun x ↦ (e x).elim⟩) X)
      (fun _ ↦ interpObj I O (M (fun x ↦ (e x).elim)) X)
      (deltaEmptyWeight I E e X))
    (deltaInto I O E M (fun x ↦ (e x).elim) X)

/-- The generic injection square: the semantic empty-summand inclusion
commutes the morphism map of the `delta` interpretation with the
summand's. -/
theorem interpMor_deltaEmpty_inj (E : Type uB) (e : E → PEmpty.{1})
    (M : (E → I) → IR.{max uA uB, uB, uI, uO} I O)
    (Z W : FreeCoprodCompDisc.{max uA uB, uI} I)
    (h : FreeCoprodCompDisc.Hom I Z W) :
    FreeCoprodCompDisc.Hom.comp O (deltaEmptyInj I O E e M Z)
        (interpMor I O (delta I O E M) Z W h) =
      FreeCoprodCompDisc.Hom.comp O
        (interpMor I O (M (fun x ↦ (e x).elim)) Z W h)
        (deltaEmptyInj I O E e M W) :=
  (FreeCoprodCompDisc.Hom.comp_assoc O
      (FreeCoprodCompDisc.coprodInj O
        (FreeCoprodCompDisc.Hom I
          (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨E, fun x ↦ (e x).elim⟩) Z)
        (fun _ ↦ interpObj I O (M (fun x ↦ (e x).elim)) Z)
        (deltaEmptyWeight I E e Z))
      (deltaInto I O E M (fun x ↦ (e x).elim) Z)
      (interpMor I O (delta I O E M) Z W h)).trans
    ((congrArg
        (FreeCoprodCompDisc.Hom.comp O
          (FreeCoprodCompDisc.coprodInj O
            (FreeCoprodCompDisc.Hom I
              (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I
                ⟨E, fun x ↦ (e x).elim⟩) Z)
            (fun _ ↦ interpObj I O (M (fun x ↦ (e x).elim)) Z)
            (deltaEmptyWeight I E e Z)))
        (deltaInto_natural I O E M (fun x ↦ (e x).elim) Z W h).symm).trans
      ((FreeCoprodCompDisc.Hom.comp_assoc O
          (FreeCoprodCompDisc.coprodInj O
            (FreeCoprodCompDisc.Hom I
              (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I
                ⟨E, fun x ↦ (e x).elim⟩) Z)
            (fun _ ↦ interpObj I O (M (fun x ↦ (e x).elim)) Z)
            (deltaEmptyWeight I E e Z))
          (FreeCoprodCompDisc.copowerHomMapMor
            (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨E, fun x ↦ (e x).elim⟩)
            (interpMor I O (M (fun x ↦ (e x).elim))) Z W h)
          (deltaInto I O E M (fun x ↦ (e x).elim) W)).symm.trans
        ((congrArg
            (fun t ↦ FreeCoprodCompDisc.Hom.comp O t
              (deltaInto I O E M (fun x ↦ (e x).elim) W))
            (FreeCoprodCompDisc.coprodInj_mor O
              (FreeCoprodCompDisc.Hom I
                (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I
                  ⟨E, fun x ↦ (e x).elim⟩) Z)
              (FreeCoprodCompDisc.Hom I
                (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I
                  ⟨E, fun x ↦ (e x).elim⟩) W)
              (fun e' ↦ FreeCoprodCompDisc.Hom.comp I e' h)
              (fun _ ↦ interpObj I O (M (fun x ↦ (e x).elim)) Z)
              (fun _ ↦ interpObj I O (M (fun x ↦ (e x).elim)) W)
              (fun _ ↦ interpMor I O (M (fun x ↦ (e x).elim)) Z W h)
              (deltaEmptyWeight I E e Z))).trans
          ((congrArg
              (fun t ↦ FreeCoprodCompDisc.Hom.comp O
                (FreeCoprodCompDisc.Hom.comp O
                  (interpMor I O (M (fun x ↦ (e x).elim)) Z W h)
                  (FreeCoprodCompDisc.coprodInj O
                    (FreeCoprodCompDisc.Hom I
                      (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I
                        ⟨E, fun x ↦ (e x).elim⟩) W)
                    (fun _ ↦ interpObj I O (M (fun x ↦ (e x).elim)) W) t))
                (deltaInto I O E M (fun x ↦ (e x).elim) W))
              (FreeCoprodCompDisc.emptyHom_ext I E e W
                (FreeCoprodCompDisc.Hom.comp I (deltaEmptyWeight I E e Z) h)
                (deltaEmptyWeight I E e W))).trans
            (FreeCoprodCompDisc.Hom.comp_assoc O
              (interpMor I O (M (fun x ↦ (e x).elim)) Z W h)
              (FreeCoprodCompDisc.coprodInj O
                (FreeCoprodCompDisc.Hom I
                  (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I
                    ⟨E, fun x ↦ (e x).elim⟩) W)
                (fun _ ↦ interpObj I O (M (fun x ↦ (e x).elim)) W)
                (deltaEmptyWeight I E e W))
              (deltaInto I O E M (fun x ↦ (e x).elim) W))))))

/-- Transport of a summand interpretation along an equality of
assignments: the object-level `isoOfEq` agrees with the name-level
cast, for any proofs of the assignment equality. -/
theorem interpObj_isoOfEq_cast (E : Type uB)
    (M : (E → I) → IR.{max uA uB, uB, uI, uO} I O)
    (X : FreeCoprodCompDisc.{max uA uB, uI} I) (a : E → I) :
    ∀ (c : E → I) (s : a = c) (s' : a = c)
      (y : (interpObj I O (M a) X).1),
      (FreeCoprodCompDisc.isoOfEq O
          (congrArg (fun m ↦ interpObj I O (M m) X) s)).1 y =
        cast (congrArg (fun m ↦ (interpObj I O (M m) X).1) s') y :=
  fun _ s ↦
    Eq.rec (motive := fun c' s'' ↦ ∀ (s' : a = c')
        (y : (interpObj I O (M a) X).1),
        (FreeCoprodCompDisc.isoOfEq O
            (congrArg (fun m ↦ interpObj I O (M m) X) s'')).1 y =
          cast (congrArg (fun m ↦ (interpObj I O (M m) X).1) s') y)
      (fun _ _ ↦ rfl) s

/-- The transported summand isomorphism of the Lemma 4 `δ`-square at
the empty inclusion: the summand's Lemma 4 isomorphism followed by the
transport along the collapse of the merged assignment. -/
def deltaEmptySummandHom (E : Type uB) (e : E → PEmpty.{1})
    (M : (E → I) → IR.{max uA uB, uB, uI, uO} I O)
    (Q : Type uB) (q : Q → I) (k : FreeCoprodCompDisc.{max uA uB, uI} I) :
    FreeCoprodCompDisc.Hom O
      (interpObj I O
        (precomp I O Q q (M (precompMerge I Q q (fun x ↦ (e x).elim)
          (fun z : {z : E // (fun x ↦ (e x).elim : E → Q ⊕ PUnit.{uB + 1}) z =
              Sum.inr PUnit.unit} ↦
            (((e z.1).elim : PEmpty.{1}).elim : I))))) k)
      (interpObj I O (M (fun x ↦ (e x).elim))
        (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Q, q⟩ k)) :=
  FreeCoprodCompDisc.Hom.comp O
    (FreeCoprodCompDisc.Iso.hom O
      (interpPrecompIso I O
        (M (precompMerge I Q q (fun x ↦ (e x).elim)
          (fun z ↦ (((e z.1).elim : PEmpty.{1}).elim : I)))) Q q k))
    (FreeCoprodCompDisc.Iso.hom O
      (FreeCoprodCompDisc.isoOfEq O
        (congrArg
          (fun a ↦ interpObj I O (M a)
            (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Q, q⟩ k))
          (funext (fun x ↦ (e x).elim) :
            (fun x ↦ ((e x).elim : I)) =
              precompMerge I Q q (fun x ↦ (e x).elim)
                (fun z ↦ (((e z.1).elim : PEmpty.{1}).elim : I))).symm)))

/-- The name-level computation of the Lemma 4 `δ`-square at the empty
inclusion, with every empty-derived assignment equality generalized:
both routes transport the summand's Lemma 4 image along propositionally
equal paths, identified by proof irrelevance at the base. -/
theorem deltaEmpty_strip (E : Type uB) (e : E → PEmpty.{1})
    (M : (E → I) → IR.{max uA uB, uB, uI, uO} I O)
    (Q : Type uB) (q : Q → I) (k : FreeCoprodCompDisc.{max uA uB, uI} I) :
    ∀ (j' : {z : E // (fun x ↦ (e x).elim : E → Q ⊕ PUnit.{uB + 1}) z =
        Sum.inr PUnit.unit} → I)
      (hj : (fun z : {z : E // (fun x ↦ (e x).elim : E → Q ⊕ PUnit.{uB + 1}) z =
          Sum.inr PUnit.unit} ↦ (((e z.1).elim : PEmpty.{1}).elim : I)) = j')
      (w₁ : E → Q ⊕ k.1)
      (s₁ : precompMerge I Q q (fun x ↦ (e x).elim) j' = Sum.elim q k.2 ∘ w₁)
      (w₂ : E → Q ⊕ k.1) (_hw : w₁ = w₂)
      (b₂ : E → I)
      (r₂ : precompMerge I Q q (fun x ↦ (e x).elim)
          (fun z ↦ (((e z.1).elim : PEmpty.{1}).elim : I)) = b₂)
      (s₂ : b₂ = Sum.elim q k.2 ∘ w₂)
      (n : (interpObj I O (precomp I O Q q (M (precompMerge I Q q
        (fun x ↦ (e x).elim)
        (fun z ↦ (((e z.1).elim : PEmpty.{1}).elim : I))))) k).1),
      (⟨w₁, (FreeCoprodCompDisc.isoOfEq O
          (congrArg (fun m ↦ interpObj I O (M m)
            (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Q, q⟩ k)) s₁)).1
          ((FreeCoprodCompDisc.Iso.hom O
            (interpPrecompIso I O
              (M (precompMerge I Q q (fun x ↦ (e x).elim) j')) Q q k)).1
            (cast (congrArg (fun t ↦ (interpObj I O (precomp I O Q q
              (M (precompMerge I Q q (fun x ↦ (e x).elim) t))) k).1) hj) n))⟩ :
        (interpObj I O (delta I O E M)
          (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Q, q⟩ k)).1) =
      ⟨w₂, cast (congrArg (fun m ↦ (interpObj I O (M m)
          (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Q, q⟩ k)).1) s₂)
        ((FreeCoprodCompDisc.isoOfEq O
          (congrArg (fun m ↦ interpObj I O (M m)
            (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Q, q⟩ k)) r₂)).1
          ((FreeCoprodCompDisc.Iso.hom O
            (interpPrecompIso I O (M (precompMerge I Q q (fun x ↦ (e x).elim)
              (fun z ↦ (((e z.1).elim : PEmpty.{1}).elim : I)))) Q q k)).1 n))⟩ :=
  fun _ hj ↦
    Eq.rec (motive := fun j'' hj' ↦ ∀ (w₁ : E → Q ⊕ k.1)
        (s₁ : precompMerge I Q q (fun x ↦ (e x).elim) j'' = Sum.elim q k.2 ∘ w₁)
        (w₂ : E → Q ⊕ k.1) (_hw : w₁ = w₂) (b₂ : E → I)
        (r₂ : precompMerge I Q q (fun x ↦ (e x).elim)
            (fun z ↦ (((e z.1).elim : PEmpty.{1}).elim : I)) = b₂)
        (s₂ : b₂ = Sum.elim q k.2 ∘ w₂)
        (n : (interpObj I O (precomp I O Q q (M (precompMerge I Q q
          (fun x ↦ (e x).elim)
          (fun z ↦ (((e z.1).elim : PEmpty.{1}).elim : I))))) k).1),
        (⟨w₁, (FreeCoprodCompDisc.isoOfEq O
            (congrArg (fun m ↦ interpObj I O (M m)
              (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Q, q⟩ k)) s₁)).1
            ((FreeCoprodCompDisc.Iso.hom O
              (interpPrecompIso I O
                (M (precompMerge I Q q (fun x ↦ (e x).elim) j'')) Q q k)).1
              (cast (congrArg (fun t ↦ (interpObj I O (precomp I O Q q
                (M (precompMerge I Q q (fun x ↦ (e x).elim) t))) k).1) hj') n))⟩ :
          (interpObj I O (delta I O E M)
            (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Q, q⟩ k)).1) =
        ⟨w₂, cast (congrArg (fun m ↦ (interpObj I O (M m)
            (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Q, q⟩ k)).1) s₂)
          ((FreeCoprodCompDisc.isoOfEq O
            (congrArg (fun m ↦ interpObj I O (M m)
              (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Q, q⟩ k)) r₂)).1
            ((FreeCoprodCompDisc.Iso.hom O
              (interpPrecompIso I O (M (precompMerge I Q q (fun x ↦ (e x).elim)
                (fun z ↦ (((e z.1).elim : PEmpty.{1}).elim : I)))) Q q k)).1
              n))⟩)
      (fun w₁ s₁ _ hw ↦
        Eq.rec (motive := fun w₂' _ ↦ ∀ (b₂ : E → I)
            (r₂ : precompMerge I Q q (fun x ↦ (e x).elim)
                (fun z ↦ (((e z.1).elim : PEmpty.{1}).elim : I)) = b₂)
            (s₂ : b₂ = Sum.elim q k.2 ∘ w₂')
            (n : (interpObj I O (precomp I O Q q (M (precompMerge I Q q
              (fun x ↦ (e x).elim)
              (fun z ↦ (((e z.1).elim : PEmpty.{1}).elim : I))))) k).1),
            (⟨w₁, (FreeCoprodCompDisc.isoOfEq O
                (congrArg (fun m ↦ interpObj I O (M m)
                  (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Q, q⟩ k)) s₁)).1
                ((FreeCoprodCompDisc.Iso.hom O
                  (interpPrecompIso I O (M (precompMerge I Q q
                    (fun x ↦ (e x).elim)
                    (fun z ↦ (((e z.1).elim : PEmpty.{1}).elim : I)))) Q q k)).1
                  n)⟩ :
              (interpObj I O (delta I O E M)
                (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Q, q⟩ k)).1) =
            ⟨w₂', cast (congrArg (fun m ↦ (interpObj I O (M m)
                (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Q, q⟩ k)).1) s₂)
              ((FreeCoprodCompDisc.isoOfEq O
                (congrArg (fun m ↦ interpObj I O (M m)
                  (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Q, q⟩ k)) r₂)).1
                ((FreeCoprodCompDisc.Iso.hom O
                  (interpPrecompIso I O (M (precompMerge I Q q
                    (fun x ↦ (e x).elim)
                    (fun z ↦ (((e z.1).elim : PEmpty.{1}).elim : I)))) Q q k)).1
                  n))⟩)
          (fun _ r₂ ↦
            Eq.rec (motive := fun b₂' r₂' ↦ ∀ (s₂ : b₂' = Sum.elim q k.2 ∘ w₁)
                (n : (interpObj I O (precomp I O Q q (M (precompMerge I Q q
                  (fun x ↦ (e x).elim)
                  (fun z ↦ (((e z.1).elim : PEmpty.{1}).elim : I))))) k).1),
                (⟨w₁, (FreeCoprodCompDisc.isoOfEq O
                    (congrArg (fun m ↦ interpObj I O (M m)
                      (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Q, q⟩ k))
                      s₁)).1
                    ((FreeCoprodCompDisc.Iso.hom O
                      (interpPrecompIso I O (M (precompMerge I Q q
                        (fun x ↦ (e x).elim)
                        (fun z ↦ (((e z.1).elim : PEmpty.{1}).elim : I))))
                        Q q k)).1 n)⟩ :
                  (interpObj I O (delta I O E M)
                    (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Q, q⟩ k)).1) =
                ⟨w₁, cast (congrArg (fun m ↦ (interpObj I O (M m)
                    (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Q, q⟩ k)).1)
                    s₂)
                  ((FreeCoprodCompDisc.isoOfEq O
                    (congrArg (fun m ↦ interpObj I O (M m)
                      (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Q, q⟩ k))
                      r₂')).1
                    ((FreeCoprodCompDisc.Iso.hom O
                      (interpPrecompIso I O (M (precompMerge I Q q
                        (fun x ↦ (e x).elim)
                        (fun z ↦ (((e z.1).elim : PEmpty.{1}).elim : I))))
                        Q q k)).1 n))⟩)
              (fun s₂ n ↦
                congrArg
                  (fun t ↦ (⟨w₁, t⟩ :
                    (interpObj I O (delta I O E M)
                      (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I
                        ⟨Q, q⟩ k)).1))
                  (interpObj_isoOfEq_cast I O E M
                    (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Q, q⟩ k)
                    (precompMerge I Q q (fun x ↦ (e x).elim)
                      (fun z ↦ (((e z.1).elim : PEmpty.{1}).elim : I)))
                    (Sum.elim q k.2 ∘ w₁) s₁ s₂
                    ((FreeCoprodCompDisc.Iso.hom O
                      (interpPrecompIso I O (M (precompMerge I Q q
                        (fun x ↦ (e x).elim)
                        (fun z ↦ (((e z.1).elim : PEmpty.{1}).elim : I))))
                        Q q k)).1 n)))
              r₂)
          hw)
      hj

/-- The Lemma 4 `δ`-square at the empty inclusion: the syntactic
injection at the precomposed level, pushed through the Lemma 4
isomorphism, is the transported summand isomorphism followed by the
semantic empty-summand inclusion at the coproduct object. -/
theorem interpPrecompIso_deltaEmpty_inj (E : Type uB) (e : E → PEmpty.{1})
    (M : (E → I) → IR.{max uA uB, uB, uI, uO} I O)
    (Q : Type uB) (q : Q → I) (k : FreeCoprodCompDisc.{max uA uB, uI} I) :
    FreeCoprodCompDisc.Hom.comp O
        (FreeCoprodCompDisc.Hom.comp O
          (deltaEmptyInj I O
            {z : E // (fun x ↦ (e x).elim : E → Q ⊕ PUnit.{uB + 1}) z =
              Sum.inr PUnit.unit}
            (fun z ↦ (e z.1).elim)
            (fun j ↦ precomp I O Q q
              (M (precompMerge I Q q (fun x ↦ (e x).elim) j)))
            k)
          (FreeCoprodCompDisc.coprodInj O
            (ULift.{max uA uB} (E → Q ⊕ PUnit.{uB + 1}))
            (fun cl ↦ interpObj I O
              (delta I O {z : E // cl.down z = Sum.inr PUnit.unit}
                (fun j ↦ precomp I O Q q
                  (M (precompMerge I Q q cl.down j)))) k)
            (ULift.up (fun x ↦ (e x).elim))))
        (FreeCoprodCompDisc.Iso.hom O
          (interpPrecompIso I O (delta I O E M) Q q k)) =
      FreeCoprodCompDisc.Hom.comp O (deltaEmptySummandHom I O E e M Q q k)
        (deltaEmptyInj I O E e M
          (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Q, q⟩ k)) :=
  (congrArg
      (fun t ↦ FreeCoprodCompDisc.Hom.comp O
        (FreeCoprodCompDisc.Hom.comp O
          (deltaEmptyInj I O
            {z : E // (fun x ↦ (e x).elim : E → Q ⊕ PUnit.{uB + 1}) z =
              Sum.inr PUnit.unit}
            (fun z ↦ (e z.1).elim)
            (fun j ↦ precomp I O Q q
              (M (precompMerge I Q q (fun x ↦ (e x).elim) j)))
            k)
          (FreeCoprodCompDisc.coprodInj O
            (ULift.{max uA uB} (E → Q ⊕ PUnit.{uB + 1}))
            (fun cl ↦ interpObj I O
              (delta I O {z : E // cl.down z = Sum.inr PUnit.unit}
                (fun j ↦ precomp I O Q q
                  (M (precompMerge I Q q cl.down j)))) k)
            (ULift.up (fun x ↦ (e x).elim))))
        (FreeCoprodCompDisc.Iso.hom O (t Q q k)))
      (interpPrecompIso_mk I O (Sum.inr (Sum.inr E)) (M ∘ ULift.down))).trans
    (Subtype.ext (funext (fun n ↦
      deltaEmpty_strip I O E e M Q q k
        (fun z ↦ k.2 (((e z.1).elim : PEmpty.{1}).elim))
        (funext (fun z ↦ (e z.1).elim))
        (arrowSumMerge (fun x ↦ (e x).elim)
          (fun z ↦ (((e z.1).elim : PEmpty.{1}).elim : k.1)))
        (precompMerge_elim I Q q k E (fun x ↦ (e x).elim)
          (fun z ↦ (((e z.1).elim : PEmpty.{1}).elim : k.1)))
        (fun x ↦ ((e x).elim : Q ⊕ k.1))
        (funext (fun x ↦ (e x).elim))
        (fun x ↦ ((e x).elim : I))
        (funext (fun x ↦ (e x).elim)).symm
        (funext (fun x ↦ (e x).elim))
        n)))

/-- The statement of the `IR.deltaEmptyPush` characterization at one
code: `IR.interpHom` sends a pushed morphism to the composite with the
semantic empty-summand inclusion. -/
def InterpHomDeltaEmptyPushMotive (γ : IR.{max uA uB, uB, uI, uO} I O) : Prop :=
  ∀ (E : Type uB) (e : E → PEmpty.{1})
    (M : (E → I) → IR.{max uA uB, uB, uI, uO} I O)
    (f : Hom.{uA, uB, uI, uO} I O γ (M (fun x ↦ (e x).elim)))
    (X : FreeCoprodCompDisc.{max uA uB, uI} I),
    (interpHom I O γ (delta I O E M) (deltaEmptyPush I O γ E e M f)).1 X =
      FreeCoprodCompDisc.Hom.comp O
        ((interpHom I O γ (M (fun x ↦ (e x).elim)) f).1 X)
        (deltaEmptyInj I O E e M X)

/-- The name component of `IR.innerHomEquivCast` at an empty-witnessed
direction, as a cast of the untransported name, for any proofs of the
assignment equality. -/
theorem innerHomEquivCast_fst_cast (o : O) (E : Type uB) (e : E → PEmpty.{1})
    (M : (E → I) → IR.{max uA uB, uB, uI, uO} I O) :
    ∀ (j : E → I) (pf : (fun b ↦ ((e b).elim : I)) = j)
      (h' : (fun b ↦ ((e b).elim : I)) = j)
      (f : InnerHom.{uA, uB, uI, uO} I O o (M (fun b ↦ (e b).elim))),
      ((innerHomEquivCast I O o E (M ∘ ULift.down)
          (fun x ↦ innerHomEquiv I O o ((M ∘ ULift.down) x))
          (fun b ↦ (e b).elim) j pf) f).1 =
        cast
          (congrArg
            (fun t ↦ (interpObj I O (M t) (FreeCoprodCompDisc.emptyObj I)).1) h')
          ((innerHomEquiv I O o (M (fun b ↦ (e b).elim)) f).1) :=
  fun _ pf ↦
    Eq.rec (motive := fun j' pf' ↦ ∀ (h' : (fun b ↦ ((e b).elim : I)) = j')
        (f : InnerHom.{uA, uB, uI, uO} I O o (M (fun b ↦ (e b).elim))),
        ((innerHomEquivCast I O o E (M ∘ ULift.down)
            (fun x ↦ innerHomEquiv I O o ((M ∘ ULift.down) x))
            (fun b ↦ (e b).elim) j' pf') f).1 =
          cast
            (congrArg
              (fun t ↦ (interpObj I O (M t)
                (FreeCoprodCompDisc.emptyObj I)).1) h')
            ((innerHomEquiv I O o (M (fun b ↦ (e b).elim)) f).1))
      (fun _ _ ↦ rfl) pf

/-- The singleton morphism at the empty-witnessed `δ`-name factors
through the semantic empty-summand inclusion. -/
theorem homSingletonEquiv_symm_deltaEmptyInj (o : O) (E : Type uB)
    (e : E → PEmpty.{1}) (M : (E → I) → IR.{max uA uB, uB, uI, uO} I O)
    (f : InnerHom.{uA, uB, uI, uO} I O o (M (fun x ↦ (e x).elim))) :
    (FreeCoprodCompDisc.homSingletonEquiv O o
        (interpObj I O (delta I O E M) (FreeCoprodCompDisc.emptyObj I))).symm
        (innerHomEquiv I O o (delta I O E M) ⟨e, f⟩) =
      FreeCoprodCompDisc.Hom.comp O
        ((FreeCoprodCompDisc.homSingletonEquiv O o
            (interpObj I O (M (fun x ↦ (e x).elim))
              (FreeCoprodCompDisc.emptyObj I))).symm
          (innerHomEquiv I O o (M (fun x ↦ (e x).elim)) f))
        (deltaEmptyInj I O E e M (FreeCoprodCompDisc.emptyObj I)) :=
  (congrArg
      (fun (t : InnerHom.{uA, uB, uI, uO} I O o (delta I O E M) ≃
          {z : (interpObj I O (delta I O E M)
              (FreeCoprodCompDisc.emptyObj I)).1 //
            (interpObj I O (delta I O E M)
              (FreeCoprodCompDisc.emptyObj I)).2 z = o}) ↦
        (FreeCoprodCompDisc.homSingletonEquiv O o
          (interpObj I O (delta I O E M)
            (FreeCoprodCompDisc.emptyObj I))).symm (t ⟨e, f⟩))
      (innerHomEquiv_mk I O o (Sum.inr (Sum.inr E)) (M ∘ ULift.down))).trans
    (Subtype.ext (funext (fun _ ↦
      congrArg
        (fun t ↦ (⟨fun x ↦ (e x).elim, t⟩ :
          (interpObj I O (delta I O E M) (FreeCoprodCompDisc.emptyObj I)).1))
        (innerHomEquivCast_fst_cast I O o E e M
          ((FreeCoprodCompDisc.emptyObj I).2 ∘ (fun b ↦ (e b).elim))
          (funext (fun b ↦ (e b).elim)) (funext (fun b ↦ (e b).elim)) f))))

/-- The empty-push equation for the transported `ι`-composite, by
elimination of the code equality: at the reflexive instance both sides
compute to singleton morphisms into the initial-object fiber, related
by `IR.homSingletonEquiv_symm_deltaEmptyInj` and the injection
square. -/
theorem interpHomIotaCast_deltaEmptyPush (o : O) (E : Type uB)
    (e : E → PEmpty.{1}) (M : (E → I) → IR.{max uA uB, uB, uI, uO} I O)
    (f : InnerHom.{uA, uB, uI, uO} I O o (M (fun x ↦ (e x).elim)))
    (X : FreeCoprodCompDisc.{max uA uB, uI} I)
    (ir : IR.{max uA uB, uB, uI, uO} I O)
    (eIr : iota.{max uA uB, uB, uI, uO} I O o = ir) :
    ((interpHomIotaCast I O o (delta I O E M) ir eIr) ⟨e, f⟩).1 X =
      FreeCoprodCompDisc.Hom.comp O
        (((interpHomIotaCast I O o (M (fun x ↦ (e x).elim)) ir eIr) f).1 X)
        (deltaEmptyInj I O E e M X) :=
  Eq.rec (motive := fun ir' eIr' ↦
      ((interpHomIotaCast I O o (delta I O E M) ir' eIr') ⟨e, f⟩).1 X =
        FreeCoprodCompDisc.Hom.comp O
          (((interpHomIotaCast I O o (M (fun x ↦ (e x).elim)) ir' eIr') f).1 X)
          (deltaEmptyInj I O E e M X))
    ((congrArg
        (fun t ↦ FreeCoprodCompDisc.Hom.comp O t
          (interpMor I O (delta I O E M) (FreeCoprodCompDisc.emptyObj I) X
            (FreeCoprodCompDisc.emptyDesc I X)))
        (homSingletonEquiv_symm_deltaEmptyInj I O o E e M f)).trans
      ((FreeCoprodCompDisc.Hom.comp_assoc O
            ((FreeCoprodCompDisc.homSingletonEquiv O o
                (interpObj I O (M (fun x ↦ (e x).elim))
                  (FreeCoprodCompDisc.emptyObj I))).symm
              (innerHomEquiv I O o (M (fun x ↦ (e x).elim)) f))
            (deltaEmptyInj I O E e M (FreeCoprodCompDisc.emptyObj I))
            (interpMor I O (delta I O E M) (FreeCoprodCompDisc.emptyObj I) X
              (FreeCoprodCompDisc.emptyDesc I X))).trans
          ((congrArg
              (FreeCoprodCompDisc.Hom.comp O
                ((FreeCoprodCompDisc.homSingletonEquiv O o
                    (interpObj I O (M (fun x ↦ (e x).elim))
                      (FreeCoprodCompDisc.emptyObj I))).symm
                  (innerHomEquiv I O o (M (fun x ↦ (e x).elim)) f)))
              (interpMor_deltaEmpty_inj I O E e M
                (FreeCoprodCompDisc.emptyObj I) X
                (FreeCoprodCompDisc.emptyDesc I X))).trans
            (FreeCoprodCompDisc.Hom.comp_assoc O
              ((FreeCoprodCompDisc.homSingletonEquiv O o
                  (interpObj I O (M (fun x ↦ (e x).elim))
                    (FreeCoprodCompDisc.emptyObj I))).symm
                (innerHomEquiv I O o (M (fun x ↦ (e x).elim)) f))
              (interpMor I O (M (fun x ↦ (e x).elim))
                (FreeCoprodCompDisc.emptyObj I) X
                (FreeCoprodCompDisc.emptyDesc I X))
              (deltaEmptyInj I O E e M X)).symm)))
    eIr

/-- The `ι`-case of the `IR.deltaEmptyPush` characterization. -/
theorem interpHom_deltaEmptyPush_mk_iota (o : O)
    (d : Direction I O (Sum.inl o : Shape.{max uA uB, uB, uO} O) →
      IR.{max uA uB, uB, uI, uO} I O) :
    InterpHomDeltaEmptyPushMotive I O (mk I O (Sum.inl o) d) :=
  fun E e M f X ↦
    (congrArg
        (fun t ↦ (interpHom I O (mk I O (Sum.inl o) d)
          (delta I O E M) t).1 X)
        (deltaEmptyPush_mk_iota I O o d E e M f)).trans
      ((congrArg (fun eq ↦ (eq (⟨e, f⟩ :
            InnerHom.{uA, uB, uI, uO} I O o (delta I O E M))).1 X)
          (interpHomEquiv_mk I O (Sum.inl o) d (delta I O E M))).trans
        ((interpHomIotaCast_deltaEmptyPush I O o E e M f X
            (mk I O (Sum.inl o) d)
            (mk_congr I O (Sum.inl o)
              (funext (fun x ↦ nomatch x)) :
                mk I O (Sum.inl o) PEmpty.elim = mk I O (Sum.inl o) d)).trans
          (congrArg
            (fun t ↦ FreeCoprodCompDisc.Hom.comp O t
              (deltaEmptyInj I O E e M X))
            (congrArg (fun eq ↦ (eq f).1 X)
              (interpHomEquiv_mk I O (Sum.inl o) d
                (M (fun x ↦ (e x).elim)))).symm)))

/-- The `σ`-domain case of the `IR.deltaEmptyPush` characterization:
componentwise by the inductive hypotheses, then the cotuple
compatibility. -/
theorem interpHom_deltaEmptyPush_mk_sigma (A : Type (max uA uB))
    (d : Direction I O (Sum.inr (Sum.inl A) : Shape.{max uA uB, uB, uO} O) →
      IR.{max uA uB, uB, uI, uO} I O)
    (ih : (x : Direction I O (Sum.inr (Sum.inl A) : Shape.{max uA uB, uB, uO} O)) →
      InterpHomDeltaEmptyPushMotive I O (d x)) :
    InterpHomDeltaEmptyPushMotive I O (mk I O (Sum.inr (Sum.inl A)) d) :=
  fun E e M f X ↦
    (congrArg
        (fun t ↦ (interpHom I O (mk I O (Sum.inr (Sum.inl A)) d)
          (delta I O E M) t).1 X)
        (deltaEmptyPush_mk_sigma I O A d E e M f)).trans
      ((interpHom_sigma I O A (fun a ↦ d (ULift.up a)) (delta I O E M)
          (fun b ↦ deltaEmptyPush I O (d (ULift.up b)) E e M (f b)) X).trans
        ((congrArg
            (FreeCoprodCompDisc.coprodDesc O A
              (fun a ↦ interpObj I O (d (ULift.up a)) X)
              (interpObj I O (delta I O E M) X))
            (funext (fun b ↦ ih (ULift.up b) E e M (f b) X))).trans
          ((FreeCoprodCompDisc.coprodDesc_comp O A
              (fun a ↦ interpObj I O (d (ULift.up a)) X)
              (interpObj I O (M (fun x ↦ (e x).elim)) X)
              (interpObj I O (delta I O E M) X)
              (fun b ↦ (interpHom I O (d (ULift.up b))
                (M (fun x ↦ (e x).elim)) (f b)).1 X)
              (deltaEmptyInj I O E e M X)).symm.trans
            (congrArg
              (fun t ↦ FreeCoprodCompDisc.Hom.comp O t
                (deltaEmptyInj I O E e M X))
              (interpHom_sigma I O A (fun a ↦ d (ULift.up a))
                (M (fun x ↦ (e x).elim)) f X).symm))))

/-- Elimination of the assignment cast in the `δ`-domain step of
`IR.deltaEmptyPush`: composing the transported morphism's
interpretation with the transported summand isomorphism recovers the
untransported composite. -/
theorem interpHom_deltaEmptySummand_cast (γ : IR.{max uA uB, uB, uI, uO} I O)
    (E : Type uB) (e : E → PEmpty.{1})
    (M : (E → I) → IR.{max uA uB, uB, uI, uO} I O)
    (Q : Type uB) (q : Q → I) (X : FreeCoprodCompDisc.{max uA uB, uI} I) :
    ∀ (a : E → I) (h : (fun x ↦ ((e x).elim : I)) = a)
      (f : Hom.{uA, uB, uI, uO} I O γ
        (precomp I O Q q (M (fun x ↦ (e x).elim)))),
      FreeCoprodCompDisc.Hom.comp O
          ((interpHom I O γ (precomp I O Q q (M a))
            (cast (congrArg (fun a' ↦ Hom I O γ (precomp I O Q q (M a'))) h)
              f)).1 X)
          (FreeCoprodCompDisc.Hom.comp O
            (FreeCoprodCompDisc.Iso.hom O (interpPrecompIso I O (M a) Q q X))
            (FreeCoprodCompDisc.Iso.hom O
              (FreeCoprodCompDisc.isoOfEq O
                (congrArg
                  (fun a' ↦ interpObj I O (M a')
                    (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Q, q⟩ X))
                  h.symm)))) =
        FreeCoprodCompDisc.Hom.comp O
          ((interpHom I O γ (precomp I O Q q (M (fun x ↦ (e x).elim))) f).1 X)
          (FreeCoprodCompDisc.Iso.hom O
            (interpPrecompIso I O (M (fun x ↦ (e x).elim)) Q q X)) :=
  fun _ h ↦
    Eq.rec (motive := fun a' h' ↦ ∀ (f : Hom.{uA, uB, uI, uO} I O γ
        (precomp I O Q q (M (fun x ↦ (e x).elim)))),
        FreeCoprodCompDisc.Hom.comp O
            ((interpHom I O γ (precomp I O Q q (M a'))
              (cast
                (congrArg (fun a'' ↦ Hom I O γ (precomp I O Q q (M a''))) h')
                f)).1 X)
            (FreeCoprodCompDisc.Hom.comp O
              (FreeCoprodCompDisc.Iso.hom O
                (interpPrecompIso I O (M a') Q q X))
              (FreeCoprodCompDisc.Iso.hom O
                (FreeCoprodCompDisc.isoOfEq O
                  (congrArg
                    (fun a'' ↦ interpObj I O (M a'')
                      (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Q, q⟩ X))
                    h'.symm)))) =
          FreeCoprodCompDisc.Hom.comp O
            ((interpHom I O γ
              (precomp I O Q q (M (fun x ↦ (e x).elim))) f).1 X)
            (FreeCoprodCompDisc.Iso.hom O
              (interpPrecompIso I O (M (fun x ↦ (e x).elim)) Q q X)))
      (fun _ ↦ rfl) h

/-- The transported-composite equation behind the `δ`-domain case of
the `IR.deltaEmptyPush` characterization: the composite injection
pushed through the Lemma 4 isomorphism and the bridge factors out of
the transported composite. -/
theorem interpHomDeltaSummand_deltaEmpty_theta (B : Type uB)
    (c : (B → I) → IR.{max uA uB, uB, uI, uO} I O)
    (E : Type uB) (e : E → PEmpty.{1})
    (M : (E → I) → IR.{max uA uB, uB, uI, uO} I O) (i : B → I)
    (u : Hom.{uA, uB, uI, uO} I O (c i) (precomp I O B i (delta I O E M)))
    (w : Hom.{uA, uB, uI, uO} I O (c i)
      (precomp I O B i (M (precompMerge I B i (fun x ↦ (e x).elim)
        (fun z : {z : E // (fun x ↦ (e x).elim : E → B ⊕ PUnit.{uB + 1}) z =
            Sum.inr PUnit.unit} ↦ (((e z.1).elim : PEmpty.{1}).elim : I))))))
    (v : Hom.{uA, uB, uI, uO} I O (c i)
      (precomp I O B i (M (fun x ↦ (e x).elim))))
    (X : FreeCoprodCompDisc.{max uA uB, uI} I)
    (hu : (interpHom I O (c i) (precomp I O B i (delta I O E M)) u).1 X =
      FreeCoprodCompDisc.Hom.comp O
        ((interpHom I O (c i)
          (precomp I O B i (M (precompMerge I B i (fun x ↦ (e x).elim)
            (fun z ↦ (((e z.1).elim : PEmpty.{1}).elim : I))))) w).1 X)
        (FreeCoprodCompDisc.Hom.comp O
          (deltaEmptyInj I O
            {z : E // (fun x ↦ (e x).elim : E → B ⊕ PUnit.{uB + 1}) z =
              Sum.inr PUnit.unit}
            (fun z ↦ (e z.1).elim)
            (fun j ↦ precomp I O B i
              (M (precompMerge I B i (fun x ↦ (e x).elim) j)))
            X)
          (FreeCoprodCompDisc.coprodInj O
            (ULift.{max uA uB} (E → B ⊕ PUnit.{uB + 1}))
            (fun cl ↦ interpObj I O
              (delta I O {z : E // cl.down z = Sum.inr PUnit.unit}
                (fun j ↦ precomp I O B i
                  (M (precompMerge I B i cl.down j)))) X)
            (ULift.up (fun x ↦ (e x).elim)))))
    (hv : FreeCoprodCompDisc.Hom.comp O
        ((interpHom I O (c i)
          (precomp I O B i (M (precompMerge I B i (fun x ↦ (e x).elim)
            (fun z ↦ (((e z.1).elim : PEmpty.{1}).elim : I))))) w).1 X)
        (deltaEmptySummandHom I O E e M B i X) =
      FreeCoprodCompDisc.Hom.comp O
        ((interpHom I O (c i)
          (precomp I O B i (M (fun x ↦ (e x).elim))) v).1 X)
        (FreeCoprodCompDisc.Iso.hom O
          (interpPrecompIso I O (M (fun x ↦ (e x).elim)) B i X))) :
    FreeCoprodCompDisc.Hom.comp O
        (FreeCoprodCompDisc.Hom.comp O
          ((interpHom I O (c i) (precomp I O B i (delta I O E M)) u).1 X)
          (FreeCoprodCompDisc.Iso.hom O
            (interpPrecompIso I O (delta I O E M) B i X)))
        ((plusLiftBridgeNatInv I O B i (delta I O E M)).1 X) =
      FreeCoprodCompDisc.Hom.comp O
        (FreeCoprodCompDisc.Hom.comp O
          (FreeCoprodCompDisc.Hom.comp O
            ((interpHom I O (c i)
              (precomp I O B i (M (fun x ↦ (e x).elim))) v).1 X)
            (FreeCoprodCompDisc.Iso.hom O
              (interpPrecompIso I O (M (fun x ↦ (e x).elim)) B i X)))
          ((plusLiftBridgeNatInv I O B i (M (fun x ↦ (e x).elim))).1 X))
        (deltaEmptyInj I O E e M
          (FreeCoprodCompDisc.plus I
            (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) X)) :=
  (congrArg
      (fun t ↦ FreeCoprodCompDisc.Hom.comp O
        (FreeCoprodCompDisc.Hom.comp O t
          (FreeCoprodCompDisc.Iso.hom O
            (interpPrecompIso I O (delta I O E M) B i X)))
        ((plusLiftBridgeNatInv I O B i (delta I O E M)).1 X))
      hu).trans
    ((congrArg
        (fun t ↦ FreeCoprodCompDisc.Hom.comp O t
          ((plusLiftBridgeNatInv I O B i (delta I O E M)).1 X))
        ((FreeCoprodCompDisc.Hom.comp_assoc O
            ((interpHom I O (c i)
              (precomp I O B i (M (precompMerge I B i (fun x ↦ (e x).elim)
                (fun z ↦ (((e z.1).elim : PEmpty.{1}).elim : I))))) w).1 X)
            (FreeCoprodCompDisc.Hom.comp O
              (deltaEmptyInj I O
                {z : E // (fun x ↦ (e x).elim : E → B ⊕ PUnit.{uB + 1}) z =
                  Sum.inr PUnit.unit}
                (fun z ↦ (e z.1).elim)
                (fun j ↦ precomp I O B i
                  (M (precompMerge I B i (fun x ↦ (e x).elim) j)))
                X)
              (FreeCoprodCompDisc.coprodInj O
                (ULift.{max uA uB} (E → B ⊕ PUnit.{uB + 1}))
                (fun cl ↦ interpObj I O
                  (delta I O {z : E // cl.down z = Sum.inr PUnit.unit}
                    (fun j ↦ precomp I O B i
                      (M (precompMerge I B i cl.down j)))) X)
                (ULift.up (fun x ↦ (e x).elim))))
            (FreeCoprodCompDisc.Iso.hom O
              (interpPrecompIso I O (delta I O E M) B i X))).trans
          ((congrArg
              (FreeCoprodCompDisc.Hom.comp O
                ((interpHom I O (c i)
                  (precomp I O B i (M (precompMerge I B i
                    (fun x ↦ (e x).elim)
                    (fun z ↦ (((e z.1).elim : PEmpty.{1}).elim : I)))))
                  w).1 X))
              (interpPrecompIso_deltaEmpty_inj I O E e M B i X)).trans
            ((FreeCoprodCompDisc.Hom.comp_assoc O
                ((interpHom I O (c i)
                  (precomp I O B i (M (precompMerge I B i
                    (fun x ↦ (e x).elim)
                    (fun z ↦ (((e z.1).elim : PEmpty.{1}).elim : I)))))
                  w).1 X)
                (deltaEmptySummandHom I O E e M B i X)
                (deltaEmptyInj I O E e M
                  (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I
                    ⟨B, i⟩ X))).symm.trans
              (congrArg
                (fun t ↦ FreeCoprodCompDisc.Hom.comp O t
                  (deltaEmptyInj I O E e M
                    (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨B, i⟩ X)))
                hv))))).trans
      ((FreeCoprodCompDisc.Hom.comp_assoc O
          (FreeCoprodCompDisc.Hom.comp O
            ((interpHom I O (c i)
              (precomp I O B i (M (fun x ↦ (e x).elim))) v).1 X)
            (FreeCoprodCompDisc.Iso.hom O
              (interpPrecompIso I O (M (fun x ↦ (e x).elim)) B i X)))
          (deltaEmptyInj I O E e M
            (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨B, i⟩ X))
          ((plusLiftBridgeNatInv I O B i (delta I O E M)).1 X)).trans
        ((congrArg
            (FreeCoprodCompDisc.Hom.comp O
              (FreeCoprodCompDisc.Hom.comp O
                ((interpHom I O (c i)
                  (precomp I O B i (M (fun x ↦ (e x).elim))) v).1 X)
                (FreeCoprodCompDisc.Iso.hom O
                  (interpPrecompIso I O (M (fun x ↦ (e x).elim)) B i X))))
            (interpMor_deltaEmpty_inj I O E e M
              (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨B, i⟩ X)
              (FreeCoprodCompDisc.plus I
                (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) X)
              (plusLiftBridgeInvHom I B i X))).trans
          (FreeCoprodCompDisc.Hom.comp_assoc O
            (FreeCoprodCompDisc.Hom.comp O
              ((interpHom I O (c i)
                (precomp I O B i (M (fun x ↦ (e x).elim))) v).1 X)
              (FreeCoprodCompDisc.Iso.hom O
                (interpPrecompIso I O (M (fun x ↦ (e x).elim)) B i X)))
            ((plusLiftBridgeNatInv I O B i (M (fun x ↦ (e x).elim))).1 X)
            (deltaEmptyInj I O E e M
              (FreeCoprodCompDisc.plus I
                (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩)
                X))).symm)))

/-- The per-summand transport of the empty-summand inclusion through
the `δ`-case target transports, given the summand's own push and cast
equations. -/
theorem interpHomDeltaSummand_deltaEmptyInj (B : Type uB)
    (c : (B → I) → IR.{max uA uB, uB, uI, uO} I O)
    (E : Type uB) (e : E → PEmpty.{1})
    (M : (E → I) → IR.{max uA uB, uB, uI, uO} I O) (i : B → I)
    (u : Hom.{uA, uB, uI, uO} I O (c i) (precomp I O B i (delta I O E M)))
    (w : Hom.{uA, uB, uI, uO} I O (c i)
      (precomp I O B i (M (precompMerge I B i (fun x ↦ (e x).elim)
        (fun z : {z : E // (fun x ↦ (e x).elim : E → B ⊕ PUnit.{uB + 1}) z =
            Sum.inr PUnit.unit} ↦ (((e z.1).elim : PEmpty.{1}).elim : I))))))
    (v : Hom.{uA, uB, uI, uO} I O (c i)
      (precomp I O B i (M (fun x ↦ (e x).elim))))
    (X : FreeCoprodCompDisc.{max uA uB, uI} I)
    (hu : (interpHom I O (c i) (precomp I O B i (delta I O E M)) u).1 X =
      FreeCoprodCompDisc.Hom.comp O
        ((interpHom I O (c i)
          (precomp I O B i (M (precompMerge I B i (fun x ↦ (e x).elim)
            (fun z ↦ (((e z.1).elim : PEmpty.{1}).elim : I))))) w).1 X)
        (FreeCoprodCompDisc.Hom.comp O
          (deltaEmptyInj I O
            {z : E // (fun x ↦ (e x).elim : E → B ⊕ PUnit.{uB + 1}) z =
              Sum.inr PUnit.unit}
            (fun z ↦ (e z.1).elim)
            (fun j ↦ precomp I O B i
              (M (precompMerge I B i (fun x ↦ (e x).elim) j)))
            X)
          (FreeCoprodCompDisc.coprodInj O
            (ULift.{max uA uB} (E → B ⊕ PUnit.{uB + 1}))
            (fun cl ↦ interpObj I O
              (delta I O {z : E // cl.down z = Sum.inr PUnit.unit}
                (fun j ↦ precomp I O B i
                  (M (precompMerge I B i cl.down j)))) X)
            (ULift.up (fun x ↦ (e x).elim)))))
    (hv : FreeCoprodCompDisc.Hom.comp O
        ((interpHom I O (c i)
          (precomp I O B i (M (precompMerge I B i (fun x ↦ (e x).elim)
            (fun z ↦ (((e z.1).elim : PEmpty.{1}).elim : I))))) w).1 X)
        (deltaEmptySummandHom I O E e M B i X) =
      FreeCoprodCompDisc.Hom.comp O
        ((interpHom I O (c i)
          (precomp I O B i (M (fun x ↦ (e x).elim))) v).1 X)
        (FreeCoprodCompDisc.Iso.hom O
          (interpPrecompIso I O (M (fun x ↦ (e x).elim)) B i X))) :
    (interpHomDeltaSummand I O B c (delta I O E M) i u).1 X =
      FreeCoprodCompDisc.Hom.comp O
        ((interpHomDeltaSummand I O B c (M (fun x ↦ (e x).elim)) i v).1 X)
        (deltaEmptyInj I O E e M X) :=
  (congrArg
      (FreeCoprodCompDisc.coprodDesc O
        (FreeCoprodCompDisc.Hom I
          (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) X)
        (fun _ ↦ interpObj I O (c i) X)
        (interpObj I O (delta I O E M) X))
      (funext (fun e' ↦
        (congrArg
            (fun t ↦ FreeCoprodCompDisc.Hom.comp O t
              (interpMor I O (delta I O E M)
                (FreeCoprodCompDisc.plus I
                  (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) X)
                X
                (FreeCoprodCompDisc.coprodPairDesc I e'
                  (FreeCoprodCompDisc.Hom.id I X))))
            (interpHomDeltaSummand_deltaEmpty_theta I O B c E e M i u w v X
              hu hv)).trans
          ((FreeCoprodCompDisc.Hom.comp_assoc O
              (FreeCoprodCompDisc.Hom.comp O
                (FreeCoprodCompDisc.Hom.comp O
                  ((interpHom I O (c i)
                    (precomp I O B i (M (fun x ↦ (e x).elim))) v).1 X)
                  (FreeCoprodCompDisc.Iso.hom O
                    (interpPrecompIso I O (M (fun x ↦ (e x).elim)) B i X)))
                ((plusLiftBridgeNatInv I O B i
                  (M (fun x ↦ (e x).elim))).1 X))
              (deltaEmptyInj I O E e M
                (FreeCoprodCompDisc.plus I
                  (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) X))
              (interpMor I O (delta I O E M)
                (FreeCoprodCompDisc.plus I
                  (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) X)
                X
                (FreeCoprodCompDisc.coprodPairDesc I e'
                  (FreeCoprodCompDisc.Hom.id I X)))).trans
            ((congrArg
                (FreeCoprodCompDisc.Hom.comp O
                  (FreeCoprodCompDisc.Hom.comp O
                    (FreeCoprodCompDisc.Hom.comp O
                      ((interpHom I O (c i)
                        (precomp I O B i (M (fun x ↦ (e x).elim))) v).1 X)
                      (FreeCoprodCompDisc.Iso.hom O
                        (interpPrecompIso I O (M (fun x ↦ (e x).elim))
                          B i X)))
                    ((plusLiftBridgeNatInv I O B i
                      (M (fun x ↦ (e x).elim))).1 X)))
                (interpMor_deltaEmpty_inj I O E e M
                  (FreeCoprodCompDisc.plus I
                    (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) X)
                  X
                  (FreeCoprodCompDisc.coprodPairDesc I e'
                    (FreeCoprodCompDisc.Hom.id I X)))).trans
              (FreeCoprodCompDisc.Hom.comp_assoc O
                (FreeCoprodCompDisc.Hom.comp O
                  (FreeCoprodCompDisc.Hom.comp O
                    ((interpHom I O (c i)
                      (precomp I O B i (M (fun x ↦ (e x).elim))) v).1 X)
                    (FreeCoprodCompDisc.Iso.hom O
                      (interpPrecompIso I O (M (fun x ↦ (e x).elim)) B i X)))
                  ((plusLiftBridgeNatInv I O B i
                    (M (fun x ↦ (e x).elim))).1 X))
                (interpMor I O (M (fun x ↦ (e x).elim))
                  (FreeCoprodCompDisc.plus I
                    (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) X)
                  X
                  (FreeCoprodCompDisc.coprodPairDesc I e'
                    (FreeCoprodCompDisc.Hom.id I X)))
                (deltaEmptyInj I O E e M X)).symm))))).trans
    (FreeCoprodCompDisc.coprodDesc_comp O
        (FreeCoprodCompDisc.Hom I
          (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) X)
        (fun _ ↦ interpObj I O (c i) X)
        (interpObj I O (M (fun x ↦ (e x).elim)) X)
        (interpObj I O (delta I O E M) X)
        (fun e' ↦ FreeCoprodCompDisc.Hom.comp O
          (FreeCoprodCompDisc.Hom.comp O
            (FreeCoprodCompDisc.Hom.comp O
              ((interpHom I O (c i)
                (precomp I O B i (M (fun x ↦ (e x).elim))) v).1 X)
              (FreeCoprodCompDisc.Iso.hom O
                (interpPrecompIso I O (M (fun x ↦ (e x).elim)) B i X)))
            ((plusLiftBridgeNatInv I O B i (M (fun x ↦ (e x).elim))).1 X))
          (interpMor I O (M (fun x ↦ (e x).elim))
            (FreeCoprodCompDisc.plus I
              (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) X) X
            (FreeCoprodCompDisc.coprodPairDesc I e'
              (FreeCoprodCompDisc.Hom.id I X))))
        (deltaEmptyInj I O E e M X)).symm

/-- The `δ`-domain case of the `IR.deltaEmptyPush` characterization. -/
theorem interpHom_deltaEmptyPush_mk_delta (B : Type uB)
    (d : Direction I O (Sum.inr (Sum.inr B) : Shape.{max uA uB, uB, uO} O) →
      IR.{max uA uB, uB, uI, uO} I O)
    (ih : (x : Direction I O (Sum.inr (Sum.inr B) : Shape.{max uA uB, uB, uO} O)) →
      InterpHomDeltaEmptyPushMotive I O (d x)) :
    InterpHomDeltaEmptyPushMotive I O (mk I O (Sum.inr (Sum.inr B)) d) :=
  fun E e M f X ↦
    (congrArg
        (fun t ↦ (interpHom I O (mk I O (Sum.inr (Sum.inr B)) d)
          (delta I O E M) t).1 X)
        (deltaEmptyPush_mk_delta I O B d E e M f)).trans
      ((interpHom_delta I O B (fun j ↦ d (ULift.up j)) (delta I O E M)
          (fun i ↦ sigmaPush I O (d (ULift.up i))
            (ULift.{max uA uB} (E → B ⊕ PUnit.{uB + 1}))
            (fun cl ↦ delta I O {z : E // cl.down z = Sum.inr PUnit.unit}
              (fun j ↦ precomp I O B i (M (precompMerge I B i cl.down j))))
            (ULift.up (fun x ↦ (e x).elim))
            (deltaEmptyPush I O (d (ULift.up i))
              {z : E // (fun x ↦ (e x).elim) z = Sum.inr PUnit.unit}
              (fun z ↦ (e z.1).elim)
              (fun j ↦ precomp I O B i
                (M (precompMerge I B i (fun x ↦ (e x).elim) j)))
              (cast (congrArg
                (fun a ↦ Hom I O (d (ULift.up i)) (precomp I O B i (M a)))
                (funext (fun x ↦ (e x).elim) :
                  (fun x ↦ (e x).elim) = precompMerge I B i
                    (fun x ↦ (e x).elim)
                    (fun z : {z : E // (fun x ↦ (e x).elim) z =
                        Sum.inr PUnit.unit}
                      ↦ ((e z.1).elim : PEmpty.{1}).elim)))
                (f i)))) X).trans
        ((congrArg
            (deltaDesc I O B (fun j ↦ d (ULift.up j)) X
              (interpObj I O (delta I O E M) X))
            (funext (fun i ↦
              interpHomDeltaSummand_deltaEmptyInj I O B
                (fun j ↦ d (ULift.up j)) E e M i
                (sigmaPush I O (d (ULift.up i))
                  (ULift.{max uA uB} (E → B ⊕ PUnit.{uB + 1}))
                  (fun cl ↦ delta I O
                    {z : E // cl.down z = Sum.inr PUnit.unit}
                    (fun j ↦ precomp I O B i
                      (M (precompMerge I B i cl.down j))))
                  (ULift.up (fun x ↦ (e x).elim))
                  (deltaEmptyPush I O (d (ULift.up i))
                    {z : E // (fun x ↦ (e x).elim) z = Sum.inr PUnit.unit}
                    (fun z ↦ (e z.1).elim)
                    (fun j ↦ precomp I O B i
                      (M (precompMerge I B i (fun x ↦ (e x).elim) j)))
                    (cast (congrArg
                      (fun a ↦ Hom I O (d (ULift.up i))
                        (precomp I O B i (M a)))
                      (funext (fun x ↦ (e x).elim) :
                        (fun x ↦ (e x).elim) = precompMerge I B i
                          (fun x ↦ (e x).elim)
                          (fun z : {z : E // (fun x ↦ (e x).elim) z =
                              Sum.inr PUnit.unit}
                            ↦ ((e z.1).elim : PEmpty.{1}).elim)))
                      (f i))))
                (cast (congrArg
                  (fun a ↦ Hom I O (d (ULift.up i))
                    (precomp I O B i (M a)))
                  (funext (fun x ↦ (e x).elim) :
                    (fun x ↦ (e x).elim) = precompMerge I B i
                      (fun x ↦ (e x).elim)
                      (fun z : {z : E // (fun x ↦ (e x).elim) z =
                          Sum.inr PUnit.unit}
                        ↦ ((e z.1).elim : PEmpty.{1}).elim)))
                  (f i))
                (f i) X
                ((interpHom_sigmaPush I O (d (ULift.up i))
                    (ULift.{max uA uB} (E → B ⊕ PUnit.{uB + 1}))
                    (fun cl ↦ delta I O
                      {z : E // cl.down z = Sum.inr PUnit.unit}
                      (fun j ↦ precomp I O B i
                        (M (precompMerge I B i cl.down j))))
                    (ULift.up (fun x ↦ (e x).elim))
                    (deltaEmptyPush I O (d (ULift.up i))
                      {z : E // (fun x ↦ (e x).elim) z = Sum.inr PUnit.unit}
                      (fun z ↦ (e z.1).elim)
                      (fun j ↦ precomp I O B i
                        (M (precompMerge I B i (fun x ↦ (e x).elim) j)))
                      (cast (congrArg
                        (fun a ↦ Hom I O (d (ULift.up i))
                          (precomp I O B i (M a)))
                        (funext (fun x ↦ (e x).elim) :
                          (fun x ↦ (e x).elim) = precompMerge I B i
                            (fun x ↦ (e x).elim)
                            (fun z : {z : E // (fun x ↦ (e x).elim) z =
                                Sum.inr PUnit.unit}
                              ↦ ((e z.1).elim : PEmpty.{1}).elim)))
                        (f i))) X).trans
                  ((congrArg
                      (fun t ↦ FreeCoprodCompDisc.Hom.comp O t
                        (FreeCoprodCompDisc.coprodInj O
                          (ULift.{max uA uB} (E → B ⊕ PUnit.{uB + 1}))
                          (fun cl ↦ interpObj I O
                            (delta I O
                              {z : E // cl.down z = Sum.inr PUnit.unit}
                              (fun j ↦ precomp I O B i
                                (M (precompMerge I B i cl.down j)))) X)
                          (ULift.up (fun x ↦ (e x).elim))))
                      (ih (ULift.up i)
                        {z : E // (fun x ↦ (e x).elim :
                          E → B ⊕ PUnit.{uB + 1}) z = Sum.inr PUnit.unit}
                        (fun z ↦ (e z.1).elim)
                        (fun j ↦ precomp I O B i
                          (M (precompMerge I B i (fun x ↦ (e x).elim) j)))
                        (cast (congrArg
                          (fun a ↦ Hom I O (d (ULift.up i))
                            (precomp I O B i (M a)))
                          (funext (fun x ↦ (e x).elim) :
                            (fun x ↦ (e x).elim) = precompMerge I B i
                              (fun x ↦ (e x).elim)
                              (fun z : {z : E // (fun x ↦ (e x).elim) z =
                                  Sum.inr PUnit.unit}
                                ↦ ((e z.1).elim : PEmpty.{1}).elim)))
                          (f i))
                        X)).trans
                    (FreeCoprodCompDisc.Hom.comp_assoc O
                      ((interpHom I O (d (ULift.up i))
                        (precomp I O B i (M (precompMerge I B i
                          (fun x ↦ (e x).elim)
                          (fun z ↦ (((e z.1).elim : PEmpty.{1}).elim : I)))))
                        (cast (congrArg
                          (fun a ↦ Hom I O (d (ULift.up i))
                            (precomp I O B i (M a)))
                          (funext (fun x ↦ (e x).elim) :
                            (fun x ↦ (e x).elim) = precompMerge I B i
                              (fun x ↦ (e x).elim)
                              (fun z : {z : E // (fun x ↦ (e x).elim) z =
                                  Sum.inr PUnit.unit}
                                ↦ ((e z.1).elim : PEmpty.{1}).elim)))
                          (f i))).1 X)
                      (deltaEmptyInj I O
                        {z : E // (fun x ↦ (e x).elim :
                          E → B ⊕ PUnit.{uB + 1}) z = Sum.inr PUnit.unit}
                        (fun z ↦ (e z.1).elim)
                        (fun j ↦ precomp I O B i
                          (M (precompMerge I B i (fun x ↦ (e x).elim) j)))
                        X)
                      (FreeCoprodCompDisc.coprodInj O
                        (ULift.{max uA uB} (E → B ⊕ PUnit.{uB + 1}))
                        (fun cl ↦ interpObj I O
                          (delta I O
                            {z : E // cl.down z = Sum.inr PUnit.unit}
                            (fun j ↦ precomp I O B i
                              (M (precompMerge I B i cl.down j)))) X)
                        (ULift.up (fun x ↦ (e x).elim))))))
                (interpHom_deltaEmptySummand_cast I O (d (ULift.up i))
                  E e M B i X
                  (precompMerge I B i (fun x ↦ (e x).elim)
                    (fun z ↦ (((e z.1).elim : PEmpty.{1}).elim : I)))
                  (funext (fun x ↦ (e x).elim))
                  (f i))))).trans
          ((deltaDesc_comp I O B (fun j ↦ d (ULift.up j)) X
              (interpObj I O (M (fun x ↦ (e x).elim)) X)
              (interpObj I O (delta I O E M) X)
              (fun i ↦ (interpHomDeltaSummand I O B (fun j ↦ d (ULift.up j))
                (M (fun x ↦ (e x).elim)) i (f i)).1 X)
              (deltaEmptyInj I O E e M X)).symm.trans
            (congrArg
              (fun t ↦ FreeCoprodCompDisc.Hom.comp O t
                (deltaEmptyInj I O E e M X))
              (interpHom_delta I O B (fun j ↦ d (ULift.up j))
                (M (fun x ↦ (e x).elim)) f X).symm))))

/-- `IR.interpHom` sends `IR.deltaEmptyPush` to composition with the
semantic empty-summand inclusion, by `IR.induction`. -/
theorem interpHom_deltaEmptyPush (γ : IR.{max uA uB, uB, uI, uO} I O) :
    InterpHomDeltaEmptyPushMotive I O γ :=
  induction I O (InterpHomDeltaEmptyPushMotive I O)
    (fun s ↦ match s with
      | Sum.inl o => fun d _ ↦ interpHom_deltaEmptyPush_mk_iota I O o d
      | Sum.inr (Sum.inl A) => fun d ih ↦
          interpHom_deltaEmptyPush_mk_sigma I O A d ih
      | Sum.inr (Sum.inr B) => fun d ih ↦
          interpHom_deltaEmptyPush_mk_delta I O B d ih)
    γ

/-! ### The navigation characterizations -/

/-- The `IR.msigmaPush` characterization: `IR.interpHom` sends a stack
`σ`-push to the composite with the semantic `σ`-injection conjugated
through the iterated Lemma 4 isomorphism. -/
theorem interpHom_msigmaPush (D : IR.{max uA uB, uB, uI, uO} I O)
    (A' : Type (max uA uB)) (K' : A' → IR.{max uA uB, uB, uI, uO} I O) (a' : A')
    (L : List (SupObj.{uB, uI} I))
    (f : Hom.{uA, uB, uI, uO} I O D (mprecomp I O L (K' a')))
    (X : FreeCoprodCompDisc.{max uA uB, uI} I) :
    (interpHom I O D (mprecomp I O L (sigma I O A' K'))
        (msigmaPush I O D A' K' a' L f)).1 X =
      FreeCoprodCompDisc.Hom.comp O
        ((interpHom I O D (mprecomp I O L (K' a')) f).1 X)
        (FreeCoprodCompDisc.Hom.comp O
          (FreeCoprodCompDisc.Hom.comp O
            (FreeCoprodCompDisc.Iso.hom O
              (mprecompIso.{uA, uB, uI, uO} I O L (K' a') X))
            (FreeCoprodCompDisc.coprodInj O A'
              (fun a ↦ interpObj I O (K' a) (mplus.{uA, uB, uI} I L X)) a'))
          (FreeCoprodCompDisc.Iso.invHom O
            (mprecompIso.{uA, uB, uI, uO} I O L (sigma I O A' K') X))) :=
  L.rec (motive := fun L' ↦ ∀ (A'' : Type (max uA uB))
      (K'' : A'' → IR.{max uA uB, uB, uI, uO} I O) (a'' : A'')
      (f' : Hom.{uA, uB, uI, uO} I O D (mprecomp I O L' (K'' a'')))
      (X' : FreeCoprodCompDisc.{max uA uB, uI} I),
      (interpHom I O D (mprecomp I O L' (sigma I O A'' K''))
          (msigmaPush I O D A'' K'' a'' L' f')).1 X' =
        FreeCoprodCompDisc.Hom.comp O
          ((interpHom I O D (mprecomp I O L' (K'' a'')) f').1 X')
          (FreeCoprodCompDisc.Hom.comp O
            (FreeCoprodCompDisc.Hom.comp O
              (FreeCoprodCompDisc.Iso.hom O
                (mprecompIso.{uA, uB, uI, uO} I O L' (K'' a'') X'))
              (FreeCoprodCompDisc.coprodInj O A''
                (fun a ↦ interpObj I O (K'' a) (mplus.{uA, uB, uI} I L' X'))
                a''))
            (FreeCoprodCompDisc.Iso.invHom O
              (mprecompIso.{uA, uB, uI, uO} I O L' (sigma I O A'' K'') X'))))
    (fun A'' K'' a'' f' X' ↦ interpHom_sigmaPush I O D A'' K'' a'' f' X')
    (fun b _L ih A'' K'' a'' f' X' ↦
      (ih (ULift.{uB} A'') (fun x ↦ precomp I O b.1 b.2 (K'' x.down))
          (ULift.up a'') f' X').trans
        (congrArg
          (FreeCoprodCompDisc.Hom.comp O
            ((interpHom I O D
              (mprecomp I O _L (precomp I O b.1 b.2 (K'' a''))) f').1 X'))
          ((congrArg
              (fun t ↦ FreeCoprodCompDisc.Hom.comp O
                (FreeCoprodCompDisc.Hom.comp O
                  (FreeCoprodCompDisc.Iso.hom O
                    (mprecompIso.{uA, uB, uI, uO} I O _L
                      (precomp I O b.1 b.2 (K'' a'')) X'))
                  t)
                (FreeCoprodCompDisc.Iso.invHom O
                  (mprecompIso.{uA, uB, uI, uO} I O _L
                    (precomp I O b.1 b.2 (sigma I O A'' K'')) X')))
              (FreeCoprodCompDisc.eq_comp_invHom O
                (interpObj I O (precomp I O b.1 b.2 (K'' a''))
                  (mplus.{uA, uB, uI} I _L X'))
                (interpObj I O (precomp I O b.1 b.2 (sigma I O A'' K''))
                  (mplus.{uA, uB, uI} I _L X'))
                (interpObj I O (sigma I O A'' K'')
                  (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b
                    (mplus.{uA, uB, uI} I _L X')))
                (FreeCoprodCompDisc.coprodInj O (ULift.{uB} A'')
                  (fun x ↦ interpObj I O (precomp I O b.1 b.2 (K'' x.down))
                    (mplus.{uA, uB, uI} I _L X'))
                  (ULift.up a''))
                (FreeCoprodCompDisc.Hom.comp O
                  (FreeCoprodCompDisc.Iso.hom O
                    (interpPrecompIso I O (K'' a'') b.1 b.2
                      (mplus.{uA, uB, uI} I _L X')))
                  (FreeCoprodCompDisc.coprodInj O A''
                    (fun a ↦ interpObj I O (K'' a)
                      (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b
                        (mplus.{uA, uB, uI} I _L X')))
                    a''))
                (interpPrecompIso I O (sigma I O A'' K'') b.1 b.2
                  (mplus.{uA, uB, uI} I _L X'))
                (interpPrecompIso_sigma_inj I O A'' K'' a'' b.1 b.2
                  (mplus.{uA, uB, uI} I _L X')))).trans
            ((FreeCoprodCompDisc.Hom.comp_assoc O
                (FreeCoprodCompDisc.Iso.hom O
                  (mprecompIso.{uA, uB, uI, uO} I O _L
                    (precomp I O b.1 b.2 (K'' a'')) X'))
                (FreeCoprodCompDisc.Hom.comp O
                  (FreeCoprodCompDisc.Hom.comp O
                    (FreeCoprodCompDisc.Iso.hom O
                      (interpPrecompIso I O (K'' a'') b.1 b.2
                        (mplus.{uA, uB, uI} I _L X')))
                    (FreeCoprodCompDisc.coprodInj O A''
                      (fun a ↦ interpObj I O (K'' a)
                        (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b
                          (mplus.{uA, uB, uI} I _L X')))
                      a''))
                  (FreeCoprodCompDisc.Iso.invHom O
                    (interpPrecompIso I O (sigma I O A'' K'') b.1 b.2
                      (mplus.{uA, uB, uI} I _L X'))))
                (FreeCoprodCompDisc.Iso.invHom O
                  (mprecompIso.{uA, uB, uI, uO} I O _L
                    (precomp I O b.1 b.2 (sigma I O A'' K'')) X'))).trans
              ((congrArg
                  (FreeCoprodCompDisc.Hom.comp O
                    (FreeCoprodCompDisc.Iso.hom O
                      (mprecompIso.{uA, uB, uI, uO} I O _L
                        (precomp I O b.1 b.2 (K'' a'')) X')))
                  (FreeCoprodCompDisc.Hom.comp_assoc O
                    (FreeCoprodCompDisc.Hom.comp O
                      (FreeCoprodCompDisc.Iso.hom O
                        (interpPrecompIso I O (K'' a'') b.1 b.2
                          (mplus.{uA, uB, uI} I _L X')))
                      (FreeCoprodCompDisc.coprodInj O A''
                        (fun a ↦ interpObj I O (K'' a)
                          (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b
                            (mplus.{uA, uB, uI} I _L X')))
                        a''))
                    (FreeCoprodCompDisc.Iso.invHom O
                      (interpPrecompIso I O (sigma I O A'' K'') b.1 b.2
                        (mplus.{uA, uB, uI} I _L X')))
                    (FreeCoprodCompDisc.Iso.invHom O
                      (mprecompIso.{uA, uB, uI, uO} I O _L
                        (precomp I O b.1 b.2 (sigma I O A'' K'')) X')))).trans
                ((FreeCoprodCompDisc.Hom.comp_assoc O
                    (FreeCoprodCompDisc.Iso.hom O
                      (mprecompIso.{uA, uB, uI, uO} I O _L
                        (precomp I O b.1 b.2 (K'' a'')) X'))
                    (FreeCoprodCompDisc.Hom.comp O
                      (FreeCoprodCompDisc.Iso.hom O
                        (interpPrecompIso I O (K'' a'') b.1 b.2
                          (mplus.{uA, uB, uI} I _L X')))
                      (FreeCoprodCompDisc.coprodInj O A''
                        (fun a ↦ interpObj I O (K'' a)
                          (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b
                            (mplus.{uA, uB, uI} I _L X')))
                        a''))
                    (FreeCoprodCompDisc.Hom.comp O
                      (FreeCoprodCompDisc.Iso.invHom O
                        (interpPrecompIso I O (sigma I O A'' K'') b.1 b.2
                          (mplus.{uA, uB, uI} I _L X')))
                      (FreeCoprodCompDisc.Iso.invHom O
                        (mprecompIso.{uA, uB, uI, uO} I O _L
                          (precomp I O b.1 b.2 (sigma I O A'' K'')) X')))).symm.trans
                  (congrArg
                    (fun t ↦ FreeCoprodCompDisc.Hom.comp O t
                      (FreeCoprodCompDisc.Hom.comp O
                        (FreeCoprodCompDisc.Iso.invHom O
                          (interpPrecompIso I O (sigma I O A'' K'') b.1 b.2
                            (mplus.{uA, uB, uI} I _L X')))
                        (FreeCoprodCompDisc.Iso.invHom O
                          (mprecompIso.{uA, uB, uI, uO} I O _L
                            (precomp I O b.1 b.2 (sigma I O A'' K'')) X'))))
                    (FreeCoprodCompDisc.Hom.comp_assoc O
                      (FreeCoprodCompDisc.Iso.hom O
                        (mprecompIso.{uA, uB, uI, uO} I O _L
                          (precomp I O b.1 b.2 (K'' a'')) X'))
                      (FreeCoprodCompDisc.Iso.hom O
                        (interpPrecompIso I O (K'' a'') b.1 b.2
                          (mplus.{uA, uB, uI} I _L X')))
                      (FreeCoprodCompDisc.coprodInj O A''
                        (fun a ↦ interpObj I O (K'' a)
                          (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b
                            (mplus.{uA, uB, uI} I _L X')))
                        a'')).symm)))))))
    A' K' a' f X

/-- The `IR.deltaNavBase` characterization: `IR.interpHom` sends the
base navigation to the composite with the empty-summand inclusion at
the all-resolved classifier's unresolved subtype, followed by the
semantic `σ`-injection at that classifier. -/
theorem interpHom_deltaNavBase (D : IR.{max uA uB, uB, uI, uO} I O)
    (Bout : Type uB) (iout : Bout → I) (Bin : Type uB)
    (K : (Bin → I) → IR.{max uA uB, uB, uI, uO} I O) (g : Bin → Bout)
    (f : Hom.{uA, uB, uI, uO} I O D (precomp I O Bout iout (K (iout ∘ g))))
    (X : FreeCoprodCompDisc.{max uA uB, uI} I) :
    (interpHom I O D (precomp I O Bout iout (delta I O Bin K))
        (deltaNavBase I O D Bout iout Bin K g f)).1 X =
      FreeCoprodCompDisc.Hom.comp O
        ((interpHom I O D (precomp I O Bout iout (K (iout ∘ g))) f).1 X)
        (FreeCoprodCompDisc.Hom.comp O
          (deltaEmptyInj I O
            {z : Bin // (fun b ↦ Sum.inl (g b) : Bin → Bout ⊕ PUnit.{uB + 1}) z =
              Sum.inr PUnit.unit}
            (fun z ↦ nomatch z.2)
            (fun j ↦ precomp I O Bout iout
              (K (precompMerge I Bout iout (fun b ↦ Sum.inl (g b)) j)))
            X)
          (FreeCoprodCompDisc.coprodInj O
            (ULift.{max uA uB} (Bin → Bout ⊕ PUnit.{uB + 1}))
            (fun cl ↦ interpObj I O
              (delta I O {z : Bin // cl.down z = Sum.inr PUnit.unit}
                (fun j ↦ precomp I O Bout iout
                  (K (precompMerge I Bout iout cl.down j)))) X)
            (ULift.up (fun b ↦ Sum.inl (g b))))) :=
  (interpHom_sigmaPush I O D (ULift.{max uA uB} (Bin → Bout ⊕ PUnit.{uB + 1}))
      (fun cl ↦ delta I O {z : Bin // cl.down z = Sum.inr PUnit.unit}
        (fun j ↦ precomp I O Bout iout
          (K (precompMerge I Bout iout cl.down j))))
      (ULift.up (fun b ↦ Sum.inl (g b)))
      (deltaEmptyPush I O D
        {z : Bin // (fun b ↦ Sum.inl (g b) : Bin → Bout ⊕ PUnit.{uB + 1}) z =
          Sum.inr PUnit.unit}
        (fun z ↦ nomatch z.2)
        (fun j ↦ precomp I O Bout iout
          (K (precompMerge I Bout iout (fun b ↦ Sum.inl (g b)) j)))
        f)
      X).trans
    ((congrArg
        (fun t ↦ FreeCoprodCompDisc.Hom.comp O t
          (FreeCoprodCompDisc.coprodInj O
            (ULift.{max uA uB} (Bin → Bout ⊕ PUnit.{uB + 1}))
            (fun cl ↦ interpObj I O
              (delta I O {z : Bin // cl.down z = Sum.inr PUnit.unit}
                (fun j ↦ precomp I O Bout iout
                  (K (precompMerge I Bout iout cl.down j)))) X)
            (ULift.up (fun b ↦ Sum.inl (g b)))))
        (interpHom_deltaEmptyPush I O D
          {z : Bin // (fun b ↦ Sum.inl (g b) : Bin → Bout ⊕ PUnit.{uB + 1}) z =
            Sum.inr PUnit.unit}
          (fun z ↦ nomatch z.2)
          (fun j ↦ precomp I O Bout iout
            (K (precompMerge I Bout iout (fun b ↦ Sum.inl (g b)) j)))
          f X)).trans
      (FreeCoprodCompDisc.Hom.comp_assoc O
        ((interpHom I O D (precomp I O Bout iout (K (iout ∘ g))) f).1 X)
        (deltaEmptyInj I O
          {z : Bin // (fun b ↦ Sum.inl (g b) : Bin → Bout ⊕ PUnit.{uB + 1}) z =
            Sum.inr PUnit.unit}
          (fun z ↦ nomatch z.2)
          (fun j ↦ precomp I O Bout iout
            (K (precompMerge I Bout iout (fun b ↦ Sum.inl (g b)) j)))
          X)
        (FreeCoprodCompDisc.coprodInj O
          (ULift.{max uA uB} (Bin → Bout ⊕ PUnit.{uB + 1}))
          (fun cl ↦ interpObj I O
            (delta I O {z : Bin // cl.down z = Sum.inr PUnit.unit}
              (fun j ↦ precomp I O Bout iout
                (K (precompMerge I Bout iout cl.down j)))) X)
          (ULift.up (fun b ↦ Sum.inl (g b))))))

/-- The name-level computation of the Lemma 4 `δ`-square at a summand
of a classifier's unresolved subtype, with every assignment equality
generalized: both routes transport the summand's Lemma 4 image along
propositionally equal paths, identified by proof irrelevance at the
base. -/
theorem deltaNav_strip (Bin : Type uB)
    (K : (Bin → I) → IR.{max uA uB, uB, uI, uO} I O)
    (Q : Type uB) (q : Q → I) (k : FreeCoprodCompDisc.{max uA uB, uI} I)
    (cl : Bin → Q ⊕ PUnit.{uB + 1}) :
    ∀ (j₀ j₂ : {z : Bin // cl z = Sum.inr PUnit.unit} → I) (hj : j₀ = j₂)
      (w₁ : Bin → Q ⊕ k.1)
      (s₁ : precompMerge I Q q cl j₂ = Sum.elim q k.2 ∘ w₁)
      (w₂ : Bin → Q ⊕ k.1) (_hw : w₁ = w₂)
      (b₀ : Bin → I) (r₀ : precompMerge I Q q cl j₀ = b₀)
      (s₂ : b₀ = Sum.elim q k.2 ∘ w₂)
      (n : (interpObj I O
        (precomp I O Q q (K (precompMerge I Q q cl j₀))) k).1),
      (⟨w₁, (FreeCoprodCompDisc.isoOfEq O
          (congrArg (fun m ↦ interpObj I O (K m)
            (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Q, q⟩ k)) s₁)).1
          ((FreeCoprodCompDisc.Iso.hom O
            (interpPrecompIso I O (K (precompMerge I Q q cl j₂)) Q q k)).1
            (cast (congrArg (fun t ↦ (interpObj I O
              (precomp I O Q q (K (precompMerge I Q q cl t))) k).1) hj) n))⟩ :
        (interpObj I O (delta I O Bin K)
          (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Q, q⟩ k)).1) =
      ⟨w₂, cast (congrArg (fun m ↦ (interpObj I O (K m)
          (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Q, q⟩ k)).1) s₂)
        ((FreeCoprodCompDisc.Iso.hom O
          (interpPrecompIso I O (K b₀) Q q k)).1
          (cast (congrArg (fun t ↦ (interpObj I O
            (precomp I O Q q (K t)) k).1) r₀) n))⟩ :=
  fun j₀ _ hj ↦
    Eq.rec (motive := fun j₂' hj' ↦ ∀ (w₁ : Bin → Q ⊕ k.1)
        (s₁ : precompMerge I Q q cl j₂' = Sum.elim q k.2 ∘ w₁)
        (w₂ : Bin → Q ⊕ k.1) (_hw : w₁ = w₂)
        (b₀ : Bin → I) (r₀ : precompMerge I Q q cl j₀ = b₀)
        (s₂ : b₀ = Sum.elim q k.2 ∘ w₂)
        (n : (interpObj I O
          (precomp I O Q q (K (precompMerge I Q q cl j₀))) k).1),
        (⟨w₁, (FreeCoprodCompDisc.isoOfEq O
            (congrArg (fun m ↦ interpObj I O (K m)
              (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Q, q⟩ k)) s₁)).1
            ((FreeCoprodCompDisc.Iso.hom O
              (interpPrecompIso I O (K (precompMerge I Q q cl j₂')) Q q k)).1
              (cast (congrArg (fun t ↦ (interpObj I O
                (precomp I O Q q (K (precompMerge I Q q cl t))) k).1) hj')
                n))⟩ :
          (interpObj I O (delta I O Bin K)
            (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Q, q⟩ k)).1) =
        ⟨w₂, cast (congrArg (fun m ↦ (interpObj I O (K m)
            (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Q, q⟩ k)).1) s₂)
          ((FreeCoprodCompDisc.Iso.hom O
            (interpPrecompIso I O (K b₀) Q q k)).1
            (cast (congrArg (fun t ↦ (interpObj I O
              (precomp I O Q q (K t)) k).1) r₀) n))⟩)
      (fun w₁ s₁ _ hw ↦
        Eq.rec (motive := fun w₂' _ ↦ ∀ (b₀ : Bin → I)
            (r₀ : precompMerge I Q q cl j₀ = b₀)
            (s₂ : b₀ = Sum.elim q k.2 ∘ w₂')
            (n : (interpObj I O
              (precomp I O Q q (K (precompMerge I Q q cl j₀))) k).1),
            (⟨w₁, (FreeCoprodCompDisc.isoOfEq O
                (congrArg (fun m ↦ interpObj I O (K m)
                  (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Q, q⟩ k))
                  s₁)).1
                ((FreeCoprodCompDisc.Iso.hom O
                  (interpPrecompIso I O (K (precompMerge I Q q cl j₀))
                    Q q k)).1 n)⟩ :
              (interpObj I O (delta I O Bin K)
                (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Q, q⟩ k)).1) =
            ⟨w₂', cast (congrArg (fun m ↦ (interpObj I O (K m)
                (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Q, q⟩ k)).1)
                s₂)
              ((FreeCoprodCompDisc.Iso.hom O
                (interpPrecompIso I O (K b₀) Q q k)).1
                (cast (congrArg (fun t ↦ (interpObj I O
                  (precomp I O Q q (K t)) k).1) r₀) n))⟩)
          (fun _ r₀ ↦
            Eq.rec (motive := fun b₀' r₀' ↦ ∀
                (s₂ : b₀' = Sum.elim q k.2 ∘ w₁)
                (n : (interpObj I O
                  (precomp I O Q q (K (precompMerge I Q q cl j₀))) k).1),
                (⟨w₁, (FreeCoprodCompDisc.isoOfEq O
                    (congrArg (fun m ↦ interpObj I O (K m)
                      (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Q, q⟩ k))
                      s₁)).1
                    ((FreeCoprodCompDisc.Iso.hom O
                      (interpPrecompIso I O (K (precompMerge I Q q cl j₀))
                        Q q k)).1 n)⟩ :
                  (interpObj I O (delta I O Bin K)
                    (FreeCoprodCompDisc.plus.{uI, uB, max uA uB}
                      I ⟨Q, q⟩ k)).1) =
                ⟨w₁, cast (congrArg (fun m ↦ (interpObj I O (K m)
                    (FreeCoprodCompDisc.plus.{uI, uB, max uA uB}
                      I ⟨Q, q⟩ k)).1) s₂)
                  ((FreeCoprodCompDisc.Iso.hom O
                    (interpPrecompIso I O (K b₀') Q q k)).1
                    (cast (congrArg (fun t ↦ (interpObj I O
                      (precomp I O Q q (K t)) k).1) r₀') n))⟩)
              (fun s₂ n ↦
                congrArg
                  (fun t ↦ (⟨w₁, t⟩ :
                    (interpObj I O (delta I O Bin K)
                      (FreeCoprodCompDisc.plus.{uI, uB, max uA uB}
                        I ⟨Q, q⟩ k)).1))
                  (interpObj_isoOfEq_cast I O Bin K
                    (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Q, q⟩ k)
                    (precompMerge I Q q cl j₀) (Sum.elim q k.2 ∘ w₁) s₁ s₂
                    ((FreeCoprodCompDisc.Iso.hom O
                      (interpPrecompIso I O (K (precompMerge I Q q cl j₀))
                        Q q k)).1 n)))
              r₀)
          hw)
      hj

/-- The all-resolved navigation square: the composite inclusion of the
`IR.deltaNavBase` characterization, pushed through the Lemma 4
isomorphism, is the copower injection at the graph weight of the
factorization followed by the summand inclusion, after the summand's
Lemma 4 isomorphism. -/
theorem interpPrecompIso_deltaNav_inj (Bout : Type uB) (iout : Bout → I)
    (Bin : Type uB) (K : (Bin → I) → IR.{max uA uB, uB, uI, uO} I O)
    (g : Bin → Bout) (X : FreeCoprodCompDisc.{max uA uB, uI} I) :
    FreeCoprodCompDisc.Hom.comp O
        (FreeCoprodCompDisc.Hom.comp O
          (deltaEmptyInj I O
            {z : Bin // (fun b ↦ Sum.inl (g b) : Bin → Bout ⊕ PUnit.{uB + 1}) z =
              Sum.inr PUnit.unit}
            (fun z ↦ nomatch z.2)
            (fun j ↦ precomp I O Bout iout
              (K (precompMerge I Bout iout (fun b ↦ Sum.inl (g b)) j)))
            X)
          (FreeCoprodCompDisc.coprodInj O
            (ULift.{max uA uB} (Bin → Bout ⊕ PUnit.{uB + 1}))
            (fun cl ↦ interpObj I O
              (delta I O {z : Bin // cl.down z = Sum.inr PUnit.unit}
                (fun j ↦ precomp I O Bout iout
                  (K (precompMerge I Bout iout cl.down j)))) X)
            (ULift.up (fun b ↦ Sum.inl (g b)))))
        (FreeCoprodCompDisc.Iso.hom O
          (interpPrecompIso I O (delta I O Bin K) Bout iout X)) =
      FreeCoprodCompDisc.Hom.comp O
        (FreeCoprodCompDisc.Hom.comp O
          (FreeCoprodCompDisc.Iso.hom O
            (interpPrecompIso I O (K (iout ∘ g)) Bout iout X))
          (FreeCoprodCompDisc.coprodInj O
            (FreeCoprodCompDisc.Hom I
              (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Bin, iout ∘ g⟩)
              (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Bout, iout⟩ X))
            (fun _ ↦ interpObj I O (K (iout ∘ g))
              (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Bout, iout⟩ X))
            ⟨fun z ↦ Sum.inl (g z.down), rfl⟩))
        (deltaInto I O Bin K (iout ∘ g)
          (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Bout, iout⟩ X)) :=
  (congrArg
      (fun t ↦ FreeCoprodCompDisc.Hom.comp O
        (FreeCoprodCompDisc.Hom.comp O
          (deltaEmptyInj I O
            {z : Bin // (fun b ↦ Sum.inl (g b) : Bin → Bout ⊕ PUnit.{uB + 1}) z =
              Sum.inr PUnit.unit}
            (fun z ↦ nomatch z.2)
            (fun j ↦ precomp I O Bout iout
              (K (precompMerge I Bout iout (fun b ↦ Sum.inl (g b)) j)))
            X)
          (FreeCoprodCompDisc.coprodInj O
            (ULift.{max uA uB} (Bin → Bout ⊕ PUnit.{uB + 1}))
            (fun cl ↦ interpObj I O
              (delta I O {z : Bin // cl.down z = Sum.inr PUnit.unit}
                (fun j ↦ precomp I O Bout iout
                  (K (precompMerge I Bout iout cl.down j)))) X)
            (ULift.up (fun b ↦ Sum.inl (g b)))))
        (FreeCoprodCompDisc.Iso.hom O (t Bout iout X)))
      (interpPrecompIso_mk I O (Sum.inr (Sum.inr Bin)) (K ∘ ULift.down))).trans
    (Subtype.ext (funext (fun n ↦
      ((rfl :
        (FreeCoprodCompDisc.Hom.comp O
            (FreeCoprodCompDisc.Hom.comp O
              (deltaEmptyInj I O
                {z : Bin //
                  (fun b ↦ Sum.inl (g b) : Bin → Bout ⊕ PUnit.{uB + 1}) z =
                    Sum.inr PUnit.unit}
                (fun z ↦ nomatch z.2)
                (fun j ↦ precomp I O Bout iout
                  (K (precompMerge I Bout iout (fun b ↦ Sum.inl (g b)) j)))
                X)
              (FreeCoprodCompDisc.coprodInj O
                (ULift.{max uA uB} (Bin → Bout ⊕ PUnit.{uB + 1}))
                (fun cl ↦ interpObj I O
                  (delta I O {z : Bin // cl.down z = Sum.inr PUnit.unit}
                    (fun j ↦ precomp I O Bout iout
                      (K (precompMerge I Bout iout cl.down j)))) X)
                (ULift.up (fun b ↦ Sum.inl (g b)))))
            (FreeCoprodCompDisc.Iso.hom O
              (interpPrecompIsoStep I O (Sum.inr (Sum.inr Bin)) (K ∘ ULift.down)
                (fun x ↦ interpPrecompIso I O ((K ∘ ULift.down) x))
                Bout iout X))).1 n =
          (⟨arrowSumMerge (fun b ↦ Sum.inl (g b))
            (fun z ↦ ((nomatch z.2 : PEmpty.{1}).elim : X.1)),
          (FreeCoprodCompDisc.isoOfEq O
            (congrArg
              (fun m ↦ interpObj I O (K m)
                (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Bout, iout⟩ X))
              (precompMerge_elim I Bout iout X Bin (fun b ↦ Sum.inl (g b))
                (fun z ↦ ((nomatch z.2 : PEmpty.{1}).elim : X.1))))).1
            ((FreeCoprodCompDisc.Iso.hom O
              (interpPrecompIso I O
                (K (precompMerge I Bout iout (fun b ↦ Sum.inl (g b))
                  (fun z ↦ X.2 ((nomatch z.2 : PEmpty.{1}).elim))))
                Bout iout X)).1
              (cast
                (congrArg
                  (fun t ↦ (interpObj I O (precomp I O Bout iout
                    (K (precompMerge I Bout iout (fun b ↦ Sum.inl (g b)) t)))
                    X).1)
                  (funext (fun z ↦ nomatch z.2) :
                    (fun x : {z : Bin //
                        (fun b ↦ Sum.inl (g b) :
                          Bin → Bout ⊕ PUnit.{uB + 1}) z =
                          Sum.inr PUnit.unit} ↦
                      ((nomatch x.2 : PEmpty.{1}).elim : I)) =
                      fun z : {z : Bin //
                        (fun b ↦ Sum.inl (g b) :
                          Bin → Bout ⊕ PUnit.{uB + 1}) z =
                          Sum.inr PUnit.unit} ↦
                        X.2 ((nomatch z.2 : PEmpty.{1}).elim)))
                n))⟩ :
          (interpObj I O (delta I O Bin K)
            (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Bout, iout⟩ X)).1)).trans
        ((deltaNav_strip I O Bin K Bout iout X (fun b ↦ Sum.inl (g b))
          (fun x ↦ ((nomatch x.2 : PEmpty.{1}).elim : I))
          (fun z ↦ X.2 ((nomatch z.2 : PEmpty.{1}).elim))
          (funext (fun z ↦ nomatch z.2))
          (arrowSumMerge (fun b ↦ Sum.inl (g b))
            (fun z ↦ ((nomatch z.2 : PEmpty.{1}).elim : X.1)))
          (precompMerge_elim I Bout iout X Bin (fun b ↦ Sum.inl (g b))
            (fun z ↦ ((nomatch z.2 : PEmpty.{1}).elim : X.1)))
          (fun z ↦ (Sum.inl (g z) : Bout ⊕ X.1))
          rfl
          (iout ∘ g)
          (funext (fun _ ↦ rfl))
          (funext (fun _ ↦ rfl))
          n).trans
          (rfl :
            (FreeCoprodCompDisc.Hom.comp O
            (FreeCoprodCompDisc.Hom.comp O
              (FreeCoprodCompDisc.Iso.hom O
                (interpPrecompIso I O (K (iout ∘ g)) Bout iout X))
              (FreeCoprodCompDisc.coprodInj O
                (FreeCoprodCompDisc.Hom I
                  (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I
                    ⟨Bin, iout ∘ g⟩)
                  (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I
                    ⟨Bout, iout⟩ X))
                (fun _ ↦ interpObj I O (K (iout ∘ g))
                  (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I
                    ⟨Bout, iout⟩ X))
                ⟨fun z ↦ Sum.inl (g z.down), rfl⟩))
            (deltaInto I O Bin K (iout ∘ g)
              (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I
                ⟨Bout, iout⟩ X))).1 n =
              (⟨fun z ↦ Sum.inl (g z),
          cast
            (congrArg
              (fun m ↦ (interpObj I O (K m)
                (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I
                  ⟨Bout, iout⟩ X)).1)
              (funext (fun _ ↦ rfl) :
                iout ∘ g = Sum.elim iout X.2 ∘ fun z : Bin ↦ Sum.inl (g z)))
            ((FreeCoprodCompDisc.Iso.hom O
              (interpPrecompIso I O (K (iout ∘ g)) Bout iout X)).1
              (cast
                (congrArg
                  (fun t ↦ (interpObj I O
                    (precomp I O Bout iout (K t)) X).1)
                  (funext (fun _ ↦ rfl) :
                    precompMerge I Bout iout (fun b ↦ Sum.inl (g b))
                        (fun x : {z : Bin //
                          (fun b ↦ Sum.inl (g b) :
                            Bin → Bout ⊕ PUnit.{uB + 1}) z =
                              Sum.inr PUnit.unit} ↦
                          ((nomatch x.2 : PEmpty.{1}).elim : I)) =
                      iout ∘ g))
                n))⟩ :
          (interpObj I O (delta I O Bin K)
            (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Bout, iout⟩ X)).1)).symm)))))

/-- The tower navigation weight: the graph of the factorization into
the appended superscript, followed by the iterated right injection up
the tower. By `List.rec`, so the `cons` equation is definitional. -/
def navWeight (Bout : Type uB) (iout : Bout → I) (Bin : Type uB) (g : Bin → Bout)
    (X : FreeCoprodCompDisc.{max uA uB, uI} I) (L : List (SupObj.{uB, uI} I)) :
    FreeCoprodCompDisc.Hom I
      (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Bin, iout ∘ g⟩)
      (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X) :=
  L.rec (motive := fun L' : List (SupObj.{uB, uI} I) ↦
      FreeCoprodCompDisc.Hom I
        (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Bin, iout ∘ g⟩)
        (mplus.{uA, uB, uI} I (L' ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X))
    ⟨fun z ↦ Sum.inl (g z.down), rfl⟩
    (fun a _L ih ↦
      FreeCoprodCompDisc.Hom.comp I ih
        (FreeCoprodCompDisc.coprodPairInr.{uI, uB, max uA uB} I a
          (mplus.{uA, uB, uI} I (_L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X)))

/-- `IR.navWeight`, transported along `IR.mplus_snoc`, is the graph
weight at the base followed by the tower injection `IR.mplusInj`. -/
theorem navWeight_snoc (Bout : Type uB) (iout : Bout → I) (Bin : Type uB)
    (g : Bin → Bout) (X : FreeCoprodCompDisc.{max uA uB, uI} I)
    (L : List (SupObj.{uB, uI} I)) :
    cast
        (congrArg
          (FreeCoprodCompDisc.Hom I
            (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Bin, iout ∘ g⟩))
          (mplus_snoc.{uA, uB, uI} I L (⟨Bout, iout⟩ : SupObj.{uB, uI} I) X))
        (navWeight I Bout iout Bin g X L) =
      FreeCoprodCompDisc.Hom.comp I
        (⟨fun z ↦ Sum.inl (g z.down), rfl⟩ :
          FreeCoprodCompDisc.Hom I
            (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Bin, iout ∘ g⟩)
            (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Bout, iout⟩ X))
        (mplusInj.{uA, uB, uI} I L
          (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Bout, iout⟩ X)) :=
  L.rec (motive := fun L' ↦
      cast
          (congrArg
            (FreeCoprodCompDisc.Hom I
              (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Bin, iout ∘ g⟩))
            (mplus_snoc.{uA, uB, uI} I L' (⟨Bout, iout⟩ : SupObj.{uB, uI} I) X))
          (navWeight I Bout iout Bin g X L') =
        FreeCoprodCompDisc.Hom.comp I
          (⟨fun z ↦ Sum.inl (g z.down), rfl⟩ :
            FreeCoprodCompDisc.Hom I
              (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Bin, iout ∘ g⟩)
              (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Bout, iout⟩ X))
          (mplusInj.{uA, uB, uI} I L'
            (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Bout, iout⟩ X)))
    (FreeCoprodCompDisc.Hom.comp_id I
      (⟨fun z ↦ Sum.inl (g z.down), rfl⟩ :
        FreeCoprodCompDisc.Hom I
          (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Bin, iout ∘ g⟩)
          (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Bout, iout⟩ X))).symm
    (fun a _L ih ↦
      (comp_coprodPairInr_cast I a
          (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Bin, iout ∘ g⟩)
          (mplus.{uA, uB, uI} I (_L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X)
          (mplus.{uA, uB, uI} I _L
            (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Bout, iout⟩ X))
          (mplus_snoc.{uA, uB, uI} I _L (⟨Bout, iout⟩ : SupObj.{uB, uI} I) X)
          (navWeight I Bout iout Bin g X _L)).trans
        ((congrArg
            (fun t ↦ FreeCoprodCompDisc.Hom.comp I t
              (FreeCoprodCompDisc.coprodPairInr.{uI, uB, max uA uB} I a
                (mplus.{uA, uB, uI} I _L
                  (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I
                    ⟨Bout, iout⟩ X))))
            ih).trans
          (FreeCoprodCompDisc.Hom.comp_assoc I
            (⟨fun z ↦ Sum.inl (g z.down), rfl⟩ :
              FreeCoprodCompDisc.Hom I
                (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Bin, iout ∘ g⟩)
                (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Bout, iout⟩ X))
            (mplusInj.{uA, uB, uI} I _L
              (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Bout, iout⟩ X))
            (FreeCoprodCompDisc.coprodPairInr.{uI, uB, max uA uB} I a
              (mplus.{uA, uB, uI} I _L
                (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I
                  ⟨Bout, iout⟩ X))))))

/-- The reindexing of a lifted direction family along the inclusion of
the all-unresolved classifier's subtype (all of the arity). -/
def navReindex (Bin : Type uB) (j : Bin → I) (Q : Type uB) :
    FreeCoprodCompDisc.Hom I
      (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Bin, j⟩)
      (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I
        ⟨{z : Bin //
            (fun _ : Bin ↦ (Sum.inr PUnit.unit : Q ⊕ PUnit.{uB + 1})) z =
              Sum.inr PUnit.unit},
          fun z ↦ j z.1⟩) :=
  ⟨fun z ↦ ULift.up ⟨z.down, rfl⟩, rfl⟩

/-- `IR.navWeight` at the all-unresolved classifier's subtype,
restricted along `IR.navReindex`, is `IR.navWeight` at the base
arity. -/
theorem navWeight_reindex (Bout : Type uB) (iout : Bout → I) (Bin : Type uB)
    (g : Bin → Bout) (Q : Type uB) (X : FreeCoprodCompDisc.{max uA uB, uI} I)
    (L : List (SupObj.{uB, uI} I)) :
    FreeCoprodCompDisc.Hom.comp I (navReindex.{uA, uB, uI} I Bin (iout ∘ g) Q)
        (navWeight I Bout iout
          {z : Bin //
            (fun _ : Bin ↦ (Sum.inr PUnit.unit : Q ⊕ PUnit.{uB + 1})) z =
              Sum.inr PUnit.unit}
          (fun z ↦ g z.1) X L) =
      navWeight I Bout iout Bin g X L :=
  L.rec (motive := fun L' ↦
      FreeCoprodCompDisc.Hom.comp I (navReindex.{uA, uB, uI} I Bin (iout ∘ g) Q)
          (navWeight I Bout iout
            {z : Bin //
              (fun _ : Bin ↦ (Sum.inr PUnit.unit : Q ⊕ PUnit.{uB + 1})) z =
                Sum.inr PUnit.unit}
            (fun z ↦ g z.1) X L') =
        navWeight I Bout iout Bin g X L')
    (Subtype.ext rfl)
    (fun a _L ih ↦
      (FreeCoprodCompDisc.Hom.comp_assoc I
          (navReindex.{uA, uB, uI} I Bin (iout ∘ g) Q)
          (navWeight I Bout iout
            {z : Bin //
              (fun _ : Bin ↦ (Sum.inr PUnit.unit : Q ⊕ PUnit.{uB + 1})) z =
                Sum.inr PUnit.unit}
            (fun z ↦ g z.1) X _L)
          (FreeCoprodCompDisc.coprodPairInr.{uI, uB, max uA uB} I a
            (mplus.{uA, uB, uI} I
              (_L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X))).symm.trans
        (congrArg
          (fun t ↦ FreeCoprodCompDisc.Hom.comp I t
            (FreeCoprodCompDisc.coprodPairInr.{uI, uB, max uA uB} I a
              (mplus.{uA, uB, uI} I
                (_L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X)))
          ih))

/-- The all-unresolved navigation square: the copower injection into
the all-unresolved classifier summand, pushed through the Lemma 4
isomorphism, is the copower injection at the reindexed weight followed
by the summand inclusion, after the summand's Lemma 4 isomorphism. -/
theorem interpPrecompIso_deltaNavAll_inj (Bin : Type uB)
    (K : (Bin → I) → IR.{max uA uB, uB, uI, uO} I O)
    (Q : Type uB) (q : Q → I) (j : Bin → I)
    (k : FreeCoprodCompDisc.{max uA uB, uI} I)
    (u : FreeCoprodCompDisc.Hom I
      (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I
        ⟨{z : Bin //
          (fun _ : Bin ↦ (Sum.inr PUnit.unit : Q ⊕ PUnit.{uB + 1})) z = Sum.inr PUnit.unit},
          fun z ↦ j z.1⟩)
      k) :
    FreeCoprodCompDisc.Hom.comp O
        (FreeCoprodCompDisc.Hom.comp O
          (FreeCoprodCompDisc.Hom.comp O
            (FreeCoprodCompDisc.coprodInj O
              (FreeCoprodCompDisc.Hom I
                (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I
                  ⟨{z : Bin //
                    (fun _ : Bin ↦ (Sum.inr PUnit.unit : Q ⊕ PUnit.{uB + 1}))
                      z = Sum.inr PUnit.unit},
                    fun z ↦ j z.1⟩)
                k)
              (fun _ ↦ interpObj I O
                (precomp I O Q q (K (precompMerge I Q q
                  (fun _ : Bin ↦ (Sum.inr PUnit.unit : Q ⊕ PUnit.{uB + 1}))
                  (fun z : {z : Bin //
                    (fun _ : Bin ↦ (Sum.inr PUnit.unit : Q ⊕ PUnit.{uB + 1}))
                      z = Sum.inr PUnit.unit} ↦
                    j z.1))))
                k)
              u)
            (deltaInto I O {z : Bin //
              (fun _ : Bin ↦ (Sum.inr PUnit.unit : Q ⊕ PUnit.{uB + 1})) z = Sum.inr PUnit.unit}
              (fun m ↦ precomp I O Q q (K (precompMerge I Q q
                (fun _ : Bin ↦ (Sum.inr PUnit.unit : Q ⊕ PUnit.{uB + 1})) m)))
              (fun z ↦ j z.1) k))
          (FreeCoprodCompDisc.coprodInj O
            (ULift.{max uA uB} (Bin → Q ⊕ PUnit.{uB + 1}))
            (fun cl ↦ interpObj I O
              (delta I O {z : Bin // cl.down z = Sum.inr PUnit.unit}
                (fun m ↦ precomp I O Q q
                  (K (precompMerge I Q q cl.down m)))) k)
            (ULift.up (fun _ : Bin ↦ (Sum.inr PUnit.unit : Q ⊕ PUnit.{uB + 1})))))
        (FreeCoprodCompDisc.Iso.hom O
          (interpPrecompIso I O (delta I O Bin K) Q q k)) =
      FreeCoprodCompDisc.Hom.comp O
        (FreeCoprodCompDisc.Hom.comp O
          (FreeCoprodCompDisc.Iso.hom O (interpPrecompIso I O (K j) Q q k))
          (FreeCoprodCompDisc.coprodInj O
            (FreeCoprodCompDisc.Hom I
              (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Bin, j⟩)
              (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Q, q⟩ k))
            (fun _ ↦ interpObj I O (K j)
              (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Q, q⟩ k))
            (FreeCoprodCompDisc.Hom.comp I (navReindex.{uA, uB, uI} I Bin j Q)
              (FreeCoprodCompDisc.Hom.comp I u
                (FreeCoprodCompDisc.coprodPairInr.{uI, uB, max uA uB} I ⟨Q, q⟩ k)))))
        (deltaInto I O Bin K j
          (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Q, q⟩ k)) :=
  (congrArg
      (fun t ↦ FreeCoprodCompDisc.Hom.comp O
        (FreeCoprodCompDisc.Hom.comp O
          (FreeCoprodCompDisc.Hom.comp O
            (FreeCoprodCompDisc.coprodInj O
              (FreeCoprodCompDisc.Hom I
                (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I
                  ⟨{z : Bin //
                    (fun _ : Bin ↦ (Sum.inr PUnit.unit : Q ⊕ PUnit.{uB + 1}))
                      z = Sum.inr PUnit.unit},
                    fun z ↦ j z.1⟩)
                k)
              (fun _ ↦ interpObj I O
                (precomp I O Q q (K (precompMerge I Q q
                  (fun _ : Bin ↦ (Sum.inr PUnit.unit : Q ⊕ PUnit.{uB + 1}))
                  (fun z : {z : Bin //
                    (fun _ : Bin ↦ (Sum.inr PUnit.unit : Q ⊕ PUnit.{uB + 1}))
                      z = Sum.inr PUnit.unit} ↦
                    j z.1))))
                k)
              u)
            (deltaInto I O {z : Bin //
              (fun _ : Bin ↦ (Sum.inr PUnit.unit : Q ⊕ PUnit.{uB + 1})) z = Sum.inr PUnit.unit}
              (fun m ↦ precomp I O Q q (K (precompMerge I Q q
                (fun _ : Bin ↦ (Sum.inr PUnit.unit : Q ⊕ PUnit.{uB + 1})) m)))
              (fun z ↦ j z.1) k))
          (FreeCoprodCompDisc.coprodInj O
            (ULift.{max uA uB} (Bin → Q ⊕ PUnit.{uB + 1}))
            (fun cl ↦ interpObj I O
              (delta I O {z : Bin // cl.down z = Sum.inr PUnit.unit}
                (fun m ↦ precomp I O Q q
                  (K (precompMerge I Q q cl.down m)))) k)
            (ULift.up (fun _ : Bin ↦ (Sum.inr PUnit.unit : Q ⊕ PUnit.{uB + 1})))))
        (FreeCoprodCompDisc.Iso.hom O (t Q q k)))
      (interpPrecompIso_mk I O (Sum.inr (Sum.inr Bin)) (K ∘ ULift.down))).trans
    (Subtype.ext (funext (fun n ↦
      ((rfl :
        (FreeCoprodCompDisc.Hom.comp O
            (FreeCoprodCompDisc.Hom.comp O
              (FreeCoprodCompDisc.Hom.comp O
                (FreeCoprodCompDisc.coprodInj O
                  (FreeCoprodCompDisc.Hom I
                    (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I
                      ⟨{z : Bin //
                        (fun _ : Bin ↦ (Sum.inr PUnit.unit : Q ⊕ PUnit.{uB + 1}))
                          z = Sum.inr PUnit.unit},
                        fun z ↦ j z.1⟩)
                    k)
                  (fun _ ↦ interpObj I O
                    (precomp I O Q q (K (precompMerge I Q q
                      (fun _ : Bin ↦ (Sum.inr PUnit.unit : Q ⊕ PUnit.{uB + 1}))
                      (fun z : {z : Bin //
                        (fun _ : Bin ↦ (Sum.inr PUnit.unit : Q ⊕ PUnit.{uB + 1}))
                          z = Sum.inr PUnit.unit} ↦
                        j z.1))))
                    k)
                  u)
                (deltaInto I O {z : Bin //
                  (fun _ : Bin ↦ (Sum.inr PUnit.unit : Q ⊕ PUnit.{uB + 1})) z = Sum.inr PUnit.unit}
                  (fun m ↦ precomp I O Q q (K (precompMerge I Q q
                    (fun _ : Bin ↦ (Sum.inr PUnit.unit : Q ⊕ PUnit.{uB + 1})) m)))
                  (fun z ↦ j z.1) k))
              (FreeCoprodCompDisc.coprodInj O
                (ULift.{max uA uB} (Bin → Q ⊕ PUnit.{uB + 1}))
                (fun cl ↦ interpObj I O
                  (delta I O {z : Bin // cl.down z = Sum.inr PUnit.unit}
                    (fun m ↦ precomp I O Q q
                      (K (precompMerge I Q q cl.down m)))) k)
                (ULift.up (fun _ : Bin ↦ (Sum.inr PUnit.unit : Q ⊕ PUnit.{uB + 1})))))
            (FreeCoprodCompDisc.Iso.hom O
              (interpPrecompIsoStep I O (Sum.inr (Sum.inr Bin))
                (K ∘ ULift.down)
                (fun x ↦ interpPrecompIso I O ((K ∘ ULift.down) x))
                Q q k))).1 n =
          (⟨arrowSumMerge
            (fun _ : Bin ↦ (Sum.inr PUnit.unit : Q ⊕ PUnit.{uB + 1})) (fun z ↦ u.1 (ULift.up z)),
            (FreeCoprodCompDisc.isoOfEq O
              (congrArg
                (fun m ↦ interpObj I O (K m)
                  (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Q, q⟩ k))
                (precompMerge_elim I Q q k Bin
                  (fun _ : Bin ↦ (Sum.inr PUnit.unit : Q ⊕ PUnit.{uB + 1}))
                  (fun z ↦ u.1 (ULift.up z))))).1
              ((FreeCoprodCompDisc.Iso.hom O
                (interpPrecompIso I O
                  (K (precompMerge I Q q (fun _ : Bin ↦ (Sum.inr PUnit.unit : Q ⊕ PUnit.{uB + 1}))
                    (fun z ↦ k.2 (u.1 (ULift.up z)))))
                  Q q k)).1
                (cast
                  (congrArg
                    (fun t ↦ (interpObj I O (precomp I O Q q
                      (K (precompMerge I Q q
                        (fun _ : Bin ↦ (Sum.inr PUnit.unit : Q ⊕ PUnit.{uB + 1})) t))) k).1)
                    (funext (fun z ↦ (congrFun u.2 (ULift.up z)).symm) :
                      (fun z : {z : Bin //
                        (fun _ : Bin ↦ (Sum.inr PUnit.unit : Q ⊕ PUnit.{uB + 1}))
                          z = Sum.inr PUnit.unit} ↦
                        j z.1) =
                        fun z : {z : Bin //
                          (fun _ : Bin ↦ (Sum.inr PUnit.unit : Q ⊕ PUnit.{uB + 1}))
                            z = Sum.inr PUnit.unit} ↦
                          k.2 (u.1 (ULift.up z))))
                  n))⟩ :
            (interpObj I O (delta I O Bin K)
              (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Q, q⟩ k)).1)).trans
        ((deltaNav_strip I O Bin K Q q k (fun _ : Bin ↦ (Sum.inr PUnit.unit : Q ⊕ PUnit.{uB + 1}))
          (fun z ↦ j z.1)
          (fun z ↦ k.2 (u.1 (ULift.up z)))
          (funext (fun z ↦ (congrFun u.2 (ULift.up z)).symm))
          (arrowSumMerge
            (fun _ : Bin ↦ (Sum.inr PUnit.unit : Q ⊕ PUnit.{uB + 1})) (fun z ↦ u.1 (ULift.up z)))
          (precompMerge_elim I Q q k Bin
            (fun _ : Bin ↦ (Sum.inr PUnit.unit : Q ⊕ PUnit.{uB + 1})) (fun z ↦ u.1 (ULift.up z)))
          (fun b ↦ (Sum.inr (u.1 (ULift.up ⟨b, rfl⟩)) : Q ⊕ k.1))
          rfl
          j
          (funext (fun _ ↦ rfl))
          (funext (fun b ↦ (congrFun u.2 (ULift.up ⟨b, rfl⟩)).symm))
          n).trans
          (rfl :
            (FreeCoprodCompDisc.Hom.comp O
                (FreeCoprodCompDisc.Hom.comp O
                  (FreeCoprodCompDisc.Iso.hom O
                    (interpPrecompIso I O (K j) Q q k))
                  (FreeCoprodCompDisc.coprodInj O
                    (FreeCoprodCompDisc.Hom I
                      (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Bin, j⟩)
                      (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Q, q⟩ k))
                    (fun _ ↦ interpObj I O (K j)
                      (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Q, q⟩ k))
                    (FreeCoprodCompDisc.Hom.comp I
                      (navReindex.{uA, uB, uI} I Bin j Q)
                      (FreeCoprodCompDisc.Hom.comp I u
                        (FreeCoprodCompDisc.coprodPairInr.{uI, uB, max uA uB} I ⟨Q, q⟩ k)))))
                (deltaInto I O Bin K j
                  (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I
                    ⟨Q, q⟩ k))).1 n =
              (⟨fun b ↦ (Sum.inr (u.1 (ULift.up ⟨b, rfl⟩)) : Q ⊕ k.1),
                cast
                  (congrArg
                    (fun m ↦ (interpObj I O (K m)
                      (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I
                        ⟨Q, q⟩ k)).1)
                    (funext
                      (fun b ↦ (congrFun u.2 (ULift.up ⟨b, rfl⟩)).symm) :
                      j = Sum.elim q k.2 ∘
                        fun b : Bin ↦
                          (Sum.inr (u.1 (ULift.up ⟨b, rfl⟩)) : Q ⊕ k.1)))
                  ((FreeCoprodCompDisc.Iso.hom O
                    (interpPrecompIso I O (K j) Q q k)).1
                    (cast
                      (congrArg
                        (fun t ↦ (interpObj I O
                          (precomp I O Q q (K t)) k).1)
                        (funext (fun _ ↦ rfl) :
                          precompMerge I Q q
                            (fun _ : Bin ↦ (Sum.inr PUnit.unit : Q ⊕ PUnit.{uB + 1}))
                              (fun z : {z : Bin //
                                (fun _ : Bin ↦ (Sum.inr PUnit.unit : Q ⊕ PUnit.{uB + 1}))
                                  z = Sum.inr PUnit.unit} ↦
                                j z.1) =
                            j))
                      n))⟩ :
                (interpObj I O (delta I O Bin K)
                  (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I
                    ⟨Q, q⟩ k)).1)).symm)))))

/-- The tower-conjugated navigation inclusion: the copower injection
at the `IR.navWeight` weight followed by the summand inclusion, both
at the tower coproduct, conjugated by the iterated Lemma 4
isomorphisms. -/
def navInj (Bout : Type uB) (iout : Bout → I) (Bin : Type uB)
    (K : (Bin → I) → IR.{max uA uB, uB, uI, uO} I O) (g : Bin → Bout)
    (L : List (SupObj.{uB, uI} I)) (X : FreeCoprodCompDisc.{max uA uB, uI} I) :
    FreeCoprodCompDisc.Hom O
      (interpObj I O
        (mprecomp I O (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)])
          (K (iout ∘ g))) X)
      (interpObj I O
        (mprecomp I O (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)])
          (delta I O Bin K)) X) :=
  FreeCoprodCompDisc.Hom.comp O
    (FreeCoprodCompDisc.Hom.comp O
      (FreeCoprodCompDisc.Iso.hom O
        (mprecompIso.{uA, uB, uI, uO} I O
          (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) (K (iout ∘ g)) X))
      (FreeCoprodCompDisc.Hom.comp O
        (FreeCoprodCompDisc.coprodInj O
          (FreeCoprodCompDisc.Hom I
            (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Bin, iout ∘ g⟩)
            (mplus.{uA, uB, uI} I
              (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X))
          (fun _ ↦ interpObj I O (K (iout ∘ g))
            (mplus.{uA, uB, uI} I
              (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X))
          (navWeight I Bout iout Bin g X L))
        (deltaInto I O Bin K (iout ∘ g)
          (mplus.{uA, uB, uI} I
            (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X))))
    (FreeCoprodCompDisc.Iso.invHom O
      (mprecompIso.{uA, uB, uI, uO} I O
        (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) (delta I O Bin K) X))

/-- The base-inclusion equation: the composite inclusion of the
`IR.deltaNavBase` characterization is `IR.navInj` at the empty
stack. -/
theorem navInj_nil (Bout : Type uB) (iout : Bout → I) (Bin : Type uB)
    (K : (Bin → I) → IR.{max uA uB, uB, uI, uO} I O) (g : Bin → Bout)
    (X : FreeCoprodCompDisc.{max uA uB, uI} I) :
    FreeCoprodCompDisc.Hom.comp O
        (deltaEmptyInj I O
          {z : Bin // (fun b ↦ Sum.inl (g b) : Bin → Bout ⊕ PUnit.{uB + 1}) z =
            Sum.inr PUnit.unit}
          (fun z ↦ nomatch z.2)
          (fun j ↦ precomp I O Bout iout
            (K (precompMerge I Bout iout (fun b ↦ Sum.inl (g b)) j)))
          X)
        (FreeCoprodCompDisc.coprodInj O
          (ULift.{max uA uB} (Bin → Bout ⊕ PUnit.{uB + 1}))
          (fun cl ↦ interpObj I O
            (delta I O {z : Bin // cl.down z = Sum.inr PUnit.unit}
              (fun j ↦ precomp I O Bout iout
                (K (precompMerge I Bout iout cl.down j)))) X)
          (ULift.up (fun b ↦ Sum.inl (g b)))) =
      navInj I O Bout iout Bin K g [] X :=
  (FreeCoprodCompDisc.eq_comp_invHom O
      (interpObj I O (precomp I O Bout iout (K (iout ∘ g))) X)
      (interpObj I O (precomp I O Bout iout (delta I O Bin K)) X)
      (interpObj I O (delta I O Bin K)
        (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Bout, iout⟩ X))
      (FreeCoprodCompDisc.Hom.comp O
        (deltaEmptyInj I O
          {z : Bin // (fun b ↦ Sum.inl (g b) : Bin → Bout ⊕ PUnit.{uB + 1}) z =
            Sum.inr PUnit.unit}
          (fun z ↦ nomatch z.2)
          (fun j ↦ precomp I O Bout iout
            (K (precompMerge I Bout iout (fun b ↦ Sum.inl (g b)) j)))
          X)
        (FreeCoprodCompDisc.coprodInj O
          (ULift.{max uA uB} (Bin → Bout ⊕ PUnit.{uB + 1}))
          (fun cl ↦ interpObj I O
            (delta I O {z : Bin // cl.down z = Sum.inr PUnit.unit}
              (fun j ↦ precomp I O Bout iout
                (K (precompMerge I Bout iout cl.down j)))) X)
          (ULift.up (fun b ↦ Sum.inl (g b)))))
      (FreeCoprodCompDisc.Hom.comp O
        (FreeCoprodCompDisc.Hom.comp O
          (FreeCoprodCompDisc.Iso.hom O
            (interpPrecompIso I O (K (iout ∘ g)) Bout iout X))
          (FreeCoprodCompDisc.coprodInj O
            (FreeCoprodCompDisc.Hom I
              (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Bin, iout ∘ g⟩)
              (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Bout, iout⟩ X))
            (fun _ ↦ interpObj I O (K (iout ∘ g))
              (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Bout, iout⟩ X))
            ⟨fun z ↦ Sum.inl (g z.down), rfl⟩))
        (deltaInto I O Bin K (iout ∘ g)
          (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Bout, iout⟩ X)))
      (interpPrecompIso I O (delta I O Bin K) Bout iout X)
      (interpPrecompIso_deltaNav_inj I O Bout iout Bin K g X)).trans
    (congrArg
      (fun t ↦ FreeCoprodCompDisc.Hom.comp O t
        (FreeCoprodCompDisc.Iso.invHom O
          (interpPrecompIso I O (delta I O Bin K) Bout iout X)))
      (FreeCoprodCompDisc.Hom.comp_assoc O
        (FreeCoprodCompDisc.Iso.hom O
          (interpPrecompIso I O (K (iout ∘ g)) Bout iout X))
        (FreeCoprodCompDisc.coprodInj O
          (FreeCoprodCompDisc.Hom I
            (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Bin, iout ∘ g⟩)
            (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Bout, iout⟩ X))
          (fun _ ↦ interpObj I O (K (iout ∘ g))
            (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Bout, iout⟩ X))
          ⟨fun z ↦ Sum.inl (g z.down), rfl⟩)
        (deltaInto I O Bin K (iout ∘ g)
          (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Bout, iout⟩ X))))

/-- The cons-inclusion equation: the navigation inclusion at the
unresolved-subtype data, composed with the classifier-summand
inclusion conjugated through the tower isomorphisms, is `IR.navInj`
at the extended stack. -/
theorem navInj_cons (Bout : Type uB) (iout : Bout → I) (Bin : Type uB)
    (K : (Bin → I) → IR.{max uA uB, uB, uI, uO} I O) (g : Bin → Bout)
    (a : SupObj.{uB, uI} I) (L : List (SupObj.{uB, uI} I))
    (X : FreeCoprodCompDisc.{max uA uB, uI} I) :
    FreeCoprodCompDisc.Hom.comp O
        (navInj I O Bout iout
          {z : Bin //
            (fun _ : Bin ↦ (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) z =
              Sum.inr PUnit.unit}
          (fun m ↦ precomp I O a.1 a.2 (K (precompMerge I a.1 a.2
            (fun _ : Bin ↦ (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) m)))
          (fun z ↦ g z.1) L X)
        (FreeCoprodCompDisc.Hom.comp O
            (FreeCoprodCompDisc.Hom.comp O
              (FreeCoprodCompDisc.Iso.hom O
                (mprecompIso.{uA, uB, uI, uO} I O (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)])
                    (delta I O
                      {z : Bin //
                        (fun _ : Bin ↦ (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) z =
                          Sum.inr PUnit.unit}
                      (fun m ↦ precomp I O a.1 a.2 (K (precompMerge I a.1 a.2
                        (fun _ : Bin ↦ (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) m))))
                    X))
              (FreeCoprodCompDisc.coprodInj O
                (ULift.{max uA uB, uB} (Bin → a.1 ⊕ PUnit.{uB + 1}))
                (fun cl ↦ interpObj I O
                  (delta I O {z : Bin // cl.down z = Sum.inr PUnit.unit}
                    (fun m ↦ precomp I O a.1 a.2 (K (precompMerge I a.1 a.2 cl.down m))))
                  (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X))
                (ULift.up (fun _ : Bin ↦ (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})))))
            (FreeCoprodCompDisc.Iso.invHom O
              (mprecompIso.{uA, uB, uI, uO} I O (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)])
                  (sigma I O (ULift.{max uA uB, uB} (Bin → a.1 ⊕ PUnit.{uB + 1}))
                    (fun cl ↦ delta I O {z : Bin // cl.down z = Sum.inr PUnit.unit}
                      (fun m ↦ precomp I O a.1 a.2 (K (precompMerge I a.1 a.2 cl.down m)))))
                  X))) =
      navInj I O Bout iout Bin K g (a :: L) X :=
  Eq.trans
    (FreeCoprodCompDisc.Hom.comp_assoc O
      (FreeCoprodCompDisc.Hom.comp O
        (FreeCoprodCompDisc.Iso.hom O
          (mprecompIso.{uA, uB, uI, uO} I O (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)])
            (precomp I O a.1 a.2 (K (iout ∘ g))) X))
        (FreeCoprodCompDisc.Hom.comp O
          (FreeCoprodCompDisc.coprodInj O
            (FreeCoprodCompDisc.Hom I
              (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I
                ⟨
                  {z : Bin // (fun _ : Bin ↦ (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) z =
                    Sum.inr PUnit.unit}, fun z ↦ (iout ∘ g) z.1⟩)
              (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X))
            (fun _ ↦ interpObj I O
              (precomp I O a.1 a.2
                (K
                  (precompMerge I a.1 a.2
                    (fun _ : Bin ↦ (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1}))
                    (fun z :
                      {z : Bin // (fun _ : Bin ↦ (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) z =
                        Sum.inr PUnit.unit} ↦ (iout ∘ g) z.1))))
              (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X))
            (navWeight I Bout iout
              {z : Bin // (fun _ : Bin ↦ (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) z = Sum.inr
                PUnit.unit} (fun z ↦ g z.1) X L))
          (deltaInto I O
            {z : Bin // (fun _ : Bin ↦ (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) z = Sum.inr
              PUnit.unit}
            (fun m ↦ precomp I O a.1 a.2
              (K
                (precompMerge I a.1 a.2 (fun _ : Bin ↦ (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1}))
                  m))) (fun z ↦ (iout ∘ g) z.1)
            (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X))))
      (FreeCoprodCompDisc.Iso.invHom O
        (mprecompIso.{uA, uB, uI, uO} I O (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)])
          (delta I O
            {z : Bin // (fun _ : Bin ↦ (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) z = Sum.inr
              PUnit.unit}
            (fun m ↦ precomp I O a.1 a.2
              (K
                (precompMerge I a.1 a.2 (fun _ : Bin ↦ (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1}))
                  m)))) X))
      (FreeCoprodCompDisc.Hom.comp O
        (FreeCoprodCompDisc.Hom.comp O
          (FreeCoprodCompDisc.Iso.hom O
            (mprecompIso.{uA, uB, uI, uO} I O (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)])
              (delta I O
                {z : Bin // (fun _ : Bin ↦ (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) z = Sum.inr
                  PUnit.unit}
                (fun m ↦ precomp I O a.1 a.2
                  (K
                    (precompMerge I a.1 a.2
                      (fun _ : Bin ↦ (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) m)))) X))
          (FreeCoprodCompDisc.coprodInj O (ULift.{max uA uB, uB} (Bin → a.1 ⊕ PUnit.{uB + 1}))
            (fun cl ↦ interpObj I O
              (delta I O {z : Bin // cl.down z = Sum.inr PUnit.unit}
                (fun m ↦ precomp I O a.1 a.2 (K (precompMerge I a.1 a.2 cl.down m))))
              (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X))
            (ULift.up (fun _ : Bin ↦ (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})))))
        (FreeCoprodCompDisc.Iso.invHom O
          (mprecompIso.{uA, uB, uI, uO} I O (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)])
            (sigma I O (ULift.{max uA uB, uB} (Bin → a.1 ⊕ PUnit.{uB + 1}))
              (fun cl ↦ delta I O {z : Bin // cl.down z = Sum.inr PUnit.unit}
                (fun m ↦ precomp I O a.1 a.2 (K (precompMerge I a.1 a.2 cl.down m))))) X))))
    (Eq.trans
      (congrArg
        (FreeCoprodCompDisc.Hom.comp O
          (FreeCoprodCompDisc.Hom.comp O
            (FreeCoprodCompDisc.Iso.hom O
              (mprecompIso.{uA, uB, uI, uO} I O (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)])
                (precomp I O a.1 a.2 (K (iout ∘ g))) X))
            (FreeCoprodCompDisc.Hom.comp O
              (FreeCoprodCompDisc.coprodInj O
                (FreeCoprodCompDisc.Hom I
                  (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I
                    ⟨
                      {z : Bin // (fun _ : Bin ↦ (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) z =
                        Sum.inr PUnit.unit}, fun z ↦ (iout ∘ g) z.1⟩)
                  (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X))
                (fun _ ↦ interpObj I O
                  (precomp I O a.1 a.2
                    (K
                      (precompMerge I a.1 a.2
                        (fun _ : Bin ↦ (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1}))
                        (fun z :
                          {z : Bin // (fun _ : Bin ↦ (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) z
                            = Sum.inr PUnit.unit} ↦ (iout ∘ g) z.1))))
                  (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X))
                (navWeight I Bout iout
                  {z : Bin // (fun _ : Bin ↦ (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) z =
                    Sum.inr PUnit.unit} (fun z ↦ g z.1) X L))
              (deltaInto I O
                {z : Bin // (fun _ : Bin ↦ (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) z = Sum.inr
                  PUnit.unit}
                (fun m ↦ precomp I O a.1 a.2
                  (K
                    (precompMerge I a.1 a.2
                      (fun _ : Bin ↦ (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) m)))
                (fun z ↦ (iout ∘ g) z.1)
                (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X)))))
        (Eq.trans
          (Eq.symm
            (FreeCoprodCompDisc.Hom.comp_assoc O
              (FreeCoprodCompDisc.Iso.invHom O
                (mprecompIso.{uA, uB, uI, uO} I O (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)])
                  (delta I O
                    {z : Bin // (fun _ : Bin ↦ (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) z =
                      Sum.inr PUnit.unit}
                    (fun m ↦ precomp I O a.1 a.2
                      (K
                        (precompMerge I a.1 a.2
                          (fun _ : Bin ↦ (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) m)))) X))
              (FreeCoprodCompDisc.Hom.comp O
                (FreeCoprodCompDisc.Iso.hom O
                  (mprecompIso.{uA, uB, uI, uO} I O (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)])
                    (delta I O
                      {z : Bin // (fun _ : Bin ↦ (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) z =
                        Sum.inr PUnit.unit}
                      (fun m ↦ precomp I O a.1 a.2
                        (K
                          (precompMerge I a.1 a.2
                            (fun _ : Bin ↦ (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) m)))) X))
                (FreeCoprodCompDisc.coprodInj O (ULift.{max uA uB, uB} (Bin → a.1 ⊕ PUnit.{uB + 1}))
                  (fun cl ↦ interpObj I O
                    (delta I O {z : Bin // cl.down z = Sum.inr PUnit.unit}
                      (fun m ↦ precomp I O a.1 a.2 (K (precompMerge I a.1 a.2 cl.down m))))
                    (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X))
                  (ULift.up (fun _ : Bin ↦ (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})))))
              (FreeCoprodCompDisc.Iso.invHom O
                (mprecompIso.{uA, uB, uI, uO} I O (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)])
                  (sigma I O (ULift.{max uA uB, uB} (Bin → a.1 ⊕ PUnit.{uB + 1}))
                    (fun cl ↦ delta I O {z : Bin // cl.down z = Sum.inr PUnit.unit}
                      (fun m ↦ precomp I O a.1 a.2 (K (precompMerge I a.1 a.2 cl.down m))))) X))))
          (congrArg
            (fun t ↦ FreeCoprodCompDisc.Hom.comp O t
              (FreeCoprodCompDisc.Iso.invHom O
                (mprecompIso.{uA, uB, uI, uO} I O (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)])
                  (sigma I O (ULift.{max uA uB, uB} (Bin → a.1 ⊕ PUnit.{uB + 1}))
                    (fun cl ↦ delta I O {z : Bin // cl.down z = Sum.inr PUnit.unit}
                      (fun m ↦ precomp I O a.1 a.2 (K (precompMerge I a.1 a.2 cl.down m))))) X)))
            (Eq.trans
              (Eq.symm
                (FreeCoprodCompDisc.Hom.comp_assoc O
                  (FreeCoprodCompDisc.Iso.invHom O
                    (mprecompIso.{uA, uB, uI, uO} I O (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)])
                      (delta I O
                        {z : Bin // (fun _ : Bin ↦ (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) z =
                          Sum.inr PUnit.unit}
                        (fun m ↦ precomp I O a.1 a.2
                          (K
                            (precompMerge I a.1 a.2
                              (fun _ : Bin ↦ (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) m)))) X))
                  (FreeCoprodCompDisc.Iso.hom O
                    (mprecompIso.{uA, uB, uI, uO} I O (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)])
                      (delta I O
                        {z : Bin // (fun _ : Bin ↦ (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) z =
                          Sum.inr PUnit.unit}
                        (fun m ↦ precomp I O a.1 a.2
                          (K
                            (precompMerge I a.1 a.2
                              (fun _ : Bin ↦ (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) m)))) X))
                  (FreeCoprodCompDisc.coprodInj O
                    (ULift.{max uA uB, uB} (Bin → a.1 ⊕ PUnit.{uB + 1}))
                    (fun cl ↦ interpObj I O
                      (delta I O {z : Bin // cl.down z = Sum.inr PUnit.unit}
                        (fun m ↦ precomp I O a.1 a.2 (K (precompMerge I a.1 a.2 cl.down m))))
                      (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X))
                    (ULift.up (fun _ : Bin ↦ (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1}))))))
              (Eq.trans
                (congrArg
                  (fun t ↦ FreeCoprodCompDisc.Hom.comp O t
                    (FreeCoprodCompDisc.coprodInj O
                      (ULift.{max uA uB, uB} (Bin → a.1 ⊕ PUnit.{uB + 1}))
                      (fun cl ↦ interpObj I O
                        (delta I O {z : Bin // cl.down z = Sum.inr PUnit.unit}
                          (fun m ↦ precomp I O a.1 a.2 (K (precompMerge I a.1 a.2 cl.down m))))
                        (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X))
                      (ULift.up (fun _ : Bin ↦ (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})))))
                  (FreeCoprodCompDisc.Iso.invHom_hom O
                    (mprecompIso.{uA, uB, uI, uO} I O (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)])
                      (delta I O
                        {z : Bin // (fun _ : Bin ↦ (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) z =
                          Sum.inr PUnit.unit}
                        (fun m ↦ precomp I O a.1 a.2
                          (K
                            (precompMerge I a.1 a.2
                              (fun _ : Bin ↦ (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) m)))) X)))
                (FreeCoprodCompDisc.Hom.id_comp O
                  (FreeCoprodCompDisc.coprodInj O
                    (ULift.{max uA uB, uB} (Bin → a.1 ⊕ PUnit.{uB + 1}))
                    (fun cl ↦ interpObj I O
                      (delta I O {z : Bin // cl.down z = Sum.inr PUnit.unit}
                        (fun m ↦ precomp I O a.1 a.2 (K (precompMerge I a.1 a.2 cl.down m))))
                      (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X))
                    (ULift.up (fun _ : Bin ↦ (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1}))))))))))
      (Eq.trans
        (FreeCoprodCompDisc.Hom.comp_assoc O
          (FreeCoprodCompDisc.Iso.hom O
            (mprecompIso.{uA, uB, uI, uO} I O (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)])
              (precomp I O a.1 a.2 (K (iout ∘ g))) X))
          (FreeCoprodCompDisc.Hom.comp O
            (FreeCoprodCompDisc.coprodInj O
              (FreeCoprodCompDisc.Hom I
                (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I
                  ⟨
                    {z : Bin // (fun _ : Bin ↦ (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) z =
                      Sum.inr PUnit.unit}, fun z ↦ (iout ∘ g) z.1⟩)
                (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X))
              (fun _ ↦ interpObj I O
                (precomp I O a.1 a.2
                  (K
                    (precompMerge I a.1 a.2
                      (fun _ : Bin ↦ (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1}))
                      (fun z :
                        {z : Bin // (fun _ : Bin ↦ (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) z =
                          Sum.inr PUnit.unit} ↦ (iout ∘ g) z.1))))
                (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X))
              (navWeight I Bout iout
                {z : Bin // (fun _ : Bin ↦ (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) z = Sum.inr
                  PUnit.unit} (fun z ↦ g z.1) X L))
            (deltaInto I O
              {z : Bin // (fun _ : Bin ↦ (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) z = Sum.inr
                PUnit.unit}
              (fun m ↦ precomp I O a.1 a.2
                (K
                  (precompMerge I a.1 a.2
                    (fun _ : Bin ↦ (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) m)))
              (fun z ↦ (iout ∘ g) z.1)
              (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X)))
          (FreeCoprodCompDisc.Hom.comp O
            (FreeCoprodCompDisc.coprodInj O (ULift.{max uA uB, uB} (Bin → a.1 ⊕ PUnit.{uB + 1}))
              (fun cl ↦ interpObj I O
                (delta I O {z : Bin // cl.down z = Sum.inr PUnit.unit}
                  (fun m ↦ precomp I O a.1 a.2 (K (precompMerge I a.1 a.2 cl.down m))))
                (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X))
              (ULift.up (fun _ : Bin ↦ (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1}))))
            (FreeCoprodCompDisc.Iso.invHom O
              (mprecompIso.{uA, uB, uI, uO} I O (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)])
                (sigma I O (ULift.{max uA uB, uB} (Bin → a.1 ⊕ PUnit.{uB + 1}))
                  (fun cl ↦ delta I O {z : Bin // cl.down z = Sum.inr PUnit.unit}
                    (fun m ↦ precomp I O a.1 a.2 (K (precompMerge I a.1 a.2 cl.down m))))) X))))
        (Eq.trans
          (congrArg
            (FreeCoprodCompDisc.Hom.comp O
              (FreeCoprodCompDisc.Iso.hom O
                (mprecompIso.{uA, uB, uI, uO} I O (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)])
                  (precomp I O a.1 a.2 (K (iout ∘ g))) X)))
            (Eq.symm
              (FreeCoprodCompDisc.Hom.comp_assoc O
                (FreeCoprodCompDisc.Hom.comp O
                  (FreeCoprodCompDisc.coprodInj O
                    (FreeCoprodCompDisc.Hom I
                      (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I
                        ⟨
                          {z : Bin // (fun _ : Bin ↦ (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) z
                            = Sum.inr PUnit.unit}, fun z ↦ (iout ∘ g) z.1⟩)
                      (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X))
                    (fun _ ↦ interpObj I O
                      (precomp I O a.1 a.2
                        (K
                          (precompMerge I a.1 a.2
                            (fun _ : Bin ↦ (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1}))
                            (fun z :
                              {z : Bin //
                                (fun _ : Bin ↦ (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) z =
                                Sum.inr PUnit.unit} ↦ (iout ∘ g) z.1))))
                      (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X))
                    (navWeight I Bout iout
                      {z : Bin // (fun _ : Bin ↦ (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) z =
                        Sum.inr PUnit.unit} (fun z ↦ g z.1) X L))
                  (deltaInto I O
                    {z : Bin // (fun _ : Bin ↦ (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) z =
                      Sum.inr PUnit.unit}
                    (fun m ↦ precomp I O a.1 a.2
                      (K
                        (precompMerge I a.1 a.2
                          (fun _ : Bin ↦ (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) m)))
                    (fun z ↦ (iout ∘ g) z.1)
                    (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X)))
                (FreeCoprodCompDisc.coprodInj O (ULift.{max uA uB, uB} (Bin → a.1 ⊕ PUnit.{uB + 1}))
                  (fun cl ↦ interpObj I O
                    (delta I O {z : Bin // cl.down z = Sum.inr PUnit.unit}
                      (fun m ↦ precomp I O a.1 a.2 (K (precompMerge I a.1 a.2 cl.down m))))
                    (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X))
                  (ULift.up (fun _ : Bin ↦ (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1}))))
                (FreeCoprodCompDisc.Iso.invHom O
                  (mprecompIso.{uA, uB, uI, uO} I O (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)])
                    (sigma I O (ULift.{max uA uB, uB} (Bin → a.1 ⊕ PUnit.{uB + 1}))
                      (fun cl ↦ delta I O {z : Bin // cl.down z = Sum.inr PUnit.unit}
                        (fun m ↦ precomp I O a.1 a.2 (K (precompMerge I a.1 a.2 cl.down m))))) X))))
                        )
          (Eq.trans
            (congrArg
              (fun t ↦ FreeCoprodCompDisc.Hom.comp O
                (FreeCoprodCompDisc.Iso.hom O
                  (mprecompIso.{uA, uB, uI, uO} I O (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)])
                    (precomp I O a.1 a.2 (K (iout ∘ g))) X))
                (FreeCoprodCompDisc.Hom.comp O t
                  (FreeCoprodCompDisc.Iso.invHom O
                    (mprecompIso.{uA, uB, uI, uO} I O (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)])
                      (sigma I O (ULift.{max uA uB, uB} (Bin → a.1 ⊕ PUnit.{uB + 1}))
                        (fun cl ↦ delta I O {z : Bin // cl.down z = Sum.inr PUnit.unit}
                          (fun m ↦ precomp I O a.1 a.2 (K (precompMerge I a.1 a.2 cl.down m))))) X))
                          ))
              (FreeCoprodCompDisc.eq_comp_invHom O
                (interpObj I O
                  (precomp I O a.1 a.2
                    (K
                      (precompMerge I a.1 a.2
                        (fun _ : Bin ↦ (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1}))
                        (fun z :
                          {z : Bin // (fun _ : Bin ↦ (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) z
                            = Sum.inr PUnit.unit} ↦ (iout ∘ g) z.1))))
                  (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X))
                (interpObj I O (precomp I O a.1 a.2 (delta I O Bin K))
                  (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X))
                (interpObj I O (delta I O Bin K)
                  (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I a
                    (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X)))
                (FreeCoprodCompDisc.Hom.comp O
                  (FreeCoprodCompDisc.Hom.comp O
                    (FreeCoprodCompDisc.coprodInj O
                      (FreeCoprodCompDisc.Hom I
                        (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I
                          ⟨
                            {z : Bin // (fun _ : Bin ↦ (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1}))
                              z = Sum.inr PUnit.unit}, fun z ↦ (iout ∘ g) z.1⟩)
                        (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X))
                      (fun _ ↦ interpObj I O
                        (precomp I O a.1 a.2
                          (K
                            (precompMerge I a.1 a.2
                              (fun _ : Bin ↦ (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1}))
                              (fun z :
                                {z : Bin //
                                  (fun _ : Bin ↦ (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) z =
                                  Sum.inr PUnit.unit} ↦ (iout ∘ g) z.1))))
                        (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X))
                      (navWeight I Bout iout
                        {z : Bin // (fun _ : Bin ↦ (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) z =
                          Sum.inr PUnit.unit} (fun z ↦ g z.1) X L))
                    (deltaInto I O
                      {z : Bin // (fun _ : Bin ↦ (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) z =
                        Sum.inr PUnit.unit}
                      (fun m ↦ precomp I O a.1 a.2
                        (K
                          (precompMerge I a.1 a.2
                            (fun _ : Bin ↦ (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) m)))
                      (fun z ↦ (iout ∘ g) z.1)
                      (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X)))
                  (FreeCoprodCompDisc.coprodInj O
                    (ULift.{max uA uB, uB} (Bin → a.1 ⊕ PUnit.{uB + 1}))
                    (fun cl ↦ interpObj I O
                      (delta I O {z : Bin // cl.down z = Sum.inr PUnit.unit}
                        (fun m ↦ precomp I O a.1 a.2 (K (precompMerge I a.1 a.2 cl.down m))))
                      (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X))
                    (ULift.up (fun _ : Bin ↦ (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})))))
                (FreeCoprodCompDisc.Hom.comp O
                  (FreeCoprodCompDisc.Hom.comp O
                    (FreeCoprodCompDisc.Iso.hom O
                      (interpPrecompIso I O (K (iout ∘ g)) a.1 a.2
                        (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X)))
                    (FreeCoprodCompDisc.coprodInj O
                      (FreeCoprodCompDisc.Hom I
                        (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Bin, iout ∘ g⟩)
                        (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I a
                          (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X)))
                      (fun _ ↦ interpObj I O (K (iout ∘ g))
                        (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I a
                          (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X)))
                      (FreeCoprodCompDisc.Hom.comp I (navReindex.{uA, uB, uI} I Bin (iout ∘ g) a.1)
                        (FreeCoprodCompDisc.Hom.comp I
                          (navWeight I Bout iout
                            {z : Bin // (fun _ : Bin ↦ (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1}))
                              z = Sum.inr PUnit.unit} (fun z ↦ g z.1) X L)
                          (FreeCoprodCompDisc.coprodPairInr.{uI, uB, max uA uB} I a
                            (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X)))))
                            )
                  (deltaInto I O Bin K (iout ∘ g)
                    (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I a
                      (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X))))
                (interpPrecompIso I O (delta I O Bin K) a.1 a.2
                  (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X))
                (interpPrecompIso_deltaNavAll_inj I O Bin K a.1 a.2 (iout ∘ g)
                  (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X)
                  (navWeight I Bout iout
                    {z : Bin // (fun _ : Bin ↦ (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) z =
                      Sum.inr PUnit.unit} (fun z ↦ g z.1) X L))))
            (Eq.trans
              (congrArg
                (fun w ↦ FreeCoprodCompDisc.Hom.comp O
                  (FreeCoprodCompDisc.Iso.hom O
                    (mprecompIso.{uA, uB, uI, uO} I O (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)])
                      (precomp I O a.1 a.2 (K (iout ∘ g))) X))
                  (FreeCoprodCompDisc.Hom.comp O
                    (FreeCoprodCompDisc.Hom.comp O
                      (FreeCoprodCompDisc.Hom.comp O
                        (FreeCoprodCompDisc.Hom.comp O
                          (FreeCoprodCompDisc.Iso.hom O
                            (interpPrecompIso I O (K (iout ∘ g)) a.1 a.2
                              (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X)))
                          (FreeCoprodCompDisc.coprodInj O
                            (FreeCoprodCompDisc.Hom I
                              (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Bin, iout ∘ g⟩)
                              (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I a
                                (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X)
                                ))
                            (fun _ ↦ interpObj I O (K (iout ∘ g))
                              (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I a
                                (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X)
                                )) (w)))
                        (deltaInto I O Bin K (iout ∘ g)
                          (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I a
                            (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X))))
                      (FreeCoprodCompDisc.Iso.invHom O
                        (interpPrecompIso I O (delta I O Bin K) a.1 a.2
                          (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X))))
                    (FreeCoprodCompDisc.Iso.invHom O
                      (mprecompIso.{uA, uB, uI, uO} I O (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)])
                        (sigma I O (ULift.{max uA uB, uB} (Bin → a.1 ⊕ PUnit.{uB + 1}))
                          (fun cl ↦ delta I O {z : Bin // cl.down z = Sum.inr PUnit.unit}
                            (fun m ↦ precomp I O a.1 a.2 (K (precompMerge I a.1 a.2 cl.down m))))) X
                            ))))
                (Eq.trans
                  (Eq.symm
                    (FreeCoprodCompDisc.Hom.comp_assoc I
                      (navReindex.{uA, uB, uI} I Bin (iout ∘ g) a.1)
                      (navWeight I Bout iout
                        {z : Bin // (fun _ : Bin ↦ (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) z =
                          Sum.inr PUnit.unit} (fun z ↦ g z.1) X L)
                      (FreeCoprodCompDisc.coprodPairInr.{uI, uB, max uA uB} I a
                        (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X))))
                  (congrArg
                    (fun t ↦ FreeCoprodCompDisc.Hom.comp I t
                      (FreeCoprodCompDisc.coprodPairInr.{uI, uB, max uA uB} I a
                        (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X)))
                    (navWeight_reindex I Bout iout Bin g a.1 X L))))
              (Eq.trans
                (congrArg
                  (FreeCoprodCompDisc.Hom.comp O
                    (FreeCoprodCompDisc.Iso.hom O
                      (mprecompIso.{uA, uB, uI, uO} I O (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)])
                        (precomp I O a.1 a.2 (K (iout ∘ g))) X)))
                  (FreeCoprodCompDisc.Hom.comp_assoc O
                    (FreeCoprodCompDisc.Hom.comp O
                      (FreeCoprodCompDisc.Hom.comp O
                        (FreeCoprodCompDisc.Iso.hom O
                          (interpPrecompIso I O (K (iout ∘ g)) a.1 a.2
                            (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X)))
                        (FreeCoprodCompDisc.coprodInj O
                          (FreeCoprodCompDisc.Hom I
                            (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Bin, iout ∘ g⟩)
                            (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I a
                              (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X)))
                          (fun _ ↦ interpObj I O (K (iout ∘ g))
                            (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I a
                              (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X)))
                          (FreeCoprodCompDisc.Hom.comp I (navWeight I Bout iout Bin g X L)
                            (FreeCoprodCompDisc.coprodPairInr.{uI, uB, max uA uB} I a
                              (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X)))
                              ))
                      (deltaInto I O Bin K (iout ∘ g)
                        (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I a
                          (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X))))
                    (FreeCoprodCompDisc.Iso.invHom O
                      (interpPrecompIso I O (delta I O Bin K) a.1 a.2
                        (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X)))
                    (FreeCoprodCompDisc.Iso.invHom O
                      (mprecompIso.{uA, uB, uI, uO} I O (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)])
                        (sigma I O (ULift.{max uA uB, uB} (Bin → a.1 ⊕ PUnit.{uB + 1}))
                          (fun cl ↦ delta I O {z : Bin // cl.down z = Sum.inr PUnit.unit}
                            (fun m ↦ precomp I O a.1 a.2 (K (precompMerge I a.1 a.2 cl.down m))))) X
                            ))))
                (Eq.trans
                  (congrArg
                    (fun t ↦ FreeCoprodCompDisc.Hom.comp O
                      (FreeCoprodCompDisc.Iso.hom O
                        (mprecompIso.{uA, uB, uI, uO} I O
                          (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)])
                          (precomp I O a.1 a.2 (K (iout ∘ g))) X))
                      (FreeCoprodCompDisc.Hom.comp O t
                        (FreeCoprodCompDisc.Hom.comp O
                          (FreeCoprodCompDisc.Iso.invHom O
                            (interpPrecompIso I O (delta I O Bin K) a.1 a.2
                              (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X)))
                          (FreeCoprodCompDisc.Iso.invHom O
                            (mprecompIso.{uA, uB, uI, uO} I O
                              (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)])
                              (sigma I O (ULift.{max uA uB, uB} (Bin → a.1 ⊕ PUnit.{uB + 1}))
                                (fun cl ↦ delta I O {z : Bin // cl.down z = Sum.inr PUnit.unit}
                                  (fun m ↦ precomp I O a.1 a.2
                                    (K (precompMerge I a.1 a.2 cl.down m))))) X)))))
                    (FreeCoprodCompDisc.Hom.comp_assoc O
                      (FreeCoprodCompDisc.Iso.hom O
                        (interpPrecompIso I O (K (iout ∘ g)) a.1 a.2
                          (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X)))
                      (FreeCoprodCompDisc.coprodInj O
                        (FreeCoprodCompDisc.Hom I
                          (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Bin, iout ∘ g⟩)
                          (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I a
                            (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X)))
                        (fun _ ↦ interpObj I O (K (iout ∘ g))
                          (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I a
                            (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X)))
                        (FreeCoprodCompDisc.Hom.comp I (navWeight I Bout iout Bin g X L)
                          (FreeCoprodCompDisc.coprodPairInr.{uI, uB, max uA uB} I a
                            (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X))))
                      (deltaInto I O Bin K (iout ∘ g)
                        (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I a
                          (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X)))))
                  (Eq.trans
                    (Eq.symm
                      (FreeCoprodCompDisc.Hom.comp_assoc O
                        (FreeCoprodCompDisc.Iso.hom O
                          (mprecompIso.{uA, uB, uI, uO} I O
                            (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)])
                            (precomp I O a.1 a.2 (K (iout ∘ g))) X))
                        (FreeCoprodCompDisc.Hom.comp O
                          (FreeCoprodCompDisc.Iso.hom O
                            (interpPrecompIso I O (K (iout ∘ g)) a.1 a.2
                              (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X)))
                          (FreeCoprodCompDisc.Hom.comp O
                            (FreeCoprodCompDisc.coprodInj O
                              (FreeCoprodCompDisc.Hom I
                                (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Bin, iout ∘ g⟩)
                                (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I a
                                  (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)])
                                    X)))
                              (fun _ ↦ interpObj I O (K (iout ∘ g))
                                (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I a
                                  (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)])
                                    X)))
                              (FreeCoprodCompDisc.Hom.comp I (navWeight I Bout iout Bin g X L)
                                (FreeCoprodCompDisc.coprodPairInr.{uI, uB, max uA uB} I a
                                  (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)])
                                    X))))
                            (deltaInto I O Bin K (iout ∘ g)
                              (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I a
                                (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X)
                                ))))
                        (FreeCoprodCompDisc.Hom.comp O
                          (FreeCoprodCompDisc.Iso.invHom O
                            (interpPrecompIso I O (delta I O Bin K) a.1 a.2
                              (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X)))
                          (FreeCoprodCompDisc.Iso.invHom O
                            (mprecompIso.{uA, uB, uI, uO} I O
                              (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)])
                              (sigma I O (ULift.{max uA uB, uB} (Bin → a.1 ⊕ PUnit.{uB + 1}))
                                (fun cl ↦ delta I O {z : Bin // cl.down z = Sum.inr PUnit.unit}
                                  (fun m ↦ precomp I O a.1 a.2
                                    (K (precompMerge I a.1 a.2 cl.down m))))) X)))))
                    (congrArg
                      (fun t ↦ FreeCoprodCompDisc.Hom.comp O t
                        (FreeCoprodCompDisc.Hom.comp O
                          (FreeCoprodCompDisc.Iso.invHom O
                            (interpPrecompIso I O (delta I O Bin K) a.1 a.2
                              (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X)))
                          (FreeCoprodCompDisc.Iso.invHom O
                            (mprecompIso.{uA, uB, uI, uO} I O
                              (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)])
                              (sigma I O (ULift.{max uA uB, uB} (Bin → a.1 ⊕ PUnit.{uB + 1}))
                                (fun cl ↦ delta I O {z : Bin // cl.down z = Sum.inr PUnit.unit}
                                  (fun m ↦ precomp I O a.1 a.2
                                    (K (precompMerge I a.1 a.2 cl.down m))))) X))))
                      (Eq.symm
                        (FreeCoprodCompDisc.Hom.comp_assoc O
                          (FreeCoprodCompDisc.Iso.hom O
                            (mprecompIso.{uA, uB, uI, uO} I O
                              (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)])
                              (precomp I O a.1 a.2 (K (iout ∘ g))) X))
                          (FreeCoprodCompDisc.Iso.hom O
                            (interpPrecompIso I O (K (iout ∘ g)) a.1 a.2
                              (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X)))
                          (FreeCoprodCompDisc.Hom.comp O
                            (FreeCoprodCompDisc.coprodInj O
                              (FreeCoprodCompDisc.Hom I
                                (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Bin, iout ∘ g⟩)
                                (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I a
                                  (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)])
                                    X)))
                              (fun _ ↦ interpObj I O (K (iout ∘ g))
                                (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I a
                                  (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)])
                                    X)))
                              (FreeCoprodCompDisc.Hom.comp I (navWeight I Bout iout Bin g X L)
                                (FreeCoprodCompDisc.coprodPairInr.{uI, uB, max uA uB} I a
                                  (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)])
                                    X))))
                            (deltaInto I O Bin K (iout ∘ g)
                              (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I a
                                (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X)
                                ))))))))))))))

/-- The `IR.deltaNav` characterization: `IR.interpHom` sends the
tower navigation to the composite with the tower-conjugated
navigation inclusion `IR.navInj`, by `List.rec` following
`IR.deltaNav`'s own recursion. -/
theorem interpHom_deltaNav (D : IR.{max uA uB, uB, uI, uO} I O)
    (Bout : Type uB) (iout : Bout → I) (Bin : Type uB)
    (K : (Bin → I) → IR.{max uA uB, uB, uI, uO} I O) (g : Bin → Bout)
    (L : List (SupObj.{uB, uI} I))
    (f : Hom.{uA, uB, uI, uO} I O D
      (mprecomp I O (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) (K (iout ∘ g))))
    (X : FreeCoprodCompDisc.{max uA uB, uI} I) :
    (interpHom I O D
        (mprecomp I O (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)])
          (delta I O Bin K))
        (deltaNav I O D Bout iout Bin K g L f)).1 X =
      FreeCoprodCompDisc.Hom.comp O
        ((interpHom I O D
          (mprecomp I O (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)])
            (K (iout ∘ g))) f).1 X)
        (navInj I O Bout iout Bin K g L X) :=
  L.rec (motive := fun L' : List (SupObj.{uB, uI} I) ↦
      ∀ (Bin' : Type uB) (K' : (Bin' → I) → IR.{max uA uB, uB, uI, uO} I O)
        (g' : Bin' → Bout)
        (f' : Hom.{uA, uB, uI, uO} I O D
          (mprecomp I O (L' ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)])
            (K' (iout ∘ g'))))
        (X' : FreeCoprodCompDisc.{max uA uB, uI} I),
      (interpHom I O D
          (mprecomp I O (L' ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)])
            (delta I O Bin' K'))
          (deltaNav I O D Bout iout Bin' K' g' L' f')).1 X' =
        FreeCoprodCompDisc.Hom.comp O
          ((interpHom I O D
            (mprecomp I O (L' ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)])
              (K' (iout ∘ g'))) f').1 X')
          (navInj I O Bout iout Bin' K' g' L' X'))
    (fun Bin' K' g' f' X' ↦
      (interpHom_deltaNavBase I O D Bout iout Bin' K' g' f' X').trans
        (congrArg
          (FreeCoprodCompDisc.Hom.comp O
            ((interpHom I O D (precomp I O Bout iout (K' (iout ∘ g'))) f').1 X'))
          (navInj_nil I O Bout iout Bin' K' g' X')))
    (fun a _L ih Bin' K' g' f' X' ↦
      Eq.trans (interpHom_msigmaPush I O D (ULift.{max uA uB, uB} (Bin' → a.1 ⊕ PUnit.{uB + 1}))
        (fun cl ↦ delta I O {z : Bin' // cl.down z = Sum.inr PUnit.unit} (fun m ↦ precomp I O
        a.1 a.2 (K' (precompMerge I a.1 a.2 cl.down m)))) (ULift.up (fun _ ↦ Sum.inr PUnit.unit))
        (_L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) (deltaNav I O D Bout iout {z : Bin' // (fun _
        : Bin' ↦ (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) z = Sum.inr PUnit.unit} (fun m ↦
        precomp I O a.1 a.2 (K' (precompMerge I a.1 a.2 (fun _ : Bin' ↦ (Sum.inr PUnit.unit : a.1
        ⊕ PUnit.{uB + 1})) m))) (fun z ↦ g' z.1) _L f') X') (Eq.trans (congrArg (fun t ↦
        FreeCoprodCompDisc.Hom.comp O t (FreeCoprodCompDisc.Hom.comp O
        (FreeCoprodCompDisc.Hom.comp O (FreeCoprodCompDisc.Iso.hom O (mprecompIso.{uA, uB, uI, uO}
        I O (_L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) (delta I O {z : Bin' // (fun _ : Bin' ↦
        (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) z = Sum.inr PUnit.unit} (fun m ↦ precomp I O
        a.1 a.2 (K' (precompMerge I a.1 a.2 (fun _ : Bin' ↦ (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB
        + 1})) m)))) X')) (FreeCoprodCompDisc.coprodInj O (ULift.{max uA uB, uB} (Bin' → a.1 ⊕
        PUnit.{uB + 1})) (fun cl ↦ interpObj I O (delta I O {z : Bin' // cl.down z = Sum.inr
        PUnit.unit} (fun m ↦ precomp I O a.1 a.2 (K' (precompMerge I a.1 a.2 cl.down m))))
        (mplus.{uA, uB, uI} I (_L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X')) (ULift.up (fun _
        ↦ Sum.inr PUnit.unit)))) (FreeCoprodCompDisc.Iso.invHom O (mprecompIso.{uA, uB, uI, uO} I
        O (_L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) (sigma I O (ULift.{max uA uB, uB} (Bin' →
        a.1 ⊕ PUnit.{uB + 1})) (fun cl ↦ delta I O {z : Bin' // cl.down z = Sum.inr PUnit.unit}
        (fun m ↦ precomp I O a.1 a.2 (K' (precompMerge I a.1 a.2 cl.down m))))) X')))) (ih {z :
        Bin' // (fun _ : Bin' ↦ (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) z = Sum.inr
        PUnit.unit} (fun m ↦ precomp I O a.1 a.2 (K' (precompMerge I a.1 a.2 (fun _ : Bin' ↦
        (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) m))) (fun z ↦ g' z.1) f' X')) (Eq.trans
        (FreeCoprodCompDisc.Hom.comp_assoc O ((interpHom I O D (mprecomp I O (_L ++ [(⟨Bout, iout⟩
        : SupObj.{uB, uI} I)]) (precomp I O a.1 a.2 (K' (iout ∘ g')))) f').1 X') (navInj I O Bout
        iout {z : Bin' // (fun _ : Bin' ↦ (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) z =
        Sum.inr PUnit.unit} (fun m ↦ precomp I O a.1 a.2 (K' (precompMerge I a.1 a.2 (fun _ :
        Bin' ↦ (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) m))) (fun z ↦ g' z.1) _L X')
        (FreeCoprodCompDisc.Hom.comp O (FreeCoprodCompDisc.Hom.comp O (FreeCoprodCompDisc.Iso.hom
        O (mprecompIso.{uA, uB, uI, uO} I O (_L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) (delta I
        O {z : Bin' // (fun _ : Bin' ↦ (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) z = Sum.inr
        PUnit.unit} (fun m ↦ precomp I O a.1 a.2 (K' (precompMerge I a.1 a.2 (fun _ : Bin' ↦
        (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) m)))) X')) (FreeCoprodCompDisc.coprodInj O
        (ULift.{max uA uB, uB} (Bin' → a.1 ⊕ PUnit.{uB + 1})) (fun cl ↦ interpObj I O (delta I O
        {z : Bin' // cl.down z = Sum.inr PUnit.unit} (fun m ↦ precomp I O a.1 a.2 (K'
        (precompMerge I a.1 a.2 cl.down m)))) (mplus.{uA, uB, uI} I (_L ++ [(⟨Bout, iout⟩ :
        SupObj.{uB, uI} I)]) X')) (ULift.up (fun _ ↦ Sum.inr PUnit.unit))))
        (FreeCoprodCompDisc.Iso.invHom O (mprecompIso.{uA, uB, uI, uO} I O (_L ++ [(⟨Bout, iout⟩ :
        SupObj.{uB, uI} I)]) (sigma I O (ULift.{max uA uB, uB} (Bin' → a.1 ⊕ PUnit.{uB + 1})) (fun
        cl ↦ delta I O {z : Bin' // cl.down z = Sum.inr PUnit.unit} (fun m ↦ precomp I O a.1 a.2
        (K' (precompMerge I a.1 a.2 cl.down m))))) X')))) (congrArg (FreeCoprodCompDisc.Hom.comp O
        ((interpHom I O D (mprecomp I O (_L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) (precomp I O
        a.1 a.2 (K' (iout ∘ g')))) f').1 X')) (navInj_cons I O Bout iout Bin' K' g' a _L X')))))
    Bin K g f X

/-! ### The identity-image induction -/

/-- The statement of the identity-image equation at one code: the
component of `IR.interpHom` at the pre-unit is the semantic pre-unit
component. -/
def InterpHomPreUnitMotive (γ : IR.{max uA uB, uB, uI, uO} I O) : Prop :=
  ∀ (L : List (SupObj.{uB, uI} I)) (X : FreeCoprodCompDisc.{max uA uB, uI} I),
    (interpHom I O γ (mprecomp I O L γ) (preUnitStack I O γ L)).1 X =
      preUnitComponent I O γ L X

/-- Elimination of a codomain-code transport inside `IR.interpHom`, by
elimination of the generalized equality: the transport passes to an
object-equality transport on the component. -/
theorem interpHom_cast_cod (D : IR.{max uA uB, uB, uI, uO} I O)
    (γ₀ : IR.{max uA uB, uB, uI, uO} I O)
    (X : FreeCoprodCompDisc.{max uA uB, uI} I) :
    ∀ (γ'' : IR.{max uA uB, uB, uI, uO} I O) (h : γ₀ = γ'')
      (f : Hom.{uA, uB, uI, uO} I O D γ₀),
      (interpHom I O D γ'' (cast (congrArg (Hom I O D) h) f)).1 X =
        FreeCoprodCompDisc.Hom.comp O ((interpHom I O D γ₀ f).1 X)
          (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
            (congrArg (fun cc ↦ interpObj I O cc X) h))) :=
  fun _ h ↦
    Eq.rec (motive := fun γ'' h' ↦
        ∀ f : Hom.{uA, uB, uI, uO} I O D γ₀,
          (interpHom I O D γ'' (cast (congrArg (Hom I O D) h') f)).1 X =
            FreeCoprodCompDisc.Hom.comp O ((interpHom I O D γ₀ f).1 X)
              (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
                (congrArg (fun cc ↦ interpObj I O cc X) h'))))
      (fun f ↦ (FreeCoprodCompDisc.Hom.comp_id O
        ((interpHom I O D γ₀ f).1 X)).symm)
      h

/-- An object-equality transport of the interpreted argument passes
through `IR.interpMor`, by elimination of the generalized equality. -/
theorem interpMor_isoOfEq_dom (γ' : IR.{max uA uB, uB, uI, uO} I O)
    (W Y : FreeCoprodCompDisc.{max uA uB, uI} I) :
    ∀ (V : FreeCoprodCompDisc.{max uA uB, uI} I) (q : W = V)
      (h : FreeCoprodCompDisc.Hom I V Y),
      FreeCoprodCompDisc.Hom.comp O
          (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
            (congrArg (interpObj I O γ') q)))
          (interpMor I O γ' V Y h) =
        interpMor I O γ' W Y
          (FreeCoprodCompDisc.Hom.comp I
            (FreeCoprodCompDisc.Iso.hom I (FreeCoprodCompDisc.isoOfEq I q)) h) :=
  fun _ q ↦
    Eq.rec (motive := fun V' q' ↦
        ∀ h : FreeCoprodCompDisc.Hom I V' Y,
          FreeCoprodCompDisc.Hom.comp O
              (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
                (congrArg (interpObj I O γ') q')))
              (interpMor I O γ' V' Y h) =
            interpMor I O γ' W Y
              (FreeCoprodCompDisc.Hom.comp I
                (FreeCoprodCompDisc.Iso.hom I
                  (FreeCoprodCompDisc.isoOfEq I q')) h))
      (fun _ ↦ rfl) q

/-- Naturality of the iterated right injection `IR.mplusInj` in the
base object. -/
theorem mplusInj_natural (L : List (SupObj.{uB, uI} I))
    (Z W : FreeCoprodCompDisc.{max uA uB, uI} I)
    (h : FreeCoprodCompDisc.Hom I Z W) :
    FreeCoprodCompDisc.Hom.comp I (mplusInj.{uA, uB, uI} I L Z)
        (mplusMorMap.{uA, uB, uI} I L Z W h) =
      FreeCoprodCompDisc.Hom.comp I h (mplusInj.{uA, uB, uI} I L W) :=
  L.rec (motive := fun L' ↦
      FreeCoprodCompDisc.Hom.comp I (mplusInj.{uA, uB, uI} I L' Z)
          (mplusMorMap.{uA, uB, uI} I L' Z W h) =
        FreeCoprodCompDisc.Hom.comp I h (mplusInj.{uA, uB, uI} I L' W))
    ((FreeCoprodCompDisc.Hom.id_comp I h).trans
      (FreeCoprodCompDisc.Hom.comp_id I h).symm)
    (fun a _L ih ↦
      (FreeCoprodCompDisc.Hom.comp_assoc I (mplusInj.{uA, uB, uI} I _L Z)
          (FreeCoprodCompDisc.coprodPairInr.{uI, uB, max uA uB} I a (mplus.{uA, uB, uI} I _L Z))
          (FreeCoprodCompDisc.coprodPairMor I
            (FreeCoprodCompDisc.Hom.id I a)
            (mplusMorMap.{uA, uB, uI} I _L Z W h))).trans
        ((congrArg
            (FreeCoprodCompDisc.Hom.comp I (mplusInj.{uA, uB, uI} I _L Z) :
              _ → _)
            (FreeCoprodCompDisc.coprodPairInr_mor I a (mplus.{uA, uB, uI} I _L Z)
              (mplus.{uA, uB, uI} I _L W)
              (mplusMorMap.{uA, uB, uI} I _L Z W h))).trans
          ((FreeCoprodCompDisc.Hom.comp_assoc I (mplusInj.{uA, uB, uI} I _L Z)
              (mplusMorMap.{uA, uB, uI} I _L Z W h)
              (FreeCoprodCompDisc.coprodPairInr.{uI, uB, max uA uB} I a
                (mplus.{uA, uB, uI} I _L W))).symm.trans
            ((congrArg
                (fun t ↦ FreeCoprodCompDisc.Hom.comp I t
                  (FreeCoprodCompDisc.coprodPairInr.{uI, uB, max uA uB} I a
                    (mplus.{uA, uB, uI} I _L W)))
                ih).trans
              (FreeCoprodCompDisc.Hom.comp_assoc I h
                (mplusInj.{uA, uB, uI} I _L W)
                (FreeCoprodCompDisc.coprodPairInr.{uI, uB, max uA uB} I a
                  (mplus.{uA, uB, uI} I _L W)))))))

/-- The weighted summand inclusion commutes with the interpreted
morphism: reindexing the weight moves the inclusion to the codomain
object. -/
theorem deltaIntoWeight_comp (B : Type uB)
    (c : (B → I) → IR.{max uA uB, uB, uI, uO} I O) (i : B → I)
    (Z W : FreeCoprodCompDisc.{max uA uB, uI} I)
    (h : FreeCoprodCompDisc.Hom I Z W)
    (u : FreeCoprodCompDisc.Hom I
      (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) Z) :
    FreeCoprodCompDisc.Hom.comp O
        (FreeCoprodCompDisc.Hom.comp O
          (FreeCoprodCompDisc.coprodInj O
            (FreeCoprodCompDisc.Hom I
              (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) Z)
            (fun _ ↦ interpObj I O (c i) Z) u)
          (deltaInto I O B c i Z))
        (interpMor I O (delta I O B c) Z W h) =
      FreeCoprodCompDisc.Hom.comp O
        (FreeCoprodCompDisc.Hom.comp O (interpMor I O (c i) Z W h)
          (FreeCoprodCompDisc.coprodInj O
            (FreeCoprodCompDisc.Hom I
              (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) W)
            (fun _ ↦ interpObj I O (c i) W)
            (FreeCoprodCompDisc.Hom.comp I u h)))
        (deltaInto I O B c i W) :=
  (FreeCoprodCompDisc.Hom.comp_assoc O
      (FreeCoprodCompDisc.coprodInj O
        (FreeCoprodCompDisc.Hom I
          (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) Z)
        (fun _ ↦ interpObj I O (c i) Z) u)
      (deltaInto I O B c i Z) (interpMor I O (delta I O B c) Z W h)).trans
    ((congrArg
        (FreeCoprodCompDisc.Hom.comp O
          (FreeCoprodCompDisc.coprodInj O
            (FreeCoprodCompDisc.Hom I
              (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) Z)
            (fun _ ↦ interpObj I O (c i) Z) u))
        (deltaInto_natural I O B c i Z W h).symm).trans
      ((FreeCoprodCompDisc.Hom.comp_assoc O
          (FreeCoprodCompDisc.coprodInj O
            (FreeCoprodCompDisc.Hom I
              (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) Z)
            (fun _ ↦ interpObj I O (c i) Z) u)
          (FreeCoprodCompDisc.copowerHomMapMor
            (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩)
            (interpMor I O (c i)) Z W h)
          (deltaInto I O B c i W)).symm.trans
        (congrArg
          (fun t ↦ FreeCoprodCompDisc.Hom.comp O t (deltaInto I O B c i W))
          (FreeCoprodCompDisc.coprodInj_mor O
            (FreeCoprodCompDisc.Hom I
              (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) Z)
            (FreeCoprodCompDisc.Hom I
              (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) W)
            (fun e' ↦ FreeCoprodCompDisc.Hom.comp I e' h)
            (fun _ ↦ interpObj I O (c i) Z)
            (fun _ ↦ interpObj I O (c i) W)
            (fun _ ↦ interpMor I O (c i) Z W h) u))))

/-- The forward component of `IR.mprecompIso` at a right-appended
superscript, with the `IR.mplus_snoc` transport moved to the other
side. -/
theorem mprecompIso_snoc_hom_comp (L : List (SupObj.{uB, uI} I))
    (b : SupObj.{uB, uI} I) (γ : IR.{max uA uB, uB, uI, uO} I O)
    (X : FreeCoprodCompDisc.{max uA uB, uI} I) :
    FreeCoprodCompDisc.Hom.comp O
        (FreeCoprodCompDisc.Hom.comp O
          (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
            (congrArg (fun cc ↦ interpObj I O cc X) (mprecomp_snoc I O L b γ))))
          (FreeCoprodCompDisc.Iso.hom O
            (interpPrecompIso I O (mprecomp I O L γ) b.1 b.2 X)))
        (FreeCoprodCompDisc.Iso.hom O (mprecompIso.{uA, uB, uI, uO} I O L γ
          (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b X))) =
      FreeCoprodCompDisc.Hom.comp O
        (FreeCoprodCompDisc.Iso.hom O
          (mprecompIso.{uA, uB, uI, uO} I O (L ++ [b]) γ X))
        (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
          (congrArg (interpObj I O γ) (mplus_snoc.{uA, uB, uI} I L b X)))) :=
  ((congrArg
      (fun t ↦ FreeCoprodCompDisc.Hom.comp O t
        (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
          (congrArg (interpObj I O γ) (mplus_snoc.{uA, uB, uI} I L b X)))))
      (mprecompIso_snoc_hom I O L b γ X)).trans
    ((FreeCoprodCompDisc.Hom.comp_assoc O
        (FreeCoprodCompDisc.Hom.comp O
          (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
            (congrArg (fun cc ↦ interpObj I O cc X) (mprecomp_snoc I O L b γ))))
          (FreeCoprodCompDisc.Iso.hom O
            (interpPrecompIso I O (mprecomp I O L γ) b.1 b.2 X)))
        (FreeCoprodCompDisc.Hom.comp O
          (FreeCoprodCompDisc.Iso.hom O (mprecompIso.{uA, uB, uI, uO} I O L γ
            (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b X)))
          (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
            (congrArg (interpObj I O γ)
              (mplus_snoc.{uA, uB, uI} I L b X).symm))))
        (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
          (congrArg (interpObj I O γ) (mplus_snoc.{uA, uB, uI} I L b X))))).trans
      (congrArg
        (FreeCoprodCompDisc.Hom.comp O
          (FreeCoprodCompDisc.Hom.comp O
            (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
              (congrArg (fun cc ↦ interpObj I O cc X)
                (mprecomp_snoc I O L b γ))))
            (FreeCoprodCompDisc.Iso.hom O
              (interpPrecompIso I O (mprecomp I O L γ) b.1 b.2 X))))
        ((FreeCoprodCompDisc.Hom.comp_assoc O
            (FreeCoprodCompDisc.Iso.hom O
              (mprecompIso.{uA, uB, uI, uO} I O L γ
                (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b X)))
            (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
              (congrArg (interpObj I O γ)
                (mplus_snoc.{uA, uB, uI} I L b X).symm)))
            (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
              (congrArg (interpObj I O γ)
                (mplus_snoc.{uA, uB, uI} I L b X))))).trans
          ((congrArg
              (FreeCoprodCompDisc.Hom.comp O
                (FreeCoprodCompDisc.Iso.hom O
                  (mprecompIso.{uA, uB, uI, uO} I O L γ
                    (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b X))))
              (FreeCoprodCompDisc.isoOfEq_symm_hom_comp.{max uA uB, uO} O
                (interpObj I O γ (mplus.{uA, uB, uI} I (L ++ [b]) X))
                (interpObj I O γ (mplus.{uA, uB, uI} I L
                  (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b X)))
                (congrArg (interpObj I O γ)
                  (mplus_snoc.{uA, uB, uI} I L b X)))).trans
            (FreeCoprodCompDisc.Hom.comp_id O
              (FreeCoprodCompDisc.Iso.hom O
                (mprecompIso.{uA, uB, uI, uO} I O L γ
                  (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b X))))))))).symm

/-- The tower morphism induced by a weight at a right-appended
superscript: the `IR.mplus_snoc` transport followed by the tower action
on the bridge cotuple at the base. -/
def navBridgeMor (B : Type uB) (i : B → I) (L : List (SupObj.{uB, uI} I))
    (X : FreeCoprodCompDisc.{max uA uB, uI} I)
    (e : FreeCoprodCompDisc.Hom I
      (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) X) :
    FreeCoprodCompDisc.Hom I
      (mplus.{uA, uB, uI} I (L ++ [(⟨B, i⟩ : SupObj.{uB, uI} I)]) X)
      (mplus.{uA, uB, uI} I L X) :=
  FreeCoprodCompDisc.Hom.comp I
    (FreeCoprodCompDisc.Iso.hom I (FreeCoprodCompDisc.isoOfEq I
      (mplus_snoc.{uA, uB, uI} I L (⟨B, i⟩ : SupObj.{uB, uI} I) X)))
    (mplusMorMap.{uA, uB, uI} I L
      (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨B, i⟩ X) X
      (FreeCoprodCompDisc.Hom.comp I (plusLiftBridgeInvHom I B i X)
        (FreeCoprodCompDisc.coprodPairDesc I e (FreeCoprodCompDisc.Hom.id I X))))

/-- The tower injection at a right-appended superscript, followed by the
weight's tower morphism, is the tower injection at the base stack. -/
theorem mplusInj_navBridge (B : Type uB) (i : B → I)
    (L : List (SupObj.{uB, uI} I)) (X : FreeCoprodCompDisc.{max uA uB, uI} I)
    (e : FreeCoprodCompDisc.Hom I
      (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) X) :
    FreeCoprodCompDisc.Hom.comp I
        (mplusInj.{uA, uB, uI} I (L ++ [(⟨B, i⟩ : SupObj.{uB, uI} I)]) X)
        (navBridgeMor.{uA, uB, uI} I B i L X e) =
      mplusInj.{uA, uB, uI} I L X :=
  (FreeCoprodCompDisc.Hom.comp_assoc I
      (mplusInj.{uA, uB, uI} I (L ++ [(⟨B, i⟩ : SupObj.{uB, uI} I)]) X)
      (FreeCoprodCompDisc.Iso.hom I (FreeCoprodCompDisc.isoOfEq I
        (mplus_snoc.{uA, uB, uI} I L (⟨B, i⟩ : SupObj.{uB, uI} I) X)))
      (mplusMorMap.{uA, uB, uI} I L
        (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨B, i⟩ X) X
        (FreeCoprodCompDisc.Hom.comp I (plusLiftBridgeInvHom I B i X)
          (FreeCoprodCompDisc.coprodPairDesc I e
            (FreeCoprodCompDisc.Hom.id I X))))).symm.trans
    ((congrArg
        (fun t ↦ FreeCoprodCompDisc.Hom.comp I t
          (mplusMorMap.{uA, uB, uI} I L
            (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨B, i⟩ X) X
            (FreeCoprodCompDisc.Hom.comp I (plusLiftBridgeInvHom I B i X)
              (FreeCoprodCompDisc.coprodPairDesc I e
                (FreeCoprodCompDisc.Hom.id I X)))))
        ((FreeCoprodCompDisc.comp_isoOfEq_hom.{max uA uB, uI} I X
            (mplus.{uA, uB, uI} I (L ++ [(⟨B, i⟩ : SupObj.{uB, uI} I)]) X)
            (mplus.{uA, uB, uI} I L
              (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨B, i⟩ X))
            (mplus_snoc.{uA, uB, uI} I L (⟨B, i⟩ : SupObj.{uB, uI} I) X)
            (mplusInj.{uA, uB, uI} I
              (L ++ [(⟨B, i⟩ : SupObj.{uB, uI} I)]) X)).trans
          (mplusInj_snoc.{uA, uB, uI} I L
            (⟨B, i⟩ : SupObj.{uB, uI} I) X))).trans
      ((FreeCoprodCompDisc.Hom.comp_assoc I
          (FreeCoprodCompDisc.coprodPairInr.{uI, uB, max uA uB} I (⟨B, i⟩ : SupObj.{uB, uI} I) X)
          (mplusInj.{uA, uB, uI} I L
            (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨B, i⟩ X))
          (mplusMorMap.{uA, uB, uI} I L
            (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨B, i⟩ X) X
            (FreeCoprodCompDisc.Hom.comp I (plusLiftBridgeInvHom I B i X)
              (FreeCoprodCompDisc.coprodPairDesc I e
                (FreeCoprodCompDisc.Hom.id I X))))).trans
        ((congrArg
            (FreeCoprodCompDisc.Hom.comp I
              (FreeCoprodCompDisc.coprodPairInr.{uI, uB, max uA uB} I
                (⟨B, i⟩ : SupObj.{uB, uI} I) X))
            (mplusInj_natural.{uA, uB, uI} I L
              (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨B, i⟩ X) X
              (FreeCoprodCompDisc.Hom.comp I (plusLiftBridgeInvHom I B i X)
                (FreeCoprodCompDisc.coprodPairDesc I e
                  (FreeCoprodCompDisc.Hom.id I X))))).trans
          ((FreeCoprodCompDisc.Hom.comp_assoc I
              (FreeCoprodCompDisc.coprodPairInr.{uI, uB, max uA uB} I
                (⟨B, i⟩ : SupObj.{uB, uI} I) X)
              (FreeCoprodCompDisc.Hom.comp I (plusLiftBridgeInvHom I B i X)
                (FreeCoprodCompDisc.coprodPairDesc I e
                  (FreeCoprodCompDisc.Hom.id I X)))
              (mplusInj.{uA, uB, uI} I L X)).symm.trans
            ((congrArg
                (fun t ↦ FreeCoprodCompDisc.Hom.comp I t
                  (mplusInj.{uA, uB, uI} I L X))
                (Subtype.ext rfl :
                  FreeCoprodCompDisc.Hom.comp I
                      (FreeCoprodCompDisc.coprodPairInr.{uI, uB, max uA uB} I
                        (⟨B, i⟩ : SupObj.{uB, uI} I) X)
                      (FreeCoprodCompDisc.Hom.comp I
                        (plusLiftBridgeInvHom I B i X)
                        (FreeCoprodCompDisc.coprodPairDesc I e
                          (FreeCoprodCompDisc.Hom.id I X))) =
                    FreeCoprodCompDisc.Hom.id I X)).trans
              (FreeCoprodCompDisc.Hom.id_comp I
                (mplusInj.{uA, uB, uI} I L X)))))))

/-- The tower navigation weight, followed by the weight's tower
morphism, is the weight followed by the tower injection at the base
stack. -/
theorem navWeight_navBridge (B : Type uB) (i : B → I)
    (L : List (SupObj.{uB, uI} I)) (X : FreeCoprodCompDisc.{max uA uB, uI} I)
    (e : FreeCoprodCompDisc.Hom I
      (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) X) :
    FreeCoprodCompDisc.Hom.comp I
        (navWeight I B i B _root_.id X L)
        (navBridgeMor.{uA, uB, uI} I B i L X e) =
      FreeCoprodCompDisc.Hom.comp I e (mplusInj.{uA, uB, uI} I L X) :=
  (FreeCoprodCompDisc.Hom.comp_assoc I
      (navWeight I B i B _root_.id X L)
      (FreeCoprodCompDisc.Iso.hom I (FreeCoprodCompDisc.isoOfEq I
        (mplus_snoc.{uA, uB, uI} I L (⟨B, i⟩ : SupObj.{uB, uI} I) X)))
      (mplusMorMap.{uA, uB, uI} I L
        (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨B, i⟩ X) X
        (FreeCoprodCompDisc.Hom.comp I (plusLiftBridgeInvHom I B i X)
          (FreeCoprodCompDisc.coprodPairDesc I e
            (FreeCoprodCompDisc.Hom.id I X))))).symm.trans
    ((congrArg
        (fun t ↦ FreeCoprodCompDisc.Hom.comp I t
          (mplusMorMap.{uA, uB, uI} I L
            (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨B, i⟩ X) X
            (FreeCoprodCompDisc.Hom.comp I (plusLiftBridgeInvHom I B i X)
              (FreeCoprodCompDisc.coprodPairDesc I e
                (FreeCoprodCompDisc.Hom.id I X)))))
        ((FreeCoprodCompDisc.comp_isoOfEq_hom.{max uA uB, uI} I
            (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩)
            (mplus.{uA, uB, uI} I (L ++ [(⟨B, i⟩ : SupObj.{uB, uI} I)]) X)
            (mplus.{uA, uB, uI} I L
              (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨B, i⟩ X))
            (mplus_snoc.{uA, uB, uI} I L (⟨B, i⟩ : SupObj.{uB, uI} I) X)
            (navWeight I B i B _root_.id X L)).trans
          (navWeight_snoc I B i B _root_.id X L))).trans
      ((FreeCoprodCompDisc.Hom.comp_assoc I
          (⟨fun z ↦ Sum.inl (_root_.id z.down), rfl⟩ :
            FreeCoprodCompDisc.Hom I
              (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩)
              (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨B, i⟩ X))
          (mplusInj.{uA, uB, uI} I L
            (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨B, i⟩ X))
          (mplusMorMap.{uA, uB, uI} I L
            (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨B, i⟩ X) X
            (FreeCoprodCompDisc.Hom.comp I (plusLiftBridgeInvHom I B i X)
              (FreeCoprodCompDisc.coprodPairDesc I e
                (FreeCoprodCompDisc.Hom.id I X))))).trans
        ((congrArg
            (FreeCoprodCompDisc.Hom.comp I
              (⟨fun z ↦ Sum.inl (_root_.id z.down), rfl⟩ :
                FreeCoprodCompDisc.Hom I
                  (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩)
                  (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨B, i⟩ X)))
            (mplusInj_natural.{uA, uB, uI} I L
              (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨B, i⟩ X) X
              (FreeCoprodCompDisc.Hom.comp I (plusLiftBridgeInvHom I B i X)
                (FreeCoprodCompDisc.coprodPairDesc I e
                  (FreeCoprodCompDisc.Hom.id I X))))).trans
          ((FreeCoprodCompDisc.Hom.comp_assoc I
              (⟨fun z ↦ Sum.inl (_root_.id z.down), rfl⟩ :
                FreeCoprodCompDisc.Hom I
                  (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩)
                  (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨B, i⟩ X))
              (FreeCoprodCompDisc.Hom.comp I (plusLiftBridgeInvHom I B i X)
                (FreeCoprodCompDisc.coprodPairDesc I e
                  (FreeCoprodCompDisc.Hom.id I X)))
              (mplusInj.{uA, uB, uI} I L X)).symm.trans
            (congrArg
              (fun t ↦ FreeCoprodCompDisc.Hom.comp I t
                (mplusInj.{uA, uB, uI} I L X))
              (Subtype.ext rfl :
                FreeCoprodCompDisc.Hom.comp I
                    (⟨fun z ↦ Sum.inl (_root_.id z.down), rfl⟩ :
                      FreeCoprodCompDisc.Hom I
                        (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩)
                        (FreeCoprodCompDisc.plus.{uI, uB, max uA uB}
                          I ⟨B, i⟩ X))
                    (FreeCoprodCompDisc.Hom.comp I
                      (plusLiftBridgeInvHom I B i X)
                      (FreeCoprodCompDisc.coprodPairDesc I e
                        (FreeCoprodCompDisc.Hom.id I X))) =
                  e))))))

/-- The tower-conjugated navigation inclusion, followed by the tower
isomorphism at the extended stack, is the weighted copower injection
and the summand inclusion at the tower coproduct. -/
theorem navInj_comp_hom (Bout : Type uB) (iout : Bout → I) (Bin : Type uB)
    (K : (Bin → I) → IR.{max uA uB, uB, uI, uO} I O) (g : Bin → Bout)
    (L : List (SupObj.{uB, uI} I)) (X : FreeCoprodCompDisc.{max uA uB, uI} I) :
    FreeCoprodCompDisc.Hom.comp O (navInj I O Bout iout Bin K g L X)
        (FreeCoprodCompDisc.Iso.hom O
          (mprecompIso.{uA, uB, uI, uO} I O
            (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) (delta I O Bin K) X)) =
      FreeCoprodCompDisc.Hom.comp O
        (FreeCoprodCompDisc.Iso.hom O
          (mprecompIso.{uA, uB, uI, uO} I O
            (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) (K (iout ∘ g)) X))
        (FreeCoprodCompDisc.Hom.comp O
          (FreeCoprodCompDisc.coprodInj O
            (FreeCoprodCompDisc.Hom I
              (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Bin, iout ∘ g⟩)
              (mplus.{uA, uB, uI} I
                (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X))
            (fun _ ↦ interpObj I O (K (iout ∘ g))
              (mplus.{uA, uB, uI} I
                (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X))
            (navWeight I Bout iout Bin g X L))
          (deltaInto I O Bin K (iout ∘ g)
            (mplus.{uA, uB, uI} I
              (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X))) :=
  (congrArg
      (FreeCoprodCompDisc.Hom.comp O
        (FreeCoprodCompDisc.Hom.comp O
          (FreeCoprodCompDisc.Iso.hom O
            (mprecompIso.{uA, uB, uI, uO} I O
              (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) (K (iout ∘ g)) X))
          (FreeCoprodCompDisc.Hom.comp O
            (FreeCoprodCompDisc.coprodInj O
              (FreeCoprodCompDisc.Hom I
                (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Bin, iout ∘ g⟩)
                (mplus.{uA, uB, uI} I
                  (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X))
              (fun _ ↦ interpObj I O (K (iout ∘ g))
                (mplus.{uA, uB, uI} I
                  (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X))
              (navWeight I Bout iout Bin g X L))
            (deltaInto I O Bin K (iout ∘ g)
              (mplus.{uA, uB, uI} I
                (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X)))))
      (FreeCoprodCompDisc.Iso.invHom_hom O
        (mprecompIso.{uA, uB, uI, uO} I O
          (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)])
          (delta I O Bin K) X))).trans
    (FreeCoprodCompDisc.Hom.comp_id O
      (FreeCoprodCompDisc.Hom.comp O
        (FreeCoprodCompDisc.Iso.hom O
          (mprecompIso.{uA, uB, uI, uO} I O
            (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) (K (iout ∘ g)) X))
        (FreeCoprodCompDisc.Hom.comp O
          (FreeCoprodCompDisc.coprodInj O
            (FreeCoprodCompDisc.Hom I
              (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Bin, iout ∘ g⟩)
              (mplus.{uA, uB, uI} I
                (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X))
            (fun _ ↦ interpObj I O (K (iout ∘ g))
              (mplus.{uA, uB, uI} I
                (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X))
            (navWeight I Bout iout Bin g X L))
          (deltaInto I O Bin K (iout ∘ g)
            (mplus.{uA, uB, uI} I
              (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X)))))

/-- The semantic pre-unit component, followed by the tower
isomorphism, is the interpreted tower injection. -/
theorem preUnitComponent_comp_hom (γ : IR.{max uA uB, uB, uI, uO} I O)
    (L : List (SupObj.{uB, uI} I)) (X : FreeCoprodCompDisc.{max uA uB, uI} I) :
    FreeCoprodCompDisc.Hom.comp O (preUnitComponent I O γ L X)
        (FreeCoprodCompDisc.Iso.hom O
          (mprecompIso.{uA, uB, uI, uO} I O L γ X)) =
      interpMor I O γ X (mplus.{uA, uB, uI} I L X)
        (mplusInj.{uA, uB, uI} I L X) :=
  (congrArg
      (FreeCoprodCompDisc.Hom.comp O
        (interpMor I O γ X (mplus.{uA, uB, uI} I L X)
          (mplusInj.{uA, uB, uI} I L X)))
      (FreeCoprodCompDisc.Iso.invHom_hom O
        (mprecompIso.{uA, uB, uI, uO} I O L γ X))).trans
    (FreeCoprodCompDisc.Hom.comp_id O
      (interpMor I O γ X (mplus.{uA, uB, uI} I L X)
        (mplusInj.{uA, uB, uI} I L X)))

/-- The reduced form of the per-weight identity-image equation: after
the tower isomorphisms cancel, both routes are the interpreted tower
injection followed by the reindexed weighted summand inclusion. -/
theorem interpHom_preUnitStack_deltaWeightRight (B : Type uB)
    (d : Direction I O (Sum.inr (Sum.inr B) : Shape.{max uA uB, uB, uO} O) →
      IR.{max uA uB, uB, uI, uO} I O)
    (ih : (x : Direction I O (Sum.inr (Sum.inr B) : Shape.{max uA uB, uB, uO} O)) →
      InterpHomPreUnitMotive I O (d x))
    (L : List (SupObj.{uB, uI} I)) (X : FreeCoprodCompDisc.{max uA uB, uI} I)
    (i : B → I)
    (e : FreeCoprodCompDisc.Hom I
      (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) X) :
    FreeCoprodCompDisc.Hom.comp O
        ((interpHom I O (d (ULift.up i))
          (mprecomp I O (L ++ [(⟨B, i⟩ : SupObj.{uB, uI} I)])
            (mk I O (Sum.inr (Sum.inr B)) d))
          (deltaNav I O (d (ULift.up i)) B i B (fun i' ↦ d (ULift.up i'))
            _root_.id L
            (preUnitStack I O (d (ULift.up i))
              (L ++ [(⟨B, i⟩ : SupObj.{uB, uI} I)])))).1 X)
        (FreeCoprodCompDisc.Hom.comp O
          (FreeCoprodCompDisc.Iso.hom O
            (mprecompIso.{uA, uB, uI, uO} I O
              (L ++ [(⟨B, i⟩ : SupObj.{uB, uI} I)])
              (mk I O (Sum.inr (Sum.inr B)) d) X))
          (interpMor I O (mk I O (Sum.inr (Sum.inr B)) d)
            (mplus.{uA, uB, uI} I (L ++ [(⟨B, i⟩ : SupObj.{uB, uI} I)]) X)
            (mplus.{uA, uB, uI} I L X)
            (navBridgeMor.{uA, uB, uI} I B i L X e))) =
      FreeCoprodCompDisc.Hom.comp O
        (FreeCoprodCompDisc.coprodInj O
          (FreeCoprodCompDisc.Hom I
            (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) X)
          (fun _ ↦ interpObj I O (d (ULift.up i)) X) e)
        (FreeCoprodCompDisc.Hom.comp O
          (deltaInto I O B (fun j ↦ d (ULift.up j)) i X)
          (interpMor I O (mk I O (Sum.inr (Sum.inr B)) d) X
            (mplus.{uA, uB, uI} I L X) (mplusInj.{uA, uB, uI} I L X))) :=
  (congrArg
      (fun t ↦ FreeCoprodCompDisc.Hom.comp O t
        (FreeCoprodCompDisc.Hom.comp O
          (FreeCoprodCompDisc.Iso.hom O
            (mprecompIso.{uA, uB, uI, uO} I O
              (L ++ [(⟨B, i⟩ : SupObj.{uB, uI} I)])
              (mk I O (Sum.inr (Sum.inr B)) d) X))
          (interpMor I O (mk I O (Sum.inr (Sum.inr B)) d)
            (mplus.{uA, uB, uI} I (L ++ [(⟨B, i⟩ : SupObj.{uB, uI} I)]) X)
            (mplus.{uA, uB, uI} I L X)
            (navBridgeMor.{uA, uB, uI} I B i L X e))))
      ((interpHom_deltaNav I O (d (ULift.up i)) B i B
          (fun i' ↦ d (ULift.up i')) _root_.id L
          (preUnitStack I O (d (ULift.up i))
            (L ++ [(⟨B, i⟩ : SupObj.{uB, uI} I)])) X).trans
        (congrArg
          (fun t ↦ FreeCoprodCompDisc.Hom.comp O t
            (navInj I O B i B (fun i' ↦ d (ULift.up i')) _root_.id L X))
          (ih (ULift.up i) (L ++ [(⟨B, i⟩ : SupObj.{uB, uI} I)]) X)))).trans
    ((congrArg
        (fun t ↦ FreeCoprodCompDisc.Hom.comp O
          (preUnitComponent I O (d (ULift.up i))
            (L ++ [(⟨B, i⟩ : SupObj.{uB, uI} I)]) X)
          (FreeCoprodCompDisc.Hom.comp O t
            (interpMor I O (mk I O (Sum.inr (Sum.inr B)) d)
              (mplus.{uA, uB, uI} I (L ++ [(⟨B, i⟩ : SupObj.{uB, uI} I)]) X)
              (mplus.{uA, uB, uI} I L X)
              (navBridgeMor.{uA, uB, uI} I B i L X e))))
        (navInj_comp_hom I O B i B (fun i' ↦ d (ULift.up i')) _root_.id
          L X)).trans
      ((congrArg
          (fun t ↦ FreeCoprodCompDisc.Hom.comp O t
            (FreeCoprodCompDisc.Hom.comp O
              (FreeCoprodCompDisc.Hom.comp O
                (FreeCoprodCompDisc.coprodInj O
                  (FreeCoprodCompDisc.Hom I
                    (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩)
                    (mplus.{uA, uB, uI} I
                      (L ++ [(⟨B, i⟩ : SupObj.{uB, uI} I)]) X))
                  (fun _ ↦ interpObj I O (d (ULift.up i))
                    (mplus.{uA, uB, uI} I
                      (L ++ [(⟨B, i⟩ : SupObj.{uB, uI} I)]) X))
                  (navWeight I B i B _root_.id X L))
                (deltaInto I O B (fun j ↦ d (ULift.up j)) i
                  (mplus.{uA, uB, uI} I
                    (L ++ [(⟨B, i⟩ : SupObj.{uB, uI} I)]) X)))
              (interpMor I O (mk I O (Sum.inr (Sum.inr B)) d)
                (mplus.{uA, uB, uI} I (L ++ [(⟨B, i⟩ : SupObj.{uB, uI} I)]) X)
                (mplus.{uA, uB, uI} I L X)
                (navBridgeMor.{uA, uB, uI} I B i L X e))))
          (preUnitComponent_comp_hom I O (d (ULift.up i))
            (L ++ [(⟨B, i⟩ : SupObj.{uB, uI} I)]) X)).trans
        ((congrArg
            (FreeCoprodCompDisc.Hom.comp O
              (interpMor I O (d (ULift.up i)) X
                (mplus.{uA, uB, uI} I (L ++ [(⟨B, i⟩ : SupObj.{uB, uI} I)]) X)
                (mplusInj.{uA, uB, uI} I
                  (L ++ [(⟨B, i⟩ : SupObj.{uB, uI} I)]) X)))
            (deltaIntoWeight_comp I O B (fun j ↦ d (ULift.up j)) i
              (mplus.{uA, uB, uI} I (L ++ [(⟨B, i⟩ : SupObj.{uB, uI} I)]) X)
              (mplus.{uA, uB, uI} I L X)
              (navBridgeMor.{uA, uB, uI} I B i L X e)
              (navWeight I B i B _root_.id X L))).trans
          ((congrArg
              (fun t ↦ FreeCoprodCompDisc.Hom.comp O
                (FreeCoprodCompDisc.Hom.comp O t
                  (FreeCoprodCompDisc.coprodInj O
                    (FreeCoprodCompDisc.Hom I
                      (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩)
                      (mplus.{uA, uB, uI} I L X))
                    (fun _ ↦ interpObj I O (d (ULift.up i))
                      (mplus.{uA, uB, uI} I L X))
                    (FreeCoprodCompDisc.Hom.comp I
                      (navWeight I B i B _root_.id X L)
                      (navBridgeMor.{uA, uB, uI} I B i L X e))))
                (deltaInto I O B (fun j ↦ d (ULift.up j)) i
                  (mplus.{uA, uB, uI} I L X)))
              (interpMor_comp I O (d (ULift.up i)) X
                (mplus.{uA, uB, uI} I (L ++ [(⟨B, i⟩ : SupObj.{uB, uI} I)]) X)
                (mplus.{uA, uB, uI} I L X)
                (mplusInj.{uA, uB, uI} I
                  (L ++ [(⟨B, i⟩ : SupObj.{uB, uI} I)]) X)
                (navBridgeMor.{uA, uB, uI} I B i L X e)).symm).trans
            ((congrArg
                (fun t ↦ FreeCoprodCompDisc.Hom.comp O
                  (FreeCoprodCompDisc.Hom.comp O
                    (interpMor I O (d (ULift.up i)) X
                      (mplus.{uA, uB, uI} I L X) t)
                    (FreeCoprodCompDisc.coprodInj O
                      (FreeCoprodCompDisc.Hom I
                        (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩)
                        (mplus.{uA, uB, uI} I L X))
                      (fun _ ↦ interpObj I O (d (ULift.up i))
                        (mplus.{uA, uB, uI} I L X))
                      (FreeCoprodCompDisc.Hom.comp I
                        (navWeight I B i B _root_.id X L)
                        (navBridgeMor.{uA, uB, uI} I B i L X e))))
                  (deltaInto I O B (fun j ↦ d (ULift.up j)) i
                    (mplus.{uA, uB, uI} I L X)))
                (mplusInj_navBridge.{uA, uB, uI} I B i L X e)).trans
              ((congrArg
                  (fun t ↦ FreeCoprodCompDisc.Hom.comp O
                    (FreeCoprodCompDisc.Hom.comp O
                      (interpMor I O (d (ULift.up i)) X
                        (mplus.{uA, uB, uI} I L X)
                        (mplusInj.{uA, uB, uI} I L X))
                      (FreeCoprodCompDisc.coprodInj O
                        (FreeCoprodCompDisc.Hom I
                          (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩)
                          (mplus.{uA, uB, uI} I L X))
                        (fun _ ↦ interpObj I O (d (ULift.up i))
                          (mplus.{uA, uB, uI} I L X))
                        t))
                    (deltaInto I O B (fun j ↦ d (ULift.up j)) i
                      (mplus.{uA, uB, uI} I L X)))
                  (navWeight_navBridge.{uA, uB, uI} I B i L X e)).trans
                (deltaIntoWeight_comp I O B (fun j ↦ d (ULift.up j)) i X
                  (mplus.{uA, uB, uI} I L X)
                  (mplusInj.{uA, uB, uI} I L X) e).symm))))))

/-- The per-weight identity-image equation at a `δ`-domain: at each
weight out of the lifted arity, the copower-adjunction transport of the
navigated subcode pre-unit is the weight's injection followed by the
summand inclusion and the semantic pre-unit component. -/
theorem interpHom_preUnitStack_deltaWeight (B : Type uB)
    (d : Direction I O (Sum.inr (Sum.inr B) : Shape.{max uA uB, uB, uO} O) →
      IR.{max uA uB, uB, uI, uO} I O)
    (ih : (x : Direction I O (Sum.inr (Sum.inr B) : Shape.{max uA uB, uB, uO} O)) →
      InterpHomPreUnitMotive I O (d x))
    (L : List (SupObj.{uB, uI} I)) (X : FreeCoprodCompDisc.{max uA uB, uI} I)
    (i : B → I)
    (e : FreeCoprodCompDisc.Hom I
      (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) X) :
    FreeCoprodCompDisc.Hom.comp O
        (FreeCoprodCompDisc.Hom.comp O
          (FreeCoprodCompDisc.Hom.comp O
            ((interpHom I O (d (ULift.up i))
              (precomp I O B i (mprecomp I O L (mk I O (Sum.inr (Sum.inr B)) d)))
              (preUnitDeltaData I O B d L i)).1 X)
            (FreeCoprodCompDisc.Iso.hom O
              (interpPrecompIso I O
                (mprecomp I O L (mk I O (Sum.inr (Sum.inr B)) d)) B i X)))
          ((plusLiftBridgeNatInv I O B i
            (mprecomp I O L (mk I O (Sum.inr (Sum.inr B)) d))).1 X))
        (interpMor I O (mprecomp I O L (mk I O (Sum.inr (Sum.inr B)) d))
          (FreeCoprodCompDisc.plus I
            (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) X)
          X
          (FreeCoprodCompDisc.coprodPairDesc I e
            (FreeCoprodCompDisc.Hom.id I X))) =
      FreeCoprodCompDisc.Hom.comp O
        (FreeCoprodCompDisc.coprodInj O
          (FreeCoprodCompDisc.Hom I
            (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) X)
          (fun _ ↦ interpObj I O (d (ULift.up i)) X) e)
        (FreeCoprodCompDisc.Hom.comp O
          (deltaInto I O B (fun j ↦ d (ULift.up j)) i X)
          (preUnitComponent I O (mk I O (Sum.inr (Sum.inr B)) d) L X)) :=
  FreeCoprodCompDisc.eq_comp_invHom O (interpObj I O (d (ULift.up i)) X)
    (interpObj I O (mprecomp I O L (mk I O (Sum.inr (Sum.inr B)) d)) X)
    (interpObj I O (mk I O (Sum.inr (Sum.inr B)) d) (mplus.{uA, uB, uI} I L X))
    (FreeCoprodCompDisc.Hom.comp O
      (FreeCoprodCompDisc.Hom.comp O
        (FreeCoprodCompDisc.Hom.comp O
          ((interpHom I O (d (ULift.up i))
            (precomp I O B i (mprecomp I O L (mk I O (Sum.inr (Sum.inr B)) d)))
            (preUnitDeltaData I O B d L i)).1 X)
          (FreeCoprodCompDisc.Iso.hom O
            (interpPrecompIso I O
              (mprecomp I O L (mk I O (Sum.inr (Sum.inr B)) d)) B i X)))
        ((plusLiftBridgeNatInv I O B i
          (mprecomp I O L (mk I O (Sum.inr (Sum.inr B)) d))).1 X))
      (interpMor I O (mprecomp I O L (mk I O (Sum.inr (Sum.inr B)) d))
        (FreeCoprodCompDisc.plus I
          (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) X)
        X
        (FreeCoprodCompDisc.coprodPairDesc I e (FreeCoprodCompDisc.Hom.id I X))))
    (FreeCoprodCompDisc.Hom.comp O
      (FreeCoprodCompDisc.coprodInj O
        (FreeCoprodCompDisc.Hom I
          (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) X)
        (fun _ ↦ interpObj I O (d (ULift.up i)) X) e)
      (FreeCoprodCompDisc.Hom.comp O
        (deltaInto I O B (fun j ↦ d (ULift.up j)) i X)
        (interpMor I O (mk I O (Sum.inr (Sum.inr B)) d) X
          (mplus.{uA, uB, uI} I L X) (mplusInj.{uA, uB, uI} I L X))))
    (mprecompIso.{uA, uB, uI, uO} I O L (mk I O (Sum.inr (Sum.inr B)) d) X)
    ((congrArg
        (fun t ↦ FreeCoprodCompDisc.Hom.comp O
          (FreeCoprodCompDisc.Hom.comp O
            ((interpHom I O (d (ULift.up i))
              (precomp I O B i
                (mprecomp I O L (mk I O (Sum.inr (Sum.inr B)) d)))
              (preUnitDeltaData I O B d L i)).1 X)
            (FreeCoprodCompDisc.Iso.hom O
              (interpPrecompIso I O
                (mprecomp I O L (mk I O (Sum.inr (Sum.inr B)) d)) B i X)))
          (FreeCoprodCompDisc.Hom.comp O t
            (FreeCoprodCompDisc.Iso.hom O
              (mprecompIso.{uA, uB, uI, uO} I O L
                (mk I O (Sum.inr (Sum.inr B)) d) X))))
        (interpMor_comp I O (mprecomp I O L (mk I O (Sum.inr (Sum.inr B)) d))
            (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨B, i⟩ X)
            (FreeCoprodCompDisc.plus I
              (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) X)
            X (plusLiftBridgeInvHom I B i X)
            (FreeCoprodCompDisc.coprodPairDesc I e
              (FreeCoprodCompDisc.Hom.id I X))).symm).trans
      ((congrArg
          (FreeCoprodCompDisc.Hom.comp O
            (FreeCoprodCompDisc.Hom.comp O
              ((interpHom I O (d (ULift.up i))
                (precomp I O B i
                  (mprecomp I O L (mk I O (Sum.inr (Sum.inr B)) d)))
                (preUnitDeltaData I O B d L i)).1 X)
              (FreeCoprodCompDisc.Iso.hom O
                (interpPrecompIso I O
                  (mprecomp I O L (mk I O (Sum.inr (Sum.inr B)) d)) B i X))))
          (mprecompIso_natural.{uA, uB, uI, uO} I O L
            (mk I O (Sum.inr (Sum.inr B)) d)
            (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨B, i⟩ X) X
            (FreeCoprodCompDisc.Hom.comp I (plusLiftBridgeInvHom I B i X)
              (FreeCoprodCompDisc.coprodPairDesc I e
                (FreeCoprodCompDisc.Hom.id I X))))).trans
        ((congrArg
            (fun t ↦ FreeCoprodCompDisc.Hom.comp O
              (FreeCoprodCompDisc.Hom.comp O t
                (FreeCoprodCompDisc.Iso.hom O
                  (interpPrecompIso I O
                    (mprecomp I O L (mk I O (Sum.inr (Sum.inr B)) d)) B i X)))
              (FreeCoprodCompDisc.Hom.comp O
                (FreeCoprodCompDisc.Iso.hom O
                  (mprecompIso.{uA, uB, uI, uO} I O L
                    (mk I O (Sum.inr (Sum.inr B)) d)
                    (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨B, i⟩ X)))
                (interpMor I O (mk I O (Sum.inr (Sum.inr B)) d)
                  (mplus.{uA, uB, uI} I L
                    (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨B, i⟩ X))
                  (mplus.{uA, uB, uI} I L X)
                  (mplusMorMap.{uA, uB, uI} I L
                    (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨B, i⟩ X) X
                    (FreeCoprodCompDisc.Hom.comp I
                      (plusLiftBridgeInvHom I B i X)
                      (FreeCoprodCompDisc.coprodPairDesc I e
                        (FreeCoprodCompDisc.Hom.id I X)))))))
            (interpHom_cast_cod I O (d (ULift.up i))
              (mprecomp I O (L ++ [(⟨B, i⟩ : SupObj.{uB, uI} I)])
                (mk I O (Sum.inr (Sum.inr B)) d))
              X
              (precomp I O B i
                (mprecomp I O L (mk I O (Sum.inr (Sum.inr B)) d)))
              (mprecomp_snoc I O L (⟨B, i⟩ : SupObj.{uB, uI} I)
                (mk I O (Sum.inr (Sum.inr B)) d))
              (deltaNav I O (d (ULift.up i)) B i B (fun i' ↦ d (ULift.up i'))
                _root_.id L
                (preUnitStack I O (d (ULift.up i))
                  (L ++ [(⟨B, i⟩ : SupObj.{uB, uI} I)]))))).trans
          ((congrArg
              (fun t ↦ FreeCoprodCompDisc.Hom.comp O
                ((interpHom I O (d (ULift.up i))
                  (mprecomp I O (L ++ [(⟨B, i⟩ : SupObj.{uB, uI} I)])
                    (mk I O (Sum.inr (Sum.inr B)) d))
                  (deltaNav I O (d (ULift.up i)) B i B
                    (fun i' ↦ d (ULift.up i')) _root_.id L
                    (preUnitStack I O (d (ULift.up i))
                      (L ++ [(⟨B, i⟩ : SupObj.{uB, uI} I)])))).1 X)
                (FreeCoprodCompDisc.Hom.comp O t
                  (interpMor I O (mk I O (Sum.inr (Sum.inr B)) d)
                    (mplus.{uA, uB, uI} I L
                      (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨B, i⟩ X))
                    (mplus.{uA, uB, uI} I L X)
                    (mplusMorMap.{uA, uB, uI} I L
                      (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨B, i⟩ X) X
                      (FreeCoprodCompDisc.Hom.comp I
                        (plusLiftBridgeInvHom I B i X)
                        (FreeCoprodCompDisc.coprodPairDesc I e
                          (FreeCoprodCompDisc.Hom.id I X)))))))
              (mprecompIso_snoc_hom_comp I O L (⟨B, i⟩ : SupObj.{uB, uI} I)
                (mk I O (Sum.inr (Sum.inr B)) d) X)).trans
            ((congrArg
                (fun t ↦ FreeCoprodCompDisc.Hom.comp O
                  ((interpHom I O (d (ULift.up i))
                    (mprecomp I O (L ++ [(⟨B, i⟩ : SupObj.{uB, uI} I)])
                      (mk I O (Sum.inr (Sum.inr B)) d))
                    (deltaNav I O (d (ULift.up i)) B i B
                      (fun i' ↦ d (ULift.up i')) _root_.id L
                      (preUnitStack I O (d (ULift.up i))
                        (L ++ [(⟨B, i⟩ : SupObj.{uB, uI} I)])))).1 X)
                  (FreeCoprodCompDisc.Hom.comp O
                    (FreeCoprodCompDisc.Iso.hom O
                      (mprecompIso.{uA, uB, uI, uO} I O
                        (L ++ [(⟨B, i⟩ : SupObj.{uB, uI} I)])
                        (mk I O (Sum.inr (Sum.inr B)) d) X))
                    t))
                (interpMor_isoOfEq_dom I O (mk I O (Sum.inr (Sum.inr B)) d)
                  (mplus.{uA, uB, uI} I
                    (L ++ [(⟨B, i⟩ : SupObj.{uB, uI} I)]) X)
                  (mplus.{uA, uB, uI} I L X)
                  (mplus.{uA, uB, uI} I L
                    (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨B, i⟩ X))
                  (mplus_snoc.{uA, uB, uI} I L
                    (⟨B, i⟩ : SupObj.{uB, uI} I) X)
                  (mplusMorMap.{uA, uB, uI} I L
                    (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨B, i⟩ X) X
                    (FreeCoprodCompDisc.Hom.comp I
                      (plusLiftBridgeInvHom I B i X)
                      (FreeCoprodCompDisc.coprodPairDesc I e
                        (FreeCoprodCompDisc.Hom.id I X)))))).trans
              (interpHom_preUnitStack_deltaWeightRight I O B d ih L X i e))))))

/-- The per-summand identity-image equation at a `δ`-domain: the
navigated subcode pre-unit's transported interpretation is the summand
inclusion followed by the semantic pre-unit component. -/
theorem interpHom_preUnitStack_deltaSummand (B : Type uB)
    (d : Direction I O (Sum.inr (Sum.inr B) : Shape.{max uA uB, uB, uO} O) →
      IR.{max uA uB, uB, uI, uO} I O)
    (ih : (x : Direction I O (Sum.inr (Sum.inr B) : Shape.{max uA uB, uB, uO} O)) →
      InterpHomPreUnitMotive I O (d x))
    (L : List (SupObj.{uB, uI} I)) (X : FreeCoprodCompDisc.{max uA uB, uI} I)
    (i : B → I) :
    (interpHomDeltaSummand I O B (fun j ↦ d (ULift.up j))
        (mprecomp I O L (mk I O (Sum.inr (Sum.inr B)) d)) i
        (preUnitDeltaData I O B d L i)).1 X =
      FreeCoprodCompDisc.Hom.comp O
        (deltaInto I O B (fun j ↦ d (ULift.up j)) i X)
        (preUnitComponent I O (mk I O (Sum.inr (Sum.inr B)) d) L X) :=
  (congrArg
      (FreeCoprodCompDisc.coprodDesc O
        (FreeCoprodCompDisc.Hom I
          (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) X)
        (fun _ ↦ interpObj I O (d (ULift.up i)) X)
        (interpObj I O (mprecomp I O L (mk I O (Sum.inr (Sum.inr B)) d)) X))
      (funext (fun e ↦
        interpHom_preUnitStack_deltaWeight I O B d ih L X i e))).trans
    (FreeCoprodCompDisc.coprodDesc_eta O
      (FreeCoprodCompDisc.Hom I
        (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) X)
      (fun _ ↦ interpObj I O (d (ULift.up i)) X)
      (interpObj I O (mprecomp I O L (mk I O (Sum.inr (Sum.inr B)) d)) X)
      (FreeCoprodCompDisc.Hom.comp O
        (deltaInto I O B (fun j ↦ d (ULift.up j)) i X)
        (preUnitComponent I O (mk I O (Sum.inr (Sum.inr B)) d) L X)))

/-- The `δ`-domain case of the identity-image equation. -/
theorem interpHom_preUnitStack_mk_delta (B : Type uB)
    (d : Direction I O (Sum.inr (Sum.inr B) : Shape.{max uA uB, uB, uO} O) →
      IR.{max uA uB, uB, uI, uO} I O)
    (ih : (x : Direction I O (Sum.inr (Sum.inr B) : Shape.{max uA uB, uB, uO} O)) →
      InterpHomPreUnitMotive I O (d x)) :
    InterpHomPreUnitMotive I O (mk I O (Sum.inr (Sum.inr B)) d) :=
  fun L X ↦
    (congrArg
        (fun t ↦ (interpHom I O (mk I O (Sum.inr (Sum.inr B)) d)
          (mprecomp I O L (mk I O (Sum.inr (Sum.inr B)) d)) t).1 X)
        (funext (fun i ↦ preUnitStack_mk_delta I O B d L i))).trans
      ((interpHom_delta I O B (fun j ↦ d (ULift.up j))
          (mprecomp I O L (mk I O (Sum.inr (Sum.inr B)) d))
          (preUnitDeltaData I O B d L) X).trans
        ((congrArg
            (deltaDesc I O B (fun j ↦ d (ULift.up j)) X
              (interpObj I O (mprecomp I O L (mk I O (Sum.inr (Sum.inr B)) d)) X))
            (funext (fun i ↦
              interpHom_preUnitStack_deltaSummand I O B d ih L X i))).trans
          (deltaDesc_eta I O B (fun j ↦ d (ULift.up j)) X
            (interpObj I O (mprecomp I O L (mk I O (Sum.inr (Sum.inr B)) d)) X)
            (preUnitComponent I O (mk I O (Sum.inr (Sum.inr B)) d) L X))))

/-- The identity-image equation at an `ι`-domain, with the codomain
code and the target morphism generalized: at the reflexive instance the
codomain interpretation is the singleton object, so any two morphisms
into it agree. -/
theorem interpHom_preUnitStack_iotaGen (o : O)
    (d : Direction I O (Sum.inl o : Shape.{max uA uB, uB, uO} O) →
      IR.{max uA uB, uB, uI, uO} I O)
    (X : FreeCoprodCompDisc.{max uA uB, uI} I) :
    ∀ (γ'' : IR.{max uA uB, uB, uI, uO} I O)
      (hh : iota.{max uA uB, uB, uI, uO} I O o = γ'')
      (t : FreeCoprodCompDisc.Hom O
        (interpObj I O (mk I O (Sum.inl o) d) X) (interpObj I O γ'' X)),
      (interpHom I O (mk I O (Sum.inl o) d) γ''
        (cast (congrArg (Hom I O (mk I O (Sum.inl o) d)) hh)
          (ULift.up (PLift.up rfl) :
            Hom.{uA, uB, uI, uO} I O (mk I O (Sum.inl o) d)
              (iota.{max uA uB, uB, uI, uO} I O o)))).1 X = t :=
  fun _ hh ↦
    Eq.rec (motive := fun (γ'' : IR.{max uA uB, uB, uI, uO} I O)
        (hh' : iota.{max uA uB, uB, uI, uO} I O o = γ'') ↦
        ∀ t : FreeCoprodCompDisc.Hom O
          (interpObj I O (mk I O (Sum.inl o) d) X) (interpObj I O γ'' X),
          (interpHom I O (mk I O (Sum.inl o) d) γ''
            (cast (congrArg (Hom I O (mk I O (Sum.inl o) d)) hh')
              (ULift.up (PLift.up rfl) :
                Hom.{uA, uB, uI, uO} I O (mk I O (Sum.inl o) d)
                  (iota.{max uA uB, uB, uI, uO} I O o)))).1 X = t)
      (fun _ ↦ Subtype.ext (funext (fun _ ↦ congrArg ULift.up rfl))) hh

/-- The `ι`-domain case of the identity-image equation. -/
theorem interpHom_preUnitStack_mk_iota (o : O)
    (d : Direction I O (Sum.inl o : Shape.{max uA uB, uB, uO} O) →
      IR.{max uA uB, uB, uI, uO} I O) :
    InterpHomPreUnitMotive I O (mk I O (Sum.inl o) d) :=
  fun L X ↦
    (congrArg
        (fun t ↦ (interpHom I O (mk I O (Sum.inl o) d)
          (mprecomp I O L (mk I O (Sum.inl o) d)) t).1 X)
        (preUnitStack_mk_iota I O o d L)).trans
      (interpHom_preUnitStack_iotaGen I O o d X
        (mprecomp I O L (mk I O (Sum.inl o) d))
        (mprecomp_iota_mk I O L o d).symm
        (preUnitComponent I O (mk I O (Sum.inl o) d) L X))

/-- The per-summand identity-image equation at a `σ`-domain: the stack
`σ`-push of the subcode's pre-unit is the semantic `σ`-injection
followed by the pre-unit component. -/
theorem interpHom_preUnitStack_sigmaSummand (A : Type (max uA uB))
    (d : Direction I O (Sum.inr (Sum.inl A) : Shape.{max uA uB, uB, uO} O) →
      IR.{max uA uB, uB, uI, uO} I O)
    (ih : (x : Direction I O (Sum.inr (Sum.inl A) : Shape.{max uA uB, uB, uO} O)) →
      InterpHomPreUnitMotive I O (d x))
    (L : List (SupObj.{uB, uI} I)) (X : FreeCoprodCompDisc.{max uA uB, uI} I)
    (a : A) :
    (interpHom I O (d (ULift.up a))
        (mprecomp I O L (mk I O (Sum.inr (Sum.inl A)) d))
        (msigmaPush I O (d (ULift.up a)) A (fun a' ↦ d (ULift.up a')) a L
          (preUnitStack I O (d (ULift.up a)) L))).1 X =
      FreeCoprodCompDisc.Hom.comp O
        (FreeCoprodCompDisc.coprodInj O A
          (fun a' ↦ interpObj I O (d (ULift.up a')) X) a)
        (preUnitComponent I O (mk I O (Sum.inr (Sum.inl A)) d) L X) :=
  (interpHom_msigmaPush I O (d (ULift.up a)) A (fun a' ↦ d (ULift.up a')) a L
      (preUnitStack I O (d (ULift.up a)) L) X).trans
    ((congrArg
        (fun t ↦ FreeCoprodCompDisc.Hom.comp O t
          (FreeCoprodCompDisc.Hom.comp O
            (FreeCoprodCompDisc.Hom.comp O
              (FreeCoprodCompDisc.Iso.hom O
                (mprecompIso.{uA, uB, uI, uO} I O L (d (ULift.up a)) X))
              (FreeCoprodCompDisc.coprodInj O A
                (fun a' ↦ interpObj I O (d (ULift.up a'))
                  (mplus.{uA, uB, uI} I L X)) a))
            (FreeCoprodCompDisc.Iso.invHom O
              (mprecompIso.{uA, uB, uI, uO} I O L
                (mk I O (Sum.inr (Sum.inl A)) d) X))))
        (ih (ULift.up a) L X)).trans
      ((congrArg
          (fun t ↦ FreeCoprodCompDisc.Hom.comp O
            (interpMor I O (d (ULift.up a)) X (mplus.{uA, uB, uI} I L X)
              (mplusInj.{uA, uB, uI} I L X))
            (FreeCoprodCompDisc.Hom.comp O t
              (FreeCoprodCompDisc.Hom.comp O
                (FreeCoprodCompDisc.coprodInj O A
                  (fun a' ↦ interpObj I O (d (ULift.up a'))
                    (mplus.{uA, uB, uI} I L X)) a)
                (FreeCoprodCompDisc.Iso.invHom O
                  (mprecompIso.{uA, uB, uI, uO} I O L
                    (mk I O (Sum.inr (Sum.inl A)) d) X)))))
          (FreeCoprodCompDisc.Iso.invHom_hom O
            (mprecompIso.{uA, uB, uI, uO} I O L (d (ULift.up a)) X))).trans
        (congrArg
          (fun t ↦ FreeCoprodCompDisc.Hom.comp O t
            (FreeCoprodCompDisc.Iso.invHom O
              (mprecompIso.{uA, uB, uI, uO} I O L
                (mk I O (Sum.inr (Sum.inl A)) d) X)))
          (interpMor_sigma_inj I O A (fun a' ↦ d (ULift.up a')) a X
            (mplus.{uA, uB, uI} I L X) (mplusInj.{uA, uB, uI} I L X)).symm)))

/-- The `σ`-domain case of the identity-image equation. -/
theorem interpHom_preUnitStack_mk_sigma (A : Type (max uA uB))
    (d : Direction I O (Sum.inr (Sum.inl A) : Shape.{max uA uB, uB, uO} O) →
      IR.{max uA uB, uB, uI, uO} I O)
    (ih : (x : Direction I O (Sum.inr (Sum.inl A) : Shape.{max uA uB, uB, uO} O)) →
      InterpHomPreUnitMotive I O (d x)) :
    InterpHomPreUnitMotive I O (mk I O (Sum.inr (Sum.inl A)) d) :=
  fun L X ↦
    (congrArg
        (fun t ↦ (interpHom I O (mk I O (Sum.inr (Sum.inl A)) d)
          (mprecomp I O L (mk I O (Sum.inr (Sum.inl A)) d)) t).1 X)
        (funext (fun a ↦ preUnitStack_mk_sigma I O A d L a))).trans
      ((interpHom_sigma I O A (fun a ↦ d (ULift.up a))
          (mprecomp I O L (mk I O (Sum.inr (Sum.inl A)) d))
          (fun a ↦ msigmaPush I O (d (ULift.up a)) A
            (fun a' ↦ d (ULift.up a')) a L
            (preUnitStack I O (d (ULift.up a)) L)) X).trans
        ((congrArg
            (FreeCoprodCompDisc.coprodDesc O A
              (fun a ↦ interpObj I O (d (ULift.up a)) X)
              (interpObj I O
                (mprecomp I O L (mk I O (Sum.inr (Sum.inl A)) d)) X))
            (funext (fun a ↦
              interpHom_preUnitStack_sigmaSummand I O A d ih L X a))).trans
          (FreeCoprodCompDisc.coprodDesc_eta O A
            (fun a ↦ interpObj I O (d (ULift.up a)) X)
            (interpObj I O (mprecomp I O L (mk I O (Sum.inr (Sum.inl A)) d)) X)
            (preUnitComponent I O (mk I O (Sum.inr (Sum.inl A)) d) L X))))

/-- `IR.interpHom` sends `IR.preUnitStack` to the semantic pre-unit
component, by `IR.induction`. -/
theorem interpHom_preUnitStack (γ : IR.{max uA uB, uB, uI, uO} I O) :
    InterpHomPreUnitMotive I O γ :=
  induction I O (InterpHomPreUnitMotive I O)
    (fun s ↦ match s with
      | Sum.inl o => fun d _ ↦ interpHom_preUnitStack_mk_iota I O o d
      | Sum.inr (Sum.inl A) => fun d ih ↦ interpHom_preUnitStack_mk_sigma I O A d ih
      | Sum.inr (Sum.inr B) => fun d ih ↦ interpHom_preUnitStack_mk_delta I O B d ih)
    γ

/-! ### Composition and the category laws -/

/-- Composition of IR-code morphisms (Corollary 2 of
[HancockMcBrideGhaniMalatestaAltenkirch2013]): the image under
fullness of the vertical composite of the interpreted
transformations. -/
def comp (γ γ' γ'' : IR.{max uA uB, uB, uI, uO} I O)
    (f : Hom.{uA, uB, uI, uO} I O γ γ')
    (g : Hom.{uA, uB, uI, uO} I O γ' γ'') :
    Hom.{uA, uB, uI, uO} I O γ γ'' :=
  natToHom I O γ γ''
    (FreeCoprodCompDisc.NatTrans.vcomp (interpHom I O γ γ' f)
      (interpHom I O γ' γ'' g))

/-- `IR.interpHom` sends `IR.comp` to the vertical composite: the
interpretation is functorial on morphisms. -/
theorem interpHom_comp (γ γ' γ'' : IR.{max uA uB, uB, uI, uO} I O)
    (f : Hom.{uA, uB, uI, uO} I O γ γ')
    (g : Hom.{uA, uB, uI, uO} I O γ' γ'') :
    interpHom I O γ γ'' (comp I O γ γ' γ'' f g) =
      FreeCoprodCompDisc.NatTrans.vcomp (interpHom I O γ γ' f)
        (interpHom I O γ' γ'' g) :=
  interpHom_natToHom I O γ γ''
    (FreeCoprodCompDisc.NatTrans.vcomp (interpHom I O γ γ' f)
      (interpHom I O γ' γ'' g))

/-- Associativity of `IR.comp`, by conjugation through the Theorem 3
equivalence and associativity of vertical composition. -/
theorem comp_assoc (γ γ' γ'' γ''' : IR.{max uA uB, uB, uI, uO} I O)
    (f : Hom.{uA, uB, uI, uO} I O γ γ')
    (g : Hom.{uA, uB, uI, uO} I O γ' γ'')
    (h : Hom.{uA, uB, uI, uO} I O γ'' γ''') :
    comp I O γ γ'' γ''' (comp I O γ γ' γ'' f g) h =
      comp I O γ γ' γ''' f (comp I O γ' γ'' γ''' g h) :=
  (congrArg (fun t ↦ natToHom I O γ γ'''
      (FreeCoprodCompDisc.NatTrans.vcomp t (interpHom I O γ'' γ''' h)))
    (interpHom_comp I O γ γ' γ'' f g)).trans
    ((congrArg (natToHom I O γ γ''')
        (FreeCoprodCompDisc.NatTrans.vcomp_assoc (interpHom I O γ γ' f)
          (interpHom I O γ' γ'' g) (interpHom I O γ'' γ''' h))).trans
      (congrArg (fun t ↦ natToHom I O γ γ'''
          (FreeCoprodCompDisc.NatTrans.vcomp (interpHom I O γ γ' f) t))
        (interpHom_comp I O γ' γ'' γ''' g h)).symm)

/-- `IR.interpHom` sends `IR.id` to the identity transformation: the
identity-image equation at the empty stack. -/
theorem interpHom_id (γ : IR.{max uA uB, uB, uI, uO} I O) :
    interpHom I O γ γ (IR.id I O γ) =
      FreeCoprodCompDisc.NatTrans.id (interpObj I O γ) (interpMor I O γ) :=
  Subtype.ext (funext (fun X ↦
    (interpHom_preUnitStack I O γ [] X).trans (preUnitComponent_nil I O γ X)))

/-- `IR.id` is a left identity for `IR.comp`, by conjugation through the
Theorem 3 equivalence and the left identity of vertical composition. -/
theorem id_comp (γ γ' : IR.{max uA uB, uB, uI, uO} I O)
    (f : Hom.{uA, uB, uI, uO} I O γ γ') :
    comp I O γ γ γ' (IR.id I O γ) f = f :=
  (congrArg
      (fun t ↦ natToHom I O γ γ'
        (FreeCoprodCompDisc.NatTrans.vcomp t (interpHom I O γ γ' f)))
      (interpHom_id I O γ)).trans
    ((congrArg (natToHom I O γ γ')
        (FreeCoprodCompDisc.NatTrans.id_vcomp
          (interpHom I O γ γ' f))).trans
      (natToHom_interpHom I O γ γ' f))

/-- `IR.id` is a right identity for `IR.comp`, by conjugation through the
Theorem 3 equivalence and the right identity of vertical composition. -/
theorem comp_id (γ γ' : IR.{max uA uB, uB, uI, uO} I O)
    (f : Hom.{uA, uB, uI, uO} I O γ γ') :
    comp I O γ γ' γ' f (IR.id I O γ') = f :=
  (congrArg
      (fun t ↦ natToHom I O γ γ'
        (FreeCoprodCompDisc.NatTrans.vcomp (interpHom I O γ γ' f) t))
      (interpHom_id I O γ')).trans
    ((congrArg (natToHom I O γ γ')
        (FreeCoprodCompDisc.NatTrans.vcomp_id
          (interpHom I O γ γ' f))).trans
      (natToHom_interpHom I O γ γ' f))

end IR

end IndRec
