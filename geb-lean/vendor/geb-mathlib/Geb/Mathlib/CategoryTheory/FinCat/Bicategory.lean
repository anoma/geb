/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.CategoryTheory.FinCat.Hom2
public import Mathlib.CategoryTheory.Bicategory.Strict.Basic

/-!
# The bicategory of finite-category specifications

Whiskering a 2-cell specification by a 1-cell specification on either
side. Left whiskering reindexes the components along the inner 1-cell's
object map; right whiskering applies the outer 1-cell's total morphism
map to each component.

## Main definitions

* `CategoryTheory.FinCat.Hom₂.whiskerLeft`,
  `CategoryTheory.FinCat.Hom₂.whiskerRight` — the two whiskerings.
* `CategoryTheory.FinCat.bicategory`,
  `CategoryTheory.FinCat.bicategory_strict`,
  `CategoryTheory.FinCat.category` — the bicategory of specifications,
  its strictness, and the resulting category.

## Main statements

* `FinCat.Hom₂.eqToHom_app` — the components of `CategoryTheory.eqToHom`
  at an equality of 1-cell specifications.
* `FinCat.Hom₂.id_whiskerLeft`, `FinCat.Hom₂.comp_whiskerLeft`,
  `FinCat.Hom₂.id_whiskerRight`, `FinCat.Hom₂.comp_whiskerRight`,
  `FinCat.Hom₂.whiskerRight_id`, `FinCat.Hom₂.whiskerRight_comp`,
  `FinCat.Hom₂.whisker_assoc`, `FinCat.Hom₂.whisker_exchange`,
  `FinCat.Hom₂.pentagon`, `FinCat.Hom₂.triangle` — the coherence axioms
  of a bicategory, with the associator and the unitors taken to be
  `CategoryTheory.eqToHom` at the strict equalities
  `FinCat.Hom.assoc`, `FinCat.Hom.id_comp` and `FinCat.Hom.comp_id`.

## Implementation notes

The whiskerings' result types are written with `⟶` at the 2-cell level,
which resolves through `FinCat.Hom.instCategory`, and with
`FinCat.Hom.comp` for the 1-cell composite. The 1-cell composite cannot
be written `≫`: that notation needs a `CategoryTheory.CategoryStruct`
on `FinCat`, which does not yet exist.

The coherence proofs stay at the component level and apply
`FinCat.Hom₂.ext` as a term rather than through the `ext` tactic.
`FinCat.Mor` is an `abbrev` and so reducible, and the `@[ext]` chain
descends through `Fin.ext` to `Fin.val`, past the point at which
`FinCat.Hom₂.natCheck_total` and `FinCat.Hom.mapTotal_id` apply. The
`Fin.cast` that `FinCat.Hom₂.eqToHom_app` introduces is definitionally
the identity at `FinCat.Mor`, 1-cell composition being definitionally
unital and associative on `objMap`; it is therefore left to `exact` and
never rewritten away.

`FinCat.Hom.comp_mapTotal` is what both naturality checks open with: the
composite specification's total map and the composite of the two total
maps dispatch on different `Nat.decLt` instances and are not
definitionally equal.

Left whiskering's check reduces to the inner 2-cell's naturality at
`F.mapTotal (S.emb f)`, which `FinCat.Hom.mapTotal_emb` identifies with
`F.map i j f` — a value of the full hom type rather than an embedded
client morphism, a 1-cell specification being free to send a client
morphism to a reserved identity. It therefore needs
`FinCat.Hom₂.natCheck_total`, the extension of the check off the client
range, rather than `FinCat.Hom₂.natCheck_eq_true_iff` alone.

## References

* [JohnsonYau2021] § 2.1 — the notion of bicategory, of which the
  whiskerings are part of the data.
* [JohnsonYau2021] § 2.3 — 2-categories, Definition 2.3.1, the strict
  case.

## Tags

category, functor, natural transformation, bicategory, 2-category,
whiskering, finite category, decidable, constructive, choice-free
-/

@[expose] public section

namespace CategoryTheory

namespace FinCat

namespace Hom₂

/-- Left whiskering: pure reindexing. -/
def whiskerLeft {S T U : FinCat} (F : Hom S T) {G H : Hom T U}
    (η : G ⟶ H) : F.comp G ⟶ F.comp H where
  app i := η.app (F.objMap i)
  natValid := by
    refine (natCheck_eq_true_iff S U (F.comp G) (F.comp H) _).mpr ?_
    intro i j f
    rw [Hom.comp_mapTotal, Hom.comp_mapTotal]
    exact natCheck_total η (F.mapTotal (S.emb f))

/-- Right whiskering: application of the outer 1-cell's total map. -/
def whiskerRight {S T U : FinCat} {F G : Hom S T} (η : F ⟶ G)
    (H : Hom T U) : F.comp H ⟶ G.comp H where
  app i := H.mapTotal (η.app i)
  natValid := by
    refine (natCheck_eq_true_iff S U (F.comp H) (G.comp H) _).mpr ?_
    intro i j f
    have h := congrArg H.mapTotal ((natCheck_eq_true_iff S T F G η.app).mp η.natValid i j f)
    rw [H.mapTotal_compTotal, H.mapTotal_compTotal] at h
    rw [Hom.comp_mapTotal, Hom.comp_mapTotal]
    exact h

/-- The components of `eqToHom` at an equality of 1-cells. It cannot be
stated as `(eqToHom p).app i = T.id (F.objMap i)`: `app`'s type
mentions both `F.objMap` and `G.objMap`, so the two sides would have
different types. -/
theorem eqToHom_app {S T : FinCat} {F G : Hom S T} (p : F = G) (i : Fin S.objCount) :
    (eqToHom p : F ⟶ G).app i
      = Fin.cast (congrArg (fun H ↦ T.homCount (F.objMap i) (H.objMap i)) p)
          (T.id (F.objMap i)) := by cases p; rfl

variable {S T U V W : FinCat}

/-- Left whiskering by the identity 1-cell is conjugation by the left
unitor. -/
theorem id_whiskerLeft {F G : Hom S T} (η : F ⟶ G) :
    whiskerLeft (Hom.id S) η
      = eqToHom (Hom.id_comp F) ≫ η ≫ eqToHom (Hom.id_comp G).symm :=
  Hom₂.ext fun i ↦ by
    rw [app_comp, app_comp, eqToHom_app, eqToHom_app]
    exact ((T.id_comp _).trans (T.comp_id _)).symm

/-- Left whiskering by a composite 1-cell is the two whiskerings in
turn, conjugated by the associator. -/
theorem comp_whiskerLeft (F : Hom S T) (G : Hom T U)
    {H H' : Hom U V} (η : H ⟶ H') :
    whiskerLeft (F.comp G) η
      = eqToHom (Hom.assoc F G H) ≫ whiskerLeft F (whiskerLeft G η)
          ≫ eqToHom (Hom.assoc F G H').symm :=
  Hom₂.ext fun i ↦ by
    rw [app_comp, app_comp, eqToHom_app, eqToHom_app]
    exact ((V.id_comp _).trans (V.comp_id _)).symm

/-- Right whiskering the identity 2-cell gives the identity 2-cell. -/
theorem id_whiskerRight (F : Hom S T) (G : Hom T U) :
    whiskerRight (𝟙 F) G = 𝟙 (F.comp G) :=
  Hom₂.ext fun i ↦ G.mapTotal_id (F.objMap i)

/-- Right whiskering distributes over vertical composition. -/
theorem comp_whiskerRight {F G H : Hom S T} (η : F ⟶ G) (θ : G ⟶ H)
    (I : Hom T U) :
    whiskerRight (η ≫ θ) I = whiskerRight η I ≫ whiskerRight θ I :=
  Hom₂.ext fun i ↦ I.mapTotal_compTotal (η.app i) (θ.app i)

/-- Right whiskering by the identity 1-cell is conjugation by the right
unitor. -/
theorem whiskerRight_id {F G : Hom S T} (η : F ⟶ G) :
    whiskerRight η (Hom.id T)
      = eqToHom (Hom.comp_id F) ≫ η ≫ eqToHom (Hom.comp_id G).symm :=
  Hom₂.ext fun i ↦ by
    rw [app_comp, app_comp, eqToHom_app, eqToHom_app]
    exact (Hom.id_mapTotal T (η.app i)).trans ((T.id_comp _).trans (T.comp_id _)).symm

/-- Right whiskering by a composite 1-cell is the two whiskerings in
turn, conjugated by the associator. -/
theorem whiskerRight_comp {F F' : Hom S T} (η : F ⟶ F') (G : Hom T U)
    (H : Hom U V) :
    whiskerRight η (G.comp H)
      = eqToHom (Hom.assoc F G H).symm ≫ whiskerRight (whiskerRight η G) H
          ≫ eqToHom (Hom.assoc F' G H) :=
  Hom₂.ext fun i ↦ by
    rw [app_comp, app_comp, eqToHom_app, eqToHom_app]
    exact (Hom.comp_mapTotal G H (η.app i)).trans ((V.id_comp _).trans (V.comp_id _)).symm

/-- Right whiskering a left whiskering is, conjugated by the associator,
the left whiskering of a right whiskering. -/
theorem whisker_assoc (F : Hom S T) {G G' : Hom T U} (η : G ⟶ G')
    (H : Hom U V) :
    whiskerRight (whiskerLeft F η) H
      = eqToHom (Hom.assoc F G H) ≫ whiskerLeft F (whiskerRight η H)
          ≫ eqToHom (Hom.assoc F G' H).symm :=
  Hom₂.ext fun i ↦ by
    rw [app_comp, app_comp, eqToHom_app, eqToHom_app]
    exact ((V.id_comp _).trans (V.comp_id _)).symm

/-- The exchange law between left and right whiskering. -/
theorem whisker_exchange {F G : Hom S T} {H I : Hom T U}
    (η : F ⟶ G) (θ : H ⟶ I) :
    whiskerLeft F θ ≫ whiskerRight η I = whiskerRight η H ≫ whiskerLeft G θ :=
  Hom₂.ext fun i ↦ (natCheck_total θ (η.app i)).symm

/-- The pentagon identity for the associator. -/
theorem pentagon (F : Hom S T) (G : Hom T U) (H : Hom U V)
    (I : Hom V W) :
    whiskerRight (eqToHom (Hom.assoc F G H)) I
        ≫ eqToHom (Hom.assoc F (G.comp H) I)
        ≫ whiskerLeft F (eqToHom (Hom.assoc G H I))
      = eqToHom (Hom.assoc (F.comp G) H I)
          ≫ eqToHom (Hom.assoc F G (H.comp I)) :=
  Hom₂.ext fun i ↦ by
    change W.compTotal (I.mapTotal ((eqToHom (Hom.assoc F G H)).app i))
        (W.compTotal ((eqToHom (Hom.assoc F (G.comp H) I)).app i)
          ((eqToHom (Hom.assoc G H I)).app (F.objMap i)))
      = W.compTotal ((eqToHom (Hom.assoc (F.comp G) H I)).app i)
          ((eqToHom (Hom.assoc F G (H.comp I))).app i)
    rw [eqToHom_app, eqToHom_app, eqToHom_app, eqToHom_app, eqToHom_app]
    exact (congrArg (fun y ↦ W.compTotal y _)
      (I.mapTotal_id (H.objMap (G.objMap (F.objMap i))))).trans (W.id_comp _)

/-- The triangle identity relating the associator and the unitors. -/
theorem triangle (F : Hom S T) (G : Hom T U) :
    eqToHom (Hom.assoc F (Hom.id T) G)
        ≫ whiskerLeft F (eqToHom (Hom.id_comp G))
      = whiskerRight (eqToHom (Hom.comp_id F)) G :=
  Hom₂.ext fun i ↦ by
    change U.compTotal ((eqToHom (Hom.assoc F (Hom.id T) G)).app i)
        ((eqToHom (Hom.id_comp G)).app (F.objMap i))
      = G.mapTotal ((eqToHom (Hom.comp_id F)).app i)
    rw [eqToHom_app, eqToHom_app, eqToHom_app]
    exact (U.comp_id (U.id (G.objMap (F.objMap i)))).trans (G.mapTotal_id (F.objMap i)).symm

end Hom₂

/-- The bicategory of finite-category specifications. -/
instance bicategory : Bicategory FinCat where
  Hom S T := Hom S T
  id S := Hom.id S
  comp F G := F.comp G
  homCategory _ _ := Hom.instCategory
  whiskerLeft := Hom₂.whiskerLeft
  whiskerRight := Hom₂.whiskerRight
  associator F G H := @eqToIso _ Hom.instCategory _ _ (Hom.assoc F G H)
  leftUnitor F := @eqToIso _ Hom.instCategory _ _ (Hom.id_comp F)
  rightUnitor F := @eqToIso _ Hom.instCategory _ _ (Hom.comp_id F)
  id_whiskerLeft := Hom₂.id_whiskerLeft
  comp_whiskerLeft := Hom₂.comp_whiskerLeft
  id_whiskerRight := Hom₂.id_whiskerRight
  comp_whiskerRight := Hom₂.comp_whiskerRight
  whiskerRight_id := Hom₂.whiskerRight_id
  whiskerRight_comp := Hom₂.whiskerRight_comp
  whisker_assoc := Hom₂.whisker_assoc
  whisker_exchange := Hom₂.whisker_exchange
  pentagon := Hom₂.pentagon
  triangle := Hom₂.triangle

/-- The bicategory of specifications is strict: 1-cell composition is
unital and associative on the nose. -/
instance bicategory_strict : Bicategory.Strict FinCat where
  id_comp := Hom.id_comp
  comp_id := Hom.comp_id
  assoc := Hom.assoc
  leftUnitor_eqToIso := fun _ ↦ rfl
  rightUnitor_eqToIso := fun _ ↦ rfl
  associator_eqToIso := fun _ _ _ ↦ rfl

/-- The category of finite-category specifications, from the strict
bicategory. Named rather than left to the anonymous priority-100
instance, following `CategoryTheory.Cat.category`. There are no
universe parameters to pin: `FinCat`, `FinCat.Hom` and `FinCat.Hom₂`
all live at `Type 0`. -/
instance category : Category FinCat := StrictBicategory.category FinCat

end FinCat

end CategoryTheory
