/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.Data.PFunctor.IndRec.Basic

/-!
# Functoriality of the IR interpretation

The functoriality content of Theorem 2.4 of
[GhaniNordvallForsbergMalatesta2015] (which attributes the theorem
to [DybjerSetzer2003]): the interpretation of an `IR` code, given by
the object map `IR.interpObj` and the morphism map `IR.interpMor`,
preserves identities and composition, so `⟦γ⟧` is a functor between
the free coproduct completions. The characterizing equations of
`IR.interpMor` at each code constructor follow from the
propositional computation rule `IR.rec_mk`.

## Main statements

* `IR.interpMor_mk` — the characterizing equation of `IR.interpMor`
  at `IR.mk`, with the per-constructor forms `IR.interpMor_iota`,
  `IR.interpMor_sigma`, and `IR.interpMor_delta`.
* `IR.interpMor_id` — preservation of identities
  ([GhaniNordvallForsbergMalatesta2015], Theorem 2.4).
* `IR.interpMor_comp` — preservation of composition
  ([GhaniNordvallForsbergMalatesta2015], Theorem 2.4).

## Implementation notes

The characterizing equations follow from the propositional
computation rule `IR.rec_mk`. The mathlib `Category`/`Functor`
packaging is deferred to a `Classical.choice`-enabled wrapper (see
`TODO.md`). The functor laws are `Prop`-valued and go through
`IR.induction` with the objects and morphisms quantified in the motive.
The composition law first eliminates the two morphism-commutation
equalities (nested `Eq.rec`s whose motives — `InterpMorCompHgMotive`
and `InterpMorCompHfMotive` — abstract a decoding together with its
commutation proof), so that at the base case every decoding factors
through the codomain decoding and the `homOfEq` transports in
`IR.interpMorDelta` reduce definitionally; both laws then reduce to
the functoriality of `FreeCoprodCompDisc.coprodMor`.

## References

* [DybjerSetzer2003]
* [GhaniNordvallForsbergMalatesta2015]

## Tags

inductive-recursive, interpretation, functor, free coproduct
completion
-/

@[expose] public section

universe uA uB uI uO w

namespace IndRec

open CategoryTheory

variable (I : Type uI) (O : Type uO)

namespace IR

/-- The characterizing equation of `IR.interpMor` at `IR.mk`: the
morphism map computes by one step of `IR.interpMorStep`
([GhaniNordvallForsbergMalatesta2015], Theorem 2.4). -/
theorem interpMor_mk (s : Shape O)
    (d : Direction I O s → IR.{uA, uB, uI, uO} I O) :
    interpMor I O (mk I O s d) =
      interpMorStep I O s d (fun x ↦ interpMor I O (d x)) :=
  rec_mk I O (interpMorStep I O) s d

/-- The characterizing equation of `IR.interpMor` at `IR.iota`
([GhaniNordvallForsbergMalatesta2015], Theorem 2.4). -/
theorem interpMor_iota (o : O) :
    interpMor.{uA, uB, uI, uO} I O (iota I O o) =
      interpMorIota.{uA, uB, uI, uO} I O o :=
  rec_mk I O (interpMorStep I O) (Sum.inl o) PEmpty.elim

/-- The characterizing equation of `IR.interpMor` at `IR.sigma`
([GhaniNordvallForsbergMalatesta2015], Theorem 2.4). -/
theorem interpMor_sigma (A : Type uA)
    (c : A → IR.{uA, uB, uI, uO} I O) :
    interpMor I O (sigma I O A c) =
      interpMorSigma I O A (fun a ↦ interpObj I O (c a))
        (fun a ↦ interpMor I O (c a)) :=
  rec_mk I O (interpMorStep I O) (Sum.inr (Sum.inl A)) (c ∘ ULift.down)

/-- The characterizing equation of `IR.interpMor` at `IR.delta`
([GhaniNordvallForsbergMalatesta2015], Theorem 2.4). -/
theorem interpMor_delta (B : Type uB)
    (c : (B → I) → IR.{uA, uB, uI, uO} I O) :
    interpMor I O (delta I O B c) =
      interpMorDelta I O B (fun f ↦ interpObj I O (c f))
        (fun f ↦ interpMor I O (c f)) :=
  rec_mk I O (interpMorStep I O) (Sum.inr (Sum.inr B)) (c ∘ ULift.down)

/-- The motive of the identity functor law: at every object, the
morphism map sends the identity to the identity. -/
def InterpMorIdMotive (γ : IR.{uA, uB, uI, uO} I O) : Prop :=
  ∀ X : FreeCoprodCompDisc.{max uA uB, uI} I,
    interpMor I O γ X X (FreeCoprodCompDisc.Hom.id I X) =
      FreeCoprodCompDisc.Hom.id O (interpObj I O γ X)

/-- The inductive step of the identity functor law: after the
characterizing equation `IR.interpMor_mk`, the `ι` case is
definitional and the `σ`/`δ` cases are the inductive hypotheses
followed by `FreeCoprodCompDisc.coprodMor_id` (the `δ`-case
`homOfEq` transport reduces definitionally at the identity, whose
commutation proof is reflexivity). -/
theorem interpMor_id_step :
    InductionStep.{uA, uB, uI, uO} I O (InterpMorIdMotive I O) :=
  fun s d ih X ↦
    (congrFun (congrFun (congrFun (interpMor_mk I O s d) X) X)
      (FreeCoprodCompDisc.Hom.id I X)).trans
      (match s, d, ih with
        | Sum.inl _, _, _ => rfl
        | Sum.inr (Sum.inl A), d, ih =>
            (congrArg
              (FreeCoprodCompDisc.coprodMor O A A _root_.id
                (fun a ↦ interpObj I O (d (ULift.up a)) X)
                (fun a ↦ interpObj I O (d (ULift.up a)) X))
              (funext (fun a ↦ ih (ULift.up a) X))).trans
              (FreeCoprodCompDisc.coprodMor_id O A
                (fun a ↦ interpObj I O (d (ULift.up a)) X))
        | Sum.inr (Sum.inr B), d, ih =>
            (congrArg
              (FreeCoprodCompDisc.coprodMor O (B → X.1) (B → X.1) _root_.id
                (fun g ↦ interpObj I O (d (ULift.up (X.2 ∘ g))) X)
                (fun g ↦ interpObj I O (d (ULift.up (X.2 ∘ g))) X))
              (funext (fun g ↦ ih (ULift.up (X.2 ∘ g)) X))).trans
              (FreeCoprodCompDisc.coprodMor_id O (B → X.1)
                (fun g ↦ interpObj I O (d (ULift.up (X.2 ∘ g))) X)))

/-- Preservation of identities by the interpretation
([GhaniNordvallForsbergMalatesta2015], Theorem 2.4). -/
theorem interpMor_id (γ : IR.{uA, uB, uI, uO} I O) :
    InterpMorIdMotive I O γ :=
  induction I O (InterpMorIdMotive I O) (interpMor_id_step I O) γ

/-- The motive of the composition functor law: at all objects and
morphisms, the morphism map sends a composite to the composite of
the images. -/
def InterpMorCompMotive (γ : IR.{uA, uB, uI, uO} I O) : Prop :=
  ∀ X Y Z : FreeCoprodCompDisc.{max uA uB, uI} I,
    ∀ f : FreeCoprodCompDisc.Hom I X Y,
      ∀ g : FreeCoprodCompDisc.Hom I Y Z,
        interpMor I O γ X Z (FreeCoprodCompDisc.Hom.comp I f g) =
          FreeCoprodCompDisc.Hom.comp O
            (interpMor I O γ X Y f) (interpMor I O γ Y Z g)

/-- The first morphism of the composition law's base case: every
decoding factors through the codomain decoding, and the commutation
proof is reflexivity. -/
def compBaseF (X1 Y1 Z1 : Type w) (Z2 : Z1 → I)
    (f1 : X1 → Y1) (g1 : Y1 → Z1) :
    FreeCoprodCompDisc.Hom I
      (⟨X1, Z2 ∘ g1 ∘ f1⟩ : FreeCoprodCompDisc.{w, uI} I)
      ⟨Y1, Z2 ∘ g1⟩ :=
  ⟨f1, rfl⟩

/-- The second morphism of the composition law's base case. -/
def compBaseG (Y1 Z1 : Type w) (Z2 : Z1 → I) (g1 : Y1 → Z1) :
    FreeCoprodCompDisc.Hom I
      (⟨Y1, Z2 ∘ g1⟩ : FreeCoprodCompDisc.{w, uI} I)
      ⟨Z1, Z2⟩ :=
  ⟨g1, rfl⟩

/-- The motive of the second (inner) equality elimination of the
composition law: the middle decoding is generalized together with
its commutation proof. -/
def InterpMorCompHgMotive (s : Shape O)
    (d : Direction I O s → IR.{uA, uB, uI, uO} I O)
    (X1 Y1 Z1 : Type (max uA uB)) (Z2 : Z1 → I)
    (f1 : X1 → Y1) (g1 : Y1 → Z1)
    (y2 : Y1 → I) (hg : Z2 ∘ g1 = y2) : Prop :=
  interpMor I O (mk I O s d) ⟨X1, y2 ∘ f1⟩ ⟨Z1, Z2⟩
      (FreeCoprodCompDisc.Hom.comp I (X := ⟨X1, y2 ∘ f1⟩)
        (Y := ⟨Y1, y2⟩) (Z := ⟨Z1, Z2⟩) ⟨f1, rfl⟩ ⟨g1, hg⟩) =
    FreeCoprodCompDisc.Hom.comp O
      (interpMor I O (mk I O s d) ⟨X1, y2 ∘ f1⟩ ⟨Y1, y2⟩ ⟨f1, rfl⟩)
      (interpMor I O (mk I O s d) ⟨Y1, y2⟩ ⟨Z1, Z2⟩ ⟨g1, hg⟩)

/-- The motive of the first (outer) equality elimination of the
composition law: the domain decoding is generalized together with
its commutation proof. -/
def InterpMorCompHfMotive (s : Shape O)
    (d : Direction I O s → IR.{uA, uB, uI, uO} I O)
    (X1 Y1 Z1 : Type (max uA uB)) (Y2 : Y1 → I) (Z2 : Z1 → I)
    (f1 : X1 → Y1) (g1 : Y1 → Z1) (hg : Z2 ∘ g1 = Y2)
    (x2 : X1 → I) (hf : Y2 ∘ f1 = x2) : Prop :=
  interpMor I O (mk I O s d) ⟨X1, x2⟩ ⟨Z1, Z2⟩
      (FreeCoprodCompDisc.Hom.comp I (X := ⟨X1, x2⟩)
        (Y := ⟨Y1, Y2⟩) (Z := ⟨Z1, Z2⟩) ⟨f1, hf⟩ ⟨g1, hg⟩) =
    FreeCoprodCompDisc.Hom.comp O
      (interpMor I O (mk I O s d) ⟨X1, x2⟩ ⟨Y1, Y2⟩ ⟨f1, hf⟩)
      (interpMor I O (mk I O s d) ⟨Y1, Y2⟩ ⟨Z1, Z2⟩ ⟨g1, hg⟩)

/-- The shape dispatch of the composition law's base case, at the
level of `IR.interpMorStep`: the `ι` case is definitional, and the
`σ`/`δ` cases are the inductive hypotheses followed by
`FreeCoprodCompDisc.coprodMor_comp` (at the base objects every
`homOfEq` transport reduces definitionally). -/
theorem interpMorStep_comp (s : Shape O)
    (d : Direction I O s → IR.{uA, uB, uI, uO} I O)
    (X1 Y1 Z1 : Type (max uA uB)) (Z2 : Z1 → I)
    (f1 : X1 → Y1) (g1 : Y1 → Z1)
    (ih : (x : Direction I O s) → InterpMorCompMotive I O (d x)) :
    interpMorStep I O s d (fun x ↦ interpMor I O (d x))
        ⟨X1, Z2 ∘ g1 ∘ f1⟩ ⟨Z1, Z2⟩
        (FreeCoprodCompDisc.Hom.comp I
          (compBaseF I X1 Y1 Z1 Z2 f1 g1) (compBaseG I Y1 Z1 Z2 g1)) =
      FreeCoprodCompDisc.Hom.comp O
        (interpMorStep I O s d (fun x ↦ interpMor I O (d x))
          ⟨X1, Z2 ∘ g1 ∘ f1⟩ ⟨Y1, Z2 ∘ g1⟩
          (compBaseF I X1 Y1 Z1 Z2 f1 g1))
        (interpMorStep I O s d (fun x ↦ interpMor I O (d x))
          ⟨Y1, Z2 ∘ g1⟩ ⟨Z1, Z2⟩
          (compBaseG I Y1 Z1 Z2 g1)) :=
  match s, d, ih with
  | Sum.inl _, _, _ => rfl
  | Sum.inr (Sum.inl A), d, ih =>
      Eq.trans
        (congrArg
          (FreeCoprodCompDisc.coprodMor O A A _root_.id
            (fun a ↦ interpObj I O (d (ULift.up a)) ⟨X1, Z2 ∘ g1 ∘ f1⟩)
            (fun a ↦ interpObj I O (d (ULift.up a)) ⟨Z1, Z2⟩))
          (funext (fun a ↦
            ih (ULift.up a) ⟨X1, Z2 ∘ g1 ∘ f1⟩ ⟨Y1, Z2 ∘ g1⟩ ⟨Z1, Z2⟩
              (compBaseF I X1 Y1 Z1 Z2 f1 g1)
              (compBaseG I Y1 Z1 Z2 g1))))
        (Eq.symm
          (FreeCoprodCompDisc.coprodMor_comp O A A A _root_.id _root_.id
            (fun a ↦ interpObj I O (d (ULift.up a)) ⟨X1, Z2 ∘ g1 ∘ f1⟩)
            (fun a ↦ interpObj I O (d (ULift.up a)) ⟨Y1, Z2 ∘ g1⟩)
            (fun a ↦ interpObj I O (d (ULift.up a)) ⟨Z1, Z2⟩)
            (fun a ↦ interpMor I O (d (ULift.up a))
              ⟨X1, Z2 ∘ g1 ∘ f1⟩ ⟨Y1, Z2 ∘ g1⟩
              (compBaseF I X1 Y1 Z1 Z2 f1 g1))
            (fun a ↦ interpMor I O (d (ULift.up a))
              ⟨Y1, Z2 ∘ g1⟩ ⟨Z1, Z2⟩
              (compBaseG I Y1 Z1 Z2 g1))))
  | Sum.inr (Sum.inr B), d, ih =>
      Eq.trans
        (congrArg
          (FreeCoprodCompDisc.coprodMor O (B → X1) (B → Z1)
            (fun q ↦ g1 ∘ f1 ∘ q)
            (fun q ↦ interpObj I O
              (d (ULift.up (Z2 ∘ g1 ∘ f1 ∘ q))) ⟨X1, Z2 ∘ g1 ∘ f1⟩)
            (fun q ↦ interpObj I O
              (d (ULift.up (Z2 ∘ q))) ⟨Z1, Z2⟩))
          (funext (fun q ↦
            ih (ULift.up (Z2 ∘ g1 ∘ f1 ∘ q))
              ⟨X1, Z2 ∘ g1 ∘ f1⟩ ⟨Y1, Z2 ∘ g1⟩ ⟨Z1, Z2⟩
              (compBaseF I X1 Y1 Z1 Z2 f1 g1)
              (compBaseG I Y1 Z1 Z2 g1))))
        (Eq.symm
          (FreeCoprodCompDisc.coprodMor_comp O
            (B → X1) (B → Y1) (B → Z1)
            (fun q ↦ f1 ∘ q) (fun q ↦ g1 ∘ q)
            (fun q ↦ interpObj I O
              (d (ULift.up (Z2 ∘ g1 ∘ f1 ∘ q))) ⟨X1, Z2 ∘ g1 ∘ f1⟩)
            (fun q ↦ interpObj I O
              (d (ULift.up (Z2 ∘ g1 ∘ q))) ⟨Y1, Z2 ∘ g1⟩)
            (fun q ↦ interpObj I O
              (d (ULift.up (Z2 ∘ q))) ⟨Z1, Z2⟩)
            (fun q ↦ interpMor I O (d (ULift.up (Z2 ∘ g1 ∘ f1 ∘ q)))
              ⟨X1, Z2 ∘ g1 ∘ f1⟩ ⟨Y1, Z2 ∘ g1⟩
              (compBaseF I X1 Y1 Z1 Z2 f1 g1))
            (fun q ↦ interpMor I O (d (ULift.up (Z2 ∘ g1 ∘ q)))
              ⟨Y1, Z2 ∘ g1⟩ ⟨Z1, Z2⟩
              (compBaseG I Y1 Z1 Z2 g1))))

/-- The composition law's base case: `InterpMorCompHgMotive` at the
factored middle decoding and reflexivity, by the characterizing
equation `IR.interpMor_mk` on both sides of `interpMorStep_comp`. -/
theorem interpMor_comp_base (s : Shape O)
    (d : Direction I O s → IR.{uA, uB, uI, uO} I O)
    (X1 Y1 Z1 : Type (max uA uB)) (Z2 : Z1 → I)
    (f1 : X1 → Y1) (g1 : Y1 → Z1)
    (ih : (x : Direction I O s) → InterpMorCompMotive I O (d x)) :
    InterpMorCompHgMotive I O s d X1 Y1 Z1 Z2 f1 g1 (Z2 ∘ g1) rfl :=
  Eq.trans
    (congrFun (congrFun (congrFun (interpMor_mk I O s d)
      ⟨X1, Z2 ∘ g1 ∘ f1⟩) ⟨Z1, Z2⟩)
      (FreeCoprodCompDisc.Hom.comp I
        (compBaseF I X1 Y1 Z1 Z2 f1 g1) (compBaseG I Y1 Z1 Z2 g1)))
    (Eq.trans
      (interpMorStep_comp I O s d X1 Y1 Z1 Z2 f1 g1 ih)
      (Eq.symm
        (congrArg₂ (FreeCoprodCompDisc.Hom.comp O)
          (congrFun (congrFun (congrFun (interpMor_mk I O s d)
            ⟨X1, Z2 ∘ g1 ∘ f1⟩) ⟨Y1, Z2 ∘ g1⟩)
            (compBaseF I X1 Y1 Z1 Z2 f1 g1))
          (congrFun (congrFun (congrFun (interpMor_mk I O s d)
            ⟨Y1, Z2 ∘ g1⟩) ⟨Z1, Z2⟩)
            (compBaseG I Y1 Z1 Z2 g1)))))

/-- The inductive step of the composition functor law: destructure
the objects and morphisms, then eliminate the two commutation
equalities into the base case `IR.interpMor_comp_base`. -/
theorem interpMor_comp_step :
    InductionStep.{uA, uB, uI, uO} I O (InterpMorCompMotive I O) :=
  fun s d ih X Y Z f g ↦
    match X, Y, Z, f, g with
    | ⟨X1, _X2⟩, ⟨Y1, Y2⟩, ⟨Z1, Z2⟩, ⟨f1, hf⟩, ⟨g1, hg⟩ =>
      Eq.rec
        (motive := fun x2 hf' ↦
          InterpMorCompHfMotive I O s d X1 Y1 Z1 Y2 Z2 f1 g1 hg x2 hf')
        (Eq.rec
          (motive := fun y2 hg' ↦
            InterpMorCompHgMotive I O s d X1 Y1 Z1 Z2 f1 g1 y2 hg')
          (interpMor_comp_base I O s d X1 Y1 Z1 Z2 f1 g1 ih)
          hg)
        hf

/-- Preservation of composition by the interpretation
([GhaniNordvallForsbergMalatesta2015], Theorem 2.4). -/
theorem interpMor_comp (γ : IR.{uA, uB, uI, uO} I O) :
    InterpMorCompMotive I O γ :=
  induction I O (InterpMorCompMotive I O) (interpMor_comp_step I O) γ

end IR

end IndRec
