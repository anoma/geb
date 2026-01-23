import GebLean.Weighted
import GebLean.ParanatAlg
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Functor.Currying

/-!
# Mendler-Lambek Correspondence via Restricted Coends

This module implements the correspondence between Mendler-style algebras
and conventional (Lambek) algebras for difunctors, following Vene's thesis
"Categorical Programming with Inductive and Coinductive Types" (sections
5.3-5.7).

## Overview

For an endodifunctor `G : Cᵒᵖ ⥤ C ⥤ C`:

- A **Mendler-style G-algebra** is a pair `(pt, Φ)` where `pt : C` and
  `Φ : HomToProf pt → G ⇓ pt` is a dinatural transformation. Concretely,
  for each `A`, we have `Φ_A : (A ⟶ pt) → (G(A,A) ⟶ pt)`.

- A **conventional G^e-algebra** is a pair `(pt, φ)` where
  `φ : G^e(pt) ⟶ pt` and `G^e` is defined via restricted coends.

The main result is that the categories of Mendler-style G-algebras and
conventional G^e-algebras are isomorphic (Theorem 5.19 in Vene).

## Definitions

- `HomToProf pt`: The profunctor `(A, B) ↦ (A ⟶ pt)`, constant in `B`
- `MendlerAlgebra G`: Mendler-style algebra for difunctor `G`
- The equivalence between `MendlerAlgebra G` and `RestrictedCowedge G (HomToProf pt)`

## References

* Vene, "Categorical Programming with Inductive and Coinductive Types"
-/

namespace GebLean

open CategoryTheory Limits Opposite

universe u v

variable {C : Type u} [Category.{v} C]

section HomToProfunctor

/-!
## The Hom-To Profunctor

For a fixed object `pt : C`, define the profunctor `HomToProf pt : Cᵒᵖ ⥤ C ⥤ Type v`
where `(HomToProf pt)(A, B) = (A ⟶ pt)`.

This is constant in the second argument and contravariant in the first via
precomposition. A diagonal element at `A` is a morphism `A ⟶ pt`.

This corresponds to Vene's "Id^i/C" (identity restricted to C) profunctor.
-/

/-- The profunctor `HomToProf pt` sends `(A, B)` to `(A ⟶ pt)`.
Contravariant in `A` via precomposition, constant in `B`.

Constructed as the currying of `(Prod.fst Cᵒᵖ C) ⋙ (yoneda.obj pt)`:
- `Prod.fst` projects out the first component
- `yoneda.obj pt` gives the representable presheaf Hom(-, pt)
- Currying converts from `Cᵒᵖ × C ⥤ Type v` to `Cᵒᵖ ⥤ C ⥤ Type v`

This corresponds to Vene's "Id^i/C" (identity restricted to C) profunctor. -/
def HomToProf (pt : C) : Cᵒᵖ ⥤ C ⥤ Type v :=
  Functor.curry.obj (CategoryTheory.Prod.fst Cᵒᵖ C ⋙ yoneda.obj pt)

/-- The object at `(A, B)` in `HomToProf pt` is `(A.unop ⟶ pt)`. -/
@[simp]
theorem HomToProf_obj_obj (pt : C) (A : Cᵒᵖ) (B : C) :
    ((HomToProf pt).obj A).obj B = (A.unop ⟶ pt) := by
  simp only [HomToProf, Functor.curry_obj_obj_obj, Functor.comp_obj,
             CategoryTheory.Prod.fst_obj, yoneda_obj_obj]

/-- The diagonal of `HomToProf pt` at `A` is the hom-set `(A ⟶ pt)`. -/
theorem HomToProf_diag (pt A : C) :
    diagApp (HomToProf pt) A = (A ⟶ pt) := by
  simp only [diagApp, HomToProf_obj_obj]

/-- The map in the first (contravariant) argument: precomposition. -/
@[simp]
theorem HomToProf_map_app (pt : C) {A₁ A₂ : Cᵒᵖ} (f : A₁ ⟶ A₂) (B : C)
    (h : A₁.unop ⟶ pt) :
    ((HomToProf pt).map f).app B h = f.unop ≫ h := by
  simp only [HomToProf, Functor.curry_obj_map_app, Functor.comp_map,
             CategoryTheory.Prod.fst_map, yoneda_obj_map]

/-- The map in the second (covariant) argument is identity. -/
@[simp]
theorem HomToProf_obj_map (pt : C) (A : Cᵒᵖ) {B₁ B₂ : C} (g : B₁ ⟶ B₂)
    (h : A.unop ⟶ pt) :
    ((HomToProf pt).obj A).map g h = h := by
  simp only [HomToProf, Functor.curry_obj_obj_map, Functor.comp_map,
             CategoryTheory.Prod.fst_map, yoneda_obj_map]
  simp [Category.id_comp]

/-- Left action (contravariant): precomposition with `f`. -/
theorem HomToProf_lmap (pt : C) {A B : C} (f : A ⟶ B)
    (h : diagApp (HomToProf pt) B) :
    Profunctor.lmap (HomToProf pt) f h = f ≫ h := by
  simp only [Profunctor.lmap, HomToProf_map_app]
  rfl

/-- Right action (covariant): identity (constant in second argument). -/
theorem HomToProf_rmap (pt : C) {A B : C} (f : A ⟶ B)
    (h : diagApp (HomToProf pt) A) :
    Profunctor.rmap (HomToProf pt) f h = h := by
  simp only [Profunctor.rmap, HomToProf_obj_map]

/-- `HomToProf pt` equals `IdProf ⇓ pt` (the identity profunctor sliced over pt).

This formalizes the connection to Vene's "Id^i/C" notation: the profunctor
sending `(A, B)` to `(A ⟶ pt)` is exactly the slice of the identity
endodifunctor over `pt`. Both are constant in the second argument and
contravariant (via precomposition) in the first. -/
theorem HomToProf_eq_sliceIdProf (pt : C) : HomToProf pt = IdProf ⇓ pt := by
  apply CategoryTheory.Functor.ext
  case h_obj =>
    intro A
    apply CategoryTheory.Functor.ext
    case h_obj => intro B; rfl
    case h_map =>
      intro B₁ B₂ g
      simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
      ext h
      simp only [HomToProf_obj_map, sliceProfunctor_obj_map, IdProf, Functor.const_obj_obj,
        Functor.const_obj_map, NatTrans.id_app, Category.id_comp]
  case h_map =>
    intro A₁ A₂ f
    ext B h
    simp only [NatTrans.comp_app, types_comp_apply, eqToHom_app, eqToHom_refl, types_id_apply,
      HomToProf_map_app, sliceProfunctor_map_app, IdProf, Functor.const_obj_obj,
      Functor.id_obj, Functor.id_map]

end HomToProfunctor

section MendlerAlgebra

/-!
## Mendler-Style Algebras for Difunctors

A Mendler-style G-algebra for an endodifunctor `G : Cᵒᵖ ⥤ C ⥤ C` is a pair
`(pt, Φ)` where:
- `pt : C` is the carrier object
- `Φ` is a dinatural transformation from `HomToProf pt` to `G ⇓ pt`

Concretely, `Φ` is a family `{Φ_A}_{A : C}` of functions:
  `Φ_A : (A ⟶ pt) → (G(A, A) ⟶ pt)`
satisfying the dinaturality condition: for `g : A ⟶ B` and `β : B ⟶ pt`:
  `Φ_A(β ∘ g) ∘ G(g, id) = Φ_B(β) ∘ G(id, g)`
-/

variable (G : Cᵒᵖ ⥤ C ⥤ C)

/-- A Mendler-style algebra for an endodifunctor `G` over a fixed carrier `pt`.
This contains the algebra data without bundling the carrier object. -/
@[ext]
structure MendlerAlgebraOver (pt : C) where
  /-- The cowedge data over the carrier. -/
  toRestrictedCowedgeOver : RestrictedCowedgeOver pt G (HomToProf pt)

namespace MendlerAlgebraOver

variable {G}

/-- The family of algebra operations. -/
abbrev family {pt : C} (m : MendlerAlgebraOver G pt) :
    ParanatSig (HomToProf pt) (G ⇓ pt) :=
  m.toRestrictedCowedgeOver.family

/-- The dinaturality condition. -/
abbrev isDinatural {pt : C} (m : MendlerAlgebraOver G pt) :
    IsDinatural (HomToProf pt) (G ⇓ pt) m.family :=
  m.toRestrictedCowedgeOver.isDinatural

/-- Constructor with explicit family and dinaturality arguments. -/
@[match_pattern]
def mk' (pt : C) (family : ParanatSig (HomToProf pt) (G ⇓ pt))
    (isDinatural : IsDinatural (HomToProf pt) (G ⇓ pt) family) :
    MendlerAlgebraOver G pt :=
  ⟨⟨family, isDinatural⟩⟩

end MendlerAlgebraOver

/-- A Mendler-style algebra for an endodifunctor `G`. -/
@[ext]
structure MendlerAlgebra where
  /-- The carrier object. -/
  pt : C
  /-- The algebra data over the carrier. -/
  toMendlerAlgebraOver : MendlerAlgebraOver G pt

namespace MendlerAlgebra

variable {G}

/-- The family of algebra operations. -/
abbrev family (m : MendlerAlgebra G) : ParanatSig (HomToProf m.pt) (G ⇓ m.pt) :=
  m.toMendlerAlgebraOver.family

/-- The dinaturality condition. -/
abbrev isDinatural (m : MendlerAlgebra G) :
    IsDinatural (HomToProf m.pt) (G ⇓ m.pt) m.family :=
  m.toMendlerAlgebraOver.isDinatural

/-- The underlying RestrictedCowedgeOver. -/
abbrev toRestrictedCowedgeOver (m : MendlerAlgebra G) :
    RestrictedCowedgeOver m.pt G (HomToProf m.pt) :=
  m.toMendlerAlgebraOver.toRestrictedCowedgeOver

/-- Constructor with explicit family and dinaturality arguments. -/
@[match_pattern]
def mk' (pt : C) (family : ParanatSig (HomToProf pt) (G ⇓ pt))
    (isDinatural : IsDinatural (HomToProf pt) (G ⇓ pt) family) : MendlerAlgebra G :=
  ⟨pt, ⟨⟨family, isDinatural⟩⟩⟩

/-- The algebra operation at object `A`: given `γ : A ⟶ pt`, produce
`G(A, A) ⟶ pt`. -/
def algOp (m : MendlerAlgebra G) (A : C) (γ : A ⟶ m.pt) :
    (G.obj (Opposite.op A)).obj A ⟶ m.pt :=
  m.family A γ

/-- The explicit dinaturality condition: for `g : A ⟶ B` and `β : B ⟶ pt`,
the two paths from `G(B, A)` to `pt` agree:
  `G(g, id) ≫ Φ_A(β ∘ g) = G(id, g) ≫ Φ_B(β)` -/
theorem dinaturality (m : MendlerAlgebra G) {A B : C} (g : A ⟶ B)
    (β : B ⟶ m.pt) :
    (G.map g.op).app A ≫ m.family A (g ≫ β) =
    (G.obj (Opposite.op B)).map g ≫ m.family B β := by
  have dinat := m.isDinatural A B g β
  simp only [Profunctor.lmap, Profunctor.rmap, sliceProfunctor_obj_map,
    sliceProfunctor_map_app, HomToProf_map_app, HomToProf_obj_map,
    Quiver.Hom.unop_op] at dinat
  exact dinat.symm

/-- Convert a Mendler algebra to a restricted cowedge. -/
def toRestrictedCowedge (m : MendlerAlgebra G) :
    RestrictedCowedge G (HomToProf m.pt) where
  pt := m.pt
  toRestrictedCowedgeOver := ⟨m.family, m.isDinatural⟩

/-- Construct a Mendler algebra from a restricted cowedge with HomToProf pt
whose carrier is pt. -/
def ofRestrictedCowedge' (pt : C) (family : ParanatSig (HomToProf pt) (G ⇓ pt))
    (isDinatural : IsDinatural (HomToProf pt) (G ⇓ pt) family) : MendlerAlgebra G :=
  ⟨pt, ⟨⟨family, isDinatural⟩⟩⟩

/-- Construct a Mendler algebra from a point and a RestrictedCowedgeOver. -/
def ofRestrictedCowedgeOver (pt : C) (u : RestrictedCowedgeOver pt G (HomToProf pt)) :
    MendlerAlgebra G :=
  ⟨pt, ⟨u⟩⟩

/-- Construct a Mendler algebra from a point and a MendlerAlgebraOver. -/
def ofMendlerAlgebraOver (pt : C) (m : MendlerAlgebraOver G pt) : MendlerAlgebra G :=
  ⟨pt, m⟩

/-- Round-trip from MendlerAlgebra to MendlerAlgebraOver and back. -/
theorem ofMendlerAlgebraOver_toMendlerAlgebraOver (m : MendlerAlgebra G) :
    ofMendlerAlgebraOver m.pt m.toMendlerAlgebraOver = m := rfl

/-- Round-trip from MendlerAlgebraOver to MendlerAlgebra and back. -/
theorem toMendlerAlgebraOver_ofMendlerAlgebraOver (pt : C)
    (u : MendlerAlgebraOver G pt) :
    (ofMendlerAlgebraOver pt u).toMendlerAlgebraOver = u := rfl

/-- Round-trip from MendlerAlgebra to RestrictedCowedgeOver and back. -/
theorem ofRestrictedCowedgeOver_toRestrictedCowedgeOver (m : MendlerAlgebra G) :
    ofRestrictedCowedgeOver m.pt m.toRestrictedCowedgeOver = m := rfl

/-- Round-trip from RestrictedCowedgeOver to MendlerAlgebra and back. -/
theorem toRestrictedCowedgeOver_ofRestrictedCowedgeOver (pt : C)
    (u : RestrictedCowedgeOver pt G (HomToProf pt)) :
    (ofRestrictedCowedgeOver pt u).toRestrictedCowedgeOver = u := rfl

end MendlerAlgebra

/-- A morphism of Mendler algebras. -/
@[ext]
structure MendlerAlgebraHom {G : Cᵒᵖ ⥤ C ⥤ C} (m₁ m₂ : MendlerAlgebra G) where
  /-- The underlying morphism in C. -/
  hom : m₁.pt ⟶ m₂.pt
  /-- The compatibility condition: `h ∘ Φ_A(γ) = Ψ_A(h ∘ γ)`. -/
  comm : ∀ (A : C) (γ : A ⟶ m₁.pt),
    m₁.family A γ ≫ hom = m₂.family A (γ ≫ hom)

namespace MendlerAlgebraHom

variable {G : Cᵒᵖ ⥤ C ⥤ C}

/-- Identity morphism on a Mendler algebra. -/
@[simps]
def id (m : MendlerAlgebra G) : MendlerAlgebraHom m m where
  hom := 𝟙 m.pt
  comm _ _ := by simp

/-- Composition of Mendler algebra morphisms. -/
@[simps]
def comp {m₁ m₂ m₃ : MendlerAlgebra G}
    (f : MendlerAlgebraHom m₁ m₂) (g : MendlerAlgebraHom m₂ m₃) :
    MendlerAlgebraHom m₁ m₃ where
  hom := f.hom ≫ g.hom
  comm A γ := by
    rw [← Category.assoc, f.comm, g.comm]
    simp [Category.assoc]

end MendlerAlgebraHom

/-- The category of Mendler algebras for `G`. -/
instance MendlerAlgebraCat : Category (MendlerAlgebra G) where
  Hom := MendlerAlgebraHom
  id := MendlerAlgebraHom.id
  comp := MendlerAlgebraHom.comp
  id_comp _ := by ext; simp [MendlerAlgebraHom.comp, MendlerAlgebraHom.id]
  comp_id _ := by ext; simp [MendlerAlgebraHom.comp, MendlerAlgebraHom.id]
  assoc _ _ _ := by ext; simp [MendlerAlgebraHom.comp, Category.assoc]

end MendlerAlgebra

section MendlerRestrictedEquivalence

/-!
## Equivalence: Mendler Algebras and Restricted Cowedges

A Mendler algebra `(pt, Φ)` is exactly a `RestrictedCowedge G (HomToProf pt)`.
We establish this correspondence formally.

The relationship is:
- `MendlerAlgebra G` bundles the carrier `pt` with the algebra structure
- `RestrictedCowedge G H` has a fixed restriction profunctor `H`

For each `pt`, `MendlerAlgebra G` restricted to carrier `pt` is equivalent
to `RestrictedCowedge G (HomToProf pt)`.
-/

variable (G : Cᵒᵖ ⥤ C ⥤ C)

/-- A Mendler algebra determines a restricted cowedge with the HomToProf
profunctor for its carrier. -/
def mendlerToRestrictedCowedge (m : MendlerAlgebra G) :
    RestrictedCowedge G (HomToProf m.pt) :=
  m.toRestrictedCowedge

/-- A restricted cowedge with HomToProf pt whose carrier equals pt determines
a Mendler algebra. We use `Eq.rec` on `hpt.symm` to transport from
`HomToProf pt` to `HomToProf rc.pt`, aligning both profunctor arguments
with the carrier. -/
def restrictedCowedgeToMendler (pt : C) (rc : RestrictedCowedge G (HomToProf pt))
    (hpt : rc.pt = pt) : MendlerAlgebra G where
  pt := rc.pt
  toMendlerAlgebraOver := ⟨⟨
    Eq.rec (motive := fun x _ => ParanatSig (HomToProf x) (G ⇓ rc.pt))
      rc.family hpt.symm,
    Eq.rec (motive := fun x h =>
        IsDinatural (HomToProf x) (G ⇓ rc.pt)
          (Eq.rec (motive := fun y _ => ParanatSig (HomToProf y) (G ⇓ rc.pt))
            rc.family h))
      rc.isDinatural hpt.symm⟩⟩

/-- For a Mendler algebra, converting to restricted cowedge and back
preserves the structure. -/
theorem mendler_restrictedCowedge_roundtrip (m : MendlerAlgebra G) :
    restrictedCowedgeToMendler G m.pt (mendlerToRestrictedCowedge G m) rfl = m := by
  cases m with | mk pt u => cases u with | mk r => cases r with | mk fam dinat => rfl

end MendlerRestrictedEquivalence

section WeightedCowedgeCorrespondence

/-!
## WeightedCowedge Correspondence for HomToProf

For the weight profunctor `H = HomToProf pt`, the categories of weighted
cowedges and restricted cowedges are equivalent. This is because the
weight at any co-twisted arrow `(arr : cod ⟶ dom)` is `cod ⟶ pt`, which
depends only on the codomain (source) of the co-twisted arrow.

The weighted cocone naturality condition forces off-diagonal legs to be
uniquely determined by diagonal legs. For a morphism
`m : coTwObjMk arr ⟶ idCoTwistedArrow cod` in CoTwistedArrow:

  D.map m ≫ c.leg (id_{cod}) w = c.leg (coTwObjMk arr) (W.map m.op w)

Since `HomToProf pt` is constant in the covariant position, `W.map m.op`
is identity, so:

  c.leg (coTwObjMk arr) γ = D.map m ≫ c.leg (id_{cod}) γ
                         = (G.map arr.op).app cod ≫ family cod γ

Thus every `RestrictedCowedge G (HomToProf pt)` extends uniquely to a
`WeightedCowedge (HomToProf pt) G`, and vice versa.
-/

variable (G : Cᵒᵖ ⥤ C ⥤ C)

/-- A weighted Mendler cowedge is a WeightedCowedge with weight HomToProf pt
and diagram G. -/
abbrev WeightedMendlerCowedge (pt : C) := WeightedCowedge (HomToProf pt) G

/-!
### Extension from RestrictedCowedge to WeightedCowedge

Given a restricted cowedge with `family : A → (A ⟶ pt) → (G(A,A) ⟶ rc.pt)`,
we extend to all co-twisted arrows via:

  extendLeg (arr : cod ⟶ dom) (γ : cod ⟶ pt) := (G.map arr.op).app cod ≫ family cod γ
-/

/-- The extended leg at an arbitrary co-twisted arrow, computed from
diagonal family data. For `(arr : cod ⟶ dom)` with weight `γ : cod ⟶ pt`,
this is `(G.map arr.op).app cod ≫ family cod γ : G(dom, cod) ⟶ pt`. -/
def extendMendlerLeg (pt : C) (rc : RestrictedCowedgeOver pt G (HomToProf pt))
    (tw : CoTwistedArrow C) :
    (profunctorOnOpCoTwistedArrow C (HomToProf pt)).obj (Opposite.op tw) →
    ((profunctorOnCoTwistedArrow C G).obj tw ⟶ pt) := fun w =>
  let cod := coTwCod tw
  let dom := coTwDom tw
  let arr := coTwArr tw
  have hWeight : (profunctorOnOpCoTwistedArrow C (HomToProf pt)).obj (Opposite.op tw) =
      (cod ⟶ pt) := profunctorOnOpCoTwistedArrow_at_arrow (HomToProf pt) arr
  let γ : cod ⟶ pt := cast hWeight w
  have hSlice : diagApp (G ⇓ pt) cod = ((G.obj (Opposite.op cod)).obj cod ⟶ pt) :=
    sliceProfunctor_obj_obj G pt (Opposite.op cod) cod
  let leg_at_cod : (G.obj (Opposite.op cod)).obj cod ⟶ pt :=
    cast hSlice (rc.family cod (cast (HomToProf_diag pt cod) γ))
  have hDom : (G.obj (Opposite.op dom)).obj cod =
      (profunctorOnCoTwistedArrow C G).obj tw := rfl
  eqToHom hDom ≫ (G.map arr.op).app cod ≫ leg_at_cod

/-- For HomToProf, the weight at any co-twisted arrow depends only on the
codomain (source in C). -/
theorem HomToProf_weight_at_coTw (pt : C) (tw : CoTwistedArrow C) :
    (profunctorOnOpCoTwistedArrow C (HomToProf pt)).obj (Opposite.op tw) =
    (coTwCod tw ⟶ pt) :=
  profunctorOnOpCoTwistedArrow_at_arrow (HomToProf pt) (coTwArr tw)

/-- For HomToProf, the weight map along a CoTwistedArrow morphism is
precomposition by the codomain arrow component. This is because HomToProf
is constant in its covariant position. -/
theorem HomToProf_weight_map_eq (pt : C) {tw tw' : CoTwistedArrow C}
    (f : tw ⟶ tw') (w : coTwCod tw' ⟶ pt) :
    cast (HomToProf_weight_at_coTw pt tw)
      ((profunctorOnOpCoTwistedArrow C (HomToProf pt)).map f.op
        (cast (HomToProf_weight_at_coTw pt tw').symm w)) =
    coTwCodArr f ≫ w := by
  simp only [profunctorOnOpCoTwistedArrow_map, profunctorOnTwistedArrow_map]
  simp only [coTwistedArrowOpEquiv_map_twDomArr, coTwistedArrowOpEquiv_map_twCodArr]
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  -- The types are definitionally equal, so we can use congrArg
  have hCod : twCod (coTwistedArrowOpEquivTwistedArrow.functor.obj (op tw')) =
              coTwDom tw' := coTwistedArrowOpEquiv_obj_cod tw'
  have hDom : twDom (coTwistedArrowOpEquivTwistedArrow.functor.obj (op tw)) =
              coTwCod tw := coTwistedArrowOpEquiv_obj_dom tw
  -- Rewrite using the weight definition to get the cast chain
  simp only [cast_eq]
  -- Now simplify the HomToProf behavior
  change (((HomToProf pt).map (coTwCodArr f).op).app _ ≫
          ((HomToProf pt).obj _).map (coTwDomArr f)) w = coTwCodArr f ≫ w
  -- Expand the composition in Type
  change ((HomToProf pt).obj (op (coTwCod tw))).map (coTwDomArr f)
       (((HomToProf pt).map (coTwCodArr f).op).app (coTwDom tw') w) =
       coTwCodArr f ≫ w
  -- HomToProf_obj_map: ((HomToProf pt).obj A).map g h = h
  rw [HomToProf_obj_map]
  -- Now the goal is: ((HomToProf pt).map (coTwCodArr f).op).app (coTwDom tw') w = coTwCodArr f ≫ w
  -- HomToProf_map_app: ((HomToProf pt).map f).app B h = f.unop ≫ h
  rw [HomToProf_map_app, Quiver.Hom.unop_op]

/-!
### Naturality of the extension

The extended legs satisfy weighted cocone naturality. For a morphism
`f : tw ⟶ tw'` in CoTwistedArrow C:

  (profunctorOnCoTwistedArrow C G).map f ≫ extendMendlerLeg tw' w
    = extendMendlerLeg tw (weight.map f.op w)

The proof relies on:
1. For HomToProf, weight transport along `f.op` is precomposition by `coTwCodArr f`
   (proven in `HomToProf_weight_map_eq`)
2. The co-twisted arrow commutator:
   `coTwCodArr f ≫ coTwArr tw' ≫ coTwDomArr f = coTwArr tw`
3. The dinaturality of the restricted cowedge
-/

/-- For HomToProf, the weight map along a CoTwistedArrow morphism equals
precomposition by coTwCodArr f. This is a direct computation without casts. -/
theorem HomToProf_weight_map_eq' (pt : C) {tw tw' : CoTwistedArrow C}
    (f : tw ⟶ tw') (γ : coTwCod tw' ⟶ pt) :
    (profunctorOnOpCoTwistedArrow C (HomToProf pt)).map f.op γ =
    coTwCodArr f ≫ γ := by
  simp only [profunctorOnOpCoTwistedArrow_map, profunctorOnTwistedArrow_map]
  simp only [coTwistedArrowOpEquiv_map_twDomArr, coTwistedArrowOpEquiv_map_twCodArr]
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  -- The composition in Type v is function composition
  simp only [types_comp_apply]
  rw [HomToProf_obj_map, HomToProf_map_app, Quiver.Hom.unop_op]

/-- The extended legs satisfy weighted cocone naturality. -/
theorem extendMendlerLeg_natural (pt : C) (rc : RestrictedCowedgeOver pt G (HomToProf pt))
    {tw tw' : CoTwistedArrow C} (f : tw ⟶ tw')
    (w' : (profunctorOnOpCoTwistedArrow C (HomToProf pt)).obj (Opposite.op tw')) :
    (profunctorOnCoTwistedArrow C G).map f ≫ extendMendlerLeg (G := G) pt rc tw' w' =
    extendMendlerLeg (G := G) pt rc tw
      ((profunctorOnOpCoTwistedArrow C (HomToProf pt)).map f.op w') := by
  -- Unfold the extended legs and diagram map
  unfold extendMendlerLeg
  rw [profunctorOnCoTwistedArrow_map]
  -- Simplify and normalize - eliminate eqToHom casts and let bindings
  simp only [eqToHom_refl, Category.id_comp, Category.assoc, cast_eq]
  -- Use the weight transport lemma on the RHS
  rw [HomToProf_weight_map_eq' pt f]
  -- The goal is now about rc.family at different positions
  -- Use the co-twisted arrow commutator: coTwCodArr f ≫ coTwArr tw' ≫ coTwDomArr f = coTwArr tw
  have comm := coTwHomComm f
  rw [← comm]
  simp only [op_comp, Functor.map_comp, NatTrans.comp_app, Category.assoc]
  -- Use naturality of G.map (coTwArr tw') - it's a natural transformation
  have nat_arr := (G.map (coTwArr tw').op).naturality (coTwCodArr f)
  -- Goal: (G.map domArr).app cod ≫ G.obj.map codArr ≫ (G.map arr').app cod' ≫ family
  --     = (G.map domArr).app cod ≫ (G.map arr').app cod ≫ (G.map codArr).app cod ≫ family
  -- First use congr to match the first morphism
  congr 1
  -- Now goal: G.obj.map codArr ≫ (G.map arr').app cod' ≫ family w'
  --         = (G.map arr').app cod ≫ (G.map codArr).app cod ≫ family (codArr ≫ w')
  -- Use naturality of G.map (coTwArr tw') to swap
  calc (G.obj (op (coTwDom tw'))).map (coTwCodArr f) ≫
       (G.map (coTwArr tw').op).app (coTwCod tw') ≫ rc.family (coTwCod tw') w'
    = (G.map (coTwArr tw').op).app (coTwCod tw) ≫
      (G.obj (op (coTwCod tw'))).map (coTwCodArr f) ≫ rc.family (coTwCod tw') w' := by
        rw [← Category.assoc, nat_arr, Category.assoc]
  _ = (G.map (coTwArr tw').op).app (coTwCod tw) ≫
      (G.map (coTwCodArr f).op).app (coTwCod tw) ≫ rc.family (coTwCod tw) (coTwCodArr f ≫ w') := by
        congr 1
        -- Use dinaturality of rc.family with g = coTwCodArr f
        have dinat := rc.isDinatural (coTwCod tw) (coTwCod tw') (coTwCodArr f) w'
        simp only [Profunctor.lmap, Profunctor.rmap, sliceProfunctor_obj_map,
          sliceProfunctor_map_app, Quiver.Hom.unop_op, HomToProf_map_app,
          HomToProf_obj_map] at dinat
        exact dinat

/-- Extends a restricted cowedge to a weighted cowedge over the same point.
This is the inverse direction of `restrictWeightedCowedge` for `HomToProf`. -/
def extendRestrictedCowedge (pt : C) (rc : RestrictedCowedgeOver pt G (HomToProf pt)) :
    WeightedCowedgeOver pt (HomToProf pt) G where
  ι := {
    app := fun tw => extendMendlerLeg (G := G) pt rc tw.unop
    naturality := fun tw tw' f => by
      ext w
      simp only [types_comp_apply]
      -- f : tw ⟶ tw' in (CoTwistedArrow C)ᵒᵖ
      -- f.unop : tw'.unop ⟶ tw.unop in CoTwistedArrow C
      -- extendMendlerLeg_natural gives:
      --   D.map f.unop ≫ leg (tw.unop) w = leg (tw'.unop) (W.map f w)
      -- homToFunctor.map f gives: D.map f.unop ≫ -
      -- So we need symm to get the right equation
      exact (extendMendlerLeg_natural (G := G) pt rc f.unop w).symm
  }

/-- Extends a restricted cowedge to a weighted cowedge (bundled with point). -/
def extendRestrictedCowedgeFull (pt : C)
    (rc : RestrictedCowedgeOver pt G (HomToProf pt)) :
    WeightedCowedge (HomToProf pt) G :=
  ⟨pt, extendRestrictedCowedge (G := G) pt rc⟩

/-- At an identity co-twisted arrow, the extended leg reduces to the original
family (up to canonical casts). -/
theorem extendMendlerLeg_at_identity (pt : C)
    (rc : RestrictedCowedgeOver pt G (HomToProf pt)) (A : C)
    (γ : (profunctorOnOpCoTwistedArrow C (HomToProf pt)).obj
      (Opposite.op (idCoTwistedArrow A))) :
    diagonalToIdentityHom G A ≫
      extendMendlerLeg (G := G) pt rc (idCoTwistedArrow A) γ =
    rc.family A (weightAtIdentityToDiagApp (HomToProf pt) A γ) := by
  unfold extendMendlerLeg idCoTwistedArrow
  simp only [coTwObjMk_arr, coTwObjMk_cod, coTwObjMk_dom]
  simp only [op_id, Functor.map_id, NatTrans.id_app]
  simp only [diagonalToIdentityHom, profunctorOnCoTwistedArrow_at_identity,
    eqToHom_refl, Category.id_comp]
  simp only [weightAtIdentityToDiagApp, cast_eq]
  exact Category.id_comp _

/-- The extend-restrict round-trip is the identity on RestrictedCowedgeOver. -/
theorem restrict_extend_roundtrip (pt : C)
    (rc : RestrictedCowedgeOver pt G (HomToProf pt)) :
    (restrictWeightedCowedge (HomToProf pt) G
      (extendRestrictedCowedgeFull (G := G) pt rc)).toRestrictedCowedgeOver = rc := by
  apply RestrictedCowedgeOver.ext
  funext A h
  simp only [restrictWeightedCowedge, weightedCowedgeFamilyAtIdentity,
    extendRestrictedCowedgeFull, extendRestrictedCowedge, WeightedCocone.leg]
  rw [extendMendlerLeg_at_identity (G := G)]
  simp only [weightAtIdentityToDiagApp_diagAppToWeightAtIdentity]

/-- The extended leg at any co-twisted arrow matches the original leg
when starting from a weighted cowedge. This follows from the uniqueness
of extension: the naturality condition forces the leg to be the
composition `(G.map arr.op).app cod ≫ family cod`. -/
-- Helper theorem for the canonical form where tw = coTwObjMk arr
theorem extendMendlerLeg_eq_original_leg_at_coTwObjMk (pt : C)
    (wc : WeightedCoconeOver pt (profunctorOnOpCoTwistedArrow C (HomToProf pt))
      (profunctorOnCoTwistedArrow C G))
    {cod dom : C} (arr : cod ⟶ dom)
    (γ : (profunctorOnOpCoTwistedArrow C (HomToProf pt)).obj
      (Opposite.op (coTwObjMk arr))) :
    let rc := (restrictWeightedCowedge (HomToProf pt) G
      ⟨pt, wc⟩).toRestrictedCowedgeOver
    extendMendlerLeg (G := G) pt rc (coTwObjMk arr) γ =
    wc.ι.app (Opposite.op (coTwObjMk arr)) γ := by
  intro rc
  unfold extendMendlerLeg
  simp only [coTwObjMk_cod, coTwObjMk_dom, coTwObjMk_arr]
  -- Use weighted cocone naturality with coTwToIdentityAtSource
  have nat := wc.ι.naturality (coTwToIdentityAtSource arr).op
  have natγ := congrFun nat γ
  simp only [types_comp_apply] at natγ
  -- For HomToProf, W.map (coTwToIdentityAtSource arr).op γ = γ
  have weight_map_eq : (profunctorOnOpCoTwistedArrow C (HomToProf pt)).map
      (coTwToIdentityAtSource arr).op γ = γ := by
    simp only [profunctorOnOpCoTwistedArrow_map, profunctorOnTwistedArrow_map,
      equiv_map_coTwToIdentityAtSource_twDomArr, equiv_map_coTwToIdentityAtSource_twCodArr]
    simp only [types_comp_apply]
    simp only [HomToProf_map_app, Quiver.Hom.unop_op, HomToProf_obj_map]
    exact Category.id_comp γ
  rw [weight_map_eq] at natγ
  -- homToFunctor map is precomposition by diagram map
  have homToFunctor_map_form :
      (homToFunctor (profunctorOnCoTwistedArrow C G) pt).map
        (coTwToIdentityAtSource arr).op
        (wc.ι.app (Opposite.op (idCoTwistedArrow cod)) γ) =
      (profunctorOnCoTwistedArrow C G).map (coTwToIdentityAtSource arr) ≫
        wc.ι.app (Opposite.op (idCoTwistedArrow cod)) γ := rfl
  rw [homToFunctor_map_form] at natγ
  rw [diagram_map_coTwToIdentityAtSource] at natγ
  -- natγ: wc.ι(coTwObjMk arr) γ = (G.map arr.op).app cod ≫ wc.ι(id_cod) γ
  rw [natγ]
  -- Show our formula equals (G.map arr.op).app cod ≫ wc.ι(id_cod) γ
  unfold rc restrictWeightedCowedge weightedCowedgeFamilyAtIdentity
  simp only [eqToHom_refl, Category.id_comp]
  congr 1
  simp only [profunctorOnCoTwistedArrow_at_identity]
  simp only [diagAppToWeightAtIdentity, cast_eq]
  -- Need to unfold diagonalToIdentityHom and leg
  simp only [diagonalToIdentityHom, WeightedCocone.leg]
  -- The structure { pt := pt, toWeightedCoconeOver := wc } has ι = wc.ι
  -- (WeightedCocone.ι c = c.toWeightedCoconeOver.ι)
  have h : ({ pt := pt, toWeightedCoconeOver := wc } :
    WeightedCocone (profunctorOnOpCoTwistedArrow C (HomToProf pt))
      (profunctorOnCoTwistedArrow C G)).ι = wc.ι := rfl
  rw [h]
  exact Category.id_comp _

-- General theorem using the canonical form
theorem extendMendlerLeg_eq_original_leg (pt : C)
    (wc : WeightedCoconeOver pt (profunctorOnOpCoTwistedArrow C (HomToProf pt))
      (profunctorOnCoTwistedArrow C G))
    (tw : CoTwistedArrow C)
    (γ : (profunctorOnOpCoTwistedArrow C (HomToProf pt)).obj (Opposite.op tw)) :
    let rc := (restrictWeightedCowedge (HomToProf pt) G
      ⟨pt, wc⟩).toRestrictedCowedgeOver
    extendMendlerLeg (G := G) pt rc tw γ =
    wc.ι.app (Opposite.op tw) γ := by
  intro rc
  -- A co-twisted arrow is definitionally a triple (cod, dom, arr : cod ⟶ dom)
  -- represented as coTwObjMk arr
  -- Use the specific case theorem which handles the canonical form
  have h := coTw_eq_coTwObjMk tw
  -- Revert γ and tw to substitute together
  revert γ
  rw [h]
  intro γ
  exact extendMendlerLeg_eq_original_leg_at_coTwObjMk (G := G) pt wc (coTwArr tw) γ

/-- The extend-restrict round-trip is the identity on weighted cowedges
with point pt. Starting from a weighted cowedge, restricting to diagonal,
and then extending gives back the original cowedge. -/
theorem extend_restrict_roundtrip (pt : C)
    (wc : WeightedCoconeOver pt (profunctorOnOpCoTwistedArrow C (HomToProf pt))
      (profunctorOnCoTwistedArrow C G)) :
    (extendRestrictedCowedgeFull (G := G) pt
      (restrictWeightedCowedge (HomToProf pt) G ⟨pt, wc⟩).toRestrictedCowedgeOver
    ).toWeightedCoconeOver = wc := by
  ext tw γ
  simp only [extendRestrictedCowedgeFull, extendRestrictedCowedge]
  exact extendMendlerLeg_eq_original_leg (G := G) pt wc tw.unop γ

/-- Restriction from weighted Mendler cowedge to Mendler algebra.
This extracts the diagonal data from a weighted cowedge by composing
`restrictWeightedCowedge` with `restrictedCowedgeToMendler`. -/
def weightedMendlerToMendler (pt : C) (wc : WeightedMendlerCowedge G pt)
    (hpt : wc.pt = pt) : MendlerAlgebra G :=
  let rc := restrictWeightedCowedge (HomToProf pt) G wc
  restrictedCowedgeToMendler G pt rc hpt

end WeightedCowedgeCorrespondence

section MendlerLambekCorrespondence

/-!
## The G^e Functor and Mendler-Lambek Correspondence

Following Vene's thesis (Section 5.5), we define the functor G^e that
mediates between Mendler-style algebras and conventional algebras.

For an endodifunctor G : Cᵒᵖ ⥤ C ⥤ C, assume that for every object pt,
there exists a (HomToProf pt)-restricted G-coend. Then:

- `G^e(pt) = (restrictedCoend G (HomToProf pt)).pt`
- `G^e(h : pt₁ → pt₂)` is defined via the universal property

The correspondence is:
- `floor(Φ)` : MendlerAlg → ConventionalAlg (the universal morphism)
- `ceil(φ)` : ConventionalAlg → MendlerAlg (composition with injection)

Theorem 5.19: These form an isomorphism of categories.
-/

variable {C : Type u} [Category.{v} C]
variable (G : Cᵒᵖ ⥤ C ⥤ C)

/-- For G^e to be defined, we need (HomToProf pt)-restricted G-coends
to exist for all objects pt. This class bundles this assumption. -/
class HasAllHomToProfCoends where
  hasCoend : ∀ (pt : C), HasRestrictedCoend G (HomToProf pt)

namespace HasAllHomToProfCoends

open HasRestrictedCoend

variable [HasAllHomToProfCoends G]

instance instHasRestrictedCoend (pt : C) : HasRestrictedCoend G (HomToProf pt) :=
  HasAllHomToProfCoends.hasCoend pt

/-- The object part of G^e: the carrier of the restricted coend. -/
def GExtObj (pt : C) : C :=
  (restrictedCoend G (HomToProf pt)).pt

/-- The injection family for the restricted coend at pt. -/
def GExtInj (pt : C) (A : C) (γ : A ⟶ pt) :
    (G.obj (Opposite.op A)).obj A ⟶ GExtObj G pt :=
  (restrictedCoend G (HomToProf pt)).family A γ

/-- The universal morphism from restricted coend to any cowedge. -/
def GExtDesc (pt : C) (d : RestrictedCowedge G (HomToProf pt)) :
    GExtObj G pt ⟶ d.pt :=
  (restrictedCoendIsInitial G (HomToProf pt)).descHom d

/-- Given h : pt₁ → pt₂, construct a (HomToProf pt₁)-restricted cowedge
with carrier G^e(pt₂). The family is: for γ : A → pt₁, compose with
the injection at pt₂. -/
def GExtMapCowedge (pt₁ pt₂ : C) (h : pt₁ ⟶ pt₂) :
    RestrictedCowedge G (HomToProf pt₁) where
  pt := GExtObj G pt₂
  toRestrictedCowedgeOver := ⟨fun A γ => GExtInj G pt₂ A (γ ≫ h), by
    intro A B g x
    have dinat := (restrictedCoend G (HomToProf pt₂)).isDinatural A B g (x ≫ h)
    simp only [Profunctor.lmap, Profunctor.rmap, sliceProfunctor,
      HomToProf_map_app, HomToProf_obj_map, GExtInj, Category.assoc] at dinat ⊢
    exact dinat⟩

/-- The morphism part of G^e: uses the universal property. -/
def GExtMap (pt₁ pt₂ : C) (h : pt₁ ⟶ pt₂) :
    GExtObj G pt₁ ⟶ GExtObj G pt₂ :=
  GExtDesc G pt₁ (GExtMapCowedge G pt₁ pt₂ h)

/-- G^e preserves identity: G^e(id) = id.
Uses uniqueness of the universal morphism from a coend.

The identity on GExtObj G pt and GExtMap G pt pt (𝟙 pt) both satisfy the
same commutativity condition with respect to the coend injection. -/
theorem GExtMap_id (pt : C) :
    GExtMap G pt pt (𝟙 pt) = 𝟙 (GExtObj G pt) := by
  let hmorphId : (restrictedCoend G (HomToProf pt)) ⟶
      (GExtMapCowedge G pt pt (𝟙 pt)) := {
    hom := 𝟙 (GExtObj G pt)
    comm := fun A γ => by
      simp only [GExtMapCowedge, RestrictedCowedge.family, GExtInj, Category.comp_id]
      exact Category.comp_id _
  }
  have heq : hmorphId = (restrictedCoendIsInitial G (HomToProf pt)).to _ :=
    (restrictedCoendIsInitial G (HomToProf pt)).hom_ext hmorphId _
  simp only [GExtMap, GExtDesc, IsRestrictedCoend.descHom, IsRestrictedCoend.desc]
  have step := congrArg RestrictedCowedge.Hom.hom heq.symm
  simp only at step
  exact step

/-- G^e preserves composition: G^e(g ∘ f) = G^e(g) ∘ G^e(f).
Uses uniqueness of the universal morphism. -/
theorem GExtMap_comp (pt₁ pt₂ pt₃ : C) (f : pt₁ ⟶ pt₂) (g : pt₂ ⟶ pt₃) :
    GExtMap G pt₁ pt₃ (f ≫ g) = GExtMap G pt₁ pt₂ f ≫ GExtMap G pt₂ pt₃ g := by
  let hmorphComp : (restrictedCoend G (HomToProf pt₁)) ⟶
      (GExtMapCowedge G pt₁ pt₃ (f ≫ g)) := {
    hom := GExtMap G pt₁ pt₂ f ≫ GExtMap G pt₂ pt₃ g
    comm := fun A γ => by
      simp only [GExtMap, GExtDesc, IsRestrictedCoend.descHom, IsRestrictedCoend.desc,
        GExtMapCowedge, RestrictedCowedge.family, GExtInj]
      have h1 := ((restrictedCoendIsInitial G (HomToProf pt₁)).to
        (GExtMapCowedge G pt₁ pt₂ f)).comm A γ
      have h2 := ((restrictedCoendIsInitial G (HomToProf pt₂)).to
        (GExtMapCowedge G pt₂ pt₃ g)).comm A (γ ≫ f)
      simp only [GExtMapCowedge, RestrictedCowedge.family, GExtInj] at h1 h2
      rw [← Category.assoc, h1, h2, Category.assoc]
  }
  have heq : hmorphComp =
      (restrictedCoendIsInitial G (HomToProf pt₁)).to (GExtMapCowedge G pt₁ pt₃ (f ≫ g)) :=
    (restrictedCoendIsInitial G (HomToProf pt₁)).hom_ext hmorphComp _
  simp only [GExtMap, GExtDesc, IsRestrictedCoend.descHom, IsRestrictedCoend.desc]
  have step := congrArg RestrictedCowedge.Hom.hom heq.symm
  simp only at step
  exact step

/-- The endofunctor G^e : C ⥤ C.
G^e(pt) is the carrier of the (HomToProf pt)-restricted G-coend. -/
@[simps]
def GExtFunctor : C ⥤ C where
  obj := GExtObj G
  map := GExtMap G _ _
  map_id := GExtMap_id G
  map_comp := GExtMap_comp G _ _ _

end HasAllHomToProfCoends

/-!
## Conventional Algebras and Floor/Ceiling Translations

A conventional F-algebra for an endofunctor F : C ⥤ C is a pair (pt, φ)
where φ : F(pt) ⟶ pt.

We define:
- `ConventionalAlgebra F`: the structure of F-algebras
- `floor`: MendlerAlgebra G → ConventionalAlgebra (GExtFunctor G)
- `ceil`: ConventionalAlgebra (GExtFunctor G) → MendlerAlgebra G
-/

/-- A conventional F-algebra for an endofunctor F : C ⥤ C. -/
@[ext]
structure ConventionalAlgebra (F : C ⥤ C) where
  /-- The carrier object. -/
  pt : C
  /-- The algebra structure morphism. -/
  str : F.obj pt ⟶ pt

/-- A morphism of conventional F-algebras. -/
@[ext]
structure ConventionalAlgebraHom {F : C ⥤ C}
    (a₁ a₂ : ConventionalAlgebra F) where
  /-- The underlying morphism in C. -/
  hom : a₁.pt ⟶ a₂.pt
  /-- The compatibility condition: str₂ ∘ F(h) = h ∘ str₁. -/
  comm : F.map hom ≫ a₂.str = a₁.str ≫ hom

namespace ConventionalAlgebraHom

variable {F : C ⥤ C}

/-- Identity morphism on a conventional algebra. -/
@[simps]
def id (a : ConventionalAlgebra F) : ConventionalAlgebraHom a a where
  hom := 𝟙 a.pt
  comm := by simp

/-- Composition of conventional algebra morphisms. -/
@[simps]
def comp {a₁ a₂ a₃ : ConventionalAlgebra F}
    (f : ConventionalAlgebraHom a₁ a₂) (g : ConventionalAlgebraHom a₂ a₃) :
    ConventionalAlgebraHom a₁ a₃ where
  hom := f.hom ≫ g.hom
  comm := by
    rw [F.map_comp, Category.assoc, g.comm, ← Category.assoc, f.comm]
    simp [Category.assoc]

end ConventionalAlgebraHom

/-- The category of conventional F-algebras. -/
instance ConventionalAlgebraCat (F : C ⥤ C) : Category (ConventionalAlgebra F) where
  Hom := ConventionalAlgebraHom
  id := ConventionalAlgebraHom.id
  comp := ConventionalAlgebraHom.comp
  id_comp _ := by ext; simp [ConventionalAlgebraHom.comp, ConventionalAlgebraHom.id]
  comp_id _ := by ext; simp [ConventionalAlgebraHom.comp, ConventionalAlgebraHom.id]
  assoc _ _ _ := by ext; simp [ConventionalAlgebraHom.comp, Category.assoc]

section FloorCeiling

variable (G : Cᵒᵖ ⥤ C ⥤ C) [HasAllHomToProfCoends G]

open HasRestrictedCoend HasAllHomToProfCoends

/-- The floor translation: converts a Mendler algebra (pt, Φ) to a conventional
G^e-algebra (pt, floor(Φ)) where floor(Φ) is the universal morphism from
the restricted coend to pt. -/
def floor (m : MendlerAlgebra G) :
    ConventionalAlgebra (HasAllHomToProfCoends.GExtFunctor G) where
  pt := m.pt
  str := HasAllHomToProfCoends.GExtDesc G m.pt m.toRestrictedCowedge

/-- The ceiling translation: converts a conventional G^e-algebra (pt, φ)
to a Mendler algebra (pt, ceil(φ)) where ceil(φ)_A(γ) = φ ∘ inj_A(γ). -/
def ceil (a : ConventionalAlgebra (HasAllHomToProfCoends.GExtFunctor G)) :
    MendlerAlgebra G where
  pt := a.pt
  toMendlerAlgebraOver := ⟨⟨fun A γ => HasAllHomToProfCoends.GExtInj G a.pt A γ ≫ a.str, by
    intro A B g x
    simp only [Profunctor.lmap, Profunctor.rmap, sliceProfunctor_obj_map,
      sliceProfunctor_map_app, Quiver.Hom.unop_op, HomToProf_map_app, HomToProf_obj_map]
    have dinat := (restrictedCoend G (HomToProf a.pt)).isDinatural A B g x
    simp only [Profunctor.lmap, Profunctor.rmap, sliceProfunctor_obj_map,
      sliceProfunctor_map_app, Quiver.Hom.unop_op, HomToProf_map_app, HomToProf_obj_map,
      HasAllHomToProfCoends.GExtInj] at dinat ⊢
    simp only [← Category.assoc]
    exact congrArg (· ≫ a.str) dinat⟩⟩

/-- floor(ceil(φ)) = φ (Proposition 5.15 in Vene).
The floor of the ceiling of a conventional algebra structure is the
original structure. -/
theorem floor_ceil (a : ConventionalAlgebra (HasAllHomToProfCoends.GExtFunctor G)) :
    floor G (ceil G a) = a := by
  cases a with | mk pt str =>
  simp only [floor, ceil, MendlerAlgebra.toRestrictedCowedge, MendlerAlgebra.family,
    GExtDesc, GExtInj]
  congr 1
  let targetCowedge : RestrictedCowedge G (HomToProf pt) :=
    ⟨pt, ⟨fun A γ => (restrictedCoend G (HomToProf pt)).family A γ ≫ str,
     (ceil G ⟨pt, str⟩).isDinatural⟩⟩
  let strMorph : RestrictedCowedge.Hom (restrictedCoend G (HomToProf pt)) targetCowedge := {
    hom := str
    comm := fun _ _ => rfl
  }
  have huniq := (restrictedCoendIsInitial G (HomToProf pt)).hom_ext
    ((restrictedCoendIsInitial G (HomToProf pt)).to targetCowedge) strMorph
  simp only [IsRestrictedCoend.descHom, IsRestrictedCoend.desc]
  exact congrArg RestrictedCowedge.Hom.hom huniq

/-- ceil(floor(Φ)) = Φ (Proposition 5.16 in Vene).
The ceiling of the floor of a Mendler algebra is the original algebra. -/
theorem ceil_floor (m : MendlerAlgebra G) :
    ceil G (floor G m) = m := by
  cases m with | mk pt u =>
  cases u with | mk r =>
  cases r with | mk family isDinat =>
  simp only [ceil, floor, MendlerAlgebra.toRestrictedCowedge, MendlerAlgebra.family,
    GExtDesc, GExtInj]
  congr 1
  apply MendlerAlgebraOver.ext
  apply RestrictedCowedgeOver.ext
  funext A γ
  exact ((restrictedCoendIsInitial G (HomToProf pt)).to
    ⟨pt, ⟨family, isDinat⟩⟩).comm A γ

/-- floor preserves morphisms (Proposition 5.18 in Vene).
If h is a Mendler algebra morphism, then h is a conventional G^e-algebra
morphism between the floor algebras. -/
def floorHom {m₁ m₂ : MendlerAlgebra G} (f : m₁ ⟶ m₂) :
    floor G m₁ ⟶ floor G m₂ where
  hom := f.hom
  comm := by
    simp only [floor, GExtFunctor_map, GExtMap, GExtDesc, GExtMapCowedge,
      MendlerAlgebra.toRestrictedCowedge, IsRestrictedCoend.descHom, IsRestrictedCoend.desc]
    let targetCowedge : RestrictedCowedge G (HomToProf m₁.pt) := {
      pt := m₂.pt
      toRestrictedCowedgeOver := ⟨fun A γ => m₂.family A (γ ≫ f.hom), by
        intro A B g x
        have hdinat := m₂.isDinatural A B g (x ≫ f.hom)
        simp only [Profunctor.lmap, Profunctor.rmap, sliceProfunctor,
          HomToProf_map_app, HomToProf_obj_map, Category.assoc] at hdinat ⊢
        exact hdinat⟩
    }
    let lhsMorph : RestrictedCowedge.Hom (restrictedCoend G (HomToProf m₁.pt)) targetCowedge := {
      hom := (restrictedCoendIsInitial G (HomToProf m₁.pt)).descHom
          (GExtMapCowedge G m₁.pt m₂.pt f.hom) ≫
        (restrictedCoendIsInitial G (HomToProf m₂.pt)).descHom m₂.toRestrictedCowedge
      comm := fun A γ => by
        simp only [IsRestrictedCoend.descHom, IsRestrictedCoend.desc,
          GExtMapCowedge, GExtInj, MendlerAlgebra.toRestrictedCowedge]
        have h1 := (restrictedCoendIsInitial G (HomToProf m₁.pt)).to
          (GExtMapCowedge G m₁.pt m₂.pt f.hom) |>.comm A γ
        simp only [GExtMapCowedge, GExtInj] at h1
        simp only [← Category.assoc]
        rw [h1]
        have h2 := (restrictedCoendIsInitial G (HomToProf m₂.pt)).to
          m₂.toRestrictedCowedge |>.comm A (γ ≫ f.hom)
        simp only [MendlerAlgebra.toRestrictedCowedge] at h2
        exact h2
    }
    let rhsMorph : RestrictedCowedge.Hom (restrictedCoend G (HomToProf m₁.pt)) targetCowedge := {
      hom := (restrictedCoendIsInitial G (HomToProf m₁.pt)).descHom
          m₁.toRestrictedCowedge ≫ f.hom
      comm := fun A γ => by
        simp only [IsRestrictedCoend.descHom, IsRestrictedCoend.desc,
          MendlerAlgebra.toRestrictedCowedge]
        have h1 := (restrictedCoendIsInitial G (HomToProf m₁.pt)).to
          m₁.toRestrictedCowedge |>.comm A γ
        simp only [MendlerAlgebra.toRestrictedCowedge] at h1
        simp only [← Category.assoc]
        rw [h1]
        exact f.comm A γ
    }
    have huniq := (restrictedCoendIsInitial G (HomToProf m₁.pt)).hom_ext lhsMorph rhsMorph
    exact congrArg RestrictedCowedge.Hom.hom huniq

/-- ceil preserves morphisms (Proposition 5.17 in Vene).
If h is a conventional G^e-algebra morphism, then h is a Mendler algebra
morphism between the ceiling algebras. -/
def ceilHom {a₁ a₂ : ConventionalAlgebra (HasAllHomToProfCoends.GExtFunctor G)}
    (f : a₁ ⟶ a₂) : ceil G a₁ ⟶ ceil G a₂ where
  hom := f.hom
  comm := by
    intro A γ
    simp only [ceil, MendlerAlgebra.family, MendlerAlgebraOver.family, GExtInj]
    have comm := f.comm
    simp only [GExtFunctor_map, GExtMap, GExtDesc, GExtMapCowedge,
      IsRestrictedCoend.descHom, IsRestrictedCoend.desc] at comm
    rw [Category.assoc, ← comm, ← Category.assoc]
    have h := (restrictedCoendIsInitial G (HomToProf a₁.pt)).to
      (GExtMapCowedge G a₁.pt a₂.pt f.hom) |>.comm A γ
    simp only [GExtMapCowedge, RestrictedCowedge.family, GExtInj] at h ⊢
    rw [h]

/-- The floor functor: MendlerAlgebra G ⥤ ConventionalAlgebra (GExtFunctor G). -/
@[simps]
def floorFunctor : MendlerAlgebra G ⥤
    ConventionalAlgebra (HasAllHomToProfCoends.GExtFunctor G) where
  obj := floor G
  map := floorHom G
  map_id := fun _ => ConventionalAlgebraHom.ext rfl
  map_comp := fun _ _ => ConventionalAlgebraHom.ext rfl

/-- The ceiling functor: ConventionalAlgebra (GExtFunctor G) ⥤ MendlerAlgebra G. -/
@[simps]
def ceilFunctor : ConventionalAlgebra (HasAllHomToProfCoends.GExtFunctor G) ⥤
    MendlerAlgebra G where
  obj := ceil G
  map := ceilHom G
  map_id := fun _ => MendlerAlgebraHom.ext rfl
  map_comp := fun _ _ => MendlerAlgebraHom.ext rfl

/-- The .hom component of eqToHom in ConventionalAlgebra is eqToHom in C. -/
@[simp]
theorem ConventionalAlgebra.eqToHom_hom {F : C ⥤ C} {a b : ConventionalAlgebra F}
    (h : a = b) : (eqToHom h).hom = eqToHom (congrArg ConventionalAlgebra.pt h) := by
  subst h
  rfl

/-- The .hom component of eqToHom in MendlerAlgebra is eqToHom in C. -/
@[simp]
theorem MendlerAlgebra.eqToHom_hom' {G' : Cᵒᵖ ⥤ C ⥤ C} {m₁ m₂ : MendlerAlgebra G'}
    (h : m₁ = m₂) : (eqToHom h).hom = eqToHom (congrArg MendlerAlgebra.pt h) := by
  subst h
  rfl

/-- floor ∘ ceil = id on the conventional algebra category. -/
theorem floorFunctor_comp_ceilFunctor :
    ceilFunctor G ⋙ floorFunctor G = 𝟭 _ :=
  Functor.ext (floor_ceil G) (fun a₁ a₂ f => by
    simp only [Functor.comp_map, Functor.id_map, floorFunctor_map, ceilFunctor_map]
    apply ConventionalAlgebraHom.ext
    simp only [floorHom, ceilHom]
    have heq1 : congrArg ConventionalAlgebra.pt (floor_ceil G a₁) = rfl := rfl
    have heq2 : congrArg ConventionalAlgebra.pt (floor_ceil G a₂).symm = rfl := rfl
    rw [show (eqToHom (floor_ceil G a₁) ≫ f ≫ eqToHom (floor_ceil G a₂).symm).hom =
        (eqToHom (floor_ceil G a₁)).hom ≫ f.hom ≫ (eqToHom (floor_ceil G a₂).symm).hom
        from rfl]
    rw [ConventionalAlgebra.eqToHom_hom, ConventionalAlgebra.eqToHom_hom,
        heq1, heq2, eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id])

/-- ceil ∘ floor = id on the Mendler algebra category. -/
theorem ceilFunctor_comp_floorFunctor :
    floorFunctor G ⋙ ceilFunctor G = 𝟭 _ :=
  Functor.ext (ceil_floor G) (fun m₁ m₂ f => by
    simp only [Functor.comp_map, Functor.id_map, floorFunctor_map, ceilFunctor_map]
    apply MendlerAlgebraHom.ext
    simp only [ceilHom, floorHom]
    have heq1 : congrArg MendlerAlgebra.pt (ceil_floor G m₁) = rfl := rfl
    have heq2 : congrArg MendlerAlgebra.pt (ceil_floor G m₂).symm = rfl := rfl
    rw [show (eqToHom (ceil_floor G m₁) ≫ f ≫ eqToHom (ceil_floor G m₂).symm).hom =
        (eqToHom (ceil_floor G m₁)).hom ≫ f.hom ≫ (eqToHom (ceil_floor G m₂).symm).hom
        from rfl]
    rw [MendlerAlgebra.eqToHom_hom', MendlerAlgebra.eqToHom_hom',
        heq1, heq2, eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id])

/-- The Mendler-Lambek correspondence (Theorem 5.19 in Vene):
The categories of Mendler algebras and conventional G^e-algebras are
isomorphic. -/
def mendlerLambekEquiv :
    MendlerAlgebra G ≌ ConventionalAlgebra (HasAllHomToProfCoends.GExtFunctor G) :=
  CategoryTheory.Equivalence.mk (floorFunctor G) (ceilFunctor G)
    (CategoryTheory.Iso.refl _
      |>.symm.trans (CategoryTheory.eqToIso (ceilFunctor_comp_floorFunctor G).symm))
    (CategoryTheory.eqToIso (floorFunctor_comp_ceilFunctor G))

end FloorCeiling

end MendlerLambekCorrespondence

end GebLean
