/-
Copyright (c) 2026 The geb-mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The geb-mathlib contributors
-/
module

public import Mathlib.CategoryTheory.Grothendieck
public import Mathlib.CategoryTheory.Category.Cat.Op
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Tactic.Attr.Core

/-!
# Covariant and contravariant Grothendieck constructions

For a functor `F : C ⥤ Cat`, mathlib's `CategoryTheory.Grothendieck F`
is the covariant Grothendieck construction. This module adds:

* a `Cat`-valued packaging of the covariant construction
  (`Grothendieck.functorToCat`);
* `GrothendieckOp F`, the covariant construction applied to the
  oppositization `F ⋙ Cat.opFunctor`;
* `CoGrothendieck G`, the contravariant Grothendieck construction of
  `G : Cᵒᵖ ⥤ Cat`, defined as `(GrothendieckOp G)ᵒᵖ`, together with an
  interface whose constructors and destructors use morphisms of `C`.

## Main definitions

* `CategoryTheory.Grothendieck.functorToCat`
* `CategoryTheory.GrothendieckOp`
* `CategoryTheory.CoGrothendieck`

## Main statements

* `GrothendieckOp.hom_ext` and `CoGrothendieck.hom_ext`
* `GrothendieckOp.map_id_eq`/`map_comp_eq` and the `CoGrothendieck`
  counterparts

## Implementation notes

`GrothendieckOp` and `CoGrothendieck` are semireducible `def` type
synonyms, not `abbrev`s and not new structures: instance synthesis and
object-level dot notation stop at the new names, while all round-trip
lemmas hold by `rfl`. Both are `@[implicit_reducible]`: type-level
unification compares types at implicit transparency, so the attribute
lets keyed `rw`/`simp` matching cross the synonym while instance
synthesis and dot notation still stop at it. Morphism-level dot notation resolves through
`Quiver.Hom` to `Grothendieck.Hom`'s own projections (whose op-side
types make direction misuse a type error); the wrapper accessors
`homBase`/`homFiber` are therefore free functions, used qualified or
via `open`.

Universe levels match the covariant construction exactly: for
`F : C ⥤ Cat.{v₂, u₂}` with `C : Type u` and `Category.{v} C`, both
`GrothendieckOp F` and `CoGrothendieck G` live in `Type (max u u₂)`
with `Category.{max v v₂}` instances, since `ᵒᵖ` and `Cat.opFunctor`
preserve universes. The packaged functors (`functor`, `functorToCat`)
restrict to `E : Cat.{v, u}` with fibers in the same `Cat.{v, u}`,
inherited from mathlib's `Grothendieck.functor`.

`Cat` is a semireducible `def` (`Bundled Category`), not an `abbrev`,
so a keyed `rw`/`simp` rewrite that must unify a generic `Cᵒᵖ`-shaped
lemma (`unop_comp`, `eqToHom_unop`, `Grothendieck.id_fiber`,
`Grothendieck.comp_fiber`) against a term routed through
`Cat.opFunctor.obj`/`F.map _ |>.toFunctor` fails even though the two
sides are definitionally equal. `GrothendieckOp.hom_ext`, `homFiber_id`, `homFiber_comp`, and
`GrothendieckOp.homFiber_map_map` isolate a single `erw` step — which
unifies at a higher transparency — to cross exactly that reducibility boundary; the
surrounding steps stay on `rfl`/`rw`/`simp`.

## References

The contravariant Grothendieck construction is standard; see
[Vistoli2008] and [JohnsonYau2021].

## Tags

Grothendieck construction, contravariant, opposite category, fibered
category
-/

@[expose] public section

universe u v u₂ v₂

namespace CategoryTheory

open CategoryTheory.Functor

variable {C : Type u} [Category.{v} C]

/-! ## Covariant construction: `Cat`-valued packaging -/

namespace Grothendieck

/-- The covariant Grothendieck construction as a functor to `Cat`:
`Grothendieck.functor` followed by forgetting the projection to the
base. -/
def functorToCat {E : Cat.{v, u}} : (↑E ⥤ Cat.{v, u}) ⥤ Cat.{v, u} :=
  Grothendieck.functor ⋙ Over.forget E

/-- `functorToCat` sends a functor to the Grothendieck construction on it. -/
@[simp]
theorem functorToCat_obj {E : Cat.{v, u}} (F : ↑E ⥤ Cat.{v, u}) :
    functorToCat.obj F = Cat.of (Grothendieck F) :=
  rfl

/-- `functorToCat` sends a natural transformation to the induced functor. -/
@[simp]
theorem functorToCat_map {E : Cat.{v, u}} {F F' : ↑E ⥤ Cat.{v, u}}
    (α : F ⟶ F') : functorToCat.map α = (Grothendieck.map α).toCatHom :=
  rfl

end Grothendieck

/-! ## The Grothendieck construction of an oppositized functor -/

/-- The covariant Grothendieck construction applied to the
oppositization of `F`: objects are pairs of a base object `c : C` and a
fiber object of `F.obj c`, and morphisms reverse the fiber direction
relative to `Grothendieck F`. -/
@[implicit_reducible]
def GrothendieckOp (F : C ⥤ Cat.{v₂, u₂}) : Type (max u u₂) :=
  Grothendieck (F ⋙ Cat.opFunctor)

namespace GrothendieckOp

/-- The category structure on `GrothendieckOp F`, inherited from the
underlying covariant Grothendieck construction. -/
instance category (F : C ⥤ Cat.{v₂, u₂}) :
    Category.{max v v₂} (GrothendieckOp F) :=
  inferInstanceAs (Category (Grothendieck (F ⋙ Cat.opFunctor)))

variable {F : C ⥤ Cat.{v₂, u₂}}

/-- Construct an object of `GrothendieckOp F` from a base object and a
fiber object. -/
def mk (base : C) (fiber : F.obj base) : GrothendieckOp F :=
  ⟨base, Opposite.op fiber⟩

/-- The base object of an object of `GrothendieckOp F`. -/
def base (X : GrothendieckOp F) : C :=
  Grothendieck.base X

/-- The fiber object of an object of `GrothendieckOp F`. -/
def fiber (X : GrothendieckOp F) : F.obj X.base :=
  Opposite.unop (Grothendieck.fiber X)

/-- `mk` recovers the base component on the nose. -/
@[simp]
theorem base_mk (b : C) (f : F.obj b) : (mk b f).base = b :=
  rfl

/-- `mk` recovers the fiber component on the nose. -/
@[simp]
theorem fiber_mk (b : C) (f : F.obj b) : (mk b f).fiber = f :=
  rfl

/-- Every object of `GrothendieckOp F` is `mk` applied to its own base
and fiber. -/
@[simp]
theorem mk_base_fiber (X : GrothendieckOp F) : mk X.base X.fiber = X :=
  rfl

/-- Construct a morphism of `GrothendieckOp F` from a base morphism and
a fiber morphism. The fiber morphism runs from the target fiber to the
pushforward of the source fiber — the reversal relative to
`Grothendieck.Hom`. -/
def homMk {X Y : GrothendieckOp F} (base : X.base ⟶ Y.base)
    (fiber : Y.fiber ⟶ (F.map base).toFunctor.obj X.fiber) : X ⟶ Y :=
  ⟨base, fiber.op⟩

/-- The base morphism of a morphism of `GrothendieckOp F`. -/
def homBase {X Y : GrothendieckOp F} (f : X ⟶ Y) : X.base ⟶ Y.base :=
  Grothendieck.Hom.base f

/-- The fiber morphism of a morphism of `GrothendieckOp F`. -/
def homFiber {X Y : GrothendieckOp F} (f : X ⟶ Y) :
    Y.fiber ⟶ (F.map (homBase f)).toFunctor.obj X.fiber :=
  Quiver.Hom.unop (Grothendieck.Hom.fiber f)

/-- `homMk` recovers the base component on the nose. -/
@[simp]
theorem homBase_homMk {X Y : GrothendieckOp F} (b : X.base ⟶ Y.base)
    (φ : Y.fiber ⟶ (F.map b).toFunctor.obj X.fiber) :
    homBase (homMk b φ) = b :=
  rfl

/-- `homMk` recovers the fiber component on the nose. -/
@[simp]
theorem homFiber_homMk {X Y : GrothendieckOp F} (b : X.base ⟶ Y.base)
    (φ : Y.fiber ⟶ (F.map b).toFunctor.obj X.fiber) :
    homFiber (homMk b φ) = φ :=
  rfl

/-- Every morphism of `GrothendieckOp F` is `homMk` applied to its own
base and fiber components. -/
@[simp]
theorem homMk_base_fiber {X Y : GrothendieckOp F} (f : X ⟶ Y) :
    homMk (homBase f) (homFiber f) = f :=
  rfl

/-- Two morphisms of `GrothendieckOp F` agree once their base
components agree and their fiber components agree after transport
along that agreement. -/
@[ext (iff := false)]
theorem hom_ext {X Y : GrothendieckOp F} (f g : X ⟶ Y)
    (hbase : homBase f = homBase g)
    (hfiber : homFiber f ≫ eqToHom (by rw [hbase]) = homFiber g) :
    f = g := by
  refine Grothendieck.ext f g hbase ?_
  apply Quiver.Hom.unop_inj
  erw [unop_comp, eqToHom_unop]
  exact hfiber

/-- `homBase` sends the identity morphism to the identity morphism. -/
@[simp]
theorem homBase_id (X : GrothendieckOp F) : homBase (𝟙 X) = 𝟙 X.base :=
  rfl

/-- `homFiber` of the identity morphism is the canonical transport
isomorphism. -/
@[simp]
theorem homFiber_id (X : GrothendieckOp F) :
    homFiber (𝟙 X) = eqToHom (by simp) := by
  erw [homFiber, Grothendieck.id_fiber, eqToHom_unop]
  rfl

/-- `homBase` is functorial: it sends composition to composition. -/
@[simp]
theorem homBase_comp {X Y Z : GrothendieckOp F} (f : X ⟶ Y) (g : Y ⟶ Z) :
    homBase (f ≫ g) = homBase f ≫ homBase g :=
  rfl

/-- `homFiber` of a composite is the composite of the fiber morphisms,
transported along the base functoriality. -/
@[simp]
theorem homFiber_comp {X Y Z : GrothendieckOp F} (f : X ⟶ Y)
    (g : Y ⟶ Z) :
    homFiber (f ≫ g) =
      homFiber g ≫ (F.map (homBase g)).toFunctor.map (homFiber f) ≫
        eqToHom (by simp) := by
  erw [homFiber, Grothendieck.comp_fiber, unop_comp, unop_comp, eqToHom_unop,
    Functor.op_map, Category.assoc]
  rfl

/-- The projection `GrothendieckOp F ⥤ C` onto the base category. -/
def forget (F : C ⥤ Cat.{v₂, u₂}) : GrothendieckOp F ⥤ C :=
  Grothendieck.forget (F ⋙ Cat.opFunctor)

/-- `forget` sends an object of `GrothendieckOp F` to its base object. -/
@[simp]
theorem forget_obj (X : GrothendieckOp F) : (forget F).obj X = X.base :=
  rfl

/-- `forget` sends a morphism of `GrothendieckOp F` to its base morphism. -/
@[simp]
theorem forget_map {X Y : GrothendieckOp F} (f : X ⟶ Y) :
    (forget F).map f = homBase f :=
  rfl

/-- A natural transformation `α : F ⟶ F'` induces a functor
`GrothendieckOp F ⥤ GrothendieckOp F'`. -/
def map {F F' : C ⥤ Cat.{v₂, u₂}} (α : F ⟶ F') :
    GrothendieckOp F ⥤ GrothendieckOp F' :=
  Grothendieck.map (whiskerRight α Cat.opFunctor)

/-- `map` sends `mk b f` to `mk b` applied to the pushforward of `f` along `α`. -/
@[simp]
theorem map_obj_mk {F F' : C ⥤ Cat.{v₂, u₂}} (α : F ⟶ F') (b : C)
    (f : F.obj b) :
    (map α).obj (mk b f) = mk b ((α.app b).toFunctor.obj f) :=
  rfl

/-- `map` leaves the base component of a morphism unchanged. -/
@[simp]
theorem homBase_map_map {F F' : C ⥤ Cat.{v₂, u₂}} (α : F ⟶ F')
    {X Y : GrothendieckOp F} (f : X ⟶ Y) :
    homBase ((map α).map f) = homBase f :=
  rfl

/-- `map` transports the fiber component of a morphism along `α`, up to the
canonical isomorphism supplied by `α`'s naturality. -/
@[simp]
theorem homFiber_map_map {F F' : C ⥤ Cat.{v₂, u₂}} (α : F ⟶ F')
    {X Y : GrothendieckOp F} (f : X ⟶ Y) :
    homFiber ((map α).map f) =
      (α.app Y.base).toFunctor.map (homFiber f) ≫
        eqToHom (congrArg
          (fun p : F.obj X.base ⟶ F'.obj Y.base ↦
            p.toFunctor.obj X.fiber)
          (α.naturality (homBase f))) := by
  simp only [map, homBase, homFiber, Grothendieck.map_map_fiber, Functor.comp_map,
    Cat.Hom.comp_toFunctor]
  erw [Functor.op_map, unop_comp, eqToHom_unop]
  rfl

/-- `map` sends the identity natural transformation to the identity functor. -/
theorem map_id_eq (F : C ⥤ Cat.{v₂, u₂}) :
    map (𝟙 F) = 𝟭 (GrothendieckOp F) := by
  rw [map, whiskerRight_id']
  exact Grothendieck.map_id_eq

/-- `map` sends composition of natural transformations to composition of
functors. -/
theorem map_comp_eq {F F' F'' : C ⥤ Cat.{v₂, u₂}} (α : F ⟶ F')
    (β : F' ⟶ F'') : map (α ≫ β) = map α ⋙ map β := by
  rw [map, whiskerRight_comp]
  exact Grothendieck.map_comp_eq _ _

/-- `map (𝟙 F)` is the identity functor, as an isomorphism. -/
def mapIdIso (F : C ⥤ Cat.{v₂, u₂}) : map (𝟙 F) ≅ 𝟭 (GrothendieckOp F) :=
  eqToIso (map_id_eq F)

/-- `map` sends composition of natural transformations to composition
of functors, as an isomorphism. -/
def mapCompIso {F F' F'' : C ⥤ Cat.{v₂, u₂}} (α : F ⟶ F')
    (β : F' ⟶ F'') : map (α ≫ β) ≅ map α ⋙ map β :=
  eqToIso (map_comp_eq α β)

/-- The `GrothendieckOp` construction as a functor from `↑E ⥤ Cat` to
the over category of `E` in `Cat`: post-compose with `Cat.opFunctor`,
then apply mathlib's `Grothendieck.functor`. -/
def functor {E : Cat.{v, u}} :
    (↑E ⥤ Cat.{v, u}) ⥤ Over (T := Cat.{v, u}) E :=
  (whiskeringRight ↑E Cat.{v, u} Cat.{v, u}).obj Cat.opFunctor ⋙
    Grothendieck.functor

/-- `functor` sends `F` to an over-object whose hom component is
`forget F`. -/
@[simp]
theorem functor_obj_hom {E : Cat.{v, u}} (F : ↑E ⥤ Cat.{v, u}) :
    (functor.obj F).hom = (forget F).toCatHom :=
  rfl

/-- The `GrothendieckOp` construction as a functor to `Cat`. -/
def functorToCat {E : Cat.{v, u}} : (↑E ⥤ Cat.{v, u}) ⥤ Cat.{v, u} :=
  functor ⋙ Over.forget E

/-- `functorToCat` sends a functor to the `GrothendieckOp` construction
on it. -/
@[simp]
theorem functorToCat_obj {E : Cat.{v, u}} (F : ↑E ⥤ Cat.{v, u}) :
    functorToCat.obj F = Cat.of (GrothendieckOp F) :=
  rfl

end GrothendieckOp

/-! ## The contravariant Grothendieck construction -/

/-- The contravariant Grothendieck construction of `G : Cᵒᵖ ⥤ Cat`:
the opposite category of `GrothendieckOp G`. Objects are pairs of
`c : C` and an object of `G.obj (op c)`; a morphism `X ⟶ Y` consists of
`β : X.base ⟶ Y.base` in `C` and a fiber morphism
`X.fiber ⟶ (G.map β.op).toFunctor.obj Y.fiber`. -/
@[implicit_reducible]
def CoGrothendieck (G : Cᵒᵖ ⥤ Cat.{v₂, u₂}) : Type (max u u₂) :=
  (GrothendieckOp G)ᵒᵖ

namespace CoGrothendieck

/-- The category structure on `CoGrothendieck G`, inherited from the
opposite of `GrothendieckOp G`. -/
instance category (G : Cᵒᵖ ⥤ Cat.{v₂, u₂}) :
    Category.{max v v₂} (CoGrothendieck G) :=
  inferInstanceAs (Category (GrothendieckOp G)ᵒᵖ)

variable {G : Cᵒᵖ ⥤ Cat.{v₂, u₂}}

/-- Construct an object of `CoGrothendieck G` from a base object and a
fiber object. -/
def mk (base : C) (fiber : G.obj (Opposite.op base)) :
    CoGrothendieck G :=
  Opposite.op (GrothendieckOp.mk (Opposite.op base) fiber)

/-- The base object of an object of `CoGrothendieck G`, as an object
of `C`. -/
def base (X : CoGrothendieck G) : C :=
  Opposite.unop (GrothendieckOp.base (Opposite.unop X))

/-- The fiber object of an object of `CoGrothendieck G`. -/
def fiber (X : CoGrothendieck G) : G.obj (Opposite.op X.base) :=
  GrothendieckOp.fiber (Opposite.unop X)

/-- `mk` recovers the base component on the nose. -/
@[simp]
theorem base_mk (b : C) (f : G.obj (Opposite.op b)) : (mk b f).base = b :=
  rfl

/-- `mk` recovers the fiber component on the nose. -/
@[simp]
theorem fiber_mk (b : C) (f : G.obj (Opposite.op b)) :
    (mk b f).fiber = f :=
  rfl

/-- Every object of `CoGrothendieck G` is `mk` applied to its own base
and fiber. -/
@[simp]
theorem mk_base_fiber (X : CoGrothendieck G) : mk X.base X.fiber = X :=
  rfl

/-- Construct a morphism of `CoGrothendieck G` from a base morphism in
`C` and a fiber morphism. -/
def homMk {X Y : CoGrothendieck G} (base : X.base ⟶ Y.base)
    (fiber : X.fiber ⟶ (G.map base.op).toFunctor.obj Y.fiber) :
    X ⟶ Y :=
  Quiver.Hom.op (GrothendieckOp.homMk base.op fiber)

/-- The base morphism of a morphism of `CoGrothendieck G`, as a
morphism of `C`. -/
def homBase {X Y : CoGrothendieck G} (f : X ⟶ Y) : X.base ⟶ Y.base :=
  Quiver.Hom.unop (GrothendieckOp.homBase (Quiver.Hom.unop f))

/-- The fiber morphism of a morphism of `CoGrothendieck G`. -/
def homFiber {X Y : CoGrothendieck G} (f : X ⟶ Y) :
    X.fiber ⟶ (G.map (homBase f).op).toFunctor.obj Y.fiber :=
  GrothendieckOp.homFiber (Quiver.Hom.unop f)

/-- `homMk` recovers the base component on the nose. -/
@[simp]
theorem homBase_homMk {X Y : CoGrothendieck G} (b : X.base ⟶ Y.base)
    (φ : X.fiber ⟶ (G.map b.op).toFunctor.obj Y.fiber) :
    homBase (homMk b φ) = b :=
  rfl

/-- `homMk` recovers the fiber component on the nose. -/
@[simp]
theorem homFiber_homMk {X Y : CoGrothendieck G} (b : X.base ⟶ Y.base)
    (φ : X.fiber ⟶ (G.map b.op).toFunctor.obj Y.fiber) :
    homFiber (homMk b φ) = φ :=
  rfl

/-- Every morphism of `CoGrothendieck G` is `homMk` applied to its own
base and fiber components. -/
@[simp]
theorem homMk_base_fiber {X Y : CoGrothendieck G} (f : X ⟶ Y) :
    homMk (homBase f) (homFiber f) = f :=
  rfl

/-- Two morphisms of `CoGrothendieck G` agree once their base
components agree and their fiber components agree after transport
along that agreement. -/
@[ext (iff := false)]
theorem hom_ext {X Y : CoGrothendieck G} (f g : X ⟶ Y)
    (hbase : homBase f = homBase g)
    (hfiber : homFiber f ≫ eqToHom (by rw [hbase]) = homFiber g) :
    f = g := by
  apply Quiver.Hom.unop_inj
  refine GrothendieckOp.hom_ext _ _ (Quiver.Hom.unop_inj hbase) ?_
  exact hfiber

/-- `homBase` sends the identity morphism to the identity morphism. -/
@[simp]
theorem homBase_id (X : CoGrothendieck G) : homBase (𝟙 X) = 𝟙 X.base :=
  rfl

/-- `homFiber` of the identity morphism is the canonical transport
isomorphism. -/
@[simp]
theorem homFiber_id (X : CoGrothendieck G) :
    homFiber (𝟙 X) = eqToHom (by simp) :=
  GrothendieckOp.homFiber_id (Opposite.unop X)

/-- `homBase` is functorial: it sends composition to composition. -/
@[simp]
theorem homBase_comp {X Y Z : CoGrothendieck G} (f : X ⟶ Y)
    (g : Y ⟶ Z) : homBase (f ≫ g) = homBase f ≫ homBase g :=
  rfl

/-- `homFiber` of a composite is the composite of the fiber morphisms,
transported along the base functoriality. -/
@[simp]
theorem homFiber_comp {X Y Z : CoGrothendieck G} (f : X ⟶ Y)
    (g : Y ⟶ Z) :
    homFiber (f ≫ g) =
      homFiber f ≫ (G.map (homBase f).op).toFunctor.map (homFiber g) ≫
        eqToHom (by simp) :=
  GrothendieckOp.homFiber_comp (Quiver.Hom.unop g) (Quiver.Hom.unop f)

/-- The projection `CoGrothendieck G ⥤ C` onto the base category. -/
def forget (G : Cᵒᵖ ⥤ Cat.{v₂, u₂}) : CoGrothendieck G ⥤ C :=
  (GrothendieckOp.forget G).leftOp

/-- `forget` sends an object of `CoGrothendieck G` to its base object. -/
@[simp]
theorem forget_obj (X : CoGrothendieck G) : (forget G).obj X = X.base :=
  rfl

/-- `forget` sends a morphism of `CoGrothendieck G` to its base morphism. -/
@[simp]
theorem forget_map {X Y : CoGrothendieck G} (f : X ⟶ Y) :
    (forget G).map f = homBase f :=
  rfl

/-- A natural transformation `α : G ⟶ G'` induces a functor
`CoGrothendieck G ⥤ CoGrothendieck G'` (covariantly in `α`). -/
def map {G G' : Cᵒᵖ ⥤ Cat.{v₂, u₂}} (α : G ⟶ G') :
    CoGrothendieck G ⥤ CoGrothendieck G' :=
  (GrothendieckOp.map α).op

/-- `map` sends `mk b f` to `mk b` applied to the pushforward of `f` along `α`. -/
@[simp]
theorem map_obj_mk {G G' : Cᵒᵖ ⥤ Cat.{v₂, u₂}} (α : G ⟶ G') (b : C)
    (f : G.obj (Opposite.op b)) :
    (map α).obj (mk b f) =
      mk b ((α.app (Opposite.op b)).toFunctor.obj f) :=
  rfl

/-- `map` leaves the base component of a morphism unchanged. -/
@[simp]
theorem homBase_map_map {G G' : Cᵒᵖ ⥤ Cat.{v₂, u₂}} (α : G ⟶ G')
    {X Y : CoGrothendieck G} (f : X ⟶ Y) :
    homBase ((map α).map f) = homBase f :=
  rfl

/-- `map` transports the fiber component of a morphism along `α`, up to the
canonical isomorphism supplied by `α`'s naturality. -/
@[simp]
theorem homFiber_map_map {G G' : Cᵒᵖ ⥤ Cat.{v₂, u₂}} (α : G ⟶ G')
    {X Y : CoGrothendieck G} (f : X ⟶ Y) :
    homFiber ((map α).map f) =
      (α.app (Opposite.op X.base)).toFunctor.map (homFiber f) ≫
        eqToHom (congrArg
          (fun p : G.obj (Opposite.op Y.base) ⟶
              G'.obj (Opposite.op X.base) ↦
            p.toFunctor.obj Y.fiber)
          (α.naturality ((homBase f).op))) :=
  GrothendieckOp.homFiber_map_map α (Quiver.Hom.unop f)

/-- `map` sends the identity natural transformation to the identity functor. -/
theorem map_id_eq (G : Cᵒᵖ ⥤ Cat.{v₂, u₂}) :
    map (𝟙 G) = 𝟭 (CoGrothendieck G) := by
  rw [map, GrothendieckOp.map_id_eq]
  rfl

/-- `map` sends composition of natural transformations to composition of
functors. -/
theorem map_comp_eq {G G' G'' : Cᵒᵖ ⥤ Cat.{v₂, u₂}} (α : G ⟶ G')
    (β : G' ⟶ G'') : map (α ≫ β) = map α ⋙ map β := by
  rw [map, GrothendieckOp.map_comp_eq]
  rfl

/-- `map (𝟙 G)` is the identity functor, as an isomorphism. -/
def mapIdIso (G : Cᵒᵖ ⥤ Cat.{v₂, u₂}) : map (𝟙 G) ≅ 𝟭 (CoGrothendieck G) :=
  eqToIso (map_id_eq G)

/-- `map` sends composition of natural transformations to composition
of functors, as an isomorphism. -/
def mapCompIso {G G' G'' : Cᵒᵖ ⥤ Cat.{v₂, u₂}} (α : G ⟶ G')
    (β : G' ⟶ G'') : map (α ≫ β) ≅ map α ⋙ map β :=
  eqToIso (map_comp_eq α β)

/-- The `CoGrothendieck` construction as a functor from `(↑E)ᵒᵖ ⥤ Cat`
to the over category of `E` in `Cat`: apply `GrothendieckOp.functor`
over the base `(↑E)ᵒᵖ`, oppositize the total category with
`Over.post Cat.opFunctor`, and retarget along `unopUnop`. -/
def functor {E : Cat.{v, u}} :
    ((↑E)ᵒᵖ ⥤ Cat.{v, u}) ⥤ Over (T := Cat.{v, u}) E :=
  GrothendieckOp.functor (E := Cat.of (↑E)ᵒᵖ) ⋙
    Over.post Cat.opFunctor ⋙ Over.map (unopUnop ↑E).toCatHom

/-- `functor` sends `G` to an over-object whose hom component is
`forget G`. -/
@[simp]
theorem functor_obj_hom {E : Cat.{v, u}} (G : (↑E)ᵒᵖ ⥤ Cat.{v, u}) :
    (functor.obj G).hom = (forget G).toCatHom :=
  rfl

/-- The `CoGrothendieck` construction as a functor to `Cat`. -/
def functorToCat {E : Cat.{v, u}} :
    ((↑E)ᵒᵖ ⥤ Cat.{v, u}) ⥤ Cat.{v, u} :=
  functor ⋙ Over.forget E

/-- `functorToCat` sends a functor to the `CoGrothendieck` construction
on it. -/
@[simp]
theorem functorToCat_obj {E : Cat.{v, u}} (G : (↑E)ᵒᵖ ⥤ Cat.{v, u}) :
    functorToCat.obj G = Cat.of (CoGrothendieck G) :=
  rfl

end CoGrothendieck

end CategoryTheory
