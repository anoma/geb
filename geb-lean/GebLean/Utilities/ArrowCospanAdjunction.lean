import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Cospan
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackCone
import Mathlib.CategoryTheory.Adjunction.Reflective

/-!
# Arrow-Cospan Coreflective Adjunction

Dual to `ArrowSpanAdjunction`: given a category
with constructive pullbacks, the arrow category is
a coreflective subcategory of the category of
cospan diagrams.

The inclusion sends an arrow `f : P ⟶ Q` to the
cospan `P ─[f]→ Q ←[𝟙]─ Q`. The coreflector
sends each cospan to the arrow given by the right
projection from its pullback.

The adjunction is parameterized by an explicit
choice of limit cone for each cospan, avoiding
`Classical.choice`.
-/

open CategoryTheory Limits

namespace GebLean

universe v u

variable {C : Type u} [Category.{v} C]

/-- The inclusion of the arrow category into the
category of cospan diagrams, sending an arrow
`f : P ⟶ Q` to the cospan
`P ─[f]→ Q ←[𝟙]─ Q`. -/
@[simps]
def arrowCospanInclusion
    (C : Type u) [Category.{v} C] :
    Arrow C ⥤ (WalkingCospan ⥤ C) where
  obj f := cospan f.hom (𝟙 f.right)
  map {f g} sq :=
    cospanHomMk sq.right sq.left sq.right
      sq.w.symm
      (by simp)
  map_id f := by
    apply NatTrans.ext
    funext j
    match j with
    | .one => simp
    | .left => simp
    | .right => simp
  map_comp {f g h} sq₁ sq₂ := by
    apply NatTrans.ext
    funext j
    match j with
    | .one => simp
    | .left => simp
    | .right => simp

/-- `arrowCospanInclusion` is fully faithful. -/
def arrowCospanInclusion.fullyFaithful :
    (arrowCospanInclusion C).FullyFaithful where
  preimage {f g} α :=
    Arrow.homMk (α.app .left) (α.app .right)
      (by
        have hinl :=
          α.naturality WalkingCospan.Hom.inl
        have hinr :=
          α.naturality WalkingCospan.Hom.inr
        simp at hinr
        simp [hinr] at hinl
        exact hinl.symm)
  map_preimage {f g} α := by
    apply NatTrans.ext
    funext j
    match j with
    | .one =>
      change α.app .right = α.app .one
      have h :=
        α.naturality WalkingCospan.Hom.inr
      simp at h
      exact h.symm
    | .left => simp
    | .right => simp
  preimage_map {f g} sq := by
    apply Arrow.hom_ext
    · rfl
    · rfl

instance : (arrowCospanInclusion C).Faithful :=
  arrowCospanInclusion.fullyFaithful.faithful

instance : (arrowCospanInclusion C).Full :=
  arrowCospanInclusion.fullyFaithful.full

/-- The coreflector from cospan diagrams to
arrows, sending each cospan to the arrow given
by the right projection from its pullback.
Parameterized by an explicit choice of limit
cone for each cospan. -/
def cospanArrowCoreflector
    (pullbacks :
      (S : WalkingCospan ⥤ C) → LimitCone S) :
    (WalkingCospan ⥤ C) ⥤ Arrow C where
  obj S :=
    Arrow.mk
      ((pullbacks S).cone.π.app WalkingCospan.right)
  map {S₁ S₂} α :=
    Arrow.homMk
      ((pullbacks S₂).isLimit.lift
        (Cone.mk (pullbacks S₁).cone.pt
          ((pullbacks S₁).cone.π ≫ α)))
      (α.app WalkingCospan.right)
      (by
        have := (pullbacks S₂).isLimit.fac
          (Cone.mk (pullbacks S₁).cone.pt
            ((pullbacks S₁).cone.π ≫ α))
          WalkingCospan.right
        dsimp at this
        exact this)
  map_id S := by
    apply Arrow.hom_ext
    · dsimp
      symm
      apply (pullbacks S).isLimit.uniq
        (Cone.mk (pullbacks S).cone.pt
          ((pullbacks S).cone.π ≫ 𝟙 S))
      intro j
      simp [Category.comp_id]
    · simp
  map_comp {S₁ S₂ S₃} α β := by
    apply Arrow.hom_ext
    · dsimp
      symm
      apply (pullbacks S₃).isLimit.uniq
        (Cone.mk (pullbacks S₁).cone.pt
          ((pullbacks S₁).cone.π ≫ (α ≫ β)))
      intro j
      rw [Category.assoc,
        (pullbacks S₃).isLimit.fac
          (Cone.mk (pullbacks S₂).cone.pt
            ((pullbacks S₂).cone.π ≫ β)) j]
      dsimp
      rw [← Category.assoc,
        (pullbacks S₂).isLimit.fac
          (Cone.mk (pullbacks S₁).cone.pt
            ((pullbacks S₁).cone.π ≫ α)) j]
      dsimp
      simp only [Category.assoc]
    · simp

/-- The cone over `cospan f.hom (𝟙 f.right)` with
point `f.left`, used to define the unit. -/
def arrowCospanAdjUnitCone
    (f : Arrow C) :
    Cone ((arrowCospanInclusion C).obj f) where
  pt := f.left
  π :=
    { app := fun j => match j with
        | .one => f.hom
        | .left => 𝟙 _
        | .right => f.hom
      naturality := by
        intro X Y h
        induction h with
        | id => simp
        | term j =>
          cases j <;>
            simp [arrowCospanInclusion] }

/-- The unit of the arrow-cospan adjunction at
an arrow `f`. Maps `f` into the coreflection
(the pullback arrow) via the universal
property. -/
def arrowCospanAdjUnitApp
    (pullbacks :
      (S : WalkingCospan ⥤ C) → LimitCone S)
    (f : Arrow C) :
    f ⟶ ((arrowCospanInclusion C ⋙
      cospanArrowCoreflector pullbacks).obj f) :=
  Arrow.homMk
    ((pullbacks _).isLimit.lift
      (arrowCospanAdjUnitCone f))
    (𝟙 _)
    (by
      dsimp [cospanArrowCoreflector]
      rw [Category.comp_id]
      exact (pullbacks _).isLimit.fac
        (arrowCospanAdjUnitCone f)
        WalkingCospan.right)

/-- The unit of the arrow-cospan adjunction as a
natural transformation. -/
def arrowCospanAdjUnit
    (pullbacks :
      (S : WalkingCospan ⥤ C) → LimitCone S) :
    𝟭 (Arrow C) ⟶
    arrowCospanInclusion C ⋙
      cospanArrowCoreflector pullbacks where
  app f := arrowCospanAdjUnitApp pullbacks f
  naturality {f g} sq := by
    apply Arrow.hom_ext
    · dsimp [arrowCospanAdjUnitApp,
        cospanArrowCoreflector]
      apply (pullbacks _).isLimit.hom_ext
      intro j
      simp only [Category.assoc,
        (pullbacks _).isLimit.fac]
      dsimp [arrowCospanAdjUnitCone]
      match j with
      | .one =>
        simp only [← Category.assoc,
          (pullbacks _).isLimit.fac]
        dsimp [arrowCospanAdjUnitCone]
        exact sq.w
      | .left =>
        simp only [← Category.assoc,
          (pullbacks _).isLimit.fac]
        simp
      | .right =>
        simp only [← Category.assoc,
          (pullbacks _).isLimit.fac]
        dsimp [arrowCospanAdjUnitCone]
        exact sq.w
    · simp [arrowCospanAdjUnitApp,
        cospanArrowCoreflector]

/-- The counit of the arrow-cospan adjunction at
a cospan `S`. Maps the inclusion of the
coreflection back to `S`. -/
def arrowCospanAdjCounitApp
    (pullbacks :
      (S : WalkingCospan ⥤ C) → LimitCone S)
    (S : WalkingCospan ⥤ C) :
    ((cospanArrowCoreflector pullbacks ⋙
      arrowCospanInclusion C).obj S) ⟶ S :=
  cospanHomMk
    (S.map WalkingCospan.Hom.inr)
    ((pullbacks S).cone.π.app WalkingCospan.left)
    (𝟙 _)
    (by
      dsimp [cospanArrowCoreflector,
        arrowCospanInclusion]
      exact ((pullbacks S).cone.w
        WalkingCospan.Hom.inr).trans
        ((pullbacks S).cone.w
          WalkingCospan.Hom.inl).symm)
    (by simp [arrowCospanInclusion,
      cospanArrowCoreflector])

/-- The counit of the arrow-cospan adjunction as
a natural transformation. -/
def arrowCospanAdjCounit
    (pullbacks :
      (S : WalkingCospan ⥤ C) → LimitCone S) :
    cospanArrowCoreflector pullbacks ⋙
      arrowCospanInclusion C ⟶
    𝟭 (WalkingCospan ⥤ C) where
  app S := arrowCospanAdjCounitApp pullbacks S
  naturality {S₁ S₂} α := by
    apply NatTrans.ext; funext j
    match j with
    | .one =>
      simp [arrowCospanAdjCounitApp,
        cospanArrowCoreflector]
    | .left =>
      dsimp [arrowCospanAdjCounitApp,
        cospanArrowCoreflector,
        arrowCospanInclusion]
      exact (pullbacks S₂).isLimit.fac
        (Cone.mk (pullbacks S₁).cone.pt
          ((pullbacks S₁).cone.π ≫ α))
        WalkingCospan.left
    | .right =>
      simp [arrowCospanAdjCounitApp,
        cospanArrowCoreflector,
        arrowCospanInclusion]

private theorem limit_hom_ext
    {J : Type*} [Category J]
    {F : J ⥤ C} {c : Cone F}
    (hc : IsLimit c)
    {W : C} {f g : W ⟶ c.pt}
    (h : ∀ j, f ≫ c.π.app j =
      g ≫ c.π.app j) : f = g := by
  let s := Cone.mk W
    ((Functor.const J).map f ≫ c.π)
  have hf : f = hc.lift s :=
    hc.uniq s f (fun j => by dsimp [s])
  have hg : g = hc.lift s :=
    hc.uniq s g (fun j => by
      dsimp [s]; exact (h j).symm)
  rw [hf, hg]

/-- The left triangle identity:
`inclusion.map (unit f) ≫ counit (inclusion f)
= 𝟙`. -/
theorem arrowCospanAdj_left_triangle
    (pullbacks :
      (S : WalkingCospan ⥤ C) → LimitCone S)
    (f : Arrow C) :
    (arrowCospanInclusion C).map
      (arrowCospanAdjUnitApp pullbacks f) ≫
    arrowCospanAdjCounitApp pullbacks
      ((arrowCospanInclusion C).obj f) =
    𝟙 _ := by
  ext j
  match j with
  | .one | .right =>
    simp [arrowCospanAdjUnitApp,
      arrowCospanAdjCounitApp,
      arrowCospanInclusion,
      cospanArrowCoreflector]
  | .left =>
    dsimp [arrowCospanAdjUnitApp,
      arrowCospanAdjCounitApp,
      arrowCospanInclusion,
      cospanArrowCoreflector]
    exact (pullbacks _).isLimit.fac
      (arrowCospanAdjUnitCone f)
      WalkingCospan.left

-- `linter.flexible` is locally disabled for
-- `arrowCospanAdj_right_triangle`: the proof
-- relies on `simp` (not `simp only`) to drive the
-- `(pullbacks _).isLimit.fac` rewrite after unfolding
-- `arrowCospanAdjUnitCone`.  `IsLimit.fac` is not
-- `@[simp]`-tagged but is reachable from `simp`'s
-- matcher via the lifted-cone projection, so the
-- linter's `simp only [...]` rewrite suggestion is
-- not equivalent.
set_option linter.flexible false in
/-- The right triangle identity:
`unit (coreflector S) ≫ coreflector.map
(counit S) = 𝟙`. -/
theorem arrowCospanAdj_right_triangle
    (pullbacks :
      (S : WalkingCospan ⥤ C) → LimitCone S)
    (S : WalkingCospan ⥤ C) :
    arrowCospanAdjUnitApp pullbacks
      ((cospanArrowCoreflector pullbacks).obj
        S) ≫
    (cospanArrowCoreflector pullbacks).map
      (arrowCospanAdjCounitApp pullbacks S) =
    𝟙 _ := by
  apply Arrow.hom_ext
  · dsimp [arrowCospanAdjUnitApp,
      arrowCospanAdjCounitApp,
      cospanArrowCoreflector, arrowCospanInclusion]
    apply limit_hom_ext
      (pullbacks S).isLimit
    intro j
    rw [Category.id_comp,
      Category.assoc,
      (pullbacks S).isLimit.fac]
    simp [arrowCospanAdjUnitCone]
    match j with
    | .one =>
      exact (pullbacks S).cone.w
        WalkingCospan.Hom.inr
    | .left => simp
    | .right => simp
  · simp [arrowCospanAdjUnitApp,
      arrowCospanAdjCounitApp,
      cospanArrowCoreflector]

/-- The adjunction
`arrowCospanInclusion C ⊣
cospanArrowCoreflector pullbacks`,
parameterized by an explicit limit cone
assignment. -/
def arrowCospanAdj
    (pullbacks :
      (S : WalkingCospan ⥤ C) → LimitCone S) :
    arrowCospanInclusion C ⊣
      cospanArrowCoreflector pullbacks :=
  Adjunction.mkOfUnitCounit {
    unit := arrowCospanAdjUnit pullbacks
    counit := arrowCospanAdjCounit pullbacks
    left_triangle := by
      apply NatTrans.ext; funext f
      have h := arrowCospanAdj_left_triangle pullbacks f
      simpa [arrowCospanAdjUnit, arrowCospanAdjCounit]
        using h
    right_triangle := by
      apply NatTrans.ext; funext S
      have h := arrowCospanAdj_right_triangle pullbacks S
      simpa [arrowCospanAdjUnit, arrowCospanAdjCounit]
        using h
  }

/-- `Arrow C` is a coreflective subcategory of
`WalkingCospan ⥤ C` via the arrow-cospan
inclusion, given an explicit limit cone
assignment.

This is a `@[reducible] def` rather than an
`instance`: the explicit `pullbacks` argument is
not inferable from
`Coreflective (arrowCospanInclusion C)`, so
typeclass resolution cannot synthesise it.  Call
sites that have a chosen `pullbacks` family in
scope can promote this to a local `instance` via
`local instance := arrowCospanCoreflective ...`. -/
@[reducible] def arrowCospanCoreflective
    (pullbacks :
      (S : WalkingCospan ⥤ C) → LimitCone S) :
    Coreflective (arrowCospanInclusion C) where
  R := cospanArrowCoreflector pullbacks
  adj := arrowCospanAdj pullbacks

end GebLean
