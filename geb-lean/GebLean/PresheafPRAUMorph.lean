import GebLean.PresheafPRA
import Mathlib.CategoryTheory.Limits.Opposites
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.Pi
import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Limits and Colimits in CoprodCovarRepCat

This module establishes the existence of limits in
`CoprodCovarRepCat C` under appropriate conditions
on `C`.

The strategy uses mathlib's `op`-based infrastructure
directly (no dependence on `op'`):

1. `Grothendieck (familyFunctor C)` has colimits
   (via `hasColimitsOfShape_grothendieck`)

2. `CoprodCovarRepCat C = (Grothendieck ...)ᵒᵖ` has
   limits (via `hasLimits_op_of_hasColimits`)

3. Limits of arbitrary shape `J` in
   `CoprodCovarRepCat C` are computed as: positions
   are sections of the position diagram, and fibers
   are colimits of the fiber diagram in `C`.
-/

namespace GebLean

open CategoryTheory CategoryTheory.Limits

universe u v w

variable {C : Type u} [Category.{v} C]

/-! ## Position functor for diagrams -/

section PositionFunctor

variable {J : Type w} [Category.{w} J]
variable (D : J ⥤ CoprodCovarRepCat.{u, v, w} C)

/--
The position functor of a diagram
`D : J ⥤ CoprodCovarRepCat C`. Sends `j` to the
index type `ccrNewIndex (D.obj j)` and a morphism
`f` to the reindexing function `ccrNewReindex`.
-/
def ccrDiagPosFunctor : J ⥤ Type w := D ⋙ ccrNewIndexFunctor C

end PositionFunctor

/-! ## Limit construction for CoprodCovarRepCat

The limit of a diagram `D : J ⥤ CoprodCovarRepCat C`
is constructed as follows:

- Positions: the sections of the position functor
  `ccrDiagPosFunctor D`, i.e., compatible families
  `(x_j)_j` where `ccrNewReindex (D.map f) x_{j₁} =
  x_{j₂}` for all `f : j₁ ⟶ j₂`.

- Directions at `z = (x_j)_j`: the colimit in `C`
  of the contravariant diagram
  `j ↦ ccrNewFamily (D.obj j) (x_j)`.
-/

section LimitConstruction

variable {J : Type w} [Category.{w} J]
variable (D : J ⥤ CoprodCovarRepCat.{u, v, w} C)

/--
The type of compatible position families for
`D`. An element consists of a choice of position
`x_j : ccrNewIndex (D.obj j)` for each `j`, such
that `ccrNewReindex (D.map f) x_{j₁} = x_{j₂}`
for all morphisms `f : j₁ ⟶ j₂`.
-/
def ccrLimPosSections :=
  (ccrDiagPosFunctor D).sections

/--
The projection of a compatible position family
to position at `j`.
-/
def ccrLimPosProj
    (z : ccrLimPosSections D) (j : J) :
    ccrNewIndex (D.obj j) :=
  z.val j

/--
Compatibility of position projections with the
diagram morphisms.
-/
lemma ccrLimPosProj_compat
    (z : ccrLimPosSections D)
    {j₁ j₂ : J} (f : j₁ ⟶ j₂) :
    ccrNewReindex (D.map f)
      (ccrLimPosProj D z j₁) =
      ccrLimPosProj D z j₂ :=
  z.property f

/--
The fiber morphism at a compatible position family,
adjusted for position compatibility.
-/
def ccrLimFiberMap
    (z : ccrLimPosSections D)
    {j₁ j₂ : J} (f : j₁ ⟶ j₂) :
    ccrNewFamily (D.obj j₂)
      (ccrLimPosProj D z j₂) ⟶
    ccrNewFamily (D.obj j₁)
      (ccrLimPosProj D z j₁) :=
  eqToHom (congrArg
    (ccrNewFamily (D.obj j₂))
    (ccrLimPosProj_compat D z f).symm) ≫
  ccrNewFiberMor (D.map f)
    (ccrLimPosProj D z j₁)

private lemma ccrLimFiberMap_id_aux
    {P : CoprodCovarRepCat.{u, v, w} C}
    {m : P ⟶ P} (hm : m = 𝟙 P)
    (i : ccrNewIndex P)
    (h : ccrNewReindex m i = i) :
    eqToHom (congrArg (ccrNewFamily P) h.symm)
      ≫ ccrNewFiberMor m i =
      𝟙 _ := by
  subst hm
  simp only [ccrNewFiberMor]
  -- (𝟙 P).unop.fiber i = eqToHom _ in
  -- the pi category, which at index i gives
  -- eqToHom in C.
  have : (𝟙 P).unop.fiber i =
      eqToHom (congrArg (ccrNewFamily P)
        h) := by
    simp only [ccrNewFamily]
    rfl
  rw [this, eqToHom_trans, eqToHom_refl]

lemma ccrLimFiberMap_id
    (z : ccrLimPosSections D) (j : J) :
    ccrLimFiberMap D z (𝟙 j) =
      𝟙 _ := by
  exact ccrLimFiberMap_id_aux (D.map_id j)
    (ccrLimPosProj D z j)
    (ccrLimPosProj_compat D z (𝟙 j))

private lemma ccrLimFiberMap_comp_aux
    {P Q R : CoprodCovarRepCat.{u, v, w} C}
    {mf : P ⟶ Q} {mg : Q ⟶ R}
    {mfg : P ⟶ R}
    (hcomp : mfg = mf ≫ mg)
    (iP : ccrNewIndex P) (iQ : ccrNewIndex Q)
    (iR : ccrNewIndex R)
    (hf : ccrNewReindex mf iP = iQ)
    (hg : ccrNewReindex mg iQ = iR)
    (hfg : ccrNewReindex mfg iP = iR) :
    eqToHom (congrArg (ccrNewFamily R)
        hfg.symm) ≫
      ccrNewFiberMor mfg iP =
    (eqToHom (congrArg (ccrNewFamily R)
        hg.symm) ≫
      ccrNewFiberMor mg iQ) ≫
    (eqToHom (congrArg (ccrNewFamily Q)
        hf.symm) ≫
      ccrNewFiberMor mf iP) := by
  subst hcomp
  subst hf
  simp only [eqToHom_refl, Category.id_comp]
  rw [ccrNewFiberMor_comp]
  simp [Category.assoc]

lemma ccrLimFiberMap_comp
    (z : ccrLimPosSections D)
    {j₁ j₂ j₃ : J}
    (f : j₁ ⟶ j₂) (g : j₂ ⟶ j₃) :
    ccrLimFiberMap D z (f ≫ g) =
    ccrLimFiberMap D z g ≫
      ccrLimFiberMap D z f := by
  exact ccrLimFiberMap_comp_aux
    (D.map_comp f g)
    (ccrLimPosProj D z j₁)
    (ccrLimPosProj D z j₂)
    (ccrLimPosProj D z j₃)
    (ccrLimPosProj_compat D z f)
    (ccrLimPosProj_compat D z g)
    (ccrLimPosProj_compat D z (f ≫ g))

/--
The fiber functor at a compatible position family
`z`. For each `j : Jᵒᵖ`, gives the direction object
`ccrNewFamily (D.obj j.unop) (π_j z)`. Morphisms
are the fiber morphisms from `D`, going backward.
-/
def ccrDiagFiberFunctor
    (z : ccrLimPosSections D) :
    Jᵒᵖ ⥤ C where
  obj jop :=
    ccrNewFamily (D.obj jop.unop)
      (ccrLimPosProj D z jop.unop)
  map {j₁op j₂op} fop :=
    ccrLimFiberMap D z fop.unop
  map_id jop :=
    ccrLimFiberMap_id D z jop.unop
  map_comp {j₁op j₂op j₃op} fop gop := by
    change ccrLimFiberMap D z
        (gop.unop ≫ fop.unop) =
      ccrLimFiberMap D z fop.unop ≫
        ccrLimFiberMap D z gop.unop
    exact ccrLimFiberMap_comp D z
      gop.unop fop.unop

/-! ## Type equality for CoprodCovarRepCat -/

/--
The underlying type of `CoprodCovarRepCat C` is
definitionally equal to
`(Grothendieck (familyFunctor C))ᵒᵖ`.
-/
lemma ccrNewTypeEq :
    ↑(CoprodCovarRepCat.{u, v, w} C) =
    (Grothendieck
      (familyFunctor.{u, v, w} C))ᵒᵖ :=
  rfl

end LimitConstruction

/-! ## HasLimitsOfShape for CoprodCovarRepCat

The Grothendieck construction on the family functor
has colimits of shape `J` when:
- The base `(Type w)ᵒᵖ` has colimits of shape `J`
  (equivalently, `Type w` has limits of shape `Jᵒᵖ`)
- Each fiber `X → C` has colimits of shape `J`
  (equivalently, `C` has colimits of shape `J`)

Colimits in the Grothendieck construction then give
limits in the opposite category
`CoprodCovarRepCat C`.
-/

section HasLimitsOfShapeCCR

variable {J : Type w} [Category.{w} J]
variable {C : Type u} [Category.{v} C]

/--
The Pi category `I → C` has colimits of shape `J`
when `C` does. Follows from the equivalence
`(I → C) ≌ (Discrete I ⥤ C)` and the functor
category colimits instance.
-/
theorem piHasColimitsOfShape
    {I : Type w} [HasColimitsOfShape J C] :
    HasColimitsOfShape J (I → C) :=
  Adjunction.hasColimitsOfShape_of_equivalence
    (piEquivalenceFunctorDiscrete I C).functor

/--
Each fiber of `familyFunctor C` — the Pi category
`X.unop → C` — has colimits of shape `J` when `C`
does.
-/
theorem grothendieckFiberHasColimitsOfShape
    [HasColimitsOfShape J C]
    (X : (Type w)ᵒᵖ) :
    HasColimitsOfShape J
      ↑((familyFunctor.{u, v, w} C).obj X) :=
  piHasColimitsOfShape

/--
The base category `(Type w)ᵒᵖ` has colimits of
shape `J` when `Type w` has limits of shape `Jᵒᵖ`.
-/
theorem typeOpHasColimitsOfShape :
    HasColimitsOfShape J (Type w)ᵒᵖ :=
  hasColimitsOfShape_op_of_hasLimitsOfShape

end HasLimitsOfShapeCCR

/-! ## Explicit limit construction for CoprodCovarRepCat

We build an explicit `HasLimit` instance for any
diagram `D : J ⥤ CoprodCovarRepCat C` by
constructing a `LimitCone`. The vertex has:
- Positions: the sections of the position diagram
- Fibers: colimits in `C` of the fiber diagrams
-/

section ExplicitLimit

variable {J : Type w} [Category.{w} J]
variable {C : Type u} [Category.{v} C]
variable [HasColimitsOfShape Jᵒᵖ C]
variable (D : J ⥤ CoprodCovarRepCat.{u, v, w} C)

private def ccrHasLimit_iotaGr
    (getCocone :
      ∀ (z : ccrLimPosSections D),
        ColimitCocone
          (ccrDiagFiberFunctor D z))
    (j : Jᵒᵖ) :
    D.leftOp.obj j ⟶
      (⟨Opposite.op (ccrLimPosSections D),
        fun z =>
          (getCocone z).cocone.pt⟩ :
        Grothendieck
          (familyFunctor.{u, v, w} C)) :=
  { base := Quiver.Hom.op
      (fun z : ccrLimPosSections D =>
        ccrLimPosProj D z j.unop)
    fiber := fun z =>
      (getCocone z).cocone.ι.app j }

omit [HasColimitsOfShape Jᵒᵖ C] in
private lemma ccrHasLimit_cocone_nat
    (getCocone :
      ∀ (z : ccrLimPosSections D),
        ColimitCocone
          (ccrDiagFiberFunctor D z))
    (j₁ j₂ : Jᵒᵖ)
    (f : j₁ ⟶ j₂) :
    D.leftOp.map f ≫
      ccrHasLimit_iotaGr D getCocone j₂ =
      ccrHasLimit_iotaGr D getCocone j₁ := by
  unfold ccrHasLimit_iotaGr
  have hbase :
      (D.leftOp.map f).base ≫
        Quiver.Hom.op
          (fun z : ccrLimPosSections D =>
            ccrLimPosProj D z j₂.unop) =
        Quiver.Hom.op
          (fun z : ccrLimPosSections D =>
            ccrLimPosProj D z j₁.unop) := by
    apply Quiver.Hom.unop_inj
    funext z
    exact ccrLimPosProj_compat D z f.unop
  apply Grothendieck.ext _ _ hbase
  -- The fiber goal is at the Pi-category
  -- level: eqToHom _ ≫ (f ≫ g).fiber = rhs
  -- Rewrite using Grothendieck comp_fiber.
  rw [Grothendieck.comp_fiber,
    ← Category.assoc (eqToHom _)
      (eqToHom _) _,
    eqToHom_trans]
  funext z
  dsimp only []
  have hnat :=
    (getCocone z).cocone.w f
  simp only [] at hnat
  rw [← hnat]
  simp only [ccrDiagFiberFunctor,
    ccrLimFiberMap, ccrNewFiberMor,
    Category.assoc]
  have pi_eqToHom_comp_apply :
      ∀ {I : Type w} {C' : Type u}
        [inst : Category.{v} C']
        {X Y Z : I → C'}
        (h : X = Y)
        (f : Y ⟶ Z)
        (i : I),
        (eqToHom h ≫ f) i =
          eqToHom (congrFun h i) ≫ f i := by
    intro I C' inst X Y Z h f i
    subst h; rfl
  rw [pi_eqToHom_comp_apply]
  congr 1

private def ccrHasLimit_descBase
    (s : Cocone D.leftOp)
    (x : s.pt.base.unop) :
    ccrLimPosSections D :=
  ⟨fun j =>
    (s.ι.app
      (Opposite.op j)).base.unop x,
    fun {j₁ j₂} f => by
      have nat := s.w (Quiver.Hom.op f)
      exact congrFun (congrArg
        (fun h =>
          Quiver.Hom.unop h.base)
        nat) x⟩

omit [HasColimitsOfShape Jᵒᵖ C] in
private lemma ccrHasLimit_desc_nat
    (s : Cocone D.leftOp)
    (x : s.pt.base.unop)
    (j₁ j₂ : Jᵒᵖ) (f : j₁ ⟶ j₂) :
    (ccrDiagFiberFunctor D
      (ccrHasLimit_descBase D s x)).map
        f ≫
      (s.ι.app j₂).fiber x =
    (s.ι.app j₁).fiber x ≫
      ((Functor.const Jᵒᵖ).obj
        (s.pt.fiber x)).map f := by
  -- Remove ≫ Functor.const.map f (= 𝟙).
  change (ccrDiagFiberFunctor D
    (ccrHasLimit_descBase D s x)).map
      f ≫
    (s.ι.app j₂).fiber x =
    (s.ι.app j₁).fiber x ≫ 𝟙 _
  rw [Category.comp_id]
  -- Unfold ccrDiagFiberFunctor.map f.
  simp only [ccrDiagFiberFunctor,
    ccrLimFiberMap, ccrNewFiberMor,
    Category.assoc]
  -- Extract from s.w f.
  have nat : D.leftOp.map f ≫
      s.ι.app j₂ = s.ι.app j₁ := by
    rw [← s.w f]
  -- Extract fiber at x from nat.
  have hfib := congrFun
    (Grothendieck.congr nat) x
  rw [Grothendieck.comp_fiber] at hfib
  rw [pi_eqToHom_comp_apply,
    pi_eqToHom_comp_apply] at hfib
  rw [pi_comp_apply] at hfib
  -- hfib:
  --   eqToHom p ≫ familyBif_stuff x
  --     ≫ ι_j₂ x
  --   = eqToHom q ≫ ι_j₁ x
  -- Goal:
  --   eqToHom r ≫ D_fiber ≫ ι_j₂ x
  --   = ι_j₁ x
  -- `familyBif_stuff x` and `D_fiber` are
  -- (extensionally) the same morphism but
  -- expressed through different
  -- compositions. The eqToHom proofs differ.
  -- Factor out the common part.
  -- First, left-cancel eqToHom from hfib.
  rw [eqToHom_comp_iff] at hfib
  rw [← Category.assoc,
    eqToHom_trans] at hfib
  -- hfib: familyBif_stuff x ≫ ι_j₂ x
  --   = eqToHom _ ≫ ι_j₁ x
  -- Goal: eqToHom _ ≫ D_fiber ≫ ι_j₂ x
  --   = ι_j₁ x
  -- Use eqToHom_comp_iff to also left-cancel
  -- from goal, getting:
  -- D_fiber ≫ ι_j₂ x = eqToHom _ ≫ ι_j₁ x
  rw [eqToHom_comp_iff]
  -- Goal: D_fiber ≫ ι_j₂ x
  --   = eqToHom _.symm ≫ ι_j₁ x
  -- hfib: familyBif_stuff x ≫ ι_j₂ x
  --   = eqToHom _ ≫ ι_j₁ x
  -- D_fiber and familyBif_stuff x are
  -- definitionally equal (both are
  -- .unop.fiber at the same index).
  -- Use proof irrelevance on eqToHom.
  convert hfib using 2

/--
`HasLimit D` for any diagram
`D : J ⥤ CoprodCovarRepCat C`, given that `C` has
colimits of shape `Jᵒᵖ`.
-/
theorem ccrHasLimit : HasLimit D := by
  have getCocone :
      ∀ (z : ccrLimPosSections D),
        ColimitCocone
          (ccrDiagFiberFunctor D z) :=
    fun z => getColimitCocone _
  let vtxGr : Grothendieck
      (familyFunctor.{u, v, w} C) :=
    ⟨Opposite.op (ccrLimPosSections D),
      fun z => (getCocone z).cocone.pt⟩
  let iotaGr :=
    ccrHasLimit_iotaGr D getCocone
  -- Build cocone.
  let cc : Cocone D.leftOp :=
    { pt := vtxGr
      ι :=
        { app := iotaGr
          naturality := fun {j₁ j₂} f => by
            change D.leftOp.map f ≫
              iotaGr j₂ =
              iotaGr j₁ ≫ 𝟙 _
            rw [Category.comp_id]
            exact ccrHasLimit_cocone_nat
              D getCocone j₁ j₂ f } }
  -- Build desc: vtxGr ⟶ s.pt for each
  -- cocone s over D.leftOp.
  let desc (s : Cocone D.leftOp) :
      vtxGr ⟶ s.pt :=
    { base := Quiver.Hom.op
        (ccrHasLimit_descBase D s)
      fiber := fun x =>
        -- x : s.pt.base.unop
        -- Need: vtxGr.fiber(descBase x)
        --   ⟶ s.pt.fiber x
        -- vtxGr.fiber z =
        --   (getCocone z).cocone.pt
        -- Use the colimit universal
        -- property of getCocone.
        (getCocone
          (ccrHasLimit_descBase D s
            x)).isColimit.desc
          { pt := s.pt.fiber x
            ι :=
              { app := fun j =>
                  (s.ι.app j).fiber x
                naturality :=
                  fun {j₁ j₂} f =>
                    ccrHasLimit_desc_nat
                      D s x j₁ j₂ f
              }
          }
    }
  -- Abbreviation for the descent cocone.
  let descCocone
      (s : Cocone D.leftOp)
      (x : s.pt.base.unop) :
      Cocone (ccrDiagFiberFunctor D
        (ccrHasLimit_descBase D s x)) :=
    { pt := s.pt.fiber x
      ι :=
        { app := fun j =>
            (s.ι.app j).fiber x
          naturality :=
            fun {j₁ j₂} f =>
              ccrHasLimit_desc_nat
                D s x j₁ j₂ f
        }
    }
  -- Build IsColimit for cc.
  -- The fac proof: iotaGr j ≫ desc s
  --   = s.ι.app j.
  -- We prove this by showing both base
  -- and fiber components are equal.
  -- Build IsColimit cc.
  have isColim : IsColimit cc := by
    refine
      { desc := desc
        fac := fun s j => ?fac
        uniq := fun s m hm => ?uniq }
    case fac =>
      exact Grothendieck.ext _ _ rfl (by
        rw [Grothendieck.comp_fiber]
        funext x
        -- Goal is (A ≫ B ≫ C ≫ D) x = E
        -- Reassociate and apply pointwise.
        rw [← Category.assoc (eqToHom _)
          (eqToHom _) _,
          eqToHom_trans]
        rw [pi_eqToHom_comp_apply,
          pi_comp_apply]
        -- Use colimit fac via convert.
        have fac :=
          (getCocone
            (ccrHasLimit_descBase D s
              x)).isColimit.fac
            (descCocone s x) j
        simp only [] at fac
        -- fac: ι.app j ≫ desc = leg j
        -- Goal: eqToHom _ ≫ stuff x
        --   ≫ desc_fiber x = leg j x
        -- Chain: eqToHom _ ≫ stuff x
        --   should equal ι.app j.
        rw [← Category.assoc]
        -- Use convert with fac.
        -- The (desc s).fiber x IS the
        -- colimit descent.
        -- The composition should match fac
        -- up to definitional unfolding.
        convert fac using 2
        -- Remaining: eqToHom ≫ stuff = ι.
        -- The eqToHom maps between fiber
        -- types at equal indices.
        -- stuff = familyBifunctor_map at x
        -- = (cc.ι.app j).fiber
        --   ((desc s).base.unop x)
        -- = (getCocone (descBase x))
        --   .cocone.ι.app j
        -- (by definition of iotaGr).
        -- The eqToHom is between the same
        -- types (the indices are def. equal).
        simp only [eqToHom_refl,
          Category.id_comp]
        rfl)
    case uniq =>
      -- Use cases on m to enable subst.
      obtain ⟨m_base, m_fiber⟩ := m
      have hbase :
          m_base = (desc s).base := by
        apply Quiver.Hom.unop_inj
        funext x
        apply Subtype.ext
        funext j
        exact congrFun (congrArg
          Quiver.Hom.unop (congrArg
            Grothendieck.Hom.base
            (hm (Opposite.op j)))) x
      subst hbase
      -- Now m = ⟨(desc s).base, m_fiber⟩.
      -- Need: ⟨base, m_fiber⟩ = desc s.
      -- The base is already equal, so
      -- ext gives: m_fiber = (desc s).fiber.
      refine Grothendieck.ext _ _ rfl ?_
      -- Fiber: eqToHom rfl ≫ m_fiber
      --   = (desc s).fiber.
      -- eqToHom rfl = 𝟙.
      funext x
      simp only [eqToHom_refl,
        Category.id_comp]
      -- m_fiber x = (desc s).fiber x
      -- Use colimit uniqueness.
      apply (getCocone
        (ccrHasLimit_descBase D s
          x)).isColimit.uniq
        (descCocone s x)
      intro j
      -- Need: ι j ≫ m_fiber x
      --   = (s.ι.app j).fiber x
      -- From hm j:
      -- ⟨(desc s).base, m_fiber⟩ composed
      -- with iotaGr j = s.ι.app j.
      have hj := hm j
      -- Extract fiber at x from hj.
      have hfibj :=
        congrFun
          (Grothendieck.congr hj) x
      rw [Grothendieck.comp_fiber] at hfibj
      simp only [eqToHom_refl,
        Category.id_comp] at hfibj
      exact hfibj
  exact HasLimit.mk
    { cone := coneOfCoconeLeftOp cc
      isLimit :=
        isLimitConeOfCoconeLeftOp D isColim }

end ExplicitLimit

/-! ## HasLimitsOfShape for CoprodCovarRepCat

Packaging `ccrHasLimit` into typeclass instances
enables mathlib's limit functor `lim` and the
adjunction `constLimAdj : Functor.const J ⊣ lim`.
-/

section LimitInstances

variable {J : Type w} [Category.{w} J]
variable {C : Type u} [Category.{v} C]

/--
`CoprodCovarRepCat C` has limits of shape `J` when
`C` has colimits of shape `Jᵒᵖ`.
-/
instance ccrHasLimitsOfShape
    [HasColimitsOfShape Jᵒᵖ C] :
    HasLimitsOfShape J
      (↑(CoprodCovarRepCat.{u, v, w} C)) :=
  ⟨fun D => ccrHasLimit D⟩

end LimitInstances

section LimitSize

variable {C : Type u} [Category.{v} C]

/--
`CoprodCovarRepCat C` has all limits of size
`(w, w)` when `C` has all colimits of that size.
-/
instance ccrHasLimitsOfSize
    [HasColimitsOfSize.{w, w} C] :
    HasLimitsOfSize.{w, w}
      (↑(CoprodCovarRepCat.{u, v, w} C)) :=
  ⟨fun _ _ => inferInstance⟩

end LimitSize

/-! ## Computable Limit Functor

Mathlib's `lim` and `constLimAdj` are
not computable (they use `choice` to
select limit cones). To obtain a computable limit
functor for `CoprodCovarRepCat C` and a computable
adjunction with the constant functor, we
parameterize by an explicit choice of colimit
cocones in `C` (following the pattern of
`spanArrowReflector` in `ArrowSpanAdjunction`).
-/

section ComputableLimFunctor

variable {J : Type w} [Category.{w} J]
variable {C : Type u} [Category.{v} C]
variable
  (chooseColim :
    (F : Jᵒᵖ ⥤ C) → ColimitCocone F)

variable
  (D : J ⥤ CoprodCovarRepCat.{u, v, w} C)

/--
The vertex of the limit cone for `D` in the
Grothendieck construction. Positions are the
sections of the position diagram; fibers are
colimits of the fiber diagrams in `C`.
-/
def ccrLimVertexGr :
    Grothendieck
      (familyFunctor.{u, v, w} C) :=
  ⟨Opposite.op (ccrLimPosSections D),
    fun z =>
      (chooseColim
        (ccrDiagFiberFunctor D z)).cocone.pt⟩

/--
The injection morphism from `D.leftOp.obj j` to
`ccrLimVertexGr` in the Grothendieck construction.
-/
def ccrLimIotaGr
    (j : Jᵒᵖ) :
    D.leftOp.obj j ⟶
      ccrLimVertexGr chooseColim D :=
  { base := Quiver.Hom.op
      (fun z : ccrLimPosSections D =>
        ccrLimPosProj D z j.unop)
    fiber := fun z =>
      (chooseColim
        (ccrDiagFiberFunctor D z)).cocone.ι.app
          j }

/--
The colimit cocone for `D.leftOp` in the
Grothendieck construction with vertex
`ccrLimVertexGr`.
-/
def ccrLimCoconeGr :
    Cocone D.leftOp where
  pt := ccrLimVertexGr chooseColim D
  ι :=
    { app := ccrLimIotaGr chooseColim D
      naturality := fun {j₁ j₂} f => by
        change D.leftOp.map f ≫
          ccrLimIotaGr chooseColim D j₂ =
          ccrLimIotaGr chooseColim D j₁ ≫ 𝟙 _
        rw [Category.comp_id]
        exact ccrHasLimit_cocone_nat
          D (fun z => chooseColim
            (ccrDiagFiberFunctor D z))
          j₁ j₂ f }

/--
The descent morphism from `ccrLimVertexGr` to
the vertex of any cocone over `D.leftOp`.
-/
def ccrLimDescGr
    (s : Cocone D.leftOp) :
    ccrLimVertexGr chooseColim D ⟶ s.pt :=
  { base := Quiver.Hom.op
      (ccrHasLimit_descBase D s)
    fiber := fun x =>
      (chooseColim
        (ccrDiagFiberFunctor D
          (ccrHasLimit_descBase D s
            x))).isColimit.desc
        { pt := s.pt.fiber x
          ι :=
            { app := fun j =>
                (s.ι.app j).fiber x
              naturality :=
                fun {j₁ j₂} f =>
                  ccrHasLimit_desc_nat
                    D s x j₁ j₂ f } } }

private def ccrLimDescCocone
    (s : Cocone D.leftOp)
    (x : s.pt.base.unop) :
    Cocone (ccrDiagFiberFunctor D
      (ccrHasLimit_descBase D s x)) :=
  { pt := s.pt.fiber x
    ι :=
      { app := fun j =>
          (s.ι.app j).fiber x
        naturality :=
          fun {j₁ j₂} f =>
            ccrHasLimit_desc_nat
              D s x j₁ j₂ f } }

/--
`ccrLimCoconeGr` is a colimit cocone for
`D.leftOp` in the Grothendieck construction.
-/
def ccrLimCoconeGrIsColimit :
    IsColimit (ccrLimCoconeGr chooseColim D) :=
  let cc := ccrLimCoconeGr chooseColim D
  let desc' := ccrLimDescGr chooseColim D
  let descCocone' := ccrLimDescCocone D
  { desc := desc'
    fac := fun s j =>
      Grothendieck.ext _ _ rfl (by
        rw [Grothendieck.comp_fiber]
        funext x
        rw [← Category.assoc (eqToHom _)
          (eqToHom _) _,
          eqToHom_trans]
        rw [pi_eqToHom_comp_apply,
          pi_comp_apply]
        have fac :=
          (chooseColim
            (ccrDiagFiberFunctor D
              (ccrHasLimit_descBase D s
                x))).isColimit.fac
            (descCocone' s x) j
        simp only [] at fac
        rw [← Category.assoc]
        convert fac using 2
        simp only [eqToHom_refl,
          Category.id_comp]
        rfl)
    uniq := fun s m hm => by
      obtain ⟨m_base, m_fiber⟩ := m
      have hbase :
          m_base = (desc' s).base := by
        apply Quiver.Hom.unop_inj
        funext x
        apply Subtype.ext
        funext j
        exact congrFun (congrArg
          Quiver.Hom.unop (congrArg
            Grothendieck.Hom.base
            (hm (Opposite.op j)))) x
      subst hbase
      refine Grothendieck.ext _ _ rfl ?_
      funext x
      simp only [eqToHom_refl,
        Category.id_comp]
      apply (chooseColim
        (ccrDiagFiberFunctor D
          (ccrHasLimit_descBase D s
            x))).isColimit.uniq
        (descCocone' s x)
      intro j
      have hj := hm j
      have hfibj :=
        congrFun
          (Grothendieck.congr hj) x
      rw [Grothendieck.comp_fiber]
        at hfibj
      simp only [eqToHom_refl,
        Category.id_comp] at hfibj
      exact hfibj }

/--
An explicit `LimitCone` for any diagram
`D : J ⥤ CoprodCovarRepCat C`, given a choice
of colimit cocones in `C`.
-/
def ccrLimitCone :
    LimitCone D where
  cone :=
    coneOfCoconeLeftOp
      (ccrLimCoconeGr chooseColim D)
  isLimit :=
    isLimitConeOfCoconeLeftOp D
      (ccrLimCoconeGrIsColimit chooseColim D)

end ComputableLimFunctor

/-! ## Computable Limit Functor and Adjunction

Given explicit colimit choices in `C`, we build
a computable limit functor
`(J ⥤ CCR(C)) ⥤ CCR(C)` and prove it is right
adjoint to the constant functor.
-/

section LimFunctorAdj

variable {J : Type w} [Category.{w} J]
variable {C : Type u} [Category.{v} C]
variable
  (chooseColim :
    (F : Jᵒᵖ ⥤ C) → ColimitCocone F)

private abbrev ccrLC
    (chooseColim :
      (F : Jᵒᵖ ⥤ C) → ColimitCocone F)
    (D : J ⥤
      ↑(CoprodCovarRepCat.{u, v, w} C)) :
    LimitCone D :=
  ccrLimitCone chooseColim D

/--
The limit functor for `CoprodCovarRepCat C`,
sending a diagram `D : J ⥤ CCR(C)` to its limit.
Parameterized by an explicit choice of colimit
cocones in `C`.
-/
def ccrLimFunctor :
    (J ⥤ ↑(CoprodCovarRepCat.{u, v, w} C)) ⥤
    ↑(CoprodCovarRepCat.{u, v, w} C) where
  obj D := (ccrLC chooseColim D).cone.pt
  map {D₁ D₂} α :=
    (ccrLC chooseColim D₂).isLimit.lift
      ((Cone.postcompose α).obj
        (ccrLC chooseColim D₁).cone)
  map_id D := by
    apply (ccrLC chooseColim D).isLimit.hom_ext
    intro j
    rw [(ccrLC chooseColim D).isLimit.fac]
    simp [Cone.postcompose]
  map_comp {D₁ D₂ D₃} α β := by
    apply (ccrLC chooseColim D₃).isLimit.hom_ext
    intro j
    dsimp only [Cone.postcompose]
    simp only [Category.assoc, IsLimit.fac,
      NatTrans.comp_app]
    conv_rhs => rw [← Category.assoc]
    rw [IsLimit.fac]
    simp only [NatTrans.comp_app,
      Category.assoc]

/--
The constant-limit adjunction for
`CoprodCovarRepCat C`: the constant functor
`Functor.const J` is left adjoint to
`ccrLimFunctor chooseColim`.
-/
def ccrConstLimAdj :
    (Functor.const J :
      ↑(CoprodCovarRepCat.{u, v, w} C) ⥤
      J ⥤ ↑(CoprodCovarRepCat.{u, v, w} C)) ⊣
    ccrLimFunctor chooseColim :=
  Adjunction.mkOfHomEquiv {
    homEquiv := fun X D =>
      let il := (ccrLC chooseColim D).isLimit
      let π := (ccrLC chooseColim D).cone.π
      { toFun := fun f => il.lift ⟨X, f⟩
        invFun := fun g =>
          { app := fun j => g ≫ π.app j }
        left_inv := fun f => by
          ext j
          simp only [Functor.const_obj_obj]
          exact il.fac ⟨X, f⟩ j
        right_inv := fun g => by
          apply il.hom_ext
          intro j
          exact il.fac ⟨X, _⟩ j }
    homEquiv_naturality_left_symm :=
      fun f g => by
        ext j; simp [Category.assoc]
    homEquiv_naturality_right :=
      fun {X D₁ D₂} f α => by
        let il₂ := (ccrLC chooseColim D₂).isLimit
        apply il₂.hom_ext
        intro j
        simp only [Equiv.coe_fn_mk,
          Category.assoc]
        rw [il₂.fac]
        simp only [ccrLimFunctor,
          IsLimit.fac]
        dsimp only [Cone.postcompose]
        simp only [NatTrans.comp_app,
          ← Category.assoc, IsLimit.fac] }

end LimFunctorAdj

/-! ## PRA Reassembly

Given a positions presheaf `A : Jᵒᵖ ⥤ Type w'` and a
directions functor
`E : A.ElementsPre ⥤ (Iᵒᵖ ⥤ Type w_I)`, we reassemble
a PRA `P : PresheafPRACat I J`.

At each `j : Jᵒᵖ`, the CCR object has:
- Index type: `A.obj j`
- Family at `a : A.obj j`: `E.obj (op ⟨j, a⟩)`

The morphism action uses functoriality of `E` on
morphisms in `A.ElementsPre`.
-/

section PRAReassembly

universe u_I v_I u_J v_J w_I w'

variable {I : Type u_I} [Category.{v_I} I]
variable {J : Type u_J} [Category.{v_J} J]

/-! ### FunctorToData-based reassembly

A PRA `P : PresheafPRACat I J` is definitionally
`Jᵒᵖ ⥤ CoprodCovarRepCat(PSh(I))` where
`CoprodCovarRepCat = (Grothendieck F)ᵒᵖ`.  This
is `(J ⥤ Grothendieck F)ᵒᵖ` via `Functor.op`.

So a PRA is `G.op` for `G : J ⥤ Grothendieck F`,
and `G` is built from `FunctorToData` with
`D = J` and `baseFunc = A.op : J ⥤ (Type w')ᵒᵖ`.
-/

variable
  (A : Jᵒᵖ ⥤ Type w')
  (E : A.ElementsPre ⥤ (Iᵒᵖ ⥤ Type w_I))

/--
The fiber function for the `FunctorToData`-based
reassembly.  Sends `j : J` to the function
`A.obj (op j) → PSh(I)` given by E at each
element.
-/
def praReassembleFib (j : J) :
    (familyFunctor.{max v_I u_I (w_I + 1),
      max u_I w_I, w'}
      (↑(presheafCat.{u_I, v_I, w_I} I))).obj
        (A.rightOp.obj j) :=
  fun a => E.obj (Opposite.op ⟨Opposite.op j, a⟩)

/--
The fiber morphism function for `FunctorToData`.
For `g : j₁ ⟶ j₂` in J and `a₂ : A.obj (op j₂)`,
sends the transported fiber to the target fiber
using `E.map`.
-/
def praReassembleHom
    {j₁ j₂ : J} (g : j₁ ⟶ j₂)
    (a₂ : A.obj (Opposite.op j₂)) :
    praReassembleFib A E j₁
      (A.map g.op a₂) ⟶
    praReassembleFib A E j₂ a₂ :=
  E.map
    (Quiver.Hom.op
      (CategoryOfElements.homMk (F := A)
        ⟨Opposite.op j₂, a₂⟩
        ⟨Opposite.op j₁,
          A.map g.op a₂⟩
        g.op rfl))

/--
The Grothendieck object at `j` for the reassembled
PRA. Has base `op (A.obj j)` and fiber
`fun a => E.obj (op ⟨j, a⟩)`.
-/
def praReassembleObjGr (j : Jᵒᵖ) :
    Grothendieck
      (familyFunctor.{max v_I u_I (w_I + 1),
        max u_I w_I, w'}
        (Iᵒᵖ ⥤ Type w_I)) :=
  ⟨Opposite.op (A.obj j),
    fun a => E.obj (Opposite.op ⟨j, a⟩)⟩

/--
The Grothendieck morphism for a morphism `g : j₁ ⟶ j₂`
in `Jᵒᵖ`. Goes from `praReassembleObjGr A E j₂` to
`praReassembleObjGr A E j₁` in
`Grothendieck (familyFunctor ...)`.

The base is `op (A.map g)` and the fiber at `a₁`
is `E.map` applied to the canonical morphism
`op ⟨j₂, A.map g a₁⟩ ⟶ op ⟨j₁, a₁⟩` in
`A.ElementsPre`.
-/
def praReassembleMapGr {j₁ j₂ : Jᵒᵖ} (g : j₁ ⟶ j₂) :
    praReassembleObjGr A E j₂ ⟶
      praReassembleObjGr A E j₁ :=
  { base := Quiver.Hom.op (A.map g)
    fiber := fun a₁ =>
      E.map (Quiver.Hom.op
        (CategoryOfElements.homMk
          (F := A) ⟨j₁, a₁⟩ ⟨j₂, A.map g a₁⟩
          g rfl)) }

/--
For `g : j₁ ⟶ j₂` in `Jᵒᵖ` and `a₁ : A.obj j₁`,
the canonical morphism in `A.ElementsPre` from
`op ⟨j₂, A.map g a₁⟩` to `op ⟨j₁, a₁⟩`.
-/
def praReassembleElemMor
    {j₁ j₂ : Jᵒᵖ} (g : j₁ ⟶ j₂)
    (a₁ : A.obj j₁) :
    (Opposite.op ⟨j₂, A.map g a₁⟩ :
      A.ElementsPre) ⟶
    Opposite.op ⟨j₁, a₁⟩ :=
  Quiver.Hom.op
    (CategoryOfElements.homMk (F := A)
      ⟨j₁, a₁⟩ ⟨j₂, A.map g a₁⟩ g rfl)

private lemma praReassembleElemMor_id
    (j : Jᵒᵖ) (a : A.obj j) :
    praReassembleElemMor A (𝟙 j) a =
    eqToHom (by
      exact congrArg Opposite.op (Sigma.ext rfl
        (heq_of_eq
          (congrFun (A.map_id j) a)))) := by
  unfold praReassembleElemMor
  apply Quiver.Hom.unop_inj
  apply Subtype.ext
  simp only [Quiver.Hom.unop_op,
    CategoryOfElements.homMk]
  rw [eqToHom_unop]
  simp only [CategoryOfElements.eqToHom_val]
  rfl

private lemma praReassembleMapGr_id (j : Jᵒᵖ) :
    praReassembleMapGr A E (𝟙 j) =
      𝟙 (praReassembleObjGr A E j) := by
  unfold praReassembleMapGr praReassembleObjGr
  apply Grothendieck.ext
  case w_base =>
    exact congrArg Quiver.Hom.op (A.map_id j)
  case w_fiber =>
    funext a
    simp only [Grothendieck.id_fiber]
    rw [pi_eqToHom_comp_apply]
    -- The goal has E.map (...).op which is
    -- E.map (praReassembleElemMor ...).
    change eqToHom _ ≫
      E.map (praReassembleElemMor A (𝟙 j) a) =
      _
    rw [praReassembleElemMor_id A j a,
      eqToHom_map, eqToHom_trans,
      pi_eqToHom_apply]

private lemma praReassembleElemMor_comp
    {j₁ j₂ j₃ : Jᵒᵖ}
    (g : j₁ ⟶ j₂) (h : j₂ ⟶ j₃)
    (a₁ : A.obj j₁) :
    praReassembleElemMor A (g ≫ h) a₁ =
    (@eqToHom A.ElementsPre _
      (Opposite.op ⟨j₃, A.map (g ≫ h) a₁⟩)
      (Opposite.op
        ⟨j₃, A.map h (A.map g a₁)⟩)
      (congrArg Opposite.op
        (congrArg (Sigma.mk j₃)
          (congrFun
            (A.map_comp g h) a₁)))) ≫
    praReassembleElemMor A h (A.map g a₁) ≫
    praReassembleElemMor A g a₁ := by
  apply Quiver.Hom.unop_inj
  apply CategoryOfElements.ext (F := A)
  unfold praReassembleElemMor
  simp only [Quiver.Hom.unop_op,
    CategoryOfElements.homMk]
  erw [CategoryTheory.unop_comp,
    CategoryTheory.unop_comp]
  erw [eqToHom_unop,
    CategoryOfElements.comp_val,
    CategoryOfElements.comp_val,
    Quiver.Hom.unop_op,
    Quiver.Hom.unop_op,
    CategoryOfElements.eqToHom_val,
    eqToHom_refl, Category.comp_id]

private lemma praReassembleMapGr_comp
    {j₁ j₂ j₃ : Jᵒᵖ}
    (g : j₁ ⟶ j₂) (h : j₂ ⟶ j₃) :
    praReassembleMapGr A E (g ≫ h) =
    praReassembleMapGr A E h ≫
      praReassembleMapGr A E g := by
  unfold praReassembleMapGr
  apply Grothendieck.ext
  case w_base =>
    exact congrArg Quiver.Hom.op
      (A.map_comp g h)
  case w_fiber =>
    rw [Grothendieck.comp_fiber]
    funext a₁
    rw [pi_eqToHom_comp_apply]
    conv_rhs =>
      rw [pi_eqToHom_comp_apply,
        pi_comp_apply]
    dsimp only [familyFunctor, familyMap,
      FamilyCat, Cat.Hom.toFunctor,
      Functor.toCatHom]
    simp only [← E.map_comp]
    change eqToHom _ ≫
      E.map (praReassembleElemMor A (g ≫ h)
        a₁) =
      eqToHom _ ≫
        E.map (praReassembleElemMor A h
          (A.map g a₁) ≫
        praReassembleElemMor A g a₁)
    rw [praReassembleElemMor_comp,
      E.map_comp, eqToHom_map,
      ← Category.assoc (eqToHom _)
        (eqToHom _),
      eqToHom_trans, eqToHom_refl,
      Category.id_comp]

/--
The covariant functor `J ⥤ Grothendieck
(familyFunctor ...)` assembling position and
direction data.  Built from `praReassembleObjGr`
and `praReassembleMapGr` with reversed indexing
(`g.op` for each `g : j₁ ⟶ j₂` in J).
-/
def praReassembleGr :
    J ⥤ Grothendieck
      (familyFunctor.{max v_I u_I (w_I + 1),
        max u_I w_I, w'}
        (↑(presheafCat.{u_I, v_I, w_I} I))) where
  obj j :=
    praReassembleObjGr A E (Opposite.op j)
  map g := praReassembleMapGr A E g.op
  map_id j :=
    praReassembleMapGr_id A E (Opposite.op j)
  map_comp f g :=
    praReassembleMapGr_comp A E g.op f.op

/--
Reassemble a PRA from position and direction data
as `praReassembleGr.op : Jᵒᵖ ⥤ CCR(PSh(I))`.
-/
def praReassemble :
    Jᵒᵖ ⥤ ↑(CoprodCovarRepCat.{max v_I u_I
      (w_I + 1), max u_I w_I, w'}
      (↑(presheafCat.{u_I, v_I, w_I} I))) :=
  (praReassembleGr A E).op

/--
Extracting positions from a reassembled PRA
recovers the original position presheaf.
-/
theorem praReassemble_positions :
    (praPositionsFunctor I J).obj
      (praReassemble A E) = A := by
  rfl

/--
Extracting directions from a reassembled PRA
recovers the original direction functor.
-/
theorem praReassemble_directions :
    praDirectionsAtFunctor I J
      (praReassemble A E) = E := by
  apply Functor.hext
  · intro X; rfl
  · intro X Y f
    rw [heq_eq_eq]
    unfold praDirectionsAtFunctor
      praDirectionsAtFunctorOp
    dsimp only [praReassemble,
      Functor.op_obj, Functor.op_map,
      praReassembleGr,
      praReassembleObjGr,
      praReassembleMapGr,
      elementsPrecomp,
      ccrNewFamilyFunctor, ccrNewFamily,
      ccrNewFiberMor,
      unopUnop, Functor.comp_obj,
      Functor.comp_map, Functor.op_obj,
      Functor.op_map,
      Quiver.Hom.unop_op,
      Opposite.unop_op]
    simp only [Opposite.op_unop,
      Quiver.Hom.op_unop]
    obtain ⟨⟨j₁, a₁⟩⟩ := X
    obtain ⟨⟨j₂, a₂⟩⟩ := Y
    set g : j₂ ⟶ j₁ := f.unop.val
    have hcompat : A.map g a₂ = a₁ :=
      show _ from f.unop.property
    clear_value g
    revert f hcompat g
    intro g hcompat f
    subst f
    dsimp only [Opposite.unop_op]
    have comm : A.map g.unop.val a₂ =
      A.map hcompat a₂ :=
      show _ from g.unop.property
    generalize A.map hcompat a₂ = b
      at g comm ⊢
    have peq :
      (Opposite.op ⟨j₁, b⟩ :
        A.ElementsPre) =
      Opposite.op
        ⟨j₁, A.map g.unop.val a₂⟩ :=
      congrArg Opposite.op
        (Sigma.ext rfl
          (heq_of_eq comm.symm))
    calc eqToHom _ ≫
        E.map (CategoryOfElements.homMk
          (F := A) ⟨j₂, a₂⟩
          ⟨j₁, A.map g.unop.val a₂⟩
          g.unop.val rfl).op
      _ = E.map (eqToHom peq) ≫
          E.map (CategoryOfElements.homMk
            (F := A) ⟨j₂, a₂⟩
            ⟨j₁, A.map g.unop.val a₂⟩
            g.unop.val rfl).op := by
            congr 1
            exact (eqToHom_map E peq).symm
      _ = E.map (eqToHom peq ≫
          (CategoryOfElements.homMk
            (F := A) ⟨j₂, a₂⟩
            ⟨j₁, A.map g.unop.val a₂⟩
            g.unop.val rfl).op) := by
            rw [← E.map_comp]
      _ = E.map g := by
            congr 1
            apply Quiver.Hom.unop_inj
            apply CategoryOfElements.ext
              (F := A)
            change ((CategoryOfElements.homMk
              (F := A) ⟨j₂, a₂⟩
              ⟨j₁, A.map g.unop.val a₂⟩
              g.unop.val rfl).op.unop ≫
              (eqToHom peq).unop).val =
              g.unop.val
            simp only [
              CategoryOfElements.comp_val,
              eqToHom_unop,
              CategoryOfElements.eqToHom_val,
              eqToHom_refl,
              Category.comp_id,
              Quiver.Hom.unop_op,
              CategoryOfElements.homMk]


end PRAReassembly

end GebLean
