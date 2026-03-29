import GebLean.PshInternalExternalize

open CategoryTheory Limits

namespace GebLean

universe u v w

variable {C : Type u} [Category.{v} C]

/-- An internal presheaf on an internal category
`X` in the presheaf topos `[C^op, Set]`.

Consists of a "total space" presheaf `fiber` with
a projection `proj` to the object presheaf of `X`,
together with an action by the morphism presheaf
of `X` satisfying unit and associativity axioms.

The axioms are stated pointwise (at each stage
`c : C^op`). -/
structure PshInternalPresheaf
    (X : PshInternalCat.{u, v, w} C) where
  /-- The total-space presheaf. -/
  fiber : Cᵒᵖ ⥤ Type w
  /-- Projection to the object presheaf. -/
  proj : fiber ⟶ X.objPresheaf
  /-- The action: given an element of the fiber
  and a morphism whose source matches the
  projection of that element, produce a new
  fiber element. -/
  action :
    presheafPullback proj X.src ⟶ fiber
  /-- The action maps to the target of the
  morphism acted upon. -/
  action_tgt :
    action ≫ proj =
      presheafPullbackSnd proj X.src ≫ X.tgt
  /-- Acting by the identity morphism is the
  identity: for each stage `c` and fiber element
  `e`, acting on `e` by `idMap(proj(e))`
  recovers `e`. -/
  action_id :
    ∀ (c : Cᵒᵖ) (e : fiber.obj c),
      action.app c
        ⟨(e, X.idMap.app c (proj.app c e)),
          congr_fun
            (NatTrans.congr_app
              (fiberIdMap_src X) c).symm
            (proj.app c e)⟩ = e
  /-- Associativity of the action: acting by a
  composite equals acting sequentially. For
  composable morphisms `m₁`, `m₂` with
  `proj(e) = src(m₁)` and
  `tgt(m₁) = src(m₂)`, acting by
  `compMap(m₁, m₂)` equals first acting by
  `m₁` then by `m₂`. -/
  action_assoc :
    ∀ (c : Cᵒᵖ) (e : fiber.obj c)
      (m₁ m₂ : X.morPresheaf.obj c)
      (h₁ : proj.app c e = X.src.app c m₁)
      (h₂ : X.tgt.app c m₁ =
        X.src.app c m₂),
      action.app c
        ⟨(action.app c ⟨(e, m₁), h₁⟩, m₂),
          (congr_fun
            (NatTrans.congr_app
              (action_tgt) c)
            ⟨(e, m₁), h₁⟩).trans h₂⟩ =
      action.app c
        ⟨(e, X.compMap.app c
          ⟨(m₁, m₂), h₂⟩),
          h₁.trans
            (congr_fun
              (NatTrans.congr_app
                (fiberCompMap_src X) c)
              ⟨(m₁, m₂), h₂⟩).symm⟩

variable {X : PshInternalCat.{u, v, w} C}

/-- The fiber type of an internal presheaf at
stage `c`. -/
abbrev PshInternalPresheaf.fiberAt
    (P : PshInternalPresheaf X)
    (c : Cᵒᵖ) : Type w :=
  P.fiber.obj c

/-- The projection of a fiber element at
stage `c`. -/
abbrev PshInternalPresheaf.projAt
    (P : PshInternalPresheaf X)
    (c : Cᵒᵖ)
    (e : P.fiberAt c) : fiberObj X c :=
  P.proj.app c e

/-- The action of a morphism on a fiber element
at stage `c`, given a proof that the projection
of the element equals the source of the
morphism. -/
abbrev PshInternalPresheaf.actionAt
    (P : PshInternalPresheaf X)
    (c : Cᵒᵖ)
    (e : P.fiberAt c)
    (m : fiberMor X c)
    (h : P.projAt c e = fiberSrc X c m) :
    P.fiberAt c :=
  P.action.app c ⟨(e, m), h⟩

/-- The projection of an acted-upon element
equals the target of the morphism. -/
theorem PshInternalPresheaf.projAt_actionAt
    (P : PshInternalPresheaf X)
    (c : Cᵒᵖ)
    (e : P.fiberAt c)
    (m : fiberMor X c)
    (h : P.projAt c e = fiberSrc X c m) :
    P.projAt c (P.actionAt c e m h) =
      fiberTgt X c m :=
  congr_fun
    (NatTrans.congr_app P.action_tgt c)
    ⟨(e, m), h⟩

/-- The identity action restated in terms of
`actionAt`. -/
theorem PshInternalPresheaf.actionAt_id
    (P : PshInternalPresheaf X)
    (c : Cᵒᵖ)
    (e : P.fiberAt c) :
    P.actionAt c e
      (fiberId X c (P.projAt c e))
      (congr_fun
        (NatTrans.congr_app
          (fiberIdMap_src X) c).symm
        (P.projAt c e)) = e :=
  P.action_id c e

/-- Associativity restated in terms
of `actionAt`. -/
theorem PshInternalPresheaf.actionAt_assoc
    (P : PshInternalPresheaf X)
    (c : Cᵒᵖ)
    (e : P.fiberAt c)
    (m₁ m₂ : fiberMor X c)
    (h₁ : P.projAt c e = fiberSrc X c m₁)
    (h₂ : fiberTgt X c m₁ =
      fiberSrc X c m₂) :
    P.actionAt c
      (P.actionAt c e m₁ h₁) m₂
      ((P.projAt_actionAt c e m₁ h₁).trans
        h₂) =
    P.actionAt c e
      (fiberComp X c
        ⟨(m₁, m₂), h₂⟩)
      (h₁.trans
        (congr_fun
          (NatTrans.congr_app
            (fiberCompMap_src X) c)
          ⟨(m₁, m₂), h₂⟩).symm) :=
  P.action_assoc c e m₁ m₂ h₁ h₂

/-- A morphism of internal presheaves on `X`.

Consists of a natural transformation `map`
between the total-space presheaves that commutes
with projection and with the action. -/
structure PshInternalPresheafHom
    (P Q : PshInternalPresheaf X) where
  /-- The underlying natural transformation
  between fiber presheaves. -/
  map : P.fiber ⟶ Q.fiber
  /-- The map commutes with projection to the
  object presheaf. -/
  proj_comm : map ≫ Q.proj = P.proj
  /-- The map commutes with the action:
  applying `map` then acting in `Q` equals
  acting in `P` then applying `map`. -/
  action_comm :
    presheafPullbackLift Q.proj X.src
      (presheafPullbackFst P.proj X.src ≫ map)
      (presheafPullbackSnd P.proj X.src)
      (by rw [Category.assoc, proj_comm,
        presheafPullbackCondition]) ≫
      Q.action =
    P.action ≫ map

/-- The identity morphism of an internal
presheaf. -/
def PshInternalPresheafHom.id
    (P : PshInternalPresheaf X) :
    PshInternalPresheafHom P P where
  map := 𝟙 P.fiber
  proj_comm := Category.id_comp _
  action_comm := by
    simp only [Category.comp_id]
    have hlift : presheafPullbackLift P.proj X.src
        (presheafPullbackFst P.proj X.src)
        (presheafPullbackSnd P.proj X.src)
        (presheafPullbackCondition P.proj X.src) =
        𝟙 _ := by
      apply PullbackCone.IsLimit.hom_ext
        (presheafPullbackIsLimit ..)
      · simp
      · simp
    rw [hlift, Category.id_comp]

/-- Composition of morphisms of internal
presheaves. -/
def PshInternalPresheafHom.comp
    {P Q R : PshInternalPresheaf X}
    (f : PshInternalPresheafHom P Q)
    (g : PshInternalPresheafHom Q R) :
    PshInternalPresheafHom P R where
  map := f.map ≫ g.map
  proj_comm := by
    rw [Category.assoc, g.proj_comm,
      f.proj_comm]
  action_comm := by
    ext c ⟨⟨e, m⟩, (h : P.proj.app c e =
      X.src.app c m)⟩
    simp only [NatTrans.comp_app]
    have hf := congr_fun
      (NatTrans.congr_app f.action_comm c)
      (⟨(e, m), h⟩ :
        (presheafPullback P.proj X.src).obj c)
    simp only [NatTrans.comp_app] at hf
    have hg := congr_fun
      (NatTrans.congr_app g.action_comm c)
      (⟨(f.map.app c e, m),
        (congr_fun (NatTrans.congr_app
          f.proj_comm c) e ▸ h :
          Q.proj.app c (f.map.app c e) =
            X.src.app c m)⟩ :
        (presheafPullback Q.proj X.src).obj c)
    simp only [NatTrans.comp_app] at hg
    change R.action.app c
      ⟨(g.map.app c (f.map.app c e), m), _⟩ =
      g.map.app c (f.map.app c
        (P.action.app c ⟨(e, m), h⟩))
    have hg' : R.action.app c
      ⟨(g.map.app c (f.map.app c e), m), _⟩ =
      g.map.app c (Q.action.app c
        ⟨(f.map.app c e, m), _⟩) := hg
    have hf' : Q.action.app c
      ⟨(f.map.app c e, m), _⟩ =
      f.map.app c
        (P.action.app c ⟨(e, m), h⟩) := hf
    rw [hg', hf']

@[ext]
theorem PshInternalPresheafHom.ext
    {P Q : PshInternalPresheaf X}
    {f g : PshInternalPresheafHom P Q}
    (h : f.map = g.map) : f = g := by
  cases f; cases g; congr

instance PshInternalPresheaf.category :
    Category (PshInternalPresheaf X) where
  Hom := PshInternalPresheafHom
  id := PshInternalPresheafHom.id
  comp := PshInternalPresheafHom.comp
  id_comp := fun f ↦ by
    ext; simp [PshInternalPresheafHom.comp,
      PshInternalPresheafHom.id]
  comp_id := fun f ↦ by
    ext; simp [PshInternalPresheafHom.comp,
      PshInternalPresheafHom.id]
  assoc := fun f g h ↦ by
    ext; simp [PshInternalPresheafHom.comp,
      Category.assoc]

end GebLean
