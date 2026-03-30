import GebLean.PshInternalPresheaf
import Mathlib.CategoryTheory.Grothendieck

open CategoryTheory Limits

namespace GebLean

universe u v w

variable {C : Type u} [Category.{v} C]

/-- The Grothendieck construction of the
externalization of an internal category `X`.

Objects are pairs `⟨c, x⟩` where `c : Cᵒᵖ` and
`x : fiberObj X c`.  A morphism
`⟨c, x⟩ ⟶ ⟨c', x'⟩` consists of
`f : c ⟶ c'` in `Cᵒᵖ` together with a fiber
morphism
`(fiberRestrict X f).obj x ⟶ x'`. -/
abbrev PshInternalCat.groth
    (X : PshInternalCat.{u, v, w} C) :=
  Grothendieck (externalize X)

variable (X : PshInternalCat.{u, v, w} C)

/-- The fiber of the comparison functor at a
Grothendieck object `⟨c, x⟩`: elements of the
internal presheaf's fiber at `c` that project
to `x`. -/
def comparisonFiber
    (P : PshInternalPresheaf X)
    (p : X.groth) : Type w :=
  { e : P.fiberAt p.base //
    P.projAt p.base e = p.fiber }

/-- Naturality of projection: applying
`P.fiber.map f` then projecting equals
projecting then restricting. -/
theorem PshInternalPresheaf.projAt_naturality
    {X : PshInternalCat.{u, v, w} C}
    (P : PshInternalPresheaf X)
    {c c' : Cᵒᵖ} (f : c ⟶ c')
    (e : P.fiberAt c) :
    P.projAt c' (P.fiber.map f e) =
      (fiberRestrict X f).obj
        (P.projAt c e) :=
  congr_fun (P.proj.naturality f) e

/-- Naturality of the internal presheaf action
with respect to base change: restricting along
`f` commutes with acting by a morphism. -/
theorem PshInternalPresheaf.actionAt_naturality
    {X : PshInternalCat.{u, v, w} C}
    (P : PshInternalPresheaf X)
    {c c' : Cᵒᵖ} (f : c ⟶ c')
    (e : P.fiberAt c)
    (m : fiberMor X c)
    (h : P.projAt c e = fiberSrc X c m) :
    P.fiber.map f (P.actionAt c e m h) =
      P.actionAt c' (P.fiber.map f e)
        (X.morPresheaf.map f m)
        ((congr_fun (P.proj.naturality f) e).trans
          ((congrArg (X.objPresheaf.map f) h).trans
            (congr_fun
              (X.src.naturality f) m).symm)) :=
  (congr_fun (P.action.naturality f)
    ⟨(e, m), h⟩).symm

/-- `actionAt` depends only on the morphism value,
not on the proof argument. -/
theorem PshInternalPresheaf.actionAt_congr_m
    {X : PshInternalCat.{u, v, w} C}
    (P : PshInternalPresheaf X)
    (c : Cᵒᵖ) (e : P.fiberAt c)
    (m₁ m₂ : fiberMor X c) (hm : m₁ = m₂)
    (h₁ : P.projAt c e = fiberSrc X c m₁)
    (h₂ : P.projAt c e = fiberSrc X c m₂) :
    P.actionAt c e m₁ h₁ =
      P.actionAt c e m₂ h₂ := by
  subst hm; rfl

/-- The action of the comparison presheaf on a
Grothendieck morphism.  Given
`⟨f, φ⟩ : ⟨c, x⟩ ⟶ ⟨c', x'⟩` and a fiber
element `e` over `x`, first restricts `e` along
`f`, then acts by the fiber morphism `φ`. -/
def comparisonPresheafMap
    {X : PshInternalCat.{u, v, w} C}
    (P : PshInternalPresheaf X)
    {p q : X.groth}
    (m : p ⟶ q)
    (ex : comparisonFiber X P p) :
    comparisonFiber X P q :=
  let e₁ := P.fiber.map m.base ex.val
  let h₁ : P.projAt q.base e₁ =
      (fiberRestrict X m.base).obj p.fiber :=
    (P.projAt_naturality m.base ex.val).trans
      (congrArg _ ex.property)
  ⟨P.actionAt q.base e₁ m.fiber.val
      (h₁.trans m.fiber.prop.1.symm),
    (P.projAt_actionAt q.base e₁ m.fiber.val
      (h₁.trans m.fiber.prop.1.symm)).trans
      m.fiber.prop.2⟩

variable {X}

/-- The `eqToHom` morphism in the fiber category
has underlying value equal to the identity
morphism at the source. -/
theorem fiberHom_eqToHom_val
    (X : PshInternalCat.{u, v, w} C)
    (c : Cᵒᵖ) {a b : fiberObj X c}
    (h : a = b) :
    (eqToHom h : a ⟶ b).val =
      fiberId X c a := by
  subst h; rfl

/-- The comparison presheaf sends the identity
Grothendieck morphism to the identity. -/
theorem comparisonPresheafMap_id
    (P : PshInternalPresheaf X)
    (p : X.groth)
    (ex : comparisonFiber X P p) :
    comparisonPresheafMap P (𝟙 p) ex = ex := by
  apply Subtype.ext
  change P.action.app p.base
    ⟨(P.fiber.map (𝟙 p.base) ex.val,
      (𝟙 p : Grothendieck.Hom p p).fiber.val),
      _⟩ = ex.val
  have hmap : P.fiber.map (𝟙 p.base) ex.val =
      ex.val :=
    congr_fun (P.fiber.map_id p.base) ex.val
  have hfibval :
      (𝟙 p : Grothendieck.Hom p p).fiber.val =
        fiberId X p.base
          (P.projAt p.base ex.val) := by
    have hid :
        (𝟙 p : Grothendieck.Hom p p).fiber =
          eqToHom (by
            simp [externalize]) :=
      Grothendieck.id_fiber p
    rw [hid, fiberHom_eqToHom_val]
    exact congrArg (fiberId X p.base)
      ((congr_fun
        (X.objPresheaf.map_id p.base)
        p.fiber).trans ex.property.symm)
  exact (congrArg (P.action.app p.base)
    (Subtype.ext (Prod.ext hmap hfibval) :
      (⟨(P.fiber.map (𝟙 p.base) ex.val,
        (𝟙 p : Grothendieck.Hom p p).fiber.val),
        _⟩ :
        (presheafPullback P.proj X.src).obj
          p.base) =
      ⟨(ex.val,
        fiberId X p.base
          (P.projAt p.base ex.val)),
        _⟩)).trans
    (P.action_id p.base ex.val)

-- Chains action naturality with associativity
-- across dependent subtype equalities.
/-- The comparison presheaf sends a composite
Grothendieck morphism to the composite. -/
theorem comparisonPresheafMap_comp
    (P : PshInternalPresheaf X)
    {p q r : X.groth}
    (f : p ⟶ q) (g : q ⟶ r)
    (ex : comparisonFiber X P p) :
    comparisonPresheafMap P (f ≫ g) ex =
      comparisonPresheafMap P g
        (comparisonPresheafMap P f ex) := by
  apply Subtype.ext
  set e := ex.val
  set ef := P.fiber.map f.base e
  set egf := P.fiber.map g.base ef
  have hmc :
      P.fiber.map (f.base ≫ g.base) e = egf :=
    congr_fun (P.fiber.map_comp f.base g.base) e
  have h_f :
      P.projAt q.base ef =
        fiberSrc X q.base f.fiber.val :=
    ((P.projAt_naturality f.base e).trans
      (congrArg _ ex.property)).trans
      f.fiber.prop.1.symm
  have h_rf_tgt :
      fiberTgt X r.base
        (X.morPresheaf.map g.base
          f.fiber.val) =
        fiberSrc X r.base g.fiber.val := by
    change (X.morPresheaf.map g.base ≫
      X.tgt.app r.base) f.fiber.val =
      X.src.app r.base g.fiber.val
    rw [X.tgt.naturality g.base]
    change X.objPresheaf.map g.base
      (fiberTgt X q.base f.fiber.val) =
      fiberSrc X r.base g.fiber.val
    rw [f.fiber.prop.2]
    exact g.fiber.prop.1.symm
  have hcfv :
      (f ≫ g : Grothendieck.Hom p r).fiber.val
        = fiberComp X r.base
          ⟨(X.morPresheaf.map g.base
              f.fiber.val,
            g.fiber.val), h_rf_tgt⟩ := by
    rw [congrArg Subtype.val
      (Grothendieck.comp_fiber f g),
      fiberHom_val_eqToHom_comp]
    rfl
  have h_egf_src :
      P.projAt r.base egf = fiberSrc X r.base
        (X.morPresheaf.map g.base
          f.fiber.val) :=
    (congr_fun (P.proj.naturality g.base)
      ef).trans
      ((congrArg (X.objPresheaf.map g.base)
        h_f).trans
        (congr_fun (X.src.naturality g.base)
          f.fiber.val).symm)
  have h_egf_comp :
      P.projAt r.base egf =
        fiberSrc X r.base
          (fiberComp X r.base
            ⟨(X.morPresheaf.map g.base
                f.fiber.val,
              g.fiber.val), h_rf_tgt⟩) :=
    h_egf_src.trans
      (fiberSrc_comp X r.base
        ⟨(X.morPresheaf.map g.base
            f.fiber.val,
          g.fiber.val), h_rf_tgt⟩).symm
  have hnat :
      P.fiber.map g.base
        (P.actionAt q.base ef
          f.fiber.val h_f) =
        P.actionAt r.base egf
          (X.morPresheaf.map g.base
            f.fiber.val) h_egf_src :=
    P.actionAt_naturality g.base ef
      f.fiber.val h_f
  set target_m := fiberComp X r.base
    ⟨(X.morPresheaf.map g.base
        f.fiber.val,
      g.fiber.val), h_rf_tgt⟩
  set target_val :=
    P.actionAt r.base egf target_m h_egf_comp
  have lhs_eq :
      (comparisonPresheafMap P (f ≫ g) ex).val
        = target_val :=
    congrArg (P.action.app r.base)
      (Subtype.ext (Prod.ext hmc hcfv))
  have rhs_step1 :
      (comparisonPresheafMap P g
        (comparisonPresheafMap P f ex)).val =
        P.actionAt r.base
          (P.actionAt r.base egf
            (X.morPresheaf.map g.base
              f.fiber.val) h_egf_src)
          g.fiber.val
          ((P.projAt_actionAt r.base egf
            (X.morPresheaf.map g.base
              f.fiber.val)
            h_egf_src).trans h_rf_tgt) :=
    congrArg (P.action.app r.base)
      (Subtype.ext (Prod.ext hnat rfl))
  have rhs_step2 :
      P.actionAt r.base
        (P.actionAt r.base egf
          (X.morPresheaf.map g.base
            f.fiber.val) h_egf_src)
        g.fiber.val _ = target_val :=
    P.action_assoc r.base egf
      (X.morPresheaf.map g.base f.fiber.val)
      g.fiber.val h_egf_src h_rf_tgt
  exact lhs_eq.trans
    (rhs_step1.trans rhs_step2).symm

/-- The comparison presheaf on the Grothendieck
category, sending `⟨c, x⟩` to the fiber of the
internal presheaf over `x` at stage `c`. -/
def comparisonPresheaf
    (P : PshInternalPresheaf X) :
    X.groth ⥤ Type w where
  obj p := comparisonFiber X P p
  map m := comparisonPresheafMap P m
  map_id p := funext fun ex ↦
    comparisonPresheafMap_id P p ex
  map_comp f g := funext fun ex ↦
    comparisonPresheafMap_comp P f g ex

-- Relates presheafPullbackLift to actionAt.
/-- A morphism of internal presheaves commutes
with the action at a given stage. -/
theorem PshInternalPresheafHom.actionAt_comm
    {P Q : PshInternalPresheaf X}
    (α : PshInternalPresheafHom P Q)
    (c : Cᵒᵖ)
    (e : P.fiberAt c)
    (m : fiberMor X c)
    (h : P.projAt c e = fiberSrc X c m) :
    Q.actionAt c (α.map.app c e) m
      ((congr_fun (NatTrans.congr_app
        α.proj_comm c) e).trans h) =
    α.map.app c
      (P.actionAt c e m h) := by
  have comm := (congr_fun
    (NatTrans.congr_app α.action_comm c)
    ⟨(e, m), h⟩).symm
  let lhs_input :
      (presheafPullback Q.proj X.src).obj c :=
    ⟨(α.map.app c e, m),
      (congr_fun (NatTrans.congr_app
        α.proj_comm c) e).trans h⟩
  let rhs_input :=
    (presheafPullbackLift Q.proj X.src
      (presheafPullbackFst P.proj X.src ≫
        α.map)
      (presheafPullbackSnd P.proj X.src)
      (by rw [Category.assoc, α.proj_comm,
        presheafPullbackCondition])).app c
          ⟨(e, m), h⟩
  have hinput : lhs_input = rhs_input := by
    apply Subtype.ext
    simp [presheafPullbackLift_app_val,
      lhs_input, rhs_input]
  change Q.action.app c lhs_input =
    α.map.app c (P.action.app c ⟨(e, m), h⟩)
  rw [hinput]
  simp only [NatTrans.comp_app,
    types_comp_apply] at comm
  exact comm.symm

/-- The natural transformation induced by a
morphism of internal presheaves between the
corresponding comparison presheaves. -/
def comparisonNatTrans
    {P Q : PshInternalPresheaf X}
    (α : PshInternalPresheafHom P Q) :
    comparisonPresheaf P ⟶
      comparisonPresheaf Q where
  app p := fun ⟨e, he⟩ ↦
    ⟨α.map.app p.base e,
      (congr_fun (NatTrans.congr_app
        α.proj_comm p.base) e).trans he⟩
  naturality p q m := by
    funext ⟨e, he⟩
    apply Subtype.ext
    simp only [types_comp_apply,
      comparisonPresheaf,
      comparisonPresheafMap]
    have hnat :=
      congr_fun (α.map.naturality m.base) e
    simp only [types_comp_apply] at hnat
    rw [← α.actionAt_comm q.base
      (P.fiber.map m.base e)
      m.fiber.val _]
    exact congrArg (Q.action.app q.base)
      (Subtype.ext (Prod.ext hnat rfl))

/-- The comparison functor from internal
presheaves on `X` to presheaves on the
Grothendieck construction of `externalize X`. -/
def comparisonFunctor :
    PshInternalPresheaf X ⥤
      (X.groth ⥤ Type w) where
  obj P := comparisonPresheaf P
  map α := comparisonNatTrans α
  map_id P := by
    apply NatTrans.ext; funext p
    ext ⟨e, he⟩; rfl
  map_comp f g := by
    apply NatTrans.ext; funext p
    ext ⟨e, he⟩; rfl

/-- The fiber functor of the comparison: at a
fixed base `c : Cᵒᵖ`, sends
`x : fiberObj X c` to the subtype
`{ e : P.fiberAt c | proj(e) = x }`, and a
fiber morphism `m : x ⟶ y` in the fiber
category to the action of `P` by `m`. -/
def comparisonFib
    (P : PshInternalPresheaf X)
    (c : Cᵒᵖ) :
    fiberObj X c ⥤ Type w where
  obj x := comparisonFiber X P ⟨c, x⟩
  map {x y} m := fun ⟨e, he⟩ ↦
    ⟨P.actionAt c e m.val
      (he.trans m.prop.1.symm),
     (P.projAt_actionAt c e m.val
      (he.trans m.prop.1.symm)).trans
      m.prop.2⟩
  map_id x := by
    funext ⟨e, he⟩
    apply Subtype.ext
    simp only [types_id_apply]
    have hmor : (𝟙 x : x ⟶ x).val =
        fiberId X c (P.projAt c e) :=
      congrArg (fiberId X c) he.symm
    simp only [hmor, P.actionAt_id]
  map_comp {x y z} f g := by
    funext ⟨e, he⟩
    apply Subtype.ext
    simp only [types_comp_apply]
    exact (P.actionAt_assoc c e
      f.val g.val
      (he.trans f.prop.1.symm)
      (f.prop.2.trans g.prop.1.symm)).symm

section Inverse

variable (X : PshInternalCat.{u, v, w} C)

/-- The Grothendieck morphism from `⟨c, x⟩` to
`⟨c', (fiberRestrict X f).obj x⟩` with identity
fiber component, induced by a base morphism
`f : c ⟶ c'`. -/
def grothBaseMor
    (c c' : Cᵒᵖ) (f : c ⟶ c')
    (x : fiberObj X c) :
    (⟨c, x⟩ : X.groth) ⟶
      ⟨c', (fiberRestrict X f).obj x⟩ :=
  ⟨f, 𝟙 _⟩

/-- A Grothendieck morphism `⟨𝟙, eqToHom h⟩`
between same-base objects composed with
`eqToHom` yields the identity. -/
theorem groth_eqToHom_fiber_comp_eqToHom
    (c : Cᵒᵖ) (x y : fiberObj X c)
    (h : y = x)
    (hfy :
      (fiberRestrict X (𝟙 c)).obj x = y) :
    (Grothendieck.Hom.mk (𝟙 c)
        (eqToHom hfy) :
      (Grothendieck.mk c x : X.groth) ⟶
        Grothendieck.mk c y) ≫
      eqToHom
        (congrArg (Grothendieck.mk c) h) =
        𝟙 (Grothendieck.mk c x :
          X.groth) := by
  subst h
  simp only [eqToHom_refl, Category.comp_id]
  apply Grothendieck.ext (w_base := rfl)
  simp only [eqToHom_refl, Category.id_comp]

/-- `grothBaseMor` at the identity, composed with
the `eqToHom` from `fiberRestrict_id`, equals
the identity in the Grothendieck category. -/
theorem grothBaseMor_id_comp_eqToHom
    (c : Cᵒᵖ) (x : fiberObj X c) :
    grothBaseMor X c c (𝟙 c) x ≫
      eqToHom (congrArg (Grothendieck.mk c)
        (congr_fun (X.objPresheaf.map_id c)
          x)) =
      𝟙 (Grothendieck.mk c x :
        X.groth) :=
  groth_eqToHom_fiber_comp_eqToHom X c x
    ((fiberRestrict X (𝟙 c)).obj x)
    (congr_fun (X.objPresheaf.map_id c) x)
    rfl

/-- The base component of `eqToHom` between
same-base Grothendieck objects is the identity. -/
theorem groth_eqToHom_same_base_is_id
    (c : Cᵒᵖ) (a b : fiberObj X c)
    (h : a = b) :
    (eqToHom (congrArg (Grothendieck.mk c) h) :
      (⟨c, a⟩ : X.groth) ⟶ ⟨c, b⟩).base =
      𝟙 c := by
  subst h; rfl

/-- In `Type w`, `eqToHom` equals `cast`. -/
theorem eqToHom_eq_cast
    {A B : Type w} (h : A = B) :
    eqToHom h = cast h := by
  subst h; rfl

/-- The fiber type of the inverse construction:
at stage `c`, pairs `⟨x, e⟩` where
`x : fiberObj X c` and `e : G.obj ⟨c, x⟩`. -/
def inverseFiber
    (G : X.groth ⥤ Type w)
    (c : Cᵒᵖ) : Type w :=
  Σ (x : fiberObj X c), G.obj ⟨c, x⟩

/-- The restriction map on `inverseFiber`:
sends `⟨x, e⟩` along `f : c ⟶ c'` to
`⟨(fiberRestrict X f).obj x,
  G.map (grothBaseMor X c c' f x) e⟩`. -/
def inverseFiberMap
    (G : X.groth ⥤ Type w)
    {c c' : Cᵒᵖ} (f : c ⟶ c')
    (p : inverseFiber X G c) :
    inverseFiber X G c' :=
  ⟨(fiberRestrict X f).obj p.1,
    G.map (grothBaseMor X c c' f p.1) p.2⟩

/-- `inverseFiberMap` sends the identity morphism
to the identity function. -/
theorem inverseFiberMap_id
    (G : X.groth ⥤ Type w)
    (c : Cᵒᵖ)
    (p : inverseFiber X G c) :
    inverseFiberMap X G (𝟙 c) p = p := by
  obtain ⟨x, e⟩ := p
  simp only [inverseFiberMap]
  have hx :
      (fiberRestrict X (𝟙 c)).obj x = x :=
    congr_fun (X.objPresheaf.map_id c) x
  have hg :
      (Grothendieck.mk c
        ((fiberRestrict X (𝟙 c)).obj x) :
        X.groth) = Grothendieck.mk c x :=
    congrArg (Grothendieck.mk c) hx
  have comm :
      grothBaseMor X c c (𝟙 c) x ≫
        eqToHom hg =
      𝟙 (Grothendieck.mk c x : X.groth) :=
    grothBaseMor_id_comp_eqToHom X c x
  have hmapcomp :
      G.map (grothBaseMor X c c (𝟙 c) x) ≫
        G.map (eqToHom hg) = 𝟙 _ := by
    rw [← G.map_comp, comm, G.map_id]
  have hcast :
      cast (congrArg G.obj hg)
        (G.map
          (grothBaseMor X c c (𝟙 c) x) e) =
        e := by
    have : G.map (eqToHom hg) =
        cast (congrArg G.obj hg) := by
      rw [eqToHom_map G hg, eqToHom_eq_cast]
    rw [← this]
    exact congr_fun hmapcomp e
  exact Sigma.ext hx
    (heq_of_cast_eq (congrArg G.obj hg) hcast)

-- Chains `Grothendieck.comp_fiber`, `fiberHom_val`
-- lemmas, and `fiberRestrict.map_id`.
/-- The `.val` of the fiber of a `grothBaseMor`
composition equals `fiberId` at the composed
restriction. -/
theorem grothBaseMor_comp_fiber_val
    {c c' c'' : Cᵒᵖ}
    (f : c ⟶ c') (g : c' ⟶ c'')
    (x : fiberObj X c) :
    (grothBaseMor X c c' f x ≫
      grothBaseMor X c' c'' g
        ((fiberRestrict X f).obj x)).fiber.val =
    fiberId X c''
      ((fiberRestrict X (f ≫ g)).obj x) := by
  rw [Grothendieck.comp_fiber]
  simp only [grothBaseMor]
  rw [fiberHom_val_eqToHom_comp]
  rw [congrArg Subtype.val (Category.comp_id _)]
  change ((fiberRestrict X g).map
    (𝟙 ((fiberRestrict X f).obj x))).val =
    fiberId X c''
      ((fiberRestrict X (f ≫ g)).obj x)
  rw [congrArg Subtype.val
    ((fiberRestrict X g).map_id _)]
  exact congrArg (X.idMap.app c'')
    (congr_fun
      (X.objPresheaf.map_comp f g) x).symm

/-- Composition of `grothBaseMor` equals a single
`grothBaseMor` at the composite, up to `eqToHom`
from `fiberRestrict_comp`. -/
theorem grothBaseMor_comp
    {c c' c'' : Cᵒᵖ}
    (f : c ⟶ c') (g : c' ⟶ c'')
    (x : fiberObj X c) :
    grothBaseMor X c c' f x ≫
      grothBaseMor X c' c'' g
        ((fiberRestrict X f).obj x) =
    grothBaseMor X c c'' (f ≫ g) x ≫
      eqToHom (congrArg (Grothendieck.mk c'')
        (congr_fun (congrArg Functor.obj
          (fiberRestrict_comp X f g))
          x)) := by
  apply Grothendieck.ext
  case w_base => simp [grothBaseMor]
  case w_fiber =>
    apply fiberHom_ext
    simp [Grothendieck.comp_fiber,
      grothBaseMor]

/-- `inverseFiberMap` sends a composite morphism
to the composite of the maps. -/
theorem inverseFiberMap_comp
    (G : X.groth ⥤ Type w)
    {c c' c'' : Cᵒᵖ}
    (f : c ⟶ c') (g : c' ⟶ c'')
    (p : inverseFiber X G c) :
    inverseFiberMap X G (f ≫ g) p =
      inverseFiberMap X G g
        (inverseFiberMap X G f p) := by
  obtain ⟨x, e⟩ := p
  simp only [inverseFiberMap]
  have hx :
      (fiberRestrict X (f ≫ g)).obj x =
        (fiberRestrict X g).obj
          ((fiberRestrict X f).obj x) :=
    congr_fun (congrArg Functor.obj
      (fiberRestrict_comp X f g)) x
  have hG :
      (Grothendieck.mk c''
        ((fiberRestrict X (f ≫ g)).obj x) :
        X.groth) =
      Grothendieck.mk c''
        ((fiberRestrict X g).obj
          ((fiberRestrict X f).obj x)) :=
    congrArg (Grothendieck.mk c'') hx
  have comm :
      grothBaseMor X c c' f x ≫
        grothBaseMor X c' c'' g
          ((fiberRestrict X f).obj x) =
      grothBaseMor X c c'' (f ≫ g) x ≫
        eqToHom hG :=
    grothBaseMor_comp X f g x
  have hmapcomp :
      G.map (grothBaseMor X c c'' (f ≫ g) x) ≫
        G.map (eqToHom hG) =
      G.map (grothBaseMor X c c' f x) ≫
        G.map (grothBaseMor X c' c'' g
          ((fiberRestrict X f).obj x)) := by
    rw [← G.map_comp, ← G.map_comp, comm]
  have hcast :
      cast (congrArg G.obj hG)
        (G.map
          (grothBaseMor X c c'' (f ≫ g) x)
          e) =
      G.map (grothBaseMor X c' c'' g
          ((fiberRestrict X f).obj x))
        (G.map (grothBaseMor X c c' f x) e)
      := by
    have : G.map (eqToHom hG) =
        cast (congrArg G.obj hG) := by
      rw [eqToHom_map G hG, eqToHom_eq_cast]
    rw [← this]
    exact congr_fun hmapcomp e
  exact Sigma.ext hx
    (heq_of_cast_eq (congrArg G.obj hG) hcast)

/-- The inverse fiber functor: sends a presheaf
`G` on the Grothendieck category to a presheaf
on `Cᵒᵖ` whose fiber at `c` is
`Σ (x : fiberObj X c), G.obj ⟨c, x⟩`. -/
def inverseFiberFunctor
    (G : X.groth ⥤ Type w) :
    Cᵒᵖ ⥤ Type w where
  obj c := inverseFiber X G c
  map f := inverseFiberMap X G f
  map_id c := funext (inverseFiberMap_id X G c)
  map_comp f g :=
    funext (inverseFiberMap_comp X G f g)

/-- The projection from the inverse fiber to the
object presheaf: sends `⟨x, e⟩` to `x`. -/
def inverseProj (G : X.groth ⥤ Type w) :
    inverseFiberFunctor X G ⟶ X.objPresheaf where
  app _ := fun ⟨x, _⟩ ↦ x
  naturality _ _ _ := funext fun ⟨_, _⟩ ↦ rfl

/-- A Grothendieck morphism from `⟨c, x⟩` to
`⟨c, fiberTgt X c m⟩` with identity base, induced
by a fiber morphism `m` at stage `c` with a proof
that `x = fiberSrc X c m`. -/
def grothFiberMor
    (c : Cᵒᵖ) (x : fiberObj X c)
    (m : fiberMor X c)
    (h : x = fiberSrc X c m) :
    (⟨c, x⟩ : X.groth) ⟶
      ⟨c, fiberTgt X c m⟩ :=
  ⟨𝟙 c,
    eqToHom ((congr_fun
      (congrArg Functor.obj
        (fiberRestrict_id X c)) x).trans h) ≫
      ⟨m, ⟨rfl, rfl⟩⟩⟩

/-- Naturality of `grothFiberMor` with respect
to base change: restricting along `f` then
acting by the restricted morphism equals acting
by the original morphism then restricting. -/
theorem grothFiberMor_naturality
    {c c' : Cᵒᵖ} (f : c ⟶ c')
    (m : fiberMor X c) :
    grothBaseMor X c c' f
      (fiberSrc X c m) ≫
      grothFiberMor X c'
        ((fiberRestrict X f).obj
          (fiberSrc X c m))
        (X.morPresheaf.map f m)
        ((congrArg (X.objPresheaf.map f) rfl).trans
          (congr_fun
            (X.src.naturality f) m).symm) =
    grothFiberMor X c (fiberSrc X c m) m rfl ≫
      grothBaseMor X c c' f
        (fiberTgt X c m) ≫
      eqToHom (congrArg (Grothendieck.mk c')
        (congr_fun (X.tgt.naturality f)
          m).symm) := by
  apply Grothendieck.ext
  case w_base =>
    simp [grothBaseMor, grothFiberMor]
  case w_fiber =>
    apply fiberHom_ext
    rw [fiberHom_val_eqToHom_comp]
    trans (X.morPresheaf.map f m)
    · rw [congrArg Subtype.val
        (Grothendieck.comp_fiber
          (grothBaseMor X c c' f
            (fiberSrc X c m))
          (grothFiberMor X c'
            ((fiberRestrict X f).obj
              (fiberSrc X c m))
            (X.morPresheaf.map f m) _))]
      simp only [grothBaseMor, grothFiberMor,
        CategoryTheory.Functor.map_id,
        Category.id_comp]
      rw [fiberHom_val_eqToHom_comp,
        fiberHom_val_eqToHom_comp]
    · symm
      rw [congrArg Subtype.val
        (Grothendieck.comp_fiber
          (grothFiberMor X c
            (fiberSrc X c m) m rfl)
          (grothBaseMor X c c' f
            (fiberTgt X c m) ≫
            eqToHom _))]
      simp only [Grothendieck.comp_base,
        Grothendieck.comp_fiber,
        Grothendieck.fiber_eqToHom,
        grothBaseMor, grothFiberMor,
        CategoryTheory.Functor.map_id,
        Category.id_comp,
        eqToHom_trans]
      rw [fiberHom_val_eqToHom_comp,
        fiberHom_val_comp_eqToHom]
      simp only [externalize, fiberRestrict]
      rw [fiberHom_val_eqToHom_comp,
        Grothendieck.base_eqToHom]
      simp only [eqToHom_refl,
        Category.comp_id]

/-- The action of `grothFiberMor` on elements of
`G`, as a map from the pullback to the inverse
fiber.  Given `⟨⟨x, e⟩, m⟩` with `x = src(m)`,
produces `⟨tgt(m), G.map (grothFiberMor ...) e⟩`.
-/
def inverseActionAt
    (G : X.groth ⥤ Type w)
    (c : Cᵒᵖ)
    (p : (presheafPullback
      (inverseProj X G) X.src).obj c) :
    inverseFiber X G c :=
  let em := p.val
  let x := em.1.1
  let e := em.1.2
  let m := em.2
  let h : x = fiberSrc X c m := p.property
  ⟨fiberTgt X c m,
    G.map (grothFiberMor X c x m h) e⟩

/-- Naturality of `inverseActionAt` with respect
to base change. -/
theorem inverseActionAt_naturality
    (G : X.groth ⥤ Type w)
    {c c' : Cᵒᵖ} (f : c ⟶ c')
    (p : (presheafPullback
      (inverseProj X G) X.src).obj c) :
    inverseFiberMap X G f
      (inverseActionAt X G c p) =
      inverseActionAt X G c'
        ((presheafPullback
          (inverseProj X G) X.src).map f p) := by
  obtain ⟨⟨⟨x, e⟩, m⟩, (h : x = fiberSrc X c m)⟩
    := p
  simp only [inverseActionAt, inverseFiberMap]
  set tgtm := fiberTgt X c m
  set fm := X.morPresheaf.map f m
  have hx1 :
      (fiberRestrict X f).obj tgtm =
        fiberTgt X c' fm :=
    (congr_fun (X.tgt.naturality f) m).symm
  have h' : (fiberRestrict X f).obj x =
      fiberSrc X c' fm := by
    change X.objPresheaf.map f x =
      X.src.app c' fm
    rw [h]
    exact (congr_fun (X.src.naturality f) m).symm
  have hobj :
      (Grothendieck.mk c'
        ((fiberRestrict X f).obj tgtm) :
        X.groth) =
      Grothendieck.mk c'
        (fiberTgt X c' fm) :=
    congrArg (Grothendieck.mk c') hx1
  have hcomm :
      grothFiberMor X c x m h ≫
        grothBaseMor X c c' f tgtm ≫
        eqToHom hobj =
      grothBaseMor X c c' f x ≫
        grothFiberMor X c'
          ((fiberRestrict X f).obj x)
          fm h' := by
    subst h
    exact (grothFiberMor_naturality X f m).symm
  have hcast :
      cast (congrArg G.obj hobj)
        (G.map (grothBaseMor X c c' f tgtm)
          (G.map (grothFiberMor X c x m h)
            e)) =
      G.map (grothFiberMor X c'
          ((fiberRestrict X f).obj x)
          fm h')
        (G.map (grothBaseMor X c c' f x) e)
      := by
    have heq : G.map (eqToHom hobj) =
        cast (congrArg G.obj hobj) := by
      rw [eqToHom_map G hobj, eqToHom_eq_cast]
    rw [← heq]
    have step1 :
        G.map (grothFiberMor X c x m h) ≫
          G.map (grothBaseMor X c c' f tgtm) ≫
          G.map (eqToHom hobj) =
        G.map (grothBaseMor X c c' f x) ≫
          G.map (grothFiberMor X c'
            ((fiberRestrict X f).obj x)
            fm h') := by
      simp only [← G.map_comp, hcomm]
    exact congr_fun step1 e
  exact Sigma.ext hx1
    (heq_of_cast_eq (congrArg G.obj hobj) hcast)

/-- The action natural transformation for the
inverse construction: given a presheaf `G` on the
Grothendieck category, acts on the pullback of the
inverse fiber over the morphism presheaf to produce
a new fiber element. -/
def inverseAction
    (G : X.groth ⥤ Type w) :
    presheafPullback (inverseProj X G) X.src ⟶
      inverseFiberFunctor X G where
  app c := inverseActionAt X G c
  naturality _ _ f := funext fun p ↦
    (inverseActionAt_naturality X G f p).symm

/-- The action maps to the target of the
morphism: projection of the acted element
equals the target. -/
theorem inverseAction_tgt
    (G : X.groth ⥤ Type w) :
    inverseAction X G ≫ inverseProj X G =
      presheafPullbackSnd
        (inverseProj X G) X.src ≫ X.tgt := by
  ext c ⟨⟨⟨_, _⟩, m⟩, (_ : _ = fiberSrc X c m)⟩
  rfl

/-- The `grothFiberMor` at the identity morphism,
composed with `eqToHom` from `fiberTgt_id`, gives
the identity in the Grothendieck category. -/
theorem grothFiberMor_id
    (c : Cᵒᵖ) (x : fiberObj X c) :
    grothFiberMor X c x
      (fiberId X c x)
      (fiberSrc_id X c x).symm ≫
      eqToHom (congrArg (Grothendieck.mk c)
        (fiberTgt_id X c x)) =
    𝟙 (Grothendieck.mk c x : X.groth) := by
  apply Grothendieck.ext
  case w_base => simp [grothFiberMor]
  case w_fiber =>
    apply fiberHom_ext
    simp [grothFiberMor,
      Grothendieck.comp_fiber,
      Grothendieck.fiber_eqToHom,
      Grothendieck.base_eqToHom,
      Grothendieck.id_fiber,
      externalize, fiberRestrict,
      fiberHom_val_eqToHom_comp,
      fiberHom_val_comp_eqToHom,
      fiberHom_eqToHom_val]

/-- Acting by the identity on the inverse fiber
yields the identity.  Uses the `Sigma.ext` pattern
with `heq_of_cast_eq` for the dependent second
component. -/
theorem inverseAction_id
    (G : X.groth ⥤ Type w)
    (c : Cᵒᵖ) (p : inverseFiber X G c) :
    inverseActionAt X G c
      ⟨(p, X.idMap.app c p.1),
        (congr_fun (NatTrans.congr_app
          (fiberIdMap_src X) c).symm p.1)⟩ =
      p := by
  obtain ⟨x, e⟩ := p
  simp only [inverseActionAt]
  have hx : fiberTgt X c (fiberId X c x) = x :=
    fiberTgt_id X c x
  have hobj :
      (Grothendieck.mk c
        (fiberTgt X c (fiberId X c x)) :
        X.groth) = Grothendieck.mk c x :=
    congrArg (Grothendieck.mk c) hx
  have hmapcomp :
      G.map (grothFiberMor X c x
          (fiberId X c x)
          (fiberSrc_id X c x).symm) ≫
        G.map (eqToHom hobj) = 𝟙 _ := by
    rw [← G.map_comp,
      grothFiberMor_id X c x, G.map_id]
  have hcast :
      cast (congrArg G.obj hobj)
        (G.map (grothFiberMor X c x
            (fiberId X c x)
            (fiberSrc_id X c x).symm) e) =
        e := by
    have : G.map (eqToHom hobj) =
        cast (congrArg G.obj hobj) := by
      rw [eqToHom_map G hobj, eqToHom_eq_cast]
    rw [← this]
    exact congr_fun hmapcomp e
  exact Sigma.ext hx
    (heq_of_cast_eq (congrArg G.obj hobj) hcast)


/-- Composition of fiber Grothendieck morphisms:
acting by `m₁` then by `m₂` equals acting by
`compMap(m₁, m₂)`, up to `eqToHom`. -/
theorem grothFiberMor_comp
    (c : Cᵒᵖ)
    (m₁ m₂ : fiberMor X c)
    (h₂ : fiberTgt X c m₁ = fiberSrc X c m₂) :
    grothFiberMor X c (fiberSrc X c m₁) m₁
        rfl ≫
      grothFiberMor X c (fiberTgt X c m₁) m₂
        h₂ =
    grothFiberMor X c (fiberSrc X c m₁)
      (fiberComp X c ⟨(m₁, m₂), h₂⟩)
      ((fiberSrc_comp X c
        ⟨(m₁, m₂), h₂⟩).symm) ≫
      eqToHom (congrArg (Grothendieck.mk c)
        (fiberTgt_comp X c
          ⟨(m₁, m₂), h₂⟩)) := by
  apply Grothendieck.ext
  case w_base => simp [grothFiberMor]
  case w_fiber =>
    apply fiberHom_ext
    simp only [externalize, fiberRestrict,
      FunctorToTypes.comp,
      Functor.const_obj_obj,
      FunctorToTypes.prod.fst_app,
      FunctorToTypes.prod.snd_app,
      Cat.of_α, Functor.id_obj,
      grothFiberMor,
      Grothendieck.comp_base,
      Grothendieck.comp_fiber,
      fiberHom_val_eqToHom_comp,
      FunctorToTypes.map_id_apply,
      eqToHom_trans_assoc,
      Grothendieck.base_eqToHom,
      eqToHom_refl,
      Grothendieck.fiber_eqToHom,
      fiberHom_val_comp_eqToHom]
    have hcomp_val :
        ∀ (a b d : fiberObj X c)
          (f : a ⟶ b) (g : b ⟶ d),
          (f ≫ g).val =
            fiberComp X c
              (fiberMkCompPair X c f g) :=
      fun _ _ _ _ _ ↦ rfl
    rw [hcomp_val]
    congr 1
    apply Subtype.ext
    simp only [fiberMkCompPair]
    ext
    · rfl
    · exact @fiberHom_val_eqToHom_comp
        _ _ X c _ _ _ _ _

/-- Associativity of the inverse action:
acting by `m₁` then by `m₂` equals acting
by the composite `compMap(m₁, m₂)`. -/
theorem inverseAction_assoc
    (G : X.groth ⥤ Type w)
    (c : Cᵒᵖ) (p : inverseFiber X G c)
    (m₁ m₂ : fiberMor X c)
    (h₁ : p.1 = fiberSrc X c m₁)
    (h₂ : fiberTgt X c m₁ =
      fiberSrc X c m₂) :
    inverseActionAt X G c
      ⟨(inverseActionAt X G c
          ⟨(p, m₁), h₁⟩, m₂), h₂⟩ =
    inverseActionAt X G c
      ⟨(p, fiberComp X c ⟨(m₁, m₂), h₂⟩),
        h₁.trans
          (fiberSrc_comp X c
            ⟨(m₁, m₂), h₂⟩).symm⟩ := by
  obtain ⟨x, e⟩ := p
  simp only [inverseActionAt]
  set cp := (⟨(m₁, m₂), h₂⟩ :
    fiberCompPairs X c)
  have hx :
      fiberTgt X c m₂ =
        fiberTgt X c (fiberComp X c cp) :=
    (fiberTgt_comp X c cp).symm
  have hobj :
      (Grothendieck.mk c
        (fiberTgt X c m₂) : X.groth) =
      Grothendieck.mk c
        (fiberTgt X c (fiberComp X c cp)) :=
    congrArg (Grothendieck.mk c) hx
  have h₁' : x = fiberSrc X c m₁ := h₁
  subst h₁'
  set gfm₁ := grothFiberMor X c
    (fiberSrc X c m₁) m₁ rfl
  set gfm₂ := grothFiberMor X c
    (fiberTgt X c m₁) m₂ h₂
  set gfmc := grothFiberMor X c
    (fiberSrc X c m₁)
    (fiberComp X c cp)
    ((fiberSrc_comp X c cp).symm)
  have hcomm :
      gfm₁ ≫ gfm₂ =
        gfmc ≫
          eqToHom (congrArg (Grothendieck.mk c)
            (fiberTgt_comp X c cp)) :=
    grothFiberMor_comp X c m₁ m₂ h₂
  have hcast :
      cast (congrArg G.obj hobj)
        (G.map gfm₂ (G.map gfm₁ e)) =
      G.map gfmc e := by
    have heqcast :
        G.map (eqToHom hobj) =
          cast (congrArg G.obj hobj) := by
      rw [eqToHom_map G hobj,
        eqToHom_eq_cast]
    rw [← heqcast]
    have hcancel :
        eqToHom (congrArg (Grothendieck.mk c)
          (fiberTgt_comp X c cp)) ≫
          eqToHom hobj = 𝟙 _ := by
      simp [eqToHom_trans]
    have step :
        gfm₁ ≫ gfm₂ ≫ eqToHom hobj =
          gfmc := by
      rw [← Category.assoc, hcomm,
        Category.assoc, hcancel,
        Category.comp_id]
    have step2 :
        G.map gfm₁ ≫ G.map gfm₂ ≫
          G.map (eqToHom hobj) =
        G.map gfmc := by
      simp only [← G.map_comp, step]
    exact congr_fun step2 e
  exact Sigma.ext hx
    (heq_of_cast_eq
      (congrArg G.obj hobj) hcast)

/-- The inverse presheaf: given a presheaf `G` on
the Grothendieck category, assembles the inverse
fiber functor, projection, and action into an
internal presheaf on `X`. -/
def inversePresheaf (G : X.groth ⥤ Type w) :
    PshInternalPresheaf X where
  fiber := inverseFiberFunctor X G
  proj := inverseProj X G
  action := inverseAction X G
  action_tgt := inverseAction_tgt X G
  action_id := fun c p ↦
    inverseAction_id X G c p
  action_assoc := fun c e m₁ m₂ h₁ h₂ ↦
    inverseAction_assoc X G c e m₁ m₂ h₁ h₂

/-- The natural transformation between inverse
fiber functors induced by a morphism of
presheaves on the Grothendieck category. -/
def inverseNatTrans
    {G G' : X.groth ⥤ Type w}
    (α : G ⟶ G') :
    inverseFiberFunctor X G ⟶
      inverseFiberFunctor X G' where
  app c := fun ⟨x, e⟩ ↦
    ⟨x, α.app ⟨c, x⟩ e⟩
  naturality c c' f := by
    funext ⟨x, e⟩
    simp only [types_comp_apply,
      inverseFiberFunctor,
      inverseFiberMap]
    have hnat := congr_fun (α.naturality
      (grothBaseMor X c c' f x)).symm e
    simp only [types_comp_apply] at hnat
    exact Sigma.ext rfl (heq_of_eq hnat.symm)

/-- The morphism of internal presheaves induced
by a natural transformation between presheaves
on the Grothendieck category. -/
def inversePresheafHom
    {G G' : X.groth ⥤ Type w}
    (α : G ⟶ G') :
    PshInternalPresheafHom
      (inversePresheaf X G)
      (inversePresheaf X G') where
  map := inverseNatTrans X α
  proj_comm := by
    ext c ⟨x, e⟩; rfl
  action_comm := by
    ext c ⟨⟨⟨x, e⟩, m⟩,
      (h : x = fiberSrc X c m)⟩
    simp only [NatTrans.comp_app,
      types_comp_apply,
      inverseNatTrans,
      presheafPullbackFst,
      presheafPullbackSnd,
      presheafPullbackCone]
    exact Sigma.ext rfl
      (heq_of_eq
        (congr_fun (α.naturality
          (grothFiberMor X c x m h)).symm
          e))

/-- The inverse functor: sends a presheaf on the
Grothendieck category to an internal presheaf
on `X`, and a natural transformation to a
morphism of internal presheaves. -/
def inverseFunctor :
    (X.groth ⥤ Type w) ⥤
      PshInternalPresheaf X where
  obj G := inversePresheaf X G
  map α := inversePresheafHom X α
  map_id G := by
    apply PshInternalPresheafHom.ext
    apply NatTrans.ext; funext c
    ext ⟨x, e⟩; rfl
  map_comp f g := by
    apply PshInternalPresheafHom.ext
    apply NatTrans.ext; funext c
    ext ⟨x, e⟩; rfl

/-- Every Grothendieck morphism decomposes as a
base morphism followed by a fiber morphism
followed by an `eqToHom`. -/
theorem groth_decompose
    {p q : X.groth}
    (m : p ⟶ q) :
    grothBaseMor X p.base q.base m.base
        p.fiber ≫
      grothFiberMor X q.base
        ((fiberRestrict X m.base).obj p.fiber)
        m.fiber.val
        m.fiber.prop.1.symm ≫
      eqToHom (congrArg (Grothendieck.mk q.base)
        m.fiber.prop.2) = m := by
  apply Grothendieck.ext
  case w_base =>
    simp [grothBaseMor, grothFiberMor]
  case w_fiber =>
    apply fiberHom_ext
    simp only [
      Grothendieck.comp_fiber,
      Grothendieck.fiber_eqToHom,
      grothBaseMor, grothFiberMor,
      CategoryTheory.Functor.map_id,
      Category.id_comp,
      eqToHom_trans_assoc]
    simp only [externalize, fiberRestrict]
    simp [fiberHom_val_eqToHom_comp,
      fiberHom_val_comp_eqToHom,
      Grothendieck.base_eqToHom,
      FunctorToTypes.map_id_apply]


end Inverse

end GebLean
