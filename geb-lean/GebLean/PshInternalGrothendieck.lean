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

end Inverse

end GebLean
