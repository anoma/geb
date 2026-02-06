import Mathlib.CategoryTheory.Category.Factorisation
import Mathlib.CategoryTheory.Adjunction.Reflective
import GebLean.Utilities.TwistedArrow
import GebLean.Utilities.ConnectedGrothendieck

/-!
# Factorization categories

This module re-exports the factorization category from mathlib
(`CategoryTheory.Factorisation`) and provides additional
constructions.

Given a morphism `f : X ⟶ Y` in a category `C`, the factorization
category `Factorisation f` has:
- Objects: triples `(mid, ι : X ⟶ mid, π : mid ⟶ Y)` with
  `ι ≫ π = f`.
- Morphisms `d ⟶ e`: maps `h : d.mid ⟶ e.mid` satisfying
  `d.ι ≫ h = e.ι` and `h ≫ e.π = d.π`.

The category has an initial object `Factorisation.initial`
(with `mid := X`, `ι := 𝟙 X`, `π := f`) and a terminal object
`Factorisation.terminal` (with `mid := Y`, `ι := f`, `π := 𝟙 Y`).

The forgetful functor `Factorisation.forget : Factorisation f ⥤ C`
sends each factorization to its midpoint.

## Main definitions

- `factorisationMapObj`: Given a twisted arrow morphism `φ : x ⟶ y`,
  transforms a factorization of `twArr x` into a factorization of
  `twArr y` by pre-composing `ι` with `twDomArr φ` and
  post-composing `π` with `twCodArr φ`.

- `factorisationFunctor`: The `Cat`-valued functor
  `TwistedArrow C ⥤ Cat` sending each arrow `f` to `Factorisation f`
  and each twisted arrow morphism to the induced functor between
  factorization categories.

- `factorisationOpEquiv` / `factorisationOpIso`:
  The equivalence and categorical isomorphism
  `(Factorisation f)ᵒᵖ ≌ Factorisation (f.op)`.

- `TotalFactObj`: The total factorization category, whose objects
  are composable pairs `dom ──ι──▸ mid ──π──▸ cod` in `C`.

- `totalFactToArrow`: The forgetful functor from `TotalFactObj C`
  to `Arrow C` sending `(ι, π)` to `ι ≫ π`.

- `factorisationToTotal`: The inclusion of a fiber
  `Factorisation f` into the total factorization category.

- `factorisationUnderOverEquiv`: The equivalence
  `Factorisation f ≌ Under (Over.mk f)`.

- `factorisationOverUnderEquiv`: The equivalence
  `Factorisation f ≌ Over (Under.mk f)`.

- `factorisationToOverTw`: The fully faithful inclusion
  `Factorisation f ⥤ Over (twObjMk f)`.

- `overTwToFactorisation`: The reflector (left adjoint)
  `Over (twObjMk f) ⥤ Factorisation f`.

- `factorisationToOverTw_reflective`: The `Reflective`
  instance for `factorisationToOverTw f`.

## References

- https://ncatlab.org/nlab/show/factorization+category
- `Mathlib.CategoryTheory.Category.Factorisation`
-/

namespace GebLean

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]

/-! ## Functoriality of factorization categories

A twisted arrow morphism `φ : x ⟶ y` in `TwistedArrow C` consists
of `twDomArr φ : twDom y ⟶ twDom x` and
`twCodArr φ : twCod x ⟶ twCod y` satisfying
`twDomArr φ ≫ twArr x ≫ twCodArr φ = twArr y`.

Given such `φ`, each factorization `(mid, ι, π)` of `twArr x`
induces a factorization `(mid, twDomArr φ ≫ ι, π ≫ twCodArr φ)`
of `twArr y`. The midpoint and morphisms between midpoints are
unchanged, yielding a functor
`Factorisation (twArr x) ⥤ Factorisation (twArr y)`.
-/

/-- The image of a factorization object under a twisted arrow
morphism. The midpoint is unchanged; `ι` is pre-composed with the
domain arrow and `π` is post-composed with the codomain arrow. -/
def factorisationMapObj
    {x y : TwistedArrow C} (φ : x ⟶ y)
    (d : Factorisation (twArr x)) :
    Factorisation (twArr y) where
  mid := d.mid
  ι := twDomArr φ ≫ d.ι
  π := d.π ≫ twCodArr φ
  ι_π := by
    rw [Category.assoc, ← Category.assoc d.ι,
      d.ι_π]
    exact twHomComm φ

/-- The image of a factorization morphism under a twisted arrow
morphism. The underlying map `h` between midpoints is unchanged. -/
def factorisationMapHom
    {x y : TwistedArrow C} (φ : x ⟶ y)
    {d e : Factorisation (twArr x)}
    (g : d ⟶ e) :
    factorisationMapObj φ d ⟶ factorisationMapObj φ e where
  h := g.h
  ι_h := by
    simp only [factorisationMapObj, Category.assoc]
    rw [g.ι_h]
  h_π := by
    simp only [factorisationMapObj, ← Category.assoc]
    rw [g.h_π]

/-- The functor between factorization categories induced by a
twisted arrow morphism. Preserves midpoints and the maps between
them; only the factorization data (`ι` and `π`) changes. -/
def factorisationMap
    {x y : TwistedArrow C} (φ : x ⟶ y) :
    Factorisation (twArr x) ⥤ Factorisation (twArr y) where
  obj := factorisationMapObj φ
  map := factorisationMapHom φ
  map_id _ := Factorisation.Hom.ext rfl
  map_comp _ _ := Factorisation.Hom.ext rfl

@[simp]
private theorem factorisationMapObj_mid
    {x y : TwistedArrow C} (φ : x ⟶ y)
    (d : Factorisation (twArr x)) :
    (factorisationMapObj φ d).mid = d.mid := rfl

@[simp]
private theorem factorisationMapObj_ι
    {x y : TwistedArrow C} (φ : x ⟶ y)
    (d : Factorisation (twArr x)) :
    (factorisationMapObj φ d).ι = twDomArr φ ≫ d.ι := rfl

@[simp]
private theorem factorisationMapObj_π
    {x y : TwistedArrow C} (φ : x ⟶ y)
    (d : Factorisation (twArr x)) :
    (factorisationMapObj φ d).π = d.π ≫ twCodArr φ := rfl

@[simp]
private theorem factorisation_comp_h
    {X Y : C} {f : X ⟶ Y}
    {a b c : Factorisation f}
    (g₁ : a ⟶ b) (g₂ : b ⟶ c) :
    (g₁ ≫ g₂).h = g₁.h ≫ g₂.h := rfl

@[simp]
private theorem factorisation_eqToHom_h
    {X Y : C} {f : X ⟶ Y}
    {d e : Factorisation f}
    (p : d = e) :
    (eqToHom p).h =
    eqToHom (congrArg Factorisation.mid p) := by
  subst p; rfl

/-- The `Cat`-valued functor sending each arrow `f : a ⟶ b` in `C`
(viewed as an object of `TwistedArrow C`) to its factorization
category `Factorisation f`, and each twisted arrow morphism to the
induced functor between factorization categories. -/
def factorisationFunctor (C : Type u) [Category.{v} C] :
    TwistedArrow C ⥤ Cat.{max u v, max u v} where
  obj tw := Cat.of (Factorisation (twArr tw))
  map φ := (factorisationMap φ).toCatHom
  map_id tw := by
    apply Cat.Hom.ext
    simp only [Functor.toCatHom_toFunctor,
      Cat.Hom.id_toFunctor]
    refine CategoryTheory.Functor.ext
      (fun d ↦ ?_) (fun d e f ↦ ?_)
    · cases d
      simp only [factorisationMap, factorisationMapObj,
        Functor.id_obj, Factorisation.mk.injEq,
        heq_eq_eq, true_and]
      exact ⟨twDomArr_id tw ▸ Category.id_comp _,
        twCodArr_id tw ▸ Category.comp_id _⟩
    · apply Factorisation.Hom.ext
      simp only [factorisationMap,
        factorisationMapHom,
        factorisation_comp_h,
        factorisation_eqToHom_h,
        Functor.id_map, eqToHom_refl,
        Category.id_comp, Category.comp_id]
  map_comp φ ψ := by
    apply Cat.Hom.ext
    simp only [Functor.toCatHom_toFunctor,
      Cat.Hom.comp_toFunctor]
    refine CategoryTheory.Functor.ext
      (fun d ↦ ?_) (fun d e f ↦ ?_)
    · cases d
      simp only [factorisationMap, factorisationMapObj,
        Functor.comp_obj, Factorisation.mk.injEq,
        heq_eq_eq, true_and]
      exact ⟨by rw [twDomArr_comp, Category.assoc],
        by rw [twCodArr_comp, ← Category.assoc]⟩
    · apply Factorisation.Hom.ext
      simp only [factorisationMap,
        factorisationMapHom,
        factorisation_comp_h,
        factorisation_eqToHom_h,
        Functor.comp_map, eqToHom_refl,
        Category.id_comp, Category.comp_id]

/-! ## Opposite factorization isomorphism

The opposite of the factorization category is isomorphic to the
factorization category of the opposite morphism:
`(Factorisation f)ᵒᵖ ≅ Factorisation (f.op)`.
-/

section OpFactorisation

variable {X Y : C} (f : X ⟶ Y)

/-- Map a factorization of `f` to a factorization of `f.op`
by swapping `ι` and `π` and taking their `op`. -/
def factorisationToOp
    (d : Factorisation f) : Factorisation f.op where
  mid := Opposite.op d.mid
  ι := d.π.op
  π := d.ι.op
  ι_π := by
    rw [← op_comp, d.ι_π]

/-- Map a factorization of `f.op` back to a factorization
of `f` by unswapping. -/
def factorisationFromOp
    (d : Factorisation f.op) : Factorisation f where
  mid := d.mid.unop
  ι := d.π.unop
  π := d.ι.unop
  ι_π := by
    rw [← unop_comp, d.ι_π, Quiver.Hom.unop_op]

@[simp]
lemma factorisationToOp_mid (d : Factorisation f) :
    (factorisationToOp f d).mid = Opposite.op d.mid := rfl

@[simp]
lemma factorisationToOp_ι (d : Factorisation f) :
    (factorisationToOp f d).ι = d.π.op := rfl

@[simp]
lemma factorisationToOp_π (d : Factorisation f) :
    (factorisationToOp f d).π = d.ι.op := rfl

@[simp]
lemma factorisationFromOp_mid
    (d : Factorisation f.op) :
    (factorisationFromOp f d).mid = d.mid.unop := rfl

@[simp]
lemma factorisationFromOp_ι
    (d : Factorisation f.op) :
    (factorisationFromOp f d).ι = d.π.unop := rfl

@[simp]
lemma factorisationFromOp_π
    (d : Factorisation f.op) :
    (factorisationFromOp f d).π = d.ι.unop := rfl

lemma factorisationToOp_fromOp
    (d : Factorisation f.op) :
    factorisationToOp f (factorisationFromOp f d) = d := by
  cases d
  simp only [factorisationToOp, factorisationFromOp,
    Quiver.Hom.op_unop, Opposite.op_unop]

lemma factorisationFromOp_toOp
    (d : Factorisation f) :
    factorisationFromOp f (factorisationToOp f d) = d := by
  cases d
  simp only [factorisationToOp, factorisationFromOp,
    Quiver.Hom.unop_op, Opposite.unop_op]

/-- The functor `(Factorisation f)ᵒᵖ ⥤ Factorisation (f.op)`.

On objects, sends `op d` to `factorisationToOp f d`.
On morphisms, a morphism `op d ⟶ op e` in the opposite category
is a morphism `e ⟶ d` in `Factorisation f`, consisting of
`h : e.mid ⟶ d.mid`. This maps to `h.op : op d.mid ⟶ op e.mid`
in `Factorisation (f.op)`. -/
def factorisationOpToOpFactorisation :
    (Factorisation f)ᵒᵖ ⥤ Factorisation f.op where
  obj d := factorisationToOp f d.unop
  map {d e} g :=
    { h := g.unop.h.op
      ι_h := by
        simp only [factorisationToOp, ← op_comp,
          Factorisation.Hom.h_π]
      h_π := by
        simp only [factorisationToOp, ← op_comp,
          Factorisation.Hom.ι_h] }
  map_id _ := Factorisation.Hom.ext rfl
  map_comp _ _ := Factorisation.Hom.ext rfl

/-- The functor `Factorisation (f.op) ⥤ (Factorisation f)ᵒᵖ`.

On objects, sends `d` to `op (factorisationFromOp f d)`.
On morphisms, `h : d.mid ⟶ e.mid` in `Factorisation (f.op)`
maps to `h.unop : e'.mid ⟶ d'.mid` viewed as a morphism
`op d' ⟶ op e'` in the opposite category. -/
def opFactorisationToFactorisationOp :
    Factorisation f.op ⥤ (Factorisation f)ᵒᵖ where
  obj d := Opposite.op (factorisationFromOp f d)
  map {d e} g :=
    Quiver.Hom.op
      { h := g.h.unop
        ι_h := by
          simp only [factorisationFromOp,
            ← unop_comp, Factorisation.Hom.h_π]
        h_π := by
          simp only [factorisationFromOp,
            ← unop_comp, Factorisation.Hom.ι_h] }
  map_id _ := Quiver.Hom.unop_inj (Factorisation.Hom.ext rfl)
  map_comp _ _ :=
    Quiver.Hom.unop_inj (Factorisation.Hom.ext rfl)

lemma factorisationOpRoundTrip_obj (d : (Factorisation f)ᵒᵖ) :
    (opFactorisationToFactorisationOp f).obj
      ((factorisationOpToOpFactorisation f).obj d) = d := by
  simp only [factorisationOpToOpFactorisation,
    opFactorisationToFactorisationOp]
  exact congrArg Opposite.op (factorisationFromOp_toOp f d.unop)

lemma opFactorisationRoundTrip_obj
    (d : Factorisation f.op) :
    (factorisationOpToOpFactorisation f).obj
      ((opFactorisationToFactorisationOp f).obj d) = d := by
  simp only [factorisationOpToOpFactorisation,
    opFactorisationToFactorisationOp]
  exact factorisationToOp_fromOp f d

lemma factorisationOpRoundTrip_map
    {d e : (Factorisation f)ᵒᵖ}
    (g : d ⟶ e) :
    (factorisationOpToOpFactorisation f ⋙
      opFactorisationToFactorisationOp f).map g = g := by
  apply Quiver.Hom.unop_inj
  apply Factorisation.Hom.ext
  simp only [Functor.comp_map,
    factorisationOpToOpFactorisation,
    opFactorisationToFactorisationOp,
    Quiver.Hom.unop_op]

lemma opFactorisationRoundTrip_map
    {d e : Factorisation f.op}
    (g : d ⟶ e) :
    (opFactorisationToFactorisationOp f ⋙
      factorisationOpToOpFactorisation f).map g = g := by
  apply Factorisation.Hom.ext
  simp only [Functor.comp_map,
    factorisationOpToOpFactorisation,
    opFactorisationToFactorisationOp]
  exact Quiver.Hom.op_unop g.h

/-- The equivalence `(Factorisation f)ᵒᵖ ≌ Factorisation (f.op)`. -/
def factorisationOpEquiv :
    (Factorisation f)ᵒᵖ ≌ Factorisation f.op where
  functor := factorisationOpToOpFactorisation f
  inverse := opFactorisationToFactorisationOp f
  unitIso := NatIso.ofComponents
    (fun d => eqToIso
      (factorisationOpRoundTrip_obj f d).symm)
    (fun {d e} g => by
      simp only [eqToIso.hom, Functor.id_obj,
        Functor.comp_obj, Functor.id_map]
      rw [eqToHom_refl, eqToHom_refl,
        Category.id_comp, Category.comp_id]
      exact (factorisationOpRoundTrip_map f g).symm)
  counitIso := NatIso.ofComponents
    (fun d => eqToIso
      (opFactorisationRoundTrip_obj f d))
    (fun {d e} g => by
      simp only [eqToIso.hom, Functor.comp_obj,
        Functor.id_obj, Functor.id_map]
      rw [eqToHom_refl, eqToHom_refl,
        Category.id_comp, Category.comp_id]
      exact opFactorisationRoundTrip_map f g)

/-- The categorical isomorphism
`(Factorisation f)ᵒᵖ ≅Cat Factorisation (f.op)`. -/
def factorisationOpIso :
    (Factorisation f)ᵒᵖ ≅Cat Factorisation f.op :=
  Cat.isoOfEquiv
    (factorisationOpEquiv f)
    (factorisationOpRoundTrip_obj f)
    (opFactorisationRoundTrip_obj f)

end OpFactorisation

/-! ## The total factorization category

The total factorization category collects all factorizations
across all morphisms in `C`. An object is a morphism `f : a ⟶ b`
together with a factorization `a ⟶ m ⟶ b` of `f`. A morphism
is a commuting diagram of the form:

```text
a  ──ι──▸  m  ──π──▸  b
│          │          │
g          k          h
▾          ▾          ▾
a' ──ι'─▸  m' ──π'─▸  b'
```

satisfying `ι ≫ k = g ≫ ι'` and `k ≫ π' = π ≫ h`.
-/

section TotalFactorisation

variable (C : Type u) [Category.{v} C]

/-- An object of the total factorization category: a morphism
`f : a ⟶ b` together with a factorization `a ──ι──▸ m ──π──▸ b`
with `ι ≫ π = f`. -/
@[ext]
structure TotalFactObj where
  /-- The domain of the arrow -/
  dom : C
  /-- The codomain of the arrow -/
  cod : C
  /-- The midpoint of the factorization -/
  mid : C
  /-- The first factor `ι : dom ⟶ mid` -/
  ι : dom ⟶ mid
  /-- The second factor `π : mid ⟶ cod` -/
  π : mid ⟶ cod

/-- The composed arrow `ι ≫ π` of a total factorization object. -/
def TotalFactObj.arr (x : TotalFactObj C) : x.dom ⟶ x.cod :=
  x.ι ≫ x.π

/-- A morphism in the total factorization category: three
morphisms `(domMorph, midMorph, codMorph)` making both squares
commute. -/
@[ext]
structure TotalFactHom (x y : TotalFactObj C) where
  /-- The morphism between domains -/
  domMorph : x.dom ⟶ y.dom
  /-- The morphism between midpoints -/
  midMorph : x.mid ⟶ y.mid
  /-- The morphism between codomains -/
  codMorph : x.cod ⟶ y.cod
  /-- The left square commutes: `ι ≫ midMorph = domMorph ≫ ι'` -/
  ι_comm : x.ι ≫ midMorph = domMorph ≫ y.ι
  /-- The right square commutes: `midMorph ≫ π' = π ≫ codMorph` -/
  π_comm : midMorph ≫ y.π = x.π ≫ codMorph

/-- The identity morphism in the total factorization category. -/
def TotalFactHom.id (x : TotalFactObj C) :
    TotalFactHom C x x where
  domMorph := 𝟙 _
  midMorph := 𝟙 _
  codMorph := 𝟙 _
  ι_comm := by simp
  π_comm := by simp

/-- Composition of morphisms in the total factorization
category. -/
def TotalFactHom.comp {x y z : TotalFactObj C}
    (f : TotalFactHom C x y)
    (g : TotalFactHom C y z) :
    TotalFactHom C x z where
  domMorph := f.domMorph ≫ g.domMorph
  midMorph := f.midMorph ≫ g.midMorph
  codMorph := f.codMorph ≫ g.codMorph
  ι_comm := by
    rw [Category.assoc, ← g.ι_comm,
      ← Category.assoc, f.ι_comm, Category.assoc]
  π_comm := by
    rw [Category.assoc, g.π_comm,
      ← Category.assoc, f.π_comm, Category.assoc]

@[simp]
lemma TotalFactHom.id_domMorph (x : TotalFactObj C) :
    (TotalFactHom.id C x).domMorph = 𝟙 _ := rfl

@[simp]
lemma TotalFactHom.id_midMorph (x : TotalFactObj C) :
    (TotalFactHom.id C x).midMorph = 𝟙 _ := rfl

@[simp]
lemma TotalFactHom.id_codMorph (x : TotalFactObj C) :
    (TotalFactHom.id C x).codMorph = 𝟙 _ := rfl

@[simp]
lemma TotalFactHom.comp_domMorph
    {x y z : TotalFactObj C}
    (f : TotalFactHom C x y)
    (g : TotalFactHom C y z) :
    (TotalFactHom.comp C f g).domMorph =
    f.domMorph ≫ g.domMorph := rfl

@[simp]
lemma TotalFactHom.comp_midMorph
    {x y z : TotalFactObj C}
    (f : TotalFactHom C x y)
    (g : TotalFactHom C y z) :
    (TotalFactHom.comp C f g).midMorph =
    f.midMorph ≫ g.midMorph := rfl

@[simp]
lemma TotalFactHom.comp_codMorph
    {x y z : TotalFactObj C}
    (f : TotalFactHom C x y)
    (g : TotalFactHom C y z) :
    (TotalFactHom.comp C f g).codMorph =
    f.codMorph ≫ g.codMorph := rfl

instance : Category (TotalFactObj C) where
  Hom := TotalFactHom C
  id := TotalFactHom.id C
  comp := TotalFactHom.comp C
  id_comp _ := TotalFactHom.ext
    (Category.id_comp _) (Category.id_comp _)
    (Category.id_comp _)
  comp_id _ := TotalFactHom.ext
    (Category.comp_id _) (Category.comp_id _)
    (Category.comp_id _)
  assoc _ _ _ := TotalFactHom.ext
    (Category.assoc _ _ _) (Category.assoc _ _ _)
    (Category.assoc _ _ _)

/-- The arrow `ι ≫ π` determined by a morphism of total
factorization objects is natural:
`arr x ≫ codMorph = domMorph ≫ arr y`. -/
lemma TotalFactHom.arr_comm {x y : TotalFactObj C}
    (f : TotalFactHom C x y) :
    x.arr ≫ f.codMorph = f.domMorph ≫ y.arr := by
  unfold TotalFactObj.arr
  rw [Category.assoc, ← f.π_comm,
    ← Category.assoc, f.ι_comm, Category.assoc]

/-- The forgetful functor from the total factorization category
to the arrow category, sending `(dom, mid, cod, ι, π)` to
`ι ≫ π : dom ⟶ cod`. -/
def totalFactToArrow :
    TotalFactObj C ⥤ Arrow C where
  obj x := Arrow.mk x.arr
  map f := Arrow.homMk f.domMorph f.codMorph
    (TotalFactHom.arr_comm C f).symm
  map_id _ := by ext <;> rfl
  map_comp _ _ := by ext <;> rfl

/-- The inclusion of a fiber `Factorisation f` into the total
factorization category. -/
def factorisationToTotal {X Y : C} (f : X ⟶ Y) :
    Factorisation f ⥤ TotalFactObj C where
  obj d :=
    { dom := X
      cod := Y
      mid := d.mid
      ι := d.ι
      π := d.π }
  map g :=
    { domMorph := 𝟙 _
      midMorph := g.h
      codMorph := 𝟙 _
      ι_comm := by
        simp only [Category.id_comp]
        exact g.ι_h
      π_comm := by
        simp only [Category.comp_id]
        exact g.h_π }
  map_id _ := TotalFactHom.ext
    rfl rfl rfl
  map_comp _ _ := TotalFactHom.ext
    (Category.id_comp _).symm rfl
    (Category.id_comp _).symm

/-- The forgetful functor from the total factorization category
to `C`, sending each object to its midpoint. -/
def totalFactForgetMid :
    TotalFactObj C ⥤ C where
  obj x := x.mid
  map f := f.midMorph
  map_id _ := rfl
  map_comp _ _ := rfl

end TotalFactorisation

section TwGrothendieckFactorisation

variable (C : Type u) [Category.{v} C]

/-- The total factorization category as an instance of the connected
Grothendieck construction. An object consists of an arrow
`f : a ⟶ b` in `C` together with a factorization of `f`. -/
abbrev TotalFactGrothendieck :=
  TwGrothendieckObj C (factorisationFunctor C)

/-- Two factorisations with the same midpoint, first factor,
and second factor are heterogeneously equal, even when the
composed arrows differ propositionally. -/
private lemma factorisation_heq
    {X Y : C} {f g : X ⟶ Y}
    (d : Factorisation f) (e : Factorisation g)
    (hmid : d.mid = e.mid)
    (hι : HEq d.ι e.ι)
    (hπ : HEq d.π e.π) :
    HEq d e := by
  cases d; cases e
  cases hmid; cases hι; cases hπ
  rename_i ι_π₁ ι_π₂
  have : f = g := ι_π₁.symm.trans ι_π₂
  subst this
  exact heq_of_eq (by congr 1)

/-- The type equivalence between the connected Grothendieck
construction over `factorisationFunctor C` and the total
factorization category. The forward map extracts domain,
codomain, midpoint, and the two factors from the arrow and
fiber. The inverse packs the composed arrow and factorization
data. -/
def totalFactGrothendieckEquivObj :
    TotalFactGrothendieck C ≃ TotalFactObj C where
  toFun x :=
    { dom := twDom' x.arrow
      cod := twCod' x.arrow
      mid := x.fiber.mid
      ι := x.fiber.ι
      π := x.fiber.π }
  invFun y :=
    { arrow := twObjMk' (y.ι ≫ y.π)
      fiber :=
        { mid := y.mid
          ι := y.ι
          π := y.π
          ι_π := rfl } }
  right_inv _ := rfl
  left_inv x := by
    apply ConnGrothendieckObj.ext
    · exact congrArg twObjMk' x.fiber.ι_π
    · dsimp only []
      apply factorisation_heq <;> rfl

private abbrev toTotalFact :=
  totalFactGrothendieckEquivObj C

/-- The `Category` instance on `TotalFactGrothendieck C`,
transferred from `TotalFactObj C` via
`totalFactGrothendieckEquivObj`. Morphisms from `x` to `y` are
`TotalFactHom C (e x) (e y)` where `e` is the object
equivalence. -/
instance : Category (TotalFactGrothendieck C) where
  Hom x y :=
    TotalFactHom C (toTotalFact C x) (toTotalFact C y)
  id x := TotalFactHom.id C (toTotalFact C x)
  comp f g := TotalFactHom.comp C f g
  id_comp _ := TotalFactHom.ext
    (Category.id_comp _) (Category.id_comp _)
    (Category.id_comp _)
  comp_id _ := TotalFactHom.ext
    (Category.comp_id _) (Category.comp_id _)
    (Category.comp_id _)
  assoc _ _ _ := TotalFactHom.ext
    (Category.assoc _ _ _) (Category.assoc _ _ _)
    (Category.assoc _ _ _)

/-- The functor from `TotalFactObj C` to
`TotalFactGrothendieck C`, given by the inverse of
`totalFactGrothendieckEquivObj`. On objects, packs the
composable pair into a twisted arrow and factorisation.
On morphisms, the identity transport (since `right_inv`
is `rfl`). -/
def totalFactToGrothendieck :
    TotalFactObj C ⥤ TotalFactGrothendieck C where
  obj x := (toTotalFact C).symm x
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The functor from `TotalFactGrothendieck C` to
`TotalFactObj C`, given by `totalFactGrothendieckEquivObj`.
On objects, extracts domain, codomain, midpoint, and the
two factors. On morphisms, the identity transport (since
morphisms are defined as `TotalFactHom C (e x) (e y)`). -/
def grothendieckToTotalFact :
    TotalFactGrothendieck C ⥤ TotalFactObj C where
  obj x := toTotalFact C x
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl

/-- `grothendieckToTotalFact ⋙ totalFactToGrothendieck`
is the identity on objects. -/
private lemma grothendieckTotalRoundTrip_obj
    (x : TotalFactGrothendieck C) :
    (totalFactToGrothendieck C).obj
      ((grothendieckToTotalFact C).obj x) = x :=
  (toTotalFact C).left_inv x

/-- `totalFactToGrothendieck ⋙ grothendieckToTotalFact`
is the identity on objects. -/
private lemma totalGrothendieckRoundTrip_obj
    (x : TotalFactObj C) :
    (grothendieckToTotalFact C).obj
      ((totalFactToGrothendieck C).obj x) = x :=
  (toTotalFact C).right_inv x

/-- The categorical isomorphism
`TotalFactObj C ≅Cat TotalFactGrothendieck C`. -/
def totalFactIsoGrothendieck :
    TotalFactObj C ≅Cat TotalFactGrothendieck C where
  hom := (totalFactToGrothendieck C).toCatHom
  inv := (grothendieckToTotalFact C).toCatHom
  hom_inv_id := rfl
  inv_hom_id := by
    apply Cat.Hom.ext
    simp only [Cat.Hom.comp_toFunctor, Cat.Hom.id_toFunctor,
      Functor.toCatHom_toFunctor]
    refine Functor.hext
      (grothendieckTotalRoundTrip_obj C)
      (fun x y f => ?_)
    exact heq_of_eq rfl

end TwGrothendieckFactorisation

/-! ## Equivalence with Under-in-Over and Over-in-Under

For `f : X ⟶ Y`, the factorization category `Factorisation f` is
equivalent to `Under (Over.mk f)` (the under category of `f` viewed
as an object of `Over Y`) and to `Over (Under.mk f)` (the over
category of `f` viewed as an object of `Under X`).
-/

section FactorisationUnderOverEquiv

variable {X Y : C} (f : X ⟶ Y)

/-- The functor from `Factorisation f` to `Under (Over.mk f)`.
Each factorization `(D, ι, π)` with `ι ≫ π = f` maps to the
`Under`-object with target `Over.mk π : Over Y` and structure
morphism `Over.homMk ι : Over.mk f ⟶ Over.mk π`. -/
def factorisationToUnderOver :
    Factorisation f ⥤ Under (Over.mk f : Over Y) where
  obj d := Under.mk
    (Over.homMk (U := Over.mk f) (V := Over.mk d.π)
      d.ι d.ι_π)
  map {d e} g := Under.homMk
    (Over.homMk g.h g.h_π)
    (by
      apply Over.OverMorphism.ext
      exact g.ι_h)
  map_id _ := by
    apply Under.UnderMorphism.ext
    apply Over.OverMorphism.ext
    rfl
  map_comp _ _ := by
    apply Under.UnderMorphism.ext
    apply Over.OverMorphism.ext
    rfl

/-- The functor from `Under (Over.mk f)` to `Factorisation f`.
Each `Under`-object with target `(D, π : D ⟶ Y)` and structure
morphism `Over.homMk ι` maps to the factorization `(D, ι, π)`. -/
def underOverToFactorisation :
    Under (Over.mk f : Over Y) ⥤ Factorisation f where
  obj u :=
    { mid := u.right.left
      ι := u.hom.left
      π := u.right.hom
      ι_π := Over.w u.hom }
  map g :=
    { h := g.right.left
      ι_h := congrArg CommaMorphism.left (Under.w g)
      h_π := Over.w g.right }
  map_id _ := Factorisation.Hom.ext rfl
  map_comp _ _ := Factorisation.Hom.ext rfl

private lemma underOverRoundTrip_obj
    (d : Factorisation f) :
    (factorisationToUnderOver f ⋙
      underOverToFactorisation f).obj d = d := by
  cases d; rfl

private lemma overUnderFactRoundTrip_obj
    (u : Under (Over.mk f : Over Y)) :
    (underOverToFactorisation f ⋙
      factorisationToUnderOver f).obj u = u := by
  cases u; congr 1

private lemma underOverRoundTrip_map
    {d e : Factorisation f}
    (g : d ⟶ e) :
    (factorisationToUnderOver f ⋙
      underOverToFactorisation f).map g = g := by
  apply Factorisation.Hom.ext; rfl

private lemma overUnderFactRoundTrip_map
    {u v : Under (Over.mk f : Over Y)}
    (g : u ⟶ v) :
    (underOverToFactorisation f ⋙
      factorisationToUnderOver f).map g =
    eqToHom (overUnderFactRoundTrip_obj f u).symm ≫
    g ≫ eqToHom (overUnderFactRoundTrip_obj f v) := by
  cases u; cases v
  simp only [eqToHom_refl,
    Category.id_comp, Category.comp_id]
  apply Under.UnderMorphism.ext
  apply Over.OverMorphism.ext; rfl

/-- The equivalence
`Factorisation f ≌ Under (Over.mk f : Over Y)`. -/
def factorisationUnderOverEquiv :
    Factorisation f ≌ Under (Over.mk f : Over Y) :=
  CategoryTheory.Equivalence.mk
    (factorisationToUnderOver f)
    (underOverToFactorisation f)
    (NatIso.ofComponents
      (fun d => eqToIso
        (underOverRoundTrip_obj f d).symm)
      (fun {d e} g => by
        simp only [eqToIso.hom, Functor.id_obj,
          Functor.comp_obj, Functor.id_map]
        rw [eqToHom_refl, eqToHom_refl,
          Category.id_comp, Category.comp_id]
        exact (underOverRoundTrip_map f g).symm))
    (NatIso.ofComponents
      (fun u => eqToIso
        (overUnderFactRoundTrip_obj f u))
      (fun {u v} g => by
        simp only [eqToIso.hom, Functor.comp_obj,
          Functor.id_obj, Functor.id_map]
        rw [overUnderFactRoundTrip_map]
        simp))

end FactorisationUnderOverEquiv

section FactorisationOverUnderEquiv

variable {X Y : C} (f : X ⟶ Y)

/-- The functor from `Factorisation f` to `Over (Under.mk f)`.
Each factorization `(D, ι, π)` with `ι ≫ π = f` maps to the
`Over`-object with source `Under.mk ι : Under X` and structure
morphism `Under.homMk π : Under.mk ι ⟶ Under.mk f`. -/
def factorisationToOverUnder :
    Factorisation f ⥤ Over (Under.mk f : Under X) where
  obj d := Over.mk
    (Under.homMk (U := Under.mk d.ι)
      (V := Under.mk f) d.π d.ι_π)
  map {d e} g := Over.homMk
    (Under.homMk g.h (by exact g.ι_h))
    (by
      apply Under.UnderMorphism.ext
      exact g.h_π)
  map_id _ := by
    apply Over.OverMorphism.ext
    apply Under.UnderMorphism.ext
    rfl
  map_comp _ _ := by
    apply Over.OverMorphism.ext
    apply Under.UnderMorphism.ext
    rfl

/-- The functor from `Over (Under.mk f)` to `Factorisation f`.
Each `Over`-object with source `(D, ι : X ⟶ D)` and structure
morphism `Under.homMk π` maps to the factorization
`(D, ι, π)`. -/
def overUnderToFactorisation :
    Over (Under.mk f : Under X) ⥤ Factorisation f where
  obj o :=
    { mid := o.left.right
      ι := o.left.hom
      π := o.hom.right
      ι_π := Under.w o.hom }
  map g :=
    { h := g.left.right
      ι_h := Under.w g.left
      h_π := congrArg CommaMorphism.right (Over.w g) }
  map_id _ := Factorisation.Hom.ext rfl
  map_comp _ _ := Factorisation.Hom.ext rfl

private lemma overUnderRoundTrip_obj
    (d : Factorisation f) :
    (factorisationToOverUnder f ⋙
      overUnderToFactorisation f).obj d = d := by
  cases d; rfl

private lemma factOverUnderRoundTrip_obj
    (o : Over (Under.mk f : Under X)) :
    (overUnderToFactorisation f ⋙
      factorisationToOverUnder f).obj o = o := by
  cases o; rename_i l h; cases l; congr 1

private lemma overUnderRoundTrip_map
    {d e : Factorisation f}
    (g : d ⟶ e) :
    (factorisationToOverUnder f ⋙
      overUnderToFactorisation f).map g = g := by
  apply Factorisation.Hom.ext; rfl

private lemma factOverUnderRoundTrip_map
    {o p : Over (Under.mk f : Under X)}
    (g : o ⟶ p) :
    (overUnderToFactorisation f ⋙
      factorisationToOverUnder f).map g =
    eqToHom (factOverUnderRoundTrip_obj f o).symm ≫
    g ≫ eqToHom (factOverUnderRoundTrip_obj f p) := by
  cases o; cases p
  rename_i l₁ h₁ l₂ h₂
  cases l₁; cases l₂
  simp only [eqToHom_refl,
    Category.id_comp, Category.comp_id]
  apply Over.OverMorphism.ext
  apply Under.UnderMorphism.ext; rfl

/-- The equivalence
`Factorisation f ≌ Over (Under.mk f : Under X)`. -/
def factorisationOverUnderEquiv :
    Factorisation f ≌ Over (Under.mk f : Under X) :=
  CategoryTheory.Equivalence.mk
    (factorisationToOverUnder f)
    (overUnderToFactorisation f)
    (NatIso.ofComponents
      (fun d => eqToIso
        (overUnderRoundTrip_obj f d).symm)
      (fun {d e} g => by
        simp only [eqToIso.hom, Functor.id_obj,
          Functor.comp_obj, Functor.id_map]
        rw [eqToHom_refl, eqToHom_refl,
          Category.id_comp, Category.comp_id]
        exact (overUnderRoundTrip_map f g).symm))
    (NatIso.ofComponents
      (fun o => eqToIso
        (factOverUnderRoundTrip_obj f o))
      (fun {o p} g => by
        simp only [eqToIso.hom, Functor.comp_obj,
          Functor.id_obj, Functor.id_map]
        rw [factOverUnderRoundTrip_map]
        simp))

end FactorisationOverUnderEquiv

/-! ## Reflective inclusion into the twisted arrow slice

For `f : X ⟶ Y`, each factorization `(D, ι, π)` gives a
twisted arrow `ι : X ⟶ D` equipped with a morphism
`(𝟙 X, π) : twObjMk ι ⟶ twObjMk f`, hence an object of
`Over (twObjMk f)`. This inclusion is fully faithful and
has a left adjoint (the reflector), making `Factorisation f`
a reflective subcategory of `Over (twObjMk f)`.
-/

section FactorisationReflectiveInclusion

variable {X Y : C} (f : X ⟶ Y)

/-- The structure morphism in `Over (twObjMk f)` for a
factorization `d` of `f`. This is a twisted arrow morphism
from `twObjMk d.ι` to `twObjMk f` with domain component
`𝟙 X` and codomain component `d.π`. -/
def factorisationToOverTwHom
    (d : Factorisation f) :
    twObjMk d.ι ⟶ (twObjMk f : TwistedArrow C) :=
  twHomMk (x := twObjMk d.ι) (y := twObjMk f)
    (𝟙 X) d.π (by
      simp only [twObjMk_arr]
      rw [d.ι_π]
      exact Category.id_comp f)

/-- The twisted arrow morphism underlying the functorial map
of a factorisation morphism `g : d ⟶ e`. This goes from
`twObjMk d.ι` to `twObjMk e.ι` with domain component
`𝟙 X` and codomain component `g.h`. -/
def factorisationToOverTwMapArr
    {d e : Factorisation f} (g : d ⟶ e) :
    twObjMk d.ι ⟶ (twObjMk e.ι : TwistedArrow C) :=
  twHomMk (x := twObjMk d.ι) (y := twObjMk e.ι)
    (𝟙 X) g.h (by
      simp only [twObjMk_arr]
      rw [g.ι_h]
      exact Category.id_comp e.ι)

private lemma factorisationToOverTw_over
    {d e : Factorisation f} (g : d ⟶ e) :
    factorisationToOverTwMapArr f g ≫
      factorisationToOverTwHom f e =
      factorisationToOverTwHom f d := by
  apply twHom_ext
  · change 𝟙 X ≫ 𝟙 X = 𝟙 X
    exact Category.comp_id _
  · exact g.h_π

/-- The inclusion functor from `Factorisation f` to
`Over (twObjMk f)` in `TwistedArrow C`. Each factorization
`(D, ι, π)` maps to the twisted arrow `twObjMk ι` with
structure morphism `twHomMk (𝟙 X) π`. -/
def factorisationToOverTw :
    Factorisation f ⥤
      Over (twObjMk f : TwistedArrow C) where
  obj d := Over.mk (factorisationToOverTwHom f d)
  map g := Over.homMk
    (factorisationToOverTwMapArr f g)
    (factorisationToOverTw_over f g)
  map_id _ := by
    apply Over.OverMorphism.ext
    exact Subtype.ext rfl
  map_comp _ _ := by
    apply Over.OverMorphism.ext
    apply Subtype.ext
    simp only [Over.comp_left, Over.homMk_left]
    change ((𝟙 X).op, _) =
      ((𝟙 X).op ≫ (𝟙 X).op, _)
    congr 1
    exact (Category.comp_id _).symm

/-- The factorisation obtained from an object of
`Over (twObjMk f)`. Given a twisted arrow `tw` with a morphism
`φ : tw ⟶ twObjMk f`, the factorisation has
`mid := twCod tw`, `ι := twDomArr φ ≫ twArr tw`,
and `π := twCodArr φ`. -/
def overTwToFactorisationObj
    (o : Over (twObjMk f : TwistedArrow C)) :
    Factorisation f where
  mid := twCod o.left
  ι := twDomArr o.hom ≫ twArr o.left
  π := twCodArr o.hom
  ι_π := by
    rw [Category.assoc]
    exact twHomComm o.hom

private lemma overTwToFactorisation_ι_h
    {o₁ o₂ : Over (twObjMk f : TwistedArrow C)}
    (g : o₁ ⟶ o₂) :
    (overTwToFactorisationObj f o₁).ι ≫
      twCodArr g.left =
      (overTwToFactorisationObj f o₂).ι := by
  have hdom : twDomArr o₂.hom ≫ twDomArr g.left =
      twDomArr o₁.hom :=
    congrArg twDomArr (Over.w g)
  simp only [overTwToFactorisationObj, Category.assoc,
    ← hdom]
  congr 1
  exact twHomComm g.left

private lemma overTwToFactorisation_h_π
    {o₁ o₂ : Over (twObjMk f : TwistedArrow C)}
    (g : o₁ ⟶ o₂) :
    twCodArr g.left ≫
      (overTwToFactorisationObj f o₂).π =
      (overTwToFactorisationObj f o₁).π :=
  congrArg twCodArr (Over.w g)

/-- The reflector functor from `Over (twObjMk f)` to
`Factorisation f`. Given a twisted arrow `g : A ⟶ B` with
a morphism `(α, β) : g ⟶ f` satisfying `α ≫ g ≫ β = f`,
the reflector produces the factorisation `(B, α ≫ g, β)`. -/
def overTwToFactorisation :
    Over (twObjMk f : TwistedArrow C) ⥤
      Factorisation f where
  obj o := overTwToFactorisationObj f o
  map g :=
    { h := twCodArr g.left
      ι_h := overTwToFactorisation_ι_h f g
      h_π := overTwToFactorisation_h_π f g }
  map_id _ := Factorisation.Hom.ext rfl
  map_comp _ _ := Factorisation.Hom.ext rfl

private lemma factorisationToOverTw_domArr
    {d e : Factorisation f}
    (φ : (factorisationToOverTw f).obj d ⟶
      (factorisationToOverTw f).obj e) :
    twDomArr φ.left = 𝟙 X := by
  have h := congrArg twDomArr (Over.w φ)
  simp only [twDomArr_comp, factorisationToOverTw,
    factorisationToOverTwHom] at h
  exact (Category.id_comp _).symm.trans h

private def factorisationToOverTw_preimage
    {d e : Factorisation f}
    (φ : (factorisationToOverTw f).obj d ⟶
      (factorisationToOverTw f).obj e) :
    d ⟶ e where
  h := twCodArr φ.left
  ι_h := by
    have hdom := factorisationToOverTw_domArr f φ
    have hcomm := twHomComm φ.left
    change twDomArr φ.left ≫ d.ι ≫ twCodArr φ.left =
      e.ι at hcomm
    rw [hdom] at hcomm
    exact (Category.id_comp _).symm.trans hcomm
  h_π := congrArg twCodArr (Over.w φ)

/-- The inclusion `factorisationToOverTw f` is fully faithful.
A morphism in `Over (twObjMk f)` between images of the
inclusion is determined by its codomain component, which
equals the `h` of the underlying factorisation morphism. -/
def factorisationToOverTw_fullyFaithful :
    (factorisationToOverTw f).FullyFaithful where
  preimage φ := factorisationToOverTw_preimage f φ
  map_preimage φ := by
    apply Over.OverMorphism.ext
    apply twHom_ext
    · exact (factorisationToOverTw_domArr f φ).symm
    · rfl
  preimage_map _ := Factorisation.Hom.ext rfl

private def adjHomEquivForwardArr
    (o : Over (twObjMk f : TwistedArrow C))
    (d : Factorisation f)
    (g : (overTwToFactorisation f).obj o ⟶ d) :
    o.left ⟶ (twObjMk d.ι : TwistedArrow C) :=
  let dom := twDomArr o.hom
  twHomMk dom g.h (by
    rw [← Category.assoc, twObjMk_arr]
    exact g.ι_h)

private lemma adjHomEquivForwardArr_over
    (o : Over (twObjMk f : TwistedArrow C))
    (d : Factorisation f)
    (g : (overTwToFactorisation f).obj o ⟶ d) :
    adjHomEquivForwardArr f o d g ≫
      factorisationToOverTwHom f d = o.hom := by
  have hdom : twDomArr
      (adjHomEquivForwardArr f o d g ≫
        factorisationToOverTwHom f d) =
      twDomArr o.hom := by
    simp only [twDomArr_comp]
    exact Category.id_comp _
  have hcod : twCodArr
      (adjHomEquivForwardArr f o d g ≫
        factorisationToOverTwHom f d) =
      twCodArr o.hom := g.h_π
  exact twHom_ext _ _ hdom hcod

private def adjHomEquivForward
    (o : Over (twObjMk f : TwistedArrow C))
    (d : Factorisation f)
    (g : (overTwToFactorisation f).obj o ⟶ d) :
    o ⟶ (factorisationToOverTw f).obj d :=
  Over.homMk
    (adjHomEquivForwardArr f o d g)
    (adjHomEquivForwardArr_over f o d g)

private lemma overTw_round_trip_ι
    (d : Factorisation f) :
    ((overTwToFactorisation f).obj
      ((factorisationToOverTw f).obj d)).ι =
      d.ι := by
  simp only [overTwToFactorisation,
    factorisationToOverTw,
    overTwToFactorisationObj,
    factorisationToOverTwHom]
  exact Category.id_comp _

private lemma adjHomEquivInverse_ι_h
    (o : Over (twObjMk f : TwistedArrow C))
    (d : Factorisation f)
    (φ : o ⟶ (factorisationToOverTw f).obj d) :
    ((overTwToFactorisation f).obj o).ι ≫
      twCodArr φ.left = d.ι :=
  (overTwToFactorisation_ι_h f φ).trans
    (overTw_round_trip_ι f d)

private lemma adjHomEquivInverse_h_π
    (o : Over (twObjMk f : TwistedArrow C))
    (d : Factorisation f)
    (φ : o ⟶ (factorisationToOverTw f).obj d) :
    twCodArr φ.left ≫ d.π =
      ((overTwToFactorisation f).obj o).π :=
  overTwToFactorisation_h_π f φ

private def adjHomEquivInverse
    (o : Over (twObjMk f : TwistedArrow C))
    (d : Factorisation f)
    (φ : o ⟶ (factorisationToOverTw f).obj d) :
    (overTwToFactorisation f).obj o ⟶ d where
  h := twCodArr φ.left
  ι_h := adjHomEquivInverse_ι_h f o d φ
  h_π := adjHomEquivInverse_h_π f o d φ

private lemma adjHomEquiv_left_inv
    (o : Over (twObjMk f : TwistedArrow C))
    (d : Factorisation f)
    (g : (overTwToFactorisation f).obj o ⟶ d) :
    adjHomEquivInverse f o d
      (adjHomEquivForward f o d g) = g :=
  Factorisation.Hom.ext rfl

private lemma adjHomEquiv_right_inv
    (o : Over (twObjMk f : TwistedArrow C))
    (d : Factorisation f)
    (φ : o ⟶ (factorisationToOverTw f).obj d) :
    adjHomEquivForward f o d
      (adjHomEquivInverse f o d φ) = φ := by
  apply Over.OverMorphism.ext
  apply twHom_ext
  · change twDomArr o.hom = twDomArr φ.left
    have h := congrArg twDomArr (Over.w φ)
    simp only [twDomArr_comp,
      factorisationToOverTw,
      factorisationToOverTwHom] at h
    exact ((Category.id_comp _).symm.trans h).symm
  · rfl

private def adjHomEquiv
    (o : Over (twObjMk f : TwistedArrow C))
    (d : Factorisation f) :
    ((overTwToFactorisation f).obj o ⟶ d) ≃
      (o ⟶ (factorisationToOverTw f).obj d) where
  toFun := adjHomEquivForward f o d
  invFun := adjHomEquivInverse f o d
  left_inv := adjHomEquiv_left_inv f o d
  right_inv := adjHomEquiv_right_inv f o d

/-- The adjunction between the reflector
`overTwToFactorisation f` and the inclusion
`factorisationToOverTw f`. -/
def overTwFactorisationAdj :
    overTwToFactorisation f ⊣
      factorisationToOverTw f :=
  Adjunction.mkOfHomEquiv
    { homEquiv := adjHomEquiv f
      homEquiv_naturality_right := by
        intro o d d' g h
        apply Over.OverMorphism.ext
        apply twHom_ext
        · change twDomArr o.hom =
            𝟙 X ≫ twDomArr o.hom
          exact (Category.id_comp _).symm
        · rfl }

instance factorisationToOverTw_full :
    (factorisationToOverTw f).Full :=
  (factorisationToOverTw_fullyFaithful f).full

instance factorisationToOverTw_faithful :
    (factorisationToOverTw f).Faithful :=
  (factorisationToOverTw_fullyFaithful f).faithful

/-- The inclusion of `Factorisation f` into
`Over (twObjMk f)` in `TwistedArrow C` is
a reflective functor. The reflector sends a
twisted arrow `g : A → B` over `f` (via
`(α, β)`) to the factorisation
`(B, α ≫ g, β)`. -/
instance factorisationToOverTw_reflective :
    Reflective (factorisationToOverTw f) where
  L := overTwToFactorisation f
  adj := overTwFactorisationAdj f

end FactorisationReflectiveInclusion

/-! ## Decorated factorisation categories

Given `F : TwistedArrow C ⥤ Cat`, for each twisted arrow
`tw`, the decorated factorisation category has objects
`(d : Factorisation (twArr tw), x : F(twObjMk (𝟙 d.mid)))`
and morphisms that carry both a factorisation morphism and a
fiber morphism in `F(twObjMk h.h)`.
-/

@[simp]
lemma Factorisation.Hom_id_h
    {X Y : C} {f : X ⟶ Y} (d : Factorisation f) :
    Factorisation.Hom.h (𝟙 d) = 𝟙 d.mid := rfl

@[simp]
lemma Factorisation.Hom_comp_h
    {X Y : C} {f : X ⟶ Y}
    {d₁ d₂ d₃ : Factorisation f}
    (g : d₁ ⟶ d₂) (h : d₂ ⟶ d₃) :
    (g ≫ h).h = g.h ≫ h.h := rfl

section DecoratedFactorisation

universe w₁ w₂

variable (F : TwistedArrow C ⥤ Cat.{w₁, w₂})

lemma twObjMkFromIdentity_id (A : C) :
    twObjMkFromIdentity (𝟙 A) =
      𝟙 (twObjMk (𝟙 A)) := by
  apply twHom_ext <;> rfl

lemma twObjMkFromIdentityAtCod_id (A : C) :
    twObjMkFromIdentityAtCod (𝟙 A) =
      𝟙 (twObjMk (𝟙 A)) := by
  apply twHom_ext <;> rfl

variable (tw : TwistedArrow C)

/-- An object of the decorated factorisation category
for a twisted arrow `tw` and functor `F : TwistedArrow C ⥤ Cat`.
Consists of a factorisation of `twArr tw` and an object of
the fiber category `F(twObjMk (𝟙 d.mid))`. -/
@[ext]
structure DecFactObj where
  /-- The underlying factorisation. -/
  fact : Factorisation (twArr tw)
  /-- An object in the fiber category over the identity
  at the midpoint. -/
  fiber : F.obj (twObjMk (𝟙 fact.mid))

/-- A morphism in the decorated factorisation category from
`x` to `y`. Consists of a factorisation morphism `factHom`
and a fiber morphism in `F(twObjMk factHom.h)` from
the right-transport of `x.fiber` to the left-transport
of `y.fiber`. -/
structure DecFactHom
    (x y : DecFactObj F tw) where
  /-- The underlying factorisation morphism. -/
  factHom : x.fact ⟶ y.fact
  /-- The fiber morphism in `F(twObjMk factHom.h)`. The
  source is `x.fiber` transported along the codomain
  direction via `twObjMkFromIdentity factHom.h`. The
  target is `y.fiber` transported along the domain
  direction via `twObjMkFromIdentityAtCod factHom.h`. -/
  fiberMorph :
    (F.map (twObjMkFromIdentity factHom.h)
      ).toFunctor.obj x.fiber ⟶
    (F.map (twObjMkFromIdentityAtCod factHom.h)
      ).toFunctor.obj y.fiber

private lemma decFactId_fiber_eq
    (x : DecFactObj F tw) :
    (F.map (twObjMkFromIdentity
        (Factorisation.Hom.h (𝟙 x.fact)))
      ).toFunctor.obj x.fiber =
    (F.map (twObjMkFromIdentityAtCod
        (Factorisation.Hom.h (𝟙 x.fact)))
      ).toFunctor.obj x.fiber := by
  change (F.map (twObjMkFromIdentity (𝟙 x.fact.mid))
    ).toFunctor.obj x.fiber =
    (F.map (twObjMkFromIdentityAtCod (𝟙 x.fact.mid))
      ).toFunctor.obj x.fiber
  rw [twObjMkFromIdentity_id,
    twObjMkFromIdentityAtCod_id]

/-- The identity morphism in the decorated factorisation
category. -/
def decFactId (x : DecFactObj F tw) :
    DecFactHom F tw x x where
  factHom := 𝟙 x.fact
  fiberMorph := eqToHom (decFactId_fiber_eq F tw x)

/-- Extension morphism on the codomain: given
`g : A ⟶ B` and `g' : B ⟶ C`, produces a twisted arrow
morphism `twObjMk g ⟶ twObjMk (g ≫ g')` via `(𝟙, g')`. -/
def twExtendCod {A B E : C}
    (g : A ⟶ B) (g' : B ⟶ E) :
    twObjMk g ⟶ twObjMk (g ≫ g') :=
  twHomMk (𝟙 A) g' (by
    simp only [twObjMk_arr]
    exact Category.id_comp _)

/-- Extension morphism on the domain: given
`g : A ⟶ B` and `g' : B ⟶ E`, produces a twisted arrow
morphism `twObjMk g' ⟶ twObjMk (g ≫ g')` via `(g, 𝟙)`. -/
def twExtendDom {A B E : C}
    (g : A ⟶ B) (g' : B ⟶ E) :
    twObjMk g' ⟶ twObjMk (g ≫ g') :=
  twHomMk (x := twObjMk g') (y := twObjMk (g ≫ g'))
    g (𝟙 E) (by
    change g ≫ g' ≫ 𝟙 E = g ≫ g'
    rw [Category.comp_id])

@[simp]
lemma twExtendCod_domArr {A B E : C}
    (g : A ⟶ B) (g' : B ⟶ E) :
    twDomArr (twExtendCod g g') = 𝟙 A := rfl

@[simp]
lemma twExtendCod_codArr {A B E : C}
    (g : A ⟶ B) (g' : B ⟶ E) :
    twCodArr (twExtendCod g g') = g' := rfl

@[simp]
lemma twExtendDom_domArr {A B E : C}
    (g : A ⟶ B) (g' : B ⟶ E) :
    twDomArr (twExtendDom g g') = g := rfl

@[simp]
lemma twExtendDom_codArr {A B E : C}
    (g : A ⟶ B) (g' : B ⟶ E) :
    twCodArr (twExtendDom g g') = 𝟙 E := rfl

lemma twObjMkFromIdentity_comp {A B E : C}
    (g : A ⟶ B) (g' : B ⟶ E) :
    twObjMkFromIdentity (g ≫ g') =
      twObjMkFromIdentity g ≫
        twExtendCod g g' := by
  apply twHom_ext
  · simp only [twObjMkFromIdentity_domArr,
      twDomArr_comp, twExtendCod_domArr]
    exact (Category.comp_id _).symm
  · rfl

lemma twObjMkFromIdentityAtCod_comp {A B E : C}
    (g : A ⟶ B) (g' : B ⟶ E) :
    twObjMkFromIdentityAtCod (g ≫ g') =
      twObjMkFromIdentityAtCod g' ≫
        twExtendDom g g' := by
  apply twHom_ext
  · change g ≫ g' =
      twDomArr (twExtendDom g g') ≫
        twDomArr (twObjMkFromIdentityAtCod g')
    simp
  · change 𝟙 E =
      twCodArr (twObjMkFromIdentityAtCod g') ≫
        twCodArr (twExtendDom g g')
    simp only [twObjMkFromIdentityAtCod_codArr,
      twExtendDom_codArr]
    exact (Category.comp_id _).symm

lemma twMidPaths_eq {A B E : C}
    (g : A ⟶ B) (g' : B ⟶ E) :
    twObjMkFromIdentityAtCod g ≫
      twExtendCod g g' =
    twObjMkFromIdentity g' ≫
      twExtendDom g g' := by
  apply twHom_ext
  · change 𝟙 A ≫ g = g ≫ 𝟙 B
    rw [Category.id_comp, Category.comp_id]
  · change 𝟙 B ≫ g' = g' ≫ 𝟙 E
    rw [Category.id_comp, Category.comp_id]

/-- The source transport for composition: the equality
arising from factoring `twObjMkFromIdentity (g ≫ g')`
into `twObjMkFromIdentity g ≫ twExtendCod g g'`. -/
private lemma decFactComp_src_eq {A B E : C}
    (g : A ⟶ B) (g' : B ⟶ E)
    (x : F.obj (twObjMk (𝟙 A))) :
    (F.map (twObjMkFromIdentity (g ≫ g'))
      ).toFunctor.obj x =
    (F.map (twExtendCod g g')).toFunctor.obj
      ((F.map (twObjMkFromIdentity g)
        ).toFunctor.obj x) := by
  rw [twObjMkFromIdentity_comp,
    Functor.map_comp, Cat.Hom.comp_toFunctor,
    Functor.comp_obj]

/-- The middle transport: the equality between
the codomain-extended target of `fM` and the
domain-extended source of `fM'`. -/
private lemma decFactComp_mid_eq {A B E : C}
    (g : A ⟶ B) (g' : B ⟶ E)
    (y : F.obj (twObjMk (𝟙 B))) :
    (F.map (twExtendCod g g')).toFunctor.obj
      ((F.map (twObjMkFromIdentityAtCod g)
        ).toFunctor.obj y) =
    (F.map (twExtendDom g g')).toFunctor.obj
      ((F.map (twObjMkFromIdentity g')
        ).toFunctor.obj y) := by
  rw [← Functor.comp_obj, ← Cat.Hom.comp_toFunctor,
    ← Functor.map_comp, twMidPaths_eq,
    Functor.map_comp, Cat.Hom.comp_toFunctor,
    Functor.comp_obj]

/-- The target transport for composition: the equality
arising from factoring `twObjMkFromIdentityAtCod (g ≫ g')`
into `twObjMkFromIdentityAtCod g' ≫ twExtendDom g g'`. -/
private lemma decFactComp_tgt_eq {A B E : C}
    (g : A ⟶ B) (g' : B ⟶ E)
    (z : F.obj (twObjMk (𝟙 E))) :
    (F.map (twObjMkFromIdentityAtCod (g ≫ g'))
      ).toFunctor.obj z =
    (F.map (twExtendDom g g')).toFunctor.obj
      ((F.map (twObjMkFromIdentityAtCod g')
        ).toFunctor.obj z) := by
  rw [twObjMkFromIdentityAtCod_comp,
    Functor.map_comp, Cat.Hom.comp_toFunctor,
    Functor.comp_obj]

/-- Composition in the decorated factorisation category.
Given `m : x ⟶ y` and `n : y ⟶ z`, the composite fiber
morphism is obtained by transporting `m.fiberMorph` and
`n.fiberMorph` to `F(twObjMk (m.factHom.h ≫ n.factHom.h))`
via the codomain and domain extension morphisms, with a
middle `eqToHom` connecting them. -/
def decFactComp
    {x y z : DecFactObj F tw}
    (m : DecFactHom F tw x y)
    (n : DecFactHom F tw y z) :
    DecFactHom F tw x z where
  factHom := m.factHom ≫ n.factHom
  fiberMorph :=
    eqToHom (decFactComp_src_eq F
      m.factHom.h n.factHom.h x.fiber) ≫
    (F.map (twExtendCod m.factHom.h n.factHom.h)
      ).toFunctor.map m.fiberMorph ≫
    eqToHom (decFactComp_mid_eq F
      m.factHom.h n.factHom.h y.fiber) ≫
    (F.map (twExtendDom m.factHom.h n.factHom.h)
      ).toFunctor.map n.fiberMorph ≫
    eqToHom (decFactComp_tgt_eq F
      m.factHom.h n.factHom.h z.fiber).symm

instance : CategoryStruct (DecFactObj F tw) where
  Hom := DecFactHom F tw
  id := decFactId F tw
  comp := decFactComp F tw

/-- When the first argument is identity,
`twExtendDom (𝟙 A) g` equals `eqToHom` for the equality
`twObjMk g = twObjMk (𝟙 A ≫ g)`. -/
lemma twExtendDom_id_left {A B : C} (g : A ⟶ B) :
    twExtendDom (𝟙 A) g =
      eqToHom (congrArg twObjMk
        (Category.id_comp g).symm) := by
  apply twHom_ext
  · simp only [twExtendDom_domArr, twDomArr_eqToHom]
    rfl
  · simp only [twExtendDom_codArr, twCodArr_eqToHom]
    rfl

/-- When the second argument is identity,
`twExtendCod g (𝟙 B)` equals `eqToHom` for the equality
`twObjMk g = twObjMk (g ≫ 𝟙 B)`. -/
lemma twExtendCod_id_right {A B : C} (g : A ⟶ B) :
    twExtendCod g (𝟙 B) =
      eqToHom (congrArg twObjMk
        (Category.comp_id g).symm) := by
  apply twHom_ext
  · simp only [twExtendCod_domArr, twDomArr_eqToHom]
    rfl
  · simp only [twExtendCod_codArr, twCodArr_eqToHom]
    rfl

/-- Extensionality for `DecFactHom`: two morphisms are
equal if their factorisation morphisms are equal and their
fiber morphisms are HEq. -/
theorem decFactHom_ext {x y : DecFactObj F tw}
    {m n : DecFactHom F tw x y}
    (hFact : m.factHom = n.factHom)
    (hFiber : HEq m.fiberMorph n.fiberMorph) :
    m = n := by
  rcases m with ⟨mf, mm⟩
  rcases n with ⟨nf, nm⟩
  obtain rfl := hFact
  congr 1
  exact eq_of_heq hFiber

private lemma twObjMkFromIdentity_eqToHom
    {A B : C} {g g' : A ⟶ B} (p : g = g') :
    twObjMkFromIdentity g ≫
      eqToHom (congrArg twObjMk p) =
    twObjMkFromIdentity g' := by
  subst p; simp

private lemma twObjMkFromIdentityAtCod_eqToHom
    {A B : C} {g g' : A ⟶ B} (p : g = g') :
    twObjMkFromIdentityAtCod g ≫
      eqToHom (congrArg twObjMk p) =
    twObjMkFromIdentityAtCod g' := by
  subst p; simp

/-- Transport of a source object through an eqToHom
functor: for `p : g = g'`, transporting
`F.map(twObjMkFromIdentity g).obj a` through
`eqToHom(congrArg F.obj (congrArg twObjMk p))`
gives `F.map(twObjMkFromIdentity g').obj a`. -/
private lemma eqToHom_obj_twObjMkFromIdentity
    {A B : C} {g g' : A ⟶ B} (p : g = g')
    (a : F.obj (twObjMk (𝟙 A))) :
    (eqToHom (congrArg F.obj
        (congrArg twObjMk p))).toFunctor.obj
      ((F.map (twObjMkFromIdentity g)
        ).toFunctor.obj a) =
    (F.map (twObjMkFromIdentity g')
      ).toFunctor.obj a := by
  subst p; simp [eqToHom_refl,
    Cat.Hom.id_toFunctor]

/-- Transport of a target object through an eqToHom
functor: for `p : g = g'`, transporting
`F.map(twObjMkFromIdentityAtCod g).obj a` through
`eqToHom(congrArg F.obj (congrArg twObjMk p))`
gives `F.map(twObjMkFromIdentityAtCod g').obj a`. -/
private lemma eqToHom_obj_twObjMkFromIdentityAtCod
    {A B : C} {g g' : A ⟶ B} (p : g = g')
    (a : F.obj (twObjMk (𝟙 B))) :
    (eqToHom (congrArg F.obj
        (congrArg twObjMk p))).toFunctor.obj
      ((F.map (twObjMkFromIdentityAtCod g)
        ).toFunctor.obj a) =
    (F.map (twObjMkFromIdentityAtCod g')
      ).toFunctor.obj a := by
  subst p; simp [eqToHom_refl,
    Cat.Hom.id_toFunctor]

lemma twExtendCod_comp {A B E D : C}
    (a : A ⟶ B) (b : B ⟶ E) (c : E ⟶ D) :
    twExtendCod a b ≫ twExtendCod (a ≫ b) c =
    twExtendCod a (b ≫ c) ≫
      eqToHom (congrArg twObjMk
        (Category.assoc a b c).symm) := by
  apply twHom_ext
  · rw [twDomArr_comp, twDomArr_comp,
      twExtendCod_domArr, twExtendCod_domArr,
      twExtendCod_domArr, twDomArr_eqToHom,
      eqToHom_refl]
    simp only [twObjMk_dom, Category.comp_id]
  · rw [twCodArr_comp, twCodArr_comp,
      twExtendCod_codArr, twExtendCod_codArr,
      twExtendCod_codArr, twCodArr_eqToHom,
      eqToHom_refl]
    simp only [twObjMk_cod, Category.comp_id]

lemma twExtendDom_comp {A B E D : C}
    (a : A ⟶ B) (b : B ⟶ E) (c : E ⟶ D) :
    twExtendDom b c ≫ twExtendDom a (b ≫ c) =
    twExtendDom (a ≫ b) c ≫
      eqToHom (congrArg twObjMk
        (Category.assoc a b c)) := by
  apply twHom_ext
  · rw [twDomArr_comp, twDomArr_comp,
      twExtendDom_domArr, twExtendDom_domArr,
      twExtendDom_domArr, twDomArr_eqToHom,
      eqToHom_refl]
    simp only [twObjMk_dom, Category.id_comp]
  · rw [twCodArr_comp, twCodArr_comp,
      twExtendDom_codArr, twExtendDom_codArr,
      twExtendDom_codArr, twCodArr_eqToHom,
      eqToHom_refl]
    simp only [twObjMk_cod, Category.comp_id]

lemma twExtend_interchange {A B E D : C}
    (a : A ⟶ B) (b : B ⟶ E) (c : E ⟶ D) :
    twExtendDom a b ≫ twExtendCod (a ≫ b) c =
    twExtendCod b c ≫ twExtendDom a (b ≫ c) ≫
      eqToHom (congrArg twObjMk
        (Category.assoc a b c).symm) := by
  apply twHom_ext
  · rw [twDomArr_comp, twDomArr_comp,
      twDomArr_comp, twExtendCod_domArr,
      twExtendDom_domArr, twExtendDom_domArr,
      twExtendCod_domArr, twDomArr_eqToHom,
      eqToHom_refl]
    simp only [twObjMk_dom,
      Category.id_comp, Category.comp_id]
  · rw [twCodArr_comp, twCodArr_comp,
      twCodArr_comp, twExtendDom_codArr,
      twExtendCod_codArr, twExtendCod_codArr,
      twExtendDom_codArr, twCodArr_eqToHom,
      eqToHom_refl]
    simp only [twObjMk_cod,
      Category.id_comp, Category.comp_id]

private lemma twExtendCod_comp_eqToHom
    {A B E D : C}
    (a : A ⟶ B) (b : B ⟶ E) (c : E ⟶ D) :
    twExtendCod a b ≫ twExtendCod (a ≫ b) c ≫
      eqToHom (congrArg twObjMk
        (Category.assoc a b c)) =
    twExtendCod a (b ≫ c) := by
  apply twHom_ext
  · rw [twDomArr_comp, twDomArr_comp, twExtendCod_domArr,
      twExtendCod_domArr, twExtendCod_domArr, twDomArr_eqToHom,
      eqToHom_refl]
    simp only [twObjMk_dom, Category.comp_id]
  · rw [twCodArr_comp, twCodArr_comp, twExtendCod_codArr,
      twExtendCod_codArr, twExtendCod_codArr, twCodArr_eqToHom,
      eqToHom_refl]
    simp only [twObjMk_cod, Category.comp_id]

private lemma twExtend_interchange_eqToHom
    {A B E D : C}
    (a : A ⟶ B) (b : B ⟶ E) (c : E ⟶ D) :
    twExtendDom a b ≫ twExtendCod (a ≫ b) c ≫
      eqToHom (congrArg twObjMk
        (Category.assoc a b c)) =
    twExtendCod b c ≫ twExtendDom a (b ≫ c) := by
  apply twHom_ext
  · rw [twDomArr_comp, twDomArr_comp, twExtendDom_domArr,
      twExtendCod_domArr, twDomArr_eqToHom, eqToHom_refl,
      twDomArr_comp, twExtendDom_domArr, twExtendCod_domArr]
    simp only [twObjMk_dom, Category.comp_id, Category.id_comp]
  · rw [twCodArr_comp, twCodArr_comp, twExtendDom_codArr,
      twExtendCod_codArr, twCodArr_eqToHom, eqToHom_refl,
      twCodArr_comp, twExtendDom_codArr, twExtendCod_codArr]
    simp only [twObjMk_cod, Category.comp_id, Category.id_comp]

private lemma twExtendDom_comp_eqToHom
    {A B E D : C}
    (a : A ⟶ B) (b : B ⟶ E) (c : E ⟶ D) :
    twExtendDom (a ≫ b) c ≫
      eqToHom (congrArg twObjMk
        (Category.assoc a b c)) =
    twExtendDom b c ≫ twExtendDom a (b ≫ c) :=
  (twExtendDom_comp a b c).symm

/-- Functor-level version of twExtendCod_comp_eqToHom. -/
private lemma Fmap_twExtendCod_comp_eqToHom
    {A B E D : C}
    (a : A ⟶ B) (b : B ⟶ E) (c : E ⟶ D) :
    F.map (twExtendCod a b) ≫ F.map (twExtendCod (a ≫ b) c) ≫
      eqToHom (congrArg F.obj (congrArg twObjMk
        (Category.assoc a b c))) =
    F.map (twExtendCod a (b ≫ c)) := by
  conv_lhs => rw [← eqToHom_map F (congrArg twObjMk
        (Category.assoc a b c))]
  rw [← Functor.map_comp, ← Functor.map_comp,
    twExtendCod_comp_eqToHom]

/-- Functor-level version of twExtend_interchange_eqToHom. -/
private lemma Fmap_twExtend_interchange_eqToHom
    {A B E D : C}
    (a : A ⟶ B) (b : B ⟶ E) (c : E ⟶ D) :
    F.map (twExtendDom a b) ≫ F.map (twExtendCod (a ≫ b) c) ≫
      eqToHom (congrArg F.obj (congrArg twObjMk
        (Category.assoc a b c))) =
    F.map (twExtendCod b c) ≫ F.map (twExtendDom a (b ≫ c)) := by
  conv_lhs => rw [← eqToHom_map F (congrArg twObjMk
        (Category.assoc a b c))]
  rw [← Functor.map_comp, ← Functor.map_comp,
    twExtend_interchange_eqToHom, Functor.map_comp]

/-- Functor-level version of twExtendDom_comp_eqToHom. -/
private lemma Fmap_twExtendDom_comp_eqToHom
    {A B E D : C}
    (a : A ⟶ B) (b : B ⟶ E) (c : E ⟶ D) :
    F.map (twExtendDom (a ≫ b) c) ≫
      eqToHom (congrArg F.obj (congrArg twObjMk
        (Category.assoc a b c))) =
    F.map (twExtendDom b c) ≫ F.map (twExtendDom a (b ≫ c)) := by
  conv_lhs => rw [← eqToHom_map F (congrArg twObjMk
        (Category.assoc a b c))]
  rw [← Functor.map_comp, twExtendDom_comp_eqToHom,
    Functor.map_comp]

/-- When two morphisms in Cat are equal, their functor maps are HEq. -/
private lemma Cat_hom_map_heq {X Y : Cat} {G H : X ⟶ Y}
    (h : G = H) {A B : X} (f : A ⟶ B) :
    HEq (G.toFunctor.map f) (H.toFunctor.map f) := by
  subst h
  rfl

/-- The fM component transforms correctly under associativity:
`(twExtendCod (a≫b) c) ∘ (twExtendCod a b)` relates to `twExtendCod a (b≫c)`.
Both sides are HEq since the types differ by `Category.assoc`. -/
private lemma assoc_fM_transform
    {A B E D : C}
    (a : A ⟶ B) (b : B ⟶ E) (c : E ⟶ D)
    {src tgt : F.obj (twObjMk a)}
    (fM : src ⟶ tgt) :
    (F.map (twExtendCod (a ≫ b) c)).toFunctor.map
      ((F.map (twExtendCod a b)).toFunctor.map fM) ≍
    (eqToHom (congrArg F.obj (congrArg twObjMk
        (Category.assoc a b c)).symm)).toFunctor.map
      ((F.map (twExtendCod a (b ≫ c))).toFunctor.map fM) := by
  have h := Fmap_twExtendCod_comp_eqToHom F a b c
  have h' : F.map (twExtendCod a b) ≫ F.map (twExtendCod (a ≫ b) c) =
      F.map (twExtendCod a (b ≫ c)) ≫ eqToHom (congrArg F.obj
        (congrArg twObjMk (Category.assoc a b c))).symm := by
    rw [← h]
    simp only [Category.assoc, eqToHom_trans, eqToHom_refl,
      Category.comp_id]
  -- Step 1: LHS = composition.toFunctor.map fM
  have step1 : (F.map (twExtendCod (a ≫ b) c)).toFunctor.map
        ((F.map (twExtendCod a b)).toFunctor.map fM) =
      (F.map (twExtendCod a b) ≫ F.map (twExtendCod (a ≫ b) c)
        ).toFunctor.map fM := by
    simp only [Cat.Hom.comp_toFunctor, Functor.comp_map]
  -- Step 2: RHS = (composition with eqToHom).toFunctor.map fM
  have step2 : (eqToHom (congrArg F.obj (congrArg twObjMk
        (Category.assoc a b c)).symm)).toFunctor.map
      ((F.map (twExtendCod a (b ≫ c))).toFunctor.map fM) =
    (F.map (twExtendCod a (b ≫ c)) ≫ eqToHom (congrArg F.obj
        (congrArg twObjMk (Category.assoc a b c))).symm).toFunctor.map fM := by
    simp only [Cat.Hom.comp_toFunctor, Functor.comp_map]
  rw [step1, step2]
  -- Now both sides have the same structure: (morphism).toFunctor.map fM
  -- The morphisms in Cat are equal by h', so the maps are HEq
  exact Cat_hom_map_heq h' fM

/-- The gM component transforms correctly under associativity using interchange. -/
private lemma assoc_gM_transform
    {A B E D : C}
    (a : A ⟶ B) (b : B ⟶ E) (c : E ⟶ D)
    {src tgt : F.obj (twObjMk b)}
    (gM : src ⟶ tgt) :
    (F.map (twExtendCod (a ≫ b) c)).toFunctor.map
      ((F.map (twExtendDom a b)).toFunctor.map gM) ≍
    (eqToHom (congrArg F.obj (congrArg twObjMk
        (Category.assoc a b c)).symm)).toFunctor.map
      ((F.map (twExtendDom a (b ≫ c))).toFunctor.map
        ((F.map (twExtendCod b c)).toFunctor.map gM)) := by
  have h := Fmap_twExtend_interchange_eqToHom F a b c
  -- h says: LHS ≫ eqToHom = RHS, so LHS = RHS ≫ eqToHom.symm
  have h' : F.map (twExtendDom a b) ≫ F.map (twExtendCod (a ≫ b) c) =
      F.map (twExtendCod b c) ≫ F.map (twExtendDom a (b ≫ c)) ≫
        eqToHom (congrArg F.obj (congrArg twObjMk
          (Category.assoc a b c))).symm := by
    have step := congrArg (· ≫ eqToHom (congrArg F.obj (congrArg twObjMk
        (Category.assoc a b c))).symm) h
    simp only [Category.assoc, eqToHom_trans, eqToHom_refl,
      Category.comp_id] at step
    exact step
  have step1 : (F.map (twExtendCod (a ≫ b) c)).toFunctor.map
        ((F.map (twExtendDom a b)).toFunctor.map gM) =
      (F.map (twExtendDom a b) ≫ F.map (twExtendCod (a ≫ b) c)
        ).toFunctor.map gM := by
    simp only [Cat.Hom.comp_toFunctor, Functor.comp_map]
  have step2 : (eqToHom (congrArg F.obj (congrArg twObjMk
        (Category.assoc a b c)).symm)).toFunctor.map
      ((F.map (twExtendDom a (b ≫ c))).toFunctor.map
        ((F.map (twExtendCod b c)).toFunctor.map gM)) =
    (F.map (twExtendCod b c) ≫ F.map (twExtendDom a (b ≫ c)) ≫
      eqToHom (congrArg F.obj (congrArg twObjMk
        (Category.assoc a b c))).symm).toFunctor.map gM := by
    simp only [Cat.Hom.comp_toFunctor, Functor.comp_map]
  rw [step1, step2]
  exact Cat_hom_map_heq h' gM

/-- The hM component transforms correctly under associativity using twExtendDom_comp. -/
private lemma assoc_hM_transform
    {A B E D : C}
    (a : A ⟶ B) (b : B ⟶ E) (c : E ⟶ D)
    {src tgt : F.obj (twObjMk c)}
    (hM : src ⟶ tgt) :
    (F.map (twExtendDom (a ≫ b) c)).toFunctor.map hM ≍
    (eqToHom (congrArg F.obj (congrArg twObjMk
        (Category.assoc a b c)).symm)).toFunctor.map
      ((F.map (twExtendDom a (b ≫ c))).toFunctor.map
        ((F.map (twExtendDom b c)).toFunctor.map hM)) := by
  have h := Fmap_twExtendDom_comp_eqToHom F a b c
  -- h says: LHS ≫ eqToHom = RHS, so LHS = RHS ≫ eqToHom.symm
  have h' : F.map (twExtendDom (a ≫ b) c) =
      F.map (twExtendDom b c) ≫ F.map (twExtendDom a (b ≫ c)) ≫
        eqToHom (congrArg F.obj (congrArg twObjMk
          (Category.assoc a b c))).symm := by
    have step := congrArg (· ≫ eqToHom (congrArg F.obj (congrArg twObjMk
        (Category.assoc a b c))).symm) h
    simp only [Category.assoc, eqToHom_trans, eqToHom_refl,
      Category.comp_id] at step
    exact step
  have step2 : (eqToHom (congrArg F.obj (congrArg twObjMk
        (Category.assoc a b c)).symm)).toFunctor.map
      ((F.map (twExtendDom a (b ≫ c))).toFunctor.map
        ((F.map (twExtendDom b c)).toFunctor.map hM)) =
    (F.map (twExtendDom b c) ≫ F.map (twExtendDom a (b ≫ c)) ≫
      eqToHom (congrArg F.obj (congrArg twObjMk
        (Category.assoc a b c))).symm).toFunctor.map hM := by
    simp only [Cat.Hom.comp_toFunctor, Functor.comp_map]
  rw [step2]
  exact Cat_hom_map_heq h' hM

private theorem decFact_id_comp
    {x y : DecFactObj F tw}
    (f : DecFactHom F tw x y) :
    decFactComp F tw (decFactId F tw x) f = f := by
  rcases f with ⟨factHom, fiberMorph⟩
  simp only [decFactComp, decFactId]
  congr 1
  · exact Category.id_comp factHom
  · apply HEq.trans (eqToHom_comp_heq _ _)
    conv_lhs => rw [eqToHom_map]
    apply HEq.trans (eqToHom_comp_heq _ _)
    apply HEq.trans (eqToHom_comp_heq _ _)
    apply HEq.trans (comp_eqToHom_heq _ _)
    change (F.map (twExtendDom (𝟙 x.fact.mid)
        factHom.h)).toFunctor.map fiberMorph ≍
      fiberMorph
    rw [twExtendDom_id_left, eqToHom_map]
    exact Cat.eqToHom_map_heq _ _

private theorem decFact_comp_id
    {x y : DecFactObj F tw}
    (f : DecFactHom F tw x y) :
    decFactComp F tw f (decFactId F tw y) = f := by
  rcases f with ⟨factHom, fiberMorph⟩
  simp only [decFactComp, decFactId]
  congr 1
  · exact Category.comp_id factHom
  · apply HEq.trans (eqToHom_comp_heq _ _)
    conv_lhs =>
      rw [eqToHom_map, eqToHom_trans, eqToHom_trans]
    apply HEq.trans (comp_eqToHom_heq _ _)
    change (F.map (twExtendCod factHom.h
        (𝟙 y.fact.mid))
      ).toFunctor.map fiberMorph ≍ fiberMorph
    rw [twExtendCod_id_right, eqToHom_map]
    exact Cat.eqToHom_map_heq _ _

/-- Step 1: After simp, LHS transforms to this form (with eqToHom at start/end). -/
private lemma decFact_comp_assoc_fiber_lhs_simp
    {W X Y Z : DecFactObj F tw}
    (fH : W.fact ⟶ X.fact) (gH : X.fact ⟶ Y.fact) (hH : Y.fact ⟶ Z.fact)
    (fM : (F.map (twObjMkFromIdentity fH.h)).toFunctor.obj W.fiber ⟶
          (F.map (twObjMkFromIdentityAtCod fH.h)).toFunctor.obj X.fiber)
    (gM : (F.map (twObjMkFromIdentity gH.h)).toFunctor.obj X.fiber ⟶
          (F.map (twObjMkFromIdentityAtCod gH.h)).toFunctor.obj Y.fiber)
    (hM : (F.map (twObjMkFromIdentity hH.h)).toFunctor.obj Y.fiber ⟶
          (F.map (twObjMkFromIdentityAtCod hH.h)).toFunctor.obj Z.fiber) :
    (decFactComp F tw (decFactComp F tw ⟨fH, fM⟩ ⟨gH, gM⟩) ⟨hH, hM⟩).fiberMorph ≍
      (decFactComp F tw (decFactComp F tw ⟨fH, fM⟩ ⟨gH, gM⟩) ⟨hH, hM⟩).fiberMorph :=
  HEq.refl _

/-- Step 2: After simp, RHS transforms to this form (with eqToHom at start/end). -/
private lemma decFact_comp_assoc_fiber_rhs_simp
    {W X Y Z : DecFactObj F tw}
    (fH : W.fact ⟶ X.fact) (gH : X.fact ⟶ Y.fact) (hH : Y.fact ⟶ Z.fact)
    (fM : (F.map (twObjMkFromIdentity fH.h)).toFunctor.obj W.fiber ⟶
          (F.map (twObjMkFromIdentityAtCod fH.h)).toFunctor.obj X.fiber)
    (gM : (F.map (twObjMkFromIdentity gH.h)).toFunctor.obj X.fiber ⟶
          (F.map (twObjMkFromIdentityAtCod gH.h)).toFunctor.obj Y.fiber)
    (hM : (F.map (twObjMkFromIdentity hH.h)).toFunctor.obj Y.fiber ⟶
          (F.map (twObjMkFromIdentityAtCod hH.h)).toFunctor.obj Z.fiber) :
    (decFactComp F tw ⟨fH, fM⟩ (decFactComp F tw ⟨gH, gM⟩ ⟨hH, hM⟩)).fiberMorph ≍
      (decFactComp F tw ⟨fH, fM⟩ (decFactComp F tw ⟨gH, gM⟩ ⟨hH, hM⟩)).fiberMorph :=
  HEq.refl _

/--
HEq of compositions when categories are equal and objects match.
Given equal categories, object equalities, and piece-wise morphism HEq,
derives full composition HEq.
-/
private lemma heq_comp6_eq_cats
    {C D : Cat}
    (hCD : C = D)
    {X1 X2 X3 X4 X5 X6 X7 : ↥C}
    {Y1 Y2 Y3 Y4 Y5 Y6 Y7 : ↥D}
    {a1 : X1 ⟶ X2} {e1 : X2 ⟶ X3} {a2 : X3 ⟶ X4} {e2 : X4 ⟶ X5}
    {a3 : X5 ⟶ X6} {e3 : X6 ⟶ X7}
    {b1 : Y1 ⟶ Y2} {f1 : Y2 ⟶ Y3} {b2 : Y3 ⟶ Y4} {f2 : Y4 ⟶ Y5}
    {b3 : Y5 ⟶ Y6} {f3 : Y6 ⟶ Y7}
    (hX1 : X1 ≍ Y1) (hX2 : X2 ≍ Y2) (hX3 : X3 ≍ Y3) (hX4 : X4 ≍ Y4)
    (hX5 : X5 ≍ Y5) (hX6 : X6 ≍ Y6) (hX7 : X7 ≍ Y7)
    (ha1 : a1 ≍ b1) (he1 : e1 ≍ f1) (ha2 : a2 ≍ b2)
    (he2 : e2 ≍ f2) (ha3 : a3 ≍ b3) (he3 : e3 ≍ f3) :
    a1 ≫ e1 ≫ a2 ≫ e2 ≫ a3 ≫ e3 ≍ b1 ≫ f1 ≫ b2 ≫ f2 ≫ b3 ≫ f3 := by
  subst hCD
  have eqX1 : X1 = Y1 := eq_of_heq hX1
  have eqX2 : X2 = Y2 := eq_of_heq hX2
  have eqX3 : X3 = Y3 := eq_of_heq hX3
  have eqX4 : X4 = Y4 := eq_of_heq hX4
  have eqX5 : X5 = Y5 := eq_of_heq hX5
  have eqX6 : X6 = Y6 := eq_of_heq hX6
  have eqX7 : X7 = Y7 := eq_of_heq hX7
  subst eqX1 eqX2 eqX3 eqX4 eqX5 eqX6 eqX7
  simp only [eq_of_heq ha1, eq_of_heq he1, eq_of_heq ha2,
    eq_of_heq he2, eq_of_heq ha3, eq_of_heq he3]
  exact HEq.refl _

/--
eqToHom terms with same source and target types are HEq (proof irrelevance).
-/
private lemma assoc_fiber_eqToHom_heq
    {C : Type*} [Category C] {X Y X' Y' : C}
    (p : X = Y) (q : X' = Y')
    (hX : X = X') (hY : Y = Y') :
    eqToHom p ≍ eqToHom q := by
  subst hX hY
  cases p
  cases q
  rfl

/--
Object HEq for hA1B1/hA2B2: the twExtendCod composition.
-/
private lemma assoc_obj_heq_extendCod
    {A B E D : C}
    (a : A ⟶ B) (b : B ⟶ E) (c : E ⟶ D)
    (X : F.obj (twObjMk a)) :
    (F.map (twExtendCod (a ≫ b) c)).toFunctor.obj
      ((F.map (twExtendCod a b)).toFunctor.obj X) ≍
    (F.map (twExtendCod a (b ≫ c))).toFunctor.obj X := by
  -- From Fmap_twExtendCod_comp_eqToHom: G ≫ H ≫ eqToHom η = K
  -- Rearrange to: G ≫ H = K ≫ eqToHom η.symm
  have hEq := Fmap_twExtendCod_comp_eqToHom F a b c
  let η := congrArg F.obj (congrArg twObjMk (Category.assoc a b c))
  have hEq' : F.map (twExtendCod a b) ≫ F.map (twExtendCod (a ≫ b) c) =
      F.map (twExtendCod a (b ≫ c)) ≫ eqToHom η.symm := by
    rw [← hEq]
    simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  -- LHS = (G ≫ H).toFunctor.obj X
  have step1 : (F.map (twExtendCod (a ≫ b) c)).toFunctor.obj
      ((F.map (twExtendCod a b)).toFunctor.obj X) =
    (F.map (twExtendCod a b) ≫ F.map (twExtendCod (a ≫ b) c)).toFunctor.obj X := by
    simp only [Cat.Hom.comp_toFunctor, Functor.comp_obj]
  -- After substitution: = (K ≫ eqToHom η.symm).toFunctor.obj X
  rw [step1, hEq']
  simp only [Cat.Hom.comp_toFunctor, Functor.comp_obj]
  -- Now need: (eqToHom η.symm).toFunctor.obj Y ≍ Y
  exact eqToHom_obj_heq _ _ η.symm _

/--
Object HEq for hA4B4: the interchange case.
-/
private lemma assoc_obj_heq_interchange
    {A B E D : C}
    (a : A ⟶ B) (b : B ⟶ E) (c : E ⟶ D)
    (X : F.obj (twObjMk b)) :
    (F.map (twExtendCod (a ≫ b) c)).toFunctor.obj
      ((F.map (twExtendDom a b)).toFunctor.obj X) ≍
    (F.map (twExtendDom a (b ≫ c))).toFunctor.obj
      ((F.map (twExtendCod b c)).toFunctor.obj X) := by
  -- From Fmap_twExtend_interchange_eqToHom:
  -- LHS_comp ≫ eqToHom η = RHS_comp
  have hEq := Fmap_twExtend_interchange_eqToHom F a b c
  let η := congrArg F.obj (congrArg twObjMk (Category.assoc a b c))
  -- From hEq: (eqToHom η).toFunctor.obj (LHS.obj X) = RHS.obj X
  have step3 : (F.map (twExtendDom a b) ≫ F.map (twExtendCod (a ≫ b) c) ≫
      eqToHom η).toFunctor.obj X =
    (F.map (twExtendCod b c) ≫ F.map (twExtendDom a (b ≫ c))).toFunctor.obj X := by
    rw [hEq]
  simp only [Cat.Hom.comp_toFunctor, Functor.comp_obj] at step3
  -- step3: (eqToHom η).toFunctor.obj (LHS.obj X) = RHS.obj X
  -- where LHS.obj X = (F.map (twExtendCod (a ≫ b) c)).toFunctor.obj
  --                    ((F.map (twExtendDom a b)).toFunctor.obj X)
  -- Goal: LHS.obj X ≍ RHS.obj X
  -- Use: LHS.obj X ≍ (eqToHom η).toFunctor.obj (LHS.obj X) = RHS.obj X
  apply HEq.trans (HEq.symm (eqToHom_obj_heq _ _ η _))
  exact heq_of_eq step3

/--
Object HEq for hA6B6: the twExtendDom composition.
-/
private lemma assoc_obj_heq_extendDom
    {A B E D : C}
    (a : A ⟶ B) (b : B ⟶ E) (c : E ⟶ D)
    (X : F.obj (twObjMk c)) :
    (F.map (twExtendDom (a ≫ b) c)).toFunctor.obj X ≍
    (F.map (twExtendDom a (b ≫ c))).toFunctor.obj
      ((F.map (twExtendDom b c)).toFunctor.obj X) := by
  -- From Fmap_twExtendDom_comp_eqToHom:
  -- LHS ≫ eqToHom η = RHS_comp
  have hEq := Fmap_twExtendDom_comp_eqToHom F a b c
  let η := congrArg F.obj (congrArg twObjMk (Category.assoc a b c))
  -- From hEq: (eqToHom η).toFunctor.obj (LHS.obj X) = RHS_comp.obj X
  have step3 : (F.map (twExtendDom (a ≫ b) c) ≫ eqToHom η).toFunctor.obj X =
    (F.map (twExtendDom b c) ≫ F.map (twExtendDom a (b ≫ c))).toFunctor.obj X := by
    rw [hEq]
  simp only [Cat.Hom.comp_toFunctor, Functor.comp_obj] at step3
  -- step3: (eqToHom η).toFunctor.obj (LHS.obj X) = RHS.obj X
  -- Goal: LHS.obj X ≍ RHS.obj X
  apply HEq.trans (HEq.symm (eqToHom_obj_heq _ _ η _))
  exact heq_of_eq step3

/--
Helper for fiber associativity: given category equality, object HEqs, and
piecewise morphism HEqs, proves the full 6-composition HEq.
-/
private lemma decFact_assoc_core
    {D E : Cat.{v, u}}
    (hCatEq : D = E)
    {A1 A2 A3 A4 A5 A6 A7 : ↥D}
    {B1 B2 B3 B4 B5 B6 B7 : ↥E}
    (f1 : A1 ⟶ A2) (f2 : A3 ⟶ A4) (f3 : A5 ⟶ A6)
    (g1 : B1 ⟶ B2) (g2 : B3 ⟶ B4) (g3 : B5 ⟶ B6)
    (e1 : A2 = A3) (e2 : A4 = A5) (e3 : A6 = A7)
    (e1' : B2 = B3) (e2' : B4 = B5) (e3' : B6 = B7)
    (hf1 : f1 ≍ g1) (hf2 : f2 ≍ g2) (hf3 : f3 ≍ g3)
    -- Explicit object HEqs needed for heq_comp
    (hA1B1 : A1 ≍ B1) (hA2B2 : A2 ≍ B2) (hA4B4 : A4 ≍ B4) (hA6B6 : A6 ≍ B6) :
    f1 ≫ eqToHom e1 ≫ f2 ≫ eqToHom e2 ≫ f3 ≫ eqToHom e3 ≍
      g1 ≫ eqToHom e1' ≫ g2 ≫ eqToHom e2' ≫ g3 ≫ eqToHom e3' := by
  subst hCatEq
  cases e1; cases e2; cases e3; cases e1'; cases e2'; cases e3'
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  -- Goal: f1 ≫ f2 ≫ f3 ≍ g1 ≫ g2 ≫ g3
  -- Convert object HEqs to equalities (now in same category)
  have eq1 : A1 = B1 := eq_of_heq hA1B1
  have eq2 : A2 = B2 := eq_of_heq hA2B2
  have eq4 : A4 = B4 := eq_of_heq hA4B4
  have eq6 : A6 = B6 := eq_of_heq hA6B6
  exact heq_comp eq1 eq2 eq6 hf1 (heq_comp eq2 eq4 eq6 hf2 hf3)

/-- Core lemma for fiber associativity with explicit morphism arguments.
Takes the three factorisation morphisms and their fiber components as
separate arguments to make the structure clearer. -/
private lemma decFact_comp_assoc_fiber_explicit
    {W X Y Z : DecFactObj F tw}
    (fH : W.fact ⟶ X.fact) (gH : X.fact ⟶ Y.fact) (hH : Y.fact ⟶ Z.fact)
    (fM : (F.map (twObjMkFromIdentity fH.h)).toFunctor.obj W.fiber ⟶
          (F.map (twObjMkFromIdentityAtCod fH.h)).toFunctor.obj X.fiber)
    (gM : (F.map (twObjMkFromIdentity gH.h)).toFunctor.obj X.fiber ⟶
          (F.map (twObjMkFromIdentityAtCod gH.h)).toFunctor.obj Y.fiber)
    (hM : (F.map (twObjMkFromIdentity hH.h)).toFunctor.obj Y.fiber ⟶
          (F.map (twObjMkFromIdentityAtCod hH.h)).toFunctor.obj Z.fiber) :
    (decFactComp F tw (decFactComp F tw ⟨fH, fM⟩ ⟨gH, gM⟩) ⟨hH, hM⟩).fiberMorph ≍
      (decFactComp F tw ⟨fH, fM⟩ (decFactComp F tw ⟨gH, gM⟩ ⟨hH, hM⟩)).fiberMorph := by
  simp only [decFactComp, Functor.map_comp, Category.assoc,
    eqToHom_trans, eqToHom_trans_assoc, eqToHom_map]
  apply HEq.trans (eqToHom_comp_heq _ _)
  apply HEq.trans _ (HEq.symm (eqToHom_comp_heq _ _))
  -- Goal: LHS composition ≍ RHS composition (without leading eqToHom on each)
  -- Get all three transform lemmas
  have hfM := assoc_fM_transform F fH.h gH.h hH.h fM
  have hgM := assoc_gM_transform F fH.h gH.h hH.h gM
  have hhM := assoc_hM_transform F fH.h gH.h hH.h hM
  -- The common eqToHom from associativity
  let η := congrArg F.obj (congrArg twObjMk (Category.assoc fH.h gH.h hH.h)).symm
  -- Each piece: LHS_piece ≍ η.map(RHS_piece) ≍ RHS_piece
  have hfM' : (F.map (twExtendCod (fH.h ≫ gH.h) hH.h)).toFunctor.map
        ((F.map (twExtendCod fH.h gH.h)).toFunctor.map fM) ≍
      (F.map (twExtendCod fH.h (gH.h ≫ hH.h))).toFunctor.map fM :=
    HEq.trans hfM (Cat.eqToHom_map_heq η _)
  have hgM' : (F.map (twExtendCod (fH.h ≫ gH.h) hH.h)).toFunctor.map
        ((F.map (twExtendDom fH.h gH.h)).toFunctor.map gM) ≍
      (F.map (twExtendDom fH.h (gH.h ≫ hH.h))).toFunctor.map
        ((F.map (twExtendCod gH.h hH.h)).toFunctor.map gM) :=
    HEq.trans hgM (Cat.eqToHom_map_heq η _)
  have hhM' : (F.map (twExtendDom (fH.h ≫ gH.h) hH.h)).toFunctor.map hM ≍
      (F.map (twExtendDom fH.h (gH.h ≫ hH.h))).toFunctor.map
        ((F.map (twExtendDom gH.h hH.h)).toFunctor.map hM) :=
    HEq.trans hhM (Cat.eqToHom_map_heq η _)
  -- Convert goal to use fH.h ≫ gH.h instead of (fH ≫ gH).h
  change (F.map (twExtendCod (fH.h ≫ gH.h) hH.h)).toFunctor.map
        ((F.map (twExtendCod fH.h gH.h)).toFunctor.map fM) ≫
        eqToHom _ ≫
        (F.map (twExtendCod (fH.h ≫ gH.h) hH.h)).toFunctor.map
          ((F.map (twExtendDom fH.h gH.h)).toFunctor.map gM) ≫
        eqToHom _ ≫
        (F.map (twExtendDom (fH.h ≫ gH.h) hH.h)).toFunctor.map hM ≫
        eqToHom _ ≍
      (F.map (twExtendCod fH.h (gH.h ≫ hH.h))).toFunctor.map fM ≫
        eqToHom _ ≫
        (F.map (twExtendDom fH.h (gH.h ≫ hH.h))).toFunctor.map
          ((F.map (twExtendCod gH.h hH.h)).toFunctor.map gM) ≫
        eqToHom _ ≫
        (F.map (twExtendDom fH.h (gH.h ≫ hH.h))).toFunctor.map
          ((F.map (twExtendDom gH.h hH.h)).toFunctor.map hM) ≫
        eqToHom _
  -- The category equality for transport
  have hCatEq : F.obj (twObjMk ((fH.h ≫ gH.h) ≫ hH.h)) =
                F.obj (twObjMk (fH.h ≫ (gH.h ≫ hH.h))) :=
    congrArg F.obj (congrArg twObjMk (Category.assoc fH.h gH.h hH.h))
  -- Object HEqs via helper lemmas
  have hA1B1 := assoc_obj_heq_extendCod F fH.h gH.h hH.h
    ((F.map (twObjMkFromIdentity fH.h)).toFunctor.obj W.fiber)
  have hA2B2 := assoc_obj_heq_extendCod F fH.h gH.h hH.h
    ((F.map (twObjMkFromIdentityAtCod fH.h)).toFunctor.obj X.fiber)
  have hA4B4 := assoc_obj_heq_interchange F fH.h gH.h hH.h
    ((F.map (twObjMkFromIdentityAtCod gH.h)).toFunctor.obj Y.fiber)
  have hA6B6 := assoc_obj_heq_extendDom F fH.h gH.h hH.h
    ((F.map (twObjMkFromIdentityAtCod hH.h)).toFunctor.obj Z.fiber)
  exact decFact_assoc_core hCatEq _ _ _ _ _ _ _ _ _ _ _ _
    hfM' hgM' hhM' hA1B1 hA2B2 hA4B4 hA6B6

/-- The fiber component of associativity: the fiber morphisms are HEq
under the two different associations. -/
private lemma decFact_comp_assoc_fiber
    {w x y z : DecFactObj F tw}
    (f : DecFactHom F tw w x)
    (g : DecFactHom F tw x y)
    (h : DecFactHom F tw y z) :
    (decFactComp F tw (decFactComp F tw f g) h).fiberMorph ≍
      (decFactComp F tw f (decFactComp F tw g h)).fiberMorph :=
  decFact_comp_assoc_fiber_explicit F tw
    f.factHom g.factHom h.factHom f.fiberMorph g.fiberMorph h.fiberMorph

private theorem decFact_comp_assoc
    {w x y z : DecFactObj F tw}
    (f : DecFactHom F tw w x)
    (g : DecFactHom F tw x y)
    (h : DecFactHom F tw y z) :
    decFactComp F tw (decFactComp F tw f g) h =
      decFactComp F tw f (decFactComp F tw g h) := by
  apply decFactHom_ext F tw
  · exact Category.assoc f.factHom g.factHom h.factHom
  · exact decFact_comp_assoc_fiber F tw f g h

instance decFactCategory : Category (DecFactObj F tw) where
  id_comp := decFact_id_comp F tw
  comp_id := decFact_comp_id F tw
  assoc := decFact_comp_assoc F tw

end DecoratedFactorisation

/-! ## Decorated factorisation functor

The `Cat`-valued functor sending each twisted arrow `tw` to the
decorated factorisation category `DecFactObj F tw`, generalizing
`factorisationFunctor`. Since `factorisationMapObj` preserves
midpoints and `factorisationMapHom` preserves the underlying
morphism `h`, the fiber component is unchanged by the mapping.
-/

section DecoratedFactorisationFunctor

universe w₁ w₂

variable (F : TwistedArrow C ⥤ Cat.{w₁, w₂})

/-- The image of a decorated factorisation object under a
twisted arrow morphism. The factorisation component maps
via `factorisationMapObj`; the fiber is unchanged since the
midpoint is preserved. -/
def decFactMapObj
    {x y : TwistedArrow C} (φ : x ⟶ y)
    (d : DecFactObj F x) : DecFactObj F y where
  fact := factorisationMapObj φ d.fact
  fiber := d.fiber

/-- The image of a decorated factorisation morphism under a
twisted arrow morphism. The factorisation morphism maps via
`factorisationMapHom`; the fiber morphism is unchanged since
`h` is preserved. -/
def decFactMapHom
    {x y : TwistedArrow C} (φ : x ⟶ y)
    {d e : DecFactObj F x}
    (m : DecFactHom F x d e) :
    DecFactHom F y (decFactMapObj F φ d)
      (decFactMapObj F φ e) where
  factHom := factorisationMapHom φ m.factHom
  fiberMorph := m.fiberMorph

/-- The functor between decorated factorisation categories
induced by a twisted arrow morphism. -/
def decFactMap
    {x y : TwistedArrow C} (φ : x ⟶ y) :
    DecFactObj F x ⥤ DecFactObj F y where
  obj := decFactMapObj F φ
  map := decFactMapHom F φ
  map_id d := by
    apply decFactHom_ext F y
    · exact Factorisation.Hom.ext rfl
    · rfl
  map_comp m n := by
    apply decFactHom_ext F y
    · exact Factorisation.Hom.ext rfl
    · rfl

@[simp]
private lemma decFact_eqToHom_factHom
    (tw : TwistedArrow C)
    {d e : DecFactObj F tw}
    (p : d = e) :
    (eqToHom p :
      DecFactHom F tw d e).factHom =
    eqToHom (congrArg DecFactObj.fact p) := by
  subst p; rfl

@[simp]
private lemma decFact_comp_factHom
    (tw : TwistedArrow C)
    {d e g : DecFactObj F tw}
    (m : d ⟶ e) (n : e ⟶ g) :
    (m ≫ n).factHom =
    m.factHom ≫ n.factHom := rfl

private lemma decFactMapObj_id
    (tw : TwistedArrow C)
    (d : DecFactObj F tw) :
    decFactMapObj F (𝟙 tw) d = d := by
  rcases d with ⟨⟨mid, ι, π, ι_π⟩, fiber⟩
  simp only [decFactMapObj, factorisationMapObj,
    DecFactObj.mk.injEq, Factorisation.mk.injEq,
    heq_eq_eq, true_and]
  exact ⟨⟨twDomArr_id tw ▸ Category.id_comp _,
    twCodArr_id tw ▸ Category.comp_id _⟩,
    trivial⟩

private lemma decFactMapObj_comp
    {x y z : TwistedArrow C}
    (φ : x ⟶ y) (ψ : y ⟶ z)
    (d : DecFactObj F x) :
    decFactMapObj F (φ ≫ ψ) d =
    decFactMapObj F ψ (decFactMapObj F φ d) := by
  rcases d with ⟨⟨mid, ι, π, ι_π⟩, fiber⟩
  simp only [decFactMapObj, factorisationMapObj,
    DecFactObj.mk.injEq, Factorisation.mk.injEq,
    heq_eq_eq, true_and]
  exact ⟨⟨by rw [twDomArr_comp, Category.assoc],
    by rw [twCodArr_comp, ← Category.assoc]⟩,
    trivial⟩

/-- When a morphism `f` is sandwiched between `eqToHom`
terms, the fiber morphism is unchanged (up to HEq). -/
private lemma decFact_eqToHom_sandwich_fiberMorph_heq
    (tw : TwistedArrow C)
    {d d' e e' : DecFactObj F tw}
    (p : d' = d) (f : d ⟶ e) (q : e = e') :
    f.fiberMorph ≍
      (eqToHom p ≫ f ≫ eqToHom q).fiberMorph := by
  subst p; subst q
  have h : eqToHom rfl ≫ f ≫ eqToHom rfl = f := by
    simp only [eqToHom_refl, Category.id_comp,
      Category.comp_id]
  rw [h]

/-- The `Cat`-valued functor sending each twisted arrow `tw`
to the decorated factorisation category `DecFactObj F tw`,
and each twisted arrow morphism to the induced functor
between decorated factorisation categories. Generalizes
`factorisationFunctor` with the fiber data from `F`. -/
def decFactFunctor :
    TwistedArrow C ⥤
      Cat.{max (max u v) w₁, max (max u v) w₂} where
  obj tw := Cat.of (DecFactObj F tw)
  map φ := (decFactMap F φ).toCatHom
  map_id tw := by
    apply Cat.Hom.ext
    simp only [Functor.toCatHom_toFunctor,
      Cat.Hom.id_toFunctor]
    refine CategoryTheory.Functor.ext
      (fun d ↦ decFactMapObj_id F tw d)
      (fun d e f ↦ ?_)
    · apply decFactHom_ext F tw
      · apply Factorisation.Hom.ext
        simp only [decFact_comp_factHom,
          decFact_eqToHom_factHom,
          factorisation_comp_h,
          factorisation_eqToHom_h,
          decFactMap, decFactMapHom,
          factorisationMapHom,
          Functor.id_map, eqToHom_refl,
          Category.id_comp, Category.comp_id]
      · exact decFact_eqToHom_sandwich_fiberMorph_heq
            F tw _ f _
  map_comp φ ψ := by
    apply Cat.Hom.ext
    simp only [Functor.toCatHom_toFunctor,
      Cat.Hom.comp_toFunctor]
    refine CategoryTheory.Functor.ext
      (fun d ↦ decFactMapObj_comp F φ ψ d)
      (fun d e f ↦ ?_)
    · apply decFactHom_ext F _
      · apply Factorisation.Hom.ext
        simp only [decFact_comp_factHom,
          decFact_eqToHom_factHom,
          factorisation_comp_h,
          factorisation_eqToHom_h,
          decFactMap, decFactMapHom,
          factorisationMapHom,
          Functor.comp_map, eqToHom_refl,
          Category.id_comp, Category.comp_id]
      · exact decFact_eqToHom_sandwich_fiberMorph_heq
            F _ _
            ((decFactMap F φ ⋙ decFactMap F ψ).map f)
            _

end DecoratedFactorisationFunctor

section DecoratedFactorisationAccessors

universe w₁ w₂

variable (F : TwistedArrow C ⥤ Cat.{w₁, w₂})
variable (tw : TwistedArrow C)

/-- The fiber of a decorated factorisation object transported
to `F(twObjMk d.fact.ι)` via the twisted arrow morphism
`twObjMkFromIdentityAtCod d.fact.ι :
  twObjMk (𝟙 d.fact.mid) ⟶ twObjMk d.fact.ι`. -/
def DecFactObj.fiberAtι (d : DecFactObj F tw) :
    F.obj (twObjMk d.fact.ι) :=
  (F.map (twObjMkFromIdentityAtCod d.fact.ι)
    ).toFunctor.obj d.fiber

/-- The fiber of a decorated factorisation object transported
to `F(twObjMk d.fact.π)` via the twisted arrow morphism
`twObjMkFromIdentity d.fact.π :
  twObjMk (𝟙 d.fact.mid) ⟶ twObjMk d.fact.π`. -/
def DecFactObj.fiberAtπ (d : DecFactObj F tw) :
    F.obj (twObjMk d.fact.π) :=
  (F.map (twObjMkFromIdentity d.fact.π)
    ).toFunctor.obj d.fiber

/-- The twisted arrow morphism from `twObjMk (𝟙 d.mid)` to
`tw`, factoring through `twObjMk d.ι` via the ι-path:
`twObjMkFromIdentityAtCod ι ≫ twExtendCod ι π ≫ eqToHom`.
The `eqToHom` witnesses that `twObjMk (ι ≫ π) = tw` via
the factorisation condition `ι_π`. -/
def DecFactObj.fiberToArrMorph
    (d : DecFactObj F tw) :
    twObjMk (𝟙 d.fact.mid) ⟶ tw :=
  twObjMkFromIdentityAtCod d.fact.ι ≫
    twExtendCod d.fact.ι d.fact.π ≫
    eqToHom (congrArg twObjMk d.fact.ι_π)

/-- The fiber of a decorated factorisation object transported
to `F(tw)` via `fiberToArrMorph`. -/
def DecFactObj.fiberAtArr (d : DecFactObj F tw) :
    F.obj tw :=
  (F.map (d.fiberToArrMorph F tw)
    ).toFunctor.obj d.fiber

/-- The alternative twisted arrow morphism from
`twObjMk (𝟙 d.mid)` to `tw`, factoring through
`twObjMk d.π` via the π-path:
`twObjMkFromIdentity π ≫ twExtendDom ι π ≫ eqToHom`. -/
def DecFactObj.fiberToArrMorphViaπ
    (d : DecFactObj F tw) :
    twObjMk (𝟙 d.fact.mid) ⟶ tw :=
  twObjMkFromIdentity d.fact.π ≫
    twExtendDom d.fact.ι d.fact.π ≫
    eqToHom (congrArg twObjMk d.fact.ι_π)

/-- The ι-path and π-path from `twObjMk (𝟙 mid)` to `tw`
agree. This follows from `twMidPaths_eq`. -/
lemma DecFactObj.fiberToArrMorph_eq_viaπ
    (d : DecFactObj F tw) :
    d.fiberToArrMorph F tw =
    d.fiberToArrMorphViaπ F tw := by
  simp only [fiberToArrMorph, fiberToArrMorphViaπ,
    ← Category.assoc]
  congr 1
  exact twMidPaths_eq d.fact.ι d.fact.π

/-- The fiber morphism transported to `F(twObjMk (x.ι ≫ h))`
via `twExtendDom x.ι h`. The source and target are the
images of the source and target of `fiberMorph` under
`F.map(twExtendDom x.ι h)`. -/
def DecFactHom.fiberMorphAtι
    {x y : DecFactObj F tw}
    (f : DecFactHom F tw x y) :
    (F.map (twExtendDom x.fact.ι f.factHom.h)
      ).toFunctor.obj
      ((F.map (twObjMkFromIdentity f.factHom.h)
        ).toFunctor.obj x.fiber) ⟶
    (F.map (twExtendDom x.fact.ι f.factHom.h)
      ).toFunctor.obj
      ((F.map (twObjMkFromIdentityAtCod f.factHom.h)
        ).toFunctor.obj y.fiber) :=
  (F.map (twExtendDom x.fact.ι f.factHom.h)
    ).toFunctor.map f.fiberMorph

/-- The fiber morphism transported to `F(twObjMk (h ≫ y.π))`
via `twExtendCod h y.π`. -/
def DecFactHom.fiberMorphAtπ
    {x y : DecFactObj F tw}
    (f : DecFactHom F tw x y) :
    (F.map (twExtendCod f.factHom.h y.fact.π)
      ).toFunctor.obj
      ((F.map (twObjMkFromIdentity f.factHom.h)
        ).toFunctor.obj x.fiber) ⟶
    (F.map (twExtendCod f.factHom.h y.fact.π)
      ).toFunctor.obj
      ((F.map (twObjMkFromIdentityAtCod f.factHom.h)
        ).toFunctor.obj y.fiber) :=
  (F.map (twExtendCod f.factHom.h y.fact.π)
    ).toFunctor.map f.fiberMorph

/-- The twisted arrow morphism from `twObjMk h` to `tw`,
where `h : x.mid ⟶ y.mid` is the midpoint component of a
decorated factorisation morphism. Composed via the ι-path:
`twExtendDom x.ι h ≫ twExtendCod (x.ι ≫ h) y.π ≫ eqToHom`.
The `eqToHom` uses `x.ι ≫ h ≫ y.π = twArr tw`, which
follows from `ι_h` and `ι_π`. -/
def DecFactHom.fiberMorphToArrMorph
    {x y : DecFactObj F tw}
    (f : DecFactHom F tw x y) :
    twObjMk f.factHom.h ⟶ tw :=
  twExtendDom x.fact.ι f.factHom.h ≫
    twExtendCod (x.fact.ι ≫ f.factHom.h) y.fact.π ≫
    eqToHom (congrArg twObjMk
      (show (x.fact.ι ≫ f.factHom.h) ≫ y.fact.π =
        twArr tw by
      rw [f.factHom.ι_h, y.fact.ι_π]))

/-- The fiber morphism transported to `F(tw)` via
`fiberMorphToArrMorph`. -/
def DecFactHom.fiberMorphAtArr
    {x y : DecFactObj F tw}
    (f : DecFactHom F tw x y) :
    (F.map (f.fiberMorphToArrMorph F tw)
      ).toFunctor.obj
      ((F.map (twObjMkFromIdentity f.factHom.h)
        ).toFunctor.obj x.fiber) ⟶
    (F.map (f.fiberMorphToArrMorph F tw)
      ).toFunctor.obj
      ((F.map (twObjMkFromIdentityAtCod f.factHom.h)
        ).toFunctor.obj y.fiber) :=
  (F.map (f.fiberMorphToArrMorph F tw)
    ).toFunctor.map f.fiberMorph

end DecoratedFactorisationAccessors

section TotalDecoratedFactorisation

universe w₁ w₂

variable (C : Type u) [Category.{v} C]
variable (F : TwistedArrow C ⥤ Cat.{w₁, w₂})

/-- An object of the total decorated factorisation category:
a morphism `f : a ⟶ b` together with a factorisation and
a fiber object over the identity at the midpoint. -/
@[ext]
structure TotalDecFactObj extends TotalFactObj C where
  /-- An object in the fiber category over the identity
  at the midpoint. -/
  fiber : F.obj (twObjMk (𝟙 mid))

/-- A morphism in the total decorated factorisation category:
three morphisms `(domMorph, midMorph, codMorph)` making
both squares commute, together with a fiber morphism
from the right-transport of `x.fiber` to the left-transport
of `y.fiber`. -/
@[ext]
structure TotalDecFactHom
    (x y : TotalDecFactObj C F) extends
    TotalFactHom C x.toTotalFactObj
      y.toTotalFactObj where
  /-- The fiber morphism in `F(twObjMk midMorph)`. -/
  fiberMorph :
    (F.map (twObjMkFromIdentity
        toTotalFactHom.midMorph)
      ).toFunctor.obj x.fiber ⟶
    (F.map (twObjMkFromIdentityAtCod
        toTotalFactHom.midMorph)
      ).toFunctor.obj y.fiber

private lemma totalDecFactId_fiber_eq
    (x : TotalDecFactObj C F) :
    (F.map (twObjMkFromIdentity
        (TotalFactHom.id C x.toTotalFactObj).midMorph)
      ).toFunctor.obj x.fiber =
    (F.map (twObjMkFromIdentityAtCod
        (TotalFactHom.id C x.toTotalFactObj).midMorph)
      ).toFunctor.obj x.fiber := by
  change (F.map (twObjMkFromIdentity (𝟙 x.mid))
    ).toFunctor.obj x.fiber =
    (F.map (twObjMkFromIdentityAtCod (𝟙 x.mid))
      ).toFunctor.obj x.fiber
  rw [twObjMkFromIdentity_id,
    twObjMkFromIdentityAtCod_id]

/-- The identity morphism in the total decorated
factorisation category. -/
def TotalDecFactHom.id (x : TotalDecFactObj C F) :
    TotalDecFactHom C F x x where
  toTotalFactHom := TotalFactHom.id C x.toTotalFactObj
  fiberMorph :=
    eqToHom (totalDecFactId_fiber_eq C F x)

/-- Composition of morphisms in the total decorated
factorisation category. The fiber morphism is composed
by transporting through `twExtendCod` and `twExtendDom`,
mirroring `decFactComp`. -/
def TotalDecFactHom.comp
    {x y z : TotalDecFactObj C F}
    (m : TotalDecFactHom C F x y)
    (n : TotalDecFactHom C F y z) :
    TotalDecFactHom C F x z where
  toTotalFactHom :=
    TotalFactHom.comp C m.toTotalFactHom
      n.toTotalFactHom
  fiberMorph :=
    eqToHom (decFactComp_src_eq F
      m.midMorph n.midMorph x.fiber) ≫
    (F.map (twExtendCod m.midMorph n.midMorph)
      ).toFunctor.map m.fiberMorph ≫
    eqToHom (decFactComp_mid_eq F
      m.midMorph n.midMorph y.fiber) ≫
    (F.map (twExtendDom m.midMorph n.midMorph)
      ).toFunctor.map n.fiberMorph ≫
    eqToHom (decFactComp_tgt_eq F
      m.midMorph n.midMorph z.fiber).symm

@[simp]
lemma TotalDecFactHom.id_midMorph
    (x : TotalDecFactObj C F) :
    (TotalDecFactHom.id C F x).midMorph = 𝟙 _ :=
  rfl

@[simp]
lemma TotalDecFactHom.comp_midMorph
    {x y z : TotalDecFactObj C F}
    (f : TotalDecFactHom C F x y)
    (g : TotalDecFactHom C F y z) :
    (TotalDecFactHom.comp C F f g).midMorph =
    f.midMorph ≫ g.midMorph := rfl

/-- Extensionality for `TotalDecFactHom`: two morphisms
are equal if their `TotalFactHom` components are equal and
their fiber morphisms are heterogeneously equal. -/
theorem totalDecFactHom_ext
    {x y : TotalDecFactObj C F}
    {m n : TotalDecFactHom C F x y}
    (hFact : m.toTotalFactHom = n.toTotalFactHom)
    (hFiber : HEq m.fiberMorph n.fiberMorph) :
    m = n := by
  rcases m with ⟨mf, mm⟩
  rcases n with ⟨nf, nm⟩
  obtain rfl := hFact
  congr 1
  exact eq_of_heq hFiber

private theorem totalDecFact_id_comp
    {x y : TotalDecFactObj C F}
    (f : TotalDecFactHom C F x y) :
    TotalDecFactHom.comp C F
      (TotalDecFactHom.id C F x) f = f := by
  rcases f with ⟨factHom, fiberMorph⟩
  simp only [TotalDecFactHom.comp,
    TotalDecFactHom.id]
  congr 1
  · show TotalFactHom.comp C
        (TotalFactHom.id C _) factHom = factHom
    exact TotalFactHom.ext
      (Category.id_comp _) (Category.id_comp _)
      (Category.id_comp _)
  · apply HEq.trans (eqToHom_comp_heq _ _)
    conv_lhs => rw [eqToHom_map]
    apply HEq.trans (eqToHom_comp_heq _ _)
    apply HEq.trans (eqToHom_comp_heq _ _)
    apply HEq.trans (comp_eqToHom_heq _ _)
    change (F.map (twExtendDom (𝟙 x.mid)
        factHom.midMorph)
      ).toFunctor.map fiberMorph ≍ fiberMorph
    rw [twExtendDom_id_left, eqToHom_map]
    exact Cat.eqToHom_map_heq _ _

private theorem totalDecFact_comp_id
    {x y : TotalDecFactObj C F}
    (f : TotalDecFactHom C F x y) :
    TotalDecFactHom.comp C F f
      (TotalDecFactHom.id C F y) = f := by
  rcases f with ⟨factHom, fiberMorph⟩
  simp only [TotalDecFactHom.comp,
    TotalDecFactHom.id]
  congr 1
  · show TotalFactHom.comp C
        factHom (TotalFactHom.id C _) = factHom
    exact TotalFactHom.ext
      (Category.comp_id _) (Category.comp_id _)
      (Category.comp_id _)
  · apply HEq.trans (eqToHom_comp_heq _ _)
    conv_lhs =>
      rw [eqToHom_map, eqToHom_trans, eqToHom_trans]
    apply HEq.trans (comp_eqToHom_heq _ _)
    change (F.map (twExtendCod factHom.midMorph
        (𝟙 y.mid))
      ).toFunctor.map fiberMorph ≍ fiberMorph
    rw [twExtendCod_id_right, eqToHom_map]
    exact Cat.eqToHom_map_heq _ _

private theorem totalDecFact_comp_assoc
    {w x y z : TotalDecFactObj C F}
    (f : TotalDecFactHom C F w x)
    (g : TotalDecFactHom C F x y)
    (h : TotalDecFactHom C F y z) :
    TotalDecFactHom.comp C F
      (TotalDecFactHom.comp C F f g) h =
    TotalDecFactHom.comp C F f
      (TotalDecFactHom.comp C F g h) := by
  apply totalDecFactHom_ext C F
  · change TotalFactHom.comp C
        (TotalFactHom.comp C _ _) _ =
      TotalFactHom.comp C _
        (TotalFactHom.comp C _ _)
    exact TotalFactHom.ext
      (Category.assoc _ _ _)
      (Category.assoc _ _ _)
      (Category.assoc _ _ _)
  · -- The fiberMorph HEq follows from the same
    -- associativity argument as decFact_comp_assoc.
    rcases f with ⟨fFact, fFib⟩
    rcases g with ⟨gFact, gFib⟩
    rcases h with ⟨hFact, hFib⟩
    simp only [TotalDecFactHom.comp]
    simp only [Functor.map_comp,
      Category.assoc, eqToHom_trans,
      eqToHom_trans_assoc, eqToHom_map]
    apply HEq.trans (eqToHom_comp_heq _ _)
    apply HEq.trans _
      (HEq.symm (eqToHom_comp_heq _ _))
    have hfM := assoc_fM_transform F
      fFact.midMorph gFact.midMorph
      hFact.midMorph fFib
    have hgM := assoc_gM_transform F
      fFact.midMorph gFact.midMorph
      hFact.midMorph gFib
    have hhM := assoc_hM_transform F
      fFact.midMorph gFact.midMorph
      hFact.midMorph hFib
    let η := congrArg F.obj (congrArg twObjMk
      (Category.assoc fFact.midMorph
        gFact.midMorph hFact.midMorph).symm)
    have hfM' := HEq.trans hfM
      (Cat.eqToHom_map_heq η _)
    have hgM' := HEq.trans hgM
      (Cat.eqToHom_map_heq η _)
    have hhM' := HEq.trans hhM
      (Cat.eqToHom_map_heq η _)
    have hCatEq :
      F.obj (twObjMk ((fFact.midMorph ≫
        gFact.midMorph) ≫ hFact.midMorph)) =
      F.obj (twObjMk (fFact.midMorph ≫
        (gFact.midMorph ≫ hFact.midMorph))) :=
      congrArg F.obj (congrArg twObjMk
        (Category.assoc fFact.midMorph
          gFact.midMorph hFact.midMorph))
    have hA1B1 := assoc_obj_heq_extendCod F
      fFact.midMorph gFact.midMorph
      hFact.midMorph
      ((F.map (twObjMkFromIdentity
          fFact.midMorph)).toFunctor.obj w.fiber)
    have hA2B2 := assoc_obj_heq_extendCod F
      fFact.midMorph gFact.midMorph
      hFact.midMorph
      ((F.map (twObjMkFromIdentityAtCod
          fFact.midMorph)).toFunctor.obj x.fiber)
    have hA4B4 := assoc_obj_heq_interchange F
      fFact.midMorph gFact.midMorph
      hFact.midMorph
      ((F.map (twObjMkFromIdentityAtCod
          gFact.midMorph)).toFunctor.obj y.fiber)
    have hA6B6 := assoc_obj_heq_extendDom F
      fFact.midMorph gFact.midMorph
      hFact.midMorph
      ((F.map (twObjMkFromIdentityAtCod
          hFact.midMorph)).toFunctor.obj z.fiber)
    exact decFact_assoc_core hCatEq _ _ _ _ _ _ _ _
      _ _ _ _ hfM' hgM' hhM' hA1B1 hA2B2 hA4B4
      hA6B6

instance totalDecFactCategory :
    Category (TotalDecFactObj C F) where
  Hom := TotalDecFactHom C F
  id := TotalDecFactHom.id C F
  comp := TotalDecFactHom.comp C F
  id_comp := totalDecFact_id_comp C F
  comp_id := totalDecFact_comp_id C F
  assoc := totalDecFact_comp_assoc C F

/-- Two `DecFactObj`s with the same midpoint, factors, and
fiber are heterogeneously equal, even when the underlying
twisted arrows differ propositionally. -/
private lemma decFactObj_heq
    {tw tw' : TwistedArrow C}
    (htw : tw = tw')
    (d : DecFactObj F tw) (e : DecFactObj F tw')
    (hmid : d.fact.mid = e.fact.mid)
    (hι : HEq d.fact.ι e.fact.ι)
    (hπ : HEq d.fact.π e.fact.π)
    (hfib : HEq d.fiber e.fiber) :
    HEq d e := by
  subst htw
  rcases d with ⟨⟨dm, di, dp, dip⟩, df⟩
  rcases e with ⟨⟨em, ei, ep, eip⟩, ef⟩
  dsimp only [] at hmid hι hπ hfib
  subst hmid
  cases (eq_of_heq hι)
  cases (eq_of_heq hπ)
  cases (eq_of_heq hfib)
  exact heq_of_eq rfl

/-- The total decorated factorisation Grothendieck
construction as an instance of `TwGrothendieckObj`. -/
abbrev TotalDecFactGrothendieck :=
  TwGrothendieckObj C (decFactFunctor F)

/-- The type equivalence between the connected
Grothendieck construction over `decFactFunctor F` and the
total decorated factorisation category. -/
def totalDecFactGrothendieckEquivObj :
    TotalDecFactGrothendieck C F ≃
      TotalDecFactObj C F where
  toFun x :=
    { dom := twDom' x.arrow
      cod := twCod' x.arrow
      mid := x.fiber.fact.mid
      ι := x.fiber.fact.ι
      π := x.fiber.fact.π
      fiber := x.fiber.fiber }
  invFun y :=
    { arrow := twObjMk' (y.ι ≫ y.π)
      fiber :=
        { fact :=
            { mid := y.mid
              ι := y.ι
              π := y.π
              ι_π := rfl }
          fiber := y.fiber } }
  right_inv _ := rfl
  left_inv x := by
    apply ConnGrothendieckObj.ext
    · exact congrArg twObjMk' x.fiber.fact.ι_π
    · dsimp only []
      exact decFactObj_heq (F := F)
        (htw := congrArg tw'ToTw.obj
          (congrArg twObjMk' x.fiber.fact.ι_π))
        (hmid := rfl) (hι := HEq.refl _)
        (hπ := HEq.refl _)
        (hfib := HEq.refl _)
        (d := _) (e := _)

private abbrev toTotalDecFact :=
  totalDecFactGrothendieckEquivObj C F

/-- The `Category` instance on
`TotalDecFactGrothendieck C F`, transferred from
`TotalDecFactObj C F` via the object equivalence.
Morphisms from `x` to `y` are
`TotalDecFactHom C F (e x) (e y)` where `e` is the
object equivalence. -/
instance : Category
    (TotalDecFactGrothendieck C F) where
  Hom x y :=
    TotalDecFactHom C F
      (toTotalDecFact C F x) (toTotalDecFact C F y)
  id x :=
    TotalDecFactHom.id C F (toTotalDecFact C F x)
  comp f g := TotalDecFactHom.comp C F f g
  id_comp := totalDecFact_id_comp C F
  comp_id := totalDecFact_comp_id C F
  assoc := totalDecFact_comp_assoc C F

/-- The functor from `TotalDecFactObj C F` to
`TotalDecFactGrothendieck C F`, given by the inverse of
the object equivalence. -/
def totalDecFactToGrothendieck :
    TotalDecFactObj C F ⥤
      TotalDecFactGrothendieck C F where
  obj x := (toTotalDecFact C F).symm x
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The functor from `TotalDecFactGrothendieck C F` to
`TotalDecFactObj C F`, given by the object equivalence. -/
def grothendieckToTotalDecFact :
    TotalDecFactGrothendieck C F ⥤
      TotalDecFactObj C F where
  obj x := toTotalDecFact C F x
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl

/-- `grothendieckToTotalDecFact ⋙ totalDecFactToGrothendieck`
is the identity on objects. -/
private lemma grothendieckTotalDecFactRoundTrip_obj
    (x : TotalDecFactGrothendieck C F) :
    (totalDecFactToGrothendieck C F).obj
      ((grothendieckToTotalDecFact C F).obj x) = x :=
  (toTotalDecFact C F).left_inv x

/-- `totalDecFactToGrothendieck ⋙ grothendieckToTotalDecFact`
is the identity on objects. -/
private lemma totalDecFactGrothendieckRoundTrip_obj
    (x : TotalDecFactObj C F) :
    (grothendieckToTotalDecFact C F).obj
      ((totalDecFactToGrothendieck C F).obj x) = x :=
  (toTotalDecFact C F).right_inv x

/-- The categorical isomorphism
`TotalDecFactObj C F ≅Cat TotalDecFactGrothendieck C F`. -/
def totalDecFactIsoGrothendieck :
    TotalDecFactObj C F ≅Cat
      TotalDecFactGrothendieck C F where
  hom := (totalDecFactToGrothendieck C F).toCatHom
  inv := (grothendieckToTotalDecFact C F).toCatHom
  hom_inv_id := rfl
  inv_hom_id := by
    apply Cat.Hom.ext
    simp only [Cat.Hom.comp_toFunctor,
      Cat.Hom.id_toFunctor,
      Functor.toCatHom_toFunctor]
    refine Functor.hext
      (grothendieckTotalDecFactRoundTrip_obj C F)
      (fun x y f => ?_)
    exact heq_of_eq rfl

end TotalDecoratedFactorisation

end GebLean
