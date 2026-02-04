import Mathlib.CategoryTheory.Category.Factorisation
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

end TwGrothendieckFactorisation

end GebLean
