import GebLean.Paranatural
import GebLean.Weighted
import GebLean.ComprehensiveWeighted
import GebLean.Factorization
import GebLean.Utilities.TwistedArrow
import GebLean.Utilities.TwArrPresheaf

/-!
# Paranatural Topos

Investigation of subcategories of profunctors with
paranatural transformations that form toposes.

## Assembly functor

Given `F : TwistedArrow C ⥤ Cat` and a twisted arrow
`tw`, each decorated factorization in `DecFactObj F tw`
carries an element of `F(𝟙 mid)`. A factorization of
`twArr tw` through `mid` determines a morphism
`𝟙 mid → tw` in `Tw(C)`, so `F.map` transports the
fiber element into `F(tw)`. The resulting functor
`DecFactObj F tw ⥤ F.obj tw` is the assembly functor.

A functor `F` is diagonally determined at `tw` when
this assembly functor is an equivalence: every object
of `F(tw)` arises from a diagonal element transported
along a factorization.
-/

namespace GebLean

open CategoryTheory

universe u v w₁ w₂

variable {C : Type u} [Category.{v} C]

section AssemblyFunctor

variable (F : TwistedArrow C ⥤ Cat.{w₁, w₂})
variable (tw : TwistedArrow C)

/-- The twisted arrow morphism from `twObjMk (𝟙 mid)`
to `tw`, induced by a factorization of `twArr tw`
through `mid`. The domain arrow is `ι` and the codomain
arrow is `π`. -/
def factToTwMorph
    (d : Factorisation (twArr tw)) :
    twObjMk (𝟙 d.mid) ⟶ tw :=
  twHomMk d.ι d.π (by
    simp [twObjMk_arr, d.ι_π])

/-- The object-level assembly map: given a decorated
factorization `d`, transport the fiber element from
`F(𝟙 mid)` to `F(tw)` along `factToTwMorph`. -/
def assemblyObj
    (d : DecFactObj F tw) :
    F.obj tw :=
  (F.map (factToTwMorph tw d.fact)).toFunctor.obj
    d.fiber

/-- Given a factorization morphism `h : x.mid ⟶ y.mid`
between two factorizations of `twArr tw`, the twisted
arrow morphism from `twObjMk h` to `tw` with domain
arrow `x.ι` and codomain arrow `y.π`. -/
def factHomToTwMorph
    {x y : Factorisation (twArr tw)}
    (f : x ⟶ y) :
    twObjMk f.h ⟶ tw :=
  twHomMk x.ι y.π (by
    simp [twObjMk_arr])

@[simp]
lemma factHomToTwMorph_domArr
    {x y : Factorisation (twArr tw)}
    (f : x ⟶ y) :
    twDomArr (factHomToTwMorph tw f) = x.ι := rfl

@[simp]
lemma factHomToTwMorph_codArr
    {x y : Factorisation (twArr tw)}
    (f : x ⟶ y) :
    twCodArr (factHomToTwMorph tw f) = y.π := rfl

@[simp]
lemma factToTwMorph_domArr
    (d : Factorisation (twArr tw)) :
    twDomArr (factToTwMorph tw d) = d.ι := rfl

@[simp]
lemma factToTwMorph_codArr
    (d : Factorisation (twArr tw)) :
    twCodArr (factToTwMorph tw d) = d.π := rfl

/-- `factToTwMorph` factors through `factHomToTwMorph`
via `twObjMkFromIdentity h` on the domain side. -/
lemma factToTwMorph_eq_fromIdentity_comp
    {x y : Factorisation (twArr tw)}
    (f : x ⟶ y) :
    factToTwMorph tw x =
      twObjMkFromIdentity f.h ≫
        factHomToTwMorph tw f := by
  apply twHom_ext
  · simp only [factToTwMorph_domArr,
      twDomArr_comp, factHomToTwMorph_domArr,
      twObjMkFromIdentity_domArr]
    exact (Category.comp_id _).symm
  · simp only [factToTwMorph_codArr,
      twCodArr_comp, factHomToTwMorph_codArr,
      twObjMkFromIdentity_codArr, f.h_π]

/-- `factToTwMorph` factors through `factHomToTwMorph`
via `twObjMkFromIdentityAtCod h` on the codomain
side. -/
lemma factToTwMorph_eq_fromIdentityAtCod_comp
    {x y : Factorisation (twArr tw)}
    (f : x ⟶ y) :
    factToTwMorph tw y =
      twObjMkFromIdentityAtCod f.h ≫
        factHomToTwMorph tw f := by
  apply twHom_ext
  · simp only [factToTwMorph_domArr,
      twDomArr_comp, factHomToTwMorph_domArr,
      twObjMkFromIdentityAtCod_domArr, f.ι_h]
  · simp only [factToTwMorph_codArr,
      twCodArr_comp, factHomToTwMorph_codArr,
      twObjMkFromIdentityAtCod_codArr]
    exact (Category.id_comp _).symm

/-- The source decomposition: `assemblyObj F tw x`
equals the fiber `x.fiber` transported first by
`twObjMkFromIdentity h` and then by
`factHomToTwMorph tw f.factHom`. -/
lemma assemblyObj_source_eq
    {x y : DecFactObj F tw}
    (f : DecFactHom F tw x y) :
    assemblyObj F tw x =
    (F.map (factHomToTwMorph tw f.factHom)
      ).toFunctor.obj
      ((F.map (twObjMkFromIdentity f.factHom.h)
        ).toFunctor.obj x.fiber) := by
  unfold assemblyObj
  rw [factToTwMorph_eq_fromIdentity_comp tw
    f.factHom, Functor.map_comp,
    Cat.Hom.comp_toFunctor, Functor.comp_obj]

/-- The target decomposition: `assemblyObj F tw y`
equals the fiber `y.fiber` transported first by
`twObjMkFromIdentityAtCod h` and then by
`factHomToTwMorph tw f.factHom`. -/
lemma assemblyObj_target_eq
    {x y : DecFactObj F tw}
    (f : DecFactHom F tw x y) :
    assemblyObj F tw y =
    (F.map (factHomToTwMorph tw f.factHom)
      ).toFunctor.obj
      ((F.map (twObjMkFromIdentityAtCod
          f.factHom.h)
        ).toFunctor.obj y.fiber) := by
  unfold assemblyObj
  rw [factToTwMorph_eq_fromIdentityAtCod_comp tw
    f.factHom, Functor.map_comp,
    Cat.Hom.comp_toFunctor, Functor.comp_obj]

/-- The assembly morphism map. Given a decorated
factorization morphism `f : x ⟶ y`, transports
`f.fiberMorph` from `F(twObjMk h)` to `F(tw)` by
applying `F.map(factHomToTwMorph tw f.factHom)`,
composed with `eqToHom` transports for the source
and target decompositions. -/
def assemblyMap
    {x y : DecFactObj F tw}
    (f : DecFactHom F tw x y) :
    assemblyObj F tw x ⟶ assemblyObj F tw y :=
  eqToHom (assemblyObj_source_eq F tw f) ≫
  (F.map (factHomToTwMorph tw f.factHom)
    ).toFunctor.map f.fiberMorph ≫
  eqToHom (assemblyObj_target_eq F tw f).symm

/-- When the factorization morphism is the identity,
`factHomToTwMorph` coincides with `factToTwMorph`. -/
@[simp]
lemma factHomToTwMorph_id
    (d : Factorisation (twArr tw)) :
    factHomToTwMorph tw (𝟙 d) =
      factToTwMorph tw d := by
  apply twHom_ext <;> simp

lemma assemblyMap_id
    (x : DecFactObj F tw) :
    assemblyMap F tw (𝟙 x) =
      𝟙 (assemblyObj F tw x) := by
  change assemblyMap F tw (decFactId F tw x) =
    𝟙 (assemblyObj F tw x)
  simp only [assemblyMap, decFactId, eqToHom_refl]
  rw [CategoryTheory.Functor.map_id,
    Category.id_comp]
  simp only [eqToHom_trans, eqToHom_refl]

/-- Composing `twExtendCod` with `factHomToTwMorph` of a
composed factorization morphism yields `factHomToTwMorph`
for the first factor. -/
lemma factHomToTwMorph_comp_twExtendCod
    {x y z : Factorisation (twArr tw)}
    (f : x ⟶ y) (g : y ⟶ z) :
    twExtendCod f.h g.h ≫
      factHomToTwMorph tw (f ≫ g) =
      factHomToTwMorph tw f := by
  apply twHom_ext
  · simp only [twDomArr_comp, factHomToTwMorph_domArr,
      twExtendCod_domArr]
    exact Category.comp_id _
  · simp only [twCodArr_comp, twExtendCod_codArr,
      factHomToTwMorph_codArr]
    exact Factorisation.Hom.h_π g

/-- Composing `twExtendDom` with `factHomToTwMorph` of a
composed factorization morphism yields `factHomToTwMorph`
for the second factor. -/
lemma factHomToTwMorph_comp_twExtendDom
    {x y z : Factorisation (twArr tw)}
    (f : x ⟶ y) (g : y ⟶ z) :
    twExtendDom f.h g.h ≫
      factHomToTwMorph tw (f ≫ g) =
      factHomToTwMorph tw g := by
  apply twHom_ext
  · simp only [twDomArr_comp, factHomToTwMorph_domArr,
      twExtendDom_domArr]
    exact Factorisation.Hom.ι_h f
  · simp only [twCodArr_comp, twExtendDom_codArr,
      factHomToTwMorph_codArr]
    exact Category.id_comp _

/-- Two-level `Cat`-valued functor map expressed as
single-level with `eqToHom` transport, via
`Functor.congr_hom`. -/
lemma catMapComp_eq
    {a b c : TwistedArrow C}
    (α : a ⟶ b) (β : b ⟶ c)
    {p q : ↑(F.obj a)}
    (m : p ⟶ q) :
    let h := congrArg Cat.Hom.toFunctor
      (F.map_comp α β).symm
    (F.map β).toFunctor.map
        ((F.map α).toFunctor.map m) =
      eqToHom (Functor.congr_obj h p) ≫
      (F.map (α ≫ β)).toFunctor.map m ≫
      eqToHom (Functor.congr_obj h q).symm :=
  Functor.congr_hom
    (congrArg Cat.Hom.toFunctor
      (F.map_comp α β).symm) m

/-- `catMapComp_eq` with the composed morphism replaced
by a given `γ` via a proof `heq : α ≫ β = γ`. -/
lemma catMapComp_transport_eq
    {a b c : TwistedArrow C}
    {α : a ⟶ b} {β : b ⟶ c} {γ : a ⟶ c}
    (heq : α ≫ β = γ)
    {p q : ↑(F.obj a)}
    (m : p ⟶ q) :
    (F.map β).toFunctor.map
        ((F.map α).toFunctor.map m) =
      eqToHom (by subst heq; exact
        Functor.congr_obj (congrArg
          Cat.Hom.toFunctor
          (F.map_comp α β).symm) p) ≫
      (F.map γ).toFunctor.map m ≫
      eqToHom (by subst heq; exact
        (Functor.congr_obj (congrArg
          Cat.Hom.toFunctor
          (F.map_comp α β).symm) q).symm) := by
  subst heq
  exact catMapComp_eq F α β m

lemma assemblyMap_comp
    {x y z : DecFactObj F tw}
    (f : x ⟶ y) (g : y ⟶ z) :
    assemblyMap F tw (f ≫ g) =
      assemblyMap F tw f ≫ assemblyMap F tw g := by
  change assemblyMap F tw (decFactComp F tw f g) =
    assemblyMap F tw f ≫ assemblyMap F tw g
  simp only [assemblyMap, decFactComp]
  simp only [CategoryTheory.Functor.map_comp,
    eqToHom_map]
  simp only [← Category.assoc, eqToHom_trans]
  simp only [Category.assoc]
  rw [catMapComp_transport_eq F
    (factHomToTwMorph_comp_twExtendCod tw
      f.factHom g.factHom) f.fiberMorph]
  rw [catMapComp_transport_eq F
    (factHomToTwMorph_comp_twExtendDom tw
      f.factHom g.factHom) g.fiberMorph]
  simp only [← Category.assoc, eqToHom_trans]
  simp only [Category.assoc, eqToHom_trans]

/-- The assembly functor from the decorated
factorization category `DecFactObj F tw` to the fiber
category `F.obj tw`. Each decorated factorization
`(d, x)` with `x ∈ F(𝟙 mid)` is sent to
`F.map(factToTwMorph tw d)(x) ∈ F(tw)`. -/
def assemblyFunctor :
    DecFactObj F tw ⥤ ↑(F.obj tw) where
  obj := assemblyObj F tw
  map := assemblyMap F tw
  map_id := assemblyMap_id F tw
  map_comp f g := assemblyMap_comp F tw f g

/-- A `Cat`-valued functor `F` on the twisted arrow
category is diagonally determined at `tw` when the
assembly functor is an equivalence: every element of
`F(tw)` arises uniquely (up to isomorphism) from a
diagonal element transported along a factorization. -/
def IsDiagDetermined :=
  (assemblyFunctor F tw).IsEquivalence

end AssemblyFunctor

end GebLean
