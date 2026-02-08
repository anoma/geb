import GebLean.Paranatural
import GebLean.Weighted
import GebLean.ComprehensiveWeighted
import GebLean.Factorization
import GebLean.Utilities.TwistedArrow
import GebLean.Utilities.TwArrPresheaf
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Adjunction.Limits

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

section DiagDetermined

variable (C : Type u) [Category.{v} C]
variable (F : TwistedArrow C ⥤ Cat.{w₁, w₂})

/-- A `Cat`-valued functor `F` on the twisted arrow
category is diagonally determined when the assembly
functor is an equivalence at every twisted arrow. -/
def IsDiagDeterminedEverywhere :=
  ∀ (tw : TwistedArrow C),
    IsDiagDetermined F tw

end DiagDetermined

section EndoProfLimits

open CategoryTheory.Limits

/-!
## Topos operations in EndoProf

`EndoProf` has products and a terminal object.
Equalizers do not exist in general: the diagonal
restriction `{d ∈ F(c,c) | α_c(d) = β_c(d)}` cannot
extend to off-diagonal entries because the profunctor
actions may not preserve the equalizer condition.
-/

universe w₃

variable (C : Type u) [Category.{v} C]

/-- The unit endoprofunctor, constant at `PUnit`.
Terminal object in `EndoProf`. -/
def unitEndoProf : Cᵒᵖ ⥤ C ⥤ Type w₃ :=
  (Functor.const Cᵒᵖ).obj
    ((Functor.const C).obj PUnit.{w₃ + 1})

variable {C}
variable (F : Cᵒᵖ ⥤ C ⥤ Type w₃)

/-- The unique paranatural transformation from any
endoprofunctor to the unit endoprofunctor. -/
def endoProfToTerminal :
    Paranat F (unitEndoProf C) where
  app _ _ := PUnit.unit
  paranatural _ _ _ _ _ _ := rfl

theorem endoProfToTerminal_unique
    (α : Paranat F (unitEndoProf C)) :
    α = endoProfToTerminal F := by
  apply Paranat.ext
  funext I d
  exact match α.app I d with | PUnit.unit => rfl

instance endoProfToTerminalUnique
    (G : Cᵒᵖ ⥤ C ⥤ Type w₃) :
    @Unique (@Quiver.Hom _
      endoProfCategory.toQuiver G (unitEndoProf C))
    where
  default := endoProfToTerminal G
  uniq α := (endoProfToTerminal_unique G α).symm

def endoProfTerminal_isTerminal :
    @IsTerminal (Cᵒᵖ ⥤ C ⥤ Type w₃)
      endoProfCategory (unitEndoProf C) :=
  @IsTerminal.ofUnique _ endoProfCategory _
    (fun G => endoProfToTerminalUnique G)

variable (G : Cᵒᵖ ⥤ C ⥤ Type w₃)

/-- The pointwise product of two endoprofunctors.
`(prodEndoProf F G)(a, b) = F(a, b) × G(a, b)`,
with componentwise covariant and contravariant
actions. -/
def prodEndoProf : Cᵒᵖ ⥤ C ⥤ Type w₃ where
  obj a :=
    { obj := fun b =>
        (F.obj a).obj b × (G.obj a).obj b
      map := fun f p =>
        ((F.obj a).map f p.1,
          (G.obj a).map f p.2)
      map_id := by
        intro b; funext ⟨x, y⟩
        exact Prod.ext
          (congrFun ((F.obj a).map_id b) x)
          (congrFun ((G.obj a).map_id b) y)
      map_comp := by
        intro b₁ b₂ b₃ f g; funext ⟨x, y⟩
        exact Prod.ext
          (congrFun ((F.obj a).map_comp f g) x)
          (congrFun ((G.obj a).map_comp f g) y) }
  map {a₁ a₂} h :=
    { app := fun b p =>
        ((F.map h).app b p.1,
          (G.map h).app b p.2)
      naturality := by
        intro b₁ b₂ f; funext ⟨x, y⟩
        exact Prod.ext
          (congrFun ((F.map h).naturality f) x)
          (congrFun
            ((G.map h).naturality f) y) }
  map_id := by
    intro a; ext b ⟨x, y⟩
    · change (F.map (𝟙 a)).app b x = x
      simp
    · change (G.map (𝟙 a)).app b y = y
      simp
  map_comp := by
    intro a₁ a₂ a₃ h₁ h₂; ext b ⟨x, y⟩
    · change (F.map (h₁ ≫ h₂)).app b x =
        (F.map h₂).app b ((F.map h₁).app b x)
      simp [Functor.map_comp]
    · change (G.map (h₁ ≫ h₂)).app b y =
        (G.map h₂).app b ((G.map h₁).app b y)
      simp [Functor.map_comp]

/-- First projection from the product endoprofunctor. -/
def endoProfFst :
    Paranat (prodEndoProf F G) F where
  app _ d := d.1
  paranatural _ _ _ _ _ h :=
    congrArg Prod.fst h

/-- Second projection from the product
endoprofunctor. -/
def endoProfSnd :
    Paranat (prodEndoProf F G) G where
  app _ d := d.2
  paranatural _ _ _ _ _ h :=
    congrArg Prod.snd h

variable {F G}
variable {H : Cᵒᵖ ⥤ C ⥤ Type w₃}

/-- Pairing of two paranatural transformations into the
product endoprofunctor. -/
def endoProfPair
    (α : Paranat H F) (β : Paranat H G) :
    Paranat H (prodEndoProf F G) where
  app I d := (α.app I d, β.app I d)
  paranatural I₀ I₁ f d₀ d₁ h :=
    Prod.ext
      (α.paranatural I₀ I₁ f d₀ d₁ h)
      (β.paranatural I₀ I₁ f d₀ d₁ h)

@[simp]
theorem endoProfPair_fst
    (α : Paranat H F) (β : Paranat H G) :
    Paranat.comp (endoProfPair α β)
      (endoProfFst F G) = α := by
  apply Paranat.ext; rfl

@[simp]
theorem endoProfPair_snd
    (α : Paranat H F) (β : Paranat H G) :
    Paranat.comp (endoProfPair α β)
      (endoProfSnd F G) = β := by
  apply Paranat.ext; rfl

theorem endoProfPair_unique
    (α : Paranat H (prodEndoProf F G)) :
    α = endoProfPair
      (Paranat.comp α (endoProfFst F G))
      (Paranat.comp α (endoProfSnd F G)) := by
  apply Paranat.ext
  funext I d
  exact (Prod.mk.eta).symm

/-!
The proofs `endoProfPair_fst`, `endoProfPair_snd`,
and `endoProfPair_unique` establish the universal
property of binary products in `EndoProf` at the
level of `Paranat` morphisms: `prodEndoProf F G`
together with projections `endoProfFst` and
`endoProfSnd` satisfies the unique factorization
property.
-/

end EndoProfLimits

section ProfOnTwArrPreservesLimits

open CategoryTheory.Limits

/-!
## Limit preservation by profunctorOnTwistedArrowFunctor

`profunctorOnTwistedArrowFunctor` decomposes as
`Functor.uncurry ⋙ (whiskeringLeft ...).obj F`.
`uncurry` is one half of the currying equivalence,
hence preserves limits. `whiskeringLeft` preserves
limits when the target category has the relevant
limits. The composition preserves limits.
-/

variable {D : Type*} [Category D]
variable {J : Type*} [Category J]

instance uncurry_preservesLimitsOfShape
    [HasLimitsOfShape J D] :
    PreservesLimitsOfShape J
      (Functor.uncurry
        (C := Cᵒᵖ) (D := C) (E := D)) :=
  show PreservesLimitsOfShape J
    Functor.currying.functor from inferInstance

instance whiskeringLeftTwForget_preservesLimitsOfShape
    [HasLimitsOfShape J D] :
    PreservesLimitsOfShape J
      ((Functor.whiskeringLeft
        (TwistedArrow C) (Cᵒᵖ × C) D).obj
        (twistedArrowForget C)) :=
  inferInstance

instance profOnTwArr_preservesLimitsOfShape
    [HasLimitsOfShape J D] :
    PreservesLimitsOfShape J
      (profunctorOnTwistedArrowFunctor C
        (D := D)) := by
  unfold profunctorOnTwistedArrowFunctor
  infer_instance

end ProfOnTwArrPreservesLimits

section Equalizers

/-!
## Lack of equalizers in EndoProf

The equalizer of two paranatural transformations
`α, β : Paranat F G` would need a subprofunctor of `F`
whose diagonal is `{d ∈ F(c,c) | α(c)(d) = β(c)(d)}`
and which is closed under the profunctor actions. The
profunctor actions can map off-diagonal elements back
to the diagonal via `(F.obj (op a)).map f : F(a,b) →
F(a,a)` when `f : b ⟶ a`, or `(F.map g.op).app a :
F(b,a) → F(a,a)` when `g : a ⟶ b`. The resulting
diagonal elements may not lie in the equalizer.
-/

universe w₄

variable {C : Type u} [Category.{v} C]
variable {F G : Cᵒᵖ ⥤ C ⥤ Type w₄}

/-- The diagonal equalizer of two paranatural
transformations at an object `I`. Elements of
`diagApp F I` on which `α` and `β` agree. -/
def diagEqualizer
    (α β : Paranat F G) (I : C) : Type w₄ :=
  { d : diagApp F I // α.app I d = β.app I d }

/-- The covariant action `(F.obj (op a)).map f` for
`f : b ⟶ a` sends `F(a,b) → F(a,a)`. For the
diagonal equalizer to extend to a subprofunctor,
the image of every element of `F(a,b)` under this
map must land in `diagEqualizer α β a`. -/
def EqualizerClosedUnderCov
    (α β : Paranat F G) : Prop :=
  ∀ (a b : C) (f : b ⟶ a)
    (x : (F.obj (Opposite.op a)).obj b),
    α.app a ((F.obj (Opposite.op a)).map f x) =
    β.app a ((F.obj (Opposite.op a)).map f x)

/-- The contravariant action `(F.map g.op).app a` for
`g : a ⟶ b` sends `F(b,a) → F(a,a)`. For the
diagonal equalizer to extend to a subprofunctor,
the image of every element of `F(b,a)` under this
map must land in `diagEqualizer α β a`. -/
def EqualizerClosedUnderContra
    (α β : Paranat F G) : Prop :=
  ∀ (a b : C) (g : a ⟶ b)
    (x : (F.obj (Opposite.op b)).obj a),
    α.app a ((F.map g.op).app a x) =
    β.app a ((F.map g.op).app a x)

/-- The conjunction of closure under both the covariant
and contravariant actions. When this holds, the diagonal
equalizer extends to a subprofunctor of `F`. -/
def EqualizerWellDefined
    (α β : Paranat F G) : Prop :=
  EqualizerClosedUnderCov α β ∧
    EqualizerClosedUnderContra α β

end Equalizers

end GebLean
