import GebLean.Paranatural
import GebLean.HexagonCat
import GebLean.RelSpanDiagram
import Mathlib.CategoryTheory.Limits.IsLimit
import GebLean.Weighted
import GebLean.ComprehensiveWeighted
import GebLean.Factorization
import GebLean.ParanatAlg
import GebLean.DinaturalNumbers
import GebLean.ParamPoly
import GebLean.YonedaRelDouble
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
this assembly functor is essentially surjective: every
object of `F(tw)` is isomorphic to the image of some
diagonal element transported along a factorization.
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
    change x.ι ≫ f.h ≫ y.π = twArr tw
    rw [f.h_π, x.ι_π])

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
      twObjMkFromIdentity_codArr]
    exact f.h_π.symm

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
      twObjMkFromIdentityAtCod_domArr]
    exact f.ι_h.symm
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
  apply twHom_ext <;> rfl

lemma assemblyMap_id
    (x : DecFactObj F tw) :
    assemblyMap F tw (𝟙 x) =
      𝟙 (assemblyObj F tw x) := by
  change assemblyMap F tw (decFactId F tw x) =
    𝟙 (assemblyObj F tw x)
  simp only [assemblyMap, decFactId]
  simp only [CategoryTheory.Functor.map_id,
    Category.id_comp,
    eqToHom_trans, eqToHom_refl]

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
assembly functor is essentially surjective: every
object of `F(tw)` is isomorphic to the image of some
decorated factorization. -/
def IsDiagDetermined :=
  (assemblyFunctor F tw).EssSurj

end AssemblyFunctor

section DiagDetermined

variable (C : Type u) [Category.{v} C]
variable (F : TwistedArrow C ⥤ Cat.{w₁, w₂})

/-- A `Cat`-valued functor `F` on the twisted arrow
category is diagonally determined when the assembly
functor is essentially surjective at every twisted
arrow. -/
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

/-- The binary fan for `prodEndoProf F G` in `EndoProf`
with projections `endoProfFst` and `endoProfSnd`. -/
def endoProfBinaryFan :
    @BinaryFan _ endoProfCategory F G :=
  @BinaryFan.mk _ endoProfCategory _ _
    (prodEndoProf F G)
    (endoProfFst F G) (endoProfSnd F G)

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

/-- `endoProfBinaryFan` is a limit cone: the product
universal property in `EndoProf`. -/
def endoProfBinaryFan_isLimit :
    @IsLimit _ _ _ endoProfCategory _
      (endoProfBinaryFan F G) :=
  @BinaryFan.IsLimit.mk _ endoProfCategory _ _
    (endoProfBinaryFan F G)
    (fun f g => endoProfPair f g)
    (fun f g => endoProfPair_fst f g)
    (fun f g => endoProfPair_snd f g)
    (fun f g m hf hg => by
      rw [endoProfPair_unique m]
      exact congrArg₂ endoProfPair hf hg)

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

/-- The covariant action of `G` away from the diagonal
is injective: for every `a : C` and `g : a ⟶ b`, the
map `(G.obj (op a)).map g : G(a, a) → G(a, b)` is
injective. -/
def CovActionInjective (G : Cᵒᵖ ⥤ C ⥤ Type w₄) :
    Prop :=
  ∀ (a b : C) (g : a ⟶ b),
    Function.Injective ((G.obj (Opposite.op a)).map g)

/-- Naturality of the contravariant action provides
`DiagCompat` for the pair of elements obtained by
applying the covariant and contravariant actions to an
off-diagonal element. Given `x ∈ F(b, a)` and
`g : a ⟶ b`, the contravariant transport
`(F.map g.op).app a x ∈ F(a, a)` and covariant
transport `(F.obj (op b)).map g x ∈ F(b, b)` satisfy
`DiagCompat F a b g`. -/
theorem diagCompat_of_offDiag
    (a b : C) (g : a ⟶ b)
    (x : (F.obj (Opposite.op b)).obj a) :
    DiagCompat F a b g
      ((F.map g.op).app a x)
      ((F.obj (Opposite.op b)).map g x) := by
  simp only [DiagCompat]
  exact (congrFun ((F.map g.op).naturality g) x).symm

/-- Variant of `diagCompat_of_offDiag` with the
morphism reversed. Given `x ∈ F(a, b)` and
`f : b ⟶ a`, the contravariant transport
`(F.map f.op).app b x ∈ F(b, b)` and covariant
transport `(F.obj (op a)).map f x ∈ F(a, a)` satisfy
`DiagCompat F b a f`. -/
theorem diagCompat_of_offDiag'
    (a b : C) (f : b ⟶ a)
    (x : (F.obj (Opposite.op a)).obj b) :
    DiagCompat F b a f
      ((F.map f.op).app b x)
      ((F.obj (Opposite.op a)).map f x) := by
  simp only [DiagCompat]
  exact (congrFun ((F.map f.op).naturality f) x).symm

/-- The contravariant action of `G` away from the
diagonal is injective: for every `a : C` and
`f : b ⟶ a`, the map
`(G.map f.op).app a : G(a, a) → G(b, a)` is
injective. -/
def ContraActionInjective
    (G : Cᵒᵖ ⥤ C ⥤ Type w₄) : Prop :=
  ∀ (a b : C) (f : b ⟶ a),
    Function.Injective ((G.map f.op).app a)

/-- When `G`'s covariant action is injective at the
diagonal, covariant closure of the equalizer implies
contravariant closure. The proof applies paranaturality
of `α` and `β` to the `DiagCompat` pair from
`diagCompat_of_offDiag`, uses `EqualizerClosedUnderCov`
to equate `α` and `β` on the covariant transport, and
concludes via injectivity. -/
theorem covClosed_of_covInjective
    (α β : Paranat F G)
    (hG : CovActionInjective G)
    (hcov : EqualizerClosedUnderCov α β) :
    EqualizerClosedUnderContra α β := by
  intro a b g x
  have hcompat := diagCompat_of_offDiag (F := F) a b g x
  have hα := α.paranatural a b g _ _ hcompat
  have hβ := β.paranatural a b g _ _ hcompat
  have hd₁ : α.app b ((F.obj (Opposite.op b)).map g x)
      = β.app b ((F.obj (Opposite.op b)).map g x) :=
    hcov b a g x
  simp only [DiagCompat] at hα hβ
  have heq : (G.obj (Opposite.op a)).map g (α.app a
      ((F.map g.op).app a x))
      = (G.obj (Opposite.op a)).map g (β.app a
        ((F.map g.op).app a x)) := by
    rw [hα, hβ, hd₁]
  exact hG a b g heq

/-- When `G`'s contravariant action is injective at the
diagonal, contravariant closure of the equalizer implies
covariant closure. Symmetric to
`covClosed_of_covInjective`. -/
theorem contraClosed_of_contraInjective
    (α β : Paranat F G)
    (hG : ContraActionInjective G)
    (hcontra : EqualizerClosedUnderContra α β) :
    EqualizerClosedUnderCov α β := by
  intro a b f x
  have hcompat :=
    diagCompat_of_offDiag' (F := F) a b f x
  have hα := α.paranatural b a f _ _ hcompat
  have hβ := β.paranatural b a f _ _ hcompat
  have hd₀ :
      α.app b ((F.map f.op).app b x)
      = β.app b ((F.map f.op).app b x) :=
    hcontra b a f x
  simp only [DiagCompat] at hα hβ
  have heq : (G.map f.op).app a
      (α.app a ((F.obj (Opposite.op a)).map f x))
      = (G.map f.op).app a
        (β.app a ((F.obj (Opposite.op a)).map f x)) := by
    rw [← hα, ← hβ, hd₀]
  exact hG a b f heq

/-- When both actions of `G` are injective away from the
diagonal, the two equalizer closure conditions are
equivalent. -/
theorem equalizerClosure_iff_of_bothInjective
    (α β : Paranat F G)
    (hcov : CovActionInjective G)
    (hcontra : ContraActionInjective G) :
    EqualizerClosedUnderCov α β ↔
      EqualizerClosedUnderContra α β :=
  ⟨covClosed_of_covInjective α β hcov,
    contraClosed_of_contraInjective α β hcontra⟩

end Equalizers

section DiagDeterminedProf

/-!
## Diagonally determined profunctors (Type-valued)

For a `Type`-valued profunctor `P : Cᵒᵖ ⥤ C ⥤ Type w`,
the assembly map at a twisted arrow `tw` sends each
decorated factorization `(fact, d)` with
`d ∈ P(fact.mid, fact.mid)` to an element of
`P(twDom tw, twCod tw)` by applying the contravariant
action along `fact.ι` followed by the covariant action
along `fact.π`.
-/

open CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]
variable (P : Cᵒᵖ ⥤ C ⥤ Type w₁)
variable (tw : TwistedArrow C)

/-- The assembly map for a `Type`-valued profunctor at a
twisted arrow `tw`. Sends a decorated factorization
`⟨fact, d⟩` with `d ∈ P(mid, mid)` to an element of
`P(twDom tw, twCod tw)` via the contravariant action
along `fact.ι` and the covariant action along
`fact.π`. -/
def assemblyMapProf
    (x : (fact : Factorisation (twArr tw)) ×
      diagApp P fact.mid) :
    (P.obj (Opposite.op (twDom tw))).obj
      (twCod tw) :=
  (P.obj (Opposite.op (twDom tw))).map x.1.π
    ((P.map x.1.ι.op).app x.1.mid x.2)

variable {tw}

/-- A `Type`-valued profunctor `P` is diagonally
determined when `assemblyMapProf P tw` is surjective
for every twisted arrow `tw`: every element of
`P(a, b)` arises from some diagonal element
`d ∈ P(c, c)` transported along a factorization of
`a → b` through `c`. -/
def IsDiagDeterminedProf : Prop :=
  ∀ (tw : TwistedArrow C),
    Function.Surjective (assemblyMapProf P tw)

variable {P}

/-- `IsDiagDeterminedProf` as an `ObjectProperty` on
`EndoProf`, for use with `ObjectProperty.FullSubcategory`
to form the full subcategory of diagonally determined
profunctors. -/
def isDiagDeterminedProfProp :
    @ObjectProperty
      (EndoProf (C := C))
      endoProfCategory.toCategoryStruct :=
  fun Q => IsDiagDeterminedProf Q

/-- The full subcategory of `EndoProf` consisting of
diagonally determined profunctors. Morphisms are
paranatural transformations (inherited from
`endoProfCategory`). -/
abbrev DiagDetProf :=
  @ObjectProperty.FullSubcategory _
    endoProfCategory
    (isDiagDeterminedProfProp (C := C))

end DiagDeterminedProf

section DiagDetTerminal

/-!
## Terminal object in DiagDetProf

The unit endoprofunctor is diagonally determined:
`assemblyMapProf (unitEndoProf C) tw` maps into
`PUnit`, so surjectivity holds for any factorization.
-/

variable (C : Type u) [Category.{v} C]

theorem unitEndoProf_isDiagDetermined :
    IsDiagDeterminedProf
      (unitEndoProf.{u, v, w₁} C) :=
  fun _ y => ⟨⟨Factorisation.initial, PUnit.unit⟩,
    match y with | PUnit.unit => rfl⟩

/-- The unit endoprofunctor as an object of
`DiagDetProf`. -/
def unitDiagDetProf :
    DiagDetProf (C := C) :=
  ⟨unitEndoProf.{u, v, w₁} C,
    unitEndoProf_isDiagDetermined C⟩

open CategoryTheory.Limits in
instance unitDiagDetProf_isTerminal_unique
    (F : DiagDetProf (C := C)) :
    Unique (F ⟶ unitDiagDetProf C) where
  default := ⟨endoProfToTerminal F.obj⟩
  uniq α :=
    ObjectProperty.hom_ext _
      (endoProfToTerminal_unique F.obj α.hom)

open CategoryTheory.Limits in
def unitDiagDetProf_isTerminal :
    IsTerminal (unitDiagDetProf C) :=
  IsTerminal.ofUnique _

end DiagDetTerminal

section DiagDetProducts

/-!
## Products do not preserve diagonal determination

The product `prodEndoProf F G` is not diagonally
determined in general, even when both `F` and `G` are.

The assembly map for `prodEndoProf F G` at a twisted
arrow `tw` sends `⟨fact, (d_F, d_G)⟩` with
`d_F ∈ F(mid, mid)` and `d_G ∈ G(mid, mid)` to
`(F-action(d_F), G-action(d_G))` using the SAME
factorization `fact` for both components. But when
`F` and `G` are separately diag-determined, each
off-diagonal element may require a DIFFERENT
factorization, and the intersection of the diagonals
at a common midpoint may be empty.

Counterexample: Let `C` be the walking arrow
`{0, 1, f : 0 → 1}`. Let `F` have `F(0,0) = {a}`,
`F(1,1) = ∅`, `F(0,1) = {x}` (reached from `a` via
the initial factorization of `f`). Let `G` have
`G(0,0) = ∅`, `G(1,1) = {b}`, `G(0,1) = {y}`
(reached from `b` via the terminal factorization of
`f`). Then `F` and `G` are both diag-determined, but
`(x, y) ∈ (F × G)(0, 1)` cannot arise from any single
factorization: the initial factorization requires
`G(0,0)` (which is empty) and the terminal
factorization requires `F(1,1)` (which is empty).

This means `DiagDetProf` does NOT have binary products
inherited from `EndoProf`. The full subcategory may
still have products via a different construction, or
may lack them entirely.
-/

end DiagDetProducts

section DiagDetEqualizers

/-!
## Equalizers and diagonal determination

Diagonal determination does not imply
`EqualizerClosedUnderCov` or
`EqualizerClosedUnderContra`.

Given `x ∈ F(a, b)` with `F` diag-determined, `x`
arises from some `d ∈ F(c, c)` via a factorization of
`twArr tw` through `c`. Applying the covariant action
`(F.obj (op a)).map f` for `f : b ⟶ a` produces an
element of `F(a, a)`, but this element need not lie in
the diagonal equalizer `{d | α(a)(d) = β(a)(d)}`.

The covariant action composes functorially:
`(F.obj (op a)).map f (assemblyMapProf P tw ⟨fact, d⟩)`
= `(F.obj (op a)).map (fact.π ≫ f)
    ((F.map fact.ι.op).app fact.mid d)`.
This is an element of `F(a, a)` arising from `d` via
the factorization `(fact.ι, fact.π ≫ f)` of
`twArr tw ≫ f`, not of `𝟙 a`. Diag-determination at
`𝟙 a` tells us the result itself is reachable from
some `d' ∈ F(c', c')`, but `α` and `β` need not agree
on this `d'`.

Thus `EqualizerClosedUnderCov` and
`EqualizerClosedUnderContra` remain independent
conditions, not implied by diag-determination.
`DiagDetProf` has a terminal object but may lack both
products and equalizers from `EndoProf`.

However, `covClosed_of_covInjective` and
`contraClosed_of_contraInjective` show that when G's
actions away from the diagonal are injective, the two
closure conditions imply each other. With both
injectivity conditions, they are equivalent
(`equalizerClosure_iff_of_bothInjective`).
-/

end DiagDetEqualizers

section DiagonalizationMonad

/-!
## The diagonalization monad

The diagonalized density formula reduces the standard
density decomposition of a profunctor from four variables
to two: instead of decomposing `P(a, b)` using all
`P(c₁, c₂)` for varying `(c₁, c₂)`, it uses only
`P(c, c)` for varying `c`, glued via factorisations.

On the presheaf side, this is `Lan_iota ∘ iota*` where
`iota : I ↪ Tw(C)` is the full subcategory inclusion of
identity twisted arrows. The category `I` has
section-retraction pairs as morphisms: `Hom_I(id_c, id_d)`
consists of pairs `(α : d ⟶ c, β : c ⟶ d)` with
`α ≫ β = 𝟙 d`. There is no functor `C → Tw(C)` via
`c ↦ 𝟙 c` because a morphism `f : c → d` does not
determine both components.

A profunctor `P` is diagonally determined in the density
sense when the canonical map from `Lan_iota(iota* P)` to
`P` (the counit of the `Lan_iota ⊣ iota*` adjunction) is
an isomorphism.
-/

variable (C : Type u) [Category.{v} C]

/-- A twisted arrow is an identity when it is of the
form `twObjMk (𝟙 c)` for some object `c`. -/
def IsIdentityTwArr (tw : TwistedArrow C) : Prop :=
  ∃ (c : C), tw = twObjMk (𝟙 c)

/-- `IsIdentityTwArr` as an `ObjectProperty` on
`TwistedArrow C`. -/
def isIdentityTwArrProp :
    ObjectProperty (TwistedArrow C) :=
  IsIdentityTwArr C

/-- The full subcategory of `TwistedArrow C` on
identity arrows. Objects are twisted arrows of the
form `twObjMk (𝟙 c)`. Morphisms from `𝟙 c` to `𝟙 d`
are pairs `(α : d ⟶ c, β : c ⟶ d)` with
`α ≫ 𝟙 c ≫ β = 𝟙 d`, i.e., `α ≫ β = 𝟙 d`
(section-retraction pairs). -/
abbrev IdentityTwArr :=
  (isIdentityTwArrProp C).FullSubcategory

/-- The inclusion functor from the full subcategory of
identity twisted arrows into `TwistedArrow C`. -/
abbrev identityTwArrInclusion :
    IdentityTwArr C ⥤ TwistedArrow C :=
  (isIdentityTwArrProp C).ι

/-- The identity twisted arrow `𝟙 c` as an object of
`IdentityTwArr C`. -/
def identityTwArrObj (c : C) : IdentityTwArr C :=
  ⟨twObjMk (𝟙 c), ⟨c, rfl⟩⟩

variable {C}

/-- The decorated factorisation sigma type for a
Type-valued profunctor at a twisted arrow: pairs
`(fact, d)` with `fact` a factorisation of `twArr tw`
and `d ∈ P(fact.mid, fact.mid)`. -/
abbrev DecFactSigma
    (P : Cᵒᵖ ⥤ C ⥤ Type w₁)
    (tw : TwistedArrow C) :=
  (fact : Factorisation (twArr tw)) ×
    diagApp P fact.mid

/-- The kernel-pair relation on `DecFactSigma`:
two decorated factorisations are related when
`assemblyMapProf` sends them to the same element. -/
def diagRelation
    (P : Cᵒᵖ ⥤ C ⥤ Type w₁)
    (tw : TwistedArrow C)
    (x y : DecFactSigma P tw) : Prop :=
  assemblyMapProf P tw x = assemblyMapProf P tw y

theorem diagRelation_equiv
    (P : Cᵒᵖ ⥤ C ⥤ Type w₁)
    (tw : TwistedArrow C) :
    Equivalence (diagRelation P tw) where
  refl _ := rfl
  symm h := h.symm
  trans h₁ h₂ := h₁.trans h₂

/-- The setoid on `DecFactSigma` given by the
kernel pair of `assemblyMapProf`. -/
def diagSetoid
    (P : Cᵒᵖ ⥤ C ⥤ Type w₁)
    (tw : TwistedArrow C) :
    Setoid (DecFactSigma P tw) where
  r := diagRelation P tw
  iseqv := diagRelation_equiv P tw

/-- The diagonalization of a Type-valued profunctor at
a twisted arrow: the image of the assembly map. An
element of `P(twDom tw, twCod tw)` is in the
diagonalization when it arises from some diagonal
element transported along a factorisation. This is the
Type-level analogue of the pointwise left Kan extension
`Lan_iota(iota*(profOnTwArr P))` evaluated at `tw`. -/
def Diagonalization
    (P : Cᵒᵖ ⥤ C ⥤ Type w₁)
    (tw : TwistedArrow C) :=
  Set.range (assemblyMapProf P tw)

/-- The inclusion from the diagonalization into the
profunctor value. This is the counit of the
`Lan_iota ⊣ iota*` adjunction. -/
def diagInclusion
    (P : Cᵒᵖ ⥤ C ⥤ Type w₁)
    (tw : TwistedArrow C) :
    Diagonalization P tw →
      (P.obj (Opposite.op (twDom tw))).obj
        (twCod tw) :=
  Subtype.val

theorem diagInclusion_injective
    (P : Cᵒᵖ ⥤ C ⥤ Type w₁)
    (tw : TwistedArrow C) :
    Function.Injective (diagInclusion P tw) :=
  Subtype.val_injective

/-- `IsDiagDeterminedProf P` is equivalent to the
diagonalization inclusion being surjective at every
twisted arrow. -/
theorem isDiagDeterminedProf_iff_diagSurj
    (P : Cᵒᵖ ⥤ C ⥤ Type w₁) :
    IsDiagDeterminedProf P ↔
      ∀ (tw : TwistedArrow C),
        Function.Surjective (diagInclusion P tw) := by
  constructor
  · intro h tw y
    obtain ⟨x, hx⟩ := h tw y
    exact ⟨⟨y, x, hx⟩, rfl⟩
  · intro h tw y
    obtain ⟨⟨_, x, hx⟩, rfl⟩ := h tw y
    exact ⟨x, hx⟩

/-- The assembly map is natural with respect to twisted
arrow morphisms: the diagram
```
DecFactSigma P tw₁ --assemblyMap--> P(tw₁)
       |                               |
  (factorisationMapObj φ, id) (profOnTwArr P).map φ
       |                               |
       v                               v
DecFactSigma P tw₂ --assemblyMap--> P(tw₂)
```
commutes. -/
theorem assemblyMapProf_natural
    (P : Cᵒᵖ ⥤ C ⥤ Type w₁)
    {tw₁ tw₂ : TwistedArrow C}
    (φ : tw₁ ⟶ tw₂)
    (x : DecFactSigma P tw₁) :
    assemblyMapProf P tw₂
      ⟨factorisationMapObj φ x.1, x.2⟩ =
    (P.obj (Opposite.op (twDom tw₂))).map
        (twCodArr φ)
      ((P.map (twDomArr φ).op).app (twCod tw₁)
        (assemblyMapProf P tw₁ x)) := by
  simp only [assemblyMapProf, factorisationMapObj]
  rw [FunctorToTypes.map_comp_apply, op_comp,
    Functor.map_comp, NatTrans.comp_app,
    types_comp_apply]
  have h := congrFun
    ((P.map (twDomArr φ).op).naturality x.fst.π)
    ((P.map x.fst.ι.op).app x.fst.mid x.snd)
  simp only [types_comp_apply] at h
  exact congrArg
    ((P.obj (Opposite.op (twDom tw₂))).map
      (twCodArr φ)) h.symm

/-- The diagonalization is closed under the profunctor
action on twisted arrows: if `y` is in the image of
`assemblyMapProf P tw₁`, then the profunctor action
along `φ : tw₁ ⟶ tw₂` sends `y` into the image of
`assemblyMapProf P tw₂`. -/
theorem diag_closed_under_map
    (P : Cᵒᵖ ⥤ C ⥤ Type w₁)
    {tw₁ tw₂ : TwistedArrow C}
    (φ : tw₁ ⟶ tw₂)
    (y : (P.obj (Opposite.op (twDom tw₁))).obj
      (twCod tw₁))
    (hy : y ∈ Set.range (assemblyMapProf P tw₁)) :
    (P.obj (Opposite.op (twDom tw₂))).map
        (twCodArr φ)
      ((P.map (twDomArr φ).op).app (twCod tw₁) y)
    ∈ Set.range (assemblyMapProf P tw₂) := by
  obtain ⟨x, hx⟩ := hy
  exact ⟨⟨factorisationMapObj φ x.1, x.2⟩,
    by rw [assemblyMapProf_natural, hx]⟩

/-- The morphism map for the diagonalization functor:
transports an element of `Diagonalization P tw₁`
along `φ : tw₁ ⟶ tw₂` using the profunctor actions. -/
def diagMap
    (P : Cᵒᵖ ⥤ C ⥤ Type w₁)
    {tw₁ tw₂ : TwistedArrow C}
    (φ : tw₁ ⟶ tw₂) :
    Diagonalization P tw₁ →
      Diagonalization P tw₂ :=
  fun ⟨y, hy⟩ =>
    ⟨(P.obj (Opposite.op (twDom tw₂))).map
        (twCodArr φ)
      ((P.map (twDomArr φ).op).app (twCod tw₁) y),
    diag_closed_under_map P φ y hy⟩

theorem diagMap_id
    (P : Cᵒᵖ ⥤ C ⥤ Type w₁)
    (tw : TwistedArrow C)
    (x : Diagonalization P tw) :
    diagMap P (𝟙 tw) x = x := by
  obtain ⟨y, hy⟩ := x
  apply Subtype.ext
  simp only [diagMap, twCodArr_id, twDomArr_id,
    op_id, P.map_id, NatTrans.id_app,
    types_id_apply,
    (P.obj (Opposite.op (twDom tw))).map_id]

theorem diagMap_comp
    (P : Cᵒᵖ ⥤ C ⥤ Type w₁)
    {tw₁ tw₂ tw₃ : TwistedArrow C}
    (φ : tw₁ ⟶ tw₂) (ψ : tw₂ ⟶ tw₃)
    (x : Diagonalization P tw₁) :
    diagMap P (φ ≫ ψ) x =
    diagMap P ψ (diagMap P φ x) := by
  obtain ⟨y, hy⟩ := x
  apply Subtype.ext
  simp only [diagMap, twCodArr_comp, twDomArr_comp,
    op_comp, P.map_comp, NatTrans.comp_app,
    types_comp_apply,
    FunctorToTypes.map_comp_apply]
  have h := congrFun
    ((P.map (twDomArr ψ).op).naturality
      (twCodArr φ))
    ((P.map (twDomArr φ).op).app
      (twCod tw₁) y)
  simp only [types_comp_apply] at h
  exact congrArg
    ((P.obj (Opposite.op (twDom tw₃))).map
      (twCodArr ψ)) h.symm

/-- The diagonalization functor: a functor from
`TwistedArrow C` to `Type w₁` sending each twisted
arrow `tw` to the image of its assembly map. This is
the image of the counit of the `Lan_iota ⊣ iota*`
adjunction at `profOnTwArr P`, where `iota` is the
full subcategory inclusion of identity twisted arrows.
The left Kan extension `Lan_iota(iota*(profOnTwArr P))`
surjects onto `diagFunctor P` via the counit. -/
def diagFunctor (P : Cᵒᵖ ⥤ C ⥤ Type w₁) :
    TwistedArrow C ⥤ Type w₁ where
  obj tw := Diagonalization P tw
  map φ := diagMap P φ
  map_id tw := funext (diagMap_id P tw)
  map_comp φ ψ := funext (diagMap_comp P φ ψ)

/-- The assembly map at the initial factorisation of
`twArr tw` sends `d` to itself, since the initial
factorisation has `ι = 𝟙 (twDom tw)` and `π = twArr tw`,
and the contravariant action by `𝟙` is identity while
the covariant action by `twArr tw` takes
`P(twDom, twDom) → P(twDom, twCod)`. -/
theorem assemblyMapProf_initial
    (P : Cᵒᵖ ⥤ C ⥤ Type w₁)
    (tw : TwistedArrow C)
    (d : diagApp P (twDom tw)) :
    assemblyMapProf P tw
      ⟨Factorisation.initial, d⟩ =
    (P.obj (Opposite.op (twDom tw))).map
      (twArr tw) d := by
  simp only [assemblyMapProf, Factorisation.initial,
    op_id, P.map_id, NatTrans.id_app, types_id_apply]

/-- At an identity twisted arrow `twObjMk (𝟙 c)`, the
assembly map at the initial factorisation is the identity
on `P(c, c)`. -/
theorem assemblyMapProf_at_identity
    (P : Cᵒᵖ ⥤ C ⥤ Type w₁)
    (c : C) (d : diagApp P c) :
    assemblyMapProf P (twObjMk (𝟙 c))
      ⟨Factorisation.initial, d⟩ = d := by
  simp only [assemblyMapProf, Factorisation.initial,
    twObjMk_arr, op_id, P.map_id, NatTrans.id_app,
    types_id_apply]
  change (P.obj (Opposite.op c)).map (𝟙 c) d = d
  simp only [(P.obj (Opposite.op c)).map_id,
    types_id_apply]

/-- The unit map: embeds a diagonal element
`d ∈ P(c, c)` into the diagonalization at the identity
arrow `𝟙 c`, via the initial factorisation
`(mid = c, ι = 𝟙 c, π = 𝟙 c)`. -/
def diagUnit (P : Cᵒᵖ ⥤ C ⥤ Type w₁) (c : C)
    (d : diagApp P c) :
    Diagonalization P (twObjMk (𝟙 c)) :=
  ⟨d, ⟨Factorisation.initial, d⟩,
    assemblyMapProf_at_identity P c d⟩

theorem diagUnit_injective
    (P : Cᵒᵖ ⥤ C ⥤ Type w₁) (c : C) :
    Function.Injective (diagUnit P c) :=
  fun _ _ h => congrArg Subtype.val h

/-- A section-retraction factorisation step from
`x` to `y` in `DecFactSigma P tw`: there exist
morphisms `s : y.mid → x.mid` and `r : x.mid → y.mid`
forming a section-retraction (`s ≫ r = 𝟙`), compatible
with the factorisations, such that `y.2` is the
profunctor action of `(s, r)` on `x.2`. This is the
generating relation for the left Kan extension colimit
`Lan_iota(iota* profOnTwArr P)`, corresponding to
morphisms in
`CostructuredArrow (identityTwArrInclusion C) tw`. -/
def LanDiagStep
    (P : Cᵒᵖ ⥤ C ⥤ Type w₁)
    (tw : TwistedArrow C)
    (x y : DecFactSigma P tw) : Prop :=
  ∃ (s : y.1.mid ⟶ x.1.mid)
    (r : x.1.mid ⟶ y.1.mid),
    s ≫ r = 𝟙 y.1.mid ∧
    y.1.ι ≫ s = x.1.ι ∧
    r ≫ y.1.π = x.1.π ∧
    y.2 = (P.obj (Opposite.op y.1.mid)).map r
      ((P.map s.op).app x.1.mid x.2)

/-- The assembly map respects `LanDiagStep`: if two
decorated factorisations are related by a
section-retraction step, they have the same image
under the assembly map. -/
theorem assemblyMapProf_respects_lanDiagStep
    (P : Cᵒᵖ ⥤ C ⥤ Type w₁)
    {tw : TwistedArrow C}
    {x y : DecFactSigma P tw}
    (h : LanDiagStep P tw x y) :
    assemblyMapProf P tw x =
    assemblyMapProf P tw y := by
  obtain ⟨s, r, _, hι, hπ, helem⟩ := h
  simp only [assemblyMapProf]
  rw [← hπ, FunctorToTypes.map_comp_apply,
    ← hι, op_comp, P.map_comp, NatTrans.comp_app,
    types_comp_apply]
  apply congrArg
    ((P.obj (Opposite.op (twDom tw))).map y.1.π)
  rw [helem]
  have h := congrFun
    ((P.map y.1.ι.op).naturality r)
    ((P.map s.op).app x.1.mid x.2)
  simp only [types_comp_apply] at h
  exact h.symm

/-- The setoid on `DecFactSigma P tw` whose equivalence
relation is generated by `LanDiagStep`: two decorated
factorisations are equivalent iff they are connected
by a chain of section-retraction steps (in either
direction). The quotient by this setoid is the left
Kan extension `Lan_iota(iota* profOnTwArr P)(tw)`. -/
instance lanDiagSetoid
    (P : Cᵒᵖ ⥤ C ⥤ Type w₁)
    (tw : TwistedArrow C) :
    Setoid (DecFactSigma P tw) :=
  Relation.EqvGen.setoid (LanDiagStep P tw)

/-- The assembly map respects the equivalence relation
generated by `LanDiagStep`. -/
theorem assemblyMapProf_respects_lanDiagSetoid
    (P : Cᵒᵖ ⥤ C ⥤ Type w₁)
    {tw : TwistedArrow C}
    {x y : DecFactSigma P tw}
    (h : Relation.EqvGen
      (LanDiagStep P tw) x y) :
    assemblyMapProf P tw x =
    assemblyMapProf P tw y := by
  induction h with
  | rel _ _ hr =>
    exact assemblyMapProf_respects_lanDiagStep P hr
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- The pointwise left Kan extension
`Lan_iota(iota* profOnTwArr P)(tw)`, computed as the
quotient of decorated factorisations by the equivalence
relation generated by section-retraction steps. -/
def LanDiag (P : Cᵒᵖ ⥤ C ⥤ Type w₁)
    (tw : TwistedArrow C) :=
  Quotient (lanDiagSetoid P tw)

/-- The counit of the `Lan_iota ⊣ iota*` adjunction at
`profOnTwArr P`: a map from the Kan extension quotient
`LanDiag P tw` to `P(twDom tw, twCod tw)`, defined by
descending the assembly map to the quotient. -/
def lanDiagCounit (P : Cᵒᵖ ⥤ C ⥤ Type w₁)
    (tw : TwistedArrow C) :
    LanDiag P tw →
    (P.obj (Opposite.op (twDom tw))).obj
      (twCod tw) :=
  Quotient.lift (assemblyMapProf P tw)
    (fun _ _ h =>
      assemblyMapProf_respects_lanDiagSetoid P h)

/-- Transport a decorated factorisation along a twisted
arrow morphism. Since `factorisationMapObj` preserves
the midpoint, the diagonal element is unchanged. -/
def lanDiagMapSigma (P : Cᵒᵖ ⥤ C ⥤ Type w₁)
    {tw₁ tw₂ : TwistedArrow C} (φ : tw₁ ⟶ tw₂)
    (x : DecFactSigma P tw₁) :
    DecFactSigma P tw₂ :=
  ⟨factorisationMapObj φ x.1, x.2⟩

/-- `lanDiagMapSigma` preserves the `LanDiagStep`
relation: a section-retraction step in `tw₁` transports
to a section-retraction step in `tw₂`. -/
theorem lanDiagMapSigma_respects_lanDiagStep
    (P : Cᵒᵖ ⥤ C ⥤ Type w₁)
    {tw₁ tw₂ : TwistedArrow C} (φ : tw₁ ⟶ tw₂)
    {x y : DecFactSigma P tw₁}
    (h : LanDiagStep P tw₁ x y) :
    LanDiagStep P tw₂
      (lanDiagMapSigma P φ x)
      (lanDiagMapSigma P φ y) := by
  obtain ⟨s, r, hsr, hι, hπ, helem⟩ := h
  exact ⟨s, r, hsr, by
    simp only [lanDiagMapSigma, factorisationMapObj,
      Category.assoc, hι], by
    simp only [lanDiagMapSigma, factorisationMapObj,
      ← Category.assoc, hπ],
    helem⟩

/-- `lanDiagMapSigma` preserves the equivalence closure
of `LanDiagStep`. -/
theorem lanDiagMapSigma_respects_lanDiagSetoid
    (P : Cᵒᵖ ⥤ C ⥤ Type w₁)
    {tw₁ tw₂ : TwistedArrow C} (φ : tw₁ ⟶ tw₂)
    {x y : DecFactSigma P tw₁}
    (h : Relation.EqvGen
      (LanDiagStep P tw₁) x y) :
    Relation.EqvGen (LanDiagStep P tw₂)
      (lanDiagMapSigma P φ x)
      (lanDiagMapSigma P φ y) := by
  induction h with
  | rel _ _ hr =>
    exact Relation.EqvGen.rel _ _
      (lanDiagMapSigma_respects_lanDiagStep P φ hr)
  | refl => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ =>
    exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

/-- The functorial action of the Kan extension on
twisted arrow morphisms, defined by lifting the
sigma-level transport to the quotient. -/
def lanDiagMap (P : Cᵒᵖ ⥤ C ⥤ Type w₁)
    {tw₁ tw₂ : TwistedArrow C} (φ : tw₁ ⟶ tw₂) :
    LanDiag P tw₁ → LanDiag P tw₂ :=
  Quotient.map (lanDiagMapSigma P φ)
    (fun _ _ h =>
      lanDiagMapSigma_respects_lanDiagSetoid P φ h)

private theorem factorisationMapObj_id
    {tw : TwistedArrow C}
    (fact : Factorisation (twArr tw)) :
    factorisationMapObj (𝟙 tw) fact = fact := by
  obtain ⟨mid, ι, π, _⟩ := fact
  unfold factorisationMapObj
  simp only [twDomArr_id, twCodArr_id,
    Category.id_comp, Category.comp_id]

private theorem factorisationMapObj_comp
    {tw₁ tw₂ tw₃ : TwistedArrow C}
    (φ : tw₁ ⟶ tw₂) (ψ : tw₂ ⟶ tw₃)
    (fact : Factorisation (twArr tw₁)) :
    factorisationMapObj (φ ≫ ψ) fact =
    factorisationMapObj ψ
      (factorisationMapObj φ fact) := by
  cases fact
  simp only [factorisationMapObj,
    twDomArr_comp, twCodArr_comp, Category.assoc]

theorem lanDiagMapSigma_id
    (P : Cᵒᵖ ⥤ C ⥤ Type w₁)
    (tw : TwistedArrow C)
    (x : DecFactSigma P tw) :
    lanDiagMapSigma P (𝟙 tw) x = x := by
  obtain ⟨fact, d⟩ := x
  exact Sigma.ext
    (factorisationMapObj_id fact) HEq.rfl

theorem lanDiagMapSigma_comp
    (P : Cᵒᵖ ⥤ C ⥤ Type w₁)
    {tw₁ tw₂ tw₃ : TwistedArrow C}
    (φ : tw₁ ⟶ tw₂) (ψ : tw₂ ⟶ tw₃)
    (x : DecFactSigma P tw₁) :
    lanDiagMapSigma P (φ ≫ ψ) x =
    lanDiagMapSigma P ψ
      (lanDiagMapSigma P φ x) := by
  obtain ⟨fact, d⟩ := x
  exact Sigma.ext
    (factorisationMapObj_comp φ ψ fact) HEq.rfl

theorem lanDiagMap_id
    (P : Cᵒᵖ ⥤ C ⥤ Type w₁)
    (tw : TwistedArrow C)
    (q : LanDiag P tw) :
    lanDiagMap P (𝟙 tw) q = q := by
  induction q using Quotient.inductionOn with
  | h x =>
    simp only [lanDiagMap, Quotient.map_mk,
      lanDiagMapSigma_id]

theorem lanDiagMap_comp
    (P : Cᵒᵖ ⥤ C ⥤ Type w₁)
    {tw₁ tw₂ tw₃ : TwistedArrow C}
    (φ : tw₁ ⟶ tw₂) (ψ : tw₂ ⟶ tw₃)
    (q : LanDiag P tw₁) :
    lanDiagMap P (φ ≫ ψ) q =
    lanDiagMap P ψ (lanDiagMap P φ q) := by
  induction q using Quotient.inductionOn with
  | h x =>
    simp only [lanDiagMap, Quotient.map_mk,
      lanDiagMapSigma_comp]

/-- The left Kan extension functor
`Lan_iota(iota* profOnTwArr P) : TwistedArrow C ⥤ Type w₁`,
computed as the quotient of decorated factorisations by
the equivalence relation generated by section-retraction
steps. -/
def lanDiagFunctor (P : Cᵒᵖ ⥤ C ⥤ Type w₁) :
    TwistedArrow C ⥤ Type (max u v w₁) where
  obj tw := LanDiag P tw
  map φ := lanDiagMap P φ
  map_id tw := funext (lanDiagMap_id P tw)
  map_comp φ ψ := funext (lanDiagMap_comp P φ ψ)

/-- Naturality of `lanDiagCounit`: the counit commutes
with the functorial actions on the Kan extension quotient
and the profunctor. -/
theorem lanDiagCounit_natural
    (P : Cᵒᵖ ⥤ C ⥤ Type w₁)
    {tw₁ tw₂ : TwistedArrow C}
    (φ : tw₁ ⟶ tw₂)
    (q : LanDiag P tw₁) :
    lanDiagCounit P tw₂ (lanDiagMap P φ q) =
    (P.obj (Opposite.op (twDom tw₂))).map
        (twCodArr φ)
      ((P.map (twDomArr φ).op).app (twCod tw₁)
        (lanDiagCounit P tw₁ q)) := by
  induction q using Quotient.inductionOn with
  | h x =>
    simp only [lanDiagCounit, lanDiagMap,
      Quotient.map_mk, Quotient.lift_mk]
    exact assemblyMapProf_natural P φ x

/-- The counit factors through the diagonalization:
every element in the image of `lanDiagCounit` lies in
`Diagonalization P tw`. -/
def lanDiagCounitFactored (P : Cᵒᵖ ⥤ C ⥤ Type w₁)
    (tw : TwistedArrow C) :
    LanDiag P tw → Diagonalization P tw :=
  Quotient.lift
    (fun x => ⟨assemblyMapProf P tw x, x, rfl⟩)
    (fun _ _ h => Subtype.ext
      (assemblyMapProf_respects_lanDiagSetoid P h))

theorem isDiagDeterminedProf_iff_lanDiagCounit_surj
    (P : Cᵒᵖ ⥤ C ⥤ Type w₁) :
    IsDiagDeterminedProf P ↔
    ∀ (tw : TwistedArrow C),
      Function.Surjective (lanDiagCounit P tw) := by
  constructor
  · intro hP tw y
    obtain ⟨x, hx⟩ := hP tw y
    exact ⟨Quotient.mk _ x, by
      simp only [lanDiagCounit, Quotient.lift_mk]
      exact hx⟩
  · intro hL tw y
    obtain ⟨q, hq⟩ := hL tw y
    induction q using Quotient.inductionOn with
    | h x =>
      exact ⟨x, by
        simp only [lanDiagCounit,
          Quotient.lift_mk] at hq
        exact hq⟩

/-- The restriction of the profunctor-on-twisted-arrows
to the full subcategory of identity twisted arrows, with
`ULift` to match the universe level of `lanDiagFunctor`.
Sends `(twObjMk (𝟙 c), _)` to
`ULift.{max u v} (P(c, c))`. -/
def iotaRestriction (P : Cᵒᵖ ⥤ C ⥤ Type w₁) :
    IdentityTwArr C ⥤ Type (max u v w₁) where
  obj itw :=
    ULift.{max u v}
      ((P.obj (Opposite.op (twDom itw.1))).obj
        (twCod itw.1))
  map {itw₁ itw₂} φ x :=
    ULift.up
      ((P.obj (Opposite.op (twDom itw₂.1))).map
          (twCodArr φ.hom)
        ((P.map (twDomArr φ.hom).op).app
          (twCod itw₁.1) x.down))
  map_id itw := by
    ext ⟨x⟩
    dsimp
    rw [twDomArr_id, twCodArr_id]
    simp only [op_id, P.map_id, NatTrans.id_app,
      types_id_apply, (P.obj _).map_id]
  map_comp {itw₁ itw₂ itw₃} φ ψ := by
    ext ⟨x⟩
    dsimp
    rw [twDomArr_comp, twCodArr_comp]
    simp only [op_comp, P.map_comp,
      NatTrans.comp_app, types_comp_apply,
      FunctorToTypes.map_comp_apply]
    have h := congrFun
      ((P.map (twDomArr ψ.hom).op).naturality
        (twCodArr φ.hom))
      ((P.map (twDomArr φ.hom).op).app
        (twCod itw₁.1) x)
    simp only [types_comp_apply] at h
    exact congrArg
      ((P.obj (Opposite.op (twDom itw₃.1))).map
        (twCodArr ψ.hom)) h.symm

/-- For an identity twisted arrow `itw`, the equality
`twDom itw.1 = twCod itw.1`. -/
theorem identityTwArr_dom_eq_cod
    (itw : IdentityTwArr C) :
    twDom itw.1 = twCod itw.1 := by
  obtain ⟨c, hc⟩ := itw.2
  simp only [hc, twObjMk_dom, twObjMk_cod]

/-- The component of the unit at an identity twisted
arrow: sends `ULift.up d` where
`d ∈ P(twDom itw, twCod itw)` to the quotient class
of `⟨Factorisation.initial, d'⟩` in
`LanDiag P itw`. Here `d'` is `d` transported along
the equality `twDom itw = twCod itw`. -/
def lanDiagUnitApp
    (P : Cᵒᵖ ⥤ C ⥤ Type w₁)
    (itw : IdentityTwArr C) :
    (iotaRestriction P).obj itw →
    (lanDiagFunctor P).obj
      ((identityTwArrInclusion C).obj itw) :=
  fun ⟨d⟩ =>
    Quotient.mk _
      ⟨Factorisation.initial,
       (P.obj (Opposite.op (twDom itw.1))).map
         (eqToHom
           (identityTwArr_dom_eq_cod itw).symm)
         d⟩

theorem lanDiagUnitApp_natural
    (P : Cᵒᵖ ⥤ C ⥤ Type w₁)
    {itw₁ itw₂ : IdentityTwArr C}
    (φ : itw₁ ⟶ itw₂)
    (x : (iotaRestriction P).obj itw₁) :
    (lanDiagFunctor P).map
        ((identityTwArrInclusion C).map φ)
      (lanDiagUnitApp P itw₁ x) =
    lanDiagUnitApp P itw₂
      ((iotaRestriction P).map φ x) := by
  obtain ⟨d⟩ := x
  obtain ⟨tw₁, c₁, hc₁⟩ := itw₁
  obtain ⟨tw₂, c₂, hc₂⟩ := itw₂
  subst hc₁; subst hc₂
  dsimp only [lanDiagUnitApp, lanDiagFunctor,
    lanDiagMap, iotaRestriction,
    identityTwArrInclusion, isIdentityTwArrProp,
    ObjectProperty.ι, lanDiagMapSigma,
    identityTwArr_dom_eq_cod]
  simp only [twObjMk_dom, twObjMk_cod,
    eqToHom_refl, (P.obj _).map_id,
    types_id_apply, Quotient.map_mk]
  apply Quotient.sound
  apply Relation.EqvGen.rel
  dsimp only [lanDiagMapSigma, factorisationMapObj,
    Factorisation.initial, inducedFunctor]
  simp only [twObjMk_dom, twObjMk_cod, twObjMk_arr]
  refine ⟨twDomArr φ.hom, twCodArr φ.hom,
    ?_, ?_, ?_, rfl⟩
  · dsimp
    have h := twHomComm φ.hom
    dsimp at h
    rw [show twArr (twObjMk (𝟙 c₁)) =
        𝟙 (twCod (twObjMk (𝟙 c₁))) from rfl] at h
    have eq1 : 𝟙 (twCod (twObjMk (𝟙 c₁))) ≫
        twCodArr φ.hom = twCodArr φ.hom :=
      Category.id_comp _
    rw [eq1, twObjMk_arr] at h
    exact h
  · dsimp
    simp only [Category.id_comp, Category.comp_id]
  · dsimp
    simp only [Category.id_comp, Category.comp_id]

/-- The unit of the diagonalization monad as a
natural transformation:
`iotaRestriction P ⟶
  identityTwArrInclusion C ⋙ lanDiagFunctor P`.
Each component sends `ULift.up d` to the equivalence
class of `⟨Factorisation.initial, d'⟩`. -/
def lanDiagUnit (P : Cᵒᵖ ⥤ C ⥤ Type w₁) :
    iotaRestriction P ⟶
    (identityTwArrInclusion C) ⋙
      lanDiagFunctor P where
  app := lanDiagUnitApp P
  naturality _ _ φ := by
    ext x
    exact (lanDiagUnitApp_natural P φ x).symm

/-- The left extension of `iotaRestriction P` along
`identityTwArrInclusion C`, given by `lanDiagFunctor P`
with unit `lanDiagUnit P`. -/
def lanDiagLeftExt (P : Cᵒᵖ ⥤ C ⥤ Type w₁) :
    Functor.LeftExtension
      (identityTwArrInclusion C)
      (iotaRestriction P) :=
  Functor.LeftExtension.mk
    (lanDiagFunctor P) (lanDiagUnit P)

/-- A factorisation of `twArr tw` through a midpoint
`c` gives a morphism `twObjMk (𝟙 c) ⟶ tw` in
`TwistedArrow C`. -/
def factorisationToTwMorph
    (tw : TwistedArrow C)
    (fact : Factorisation (twArr tw)) :
    twObjMk (𝟙 fact.mid) ⟶ tw :=
  twHomMk fact.ι fact.π (by
    rw [show twArr (twObjMk (𝟙 fact.mid)) =
        𝟙 (twCod (twObjMk (𝟙 fact.mid))) from rfl]
    have eq1 :
        𝟙 (twCod (twObjMk (𝟙 fact.mid))) ≫
        fact.π = fact.π :=
      Category.id_comp _
    rw [eq1]
    exact fact.ι_π)

/-- A factorisation gives a costructured arrow from
the corresponding identity twisted arrow to `tw`. -/
def factorisationToCostructuredArrow
    (tw : TwistedArrow C)
    (fact : Factorisation (twArr tw)) :
    CostructuredArrow
      (identityTwArrInclusion C) tw :=
  CostructuredArrow.mk
    (Y := ⟨twObjMk (𝟙 fact.mid),
      fact.mid, rfl⟩)
    (show (identityTwArrInclusion C).obj
        ⟨twObjMk (𝟙 fact.mid), fact.mid, rfl⟩
        ⟶ tw
     from factorisationToTwMorph tw fact)

/-- For a cocone over the diagram
`CostructuredArrow.proj L tw ⋙ iotaRestriction P`,
a single `LanDiagStep` from `x` to `y` implies that
the cocone evaluations at the corresponding
costructured arrows agree. The proof constructs the
costructured arrow morphism from the
section-retraction data and applies cocone
naturality. -/
private theorem coconeApp_eq_of_lanDiagStep
    (P : Cᵒᵖ ⥤ C ⥤ Type w₁)
    {tw : TwistedArrow C}
    (s : Limits.Cocone
      (CostructuredArrow.proj
        (identityTwArrInclusion C) tw ⋙
        iotaRestriction P))
    {x y : DecFactSigma P tw}
    (h : LanDiagStep P tw x y) :
    s.ι.app
        (factorisationToCostructuredArrow tw x.1)
      (ULift.up x.2) =
    s.ι.app
        (factorisationToCostructuredArrow tw y.1)
      (ULift.up y.2) := by
  obtain ⟨sec, ret, hsr, hι, hπ, helem⟩ := h
  have nat := congrFun
    (s.ι.naturality
      (CostructuredArrow.homMk
        (show
          (factorisationToCostructuredArrow
            tw x.1).left ⟶
          (factorisationToCostructuredArrow
            tw y.1).left
         from ⟨twHomMk sec ret (by
           dsimp [factorisationToCostructuredArrow]
           simp [hsr])⟩)
        (by
          apply twHom_ext
          · simp only [twDomArr_comp]
            exact hι
          · simp only [twCodArr_comp]
            exact hπ)))
    (ULift.up x.2)
  simp only [types_comp_apply,
    Functor.const_obj_map, types_id_apply] at nat
  rw [← nat]
  apply congrArg
    (s.ι.app
      (factorisationToCostructuredArrow tw y.1))
  dsimp [Functor.comp_map,
    CostructuredArrow.proj_map,
    iotaRestriction,
    factorisationToCostructuredArrow,
    identityTwArrInclusion,
    isIdentityTwArrProp, ObjectProperty.ι,
    inducedFunctor]
  exact congrArg ULift.up helem.symm

/-- Extension of `coconeApp_eq_of_lanDiagStep` to the
full equivalence closure `EqvGen (LanDiagStep)`. -/
private theorem coconeApp_eq_of_lanDiagSetoid
    (P : Cᵒᵖ ⥤ C ⥤ Type w₁)
    {tw : TwistedArrow C}
    (s : Limits.Cocone
      (CostructuredArrow.proj
        (identityTwArrInclusion C) tw ⋙
        iotaRestriction P))
    {x y : DecFactSigma P tw}
    (h : Relation.EqvGen
      (LanDiagStep P tw) x y) :
    s.ι.app
        (factorisationToCostructuredArrow tw x.1)
      (ULift.up x.2) =
    s.ι.app
        (factorisationToCostructuredArrow tw y.1)
      (ULift.up y.2) := by
  induction h with
  | rel _ _ hr =>
    exact coconeApp_eq_of_lanDiagStep P s hr
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ =>
    exact ih₁.trans ih₂

/-- The left Kan extension `lanDiagLeftExt P` is
pointwise: for each `tw : TwistedArrow C`, the
cocone `(lanDiagLeftExt P).coconeAt tw` is a
colimit. The colimit property holds because:
- `desc`: elements of `LanDiag P tw` (quotient of
  decorated factorisations) map to any cocone point
  via `Quotient.lift`;
- `fac`: the cocone leg at `g` sends each element
  to the same quotient class as the corresponding
  decorated factorisation;
- `uniq`: any map from `LanDiag P tw` factoring
  through the cocone must agree with `desc` on each
  quotient representative. -/
def lanDiag_isPointwiseLan
    (P : Cᵒᵖ ⥤ C ⥤ Type w₁) :
    Functor.LeftExtension.IsPointwiseLeftKanExtension
      (lanDiagLeftExt P) := by
  intro tw
  exact
    { desc := fun s =>
        Quotient.lift
          (fun x =>
            s.ι.app
              (factorisationToCostructuredArrow
                tw x.1)
              (ULift.up x.2))
          (fun _ _ h =>
            coconeApp_eq_of_lanDiagSetoid P s h)
      fac := fun s g => by
        obtain ⟨⟨_, ⟨c, rfl⟩⟩, ⟨⟨⟩⟩, ghom⟩ := g
        ext ⟨d⟩
        simp only [types_comp_apply]
        dsimp only [
          Functor.LeftExtension.coconeAt,
          lanDiagLeftExt,
          Functor.LeftExtension.mk]
        simp only [StructuredArrow.mk_right,
          StructuredArrow.mk_hom_eq_self,
          types_comp_apply]
        dsimp only [lanDiagUnit, lanDiagFunctor,
          lanDiagUnitApp, lanDiagMap,
          identityTwArr_dom_eq_cod]
        simp only [Quotient.map_mk,
          Quotient.lift_mk]
        dsimp only [lanDiagMapSigma,
          factorisationToCostructuredArrow,
          factorisationToTwMorph,
          factorisationMapObj,
          Factorisation.initial,
          identityTwArrInclusion,
          isIdentityTwArrProp,
          ObjectProperty.ι, inducedFunctor,
          CostructuredArrow.mk]
        simp only [twObjMk_dom, twObjMk_cod,
          twObjMk_arr,
          eqToHom_refl, (P.obj _).map_id,
          types_id_apply]
        convert rfl using 3
        exact twHom_ext _ _
          (Category.comp_id _).symm
          (Category.id_comp _).symm
      uniq := fun s m hm => by
        funext q
        exact Quotient.inductionOn q fun
          ⟨fact, d⟩ => by
          simp only [Quotient.lift_mk]
          have h := congrFun
            (hm (factorisationToCostructuredArrow
              tw fact))
            (ULift.up d)
          simp only [types_comp_apply] at h
          rw [← h]
          congr 1
          dsimp only [
            Functor.LeftExtension.coconeAt,
            lanDiagLeftExt,
            Functor.LeftExtension.mk]
          simp only [StructuredArrow.mk_right,
            StructuredArrow.mk_hom_eq_self,
            types_comp_apply]
          dsimp only [lanDiagUnit, lanDiagFunctor,
            lanDiagUnitApp, lanDiagMap,
            identityTwArr_dom_eq_cod]
          simp only [Quotient.map_mk]
          dsimp only [lanDiagMapSigma,
            factorisationToCostructuredArrow,
            factorisationToTwMorph,
            factorisationMapObj,
            Factorisation.initial,
            identityTwArrInclusion,
            isIdentityTwArrProp,
            ObjectProperty.ι, inducedFunctor,
            CostructuredArrow.mk]
          simp only [twObjMk_dom, twObjMk_cod,
            twObjMk_arr,
            twHomMk_domArr, twHomMk_codArr,
            eqToHom_refl, (P.obj _).map_id,
            types_id_apply]
          convert rfl using 3
          obtain ⟨_, _, _, _⟩ := fact
          simp [Category.comp_id,
            Category.id_comp] }

/-- At an identity arrow `twObjMk (𝟙 c)`, every
decorated factorisation `⟨fact, d⟩` is related by a
single `LanDiagStep` to
`⟨initial, assemblyMapProf P _ ⟨fact, d⟩⟩`. The
section-retraction pair is `(fact.ι, fact.π)`, which
satisfies `fact.ι ≫ fact.π = 𝟙 c` since `fact`
factorises `𝟙 c`. -/
theorem lanDiagStep_to_initial_at_identity
    (P : Cᵒᵖ ⥤ C ⥤ Type w₁) (c : C)
    (x : DecFactSigma P (twObjMk (𝟙 c))) :
    LanDiagStep P (twObjMk (𝟙 c)) x
      ⟨Factorisation.initial,
       assemblyMapProf P (twObjMk (𝟙 c)) x⟩ := by
  obtain ⟨fact, d⟩ := x
  refine ⟨fact.ι, fact.π, ?_, ?_, ?_, ?_⟩
  · simp only [Factorisation.initial]
    exact fact.ι_π
  · simp only [Factorisation.initial,
      Category.id_comp]
  · simp only [Factorisation.initial, twObjMk_arr]
    exact Category.comp_id _
  · simp only [Factorisation.initial, twObjMk_arr,
      assemblyMapProf]

/-- The inverse of the unit at an identity twisted
arrow: sends a quotient element
`q ∈ LanDiag P (twObjMk (𝟙 c))` to
`ULift.up (assemblyMapProf P _ q')` where `q'` is any
representative of `q`. Well-defined since the assembly
map respects the equivalence relation. -/
def lanDiagUnitInvApp
    (P : Cᵒᵖ ⥤ C ⥤ Type w₁) (c : C) :
    LanDiag P (twObjMk (𝟙 c)) →
    (iotaRestriction P).obj
      (identityTwArrObj C c) :=
  Quotient.lift
    (fun x => ULift.up
      (assemblyMapProf P (twObjMk (𝟙 c)) x))
    (fun _ _ h => congrArg ULift.up
      (assemblyMapProf_respects_lanDiagSetoid
        P h))

/-- Left inverse: the inverse composed with the unit
is the identity on
`(iotaRestriction P).obj (identityTwArrObj C c)`. -/
theorem lanDiagUnitInvApp_comp_unitApp
    (P : Cᵒᵖ ⥤ C ⥤ Type w₁) (c : C)
    (x : (iotaRestriction P).obj
      (identityTwArrObj C c)) :
    lanDiagUnitInvApp P c
      (lanDiagUnitApp P (identityTwArrObj C c) x)
    = x := by
  obtain ⟨d⟩ := x
  simp only [lanDiagUnitApp, lanDiagUnitInvApp,
    identityTwArrObj, twObjMk_dom,
    twObjMk_cod, eqToHom_refl,
    (P.obj _).map_id, types_id_apply]
  exact congrArg ULift.up
    (assemblyMapProf_at_identity P c d)

/-- Right inverse: the unit composed with the inverse
is the identity on `LanDiag P (twObjMk (𝟙 c))`. For
each representative `⟨fact, d⟩`, the composition sends
it to `⟦⟨initial, assemblyMapProf(fact, d)⟩⟧`, which
equals `⟦⟨fact, d⟩⟧` by `lanDiagStep_to_initial_at_identity`. -/
theorem lanDiagUnitApp_comp_invApp
    (P : Cᵒᵖ ⥤ C ⥤ Type w₁) (c : C)
    (q : LanDiag P (twObjMk (𝟙 c))) :
    lanDiagUnitApp P (identityTwArrObj C c)
      (lanDiagUnitInvApp P c q)
    = q := by
  induction q using Quotient.inductionOn with
  | h x =>
    obtain ⟨fact, d⟩ := x
    simp only [lanDiagUnitInvApp, lanDiagUnitApp,
      Quotient.lift_mk, identityTwArrObj,
      twObjMk_dom, twObjMk_cod, eqToHom_refl,
      (P.obj _).map_id, types_id_apply]
    exact (Quotient.sound
      (Relation.EqvGen.rel _ _
        (lanDiagStep_to_initial_at_identity
          P c ⟨fact, d⟩))).symm

/-- The unit of the Kan extension is a bijection at
each identity twisted arrow. This is the standard
property of Kan extensions along fully faithful
functors: `iota* ∘ Lan_iota ≅ id`. -/
theorem lanDiagUnitApp_bijective
    (P : Cᵒᵖ ⥤ C ⥤ Type w₁) (c : C) :
    Function.Bijective
      (lanDiagUnitApp P
        (identityTwArrObj C c)) :=
  ⟨fun _ _ h =>
    (lanDiagUnitInvApp_comp_unitApp P c _).symm.trans
      (congrArg (lanDiagUnitInvApp P c) h |>.trans
        (lanDiagUnitInvApp_comp_unitApp P c _)),
   fun q => ⟨lanDiagUnitInvApp P c q,
    lanDiagUnitApp_comp_invApp P c q⟩⟩

section NotLeftExact

variable {a b : C} (f : a ⟶ b)

/-- A `LanDiagStep` from an initial-based element to
a terminal-based element at `twObjMk f` yields an
`IsIso f`. The step provides `s : b → a` and
`r : a → b` with `s ≫ r = 𝟙 b`, `f ≫ s = 𝟙 a`,
and `r = f`, from which `f ≫ s = 𝟙 a` and
`s ≫ f = 𝟙 b`. -/
theorem isIso_of_lanDiagStep_initial_terminal
    (P : Cᵒᵖ ⥤ C ⥤ Type w₁)
    {d₁ : diagApp P a} {d₂ : diagApp P b}
    (h : LanDiagStep P (twObjMk f)
      ⟨Factorisation.initial, d₁⟩
      ⟨Factorisation.terminal, d₂⟩) :
    IsIso f := by
  obtain ⟨s, r, hsr, hι, hπ, _⟩ := h
  simp only [Factorisation.terminal,
    Factorisation.initial, twObjMk_arr] at hι
  simp only [Factorisation.terminal,
    Factorisation.initial, twObjMk_arr] at hπ
  simp only [Factorisation.terminal] at hsr
  have hr : r = f := by
    rw [Category.comp_id] at hπ
    exact hπ
  rw [hr] at hsr
  exact ⟨⟨s, hι, hsr⟩⟩

/-- The reverse direction: a `LanDiagStep` from a
terminal-based element to an initial-based element
also yields `IsIso f`. The step provides
`s : a → b` with `s = f` and `r : b → a` with
`r ≫ f = 𝟙 a` and `f ≫ r = 𝟙 b`. -/
theorem isIso_of_lanDiagStep_terminal_initial
    (P : Cᵒᵖ ⥤ C ⥤ Type w₁)
    {d₁ : diagApp P b} {d₂ : diagApp P a}
    (h : LanDiagStep P (twObjMk f)
      ⟨Factorisation.terminal, d₁⟩
      ⟨Factorisation.initial, d₂⟩) :
    IsIso f := by
  obtain ⟨s, r, hsr, hι, hπ, _⟩ := h
  simp only [Factorisation.initial,
    Factorisation.terminal, twObjMk_arr,
    twObjMk_dom, twObjMk_cod] at hι
  simp only [Factorisation.initial,
    Factorisation.terminal, twObjMk_arr,
    twObjMk_dom, twObjMk_cod] at hπ
  simp only [Factorisation.initial,
    twObjMk_dom] at hsr
  rw [Category.id_comp] at hι
  rw [hι] at hsr
  exact ⟨⟨r, hsr, hπ⟩⟩

end NotLeftExact

section ProductComparison

variable (P Q : Cᵒᵖ ⥤ C ⥤ Type w₁)

/-- A `LanDiagStep` on `prodEndoProf P Q` induces a
`LanDiagStep` on the first component `P`. -/
theorem lanDiagStep_fst
    {tw : TwistedArrow C}
    {x y : DecFactSigma (prodEndoProf P Q) tw}
    (h : LanDiagStep (prodEndoProf P Q) tw x y) :
    LanDiagStep P tw
      ⟨x.1, x.2.1⟩ ⟨y.1, y.2.1⟩ := by
  obtain ⟨s, r, hsr, hι, hπ, helem⟩ := h
  exact ⟨s, r, hsr, hι, hπ,
    congrArg Prod.fst helem⟩

/-- A `LanDiagStep` on `prodEndoProf P Q` induces a
`LanDiagStep` on the second component `Q`. -/
theorem lanDiagStep_snd
    {tw : TwistedArrow C}
    {x y : DecFactSigma (prodEndoProf P Q) tw}
    (h : LanDiagStep (prodEndoProf P Q) tw x y) :
    LanDiagStep Q tw
      ⟨x.1, x.2.2⟩ ⟨y.1, y.2.2⟩ := by
  obtain ⟨s, r, hsr, hι, hπ, helem⟩ := h
  exact ⟨s, r, hsr, hι, hπ,
    congrArg Prod.snd helem⟩

/-- The equivalence closure of `LanDiagStep` on
`prodEndoProf P Q` induces the same on `P`. -/
private theorem lanDiagSetoid_fst
    {tw : TwistedArrow C}
    {x y : DecFactSigma (prodEndoProf P Q) tw}
    (h : Relation.EqvGen
      (LanDiagStep (prodEndoProf P Q) tw) x y) :
    Relation.EqvGen (LanDiagStep P tw)
      ⟨x.1, x.2.1⟩ ⟨y.1, y.2.1⟩ := by
  induction h with
  | rel _ _ hr =>
    exact .rel _ _ (lanDiagStep_fst P Q hr)
  | refl => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ =>
    exact .trans _ _ _ ih₁ ih₂

/-- The equivalence closure of `LanDiagStep` on
`prodEndoProf P Q` induces the same on `Q`. -/
private theorem lanDiagSetoid_snd
    {tw : TwistedArrow C}
    {x y : DecFactSigma (prodEndoProf P Q) tw}
    (h : Relation.EqvGen
      (LanDiagStep (prodEndoProf P Q) tw) x y) :
    Relation.EqvGen (LanDiagStep Q tw)
      ⟨x.1, x.2.2⟩ ⟨y.1, y.2.2⟩ := by
  induction h with
  | rel _ _ hr =>
    exact .rel _ _ (lanDiagStep_snd P Q hr)
  | refl => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ =>
    exact .trans _ _ _ ih₁ ih₂

/-- The product comparison map: the canonical map from
`LanDiag (prodEndoProf P Q) tw` to
`LanDiag P tw × LanDiag Q tw`, projecting each
component through the same factorisation. -/
def lanDiagProdComparison
    (tw : TwistedArrow C) :
    LanDiag (prodEndoProf P Q) tw →
    LanDiag P tw × LanDiag Q tw :=
  Quotient.lift
    (fun x => (⟦⟨x.1, x.2.1⟩⟧, ⟦⟨x.1, x.2.2⟩⟧))
    (fun _ _ h =>
      Prod.ext
        (Quotient.sound (lanDiagSetoid_fst P Q h))
        (Quotient.sound (lanDiagSetoid_snd P Q h)))

/-- The product comparison map commutes with the
assembly map: `lanDiagCounit (prodEndoProf P Q) tw`
decomposes as the pair of individual counit maps
on the comparison's components. -/
theorem lanDiagCounit_prod_eq
    (tw : TwistedArrow C)
    (q : LanDiag (prodEndoProf P Q) tw) :
    lanDiagCounit (prodEndoProf P Q) tw q =
    ((lanDiagCounit P tw
        (lanDiagProdComparison P Q tw q).1),
     (lanDiagCounit Q tw
        (lanDiagProdComparison P Q tw q).2)) := by
  obtain ⟨x⟩ := q
  rfl

/-- Surjectivity of `lanDiagProdComparison` implies
that every pair `(q_P, q_Q)` admits representatives
sharing a common factorisation: there exist `fact`,
`d_P`, `d_Q` such that
`⟦⟨fact, d_P⟩⟧ = q_P` and `⟦⟨fact, d_Q⟩⟧ = q_Q`. -/
theorem lanDiagProdComparison_surj_common_fact
    {tw : TwistedArrow C}
    (h : Function.Surjective
      (lanDiagProdComparison P Q tw))
    (q_P : LanDiag P tw)
    (q_Q : LanDiag Q tw) :
    ∃ (fact : Factorisation (twArr tw))
      (d_P : diagApp P fact.mid)
      (d_Q : diagApp Q fact.mid),
      (⟦⟨fact, d_P⟩⟧ : LanDiag P tw) = q_P ∧
      (⟦⟨fact, d_Q⟩⟧ : LanDiag Q tw) = q_Q := by
  obtain ⟨pre, hpre⟩ := h (q_P, q_Q)
  obtain ⟨⟨fact, d_P, d_Q⟩⟩ := pre
  exact ⟨fact, d_P, d_Q,
    congrArg Prod.fst hpre,
    congrArg Prod.snd hpre⟩

end ProductComparison

section FixedPoints

/-- A profunctor `P` is a fixed point of the
diagonalization monad `Lan_iota . iota*` when the
counit `lanDiagCounit P tw` is a bijection for every
twisted arrow `tw`. This means `P` is fully determined
by its diagonal elements in a bijective (not merely
surjective) sense. -/
def IsLanDiagFixed (P : Cᵒᵖ ⥤ C ⥤ Type w₁) : Prop :=
  ∀ (tw : TwistedArrow C),
    Function.Bijective (lanDiagCounit P tw)

/-- A fixed point of the diagonalization monad is
diagonally determined (surjectivity half of the
counit bijection). -/
theorem IsLanDiagFixed.isDiagDeterminedProf
    {P : Cᵒᵖ ⥤ C ⥤ Type w₁}
    (h : IsLanDiagFixed P) :
    IsDiagDeterminedProf P :=
  (isDiagDeterminedProf_iff_lanDiagCounit_surj P).mpr
    (fun tw => (h tw).2)

/-- The counit at an identity twisted arrow is a
bijection for any profunctor: the counit at
`twObjMk (𝟙 c)` sends a quotient element to
`P(c, c)` and is invertible via the unit
isomorphism. -/
theorem lanDiagCounit_bijective_at_identity
    (P : Cᵒᵖ ⥤ C ⥤ Type w₁) (c : C) :
    Function.Bijective
      (lanDiagCounit P (twObjMk (𝟙 c))) := by
  constructor
  · intro q₁ q₂ h
    have : lanDiagUnitInvApp P c q₁ =
        lanDiagUnitInvApp P c q₂ := by
      simp only [lanDiagUnitInvApp]
      induction q₁ using Quotient.inductionOn with
      | h x₁ =>
        induction q₂ using Quotient.inductionOn with
        | h x₂ =>
          simp only [Quotient.lift_mk,
            lanDiagCounit, Quotient.lift_mk] at h
          exact congrArg ULift.up h
    rw [← lanDiagUnitApp_comp_invApp P c q₁,
        ← lanDiagUnitApp_comp_invApp P c q₂]
    exact congrArg
      (lanDiagUnitApp P (identityTwArrObj C c))
      this
  · intro y
    exact ⟨⟦⟨Factorisation.initial, y⟩⟧, by
      simp only [lanDiagCounit, Quotient.lift_mk,
        assemblyMapProf_at_identity]⟩

/-- `IsLanDiagFixed` is equivalent to the conjunction
of `IsDiagDeterminedProf` (surjectivity of the counit)
and pointwise injectivity of the counit. -/
theorem isLanDiagFixed_iff
    (P : Cᵒᵖ ⥤ C ⥤ Type w₁) :
    IsLanDiagFixed P ↔
    IsDiagDeterminedProf P ∧
    ∀ (tw : TwistedArrow C),
      Function.Injective (lanDiagCounit P tw) := by
  constructor
  · intro h
    exact ⟨h.isDiagDeterminedProf,
      fun tw => (h tw).1⟩
  · intro ⟨hS, hI⟩ tw
    exact ⟨hI tw,
      ((isDiagDeterminedProf_iff_lanDiagCounit_surj
        P).mp hS) tw⟩

end FixedPoints

end DiagonalizationMonad

section ParametricityDivergence

/-!
## Parametricity divergence

The profunctors arising in the type
`phi : forall X. ((X -> X) -> X) -> X`, the standard
example where paranaturality (strong dinaturality) and
Reynolds parametricity diverge (Neumann, TYPES 2024).
The outer `->` is the `ParanatSig` arrow, giving source
profunctor `P(a, b) = (b -> a) -> b` and target
profunctor `Q(a, b) = b` (which is `IdProf`).
-/

/-- The covariant part of `divSource` for fixed
contravariant argument `a`: sends `b` to
`(b -> a) -> b`, with covariant action
`g : b -> b'` sending `p` to `fun h => g (p (h . g))`. -/
def divSourceInner (a : Type) : Type ⥤ Type where
  obj b := (b → a) → b
  map g p h := g (p (h ∘ g))

/-- The source profunctor for the parametricity
divergence type: `P : Type^op x Type -> Type` sending
`(a, b)` to `(b -> a) -> b`. On the diagonal,
`P(I, I) = (I -> I) -> I`. The contravariant action
of `f : a' -> a` sends `p : (b -> a) -> b` to
`fun h => p (f . h)`. -/
def divSource : Typeᵒᵖ ⥤ Type ⥤ Type where
  obj a := divSourceInner a.unop
  map f :=
    { app := fun _ p h => p (f.unop ∘ h)
      naturality := fun _ _ _ => rfl }

@[simp]
theorem divSource_obj_obj (a b : Type) :
    (divSource.obj (Opposite.op a)).obj b =
    ((b → a) → b) :=
  rfl

theorem divSource_diag (I : Type) :
    diagApp divSource I = ((I → I) → I) :=
  rfl

/-- The target profunctor for the parametricity
divergence type: `Q(a, b) = b`, ignoring the
contravariant argument. This is `IdProf`. -/
abbrev divTarget : Typeᵒᵖ ⥤ Type ⥤ Type :=
  IdProf (C := Type)

@[simp]
theorem divTarget_obj_obj (a b : Type) :
    (divTarget.obj (Opposite.op a)).obj b = b :=
  rfl

theorem divTarget_diag (I : Type) :
    diagApp divTarget I = I :=
  rfl

/-- The `ParanatSig` for the parametricity divergence
profunctors gives the type
`forall I. ((I -> I) -> I) -> I`. -/
theorem divParanatSig_eq :
    ParanatSig divSource divTarget =
    ((I : Type) → ((I → I) → I) → I) :=
  rfl

/-- `DiagCompat` for the source profunctor `divSource`
reduces to: for all `r : I₁ -> I₀`,
`f (p (r . f)) = q (f . r)`. -/
theorem divSource_diagCompat_eq
    {I₀ I₁ : Type} (f : I₀ → I₁)
    (p : (I₀ → I₀) → I₀) (q : (I₁ → I₁) → I₁) :
    DiagCompat divSource I₀ I₁ f p q =
    ((fun r : I₁ → I₀ => f (p (r ∘ f))) =
     (fun r : I₁ → I₀ => q (f ∘ r))) :=
  rfl

/-- `DiagCompat` for the target profunctor `divTarget`
(= `IdProf`) reduces to `f x = y`. -/
theorem divTarget_diagCompat_eq
    {I₀ I₁ : Type} (f : I₀ → I₁)
    (x : I₀) (y : I₁) :
    DiagCompat divTarget I₀ I₁ f x y =
    (f x = y) :=
  rfl

/-- The paranaturality (strong dinaturality) condition
for `phi : forall I. ((I -> I) -> I) -> I`, spelled
out: for all `f : I -> J`, `p`, `q`, if
`forall r : J -> I, f (p (r . f)) = q (f . r)` then
`f (phi p) = phi q`. -/
def DivParanatural
    (phi : ParanatSig divSource divTarget) : Prop :=
  ∀ (I₀ I₁ : Type) (f : I₀ → I₁)
    (p : (I₀ → I₀) → I₀)
    (q : (I₁ → I₁) → I₁),
    (∀ r : I₁ → I₀,
      f (p (r ∘ f)) = q (f ∘ r)) →
    f (phi I₀ p) = phi I₁ q

/-- The Reynolds parametricity free theorem for
`phi : forall I. ((I -> I) -> I) -> I`: for all
`f : I -> J`, `p`, `q`, if for all `h : I -> I` and
`k : J -> J` with `f . h = k . f` we have
`f (p h) = q k`, then `f (phi p) = phi q`.

The hypothesis quantifies over independent pairs
`(h, k)` satisfying the commutation condition
`f . h = k . f`, unlike `DivParanatural` which
restricts to pairs `(r . f, f . r)`. -/
def DivParametric
    (phi : ParanatSig divSource divTarget) : Prop :=
  ∀ (I₀ I₁ : Type) (f : I₀ → I₁)
    (p : (I₀ → I₀) → I₀)
    (q : (I₁ → I₁) → I₁),
    (∀ (h : I₀ → I₀) (k : I₁ → I₁),
      f ∘ h = k ∘ f →
      f (p h) = q k) →
    f (phi I₀ p) = phi I₁ q

/-- `DivParanatural` is equivalent to
`IsParanatural divSource divTarget`. The only
difference is that `DiagCompat` for `divSource` uses
function equality while `DivParanatural` uses
pointwise equality. -/
theorem divParanatural_iff_isParanatural
    (phi : ParanatSig divSource divTarget) :
    DivParanatural phi ↔
    IsParanatural divSource divTarget phi := by
  constructor
  · intro h I₀ I₁ f p q hcompat
    exact h I₀ I₁ f p q (congr_fun hcompat)
  · intro h I₀ I₁ f p q hpw
    exact h I₀ I₁ f p q (funext hpw)

/-- Paranaturality implies parametricity: every
paranatural `phi` satisfies the Reynolds free theorem.
The `DivParanatural` hypothesis tests all `r : J -> I`,
generating pairs `(r . f, f . r)`. The `DivParametric`
hypothesis tests all `(h, k)` with `f . h = k . f`,
which includes the `r`-generated pairs as a special
case (taking `r` such that `h = r . f`). Since the
paranaturality gate admits more `(p, q)` pairs
(weaker hypothesis), its conclusion covers more
cases. -/
theorem divParanatural_implies_divParametric
    {phi : ParanatSig divSource divTarget}
    (h : DivParanatural phi) :
    DivParametric phi := by
  intro I₀ I₁ f p q hrel
  apply h I₀ I₁ f p q
  intro r
  exact hrel (r ∘ f) (f ∘ r) (by ext x; rfl)

/-- The element `fun I p => p id` of
`ParanatSig divSource divTarget`.
At each type `I`, applies the given
`p : (I -> I) -> I` to the identity
endomorphism. -/
def divApplyId : ParanatSig divSource divTarget :=
  fun _ p => p id

theorem divApplyId_parametric :
    DivParametric divApplyId := by
  intro I₀ I₁ f p q hrel
  exact hrel id id rfl

/-- `divApplyId` is not paranatural. Witness:
`I₀ = I₁ = Bool`, `f = const true`,
`p = q = (· false)`. The paranaturality hypothesis
`∀ r, f (p (r ∘ f)) = q (f ∘ r)` holds since both
sides reduce to `true`, but `f (p id) = true` while
`q id = false`. -/
theorem divApplyId_not_paranatural :
    ¬ DivParanatural divApplyId := by
  intro hpn
  have := hpn Bool Bool (fun _ => true)
    (fun g => g false) (fun g => g false)
    (fun _ => rfl)
  exact absurd this (by decide)

/-- Parametricity does not imply paranaturality:
`divApplyId` witnesses the separation. -/
theorem divParametric_not_implies_divParanatural :
    ¬ (∀ phi : ParanatSig divSource divTarget,
      DivParametric phi → DivParanatural phi) :=
  fun h => divApplyId_not_paranatural
    (h divApplyId divApplyId_parametric)

/-- Candidate paranatural element:
`fun I p => p (fun x => p (fun _ => x))`.
Applies `p` to the function that replaces its
argument with the fixpoint-like iterate
`p (const x)`. -/
def divIterOnce : ParanatSig divSource divTarget :=
  fun _ p => p (fun x => p (fun _ => x))

theorem divIterOnce_parametric :
    DivParametric divIterOnce := by
  intro I₀ I₁ f p q hrel
  simp only [divIterOnce]
  apply hrel
  ext x
  exact hrel (fun _ => x) (fun _ => f x) rfl

theorem divIterOnce_not_paranatural :
    ¬ DivParanatural divIterOnce := by
  intro hpn
  have := hpn Bool Bool (fun _ => true)
    (fun g => g false) (fun g => g false)
    (fun _ => rfl)
  exact absurd this (by decide)

/-- Candidate `fun I p => p (fun _ => p (fun _ => p id))`,
three-deep iteration. -/
def divIterThree :
    ParanatSig divSource divTarget :=
  fun _ p =>
    p (fun _ => p (fun _ => p id))

theorem divIterThree_not_paranatural :
    ¬ DivParanatural divIterThree := by
  intro hpn
  have := hpn Bool Bool (fun _ => true)
    (fun g => g false) (fun g => g false)
    (fun _ => rfl)
  exact absurd this (by decide)

/-- The hom-profunctor on `Type`, sending `(A, B)`
to `A → B`. The curried form of
`Functor.hom Type`. -/
abbrev divHomProf : Typeᵒᵖ ⥤ Type ⥤ Type :=
  Functor.curry.obj (Functor.hom Type)

theorem divHomProf_diagCompat_eq
    {I₀ I₁ : Type} (f : I₀ → I₁)
    (h : I₀ → I₀) (k : I₁ → I₁) :
    DiagCompat divHomProf I₀ I₁ f h k =
    (f ∘ h = k ∘ f) :=
  rfl

/-- The relational interpretation of the function
type constructor. Given a relation `R` on inputs
and `S` on outputs, `arrowRel R S g₀ g₁` holds
iff `g₀` and `g₁` map `R`-related inputs to
`S`-related outputs. This is Wadler's `[[A → B]]`
(section 3, "Theorems for free!"). -/
def arrowRel
    {A₀ A₁ B₀ B₁ : Type}
    (R : A₀ → A₁ → Prop)
    (S : B₀ → B₁ → Prop)
    (g₀ : A₀ → B₀) (g₁ : A₁ → B₁) : Prop :=
  ∀ (a₀ : A₀) (a₁ : A₁),
    R a₀ a₁ → S (g₀ a₀) (g₁ a₁)

/-- For graph relations, `arrowRel` reduces to the
commutativity of the naturality square
`g₀ ≫ f' = f ≫ g₁`, i.e., `f' . g₀ = g₁ . f`.
This is the `Type`-level analogue of
`yonedaProdOverRelated_graph_iff`. -/
theorem arrowRel_graphRel_iff
    {A A' B B' : Type}
    (f : A → A') (f' : B → B')
    (g₀ : A → B) (g₁ : A' → B') :
    arrowRel (graphRel f) (graphRel f')
      g₀ g₁ ↔
    f' ∘ g₀ = g₁ ∘ f := by
  constructor
  · intro h
    funext a
    exact h a (f a) rfl
  · intro h a₀ a₁ hrel
    simp only [graphRel] at hrel
    subst hrel
    exact congr_fun h a₀

/-- `arrowRel` applied to graph relations coincides
with `YonedaProdOverRelated` applied to graph objects
in the presheaf category. Both reduce to the
naturality-square condition `f' . g₀ = g₁ . f`. -/
theorem arrowRel_graphRel_iff_yonedaProdOverRelated
    {A A' B B' : Type}
    (f : A → A') (f' : B → B')
    (g₀ : A → B) (g₁ : A' → B') :
    arrowRel (graphRel f) (graphRel f')
      g₀ g₁ ↔
    YonedaProdOverRelated (C := Type)
      (yonedaProdOverGraph f)
      (yonedaProdOverGraph f')
      g₀ g₁ :=
  (arrowRel_graphRel_iff f f' g₀ g₁).trans
    (yonedaProdOverRelated_graph_iff
      (C := Type) f f' g₀ g₁).symm

/-- `arrowRel` applied to graph relations coincides
with the 2-cell condition `yonedaRelSQS` in the
Yoneda relation double category, applied to the
graph embeddings of `f` and `f'` as vertical
morphisms. -/
theorem arrowRel_graphRel_iff_yonedaRelSQS
    {A A' B B' : Type}
    (f : A → A') (f' : B → B')
    (g₀ : A → B) (g₁ : A' → B') :
    arrowRel (graphRel f) (graphRel f')
      g₀ g₁ ↔
    yonedaRelSQS (C := Type)
      (yonedaRelGraph f)
      (yonedaRelGraph f')
      g₀ g₁ := by
  constructor
  · intro h
    rw [arrowRel_graphRel_iff f f' g₀ g₁] at h
    intro c p p' (hp : p ≫ f = p')
    rw [← hp]
    exact congrArg (p ≫ ·) h
  · intro h
    rw [arrowRel_graphRel_iff f f' g₀ g₁]
    funext a
    have := h (Opposite.op A)
      (𝟙 A) (𝟙 A ≫ f) rfl
    simp only [Category.id_comp] at this
    exact congr_fun this a

/-- The presheaf encoding a `Prop`-valued binary
relation `R : A → B → Prop` as a functor
`Type^op ⥤ Type`. At test object `T`, an element
is a triple `(a : T → A, b : T → B)` together
with a proof that `∀ t, R (a t) (b t)`. The
restriction action precomposes both function
components with the stage-change map. -/
def propRelPresheaf {A B : Type}
    (R : A → B → Prop) : Typeᵒᵖ ⥤ Type where
  obj T :=
    { p : (T.unop → A) × (T.unop → B) //
      ∀ t, R (p.1 t) (p.2 t) }
  map {T T'} s p :=
    ⟨(p.val.1 ∘ s.unop, p.val.2 ∘ s.unop),
     fun t => p.property (s.unop t)⟩

/-- Natural transformation from `propRelPresheaf R`
to `yonedaProdPresheaf A B` that forgets the
relation proof, retaining only the pair of
functions. -/
def propRelProj {A B : Type}
    (R : A → B → Prop) :
    propRelPresheaf R ⟶
      yonedaProdPresheaf (C := Type) A B where
  app T p := p.val

/-- A `Prop`-valued relation `R : A → B → Prop`,
viewed as an object of the slice category
`Over (yonedaProdPresheaf A B)`, i.e., as
a `YonedaProdOver A B` in `PSh(Type)`. The
underlying presheaf is `propRelPresheaf R` and
the structure map projects out the function
pair, forgetting the relation proof. -/
def propRelToYonedaProdOver {A B : Type}
    (R : A → B → Prop) :
    YonedaProdOver (C := Type) A B :=
  Over.mk (propRelProj R)

/-- Natural isomorphism between the presheaf
encoding of a graph relation and the representable
presheaf on the domain. At stage `T`, the forward
map extracts the first component of the pair
(the second is determined by the graph condition),
and the inverse reconstructs the pair using
post-composition. -/
def propRelPresheaf_graphRel_iso
    {X Y : Type} (f : X → Y) :
    propRelPresheaf (graphRel f) ≅
      yoneda.obj (C := Type) X :=
  NatIso.ofComponents
    (fun T => {
      hom := fun p => p.val.1
      inv := fun a =>
        ⟨(a, f ∘ a), fun _ => rfl⟩
      hom_inv_id := by
        ext ⟨⟨a, b⟩, h⟩
        simp only [graphRel] at h
        exact Subtype.ext
          (Prod.ext rfl (funext h))
      inv_hom_id := rfl })
    (fun _ => rfl)

/-- The `YonedaProdOver` encoding of a graph
relation `graphRel f` is isomorphic to
`yonedaProdOverGraph f`. -/
def propRelToYonedaProdOver_graphRel
    {X Y : Type} (f : X → Y) :
    propRelToYonedaProdOver (graphRel f) ≅
      yonedaProdOverGraph (C := Type) f :=
  Over.isoMk (propRelPresheaf_graphRel_iso f)
    (by
      ext T ⟨⟨a, b⟩, h⟩
      simp only [propRelPresheaf_graphRel_iso,
        propRelToYonedaProdOver, propRelProj,
        yonedaProdOverGraph,
        Over.mk_hom, NatIso.ofComponents,
        NatTrans.comp_app]
      simp only [graphRel] at h
      exact Prod.ext rfl (funext h))

/-- `arrowRel R S g₀ g₁` holds if and only if
`YonedaProdOverRelated` holds for the presheaf
encodings of `R` and `S`. The forward direction
constructs a presheaf morphism from the pointwise
condition; the reverse evaluates at `PUnit` with
constant functions. -/
theorem arrowRel_iff_yonedaProdOverRelated_propRel
    {A₀ A₁ B₀ B₁ : Type}
    (R : A₀ → A₁ → Prop)
    (S : B₀ → B₁ → Prop)
    (g₀ : A₀ → B₀) (g₁ : A₁ → B₁) :
    arrowRel R S g₀ g₁ ↔
    YonedaProdOverRelated (C := Type)
      (propRelToYonedaProdOver R)
      (propRelToYonedaProdOver S)
      g₀ g₁ := by
  constructor
  · intro h
    refine ⟨⟨fun T p =>
      ⟨(g₀ ∘ p.val.1, g₁ ∘ p.val.2),
       fun t => h _ _ (p.property t)⟩, ?_⟩,
      ?_⟩
    · intro T T' s
      ext ⟨⟨a, b⟩, hr⟩
      rfl
    · ext T ⟨⟨a, b⟩, hr⟩
      rfl
  · rintro ⟨φ, hφ⟩ a₀ a₁ hr
    let T := Opposite.op PUnit
    let elem : (propRelPresheaf R).obj T :=
      ⟨(fun _ => a₀, fun _ => a₁),
       fun _ => hr⟩
    let img := φ.app T elem
    have hcomm :
        img.val =
        (propRelProj R ≫
          yonedaProdMap (C := Type) g₀ g₁).app
          T elem := by
      change (φ.app T ≫
        (propRelProj S).app T) elem =
        ((propRelProj R).app T ≫
        (yonedaProdMap (C := Type)
          g₀ g₁).app T) elem
      exact congr_fun
        (NatTrans.congr_app hφ T) elem
    simp only [propRelProj,
      NatTrans.comp_app,
      yonedaProdMap,
      FunctorToTypes.prod.lift,
      FunctorToTypes.prod.fst,
      FunctorToTypes.prod.snd] at hcomm
    have h₁ : img.val.1 () = g₀ a₀ :=
      congr_fun (congr_arg Prod.fst hcomm) ()
    have h₂ : img.val.2 () = g₁ a₁ :=
      congr_fun (congr_arg Prod.snd hcomm) ()
    exact h₁ ▸ h₂ ▸ img.property ()

/-- A `Prop`-valued relation `R : A → B → Prop`,
viewed as a `YonedaRel` (subfunctor of the
product presheaf). -/
def propRelToYonedaRel {A B : Type}
    (R : A → B → Prop) :
    YonedaRel (C := Type) A B :=
  pshProdOverToRel (propRelToYonedaProdOver R)

/-- `arrowRel R S g₀ g₁` holds iff the presheaf
encodings of `R` and `S` are `relRelated` in the
`YonedaRel` framework. -/
theorem arrowRel_iff_relRelated_propRel
    {A₀ A₁ B₀ B₁ : Type}
    (R : A₀ → A₁ → Prop)
    (S : B₀ → B₁ → Prop)
    (g₀ : A₀ → B₀) (g₁ : A₁ → B₁) :
    arrowRel R S g₀ g₁ ↔
    relRelated (C := Type) g₀ g₁
      (propRelToYonedaRel R)
      (propRelToYonedaRel S) := by
  constructor
  · intro harr
    rw [arrowRel_iff_yonedaProdOverRelated_propRel
      R S g₀ g₁] at harr
    exact pshProdOverRelated_topshRelRelated
      harr
  · intro hrel a₀ a₁ hR
    have hobj := hrel (Opposite.op PUnit)
      (fun _ => a₀) (fun _ => a₁)
      ⟨⟨(fun _ => a₀, fun _ => a₁),
        fun _ => hR⟩, rfl⟩
    obtain ⟨⟨⟨b₀fun, b₁fun⟩, hs⟩,
      hval⟩ := hobj
    have h1 : b₀fun = g₀ ∘ fun _ => a₀ :=
      congr_arg Prod.fst hval
    have h2 : b₁fun = g₁ ∘ fun _ => a₁ :=
      congr_arg Prod.snd hval
    have := hs ()
    rw [h1, h2] at this
    exact this

/-- `arrowRel R S g₀ g₁` holds iff `yonedaRelSQS`
holds for the Yoneda relation encodings of `R` and
`S` as vertical morphisms. -/
theorem arrowRel_iff_yonedaRelSQS_propRel
    {A₀ A₁ B₀ B₁ : Type}
    (R : A₀ → A₁ → Prop)
    (S : B₀ → B₁ → Prop)
    (g₀ : A₀ → B₀) (g₁ : A₁ → B₁) :
    arrowRel R S g₀ g₁ ↔
    yonedaRelSQS (C := Type)
      (propRelToYonedaRel R)
      (propRelToYonedaRel S)
      g₀ g₁ :=
  arrowRel_iff_relRelated_propRel R S g₀ g₁

/-- The canonical relation lifting for a
profunctor `G : Typeᵒᵖ × Type ⥤ Type`.
Given relations `R` between `A₁, A₂` and
`S` between `B₁, B₂`,
`profunctorRelLift G R S x y` holds iff there
exists a witness `w : G.obj (op SubR, SubS)`
whose covariant projections match the
contravariant pullbacks of `x` and `y`.

This generalizes both `functorRelLift`
(when `G = ProjProf Type F`) and `arrowRel`
(when `G = Functor.hom Type`). -/
def profunctorRelLift
    (G : Typeᵒᵖ × Type ⥤ Type)
    {A₁ A₂ B₁ B₂ : Type}
    (R : A₁ → A₂ → Prop)
    (S : B₁ → B₂ → Prop)
    (x : G.obj (Opposite.op A₁, B₁))
    (y : G.obj (Opposite.op A₂, B₂)) :
    Prop :=
  let SubR :=
    { p : A₁ × A₂ // R p.1 p.2 }
  let SubS :=
    { q : B₁ × B₂ // S q.1 q.2 }
  let pi₁ : SubR → A₁ := fun s => s.val.1
  let pi₂ : SubR → A₂ := fun s => s.val.2
  let rho₁ : SubS → B₁ := fun s => s.val.1
  let rho₂ : SubS → B₂ := fun s => s.val.2
  ∃ (w : G.obj (Opposite.op SubR, SubS)),
    G.map (show (Opposite.op SubR, SubS) ⟶
        (Opposite.op SubR, B₁) from
      (𝟙 (Opposite.op SubR), rho₁)) w =
      G.map (show (Opposite.op A₁, B₁) ⟶
          (Opposite.op SubR, B₁) from
        (Quiver.Hom.op pi₁, 𝟙 B₁)) x ∧
    G.map (show (Opposite.op SubR, SubS) ⟶
        (Opposite.op SubR, B₂) from
      (𝟙 (Opposite.op SubR), rho₂)) w =
      G.map (show (Opposite.op A₂, B₂) ⟶
          (Opposite.op SubR, B₂) from
        (Quiver.Hom.op pi₂, 𝟙 B₂)) y

/-- When `G = ProjProf Type F` (the projection
profunctor ignoring the contravariant argument),
`profunctorRelLift` reduces to `functorRelLift`:
the contravariant component plays no role, so the
witness and conditions depend only on `S`. -/
theorem profunctorRelLift_proj_eq
    (F : Type ⥤ Type)
    {A₁ A₂ B₁ B₂ : Type}
    (R : A₁ → A₂ → Prop)
    (S : B₁ → B₂ → Prop)
    (x : F.obj B₁) (y : F.obj B₂) :
    profunctorRelLift (ProjProf Type F)
      R S x y ↔
    functorRelLift F S x y := by
  simp only [profunctorRelLift,
    functorRelLift, ProjProf_obj, ProjProf_map,
    CategoryTheory.Functor.map_id]
  rfl

/-- When `G = Functor.hom Type` (the hom
profunctor), `profunctorRelLift` reduces to
`arrowRel`: the witness encodes a function
from `R`-related inputs to `S`-related
outputs. -/
theorem profunctorRelLift_hom_eq
    {A₁ A₂ B₁ B₂ : Type}
    (R : A₁ → A₂ → Prop)
    (S : B₁ → B₂ → Prop)
    (x : A₁ → B₁) (y : A₂ → B₂) :
    profunctorRelLift (Functor.hom Type)
      R S x y ↔
    arrowRel R S x y := by
  simp only [profunctorRelLift,
    Functor.hom_map, Quiver.Hom.unop_op,
    unop_id_op, Category.id_comp,
    Category.comp_id]
  constructor
  · rintro ⟨w, hw₁, hw₂⟩ a₁ a₂ hr
    have h₁ := congr_fun hw₁ ⟨⟨a₁, a₂⟩, hr⟩
    have h₂ := congr_fun hw₂ ⟨⟨a₁, a₂⟩, hr⟩
    simp only [types_comp_apply] at h₁ h₂
    rw [← h₁, ← h₂]
    exact (w ⟨⟨a₁, a₂⟩, hr⟩).property
  · intro h
    exact ⟨fun ⟨⟨a₁, a₂⟩, hr⟩ =>
      ⟨⟨x a₁, y a₂⟩, h a₁ a₂ hr⟩,
      rfl, rfl⟩

/-- `profunctorRelLift` with the hom profunctor
equals `arrowRel`. -/
@[simp]
theorem profunctorRelLift_hom
    {A₁ A₂ B₁ B₂ : Type}
    (R : A₁ → A₂ → Prop)
    (S : B₁ → B₂ → Prop) :
    profunctorRelLift (Functor.hom Type) R S =
    arrowRel R S := by
  funext x y
  exact propext
    (profunctorRelLift_hom_eq R S x y)

/-- `profunctorRelLift` with the projection
profunctor equals `functorRelLift`. -/
@[simp]
theorem profunctorRelLift_proj
    (F : Type ⥤ Type)
    {A₁ A₂ B₁ B₂ : Type}
    (R : A₁ → A₂ → Prop)
    (S : B₁ → B₂ → Prop) :
    profunctorRelLift (ProjProf Type F) R S =
    functorRelLift F S := by
  funext x y
  exact propext
    (profunctorRelLift_proj_eq F R S x y)

/-- When both relations are graph relations,
`profunctorRelLift` reduces to a wedge
condition: `G.map (𝟙, g) x = G.map (f^op, 𝟙) y`.
This is the profunctor analogue of the wedge
condition for ends. -/
theorem profunctorRelLift_graphRel
    (G : Typeᵒᵖ × Type ⥤ Type)
    {A₁ A₂ B₁ B₂ : Type}
    (f : A₁ → A₂) (g : B₁ → B₂)
    (x : G.obj (Opposite.op A₁, B₁))
    (y : G.obj (Opposite.op A₂, B₂)) :
    profunctorRelLift G
      (graphRel f) (graphRel g) x y ↔
    G.map (show (Opposite.op A₁, B₁) ⟶
        (Opposite.op A₁, B₂) from
      (𝟙 (Opposite.op A₁), g)) x =
    G.map (show (Opposite.op A₂, B₂) ⟶
        (Opposite.op A₁, B₂) from
      (Quiver.Hom.op f, 𝟙 B₂)) y := by
  simp only [profunctorRelLift]
  let pi₁ : {p : A₁ × A₂ //
      graphRel f p.1 p.2} → A₁ :=
    fun s => s.val.1
  let pi₂ : {p : A₁ × A₂ //
      graphRel f p.1 p.2} → A₂ :=
    fun s => s.val.2
  let rho₁ : {q : B₁ × B₂ //
      graphRel g q.1 q.2} → B₁ :=
    fun s => s.val.1
  let rho₂ : {q : B₁ × B₂ //
      graphRel g q.1 q.2} → B₂ :=
    fun s => s.val.2
  let ιR : A₁ →
      {p : A₁ × A₂ // graphRel f p.1 p.2} :=
    fun a => ⟨(a, f a), rfl⟩
  let ιS : B₁ →
      {q : B₁ × B₂ // graphRel g q.1 q.2} :=
    fun b => ⟨(b, g b), rfl⟩
  have rho_eq :
      rho₂ = fun s => g (rho₁ s) := by
    funext ⟨⟨_, _⟩, h⟩; exact h.symm
  have pi_eq :
      pi₂ = fun s => f (pi₁ s) := by
    funext ⟨⟨_, _⟩, h⟩; exact h.symm
  constructor
  · rintro ⟨w, hw₁, hw₂⟩
    have comm₁ := congr_arg
      (G.map (show (Opposite.op
        {p : A₁ × A₂ //
          graphRel f p.1 p.2}, B₁) ⟶
        (Opposite.op A₁, B₁) from
        (Quiver.Hom.op ιR, 𝟙 B₁))) hw₁
    rw [← FunctorToTypes.map_comp_apply,
      ← FunctorToTypes.map_comp_apply]
      at comm₁
    change G.map (show _ ⟶ _ from
        (Quiver.Hom.op ιR, rho₁)) w =
      G.map (𝟙 _) x at comm₁
    simp only [G.map_id, types_id_apply]
      at comm₁
    have comm₂ := congr_arg
      (G.map (show (Opposite.op
        {p : A₁ × A₂ //
          graphRel f p.1 p.2}, B₂) ⟶
        (Opposite.op A₁, B₂) from
        (Quiver.Hom.op ιR, 𝟙 B₂))) hw₂
    rw [← FunctorToTypes.map_comp_apply,
      ← FunctorToTypes.map_comp_apply]
      at comm₂
    change G.map (show _ ⟶ _ from
        (Quiver.Hom.op ιR, rho₂)) w =
      G.map (show
        (Opposite.op A₂, B₂) ⟶
          (Opposite.op A₁, B₂) from
        (Quiver.Hom.op f, 𝟙 B₂)) y
      at comm₂
    rw [← comm₁,
      ← FunctorToTypes.map_comp_apply]
    change G.map (show _ ⟶ _ from
        (Quiver.Hom.op ιR,
          fun s => g (rho₁ s))) w =
      G.map (show
        (Opposite.op A₂, B₂) ⟶
          (Opposite.op A₁, B₂) from
        (Quiver.Hom.op f, 𝟙 B₂)) y
    rw [← rho_eq]
    exact comm₂
  · intro hm
    refine ⟨G.map (show
        (Opposite.op A₁, B₁) ⟶
        (Opposite.op
          {p : A₁ × A₂ //
            graphRel f p.1 p.2},
          {q : B₁ × B₂ //
            graphRel g q.1 q.2}) from
        (Quiver.Hom.op pi₁, ιS)) x,
      ?_, ?_⟩
    · rw [←
        FunctorToTypes.map_comp_apply]
      rfl
    · rw [←
        FunctorToTypes.map_comp_apply]
      change G.map (show _ ⟶ _ from
          (Quiver.Hom.op pi₁, g)) x =
        G.map (show
          (Opposite.op A₂, B₂) ⟶
            (Opposite.op
              {p : A₁ × A₂ //
                graphRel f p.1 p.2},
              B₂) from
          (Quiver.Hom.op pi₂,
            𝟙 B₂)) y
      have comm := congr_arg
        (G.map (show
          (Opposite.op A₁, B₂) ⟶
          (Opposite.op
            {p : A₁ × A₂ //
              graphRel f p.1 p.2},
            B₂) from
          (Quiver.Hom.op pi₁,
            𝟙 B₂))) hm
      rw [← FunctorToTypes.map_comp_apply,
        ← FunctorToTypes.map_comp_apply]
        at comm
      simp only [prod_comp,
        Category.id_comp,
        Category.comp_id] at comm
      have hfpi :
          Quiver.Hom.op f ≫
            Quiver.Hom.op pi₁ =
          (Quiver.Hom.op pi₂ :
            Opposite.op A₂ ⟶ _) := by
        rw [← op_comp]
        exact congrArg _ pi_eq.symm
      rw [hfpi] at comm
      exact comm

/-- A type expression in a single variable,
built from a variable, covariant functor
application, and function spaces. The relational
interpretation (`TypeExpr.relInterp`) replaces
each `var` with `graphRel f`, each `app F T`
with `functorRelLift F (T.relInterp f)`, and
each `arrow` with `arrowRel`. -/
inductive TypeExpr : Type 1 where
  | var : TypeExpr
  | app : (Type ⥤ Type) → TypeExpr → TypeExpr
  | arrow : TypeExpr → TypeExpr → TypeExpr

/-- A covariant functor applied to the bare
variable. Equivalent to `.app F .var`. -/
abbrev TypeExpr.leaf
    (F : Type ⥤ Type) : TypeExpr :=
  .app F .var

/-- The unit type expression: a constant functor
applied to the variable, yielding `PUnit` at every
diagonal interpretation. -/
abbrev TypeExpr.unit : TypeExpr :=
  .app ((Functor.const Type).obj PUnit) .var

/-- The profunctor associated to a type expression,
constructed from induction on profunctors:
- `var` maps to `IdProf` (the identity profunctor),
- `app F T` post-composes `T.toProfunctor` with `F`
  via `whiskeringRight`,
- `arrow T₁ T₂` uses `ProfDialgebraProf` on the
  uncurried forms of `T₁` and `T₂`.

The functor laws hold by composition of the
constituent functors. -/
def TypeExpr.toProfunctor :
    TypeExpr → (Typeᵒᵖ ⥤ Type ⥤ Type)
  | .var => IdProf
  | .app F T =>
    T.toProfunctor ⋙
      (Functor.whiskeringRight Type Type Type).obj F
  | .arrow T₁ T₂ =>
    ProfDialgebraProf
      (Functor.uncurry.obj T₁.toProfunctor)
      (Functor.uncurry.obj T₂.toProfunctor)

/-- The interpretation of a type expression as a
profunctor: `interp T A B` extracts the object
map from `T.toProfunctor`, assigning a type to
each pair `(A, B)` where `A` is contravariant and
`B` is covariant. `var` gives the covariant
parameter; `app F T` applies `F` to the
interpretation of `T`; `arrow` swaps the
parameters for the domain (flipping variance).
On the diagonal, `interp T A A` recovers the
standard interpretation of `T` at the type `A`. -/
abbrev TypeExpr.interp
    (T : TypeExpr) (A B : Type) : Type :=
  (T.toProfunctor.obj (Opposite.op A)).obj B

@[simp]
theorem TypeExpr.unit_interp (I : Type) :
    TypeExpr.unit.interp I I = PUnit :=
  rfl

/-- The profunctor map for a type expression:
given `f : A' → A` (contravariant) and
`g : B → B'` (covariant), maps
`T.interp A B → T.interp A' B'`. For `var`,
this is `g`. For `app F T`, this is
`F.map (T.profMap f g)`. For `arrow T₁ T₂`,
this precomposes with `T₁.profMap g f` (swapped,
since `T₁` has flipped variance) and
postcomposes with `T₂.profMap f g`. -/
def TypeExpr.profMap
    (T : TypeExpr) {A A' B B' : Type}
    (f : A' → A) (g : B → B') :
    T.interp A B → T.interp A' B' :=
  match T with
  | .var => g
  | .app F T => F.map (T.profMap f g)
  | .arrow T₁ T₂ => fun h =>
    T₂.profMap f g ∘ h ∘ T₁.profMap g f

/-- `profMap` agrees with the morphism action of
`toProfunctor`: the recursive definition computes
the same function as the uncurried functor map. -/
theorem TypeExpr.profMap_eq_toProfunctorMap
    (T : TypeExpr) {A A' B B' : Type}
    (f : A' → A) (g : B → B') :
    T.profMap f g =
      (T.toProfunctor.map (Quiver.Hom.op f)).app B ≫
        (T.toProfunctor.obj (Opposite.op A')).map g := by
  induction T generalizing A A' B B' with
  | var => simp [profMap, toProfunctor, IdProf]
  | app F T ih =>
    simp only [profMap, toProfunctor]
    rw [ih f g, CategoryTheory.Functor.map_comp]
    congr 1
  | arrow T₁ T₂ ih₁ ih₂ =>
    ext h
    simp only [profMap, toProfunctor,
      types_comp_apply,
      ProfDialgebraProf_map_app,
      ProfDialgebraProf_obj_map,
      Opposite.unop_op, Quiver.Hom.unop_op]
    funext x
    simp only [Function.comp_apply,
      types_comp_apply, Prof.map₁, Prof.map₂,
      Functor.uncurry_obj_map,
      CategoryTheory.Functor.map_id,
      NatTrans.id_app, Category.id_comp,
      Category.comp_id]
    have h₁ := congr_fun (ih₁ g f) x
    simp only [types_comp_apply] at h₁
    rw [h₁.symm]
    have h₂ := congr_fun (ih₂ f g)
      (h (T₁.profMap g f x))
    simp only [types_comp_apply] at h₂
    exact h₂

/-- `profMap id id` is the identity function. -/
@[simp]
theorem TypeExpr.profMap_id_id
    (T : TypeExpr) {I : Type} :
    T.profMap (id : I → I) (id : I → I) = id := by
  induction T generalizing I with
  | var => rfl
  | app F T ih =>
    simp only [profMap, ih]
    exact F.map_id _
  | arrow T₁ T₂ ih₁ ih₂ =>
    ext h
    simp only [profMap, ih₁, ih₂]
    rfl

/-- The relational interpretation of a type
expression at a morphism `f : I₀ → I₁`. Each
`var` contributes `graphRel f`, each `app F T`
contributes `functorRelLift F (T.relInterp f)`,
and each `arrow` contributes `arrowRel`. -/
def TypeExpr.relInterp
    (T : TypeExpr) {I₀ I₁ : Type}
    (f : I₀ → I₁) :
    T.interp I₀ I₀ → T.interp I₁ I₁ → Prop :=
  match T with
  | .var => graphRel f
  | .app F T =>
    functorRelLift F (T.relInterp f)
  | .arrow T₁ T₂ =>
    arrowRel (T₁.relInterp f) (T₂.relInterp f)

/-- The full relational interpretation of a type
expression at an arbitrary relation
`R : I₀ → I₁ → Prop`. This generalizes `relInterp`,
which only accepts function graphs (`graphRel f`).
Each `var` contributes `R` itself, each `app F T`
contributes `functorRelLift F (T.fullRelInterp R)`,
and each `arrow` contributes `arrowRel`.

This is the relational interpretation from
Wadler's "Theorems for free!" (section 2) in its
full generality, where the relation at each type
variable is an arbitrary relation rather than the
graph of a function. -/
def TypeExpr.fullRelInterp
    (T : TypeExpr) {I₀ I₁ : Type}
    (R : I₀ → I₁ → Prop) :
    T.interp I₀ I₀ → T.interp I₁ I₁ → Prop :=
  match T with
  | .var => R
  | .app F T =>
    functorRelLift F (T.fullRelInterp R)
  | .arrow T₁ T₂ =>
    arrowRel (T₁.fullRelInterp R)
      (T₂.fullRelInterp R)

@[simp]
theorem TypeExpr.unit_fullRelInterp
    {I₀ I₁ : Type} (R : I₀ → I₁ → Prop)
    (x y : PUnit) :
    TypeExpr.unit.fullRelInterp R x y := by
  simp only [TypeExpr.fullRelInterp,
    functorRelLift]
  exact ⟨PUnit.unit, rfl, rfl⟩

/-- `fullRelInterp` applied to the graph of a
function `f` coincides with `relInterp f`. -/
theorem TypeExpr.fullRelInterp_graphRel
    (T : TypeExpr) {I₀ I₁ : Type}
    (f : I₀ → I₁) :
    T.fullRelInterp (graphRel f) = T.relInterp f := by
  induction T with
  | var => rfl
  | app F T ih =>
    simp only [fullRelInterp, relInterp, ih]
  | arrow T₁ T₂ ih₁ ih₂ =>
    simp only [fullRelInterp, relInterp, ih₁, ih₂]

/-- The relational interpretation of a type
expression `T` with separate relations for the
contravariant and covariant positions. Given
`R : A → A' → Prop` and `S : B → B' → Prop`,
`T.biRelInterp R S` is a relation
`T.interp A B → T.interp A' B' → Prop`.
This specializes to `fullRelInterp` when both
arguments coincide (`biRelInterp R R = fullRelInterp R`,
see `biRelInterp_diag`) and to `profMap` at graph
relations (see `biRelInterp_graphRel`). -/
def TypeExpr.biRelInterp
    (T : TypeExpr) {A A' B B' : Type}
    (R : A → A' → Prop) (S : B → B' → Prop) :
    T.interp A B → T.interp A' B' → Prop :=
  match T with
  | .var => S
  | .app F T' =>
    functorRelLift F (T'.biRelInterp R S)
  | .arrow T₁ T₂ =>
    arrowRel (T₁.biRelInterp S R)
      (T₂.biRelInterp R S)

/-- The diagonal specialization of `biRelInterp`:
when both arguments are the same relation `R`,
`biRelInterp R R` equals `fullRelInterp R`. -/
theorem TypeExpr.biRelInterp_diag
    (T : TypeExpr) {I₀ I₁ : Type}
    (R : I₀ → I₁ → Prop) :
    T.biRelInterp R R = T.fullRelInterp R := by
  induction T with
  | var => rfl
  | app F T' ih =>
    simp only [biRelInterp, fullRelInterp, ih]
  | arrow T₁ T₂ ih₁ ih₂ =>
    simp only [biRelInterp, fullRelInterp,
      ih₁, ih₂]

/-- The graph specialization of `biRelInterp`:
at `graphRelOp f` and `graphRel g`,
`biRelInterp` recovers `profMap f g`. The dual
statement with swapped arguments is proved
simultaneously, as the two are mutually dependent
in the `arrow` case. -/
theorem TypeExpr.biRelInterp_graphRel
    (T : TypeExpr) {A A' B B' : Type}
    (f : A' → A) (g : B → B') :
    T.biRelInterp (graphRelOp f) (graphRel g) =
        graphRel (T.profMap f g) ∧
    T.biRelInterp (graphRel g) (graphRelOp f) =
        graphRelOp (T.profMap g f) := by
  induction T generalizing A A' B B' with
  | var => exact ⟨rfl, rfl⟩
  | app F T' ih =>
    obtain ⟨ih1, ih2⟩ := ih f g
    exact ⟨
      by simp only [biRelInterp, profMap, ih1,
          functorRelLift_graphRel],
      by simp only [biRelInterp, profMap, ih2,
          functorRelLift_graphRelOp]⟩
  | arrow T₁ T₂ ih₁ ih₂ =>
    obtain ⟨ih₁1, ih₁2⟩ := ih₁ f g
    obtain ⟨ih₂1, ih₂2⟩ := ih₂ f g
    refine ⟨?_, ?_⟩
    · ext h₀ h₁
      simp only [biRelInterp, arrowRel, ih₁2,
        ih₂1, graphRelOp, graphRel, profMap]
      constructor
      · intro hrel
        funext a₁
        exact hrel (T₁.profMap g f a₁) a₁ rfl
      · intro heq a₀ a₁ ha
        rw [← ha]
        exact congr_fun heq a₁
    · ext h₀ h₁
      simp only [biRelInterp, arrowRel, ih₁1,
        ih₂2, graphRel, graphRelOp, profMap]
      constructor
      · intro hrel
        funext a₀
        exact hrel a₀ (T₁.profMap f g a₀) rfl
      · intro heq a₀ a₁ ha
        rw [← ha]
        exact congr_fun heq a₀

/-- The relational interpretation of a type
expression `T` with profunctor-convention
relations. Given `R : A' → A → Prop` (the first
relation in the opposite direction) and a covariant
relation `S : B → B' → Prop`,
`T.profRelInterp R S` is
`T.biRelInterp (Function.swap R) S`. -/
def TypeExpr.profRelInterp
    (T : TypeExpr) {A A' B B' : Type}
    (R : A' → A → Prop) (S : B → B' → Prop) :
    T.interp A B → T.interp A' B' → Prop :=
  T.biRelInterp (Function.swap R) S

/-- The two-parameter morphism interpretation of a
type expression. Given `f : A → A'` and
`g : B → B'`, `T.biMorphInterp f g` is a relation
`T.interp A B → T.interp A' B' → Prop`.

For `var`, this is `graphRel g`. For `app F T'`,
this lifts `T'.biMorphInterp f g` through `F`. For
`arrow T₁ T₂`, this is the `arrowRel` of the
sub-expression interpretations with swapped
parameters on the domain.

On the diagonal (`f = g`), this recovers
`relInterp f` (see `biMorphInterp_diag`). -/
def TypeExpr.biMorphInterp
    (T : TypeExpr) {A A' B B' : Type}
    (f : A → A') (g : B → B') :
    T.interp A B → T.interp A' B' → Prop :=
  match T with
  | .var => graphRel g
  | .app F T' =>
    functorRelLift F (T'.biMorphInterp f g)
  | .arrow T₁ T₂ =>
    arrowRel (T₁.biMorphInterp g f)
      (T₂.biMorphInterp f g)

/-- On the diagonal, `biMorphInterp` recovers
`relInterp`: `biMorphInterp f f = relInterp f`. -/
theorem TypeExpr.biMorphInterp_diag
    (T : TypeExpr) {I₀ I₁ : Type}
    (f : I₀ → I₁) :
    T.biMorphInterp f f = T.relInterp f := by
  induction T with
  | var => rfl
  | app F T' ih =>
    simp only [biMorphInterp, relInterp, ih]
  | arrow T₁ T₂ ih₁ ih₂ =>
    simp only [biMorphInterp, relInterp,
      ih₁, ih₂]

/-- `biMorphInterp` is the specialization of
`biRelInterp` to graph relations:
`biMorphInterp f g =
  biRelInterp (graphRel f) (graphRel g)`. -/
theorem TypeExpr.biMorphInterp_eq_biRelInterp
    (T : TypeExpr) {A A' B B' : Type}
    (f : A → A') (g : B → B') :
    T.biMorphInterp f g =
    T.biRelInterp (graphRel f) (graphRel g) := by
  induction T generalizing A A' B B' with
  | var => rfl
  | app F T' ih =>
    simp only [biMorphInterp, biRelInterp, ih]
  | arrow T₁ T₂ ih₁ ih₂ =>
    simp only [biMorphInterp, biRelInterp,
      ih₁, ih₂]

/-- The relational interpretation of a leaf
`app F var` reduces to `graphRel (F.map f)`. -/
@[simp]
theorem TypeExpr.leaf_relInterp
    (F : Type ⥤ Type) {I₀ I₁ : Type}
    (f : I₀ → I₁) :
    (TypeExpr.leaf F).relInterp f =
    graphRel (F.map f) :=
  functorRelLift_graphRel F f

/-- The type expression for the sub-expression
`X → X` (endomorphisms) in the divergence type. -/
def divEndoTypeExpr : TypeExpr :=
  let x := TypeExpr.leaf (𝟭 Type)
  .arrow x x

/-- The type expression for the sub-expression
`(X → X) → X` in the divergence type. -/
def divArgTypeExpr : TypeExpr :=
  .arrow divEndoTypeExpr (.leaf (𝟭 Type))

/-- The type expression for the divergence type
`((X → X) → X) → X`, with the identity functor
at each leaf. -/
def divTypeExpr : TypeExpr :=
  .arrow divArgTypeExpr (.leaf (𝟭 Type))

/-- The relational interpretation of the
sub-expression `X → X` at the graph of `f`.
A pair `(h, k)` of endomorphisms is related iff
`f`-related inputs are sent to `f`-related
outputs. -/
abbrev divEndoRel {I₀ I₁ : Type}
    (f : I₀ → I₁) :=
  divEndoTypeExpr.relInterp f

/-- The relational interpretation of the
sub-expression `(X → X) → X` at the graph of
`f`. A pair `(p, q)` is related iff
`divEndoRel`-related endomorphism pairs are sent
to `graphRel f`-related value pairs. -/
abbrev divArgRel {I₀ I₁ : Type}
    (f : I₀ → I₁) :=
  divArgTypeExpr.relInterp f

/-- The relational interpretation of the full
type `((X → X) → X) → X` at the graph of `f`.
A pair `(phi₀, phi₁)` is related iff
`divArgRel`-related argument pairs are sent to
`graphRel f`-related value pairs. -/
abbrev divFullRel {I₀ I₁ : Type}
    (f : I₀ → I₁) :=
  divTypeExpr.relInterp f

/-- `divEndoRel` expands to
`arrowRel (graphRel f) (graphRel f)`. -/
theorem divEndoRel_expand
    {I₀ I₁ : Type} (f : I₀ → I₁) :
    @divEndoRel I₀ I₁ f =
    arrowRel (graphRel f) (graphRel f) := by
  simp only [divEndoRel, divEndoTypeExpr,
    TypeExpr.relInterp,
    functorRelLift_graphRel, Functor.id_map]

/-- `divArgRel` expands to
`arrowRel (arrowRel (graphRel f) (graphRel f))
  (graphRel f)`. -/
theorem divArgRel_expand
    {I₀ I₁ : Type} (f : I₀ → I₁) :
    @divArgRel I₀ I₁ f =
    arrowRel
      (arrowRel (graphRel f) (graphRel f))
      (graphRel f) := by
  simp only [divArgRel, divArgTypeExpr,
    divEndoTypeExpr,
    TypeExpr.relInterp,
    functorRelLift_graphRel, Functor.id_map]

/-- `divFullRel` expands to a nested application
of `arrowRel` and `graphRel`, with one `arrowRel`
per `→` and one `graphRel f` per `X` in the type
expression `((X → X) → X) → X`. -/
theorem divFullRel_expand
    {I₀ I₁ : Type} (f : I₀ → I₁) :
    @divFullRel I₀ I₁ f =
    arrowRel
      (arrowRel
        (arrowRel (graphRel f) (graphRel f))
        (graphRel f))
      (graphRel f) := by
  simp only [divFullRel, divTypeExpr,
    divArgTypeExpr, divEndoTypeExpr,
    TypeExpr.relInterp,
    functorRelLift_graphRel, Functor.id_map]

/-- The type expression for a dialgebra
`F(X) → G(X)` with covariant `F` and `G`. -/
def dialgebraTypeExpr
    (F G : Type ⥤ Type) : TypeExpr :=
  .arrow (.leaf F) (.leaf G)

/-- The relational interpretation of a dialgebra
type expression at a morphism `f` is equivalent
to the naturality square
`G.map f ∘ α = β ∘ F.map f`. -/
theorem dialgebraTypeExpr_relInterp_iff
    (F G : Type ⥤ Type)
    {I₀ I₁ : Type} (f : I₀ → I₁)
    (α : F.obj I₀ → G.obj I₀)
    (β : F.obj I₁ → G.obj I₁) :
    (dialgebraTypeExpr F G).relInterp f α β ↔
    G.map f ∘ α = β ∘ F.map f := by
  simp only [dialgebraTypeExpr, TypeExpr.relInterp,
    functorRelLift_graphRel, graphRel, arrowRel]
  constructor
  · intro hrel
    ext a₀
    exact hrel a₀ (F.map f a₀) rfl
  · intro heq a₀ a₁ ha
    change G.map f (α a₀) = β a₁
    rw [← ha]
    exact congr_fun heq a₀

/-- The type expression for `(F(X) → X) → X`
(the initial algebra / catamorphism type). -/
def algebraTypeExpr
    (F : Type ⥤ Type) : TypeExpr :=
  let x := TypeExpr.leaf (𝟭 Type)
  .arrow (.arrow (.leaf F) x) x

/-- The relational interpretation of the algebra
type expression agrees with paranaturality:
given F-algebra morphism pairs `(α, β)` with
`f ∘ α = β ∘ F.map f`, the conclusion is
`f(φ₀ α) = φ₁ β`.

For single-arrow sources, DiagCompat of the
profunctor and relInterp coincide, so
paranaturality and parametricity agree. -/
theorem algebraTypeExpr_relInterp_iff
    (F : Type ⥤ Type)
    {I₀ I₁ : Type} (f : I₀ → I₁)
    (φ₀ : (F.obj I₀ → I₀) → I₀)
    (φ₁ : (F.obj I₁ → I₁) → I₁) :
    (algebraTypeExpr F).relInterp f φ₀ φ₁ ↔
    ∀ (α : F.obj I₀ → I₀)
      (β : F.obj I₁ → I₁),
      f ∘ α = β ∘ F.map f →
      f (φ₀ α) = φ₁ β := by
  simp only [algebraTypeExpr, TypeExpr.relInterp,
    functorRelLift_graphRel, graphRel, arrowRel,
    Functor.id_map]
  constructor
  · intro hrel α β hab
    exact hrel α β fun a₀ a₁ ha =>
      show f (α a₀) = β a₁ by
        rw [← ha]; exact congr_fun hab a₀
  · intro hpn α β hab
    have : f ∘ α = β ∘ F.map f := by
      ext a₀
      exact hab a₀ (F.map f a₀) rfl
    exact hpn α β this

/-- The type expression for
`(X → X) → (X → X)` (the dinatural number
type). -/
def dinaturalTypeExpr : TypeExpr :=
  let x := TypeExpr.leaf (𝟭 Type)
  .arrow (.arrow x x) (.arrow x x)

/-- The relational interpretation of the
dinatural type expression agrees with
paranaturality: given endomorphism pairs
`(h, k)` with `f ∘ h = k ∘ f`, the conclusion
is `f ∘ φ₀ h = φ₁ k ∘ f`. -/
theorem dinaturalTypeExpr_relInterp_iff
    {I₀ I₁ : Type} (f : I₀ → I₁)
    (φ₀ : (I₀ → I₀) → (I₀ → I₀))
    (φ₁ : (I₁ → I₁) → (I₁ → I₁)) :
    dinaturalTypeExpr.relInterp f φ₀ φ₁ ↔
    ∀ (h : I₀ → I₀) (k : I₁ → I₁),
      f ∘ h = k ∘ f →
      f ∘ φ₀ h = φ₁ k ∘ f := by
  simp only [dinaturalTypeExpr, TypeExpr.relInterp,
    functorRelLift_graphRel, graphRel, arrowRel,
    Functor.id_map]
  constructor
  · intro hrel h k hhk
    ext a₀
    exact hrel h k
      (fun a₀' a₁' ha =>
        show f (h a₀') = k a₁' by
          rw [← ha]; exact congr_fun hhk a₀')
      a₀ (f a₀) rfl
  · intro hpn h k hhk a₀ a₁ ha
    change f (φ₀ h a₀) = φ₁ k a₁
    rw [← ha]
    have : f ∘ h = k ∘ f := by
      ext x
      exact hhk x (f x) rfl
    exact congr_fun (hpn h k this) a₀

/-- A parametric family for a type expression
`T` is a family of elements
`app I : T.interp I I` indexed by types `I`,
such that for every relation `R : I₀ → I₁ → Prop`,
the full relational interpretation
`T.fullRelInterp R` relates `app I₀` to `app I₁`.

This is Wadler's parametricity condition in its
full generality, where the relation at each type
variable is arbitrary (not restricted to function
graphs). -/
@[ext]
structure ParametricFamily (T : TypeExpr) where
  /-- The component at each type -/
  app : (I : Type) → T.interp I I
  /-- The parametricity condition -/
  parametric :
    ∀ (I₀ I₁ : Type) (R : I₀ → I₁ → Prop),
    T.fullRelInterp R (app I₀) (app I₁)

/-- Specialization of `ParametricFamily.parametric`
to the graph of a function: `T.fullRelInterp` at
`graphRel f` coincides with `T.relInterp f`. -/
theorem ParametricFamily.parametric_graphRel
    {T : TypeExpr} (p : ParametricFamily T)
    {I₀ I₁ : Type} (f : I₀ → I₁) :
    T.relInterp f (p.app I₀) (p.app I₁) :=
  T.fullRelInterp_graphRel f ▸
    p.parametric I₀ I₁ (graphRel f)

/-- A type abstraction for a type expression `T`
is a family of elements indexed by types, with no
condition imposed. This is Wadler's `∀X. T(X)` as
a type: an element of `TypeAbs T` assigns to each
type `I` an element of `T.interp I I`. -/
abbrev TypeAbs (T : TypeExpr) :=
  (I : Type) → T.interp I I

/-- Relatedness of type abstractions under the
full relational interpretation. Two type
abstractions `t₀` and `t₁` for a type expression
`T` are related if for every relation `R` between
types `I₀` and `I₁`, the elements `t₀ I₀` and
`t₁ I₁` are related by `T.fullRelInterp R`.

This is Wadler's relational interpretation of
`∀X. T(X)` ("Theorems for free!", section 2):
"polymorphic functions are related if they take
related types into related results". -/
def typeAbsRel (T : TypeExpr) (t₀ t₁ : TypeAbs T) :
    Prop :=
  ∀ (I₀ I₁ : Type) (R : I₀ → I₁ → Prop),
    T.fullRelInterp R (t₀ I₀) (t₁ I₁)

/-- Self-relatedness under `typeAbsRel` is
equivalent to the `ParametricFamily` parametricity
condition, since both quantify over all relations
with `fullRelInterp`. -/
theorem typeAbsRel_self_implies_parametric
    {T : TypeExpr} {t : TypeAbs T}
    (h : typeAbsRel T t t) :
    ∀ (I₀ I₁ : Type) (R : I₀ → I₁ → Prop),
      T.fullRelInterp R (t I₀) (t I₁) :=
  h

/-- A `ParametricFamily` from a self-related
type abstraction under `typeAbsRel`. -/
def ParametricFamily.ofTypeAbsRel
    {T : TypeExpr} (t : TypeAbs T)
    (h : typeAbsRel T t t) :
    ParametricFamily T where
  app := t
  parametric := h

/-- The relational interpretation of a type
expression relates the covariant and contravariant
projections of off-diagonal elements, and implies
the profunctor wedge condition. Both properties
are proved simultaneously by induction.

`relInterp_of_offDiag`: for `c : T.interp I₁ I₀`,
the pair `(T.profMap f id c, T.profMap id f c)` is
related by `T.relInterp f`. This is the analogue
of `diagCompat_of_offDiag` for `TypeExpr`.

`relInterp_implies_wedge`: if `T.relInterp f`
relates `x₀` and `x₁`, then
`T.profMap id f x₀ = T.profMap f id x₁`.
The converse holds for type expressions without
nested arrows (leaves and single-level arrows),
but fails for nested arrows such as
`((X → X) → X) → X` -- this is the
parametricity/paranaturality gap. -/
private theorem TypeExpr.relInterp_wedge_aux
    (T : TypeExpr) :
    (∀ {I₀ I₁ : Type} (f : I₀ → I₁)
      (c : T.interp I₁ I₀),
      T.relInterp f (T.profMap f id c)
        (T.profMap id f c)) ∧
    (∀ {I₀ I₁ : Type} (f : I₀ → I₁)
      (x₀ : T.interp I₀ I₀)
      (x₁ : T.interp I₁ I₁),
      T.relInterp f x₀ x₁ →
      T.profMap id f x₀ =
        T.profMap f id x₁) := by
  induction T with
  | var =>
    exact ⟨fun _ _ => rfl, fun _ _ _ h => h⟩
  | app F T ih =>
    obtain ⟨ih_od, ih_w⟩ := ih
    constructor
    · intro I₀ I₁ f c
      change functorRelLift F (T.relInterp f)
        (F.map (T.profMap f id) c)
        (F.map (T.profMap id f) c)
      let lift : T.interp I₁ I₀ →
          { p : T.interp I₀ I₀ ×
            T.interp I₁ I₁ //
            T.relInterp f p.1 p.2 } :=
        fun x => ⟨⟨T.profMap f id x,
          T.profMap id f x⟩, ih_od f x⟩
      exact ⟨F.map lift c,
        (FunctorToTypes.map_comp_apply F
          lift (fun s => s.val.1) c).symm,
        (FunctorToTypes.map_comp_apply F
          lift (fun s => s.val.2) c).symm⟩
    · intro I₀ I₁ f x₀ x₁ hrel
      change F.map (T.profMap id f) x₀ =
        F.map (T.profMap f id) x₁
      obtain ⟨w, hw₁, hw₂⟩ := hrel
      have heq :
          (fun (s : { p : T.interp I₀ I₀ ×
            T.interp I₁ I₁ //
            T.relInterp f p.1 p.2 }) =>
            T.profMap id f s.val.1) =
          (fun s =>
            T.profMap f id s.val.2) := by
        funext ⟨⟨a₀, a₁⟩, hr⟩
        exact ih_w f a₀ a₁ hr
      have lhs :
          F.map (T.profMap id f) x₀ =
          F.map
            (fun s => T.profMap id f s.val.1)
            w := by
        rw [← hw₁]
        exact (FunctorToTypes.map_comp_apply F
          (fun s => s.val.1)
          (T.profMap id f) w).symm
      have rhs :
          F.map
            (fun s => T.profMap f id s.val.2)
            w =
          F.map (T.profMap f id) x₁ := by
        rw [← hw₂]
        exact FunctorToTypes.map_comp_apply F
          (fun s => s.val.2)
          (T.profMap f id) w
      rw [lhs, heq, rhs]
  | arrow T₁ T₂ ih₁ ih₂ =>
    obtain ⟨ih₁_od, ih₁_w⟩ := ih₁
    obtain ⟨ih₂_od, ih₂_w⟩ := ih₂
    constructor
    · intro I₀ I₁ f c a₀ a₁ hrel₁
      change T₂.relInterp f
        (T₂.profMap f id
          (c (T₁.profMap id f a₀)))
        (T₂.profMap id f
          (c (T₁.profMap f id a₁)))
      rw [ih₁_w f a₀ a₁ hrel₁]
      exact ih₂_od f (c (T₁.profMap f id a₁))
    · intro I₀ I₁ f x₀ x₁ hrel
      funext c
      exact ih₂_w f _ _
        (hrel _ _ (ih₁_od f c))

/-- Off-diagonal elements produce related pairs:
`(T.profMap f id c, T.profMap id f c)` is related
by `T.relInterp f`. -/
theorem TypeExpr.relInterp_of_offDiag
    (T : TypeExpr) {I₀ I₁ : Type}
    (f : I₀ → I₁) (c : T.interp I₁ I₀) :
    T.relInterp f (T.profMap f id c)
      (T.profMap id f c) :=
  T.relInterp_wedge_aux.1 f c

/-- The relational interpretation implies the
profunctor wedge condition. -/
theorem TypeExpr.relInterp_implies_wedge
    (T : TypeExpr) {I₀ I₁ : Type}
    (f : I₀ → I₁)
    (x₀ : T.interp I₀ I₀)
    (x₁ : T.interp I₁ I₁)
    (hrel : T.relInterp f x₀ x₁) :
    T.profMap id f x₀ =
      T.profMap f id x₁ :=
  T.relInterp_wedge_aux.2 f x₀ x₁ hrel

/-- Every parametric family satisfies the
profunctor wedge condition: for each
`f : I₀ → I₁`,
`T.profMap id f (p.app I₀) =
T.profMap f id (p.app I₁)`. -/
theorem ParametricFamily.wedge
    {T : TypeExpr} (p : ParametricFamily T)
    {I₀ I₁ : Type} (f : I₀ → I₁) :
    T.profMap id f (p.app I₀) =
      T.profMap f id (p.app I₁) :=
  T.relInterp_implies_wedge f
    (p.app I₀) (p.app I₁)
    (p.parametric_graphRel f)

theorem idProf_diagCompat_eq
    {I₀ I₁ : Type} (f : I₀ → I₁)
    (x₀ : I₀) (x₁ : I₁) :
    DiagCompat IdProf I₀ I₁ f x₀ x₁ =
    (f x₀ = x₁) :=
  rfl

theorem algProf_diagCompat_eq
    (F : Type ⥤ Type) {I₀ I₁ : Type}
    (f : I₀ → I₁)
    (d₀ : F.obj I₀ → I₀)
    (d₁ : F.obj I₁ → I₁) :
    DiagCompat (AlgProf F) I₀ I₁ f d₀ d₁ =
    (f ∘ d₀ = d₁ ∘ F.map f) :=
  rfl

/-- Parametric families for the algebra type
expression `(F(X) → X) → X` are equivalent to
paranatural transformations from `AlgProf F` to
`IdProf`. -/
def algebraParametricEquivParanat
    (F : Type ⥤ Type) :
    ParametricFamily (algebraTypeExpr F) ≃
    Paranat (AlgProf F) IdProf where
  toFun p :=
    { app := p.app
      paranatural := fun I₀ I₁ f d₀ d₁ hdc => by
        rw [algProf_diagCompat_eq] at hdc
        rw [idProf_diagCompat_eq]
        exact (algebraTypeExpr_relInterp_iff
          F f (p.app I₀) (p.app I₁)).mp
          (p.parametric_graphRel f) d₀ d₁ hdc }
  invFun q :=
    { app := q.app
      parametric := fun I₀ I₁ R α β hrel => by
        simp only [TypeExpr.fullRelInterp,
          functorRelLift_id] at hrel ⊢
        let S := { p : I₀ × I₁ // R p.1 p.2 }
        let π₁ : S → I₀ := fun s => s.val.1
        let π₂ : S → I₁ := fun s => s.val.2
        let γ : F.obj S → S := fun w =>
          ⟨(α (F.map π₁ w), β (F.map π₂ w)),
           hrel _ _ ⟨w, rfl, rfl⟩⟩
        have hc₁ : DiagCompat (AlgProf F)
            S I₀ π₁ γ α := by
          rw [algProf_diagCompat_eq]; rfl
        have hp₁ := q.paranatural S I₀ π₁ γ α hc₁
        rw [idProf_diagCompat_eq] at hp₁
        have hc₂ : DiagCompat (AlgProf F)
            S I₁ π₂ γ β := by
          rw [algProf_diagCompat_eq]; rfl
        have hp₂ := q.paranatural S I₁ π₂ γ β hc₂
        rw [idProf_diagCompat_eq] at hp₂
        rw [← hp₁, ← hp₂]
        exact (q.app S γ).property }
  left_inv _ := by ext; rfl
  right_inv _ := by ext; rfl

/-- Elements of an initial F-algebra are in
bijection with parametric families for the
type expression `(F(X) → X) → X`. -/
def initialAlgebraParametricEquiv
    (F : Type ⥤ Type)
    (μF : Endofunctor.Algebra F)
    (hμF : Limits.IsInitial μF) :
    μF.a ≃ ParametricFamily (algebraTypeExpr F) :=
  (initialAlgebraParanatEquiv F μF hμF).trans
    (algebraParametricEquivParanat F).symm

theorem homProf_diagCompat_eq
    {I₀ I₁ : Type} (f : I₀ → I₁)
    (h : I₀ → I₀) (k : I₁ → I₁) :
    DiagCompat HomProf I₀ I₁ f h k =
    (f ∘ h = k ∘ f) :=
  rfl

/-- Parametric families for the dinatural type
expression `(X → X) → (X → X)` are equivalent
to endo-paranatural transformations of
`HomProf`. -/
def dinaturalParametricEquivParanat :
    ParametricFamily dinaturalTypeExpr ≃
    Paranat HomProf HomProf where
  toFun p :=
    { app := p.app
      paranatural := fun I₀ I₁ f d₀ d₁ hdc => by
        rw [homProf_diagCompat_eq] at hdc ⊢
        exact (dinaturalTypeExpr_relInterp_iff
          f (p.app I₀) (p.app I₁)).mp
          (p.parametric_graphRel f) d₀ d₁ hdc }
  invFun q :=
    { app := q.app
      parametric := fun I₀ I₁ R h₀ h₁ hrel
          x₀ x₁ hx => by
        simp only [TypeExpr.leaf,
          TypeExpr.fullRelInterp,
          functorRelLift_id] at hrel hx ⊢
        let S := { p : I₀ × I₁ // R p.1 p.2 }
        let π₁ : S → I₀ := fun s => s.val.1
        let π₂ : S → I₁ := fun s => s.val.2
        let hS : S → S := fun s =>
          ⟨(h₀ s.val.1, h₁ s.val.2),
           hrel s.val.1 s.val.2 s.property⟩
        have hc₁ : DiagCompat HomProf
            S I₀ π₁ hS h₀ := by
          rw [homProf_diagCompat_eq]; rfl
        have hp₁ := q.paranatural S I₀ π₁
          hS h₀ hc₁
        rw [homProf_diagCompat_eq] at hp₁
        have hc₂ : DiagCompat HomProf
            S I₁ π₂ hS h₁ := by
          rw [homProf_diagCompat_eq]; rfl
        have hp₂ := q.paranatural S I₁ π₂
          hS h₁ hc₂
        rw [homProf_diagCompat_eq] at hp₂
        let s : S := ⟨(x₀, x₁), hx⟩
        change R ((q.app I₀ h₀ ∘ π₁) s)
          ((q.app I₁ h₁ ∘ π₂) s)
        rw [← hp₁, ← hp₂]
        exact (q.app S hS s).property }
  left_inv _ := by ext; rfl
  right_inv _ := by ext; rfl

/-- Natural numbers are in bijection with
parametric families for the dinatural type
expression `(X → X) → (X → X)`. -/
def dinaturalNumbersParametricEquiv :
    ℕ ≃ ParametricFamily dinaturalTypeExpr :=
  dinaturalNumbersEquiv.trans
    dinaturalParametricEquivParanat.symm

/-- The type expression for `X → X` (the
identity / hom type). -/
abbrev homTypeExpr : TypeExpr :=
  .arrow .var .var

/-- Every parametric family for `homTypeExpr`
(`X → X`) is the identity: specializing
parametricity at `f = (fun _ => a) : Unit → I`
forces `app I a = a`. -/
theorem homTypeExpr_parametric_is_id
    (p : ParametricFamily homTypeExpr)
    (I : Type) : p.app I = id := by
  funext a
  have h := p.parametric_graphRel
    (fun (_ : Unit) => a)
  simp only [TypeExpr.relInterp,
    graphRel, arrowRel] at h
  exact (h () a rfl).symm

/-- Parametric families for `homTypeExpr`
(`X → X`) are equivalent to `Unit`: the identity
is the unique parametric inhabitant.

This is Wadler's "Theorems for free!" identity
free theorem: `∀X. X → X ≅ 1`. -/
def homParametricEquivUnit :
    ParametricFamily homTypeExpr ≃ Unit where
  toFun _ := ()
  invFun _ :=
    { app := fun _ => id
      parametric := fun _ _ R => by
        simp only [TypeExpr.fullRelInterp, arrowRel]
        exact fun _ _ h => h }
  left_inv p :=
    ParametricFamily.ext
      (funext fun I =>
        (homTypeExpr_parametric_is_id p I).symm)
  right_inv u := by cases u; rfl

/-- Parametric families for the dialgebra type
expression `F(X) → G(X)` are equivalent to
natural transformations `F ⟶ G`.

The parametricity condition at a morphism
`f : I₀ → I₁` reduces (via
`dialgebraTypeExpr_relInterp_iff`) to the
naturality square
`G.map f ∘ app I₀ = app I₁ ∘ F.map f`. -/
def dialgebraParametricEquivNatTrans
    (F G : Type ⥤ Type) :
    ParametricFamily (dialgebraTypeExpr F G) ≃
    (F ⟶ G) where
  toFun p :=
    { app := p.app
      naturality := fun {I₀ I₁} f =>
        ((dialgebraTypeExpr_relInterp_iff
          F G f (p.app I₀) (p.app I₁)).mp
          (p.parametric_graphRel f)).symm }
  invFun η :=
    { app := η.app
      parametric := fun I₀ I₁ R a₀ a₁ ha => by
        simp only [TypeExpr.fullRelInterp] at ha ⊢
        obtain ⟨w, hw₁, hw₂⟩ := ha
        exact ⟨η.app _ w,
          by rw [← FunctorToTypes.naturality,
            hw₁]; rfl,
          by rw [← FunctorToTypes.naturality,
            hw₂]; rfl⟩ }
  left_inv _ := by ext; rfl
  right_inv _ := by ext; rfl

section TypeExprWedges

universe u_pw

/-- A wedge into the parametric-family end for a
type expression `T`. The vertex is a type `pt`,
equipped with projections into each diagonal
`T.interp I I` satisfying the full relational
parametricity condition. -/
structure TypeExprWedge
    (T : TypeExpr) where
  /-- The vertex type -/
  pt : Type u_pw
  /-- The projection at each type -/
  proj : (I : Type) → pt → T.interp I I
  /-- The parametricity condition -/
  parametric :
    ∀ (w : pt) (I₀ I₁ : Type)
      (R : I₀ → I₁ → Prop),
    T.fullRelInterp R (proj I₀ w) (proj I₁ w)

/-- `ParametricFamily T` forms a `TypeExprWedge T`
with projections given by `ParametricFamily.app`. -/
def ParametricFamily.toWedge
    (T : TypeExpr) : TypeExprWedge T where
  pt := ParametricFamily T
  proj I p := p.app I
  parametric w := w.parametric

/-- The mediating morphism from any wedge to
`ParametricFamily T`. -/
def TypeExprWedge.toParametricFamily
    {T : TypeExpr} (W : TypeExprWedge T)
    (w : W.pt) : ParametricFamily T where
  app I := W.proj I w
  parametric := W.parametric w

@[simp]
theorem TypeExprWedge.toParametricFamily_app
    {T : TypeExpr} (W : TypeExprWedge T)
    (w : W.pt) (I : Type) :
    (W.toParametricFamily w).app I =
      W.proj I w :=
  rfl

/-- Any map `f : W.pt → ParametricFamily T`
commuting with projections equals
`W.toParametricFamily`. -/
theorem TypeExprWedge.toParametricFamily_unique
    {T : TypeExpr} (W : TypeExprWedge T)
    (f : W.pt → ParametricFamily T)
    (hf : ∀ (w : W.pt) (I : Type),
      (f w).app I = W.proj I w) :
    f = W.toParametricFamily :=
  funext fun w =>
    ParametricFamily.ext (funext fun I => hf w I)

/-- The relational fiber of `T` at `R`: the
subtype of pairs `(x, y)` satisfying
`fullRelInterp T R x y`. -/
def TypeExpr.relFiber
    (T : TypeExpr) {I₀ I₁ : Type}
    (R : I₀ → I₁ → Prop) :=
  { p : T.interp I₀ I₀ × T.interp I₁ I₁ //
    T.fullRelInterp R p.1 p.2 }

/-- For the diagonal (equality) relation, the two
components of a relational fiber element
coincide. -/
theorem TypeExpr.relFiber_diag_eq
    (T : TypeExpr) {I : Type}
    (p : T.relFiber
      (fun (a : I) (b : I) => a = b)) :
    p.val.1 = p.val.2 := by
  have hp : T.fullRelInterp
      (fun (a : I) (b : I) => a = b)
      p.val.1 p.val.2 :=
    p.property
  have heq :
      (fun (a : I) (b : I) => a = b) =
        graphRel id := by
    ext a b; simp [graphRel]
  have hp' : T.relInterp id p.val.1 p.val.2 :=
    (T.fullRelInterp_graphRel id ▸ heq ▸ hp)
  have hw := T.relInterp_implies_wedge
    id p.val.1 p.val.2 hp'
  simp only [profMap_id_id] at hw
  exact hw

/-- A parametric cone for `T : TypeExpr` has
projections indexed by relations rather than types.
For each relation `R : I₀ → I₁ → Prop`, the
projection gives a pair of diagonal elements
satisfying the relational condition, with
compatibility: projections at different relations
sharing an endpoint agree on that endpoint. -/
@[ext]
structure TypeExprCone
    (T : TypeExpr) where
  /-- The vertex type -/
  pt : Type u_pw
  /-- For each relation, a pair of diagonal
  elements satisfying the relational condition -/
  proj : ∀ {I₀ I₁ : Type}
    (R : I₀ → I₁ → Prop),
    pt → T.relFiber R
  /-- Compatibility at the source: for relations
  sharing a source type, the first components
  agree. -/
  compatFst :
    ∀ {I₀ I₁ I₁' : Type}
    (R : I₀ → I₁ → Prop)
    (S : I₀ → I₁' → Prop) (w : pt),
    (proj R w).val.1 = (proj S w).val.1
  /-- Compatibility at the target: for relations
  sharing a target type, the second components
  agree. -/
  compatSnd :
    ∀ {I₀ I₀' I₁ : Type}
    (R : I₀ → I₁ → Prop)
    (S : I₀' → I₁ → Prop) (w : pt),
    (proj R w).val.2 = (proj S w).val.2

/-- A morphism of parametric cones: a function
on vertices that commutes with all
relation-indexed projections. -/
@[ext]
structure TypeExprConeMorphism
    {T : TypeExpr}
    (C₁ C₂ : TypeExprCone.{u_pw} T) where
  /-- The underlying function on vertices -/
  func : C₁.pt → C₂.pt
  /-- Commutativity with projections -/
  comm :
    ∀ {I₀ I₁ : Type}
    (R : I₀ → I₁ → Prop) (w : C₁.pt),
    C₂.proj R (func w) = C₁.proj R w

/-- Conversion from parametric wedge to
parametric cone. -/
def TypeExprWedge.toCone
    {T : TypeExpr}
    (W : TypeExprWedge.{u_pw} T) :
    TypeExprCone.{u_pw} T where
  pt := W.pt
  proj R w :=
    ⟨(W.proj _ w, W.proj _ w),
     W.parametric w _ _ R⟩
  compatFst _ _ _ := rfl
  compatSnd _ _ _ := rfl

/-- Conversion from parametric cone to
parametric wedge: extract the diagonal
projection from any self-relation, with
the parametric condition from the
relation-indexed projections. -/
def TypeExprCone.toWedge
    {T : TypeExpr}
    (C : TypeExprCone.{u_pw} T) :
    TypeExprWedge.{u_pw} T where
  pt := C.pt
  proj I w := (C.proj (fun a b => a = b) w).val.1
  parametric w I₀ I₁ R := by
    have hfst :
      (C.proj (fun (a : I₀) (b : I₀) =>
        a = b) w).val.1 =
      (C.proj R w).val.1 :=
      (C.compatFst
        (fun a b => a = b) R w)
    have hdiag :
      (C.proj (fun (a : I₁) (b : I₁) =>
        a = b) w).val.1 =
      (C.proj (fun (a : I₁) (b : I₁) =>
        a = b) w).val.2 :=
      T.relFiber_diag_eq
        (C.proj (fun a b => a = b) w)
    have hsnd :
      (C.proj (fun (a : I₁) (b : I₁) =>
        a = b) w).val.2 =
      (C.proj R w).val.2 :=
      C.compatSnd (fun a b => a = b) R w
    rw [hfst, hdiag, hsnd]
    exact (C.proj R w).property

/-- Converting a wedge to a cone and back gives
the original wedge. -/
theorem TypeExprCone.toWedge_toCone
    {T : TypeExpr}
    (W : TypeExprWedge.{u_pw} T) :
    W.toCone.toWedge = W := by
  cases W; rfl

/-- Converting a cone to a wedge and back gives
the original cone. -/
theorem TypeExprWedge.toCone_toWedge
    {T : TypeExpr}
    (C : TypeExprCone.{u_pw} T) :
    C.toWedge.toCone = C := by
  cases C with | mk pt proj cFst cSnd =>
  simp only [TypeExprCone.toWedge,
    TypeExprWedge.toCone]
  congr 1
  funext I₀ I₁ R w
  apply Subtype.ext
  apply Prod.ext
  · exact cFst (fun a b => a = b) R w
  · exact (T.relFiber_diag_eq
      (proj (fun a b => a = b) w)).trans
      (cSnd (fun a b => a = b) R w)

/-- A morphism of parametric wedges from `W₁` to
`W₂`: a function on vertices that commutes with
the projections. -/
@[ext]
structure TypeExprWedgeMorphism
    {T : TypeExpr}
    (W₁ W₂ : TypeExprWedge.{u_pw} T) where
  /-- The underlying function on vertices -/
  func : W₁.pt → W₂.pt
  /-- Commutativity with projections -/
  comm :
    ∀ (I : Type) (w : W₁.pt),
    W₂.proj I (func w) = W₁.proj I w

/-- The morphism from any wedge (at universe 1)
to `ParametricFamily.toWedge`, given by
`toParametricFamily`. -/
def TypeExprWedge.toTerminal
    {T : TypeExpr}
    (W : TypeExprWedge.{1} T) :
    TypeExprWedgeMorphism W
      (ParametricFamily.toWedge T) where
  func := W.toParametricFamily
  comm _ _ := rfl

/-- `toTerminal` is the unique morphism to
`ParametricFamily.toWedge`: any morphism
`f : W ⟶ ParametricFamily.toWedge T` equals
`toTerminal`. -/
theorem TypeExprWedge.toTerminal_unique
    {T : TypeExpr}
    (W : TypeExprWedge.{1} T)
    (f : TypeExprWedgeMorphism W
      (ParametricFamily.toWedge T)) :
    f = W.toTerminal := by
  ext w
  exact ParametricFamily.ext
    (funext fun I => f.comm I w)

instance (T : TypeExpr) :
    Category (TypeExprWedge.{u_pw} T) where
  Hom := TypeExprWedgeMorphism
  id W :=
    { func := id
      comm := fun _ _ => rfl }
  comp f g :=
    { func := g.func ∘ f.func
      comm := fun I w => by
        simp only [Function.comp_apply,
          g.comm, f.comm] }
  id_comp _ := TypeExprWedgeMorphism.ext rfl
  comp_id _ := TypeExprWedgeMorphism.ext rfl
  assoc _ _ _ :=
    TypeExprWedgeMorphism.ext rfl

/-- `ParametricFamily.toWedge T` is the terminal
object in the category of parametric wedges
(at universe 1). -/
def typeExprWedge_isTerminal
    (T : TypeExpr) :
    Limits.IsTerminal
      (ParametricFamily.toWedge T) :=
  Limits.IsTerminal.ofUniqueHom
    (fun W =>
      TypeExprWedge.toTerminal W)
    (fun W f =>
      TypeExprWedge.toTerminal_unique
        W f)

instance (T : TypeExpr) :
    Category (TypeExprCone.{u_pw} T) where
  Hom := TypeExprConeMorphism
  id C :=
    { func := id
      comm := fun _ _ => rfl }
  comp f g :=
    { func := g.func ∘ f.func
      comm := fun R w => by
        simp only [Function.comp_apply,
          g.comm, f.comm] }
  id_comp _ :=
    TypeExprConeMorphism.ext rfl
  comp_id _ :=
    TypeExprConeMorphism.ext rfl
  assoc _ _ _ :=
    TypeExprConeMorphism.ext rfl

/-- The functor from parametric wedges to
parametric cones, applying `toCone` on objects
and transporting morphisms. -/
def typeExprWedgeToCone
    (T : TypeExpr) :
    TypeExprWedge.{u_pw} T ⥤
      TypeExprCone.{u_pw} T where
  obj W := W.toCone
  map f :=
    { func := f.func
      comm := fun R w => by
        simp only [TypeExprWedge.toCone]
        exact Subtype.ext (Prod.ext
          (f.comm _ w)
          (f.comm _ w)) }
  map_id _ :=
    TypeExprConeMorphism.ext rfl
  map_comp _ _ :=
    TypeExprConeMorphism.ext rfl

/-- The functor from parametric cones to
parametric wedges, applying `toWedge` on objects
and transporting morphisms. -/
def typeExprConeToWedge
    (T : TypeExpr) :
    TypeExprCone.{u_pw} T ⥤
      TypeExprWedge.{u_pw} T where
  obj C := C.toWedge
  map f :=
    { func := f.func
      comm := fun I w => by
        simp only [TypeExprCone.toWedge]
        have := f.comm
          (fun (a : I) (b : I) => a = b) w
        exact congrArg
          (fun p => p.val.1)
          this }
  map_id _ :=
    TypeExprWedgeMorphism.ext rfl
  map_comp _ _ :=
    TypeExprWedgeMorphism.ext rfl

/-- The categories `TypeExprWedge T` and
`TypeExprCone T` are equivalent.  The functors
`toCone` and `toWedge` are mutually inverse:
the unit is the identity (wedge-to-cone-to-wedge
is definitionally equal), and the counit uses
`relFiber_diag_eq` and the compatibility
conditions. -/
def typeExprWedgeConeEquivalence
    (T : TypeExpr) :
    TypeExprWedge.{u_pw} T ≌
      TypeExprCone.{u_pw} T where
  functor := typeExprWedgeToCone T
  inverse := typeExprConeToWedge T
  unitIso := NatIso.ofComponents
    (fun W => {
      hom :=
        { func := id
          comm := fun I w => by
            dsimp [typeExprConeToWedge,
              typeExprWedgeToCone,
              TypeExprWedge.toCone,
              TypeExprCone.toWedge] }
      inv :=
        { func := id
          comm := fun I w => by
            dsimp [typeExprConeToWedge,
              typeExprWedgeToCone,
              TypeExprWedge.toCone,
              TypeExprCone.toWedge] }
      hom_inv_id :=
        TypeExprWedgeMorphism.ext rfl
      inv_hom_id :=
        TypeExprWedgeMorphism.ext rfl })
    (fun f =>
      TypeExprWedgeMorphism.ext rfl)
  counitIso := NatIso.ofComponents
    (fun C => {
      hom :=
        { func := id
          comm := fun R w => by
            dsimp [typeExprWedgeToCone,
              typeExprConeToWedge,
              TypeExprWedge.toCone,
              TypeExprCone.toWedge]
            exact (Subtype.ext (Prod.ext
              (C.compatFst
                (fun a b => a = b) R w)
              ((T.relFiber_diag_eq _).trans
                (C.compatSnd
                  (fun a b => a = b)
                  R w)))).symm }
      inv :=
        { func := id
          comm := fun R w => by
            dsimp [typeExprWedgeToCone,
              typeExprConeToWedge,
              TypeExprWedge.toCone,
              TypeExprCone.toWedge]
            exact Subtype.ext (Prod.ext
              (C.compatFst
                (fun a b => a = b) R w)
              ((T.relFiber_diag_eq _).trans
                (C.compatSnd
                  (fun a b => a = b)
                  R w))) }
      hom_inv_id :=
        TypeExprConeMorphism.ext rfl
      inv_hom_id :=
        TypeExprConeMorphism.ext rfl })
    (fun f =>
      TypeExprConeMorphism.ext rfl)

/-- The composite functor
`typeExprWedgeToCone ⋙ typeExprConeToWedge`
equals the identity on `TypeExprWedge T`. -/
theorem typeExprWedgeToCone_comp_toWedge
    (T : TypeExpr) :
    typeExprWedgeToCone T ⋙
      typeExprConeToWedge T =
    𝟭 (TypeExprWedge.{u_pw} T) :=
  _root_.CategoryTheory.Functor.ext
    (fun W =>
      TypeExprCone.toWedge_toCone W)

/-- The composite functor
`typeExprConeToWedge ⋙ typeExprWedgeToCone`
equals the identity on `TypeExprCone T`. -/
theorem typeExprConeToWedge_comp_toCone
    (T : TypeExpr) :
    typeExprConeToWedge T ⋙
      typeExprWedgeToCone T =
    𝟭 (TypeExprCone.{u_pw} T) :=
  _root_.CategoryTheory.Functor.ext
    (fun C =>
      TypeExprWedge.toCone_toWedge C)
    (fun _X _Y f =>
      TypeExprConeMorphism.ext
        (funext fun w => by
          have eqToHom_func :
            ∀ (A B : TypeExprCone.{u_pw} T)
            (h : A = B) (x : A.pt),
            (eqToHom h).func x =
              cast (congrArg
                TypeExprCone.pt
                h) x := by
            intro A B h x; subst h; rfl
          have comp_func :
            ∀ (A B C :
              TypeExprCone.{u_pw} T)
            (g : A ⟶ B) (h : B ⟶ C)
            (x : A.pt),
            (g ≫ h).func x =
              h.func (g.func x) := by
            intros; rfl
          change f.func w = _
          simp only [Functor.id_map,
            comp_func, eqToHom_func,
            cast_eq]))

/-- The categories `TypeExprWedge T` and
`TypeExprCone T` are isomorphic
in `Cat`. -/
def typeExprWedgeConeIso
    (T : TypeExpr) :
    TypeExprWedge.{u_pw} T ≅Cat
      TypeExprCone.{u_pw} T where
  hom := (typeExprWedgeToCone T).toCatHom
  inv := (typeExprConeToWedge T).toCatHom
  hom_inv_id := Cat.Hom.ext
    (typeExprWedgeToCone_comp_toWedge T)
  inv_hom_id := Cat.Hom.ext
    (typeExprConeToWedge_comp_toCone T)

end TypeExprWedges

section TypeExprCategory

/-- Wrapper around `TypeExpr` to serve as
the object type for the category of type
expressions with parametric families as
morphisms. -/
@[ext]
structure TypeExprCat where
  /-- The underlying type expression. -/
  expr : TypeExpr

/-- The identity morphism in the category of
type expressions: a parametric family for
`.arrow T T` whose component at each type `I`
is the identity function. -/
def typeExprId (T : TypeExpr) :
    ParametricFamily (.arrow T T) where
  app _ := id
  parametric _ _ R := by
    simp only [TypeExpr.fullRelInterp, arrowRel]
    exact fun _ _ h => h

/-- Composition of morphisms in the category of
type expressions: given parametric families
`η : ParametricFamily (.arrow T₁ T₂)` and
`μ : ParametricFamily (.arrow T₂ T₃)`, their
composite is the pointwise composition
`μ.app I ∘ η.app I` at each type `I`. -/
def typeExprComp {T₁ T₂ T₃ : TypeExpr}
    (η : ParametricFamily (.arrow T₁ T₂))
    (μ : ParametricFamily (.arrow T₂ T₃)) :
    ParametricFamily (.arrow T₁ T₃) where
  app I := μ.app I ∘ η.app I
  parametric I₀ I₁ R := by
    simp only [TypeExpr.fullRelInterp, arrowRel]
    intro x₀ x₁ h
    have hη := η.parametric I₀ I₁ R
    simp only [TypeExpr.fullRelInterp,
      arrowRel] at hη
    have hμ := μ.parametric I₀ I₁ R
    simp only [TypeExpr.fullRelInterp,
      arrowRel] at hμ
    exact hμ _ _ (hη x₀ x₁ h)

/-- The category of type expressions, with
morphisms given by parametric families.
A morphism from `T₁` to `T₂` is a
`ParametricFamily (.arrow T₁ T₂)`: a family
of functions `T₁.interp I I → T₂.interp I I`
indexed by types `I`, satisfying the full
parametricity condition. -/
instance : Category TypeExprCat where
  Hom T₁ T₂ :=
    ParametricFamily (.arrow T₁.expr T₂.expr)
  id T := typeExprId T.expr
  comp η μ := typeExprComp η μ
  id_comp _ :=
    ParametricFamily.ext (funext fun _ => rfl)
  comp_id _ :=
    ParametricFamily.ext (funext fun _ => rfl)
  assoc _ _ _ :=
    ParametricFamily.ext (funext fun _ => rfl)

/-- The unit object of the category of type
expressions. Its underlying type expression
interprets as `PUnit` at every type. -/
def typeExprUnit : TypeExprCat :=
  ⟨TypeExpr.unit⟩

/-- Morphisms from the unit object to `⟨T⟩`
in the category of type expressions are in
bijection with parametric families for `T`.
A morphism `typeExprUnit ⟶ ⟨T⟩` is a
`ParametricFamily (.arrow .unit T)`, which
assigns to each type `I` a function
`PUnit → T.interp I I`. Evaluating at
`PUnit.unit` extracts the element, and
wrapping an element as a constant function
inverts this. -/
def typeExprHomUnitEquiv
    (T : TypeExpr) :
    (typeExprUnit ⟶ ⟨T⟩) ≃
      ParametricFamily T where
  toFun η :=
    { app := fun I => η.app I PUnit.unit
      parametric := fun I₀ I₁ R =>
        η.parametric I₀ I₁ R
          PUnit.unit PUnit.unit
          (TypeExpr.unit_fullRelInterp
            R PUnit.unit PUnit.unit) }
  invFun p :=
    { app := fun I _ => p.app I
      parametric := fun I₀ I₁ R =>
        fun _ _ _ => p.parametric I₀ I₁ R }
  left_inv η :=
    ParametricFamily.ext (funext fun I =>
      funext fun u => by cases u; rfl)
  right_inv _ :=
    ParametricFamily.ext (funext fun _ => rfl)

/-- `Hom(var, var)` in the category of type
expressions is equivalent to `Unit`: the
identity is the unique parametric family for
`X → X`. -/
def typeExprHom_var_var :
    ((TypeExprCat.mk .var) ⟶
      (TypeExprCat.mk .var)) ≃ Unit :=
  homParametricEquivUnit

/-- `Hom(leaf F, leaf G)` in the category of
type expressions is equivalent to `F ⟶ G`:
parametric families for the dialgebra type
expression `F(X) → G(X)` correspond to
natural transformations from `F` to `G`. -/
def typeExprHom_leaf_leaf
    (F G : Type ⥤ Type) :
    ((TypeExprCat.mk (.leaf F)) ⟶
      (TypeExprCat.mk (.leaf G))) ≃
        (F ⟶ G) :=
  dialgebraParametricEquivNatTrans F G

/-- `Hom(unit, algebraTypeExpr F)` in the
category of type expressions is equivalent
to the carrier of any initial `F`-algebra:
via the unit representability equivalence
composed with the parametric-family
characterization of initial algebra elements.
-/
def typeExprHomUnit_algebra
    (F : Type ⥤ Type)
    (μF : Endofunctor.Algebra F)
    (hμF : Limits.IsInitial μF) :
    (typeExprUnit ⟶
      TypeExprCat.mk (algebraTypeExpr F)) ≃
        μF.a :=
  (typeExprHomUnitEquiv _).trans
    (initialAlgebraParametricEquiv
      F μF hμF).symm

end TypeExprCategory

section RelSpanDiagram

/-- The diagram functor for a type expression `T`.
Maps type-nodes to `ULift (T.interp I I)` and
relation-nodes to `ULift (T.relFiber R)`. -/
def relSpanDiagram (T : TypeExpr) :
    RelSpanObj ⥤ Type 1 where
  obj
    | .typeNode I => ULift.{1} (T.interp I I)
    | .relNode I₀ I₁ R =>
      ULift.{1} (T.relFiber R)
  map {X Y} f :=
    match X, Y, f with
    | _, _, .id _ => id
    | _, _, .fstProj _ _ _ =>
      fun ⟨p⟩ => ⟨p.val.1⟩
    | _, _, .sndProj _ _ _ =>
      fun ⟨p⟩ => ⟨p.val.2⟩
  map_id := by
    intro X
    cases X <;> rfl
  map_comp := by
    intro X Y Z f g
    cases f <;> cases g <;> rfl

abbrev RelSpanCone (T : TypeExpr) :=
  Limits.Cone (relSpanDiagram T)

/-- The cone over `relSpanDiagram T` with vertex
`ULift (ParametricFamily T)`.  The type-node
projections extract `p.app I`; the relation-node
projections extract the relational fiber
witness `⟨(p.app I₀, p.app I₁), p.parametric⟩`. -/
def parametricFamilyCone (T : TypeExpr) :
    RelSpanCone T where
  pt := ULift.{1} (ParametricFamily T)
  π :=
    { app := fun X =>
        match X with
        | .typeNode I =>
          fun ⟨p⟩ => ⟨p.app I⟩
        | .relNode I₀ I₁ R =>
          fun ⟨p⟩ =>
            ⟨⟨(p.app I₀, p.app I₁),
              p.parametric I₀ I₁ R⟩⟩
      naturality := by
        intro X Y f
        cases f <;> rfl }

/-- Given a cone `s` over `relSpanDiagram T`
and a point `x : s.pt`, the parametricity
condition holds for the components extracted
from type-node projections. -/
theorem relSpanCone_parametric
    {T : TypeExpr}
    (s : RelSpanCone T)
    (x : s.pt)
    (I₀ I₁ : Type) (R : I₀ → I₁ → Prop) :
    T.fullRelInterp R
      (s.π.app (.typeNode I₀) x).down
      (s.π.app (.typeNode I₁) x).down := by
  have hw₁ := congr_fun (s.w
    (RelSpanHom.fstProj I₀ I₁ R)) x
  have hw₂ := congr_fun (s.w
    (RelSpanHom.sndProj I₀ I₁ R)) x
  simp only [types_comp_apply] at hw₁ hw₂
  let fiber := (s.π.app (.relNode I₀ I₁ R) x).down
  have hfib := fiber.property
  have h₁ : fiber.val.1 =
      (s.π.app (.typeNode I₀) x).down := by
    exact congr_arg ULift.down hw₁
  have h₂ : fiber.val.2 =
      (s.π.app (.typeNode I₁) x).down := by
    exact congr_arg ULift.down hw₂
  rw [← h₁, ← h₂]
  exact hfib

/-- `ParametricFamily T` is the limit of
`relSpanDiagram T`.  The lift extracts
type-node components; parametricity follows
from the cone's naturality at projection
morphisms. -/
def parametricFamilyIsLimit (T : TypeExpr) :
    Limits.IsLimit
      (parametricFamilyCone T) :=
  Limits.IsLimit.mk
    (fun s => fun x =>
      ⟨{ app := fun I =>
           (s.π.app (.typeNode I) x).down
         parametric := fun I₀ I₁ R =>
           relSpanCone_parametric
             s x I₀ I₁ R }⟩)
    (by
      intro s j
      cases j with
      | typeNode I => rfl
      | relNode I₀ I₁ R =>
        funext x
        apply ULift.ext
        apply Subtype.ext
        apply Prod.ext
        · exact (congr_arg ULift.down
            (congr_fun (s.w
              (RelSpanHom.fstProj I₀ I₁ R))
              x)).symm
        · exact (congr_arg ULift.down
            (congr_fun (s.w
              (RelSpanHom.sndProj I₀ I₁ R))
              x)).symm)
    (by
      intro s m hm
      funext x
      apply ULift.ext
      ext I
      exact congr_arg ULift.down
        (congr_fun (hm (.typeNode I)) x))

/-- The functor from `TypeExprWedge.{1} T` to
`RelSpanCone T`, sending a wedge to the cone
whose type-node projections are `ULift`-wrapped
wedge projections and whose relation-node
projections pair the projections with the
parametricity witness. -/
def wedgeToRelSpanCone (T : TypeExpr) :
    TypeExprWedge.{1} T ⥤
    RelSpanCone T where
  obj W :=
    { pt := W.pt
      π :=
        { app := fun X =>
            match X with
            | .typeNode I =>
              fun w => ⟨W.proj I w⟩
            | .relNode I₀ I₁ R =>
              fun w =>
                ⟨⟨(W.proj I₀ w, W.proj I₁ w),
                  W.parametric w I₀ I₁ R⟩⟩
          naturality := by
            intro X Y f
            cases f <;> rfl } }
  map f :=
    { hom := f.func
      w := by
        intro j
        cases j with
        | typeNode I =>
          funext w
          simp only [types_comp_apply]
          exact congrArg ULift.up
            (f.comm I w)
        | relNode I₀ I₁ R =>
          funext w
          simp only [types_comp_apply]
          apply ULift.ext
          apply Subtype.ext
          apply Prod.ext
          · exact f.comm I₀ w
          · exact f.comm I₁ w }
  map_id _ := by
    apply Limits.ConeMorphism.ext; rfl
  map_comp _ _ := by
    apply Limits.ConeMorphism.ext; rfl

/-- The functor from `RelSpanCone T` to
`TypeExprWedge.{1} T`, extracting wedge
projections from the type-node components of
the cone via `ULift.down`, with parametricity
from `relSpanCone_parametric`. -/
def relSpanConeToWedge (T : TypeExpr) :
    RelSpanCone T ⥤
    TypeExprWedge.{1} T where
  obj s :=
    { pt := s.pt
      proj := fun I w =>
        (s.π.app (.typeNode I) w).down
      parametric := fun w I₀ I₁ R =>
        relSpanCone_parametric s w I₀ I₁ R }
  map f :=
    { func := f.hom
      comm := fun I w => by
        exact congr_arg ULift.down
          (congr_fun
            (f.w (.typeNode I)) w) }
  map_id _ :=
    TypeExprWedgeMorphism.ext rfl
  map_comp _ _ :=
    TypeExprWedgeMorphism.ext rfl

/-- The composite
`wedgeToRelSpanCone T ⋙ relSpanConeToWedge T`
is naturally isomorphic to the identity on
`TypeExprWedge.{1} T`. -/
def wedgeRelSpanConeUnitIso
    (T : TypeExpr) :
    𝟭 (TypeExprWedge.{1} T) ≅
    wedgeToRelSpanCone T ⋙
      relSpanConeToWedge T :=
  NatIso.ofComponents
    (fun _ => Iso.refl _)
    (fun _ =>
      TypeExprWedgeMorphism.ext rfl)

/-- The composite cone
`relSpanConeToWedge T ⋙ wedgeToRelSpanCone T`
applied to `s` equals `s`. -/
theorem relSpanCone_roundtrip_π
    {T : TypeExpr}
    (s : RelSpanCone T)
    (j : RelSpanObj) :
    ((wedgeToRelSpanCone T).obj
      ((relSpanConeToWedge T).obj s)).π.app
        j =
    s.π.app j := by
  cases j with
  | typeNode I =>
    funext x
    simp only [wedgeToRelSpanCone,
      relSpanConeToWedge]
    exact ULift.ext _ _
      (ULift.down_up _)
  | relNode I₀ I₁ R =>
    funext x
    simp only [wedgeToRelSpanCone,
      relSpanConeToWedge]
    apply ULift.ext
    apply Subtype.ext
    apply Prod.ext
    · simp only []
      exact (congr_arg ULift.down
        (congr_fun (s.w
          (RelSpanHom.fstProj I₀ I₁ R))
          x)).symm
    · simp only []
      exact (congr_arg ULift.down
        (congr_fun (s.w
          (RelSpanHom.sndProj I₀ I₁ R))
          x)).symm

theorem relSpanCone_roundtrip
    {T : TypeExpr}
    (s : RelSpanCone T) :
    (wedgeToRelSpanCone T).obj
      ((relSpanConeToWedge T).obj s) =
    s := by
  cases s with
  | mk pt π =>
    simp only [wedgeToRelSpanCone,
      relSpanConeToWedge]
    congr 1
    exact NatTrans.ext (funext fun j =>
      relSpanCone_roundtrip_π ⟨pt, π⟩ j)

/-- The composite
`relSpanConeToWedge T ⋙ wedgeToRelSpanCone T`
is naturally isomorphic to the identity on
`RelSpanCone T`. -/
def wedgeRelSpanConeCounitIso
    (T : TypeExpr) :
    relSpanConeToWedge T ⋙
      wedgeToRelSpanCone T ≅
    𝟭 (RelSpanCone T) :=
  NatIso.ofComponents
    (fun s =>
      eqToIso (relSpanCone_roundtrip s))
    (fun {s₁ s₂} f => by
      apply Limits.ConeMorphism.ext
      simp [wedgeToRelSpanCone,
        relSpanConeToWedge])

/-- `TypeExprWedge.{1} T` is equivalent as a
category to `RelSpanCone T`, the category of
cones over the relational span diagram. -/
def wedgeRelSpanConeEquivalence
    (T : TypeExpr) :
    TypeExprWedge.{1} T ≌
    RelSpanCone T where
  functor := wedgeToRelSpanCone T
  inverse := relSpanConeToWedge T
  unitIso := wedgeRelSpanConeUnitIso T
  counitIso :=
    wedgeRelSpanConeCounitIso T
  functor_unitIso_comp W := by
    apply Limits.ConeMorphism.ext
    simp [wedgeToRelSpanCone,
      relSpanConeToWedge,
      wedgeRelSpanConeUnitIso,
      wedgeRelSpanConeCounitIso]

theorem wedge_roundtrip
    {T : TypeExpr}
    (W : TypeExprWedge.{1} T) :
    (relSpanConeToWedge T).obj
      ((wedgeToRelSpanCone T).obj W) =
    W :=
  rfl

/-- The equivalence between
`TypeExprWedge.{1} T` and `RelSpanCone T`
is a categorical isomorphism: the composites
of the two functors are (propositionally)
equal to the respective identity functors. -/
def wedgeRelSpanConeIso (T : TypeExpr) :
    TypeExprWedge.{1} T ≅Cat
    RelSpanCone T :=
  Cat.isoOfEquiv
    (wedgeRelSpanConeEquivalence T)
    (fun W => wedge_roundtrip W)
    (fun s => relSpanCone_roundtrip s)

/-- A morphism of type expressions induces a
natural transformation between the
corresponding relational span diagrams.  At
type-nodes, the morphism applies the arrow
component; at relation-nodes, it maps
relational fibers using the parametricity
condition. -/
def relSpanDiagramMap
    {T₁ T₂ : TypeExpr}
    (η : ParametricFamily (.arrow T₁ T₂)) :
    relSpanDiagram T₁ ⟶
    relSpanDiagram T₂ where
  app j :=
    match j with
    | .typeNode I =>
      fun ⟨a⟩ => ⟨η.app I a⟩
    | .relNode I₀ I₁ R =>
      fun ⟨⟨(a₁, a₂), h⟩⟩ =>
        ⟨⟨(η.app I₀ a₁, η.app I₁ a₂),
          η.parametric I₀ I₁ R a₁ a₂ h⟩⟩
  naturality := by
    intro X Y f
    cases f <;> rfl

theorem relSpanDiagramMap_id
    (T : TypeExpr) :
    relSpanDiagramMap (typeExprId T) =
    𝟙 (relSpanDiagram T) := by
  ext j x
  cases j <;> rfl

theorem relSpanDiagramMap_comp
    {T₁ T₂ T₃ : TypeExpr}
    (η : ParametricFamily (.arrow T₁ T₂))
    (μ : ParametricFamily (.arrow T₂ T₃)) :
    relSpanDiagramMap (typeExprComp η μ) =
    relSpanDiagramMap η ≫
      relSpanDiagramMap μ := by
  ext j x
  cases j <;> rfl

/-- The relational span diagram construction
is functorial: it defines a functor from the
category of type expressions to the functor
category `RelSpanObj ⥤ Type 1`. -/
def relSpanDiagramFunctor :
    TypeExprCat ⥤ (RelSpanObj ⥤ Type 1) where
  obj T := relSpanDiagram T.expr
  map η := relSpanDiagramMap η
  map_id T := relSpanDiagramMap_id T.expr
  map_comp η μ :=
    relSpanDiagramMap_comp η μ

/-- `relSpanDiagramFunctor` is fully faithful.
The preimage extracts `typeNode` components;
parametricity follows from `β.naturality` at
relation-node projections. Fullness follows
from `relFiber` being a subtype of the
product, determined by its projections. -/
def relSpanDiagramFunctor_fullyFaithful :
    relSpanDiagramFunctor.FullyFaithful where
  preimage {T₁ T₂} β :=
    { app := fun I a =>
        (β.app (.typeNode I) ⟨a⟩).down
      parametric := fun I₀ I₁ R a₁ a₂ h =>
        by
        let fiber : T₁.expr.relFiber R :=
          ⟨(a₁, a₂), h⟩
        let m := (β.app
          (.relNode I₀ I₁ R)
          ⟨fiber⟩).down
        have hfst : m.val.1 =
            (β.app (.typeNode I₀)
              ⟨a₁⟩).down := by
          exact (congr_arg ULift.down
            (congr_fun (β.naturality
              (RelSpanHom.fstProj I₀ I₁ R))
              ⟨fiber⟩)).symm
        have hsnd : m.val.2 =
            (β.app (.typeNode I₁)
              ⟨a₂⟩).down := by
          exact (congr_arg ULift.down
            (congr_fun (β.naturality
              (RelSpanHom.sndProj I₀ I₁ R))
              ⟨fiber⟩)).symm
        change T₂.expr.fullRelInterp R
          (β.app (.typeNode I₀) ⟨a₁⟩).down
          (β.app (.typeNode I₁) ⟨a₂⟩).down
        rw [← hfst, ← hsnd]
        exact m.property }
  map_preimage {T₁ T₂} β := by
    apply NatTrans.ext; funext X
    cases X with
    | typeNode I => funext ⟨_⟩; rfl
    | relNode I₀ I₁ R =>
      funext ⟨p⟩
      apply ULift.ext
      apply Subtype.ext
      have hfst :=
        (congr_arg ULift.down
          (congr_fun (β.naturality
            (RelSpanHom.fstProj I₀ I₁ R))
            ⟨p⟩)).symm
      have hsnd :=
        (congr_arg ULift.down
          (congr_fun (β.naturality
            (RelSpanHom.sndProj I₀ I₁ R))
            ⟨p⟩)).symm
      apply Prod.ext
      · exact hfst.symm
      · exact hsnd.symm

instance relSpanDiagramFunctor_faithful :
    relSpanDiagramFunctor.Faithful :=
  relSpanDiagramFunctor_fullyFaithful.faithful

instance relSpanDiagramFunctor_full :
    relSpanDiagramFunctor.Full :=
  relSpanDiagramFunctor_fullyFaithful.full

end RelSpanDiagram

section ParanaturalProfunctorEmbedding

/-- The subtype of `diagApp G I₀ × diagApp G I₁`
consisting of diagonal pairs related by
`DiagCompat` through a witness at
`relType R`. -/
def diagRelImage
    (G : Typeᵒᵖ ⥤ Type ⥤ Type)
    {I₀ I₁ : Type}
    (R : I₀ → I₁ → Prop) :=
  { p : diagApp G I₀ × diagApp G I₁ //
    ∃ (w : diagApp G (relType R)),
      DiagCompat G (relType R) I₀
        (fun s : relType R => s.val.1)
        w p.1 ∧
      DiagCompat G (relType R) I₁
        (fun s : relType R => s.val.2)
        w p.2 }

/-- The embedding of the endoprofunctor
category (with paranatural morphisms) into
`ParametricCopresheaf`. Type-nodes map to
diagonal elements `ULift (diagApp G I)`;
relation-nodes map to
`ULift (diagRelImage G R)`.
Morphisms are paranatural transformations,
transported via `DiagCompat` preservation. -/
def paranaturalProfEmbedding :
    EndoProf.{1, 0, 0} (C := Type) ⥤
    ParametricCopresheaf where
  obj G :=
    { obj := fun X =>
        match X with
        | .typeNode I =>
          ULift.{1} (diagApp G I)
        | .relNode I₀ I₁ R =>
          ULift.{1} (diagRelImage G R)
      map := fun {X Y} f =>
        match X, Y, f with
        | _, _, .id _ => id
        | _, _, .fstProj I₀ I₁ R =>
          fun ⟨p⟩ => ⟨p.val.1⟩
        | _, _, .sndProj I₀ I₁ R =>
          fun ⟨p⟩ => ⟨p.val.2⟩
      map_id := by
        intro X; cases X <;> rfl
      map_comp := by
        intro X Y Z f g
        cases f <;> cases g <;> rfl }
  map η :=
    { app := fun X =>
        match X with
        | .typeNode I =>
          fun ⟨x⟩ => ⟨η.app I x⟩
        | .relNode I₀ I₁ R =>
          fun ⟨p⟩ =>
            ⟨⟨(η.app I₀ p.val.1,
               η.app I₁ p.val.2),
              p.property.elim
                fun w ⟨hw₁, hw₂⟩ =>
                  ⟨η.app (relType R) w,
                    η.paranatural
                      (relType R) I₀
                      (fun s : relType R =>
                        s.val.1)
                      w p.val.1 hw₁,
                    η.paranatural
                      (relType R) I₁
                      (fun s : relType R =>
                        s.val.2)
                      w p.val.2 hw₂⟩⟩⟩
      naturality := by
        intro X Y f
        match X, Y, f with
        | _, _, .id _ => rfl
        | _, _, .fstProj I₀ I₁ R =>
          funext ⟨_⟩; rfl
        | _, _, .sndProj I₀ I₁ R =>
          funext ⟨_⟩; rfl }
  map_id G := by
    apply NatTrans.ext; funext X
    cases X with
    | typeNode I => funext ⟨_⟩; rfl
    | relNode I₀ I₁ R =>
      funext ⟨⟨_, _⟩⟩
      apply ULift.ext; apply Subtype.ext
      rfl
  map_comp η μ := by
    apply NatTrans.ext; funext X
    cases X with
    | typeNode I => funext ⟨_⟩; rfl
    | relNode I₀ I₁ R =>
      funext ⟨⟨_, _⟩⟩
      apply ULift.ext; apply Subtype.ext
      rfl

/-- `paranaturalProfEmbedding` is faithful:
paranatural transformations are determined
by their components `η.app I`, which the
embedding preserves at typeNodes. -/
instance paranaturalProfEmbedding_faithful :
    paranaturalProfEmbedding.Faithful where
  map_injective {G H η μ} h := by
    apply Paranat.ext; funext I x
    have := congr_arg ULift.down
      (congr_fun (congr_fun (congrArg
        NatTrans.app h) (.typeNode I))
        ⟨x⟩)
    exact this

-- Fullness analysis:
--
-- Given β on the copresheaf, the preimage
-- η.app I x := (β.app (.typeNode I) ⟨x⟩).down
-- extracts diagonal components. Paranaturality
-- of η requires: given DiagCompat G I₀ I₁ f
-- d₀ d₁, show DiagCompat H I₀ I₁ f
-- (η.app I₀ d₀) (η.app I₁ d₁).
--
-- From the diagRelImage at graphRel f, we can
-- construct a witness w at relType (graphRel f)
-- and derive the two DiagCompat conditions at
-- π₁ and π₂. To recover DiagCompat at f, one
-- shows:
--   (H.map (op π₁)).app I₁
--     ((H.obj (op I₀)).map f (η.app I₀ d₀))
--   = (H.map (op π₁)).app I₁
--     ((H.map (op f)).app I₁ (η.app I₁ d₁))
--
-- This follows from the witness conditions and
-- f ∘ π₁ = π₂ on relType (graphRel f). But
-- cancelling (H.map (op π₁)).app I₁ requires
-- it to be injective, which does not hold for
-- all profunctors. So fullness is not
-- guaranteed in general.
--
-- No natural functor exists in the other
-- direction (ParametricCopresheaf → EndoProf)
-- either: RelSpanObj has no morphisms between
-- typeNodes, so the profunctor's
-- covariant/contravariant transport maps
-- cannot be defined.

end ParanaturalProfunctorEmbedding

/-- `divEndoRel f h k` is equivalent to
`DiagCompat divHomProf I₀ I₁ f h k`, which
reduces to `f ∘ h = k ∘ f`. The relational
form quantifies pointwise over `graphRel f`;
the `DiagCompat` form uses function equality. -/
theorem divEndoRel_iff_diagCompat
    {I₀ I₁ : Type} (f : I₀ → I₁)
    (h : I₀ → I₀) (k : I₁ → I₁) :
    divEndoRel f h k ↔
    DiagCompat divHomProf I₀ I₁ f h k := by
  rw [divHomProf_diagCompat_eq,
    divEndoRel_expand]
  constructor
  · intro hrel
    ext a
    exact hrel a (f a) rfl
  · intro heq a₀ a₁ ha
    change f (h a₀) = k a₁
    rw [← ha]
    exact congr_fun heq a₀

/-- `divArgRel f p q` is equivalent to
`DivParametric`'s gate condition on `(p, q)`:
for all `(h, k)` with `f ∘ h = k ∘ f`,
`f (p h) = q k`. -/
theorem divArgRel_iff_isParanaturalAt
    {I₀ I₁ : Type} (f : I₀ → I₁)
    (p : (I₀ → I₀) → I₀)
    (q : (I₁ → I₁) → I₁) :
    divArgRel f p q ↔
    IsParanaturalAt
      divHomProf divTarget f p q := by
  rw [divArgRel_expand]
  constructor
  · intro hrel h k hcompat
    exact hrel h k
      (divEndoRel_expand f ▸
        (divEndoRel_iff_diagCompat f h k).mpr
          hcompat)
  · intro hpn h k hendo
    exact hpn h k
      ((divEndoRel_iff_diagCompat f h k).mp
        (divEndoRel_expand f ▸ hendo))

/-- `divFullRel f phi₀ phi₁` is equivalent to
`DivParametric`'s condition on `(phi₀, phi₁)`:
for all `(p, q)` satisfying the gate,
`f (phi₀ p) = phi₁ q`. -/
theorem divFullRel_iff_divParametric
    {I₀ I₁ : Type} (f : I₀ → I₁)
    (phi₀ : ((I₀ → I₀) → I₀) → I₀)
    (phi₁ : ((I₁ → I₁) → I₁) → I₁) :
    divFullRel f phi₀ phi₁ ↔
    (∀ (p : (I₀ → I₀) → I₀)
       (q : (I₁ → I₁) → I₁),
      IsParanaturalAt
        divHomProf divTarget f p q →
      DiagCompat divTarget I₀ I₁ f
        (phi₀ p) (phi₁ q)) := by
  rw [divFullRel_expand]
  constructor
  · intro hrel p q hpn
    exact hrel p q
      (divArgRel_expand f ▸
        (divArgRel_iff_isParanaturalAt
          f p q).mpr hpn)
  · intro hpn p q harg
    exact hpn p q
      ((divArgRel_iff_isParanaturalAt
        f p q).mp
        (divArgRel_expand f ▸ harg))

/-- `DivParametric phi` is equivalent to
`∀ I₀ I₁ f, divFullRel f (phi I₀) (phi I₁)`:
the Wadler relational interpretation of
`((X → X) → X) → X` at the graph of `f` holds
for the pair `(phi I₀, phi I₁)`. -/
theorem divParametric_iff_divFullRel
    (phi : ParanatSig divSource divTarget) :
    DivParametric phi ↔
    ∀ (I₀ I₁ : Type) (f : I₀ → I₁),
      divFullRel f (phi I₀) (phi I₁) := by
  constructor
  · intro hparam I₀ I₁ f
    exact (divFullRel_iff_divParametric
      f (phi I₀) (phi I₁)).mpr
      (hparam I₀ I₁ f)
  · intro hfull I₀ I₁ f
    exact (divFullRel_iff_divParametric
      f (phi I₀) (phi I₁)).mp
      (hfull I₀ I₁ f)

/-- The subtype of `ParanatSig divSource divTarget`
satisfying the parametricity condition
`DivParametric`. -/
def DivParametricSub :=
  { phi : ParanatSig divSource divTarget //
    DivParametric phi }

/-- Bundled parametricity for `((X → X) → X) → X`.
A family `app I : ((I → I) → I) → I` together with
the relational interpretation `divFullRel` at the
graph of every `f : I₀ → I₁`. -/
@[ext]
structure DivParametricBundled where
  app : ∀ (I : Type), ((I → I) → I) → I
  parametric :
    ∀ (I₀ I₁ : Type) (f : I₀ → I₁),
      divFullRel f (app I₀) (app I₁)

/-- The subtype and bundled formulations of
parametricity are equivalent:
`divParametric_iff_divFullRel` bridges between
`DivParametric` (using `IsParanaturalAt` and
`DiagCompat`) and `divFullRel` (using `arrowRel`
and `graphRel`). -/
def divParametricEquiv :
    DivParametricSub ≃ DivParametricBundled where
  toFun phi :=
    { app := phi.val
      parametric := fun I₀ I₁ f =>
        (divParametric_iff_divFullRel phi.val).mp
          phi.property I₀ I₁ f }
  invFun b :=
    ⟨b.app,
     (divParametric_iff_divFullRel b.app).mpr
       b.parametric⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := rfl

/-- The subtype of `ParanatSig divSource divTarget`
satisfying the paranaturality condition
`DivParanatural`. -/
def DivParanaturalSub :=
  { phi : ParanatSig divSource divTarget //
    DivParanatural phi }

/-- Bundled version of the paranaturality condition:
`app` is paranatural at every `f` from `divSource`
to `divTarget`.

Parallel with `DivParametricBundled`: both say
`app` preserves `DiagCompat` for `divTarget`, but
the paranaturality form requires this directly
(`IsParanaturalAt divSource divTarget`), while the
parametric form requires it only for `(p, q)` that
are themselves paranatural at `f` from `divHomProf`
to `divTarget`. -/
@[ext]
structure DivParanaturalBundled where
  app : ∀ (I : Type), ((I → I) → I) → I
  paranatural :
    ∀ (I₀ I₁ : Type) (f : I₀ → I₁),
      IsParanaturalAt divSource divTarget f
        (app I₀) (app I₁)

/-- The subtype and bundled formulations of
paranaturality are equivalent: `DivParanatural phi`
holds if and only if the `DiagCompat`-preservation
condition in `DivParanaturalBundled` holds. The
only difference is pointwise vs function equality
in the `divSource` compatibility condition. -/
def divParanaturalEquiv :
    DivParanaturalSub ≃ DivParanaturalBundled where
  toFun phi :=
    { app := phi.val
      paranatural :=
        fun I₀ I₁ f p q hcompat =>
          phi.property I₀ I₁ f p q
            (congr_fun hcompat) }
  invFun b :=
    ⟨b.app,
     fun I₀ I₁ f p q hpw =>
       b.paranatural I₀ I₁ f p q (funext hpw)⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := DivParanaturalBundled.ext rfl

/-- `DivParanaturalBundled` coincides with
`Paranat divSource divTarget`: the `DiagCompat`
condition in the bundled form is
`IsParanatural divSource divTarget`. -/
def divParanaturalBundledEquivParanat :
    DivParanaturalBundled ≃
    Paranat divSource divTarget where
  toFun b :=
    { app := b.app
      paranatural := b.paranatural }
  invFun α :=
    { app := α.app
      paranatural := α.paranatural }
  left_inv _ := rfl
  right_inv _ := rfl

/-- Full relational parametricity for
`((X → X) → X) → X`: the relational
interpretation at an arbitrary relation
`R : I₀ → I₁ → Prop` (not necessarily a graph).
A family `phi` is fully relationally parametric
if for all `(p₀, p₁)` satisfying
`arrowRel (arrowRel R R) R p₀ p₁`, the pair
`(phi I₀ p₀, phi I₁ p₁)` satisfies `R`.

This is the edge-level parametricity condition:
an edge `(I₀, I₁, R)` in the relation double
category is preserved by `phi` iff the
relational interpretation at `R` holds for the
pair `(phi I₀, phi I₁)`. -/
def DivFullRelParametric
    (phi : ParanatSig divSource divTarget) :
    Prop :=
  ∀ (I₀ I₁ : Type)
    (R : I₀ → I₁ → Prop)
    (p₀ : (I₀ → I₀) → I₀)
    (p₁ : (I₁ → I₁) → I₁),
    arrowRel (arrowRel R R) R p₀ p₁ →
    R (phi I₀ p₀) (phi I₁ p₁)

/-- Full relational parametricity implies
graph-level parametricity (`DivParametric`):
specialize `R` to `graphRel f` and convert
`arrowRel (graphRel f) (graphRel f) h₀ h₁`
to `f ∘ h₀ = h₁ ∘ f`. -/
theorem divFullRelParametric_implies_parametric
    {phi : ParanatSig divSource divTarget}
    (h : DivFullRelParametric phi) :
    DivParametric phi := by
  intro I₀ I₁ f p q hrel
  exact h I₀ I₁ (graphRel f) p q
    (fun h₀ h₁ hendo =>
      hrel h₀ h₁ (funext fun x =>
        hendo x (f x) rfl))

/-- `divApplyId` is fully relationally
parametric: for any relation `R` and any
`(p₀, p₁)` satisfying
`arrowRel (arrowRel R R) R`, the pair
`(p₀ id, p₁ id)` satisfies `R`.

The proof instantiates the gate condition
with `(id, id)` and observes that
`arrowRel R R id id` holds since `R` is
reflexive on related pairs. -/
theorem divApplyId_fullRelParametric :
    DivFullRelParametric divApplyId := by
  intro I₀ I₁ R p₀ p₁ hrel
  exact hrel id id (fun _ _ h => h)

/-- Full relational parametricity does not imply
paranaturality. `divApplyId` satisfies
`DivFullRelParametric` but not `DivParanatural`.

This is the edge-level divergence: `divApplyId`
preserves all edges in the relation double
category (arbitrary relations) but fails the
paranaturality condition (which tests a
restricted class of inputs). -/
theorem divFullRelParametric_not_implies_paranatural :
    ¬ (∀ phi : ParanatSig divSource divTarget,
      DivFullRelParametric phi →
        DivParanatural phi) :=
  fun h => divApplyId_not_paranatural
    (h divApplyId divApplyId_fullRelParametric)

/-- `DivFullRelParametric phi` is equivalent to
`∀ I₀ I₁ R, divTypeExpr.fullRelInterp R
  (phi I₀) (phi I₁)`: the relational
interpretation at arbitrary relations.

Since each leaf of `divTypeExpr` is
`.app (𝟭 Type) .var`, the `fullRelInterp`
expansion introduces `functorRelLift (𝟭 Type)`
at each variable occurrence, which simplifies
to the identity by `functorRelLift_id`. -/
theorem divFullRelParametric_iff_fullRelInterp
    (phi : ParanatSig divSource divTarget) :
    DivFullRelParametric phi ↔
    ∀ (I₀ I₁ : Type)
      (R : I₀ → I₁ → Prop),
      divTypeExpr.fullRelInterp R
        (phi I₀) (phi I₁) := by
  constructor
  · intro h I₀ I₁ R
    simp only [divTypeExpr, divArgTypeExpr,
      divEndoTypeExpr, TypeExpr.leaf,
      TypeExpr.fullRelInterp, functorRelLift_id]
    exact h I₀ I₁ R
  · intro h I₀ I₁ R
    have := h I₀ I₁ R
    simp only [divTypeExpr, divArgTypeExpr,
      divEndoTypeExpr, TypeExpr.leaf,
      TypeExpr.fullRelInterp, functorRelLift_id]
      at this
    exact this

/-- `divApplyId` does not preserve
`profBarrLiftRel` at graph relations. Since
`profBarrLiftRel` at graphs is equivalent to
`DiagCompat` (paranaturality), this follows from
`divApplyId_not_paranatural`. -/
theorem divApplyId_not_profBarrLift_preserving :
    ¬ (∀ (I₀ I₁ : Type) (f : I₀ → I₁)
      (p₀ : diagApp divSource I₀)
      (p₁ : diagApp divSource I₁),
      profBarrLiftRel divSource
        (graphRel f) p₀ p₁ →
      profBarrLiftRel divTarget
        (graphRel f)
        (divApplyId I₀ p₀)
        (divApplyId I₁ p₁)) := by
  intro h
  apply divApplyId_not_paranatural
  rw [divParanatural_iff_isParanatural]
  intro I₀ I₁ f d₀ d₁ hcompat
  exact profBarrLiftRel_graph_implies_diagCompat
    divTarget f _ _
    (h I₀ I₁ f d₀ d₁
      (diagCompat_implies_profBarrLiftRel_graph
        divSource f d₀ d₁ hcompat))

end ParametricityDivergence

end GebLean
