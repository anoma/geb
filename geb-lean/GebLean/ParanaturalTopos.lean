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

/-- The subtype of `ParanatSig divSource divTarget`
satisfying the parametricity condition
`DivParametric`. -/
def DivParametricSub :=
  { phi : ParanatSig divSource divTarget //
    DivParametric phi }

/-- Bundled version of the parametricity condition:
a family `app I : ((I → I) → I) → I` such that for
every `f : I₀ → I₁` and `(p, q)` preserving
`DiagCompat` from `divHomProf` to `divTarget`, the
pair `(app I₀ p, app I₁ q)` is `DiagCompat` for
`divTarget`. -/
@[ext]
structure DivParametricBundled where
  app : ∀ (I : Type), ((I → I) → I) → I
  parametric :
    ∀ (I₀ I₁ : Type) (f : I₀ → I₁)
      (p : (I₀ → I₀) → I₀)
      (q : (I₁ → I₁) → I₁),
      (∀ (h : I₀ → I₀) (k : I₁ → I₁),
        DiagCompat divHomProf I₀ I₁ f h k →
        DiagCompat divTarget I₀ I₁ f (p h) (q k)) →
      DiagCompat divTarget I₀ I₁ f
        (app I₀ p) (app I₁ q)

/-- The subtype and bundled formulations of
parametricity are equivalent: `DivParametric phi`
holds if and only if the `DiagCompat` preservation
condition in `DivParametricBundled` holds. -/
def divParametricEquiv :
    DivParametricSub ≃ DivParametricBundled where
  toFun phi :=
    { app := phi.val
      parametric := phi.property }
  invFun b :=
    ⟨b.app, b.parametric⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The subtype of `ParanatSig divSource divTarget`
satisfying the paranaturality condition
`DivParanatural`. -/
def DivParanaturalSub :=
  { phi : ParanatSig divSource divTarget //
    DivParanatural phi }

/-- Bundled version of the paranaturality condition:
a family `app I : ((I → I) → I) → I` such that for
every `f : I₀ → I₁` and `(p, q)` satisfying
`DiagCompat divSource`, the pair
`(app I₀ p, app I₁ q)` is `DiagCompat` for
`divTarget`. -/
@[ext]
structure DivParanaturalBundled where
  app : ∀ (I : Type), ((I → I) → I) → I
  paranatural :
    ∀ (I₀ I₁ : Type) (f : I₀ → I₁)
      (p : (I₀ → I₀) → I₀)
      (q : (I₁ → I₁) → I₁),
      DiagCompat divSource I₀ I₁ f p q →
      DiagCompat divTarget I₀ I₁ f
        (app I₀ p) (app I₁ q)

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

end ParametricityDivergence

end GebLean
