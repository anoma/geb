import GebLean.EqualizerCompletionLimits
import GebLean.LawvereBTInterp

/-!
# Equalizer Completion of the Lawvere BT Theory

Applies the free equalizer completion to
`LawvereBTQuotCat`, yielding a category
`LawvereBTLexCat` with all finite limits.
The finite products are inherited from
`LawvereBTQuotCat` and the equalizers are
freely adjoined.
-/

namespace GebLean

open CategoryTheory

/-- The equalizer completion of the Lawvere theory
of parameterized binary tree objects.  This category
has all finite limits. -/
@[reducible] def LawvereBTLexCat :=
  CoreflexivePairObj LawvereBTQuotCat

example : Category LawvereBTLexCat :=
  inferInstance

example : Limits.HasFiniteLimits
    LawvereBTLexCat :=
  inferInstance

example : HasChosenFiniteProducts
    LawvereBTLexCat :=
  inferInstance

/-! ## Interpretation functor on the equalizer
completion

Extends `interpFunctor : LawvereBTQuotCat ⥤ Type u`
to a functor `lexInterpFunctor : LawvereBTLexCat ⥤
Type u` by sending each coreflexive pair to its
equalizer in `Type u`. -/

universe u

/-- The interpretation of a coreflexive pair
object as the equalizer of the two morphisms'
interpretations. -/
def lexInterpObj
    (X : LawvereBTLexCat) : Type u :=
  { ctx : interpFunctor.{u}.obj X.src //
    interpFunctor.{u}.map X.left ctx =
    interpFunctor.{u}.map X.right ctx }

/-- If two morphisms from `X.src` are related
by a one-step coreflexive relation on `X`, then
they agree on any element of the equalizer of
`X.left` and `X.right`. -/
theorem interpFunctor_relStep_on_equalizer
    (X : LawvereBTLexCat)
    {V : LawvereBTQuotCat}
    {a b : X.src ⟶ V}
    (hab : CoreflexiveRelStep X a b)
    (ctx : interpFunctor.{u}.obj X.src)
    (hctx : interpFunctor.{u}.map X.left ctx =
      interpFunctor.{u}.map X.right ctx) :
    interpFunctor.{u}.map a ctx =
      interpFunctor.{u}.map b ctx := by
  obtain ⟨w, hl, hr⟩ := hab
  have ha :
      interpFunctor.{u}.map a ctx =
      interpFunctor.{u}.map w
        (interpFunctor.{u}.map X.left ctx) := by
    rw [← hl]
    exact congrFun
      (interpFunctor.{u}.map_comp X.left w)
      ctx
  have hb :
      interpFunctor.{u}.map b ctx =
      interpFunctor.{u}.map w
        (interpFunctor.{u}.map X.right ctx) := by
    rw [← hr]
    exact congrFun
      (interpFunctor.{u}.map_comp X.right w)
      ctx
  rw [ha, hctx, ← hb]

/-- If two morphisms from `X.src` are equivalent
under the coreflexive equivalence relation on `X`,
then they agree on any element of the equalizer of
`X.left` and `X.right`. -/
theorem interpFunctor_eqv_on_equalizer
    (X : LawvereBTLexCat)
    {V : LawvereBTQuotCat}
    {a b : X.src ⟶ V}
    (hab : CoreflexiveEqv X a b)
    (ctx : interpFunctor.{u}.obj X.src)
    (hctx : interpFunctor.{u}.map X.left ctx =
      interpFunctor.{u}.map X.right ctx) :
    interpFunctor.{u}.map a ctx =
      interpFunctor.{u}.map b ctx := by
  induction hab with
  | rel _ _ hr =>
    exact interpFunctor_relStep_on_equalizer
      X hr ctx hctx
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 =>
    exact ih1.trans ih2

/-- The raw map on equalizer subtypes induced by a
premorphism.  Given a premorphism `f : X.src ⟶
Y.src`, maps an element of the equalizer of `X`
to an element of the equalizer of `Y`. -/
def lexInterpMapRaw
    {X Y : LawvereBTLexCat}
    (f : X.src ⟶ Y.src)
    (hf : IsCPPremorphism X Y f) :
    lexInterpObj.{u} X → lexInterpObj.{u} Y :=
  fun ⟨ctx, hctx⟩ =>
    ⟨interpFunctor.{u}.map f ctx,
      by
        have h1 :
            interpFunctor.{u}.map Y.left
              (interpFunctor.{u}.map f ctx) =
            interpFunctor.{u}.map (f ≫ Y.left)
              ctx := by
          exact (congrFun
            (interpFunctor.{u}.map_comp
              f Y.left)
            ctx).symm
        have h2 :
            interpFunctor.{u}.map Y.right
              (interpFunctor.{u}.map f ctx) =
            interpFunctor.{u}.map (f ≫ Y.right)
              ctx := by
          exact (congrFun
            (interpFunctor.{u}.map_comp
              f Y.right)
            ctx).symm
        rw [h1, h2]
        exact interpFunctor_eqv_on_equalizer
          X hf ctx hctx⟩

/-- Two equivalent premorphisms induce the same
map on equalizer subtypes. -/
theorem lexInterpMapRaw_congr
    {X Y : LawvereBTLexCat}
    (f₁ f₂ : CPPreMor X Y)
    (h : CoreflexiveEqv X f₁.val f₂.val) :
    lexInterpMapRaw.{u} f₁.val f₁.property =
      lexInterpMapRaw.{u} f₂.val f₂.property := by
  funext ⟨ctx, hctx⟩
  exact Subtype.ext
    (interpFunctor_eqv_on_equalizer X h ctx hctx)

/-- The interpretation on morphisms of the
equalizer completion, lifted from premorphisms
through the quotient. -/
def lexInterpMap
    {X Y : LawvereBTLexCat}
    (f : X ⟶ Y) :
    lexInterpObj.{u} X → lexInterpObj.{u} Y :=
  Quotient.lift
    (s := cpPreMorSetoid X Y)
    (fun f_raw =>
      lexInterpMapRaw.{u} f_raw.val f_raw.property)
    (fun f₁ f₂ hrel =>
      lexInterpMapRaw_congr f₁ f₂ hrel)
    f

/-- `lexInterpMap` on the identity morphism is the
identity function. -/
theorem lexInterpMap_id
    (X : LawvereBTLexCat) :
    lexInterpMap.{u} (𝟙 X) = id := by
  funext ⟨ctx, hctx⟩
  exact Subtype.ext
    (congrFun (interpFunctor.{u}.map_id X.src) ctx)

/-- `lexInterpMap` preserves composition. -/
theorem lexInterpMap_comp
    {X Y Z : LawvereBTLexCat}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    lexInterpMap.{u} (f ≫ g) =
      lexInterpMap.{u} g ∘ lexInterpMap.{u} f := by
  revert f g
  apply Quotient.ind₂
  intro f_raw g_raw
  funext ⟨ctx, hctx⟩
  exact Subtype.ext
    (congrFun
      (interpFunctor.{u}.map_comp
        f_raw.val g_raw.val)
      ctx)

/-- The interpretation functor from the equalizer
completion of the Lawvere BT theory into `Type u`.
Sends each coreflexive pair to its equalizer and
each morphism class to the induced map between
equalizers. -/
def lexInterpFunctor :
    LawvereBTLexCat ⥤ Type u where
  obj := lexInterpObj
  map := lexInterpMap
  map_id X := lexInterpMap_id X
  map_comp f g := lexInterpMap_comp f g

/-! ## Compatibility with the embedding functor -/

/-- For a trivially-embedded object, the equalizer
subtype is equivalent to the full type, since the
equalizer condition is `id = id`. -/
def lexInterpEmbedEquiv
    (n : LawvereBTQuotCat) :
    lexInterpObj.{u} (cpEmbed n) ≃
      interpFunctor.{u}.obj n where
  toFun := fun ⟨ctx, _⟩ => ctx
  invFun := fun ctx =>
    ⟨ctx, rfl⟩
  left_inv := fun ⟨_, _⟩ => rfl
  right_inv := fun _ => rfl

/-- The composition of the embedding functor with
the lex interpretation functor is naturally
isomorphic to the original interpretation functor.
This witnesses the compatibility of `lexInterpFunctor`
with `interpFunctor` via `cpEmbedding`. -/
def lexInterpEmbedIso :
    cpEmbedding ⋙ lexInterpFunctor.{u} ≅
      interpFunctor.{u} :=
  NatIso.ofComponents
    (fun n =>
      { hom := fun ⟨ctx, _⟩ => ctx
        inv := fun ctx => ⟨ctx, rfl⟩ })
    (fun {n m} f => by
      funext ⟨ctx, hctx⟩
      rfl)

end GebLean
