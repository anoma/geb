import Mathlib.CategoryTheory.Subfunctor.Basic
import Mathlib.CategoryTheory.Subfunctor.Image
import Mathlib.CategoryTheory.Subfunctor.Sieves
import GebLean.Utilities.Presheaf
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
import Mathlib.CategoryTheory.Topos.Classifier

/-!
# Witnessed subfunctors

A `WSubfunctor F` is a constructive analogue of
mathlib's `Subfunctor F`. Where `Subfunctor`
stores membership propositionally
(`obj : ∀ U, Set (F.obj U)`, i.e., `α → Prop`),
a `WSubfunctor` stores a total presheaf and an
inclusion morphism, so the fiber over each
element `x : F.obj U` is the constructive type
`{a : W.total.obj U // W.incl.app U a = x}`.

When the inclusion is mono (pointwise injective),
each fiber is a `Subsingleton`, and witnesses
can be extracted constructively (no
`Classical.choice` needed). This enables
constructive inversions that are not possible
with propositional `Subfunctor`.

## API correspondence with `Subfunctor`

The API mirrors `Subfunctor` so that migration
is a mechanical name change:

| `Subfunctor`        | `WSubfunctor`          |
|---------------------|------------------------|
| `toFunctor`         | `total` (field)        |
| `ι`                 | `incl` (field)         |
| `range p`           | `range p`              |
| `ext`               | `ext`                  |

## Connection to `Subfunctor`

`WSubfunctor.toSubfunctor` forgets the total
presheaf and retains only propositional
membership (via `Set.range`).
-/

open CategoryTheory

namespace GebLean

universe v u w

variable {C : Type u} [Category.{v} C]

/-- A witnessed subfunctor of `F : C ⥤ Type w`.
Consists of a total presheaf and an inclusion
morphism into `F`. The fiber over
`x : F.obj U` is the constructive type
`{a : W.total.obj U // W.incl.app U a = x}`.
-/
structure WSubfunctor
    (F : C ⥤ Type w) where
  /-- The total presheaf carrying witness
  data. -/
  total : C ⥤ Type w
  /-- The inclusion morphism from the total
  presheaf into `F`. Uses `NatTrans` directly
  (not `⟶`) to avoid inheriting
  `Classical.choice` from the functor category
  `CategoryStruct` instance. -/
  incl : NatTrans total F

variable {F F' F'' : C ⥤ Type w}

namespace WSubfunctor

/-- The fiber of a witnessed subfunctor over
`x : F.obj U`: the type of witnesses that
`x` belongs to the subfunctor. -/
abbrev fiber (W : WSubfunctor F) (U : C)
    (x : F.obj U) : Type w :=
  { a : W.total.obj U // W.incl.app U a = x }

/-- The range of a morphism `p : NatTrans F' F`,
as a witnessed subfunctor. The total presheaf
is `F'` itself, and the inclusion is `p`.
The fiber over `x` is
`{a : F'.obj U // p.app U a = x}`. -/
def range (p : NatTrans F' F) : WSubfunctor F where
  total := F'
  incl := p

@[simp]
theorem range_total (p : NatTrans F' F) :
    (range p).total = F' := rfl

@[simp]
theorem range_incl (p : NatTrans F' F) :
    (range p).incl = p := rfl

/-- Forget witness data: extract the
propositional `Subfunctor` by taking
`Set.range` of the inclusion at each stage. -/
def toSubfunctor (W : WSubfunctor F) :
    Subfunctor F :=
  Subfunctor.range W.incl

/-- Extensionality: two witnessed subfunctors
with the same total presheaf and inclusion are
equal. -/
@[ext (iff := false)]
theorem ext {W₁ W₂ : WSubfunctor F}
    (htotal : W₁.total = W₂.total)
    (hincl : htotal ▸ W₁.incl = W₂.incl) :
    W₁ = W₂ := by
  cases W₁; cases W₂
  dsimp at htotal
  subst htotal
  dsimp at hincl
  exact congrArg (WSubfunctor.mk _) hincl

/-- Lift propositional membership to
constructive witnesses via `PLift`. Each
`PLift` fiber is a `Subsingleton` (by proof
irrelevance). -/
def ofSubfunctor (S : Subfunctor F) :
    WSubfunctor F where
  total := S.toFunctor
  incl := S.ι

@[simp]
theorem ofSubfunctor_total (S : Subfunctor F) :
    (ofSubfunctor S).total = S.toFunctor := rfl

@[simp]
theorem ofSubfunctor_incl (S : Subfunctor F) :
    (ofSubfunctor S).incl = S.ι := rfl

/-- The fiber of a `range` witnessed
subfunctor: the preimage type. -/
theorem range_fiber_eq (p : NatTrans F' F) (U : C)
    (x : F.obj U) :
    (range p).fiber U x =
      { a : F'.obj U // p.app U a = x } :=
  rfl

/-- Factor a morphism through the range:
given `p : NatTrans F' F`, produce a
`NatTrans F' (range p).total` (the identity,
since `(range p).total = F'`). -/
def toRange (p : NatTrans F' F) :
    NatTrans F' (range p).total :=
  NatTrans.id F'

@[simp]
theorem toRange_comp_incl
    (p : NatTrans F' F) :
    NatTrans.vcomp (toRange p)
      (range p).incl = p := by
  ext c x
  dsimp [toRange, range, NatTrans.vcomp,
    NatTrans.id]

end WSubfunctor

section ChoiceFreeNatTrans

/-! ### Choice-free natural transformation operations

Mathlib's `NatTrans.id` and `NatTrans.vcomp`
carry `Classical.choice` from `aesop_cat`
automation in their naturality proofs. These
hand-rolled versions use only `rw` and
`Category.assoc`/`id_comp`/`comp_id`, achieving
zero or `propext`-only dependencies. -/

variable {C : Type u} [Category.{v} C]
variable {D : Type*} [Category D]

/-- Choice-free identity natural
transformation. Uses `propext` only (from
`Category.id_comp`/`comp_id`). -/
def ntId (F : C ⥤ D) : NatTrans F F where
  app X := 𝟙 (F.obj X)
  naturality {X Y} f := by
    simp only [Category.id_comp,
      Category.comp_id]

/-- Choice-free composition of natural
transformations. Axiom-free. -/
def ntComp {F G H : C ⥤ D}
    (α : NatTrans F G) (β : NatTrans G H) :
    NatTrans F H where
  app X := α.app X ≫ β.app X
  naturality {X Y} f := by
    simp only [Category.assoc]
    rw [← β.naturality, ← Category.assoc,
      α.naturality, Category.assoc]

/-- Pointwise injectivity of a natural
transformation between `Type`-valued
functors. This is the choice-free analogue
of mathlib's `Mono` for functor categories.
For `Type`-valued presheaves, `NatMono m` iff
`Mono m` (via `NatTrans.mono_iff_mono_app`
and `mono_iff_injective`). -/
def NatMono {U X : C ⥤ Type w}
    (m : NatTrans U X) : Prop :=
  ∀ c, Function.Injective (m.app c)

/-- Choice-free pullback condition for
`Type`-valued presheaves. Unlike mathlib's
`IsPullback` (which is `Prop`-valued and
wraps the lift in `Nonempty`), this structure
carries the lift as constructive data. -/
structure WIsPullback
    {U X Ω₀ Ω : C ⥤ Type w}
    (m : NatTrans U X)
    (χ₀ : NatTrans U Ω₀)
    (χ : NatTrans X Ω)
    (truth : NatTrans Ω₀ Ω) where
  w : ntComp m χ = ntComp χ₀ truth
  lift :
    ∀ {W : C ⥤ Type w}
      (s₁ : NatTrans W X)
      (s₂ : NatTrans W Ω₀)
      (_ : ntComp s₁ χ = ntComp s₂ truth),
    NatTrans W U
  fac :
    ∀ {W : C ⥤ Type w}
      (s₁ : NatTrans W X)
      (s₂ : NatTrans W Ω₀)
      (hw : ntComp s₁ χ =
        ntComp s₂ truth),
    ntComp (lift s₁ s₂ hw) m = s₁
  uniq :
    ∀ {W : C ⥤ Type w}
      (s₁ : NatTrans W X)
      (s₂ : NatTrans W Ω₀)
      (hw : ntComp s₁ χ =
        ntComp s₂ truth)
      (l : NatTrans W U)
      (_ : ntComp l m = s₁),
    l = lift s₁ s₂ hw

/-- Choice-free subobject classifier for
`Type`-valued presheaf categories. All
morphisms are `NatTrans` (not `⟶`), the
pullback condition carries constructive
lift data, and mono is pointwise
injectivity. -/
structure WClassifier
    (C : Type u) [Category.{v} C] where
  /-- The classifier object. -/
  Ω : Cᵒᵖ ⥤ Type (max u v)
  /-- The terminal presheaf. -/
  Ω₀ : Cᵒᵖ ⥤ Type (max u v)
  /-- The truth morphism. -/
  truth : NatTrans Ω₀ Ω
  /-- The terminal map for any presheaf. -/
  terminal :
    ∀ (U : Cᵒᵖ ⥤ Type (max u v)),
      NatTrans U Ω₀
  /-- The classifying map for a mono. -/
  χ : ∀ {U X : Cᵒᵖ ⥤ Type (max u v)}
    (m : NatTrans U X) (_ : NatMono m),
    NatTrans X Ω
  /-- The pullback condition. -/
  isPullback :
    ∀ {U X : Cᵒᵖ ⥤ Type (max u v)}
      (m : NatTrans U X) (hm : NatMono m),
    WIsPullback m (terminal U) (χ m hm) truth
  /-- Uniqueness of the classifying map. -/
  unique :
    ∀ {U X : Cᵒᵖ ⥤ Type (max u v)}
      (m : NatTrans U X) (hm : NatMono m)
      (χ' : NatTrans X Ω)
      (_ : WIsPullback m (terminal U)
        χ' truth),
    χ' = χ m hm

end ChoiceFreeNatTrans

section WSubfunctorSieves

/-! ### Sieves from witnessed subfunctors

When `F : Cᵒᵖ ⥤ Type w` is a presheaf, a
`WSubfunctor F` determines a sieve at each
section, using `Nonempty` of the fiber to
define membership. This agrees with
`Subfunctor.sieveOfSection` applied to
`W.toSubfunctor`.
-/

open Limits

variable {C : Type u} [Category.{v} C]
variable {F : Cᵒᵖ ⥤ Type w}

open Opposite

namespace WSubfunctor

/-- The sieve of a witnessed subfunctor at a
section `s : F.obj U`: the sieve on `U.unop`
consisting of morphisms `f : V ⟶ U.unop`
such that `F.map f.op s` has a witness. -/
def sieveOfSection (W : WSubfunctor F)
    {U : Cᵒᵖ} (s : F.obj U) :
    Sieve U.unop where
  arrows V f :=
    Nonempty (W.fiber (op V)
      (F.map f.op s))
  downward_closed := by
    intro V₁ V₂ f₁ ⟨⟨a, ha⟩⟩ f₂
    refine ⟨⟨W.total.map f₂.op a, ?_⟩⟩
    have nat := congr_fun
      (W.incl.naturality f₂.op) a
    simp only [types_comp_apply] at nat
    rw [nat, ha]
    exact (congr_fun
      (F.map_comp f₁.op f₂.op) s).symm

/-- The `WSubfunctor` sieve agrees with the
`Subfunctor` sieve via `toSubfunctor`. -/
theorem sieveOfSection_eq_toSubfunctor
    (W : WSubfunctor F)
    {U : Cᵒᵖ} (s : F.obj U) :
    W.sieveOfSection s =
      W.toSubfunctor.sieveOfSection s := by
  ext V f
  dsimp [sieveOfSection,
    Subfunctor.sieveOfSection,
    toSubfunctor, Subfunctor.range]
  exact ⟨fun ⟨⟨a, ha⟩⟩ => ⟨a, ha⟩,
    fun ⟨a, ha⟩ => ⟨⟨a, ha⟩⟩⟩

/-- The classifying map of a monomorphism
`m : U ⟶ X` via `WSubfunctor`: at stage `c`,
sends `x : X.obj c` to the sieve of morphisms
along which `x` restricts into the
`WSubfunctor.range m`. -/
def wPshSieveCharMap
    (C : Type u) [Category.{v} C]
    {U X : Cᵒᵖ ⥤ Type (max u v)}
    (m : U ⟶ X) :
    X ⟶ pshSieveFunctor C where
  app c x :=
    (WSubfunctor.range m).sieveOfSection x
  naturality c₁ c₂ g := by
    funext x
    apply Sieve.ext
    intro V f
    dsimp [sieveOfSection, range, fiber,
      pshSieveFunctor]
    constructor
    · rintro ⟨⟨a, ha⟩⟩
      exact ⟨⟨a, by
        rw [ha]; symm
        exact congr_fun
          (X.map_comp g f.op) x⟩⟩
    · rintro ⟨⟨a, ha⟩⟩
      exact ⟨⟨a, by
        rw [ha]
        exact congr_fun
          (X.map_comp g f.op) x⟩⟩

/-- The classifier square commutes:
`m ≫ wPshSieveCharMap C m = terminal ≫ truth`.
-/
theorem wPshClassifierComm
    (C : Type u) [Category.{v} C]
    {U X : Cᵒᵖ ⥤ Type (max u v)}
    (m : U ⟶ X) :
    m ≫ wPshSieveCharMap C m =
      (pshTerminalIsTerminal C).from U ≫
        pshSieveTruth C := by
  ext c u
  apply Sieve.ext
  intro V f
  dsimp [wPshSieveCharMap, sieveOfSection,
    range, fiber, pshSieveTruth,
    pshSieveFunctor]
  refine iff_of_true ⟨⟨U.map f.op u, ?_⟩⟩
    trivial
  have := congr_fun (m.naturality f.op) u
  dsimp at this
  exact this

/-- From the cone condition, the
`WSubfunctor.fiber` at the identity is
inhabited. -/
theorem wPshSieveTopFiber
    {C : Type u} [Category.{v} C]
    {U X : Cᵒᵖ ⥤ Type (max u v)}
    (m : U ⟶ X) (c : Cᵒᵖ) (x : X.obj c)
    (h : (WSubfunctor.range m).sieveOfSection
      x = ⊤) :
    Nonempty
      ((WSubfunctor.range m).fiber c x) := by
  have hmem :
      ((WSubfunctor.range m).sieveOfSection
        x).arrows (𝟙 c.unop) := by
    rw [h]; trivial
  dsimp [sieveOfSection, range, fiber]
    at hmem ⊢
  simp only [FunctorToTypes.map_id_apply]
    at hmem
  exact hmem

/-- The subobject classifier square is a
pullback, via `WSubfunctor`. -/
theorem wPshSieveIsPullback
    {C : Type u} [Category.{v} C]
    {U X : Cᵒᵖ ⥤ Type (max u v)}
    (m : U ⟶ X) [Mono m] :
    IsPullback m
      ((pshTerminalIsTerminal C).from U)
      (wPshSieveCharMap C m)
      (pshSieveTruth C) where
  w := wPshClassifierComm C m
  isLimit' := by
    have hfib : ∀ (s : PullbackCone
        (wPshSieveCharMap C m)
        (pshSieveTruth C))
        (c : Cᵒᵖ) (w : s.pt.obj c),
        Nonempty ((WSubfunctor.range m).fiber
          c (s.fst.app c w)) :=
      fun s c w => wPshSieveTopFiber m c _
        (congr_fun
          (congr_app s.condition c) w)
    have hinj := pshMono_app_injective m
    refine ⟨PullbackCone.isLimitAux'
      (PullbackCone.mk m
        ((pshTerminalIsTerminal C).from U)
        (wPshClassifierComm C m))
      fun s =>
      ⟨{ app := fun c w =>
            (hfib s c w).some.1
         naturality := fun c₁ c₂ f => by
           ext w
           apply hinj c₂
           have h1 :=
             (hfib s c₂
               (s.pt.map f w)).some.2
           have h2 :=
             (hfib s c₁ w).some.2
           have nat_m :=
             congr_fun (m.naturality f)
               ((hfib s c₁ w).some.1)
           have nat_s :=
             congr_fun
               (s.fst.naturality f) w
           dsimp at h1 h2 nat_m nat_s
           change m.app c₂
             ((hfib s c₂
               (s.pt.map f w)).some.1) =
             m.app c₂
               (U.map f
                 ((hfib s c₁ w).some.1))
           rw [h1, nat_m, h2]
           exact nat_s },
       ?_, ?_, ?_⟩⟩
    · ext c w
      exact (hfib s c w).some.2
    · ext c w
      dsimp [pshTerminal]
      exact Subsingleton.elim _ _
    · intro l h₁ _
      ext c w
      apply hinj c
      have h1a :=
        congr_fun (congr_app h₁ c) w
      change m.app c (l.app c w) =
        s.fst.app c w at h1a
      rw [h1a]
      exact (hfib s c w).some.2.symm

/-- Uniqueness of the classifying map. -/
theorem wPshSieveCharMap_uniq
    {C : Type u} [Category.{v} C]
    {U X : Cᵒᵖ ⥤ Type (max u v)}
    (m : U ⟶ X) [Mono m]
    (χ' : X ⟶ pshSieveFunctor C)
    (hpb : IsPullback m
      ((pshTerminalIsTerminal C).from U)
      χ' (pshSieveTruth C)) :
    χ' = wPshSieveCharMap C m := by
  rw [show wPshSieveCharMap C m =
    pshSieveCharMap C m from by
      ext c x
      exact sieveOfSection_eq_toSubfunctor
        (WSubfunctor.range m) x]
  exact pshSieveCharMap_uniq m χ' hpb

/-- The subobject classifier data for
`Cᵒᵖ ⥤ Type (max u v)`, via `WSubfunctor`.
-/
def wPshClassifierData
    (C : Type u) [Category.{v} C] :
    Classifier
      (Cᵒᵖ ⥤ Type (max u v)) :=
  Classifier.mkOfTerminalΩ₀
    (pshTerminal C)
    (pshTerminalIsTerminal C)
    (pshSieveFunctor C)
    (pshSieveTruth C)
    (χ := fun m _ => wPshSieveCharMap C m)
    (isPullback :=
      fun m _ => wPshSieveIsPullback m)
    (uniq :=
      fun m _ χ' hpb =>
        wPshSieveCharMap_uniq m χ' hpb)

/-- `HasClassifier` instance via `WSubfunctor`.
-/
@[reducible]
def wPshHasClassifier
    (C : Type u) [Category.{v} C] :
    HasClassifier
      (Cᵒᵖ ⥤ Type (max u v)) :=
  ⟨⟨wPshClassifierData C⟩⟩

end WSubfunctor

end WSubfunctorSieves

end GebLean
