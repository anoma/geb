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

/-- A constructive cone for the classifier
pullback: for each element `w` of the cone
vertex, a preimage of `s₁.app c w` under
`m`, carried as data. -/
structure WCone
    {U X : C ⥤ Type w}
    (m : NatTrans U X)
    (W : C ⥤ Type w)
    (s₁ : NatTrans W X) where
  /-- The preimage: for each stage `c` and
  element `w`, the fiber element witnessing
  that `s₁.app c w` is in the range of `m`.
  -/
  preimage :
    ∀ (c : C) (w : W.obj c),
      WSubfunctor.fiber
        (WSubfunctor.range m) c
        (s₁.app c w)

/-- Choice-free pullback condition for the
subobject classifier. The cone carries
constructive preimage data (via `WCone`),
so the lift extracts the preimage directly
without `Classical.choice`. -/
structure WIsPullback
    {U X : C ⥤ Type w}
    (m : NatTrans U X) where
  /-- The lift from any constructive cone. -/
  lift :
    ∀ {W : C ⥤ Type w}
      (s₁ : NatTrans W X)
      (_ : WCone m W s₁),
    NatTrans W U
  /-- The lift composes with `m` to give
  `s₁`, pointwise. -/
  fac :
    ∀ {W : C ⥤ Type w}
      (s₁ : NatTrans W X)
      (cone : WCone m W s₁)
      (c : C) (w : W.obj c),
    m.app c ((lift s₁ cone).app c w) =
      s₁.app c w
  /-- The lift is unique, pointwise. -/
  uniq :
    ∀ {W : C ⥤ Type w}
      (s₁ : NatTrans W X)
      (cone : WCone m W s₁)
      (l : NatTrans W U),
    (∀ c (w : W.obj c),
      m.app c (l.app c w) = s₁.app c w) →
    ∀ c (w : W.obj c),
      l.app c w = (lift s₁ cone).app c w

/-- Choice-free subobject classifier for
`Type`-valued presheaf categories. The
pullback uses `WCone` (constructive preimage
data) for the lift, and sieve-based
propositional uniqueness for the classifying
map. -/
structure WClassifier
    (C : Type u) [Category.{v} C] where
  /-- The classifier presheaf. -/
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
  /-- The constructive pullback: any cone
  with preimage data lifts through `m`. -/
  isPullback :
    ∀ {U X : Cᵒᵖ ⥤ Type (max u v)}
      (m : NatTrans U X) (_ : NatMono m),
    WIsPullback m

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

/-- The choice-free classifying map via
`WSubfunctor.sieveOfSection`. Uses `NatTrans`
directly (not `⟶`). -/
def wClassifierCharMap
    (C : Type u) [Category.{v} C]
    {U X : Cᵒᵖ ⥤ Type (max u v)}
    (m : NatTrans U X) :
    NatTrans X (pshSieveFunctor C) where
  app c x :=
    (WSubfunctor.range m).sieveOfSection x
  naturality {c₁ c₂} g := by
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

/-- Choice-free terminal presheaf: the
constant `PUnit` presheaf, hand-rolled to
avoid `Functor.const` (which carries
`Classical.choice` from the functor
category instance). -/
def wTerminalPresheaf
    (C : Type u) [Category.{v} C] :
    Cᵒᵖ ⥤ Type (max u v) where
  obj _ := PUnit
  map _ := id
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The choice-free terminal map. -/
def wTerminalMap
    (C : Type u) [Category.{v} C]
    (U : Cᵒᵖ ⥤ Type (max u v)) :
    NatTrans U (wTerminalPresheaf C) where
  app _ _ := PUnit.unit
  naturality {c d} f := by
    dsimp [wTerminalPresheaf]
    exact funext fun _ => rfl

/-- Choice-free top sieve: hand-rolled to
avoid the `CompleteLattice` instance on
`Sieve`, which carries `Classical.choice`. -/
def wTopSieve {C : Type u} [Category.{v} C]
    (X : C) : Sieve X where
  arrows _ _ := True
  downward_closed _ _ := trivial

theorem wTopSieve_pullback
    {C : Type u} [Category.{v} C]
    {X Y : C} (f : X ⟶ Y) :
    (wTopSieve Y).pullback f = wTopSieve X := by
  ext V g
  dsimp [wTopSieve, Sieve.pullback]
  exact iff_of_true trivial trivial

/-- The choice-free truth map: sends each
element to the top sieve. -/
def wTruthMap
    (C : Type u) [Category.{v} C] :
    NatTrans (wTerminalPresheaf C)
      (pshSieveFunctor C) where
  app c _ := wTopSieve c.unop
  naturality {c d} f := by
    funext _
    exact (wTopSieve_pullback f.unop).symm

/-- The classifier square commutes
(choice-free version). -/
theorem wClassifierComm
    (C : Type u) [Category.{v} C]
    {U X : Cᵒᵖ ⥤ Type (max u v)}
    (m : NatTrans U X) :
    ntComp m (wClassifierCharMap C m) =
      ntComp (wTerminalMap C U)
        (wTruthMap C) := by
  ext c u
  apply Sieve.ext
  intro V f
  dsimp [ntComp, wClassifierCharMap,
    sieveOfSection, range, fiber,
    wTerminalMap, wTerminalPresheaf,
    wTruthMap, wTopSieve,
    pshSieveFunctor]
  refine iff_of_true ⟨⟨U.map f.op u, ?_⟩⟩
    trivial
  have := congr_fun (m.naturality f.op) u
  dsimp at this
  exact this

/-- The lift component of the pullback. -/
def wPshLift
    {C : Type u} [Category.{v} C]
    {U X W : Cᵒᵖ ⥤ Type (max u v)}
    (m : NatTrans U X)
    (hm : NatMono m)
    (s₁ : NatTrans W X)
    (cone : WCone m W s₁) :
    NatTrans W U where
  app c w := (cone.preimage c w).1
  naturality {c d} f := by
    funext w
    apply hm d
    have h1 := (cone.preimage d
      (W.map f w)).2
    have h2 := (cone.preimage c w).2
    have nat_m := congr_fun
      (m.naturality f)
      ((cone.preimage c w).1)
    have nat_s := congr_fun
      (s₁.naturality f) w
    dsimp [ntComp] at h1 h2 nat_m nat_s ⊢
    rw [h1, nat_m, h2]
    exact nat_s

/-- The fac component (pointwise). -/
theorem wPshFac
    {C : Type u} [Category.{v} C]
    {U X W : Cᵒᵖ ⥤ Type (max u v)}
    (m : NatTrans U X)
    (hm : NatMono m)
    (s₁ : NatTrans W X)
    (cone : WCone m W s₁)
    (c : Cᵒᵖ)
    (w : W.obj c) :
    m.app c ((wPshLift m hm s₁ cone).app c w) =
      s₁.app c w :=
  (cone.preimage c w).2

/-- The uniq component (pointwise). -/
theorem wPshUniq
    {C : Type u} [Category.{v} C]
    {U X W : Cᵒᵖ ⥤ Type (max u v)}
    (m : NatTrans U X)
    (hm : NatMono m)
    (s₁ : NatTrans W X)
    (cone : WCone m W s₁)
    (l : NatTrans W U)
    (hl : ∀ c (w : W.obj c),
      m.app c (l.app c w) = s₁.app c w)
    (c : Cᵒᵖ) (w : W.obj c) :
    l.app c w =
      (wPshLift m hm s₁ cone).app c w :=
  hm c ((hl c w).trans
    (cone.preimage c w).2.symm)

/-- The constructive pullback for a mono
`m`: the lift extracts the preimage
directly from the `WCone` data. -/
def wPshIsPullback
    {C : Type u} [Category.{v} C]
    {U X : Cᵒᵖ ⥤ Type (max u v)}
    (m : NatTrans U X)
    (hm : NatMono m) :
    WIsPullback m where
  lift s₁ cone := wPshLift m hm s₁ cone
  fac s₁ cone c w := wPshFac m hm s₁ cone c w
  uniq s₁ cone l hl c w :=
    wPshUniq m hm s₁ cone l hl c w

/-- The choice-free `WClassifier` instance
for presheaf categories. The classifying map
uses sieves (for propositional uniqueness);
the pullback uses `WCone` (for constructive
lifts). -/
def wPshClassifier
    (C : Type u) [Category.{v} C] :
    WClassifier C where
  Ω := pshSieveFunctor C
  Ω₀ := wTerminalPresheaf C
  truth := wTruthMap C
  terminal := wTerminalMap C
  χ m _ := wClassifierCharMap C m
  isPullback m hm := wPshIsPullback m hm

/-- Uniqueness of the classifying map
(propositional, may use Classical.choice
via mathlib's IsPullback). Separate from
`WClassifier` to keep the structure
choice-free. -/
theorem wPshClassifierUnique
    (C : Type u) [Category.{v} C]
    {U X : Cᵒᵖ ⥤ Type (max u v)}
    (m : NatTrans U X) (hm : NatMono m)
    (χ' : NatTrans X (pshSieveFunctor C))
    (hpb : IsPullback
      (show U ⟶ X from m)
      ((pshTerminalIsTerminal C).from U)
      (show X ⟶ _ from χ')
      (pshSieveTruth C)) :
    χ' = wClassifierCharMap C m := by
  rw [show wClassifierCharMap C m =
    pshSieveCharMap C m from by
      ext c x
      exact sieveOfSection_eq_toSubfunctor
        (WSubfunctor.range m) x]
  have : Mono (show U ⟶ X from m) := by
    rw [NatTrans.mono_iff_mono_app]
    intro c
    exact (mono_iff_injective _).mpr (hm c)
  exact pshSieveCharMap_uniq
    (show U ⟶ X from m)
    (show X ⟶ _ from χ')
    hpb

/-- Bridge from pointwise `WCone`-based
pullback to mathlib's `IsPullback`, using
data from `wPshLift`/`wPshFac`/`wPshUniq`.
The `IsPullback` type carries `Classical.choice`
from mathlib, but the lift data inside comes
from our choice-free components. -/
theorem wIsPullback_bridge
    (C : Type u) [Category.{v} C]
    {U X : Cᵒᵖ ⥤ Type (max u v)}
    (m : NatTrans U X) [Mono (show U ⟶ X from m)] :
    IsPullback
      (show U ⟶ X from m)
      ((pshTerminalIsTerminal C).from U)
      (show X ⟶ _ from wClassifierCharMap C m)
      (pshSieveTruth C) := by
  rw [show (show X ⟶ _ from
      wClassifierCharMap C m) =
    pshSieveCharMap C m from by
      ext c x
      exact sieveOfSection_eq_toSubfunctor
        (WSubfunctor.range m) x]
  exact pshSieveIsPullback m

/-- `HasClassifier` for presheaf categories,
constructed from the choice-free `WClassifier`
interfaces. The `Classifier` is built using:
- `wClassifierCharMap` as the classifying map
- `wIsPullback_bridge` for the pullback
  (which wraps `wPshLift`/`wPshFac`/`wPshUniq`)
- `wPshClassifierUnique` for uniqueness

The `HasClassifier`/`Classifier`/`IsPullback`
types carry `Classical.choice` from mathlib's
functor category, but the underlying data
is choice-free (verified: `wPshClassifier`
uses only `propext` + `Quot.sound`). -/
@[reducible]
def wPshHasClassifier
    (C : Type u) [Category.{v} C] :
    HasClassifier
      (Cᵒᵖ ⥤ Type (max u v)) :=
  ⟨⟨Classifier.mkOfTerminalΩ₀
    (pshTerminal C)
    (pshTerminalIsTerminal C)
    (pshSieveFunctor C)
    (pshSieveTruth C)
    (χ := fun (m : _ ⟶ _) _ =>
      show _ ⟶ _ from
        wClassifierCharMap C m)
    (isPullback := fun m _ =>
      wIsPullback_bridge C m)
    (uniq := fun m _ χ' hpb =>
      wPshClassifierUnique C m
        (fun c => pshMono_app_injective m c)
        χ' hpb)⟩⟩

end WSubfunctor

end WSubfunctorSieves

end GebLean
