/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.Logic.Equiv.Defs
public import Aesop

/-!
# Prototype: where the free coproduct completion sits inside presheaves

Throwaway exploration, not upstream-eligible content. Every declaration here is
`Classical.choice`-free.

`Fam(C)`, the free set-indexed coproduct completion of `C`
(Remarks 2.3 of [GhaniNordvallForsbergMalatesta2015]), embeds into `PSh(C)` as
the coproducts of representables. `Geb/Prototypes/FinCardUniverse/` works over
`PSh(C)`, so the question is which presheaf polynomial functors carry `Fam(C)`
into itself — whether a universe built over presheaves can be read back as a
family of codes.

This module answers it, and the answer is not the one the value computation of
`FinCardUniverse` might suggest. Membership in `Fam(C)` is closed under
set-indexed coproducts, so a representable times a constant is still in `Fam(C)`:
`isFamPsh_praPsh` shows that the shape of the p.r.a. formula's value —
a sum over shapes of a representable times the set of arity homs — is a family
presheaf whatever that set of arity homs is. So the functors do restrict, and the
coercion multiplicity the finite model exhibits is not an obstruction to
restricting: it lands in the code type, not in the decoding.

What does obstruct is the shape presheaf. Since `T₁ = T(1)`, a functor restricts
only if the terminal presheaf's image does, and the terminal presheaf need not
itself lie in `Fam(C)`: `isFamPsh_topPsh_of_terminal` shows it does when `C` has
a terminal object, and `not_isFamPsh_topPsh` shows it does not over the walking
parallel pair, which has none. The category of elements of the terminal presheaf
is `C` itself, so this is the general criterion — a presheaf lies in `Fam(C)`
exactly when every connected component of its category of elements has a
terminal object — read at the terminal presheaf. That general criterion is not
formalized here; the two brackets are.

## Main definitions

* `famPsh` — a family of objects as a presheaf, the coproduct of representables
  `Σ_u y(d u)`.
* `IsFamPsh` — membership in the image, as an unbundled natural isomorphism.
* `praPsh` — the shape of the p.r.a. formula's value: a sum over shapes of a
  representable times a set.
* `topPsh` — the terminal presheaf.

## Main statements

* `isFamPsh_praPsh` — the p.r.a. formula's value is a family presheaf, with the
  codes the shapes paired with their arity homs and the decoding read off the
  shape alone.
* `isFamPsh_topPsh_of_terminal` — the terminal presheaf is a family presheaf
  when the base has a terminal object.
* `not_isFamPsh_topPsh` — and is not, over the walking parallel pair.

## References

* [GhaniNordvallForsbergMalatesta2015]
* [Weber2007]

## Tags

prototype, presheaf, free coproduct completion, parametric right adjoint,
inductive-recursive
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace GebProto.FamBoundary

/-! ## Family presheaves -/

variable {C : Type} [SmallCategory C]

/-- A family of objects as a presheaf: the coproduct of representables
`Σ_u y(d u)`. This is the embedding of `Fam(C)` into `PSh(C)`. -/
def famPsh (U : Type) (d : U → C) : Cᵒᵖ ⥤ Type where
  obj c := Σ u : U, (c.unop ⟶ d u)
  map f := ↾ fun x ↦ (⟨x.1, f.unop ≫ x.2⟩ : Σ u : U, (_ ⟶ d u))
  map_id _ := by
    ext x
    · rfl
    · exact heq_of_eq (Category.id_comp x.2)
  map_comp _ _ := by
    ext x
    · rfl
    · exact heq_of_eq (Category.assoc _ _ x.2)

/-- A presheaf lies in the image of `Fam(C)`: it is naturally isomorphic to a
family presheaf. The isomorphism is unbundled — a family of equivalences with
the naturality equation — so that no hom of a functor category is named and the
statement stays `Classical.choice`-free. -/
def IsFamPsh (Z : Cᵒᵖ ⥤ Type) : Prop :=
  ∃ (U : Type) (d : U → C) (e : ∀ c, Z.obj c ≃ (famPsh U d).obj c),
    ∀ ⦃c c' : Cᵒᵖ⦄ (f : c ⟶ c') (x : Z.obj c),
      e c' (Z.map f x) = (famPsh U d).map f (e c x)

/-! ## The p.r.a. formula's value

At a shape presheaf that is itself a family presheaf, and an arity assignment
depending only on the shape's index, the p.r.a. formula
`T(Z)(j) = Σ_{a ∈ T₁(j)} Hom(E_a, Z)` takes the form below: a sum over shapes of
a representable times the set of arity homs. -/

/-- The p.r.a. formula's value: shapes `S` lying over objects `o s`, each
carrying a set `A s` of arity homs. -/
def praPsh (S : Type) (o : S → C) (A : S → Type) : Cᵒᵖ ⥤ Type where
  obj c := Σ s : S, (c.unop ⟶ o s) × A s
  map f := ↾ fun x ↦ (⟨x.1, f.unop ≫ x.2.1, x.2.2⟩ : Σ s : S, (_ ⟶ o s) × A s)
  map_id _ := by
    ext x
    · rfl
    · exact heq_of_eq (Prod.ext (Category.id_comp x.2.1) rfl)
  map_comp _ _ := by
    ext x
    · rfl
    · exact heq_of_eq (Prod.ext (Category.assoc _ _ x.2.1) rfl)

/-- The p.r.a. formula's value is a family presheaf: the codes are the shapes
paired with their arity homs, and the decoding is read off the shape alone.

This is why the multiplicity of arity homs is no obstruction to restricting to
`Fam(C)`: it is absorbed into the code type, the coproduct completion being
closed under set-indexed coproducts. It is also why restricting does not recover
an inductive-recursive interpretation — the decoding `o s` does not mention the
arity hom, so it does not depend on the codes the shape binds. -/
theorem isFamPsh_praPsh (S : Type) (o : S → C) (A : S → Type) :
    IsFamPsh (praPsh S o A) :=
  ⟨Σ s : S, A s, fun p ↦ o p.1,
    fun _ ↦
      { toFun := fun x ↦ ⟨⟨x.1, x.2.2⟩, x.2.1⟩
        invFun := fun y ↦ ⟨y.1.1, y.2, y.1.2⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl },
    fun _ _ _ _ ↦ rfl⟩

/-! ## The terminal presheaf

`T₁ = T(1)`, so a functor restricts only if the terminal presheaf's image does.
Whether the terminal presheaf is itself a family presheaf is a property of the
base. -/

/-- The terminal presheaf. -/
def topPsh (C : Type) [SmallCategory C] : Cᵒᵖ ⥤ Type where
  obj _ := PUnit
  map _ := ↾ fun _ ↦ PUnit.unit
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Over a base with a terminal object, the terminal presheaf is the
representable it represents, hence a family presheaf. -/
theorem isFamPsh_topPsh_of_terminal (t : C) (h : ∀ c : C, Unique (c ⟶ t)) :
    IsFamPsh (topPsh C) :=
  ⟨PUnit, fun _ ↦ t,
    fun c ↦
      { toFun := fun _ ↦ ⟨PUnit.unit, (h c.unop).default⟩
        invFun := fun _ ↦ PUnit.unit
        left_inv := fun _ ↦ rfl
        right_inv := fun y ↦ Sigma.ext rfl (heq_of_eq ((h c.unop).uniq y.2).symm) },
    fun _ _ _ _ ↦ Sigma.ext rfl (heq_of_eq ((h _).uniq _).symm)⟩

/-! ## A base where it fails

The walking parallel pair has no terminal object: `zero` is not terminal because
nothing maps from `one` to it, and `one` is not because two morphisms map into it
from `zero`. -/

/-- Nothing maps from `one` to `zero`. -/
theorem isEmpty_one_to_zero :
    IsEmpty (WalkingParallelPair.one ⟶ WalkingParallelPair.zero) :=
  ⟨fun f ↦ by cases f⟩

/-- The two parallel morphisms are distinct. -/
theorem left_ne_right :
    (WalkingParallelPairHom.left : WalkingParallelPair.zero ⟶ WalkingParallelPair.one)
      ≠ WalkingParallelPairHom.right := by
  intro h
  exact absurd h (by simp)

/-- Over the walking parallel pair the terminal presheaf is not a family
presheaf. A code would have to decode to `one`, since nothing maps from `one` to
`zero`; but then the two parallel morphisms give two elements over `zero`, where
a family presheaf isomorphic to the terminal one has exactly one. -/
theorem not_isFamPsh_topPsh : ¬ IsFamPsh (topPsh WalkingParallelPair) := by
  rintro ⟨U, d, e, -⟩
  obtain ⟨u, f⟩ := e ⟨WalkingParallelPair.one⟩ PUnit.unit
  have key : ∀ g h : WalkingParallelPair.zero ⟶ d u, g = h := by
    intro g h
    have hp : (e ⟨WalkingParallelPair.zero⟩).symm ⟨u, g⟩
        = (e ⟨WalkingParallelPair.zero⟩).symm ⟨u, h⟩ := rfl
    exact eq_of_heq (Sigma.ext_iff.mp ((e ⟨WalkingParallelPair.zero⟩).symm.injective hp)).2
  generalize hdu : d u = X at f key
  cases f
  exact left_ne_right (key _ _)

/-! ## Universal elements

A family presheaf's category of elements is a coproduct of slices, and a code is
recovered as the terminal object of its component: the element carrying the
identity — the universal element of that representable summand, in the sense of
the Yoneda correspondence, and Lawvere's generic figure.

The word "generic" is avoided here. In the parametric-right-adjoint literature
this repository cites ([Weber2007], [nLabParametricRightAdjoint]) a morphism
`f : B ⟶ T A` is *T-generic* when every commuting square over it has a unique
`T`-fill, and `T` is a parametric right adjoint exactly when every map into a
`T`-value factors as a generic followed by a `T`-image. Under that factorization
it is the *coercion* that is the generic part and the universal element that is
the trivially-factoring one, so calling the latter generic would invert the
established usage in the one setting where it is in play.

The universal element is what an inductive-recursive constraint on a direction
would ask for — asking for it says `d u = i` on the nose, where asking for an
arbitrary element says only `i ⟶ d u`.

The constraint cannot be imposed while keeping every morphism of families,
because universality is not stable: a morphism sends the universal element of `u` to
its own decoding map, which is universal only when that map is a transport.
`isUniversalElement_famMorApp` is the stability on the morphisms that do preserve it —
the split cartesian fragment, which is Dybjer and Setzer's setting.

`IsSplitCoercion` weakens the constraint from "the coercion is a transport" to
"the coercion is a split epimorphism", and `isSplitCoercion_famMorApp` is the
corresponding stability: it holds on the morphisms whose decoding maps are split
epimorphisms. So there is a constraint strictly weaker than universality that
survives non-invertible morphisms, which is the setting
`Geb/Prototypes/UniverseVariance/` shows both type formers act over. -/

/-- The universal element of a code's component: the code with the identity. -/
def universalElement (U : Type) (d : U → C) (u : U) : (famPsh U d).obj ⟨d u⟩ :=
  ⟨u, 𝟙 (d u)⟩

/-- An element is universal when its coercion is a transport: the object it lies
over is the code's decoding, on the nose. -/
def IsUniversalElement {U : Type} {d : U → C} {c : Cᵒᵖ} (x : (famPsh U d).obj c) : Prop :=
  ∃ h : c.unop = d x.1, x.2 = eqToHom h

/-- A morphism of families: a map of codes and, for each code, a morphism of
decodings. -/
structure FamMor (U : Type) (d : U → C) (U' : Type) (d' : U' → C) where
  /-- The map of codes. -/
  code : U → U'
  /-- The comparison of decodings. -/
  dec : ∀ u, d u ⟶ d' (code u)

/-- The action of a morphism of families on the family presheaves. -/
def famMorApp {U : Type} {d : U → C} {U' : Type} {d' : U' → C}
    (m : FamMor U d U' d') {c : Cᵒᵖ} (x : (famPsh U d).obj c) : (famPsh U' d').obj c :=
  ⟨m.code x.1, x.2 ≫ m.dec x.1⟩

/-- The action is natural. -/
theorem famMorApp_natural {U : Type} {d : U → C} {U' : Type} {d' : U' → C}
    (m : FamMor U d U' d') ⦃c c' : Cᵒᵖ⦄ (f : c ⟶ c') (x : (famPsh U d).obj c) :
    famMorApp m ((famPsh U d).map f x) = (famPsh U' d').map f (famMorApp m x) :=
  congrArg (Sigma.mk (m.code x.1)) (Category.assoc _ _ _)

/-- A morphism preserves universal elements when every decoding comparison is a
transport. These are the split cartesian morphisms, and Dybjer and Setzer's
`Fam |C|` is the fragment they span. -/
def PreservesUniversalElement {U : Type} {d : U → C} {U' : Type} {d' : U' → C}
    (m : FamMor U d U' d') : Prop :=
  ∀ u, ∃ h : d u = d' (m.code u), m.dec u = eqToHom h

/-- Genericity is stable under the morphisms that preserve it. -/
theorem isUniversalElement_famMorApp {U : Type} {d : U → C} {U' : Type} {d' : U' → C}
    {m : FamMor U d U' d'} (hm : PreservesUniversalElement m) {c : Cᵒᵖ}
    {x : (famPsh U d).obj c} (hx : IsUniversalElement x) : IsUniversalElement (famMorApp m x) := by
  obtain ⟨h₁, hx₁⟩ := hx
  obtain ⟨h₂, hm₂⟩ := hm x.1
  refine ⟨h₁.trans h₂, ?_⟩
  change x.2 ≫ m.dec x.1 = _
  rw [hx₁, hm₂, eqToHom_trans]
  rfl

/-- The weakened constraint: the coercion is a split epimorphism. -/
def IsSplitCoercion {U : Type} {d : U → C} {c : Cᵒᵖ} (x : (famPsh U d).obj c) : Prop :=
  ∃ s : d x.1 ⟶ c.unop, s ≫ x.2 = 𝟙 (d x.1)

/-- A universal element satisfies the weakened constraint, so it is a genuine
weakening. -/
theorem isSplitCoercion_of_isUniversalElement {U : Type} {d : U → C} {c : Cᵒᵖ}
    {x : (famPsh U d).obj c} (hx : IsUniversalElement x) : IsSplitCoercion x := by
  obtain ⟨h, hx₁⟩ := hx
  refine ⟨eqToHom h.symm, ?_⟩
  rw [hx₁, eqToHom_trans, eqToHom_refl]

/-- A morphism whose decoding comparisons are split epimorphisms. -/
def SplitDec {U : Type} {d : U → C} {U' : Type} {d' : U' → C}
    (m : FamMor U d U' d') : Prop :=
  ∀ u, ∃ t : d' (m.code u) ⟶ d u, t ≫ m.dec u = 𝟙 (d' (m.code u))

/-- The weakened constraint is stable under those morphisms: a constraint
strictly weaker than universality survives morphisms that are not transports, and
need not be invertible. -/
theorem isSplitCoercion_famMorApp {U : Type} {d : U → C} {U' : Type} {d' : U' → C}
    {m : FamMor U d U' d'} (hm : SplitDec m) {c : Cᵒᵖ}
    {x : (famPsh U d).obj c} (hx : IsSplitCoercion x) :
    IsSplitCoercion (famMorApp m x) := by
  obtain ⟨s, hs⟩ := hx
  obtain ⟨t, ht⟩ := hm x.1
  refine ⟨t ≫ s, ?_⟩
  change (t ≫ s) ≫ x.2 ≫ m.dec x.1 = _
  rw [← Category.assoc, Category.assoc t s x.2, hs, Category.comp_id, ht]
  rfl

end GebProto.FamBoundary
