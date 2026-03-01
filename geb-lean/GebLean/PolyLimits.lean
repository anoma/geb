import GebLean.PolyAlg
import GebLean.Utilities.ConnectedComponents
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Pi
import Mathlib.CategoryTheory.Limits.Shapes.Connected

/-!
# Polynomial Functors Preserve Connected Limits

A polynomial functor `polyBetweenEvalFunctor X Y P : Over X ⥤ Over Y`
sends `A` to `Σ y, Σ i, Hom(B_{y,i}, A)` over `Y`.  This is a
coproduct of representable functors.  Representable functors
preserve all limits (Yoneda), and coproducts commute with
connected limits, so the composite preserves connected limits.

The result holds for all polynomial functors between slices,
not just endofunctors.  Since
`polyBetweenEvalFunctor X Y P = polyToOverFunctor Y P`
(definitionally), the main theorem is stated for
`polyToOverFunctor`.  The endofunctor case
`polyEndoFunctor P = polyToOverFunctor X P` is a corollary.

The core limit constructions (`ccrIsLimitOfIsLimit` and
`polyToOverFamilyIsLimitOfIsLimit`) are stated under
`IsInhabitedConnected J` and are fully constructive.  The
`PreservesLimitsOfShape` instances use `IsConnected J`
and bridge to `IsInhabitedConnected` via
`Classical.inhabited_of_nonempty`.
-/

namespace GebLean

open CategoryTheory CategoryTheory.Limits

universe u

variable {D : Type (u + 1)} [Category.{u} D]

section CcrInhabitedConnectedLimits

variable {J : Type u} [Category.{u} J] [IsPreconnected J]
variable {P : CoprodCovarRepCat D}

/--
On a preconnected index category, the index component
of a cone over `K ⋙ ccrToFunctor P` is constant: for
any element `x` of the cone apex and any two objects
`j j' : J`, the index at `j` equals the index at `j'`.
-/
lemma ccrEvalIndex_const
    {K : J ⥤ D} (s : Cone (K ⋙ ccrToFunctor P))
    (x : s.pt) (j j' : J) :
    ccrEvalIndex (s.π.app j x) =
      ccrEvalIndex (s.π.app j' x) := by
  apply constant_of_preserves_morphisms
    (fun j => ccrEvalIndex (s.π.app j x))
  intro j₁ j₂ f
  have h := congr_fun (s.w f) x
  simp only [Functor.comp_map, types_comp_apply] at h
  rw [← h]
  rfl

/--
Given a cone `s` over `K ⋙ ccrToFunctor P` and an element
`x : s.pt` with a fixed reference object `j₀ : J`, transport
the morphism component at any `j` to have source
`ccrFamily P (ccrEvalIndex (s.π.app j₀ x))`.
-/
def ccrLiftMor
    {K : J ⥤ D} (s : Cone (K ⋙ ccrToFunctor P))
    (x : s.pt) (j₀ j : J) :
    ccrFamily P (ccrEvalIndex (s.π.app j₀ x)) ⟶
      K.obj j :=
  eqToHom (congr_arg (ccrFamily P)
    (ccrEvalIndex_const s x j₀ j)) ≫
  ccrEvalMor (s.π.app j x)

/--
Naturality of `ccrLiftMor`: for `f : j₁ ⟶ j₂`,
`ccrLiftMor s x j₀ j₁ ≫ K.map f = ccrLiftMor s x j₀ j₂`.
-/
lemma ccrLiftMor_naturality
    {K : J ⥤ D} (s : Cone (K ⋙ ccrToFunctor P))
    (x : s.pt) (j₀ : J) {j₁ j₂ : J} (f : j₁ ⟶ j₂) :
    ccrLiftMor s x j₀ j₁ ≫ K.map f =
      ccrLiftMor s x j₀ j₂ := by
  simp only [ccrLiftMor, Category.assoc]
  have hw := congr_fun (s.w f) x
  simp only [Functor.comp_map, types_comp_apply] at hw
  apply eq_of_heq
  have hmheq : ccrEvalMor (s.π.app j₁ x) ≫ K.map f ≍
      ccrEvalMor (s.π.app j₂ x) := by
    have := congr_arg_heq Sigma.snd hw
    simp only [ccrEvalMap, ccrToFunctor] at this
    exact this
  exact (eqToHom_comp_heq
    (ccrEvalMor (s.π.app j₁ x) ≫ K.map f) _).trans
    (hmheq.trans
      (eqToHom_comp_heq
        (ccrEvalMor (s.π.app j₂ x)) _).symm)

/--
Given a cone `s` over `K ⋙ ccrToFunctor P`, an element
`x : s.pt`, and a reference object `j₀ : J`, form a
cone over `K` with apex `ccrFamily P i₀` where
`i₀ = ccrEvalIndex (s.π.app j₀ x)`.
-/
def ccrLiftCone
    {K : J ⥤ D} (s : Cone (K ⋙ ccrToFunctor P))
    (x : s.pt) (j₀ : J) :
    Cone K where
  pt := ccrFamily P (ccrEvalIndex (s.π.app j₀ x))
  π := {
    app := ccrLiftMor s x j₀
    naturality := by
      intro j₁ j₂ f
      simp only [Functor.const_obj_obj,
        Functor.const_obj_map, Category.id_comp]
      exact (ccrLiftMor_naturality s x j₀ f).symm
  }

/--
The factorization property for the lift: the composite
`ccrEvalMk i₀ (hc.lift (...) ≫ c.π.app j)` equals
`s.π.app j x`.
-/
lemma ccrLiftCone_fac_sigma
    {K : J ⥤ D} {c : Cone K} (hc : IsLimit c)
    (s : Cone (K ⋙ ccrToFunctor P))
    (x : s.pt) (j₀ j : J) :
    ccrEvalMk (ccrEvalIndex (s.π.app j₀ x))
      (hc.lift (ccrLiftCone s x j₀) ≫ c.π.app j) =
    s.π.app j x := by
  rw [hc.fac (ccrLiftCone s x j₀) j]
  apply ccrEval_ext
  · simp only [ccrEvalMk_index]
    exact ccrEvalIndex_const s x j₀ j
  · simp only [ccrEvalMk_mor]
    exact eqToHom_comp_heq _ _

/--
Given `m x : ccrEval P c.pt` that satisfies the
factorization condition through `c`, the transported
morphism `eqToHom h ≫ ccrEvalMor (m x)` gives the
same cone projections as `ccrLiftCone`.
-/
lemma ccrLiftCone_uniq_aux
    {K : J ⥤ D} {c : Cone K}
    (s : Cone (K ⋙ ccrToFunctor P))
    (m : s.pt → (ccrToFunctor P).obj c.pt)
    (hm : ∀ j, (ccrToFunctor P).map (c.π.app j) ∘ m =
      s.π.app j)
    (x : s.pt) (j₀ : J)
    (hidx : ccrEvalIndex (m x) =
      ccrEvalIndex (s.π.app j₀ x)) (j : J) :
    eqToHom (congr_arg (ccrFamily P) hidx.symm) ≫
      ccrEvalMor (m x) ≫ c.π.app j =
    ccrLiftMor s x j₀ j := by
  apply eq_of_heq
  have hmj := congr_fun (hm j) x
  simp only [ccrToFunctor] at hmj
  exact (eqToHom_comp_heq
    (ccrEvalMor (m x) ≫ c.π.app j) _).trans
    ((congr_arg_heq ccrEvalMor hmj).trans
      (eqToHom_comp_heq _ _).symm)

/--
Coproducts of covariant representables preserve
connected limits (constructive version).  Given
`[IsInhabitedConnected J]`, the limit cone of
`ccrToFunctor P` applied to a limit cone `c` is
itself a limit.
-/
def ccrIsLimitOfIsLimit
    [Inhabited J] (P : CoprodCovarRepCat D)
    {K : J ⥤ D} {c : Cone K} (hc : IsLimit c) :
    IsLimit ((ccrToFunctor P).mapCone c) where
  lift s x :=
    let j₀ : J := default
    ccrEvalMk (ccrEvalIndex (s.π.app j₀ x))
      (hc.lift (ccrLiftCone s x j₀))
  fac s j := by
    funext x
    simp only [Functor.comp_obj,
      types_comp_apply, ccrToFunctor]
    exact ccrLiftCone_fac_sigma hc s x _ j
  uniq s m hm := by
    funext x
    simp only [Functor.comp_obj,
      ccrToFunctor] at hm ⊢
    let j₀ : J := default
    have hidx : ccrEvalIndex (m x) =
        ccrEvalIndex (s.π.app j₀ x) := by
      have hmj₀ := congr_fun (hm j₀) x
      rw [← ccrEvalMap_index (c.π.app j₀)]
      exact congr_arg ccrEvalIndex hmj₀
    apply ccrEval_ext
    · simp only [ccrEvalMk_index]
      exact hidx
    · simp only [ccrEvalMk_mor]
      apply HEq.trans
        (b := eqToHom (congr_arg (ccrFamily P)
          hidx.symm) ≫ ccrEvalMor (m x))
      · exact (eqToHom_comp_heq _ _).symm
      · apply heq_of_eq
        exact hc.uniq (ccrLiftCone s x j₀)
          (eqToHom (congr_arg (ccrFamily P)
            hidx.symm) ≫ ccrEvalMor (m x))
          (fun j => by
            rw [Category.assoc]
            exact ccrLiftCone_uniq_aux
              s m hm x j₀ hidx j)

end CcrInhabitedConnectedLimits

section CcrConnectedLimits

variable {J : Type u} [Category.{u} J] [IsConnected J]

/--
Coproducts of covariant representables preserve
connected limits.
-/
instance ccrPreservesConnectedLimits
    (P : CoprodCovarRepCat D) :
    PreservesLimitsOfShape J (ccrToFunctor P) where
  preservesLimit {K} := {
    preserves := fun {c} hc => by
      haveI : Inhabited J :=
        Classical.inhabited_of_nonempty inferInstance
      exact ⟨ccrIsLimitOfIsLimit P hc⟩
  }

end CcrConnectedLimits

section PolyFamilyConnectedLimits

variable {J : Type u} [Category.{u} J]
variable {Y : Type u}

/--
The family functor `polyToOverFamilyFunctor Y P` applied
to a limit cone yields a limit (constructive version).
Limits in `FamilyCat (Type u) Y = ∀ _ : Y, Type u` are
pointwise, and at each fiber `y`, the evaluation is
`ccrToFunctor (P y)`, which preserves connected limits
by `ccrIsLimitOfIsLimit`.
-/
def polyToOverFamilyIsLimitOfIsLimit
    [IsInhabitedConnected J]
    (P : PolyToOverCat (D := D) Y)
    {K : J ⥤ D} {c : Cone K} (hc : IsLimit c) :
    IsLimit ((polyToOverFamilyFunctor Y P).mapCone
      c) :=
  have hcy : ∀ y,
      IsLimit (CategoryTheory.pi.coneCompEval
        ((polyToOverFamilyFunctor Y P).mapCone
          c) y) :=
    fun y => ccrIsLimitOfIsLimit (P y) hc
  CategoryTheory.pi.coneOfConeEvalIsLimit hcy

/--
The family functor `polyToOverFamilyFunctor Y P`
preserves connected limits.
-/
instance polyToOverFamilyPreservesConnectedLimits
    [IsConnected J]
    (P : PolyToOverCat (D := D) Y) :
    PreservesLimitsOfShape J
      (polyToOverFamilyFunctor Y P) where
  preservesLimit {K} := {
    preserves := fun {c} hc => by
      haveI : Inhabited J :=
        Classical.inhabited_of_nonempty inferInstance
      haveI : IsInhabitedConnected J := {}
      exact ⟨polyToOverFamilyIsLimitOfIsLimit P hc⟩
  }

/--
The polynomial functor `polyToOverFunctor Y P` preserves
connected limits.  This factors as
`polyToOverFamilyFunctor Y P ⋙ familySliceForward Y`
(definitionally), and both components preserve connected
limits: the first by
`polyToOverFamilyPreservesConnectedLimits`, and the
second because it is an equivalence functor.
-/
instance polyToOverFunctorPreservesConnectedLimits
    [IsConnected J]
    (P : PolyToOverCat (D := D) Y) :
    PreservesLimitsOfShape J
      (polyToOverFunctor Y P) := by
  have : (familySliceForward Y).IsEquivalence :=
    (familySliceEquiv Y).isEquivalence_functor
  exact inferInstanceAs (PreservesLimitsOfShape J
    (polyToOverFamilyFunctor Y P ⋙
      familySliceForward Y))

end PolyFamilyConnectedLimits

section PolyBetweenConnectedLimits

variable {J : Type u} [Category.{u} J] [IsConnected J]
variable {X Y : Type u}

/--
Polynomial functors `Over X ⥤ Over Y` preserve
connected limits.
-/
instance polyBetweenPreservesConnectedLimits
    (P : PolyFunctorBetweenCat X Y) :
    PreservesLimitsOfShape J
      (polyBetweenEvalFunctor X Y P) :=
  polyToOverFunctorPreservesConnectedLimits P

/--
Polynomial endofunctors on `Over X` preserve
connected limits.
-/
instance polyEndoPreservesConnectedLimits
    (P : PolyEndo X) :
    PreservesLimitsOfShape J
      (polyEndoFunctor X P) :=
  polyBetweenPreservesConnectedLimits P

end PolyBetweenConnectedLimits

section WidePullbackInstances

variable {X Y : Type u}

/--
Polynomial functors preserve wide pullbacks.
-/
instance polyBetweenPreservesWidePullbacks
    (P : PolyFunctorBetweenCat X Y)
    (J : Type u) :
    PreservesLimitsOfShape (WidePullbackShape J)
      (polyBetweenEvalFunctor X Y P) :=
  polyBetweenPreservesConnectedLimits P

end WidePullbackInstances

end GebLean
