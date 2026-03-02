import GebLean.PolyAlg
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Pi
import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Finitary Polynomial Functors Preserve Filtered Colimits

A polynomial functor `polyBetweenEvalFunctor X Y P`
is a coproduct of covariant representables.  When the
polynomial is finitary (`PolyBetweenFinitary`), each
representable has a finite fiber type.  Finite products
commute with filtered colimits, so the coproduct of
finitely-fibered representables preserves filtered
colimits.

The proof follows the same layered decomposition as
`PolyLimits.lean`: CCR level, `Over Y` level, between
level, endo level.
-/

namespace GebLean

open CategoryTheory CategoryTheory.Limits

universe u

/-! ## Filtered Factorization in Over X -/

section FilteredFactorization

variable {X : Type u}

instance overForgetPreservesColimitsOfSize :
    PreservesColimitsOfSize.{u, u}
      (Over.forget (X : Type u)) :=
  (Over.forgetAdjStar X).leftAdjoint_preservesColimits

variable {J : Type u} [Category.{u} J] [IsFiltered J]

set_option linter.unusedFintypeInType false in
lemma overFilteredFactor
    {K : J ⥤ Over X} {c : Cocone K}
    (hc : IsColimit c)
    {B : Over X} [Fintype B.left]
    (f : B ⟶ c.pt) :
    ∃ (j : J) (g : B ⟶ K.obj j),
      g ≫ c.ι.app j = f := by
  have hcT : IsColimit
      ((Over.forget X).mapCocone c) :=
    isColimitOfPreserves (Over.forget X) hc
  have hsurj : ∀ b : B.left,
      ∃ (j : J) (y : (K.obj j).left),
        (c.ι.app j).left y = f.left b :=
    fun b => Types.jointly_surjective_of_isColimit
      hcT (f.left b)
  haveI : DecidableEq J := Classical.decEq J
  choose jB yB hyB using hsurj
  let indices : Finset J :=
    Finset.image jB Finset.univ
  obtain ⟨j₀, hj₀⟩ :=
    IsFiltered.sup_objs_exists indices
  have toJ₀ : ∀ b : B.left, jB b ⟶ j₀ :=
    fun b => (hj₀ (Finset.mem_image_of_mem jB
      (Finset.mem_univ b))).some
  let g₀ : B.left → (K.obj j₀).left :=
    fun b => (K.map (toJ₀ b)).left (yB b)
  have hg₀_over :
      (K.obj j₀).hom ∘ g₀ = B.hom := by
    funext b
    change (K.obj j₀).hom
        ((K.map (toJ₀ b)).left (yB b)) =
      B.hom b
    have hkw := Over.w (K.map (toJ₀ b))
    have hcw := Over.w (c.ι.app (jB b))
    have hfw := Over.w f
    change _ ≫ (K.obj j₀).hom =
      (K.obj (jB b)).hom at hkw
    change _ ≫ c.pt.hom =
      (K.obj (jB b)).hom at hcw
    change _ ≫ c.pt.hom = B.hom at hfw
    calc (K.obj j₀).hom
          ((K.map (toJ₀ b)).left (yB b))
        = ((K.map (toJ₀ b)).left ≫
            (K.obj j₀).hom) (yB b) := rfl
      _ = (K.obj (jB b)).hom (yB b) :=
          congr_fun hkw (yB b)
      _ = ((c.ι.app (jB b)).left ≫
            c.pt.hom) (yB b) :=
          (congr_fun hcw (yB b)).symm
      _ = c.pt.hom (f.left b) := by
          simp only [types_comp_apply,
            hyB b]
      _ = (f.left ≫ c.pt.hom) b := rfl
      _ = B.hom b := congr_fun hfw b
  let g : B ⟶ K.obj j₀ :=
    Over.homMk g₀ hg₀_over
  refine ⟨j₀, g, ?_⟩
  apply Over.OverMorphism.ext
  funext b
  simp only [Over.comp_left, types_comp_apply]
  change (c.ι.app j₀).left (g₀ b) = f.left b
  have hnat :=
    congrArg CommaMorphism.left (c.w (toJ₀ b))
  simp only [Functor.const_obj_obj,
    Over.comp_left] at hnat
  calc (c.ι.app j₀).left (g₀ b)
      = (c.ι.app j₀).left
          ((K.map (toJ₀ b)).left (yB b)) := rfl
    _ = ((K.map (toJ₀ b)).left ≫
          (c.ι.app j₀).left) (yB b) := rfl
    _ = (c.ι.app (jB b)).left (yB b) := by
        rw [hnat]
    _ = f.left b := hyB b

private lemma filteredEqualCombine
    {K : J ⥤ Over X}
    {B : Over X} {j : J}
    {g₁ g₂ : B ⟶ K.obj j}
    (kB : B.left → J) (fB : ∀ b, j ⟶ kB b)
    (hfB : ∀ b,
      (K.map (fB b)).left (g₁.left b) =
      (K.map (fB b)).left (g₂.left b))
    (S : Finset B.left) :
    ∃ (k : J) (h : j ⟶ k),
      ∀ b ∈ S,
        (K.map h).left (g₁.left b) =
        (K.map h).left (g₂.left b) := by
  induction S using Finset.cons_induction with
  | empty =>
    exact ⟨j, 𝟙 j, fun _ hb =>
      absurd hb (Finset.notMem_empty _)⟩
  | cons b₀ S hne ih =>
    obtain ⟨kS, hS, hkS⟩ := ih
    obtain ⟨m₀, w₁, w₂, _⟩ :=
      IsFilteredOrEmpty.cocone_objs
        kS (kB b₀)
    obtain ⟨m₁, e, he⟩ :=
      IsFilteredOrEmpty.cocone_maps
        (hS ≫ w₁) (fB b₀ ≫ w₂)
    refine ⟨m₁, (hS ≫ w₁) ≫ e,
      fun b hb => ?_⟩
    rw [Finset.mem_cons] at hb
    rcases hb with rfl | hb
    · have step :
          (K.map ((fB b ≫ w₂) ≫ e)).left
            (g₁.left b) =
          (K.map ((fB b ≫ w₂) ≫ e)).left
            (g₂.left b) := by
        simp only [Functor.map_comp,
          Over.comp_left, types_comp_apply]
        exact congrArg ((K.map e).left)
          (congrArg ((K.map w₂).left) (hfB b))
      rwa [← he] at step
    · have := hkS b hb
      simp only [Functor.map_comp,
        Over.comp_left,
        types_comp_apply] at this ⊢
      exact congrArg ((K.map e).left)
        (congrArg ((K.map w₁).left) this)

set_option linter.unusedFintypeInType false in
lemma overFilteredEqual
    {K : J ⥤ Over X} {c : Cocone K}
    (hc : IsColimit c)
    {B : Over X} [Fintype B.left]
    {j : J} (g₁ g₂ : B ⟶ K.obj j)
    (heq : g₁ ≫ c.ι.app j = g₂ ≫ c.ι.app j) :
    ∃ (k : J) (h : j ⟶ k),
      g₁ ≫ K.map h = g₂ ≫ K.map h := by
  have hcT : IsColimit
      ((Over.forget X).mapCocone c) :=
    isColimitOfPreserves (Over.forget X) hc
  have heqL : ∀ b : B.left,
      ((Over.forget X).mapCocone c).ι.app j
        (g₁.left b) =
      ((Over.forget X).mapCocone c).ι.app j
        (g₂.left b) := by
    intro b
    have h := congr_fun
      (congrArg CommaMorphism.left heq) b
    simp only [Over.comp_left,
      types_comp_apply] at h
    exact h
  have hptwise : ∀ b : B.left,
      ∃ (k : J) (h : j ⟶ k),
        (K.map h).left (g₁.left b) =
        (K.map h).left (g₂.left b) := by
    intro b
    have hb := heqL b
    rw [Types.FilteredColimit.isColimit_eq_iff
      (K ⋙ Over.forget X) hcT] at hb
    obtain ⟨k, f, g, hfg⟩ := hb
    obtain ⟨m, e, he⟩ :=
      IsFilteredOrEmpty.cocone_maps f g
    refine ⟨m, f ≫ e, ?_⟩
    change (K.map (f ≫ e)).left (g₁.left b) =
      (K.map (f ≫ e)).left (g₂.left b)
    have lhs :
        (K.map (f ≫ e)).left (g₁.left b) =
        (K.map e).left
          ((K.map f).left (g₁.left b)) := by
      simp only [Functor.map_comp,
        Over.comp_left, types_comp_apply]
    have rhs :
        (K.map (f ≫ e)).left (g₂.left b) =
        (K.map e).left
          ((K.map g).left (g₂.left b)) := by
      conv_lhs => rw [he]
      simp only [Functor.map_comp,
        Over.comp_left, types_comp_apply]
    rw [lhs, rhs]
    exact congrArg (K.map e).left hfg
  choose kB fB hfB using hptwise
  obtain ⟨k, h, hk⟩ :=
    filteredEqualCombine kB fB hfB Finset.univ
  exact ⟨k, h, by
    apply Over.OverMorphism.ext
    funext b
    simp only [Over.comp_left, types_comp_apply]
    exact hk b (Finset.mem_univ b)⟩

end FilteredFactorization

/-! ## Finitary CCR Preserves Filtered Colimits -/

section CcrFilteredColimits

variable {X : Type u}
variable {J : Type u} [Category.{u} J] [IsFiltered J]

omit [IsFiltered J] in
private lemma ccrFilteredNatApp
    {P : CoprodCovarRepCat (Over (X : Type u))}
    {K : J ⥤ Over X}
    (s : Cocone (K ⋙ ccrToFunctor P))
    (i : ccrIndex P) {j₁ j₂ : J}
    (g : ccrFamily P i ⟶ K.obj j₁) (h : j₁ ⟶ j₂) :
    s.ι.app j₁ (ccrEvalMk i g) =
    s.ι.app j₂
      (ccrEvalMk i (g ≫ K.map h)) := by
  have := congr_fun (s.w h) (ccrEvalMk i g)
  simp only [Functor.comp_map,
    types_comp_apply] at this
  exact this.symm

private lemma ccrFilteredCoconeConsistent
    {P : CoprodCovarRepCat (Over (X : Type u))}
    (hfin : ∀ i, Finite (ccrFamily P i).left)
    {K : J ⥤ Over X} {c : Cocone K}
    (hc : IsColimit c)
    (s : Cocone (K ⋙ ccrToFunctor P))
    (i : ccrIndex P)
    {j₁ j₂ : J}
    (g₁ : ccrFamily P i ⟶ K.obj j₁)
    (g₂ : ccrFamily P i ⟶ K.obj j₂)
    (heq : g₁ ≫ c.ι.app j₁ =
      g₂ ≫ c.ι.app j₂) :
    s.ι.app j₁ (ccrEvalMk i g₁) =
    s.ι.app j₂ (ccrEvalMk i g₂) := by
  haveI := hfin i
  haveI : Fintype (ccrFamily P i).left :=
    Fintype.ofFinite _
  obtain ⟨k, h₁, h₂, _⟩ :=
    IsFilteredOrEmpty.cocone_objs j₁ j₂
  have heqk :
      (g₁ ≫ K.map h₁) ≫ c.ι.app k =
      (g₂ ≫ K.map h₂) ≫ c.ι.app k := by
    simp only [Category.assoc, c.w]
    exact heq
  obtain ⟨k', h, hk⟩ :=
    overFilteredEqual hc
      (g₁ ≫ K.map h₁) (g₂ ≫ K.map h₂)
      heqk
  have hk_left :
      (g₁ ≫ K.map h₁) ≫ K.map h =
      (g₂ ≫ K.map h₂) ≫ K.map h := by
    have := congrArg CommaMorphism.left hk
    simp only [Over.comp_left] at this
    exact Over.OverMorphism.ext this
  calc s.ι.app j₁ (ccrEvalMk i g₁)
      = s.ι.app k
          (ccrEvalMk i (g₁ ≫ K.map h₁)) :=
        ccrFilteredNatApp s i g₁ h₁
    _ = s.ι.app k'
          (ccrEvalMk i
            ((g₁ ≫ K.map h₁) ≫ K.map h)) :=
        ccrFilteredNatApp s i _ h
    _ = s.ι.app k'
          (ccrEvalMk i
            ((g₂ ≫ K.map h₂) ≫ K.map h)) :=
        congrArg
          (s.ι.app k' ∘ ccrEvalMk i) hk_left
    _ = s.ι.app k
          (ccrEvalMk i (g₂ ≫ K.map h₂)) :=
        (ccrFilteredNatApp s i _ h).symm
    _ = s.ι.app j₂ (ccrEvalMk i g₂) :=
        (ccrFilteredNatApp s i g₂ h₂).symm

instance ccrPreservesFilteredColimits
    (P : CoprodCovarRepCat (Over (X : Type u)))
    (hfin : ∀ i, Finite (ccrFamily P i).left) :
    PreservesColimitsOfShape J
      (ccrToFunctor P) where
  preservesColimit {K} := {
    preserves := fun {c} hc => by
      have descFact :
          ∀ x : ccrEval P c.pt,
          ∃ (j : J) (g : ccrFamily P
            (ccrEvalIndex x) ⟶ K.obj j),
          g ≫ c.ι.app j = ccrEvalMor x :=
        fun x => by
          haveI := hfin (ccrEvalIndex x)
          haveI := Fintype.ofFinite
            (ccrFamily P (ccrEvalIndex x)).left
          exact overFilteredFactor hc
            (ccrEvalMor x)
      exact ⟨{
        desc := fun s x =>
          s.ι.app (descFact x).choose
            (ccrEvalMk (ccrEvalIndex x)
              (descFact x).choose_spec.choose)
        fac := fun s j => by
          funext y
          simp only [types_comp_apply]
          let z := ccrEvalMap (c.ι.app j) y
          let dz := descFact z
          let jz := dz.choose
          let gz := dz.choose_spec.choose
          let hgz := dz.choose_spec.choose_spec
          change s.ι.app jz
            (ccrEvalMk (ccrEvalIndex y) gz) =
            s.ι.app j
              (ccrEvalMk (ccrEvalIndex y)
                (ccrEvalMor y))
          exact ccrFilteredCoconeConsistent
            hfin hc s _ gz (ccrEvalMor y) hgz
        uniq := fun s m hm => by
          funext x
          let dx := descFact x
          let jx := dx.choose
          let gx := dx.choose_spec.choose
          let hgx := dx.choose_spec.choose_spec
          change m x =
            s.ι.app jx
              (ccrEvalMk (ccrEvalIndex x) gx)
          have hx :
              ccrEvalMap (c.ι.app jx)
                (ccrEvalMk (ccrEvalIndex x)
                  gx) = x :=
            Sigma.ext rfl (heq_of_eq hgx)
          conv_lhs => rw [← hx]
          have hmj := congr_fun (hm jx)
            (ccrEvalMk (ccrEvalIndex x) gx)
          simp only [types_comp_apply] at hmj
          exact hmj
      }⟩
  }

end CcrFilteredColimits

/-! ## Lifting Through Polynomial Layers -/

section PolyFamilyFilteredColimits

variable {X Y : Type u}
variable {J : Type u} [Category.{u} J] [IsFiltered J]

instance polyToOverFamilyPreservesFiltered
    (P : PolyToOverCat (D := Over X) Y)
    (hfin : ∀ (y : Y) (i : ccrIndex (P y)),
      Finite (ccrFamily (P y) i).left) :
    PreservesColimitsOfShape J
      (polyToOverFamilyFunctor Y P) where
  preservesColimit {K} := {
    preserves := fun {c} hc => by
      have hcy : ∀ y,
          IsColimit
            (CategoryTheory.pi.coconeCompEval
              ((polyToOverFamilyFunctor Y
                P).mapCocone c) y) := by
        intro y
        have inst :
            PreservesColimitsOfShape J
              (ccrToFunctor (P y)) :=
          ccrPreservesFilteredColimits
            (P y) (hfin y)
        exact (inst.preservesColimit
          (K := K) |>.preserves hc).some
      exact ⟨pi.coconeOfCoconeEvalIsColimit hcy⟩
  }

instance polyToOverPreservesFiltered
    (P : PolyToOverCat (D := Over X) Y)
    (hfin : ∀ (y : Y) (i : ccrIndex (P y)),
      Finite (ccrFamily (P y) i).left) :
    PreservesColimitsOfShape J
      (polyToOverFunctor Y P) := by
  haveI : (familySliceForward Y).IsEquivalence :=
    (familySliceEquiv Y).isEquivalence_functor
  haveI : PreservesColimitsOfShape J
      (polyToOverFamilyFunctor Y P) :=
    polyToOverFamilyPreservesFiltered P hfin
  exact inferInstanceAs
    (PreservesColimitsOfShape J
      (polyToOverFamilyFunctor Y P ⋙
        familySliceForward Y))

end PolyFamilyFilteredColimits

section PolyBetweenFilteredColimits

variable {X Y : Type u}
variable {J : Type u} [Category.{u} J] [IsFiltered J]

instance polyBetweenPreservesFiltered
    (P : PolyFunctorBetweenCat X Y)
    [hf : PolyBetweenFinitary X Y P] :
    PreservesColimitsOfShape J
      (polyBetweenEvalFunctor X Y P) :=
  polyToOverPreservesFiltered P
    (fun y i =>
      @Finite.of_fintype _
        (hf.data.familyFintype y i))

instance polyEndoPreservesFiltered
    (P : PolyEndo X)
    [PolyBetweenFinitary X X P] :
    PreservesColimitsOfShape J
      (polyEndoFunctor X P) :=
  polyBetweenPreservesFiltered P

end PolyBetweenFilteredColimits

section FreeMonadFilteredColimits

variable {X : Type u}
variable {J : Type u} [Category.{u} J] [IsFiltered J]

instance polyFreeMonadPreservesFiltered
    (P : PolyEndo X)
    [PolyBetweenFinitary X X P] :
    PreservesColimitsOfShape J
      (polyFreeMonad X P).toFunctor :=
  preservesColimitsOfShape_of_natIso
    (polyFreeMonadIso X P).symm

instance polyAlgHasFilteredColimitsOfShape
    (P : PolyEndo X)
    [PolyBetweenFinitary X X P] :
    HasColimitsOfShape J (PolyAlg P) := by
  haveI : HasColimitsOfShape J
      (polyFreeMonad X P).Algebra :=
    hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape
      (Monad.forget (polyFreeMonad X P))
  exact Adjunction.hasColimitsOfShape_of_equivalence
    (polyAlgMonadEquiv X P).functor

end FreeMonadFilteredColimits

end GebLean
