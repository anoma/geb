import GebLean.NatArith

/-!
# NNO Recursion from PBTO

Derives a natural number object (NNO) recursion interface
from the parameterized binary tree object (PBTO).  The
tree type `T` contains right-spine naturals (trees where
all left children are leaf).  The NNO interface wraps
the PBTO fold to operate specifically with this natural
number structure, using `toRSpineNat` to normalize
trees before folding.
-/

namespace GebLean

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]
  [h : HasChosenFiniteProducts C]
  [p : HasPBTO C]

/-- The NNO fold: normalize via `toRSpineNat`, then
fold with unary step.  Given `f : A ⟶ X` (base case)
and `g : X ⟶ X` (step), produces a morphism
`A × T ⟶ X` that recursively folds a right-spine
natural. -/
def nnoElim {A X : C} (f : A ⟶ X) (g : X ⟶ X) :
    cfpProd A p.T ⟶ X :=
  cfpMap (𝟙 A) toRSpineNat ≫
    p.elim f (cfpSnd X X ≫ g)

/-- Base case: `nnoElim(a, ℓ) = f(a)`. -/
theorem nnoElim_ℓ {A X : C}
    (f : A ⟶ X) (g : X ⟶ X) :
    cfpInsertSnd p.ℓ A ≫ nnoElim f g = f := by
  unfold nnoElim
  rw [← Category.assoc]
  have insert_rsn :
      cfpInsertSnd p.ℓ A ≫
        cfpMap (𝟙 A) toRSpineNat =
      cfpInsertSnd p.ℓ A := by
    unfold cfpInsertSnd
    rw [cfpLift_cfpMap, Category.id_comp,
      Category.assoc, toRSpineNat_ℓ]
  rw [insert_rsn, p.elim_ℓ]

/-- Composing `cfpMap (𝟙 A) natSucc` with
`p.elim f (cfpSnd X X ≫ g)` yields
`p.elim f (cfpSnd X X ≫ g) ≫ g`. -/
private theorem natSucc_elim_step
    {A X : C}
    (f : A ⟶ X) (g : X ⟶ X) :
    cfpMap (𝟙 A) natSucc ≫
      p.elim f (cfpSnd X X ≫ g) =
    p.elim f (cfpSnd X X ≫ g) ≫ g := by
  have step_def :
      cfpMap (𝟙 A) natSucc =
      cfpMap (𝟙 A)
        (cfpLift (cfpTerminalFrom p.T ≫ p.ℓ)
          (𝟙 p.T)) ≫
        cfpMap (𝟙 A) p.β := by
    show cfpMap (𝟙 A) natSucc = _
    unfold natSucc
    rw [cfpMap_id_comp']
  rw [step_def, Category.assoc, p.elim_β]
  -- Goal: cfpMap (𝟙 A) (cfpLift ...) ≫
  --   cfpLiftAssoc (elim) (elim) ≫
  --   cfpSnd X X ≫ g = elim ≫ g
  -- Suffices: ... ≫ cfpSnd X X = elim.
  have liftAssoc_snd :
      cfpLiftAssoc
        (p.elim f (cfpSnd X X ≫ g))
        (p.elim f (cfpSnd X X ≫ g)) ≫
        cfpSnd X X =
      cfpAssocSnd A p.T p.T ≫
        p.elim f (cfpSnd X X ≫ g) := by
    unfold cfpLiftAssoc
    rw [cfpLift_snd]
  -- Goal: cfpMap (𝟙 A) (cfpLift ...) ≫
  --   cfpLiftAssoc (elim) (elim) ≫
  --   cfpSnd X X ≫ g = elim ≫ g
  have cancel :
      cfpMap (𝟙 A)
        (cfpLift (cfpTerminalFrom p.T ≫ p.ℓ)
          (𝟙 p.T)) ≫
        cfpAssocSnd A p.T p.T =
      𝟙 (cfpProd A p.T) := by
    rw [← cfpMap_id A p.T]
    unfold cfpAssocSnd
    apply cfpLift_uniq
    · rw [Category.assoc, cfpLift_fst,
        cfpMap_fst, Category.comp_id]
    · rw [Category.assoc, cfpLift_snd,
        ← Category.assoc, cfpMap_snd,
        Category.assoc, cfpLift_snd]
  rw [← Category.assoc
    (cfpLiftAssoc _ _) (cfpSnd X X) g,
    liftAssoc_snd,
    Category.assoc
      (cfpAssocSnd A p.T p.T)
      (p.elim f (cfpSnd X X ≫ g)) g,
    ← Category.assoc
      (cfpMap (𝟙 A) _)
      (cfpAssocSnd A p.T p.T),
    cancel, Category.id_comp]

/-- Step case:
`nnoElim(a, natSucc(n)) = g(nnoElim(a, n))`. -/
theorem nnoElim_s {A X : C}
    (f : A ⟶ X) (g : X ⟶ X) :
    cfpMap (𝟙 A) natSucc ≫ nnoElim f g =
    nnoElim f g ≫ g := by
  unfold nnoElim
  rw [← Category.assoc,
    ← cfpMap_id_comp' natSucc toRSpineNat,
    natSucc_toRSpineNat_comm,
    cfpMap_id_comp',
    Category.assoc,
    natSucc_elim_step f g,
    ← Category.assoc]

/-- The step function for `toRSpineNat`
(`cfpLift (term ≫ ℓ) (cfpSnd ≫ toRSN) ≫ β`)
equals `cfpSnd ≫ toRSpineNat ≫ natSucc`. -/
private theorem toRSpineNat_step_factor :
    cfpLift
      (cfpTerminalFrom (cfpProd p.T p.T) ≫ p.ℓ)
      (cfpSnd p.T p.T ≫ toRSpineNat) ≫ p.β =
    cfpSnd p.T p.T ≫ toRSpineNat ≫
      (natSucc : p.T ⟶ p.T) := by
  -- Both sides end with ≫ β; reduce to showing
  -- the cfpLift parts agree.
  have lift_eq :
      cfpSnd p.T p.T ≫ toRSpineNat ≫
        cfpLift (cfpTerminalFrom p.T ≫ p.ℓ)
          (𝟙 p.T) =
      cfpLift
        (cfpTerminalFrom
          (cfpProd p.T p.T) ≫ p.ℓ)
        (cfpSnd p.T p.T ≫ toRSpineNat) := by
    rw [cfpLift_precomp, cfpLift_precomp,
      Category.comp_id]
    have term_eq :
        cfpSnd p.T p.T ≫ toRSpineNat ≫
          cfpTerminalFrom p.T =
        cfpTerminalFrom (cfpProd p.T p.T) :=
      h.terminal.uniq _
    rw [show cfpSnd p.T p.T ≫ toRSpineNat ≫
        cfpTerminalFrom p.T ≫ p.ℓ =
        (cfpSnd p.T p.T ≫ toRSpineNat ≫
          cfpTerminalFrom p.T) ≫ p.ℓ from
        by simp only [Category.assoc],
      term_eq]
  unfold natSucc
  rw [← Category.assoc
    (toRSpineNat)
    (cfpLift (cfpTerminalFrom p.T ≫ p.ℓ)
      (𝟙 p.T))
    p.β,
    ← Category.assoc
      (cfpSnd p.T p.T)
      (toRSpineNat ≫
        cfpLift (cfpTerminalFrom p.T ≫ p.ℓ)
          (𝟙 p.T))
      p.β,
    lift_eq]

/-- `cfpInsertSnd ℓ A ≫ cfpMap (𝟙 A) toRSpineNat`
absorbs the normalization. -/
private theorem insert_ℓ_rsn (A : C) :
    cfpInsertSnd p.ℓ A ≫
      cfpMap (𝟙 A) (toRSpineNat : p.T ⟶ p.T) =
    cfpInsertSnd p.ℓ A := by
  unfold cfpInsertSnd
  rw [cfpLift_cfpMap, Category.id_comp,
    Category.assoc, toRSpineNat_ℓ]

/-- The β-step for `cfpMap (𝟙 A) toRSpineNat ≫ φ`
when `φ` satisfies the NNO natSucc step. -/
private theorem rsn_φ_β_step
    {A X : C}
    (φ : cfpProd A p.T ⟶ X)
    (g : X ⟶ X)
    (hs : cfpMap (𝟙 A) natSucc ≫ φ = φ ≫ g) :
    cfpMap (𝟙 A) p.β ≫
      cfpMap (𝟙 A) toRSpineNat ≫ φ =
    cfpLiftAssoc
      (cfpMap (𝟙 A) toRSpineNat ≫ φ)
      (cfpMap (𝟙 A) toRSpineNat ≫ φ) ≫
      (cfpSnd X X ≫ g) := by
  -- LHS: rewrite to cfpMap (𝟙 A) (β ≫ toRSN) ≫ φ.
  rw [← Category.assoc, ← cfpMap_id_comp']
  -- LHS: cfpMap (𝟙 A) (β ≫ toRSN) ≫ φ.
  -- Apply toRSpineNat_β inside cfpMap.
  conv_lhs =>
    rw [toRSpineNat_β,
      toRSpineNat_step_factor]
  -- LHS: cfpMap (𝟙 A)
  --   (snd ≫ toRSN ≫ natSucc) ≫ φ.
  rw [cfpMap_id_comp'
    (cfpSnd p.T p.T)
    (toRSpineNat ≫ natSucc)]
  have cfpMap_snd_eq :
      cfpMap (𝟙 A) (cfpSnd p.T p.T) =
      cfpAssocSnd A p.T p.T := by
    unfold cfpMap cfpAssocSnd
    congr 1
    exact Category.comp_id _
  rw [cfpMap_snd_eq,
    cfpMap_id_comp' toRSpineNat natSucc]
  simp only [Category.assoc]
  rw [hs]
  -- LHS: cfpAssocSnd ≫ cfpMap (𝟙 A) toRSN ≫
  --   φ ≫ g.
  -- RHS: cfpLiftAssoc ψ ψ ≫ cfpSnd X X ≫ g.
  rw [← Category.assoc
    (cfpLiftAssoc _ _) (cfpSnd X X) g]
  unfold cfpLiftAssoc
  rw [cfpLift_snd]
  simp only [Category.assoc]

/-- Any `toRSpineNat`-invariant morphism satisfying
the base and step conditions equals `nnoElim`. -/
theorem nnoElim_uniq {A X : C}
    (f : A ⟶ X) (g : X ⟶ X)
    (φ : cfpProd A p.T ⟶ X)
    (hℓ : cfpInsertSnd p.ℓ A ≫ φ = f)
    (hs :
      cfpMap (𝟙 A) natSucc ≫ φ = φ ≫ g)
    (hnorm :
      cfpMap (𝟙 A) toRSpineNat ≫ φ = φ) :
    φ = nnoElim f g := by
  -- φ = cfpMap (𝟙 A) toRSN ≫ φ by hnorm, so
  -- φ satisfies the PBTO conditions for
  -- p.elim f (cfpSnd X X ≫ g).
  have liftAssoc_rsn :
      cfpLiftAssoc
        (cfpMap (𝟙 A) toRSpineNat ≫ φ)
        (cfpMap (𝟙 A) toRSpineNat ≫ φ) =
      cfpLiftAssoc φ φ := by
    unfold cfpLiftAssoc
    congr 1 <;> rw [hnorm]
  have β_step :
      cfpMap (𝟙 A) p.β ≫ φ =
      cfpLiftAssoc φ φ ≫
        (cfpSnd X X ≫ g) := by
    conv_lhs => rw [hnorm.symm]
    rw [rsn_φ_β_step φ g hs, liftAssoc_rsn]
  unfold nnoElim
  conv_lhs => rw [hnorm.symm]
  congr 1
  exact p.elim_uniq f (cfpSnd X X ≫ g)
    φ hℓ β_step

/-- Cantor unpairing: `T ⟶ T × T`. Embeds the
input as a terminal-parameterized tree, then
applies the unpairing catamorphism. -/
def cantorUnpair : p.T ⟶ cfpProd p.T p.T :=
  cfpLift (cfpTerminalFrom p.T) (𝟙 p.T) ≫
    cantorUnpairHelper

end GebLean
