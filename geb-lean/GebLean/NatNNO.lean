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

/-- `cantorPair` absorbs `toRSpineNat`:
normalizing both inputs then pairing equals
just pairing. -/
private theorem cantorPair_absorbs_rsn :
    cfpMap toRSpineNat toRSpineNat ≫
      cantorPair =
    (cantorPair :
      cfpProd p.T p.T ⟶ p.T) := by
  rw [cantorPair_toRSpineNat_comm]
  unfold cantorPair
  rw [Category.assoc,
    ← natPlus_toRSpineNat_first,
    ← Category.assoc,
    cfpLift_cfpMap,
    Category.comp_id,
    Category.assoc,
    show natTri ≫ toRSpineNat =
      natTri from
      natTri_isRSpineNatNorm]

/-- `cantorPair` absorbs `toRSpineNat` on its
first argument. -/
private theorem cantorPair_absorbs_rsn_fst :
    cfpMap toRSpineNat (𝟙 p.T) ≫
      cantorPair =
    (cantorPair :
      cfpProd p.T p.T ⟶ p.T) := by
  have step1 :
      cfpMap toRSpineNat (𝟙 p.T) ≫
        cantorPair =
      cfpMap toRSpineNat (𝟙 p.T) ≫
        cfpMap toRSpineNat toRSpineNat ≫
        cantorPair := by
    rw [cantorPair_absorbs_rsn]
  have step2 :
      cfpMap toRSpineNat (𝟙 p.T) ≫
        cfpMap (toRSpineNat : p.T ⟶ p.T)
          toRSpineNat =
      cfpMap toRSpineNat toRSpineNat := by
    rw [cfpMap_comp, toRSpineNat_idem,
      Category.id_comp]
  rw [step1, ← Category.assoc, step2,
    cantorPair_absorbs_rsn]

/-- `cantorPair(ℓ, b) = natTri(toRSN(b))`. -/
private theorem cantorPair_ℓ_snd :
    cfpLift (cfpTerminalFrom p.T ≫ p.ℓ)
      (𝟙 p.T) ≫ cantorPair =
    toRSpineNat ≫ (natTri : p.T ⟶ p.T) := by
  unfold cantorPair
  rw [← Category.assoc, cfpLift_precomp,
    cfpLift_fst,
    show cfpLift (cfpTerminalFrom p.T ≫ p.ℓ)
      (𝟙 p.T) ≫ natPlus ≫ natTri =
      toRSpineNat ≫ natTri from by
      rw [← Category.assoc,
        natPlus_ℓ_left_eq_toRSpineNat]]
  -- cfpLift (toRSN ≫ natTri) (term ≫ ℓ) ≫ natPlus
  --   = toRSN ≫ natTri
  -- because the second component is ℓ,
  -- and natPlus(x, ℓ) = x.
  have h_fst :
      cfpLift (toRSpineNat ≫ natTri)
        (cfpTerminalFrom p.T ≫ p.ℓ) ≫
        cfpFst p.T p.T = toRSpineNat ≫ natTri :=
    cfpLift_fst _ _
  have h_snd :
      cfpLift (toRSpineNat ≫ natTri)
        (cfpTerminalFrom p.T ≫ p.ℓ) ≫
        cfpSnd p.T p.T =
      cfpTerminalFrom p.T ≫ p.ℓ :=
    cfpLift_snd _ _
  have cfpInsertSnd_form :
      cfpLift (toRSpineNat ≫ natTri)
        (cfpTerminalFrom p.T ≫ p.ℓ) =
      (toRSpineNat ≫ natTri) ≫
        cfpInsertSnd p.ℓ p.T := by
    unfold cfpInsertSnd
    rw [cfpLift_precomp, Category.comp_id]
    congr 1
    have term_absorb :
        (toRSpineNat ≫ (natTri : p.T ⟶ p.T)) ≫
          cfpTerminalFrom p.T =
        cfpTerminalFrom p.T :=
      h.terminal.uniq _
    simp only [← Category.assoc] at *
    rw [term_absorb]
  rw [cfpInsertSnd_form, Category.assoc,
    natPlus_ℓ, Category.comp_id]

/-- `cantorUnpair(ℓ) = (ℓ, ℓ)`. -/
private theorem cantorUnpair_ℓ :
    p.ℓ ≫ cantorUnpair =
    cfpLift p.ℓ p.ℓ := by
  unfold cantorUnpair
  rw [← Category.assoc, cfpLift_precomp,
    Category.comp_id]
  have term_eq :
      p.ℓ ≫ cfpTerminalFrom p.T =
      cfpTerminalFrom cfpTerminal :=
    h.terminal.uniq _
  rw [term_eq]
  have embed_eq :
      cfpLift (cfpTerminalFrom cfpTerminal) p.ℓ =
      cfpInsertSnd p.ℓ cfpTerminal := by
    unfold cfpInsertSnd
    congr 1
    · exact (h.terminal.uniq _).symm
    · rw [show cfpTerminalFrom cfpTerminal =
        𝟙 cfpTerminal from
        (h.terminal.uniq _).symm,
        Category.id_comp]
  rw [embed_eq, cantorUnpairHelper_ℓ]

/-- `cantorUnpair(natSucc(n)) =
cantorNextPair(cantorUnpair(n))`. -/
private theorem cantorUnpair_natSucc :
    natSucc ≫ cantorUnpair =
    cantorUnpair ≫
      (cantorNextPair :
        cfpProd p.T p.T ⟶ cfpProd p.T p.T) := by
  unfold cantorUnpair
  -- LHS: natSucc ≫ embed ≫ UH
  -- RHS: embed ≫ UH ≫ cantorNextPair
  -- Step 1: compute natSucc ≫ embed
  have embed_succ :
      natSucc ≫
        cfpLift (cfpTerminalFrom p.T)
          (𝟙 p.T) =
      cfpLift (cfpTerminalFrom p.T)
        (natSucc : p.T ⟶ p.T) := by
    rw [cfpLift_precomp, Category.comp_id]
    congr 1
    exact h.terminal.uniq _
  -- Step 2: factor cfpLift (term) natSucc
  --   = embed ≫ cfpMap (𝟙 1) natSucc
  have succ_factor :
      cfpLift (cfpTerminalFrom p.T)
        (natSucc : p.T ⟶ p.T) =
      cfpLift (cfpTerminalFrom p.T) (𝟙 p.T) ≫
        cfpMap (𝟙 cfpTerminal) natSucc := by
    rw [cfpLift_cfpMap, Category.comp_id,
      Category.id_comp]
  -- Step 3: natSucc = cfpLift ... ≫ β
  have natSucc_as_β :
      cfpMap (𝟙 cfpTerminal)
        (natSucc : p.T ⟶ p.T) =
      cfpMap (𝟙 cfpTerminal)
        (cfpLift (cfpTerminalFrom p.T ≫ p.ℓ)
          (𝟙 p.T)) ≫
        cfpMap (𝟙 cfpTerminal) p.β := by
    unfold natSucc
    rw [cfpMap_id_comp']
  -- Step 4: cfpLiftAssoc UH UH ≫ cfpSnd
  --   = cfpAssocSnd ≫ UH
  have liftAssoc_snd :
      cfpLiftAssoc
        (cantorUnpairHelper :
          cfpProd cfpTerminal p.T ⟶
            cfpProd p.T p.T)
        cantorUnpairHelper ≫
        cfpSnd (cfpProd p.T p.T)
          (cfpProd p.T p.T) =
      cfpAssocSnd cfpTerminal p.T p.T ≫
        cantorUnpairHelper := by
    unfold cfpLiftAssoc
    rw [cfpLift_snd]
  -- Step 5: cfpMap (𝟙 1) (cfpLift ...) ≫
  --   cfpAssocSnd = 𝟙
  have cancel :
      cfpMap (𝟙 cfpTerminal)
        (cfpLift (cfpTerminalFrom p.T ≫ p.ℓ)
          (𝟙 p.T)) ≫
        cfpAssocSnd cfpTerminal p.T p.T =
      𝟙 (cfpProd cfpTerminal p.T) := by
    rw [← cfpMap_id cfpTerminal p.T]
    unfold cfpAssocSnd
    apply cfpLift_uniq
    · rw [Category.assoc, cfpLift_fst,
        cfpMap_fst, Category.comp_id]
    · rw [Category.assoc, cfpLift_snd,
        ← Category.assoc, cfpMap_snd,
        Category.assoc, cfpLift_snd]
  rw [← Category.assoc
    (natSucc : p.T ⟶ p.T), embed_succ,
    succ_factor]
  simp only [Category.assoc]
  rw [natSucc_as_β]
  simp only [Category.assoc]
  rw [cantorUnpairHelper_β]
  unfold cantorUnpairStep
  -- Goal has: ... ≫ cfpLiftAssoc UH UH ≫
  --   cfpSnd ≫ cantorNextPair
  -- Use liftAssoc_snd to replace
  --   cfpLiftAssoc UH UH ≫ cfpSnd
  --   with cfpAssocSnd ≫ UH
  rw [show cfpLiftAssoc
      cantorUnpairHelper cantorUnpairHelper ≫
      cfpSnd (cfpProd p.T p.T)
        (cfpProd p.T p.T) ≫
      cantorNextPair =
    cfpAssocSnd cfpTerminal p.T p.T ≫
      cantorUnpairHelper ≫
      cantorNextPair from by
    simp only [← Category.assoc]
    rw [liftAssoc_snd]]
  -- Goal: embed ≫ cfpMap ... ≫
  --   cfpAssocSnd ≫ UH ≫ cantorNextPair
  --   = embed ≫ UH ≫ cantorNextPair
  simp only [← Category.assoc
    (cfpMap _ _) (cfpAssocSnd _ _ _)]
  rw [cancel, Category.id_comp]

/-- The retraction property:
`cantorUnpair ≫ cantorPair = toRSpineNat`. -/
theorem cantorUnpair_cantorPair :
    cantorUnpair ≫ cantorPair =
    (toRSpineNat : p.T ⟶ p.T) := by
  unfold cantorUnpair
  rw [Category.assoc,
    cantorUnpairHelper_cantorPair]
  -- LHS = embed ≫ p.elim ℓ (cfpSnd ≫ natSucc)
  -- = toRSN, which is embed ≫ p.elim ℓ step
  -- where step = cfpSnd ≫ natSucc
  -- (after toRSpineNat_step_eq_natSucc).
  -- Use natPlus_ℓ_left_eq_toRSpineNat:
  -- cfpLift (term ≫ ℓ) (𝟙 T) ≫ natPlus = toRSN.
  -- natPlus = p.elim (𝟙 T) (cfpSnd ≫ natSucc).
  -- By elim_naturality:
  -- embed ≫ cfpMap ℓ (𝟙 T) ≫ natPlus
  -- = embed ≫ p.elim ℓ (cfpSnd ≫ natSucc).
  -- Then toRSN = embed' ≫ natPlus
  -- = embed ≫ cfpMap ℓ (𝟙 T) ≫ natPlus
  -- = embed ≫ p.elim ℓ (cfpSnd ≫ natSucc).
  rw [show cfpLift (cfpTerminalFrom p.T)
      (𝟙 p.T) ≫
      p.elim p.ℓ
        (cfpSnd p.T p.T ≫ natSucc) =
    cfpLift (cfpTerminalFrom p.T ≫ p.ℓ)
      (𝟙 p.T) ≫ natPlus from by
    have factor :
        cfpLift
          (cfpTerminalFrom p.T ≫ p.ℓ)
          (𝟙 p.T) =
        cfpLift (cfpTerminalFrom p.T)
          (𝟙 p.T) ≫
          cfpMap (p.ℓ : cfpTerminal ⟶ p.T)
            (𝟙 p.T) := by
      rw [cfpLift_cfpMap, Category.comp_id]
    rw [factor, Category.assoc]
    unfold natPlus
    rw [elim_naturality p.ℓ (𝟙 p.T)
      (cfpSnd p.T p.T ≫ natSucc),
      Category.comp_id],
    natPlus_ℓ_left_eq_toRSpineNat]

/-- `cfpFst T T` equals the fold
`p.elim (𝟙 T) (cfpSnd T T)`: the first projection
ignores the tree argument entirely, returning the
parameter unchanged. -/
private theorem cfpFst_eq_elim :
    cfpFst p.T p.T =
    p.elim (𝟙 p.T)
      (cfpSnd p.T p.T) :=
  p.elim_uniq (𝟙 p.T) (cfpSnd p.T p.T)
    (cfpFst p.T p.T)
    (by unfold cfpInsertSnd
        rw [cfpLift_fst])
    (by rw [cfpMap_fst, Category.comp_id]
        unfold cfpLiftAssoc
        rw [cfpLift_snd]
        unfold cfpAssocSnd
        rw [cfpLift_fst])

/-- Subtracting the second addend from a sum
recovers the first:
`natTruncSub(natPlus(x, c), c) = x`. -/
theorem natTruncSub_natPlus_cancel :
    cfpLift (natPlus : cfpProd p.T p.T ⟶ p.T)
      (cfpSnd p.T p.T) ≫ natTruncSub =
    cfpFst p.T p.T := by
  rw [cfpFst_eq_elim]
  apply p.elim_uniq (𝟙 p.T) (cfpSnd p.T p.T)
  · rw [← Category.assoc]
    have : cfpInsertSnd p.ℓ p.T ≫
        cfpLift natPlus (cfpSnd p.T p.T) =
      cfpInsertSnd p.ℓ p.T := by
      apply cfpLift_uniq
      · rw [Category.assoc, cfpLift_fst,
          natPlus_ℓ]
      · rw [Category.assoc, cfpLift_snd]
        unfold cfpInsertSnd
        rw [cfpLift_snd]
    rw [this]
    unfold natTruncSub
    rw [p.elim_ℓ]
  · -- Both sides equal cfpAssocSnd ≫ ψ where
    -- ψ = cfpLift natPlus (cfpSnd T T) ≫
    --   natTruncSub.
    -- Step A: Simplify the RHS.
    have h_rhs :
        cfpLiftAssoc
          (cfpLift natPlus
            (cfpSnd p.T p.T) ≫ natTruncSub)
          (cfpLift natPlus
            (cfpSnd p.T p.T) ≫ natTruncSub) ≫
          cfpSnd p.T p.T =
        cfpAssocSnd p.T p.T p.T ≫
          (cfpLift natPlus
            (cfpSnd p.T p.T) ≫
            natTruncSub) := by
      unfold cfpLiftAssoc
      rw [cfpLift_snd]
    rw [h_rhs]; clear h_rhs
    -- Step B: Factor cfpMap (𝟙 T) β through
    -- cfpLift natPlus (cfpSnd T T) to get
    -- cfpLift (... ≫ natSucc) (... ≫ β).
    have h_factor :
        cfpMap (𝟙 p.T) p.β ≫
          cfpLift natPlus (cfpSnd p.T p.T) =
        cfpLift
          (cfpLiftAssoc natPlus natPlus ≫
            cfpSnd p.T p.T ≫ natSucc)
          (cfpSnd p.T (cfpProd p.T p.T) ≫
            p.β) := by
      rw [cfpLift_precomp, natPlus_β,
        cfpMap_snd]
    -- Step C: Extract cfpMap (𝟙 T) β from the
    -- cfpLift pairing using cfpLift_cfpMap.
    have h_extract :
        cfpLift
          (cfpLiftAssoc natPlus natPlus ≫
            cfpSnd p.T p.T ≫ natSucc)
          (cfpSnd p.T (cfpProd p.T p.T) ≫
            p.β) =
        cfpLift
          (cfpLiftAssoc natPlus natPlus ≫
            cfpSnd p.T p.T ≫ natSucc)
          (cfpSnd p.T (cfpProd p.T p.T)) ≫
          cfpMap (𝟙 p.T) p.β := by
      rw [cfpLift_cfpMap, Category.comp_id]
    -- Step D: Combine to get
    -- LHS = cfpLift (...) (...) ≫
    --   cfpMap (𝟙 T) β ≫ natTruncSub.
    -- Then apply natTruncSub_β.
    have h_tsβ :
        cfpMap (𝟙 p.T) p.β ≫ natTruncSub =
        cfpLiftAssoc natTruncSub natTruncSub ≫
          (cfpSnd p.T p.T ≫ natPred) :=
      natTruncSub_β
    -- Step E: cfpLiftAssoc natTruncSub
    -- natTruncSub ≫ cfpSnd = cfpAssocSnd ≫
    -- natTruncSub.
    have h_la_snd :
        cfpLiftAssoc
          (natTruncSub :
            cfpProd p.T p.T ⟶ p.T)
          natTruncSub ≫
          cfpSnd p.T p.T =
        cfpAssocSnd p.T p.T p.T ≫
          natTruncSub := by
      unfold cfpLiftAssoc; rw [cfpLift_snd]
    -- Step F: cfpLift ≫ cfpAssocSnd
    -- = cfpLift (fst) (snd ≫ cfpSnd).
    have h_lift_assocSnd :
        cfpLift
          (cfpLiftAssoc natPlus natPlus ≫
            cfpSnd p.T p.T ≫ natSucc)
          (cfpSnd p.T (cfpProd p.T p.T)) ≫
          cfpAssocSnd p.T p.T p.T =
        cfpLift
          (cfpLiftAssoc natPlus natPlus ≫
            cfpSnd p.T p.T ≫ natSucc)
          (cfpSnd p.T (cfpProd p.T p.T) ≫
            cfpSnd p.T p.T) := by
      unfold cfpAssocSnd
      rw [cfpLift_precomp]
      apply cfpLift_uniq
      · rw [cfpLift_fst, ← Category.assoc,
          cfpLift_fst]
      · rw [cfpLift_snd, ← Category.assoc,
          cfpLift_snd]
    -- Step G: Factor out cfpMap natSucc (𝟙 T)
    -- from the first component.
    have h_factor_succ :
        cfpLift
          (cfpLiftAssoc natPlus natPlus ≫
            cfpSnd p.T p.T ≫ natSucc)
          (cfpSnd p.T (cfpProd p.T p.T) ≫
            cfpSnd p.T p.T) =
        cfpLift
          (cfpLiftAssoc natPlus natPlus ≫
            cfpSnd p.T p.T)
          (cfpSnd p.T (cfpProd p.T p.T) ≫
            cfpSnd p.T p.T) ≫
          cfpMap natSucc (𝟙 p.T) := by
      rw [cfpLift_cfpMap]
      congr 1
      · rw [Category.assoc]
      · rw [Category.comp_id]
    -- Step H: cfpLiftAssoc natPlus natPlus ≫
    -- cfpSnd = cfpAssocSnd ≫ natPlus.
    have h_la_natPlus_snd :
        cfpLiftAssoc
          (natPlus : cfpProd p.T p.T ⟶ p.T)
          natPlus ≫
          cfpSnd p.T p.T =
        cfpAssocSnd p.T p.T p.T ≫
          natPlus := by
      unfold cfpLiftAssoc; rw [cfpLift_snd]
    -- Step I: The resulting cfpLift equals
    -- cfpAssocSnd ≫ cfpLift natPlus (cfpSnd T T).
    have h_lift_eq :
        cfpLift
          (cfpAssocSnd p.T p.T p.T ≫ natPlus)
          (cfpSnd p.T (cfpProd p.T p.T) ≫
            cfpSnd p.T p.T) =
        cfpAssocSnd p.T p.T p.T ≫
          cfpLift natPlus
            (cfpSnd p.T p.T) := by
      rw [cfpLift_precomp]
      congr 1
      unfold cfpAssocSnd
      rw [cfpLift_snd]
    -- Assemble the chain using calc.
    calc cfpMap (𝟙 p.T) p.β ≫
          cfpLift natPlus (cfpSnd p.T p.T) ≫
          natTruncSub
      _ = (cfpMap (𝟙 p.T) p.β ≫
            cfpLift natPlus
              (cfpSnd p.T p.T)) ≫
          natTruncSub := by
        rw [Category.assoc]
      _ = (cfpLift
            (cfpLiftAssoc natPlus natPlus ≫
              cfpSnd p.T p.T ≫ natSucc)
            (cfpSnd p.T (cfpProd p.T p.T)) ≫
            cfpMap (𝟙 p.T) p.β) ≫
          natTruncSub := by
        rw [h_factor, h_extract]
      _ = cfpLift
            (cfpLiftAssoc natPlus natPlus ≫
              cfpSnd p.T p.T ≫ natSucc)
            (cfpSnd p.T (cfpProd p.T p.T)) ≫
          cfpMap (𝟙 p.T) p.β ≫
          natTruncSub := by
        rw [Category.assoc]
      _ = cfpLift
            (cfpLiftAssoc natPlus natPlus ≫
              cfpSnd p.T p.T ≫ natSucc)
            (cfpSnd p.T (cfpProd p.T p.T)) ≫
          cfpLiftAssoc natTruncSub
            natTruncSub ≫
          cfpSnd p.T p.T ≫ natPred := by
        rw [h_tsβ]
      _ = (cfpLift
            (cfpLiftAssoc natPlus natPlus ≫
              cfpSnd p.T p.T ≫ natSucc)
            (cfpSnd p.T (cfpProd p.T p.T)) ≫
          cfpAssocSnd p.T p.T p.T) ≫
          natTruncSub ≫ natPred := by
        rw [show cfpLift
              (cfpLiftAssoc natPlus natPlus ≫
                cfpSnd p.T p.T ≫ natSucc)
              (cfpSnd p.T (cfpProd p.T p.T)) ≫
            cfpLiftAssoc natTruncSub
              natTruncSub ≫
            cfpSnd p.T p.T ≫ natPred =
          cfpLift
              (cfpLiftAssoc natPlus natPlus ≫
                cfpSnd p.T p.T ≫ natSucc)
              (cfpSnd p.T (cfpProd p.T p.T)) ≫
            (cfpLiftAssoc natTruncSub
                natTruncSub ≫
              cfpSnd p.T p.T) ≫ natPred
          from by
            simp only [Category.assoc]]
        rw [h_la_snd]
        simp only [Category.assoc]
      _ = cfpLift
            (cfpLiftAssoc natPlus natPlus ≫
              cfpSnd p.T p.T ≫ natSucc)
            (cfpSnd p.T (cfpProd p.T p.T) ≫
              cfpSnd p.T p.T) ≫
          natTruncSub ≫ natPred := by
        rw [h_lift_assocSnd]
      _ = (cfpLift
            (cfpLiftAssoc natPlus natPlus ≫
              cfpSnd p.T p.T)
            (cfpSnd p.T (cfpProd p.T p.T) ≫
              cfpSnd p.T p.T) ≫
          cfpMap natSucc (𝟙 p.T)) ≫
          natTruncSub ≫ natPred := by
        rw [h_factor_succ]
      _ = cfpLift
            (cfpLiftAssoc natPlus natPlus ≫
              cfpSnd p.T p.T)
            (cfpSnd p.T (cfpProd p.T p.T) ≫
              cfpSnd p.T p.T) ≫
          cfpMap natSucc (𝟙 p.T) ≫
          (natTruncSub ≫ natPred) := by
        simp only [Category.assoc]
      _ = cfpLift
            (cfpLiftAssoc natPlus natPlus ≫
              cfpSnd p.T p.T)
            (cfpSnd p.T (cfpProd p.T p.T) ≫
              cfpSnd p.T p.T) ≫
          natTruncSub := by
        rw [natSucc_natTruncSub_natPred]
      _ = cfpLift
            (cfpAssocSnd p.T p.T p.T ≫
              natPlus)
            (cfpSnd p.T (cfpProd p.T p.T) ≫
              cfpSnd p.T p.T) ≫
          natTruncSub := by
        rw [h_la_natPlus_snd]
      _ = (cfpAssocSnd p.T p.T p.T ≫
            cfpLift natPlus
              (cfpSnd p.T p.T)) ≫
          natTruncSub := by
        rw [h_lift_eq]
      _ = cfpAssocSnd p.T p.T p.T ≫
          cfpLift natPlus
            (cfpSnd p.T p.T) ≫
          natTruncSub := by
        rw [Category.assoc]

end GebLean
