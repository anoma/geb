import GebLean.TreeGoedel

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

/-- Step morphism for `triRootState`.  Given the
pair `(s, rem)` representing diagonal index and
offset within the diagonal:
- When `s - rem = 0` (diagonal complete): advance
  to `(s + 1, 0)`.
- When `s - rem > 0` (still within diagonal):
  stay at `(s, rem + 1)`. -/
def triRootStep :
    cfpProd p.T p.T ⟶ cfpProd p.T p.T :=
  cfpLift
    (iteBranches
      (cfpFst p.T p.T ≫ natSucc)
      (cfpFst p.T p.T)
      (natTruncSub ≫ isLeafEndo))
    (iteBranches
      (cfpTerminalFrom (cfpProd p.T p.T) ≫ p.ℓ)
      (cfpSnd p.T p.T ≫ natSucc)
      (natTruncSub ≫ isLeafEndo))

/-- Fold computing the `(diagonal, offset)` pair
by walking through natural numbers in order.
At `ℓ` (zero), the state is `(0, 0)`.
At each successor, applies `triRootStep`. -/
def triRootState : p.T ⟶ cfpProd p.T p.T :=
  cfpLift (cfpTerminalFrom p.T) (𝟙 p.T) ≫
    nnoElim
      (cfpLift
        (cfpTerminalFrom cfpTerminal ≫ p.ℓ)
        (cfpTerminalFrom cfpTerminal ≫ p.ℓ))
      triRootStep

/-- Base case: `triRootState(ℓ) = (ℓ, ℓ)`. -/
theorem triRootState_ℓ :
    p.ℓ ≫ triRootState =
    cfpLift p.ℓ
      (p.ℓ : cfpTerminal (C := C) ⟶ p.T) := by
  unfold triRootState
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
  rw [embed_eq, nnoElim_ℓ]
  congr 1 <;>
  · rw [show cfpTerminalFrom cfpTerminal =
      (𝟙 cfpTerminal : cfpTerminal (C := C) ⟶ _)
      from (h.terminal.uniq _).symm,
      Category.id_comp]

/-- Step case: `triRootState(natSucc(n)) =
triRootStep(triRootState(n))`. -/
theorem triRootState_s :
    natSucc ≫ triRootState =
    triRootState ≫
      (triRootStep :
        cfpProd p.T p.T ⟶
          cfpProd p.T p.T) := by
  unfold triRootState
  rw [← Category.assoc, cfpLift_precomp,
    Category.comp_id]
  have term_eq :
      natSucc ≫ cfpTerminalFrom p.T =
      cfpTerminalFrom p.T :=
    h.terminal.uniq _
  rw [term_eq]
  have factor :
      cfpLift (cfpTerminalFrom p.T) natSucc =
      cfpLift (cfpTerminalFrom p.T) (𝟙 p.T) ≫
        cfpMap (𝟙 cfpTerminal) natSucc := by
    rw [cfpLift_cfpMap, Category.comp_id,
      Category.id_comp]
  rw [factor, Category.assoc, nnoElim_s]
  simp only [← Category.assoc]

/-- Integer triangle root: extracts the diagonal
index from the `triRootState` fold. -/
def triRoot : p.T ⟶ p.T :=
  triRootState ≫ cfpFst p.T p.T

/-- Offset within the diagonal: extracts the
offset component from the `triRootState` fold. -/
def triRootOffset : p.T ⟶ p.T :=
  triRootState ≫ cfpSnd p.T p.T

/-- Base case: `triRoot(ℓ) = ℓ`. -/
theorem triRoot_ℓ :
    p.ℓ ≫ triRoot =
    (p.ℓ : cfpTerminal (C := C) ⟶ p.T) := by
  unfold triRoot
  rw [← Category.assoc, triRootState_ℓ,
    cfpLift_fst]

/-- Base case: `triRootOffset(ℓ) = ℓ`. -/
theorem triRootOffset_ℓ :
    p.ℓ ≫ triRootOffset =
    (p.ℓ : cfpTerminal (C := C) ⟶ p.T) := by
  unfold triRootOffset
  rw [← Category.assoc, triRootState_ℓ,
    cfpLift_snd]

/-- When `s = rem`, the truncated subtraction
gives `ℓ` (leaf), so `triRootStep` advances to
the next diagonal:
`triRootStep(s, s) = (s + 1, ℓ)`. -/
private theorem natTruncSub_diag {D : C}
    (s : D ⟶ p.T) :
    cfpLift s s ≫ natTruncSub =
    cfpTerminalFrom D ≫ p.ℓ := by
  have factor :
      cfpLift s s ≫ natTruncSub =
      s ≫ (cfpLift (𝟙 p.T) (𝟙 p.T) ≫
        natTruncSub) := by
    rw [← Category.assoc]
    congr 1
    rw [cfpLift_precomp]
    simp only [Category.comp_id]
  rw [factor, natTruncSub_self, ← Category.assoc]
  congr 1
  exact h.terminal.uniq _

theorem triRootStep_diag {D : C}
    (s : D ⟶ p.T) :
    cfpLift s s ≫ triRootStep =
    cfpLift (s ≫ natSucc)
      (cfpTerminalFrom D ≫ p.ℓ) := by
  have cond_eq :
      cfpLift s s ≫ natTruncSub ≫ isLeafEndo =
      cfpTerminalFrom D ≫ p.ℓ := by
    rw [← Category.assoc, natTruncSub_diag,
      Category.assoc, isLeafEndo_ℓ]
  unfold triRootStep
  apply cfpLift_uniq
  · -- First component: show fst = s ≫ natSucc
    simp only [Category.assoc]
    rw [cfpLift_fst,
      iteBranches_precomp,
      ← Category.assoc, cfpLift_fst,
      cond_eq, iteBranches_ℓ]
  · -- Second component: show snd = term ≫ ℓ
    simp only [Category.assoc]
    rw [cfpLift_snd,
      iteBranches_precomp]
    -- Simplify the thn argument
    have thn_eq :
        cfpLift s s ≫
          cfpTerminalFrom
            (cfpProd p.T p.T) ≫ p.ℓ =
        cfpTerminalFrom D ≫ p.ℓ := by
      rw [← Category.assoc]
      congr 1
      exact h.terminal.uniq _
    -- Simplify the els argument
    have els_eq :
        cfpLift s s ≫
          cfpSnd p.T p.T ≫ natSucc =
        s ≫ natSucc := by
      rw [← Category.assoc, cfpLift_snd]
    rw [thn_eq, els_eq, cond_eq,
      iteBranches_ℓ]

/-- When `s > rem` (the truncated subtraction
factors through `β`), `triRootStep` stays on
the same diagonal and increments the offset:
`triRootStep(s, rem) = (s, rem + 1)`. -/
theorem triRootStep_within {D : C}
    (s rem : D ⟶ p.T)
    (r : D ⟶ cfpProd p.T p.T)
    (hr : cfpLift s rem ≫ natTruncSub =
      r ≫ p.β) :
    cfpLift s rem ≫ triRootStep =
    cfpLift s (rem ≫ natSucc) := by
  have cond_eq :
      cfpLift s rem ≫
        natTruncSub ≫ isLeafEndo =
      cfpTerminalFrom D ≫ treeFalse := by
    rw [← Category.assoc, hr,
      Category.assoc, isLeafEndo_β]
    rw [← Category.assoc]
    congr 1
    exact h.terminal.uniq _
  set r' := cfpTerminalFrom D ≫
    cfpLift p.ℓ p.ℓ with hr'_def
  have cond_β :
      cfpLift s rem ≫
        natTruncSub ≫ isLeafEndo =
      r' ≫ p.β := by
    rw [← Category.assoc, hr,
      Category.assoc, isLeafEndo_β,
      ← Category.assoc]
    have rterm :
        r ≫ cfpTerminalFrom
          (cfpProd p.T p.T) =
        cfpTerminalFrom D :=
      h.terminal.uniq _
    rw [rterm]
    unfold treeFalse
    rw [Category.assoc]
  unfold triRootStep
  apply cfpLift_uniq
  · -- First component
    simp only [Category.assoc]
    rw [cfpLift_fst,
      iteBranches_precomp]
    have fst_eq :
        cfpLift s rem ≫ cfpFst p.T p.T = s :=
      cfpLift_fst _ _
    rw [show cfpLift s rem ≫
        cfpFst p.T p.T ≫ natSucc =
      s ≫ natSucc from by
        rw [← Category.assoc, fst_eq],
      fst_eq, cond_β]
    exact iteBranches_β _ _ _
  · -- Second component
    simp only [Category.assoc]
    rw [cfpLift_snd,
      iteBranches_precomp]
    have thn_eq :
        cfpLift s rem ≫
          cfpTerminalFrom
            (cfpProd p.T p.T) ≫ p.ℓ =
        cfpTerminalFrom D ≫ p.ℓ := by
      rw [← Category.assoc]
      congr 1
      exact h.terminal.uniq _
    have els_eq :
        cfpLift s rem ≫
          cfpSnd p.T p.T ≫ natSucc =
        rem ≫ natSucc := by
      rw [← Category.assoc, cfpLift_snd]
    rw [thn_eq, els_eq, cond_β]
    exact iteBranches_β _ _ _

/-- Cancellation: `natTruncSub(natPlus(x, a), a) =
x`, at a general domain. -/
private theorem natTruncSub_natPlus_cancel'
    {D : C} (x a : D ⟶ p.T) :
    cfpLift (cfpLift x a ≫ natPlus) a ≫
      natTruncSub = x := by
  have factor :
      cfpLift (cfpLift x a ≫ natPlus) a =
      cfpLift x a ≫
        cfpLift natPlus
          (cfpSnd p.T p.T) := by
    symm
    apply cfpLift_uniq
    · rw [Category.assoc, cfpLift_fst]
    · rw [Category.assoc, cfpLift_snd,
        cfpLift_snd]
  rw [factor, Category.assoc,
    natTruncSub_natPlus_cancel,
    cfpLift_fst]

/-- When the first component is
`natPlus(succ(b), a)` and the second is `a`,
the offset `a` is below the diagonal index,
so `triRootStep` stays within the diagonal and
increments the offset. -/
theorem triRootStep_natPlus_succ {D : C}
    (a b : D ⟶ p.T) :
    cfpLift
      (cfpLift (b ≫ natSucc) a ≫ natPlus)
      a ≫ triRootStep =
    cfpLift
      (cfpLift (b ≫ natSucc) a ≫ natPlus)
      (a ≫ natSucc) := by
  apply triRootStep_within _ _
    (b ≫ cfpLift
      (cfpTerminalFrom p.T ≫ p.ℓ) (𝟙 p.T))
  rw [natTruncSub_natPlus_cancel']
  unfold natSucc
  simp only [Category.assoc]

/-- `triRootState` absorbs `toRSpineNat`. -/
theorem triRootState_toRSpineNat :
    toRSpineNat ≫ triRootState =
    (triRootState : p.T ⟶ cfpProd p.T p.T) :=
  by
  unfold triRootState
  -- LHS: toRSN ≫ embed ≫ nnoElim(base, step).
  -- embed = cfpLift(term, 𝟙).
  -- toRSN ≫ embed = cfpLift(term, toRSN).
  -- RHS: embed ≫ nnoElim(base, step).
  -- nnoElim = cfpMap(𝟙, toRSN) ≫ elim(...).
  -- embed ≫ cfpMap(𝟙, toRSN)
  --   = cfpLift(term, toRSN).
  -- So both sides = cfpLift(term, toRSN) ≫
  --   elim(...).
  have lhs_embed :
      toRSpineNat ≫
        cfpLift (cfpTerminalFrom p.T)
          (𝟙 p.T) =
      cfpLift (cfpTerminalFrom p.T)
        toRSpineNat := by
    rw [cfpLift_precomp, Category.comp_id]
    congr 1
    exact h.terminal.uniq _
  have rhs_embed :
      cfpLift (cfpTerminalFrom p.T)
        (𝟙 p.T) ≫
        cfpMap (𝟙 cfpTerminal) toRSpineNat =
      cfpLift (cfpTerminalFrom p.T)
        toRSpineNat := by
    rw [cfpLift_cfpMap, Category.comp_id,
      Category.id_comp]
  have rsn_idem :
      cfpLift (cfpTerminalFrom p.T)
        toRSpineNat ≫
        cfpMap (𝟙 cfpTerminal) toRSpineNat =
      cfpLift (cfpTerminalFrom p.T)
        toRSpineNat := by
    rw [cfpLift_cfpMap,
      show cfpTerminalFrom p.T ≫
        (𝟙 cfpTerminal :
          cfpTerminal (C := C) ⟶ cfpTerminal) =
        cfpTerminalFrom p.T from
        Category.comp_id _,
      toRSpineNat_idem]
  unfold nnoElim
  simp only [← Category.assoc]
  rw [lhs_embed, rsn_idem, rhs_embed]

/-- `triRoot` absorbs `toRSpineNat`:
`toRSpineNat ≫ triRoot = triRoot`. -/
theorem triRoot_toRSpineNat :
    toRSpineNat ≫ triRoot =
    (triRoot : p.T ⟶ p.T) := by
  unfold triRoot
  rw [← Category.assoc,
    triRootState_toRSpineNat]

/-- `triRootOffset` absorbs `toRSpineNat`:
`toRSpineNat ≫ triRootOffset = triRootOffset`.
-/
theorem triRootOffset_toRSpineNat :
    toRSpineNat ≫ triRootOffset =
    (triRootOffset : p.T ⟶ p.T) := by
  unfold triRootOffset
  rw [← Category.assoc,
    triRootState_toRSpineNat]

/-- Adding `k` to a number and computing
`triRootState` equals iterating `triRootStep` `k`
times on the `triRootState` of the original:
`natPlus ≫ triRootState =
  nnoElim triRootState triRootStep`. -/
theorem natPlus_triRootState :
    natPlus ≫ triRootState =
    nnoElim (triRootState : p.T ⟶ cfpProd p.T p.T)
      triRootStep := by
  apply nnoElim_uniq
    (triRootState : p.T ⟶ cfpProd p.T p.T)
    triRootStep
    (natPlus ≫ triRootState)
  · -- Base: cfpInsertSnd ℓ T ≫ natPlus ≫
    -- triRootState = triRootState
    rw [← Category.assoc, natPlus_ℓ,
      Category.id_comp]
  · -- Step: cfpMap (𝟙) natSucc ≫ natPlus ≫
    -- triRootState = natPlus ≫ triRootState ≫
    -- triRootStep
    have succ_natPlus :
        cfpMap (𝟙 p.T) natSucc ≫ natPlus =
        natPlus ≫ (natSucc : p.T ⟶ p.T) := by
      have eq1 :
          cfpMap (𝟙 p.T)
            (natSucc : p.T ⟶ p.T) =
          cfpLift (cfpFst p.T p.T)
            (cfpSnd p.T p.T ≫ natSucc) := by
        unfold cfpMap
        congr 1
        rw [Category.comp_id]
      rw [eq1,
        natPlus_succ (cfpFst p.T p.T)
          (cfpSnd p.T p.T)]
      have eta :
          cfpLift (cfpFst p.T p.T)
            (cfpSnd p.T p.T) =
          𝟙 (cfpProd p.T p.T) :=
        (cfpLift_uniq
          (cfpFst p.T p.T) (cfpSnd p.T p.T)
          (𝟙 (cfpProd p.T p.T))
          (Category.id_comp _)
          (Category.id_comp _)).symm
      rw [eta, Category.id_comp]
    rw [← Category.assoc, succ_natPlus]
    simp only [Category.assoc]
    rw [triRootState_s]
  · -- Norm: cfpMap (𝟙) toRSN ≫ natPlus ≫
    -- triRootState = natPlus ≫ triRootState
    rw [← Category.assoc,
      natPlus_toRSpineNat_second]

/-- `natTri(succ(n)) = succ(cantorPair(n, 0))`:
the successor triangular number is one past the
last point of diagonal n (which is
`cantorPair(n, 0)`). -/
private theorem natTri_succ_eq_succ_cantorPairAt0 :
    natSucc ≫ natTri =
    (cfpLift (𝟙 p.T)
      (cfpTerminalFrom p.T ≫ p.ℓ) ≫
      cantorPair) ≫
    (natSucc : p.T ⟶ p.T) := by
  -- RHS: cantorPair(n, 0) ≫ natSucc.
  -- cantorPair(n, 0) = natPlus(natTri(n), n).
  -- So RHS = succ(natPlus(natTri(n), n)).
  -- LHS: natTri(succ(n))
  --   = natPlus(succ(toRSN(n)), natTri(n))
  --   = succ(natPlus(toRSN(n), natTri(n)))
  --   = succ(natPlus(natTri(n), toRSN(n)))
  --   = succ(natPlus(natTri(n), n))
  -- by commutativity and absorption.
  -- First, simplify the RHS.
  -- Simplify cantorPair(n, 0).
  -- cfpLift (𝟙 T) (term ≫ ℓ) ≫ cantorPair
  -- = cfpLift (𝟙 T) (term ≫ ℓ) ≫
  --   cfpLift (natPlus ≫ natTri) cfpFst ≫ natPlus
  -- = cfpLift (natPlus(n, 0) ≫ natTri) (𝟙) ≫
  --   natPlus
  -- = cfpLift natTri (𝟙) ≫ natPlus.
  have cantorPairAt0 :
      cfpLift (𝟙 p.T)
        (cfpTerminalFrom p.T ≫ p.ℓ) ≫
        cantorPair =
      cfpLift natTri (𝟙 p.T) ≫
        natPlus := by
    unfold cantorPair
    rw [← Category.assoc, cfpLift_precomp]
    have fst_eq :
        cfpLift (𝟙 p.T)
          (cfpTerminalFrom p.T ≫ p.ℓ) ≫
          natPlus ≫ natTri =
        (natTri : p.T ⟶ p.T) := by
      rw [← Category.assoc,
        natPlus_zero (𝟙 p.T),
        Category.id_comp]
    have snd_eq :
        cfpLift (𝟙 p.T)
          (cfpTerminalFrom p.T ≫ p.ℓ) ≫
          cfpFst p.T p.T =
        (𝟙 p.T : p.T ⟶ p.T) := by
      rw [cfpLift_fst]
    rw [fst_eq, snd_eq]
  rw [cantorPairAt0]
  -- RHS = cfpLift natTri (𝟙 T) ≫ natPlus ≫
  --   natSucc
  -- LHS = natSucc ≫ natTri.
  rw [natTri_natSucc]
  -- LHS has embed ≫ natTriHelper ≫ cfpFst ≫
  -- natSucc; simplify using toRSpineNat.
  have embed_fst :
      cfpLift (cfpTerminalFrom p.T) (𝟙 p.T) ≫
        natTriHelper ≫ cfpFst p.T p.T =
      (toRSpineNat : p.T ⟶ p.T) :=
    embed_natTriHelper_cfpFst
  rw [show cfpLift (cfpTerminalFrom p.T)
      (𝟙 p.T) ≫ natTriHelper ≫
      cfpFst p.T p.T ≫ natSucc =
    (cfpLift (cfpTerminalFrom p.T) (𝟙 p.T) ≫
      natTriHelper ≫ cfpFst p.T p.T) ≫
    natSucc from by
      simp only [Category.assoc],
    embed_fst]
  rw [natPlus_succ_left toRSpineNat natTri]
  -- Both sides = ... ≫ natSucc.
  congr 1
  -- cfpLift toRSN natTri ≫ natPlus =
  -- cfpLift natTri (𝟙 T) ≫ natPlus
  -- by commutativity (both args rsn) and
  -- absorption.
  rw [(natPlus_comm_rsn toRSpineNat natTri
    toRSpineNat_idem
    natTri_isRSpineNatNorm).symm]
  -- cfpLift natTri toRSN ≫ natPlus =
  -- cfpLift natTri (𝟙 T) ≫ natPlus
  have : cfpLift natTri
      (toRSpineNat : p.T ⟶ p.T) =
    cfpLift natTri (𝟙 p.T) ≫
      cfpMap (𝟙 p.T) toRSpineNat := by
    rw [cfpLift_cfpMap, Category.comp_id,
      Category.id_comp]
  rw [this, Category.assoc,
    natPlus_toRSpineNat_second]

/-- `natTri(ℓ) ≫ triRoot = ℓ`:
the triangle root of `T(0) = 0` is `0`. -/
theorem natTri_ℓ_triRoot :
    p.ℓ ≫ natTri ≫ triRoot =
    (p.ℓ : cfpTerminal (C := C) ⟶ p.T) := by
  rw [← Category.assoc, natTri_ℓ, triRoot_ℓ]

/-- `natTri(ℓ) ≫ triRootOffset = ℓ`:
the offset of `T(0) = 0` is `0`. -/
theorem natTri_ℓ_triRootOffset :
    p.ℓ ≫ natTri ≫ triRootOffset =
    (p.ℓ : cfpTerminal (C := C) ⟶ p.T) := by
  rw [← Category.assoc, natTri_ℓ,
    triRootOffset_ℓ]

/-- The offset-incrementing step morphism:
`(s, r) ↦ (s, natSucc(r))`. Unlike `triRootStep`,
this step always increments the second component
without checking the diagonal boundary. -/
def simpleTriRootStep :
    cfpProd p.T p.T ⟶ cfpProd p.T p.T :=
  cfpLift (cfpFst p.T p.T)
    (cfpSnd p.T p.T ≫ natSucc)

/-- Walking with `simpleTriRootStep` from `(s, ℓ)`
for `k` steps gives `(s, toRSN(k))`.  This is the
"simple diagonal walk" that unconditionally
increments the offset. -/
def simpleDiagWalk :
    cfpProd p.T p.T ⟶ cfpProd p.T p.T :=
  nnoElim
    (cfpLift (𝟙 p.T) (cfpTerminalFrom p.T ≫ p.ℓ))
    simpleTriRootStep

/-- Base case: `simpleDiagWalk(s, ℓ) = (s, ℓ)`. -/
theorem simpleDiagWalk_ℓ :
    cfpInsertSnd p.ℓ p.T ≫ simpleDiagWalk =
    cfpLift (𝟙 p.T)
      (cfpTerminalFrom p.T ≫ p.ℓ) := by
  unfold simpleDiagWalk
  rw [nnoElim_ℓ]

/-- Step case: `simpleDiagWalk(s, natSucc(k)) =
simpleTriRootStep(simpleDiagWalk(s, k))`. -/
theorem simpleDiagWalk_s :
    cfpMap (𝟙 p.T) natSucc ≫ simpleDiagWalk =
    simpleDiagWalk ≫
      (simpleTriRootStep :
        cfpProd p.T p.T ⟶
          cfpProd p.T p.T) := by
  unfold simpleDiagWalk
  rw [nnoElim_s]

/-- `simpleDiagWalk(s, k) = (s, toRSN(k))`:
the simple walk preserves the first component
and normalizes the second. -/
theorem simpleDiagWalk_eq :
    simpleDiagWalk =
    cfpLift (cfpFst p.T p.T)
      (cfpSnd p.T p.T ≫ toRSpineNat) := by
  symm
  unfold simpleDiagWalk
  apply nnoElim_uniq
  · -- Base: cfpInsertSnd ℓ T ≫ cfpLift fst
    -- (snd ≫ toRSN) = cfpLift (𝟙) (term ≫ ℓ)
    unfold cfpInsertSnd
    rw [cfpLift_precomp, cfpLift_fst]
    congr 1
    rw [show cfpLift (𝟙 p.T)
        (cfpTerminalFrom p.T ≫ p.ℓ) ≫
        cfpSnd p.T p.T ≫ toRSpineNat =
      (cfpLift (𝟙 p.T)
          (cfpTerminalFrom p.T ≫ p.ℓ) ≫
        cfpSnd p.T p.T) ≫ toRSpineNat from
        by simp only [Category.assoc],
      cfpLift_snd]
    simp only [Category.assoc]
    rw [toRSpineNat_ℓ]
  · -- Step: both sides equal
    --   cfpLift fst (snd ≫ toRSN ≫ natSucc)
    have h_lhs :
        cfpMap (𝟙 p.T) natSucc ≫
          cfpLift (cfpFst p.T p.T)
            (cfpSnd p.T p.T ≫ toRSpineNat) =
        cfpLift (cfpFst p.T p.T)
          (cfpSnd p.T p.T ≫ toRSpineNat ≫
            natSucc) := by
      rw [cfpLift_precomp,
        cfpMap_fst, Category.comp_id]
      congr 1
      rw [show cfpMap (𝟙 p.T)
          (natSucc : p.T ⟶ p.T) ≫
        cfpSnd p.T p.T ≫ toRSpineNat =
        (cfpMap (𝟙 p.T) natSucc ≫
          cfpSnd p.T p.T) ≫ toRSpineNat from
          by simp only [Category.assoc],
        cfpMap_snd, Category.assoc,
        natSucc_toRSpineNat_comm]
    have h_rhs :
        cfpLift (cfpFst p.T p.T)
          (cfpSnd p.T p.T ≫ toRSpineNat) ≫
        simpleTriRootStep =
        cfpLift (cfpFst p.T p.T)
          (cfpSnd p.T p.T ≫ toRSpineNat ≫
            natSucc) := by
      unfold simpleTriRootStep
      rw [cfpLift_precomp, cfpLift_fst]
      congr 1
      simp only [← Category.assoc]
      rw [cfpLift_snd]
    rw [h_lhs, h_rhs]
  · -- Norm
    rw [cfpLift_precomp]
    have hf :
        cfpMap (𝟙 p.T) toRSpineNat ≫
          cfpFst p.T p.T =
        cfpFst p.T p.T := by
      rw [cfpMap_fst, Category.comp_id]
    have hg :
        cfpMap (𝟙 p.T) toRSpineNat ≫
          (cfpSnd p.T p.T ≫ toRSpineNat) =
        cfpSnd p.T p.T ≫ toRSpineNat := by
      rw [← Category.assoc, cfpMap_snd,
        Category.assoc, toRSpineNat_idem]
    rw [hf, hg]

/-- `natEq(ℓ, z) = isLeafEndo(z)`. -/
theorem natEq_ℓ_left :
    cfpLift (cfpTerminalFrom p.T ≫ p.ℓ)
      (𝟙 p.T) ≫ natEq =
    (isLeafEndo : p.T ⟶ p.T) := by
  unfold natEq
  rw [← Category.assoc, ← Category.assoc,
    cfpLift_precomp]
  have h1 :
      cfpLift (cfpTerminalFrom p.T ≫ p.ℓ)
        (𝟙 p.T) ≫ natTruncSub =
      cfpTerminalFrom p.T ≫ p.ℓ :=
    natTruncSub_ℓ_left (𝟙 p.T)
  have hswap :
      cfpLift (cfpTerminalFrom p.T ≫ p.ℓ)
        (𝟙 p.T) ≫ cfpSwap p.T p.T =
      cfpLift (𝟙 p.T)
        (cfpTerminalFrom p.T ≫ p.ℓ) := by
    unfold cfpSwap
    rw [cfpLift_precomp, cfpLift_fst,
      cfpLift_snd]
  have h2 :
      cfpLift (cfpTerminalFrom p.T ≫ p.ℓ)
        (𝟙 p.T) ≫ cfpSwap p.T p.T ≫
        natTruncSub =
      𝟙 p.T := by
    rw [← Category.assoc, hswap]
    exact natTruncSub_ℓ
  rw [h1, h2,
    natPlus_ℓ_left_eq_toRSpineNat,
    toRSpineNat_isLeafEndo]

/-- `natPlus ≫ isLeafEndo = boolAnd`:
applying `isLeafEndo` to a sum yields the
conjunction of `isLeafEndo` on the summands. -/
private theorem natPlus_isLeafEndo_eq_boolAnd :
    natPlus ≫ isLeafEndo =
    (boolAnd : cfpProd p.T p.T ⟶ p.T) := by
  rw [boolAnd_eq_elim]
  have base :
      cfpInsertSnd p.ℓ p.T ≫
        (natPlus ≫ isLeafEndo) =
      isLeafEndo := by
    rw [← Category.assoc, natPlus_ℓ,
      Category.id_comp]
  have step :
      cfpMap (𝟙 p.T) p.β ≫
        (natPlus ≫ isLeafEndo) =
      cfpLiftAssoc (natPlus ≫ isLeafEndo)
        (natPlus ≫ isLeafEndo) ≫
        (cfpTerminalFrom (cfpProd p.T p.T) ≫
          treeFalse) := by
    rw [← Category.assoc, natPlus_β,
      Category.assoc, Category.assoc,
      natSucc_isLeafEndo]
    have lhs :
        cfpLiftAssoc natPlus natPlus ≫
          cfpSnd p.T p.T ≫
          cfpTerminalFrom p.T ≫
          treeFalse =
        cfpTerminalFrom _ ≫ treeFalse := by
      rw [← Category.assoc
        (cfpLiftAssoc natPlus natPlus),
        ← Category.assoc
          (cfpLiftAssoc natPlus natPlus ≫
            cfpSnd p.T p.T)]
      congr 1; exact h.terminal.uniq _
    have rhs :
        cfpLiftAssoc
          (natPlus ≫ isLeafEndo)
          (natPlus ≫ isLeafEndo) ≫
          cfpTerminalFrom
            (cfpProd p.T p.T) ≫
          treeFalse =
        cfpTerminalFrom _ ≫ treeFalse := by
      rw [← Category.assoc]
      congr 1; exact h.terminal.uniq _
    rw [lhs, rhs]
  exact p.elim_uniq isLeafEndo
    (cfpTerminalFrom (cfpProd p.T p.T) ≫
      treeFalse)
    (natPlus ≫ isLeafEndo)
    base step

/-- `natEq` decomposes as `boolAnd` of the two
truncated subtractions:
`natEq(x, y) = boolAnd(x - y, y - x)`. -/
private theorem natEq_eq_boolAnd_natTruncSub :
    (natEq : cfpProd p.T p.T ⟶ p.T) =
    cfpLift natTruncSub
      (cfpSwap p.T p.T ≫ natTruncSub) ≫
      boolAnd := by
  have h_unfold : natEq =
      cfpLift natTruncSub
        (cfpSwap p.T p.T ≫ natTruncSub) ≫
        natPlus ≫
        (isLeafEndo : p.T ⟶ p.T) := rfl
  rw [h_unfold, ← natPlus_isLeafEndo_eq_boolAnd]

/-- Symmetry of `natEq`:
`natEq(y, x) = natEq(x, y)`. -/
theorem natEq_symm :
    cfpSwap p.T p.T ≫ natEq =
    (natEq : cfpProd p.T p.T ⟶ p.T) := by
  rw [natEq_eq_boolAnd_natTruncSub,
    ← Category.assoc, cfpLift_precomp]
  have swap_fst :
      cfpSwap p.T p.T ≫ cfpFst p.T p.T =
      cfpSnd p.T p.T := by
    unfold cfpSwap; exact cfpLift_fst _ _
  have swap_snd :
      cfpSwap p.T p.T ≫ cfpSnd p.T p.T =
      cfpFst p.T p.T := by
    unfold cfpSwap; exact cfpLift_snd _ _
  have cfpSwap_invol :
      cfpSwap p.T p.T ≫
        cfpSwap p.T p.T =
      𝟙 (cfpProd p.T p.T) := by
    rw [show 𝟙 (cfpProd p.T p.T) =
        cfpLift (cfpFst p.T p.T)
          (cfpSnd p.T p.T) from
      cfpLift_uniq _ _ _
        (Category.id_comp _)
        (Category.id_comp _)]
    apply cfpLift_uniq
    · rw [Category.assoc, swap_fst, swap_snd]
    · rw [Category.assoc, swap_snd, swap_fst]
  have h_swap_swap :
      cfpSwap p.T p.T ≫
        cfpSwap p.T p.T ≫ natTruncSub =
      natTruncSub := by
    rw [← Category.assoc, cfpSwap_invol,
      Category.id_comp]
  rw [h_swap_swap]
  -- Goal should be:
  -- cfpLift (swap ≫ nts) nts ≫ boolAnd
  -- = cfpLift nts (swap ≫ nts) ≫ boolAnd
  exact boolAnd_comm
    (cfpSwap p.T p.T ≫ natTruncSub)
    natTruncSub

/-- `boolAnd(boolAnd(x, z), natEq(x, z))
  = boolAnd(x, z)`:
conjunction implies equality. -/
private theorem boolAnd_implies_natEq :
    cfpLift boolAnd natEq ≫ boolAnd =
    (boolAnd : cfpProd p.T p.T ⟶ p.T) := by
  conv_rhs => rw [boolAnd_eq_elim]
  apply p.elim_uniq isLeafEndo
    (cfpTerminalFrom (cfpProd p.T p.T) ≫
      treeFalse)
  · -- Base: cfpInsertSnd ℓ T ≫ LHS = isLeafEndo.
    rw [← Category.assoc]
    have base_lift :
        cfpInsertSnd p.ℓ p.T ≫
          cfpLift boolAnd natEq =
        cfpLift isLeafEndo isLeafEndo := by
      rw [cfpLift_precomp]
      congr 1
      · exact boolAnd_ℓ_right
      · exact natEq_ℓ_right
    rw [base_lift]
    have diag :
        cfpLift (isLeafEndo : p.T ⟶ p.T)
          isLeafEndo =
        isLeafEndo ≫
          cfpLift (𝟙 p.T) (𝟙 p.T) := by
      rw [cfpLift_precomp]
      simp only [Category.comp_id]
    rw [diag, Category.assoc, boolAnd_idem,
      isLeafEndo_idem]
  · -- Step: cfpMap (𝟙 T) β ≫ LHS
    --   = cfpLiftAssoc LHS LHS ≫ term ≫ treeFalse.
    rw [← Category.assoc]
    have step_lift :
        cfpMap (𝟙 p.T) p.β ≫
          cfpLift boolAnd natEq =
        cfpLift
          (cfpTerminalFrom
            (cfpProd p.T (cfpProd p.T p.T)) ≫
            treeFalse)
          (cfpMap (𝟙 p.T) p.β ≫ natEq) := by
      rw [cfpLift_precomp]
      congr 1
      exact boolAnd_β_right
    rw [step_lift, boolAnd_treeFalse_left]
    -- RHS: cfpLiftAssoc ... ≫ term ≫ treeFalse
    --   = term ≫ treeFalse.
    rw [← Category.assoc]
    congr 1
    exact (h.terminal.uniq _).symm

/-- The NNO step rule for `natTruncSub` on
its second argument:
`natTruncSub(x, natSucc(y))
  = natPred(natTruncSub(x, y))`. -/
private theorem natTruncSub_natSucc_second :
    cfpMap (𝟙 p.T) natSucc ≫ natTruncSub =
    natTruncSub ≫ (natPred : p.T ⟶ p.T) := by
  have factor_succ :
      cfpMap (𝟙 p.T) natSucc =
      cfpMap (𝟙 p.T)
        (cfpLift (cfpTerminalFrom p.T ≫ p.ℓ)
          (𝟙 p.T)) ≫
        cfpMap (𝟙 p.T) p.β := by
    rw [← cfpMap_id_comp']
    rfl
  rw [factor_succ, Category.assoc,
    natTruncSub_β]
  have la_snd :
      cfpLiftAssoc natTruncSub natTruncSub ≫
        cfpSnd p.T p.T =
      cfpAssocSnd p.T p.T p.T ≫
        natTruncSub := by
    unfold cfpLiftAssoc; rw [cfpLift_snd]
  rw [← Category.assoc
    (cfpLiftAssoc natTruncSub natTruncSub),
    la_snd, Category.assoc]
  have cancel :
      cfpMap (𝟙 p.T)
        (cfpLift (cfpTerminalFrom p.T ≫ p.ℓ)
          (𝟙 p.T)) ≫
        cfpAssocSnd p.T p.T p.T =
      𝟙 (cfpProd p.T p.T) := by
    rw [← cfpMap_id p.T p.T]
    unfold cfpAssocSnd
    apply cfpLift_uniq
    · rw [Category.assoc, cfpLift_fst,
        cfpMap_fst, Category.comp_id]
    · rw [Category.assoc, cfpLift_snd,
        ← Category.assoc, cfpMap_snd,
        Category.assoc, cfpLift_snd]
  rw [← Category.assoc, cancel,
    Category.id_comp]

/-- Associativity of truncated subtraction with
addition:
`natTruncSub(natTruncSub(x, y), z)
  = natTruncSub(x, natPlus(y, z))`. -/
private theorem natTruncSub_assoc :
    cfpLift
      (cfpFst (cfpProd p.T p.T) p.T ≫
        natTruncSub)
      (cfpSnd (cfpProd p.T p.T) p.T) ≫
      natTruncSub =
    cfpLift
      (cfpFst (cfpProd p.T p.T) p.T ≫
        cfpFst p.T p.T)
      (cfpLift
        (cfpFst (cfpProd p.T p.T) p.T ≫
          cfpSnd p.T p.T)
        (cfpSnd (cfpProd p.T p.T) p.T) ≫
        natPlus) ≫
      (natTruncSub :
        cfpProd p.T p.T ⟶ p.T) := by
  set A := cfpProd p.T p.T
  set ψ_L : cfpProd A p.T ⟶ p.T :=
    cfpLift (cfpFst A p.T ≫ natTruncSub)
      (cfpSnd A p.T) ≫ natTruncSub
  set ψ_R : cfpProd A p.T ⟶ p.T :=
    cfpLift (cfpFst A p.T ≫ cfpFst p.T p.T)
      (cfpLift (cfpFst A p.T ≫ cfpSnd p.T p.T)
        (cfpSnd A p.T) ≫ natPlus) ≫
      natTruncSub
  change ψ_L = ψ_R
  -- Show ψ_L = ψ_R by nnoElim_uniq.
  have ψ_L_eq : ψ_L = nnoElim natTruncSub
      natPred := by
    apply nnoElim_uniq natTruncSub natPred ψ_L
    · -- Base
      simp only [ψ_L, ← Category.assoc]
      rw [cfpLift_precomp]
      have hfst :
          cfpInsertSnd p.ℓ A ≫ cfpFst A p.T ≫
            natTruncSub =
          natTruncSub := by
        rw [← Category.assoc]
        unfold cfpInsertSnd
        rw [cfpLift_fst, Category.id_comp]
      have hsnd :
          cfpInsertSnd p.ℓ A ≫
            cfpSnd A p.T =
          cfpTerminalFrom A ≫ p.ℓ := by
        unfold cfpInsertSnd; rw [cfpLift_snd]
      rw [hfst, hsnd]
      have factor :
          cfpLift natTruncSub
            (cfpTerminalFrom A ≫ p.ℓ) =
          natTruncSub ≫
            cfpInsertSnd p.ℓ p.T := by
        unfold cfpInsertSnd
        rw [cfpLift_precomp, Category.comp_id]
        congr 1
        rw [← Category.assoc]; congr 1
        exact (h.terminal.uniq _).symm
      rw [factor, Category.assoc,
        natTruncSub_ℓ, Category.comp_id]
    · -- Step
      simp only [ψ_L, ← Category.assoc]
      rw [cfpLift_precomp]
      rw [show cfpMap (𝟙 A) natSucc ≫
          cfpFst A p.T ≫ natTruncSub =
        cfpFst A p.T ≫ natTruncSub from by
          rw [← Category.assoc, cfpMap_fst,
            Category.comp_id],
        show cfpMap (𝟙 A) natSucc ≫
          cfpSnd A p.T =
        cfpSnd A p.T ≫ natSucc from
          cfpMap_snd _ _]
      rw [show cfpLift
          (cfpFst A p.T ≫ natTruncSub)
          (cfpSnd A p.T ≫ natSucc) =
        cfpLift (cfpFst A p.T ≫ natTruncSub)
          (cfpSnd A p.T) ≫
          cfpMap (𝟙 p.T) natSucc from by
          rw [cfpLift_cfpMap,
            Category.comp_id],
        Category.assoc,
        natTruncSub_natSucc_second]
      simp only [Category.assoc]
    · -- Norm
      simp only [ψ_L, ← Category.assoc]
      rw [cfpLift_precomp]
      rw [show cfpMap (𝟙 A) toRSpineNat ≫
          cfpFst A p.T ≫ natTruncSub =
        cfpFst A p.T ≫ natTruncSub from by
          rw [← Category.assoc, cfpMap_fst,
            Category.comp_id],
        show cfpMap (𝟙 A) toRSpineNat ≫
          cfpSnd A p.T =
        cfpSnd A p.T ≫ toRSpineNat from
          cfpMap_snd _ _]
      rw [show cfpLift
          (cfpFst A p.T ≫ natTruncSub)
          (cfpSnd A p.T ≫ toRSpineNat) =
        cfpLift (cfpFst A p.T ≫ natTruncSub)
          (cfpSnd A p.T) ≫
          cfpMap (𝟙 p.T) toRSpineNat from by
          rw [cfpLift_cfpMap,
            Category.comp_id],
        Category.assoc,
        natTruncSub_toRSpineNat_second]
  have ψ_R_eq : ψ_R = nnoElim natTruncSub
      natPred := by
    apply nnoElim_uniq natTruncSub natPred ψ_R
    · -- Base
      simp only [ψ_R, ← Category.assoc]
      rw [cfpLift_precomp]
      rw [show cfpInsertSnd p.ℓ A ≫
          cfpFst A p.T ≫ cfpFst p.T p.T =
        cfpFst p.T p.T from by
          rw [← Category.assoc]
          unfold cfpInsertSnd
          rw [cfpLift_fst, Category.id_comp]]
      -- Simplify the natPlus argument.
      have hsnd_lift :
          cfpInsertSnd p.ℓ A ≫
            cfpLift (cfpFst A p.T ≫
              cfpSnd p.T p.T)
              (cfpSnd A p.T) ≫ natPlus =
          cfpSnd p.T p.T := by
        rw [← Category.assoc, cfpLift_precomp]
        rw [show cfpInsertSnd p.ℓ A ≫
            cfpFst A p.T ≫ cfpSnd p.T p.T =
          cfpSnd p.T p.T from by
            rw [← Category.assoc]
            unfold cfpInsertSnd
            rw [cfpLift_fst, Category.id_comp],
          show cfpInsertSnd p.ℓ A ≫
            cfpSnd A p.T =
          cfpTerminalFrom A ≫ p.ℓ from by
            unfold cfpInsertSnd
            exact cfpLift_snd _ _]
        have factor :
            cfpLift (cfpSnd p.T p.T)
              (cfpTerminalFrom A ≫ p.ℓ) =
            cfpSnd p.T p.T ≫
              cfpInsertSnd p.ℓ p.T := by
          unfold cfpInsertSnd
          rw [cfpLift_precomp, Category.comp_id]
          congr 1; rw [← Category.assoc]
          congr 1
          exact (h.terminal.uniq _).symm
        rw [factor, Category.assoc, natPlus_ℓ,
          Category.comp_id]
      rw [hsnd_lift]
      rw [show cfpLift (cfpFst p.T p.T)
          (cfpSnd p.T p.T) = 𝟙 A from
        (cfpLift_uniq _ _ _
          (Category.id_comp _)
          (Category.id_comp _)).symm,
        Category.id_comp]
    · -- Step
      simp only [ψ_R, ← Category.assoc]
      rw [cfpLift_precomp]
      rw [show cfpMap (𝟙 A) natSucc ≫
          cfpFst A p.T ≫ cfpFst p.T p.T =
        cfpFst A p.T ≫ cfpFst p.T p.T from by
          rw [← Category.assoc, cfpMap_fst,
            Category.comp_id]]
      have hsnd_step :
          cfpMap (𝟙 A) natSucc ≫
            cfpLift (cfpFst A p.T ≫
              cfpSnd p.T p.T)
              (cfpSnd A p.T) ≫ natPlus =
          (cfpLift (cfpFst A p.T ≫
              cfpSnd p.T p.T)
            (cfpSnd A p.T) ≫ natPlus) ≫
            natSucc := by
        rw [← Category.assoc, cfpLift_precomp]
        rw [show cfpMap (𝟙 A) natSucc ≫
            cfpFst A p.T ≫ cfpSnd p.T p.T =
          cfpFst A p.T ≫ cfpSnd p.T p.T from by
            rw [← Category.assoc, cfpMap_fst,
              Category.comp_id],
          show cfpMap (𝟙 A) natSucc ≫
            cfpSnd A p.T =
          cfpSnd A p.T ≫ natSucc from
            cfpMap_snd _ _,
          natPlus_succ]
      rw [hsnd_step]
      rw [show cfpLift
          (cfpFst A p.T ≫ cfpFst p.T p.T)
          ((cfpLift (cfpFst A p.T ≫
              cfpSnd p.T p.T)
            (cfpSnd A p.T) ≫ natPlus) ≫
              natSucc) =
        cfpLift (cfpFst A p.T ≫
            cfpFst p.T p.T)
          (cfpLift (cfpFst A p.T ≫
              cfpSnd p.T p.T)
            (cfpSnd A p.T) ≫ natPlus) ≫
          cfpMap (𝟙 p.T) natSucc from by
          rw [cfpLift_cfpMap,
            Category.comp_id],
        Category.assoc,
        natTruncSub_natSucc_second]
      simp only [Category.assoc]
    · -- Norm
      simp only [ψ_R, ← Category.assoc]
      rw [cfpLift_precomp]
      rw [show cfpMap (𝟙 A) toRSpineNat ≫
          cfpFst A p.T ≫ cfpFst p.T p.T =
        cfpFst A p.T ≫ cfpFst p.T p.T from by
          rw [← Category.assoc, cfpMap_fst,
            Category.comp_id]]
      have hsnd_norm :
          cfpMap (𝟙 A) toRSpineNat ≫
            cfpLift (cfpFst A p.T ≫
              cfpSnd p.T p.T)
              (cfpSnd A p.T) ≫ natPlus =
          cfpLift (cfpFst A p.T ≫
              cfpSnd p.T p.T)
            (cfpSnd A p.T) ≫ natPlus := by
        rw [← Category.assoc, cfpLift_precomp]
        rw [show cfpMap (𝟙 A) toRSpineNat ≫
            cfpFst A p.T ≫ cfpSnd p.T p.T =
          cfpFst A p.T ≫ cfpSnd p.T p.T from by
            rw [← Category.assoc, cfpMap_fst,
              Category.comp_id],
          show cfpMap (𝟙 A) toRSpineNat ≫
            cfpSnd A p.T =
          cfpSnd A p.T ≫ toRSpineNat from
            cfpMap_snd _ _]
        rw [show cfpLift (cfpFst A p.T ≫
              cfpSnd p.T p.T)
            (cfpSnd A p.T ≫ toRSpineNat) =
          cfpLift (cfpFst A p.T ≫
              cfpSnd p.T p.T)
            (cfpSnd A p.T) ≫
            cfpMap (𝟙 p.T) toRSpineNat from by
            rw [cfpLift_cfpMap,
              Category.comp_id],
          Category.assoc,
          natPlus_toRSpineNat_second]
      rw [hsnd_norm]
  rw [ψ_L_eq, ψ_R_eq]

/-- `isLeafEndo(v)` implies `isLeafEndo(natPred(v))`:
`boolAnd(isLeafEndo(v), isLeafEndo(natPred(v)))
  = isLeafEndo(v)`. -/
private theorem isLeafEndo_natPred_mono :
    cfpLift isLeafEndo
      (natPred ≫ isLeafEndo) ≫ boolAnd =
    (isLeafEndo : p.T ⟶ p.T) := by
  -- Lift to cfpProd cfpTerminal T ⟶ T and
  -- show both sides equal the same catamorphism.
  set sect : p.T ⟶ cfpProd cfpTerminal p.T :=
    cfpLift (cfpTerminalFrom p.T) (𝟙 p.T)
  set snd : cfpProd cfpTerminal p.T ⟶ p.T :=
    cfpSnd cfpTerminal p.T
  have sect_snd : sect ≫ snd = 𝟙 p.T :=
    cfpLift_snd _ _
  -- Lift LHS.
  set φ : cfpProd cfpTerminal p.T ⟶ p.T :=
    cfpLift (snd ≫ isLeafEndo)
      (snd ≫ natPred ≫ isLeafEndo) ≫ boolAnd
  have sect_φ :
      sect ≫ φ =
      cfpLift isLeafEndo
        (natPred ≫ isLeafEndo) ≫ boolAnd := by
    change sect ≫ cfpLift (snd ≫ isLeafEndo)
        (snd ≫ natPred ≫ isLeafEndo) ≫
      boolAnd = _
    rw [← Category.assoc, cfpLift_precomp]
    simp only [← Category.assoc, sect_snd,
      Category.id_comp]
  -- Lift RHS.
  have sect_isLeafEndo :
      sect ≫ (snd ≫ isLeafEndo) =
      isLeafEndo := by
    rw [← Category.assoc, sect_snd,
      Category.id_comp]
  -- Show φ = snd ≫ isLeafEndo by p.elim_uniq.
  -- Base: cfpInsertSnd ℓ 1 ≫ φ = ℓ.
  have φ_base :
      cfpInsertSnd p.ℓ cfpTerminal ≫ φ = p.ℓ := by
    change cfpInsertSnd p.ℓ cfpTerminal ≫
      cfpLift (snd ≫ isLeafEndo)
        (snd ≫ natPred ≫ isLeafEndo) ≫
      boolAnd = p.ℓ
    have hsnd : cfpInsertSnd p.ℓ cfpTerminal ≫
        snd = p.ℓ := by
      unfold cfpInsertSnd
      rw [cfpLift_snd, cfpTerminalFrom_terminal,
        Category.id_comp]
    rw [← Category.assoc, cfpLift_precomp]
    simp only [← Category.assoc, hsnd]
    rw [isLeafEndo_ℓ, natPred_ℓ,
      isLeafEndo_ℓ, boolAnd_ℓ_ℓ]
  -- Step: cfpMap (𝟙 1) β ≫ φ =
  --   cfpLiftAssoc φ φ ≫ (term ≫ treeFalse).
  have φ_step :
      cfpMap (𝟙 cfpTerminal) p.β ≫ φ =
      cfpLiftAssoc φ φ ≫
        (cfpTerminalFrom (cfpProd p.T p.T) ≫
          treeFalse) := by
    change cfpMap (𝟙 cfpTerminal) p.β ≫
      cfpLift (snd ≫ isLeafEndo)
        (snd ≫ natPred ≫ isLeafEndo) ≫
      boolAnd =
      cfpLiftAssoc φ φ ≫
        (cfpTerminalFrom (cfpProd p.T p.T) ≫
          treeFalse)
    rw [← Category.assoc, cfpLift_precomp]
    have hsnd_β :
        cfpMap (𝟙 cfpTerminal) p.β ≫ snd =
        cfpSnd cfpTerminal (cfpProd p.T p.T) ≫
          p.β := by
      rw [cfpMap_snd]
    rw [show cfpMap (𝟙 cfpTerminal) p.β ≫
        snd ≫ isLeafEndo =
      cfpSnd cfpTerminal (cfpProd p.T p.T) ≫
        p.β ≫ isLeafEndo from by
        rw [← Category.assoc, ← Category.assoc,
          hsnd_β],
      isLeafEndo_β]
    -- First component: cfpSnd ≫ term ≫ treeFalse
    --   = term ≫ treeFalse.
    set D :=
      cfpProd cfpTerminal (cfpProd p.T p.T)
    have hterm :
        cfpSnd cfpTerminal (cfpProd p.T p.T) ≫
          cfpTerminalFrom (cfpProd p.T p.T) =
        cfpTerminalFrom D :=
      h.terminal.uniq _
    rw [show cfpLift
        (cfpSnd cfpTerminal (cfpProd p.T p.T) ≫
          cfpTerminalFrom (cfpProd p.T p.T) ≫
          treeFalse)
        (cfpMap (𝟙 cfpTerminal) p.β ≫
          snd ≫ natPred ≫ isLeafEndo) ≫
        boolAnd =
      cfpLift (cfpTerminalFrom D ≫ treeFalse)
        (cfpMap (𝟙 cfpTerminal) p.β ≫
          snd ≫ natPred ≫ isLeafEndo) ≫
        boolAnd from by
        congr 2
        rw [← Category.assoc, hterm],
      boolAnd_treeFalse_left]
    rw [← Category.assoc]
    congr 1
    exact (h.terminal.uniq _).symm
  -- RHS satisfies the same conditions.
  have rhs_base :
      cfpInsertSnd p.ℓ cfpTerminal ≫
        (snd ≫ isLeafEndo) = p.ℓ := by
    rw [← Category.assoc]
    have : cfpInsertSnd p.ℓ cfpTerminal ≫
        snd = p.ℓ := by
      unfold cfpInsertSnd
      rw [cfpLift_snd, cfpTerminalFrom_terminal,
        Category.id_comp]
    rw [this, isLeafEndo_ℓ]
  have rhs_step :
      cfpMap (𝟙 cfpTerminal) p.β ≫
        (snd ≫ isLeafEndo) =
      cfpLiftAssoc (snd ≫ isLeafEndo)
        (snd ≫ isLeafEndo) ≫
        (cfpTerminalFrom (cfpProd p.T p.T) ≫
          treeFalse) := by
    set D := cfpProd cfpTerminal (cfpProd p.T p.T)
    rw [← Category.assoc, cfpMap_snd,
      Category.assoc, isLeafEndo_β]
    have lhs_term :
        cfpSnd cfpTerminal (cfpProd p.T p.T) ≫
          cfpTerminalFrom (cfpProd p.T p.T) =
        (cfpTerminalFrom D : D ⟶ cfpTerminal) :=
      h.terminal.uniq _
    have rhs_term :
        cfpLiftAssoc (snd ≫ isLeafEndo)
          (snd ≫ isLeafEndo) ≫
          cfpTerminalFrom (cfpProd p.T p.T) =
        (cfpTerminalFrom D : D ⟶ cfpTerminal) :=
      h.terminal.uniq _
    simp only [← Category.assoc]
    rw [lhs_term, rhs_term]
  have rhs_eq :
      snd ≫ isLeafEndo =
      p.elim p.ℓ (cfpTerminalFrom
        (cfpProd p.T p.T) ≫ treeFalse) :=
    p.elim_uniq p.ℓ
      (cfpTerminalFrom (cfpProd p.T p.T) ≫
        treeFalse)
      (snd ≫ isLeafEndo)
      rhs_base rhs_step
  -- Conclude.
  have φ_eq :
      φ = snd ≫ isLeafEndo := by
    rw [rhs_eq]
    exact p.elim_uniq p.ℓ
      (cfpTerminalFrom (cfpProd p.T p.T) ≫
        treeFalse)
      φ φ_base φ_step
  calc cfpLift (isLeafEndo : p.T ⟶ p.T)
        (natPred ≫ isLeafEndo) ≫ boolAnd
      = sect ≫ φ := sect_φ.symm
    _ = sect ≫ (snd ≫ isLeafEndo) := by
        rw [φ_eq]
    _ = isLeafEndo := sect_isLeafEndo

/-- For any `f : cfpProd T T ⟶ T` satisfying the
base condition `boolAnd(isLeafEndo(ℓ), f(ℓ, c))
= ℓ`, the swapped composition
`cfpSwap ≫ cfpLift (cfpFst ≫ isLeafEndo) f
≫ boolAnd` equals the catamorphism
`p.elim (cfpTerminalFrom T ≫ ℓ)
(cfpTerminalFrom _ ≫ treeFalse)`. -/
private theorem swap_isLeafEndo_boolAnd_elim
    (f : cfpProd p.T p.T ⟶ p.T)
    (hbase :
      cfpLift (cfpTerminalFrom p.T ≫ p.ℓ)
        (𝟙 p.T) ≫
        cfpLift (cfpFst p.T p.T ≫ isLeafEndo)
          f ≫ boolAnd =
      cfpTerminalFrom p.T ≫ p.ℓ) :
    cfpSwap p.T p.T ≫
      cfpLift (cfpFst p.T p.T ≫ isLeafEndo)
        f ≫ boolAnd =
    p.elim (cfpTerminalFrom p.T ≫ p.ℓ)
      (cfpTerminalFrom (cfpProd p.T p.T) ≫
        treeFalse) := by
  apply p.elim_uniq
    (cfpTerminalFrom p.T ≫ p.ℓ)
    (cfpTerminalFrom (cfpProd p.T p.T) ≫
      treeFalse)
  · -- Base (w = ℓ).
    simp only [← Category.assoc]
    have : cfpInsertSnd p.ℓ p.T ≫
        cfpSwap p.T p.T =
      cfpLift (cfpTerminalFrom p.T ≫ p.ℓ)
        (𝟙 p.T) := by
      unfold cfpInsertSnd cfpSwap
      rw [cfpLift_precomp, cfpLift_fst,
        cfpLift_snd]
    rw [this]; simp only [Category.assoc]
    exact hbase
  · -- Step (w = β): isLeafEndo(β) = treeFalse,
    -- so boolAnd(treeFalse, _) = treeFalse.
    -- LHS: cfpMap (𝟙 T) β ≫ swap ≫ cfpLift
    --   (fst ≫ ile) f ≫ boolAnd.
    -- After swap, fst picks up β(l,r), so
    -- isLeafEndo gives treeFalse, making
    -- boolAnd(treeFalse, _) = treeFalse.
    rw [← Category.assoc (cfpSwap p.T p.T),
      cfpLift_precomp]
    simp only [← Category.assoc]
    have swap_fst :
        cfpSwap p.T p.T ≫ cfpFst p.T p.T =
        cfpSnd p.T p.T := by
      unfold cfpSwap; exact cfpLift_fst _ _
    rw [show (cfpSwap p.T p.T ≫
        cfpFst p.T p.T) ≫ isLeafEndo =
      cfpSnd p.T p.T ≫ isLeafEndo from by
        rw [swap_fst]]
    rw [cfpLift_precomp]
    simp only [← Category.assoc]
    rw [cfpMap_snd, Category.assoc, Category.assoc,
      isLeafEndo_β, ← Category.assoc,
      show cfpSnd p.T (cfpProd p.T p.T) ≫
        cfpTerminalFrom (cfpProd p.T p.T) =
      cfpTerminalFrom
        (cfpProd p.T (cfpProd p.T p.T)) from
        h.terminal.uniq _,
      Category.assoc, boolAnd_treeFalse_left]
    simp only [← Category.assoc]
    congr 1
    exact (h.terminal.uniq _).symm

/-- `natTruncSub(natPred(a), b)
  = natPred(natTruncSub(a, b))`:
`natTruncSub` commutes with `natPred`
on its first argument. -/
theorem natTruncSub_natPred_first :
    cfpMap natPred (𝟙 p.T) ≫ natTruncSub =
    natTruncSub ≫ (natPred : p.T ⟶ p.T) := by
  rw [natTruncSub_natPred]
  unfold natTruncSub
  rw [elim_naturality natPred (𝟙 p.T)
    (cfpSnd p.T p.T ≫ natPred),
    Category.comp_id]


/-- Monotonicity of `isLeafEndo` under truncated
subtraction: `boolAnd(isLeafEndo(w),
isLeafEndo(natTruncSub(w, c))) = isLeafEndo(w)`.
Proved by folding on the first argument `w`. -/
theorem isLeafEndo_natTruncSub_mono :
    cfpLift (cfpFst p.T p.T ≫ isLeafEndo)
      (natTruncSub ≫ isLeafEndo) ≫ boolAnd =
    cfpFst p.T p.T ≫ isLeafEndo := by
  have swap_fst :
      cfpSwap p.T p.T ≫ cfpFst p.T p.T =
      cfpSnd p.T p.T := by
    unfold cfpSwap; exact cfpLift_fst _ _
  have swap_snd :
      cfpSwap p.T p.T ≫ cfpSnd p.T p.T =
      cfpFst p.T p.T := by
    unfold cfpSwap; exact cfpLift_snd _ _
  have swap_invol :
      cfpSwap p.T p.T ≫ cfpSwap p.T p.T =
      𝟙 (cfpProd p.T p.T) := by
    rw [show 𝟙 (cfpProd p.T p.T) =
        cfpLift (cfpFst p.T p.T)
          (cfpSnd p.T p.T) from
      cfpLift_uniq _ _ _
        (Category.id_comp _)
        (Category.id_comp _)]
    apply cfpLift_uniq
    · rw [Category.assoc, swap_fst, swap_snd]
    · rw [Category.assoc, swap_snd, swap_fst]
  -- Show cfpSwap ≫ LHS = catam.
  have swap_lhs :
      cfpSwap p.T p.T ≫
        (cfpLift (cfpFst p.T p.T ≫ isLeafEndo)
          (natTruncSub ≫ isLeafEndo) ≫
          boolAnd) =
      p.elim (cfpTerminalFrom p.T ≫ p.ℓ)
        (cfpTerminalFrom (cfpProd p.T p.T) ≫
          treeFalse) := by
    have h := swap_isLeafEndo_boolAnd_elim
      (natTruncSub ≫ isLeafEndo) (by
        have inner :
            cfpLift (cfpTerminalFrom p.T ≫ p.ℓ)
              (𝟙 p.T) ≫
              cfpLift
                (cfpFst p.T p.T ≫ isLeafEndo)
                (natTruncSub ≫ isLeafEndo) =
            cfpLift (cfpTerminalFrom p.T ≫ p.ℓ)
              (cfpTerminalFrom p.T ≫ p.ℓ) := by
          apply cfpLift_uniq
          · rw [Category.assoc, cfpLift_fst,
              ← Category.assoc, cfpLift_fst,
              Category.assoc, isLeafEndo_ℓ]
          · rw [Category.assoc, cfpLift_snd,
              ← Category.assoc,
              natTruncSub_ℓ_left (𝟙 p.T),
              Category.assoc, isLeafEndo_ℓ]
        calc cfpLift
                (cfpTerminalFrom p.T ≫ p.ℓ)
                (𝟙 p.T) ≫
              cfpLift
                (cfpFst p.T p.T ≫ isLeafEndo)
                (natTruncSub ≫ isLeafEndo) ≫
              (boolAnd : cfpProd p.T p.T ⟶ p.T)
            = (cfpLift
                (cfpTerminalFrom p.T ≫ p.ℓ)
                (𝟙 p.T) ≫
              cfpLift
                (cfpFst p.T p.T ≫ isLeafEndo)
                (natTruncSub ≫ isLeafEndo)) ≫
                boolAnd :=
              (Category.assoc _ _ _).symm
          _ = cfpLift
                (cfpTerminalFrom p.T ≫ p.ℓ)
                (cfpTerminalFrom p.T ≫ p.ℓ) ≫
                boolAnd := by
              rw [inner]
          _ = (cfpTerminalFrom p.T ≫
                cfpLift p.ℓ p.ℓ) ≫
                boolAnd := by
              rw [(cfpLift_precomp
                (cfpTerminalFrom p.T)
                p.ℓ p.ℓ).symm]
          _ = cfpTerminalFrom p.T ≫
                (cfpLift p.ℓ p.ℓ ≫ boolAnd) :=
              Category.assoc _ _ _
          _ = cfpTerminalFrom p.T ≫ p.ℓ := by
              rw [boolAnd_ℓ_ℓ])
    exact h
  -- Show cfpSwap ≫ RHS = same catamorphism.
  have swap_rhs :
      cfpSwap p.T p.T ≫
        (cfpFst p.T p.T ≫ isLeafEndo) =
      p.elim (cfpTerminalFrom p.T ≫ p.ℓ)
        (cfpTerminalFrom (cfpProd p.T p.T) ≫
          treeFalse) := by
    rw [← Category.assoc, swap_fst]
    apply p.elim_uniq
      (cfpTerminalFrom p.T ≫ p.ℓ)
      (cfpTerminalFrom (cfpProd p.T p.T) ≫
        treeFalse)
    · rw [← Category.assoc]
      unfold cfpInsertSnd
      rw [cfpLift_snd, Category.assoc,
        isLeafEndo_ℓ]
    · rw [← Category.assoc, cfpMap_snd,
        Category.assoc, isLeafEndo_β,
        ← Category.assoc,
        show cfpSnd p.T (cfpProd p.T p.T) ≫
          cfpTerminalFrom (cfpProd p.T p.T) =
        cfpTerminalFrom
          (cfpProd p.T (cfpProd p.T p.T)) from
          h.terminal.uniq _,
        ← show cfpLiftAssoc
            (cfpSnd p.T p.T ≫ isLeafEndo)
            (cfpSnd p.T p.T ≫ isLeafEndo) ≫
          cfpTerminalFrom (cfpProd p.T p.T) =
        cfpTerminalFrom
          (cfpProd p.T (cfpProd p.T p.T)) from
          h.terminal.uniq _,
        Category.assoc]
  -- Cancel swap.
  have h_eq :
      cfpSwap p.T p.T ≫
        (cfpLift (cfpFst p.T p.T ≫ isLeafEndo)
          (natTruncSub ≫ isLeafEndo) ≫
          boolAnd) =
      cfpSwap p.T p.T ≫
        (cfpFst p.T p.T ≫ isLeafEndo) := by
    rw [swap_lhs, swap_rhs]
  calc cfpLift (cfpFst p.T p.T ≫ isLeafEndo)
          (natTruncSub ≫ isLeafEndo) ≫ boolAnd
      = 𝟙 _ ≫ (cfpLift
          (cfpFst p.T p.T ≫ isLeafEndo)
          (natTruncSub ≫ isLeafEndo) ≫
          boolAnd) :=
        (Category.id_comp _).symm
    _ = (cfpSwap p.T p.T ≫
          cfpSwap p.T p.T) ≫
          (cfpLift
            (cfpFst p.T p.T ≫ isLeafEndo)
            (natTruncSub ≫ isLeafEndo) ≫
            boolAnd) := by
        rw [swap_invol]
    _ = cfpSwap p.T p.T ≫
          (cfpSwap p.T p.T ≫
            (cfpLift
              (cfpFst p.T p.T ≫ isLeafEndo)
              (natTruncSub ≫ isLeafEndo) ≫
              boolAnd)) := by
        rw [Category.assoc]
    _ = cfpSwap p.T p.T ≫
          (cfpSwap p.T p.T ≫
            (cfpFst p.T p.T ≫
              isLeafEndo)) := by
        rw [h_eq]
    _ = (cfpSwap p.T p.T ≫
          cfpSwap p.T p.T) ≫
          (cfpFst p.T p.T ≫ isLeafEndo) := by
        rw [Category.assoc]
    _ = cfpFst p.T p.T ≫ isLeafEndo := by
        rw [swap_invol, Category.id_comp]

/-- Fold composition: iterating `g` a total of
`m + n` times decomposes as `n` iterations after
`m` iterations.  That is,
`g^n(nnoElim f g (a, m)) = nnoElim f g (a, m+n)`,
expressed as:
`cfpMap (nnoElim f g) (𝟙 T) ≫ nnoElim (𝟙 X) g
  = nnoElim (nnoElim f g) g`. -/
private theorem cfpMap_comm_snd
    {B X : C} (f : B ⟶ X) (k : p.T ⟶ p.T) :
    cfpMap (𝟙 B) k ≫ cfpMap f (𝟙 p.T) =
    cfpMap f (𝟙 p.T) ≫ cfpMap (𝟙 X) k := by
  rw [cfpMap_comp, cfpMap_comp]
  simp only [Category.id_comp, Category.comp_id]

private theorem nnoElim_absorbs_toRSN
    {X : C} (g : X ⟶ X) :
    cfpMap (𝟙 X) toRSpineNat ≫
      nnoElim (𝟙 X) g =
    nnoElim (𝟙 X) g := by
  unfold nnoElim
  rw [← Category.assoc]
  congr 1
  rw [cfpMap_comp, Category.id_comp,
    toRSpineNat_idem]

theorem nnoElim_fold_compose
    {A X : C} (f : A ⟶ X) (g : X ⟶ X) :
    cfpMap (nnoElim f g) (𝟙 p.T) ≫
      nnoElim (𝟙 X) g =
    nnoElim (nnoElim f g) g := by
  apply nnoElim_uniq
  · -- Base: cfpInsertSnd ℓ ≫ φ = nnoElim f g
    rw [← Category.assoc,
      cfpInsertSnd_cfpMap,
      Category.assoc, nnoElim_ℓ,
      Category.comp_id]
  · -- Step: cfpMap (𝟙 _) natSucc ≫ φ = φ ≫ g
    rw [Category.assoc, ← Category.assoc
      (cfpMap (𝟙 _) natSucc)
      (cfpMap (nnoElim f g) (𝟙 p.T)),
      cfpMap_comm_snd,
      Category.assoc, nnoElim_s]
  · -- Norm: cfpMap (𝟙 _) toRSN ≫ φ = φ
    rw [← Category.assoc
      (cfpMap (𝟙 _) toRSpineNat)
      (cfpMap (nnoElim f g) (𝟙 p.T)),
      cfpMap_comm_snd,
      Category.assoc, nnoElim_absorbs_toRSN]

end GebLean
