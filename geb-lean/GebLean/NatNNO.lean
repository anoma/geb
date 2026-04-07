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

end GebLean
