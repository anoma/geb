import GebLean.NatArith

/-!
# Goedel Encoding of Trees

Defines a Goedel encoding of binary trees as
right-spine natural numbers via Cantor pairing, with
computation rules for leaves and branches.
-/

namespace GebLean

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]
  [h : HasChosenFiniteProducts C]
  [p : HasPBTO C]

/-- Parameterized Goedel encoding of trees as
right-spine naturals.
`treeToNatParam(a, leaf) = ℓ(a)`,
`treeToNatParam(a, branch(l, r)) =
  natSucc(cantorPair(
    treeToNatParam(a, l),
    treeToNatParam(a, r)))`.
Uses `p.elim` with carrier `p.T`:
base = `p.ℓ`, step = `cantorPair ≫ natSucc`. -/
def treeToNatParam :
    cfpProd cfpTerminal p.T ⟶ p.T :=
  p.elim p.ℓ (cantorPair ≫ natSucc)

/-- Leaf computation rule for `treeToNatParam`:
`treeToNatParam(a, leaf) = ℓ(a)`. -/
theorem treeToNatParam_ℓ :
    cfpInsertSnd p.ℓ cfpTerminal ≫
      treeToNatParam =
    p.ℓ := by
  unfold treeToNatParam
  exact p.elim_ℓ p.ℓ _

/-- Branch computation rule for `treeToNatParam`:
`treeToNatParam(a, branch(l, r)) =
  natSucc(cantorPair(
    treeToNatParam(a, l),
    treeToNatParam(a, r)))`. -/
theorem treeToNatParam_β :
    cfpMap (𝟙 cfpTerminal) p.β ≫
      treeToNatParam =
    cfpLiftAssoc treeToNatParam
      treeToNatParam ≫
      (cantorPair ≫ natSucc) := by
  unfold treeToNatParam
  exact p.elim_β p.ℓ _

/-- Goedel encoding of trees as right-spine naturals.
`treeToNat(leaf) = 0`,
`treeToNat(branch(l, r)) =
  succ(cantorPair(treeToNat(l), treeToNat(r)))`.
Defined as the composition of the terminal-pairing
morphism with `treeToNatParam`. -/
def treeToNat : p.T ⟶ p.T :=
  cfpLift (cfpTerminalFrom p.T) (𝟙 p.T) ≫
    treeToNatParam

/-- Leaf computation rule for `treeToNat`:
`treeToNat(leaf) = leaf`. -/
theorem treeToNat_ℓ :
    p.ℓ ≫ treeToNat =
    (p.ℓ : cfpTerminal (C := C) ⟶ p.T) := by
  unfold treeToNat
  rw [← Category.assoc]
  have factor :
      p.ℓ ≫ cfpLift (cfpTerminalFrom p.T)
        (𝟙 p.T) =
      cfpInsertSnd p.ℓ cfpTerminal := by
    unfold cfpInsertSnd
    rw [cfpLift_precomp, Category.comp_id]
    have hterm :
        p.ℓ ≫ cfpTerminalFrom p.T =
        cfpTerminalFrom cfpTerminal :=
      h.terminal.uniq _
    rw [hterm, cfpTerminalFrom_terminal,
      Category.id_comp]
  rw [factor, treeToNatParam_ℓ]

/-- The composition `p.β ≫ cfpLift
(cfpTerminalFrom T) (𝟙 T)` factors through
`cfpMap (𝟙 1) p.β`. -/
private theorem β_cfpLift_factor :
    p.β ≫ cfpLift (cfpTerminalFrom p.T)
      (𝟙 p.T) =
    cfpLift
      (cfpTerminalFrom (cfpProd p.T p.T))
      (𝟙 (cfpProd p.T p.T)) ≫
      cfpMap (𝟙 cfpTerminal) p.β := by
  rw [cfpLift_precomp, Category.comp_id]
  unfold cfpMap
  rw [cfpLift_precomp]
  congr 1
  · rw [← Category.assoc, cfpLift_fst,
      Category.comp_id]
    exact h.terminal.uniq _
  · rw [← Category.assoc, cfpLift_snd,
      Category.id_comp]

/-- Pre-composing `cfpAssocFst` with the
terminal-pairing on `T × T` extracts the
first-component terminal pairing. -/
private theorem cfpLift_cfpAssocFst :
    cfpLift
      (cfpTerminalFrom (cfpProd p.T p.T))
      (𝟙 (cfpProd p.T p.T)) ≫
      cfpAssocFst cfpTerminal p.T p.T =
    cfpLift
      (cfpTerminalFrom (cfpProd p.T p.T))
      (cfpFst p.T p.T) := by
  unfold cfpAssocFst
  rw [cfpLift_precomp]
  apply cfpLift_uniq
  · rw [cfpLift_fst, cfpLift_fst]
  · rw [cfpLift_snd, ← Category.assoc,
      cfpLift_snd, Category.id_comp]

/-- Pre-composing `cfpAssocSnd` with the
terminal-pairing on `T × T` extracts the
second-component terminal pairing. -/
private theorem cfpLift_cfpAssocSnd :
    cfpLift
      (cfpTerminalFrom (cfpProd p.T p.T))
      (𝟙 (cfpProd p.T p.T)) ≫
      cfpAssocSnd cfpTerminal p.T p.T =
    cfpLift
      (cfpTerminalFrom (cfpProd p.T p.T))
      (cfpSnd p.T p.T) := by
  unfold cfpAssocSnd
  rw [cfpLift_precomp]
  apply cfpLift_uniq
  · rw [cfpLift_fst, cfpLift_fst]
  · rw [cfpLift_snd, ← Category.assoc,
      cfpLift_snd, Category.id_comp]

/-- For any projection `π : T × T ⟶ T`, the
terminal pairing `cfpLift (cfpTerminalFrom (T×T)) π`
equals `cfpLift (π ≫ cfpTerminalFrom T) π`. -/
private theorem cfpLift_term_proj
    (π : cfpProd p.T p.T ⟶ p.T) :
    cfpLift
      (cfpTerminalFrom (cfpProd p.T p.T)) π =
    cfpLift (π ≫ cfpTerminalFrom p.T) π := by
  congr 1
  exact (h.terminal.uniq _).symm

/-- For any morphism `k : D ⟶ T`, the
terminal pairing
`cfpLift (k ≫ cfpTerminalFrom T) k` equals
`k ≫ cfpLift (cfpTerminalFrom T) (𝟙 T)`. -/
private theorem cfpLift_term_proj_precomp
    {D : C} (k : D ⟶ p.T) :
    cfpLift (k ≫ cfpTerminalFrom p.T) k =
    k ≫ cfpLift (cfpTerminalFrom p.T)
      (𝟙 p.T) := by
  rw [cfpLift_precomp, Category.comp_id]

/-- The first-component terminal pairing composes
with `treeToNatParam` to yield the first projection
followed by `treeToNat`. -/
private theorem cfpLift_fst_treeToNatParam :
    cfpLift
      (cfpTerminalFrom (cfpProd p.T p.T))
      (cfpFst p.T p.T) ≫
      treeToNatParam =
    cfpFst p.T p.T ≫ treeToNat := by
  unfold treeToNat
  rw [cfpLift_term_proj,
    cfpLift_term_proj_precomp,
    Category.assoc]

/-- The second-component terminal pairing composes
with `treeToNatParam` to yield the second projection
followed by `treeToNat`. -/
private theorem cfpLift_snd_treeToNatParam :
    cfpLift
      (cfpTerminalFrom (cfpProd p.T p.T))
      (cfpSnd p.T p.T) ≫
      treeToNatParam =
    cfpSnd p.T p.T ≫ treeToNat := by
  unfold treeToNat
  rw [cfpLift_term_proj,
    cfpLift_term_proj_precomp,
    Category.assoc]

/-- The composition of the terminal-pairing
morphism applied to `T × T` with `cfpLiftAssoc
treeToNatParam treeToNatParam` equals
`cfpMap treeToNat treeToNat`. -/
private theorem cfpLift_cfpLiftAssoc_eq :
    cfpLift
      (cfpTerminalFrom (cfpProd p.T p.T))
      (𝟙 (cfpProd p.T p.T)) ≫
      cfpLiftAssoc treeToNatParam
        treeToNatParam =
    cfpMap treeToNat treeToNat := by
  unfold cfpLiftAssoc cfpMap
  rw [cfpLift_precomp]
  apply cfpLift_uniq
  · rw [cfpLift_fst, ← Category.assoc,
      cfpLift_cfpAssocFst,
      cfpLift_fst_treeToNatParam]
  · rw [cfpLift_snd, ← Category.assoc,
      cfpLift_cfpAssocSnd,
      cfpLift_snd_treeToNatParam]

/-- Branch computation rule for `treeToNat`:
`treeToNat(branch(l, r)) =
  natSucc(cantorPair(treeToNat(l),
    treeToNat(r)))`. -/
theorem treeToNat_β :
    p.β ≫ treeToNat =
    cfpMap treeToNat treeToNat ≫
      cantorPair ≫ natSucc := by
  conv_lhs => rw [show treeToNat =
    cfpLift (cfpTerminalFrom p.T) (𝟙 p.T) ≫
      treeToNatParam from rfl]
  rw [← Category.assoc, β_cfpLift_factor]
  simp only [Category.assoc]
  rw [treeToNatParam_β, ← Category.assoc,
    cfpLift_cfpLiftAssoc_eq]

/-- Comparing two branch-encoded values via `natEq`
cancels the `natSucc`:
`natEq(treeToNat(β(l₁,r₁)), treeToNat(β(l₂,r₂)))
  = natEq(cantorPair(treeToNat(l₁),treeToNat(r₁)),
          cantorPair(treeToNat(l₂),treeToNat(r₂)))`.
-/
theorem treeToNat_β_natEq :
    cfpLift (p.β ≫ treeToNat)
        (p.β ≫ treeToNat) ≫ natEq =
    cfpLift
        (cfpMap treeToNat treeToNat ≫
          cantorPair)
        (cfpMap treeToNat treeToNat ≫
          cantorPair) ≫
      natEq := by
  have h1 :
      p.β ≫ treeToNat =
      (cfpMap treeToNat treeToNat ≫
        cantorPair) ≫ natSucc := by
    rw [treeToNat_β, Category.assoc]
  rw [h1]
  exact @natEq_succ_cancel C _ h p
    (cfpProd p.T p.T)
    (cfpMap treeToNat treeToNat ≫ cantorPair)
    (cfpMap treeToNat treeToNat ≫ cantorPair)

/-- `treeToNatParam ≫ toRSpineNat =
treeToNatParam`. -/
private theorem treeToNatParam_rsn :
    treeToNatParam ≫ toRSpineNat =
    (treeToNatParam :
      cfpProd cfpTerminal p.T ⟶ p.T) := by
  unfold treeToNatParam
  have hw :
      cfpMap toRSpineNat toRSpineNat ≫
        ((cantorPair :
          cfpProd p.T p.T ⟶ p.T) ≫
          natSucc) =
      (cantorPair ≫ natSucc) ≫
        toRSpineNat := by
    rw [← Category.assoc,
      cantorPair_toRSpineNat_comm,
      Category.assoc, Category.assoc,
      natSucc_toRSpineNat_comm]
  rw [elim_algebra_morphism p.ℓ
    (cantorPair ≫ natSucc)
    toRSpineNat
    (cantorPair ≫ natSucc)
    hw,
    toRSpineNat_ℓ]

/-- `treeToNat` is right-spine normalized. -/
theorem treeToNat_isRSpineNatNorm :
    IsRSpineNatNorm
      (treeToNat : p.T ⟶ p.T) := by
  unfold IsRSpineNatNorm treeToNat
  rw [Category.assoc,
    treeToNatParam_rsn]

variable {D : C}

/-- Truncated subtraction with zero as first
argument yields zero:
`natTruncSub(ℓ, t) = ℓ` for all `t`. -/
theorem natTruncSub_ℓ_left
    (a : D ⟶ p.T) :
    cfpLift (cfpTerminalFrom D ≫ p.ℓ) a ≫
      natTruncSub =
    cfpTerminalFrom D ≫ p.ℓ := by
  have factor :
      cfpLift (cfpTerminalFrom D ≫ p.ℓ) a =
      cfpLift (𝟙 D) a ≫
        cfpMap (cfpTerminalFrom D ≫ p.ℓ)
          (𝟙 p.T) := by
    symm
    apply cfpLift_uniq
    · rw [Category.assoc, cfpMap_fst,
        ← Category.assoc, cfpLift_fst,
        Category.id_comp]
    · rw [Category.assoc, cfpMap_snd,
        ← Category.assoc, cfpLift_snd,
        Category.comp_id]
  rw [factor, Category.assoc]
  unfold natTruncSub
  rw [elim_naturality
    (cfpTerminalFrom D ≫ p.ℓ)
    (𝟙 p.T)
    (cfpSnd p.T p.T ≫ natPred)]
  simp only [Category.comp_id]
  have const_eq :
      cfpTerminalFrom (cfpProd D p.T) ≫ p.ℓ =
      p.elim (cfpTerminalFrom D ≫ p.ℓ)
        (cfpSnd p.T p.T ≫ natPred) :=
    p.elim_uniq _ _ _ (by
      rw [← Category.assoc]
      congr 1
      exact h.terminal.uniq _
    ) (by
      have lhs_eq :
          cfpMap (𝟙 D) p.β ≫
            cfpTerminalFrom
              (cfpProd D p.T) ≫ p.ℓ =
          cfpTerminalFrom
            (cfpProd D
              (cfpProd p.T p.T)) ≫ p.ℓ := by
        rw [← Category.assoc]
        congr 1
        exact h.terminal.uniq _
      rw [lhs_eq]
      unfold cfpLiftAssoc
      rw [← Category.assoc
        (cfpLift _ _)
        (cfpSnd p.T p.T) natPred,
        cfpLift_snd, ← Category.assoc]
      have :
          cfpAssocSnd D p.T p.T ≫
            cfpTerminalFrom (cfpProd D p.T) =
          cfpTerminalFrom
            (cfpProd D
              (cfpProd p.T p.T)) :=
        h.terminal.uniq _
      rw [this, Category.assoc, natPred_ℓ])
  rw [← const_eq, ← Category.assoc]
  congr 1
  exact h.terminal.uniq _

/-- `natSucc ≫ isLeafEndo = cfpTerminalFrom T ≫
treeFalse`: the successor of any right-spine natural
is not a leaf. -/
theorem natSucc_isLeafEndo :
    natSucc ≫ isLeafEndo =
    cfpTerminalFrom p.T ≫
      (treeFalse : cfpTerminal (C := C) ⟶ _)
    := by
  unfold natSucc
  rw [Category.assoc, isLeafEndo_β,
    ← Category.assoc]
  congr 1
  exact h.terminal.uniq _

/-- `natEq(ℓ, natSucc(a)) = treeFalse`:
comparing zero against any successor yields
false. -/
theorem natEq_ℓ_succ (a : D ⟶ p.T) :
    cfpLift (cfpTerminalFrom D ≫ p.ℓ)
        (a ≫ natSucc) ≫ natEq =
    cfpTerminalFrom D ≫ treeFalse := by
  unfold natEq
  rw [← Category.assoc, ← Category.assoc,
    cfpLift_precomp]
  have comp1 :
      cfpLift (cfpTerminalFrom D ≫ p.ℓ)
        (a ≫ natSucc) ≫ natTruncSub =
      cfpTerminalFrom D ≫ p.ℓ :=
    natTruncSub_ℓ_left (a ≫ natSucc)
  have hswap :
      cfpLift (cfpTerminalFrom D ≫ p.ℓ)
        (a ≫ natSucc) ≫
        cfpSwap p.T p.T =
      cfpLift (a ≫ natSucc)
        (cfpTerminalFrom D ≫ p.ℓ) := by
    unfold cfpSwap
    rw [cfpLift_precomp, cfpLift_fst,
      cfpLift_snd]
  have comp2_factor :
      cfpLift (a ≫ natSucc)
        (cfpTerminalFrom D ≫ p.ℓ) =
      (a ≫ natSucc) ≫
        cfpInsertSnd p.ℓ p.T := by
    unfold cfpInsertSnd
    rw [cfpLift_precomp, Category.comp_id]
    congr 1
    rw [← Category.assoc]
    have : (a ≫ natSucc) ≫
        cfpTerminalFrom p.T =
        cfpTerminalFrom D :=
      h.terminal.uniq _
    rw [this]
  have comp2 :
      cfpLift (cfpTerminalFrom D ≫ p.ℓ)
        (a ≫ natSucc) ≫
        cfpSwap p.T p.T ≫ natTruncSub =
      a ≫ natSucc := by
    rw [← Category.assoc, hswap,
      comp2_factor, Category.assoc,
      natTruncSub_ℓ, Category.comp_id]
  rw [comp1, comp2]
  rw [natPlus_succ, Category.assoc,
    natSucc_isLeafEndo, ← Category.assoc]
  congr 1
  exact h.terminal.uniq _

/-- `natEq(natSucc(a), ℓ) = treeFalse`:
comparing any successor against zero yields
false. -/
theorem natEq_succ_ℓ (a : D ⟶ p.T) :
    cfpLift (a ≫ natSucc)
        (cfpTerminalFrom D ≫ p.ℓ) ≫ natEq =
    cfpTerminalFrom D ≫ treeFalse := by
  unfold natEq
  rw [← Category.assoc, ← Category.assoc,
    cfpLift_precomp]
  have comp1_factor :
      cfpLift (a ≫ natSucc)
        (cfpTerminalFrom D ≫ p.ℓ) =
      (a ≫ natSucc) ≫
        cfpInsertSnd p.ℓ p.T := by
    unfold cfpInsertSnd
    rw [cfpLift_precomp, Category.comp_id]
    congr 1
    rw [← Category.assoc]
    have : (a ≫ natSucc) ≫
        cfpTerminalFrom p.T =
        cfpTerminalFrom D :=
      h.terminal.uniq _
    rw [this]
  have comp1 :
      cfpLift (a ≫ natSucc)
        (cfpTerminalFrom D ≫ p.ℓ) ≫
        natTruncSub =
      a ≫ natSucc := by
    rw [comp1_factor, Category.assoc,
      natTruncSub_ℓ, Category.comp_id]
  have hswap :
      cfpLift (a ≫ natSucc)
        (cfpTerminalFrom D ≫ p.ℓ) ≫
        cfpSwap p.T p.T =
      cfpLift (cfpTerminalFrom D ≫ p.ℓ)
        (a ≫ natSucc) := by
    unfold cfpSwap
    rw [cfpLift_precomp, cfpLift_fst,
      cfpLift_snd]
  have comp2 :
      cfpLift (a ≫ natSucc)
        (cfpTerminalFrom D ≫ p.ℓ) ≫
        cfpSwap p.T p.T ≫ natTruncSub =
      cfpTerminalFrom D ≫ p.ℓ := by
    rw [← Category.assoc, hswap,
      natTruncSub_ℓ_left]
  rw [comp1, comp2]
  rw [natPlus_zero, Category.assoc,
    natSucc_isLeafEndo, ← Category.assoc]
  congr 1
  exact h.terminal.uniq _

end GebLean
