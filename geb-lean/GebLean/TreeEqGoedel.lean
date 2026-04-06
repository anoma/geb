import GebLean.TreeGoedel

/-!
# Tree Equality via Goedel Encoding

Defines tree equality by encoding both trees as
right-spine naturals via the Goedel encoding
(`treeToNat`) and comparing via `natEq`.
Establishes computation rules for all four
leaf/branch combinations.
-/

namespace GebLean

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]
  [h : HasChosenFiniteProducts C]
  [p : HasPBTO C]

/-- Tree equality via Goedel encoding: encode both
trees as right-spine naturals, compare the naturals.
Returns `p.ℓ` iff the trees are structurally equal,
`treeFalse` otherwise. -/
def treeEqG : cfpProd p.T p.T ⟶ p.T :=
  cfpMap treeToNat treeToNat ≫ natEq

/-- `treeEqG` is Boolean-valued:
`treeEqG ≫ isLeafEndo = treeEqG`. -/
theorem treeEqG_bool :
    treeEqG ≫ isLeafEndo =
    (treeEqG : cfpProd p.T p.T ⟶ p.T) := by
  unfold treeEqG
  rw [Category.assoc, natEq_bool]

/-- `natEq` at `(ℓ, ℓ)` yields `ℓ`. -/
private theorem natEq_refl_ℓ :
    cfpLift (p.ℓ : cfpTerminal (C := C) ⟶ p.T)
      p.ℓ ≫ natEq =
    (p.ℓ : cfpTerminal (C := C) ⟶ p.T) := by
  have factor :
      cfpLift
        (p.ℓ : cfpTerminal (C := C) ⟶ p.T)
        p.ℓ =
      p.ℓ ≫ cfpLift (𝟙 p.T) (𝟙 p.T) := by
    rw [cfpLift_precomp, Category.comp_id]
  rw [factor, Category.assoc, natEq_refl,
    ← Category.assoc]
  exact (congrArg (· ≫ p.ℓ)
    (h.terminal.uniq _)).trans
    ((congrArg (· ≫ p.ℓ)
      cfpTerminalFrom_terminal).trans
      (Category.id_comp p.ℓ))

/-- Leaf-leaf computation rule for `treeEqG`:
`treeEqG(ℓ, ℓ) = ℓ`. -/
theorem treeEqG_ℓℓ :
    cfpLift p.ℓ p.ℓ ≫ treeEqG =
    (p.ℓ : cfpTerminal (C := C) ⟶ p.T) := by
  change cfpLift p.ℓ p.ℓ ≫
    cfpMap treeToNat treeToNat ≫ natEq = p.ℓ
  rw [← Category.assoc, cfpLift_cfpMap,
    treeToNat_ℓ]
  exact natEq_refl_ℓ

/-- Leaf-branch computation rule for `treeEqG`:
`treeEqG(ℓ, β(a, b)) = treeFalse`. -/
theorem treeEqG_ℓβ :
    cfpMap p.ℓ p.β ≫ treeEqG =
    cfpTerminalFrom _ ≫
      (treeFalse : cfpTerminal (C := C) ⟶ p.T)
      := by
  unfold treeEqG
  rw [← Category.assoc, cfpMap_comp,
    treeToNat_ℓ, treeToNat_β]
  have step :
      cfpMap (p.ℓ : cfpTerminal (C := C) ⟶ p.T)
        (cfpMap treeToNat treeToNat ≫
          cantorPair ≫ natSucc) =
      cfpLift
        (cfpTerminalFrom
          (cfpProd cfpTerminal
            (cfpProd p.T p.T)) ≫ p.ℓ)
        (cfpSnd cfpTerminal (cfpProd p.T p.T) ≫
          cfpMap treeToNat treeToNat ≫
          cantorPair ≫ natSucc) := by
    unfold cfpMap
    apply cfpLift_uniq
    · rw [cfpLift_fst]
      congr 1; exact h.terminal.uniq _
    · rw [cfpLift_snd]
  have reassoc :
      cfpSnd cfpTerminal (cfpProd p.T p.T) ≫
        cfpMap treeToNat treeToNat ≫
        cantorPair ≫ natSucc =
      (cfpSnd cfpTerminal (cfpProd p.T p.T) ≫
        cfpMap treeToNat treeToNat ≫
        cantorPair) ≫ natSucc := by
    simp only [Category.assoc]
  rw [step, reassoc]
  exact natEq_ℓ_succ _

/-- Branch-leaf computation rule for `treeEqG`:
`treeEqG(β(a, b), ℓ) = treeFalse`. -/
theorem treeEqG_βℓ :
    cfpMap p.β p.ℓ ≫ treeEqG =
    cfpTerminalFrom _ ≫
      (treeFalse : cfpTerminal (C := C) ⟶ p.T)
      := by
  unfold treeEqG
  rw [← Category.assoc, cfpMap_comp,
    treeToNat_β, treeToNat_ℓ]
  have step :
      cfpMap
        (cfpMap treeToNat treeToNat ≫
          cantorPair ≫ natSucc)
        (p.ℓ : cfpTerminal (C := C) ⟶ p.T) ≫
        natEq =
      cfpLift
        ((cfpFst (cfpProd p.T p.T)
          cfpTerminal ≫
          cfpMap treeToNat treeToNat ≫
          cantorPair) ≫ natSucc)
        (cfpTerminalFrom _ ≫ p.ℓ) ≫ natEq := by
    congr 1
    unfold cfpMap
    apply cfpLift_uniq
    · rw [cfpLift_fst]
      simp only [Category.assoc]
    · rw [cfpLift_snd]
      congr 1; exact h.terminal.uniq _
  rw [step]
  exact natEq_succ_ℓ _

/-- Composing `cfpMap p.β p.β` with
`cfpMap treeToNat treeToNat` and canceling
`natSucc` via `natEq_succ_cancel`.
Reduces `treeEqG_ββ` to comparing
`cantorPair`-encoded values via `natEq`. -/
private theorem treeEqG_ββ_reduce :
    cfpMap p.β p.β ≫ treeEqG =
    cfpMap
      (cfpMap treeToNat treeToNat ≫ cantorPair)
      (cfpMap treeToNat treeToNat ≫
        cantorPair) ≫
    (natEq : cfpProd p.T p.T ⟶ p.T) := by
  unfold treeEqG
  rw [← Category.assoc, cfpMap_comp,
    treeToNat_β]
  rw [cfpMap_comp_comp
    (cfpMap treeToNat treeToNat) _
    (cfpMap treeToNat treeToNat) _,
    cfpMap_comp_comp
      (cantorPair : cfpProd p.T p.T ⟶ p.T) _
      cantorPair _,
    Category.assoc, Category.assoc]
  rw [← cfpMap_comp]
  have natSucc_cancel :
      cfpMap (natSucc : p.T ⟶ p.T) natSucc ≫
        natEq =
      (natEq : cfpProd p.T p.T ⟶ p.T) := by
    unfold cfpMap
    rw [natEq_succ_cancel,
      show cfpLift (cfpFst p.T p.T)
        (cfpSnd p.T p.T) =
        𝟙 (cfpProd p.T p.T) from
        (cfpLift_uniq _ _ _
          (Category.id_comp _)
          (Category.id_comp _)).symm,
      Category.id_comp]
  simp only [Category.assoc, natSucc_cancel]

end GebLean
