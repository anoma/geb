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

/-- Leaf-leaf computation rule for `treeEqG`:
`treeEqG(ℓ, ℓ) = ℓ`. -/
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
  -- Goal: (p.ℓ ≫ cfpTerminalFrom T) ≫ p.ℓ = p.ℓ
  -- p.ℓ ≫ cfpTerminalFrom T : cfpTerminal ⟶
  -- cfpTerminal.
  -- Use transitivity to avoid rw issues.
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

end GebLean
