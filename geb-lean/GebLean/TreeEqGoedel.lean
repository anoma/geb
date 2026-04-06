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

/-- Cantor pairing injectivity under `natEq`:
`natEq(cantorPair(a,b), cantorPair(c,d)) =
  boolAnd(natEq(a,c), natEq(b,d))`.
This is the equational form of the statement that
`cantorPair` reflects equality via `natEq`. -/
def NatEqCantorPair
    (C : Type u) [Category.{v} C]
    [HasChosenFiniteProducts C]
    [HasPBTO C] : Prop :=
  cfpMap cantorPair cantorPair ≫ natEq =
  cfpLift
    (cfpLift
      (cfpFst (cfpProd p.T p.T)
        (cfpProd p.T p.T) ≫
        cfpFst p.T p.T)
      (cfpSnd (cfpProd p.T p.T)
        (cfpProd p.T p.T) ≫
        cfpFst p.T p.T) ≫
      natEq)
    (cfpLift
      (cfpFst (cfpProd p.T p.T)
        (cfpProd p.T p.T) ≫
        cfpSnd p.T p.T)
      (cfpSnd (cfpProd p.T p.T)
        (cfpProd p.T p.T) ≫
        cfpSnd p.T p.T) ≫
      natEq) ≫
    (boolAnd : cfpProd p.T p.T ⟶ p.T)

/-- Branch-branch computation rule for `treeEqG`:
`treeEqG(β(a₁,a₂), β(b₁,b₂)) =
  boolAnd(treeEqG(a₁,b₁), treeEqG(a₂,b₂))`.
Depends on `NatEqCantorPair C`. -/
theorem treeEqG_ββ
    (hCP : NatEqCantorPair (p := p) C) :
    cfpMap p.β p.β ≫ treeEqG =
    cfpLift
      (cfpLift
        (cfpFst (cfpProd p.T p.T)
          (cfpProd p.T p.T) ≫
          cfpFst p.T p.T)
        (cfpSnd (cfpProd p.T p.T)
          (cfpProd p.T p.T) ≫
          cfpFst p.T p.T) ≫
        treeEqG)
      (cfpLift
        (cfpFst (cfpProd p.T p.T)
          (cfpProd p.T p.T) ≫
          cfpSnd p.T p.T)
        (cfpSnd (cfpProd p.T p.T)
          (cfpProd p.T p.T) ≫
          cfpSnd p.T p.T) ≫
        treeEqG) ≫
      boolAnd := by
  rw [treeEqG_ββ_reduce,
    show cfpMap
      (cfpMap treeToNat treeToNat ≫ cantorPair)
      (cfpMap treeToNat treeToNat ≫ cantorPair) =
    cfpMap
      (cfpMap treeToNat treeToNat)
      (cfpMap treeToNat treeToNat) ≫
    cfpMap cantorPair cantorPair from
      (cfpMap_comp
        (cfpMap treeToNat treeToNat)
        (cfpMap treeToNat treeToNat)
        cantorPair cantorPair).symm,
    Category.assoc, hCP,
    ← Category.assoc]
  congr 1
  have precomp_lift :
      cfpMap
        (cfpMap (C := C) treeToNat treeToNat)
        (cfpMap treeToNat treeToNat) ≫
      cfpLift
        (cfpLift
          (cfpFst (cfpProd p.T p.T)
            (cfpProd p.T p.T) ≫
            cfpFst p.T p.T)
          (cfpSnd (cfpProd p.T p.T)
            (cfpProd p.T p.T) ≫
            cfpFst p.T p.T) ≫
          natEq)
        (cfpLift
          (cfpFst (cfpProd p.T p.T)
            (cfpProd p.T p.T) ≫
            cfpSnd p.T p.T)
          (cfpSnd (cfpProd p.T p.T)
            (cfpProd p.T p.T) ≫
            cfpSnd p.T p.T) ≫
          natEq) =
      cfpLift
        (cfpLift
          (cfpFst (cfpProd p.T p.T)
            (cfpProd p.T p.T) ≫
            cfpFst p.T p.T)
          (cfpSnd (cfpProd p.T p.T)
            (cfpProd p.T p.T) ≫
            cfpFst p.T p.T) ≫
          treeEqG)
        (cfpLift
          (cfpFst (cfpProd p.T p.T)
            (cfpProd p.T p.T) ≫
            cfpSnd p.T p.T)
          (cfpSnd (cfpProd p.T p.T)
            (cfpProd p.T p.T) ≫
            cfpSnd p.T p.T) ≫
          treeEqG) := by
    rw [cfpLift_precomp]
    have lift_eq
        (inner : cfpProd p.T p.T ⟶ p.T)
        (hinner :
          cfpMap treeToNat treeToNat ≫
            inner = inner ≫ treeToNat) :
        cfpMap
          (cfpMap treeToNat treeToNat)
          (cfpMap treeToNat treeToNat) ≫
        cfpLift
          (cfpFst (cfpProd p.T p.T)
            (cfpProd p.T p.T) ≫ inner)
          (cfpSnd (cfpProd p.T p.T)
            (cfpProd p.T p.T) ≫ inner) ≫
        natEq =
        cfpLift
          (cfpFst (cfpProd p.T p.T)
            (cfpProd p.T p.T) ≫ inner)
          (cfpSnd (cfpProd p.T p.T)
            (cfpProd p.T p.T) ≫ inner) ≫
        treeEqG := by
      have M_fst_inner :
          cfpMap
            (cfpMap treeToNat treeToNat)
            (cfpMap treeToNat treeToNat) ≫
            cfpFst (cfpProd p.T p.T)
              (cfpProd p.T p.T) ≫ inner =
          cfpFst (cfpProd p.T p.T)
            (cfpProd p.T p.T) ≫
            inner ≫ treeToNat := by
        rw [← Category.assoc, cfpMap_fst,
          Category.assoc, hinner]
      have M_snd_inner :
          cfpMap
            (cfpMap treeToNat treeToNat)
            (cfpMap treeToNat treeToNat) ≫
            cfpSnd (cfpProd p.T p.T)
              (cfpProd p.T p.T) ≫ inner =
          cfpSnd (cfpProd p.T p.T)
            (cfpProd p.T p.T) ≫
            inner ≫ treeToNat := by
        rw [← Category.assoc, cfpMap_snd,
          Category.assoc, hinner]
      have factor :
          cfpMap
            (cfpMap treeToNat treeToNat)
            (cfpMap treeToNat treeToNat) ≫
          cfpLift
            (cfpFst (cfpProd p.T p.T)
              (cfpProd p.T p.T) ≫ inner)
            (cfpSnd (cfpProd p.T p.T)
              (cfpProd p.T p.T) ≫ inner) =
          cfpLift
            (cfpFst (cfpProd p.T p.T)
              (cfpProd p.T p.T) ≫ inner)
            (cfpSnd (cfpProd p.T p.T)
              (cfpProd p.T p.T) ≫ inner) ≫
            cfpMap treeToNat treeToNat := by
        rw [cfpLift_precomp,
          M_fst_inner, M_snd_inner]
        simp only [Category.assoc,
          cfpLift_cfpMap]
      rw [← Category.assoc, factor,
        Category.assoc]
      rfl
    congr 1
    · exact lift_eq (cfpFst p.T p.T)
        (cfpMap_fst treeToNat treeToNat)
    · exact lift_eq (cfpSnd p.T p.T)
        (cfpMap_snd treeToNat treeToNat)
  exact precomp_lift

end GebLean
