import GebLean.LawvereBTInterp
import GebLean.TreePERLimits
import GebLean.TreePERColimits

/-!
# Converse transitivity for LawvereBTQuotCat

Proves that in `LawvereBTQuotCat`, quantified
(Prop-valued) transitivity of a relation implies
equational (`boolAnd`-based) transitivity.  This
is the converse of `eqTransitive_implies_quant`,
specialized to `LawvereBTQuotCat`.

The proof uses `lawvereBTQuotCat_isSeparator` to
reduce the morphism equation to global elements,
then performs a case split on Boolean-valued global
elements (which are either `ℓ` or `treeFalse` in
`LawvereBTQuotCat`).
-/

namespace GebLean

open CategoryTheory

/-! ## Global element case split in
LawvereBTQuotCat -/

/-- A Boolean-valued global element of T in
`LawvereBTQuotCat` is either `ℓ` or `treeFalse`.

The proof goes through the interpretation: a
Boolean BT tree (fixed by `isLeafEndo`) is
either `BT.leaf` or `BT.node BT.leaf BT.leaf`,
which lift back via completeness. -/
theorem lawvereBT_bool_dichotomy
    (e : (0 : LawvereBTQuotCat) ⟶
      HasPBTO.T (C := LawvereBTQuotCat))
    (he : e ≫ isLeafEndo = e) :
    e = HasPBTO.ℓ ∨
    e = treeFalse (C := LawvereBTQuotCat) := by
  -- Extract the BT value via interpretation.
  let ctx₀ : Fin 0 → BT.{0} := Fin.elim0
  let j₀ : Fin 1 := ⟨0, Nat.zero_lt_one⟩
  let a : BT.{0} :=
    BTMorNQuo.interpU e ctx₀ j₀
  -- Helper: two morphisms 0 ⟶ 1 in
  -- LawvereBTQuotCat are equal iff their
  -- single BT values agree.
  have mor_eq_of_bt_eq :
      ∀ (f g : (0 : LawvereBTQuotCat) ⟶ 1),
      BTMorNQuo.interpU f ctx₀ j₀ =
        BTMorNQuo.interpU g ctx₀ j₀ →
      f = g := by
    intro f g hfg
    have hinj :=
      @Functor.Faithful.map_injective
        _ _ _ _
        interpFunctor.{0} _ 0 1 f g
    apply hinj
    funext ctx j
    have hctx : ctx = ctx₀ :=
      funext (fun i => Fin.elim0 i)
    subst hctx
    have hj : j = j₀ :=
      Fin.ext (Nat.lt_one_iff.mp j.isLt)
    subst hj
    exact hfg
  -- Case-split on the BT tree.
  rcases BT.leaf_or_node a with ha | ⟨l, r, ha⟩
  · -- Case a = BT.leaf: e = ℓ.
    left
    apply mor_eq_of_bt_eq
    change a = _
    rw [ha]
    -- interpU(ℓ) at ctx₀ j₀ = BT.leaf.
    -- HasPBTO.ℓ = btLeafQ = ⟦btLeaf⟧.
    -- BTMorN.interpU btLeaf ctx₀ j₀ =
    -- BTMor1.leaf.interpU ctx₀ = BT.leaf.
    change BT.leaf = BTMorNQuo.interpU
      btLeafQ ctx₀ j₀
    unfold btLeafQ BTMorNQuo.interpU
    simp only [Quotient.lift_mk]
    unfold BTMorN.interpU btLeaf
    exact (BTMor1.interpU_leaf ctx₀).symm
  · -- Case a = BT.node l r: e = treeFalse.
    right
    let e₁ : (0 : LawvereBTQuotCat) ⟶ 1 :=
      Quotient.mk (btMorNSetoid 0 1)
        (fun (_ : Fin 1) => quoteBT l)
    let e₂ : (0 : LawvereBTQuotCat) ⟶ 1 :=
      Quotient.mk (btMorNSetoid 0 1)
        (fun (_ : Fin 1) => quoteBT r)
    have he₁_interp :
        BTMorNQuo.interpU e₁ ctx₀ j₀ = l := by
      change (quoteBT l).interpU Fin.elim0 = l
      exact quoteBT_interpU l Fin.elim0
    have he₂_interp :
        BTMorNQuo.interpU e₂ ctx₀ j₀ = r := by
      change (quoteBT r).interpU Fin.elim0 = r
      exact quoteBT_interpU r Fin.elim0
    have he_branch :
        e = cfpLift e₁ e₂ ≫ HasPBTO.β := by
      apply mor_eq_of_bt_eq
      change a = _
      rw [ha]
      change BT.node l r =
        BTMorNQuo.interpU
          (BTMorNQuo.comp
            (BTMorNQuo.pair e₁ e₂)
            btBranchQ) ctx₀ j₀
      rw [BTMorNQuo.interpU_comp]
      have h0 : BTMorNQuo.interpU
          (BTMorNQuo.pair e₁ e₂) ctx₀
          ⟨0, by omega⟩ = l := by
        have hc := BTMorNQuo.interpU_comp
          (BTMorNQuo.pair e₁ e₂)
          BTMorNQuo.fst ctx₀
        rw [BTMorNQuo.pair_fst] at hc
        exact congrFun hc j₀ ▸ he₁_interp
      have h1 : BTMorNQuo.interpU
          (BTMorNQuo.pair e₁ e₂) ctx₀
          ⟨1, by omega⟩ = r := by
        have hc := BTMorNQuo.interpU_comp
          (BTMorNQuo.pair e₁ e₂)
          BTMorNQuo.snd ctx₀
        rw [BTMorNQuo.pair_snd] at hc
        exact congrFun hc j₀ ▸ he₂_interp
      change BT.node l r = _
      unfold btBranchQ BTMorNQuo.interpU
      simp only [Quotient.lift_mk]
      unfold BTMorN.interpU btBranch
      rw [BTMor1.interpU_branch,
        BTMor1.interpU_proj,
        BTMor1.interpU_proj]
      exact congrArg₂ BT.node h0.symm h1.symm
    have hterm :
        cfpLift e₁ e₂ ≫
          cfpTerminalFrom
            (cfpProd HasPBTO.T HasPBTO.T) =
        cfpTerminalFrom
          (0 : LawvereBTQuotCat) :=
      (HasChosenFiniteProducts.mk
        lawvereBTQuotTerminal
        lawvereBTQuotProduct).terminal.uniq _
    calc e
        = (cfpLift e₁ e₂ ≫ HasPBTO.β) ≫
            isLeafEndo := by
          rw [← he_branch]; exact he.symm
      _ = cfpLift e₁ e₂ ≫
            (HasPBTO.β ≫ isLeafEndo) :=
          Category.assoc _ _ _
      _ = cfpLift e₁ e₂ ≫
            (cfpTerminalFrom
              (cfpProd HasPBTO.T HasPBTO.T) ≫
              treeFalse) := by
          rw [isLeafEndo_β]
      _ = (cfpLift e₁ e₂ ≫
            cfpTerminalFrom
              (cfpProd HasPBTO.T HasPBTO.T)) ≫
            treeFalse :=
          (Category.assoc _ _ _).symm
      _ = cfpTerminalFrom 0 ≫ treeFalse := by
          rw [hterm]
      _ = treeFalse := rfl

/-- `LawvereBTQuotCat` satisfies `HasBoolDichotomy`:
every Boolean global element is `ℓ` or
`treeFalse`. -/
theorem lawvereBTQuotCat_hasBoolDichotomy :
    HasBoolDichotomy LawvereBTQuotCat :=
  lawvereBT_bool_dichotomy

/-- Every global element of `T` in
`LawvereBTQuotCat` is either `HasPBTO.ℓ` or a
branch `cfpLift el er ≫ HasPBTO.β`.  The proof
extracts the underlying `BT` value via
`BTMorNQuo.interpU` and applies `BT.leaf_or_node`;
in the node case, the quoted children supply the
existential witnesses. -/
theorem lawvereBT_tree_dichotomy
    (e : (0 : LawvereBTQuotCat) ⟶
      HasPBTO.T (C := LawvereBTQuotCat)) :
    e = HasPBTO.ℓ ∨
    ∃ (el er : (0 : LawvereBTQuotCat) ⟶
      HasPBTO.T (C := LawvereBTQuotCat)),
      e = cfpLift el er ≫ HasPBTO.β := by
  let ctx₀ : Fin 0 → BT.{0} := Fin.elim0
  let j₀ : Fin 1 := ⟨0, Nat.zero_lt_one⟩
  let a : BT.{0} :=
    BTMorNQuo.interpU e ctx₀ j₀
  have mor_eq_of_bt_eq :
      ∀ (f g : (0 : LawvereBTQuotCat) ⟶ 1),
      BTMorNQuo.interpU f ctx₀ j₀ =
        BTMorNQuo.interpU g ctx₀ j₀ →
      f = g := by
    intro f g hfg
    have hinj :=
      @Functor.Faithful.map_injective
        _ _ _ _
        interpFunctor.{0} _ 0 1 f g
    apply hinj
    funext ctx j
    have hctx : ctx = ctx₀ :=
      funext (fun i => Fin.elim0 i)
    subst hctx
    have hj : j = j₀ :=
      Fin.ext (Nat.lt_one_iff.mp j.isLt)
    subst hj
    exact hfg
  rcases BT.leaf_or_node a with ha | ⟨l, r, ha⟩
  · left
    apply mor_eq_of_bt_eq
    change a = _
    rw [ha]
    change BT.leaf = BTMorNQuo.interpU
      btLeafQ ctx₀ j₀
    unfold btLeafQ BTMorNQuo.interpU
    simp only [Quotient.lift_mk]
    unfold BTMorN.interpU btLeaf
    exact (BTMor1.interpU_leaf ctx₀).symm
  · right
    let e₁ : (0 : LawvereBTQuotCat) ⟶ 1 :=
      Quotient.mk (btMorNSetoid 0 1)
        (fun (_ : Fin 1) => quoteBT l)
    let e₂ : (0 : LawvereBTQuotCat) ⟶ 1 :=
      Quotient.mk (btMorNSetoid 0 1)
        (fun (_ : Fin 1) => quoteBT r)
    refine ⟨e₁, e₂, ?_⟩
    have he₁_interp :
        BTMorNQuo.interpU e₁ ctx₀ j₀ = l := by
      change (quoteBT l).interpU Fin.elim0 = l
      exact quoteBT_interpU l Fin.elim0
    have he₂_interp :
        BTMorNQuo.interpU e₂ ctx₀ j₀ = r := by
      change (quoteBT r).interpU Fin.elim0 = r
      exact quoteBT_interpU r Fin.elim0
    apply mor_eq_of_bt_eq
    change a = _
    rw [ha]
    change BT.node l r =
      BTMorNQuo.interpU
        (BTMorNQuo.comp
          (BTMorNQuo.pair e₁ e₂)
          btBranchQ) ctx₀ j₀
    rw [BTMorNQuo.interpU_comp]
    have h0 : BTMorNQuo.interpU
        (BTMorNQuo.pair e₁ e₂) ctx₀
        ⟨0, by omega⟩ = l := by
      have hc := BTMorNQuo.interpU_comp
        (BTMorNQuo.pair e₁ e₂)
        BTMorNQuo.fst ctx₀
      rw [BTMorNQuo.pair_fst] at hc
      exact congrFun hc j₀ ▸ he₁_interp
    have h1 : BTMorNQuo.interpU
        (BTMorNQuo.pair e₁ e₂) ctx₀
        ⟨1, by omega⟩ = r := by
      have hc := BTMorNQuo.interpU_comp
        (BTMorNQuo.pair e₁ e₂)
        BTMorNQuo.snd ctx₀
      rw [BTMorNQuo.pair_snd] at hc
      exact congrFun hc j₀ ▸ he₂_interp
    change BT.node l r = _
    unfold btBranchQ BTMorNQuo.interpU
    simp only [Quotient.lift_mk]
    unfold BTMorN.interpU btBranch
    rw [BTMor1.interpU_branch,
      BTMor1.interpU_proj,
      BTMor1.interpU_proj]
    exact congrArg₂ BT.node h0.symm h1.symm

/-! ## Main theorem -/

/-- In LawvereBTQuotCat, `cfpTerminalFrom 0` is
the identity. -/
private theorem cfpTerminalFrom_zero :
    cfpTerminalFrom (0 : LawvereBTQuotCat) =
    𝟙 (0 : LawvereBTQuotCat) :=
  cfpTerminalFrom_terminal

set_option backward.isDefEq.respectTransparency false in
/-- `IsLeafConst f` for `f : 0 ⟶ T` in
LawvereBTQuotCat simplifies to `f = ℓ`. -/
private theorem isLeafConst_zero_eq_ℓ
    {f : (0 : LawvereBTQuotCat) ⟶
      HasPBTO.T (C := LawvereBTQuotCat)} :
    IsLeafConst f ↔
    f = HasPBTO.ℓ
      (C := LawvereBTQuotCat) := by
  unfold IsLeafConst
  constructor
  · intro h
    rw [cfpTerminalFrom_zero,
      Category.id_comp] at h
    exact h
  · intro h
    rw [cfpTerminalFrom_zero, Category.id_comp]
    exact h

set_option backward.isDefEq.respectTransparency false in
/-- `treeFalse` in LawvereBTQuotCat equals
`cfpTerminalFrom 0 ≫ treeFalse`. -/
private theorem treeFalse_eq_terminal_treeFalse :
    treeFalse (C := LawvereBTQuotCat) =
    cfpTerminalFrom (0 : LawvereBTQuotCat) ≫
      treeFalse := by
  rw [cfpTerminalFrom_zero, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
/-- In `LawvereBTQuotCat`, quantified transitivity
implies equational transitivity.  This is the
converse of `eqTransitive_implies_quant`,
specialized to `LawvereBTQuotCat`. -/
theorem quantTransitive_implies_eq_lawvereBT
    (rel : cfpProd
      (HasPBTO.T (C := LawvereBTQuotCat))
      (HasPBTO.T (C := LawvereBTQuotCat)) ⟶
      HasPBTO.T (C := LawvereBTQuotCat))
    (rel_bool : rel ≫ isLeafEndo = rel)
    (ht : QuantTransitive rel) :
    EqTransitive rel := by
  unfold EqTransitive
  -- Reduce to global elements via separator.
  apply lawvereBTQuotCat_isSeparator.def
  intro e
  -- Set abbreviations.
  set A := e ≫ (cfpLift
    (cfpLift t3x t3z ≫ rel)
    (cfpLift t3z t3y ≫ rel) ≫ boolAnd)
  set B := e ≫ (cfpLift t3x t3y ≫ rel)
  have goal_eq : e ≫
      cfpLift
        (cfpLift (cfpLift t3x t3z ≫ rel)
          (cfpLift t3z t3y ≫ rel) ≫ boolAnd)
        (cfpLift t3x t3y ≫ rel) ≫ boolAnd =
      cfpLift A B ≫ boolAnd := by
    rw [← Category.assoc, cfpLift_precomp e]
  rw [goal_eq]
  have hA_bool : A ≫ isLeafEndo = A := by
    change (e ≫ (cfpLift
      (cfpLift t3x t3z ≫ rel)
      (cfpLift t3z t3y ≫ rel) ≫ boolAnd)) ≫
      isLeafEndo = _
    rw [Category.assoc, Category.assoc,
      boolAnd_output_boolean]
  set rxz := e ≫ cfpLift t3x t3z ≫ rel
  set rzy := e ≫ cfpLift t3z t3y ≫ rel
  have hA_eq : A = cfpLift rxz rzy ≫ boolAnd := by
    change e ≫ cfpLift
      (cfpLift t3x t3z ≫ rel)
      (cfpLift t3z t3y ≫ rel) ≫ boolAnd =
      cfpLift rxz rzy ≫ boolAnd
    rw [← Category.assoc, cfpLift_precomp e]
  have hrxz_bool : rxz ≫ isLeafEndo = rxz := by
    change (e ≫ cfpLift t3x t3z ≫ rel) ≫
      isLeafEndo = _
    rw [Category.assoc, Category.assoc, rel_bool]
  have hrzy_bool : rzy ≫ isLeafEndo = rzy := by
    change (e ≫ cfpLift t3z t3y ≫ rel) ≫
      isLeafEndo = _
    rw [Category.assoc, Category.assoc, rel_bool]
  rcases lawvereBT_bool_dichotomy rxz
    hrxz_bool with hrxz | hrxz
  · -- rxz = ℓ.  Case split on rzy.
    rcases lawvereBT_bool_dichotomy rzy
      hrzy_bool with hrzy | hrzy
    · -- rxz = ℓ, rzy = ℓ.
      have hA_eq_ℓ : A = HasPBTO.ℓ := by
        rw [hA_eq, hrxz, hrzy, boolAnd_ℓ_ℓ]
      have hB_lc : IsLeafConst B := by
        have h1 : IsLeafConst rxz :=
          isLeafConst_zero_eq_ℓ.mpr hrxz
        have h2 : IsLeafConst rzy :=
          isLeafConst_zero_eq_ℓ.mpr hrzy
        exact ht e h1 h2
      have hB_eq_ℓ : B = HasPBTO.ℓ :=
        isLeafConst_zero_eq_ℓ.mp hB_lc
      rw [hA_eq_ℓ, hB_eq_ℓ, boolAnd_ℓ_ℓ]
    · -- rxz = ℓ, rzy = treeFalse.
      have boolAnd_ℓ_tf :
          cfpLift
            (HasPBTO.ℓ
              (C := LawvereBTQuotCat))
            (treeFalse
              (C := LawvereBTQuotCat)) ≫
            boolAnd =
          treeFalse := by
        rw [boolAnd_treeIte_form,
          @isLeafEndo_treeFalse
            LawvereBTQuotCat _ _ _]
        have : cfpTerminalFrom
            (cfpTerminal
              (C := LawvereBTQuotCat)) ≫
            treeFalse =
          treeFalse := by
          rw [cfpTerminalFrom_terminal,
            Category.id_comp]
        rw [this]
        exact treeIte_equal_branches
          treeFalse HasPBTO.ℓ
      have hA_eq_tf : A = treeFalse := by
        rw [hA_eq, hrxz, hrzy, boolAnd_ℓ_tf]
      rw [hA_eq_tf,
        treeFalse_eq_terminal_treeFalse,
        boolAnd_treeFalse_left]
  · -- rxz = treeFalse.
    have hA_eq_tf : A = treeFalse := by
      rw [hA_eq, hrxz,
        treeFalse_eq_terminal_treeFalse,
        boolAnd_treeFalse_left]
    rw [hA_eq_tf,
      treeFalse_eq_terminal_treeFalse,
      boolAnd_treeFalse_left]

/-! ## The Lawvere BT PER category -/

/-- Objects of the PER category over
`LawvereBTQuotCat`: partial equivalence relations on
the binary tree object `T` with Boolean-valued output.
This is the "decidable layer" of the PER completion,
interpreted as the category of types with primitive
recursively decidable equality. -/
abbrev LawvereBTPER :=
  @TreePERObj LawvereBTQuotCat _ _ _

/-- The PER category over `LawvereBTQuotCat` has
all finite limits. -/
theorem
    lawvereBTPER_hasFiniteLimits :
    Limits.HasFiniteLimits LawvereBTPER :=
  treePER_hasFiniteLimits
    lawvereBTQuotCat_isSeparator
    lawvereBTQuotCat_hasBoolDichotomy

/-- The PER category over `LawvereBTQuotCat` has
all finite coproducts. -/
theorem
    lawvereBTPER_hasFiniteCoproducts :
    Limits.HasFiniteCoproducts LawvereBTPER :=
  treePER_hasFiniteCoproducts
    lawvereBTQuotCat_isSeparator
    lawvereBTQuotCat_hasBoolDichotomy

end GebLean
