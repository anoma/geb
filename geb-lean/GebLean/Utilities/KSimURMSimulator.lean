import GebLean.Utilities.ZeroTestURM
import GebLean.Utilities.KArith
import GebLean.LawvereKSim
import GebLean.LawvereKSimInterp

/-!
# K^sim simulator for the zero-test URM kernel

For every `URMProgram a` (T1 + T2's `URMProgram` family at
`GebLean/Utilities/ZeroTestURM.lean:122`), this module builds a
single-output K^sim morphism `simulate : URMProgram a →
KMor1 (a + 1)` whose interpretation at `(y, v)` equals the value
of the output register after `y` steps from `URMState.init P v`.
The simulator is a `KMor1.simrec` (`LawvereKSim.lean:50`) with
system size `P.numRegs + 1`: components `0, …, numRegs - 1`
track register values; component `numRegs` (the last) tracks the
PC. Output index is `P.outputReg.castSucc`. The simulator is at
K^sim level ≤ 2 (base sup 0, step sup ≤ 1, simrec adds 1).

## Main definitions

- `KMor1.pcDispatch`: a non-substituting bottom-up `cond`-chain
  combinator reading the last context slot (the PC) and
  selecting branches keyed to specific PC values.
- `baseFamily`: the simrec's base family at the initial state.
- `stepFamily`: the simrec's step family at one URM step.
- `simulate`: the public-facing simulator term.

## Main statements

- `KMor1.interp_pcDispatch_match`, `KMor1.interp_pcDispatch_default`:
  the dispatcher's interpretation simp lemmas.
- `KMor1.pcDispatch_level`: the dispatcher's level bound (1 when
  branches and default are level ≤ 1).
- `simulate_interp`: the simulator's output equals
  `URMState.runFor`'s output projected at `outputReg`.
- `simulate_level`: the simulator is at K^sim level ≤ 2.

## Implementation notes

The bottom-up `cond`-chain reads
`pred^k(PC) = 0 ⇔ PC ≤ k` (Tourlakis § 0.1.0.20 chained with
§ 0.1.0.8); the nested fall-through structure converts the
inequality into the equality `PC = k` at each level. The
recursive case does *not* substitute the PC slot via
`KMor1.comp _ shift` — branches and default sit at the same
context as their siblings, so the interp simp lemmas hold
verbatim without context-substitution corrections.

## References

- Tourlakis 2018 `PR-complexity-topics.pdf` § 0.1.0.37
  (simulation lemma).
- `docs/superpowers/specs/2026-05-21-step-t3-urm-to-ksim-simulator-design.md`
  § 3 (architecture), § 4 (correctness), § 5 (level).

## Tags

URM, K^sim, simulator, simrec, Tourlakis
-/

namespace GebLean

/-- The `k`-fold composition of `KMor1.pred` over the last
context slot, `KMor1.proj (Fin.last n)`. Level 0 for `k = 0`,
level 1 for `k ≥ 1`. Used inside `KMor1.pcDispatch`'s `cond`
chain as the level-1 inequality test `predIter k = 0 ⇔ PC ≤ k`
(Tourlakis § 0.1.0.20 chained with § 0.1.0.8). -/
private def KMor1.predIter (n k : ℕ) : KMor1 (n + 1) :=
  match k with
  | 0     => KMor1.proj (Fin.last n)
  | k + 1 =>
    KMor1.comp KMor1.pred
      (fun _ : Fin 1 => KMor1.predIter n k)

/-- `KMor1.predIter n k` interprets as `k`-fold `Nat.pred` over
the last context slot, equivalent to `ctx (Fin.last n) - k`
(truncated subtraction on `ℕ`). -/
@[simp] theorem KMor1.interp_predIter
    (n k : ℕ) (ctx : Fin (n + 1) → ℕ) :
    (KMor1.predIter n k).interp ctx = ctx (Fin.last n) - k := by
  induction k with
  | zero =>
    simp only [KMor1.predIter, KMor1.interp_proj, Nat.sub_zero]
  | succ k ih =>
    simp only [KMor1.predIter, KMor1.interp_comp,
      KMor1.interp_pred]
    rw [ih, Nat.pred_eq_sub_one]
    omega

/-- `KMor1.predIter n k` has level ≤ 1 for every `n` and `k`
(level 0 when `k = 0`, level 1 when `k ≥ 1`). -/
theorem KMor1.predIter_level (n k : ℕ) :
    (KMor1.predIter n k).level ≤ 1 := by
  induction k with
  | zero =>
    change KMor1.level (KMor1.proj (Fin.last n)) ≤ 1
    unfold KMor1.level
    omega
  | succ k ih =>
    change KMor1.level
        (KMor1.comp KMor1.pred (fun _ : Fin 1 => KMor1.predIter n k))
        ≤ 1
    unfold KMor1.level
    have hsup :
        Fin.maxOfNat 1
          (fun _ : Fin 1 => (KMor1.predIter n k).level) ≤ 1 :=
      Fin.maxOfNat_le (by intro _; exact ih)
    have hpred : KMor1.level (KMor1.pred : KMor1 1) = 1 := rfl
    simp only []
    omega

/-- Auxiliary continuation for `KMor1.pcDispatch`: at offset
`k`, test `KMor1.predIter n k = 0 ⇔ PC ≤ k`, select
`branches ⟨0, _⟩` if so, else recurse at offset `k + 1` over
`branches ∘ Fin.succ`. The recursive call sits at the *same*
context as the surrounding `cond`; branches and default are
never wrapped in a context-substituting `KMor1.comp`. -/
private def KMor1.pcDispatchFrom {n : ℕ}
    (k size : ℕ)
    (branches : Fin size → KMor1 (n + 1))
    (default : KMor1 (n + 1)) :
    KMor1 (n + 1) :=
  match size with
  | 0 => default
  | size' + 1 =>
    KMor1.comp KMor1.cond
      (fun i : Fin 3 => match i with
        | ⟨0, _⟩ => KMor1.predIter n k
        | ⟨1, _⟩ => branches ⟨0, by omega⟩
        | ⟨2, _⟩ =>
          KMor1.pcDispatchFrom (k + 1) size'
            (fun j : Fin size' => branches j.succ) default)

/-- The PC-dispatch combinator: given `size` branches keyed to
specific PC values (the last context slot) and a `default` for
PC values `≥ size`, return a `KMor1 (n + 1)` that interprets to
`branches k` when PC = `k` (`k < size`), else `default`.

Implementation defers to `KMor1.pcDispatchFrom 0 size`. -/
def KMor1.pcDispatch {n : ℕ} (size : ℕ)
    (branches : Fin size → KMor1 (n + 1))
    (default : KMor1 (n + 1)) :
    KMor1 (n + 1) :=
  KMor1.pcDispatchFrom 0 size branches default

private theorem KMor1.interp_pcDispatchFrom_match
    {n : ℕ} (size : ℕ) (k : ℕ)
    (branches : Fin size → KMor1 (n + 1))
    (default : KMor1 (n + 1)) (ctx : Fin (n + 1) → ℕ)
    (j : Fin size) (h : ctx (Fin.last n) = k + j.val) :
    (KMor1.pcDispatchFrom k size branches default).interp ctx
      = (branches j).interp ctx := by
  induction size generalizing k with
  | zero => exact Fin.elim0 j
  | succ size' ih =>
    simp only [KMor1.pcDispatchFrom, KMor1.interp_comp,
      KMor1.interp_cond, KMor1.interp_predIter]
    by_cases hj : j = ⟨0, by omega⟩
    · rw [hj]
      have hsub0 : ctx (Fin.last n) - k = 0 := by
        rw [h, hj]; simp
      rw [hsub0]; simp
    · have hjpos : 0 < j.val := by
        rcases j with ⟨v, hv⟩
        rcases v with _ | v'
        · exact absurd (Fin.ext rfl : (⟨0, by omega⟩ : Fin (size' + 1)) = ⟨0, hv⟩) hj
        · simp
      have hsub : ctx (Fin.last n) - k ≠ 0 := by
        rw [h]; omega
      rw [if_neg hsub]
      have hpred : ctx (Fin.last n) = (k + 1) + (j.val - 1) := by
        rw [h]; omega
      have ih_applied :=
        ih (k + 1) (fun j' : Fin size' => branches j'.succ)
          ⟨j.val - 1, by omega⟩ hpred
      rw [ih_applied]
      change (branches _).interp ctx = (branches _).interp ctx
      congr 2
      apply Fin.ext
      simp [Fin.succ]
      omega

private theorem KMor1.interp_pcDispatchFrom_default
    {n : ℕ} (size : ℕ) (k : ℕ)
    (branches : Fin size → KMor1 (n + 1))
    (default : KMor1 (n + 1)) (ctx : Fin (n + 1) → ℕ)
    (h : ctx (Fin.last n) ≥ k + size) :
    (KMor1.pcDispatchFrom k size branches default).interp ctx
      = default.interp ctx := by
  induction size generalizing k with
  | zero => simp [KMor1.pcDispatchFrom]
  | succ size' ih =>
    simp only [KMor1.pcDispatchFrom, KMor1.interp_comp,
      KMor1.interp_cond, KMor1.interp_predIter]
    have hsub : ctx (Fin.last n) - k ≠ 0 := by omega
    rw [if_neg hsub]
    apply ih
    omega

/-- When the PC slot equals `k.val` for some `k : Fin size`,
`KMor1.pcDispatch` interprets as `branches k`. Not a `simp`
lemma: `simp` cannot infer `k` from the LHS, since `k` appears
only in the hypothesis and conclusion. Invoked explicitly via
`rw`. -/
theorem KMor1.interp_pcDispatch_match
    {n : ℕ} (size : ℕ)
    (branches : Fin size → KMor1 (n + 1))
    (default : KMor1 (n + 1)) (ctx : Fin (n + 1) → ℕ)
    (k : Fin size) (h : ctx (Fin.last n) = k.val) :
    (KMor1.pcDispatch size branches default).interp ctx
      = (branches k).interp ctx := by
  unfold KMor1.pcDispatch
  exact KMor1.interp_pcDispatchFrom_match size 0 branches default
    ctx k (by rw [h]; omega)

/-- When the PC slot is ≥ `size`, `KMor1.pcDispatch` interprets
as `default`. -/
@[simp] theorem KMor1.interp_pcDispatch_default
    {n : ℕ} (size : ℕ)
    (branches : Fin size → KMor1 (n + 1))
    (default : KMor1 (n + 1)) (ctx : Fin (n + 1) → ℕ)
    (h : ctx (Fin.last n) ≥ size) :
    (KMor1.pcDispatch size branches default).interp ctx
      = default.interp ctx := by
  unfold KMor1.pcDispatch
  exact KMor1.interp_pcDispatchFrom_default size 0 branches default
    ctx (by omega)

/-- Inner level lemma for `pcDispatchFrom`: when branches and
default are level ≤ 1, the dispatcher is level ≤ 1. By
induction on `size` with `k` and `branches` generalised. -/
private theorem KMor1.pcDispatchFrom_level
    {n : ℕ} (size : ℕ) (k : ℕ)
    (branches : Fin size → KMor1 (n + 1))
    (default : KMor1 (n + 1))
    (h_branches : ∀ j, (branches j).level ≤ 1)
    (h_default : default.level ≤ 1) :
    (KMor1.pcDispatchFrom k size branches default).level ≤ 1 := by
  induction size generalizing k with
  | zero =>
    change (default).level ≤ 1
    exact h_default
  | succ size' ih =>
    have hpred : (KMor1.predIter n k).level ≤ 1 :=
      KMor1.predIter_level n k
    have hb0 : (branches ⟨0, by omega⟩).level ≤ 1 :=
      h_branches _
    have hrecur : (KMor1.pcDispatchFrom (k + 1) size'
        (fun j : Fin size' => branches j.succ) default).level ≤ 1 :=
      ih (k + 1) (fun j => branches j.succ)
        (fun j => h_branches j.succ)
    change max (KMor1.cond.level)
           (Fin.maxOfNat 3 (fun i : Fin 3 =>
             match i with
             | ⟨0, _⟩ => (KMor1.predIter n k).level
             | ⟨1, _⟩ => (branches ⟨0, by omega⟩).level
             | ⟨2, _⟩ => (KMor1.pcDispatchFrom (k + 1) size'
                 (fun j : Fin size' => branches j.succ) default).level))
           ≤ 1
    have hcond_level : (KMor1.cond : KMor1 3).level = 1 := by decide
    have hsup :
        Fin.maxOfNat 3 (fun i : Fin 3 =>
          match i with
          | ⟨0, _⟩ => (KMor1.predIter n k).level
          | ⟨1, _⟩ => (branches ⟨0, by omega⟩).level
          | ⟨2, _⟩ => (KMor1.pcDispatchFrom (k + 1) size'
              (fun j => branches j.succ) default).level) ≤ 1 :=
      Fin.maxOfNat_le (by
        intro i
        match i with
        | ⟨0, _⟩ => exact hpred
        | ⟨1, _⟩ => exact hb0
        | ⟨2, _⟩ => exact hrecur)
    rw [hcond_level]
    exact Nat.max_le.mpr ⟨le_refl 1, hsup⟩

/-- `KMor1.pcDispatch` is at level ≤ 1 when branches and
default are level ≤ 1. -/
theorem KMor1.pcDispatch_level
    {n : ℕ} (size : ℕ)
    (branches : Fin size → KMor1 (n + 1))
    (default : KMor1 (n + 1))
    (h_branches : ∀ j, (branches j).level ≤ 1)
    (h_default : default.level ≤ 1) :
    (KMor1.pcDispatch size branches default).level ≤ 1 := by
  unfold KMor1.pcDispatch
  exact KMor1.pcDispatchFrom_level size 0 branches default
    h_branches h_default

end GebLean

namespace GebLean.KSimURMSimulator

open GebLean.ZeroTestURM
open GebLean

/-- The base family for `simulate`'s simrec at time `y = 0`,
mirroring `URMState.init` syntactically. By `Fin.lastCases`:
the `Fin.last` case is the PC component (`KMor1.zero`, since
`URMState.init`'s `pc := 0`); the `castSucc` case is a register
component for `r : Fin P.numRegs`, which performs the same
`List.find?` lookup as `URMState.init`'s `regs` field and
returns the corresponding `KMor1.proj` for an input slot, or
`KMor1.zero` otherwise.

In the `some i` branch, `i : Fin a` is the input slot index
returned by `List.find?` (distinct from the outer-scope
register index `r : Fin P.numRegs`); `KMor1.proj i` then has
type `KMor1 a`, matching the `baseFamily` return type.

Per spec § 3.3. -/
def baseFamily {a : ℕ} (P : URMProgram a) :
    Fin (P.numRegs + 1) → KMor1 a :=
  Fin.lastCases
    (KMor1.zero : KMor1 a)
    (fun r : Fin P.numRegs =>
      match (List.finRange a).find?
            (fun i => decide (P.inputRegs i = r)) with
      | some i => KMor1.proj i
      | none   => KMor1.zero)

-- AXIOM_ALLOW: Classical.choice (transitively via mathlib's
-- Fin.lastCases_castSucc / Fin.reverseInduction.go; project
-- policy accepts this exception per .claude/rules/lean-coding.md
-- § Accepted exceptions).
/-- Every base-family component is at level 0 (each is
`KMor1.zero` or `KMor1.proj _`). -/
theorem baseFamily_level {a : ℕ} (P : URMProgram a)
    (j : Fin (P.numRegs + 1)) :
    (baseFamily P j).level = 0 := by
  refine Fin.lastCases ?_ ?_ j
  · -- j = Fin.last P.numRegs
    simp only [baseFamily, Fin.lastCases_last]
    rfl
  · -- j = r.castSucc for some r : Fin P.numRegs
    intro r
    simp only [baseFamily, Fin.lastCases_castSucc]
    cases h : (List.finRange a).find?
        (fun i => decide (P.inputRegs i = r)) with
    | some i => unfold KMor1.level; omega
    | none => unfold KMor1.level; omega

/-- Projection at the step context's last slot: the previous
PC value. Level 0. The Fin index is pinned numerically as
`⟨a + 1 + P.numRegs, _⟩` rather than `Fin.last …` because
`Fin.last (a + P.numRegs + 1)` and `Fin (a + 1 + (P.numRegs + 1))`
may fail to unify definitionally under Lean's `Nat.add` normal
form; the explicit construction sidesteps that elaboration risk. -/
private def I_prev {a : ℕ} (P : URMProgram a) :
    KMor1 (a + 1 + (P.numRegs + 1)) :=
  KMor1.proj ⟨a + 1 + P.numRegs, by omega⟩

/-- Projection at slot `a + 1 + j.val` of the step context:
the previous value of register `j`. Level 0. -/
private def v_j_prev {a : ℕ} (P : URMProgram a)
    (j : Fin P.numRegs) :
    KMor1 (a + 1 + (P.numRegs + 1)) :=
  KMor1.proj ⟨a + 1 + j.val, by
    have := j.isLt
    omega⟩

/-- The PC-component step-family branch for instruction at
PC = k. Returns the new PC value after executing the
instruction:

- `.stop` → unchanged (`I_prev`);
- `.jumpZ i l₁ l₂` → `cond` on `v_i_prev` selecting `l₁` if 0,
  else `l₂`;
- `.assign`, `.inc`, `.dec` → `I_prev + 1`. -/
private def branches_pc {a : ℕ} (P : URMProgram a)
    (k : Fin P.instrs.size) :
    KMor1 (a + 1 + (P.numRegs + 1)) :=
  match P.instrs[k]'k.isLt with
  | URMInstr.stop => I_prev P
  | URMInstr.jumpZ i l₁ l₂ =>
    KMor1.comp KMor1.cond
      (fun ix : Fin 3 => match ix with
        | ⟨0, _⟩ => v_j_prev P i
        | ⟨1, _⟩ => KMor1.natK' _ l₁
        | ⟨2, _⟩ => KMor1.natK' _ l₂)
  | URMInstr.assign _ _ =>
    KMor1.comp KMor1.succ (fun _ : Fin 1 => I_prev P)
  | URMInstr.inc _ =>
    KMor1.comp KMor1.succ (fun _ : Fin 1 => I_prev P)
  | URMInstr.dec _ =>
    KMor1.comp KMor1.succ (fun _ : Fin 1 => I_prev P)

/-- The register-`j`-component step-family branch for
instruction at PC = k. Returns the new register-`j` value
after executing the instruction:

- `.assign i c` if `i = j` → `c`; else `v_j_prev`.
- `.inc i` if `i = j` → `v_j_prev + 1`; else `v_j_prev`.
- `.dec i` if `i = j` → `pred v_j_prev`; else `v_j_prev`.
- `.jumpZ`, `.stop` → `v_j_prev` (registers unchanged). -/
private def branches_j {a : ℕ} (P : URMProgram a)
    (j : Fin P.numRegs) (k : Fin P.instrs.size) :
    KMor1 (a + 1 + (P.numRegs + 1)) :=
  match P.instrs[k]'k.isLt with
  | URMInstr.assign i c =>
    if i.val = j.val then KMor1.natK' _ c else v_j_prev P j
  | URMInstr.inc i =>
    if i.val = j.val then
      KMor1.comp KMor1.succ (fun _ : Fin 1 => v_j_prev P j)
    else v_j_prev P j
  | URMInstr.dec i =>
    if i.val = j.val then
      KMor1.comp KMor1.pred (fun _ : Fin 1 => v_j_prev P j)
    else v_j_prev P j
  | URMInstr.jumpZ _ _ _ => v_j_prev P j
  | URMInstr.stop => v_j_prev P j

/-- The step family for `simulate`'s simrec. By `Fin.lastCases`:
the `Fin.last` case is the PC component (dispatched via
`pcDispatch` over `branches_pc` with `default_pc := I_prev`);
the `castSucc` case is a register-`j` component (dispatched via
`pcDispatch` over `branches_j j` with `default_j := v_j_prev`).
Each branch is at level ≤ 1 by inspection (cond, pred are
level 1; succ, proj, natK' are level 0); the dispatcher's
`pcDispatch_level` gives `stepFamily P i` at level ≤ 1.

Per spec § 3.4. -/
def stepFamily {a : ℕ} (P : URMProgram a) :
    Fin (P.numRegs + 1) → KMor1 (a + 1 + (P.numRegs + 1)) :=
  Fin.lastCases
    (KMor1.pcDispatch P.instrs.size
      (fun k => branches_pc P k)
      (I_prev P))
    (fun j : Fin P.numRegs =>
      KMor1.pcDispatch P.instrs.size
        (fun k => branches_j P j k)
        (v_j_prev P j))

-- AXIOM_ALLOW: Classical.choice (transitively via mathlib's
-- Fin.lastCases_castSucc; see .claude/rules/lean-coding.md
-- § Accepted exceptions).
/-- Every step-family component is at level ≤ 1. Each branch
and the default are at level ≤ 1 by inspection; the dispatcher's
`KMor1.pcDispatch_level` gives the result. -/
theorem stepFamily_level {a : ℕ} (P : URMProgram a)
    (j : Fin (P.numRegs + 1)) :
    (stepFamily P j).level ≤ 1 := by
  -- Common abbreviations for branch reasoning.
  have hsucc : (KMor1.succ : KMor1 1).level = 0 := rfl
  have hpred : (KMor1.pred : KMor1 1).level = 1 := by decide
  have hcond : (KMor1.cond : KMor1 3).level = 1 := by decide
  have hI : (I_prev P).level = 0 := by unfold I_prev KMor1.level; rfl
  refine Fin.lastCases ?_ ?_ j
  · -- j = Fin.last P.numRegs
    simp only [stepFamily, Fin.lastCases_last]
    apply KMor1.pcDispatch_level
    · intro k
      unfold branches_pc
      match hi : P.instrs[k]'k.isLt with
      | URMInstr.assign i c =>
        simp only [KMor1.level]
        have hsup :
            Fin.maxOfNat 1 (fun _ : Fin 1 => (I_prev P).level)
              ≤ 1 :=
          Fin.maxOfNat_le (by intro _; rw [hI]; omega)
        omega
      | URMInstr.inc i =>
        simp only [KMor1.level]
        have hsup :
            Fin.maxOfNat 1 (fun _ : Fin 1 => (I_prev P).level)
              ≤ 1 :=
          Fin.maxOfNat_le (by intro _; rw [hI]; omega)
        omega
      | URMInstr.dec i =>
        simp only [KMor1.level]
        have hsup :
            Fin.maxOfNat 1 (fun _ : Fin 1 => (I_prev P).level)
              ≤ 1 :=
          Fin.maxOfNat_le (by intro _; rw [hI]; omega)
        omega
      | URMInstr.jumpZ i l₁ l₂ =>
        simp only [KMor1.level]
        have hv : (v_j_prev P i).level = 0 := by
          unfold v_j_prev KMor1.level; rfl
        have hsup :
            Fin.maxOfNat 3 (fun ix : Fin 3 =>
              (match ix with
                | (⟨0, _⟩ : Fin 3) => v_j_prev P i
                | ⟨1, _⟩ => KMor1.natK' _ l₁
                | ⟨2, _⟩ => KMor1.natK' _ l₂).level) ≤ 1 :=
          Fin.maxOfNat_le (by
            intro ix
            match ix with
            | ⟨0, _⟩ => rw [hv]; omega
            | ⟨1, _⟩ => rw [KMor1.natK'_level]; omega
            | ⟨2, _⟩ => rw [KMor1.natK'_level]; omega)
        omega
      | URMInstr.stop =>
        rw [hI]; omega
    · rw [hI]; omega
  · intro r
    have hv : (v_j_prev P r).level = 0 := by
      unfold v_j_prev KMor1.level; rfl
    simp only [stepFamily, Fin.lastCases_castSucc]
    apply KMor1.pcDispatch_level
    · intro k
      unfold branches_j
      match hi : P.instrs[k]'k.isLt with
      | URMInstr.assign i c =>
        dsimp only
        by_cases h : i.val = r.val
        · rw [if_pos h]
          have := KMor1.natK'_level (a + 1 + (P.numRegs + 1)) c
          omega
        · rw [if_neg h, hv]; omega
      | URMInstr.inc i =>
        dsimp only
        by_cases h : i.val = r.val
        · rw [if_pos h]
          simp only [KMor1.level]
          have hsup :
              Fin.maxOfNat 1 (fun _ : Fin 1 => (v_j_prev P r).level)
                ≤ 1 :=
            Fin.maxOfNat_le (by intro _; rw [hv]; omega)
          omega
        · rw [if_neg h, hv]; omega
      | URMInstr.dec i =>
        dsimp only
        by_cases h : i.val = r.val
        · rw [if_pos h]
          simp only [KMor1.level]
          have hsup :
              Fin.maxOfNat 1 (fun _ : Fin 1 => (v_j_prev P r).level)
                ≤ 1 :=
            Fin.maxOfNat_le (by intro _; rw [hv]; omega)
          omega
        · rw [if_neg h, hv]; omega
      | URMInstr.jumpZ i l₁ l₂ =>
        dsimp only
        rw [hv]; omega
      | URMInstr.stop =>
        dsimp only
        rw [hv]; omega
    · rw [hv]; omega

/-- The K^sim simulator for a URMProgram: a single
`KMor1.simrec` with system size `P.numRegs + 1` (registers at
indices `0..numRegs - 1`, PC at index `numRegs`), base family
`baseFamily P`, step family `stepFamily P`, and output index
`P.outputReg.castSucc`. Returns a morphism of arity `a + 1`:
slot 0 carries the time bound `y`, slots `1..a` carry the
input vector.

Per spec § 3.1, § 3.2. -/
def simulate {a : ℕ} (P : URMProgram a) : KMor1 (a + 1) :=
  KMor1.simrec (a := a) (k := P.numRegs)
    (i := P.outputReg.castSucc)
    (baseFamily P)
    (stepFamily P)

/-- Back-peel reduction for `URMState.runFor`: derived from the
front-peel `runFor_succ` (`ZeroTestURM.lean:192`) and additivity
`runFor_add` (`:199`). Inside the helper-lemma scope the `s`
parameter is fully general — the helper itself does not hit the
fixed-`s := init P v` trap. Only the consumer
(`simulate_step_match`'s step case) is locked to that specific
`s`, which is why `runFor_succ` (front-peel, `@[simp]`) is
wrong-directional there and this back-peel form must be
invoked explicitly. Placed directly under
`namespace GebLean.KSimURMSimulator` (no `URMState`
sub-namespace) so the fully qualified name is
`GebLean.KSimURMSimulator.runFor_succ_init_back`, avoiding
confusing parallelism with `GebLean.ZeroTestURM.URMState`. Per
spec § 4.3. -/
private theorem runFor_succ_init_back {a : ℕ}
    (P : URMProgram a) (s : URMState P) (y : ℕ) :
    URMState.runFor P s (y + 1)
      = URMState.step P (URMState.runFor P s y) := by
  rw [URMState.runFor_add P s y 1]
  rw [URMState.runFor_succ P (URMState.runFor P s y) 0]
  rw [URMState.runFor_zero]

/-- The `simrecVec_succ`-produced dispatcher context, evaluated
at any slot in the "previous-component" range
(`a + 1 ≤ slot < a + 1 + (P.numRegs + 1)`), equals the previous
simrec component at the residue index `slot - (a + 1)`. Used
across both the PC and the register-`j` components in the step
case of `simulate_step_match`. Per round-4 findings R4-B2,
R4-S6, R4-M3.

This helper is the sole site in T3 that couples directly to
`KMor1.simrecVec_succ`'s `dite`-form context shape
(`LawvereKSimInterp.lean:193 – 209`). If that lemma's shape
changes (for example, the inner
`if h₂ : idx.val = 0 then n else params ⟨…⟩` becomes a
`match`), the body's `change` will need to be re-stated to match
the new form. All call sites consume the helper through its
declared signature only — per plan round-6 serious finding R6-S1. -/
private lemma step_ctx_eval_simrec {a : ℕ} (P : URMProgram a)
    (v : Fin a → ℕ) (y : ℕ)
    (slot : ℕ) (h_slot_bound : slot < a + 1 + (P.numRegs + 1))
    (h_slot_ge : a + 1 ≤ slot) :
    (fun idx : Fin (a + 1 + (P.numRegs + 1)) =>
       if h₁ : idx.val < a + 1 then
         if h₂ : idx.val = 0 then (y : ℕ)
         else v ⟨idx.val - 1, by omega⟩
       else
         KMor1.simrecVec (baseFamily P) (stepFamily P) v y
           ⟨idx.val - (a + 1), by omega⟩)
        ⟨slot, h_slot_bound⟩
    = KMor1.simrecVec (baseFamily P) (stepFamily P) v y
        ⟨slot - (a + 1), by omega⟩ := by
  change (if h₁ : slot < a + 1 then _ else
          KMor1.simrecVec (baseFamily P) (stepFamily P) v y
            ⟨slot - (a + 1), by omega⟩) = _
  rw [dif_neg (by omega)]

-- AXIOM_ALLOW: Classical.choice (transitively via mathlib's
-- Fin.lastCases_castSucc; see .claude/rules/lean-coding.md
-- § Accepted exceptions).
/-- The conjunctive vector invariant: at every time `y`, the
simrec state vector at each component matches the URM state's
corresponding field. The PC component is at index
`Fin.last P.numRegs`; each register-`j` component is at index
`j.castSucc` (for `j : Fin P.numRegs`).

Per spec § 4.2. -/
private theorem simulate_step_match {a : ℕ}
    (P : URMProgram a) (v : Fin a → ℕ) (y : ℕ) :
    KMor1.simrecVec (baseFamily P) (stepFamily P) v y
        (Fin.last P.numRegs)
      = ((URMState.init P v).runFor P y).pc
    ∧ ∀ j : Fin P.numRegs,
        KMor1.simrecVec (baseFamily P) (stepFamily P) v y
            j.castSucc
          = ((URMState.init P v).runFor P y).regs j := by
  induction y with
  | zero =>
    refine ⟨?_, ?_⟩
    · simp only [KMor1.simrecVec_zero, baseFamily,
        Fin.lastCases_last, KMor1.interp_zero]
      rw [URMState.runFor_zero]
      unfold URMState.init
      rfl
    · intro j
      simp only [KMor1.simrecVec_zero, baseFamily,
        Fin.lastCases_castSucc]
      rw [URMState.runFor_zero]
      cases h : (List.finRange a).find?
          (fun i => decide (P.inputRegs i = j)) with
      | some i =>
        simp only [KMor1.interp_proj]
        unfold URMState.init
        simp only [h]
      | none =>
        simp only [KMor1.interp_zero]
        unfold URMState.init
        simp only [h]
  | succ y ih =>
    obtain ⟨ih_pc, ih_regs⟩ := ih
    rw [runFor_succ_init_back]
    refine ⟨?_, ?_⟩
    · -- PC component at y + 1.
      rw [KMor1.simrecVec_succ]
      simp only [stepFamily, Fin.lastCases_last]
      have h_ctx_last_pc :
          (fun idx : Fin (a + 1 + (P.numRegs + 1)) =>
            if h₁ : idx.val < a + 1 then
              if h₂ : idx.val = 0 then (y : ℕ)
              else v ⟨idx.val - 1, by omega⟩
            else
              KMor1.simrecVec (baseFamily P) (stepFamily P) v y
                ⟨idx.val - (a + 1), by omega⟩)
              (Fin.last (a + 1 + P.numRegs))
            = ((URMState.init P v).runFor P y).pc := by
        rw [show (Fin.last (a + 1 + P.numRegs)
                : Fin (a + 1 + (P.numRegs + 1)))
              = ⟨a + 1 + P.numRegs, by omega⟩
              from by apply Fin.ext; rfl]
        rw [step_ctx_eval_simrec P v y (a + 1 + P.numRegs)
              (by omega) (by omega)]
        rw [show (⟨a + 1 + P.numRegs - (a + 1), by omega⟩
                : Fin (P.numRegs + 1))
              = Fin.last P.numRegs
              from by apply Fin.ext; simp [Fin.last]]
        exact ih_pc
      by_cases h_inbounds :
          ((URMState.init P v).runFor P y).pc < P.instrs.size
      · set pcVal := ((URMState.init P v).runFor P y).pc with hpc
        rw [KMor1.interp_pcDispatch_match P.instrs.size
              (fun k => branches_pc P k) (I_prev P) _
              ⟨pcVal, h_inbounds⟩ h_ctx_last_pc]
        match h_instr : P.instrs[pcVal]'h_inbounds with
        | URMInstr.assign i c =>
          have h_instr2 : P.instrs[(⟨pcVal, h_inbounds⟩ : Fin _)]
              = URMInstr.assign i c := h_instr
          simp only [branches_pc, h_instr2, KMor1.interp_comp,
            KMor1.interp_succ, I_prev, KMor1.interp_proj]
          simp only [URMState.step]
          rw [dif_pos h_inbounds]
          rw [show P.instrs[(URMState.runFor P (URMState.init P v) y).pc]
                = URMInstr.assign i c from h_instr]
          rw [dif_neg (by omega : ¬ a + 1 + P.numRegs < a + 1)]
          rw [show (⟨a + 1 + P.numRegs - (a + 1), by omega⟩
                  : Fin (P.numRegs + 1))
                = Fin.last P.numRegs
                from by apply Fin.ext; simp [Fin.last]]
          rw [ih_pc]
        | URMInstr.inc i =>
          have h_instr2 : P.instrs[(⟨pcVal, h_inbounds⟩ : Fin _)]
              = URMInstr.inc i := h_instr
          simp only [branches_pc, h_instr2, KMor1.interp_comp,
            KMor1.interp_succ, I_prev, KMor1.interp_proj]
          simp only [URMState.step]
          rw [dif_pos h_inbounds]
          rw [show P.instrs[(URMState.runFor P (URMState.init P v) y).pc]
                = URMInstr.inc i from h_instr]
          rw [dif_neg (by omega : ¬ a + 1 + P.numRegs < a + 1)]
          rw [show (⟨a + 1 + P.numRegs - (a + 1), by omega⟩
                  : Fin (P.numRegs + 1))
                = Fin.last P.numRegs
                from by apply Fin.ext; simp [Fin.last]]
          rw [ih_pc]
        | URMInstr.dec i =>
          have h_instr2 : P.instrs[(⟨pcVal, h_inbounds⟩ : Fin _)]
              = URMInstr.dec i := h_instr
          simp only [branches_pc, h_instr2, KMor1.interp_comp,
            KMor1.interp_succ, I_prev, KMor1.interp_proj]
          simp only [URMState.step]
          rw [dif_pos h_inbounds]
          rw [show P.instrs[(URMState.runFor P (URMState.init P v) y).pc]
                = URMInstr.dec i from h_instr]
          rw [dif_neg (by omega : ¬ a + 1 + P.numRegs < a + 1)]
          rw [show (⟨a + 1 + P.numRegs - (a + 1), by omega⟩
                  : Fin (P.numRegs + 1))
                = Fin.last P.numRegs
                from by apply Fin.ext; simp [Fin.last]]
          rw [ih_pc]
        | URMInstr.jumpZ i l₁ l₂ =>
          have h_instr2 : P.instrs[(⟨pcVal, h_inbounds⟩ : Fin _)]
              = URMInstr.jumpZ i l₁ l₂ := h_instr
          simp only [branches_pc, h_instr2, KMor1.interp_comp,
            KMor1.interp_cond, v_j_prev, KMor1.interp_proj]
          simp only [URMState.step]
          rw [dif_pos h_inbounds]
          rw [show P.instrs[(URMState.runFor P (URMState.init P v) y).pc]
                = URMInstr.jumpZ i l₁ l₂ from h_instr]
          rw [dif_neg (by omega : ¬ a + 1 + i.val < a + 1)]
          rw [show (⟨a + 1 + i.val - (a + 1), by omega⟩
                : Fin (P.numRegs + 1)) = i.castSucc
                from by apply Fin.ext; simp [Fin.castSucc]]
          rw [ih_regs i]
          simp only [KMor1.natK', KMor1.interp_comp, KMor1.interp_natK]
        | URMInstr.stop =>
          have h_instr2 : P.instrs[(⟨pcVal, h_inbounds⟩ : Fin _)]
              = URMInstr.stop := h_instr
          simp only [branches_pc, h_instr2, I_prev, KMor1.interp_proj]
          simp only [URMState.step]
          rw [dif_pos h_inbounds]
          rw [show P.instrs[(URMState.runFor P (URMState.init P v) y).pc]
                = URMInstr.stop from h_instr]
          rw [dif_neg (by omega : ¬ a + 1 + P.numRegs < a + 1)]
          rw [show (⟨a + 1 + P.numRegs - (a + 1), by omega⟩
                  : Fin (P.numRegs + 1))
                = Fin.last P.numRegs
                from by apply Fin.ext; simp [Fin.last]]
          exact ih_pc
      · push_neg at h_inbounds
        have h_ctx_ge :
            (fun idx : Fin (a + 1 + (P.numRegs + 1)) =>
              if h₁ : idx.val < a + 1 then
                if h₂ : idx.val = 0 then (y : ℕ)
                else v ⟨idx.val - 1, by omega⟩
              else
                KMor1.simrecVec (baseFamily P) (stepFamily P) v y
                  ⟨idx.val - (a + 1), by omega⟩)
                (Fin.last (a + 1 + P.numRegs))
              ≥ P.instrs.size := by
          rw [h_ctx_last_pc]; exact h_inbounds
        rw [KMor1.interp_pcDispatch_default P.instrs.size
              (fun k => branches_pc P k) (I_prev P) _ h_ctx_ge]
        simp only [I_prev, KMor1.interp_proj]
        simp only [URMState.step]
        rw [dif_neg (Nat.not_lt_of_ge h_inbounds)]
        rw [dif_neg (by omega : ¬ a + 1 + P.numRegs < a + 1)]
        rw [show (⟨a + 1 + P.numRegs - (a + 1), by omega⟩
                : Fin (P.numRegs + 1))
              = Fin.last P.numRegs
              from by apply Fin.ext; simp [Fin.last]]
        exact ih_pc
    · -- Register-j component at y + 1.
      intro j
      rw [KMor1.simrecVec_succ]
      simp only [stepFamily, Fin.lastCases_castSucc]
      have h_ctx_last_pc :
          (fun idx : Fin (a + 1 + (P.numRegs + 1)) =>
            if h₁ : idx.val < a + 1 then
              if h₂ : idx.val = 0 then (y : ℕ)
              else v ⟨idx.val - 1, by omega⟩
            else
              KMor1.simrecVec (baseFamily P) (stepFamily P) v y
                ⟨idx.val - (a + 1), by omega⟩)
              (Fin.last (a + 1 + P.numRegs))
            = ((URMState.init P v).runFor P y).pc := by
        rw [show (Fin.last (a + 1 + P.numRegs)
                : Fin (a + 1 + (P.numRegs + 1)))
              = ⟨a + 1 + P.numRegs, by omega⟩
              from by apply Fin.ext; rfl]
        rw [step_ctx_eval_simrec P v y (a + 1 + P.numRegs)
              (by omega) (by omega)]
        rw [show (⟨a + 1 + P.numRegs - (a + 1), by omega⟩
                : Fin (P.numRegs + 1))
              = Fin.last P.numRegs
              from by apply Fin.ext; simp [Fin.last]]
        exact ih_pc
      by_cases h_inbounds :
          ((URMState.init P v).runFor P y).pc < P.instrs.size
      · set pcVal := ((URMState.init P v).runFor P y).pc with hpc
        rw [KMor1.interp_pcDispatch_match P.instrs.size
              (fun k => branches_j P j k) (v_j_prev P j) _
              ⟨pcVal, h_inbounds⟩ h_ctx_last_pc]
        match h_instr : P.instrs[pcVal]'h_inbounds with
        | URMInstr.assign i c =>
          have h_instr2 : P.instrs[(⟨pcVal, h_inbounds⟩ : Fin _)]
              = URMInstr.assign i c := h_instr
          simp only [branches_j, h_instr2]
          simp only [URMState.step]
          rw [dif_pos h_inbounds]
          rw [show P.instrs[(URMState.runFor P (URMState.init P v) y).pc]
                = URMInstr.assign i c from h_instr]
          by_cases h_eq : i.val = j.val
          · rw [if_pos h_eq]
            simp only [KMor1.natK', KMor1.interp_comp, KMor1.interp_natK]
            rw [Function.update_apply, if_pos (Fin.ext h_eq).symm]
          · rw [if_neg h_eq]
            simp only [v_j_prev, KMor1.interp_proj]
            rw [Function.update_apply,
                if_neg (fun h => h_eq (Fin.val_eq_of_eq h).symm)]
            rw [dif_neg (by omega : ¬ a + 1 + j.val < a + 1)]
            rw [show (⟨a + 1 + j.val - (a + 1), by omega⟩
                    : Fin (P.numRegs + 1))
                  = j.castSucc
                  from by apply Fin.ext; simp [Fin.castSucc]]
            exact ih_regs j
        | URMInstr.inc i =>
          have h_instr2 : P.instrs[(⟨pcVal, h_inbounds⟩ : Fin _)]
              = URMInstr.inc i := h_instr
          simp only [branches_j, h_instr2]
          simp only [URMState.step]
          rw [dif_pos h_inbounds]
          rw [show P.instrs[(URMState.runFor P (URMState.init P v) y).pc]
                = URMInstr.inc i from h_instr]
          by_cases h_eq : i.val = j.val
          · rw [if_pos h_eq]
            simp only [KMor1.interp_comp, KMor1.interp_succ,
              v_j_prev, KMor1.interp_proj]
            rw [Function.update_apply, if_pos (Fin.ext h_eq).symm]
            rw [dif_neg (by omega : ¬ a + 1 + j.val < a + 1)]
            rw [show (⟨a + 1 + j.val - (a + 1), by omega⟩
                    : Fin (P.numRegs + 1))
                  = j.castSucc
                  from by apply Fin.ext; simp [Fin.castSucc]]
            rw [ih_regs j]
            rw [show i = j from Fin.ext h_eq]
          · rw [if_neg h_eq]
            simp only [v_j_prev, KMor1.interp_proj]
            rw [Function.update_apply,
                if_neg (fun h => h_eq (Fin.val_eq_of_eq h).symm)]
            rw [dif_neg (by omega : ¬ a + 1 + j.val < a + 1)]
            rw [show (⟨a + 1 + j.val - (a + 1), by omega⟩
                    : Fin (P.numRegs + 1))
                  = j.castSucc
                  from by apply Fin.ext; simp [Fin.castSucc]]
            exact ih_regs j
        | URMInstr.dec i =>
          have h_instr2 : P.instrs[(⟨pcVal, h_inbounds⟩ : Fin _)]
              = URMInstr.dec i := h_instr
          simp only [branches_j, h_instr2]
          simp only [URMState.step]
          rw [dif_pos h_inbounds]
          rw [show P.instrs[(URMState.runFor P (URMState.init P v) y).pc]
                = URMInstr.dec i from h_instr]
          by_cases h_eq : i.val = j.val
          · rw [if_pos h_eq]
            simp only [KMor1.interp_comp, KMor1.interp_pred,
              v_j_prev, KMor1.interp_proj]
            rw [Function.update_apply, if_pos (Fin.ext h_eq).symm]
            rw [dif_neg (by omega : ¬ a + 1 + j.val < a + 1)]
            rw [show (⟨a + 1 + j.val - (a + 1), by omega⟩
                    : Fin (P.numRegs + 1))
                  = j.castSucc
                  from by apply Fin.ext; simp [Fin.castSucc]]
            rw [ih_regs j]
            rw [show i = j from Fin.ext h_eq]
            exact Nat.pred_eq_sub_one
          · rw [if_neg h_eq]
            simp only [v_j_prev, KMor1.interp_proj]
            rw [Function.update_apply,
                if_neg (fun h => h_eq (Fin.val_eq_of_eq h).symm)]
            rw [dif_neg (by omega : ¬ a + 1 + j.val < a + 1)]
            rw [show (⟨a + 1 + j.val - (a + 1), by omega⟩
                    : Fin (P.numRegs + 1))
                  = j.castSucc
                  from by apply Fin.ext; simp [Fin.castSucc]]
            exact ih_regs j
        | URMInstr.jumpZ i l₁ l₂ =>
          have h_instr2 : P.instrs[(⟨pcVal, h_inbounds⟩ : Fin _)]
              = URMInstr.jumpZ i l₁ l₂ := h_instr
          simp only [branches_j, h_instr2, v_j_prev, KMor1.interp_proj]
          simp only [URMState.step]
          rw [dif_pos h_inbounds]
          rw [show P.instrs[(URMState.runFor P (URMState.init P v) y).pc]
                = URMInstr.jumpZ i l₁ l₂ from h_instr]
          rw [dif_neg (by omega : ¬ a + 1 + j.val < a + 1)]
          rw [show (⟨a + 1 + j.val - (a + 1), by omega⟩
                  : Fin (P.numRegs + 1))
                = j.castSucc
                from by apply Fin.ext; simp [Fin.castSucc]]
          exact ih_regs j
        | URMInstr.stop =>
          have h_instr2 : P.instrs[(⟨pcVal, h_inbounds⟩ : Fin _)]
              = URMInstr.stop := h_instr
          simp only [branches_j, h_instr2, v_j_prev, KMor1.interp_proj]
          simp only [URMState.step]
          rw [dif_pos h_inbounds]
          rw [show P.instrs[(URMState.runFor P (URMState.init P v) y).pc]
                = URMInstr.stop from h_instr]
          rw [dif_neg (by omega : ¬ a + 1 + j.val < a + 1)]
          rw [show (⟨a + 1 + j.val - (a + 1), by omega⟩
                  : Fin (P.numRegs + 1))
                = j.castSucc
                from by apply Fin.ext; simp [Fin.castSucc]]
          exact ih_regs j
      · push_neg at h_inbounds
        have h_ctx_ge :
            (fun idx : Fin (a + 1 + (P.numRegs + 1)) =>
              if h₁ : idx.val < a + 1 then
                if h₂ : idx.val = 0 then (y : ℕ)
                else v ⟨idx.val - 1, by omega⟩
              else
                KMor1.simrecVec (baseFamily P) (stepFamily P) v y
                  ⟨idx.val - (a + 1), by omega⟩)
                (Fin.last (a + 1 + P.numRegs))
              ≥ P.instrs.size := by
          rw [h_ctx_last_pc]; exact h_inbounds
        rw [KMor1.interp_pcDispatch_default P.instrs.size
              (fun k => branches_j P j k) (v_j_prev P j) _ h_ctx_ge]
        simp only [v_j_prev, KMor1.interp_proj]
        simp only [URMState.step]
        rw [dif_neg (Nat.not_lt_of_ge h_inbounds)]
        rw [dif_neg (by omega : ¬ a + 1 + j.val < a + 1)]
        rw [show (⟨a + 1 + j.val - (a + 1), by omega⟩
                : Fin (P.numRegs + 1))
              = j.castSucc
              from by apply Fin.ext; simp [Fin.castSucc]]
        exact ih_regs j

-- AXIOM_ALLOW: Classical.choice (transitively via mathlib's
-- Fin.lastCases_castSucc through simulate_step_match; see
-- .claude/rules/lean-coding.md § Accepted exceptions).
/-- The K^sim simulator's output at time `y` and input `v`
equals the value of `P.outputReg` after `y` URM steps from
`URMState.init P v`. Holds for every `URMProgram a`; no
`WellBounded` precondition required. Per spec § 4.1. -/
theorem simulate_interp {a : ℕ} (P : URMProgram a)
    (y : ℕ) (v : Fin a → ℕ) :
    (simulate P).interp (Fin.cons y v)
      = ((URMState.init P v).runFor P y).regs P.outputReg := by
  simp only [simulate, KMor1.interp_simrec, Fin.cons_zero,
    Fin.cons_succ]
  exact (simulate_step_match P v y).2 P.outputReg

-- AXIOM_ALLOW: Classical.choice (transitively via mathlib's
-- Fin.lastCases_castSucc through baseFamily_level /
-- stepFamily_level; see .claude/rules/lean-coding.md
-- § Accepted exceptions).
/-- The K^sim simulator is at level ≤ 2. By `KMor1.level`'s
`.simrec` clause, the level is `max sup_h sup_g + 1` where
`sup_h ≤ 0` (each base-family component is level 0 per
`baseFamily_level`) and `sup_g ≤ 1` (each step-family
component is level ≤ 1 per `stepFamily_level`). Per spec § 5. -/
theorem simulate_level {a : ℕ} (P : URMProgram a) :
    (simulate P).level ≤ 2 := by
  unfold simulate
  change max (Fin.maxOfNat _ (fun i => (baseFamily P i).level))
             (Fin.maxOfNat _ (fun i => (stepFamily P i).level))
         + 1 ≤ 2
  apply Nat.add_le_add_right
  apply max_le
  · exact Fin.maxOfNat_le (by intro i; rw [baseFamily_level]; omega)
  · exact Fin.maxOfNat_le (fun i => stepFamily_level P i)

end GebLean.KSimURMSimulator
