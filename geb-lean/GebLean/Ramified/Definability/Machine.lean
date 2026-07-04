import GebLean.Ramified.Algebras
import GebLean.Ramified.Definability.Simultaneous
import GebLean.Ramified.Definability.Ladder
import GebLean.Ramified.Definability.Bounds
import GebLean.Utilities.ZeroTestURM
import Mathlib.Algebra.BigOperators.Fin

/-!
# Machine-state simulation of the zero-test URM by simultaneous recurrence

Leivant III's Lemma 6 (section 3.2) over the `1 + X` word algebra `natAlgSig`:
the machine-state simulation of the repository's zero-test unbounded register
machine (`GebLean/Utilities/ZeroTestURM.lean`) by a single ramified
simultaneous recurrence on the step count. For a `URMProgram p` of arity `a`
with `p.numRegs` registers, the simultaneous family (from
`GebLean/Ramified/Definability/Simultaneous.lean`) has `1 + p.numRegs`
components at the base sort `o`: component `0` tracks the program counter and
component `r + 1` the register `r`. Each component is a ramified recurrence on
the step-count numeral, constructed so that after `t` steps the components track
the program counter and registers of `URMState.runFor p (URMState.init p v) t`.

## Main definitions

* `urmSteps` — the per-component step clauses `SimulSteps (1 + p.numRegs)
  (List.replicate a o) o`. The successor clause of each component case-splits
  on the program counter (a `chooseIdent` over the instruction list) and, per
  instruction, applies the constructor (`inc`), the destructor `ramDstr`
  (`dec`), the case function `ramCase` on the tested register (`jumpZ`), the
  constant numeral (`assign`), or the identity (`stop`). Each case-split
  carries a final identity arm: `URMState.step` is the identity at every
  `pc ≥ instrs.size`, and `chooseIdent`'s fall-through routes every
  out-of-range program counter to that identity arm.
* `sttIdent`, `regIdent` — the program-counter component `simulProj … 0` and
  the register components `simulProj … (r + 1)`.
* `urmEnv` — the environment loading the input numerals at the `o` positions
  and the step-count numeral at the `Ω (o → o)` position.
* `machineCtx` — eq. (8)'s staggered input context: `a` copies of `Ω (θᵢ → θᵢ)`
  with `θᵢ = Ω^{a-1-i}(clockSort q (Ω ω))`, letting the per-input sizes chain
  through the addition copies. Every entry is an object sort (`machineCtx_isObj`)
  and its length is `a` (`machineCtx_length`).
* `sizeFold`, `machineClock` — the staggered size sum and the clock
  `c × 2_q(sz(a))`, built from `szAtIdent`/`addAtIdent`, `twoPowIdent`,
  `mulAtIdent`, and the numeral constant.
* `machineEnv`, `machineIdent`, `machineRealizer` — the numeric input
  environment, the realizer as an identifier (the output-register component fed
  the parameter coercions `δ` and the clock), and the realizer as a morphism of
  `RMRecCat natAlgSig`.

## Main statements

* `urm_simul_interp` — the Lemma 6 invariant: at step count `t` and inputs
  `v`, the program-counter and register components denote the program counter
  and registers of `URMState.runFor p (URMState.init p v) t`, read out through
  `freeAlgToNat`. Proved by induction on `t` with an arm-by-arm match against
  `URMState.step`.
* `urm_ramified_definable` — Lemma 6 with eq. (8) (paper section 3.2, p. 221):
  for a machine computing `f` within time `c × tower q` of the maximum input
  (in the `runFor`-stabilized form), the realizer's denotation is `f`. The clock
  denotes `c * tower q (∑ᵢ (vᵢ + 1))` (`sizeFold_interp`, `machineClock_interp`);
  `maxOfNat_le_sum_succ` and `clock_mono` bound the maximum input by it, and
  `urm_simul_interp` at the clock count closes the read-off. The eq. (8) sort
  reconciliation — the paper's "Let θ = Ωo" surface slips against the staggered
  `machineCtx` and the count sort `ω = Ω(o → o)` — is a presentation adaptation
  (spec section 1.2, standing decision 5); the s1.2 embedding argument is the
  fidelity justification for transcribing against the zero-test URM.

## Implementation notes

The step clauses read the recursive results as the whole selector-indexed state
function `o → o` of the simultaneous recurrence: applying it to the selector
numeral `0` recovers the previous program counter, and to `r + 1` the previous
register `r`. Each per-instruction update is a small explicit definition at
context `[o → o]` (`urmInstrUpdate`); the successor clause of a component wraps
them in a `chooseIdent` over the instruction list, indexed by the program
counter, whose last entry is the identity update. The base clause loads
`URMState.init`'s convention through the same constructive `List.find?` lookup:
program counter `0`, input registers from the parameters, work registers `0`.

The simulation is stated against `URMState.step` directly. Each zero-test URM
instruction is a single command or a constant-length command block of Leivant
III's register machines over the unary algebra (section 3.1): `inc`/`dec` are
in-place constructor assignment and destructor, `assign i c` is a zero
assignment followed by `c` increments, `jumpZ` is the two-way branch, and
`stop` is the end-state convention, with program-counter values as machine
states. URM computations are therefore Leivant-machine computations with
constant overhead (spec section 1.2), so transcribing Lemma 6 against
`URMState.step` is faithful to the paper's register-machine model.

## References

D. Leivant, "Ramified recurrence and computational complexity III: Higher type
recurrence and elementary complexity", Annals of Pure and Applied Logic 96
(1999) 209-229, DOI `10.1016/S0168-0072(98)00040-2`. The machine-state
simulation is Lemma 6, section 3.2; the register-machine model and the
embedding of the zero-test URM into it are section 3.1 and spec section 1.2.
The simultaneous-recurrence realization is section 2.6, eqs. (6)-(7). The
component-indexed packaging of a register machine into the simultaneous family,
and the identity arm routing the implicit-halt state through `chooseIdent`'s
fall-through, are novel packaging.

## Tags

ramified recurrence, simultaneous recurrence, register machine, zero-test URM,
elementary complexity, Leivant
-/

namespace GebLean.Ramified

open CategoryTheory
open GebLean.ZeroTestURM

/-- The recurrence-result variable `phi` of a successor step clause: the sole
`o → o` position of the step context `replicate a o ++ [o → o] ++ [o]`, at
index `a`, over any definition signature. Its denotation is the previous state
as the selector-indexed function `selector ↦ component value`. -/
def urmPhiVar {n : ℕ} (hI : Fin n → List RType × RType) (a : ℕ) :
    Tm (defnSig natAlgSig n hI)
      (List.replicate a RType.o ++ [RType.arrow RType.o RType.o] ++ [RType.o])
      (RType.arrow RType.o RType.o) :=
  Tm.reind
    ((get_finAppL (List.replicate a RType.o ++ [RType.arrow RType.o RType.o]) [RType.o]
        (finAppR (List.replicate a RType.o) [RType.arrow RType.o RType.o]
          ⟨0, by decide⟩)).trans
      (get_finAppR (List.replicate a RType.o) [RType.arrow RType.o RType.o]
        ⟨0, by decide⟩))
    (Tm.var (finAppL (List.replicate a RType.o ++ [RType.arrow RType.o RType.o]) [RType.o]
      (finAppR (List.replicate a RType.o) [RType.arrow RType.o RType.o] ⟨0, by decide⟩)))

/-- The per-instruction update identifier at context `[o → o]` returning the
component's unchanged value: `phi` applied to the component's own selector
numeral `jval` (program counter at `jval = 0`, register `jval - 1` otherwise).
The identity arm of every case-split. -/
def urmSelfUpdate (jval : ℕ) : RIdent natAlgSig [RType.arrow RType.o RType.o] RType.o :=
  RIdent.defn ⟨0, finZeroElim,
    defnApp RType.o RType.o (Tm.var 0) (tmNat jval)⟩ finZeroElim

/-- The per-instruction update identifier returning the successor of the
component's value: `sc (phi (jval))`. The program-counter advance
(`assign`/`inc`/`dec` at the counter) and the register increment (`inc` at the
target). -/
def urmSuccUpdate (jval : ℕ) : RIdent natAlgSig [RType.arrow RType.o RType.o] RType.o :=
  RIdent.defn ⟨0, finZeroElim,
    tmSucc (defnApp RType.o RType.o (Tm.var 0) (tmNat jval))⟩ finZeroElim

/-- The per-instruction update identifier returning the constant numeral `c`,
ignoring the previous state: the register write of `assign i c` at the target
register. -/
def urmConstUpdate (c : ℕ) : RIdent natAlgSig [RType.arrow RType.o RType.o] RType.o :=
  RIdent.defn ⟨0, finZeroElim, tmNat c⟩ finZeroElim

/-- The per-instruction update identifier returning the predecessor of the
component's value: the destructor `ramDstr` applied to `phi (jval)`. The
register update of `dec i` at the target register. -/
def urmDecUpdate (jval : ℕ) : RIdent natAlgSig [RType.arrow RType.o RType.o] RType.o :=
  RIdent.defn ⟨1, Function.const _ ([RType.o], RType.o),
    Tm.op (sig := defnSig natAlgSig 1 (Function.const _ ([RType.o], RType.o)))
      (Sum.inl (Sum.inr ⟨0, by decide⟩))
      (Fin.cons (defnApp RType.o RType.o (Tm.var 0) (tmNat jval)) finZeroElim)⟩
    (fun _ => ramDstr)

/-- The per-instruction update identifier returning the two-way branch target:
the case function `ramCase` applied to `l₁` (the zero target), `l₂` (the
nonzero target), and `phi (iv + 1)` (the tested register `iv`). The
program-counter update of `jumpZ i l₁ l₂`. -/
def urmJumpUpdate (iv l₁ l₂ : ℕ) : RIdent natAlgSig [RType.arrow RType.o RType.o] RType.o :=
  RIdent.defn ⟨1, Function.const _ ([RType.o, RType.o, RType.o], RType.o),
    Tm.op (sig := defnSig natAlgSig 1 (Function.const _ ([RType.o, RType.o, RType.o], RType.o)))
      (Sum.inl (Sum.inr ⟨0, by decide⟩))
      (Fin.cons (tmNat l₁)
        (Fin.cons (tmNat l₂)
          (Fin.cons (defnApp RType.o RType.o (Tm.var 0) (tmNat (iv + 1))) finZeroElim)))⟩
    (fun _ => ramCase RType.o)

/-- The identity update denotes the component's own previous value: on a state
function `φ`, `urmSelfUpdate jval` returns `φ` at the component's selector
numeral `jval`. -/
theorem urmSelfUpdate_interp (jval : ℕ)
    (φ : RType.interp (FreeAlg natAlgSig) (RType.arrow RType.o RType.o)) :
    (urmSelfUpdate jval).interp (Fin.cons φ finZeroElim) = φ (natToFreeAlg jval) := by
  rw [urmSelfUpdate, RIdent.interp_defn]
  simp only [defnApp_eval, tmNat_eval]
  rfl

/-- The constant update denotes the numeral `c`, ignoring the previous state. -/
theorem urmConstUpdate_interp (c : ℕ)
    (φ : RType.interp (FreeAlg natAlgSig) (RType.arrow RType.o RType.o)) :
    (urmConstUpdate c).interp (Fin.cons φ finZeroElim) = natToFreeAlg c := by
  rw [urmConstUpdate, RIdent.interp_defn]
  exact tmNat_eval _ _ c

/-- The successor update denotes one more than the component's previous value,
read as a count: `freeAlgToNat` of the result is `freeAlgToNat (φ jval) + 1`. -/
theorem urmSuccUpdate_interp (jval : ℕ)
    (φ : RType.interp (FreeAlg natAlgSig) (RType.arrow RType.o RType.o)) :
    freeAlgToNat ((urmSuccUpdate jval).interp (Fin.cons φ finZeroElim))
      = freeAlgToNat (φ (natToFreeAlg jval)) + 1 := by
  have h : (urmSuccUpdate jval).interp (Fin.cons φ finZeroElim)
      = FreeAlg.mk (A := natAlgSig) true (fun _ => φ (natToFreeAlg jval)) := by
    rw [urmSuccUpdate, RIdent.interp_defn]
    refine congrArg (FreeAlg.mk (A := natAlgSig) true) (funext (fun v => ?_))
    induction v using Fin.cases with
    | zero =>
      exact eq_of_heq ((cast_heq _ _).trans (heq_of_eq (congrArg φ (tmNat_eval _ _ jval))))
    | succ v' => exact v'.elim0
  rw [h]
  rfl

/-- The decrement update denotes one less than the component's previous value,
read as a count, via the destructor `ramDstr`: `freeAlgToNat` of the result is
`freeAlgToNat (φ jval) - 1`. -/
theorem urmDecUpdate_interp (jval : ℕ)
    (φ : RType.interp (FreeAlg natAlgSig) (RType.arrow RType.o RType.o)) :
    freeAlgToNat ((urmDecUpdate jval).interp (Fin.cons φ finZeroElim))
      = freeAlgToNat (φ (natToFreeAlg jval)) - 1 := by
  have h : (urmDecUpdate jval).interp (Fin.cons φ finZeroElim)
      = ramDstr.interp (dstrEnv (φ (natToFreeAlg jval))) := by
    rw [urmDecUpdate, RIdent.interp_defn]
    refine congrArg ramDstr.interp (funext (fun i => ?_))
    induction i using Fin.cases with
    | zero => exact congrArg φ (tmNat_eval _ _ jval)
    | succ i' => exact i'.elim0
  rw [h, ramDstr_interp]

/-- The case function on a count argument branches on whether the count is zero:
`ramCase` at `caseEnv y₀ y₁ z` denotes `y₀` when `freeAlgToNat z` is zero and
`y₁` otherwise. -/
theorem ramCase_interp_ite (y0 y1 : FreeAlg natAlgSig) (z : FreeAlg natAlgSig) :
    (ramCase RType.o).interp (caseEnv RType.o y0 y1 z)
      = if freeAlgToNat z = 0 then y0 else y1 := by
  cases z with
  | mk _ b subs =>
    cases b with
    | false =>
      change (ramCase RType.o).interp (caseEnv RType.o y0 y1 (FreeAlg.mk false subs)) = _
      rw [ramCase_interp]; rfl
    | true =>
      change (ramCase RType.o).interp (caseEnv RType.o y0 y1 (FreeAlg.mk true subs)) = _
      rw [ramCase_interp]; rfl

/-- The jump update denotes the zero target `l₁` when the tested register `iv`
is zero and the nonzero target `l₂` otherwise, via the case function `ramCase`
applied to `φ (iv + 1)`. -/
theorem urmJumpUpdate_interp (iv l₁ l₂ : ℕ)
    (φ : RType.interp (FreeAlg natAlgSig) (RType.arrow RType.o RType.o)) :
    (urmJumpUpdate iv l₁ l₂).interp (Fin.cons φ finZeroElim)
      = if freeAlgToNat (φ (natToFreeAlg (iv + 1))) = 0
        then natToFreeAlg l₁ else natToFreeAlg l₂ := by
  have h : (urmJumpUpdate iv l₁ l₂).interp (Fin.cons φ finZeroElim)
      = (ramCase RType.o).interp
          (caseEnv RType.o (natToFreeAlg l₁) (natToFreeAlg l₂) (φ (natToFreeAlg (iv + 1)))) := by
    rw [urmJumpUpdate, RIdent.interp_defn]
    refine congrArg (ramCase RType.o).interp (funext (fun i => ?_))
    induction i using Fin.cases with
    | zero => exact tmNat_eval _ _ l₁
    | succ i' =>
      induction i' using Fin.cases with
      | zero => exact tmNat_eval _ _ l₂
      | succ i'' =>
        induction i'' using Fin.cases with
        | zero => exact congrArg φ (tmNat_eval _ _ (iv + 1))
        | succ i''' => exact i'''.elim0
  rw [h, ramCase_interp_ite]

/-- The update identifier for component `j` when executing `instr`: the program
counter (`j.val = 0`) advances, branches, or halts; the register `j.val - 1`
either receives the write, increments, decrements (when it is the instruction's
target `j.val = i.val + 1`), or is left unchanged. Mirrors the arm of
`URMState.step` for `instr`, projected onto component `j`. -/
def urmInstrUpdate {a : ℕ} (p : URMProgram a) (j : Fin (1 + p.numRegs))
    (instr : URMInstr p.numRegs) : RIdent natAlgSig [RType.arrow RType.o RType.o] RType.o :=
  if j.val = 0 then
    match instr with
    | URMInstr.assign _ _ => urmSuccUpdate j.val
    | URMInstr.inc _ => urmSuccUpdate j.val
    | URMInstr.dec _ => urmSuccUpdate j.val
    | URMInstr.jumpZ i l₁ l₂ => urmJumpUpdate i.val l₁ l₂
    | URMInstr.stop => urmSelfUpdate j.val
  else
    match instr with
    | URMInstr.assign i c => if j.val = i.val + 1 then urmConstUpdate c else urmSelfUpdate j.val
    | URMInstr.inc i => if j.val = i.val + 1 then urmSuccUpdate j.val else urmSelfUpdate j.val
    | URMInstr.dec i => if j.val = i.val + 1 then urmDecUpdate j.val else urmSelfUpdate j.val
    | URMInstr.jumpZ _ _ _ => urmSelfUpdate j.val
    | URMInstr.stop => urmSelfUpdate j.val

/-- The `chooseIdent` entry for component `j` at program-counter value `k`: the
update executing instruction `k` when `k` is in range, and the identity update
`urmSelfUpdate` otherwise (the last entry, reached by the fall-through for every
`pc ≥ instrs.size`). -/
def urmEntryIdent {a : ℕ} (p : URMProgram a) (j : Fin (1 + p.numRegs))
    (k : Fin (p.instrs.size + 1)) : RIdent natAlgSig [RType.arrow RType.o RType.o] RType.o :=
  if h : k.val < p.instrs.size then urmInstrUpdate p j (p.instrs[k.val]'h)
  else urmSelfUpdate j.val

/-- The hole contexts of a successor step clause: hole `0` is the selector
`chooseIdent p.instrs.size o` over the `instrs.size + 1` entries; each hole
`k + 1` is a per-instruction update identifier at context `[o → o]`. -/
def urmStepHoleIdx {a : ℕ} (p : URMProgram a) :
    Fin (p.instrs.size + 2) → List RType × RType
  | ⟨0, _⟩ => (RType.o :: List.replicate (p.instrs.size + 1) RType.o, RType.o)
  | ⟨_ + 1, _⟩ => ([RType.arrow RType.o RType.o], RType.o)

/-- The defining term of a successor step clause for component `j`: the selector
`chooseIdent` (hole `0`) applied to the program counter `phi (0)` and, at entry
`k`, the entry update identifier (hole `k + 1`) applied to `phi`. -/
def urmStepBody {a : ℕ} (p : URMProgram a) :
    Tm (defnSig natAlgSig (p.instrs.size + 2) (urmStepHoleIdx p))
      (List.replicate a RType.o ++ [RType.arrow RType.o RType.o] ++ [RType.o])
      RType.o :=
  Tm.op (sig := defnSig natAlgSig (p.instrs.size + 2) (urmStepHoleIdx p))
    (Sum.inl (Sum.inr ⟨0, by omega⟩))
    (Fin.cons
      (defnApp RType.o RType.o (urmPhiVar (urmStepHoleIdx p) a) (tmNat 0))
      (fun k : Fin (List.replicate (p.instrs.size + 1) RType.o).length =>
        Tm.reind (get_replicate (p.instrs.size + 1) RType.o k).symm
          (Tm.op (sig := defnSig natAlgSig (p.instrs.size + 2) (urmStepHoleIdx p))
            (Sum.inl (Sum.inr ⟨k.val + 1, by
              have := k.isLt; simp only [List.length_replicate] at this; omega⟩))
            (Fin.cons (urmPhiVar (urmStepHoleIdx p) a) finZeroElim))))

/-- The identifiers filling a successor step clause's holes: hole `0` is the
selector `chooseIdent p.instrs.size o`; each hole `k + 1` is the entry update
`urmEntryIdent p j k`. -/
def urmStepChildren {a : ℕ} (p : URMProgram a) (j : Fin (1 + p.numRegs)) :
    (h : Fin (p.instrs.size + 2)) →
      RIdent natAlgSig (urmStepHoleIdx p h).1 (urmStepHoleIdx p h).2
  | ⟨0, _⟩ => chooseIdent p.instrs.size RType.o
  | ⟨k + 1, hk⟩ => urmEntryIdent p j ⟨k, by omega⟩

/-- The successor step clause for component `j`: the explicit definition whose
body is `urmStepBody` and whose holes are `urmStepChildren`. Its denotation
evaluates the selector `chooseIdent` at the previous program counter over the
per-instruction entry updates. -/
def urmStepClause {a : ℕ} (p : URMProgram a) (j : Fin (1 + p.numRegs)) :
    RIdent natAlgSig
      (List.replicate a RType.o ++ [RType.arrow RType.o RType.o] ++ [RType.o]) RType.o :=
  RIdent.defn ⟨p.instrs.size + 2, urmStepHoleIdx p, urmStepBody p⟩ (urmStepChildren p j)

/-- The parameter variable at input slot `i` of a base step clause: the `i`-th
parameter of the context `replicate a o ++ [] ++ [o]`, reindexed to `o`. Reads
the input numeral loaded at slot `i`. -/
def urmParamVar {a : ℕ} (i : Fin a) :
    Tm (defnSig natAlgSig 0 finZeroElim)
      (List.replicate a RType.o ++ ([] : List RType) ++ [RType.o]) RType.o :=
  Tm.reind
    ((get_finAppL (List.replicate a RType.o ++ ([] : List RType)) [RType.o]
        (finAppL (List.replicate a RType.o) ([] : List RType)
          ⟨i.val, by rw [List.length_replicate]; exact i.isLt⟩)).trans
      ((get_finAppL (List.replicate a RType.o) ([] : List RType)
          ⟨i.val, by rw [List.length_replicate]; exact i.isLt⟩).trans
        (get_replicate a RType.o ⟨i.val, by rw [List.length_replicate]; exact i.isLt⟩)))
    (Tm.var (finAppL (List.replicate a RType.o ++ ([] : List RType)) [RType.o]
      (finAppL (List.replicate a RType.o) ([] : List RType)
        ⟨i.val, by rw [List.length_replicate]; exact i.isLt⟩)))

/-- The base step clause for component `j`: the program counter starts at `0`;
register `j.val - 1` loads the input parameter of the slot mapping to it (via
the same constructive `List.find?` lookup as `URMState.init`), defaulting to
`0`. -/
def urmBaseClause {a : ℕ} (p : URMProgram a) (j : Fin (1 + p.numRegs)) :
    RIdent natAlgSig
      (List.replicate a RType.o ++ ([] : List RType) ++ [RType.o]) RType.o :=
  RIdent.defn ⟨0, finZeroElim,
    if h : j.val = 0 then tmZero
    else
      match (List.finRange a).find?
          (fun i => decide (p.inputRegs i = ⟨j.val - 1, by omega⟩)) with
      | some i => urmParamVar i
      | none => tmZero⟩
    finZeroElim

/-- Leivant III Lemma 6's per-component step clauses (section 3.2): the
`1 + p.numRegs` components of the simultaneous family — component `0` the
program counter, component `r + 1` the register `r` — each a ramified
recurrence on the step count. The base clause loads `URMState.init`; the
successor clause case-splits on the program counter and applies the
instruction's update. -/
def urmSteps {a : ℕ} (p : URMProgram a) :
    SimulSteps (1 + p.numRegs) (List.replicate a RType.o) RType.o :=
  fun j i =>
    match i with
    | false => urmBaseClause p j
    | true => urmStepClause p j

/-- The positivity of the component count `1 + p.numRegs`, the recurrence
hypothesis of the simultaneous family. -/
theorem urm_component_pos {a : ℕ} (p : URMProgram a) : 0 < 1 + p.numRegs :=
  Nat.add_pos_left Nat.one_pos p.numRegs

/-- Leivant III Lemma 6's program-counter component: the `0`-th projection of
the simultaneous family. -/
def sttIdent {a : ℕ} (p : URMProgram a) :
    RIdent natAlgSig
      (List.replicate a RType.o ++ [RType.omega (RType.arrow RType.o RType.o)]) RType.o :=
  simulProj (urm_component_pos p) (List.replicate a RType.o) RType.o (urmSteps p)
    ⟨0, urm_component_pos p⟩

/-- Leivant III Lemma 6's register components: the `r + 1`-th projection of the
simultaneous family tracks register `r`. -/
def regIdent {a : ℕ} (p : URMProgram a) (r : Fin p.numRegs) :
    RIdent natAlgSig
      (List.replicate a RType.o ++ [RType.omega (RType.arrow RType.o RType.o)]) RType.o :=
  simulProj (urm_component_pos p) (List.replicate a RType.o) RType.o (urmSteps p)
    ⟨r.val + 1, by have := r.isLt; omega⟩

/-- The parameter environment of the machine simulation: the input numerals
`v i` loaded at the `o` positions `replicate a o`. -/
def urmParamEnv {a : ℕ} (v : Fin a → ℕ) :
    ∀ k : Fin (List.replicate a RType.o).length,
      RType.interp (FreeAlg natAlgSig) ((List.replicate a RType.o).get k) :=
  fun k => cast (congrArg (RType.interp (FreeAlg natAlgSig)) (get_replicate a RType.o k).symm)
    (natToFreeAlg (v ⟨k.val, by
      have := k.isLt; simp only [List.length_replicate] at this; exact this⟩))

/-- The environment of the machine simulation at step count `t`: the input
numerals at the `o` positions and the step-count numeral `t` at the
`Ω (o → o)` position. -/
@[nolint unusedArguments]
def urmEnv {a : ℕ} (_p : URMProgram a) (v : Fin a → ℕ) (t : ℕ) :
    ∀ k : Fin (List.replicate a RType.o
        ++ [RType.omega (RType.arrow RType.o RType.o)] : Ctx RType).length,
      RType.interp (FreeAlg natAlgSig)
        ((List.replicate a RType.o
          ++ [RType.omega (RType.arrow RType.o RType.o)] : Ctx RType).get k) :=
  simulEnv (List.replicate a RType.o) RType.o (urmParamEnv v) (natToFreeAlg t)

/-- The recurrence-result variable of a successor step clause denotes the sole
function-valued recursive result `φvec ⟨0, _⟩` of the step environment: reading
`urmPhiVar` at `simulStepEnv … true pe φvec u` recovers the previous state as
the selector-indexed function. -/
theorem urmPhiVar_eval {a n : ℕ} {hI : Fin n → List RType × RType}
    (ih : ∀ j : Fin n, (∀ i : Fin (hI j).1.length,
        RType.interp (FreeAlg natAlgSig) ((hI j).1.get i)) →
        RType.interp (FreeAlg natAlgSig) (hI j).2)
    (pe : ∀ v : Fin (List.replicate a RType.o).length,
      RType.interp (FreeAlg natAlgSig) ((List.replicate a RType.o).get v))
    (φvec : Fin (natAlgSig.ar true) →
      RType.interp (FreeAlg natAlgSig) (RType.arrow RType.o RType.o))
    (u : FreeAlg natAlgSig) :
    (urmPhiVar hI a).eval (defnModel natAlgSig n hI ih)
        (simulStepEnv (List.replicate a RType.o) RType.o true pe φvec u)
      = φvec ⟨0, by decide⟩ := by
  refine eq_of_heq ?_
  rw [urmPhiVar]
  refine (Tm.eval_reind_var_heq (defnModel natAlgSig n hI ih) _ _).trans ?_
  rw [simulStepEnv]
  refine (snocEnv_heq_left (List.replicate a RType.o
      ++ List.replicate (natAlgSig.ar true) (RType.arrow RType.o RType.o)) RType.o
      (childEnv (List.replicate a RType.o) (RType.arrow RType.o RType.o)
        (natAlgSig.ar true) pe φvec) u
      (finAppR (List.replicate a RType.o)
        (List.replicate (natAlgSig.ar true) (RType.arrow RType.o RType.o))
        ⟨0, by decide⟩) _ rfl).trans ?_
  refine (heq_of_eq (childEnv_finAppR pe φvec ⟨0, by decide⟩ (by decide))).trans ?_
  exact (cast_heq _ _).trans (cast_heq _ _)

/-- The successor step clause for component `j` reduces to the selector
`chooseIdent p.instrs.size o` applied to the previous program counter `φ (0)`
over the per-instruction entry updates, each fed the state function `φ`. The
step's arg-vector reduction consumed by the machine-simulation invariant. -/
theorem urmStepClause_interp {a : ℕ} (p : URMProgram a) (j : Fin (1 + p.numRegs))
    (pe : ∀ v : Fin (List.replicate a RType.o).length,
      RType.interp (FreeAlg natAlgSig) ((List.replicate a RType.o).get v))
    (φvec : Fin (natAlgSig.ar true) →
      RType.interp (FreeAlg natAlgSig) (RType.arrow RType.o RType.o))
    (u : FreeAlg natAlgSig) :
    (urmStepClause p j).interp
        (simulStepEnv (List.replicate a RType.o) RType.o true pe φvec u)
      = (chooseIdent p.instrs.size RType.o).interp
          (chooseEnv p.instrs.size RType.o (φvec ⟨0, by decide⟩ (natToFreeAlg 0))
            (fun k => (urmEntryIdent p j ⟨k.val, by
                have h := k.isLt
                have _hl : (List.replicate (p.instrs.size + 1) RType.o).length
                  = p.instrs.size + 1 := by simp
                omega⟩).interp
              (Fin.cons (φvec ⟨0, by decide⟩) finZeroElim))) := by
  let m0 := defnModel natAlgSig (p.instrs.size + 2) (urmStepHoleIdx p)
    (fun h => (urmStepChildren p j h).interp)
  let e0 := simulStepEnv (List.replicate a RType.o) RType.o true pe φvec u
  refine congrArg (chooseIdent p.instrs.size RType.o).interp (funext (fun idx => ?_))
  induction idx using Fin.cases with
  | zero =>
    change (urmPhiVar (urmStepHoleIdx p) a).eval m0 e0 ((tmNat 0).eval m0 e0)
        = φvec ⟨0, by decide⟩ (natToFreeAlg 0)
    rw [urmPhiVar_eval, tmNat_eval]
  | succ k =>
    change (Tm.reind (get_replicate (p.instrs.size + 1) RType.o k).symm
          (Tm.op (sig := defnSig natAlgSig (p.instrs.size + 2) (urmStepHoleIdx p))
            (Sum.inl (Sum.inr ⟨k.val + 1, by
                have h := k.isLt
                have _hl : (List.replicate (p.instrs.size + 1) RType.o).length
                  = p.instrs.size + 1 := by simp
                omega⟩))
            (Fin.cons (urmPhiVar (urmStepHoleIdx p) a) finZeroElim))).eval m0 e0
        = chooseEnv p.instrs.size RType.o (φvec ⟨0, by decide⟩ (natToFreeAlg 0))
            (fun k => (urmEntryIdent p j ⟨k.val, by
                have h := k.isLt
                have _hl : (List.replicate (p.instrs.size + 1) RType.o).length
                  = p.instrs.size + 1 := by simp
                omega⟩).interp
              (Fin.cons (φvec ⟨0, by decide⟩) finZeroElim)) k.succ
    refine (Tm.eval_transport m0 e0 (get_replicate (p.instrs.size + 1) RType.o k).symm _).trans ?_
    refine eq_of_heq ((cast_heq _ _).trans ?_)
    refine HEq.trans (heq_of_eq (congrArg
      (urmEntryIdent p j ⟨k.val, by
                have h := k.isLt
                have _hl : (List.replicate (p.instrs.size + 1) RType.o).length
                  = p.instrs.size + 1 := by simp
                omega⟩).interp (funext (fun i => ?_))))
      ((cast_heq _ _).symm)
    induction i using Fin.cases with
    | zero => exact urmPhiVar_eval (fun h => (urmStepChildren p j h).interp) pe φvec u
    | succ i' => exact i'.elim0

/-- The parameter variable at input slot `i` of a base step clause denotes the
input numeral `v i`: reading `urmParamVar i` at the base step environment
recovers the loaded parameter. -/
theorem urmParamVar_eval {a : ℕ}
    (ih : ∀ j : Fin 0,
      (∀ i : Fin ((finZeroElim : Fin 0 → List RType × RType) j).1.length,
        RType.interp (FreeAlg natAlgSig) (((finZeroElim : Fin 0 → List RType × RType) j).1.get i)) →
        RType.interp (FreeAlg natAlgSig) ((finZeroElim : Fin 0 → List RType × RType) j).2)
    (v : Fin a → ℕ) (i : Fin a) (u : FreeAlg natAlgSig) :
    (urmParamVar i).eval (defnModel natAlgSig 0 finZeroElim ih)
        (simulStepEnv (List.replicate a RType.o) RType.o false (urmParamEnv v)
          finZeroElim u)
      = natToFreeAlg (v i) := by
  refine eq_of_heq ?_
  rw [urmParamVar]
  refine (Tm.eval_reind_var_heq (defnModel natAlgSig 0 finZeroElim ih) _ _).trans ?_
  rw [simulStepEnv]
  refine (snocEnv_heq_left (List.replicate a RType.o
      ++ List.replicate (natAlgSig.ar false) (RType.arrow RType.o RType.o)) RType.o
      (childEnv (List.replicate a RType.o) (RType.arrow RType.o RType.o)
        (natAlgSig.ar false) (urmParamEnv v) finZeroElim) u
      (finAppL (List.replicate a RType.o)
        (List.replicate (natAlgSig.ar false) (RType.arrow RType.o RType.o))
        ⟨i.val, by
          have h := i.isLt
          have hl : (List.replicate a RType.o).length = a := by simp
          omega⟩) _ rfl).trans ?_
  refine (heq_of_eq (childEnv_finAppL (urmParamEnv v) finZeroElim ⟨i.val, by
          have h := i.isLt
          have hl : (List.replicate a RType.o).length = a := by simp
          omega⟩)).trans ?_
  exact (cast_heq _ _).trans (cast_heq _ _)

/-- The componentwise reference solution of the URM simultaneous family after
`t` steps reads out to the program counter (component `0`) and registers
(component `r + 1`) of `URMState.runFor p (URMState.init p v) t`. Proved by
induction on `t`: the base clause loads `URMState.init` and the successor clause
executes `URMState.step` at the previous program counter. -/
theorem urm_simulSol_eq {a : ℕ} (p : URMProgram a) (v : Fin a → ℕ) :
    ∀ (t : ℕ) (j : Fin (1 + p.numRegs)),
      freeAlgToNat (simulSol (List.replicate a RType.o) RType.o (urmSteps p)
          (urmParamEnv v) t j)
        = if h : j.val = 0 then (URMState.runFor p (URMState.init p v) t).pc
          else (URMState.runFor p (URMState.init p v) t).regs
            ⟨j.val - 1, by omega⟩ := by
  intro t
  induction t with
  | zero =>
    intro j
    by_cases hj : j.val = 0
    · rw [dif_pos hj, URMState.runFor_zero]
      change freeAlgToNat ((urmBaseClause p j).interp _) = _
      rw [urmBaseClause, RIdent.interp_defn, dif_pos hj]
      exact congrArg freeAlgToNat (tmNat_eval _ _ 0)
    · rw [dif_neg hj, URMState.runFor_zero]
      change freeAlgToNat ((urmBaseClause p j).interp _) = _
      rw [urmBaseClause, RIdent.interp_defn, dif_neg hj]
      have key : ∀ (ih : ∀ j : Fin 0,
            (∀ i : Fin ((finZeroElim : Fin 0 → List RType × RType) j).1.length,
              RType.interp (FreeAlg natAlgSig)
                (((finZeroElim : Fin 0 → List RType × RType) j).1.get i)) →
              RType.interp (FreeAlg natAlgSig) ((finZeroElim : Fin 0 → List RType × RType) j).2)
          (u : FreeAlg natAlgSig) (fo : Option (Fin a)),
          freeAlgToNat ((match fo with | some i => urmParamVar i | none => tmZero).eval
              (defnModel natAlgSig 0 finZeroElim ih)
              (simulStepEnv (List.replicate a RType.o) RType.o false (urmParamEnv v)
                finZeroElim u))
            = (match fo with | some i => v i | none => 0) := by
        intro ih u fo
        cases fo with
        | some i =>
          exact (congrArg freeAlgToNat (urmParamVar_eval ih v i u)).trans
            (freeAlgToNat_natToFreeAlg (v i))
        | none =>
          exact (congrArg freeAlgToNat (tmNat_eval _ _ 0)).trans (freeAlgToNat_natToFreeAlg 0)
      exact key _ _ _
  | succ n ih =>
    intro j
    have hstep : URMState.runFor p (URMState.init p v) (n + 1)
        = URMState.step p (URMState.runFor p (URMState.init p v) n) :=
      (URMState.runFor_add p (URMState.init p v) n 1).trans rfl
    have hcomp : ∀ m : Fin (1 + p.numRegs),
        freeAlgToNat (simulSolFun j.pos (List.replicate a RType.o) RType.o (urmSteps p)
            (urmParamEnv v) n (natToFreeAlg m.val))
          = if h : m.val = 0 then (URMState.runFor p (URMState.init p v) n).pc
            else (URMState.runFor p (URMState.init p v) n).regs ⟨m.val - 1, by omega⟩ := by
      intro m
      rw [simulSolFun_numeral]
      exact ih m
    have hzval : freeAlgToNat (simulSolFun j.pos (List.replicate a RType.o) RType.o (urmSteps p)
          (urmParamEnv v) n (natToFreeAlg 0))
        = (URMState.runFor p (URMState.init p v) n).pc := by
      have h0 := hcomp ⟨0, j.pos⟩
      simpa using h0
    change freeAlgToNat ((urmStepClause p j).interp (simulStepEnv (List.replicate a RType.o)
      RType.o true (urmParamEnv v) (fun _v => simulSolFun j.pos (List.replicate a RType.o)
        RType.o (urmSteps p) (urmParamEnv v) n) (natToFreeAlg j.val))) = _
    rw [urmStepClause_interp, hstep]
    have hz : (fun _v : Fin (natAlgSig.ar true) => simulSolFun j.pos (List.replicate a RType.o)
          RType.o (urmSteps p) (urmParamEnv v) n) ⟨0, by decide⟩ (natToFreeAlg 0)
        = natToFreeAlg (URMState.runFor p (URMState.init p v) n).pc :=
      (natToFreeAlg_freeAlgToNat _).symm.trans (congrArg natToFreeAlg hzval)
    by_cases hpc : (URMState.runFor p (URMState.init p v) n).pc < p.instrs.size
    · rw [chooseIdent_interp p.instrs.size RType.o _ _
        ⟨(URMState.runFor p (URMState.init p v) n).pc, by omega⟩ hz]
      rw [urmEntryIdent, dif_pos hpc]
      cases hi : p.instrs[(URMState.runFor p (URMState.init p v) n).pc]'hpc with
      | assign i c =>
        simp only [URMState.step, dif_pos hpc, hi]
        rw [urmInstrUpdate]
        by_cases hj0 : j.val = 0
        · rw [if_pos hj0, dif_pos hj0, urmSuccUpdate_interp, hcomp j, dif_pos hj0]
        · rw [if_neg hj0, dif_neg hj0]
          by_cases hjt : j.val = i.val + 1
          · rw [if_pos hjt, urmConstUpdate_interp, freeAlgToNat_natToFreeAlg,
              Function.update_apply,
              if_pos (show (⟨j.val - 1, by omega⟩ : Fin p.numRegs) = i from
                Fin.ext (show j.val - 1 = i.val by omega))]
          · rw [if_neg hjt, urmSelfUpdate_interp, hcomp j, dif_neg hj0,
              Function.update_apply,
              if_neg (fun he => hjt (by have h2 : j.val - 1 = i.val := Fin.ext_iff.mp he; omega))]
      | inc i =>
        simp only [URMState.step, dif_pos hpc, hi]
        rw [urmInstrUpdate]
        by_cases hj0 : j.val = 0
        · rw [if_pos hj0, dif_pos hj0, urmSuccUpdate_interp, hcomp j, dif_pos hj0]
        · rw [if_neg hj0, dif_neg hj0]
          by_cases hjt : j.val = i.val + 1
          · rw [if_pos hjt, urmSuccUpdate_interp, hcomp j, dif_neg hj0,
              Function.update_apply,
              if_pos (show (⟨j.val - 1, by omega⟩ : Fin p.numRegs) = i from
                Fin.ext (show j.val - 1 = i.val by omega))]
            congr 2
            exact Fin.ext (show j.val - 1 = i.val by omega)
          · rw [if_neg hjt, urmSelfUpdate_interp, hcomp j, dif_neg hj0,
              Function.update_apply,
              if_neg (fun he => hjt (by have h2 : j.val - 1 = i.val := Fin.ext_iff.mp he; omega))]
      | dec i =>
        simp only [URMState.step, dif_pos hpc, hi]
        rw [urmInstrUpdate]
        by_cases hj0 : j.val = 0
        · rw [if_pos hj0, dif_pos hj0, urmSuccUpdate_interp, hcomp j, dif_pos hj0]
        · rw [if_neg hj0, dif_neg hj0]
          by_cases hjt : j.val = i.val + 1
          · rw [if_pos hjt, urmDecUpdate_interp, hcomp j, dif_neg hj0,
              Function.update_apply,
              if_pos (show (⟨j.val - 1, by omega⟩ : Fin p.numRegs) = i from
                Fin.ext (show j.val - 1 = i.val by omega))]
            congr 2
            exact Fin.ext (show j.val - 1 = i.val by omega)
          · rw [if_neg hjt, urmSelfUpdate_interp, hcomp j, dif_neg hj0,
              Function.update_apply,
              if_neg (fun he => hjt (by have h2 : j.val - 1 = i.val := Fin.ext_iff.mp he; omega))]
      | jumpZ i l₁ l₂ =>
        simp only [URMState.step, dif_pos hpc, hi]
        rw [urmInstrUpdate]
        by_cases hj0 : j.val = 0
        · rw [if_pos hj0, dif_pos hj0, urmJumpUpdate_interp,
            hcomp ⟨i.val + 1, by have := i.isLt; omega⟩, dif_neg (Nat.succ_ne_zero i.val)]
          have hii : (⟨i.val + 1 - 1, by omega⟩ : Fin p.numRegs) = i :=
            Fin.ext (show i.val + 1 - 1 = i.val by omega)
          rw [hii]
          by_cases hz0 : (URMState.runFor p (URMState.init p v) n).regs i = 0
          · rw [if_pos hz0, if_pos hz0, freeAlgToNat_natToFreeAlg]
          · rw [if_neg hz0, if_neg hz0, freeAlgToNat_natToFreeAlg]
        · rw [if_neg hj0, dif_neg hj0, urmSelfUpdate_interp, hcomp j, dif_neg hj0]
      | stop =>
        simp only [URMState.step, dif_pos hpc, hi]
        rw [urmInstrUpdate]
        by_cases hj0 : j.val = 0
        · rw [if_pos hj0, dif_pos hj0, urmSelfUpdate_interp, hcomp j, dif_pos hj0]
        · rw [if_neg hj0, dif_neg hj0, urmSelfUpdate_interp, hcomp j, dif_neg hj0]
    · rw [chooseIdent_interp_ge p.instrs.size RType.o _ _
        (URMState.runFor p (URMState.init p v) n).pc (by omega) hz]
      rw [show (Fin.last p.instrs.size) = ⟨p.instrs.size, by omega⟩ from rfl,
        urmEntryIdent, dif_neg (Nat.lt_irrefl p.instrs.size)]
      have hid : URMState.step p (URMState.runFor p (URMState.init p v) n)
          = URMState.runFor p (URMState.init p v) n := by
        simp only [URMState.step, dif_neg hpc]
      rw [urmSelfUpdate_interp, hcomp j, hid]

/-- Leivant III Lemma 6 (section 3.2, DOI `10.1016/S0168-0072(98)00040-2`): the
ramified simultaneous recurrence simulates the zero-test URM. After `t` steps
the program-counter component `sttIdent` reads out to the program counter and
each register component `regIdent r` to register `r` of
`URMState.runFor p (URMState.init p v) t`. -/
theorem urm_simul_interp {a : ℕ} (p : URMProgram a) (v : Fin a → ℕ) (t : ℕ) :
    freeAlgToNat ((sttIdent p).interp (urmEnv p v t))
        = (URMState.runFor p (URMState.init p v) t).pc ∧
      ∀ r : Fin p.numRegs,
        freeAlgToNat ((regIdent p r).interp (urmEnv p v t))
          = (URMState.runFor p (URMState.init p v) t).regs r := by
  refine ⟨?_, ?_⟩
  · rw [sttIdent, urmEnv, simulProj_interp]
    have h := urm_simulSol_eq p v t ⟨0, urm_component_pos p⟩
    rwa [dif_pos rfl] at h
  · intro r
    rw [regIdent, urmEnv, simulProj_interp]
    have h := urm_simulSol_eq p v t ⟨r.val + 1, by have := r.isLt; omega⟩
    rw [dif_neg (Nat.succ_ne_zero r.val)] at h
    exact h.trans (congrArg (URMState.runFor p (URMState.init p v) t).regs (Fin.ext rfl))

/-- The numeral `k` as a term at an object sort `s` over a definition signature:
the `k`-fold successor of the nullary constructor at `s`. The object-sort
generalization of `tmNat` (`GebLean/Ramified/Definability/Simultaneous.lean`)
to an arbitrary object sort. -/
def numObjTm {n : Nat} {h : Fin n → List RType × RType} {Γ : Ctx RType}
    (s : RType) (hs : s.IsObj) : Nat → Tm (defnSig natAlgSig n h) Γ s
  | 0 => tmZeroObj s hs
  | k + 1 => tmSuccObj s hs (numObjTm s hs k)

/-- A numeral term at an object sort evaluates to the carrier copy of the
numeral. Proved by induction on the numeral through the constructor
interpretation. -/
theorem numObjTm_eval {n : Nat} {hI : Fin n → List RType × RType}
    (ih : ∀ j : Fin n, (∀ i : Fin (hI j).1.length,
        RType.interp (FreeAlg natAlgSig) ((hI j).1.get i)) →
        RType.interp (FreeAlg natAlgSig) (hI j).2)
    {Γ : Ctx RType} (s : RType) (hs : s.IsObj)
    (ρ : (defnModel natAlgSig n hI ih).Env Γ) : (k : Nat) →
    (numObjTm s hs k).eval (defnModel natAlgSig n hI ih) ρ
      = cast (RType.interp_isObj (FreeAlg natAlgSig) hs).symm (natToFreeAlg k)
  | 0 => by
    refine congrArg (cast (RType.interp_isObj (FreeAlg natAlgSig) hs).symm) ?_
    exact congrArg (FreeAlg.mk (A := natAlgSig) false) (funext fun i => i.elim0)
  | k + 1 => by
    refine congrArg (cast (RType.interp_isObj (FreeAlg natAlgSig) hs).symm) ?_
    refine congrArg (FreeAlg.mk (A := natAlgSig) true) (funext fun i => ?_)
    induction i using Fin.cases with
    | zero =>
      exact eq_of_heq
        (HEq.trans (cast_heq _ _)
          (HEq.trans (heq_of_eq (numObjTm_eval ih s hs ρ k)) (cast_heq _ _)))
    | succ i' => exact i'.elim0

/-- The constant identifier at an object sort `s` returning the numeral `k`,
ignoring its environment: the explicit definition whose body is `numObjTm`. Its
denotation is the carrier copy of the numeral (`constObjIdent_interp`). The
constant multiple `c` of the eq. (8) clock is `constObjIdent (Ω ω) _ _ c`. -/
def constObjIdent (s : RType) (hs : s.IsObj) (Γ : Ctx RType) (k : Nat) :
    RIdent natAlgSig Γ s :=
  RIdent.defn ⟨0, finZeroElim, numObjTm s hs k⟩ finZeroElim

/-- The constant identifier denotes the carrier copy of its numeral. -/
theorem constObjIdent_interp (s : RType) (hs : s.IsObj) (Γ : Ctx RType) (k : Nat)
    (ρ : ∀ i : Fin Γ.length, RType.interp (FreeAlg natAlgSig) (Γ.get i)) :
    (constObjIdent s hs Γ k).interp ρ
      = cast (RType.interp_isObj (FreeAlg natAlgSig) hs).symm (natToFreeAlg k) := by
  rw [constObjIdent, RIdent.interp_defn]
  exact numObjTm_eval _ s hs ρ k

/-- The staggered input context of the eq. (8) assembly over a base object sort
`β`: `stagCtx 0 β = []` and
`stagCtx (n + 1) β = stagCtx n (Ω β) ++ [Ω (β → β)]`. Position `i` of
`stagCtx n β` carries the input sort `Ω (θᵢ → θᵢ)` with `θᵢ = Ω^{n-1-i} β`, so
that the per-input size at `θᵢ` and the descending partial sums chain through
the addition copies `θ', Ω θ' → θ'` (`addAtIdent`). Novel packaging. -/
def stagCtx : Nat → RType → Ctx RType
  | 0, _β => []
  | n + 1, β => stagCtx n (RType.omega β) ++ [RType.omega (expFun β)]

/-- The staggered input context of length `n` has length `n`. -/
theorem stagCtx_length : (n : Nat) → (β : RType) → (stagCtx n β).length = n
  | 0, _β => rfl
  | n + 1, β => by
    rw [stagCtx, List.length_append, stagCtx_length n (RType.omega β)]
    rfl

/-- Every sort of the staggered input context is an object sort: each is an
`Omega` sort (`Ω (β → β)` at the appended tail, an `Omega` sort recursively). -/
theorem stagCtx_forall_isObj :
    (n : Nat) → (β : RType) → ∀ x ∈ stagCtx n β, x.IsObj
  | 0, _β => by intro x hx; simp [stagCtx] at hx
  | n + 1, β => by
    intro x hx
    rw [stagCtx, List.mem_append] at hx
    rcases hx with h | h
    · exact stagCtx_forall_isObj n (RType.omega β) x h
    · rw [List.mem_singleton] at h; subst h; exact Or.inr rfl

/-- The base object sort of the eq. (8) assembly at clock height `q`:
`clockSort q (Ω ω)` with `ω = Ω (o → o)` the count sort of the machine
simultaneous family. The total size sum lands here, and `twoPowIdent q (Ω ω)`
lowers it to `Ω ω`. -/
def machineBaseSort (q : ℕ) : RType :=
  clockSort q (RType.omega (RType.omega (RType.arrow RType.o RType.o)))

/-- The base object sort is an object sort (`clockSort_isObj` at the `Omega`
sort `Ω ω`). -/
theorem machineBaseSort_isObj (q : ℕ) : (machineBaseSort q).IsObj :=
  clockSort_isObj q _ (Or.inr rfl)

/-- Leivant III Lemma 6's realizer input context (paper section 3.2, eq. (8)):
`a` copies of the staggered input sort `Ω (θᵢ → θᵢ)`, with
`θᵢ = Ω^{a-1-i}(machineBaseSort q)`. Position `i` carries input `i` at
`Ω (θᵢ → θᵢ)`; the size `sz` at `θᵢ` and the descending addition copies chain
the per-input sizes into the total at `machineBaseSort q`, from which
`twoPowIdent q` and the constant multiple build the clock. Every entry is an
object sort beyond the tower sorts. -/
def machineCtx (a q : ℕ) : Ctx RType :=
  stagCtx a (machineBaseSort q)

/-- The realizer input context has length `a`. -/
theorem machineCtx_length (a q : ℕ) : (machineCtx a q).length = a :=
  stagCtx_length a _

/-- Every entry of the realizer input context is an object sort. -/
theorem machineCtx_isObj (a q : ℕ) :
    ∀ i : Fin (machineCtx a q).length, ((machineCtx a q).get i).IsObj :=
  fun i => stagCtx_forall_isObj a _ _ ((machineCtx a q).get_mem i)

/-- The projection identifier reading a context variable: at context `Γ` and
result `Γ.get i`, the explicit definition whose body is the variable `i`. Its
denotation is the environment at position `i`. -/
def projIdent {A : AlgSig} (Γ : Ctx RType) (i : Fin Γ.length) :
    RIdent A Γ (Γ.get i) :=
  RIdent.defn ⟨0, finZeroElim, Tm.var i⟩ finZeroElim

/-- The numeric reading of a value at an `Omega` sort is `freeAlgToNat`: the
carrier-copy transport of `objToNat` at an `Omega` sort is the identity. -/
theorem objToNat_omega (t : RType) (x : RType.interp (FreeAlg natAlgSig) (RType.omega t)) :
    objToNat (Or.inr rfl : (RType.omega t).IsObj) x = freeAlgToNat x :=
  congrArg freeAlgToNat (eq_of_heq (cast_heq _ _))

/-- The projection identifier transported to a known sort: `projIdent Γ i` cast
along `Γ.get i = σ`. Its denotation is the environment at `i` transported along
the same equality. -/
def projIdentEq {A : AlgSig} (Γ : Ctx RType) (i : Fin Γ.length) (σ : RType)
    (h : Γ.get i = σ) : RIdent A Γ σ :=
  h ▸ projIdent Γ i

/-- The transported projection denotes the environment at its position. -/
theorem projIdentEq_interp {A : AlgSig} (Γ : Ctx RType) (i : Fin Γ.length)
    (σ : RType) (h : Γ.get i = σ)
    (ρ : ∀ k : Fin Γ.length, RType.interp (FreeAlg A) (Γ.get k)) :
    (projIdentEq Γ i σ h).interp ρ
      = cast (congrArg (RType.interp (FreeAlg A)) h) (ρ i) := by
  subst h; rfl

/-- The hole contexts of a saturated identifier application: hole `0` is the
applied identifier `f` at its own context `Δ` and result `τ`; each hole `k + 1`
is the `k`-th argument identifier at the outer context `Γ` and the argument's
sort `Δ.get k`. -/
def applyHoleIdx (Γ Δ : Ctx RType) (τ : RType) :
    Fin (Δ.length + 1) → List RType × RType
  | ⟨0, _⟩ => (Δ, τ)
  | ⟨k + 1, h⟩ => (Γ, Δ.get ⟨k, by omega⟩)

/-- The defining term of a saturated identifier application: hole `0` (the
identifier `f`) applied to the argument vector, where the `j`-th argument is
hole `j + 1` (the `j`-th argument identifier) applied to the outer context's
variables. -/
def applyBody {A : AlgSig} (Γ Δ : Ctx RType) (τ : RType) :
    Tm (defnSig A (Δ.length + 1) (applyHoleIdx Γ Δ τ)) Γ τ :=
  Tm.op (sig := defnSig A (Δ.length + 1) (applyHoleIdx Γ Δ τ))
    (Sum.inl (Sum.inr ⟨0, Nat.succ_pos _⟩))
    (fun j : Fin Δ.length =>
      Tm.op (sig := defnSig A (Δ.length + 1) (applyHoleIdx Γ Δ τ))
        (Sum.inl (Sum.inr ⟨j.val + 1, by omega⟩))
        (fun i : Fin Γ.length => Tm.var i))

/-- The identifiers filling a saturated identifier application's holes: hole `0`
is the applied identifier `f`; each hole `k + 1` is the `k`-th argument
identifier. -/
def applyChildren {A : AlgSig} {Γ Δ : Ctx RType} {τ : RType} (f : RIdent A Δ τ)
    (args : (k : Fin Δ.length) → RIdent A Γ (Δ.get k)) :
    (h : Fin (Δ.length + 1)) →
      RIdent A (applyHoleIdx Γ Δ τ h).1 (applyHoleIdx Γ Δ τ h).2
  | ⟨0, _⟩ => f
  | ⟨k + 1, h⟩ => args ⟨k, by omega⟩

/-- Application of an identifier `f : RIdent A Δ τ` to an argument vector, each
argument an identifier over the outer context `Γ`: the explicit definition
whose body is `applyBody` and whose holes are `applyChildren`. Its denotation
applies `f`'s denotation to the argument identifiers' denotations. The
combinator form used to compose the ladder identifiers of the eq. (8) assembly.
Novel packaging. -/
def applyIdent {A : AlgSig} {Γ Δ : Ctx RType} {τ : RType} (f : RIdent A Δ τ)
    (args : (k : Fin Δ.length) → RIdent A Γ (Δ.get k)) : RIdent A Γ τ :=
  RIdent.defn ⟨Δ.length + 1, applyHoleIdx Γ Δ τ, applyBody Γ Δ τ⟩
    (applyChildren f args)

/-- The denotation of a saturated identifier application applies `f`'s
denotation to the argument identifiers' denotations at the outer environment. -/
theorem applyIdent_interp {A : AlgSig} {Γ Δ : Ctx RType} {τ : RType}
    (f : RIdent A Δ τ) (args : (k : Fin Δ.length) → RIdent A Γ (Δ.get k))
    (ρ : ∀ i : Fin Γ.length, RType.interp (FreeAlg A) (Γ.get i)) :
    (applyIdent f args).interp ρ = f.interp (fun j => (args j).interp ρ) :=
  rfl

/-- The denotation of a one-argument application. -/
theorem applyIdent1_interp {A : AlgSig} {Γ : Ctx RType} {σ τ : RType}
    (f : RIdent A [σ] τ) (g : RIdent A Γ σ)
    (ρ : ∀ i : Fin Γ.length, RType.interp (FreeAlg A) (Γ.get i)) :
    (applyIdent f (Fin.cons g finZeroElim)).interp ρ
      = f.interp (Fin.cons (g.interp ρ) finZeroElim) := by
  rw [applyIdent_interp]
  refine congrArg f.interp (funext (fun j => ?_))
  refine Fin.cases ?_ (fun j' => j'.elim0) j
  rfl

/-- The denotation of a two-argument application. -/
theorem applyIdent2_interp {A : AlgSig} {Γ : Ctx RType} {σ₁ σ₂ τ : RType}
    (f : RIdent A [σ₁, σ₂] τ) (g₁ : RIdent A Γ σ₁) (g₂ : RIdent A Γ σ₂)
    (ρ : ∀ i : Fin Γ.length, RType.interp (FreeAlg A) (Γ.get i)) :
    (applyIdent f (Fin.cons g₁ (Fin.cons g₂ finZeroElim))).interp ρ
      = f.interp (Fin.cons (g₁.interp ρ) (Fin.cons (g₂.interp ρ) finZeroElim)) := by
  rw [applyIdent_interp]
  refine congrArg f.interp (funext (fun j => ?_))
  refine Fin.cases ?_ (fun j' => Fin.cases ?_ (fun j'' => j''.elim0) j') j
  · rfl
  · rfl

/-- The staggered size sum of the eq. (8) assembly over a base object sort `β`:
`sizeFold 0 β` is the numeral `0`, and `sizeFold (n + 1) β` adds the size of the
last input (`szAtIdent β` at the appended variable, landing at `β`) to the
descending partial sum of the first `n` inputs (`sizeFold n (Ω β)`, landing at
`Ω β`) through the addition copy `addAtIdent β : β, Ω β → β`. Its numeric
denotation is `∑ᵢ (countᵢ + 1)` (`sizeFold_interp`). Novel packaging. -/
def sizeFold : (n : Nat) → (β : RType) → (hβ : β.IsObj) →
    RIdent natAlgSig (stagCtx n β) β
  | 0, β, hβ => constObjIdent β hβ (stagCtx 0 β) 0
  | n + 1, β, hβ =>
    applyIdent (addAtIdent β hβ)
      (Fin.cons
        (applyIdent (szAtIdent β hβ)
          (Fin.cons
            (projIdentEq (stagCtx n (RType.omega β) ++ [RType.omega (expFun β)])
              (finAppR (stagCtx n (RType.omega β)) [RType.omega (expFun β)] ⟨0, Nat.zero_lt_one⟩)
              (RType.omega (expFun β))
              (get_finAppR (stagCtx n (RType.omega β)) [RType.omega (expFun β)]
                ⟨0, Nat.zero_lt_one⟩))
            finZeroElim))
        (Fin.cons
          (applyIdent (sizeFold n (RType.omega β) (Or.inr rfl))
            (fun k => projIdentEq (stagCtx n (RType.omega β) ++ [RType.omega (expFun β)])
              (finAppL (stagCtx n (RType.omega β)) [RType.omega (expFun β)] k)
              ((stagCtx n (RType.omega β)).get k)
              (get_finAppL (stagCtx n (RType.omega β)) [RType.omega (expFun β)] k)))
          finZeroElim))

/-- The constant identifier's numeric reading is its numeral. -/
theorem objToNat_constObjIdent (s : RType) (hs : s.IsObj) (Γ : Ctx RType) (k : Nat)
    (ρ : ∀ i : Fin Γ.length, RType.interp (FreeAlg natAlgSig) (Γ.get i)) :
    objToNat hs ((constObjIdent s hs Γ k).interp ρ) = k := by
  rw [constObjIdent_interp]
  unfold objToNat
  exact (congrArg freeAlgToNat (eq_of_heq ((cast_heq _ _).trans (cast_heq _ _)))).trans
    (freeAlgToNat_natToFreeAlg k)

/-- The numeric reading of the `i`-th input of the staggered context: the count
of the value at position `i`, an object sort. -/
def stagCount (n : Nat) (β : RType)
    (ρ : ∀ i : Fin (stagCtx n β).length,
      RType.interp (FreeAlg natAlgSig) ((stagCtx n β).get i))
    (i : Fin (stagCtx n β).length) : ℕ :=
  objToNat (stagCtx_forall_isObj n β _ ((stagCtx n β).get_mem i)) (ρ i)

/-- The sum over the positions of a snoc context splits into the sum over the
prefix positions and the value at the appended position. -/
theorem fin_sum_snoc {M : Type*} [AddCommMonoid M] (l : List RType) (x : RType)
    (f : Fin (l ++ [x]).length → M) :
    ∑ i, f i
      = (∑ k : Fin l.length, f (finAppL l [x] k))
        + f (finAppR l [x] ⟨0, Nat.zero_lt_one⟩) := by
  have hlen : (l ++ [x]).length = l.length + 1 := by simp [List.length_append]
  rw [← Equiv.sum_comp (finCongr hlen).symm f, Fin.sum_univ_castSucc]
  refine congrArg₂ (· + ·) ?_ (congrArg f (Fin.ext (by simp [finAppR])))
  exact Finset.sum_congr rfl (fun k _ => congrArg f (Fin.ext rfl))

/-- The staggered size sum denotes the total input size `∑ᵢ (countᵢ + 1)`:
each per-input size counts `countᵢ + 1` (`szAtIdent_interp`), and the descending
addition copies sum them. Proved by induction on the input count. -/
theorem sizeFold_interp : (n : Nat) → (β : RType) → (hβ : β.IsObj) →
    (ρ : ∀ i : Fin (stagCtx n β).length,
      RType.interp (FreeAlg natAlgSig) ((stagCtx n β).get i)) →
    objToNat hβ ((sizeFold n β hβ).interp ρ) = ∑ i, (stagCount n β ρ i + 1)
  | 0, _β, _hβ, _ρ => by
    rw [sizeFold, objToNat_constObjIdent]
    exact (Finset.sum_eq_zero (fun i _ => absurd i.2 (by simp [stagCtx]))).symm
  | n + 1, β, hβ, ρ => by
    rw [sizeFold, applyIdent_interp, addAtIdent_interp_env]
    have hsz : objToNat hβ
        ((applyIdent (szAtIdent β hβ)
          (Fin.cons
            (projIdentEq (stagCtx n (RType.omega β) ++ [RType.omega (expFun β)])
              (finAppR (stagCtx n (RType.omega β)) [RType.omega (expFun β)]
                ⟨0, Nat.zero_lt_one⟩)
              (RType.omega (expFun β))
              (get_finAppR (stagCtx n (RType.omega β)) [RType.omega (expFun β)]
                ⟨0, Nat.zero_lt_one⟩))
            finZeroElim)).interp ρ)
        = stagCount (n + 1) β ρ
            (finAppR (stagCtx n (RType.omega β)) [RType.omega (expFun β)]
              ⟨0, Nat.zero_lt_one⟩) + 1 := by
      rw [applyIdent_interp, szAtIdent_interp]
      change freeAlgToNat ((projIdentEq (stagCtx n (RType.omega β) ++ [RType.omega (expFun β)])
          (finAppR (stagCtx n (RType.omega β)) [RType.omega (expFun β)] ⟨0, Nat.zero_lt_one⟩)
          (RType.omega (expFun β))
          (get_finAppR (stagCtx n (RType.omega β)) [RType.omega (expFun β)]
            ⟨0, Nat.zero_lt_one⟩)).interp ρ) + 1 = _
      rw [projIdentEq_interp, ← objToNat_omega (expFun β), stagCount]
      exact congrArg (· + 1) (objToNat_cast _ _ _ _)
    have hpre : freeAlgToNat
        ((applyIdent (sizeFold n (RType.omega β) (Or.inr rfl))
          (fun k => projIdentEq (stagCtx n (RType.omega β) ++ [RType.omega (expFun β)])
            (finAppL (stagCtx n (RType.omega β)) [RType.omega (expFun β)] k)
            ((stagCtx n (RType.omega β)).get k)
            (get_finAppL (stagCtx n (RType.omega β)) [RType.omega (expFun β)] k))).interp ρ)
        = ∑ k : Fin (stagCtx n (RType.omega β)).length,
            (stagCount (n + 1) β ρ
              (finAppL (stagCtx n (RType.omega β)) [RType.omega (expFun β)] k) + 1) := by
      rw [← objToNat_omega β, applyIdent_interp, sizeFold_interp n (RType.omega β) (Or.inr rfl)]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      congr 1
      rw [stagCount, stagCount, projIdentEq_interp]
      exact objToNat_cast _ _ _ _
    change objToNat hβ
          ((applyIdent (szAtIdent β hβ)
            (Fin.cons
              (projIdentEq (stagCtx n (RType.omega β) ++ [RType.omega (expFun β)])
                (finAppR (stagCtx n (RType.omega β)) [RType.omega (expFun β)] ⟨0, Nat.zero_lt_one⟩)
                (RType.omega (expFun β))
                (get_finAppR (stagCtx n (RType.omega β)) [RType.omega (expFun β)]
                  ⟨0, Nat.zero_lt_one⟩))
              finZeroElim)).interp ρ)
        + freeAlgToNat
          ((applyIdent (sizeFold n (RType.omega β) (Or.inr rfl))
            (fun k => projIdentEq (stagCtx n (RType.omega β) ++ [RType.omega (expFun β)])
              (finAppL (stagCtx n (RType.omega β)) [RType.omega (expFun β)] k)
              ((stagCtx n (RType.omega β)).get k)
              (get_finAppL (stagCtx n (RType.omega β)) [RType.omega (expFun β)] k))).interp ρ)
      = ∑ i, (stagCount (n + 1) β ρ i + 1)
    rw [hsz, hpre]
    exact (Nat.add_comm _ _).trans
      (fin_sum_snoc (stagCtx n (RType.omega β)) (RType.omega (expFun β))
        (fun i => stagCount (n + 1) β ρ i + 1)).symm

/-- Leivant III eq. (8)'s clock `c × 2_q(sz(a))` (paper section 3.2, p. 221) as
an identifier over the realizer input context: the constant `c` (a numeral at
`Ω ω`) times `twoPowIdent q` of the staggered size sum, through the
multiplication copy `mulAtIdent ω : (Ω ω)² → ω`. Its denotation lands at the
count sort `ω = Ω (o → o)`. -/
def machineClock {a : ℕ} (c q : ℕ) :
    RIdent natAlgSig (machineCtx a q) (RType.omega (RType.arrow RType.o RType.o)) :=
  applyIdent (mulAtIdent (RType.omega (RType.arrow RType.o RType.o)) (Or.inr rfl))
    (Fin.cons
      (constObjIdent (RType.omega (RType.omega (RType.arrow RType.o RType.o))) (Or.inr rfl)
        (machineCtx a q) c)
      (Fin.cons
        (applyIdent
          (twoPowIdent q (RType.omega (RType.omega (RType.arrow RType.o RType.o))) (Or.inr rfl))
          (Fin.cons (sizeFold a (machineBaseSort q) (machineBaseSort_isObj q)) finZeroElim))
        finZeroElim))

/-- Leivant III eq. (8)'s clock denotes `c × 2_q` of the total input size: its
numeric reading is `c * tower q (∑ᵢ (countᵢ + 1))`. Combines
`mulAtIdent_interp_env`, `twoPowIdent_interp`, and `sizeFold_interp`. -/
theorem machineClock_interp {a : ℕ} (c q : ℕ)
    (ρ : ∀ i : Fin (machineCtx a q).length,
      RType.interp (FreeAlg natAlgSig) ((machineCtx a q).get i)) :
    freeAlgToNat ((machineClock c q).interp ρ)
      = c * GebLean.tower q (∑ i, (stagCount a (machineBaseSort q) ρ i + 1)) := by
  rw [machineClock, ← objToNat_omega (RType.arrow RType.o RType.o), applyIdent2_interp,
    mulAtIdent_interp_env]
  have hc : freeAlgToNat
      ((constObjIdent (RType.omega (RType.omega (RType.arrow RType.o RType.o))) (Or.inr rfl)
        (machineCtx a q) c).interp ρ) = c := by
    rw [← objToNat_omega (RType.omega (RType.arrow RType.o RType.o)), objToNat_constObjIdent]
  have h2 : freeAlgToNat
      ((applyIdent
        (twoPowIdent q (RType.omega (RType.omega (RType.arrow RType.o RType.o))) (Or.inr rfl))
        (Fin.cons (sizeFold a (machineBaseSort q) (machineBaseSort_isObj q))
          finZeroElim)).interp ρ)
      = GebLean.tower q (∑ i, (stagCount a (machineBaseSort q) ρ i + 1)) := by
    rw [← objToNat_omega (RType.omega (RType.arrow RType.o RType.o)), applyIdent1_interp,
      twoPowIdent_interp]
    exact congrArg (GebLean.tower q) (sizeFold_interp a (machineBaseSort q)
      (machineBaseSort_isObj q) ρ)
  change freeAlgToNat
      ((constObjIdent (RType.omega (RType.omega (RType.arrow RType.o RType.o))) (Or.inr rfl)
        (machineCtx a q) c).interp ρ)
      * freeAlgToNat
        ((applyIdent
          (twoPowIdent q (RType.omega (RType.omega (RType.arrow RType.o RType.o))) (Or.inr rfl))
          (Fin.cons (sizeFold a (machineBaseSort q) (machineBaseSort_isObj q))
            finZeroElim)).interp ρ) = _
  rw [hc, h2]

/-- The numeric environment over the realizer input context: position `i` carries
the numeral of `v i`, transported to the carrier copy of its object sort. -/
def machineEnv {a : ℕ} (q : ℕ) (v : Fin a → ℕ) :
    (standardModel (higherOrder natAlgSig)).Env (machineCtx a q) :=
  fun i => cast (RType.interp_isObj (FreeAlg natAlgSig) (machineCtx_isObj a q i)).symm
    (natToFreeAlg (v ⟨i.val, Nat.lt_of_lt_of_eq i.isLt (machineCtx_length a q)⟩))

/-- The numeric reading of the environment at position `i` is `v` at that
position. -/
theorem freeAlgToNat_machineEnv {a : ℕ} (q : ℕ) (v : Fin a → ℕ)
    (i : Fin (machineCtx a q).length) :
    objToNat (machineCtx_isObj a q i) (machineEnv q v i)
      = v ⟨i.val, Nat.lt_of_lt_of_eq i.isLt (machineCtx_length a q)⟩ := by
  unfold objToNat machineEnv
  refine (congrArg freeAlgToNat (eq_of_heq ((cast_heq _ _).trans (cast_heq _ _)))).trans
    (freeAlgToNat_natToFreeAlg _)

/-- Cast an identifier along a result-sort equality. -/
def castResult {A : AlgSig} {Γ : Ctx RType} {σ σ' : RType} (h : σ = σ')
    (f : RIdent A Γ σ) : RIdent A Γ σ' :=
  h ▸ f

/-- The cast identifier's denotation is the transported denotation. -/
theorem castResult_interp {A : AlgSig} {Γ : Ctx RType} {σ σ' : RType} (h : σ = σ')
    (f : RIdent A Γ σ)
    (ρ : ∀ i : Fin Γ.length, RType.interp (FreeAlg A) (Γ.get i)) :
    (castResult h f).interp ρ = cast (congrArg (RType.interp (FreeAlg A)) h) (f.interp ρ) := by
  subst h; rfl

/-- The parameter-loading coercion for input `i` (eq. (8)'s `δ_{Ω(η→η)}`):
`deltaIdent` (δ) applied to the `i`-th input variable, reading its numeral back
at the base sort `o`. -/
def deltaArg {a : ℕ} (q : ℕ) (i : Fin a) : RIdent natAlgSig (machineCtx a q) RType.o :=
  applyIdent
    (deltaIdent natAlgSig false rfl
      ((machineCtx a q).get ⟨i.val, Nat.lt_of_lt_of_eq i.isLt (machineCtx_length a q).symm⟩)
      (machineCtx_isObj a q ⟨i.val, Nat.lt_of_lt_of_eq i.isLt (machineCtx_length a q).symm⟩))
    (Fin.cons
      (projIdent (machineCtx a q)
        ⟨i.val, Nat.lt_of_lt_of_eq i.isLt (machineCtx_length a q).symm⟩)
      finZeroElim)

/-- The sort at a below-`a` position of the register context is `o`. -/
theorem machineDom_get_lt {a : ℕ}
    (k : Fin (List.replicate a RType.o
      ++ [RType.omega (RType.arrow RType.o RType.o)]).length) (h : k.val < a) :
    (List.replicate a RType.o
      ++ [RType.omega (RType.arrow RType.o RType.o)]).get k = RType.o := by
  rw [get_append_lt _ _ k (by rw [List.length_replicate]; exact h)]
  exact get_replicate a RType.o _

/-- The sort at an at-or-beyond-`a` position of the register context is `ω`. -/
theorem machineDom_get_ge {a : ℕ}
    (k : Fin (List.replicate a RType.o
      ++ [RType.omega (RType.arrow RType.o RType.o)]).length) (h : ¬ k.val < a) :
    (List.replicate a RType.o
      ++ [RType.omega (RType.arrow RType.o RType.o)]).get k
      = RType.omega (RType.arrow RType.o RType.o) := by
  rw [get_append_ge _ _ k (by rw [List.length_replicate]; exact h)]
  exact List.mem_singleton.mp (List.get_mem _ _)

/-- The realizer's argument vector for `regIdent`: the `a` parameter coercions at
the base-sort positions and the clock at the count position. -/
def machineArgs {a : ℕ} (c q : ℕ)
    (k : Fin (List.replicate a RType.o
      ++ [RType.omega (RType.arrow RType.o RType.o)]).length) :
      RIdent natAlgSig (machineCtx a q)
        ((List.replicate a RType.o
          ++ [RType.omega (RType.arrow RType.o RType.o)]).get k) :=
  if h : k.val < a then
    castResult (machineDom_get_lt k h).symm (deltaArg q ⟨k.val, h⟩)
  else
    castResult (machineDom_get_ge k h).symm (machineClock c q)

/-- Leivant III eq. (8)'s realizer as an identifier: the output register
component `regIdent p p.outputReg` fed the parameter coercions and the clock. -/
def machineIdent {a : ℕ} (p : URMProgram a) (c q : ℕ) :
    RIdent natAlgSig (machineCtx a q) RType.o :=
  applyIdent (regIdent p p.outputReg) (machineArgs c q)

/-- Leivant III eq. (8)'s realizer (paper section 3.2, p. 221) as a morphism of
`RMRecCat natAlgSig` over the staggered input context: the sole term applies the
output-register component of the machine simulation, fed the parameter coercions
`δ` on each input and the clock `c × 2_q(sz(a))`. -/
def machineRealizer {a : ℕ} (p : URMProgram a) (c q : ℕ) :
    Hom (higherOrder natAlgSig) (interpQuotRel (higherOrder natAlgSig))
      (machineCtx a q) [RType.o] :=
  identHom (machineIdent p c q)

/-- The parameter coercion on the numeric environment reads the input numeral. -/
theorem deltaArg_machineEnv {a : ℕ} (q : ℕ) (v : Fin a → ℕ) (i : Fin a) :
    (deltaArg q i).interp (machineEnv q v) = natToFreeAlg (v i) := by
  rw [deltaArg, applyIdent1_interp, deltaIdent_interp]
  exact eq_of_heq ((cast_heq _ _).trans ((cast_heq _ _).trans
    (heq_of_eq (congrArg (fun j => natToFreeAlg (v j)) (Fin.ext rfl)))))

/-- Leivant III Lemma 6 with eq. (8) (paper section 3.2, DOI
`10.1016/S0168-0072(98)00040-2`): the realizer defines `f`. If `p` computes `f`
within time `c × tower q` of the maximum input (in the `runFor`-stabilized form),
then the realizer's denotation, read through `freeAlgToNat`, is `f v` at every
input `v`. The clock denotation is `c * tower q (∑ᵢ (vᵢ + 1))` by the ladder
interpretation lemmas; `maxOfNat_le_sum_succ` and `clock_mono` bound the maximum
input by it, and the machine invariant `urm_simul_interp` at the clock count
closes the read-off.

The `s1.2` embedding argument (the zero-test URM against Leivant's register
machines) is the fidelity justification recorded in the module docstring. The
eq. (8) sort reconciliation is a presentation adaptation: the paper's "Let
θ = Ωo" display carries surface sort slips, reconciled here by the staggered
`machineCtx` sorts and the count sort `ω = Ω(o → o)`. -/
theorem urm_ramified_definable {a : ℕ} (p : URMProgram a)
    (f : (Fin a → ℕ) → ℕ) (c q : ℕ)
    (hf : ∀ (v : Fin a → ℕ) (t : ℕ),
      c * GebLean.tower q (Fin.maxOfNat a v) ≤ t →
      (URMState.runFor p (URMState.init p v) t).regs p.outputReg = f v) :
    ∀ v, freeAlgToNat ((machineRealizer p c q).eval (machineEnv q v) 0) = f v := by
  intro v
  set t := freeAlgToNat ((machineClock c q).interp (machineEnv q v)) with ht
  have hTval : t = c * GebLean.tower q (∑ i : Fin a, (v i + 1)) := by
    rw [ht, machineClock_interp]
    refine congrArg (fun s => c * GebLean.tower q s) ?_
    rw [← Equiv.sum_comp (finCongr (machineCtx_length a q)) (fun i => v i + 1)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine congrArg (· + 1) ?_
    exact (freeAlgToNat_machineEnv q v i).trans (congrArg v (Fin.ext rfl))
  have hbound : c * GebLean.tower q (Fin.maxOfNat a v) ≤ t := by
    rw [hTval]
    exact Definability.clock_mono c q (Definability.maxOfNat_le_sum_succ a v)
  have henv : (fun k => (machineArgs c q k).interp (machineEnv q v)) = urmEnv p v t := by
    funext k
    change (machineArgs c q k).interp (machineEnv q v)
      = snocEnv (List.replicate a RType.o) (RType.omega (RType.arrow RType.o RType.o))
          (urmParamEnv v) (natToFreeAlg t) k
    refine finApp_cases
      (motive := fun k => (machineArgs c q k).interp (machineEnv q v)
        = snocEnv (List.replicate a RType.o) (RType.omega (RType.arrow RType.o RType.o))
            (urmParamEnv v) (natToFreeAlg t) k)
      (fun i => ?_) (fun j => ?_) k
    · have hlt : (finAppL (List.replicate a RType.o)
          [RType.omega (RType.arrow RType.o RType.o)] i).val < a := by
        have h := i.isLt; simp only [List.length_replicate] at h; simpa [finAppL] using h
      simp only [machineArgs]
      rw [dif_pos hlt, castResult_interp, deltaArg_machineEnv q v ⟨_, hlt⟩]
      refine eq_of_heq ((cast_heq _ _).trans ?_)
      refine HEq.symm ((snocEnv_heq_left (List.replicate a RType.o)
        (RType.omega (RType.arrow RType.o RType.o)) (urmParamEnv v) (natToFreeAlg t)
        i _ rfl).trans ?_)
      rw [urmParamEnv]
      exact (cast_heq _ _).trans
        (heq_of_eq (congrArg (fun j => natToFreeAlg (v j)) (Fin.ext rfl)))
    · have hge : ¬ (finAppR (List.replicate a RType.o)
          [RType.omega (RType.arrow RType.o RType.o)] j).val < a := by
        simp only [finAppR, List.length_replicate]; omega
      simp only [machineArgs]
      rw [dif_neg hge, castResult_interp]
      refine eq_of_heq ((cast_heq _ _).trans ?_)
      refine HEq.symm ((snocEnv_heq_right (List.replicate a RType.o)
        (RType.omega (RType.arrow RType.o RType.o)) (urmParamEnv v) (natToFreeAlg t)
        _ (by simp only [finAppR]; omega)).trans ?_)
      rw [ht]
      exact heq_of_eq
        (natToFreeAlg_freeAlgToNat ((machineClock c q).interp (machineEnv q v)))
  rw [machineRealizer, identHom_eval, machineIdent, applyIdent_interp, henv,
    (urm_simul_interp p v t).2 p.outputReg]
  exact hf v t hbound

end GebLean.Ramified
