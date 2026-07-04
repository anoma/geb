import GebLean.Ramified.Algebras
import GebLean.Ramified.Definability.Simultaneous
import GebLean.Utilities.ZeroTestURM

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

end GebLean.Ramified
