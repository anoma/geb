# T2 plan adversarial review — round 4

## Summary

Round 4 empirically verifies the two round-3 fixes (S1'
invariant proofs in `compileFrag_sub`; S2'
`URMInstr.fromRawList` batch conversion) by reproducing the
plan's combinator bodies inside `lean_run_code` against
current mathlib. All three atomic combinators
(`compileFrag_succ`, `compileFrag_proj`, `compileFrag_sub`)
elaborate cleanly with the proposed Lean text. The plan's
namespace placement, step renumbering (Steps 2.1–2.6), and
cross-references for the new Step 2.4 declarations
(`URMRaw.boundedBy`, `URMInstr.fromRawList`) are internally
consistent. The round-1 deferrals B3 and M3 remain
acceptable; nothing in the round-3 fixes affects them.

Counts: 0 blockers, 0 serious, 0 minor, 1 nit.

The plan is converged for the purposes of this review cycle.

## Round-3 fix verification

| Round-3 ID | Status | Empirical evidence |
| --- | --- | --- |
| S1' (`fin_cases` invariant proofs in `compileFrag_sub`) | fix verified | `lean_run_code` harness confirms the three patterns close their goals — see § Empirical verification S1' below. |
| S2' (`URMInstr.fromRawList` replaces per-element `toBounded`) | fix verified | `lean_run_code` harness confirms (a) `URMInstr.fromRawList` is well-typed, (b) the three `hBound` proofs (12, 11, 19 `rfl` cases) discharge against `URMRaw.boundedBy`, (c) full combinator bodies elaborate. See § Empirical verification S2' below. |

## Empirical verification S1'

Harness (full mathlib import; `Mathlib.Tactic.FinCases` alone
is insufficient because `Fintype (Fin 2)` is required and
lives elsewhere — the project's `LawvereERKSim.lean` will
transitively import mathlib via `GebLean/Utilities/ZeroTestURM.lean`,
so this is a faithful reproduction of the compile context):

```lean
import Mathlib

example :
    Function.Injective
      (Fin.cases (⟨2, by decide⟩ : Fin 6)
        (Fin.cases (⟨3, by decide⟩ : Fin 6) Fin.elim0) : Fin 2 → Fin 6) := by
  intro p q hpq
  fin_cases p <;> fin_cases q <;>
    first | rfl | (exfalso; revert hpq; decide)

example :
    ∀ p : Fin 2,
      (Fin.cases (⟨2, by decide⟩ : Fin 6)
        (Fin.cases (⟨3, by decide⟩ : Fin 6) Fin.elim0) : Fin 2 → Fin 6) p
        ≠ (⟨1, by decide⟩ : Fin 6) := by
  intro p hp
  fin_cases p <;> exact absurd hp (by decide)

example :
    ∀ p : Fin 2,
      (Fin.cases (⟨2, by decide⟩ : Fin 6)
        (Fin.cases (⟨3, by decide⟩ : Fin 6) Fin.elim0) : Fin 2 → Fin 6) p
        ≠ (⟨0, by decide⟩ : Fin 6) := by
  intro p hp
  fin_cases p <;> exact absurd hp (by decide)
```

Result (verbatim): `{"success":true,"timed_out":false,"diagnostics":[]}`.

Each of the three invariant proofs (`inputRegs_inj`,
`outputReg_not_input`, `zeroReg_not_input`) closes against
the round-3 patterns. The exact text from the plan body at
Step 5.4 (plan lines 1254–1266) matches verbatim.

## Empirical verification S2'

Harness reproducing all Task-2 internal helpers and all
three round-3-rewritten Task-5 combinator bodies:

```lean
import Mathlib

namespace TestHarness

inductive URMInstr (r : ℕ) : Type
  | assign (i : Fin r) (c : ℕ) : URMInstr r
  | inc (i : Fin r) : URMInstr r
  | dec (i : Fin r) : URMInstr r
  | jumpZ (i : Fin r) (l₁ l₂ : ℕ) : URMInstr r
  | stop : URMInstr r
  deriving Repr, DecidableEq, Inhabited

inductive URMInstrRaw : Type
  | assignR (i c : ℕ) : URMInstrRaw
  | incR (i : ℕ) : URMInstrRaw
  | decR (i : ℕ) : URMInstrRaw
  | jumpZR (i l₁ l₂ : ℕ) : URMInstrRaw
  | stopR : URMInstrRaw
  deriving Repr, DecidableEq, Inhabited

def URMInstrRaw.regBound : URMInstrRaw → ℕ
  | .assignR i _ => i + 1
  | .incR i => i + 1
  | .decR i => i + 1
  | .jumpZR i _ _ => i + 1
  | .stopR => 0

def URMInstrRaw.toBounded
    (r : ℕ) (instr : URMInstrRaw) (h : instr.regBound ≤ r) :
    URMInstr r :=
  match instr, h with
  | .assignR i c, h => .assign ⟨i, h⟩ c
  | .incR i, h => .inc ⟨i, h⟩
  | .decR i, h => .dec ⟨i, h⟩
  | .jumpZR i l₁ l₂, h => .jumpZ ⟨i, h⟩ l₁ l₂
  | .stopR, _ => .stop

def URMRaw.boundedBy (r : ℕ) (l : List URMInstrRaw) : Prop :=
  ∀ ins ∈ l, URMInstrRaw.regBound ins ≤ r

def URMInstr.fromRawList (r : ℕ) (l : List URMInstrRaw)
    (h : URMRaw.boundedBy r l) :
    Array (URMInstr r) :=
  (l.attach.map (fun ⟨ins, hmem⟩ =>
    URMInstrRaw.toBounded r ins (h ins hmem))).toArray

def URMRaw.goto (l : ℕ) : URMInstrRaw := .jumpZR 0 l l

def URMRaw.transferLoop (pcBase src dst : ℕ) : List URMInstrRaw :=
  [ .jumpZR src (pcBase + 4) (pcBase + 1),
    .decR src, .incR dst, URMRaw.goto pcBase ]

def URMRaw.preservingTransfer
    (pcBase src dst tmp : ℕ) : List URMInstrRaw :=
  [ .jumpZR src (pcBase + 5) (pcBase + 1),
    .decR src, .incR dst, .incR tmp, URMRaw.goto pcBase,
    .jumpZR tmp (pcBase + 9) (pcBase + 6),
    .decR tmp, .incR src, URMRaw.goto (pcBase + 5) ]

structure CF (a : ℕ) where
  numRegs : ℕ
  numRegs_pos : 0 < numRegs
  inputRegs : Fin a → Fin numRegs
  outputReg : Fin numRegs
  instrs : Array (URMInstr numRegs)
  inputRegs_inj : Function.Injective inputRegs
  outputReg_not_input : ∀ i, inputRegs i ≠ outputReg
  zeroReg_not_input : ∀ i, inputRegs i ≠ ⟨0, numRegs_pos⟩
  zeroReg_not_output : outputReg ≠ ⟨0, numRegs_pos⟩

def compileFrag_succ : CF 1 :=
  let rawList : List URMInstrRaw :=
    (.assignR 0 0)
      :: (URMRaw.preservingTransfer 1 2 1 3
          ++ [.incR 1, .stopR])
  have hBound : URMRaw.boundedBy 4 rawList := by
    intro ins hmem
    simp only [rawList, URMRaw.preservingTransfer,
      URMRaw.goto, List.mem_cons, List.mem_append,
      List.mem_singleton] at hmem
    rcases hmem with
      rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  { numRegs := 4
    numRegs_pos := by decide
    inputRegs := fun _ => ⟨2, by decide⟩
    outputReg := ⟨1, by decide⟩
    instrs := URMInstr.fromRawList 4 rawList hBound
    inputRegs_inj := by
      intro i j _
      exact Subsingleton.elim _ _
    outputReg_not_input := by
      intro i h
      have hv : (⟨2, by decide⟩ : Fin 4)
        = ⟨1, by decide⟩ := h
      exact absurd (Fin.mk.inj_iff.mp hv).1 (by decide)
    zeroReg_not_input := by
      intro i h
      have hv : (⟨2, by decide⟩ : Fin 4)
        = ⟨0, by decide⟩ := h
      exact absurd (Fin.mk.inj_iff.mp hv).1 (by decide)
    zeroReg_not_output := by decide }

def compileFrag_proj {k : ℕ} (i : Fin k) : CF k :=
  let rawList : List URMInstrRaw :=
    (.assignR 0 0)
      :: ((URMRaw.preservingTransfer 1 (2 + i.val) 1 (2 + k))
          ++ [.stopR])
  have hBound : URMRaw.boundedBy (k + 3) rawList := by
    intro ins hmem
    simp only [rawList, URMRaw.preservingTransfer,
      URMRaw.goto, List.mem_cons, List.mem_append,
      List.mem_singleton] at hmem
    rcases hmem with
      rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl
    all_goals (simp only [URMInstrRaw.regBound];
      have : i.val < k := i.isLt; omega)
  { numRegs := k + 3
    numRegs_pos := by omega
    inputRegs := fun j => ⟨2 + j.val, by omega⟩
    outputReg := ⟨1, by omega⟩
    instrs := URMInstr.fromRawList (k + 3) rawList hBound
    inputRegs_inj := by
      intro p q hpq
      have : (⟨2 + p.val, by omega⟩ : Fin (k + 3))
        = ⟨2 + q.val, by omega⟩ := hpq
      apply Fin.ext
      have h := (Fin.mk.inj_iff.mp this).1
      omega
    outputReg_not_input := by
      intro p hp
      have : (⟨2 + p.val, by omega⟩ : Fin (k + 3))
        = ⟨1, by omega⟩ := hp
      have h := (Fin.mk.inj_iff.mp this).1
      omega
    zeroReg_not_input := by
      intro p hp
      have : (⟨2 + p.val, by omega⟩ : Fin (k + 3))
        = ⟨0, by omega⟩ := hp
      have h := (Fin.mk.inj_iff.mp this).1
      omega
    zeroReg_not_output := by
      intro h
      have hh : (⟨0, by omega⟩ : Fin (k + 3))
        = ⟨1, by omega⟩ := h
      have hh' := (Fin.mk.inj_iff.mp hh).1
      omega }

def compileFrag_sub : CF 2 :=
  let rawList : List URMInstrRaw :=
    (.assignR 0 0)
      :: ((URMRaw.preservingTransfer 1 2 1 4)
          ++ (URMRaw.transferLoop 10 3 5)
          ++ [ .jumpZR 5 18 15,
               .decR 5,
               .decR 1,
               URMRaw.goto 14,
               .stopR ])
  have hBound : URMRaw.boundedBy 6 rawList := by
    intro ins hmem
    simp only [rawList, URMRaw.preservingTransfer,
      URMRaw.transferLoop, URMRaw.goto,
      List.mem_cons, List.mem_append,
      List.mem_singleton] at hmem
    rcases hmem with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  { numRegs := 6
    numRegs_pos := by decide
    inputRegs :=
      Fin.cases (⟨2, by decide⟩ : Fin 6)
        (Fin.cases (⟨3, by decide⟩ : Fin 6) Fin.elim0)
    outputReg := ⟨1, by decide⟩
    instrs := URMInstr.fromRawList 6 rawList hBound
    inputRegs_inj := by
      intro p q hpq
      fin_cases p <;> fin_cases q <;>
        first | rfl | (exfalso; revert hpq; decide)
    outputReg_not_input := by
      intro p hp
      fin_cases p <;> exact absurd hp (by decide)
    zeroReg_not_input := by
      intro p hp
      fin_cases p <;> exact absurd hp (by decide)
    zeroReg_not_output := by decide }

end TestHarness
```

Result (verbatim): `{"success":true,"timed_out":false,"diagnostics":[]}`.

Confirms:

- `URMInstr.fromRawList` is well-typed against the plan's
  Step 2.4 definition.
- `compileFrag_succ`'s `hBound` discharges through 12 `rfl`
  cases (1 cons + 9 preservingTransfer + 1 incR + 1 stopR).
- `compileFrag_proj`'s `hBound` discharges through 11 `rfl`
  cases (1 cons + 9 preservingTransfer + 1 stopR) via the
  `i.val < k := i.isLt; omega` discharge.
- `compileFrag_sub`'s `hBound` discharges through 19 `rfl`
  cases (1 cons + 9 preservingTransfer + 4 transferLoop +
  5 tail) under `all_goals decide`.
- The `let rawList := ...; have hBound : ... ; { ... }`
  layout (with `hBound` introduced outside the structure
  literal) elaborates correctly inside a `def` body.
- All four invariant proofs for each combinator close.

A separate harness verified the plan's secondary fallback
suggestion (`by intro ins hmem; revert hmem; decide` for
`compileFrag_succ`'s closed-`Nat` `rawList`) also closes
the goal — consistent with the plan's note at lines
1085–1092.

## Plan structural consistency

- **Step numbering.** Steps 2.1–2.6 are contiguous and
  non-duplicated. Step 2.4 introduces the new helpers;
  Steps 2.5 and 2.6 are the renumbered verify/commit steps.
- **Namespace placement.** All new declarations
  (`URMRaw.boundedBy`, `URMInstr.fromRawList`) are appended
  inside `namespace LawvereERKSim` (per Step 2.1's
  "Append inside `namespace LawvereERKSim`" directive,
  which Step 2.4 inherits). Fully qualified names are
  `GebLean.LawvereERKSim.URMRaw.boundedBy` and
  `GebLean.LawvereERKSim.URMInstr.fromRawList`.
- **Cross-references.** `URMInstr.fromRawList` is
  referenced in Steps 5.2 (line 1043), 5.3 (line 1131),
  5.4 (line 1253); `URMRaw.boundedBy` is referenced in
  Step 5 `hBound` proof headings at lines 1026, 1117,
  1237. Commit-body footer at Step 2.6 (line 673) cites
  `URMInstr.fromRawList over List.attach`. All consistent.
- **Step 12.4 named-declaration list.** Lists 15 spec-named
  declarations including `URMInstrRaw` and
  `URMInstrRaw.toBounded`; `URMInstr.fromRawList` and
  `URMRaw.boundedBy` are correctly omitted as internal
  helpers. The grep regex at line 2258 does not match
  these new declarations, consistent with their internal
  status.

## B3 deferral re-evaluation

Round 1 flagged five `sorry` placeholders in Tasks 6.3,
7.1, 8.1, 11.1, 11.2. Round 2 accepted the deferral; round
3 re-evaluated and accepted. Round 4: nothing in the round-3
fixes touches these tasks. The deferral continues to hold.

## M3 deferral re-evaluation

Round 1 flagged repeated `Tourlakis 2018 §X p. Y` citations
across declaration docstrings. Round 2 accepted the
deferral. Round 4: the round-3 fixes add no new docstrings;
the deferral continues to hold.

## Nits

### N1. Internal-helpers paragraph at lines 2246–2252 omits the new declarations

The paragraph at plan lines 2246–2252 enumerates
"additional emission/internal helpers introduced by this
plan" — `URMInstr.reindex`, `URMInstr.shiftPC`,
`URMRaw.goto`, `URMRaw.transferLoop`,
`URMRaw.transferLoopLen`, `URMRaw.preservingTransfer`,
`URMRaw.preservingTransferLen`, `URMInstrRaw.regBound`,
`CompiledFragment.zeroReg`. The new Step 2.4 helpers
(`URMRaw.boundedBy`, `URMInstr.fromRawList`) belong in
this list. Strictly informational — the Step 12.4 grep
already tolerates "or more" matches, so this does not
affect verification correctness; only the prose listing
is stale.

Suggested addition: insert `URMRaw.boundedBy` and
`URMInstr.fromRawList` alphabetically into the
parenthetical list at plan line 2247–2251.

## Sign-off

Plan converged on round-4 review (zero blocker, zero
serious).

The two round-3 findings (S1' invariant proofs, S2'
`URMInstr.fromRawList` batch conversion) have been
addressed and empirically verified against current
mathlib via `lean_run_code`. One minor documentary nit
(N1, internal-helpers paragraph) is informational and
does not require a round 5.
