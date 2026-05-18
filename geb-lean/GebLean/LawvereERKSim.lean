import GebLean.LawvereER
import GebLean.Utilities.ZeroTestURM

/-!
# erToK: ER → K^sim_2 via zero-test URM simulation

The compiler half of the erToK construction: emit a
`URMProgram` from an `ERMor1 a` term such that running the
URM long enough produces `e.interp v` in the output
register.

## Main definitions

- `URMInstrRaw`: ℕ-indexed instruction intermediate used
  by compiler combinators before the final register-count
  is known.
- `URMInstrRaw.toBounded`: total conversion from a raw
  instruction to a `URMInstr r`, given a bound proof on
  every register index appearing in the raw instruction.

## References

- Tourlakis 2018 §0.1.0.37 (pp. 15–16): URM semantics.
- Tourlakis 2018 p. 19: worked URM examples (M template
  for `λx.x`, N template for `λx.x+1`, R^XY_Z template
  for `λxy.xy`).
- Tourlakis 2018 p. 20: Loop-to-URM translation template
  with per-Loop scratch register B.
- Tourlakis 2018 p. 21: bounded-recursion URM template.
- Tourlakis 2018 §0.1.0.42 (p. 18): `f ∈ E^n` is
  URM-computable within time bound in `E^n`.
- Spec §5 (ER → URM compiler):
  `docs/superpowers/specs/2026-05-16-er-to-k-via-cslib-urm-design.md`.

## Tags

URM, compiler, ER, Tourlakis, simulation
-/

namespace GebLean

namespace LawvereERKSim

open GebLean.ZeroTestURM

/-- Raw URM instruction with ℕ-indexed registers and
absolute PC labels. Compiler combinators emit raw
instructions during composition; the final
`CompiledFragment` constructs the `URMInstr numRegs`
array by converting each raw instruction through
`URMInstrRaw.toBounded` once `numRegs` is known.

The five constructors mirror `URMInstr` exactly except
register indices are plain ℕ instead of `Fin r`. Tourlakis
2018 §0.1.0.37 p. 16. -/
inductive URMInstrRaw : Type
  /-- `assignR i c` is Tourlakis's `V_i ← c`. -/
  | assignR (i c : ℕ) : URMInstrRaw
  /-- `incR i` is Tourlakis's `V_i ← V_i + 1`. -/
  | incR (i : ℕ) : URMInstrRaw
  /-- `decR i` is Tourlakis's `V_i ← V_i ∸ 1`. -/
  | decR (i : ℕ) : URMInstrRaw
  /-- `jumpZR i l₁ l₂` is Tourlakis's two-target
  zero-test jump. -/
  | jumpZR (i l₁ l₂ : ℕ) : URMInstrRaw
  /-- `stopR` is Tourlakis's halt. -/
  | stopR : URMInstrRaw
  deriving Repr, DecidableEq, Inhabited

/-- The maximum register index referenced by a raw
instruction, plus 1. Provides the lower bound on
`numRegs` needed to type the instruction as
`URMInstr numRegs`. -/
def URMInstrRaw.regBound : URMInstrRaw → ℕ
  | .assignR i _ => i + 1
  | .incR i => i + 1
  | .decR i => i + 1
  | .jumpZR i _ _ => i + 1
  | .stopR => 0

/-- Convert a raw instruction to a bounded `URMInstr r`,
given a bound proof on the raw instruction's register
index. Total function; the bound proof is consumed at the
`Fin r` construction site. -/
def URMInstrRaw.toBounded
    (r : ℕ) (instr : URMInstrRaw)
    (h : instr.regBound ≤ r) : URMInstr r :=
  match instr, h with
  | .assignR i c, h => .assign ⟨i, h⟩ c
  | .incR i, h => .inc ⟨i, h⟩
  | .decR i, h => .dec ⟨i, h⟩
  | .jumpZR i l₁ l₂, h => .jumpZ ⟨i, h⟩ l₁ l₂
  | .stopR, _ => .stop

/-- All raw instructions in a list have register bound
≤ `r`. -/
def URMRaw.boundedBy (r : ℕ) (l : List URMInstrRaw) :
    Prop :=
  ∀ ins ∈ l, URMInstrRaw.regBound ins ≤ r

/-- Batch-convert a `URMRaw.boundedBy r`-witnessed list
of raw instructions to an `Array (URMInstr r)`. Uses
`List.attach` to carry the membership proof pointwise. -/
def URMInstr.fromRawList (r : ℕ) (l : List URMInstrRaw)
    (h : URMRaw.boundedBy r l) :
    Array (URMInstr r) :=
  (l.attach.map (fun ⟨ins, hmem⟩ =>
    URMInstrRaw.toBounded r ins (h ins hmem))).toArray

end LawvereERKSim

end GebLean
