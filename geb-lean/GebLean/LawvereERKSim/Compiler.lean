import GebLean.LawvereER
import GebLean.Utilities.ZeroTestURM
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases

/-!
# LawvereERKSim — compiler

Per-constructor URM-fragment compilation for the ER → URM half of the erToK
construction. Emits a `URMProgram` from an `ERMor1 a` term; correctness lives
in sibling submodules under `GebLean/LawvereERKSim/`.

## Main definitions

- `URMInstrRaw`, `URMInstrRaw.regBound`, `URMInstrRaw.toBounded`,
  `URMInstrRaw.boundedBy`, `URMInstrRaw.toBoundedArray`,
  `URMInstrRaw.reindexShift`: raw-instruction intermediate and its conversion
  to `URMInstr r`.
- `CompiledFragment`: bundled sub-fragment with invariants (`numRegs_pos`,
  `zeroReg_not_input`, `zeroReg_not_output`, `lastInstr_isStop`).
- `CompiledFragment.zeroReg`, `URMRaw.goto`, `URMRaw.transferLoop`,
  `URMRaw.transferLoopLen`, `URMRaw.preservingTransfer`,
  `URMRaw.preservingTransferLen`: emission helpers.
- `compileFrag_zero`, `compileFrag_succ`, `compileFrag_proj`,
  `compileFrag_sub`, `compileFrag_comp`, `compileFrag_bsum`,
  `compileFrag_bprod`: per-ER-constructor compilers.
- `compileFrag_sub_inputRegs`, `compileFrag_comp_subBlock`,
  `bsum_prologueSrc`, `bsum_prologueBlock`, `bsum_zeroSweep`: per-compiler
  building blocks.
- `gsPrefixSum`, `toRawOfBounded`: arithmetic and conversion helpers.
- `compileERFrag`, `compileER`, `compileER_numRegs`, `compileER_runtime`:
  top-level compiler and runtime witness.

## Main statements

- `URMInstrRaw.toBoundedArray_size`, `URMInstrRaw.toBoundedArray_getElem`,
  `URMInstrRaw.toBoundedArray_getElem?`,
  `URMInstrRaw.toBoundedArray_back?_of_last_stopR`: bounded-array indexing
  and last-instruction lemmas.
- `URMInstrRaw.toBounded_congr`: conversion congruence.
- `regBound_toRawOfBounded_le`, `regBound_reindexShift_le_offset_add`:
  register-bound preservation.
- `gsPrefixSum_succ_eq`, `gsPrefixSum_mono`: arithmetic lemmas on the
  prefix-sum helper.
- `boundedBy_preservingTransfer`, `boundedBy_transferLoop`,
  `boundedBy_compileFrag_comp_subBlock`, `boundedBy_bsum_prologueBlock`,
  `boundedBy_bsum_zeroSweep`: per-emission-helper register-bound theorems.

## References

- Tourlakis 2018 `PR-complexity-topics.pdf` §0.1.0.37 (URM kernel), p. 19
  (succ), §0.1.0.43 (Ritchie–Cobham).
- Spec: `docs/superpowers/specs/2026-05-19-lawvere-er-k-sim-file-split-design.md`.
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

/-- Congruence of `toBounded` along an equality on the raw
instruction. The boundedness witnesses are
proof-irrelevant for fixed `r` and matching raw instructions,
so the result equality follows by transporting the proof
across the raw equality. -/
theorem URMInstrRaw.toBounded_congr (r : ℕ)
    {ins ins' : URMInstrRaw} (h_raw : ins = ins')
    (h : ins.regBound ≤ r) (h' : ins'.regBound ≤ r) :
    URMInstrRaw.toBounded r ins h = URMInstrRaw.toBounded r ins' h' := by
  subst h_raw; rfl

/-- All raw instructions in a list have register bound
≤ `r`. -/
def URMInstrRaw.boundedBy (r : ℕ) (l : List URMInstrRaw) :
    Prop :=
  ∀ ins ∈ l, URMInstrRaw.regBound ins ≤ r

/-- Batch-convert a `URMInstrRaw.boundedBy r`-witnessed
list of raw instructions to an `Array (URMInstr r)`.
Uses `List.attach` to carry the membership proof
pointwise. -/
def URMInstrRaw.toBoundedArray (r : ℕ)
    (l : List URMInstrRaw)
    (h : URMInstrRaw.boundedBy r l) :
    Array (URMInstr r) :=
  (l.attach.map (fun ⟨ins, hmem⟩ =>
    URMInstrRaw.toBounded r ins (h ins hmem))).toArray

/-- If a raw instruction list ends with `.stopR`, then its
bounded-array form ends with `.stop`. Used by combinators
to discharge `CompiledFragment.lastInstr_isStop`. -/
private theorem URMInstrRaw.toBoundedArray_back?_of_last_stopR
    {r : ℕ} {l : List URMInstrRaw}
    (h : URMInstrRaw.boundedBy r l)
    (hl : l.getLast? = some .stopR) :
    (URMInstrRaw.toBoundedArray r l h).back? = some .stop := by
  rw [List.getLast?_eq_some_iff] at hl
  obtain ⟨l', hl'⟩ := hl
  subst hl'
  unfold URMInstrRaw.toBoundedArray
  rw [List.back?_toArray, List.attach_append]
  simp only [List.map_append, List.map_cons, List.map_nil,
    List.attach_cons, List.attach_nil, List.getLast?_concat]
  rfl

/-- The size of `toBoundedArray r l h` equals `l.length`. -/
private theorem URMInstrRaw.toBoundedArray_size
    (r : ℕ) (l : List URMInstrRaw)
    (h : URMInstrRaw.boundedBy r l) :
    (URMInstrRaw.toBoundedArray r l h).size = l.length := by
  unfold URMInstrRaw.toBoundedArray
  rw [List.size_toArray, List.length_map, List.length_attach]

/-- Indexing `toBoundedArray r l h` at `i < l.length`
yields `toBounded` applied to the `i`-th raw element. -/
theorem URMInstrRaw.toBoundedArray_getElem
    (r : ℕ) (l : List URMInstrRaw)
    (h : URMInstrRaw.boundedBy r l)
    (i : ℕ) (hi : i < (URMInstrRaw.toBoundedArray r l h).size) :
    (URMInstrRaw.toBoundedArray r l h)[i] =
      URMInstrRaw.toBounded r (l[i]'(by
        rw [URMInstrRaw.toBoundedArray_size] at hi; exact hi))
        (h _ (List.getElem_mem (by
          rw [URMInstrRaw.toBoundedArray_size] at hi; exact hi))) := by
  unfold URMInstrRaw.toBoundedArray
  rw [List.getElem_toArray, List.getElem_map,
    List.getElem_attach]

/-- `getElem?` form of `toBoundedArray_getElem`: at any
`i < l.length`, the bounded array yields
`some (toBounded …)`. -/
theorem URMInstrRaw.toBoundedArray_getElem?
    (r : ℕ) (l : List URMInstrRaw)
    (h : URMInstrRaw.boundedBy r l)
    (i : ℕ) (hi : i < l.length) :
    (URMInstrRaw.toBoundedArray r l h)[i]? =
      some (URMInstrRaw.toBounded r (l[i]'hi)
        (h _ (List.getElem_mem hi))) := by
  have hsize : i < (URMInstrRaw.toBoundedArray r l h).size := by
    rw [URMInstrRaw.toBoundedArray_size]; exact hi
  rw [Array.getElem?_eq_getElem hsize,
    URMInstrRaw.toBoundedArray_getElem]

/-- A compiled URM fragment for a sub-expression of arity
`a`. Compositional building block: per-ER-constructor
combinators (`compileFrag_*`) glue sub-fragments into
larger fragments by register-index injection and
PC-shifting; the top-level `compileER` returns the
fragment's underlying `URMProgram a` via the
auto-generated `.toURMProgram`.

Extends `URMProgram a` (the arity-indexed URM kernel
program type, Task 0 refactor); adds the reserved-zero
convention used to encode unconditional `goto` via
`jumpZ V_z l l` per spec §5.1.

Convention: the reserved-zero register is `⟨0, …⟩` and
the first instruction in `instrs` is `assign ⟨0, …⟩ 0`,
defensively initialising it. -/
@[ext] structure CompiledFragment (a : ℕ)
    extends URMProgram a where
  /-- 0 < numRegs (the reserved-zero register exists). -/
  numRegs_pos : 0 < numRegs
  /-- Reserved-zero register `⟨0, numRegs_pos⟩` disjoint
  from all input registers. -/
  zeroReg_not_input : ∀ i, inputRegs i ≠ ⟨0, numRegs_pos⟩
  /-- Reserved-zero register disjoint from the output
  register. -/
  zeroReg_not_output : (⟨0, numRegs_pos⟩ : Fin numRegs)
    ≠ outputReg
  /-- The last instruction is the halt instruction. Used
  by combinators that drop a trailing `.stop` to splice
  sub-fragments together. -/
  lastInstr_isStop : instrs.back? = some .stop

/-- The reserved-zero register `⟨0, F.numRegs_pos⟩`. -/
def CompiledFragment.zeroReg {a : ℕ}
    (F : CompiledFragment a) : Fin F.numRegs :=
  ⟨0, F.numRegs_pos⟩

/-- Encode unconditional `goto l` as Tourlakis's
informal shorthand (p. 19): two-target zero-test jump on
the reserved-zero register `V_z` (= register 0). Both
branches go to `l`, so the jump is unconditional.

Returns a single raw instruction. -/
def URMRaw.goto (l : ℕ) : URMInstrRaw :=
  .jumpZR 0 l l

/-- Destructive transfer `V_dst ← V_dst + V_src;
V_src ← 0`. Body of Tourlakis 2018 p. 19's M program for
`λx.x`, generalised to arbitrary `src` and `dst` and
omitting the trailing `stop`. Emits exactly 4 raw
instructions starting at PC offset `pcBase`; exit PC is
`pcBase + 4`.

Returns the instruction list. The caller is responsible
for placing the returned instructions at `pcBase` in the
overall fragment. -/
def URMRaw.transferLoop (pcBase src dst : ℕ) :
    List URMInstrRaw :=
  [ .jumpZR src (pcBase + 4) (pcBase + 1),
    .decR src,
    .incR dst,
    URMRaw.goto pcBase ]

/-- Number of raw instructions emitted by
`transferLoop`. -/
def URMRaw.transferLoopLen : ℕ := 4

/-- Preserving transfer `V_dst ← V_dst + V_src;
V_src unchanged`. Two destructive-transfer loops via a
tmp register; spec §5.1 register-allocation discipline.
Emits exactly 9 raw instructions starting at PC offset
`pcBase`; exit PC is `pcBase + 9`. -/
def URMRaw.preservingTransfer
    (pcBase src dst tmp : ℕ) : List URMInstrRaw :=
  -- Loop 1: V_src consumed; V_dst, V_tmp accumulate.
  -- PCs pcBase..pcBase+4 (5 instructions):
  [ .jumpZR src (pcBase + 5) (pcBase + 1),  -- pcBase
    .decR src,                              -- pcBase+1
    .incR dst,                              -- pcBase+2
    .incR tmp,                              -- pcBase+3
    URMRaw.goto pcBase,                     -- pcBase+4
  -- Loop 2: V_tmp consumed; V_src restored.
  -- PCs pcBase+5..pcBase+8 (4 instructions):
    .jumpZR tmp (pcBase + 9) (pcBase + 6),  -- pcBase+5
    .decR tmp,                              -- pcBase+6
    .incR src,                              -- pcBase+7
    URMRaw.goto (pcBase + 5) ]              -- pcBase+8

/-- Number of raw instructions emitted by
`preservingTransfer`. -/
def URMRaw.preservingTransferLen : ℕ := 9

/-- Fragment for `ERMor1.zero`. Tourlakis 2018 §0.1.0.37
p. 16 instruction set; spec §5.1 zero template. Output is
the constant 0; emits `assign V_z 0; assign V_out 0;
stop`. -/
def compileFrag_zero : CompiledFragment 0 where
  numRegs := 2
  numRegs_pos := by decide
  inputRegs := Fin.elim0
  outputReg := ⟨1, by decide⟩
  instrs := #[
    .assign ⟨0, by decide⟩ 0,
    .assign ⟨1, by decide⟩ 0,
    .stop ]
  inputRegs_inj := by
    intro a _ _
    exact Fin.elim0 a
  outputReg_not_input := by
    intro i _
    exact Fin.elim0 i
  zeroReg_not_input := by
    intro i _
    exact Fin.elim0 i
  zeroReg_not_output := by decide
  lastInstr_isStop := by decide

/-- Fragment for `ERMor1.succ`. Tourlakis 2018 p. 19
N-template (M plus one increment); spec §5.1 succ
template. Copies the single input to the output
non-destructively, then increments. -/
def compileFrag_succ : CompiledFragment 1 :=
  let rawList : List URMInstrRaw :=
    (.assignR 0 0)
      :: (URMRaw.preservingTransfer 1 2 1 3
          ++ [.incR 1, .stopR])
  have hBound : URMInstrRaw.boundedBy 4 rawList := by
    change ∀ ins ∈ rawList, _
    simp only [rawList, URMRaw.preservingTransfer,
      URMRaw.goto, List.forall_mem_cons,
      List.forall_mem_append, List.not_mem_nil,
      IsEmpty.forall_iff, forall_const]
    decide
  { numRegs := 4
    numRegs_pos := by decide
    inputRegs := fun _ => ⟨2, by decide⟩
    outputReg := ⟨1, by decide⟩
    instrs := URMInstrRaw.toBoundedArray 4 rawList hBound
    inputRegs_inj := by
      intro i j _
      exact Subsingleton.elim _ _
    outputReg_not_input := by
      intro _ h
      exact absurd (congrArg Fin.val h) (by decide)
    zeroReg_not_input := by
      intro _ h
      exact absurd (congrArg Fin.val h) (by decide)
    zeroReg_not_output := by decide
    lastInstr_isStop :=
      URMInstrRaw.toBoundedArray_back?_of_last_stopR hBound
        (by simp [rawList, URMRaw.preservingTransfer,
          URMRaw.goto]) }

/-- Fragment for `ERMor1.proj i`. Spec §5.1 proj
template. Preserving-transfer from input slot `i`'s
register to the output. -/
def compileFrag_proj {k : ℕ} (i : Fin k) :
    CompiledFragment k :=
  let rawList : List URMInstrRaw :=
    (.assignR 0 0)
      :: ((URMRaw.preservingTransfer 1 (2 + i.val) 1 (2 + k))
          ++ [.stopR])
  have hBound : URMInstrRaw.boundedBy (k + 3) rawList := by
    have hi : i.val < k := i.isLt
    intro ins hmem
    -- Decompose membership via simp; rewrite `ins` from
    -- each equality and discharge per disjunct with
    -- `omega` (which sees `hi`).
    simp only [rawList, URMRaw.preservingTransfer,
      URMRaw.goto, List.mem_cons, List.mem_append,
      List.not_mem_nil, or_false] at hmem
    rcases hmem with h | h | h
    · rw [h]; simp only [URMInstrRaw.regBound]; omega
    · rcases h with h | h | h | h | h | h | h | h | h <;>
        (rw [h]; simp only [URMInstrRaw.regBound]; omega)
    · rw [h]; simp only [URMInstrRaw.regBound]; omega
  { numRegs := k + 3
    numRegs_pos := by omega
    inputRegs := fun j => ⟨2 + j.val, by omega⟩
    outputReg := ⟨1, by omega⟩
    instrs := URMInstrRaw.toBoundedArray (k + 3) rawList hBound
    inputRegs_inj := by
      intro p q hpq
      apply Fin.ext
      have h : (2 + p.val : ℕ) = (2 + q.val : ℕ) :=
        congrArg Fin.val hpq
      omega
    outputReg_not_input := by
      intro p hp
      have h : (2 + p.val : ℕ) = (1 : ℕ) :=
        congrArg Fin.val hp
      omega
    zeroReg_not_input := by
      intro p hp
      have h : (2 + p.val : ℕ) = (0 : ℕ) :=
        congrArg Fin.val hp
      omega
    zeroReg_not_output := by
      intro h
      have h' : (0 : ℕ) = (1 : ℕ) := congrArg Fin.val h
      omega
    lastInstr_isStop :=
      URMInstrRaw.toBoundedArray_back?_of_last_stopR hBound
        (by simp [rawList, URMRaw.preservingTransfer,
          URMRaw.goto]) }

/-- Input register assignment for `compileFrag_sub`:
slot 0 → register 2, slot 1 → register 3. Built via
`Fin.cases` over the two-element `Fin 2`. -/
def compileFrag_sub_inputRegs : Fin 2 → Fin 6 :=
  Fin.cases (⟨2, by decide⟩) (fun _ => ⟨3, by decide⟩)

/-- `compileFrag_sub_inputRegs` on slot 0. -/
@[simp] theorem compileFrag_sub_inputRegs_zero :
    compileFrag_sub_inputRegs 0 = ⟨2, by decide⟩ := rfl

/-- `compileFrag_sub_inputRegs` on slot 1. -/
@[simp] theorem compileFrag_sub_inputRegs_one :
    compileFrag_sub_inputRegs 1 = ⟨3, by decide⟩ := rfl

/-- Fragment for `ERMor1.sub`. Spec §5.1 sub template:
preserving-transfer X to output; destructive copy of Y
to scratch; outer loop decrementing both output and
scratch. Tourlakis 2018 p. 19 M-template plus
Loop-to-URM expansion (p. 20). -/
def compileFrag_sub : CompiledFragment 2 :=
  let rawList : List URMInstrRaw :=
    (.assignR 0 0)
      :: ((URMRaw.preservingTransfer 1 2 1 4)
          ++ (URMRaw.transferLoop 10 3 5)
          ++ [ .jumpZR 5 18 15,
               .decR 5,
               .decR 1,
               URMRaw.goto 14,
               .stopR ])
  have hBound : URMInstrRaw.boundedBy 6 rawList := by
    change ∀ ins ∈ rawList, _
    simp only [rawList, URMRaw.preservingTransfer,
      URMRaw.transferLoop, URMRaw.goto,
      List.forall_mem_cons, List.forall_mem_append,
      List.not_mem_nil, IsEmpty.forall_iff, forall_const]
    decide
  { numRegs := 6
    numRegs_pos := by decide
    inputRegs := compileFrag_sub_inputRegs
    outputReg := ⟨1, by decide⟩
    instrs := URMInstrRaw.toBoundedArray 6 rawList hBound
    inputRegs_inj := by
      intro p q hpq
      -- `p, q : Fin 2` each lie in {0, 1}; the slot-to-
      -- register function is injective on those values.
      -- Use `Fin.cases` (Lean-core eliminator) for a
      -- constructive case-split avoiding mathlib's
      -- `fin_cases` (which pulls in `Classical.choice`).
      apply Fin.ext
      have h := congrArg Fin.val hpq
      revert h
      refine Fin.cases ?_
        (fun i => Fin.cases ?_ (fun j => j.elim0) i) p <;>
        refine Fin.cases ?_
          (fun i => Fin.cases ?_ (fun j => j.elim0) i) q <;>
        intro h <;>
        (first | rfl | (exfalso; revert h; decide))
    outputReg_not_input := by
      intro p hp
      have h := congrArg Fin.val hp
      revert h
      refine Fin.cases ?_
        (fun i => Fin.cases ?_ (fun j => j.elim0) i) p <;>
        intro h <;> revert h <;> decide
    zeroReg_not_input := by
      intro p hp
      have h := congrArg Fin.val hp
      revert h
      refine Fin.cases ?_
        (fun i => Fin.cases ?_ (fun j => j.elim0) i) p <;>
        intro h <;> revert h <;> decide
    zeroReg_not_output := by decide
    lastInstr_isStop :=
      URMInstrRaw.toBoundedArray_back?_of_last_stopR hBound
        (by simp [rawList, URMRaw.preservingTransfer,
          URMRaw.transferLoop, URMRaw.goto]) }

/-- Convert a typed `URMInstr r` to its raw form,
discarding the bound proof on register indices. Used by
`compileFrag_comp` to splice sub-fragment instructions
into the raw-list emission pipeline. -/
def toRawOfBounded {r : ℕ} : URMInstr r → URMInstrRaw
  | .assign i c => .assignR i.val c
  | .inc i => .incR i.val
  | .dec i => .decR i.val
  | .jumpZ i l₁ l₂ => .jumpZR i.val l₁ l₂
  | .stop => .stopR

/-- Register bound of `toRawOfBounded ins` is at most
`r` — every register index in `ins` is a `Fin r`, so its
`Nat`-form `+1` is at most `r`-bounded by the `Fin` proof.
We state the bound as `≤ r` (so callers can chain). -/
theorem regBound_toRawOfBounded_le {r : ℕ} (ins : URMInstr r) :
    (toRawOfBounded ins).regBound ≤ r := by
  cases ins
  · exact Fin.isLt _
  · exact Fin.isLt _
  · exact Fin.isLt _
  · exact Fin.isLt _
  · exact Nat.zero_le _

/-- Reindex and PC-shift a sub-fragment's instructions in
one go at the raw level: emit a `URMInstrRaw` with
register indices shifted by `regOffset` and PC labels
shifted by `pcShift`. -/
def URMInstrRaw.reindexShift (regOffset pcShift : ℕ) :
    URMInstrRaw → URMInstrRaw
  | .assignR i c => .assignR (regOffset + i) c
  | .incR i => .incR (regOffset + i)
  | .decR i => .decR (regOffset + i)
  | .jumpZR i l₁ l₂ =>
      .jumpZR (regOffset + i) (pcShift + l₁) (pcShift + l₂)
  | .stopR => .stopR

/-- Cumulative register count of the first `n`
sub-fragments. Used by `compileFrag_comp` to lay out
disjoint register blocks. -/
def gsPrefixSum {k a : ℕ}
    (frag_gs : Fin k → CompiledFragment a) :
    ℕ → ℕ
  | 0 => 0
  | n + 1 =>
    gsPrefixSum frag_gs n
      + (if h : n < k then (frag_gs ⟨n, h⟩).numRegs else 0)

/-- The block size contributed by `frag_gs i` to the
prefix sum equals `(frag_gs i).numRegs`. -/
theorem gsPrefixSum_succ_eq {k a : ℕ}
    (frag_gs : Fin k → CompiledFragment a) (i : Fin k) :
    gsPrefixSum frag_gs (i.val + 1)
      = gsPrefixSum frag_gs i.val + (frag_gs i).numRegs := by
  change gsPrefixSum frag_gs i.val
      + (if h : i.val < k then (frag_gs ⟨i.val, h⟩).numRegs else 0)
    = gsPrefixSum frag_gs i.val + (frag_gs i).numRegs
  simp only [i.isLt, dite_true, Fin.eta]

/-- `gsPrefixSum` is monotone. -/
theorem gsPrefixSum_mono {k a : ℕ}
    (frag_gs : Fin k → CompiledFragment a) {n m : ℕ}
    (h : n ≤ m) :
    gsPrefixSum frag_gs n ≤ gsPrefixSum frag_gs m := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih =>
    refine Nat.le_trans ih ?_
    change gsPrefixSum frag_gs _
      ≤ gsPrefixSum frag_gs _ + (if h : _ < k then _ else 0)
    split <;> omega

/-- Boundedness lemma for `preservingTransfer`: every
emitted raw instruction has register bound at most
`max(src, dst, tmp) + 1`. -/
theorem boundedBy_preservingTransfer (r pcBase src dst tmp : ℕ)
    (hsrc : src + 1 ≤ r) (hdst : dst + 1 ≤ r)
    (htmp : tmp + 1 ≤ r) :
    URMInstrRaw.boundedBy r
      (URMRaw.preservingTransfer pcBase src dst tmp) := by
  intro ins hmem
  simp only [URMRaw.preservingTransfer, URMRaw.goto,
    List.mem_cons, List.not_mem_nil,
    or_false] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h <;>
    (rw [h]; simp only [URMInstrRaw.regBound]; omega)

/-- Boundedness lemma for `transferLoop`. -/
theorem boundedBy_transferLoop (r pcBase src dst : ℕ)
    (hsrc : src + 1 ≤ r) (hdst : dst + 1 ≤ r) :
    URMInstrRaw.boundedBy r
      (URMRaw.transferLoop pcBase src dst) := by
  intro ins hmem
  simp only [URMRaw.transferLoop, URMRaw.goto,
    List.mem_cons, List.not_mem_nil,
    or_false] at hmem
  rcases hmem with h | h | h | h <;>
    (rw [h]; simp only [URMInstrRaw.regBound]; omega)

/-- Bound on `URMInstrRaw.reindexShift`. -/
theorem regBound_reindexShift_le_offset_add
    (regOffset pcShift bound : ℕ)
    (ins : URMInstrRaw) (h : ins.regBound ≤ bound) :
    (URMInstrRaw.reindexShift regOffset pcShift ins).regBound
      ≤ regOffset + bound := by
  cases ins <;>
    simp only [URMInstrRaw.reindexShift, URMInstrRaw.regBound] <;>
    (revert h; simp only [URMInstrRaw.regBound]; omega)

/-- Block at offset `pcBase` for sub-fragment `i`:
input-wiring preamble (`a` copies of `preservingTransfer`
moving outer input `j` into the reindexed slot of
`(frag_gs i).inputRegs j`), then `gs i`'s instructions
(minus trailing stop) reindexed and PC-shifted, then a
destructive `transferLoop` wiring `gs i`'s output into
`f`'s `i`-th input slot. -/
def compileFrag_comp_subBlock {k a : ℕ}
    (frag_f : CompiledFragment k)
    (frag_gs : Fin k → CompiledFragment a)
    (gsBase fBase tmpReg : ℕ) (i : Fin k) (pcBase : ℕ) :
    List URMInstrRaw :=
  let bodyBase : ℕ := pcBase + 9 * a
  let trBase : ℕ :=
    bodyBase + ((frag_gs i).instrs.size - 1)
  let inputCopies : List URMInstrRaw :=
    (List.finRange a).flatMap fun j =>
      URMRaw.preservingTransfer
        (pcBase + 9 * j.val)
        (2 + j.val)
        (gsBase + ((frag_gs i).inputRegs j).val)
        tmpReg
  let body : List URMInstrRaw :=
    (frag_gs i).instrs.pop.toList.map fun ins =>
      URMInstrRaw.reindexShift gsBase bodyBase (toRawOfBounded ins)
  let transfer : List URMInstrRaw :=
    URMRaw.transferLoop trBase
      (gsBase + ((frag_gs i).outputReg).val)
      (fBase + (frag_f.inputRegs i).val)
  inputCopies ++ body ++ transfer

/-- Boundedness lemma for `compileFrag_comp_subBlock`:
each emitted raw instruction has register bound at most
`nR`, given arithmetic bounds linking `gsBase`, `fBase`,
`tmpReg`, the sub-fragment's register count, and `f`'s
register count. -/
theorem boundedBy_compileFrag_comp_subBlock {k a : ℕ}
    (frag_f : CompiledFragment k)
    (frag_gs : Fin k → CompiledFragment a)
    (gsBase fBase tmpReg nR : ℕ) (i : Fin k) (pcBase : ℕ)
    (hGsBlock : gsBase + (frag_gs i).numRegs ≤ fBase)
    (hFBlock : fBase + frag_f.numRegs = tmpReg)
    (hTmp : tmpReg < nR) (ha : a ≤ fBase) :
    URMInstrRaw.boundedBy nR
      (compileFrag_comp_subBlock frag_f frag_gs
        gsBase fBase tmpReg i pcBase) := by
  unfold compileFrag_comp_subBlock
  -- bound facts shared across all three sub-lists
  have hOut : gsBase + ((frag_gs i).outputReg).val + 1 ≤ nR := by
    have hO : ((frag_gs i).outputReg).val < (frag_gs i).numRegs :=
      (frag_gs i).outputReg.isLt
    omega
  have hFIn : fBase + (frag_f.inputRegs i).val + 1 ≤ nR := by
    have hI : (frag_f.inputRegs i).val < frag_f.numRegs :=
      (frag_f.inputRegs i).isLt
    omega
  have hTmpR : tmpReg + 1 ≤ nR := by omega
  intro ins hmem
  simp only [List.mem_append, List.mem_flatMap,
    List.mem_map] at hmem
  rcases hmem with ((⟨j, _, hj⟩) | ⟨ins', _, heq⟩) | hT
  · -- inputCopies branch
    have hJa : j.val + 1 ≤ a := j.isLt
    have hSrc : (2 + j.val) + 1 ≤ nR := by omega
    have hDst : (gsBase + ((frag_gs i).inputRegs j).val) + 1 ≤ nR := by
      have hI : ((frag_gs i).inputRegs j).val < (frag_gs i).numRegs :=
        ((frag_gs i).inputRegs j).isLt
      omega
    exact boundedBy_preservingTransfer nR _ _ _ _ hSrc hDst hTmpR ins hj
  · -- body branch
    rw [← heq]
    have hb : (toRawOfBounded ins').regBound ≤ (frag_gs i).numRegs :=
      regBound_toRawOfBounded_le ins'
    have hr := regBound_reindexShift_le_offset_add gsBase
      (pcBase + 9 * a) (frag_gs i).numRegs (toRawOfBounded ins') hb
    omega
  · -- transfer branch
    exact boundedBy_transferLoop nR _ _ _ hOut hFIn ins hT

/-- Fragment for `ERMor1.comp f gs`. Spec §5.1.2:
sequentially run each sub-URM `gs i` (after a
preserving-transfer preamble that copies outer inputs into
`gs i`'s input slots), destructively transfer its output
into `f`'s `i`-th input slot via `transferLoop`, then run
`f`'s URM (whose own trailing `stop` becomes the outer
fragment's halt instruction). Tourlakis 2018 p. 21
"concatenate M_g and M_f".

Design choice: each sub-fragment is allocated a disjoint
register block of size `(frag_gs i).numRegs` (so its
internal zero register, distinct from the outer zero
register, is initialised by its own first-instruction
`assign 0 0` once reindexed). One shared scratch register
at slot `numRegs - 1` services every `preservingTransfer`
input-wiring step. `f`'s block sits immediately after the
last `gs i` block. -/
def compileFrag_comp {k a : ℕ}
    (frag_f : CompiledFragment k)
    (frag_gs : Fin k → CompiledFragment a) :
    CompiledFragment a :=
  let totalGsRegs : ℕ := gsPrefixSum frag_gs k
  let fBase : ℕ := 2 + a + totalGsRegs
  let tmpReg : ℕ := fBase + frag_f.numRegs
  let nR : ℕ := tmpReg + 1
  let gsBase : Fin k → ℕ :=
    fun i => 2 + a + gsPrefixSum frag_gs i.val
  -- Cumulative PC offset before block `i`. The whole
  -- emission begins with one `assign 0 0` at PC 0, so
  -- block `i`'s base PC is `1 + Σ_{j < i} (per-block
  -- length)`; this is encoded inline by threading
  -- `pcBase` through a `List.foldl` rather than as a
  -- separate prefix-sum function.
  let blockLen : Fin k → ℕ := fun i =>
    9 * a + ((frag_gs i).instrs.size - 1) + 4
  let pcBase : Fin k → ℕ := fun i =>
    1 + ((List.finRange k).filter
        (fun j => decide (j.val < i.val))).foldr
      (fun j acc => acc + blockLen j) 0
  let subBlocks : List URMInstrRaw :=
    (List.finRange k).flatMap fun i =>
      compileFrag_comp_subBlock frag_f frag_gs
        (gsBase i) fBase tmpReg i (pcBase i)
  let fPcBase : ℕ :=
    1 + (List.finRange k).foldr
      (fun j acc => acc + blockLen j) 0
  let fBody : List URMInstrRaw :=
    frag_f.instrs.toList.map fun ins =>
      URMInstrRaw.reindexShift fBase fPcBase (toRawOfBounded ins)
  let rawList : List URMInstrRaw :=
    (.assignR 0 0) :: (subBlocks ++ fBody)
  -- Shared arithmetic bounds.
  have hTmpLt : tmpReg < nR := by simp only [nR]; omega
  have hFBlockEq : fBase + frag_f.numRegs = tmpReg := by
    simp only [tmpReg]
  have ha_le : a ≤ fBase := by
    simp only [fBase]; omega
  have hGsBlock : ∀ i : Fin k,
      gsBase i + (frag_gs i).numRegs ≤ fBase := by
    intro i
    have hmono : gsPrefixSum frag_gs (i.val + 1)
        ≤ gsPrefixSum frag_gs k :=
      gsPrefixSum_mono frag_gs i.isLt
    have hsucc :
        gsPrefixSum frag_gs (i.val + 1)
          = gsPrefixSum frag_gs i.val + (frag_gs i).numRegs :=
      gsPrefixSum_succ_eq frag_gs i
    simp only [gsBase, fBase, totalGsRegs]
    omega
  have hBound : URMInstrRaw.boundedBy nR rawList := by
    intro ins hmem
    have hmem' : ins = (.assignR 0 0 : URMInstrRaw)
        ∨ ins ∈ subBlocks ++ fBody := List.mem_cons.mp hmem
    rcases hmem' with hAssign | hmem
    · -- `assignR 0 0` (head of rawList)
      rw [hAssign]; simp only [URMInstrRaw.regBound]
      simp only [nR, tmpReg, fBase]; omega
    rcases List.mem_append.mp hmem with hSub | hF
    · -- sub-block branch
      rcases List.mem_flatMap.mp hSub with ⟨i, _, hi⟩
      exact boundedBy_compileFrag_comp_subBlock frag_f frag_gs
        (gsBase i) fBase tmpReg nR i (pcBase i)
        (hGsBlock i) hFBlockEq hTmpLt ha_le ins hi
    · -- f-body branch
      rcases List.mem_map.mp hF with ⟨ins', _, heq⟩
      rw [← heq]
      have hb : (toRawOfBounded ins').regBound ≤ frag_f.numRegs :=
        regBound_toRawOfBounded_le ins'
      have hr := regBound_reindexShift_le_offset_add fBase
        fPcBase frag_f.numRegs (toRawOfBounded ins') hb
      omega
  have hFInstrsLast : frag_f.instrs.toList.getLast?
      = some (URMInstr.stop : URMInstr frag_f.numRegs) := by
    rw [Array.getLast?_toList]; exact frag_f.lastInstr_isStop
  have hFBodyLast : fBody.getLast? = some .stopR := by
    simp only [fBody, List.getLast?_map, hFInstrsLast,
      Option.map_some]
    rfl
  have hFBodyNe : fBody ≠ [] := by
    intro he; rw [he] at hFBodyLast; simp at hFBodyLast
  have hLastStopR : rawList.getLast? = some .stopR := by
    have hSubFLast :
        (subBlocks ++ fBody).getLast? = some .stopR :=
      List.getLast?_append_of_ne_nil _ hFBodyNe ▸ hFBodyLast
    simp only [rawList, List.getLast?_cons, hSubFLast,
      Option.getD_some]
  { numRegs := nR
    numRegs_pos := by
      simp only [nR]; omega
    inputRegs := fun j => ⟨2 + j.val, by
      have : j.val < a := j.isLt
      simp only [nR, tmpReg, fBase]; omega⟩
    outputReg := ⟨fBase + frag_f.outputReg.val, by
      have hO : frag_f.outputReg.val < frag_f.numRegs :=
        frag_f.outputReg.isLt
      simp only [nR, tmpReg]; omega⟩
    instrs := URMInstrRaw.toBoundedArray nR rawList hBound
    inputRegs_inj := by
      intro p q hpq
      apply Fin.ext
      have h : (2 + p.val : ℕ) = (2 + q.val : ℕ) :=
        congrArg Fin.val hpq
      omega
    outputReg_not_input := by
      intro p hp
      have hp_lt : p.val < a := p.isLt
      have h : (2 + p.val : ℕ) = (fBase + frag_f.outputReg.val : ℕ) :=
        congrArg Fin.val hp
      simp only [fBase] at h
      omega
    zeroReg_not_input := by
      intro p hp
      have h : (2 + p.val : ℕ) = (0 : ℕ) :=
        congrArg Fin.val hp
      omega
    zeroReg_not_output := by
      intro h
      have h' : (0 : ℕ) = (fBase + frag_f.outputReg.val : ℕ) :=
        congrArg Fin.val h
      simp only [fBase] at h'
      omega
    lastInstr_isStop :=
      URMInstrRaw.toBoundedArray_back?_of_last_stopR hBound
        hLastStopR }

/-- Source register for the per-iteration prologue at
slot `s : Fin (k + 1)`. Slot 0 receives the iteration
index `V_i` (located at register `k + 4`); slots `1..k`
receive the outer parameter at register `s.val + 2`. -/
private def bsum_prologueSrc (k : ℕ) (s : Fin (k + 1)) : ℕ :=
  if s.val = 0 then k + 4 else s.val + 2

/-- Per-slot block of the `compileFrag_bsum` per-iteration
prologue: copy the outer register at `bsum_prologueSrc k s`
into f's `s`-th input register (reindexed by `fBase`),
using `tmp1` as scratch. Each iteration's prologue is
preceded by a zero-sweep over all of f's reindexed registers
(`bsum_zeroSweep` below), so `preservingTransfer`'s additive
write produces the current iteration's source value rather
than accumulating across iterations; the zero-sweep also
flushes any internal scratches that nested combinators
inside `frag_f` may have left in f's register block.
Emitted at PC offset `prologueBase + 9 * s.val`; emits
exactly 9 raw instructions. -/
private def bsum_prologueBlock {k : ℕ}
    (frag_f : CompiledFragment (k + 1))
    (fBase tmp1 prologueBase : ℕ) (s : Fin (k + 1)) :
    List URMInstrRaw :=
  URMRaw.preservingTransfer
    (prologueBase + 9 * s.val)
    (bsum_prologueSrc k s)
    (fBase + (frag_f.inputRegs s).val)
    tmp1

/-- Boundedness lemma for `bsum_prologueBlock`: every
emitted raw instruction has register bound at most `nR`,
given arithmetic facts placing `bsum_prologueSrc k s`,
`fBase + (frag_f.inputRegs s).val`, and `tmp1` inside
`nR`. -/
private theorem boundedBy_bsum_prologueBlock {k : ℕ}
    (frag_f : CompiledFragment (k + 1))
    (fBase tmp1 prologueBase nR : ℕ) (s : Fin (k + 1))
    (hSrc : bsum_prologueSrc k s + 1 ≤ nR)
    (hDst : fBase + (frag_f.inputRegs s).val + 1 ≤ nR)
    (hTmp : tmp1 + 1 ≤ nR) :
    URMInstrRaw.boundedBy nR
      (bsum_prologueBlock frag_f fBase tmp1 prologueBase s) := by
  intro ins hpT
  simp only [bsum_prologueBlock] at hpT
  exact boundedBy_preservingTransfer nR _ _ _ _ hSrc hDst hTmp ins hpT

/-- Zero-sweep over all of f's reindexed registers
(`frag_f.numRegs` `assignR` instructions emitting
`assignR (fBase + r) 0` for `r ∈ [0, frag_f.numRegs)`).
Run at the start of each `compileFrag_bsum` iteration's
prologue to flush f's entire register block; this ensures
nested combinators inside `frag_f` whose internal scratches
accumulate additively (e.g. `compileFrag_comp`'s gs-input
slots) start each iteration from zero. -/
def bsum_zeroSweep {k : ℕ}
    (frag_f : CompiledFragment (k + 1)) (fBase : ℕ) :
    List URMInstrRaw :=
  (List.finRange frag_f.numRegs).map fun r =>
    (.assignR (fBase + r.val) 0 : URMInstrRaw)

/-- Boundedness lemma for `bsum_zeroSweep`: every emitted
instruction targets a register inside `nR`, given
`fBase + frag_f.numRegs ≤ nR`. -/
private theorem boundedBy_bsum_zeroSweep {k : ℕ}
    (frag_f : CompiledFragment (k + 1)) (fBase nR : ℕ)
    (hBlock : fBase + frag_f.numRegs ≤ nR) :
    URMInstrRaw.boundedBy nR (bsum_zeroSweep frag_f fBase) := by
  intro ins hmem
  simp only [bsum_zeroSweep, List.mem_map] at hmem
  rcases hmem with ⟨r, _, heq⟩
  rw [← heq]
  simp only [URMInstrRaw.regBound]
  have hr : r.val < frag_f.numRegs := r.isLt
  omega

/-- Fragment for `ERMor1.bsum f`. Spec §5.1, §5.1.1.
Outer Loop with iteration-counter register `V_i`
incrementing each iteration and bound register `V_x`
decrementing each iteration. Per-iteration prologue
re-clones outer parameters and writes `V_i` to f's
slot-0 scratch. Inner body invokes `frag_f`'s URM
(reindexed and PC-shifted) and `transferLoop`-adds
f's output into the bsum's output register.
Tourlakis 2018 p. 21 bounded-recursion template. -/
def compileFrag_bsum {k : ℕ}
    (frag_f : CompiledFragment (k + 1)) :
    CompiledFragment (k + 1) :=
  -- Register layout (outer):
  --   0     : V_z (reserved zero)
  --   1     : V_acc (accumulator / outputReg)
  --   2     : V_bound_in (outer input slot 0)
  --   3..k+2: V_param_j (outer input slots 1..k)
  --   k + 3 : V_x  (destructive clone of V_bound_in)
  --   k + 4 : V_i  (iteration index)
  --   k + 5 : tmp1 (scratch for preservingTransfer)
  --   k + 6 : tmp2 (scratch for cloning bound into V_x)
  --   k+7.. : f's reindexed registers (block size = frag_f.numRegs)
  let vAcc : ℕ := 1
  let vBoundIn : ℕ := 2
  let vX : ℕ := k + 3
  let vI : ℕ := k + 4
  let tmp1 : ℕ := k + 5
  let tmp2 : ℕ := k + 6
  let fBase : ℕ := k + 7
  let nR : ℕ := fBase + frag_f.numRegs
  -- PC layout (offsets are absolute):
  --   0  : assignR 0 0     (V_z ← 0)
  --   1  : assignR vAcc 0
  --   2  : assignR vX 0
  --   3  : assignR vI 0
  --   4..12 : preservingTransfer 4 vBoundIn vX tmp2  (9 instrs)
  --   13 : jumpZR vX exitPC bodyStartPC          (loop top)
  --   14 : decR vX                                (body start)
  --   15..(15 + frag_f.numRegs - 1) : zero-sweep over f's block
  --     (`frag_f.numRegs` `assignR (fBase + r) 0` instructions);
  --     flushes f's reindexed register block at the start of each
  --     iteration so internal scratches of nested combinators
  --     inside f do not accumulate across iterations.
  --   (15 + frag_f.numRegs)..(bodyPCBase - 1) : per-iter prologue,
  --     k+1 blocks of `preservingTransfer` (9 instrs each)
  --     copying outer sources into f's input slots.
  --   bodyPCBase = 15 + frag_f.numRegs + 9 * (k + 1) :
  --     f's body (frag_f.instrs.size - 1 instrs, reindexed and PC-shifted)
  --   bodyPCBase + fBodyLen .. + 3 : transferLoop f-out → vAcc (4 instrs)
  --   bodyPCBase + fBodyLen + 4 : incR vI
  --   bodyPCBase + fBodyLen + 5 : goto topPC
  --   exitPC = bodyPCBase + fBodyLen + 6 : stopR
  let topPC : ℕ := 13
  let bodyStartPC : ℕ := 14
  let zeroSweepBase : ℕ := 15
  let prologueBase : ℕ := 15 + frag_f.numRegs
  let bodyPCBase : ℕ := 15 + frag_f.numRegs + 9 * (k + 1)
  let fBodyLen : ℕ := frag_f.instrs.size - 1
  let trBase : ℕ := bodyPCBase + fBodyLen
  let incIPC : ℕ := trBase + 4
  let gotoTopPC : ℕ := trBase + 5
  let exitPC : ℕ := trBase + 6
  let prelude : List URMInstrRaw :=
    [ .assignR 0 0,
      .assignR vAcc 0,
      .assignR vX 0,
      .assignR vI 0 ]
        ++ URMRaw.preservingTransfer 4 vBoundIn vX tmp2
  let loopTop : List URMInstrRaw :=
    [ .jumpZR vX exitPC bodyStartPC,
      .decR vX ]
  let zeroSweep : List URMInstrRaw :=
    bsum_zeroSweep frag_f fBase
  let prologue : List URMInstrRaw :=
    (List.finRange (k + 1)).flatMap fun s =>
      bsum_prologueBlock frag_f fBase tmp1 prologueBase s
  let fBody : List URMInstrRaw :=
    frag_f.instrs.pop.toList.map fun ins =>
      URMInstrRaw.reindexShift fBase bodyPCBase (toRawOfBounded ins)
  let accUpdate : List URMInstrRaw :=
    URMRaw.transferLoop trBase
      (fBase + frag_f.outputReg.val) vAcc
  let epilogue : List URMInstrRaw :=
    [ .incR vI, URMRaw.goto topPC, .stopR ]
  let rawList : List URMInstrRaw :=
    prelude ++ loopTop ++ zeroSweep ++ prologue ++ fBody
      ++ accUpdate ++ epilogue
  -- Shared boundedness facts.
  have hAcc : vAcc + 1 ≤ nR := by
    simp only [vAcc, nR, fBase]; omega
  have hBoundIn : vBoundIn + 1 ≤ nR := by
    simp only [vBoundIn, nR, fBase]; omega
  have hVX : vX + 1 ≤ nR := by
    simp only [vX, nR, fBase]; omega
  have hVI : vI + 1 ≤ nR := by
    simp only [vI, nR, fBase]; omega
  have hTmp1 : tmp1 + 1 ≤ nR := by
    simp only [tmp1, nR, fBase]; omega
  have hTmp2 : tmp2 + 1 ≤ nR := by
    simp only [tmp2, nR, fBase]; omega
  have hFOut : fBase + frag_f.outputReg.val + 1 ≤ nR := by
    have : frag_f.outputReg.val < frag_f.numRegs :=
      frag_f.outputReg.isLt
    simp only [nR]; omega
  have hPrologueSrc : ∀ s : Fin (k + 1),
      bsum_prologueSrc k s + 1 ≤ nR := by
    intro s
    have hs : s.val < k + 1 := s.isLt
    simp only [bsum_prologueSrc, nR, fBase]
    split <;> omega
  have hFIn : ∀ s : Fin (k + 1),
      fBase + (frag_f.inputRegs s).val + 1 ≤ nR := by
    intro s
    have : (frag_f.inputRegs s).val < frag_f.numRegs :=
      (frag_f.inputRegs s).isLt
    simp only [nR]; omega
  -- Boundedness of every block.
  have hPreludeBound : URMInstrRaw.boundedBy nR prelude := by
    intro ins hmem
    simp only [prelude, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hmem
    rcases hmem with (h | h | h | h) | hpT
    · rw [h]; simp only [URMInstrRaw.regBound]; omega
    · rw [h]; simp only [URMInstrRaw.regBound]; exact hAcc
    · rw [h]; simp only [URMInstrRaw.regBound]; exact hVX
    · rw [h]; simp only [URMInstrRaw.regBound]; exact hVI
    · exact boundedBy_preservingTransfer nR _ _ _ _
        hBoundIn hVX hTmp2 ins hpT
  have hLoopTopBound : URMInstrRaw.boundedBy nR loopTop := by
    intro ins hmem
    simp only [loopTop, List.mem_cons, List.not_mem_nil,
      or_false] at hmem
    rcases hmem with h | h <;>
      (rw [h]; simp only [URMInstrRaw.regBound]; exact hVX)
  have hPrologueBound : URMInstrRaw.boundedBy nR prologue := by
    intro ins hmem
    simp only [prologue, List.mem_flatMap] at hmem
    rcases hmem with ⟨s, _, hs⟩
    exact boundedBy_bsum_prologueBlock frag_f fBase tmp1
      prologueBase nR s (hPrologueSrc s) (hFIn s) hTmp1 ins hs
  have hFBodyBound : URMInstrRaw.boundedBy nR fBody := by
    intro ins hmem
    simp only [fBody, List.mem_map] at hmem
    rcases hmem with ⟨ins', _, heq⟩
    rw [← heq]
    have hb : (toRawOfBounded ins').regBound ≤ frag_f.numRegs :=
      regBound_toRawOfBounded_le ins'
    have hr := regBound_reindexShift_le_offset_add fBase
      bodyPCBase frag_f.numRegs (toRawOfBounded ins') hb
    simp only [nR]; omega
  have hAccUpdateBound : URMInstrRaw.boundedBy nR accUpdate :=
    boundedBy_transferLoop nR _ _ _ hFOut hAcc
  have hEpilogueBound : URMInstrRaw.boundedBy nR epilogue := by
    intro ins hmem
    simp only [epilogue, URMRaw.goto, List.mem_cons,
      List.not_mem_nil, or_false] at hmem
    rcases hmem with h | h | h
    · rw [h]; simp only [URMInstrRaw.regBound]; exact hVI
    · rw [h]; simp only [URMInstrRaw.regBound]; omega
    · rw [h]; simp only [URMInstrRaw.regBound]; omega
  have hZeroSweepBound : URMInstrRaw.boundedBy nR zeroSweep := by
    have hBlock : fBase + frag_f.numRegs ≤ nR := by
      simp only [nR]; omega
    exact boundedBy_bsum_zeroSweep frag_f fBase nR hBlock
  have hBound : URMInstrRaw.boundedBy nR rawList := by
    intro ins hmem
    simp only [rawList, List.mem_append] at hmem
    rcases hmem with
      (((((hP | hL) | hZ) | hPr) | hF) | hA) | hE
    · exact hPreludeBound ins hP
    · exact hLoopTopBound ins hL
    · exact hZeroSweepBound ins hZ
    · exact hPrologueBound ins hPr
    · exact hFBodyBound ins hF
    · exact hAccUpdateBound ins hA
    · exact hEpilogueBound ins hE
  -- Last raw instruction is `.stopR` (rightmost element
  -- of `epilogue`).
  have hEpiNeNil : epilogue ≠ [] := by
    simp only [epilogue, ne_eq, reduceCtorEq, not_false_eq_true]
  have hEpiLast : epilogue.getLast? = some .stopR := by
    simp only [epilogue]; rfl
  have hLastStopR : rawList.getLast? = some .stopR := by
    simp only [rawList]
    rw [List.getLast?_append_of_ne_nil _ hEpiNeNil]
    exact hEpiLast
  { numRegs := nR
    numRegs_pos := by simp only [nR, fBase]; omega
    inputRegs := fun j => ⟨2 + j.val, by
      have : j.val < k + 1 := j.isLt
      simp only [nR, fBase]; omega⟩
    outputReg := ⟨1, by simp only [nR, fBase]; omega⟩
    instrs := URMInstrRaw.toBoundedArray nR rawList hBound
    inputRegs_inj := by
      intro p q hpq
      apply Fin.ext
      have h : (2 + p.val : ℕ) = (2 + q.val : ℕ) :=
        congrArg Fin.val hpq
      omega
    outputReg_not_input := by
      intro p hp
      have h : (2 + p.val : ℕ) = (1 : ℕ) :=
        congrArg Fin.val hp
      omega
    zeroReg_not_input := by
      intro p hp
      have h : (2 + p.val : ℕ) = (0 : ℕ) :=
        congrArg Fin.val hp
      omega
    zeroReg_not_output := by
      intro h
      have h' : (0 : ℕ) = (1 : ℕ) := congrArg Fin.val h
      omega
    lastInstr_isStop :=
      URMInstrRaw.toBoundedArray_back?_of_last_stopR hBound
        hLastStopR }

/-- Fragment for `ERMor1.bprod f`. Spec §5.1, §5.1.1.
Mirrors `compileFrag_bsum` with a multiplicative
accumulator; initial value 1 (empty product).
Multiplication accumulator update emits Tourlakis 2018
p. 19's R^XY_Z nested-loop template. -/
def compileFrag_bprod {k : ℕ}
    (frag_f : CompiledFragment (k + 1)) :
    CompiledFragment (k + 1) :=
  -- Register layout (outer):
  --   0     : V_z (reserved zero)
  --   1     : V_acc (accumulator / outputReg)
  --   2     : V_bound_in (outer input slot 0)
  --   3..k+2: V_param_j (outer input slots 1..k)
  --   k + 3 : V_x  (destructive clone of V_bound_in)
  --   k + 4 : V_i  (iteration index)
  --   k + 5 : tmp1 (scratch for prologue preservingTransfer)
  --   k + 6 : tmp2 (scratch for cloning bound into V_x)
  --   k + 7 : V_acc_clone (multiplicative scratch:
  --           destructive copy of V_acc)
  --   k + 8 : V_factor    (destructive copy of V_f_out)
  --   k + 9 : V_mul_tmp   (preservingTransfer scratch
  --           used inside the inner add of the
  --           R^XY_Z multiplication template)
  --   k+10..: f's reindexed registers (block size = frag_f.numRegs)
  let vAcc : ℕ := 1
  let vBoundIn : ℕ := 2
  let vX : ℕ := k + 3
  let vI : ℕ := k + 4
  let tmp1 : ℕ := k + 5
  let tmp2 : ℕ := k + 6
  let vAccClone : ℕ := k + 7
  let vFactor : ℕ := k + 8
  let vMulTmp : ℕ := k + 9
  let fBase : ℕ := k + 10
  let nR : ℕ := fBase + frag_f.numRegs
  -- PC layout (offsets are absolute):
  --   0  : assignR 0 0     (V_z ← 0)
  --   1  : assignR vAcc 0
  --   2  : assignR vX 0
  --   3  : assignR vI 0
  --   4..12 : preservingTransfer 4 vBoundIn vX tmp2 (9 instrs)
  --   13 : incR vAcc       (V_acc ← 1; empty product)
  --   14 : jumpZR vX exitPC bodyStartPC (loop top)
  --   15 : decR vX                            (body start)
  --   16..(16 + frag_f.numRegs - 1) : zero-sweep over f's block
  --     (`frag_f.numRegs` `assignR (fBase + r) 0` instructions).
  --   (16 + frag_f.numRegs)..(bodyPCBase - 1) : per-iter prologue,
  --     `k + 1` blocks of `preservingTransfer` (9 instrs each).
  --   bodyPCBase = 16 + frag_f.numRegs + 9 * (k + 1) :
  --     f's body (frag_f.instrs.size - 1 instrs, reindexed/PC-shifted)
  --   trBase = bodyPCBase + fBodyLen :
  --     accumulator-update block (21 instrs)
  --     trBase..trBase+3   : transferLoop V_acc → V_acc_clone
  --     trBase+4..trBase+7 : transferLoop V_f_out → V_factor
  --     trBase+8           : jumpZR V_factor (trBase+20) (trBase+9)
  --     trBase+9           : decR V_factor
  --     trBase+10..+18     : preservingTransfer
  --                          V_acc_clone → V_acc (9 instrs)
  --     trBase+19          : goto (trBase+8)
  --     trBase+20          : assignR V_acc_clone 0 (reset clone)
  --   trBase+21 : incR vI
  --   trBase+22 : goto topPC
  --   exitPC = trBase + 23 : stopR
  let topPC : ℕ := 14
  let bodyStartPC : ℕ := 15
  let prologueBase : ℕ := 16 + frag_f.numRegs
  let bodyPCBase : ℕ := 16 + frag_f.numRegs + 9 * (k + 1)
  let fBodyLen : ℕ := frag_f.instrs.size - 1
  let trBase : ℕ := bodyPCBase + fBodyLen
  let exitPC : ℕ := trBase + 23
  let prelude : List URMInstrRaw :=
    [ .assignR 0 0,
      .assignR vAcc 0,
      .assignR vX 0,
      .assignR vI 0 ]
        ++ URMRaw.preservingTransfer 4 vBoundIn vX tmp2
        ++ [ .incR vAcc ]
  let loopTop : List URMInstrRaw :=
    [ .jumpZR vX exitPC bodyStartPC,
      .decR vX ]
  let zeroSweep : List URMInstrRaw :=
    bsum_zeroSweep frag_f fBase
  let prologue : List URMInstrRaw :=
    (List.finRange (k + 1)).flatMap fun s =>
      bsum_prologueBlock frag_f fBase tmp1 prologueBase s
  let fBody : List URMInstrRaw :=
    frag_f.instrs.pop.toList.map fun ins =>
      URMInstrRaw.reindexShift fBase bodyPCBase (toRawOfBounded ins)
  let accUpdate : List URMInstrRaw :=
    URMRaw.transferLoop trBase vAcc vAccClone
      ++ URMRaw.transferLoop (trBase + 4)
          (fBase + frag_f.outputReg.val) vFactor
      ++ [ .jumpZR vFactor (trBase + 20) (trBase + 9),
           .decR vFactor ]
      ++ URMRaw.preservingTransfer (trBase + 10)
          vAccClone vAcc vMulTmp
      ++ [ URMRaw.goto (trBase + 8),
           .assignR vAccClone 0 ]
  let epilogue : List URMInstrRaw :=
    [ .incR vI, URMRaw.goto topPC, .stopR ]
  let rawList : List URMInstrRaw :=
    prelude ++ loopTop ++ zeroSweep ++ prologue ++ fBody
      ++ accUpdate ++ epilogue
  -- Shared boundedness facts.
  have hAcc : vAcc + 1 ≤ nR := by
    simp only [vAcc, nR, fBase]; omega
  have hBoundIn : vBoundIn + 1 ≤ nR := by
    simp only [vBoundIn, nR, fBase]; omega
  have hVX : vX + 1 ≤ nR := by
    simp only [vX, nR, fBase]; omega
  have hVI : vI + 1 ≤ nR := by
    simp only [vI, nR, fBase]; omega
  have hTmp1 : tmp1 + 1 ≤ nR := by
    simp only [tmp1, nR, fBase]; omega
  have hTmp2 : tmp2 + 1 ≤ nR := by
    simp only [tmp2, nR, fBase]; omega
  have hAccClone : vAccClone + 1 ≤ nR := by
    simp only [vAccClone, nR, fBase]; omega
  have hFactor : vFactor + 1 ≤ nR := by
    simp only [vFactor, nR, fBase]; omega
  have hMulTmp : vMulTmp + 1 ≤ nR := by
    simp only [vMulTmp, nR, fBase]; omega
  have hFOut : fBase + frag_f.outputReg.val + 1 ≤ nR := by
    have : frag_f.outputReg.val < frag_f.numRegs :=
      frag_f.outputReg.isLt
    simp only [nR]; omega
  have hPrologueSrc : ∀ s : Fin (k + 1),
      bsum_prologueSrc k s + 1 ≤ nR := by
    intro s
    have hs : s.val < k + 1 := s.isLt
    simp only [bsum_prologueSrc, nR, fBase]
    split <;> omega
  have hFIn : ∀ s : Fin (k + 1),
      fBase + (frag_f.inputRegs s).val + 1 ≤ nR := by
    intro s
    have : (frag_f.inputRegs s).val < frag_f.numRegs :=
      (frag_f.inputRegs s).isLt
    simp only [nR]; omega
  -- Boundedness of every block.
  have hPreludeBound : URMInstrRaw.boundedBy nR prelude := by
    intro ins hmem
    simp only [prelude, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hmem
    rcases hmem with ((h | h | h | h) | hpT) | h
    · rw [h]; simp only [URMInstrRaw.regBound]; omega
    · rw [h]; simp only [URMInstrRaw.regBound]; exact hAcc
    · rw [h]; simp only [URMInstrRaw.regBound]; exact hVX
    · rw [h]; simp only [URMInstrRaw.regBound]; exact hVI
    · exact boundedBy_preservingTransfer nR _ _ _ _
        hBoundIn hVX hTmp2 ins hpT
    · rw [h]; simp only [URMInstrRaw.regBound]; exact hAcc
  have hLoopTopBound : URMInstrRaw.boundedBy nR loopTop := by
    intro ins hmem
    simp only [loopTop, List.mem_cons, List.not_mem_nil,
      or_false] at hmem
    rcases hmem with h | h <;>
      (rw [h]; simp only [URMInstrRaw.regBound]; exact hVX)
  have hPrologueBound : URMInstrRaw.boundedBy nR prologue := by
    intro ins hmem
    simp only [prologue, List.mem_flatMap] at hmem
    rcases hmem with ⟨s, _, hs⟩
    exact boundedBy_bsum_prologueBlock frag_f fBase tmp1
      prologueBase nR s (hPrologueSrc s) (hFIn s) hTmp1 ins hs
  have hFBodyBound : URMInstrRaw.boundedBy nR fBody := by
    intro ins hmem
    simp only [fBody, List.mem_map] at hmem
    rcases hmem with ⟨ins', _, heq⟩
    rw [← heq]
    have hb : (toRawOfBounded ins').regBound ≤ frag_f.numRegs :=
      regBound_toRawOfBounded_le ins'
    have hr := regBound_reindexShift_le_offset_add fBase
      bodyPCBase frag_f.numRegs (toRawOfBounded ins') hb
    simp only [nR]; omega
  have hAccUpdateBound : URMInstrRaw.boundedBy nR accUpdate := by
    intro ins hmem
    simp only [accUpdate, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hmem
    rcases hmem with
      ((((hTr1 | hTr2) | hOuter) | hInner) | hTail)
    · exact boundedBy_transferLoop nR _ _ _
        hAcc hAccClone ins hTr1
    · exact boundedBy_transferLoop nR _ _ _
        hFOut hFactor ins hTr2
    · rcases hOuter with h | h
      · rw [h]; simp only [URMInstrRaw.regBound]; exact hFactor
      · rw [h]; simp only [URMInstrRaw.regBound]; exact hFactor
    · exact boundedBy_preservingTransfer nR _ _ _ _
        hAccClone hAcc hMulTmp ins hInner
    · rcases hTail with h | h
      · rw [h]; simp only [URMRaw.goto, URMInstrRaw.regBound]
        omega
      · rw [h]; simp only [URMInstrRaw.regBound]; exact hAccClone
  have hEpilogueBound : URMInstrRaw.boundedBy nR epilogue := by
    intro ins hmem
    simp only [epilogue, URMRaw.goto, List.mem_cons,
      List.not_mem_nil, or_false] at hmem
    rcases hmem with h | h | h
    · rw [h]; simp only [URMInstrRaw.regBound]; exact hVI
    · rw [h]; simp only [URMInstrRaw.regBound]; omega
    · rw [h]; simp only [URMInstrRaw.regBound]; omega
  have hZeroSweepBound : URMInstrRaw.boundedBy nR zeroSweep := by
    have hBlock : fBase + frag_f.numRegs ≤ nR := by
      simp only [nR]; omega
    exact boundedBy_bsum_zeroSweep frag_f fBase nR hBlock
  have hBound : URMInstrRaw.boundedBy nR rawList := by
    intro ins hmem
    simp only [rawList, List.mem_append] at hmem
    rcases hmem with
      (((((hP | hL) | hZ) | hPr) | hF) | hA) | hE
    · exact hPreludeBound ins hP
    · exact hLoopTopBound ins hL
    · exact hZeroSweepBound ins hZ
    · exact hPrologueBound ins hPr
    · exact hFBodyBound ins hF
    · exact hAccUpdateBound ins hA
    · exact hEpilogueBound ins hE
  -- Last raw instruction is `.stopR` (rightmost element
  -- of `epilogue`).
  have hEpiNeNil : epilogue ≠ [] := by
    simp only [epilogue, ne_eq, reduceCtorEq, not_false_eq_true]
  have hEpiLast : epilogue.getLast? = some .stopR := by
    simp only [epilogue]; rfl
  have hLastStopR : rawList.getLast? = some .stopR := by
    simp only [rawList]
    rw [List.getLast?_append_of_ne_nil _ hEpiNeNil]
    exact hEpiLast
  { numRegs := nR
    numRegs_pos := by simp only [nR, fBase]; omega
    inputRegs := fun j => ⟨2 + j.val, by
      have : j.val < k + 1 := j.isLt
      simp only [nR, fBase]; omega⟩
    outputReg := ⟨1, by simp only [nR, fBase]; omega⟩
    instrs := URMInstrRaw.toBoundedArray nR rawList hBound
    inputRegs_inj := by
      intro p q hpq
      apply Fin.ext
      have h : (2 + p.val : ℕ) = (2 + q.val : ℕ) :=
        congrArg Fin.val hpq
      omega
    outputReg_not_input := by
      intro p hp
      have h : (2 + p.val : ℕ) = (1 : ℕ) :=
        congrArg Fin.val hp
      omega
    zeroReg_not_input := by
      intro p hp
      have h : (2 + p.val : ℕ) = (0 : ℕ) :=
        congrArg Fin.val hp
      omega
    zeroReg_not_output := by
      intro h
      have h' : (0 : ℕ) = (1 : ℕ) := congrArg Fin.val h
      omega
    lastInstr_isStop :=
      URMInstrRaw.toBoundedArray_back?_of_last_stopR hBound
        hLastStopR }

/-- Recursive driver: emit a `CompiledFragment a` for
each `ERMor1 a` constructor by dispatching to the
per-constructor combinators. -/
def compileERFrag : {a : ℕ} → ERMor1 a → CompiledFragment a
  | _, .zero => compileFrag_zero
  | _, .succ => compileFrag_succ
  | _, .proj i => compileFrag_proj i
  | _, .sub => compileFrag_sub
  | _, .comp f gs =>
      compileFrag_comp (compileERFrag f)
        (fun i => compileERFrag (gs i))
  | _, .bsum f => compileFrag_bsum (compileERFrag f)
  | _, .bprod f => compileFrag_bprod (compileERFrag f)

/-- The top-level ER → URM compiler. Returns a
`URMProgram a` (arity-indexed per Task 0's refactor)
whose execution on input `v : Fin a → ℕ` produces
`e.interp v` in the output register. Spec §5; Tourlakis
2018 §0.1.0.37 (pp. 15–16) URM semantics; Tourlakis
2018 pp. 19–21 per-template constructions. -/
def compileER {a : ℕ} (e : ERMor1 a) : URMProgram a :=
  (compileERFrag e).toURMProgram

/-- Structural upper bound for `(compileERFrag e).numRegs`.
Mirrors `compileERFrag`'s recursion so the `bsum`/`bprod`
per-iteration zero-sweep cost (`frag_f.numRegs` `assignR`
instructions per iteration) can be folded into
`compileER_runtime` without exposing the compiled fragment. -/
def compileER_numRegs : {a : ℕ} → ERMor1 a → ℕ
  | _, .zero => 2
  | _, .succ => 4
  | a, .proj _ => a + 3
  | _, .sub => 6
  | a, .comp (k := k) f gs =>
      2 + a
        + ((List.finRange k).map
            (fun i => compileER_numRegs (gs i))).foldl
          (· + ·) 0
        + compileER_numRegs f + 1
  | _, .bsum (k := k) f => k + 7 + compileER_numRegs f
  | _, .bprod (k := k) f => k + 9 + compileER_numRegs f

/-- Runtime witness: a step count sufficient for
`URMState.runFor (compileER e) v` to reach a state where
the output register holds `e.interp v`. Structural
recursion on `e`; per-template costs match the spec §5.2
shape. Tourlakis 2018 §0.1.0.42 (p. 18) `f ∈ E^n` is
URM-computable within time `t ∈ E^n`. -/
def compileER_runtime : {a : ℕ} → ERMor1 a →
    (Fin a → ℕ) → ℕ
  | _, .zero, _ => 3
  | _, .succ, v => 12 + 10 * v 0
  | _, .proj i, v => 11 + 10 * v i
  | _, .sub, v => 20 + 10 * v 0 + 10 * v 1
  | a, .comp (k := k) f gs, v =>
      let inner : Fin k → ℕ := fun i => (gs i).interp v
      let v_total : ℕ :=
        ((List.finRange a).map v).foldl (· + ·) 0
      let glue : ℕ :=
        ((List.finRange k).map
          (fun i => compileER_runtime (gs i) v
            + 4 + 5 * inner i
            + 9 * v_total + 2 * a)).foldl (· + ·) 0
      glue + compileER_runtime f inner + 2
  | _, .bsum (k := k) f, v =>
      let bound : ℕ := v 0
      let nRegs_f : ℕ := compileER_numRegs f
      let perIter : ℕ → ℕ := fun i =>
        let ctx_f : Fin (k + 1) → ℕ :=
          Fin.cons i (Fin.tail v)
        let outerSum : ℕ :=
          ((List.finRange k).map (Fin.tail v)).foldl
            (· + ·) 0
        compileER_runtime f ctx_f
        + 50 + 10 * (i + outerSum)
        + 5 * f.interp ctx_f
        + nRegs_f
      30 + 10 * bound +
        ((List.range bound).map perIter).foldl (· + ·) 0
  | _, .bprod (k := k) f, v =>
      let bound : ℕ := v 0
      let nRegs_f : ℕ := compileER_numRegs f
      let perIter : ℕ → ℕ := fun i =>
        let ctx_f : Fin (k + 1) → ℕ :=
          Fin.cons i (Fin.tail v)
        let outerSum : ℕ :=
          ((List.finRange k).map (Fin.tail v)).foldl
            (· + ·) 0
        compileER_runtime f ctx_f
        + 60 + 10 * (i + outerSum)
        + 5 * f.interp ctx_f
        + nRegs_f
      40 + 10 * bound +
        ((List.range bound).map perIter).foldl (· + ·) 0


end LawvereERKSim
end GebLean
