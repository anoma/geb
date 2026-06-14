# Convenient rich-basis ERA — implementation plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan task-by-task.
> Steps use checkbox (`- [ ]`) syntax for tracking.

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [How to read this plan (Lean proof-development conventions)](#how-to-read-this-plan-lean-proof-development-conventions)
- [File structure](#file-structure)
- [Milestone M0a — rename `exp2` to `pow2`](#milestone-m0a--rename-exp2-to-pow2)
- [Milestone M0b — add the mul, div, pow primitives and axioms](#milestone-m0b--add-the-mul-div-pow-primitives-and-axioms)
  - [Step group A — rename derived operations to encodings](#step-group-a--rename-derived-operations-to-encodings)
  - [Step group B — add primitive constructors and notation](#step-group-b--add-primitive-constructors-and-notation)
  - [Step group C — the seven new axioms and `eraDefs`](#step-group-c--the-seven-new-axioms-and-eradefs)
- [Milestone M0c — soundness and primitive numeral computation](#milestone-m0c--soundness-and-primitive-numeral-computation)
- [Milestone M1a — categoricity for the structural operations](#milestone-m1a--categoricity-for-the-structural-operations)
- [Milestone M1b — categoricity for `mod`, `div`, and the capstone](#milestone-m1b--categoricity-for-mod-div-and-the-capstone)
- [Milestone M2 — recovery (Approach 2), the gate](#milestone-m2--recovery-approach-2-the-gate)
- [Milestone M3 — E1 `derivable_sub_eq_subFormula`](#milestone-m3--e1-derivable_sub_eq_subformula)
- [Milestone M4 — E2 `derivable_two_mul_eq_edmul`](#milestone-m4--e2-derivable_two_mul_eq_edmul)
- [Milestone M5 — E3 `derivable_div_eq_divFormula`](#milestone-m5--e3-derivable_div_eq_divformula)
- [Milestone M6 — E4 `derivable_mul_eq_mulFormula`](#milestone-m6--e4-derivable_mul_eq_mulformula)
- [Milestone M7 — E5 `derivable_pow_eq_powFormula`](#milestone-m7--e5-derivable_pow_eq_powformula)
- [Milestone M8 — pure-generator closure corollaries](#milestone-m8--pure-generator-closure-corollaries)
- [Self-review (completed during authoring)](#self-review-completed-during-authoring)

<!-- END doctoc -->

**Goal:** Replace `GebLean/Era.lean`'s near-minimal basis with the
convenient seven-primitive basis `{add, mod, pow2, tsub, mul, div, pow}`
(sound and categorical), then derive the five PSS superposition
identities as open `Derivable` redundancy theorems.

**Architecture:** Single file `GebLean/Era.lean`, extending the existing
logic-free equation calculus. The generic core is untouched. The seven
primitives carry eighteen recursion axioms; soundness and categoricity
(the recovery-independent base) come first; the recovery proof and the
five redundancy theorems (recovery-gated) follow. See the design spec
`docs/superpowers/specs/2026-06-13-era-rich-basis-design.md`.

**Tech stack:** Lean 4 + Mathlib (the project pin); `lake build`,
`lake test`, `lake lint`; `scripts/pre-commit.sh`;
`scripts/check-axioms.sh`.

**Resources for difficult steps.** When a step resists a direct proof,
bring the full toolset to bear rather than concluding it is unreachable:
`lean4:autoprove` and `lean4:sorry-filler-deep` for stubborn goals;
`lean4:autoformalize` for developments with precedent (in particular
Goodstein's double induction, which the recovery work draws on);
`lean4:prove`/`lean4:golf`/`lean4:refactor`; the `lean-lsp` search tools
(`leansearch`, `loogle`, `local_search`, `hammer_premise`); and
`superpowers:brainstorming` with `sequential-thinking` to re-plan a
phase. M2 (recovery) is the step most likely to be hard and is the one
most worth exhausting every avenue before escalating or deferring.

---

## How to read this plan (Lean proof-development conventions)

This is a proof-development plan. The unit of work is one declaration
(a `def`, `theorem`, or tight cluster). The TDD rhythm maps as:

- "Write the failing test" = state the declaration with its full
  signature and `:= by sorry` (or `:= _` to print the goal).
- "Run it to see it fail" = `lake build`; confirm the elaborated goal
  matches the intended statement (or that `sorry`/the underscore is the
  only error).
- "Implement" = supply the proof or body per the stated strategy.
- "Run to see it pass" = `lake build` (green, no `sorry`, no
  underscore).
- "Commit" = at each milestone boundary, `bash scripts/pre-commit.sh`
  then `scripts/check-axioms.sh`, then commit via `jj`
  (state-mutating `git` is hook-blocked; use `jj`).

Project rules binding every task:

- No `sorry`, `admit`, or underscore in any committed state. `sorry` is
  permitted only transiently between commits while a proof is in
  progress.
- Axiom-clean: `scripts/check-axioms.sh` must report only `propext`,
  `Quot.sound`, `Classical.choice` for every new declaration.
- New lines obey the 100-character limit; mathlib naming and docstring
  conventions apply (module docstring already present; every new `def`,
  `theorem`, and `axiom`-as-`def` carries a `/-- … -/` docstring).
- `lake build`/`lake test` only; never `lake env lean`, never
  `lake clean`.
- Within a milestone, intermediate non-compiling states are acceptable;
  every milestone's terminating commit must be green and axiom-clean.

The recovery-gated milestones (M2–M8) give exact statements and
strategies; their proof terms are discovered during execution. M2 is a
gate: its outcome (which recovery strength lands) determines the exact
tactics for M3–M8 and may require returning here to refine those tasks.

## File structure

Single file: `GebLean/Era.lean`. Content order after the change (the
generic core through `Derivable.sound` is unchanged):

1. Generic calculus (unchanged).
2. ERA instance: `EraB` (7 constructors), `eraAr`, smart constructors,
   `subst`/congruence lemmas, infix notation.
3. The eighteen axioms; `eraDefs`.
4. `eraInterp`; `eraDefs_sound`.
5. Categoricity: per-operation uniqueness; `eraInterp_unique`.
6. Numeral layer; consistency; closed-completeness.
7. Additive and order algebra (existing, retained).
8. Recovery proof.
9. Encodings (`subFormula`, `esq`, `edmul`, `divFormula`, `mulFormula`,
   `powFormula`) and their congruence/numeral lemmas.
10. Redundancy theorems E1–E5 and the pure-generator corollaries.

---

## Milestone M0a — rename `exp2` to `pow2`

**Files:** Modify `GebLean/Era.lean` (rename only; no semantic change).

**Rename table — rename every identifier containing `exp2` (the
complete set, confirmed by `grep -oE "[A-Za-z_]*exp2[A-Za-z_0-9]*"`):**

```text
EraB.exp2          → EraB.pow2      (inductive constructor)
eexp2              → epow2          (smart constructor)
eexp2_subst        → epow2_subst
eexp2_congr        → epow2_congr
app_exp2_eq        → app_pow2_eq
axExp0             → axPow2Z
axExpS             → axPow2S
numeral_exp2       → numeral_pow2
derivable_exp2_zero → derivable_pow2_zero
derivable_exp2_succ → derivable_pow2_succ
```

`derivable_pow2_succ` is cited by the M2 recovery proof, so its rename
must land in M0a. Update the `eraInterp` `.exp2` arm to `.pow2`, the
`eraAr` arm, the `eraDefs` list entries, the `eraDefs_sound`
`simp only [...]` list (which references `axExp0`/`axExpS` by name), and
the `closed_term_numeral` `.exp2` case to `.pow2`. The defining
equations are unchanged (`axPow2Z : 2^0 = 1`,
`axPow2S : 2^(S x) = 2^x + 2^x`).

- [ ] **Step 1: Apply the rename across the file.**
  Use the rename table. The `EraB` constructor rename is the
  load-bearing one; the rest follow it.

- [ ] **Step 2: Build green.**
  Run: `lake build`
  Expected: no errors. (`lake build` is authoritative; do not use
  `lake env lean`.)

- [ ] **Step 3: Commit M0a.**
  Run: `bash scripts/pre-commit.sh` then `scripts/check-axioms.sh`.
  Commit via `jj` with message `refactor(era): rename exp2 to pow2`.

---

## Milestone M0b — add the mul, div, pow primitives and axioms

This milestone renames the head's derived operations into the named
encodings, repoints the infix notation to new primitive constructors,
adds the seven new axioms, and assembles the eighteen-axiom `eraDefs`.
Intermediate states will not compile; only the final commit must be
green.

**Files:** Modify `GebLean/Era.lean`.

### Step group A — rename derived operations to encodings

- [ ] **Step 1: Rename the derived defs and their lemmas.**

```text
emul             → mulFormula
emul_congr       → mulFormula_congr
numeral_mul      → numeral_mulFormula
derivable_mul_zero → derivable_mulFormula_zero
ediv             → divFormula
ediv_congr       → divFormula_congr
numeral_div      → numeral_divFormula
derivable_div_zero → derivable_divFormula_zero
derivable_zero_div → derivable_zero_divFormula
epow             → powFormula
epow_congr       → powFormula_congr
numeral_pow      → numeral_powFormula
```

Critical: this is not a pure textual rename of the lemmas. The head
states these lemmas using the `*ᵉ`/`/ᵉ`/`^ᵉ` notation (e.g.
`derivable_mul_zero : ⟨u *ᵉ .zero, .zero⟩`), and Step group B repoints
that notation to the new primitives. Each renamed encoding lemma's
*statement* must therefore be rewritten to the explicit encoding head
(`mulFormula u .zero`, `numeral_mulFormula (.numeral a) (.numeral b)`,
`mulFormula_congr` over `mulFormula`, etc.), not left in notation —
otherwise the statement denotes the primitive while the body builds the
encoding, a type mismatch. The `_congr` lemmas restate directly. For
`numeral_powFormula`: because `powFormula`'s body keeps `*ᵉ` (the
primitive `mul`, per spec §5, see below), its numeral computation
depends on the primitive `numeral_mul`, which is added in M0c; defer
`numeral_powFormula` to M0c rather than treating it as an M0b rename.

Also delete the three old derived-operation notation declarations
(currently `infixl:70 " /ᵉ " => ediv` at Era.lean:1071,
`infixl:70 " *ᵉ " => emul` at :1096, `infixr:75 " ^ᵉ " => epow` at :1155).
Renaming the `def`s leaves these notations pointing at names that no
longer exist; they are re-added in Step group B bound to the new
primitive constructors. (Adding a second `infixl` for the same token
does not remove the first, so the old lines must be deleted, not merely
shadowed.)

`edmul`, `esq`, `subFormula` and their lemmas keep their names. The
`powFormula` body currently reads (in the head, as `epow`):

```lean
def powFormula {n : Nat} (s t : ETm n) : ETm n :=
  epow2 ((s *ᵉ t +ᵉ s +ᵉ one) *ᵉ t) %ᵉ (epow2 (s *ᵉ t +ᵉ s +ᵉ one) ∸ᵉ s)
```

Its `*ᵉ` occurrences are to denote the new primitive `mul` (Step group
B repoints the notation). Leave the body using `*ᵉ`; it resolves to the
primitive once the notation is repointed.

### Step group B — add primitive constructors and notation

- [ ] **Step 2: Extend `EraB` and `eraAr`.**

```lean
inductive EraB : Type
  | add | mod | pow2 | tsub | mul | div | pow
  deriving DecidableEq

def eraAr : EraB → Nat
  | .add => 2 | .mod => 2 | .pow2 => 1 | .tsub => 2
  | .mul => 2 | .div => 2 | .pow => 2
```

- [ ] **Step 3: Add smart constructors, `subst` lemmas, congruence
  lemmas, and repoint the infix notation** for `mul`, `div`, `pow`,
  modeled exactly on the existing `etsub`/`etsub_subst`/`etsub_congr`
  pattern.

```lean
def emul {n : Nat} (s t : ETm n) : ETm n := .app .mul (fcons s (fcons t Fin.elim0))
def ediv {n : Nat} (s t : ETm n) : ETm n := .app .div (fcons s (fcons t Fin.elim0))
def epow {n : Nat} (s t : ETm n) : ETm n := .app .pow (fcons s (fcons t Fin.elim0))
infixl:70 " *ᵉ " => emul
infixl:70 " /ᵉ " => ediv
infixr:75 " ^ᵉ " => epow
```

Add `emul_subst`/`ediv_subst`/`epow_subst` (copy the body of
`etsub_subst`, changing the symbol) and `emul_congr`/`ediv_congr`/
`epow_congr` (copy `etsub_congr`). Add `app_mul_eq`/`app_div_eq`/
`app_pow_eq` (copy `app_tsub_eq`). The old `*ᵉ`/`/ᵉ`/`^ᵉ` notations that
pointed to the now-renamed derived ops are removed by this repointing.

### Step group C — the seven new axioms and `eraDefs`

- [ ] **Step 4: Add the seven convenience axioms.**

```lean
def axMul0 : (n : Nat) × EEqn n := ⟨1, ⟨(.var 0) *ᵉ .zero, .zero⟩⟩
def axMulS : (n : Nat) × EEqn n :=
  ⟨2, ⟨(.var 0) *ᵉ .succ (.var 1), ((.var 0) *ᵉ (.var 1)) +ᵉ (.var 0)⟩⟩
def axPow0 : (n : Nat) × EEqn n := ⟨1, ⟨(.var 0) ^ᵉ .zero, one⟩⟩
def axPowS : (n : Nat) × EEqn n :=
  ⟨2, ⟨(.var 0) ^ᵉ .succ (.var 1), ((.var 0) ^ᵉ (.var 1)) *ᵉ (.var 0)⟩⟩
def axDivZ : (n : Nat) × EEqn n := ⟨1, ⟨(.var 0) /ᵉ .zero, .zero⟩⟩
def axDiv0 : (n : Nat) × EEqn n := ⟨1, ⟨(.zero : ETm 1) /ᵉ .succ (.var 0), .zero⟩⟩
def axDivS : (n : Nat) × EEqn n :=
  ⟨2, ⟨.succ (.var 0) /ᵉ .succ (.var 1),
       ((.var 0) /ᵉ .succ (.var 1)) +ᵉ
         (one ∸ᵉ ((.var 1) ∸ᵉ ((.var 0) %ᵉ .succ (.var 1))))⟩⟩
```

Note `axDivS` uses the primitive remainder `x mod S y` (the design
refinement), not `daab65a9`'s spelled-out `x ∸ S y · (x / S y)`.

- [ ] **Step 5: Assemble the eighteen-axiom `eraDefs`.**

```lean
def eraDefs : Defs EraB eraAr :=
  [axAdd0, axAddS, axMod0, axModLt, axModAdd, axPow2Z, axPow2S,
   axSub0, axSubS, axPred0, axPredS,
   axMul0, axMulS, axPow0, axPowS, axDivZ, axDiv0, axDivS]
```

- [ ] **Step 6: Build green.**
  Run: `lake build`
  Expected: no errors. Two membership-witness styles in the file react
  differently to the list growing to eighteen: the `derivable_def
  (by simp [eraDefs, axFoo])` witnesses are name-driven and robust, but
  the explicit hand-built chains (`.head _` / `.tail _ (.head _)`, e.g.
  in `derivable_zero_add`) are position-sensitive. The new axioms append
  after the existing eleven and `axAdd0`/`axAddS` stay at positions 0/1,
  so the explicit chains survive; confirm at this build.

- [ ] **Step 7: Update the module docstring.**
  The head module docstring describes "the minimal three-element
  substitution basis `{x+y, x mod y, 2ˣ}`" with Mazzanti's operations
  "derived as terms over this basis"; after this milestone `mul`/`div`/
  `pow` are primitives, so that text is false. Rewrite the basis
  description to the seven-primitive convenient basis and its
  generator/convenience partition; update the `## References` section;
  and mark the `axDivS` `mod`-remainder refinement as a novel
  modification of `daab65a9` (per spec §10 and the cite-the-literature
  rule). Re-run `lake build`.

- [ ] **Step 8: Commit M0b.**
  `bash scripts/pre-commit.sh`; `scripts/check-axioms.sh`; commit via
  `jj` with `feat(era): add mul/div/pow primitives and recursion axioms`.

---

## Milestone M0c — soundness and primitive numeral computation

**Files:** Modify `GebLean/Era.lean`.

- [ ] **Step 1: Extend `eraInterp`.**

```lean
def eraInterp : (b : EraB) → (Fin (eraAr b) → Nat) → Nat
  | .add,  v => v ⟨0, by decide⟩ + v ⟨1, by decide⟩
  | .mod,  v => v ⟨0, by decide⟩ % v ⟨1, by decide⟩
  | .pow2, v => 2 ^ v ⟨0, by decide⟩
  | .tsub, v => v ⟨0, by decide⟩ - v ⟨1, by decide⟩
  | .mul,  v => v ⟨0, by decide⟩ * v ⟨1, by decide⟩
  | .div,  v => v ⟨0, by decide⟩ / v ⟨1, by decide⟩
  | .pow,  v => v ⟨0, by decide⟩ ^ v ⟨1, by decide⟩
```

- [ ] **Step 2: Add the `Nat` lemma `succ_div_succ`** (transcribe from
  `daab65a9`, lines 419–435), then adapt for the `mod`-form remainder.

Strategy: `daab65a9`'s `succ_div_succ` proves the increment recurrence
with remainder `x - (y+1)*(x/(y+1))`. Transcribe its proof, then rewrite
that remainder to `x % (y+1)`. The rewrite is *not* a bare `omega` step:
`omega` is linear and cannot see `(y+1)*(x/(y+1))`. Introduce the
division identity as a hypothesis first — `have hdm := Nat.div_add_mod x
(y+1)` — and follow `daab65a9`'s case split on whether the remainder has
reached `y` (`x % (y+1) = y` versus `< y`); each branch then closes by
`omega` with `hdm` (and the relevant `Nat.add_mul_div`/`Nat.div_eq_of_lt`
facts) in context.

```lean
theorem succ_div_succ (x y : Nat) :
    (x + 1) / (y + 1)
      = x / (y + 1) + (1 - (y - x % (y + 1))) := by
  have hdm := Nat.div_add_mod x (y + 1)
  -- daab65a9 case split on x % (y+1) = y vs < y; close each by omega
  -- with hdm in context. Mirror daab65a9 lines 419-435.
  sorry
```

- [ ] **Step 3: Extend `eraDefs_sound`** to discharge all eighteen
  axioms.

Strategy: keep the head's generator arms; add arms for the seven new
axioms. The `mul`/`pow` arms close by `Nat.mul_succ`/`Nat.pow_zero`/
`Nat.pow_succ`/`Nat.mul_zero`; the `div` arms by `Nat.div_zero`,
`Nat.zero_div`, and `succ_div_succ`. Extend the `refine ⟨…⟩` to
eighteen goals and the discharge `first | …` block with the new cases
(model on `daab65a9`'s `eraDefs_sound`, lines 438–455).

- [ ] **Step 4: Re-derive the primitive numeral lemmas.**

```lean
theorem numeral_mul {n : Nat} (a b : Nat) :
    Derivable eraDefs ⟨(.numeral a : ETm n) *ᵉ .numeral b, .numeral (a * b)⟩
theorem numeral_pow {n : Nat} (a b : Nat) :
    Derivable eraDefs ⟨(.numeral a : ETm n) ^ᵉ .numeral b, .numeral (a ^ b)⟩
theorem numeral_div {n : Nat} (a b : Nat) :
    Derivable eraDefs ⟨(.numeral a : ETm n) /ᵉ .numeral b, .numeral (a / b)⟩
```

Strategy: transcribe `daab65a9`'s `numeral_mul`/`numeral_pow`/
`numeral_div` (lines 678–721), replacing its `bin_congr .mul` with the
per-op `emul_congr` and so on. `numeral_div` recurses with `succ_div_succ`
and a nested induction; follow `daab65a9` exactly. Then derive
`numeral_powFormula` (deferred from M0b, since `powFormula` uses the
primitive `*ᵉ`): transcribe the head's old `numeral_pow` body (now over
`powFormula`), which composes the primitive `numeral_mul` just derived.
Restate any encoding intermediates (`numeral_mulFormula`,
`numeral_divFormula`) with explicit `…Formula` heads if a proof needs
them.

- [ ] **Step 5: Add the primitive recursion-law instances.** The
  redundancy proofs (M5/M6/M7) consume these as `uniq` base/step inputs;
  they are direct instantiations of the new axioms, modeled on the head's
  `derivable_sub_zero` (each is one `derivable_def` application plus a
  `simp only [Tm.subst, …]` cleanup):

```lean
theorem derivable_mul_zero {n : Nat} (u : ETm n) :
    Derivable eraDefs ⟨u *ᵉ .zero, .zero⟩
theorem derivable_mul_succ {n : Nat} (u v : ETm n) :
    Derivable eraDefs ⟨u *ᵉ .succ v, (u *ᵉ v) +ᵉ u⟩
theorem derivable_pow_zero {n : Nat} (u : ETm n) :
    Derivable eraDefs ⟨u ^ᵉ .zero, one⟩
theorem derivable_pow_succ {n : Nat} (u v : ETm n) :
    Derivable eraDefs ⟨u ^ᵉ .succ v, (u ^ᵉ v) *ᵉ u⟩
theorem derivable_div_zero {n : Nat} (u : ETm n) :
    Derivable eraDefs ⟨u /ᵉ .zero, .zero⟩
theorem derivable_zero_div {n : Nat} (u : ETm n) :
    Derivable eraDefs ⟨(.zero : ETm n) /ᵉ .succ u, .zero⟩
theorem derivable_div_succ {n : Nat} (u v : ETm n) :
    Derivable eraDefs
      ⟨.succ u /ᵉ .succ v,
       (u /ᵉ .succ v) +ᵉ (one ∸ᵉ (v ∸ᵉ (u %ᵉ .succ v)))⟩
```

  These names (`derivable_mul_zero` etc.) refer to the new primitives;
  they are distinct from the encoding zero-laws `derivable_mulFormula_zero`
  /`derivable_divFormula_zero`/`derivable_zero_divFormula` renamed in M0b.

- [ ] **Step 6: Update `closed_term_numeral`** to cover the seven
  constructors (`.add`, `.mod`, `.pow2`, `.tsub`, `.mul`, `.div`,
  `.pow`), one arm per constructor of the form:

```lean
| <op> => rw [app_<op>_eq ts]
          exact (<op>_congr (ih _) (ih _)).trans (numeral_<op> _ _)
```

- [ ] **Step 7: Build green; confirm no `sorry`.**
  Run: `lake build`
  Expected: no errors, no `sorry` (replace the Step 2 `sorry`).

- [ ] **Step 8: Commit M0c.**
  `bash scripts/pre-commit.sh`; `scripts/check-axioms.sh`; commit via
  `jj` with `feat(era): prove soundness and numeral computation for the
  rich basis`.

---

## Milestone M1a — categoricity for the structural operations

**Files:** Modify `GebLean/Era.lean` (new section after
`eraDefs_sound`).

Each lemma: any `Nat`-valued function satisfying the operation's axioms
equals the intended `Nat` operation, given dependency operations pinned.
These are `Nat`-meta inductions, recovery-independent.

- [ ] **Step 1: `add` uniqueness.**

```lean
theorem add_unique (g : Nat → Nat → Nat)
    (h0 : ∀ x, g x 0 = x) (hS : ∀ x y, g x (y + 1) = g x y + 1) :
    ∀ x y, g x y = x + y
```

Strategy: `intro x y; induction y` ; base `h0`; step `hS` + `ih`.

- [ ] **Step 2: `tsub`/`pred` uniqueness.**

```lean
theorem sub_unique (g : Nat → Nat → Nat)
    (h0 : ∀ x, g x 0 = x) (hS : ∀ x y, g x (y + 1) = g (g x y) 1)
    (hp0 : g 0 1 = 0) (hpS : ∀ x, g (x + 1) 1 = x) :
    ∀ x y, g x y = x - y
```

Strategy: first prove `∀ z, g z 1 = z - 1` by `cases z` (hp0/hpS); then
`induction y` using `hS` and that fact; close with `omega`.

- [ ] **Step 3: `mul` uniqueness** (depends on `add` pinned).

```lean
theorem mul_unique (g : Nat → Nat → Nat)
    (h0 : ∀ x, g x 0 = 0) (hS : ∀ x y, g x (y + 1) = g x y + x) :
    ∀ x y, g x y = x * y
```

Strategy: `induction y`; step uses `hS`, `ih`, `Nat.mul_succ`.

- [ ] **Step 4: `pow` uniqueness** (depends on `mul`).

```lean
theorem pow_unique (g : Nat → Nat → Nat)
    (h0 : ∀ x, g x 0 = 1) (hS : ∀ x y, g x (y + 1) = g x y * x) :
    ∀ x y, g x y = x ^ y
```

Strategy: `induction y`; step uses `hS`, `ih`, `Nat.pow_succ`.

- [ ] **Step 5: `pow2` uniqueness** (depends on `add`).

```lean
theorem pow2_unique (g : Nat → Nat)
    (h0 : g 0 = 1) (hS : ∀ x, g (x + 1) = g x + g x) :
    ∀ x, g x = 2 ^ x
```

Strategy: `induction x`; step uses `hS`, `ih`, `Nat.pow_succ`, `omega`.

- [ ] **Step 6: Build green; commit M1a.**
  `lake build`; `bash scripts/pre-commit.sh`; `scripts/check-axioms.sh`;
  commit via `jj` with `feat(era): prove categoricity of the structural
  operations`.

---

## Milestone M1b — categoricity for `mod`, `div`, and the capstone

**Files:** Modify `GebLean/Era.lean`.

- [ ] **Step 1: `mod` uniqueness** (depends on `add`).

```lean
theorem mod_unique (g : Nat → Nat → Nat)
    (h0 : ∀ x, g x 0 = x)
    (hlt : ∀ x y, g x (x + (y + 1)) = x)
    (hadd : ∀ x y, g (x + y) y = g x y) :
    ∀ x y, g x y = x % y
```

Strategy: `cases y`; for `0`, `h0` and `Nat.mod_zero`. For `y+1`:
strong induction on `x` via `induction x using Nat.strongRecOn`
(or `Nat.strong_induction_on`; both exist in the pin and are
axiom-clean). If `x < y+1`, write `y+1 = x + (k+1)`
and apply `hlt`, matching `Nat.mod_eq_of_lt`. If `x ≥ y+1`, write
`x = (x-(y+1)) + (y+1)`, apply `hadd` to peel, then the induction
hypothesis on `x-(y+1)`, matching `Nat.add_mod_right`. This mirrors the
head's `numeral_mod` case split.

- [ ] **Step 2: `div` uniqueness** (depends on `add`, `mod`, `tsub`).

```lean
theorem div_unique (g : Nat → Nat → Nat)
    (hz : ∀ x, g x 0 = 0) (h0 : ∀ y, g 0 (y + 1) = 0)
    (hS : ∀ x y, g (x + 1) (y + 1)
            = g x (y + 1) + (1 - (y - x % (y + 1)))) :
    ∀ x y, g x y = x / y
```

Strategy: `cases y`; `0` by `hz`/`Nat.div_zero`. For `y+1`: induction on
`x`; base `h0`/`Nat.zero_div`; step `hS` + `ih` + `succ_div_succ`.

- [ ] **Step 3: Per-symbol axiom-extraction helpers.** For each symbol,
  state a helper that pulls its axiom equations out of `hI` into the
  pointwise `Nat` form the `*_unique` lemma expects (each axiom's `eval`
  unfolds through `Tm.eval`, the smart constructors, and `fcons`).
  Membership in `eraDefs` is discharged by `simp`/`List` lemmas. Prove
  one symbol at a time, building after each so a failure localizes:

```lean
-- shape (one per symbol); e.g. add:
have hadd0 : ∀ x, I .add (fcons x (fcons 0 Fin.elim0)) = x := …
have haddS : ∀ x y,
    I .add (fcons x (fcons (y+1) Fin.elim0))
      = I .add (fcons x (fcons y Fin.elim0)) + 1 := …
```

  Run `lake build` after each symbol's helper.

- [ ] **Step 4: Assemble `eraInterp_unique`.**

```lean
theorem eraInterp_unique
    (I : (b : EraB) → (Fin (eraAr b) → Nat) → Nat)
    (hI : ∀ d ∈ eraDefs, ∀ ρ : Fin d.1 → Nat,
            d.2.lhs.eval I ρ = d.2.rhs.eval I ρ) :
    I = eraInterp
```

  `funext b v`; `cases b`; in each arm feed the Step 3 helpers to the
  matching `*_unique` lemma in dependency order (`add`, then `tsub`,
  `mul`, `pow`, `pow2`, `mod`, `div`), and rewrite `v` to its components
  via `fcons` eta (`fcons_eta`).

- [ ] **Step 5: Build green; commit M1b.**
  `lake build`; `bash scripts/pre-commit.sh`; `scripts/check-axioms.sh`;
  commit via `jj` with `feat(era): prove the categoricity capstone
  eraInterp_unique`.

**Checkpoint:** M0a–M1b is the recovery-independent base result. The
bookmark is mergeable here even if the recovery-gated milestones do not
complete.

---

## Milestone M2 — recovery (Approach 2), the gate

**Files:** Modify `GebLean/Era.lean` (new section after the order
algebra).

This is the hardest step. Per the "Resources for difficult steps" note
above, exhaust every avenue here before escalating or deferring:
`lean4:autoformalize`/`lean4:autoprove` (Goodstein's double induction
has precedent for the autoformalizer), `lean4:sorry-filler-deep`, the
`lean-lsp` search tools, and `superpowers:brainstorming` with
`sequential-thinking` to re-plan the approach if Approaches 2/1/3 all
stall.

**Goal statement (the witnessed-domination form `derivable_esubAt_of_add`
consumes):**

```lean
theorem derivable_two_pow_dominates {n : Nat} (a : ETm n) :
    ∃ p : ETm n, Derivable eraDefs ⟨epow2 a, a +ᵉ .succ p⟩
```

or, if a closed-form witness `p` is preferable, the explicit form

```lean
theorem derivable_add_sub_two_pow {n : Nat} (a : ETm n) :
    Derivable eraDefs ⟨a +ᵉ (epow2 a ∸ᵉ a), epow2 a⟩
```

- [ ] **Step 1: State the goal with `sorry`; confirm the goal.**
  Run: `lake build`; confirm the elaborated goal is as intended.

- [ ] **Step 2: Prove by induction on `a`** via `uniq`, reusing the
  existing order-algebra lemmas (`derivable_self_sub_add`,
  `derivable_add_sub_add_left`, `derivable_one_le_two_pow`,
  `derivable_add_sub_cancel_left`, `derivable_sub_add`). The step relates
  `2^(S a) = 2^a + 2^a` (`derivable_pow2_succ`, renamed in M0a) to the
  witness at `a`. Blueprint: the `Nat` facts `Nat.lt_two_pow_self` and
  `subFormula_eval`'s domination bounds.

- [ ] **Step 3: GATE — fix the recovery strength needed downstream.**
  If Step 2 closes with the existing order algebra, E1 (M3) is unblocked
  (it consumes only the narrow witnessed form via
  `derivable_esubAt_of_add`). Before proceeding past M3, probe a
  representative E3/E5 step obligation (the modulus domination in
  `div_identity`/`pow_identity`): if it needs the general symmetric
  identity rather than the narrow `2^e` form, prove Approach 1 now,
  within M2, to avoid re-opening the gate mid-execution. Escalation
  ladder per spec §7:
  - Approach 1: prove `derivable_add_sub_symm`
    (`a + (b ∸ a) = b + (a ∸ b)`) by `uniq` on the first argument, with
    the isolated lemma `(b + (a ∸ b)) ∸ a = b ∸ a` by nested `uniq`;
    then specialize.
  - Approach 3: build the bounded-sum term-former and Goodstein's
    order-algebra development (downstream infrastructure, itself most
    likely downstream of recovery; record the escalation and amend this
    plan if it changes M5–M8).
  Record the decision in the commit message; amend this plan if it
  changes the downstream strategy.

- [ ] **Step 4: Build green; commit M2.**
  `lake build` (no `sorry`); `bash scripts/pre-commit.sh`;
  `scripts/check-axioms.sh`; commit via `jj` with
  `feat(era): derive exponential domination with witness`.

---

## Milestone M3 — E1 `derivable_sub_eq_subFormula`

**Files:** Modify `GebLean/Era.lean`.

**Statement:**

```lean
theorem derivable_sub_eq_subFormula {n : Nat} (x y : ETm n) :
    Derivable eraDefs ⟨x ∸ᵉ y, subFormula x y⟩
```

- [ ] **Step 1: State with `sorry`; confirm goal via `lake build`.**

- [ ] **Step 2: Prove** by deciding `subFormula` against `tsub`'s axioms
  via the `esubAt` template. Use `subFormula_eq_esubAt`,
  `derivable_esubAt_of_add` (discharging its `hdom` hypothesis with M2's
  `derivable_two_pow_dominates`/`derivable_add_sub_two_pow`), and
  `derivable_esubAt_of_lt`. Blueprint: `subFormula_eval`. The proof
  shows `subFormula x y` satisfies the same recursion as `x ∸ᵉ y` (or
  matches by the two `esubAt` shape lemmas), then concludes equality.

- [ ] **Step 3: Build green; commit M3.**
  `feat(era): derive subtraction redundancy (PSS Lemma 2)`.

---

## Milestone M4 — E2 `derivable_two_mul_eq_edmul`

**Files:** Modify `GebLean/Era.lean`.

**Statement:**

```lean
theorem derivable_two_mul_eq_edmul {n : Nat} (x y : ETm n) :
    Derivable eraDefs ⟨.numeral 2 *ᵉ (x *ᵉ y), edmul x y⟩
```

- [ ] **Step 1: State with `sorry`; confirm goal.**

- [ ] **Step 2: Prove.** Strategy: derive the witnessed squaring-sum
  identity `esq (x +ᵉ y) = (esq x +ᵉ esq y) +ᵉ (.numeral 2 *ᵉ (x *ᵉ y))`,
  then `edmul x y = esq (x+y) ∸ (esq x + esq y)` reduces by
  `derivable_add_sub_cancel_left` (already proven, recovery-free *given*
  the witnessed identity). Whether the squaring-sum identity itself
  needs M2's domination is decided here (spec §5); if it does, reuse M2.
  Blueprint: `dmul_identity`, `sq_identity`.

- [ ] **Step 3: Build green; commit M4.**
  `feat(era): derive double-product redundancy`.

---

## Milestone M5 — E3 `derivable_div_eq_divFormula`

**Files:** Modify `GebLean/Era.lean`.

Division precedes multiplication: E4 reduces to E3 plus a divide-by-2
lemma, so E3 lands first. This intentionally reorders the spec §8
milestone table, which listed E4 (mul) before E3 (div).

**Statement:**

```lean
theorem derivable_div_eq_divFormula {n : Nat} (x y : ETm n) :
    Derivable eraDefs ⟨x /ᵉ y, divFormula x y⟩
```

- [ ] **Step 1: State with `sorry`; confirm goal.**

- [ ] **Step 2: Prove** by `uniq`/`ext_succ` showing `divFormula`
  satisfies `div`'s axioms (`axDivZ`, `axDiv0`, `axDivS`): base cases via
  the encoding zero-laws `derivable_divFormula_zero`/
  `derivable_zero_divFormula`; the dividend-step matches `axDivS`'s
  increment recurrence (the primitive form is `derivable_div_succ`, M0c
  Step 5). High-risk: the step induction consumes M2's domination (the
  modulus `edmul (S x) y ∸ 1` must dominate). If M2 delivered only
  Approach 2's narrow form and the step needs the general symmetric
  identity, escalate per the M2 gate. Blueprint: `div_identity`.

- [ ] **Step 3: Build green; commit M5.**
  `feat(era): derive division redundancy (PSS Lemma 3)`.

---

## Milestone M6 — E4 `derivable_mul_eq_mulFormula`

**Files:** Modify `GebLean/Era.lean`.

**Statement** (recall `mulFormula x y = divFormula (edmul x y) (numeral 2)`):

```lean
theorem derivable_mul_eq_mulFormula {n : Nat} (x y : ETm n) :
    Derivable eraDefs ⟨x *ᵉ y, mulFormula x y⟩
```

- [ ] **Step 1: Prove the divide-by-2 lemma.**

```lean
theorem derivable_two_mul_div_two {n : Nat} (z : ETm n) :
    Derivable eraDefs ⟨(.numeral 2 *ᵉ z) /ᵉ .numeral 2, z⟩
```

Strategy: a division fact at the fixed divisor 2, from the primitive
`div` axioms or from E3 (`derivable_div_eq_divFormula`) with
`div_identity` at divisor 2. Decide at this step whether it is
recovery-free; if it consumes domination, it inherits M2.

- [ ] **Step 2: Prove E4 by the algebraic chain** (no `uniq`):
  from E2 (`derivable_two_mul_eq_edmul`) rewrite `edmul x y` to
  `.numeral 2 *ᵉ (x *ᵉ y)`; from `derivable_two_mul_div_two (x *ᵉ y)`
  obtain `(.numeral 2 *ᵉ (x *ᵉ y)) /ᵉ .numeral 2 = x *ᵉ y`; hence
  `(edmul x y) /ᵉ .numeral 2 = x *ᵉ y`. Rewrite the primitive `/ᵉ` to
  `divFormula` via E3 (`ediv_congr`/instantiation) to reach
  `mulFormula x y = divFormula (edmul x y) (numeral 2)`. Conclude
  `x *ᵉ y = mulFormula x y` by `symm`/`trans`.

- [ ] **Step 3: Build green; commit M6.**
  `feat(era): derive multiplication redundancy`.

---

## Milestone M7 — E5 `derivable_pow_eq_powFormula`

**Files:** Modify `GebLean/Era.lean`.

**Statement:**

```lean
theorem derivable_pow_eq_powFormula {n : Nat} (x y : ETm n) :
    Derivable eraDefs ⟨x ^ᵉ y, powFormula x y⟩
```

- [ ] **Step 1: State with `sorry`; confirm goal.**

- [ ] **Step 2: Prove** by `uniq` showing `powFormula` satisfies `pow`'s
  axioms (`axPow0`, `axPowS`): base `powFormula x 0 = 1`; step
  `powFormula x (S y) = powFormula x y * x`. Highest-risk task: the step
  relates the modular representation at `y+1` to `y` and consumes the
  domination `x^y < 2^(xy+x+1) ∸ x`. Blueprint: `pow_identity` and
  `pow_mod_rep` (already in the file as `Nat` lemmas). Escalate per the
  M2 gate if needed.

- [ ] **Step 3: Build green; commit M7.**
  `feat(era): derive exponentiation redundancy`.

---

## Milestone M8 — pure-generator closure corollaries

**Files:** Modify `GebLean/Era.lean`.

**Goal:** express each convenience operation over the bare
`{add, mod, pow2}` by substituting E1 (eliminating `tsub`) and E4
(eliminating `mul` from `powFormula`).

- [ ] **Step 1: State the corollaries** (one per convenience op), e.g.

```lean
theorem derivable_sub_eq_generators {n : Nat} (x y : ETm n) :
    Derivable eraDefs ⟨x ∸ᵉ y, subFormula x y⟩
-- subFormula is already over {add, mod, pow2}; E1 is the corollary.
theorem derivable_mul_eq_generators {n : Nat} (x y : ETm n) :
    Derivable eraDefs ⟨x *ᵉ y, mulFormulaGen x y⟩
-- mulFormulaGen: mulFormula with every ∸ᵉ replaced by subFormula.
```

Define the `…Gen` encodings (each `…Formula` with `∸ᵉ` replaced by
`subFormula` and, for `powFormula`, `*ᵉ` replaced by `mulFormulaGen`).

- [ ] **Step 2: Prove** each corollary by transitivity from the E1–E5
  theorem and congruence rewriting (`etsub_congr` with E1, `emul_congr`
  with E4) to substitute the residual `tsub`/`mul`.

- [ ] **Step 3: Build green; commit M8.**
  `feat(era): object-level pure-generator closure (PSS minimality)`.

---

## Self-review (completed during authoring)

- **Spec coverage:** §3 basis/axioms → M0a/M0b (with the module-docstring
  update, M0b Step 7); §4 soundness → M0c, categoricity → M1a/M1b; §5
  E1 → M3, E2 → M4, E3 → M5, E4 → M6, E5 → M7, closure → M8; §7 recovery
  → M2 with the escalation gate. Acceptance §11 base = M0a–M1b;
  redundancy = M3–M8.
- **Placeholders:** the `sorry` markers in M2–M8 are transient
  proof-in-progress states with stated strategies and blueprints, not
  vague TODOs; every declaration carries an exact statement. M0c Step 2
  carries one transient `sorry` removed by M0c Step 7.
- **Type consistency:** encoding names (`subFormula`, `esq`, `edmul`,
  `divFormula`, `mulFormula`, `powFormula`), theorem names
  (`derivable_<op>_eq_<encoding>`), the primitive recursion-law instances
  (`derivable_mul_zero`/`_succ`, `derivable_div_zero`/`_succ`,
  `derivable_zero_div`, `derivable_pow_zero`/`_succ`, distinct from the
  encoding zero-laws `derivable_mulFormula_zero` etc.), and
  `*_unique`/`eraInterp_unique` are used consistently. `mulFormula` is
  defined in M0b Step group A and used in M6/M8.
- **Sequencing:** division (E3, M5) precedes multiplication (E4, M6),
  since E4 reduces to E3 plus `derivable_two_mul_div_two`; this reorders
  the spec §8 table. Recovery strength: M3 (E1) uses only the narrow
  Approach-2 form; M5/M7 (div/pow) may require Approach 1's general
  identity, probed and fixed at the M2 gate (M2 Step 3).
