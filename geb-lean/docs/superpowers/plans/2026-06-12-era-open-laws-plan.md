# Era open-term recursion laws implementation plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan
> task-by-task. Steps use checkbox (`- [ ]`) syntax for
> tracking. Lean proof scripts are discovered during execution
> with the `lean4` skills; each task fixes the theorem signature
> (determined by the spec) and the proof strategy, and the
> worker fills the tactic script.

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Reference documents](#reference-documents)
- [Conventions for every task](#conventions-for-every-task)
- [File structure](#file-structure)
- [Phase 0 — infrastructure](#phase-0--infrastructure)
  - [Task 0.1: name the additive flip `0 + x = x`](#task-01-name-the-additive-flip-0--x--x)
  - [Task 0.2: zero/successor extensionality rule (E₃)](#task-02-zerosuccessor-extensionality-rule-e%E2%82%83)
- [Phase 1 — additive algebra by `uniq`](#phase-1--additive-algebra-by-uniq)
  - [Task 1.1: `succ_add` (Goodstein (7))](#task-11-succ_add-goodstein-7)
  - [Task 1.2: `add_comm` (Goodstein (8))](#task-12-add_comm-goodstein-8)
  - [Task 1.3: `add_assoc` (Goodstein (10))](#task-13-add_assoc-goodstein-10)
- [Phase 2 — mod corollaries](#phase-2--mod-corollaries)
  - [Task 2.1: `zero_mod`](#task-21-zero_mod)
  - [Task 2.2: `mod_self`](#task-22-mod_self)
- [Phase 3 — laws not requiring domination](#phase-3--laws-not-requiring-domination)
  - [Task 3.1: `zero_sub` (E₃ split)](#task-31-zero_sub-e%E2%82%83-split)
  - [Task 3.2: `sub_self`](#task-32-sub_self)
  - [Task 3.3: `pred_zero` (deliverable 3 of 11)](#task-33-pred_zero-deliverable-3-of-11)
  - [Task 3.4: `edmul_zero`](#task-34-edmul_zero)
  - [Task 3.5: `mul_zero` (deliverable 5 of 11)](#task-35-mul_zero-deliverable-5-of-11)
  - [Task 3.6: `div_zero` (deliverable 9 of 11)](#task-36-div_zero-deliverable-9-of-11)
  - [Task 3.7: `zero_div` (deliverable 10 of 11)](#task-37-zero_div-deliverable-10-of-11)
  - [Task 3.8: Phase 3 checkpoint](#task-38-phase-3-checkpoint)
- [Phase 4a — the subtraction cluster](#phase-4a--the-subtraction-cluster)
  - [Task 4a.1: the `esubAt` template definition](#task-4a1-the-esubat-template-definition)
  - [Task 4a.2: the two shape-decided template laws](#task-4a2-the-two-shape-decided-template-laws)
  - [Task 4a.3: the exponential-domination family (OPEN obligation)](#task-4a3-the-exponential-domination-family-open-obligation)
  - [Task 4a.4: `sub_zero` (deliverable 1 of 11; verified reduction)](#task-4a4-sub_zero-deliverable-1-of-11-verified-reduction)
  - [Task 4a.5: `pred_succ` (deliverable 4 of 11; verified reduction)](#task-4a5-pred_succ-deliverable-4-of-11-verified-reduction)
  - [Task 4a.6: subtraction cluster entry — (1)/(2)/`sub_succ` (OPEN)](#task-4a6-subtraction-cluster-entry--12sub_succ-open)
- [Phase 4b — the multiplicative cluster](#phase-4b--the-multiplicative-cluster)
  - [Task 4b.1: multiplicative cluster entry (OPEN)](#task-4b1-multiplicative-cluster-entry-open)
  - [Task 4b.2: multiplicative algebra as needed](#task-4b2-multiplicative-algebra-as-needed)
  - [Task 4b.3: `pow_zero` (deliverable 7 of 11; verified reduction)](#task-4b3-pow_zero-deliverable-7-of-11-verified-reduction)
  - [Task 4b.4: `pow_succ` and `div_succ` (deliverables 8, 11 of 11; OPEN depth)](#task-4b4-pow_succ-and-div_succ-deliverables-8-11-of-11-open-depth)
- [Final verification](#final-verification)
  - [Task F.1: full-suite green and axiom audit](#task-f1-full-suite-green-and-axiom-audit)
  - [Task F.2: optional cleanup (spec §9)](#task-f2-optional-cleanup-spec-9)
  - [Task F.3: documentation and handoff](#task-f3-documentation-and-handoff)
- [Self-review notes](#self-review-notes)

<!-- END doctoc -->

**Goal:** Derive, as theorems over the unchanged seven-equation
axiom set `eraDefs`, the eleven open-term recursion laws for the
derived operations of the minimal-basis ERA in
`GebLean/Era.lean`.

**Architecture:** Append a new section to `GebLean/Era.lean`
after "The Mazzanti operations, derived". Build bottom-up: an
extensionality rule and additive algebra (Phase 0–1), mod
corollaries (Phase 2), the subtraction template plus the laws
not needing exponential domination (Phase 3), then the two
clusters whose entries rest on open obligations (Phase 4a–4b).
Each law is obtained by unfolding the derived operation and
mirroring its `Nat`-level identity proof at the object level,
per spec §5.

**Tech Stack:** Lean 4 (core only, no mathlib), the `Derivable`
equation calculus already in `GebLean/Era.lean`; build with
`lake build` / `lake test`; pre-commit via
`bash scripts/pre-commit.sh`.

---

## Reference documents

- Spec: `docs/superpowers/specs/2026-06-12-era-open-laws-design.md`
  (read §5–§9 before starting; the per-law proof sketches and the
  open-obligation analysis live there).
- `GebLean/Era.lean`: the calculus (`Derivable`, lines 124–149),
  the seven axiom-instance lemmas (`derivable_add_zero` …
  `derivable_exp2_succ`), the per-operation congruences, the
  numeral lemmas, the `0 + x = x` example (lines 440–463), and
  the `Nat`-level identities `sq_identity`, `tsub_identity`,
  `dmul_identity`, `div_identity`, `pow_identity` with their
  `Nat.mod_eq_of_lt` sites.
- [Goo54] R. L. Goodstein, Math. Scand. 2 (1954) 247–261; the
  derivation playbook (schemata K, U₁, E₁–E₃; equations
  (1)–(17)).

## Conventions for every task

- One declaration at a time; the build must be green (no
  `sorry`, no `_`) before the task's commit, except where a task
  explicitly carries a `sorry` between its own steps for a
  `lean4` skill that requires it (removed before commit).
- Verification command for every Lean step: `lake build`
  (authoritative; never `lake env lean`). The commit step runs
  `bash scripts/pre-commit.sh` (`lake test` + `lake lint`).
- Each new `theorem`/`def` carries a `/-- … -/` docstring; cite
  the [Goo54] equation number or the mirrored `Nat`-identity in
  the docstring where applicable (citation rule, `CLAUDE.md`).
- Axiom hygiene: after each law builds, run
  `lean_verify` (or `#print axioms <name>`) and confirm the
  axiom set is contained in `{propext, Quot.sound}`. Record any
  `Classical.choice` leak as a defect to fix before commit
  (every sketch here is `Classical.choice`-free).
- Commit messages: `feat(era): <imperative lowercase subject>`,
  no trailing period, subject under ~72 chars.

## File structure

- Modify: `GebLean/Era.lean` — append all new declarations in a
  new module-docstring section. No new files: the theorems are
  the deliverable, and the file's closed-form completeness story
  (`eraClosedComplete`) already exercises them indirectly. If the
  file's length becomes unwieldy during execution, a split of the
  derived-operations material into
  `GebLean/Era/Mazzanti.lean` may be proposed as a separate
  refactoring branch (one-concern-per-branch rule); do not bundle
  it here.

---

## Phase 0 — infrastructure

### Task 0.1: name the additive flip `0 + x = x`

**Files:**

- Modify: `GebLean/Era.lean` (replace the `example` at lines
  ~440–463 with a named theorem; keep the proof body).

- [ ] **Step 1: promote the example to a theorem.** Replace
  `example : Derivable eraDefs ⟨(.zero : ETm 1) +ᵉ .var 0, …⟩`
  with the parametric form:

```lean
/-- `0 + u = u` (Goodstein 1954 (6)); the additive flip of
`derivable_add_zero`, by `uniq` (the defining equation gives only
`u + 0 = u`). -/
theorem derivable_zero_add {n : Nat} (u : ETm n) :
    Derivable eraDefs ⟨(.zero : ETm n) +ᵉ u, u⟩ := by
  sorry
```

Adapt the existing `example` proof (which proves the `n = 1`,
`u = .var 0` case) to arbitrary `n` and `u` by proving the
`.var 0` case at scope 1 and instantiating with
`Derivable.inst (fun _ => u)`, or by reproducing the `uniq`
directly at scope `n`. The example's three `uniq` premises
(`base`, `stepF`, `stepG`) carry over.

- [ ] **Step 2: build.** Run `lake build`. Expected: green.

- [ ] **Step 3: axiom check.** `#print axioms derivable_zero_add`;
  expected `[propext, Quot.sound]`.

- [ ] **Step 4: commit.**

```bash
bash scripts/pre-commit.sh
jj describe -m "feat(era): name the additive flip 0 + u = u"
```

### Task 0.2: zero/successor extensionality rule (E₃)

**Files:**

- Modify: `GebLean/Era.lean` (add after `Derivable.succ_congr`).

- [ ] **Step 1: state the rule.**

```lean
/-- Zero/successor extensionality (Goodstein 1954 E₃): two
solutions agreeing at `0` and at every successor are equal.
Derived from `uniq` with a step functional that ignores the
previous-value slot. -/
theorem Derivable.ext_succ {B : Type} {ar : B → Nat}
    {defs : Defs B ar} {n : Nat} {F G : Tm B ar (n + 1)}
    (h0 : Derivable defs ⟨F.subst (sub0 .zero), G.subst (sub0 .zero)⟩)
    (hS : Derivable defs ⟨F.subst bump, G.subst bump⟩) :
    Derivable defs ⟨F, G⟩ := by
  sorry
```

- [ ] **Step 2: prove.** Apply `Derivable.uniq` with `H` the
  weakening of `F.subst bump : Tm B ar (n+1)` into
  `Tm B ar (n+2)` by inserting a dummy at variable 1 (the
  previous-value slot). Concretely `H := (F.subst bump).subst σ`
  for the renaming `σ : Fin (n+1) → Tm B ar (n+2)` sending
  variable 0 to variable 0 and variable `i+1` to variable `i+2`
  (skip the prev slot). Then:
  - `uniq` premise 1 is `h0`.
  - `uniq` premise 2 (`F.subst bump = H.subst (recArgs F)`):
    `H.subst (recArgs F)` reduces to `F.subst bump` because `H`
    does not mention variable 1 and `recArgs F` is the identity on
    variables 0 and 2..n+1; close by `Tm.subst_subst` plus a
    `funext`/`Fin` case split, ending in `refl`.
  - `uniq` premise 3 (`G.subst bump = H.subst (recArgs G)`):
    `H.subst (recArgs G) = F.subst bump` by the same reduction;
    the goal becomes `G.subst bump = F.subst bump`, i.e. `hS.symm`.
  Use the `lean4:prove` skill; the substitution-commutation
  bookkeeping mirrors `eadd_subst`/`fcons_eta` patterns already
  in the file.

- [ ] **Step 3: build.** `lake build`. Expected: green.

- [ ] **Step 4: axiom check.** `#print axioms Derivable.ext_succ`;
  expected contained in `{propext, Quot.sound}`.

- [ ] **Step 5: commit.**

```bash
bash scripts/pre-commit.sh
jj describe -m "feat(era): add zero/successor extensionality rule"
```

---

## Phase 1 — additive algebra by `uniq`

Order is fixed by base-availability (spec §6 Phase 1): each
multi-variable law's `uniq` base instance must already be
proven.

### Task 1.1: `succ_add` (Goodstein (7))

**Files:** Modify `GebLean/Era.lean`.

- [ ] **Step 1: state.**

```lean
/-- `S u + v = S (u + v)` (`succ_add`); from Goodstein 1954's
interchange (7) `u + S v = S u + v` and the defining
`u + S v = S (u + v)`. -/
theorem derivable_succ_add {n : Nat} (u v : ETm n) :
    Derivable eraDefs ⟨.succ u +ᵉ v, .succ (u +ᵉ v)⟩ := by
  sorry
```

- [ ] **Step 2: prove** by `uniq` on `v` (recursion variable in
  position 0). Base `v = 0`: `S u + 0 = S u = S (u + 0)` from
  `derivable_add_zero` and `succ_congr`. Step: both sides advance
  by `derivable_add_succ`. Mirror the `example` invocation
  pattern. `lean4:prove`.

- [ ] **Step 3: build + axiom check.** `lake build`;
  `#print axioms derivable_succ_add`.

- [ ] **Step 4: commit.**

```bash
bash scripts/pre-commit.sh
jj describe -m "feat(era): derive succ_add by uniq"
```

### Task 1.2: `add_comm` (Goodstein (8))

**Files:** Modify `GebLean/Era.lean`.

- [ ] **Step 1: state.**

```lean
/-- `u + v = v + u` (Goodstein 1954 (8)). -/
theorem derivable_add_comm {n : Nat} (u v : ETm n) :
    Derivable eraDefs ⟨u +ᵉ v, v +ᵉ u⟩ := by
  sorry
```

- [ ] **Step 2: prove** by `uniq` on `v`. Base `v = 0`:
  `u + 0 = u = 0 + u` from `derivable_add_zero`/`derivable_add_zero`
  (the base instance is `derivable_zero_add`, available from Task
  0.1). Step: `u + S v = S(u + v)` (`derivable_add_succ`) and
  `S v + u = S(v + u)` (`derivable_succ_add`, Task 1.1), reduced
  through the inductive hypothesis. `lean4:prove`.

- [ ] **Step 3: build + axiom check.**

- [ ] **Step 4: commit.**

```bash
bash scripts/pre-commit.sh
jj describe -m "feat(era): derive add_comm by uniq"
```

### Task 1.3: `add_assoc` (Goodstein (10))

**Files:** Modify `GebLean/Era.lean`.

- [ ] **Step 1: state.**

```lean
/-- `(u + v) + w = u + (v + w)` (Goodstein 1954 (10)). -/
theorem derivable_add_assoc {n : Nat} (u v w : ETm n) :
    Derivable eraDefs ⟨(u +ᵉ v) +ᵉ w, u +ᵉ (v +ᵉ w)⟩ := by
  sorry
```

- [ ] **Step 2: prove** by `uniq` on `w` (Goodstein: "with `c`
  as variable, apply U₁"). Base `w = 0`: both sides reduce to
  `u + v` by `derivable_add_zero`. Step: both advance by
  `derivable_add_succ` and `eadd_congr`. `lean4:prove`.

- [ ] **Step 3: build + axiom check.**

- [ ] **Step 4: commit.**

```bash
bash scripts/pre-commit.sh
jj describe -m "feat(era): derive add_assoc by uniq"
```

---

## Phase 2 — mod corollaries

### Task 2.1: `zero_mod`

**Files:** Modify `GebLean/Era.lean`.

- [ ] **Step 1: state.**

```lean
/-- `0 mod v = 0`. -/
theorem derivable_zero_mod {n : Nat} (v : ETm n) :
    Derivable eraDefs ⟨(.zero : ETm n) %ᵉ v, .zero⟩ := by
  sorry
```

- [ ] **Step 2: prove** by `uniq` on `v` with step functional
  `H := .zero` (spec §6 Phase 2). Base `v = 0`: `0 mod 0 = 0`
  from `derivable_mod_zero`. Step: `0 mod (S v) = 0` from
  `axModLt` at `(0, v)` (i.e. `derivable_mod_lt 0 v`, noting
  `0 + S v = S v` via `derivable_zero_add`). `lean4:prove`.

- [ ] **Step 3: build + axiom check.**

- [ ] **Step 4: commit.**

```bash
bash scripts/pre-commit.sh
jj describe -m "feat(era): derive zero_mod by uniq"
```

### Task 2.2: `mod_self`

**Files:** Modify `GebLean/Era.lean`.

- [ ] **Step 1: state.**

```lean
/-- `v mod v = 0`. -/
theorem derivable_mod_self {n : Nat} (v : ETm n) :
    Derivable eraDefs ⟨v %ᵉ v, .zero⟩ := by
  sorry
```

- [ ] **Step 2: prove** without induction (spec §6 Phase 2):
  from `derivable_mod_add` at `(0, v)` — `(0 + v) mod v = 0 mod v`
  — rewrite `0 + v = v` by `derivable_zero_add` under
  `emod_congr`, then chain with `derivable_zero_mod v`.
  `lean4:prove`.

- [ ] **Step 3: build + axiom check.**

- [ ] **Step 4: commit.**

```bash
bash scripts/pre-commit.sh
jj describe -m "feat(era): derive mod_self"
```

---

## Phase 3 — laws not requiring domination

### Task 3.1: `zero_sub` (E₃ split)

**Files:** Modify `GebLean/Era.lean`.

- [ ] **Step 1: state.**

```lean
/-- `0 ∸ w = 0`. -/
theorem derivable_zero_sub {n : Nat} (w : ETm n) :
    Derivable eraDefs ⟨(.zero : ETm n) ∸ᵉ w, .zero⟩ := by
  sorry
```

- [ ] **Step 2: prove** by `Derivable.ext_succ` on `w` (Task
  0.2). Set up `F := (.zero ∸ᵉ .var 0)`, `G := .zero` at scope
  `n+1` and instantiate, or prove the `.var 0` case at scope 1
  and `inst`. Zero case (`w = 0`): unfold `esub`; with
  `P := eexp2 (.zero +ᵉ .zero)`, both remainders close via
  `axAdd0` (`derivable_add_zero`), `mod_self`, `zero_mod`.
  Successor case (`w = .succ x`): inner remainder
  `(P +ᵉ .zero) %ᵉ (P +ᵉ .succ x)` is `derivable_mod_lt` after
  `derivable_add_zero`; outer remainder is `mod_self`. (The
  split is required because `axModLt` matches only a
  successor-shaped addend; spec §6 Phase 3.) `lean4:prove`.

- [ ] **Step 3: build + axiom check.**

- [ ] **Step 4: commit.**

```bash
bash scripts/pre-commit.sh
jj describe -m "feat(era): derive zero_sub by extensionality split"
```

### Task 3.2: `sub_self`

**Files:** Modify `GebLean/Era.lean`.

- [ ] **Step 1: state.**

```lean
/-- `t ∸ t = 0`. -/
theorem derivable_sub_self {n : Nat} (t : ETm n) :
    Derivable eraDefs ⟨t ∸ᵉ t, .zero⟩ := by
  sorry
```

- [ ] **Step 2: prove** by unfolding `esub`: inner remainder is
  `mod_self`, outer is `zero_mod`; no case split, the divisor and
  dividend shapes coincide (spec §6 Phase 3). `lean4:prove`.

- [ ] **Step 3: build + axiom check.**

- [ ] **Step 4: commit.**

```bash
bash scripts/pre-commit.sh
jj describe -m "feat(era): derive sub_self"
```

### Task 3.3: `pred_zero` (deliverable 3 of 11)

**Files:** Modify `GebLean/Era.lean`.

- [ ] **Step 1: state (verbatim from spec §4).**

```lean
/-- `0 ∸ 1 = 0` (predecessor of zero). -/
theorem derivable_pred_zero {n : Nat} :
    Derivable eraDefs ⟨(.zero : ETm n) ∸ᵉ one, .zero⟩ :=
  derivable_zero_sub one
```

- [ ] **Step 2: build + axiom check.** `lake build`;
  `#print axioms derivable_pred_zero`.

- [ ] **Step 3: commit.**

```bash
bash scripts/pre-commit.sh
jj describe -m "feat(era): derive pred_zero from zero_sub"
```

### Task 3.4: `edmul_zero`

**Files:** Modify `GebLean/Era.lean`.

- [ ] **Step 1: state.**

```lean
/-- `edmul t 0 = 0` (the double product `2·t·0`). -/
theorem derivable_edmul_zero {n : Nat} (t : ETm n) :
    Derivable eraDefs ⟨edmul t .zero, .zero⟩ := by
  sorry
```

- [ ] **Step 2: prove** (spec §6 Phase 3): unfold `edmul t 0 =`
  `esq (t +ᵉ 0) ∸ᵉ (esq t +ᵉ esq 0)`. Reduce `esq (t +ᵉ 0)` to
  `esq t` by `esq_congr` on `derivable_add_zero`; reduce `esq 0`
  to `0` (`numeral_sq` at `a = 0`, giving `esq 0 = numeral 0 =`
  `.zero`); reduce `esq t +ᵉ 0` to `esq t` by `derivable_add_zero`.
  The expression becomes `esq t ∸ᵉ esq t`, closed by
  `derivable_sub_self`. `lean4:prove`.

- [ ] **Step 3: build + axiom check.**

- [ ] **Step 4: commit.**

```bash
bash scripts/pre-commit.sh
jj describe -m "feat(era): derive edmul_zero"
```

### Task 3.5: `mul_zero` (deliverable 5 of 11)

**Files:** Modify `GebLean/Era.lean`.

- [ ] **Step 1: state (verbatim from spec §4).**

```lean
/-- `u * 0 = 0`. -/
theorem derivable_mul_zero {n : Nat} (u : ETm n) :
    Derivable eraDefs ⟨u *ᵉ .zero, .zero⟩ := by
  sorry
```

- [ ] **Step 2: prove** (spec §6 Phase 3): unfold
  `u *ᵉ 0 = edmul u 0 /ᵉ numeral 2`. Rewrite `edmul u 0` to `0`
  by `derivable_edmul_zero` under `ediv_congr`, giving
  `.zero /ᵉ numeral 2`. Close by `numeral_div 0 2`: its statement
  `(numeral 0) /ᵉ (numeral 2) = numeral (0 / 2)` is
  `.zero /ᵉ numeral 2 = .zero` after `numeral 0 = .zero` (defeq)
  and `0 / 2 = 0`. This route uses only the existing numeral
  lemma, with no forward dependence on `zero_div` (Task 3.7).
  `lean4:prove`.

- [ ] **Step 3: build + axiom check.**

- [ ] **Step 4: commit.**

```bash
bash scripts/pre-commit.sh
jj describe -m "feat(era): derive mul_zero"
```

### Task 3.6: `div_zero` (deliverable 9 of 11)

**Files:** Modify `GebLean/Era.lean`.

- [ ] **Step 1: state (verbatim from spec §4).**

```lean
/-- `u / 0 = 0`. -/
theorem derivable_div_zero {n : Nat} (u : ETm n) :
    Derivable eraDefs ⟨u /ᵉ .zero, .zero⟩ := by
  sorry
```

- [ ] **Step 2: prove** (spec §6 Phase 3). Unfold
  `u /ᵉ 0 = edmul (S u) (u ∸ᵉ (u %ᵉ 0)) %ᵉ (edmul (S u) 0 ∸ᵉ one)`.
  Reduce `u %ᵉ 0` to `u` by `derivable_mod_zero` (`axMod0`); then
  `u ∸ᵉ u` to `0` by `derivable_sub_self`; then
  `edmul (S u) 0` to `0` by `derivable_edmul_zero`; the divisor
  becomes `0 ∸ᵉ one`, reduced to `0` by `derivable_pred_zero`
  (`zero_sub`); the dividend `edmul (S u) 0` to `0` by
  `derivable_edmul_zero`. Goal becomes `0 %ᵉ 0 = 0` by
  `derivable_mod_zero` (`axMod0`). `lean4:prove`.

- [ ] **Step 3: build + axiom check.**

- [ ] **Step 4: commit.**

```bash
bash scripts/pre-commit.sh
jj describe -m "feat(era): derive div_zero"
```

### Task 3.7: `zero_div` (deliverable 10 of 11)

**Files:** Modify `GebLean/Era.lean`.

- [ ] **Step 1: state (verbatim from spec §4).**

```lean
/-- `0 / S u = 0`. -/
theorem derivable_zero_div {n : Nat} (u : ETm n) :
    Derivable eraDefs ⟨(.zero : ETm n) /ᵉ .succ u, .zero⟩ := by
  sorry
```

- [ ] **Step 2: prove** (spec §6 Phase 3, repaired sketch).
  Unfold `0 /ᵉ S u =`
  `edmul (S 0) (0 ∸ᵉ (0 %ᵉ S u)) %ᵉ (edmul (S 0) (S u) ∸ᵉ one)`.
  Rewrite `0 %ᵉ S u` to `0` by `derivable_zero_mod` under
  `esub_congr`, so the dividend's subtraction is `0 ∸ᵉ 0`, closed
  by `derivable_sub_self` (the `w = 0` case); the dividend's
  `edmul (S 0) 0` then reduces by `derivable_edmul_zero` (or
  `numeral_dmul`) to `.zero`. The modulus stays open in `u`;
  close the outer remainder by `derivable_zero_mod` under
  `emod_congr`. `lean4:prove`.

- [ ] **Step 3: build + axiom check.**

- [ ] **Step 4: commit.**

```bash
bash scripts/pre-commit.sh
jj describe -m "feat(era): derive zero_div"
```

### Task 3.8: Phase 3 checkpoint

- [ ] **Step 1:** Confirm the four Phase-0-to-3 deliverables of
  the eleven (`pred_zero`, `mul_zero`, `div_zero`, `zero_div`)
  build and pass axiom check. Run `bash scripts/pre-commit.sh`.
- [ ] **Step 2:** Use `lean4:checkpoint` to record progress. This
  is the boundary of the unconditional acceptance tier (spec §9).

---

## Phase 4a — the subtraction cluster

The subtraction template and the laws below depend on the
exponential-domination family (spec §7.3), which has **no
verified derivation at spec time**. Tasks 4a.1–4a.2 build the
template (closed obligations). Task 4a.3 is the first open
obligation: it carries the staged-exit protocol.

### Task 4a.1: the `esubAt` template definition

**Files:** Modify `GebLean/Era.lean`.

- [ ] **Step 1: define.**

```lean
/-- Exponent-parametric truncated subtraction: the `esub`
unfolding with the exponent `e` exposed as a separate argument,
so that `s ∸ᵉ t = esubAt (s +ᵉ t) s t` definitionally. -/
def esubAt {n : Nat} (e s t : ETm n) : ETm n :=
  ((eexp2 e +ᵉ s) %ᵉ (eexp2 e +ᵉ t)) %ᵉ (eexp2 e +ᵉ s)
```

- [ ] **Step 2: definitional-agreement lemma.**

```lean
/-- `esub` is `esubAt` at the canonical exponent. -/
theorem esub_eq_esubAt {n : Nat} (s t : ETm n) :
    s ∸ᵉ t = esubAt (s +ᵉ t) s t := rfl
```

- [ ] **Step 3: build.** `lake build`. Expected: green (both by
  `rfl`/unfolding).

- [ ] **Step 4: commit.**

```bash
bash scripts/pre-commit.sh
jj describe -m "feat(era): add exponent-parametric esubAt template"
```

### Task 4a.2: the two shape-decided template laws

**Files:** Modify `GebLean/Era.lean`.

- [ ] **Step 1: state `esubAt_of_lt`** (no domination
  hypothesis; spec §7.2).

```lean
/-- `esubAt e u v = 0` when `v` dominates `u` by a successor. -/
theorem derivable_esubAt_of_lt {n : Nat} {e u v d : ETm n}
    (hlt : Derivable eraDefs ⟨v, u +ᵉ .succ d⟩) :
    Derivable eraDefs ⟨esubAt e u v, .zero⟩ := by
  sorry
```

  Prove: inner divisor `eexp2 e +ᵉ v = (eexp2 e +ᵉ u) +ᵉ .succ d`
  by additive algebra from `hlt`, so `derivable_mod_lt` gives the
  inner remainder `eexp2 e +ᵉ u`; the outer is
  `derivable_mod_self`.

- [ ] **Step 2: state `esubAt_of_add`** (one domination
  hypothesis; spec §7.2).

```lean
/-- `esubAt e u v = w` when `u = w + v` and `2^e` dominates `u`
by a successor. -/
theorem derivable_esubAt_of_add {n : Nat} {e u v w p : ETm n}
    (hsum : Derivable eraDefs ⟨u, w +ᵉ v⟩)
    (hdom : Derivable eraDefs ⟨eexp2 e, u +ᵉ .succ p⟩) :
    Derivable eraDefs ⟨esubAt e u v, w⟩ := by
  sorry
```

  Prove (spec §7.2): inner remainder — rewrite
  `eexp2 e +ᵉ u = w +ᵉ (eexp2 e +ᵉ v)` (additive algebra +
  `hsum`), apply `derivable_mod_add`, leaving
  `w %ᵉ (eexp2 e +ᵉ v)`; then `derivable_mod_lt` after exhibiting
  `eexp2 e +ᵉ v = w +ᵉ .succ (v +ᵉ v +ᵉ p)` from `hdom`/`hsum` by
  additive algebra. Outer remainder — `derivable_mod_lt` after
  exhibiting `eexp2 e +ᵉ u = w +ᵉ .succ (v +ᵉ p +ᵉ w +ᵉ v)`
  likewise. Use `derivable_add_comm`/`add_assoc`/`succ_add` for
  the rearrangements; `lean4:prove`.

- [ ] **Step 3: build + axiom check** for both.

- [ ] **Step 4: commit.**

```bash
bash scripts/pre-commit.sh
jj describe -m "feat(era): add shape-decided esubAt template laws"
```

### Task 4a.3: the exponential-domination family (OPEN obligation)

**Files:** Modify `GebLean/Era.lean`.

This task has no verified derivation (spec §7.3, §8). Attempt it;
if blocked, follow the staged-exit protocol (spec §9) — do not
extend `eraDefs`.

- [ ] **Step 1: state the summand-family member** to attempt
  first (the minimal instance the Phase-4a reductions consume):

```lean
/-- Domination: `2^(S u) = u + S t` for an explicit witness `t`
(true since `u + 1 ≤ 2^(u+1)`). -/
theorem derivable_exp2_succ_dominates {n : Nat} (u : ETm n) :
    ∃ t : ETm n, Derivable eraDefs ⟨eexp2 (.succ u), u +ᵉ .succ t⟩ := by
  sorry
```

  (The witness shape and whether the statement should fix `t`
  explicitly rather than existentially are part of the
  obligation; spec §7.3 records the candidate
  `t := eexp2 (.succ u') %ᵉ (eexp2 u' +ᵉ .succ u')` route and its
  unverified status.)

- [ ] **Step 2: attempt** via the `lean4:autoprove` /
  `lean4:sorry-filler-deep` skills against the §7.3 candidate
  approach and the §8 rejected list (do not retry the three
  rejected routes). Budget the attempt; if no progress, proceed
  to Step 3.

- [ ] **Step 3 (impasse branch): staged exit.** If domination
  resists, stop here. Commit the completed Phases 0–3 and the
  template (Tasks 4a.1–4a.2) as the partial result, and write a
  stuck-and-ask report (`lean-coding.md` template) documenting:
  what was attempted, which §8 routes were excluded, and the
  precise object-level obligation that blocks. Update the spec's
  §9 status note and the handoff. Do **not** mark Task 853
  complete; mark this plan's Phase 4 blocked pending the
  obligation.

- [ ] **Step 4 (success branch): build + axiom check + commit.**

```bash
bash scripts/pre-commit.sh
jj describe -m "feat(era): derive exponential domination family"
```

### Task 4a.4: `sub_zero` (deliverable 1 of 11; verified reduction)

Depends on Task 4a.3 (domination). Spec §7.4: verified reduction
**given** domination.

**Files:** Modify `GebLean/Era.lean`.

- [ ] **Step 1: state (verbatim from spec §4).**

```lean
/-- `u ∸ 0 = u`. -/
theorem derivable_sub_zero {n : Nat} (u : ETm n) :
    Derivable eraDefs ⟨u ∸ᵉ .zero, u⟩ := by
  sorry
```

- [ ] **Step 2: prove** (spec §7.4) as the `esubAt_of_add`
  instance at `e := u +ᵉ .zero`, `v := .zero`, `w := u`:
  `hsum` is `derivable_add_zero u` (symm), `hdom` from the
  domination instance at `e := u +ᵉ 0`, `a := u`. Then
  `esub_eq_esubAt` bridges `u ∸ᵉ 0` to `esubAt (u +ᵉ 0) u 0`.
  `lean4:prove`.

- [ ] **Step 3: build + axiom check.**

- [ ] **Step 4: commit.**

```bash
bash scripts/pre-commit.sh
jj describe -m "feat(era): derive sub_zero from esubAt template"
```

### Task 4a.5: `pred_succ` (deliverable 4 of 11; verified reduction)

Depends on Task 4a.3. Spec §7.4: verified reduction.

**Files:** Modify `GebLean/Era.lean`.

- [ ] **Step 1: state (verbatim from spec §4).**

```lean
/-- `S u ∸ 1 = u`. -/
theorem derivable_pred_succ {n : Nat} (u : ETm n) :
    Derivable eraDefs ⟨.succ u ∸ᵉ one, u⟩ := by
  sorry
```

- [ ] **Step 2: prove** (spec §7.4): `S u ∸ᵉ one =`
  `esubAt (S u +ᵉ one) (S u) one`; `esubAt_of_add` at `w := u`,
  `v := one`, with `hsum : S u = u +ᵉ one` (additive algebra:
  `S u = u + 1` via `derivable_add_succ`/`add_zero`) and `hdom`
  the domination instance at `e := S u +ᵉ one`, `a := u`.
  `lean4:prove`.

- [ ] **Step 3: build + axiom check.**

- [ ] **Step 4: commit.**

```bash
bash scripts/pre-commit.sh
jj describe -m "feat(era): derive pred_succ from esubAt template"
```

### Task 4a.6: subtraction cluster entry — (1)/(2)/`sub_succ` (OPEN)

**Files:** Modify `GebLean/Era.lean`.

Spec §7.4: {(1) `(a∸b)∸1 = (a∸1)∸b`, (2) `Sa∸Sb = a∸b`,
`sub_succ`} are mutually derivable but no member has a verified
derivation from the template alone. Attempt in the §7.4 order;
staged-exit protocol applies.

- [ ] **Step 1: attempt route (i)** — derive (2)
  `Sa ∸ Sb = a ∸ b` at the `esubAt` level by `Derivable.ext_succ`
  on one variable with the other as parameter, using the template
  laws to evaluate both sides at `0` and at successors. State:

```lean
/-- Goodstein 1954 (2): `S u ∸ S v = u ∸ v`. -/
theorem derivable_sub_succ_succ {n : Nat} (u v : ETm n) :
    Derivable eraDefs ⟨.succ u ∸ᵉ .succ v, u ∸ᵉ v⟩ := by
  sorry
```

- [ ] **Step 2: attempt route (ii)** if (i) stalls — an
  exponent-stability lemma
  `esubAt e u v = esubAt e' u v` given domination of both
  exponents, to let inductions fix one exponent.

- [ ] **Step 3: attempt route (iii)** if (i)–(ii) stall —
  transpose Goodstein's two-variable induction I₂ ([Goo54]
  p. 253); costly (consumes (13), (16), (17)).

- [ ] **Step 4: derive `sub_succ`** (deliverable 2 of 11) once a
  cluster member lands. Statement (verbatim from spec §4):

```lean
/-- `u ∸ S v = (u ∸ v) ∸ 1`. -/
theorem derivable_sub_succ {n : Nat} (u v : ETm n) :
    Derivable eraDefs ⟨u ∸ᵉ .succ v, (u ∸ᵉ v) ∸ᵉ one⟩ := by
  sorry
```

  Route: `sub_succ` from (1)+(2) by `uniq` on `u` with a
  parameter-using step functional ignoring the previous-value
  slot (spec §7.4: F-premise by (2), G-premise by (1) plus
  `pred_succ`).

- [ ] **Step 5 (impasse branch): staged exit** as in Task 4a.3
  Step 3.

- [ ] **Step 6 (success branch): build + axiom check + commit**
  each landed member separately.

```bash
bash scripts/pre-commit.sh
jj describe -m "feat(era): derive sub_succ via cluster entry"
```

---

## Phase 4b — the multiplicative cluster

Reachable only after Phase 4a. Cluster entry is open (spec §7.5):
`mul_succ`, mod-of-multiple, and the squaring law are mutually
dependent; one must be entered from the template and domination
layers. Staged-exit protocol applies throughout.

### Task 4b.1: multiplicative cluster entry (OPEN)

**Files:** Modify `GebLean/Era.lean`.

- [ ] **Step 1: attempt the candidate route** (spec §7.5):
  derive the `edmul` successor recursion first —

```lean
/-- `edmul u (S v) = edmul u v + u + u` (the double product
`2u(Sv) = 2uv + 2u`). -/
theorem derivable_edmul_succ {n : Nat} (u v : ETm n) :
    Derivable eraDefs
      ⟨edmul u (.succ v), edmul u v +ᵉ u +ᵉ u⟩ := by
  sorry
```

  then `mul_succ` (deliverable 6 of 11) from it via the `emul`
  unfolding (`emul s t = edmul s t /ᵉ numeral 2`) and the
  division/numeral machinery. Statement (verbatim from spec §4):

```lean
/-- `u * S v = u * v + u`. -/
theorem derivable_mul_succ {n : Nat} (u v : ETm n) :
    Derivable eraDefs ⟨u *ᵉ .succ v, (u *ᵉ v) +ᵉ u⟩ := by
  sorry
```

- [ ] **Step 2: derive mod-of-multiple** (spec §7.5) once
  `mul_succ` lands:

```lean
/-- `(m * k + r) mod m = r mod m` (object-level `Nat.mul_add_mod`,
multiplier second). -/
theorem derivable_mul_add_mod {n : Nat} (m k r : ETm n) :
    Derivable eraDefs ⟨(m *ᵉ k +ᵉ r) %ᵉ m, r %ᵉ m⟩ := by
  sorry
```

  by `uniq` on `k`: base `mul_zero` and `zero_add`; step
  `mul_succ`, `axModAdd`, and additive algebra.

- [ ] **Step 3 (impasse branch): staged exit** as in Task 4a.3
  Step 3 — record which entry member blocked.

- [ ] **Step 4 (success branch): build + axiom check + commit**
  each landed member.

```bash
bash scripts/pre-commit.sh
jj describe -m "feat(era): derive mul_succ and mod-of-multiple"
```

### Task 4b.2: multiplicative algebra as needed

**Files:** Modify `GebLean/Era.lean`.

- [ ] **Step 1:** Derive only the multiplicative laws the
  remaining deliverables consume, in Goodstein's order
  ([Goo54] p. 250): (11) `S u * v = u * v + v` (`uniq`, from
  `mul_zero`/`mul_succ`/(8)/(10)), then (14) `u * v = v * u`,
  (15) `u * (v + w) = u * v + u * w`, (15.1)
  `u * (v * w) = (u * v) * w` as required by Tasks 4b.3–4b.4.
  Defer any law not actually consumed (YAGNI). State each with a
  `/-- … (Goodstein 1954 (N)) -/` docstring; prove by `uniq`
  mirroring the cited derivation.

- [ ] **Step 2: build + axiom check + commit** per law.

```bash
bash scripts/pre-commit.sh
jj describe -m "feat(era): derive multiplicative algebra laws"
```

### Task 4b.3: `pow_zero` (deliverable 7 of 11; verified reduction)

**Files:** Modify `GebLean/Era.lean`.

Depends on Task 4a.3 (domination) and Tasks 4b.1–4b.2
(`mul_zero` is already from Phase 3; `esubAt_of_add` from
Task 4a.2). Spec §7.6: verified reduction (no `pow_mod_rep`
needed), given domination.

- [ ] **Step 1: state (verbatim from spec §4).**

```lean
/-- `u ^ 0 = 1`. -/
theorem derivable_pow_zero {n : Nat} (u : ETm n) :
    Derivable eraDefs ⟨u ^ᵉ .zero, one⟩ := by
  sorry
```

- [ ] **Step 2: prove** (spec §7.6): unfold
  `u ^ᵉ 0 = eexp2 ((u *ᵉ 0 +ᵉ u +ᵉ one) *ᵉ 0) %ᵉ`
  `(eexp2 (u *ᵉ 0 +ᵉ u +ᵉ one) ∸ᵉ u)`. The dividend's outer
  `*ᵉ 0` reduces by `mul_zero` to `0`, then `eexp2 0 = one`
  (`derivable_exp2_zero`). The inner exponent reduces by
  `mul_zero`/`zero_add` to `u +ᵉ one`; the modulus is
  `2^(u+1) ∸ᵉ u`, converted by `esubAt_of_add` from the
  domination instance `2^(u+1) = u +ᵉ .succ (.succ t)`; then
  `1 %ᵉ (modulus) = 1` by `derivable_mod_lt`. `lean4:prove`.

- [ ] **Step 3: build + axiom check.**

- [ ] **Step 4: commit.**

```bash
bash scripts/pre-commit.sh
jj describe -m "feat(era): derive pow_zero from domination"
```

### Task 4b.4: `pow_succ` and `div_succ` (deliverables 8, 11 of 11; OPEN depth)

**Files:** Modify `GebLean/Era.lean`.

Spec §7.6: deepest targets; route sketched only. Staged-exit
protocol applies.

- [ ] **Step 1: transpose `pow_mod_rep`** (spec §7.6): introduce
  the witness as an explicit term, derive its recursion equation
  by `uniq`, and the mod-peeling by `derivable_mul_add_mod`
  (Task 4b.1).

- [ ] **Step 2: derive `pow_succ`** (deliverable 8 of 11).
  Statement (verbatim from spec §4):

```lean
/-- `u ^ S v = u ^ v * u`. -/
theorem derivable_pow_succ {n : Nat} (u v : ETm n) :
    Derivable eraDefs ⟨u ^ᵉ .succ v, (u ^ᵉ v) *ᵉ u⟩ := by
  sorry
```

  by mirroring `pow_identity` through the transposed
  `pow_mod_rep`, multiplicative algebra, and
  `derivable_mul_add_mod`.

- [ ] **Step 3: derive `div_succ`** (deliverable 11 of 11).
  Statement (verbatim from spec §4):

```lean
/-- `S u / S v = (u / S v) + (1 ∸ (v ∸ (u ∸ S v * (u / S v)))).` -/
theorem derivable_div_succ {n : Nat} (u v : ETm n) :
    Derivable eraDefs ⟨.succ u /ᵉ .succ v,
      (u /ᵉ .succ v) +ᵉ
        (one ∸ᵉ (v ∸ᵉ (u ∸ᵉ .succ v *ᵉ (u /ᵉ .succ v))))⟩ := by
  sorry
```

  by mirroring `div_identity` (multiplicative algebra +
  `derivable_mul_add_mod`).

- [ ] **Step 4 (impasse branch): staged exit** as in Task 4a.3
  Step 3.

- [ ] **Step 5 (success branch): build + axiom check + commit**
  each law.

```bash
bash scripts/pre-commit.sh
jj describe -m "feat(era): derive pow_succ and div_succ"
```

---

## Final verification

### Task F.1: full-suite green and axiom audit

- [ ] **Step 1:** `bash scripts/pre-commit.sh` (full `lake test`
  and `lake lint`).
- [ ] **Step 2:** `bash scripts/check-axioms.sh` (or
  `#print axioms` on each of the eleven deliverables); confirm
  every new theorem's axioms are contained in
  `{propext, Quot.sound}` and none is `sorryAx`.
- [ ] **Step 3:** Confirm no `sorry`, no `admit`, no `_`
  placeholder remains: `grep -nE '\bsorry\b|\badmit\b' GebLean/Era.lean`
  expects no match.
- [ ] **Step 4:** Confirm `eraDefs` is byte-for-byte unchanged
  from `ed0b6752` (`git diff ed0b6752 -- GebLean/Era.lean` shows
  only additions after the Mazzanti section and the Task 0.1
  example-to-theorem edit; the `eraDefs` definition is
  untouched).

### Task F.2: optional cleanup (spec §9)

- [ ] **Step 1:** If Phase 4 completed, re-derive
  `numeral_sub`/`numeral_mul`/`numeral_div`/`numeral_pow` as
  corollaries of the open laws (replacing the `Nat`-identity
  routes), if it reduces total proof size. Skip if it does not
  (code-is-cost). Separate commit.

### Task F.3: documentation and handoff

- [ ] **Step 1:** Update the module docstring's
  `## Main statements` to list the eleven open laws (and note any
  left blocked by the staged exit, with the obligation
  referenced).
- [ ] **Step 2:** Update `project_era_substitution_basis.md`
  memory: the open-laws are now theorems (or: blocked at
  obligation X), superseding the "NOT ported" note.
- [ ] **Step 3:** Push only after user line-by-line review
  (`CLAUDE.md` hard rule); do not `jj git push` autonomously.

## Self-review notes

- **Spec coverage:** every §4 deliverable maps to a task —
  `sub_zero` (4a.4), `sub_succ` (4a.6), `pred_zero` (3.3),
  `pred_succ` (4a.5), `mul_zero` (3.5), `mul_succ` (4b.1),
  `pow_zero` (4b.3), `pow_succ` (4b.4), `div_zero` (3.6),
  `zero_div` (3.7), `div_succ` (4b.4). Supporting §6–§7 lemmas
  (E₃, additive/mult. algebra, mod corollaries, `esubAt`
  template, domination) each have a task.
- **Open obligations** (spec §7.3 domination, §7.4 subtraction
  entry, §7.5 multiplicative entry) are isolated in Tasks 4a.3,
  4a.6, 4b.1, each with the staged-exit protocol of spec §9;
  Phases 0–3 (Tasks 0.1–3.8) are unconditional and deliver four
  of the eleven laws.
- **Dependency order** matches spec §6: 0 → 1 → 2 → 3 → 4a → 4b;
  within Phase 3, `mul_zero` (3.5) routes through `numeral_div`
  rather than the later `zero_div` (3.7) to avoid a forward
  dependence.
