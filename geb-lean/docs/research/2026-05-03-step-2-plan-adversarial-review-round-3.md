# Adversarial review (round 3) of the step-2 plan and spec
<!-- ER-side simultaneous bounded recursion -->

> Reviewer's stance: fresh round-3 reading of
> `docs/superpowers/plans/2026-05-03-step-2-er-simultaneous-bounded-rec.md`
> and
> `docs/superpowers/specs/2026-05-03-step-2-er-simultaneous-bounded-rec-design.md`
> at the post-round-2-fixes revision (commit `bb75dc41`).
> No shared context with rounds 1 or 2.  Source materials read
> end-to-end: the plan and spec under review; rounds 1 and 2
> reviews; master design §3.2 and §15.13; CLAUDE.md; step-1's
> round-3 review for stylistic anchoring; the existing
> infrastructure
> (`GebLean/Utilities/ERArith.lean`,
> `GebLean/Utilities/Tupling.lean`,
> `GebLean/Utilities/ERTupling.lean`,
> `GebLean/Utilities/KSimSzudzikSimrec.lean`,
> `GebLean/LawvereERPolynomialBound.lean`,
> `GebLeanTests/Utilities/ERArith.lean`,
> mathlib `Fin.Tuple.Basic`).  By round 3 the threshold for
> finding defects is high; this pass verifies the round-2 fix
> set against the present text and looks for what slipped
> through the prior rounds and for any second-order defects
> introduced by the round-2 edits themselves.

## Overall assessment

Every round-2 fix verifies as held in the present text.  The
load-bearing chains — the `rw`-based application of
`ERMor1.boundedRec_eq_natRec_of_bounded` with three
explicit-`?_` placeholder goals dispatched in order; the
top-level extraction of `Nat_rec_packed_eq_tuplePack_simRecVec`
serving both the dominance discharge and the main equality;
the `simp only`-with-explicit-lists style throughout Task 14;
the spec's revised statement of
`packedStep_interp_eq_tuplePack_step` using the real `h`
parameter; the `Fin.append_left` / `Fin.append_right` /
`Fin.cons_zero` / `Fin.cons_succ` simp set in
`interp_packedStepCtx` — close on independent walkthrough
against the existing
`ERMor1.boundedRec_eq_natRec_of_bounded` API
(`GebLean/Utilities/ERArith.lean:2193-2213`) and the
existing `rw`-pattern usage at
`GebLeanTests/Utilities/ERArith.lean:71`.

Citations now lead with §0.1.0.34 (the proof technique) and
cite §0.1.0.35 only as the higher-level corollary for `n ≥ 2`.
Spot checks on five docstrings (Nat.simRecVec definition,
tuplePackedBound, simultaneousBoundedRec, the named lemmas
group, ofSimultaneousBoundedRec) confirm uniform citation
shape.

Banned-word grep clean on both files.  Bare `simp [...]`
occurrences appear only in the discipline-reminder section
itself (plan line 103, where the rule itself is being
quoted).  Line-length: 4 lines exceed 80 characters in the
plan (lines 1038, 1606, 2207, 3081), each at 83–87 chars,
within the round-2 review's "unavoidable" exception band.
The spec has 0 lines over 80.

Below: numbered findings.  V1–V8 are round-2-fix
verifications.  F1–F5 are new findings from this pass.

---

## V1 — E1 (`apply` vs `rw` for `boundedRec_eq_natRec_of_bounded`) — fixed

**Claim under challenge.** Round 2 reported (E1) that
Task 14.3's `apply boundedRec_eq_natRec_of_bounded` could not
unify the lemma's RHS (`Nat.rec ...`) against the goal's RHS
(`Nat.tuplePack k (Nat.simRecVec ... n x)`).  The fix
recommended extracting `Nat_rec_packed_eq_tuplePack_simRecVec`
to a top-level lemma and using `rw` with `?_` placeholders.

**Finding.** Plan Task 14.3 (lines 1531–1563) now defines
`Nat_rec_packed_eq_tuplePack_simRecVec` as a top-level
theorem with two cases (`zero` via
`packedBase_interp_eq_tuplePack_simRecVec_zero` and `succ`
via `simp only [ih]` then
`packedStep_interp_eq_tuplePack_step`).  Spec §5.3 lists it
in the public surface (line 148) and provides its full
statement (lines 544–555).

Task 14.4's `packedRec_eq_tuplePack_simRecVec` (lines 1611–
1628) now uses the corrected idiom:

```lean
rw [ERMor1.boundedRec_eq_natRec_of_bounded
      (ERMor1.packedBase k a h)
      (ERMor1.packedStep k a g)
      (ERMor1.tuplePackedBound k componentBound)
      n x ?_ ?_]
· exact ERMor1.Nat_rec_packed_eq_tuplePack_simRecVec
    k a h g n x
· -- dominance discharge
  intro j h_j_le_n
  rw [ERMor1.Nat_rec_packed_eq_tuplePack_simRecVec
        k a h g j x]
  exact ERMor1.packedBound_dominates_iter
    k a h g componentBound n x j h_j_le_n h_dominates
· exact ERMor1.packedBound_mono
    k a componentBound n x h_mono
```

This idiom is verified to work with
`boundedRec_eq_natRec_of_bounded` by direct precedent at
`GebLeanTests/Utilities/ERArith.lean:71`
(`rw [ERMor1.boundedRec_eq_natRec_of_bounded]` followed by
three bullets discharging the equation, the dominance
hypothesis, and the monotonicity hypothesis in the order the
lemma's signature presents them).

The hypothesis-discharge bullet is structured correctly:
`intro j h_j_le_n` exposes a `Nat.rec ... ≤ ...` goal; the
`rw` with the unconditional
`Nat_rec_packed_eq_tuplePack_simRecVec` rewrites the LHS to
`Nat.tuplePack k (Nat.simRecVec ... j x)`; then
`packedBound_dominates_iter` closes against
`(tuplePackedBound k componentBound).interp (Fin.cons j x)`.
The shapes line up exactly with the lemma signatures in
spec §5.3.

**Severity.** Clean.

---

## V2 — E2 (bare `simp [...]` in Task 14.1) — fixed

**Claim under challenge.** Round 2 reported (E2) three bare
`simp [...]` calls in Task 14.1's `interp_packedStepCtx`
proof.

**Finding.** Plan Task 14.1 (lines 1430, 1437, 1445) now
reads:

- Line 1430: `simp only [ERMor1.packedStepCtx,
  ERMor1.interp_proj, Fin.append_left, Fin.cons_zero]`.
- Line 1437: `simp only [ERMor1.packedStepCtx, h_param,
  ERMor1.interp_proj, Fin.append_left, Fin.cons_succ]`.
- Line 1445: `simp only [ERMor1.packedStepCtx, h_param,
  ERMor1.interp_comp, ERMor1.interp_tupleAt,
  ERMor1.interp_proj, Fin.append_right, Fin.cons_zero]`.

All three now use `simp only` with explicit lemma lists.
The promoted lemma names (`Fin.append_left`,
`Fin.append_right`, `Fin.cons_zero`, `Fin.cons_succ`) are
verified to exist in mathlib's `Mathlib.Data.Fin.Tuple.Basic`
(grep confirms uses at lines 363–367 and 647–650 of that
file with the canonical signatures).

A single bare `simp [...]` literal still appears in the
plan, but only at line 103 in the
discipline-reminder section itself, where the rule is being
quoted ("Use `simp only [...]` not bare `simp [...]`.").

**Severity.** Clean.

---

## V3 — E4 (spec §5.3 step-lemma incorrect statement) — fixed

**Claim under challenge.** Round 2 reported (E4) that spec
§5.3's `packedStep_interp_eq_tuplePack_step` used a
`fun y => 0` zero-base substitution that misled the
docstring "bases unused at step".

**Finding.** Spec §5.3 (lines 519–533) now reads:

```lean
theorem packedStep_interp_eq_tuplePack_step
    (k a : ℕ)
    (h : Fin (k + 1) → ERMor1 a)
    (g : Fin (k + 1) → ERMor1 (a + 1 + (k + 1)))
    (n : ℕ) (x : Fin a → ℕ) :
    (ERMor1.packedStep k a g).interp
        (Fin.cons n
          (Fin.cons
            (Nat.tuplePack k
              (Nat.simRecVec k a (fun j' => (h j').interp)
                (fun j' => (g j').interp) n x))
            x))
      = Nat.tuplePack k
          (Nat.simRecVec k a (fun j' => (h j').interp)
            (fun j' => (g j').interp) (n + 1) x)
```

The `h` parameter is now passed through to both `simRecVec`
calls (LHS at `n`, RHS at `n + 1`).  The misleading
"bases unused at step" comment is gone.  The supporting
docstring at lines 510–518 now says "Although `packedStep`
itself does not depend on `h`, the lemma's statement does
… The dependency on `h` is mathematically real."  Spec and
plan are now consistent — plan Task 14.2 (lines 1468–1481)
uses the same statement with a `let prev_packed := …`
binding for the inner pack expression, which is
mathematically equivalent to the spec's inlined form.

**Severity.** Clean.

---

## V4 — E3 (`Nat.zero_eq` in zero-case `simp` set) — fixed

**Claim under challenge.** Round 2 flagged (E3) that
`Nat.zero_eq` is not a current mathlib lemma name, so the
zero-case `simp only [Nat.rec, Nat.zero_eq]` in
Task 14.3 would error.

**Finding.** Plan Task 14.3 zero case (lines 1544–1552) now
reads:

```lean
| zero =>
    -- The zero case of `Nat.rec` reduces definitionally
    -- to the base value.  The base value
    -- `(packedBase k a h).interp x` equals
    -- `Nat.tuplePack k (simRecVec ... 0 x)` by the
    -- packedBase lemma.
    exact
      ERMor1.packedBase_interp_eq_tuplePack_simRecVec_zero
        k a h g x
```

`Nat.zero_eq` is gone.  The zero case relies on iota-
reduction of `Nat.rec base step 0 ≡ base`, which is
definitional in Lean 4's kernel; `exact` directly closes
without needing a `simp` step.

**Severity.** Clean.

---

## V5 — E5 (`rw [Nat.rec, ih]` non-standard form) — fixed

**Claim under challenge.** Round 2 flagged (E5) that
`rw [Nat.rec, ih]` is non-standard: `Nat.rec` is a
recursor, not a rewrite-form equation.

**Finding.** Plan Task 14.3 succ case (lines 1553–1563) now
reads:

```lean
| succ m ih =>
    -- The succ case of `Nat.rec` reduces definitionally
    -- to `step m (Nat.rec ... m)`.  Substitute the
    -- inductive hypothesis to expose the
    -- `tuplePack k (simRecVec ... m x)` form, then
    -- close via `packedStep_interp_eq_tuplePack_step`.
    simp only [ih]
    exact
      ERMor1.packedStep_interp_eq_tuplePack_step
        k a h g m x
```

`rw [Nat.rec, ih]` is replaced with `simp only [ih]`.  In
Lean 4, `simp only` performs iota-reduction as part of its
normalization closure, so `Nat.rec base step (m + 1)` is
iota-reduced to `step m (Nat.rec base step m)`, exposing
`Nat.rec base step m` as a subterm matchable by `ih`.

The plan additionally provides a fallback parenthetical
(lines 1565–1569) describing the alternative `change` plus
`rw [ih]` form if `simp only [ih]` does not fire.

**Severity.** Clean.  (See F1 below for a related concern.)

---

## V6 — E6 (`Nat.simRecVec_succ` missing in Task 14.2 simp set) — fixed

**Claim under challenge.** Round 2 flagged (E6) that
Task 14.2's initial `simp only` set omitted
`Nat.simRecVec_succ`, leaving the RHS un-reduced.

**Finding.** Plan Task 14.2 (lines 1483–1485) now reads:

```lean
simp only [ERMor1.packedStep, ERMor1.interp_comp,
  ERMor1.interp_tuplePack, Nat.simRecVec_succ]
```

`Nat.simRecVec_succ` is now in the set, so the RHS reduces
to `g_all j (Fin.append (Fin.cons n x) (simRecVec ... n x))`
shape ahead of the `congr 1; funext j` chain.

**Severity.** Clean.

---

## V7 — Citation discipline — uniformly leads with §0.1.0.34

**Claim under challenge.** The round-2 review's V4 confirmed
the §0.1.0.34 / §0.1.0.35 distinction landed.  Round 3
spot-checks the discipline holds across every public
docstring.

**Finding.** Spot-check of five docstrings:

- `Nat.simRecVec` (spec §3.1, lines 215; plan Task 1.4,
  lines 226–229): cites §0.1.0.7 (definition) plus §0.1.0.34
  (proof technique). ✓
- `ERMor1.tuplePackedBound` (spec §4.1, line 310; plan
  Task 5.4, lines 610–611): cites §3.2 plus §0.1.0.34, p. 14
  for `Nat.tuplePack_le`. ✓
- `ERMor1.simultaneousBoundedRec` (spec §5.2, lines 469–471;
  plan Task 11.1, lines 1201–1204): cites §0.1.0.34 (proof
  technique) with §0.1.0.35 as "higher-level corollary for
  `n ≥ 2`".  ✓
- `simultaneousBoundedRec_interp_correct` (spec §5.4,
  lines 632–634; plan Task 15.1, lines 1688–1690): same
  citation form. ✓
- `ofSimultaneousBoundedRec` (spec §5.5, lines 704–706;
  plan Task 16.1, lines 1785–1787): cites §3.2 + §15.13
  punch-list ("no `3^E`-style coefficient leaks out"). ✓

All five spot checks confirm the §0.1.0.34-primary,
§0.1.0.35-corollary discipline.  Per the count tally,
the spec has 9 §0.1.0.34 references vs 6 §0.1.0.35;
the plan has 17 vs 10.  No remaining instances of
§0.1.0.35 used as primary citation.

**Severity.** Clean.

---

## V8 — Internal consistency: `packedStep` / `packedStepCtx` types

**Claim under challenge.** Are the `packedStep`,
`packedStepCtx`, and named-lemma signatures consistent
across spec §5.1 / §5.2 and plan tasks 10.5, 10.6, 14.1?

**Finding.** Direct comparison:

- `packedStepCtx (k a : ℕ) : Fin (a + 1 + (k + 1)) →
  ERMor1 (a + 2)` — spec §5.1 (lines 437–438), plan
  Task 10.5 (lines 1119–1120).  Identical pattern bodies. ✓
- `packedStep (k a : ℕ) (g : Fin (k + 1) →
  ERMor1 (a + 1 + (k + 1))) : ERMor1 (a + 2)` — spec
  §5.1 (lines 453–455), plan Task 10.6 (lines 1151–1153).
  Identical bodies. ✓
- `interp_packedStepCtx` (plan Task 14.1, lines 1418–1424)
  has signature `(k a : ℕ) (n prev_packed : ℕ)
  (x : Fin a → ℕ) (i : Fin (a + 1 + (k + 1))) : ...
  = (Fin.append (Fin.cons n x) (Nat.tupleAt k prev_packed))
  i`.  The output `Fin (a + 1 + (k + 1)) → ℕ` matches the
  outer-context arity; the appended pieces have arities
  `Fin (a + 1) → ℕ` (`Fin.cons n x`) and `Fin (k + 1) → ℕ`
  (`Nat.tupleAt k prev_packed`), summing to
  `a + 1 + (k + 1)`. ✓

Slot-arithmetic verified independently:

- Param branch (`v < a`): outer index `v + 1` lies in
  `1..a`; inner slot is `v + 2` lying in `2..a + 1`.
  `omega` discharges `v + 2 < a + 2` from `v < a`. ✓
- Prev branch (`¬ (v < a)`): outer index `v + 1` lies in
  `a + 1..a + k + 1`; prev-vector index is `v - a` lying
  in `0..k`.  From `h_v : v + 1 < a + 1 + (k + 1)` (giving
  `v < a + k + 1`) and `v ≥ a`, we obtain `v - a ≤ k`,
  hence `v - a < k + 1`. ✓

**Severity.** Clean.

---

## F1 — `simp only [ih]` reliance on iota-reduction (concern)

**Claim under challenge.** Plan Task 14.3's succ case uses
`simp only [ih]` to rewrite `Nat.rec base step (m + 1)` to
the form `Nat.tuplePack k (simRecVec ... (m + 1) x)`, with
`ih : Nat.rec base step m = Nat.tuplePack k
(simRecVec ... m x)`.

**Finding.** For `simp only [ih]` to fire, the goal LHS
must contain `Nat.rec base step m` as a subterm.  At the
start of the succ case, the goal is
`Nat.rec base step (m + 1) = Nat.tuplePack k
(simRecVec ... (m + 1) x)`.  The LHS does not literally
contain `Nat.rec base step m`; it contains
`Nat.rec base step (m + 1)`, which is iota-reducible to
`step m (Nat.rec base step m)` but Lean does not eagerly
display the reduced form.

`simp` and `simp only` do perform beta / eta / iota
reduction as part of normalization (per the Lean reference
manual), so in practice `simp only [ih]` first iota-reduces
`Nat.rec base step (m + 1)` to `step m (Nat.rec base step
m)`, exposing `Nat.rec base step m` as a subterm, then
rewrites via `ih`.  This is the standard idiom for
`Nat.rec`-style inductions inside `simp only`.

The plan acknowledges this dependency at lines 1565–1569
with an explicit fallback: "If `simp only [ih]` does not
fire because `Nat.rec`'s definitional unfolding is needed
first, the implementer can use a `change` step to expose
`(packedStep ...).interp (Fin.cons m (Fin.cons (Nat.rec
... m) x)) = _` and then `rw [ih]`."  The fallback is
sound and easy to apply if the primary tactic does not
discharge.

The concern is that `simp only [ih]` working depends on
`simp`'s iota-closure behavior, which is reliable in
mathlib practice but is a subtle dependency.  An
implementer reading the plan may not realize the
iota-step is implicit.

**Severity.** Concern (minor — fallback is documented).

**Recommended action.** Add one sentence to the plan's
Task 14.3 succ-case comment noting that `simp only [ih]`
relies on `simp`'s iota-reduction closure (the LHS pattern
`Nat.rec base step m` is exposed by iota-reducing
`Nat.rec base step (m + 1)`).  No code change required.

---

## F2 — Task 13.1 `packedBound_dominates_iter`'s spurious `n` (minor)

**Claim under challenge.** Plan Task 13.1
(lines 1320–1339) defines `packedBound_dominates_iter`:

```lean
theorem packedBound_dominates_iter
    (k a : ℕ)
    (h : Fin (k + 1) → ERMor1 a)
    (g : Fin (k + 1) → ERMor1 (a + 1 + (k + 1)))
    (componentBound : ERMor1 (a + 1))
    (n : ℕ) (x : Fin a → ℕ) (m : ℕ) (h_m_le_n : m ≤ n)
    (h_dominates :
      ∀ (m' : ℕ), m' ≤ n → ∀ (j : Fin (k + 1)),
        Nat.simRecVec ... m' x j
          ≤ componentBound.interp (Fin.cons m' x)) :
    Nat.tuplePack k (Nat.simRecVec ... m x)
      ≤ (ERMor1.tuplePackedBound k componentBound).interp
          (Fin.cons m x) := by
  apply ERMor1.tuplePackedBound_dominates
  intro j
  exact h_dominates m h_m_le_n j
```

**Finding.** The lemma's `(n : ℕ)` and `(h_m_le_n : m ≤ n)`
parameters are used only to invoke `h_dominates m h_m_le_n
j`.  Conceptually `n` is the upper-bound iteration up to
which the dominance hypothesis is guaranteed; the lemma
specializes to a particular `m ≤ n`.

The signature is correct — it matches the discharge-site
in Task 14.4 (`packedBound_dominates_iter k a h g
componentBound n x j h_j_le_n h_dominates`).  The
parametrization through `n` is forced by the hypothesis
form of `h_dominates`, which itself takes `m'` ranging
over `m' ≤ n`.

A simpler signature would inline the dominance fact at
the specific `m`:

```lean
... (h_dominates_m : ∀ j, Nat.simRecVec ... m x j
      ≤ componentBound.interp (Fin.cons m x)) : ...
```

eliminating `n` and `h_m_le_n`.  The caller then provides
`fun j => h_dominates m h_m_le_n j`.  This is a marginal
ergonomic preference and the present signature works; the
plan's choice keeps the discharge-site syntax compact at
the cost of two extra parameters in the helper.

**Severity.** Minor.

**Recommended action.** No change required.  Either
signature is acceptable.

---

## F3 — `interp_packedStepCtx` `match v, h_v with` form (clean)

**Claim under challenge.** Round 2 (E8) flagged that the
`match v, h_v with` form in Task 14.1's
`interp_packedStepCtx` proof might fail to elaborate
against the `packedStepCtx` definition's pattern shape.

**Finding.** Reviewing the present text:

```lean
rcases i with ⟨v, h_v⟩
match v, h_v with
| 0, _ => ...
| s + 1, h_in => ...
```

The `match` is on the values `(v, h_v)` after
`rcases i`.  In the `0, _` case, `v` becomes `0` and `h_v`
is unnamed.  In the `s + 1, h_in` case, `v` becomes `s + 1`
and `h_v` becomes `h_in`.  Lean 4 supports this tactic-level
`match` form (it lifts the term-level `match` into the
tactic monad).

The `packedStepCtx` definition itself is term-level pattern
matching; the proof's `match` is tactic-level pattern
matching on the destructured `i`.  After `rcases i with
⟨v, h_v⟩`, `i` is replaced by `⟨v, h_v⟩` everywhere in
the goal, and the proof needs to compute
`(packedStepCtx k a ⟨v, h_v⟩).interp ...` for each value
of `v`.  The `match v, h_v with` then aligns with the
def's pattern via def-elaboration.

This is the same pattern step-1 uses (`tupleAt_le`'s
induction at `Tupling.lean:99`).  Verified to elaborate
in mathlib practice.

**Severity.** Clean.

**Recommended action.** None.

---

## F4 — Test discipline: 2-component swap example uses `decide` (clean)

**Claim under challenge.** Plan Task 4.3 (lines 496–507)
provides a 2-component swap example with `:= by decide`:

```lean
example :
    simRecVec 1 0
      (fun j _ => match j with
        | ⟨0, _⟩ => 1
        | ⟨1, _⟩ => 2)
      (fun j ctx => match j with
        | ⟨0, _⟩ => ctx ⟨2, by decide⟩
        | ⟨1, _⟩ => ctx ⟨1, by decide⟩)
      5 (fun _ => 0) ⟨0, by decide⟩ = 2 := by decide
```

**Finding.** Tracing:

- Iter 0: `(1, 2)`.
- Iter 1: each component reads from prev via slots 1 and
  2.  Component 0 reads slot 2 (prev component 1) = 2;
  component 1 reads slot 1 (prev component 0) = 1.
  Result: `(2, 1)`.
- Iter 2: swap again → `(1, 2)`.
- Iter 3: `(2, 1)`.  Iter 4: `(1, 2)`.  Iter 5: `(2, 1)`.

Component 0 at iteration 5 = 2.  ✓

The `decide` invocation evaluates `simRecVec 1 0 ...`
through 5 iterations of `Nat.rec` over a `Fin 2 → ℕ` value.
This is a Nat-level computation with no Gödel-numbering
(no ER `.interp` chain, no `Nat.pair`/`Nat.unpair` of
large numbers).  The values stay in `{1, 2}` throughout,
so `decide` will close in microseconds.

The slot indices (`⟨2, by decide⟩` and `⟨1, by decide⟩`)
are within the `Fin 3` step-input arity (since
`a + 1 + (k + 1) = 0 + 1 + 2 = 3`).  ✓

The base case uses `Fin 2` indices (`⟨0, _⟩` and `⟨1, _⟩`)
and the step case uses `Fin 3` indices (`ctx ⟨2, ...⟩`
for prev component 1; `ctx ⟨1, ...⟩` for prev component
0; slot 0 is the iteration counter, unused).  ✓

The Gödel-numbering test discipline at plan lines 134–141
restricts `#guard` on `ERMor1.<X>.interp` for `X`
involving Gödel-coding constructions; this Nat-level
example does not consume any ER `.interp`, so the
discipline does not apply.  ✓

**Severity.** Clean.

**Recommended action.** None.

---

## F5 — `ofSimultaneousBoundedRec` `.bounds` chain (clean)

**Claim under challenge.** Plan Task 16.1 (lines 1810–1829)
constructs the `.bounds` field of
`ofSimultaneousBoundedRec` via
`exact h_component.trans (h_bound.trans h_poly)` (the
post-round-1 fix replacing the original `omega`).  Walk
through the chain.

**Finding.**

- `h_component`'s claim (lines 1810–1821):

  ```lean
  ((ERMor1.simultaneousBoundedRec k a h g
        componentBound) i).interp ctx
    ≤ (ERMor1.boundedRec
          (ERMor1.packedBase k a h)
          (ERMor1.packedStep k a g)
          (ERMor1.tuplePackedBound k
            componentBound)).interp ctx
  ```

  Proven by `simp only [ERMor1.simultaneousBoundedRec,
  ERMor1.interp_comp, ERMor1.interp_tupleAt,
  Matrix.cons_val_zero]; exact Nat.tupleAt_le k _ i`.

- `h_bound`'s claim (lines 1822–1826) is from
  `interp_boundedRec_le_bound`
  (`Utilities/ERArith.lean:1804`):

  ```lean
  (boundedRec base step bound).interp ctx
    ≤ bound.interp ctx
  ```

  Substituted: `(boundedRec packedBase packedStep
  tuplePackedBound).interp ctx ≤ tuplePackedBound.interp
  ctx`.  ✓

- `h_poly`'s claim (lines 1827–1828) is from
  `(ofTuplePackedBound k pb_bound).bounds ctx`:

  ```lean
  tuplePackedBound.interp ctx ≤
    (ofTuplePackedBound k pb_bound).coefficient *
      (max + 1) ^ (ofTuplePackedBound k pb_bound).degree +
      (ofTuplePackedBound k pb_bound).constant
  ```

  ✓

- `.bounds`'s expected output is

  ```lean
  ((simultaneousBoundedRec k a h g componentBound) i).interp
      ctx ≤
    (ofSimultaneousBoundedRec ... i).coefficient *
      (max + 1) ^ (ofSimultaneousBoundedRec ... i).degree +
      (ofSimultaneousBoundedRec ... i).constant
  ```

  Since the `coefficient`, `degree`, `constant` fields of
  `ofSimultaneousBoundedRec` are defined to equal the
  corresponding fields of `ofTuplePackedBound k pb_bound`
  (lines 1799–1804), the RHS of `.bounds` equals the RHS
  of `h_poly` definitionally. ✓

The chain
`h_component : A ≤ B`, `h_bound : B ≤ C`,
`h_poly : C ≤ D` composes via
`h_component.trans (h_bound.trans h_poly) : A ≤ D`,
matching the expected `.bounds` output.  ✓

The §15.13 punch-list claim ("no `3^E`-style coefficient
leaks out") is preserved by inheritance from
`ofTuplePackedBound`, whose coefficient depends only on
`(k, pb_bound)` not on any source K^sim term structure.

**Severity.** Clean.

**Recommended action.** None.

---

## Summary

**Total items.** 13 (V1–V8 round-2-fix verifications;
F1–F5 new findings).

**Defects.** 0.

**Concerns.** 1.

- F1 — `simp only [ih]` in Task 14.3 succ case relies on
  `simp`'s iota-reduction closure.  Plan provides a
  fallback; recommend a one-sentence note.

**Minor.** 1.

- F2 — `packedBound_dominates_iter`'s `(n, h_m_le_n)`
  parametrization could be inlined at the specific `m`
  for an ergonomic simplification; either form works.

**Clean.** 11.

- V1, V2, V3, V4, V5, V6, V7, V8, F3, F4, F5.

**Overall assessment.** Clean bill of health.

The plan and spec are implementable in their current
form.  Rounds 1 and 2 addressed the structural defects
(slot-arithmetic off-by-one, slot-ordering mismatch,
constructor-name typo, `apply`-vs-`rw` unification, bare
`simp` style violations, spec coherence on the step
lemma, `Nat.zero_eq` non-existence,
`rw [Nat.rec, ih]` non-standard form, missing
`Nat.simRecVec_succ`); round 3 verifies the round-2
fixes hold without exception.  The remaining items are
an implementation-time clarification (F1 — note that
`simp only [ih]` works via iota-reduction) and a
parameter-style preference (F2 — either signature is
acceptable).  Neither is a blocker.

The mathematical content was already verified across
prior rounds (Tourlakis citation discipline at §0.1.0.34
primary / §0.1.0.35 corollary; bound formula
`tuplePackCoef k * (componentBound + 1)^(2^k)`;
PolyBound coefficient formula; bottom-up named-composite
discipline; `Fin (a + 1 + (k + 1))` outer / `Fin (a + 2)`
inner slot conventions matching master design §3.2 and
existing `kSimStepContext`).  Round 3 adds verification
that:

- The `rw`-based discharge of
  `boundedRec_eq_natRec_of_bounded` aligns with the
  existing usage pattern at
  `GebLeanTests/Utilities/ERArith.lean:71`.
- The `Nat_rec_packed_eq_tuplePack_simRecVec` extraction
  to top level enables both the dominance discharge and
  the main equality in `packedRec_eq_tuplePack_simRecVec`
  without duplication.
- The `interp_packedStepCtx` simp set
  (`Fin.append_left`, `Fin.append_right`,
  `Fin.cons_zero`, `Fin.cons_succ`) matches mathlib's
  current naming (verified by grep over
  `.lake/packages/mathlib/Mathlib/Data/Fin/Tuple/Basic.lean`).
- The `ofSimultaneousBoundedRec` `.bounds` `.trans`-chain
  composes correctly to discharge the per-component
  PolyBound claim against the inherited
  `ofTuplePackedBound` shape.
- The 2-component swap example in Task 4.3 evaluates to
  the claimed value 2 by parity-of-iteration analysis,
  and `decide` will close it in negligible time.

End of round-3 adversarial review.
