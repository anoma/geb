# Adversarial review (round 2) of the step-2 plan
<!-- ER-side simultaneous bounded recursion -->

> Reviewer's stance: fresh round-2 reading of
> `docs/superpowers/plans/2026-05-03-step-2-er-simultaneous-bounded-rec.md`
> and
> `docs/superpowers/specs/2026-05-03-step-2-er-simultaneous-bounded-rec-design.md`
> against the round-1 review at
> `docs/research/2026-05-03-step-2-plan-adversarial-review-round-1.md`,
> master design §3.2 / §15.13, CLAUDE.md, and the existing
> infrastructure (`GebLean/Utilities/Tupling.lean`,
> `GebLean/Utilities/ERTupling.lean`,
> `GebLean/Utilities/ERArith.lean`,
> `GebLean/Utilities/KSimSzudzikSimrec.lean`,
> `GebLean/LawvereERPolynomialBound.lean`).

## Overall assessment

Round-1's three defects (D1 off-by-one, D2 slot-ordering,
D3 `ofZero` typo) all verify as fixed.  Plan and spec now
use master-design-aligned arities `a + 1 + (k + 1)`,
`a + 2`, `a + 1` throughout, with slot ordering
`(counter, params, prev)` outer / `(counter, packed_prev,
params)` inner.  Citations now lead with §0.1.0.34
(matching the proof technique).  Tasks 13–14 are reordered.
`ofZeroN 0` is used.  No all-caps "BLOCKED" in narrative
prose.  Banned-word grep clean on plan and spec.

Round-2 surfaces one new defect plus several new concerns
in the proof outlines for Task 14 (the iteration-induction
chain that consumes `boundedRec_eq_natRec_of_bounded`).
The defect (E1) is in the choice of `apply` over `rw` for
`boundedRec_eq_natRec_of_bounded` — the lemma's
conclusion-RHS is `Nat.rec ...`, but the goal's RHS is
`Nat.tuplePack ...`, so `apply` cannot unify them.
Concerns E2–E5 are tactical / structural issues in the
Task 14 proof sketches.

The spec also retained an incorrect statement for
`packedStep_interp_eq_tuplePack_step` (§5.3) that the
round-1 fixes did not touch (E4).

## Round-1 fix verifications

### V1 — D1 (off-by-one in `packedStepCtx`'s parameter branch) — fixed

Plan Task 10.5 / spec §5.1 now define:

```lean
| ⟨v + 1, h_v⟩ =>
    if h_param : v < a then
      ERMor1.proj ⟨v + 2, by omega⟩
    else
      ERMor1.comp
        (ERMor1.tupleAt k ⟨v - a, by omega⟩)
        ![ERMor1.proj 1]
```

With outer arity `Fin (a + 1 + (k + 1))` and slot ordering
`(counter, params, prev)`, the arithmetic checks:

- Param branch (`v < a`, outer index `v + 1` in
  `1..a`): inner slot is `v + 2`, range `2..a + 1`.  ✓
- Prev branch (`v ≥ a`, outer index `v + 1` in
  `a + 1..a + k + 1`): prev-vector index is `v - a`,
  range `0..k`.  ✓

Both `omega` invocations close: for params, `v + 2 < a + 2`
follows from `v < a`; for prev, `v - a < k + 1` follows
from `v + 1 < a + 1 + (k + 1)` (giving `v < a + k + 1`)
and `v ≥ a`.

### V2 — D2 (slot-ordering inconsistency) — fixed

Plan and spec now consistently use `a + 1 + (k + 1)`,
`a + 2`, `a + 1`, matching master design §3.2 and existing
`kSimStepContext`.  `Nat.simRecVec`'s step is
`g_all j (Fin.append (Fin.cons n x) prev)` — slot 0
counter, slots 1..a params, slots a+1..a+k+1 prev.
`ERMor1.boundedRec` instantiated at `k_b = a` produces
`ERMor1 (a + 1)` definitionally (no `1 + a` / `a + 1`
mismatch).  `simultaneousBoundedRec`'s return type
`ERMorN (a + 1) (k + 1)` is consistent.

### V3 — D3 (`ofZero` vs `ofZeroN`) — fixed

Plan Task 9.2 now writes `ERMor1.PolyBound.ofZeroN 0`, and
Task 17.2 also uses `ofZeroN`.  No remaining
`ofZero (n := 0)` references.

### V4 — C1 (Tourlakis citation imprecision) — fixed

Plan and spec lead with §0.1.0.34 (the proof technique:
pairing-based pack-and-unpack closure of E^2 under
simultaneous bounded recursion); §0.1.0.35 is now cited
only as the "higher-level corollary for `n ≥ 2`" /
generalization to `E^{n+1}`.  The
`Nat.simRecVec` definition cites §0.1.0.7 (the K^sim
hierarchy definition) plus §0.1.0.34 (the proof technique).

### V5 — C2 (Task 13/14 ordering) — fixed

Plan Task 13 now lands `packedBound_dominates_iter` and
`packedBound_mono` (the discharge lemmas) before Task 14
introduces `packedRec_eq_tuplePack_simRecVec` (which
consumes them).  The plan body explicitly notes the swap
(line 1302).

### V6 — C4 (`Matrix.cons_val_zero` in Task 15.1 simp set) — addressed

Plan Task 15.1's simp set now reads
`simp only [ERMor1.simultaneousBoundedRec,
ERMor1.interp_comp, ERMor1.interp_tupleAt,
Matrix.cons_val_zero]`.  `Matrix.cons_val_zero` is now
included.  Task 16.1 also includes it.  Task 12.1 (base
case) does not include it; the plan does not flag this,
but with `interp_tuplePack` and `simRecVec_zero` in the
simp set it should still close.

### V7 — C5 (`omega` → `Nat.le_trans`) — fixed

Plan Task 16.1 now ends with
`exact h_component.trans (h_bound.trans h_poly)` instead
of `omega`.  This handles the non-linear `^`-bearing
final goal correctly.

### V8 — M1 (all-caps "BLOCKED") — fixed

No remaining "BLOCKED" / "REQUIRED" in narrative.  Plan
prose says "iterate until clean before committing" and
similar formulations.  Banned-word grep clean.

### V9 — M2 (line lengths) — substantially fixed

Plan has 4 lines > 80 chars (lines 1, 569, 1170, 1982),
each is either an unavoidable URL or close enough to be
acceptable per round 1's "unavoidable URLs" exception.
Spec has 0 lines > 80.

---

## New findings

## E1 — Task 14.3 `apply` against non-unifiable RHS (defect)

**Claim under challenge.** Plan Task 14.3's
`packedRec_eq_tuplePack_simRecVec` proof begins:

```lean
... :
    (ERMor1.boundedRec ...).interp (Fin.cons n x)
      = Nat.tuplePack k (Nat.simRecVec k a ... n x) := by
  apply ERMor1.boundedRec_eq_natRec_of_bounded
  · ...  -- discharges hypothesis 1 (dominance)
  · ...  -- discharges hypothesis 2 (monotonicity)
```

**Finding.** The conclusion of
`ERMor1.boundedRec_eq_natRec_of_bounded`
(`ERArith.lean:2206-2211`) is

```lean
(ERMor1.boundedRec base step bound).interp
    (Fin.cons n ctx) =
  Nat.rec (base.interp ctx)
    (fun j prev =>
      step.interp (Fin.cons j (Fin.cons prev ctx)))
    n
```

To dispatch the goal via `apply`, Lean must unify the
lemma's RHS (`Nat.rec ...`) with the goal's RHS
(`Nat.tuplePack k (Nat.simRecVec ... n x)`).  These are
not definitionally equal — `Nat.tuplePack k` is a
non-trivial function applied to `Nat.simRecVec ... n x`,
which is itself a `Nat.rec`-style recursive computation,
but Lean's unifier will not equate them.  `apply` will
fail to elaborate.

The intended proof structure is:

1. Rewrite via `boundedRec_eq_natRec_of_bounded` to turn
   the LHS into `Nat.rec ...`, leaving a goal
   `Nat.rec ... = Nat.tuplePack ...`.
2. Prove the auxiliary `Nat.rec ... = Nat.tuplePack ...`
   identity (the plan's `h_rec_eq` does this — but it is
   nested inside a hypothesis-discharge subgoal where it
   is not load-bearing for the main proof).

The plan's `h_rec_eq` (built inside the goal-1 dispatch)
is mathematically the right object, but it is bound to
the discharge subgoal's local context and is not
available to close the main goal afterward.

**Severity.** Defect.

**Recommended action.** Restructure Task 14.3's proof.
One option:

```lean
... := by
  have h_rec_eq : ∀ j ≤ n,
      Nat.rec ((ERMor1.packedBase k a h).interp x)
        (fun m prev =>
          (ERMor1.packedStep k a g).interp
            (Fin.cons m (Fin.cons prev x))) j
        = Nat.tuplePack k
            (Nat.simRecVec k a (fun j' => (h j').interp)
              (fun j' => (g j').interp) j x) := by
    intro j h_j_le_n
    induction j with
    | zero => ...
    | succ m ih => ...
  rw [ERMor1.boundedRec_eq_natRec_of_bounded
        (n := n) ... ?_ ?_]
  · exact h_rec_eq n (le_refl n)
  · -- hypothesis 1: dominance
    intro j h_j_le_n
    rw [h_rec_eq j h_j_le_n]
    exact packedBound_dominates_iter ...
  · -- hypothesis 2: monotonicity
    exact packedBound_mono ...
```

Or use `Eq.trans (boundedRec_eq_natRec_of_bounded ...) (h_rec_eq n (le_refl n))`.
The implementer must extract `h_rec_eq` to top-level scope
so it is available both for the dominance discharge and
for the final equality.

---

## E2 — Task 14.1 uses bare `simp [...]` instead of `simp only [...]` (defect)

**Claim under challenge.** Plan Task 14.1's
`interp_packedStepCtx` proof contains three uses of
bare `simp [...]`:

- Line 1430: `simp [ERMor1.packedStepCtx, ...]`.
- Line 1437: `simp [ERMor1.packedStepCtx, h_param, ...]`.
- Line 1444: `simp [ERMor1.packedStepCtx, h_param, ...]`.

**Finding.** CLAUDE.md "Code Style" says: "Use
`simp only [...]` not bare `simp [...]`."  The plan body
mirrors this rule explicitly in its style-and-discipline
reminders (line 103: "Use `simp only [...]` not bare
`simp [...]`").  All three uses in Task 14.1 violate the
rule.

In addition to the style violation, bare `simp` here
introduces fragility: if mathlib adds a new simp lemma in
the `Fin.append` / `Fin.cons` neighbourhood, the proof's
behavior may change unexpectedly.

**Severity.** Defect (style rule violation; the plan is
prescriptive and the implementer must use `simp only`).

**Recommended action.** Change all three `simp [...]` to
`simp only [...]`.  In the closing-out simp arguments,
the implementer will need to enumerate the supporting
lemmas explicitly.  The plan's parenthetical at lines
1449–1456 already hints that
`Fin.append_left`, `Fin.append_right`, `Fin.cons_zero`,
`Fin.cons_succ` may be needed; promote those into the
explicit `simp only` set.

---

## E3 — Task 14.3 `simp only [Nat.rec, Nat.zero_eq]` is suspect (concern)

**Claim under challenge.** Plan Task 14.3's `induction j`
zero-case writes:

```lean
| zero =>
    simp only [Nat.rec, Nat.zero_eq]
    exact
      ERMor1.packedBase_interp_eq_tuplePack_simRecVec_zero
        k a h g x
```

**Finding.** Two issues:

1. `Nat.rec` is the type-theoretic recursor, not a typical
   `simp` rewrite lemma.  Including it in `simp only` does
   not always trigger the iota-reduction the plan expects;
   in modern Lean 4 / mathlib, the canonical way to expose
   `Nat.rec base step 0 = base` is by `rfl` /
   definitional reduction or by explicit pattern matching
   on the recursor's behavior.

2. `Nat.zero_eq` is a name from Lean 3 / early Lean 4 that
   has been variously deprecated; in current mathlib it
   is sometimes absent or marked deprecated.  `simp only`
   with a missing or deprecated lemma name will produce a
   warning or error.

   Verified by `grep` over `GebLean/`: no `Nat.zero_eq`
   uses anywhere in the codebase.  The plan introduces a
   reference that may not resolve.

A cleaner zero-case:

```lean
| zero =>
    show (ERMor1.packedBase k a h).interp x = _
    exact ERMor1.packedBase_interp_eq_tuplePack_simRecVec_zero
      k a h g x
```

or just:

```lean
| zero =>
    exact ERMor1.packedBase_interp_eq_tuplePack_simRecVec_zero
      k a h g x
```

(if the `Nat.rec ... 0 = base.interp ctx` reduction is
definitional, which it is in Lean 4's kernel.)

**Severity.** Concern.

**Recommended action.** Drop `Nat.zero_eq` from the simp
set.  Replace `simp only [Nat.rec, Nat.zero_eq]` with
either `rfl`-based reduction or an explicit `change` /
`show` step.  The successor case's `rw [Nat.rec, ih]`
likewise needs revision (see E5).

---

## E4 — Spec §5.3 step-lemma mathematically incorrect (defect)

**Claim under challenge.** Spec §5.3's statement of
`packedStep_interp_eq_tuplePack_step`:

```lean
theorem packedStep_interp_eq_tuplePack_step
    (k a : ℕ)
    (g : Fin (k + 1) → ERMor1 (a + 1 + (k + 1)))
    (n : ℕ) (x : Fin a → ℕ) (prev_packed : ℕ)
    (h_prev :
      prev_packed = Nat.tuplePack k
        (Nat.simRecVec k a
          (fun j' => fun y => 0)  -- bases unused at step
          (fun j' => (g j').interp) n x)) :
    (ERMor1.packedStep k a g).interp
        (Fin.cons n (Fin.cons prev_packed x))
      = Nat.tuplePack k
          (Nat.simRecVec k a (fun j' => fun y => 0)
            (fun j' => (g j').interp) (n + 1) x)
```

**Finding.** The bases-as-zero substitution
(`fun j' => fun y => 0`) is mathematically wrong.
`Nat.simRecVec k a h_all g_all (n + 1) x` depends on
`h_all` only through the iterated step composition: at
iteration `n + 1`, every base value `h_all j' x` has been
overwritten by `n + 1` step applications, so by induction
the value at iteration `n + 1` depends on the bases only
via the `n`-fold iterated step starting from
`h_all j' x`.  Replacing the bases with the zero family
gives a different function entirely — only iteration 0 is
unaffected.

The spec's hypothesis says `prev_packed = tuplePack k
(simRecVec k a 0-bases g-step n x)`, then concludes the
step output equals `tuplePack k (simRecVec k a 0-bases
g-step (n + 1) x)`.  This statement IS true (because the
bases factor through the inductive iteration: if
`prev_packed = tuplePack k (simRecVec ... n x)` for
*any* base family, the step produces `tuplePack k
(simRecVec ... (n + 1) x)` for *the same* base family).
But the comment "bases unused at step" is misleading —
the bases do not vanish; they are just held fixed across
iterations.

The plan's Task 14.2 uses a different and correct form:

```lean
theorem packedStep_interp_eq_tuplePack_step
    (k a : ℕ)
    (h : Fin (k + 1) → ERMor1 a)
    (g : Fin (k + 1) → ERMor1 (a + 1 + (k + 1)))
    (n : ℕ) (x : Fin a → ℕ) :
    let prev_packed :=
      Nat.tuplePack k
        (Nat.simRecVec k a (fun j' => (h j').interp)
          (fun j' => (g j').interp) n x)
    (ERMor1.packedStep k a g).interp
        (Fin.cons n (Fin.cons prev_packed x))
      = Nat.tuplePack k
          (Nat.simRecVec k a (fun j' => (h j').interp)
            (fun j' => (g j').interp) (n + 1) x)
```

This uses the actual `h` parameter (no zero-base
substitution) and binds `prev_packed` via `let`, which is
the correct mathematical statement.

The spec and plan are inconsistent for this lemma.  A
reader of the spec who follows §5.3 verbatim will produce
either a misleading comment ("bases unused") or an
incorrect proof attempt at the call site.

**Severity.** Defect (spec coherence).

**Recommended action.** Update spec §5.3 to match the
plan Task 14.2 statement: remove the
`(fun j' => fun y => 0)` substitution; reintroduce the
`h` parameter; and use the `let` binding for
`prev_packed`.  Drop the misleading "bases unused at
step" comment.

---

## E5 — Task 14.3 `rw [Nat.rec, ih]` is non-standard (concern)

**Claim under challenge.** Plan Task 14.3's
`induction j` succ-case writes:

```lean
| succ m ih =>
    rw [Nat.rec, ih]
    exact
      ERMor1.packedStep_interp_eq_tuplePack_step
        k a h g m x
```

**Finding.** `Nat.rec` is a recursor, not a rewrite-form
equation lemma.  `rw [Nat.rec]` would attempt to rewrite
using the type or signature of `Nat.rec`, which is not a
proof of an equation.  In modern Lean 4 / mathlib, the
canonical way to step the recursor is either:

- Definitional reduction:
  `Nat.rec base step (Nat.succ n) = step n (Nat.rec base step n)`
  is iota-reducible, so `rfl` or `change` or `show` can
  expose the `step n prev` form.
- `simp only [Nat.rec_succ]` (if such a simp lemma exists
  in the present mathlib version; verify before writing).

Even granting that `rw [Nat.rec]` is interpreted as
"unfold one step of the recursor" (which it is not, in
Lean 4), the plan's interleaving of `Nat.rec` unfolding
and `ih` rewriting is fragile.

A cleaner succ-case:

```lean
| succ m ih =>
    show (ERMor1.packedStep k a g).interp
            (Fin.cons m (Fin.cons (Nat.rec ... m) x))
          = _
    rw [ih]
    exact ERMor1.packedStep_interp_eq_tuplePack_step
      k a h g m x
```

or `simp only [Nat.rec]` followed by `rw [ih]`.

**Severity.** Concern.

**Recommended action.** Replace `rw [Nat.rec, ih]` with
either an explicit `show` / `change` chain that exposes
the `step m (Nat.rec ... m)` form, or with the canonical
mathlib `simp` lemma for `Nat.rec` succ-unfolding.
Verify the lemma name (`Nat.rec_succ`?) exists in the
current mathlib version before writing.

---

## E6 — Task 14.2 omits `Nat.simRecVec_succ` from initial simp set (concern)

**Claim under challenge.** Plan Task 14.2's proof of
`packedStep_interp_eq_tuplePack_step`:

```lean
intro prev_packed
simp only [ERMor1.packedStep, ERMor1.interp_comp,
  ERMor1.interp_tuplePack]
congr 1
funext j
rw [ERMor1.interp_comp]
congr 1
funext i
rw [ERMor1.interp_packedStepCtx]
-- Goal: (Fin.append (Fin.cons n x)
--         (Nat.tupleAt k prev_packed)) i
--     = (Fin.append (Fin.cons n x)
--         (Nat.simRecVec k a ... n x)) i
congr 1
funext j'
show Nat.tupleAt k prev_packed j' = ...
```

**Finding.** Two structural issues:

1. The plan's comment "Goal: (Fin.append ... Nat.tupleAt
   k prev_packed) i = (Fin.append ... Nat.simRecVec ... n
   x) i" is reached only after the RHS's `Nat.simRecVec
   ... (n + 1) x` is unfolded via `Nat.simRecVec_succ`.
   But `simp only` in the proof's first step does not
   include `Nat.simRecVec_succ`; the plan omits it.

   Without that unfolding, `congr 1; funext j` after
   `simp only [interp_tuplePack]` gives a goal of the
   form
   `(fun j => (g j).interp ...) = Nat.simRecVec ... (n+1) x`,
   which has `simRecVec ... (n+1) x` un-reduced.  Then
   `funext j` produces
   `(g j).interp ... = Nat.simRecVec ... (n + 1) x j`,
   and the proof needs to unfold the RHS via
   `simp only [Nat.simRecVec_succ]` (or the @[simp]
   `simRecVec_succ` lemma fires automatically inside
   bare `simp`, but the proof uses `simp only`).

2. The chain `congr 1; funext j; rw [interp_comp]; congr
   1; funext i; rw [interp_packedStepCtx]` relies on
   `interp_packedStepCtx` having a clean form for `i`.
   But Task 14.1's `interp_packedStepCtx` is itself in
   doubt due to E2 (uses bare `simp`).  If E2 forces
   `interp_packedStepCtx` to use a different form (e.g.,
   case-split on `i.val` via match), the consumers in
   Task 14.2 may need a different rewrite strategy.

**Severity.** Concern.

**Recommended action.** Add `Nat.simRecVec_succ` to the
initial `simp only` set in Task 14.2.  Verify the
slot-routing produces matching shapes after rewriting.
Re-verify the chain works once Task 14.1's
`interp_packedStepCtx` is in its final form.

---

## E7 — `Matrix.cons_val_zero` not in Task 12.1's simp set (minor)

**Claim under challenge.** Plan Task 12.1's
`packedBase_interp_eq_tuplePack_simRecVec_zero` uses

```lean
simp only [ERMor1.packedBase, ERMor1.interp_comp,
  ERMor1.interp_tuplePack, Nat.simRecVec_zero]
```

**Finding.** After unfolding `packedBase` and
`interp_comp`, the inner term becomes `(tuplePack k).interp
(fun j => (h j).interp x)`, which by `interp_tuplePack`
becomes `Nat.tuplePack k (fun j => (h j).interp x)`.  The
RHS is `Nat.tuplePack k (Nat.simRecVec ... 0 x)`, which
after `simRecVec_zero` (a `@[simp]` `rfl` lemma) becomes
`Nat.tuplePack k (fun j => (h j).interp x)`.  The two
sides are then `rfl`-equal.

The simp set should reduce both sides to the same form
without needing `Matrix.cons_val_zero`, since `packedBase`
uses no `Matrix.cons` form.  The plan's caveat
"If the simp set doesn't reduce cleanly, add a `funext`
or `change`" covers any leftover lambda-equality issue.

V6's caveat that Task 15.1 needs `Matrix.cons_val_zero`
does not apply here (Task 12 has no `![]`-shape cons).
This is an asymmetry but not an error.

**Severity.** Minor.

**Recommended action.** No change required.  The plan's
Task 12.1 should close as written.

---

## E8 — `interp_packedStepCtx` `match v, h_v with` form (minor)

**Claim under challenge.** Plan Task 14.1's
`interp_packedStepCtx` uses

```lean
rcases i with ⟨v, h_v⟩
match v, h_v with
| 0, _ => ...
| s + 1, h_in => ...
```

**Finding.** The `match v, h_v with` form is acceptable
in tactic mode (after `rcases`), pattern-matching on the
`Nat` value `v` and the proposition
`h_v : v < a + 1 + (k + 1)`.  The named bindings `_`
(in case `0`) and `h_in` (in case `s + 1`) work.

But the `packedStepCtx` definition itself uses
`| ⟨0, _⟩` and `| ⟨v + 1, h_v⟩` patterns at the function
level, not in tactic mode.  When `interp_packedStepCtx`'s
proof tries to compute
`(ERMor1.packedStepCtx k a ⟨v, h_v⟩).interp ...`, Lean's
elaborator must match the pattern.  After
`rcases i with ⟨v, h_v⟩` and then `match v, h_v with`,
the tactic-level match should align with the
function-level match.  This pattern is verified used in
existing infrastructure (e.g., `kSimStepContext`'s
`if h₀ : idx.val = 0` — but not the same `match` shape).

A safer alternative is to use `Fin.cases` /
`Fin.lastCases` (avoids the manual `Nat`-level pattern
match), as in `tupleAt_le`'s induction
(`Tupling.lean:99`).

**Severity.** Minor.

**Recommended action.** No change required if the
`match` form elaborates.  If the implementer encounters
elaboration issues, switch to `Fin.cases` /
`Fin.lastCases` style.

---

## E9 — Task 14.3 `Nat.rec` form ambiguity at top of induction (concern)

**Claim under challenge.** Plan Task 14.3's `h_rec_eq`
inside the dominance-discharge subgoal binds:

```lean
have h_rec_eq :
    Nat.rec ((ERMor1.packedBase k a h).interp x)
      (fun m prev =>
        (ERMor1.packedStep k a g).interp
          (Fin.cons m (Fin.cons prev x))) j
      = Nat.tuplePack k
          (Nat.simRecVec k a ... j x) := by
  induction j with
    ...
```

**Finding.** This induction is over `j` (the outer-loop
variable from the `apply boundedRec_eq_natRec_of_bounded`
discharge), not over `n`.  The induction hypothesis at
`succ m` is the equation at `j = m`.  But the `j` in
the goal is bound by `intro j h_j_le_n` in the dominance
discharge.  Lean's `induction` tactic on `j` will
generalize all dependencies on `j` — including
`h_j_le_n : j ≤ n`.  The induction hypothesis will then
be `(m ≤ n → ...)`.  But the induction step provides
`m + 1 ≤ n` (the goal's hypothesis after `intro`), not
`m ≤ n` for the IH.

The implementer may need:

- A separate top-level lemma proving the equation
  `Nat.rec ... j = Nat.tuplePack k (Nat.simRecVec ... j x)`
  for all `j`, without the `j ≤ n` hypothesis (since the
  equation holds unconditionally — the `boundedRec`-vs-
  `Nat.rec` correctness is what needs the hypothesis,
  not the recursor-pattern equation itself).
- Then applying the unconditional lemma at `j` inside
  the dominance discharge.

The plan's coupling of the unconditional equation
`Nat.rec ... j = Nat.tuplePack k ...` with the bounded
discharge subgoal makes the induction harder than
necessary.

**Severity.** Concern.

**Recommended action.** Refactor: extract `h_rec_eq` to
a top-level `have` (or even a separate named lemma)
proving `∀ j, Nat.rec ... j = Nat.tuplePack k ...`.
Apply it at `j` inside the dominance discharge and at
`n` for the main equality (closing the gap from E1).

---

## E10 — `Nat.rec` direct use vs `Nat.recAux` (minor)

**Claim under challenge.** Plan Task 14.3 writes
`Nat.rec ((ERMor1.packedBase k a h).interp x) (fun m prev => ...) j`.

**Finding.** Lean 4's `Nat.rec` has signature
`{motive : Nat → Sort u} → motive 0 → ((n : Nat) → motive
n → motive (n + 1)) → (t : Nat) → motive t`.
With a non-dependent motive `(fun _ => ℕ)`, `Nat.rec`
specializes to the iterator form the plan uses.  Lean
will elaborate this — but the plan's writing
`Nat.rec ((ERMor1.packedBase k a h).interp x) (fun m
prev => ...) j` requires Lean to infer the motive.

For comparison, the existing
`boundedRec_eq_natRec_of_bounded` uses the same pattern
in its conclusion:
`Nat.rec (base.interp ctx) (fun j prev => step.interp
(Fin.cons j (Fin.cons prev ctx))) n`.  So the form is
verified consistent.

**Severity.** Clean.

**Recommended action.** None.

---

## E11 — Plan Task 9.2's `ofZeroN 0` produces `coefficient = 0`, not `1` (minor)

**Claim under challenge.** Plan Task 9.2 contains:

```lean
example :
    (ERMor1.PolyBound.ofTuplePackedBound 1
       (ERMor1.PolyBound.ofZeroN 0)).coefficient
      = Nat.tuplePackCoef 1 * 1 ^ (2 ^ 1) := rfl
```

**Finding.** `ofZeroN 0` produces a `PolyBound (ERMor1.zeroN 0)`
with field values `degree = 0`, `coefficient = 0`,
`constant = 0` (per the explanation at lines 981–987).
`ofTuplePackedBound k pb`'s coefficient is
`tuplePackCoef k * (pb.coefficient + pb.constant + 1)^(2^k)
= tuplePackCoef k * (0 + 0 + 1)^(2^k)
= tuplePackCoef k * 1^(2^k)`.

At `k = 1`, this is `tuplePackCoef 1 * 1^(2^1)
= tuplePackCoef 1 * 1 = tuplePackCoef 1`.

The plan writes `Nat.tuplePackCoef 1 * 1 ^ (2 ^ 1)`,
which equals `tuplePackCoef 1 * 1` — same as
`tuplePackCoef 1`.  The example is consistent.

The `rfl` may or may not close depending on whether
`1 ^ (2 ^ 1)` reduces — for `Nat`, `1 ^ 2 = 1` is
definitional (via `Nat.pow_succ`-style reduction), so
`rfl` likely closes.  If not, replace with `by decide`
or `by norm_num`.

**Severity.** Clean (just a verification check).

**Recommended action.** None.  If `rfl` does not close
on implementation, fall back to `by decide` for the
arithmetic equality.

---

## Summary

- **Total items reviewed:** 20 (V1–V9 round-1 fix
  verifications; E1–E11 new findings).
- **Round-1 fix verifications:** 9 (all pass — the round-1
  defects D1, D2, D3 verify as fixed; concerns C1, C2,
  C4, C5 verify as fixed; minor M1, M2 verify as fixed).
- **New defects:** 3 (E1 `apply` vs `rw` mismatch in
  Task 14.3; E2 bare `simp` violations in Task 14.1;
  E4 spec §5.3 incorrect statement).
- **New concerns:** 4 (E3 `Nat.zero_eq` / `Nat.rec` simp
  oddity; E5 `rw [Nat.rec, ih]` non-standard form; E6
  missing `Nat.simRecVec_succ` in Task 14.2 simp set;
  E9 `h_rec_eq`'s `j ≤ n` over-coupling).
- **Minor / clean:** 4 (E7 Task 12.1 simp asymmetry —
  no fix needed; E8 `match v, h_v` form — clean
  conditionally; E10 `Nat.rec` form — clean; E11
  PolyBound coefficient — clean).

**Overall assessment:** **plan needs revision.**  The
round-1 defects are all fixed, and the slot-arithmetic
arithmetic verifies on independent recomputation.  But
the round-2 review surfaces three new defects in the
Task 14 proof outlines:

- E1 (`apply boundedRec_eq_natRec_of_bounded` cannot
  unify against the goal's `Nat.tuplePack` RHS) is the
  load-bearing issue: the plan as written would not
  compile at Task 14.3.
- E2 (bare `simp` in Task 14.1) violates a CLAUDE.md
  prescriptive style rule that the plan itself
  references in its discipline section.
- E4 (spec §5.3 statement uses bases-as-zero) is a spec
  coherence issue that the round-1 revisions did not
  reach.

Concerns E3, E5, E6, E9 are tactical-level proof
fragility issues that will cost the implementer
debugging time if not addressed in the plan.

Recommended sequence:

1. Fix E1 by extracting `h_rec_eq` to top-level scope
   (proving `∀ j, Nat.rec ... j = Nat.tuplePack k
   (Nat.simRecVec ... j x)` unconditionally) and using
   `rw` rather than `apply` for
   `boundedRec_eq_natRec_of_bounded`.  This subsumes E9.
2. Fix E2 by changing all `simp [...]` in Task 14.1 to
   `simp only [...]` with explicit lemma lists.
3. Fix E4 by updating spec §5.3 to match plan Task 14.2's
   correct statement.
4. Address E3 by dropping `Nat.zero_eq` and using
   `rfl`-based zero-case reduction.
5. Address E5 by replacing `rw [Nat.rec, ih]` with the
   canonical `Nat.rec` succ-unfolding pattern (or
   `change` / `show`).
6. Address E6 by adding `Nat.simRecVec_succ` to Task
   14.2's initial simp set.

After E1–E4 are fixed and E3, E5, E6 are addressed, the
plan should be coherent enough to enter implementation.
