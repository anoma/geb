# Step 3 spec adversarial review — round 3

## Summary

R2-N1 is correctly fixed.  R2-S1's intent is correctly captured (the
multiplicative bridge `h_mul_bridge` has been added and §9.6's
mitigation prose has been extended), and the empirical Lean LSP
verification confirms that `omega` does close the succ-case goal once
the bridge is in scope.  However, two new substantive defects were
introduced into the §4.2 proof during the round-2 patch, and one
pre-existing latent defect in §4.1 surfaces under the same empirical
verification:

- **R3-S1 (substantive, new):** §4.2's revised proof inserts
  `have hcoll : (fun _ : Fin 1 => (A_one_iter r).interp ctx)
  (0 : Fin 1) = (A_one_iter r).interp ctx := rfl` followed by
  `rw [hcoll, ih]`.  Empirically the `rw [hcoll, ...]` step
  fails: the immediately preceding `simp only [...,
  interp_A_one]` already collapses the inner `(fun _ => ...) 0`
  application via the closed-form rewrite, so by the time
  `hcoll` is introduced the LHS pattern it tries to rewrite no
  longer occurs in the goal.  The fix is to drop `hcoll`
  entirely and use just `rw [ih]`.  Verified empirically: with
  `hcoll` removed and `h_mul_bridge` retained, the entire §4.2
  succ-case proof closes with no errors or warnings.

- **R3-S2 (substantive, pre-existing but not previously
  flagged):** §4.1's proof closes with `ring`, with the spec
  noting parenthetically that "final implementation may use
  `omega` if `ring` does not close the residual `Nat`-arithmetic
  goal."  Empirically, `ring` does NOT close in Lean: after
  `simp only [..., ERMor1.interp_addN, ...]`, the residual goal
  is `(ctx 0).succ * 2 = 2 + ctx 0 * 2`, which `ring` cannot
  prove on `Nat` (the `Nat.succ` in the LHS is opaque to
  `ring`); `omega` closes immediately.  The spec correctly
  anticipates this as a fallback, but the primary tactic shown
  in the code block is the one that fails.  Recommend swapping
  the example to `omega` (and dropping the parenthetical to
  match), or at least flipping the prose so the working tactic
  is the primary suggestion.

- **R3-N1 (minor, new):** §4.2's `simp only [ERMor1.interp_proj,
  pow_zero, one_mul, pow_one]` zero-case argument list contains
  the unused `pow_one`; the linter warns
  `simp argument is unused: pow_one`.  Removing `pow_one` from
  the simp set is the correction.  This is below the
  no-warnings discipline threshold and the user has authorized
  fixing minor cosmetic items; it can be silently dropped during
  implementation.

The R3-S1 defect is in the verbatim §4.2 proof transcription, and
without the fix the proof does not type-check; this prevents
Step 3 from going to implementation as written.  The R3-S2 defect
is half-anticipated by the spec (omega is named as fallback) but
the lead-with-`ring` form invites a wasted iteration.  Both fixes
are tiny.

Recommendation: **one more revision pass** (small) to swap two
tactics and drop one simp argument, then approval.  All other
round-1 / round-2 findings are correctly addressed.

## Round-2 fixes verified

### R2-S1 (substantive): §4.2 succ-case `omega` does not close

**Status: bridging hypothesis correctly added; empirical
verification confirms `omega` closes the succ-case once the
bridge is in scope.**

The spec at §4.2 lines 295-298 now contains:

```lean
have h_mul_bridge :
    2 ^ (r + 1) * ctx 0 = 2 * (2 ^ r * ctx 0) := by
  rw [h_succ1]; ring
omega
```

I empirically verified by:

1. Constructing a complete temporary copy of the §4.2 proof
   (with the `hcoll` block REMOVED — see R3-S1 below) plus all
   the round-2 hypotheses.  `lean_diagnostic_messages` returned
   `success: true, items: []` — clean close.
2. As a control, removing only the `h_mul_bridge` hypothesis
   (keeping all of `h_succ1`, `h_succ2`, `h_pow_ge_two`).  The
   resulting `omega` call fails with the same atomization
   counterexample shape that round 2 reported: it treats
   `2 ^ (r + 1) * ctx 0` and `2 ^ r * ctx 0` as independent
   atoms `b` and `c`, with the linear relation among `2 ^ r`,
   `2 ^ (r + 1)` insufficient to bridge.

So the bridge is necessary and sufficient.  The §9.6 prose
addition correctly describes the bridge alongside the linear
`pow_succ` rewrites.  R2-S1 is closed.

### R2-N1 (minor): master-design §3.6 stale `expER = A_two` line

**Status: correctly fixed.**  The §3.6 §0.1.0.17 (c) catalogue
entry at master-design lines 1185-1190 now reads:

> **§0.1.0.17 (c) (`λx.2^x` ∈ K^sim_2)** — realized by
> `A_two_iter 1` = `ERMor1.towerER 1` (since
> `tower 1 x = 2 ^ x` per `Utilities/Tower.lean`).  No
> separate unary `ERMor1.A_two` exists; `ERMor1.expER :
> ERMor1 2` realizes the binary `λ(n, y). y ^ n`, not
> the unary form (see §3.3 Lean entities).

This matches the §0.1.0.4 catalogue form and the §3.3 Lean
entities subsection.  `grep` over the master design for `A_two`
(excluding `A_two_iter`) confirms the only remaining occurrences
are explicit "no separate `A_two`" disclaimers in §3.3 lines
815-824 and the §3.6 §0.1.0.17 (c) entry above; both are
narrative explanations that no such name exists, not stale
claims.  R2-N1 is closed.

## New findings (round 3)

### R3-S1 (substantive): §4.2 `hcoll` rewrite fails empirically

**Location:** §4.2 lines 281-285.

**Issue:** The succ-case proof inserts an `hcoll` step:

```lean
simp only [ERMor1.interp_comp, interp_A_one]
have hcoll :
    (fun _ : Fin 1 =>
      (A_one_iter r).interp ctx) (0 : Fin 1)
      = (A_one_iter r).interp ctx := rfl
rw [hcoll, ih]
```

After the preceding `simp only [..., interp_A_one]`, the
`(fun _ => (A_one_iter r).interp ctx) 0` application has
already been beta-reduced (and the surrounding `interp_A_one`
rewrite has fired), so the goal at the `rw [hcoll, ...]`
position is:

```text
2 * (A_one_iter r).interp ctx + 2
  = 2 ^ (r + 1) * ctx 0 + (2 ^ (r + 1 + 1) - 2)
```

The pattern `(fun _ => (A_one_iter r).interp ctx) 0` does not
appear here, so `rw [hcoll, ...]` fails with
`Tactic 'rewrite' failed: did not find an occurrence of the
pattern`.

Empirical verification: I transcribed the §4.2 proof verbatim
(plus the §3.x prerequisites) into a temporary file and asked
the Lean LSP for diagnostics.  The error reproduces.  Removing
the entire `hcoll` block and using just `rw [ih]` (which is
what the proof was attempting to do via `hcoll`'s redundant
beta) produces a clean close — confirmed `success: true,
items: []`.

**Proposed fix:** Replace the §4.2 succ-case block

```lean
| succ r ih =>
    unfold A_one_iter
    simp only [ERMor1.interp_comp, interp_A_one]
    have hcoll :
        (fun _ : Fin 1 =>
          (A_one_iter r).interp ctx) (0 : Fin 1)
          = (A_one_iter r).interp ctx := rfl
    rw [hcoll, ih]
    ...
```

with

```lean
| succ r ih =>
    unfold A_one_iter
    simp only [ERMor1.interp_comp, interp_A_one]
    rw [ih]
    ...
```

(All the remaining have-chain — `h_succ1`, `h_succ2`,
`h_pow_ge_two`, `h_mul_bridge`, and the closing `omega` —
remains unchanged and closes.)

This is a small fix, but it is in the literal proof text of the
spec, so without it Step 3 cannot proceed to implementation as
written.

### R3-S2 (substantive): §4.1 `ring` does not close

**Location:** §4.1 lines 252-258.

**Issue:** §4.1's interp_A_one proof reads

```lean
@[simp] theorem interp_A_one (ctx : Fin 1 → ℕ) :
    A_one.interp ctx = 2 * (ctx 0) + 2 := by
  unfold A_one
  simp only [ERMor1.interp_comp, ERMor1.interp_addN,
    ERMor1.interp_succ, ERMor1.interp_proj]
  ring
```

with a parenthetical "Tactic shape; final implementation may
use `omega` if `ring` does not close the residual
`Nat`-arithmetic goal."

Empirically, `ring` does NOT close.  `ERMor1.interp_addN`'s
RHS is `ctx 0 + ctx 1`, but after `simp only` fires through
the `succ`/`proj` slots, the residual goal Lean produces is

```text
(ctx 0).succ * 2 = 2 + ctx 0 * 2
```

— note the `Nat.succ` in the LHS arising from how the simp
set normalizes the `succ`-of-`succ` pattern.  `ring` rejects
this on `Nat` (it suggests `ring_nf`, which also doesn't
close on its own).  `omega` closes immediately.

Empirical verification: same temporary-file methodology.
With `ring`, error: `unsolved goals: ⊢ (ctx 0).succ * 2 =
2 + ctx 0 * 2`; with `omega`, clean.

**Proposed fix:** Either

(a) Replace `ring` with `omega` in the §4.1 code block.
    Drop or invert the parenthetical so the working tactic
    is primary.  Recommended.

(b) Add an explicit `change` step that introduces the
    canonical form `ring` can handle (more verbose,
    unnecessary).

Either way, the implementer following the spec verbatim with
`ring` will hit a failure on the very first proof of the
module, so the lead-with-`ring` form is misleading.  This is
half-anticipated by the parenthetical, but the failure-cost
is asymmetric: a working tactic costs nothing to prefer.

(Note: §9.6 anticipates `omega`-vs-`ring` issues for the
*succ-case* of §4.2; it does not mention §4.1.  §4.1's
parenthetical is the only protection.)

### R3-N1 (minor): unused `pow_one` simp argument in §4.2 zero-case

**Location:** §4.2 lines 274-276.

**Issue:** The zero-case proof reads

```lean
simp only [ERMor1.interp_proj, pow_zero, one_mul,
  pow_one]
```

The Lean linter reports `pow_one` as unused.  Removing it from
the simp set leaves the proof closing cleanly.

**Proposed fix:** Drop `pow_one` from the simp argument list:

```lean
simp only [ERMor1.interp_proj, pow_zero, one_mul]
```

Per the prompt this can be silently fixed during
implementation; flagging here for completeness.

## Items checked and confirmed correct (this round)

- §4.2 succ-case proof, with R3-S1 fix applied (drop `hcoll`)
  and `h_mul_bridge` retained: closes cleanly, no warnings.
  Empirically verified.
- §4.2 zero-case proof, with R3-N1 fix applied (drop
  `pow_one`): closes cleanly.  Empirically verified.
- §4.1 proof, with R3-S2 fix applied (`ring → omega`): closes
  cleanly.  Empirically verified.
- §5.1 `PolyBound.ofA_one` proof: with the §4.1 fix in place,
  the verbatim §5.1 code closes cleanly.  Empirically verified.
- §5.2 `PolyBound.ofA_one_iter` proof: with the §4.1 / §4.2
  fixes in place, the verbatim §5.2 code closes cleanly.
  Empirically verified.
- §4.3 `interp_A_two_iter` proof: pure routing through
  `ERMor1.interp_towerER`, no issues.
- Master design §3.6 §0.1.0.17 (c) catalogue entry, post-R2-N1.
- Master design §3.3 Lean-entities subsection (lines 800-824):
  the "no separate unary `A_two`" prose is consistent and
  cross-references §3.6 correctly.
- Master design `grep` for any remaining stale
  `A_two = expER` claim: only narrative disclaimers remain
  (lines 819-824 in §3.3, lines 1188-1190 in §3.6); both
  describe the absence of `A_two`, not its existence.
- §9.6 mitigation prose: now correctly enumerates
  (a) the linear `pow_succ` equalities,
  (b) the `Nat.one_le_pow` positivity hypothesis, and
  (c) the multiplicative bridge.  Matches the §4.2 have-chain
  the implementer must produce.
- §1.2 out-of-scope clarifying paragraph re `A_two`: aligned
  with §3.3 / §3.6 of the master design.
- §10 acceptance criteria: items 1-6 unchanged from round 2,
  still complete.
- §6.1 test guards: arithmetic checked
  (`2^2 * 3 + (2^3 - 2) = 18`, etc.).
- §7 citation table: complete; one-to-one with §3-§5 surface.

## Recommendation

**One more revision pass, scope minimal.**  Three edits, all
tiny:

1. **R3-S1**: drop the `hcoll` block from §4.2's succ-case
   proof; replace `rw [hcoll, ih]` with `rw [ih]`.  Retain
   the rest of the have-chain (`h_succ1`, `h_succ2`,
   `h_pow_ge_two`, `h_mul_bridge`, closing `omega`).
2. **R3-S2**: in §4.1, swap `ring` for `omega` and drop the
   "may use `omega` if `ring` does not close" parenthetical
   (or invert it so `omega` is primary).
3. **R3-N1**: drop `pow_one` from §4.2's zero-case
   `simp only` argument list.

After these edits the verbatim spec proofs all close cleanly
under empirical Lean LSP verification.  No other defects
identified.  Round 4 should be a pure clean-bill-of-health
pass after the three edits land.
