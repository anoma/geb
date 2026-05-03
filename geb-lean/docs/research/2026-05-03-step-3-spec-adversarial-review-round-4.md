# Step 3 spec adversarial review — round 4

## Summary

**Approved.**

The three round-3 fixes have been correctly applied to the spec, the
proofs in §4.x and §5.x build cleanly with no warnings, and no new
defects were introduced.  No substantive items missed by earlier
rounds were located.

## Round-3 fixes verified

### R3-S1 (substantive): §4.2 succ-case `hcoll` rfl-rewrite removed

The §4.2 succ-case in the round-3 spec inserted `have hcoll : ...
:= rfl` followed by `rw [hcoll, ih]`; the round-3 reviewer found
that the preceding `simp only [..., interp_A_one]` had already
collapsed the inner `(fun _ => ...) 0` application, so the
`rw [hcoll, ...]` step had no occurrence to rewrite.

The current spec (post-1fa6fc3f) shows:

```lean
| succ r ih =>
    unfold A_one_iter
    simp only [ERMor1.interp_comp, interp_A_one]
    rw [ih]
    have h_succ1 : 2 ^ (r + 1) = 2 * 2 ^ r := by
      ...
```

The `hcoll` block is gone; `rw [ih]` stands alone.  The remaining
have-chain (`h_succ1`, `h_succ2`, `h_pow_ge_two`, `h_mul_bridge`,
closing `omega`) is unchanged from the round-2 form.  Fix correctly
applied.

### R3-S2 (substantive): §4.1 closing tactic swapped to `omega`

The §4.1 proof now closes with `omega` (not `ring`):

```lean
@[simp] theorem interp_A_one (ctx : Fin 1 → ℕ) :
    A_one.interp ctx = 2 * (ctx 0) + 2 := by
  unfold A_one
  simp only [ERMor1.interp_comp, ERMor1.interp_addN,
    ERMor1.interp_succ, ERMor1.interp_proj]
  omega
```

The parenthetical immediately following has been rewritten to
explain that `omega` is preferred because `ring` does not normalize
`Nat.succ` patterns left by the simp set.  Fix correctly applied.

### R3-N1 (minor): unused `pow_one` simp argument removed

The §4.2 zero-case `simp only [...]` argument list now reads
`[ERMor1.interp_proj, pow_zero, one_mul]` — `pow_one` is gone.
Fix correctly applied.

## Empirical Lean verification of §4 and §5 proofs

I transcribed the spec's §3.1 / §3.2 / §3.3 definitions and the
§4.1 / §4.2 / §4.3 / §5.1 / §5.2 proofs into a fresh Lean file
under `GebLean/Utilities/` (renamed to avoid colliding with any
future implementation), with imports matching §2.1, and ran
`lake build` against the resulting module.

Result: clean build, no errors, no warnings, no `sorry`, no
`admit`.  The build line was

```text
✔ [1288/1288] Built GebLean.Utilities.<...> (1.0s)
Build completed successfully.
```

All five definitions and all five proofs (three interp lemmas, two
PolyBound builders) closed exactly as written in the spec.  The
test file has been removed from the working tree (no commit was
made to the codebase as part of this review).

## Items checked

- §4.1 `interp_A_one` — closes with the stated tactic shape.
- §4.2 `interp_A_one_iter` — both zero and succ cases close with
  the stated tactic shape.
- §4.3 `interp_A_two_iter` — closes via `ERMor1.interp_towerER`.
- §5.1 `ofA_one` — closes with the stated `Finset.le_sup` +
  `omega` shape.
- §5.2 `ofA_one_iter` — closes with `Nat.mul_le_mul_left` +
  `omega`.
- §1.2 polynomial-vs-tower split prose, §5.3 absence-of-
  `ofA_two_iter` paragraph, §6.1 test-list `#guard`s, §7
  citations, §8 out-of-scope list, §9.x risks — all consistent
  with no internal contradiction.
- Citation discipline (CLAUDE.md transcription rules) — all
  public `def`/`theorem` names listed in §7 with literature
  references.  The cross-reference network points at master
  design §3.3 and the polynomial-bound research doc.
- Module-import list (§2.1) matches the imports needed by the
  empirical build.

## No new defects introduced

The R3 patch was three mechanical edits (drop `hcoll` block,
swap `ring` → `omega`, drop unused `pow_one`).  None of these
introduced new statement, no new term, and no new hypothesis;
each edit was strictly local.  Empirical build confirms the
edits are coherent with the surrounding proof structure.

## Findings missed by earlier rounds

None located.  The empirical build is the same check the
round-3 reviewer ran (per the round-3 report's "Items checked"
section), and it now succeeds end-to-end on the post-R3 spec.

## Recommendation

**Approve.**  The spec is clean of anything more than cosmetic
items.  Step 3 is ready to transition to plan-writing.
