# Step 3 spec adversarial review — round 2

## Summary

The round-1 fixes for findings F1, F3, F4 (spec side), F5/F6, F7, F8,
F9, F10, F11, F12 are correct.  However, **F2 is only partially
fixed**: §4.2's revised succ-case proof now adds the right
`pow_succ`-derived hypotheses (`h_succ1`, `h_succ2`,
`h_pow_ge_two`), but the closing `omega` still does not discharge
the goal.  Empirical verification with `lean_diagnostic_messages`
on a transcribed copy of the §4.2 proof confirms `omega` reports
"could not prove the goal", with the counterexample summary showing
that omega is treating `2 ^ (r + 1) * x` and `2 ^ r * x` as
unrelated atoms `b` and `c`.  The issue is that the succ-case goal
contains *nonlinear* products of opaque terms (`2 ^ (r + 1) * ctx 0`
vs `2 ^ r * ctx 0`), and a linear hypothesis `2 ^ (r + 1) = 2 * 2 ^ r`
cannot bridge them for omega — omega will not multiply that equality
by `ctx 0`.  An additional bridge `have h_mul_bridge : 2^(r+1) * ctx 0
= 2 * (2^r * ctx 0) := by rw [h_succ1]; ring` (or analogous) is
required, AND the closing tactic should be `omega` (with that
bridge).  An empirical proof of this shape was tested and passes.

Round-2 also identifies a new finding: the master-design touch-up
to §3.6 fixed the §0.1.0.4 catalogue entry but left the
**§0.1.0.17 (c)** bullet untouched at line 1185-1186, where it
still claims `ERMor1.expER = ERMor1.A_two`.  This is the same
type-inconsistent equation round-1 F4 flagged in §3.3; the
follow-up edit was only partial.

Total round-2 findings: 2 (1 substantive, 1 minor).

Recommendation: **round 3** — the round-3 cycle should be small
(one proof-tactic correction in §4.2 plus one master-design edit
to §3.6), but it must happen before the spec is ready for
implementation.  All other round-1 fixes have landed correctly.

## Round-1 fixes verified

### F1 (blocker): import list

**Status: correct.**  §2.1 now lists `GebLean.LawvereER`,
`GebLean.Utilities.ERArith`, `GebLean.LawvereERBoundComputable`,
`GebLean.LawvereERPolynomialBound`, and `GebLean.Utilities.Tower`.
Cross-checked against the actual modules:

- `ERMor1.succ`, `proj`, `comp` are constructors at
  `GebLean/LawvereER.lean:40-47`; their interp simp lemmas
  `interp_succ`, `interp_proj`, `interp_comp` at lines
  104-127.
- `ERMor1.addN` is at `GebLean/Utilities/ERArith.lean:42`;
  `interp_addN` at line 58.
- `ERMor1.towerER` and `interp_towerER` are at
  `GebLean/LawvereERBoundComputable.lean:230` and `240`.
- `ERMor1.PolyBound` is at
  `GebLean/LawvereERPolynomialBound.lean:42`.

All citations resolve.

### F2 (substantive): §4.2 succ-case proof

**Status: only partially fixed (substantive issue remains).**

The revised proof provides the three needed `have`s
(`h_succ1`, `h_succ2`, `h_pow_ge_two`) and drops the
`ring_nf` that round 1 flagged as ineffective on
`Nat`-truncating subtraction.  But the closing `omega`
will not discharge the goal.

Empirical verification: I transcribed the §4.2 succ-case proof
verbatim into a temporary file and asked the Lean LSP for
diagnostics.  The result was an `omega` error with the
counterexample summary:

```
omega could not prove the goal:
a possible counterexample may satisfy the constraints
  c ≥ 0
  b ≥ 0
  b - 2*c ≥ 1
  ...
where
 a := ↑2 ^ r
 b := ↑(2 ^ (r + 1)) * ↑x
 c := ↑(2 ^ r) * ↑x
```

The counterexample variables `b` and `c` show that omega
atomizes `2 ^ (r + 1) * ctx 0` and `2 ^ r * ctx 0` as
*independent* atoms.  The hypothesis `h_succ1 : 2 ^ (r + 1)
= 2 * 2 ^ r` is linear in `2 ^ r` and `2 ^ (r + 1)`, but
multiplying through by `ctx 0` to obtain
`2 ^ (r + 1) * ctx 0 = 2 * (2 ^ r * ctx 0)` is a nonlinear
manoeuvre omega does not perform.

I verified that an additional bridging hypothesis closes
the goal:

```lean
have h_mul_bridge :
    2 ^ (r + 1) * x = 2 * (2 ^ r * x) := by
  rw [h_succ1]; ring
omega
```

(Tested empirically — passes with no errors.)

Equivalently, the implementer could rewrite the goal first
via `rw [h_succ1, h_succ2]` and then close by `ring`, but
this requires that `ring` succeed on a `Nat` goal with
truncating subtraction — and as round-1 F11 / spec §9.6
correctly note, `ring`/`ring_nf` does NOT normalize
`Nat`-truncating subtraction.  I empirically verified the
`rw [h_succ2, h_succ1]; ring_nf; omega` chain also fails.
The robust path is the `h_mul_bridge` approach.

The spec's prose acknowledges this risk in §9.6 ("`omega`
does not handle `2 ^ r` symbolically … explicit
`pow_succ`-derived have-chain in §4.2's proof"), but the
have-chain shown in §4.2 is incomplete: it gives the linear
relations among `2 ^ r`, `2 ^ (r+1)`, `2 ^ (r+2)` but not
the multiplicative bridge needed for the goal's `2^(r+1) * x`
term.  The fix is small but substantive: add one more
`have` (the `h_mul_bridge` shown above), or document that
the implementer must supply such a bridge.

### F3 (substantive): §5.2 `Nat.mul_le_mul_left` chain

**Status: correct.**  §5.2 now has the chain
`h_ctx0_le_sup` → `h_ctx0_le_succ` (via `omega`) →
`h_mul := Nat.mul_le_mul_left _ h_ctx0_le_succ` →
`omega`.  Empirically verified that the final `omega`
closes the bound goal, since `2 ^ (r + 1) - 2` appears
identically on both sides of the inequality and the
`h_mul` hypothesis is linear in atoms `2^r * ctx 0` and
`2^r * (sup + 1)`.  No issue.

### F4 (minor): master-design `A_two = expER` correction

**Status: spec-side update is correct.**  §1.2 of the spec
adds the requested parenthetical and the §3.3 bullet of
the master design has been correctly rewritten.  However,
see new finding R2-N1 below: the corresponding §3.6
catalogue update is incomplete.

### F5/F6 (minor): `(0 : Fin 1)` form

**Status: correct.**  All occurrences of `⟨0, by decide⟩`
in §3.1, §3.2, §4.x, §5.x have been replaced with `0`
(relying on `OfNat (Fin 1) 0`).  The construction in §3.1
uses `ERMor1.proj (0 : Fin 1)` with explicit type
ascription; §3.2's `r = 0` base case uses
`ERMor1.proj (0 : Fin 1)`; the interp lemma RHSs use
`ctx 0`.  This matches existing codebase convention
(e.g. `interp_towerER` uses `ctx 0`, and `ofProj` uses
`Finset.le_sup (Finset.mem_univ _)` with `ctx i`).
Downstream simp-lemma reuse should work.

### F7 (substantive): `ofA_one_iter` docstring

**Status: correct.**  The docstring on line 366-379 of
the revised spec no longer contains the "loose by `2^r`"
claim; instead it correctly states "The constant slot is
matched exactly (no looseness there)" and "the bounds
proof reduces to a `Nat.mul_le_mul_left` step on the
leading-coefficient slot."  Mathematically accurate.

### F8 (minor): `#guard` cost prose

**Status: correct.**  §6.1 prose now reads "shallow, with
`bsum` reductions only at small bounds via `mulN`" instead
of the misleading "no bprod / no boundedRec" form.  §9.3
still mentions "no bprod" but in the right context (kernel
reduction terminates quickly).  Acceptable.

### F9 (minor): docstring discipline at §4

**Status: correct.**  §4 lead now contains "All theorems in
this section carry the docstring citations listed in §7"
explicitly.

### F10 (minor): §10 acceptance criteria

**Status: correct.**  §10 item 1 now lists module-docstring
requirements: "polynomial-vs-tower split paragraph that
explicitly documents the absence of `ofA_two_iter` (per §5.3)
and pointers to
`docs/research/2026-04-30-ksim-polynomial-bound-references.md`
and master design §3.3 (per §7)" plus per-entity
docstrings.

### F11 (substantive): §9 risks for `omega`/`ring_nf`

**Status: correct (as documentation), partial (as
implementation hint).**  §9.6 now correctly documents that
`omega` is opaque on `2 ^ r` and that `ring_nf` does not
normalize `Nat`-truncating subtraction.  This text is
accurate.  However, the §9.6 mitigation describes the
have-chain in §4.2 as sufficient; per F2 above, that have-
chain is incomplete (lacks the multiplicative bridge).  The
risk text is good documentation of *why* the proof needs
care; the §4.2 implementation hint is what falls short.

### F12 (minor): name-based references

**Status: correct.**  §3.3 now references "the existing
named composite `def ERMor1.towerER` in
`LawvereERBoundComputable.lean`" instead of "line 230".
§5.1 references "`def ERMor1.PolyBound.ofAddN` in
`LawvereERPolynomialBound.lean`".  No remaining line-number
citations in the spec.

## New findings (round 2)

### R2-S1 (substantive): §4.2 succ-case `omega` does not close

**Location:** §4.2 lines 271-296.

**Issue:** As detailed under "F2 verification" above, the
final `omega` call in the revised succ-case proof does not
discharge the goal.  Empirical verification with
`lean_diagnostic_messages` produced an explicit
counterexample summary showing omega atomizing the two
`* ctx 0` products as independent atoms.

**Proposed fix:** Insert a multiplicative bridge before the
closing `omega`:

```lean
| succ r ih =>
    unfold A_one_iter
    simp only [ERMor1.interp_comp, interp_A_one]
    have hcoll :
        (fun _ : Fin 1 =>
          (A_one_iter r).interp ctx) (0 : Fin 1)
          = (A_one_iter r).interp ctx := rfl
    rw [hcoll, ih]
    have h_succ1 : 2 ^ (r + 1) = 2 * 2 ^ r := by
      rw [pow_succ]; ring
    have h_succ2 : 2 ^ (r + 2) = 2 * 2 ^ (r + 1) := by
      rw [pow_succ]; ring
    have h_pow_ge_two : 2 ≤ 2 ^ (r + 1) := by
      rw [h_succ1]
      have : 1 ≤ 2 ^ r :=
        Nat.one_le_pow _ _ (by omega)
      omega
    have h_mul_bridge :
        2 ^ (r + 1) * ctx 0 = 2 * (2 ^ r * ctx 0) := by
      rw [h_succ1]; ring
    omega
```

The added `h_mul_bridge` is the linear equality between
the two `* ctx 0` atoms; with it, omega can close the
linear-arithmetic problem.

(Note: §9.6's prose already alerts the implementer to the
opacity of `2 ^ r` for omega, which is correct
documentation.  The fix here is to extend the have-chain
in §4.2 — and ideally update §9.6's mitigation to mention
that the bridge is *both* the linear relations *and* the
multiplicative bridge.)

### R2-N1 (minor): master-design §3.6 catalogue still has stale `expER = A_two` line

**Location:** Master design
`docs/research/2026-05-02-er-ksim2-equiv-via-urm-master-design.md`
line 1185-1186.

**Issue:** The round-1 commit's "Master-design touch-up"
log entry promises a §3.6 update.  The §0.1.0.4 catalogue
entry was correctly updated.  However, the
**§0.1.0.17 (c)** entry at line 1185-1186 still reads:

> **§0.1.0.17 (c) (`λx.2^x` ∈ K^sim_2)** — `ERMor1.expER =
> ERMor1.A_two`. Existing ✓.

This is the same type-inconsistent claim that round-1 F4
identified (no `ERMor1.A_two` definition exists or will be
shipped; `expER : ERMor1 2` is binary, not the unary
`λx. 2^x`).  The fix to §3.3 was applied; the parallel
fix to §3.6 was missed.

**Proposed fix:** Replace the §0.1.0.17 (c) bullet with:

> **§0.1.0.17 (c) (`λx.2^x` ∈ K^sim_2)** — realized by
> `A_two_iter 1` = `ERMor1.towerER 1` (since `tower 1 x =
> 2^x` per `Utilities/Tower.lean`).  No separate unary
> `ERMor1.A_two` exists; `ERMor1.expER : ERMor1 2`
> realizes the binary `λ(n,y). y^n`, not the unary form
> (see §3.3 Lean entities).

This aligns the catalogue with the §3.3 amendment.

## Items checked and confirmed correct (post-revision)

- §2.1 import list: all five imports resolve to actual
  modules and symbols at the cited names.
- §3.1 `A_one` construction: `addN(succ(proj 0), succ(proj 0))`
  is `(x+1)+(x+1) = 2x+2`, which interprets to
  `2 * (ctx 0) + 2`.  Construction matches existing pattern
  in `ofAddN` etc.
- §3.2 `A_one_iter` recursion direction
  (`comp A_one (fun _ => A_one_iter r)`): correctly
  documented as "apply r-fold first, then one more
  `A_one`" in §3.2 prose; matches the Lean code
  semantically (function composition is `f ∘ g = λx. f (g x)`).
- §4.1 `interp_A_one` proof: `unfold A_one; simp only [...];
  ring` should close (interpretation of the construction is
  pure-Nat addition without truncating subtraction; `ring`
  handles `(ctx 0 + 1) + (ctx 0 + 1) = 2 * ctx 0 + 2`).
  Spec also offers `omega` as fallback.
- §4.3 `interp_A_two_iter` proof: `unfold A_two_iter; exact
  ERMor1.interp_towerER r ctx` is a direct routing through
  the existing simp lemma.  Verified `interp_towerER`
  signature matches exactly.
- §5.1 `ofA_one`: bound shape `2 * (sup + 1) + 0` plus
  `ctx 0 ≤ sup`, leading to `2 * ctx 0 + 2 ≤ 2 * (sup + 1)`,
  which is `≤ 2 * sup + 2`.  Closes with `omega`.
- §5.2 `ofA_one_iter`: empirically verified that the
  revised proof's final `omega` closes given `h_mul`.
- §5.3 no `PolyBound.ofA_two_iter`: justification is
  correct; `tower r x` for `r ≥ 1` is super-polynomial.
- §6.1 tests: `A_one_iter 2 ![3] = 18` arithmetic correct
  (`2^2 * 3 + (2^3 - 2) = 12 + 6 = 18`).  Other guards
  also correct.
- §7 citation table: each public def/theorem in §3-§5 has a
  corresponding citation entry.  No orphans found in either
  direction.
- §8 step-4 hand-off list: items 1-8 cover everything
  master design §3.4 owes.
- §9 risks: §9.1-§9.7 cover the substantive risks; the
  prose at §9.6 is accurate as documentation (only the
  §4.2 implementation-hint mitigation is incomplete per
  R2-S1).
- §10 acceptance criteria: items 1-6 enumerate the
  deliverables completely.
- Master design §3.3 Lean-entities subsection: the
  rewrite from "`A_two = expER`" to "no separate unary
  `A_two` def" is mathematically accurate and properly
  reasoned.
- The transcription-discipline citations in spec §7 point
  at Tourlakis 2018 page 22 plus master design §3.3, and
  cross-reference
  `2026-04-30-ksim-polynomial-bound-references.md`.
  Citation discipline is satisfied.

## Recommendation

**Round 3, scope minimal.**  Two fixes required:

1. **R2-S1**: extend the §4.2 succ-case proof with a
   multiplicative bridge `have h_mul_bridge : 2^(r+1) * ctx 0
   = 2 * (2^r * ctx 0) := by rw [h_succ1]; ring`, and update
   §9.6's mitigation prose to mention that the bridge is
   needed in addition to the linear `pow_succ` rewrites.
2. **R2-N1**: update master-design §3.6 line 1185-1186 to
   replace the stale `ERMor1.expER = ERMor1.A_two` claim
   with the parallel form used in §0.1.0.4 ("realized by
   `A_two_iter 1`").

After these two edits, the spec is ready for
implementation.  All other round-1 findings have been
addressed correctly.
