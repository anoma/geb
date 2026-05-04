# Step 4 plan adversarial review (round 2)

Plan under review:
`docs/superpowers/plans/2026-05-03-step-4-ksim-majorization.md`
(2228 lines, 22 tasks).
Round 1 reported 0 blockers, 12 majors, 13 minors, 5 nits.
This round audits the round-1 fixes and looks for newly
introduced risks.

The plan is in noticeably better shape than round 1.
Most of the round-1 majors are genuinely closed: tasks 18+19
are merged, task 16's `sorry`s are replaced with a single
trailing `_`, the `set stepCtx` indirection is dropped in
favor of a direct lambda inside `vMax_le_of_pointwise`, and
the γ.5 / Task 8 / Task 9 proofs are expanded into explicit
`calc` chains. One previous major (Task 14) survives in a
new form, however, and one new minor concern about
definitional reduction surfaces.

## Findings

### Finding 1

- Severity: major.
- Location: Task 14, Step 14.1 (`A_one_iter_compose`).
- Issue: the proof body still does not close. After
  three `interp_A_one_iter` rewrites and the substitutions
  `rw [h_pow_add, h_pow_succ_b, h_pow_succ_ab]`, the proof
  invokes `ring_nf` followed by `rw [h_pow_succ_a]` and a
  second `ring_nf; omega`. I verified this directly via
  `mcp__lean-lsp__lean_run_code`: the first `ring_nf`
  normalizes `2 ^ (a + 1)` to `2 ^ a * 2`, so the subsequent
  `rw [h_pow_succ_a]` raises
  `Tactic 'rewrite' failed: Did not find an occurrence
  of the pattern 2 ^ (a + 1)`.  Even with that rewrite
  removed, a bare `omega` cannot close — omega sees the
  three pow atoms `2^a`, `2^b`, `2^a * 2^b` as independent
  and the residual contains a Nat-truncating subtraction
  `(2^b * 2 - 2) * 2^a` whose distribution into
  `2^a * 2^b * 2 - 2^a * 2` requires `Nat.mul_sub` (or a
  manual `Nat.left_distrib`-with-cap argument) that neither
  `omega` nor `ring_nf` performs.
- Proposed fix: use the explicit `Nat.mul_sub` bridge.
  A confirmed-working chain (verified via lean-lsp):

```lean
  have hpa : 1 ≤ 2 ^ a := Nat.one_le_pow _ _ (by omega)
  have hpb : 1 ≤ 2 ^ b := Nat.one_le_pow _ _ (by omega)
  have h3 : 2 ^ (a + b) = 2 ^ a * 2 ^ b := Nat.pow_add 2 a b
  have h4 : 2 ^ (a + b + 1) = 2 * (2 ^ a * 2 ^ b) := by
    rw [Nat.pow_succ, h3]; ring
  have h5 : 2 ^ (b + 1) = 2 * 2 ^ b := by
    rw [Nat.pow_succ]; ring
  have h6 : 2 ^ (a + 1) = 2 * 2 ^ a := by
    rw [Nat.pow_succ]; ring
  rw [h3, h4, h5, h6]
  have hdist :
      2 ^ a * (2 ^ b * x + (2 * 2 ^ b - 2))
        = 2 ^ a * 2 ^ b * x + 2 ^ a * (2 * 2 ^ b - 2) := by
    ring
  rw [hdist]
  have hbridge :
      2 ^ a * (2 * 2 ^ b - 2)
        = 2 * (2 ^ a * 2 ^ b) - 2 * 2 ^ a := by
    rw [Nat.mul_sub _ (2 * 2 ^ b) 2]
    ring_nf
  rw [hbridge]
  have h2ab_ge : 2 * 2 ^ a ≤ 2 * (2 ^ a * 2 ^ b) := by
    apply Nat.mul_le_mul_left
    nlinarith
  omega
```

  This is significantly longer than the current draft.
  An alternative is to prove `A_one_iter_compose` by
  induction on `a` (the outer iterate), which avoids the
  Nat-subtraction-distribution barrier entirely; that
  recursion is exactly the shape of `A_one_iter`'s `succ`
  case in `interp_A_one_iter`.

### Finding 2

- Severity: minor.
- Location: Task 18, Step 18.1 (`raise` case,
  `h_p2_zero : p.2 = 0 := rfl`).
- Issue: `KMor1.majorize_one` is defined non-recursively as
  `fun f h => let p := KMor1.linearBound f h; let r := ...;
  (r, 0)`. So `(KMor1.majorize_one f hf).2` reduces by
  `def` unfolding through the two `let`-bindings to `0`,
  and `rfl` should suffice. The risk is reducibility: a
  `def` (vs `@[reducible] def` or `abbrev`) is reducible
  for `rfl` only with `@[reducible]` or full unfolding.
  `Prod.snd (r, 0) = 0` is `iota`-reducible regardless,
  but `(KMor1.majorize_one f hf).2` first has to unfold
  `KMor1.majorize_one` which is a `def`. Lean 4's definitional
  equality does unfold non-recursive `def`s, so `rfl` should
  work, but if it doesn't, the fallback is
  `by unfold KMor1.majorize_one; rfl`.
- Proposed fix: pre-specify the fallback so a subagent
  doesn't burn an iteration. Either change the line to
  `by unfold KMor1.majorize_one; rfl` up front, or leave
  the comment "(if `rfl` fails, fall back to
  `by unfold KMor1.majorize_one; rfl`)".

### Finding 3

- Severity: minor.
- Location: Task 16, Step 16.3 (succ case, trailing `_`).
- Issue: the proof builds `h_prev_le_M`, `set M := ...`,
  and `h_stepCtx_bound`, then leaves a single `_` to be
  filled in by the implementer with the chain
  "`g_fam j` interp at stepCtx → A_1^r_G(vMax stepCtx) →
  A_1^r_G(A_1^{r_H+n·r_G}(M)) → A_1^{r_G + r_H + n·r_G}(M)
  → A_1^{r_H + (n+1)·r_G}(max (n+1) (vMax params))".
  The plan describes this in prose but does not write the
  Lean. With `apply` followed by `vMax_le_of_pointwise; intro
  idx; by_cases h₁`, the goal after the inline `h_stepCtx_bound`
  block is a residual `... ≤ A_1^{r_H + (n+1)·r_G}(max (n+1) ...)`
  shape. A subagent will face the load-bearing chain at the
  trailing `_` with only an English summary as guidance.
  Per CLAUDE.md `_`-discipline this is acceptable, but it is
  the largest single remaining hole in the plan and merits
  pre-specifying the actual Lean expression (or factoring
  into a private named lemma `simrecVec_step_apply`).
- Proposed fix: replace the trailing `_` with the explicit
  Lean chain. Approximate shape:

```lean
      calc (g_fam j).interp (fun idx => ...)
          ≤ (ERMor1.A_one_iter r_G).interp
              ![vMax (fun idx => ...)] := hstep j _
        _ ≤ (ERMor1.A_one_iter r_G).interp
              ![(ERMor1.A_one_iter (r_H + n * r_G)).interp ![M]]
              := by
            rw [ERMor1.interp_A_one_iter,
                ERMor1.interp_A_one_iter]
            -- monotonicity in the input slot
            simp only [Matrix.cons_val_zero]
            have h_pow_pos : 1 ≤ 2 ^ r_G :=
              Nat.one_le_pow _ _ (by omega)
            have h_mul := Nat.mul_le_mul_left (2 ^ r_G)
              h_stepCtx_bound
            omega
        _ = (ERMor1.A_one_iter (r_G + (r_H + n * r_G))).interp
              ![M] := A_one_iter_compose r_G (r_H + n * r_G) M
        _ = (ERMor1.A_one_iter (r_H + (n + 1) * r_G)).interp
              ![M] := by
            congr 1; ring
        _ ≤ (ERMor1.A_one_iter (r_H + (n + 1) * r_G)).interp
              ![max (n + 1) (vMax params)] := by
            ...
```

  Confirming this chain's `omega` step closes will require
  the same kind of reducibility hygiene as Finding 1 — which
  is why pre-writing it (rather than leaving a `_`) is
  worth doing in the plan.

### Finding 4

- Severity: minor.
- Location: Task 18, Step 18.1 (simrec case `change` step).
- Issue: I verified
  `(fun j => v (Fin.succ j)) = Fin.tail v := rfl`
  passes (lean-lsp confirmed). The `change` step is sound.
  But `change` operates on the goal, and after
  `simp only [KMor1.majorize, KMor1.interp_simrec]` the
  goal contains `KMor1.simrecVec h_fam g_fam (fun j => v
  (Fin.succ j)) (v 0) i ≤ ...` where the RHS is the
  full unfolding of `KMor1.majorize`'s simrec branch
  (atomic `(2, r_H + r_G + 2)` per Task 17). The `change`
  has to match that RHS exactly. The plan writes
  `change ... ≤ _` with `_` for the RHS, which delegates
  RHS-matching to elaboration. Should work, but if Lean's
  elaborator can't infer the RHS underscore, the implementer
  needs to spell it out.
- Proposed fix: monitor; not a hard issue.

### Finding 5

- Severity: minor.
- Location: Task 18, Step 18.1 (comp case `tower_compose_offsets`
  application, line 1748–1749).
- Issue: the `calc` step writes
  `_ ≤ tower (p_f.1 + r_g) (vMax v + o_g + p_f.2)
        := tower_compose_offsets _ _ _`. The
  `tower_compose_offsets` lemma (Task 8) has signature
  `{a b : ℕ} (x c d : ℕ) :
   tower a (tower b (x + c) + d) ≤ tower (a + b) (x + c + d)`.
  Applied with `a := p_f.1`, `b := r_g`, `x := vMax v`,
  `c := o_g`, `d := p_f.2`, it gives
  `tower p_f.1 (tower r_g (vMax v + o_g) + p_f.2) ≤
   tower (p_f.1 + r_g) (vMax v + o_g + p_f.2)`. The previous
  calc step ended with
  `tower p_f.1 (tower r_g (vMax v + o_g) + p_f.2)`, so this
  matches. Implicit args might need explicit hints; the
  three underscores stand for `x`, `c`, `d` and Lean should
  infer them from the goal. OK.
- Proposed fix: none. Verify on first build.

### Finding 6

- Severity: minor.
- Location: Task 8, Step 8.1 (inline
  `by omega : 1 + d ≤ 2 ^ d`).
- Issue: I verified that with `h_pow_ge : d + 1 ≤ 2 ^ d` in
  scope, `by omega` closes `1 + d ≤ 2 ^ d` — `omega` picks
  up `h_pow_ge` and reorders. So the inline tactic block
  sees `h_pow_ge` from the surrounding context. Confirmed
  closes via lean-lsp.
- Proposed fix: none.

### Finding 7

- Severity: minor.
- Location: Task 13, Step 13.1 (`h_int` subgoal).
- Issue: I verified the round-1 fix
  `rw [h_expand]; omega` closes — even though the expansion
  contains products `r_H * m`, `m * r_G`, omega treats them
  as atoms and the residual goal
  `r_H + m * r_G + 1 ≤ r_H * m + r_H + m * r_G + r_G + m + 1`
  reduces to `0 ≤ r_H * m + r_G + m`, which omega proves
  directly. Confirmed via lean-lsp.
- Proposed fix: none.

### Finding 8

- Severity: minor.
- Location: Task 13, Step 13.1 (two embedded `nlinarith`
  calls in calc steps).
- Issue: I verified
  `(r_H + r_G + 1) * (m + 1) + (m + 1) ≤ (r_H + r_G + 2) * (m + 1)`
  closes by `nlinarith` (lean-lsp confirmed). The other
  `nlinarith` step `(r_H + r_G + 1) * (m + 1) ≤
  (r_H + r_G + 2) * (m + 1)` also closes by `nlinarith`.
  Both pass.
- Proposed fix: none.

### Finding 9

- Severity: minor.
- Location: Task 18, Step 18.1 (multiple `set` blocks).
- Issue: the comp branch sets `p_f`, `r_g`, `o_g`; the
  simrec branch sets `r_H`, `r_G`. Each `set ... with hX`
  creates a binding plus a hypothesis for unfolding. The
  total scaffolding in this branch reaches ~80 lines per
  case, which approaches the ~80-line factoring threshold
  the plan flags in Step 16's prose. The comp+simrec
  combined form is ~150 lines. Splitting into private
  lemmas (`comp_dominance`, `simrec_dominance`) per Step 16's
  fallback advice would help readability and incremental
  build feedback for subagents.
- Proposed fix: documentation-level note. The plan
  acknowledges the option in Step 16 but does not extend
  it to Step 18. Consider adding the same factoring
  guidance to Step 18's prose.

### Finding 10

- Severity: minor.
- Location: Task 11, Step 11.1 (final `tower 2 (x + k + 2)`
  closure).
- Issue: round 1's Finding 14 fix moves to
  `simp only [tower_succ, tower_zero]` at the end.
  Verified that `tower 2 y = 2 ^ tower 1 y =
  2 ^ (2 ^ tower 0 y) = 2 ^ (2 ^ y)` reduces by rfl-simp.
  The `simp only` invocation should close
  `2 ^ (2 ^ (x + k + 2)) = tower 2 (x + k + 2)` directly.
  OK.
- Proposed fix: none.

### Finding 11

- Severity: minor.
- Location: Task 16, Step 16.2 (base case).
- Issue: round 1's Finding 1 fix uses
  `rw [KMor1.simrecVec_zero]` followed by
  `simp only [Nat.zero_mul, Nat.add_zero]` and `omega` for
  `max 0 (vMax params) = vMax params`. The chain is sound
  and idiomatic. OK.
- Proposed fix: none.

### Finding 12

- Severity: minor.
- Location: Task 18, Step 18.1 (raise case
  `h_input_eq` step).
- Issue: the line
  `have h_input_eq : vMax v + p.1 + 2 = vMax v + (p.1 + 2)
   := by ring` is correct for `Nat`. `ring` over `ℕ` handles
  associativity. Followed by `rw [h_input_eq] at h_cross`
  reshapes `A_two_iter 2 ![vMax v + p.1 + 2]` to
  `A_two_iter 2 ![vMax v + (p.1 + 2)]`, matching the goal's
  RHS shape. OK.
- Proposed fix: none.

### Finding 13

- Severity: minor.
- Location: Task 17, Step 17.1 (simrec branch).
- Issue: round 1's Finding 21 noted that the `def` ignores
  `i`. The plan retains
  `| _, .simrec _ h_fam g_fam, hyp =>` with `_` for the
  selector. Step 18's simrec proof binds `i` as
  `| _, .simrec i h_fam g_fam, hyp, v => ...`. The `def`
  does not depend on `i`, so the underscore is fine. The
  `theorem`'s `i` is needed for the goal `simrecVec ... i`.
  The two patterns must agree on the `KMor1` arity
  (`majorize` and `majorize_by_A_two_iter` both pattern
  on the same constructor shape); this works because
  `_` and `i` both bind a single argument slot.
- Proposed fix: none.

### Finding 14

- Severity: minor.
- Location: Task 21 (test module).
- Issue: the test file's two `example` proofs spell out
  `(Finset.univ : Finset (Fin a)).sup (![...] : Fin a → ℕ)`
  to substitute for the private `vMax` abbrev. This works
  but is verbose. Alternative: export `vMax` (drop
  `private`) so tests read more naturally. The plan picks
  privacy on `vMax`, which is the right default — keeping
  the test module's verbose form is acceptable. No change
  needed.
- Proposed fix: none.

### Finding 15

- Severity: nit.
- Location: throughout the plan (privacy consistency).
- Issue: round 1's Finding 26 raised privacy inconsistency.
  The round-2 plan does not appear to have applied a
  consistent rule (γ-lemmas remain public,
  `vMax_*`/`tower_*` private). This matches the spec's
  intent but is a judgment call. Cosmetic.
- Proposed fix: none. Round 1's Finding 26 stands.

### Finding 16

- Severity: nit.
- Location: Self-review section, line 2197.
- Issue: the self-review still says
  `KMor1.majorize_by_A_two_iter → Tasks 18 + 19`,
  but Tasks 18 and 19 are merged into a single Task 18 in
  the round-2 plan. The self-review text is stale.
- Proposed fix: change to
  `KMor1.majorize_by_A_two_iter → Task 18`. Also update
  the placeholder-scan paragraph (line 2204) which says
  "Tasks 16 and 18-19 use `_` placeholders" to "Tasks 16
  and 18 use `_` placeholders".

### Finding 17

- Severity: nit.
- Location: Task 22, Step 22.2 (markdownlint command).
- Issue: the command lists round-1 and round-2 spec review
  files but not the round-1 plan review file
  (`docs/research/2026-05-03-step-4-plan-adversarial-review-round-1.md`).
  When the plan-review-round-2 file lands (this file), it
  also needs to be added.
- Proposed fix: extend the markdownlint argument list to
  include both plan-review-round-1 and -round-2 docs.

## Summary

- Blockers: 0.
- Majors: 1 (Finding 1 — Task 14's `A_one_iter_compose`
  proof still does not close as written).
- Minors: 11 (Findings 2–12).
- Nits: 3 (Findings 15–17).

Mergeability: the plan is in much better shape than round 1.
Eleven of the twelve round-1 majors are genuinely closed.
The remaining major (Task 14) is a real proof-engineering
issue that a subagent will hit on first build and burn 1–2
iterations resolving without pre-specified guidance. The
recommended path is to either (a) inline the `Nat.mul_sub`
bridge proof shown in Finding 1, or (b) reproof
`A_one_iter_compose` by induction on `a` (using
`interp_A_one_iter`'s succ-case shape directly), which
sidesteps the truncating-subtraction distribution.

Finding 3 (Task 16's trailing `_`) is the next biggest
risk for execution time but qualifies as minor under
CLAUDE.md's `_`-discipline; pre-specifying the chain in
the plan would still save a subagent dispatch.

The other minors are mostly definitional-reducibility
flags and consistency notes that a subagent will resolve
in seconds during incremental build feedback.

Round 2 verdict: the plan is dispatchable to subagents
once Finding 1 is fixed. The other findings are
judgment-call cleanups that do not block execution.
