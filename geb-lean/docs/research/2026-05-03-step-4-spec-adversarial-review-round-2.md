# Step 4 Spec — Adversarial Review, Round 2

Adversarial review of the revised
`docs/superpowers/specs/2026-05-03-step-4-ksim-majorization-design.md`
after round-1 fixes. The five round-1 blockers and four
round-1 majors are genuinely closed by the revisions; the
new content (§4.5 parametric γ-lemma, the
`majorize_one`-zero-offset shape in §5.2 and §6.2, the
`fun _ : Fin 1 => ...` ascription in §7) checks out
arithmetically and at the type level. Remaining findings
are minor or nit-level.

## Findings

### 1. §4.5 chain skips the `(M = m)` substitution justification

- **Severity**: minor.
- **Location**: §4.5 proof outline, lines 404–412.
- **Issue**: the chain's first line writes
  `A_1^{r_H + m·r_G}(m) ≤ 2^{r_H + m·r_G + 1} · (m + 1)`
  citing γ.2 (§4.2). γ.2 reads
  `A_1^k(x) ≤ 2^{k+1} · (x + 1)`. The substitution
  `k := r_H + m·r_G`, `x := m` is correct, but the
  spec's `m` plays two roles in the result line — it
  appears in the exponent `r_H + m·r_G + 1` AND in the
  factor `(m + 1)`. Implementers may mis-read the role
  duplication. No mathematical bug; `omega` plus the γ.2
  rewrite handles it, but the proof outline should
  spell out the substitution explicitly to remove the
  ambiguity.
- **Proposed fix**: rewrite the outline's first chain
  line as
  `A_1^k(m) ≤ 2^{k+1} · (m + 1)` with `k := r_H + m·r_G`,
  followed by substitution. Verifies the boundary cases
  (`r_H = r_G = 0`, `m = 0`, `r_G = 0, r_H ≥ 1`) all go
  through without slack, since at each the integer
  inequality `r_H + m·r_G + 1 ≤ (r_H + r_G + 1)·(m + 1)`
  attains equality only at the corner `r_G = m = 0` —
  fine for a `≤` chain.

### 2. §4.5 step "k ≤ 2^k" applied at non-trivial value

- **Severity**: nit.
- **Location**: §4.5 outline line 409.
- **Issue**: the chain step
  `2^{(r_H + r_G + 1) · 2^{m+1}} ≤ 2^{2^{r_H + r_G + 1} · 2^{m+1}}`
  uses `r_H + r_G + 1 ≤ 2^{r_H + r_G + 1}`, citing
  `Tower.le_two_pow_self`. Edge case at
  `r_H = r_G = 0`: `1 ≤ 2^1 = 2`, fine. The proof
  outline's `(k ≤ 2^k)` parenthetical does not name
  `Tower.le_two_pow_self` explicitly; readers may
  search for `Nat.lt_two_pow_self` instead (which is
  the strict version in mathlib). Pinning the lemma
  avoids confusion.
- **Proposed fix**: in §4.5's hint list, replace
  `(k ≤ 2^k)` with `(le_two_pow_self (r_H + r_G + 1))`.

### 3. §6.2 succ-case missing `n ≤ A_1^k(...)` step

- **Severity**: minor.
- **Location**: §6.2 step bullet, lines 624–633.
- **Issue**: the step bullet says "Bound vMax of the
  concatenated context by IH (for prev-slots) and
  `n ≤ max (n+1) (vMax params)` (for counter and
  params slots). Apply `hstep j`. Compose with IH via
  `A_one_iter_compose`." The master design's prose
  proof (lines 999–1007) handles the corresponding
  `n ≤ M_n` step by `A_1^k(y) ≥ y` followed by
  monotonicity. The spec's outline omits this
  intermediate step: passing from
  `A_1^{r_G}(max(n, M_n))` to
  `A_1^{r_G}(M_n) = A_1^{r_G}(A_1^{r_H + n·r_G}(...))`
  requires `n ≤ A_1^{r_H + n·r_G}(max n (vMax params))`,
  which uses `self_le_A_one_iter`-style monotonicity.
- **Proposed fix**: in §6.2's step bullet, add an
  explicit sub-step "use `n ≤ max(n, vMax params) ≤
  A_1^{r_H + n·r_G}(max(n, vMax params))` (the latter
  via the monotonicity `x ≤ A_1^k(x)` derivable from
  the closed form: `2^k · x + (2^{k+1} − 2) ≥ x`)". Or
  cite an explicit auxiliary lemma `self_le_A_one_iter`
  if one is to be added to §6.4's auxiliary list.

### 4. §6.4 `tower_add_offset_le` chain skips a step

- **Severity**: minor.
- **Location**: §6.4 fourth bullet, lines 701–713.
- **Issue**: the inductive proof outline says "At
  `b + 1`: by IH ..., so by monotonicity of `(2 ^ ·)`
  ... using `2^d ≥ d + 1` (from `Nat.lt_two_pow_self`)
  at the first step (with the trivial `d = 0` edge
  case as equality)." The actual chain
  `2^(tower b x) + d ≤ 2^(tower b x) · 2^d` requires
  `d ≤ 2^(tower b x) · (2^d − 1)`. At `d = 0`: `0 ≤ 0`,
  fine. At `d ≥ 1, tower b x = 0` (achievable at
  `b = 0, x = 0`): need `d ≤ 1 · (2^d − 1) = 2^d − 1`,
  i.e. `d + 1 ≤ 2^d`. True for `d ≥ 1`. At
  `d ≥ 1, tower b x ≥ 1`: `d ≤ 2^N · (2^d − 1)` with
  `N ≥ 1` and `2^d − 1 ≥ 1`, so RHS `≥ 2`, need
  `d ≤ 2^N · (2^d − 1)`. Holds. The proof outline's
  hand-wave "`2^d ≥ d + 1`" is the right bound but
  needs to be applied as
  `2^(tower b x) + d ≤ 2^(tower b x) · 2^d`, not
  `2^(tower b x) + d ≤ 2^(tower b x) + (2^d − 1)`.
  The two are different; the chain skips the algebraic
  step.
- **Proposed fix**: spell out the multiplicative step
  `2^N + d ≤ 2^N · 2^d` for `N ≥ 0, d ≥ 0` as a
  separate sub-lemma (or as an inline `have`), proved
  by case-splitting on `d` (`d = 0`: equality;
  `d ≥ 1`: `2^N · 2^d − 2^N = 2^N · (2^d − 1) ≥
  2^N · d ≥ d`).

### 5. §6.3 simrec `vMax_cons` needs `Fin.cons_self_tail`

- **Severity**: minor.
- **Location**: §6.3 simrec bullet, lines 673–686.
- **Issue**: per `KMor1.interp_simrec` (in
  `LawvereKSimInterp.lean` line 167–170), the simrec's
  interpretation is
  `simrecVec h g (fun j => ctx (Fin.succ j)) (ctx 0) i`,
  i.e. `params = Fin.tail v` and recursion variable
  `= v 0`. The §6.3 outline writes "Note `max m
  (vMax_params) = vMax v` (using `vMax_cons` from
  §6.4)". `vMax_cons`'s statement is
  `vMax (Fin.cons n v) = max n (vMax v)`. Applying
  this requires `v = Fin.cons (v 0) (Fin.tail v)`,
  which is true definitionally (`Fin.cons_self_tail`
  in mathlib, or by `funext` + `Fin.cases`). The spec
  doesn't surface this rewriting step.
- **Proposed fix**: in §6.3, add a sentence
  "use `Fin.cons_self_tail` (or equivalent) to rewrite
  `v = Fin.cons (v 0) (Fin.tail v)`, then
  `vMax_cons`". Add `Fin.cons_self_tail` to §6.4's
  auxiliary list if mathlib's name differs from what
  the codebase has scope for.

### 6. §6.3 simrec needs `A_one_iter` monotonicity in `k`

- **Severity**: minor.
- **Location**: §6.3 simrec bullet, lines 681–684.
- **Issue**: the outline jumps from
  `simrec.interp v ≤ A_1^{r_H + (v 0)·r_G}(vMax v)`
  to applying §4.5 at `m := vMax v`. To do this, it
  must first lift the exponent: `r_H + (v 0)·r_G ≤
  r_H + (vMax v)·r_G` (using `v 0 ≤ vMax v`), and the
  input `vMax v` already matches §4.5's `m`. The
  exponent lift uses `A_1^k` monotonicity in `k`
  (the `A_one_iter` family is monotone in the
  iteration count for fixed input — provable from the
  closed form). The spec doesn't state this
  monotonicity lemma anywhere; §6.4's auxiliary list
  doesn't include it.
- **Proposed fix**: add `A_one_iter_mono_left :
  ∀ {x : ℕ} {k₁ k₂ : ℕ}, k₁ ≤ k₂ →
  (A_one_iter k₁).interp ![x] ≤ (A_one_iter k₂).interp ![x]`
  to §6.4's auxiliary list. Provable from
  `interp_A_one_iter`'s closed form plus
  `Nat.pow_le_pow_right`.

### 7. §5.2 docstring framing about elided `o_H`/`o_G`

- **Severity**: nit.
- **Location**: §5.2 lines 537–542.
- **Issue**: the docstring states "`majorize_one`
  always returns `(r, 0)` ..., so the `o_H` and `o_G`
  terms that would otherwise appear in the
  accumulation are identically zero." Correct, since
  `majorize_one` (§5.1) literally returns `(r, 0)`.
  However the §5.2 def code does NOT compute an `o_H`
  / `o_G` foldr — it omits the `.2` accumulation
  entirely. The docstring's framing implies an
  accumulation that the code skips. Minor confusion,
  no bug.
- **Proposed fix**: rephrase docstring as
  "`majorize_one` always returns `(r, 0)`; the offset
  accumulation simplifies to `0` and is therefore
  elided from the `Fin.foldr` chain entirely."

### 8. §7 `interp` reduction needs pointwise-constant step

- **Severity**: minor.
- **Location**: §7 proof outline, lines 745–751.
- **Issue**: the outline says "unfold via
  `interp_comp`, `interp_A_two_iter`,
  `interp_sumCtxERPlusOffset`. RHS becomes
  `tower (majorize.1) ((∑ i, v i) + majorize.2)`."
  The intermediate step
  `(comp (A_two_iter p.1) (fun _ : Fin 1 => sumCtxERPlusOffset a p.2)).interp v
   = (A_two_iter p.1).interp (fun i => (sumCtxERPlusOffset a p.2).interp v)
   = (A_two_iter p.1).interp ![∑ j, v j + p.2]`
  requires that `fun i : Fin 1 => (sumCtxERPlusOffset a p.2).interp v`
  reduces to `![∑ j, v j + p.2]` (a `Fin 1 → ℕ`
  function with single value `(∑ j, v j) + p.2`). At
  `i = 0` this is `(∑ j, v j) + p.2`; the function is
  pointwise constant. `interp_A_two_iter` then
  reduces to `tower p.1 ((∑ j, v j) + p.2)` via the
  `ctx 0` argument. The spec's outline omits this
  pointwise-constant step; the implementer must
  insert `funext` or `Fin.eq_zero` reasoning.
- **Proposed fix**: in §7's proof outline, add a
  sentence: "the inner `fun _ : Fin 1 => ...` is
  pointwise-constant, so its image under `interp` is
  the constant function `Fin 1 → ℕ` whose value at
  `0` is `(∑ j, v j) + p.2`; pass this through
  `interp_A_two_iter`'s `ctx 0` slot."

### 9. §8 `example` test elaboration cost

- **Severity**: minor (runtime).
- **Location**: §8.1 lines 805–817.
- **Issue**: the `example` proofs invoke
  `KMor1.majorize addK (by decide)` which produces
  `(2, p.2)` for some `p.2` value computed by
  structural recursion through `majorize_one` plus
  `linearBound`. `linearBound`'s evaluation at `addK`
  itself requires `level0Shape` invocations that
  unfold `Finset.univ.sup` over `Fin (k+1)`. The
  test docstring (§8.1 lines 822–826) reasons that
  the example's RHS `tower 2 (...)` is not forced —
  fine, the example bypasses it via
  `majorize_by_A_two_iter`. But the LHS arguments to
  the theorem at the call site (`KMor1.majorize addK
  (by decide)`) ARE evaluated by the elaborator to
  produce a `(r, offset) : ℕ × ℕ`; that evaluation
  cost is where finding 14 of round 1 was concerned.
  At the type level, this is a mere `ℕ × ℕ` literal,
  so reduction should terminate quickly — the
  potentially expensive part (kernel-evaluating
  `tower 2 (...)` to a Nat literal) is indeed
  bypassed. The risk is that the theorem's RHS
  expressions in the `example` must be
  definitionally equal to the elaborated expressions
  for the proof to typecheck without `decide`-heavy
  reasoning, and the `vMax` and `KMor1.majorize`
  computations inside `![...]` might force kernel
  evaluation of intermediate `Finset.univ.sup` calls
  that are slow but tractable.
- **Proposed fix**: at task-1 implementation time,
  benchmark the `example`'s elaboration; if it
  exceeds a reasonable time bound (~2s), bind the
  `(KMor1.majorize addK (by decide))` to a local
  `let p := ...` once and reference `p.1`, `p.2`
  throughout, to avoid re-evaluation.

### 10. §5.2 `comp` case `o_g` accumulation

- **Severity**: minor.
- **Location**: §5.2 lines 498–501.
- **Issue**: the comp case computes
  `o_g := Fin.foldr _ (fun i acc => max acc
  (KMor1.majorize (gs i) (hgs i)).2) 0` and outputs
  `(p_f.1 + r_g, p_f.2 + o_g)`. The dominance proof
  (§6.3 comp bullet) needs each child's offset to
  satisfy `(gs i).interp v ≤ A_2^{r_g}(vMax v + o_g)`
  after the foldr-max lift; this requires bounding
  each child's offset by `o_g` (via
  `Fin.foldr_max_ge` on the `.2` slot). The spec's
  §6.3 mentions `Fin.foldr_max_ge` only once, in the
  comp context, but does not specify its application
  to BOTH the `.1` and `.2` slots. With `Fin.foldr`
  reused twice (once for `r_g`, once for `o_g`), the
  proof needs `Fin.foldr_max_ge` for both — a single
  lemma applied at two different child accessors.
- **Proposed fix**: in §6.3's comp bullet, clarify
  that `Fin.foldr_max_ge` is invoked once per
  per-child quantity (`.1` and `.2`), each producing
  the upper bound needed for the subsequent
  `tower_mono_*` application.

### 11. §6.4 `tower_compose_offsets` redundant `c` parameter

- **Severity**: nit.
- **Location**: §6.4 last bullet, lines 714–720.
- **Issue**: the lemma signature is
  `tower a (tower b (x + c) + d) ≤ tower (a + b) (x + c + d)`.
  In §6.3's comp application, the call site is
  `tower p_f.1 (tower r_g (vMax v + o_g) + p_f.2) ≤
   tower (p_f.1 + r_g) (vMax v + o_g + p_f.2)`,
  matching `a := p_f.1, b := r_g, x := vMax v,
  c := o_g, d := p_f.2`. The `c` parameter is
  redundant — replacing `x + c` by a single `x'`
  yields the same lemma. Carrying `c` separately is
  fine (it forwards from §6.3's structure) but adds
  a parameter the proof must thread.
- **Proposed fix**: optional: simplify the lemma's
  signature to `tower a (tower b x + d) ≤ tower
  (a + b) (x + d)`, and let the call site instantiate
  `x := vMax v + o_g`. No mathematical change,
  cleaner proof.

### 12. §3.1 `interp_sumCtxER` proof match-evaluation step

- **Severity**: nit.
- **Location**: §3.1 lines 244–252.
- **Issue**: the `sumCtxER (n+1)` def uses
  `comp addN (fun i => match i with | ⟨0, _⟩ => proj
  (Fin.last n) | ⟨1, _⟩ => comp (sumCtxER n)
  (fun j => proj (Fin.castSucc j)))`. After
  `interp_comp` and `interp_addN`, the proof needs to
  evaluate the match at `i = 0` and `i = 1`
  separately. Lean's `simp` may or may not unfold
  the match cleanly without `Fin.cases`-style
  reasoning. The spec's proof hint cites
  `Fin.sum_univ_castSucc`, `interp_addN`,
  `interp_proj`, `interp_zeroN` — but not the match
  evaluation. Implementer may need `Fin.isValue` or
  manual `Fin.cases` to reduce `(fun i => ...).i`
  at `i = 0`/`i = 1`.
- **Proposed fix**: add `Fin.isValue` (or `decide`
  on `i.val < 2`) to the proof hint list in §3.1's
  `interp_sumCtxER` outline.

### 13. §1.2 / §2.4 phrasing "de-private"

- **Severity**: nit.
- **Location**: §1.2 line 53, §2.4 lines 175–192.
- **Issue**: the spec uses the verb "de-privates" /
  "de-privating" for removing the `private` modifier
  from `Fin.foldr_max_ge`. Not a banned word, but
  awkward; "make public" or "remove private modifier"
  reads more cleanly.
- **Proposed fix**: optional rephrasing; not blocking.

### 14. Round-1 finding 14 (#guard runtime) — residual

- **Severity**: nit.
- **Location**: §8.1 lines 822–829.
- **Issue**: the spec's footer explanation
  ("kernel to evaluate `A_two_iter`'s `expER` tree
  ... is intractable per CLAUDE.md memory") correctly
  diagnoses the round-1 blocker. The replacement
  `example`-with-`majorize_by_A_two_iter`-application
  pattern bypasses kernel evaluation of the tower.
  No residual blocker. However: the explanation
  uses CLAUDE.md memory phrasing
  ("not safe for `#guard`") that future readers may
  want a single-line citation for. Already
  cited inline; fine.
- **Proposed fix**: none.

### 15. §6.2's hypothesis `r_H, r_G` are arity-dependent

- **Severity**: nit (carried over from round 1
  finding 21).
- **Location**: §6.2 lines 595–613.
- **Issue**: round 1 finding 21 noted that `r_G`
  produced by `majorize_one` on `g_fam j : KMor1
  (a + 1 + (k + 1))` is a level-1 majorant at the
  *higher* arity `a + 1 + (k + 1)`, NOT at the outer
  `KMor1 a`. The revised spec lists `r_H, r_G : ℕ`
  as bare hypothesis parameters in §6.2 (line 601),
  with no docstring annotation about which arity
  the bound holds at. The level-2 caller (§6.3
  simrec bullet) supplies `r_H, r_G` from per-`j`
  `majorize_one` calls and takes the foldr-max; that
  threads correctly only if the type elaboration
  matches (it does). Round 1's recommendation to
  annotate this in the docstring was acknowledged
  but not done.
- **Proposed fix**: add a sentence to §6.2's
  docstring: "`r_H` is shared across all `h_fam j`
  (children at outer arity `a`); `r_G` is shared
  across all `g_fam j` (children at the higher
  context arity `a + 1 + (k + 1)`)."

## Summary

- Blocker: **0**.
- Major: **0**.
- Minor: 1, 3, 4, 5, 6, 8, 9, 10 = **8**.
- Nit: 2, 7, 11, 12, 13, 14, 15 = **7**.
- Total: 15.

The five round-1 blockers and four round-1 majors are
genuinely closed:

- Round-1 finding 1 (level-2 simrec γ chain) — closed by
  the new §4.5 `A_one_iter_linear_le_A_two_iter_two`
  lemma. The integer inequality `r_H + m·r_G + 1 ≤
  (r_H + r_G + 1)·(m + 1)` was verified at edge cases
  `r_H = r_G = 0`, `m = 0`, and `r_G = 0, r_H ≥ 1`. The
  outer `2^{...}` exponent matches `m + r_H + r_G + 2`
  as claimed.
- Round-1 finding 2 (§6.2 conclusion shape) — closed by
  restating §6.2 with offset-zero hypotheses, leveraging
  `majorize_one`'s identically-zero offset.
- Round-1 finding 3 (offset accumulation in `simrecVec`
  IH step) — closed by the same restatement: with
  zero offsets, the step case reduces to the master
  design's exact algebra.
- Round-1 finding 4 (linearBound interface mismatch) —
  closed by the explicit `private abbrev vMax`
  declaration in §2.3 lines 158–164.
- Round-1 finding 14 (`#guard` runtime) — closed by
  switching to `example`-based proof terms in §8.1
  with explanatory footer.
- Round-1 finding 16 (`comp` arity ascription) —
  closed by the explicit `fun _ : Fin 1 =>
  sumCtxERPlusOffset a p.2` ascription in §7.
- Round-1 findings 6, 7, 9 (proof-tactic gaps) —
  closed by §6.4's auxiliary lemma list (which now
  includes `tower_add_offset_le` and
  `tower_compose_offsets`) and the cited mathlib
  hooks.

Step 5's bridge lemma (`majorize_by_componentBound`,
§7) typechecks against the existing `ERMor1.comp`
signature (verified in `LawvereER.lean` line 88: `comp
: {k n : ℕ} → ERMor1 k → (Fin k → ERMor1 n) → ERMor1
n`). The `Fin.foldr` patterns in §5.2's `comp` and
`simrec` cases satisfy Lean's structural-recursion
contract by mirroring the existing `KMor1.linearBound`
(in `LawvereKSimPolynomialBound.lean` lines 207–277):
`majorize` recurses into itself only on direct
sub-terms (`f`, `gs i`); the simrec case offloads to
`majorize_one`, a separate function — same pattern
`linearBound` uses with `level0Shape`.

The remaining minor findings are proof-tactic gaps
(missing auxiliary lemmas like `A_one_iter_mono_left`,
`Fin.cons_self_tail`, an explicit `2^N + d ≤ 2^N · 2^d`
sub-step) that the implementer will encounter and
resolve during execution. None of them prevents the
spec from being mergeable.

**Overall assessment**: the spec is mergeable. The
remaining items are documentation polish and
proof-tactic-list completeness, not mathematical or
type-correctness concerns.
