# Step 4 plan adversarial review (round 1)

Plan under review:
`docs/superpowers/plans/2026-05-03-step-4-ksim-majorization.md`
(22 tasks, 2280 lines).
Spec: approved after two rounds of review.
This review focuses on the per-task Lean code, task ordering, and
hidden traps an implementer would hit.

The plan covers spec §1.2 in scope: every entity in the spec maps
onto exactly one task, and the self-review section verifies that
mapping. The Lean snippets are detailed; many of them are precise
and probably elaborate as written, but several proof bodies have
real risks. Most findings below are major or minor — none rise
to the level of a hard blocker on the design, but a couple should
be tightened before dispatch to subagents because they will
otherwise burn an iteration each.

## Findings

### Finding 1

- Severity: major.
- Location: Task 16, Step 16.2 (base case).
- Issue: the proof writes
  `simp only [KMor1.simrecVec, Nat.zero_mul, Nat.add_zero]` and
  then `rw [h_zero_max]` where
  `h_zero_max : max 0 (vMax params) = vMax params := Nat.zero_max _`.
  Two concerns:
  - `Nat.zero_max` is not a standard core/mathlib name in current
    Lean 4. The standard form is `Nat.zero_max` only if it has been
    re-introduced; in mathlib it is typically spelled `zero_max`
    (in `Mathlib.Order.Lattice` for `LinearOrder`) or proved via
    `Nat.max_eq_right (Nat.zero_le _)` / closed by `omega`. Calling
    it `Nat.zero_max _` is a real risk.
  - `simp only [KMor1.simrecVec]` unfolds the recursion. There is
    a far more idiomatic and safer path: the rfl-simp lemma
    `KMor1.simrecVec_zero` (in `LawvereKSimInterp.lean` line 179)
    rewrites the LHS to `(h_fam j).interp params` directly, with
    no exposure to the inner pattern of `simrecVec`'s definition.
- Proposed fix: rewrite using `KMor1.simrecVec_zero` rather than
  unfolding `simrecVec`. Replace `Nat.zero_max _` with
  `Nat.max_eq_right (Nat.zero_le _)`, or close the rewrite step
  by `omega` after `set M := max 0 (vMax params)`.

### Finding 2

- Severity: major.
- Location: Task 16, Step 16.3 (succ case).
- Issue: the proof body contains TWO `sorry` placeholders
  (one at the `h_iterate_M` declaration explicitly marked
  `:= by sorry`, one at the end). The plan acknowledges this
  with "(The implementer should not actually leave `sorry` in
  the committed code — the `sorry`s above are scaffolding for
  the proof structure.)" but `sorry` use is forbidden by
  CLAUDE.md ("never use `sorry`"). The plan should not seed
  these even as scaffolding because:
  - The lakefile sets `warningAsError = true`; even the scaffold
    intermediate state will fail the build.
  - The plan also instructs the implementer to insert `_`
    underscores per CLAUDE.md, which is the right pattern.
- Proposed fix: replace every `sorry` in the Step 16.3 sketch
  with `_`. Move the explanatory text into a comment so the
  implementer reads "this hole is filled with the chain X"
  rather than "this hole has a `sorry` to be removed later".
  Also remove the dead `h_iterate_M` block — its declaration
  is annotated as "(placeholder: not actually needed)", which
  is a code smell in a plan handed to a subagent.

### Finding 3

- Severity: major.
- Location: Task 16, Step 16.3 (the `set stepCtx` definition).
- Issue: the plan defines `stepCtx` inside the proof body, and
  the goal after `simp only [KMor1.simrecVec]` should already
  contain a `dite`-shaped function that matches `stepCtx`. But
  Lean's `set` tactic with `with hstepCtx` requires the term
  to literally appear in the goal. The way `simrecVec` unfolds
  at `n + 1` is via `simrecVec_succ`, which rewrites to a
  `(g_fam j).interp (fun idx => if h₁ : idx.val < a + 1 then ...
  else simrecVec h_fam g_fam params n ⟨..., _⟩)`. Whether `set`
  can capture this reliably depends on the exact eta- and
  beta-reduction shape Lean leaves the goal in after
  `simp only [KMor1.simrecVec]`. There is also a divergence:
  `simrecVec_succ`'s body uses `n` (the predecessor) where the
  plan's `stepCtx` writes `n` (the same), so this matches.
  The risk is the `h₂ : idx.val = 0` clause: in `simrecVec_succ`
  the body uses `h₂` as a hypothesis name, and the `if h₂ : ...`
  binding inside a non-tactic term is a `dite` whose match
  shape depends on the equation compiler.
- Proposed fix: replace `set stepCtx := ... with hstepCtx`
  followed by `unfold_let stepCtx` with a direct rewrite via
  `simp only [KMor1.simrecVec_succ]` (which is the rfl-simp
  lemma). Then `apply vMax_le_of_pointwise; intro idx;
  by_cases h₁ : idx.val < a + 1` works directly on the goal
  without the `set` indirection.

### Finding 4

- Severity: major.
- Location: Task 19, Step 19.2 (simrec case).
- Issue: after `simp only [KMor1.majorize, KMor1.interp_simrec]`,
  the goal contains
  `KMor1.simrecVec h_fam g_fam (fun j => v (Fin.succ j)) (v 0) i`
  (per `interp_simrec` in `LawvereKSimInterp.lean` line 161),
  not `KMor1.simrecVec h_fam g_fam (Fin.tail v) (v 0) i` as the
  plan writes. The plan then calls
  `KMor1.simrecVec_le_A_one_iter h_fam g_fam hh hg r_H r_G h_base
  h_step (Fin.tail v) (v 0) i`. `Fin.tail v` is definitionally
  equal to `fun j => v (Fin.succ j)`, but the proof's
  `calc` chain begins with
  `KMor1.simrecVec h_fam g_fam (Fin.tail v) (v 0) i ≤ ...`,
  not with the form left in the goal. Either the calc starting
  term has to match, or the proof needs an explicit
  `change` step or a definitional-equality move.
- Proposed fix: insert
  `change KMor1.simrecVec h_fam g_fam (Fin.tail v) (v 0) i ≤ _`
  before the `calc`, or `show` the same. Alternatively rewrite
  via `Fin.tail` definitional equality:
  `have heq : (fun j => v (Fin.succ j)) = Fin.tail v := rfl`
  and `rw [heq]`.

### Finding 5

- Severity: major.
- Location: Task 19, Step 19.2 (the `h_max_eq` step, line 1887).
- Issue: the proof writes
  `have h_max_eq : max (v 0) (vMax (Fin.tail v)) = vMax v := by
    conv_rhs => rw [h_cons_v]; rw [vMax_cons]`. This relies on:
  - `vMax_cons` from Task 2 stating
    `vMax (Fin.cons n v) = max n (vMax v)`. Task 2's `vMax_cons`
    has signature
    `(n : ℕ) (v : Fin a → ℕ) : vMax (Fin.cons n v) = max n (vMax v)`,
    OK.
  - The `conv_rhs => rw [h_cons_v]` rewrites `vMax v` to
    `vMax (Fin.cons (v 0) (Fin.tail v))`, then `rw [vMax_cons]`
    rewrites that back to `max (v 0) (vMax (Fin.tail v))`. The
    direction is correct, but the conv block syntax has a subtle
    issue: `conv_rhs => rw [h_cons_v]` will only rewrite the
    visible occurrence, and `vMax v` is an `abbrev` for
    `(Finset.univ : Finset (Fin a)).sup v`. The unification
    `(Finset.univ).sup v` vs `(Finset.univ).sup
    (Fin.cons (v 0) (Fin.tail v))` requires `v` to be syntactically
    rewritable, which depends on `h_cons_v` being stated as
    `v = Fin.cons (v 0) (Fin.tail v)` (it is, since
    `Fin.cons_self_tail v : Fin.cons (v 0) (Fin.tail v) = v` so
    its `.symm` flips it correctly). Good.
- Proposed fix: low priority but worth noting — in case the
  `abbrev` indirection trips elaboration, the implementer can
  unfold `vMax` first via `unfold vMax` or `show`, or use
  `Finset.sup_congr rfl` to avoid the issue entirely. No code
  change needed up front; flag for incremental-build attention.

### Finding 6

- Severity: major.
- Location: Task 19, Step 19.2 (post-`h_gamma`, line 1912).
- Issue: the calc terminator is
  `_ = tower 2 (vMax v + (r_H + r_G + 2)) := by congr 1; ring`.
  But `KMor1.majorize` for the simrec branch (Task 17) returns
  `(2, r_H + r_G + 2)`, so the goal after
  `simp only [KMor1.majorize, KMor1.interp_simrec]` and
  `rw [ERMor1.interp_A_two_iter]` should be
  `tower (KMor1.majorize ...).1 (vMax v + (KMor1.majorize ...).2)`
  reducing to `tower 2 (vMax v + (r_H + r_G + 2))`. But the
  `r_H` and `r_G` in the goal are the actually-pinned `Fin.foldr`-
  expressions over `majorize_one` results; the `set r_H := ...
  with hr_H` and `set r_G := ...` declarations rebind to local
  names. So the goal type after `set` will be
  `tower 2 (vMax v + (r_H + r_G + 2))`, matching the calc's last
  line. Good — but the calc's penultimate line returns
  `tower 2 (vMax v + r_H + r_G + 2)` (no inner parens) from
  `h_gamma`, and the equality step needs `congr 1; ring` to
  shuffle parens. `ring` over `ℕ` handles this. OK.
- Proposed fix: none, but this proof step has six load-bearing
  rewrite/calc moves — verify on first build attempt.

### Finding 7

- Severity: major.
- Location: Tasks 18 + 19 (theorem-by-pattern-match form).
- Issue: the plan defines `KMor1.majorize_by_A_two_iter` as
  `theorem KMor1.majorize_by_A_two_iter : ∀ ... | _, .zero, _, v
  => by ...`. Lean 4 supports theorem-by-pattern-match for
  structural recursion, but the equation compiler only generates
  the recursion principle when termination is structurally
  obvious AND every branch type-checks at the same instantiation
  pattern. When Task 18 lands the file in a temporarily broken
  state with `_` placeholders for `comp` and `simrec`, the
  build will fail with "unsolved goals" at those branches —
  fine. But the plan acknowledges this in Step 18.2 and asks
  the implementer NOT to commit until Task 19. This is unusual
  for the per-task commit cadence used elsewhere; subagent-
  driven execution that reviews each task independently will
  see Task 18 in a broken state.
- Proposed fix: either (a) merge Tasks 18 and 19 into a single
  task, or (b) state Task 18 as proving the atomic + raise
  cases inside a private lemma (or inside `by induction f` with
  `cases f` on the relevant sub-cases) without forcing the
  `match`-on-constructor shape. Either keeps each commit green.

### Finding 8

- Severity: major.
- Location: Task 8, Step 8.1 (`tower_add_offset_le` succ case).
- Issue: the proof structure builds
  `h_mul : 2 ^ tower b x + d ≤ 2 ^ tower b x * 2 ^ d`. Inside,
  the inner `calc` chain has
  `2 ^ tower b x + d ≤ 2 ^ tower b x * 1 + 2 ^ tower b x * d :=
    by have := h_pos; nlinarith` then
  `_ = 2 ^ tower b x * (1 + d) := by ring`. The `nlinarith` step
  is fragile: it must derive
  `N + d ≤ N + N · d` (where `N := 2 ^ tower b x ≥ 1`) without
  any hint that `N ≥ 1` is the relevant fact (only `h_pos` is
  in the local context, but `nlinarith` doesn't always pick up
  the right premises). On `ℕ` this can fail since `N · d ≥ d`
  requires `N ≥ 1`, and `nlinarith` over `ℕ` is less reliable
  than over `ℤ`. There is also an unused `have := Nat.mul_le_mul_left ...
  (show 1 + d ≤ d + 1 from by omega)` four lines above the
  `calc` — dead code in a plan.
- Proposed fix: simplify the inner block. Replace with
  `have : N + d ≤ N + N * d :=
    Nat.add_le_add_left (Nat.le_mul_of_pos_left _ h_pos) _`
  or close `2 ^ N + d ≤ 2 ^ N * 2 ^ d` directly via
  `Nat.add_le_mul` (or its variants). Drop the unused
  `Nat.mul_le_mul_left _ ...` `have`.

### Finding 9

- Severity: major.
- Location: Task 9 (γ.1).
- Issue: the proof writes
  `show c * x + d ≤ 2 ^ r * (![x] (0 : Fin 1)) + (2 ^ (r + 1) - 2)`
  as a `show` directive. Two concerns:
  - `(![x] : Fin 1 → ℕ) (0 : Fin 1)` reduces by `Matrix.cons_val_zero`,
    which the next line invokes via `simp only`. But `show` runs
    BEFORE that simp, so the `show` text must match what's in
    the goal after `rw [ERMor1.interp_A_one_iter]`. The closed
    form from `interp_A_one_iter` produces
    `2 ^ r * (![x] 0) + (2 ^ (r + 1) - 2)` with `![x] 0` (no
    `(0 : Fin 1)` ascription). The plan's `show` adds the
    explicit `(0 : Fin 1)` ascription which may or may not
    match the elaborated goal. If Lean's elaborator emits
    `Matrix.cons_val_zero` reduction first, this `show` is
    redundant and may fail to match.
  - Per CLAUDE.md style ("Use `change` not `show` when the goal
    text differs from what Lean has after reduction"), this
    should use `change` instead.
- Proposed fix: drop the `show` directive; rely on the
  `simp only [Matrix.cons_val_zero]` step to normalize, then
  close with `omega`. Or use `change` per CLAUDE.md guidance.

### Finding 10

- Severity: major.
- Location: Task 13 (γ.5), `h_int` step.
- Issue: the proof states
  `have h_int : r_H + m * r_G + 1 ≤ (r_H + r_G + 1) * (m + 1)
    := by nlinarith [Nat.zero_le r_H, Nat.zero_le r_G, Nat.zero_le m]`.
  Expanding RHS: `r_H · m + r_H + m · r_G + r_G + m + 1`. So we
  need `r_H · m + r_G + m ≥ 0`, which holds trivially. The
  `nlinarith` invocation should close this, but `nlinarith` over
  `ℕ` is sensitive: it sometimes refuses goals containing `*`
  unless given multiplicative hints. The plan does pass
  `Nat.zero_le _` hints which help. Risk: medium — this is the
  most likely `nlinarith` failure in the cycle.
- Proposed fix: give an explicit `ring_nf` first to expand RHS
  to `r_H · m + r_H + m · r_G + r_G + m + 1`, then `omega`. Or
  introduce
  `have : (r_H + r_G + 1) * (m + 1) =
    r_H * m + r_H + m * r_G + r_G + m + 1 := by ring`
  and then `omega`.

### Finding 11

- Severity: major.
- Location: Task 14 (`A_one_iter_compose`).
- Issue: the proof writes a long `have` chain ending with
  `ring_nf; omega`. The goal after `rw [interp_A_one_iter, ...]`
  three times is:
  `2 ^ a * (2 ^ b * x + (2 ^ (b + 1) - 2)) + (2 ^ (a + 1) - 2)
   = 2 ^ (a + b) * x + (2 ^ (a + b + 1) - 2)`. After `ring_nf`,
  the LHS expands but `2 ^ (a + 1)`, `2 ^ (b + 1)`, `2 ^ (a + b + 1)`
  remain as separate `pow` terms — `omega` does not reason
  about products like `2 ^ a * 2 ^ b`. The plan gives `h_pow_add`
  etc. as `have`s but does not actually `rw` by them before
  invoking `omega`. So `omega` will fail.
- Proposed fix: after `ring_nf`, explicitly
  `rw [h_pow_add, h_pow_succ_a, h_pow_succ_b, h_pow_succ_ab]`
  to push everything into a single base term `N := 2 ^ a *
  2 ^ b`, then `omega` with positivity hypotheses. Alternative:
  prove this via the explicit linear-algebra calc chain
  rather than `ring_nf; omega`. The plan's note about falling
  back to a `calc` chain is correct, but the primary path it
  shows will not close.

### Finding 12

- Severity: major.
- Location: Task 18, Step 18.1 (raise case proof of `h_p2_zero`).
- Issue: the plan writes
  `have h_p2_zero : p.2 = 0 := by
    unfold KMor1.majorize_one at hp
    simp only at hp
    exact congrArg Prod.snd hp.symm |>.trans rfl`
  followed by a comment "or simply `rfl` if majorize_one's Prod
  definitional unfolding goes through". `KMor1.majorize_one`
  returns `(r, 0)` per Task 15, so `p.2 = 0` should hold by
  definitional unfolding once `p` is unfolded. The
  `congrArg Prod.snd hp.symm |>.trans rfl` chain is a brittle
  way to get there — `simp only at hp` is a no-op if `hp`
  already has the correct shape, and the `congrArg` chain is
  awkward. Risk: this proof step will likely fail and the
  implementer will burn time figuring out the right
  combination.
- Proposed fix: replace with the simplest of:
  - `have h_p2_zero : p.2 = 0 := rfl`
  - `have h_p2_zero : p.2 = 0 := by simp [KMor1.majorize_one]`
  - `have h_p2_zero : p.2 = 0 := by unfold KMor1.majorize_one; rfl`
  Drop the comment "(or simply `rfl` ...)" — the plan should
  pick one path and stick to it.

### Finding 13

- Severity: minor.
- Location: Task 18, Step 18.1 (`succ` case).
- Issue: the proof closes via `omega`, with hypotheses
  `h_self : vMax v + 3 ≤ tower 2 (vMax v + 3)` and
  `h_v0 : v 0 ≤ vMax v`. The goal at that point (after the
  `simp only [KMor1.majorize, KMor1.interp_succ,
  ERMor1.interp_A_two_iter, Matrix.cons_val_zero]`) is
  `(v 0).succ ≤ tower 2 (vMax v + 3)`. `omega` cannot handle
  `tower`-shaped expressions — it treats them as opaque atoms.
  So the proof needs `tower 2 (vMax v + 3)` and `vMax v + 3` to
  be linked by an inequality `omega` can see. `h_self` provides
  exactly that link, so `omega` should close: it has
  `(v 0).succ = v 0 + 1` (built-in), `v 0 ≤ vMax v`, and
  `vMax v + 3 ≤ T` where `T := tower 2 (vMax v + 3)`. From these
  it derives `v 0 + 1 ≤ vMax v + 3 ≤ T`. OK.
- Proposed fix: none needed; flag for monitoring during impl.

### Finding 14

- Severity: minor.
- Location: Task 11, Step 11.1 (γ.3, final calc step).
- Issue: the proof closes the last calc step
  `_ = tower 2 (x + k + 2)` via two nested `change` steps and
  `rw [tower_succ]; ... rw [tower_zero]`. But `tower_succ` and
  `tower_zero` are both rfl-simp lemmas (per `Tower.lean` lines
  21–24). A simpler closure is
  `_ = tower 2 (x + k + 2) := by simp [tower_succ, tower_zero]`
  or even just `_ = tower 2 (x + k + 2) := rfl` (since `tower 2
  y = 2 ^ tower 1 y = 2 ^ (2 ^ tower 0 y) = 2 ^ (2 ^ y)`
  reduces by definitional unfolding). The plan's `change` chain
  works but is unnecessarily complex.
- Proposed fix: replace with `:= rfl` or
  `simp only [tower_succ, tower_zero]`.

### Finding 15

- Severity: minor.
- Location: Task 13, Step 13.1 (γ.5, `h_tower` near end).
- Issue: same as Finding 14 — the `change`/`rw [tower_succ]`/
  `change`/`rw [tower_zero]` chain is doing what one
  definitional-`rfl` could do. Cosmetic.
- Proposed fix: same as Finding 14.

### Finding 16

- Severity: minor.
- Location: Task 21 (tests), `#guard` for `majorize_one addK`.
- Issue: `KMor1.majorize_one addK h` calls `KMor1.linearBound
  addK h`, which is a structural recursion through addK's
  simrec branch, then computes `Nat.log 2 (p.1 + 1) + 1` etc.
  `addK` is a level-1 simrec, and `linearBound` at level-1
  simrec handles via its `simrec` branch (line 239 in
  `LawvereKSimPolynomialBound.lean`). For a level-1 simrec
  with level-0 children, this evaluates to a small constant
  via `level0Shape.linearBound`. Then `Nat.log 2` gets called
  on small constants, which `decide` handles. So
  `(KMor1.majorize_one addK ...).1 ≥ 1` should be a decidable
  Nat comparison that closes by `#guard`. Speed-wise this is
  fine — `linearBound` evaluates efficiently. Note the
  `#guard` form requires the value to compute to a literal Nat,
  and `KMor1.majorize_one addK ...` does compute (since
  `linearBound` is definitionally a `def`, not a `theorem`).
  OK.
- Proposed fix: none. Sanity check.

### Finding 17

- Severity: minor.
- Location: Task 21, end of test file.
- Issue: the second `example` proof has shape
  `example : KMor1.succ.interp ![3] ≤ ...`.
  The plan does not declare `KMor1.succ` as `KMor1.succ.interp`
  takes `Fin 1 → ℕ`, so `![3] : Fin 1 → ℕ` works. But the test's
  `vMax` substitute is
  `(Finset.univ : Finset (Fin 1)).sup (![3] : Fin 1 → ℕ)`, which
  computes to `3`. The implicit-argument flow through `Fin 1`
  should be fine, but the literal `(0 : Fin 2)` appears in the
  `proj` `#guard` which depends on `OfNat (Fin 2) 0`. Standard.
- Proposed fix: none.

### Finding 18

- Severity: minor.
- Location: Tasks 5–7 (sumCtxER family) and Task 4 definition.
- Issue: `sumCtxER` at `n + 1` is built as
  `comp addN [proj (Fin.last n), comp (sumCtxER n) (proj
  (Fin.castSucc j))]`. The plan's `Fin.sum_univ_castSucc`-based
  proof requires the closed-form sum to land as
  `∑ i : Fin n, v (Fin.castSucc i) + v (Fin.last n)`. The
  binary `addN` interp gives
  `v (Fin.last n) + (∑ i : Fin n, v (Fin.castSucc i))`, with
  `+` flipped relative to `Fin.sum_univ_castSucc`. The plan's
  proof closes this via `ring`. Fine — `ring` handles
  commutativity. Just confirm Nat-`ring` is in scope; mathlib's
  `Mathlib.Algebra.BigOperators.Fin` or `.Ring.Finset` should
  bring it.
- Proposed fix: if `ring` is not in scope after the listed
  imports, the implementer falls back to `omega` or
  `Nat.add_comm`.

### Finding 19

- Severity: minor.
- Location: Task 7, Step 7.2.
- Issue: `interp_sumCtxERPlusOffset`'s proof body is just
  `unfold sumCtxERPlusOffset; simp only [...]`. The `simp only`
  list includes `interp_sumCtxER`, which is `@[simp]` from
  Task 5. If the `addN` interp leaves the goal as
  `(∑ i, v i) + offset` directly, the `simp` set should close
  it. But the `match` in `sumCtxERPlusOffset`'s definition
  could leave residual `Fin.isValue`-style goals after the
  `addN` rewrite. The plan does include `Fin.isValue` in the
  simp set. OK, but if `match` blocks elaborate to non-trivial
  `dite` binders, more work may be needed.
- Proposed fix: monitor; if `simp only` leaves residual,
  fall back to manual case-split via `Fin.cases` on the inner
  `Fin 2` index.

### Finding 20

- Severity: minor.
- Location: Task 20 (bridge).
- Issue: the plan's bridge proof writes
  `simp only [ERMor1.interp_sumCtxERPlusOffset, Fin.isValue,
  Matrix.cons_val_zero]`. The RHS after the unfolding becomes
  `tower p.1 ((fun _ : Fin 1 => ((∑ i, v i) + p.2)) 0)`. The
  inner `fun _ : Fin 1 => ...` requires beta reduction at the
  index 0 to get `((∑ i, v i) + p.2)`. `simp only` includes
  `Matrix.cons_val_zero` but the actual fed argument is
  produced by `interp_comp` — namely `fun i => (... i).interp v`
  applied through `Matrix.cons` notation. The plan does NOT
  use `![...]` for the outer `comp`'s argument family; it uses
  `fun _ : Fin 1 => ...` per the spec. So the goal contains
  a `fun _ : Fin 1 => ...` value, not a `Matrix.cons`. The
  `Matrix.cons_val_zero` simp lemma may not fire. Need either
  `Function.const` reduction or a beta step.
- Proposed fix: insert `simp only [Function.const_apply]` or
  rely on `simp only [...]` doing beta reduction. The plan
  flags this with "(simp only invocation reduces ... pointwise;
  may need funext or change)" — that note is correct, but the
  fix should be pre-specified, not left to "implementer
  discretion".

### Finding 21

- Severity: minor.
- Location: Task 17 (`KMor1.majorize` def).
- Issue: the `simrec` branch reuses the `i` parameter implicitly
  with `_` placeholder: `| _, .simrec _ h_fam g_fam, hyp =>`.
  This drops the `Fin (k + 1)` index `i` (the simrec's output
  selector). `KMor1.simrec` takes
  `(i : Fin (k + 1)) (h_fam : Fin (k + 1) → KMor1 a) (g_fam : ...)`,
  so the arity is right. But Task 19's simrec proof does
  `| _, .simrec i h_fam g_fam, hyp, v => ...` — with `i` bound.
  The `def` and the `theorem` must agree on whether `i` is
  bound, so this is fine: the `def` ignores `i` (since the
  output `(r, offset)` depends only on the family levels).
- Proposed fix: none.

### Finding 22

- Severity: minor.
- Location: Task 17 (`hgs` and `hh`/`hg` constructions, lines
  1539–1544 and 1561–1578).
- Issue: in the `comp` branch
  `Finset.le_sup (f := fun j => (gs j).level) (Finset.mem_univ i)`
  produces `(gs i).level ≤ Finset.univ.sup (fun j => (gs j).level)`.
  Then `le_trans (le_max_right _ _) h` needs to consume the
  `≤ max f.level (Finset.univ.sup ...)`. After `unfold
  KMor1.level at h`, `h` becomes
  `max f.level (Finset.univ.sup (fun j => (gs j).level)) ≤ 2`.
  So the chain `Finset.le_sup ... ≤ Finset.univ.sup ≤
  max f.level (Finset.univ.sup ...) ≤ 2` is correct via
  `le_trans` twice. OK. (Same shape used for simrec.)
- Proposed fix: none. Same pattern as `linearBound`'s shape.

### Finding 23

- Severity: minor.
- Location: Task 3 (de-privating `Fin.foldr_max_ge`).
- Issue: the plan removes the `private` modifier on a lemma
  that lives in the `Fin` namespace (it is named
  `Fin.foldr_max_ge`). De-privating it makes it visible
  globally under `Fin.foldr_max_ge`. mathlib does NOT have a
  conflicting `Fin.foldr_max_ge` currently, but should mathlib
  add one in a future version, name collision is possible.
  A defensive alternative: state the lemma locally in
  `LawvereKSimMajorization.lean` (as the spec §2.4 alternative
  notes). The plan picks de-privating without
  explicitly weighing the alternative; minor.
- Proposed fix: documentation-level note; either choice is
  acceptable.

### Finding 24

- Severity: minor.
- Location: Task 16, Step 16.3 (succ case, `h_apply_step`).
- Issue: `hstep j stepCtx` requires that `stepCtx` matches the
  `Fin (a + 1 + (k + 1)) → ℕ` shape that `g_fam j`'s domain
  expects. `simrecVec_succ` gives
  `(g_fam j).interp (fun idx => ...)`, which has that exact
  shape. OK. The chain
  `(g_fam j).interp stepCtx ≤ A_1^{r_G}(vMax stepCtx)` then
  uses `hstep` directly.
- Proposed fix: none.

### Finding 25

- Severity: minor.
- Location: Task 19, Step 19.1 (`comp` case, line 1768
  `rw [ERMor1.interp_A_two_iter] at h_i ⊢`).
- Issue: the rewrite target `at h_i ⊢` rewrites both `h_i`
  (the IH) and the current goal. After rewriting, both contain
  `tower (...).1 (vMax v + (...).2)`. The next line is
  `simp only [Matrix.cons_val_zero] at h_i ⊢`. But
  `interp_A_two_iter` already produces `tower r (ctx 0)`, where
  `ctx = ![vMax v + ...]`. `Matrix.cons_val_zero` reduces
  `![y] 0 = y`. OK.
- Proposed fix: none.

### Finding 26

- Severity: nit.
- Location: Throughout the plan.
- Issue: the plan uses `private theorem` and `private abbrev`
  for several auxiliary lemmas. A few public lemmas (e.g.
  `linearBound_le_A_one_iter`, `A_one_iter_compose`,
  `self_le_A_one_iter`, `A_one_iter_mono_left`,
  `A_one_iter_le_A_two_iter_two`,
  `A_one_iter_linear_le_A_two_iter_two`,
  `two_pow_succ_mul_succ_le_tower_two`,
  `A_one_iter_le_two_pow_succ`) are file-local pure-Nat lemmas
  but lack the `private` modifier. Whether they should be
  `private` is a judgment call: the spec lists them under
  `namespace GebLean`, and they may be useful to future
  consumers. The plan does not make this consistent (e.g.
  `tower_compose_offsets` and `tower_add_offset_le` are
  `private`, but `linearBound_le_A_one_iter` is public).
- Proposed fix: pick a consistent rule. Suggested: keep all
  γ-lemmas (4.1–4.6) public (they may be reused by future
  workstreams), keep all `vMax_*` and `tower_*` auxiliaries
  private (file-local plumbing). This matches the spec's
  intent.

### Finding 27

- Severity: nit.
- Location: Task 16, succ case (around `h_iterate_M`).
- Issue: contains a placeholder `:= by sorry` annotation that
  the prose explicitly says "not needed as a separate `have`".
  This is dead code embedded in the plan and will confuse a
  subagent.
- Proposed fix: remove the entire `h_iterate_M` block from the
  plan; leave just the rest of the chain.

### Finding 28

- Severity: nit.
- Location: Task 21, `#guard` on `Nat.log 2 (...)`.
- Issue: per CLAUDE.md memory ("Use proven `@[simp]` lemmas,
  not direct kernel reduction"), the witness `#guard`s here
  should be fast — `KMor1.majorize_one`'s computation is
  Nat-arithmetic-only (no ER `interp` reductions, no
  Gödel-numbering chains), so even reducing `Nat.log 2 (...)`
  on small constants is sub-second. The `#guard
  (KMor1.majorize_one addK ...).1 ≥ 1` is fine. Confirmed in
  Finding 16.
- Proposed fix: none.

### Finding 29

- Severity: nit.
- Location: Banned-word audit on prose comments inside Lean
  code in the plan.
- Issue: I scanned for CLAUDE.md banned words (important, key,
  core, advanced, complex, simple, actually, fundamental,
  critical, advantage, benefit, insight, careful, difficult,
  blocked, incomplete, future, issue, problem, wait, hmm,
  sorry). Findings:
  - "load-bearing" appears multiple times in spec/plan prose
    — not banned, ok.
  - "critical sub-lemmas" in Task 9 docstring — wait, "critical"
    is banned. Actually the plan uses "Critical sub-lemmas"
    in Step 9.1 explanatory parenthetical, but it is in a
    PROSE COMMENT, not in committed code. Still it should be
    flagged because the plan says the implementer should
    transcribe these comments into committed code.
  - "load-bearing" repeats — not banned.
  - The plan says "fall back" several times — not banned.
  - "Critical" usage in Task 9 is the only banned word
    appearance I found.
- Proposed fix: replace "Critical sub-lemmas" in Step 9.1's
  parenthetical with "Required sub-lemmas" or "Sub-lemmas".

### Finding 30

- Severity: nit.
- Location: Task 22, Step 22.3 (workstream update text).
- Issue: the new "## Next steps" content lives inside a code
  fence labeled `markdown`, but the plan also says "(Replace
  the existing 'Next steps' section with the new one.)". The
  workflow ambiguity here is whether the implementer pastes
  the code-fenced content as-is (including any other section's
  content the plan does not show) or surgically replaces only
  the "Next steps" subsection.
- Proposed fix: clarify: the markdown block contains only the
  bullet describing step 4 completion plus a `## Next steps`
  heading; the implementer should append the bullet to
  Progress, then replace the existing Next steps section.

## Summary

- Blockers: 0.
- Majors: 12 (Findings 1–12).
- Minors: 13 (Findings 13–25).
- Nits: 5 (Findings 26–30).

Mergeability: this plan is dispatchable to subagents but
should be tightened first. The majors cluster around three
hot spots:

1. Task 16 (`simrecVec_le_A_one_iter`): contains `sorry`
   placeholders, fragile `set` use, and an unsafe `Nat.zero_max`
   call. The biggest single proof in the cycle has the most
   risk.
2. Task 19 (simrec branch of `majorize_by_A_two_iter`):
   `Fin.tail` vs `fun j => v (Fin.succ j)` mismatch; multi-step
   `calc` whose first term may not match the goal exactly.
3. Tasks 9, 13, 14: pure-Nat arithmetic chains where
   `nlinarith`/`omega` are doing the heavy lifting on
   non-linear `2 ^ N` products. Each has a real risk of failing
   to close as written.

Also: Tasks 18 + 19 should be merged or reorganized so each
commit is green; the per-task commit cadence used elsewhere is
broken by Task 18's "DO NOT commit yet" directive.

None of these prevent execution. The implementer will work
through them, but each major is one or two iterations of
incremental-build feedback that adds ~10 minutes and one
subagent dispatch. Tightening before dispatch saves 1–2 hours
of execution time.
