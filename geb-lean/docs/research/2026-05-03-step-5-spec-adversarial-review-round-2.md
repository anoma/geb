# Step 5 spec — Adversarial review round 2

## Summary

The round-1 blocker (B1, dominance shape) and most majors (M1, M2, M5,
M6, M7) are adequately resolved. The spec-internal banned-word usages
(m1) and the imports-list omission (m2) are also resolved. However,
two majors are not adequately closed:

- M3 / new finding **A**: the §6.2.2 "Step 3" body
  `congr 2 <;> simp [Fin.cons_zero, Fin.cons_succ]` does NOT typecheck:
  `congr 2` already closes the goal completely (because
  `(Fin.cons m x) 0` reduces to `m` and `(Fin.cons m x) ∘ Fin.succ`
  reduces to `x` by definitional rewriting), leaving the `simp` to
  fire on an empty goal-list, which raises a "tactic does nothing"
  warning — and under the project's `weak.linter.mathlibStandardSet`
  / `warningAsError = true` lakefile setting, this is a build error.
  Verified empirically.
- New finding **C**: the new bridge lemma
  `KMor1.simrecVec_eq_Nat_simRecVec`'s "~15 lines" claim is unrealistic.
  The IH from `induction n` is specialized to a fixed `j`, but the step
  case requires the IH at every index of the previous-iteration vector
  (because the step appends `simRecVec ... n params` as a tail of the
  context). The proof needs to be quantified over `j` via
  `intro n; induction n with ... | succ n ih => intro j; ...` and the
  IH applied componentwise — a moderately substantive 25-40 line
  proof, not 15.

There is also a non-trivial new shape concern (finding **D/E**) about
the IH-adapter in §5.3: the elaboration of `kToER (h_fam j) _` with
the placeholder `_` is fragile when the IH from `induction f` is
shaped as `ih_h j` without the level argument abstracted out. Worth
verifying empirically at task time — but a more robust fix is to
make `kToER_interp_simrec` either accept the IH at *one* concrete
level proof (which the implementer fixes in the body via proof
irrelevance) or take the level proofs as part of the data the IHs
depend on.

Counts of new findings: **0 blockers, 2 majors, 4 minors**.
Round-1 status: **B1 resolved; M1 partially resolved; M2, M4, M5,
M6, M7 resolved; M3 still open** (re-stated as the §6.2.2 Step 3
issue). Of the round-1 minors: m1, m2, m3, m4, m5, m8, m9 resolved
or sufficiently soft; m6, m7 remain marginal.

The spec is close to ready. The remaining majors are local pseudocode
fixes; round 3 is not strictly required if the implementer is
expected to fix the `congr 2 <;> simp ...` line at task time and
adopt a more careful 25-40 line bridge-lemma proof. If the spec is
to be tightened before transitioning to writing-plans, two surgical
edits suffice (see Recommendations).

## Status of round-1 findings

### Resolved

- **B1 (dominance shape blocker)**. The spec now states
  `kToER_simrec_dominates` directly in the kToER-translated form,
  taking `ih_h` and `ih_g` as explicit hypotheses (option 1 of round
  1's three fix paths). The 5-step proof body in §6.2.2 begins by
  using the IHs to rewrite the kToER-translated families back to the
  K^sim-side ones, then bridges via
  `KMor1.simrecVec_eq_Nat_simRecVec`, then applies
  `KMor1.majorize_by_componentBound` plus the new
  `majorize_simrec_index_indep`. The architecture is sound; subject
  to the M3 / finding A objection about the literal `congr 2 <;>
  simp` line in step 3, the path is correct.
- **M2 (`addK` arity / privacy)**. Spec §9.2 now constructs an
  inline `addK : KMor1 2` rather than referencing the private
  Phase-1 definition. **Empirically verified to typecheck and
  evaluate correctly**: `addKSpec.interp ![3, 5] = 8` and
  `addKSpec.interp ![0, 7] = 7` both reduced. The implicit Fin
  numeric literal coercions for `KMor1.proj 0` and `KMor1.proj 2`
  resolve correctly without explicit `Fin.mk` / explicit type
  annotation.
- **M4 (rfl fragility for `majorize_simrec_index_indep`)**. The
  spec now uses `simp only [KMor1.majorize]` followed by `rfl` (or
  empty-tail close) and documents a hand-construction fallback. The
  callout is appropriately sized.
- **M5 (kToER let-chain equation compiler)**. §6.3 now documents the
  inline form as primary with a refactor fallback to a non-recursive
  helper `kToER_simrec_bound`. The fallback path is sound: the bound
  depends on `KMor1.majorize` of the input, which is non-recursive,
  so extraction works.
- **M6 (`sumCtxER_cons_le_of_le` proof)**. §6.2.3 now has a concrete
  inductive proof body, with a documented assessment that the
  implementer may need adaptation at task time (e.g., if mathlib's
  `Fin.foldr_succ` has shifted name). The structure is plausible.
- **M7 (functor-law optimism)**. §8.3 now defaults to
  `Quotient.sound` followed by `intro v i; simp only [...]` with
  documented expected simp set, and documents `rfl` as opportunistic
  rather than expected. This is appropriate.
- **m1 (banned words)**. Empirical re-grep confirms all banned-word
  occurrences in the spec body are now inside the explicit
  banned-word *list* (lines 1066-1070) or the acceptance-criteria
  text using the technically-allowed phrase "no `sorry` and no
  warnings" (line 1093 / 1098). No banned-word in-prose violations
  remain.
- **m2 (no explicit imports section)**. §3.2 now contains an
  alphabetized eight-line explicit import list. Sufficient.
- **m3 (citation gaps)**. §6 helpers and §7 / §8 lemmas now carry
  Tourlakis citations (§0.1.0.34, §0.1.0.10, §0.1.0.44 as
  appropriate). Sufficient.
- **m4 (confirmation)**. No fix needed; round-1 already confirmed.
- **m5 (Quotient.exact rewrite shape)**. §8.2's well-definedness
  body now uses the standard idiom: chain `rep_eq.trans
  rec₂.rep_eq.symm` directly and feed to `Quotient.exact`. Correct.
- **m8 (`[conditional]` line)**. §3.1's
  `ERMor1.sumCtxER_cons_le_of_le` line now reads "Default plan: add
  it at task time. Skip only if the implementer finds an inline-clean
  tactic". Acceptable.
- **m9 (`kToERFunctor_map_quot` signature)**. The spec now lists the
  helper in §8.4 prosily, without a precise signature, and documents
  that an implementer adding it would have to construct a small
  `KMorNQuo.atDepth.ofRep` add-on. The deferral is now adequately
  signposted.

### Still open

- **M1 (induction-hypothesis signature)**. Partially resolved.
  `kToER_interp_simrec`'s signature now correctly binds `h'` and
  `v'` in `ih_h` / `ih_g` (no more dangling `h_h` / `h_g`). However,
  the §5.3 adapter that converts the `induction f`-generated IHs to
  the new shape uses
  `rw [show kToER (h_fam j) h' = kToER (h_fam j) _ from rfl]`. This
  is fragile — `kToER` takes a level proof argument, and the `_`
  placeholder may or may not unify to the level proof in scope from
  the IH. The right fix is to expose the IHs from `induction f`
  directly without the placeholder rewrite — `ih_h j v'` already
  has the level proof baked in as a closed term, so the rewrite
  step is redundant if the type ascription matches. See finding
  D/E for the precise concern.
- **M3 (`KMor1.interp_simrec` extraction shape)**. The spec's fix
  (§6.2.2 Step 3 line `congr 2 <;> simp [Fin.cons_zero,
  Fin.cons_succ]`) does not work as written. Empirically verified:
  `congr 2` alone closes the goal entirely (because the post-rewrite
  goal `simrecVec h_fam g_fam x m j = simrecVec h_fam g_fam (fun j'
  => (Fin.cons m x) (Fin.succ j')) ((Fin.cons m x) 0) j` reduces to
  reflexivity by `Fin.cons` definitional unfolding), and the trailing
  `<;> simp [...]` then fires on an empty goal-list, producing a
  "'simp [Fin.cons_zero, Fin.cons_succ]' tactic does nothing"
  warning, which the project's `warningAsError = true` lakefile
  setting promotes to a build error. Either drop the `<;> simp` or
  replace `congr 2 <;> simp [...]` with just `congr 2`.

## New findings

### Blockers

None.

### Majors

#### A. §6.2.2 Step 3 `congr 2 <;> simp` line is a build error

(Restated from M3 still-open.) Empirically verified by writing the
exact line into a scratch test module:

```lean
example {a k : ℕ}
    (h_fam : Fin (k + 1) → KMor1 a)
    (g_fam : Fin (k + 1) → KMor1 (a + 1 + (k + 1)))
    (m : ℕ) (x : Fin a → ℕ) (j : Fin (k + 1)) :
    KMor1.simrecVec h_fam g_fam x m j
      = (KMor1.simrec j h_fam g_fam).interp (Fin.cons m x) := by
  rw [KMor1.interp_simrec]
  congr 2 <;> simp [Fin.cons_zero, Fin.cons_succ]
```

Build error:

```text
error: 'simp [Fin.cons_zero, Fin.cons_succ]' tactic does nothing
Note: This linter can be disabled with `set_option linter.unusedTactic false`
```

The same lemma closes with just:

```lean
  rw [KMor1.interp_simrec]
  congr 2
```

(Empirically verified to build clean.)

Fix: replace the `congr 2 <;> simp [Fin.cons_zero, Fin.cons_succ]`
line in §6.2.2 (and the analogous line at §6.2.4 step 5,
`congr 1 <;> simp [Fin.cons_zero, Fin.cons_succ]`) with `congr 2`
(resp. `congr 1`) and document that the residual goals (if any)
close definitionally via `Fin.cons`'s computation rules.

#### B. New bridge lemma proof shape is more involved than spec suggests

The spec at §6.1 says
`KMor1.simrecVec_eq_Nat_simRecVec` is "~15 lines per the
documented proof shape". Empirically, the proof requires
quantifying the IH over the index `j`:

```lean
theorem KMor1.simrecVec_eq_Nat_simRecVec {a k : ℕ}
    (h : Fin (k + 1) → KMor1 a)
    (g : Fin (k + 1) → KMor1 (a + 1 + (k + 1)))
    (params : Fin a → ℕ) :
    ∀ (n : ℕ) (j : Fin (k + 1)),
      KMor1.simrecVec h g params n j
        = Nat.simRecVec k a (fun j' => (h j').interp)
            (fun j' => (g j').interp) n params j := by
  intro n
  induction n with
  | zero => intro j; rfl
  | succ n ih =>
    intro j
    -- Step case: rewrite the dite-based stepCtx (KMor1.simrecVec)
    -- to the Fin.append-based form (Nat.simRecVec).  Requires
    -- a case split on `idx.val < a + 1` plus rewriting in the
    -- inner branch via Fin.cons_zero / Fin.cons_succ, and in
    -- the outer branch via ih applied at the appropriate index.
    sorry
```

If the IH is taken with `j` already bound (i.e., the spec's stated
form), then the step case cannot apply the IH componentwise to the
previous-iteration vector inside the `Fin.append` (because the
previous vector has multiple components, not just `j`'s).

The expected proof is **25-40 lines**, mirroring the existing
private `interp_simrec_eq_simrecVec` proof at lines 121-155 of
`LawvereKSimInterp.lean` (35 lines for the analogous shape). The
spec's "~15 lines" estimate is too tight.

Fix: update the §6.1 prose to "~25-40 lines, mirroring the existing
private proof shape" so the implementer is not surprised. The
function signature can stay as written (with `n` and `j` both
explicit on the right of the arrow) but the proof body should use
`intro n; induction n with ... | succ n ih => intro j; ...` to get
the IH componentwise.

### Minors

#### m1'. §5.3 IH-adapter `rw [show ... from rfl]` is unnecessarily fragile

The §5.3 pseudocode:

```lean
  | simrec i h_fam g_fam ih_h ih_g =>
      exact kToER_interp_simrec i h_fam g_fam h v
        (fun j h' v' => by
          rw [show kToER (h_fam j) h' = kToER (h_fam j) _
              from rfl]
          exact ih_h j v')
        ...
```

The `rw [show kToER (h_fam j) h' = kToER (h_fam j) _ from rfl]` is
a no-op pattern that aims to coerce the IH's level-proof argument
into the supplied `h'`. Since Lean's `kToER` is parameterized by an
implicit-or-explicit `(h : (h_fam j).level ≤ 2)`, two different
proofs of the same Prop produce *propositionally* equal but not
*syntactically* identical terms, and Lean's definitional unfolding
across the level-proof argument depends on irrelevance discipline.
The cleaner adapter is:

```lean
        (fun j h' v' => by
          have := ih_h j v'
          -- `this : (kToER (h_fam j) (h_h j)).interp v' =
          --         (h_fam j).interp v'`
          -- where h_h is the level proof inferred by the
          -- equation compiler at this case.  By proof
          -- irrelevance, `kToER (h_fam j) (h_h j) =
          -- kToER (h_fam j) h'`, but Lean treats this as
          -- definitional only when proofs irrelevance is
          -- exposed via `Subsingleton.elim` or
          -- `proof_irrel_heq`.
          convert this using 0)
```

or rely on the even simpler `exact ih_h j v'` with appropriate
level-proof inference. The implementer should verify at task time
which actually fires; the spec should mark this as
"implementer verifies via lean-lsp; one of the alternatives below
will close cleanly".

#### m2'. §8.3 `simp only` simp set is incomplete

The §8.3 pseudocode for `kToERFunctor_map_id`:

```lean
  apply Quotient.sound
  intro v i
  simp only [kToERN, kToER, KMorN.id, ERMorN.id,
    KMor1.interp_proj, ERMor1.interp_proj]
```

is missing `Quotient.lift_mk` and the destructuring of the
`Quotient.liftOn` itself. The actual goal after `apply
Quotient.sound; intro v i` involves
`(Quotient.liftOn ...).interp v i = ...`, which requires
`Quotient.lift_mk` (or `Quotient.liftOn_mk`) to fire before the
inner `kToERN` / `kToER` simp lemmas can match. Add to the simp
set: `Quotient.liftOn_mk`, `Quotient.lift_mk`, `Quotient.mk_eq_mk`
as candidates.

The spec already hedges with "the `simp only` set may need
additional lemmas the implementer discovers at task time", but
adding the Quotient lemmas pre-emptively reduces the at-task-time
discovery burden.

#### m3'. §6.2.4 Step 5 has the same `congr 1 <;> simp` issue

```lean
  rw [KMor1.interp_simrec]
  congr 1 <;> simp [Fin.cons_zero, Fin.cons_succ]
```

By the same reasoning as finding A, this either has the residual
goals close definitionally (in which case the `<;> simp` produces a
"tactic does nothing" warning) or it does not (in which case the
simp set may need additional lemmas). Empirically, with `congr 1`
and then explicit cases for the params and base entries, the
definitional reduction works without any simp. Replace with
`congr 1` (followed by explicit handling of the two residual
goals: one for params via `Fin.cons_succ`, one for base via
`Fin.cons_zero`) or with just `congr 2` if reduction closes both.

#### m4'. §6.2.3 `kToER_simrec_bound_mono` final `omega` step relies on absent inequality

The final step of §6.2.3's spec proof body:

```lean
  | succ a' ih =>
    simp only [Fin.foldr_succ, Fin.cons_zero, Fin.cons_succ]
    have ih_step : ... := by
      simp only [Fin.cons_succ]
      exact le_of_eq rfl
    -- Combine the slot-0 bump (m ≤ n) with the unchanged
    -- inner foldr.
    omega
```

The `omega` close at the end is over a goal involving
`Fin.foldr` outputs that `omega` cannot directly see (because they
are not `ℕ`-literal expressions; they are arbitrary
`Fin.foldr`-produced values). The `ih_step` `le_of_eq rfl` claim is
also unjustified — `Fin.foldr` over different functions doesn't
reduce to `rfl` even when the functions agree on the relevant
indices. The proof body needs to be rewritten as:

```lean
  | succ a' ih =>
    simp only [Fin.foldr_succ, Fin.cons_zero, Fin.cons_succ]
    -- Goal:
    -- Fin.foldr (a' + 1) (fun i acc => acc + Fin.cons m x (Fin.succ i)) m
    -- ≤ Fin.foldr (a' + 1) (fun i acc => acc + Fin.cons n x (Fin.succ i)) n
    -- The inner foldr terms are pointwise equal (Fin.cons _ x ∘ Fin.succ
    -- = x) so the body reduces to:
    -- (Fin.foldr (a'+1) (fun i acc => acc + x i) m) ≤
    -- (Fin.foldr (a'+1) (fun i acc => acc + x i) n)
    -- which is monotonicity in the initial accumulator.
    sorry
```

This is closer to a 10-15 line proof using a `Fin.foldr`-monotonicity
lemma (which may need to be proved as a side helper). The spec's
6-line claim is too tight.

## Empirical verifications performed

- **§9.2 inline addK construction**: typechecks and evaluates;
  `addKSpec.interp ![3, 5] = 8`, `addKSpec.interp ![0, 7] = 7`.
  The spec's exact pseudocode (with `KMor1.proj 0`, `KMor1.proj 2`
  using implicit Fin coercions and `![KMor1.proj 2]` Matrix
  notation) parses without explicit type annotation, modulo the
  `Mathlib.Data.Fin.VecNotation` import for `!` notation.
- **§6.2.2 Step 3 `congr 2 <;> simp [...]` line**: writes a build
  error. The bare `congr 2` closes the goal cleanly.
- **§6.1 bridge lemma `KMor1.simrecVec_eq_Nat_simRecVec` proof
  shape**: the IH from `induction n` is fixed at one `j`, but the
  step case requires the IH at every index of the previous-iter
  vector. The fix (intro `n`, induction, intro `j` per branch)
  is not accommodated by the spec's "~15 lines" estimate; expected
  proof size is 25-40 lines.
- **`Fin.cons_zero` and `Fin.cons_succ`**: confirmed present in
  current mathlib via grep on the existing
  `LawvereKSimMajorization.lean` proofs (lines 68, 71, 75, 79).
- **`Fin.cons_self_tail`**: confirmed present (line 871).

## Recommendations

The spec is close to ready. To close the two remaining majors with
minimum churn, edit two pseudocode blocks:

1. **§6.2.2 Step 3 (and the analogous §6.2.4 Step 5)**: change
   `congr 2 <;> simp [Fin.cons_zero, Fin.cons_succ]` to `congr 2`.
   Add prose noting that the residual subgoals (if any) close
   definitionally via `Fin.cons`'s computation rules; if Lean's
   reduction does not fire, fall back to explicit handling of each
   residual goal with `Fin.cons_zero` / `Fin.cons_succ`.

2. **§6.1 bridge-lemma proof estimate**: change "~15 lines per the
   documented proof shape" to "~25-40 lines, with the IH
   quantified over the output index `j` so the step case can apply
   the IH componentwise to the previous-iter vector inside
   `Fin.append`. Mirrors the existing private
   `interp_simrec_eq_simrecVec` proof at
   `LawvereKSimInterp.lean` lines 121-155 (35 lines)".

After these two edits, the spec is acceptable as written to begin
the writing-plans phase. The remaining minors are implementer-
discretion fixes that can be handled at task time without spec
revision.

## Round-3 trigger

A round 3 is **not strictly required**. With the two recommendation
edits applied, the spec is sound. If significant additional
clarifications (e.g., the §5.3 IH-adapter `rw [show ... from rfl]`
turns out to fail at task time) emerge during implementation, those
should be addressed via a spec patch rather than another full
adversarial-review round.
