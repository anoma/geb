# Step 5 plan — Adversarial review round 1

## Summary

The plan covers the spec faithfully and has a sensible 20-task
decomposition with appropriate granularity for most steps. Build
discipline, citations, and ordering are largely in order. However,
several proof-script fragments in load-bearing tasks (Tasks 7, 9,
13, 14, 15, 18) contain concrete bugs or shape mismatches that will
cause the implementer to stall without further guidance. One bug
(the `hrel v' i'` shape in Task 13) was inherited verbatim from the
spec and not caught by the three rounds of spec review; the others
are plan-specific gaps.

Counts: **0 blockers, 7 majors, 8 minors**. The plan is salvageable
with a round-2 pass that resolves the dominance-bound shape mismatch
(M1), the Quotient-relation shape (M2), and the Tier 2 level-proof
synthesis (M3). The remaining majors are consequences of the
underlying ambiguities.

## Blockers

None. Every task is implementable in principle, given an implementer
willing to deviate from the literal pseudocode and apply
proof-engineering judgement.

## Majors

### M1. Dominance-bound shape mismatch in Tasks 5/7/9

`KMor1.majorize_by_componentBound` (step 4,
`LawvereKSimMajorization.lean:910`) produces a bound of shape
`ERMor1.comp (A_two_iter p.1) (fun _ : Fin 1 => sumCtxERPlusOffset a p.2)`,
where the second `comp` argument is a `fun _ : Fin 1 => ...`
lambda. Task 5's `kToER` simrec branch builds the bound as
`ERMor1.comp (A_two_iter p.1) ![sumCtxERPlusOffset (a + 1) p.2]`,
using Matrix `![...]` cons-vec notation. Although these two forms
are propositionally equal (verified empirically — closes by
`funext i; match i with | ⟨0, _⟩ => rfl`), they are not
syntactically nor definitionally identical.

Task 7's "Step 6" `rw [KMor1.majorize_simrec_index_indep ...] at h_dom`
expects the `h_dom` term — coming from
`majorize_by_componentBound (.simrec j h_fam g_fam) h_j (Fin.cons m x)` —
to bridge cleanly to the `bound` carried in the
`kToER_simrec_dominates` statement. But `bound` uses `![...]` and
`h_dom` uses `fun _ : Fin 1 => ...`. The `rw` will not bridge that
gap. The plan's "If errors occur" list for Task 7 mentions
`change`-based alignment but does not flag this specific mismatch
or supply the `funext`-based congruence.

Recommended fix: add an explicit `Matrix.cons_eq_cons_const` /
`funext`-based bridge in Task 7's preamble, or change Task 5's
`kToER` simrec bound to use the same `fun _ : Fin 1 => ...` shape
that step 4 produces, eliminating the divergence entirely.

### M2. `Quotient.exact` gives function-level eq, not per-component

Tasks 12 and 13 (and verbatim in spec §8.2) assert:

```lean
have hrel : (kMorNSetoid n m).r rec₁.rep rec₂.rep := Quotient.exact h_eq
-- hrel : ∀ v i, (rec₁.rep i).interp v = (rec₂.rep i).interp v
exact kToERN_compat_extEq rec₁.rep_level rec₂.rep_level
  (fun v' i' => hrel v' i') v i)
```

But `kMorNSetoid n m` (defined at `LawvereKSimQuot.lean:21`) has
`r f g := ∀ ctx : Fin n → ℕ, f.interp ctx = g.interp ctx`, where
`f.interp ctx : Fin m → ℕ`. So `hrel : ∀ ctx, rec₁.rep.interp ctx
= rec₂.rep.interp ctx`. This is a function-level equality;
`hrel v'` returns `rec₁.rep.interp v' = rec₂.rep.interp v'`, an
`Eq` of `Fin m → ℕ` functions. Applying `i'` to that `Eq` is
malformed — the term `hrel v' i'` does not type-check.

The fix is `congr_fun (hrel v') i'`, or equivalently
`(funext_iff.mp (hrel v')) i'`, or restructuring the
`kToERN_compat_extEq`'s hypothesis shape to consume the
function-level equality directly.

This bug was present in spec round-3 with no catch; the plan
inherits it.

### M3. Tier 2 `kToER_interp addK _ _` cannot synthesize the level-proof placeholder

Task 18's pseudocode:

```lean
example : (kToER addK
              (by simp [addK, KMor1.level])).interp ![3, 5]
            = addK.interp ![3, 5] :=
  kToER_interp addK _ _
```

Empirical test (lean-lsp via `lean_multi_attempt` against a stub):
the two `_`s in `kToER_interp addK _ _` correspond to the level
proof `addK.level ≤ 2` and the context `v`. Lean reports
"don't know how to synthesize placeholder for argument `h`". The
level proof must be supplied explicitly, e.g.
`kToER_interp addK (by simp [addK, KMor1.level]) ![3, 5]`. The
plan does not supply this and does not flag it.

Implementer-time fix is one line, but the plan's literal
pseudocode will not compile.

### M4. Task 14/15 `simp only [kToER]` does not unfold the equation compiler match

`kToER` is defined by pattern-matching across five constructors;
its equation lemmas are auto-generated as
`kToER.eq_1 ... kToER.eq_5` (or per-case named lemmas), not as a
single `kToER` simp rule. `simp only [kToER]` will likely fail to
fire on `kToER (KMor1.proj i) _` (Task 14) or
`kToER (KMor1.comp f gs) _` (Task 15) without the Task-6
`kToER_proj` / a Task-6-extended `kToER_comp` lemma in the
simp set.

Task 6 only defines simp lemmas for `kToER_zero`, `kToER_succ`,
`kToER_proj`, and `kToER_raise` — not `kToER_comp`. Task 15's
`map_comp` needs the comp-arm reduction. The plan should either:

- extend Task 6 to include `kToER_comp` (proved by `rfl` against
  the def), or
- replace `simp only [kToER]` in Tasks 14/15 with the explicit
  per-arm lemma names.

### M5. Task 14/15 `apply Quotient.sound` may not fire before reduction of `Quotient.liftOn`

The goal in Task 14 starts as
`kToERFunctor_map (𝟙 n) = 𝟙 (n : LawvereERCat)`. The LHS unfolds
to `Quotient.liftOn ... ...` (per Task 13's def). For
`apply Quotient.sound` to succeed, both LHS and RHS must be in
the form `Quotient.mk _ _`. The LHS isn't until
`Quotient.liftOn_mk` fires.

In practice, `Quotient.liftOn (Quotient.mk s a) f h` does reduce
to `f a` definitionally (quotient computation rule), so this may
just work. But it depends on the elaborator unfolding
`KSimMor.id`'s `depth_witness` to `Quotient.mk _ ⟨...⟩` — and the
plan does not unfold `kToERFunctor_map` or expose
`Quotient.liftOn_mk` before `apply Quotient.sound`. If the
identity's `depth_witness` is stored opaquely (which it isn't —
`KMorNQuo.id_atDepth` at `LawvereKSimQuot.lean:411` is a direct
`Quotient.mk _ {...}`), this should reduce.

Recommended: insert
`unfold kToERFunctor_map; show Quotient.mk _ _ = Quotient.mk _ _`
before `apply Quotient.sound`, or use
`refine Quotient.sound ?_` after a confirmed reduction.

### M6. Task 7 step 4's `simp only [KMor1.level]` claim of index-independence

Task 7 step 4 establishes `(KMor1.simrec j h_fam g_fam).level
= (KMor1.simrec i h_fam g_fam).level` via `simp only
[KMor1.level]`. This is correct because the simrec branch of
`KMor1.level` does not consume the index argument
(`LawvereKSim.lean:112`). Verified by lean-lsp test against
Task 2's `majorize_simrec_index_indep` analogue.

But: Task 7 mentions `simp only [KMor1.level]` may fail to unfold
the match — and the recommended fallback `show ... = ...; rfl`
won't necessarily work either, because `KMor1.level` on
`KMor1.simrec` reduces by `Eq.refl` only after Lean has chosen
the simrec branch of the match. For both `i` and `j` arguments to
the same `simrec` constructor, the reductions are
definitionally identical. So `rfl` should close. Verified for
Task 2's analogue (`simp only [KMor1.majorize]` closes the
analogous goal). Likely OK at task time.

Marking Major because the fallback specified in the plan
(`show ... = ...; rfl`) is unlikely to be the smoothest path —
the simpler `rfl` should suffice. Implementer-experience risk.

### M7. Task 9 step 2's `show` move requires exact goal-text match

The plan exposes the simrec call via:

```lean
show (ERMor1.simultaneousBoundedRec k a
        (fun j => kToER (h_fam j) (h_h j))
        (fun j => kToER (g_fam j) (h_g j))
        (let p := KMor1.majorize (.simrec i h_fam g_fam) h
         ERMor1.comp (ERMor1.A_two_iter p.1)
           ![ERMor1.sumCtxERPlusOffset (a + 1) p.2])
        i).interp (Fin.cons n x) = _
```

Lean's `show` is strict pattern matching on the goal text. If
`kToER`'s reduction step has produced a goal with the inline `let`
expanded (or with the `bound` projected differently), this will
fail. The plan's "If errors occur" guidance recommends using
`mcp__lean-lsp__lean_goal` to discover the actual goal text — that
is a runtime workaround, but it leaves the implementer to invent
the right `show` form.

Recommended: replace the `show` with `change` or with an
intermediate `have`-rewrite that names the parts, so the proof is
robust to elaboration variation.

## Minors

### m1. "block" usage borderline in lines 181, 195, 621, 636, 1265

Plan uses "import block", "namespace block", and "by block" as
technical CS jargon. The CLAUDE.md banned-word list includes
"block". These are fixed Lean syntactic units (`namespace ... end`,
`by ...`) and appear as such in mathlib docs. Borderline; could be
"section" or "scope" instead.

### m2. "simple" on plan line 2033

"trivially mechanical tasks (skeleton creation, simple def
additions)" uses the banned word "simple". Should be revised.

### m3. Task 6's `kToER_raise` `rfl` is verified to work

The plan flags concern about proof-irrelevance failing. Empirically
verified (lean-lsp): a stub `kToERStub` with the analogous raise
arm and the analogous lemma closes by `rfl`. Lean's proof
irrelevance for `Prop`-valued level proofs handles it. The plan's
fallback list (`unfold kToER`, `congr` + `Subsingleton.elim`) is
unnecessary; could be removed for clarity.

### m4. Task 1's bridge proof empirically partially verified

The proof body in Task 1.5 was attempted via lean-lsp
(`lean_multi_attempt` against ERSimultaneousBoundedRec.lean which
already imports SimRec.lean). The setup blocks at the
`GebLean.KMor1` namespace not being available at the chosen test
position — could not run the proof end-to-end. The structure
(induction on `n`, `congr 1` after `Nat.simRecVec_succ` /
`KMor1.simrecVec` unfolds, `by_cases h₁` and `h₂` mirroring the
existing private `interp_simrec_eq_simrecVec`) is sound and
analogous to existing proven code.

The dependency `import GebLean.Utilities.SimRec` is genuinely
needed (verified: `LawvereKSimInterp.lean` imports only
`GebLean.LawvereKSim`, which imports only mathlib `Mathlib.Data.Fin.Basic`,
`Mathlib.Data.Finset.Lattice.Fold`, `Mathlib.Data.Fintype.Basic` —
no transitive `Nat.simRecVec` access).

### m5. Citation discipline gaps in plan docstrings

Per CLAUDE.md's literature-citation discipline:

- Task 1 cites "master design §3.5" but does not cite a Tourlakis
  paragraph, even though the bridge concerns simultaneous primitive
  recursion (§0.1.0.7 / §0.1.0.34). Recommended add.
- Task 6's atomic interp lemmas have no Tourlakis citation. Could
  reference §0.1.0.44 (the level-2 ⊆ direction).
- Tasks 11, 12, 13, 14, 15, 16 cite master design §3.5 but no
  Tourlakis paragraph. Some are pure plumbing (Task 11
  `kToERN`, Task 12 `kToERN_compat_extEq`); for those a master-
  design-only citation is fine. Tasks 14/15 are functor laws —
  cite §0.1.0.44 ⊆ direction.

### m6. Task 17's atomic test `kToER_raise` example proof requires a free `f`

```lean
example {f : KMor1 2}
        (h : (KMor1.raise f).level ≤ 2)
        (h' : f.level ≤ 2) :
    kToER (KMor1.raise f) h = kToER f h' := rfl
```

This uses `{f : KMor1 2}` as an implicit argument to an `example`,
which only works if Lean does not flag "instance-implicit cannot
be inferred". Since `f` is implicit and not used in instance
search, this should fire as a hypothesis-only example. Verified
similar pattern works for the stub. Not a blocker but worth
checking that `example` accepts `{...}` as bound hypothesis.

### m7. Task 18's `addK.level ≤ 2` proof actually evaluates fine

Empirically verified: `simp [addK, KMor1.level]` closes the goal
`addK.level ≤ 2` for the spec's `addK` definition. No fallback
needed. The plan's fallback list ("If the simp doesn't reduce the
`Finset.univ.sup`") is over-cautious. Minor.

### m8. `lake build GebLean.LawvereKSimER` syntax verified

Empirically: `lake build GebLean.LawvereKSim` succeeds against the
existing module. The `lake build <Module>` syntax is correct (no
`--` separator needed). Task instructions match.

## Empirical verifications performed

The following were tested via `lean_multi_attempt` against the
existing codebase:

1. **Task 2 `simp only [KMor1.majorize]`** closes the
   index-independence goal cleanly (no diagnostics).
2. **Task 17 `addK` parsing**: the inline `KMor1.simrec (k := 0)
   ⟨0, by omega⟩ (fun _ => KMor1.proj 0) (fun _ => KMor1.comp
   KMor1.succ ![KMor1.proj 2])` parses correctly with `a = 1`
   inferred from the `KMor1 2` annotation.
3. **Task 18 `addK.level ≤ 2`**: `simp [addK, KMor1.level]` closes
   the level proof.
4. **Task 18 `kToER_interp addK _ _` synthesis failure**: stubbed
   `kToER_interp_stub addKtest3 _ ![3, 5]` fails with "don't know
   how to synthesize placeholder for argument `h`". Confirms M3.
5. **Task 6 `kToER_raise` `rfl`**: stub mirrors the proof and
   closes by `rfl`. Confirms M3 minor.
6. **Mismatch `(fun _ : Fin 1 => x) = ![x]`**: closed by `funext;
   match | ⟨0, _⟩ => rfl`. Confirms M1 (the two forms are equal but
   not definitional).
7. **`KMor1.level` index-independence definitional shape**: the
   simrec branch of `KMor1.level` ignores the index per
   `LawvereKSim.lean:112`. `simp only [KMor1.majorize]` (the
   analogue at `KMor1.majorize` simrec-branch) closes the analogous
   goal.
8. **Import requirement for Task 1**: `LawvereKSimInterp.lean`
   imports only `GebLean.LawvereKSim`, which imports only
   mathlib `Mathlib.Data.Fin.Basic`,
   `Mathlib.Data.Finset.Lattice.Fold`, `Mathlib.Data.Fintype.Basic`
   — no transitive `Nat.simRecVec` access. Task 1's
   `import GebLean.Utilities.SimRec` is genuinely needed.
9. **`Fin.cons_self_tail` exists**: confirmed via `lean_loogle`.
10. **`lake build <Module>`**: confirmed `lake build
    GebLean.LawvereKSim` succeeds with the bare module-name form.

## Recommendations

1. **Plan revision** addressing M1 (bound shape), M2
   (`hrel`/`congr_fun`), and M3 (level-proof synthesis) is needed
   before the plan is dispatched to subagents. These three are
   load-bearing and will halt subagents at Tasks 7, 13, and 18.
2. **M4-M5 functor laws** should add explicit per-arm simp lemmas
   (`kToER_comp`) to Task 6 and an `unfold kToERFunctor_map`
   prelude to Tasks 14/15.
3. **M6-M7 risk mitigation**: prove Task 2's
   `majorize_simrec_index_indep` first via a focused subagent and
   verify the `rfl` path before Task 7 begins. Task 9 should
   prefer `change`-based goal alignment over `show` for elaboration
   robustness.
4. **Spec round 4 should also be considered** to close the M2 bug
   inherited from spec §8.2. The spec text and the plan text both
   carry the malformed `hrel v' i'` invocation.
5. **m1-m2 banned-word audit**: replace "block" → "section" /
   "scope" and "simple def additions" → "atomic def additions".
6. **m5 citations**: add Tourlakis-paragraph references to Tasks
   1, 6, 11, 12, 13, 14, 15.

## Round-2 trigger

Round 2 is recommended after the plan author addresses M1-M5. If
M2 cannot be cleanly fixed in the plan without amending the spec,
spec round 4 should run in parallel with the plan revision. Plan
round 2 should re-verify Task 7 and Task 13 against the corrected
shapes via lean-lsp before the plan re-enters the dispatch
pipeline.
