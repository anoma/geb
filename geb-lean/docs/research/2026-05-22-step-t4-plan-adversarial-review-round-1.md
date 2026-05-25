# T4 plan adversarial review — round 1

Adversarial review of
[`docs/superpowers/plans/2026-05-22-step-t4-runtime-bound-plan.md`](../superpowers/plans/2026-05-22-step-t4-runtime-bound-plan.md)
against
[`docs/superpowers/specs/2026-05-22-step-t4-runtime-bound-design.md`](../superpowers/specs/2026-05-22-step-t4-runtime-bound-design.md)
and the authoritative project sources cited in the brief.

## Summary

- Blockers: 9
- Serious: 8
- Minor: 6

The plan does not type-check against the surfaces it claims to
consume. Two of the largest blockers — non-existent
`KMor1.level_*` simp lemmas and non-existent
`Tower.tower_ge_two`/`Tower.tower_mono_both` — propagate
throughout Tasks 1–10 and make a faithful execution impossible
as written. The plan also disagrees with itself about the
AXIOM_ALLOW site count and bakes a project-rule violation
(committing `sorry`-bearing code across Tasks 5–8) into the
workflow. A revision pass is required before the plan is
ready to drive an SDD execution.

## Blockers

### B1: `KMor1.level_*` simp lemmas referenced throughout do not exist

Multiple tasks issue rewrites against simp lemmas that are not in
the codebase. `GebLean/Utilities/KArith.lean` does not declare
`KMor1.level_add`, `KMor1.level_monus`, `KMor1.level_pow2`,
`KMor1.level_natK'`. `GebLean/LawvereKSim.lean` does not declare
`KMor1.level_comp`, `KMor1.level_proj`, `KMor1.level_zero`. The
file's level pattern is `example : KMor1.add.level = 1 := by
decide` (KArith.lean:159) — concrete computations, not named
simp lemmas. The T3 simulator's
`simulate_level` (KSimURMSimulator.lean:975–984) confirms the
codebase convention: unfold via `unfold simulate; change …` and
discharge with `Fin.maxOfNat_le` + `max_le`, not `simp only
[KMor1.level_comp]`.

Sites where the plan references these non-existent names:

- Task 1, Step 6 (line 242–250): "`simp only [KMor1.maxK,
  KMor1.level_comp, KMor1.level_add, KMor1.level_monus,
  KMor1.level_proj]`".
- Task 2, Step 6 (line 376–401): `simp only [KMor1.maxOver,
  KMor1.level_comp]`, `simp only [KMor1.level_comp,
  KMor1.level_proj]`, `simp [KMor1.level_proj]`.
- Task 3, Step 4 (line 481–491): `simp only [KMor1.pow2_iter,
  KMor1.level_comp, KMor1.level_pow2]`, `simp [KMor1.pow2_iter,
  KMor1.level_proj]`.
- Task 9, Step 4 (line 1356–1369): "`simp only [boundExprK,
  KMor1.level_comp, KMor1.level_pow2_iter, KMor1.level_add,
  KMor1.level_maxOver, KMor1.level_natK']`" plus
  `KMor1.level_natK'` in the body.
- Task 10, Step 5 (line 1483–1493): `simp only [erToK,
  KMor1.level_comp]` and `simp [Fin.cons_succ,
  KMor1.level_proj]`.

Either every Task 1–10 level proof must be rewritten in the
`unfold X; change max … ≤ 2; apply Nat.add_le_add_right; apply
max_le; …` style of `simulate_level`, or the plan must add a
preceding Task ("Task 0.5") that introduces the missing
`@[simp]` level lemmas in `KArith.lean` and
`LawvereKSim.lean`. Either way the cited code blocks above will
not elaborate.

### B2: `Tower.tower_ge_two` and `Tower.tower_mono_both` do not exist

The brief specifically called for verification of these names.
A scan of `GebLean/Utilities/Tower.lean` confirms the file
exposes (and only exposes): `tower`, `tower_zero`, `tower_succ`,
`self_le_tower`, `one_le_tower_of_one_le`, `tower_mono_right`,
`tower_comp`, `le_two_pow_self`, `tower_mono_left`,
`two_pow_le_tower_one`, `two_mul_le_two_pow`,
`mul_tower_le_tower_add_two`, `tower_pow_le_tower_add_three`.

The plan invokes:

- Task 6, Step 2 (line 863): `Tower.tower_mono_both
  (Fin.le_maxOfNat _ _ i) (by omega)`.
- Task 6, Step 4 (line 903–904):

  ```text
  have h_X_ge_2 : tower mu_g m ≥ 2 := by
    exact Tower.tower_ge_two _ _ (by … omega)
  ```

Neither lemma is defined. `tower_mono_both` would have to be
synthesised from `tower_mono_left` and `tower_mono_right`
(both exist). `tower_ge_two` would have to be derived from
`self_le_tower` + `Nat.le_trans` with an `m ≥ 2` hypothesis,
which the plan does not establish; the comp case has no a
priori `m ≥ 2` either.

### B3: `Tower.self_le_tower` arity / signature mismatch

`Tower.lean:27` declares `theorem self_le_tower (k x : ℕ) : x ≤
tower k x` — two explicit `ℕ` arguments, no precondition. The
plan applies it with a third "preconditioned-by-omega" argument
at multiple sites, e.g. Task 5 Step 4 (line 732): "`exact
this.trans (Tower.self_le_tower _ _ (by omega))`"; Step 5 (line
760); Step 6 (line 786); Task 6 Step 4 (line 911) "`have :=
Tower.self_le_tower mu_g m (by omega)`". These will fail with
"too many arguments". Strip the `(by omega)`.

### B4: `check-axioms.sh` does not accept declaration names

The plan instructs running e.g. `bash scripts/check-axioms.sh
KMor1.maxK KMor1.interp_maxK KMor1.maxK_level` (Task 1 Step 8,
line 264–265); same shape in Tasks 2, 3, 4, 8, 9, 10, 11, 12, 13,
14. The script's argument parser (scripts/check-axioms.sh
lines ~75–135) only accepts files, directories, or glob
patterns; non-file/non-directory positional arguments fail with
"Error: `<arg>` is not a file or directory" (line ~135). The
script auto-discovers declarations within the supplied files.

Every per-task axiom-audit step must be reworded to pass file
paths, e.g. `bash scripts/check-axioms.sh
GebLean/Utilities/KArith.lean` (then read the script's report
to confirm only the expected declarations carry the documented
AXIOM_ALLOW set). The Task 0 baseline call at line 152 is the
only correctly shaped invocation.

### B5: workflow embeds `sorry` across commits, violating the project rule

`CLAUDE.md` § "`sorry`, `admit`, and underscores" states `sorry`
is permitted between commits but "is never permitted in
committed code". The plan's Task 5, Step 8 (line 796–805)
acknowledges this and instructs the worker to *defer the commit
through Tasks 5–8*:

> Do NOT commit while `sorry` is present in committed code.
> Per the project rule, `sorry` is permitted only between
> commits while a skill needs it. … defer the commit until
> Task 8 completes all four inductive cases. Mark this task as
> *partially complete* and proceed to Task 6 in the same
> working-copy state.

This is internally consistent with the rule but inconsistent
with the plan's own workflow notes at line 91–95
("Conventional commits. Subject: `feat(ertok): …`") and with
the per-task commit instructions in Tasks 5, 6, 7 themselves
(each ends with what looks like an SDD-style "commit on task
completion" step but is then countermanded). The SDD harness
expects per-task commits as part of its progress tracking;
spreading one logical commit across four tasks breaks the
abstraction.

The blocker is structural, not just stylistic: the worker
cannot "complete" Tasks 5, 6, or 7 in the SDD sense without
committing, and the plan does not specify how the SDD-level
progress is tracked when several tasks share one commit. Either
fold Tasks 5–8 into a single Task 5 with sub-steps (sub-tasks 5a,
5b, 5c, 5d, plus a final assembly + commit step), or restructure
each task so its commit contains a clean intermediate
proposition (e.g. prove a per-constructor lemma and call its
combination via a final task) — but in either case the current
shape ("partially complete, no commit, proceed to next task")
contradicts SDD's task-as-commit-unit semantics.

### B6: Task 10 Step 6's `compileER_runFor` call does not type-check

Task 10's `erToK_interp` body (line 1505–1518):

```text
  rw [KSimURMSimulator.simulate_interp]
  exact compileER_runFor e v _ (boundExprK_dominates e v)
```

`compileER_runFor` resides under `namespace GebLean.LawvereERKSim`
(Top.lean:89). Inside `namespace GebLean` (which the plan opens
in Task 4 Step 1 and continues to in Tasks 9, 10, 11), the name
is `LawvereERKSim.compileER_runFor`, not bare
`compileER_runFor`. Same issue for unqualified
`compileER_runtime` references in Tasks 5–8 (line 669, 1029,
1148 etc.).

Additionally: after `rw [KSimURMSimulator.simulate_interp]`,
the LHS at that point is `(simulate (compileER e)).interp
(Fin.cons ((boundExprK e).interp v) v)`, but the rewrite
target's RHS is in terms of `Fin.cons y v`. The simp/rewrite
must first reduce the family `Fin.cons (boundExprK e) (fun i =>
KMor1.proj i)` applied (via `KMor1.interp_comp`) at vector `v`
to `Fin.cons ((boundExprK e).interp v) v`. The proj-component
identity `(KMor1.proj i).interp v = v i` is `KMor1.interp_proj`
(@[simp]); the plan does not invoke it. A `simp only
[KMor1.interp_comp, KMor1.interp_proj]` step is missing before
`rw [KSimURMSimulator.simulate_interp]`.

### B7: Task 13 `map_id` does not discharge by `rfl`

Task 13 Step 1 (line 1793–1809) closes
`erToKFunctor_map_id` after `apply Quotient.sound; intro v;
funext j` with the assertion (line 1808): `rfl`. The supporting
text claims "erToK ∘ proj = proj definitionally".

This is not definitional. `erToK (ERMor1.proj i) = KMor1.comp
(simulate (compileER (ERMor1.proj i))) (Fin.cons (boundExprK
(ERMor1.proj i)) (fun i => KMor1.proj i))` — a deeply nested
composition. Its *interp at v* equals `v i` only by going
through `erToK_interp`, which is *not* definitional and which
moreover carries an AXIOM_ALLOW dependency on
`simulate_interp` (and thus `Fin.lastCases_castSucc`). The
`Quotient.sound` discharge needs `rw [erToKN_interp]` (or the
underlying `erToK_interp`) to reduce both sides to `ERMor1.proj
j`'s interp, then close — not `rfl`.

This blocker also raises the AXIOM_ALLOW expectation at
`erToKFunctor_map_id` from "[propext, Quot.sound] only" (Task 13
Step 6, line 1866) to inheriting `Classical.choice` from
`erToK_interp` — a propagation the plan explicitly disclaims.

### B8: Task 5 `proj` case mis-types the bound

Task 5 Step 5 (line 743) writes `intro v` then enters the `proj i`
arm with `compileER_runtime, ERMor1.interp_proj`,
`boundExprKParams`. The recipe gives `proj i ↦ (2, 16)` (spec
§4.2 table); the runtime constant is `11 + 10·v i`. The
`offset` field is `16` per the recipe. The pseudo-Lean code at
line 749 shapes the calc as
`10 * (v i + 2) ≤ 10 * (Fin.maxOfNat _ v + 16) := by have := h_vi; omega`.
This holds (`v i + 2 ≤ Fin.maxOfNat _ v + 16`), but the next
chain step (line 753):

```text
  _ ≤ (Fin.maxOfNat _ v + 16) * tower 0 (Fin.maxOfNat _ v + 16)
      := by simp [tower]; nlinarith
```

requires `10 ≤ Fin.maxOfNat _ v + 16`, which holds, but
`nlinarith` needs to verify the multiplicative chain
`10 · (m+16) ≤ (m+16)^2` for `m+16 ≥ 10` and *over all `m`*.
This is fine, but the `simp [tower]; nlinarith` shape is not
"a single mul_tower_le_tower_add_two", as the spec rationale at
§4.2 ("Atoms" paragraph) claims. The proof shape the spec
advertises is `mul_tower_le_tower_add_two` with the linear
coefficient `10` absorbed in *one* step. The plan's atom-case
proofs all detour through `nlinarith` to prove
`(m+16) · (m+16) ≥ 10·(m+16)`, which is a separate step.
Either the spec's "single application of
mul_tower_le_tower_add_two" rationale is wrong, or the plan's
chain should be tighter. Either way the inconsistency between
spec and plan is a defect.

Same issue in Task 5 Step 4 (`succ`, line 717–732) and Task 5
Step 6 (`sub`, line 765–786).

### B9: Task 9 `boundExprK_interp` body does not type-check

Task 9 Step 3 (line 1340–1352):

```text
@[simp] theorem boundExprK_interp
    {a : ℕ} (e : ERMor1 a) (v : Fin a → ℕ) :
    (boundExprK e).interp v
      = tower (boundExprKParams e).1
              (Fin.maxOfNat _ v + (boundExprKParams e).2) := by
  simp only [boundExprK, KMor1.interp_comp,
    KMor1.interp_pow2_iter, KMor1.interp_add,
    KMor1.interp_maxOver, KMor1.interp_natK']
  rfl
```

`KMor1.interp_pow2_iter` (introduced in Task 3) has form
`(KMor1.pow2_iter r).interp ![x] = tower r x` (line 461–463) —
specialised to the arity-1 vector `![x]`. The boundExprK call
applies `pow2_iter p.1` at the result vector of a *family*
indexed by `Fin 1`. After `simp only [KMor1.interp_comp]`,
the LHS expands to `(KMor1.pow2_iter p.1).interp (fun _ : Fin 1 =>
…)`. To rewrite that to `tower p.1 …`, the simp engine must
recognise `(fun _ : Fin 1 => x) = ![x]` (i.e., `Fin.cons x
Fin.elim0`); this is not generally a simp normal form. The
plan's "`rfl`" close at the end is unlikely to discharge.

Either `KMor1.interp_pow2_iter` needs a generalised
form (`∀ v : Fin 1 → ℕ, (pow2_iter r).interp v = tower r (v 0)`)
established in Task 3, or Task 9's interp lemma needs an
explicit `change`/`congr` step to reshape the inner family.

## Serious

### S1: AXIOM_ALLOW site count contradicts itself

Workflow notes line 84–88 say "the three AXIOM_ALLOW sites
enumerated in spec §11". Spec §11 indeed enumerates exactly
three sites. But Task 15 Step 5 (line 1972) and the closeout
(line 2053) say "the five AXIOM_ALLOW'd sites" / "5 AXIOM_ALLOW
sites annotated", and the closeout commit message (line 2001)
echoes "confirm 5 AXIOM_ALLOW sites". Either the spec has been
extended without updating §11, or the plan has invented two
extra sites. The "additional" sites the plan implicitly counts
(see line 1972 "`erToKN_interp` and downstream") are inheritance
of `erToK_interp`'s annotation, not new annotated sites;
inheritance should not be re-counted.

Fix: standardise on the spec's 3-site count and remove the "5"
references.

### S2: Task 4 missing `lake build` between def and axiom audit

Per the plan's own TDD pattern (workflow notes line 110–115):
"(i) signature with `by sorry`, (ii) `lake build`, (iii) fill
the body, (iv) `lake build` clean, (v) per-declaration axiom
check, (vi) commit". Task 4 Step 3 (line 591–618) introduces the
full `boundExprKParams` body in one shot (no sorry intermediate);
this is acceptable because the body is a structural recursion
that elaborates as a unit, but the plan does not call this out
as an intentional deviation. Task 0's check at Step 4 confirms
clean baseline; Task 4's first `lake build` is Step 4 (after the
body), which is fine. Flag as documentation defect, not a
blocker.

### S3: `boundExprKParams` pattern match on `.zero` may not elaborate

Task 4 Step 3 (line 600–618):

```text
def boundExprKParams : {a : ℕ} → ERMor1 a → ℕ × ℕ
  | _, .zero    => (0, 3)
  | _, .succ    => (2, 16)
  ...
```

`ERMor1.zero : ERMor1 0`, `ERMor1.succ : ERMor1 1`, `ERMor1.sub :
ERMor1 2` (LawvereER.lean:36–48). The arity is fixed by the
constructor. Lean dependent pattern matching usually handles
this — but the explicit `_, .zero` with `_` placeholder is
unusual; the more idiomatic shape is `| .zero => (0, 3)` (with
the `a` argument elided to `_` in the entire match) or `|
(0 : ℕ), .zero => (0, 3)`. Worth a build check before committing
the recipe.

### S4: Task 11 `KMorN` arity for `erToKN`

Spec §8.1 (line 694) and plan Task 11 Step 3 (line 1633–1638)
both write `erToKN {n m : ℕ} (e : ERMorN n m) : KMorN n m := fun
j => erToK (e j)`. `KMorN n m := Fin m → KMor1 n`
(LawvereKSim.lean:65). `ERMorN n m := Fin m → ERMor1 n`
(LawvereER.lean:151). For `j : Fin m`, `e j : ERMor1 n`, so
`erToK (e j) : KMor1 n`. Type checks. OK.

But Task 12 Step 2 (line 1719–1724) builds:

```text
private def erToKN_atDepth {n m : ℕ}
    (e : ERMorN n m) :
    KMorNQuo.atDepth 2
      (Quotient.mk (kMorNSetoid n m) (erToKN e)) :=
  Quotient.mk _ ⟨erToKN e, erToKN_level e, rfl⟩
```

`erToKN_level e : ∀ j, (erToKN e j).level ≤ 2` per Task 11 Step
5 (line 1652–1654) — but Task 11 Step 5's signature is
`(j : Fin m) : (erToKN e j).level ≤ 2`, i.e. a function of `j`,
not a `∀ j, …` proof. To pass to a structure field expecting
`∀ j, level ≤ 2`, the worker must write `erToKN_level (e := e)`
or `fun j => erToKN_level e j`. The plan writes
`erToKN_level e`, which is the partial application — fine if
the `j` argument is inferred from the target. But more
seriously: the depth-2 witness structure (per the kToER mirror,
LawvereKSimER.lean:386–397) has fields `rep`, `rep_level`, and
`rep_eq`, not just two. The plan's three-field anonymous
constructor `⟨erToKN e, erToKN_level e, rfl⟩` may or may not
match the field order; the kToER side at line 387–388 packages
`⟨rec.rep, rec.rep_level⟩` for what *looks* like a two-field
constructor (`Quotient.mk _ ⟨rec.rep, rec.rep_level⟩`), but
the corresponding depth-2-witness type is more involved. The
plan should explicitly inspect `KMorNQuo.atDepth`'s definition
in `LawvereKSimQuot.lean` and instantiate its constructor by
name — relying on anonymous-constructor matching is fragile.

### S5: Tower lemma `tower_pow_le_tower_add_three` requires `m ≥ 2`

`Tower.lean:120` declares `tower_pow_le_tower_add_three
{k m : ℕ} (hm : 2 ≤ m) : tower k m ^ m ≤ tower (k + 3) m`. The
plan's bprod case (Task 8 Step 3, line 1172–1184) invokes it
implicitly. The hypothesis `m ≥ 2` must be discharged — bprod's
`m := Fin.maxOfNat _ v + ((boundExprKParams f).2 + 44) ≥ 44 ≥
2`, so it holds, but the plan does not stage the proof.

Same issue in bsum/comp uses of `mul_tower_le_tower_add_two`:
all require `2 ≤ m`, all are non-trivial to discharge if `v`
might be `Fin.elim0` (arity-0 vector). When `a = 0`,
`Fin.maxOfNat 0 v = 0`, so `m = 0 + offset = offset ≥ 2` only
because every recipe offset is `≥ 2`. The plan does not verify
this lower bound on the offsets (zero offset is 3, succ/proj 16,
sub 24, comp `≥ 8` only via `4·a + 8` which is 8 at `a = 0`,
bsum 32, bprod 44 — all ≥ 2, good). Add an `omega` lemma or
`have h_m : 2 ≤ m := by omega` at the top of each non-atom case.

### S6: Task 6 comp `glue` formula does not match `compileER_runtime` shape

Task 6 Step 5 (line 932–945) introduces:

```text
have h_glue :
    ((List.finRange k).map
      (fun i => compileER_runtime (gs i) v
        + 4 + 5 * (gs i).interp v
        + 9 * ((List.finRange a).map v).foldl (· + ·) 0
        + 2 * a)).foldl (· + ·) 0
      ≤ tower (mu_f + mu_g + 5) m := by
  sorry
```

The summand `+ 9 * ((List.finRange a).map v).foldl (· + ·) 0`
appears outside the per-`i` index and is the same `v_total`
constant for every `i`. The `4 + 5·val + 9·v_total + 2·a`
shape implies *each* sub-term carries a `v_total`. But the
spec's rationale (§4.2 comp paragraph (iii), p. 19–20 of the
spec text) describes the outer-glue absorption as exactly *one*
`9 · v_total` factor, not `k · 9 · v_total`. Either the spec
mis-states the runtime shape or the plan mis-transcribes; in
either case, `compileER_runtime e v`'s exact body should be
re-read at `Compiler.lean:1722–1770` and the per-`i` shape
should be cited verbatim in the plan.

### S7: Task 6 chain calls `Tower.tower_comp` with `ring_nf` for term reshape

Task 6 Step 4 (line 922–926): `_ = tower (mu_f + mu_g + 2) m :=
by rw [Tower.tower_comp]; ring_nf`. `Tower.tower_comp` has shape
`tower j (tower k x) = tower (j + k) x`. After `rw
[Tower.tower_comp]`, the result is `tower (mu_f + (mu_g + 2))
m = tower (mu_f + mu_g + 2) m`, which closes by `Nat.add_assoc`
(or `rfl` modulo associativity). `ring_nf` may close it; `omega`
won't (it acts on linear arithmetic over `ℕ`, not on identities
inside `tower`'s first argument unless rewritten further). Flag
as fragile.

### S8: TOC anchor-format consistency with T3 plan

The T3 plan (2026-05-21-step-t3-urm-to-ksim-simulator-plan.md)
uses the same doctoc-generated TOC layout. The T4 plan's TOC at
line 41–61 is correctly bracketed by `<!-- START doctoc -->` /
`<!-- END doctoc -->` markers. OK. No defect on this axis.

## Minor

### M1: `Fin.maxOfNat_succ` referenced but unproven

Task 2 Step 5 (line 370–372):

> If `simp [Fin.maxOfNat, Fin.foldr_succ]` does not close, use
> `Fin.maxOfNat_succ` (introduce it locally as a helper lemma
> in `LawvereKSim.lean` if not already present).

`Fin.maxOfNat_succ` is not in the codebase. `Fin.foldr_succ` is
in Lean core / mathlib and is used inside `Fin.le_maxOfNat`
(LawvereKSim.lean:121); the `simp [Fin.maxOfNat,
Fin.foldr_succ]` chain should work in principle. The "if not
already present, introduce it locally" instruction is fine but
should specify the lemma's exact statement, since the
recursive-equation form needs care about how `Fin.maxOfNat`
recurses on `n.succ`.

### M2: `KMor1.maxK` docstring claims level 1; should be ≤ 2

Task 1 Step 1 (line 183–189) docstring asserts "Level ≤ 2
(composition of `KMor1.add` at level 1 with `KMor1.monus` at
level 2 and projections at level 0)". `KMor1.add` has level 1
(KArith.lean:159 `example` proves it). `KMor1.monus` has level 2
(KArith.lean:472 `example` proves it). The composition has
level `max 1 2 = 2`. OK; docstring is accurate.

### M3: Commit message in Task 9 has bash-escape bug

Task 9 Step 8 (line 1397–1406):

```text
jj describe -m 'feat(ertok): assemble boundExprK from pow2_iter, maxOver, natK''

Composite shape: pow2_iter mu ∘ (add ∘ ⟨maxOver a, natK'' a offset⟩).
...
boundExprK_dominates'\''s runtime conjunct.
```

The single-quoted message body contains `''` (intended as an
escaped single quote inside `natK'`) — but inside a `'…'`
delimited string in bash, `''` terminates and immediately
re-opens the literal, leaving an empty inside. The intended
`natK'` literal renders as `natK` followed by end-of-string.
Use heredoc form or `\'` outside the single-quoted region.

The `'\''` later (line 1403) is correct bash escaping.

### M4: Mixed line widths in pseudo-Lean blocks

Many code blocks exceed mathlib's 100-character line width when
unindented (e.g. Task 6 Step 4 lines 891–895, Task 8 Step 5
lines 1206–1209). These are pseudocode and will be wrapped on
execution, but should be wrapped in the plan too for readability
and to set the right precedent for the worker.

### M5: Closeout LOC estimate off

Closeout (line 2016): "~1480 LOC. Comparable to T3." Spec §14
(line 952–961) estimates "Total ~1480"; T3 actual at PR
db059ef4 was ~1000 LOC (per spec §14 line 963). Plan's estimate
matches the spec; spec's "Comparable to T3" was already off
(T3 is ~1000, T4 estimate ~1480 — 48% larger). Carry-over
defect.

### M6: References section omits Tourlakis 0.1.0.27

Plan references at line 2094: "Tourlakis 2018
`PR-complexity-topics.pdf` §0.1.0.27, §0.1.0.37, §0.1.0.42,
§0.1.0.43, §0.1.0.44." Spec §15 (line 970–975) cites the same
five sections in different order. OK; non-issue. Strike from
review. (Retained for transparency that the comparison was
checked.)

## Methodology

For each blocker / serious finding, the cited
`docs/superpowers/plans/2026-05-22-step-t4-runtime-bound-plan.md`
text was located by `Read`, and the named declaration was
verified or refuted by direct inspection of:

- `/home/terence/git-workspaces/geb/geb-lean/GebLean/Utilities/Tower.lean`
- `/home/terence/git-workspaces/geb/geb-lean/GebLean/Utilities/KArith.lean`
- `/home/terence/git-workspaces/geb/geb-lean/GebLean/Utilities/KSimURMSimulator.lean`
- `/home/terence/git-workspaces/geb/geb-lean/GebLean/LawvereKSim.lean`
- `/home/terence/git-workspaces/geb/geb-lean/GebLean/LawvereKSimER.lean`
- `/home/terence/git-workspaces/geb/geb-lean/GebLean/LawvereER.lean`
- `/home/terence/git-workspaces/geb/geb-lean/GebLean/LawvereERKSim/Top.lean`
- `/home/terence/git-workspaces/geb/geb-lean/GebLean/LawvereERKSim/Compiler.lean`
  (header / signature lines only)
- `/home/terence/git-workspaces/geb/geb-lean/scripts/check-axioms.sh`
- `/home/terence/git-workspaces/geb/geb-lean/CLAUDE.md` and
  `.claude/rules/{lean-coding,markdown-writing,fork-upstream-flow}.md`
- The spec
  `/home/terence/git-workspaces/geb/geb-lean/docs/superpowers/specs/2026-05-22-step-t4-runtime-bound-design.md`

The T3 plan
`/home/terence/git-workspaces/geb/geb-lean/docs/superpowers/plans/2026-05-21-step-t3-urm-to-ksim-simulator-plan.md`
was inspected only structurally (TOC + workflow notes) for
format comparison; no T3 content was lifted into findings.

Mathlib upstream guides (re-fetched per `CLAUDE.md` § Mathlib
upstream guides binding) were not re-pulled in this round; the
local digest at `.claude/rules/lean-coding.md` was used for
style/naming/commit-message checks. The commit-message Task 9
heredoc bug (M3) is the only such finding.

No claim was forwarded that depended solely on the plan's own
self-reported invariants; every blocker is verified against the
authoritative codebase. Where verification was indirect (e.g.,
S4's "the depth-2 witness has more fields than the plan's
anonymous constructor accommodates"), the finding's confidence
is downgraded to "serious" rather than "blocker".
