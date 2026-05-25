# T4 plan adversarial review — round 2

Round-2 adversarial review of
[`docs/superpowers/plans/2026-05-22-step-t4-runtime-bound-plan.md`](../superpowers/plans/2026-05-22-step-t4-runtime-bound-plan.md)
at jj revision `66dbb02c` on `feat/ertok-runtime-bound`,
against
[`docs/superpowers/specs/2026-05-22-step-t4-runtime-bound-design.md`](../superpowers/specs/2026-05-22-step-t4-runtime-bound-design.md),
the round-1 review at
[`docs/research/2026-05-22-step-t4-plan-adversarial-review-round-1.md`](2026-05-22-step-t4-plan-adversarial-review-round-1.md),
and the authoritative project sources cited inline.

## Summary

- Residual blockers from round 1: 1 (B6 partially)
- Newly-escalated blockers (round-1 deferred): 0
- Newly-introduced blockers (from round-1 fixes): 0
- Residual serious: 2 (S4, S6 deferred)
- Newly-escalated serious (round-1 deferred): 1 (B8 reclassified)
- Newly-introduced serious: 1 (Task 10 `Fin.cons` family
  normalisation)
- Minor: 3

Round-1 blockers B1, B2, B3, B4, B5, B7, B9 are addressed.
B6 is partially addressed (namespace qualification fixed; the
inserted `simp only [Fin.cons_zero, Fin.cons_succ]` step does
not actually achieve the family normalisation the proof needs;
see N1). Round-1 deferred items B8 and S5 are now addressed by
the workflow note; S3 and S6 remain unaddressed. The plan does
not yet converge.

## Round-1 fix verifications

### B1 — `KMor1.level_*` simp lemmas: ADDRESSED

The workflow notes at lines 98–109 of the revised plan
acknowledge that `KMor1.level_*` simp lemmas do not exist and
adopt the `example : <decl>.level = N := by decide` /
`unfold <decl> ; Nat.max_le.mpr ⟨…, …⟩` + `Fin.maxOfNat_le`
pattern (mirroring `KSimURMSimulator.lean:975-984`'s
`simulate_level`). Tasks 1 (Step 6, lines 299–311), 2 (Step 6,
lines 440–462), 3 (Step 4, lines 549–570), 9 (Step 4, lines
1469–1486), and 10 (Step 5, lines 1592–1605) follow this
pattern. Tasks 2, 3, 9, 10 carry intentional `sorry` TDD
scaffolds at the open-arity level lemmas; the implementer
fills following the `simulate_level` chain. Pattern matches
the codebase convention at `KArith.lean:38, 72, 106, 159,
217, 264` (single-pattern `example` lines) and
`KArith.lean:290–308` (open-arity `natK_level`).

Confirmed against `LawvereKSim.lean:146-156` (`KMor1.level`
definition) and `KSimURMSimulator.lean:975-984`
(`simulate_level` discharge pattern).

### B2 — `Tower.tower_mono_both`, `Tower.tower_ge_two`: ADDRESSED

The workflow notes at lines 111–130 enumerate the actual
Tower surface and instruct the implementer to synthesise
`tower_mono_both` inline as
`(tower_mono_left h₁ _).trans (tower_mono_right _ h₂)`. The
plan no longer references the non-existent
`Tower.tower_mono_both` or `Tower.tower_ge_two`. Task 6 Step 4
(lines 980–998) explicitly stages the synthesis inline.

Confirmed against `Tower.lean:27, 42, 51, 65, 102, 120`
(actual exposed surface).

### B3 — `Tower.self_le_tower` 3rd-arg removal: ADDRESSED

`grep -n "self_le_tower _ _" plan.md` returns lines 808–809,
837, 993, 994, 996, 1004, 1083 — all two-argument invocations.
No `Tower.self_le_tower _ _ (by omega)` (three-argument)
forms remain. Workflow note at line 113 explicitly states
the two-argument signature.

### B4 — `check-axioms.sh` file-path argument: ADDRESSED

All `bash scripts/check-axioms.sh` invocations in the revised
plan pass file paths:

- Line 320: `GebLean/Utilities/KArith.lean` (Task 1).
- Line 476: `GebLean/Utilities/KArith.lean` (Task 2).
- Line 576: `GebLean/Utilities/KArith.lean` (Task 3).
- Line 702: `GebLean/LawvereERKSim/RuntimeBound.lean`
  (Task 4).
- Line 1365: `GebLean/LawvereERKSim/RuntimeBound.lean`
  (Task 8).
- Line 1502: `GebLean/LawvereERKSim/RuntimeBound.lean`
  (Task 9).
- Line 1656: `GebLean/LawvereERKSim/ErToK.lean` (Task 10).
- Line 1804, 1890, 2002, 2054: `GebLean/LawvereERKSim/ErToKFunctor.lean`
  (Tasks 11–14).
- Line 2113: no arguments (Task 15, full-project audit).

All shapes match the script's argument parser at
`scripts/check-axioms.sh:75-135`. Workflow-note line 82–96
explains that the script auto-discovers declarations.

### B5 — sorry-spans-tasks workflow: ADDRESSED

The workflow notes at lines 158–170 explicitly carve out a
"joint-commit exception" for Tasks 5–8, declaring that
`boundExprKParams_dominates`'s four inductive cases land
together as Task 8's commit. The exception is named and
scoped ("No other task carries this exception"). Tasks 5
Step 8 (line 873–882), 6 Step 10 (line 1099–1103), 7 (no
final commit step), and 8 Step 12 (line 1373–1396)
internally consistent.

The deviation from "task = commit" semantics is now
documented; the SDD harness invoking this plan must treat
Tasks 5–8 as one logical commit unit.

### B6 — `compileER_runFor` namespace: PARTIALLY ADDRESSED

Task 10 Step 6 (line 1611–1618) explicitly addresses the
namespace qualification:

> Note: `compileER_runFor` and `compileER_runtime` reside in
> `namespace GebLean.LawvereERKSim` (Top.lean / Compiler.lean);
> inside `namespace GebLean` the qualified path is
> `LawvereERKSim.compileER_runFor`.

And line 1642 writes `LawvereERKSim.compileER_runFor`.
Confirmed against `Top.lean:89-99` (closes `LawvereERKSim`
and `GebLean` namespaces in that order) and
`Compiler.lean` (also under `namespace GebLean.LawvereERKSim`).

The added `simp only [KMor1.interp_comp, KMor1.interp_proj,
Fin.cons_zero, Fin.cons_succ]` at line 1631 partially
addresses the missing-simp half of B6, but does NOT actually
achieve the family normalisation needed. See N1 below.

The `compileER_runtime` references in Tasks 5–8 (e.g., lines
771, 783, 821, 843, 900, 1119, 1239) remain unqualified;
since these tasks operate inside `namespace GebLean`, the
unqualified references will fail to resolve to
`LawvereERKSim.compileER_runtime`. Same fix needed: prefix
each `compileER_runtime` with `LawvereERKSim.` (or `open
GebLean.LawvereERKSim` at the top of `RuntimeBound.lean`).
This was a residual half of B6; not addressed in the revision.

### B7 — Task 13 `map_id` rfl claim: ADDRESSED (with caveat)

Task 13 Step 1 (line 1940–1948) replaces the `rfl` close with
`rw [erToKN_interp]; rfl`. The trailing `rfl` is plausible
because after the rewrite both sides reduce to `(KMor1.proj
j).interp v` and `(ERMor1.proj j).interp v`, each of which is
definitionally `v j` (per `LawvereKSimInterp.lean:98-101` and
`LawvereER.lean:110-113`, both of which prove `rfl`).

However, the actual goal after `apply Quotient.sound; intro v;
funext j` is the equality of two `KMor1`-interps (the
quotient is on `KMorN`, not `ERMorN` × `KMorN`), so
`erToKN_interp` rewrites one side from `(erToKN (e_repr) j).interp v` to
`(e_repr j).interp v` (where `e_repr j = ERMor1.proj j`); the
other side (the `ERMorNQuo`-side identity representative
`fun j => KMor1.proj j`) is already in `(KMor1.proj j).interp
v = v j` shape after `KMor1.interp_proj`.

But wait — `Quotient.sound` operates on the `KMorN`-side
quotient (since `erToKFunctor_map e : KSimMor 2 n m` whose
underlying `hom : KMorNQuo n m`); so the equality being
discharged is:

```text
Quotient.mk _ (erToKN (𝟙 n in ERMorN)) = Quotient.mk _ (KMorN.id n)
```

which under the setoid relation becomes
`∀ v j, (erToKN _ j).interp v = (KMorN.id n j).interp v`.
LHS reduces by `erToKN_interp` and the ER `𝟙`'s representative
to `(ERMor1.proj j).interp v = v j`; RHS reduces by
`KMor1.interp_proj` to `v j`. Then `rfl` closes (both sides
are syntactically `v j`).

Note line 1945–1948's annotation correctly claims this proof
INHERITS the AXIOM_ALLOW from `erToK_interp`. Confirmed
against the kToER analogue at
`LawvereKSimER.lean:412` (closes by `rfl` because in *that*
direction, `kToER (KMor1.proj i)` reduces definitionally to
`ERMor1.proj i`; the reverse direction needs the explicit
rewrite step the plan now does).

### B8 — atom nlinarith vs single Tower lemma (escalated to R-S1)

The plan's atom proofs (Task 5 Steps 4–6, lines 781–863) all
use a calc chain ending with `apply Tower.mul_tower_le_tower_add_two`,
but the chain step *before* that absorbs the linear
coefficient via `nlinarith`:

```text
_ ≤ (Fin.maxOfNat _ v + 16) * tower 0 (Fin.maxOfNat _ v + 16)
    := by simp [tower]; nlinarith
```

The spec's §4.2 atoms paragraph (lines 219+) describes the
atom rationale as a single `mul_tower_le_tower_add_two`
application. Strictly speaking the plan's chain uses one
`mul_tower_le_tower_add_two` PLUS one `nlinarith` step to
arrange `X · X` first. This is consistent if "single
application of mul_tower_le_tower_add_two" is read as
"the only Tower lemma cited is `mul_tower_le_tower_add_two`"
(with `nlinarith` being a Nat-side preparation). But the spec
rationale's phrasing implies a single end-to-end step. See
R-S1 below.

### B9 — `KMor1.interp_pow2_iter` ![x] vs Fin 1 family: ADDRESSED

Task 9 Step 3 (line 1431–1443) adds the prerequisite that
Task 3's `KMor1.interp_pow2_iter` must be stated in
`(v : Fin 1 → ℕ) ↦ tower r (v 0)` form, not the `![x]` form.
Task 3 Step 3 (lines 530–546) writes the lemma as
`∀ (r x : ℕ), (KMor1.pow2_iter r).interp ![x] = tower r x`,
which is the `![x]` form — Task 3's signature was NOT updated
to match Task 9's prerequisite. The plan now has an internal
inconsistency between Task 3's actual signature (`![x]`) and
Task 9's prerequisite (`v 0`). See R-S2 below.

### S1 — AXIOM_ALLOW count standardisation: ADDRESSED

All references in the revised plan are to "the three primary
AXIOM_ALLOW sites" (workflow note line 86–88, Task 15 Step 5
line 2115). The Task 13 Step 1 (line 1945) note explicitly
states the `erToKFunctor_map_id` inherits AXIOM_ALLOW from
`erToK_interp` (not a new site). No remaining "5" references.

### S5 — Tower lemma `2 ≤ m` hypothesis: PARTIALLY ADDRESSED

Workflow note line 124–128 states: "Tasks 5-8 must stage the
`2 ≤ m` hypothesis (every recipe offset is `≥ 3`, so
`m = Fin.maxOfNat _ v + offset ≥ 3 ≥ 2`)." The per-task
proofs partly comply: Task 5 Steps 4–6 each invoke
`mul_tower_le_tower_add_two` and close the `2 ≤ m` side with
`omega` (lines 805–806, 834, 859). Task 6 Step 4 line 1012
similarly. Task 8 Step 3 (line 1265–1274) calls
`tower_pow_le_tower_add_three` from a `sorry`-bodied helper
without showing the discharge; the implementer must thread
`2 ≤ m`. This is acceptable since the workflow note covers it.

## Residual blockers

### R-B1: Task 5–8 `compileER_runtime` namespace qualification missing

The plan's `RuntimeBound.lean` skeleton (Task 4 Step 1, line
617–662) opens `namespace GebLean` but does NOT open
`GebLean.LawvereERKSim`. Tasks 5–8 then reference
`compileER_runtime` unqualified at lines 746, 771, 783, 821,
843, 900, 1119, 1147, 1239, 1316 (and many more inside the
proof bodies). Per the existing fix to B6 (Task 10 Step 6
line 1611–1618), the qualified name is
`LawvereERKSim.compileER_runtime`. Tasks 5–8 will not
elaborate as written.

Fix: either prefix every `compileER_runtime` reference in
Tasks 5–8 with `LawvereERKSim.`, or add an
`open LawvereERKSim` line to Task 4's module skeleton.

The plan's revision addressed the equivalent issue at Task 10
(`compileER_runFor`) but did not propagate the fix backward
to Tasks 5–8's `compileER_runtime` references. This is a
hard build-failure issue (Lean will report "unknown
identifier `compileER_runtime`" at the first `simp only`
unfolding).

Severity: blocker (every Task 5–8 step fails at the unfold).

## Residual serious

### R-S1: atom proofs use `nlinarith` not consistent with spec's "single application"

(From round-1 B8 deferred.) Spec §4.2 (atoms paragraph)
describes the atom rationale as a single
`mul_tower_le_tower_add_two`. Plan Task 5 Steps 4–6 invoke
`mul_tower_le_tower_add_two` once but require a preliminary
`nlinarith` to establish `X · X` first. The chain works (`10
· (m+16) ≤ (m+16) · (m+16)` because `m+16 ≥ 10` follows from
`offset ≥ 10`; the offsets are 3, 16, 16, 24 respectively —
zero is 3, which is < 10). For the `zero` case (Task 5 Step
3, line 770–774), the runtime is the constant `3`, the
`offset` is `3`, and `tower 0 m = m ≥ 3`, so the chain
collapses to `omega` (no `mul_tower_le_tower_add_two` needed).
For `succ`/`proj`/`sub` (offsets 16, 16, 24), `m+offset ≥
offset ≥ 10`, so `nlinarith` for `10 · (m+offset) ≤
(m+offset)^2` holds.

The inconsistency between spec rationale ("single
application") and plan implementation (`nlinarith` + one
`mul_tower_le_tower_add_two`) is a documentation defect:
either the spec should be reworded to "one
`mul_tower_le_tower_add_two` (after `nlinarith` setup)" or
the plan's atom proofs should be reshaped to genuinely
single-step (e.g., increase the recipe offsets to make the
linear coefficient inequality direct rather than
multiplicative). Carry forward.

Severity: serious (defect of plan/spec consistency, not of
elaboration).

### R-S2: Task 3 `interp_pow2_iter` signature mismatch with Task 9 prerequisite

(From round-1 B9 follow-through.) Task 9 Step 3 (line 1431–
1443) explicitly states a prerequisite that Task 3's
`KMor1.interp_pow2_iter` be stated in `(r : ℕ) (v : Fin 1 →
ℕ) ↦ tower r (v 0)` form. Task 3 Step 3 (line 530–546) still
writes the lemma in the `(r x : ℕ) ↦ ![x]` form. The plan's
fix to B9 noted the prerequisite but did not edit Task 3's
signature to match.

Fix: update Task 3 Step 3 to use the generalised form, as
the plan's own §B9 fix explicitly directs ("rather than the
`![x]` form. The proof's `simp [tower]` step then closes
after `Fin 0`-vector destruction. Update Task 3 Step 3
accordingly.").

Severity: serious — the prerequisite is named but not
implemented. Without the fix, Task 9 Step 3's `simp only
[..., KMor1.interp_pow2_iter, ...]` will not fire (or will
fire in the wrong shape and leave a goal Lean cannot close
by `rfl`).

### S3 — `boundExprKParams` `_, .zero` pattern (deferred from R1; not addressed)

The plan still writes (Task 4 Step 3, line 678–696):

```text
def boundExprKParams : {a : ℕ} → ERMor1 a → ℕ × ℕ
  | _, .zero    => (0, 3)
  | _, .succ    => (2, 16)
  ...
```

Lean dependent pattern matching usually handles this, but the
`_` placeholder on the implicit `a` argument is unusual. The
idiomatic shape is `| .zero => (0, 3)` (relying on the
constructor to determine `a`). This may elaborate; the safer
form is to drop the `_`. Mark as serious because Lean's
dependent-match elaborator can be finicky with explicit `_`
in implicit positions; the plan should default to the
constructor-only pattern.

Severity: serious (potential elaboration failure).

### S4 — Task 12 `KMorNQuo.atDepth` packaging: NOT ADDRESSED

The plan's Task 12 Step 2 (lines 1846–1852) writes:

```text
private def erToKN_atDepth {n m : ℕ}
    (e : ERMorN n m) :
    KMorNQuo.atDepth 2
      (Quotient.mk (kMorNSetoid n m) (erToKN e)) :=
  Quotient.mk _ ⟨erToKN e, erToKN_level e, rfl⟩
```

Per `LawvereKSimQuot.lean:375-396`, `KMorNQuo.atDepth d q` is
the quotient of a structure with three fields:
`rep : KMorN n m`, `rep_level : ∀ i, (rep i).level ≤ d`,
`rep_eq : Quotient.mk _ rep = q`. The plan's
`⟨erToKN e, erToKN_level e, rfl⟩` triple does not match field
order checked at runtime — `erToKN_level e` has signature
`(j : Fin m) → (erToKN e j).level ≤ 2` (from Task 11 Step 5,
line 1779–1785), a function of `j`, not a `∀ j, …` proof.
The anonymous constructor will need `(fun j => erToKN_level e j)`
or Lean's elaboration may infer it; this is fragile.

Further, the kToER analogue at `LawvereKSimER.lean:411-417`
(`KMorNQuo.id_atDepth`) builds with NAMED fields, not
anonymous constructor:

```text
def KMorNQuo.id_atDepth {n d : ℕ} :
    KMorNQuo.atDepth d (KMorNQuo.id n) :=
  Quotient.mk _ {
      rep        := KMorN.id n,
      rep_level  := fun _ => by ...,
      rep_eq     := rfl }
```

The plan should mirror the named-field form, not anonymous
constructor.

Fix: rewrite Task 12 Step 2 to use named fields:

```text
private def erToKN_atDepth ... :=
  Quotient.mk _ {
      rep := erToKN e,
      rep_level := fun j => erToKN_level e j,
      rep_eq := rfl }
```

Severity: serious (anonymous-constructor matching is
fragile; the kToER analogue uses named fields).

### R-S3 (deferred from R1's S6): comp `glue` formula and `9·v_total` per-i shape

The plan's Task 6 Step 5 (line 1023–1037) writes the glue
formula with the per-i shape including `9 * v_total + 2 * a`
inside each per-`i` summand. Verified against
`Compiler.lean:1727-1739`:

```text
| a, .comp (k := k) f gs, v =>
    let inner : Fin k → ℕ := fun i => (gs i).interp v
    let v_total : ℕ := ((List.finRange a).map v).foldl (· + ·) 0
    let glue : ℕ :=
      ((List.finRange k).map
        (fun i => compileER_runtime (gs i) v
          + 4 + 5 * inner i
          + 9 * v_total + 2 * a)).foldl (· + ·) 0
    glue + compileER_runtime f inner + 2
```

`9 · v_total` IS per-i (inside the `(fun i => …)` mapped
over `List.finRange k`). The plan's transcription matches
`Compiler.lean`'s shape.

But the spec rationale (referenced as "the per-i `+ 9 *
v_total` shape may be wrong") was the round-1 deferral. The
plan's transcription correctly carries the `9 * v_total` per
each `i`, summing `k · 9 · v_total` over the outer fold. The
bound proof must therefore absorb `k · 9 · v_total` as a
factor of `k · m · m`, not just `9 · v_total ≤ m · m`. The
recipe's `+ 4·a + 8` offset and `+ 6` mu_g+mu_f+6 tower
height must be sufficient to dominate `k · 9 · v_total`. This
is a non-trivial proof obligation; the plan's "implementer
must check whether the bound discharges at +6 (via tighter
absorption chains) or whether the recipe needs to be revised
to +7" note (line 1056–1058) flags the risk without
resolving it.

Severity: serious — the recipe is fixed by literature, but
the bound may not discharge at `+6` once `k · 9 · v_total`
is factored in. If `+7` is needed, every downstream tower
estimate shifts and Task 13/14 verifications need updating.

## New issues (from round-1 fixes)

### N1: Task 10 Step 6 family-normalisation simp is insufficient for `simulate_interp`

After `simp only [KMor1.interp_comp]` at Task 10 Step 6 (line
1631), the goal is approximately:

```text
(simulate (compileER e)).interp
    (fun j => (Fin.cons (boundExprK e) (fun i => KMor1.proj i) j).interp v)
  = e.interp v
```

For `rw [KSimURMSimulator.simulate_interp]` to fire, the
argument must unify with `Fin.cons y v_rest` (Lean-syntactic),
where `y` and `v_rest` are arbitrary. The current shape is a
`fun j => ...` whose body destructures `j` via `Fin.cons`.

The `simp only [KMor1.interp_proj, Fin.cons_zero,
Fin.cons_succ]` step is intended to reduce the `interp_proj`
on the projection slots and beta-reduce the `Fin.cons`
destruction. But `Fin.cons_zero` and `Fin.cons_succ` only
fire when `j` is `0` or `Fin.succ k` — they don't fire under
a `fun j => …` lambda where `j` is bound.

The standard rewrite to "merge `fun j ↦ (Fin.cons a as j).interp v`"
into `Fin.cons (a.interp v) (fun i ↦ (as i).interp v)`
requires either:

- `funext` followed by `cases j using Fin.cases` with
  explicit handling of zero/succ branches, OR
- a custom rewrite lemma like
  `Fin.cons_interp_distrib`, OR
- a `show` step asserting the family is `Fin.cons ((boundExprK
  e).interp v) v` and closing the equality via funext.

The plan does not supply any of these. After
`simp only [KMor1.interp_comp, KMor1.interp_proj,
Fin.cons_zero, Fin.cons_succ]`, the family will still appear
in `fun j => (Fin.cons ... j).interp v` form, and
`rw [simulate_interp]` will not fire (or will fail to unify).

The fix is to add a `change`/`show` step that asserts the
family equals `Fin.cons ((boundExprK e).interp v) v`, with
`funext` and case analysis on the `Fin` index, before
applying `simulate_interp`:

```lean
have h_family :
    (fun j => (Fin.cons (boundExprK e) (fun i => KMor1.proj i) j).interp v)
      = Fin.cons ((boundExprK e).interp v) v := by
  funext j
  refine Fin.cases ?_ ?_ j
  · simp [Fin.cons_zero]
  · intro k; simp [Fin.cons_succ, KMor1.interp_proj]
rw [h_family, KSimURMSimulator.simulate_interp]
```

Severity: serious — the proof as written will fail at the
`rw [simulate_interp]` step. The fix is mechanical but not
automatic.

### N2: Task 13 functor laws missing AXIOM_ALLOW annotations

Task 13 Step 1 (lines 1944–1949) claims `erToKFunctor_map_id`
inherits AXIOM_ALLOW from `erToK_interp` via `erToKN_interp`.
But `Quotient.sound` itself is `[propext, Quot.sound]`-only
(per `LawvereKSimQuot.lean` instances) — that part is fine.
The proof body uses `rw [erToKN_interp]` which transitively
depends on `erToK_interp`'s `Classical.choice` annotation.

Spec §11 (line 879–886) explicitly excludes `map_id` and
`map_comp` from the AXIOM_ALLOW site count: "AXIOM_ALLOW
annotation does not propagate further than these three
sites. Notably: `erToKFunctor.map_id` and
`erToKFunctor.map_comp` rely on `erToK_interp`'s value
identity ... but the quotient operations themselves
... are `[propext, Quot.sound]`-only, so the functor laws
inherit the AXIOM_ALLOW only via `erToK_interp`."

The spec says map_id/map_comp INHERIT the AXIOM_ALLOW but
are not new sites. The plan's Task 13 Step 6 line 2003–2009
correctly states this. No new defect — but the spec text and
plan text together are technically saying "the axiom set is
inherited from erToK_interp", which means the
`#print axioms` output of `erToKFunctor_map_id` will include
`Classical.choice`. The `check-axioms.sh` script does NOT
automatically propagate AXIOM_ALLOW annotations from a
called declaration to its caller — every flagged
declaration must carry its own annotation OR the caller
must avoid the path that pulls the axiom.

Verify: a transitive AXIOM_ALLOW does not need explicit
annotation if the script's auto-allowlist behaviour
suppresses it. Re-reading `scripts/check-axioms.sh`
(modification 2 of the local-vs-upstream diff): "if a
declaration is immediately preceded ... by ... lines of the
form `-- AXIOM_ALLOW: <axiom-name> (optional rationale)` and
every axiom flagged for that declaration appears in the
collected AXIOM_ALLOW set, the declaration is suppressed".
The script suppresses per-declaration. So
`erToKFunctor_map_id` and `erToKFunctor_map_comp` will both
appear as flagged unless they carry their own AXIOM_ALLOW
annotation OR their `Classical.choice` set is empty.

The plan's Task 13 does not add an explicit AXIOM_ALLOW
annotation to `erToKFunctor_map_id` or
`erToKFunctor_map_comp`. The axiom audit will report them as
defects unless they're annotated.

Fix: Task 13 needs to add `-- AXIOM_ALLOW: Classical.choice
(inherits via erToKN_interp / erToK_interp; see spec §11)`
above both `erToKFunctor_map_id` and
`erToKFunctor_map_comp` declarations.

Severity: serious (the axiom audit will fail at Task 13's
final step without the annotations).

## Minor

### M1: residual `Fin.maxOfNat_succ` reference (carry-over from round-1 M1)

Task 2 Step 5 (line 426–429) still references the
non-existent `Fin.maxOfNat_succ`:

> If `simp [Fin.maxOfNat, Fin.foldr_succ]` does not close,
> use `Fin.maxOfNat_succ` (introduce it locally as a helper
> lemma in `LawvereKSim.lean` if not already present).

This is a fallback hint, not a hard reference. Acceptable as
a TDD-recovery hint. Carry-over from round 1; no fix needed.

### M2: Task 6 preamble does not acknowledge Task 5's deferred commit

Task 6's preamble (line 887–894) does not mention that the
working-copy state coming in carries `sorry`-bearing code from
Task 5. The workflow note at line 158–170 covers this
abstractly; a per-task header reminder would aid the SDD
implementer.

Severity: minor (workflow-clarity issue).

### M3: closeout LOC estimate carry-over from round 1's M5

Closeout (line 2162): "~1480 LOC. Comparable to T3." T3 was
~1000 LOC at PR `db059ef4`; T4 estimate ~1480 is 48% larger.
Round-1 flagged this; round-2 has not corrected.

Severity: minor.

### M4: markdownlint check passes

Confirmed: `markdownlint-cli2
docs/superpowers/plans/2026-05-22-step-t4-runtime-bound-plan.md`
reports 0 errors.

## Methodology

Each round-1 finding was located in the revised plan by line
number. The cited declarations and lemma signatures were
verified against:

- `GebLean/Utilities/Tower.lean` (lines 17, 27, 42, 51, 65,
  102, 120).
- `GebLean/Utilities/KArith.lean` (lines 38, 72, 106, 159,
  217, 264, 290–308, 315, 320–325 for level patterns).
- `GebLean/Utilities/KSimURMSimulator.lean` (lines 548,
  958–984 for `simulate`, `simulate_interp`, `simulate_level`
  surface).
- `GebLean/LawvereKSim.lean` (lines 146–162 for `KMor1.level`
  definition; 65, 86–140 for `KMorN`, `Fin.maxOfNat`).
- `GebLean/LawvereKSimInterp.lean` (lines 80–125 for
  `KMor1.interp` and its `interp_*` simp lemmas).
- `GebLean/LawvereKSimQuot.lean` (lines 375–469 for `KSimMor`,
  `KMorNQuo.atDepth`, `KMorNQuo.id_atDepth`,
  `KMorNQuo.comp_atDepth`).
- `GebLean/LawvereKSimER.lean` (lines 384–474 for
  `kToERFunctor_map`, `kToERFunctor_map_id`,
  `kToERFunctor_map_comp` mirror).
- `GebLean/LawvereER.lean` (lines 82–114 for `ERMor1.interp`
  and its `interp_*` simp lemmas).
- `GebLean/LawvereERKSim/Top.lean` (lines 80–97 for
  `compileER_runFor` namespace and signature).
- `GebLean/LawvereERKSim/Compiler.lean` (lines 1720–1770 for
  `compileER_runtime`'s comp/bsum/bprod shapes).
- `scripts/check-axioms.sh` (lines 75–135 for argument
  parsing; modification 2 documentation for AXIOM_ALLOW
  scanning).
- Spec at
  `docs/superpowers/specs/2026-05-22-step-t4-runtime-bound-design.md`
  (lines 219, 425, 844–886 for atoms rationale and §11 axiom
  budget).

The mathlib upstream guides
(`https://leanprover-community.github.io/contribute/{naming,style,doc,commit}.html`)
were not re-pulled in this round; the
`.claude/rules/lean-coding.md` local digest sufficed for
style / naming / commit-message checks. No new commit-message
defects beyond round-1 M3 (which is fixed in the revised
plan via the `$'...\\n...'` form at line 1512).

The plan is markdownlint-clean per the standard
`.markdownlint-cli2.jsonc` configuration.
