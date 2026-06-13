# Adversarial review — era-open-laws plan, round 1

Reviewer: fresh-context agent. Artifact:
`docs/superpowers/plans/2026-06-12-era-open-laws-plan.md`.
Sources checked: `GebLean/Era.lean` (full, working tree, builds
clean), the converged spec
`docs/superpowers/specs/2026-06-12-era-open-laws-design.md` and
its three review rounds, the project rules (`CLAUDE.md`,
`.claude/rules/lean-coding.md`,
`.claude/rules/markdown-writing.md`). Every Lean signature and
every definitional-equality (`rfl`) claim in the plan was
elaborated against `Era.lean` in a scratch module (since
removed); results are reported under each finding and under
"Checks with no finding". The [Goo54] PDF was not available in
this environment (`/tmp/goodstein1954.pdf` absent); the
equation-number citations are assessed against the spec's
provenance table (§2) and spec review-1, which checked them
against the PDF.

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Summary](#summary)
- [Findings](#findings)
  - [RP1-m1 (Minor) — plan lacks a doctoc table of contents](#rp1-m1-minor--plan-lacks-a-doctoc-table-of-contents)
  - [RP1-m2 (Minor) — Task 3.5 names a forward-dependent route then retracts it](#rp1-m2-minor--task-35-names-a-forward-dependent-route-then-retracts-it)
  - [RP1-m3 (Minor) — Task 4b.3 omits an explicit open-dependency line](#rp1-m3-minor--task-4b3-omits-an-explicit-open-dependency-line)
  - [RP1-m4 (Minor) — Task 3.7 cites `numeral_mul` for an `edmul`-headed dividend](#rp1-m4-minor--task-37-cites-numeral_mul-for-an-edmul-headed-dividend)
  - [RP1-m5 (Minor) — Task 1.1 docstring attribution of Goodstein (7) is loose](#rp1-m5-minor--task-11-docstring-attribution-of-goodstein-7-is-loose)
- [Checks with no finding](#checks-with-no-finding)
- [Verdict](#verdict)

<!-- END doctoc -->

## Summary

| # | Severity | Title |
| --- | --- | --- |
| RP1-m1 | Minor | The plan has eleven `##` headings but no doctoc TOC; recent plans carry one and the paired spec carries one |
| RP1-m2 | Minor | Task 3.5 Step 2 names `derivable_zero_div` (Task 3.7) as a route before retracting it for the numeral route; the muddle invites the forward dependency it then disclaims |
| RP1-m3 | Minor | Task 4b.3 (`pow_zero`, verified reduction) omits the explicit "Depends on Task 4a.3" line that the parallel verified reductions 4a.4 and 4a.5 carry |
| RP1-m4 | Minor | Task 3.7 cites `numeral_mul` for reducing an `edmul`-headed dividend; only `numeral_dmul` (or the already-proven `edmul_zero`) applies |
| RP1-m5 | Minor | Task 1.1 docstring attributes `succ_add` to "Goodstein 1954 (7)"; (7) is the interchange `a+Sb=Sa+b`, and `succ_add` is a combination, as the parenthetical half-acknowledges |

No Blocker and no Major findings. All theorem and definition
signatures elaborate; every definitional-equality (`rfl`) claim
holds; no cited lemma is missing; the dependency order contains
no cycle and no forward dependency.

## Findings

### RP1-m1 (Minor) — plan lacks a doctoc table of contents

`.claude/rules/markdown-writing.md` § Tables of contents:
"Every committed Markdown document with more than one `##`
heading carries an auto-maintained table of contents at the
top." The plan has eleven `##` headings (lines 34, 50, 70, 84,
180, 274, 334, 555, 816, 985, 1024) and no
`<!-- START doctoc -->` / `<!-- END doctoc -->` markers.
`markdownlint-cli2` reports zero errors, so this is not caught
by the linter; it is the separate TOC rule. The paired spec
(`2026-06-12-era-open-laws-design.md`) carries a TOC, and recent
plans (`2026-05-17-*` onward) do as well.

Fix: `doctoc docs/superpowers/plans/2026-06-12-era-open-laws-plan.md`
once to insert the markers, then
`doctoc --update-only docs/superpowers/plans/`; re-verify
`markdownlint-cli2` clean afterward.

### RP1-m2 (Minor) — Task 3.5 names a forward-dependent route then retracts it

Task 3.5 (`mul_zero`) Step 2 (lines 462–470) reads: "then
`0 /ᵉ numeral 2 = 0` by `derivable_zero_div` (Task 3.7)
instantiated, or directly by the numeral route `numeral_div 0 2`.
To avoid a forward dependence on Task 3.7, close via
`numeral_div`/`numeral_mul`…". Naming `derivable_zero_div`
(Task 3.7, later in the same phase) as a candidate route, then
retracting it, leaves a worker who reads only the first sentence
liable to introduce exactly the forward dependence the plan's
own self-review (lines 1038–1041) says it avoids. The retraction
is correct and the numeral route is verified (see "Checks with
no finding"): `numeral_div 0 2 : Derivable eraDefs ⟨numeral 0 /ᵉ
numeral 2, numeral 0⟩`, and `numeral 0 = .zero` definitionally,
so it closes `⟨.zero /ᵉ numeral 2, .zero⟩` directly.

Fix: delete the `derivable_zero_div`-first clause; state only the
`numeral_div 0 2` route. (Mention of `numeral_mul` is also
unnecessary here — the dividend `0 /ᵉ numeral 2` is closed by
`numeral_div` alone.)

### RP1-m3 (Minor) — Task 4b.3 omits an explicit open-dependency line

Tasks 4a.4 (`sub_zero`) and 4a.5 (`pred_succ`) each open with an
explicit dependency line ("Depends on Task 4a.3 (domination).",
lines 697, 729). Task 4b.3 (`pow_zero`) is the third "verified
reduction given domination" and consumes the domination family
in its Step 2 ("converted by `esubAt_of_add` from the domination
instance `2^(u+1) = u +ᵉ .succ (.succ t)`", lines 918–920), but
its subheading only says "given domination" (line 901) without
the parallel "Depends on Task 4a.3" line. Dimension-D check: the
dependency is present in the step body, so this is a
consistency/visibility gap, not a missing dependency.

Fix: add "Depends on Task 4a.3 (domination)." to Task 4b.3's
preamble, matching 4a.4/4a.5.

### RP1-m4 (Minor) — Task 3.7 cites `numeral_mul` for an `edmul`-headed dividend

Task 3.7 (`zero_div`) Step 2 (line 532): "the dividend then
reduces by numerals (`numeral_dmul`/`numeral_mul`) to `.zero`."
After `0 %ᵉ S u → 0` and `0 ∸ᵉ 0 → 0`, the dividend is
`edmul (.succ .zero) .zero` (the `ediv` unfolding has an `edmul`
head, verified by `rfl`). `numeral_mul` is the computation lemma
for `*ᵉ` (`emul`), not `edmul`, so it does not apply to this
term. `numeral_dmul 1 0 : edmul (numeral 1) (numeral 0) =
numeral 0` does apply (`.succ .zero = numeral 1`, `.zero =
numeral 0` definitionally), as does the already-proven
`derivable_edmul_zero` (Task 3.4).

Fix: drop `numeral_mul` from the citation; cite `numeral_dmul`
or, more economically, `derivable_edmul_zero`.

### RP1-m5 (Minor) — Task 1.1 docstring attribution of Goodstein (7) is loose

Task 1.1 (line 193) docstring: "`S u + v = S (u + v)`
(Goodstein 1954 (7), combined with the defining `u + S v =
S (u + v)`)". Per the spec provenance table (§2, line 53) and
spec review-1 (which checked the citations against the PDF,
review-1 lines 213–219), Goodstein (7) is the interchange
`a + Sb = Sa + b`. The theorem `derivable_succ_add` states
`succ_add` (`S u + v = S(u + v)`), which is not (7) itself but
the combination of (7) `a+Sb=Sa+b` with `add_succ`
`a+Sb=S(a+b)`. The parenthetical "combined with the defining
`u + S v = S(u + v)`" does signal a combination, so the
attribution is defensible; it would be more precise to name (7)
as the interchange law rather than leave the reader to infer
that "(7), combined with …" is not a direct transcription of (7).

Fix (optional): "the successor/addition interchange, from
Goodstein 1954 (7) `a + Sb = Sa + b` together with the defining
`u + S v = S(u + v)`".

## Checks with no finding

Signature elaboration (each stated theorem/def in the plan was
elaborated against `Era.lean`; all compile, with only the
expected `sorry` placeholders):

- Task 0.1 `derivable_zero_add {n} (u : ETm n) : Derivable
  eraDefs ⟨(.zero : ETm n) +ᵉ u, u⟩` — elaborates. The
  generalization claim (prove the `.var 0` case at scope 1 then
  `Derivable.inst (fun _ => u)`, or reproduce `uniq` at scope
  `n`) is sound against the `example` at lines 440–463, whose
  three `uniq` premises (`base`, `stepF`, `stepG`) are the same
  shapes.
- Task 0.2 `Derivable.ext_succ` — signature elaborates with the
  premise shapes `F.subst (sub0 .zero)` / `F.subst bump`
  matching `uniq`'s first two premise slots
  (`Era.lean` 146–147). The H-weakening construction was tested:
  `Derivable.uniq (H := (F.subst bump).subst skipPrev) h0 ?_ ?_`
  elaborates with `h0` accepted directly as `uniq`'s base
  premise (`skipPrev := fcons (.var 0) (fun i => .var i.succ.succ)`
  inserts a dummy at the previous-value slot). The remaining two
  premises (`F.subst bump = H.subst (recArgs F)` and `G.subst
  bump = H.subst (recArgs G)`, the latter reducing to `hS.symm`)
  are well-typed obligations; the substitution-commutation
  bookkeeping is left to `lean4:prove`, which is acceptable for
  this project.
- Task 4a.1 `esubAt` def and `esub_eq_esubAt … := rfl` —
  confirmed: with `esubAt e s t := ((eexp2 e +ᵉ s) %ᵉ (eexp2 e
  +ᵉ t)) %ᵉ (eexp2 e +ᵉ s)`, the equation `s ∸ᵉ t = esubAt
  (s +ᵉ t) s t` closes by `rfl` (the two sides are syntactically
  identical after `esub` unfolds with `e := s +ᵉ t`). The plan's
  defeq claim holds.
- Task 4a.2 `derivable_esubAt_of_lt` and
  `derivable_esubAt_of_add` — both signatures elaborate. The
  `esubAt_of_lt` inner-remainder step (`derivable_mod_lt (eexp2 e
  +ᵉ u) d : ⟨(eexp2 e +ᵉ u) %ᵉ ((eexp2 e +ᵉ u) +ᵉ .succ d),
  eexp2 e +ᵉ u⟩`) typechecks, matching the sketch.
- Task 3.5 `mul_zero` numeral route — `u *ᵉ .zero = edmul u
  .zero /ᵉ Tm.numeral 2` by `rfl`; after `edmul u .zero → .zero`
  the goal `⟨.zero /ᵉ numeral 2, .zero⟩` is closed by
  `numeral_div 0 2` directly (`exact (numeral_div 0 2)`
  elaborates), confirming `numeral 0 = .zero` and `numeral (0/2)
  = .zero` defeq. The chain works as the prompt anticipated.
- Task 3.4 `edmul_zero` — `edmul t .zero = esq (t +ᵉ .zero) ∸ᵉ
  (esq t +ᵉ esq .zero)` by `rfl`, matching the unfolding the
  sketch reduces.
- Task 3.6 `div_zero` — `u /ᵉ .zero = edmul (.succ u) (u ∸ᵉ (u
  %ᵉ .zero)) %ᵉ (edmul (.succ u) .zero ∸ᵉ one)` by `rfl`; the
  reduction chain (`axMod0`, `sub_self`, `edmul_zero`,
  `pred_zero`, `axMod0`) uses only prior lemmas.
- Task 3.7 `zero_div` — `(.zero) /ᵉ .succ u = edmul (.succ
  .zero) (.zero ∸ᵉ (.zero %ᵉ .succ u)) %ᵉ (edmul (.succ .zero)
  (.succ u) ∸ᵉ one)` by `rfl`, matching the unfolding.
- Task 4b.3 `pow_zero` — `u ^ᵉ .zero = eexp2 ((u *ᵉ .zero +ᵉ u
  +ᵉ one) *ᵉ .zero) %ᵉ (eexp2 (u *ᵉ .zero +ᵉ u +ᵉ one) ∸ᵉ u)` by
  `rfl`, matching `epow` (`Era.lean` 1009–1010). The modulus
  arithmetic the prompt asked about checks: `1 = .succ .zero`,
  and `derivable_mod_lt one d : ⟨one %ᵉ (one +ᵉ .succ d), one⟩`
  elaborates, so once `esubAt_of_add` converts the modulus to a
  `.succ`-shaped divisor `one +ᵉ .succ d` (equivalently `.succ
  (.succ t)` after additive normalization), `1 %ᵉ (modulus) = 1`
  follows by `mod_lt`. The reduction is sound given domination.
- Task 4b.4 `derivable_div_succ` — the precedence-sensitive
  statement `⟨.succ u /ᵉ .succ v, (u /ᵉ .succ v) +ᵉ (one ∸ᵉ (v
  ∸ᵉ (u ∸ᵉ .succ v *ᵉ (u /ᵉ .succ v))))⟩` parses and elaborates
  identically to the §4 deliverable (`*ᵉ` at 70 binds tighter
  than `∸ᵉ` at 65).
- `derivable_mod_lt` actual signature is `(u v : ETm n) :
  Derivable eraDefs ⟨u %ᵉ (u +ᵉ Tm.succ v), u⟩` — matches the
  shape the plan relies on throughout (Tasks 2.1, 3.1, 4a.2,
  4b.3). `numeral_div` actual signature is `(a b : Nat) :
  Derivable eraDefs ⟨numeral a /ᵉ numeral b, numeral (a / b)⟩` —
  matches Task 3.5's use.

Dependency ordering (dimension C; no cycle, no forward
dependency):

- Phase 0 → 1 → 2 → 3 → 4a → 4b as the plan and spec §6 state.
- Phase 3 internal order verified: 3.1 `zero_sub` uses ext_succ
  (0.2), mod_self (2.2), zero_mod (2.1); 3.2 `sub_self` uses
  mod_self/zero_mod; 3.3 `pred_zero` uses zero_sub (3.1); 3.4
  `edmul_zero` uses sub_self (3.2) + `numeral_sq` (exists); 3.5
  `mul_zero` uses edmul_zero (3.4) + `numeral_div` (exists),
  explicitly not 3.7; 3.6 `div_zero` uses mod_zero (exists),
  sub_self (3.2), edmul_zero (3.4), pred_zero (3.3); 3.7
  `zero_div` uses zero_mod (2.1), sub_self (3.2), numeral
  lemmas. The prompt's stated ordering analysis is correct.
- Phase 1 base-availability: `succ_add` (1.1) base needs only
  add_zero; `add_comm` (1.2) base is `zero_add` (0.1);
  `add_assoc` (1.3) base is add_zero. Consistent with spec §6
  Phase 1.

Open-obligation honesty (dimension D):

- Tasks 4a.3, 4a.6, 4b.1, 4b.4 are each marked OPEN in their
  headers and carry the staged-exit protocol (4a.3 Step 3; 4a.6
  Step 5; 4b.1 Step 3; 4b.4 Step 4), consistent with spec §9 and
  the plan's self-review (lines 1033–1037). None instructs
  extending `eraDefs`; each routes an impasse to the
  stuck-and-ask template.
- The verified-reduction tasks 4a.4 and 4a.5 state their
  dependence on the open Task 4a.3 explicitly; 4b.3 states it
  only in-step (see RP1-m3).

Process:

- Plan header matches the writing-plans required header (title +
  "For agentic workers" REQUIRED SUB-SKILL block + Goal +
  Architecture + Tech Stack).
- All 24 commit subjects are `feat(era): <lowercase imperative>`,
  no trailing period, each under 72 characters — compliant with
  `.claude/rules/lean-coding.md` § Commit messages.
- `markdownlint-cli2` reports zero errors on the plan.
- No `sorry`/`admit`/`_` placeholder is left in the plan as a
  deliverable (the `sorry` bodies in the stated signatures are
  task-internal stand-ins removed before each commit, per the
  Conventions block lines 52–55; this matches the project
  `sorry` policy).
- New declaration names follow conventions: `derivable_*`
  theorems in `snake_case`; `Derivable.ext_succ` and `esubAt`
  consistent with existing `Derivable.symm`/`esub` naming;
  `esubAt` is a `def` in `lowerCamelCase`.
- Axiom-hygiene step present per task (`#print axioms` /
  `lean_verify`, contained in `{propext, Quot.sound}`), and the
  final audit (Task F.1) runs `check-axioms.sh` and greps for
  `sorry`/`admit`.
- `eraDefs`-unchanged invariant is asserted and checked
  (Task F.1 Step 4); the only edit to existing code is the Task
  0.1 example-to-theorem promotion, which is additive in API.

## Verdict

Pass with minors. No Blocker and no Major findings: every Lean
signature elaborates, every `rfl`/defeq claim holds, every cited
lemma exists, the dependency order is acyclic with no forward
dependency, and the open obligations are honestly isolated with
the staged-exit protocol. The five Minor findings are a missing
doctoc TOC (RP1-m1), two citation/route imprecisions inviting a
disclaimed forward dependency (RP1-m2, RP1-m4), one
dependency-line consistency gap (RP1-m3), and one loose
literature attribution (RP1-m5) — all fixable by local edits to
the plan, none blocking execution.
