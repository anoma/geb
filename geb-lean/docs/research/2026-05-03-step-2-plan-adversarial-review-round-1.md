# Adversarial review (round 1) of the step-2 plan
<!-- ER-side simultaneous bounded recursion -->

> Reviewer's stance: fresh adversarial reading of
> `docs/superpowers/plans/2026-05-03-step-2-er-simultaneous-bounded-rec.md`
> (commit `bad330f5`), against
> `docs/superpowers/specs/2026-05-03-step-2-er-simultaneous-bounded-rec-design.md`
> (commit `93b65e0a`), master design §3.2 / §15.13 in
> `docs/research/2026-05-02-er-ksim2-equiv-via-urm-master-design.md`,
> CLAUDE.md, and existing infrastructure
> (`GebLean/Utilities/Tupling.lean`,
> `GebLean/Utilities/ERTupling.lean`,
> `GebLean/Utilities/ERArith.lean`,
> `GebLean/Utilities/KSimSzudzikSimrec.lean`,
> `GebLean/LawvereERPolynomialBound.lean`).
> Tourlakis 2018 §0.1.0.7, §0.1.0.34, §0.1.0.35 verified by
> `pdftotext` extraction.

## Overall assessment

**The plan needs revision before implementation.** Two
defects are load-bearing — D1 (slot-arithmetic off-by-one in
`packedStepCtx`'s parameter branch) and D2 (slot-ordering
inconsistency between plan, spec, master design, and existing
ER infrastructure that propagates to type mismatches via the
`a + 1` vs `1 + a` non-defeq). One additional defect (D3) is
the `ofZero` vs `ofZeroN` confusion in Task 9. Several
concerns and minor items remain.

The bound formula
`tuplePackCoef k * (componentBound + 1)^(2^k)` and its
PolyBound derivation
`coefficient = tuplePackCoef k * (pb.coefficient + pb.constant + 1)^(2^k)`
both verify on independent algebraic checking. The Tourlakis
citations are substantively accurate but slightly imprecise
(C1 below).

Below: numbered findings with claim, finding, severity, and
recommended action.

---

## D1 — `packedStepCtx`'s parameter-branch projection index is off by one (defect)

**Claim under challenge.** Task 10.5 (and spec §5.1) defines
`packedStepCtx k a : Fin (1 + (k + 1) + a) → ERMor1 (1 + 1 + a)`
and routes the `s + 1`-input slot in the parameter branch
(when `¬ (s < k + 1)`) to `ERMor1.proj ⟨s - k, _⟩`.

**Finding.** This is off by one. The plan's slot convention
declares (Task 10.5 docstring; Task 13.1 helper docstring):

- Inner `(1 + 1 + a)`-context: slot 0 = counter, slot 1 =
  prev\_packed, slots 2..a+1 = parameters 0..a−1.
- Outer `(1 + (k + 1) + a)`-context: slot 0 = counter, slots
  1..k+1 = previous components, slots k+2..k+1+a = parameters
  0..a−1.

For an outer index `i = s + 1` falling into the parameters
range (`s + 1 ≥ k + 2`, equivalently `s ≥ k + 1`), the
parameter index is `p = (s + 1) − (k + 2) = s − k − 1`. The
target inner slot is `p + 2 = s − k + 1`, not `s − k`.

A concrete check at `s = k + 1` (the first parameter slot):
the outer index is `s + 1 = k + 2`, which is parameter 0. The
target inner slot is 2 (first parameter slot of the inner
context). The plan computes `s − k = 1`, which is the
prev\_packed slot. The projection would extract `prev_packed`
where the parameter is expected.

The Task 13.1 helper claims `interp_packedStepCtx`'s parameter
branch reduces to
`Fin.cons n (Fin.append (Nat.tupleAt k prev_packed) x) i`.
For outer index `i = s + 1` in the params range, this is
`x ⟨s - k - 1, _⟩` (an `a`-element vector). With the off-by-one
projection, the value extracted is `prev_packed` at
`s = k + 1`, then `x ⟨s - k - 2, _⟩` for higher `s` — a
shifted parameter vector with `prev_packed` in slot 0.

The plan's two `sorry` placeholders in Task 13.1's
`interp_packedStepCtx` proof would never close with the
present `packedStepCtx` definition.

**Severity.** Defect.

**Recommended action.** Replace `⟨s - k, _⟩` with
`⟨s - k + 1, _⟩` in Task 10.5's parameter-branch projection.
Update the `omega` proof obligation accordingly: we need
`s - k + 1 < 1 + 1 + a`, which follows from `s + 1 < 1 + (k + 1) + a`
and `s ≥ k + 1` (giving `s - k ≤ a`, hence `s - k + 1 ≤ a + 1 < a + 2`).
Also fix the docstring in Task 10.5 ("proj 2..k+2+a" — the
projection range only goes up to `a + 1`, not `k + 2 + a`).
Apply the same fix in the spec §5.1 (which has the same
definition).

---

## D2 — Slot-ordering inconsistency with master design (defect)

**Claim under challenge.** Tasks 10–17 declare arities using
`1 + (k + 1) + a`, `1 + 1 + a`, `1 + a`, with slot 0 =
counter, slots 1..k+1 = prev-vector, slots k+2..k+1+a =
parameters.

**Finding.** This contradicts every other layer of the
project:

1. **Master design §3.2 (lines 686–693)** declares
   `g : Fin (k + 1) → ERMor1 (a + 1 + (k + 1))` and
   `componentBound : ERMor1 (a + 1)`, returning
   `ERMorN (a + 1) (k + 1)`. The convention is slot 0 =
   counter, slots 1..a = parameters, slots a+1..a+k+1 =
   prev-vector. The plan reverses the parameter-vs-prev order
   and reorders `a + 1` to `1 + a`.

2. **Existing `kSimStepContext`** in
   `GebLean/Utilities/KSimSzudzikSimrec.lean` line 364 uses
   exactly this master-design layout
   (`Fin (a + 1 + (k + 1)) → ERMor1 (a + 2)`, with slot 0 =
   counter, slots 1..a = parameters, slots a+1..a+k+1 = prev
   components). Existing `kSimPackedStep g : ERMor1 (a + 2)`
   and `kSimTowerBound h g : ERMor1 (a + 1)` follow the same
   convention.

3. **Existing `ERMor1.boundedRec` substrate.** Its signature
   (`Utilities/ERArith.lean:1782-1799`) is
   `boundedRec (base : ERMor1 k) (step : ERMor1 (k + 2))`
   `(bound : ERMor1 (k + 1)) : ERMor1 (k + 1)`,
   and `boundedRec_eq_natRec_of_bounded` (line 2193) calls
   the step at `Fin.cons i (Fin.cons prev ctx)` — slot 0 =
   counter, slot 1 = prev, slots 2..k+1 = ctx, with the result
   at `Fin.cons n ctx`.

   The plan's Task 11 `simultaneousBoundedRec` instantiates
   `boundedRec` with what should be `k_b = a`. In Lean's Nat
   reduction, `1 + a` does **not** reduce to `a + 1` for
   variable `a` (`Nat.add` recurses on the second argument:
   `1 + a` cannot reduce while `a + 1 = succ a` does). So
   `boundedRec` with `k_b = a` produces `ERMor1 (a + 1)`,
   which is not definitionally equal to the plan's expected
   `ERMor1 (1 + a)`. The plan's `let packedRec : ERMor1 (1 + a)`
   binding would fail to elaborate without an `eqToHom`
   transport or a `change`.

   Similarly: Task 13.1's `interp_packedStepCtx` evaluates at
   `Fin.cons n (Fin.cons prev_packed x)`, whose type reduces to
   `Fin ((1 + a) + 1) → ℕ`, but `packedStepCtx k a i` expects
   input `Fin (1 + 1 + a) → ℕ`. These are not defeq.

4. **`Nat.simRecVec` step input convention.** Task 1.4 / spec
   §3.1 defines the step as
   `g_all j (Fin.cons n (Fin.append prev x))`, which gives
   slot 0 = counter, slots 1..k+1 = prev, slots k+2..k+1+a =
   parameters. This is the plan's chosen layout — internally
   consistent, but disagreeing with the ER side.

The slot-order discrepancy in (1)–(2) is a real conflict
with the master design's mathematical contract for the
interface; the `1 + a` vs `a + 1` mismatch in (3) prevents
Lean elaboration from succeeding.

**Severity.** Defect.

**Recommended action.** Settle the slot convention before
implementation. Two coherent options:

- **Option A (align with master design + existing
  `kSimStepContext`):** rewrite the plan to use
  `a + 1 + (k + 1)`, `a + 2`, `a + 1` arities with slot 0 =
  counter, slots 1..a = parameters, slots a+1..a+k+1 = prev.
  Re-state `Nat.simRecVec`'s step as
  `g_all j (Fin.cons n (Fin.append x prev))`. This minimizes
  drift from the master design, matches existing
  `kSimStepContext`, and aligns with `boundedRec`'s natural
  output type `ERMor1 (a + 1)`.
- **Option B (keep plan's layout):** add an explicit
  master-design amendment recording the slot reordering, plus
  insert `eqToHom` transports or rewrite-by-`Nat.add_comm`
  steps at every `boundedRec` boundary, plus update
  `Nat.simRecVec`'s call shape to use `Fin.cons n (Fin.append prev x)`
  consistently.

If neither is acceptable, this is a CLAUDE.md
"non-negotiable interface" violation: master design §3.2's
interface is the literature-fixed contract, and the plan
silently drifts from it. Option A is the literature-aligned
choice.

---

## D3 — Task 9 test uses `ofZero` with a non-existent `n` parameter (defect)

**Claim under challenge.** Task 9.2 includes test cases such as

```lean
example :
    (ERMor1.PolyBound.ofTuplePackedBound 0
       (ERMor1.PolyBound.ofZero (n := 0))).degree = 0 := rfl
```

**Finding.** `ERMor1.PolyBound.ofZero` in
`GebLean/LawvereERPolynomialBound.lean:128` is defined as

```lean
def ofZero : PolyBound ERMor1.zero where ...
```

It is `PolyBound`-of-`ERMor1.zero` (arity 0, no parameter `n`),
not `PolyBound`-of-`ERMor1.zeroN n`. The plan's spec §6.2
correctly references `ofZeroN 0`, but Task 9.2's transcription
uses `ofZero (n := 0)`, which will not elaborate. Task 17.2
also references `ofZeroN`, suggesting the plan-author knew
the right name but transcribed `ofZero` in Task 9 by mistake.

In addition, the plan's parenthetical at the end of Task 9.2
("`ERMor1.PolyBound.ofZero` produces a PolyBound with
`degree = 0`, ...") muddles the picture: `ofZero` is for
arity 0, while the test is at arity 0 — but the plan calls
`ofTuplePackedBound 1 (ofZero ...)`, expecting
`componentBound : ERMor1 0`. That is consistent with `ofZero`
(no `n` parameter) — but then the `(n := 0)` keyword argument
is meaningless and will be rejected.

**Severity.** Defect.

**Recommended action.** Replace `ofZero (n := 0)` with either
`ofZeroN 0` (matching `ERMor1.zeroN 0`) or plain `ofZero` (no
keyword argument; matching `ERMor1.zero`). Fix the post-hoc
explanation ("ofZero produces a PolyBound with degree = 0...")
to align with whichever choice is made. Update the
componentBound's expected ER value
(`tuplePackedBound k ERMor1.zero` vs
`tuplePackedBound k (ERMor1.zeroN 0)`).

---

## C1 — Tourlakis §0.1.0.35 vs §0.1.0.34 citation imprecision (concern)

**Claim under challenge.** The plan / spec consistently cite
"Tourlakis 2018 §0.1.0.35 (closure of E^{n+1} under
simultaneous bounded recursion)" as the literature
realization of `simultaneousBoundedRec`.

**Finding.** Verified by `pdftotext` extraction from
`PR-complexity-topics.pdf`:

- §0.1.0.34 (line 735 of the extract) is the **theorem**:
  "E^2 is closed under simultaneous bounded recursion, where,
  additionally to the standard schema, k bounding functions
  B\_i, for i = 1, …, k, are given, and the functions f\_i
  resulting from the schema must satisfy f\_i(x, ~y) ≤
  B\_i(x, ~y) everywhere." Its proof (lines 740–832) uses the
  pairing function `J = λxy.(x+y)^2 + x ∈ E^2`, the iterated
  pack `[[z_1, ..., z_k]]^{(k)}`, and notes the inequality
  `[[f_1(x, y), ..., f_k(x, y)]]^{(k)} ≤ [[B_1(x, y), ..., B_k(x, y)]]^{(k)}`.
  This is precisely the proof technique the plan
  implements.
- §0.1.0.35 (line 834) is the **corollary**: "E^n, for n ≥ 2,
  is closed under simultaneous bounded recursion." A
  one-line generalization of §0.1.0.34 to higher Grzegorczyk
  classes.

The plan's "(closure of E^{n+1} under …)" wording suggests
§0.1.0.35 covers all `n ≥ 0`, but Tourlakis's wording is
`n ≥ 2`. More substantively, the proof technique cited (the
pairing-based pack and the bounded-recursion closure
argument) is in §0.1.0.34, not §0.1.0.35.

The level-2 specialization that the master design uses is
exactly §0.1.0.34 (E^2 = K^sim\_2). §0.1.0.35 only matters
once we ascend to higher levels.

**Severity.** Concern (citation imprecision; not a
mathematical error).

**Recommended action.** Make §0.1.0.34 the primary citation
for `simultaneousBoundedRec` and its proof technique
(`Nat.tuplePack` pack-by-pairing, value bound). Cite §0.1.0.35
as the higher-level generalization (relevant for K^sim\_n
hierarchies for n ≥ 3, not used in the present
formalization). Update spec §7 and plan Task 18.2 citation
list. Adjust docstrings of `Nat.simRecVec`,
`ERMor1.simultaneousBoundedRec`, and
`simultaneousBoundedRec_interp_correct` accordingly.

---

## C2 — Task 13 sorry placeholders need concrete guidance (concern)

**Claim under challenge.** Task 13.1's `interp_packedStepCtx`
proof contains two `sorry` placeholders (at the two cases of
the `by_cases` on `h_prev`). Task 13.3's
`packedRec_eq_tuplePack_simRecVec` contains a single `sorry`
covering "the actual proof is ~40 lines". Both placeholders
are flagged as illustrative, and both must be filled before
commit (since `warningAsError = true` rejects `sorry`).

**Finding.** The placeholder in Task 13.3 has a concrete
proof outline (apply `boundedRec_eq_natRec_of_bounded`, do
induction on `n`, dispatch base via Task 12 and step via
Task 13.2). The implementer has enough to proceed. But:

1. The hypothesis discharge in Task 13.3 needs to invoke
   `packedBound_dominates_iter` (Task 14.1) and
   `packedBound_mono` (Task 14.2). These are defined
   **after** Task 13.3 in the plan's commit sequence (Task 14
   commits depend on Task 13 already being clean). The
   build-and-commit ordering forces Task 13's commit to land
   before Task 14's lemmas exist. The implementer cannot
   write a clean `packedRec_eq_tuplePack_simRecVec` proof
   without those helpers.

2. Task 13.1's `sorry` placeholders give no concrete tactic
   route. The proof needs `Fin.cons` / `Fin.append`
   simp-lemma chains to align the case `s + 1` with the
   target's `Fin.append` vector at index `s`. Even a sketch
   like "use `Fin.append_left` for `s < k + 1` and
   `Fin.append_right` for the params branch" would help.
   Without one, the implementer is left hunting for
   simp-lemma names.

3. Task 13.2's `packedStep_interp_eq_tuplePack_step` proof
   relies on `interp_packedStepCtx` (Task 13.1) being clean.
   With Task 13.1 stuck on placeholders, Task 13.2 cannot
   land cleanly either.

The "report `BLOCKED`" instruction (which uses an all-caps
non-acronym banned by CLAUDE.md, see M1 below) is also not
a substitute for a complete plan: an executing-plans agent
needs a concrete proof recipe.

**Severity.** Concern (the path is recoverable, but the
plan's commit-ordering and missing tactics force the
implementer into design work).

**Recommended action.** Reorder Tasks 13–14 so Task 14's
discharge lemmas land before Task 13.3 consumes them, or
combine 13.3 + 14 into one task. For Task 13.1, add at
least one of: (a) a concrete tactic chain naming the
`Fin.cons_zero`, `Fin.cons_succ`, `Fin.append_left`,
`Fin.append_right` simp lemmas; (b) a worked-out version
in the plan body for one of the two branches; (c) the
appeal to the existing `kSimStepContext_interp` lemma
(`KSimSzudzikSimrec.lean`), which already proves an
analogous slot-routing in the master-design layout. The
last is the cleanest if Option A from D2 is taken.

---

## C3 — `Nat.le_of_not_lt` may not be the right name (concern)

**Claim under challenge.** Task 10.5's `omega` invocation is
preceded by `have hs_ge : s ≥ k + 1 := Nat.le_of_not_lt h_prev`.

**Finding.** Verified by codebase search:
`Nat.le_of_not_lt` is used elsewhere
(`LawvereNatBTV2.lean:354`, `LawvereKSimQuot.lean:333`,
`LawvereTreeERQuot.lean:455`). The lemma exists and produces
`b ≤ a` from `¬ a < b` (i.e., `¬ a < b → b ≤ a`). The plan
uses it on `h_prev : ¬ (s < k + 1)`, which gives
`k + 1 ≤ s`, equivalently `s ≥ k + 1`. ✓

The construct as written should work. But note: `omega`
alone, with `h_in : s + 1 < 1 + (k + 1) + a` and the
implicit `h_prev`, can conclude `s - k + 1 < 1 + 1 + a`
(the corrected D1 bound), so the explicit `have hs_ge` is
unnecessary scaffolding. The implementer might omit the
intermediate `have` once D1 is corrected.

**Severity.** Minor.

**Recommended action.** No fix required, but consider
streamlining once D1 is addressed: the entire `by` script
can become a single `omega`.

---

## C4 — `simultaneousBoundedRec_interp_correct` outline omits dependent-rewrite (concern)

**Claim under challenge.** Task 15.1's proof outline is:

```lean
simp only [ERMor1.simultaneousBoundedRec,
  ERMor1.interp_comp, ERMor1.interp_tupleAt]
rw [ERMor1.packedRec_eq_tuplePack_simRecVec
      k a h g componentBound n x h_dominates h_mono]
rw [Nat.tupleAt_tuplePack]
```

**Finding.** After unfolding `simultaneousBoundedRec`, the
inner term is `ERMor1.comp (ERMor1.tupleAt k i) ![packedRec]`.
After `interp_comp`, it becomes
`(tupleAt k i).interp (fun _ : Fin 1 => packedRec.interp ctx)`.
After `interp_tupleAt`, it becomes
`Nat.tupleAt k (packedRec.interp ctx) i`.

But the `interp_tupleAt` lemma signature is

```lean
(tupleAt k i).interp ctx = Nat.tupleAt k (ctx 0) i
```

with `ctx : Fin 1 → ℕ`. The `ctx 0` is the result of
applying the function (`fun _ => packedRec.interp ctx`) at
index 0, which yields `packedRec.interp ctx`. The simp set
the plan provides should reduce, but `interp_tupleAt`
expects `Fin 1`-input, while the result of `interp_comp`
gives a `fun _ : Fin 1 => ...` lambda. Lean's `simp only`
may not collapse this lambda into a direct `interp` call
without `Matrix.cons_val_zero` or a `funext` step.

The plan flags this generally ("If the simp set above
doesn't close it cleanly, the implementer may need to add
`Matrix.head_fin_const` or case-split via `match` on the
`Fin 2` indices") but specifically for Task 6, not Task 15.

Same caveat applies to Task 12's
`packedBase_interp_eq_tuplePack_simRecVec_zero` and
Task 16's `ofSimultaneousBoundedRec`.

**Severity.** Concern (proof might not go through with the
literal tactics; implementer guidance needed).

**Recommended action.** Note in Task 15.1 (and 12, 16) that
`Matrix.cons_val_zero` and possibly a `change` to align the
`![packedRec]` lambda with `Fin 1`-application may be
needed. Or include explicit `change` steps in the proof
sketch to show how the lambda gets reduced.

---

## C5 — `ofSimultaneousBoundedRec`'s final `omega` is non-linear (concern)

**Claim under challenge.** Task 16.1's `bounds` proof ends
with

```lean
have h_component : ((sBR ... i).interp ctx
  ≤ packedRec.interp ctx) := ...
have h_bound : (packedRec.interp ctx ≤ tuplePackedBound.interp ctx) := ...
have h_poly := (PolyBound.ofTuplePackedBound k pb_bound).bounds ctx
omega
```

**Finding.** `omega` solves linear arithmetic over `ℤ` /
`ℕ`. The polynomial bound goal involves
`coefficient * (max + 1) ^ degree + constant`, a non-linear
expression in `max` and `degree`. After the three `have`s,
the goal is

```text
((sBR ... i).interp ctx) ≤ pb.coefficient * (M + 1) ^ pb.degree + pb.constant
```

where `M = (Finset.univ).sup ctx` and `pb` is the inherited
PolyBound. Chaining `h_component ≤ h_bound ≤ h_poly` is a
direct three-step `Nat.le_trans`, no arithmetic needed.

`omega` cannot close this — it does not know about `^` or
about the non-linear combination. The plan flags this as a
risk ("The `omega` at the end may not close the goal directly
if the inequality chain involves non-linear terms. Fallback:
`linarith [h_component, h_bound, h_poly]` or explicit
`Nat.le_trans` chain"), but `linarith` also doesn't do `^`.

The right tactic is `exact Nat.le_trans (Nat.le_trans h_component h_bound) h_poly`
or equivalent.

**Severity.** Concern.

**Recommended action.** Replace the placeholder `omega` in
Task 16.1 with `exact Nat.le_trans (Nat.le_trans h_component h_bound) h_poly`
(or `exact h_component.trans (h_bound.trans h_poly)`). Also
note: the simp + `change` machinery in the `have h_component`
script may not reduce the goal to the form
`Nat.tupleAt k packedRec.interp ctx i ≤ packedRec.interp ctx`
without a `change` step or further elaboration; verify on
implementation.

---

## C6 — `tuplePackedBound_dominates` calc chain is verbose (concern)

**Claim under challenge.** Task 7.1's proof of
`tuplePackedBound_dominates`:

```lean
have h_pack := Nat.tuplePack_le k v
have h_sup : (univ).sup v ≤ componentBound.interp ctx := ...
have h_pow_le :
    ((univ).sup v + 1) ^ (2 ^ k)
      ≤ (componentBound.interp ctx + 1) ^ (2 ^ k) := ...
calc Nat.tuplePack k v
    ≤ tuplePackCoef k * ((univ).sup v + 1) ^ (2 ^ k) := h_pack
  _ ≤ tuplePackCoef k * (componentBound.interp ctx + 1) ^ (2 ^ k) := ...
```

**Finding.** This is correct mathematically. But the
hypothesis form for `h_components`
(`∀ j, v j ≤ componentBound.interp ctx`) gives bound on
each component, while `h_sup` requires `(univ).sup v ≤
componentBound.interp ctx`. The plan derives `h_sup` via
`Finset.sup_le; intro j _; exact h_components j`. Verified —
this is the standard idiom.

The mathematical chain works. Minor: the proof produces an
intermediate term
`tuplePackCoef k * ((univ).sup v + 1) ^ (2 ^ k)` that is
neither the hypothesis nor the goal; this is fine but
verbose. A `calc` with `Nat.le_trans` could shorten.

**Severity.** Minor.

**Recommended action.** No change required; the proof
should work as written, modulo the `Nat.pow_le_pow_left`
mathlib API name (verify on implementation: the canonical
mathlib name is `Nat.pow_le_pow_left : h : m ≤ n → m^k ≤ n^k`).

---

## C7 — Task 4.3 `decide` may be slow or fail on the 2-component swap example (concern)

**Claim under challenge.** Task 4.3 includes the test

```lean
example :
    simRecVec 1 0
      (fun j _ => match j with | ⟨0, _⟩ => 1 | ⟨1, _⟩ => 2)
      (fun j ctx => match j with
        | ⟨0, _⟩ => ctx ⟨2, by decide⟩
        | ⟨1, _⟩ => ctx ⟨1, by decide⟩)
      5 (fun _ => 0) ⟨0, by decide⟩ = 2 := by decide
```

**Finding.** `simRecVec 1 0 ... 5 ...` recursively reduces
through five iterations of `Fin.cons` + `Fin.append`
constructions, with two component matches per iteration.
For `decide` to close, Lean's kernel must fully reduce all
Nat-level computations and `Fin.append`-projections to
boolean equality. Since these are all defined at the Nat
level (no `boundedRec`, no Gödel-numbering kernel
explosion), `decide` should handle this in reasonable time,
but the recursion through `Fin.append` may be slower than
hoped.

Note also: the `simp` lemmas `Nat.simRecVec_zero` and
`Nat.simRecVec_succ` are `rfl` lemmas, so unfolding by
`decide` should track. The `match` patterns inside the
step function (`⟨0, _⟩ => ctx ⟨2, by decide⟩`) are
WHNF-reducible, so kernel evaluation should proceed. Risk
is low.

**Severity.** Minor.

**Recommended action.** No change required, but flag as a
potential implementer-time concern: if `decide` times out, fall
back to a manual unfolding chain or use `native_decide`
(noted by CLAUDE.md as not preferred but acceptable for tests
when needed).

---

## C8 — `Nat.simRecVec_succ` `rfl` proof check (clean)

**Claim under challenge.** Task 2.1's
`@[simp] simRecVec_succ` lemma is proven by `rfl`, claiming
the statement reduces directly:

```lean
simRecVec k a h_all g_all (n + 1) x j
  = g_all j (Fin.cons n
      (Fin.append (simRecVec k a h_all g_all n x) x))
```

**Finding.** The `def simRecVec`'s `n + 1` arm is

```lean
| n + 1, x => fun j => g_all j (Fin.cons n
    (Fin.append (simRecVec k a h_all g_all n x) x))
```

Applying to `(n + 1) x j` directly gives the RHS. So `rfl`
should close — provided Lean's elaboration doesn't fight
the `Fin.append` shape. If `Fin.append` is opaquely defined
in mathlib (it isn't — it's a plain `def`), `rfl` works.

**Severity.** Clean.

**Recommended action.** None.

---

## C9 — `simRecVec_le_of_dominates` structural-recursion check (clean)

**Claim under challenge.** Task 3.1 declares
`simRecVec_le_of_dominates` by pattern-matching on the
counter `n` (`| 0, x, j` and `| n + 1, x, j`), recursing
in the step case:

```lean
| n + 1, x, j => by
    simp only [simRecVec_succ]
    apply h_step n x (simRecVec k a h_all g_all n x) j
    intro j'
    exact simRecVec_le_of_dominates k a h_all g_all
      componentBound h_base h_step n x j'
```

**Finding.** The recursive call is on `n` (decreasing
argument). For Lean's structural-recursion checker, `n` is
the first explicit argument (after `k a` are constants and
the `h_all` / `g_all` / `componentBound` / `h_base` /
`h_step` parameters are constants, then `n x j` is the
trio with structural `n`). Lean should accept this, since
all of `k`, `a`, `h_all`, `g_all`, `componentBound`,
`h_base`, `h_step` remain unchanged across the recursive
call. The match-on-`n`-only with constant `x, j` is the
standard pattern.

But: the parameters are listed as `(n : ℕ) (x : Fin a → ℕ) (j : Fin (k + 1))`
**after** the hypothesis arguments. In Lean's recursion
checker, all preceding args are typically generalized first.
The pattern match on `n` with `j` and `x` "captured" by
position is fine.

The `simRecVec_le_of_dominates k a h_all g_all componentBound h_base h_step n x j'`
recursive call uses the same arguments — `simp` may insert
`@simRecVec_le_of_dominates ...` with explicit args but
this is fine.

**Severity.** Clean.

**Recommended action.** None.

---

## C10 — `tuplePackedBound` `expER` and Gödel-numbering (clean)

**Claim under challenge.** Spec §8.1 Risk 3 notes "`2^k`
appearing as a literal large `Nat` for `k ≥ 4` makes
`decide`-based smoke tests slow; tests at `k ≤ 2` only."

**Finding.** Verified: `Nat.expER` and `tuplePackedBound`
mediated through `mulN`, `addN`, `expER`, `natN` produce
ER terms whose `.interp` evaluation routes through Gödel
numbering for `boundedRec`. The Step 1 lesson (per
CLAUDE.md "ER-side `.interp` test discipline (Gödel
numbering)") restricts ER-side `#guard`s to trivial arity.

The plan's Tasks 9 and 17 correctly limit tests to
PolyBound-shape verification (struct field access only).
This is consistent with the discipline. ✓

**Severity.** Clean.

**Recommended action.** None.

---

## C11 — `interp_tuplePackedBound` may need `Matrix.head_cons` (clean)

**Claim under challenge.** Task 6.1's proof of
`@[simp] interp_tuplePackedBound`:

```lean
simp only [ERMor1.tuplePackedBound, ERMor1.interp_comp,
  ERMor1.interp_mulN, ERMor1.interp_expER,
  ERMor1.interp_addN, ERMor1.interp_natN,
  Matrix.cons_val_zero, Matrix.cons_val_one,
  Matrix.head_cons]
```

**Finding.** The `tuplePackedBound` definition uses
`Matrix.cons` (`![ a , b ]`) with two-element matrices for
binary operations. After unfolding via `interp_comp`,
`interp_mulN`, etc., the `Matrix.cons`-shape lambdas appear
as `(![interp_a, interp_b]) i` for `i : Fin 2`. The simp
lemmas `Matrix.cons_val_zero` and `Matrix.cons_val_one`
together with `Matrix.head_cons` should reduce these.

But `Matrix.head_cons` reduces `![a, b].head` to `a`, not
`![a, b] 1`. For `Matrix.cons_val_one`, the lemma is
`![a, b] 1 = b` (or similar). Verify mathlib API at
implementation.

The plan flags this generally ("If the simp set above
doesn't close it cleanly, the implementer may need to add
`Matrix.head_fin_const` or case-split via `match`"). This
is consistent with step 1 task 8's approach — fine.

**Severity.** Clean.

**Recommended action.** None; matches step 1 pattern.

---

## M1 — All-caps "BLOCKED" used in plan body (minor)

**Claim under challenge.** Lines 1307 and 1438 use the
all-caps word "BLOCKED" in instructions to the implementer
("If the proof gets stuck, report `BLOCKED`"; "Report
status `BLOCKED` if you cannot fill it.").

**Finding.** CLAUDE.md says "Never use all-caps words
unless they're acronyms." `BLOCKED` is not an acronym. It
also (along with `block`) appears on the banned-words list
in CLAUDE.md.

**Severity.** Minor.

**Recommended action.** Replace with lowercase or rephrase
("report being stuck", "if the proof is not closing", etc.).

---

## M2 — Some plan lines exceed 80 characters (minor)

**Claim under challenge.** Plan lines should keep to ≤80.

**Finding.** Lines 1, 168, 554, 1031, 1134, 1451, 1920
exceed 80 characters. Most are unavoidable URLs (full
`docs/superpowers/specs/...md` paths) or shell commit
messages. The plan-author can wrap or shorten in markdown
prose, but `git commit -m` on a single line is constrained.

**Severity.** Minor.

**Recommended action.** Wrap the markdown prose lines
(168, 554, 1031, 1920) by splitting URL into "see [path]
for [context]" form across two lines. Commit-message lines
(1134, 1451) can use HEREDOC for multi-line commits.

---

## M3 — `Nat.simRec` `@[simp]` promotion deferred (minor)

**Claim under challenge.** Task 1.5's `Nat.simRec` is a
plain `def`. Spec §8.5 notes "Initially kept as plain
`def`. If downstream proofs frequently `unfold Nat.simRec`,
promote to `@[simp]` in a follow-up."

**Finding.** Without `@[simp]`, downstream proofs that
encounter `Nat.simRec ...` must explicitly unfold or use
`show`. With `@[simp]`, `Nat.simRec` would auto-unfold to
`Nat.simRecVec ... j`. Since `Nat.simRecVec` already has
`@[simp]` `_zero` and `_succ` lemmas, promoting `simRec` to
`@[simp]` would chain cleanly and likely simplify
downstream proofs.

The plan defers promotion to a follow-up. This is fine for
step 2's scope.

**Severity.** Minor.

**Recommended action.** No fix needed; consider promotion
during step-3+ if friction emerges.

---

## M4 — `ofTuplePackedBound` "no `3^E`-style coefficient" wording (minor)

**Claim under challenge.** Task 8.1's docstring claim:

> §15.13 punch-list claim ('no 3^E-style coefficient leaks
> out') satisfied: the coefficient depends only on (k, pb),
> not on the source K^sim term's structure.

**Finding.** The coefficient is
`tuplePackCoef k * (pb.coefficient + pb.constant + 1)^(2^k)`.
At fixed `k`, this is determined by the input PolyBound
`pb`. `pb` itself is a per-K^sim-term object, so the
coefficient does depend on the K^sim source. The claim is
that the **shape** (a polynomial bound, not a `3^E`-shape
tower) is independent of the K^sim source.

This is consistent with §15.13's wording ("no `3^E`-style
coefficient leaks out of `simultaneousBoundedRec`'s
implementation"). `3^E` is shorthand for "an `expER^E`
tower of height proportional to the source term's
`towerHeight`". The new bound is a polynomial in
`pb.coefficient + pb.constant + 1` raised to `2^k` —
polynomial in shape. ✓

The docstring wording could be sharper ("the coefficient
*shape* depends only on (k, pb_bound)'s shape, not on the
source K^sim term's structure"), but the substance is
correct.

**Severity.** Minor (wording precision).

**Recommended action.** Clarify the docstring phrasing in
Task 8.1 and Task 16.1: "the bound shape is polynomial,
with coefficient computed from `(k, pb.coefficient,
pb.constant)` — no tower / `expER` artefact."

---

## M5 — Tower-height arithmetic deferred to step 4 (minor)

**Claim under challenge.** Master design §3.2 (lines
750-757) includes "Tower-height arithmetic" prose: "If
`componentBound` is at ER tower height `h_c`, the
packed-state bound (derived in step 2) is at most height
`max(h_c, 2)`...". Spec §1.2 lists "Tower-height
arithmetic as an explicit theorem" as out-of-scope.

**Finding.** The plan does not produce a tower-height
lemma for `tuplePackedBound`. The master design's prose
hints the result is "stays at the same tower height as
componentBound" once `h_c ≥ 2`. If step 4's level-2
majorization arithmetic depends on this property (master
design §3.4 hints "the level-2 case using `A_2^r`'s
monotonicity"), step 4 will need it.

The plan flags this in spec §8.4 as a follow-up. Step 2's
scope is unaffected, but step 4 will need to add a
`tuplePackedBound_towerHeight_le` lemma or similar.

**Severity.** Minor (out-of-scope but flagged).

**Recommended action.** No change required for step 2.

---

## M6 — `simRec` unused-parameter warning risk (minor)

**Claim under challenge.** Task 1.5's `Nat.simRec`:

```lean
def simRec (k a : ℕ)
    (h_all : Fin (k + 1) → (Fin a → ℕ) → ℕ)
    (g_all : Fin (k + 1) →
      (Fin (1 + (k + 1) + a) → ℕ) → ℕ)
    (j : Fin (k + 1)) (n : ℕ) (x : Fin a → ℕ) : ℕ :=
  simRecVec k a h_all g_all n x j
```

**Finding.** All parameters appear in the body. No unused
warning. ✓

**Severity.** Clean.

**Recommended action.** None.

---

## M7 — `simRecVec_le_of_dominates` `h_step` form is asymmetric (minor)

**Claim under challenge.** Task 3.1's `h_step` form:

```lean
(h_step : ∀ n x prev j,
   (∀ j', prev j' ≤ componentBound n x) →
   g_all j (Fin.cons n (Fin.append prev x))
     ≤ componentBound (n + 1) x)
```

**Finding.** This passes `componentBound n x` as the bound
on the previous components (left-of-implication) and
demands the step output be bounded by
`componentBound (n + 1) x`. Asymmetric with respect to the
counter — the "previous" iteration's bound is at counter
`n`, but the next-iteration's bound is at counter `n + 1`.

For monotonic `componentBound` in `n` (which the master
design assumes via `h_mono`), this is the natural
formulation. For non-monotonic `componentBound`, the user
needs to provide a stronger `h_step`. ✓ matches Tourlakis
§0.1.0.34's formulation (each `f_i(x, ~y) ≤ B_i(x, ~y)` at
the *current* iteration).

**Severity.** Clean.

**Recommended action.** None.

---

## M8 — Spec §6.1 uses bare `simRecVec` after `open Nat` (minor)

**Claim under challenge.** Task 4.2 / spec §6.1 uses
`simRecVec 0 0 (fun _ _ => 5)` etc., relying on `open Nat`.

**Finding.** Task 4.1's test-module skeleton opens `Nat`
explicitly. Subsequent `#guard simRecVec ...` calls
resolve via the `open`. ✓

**Severity.** Clean.

**Recommended action.** None.

---

## M9 — Full project build deferred to Task 18 (minor)

**Claim under challenge.** Plan Task 18.1 runs
`lake build` and `lake test`, but each Task X.5 commits
after `lake build <Module>` only. The full project build
runs only at Task 18.

**Finding.** This is consistent with step 1's pattern. The
forced re-elaboration (`rm -f .olean && lake build
<Module>`) per task ensures the new module compiles
in isolation, and Task 18.1 force-rebuilds all six new
modules at the end.

**Severity.** Clean.

**Recommended action.** None.

---

## M10 — Task 8.1's `linarith`/`omega` mix uses non-trivial intermediate steps (minor)

**Claim under challenge.** Task 8.1's
`ofTuplePackedBound`'s `bounds` proof uses
`omega`-resolution at multiple steps:
`have h_const_le := Nat.le_mul_of_pos_right _ hpow_pos`,
`have := h_cb; omega`, `omega`.

**Finding.** Each `omega` call has explicit hypotheses
that should suffice for linear arithmetic. The non-linear
substitution `(A * X^d + B + 1) ≤ (A + B + 1) * X^d` is
done via the explicit calc-chain
`pb.coefficient * X^pb.degree + pb.constant + 1 ≤ ... = ...`,
which is correct (verified algebraically: at `X ≥ 1`,
`X^d ≥ 1`, so `B ≤ B * X^d`).

**Severity.** Clean.

**Recommended action.** None.

---

## M11 — Plan Task 18.4 `.session/workstreams` update path may not exist yet (minor)

**Claim under challenge.** Task 18.4 updates
`.session/workstreams/er-ksim2-equiv-via-urm.md`.

**Finding.** Repository contains
`.session/workstreams/` per CLAUDE.md. Whether the file
exists at this exact path was not verified — the plan
assumes step 1 created it. If step 1 didn't, this task
must `Create:` the file.

**Severity.** Minor.

**Recommended action.** Verify the file exists at session-
update time; create if absent.

---

## Summary

- **Total items reviewed:** 18 (D1–D3, C1–C11, M1–M11; some
  M-items are clean checks).
- **Defects:** 3 (D1, D2, D3 — must be fixed before
  implementation).
- **Concerns:** 7 (C1–C7 — should be addressed; some are
  citation/wording, others are tactic-level).
- **Minor items:** 11 (M1–M11 — wording, build-ordering,
  process; mostly tracker-level).
- **Clean items:** several within the M-range (M3, M6, M8,
  M9, M10).

**Overall assessment:** **plan needs revision.** The
slot-arithmetic off-by-one in D1 will cause the
`packedStepCtx` and `interp_packedStepCtx` proofs to fail
to elaborate. The slot-ordering inconsistency in D2 will
cause type mismatches between the plan's
`simultaneousBoundedRec` and the existing `boundedRec`
substrate, and silently drifts from the master design's
mathematical contract for the interface. D3 is a
straightforward typo that will prevent Task 9 from compiling.

Recommended sequence:

1. Resolve D2 by choosing Option A (align with master
   design + existing `kSimStepContext`) or Option B (record
   the slot reordering as a master-design amendment with
   `eqToHom` transports).
2. Fix D1's off-by-one in `packedStepCtx`. With Option A's
   reordering this becomes `s + 1` (param 0 maps to inner
   slot 1) — re-derive in either case.
3. Fix D3's `ofZero` / `ofZeroN` typo in Task 9.
4. Refine C1's citation to §0.1.0.34 (the actual theorem
   the plan implements).
5. Reorder Task 13–14 dependencies per C2.
6. Tighten Task 15.1 / 16.1 proof outlines per C4 / C5.

After D1–D3 are fixed and the citation in C1 is corrected,
the plan should be coherent enough to enter implementation.
