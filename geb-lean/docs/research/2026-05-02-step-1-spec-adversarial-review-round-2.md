# Adversarial review (round 2) of the step-1 spec — ER-side tupling

> Reviewer's stance: fresh round-2 read of
> `docs/superpowers/specs/2026-05-02-step-1-er-tupling-design.md`
> at the post-round-1-fixes revision (commit `d1241116`). Round-1
> review (`2026-05-02-step-1-spec-adversarial-review-round-1.md`)
> read for context on what is already verified or addressed; this
> round focuses on (a) verifying the round-1 fixes hold without
> introducing new defects, and (b) catching what round 1 missed,
> particularly around the existing `LawvereERQuot.lean` interface,
> downstream consumers in step 2 and beyond, and the orientation
> of the §1.4/§1.3 conventions. Source materials read end-to-end:
> the spec under review; round-1 review;
> `LawvereER.lean` (lines 140-260), `LawvereERQuot.lean`
> (full); `LawvereERDelta.lean` for usage-pattern cross-check;
> master design §3.1, §3.2, §3.7, §15.12; CLAUDE.md
> banned-words list and discipline notes.

## Overall assessment

**The round-1 fixes substantively address D1, D3, D4, D11, and
D13. D2 is partially addressed but exposes two new defects in the
quotient-class notation that round 1 did not catch.** The
mathematical content remains correct (round-1 verifications stand);
the new findings are interface-level and centred on the spec's
unverified assumption that `⟦·⟧`/`≈` notation works against
`erMorNSetoid`, when in fact `erMorNSetoid` is declared as a
plain `def` rather than an `instance` of `Setoid`. Two of the
findings below would block the spec's §4.4 / §5.3 from compiling
as written; they are individually small edits but they are real.

Below: numbered findings with claim, finding, severity, and
recommended action. Items E1–E4 are new defects/concerns specific
to round 2; items V1–V6 are verifications of round-1 fixes
holding (or partially holding).

---

## V1 — D1 fix (round-trip lemma `comp` order) verified clean

**Claim verified.** Round 1 D1 reported swapped `comp` arguments
in §4.4. The post-fix §4.4.2 reads:

```lean
theorem ERMorN.tupleAt_tuplePack (k : ℕ) :
    ERMorN.comp
      (ERMorN.lift (ERMor1.tuplePack k))
      (ERMorN.ofVec (fun i : Fin (k+1) => ERMor1.tupleAt k i))
      ≈ ERMorN.id (k+1)

theorem ERMorN.tuplePack_tupleAt (k : ℕ) :
    ERMorN.comp
      (ERMorN.ofVec (fun i : Fin (k+1) => ERMor1.tupleAt k i))
      (ERMorN.lift (ERMor1.tuplePack k))
      ≈ ERMorN.id 1
```

**Finding.** With `ERMorN.comp (f : ERMorN n m) (g : ERMorN m k)
: ERMorN n k` and `f` running first per
`LawvereER.lean:167-186`, the orderings now produce:

- First lemma: `lift (tuplePack k) : ERMorN (k+1) 1` first, then
  `ofVec (tupleAt …) : ERMorN 1 (k+1)`, yielding
  `ERMorN (k+1) (k+1)` — equates to `ERMorN.id (k+1)`. ✓
- Second lemma: `ofVec (tupleAt …) : ERMorN 1 (k+1)` first, then
  `lift (tuplePack k) : ERMorN (k+1) 1`, yielding `ERMorN 1 1` —
  equates to `ERMorN.id 1`. ✓

The fix is correct.

**Severity.** Clean.

## V2 — D3 fix (`ERMorN.lift` / `ERMorN.ofVec`) added to spec

**Claim verified.** Round 1 D3 reported these helpers
referenced but not defined. The post-fix §4.4.1 adds:

```lean
def ERMorN.lift {n : ℕ} (f : ERMor1 n) : ERMorN n 1 :=
  fun _ => f

def ERMorN.ofVec {n m : ℕ} (g : Fin m → ERMor1 n) :
    ERMorN n m := g
```

**Finding.** Both are present in §4.4.1 with proper signatures.
The implementation order (§9 step 3.iv) places them between the
PolyBound builders and the round-trip lemmas, matching the
bottom-up named-composite discipline. ✓

**Severity.** Clean.

## V3 — D4 fix (`Fin.init` / `Finset.sup` step folded inline)

**Claim verified.** Round 1 D4 asked for the `Finset.sup`
sub-step to be folded inline into §3.4's proof outline. The
post-fix §3.4 step case now reads:

> For the IH on `Fin.init v` we need
> `(Finset.univ : Finset (Fin (k+1))).sup (Fin.init v) ≤ M'`.
> Since `Fin.init v i = v i.castSucc`, this reduces to
> `Finset.sup_le` followed by
> `Finset.le_sup (Finset.mem_univ i.castSucc) :
>    v i.castSucc ≤ M'`.

**Finding.** The Lean-level `Finset.sup_le_iff` /
`Finset.le_sup` flow is now spelled out where the implementer
will see it, rather than living in §8.1's separate ergonomic-risk
list. ✓

**Severity.** Clean.

## V4 — D11 fix (`@[simp]` recursive-case `tupleAt` lemmas added)

**Claim verified.** Round 1 D11 reported the parenthetical
mention of `Fin.lastCases_castSucc`/`Fin.lastCases_last` did not
commit to adding the two recursive-case lemmas. Post-fix §3.2
adds them explicitly:

```lean
@[simp] theorem Nat.tupleAt_succ_last (k n : ℕ) :
    Nat.tupleAt (k+1) n (Fin.last (k+1))
      = (Nat.unpair n).2 := by
  simp [Nat.tupleAt, Fin.lastCases_last]

@[simp] theorem Nat.tupleAt_succ_castSucc (k n : ℕ)
    (j : Fin (k+1)) :
    Nat.tupleAt (k+1) n j.castSucc
      = Nat.tupleAt k (Nat.unpair n).1 j := by
  simp [Nat.tupleAt, Fin.lastCases_castSucc]
```

**Finding.** Both lemmas are now in the spec's public surface
(§2.1) and proof outline (§3.2/§3.3 reference them). The proofs
themselves invoke the mathlib lemma names as `simp` rewrites.
See E2 below for a separate concern about whether
`Fin.lastCases_last` and `Fin.lastCases_castSucc` are the
canonical mathlib names.

**Severity.** Clean (modulo E2's name-existence concern).

## V5 — D13 fix (`Mathlib.Data.Fin.Tuple.Basic` import added)

**Claim verified.** Post-fix §2.1 reads:

> Imports: `Mathlib.Data.Nat.Pairing` and
> `Mathlib.Data.Fin.Tuple.Basic` (the latter for `Fin.init`,
> `Fin.lastCases`, and the reduction lemmas
> `Fin.lastCases_last` / `Fin.lastCases_castSucc`).

**Finding.** Import declaration now matches the §3.1/§3.2
usage. ✓

**Severity.** Clean.

## V6 — D23 fix (citation cross-check step in implementation order)

**Claim verified.** Post-fix §9 step 5 explicitly says:

> Step 5. **Citation cross-check.** Verify each entity's
> docstring contains the §7-listed citation verbatim, not a
> shortened paraphrase. Cross-reference the §7.1/§7.2 tables.

**Finding.** The citation-discipline check is now an explicit
implementation step. ✓

**Severity.** Clean.

---

## E1 — `erMorNSetoid` is a `def`, not an `instance` (defect)

**Claim under challenge.** Spec §5.3 writes:

```lean
def tupleIso (k : ℕ) : (k + 1 : LawvereERCat) ≅ 1 where
  hom        := ⟦ERMorN.lift (ERMor1.tuplePack k)⟧
  inv        := ⟦ERMorN.ofVec
                    (fun i : Fin (k+1) => ERMor1.tupleAt k i)⟧
  ...
```

and §4.4.2 writes "the setoid `≈` resolves to
`(erMorNSetoid (k+1) (k+1)).r`".

**Finding.** Direct verification of `LawvereERQuot.lean:23-32`:

```lean
def erMorNSetoid (n m : ℕ) :
    Setoid (ERMorN n m) where
  r f g := ∀ ctx : Fin n → ℕ,
    f.interp ctx = g.interp ctx
  iseqv := { … }
```

The declaration uses `def`, not `instance`. Consequence:

1. The `⟦·⟧` notation (which is mathlib's anonymous-constructor
   notation for `Quotient.mk` from a `Setoid` typeclass instance,
   per `Mathlib.Data.Quot.Basic` and the standard
   `Quotient.mk''`/`Quotient.mk` API) does NOT resolve against a
   plain `def`-declared setoid. Existing GebLean code agrees:
   every `LawvereERQuot.lean` and `LawvereERDelta.lean` site
   that constructs an `ERMorNQuo n m` value uses the explicit
   form `Quotient.mk (erMorNSetoid n m) f` — there is not a
   single occurrence of `⟦·⟧` notation against `ERMorN` anywhere
   in the codebase (verified via
   `grep -rn "⟦" GebLean/LawvereER*.lean`: no matches).

2. The `≈` notation expands via the `HasEquiv` typeclass, which
   Lean resolves through a `Setoid` instance. With
   `erMorNSetoid` as a plain `def`, `≈` will not auto-resolve to
   `(erMorNSetoid n m).r`. The lemma statements in §4.4.2 as
   written (with bare `≈`) will produce an "instance not found"
   error.

The spec's parenthetical "the setoid `≈` resolves to
`(erMorNSetoid (k+1) (k+1)).r`" is an *aspirational* claim, not
a verified one — it would hold only if `erMorNSetoid` were
declared `instance`, or if a separate `instance : Setoid (ERMorN
n m) := erMorNSetoid n m` were added.

The §5.3 `Quot.sound` invocation has a related issue: `Quot.sound`
takes an underlying-relation proof and produces equality of
`Quot.mk` classes, but the `⟦·⟧` notation (when it works) goes
through `Quotient.mk`, and the existing codebase pattern is
`Quotient.sound (s := erMorNSetoid n m) (relation_proof)`. Spec's
`Quot.sound` would not directly accept the round-trip lemma with
`≈` shape against the §5.3 quotient classes.

**Severity.** Defect.

**Recommended action.** Three independent fixes are required:

1. Either (a) change `erMorNSetoid` from `def` to `instance` in
   `LawvereERQuot.lean` (a one-line edit; this *is* an interface
   change to a previously-built module, so it requires a small
   audit pass but is non-breaking — every existing call site
   that uses the explicit
   `Quotient.mk (erMorNSetoid n m) ...` form still type-checks
   because explicit setoid arguments still work when the
   instance is in scope), OR (b) keep `erMorNSetoid` as `def`
   and rewrite §4.4.2 / §5.3 to use the explicit forms:

   ```lean
   theorem ERMorN.tupleAt_tuplePack (k : ℕ) :
       (erMorNSetoid (k+1) (k+1)).r
         (ERMorN.comp
           (ERMorN.lift (ERMor1.tuplePack k))
           (ERMorN.ofVec
              (fun i : Fin (k+1) => ERMor1.tupleAt k i)))
         (ERMorN.id (k+1))
   ```

   (and similarly for the second lemma), and §5.3's:

   ```lean
   def tupleIso (k : ℕ) : (k + 1 : LawvereERCat) ≅ 1 where
     hom := Quotient.mk (erMorNSetoid (k+1) 1)
              (ERMorN.lift (ERMor1.tuplePack k))
     inv := Quotient.mk (erMorNSetoid 1 (k+1))
              (ERMorN.ofVec
                 (fun i : Fin (k+1) => ERMor1.tupleAt k i))
     hom_inv_id := by
       exact Quotient.sound
         (s := erMorNSetoid (k+1) (k+1))
         (ERMorN.tupleAt_tuplePack k)
     inv_hom_id := by
       exact Quotient.sound
         (s := erMorNSetoid 1 1)
         (ERMorN.tuplePack_tupleAt k)
   ```

2. The recommendation between (a) and (b) is (b): registering an
   `instance` for `ERMorN n m`'s setoid would mean that any
   `≈` between `ERMorN` values resolves to extensional-interp
   equality, which is fine here but could be surprising
   downstream. The explicit-form rewrite preserves the existing
   "every quotient value carries its setoid argument explicitly"
   pattern that the rest of `LawvereERQuot.lean` /
   `LawvereERDelta.lean` follows.

3. Update §5.2's gate G3 wording from
   "reduces to `Quot.sound`" to
   "reduces to `Quotient.sound (s := erMorNSetoid · ·)`",
   matching the existing codebase convention.

## E2 — `Fin.lastCases_*` mathlib names not verified (concern)

**Claim under challenge.** §3.2 invokes
`Fin.lastCases_last` and `Fin.lastCases_castSucc` as `simp`
rewrites to discharge `Nat.tupleAt_succ_last` and
`Nat.tupleAt_succ_castSucc`. §3.3's bijection-theorem proof
outline says "`Fin.lastCases_last` (for `i = Fin.last`) or
`Fin.lastCases_castSucc` (for `i = j.castSucc`)".

**Finding.** I cannot verify by `lake build`, but mathlib's
`Fin.lastCases` reduction lemmas in
`Mathlib/Data/Fin/Tuple/Basic.lean` are conventionally named
`Fin.lastCases_last` and `Fin.lastCases_castSucc` — but mathlib
has also at times used the variant names `Fin.lastCases_apply`
or a `@[simp]` anonymous form. The spec asserts the names
without an in-mathlib citation. If the names have drifted in
the pinned mathlib commit, the §3.2 proofs will fail.

The round-1 review's D11 fix introduced these names; the spec
should commit to verifying them at implementation start, before
the bijection-theorem proofs go down the wrong simp path.

**Severity.** Concern.

**Recommended action.** Add a one-line verification step to §9
implementation order, just after step 1.ii (the `@[simp]`
interp lemmas):

> 1.ii.5: Before proving the lemmas, verify mathlib's
> `Fin.lastCases` reduction-lemma names by `#check
> @Fin.lastCases_last` and `#check @Fin.lastCases_castSucc`. If
> the names differ, update §3.2 + §3.3 accordingly.

## E3 — `ERMorN.lift` `n` parameter naming clashes with `tuplePack k` (minor)

**Claim under challenge.** §4.4.1 defines
`ERMorN.lift {n : ℕ} (f : ERMor1 n) : ERMorN n 1`. §4.4.2 uses
`ERMorN.lift (ERMor1.tuplePack k)` where
`ERMor1.tuplePack k : ERMor1 (k + 1)`. So the implicit `n` of
`lift` instantiates to `k + 1`.

**Finding.** Mechanical: `ERMorN.lift (ERMor1.tuplePack k) :
ERMorN (k+1) 1`. ✓ The implicit-argument resolution is fine.

But round 1 (D10) flagged that the `tuplePack` recursive call
might need explicit type ascription on `proj i.castSucc`. Now
that `lift` is also in the call chain at §4.4.2, the implementer
should be ready for *another* implicit-argument resolution
ambiguity: when Lean sees `ERMorN.lift (ERMor1.tuplePack k)` in
a context where `(k + 1)` could be either the `n` argument of
`lift` or some other natural number visible in the goal, Lean
may need help pinning `lift`'s `n := k + 1`.

The spec does not flag this potential friction. Likely benign,
but warrants a one-line ergonomic-risk note in §8.1 (which
already has 4 items along these lines).

**Severity.** Minor.

**Recommended action.** Add an §8.1 item 5 noting that
`ERMorN.lift (ERMor1.tuplePack k)` may require `(n := k+1)` to
disambiguate, and similarly for `ERMorN.ofVec` if its `m`
parameter elaboration sticks.

## E4 — Step-2 dependency on `tuplePackCoef` at fixed `k` not addressed (concern)

**Claim under challenge.** §1.1 says:

> Step 2: `ERMor1.simultaneousBoundedRec` packs intermediate
> state via `Nat.tuplePack` and unpacks via `Nat.tupleAt`,
> using the polynomial bound to certify staying in ER.

§8.1 item 4 says `tuplePackCoef k` grows fast (`tuplePackCoef 4
≈ 2.3·10⁸`) and the spec restricts smoke tests to `k ≤ 2`.

**Finding.** Master design §3.2 (lines 685-757) requires
`simultaneousBoundedRec`'s polyBound implementation to compose
the `tuplePackCoef k * (componentBound + 1)^(2^k)` bound
*inside* the `boundedRec` step. The implementation must
materialize `tuplePackCoef k` as a *literal Nat constant* in the
PolyBound's `coefficient` field; for `k = 4`, that literal is
228947161.

**This is a new finding of round 2.** It does not block step 1's
cycle, but the `tuplePackCoef` recurrence's growth rate has a
downstream consequence not captured in the current spec:

1. Step 2's `simultaneousBoundedRec_polyBound` proof will
   require evaluating `Nat.tuplePackCoef k` at the fixed `k` of
   the simrec being translated. When the K^sim simrec has 5+
   children (so `k ≥ 4` in our (k+1)-tuple convention, meaning
   a 5-tuple), the resulting polynomial-bound coefficient field
   contains a 9-digit literal that must reduce by `decide` or
   `rfl` — well within Lean's capacity, but the §6.3 spec
   restriction "`decide`-tactic timing degrades for `k ≥ 3`"
   suggests a possible step 2 friction not yet documented.

2. Step 2's user-level error messages (when a `boundedRec`
   bound is rejected) will include the `tuplePackCoef k`
   literal, which for medium `k` is opaque. Step 2's spec
   should add a "fixed-point at runtime" doc-comment so the
   user sees `tuplePackCoef 4 = 228947161` rather than a raw
   number.

This is a step-2 concern, not a step-1 spec defect. But the
step-1 spec should foreshadow it — currently §8.2 only mentions
the multiplicative-vs-additive bound shape, not the coefficient
size at moderate `k`.

**Severity.** Concern.

**Recommended action.** Append to §8.2 a one-paragraph note:

> The `tuplePackCoef k` constants grow doubly-exponentially
> (`tuplePackCoef 4 ≈ 2.3·10⁸`). Step 2's
> `simultaneousBoundedRec_polyBound` proof will instantiate
> `tuplePackCoef k` at the K^sim-simrec's child-count `k`;
> for typical K^sim_2 simrec witnesses (e.g. `addK` at `k = 1`,
> giving `tuplePackCoef 1 = 9`) the literal is small, but
> level-2 simrec witnesses with 4+ children will produce
> 9-digit coefficient literals. This is not a soundness concern
> (the bound holds for any `k`), but step 2's documentation
> should surface the literal value to readers.

---

## Re-verifications of round-1 clean items (spot checks)

I spot-checked round 1's clean items D5–D9, D14–D22, D24–D27.
Of those:

- **D6** (Tourlakis citation accuracy): not re-verified;
  trusted round 1's `pdftotext`-based reading.
- **D7** (Szudzik-vs-Cantor swap labelling): re-confirmed by
  `grep -n "natPair" Utilities/ERArith.lean:181-206`. ✓
- **D9** (`tupleAt` recursive arity types): re-walked the
  motive-and-branch types — clean as round 1 stated. ✓
- **D17** (smoke `#guard` values): re-verified
  `Nat.pair 28 7 = 819` (Szudzik: `28 ≥ 7`, so `28² + 28 + 7 =
  784 + 28 + 7 = 819`). ✓
- **D19** (`decide` examples): re-verified `tuplePack 1 ![3, 5]
  = 28 ≤ 9 * 36 = 324`. ✓
- **D22** (banned-words discipline): re-grep against the
  post-fix spec; no new banned words introduced by the round-1
  edits. Independent grep against the post-fix spec across
  the banned-words list found no matches in prose; the only
  hits are inside the standard technical terms "Tourlakis"
  and "Szudzik", which are not banned.

## Verifications specifically asked for in round-2 charter

- **G1 (object indexing).** `LawvereERCat := ℕ` per
  `LawvereERQuot.lean:143`; `instance (n : ℕ) : OfNat
  LawvereERCat n := ⟨(n : ℕ)⟩` per line 145. So
  `(k + 1 : LawvereERCat)` and `(1 : LawvereERCat)` resolve
  cleanly via `OfNat` and an inferred coercion.
  Predicted to pass. ✓
- **G2 (hom-set shapes).** `instance : CategoryStruct
  LawvereERCat where Hom := ERMorNQuo` per line 152-155. So
  `(k+1) ⟶ 1` is `ERMorNQuo (k+1) 1`, and
  `1 ⟶ (k+1)` is `ERMorNQuo 1 (k+1)`, and these are
  `Quotient (erMorNSetoid (k+1) 1)` and
  `Quotient (erMorNSetoid 1 (k+1))` respectively.
  Predicted to pass *modulo* the `⟦·⟧` notation issue (E1):
  the wrapping is correct in shape, but the syntactic notation
  for constructing the quotient class will fail.
- **G3 (iso laws via Quot.sound).** Predicted to FAIL as
  written, due to E1's `Quot.sound` vs `Quotient.sound (s :=
  ...)` mismatch. With E1's fix, predicted to pass.

So the §5.2 gate as currently written would fail at G3 (and at
G2 if the implementer reads "no wrapping" too literally), but
with E1's recommended fix, all three gates pass.

- **(k+1) re-indexing convention check.** I scanned the spec
  for off-by-one ambiguities in the variable `k`'s usage and
  found no places where "at parameter k" is used to mean
  "k-tuple" rather than "(k+1)-tuple". §1.3 states the
  convention clearly and §3.1 / §4.1 / §4.4 / §5.3 use it
  consistently. ✓

- **§4.4 round-trip lemma proof outline check.** Spec says
  "Both lemma proofs unfold `ERMorN.comp`, `ERMorN.id`,
  `ERMorN.lift`, `ERMorN.ofVec` to functions of indices,
  unfold `ERMor1.comp.interp` via the existing
  `@[simp] ERMor1.interp_comp`, and then reduce to the
  Nat-level bijection theorems via the §4.2 interp simp
  lemmas." This is mechanical and the chain
  `interp_comp → interp_lift → interp_ofVec →
  interp_tuplePack/interp_tupleAt → Nat.tupleAt_tuplePack`
  is sound. The implementer will need:

  - `(ERMorN.lift f).interp ctx i = (f).interp ctx` — provable
    by `rfl` since `lift f = fun _ => f`.
  - `(ERMorN.ofVec g).interp ctx i = (g i).interp ctx` —
    provable by `rfl` since `ofVec` is identity.

  Neither is in the spec's §4.2 simp-lemma list, but they
  are `rfl` and don't strictly need a `@[simp]` attribute.
  The proof should still go through cleanly.

- **§6.2 `decide` examples.** Re-verified all three are
  `decide`-able: `Nat.tuplePackCoef 0 = 1`, `1 = 9`, `2 = 121`
  all by `rfl` on the recurrence; the two `decide` inequality
  examples reduce to ground numerics on `ℕ`'s `Decidable`
  instance for `≤`. ✓

---

## Summary

**Total items.** 6 (4 newly-checked + 2 partial verifications).

**Defects (severity: defect).** 1

- E1 — `erMorNSetoid` is a `def`, not an `instance`; the
  spec's `⟦·⟧` notation in §5.3 and `≈` notation in §4.4
  will not resolve as written. `Quot.sound` needs replacement
  by `Quotient.sound (s := erMorNSetoid · ·)`.

**Concerns (severity: concern).** 2

- E2 — `Fin.lastCases_last` / `Fin.lastCases_castSucc`
  mathlib names not verified; spec should add a `#check`
  step.
- E4 — `tuplePackCoef k`'s growth has a downstream-document
  consequence for step 2 not captured in §8.2.

**Minor.** 1

- E3 — `ERMorN.lift`'s implicit `n` parameter may need
  disambiguation; warrants an §8.1 item 5.

**Round-1 fixes verified clean.** 6

- V1 (D1 `comp`-order fix), V2 (D3 helpers added),
  V3 (D4 `Finset.sup` step inlined), V4 (D11 `@[simp]`
  recursive-case lemmas added — modulo E2 name check),
  V5 (D13 import added), V6 (D23 citation cross-check step).

**Overall assessment.** Spec needs revision.

The round-1 fixes addressed the round-1 findings, but the
implementer's verification of `LawvereERQuot.lean`'s actual API
(driven by the round-1 D2/D3 fixes that introduced `⟦·⟧` and
`Quot.sound` into §5.3 and §4.4) was not actually carried out
against the existing code. The new defect E1 is a quotient-API
mismatch that would block §4.4 and §5.3 from compiling. It is a
small edit (rewrite `⟦·⟧` to `Quotient.mk (erMorNSetoid · ·)`,
rewrite `Quot.sound` to `Quotient.sound (s := erMorNSetoid · ·)`,
and either register `erMorNSetoid` as an `instance` or restate
the §4.4 lemmas using the explicit `(erMorNSetoid · ·).r` form),
but it must be made before implementation begins; otherwise the
implementer will hit the error mid-cycle and roll back.

The minor concerns E2, E3, E4 are documentation-grade and do not
block implementation. They would tighten the spec's
implementer-facing precision.

The mathematical content remains correct (round-1 verifications
stand, and round 2's spot checks of D6, D7, D9, D17, D19, D22
hold). The round-1 + round-2 issue list is now defect-by-defect
addressable in a single revision pass.

End of round-2 adversarial review.
