# Step 3 spec adversarial review — round 1

## Summary

The spec is mathematically sound at the level of closed forms
and bound shapes; the literature contract for `A_one`,
`A_one_iter r`, `A_two_iter r` is correctly transcribed.
However, the spec has one substantive blocking error in its
`#2.1` import list (it cites the wrong module for
`ERMor1.addN`) and several substantive errors / risks in the
proposed proof tactics for `interp_A_one_iter` (the `ring_nf;
omega` step almost certainly will not close because `omega`
does not handle `2 ^ r`, `2 ^ (r+1)`, `2 ^ (r+2)` symbolically
and `ring_nf` does not normalize Nat-truncating subtraction).
There are also a few minor inconsistencies vs the master
design (a stray `A_two = expER` reference in §3.3 of the
master design that the spec correctly elides), some
under-specified citation discipline, and a discipline gap on
the constructive interpretation of `decide` proofs.

Total findings: 12 (1 blocker, 5 substantive, 6 minor).

Recommendation: **revision**, not rewrite. The mathematical
content is right; the implementation hints in §4.2 and §5.2
need tightening, the import in §2.1 must be fixed before the
implementer touches it, and a handful of small alignments are
needed.

## Findings (severity-ordered)

### Finding 1: Wrong import for `ERMor1.addN` (severity: blocker)

**Location:** §2.1 lines 124-128 (Imports).

**Issue:** The spec says
> `GebLean.LawvereERArith` (for `ERMor1.addN`,
> `ERMor1.succ`, `ERMor1.proj`, and their interp simp
> lemmas).

`ERMor1.addN` and `interp_addN` do **not** live in
`GebLean.LawvereERArith`.  That file (`GebLean/LawvereERArith.lean`,
45 lines) defines only `expER` and `interp_expER` (plus the
helper `natBProd_const`).

`ERMor1.addN` is defined at
`GebLean/Utilities/ERArith.lean` line 42, with `interp_addN`
at line 58.  `ERMor1.succ`, `ERMor1.proj`, `ERMor1.comp` and
their interp simp lemmas are constructors / theorems in
`GebLean/LawvereER.lean` (lines 36-145).

**Evidence:**

```text
GebLean/Utilities/ERArith.lean:42:def ERMor1.addN : ERMor1 2 :=
GebLean/Utilities/ERArith.lean:58:@[simp] theorem ERMor1.interp_addN ...
GebLean/LawvereER.lean:40:  | succ : ERMor1 1
GebLean/LawvereER.lean:42:  | proj {k : ℕ} (i : Fin k) : ERMor1 k
GebLean/LawvereER.lean:104:@[simp] theorem ERMor1.interp_succ ...
GebLean/LawvereER.lean:110:@[simp] theorem ERMor1.interp_proj ...
```

**Proposed fix:** Replace the `LawvereERArith` import bullet
with two bullets:

- `GebLean.LawvereER` (transitively pulled in; explicit for
  `ERMor1.succ`, `ERMor1.proj`, `ERMor1.comp` and their
  interp simp lemmas).
- `GebLean.Utilities.ERArith` (for `ERMor1.addN` and
  `interp_addN`).

Note: `LawvereERPolynomialBound` already imports
`GebLean.Utilities.ERArith` and `GebLean.LawvereERBoundComputable`,
so the shortest correct import set for the new module is
just `GebLean.LawvereERPolynomialBound` plus
`GebLean.Utilities.ERArith` plus `GebLean.LawvereERBoundComputable`.
But spelling out `Utilities.ERArith` directly is the right
move per the spec's own §2.3 "imports for clarity"
discipline.

### Finding 2 (substantive): `interp_A_one_iter` succ case won't close

**Location:** §4.2 lines 261-270, the `succ r ih` branch of
the proof.

**Issue:** After `simp only [interp_comp, interp_A_one]`,
applying the `rfl` rewrite, and rewriting by `ih`, the goal
reduces (after beta) to roughly:

```text
2 * (2 ^ r * ctx ⟨0, _⟩ + (2 ^ (r + 1) - 2)) + 2
  = 2 ^ (r + 1) * ctx ⟨0, _⟩ + (2 ^ (r + 2) - 2)
```

`ring_nf` does not normalize Nat-truncating subtraction
(`a - b` is non-cancelling when `b > a`), so it will not
push `2 *` through `(2 ^ (r + 1) - 2)` to produce
`2 * 2 ^ (r + 1) - 4` — and even if it did, `omega` does not
handle exponential terms `2 ^ r`, `2 ^ (r + 1)`,
`2 ^ (r + 2)` symbolically.  `omega` treats them as opaque
naturals; without auxiliary hypotheses linking them, it
cannot prove `2 * 2 ^ r = 2 ^ (r + 1)`.

The single hypothesis `h_pow_ge_two : 2 ^ (r + 1) ≥ 2` is
not enough.  The proof needs (at minimum):

- `h_pr1 : 2 ^ (r + 1) = 2 * 2 ^ r`
  (from `pow_succ` or `Nat.pow_succ`).
- `h_pr2 : 2 ^ (r + 2) = 2 * 2 ^ (r + 1)`
  (likewise).
- The lower bound `h_pow_ge_two` (already listed).

Only after these are in context does `omega` reduce the goal
to a pure linear-arithmetic problem in the free naturals
`ctx ⟨0, _⟩` and `2 ^ r`.

**Evidence:** Existing proofs in the codebase that involve
`2 ^ k` always introduce a `pow_succ` rewrite or an
explicit equality before invoking `omega`, e.g.
`Utilities/Tower.lean` line 94 (`hstep : 2 ^ n + 2 ^ n = 2 ^ (n + 1)`).
The spec's "Nat-subtraction step needs a `2^{r+1} ≥ 2` lemma
for `omega`" comment in §4.2 prose paragraph
underestimates this.

**Proposed fix:** Replace the hand-wavy `ring_nf; omega`
with the explicit chain.  Rough sketch:

```lean
| succ r ih =>
    unfold A_one_iter
    simp only [ERMor1.interp_comp, interp_A_one]
    have hcoll :
        (fun _ : Fin 1 =>
          (A_one_iter r).interp ctx) ⟨0, by decide⟩ =
            (A_one_iter r).interp ctx := rfl
    rw [hcoll, ih]
    have h_succ1 : 2 ^ (r + 1) = 2 * 2 ^ r := by
      rw [pow_succ]; ring
    have h_succ2 : 2 ^ (r + 2) = 2 * 2 ^ (r + 1) := by
      rw [pow_succ]; ring
    have h_pow_ge_two : 2 ≤ 2 ^ (r + 1) := by
      rw [h_succ1]
      have : 1 ≤ 2 ^ r := Nat.one_le_pow _ _ (by omega)
      omega
    omega
```

This is still tactic-level; the implementer may inline some
steps.  The point is the spec's `ring_nf; omega` is
optimistic and should be flagged as such.

### Finding 3 (substantive): `ofA_one_iter` bounds proof needs same expansion

**Location:** §5.2 lines 354-364.

**Issue:** After `rw [interp_A_one_iter]; simp only [pow_one]`
the goal is:

```text
2 ^ r * ctx ⟨0, _⟩ + (2 ^ (r + 1) - 2)
  ≤ 2 ^ r * ((sup ctx + 1)) + (2 ^ (r + 1) - 2)
```

The `2 ^ (r + 1) - 2` cancels structurally (it's the
`+ constant` on both sides).  Reducing to
`2 ^ r * ctx ⟨0, _⟩ ≤ 2 ^ r * (sup ctx + 1)`.

`nlinarith` *can* handle this — it knows `Nat.mul_le_mul_left`
in spirit — but only if it has `h_ctx0 ≤ sup` and
`1 ≤ 2 ^ r` already in context.  `h_pow_pos : 1 ≤ 2 ^ r` is
listed.  `h_ctx0` (from `Finset.le_sup`) is listed.  So
`nlinarith` is *plausible*.  But `nlinarith` does not always
succeed on goals involving products of opaque terms
(`2 ^ r` here is opaque), and the spec's own §9.2 risk
acknowledges this.

This is more a "watch the spec's hedge" than a hard error;
the cleaner path is `Nat.mul_le_mul_left`:

```lean
have h_ctx0_le : ctx ⟨0, by decide⟩ ≤ sup ctx + 1 := by
  have := Finset.le_sup ...; omega
have : 2 ^ r * ctx ⟨0, _⟩ ≤ 2 ^ r * (sup ctx + 1) :=
  Nat.mul_le_mul_left _ h_ctx0_le
omega
```

**Proposed fix:** Mention the explicit `Nat.mul_le_mul_left`
fallback as the primary path, since `nlinarith` over Nat
with opaque `2 ^ r` is not reliable.  §9.2 already alludes
to the fallback; promote it.

### Finding 4 (minor): master-design vs spec inconsistency on `A_two = expER`

**Location:** Spec §1.2 "Out of scope and not anyone's
job", lines 70-72; master design §3.3 line 812-813.

**Issue:** Master design §3.3 says
`ERMor1.A_two = ERMor1.expER` and lists it as a Lean
entity.  The spec correctly excludes a unary
`ERMor1.A_two`, on the grounds that Tourlakis's
`A_2 = λx. 2^x` is `A_two_iter 1` (= `tower 1 x = 2^x`)
and a separate name is not warranted.

The spec's reasoning is correct; furthermore the master
design's claim is itself inconsistent: `expER : ERMor1 2`
(arity 2, interp `(ctx 1)^(ctx 0)`), so `expER ≠ λx. 2^x`
without partial application to `y = 2`.  The master design
has a (small) bug there.

The spec is right to elide the master design's
`A_two = expER` line, but the spec should explicitly
acknowledge that the master design's text on this point
will need a parallel correction.  Otherwise readers cross-
referencing the two docs will be confused.

**Evidence:**

```text
GebLean/LawvereERArith.lean:25:def ERMor1.expER : ERMor1 2 :=
docs/.../master-design.md:812:- `ERMor1.A_two = ERMor1.expER` (existing in
docs/.../master-design.md:813:  `LawvereERArith.lean` line 25). Interp `λx. 2^x`.
```

**Proposed fix:** Add one sentence to spec §1.2 noting that
master design §3.3 has a stray `A_two = expER` line which
is mathematically wrong (`expER` is binary, not unary) and
which step 3 does not implement; the master design will
need a follow-up edit.

### Finding 5: `decide` discipline for `Fin 1` index in proofs (severity: minor)

**Location:** Throughout — §3.1, §3.2, §4.1, §4.2, §5.1, §5.2.

**Issue:** The spec uses `⟨0, by decide⟩` for the unique
`Fin 1` index everywhere.  This is fine, but inconsistent
with the rest of the codebase, which uses just `0` (relying
on `OfNat (Fin 1) 0`) or `(0 : Fin 1)`.  See for example
`Utilities/ERArith.lean` line 50 (`ERMor1.proj 0`) and
`LawvereERPolynomialBound.lean`'s `ofProj` builder.

The `interp_succ` and `interp_proj` simp lemmas use the
plain numeric form `(ctx 0).succ` and `ctx i` (with `i` of
type `Fin k`); existing code calling `interp` always uses
`ctx 0`, not `ctx ⟨0, by decide⟩`.

This is mostly cosmetic but matters because:

1. The spec's `interp_A_one` simp lemma writes
   `ctx ⟨0, by decide⟩`.  When this fires as a simp rule on
   downstream goals where the user wrote `ctx 0`, simp may
   not match (the `⟨0, by decide⟩` form is a specific Fin-mk
   pattern, not the OfNat-coerced numeric).  This will
   silently break step 4's reuse of the simp lemmas.

2. Step 4 prose (master design §3.4) writes `ctx ![x]` on
   the right-hand side of bounds, which under the standard
   `Matrix.cons_val_zero` simp will reduce to `x`, not
   `ctx ⟨0, by decide⟩`.

**Evidence:** The existing `interp_towerER` lemma uses
`ctx 0` literally (LawvereERBoundComputable.lean line
242: `(ERMor1.towerER k).interp ctx = tower k (ctx 0)`).
The spec's `interp_A_two_iter` is consistent with this
shape, but `interp_A_one` and `interp_A_one_iter` are not.

**Proposed fix:** Use plain `ctx 0` (with `(0 : Fin 1)`
type ascription if needed) throughout the spec's interp
simp lemmas and in the constructions where a `Fin 1` index
is the unique projection target.  In the constructions,
`ERMor1.proj 0` (with `k := 1` inferred from context) is
shorter and matches existing code.

### Finding 6 (minor): `proj 0` vs `proj ⟨0, by decide⟩` in `A_one_iter` zero case

**Location:** §3.2 line 207 and §4.2 line 257-260.

**Issue:** `A_one_iter 0` is defined as
`ERMor1.proj ⟨0, by decide⟩` in §3.2 line 207.  The base case
of `interp_A_one_iter` then uses `simp only [..., pow_zero,
one_mul, pow_one]; omega`.  But the goal at `r = 0` is
`(proj ⟨0, by decide⟩).interp ctx = 2 ^ 0 * ctx ⟨0, _⟩ + (2 ^ 1 - 2)`.

After `simp only [interp_proj]`, the LHS becomes
`ctx ⟨0, by decide⟩`.  After `pow_zero` and `pow_one` on the
RHS, the goal is `ctx ⟨0, _⟩ = 1 * ctx ⟨0, _⟩ + (2 - 2)`,
which after `one_mul` is `ctx ⟨0, _⟩ = ctx ⟨0, _⟩ + 0`, and
`omega` closes.  Fine — but only if Lean considers the two
`ctx ⟨0, by decide⟩` and `ctx ⟨0, _⟩` syntactically equal,
which depends on the `decide` proof being definitionally
the same on both sides.

This couples to Finding 5: pick *one* `Fin 1`-index form
and stick with it.  If the spec uses `proj 0` (relying on
`OfNat`), then `interp_proj` rewrites cleanly.  If it uses
`⟨0, by decide⟩`, the proof goal will display the Fin-mk
literal everywhere and the `decide` proof may differ
on either side — `omega` may still close, but the display
is awkward.

**Proposed fix:** Use `ERMor1.proj 0` (no Fin-mk literal)
throughout.  Standardize all interp simp lemmas to
`ctx 0` on the right-hand side.

### Finding 7 (substantive): `r = 0` edge case in `ofA_one_iter`'s `constant` field

**Location:** §5.2 line 353.

**Issue:** The `constant` field is `2 ^ (r + 1) - 2`.  At
`r = 0`, this is `2 ^ 1 - 2 = 0`.  The bound shape
becomes `2 ^ 0 * (sup + 1)^1 + 0 = sup + 1`.  The interp at
`r = 0` is `proj 0`, with value `ctx 0 ≤ sup`.  So
`ctx 0 ≤ sup + 1` holds (with one bit of slack).  ✓.

At `r = 1`, constant is `2 ^ 2 - 2 = 2`.  Bound shape:
`2 * (sup + 1) + 2 = 2*sup + 4`.  Interp at `r = 1` is
`A_one(x) = 2x + 2`.  At `x = sup`, that's `2*sup + 2 ≤
2*sup + 4`.  ✓.

These check out *because* the constant slot accounts for
the worst-case constant *before* the polynomial slot
overshoots.  But the spec's docstring on line 343-345 says
"loose by `2^r` at the constant slot if compared to the
tightest possible Nat constant (max(0, 2^r − 2))".

This claim is wrong.  The `interp_A_one_iter` closed form
has `(2^{r+1} − 2)` as the literal constant, which is
exactly what the spec uses for the `constant` field.  There
is no looseness vs the closed form — the bound is tight at
the constant slot.  The looseness in the docstring is
mathematically inconsistent with the field choice.  Reading
the prose, it sounds like the spec intended a tighter
constant (`max(0, 2^r − 2)`) and explicitly chose looser
for proof brevity.  But the actual chosen constant
`2^{r+1} − 2` is the *exact* closed-form constant, not a
loosened version.

**Proposed fix:** Replace the docstring paragraph with a
correct statement:

> The constant `2^{r+1} − 2` is exactly the closed-form
> constant of `interp_A_one_iter`; the bounds proof reduces
> to `ctx 0 ≤ sup ctx + 1` (with one bit of slack, since
> `Finset.le_sup` gives `ctx 0 ≤ sup ctx`).

### Finding 8 (minor): `#guard` cost claim conflates "no bprod" with "no bsum"

**Location:** §6.1 lines 403-413, §9.3 lines 555-561.

**Issue:** §6.1 states
> "A_one: 7-generator-deep, no bprod / no boundedRec."

But `A_one` uses `addN`, which uses `mulN = boolAnd`, which
is **bsum-based** (`ERMor1.bsum (ERMor1.proj 1)` per
LawvereERBool.lean line 41-42).  So `A_one` is NOT
bsum-free.

`bsum` (unlike `bprod` of large exponentials) is
linear-time in its bound argument and pure Nat-rec, so
small-input `#guard`s do terminate.  Concretely:

- `A_one.interp ![3] = 8` requires `addN.interp ![4, 4]`,
  which fully unfolds to
  `(4 + 1) * (4 + 1) - 4 * 4 - 1`, where each multiplication
  reduces via `bsum` of size 4 or 5 — fast.
- `A_one.interp ![5] = 12` requires `addN.interp ![6, 6]`,
  with `bsum` sizes 6 and 7 — still fast.
- `A_one_iter 2 ![3] = 18` requires nested `addN` with
  `bsum` sizes ≤ 9 — still fast.

So the `#guard`s should terminate, but the spec's
self-description ("no bprod / no boundedRec") is technically
correct yet misleading: the kernel reduction does involve
`bsum` iteration.  The mitigation in §9.3 (drop slow
`#guard`s) is fine, but the prose should be precise.

This is the same family of pitfalls as the
MEMORY note "ER / Gödel-numbering interp not safe for
`#guard`" (which points to `natPair`'s composite tree and
similar `bsum`-deep constructions).  The risk-section
should explicitly mention `bsum` cost from `addN`'s use of
`mulN`.

**Proposed fix:** Replace "7-generator-deep, no bprod / no
boundedRec" with "shallow, with `bsum` reductions only at
small bounds via `mulN`".  Adjust §9.3 risk text to
mention the dependency on `bsum` size scaling with input.

### Finding 9 (minor): citation discipline — `interp_A_*` docstrings

**Location:** §4.1, §4.2, §4.3 (the theorems' code blocks
do not include docstrings); §7 promises them.

**Issue:** §7 says "Each public `def`/`theorem` carries the
literature reference in its docstring".  The code snippets
in §4.1-§4.3 show the `@[simp] theorem` declarations
without any docstring.  Per CLAUDE.md transcription
discipline, every implemented theorem in a transcription
workstream "must include the literature reference in its
docstring comment".

The implementer might naively follow the code blocks
literally and skip the docstrings; §7 lists them as
required, but the §4.x code blocks don't show them.

**Proposed fix:** Add explicit `/-- ... -/` docstring blocks
to each theorem snippet in §4.1, §4.2, §4.3, mirroring the
pattern shown in §3.1 / §3.2 / §3.3.  Or add a sentence at
the top of §4 saying "all theorems carry the docstrings
listed in §7".

### Finding 10 (minor): §10 acceptance criteria omit a few §3-§5 deliverables

**Location:** §10 lines 593-619.

**Issue:** §10 enumerates the deliverables but is missing:

- The §5.3 paragraph in the module docstring explicitly
  documenting the absence of `ofA_two_iter`.  §5.3 says
  "The module docstring includes a paragraph explaining
  the absence of `ofA_two_iter`"; §10 does not list this.

- §6.3 re-exports.  §10 items 3-4 cover the `import`
  registrations but the "Re-exports" subsection (§6.3)
  also notes both should be done at skeleton-creation
  time per discipline-1.  §10 should either state that
  explicitly or reference §2.3 / §6.3.

- The §7 literature-citation cross-reference network
  pointer.  §7 lists two research-doc cross-references
  (`2026-04-30-ksim-polynomial-bound-references.md` and
  the master design §3.3); §10 does not require these in
  the module docstring.

**Proposed fix:** Add to §10:

> 1.h Module docstring includes the polynomial-vs-tower
> split paragraph explaining the absence of
> `ofA_two_iter` (per §5.3).
> 1.i Module docstring includes pointers to
> `docs/research/2026-04-30-ksim-polynomial-bound-references.md`
> and master design §3.3 (per §7).

### Finding 11 (substantive): §9 risks omit `omega` / `ring_nf` issues

**Location:** §9 (Risks).

**Issue:** §9.1 covers Nat-subtraction in the closed form
generally, and §9.2 covers `nlinarith` failure on
`ofA_one_iter`'s bounds, but neither covers:

- The fact that `omega` cannot reason about
  `2 ^ r`, `2 ^ (r+1)`, `2 ^ (r+2)` symbolically (Finding
  2).
- The fact that `ring_nf` does not normalize Nat
  subtraction, so `ring_nf` followed by `omega` is not the
  right closing sequence in §4.2.
- The fact that `Finset.le_sup` over `Fin 1` gives
  `ctx 0 ≤ sup`, not `ctx 0 ≤ sup + 1` — so `omega` needs
  to add the extra `+1` from the bound shape.  Already
  managed implicitly in §5.1 / §5.2 but worth noting.

**Proposed fix:** Add a §9.7 risk:

> §9.7 `omega` does not handle `2 ^ r` symbolically.
> The closed-form induction in §4.2 will require
> `pow_succ` rewrites (`2 ^ (r+1) = 2 * 2 ^ r`,
> `2 ^ (r+2) = 2 * 2 ^ (r+1)`) before `omega` can
> close the linear step.  Mitigation: explicit
> `have` chain in the proof; do not rely on
> `ring_nf` (which is also stymied by Nat-truncating
> subtraction).

### Finding 12 (minor): line-number reference for `towerER` (cosmetic drift)

**Location:** §3.3 line 222-224 cites
"LawvereERBoundComputable.lean line 230".

**Issue:** Verified — `def ERMor1.towerER` is at line 230
exactly.  Citation is correct.

But the spec's own §9.4 risk acknowledges line numbers
drift; it would be more robust to cite by name (`def
ERMor1.towerER`) rather than line number.

**Proposed fix:** Replace "line 230" citations in §3.3
with name-based references (e.g. "`def ERMor1.towerER`
in `LawvereERBoundComputable.lean`").

## Items checked and confirmed correct

- Closed forms:
  - `A_one(x) = 2x + 2`: checked via construction
    `addN(succ(proj 0), succ(proj 0)) = (x+1) + (x+1) = 2x+2`. ✓
  - `A_one_iter r(x) = 2^r · x + (2^{r+1} − 2)`: checked
    by induction on `r` (modulo the proof-tactic concern
    in Finding 2). ✓ Mathematically.
  - `A_two_iter r(x) = tower r x`: routes through
    `interp_towerER` (existing). ✓
- `tower 0 x = x`, `tower 1 x = 2^x` (per `Utilities/Tower.lean`
  lines 21-24).  Spec's claim that
  `A_two = λx. 2^x` is `A_two_iter 1` is correct.
- `PolyBound` structure shape (degree, coefficient,
  constant, bounds) matches `LawvereERPolynomialBound.lean`
  line 42-50 exactly.
- `Finset.le_sup` API usage in §5 — both
  `(by simp)` and `(Finset.mem_univ _)` work; existing
  builders use the latter (more idiomatic), spec uses the
  former (works but less idiomatic).
- Recursion direction `A_1 ∘ A_1^r` for `A_one_iter` —
  matches the closed-form induction's "apply IH to the
  inner argument, then apply A_one once on top" structure.
- `expER : ERMor1 2` — verified arity is 2, with interp
  `(ctx 1)^(ctx 0)`.  Spec correctly does NOT alias
  `A_two_iter` to `expER` directly.
- §8 (step-4 hand-off list) — items 1-7 do appear to cover
  the consumers of step 3's outputs that the master
  design §3.4 promises.  Item 7 (Nat hypothesis fed to
  `simultaneousBoundedRec_interp_correct`'s dominance
  slot) is correctly identified as step-4-or-later, not
  step-3.
- The `bounds` field requirement: literal form is
  `coefficient * ((sup ctx + 1) ^ degree) + constant`.
  `simp only [Nat.add_zero]` does correctly drop the
  trailing `+ 0` when `constant := 0`.  No semantic issue.
- `tower r x` for `r ≥ 1` is not polynomially bounded in
  `x`: matches the bprod-restriction in
  `LawvereERPolynomialBound.lean`.  The spec's
  no-`ofA_two_iter` decision is correct.
- Test discipline for `A_one_iter 2`: kernel reduction
  involves `bsum` of size ≤ 9, fast enough for `#guard`
  (Finding 8 modifies the prose claim but the tests are
  fine).

## Open questions for the spec author

1. **`A_one_iter`'s recursion direction at `r = 0`.**
   §3.2 picks `proj 0` as the identity at `r = 0`.  An
   alternative is to write `r + 1 => comp A_one_iter r
   A_one`, putting `A_one` on the inside.  The spec's
   §9.5 acknowledges the two are equivalent; the chosen
   form simplifies the succ step's `interp_A_one`-fires-
   on-the-IH pattern.  Confirm: does the implementer
   need to handle the `r = 0` base any differently if
   the alternative direction is chosen?  (Answer: no — at
   `r = 0` both give `proj 0`.)

2. **Test `#guard` for `A_two_iter 0`.**  §6.1 line 416
   tests `(A_two_iter 0).interp ![5] = 5`, relying on
   `towerER 0 = proj 0`.  This is correct.  But should
   we also test `A_two_iter 0 = proj 0` definitionally
   (e.g. `#guard A_two_iter 0 = ERMor1.proj 0`)?  This
   would be redundant but documents the alias.  Probably
   skip.

3. **Recursion-direction note in §3.2.**  The spec writes
   "apply r-fold first, then one more `A_one`".  But the
   definition `r + 1 => ERMor1.comp A_one (fun _ : Fin 1
   => A_one_iter r)` has `A_one` *outside* and
   `A_one_iter r` *inside*.  Reading
   `comp f g`-as-function-composition, `f` is applied
   *after* `g`.  So at `r + 1`, the function value is
   `A_one ∘ (A_one_iter r)`, i.e. apply `A_one_iter r`
   first then `A_one`.  Prose and code agree.  ✓ (Just
   confirming.)

4. **Whether the `A_one` construction's
   `(by decide)`-checked Fin literals actually work at
   build time.**  `decide` on `0 < 1` and similar small
   bounds reduces to `Nat.decLt`, which evaluates
   trivially.  Should compile, but if it ever doesn't
   (because of some unexpected reducibility setting), use
   `Nat.lt_succ_self` or `by omega` instead.  Likely a
   non-issue.
