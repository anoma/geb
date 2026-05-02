# Adversarial review (round 2) of the ER ↔ K^sim_2 master design

> Reviewer's stance: fresh adversarial reading after round-1 revisions.
> No acceptance of design framing on faith.  Source materials
> re-read for verification: master design end-to-end (current
> revision), `LawvereKSim.lean` (simrec arity), `LawvereKSimQuot.lean`
> (KSimMor.ext, atDepth Subsingleton), `LawvereKSimPolynomialBound.lean`
> (`KMor1.linearBound_dominates` line 507), mathlib's
> `_root_.CategoryTheory.Functor.ext` (loogle-confirmed signature),
> Tourlakis 2018 page 22 ⊆ proof (re-read for level-2 majorization
> verification).

## Overall assessment

**The design is substantially improved.  The level-2
majorization arithmetic — the load-bearing math the round-1
review demanded — is now written out in §3.4 with explicit
constants, and the arithmetic verifies on independent re-
checking.  However, the renumbering / scoping pivot has left a
collection of dangling cross-references and one inconsistency
between the §3.4 theorem statement (split `def`/`theorem` per
F13 fix) and the §3.5 `kToER` body (which still uses
`.choose` against an existential).  These are fixable defects,
not architectural ones.**

The Path 2 strategy is sound and the prose proof of the
level-2 case is correct as written.  The `r_2 = 2,
offset_2 = r_H + r_G + 2` claim survives independent
adversarial verification of every arithmetic step.

Below: round-1 finding-by-finding fix verification, then
round-2 new findings.

---

## Round-1 fix verification

### F1 — §0.1.0.39 citation misidentifies subject

**Status: FIXED.** §3.6 line 1043-1050 now cites §0.1.0.34
(proof, p. 13) and §0.1.0.17 (b) for Cantor pairing in E^2,
explicitly noting "the design originally cited §0.1.0.39
here; that section is in fact about the URM-simulating
functions in K_4 and is not what we want."  §14.1 line
1927-1929 retains §0.1.0.39 only as a non-load-bearing
"noted here for completeness" entry.  Correct.

### F2 — Tupling polynomial bound shape was wrong

**Status: PARTIALLY FIXED.** §3.1 line 543-553 now states
the recurrence `B_{k+1} ≤ (M + B_k + 2)^2` (correct: from
`Nat.pair x y ≤ (x+y+1)^2` plus a bit of slack) and the
closed-form shape `(M + c_k)^{2^k}` for explicit constants
`c_k` "computed by the recurrence".  §15.12 still asserts
`tuplePack k v ≤ (max v + 1)^{2^k}` at line 2219 — the
older incorrect formula.  Step 1's cycle is left to derive
the precise `c_k` formula.

The closed-form `(M + c_k)^{2^k}` with truly constant `c_k`
is asymptotically correct but not literally tight: the
recurrence `(M+c_{k+1})^{2^{k+1}} ≥ (M + (M+c_k)^{2^k} +
2)^2` requires `c_{k+1}` chosen large enough to absorb the
inner `M`-dependence.  For very small `M` or `k` the
constants must be tuned (e.g. `c_2 = 2` works as
verified in this review).  The design's deferral to step 1
is acceptable but §15.12 should be updated to match §3.1.

**Recommended action.** Update §15.12 line 2219 to match
§3.1's `(M + c_k)^{2^k}` shape so the punch-list and §3.1
agree.

### F3 + F10 — `simultaneousBoundedRec` packing-bound and level-2 majorization arithmetic

**Status: FIXED (the load-bearing math is now written).**
§3.4 line 790-938 contains a prose proof of the level-2
case with explicit `r_2 = 2`, `offset_2 = r_H + r_G + 2`.

Independent verification of the arithmetic:

1. Closed-form induction `M_n ≤ A_1^{r_H + n·r_G}(max(n,
   max x⃗))`.  Base `n = 0`: ✓.  Step `n → n+1`: the proof
   uses `A_1^k(y) ≥ y` for `k ≥ 0` (true since `A_1(y) =
   2y+2 ≥ y`) plus monotonicity of `A_1` to fold the `max`.
   This goes through under the design's regime restriction
   (`n ≥ max x⃗`) AND without it: `max(n, max x⃗, M_n) ≤
   max(n, max x⃗, A_1^{r_H+n·r_G}(max(n, max x⃗))) =
   A_1^{r_H+n·r_G}(max(n, max x⃗))` because the third term
   dominates.  ✓
2. `A_1^{r_H + n·r_G}(M) ≤ 2^{r_H + n·r_G + 1}·(M+1)`:
   from `A_1^k(M) = 2^k · M + 2^{k+1} - 2 = 2^{k+1}·(M/2 +
   1) - 2 ≤ 2^{k+1}·(M+1)`.  ✓
3. With `M = max(n, max x⃗)` and `n ≤ M`:
   `2^{r_H + n·r_G + 1}·(M+1) ≤ 2^{r_H + M·r_G + 1}·(M+1)
   ≤ 2^{(r_H + r_G + 2)(M+1)}`.  Verified: the difference
   `(r_H+r_G+2)(M+1) - (r_H + M·r_G + 1 + log_2(M+1)) =
   2M + r_G + r_H + 1 - log_2(M+1) ≥ 0` for all `M ≥ 0`.
   ✓
4. `2^{(r_H+r_G+2)(M+1)} ≤ 2^{2^{M + r_H + r_G + 2}} =
   A_2^2(M + r_H + r_G + 2)`: needs
   `(r_H+r_G+2)(M+1) ≤ 2^{M+r_H+r_G+2}`.  Setting
   `K := r_H + r_G + 2`: `K·(M+1) ≤ 2^{M+K} = 2^M·2^K ≥
   (M+1)·K` since `2^K ≥ K` for `K ≥ 1` and `2^M ≥ M+1`
   for `M ≥ 0`.  ✓

Boundary cases:

- `n = 0`: `M_0 ≤ A_1^{r_H}(max x⃗) ≤ A_2^2(max x⃗ + r_H +
  r_G + 2)`.  ✓
- `max x⃗ = 0` and `n = 0`: `M_0 ≤ A_1^{r_H}(0) = 2^{r_H+1}
  - 2 ≤ A_2^2(r_H + r_G + 2) = 2^{2^{r_H+r_G+2}}` — since
  `r_H + 1 ≤ 2^{r_H+r_G+2}` for any non-negative `r_H, r_G`
  (the RHS is exponential, the LHS linear).  ✓

The prose proof is correct.  **F3 + F10 fix is sound.**

The note at the top of the review's "trace through the
arithmetic step-by-step" obligation is satisfied by the above.

### F4 — K^sim tupleAt at level ≤ 2 unsupported

**Status: FIXED via the credible workaround.** §3.1 line
568-585 explicitly drops K^sim-side tuplePack/tupleAt and
explains: "K^sim_2 simrec children must be at level ≤ 1, but
a Cantor-pair projection in K^sim requires step-functions
involving `mul ∈ K^sim_2`, pushing the simrec to level 3."
This matches round-1's recommendation.

Verifying the §3.5 simrec case does not implicitly need K^sim
tupling: the case at line 950-959 builds `bases : Fin (k+1) →
ERMor1 a` and `steps : Fin (k+1) → ERMor1 (a+1+(k+1))` from
recursive `kToER` calls on K^sim children, then invokes
`ERMor1.simultaneousBoundedRec`.  No K^sim tupling is touched
— K^sim's native `simrec` is the multi-output primitive on
the K^sim side; the multi-output → single-output translation
happens entirely on the ER side.  ✓

The arities line up: K^sim's `simrec` has `g : Fin (k+1) →
KMor1 (a + 1 + (k+1))` (LawvereKSim.lean line 53);
`ERMor1.simultaneousBoundedRec` per §3.2 has
`g : Fin (k+1) → ERMor1 (a + 1 + (k+1))` per the design's
interface block — match.  ✓

### F5 — Strict-equality round-trip claim

**Status: FIXED.** §11.1 line 1671 now explicitly says
"propositional functor equalities (Lean `Functor.ext`-
witnessed via `Quotient.sound` from interp-equality, not as
definitional `rfl`)".  This is the correct form.

Verification:

- `_root_.CategoryTheory.Functor.ext` exists in mathlib
  (Mathlib.CategoryTheory.EqToHom): signature `h_obj : ∀ X,
  F.obj X = G.obj X` plus `h_map` with `cat_disch`
  autoparam.
- For our case, `obj` agreement is `rfl` (both functors use
  `obj n := n`), so `eqToHom (h_obj X)` reduces to `𝟙` and
  `h_map` simplifies to `F.map f = G.map f`.
- That, in turn, reduces to `KSimMor.ext` (in
  `LawvereKSimQuot.lean` line 477, `@[ext]` lemma reducing
  to hom-field equality with `Subsingleton.elim` discharging
  the depth witness) plus `Quotient.sound` from extensional
  equality of interps via `kToER_interp` and `erToK_interp`.

The fix is materially correct.  Step 11's cycle still has
elaboration work (per CLAUDE.md memory's `_root_.Functor.ext`
collision note) but the architecture is sound.

### F6 — A_n indexing convention

**Non-defect in round 1.** Confirmed unchanged.

### F7 — `linearBound_le_A_one_iter` formula off-by-one

**Status: FIXED.** §3.4 line 740 now uses
`r := max ⌈log_2(c+1)⌉ ⌈log_2(d+2)⌉`.

Verification at edge cases:

- `d = 1`: `⌈log_2 3⌉ = 2`, `r = 2`, `A_1^2(x) = 4x+6 ≥
  c·x + 1`.  ✓
- `d = 0`: `⌈log_2 2⌉ = 1`, `r = 1`, `A_1^1(x) = 2x+2 ≥
  c·x + 0` for `c ≤ 2`; for larger `c`, `r = ⌈log_2(c+1)⌉`
  dominates.  ✓
- `c = 0, d = 0`: `r = max 0 1 = 1`.  Note: design's prose
  at line 759 says "`c = 0, d = 0`: `r = 0` works".  This
  is inconsistent with the formula, which gives `r = 1`.
  Both are valid (the formula is conservative; r=0 also
  works for c=d=0 since `A_1^0(x) = x ≥ 0`).  Minor prose-
  vs-formula inconsistency, not a math defect.

The formula is correct; the comment is loose.

**Recommended action.** Update §3.4 line 759 to read
"`c = 0, d = 0`: `r = 1` per the formula (`r = 0` would
also work but the formula picks `r = 1`)".

### F8 — Categorical iso decorative

**Status: PARTIALLY FIXED.** §3.1 line 588-594 now refers to
`LawvereERCat.tupleIso (n : ℕ) : (n + 1) ≅ 1` as
"decorative, witnessing that ER-side products of the
generator collapse via Cantor pairing in the morphism
quotient".  The K^sim-side analogue is explicitly dropped
(see F4).  The "direct evidence ... does not have more
computational content" language at line 523-527 is somewhat
softened but still over-states.  Acceptable.

### F9 — Existing dominance theorem reuse

**Status: FIXED.** §3.4 line 360-369 references
`KMor1.linearBound_dominates` (verified at
`LawvereKSimPolynomialBound.lean:507` with the right
signature: bound on `f.interp ctx`, not on
`(kToERDirect f).interp`).  Old `kToERDirect_*` references
retired or noted as "equivalent under interp-preservation
but ... `KMor1.linearBound_dominates` is more direct".

### F10 — Level-2 majorization arithmetic

**Status: FIXED.** See F3 verification above.

### F11 — URM K^sim → URM material is dead post-pivot

**Status: FIXED.** §6 now contains only §6.1 (URMSubroutinesER)
and §6.2 (KSimSubroutinesURM).  §7 contains only §7.1 (K^sim
simulator for URM) and §7.2 (interp-preservation).  §8 contains
only §8.1 (ER → URM compiler) and §8.2 (compiler interp-
preservation).  No `compileKSim`-style K^sim → URM material.

But this leaves dangling cross-references — see G1, G2 below.

### F12 — `KMor1.linearBound` exists only for level ≤ 1

**Non-defect in round 1.** Still consistent.

### F13 — Constructive `r` extraction

**Status: PARTIALLY FIXED.** §3.4 line 770-788 now correctly
splits into `def KMor1.majorize_r` and `theorem
KMor1.majorize_by_A_two_iter`.  But §3.5 line 955 still has:

```lean
let r := KMor1.majorize_by_A_n_iter f h |>.choose
```

This uses `.choose` against a theorem name that contradicts
the §3.4 split (where the data is in `majorize_r` and the
theorem is `majorize_by_A_two_iter`).  Real internal
inconsistency — see G3 below.

### F14 — ERMor1 matches Wikipedia

**Non-defect in round 1.** Unchanged.

### F15 — K^sim simrec recurses on first argument

**Non-defect in round 1.** Confirmed by re-reading
`LawvereKSim.lean:50-54`.

### F16 — Handoff document misreading of Tourlakis

**Status: FIXED.** §1.2 line 140-146 explicitly notes the
handoff's URM-both recommendation was wrong and adopts
the structural-⊆ / URM-⊇ split per Tourlakis page 22.

### F17 — Dead infrastructure not cleanly retired

**Status: PARTIALLY FIXED.** §12 line 1722-1726 still flags
`KSimSzudzikSimrec.lean`'s `kSimPackedBase/Step` and
`kSimTowerBound` as "dead code from the renamed direct
path".  No "Step 0.5 kill list" was added.  Acceptable as a
soft commitment but the dead code remains in the repo.

---

## Round-2 new findings

### G1 — Dangling cross-references to deleted subsections (defect)

**Claim being challenged.** The design references
`§6.3`, `§7.3`, `§9.4` at multiple sites, but those
subsections do not exist in the current design.

**Verification.**  `grep -n "§6\.3\|§7\.3\|§9\.4"` over the
master design:

- Line 1450: "Mirror of §6.3" (in §6.2's intro) — §6.3 does
  not exist (was the old `ERSubroutinesURM` section, now
  deleted under Path 2).
- Line 1854: "interp proofs (§7.3)" — §7.3 does not exist.
- Line 1877: "dispatch tree (§6.3, §7.1)" — §6.3 does not
  exist.
- Line 1391: "see §1.4 and §9.4" — §9.4 does not exist.
- Line 2164: "§6.2, §9.4" — §9.4 does not exist.
- Line 2195: "spot-check §9.4 (erToK side)" — §9.4 does not
  exist.

These are leftover from the pre-pivot section structure.

**Verdict.**  Defect (documentation).

**Recommended action.**  Sweep all `§N.M` references and
either (a) delete the orphaned reference, (b) point at the
nearest extant subsection, or (c) re-introduce the missing
subsection if there is content that ought to live there.

### G2 — Dead reference to `boundExpr f : ERMor1 a` in §13.1 (defect)

**Claim being challenged.** §13.1 line 1865-1867:
"`LawvereERPolynomialBound.lean`'s `ERMor1.PolyBound` and
builders — certifying that `boundExpr f` is a genuine ER
expression at level ≤ 2 (§9)."

**Verification.**  `boundExpr f` (kToER-side runtime bound
in ER) is the Path-1 entity that has been retired under
Path 2.  Path 2's analogue is `boundExprK e : KMor1 a`
(erToK-side, in K^sim, not ER) defined in §9.1.  The §13.1
text refers to an ER-typed bound that no longer exists in
the design.

**Verdict.**  Defect.

**Recommended action.**  Update §13.1 to refer to
`boundExprK e : KMor1 a` and clarify that `ERMor1.PolyBound`
is used for ER terms within `boundExprK`'s construction (or
delete the reference if not load-bearing).

### G3 — `kToER` simrec case uses `.choose` against split theorem (defect)

**Claim being challenged.** §3.5 line 955:

```lean
let r := KMor1.majorize_by_A_n_iter f h |>.choose
```

This invokes `.choose` (Classical extraction from `∃`)
against a theorem whose §3.4 statement (line 777-781)
takes a separate `def KMor1.majorize_r` providing the
constructive witness directly.

**Verification.**

- §3.4 line 770-781 states the split: `def
  KMor1.majorize_r f h : ℕ` produces the constructive `r`,
  and `theorem KMor1.majorize_by_A_two_iter ... : f.interp
  v ≤ (A_two_iter (majorize_r f h)).interp ![vMax v]` is
  a Prop-valued inequality.
- §3.5 line 955 invokes `.choose` against
  `KMor1.majorize_by_A_n_iter f h`, which is not a
  `Classical.choice`-extractable existential under the §3.4
  split — it is the inequality theorem.  The data is in
  `majorize_r`.

This is internal inconsistency between §3.4 and §3.5 plus
a violation of the constructive-discipline obligation
(F13's fix).  CLAUDE.md forbids `Classical`; `.choose` on a
non-`Decidable`-decided existential requires `Classical` in
general.

**Verdict.**  Defect.

**Recommended action.**  Update §3.5 line 955 to:

```lean
let r := KMor1.majorize_r f h
```

and use the inequality theorem (`majorize_by_A_two_iter`)
in the correctness proof of `kToER_interp`'s simrec case
(to verify `bound` dominates the iteration values).
Similarly in any other `kToER` callsites.

### G4 — `simultaneousBoundedRec`'s bound-input contract is under-specified (needs-clarification)

**Claim being challenged.** §3.5 line 956-958 builds
`bound := comp (A_two_iter r) ![maxCtxER (a+1)]` from the
`r` produced by `majorize_by_A_n_iter` (a bound on
*component* values per §3.4).  But
`ERMor1.simultaneousBoundedRec` per §3.2 is implemented by
packing the (k+1)-tuple via `Nat.tuplePack` and recursing
on the packed state via `boundedRec`.  `boundedRec`'s
truncation tests on the *packed-state value*, so its
`bound` argument must dominate the packed value — not just
the component value.

**Verification.**  By the F2-fixed bound,
`tuplePack(F_0, ..., F_k) ≤ (max F_j + c_k)^{2^k}`.  With
`max F_j ≤ A_2^2(vMax v + offset)` per §3.4, the packed
value is `≤ (A_2^2(...) + c_k)^{2^k}`, which is at most
`A_2^3(vMax v + offset')` for a slightly larger `offset'`
(absorbing the polynomial-of-2-tower into one extra
exponential).

The §3.2 design says "the kToER outer level sees a clean
ERMorN multi-output interface; the packing arithmetic does
not leak into majorization or interp-preservation proofs",
which would mean `simultaneousBoundedRec` accepts the
*component* bound and internally derives the packed-state
bound.  But the interface signature in §3.2 line 619-626
takes `bound : ERMor1 (a + 1)` without specifying whether
that bound is the component bound or the packed-state
bound.

**Verdict.**  Needs-clarification.  If the interface
contract is "bound dominates the component values" with
`simultaneousBoundedRec` internally applying the packing
slack, that is correct and §3.5's `r` from `majorize_r`
is the right input.  If the interface contract is "bound
dominates the packed-state value", §3.5's `bound`
construction is short by one A_2 layer (needs an extra
height-1 inflation to absorb tuplePack).

**Recommended action.**  Step 2's cycle must explicitly
state in the interface docstring whether `bound` is a
component bound or a packed-state bound.  If component:
the implementation must derive a packed-state bound from
it via the F2 closed-form bound, packaged into the
underlying `boundedRec` call.  Step 5's cycle must verify
the call site at §3.5 line 956 matches the chosen contract.

### G5 — F2 punch-list (§15.12) not updated to match §3.1 (minor defect)

**Claim being challenged.** §3.1 line 543-553 states the
correct recurrence and closed-form `(M + c_k)^{2^k}`.  But
§15.12 line 2218-2220 still asserts the old
`tuplePack k v ≤ (max v + 1)^{2^k}` (the round-1-flagged
under-counted version).

**Verification.**  Direct text comparison.

**Verdict.**  Minor defect (internal inconsistency).

**Recommended action.**  Update §15.12 to match §3.1's
`(M + c_k)^{2^k}` formula.

### G6 — §16.4 typo "§15.1-14.10" (typographical defect)

**Claim being challenged.** Line 2329-2330: "If during a
per-step cycle the adversarial review identifies an
obstacle that revisits a prior-failure-mode hypothesis
(§15.1-14.10), pause and re-open this master design".

**Verification.**  "§15.1-14.10" is a typo: should be
"§15.1-15.16" (the punch-list goes 15.1 through 15.16).

**Verdict.**  Typographical defect.

**Recommended action.**  Fix to `§15.1-15.16`.

### G7 — Coverage of the proof chain is end-to-end (positive finding)

**Verification.**  The kToER side (steps 1–5) now
produces `kToER`, `kToERN`, `kToERFunctor` with the
level-2 majorization theorem (§3.4) discharging
`boundedRec`'s truncation hypothesis.  The erToK side
(steps 6–10) produces `compileER`, `simulateInKSim`,
`boundExprK`, `erToK`, `erToKFunctor` per the URM
chain.  Step 11 packages the strict iso.  The kToER
critical path is `0 → 1 → 2 → 3 → 4 → 5 → 11` (7
cycles); erToK is `0 → 6 → 7 → 8/9 → 10 → 11` (6
cycles).

The chain has no logical gaps modulo G3 (the `.choose`
inconsistency) and G4 (the `bound` contract).

**Verdict.**  Non-defect.  Coverage is complete in
principle.

### G8 — Constructive `r_2 = 2` claim is correct (positive finding)

**Claim being challenged.** §3.4 line 902 states `r_2 :=
2` is constant for level 2 (regardless of K^sim term
structure beyond the `r_H, r_G` offset).

**Verification.**  Re-reading the prose proof: the
TOWER HEIGHT is constant 2; the OFFSET (`r_H + r_G + 2`)
depends on the children's level-1 majorant constants
which are functions of the K^sim term's structure.  This
matches the F3+F10 fix and is exactly the
"no `3^E` analog" property the design claims.  The claim
is correct as stated and the prose proof realizes it.

**Verdict.**  Non-defect.

### G9 — `n ≤ vMax v` substitution is a valid over-approximation (positive finding)

**Claim being challenged.** §3.4 line 891 uses "the
simrec's recursion variable is `v 0` (component 0 of the
input vector), bounded by `vMax v`".

**Verification.**  K^sim's simrec recurses on the
first argument per `LawvereKSim.lean:50-54` (output arity
`a + 1`, position 0 is the recursion variable).  At call
site `f.interp v`, the simrec body sees `v 0` as the
recursion count.  Since `vMax v = max v 0 (...) ≥ v 0`,
substituting `vMax v` for `n = v 0` is a valid over-
approximation.  The bound `M_n ≤ A_2^2(vMax v + offset)`
then specializes to `F_i(v 0, x⃗) ≤ A_2^2(vMax v + offset)`.
✓

**Verdict.**  Non-defect (the substitution is technically
loose but conservatively correct).

### G10 — erToK side scoping under Path 2 (positive finding)

**Claim being challenged.** §9 says "Under Path 2, the
runtime bound is needed only for the `erToK` direction".

**Verification.**  §9 now contains §9.1 (`boundExprK e :
KMor1 a` in K^sim_2 for ER → URM runtime) and §9.2 ("Why
`boundExprK e` is in K^sim_2").  The kToER-side runtime
bound `boundExpr f : ERMor1 a` from Path 1 is gone.  §9
fits cleanly into the erToK chain (compileER, simulateInKSim,
boundExprK, erToK).  No `kToER`-side runtime bound is
referenced anywhere in §9.

§13.1's leftover reference to `boundExpr f` (G2) is the
only orphan from this scoping.

**Verdict.**  Non-defect for the §9 itself; G2 is the
documentation orphan.

### G11 — Path 2 packing-bound vs Path-1 trap (positive finding, with caveat at G4)

**Claim being challenged.** §3.8 line 1133-1141: Path 2
avoids the `3^E` trap by encapsulating packing inside
`simultaneousBoundedRec`.

**Verification.**  The level-2 prose proof in §3.4 bounds
the *unpacked* components `M_n = max_j F_j(n, x⃗)` by
`A_2^2(vMax v + offset)`.  This bound is derived without
ever invoking `simultaneousBoundedRec`'s polyBound — it
uses only the children's A_1^r bounds and the recursion
arithmetic.

This means the kToER outer level (where `kToER_interp`'s
correctness is proved) sees the bound through the
`simultaneousBoundedRec_interp_correct` interface, which
asserts that *when bound dominates iteration values*, the
ER computation matches the K^sim simrec.  The
"iteration values" here are the packed values, and the
bound provided is on components — there is a slight mis-
match.  See G4 for the implications.

If `simultaneousBoundedRec` is implemented to accept the
component bound and internally inflate it for packing,
the absence of `3^E` blowup is genuine: the inflation is
a fixed polynomial in `2^k`-degree of the component bound,
which is dominated by one extra A_2 layer (height 3
instead of height 2).  The TOWER HEIGHT stays at fixed 3
(or 2 if the implementer is more clever), with offset
accumulating additively.  No `3^E` analog.

**Verdict.**  Non-defect, conditional on G4 being
resolved correctly.

---

## Top items the author MUST address

The design is broadly sound and the level-2 prose proof
verifies independently.  Three items still need fixing
before step 1's cycle proceeds:

1. **G3 (`.choose` inconsistency).** §3.5 line 955 uses
   `.choose` against a theorem whose §3.4 statement was
   split into a `def`-based constructive form per F13.
   This is a fixed-text edit: replace with
   `KMor1.majorize_r f h` and propagate.

2. **G1 + G2 (dangling cross-references).** Sweep §6.3,
   §7.3, §9.4 references and the `boundExpr f` leftover
   in §13.1.  All are either point-fixes or one-line
   deletions.

3. **G4 (`simultaneousBoundedRec` bound contract).**
   Step 2's cycle must explicitly state whether the
   `bound` argument to `simultaneousBoundedRec` is a
   component bound or a packed-state bound, and step 5's
   cycle must verify the call site matches.  If the
   contract is "component bound", the implementation
   must internally absorb the F2-fixed packing slack via
   one extra A_2 layer.

Items G5 (§15.12 not synced with §3.1), G6 (§16.4 typo),
and the F7 prose loose-end (`c=d=0` says r=0 when formula
gives r=1) are minor and can be folded into G1/G2's text-
sweep pass.

The level-2 prose proof itself, the F5 functor-equality
fix, the F4 K^sim-tupling drop, the F9 `KMor1.linearBound_dominates`
reuse, the F11 dead-URM-material removal, and the F16
handoff-misreading correction are all materially correct.

End of round-2 adversarial review.
