# Round-3 adversarial review — erToK via Tourlakis URM simulation

Reviewer: fresh-context `general-purpose` Agent (round 3).
Artefact under review:
[`2026-05-16-er-to-k-via-cslib-urm-design.md`](2026-05-16-er-to-k-via-cslib-urm-design.md).
Prior rounds:
[`.review-1.md`](2026-05-16-er-to-k-via-cslib-urm-design.review-1.md),
[`.review-2.md`](2026-05-16-er-to-k-via-cslib-urm-design.review-2.md).

Author response convention as in prior rounds.

## Citation verification log

External (Tourlakis 2018) verified at PDF for §0.1.0.2,
.7, .9, .17, .20, .27, .36, .37, .42, .43, .44, plus
pp. 19–21 worked examples. All PASS at cited locations.
**Exception**: §0.1.0.4 citation as "defines
A_{n+1}(x) = A_n^r(x) as r-fold iteration of A_n" FAILS
at p. 2 (which states only `λx.A_n(x) ∈ K_n`; the
iterative Ackermann recursion is in an external
subsection not contained in the 25-page PDF). Serious
S1.

§0.1.0.17(c) cited at §3.1 for `pow2 = A_2 = λx.2^x`:
p. 7 establishes `λx.2^x ∈ K^sim_2` but does not equate
`λx.2^x` with the Ackermann function `A_2`. The
identification is conventional but not literally in the
text. Minor M1.

Internal repository line numbers: all verified except
`LawvereKSimInterp.lean:122` (vague — points to private
helper rather than public `KMor1.interp_simrec` at
line 162; Minor M4) and `KArith.lean:414` for
`KMor1.signum` (actual `def` at line 420; Minor M5).

## Other verification log

**Level arithmetic.** §6.2 and §7.1 level claims trace
correctly through `KMor1.level` semantics. PASS.

**§6.1 recursion equations.** Match Tourlakis p. 16
line-by-line under the 1-indexed → 0-indexed PC shift.
PASS.

**§8.1 erToK formula.** Matches §0.1.0.44 proof p. 22.
PASS.

**§9.1 dependency graph.** No import from
`LawvereKSimER`. Independent of kToER load-bearing
path. PASS.

**§10 constructive discipline.** Spec uses `Fin.find`,
not `Classical.choose`. The `Classical.choose` form is
shown in §4.3 only as a contrast (the rejected
candidate). PASS.

**§5.1 per-template walk-through.** For
`compileER (succ)` on input `v = ![3]`: template
"V_out ← 0; loop V_in times {V_out ← V_out + 1}; V_out
← V_out + 1; stop". V_out goes 0 → 3 → 4 = succ 3. ✓
But the M-template's loop on V_in destroys V_in (the
loop body includes `V_in ← V_in ∸ 1`). The
clone-at-compile-time discipline says copies are
"destructive of a fresh scratch slot, not of the
original input" — but the M-template is destructive of
the *source* (the input register), not just the
destination. Repeated `proj` reads of the same input
register inside `comp` produce 0 after the first read,
unless restoration is performed. Serious S2.

## Findings

### Blocker

(none)

### Serious

#### S1. §3.1 / §7.1 §0.1.0.4 citation for A_{n+1}(x) = A_n^r(x) is incorrect

§0.1.0.4 on p. 2 states only `λx.A_n(x) ∈ K_n`; it does
not define `A_{n+1}` as r-fold iteration of `A_n`. The
iterative Ackermann recursion is referenced as
belonging to an external Ackermann subsection not
contained in the 25-page PDF excerpt the project has.
Remediation options:

- (i) Cite the actual Ackermann-subsection location
  (likely Tourlakis 1984 [bibliography reference [8]]
  or the course's separate Ackermann-function notes).
- (ii) Restate the spec to avoid claiming `A^r_2` as
  such. Use `pow2_iter r := r`-fold composition of
  `KMor1.pow2`; cite §0.1.0.17(c) for `pow2 ∈
  K^sim_2`; note that this functions as the runtime
  majorant per §0.1.0.27(4) and §0.1.0.44 proof's
  general scheme, but the spec does not claim
  `pow2_iter r = A^r_2`.

**Response:** fix via option (ii). Rename
`KMor1.A_two_iter` to `KMor1.pow2_iter` throughout
§3.1, §7, §8, §13.1, §13.2. Drop the §0.1.0.4
citation. Keep §0.1.0.17(c) for `pow2 ∈ K^sim_2` and
§0.1.0.44 proof for the runtime-majorant role. The
domination theorem §7.3 still holds: we are bounding
URM runtime by some level-2 K^sim term; whether that
term *equals* `A^r_2` literally is irrelevant once
domination is established. Option (i) would require
locating a Tourlakis publication outside the project's
PDF; option (ii) is self-contained.

#### S2. §5.1 register-allocation discipline inconsistent with Tourlakis's M-template

The spec's clone-at-compile-time discipline claims
"this discipline avoids any in-template 'restoration'
step: each copy is destructive of a fresh scratch
slot, not of the original input." But Tourlakis's
M-template (p. 19) is destructive of the *source*: the
loop body decrements V_src to zero while incrementing
V_dest. Repeated reads of the same input register
inside `comp` (which is the common case — every
`proj i` reads V_{inputRegs i}) would each read 0
after the first, producing wrong results.

Remediation: either (a) commit to the standard URM
preserving-transfer idiom (two scratch registers V_b
and V_tmp; first loop copies V_a into both V_b and
V_tmp while zeroing V_a; second loop copies V_tmp back
into V_a) and acknowledge each `proj i` emits two
loops, not one; or (b) pre-clone all inputs into N
copies at the program prelude using the two-loop
idiom, with `N` = number of `proj i` consumers in `e`.

**Response:** fix via option (b). Pre-clone inputs at
the program prelude: for each `i : Fin a` and each
consumer of input slot `i` in `e` (counted at
compile time during the structural recursion), the
prelude allocates a fresh scratch register `V_src_{i,j}`
(for the j-th consumer) and uses the standard
preserving-transfer idiom (two loops per scratch
register, one to copy V_{inputRegs i} into both
V_src_{i,j} and V_tmp_{i,j}, one to restore
V_{inputRegs i} from V_tmp_{i,j}). After the prelude,
all consumers read from distinct V_src_{i,j} registers.
The prelude's instruction count is `2 · k_i` per input,
where `k_i` is the consumer count for input `i`; total
overhead is linear in the size of `e`. Each per-template
`proj i` then reads V_src_{i,j} for the next available
`j`, consuming it destructively (no in-template
restoration needed because the prelude prepared a fresh
clone for this specific consumption).

This makes the register-allocation discipline
self-consistent: the prelude is the only place where
the preserving-transfer two-loop idiom appears; the
per-ER-constructor templates use destructive transfers
only and read from prelude-prepared clones.

### Minor

#### M1. §3.1 / §13.1: identification of `pow2` with `A_2` is convention, not literal

§0.1.0.17(c) (p. 7) establishes `λx.2^x ∈ K^sim_2` but
does not equate `λx.2^x` with the Ackermann function
`A_2`. The standard convention places `A_2(x)` ≈ `2^x`
with constant slack. Since `boundExprK` only needs a
majorant and `r_e` is held abstract, slack is absorbed.

**Response:** fix via the same renaming as S1 (drop
the `A_2` identification entirely; use `pow2_iter`).

#### M2. §6.1 misattributes the equality-predicate citation

§6.1's "By Tourlakis §0.1.0.17 (p. 6–7), `λx.x = a ∈
K^sim_{1,*}`" should cite §0.1.0.20 (p. 7); §13.1
cites §0.1.0.20 correctly.

**Response:** fix.

#### M3. §5.2 misattributes a quote

§5.2 cites the quote "any `λx⃗.f(x⃗) ∈ E^n` is
URM-computable within time `λx⃗.t(x⃗) ∈ E^n`" to
"Tourlakis §0.1.0.42 (p. 18) and §0.1.0.43 (p. 21)"
jointly. The quote is from §0.1.0.42 alone;
§0.1.0.43 is the Ritchie–Cobham equivalence
containing it.

**Response:** fix.

#### M4. §13.2 `LawvereKSimInterp.lean:122` is vague

Cited as "simrec interp case"; line 122 begins the
private helper `KMor1.interp_simrec_eq_simrecVec`; the
public simp lemma `KMor1.interp_simrec` is at line 162.

**Response:** fix. Replace `:122` with `:162` and
update the label to "`KMor1.interp_simrec` (simp
lemma)".

#### M5. §3 inventory `KMor1.signum` line 414 vs 420

Actual `def` at line 420; line 414 is mid-docstring.

**Response:** fix. Replace `:414` with `:420`.

#### M6. §4.1 `URMProgram` does not enforce `outputReg ∉ inputRegs.range`

Tourlakis's convention V_1 = output is disjoint from
V_2,…,V_{n+1} = inputs. The structure as written
permits aliasing, which would invalidate the base-case
equation `v_outputReg(0, x⃗) = 0`.

**Response:** fix. Add an explicit field
`outputReg_not_input : ∀ i, P.inputRegs i ≠ P.outputReg`
to the `URMProgram` structure. `compileER` discharges
this by allocating `outputReg` fresh.

### Cosmetic-taste

#### C1. §6.2 PC-dispatch presented as text snippet

Consider rendering as Lean pseudocode to match other
sections.

**Response:** reject-as-cosmetic-taste (current
presentation is readable and consistent with adjacent
plain-text dispatch tables).

#### C2. §3 table column "Tourlakis citation" inconsistent

Several entries use shorthand like "(signum)", "(proj,
std.)", "(composition)", "(sing. simrec)". Replace
with explicit page references or "not in Tourlakis;
standard" notation.

**Response:** fix. Use a uniform column format.

#### C3. §4.3 keeps the `Classical.choose` form for narrative contrast

Consider striking it to reduce reader confusion about
which definition stands.

**Response:** fix. Strike the `Classical.choose`
variant; keep a one-line note explaining the
constructive-discipline choice.

## Convergence assessment

Round does NOT converge: zero blocker(s), two serious
finding(s).
