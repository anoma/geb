# Phase IV-B Task 17c — chain assembly plan (D.1–D.5)

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> `superpowers:subagent-driven-development` (recommended) or
> `superpowers:executing-plans` to implement this plan
> task-by-task.  Steps use checkbox (`- [ ]`) syntax for
> tracking.

**Goal:** discharge the Phase IV-B headline theorem
`kSimTowerBound_dominates_inline` (level-2 simrec
dominance) by building per-child `PolyBound`s for level-1
K^sim children, plumbing them through
`kSimPackedBase_polyBound` / `kSimPackedStep_polyBound`,
applying the polynomial-iter bound, and closing into
`kSimTowerBound`'s closed-form tower expression.

**Architecture:** mirrors the level-1 template
`kSimTowerBound_dominates_level_one` (`LawvereKSimPolynomialBound.lean`
line 2578+), but starts from polynomial (not linear)
bounds on the packed step.  The chain runs:

1. Per-l, build `PolyBound (kToER (child l))` for level-1
   K^sim children via a new recursive `kToER_polyBound_of_level_one`.
2. Lift to packed PolyBounds via the existing
   `kSimPackedBase_polyBound` / `kSimPackedStep_polyBound`.
3. Apply `to_iter_step_form` to convert the packed
   step's PolyBound to single-power form.
4. Apply `Nat.polynomial_iter_tower_bound` to bound the
   j-iterated trace by `tower 2 (linear)`.
5. Bump `tower 2 → tower 3` via
   `tower_two_le_tower_three_linear`.
6. Lift `tower 3 → tower (stepTH + 1)` via
   `tower_mono_left` (uses `stepTH ≥ k + 2 ≥ 2`).
7. Absorb the linear argument into `kSimTowerBound`'s
   closed-form expression via `tower_mono_right` (uses
   the new D.3.2 chain-closing log-vs-tH lemma).

**Tech stack:** Lean 4, mathlib, `lake build` /
`lake test`.

**Convention:** every committed task ends in a clean
`lake build` plus `lake test`, with commit subject
`(Task 17c D.X)`.  Per-task labels use the existing
completion-plan numbering: D.2 = per-child PolyBound
builder, D.3 = packed-PolyBound plumbing + chain-closing
lemma, D.4 = polynomial-iter application, D.5 =
tower-arithmetic closeout.  Project policy: no `sorry`
or `admit` in committed state.  Therefore D.1 (the
headline-theorem stub) is folded into D.5's final
commit — the headline lands fully proven, not stubbed.

---

## File structure

The plan touches one module:

- **Modify** `GebLean/LawvereKSimPolynomialBound.lean`:
  add a new section after the existing
  `kSimTowerBound_dominates_level_one` (line 2578) that
  contains the level-2 analogs.  Specifically:
  - `kToER_polyBound_of_level_one` — recursive
    `PolyBound` builder for level-≤-1 K^sim translations
    (D.2; standalone commit).
  - `linearBoundLog_packedStep_le_towerHeight` (or
    similar) — the chain-closing log-vs-tH lemma at the
    packed step's PolyBound (D.3.2; standalone commit).
  - `kSimTowerBound_dominates_inline` — the headline
    public theorem (D.1 + D.3.1 + D.4 + D.5; one
    combined commit).

No new files are created.  All landed infrastructure is
in place (verified via grep on commit `4880d884`):

- `kSimPackedBase_polyBound` / `kSimPackedStep_polyBound`
  (lines 738, 817).
- `to_iter_step_form` (`LawvereERPolynomialBound:503`).
- `Nat.polynomial_iter_tower_bound`
  (`Utilities/ComputationalComplexity:471`).
- `Nat.tower_two_le_tower_three_linear`,
  `Nat.pow_le_tower_two_with_shift` (Utilities).
- `GebLean.tower_mono_left`, `GebLean.tower_mono_right`,
  `GebLean.self_le_tower` (Utilities/Tower).
- `kSimPackedStep_towerHeight_ge_succ_k` (this file,
  line 1376; private).
- `KMor1.linearBoundLog_le_towerHeight` (this file,
  line 1828; public).
- `ERMor1.PolyBound.ofZero` / `ofSucc` / `ofProj` /
  `ofComp` / `ofBoundedRec` (`LawvereERPolynomialBound`,
  per-constructor builders; `ofBoundedRec` landed at
  `f48ecf78`).

---

## Task D.2: per-child PolyBound builder

**Files:**

- Modify: `GebLean/LawvereKSimPolynomialBound.lean`
  (insert after `KMor1.linearBoundLog_le_towerHeight`,
  currently around line 2200).

**Goal:** add a recursive function

```lean
def KMor1.kToER_polyBound_of_level_one :
    {a : ℕ} → (f : KMor1 a) → (h : f.level ≤ 1) →
    ERMor1.PolyBound (kToER f (Nat.le_succ_of_le h))
```

that constructs an `ERMor1.PolyBound` for every level-≤-1
K^sim term's ER translation.  Used at the call site of
the headline theorem to feed `kSimPackedBase_polyBound`
and `kSimPackedStep_polyBound`.

**Cases:**

- `zero` / `succ` / `proj`: per-constructor builders
  (`ofZero` / `ofSucc` / `ofProj`).
- `comp f gs`: `ofComp` applied to the recursive
  `kToER_polyBound_of_level_one` for `f` and each `gs i`.
- `raise f`: `kToER (raise f) = kToER f` definitionally,
  so reuse the recursive call on `f` (which has
  `level ≤ 0 ≤ 1`).
- `simrec h_fam g_fam i`: `kToER` produces a
  `comp (kSimSzudzikUnpackAt _) (...)` wrapping a
  `boundedRec` whose components are level-0 ER
  translations.  Build a `PolyBound` via `ofComp`
  applied to:
  - `kSimSzudzikUnpackAt`'s atomic-ER PolyBound
    (built via `ofComp`/`ofProj`/etc. on its definition).
  - For the `recur` branch: `ofBoundedRec` applied to
    the level-0 children's PolyBounds (which come from
    A.5.2's level-0 infrastructure).
  - For the `proj _` branches: `ofProj`.

The simrec case is the meatiest because of the deeply-
nested `kToER` body.  Total estimated ~150-250 lines.

- [ ] **Step D.2.1: State the function with case
  skeleton + `_` holes**

```lean
/-- Recursive `PolyBound` builder for level-≤-1 K^sim
translations.  Used by `kSimTowerBound_dominates_inline`
to feed `kSimPackedBase_polyBound` /
`kSimPackedStep_polyBound`.

Public; consumed by Phase IV-B headline assembly. -/
def KMor1.kToER_polyBound_of_level_one :
    {a : ℕ} → (f : KMor1 a) → (h : f.level ≤ 1) →
    ERMor1.PolyBound (kToER f (Nat.le_succ_of_le h))
  | _, .zero,         _ => _
  | _, .succ,         _ => _
  | _, .proj _,       _ => _
  | _, .comp f gs,    h => _
  | _, .raise f,      h => _
  | _, .simrec _ _ _, h => _
```

Build will fail with "unsolved goals" per case.  This is
intentional and serves as a case-by-case to-do list.

- [ ] **Step D.2.2: Fill atomic cases (zero/succ/proj)**

```lean
  | _, .zero,         _ => by
      change ERMor1.PolyBound (ERMor1.zeroN _)
      exact ERMor1.PolyBound.ofZeroN _
  | _, .succ,         _ => by
      change ERMor1.PolyBound ERMor1.succ
      exact ERMor1.PolyBound.ofSucc
  | _, .proj i,       _ => by
      change ERMor1.PolyBound (ERMor1.proj i)
      exact ERMor1.PolyBound.ofProj i
```

The exact constructor names (`ofZeroN`, `ofSucc`,
`ofProj`) are confirmed via `grep -n
"ERMor1.PolyBound.of" GebLean/LawvereERPolynomialBound.lean`.
If a constructor name differs, adjust accordingly; the
mathematical content is the same.

The `change` rewrites match the `kToER`'s atomic-case
output: `kToER zero = ERMor1.zeroN _`,
`kToER succ = ERMor1.succ`, `kToER (proj i) = ERMor1.proj i`.

- [ ] **Step D.2.3: Fill `raise` case**

```lean
  | _, .raise f,      h => by
      have hf : f.level ≤ 0 := by
        unfold KMor1.level at h; omega
      have hf_one : f.level ≤ 1 := Nat.le_succ_of_le hf
      -- kToER (raise f) = kToER f definitionally.
      change ERMor1.PolyBound
        (kToER f (Nat.le_succ_of_le hf_one))
      exact KMor1.kToER_polyBound_of_level_one f hf_one
```

If `change` doesn't elaborate cleanly, use
`show` with the expected type or thread an explicit
ascription on the recursive call.

- [ ] **Step D.2.4: Fill `comp` case**

```lean
  | _, .comp f gs,    h => by
      have hf : f.level ≤ 1 := by
        unfold KMor1.level at h
        exact le_trans (le_max_left _ _) h
      have hgs : ∀ i, (gs i).level ≤ 1 := fun i => by
        unfold KMor1.level at h
        have hsup : Finset.univ.sup
            (fun j => (gs j).level) ≤ 1 :=
          le_trans (le_max_right _ _) h
        exact le_trans
          (Finset.le_sup
            (f := fun j => (gs j).level)
            (Finset.mem_univ i))
          hsup
      change ERMor1.PolyBound
        (ERMor1.comp (kToER f (Nat.le_succ_of_le hf))
          (fun i => kToER (gs i)
            (Nat.le_succ_of_le (hgs i))))
      apply ERMor1.PolyBound.ofComp
      · exact KMor1.kToER_polyBound_of_level_one f hf
      · intro i
        exact KMor1.kToER_polyBound_of_level_one
          (gs i) (hgs i)
```

The `change` rewrites `kToER (comp f gs)` to its
definitional unfolding.  If the elaborator complains,
replace with `simp only [kToER]` or unfold manually.

`ERMor1.PolyBound.ofComp`'s exact signature should be
verified via grep; the argument order may need
adjustment.

- [ ] **Step D.2.5: Fill `simrec` case**

This is the meatiest case.  The simrec wrapping is

```text
kToER (simrec i h_fam g_fam) =
  comp (kSimSzudzikUnpackAt a i.val)
    (fun j => if j.val = 0 then recur else proj …)
where
  recur = boundedRec (kSimPackedBase h_ER)
                     (kSimPackedStep g_ER)
                     (kSimTowerBound h_ER g_ER)
  h_ER l = kToER (h_fam l) _
  g_ER l = kToER (g_fam l) _
```

For the `simrec` case, build the PolyBound as an
`ofComp` of an atomic-ER PolyBound for
`kSimSzudzikUnpackAt` (built recursively from its
definition; or use a single `ofComp` chain mirroring
its structure) plus per-branch PolyBounds.

```lean
  | _, .simrec (a := a) (k := k) i h_fam g_fam, h => by
      have hh : ∀ j, (h_fam j).level ≤ 0 := fun j => by
        unfold KMor1.level at h
        have hsup : Finset.univ.sup
            (fun l => (h_fam l).level) ≤ 0 := by
          have := le_trans (le_max_left _ _)
            (Nat.le_of_succ_le_succ h)
          exact this
        exact le_trans
          (Finset.le_sup
            (f := fun l => (h_fam l).level)
            (Finset.mem_univ j))
          hsup
      have hg : ∀ j, (g_fam j).level ≤ 0 := fun j => by
        unfold KMor1.level at h
        have hsup : Finset.univ.sup
            (fun l => (g_fam l).level) ≤ 0 := by
          have := le_trans (le_max_right _ _)
            (Nat.le_of_succ_le_succ h)
          exact this
        exact le_trans
          (Finset.le_sup
            (f := fun l => (g_fam l).level)
            (Finset.mem_univ j))
          hsup
      have hh_one : ∀ j, (h_fam j).level ≤ 1 := fun j =>
        Nat.le_succ_of_le (hh j)
      have hg_one : ∀ j, (g_fam j).level ≤ 1 := fun j =>
        Nat.le_succ_of_le (hg j)
      -- Unfold kToER on the simrec to expose the
      -- comp-of-branches structure.
      change ERMor1.PolyBound
        (ERMor1.comp (kSimSzudzikUnpackAt a i.val)
          (fun j =>
            if h_eq : j.val = 0 then
              ERMor1.boundedRec
                (kSimPackedBase
                  (fun l => kToER (h_fam l)
                    (Nat.le_succ_of_le (hh_one l))))
                (kSimPackedStep
                  (fun l => kToER (g_fam l)
                    (Nat.le_succ_of_le (hg_one l))))
                (kSimTowerBound
                  (fun l => kToER (h_fam l)
                    (Nat.le_succ_of_le (hh_one l)))
                  (fun l => kToER (g_fam l)
                    (Nat.le_succ_of_le (hg_one l))))
            else ERMor1.proj (k := a + 1)
              ⟨j.val, by have := j.isLt; omega⟩))
      apply ERMor1.PolyBound.ofComp
      · -- PolyBound for kSimSzudzikUnpackAt _ _.
        -- This is an atomic ER term; build via the
        -- structural unfold of kSimSzudzikUnpackAt.
        sorry  -- D.2.5.a fills this
      · -- PolyBound for each branch.
        intro j
        by_cases h_eq : j.val = 0
        · -- recur branch: boundedRec wrapping
          simp only [h_eq, dite_true]
          apply ERMor1.PolyBound.ofBoundedRec
          · -- PolyBound for kSimPackedBase h_ER
            apply kSimPackedBase_polyBound
            intro l
            exact kToER_polyBound_of_level_one
              (h_fam l) (hh_one l)
          · -- PolyBound for kSimPackedStep g_ER
            apply kSimPackedStep_polyBound
            intro l
            exact kToER_polyBound_of_level_one
              (g_fam l) (hg_one l)
          · -- PolyBound for kSimTowerBound h_ER g_ER
            sorry  -- D.2.5.b fills this
        · -- proj branch
          simp only [h_eq, dite_false]
          exact ERMor1.PolyBound.ofProj _
```

The two sub-`sorry`s are:

- **D.2.5.a**: PolyBound for `kSimSzudzikUnpackAt a i`.
  This is an atomic-ER term defined by structural recursion
  on `i`; build the PolyBound similarly via structural
  recursion on `i`.  Or: define it as a `PolyBound`
  fact about a specific atomic-ER shape and apply at
  the call site.  Estimated ~30-50 lines.
- **D.2.5.b**: PolyBound for `kSimTowerBound h_ER g_ER`.
  `kSimTowerBound = iterAutoBoundExpr a stepTH baseTH`,
  which is a comp of `towerER (d+1)` with an `addN` /
  `natN` / `sumCtxER` block — all ER atoms.  Build the
  PolyBound via `ofComp` on `iterAutoBoundExpr`'s
  unfolded shape.  Estimated ~30-50 lines.

- [ ] **Step D.2.6: Fill the D.2.5.a `sorry`
  (`kSimSzudzikUnpackAt` PolyBound)**

`kSimSzudzikUnpackAt` is defined recursively in
`GebLean/Utilities/KSimSzudzikSimrec.lean:122` as a
`comp` of `natUnpairFst` / `natUnpairSnd` /
`kSimSzudzikUnpackAt` (recursive case).  Build the
PolyBound by structural recursion on `i`:

```lean
        -- Helper: PolyBound for kSimSzudzikUnpackAt at any i.
        suffices h : ERMor1.PolyBound
            (kSimSzudzikUnpackAt a i.val) by exact h
        clear h_eq j
        induction i.val with
        | zero =>
            -- Base case: unpackAt at index 0 is a
            -- comp of natUnpairFst with proj 0.
            unfold kSimSzudzikUnpackAt
            apply ERMor1.PolyBound.ofComp
            · exact ERMor1.PolyBound.ofNatUnpairFst
            · intro _
              exact ERMor1.PolyBound.ofProj _
        | succ n ih =>
            -- Recursive case: unpackAt at index (n+1) is
            -- a comp of (unpackAt at n) with natUnpairSnd
            -- + proj.
            unfold kSimSzudzikUnpackAt
            apply ERMor1.PolyBound.ofComp
            · exact ih
            · intro l
              fin_cases l
              · apply ERMor1.PolyBound.ofComp
                · exact ERMor1.PolyBound.ofNatUnpairSnd
                · intro _
                  exact ERMor1.PolyBound.ofProj _
```

The exact `kSimSzudzikUnpackAt` recursive shape may
differ; verify via the file's contents (around line 122).
The above is a sketch; the implementer adjusts to match
the actual definition.

The PolyBound constructors `ofNatUnpairFst`,
`ofNatUnpairSnd` may not exist by those names — if not,
build them inline as `ofComp` over their
sub-expressions (since `natUnpairFst` is itself an ER
term defined by structural recursion).

If the recursive build for `kSimSzudzikUnpackAt`
turns out to be more involved than ~50 lines, factor
into a separate `private theorem
kSimSzudzikUnpackAt_polyBound` adjacent to the
current location.

- [ ] **Step D.2.7: Fill the D.2.5.b `sorry`
  (`kSimTowerBound` PolyBound)**

`kSimTowerBound h g = iterAutoBoundExpr a stepTH baseTH`
unfolds to `comp (towerER (d+1)) [...]`.  Build the
PolyBound by `ofComp` on this shape:

```lean
            unfold kSimTowerBound ERMor1.iterAutoBoundExpr
            apply ERMor1.PolyBound.ofComp
            · -- PolyBound for towerER (d + 1)
              sorry  -- D.2.7.a (or use existing
                      -- towerER_polyBound if landed)
            · intro _
              -- PolyBound for inner addN/natN/sumCtxER block
              sorry  -- D.2.7.b: comp of ER atoms
```

If `kSimTowerBound`'s PolyBound is too involved to build
inline, factor into a separate
`private theorem kSimTowerBound_polyBound` helper
(taking `pb_h, pb_g` as inputs).  Estimated ~30-50 lines.

The `ERMor1.PolyBound.ofTowerER`, `ofAddN`, `ofNatN`,
`ofSumCtxER` constructors may need to be added to
`LawvereERPolynomialBound.lean` if they don't already
exist.  Check via `grep` first.

- [ ] **Step D.2.8: Run `lake build` + `lake test`**

Run: `lake build && lake test`
Expected: PASS, no warnings, all 1561+ tests pass.

- [ ] **Step D.2.9: Commit**

```bash
git add GebLean/LawvereKSimPolynomialBound.lean \
        GebLean/LawvereERPolynomialBound.lean
git commit -m "$(cat <<'EOF'
kToER_polyBound_of_level_one (Task 17c D.2)

Adds public def KMor1.kToER_polyBound_of_level_one:
recursive PolyBound builder for level-≤-1 K^sim
translations.  Used by Phase IV-B Task D.5 to feed
kSimPackedBase_polyBound and kSimPackedStep_polyBound
with per-l PolyBounds for the headline theorem
kSimTowerBound_dominates_inline.

Atomic / comp / raise cases are direct applications of
the per-constructor builders.  The simrec case unfolds
kToER's wrapping (comp of kSimSzudzikUnpackAt with
boundedRec(kSimPackedBase, kSimPackedStep,
kSimTowerBound)) and applies ofBoundedRec.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

If new per-constructor PolyBound builders had to be
added to `LawvereERPolynomialBound.lean` (e.g.
`ofNatUnpairFst`, `ofTowerER`), mention them in the
commit message body.

---

## Task D.3.2: chain-closing log-vs-tH lemma

**Files:**

- Modify: `GebLean/LawvereKSimPolynomialBound.lean`
  (insert after `kToER_polyBound_of_level_one`).

**Goal:** prove

```text
Nat.log 2 (D + 1) ≤ 3 · stepTH + small_const
```

where `D` denotes the iterated-step's `to_iter_step_form`
exponent
`pb_packed_step.degree + pb_packed_step.coefficient +
pb_packed_step.constant + 2`,
`stepTH` denotes `(kSimPackedStep g_ER).towerHeight`, and
`small_const` is project-internal accounting absorbing
the per-comp `+1` of `tH` plus the `+2` shift in the
`to_iter_step_form`.

This lemma is the level-2 analog of A.5.2.2's
`stepTH_baseTH_dominates_arg` (line ~1544+ in this file).
It feeds the final `tower_mono_right` step at D.5.

The proof routes through:

1. The structural formula for `kSimPackedStep_polyBound`'s
   fields: `degree = E = (D_max + 5) · 4^(k+1)`,
   `coefficient = 3^E`, `constant = 0`.
2. `D_max =
   sup_l ((pb_g l).degree + (pb_g l).coefficient +
   (pb_g l).constant + 2)`, where `pb_g l` is the
   per-l PolyBound from `kToER_polyBound_of_level_one`
   on the K^sim child.
3. By `KMor1.linearBoundLog_le_towerHeight` (Step 2,
   the L.* deliverable),
   `Nat.log 2 ((linearBound g_l).1 + (linearBound g_l).2 +
   1) ≤ 3 · tH(kToER g_l) + 1`.
4. Connect `pb_g l`'s fields to `linearBound g_l` via
   `kToER_polyBound_of_level_one`'s structural definition
   (or via a degree-equality lemma the implementer adds
   if needed).
5. Aggregate over `l` and through `kSimPackedStep_polyBound`'s
   `(D_max + 5) · 4^(k+1)` formula.

The exact `small_const` value is determined by the chain;
target ~10-50.

- [ ] **Step D.3.2.1: State the lemma**

```lean
/-- Chain-closing log-vs-tH inequality at the packed
step's PolyBound, level-2 analog of
`stepTH_baseTH_dominates_arg` (A.5.2.2).  The `D` here
is the single-power exponent fed into
`to_iter_step_form` by the polynomial-iter chain. -/
private theorem linearBoundLog_packedStep_le_towerHeight
    {a k : ℕ}
    (h_fam : Fin (k + 1) → KMor1 a)
    (g_fam : Fin (k + 1) → KMor1 (a + 1 + (k + 1)))
    (h_h : ∀ l, (h_fam l).level ≤ 1)
    (h_g : ∀ l, (g_fam l).level ≤ 1) :
    let h_ER : Fin (k + 1) → ERMor1 a :=
      fun l => kToER (h_fam l) (Nat.le_succ_of_le (h_h l))
    let g_ER : Fin (k + 1) → ERMor1 (a + 1 + (k + 1)) :=
      fun l => kToER (g_fam l) (Nat.le_succ_of_le (h_g l))
    let pb_h := fun l =>
      KMor1.kToER_polyBound_of_level_one (h_fam l) (h_h l)
    let pb_g := fun l =>
      KMor1.kToER_polyBound_of_level_one (g_fam l) (h_g l)
    let pb_packed_step :=
      kSimPackedStep_polyBound g_ER pb_g
    let D : ℕ :=
      pb_packed_step.degree + pb_packed_step.coefficient
        + pb_packed_step.constant + 2
    Nat.log 2 (D + 1) ≤
      3 * (kSimPackedStep g_ER).towerHeight +
        small_const := _
```

The `small_const` needs to be pinned numerically; use
the comp-case algebra to derive the smallest constant
making the chain close.  The implementer may compute it
via numerical experimentation (`#eval` on the `addK`
witness) or by tracing through the proof.

If a closed-form `small_const` proves elusive, the
implementer is empowered to use `+ small_const` as an
implicit `∃`-bound (i.e., `∃ c, Nat.log 2 (D + 1) ≤
3 · stepTH + c`) and let the headline theorem at D.5
unpack the existential.  Either form satisfies the
chain.

- [ ] **Step D.3.2.2: Prove the lemma**

The proof outline:

1. Compute `pb_packed_step.degree = E = (D_max + 5)
   · 4^(k+1)`, `pb_packed_step.coefficient = 3^E`,
   `pb_packed_step.constant = 0` (from
   `kSimPackedStep_polyBound`'s definition).
2. So `D = E + 3^E + 0 + 2 = E + 3^E + 2`.
3. `Nat.log 2 (D + 1) = Nat.log 2 (E + 3^E + 3)
   ≤ Nat.log 2 (3^E + 3 · 3^E) + 1
   = Nat.log 2 (4 · 3^E) + 1
   ≤ Nat.log 2 (3^E) + 3
   = E · Nat.log 2 3 + 3
   ≤ 2 · E + 3` (since `Nat.log 2 3 ≤ 2`).
4. `E = (D_max + 5) · 4^(k+1)`.  By
   `kSimPackedStep_towerHeight_ge_succ_k`,
   `(kSimPackedStep g_ER).tH ≥ k + 2`, so
   `4^(k+1) ≤ 4^((kSimPackedStep g_ER).tH - 1)`.
5. By `KMor1.linearBoundLog_le_towerHeight`,
   `D_max ≤ (kSimPackedStep g_ER).tH + small_const_2`.
6. Combine:
   `2 · E + 3 ≤ 2 · ((kSimPackedStep g_ER).tH + 5) ·
   4^((kSimPackedStep g_ER).tH - 1) + 3`,
   which is bounded by `3 · stepTH + small_const`
   for sufficiently large `small_const`.

The exact algebra is delicate; the implementer may need
to add small `Nat.log 2`-arithmetic helpers similar to
the L.1 work (e.g. `Nat.log 2 (a + b) ≤ ...` plus
`Nat.log 2 (3^E) ≤ 2 · E`).  Cap the helper count at
~3; if more are needed, escalate.

```lean
private theorem linearBoundLog_packedStep_le_towerHeight
    {a k : ℕ}
    (h_fam : Fin (k + 1) → KMor1 a)
    (g_fam : Fin (k + 1) → KMor1 (a + 1 + (k + 1)))
    (h_h : ∀ l, (h_fam l).level ≤ 1)
    (h_g : ∀ l, (g_fam l).level ≤ 1) :
    -- (signature as above) := by
    sorry  -- transient; filled below
```

The full proof body should be assembled inline.  Given
the complexity, the implementer is encouraged to:

(a) Write the proof bottom-up, filling sub-`have`s for
    each algebraic step.
(b) Use `nlinarith` and `omega` liberally for arithmetic
    stages.
(c) Use `mcp__lean-lsp__lean_goal` and `lean_multi_attempt`
    to inspect intermediate states.

If by step (5) the proof has not closed, escalate as
DONE_WITH_CONCERNS or BLOCKED with the goal state and
the remaining gap.

- [ ] **Step D.3.2.3: Run `lake build` + `lake test`**

Run: `lake build && lake test`
Expected: PASS, no warnings.

- [ ] **Step D.3.2.4: Commit**

```bash
git add GebLean/LawvereKSimPolynomialBound.lean
git commit -m "$(cat <<'EOF'
linearBoundLog_packedStep_le_towerHeight (Task 17c D.3.2)

Adds the chain-closing log-vs-tH inequality at the packed
step's PolyBound:
  Nat.log 2 (D + 1) ≤ 3 · stepTH + small_const
where D = pb_packed_step.degree + pb_packed_step.coefficient
+ pb_packed_step.constant + 2 is the iterated-step exponent
fed into to_iter_step_form, and stepTH = (kSimPackedStep
g_ER).towerHeight.

Level-2 analog of A.5.2.2's stepTH_baseTH_dominates_arg.
Consumes KMor1.linearBoundLog_le_towerHeight (Step 2 / L.3-5
deliverable) per-l on the K^sim children.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task D.5: headline theorem assembly (D.1 + D.3.1 + D.4 + D.5 combined)

**Files:**

- Modify: `GebLean/LawvereKSimPolynomialBound.lean`
  (insert after `linearBoundLog_packedStep_le_towerHeight`).

**Goal:** add the public theorem `kSimTowerBound_dominates_inline`
with full proof (no `sorry`, no `admit`).  Mirrors the
level-1 template `kSimTowerBound_dominates_level_one`
(line 2578) but starts from polynomial bounds.

**Note on D.1**: the original completion plan had D.1
"stub the theorem with sorry, do not commit yet".  Per
project policy (no `sorry` in committed state), this
step is folded into D.5: the headline theorem lands
fully proven in a single commit.

**Note on D.3.1**: building the packed PolyBounds is
one-line plumbing inside the headline proof — no
separate task.

**Note on D.4**: applying `to_iter_step_form` and
`Nat.polynomial_iter_tower_bound` is part of the chain
calc within the headline proof — no separate task.

- [ ] **Step D.5.1: Add the headline theorem with the
  full chain calc**

```lean
/-- Level-2 simrec dominance: the iterated packed value
of `kSimPackedStep` over `kSimPackedBase` is dominated
by `kSimTowerBound`'s closed-form tower at every
iteration counter and parameter context, when both base
and step families consist of level-≤-1 K^sim terms.
Used by `kToER_interp` at level ≤ 2 (kToER plan
Task 14).

Compared to `kSimTowerBound_dominates_level_one`
(Task 17b), the level-2 case routes through polynomial-
iteration bounds via `kSimPackedStep_polyBound`,
`to_iter_step_form`, and
`Nat.polynomial_iter_tower_bound`, in line with
Tourlakis 2018 §0.1.0.27 (3): K^sim_2 functions are
polynomially bounded, not linearly. -/
theorem kSimTowerBound_dominates_inline {a k : ℕ}
    (h_fam : Fin (k + 1) → KMor1 a)
    (g_fam : Fin (k + 1) → KMor1 (a + 1 + (k + 1)))
    (h_h : ∀ l, (h_fam l).level ≤ 1)
    (h_g : ∀ l, (g_fam l).level ≤ 1)
    (j : ℕ) (params : Fin a → ℕ) :
    Nat.rec
      ((kSimPackedBase
        (fun l => kToER (h_fam l)
          (Nat.le_succ_of_le (h_h l)))).interp params)
      (fun i prev =>
        (kSimPackedStep
          (fun l => kToER (g_fam l)
            (Nat.le_succ_of_le (h_g l)))).interp
        (Fin.cons i (Fin.cons prev params)))
      j ≤
      (kSimTowerBound
        (fun l => kToER (h_fam l)
          (Nat.le_succ_of_le (h_h l)))
        (fun l => kToER (g_fam l)
          (Nat.le_succ_of_le (h_g l)))).interp
        (Fin.cons j params) := by
  -- Set abbreviations.
  set h_ER : Fin (k + 1) → ERMor1 a :=
    fun l => kToER (h_fam l) (Nat.le_succ_of_le (h_h l))
    with h_ER_def
  set g_ER : Fin (k + 1) → ERMor1 (a + 1 + (k + 1)) :=
    fun l => kToER (g_fam l) (Nat.le_succ_of_le (h_g l))
    with g_ER_def
  -- D.3.1: build per-l PolyBounds and lift to packed.
  have pb_h : (l : Fin (k + 1)) → ERMor1.PolyBound (h_ER l) :=
    fun l => KMor1.kToER_polyBound_of_level_one
      (h_fam l) (h_h l)
  have pb_g : (l : Fin (k + 1)) → ERMor1.PolyBound (g_ER l) :=
    fun l => KMor1.kToER_polyBound_of_level_one
      (g_fam l) (h_g l)
  let pb_packed_base := kSimPackedBase_polyBound h_ER pb_h
  let pb_packed_step := kSimPackedStep_polyBound g_ER pb_g
  -- D.4: apply to_iter_step_form to get single-power bound
  -- on packed step.
  set D_step : ℕ :=
    pb_packed_step.degree + pb_packed_step.coefficient
      + pb_packed_step.constant + 2
    with hD_step_def
  -- The iterated trace: define iter step.
  -- packed step = fun (i, prev, params) => ...
  -- pretty-printed as: step prev (max j sumCtx) where
  -- sumCtx is the parameter sum.
  set sumCtx :=
    (Finset.univ : Finset (Fin (a + 1))).sum
      (Fin.cons j params)
    with hsumCtx_def
  -- Apply Nat.polynomial_iter_tower_bound.
  -- Hypothesis h_step: every step iteration ≤ (max v x + 1)^D_step.
  -- This comes from to_iter_step_form on pb_packed_step.
  have h_step_form :=
    ERMor1.PolyBound.to_iter_step_form
      (kSimPackedStep g_ER) pb_packed_step params
  -- h_step_form gives: ∀ v x, (kSimPackedStep g_ER).interp
  -- (Fin.cons x (Fin.cons v params)) ≤ (max v (max x sp) + 2)^D_step
  -- where sp = sup params.
  -- Adapt to the iter-shape: define step v x := ...
  -- Apply polynomial_iter_tower_bound.
  -- (Detailed step-by-step proof goes here.)
  sorry  -- to be filled in
```

This is the headline theorem's skeleton.  The detailed
chain calc is filled below.

- [ ] **Step D.5.2: Fill the chain calc**

The full proof body assembles:

1. `pb_packed_step.bounds` → `(packed step).interp ≤
   coefficient · (maxCtx + 1)^degree + constant`.
2. `to_iter_step_form` → single-power form
   `(packed step).interp (Fin.cons x (Fin.cons v params))
   ≤ (max v (max x sp) + 2) ^ D_step`.
3. Adapt `Nat.polynomial_iter_tower_bound`:
   `step v x := (packed step).interp (Fin.cons x
   (Fin.cons v params))` and `v_0 x := pb_packed_base.bounds`
   evaluation.  But `polynomial_iter_tower_bound`
   requires a LINEAR base bound `v_0 x ≤ m * x + m`.
   The `pb_packed_base` is polynomial (degree may exceed
   1).  Adapt by:
   - Bound
     `pb_packed_base.interp params ≤
     (maxCtx params + 2) ^ D_base`.
   - Use `pow_le_tower_two_with_shift` to lift to
     `tower 2 (linear)`.
   - Treat the iteration's effective base as the
     `tower 2`-bound, i.e., generalize
     `polynomial_iter_tower_bound` to allow an initial
     `tower 2` base by chaining.
   - OR: add a small adapter
     `Nat.polynomial_iter_tower_bound_with_pow_base` that
     accepts `v_0 x ≤ (m * x + m) ^ D_base` and produces
     the same `tower 2 (linear in (j, x, log D, m, D_base))`
     bound.
4. Apply the existing `tower_two_le_tower_three_linear`,
   `tower_mono_left`, `tower_mono_right` chain (mirroring
   level-1 line 2655+).
5. Use `linearBoundLog_packedStep_le_towerHeight` (D.3.2)
   in the final `tower_mono_right` to absorb the
   `Nat.log 2 D_step` term into `stepTH + 2*baseTH +
   small`.

```lean
  -- (Continuing from D.5.1)
  -- Decoupling the two-stage chain via pow_le_tower_two_with_shift.
  -- Step 3 of the chain: convert pb_packed_base's polynomial
  -- bound to a tower-2 bound.
  have h_base_form :
      pb_packed_base.interp params ≤
      (maxCtx params + 2) ^
        (pb_packed_base.degree + pb_packed_base.coefficient
          + pb_packed_base.constant + 2) := by
    -- pb_packed_base.bounds + folding c · y^d + k into y^(d+c+k+2).
    sorry  -- D.5.2.a fills this
  -- Use pow_le_tower_two_with_shift.
  -- pow_le_tower_two_with_shift takes parameters CC, S, KK, E
  -- and gives (CC * S + KK + 2) ^ E ≤ tower 2 (CC * S + KK + 1
  --   + Nat.log 2 E + 2).
  -- Adapt: set CC = 1, S = maxCtx params + 1, KK = 1,
  -- E = pb_packed_base.degree + ... + 2.  Then
  -- (1 * (maxCtx + 1) + 1 + 2) ^ E = (maxCtx + 4) ^ E,
  -- which dominates (maxCtx + 2) ^ E.
  sorry  -- D.5.2.b fills the rest of the chain
```

The two further `sorry`s are:

- **D.5.2.a**: convert `pb_packed_base.bounds` (which
  gives `c · y^d + k`) to the single-power form
  `y^(d+c+k+2)`.  Same shape as `to_iter_step_form`'s
  conversion; the implementer may apply
  `to_iter_step_form` directly to `pb_packed_base` (via
  appropriate arity threading) or replicate its
  algebra inline.
- **D.5.2.b**: fill the rest of the chain mirroring the
  level-1 template at lines 2614-2703.  Apply
  `polynomial_iter_tower_bound` (or its with-pow-base
  adapter), then `tower_two_le_tower_three_linear`,
  then `tower_mono_left`/`right`.

Each `sorry` is filled in its own sub-step.

- [ ] **Step D.5.3: Fill D.5.2.a (`pb_packed_base` to
  single-power form)**

Apply `ERMor1.PolyBound.to_iter_step_form` to
`pb_packed_base` — but `to_iter_step_form` expects an
`ERMor1 (k + 2)` shape (with `x` and `v` slots).
`kSimPackedBase h_ER : ERMor1 (a + 1)` has only one
slot.  So `to_iter_step_form` doesn't directly apply.

Alternative: write a small adapter in
`LawvereERPolynomialBound.lean` that converts
`pb : PolyBound f` for `f : ERMor1 (k + 1)` (single
input slot) to a single-power form
`f.interp ctx ≤ (maxCtx ctx + 2) ^ (pb.degree +
pb.coefficient + pb.constant + 2)`.  This is a one-input
specialization of `to_iter_step_form`.

```lean
theorem ERMor1.PolyBound.to_iter_step_form_one_input
    {k : ℕ} (f : ERMor1 (k + 1)) (pb : PolyBound f)
    (ctx : Fin (k + 1) → ℕ) :
    f.interp ctx ≤
      (maxCtx ctx + 2) ^
        (pb.degree + pb.coefficient + pb.constant + 2) := by
  -- Mirror to_iter_step_form's proof; replace
  -- (Fin.cons x (Fin.cons v params)) with ctx directly.
  have h_applied := pb.bounds ctx
  set y : ℕ := maxCtx ctx + 2 with hy
  set D : ℕ := pb.degree + pb.coefficient + pb.constant + 2
    with hD
  -- (rest of the proof: same algebra as to_iter_step_form)
  sorry
```

If adding this helper to `LawvereERPolynomialBound.lean`
proves more involved than ~50 lines, escalate; otherwise,
use it directly to fill D.5.2.a.

- [ ] **Step D.5.4: Fill D.5.2.b (chain assembly)**

Mirror the level-1 chain at lines 2614-2703.  The main
adaptations:

- `h_pack_le` (level 1 used `KMor1.simrecVec_seqPack_le_pow`)
  is replaced by the polynomial-iter chain via
  `polynomial_iter_tower_bound`.
- The final `tower_mono_right` step's argument-bound uses
  the new `linearBoundLog_packedStep_le_towerHeight` (D.3.2)
  instead of A.5.2.2's `stepTH_baseTH_dominates_arg`.

The detailed code is ~80-150 lines.  Use the level-1
template at line 2578-2703 as a structural reference.

If the chain doesn't close because the
`polynomial_iter_tower_bound`'s `h_base` hypothesis
requires a LINEAR base bound (`v_0 x ≤ m * x + m`) but
the packed base has a polynomial bound, the implementer
may:

(a) Add a `Nat.polynomial_iter_tower_bound_with_pow_base`
    variant in Utilities (~50 lines), which accepts a
    polynomial base bound and produces the analogous
    `tower 2 (linear)` conclusion with the polynomial
    degree absorbed into the linear coefficient via
    `pow_le_tower_two_with_shift`.
(b) Generalize the chain by treating `tower 2 (linear)
    base` as the effective initial state and chaining
    through `polynomial_iter_tower_bound` with `v_0 x =
    tower 2 (linear)`.

Option (a) is cleaner; option (b) requires more
ad-hoc reasoning.

- [ ] **Step D.5.5: Run `lake build` + `lake test`**

Run: `lake build && lake test`
Expected: PASS, no warnings, no `sorry`/`admit`.

- [ ] **Step D.5.6: Commit**

```bash
git add GebLean/LawvereKSimPolynomialBound.lean \
        GebLean/LawvereERPolynomialBound.lean \
        GebLean/Utilities/ComputationalComplexity.lean
git commit -m "$(cat <<'EOF'
kSimTowerBound_dominates_inline (Task 17c D.1, D.3.1, D.4, D.5)

Phase IV-B headline theorem: level-2 simrec dominance via
the polynomial-iteration chain.  Public theorem; consumed
by Task 14 of the kToER plan.

Chain assembly:
- D.3.1 (plumbing): kSimPackedBase_polyBound and
  kSimPackedStep_polyBound applied to the per-l PolyBounds
  from kToER_polyBound_of_level_one (D.2).
- D.4: to_iter_step_form converts pb_packed_step to single-
  power form; polynomial_iter_tower_bound bounds the
  j-iterated trace by tower 2 (linear).
- D.5: tower_two_le_tower_three_linear bumps to tower 3;
  tower_mono_left lifts to tower (stepTH + 1) via
  kSimPackedStep_towerHeight_ge_succ_k; tower_mono_right
  absorbs the linear argument into kSimTowerBound's
  closed-form expression via the D.3.2 log-vs-tH lemma.

Mirrors the level-1 template kSimTowerBound_dominates_level_one
(Task 17b) but routes through polynomial bounds rather than
linear, in line with Tourlakis 2018 §0.1.0.27 (3): K^sim_2
functions are polynomially bounded, not linearly.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

If new helpers were added (e.g.
`to_iter_step_form_one_input`,
`polynomial_iter_tower_bound_with_pow_base`), mention
them in the commit message body.

---

## Task D.6: Final verification

- [ ] **Step D.6.1: Confirm the headline theorem is
  public**

```bash
grep -n "theorem kSimTowerBound_dominates_inline" \
  GebLean/LawvereKSimPolynomialBound.lean
```

Expected: one match, NOT prefixed with `private`.

- [ ] **Step D.6.2: Confirm no extraneous sorries**

```bash
grep -rn "sorry\|admit" \
  GebLean/LawvereKSimPolynomialBound.lean \
  GebLean/LawvereERPolynomialBound.lean \
  GebLean/Utilities/ComputationalComplexity.lean
```

Expected: zero matches.

- [ ] **Step D.6.3: Run full build + test**

```bash
lake build && lake test
```

Expected: PASS, no warnings, all 1561+ tests pass.

- [ ] **Step D.6.4: No commit on this verification step**

---

## Estimated effort

- D.2: 150-300 lines (recursive PolyBound builder).
- D.3.2: 80-150 lines (log-vs-tH lemma + possibly small
  helpers).
- D.5: 150-300 lines (headline theorem assembly,
  potentially with `to_iter_step_form_one_input` and/or
  `polynomial_iter_tower_bound_with_pow_base` adapters).
- D.6: read-only.

Total: ~400-750 lines added to `LawvereKSimPolynomialBound.lean`,
plus 0-150 lines in adjacent files for adapter helpers.

If at any task the implementation exceeds the
upper-bound estimate by more than 50% (e.g. D.2 grows
beyond 450 lines, D.5 beyond 450 lines), escalate as
DONE_WITH_CONCERNS or BLOCKED — the chain may need
factoring into more sub-helpers, or the level-1
template may not transfer cleanly.

---

## Self-review checklist

**Spec coverage:**

- ✓ D.2: per-child PolyBound builder (Task D.2).
- ✓ D.3.1: packed PolyBound plumbing (folded into D.5).
- ✓ D.3.2: chain-closing log-vs-tH lemma (Task D.3.2).
- ✓ D.4: polynomial-iter application (folded into D.5).
- ✓ D.5: tower-arithmetic closeout (Task D.5).
- ✓ D.1: headline theorem (folded into D.5; no separate
  stub commit per project's no-sorry policy).

**Per-task build/test checkpoints:** D.2 commits,
D.3.2 commits, D.5 commits, D.6 verifies.

**Per-task commit subjects ending in `(Task 17c D.X)`:**
each task has a commit subject.

**Critical-path dependencies on landed lemmas:**

- `kSimPackedBase_polyBound` / `kSimPackedStep_polyBound`
  (Poly Task 16, landed) — used in D.5.
- `to_iter_step_form` (Poly Task 10, landed) — used in
  D.5 (or its one-input variant added in D.5.2.a).
- `Nat.polynomial_iter_tower_bound` (Poly Task 5,
  landed) — used in D.5.
- `Nat.tower_two_le_tower_three_linear` /
  `Nat.pow_le_tower_two_with_shift` /
  `tower_mono_left/right` (Utilities, landed) — used
  in D.5.
- `kSimPackedStep_towerHeight_ge_succ_k` (this file,
  private, landed) — used in D.5 to discharge `tower_mono_left`'s
  hypothesis `stepTH + 1 ≥ 3`.
- `KMor1.linearBoundLog_le_towerHeight` (this file,
  public, Step 2 / L.3-5 deliverable, landed) — used
  in D.3.2.

**Placeholder scan:** the plan contains transient
`sorry` placeholders inside Steps D.2.5 / D.2.6 / D.2.7
/ D.3.2.2 / D.5.1 / D.5.2 / D.5.3 / D.5.4, all
explicitly labeled as transient working-tree states
resolved by their own subsequent sub-steps before the
respective task's final commit.  No `sorry` appears in
any committed state.

**Type consistency:** all signatures use consistent
`(h : f.level ≤ 1)` plus `Nat.le_succ_of_le h` to lift
to `level ≤ 2`.  All `pb_h` / `pb_g` are functions
producing per-l PolyBounds via
`kToER_polyBound_of_level_one`.  All `pb_packed_*` are
applied via `kSimPackedBase_polyBound` /
`kSimPackedStep_polyBound`.

---

## Out-of-scope deferred work

After this plan completes, Phase IV-B is fully closed.
The next phase is the kToER theorem layer (per the high-
level outline):

- **kToER Task 14 — `kToER_interp`**: the headline
  interpretation-preservation theorem, consumes
  `kSimTowerBound_dominates_inline`.
- **kToER Task 15 — `kToERN_interp`**: pointwise lift.
- **kToER Task 16 — `kToERFunctor` obj/map fields**.
- **kToER Task 17 — functor laws (`map_id`, `map_comp`)**.
- **kToER Tasks 18-22**: tests, re-export, final
  verification.

These are separate plans, sequenced after this one.
