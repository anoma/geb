# Phase IV-B Task 17c — auxiliary structural lemma plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> `superpowers:subagent-driven-development` (recommended) or
> `superpowers:executing-plans` to implement this plan
> task-by-task.  Steps use checkbox (`- [ ]`) syntax for
> tracking.

**Goal:** establish the structural lower bound
`(kToER (KMor1.simrec h_fam g_fam i)).towerHeight ≥
max(max_l (kToER (h_fam l)).towerHeight,
    max_l (kToER (g_fam l)).towerHeight) + small_const`,
the auxiliary lemma required by the main inequality
`KMor1.linearBoundLog_le_towerHeight :
Nat.log 2 (lb stuff) ≤ 3 · (kToER f).towerHeight + 1`
of Phase IV-B (Task 17c).

**Architecture:** four-layer chain.  Layer 1 pins
`(ERMor1.iterAutoBoundExpr k d lh).towerHeight` as a closed
function of `d`.  Layer 2 pins
`(ERMor1.boundedRec base step bound).towerHeight` as a
function of the three inputs' `towerHeight`s.  Layer 3
combines layers 1+2 with the existing
`kSimPackedStep_towerHeight_ge_propagate` /
`kSimPackedBase_towerHeight_ge_propagate` to bound
`(kSimTowerBound h_ER g_ER).towerHeight ≥ max(max_l h_ER.tH,
max_l g_ER.tH) + small_const`.  Layer 4 lifts this through
the outer `comp (kSimSzudzikUnpackAt) ...` wrapping to bound
`(kToER simrec).towerHeight`.

**Tech stack:** Lean 4, mathlib, `lake build` / `lake test`.

**Convention:** every committed task ends in a clean
`lake build` plus `lake test`, with commit subject
`(Task 17c E.X)` (E = "auxiliary [E]xistential lower bound on
towerHeight").  Plans for the main lemma
(`KMor1.linearBoundLog_le_towerHeight`) and the chain-closing
work (Tasks D.2 onward) are separate from this plan.

---

## File structure

The plan touches three modules:

- **Modify** `GebLean/LawvereERBoundComputable.lean`:
  add `iterAutoBoundExpr_towerHeight_eq` and
  `iterAutoBoundExpr_towerHeight_ge_d` as `theorem`s near
  the existing `iterAutoBoundExpr` definition (currently at
  lines 410–456).
- **Modify** `GebLean/Utilities/ERArith.lean`: add
  `boundedRec_towerHeight_eq` and
  `boundedRec_towerHeight_ge_bound` as `theorem`s adjacent
  to `def ERMor1.boundedRec` (currently at lines 1782–1799).
- **Modify** `GebLean/LawvereKSimPolynomialBound.lean`:
  add `kSimTowerBound_towerHeight_ge_step` and
  `kToER_simrec_towerHeight_ge_max_child_tH` as `private
  theorem`s in the existing structural-lemmas section
  (after `kSimPackedStep_towerHeight_ge_propagate` at
  line 1507).

No new module files are created.  Each lemma has either a
`@[simp]` interp/towerHeight `_eq` form (closed-form
equality, useful for normalization) or a `_ge_*` form (the
inequality the main lemma needs).  Equalities are proved
first; inequalities are routine corollaries.

`ERMor1.towerHeight` recursion (from
`LawvereERBoundComputable.lean:34`):

```text
zero / succ / proj / sub : towerHeight = 0
comp f g  : towerHeight = f.tH + sup_i (g i).tH + 1
bsum f    : towerHeight = f.tH + 3
bprod f   : towerHeight = f.tH + 4
```

---

## Task E.1: Pin `iterAutoBoundExpr` towerHeight (closed form)

**Files:**

- Modify: `GebLean/LawvereERBoundComputable.lean`
  (insert after `theorem ERMor1.interp_iterAutoBoundExpr`,
  currently ending around line 456)

The `iterAutoBoundExpr k d lh` body (lines 410–423) is

```text
comp (towerER (d + 1))
  [comp addN
    [comp addN
      [natN(k+1, d+1+2*lh),
       comp addN [sumCtxER(k+1), sumCtxER(k+1)]],
     natN(k+1, 2)]]
```

By induction on `k`, `(towerER k).towerHeight = k`
(`towerER 0 = proj 0`, `towerHeight = 0`; succ case adds
one comp with atomic siblings, contributing `+1`).  The
inner block's towerHeight is a closed constant
`C_inner` independent of `d`, `lh`, `k` (composed of
`addN`, `natN`, `sumCtxER` — all pure ER atoms or fixed
finite `comp` chains).  `(comp f g).towerHeight = f.tH +
sup_i (g i).tH + 1`, so

```text
(iterAutoBoundExpr k d lh).towerHeight
  = (towerER (d+1)).tH + (inner block).tH + 1
  = (d + 1) + C_inner + 1
  = d + C_inner + 2.
```

The constant `C_inner` is a fixed natural number; the
plan does not pre-commit its value.  Task E.1 verifies the
shape `d + C_outer` with `C_outer = C_inner + 2` and
expresses it as a `simp` `_eq` lemma whose right-hand side
is `d + (atomic-block-towerHeight-thunk)` where the thunk
is just the value of
`(iterAutoBoundExpr 0 0 0).towerHeight`.

- [ ] **Step E.1.1: Compute the constant via `lean_run_code`**

Use the Lean MCP server to evaluate

```lean
#eval (ERMor1.iterAutoBoundExpr 0 0 0).towerHeight
```

Expected: a small positive natural (anticipated: 6).
Record the value as `C_outer` in this plan and in the
docstring of the lemma below.

- [ ] **Step E.1.2: State the `_eq` lemma**

Insert into `GebLean/LawvereERBoundComputable.lean` after
`theorem ERMor1.interp_iterAutoBoundExpr`:

```lean
/-- Closed-form towerHeight of `iterAutoBoundExpr`: the
outer `comp (towerER (d + 1))` contributes `d + 1` to the
tower height, the inner `addN/natN/sumCtxER` block
contributes a fixed structural constant, and the outer
`comp` itself contributes `+1`.  The total is `d + C` for
a closed constant `C`. -/
theorem ERMor1.iterAutoBoundExpr_towerHeight_eq
    (k d lh : ℕ) :
    (ERMor1.iterAutoBoundExpr k d lh).towerHeight =
      d + (ERMor1.iterAutoBoundExpr 0 0 0).towerHeight := by
  _
```

The right-hand side uses `(iterAutoBoundExpr 0 0 0).
towerHeight` directly rather than the numeric value `C`
so the lemma stays parametric in any future restructuring
of the inner block.  (The numeric value can be substituted
later via `decide` if/when needed.)

- [ ] **Step E.1.3: Prove the `_eq` lemma**

Replace the underscore with a structural unfold:

```lean
theorem ERMor1.iterAutoBoundExpr_towerHeight_eq
    (k d lh : ℕ) :
    (ERMor1.iterAutoBoundExpr k d lh).towerHeight =
      d + (ERMor1.iterAutoBoundExpr 0 0 0).towerHeight := by
  unfold ERMor1.iterAutoBoundExpr
  simp only [ERMor1.towerHeight]
  -- Helper: (towerER n).towerHeight = n.
  have htow : ∀ n, (ERMor1.towerER n).towerHeight = n := by
    intro n
    induction n with
    | zero => rfl
    | succ n' ih =>
        unfold ERMor1.towerER
        simp only [ERMor1.towerHeight]
        -- comp expER [towerER n', twoN 1]:
        -- expER, twoN are ER atoms (towerHeight 0); the
        -- inner sup picks (towerER n').towerHeight = n'
        -- by ih.  Outer comp adds +1.
        omega
  rw [htow (d + 1), htow 1]
  -- The inner block's towerHeight has lh, k, d as
  -- arguments only via natN constants — these are atomic.
  -- Hence both sides of the equation reduce to the same
  -- closed expression `d + C`.
  ring_nf
  -- Compute (iterAutoBoundExpr 0 0 0).towerHeight by
  -- re-unfolding once.
  show _ = d + _
  conv_rhs => rw [show
      (ERMor1.iterAutoBoundExpr 0 0 0).towerHeight =
        _ from rfl]
  -- Both reduce to `d + C_outer` symbolically; close with
  -- omega.
  omega
```

If `ring_nf` and `omega` cannot close the goal directly
because `natN` and `sumCtxER` definitions are not unfolded,
add their `towerHeight` reductions explicitly:

```lean
  have hnatN : ∀ k v,
      (ERMor1.natN k v).towerHeight =
        (ERMor1.natN 0 0).towerHeight := by
    -- natN k v = comp (iterated succ) zero — towerHeight
    -- depends only on iteration depth, which is `v`.
    sorry  -- placeholder; use lean_local_search to find
            -- the existing helper or compute by induction
```

If a closed-form helper for `natN.towerHeight` does not
exist yet, defer to a sub-task (E.1.3.a) that adds it.

- [ ] **Step E.1.4: Run `lake build`**

Run: `lake build`
Expected: PASS, no warnings.

- [ ] **Step E.1.5: Run `lake test`**

Run: `lake test`
Expected: PASS.

- [ ] **Step E.1.6: Commit**

```bash
git add GebLean/LawvereERBoundComputable.lean
git commit -m "$(cat <<'EOF'
Pin iterAutoBoundExpr towerHeight closed form (Task 17c E.1)

Adds ERMor1.iterAutoBoundExpr_towerHeight_eq stating that
(iterAutoBoundExpr k d lh).towerHeight = d + C for a closed
constant C.  Proof by structural unfold using the towerER
induction (towerER n).towerHeight = n.  Used by Task 17c E.3
(_ge_d corollary) and ultimately by the simrec auxiliary
lemma at Task 17c E.6.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task E.2: `iterAutoBoundExpr` towerHeight ≥ d corollary

**Files:**

- Modify: `GebLean/LawvereERBoundComputable.lean`
  (insert after `iterAutoBoundExpr_towerHeight_eq`)

- [ ] **Step E.2.1: State the lemma**

```lean
/-- Structural lower bound on `iterAutoBoundExpr`'s tower
height in terms of the `d` parameter alone.  The bound is
tight: it holds with equality up to the closed constant
`C = (iterAutoBoundExpr 0 0 0).towerHeight`. -/
theorem ERMor1.iterAutoBoundExpr_towerHeight_ge_d
    (k d lh : ℕ) :
    d ≤ (ERMor1.iterAutoBoundExpr k d lh).towerHeight := by
  _
```

- [ ] **Step E.2.2: Prove the lemma**

```lean
theorem ERMor1.iterAutoBoundExpr_towerHeight_ge_d
    (k d lh : ℕ) :
    d ≤ (ERMor1.iterAutoBoundExpr k d lh).towerHeight := by
  rw [ERMor1.iterAutoBoundExpr_towerHeight_eq]
  exact Nat.le_add_right d _
```

- [ ] **Step E.2.3: Run `lake build`**

Run: `lake build`
Expected: PASS, no warnings.

- [ ] **Step E.2.4: Run `lake test`**

Run: `lake test`
Expected: PASS.

- [ ] **Step E.2.5: Commit**

```bash
git add GebLean/LawvereERBoundComputable.lean
git commit -m "$(cat <<'EOF'
iterAutoBoundExpr towerHeight ≥ d corollary (Task 17c E.2)

Trivial corollary of iterAutoBoundExpr_towerHeight_eq from
E.1: dropping the closed constant C ≥ 0 gives d ≤ tH.  Used
by Task 17c E.5 to lift the bound on stepTH through
kSimTowerBound's iterAutoBoundExpr wrapping.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task E.3: `boundedRec` towerHeight closed form

**Files:**

- Modify: `GebLean/Utilities/ERArith.lean`
  (insert after `theorem ERMor1.interp_boundedRec_le_bound`,
  currently ending around line 1811)

Recall `ERMor1.boundedRec base step bound = comp minN
[betaAtN, bound]` where `betaAtN = comp beta [comp
natUnpairFst search, comp natUnpairSnd search, proj 0]` and
`search = boundedSearch (boundedRecRange bound)
(boundedRecPred base step)`.  The towerHeight involves
`base.tH`, `step.tH`, `bound.tH`, plus structural overheads
from `boundedSearch`, `boundedRecRange`, `boundedRecPred`,
`beta`, `minN`, `natUnpairFst`, `natUnpairSnd`.  The
overheads are closed constants once `base`/`step`/`bound`
are fixed.

The closed form has shape

```text
(boundedRec base step bound).towerHeight =
  max (search.tH) bound.tH + C_minN
```

where `search.tH = max (boundedRecRange bound).tH
(boundedRecPred base step).tH + C_search` with
`(boundedRecRange bound).tH` containing `bound.tH` as a
sub-expression and `(boundedRecPred base step).tH`
containing `base.tH` and `step.tH`.

The exact closed form does not need to be a single neat
expression; Task E.3 only requires a `_ge_*` form that
extracts each input's `towerHeight` as a lower bound.  We
state E.3 in its `_eq` form for diagnostic clarity, and
E.4 in `_ge_*` form for downstream use.

- [ ] **Step E.3.1: Compute the closed form via
  `lean_run_code` for a sample**

Use the Lean MCP server to evaluate, for atomic
`base`, `step`, `bound`:

```lean
#eval (ERMor1.boundedRec ERMor1.zero
  (ERMor1.proj ⟨0, by omega⟩) ERMor1.succ).towerHeight
```

Record the numeric output as `C_boundedRec_atomic` in this
plan.

Then compute the towerHeight when `bound` is replaced with
a non-trivial term, e.g.

```lean
#eval (ERMor1.boundedRec ERMor1.zero
  (ERMor1.proj ⟨0, by omega⟩)
  (ERMor1.comp ERMor1.succ
    (fun _ : Fin 1 => ERMor1.zeroN _))).towerHeight
```

Confirm the difference equals the difference in
`bound.towerHeight` (i.e., the relation is additive in
`bound.towerHeight`).

- [ ] **Step E.3.2: State the `_eq` lemma**

Insert after `interp_boundedRec_le_bound` in
`Utilities/ERArith.lean`:

```lean
/-- Closed-form towerHeight of `boundedRec`.  The structural
recursion on `comp minN [betaAtN, bound]` gives a sup over
`betaAtN.towerHeight` and `bound.towerHeight`, where
`betaAtN` further decomposes via `boundedSearch` over
`boundedRecRange bound` and `boundedRecPred base step`. -/
theorem ERMor1.boundedRec_towerHeight_eq {k : ℕ}
    (base : ERMor1 k) (step : ERMor1 (k + 2))
    (bound : ERMor1 (k + 1)) :
    (ERMor1.boundedRec base step bound).towerHeight =
      max
        (max
          ((ERMor1.boundedRecRange bound).towerHeight)
          ((ERMor1.boundedRecPred base step).towerHeight) +
            ERMor1.boundedSearch_towerHeight_offset +
            ERMor1.beta_minN_towerHeight_offset)
        bound.towerHeight +
      ERMor1.minN_outer_towerHeight_offset := by
  _
```

The named offsets `boundedSearch_towerHeight_offset` /
`beta_minN_towerHeight_offset` /
`minN_outer_towerHeight_offset` are introduced as
`private def` declarations in the same file, each defined
by structural unfold of the relevant ER expression's
towerHeight.  Define them as exact natural-number
constants — pinned by `decide` against the unfolded
towerHeight value at zero arguments, e.g.

```lean
private def ERMor1.minN_outer_towerHeight_offset : ℕ :=
  (ERMor1.comp ERMor1.minN
    (fun (_ : Fin 2) => ERMor1.zeroN 0)).towerHeight
```

Decide each constant once and refer by name thereafter.

If introducing three named offsets is overkill, fold them
into a single `boundedRec_towerHeight_overhead : ℕ`
constant whose RHS is `(boundedRec zero (proj 0) zero).
towerHeight`.  This keeps the `_eq` lemma's RHS short at
the cost of opacity:

```lean
private def ERMor1.boundedRec_towerHeight_overhead : ℕ :=
  (ERMor1.boundedRec ERMor1.zero
    (ERMor1.proj ⟨0, by omega⟩) ERMor1.zero).towerHeight

theorem ERMor1.boundedRec_towerHeight_eq {k : ℕ}
    (base : ERMor1 k) (step : ERMor1 (k + 2))
    (bound : ERMor1 (k + 1)) :
    (ERMor1.boundedRec base step bound).towerHeight =
      max (max (max base.towerHeight step.towerHeight)
                bound.towerHeight)
          (boundedRec_towerHeight_overhead) +
      0 := by
  sorry
```

The single-constant form is recommended for the plan since
the downstream lemmas only need a `≥ bound.tH + const`-style
inequality, not a precise breakdown.

- [ ] **Step E.3.3: Prove the `_eq` lemma**

If the single-constant form is chosen, prove by structural
unfold of `boundedRec`, `boundedSearch`, `boundedRecRange`,
`boundedRecPred`:

```lean
theorem ERMor1.boundedRec_towerHeight_eq {k : ℕ}
    (base : ERMor1 k) (step : ERMor1 (k + 2))
    (bound : ERMor1 (k + 1)) :
    (ERMor1.boundedRec base step bound).towerHeight =
      max (max (max base.towerHeight step.towerHeight)
                bound.towerHeight)
          (boundedRec_towerHeight_overhead) := by
  unfold ERMor1.boundedRec
  unfold ERMor1.boundedSearch
  unfold ERMor1.boundedRecRange
  unfold ERMor1.boundedRecPred
  simp only [ERMor1.towerHeight]
  -- Each occurrence of `base.towerHeight`, `step.towerHeight`,
  -- `bound.towerHeight` rolls up via Finset.univ.sup over the
  -- inner branches.  Atomic generators contribute 0; the
  -- residual fixed structural depth is the constant
  -- `boundedRec_towerHeight_overhead`.
  -- Close with omega over the resulting max-of-max
  -- expression.
  unfold boundedRec_towerHeight_overhead
  simp only [ERMor1.towerHeight]
  omega
```

If `omega` does not close because `Finset.univ.sup` over a
finite case-analysis is opaque, replace with explicit
`Finset.sup_le` plus `Finset.le_sup` instances, mirroring
the pattern used in
`kSimSzudzikPackList_towerHeight_ge_propagate` (lines
1391–1493 of `LawvereKSimPolynomialBound.lean`).

- [ ] **Step E.3.4: Run `lake build` + `lake test`**

Run: `lake build && lake test`
Expected: PASS, no warnings.

- [ ] **Step E.3.5: Commit**

```bash
git add GebLean/Utilities/ERArith.lean
git commit -m "$(cat <<'EOF'
boundedRec towerHeight closed form (Task 17c E.3)

Adds boundedRec_towerHeight_eq pinning
(boundedRec base step bound).towerHeight as
max(max(max base.tH, step.tH), bound.tH) + C_overhead
for a closed constant C_overhead.  Proof by structural
unfold of boundedRec / boundedSearch / boundedRecRange /
boundedRecPred against ERMor1.towerHeight's recursion.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task E.4: `boundedRec` towerHeight ≥ bound corollary

**Files:**

- Modify: `GebLean/Utilities/ERArith.lean`
  (insert after `boundedRec_towerHeight_eq`)

- [ ] **Step E.4.1: State the lemma**

```lean
/-- Structural lower bound on `boundedRec`'s tower height
in terms of the `bound` argument's tower height. -/
theorem ERMor1.boundedRec_towerHeight_ge_bound {k : ℕ}
    (base : ERMor1 k) (step : ERMor1 (k + 2))
    (bound : ERMor1 (k + 1)) :
    bound.towerHeight ≤
      (ERMor1.boundedRec base step bound).towerHeight := by
  _
```

- [ ] **Step E.4.2: Prove the lemma**

```lean
theorem ERMor1.boundedRec_towerHeight_ge_bound {k : ℕ}
    (base : ERMor1 k) (step : ERMor1 (k + 2))
    (bound : ERMor1 (k + 1)) :
    bound.towerHeight ≤
      (ERMor1.boundedRec base step bound).towerHeight := by
  rw [ERMor1.boundedRec_towerHeight_eq]
  exact le_trans (le_max_left _ _) (le_max_left _ _)
```

If the closed form's max nesting differs from the above,
adjust the `le_max_*` chain accordingly.

- [ ] **Step E.4.3: State the symmetric lemmas**

Add `boundedRec_towerHeight_ge_base` and
`boundedRec_towerHeight_ge_step` as parallel corollaries:

```lean
theorem ERMor1.boundedRec_towerHeight_ge_base {k : ℕ}
    (base : ERMor1 k) (step : ERMor1 (k + 2))
    (bound : ERMor1 (k + 1)) :
    base.towerHeight ≤
      (ERMor1.boundedRec base step bound).towerHeight := by
  rw [ERMor1.boundedRec_towerHeight_eq]
  -- threading through the max-of-max nesting to base
  exact le_trans
    (le_trans (le_max_left _ _) (le_max_left _ _))
    (le_max_left _ _)

theorem ERMor1.boundedRec_towerHeight_ge_step {k : ℕ}
    (base : ERMor1 k) (step : ERMor1 (k + 2))
    (bound : ERMor1 (k + 1)) :
    step.towerHeight ≤
      (ERMor1.boundedRec base step bound).towerHeight := by
  rw [ERMor1.boundedRec_towerHeight_eq]
  exact le_trans
    (le_trans (le_max_right _ _) (le_max_left _ _))
    (le_max_left _ _)
```

- [ ] **Step E.4.4: Run `lake build` + `lake test`**

Run: `lake build && lake test`
Expected: PASS, no warnings.

- [ ] **Step E.4.5: Commit**

```bash
git add GebLean/Utilities/ERArith.lean
git commit -m "$(cat <<'EOF'
boundedRec towerHeight ≥ {bound,base,step} corollaries (Task 17c E.4)

Three corollaries of boundedRec_towerHeight_eq from E.3,
extracting each input argument's towerHeight as a lower
bound on (boundedRec base step bound).towerHeight.  Used by
Task 17c E.5 to lift child bounds through the simrec
encoding's boundedRec layer.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task E.5: `kSimTowerBound` towerHeight ≥ stepTH

**Files:**

- Modify: `GebLean/Utilities/KSimSzudzikSimrec.lean`
  (insert after `theorem kSimTowerBound_mono_counter`,
  currently ending around line 462)

`kSimTowerBound h g = iterAutoBoundExpr a stepTH baseTH`
where `stepTH = (kSimPackedStep g).towerHeight` and
`baseTH = (kSimPackedBase h).towerHeight`.  By
`iterAutoBoundExpr_towerHeight_ge_d` (E.2),
`(iterAutoBoundExpr a stepTH baseTH).towerHeight ≥ stepTH`.
So
`(kSimTowerBound h g).towerHeight ≥ (kSimPackedStep g).towerHeight`.

Combined with `kSimPackedStep_towerHeight_ge_propagate`
(`LawvereKSimPolynomialBound.lean:1507`) which gives
`(kSimPackedStep g).towerHeight ≥
ERMor1.natPair.towerHeight + 2 +
sup_l (comp (g l) kSimStepContext).towerHeight`, we get
`(kSimTowerBound h g).towerHeight ≥
sup_l (g l).towerHeight + small_const`.

- [ ] **Step E.5.1: State the lemma — direct form**

```lean
/-- Structural lower bound on `kSimTowerBound`'s tower
height in terms of the packed step's tower height. -/
theorem kSimTowerBound_towerHeight_ge_packedStep
    {a k : ℕ}
    (h : Fin (k + 1) → ERMor1 a)
    (g : Fin (k + 1) → ERMor1 (a + 1 + (k + 1))) :
    (kSimPackedStep g).towerHeight ≤
      (kSimTowerBound h g).towerHeight := by
  unfold kSimTowerBound
  exact ERMor1.iterAutoBoundExpr_towerHeight_ge_d _ _ _
```

- [ ] **Step E.5.2: State the lemma — propagated form**

```lean
/-- Structural lower bound on `kSimTowerBound`'s tower
height in terms of the maximum-over-step-family child tower
height. -/
theorem kSimTowerBound_towerHeight_ge_max_step_child
    {a k : ℕ}
    (h : Fin (k + 1) → ERMor1 a)
    (g : Fin (k + 1) → ERMor1 (a + 1 + (k + 1))) :
    ERMor1.natPair.towerHeight + 2 +
      (Finset.univ : Finset (Fin (k + 1))).sup
        (fun l =>
          (ERMor1.comp (g l) kSimStepContext).towerHeight) ≤
      (kSimTowerBound h g).towerHeight := by
  exact le_trans
    (kSimPackedStep_towerHeight_ge_propagate g)
    (kSimTowerBound_towerHeight_ge_packedStep h g)
```

`kSimPackedStep_towerHeight_ge_propagate` is currently
`private` in `LawvereKSimPolynomialBound.lean`.  If
`kSimTowerBound_towerHeight_ge_max_step_child` is to live
in `KSimSzudzikSimrec.lean` (which imports nothing from
`LawvereKSimPolynomialBound.lean`), the private modifier
on the propagate lemma would need to be relaxed.

**Resolution:** instead place
`kSimTowerBound_towerHeight_ge_max_step_child` (and any
descendants relying on `kSimPackedStep_towerHeight_ge_propagate`)
in `LawvereKSimPolynomialBound.lean`, in the structural
lemmas section, alongside the existing propagate lemmas.
Move `kSimTowerBound_towerHeight_ge_packedStep` there too
for proximity.

Updated file plan:

- `GebLean/Utilities/KSimSzudzikSimrec.lean`: no additions
  for E.5 (the direct form belongs near the propagate
  lemmas).
- `GebLean/LawvereKSimPolynomialBound.lean`: add both
  E.5.1's direct form and E.5.2's propagated form as
  `private theorem`s after
  `kSimPackedStep_towerHeight_ge_propagate` (line 1507+).

- [ ] **Step E.5.3: Place both lemmas in
  `LawvereKSimPolynomialBound.lean`**

```lean
/-- Structural lower bound on `kSimTowerBound`'s tower
height in terms of the packed step's tower height.
Routes through `iterAutoBoundExpr_towerHeight_ge_d` (Task
17c E.2): `kSimTowerBound h g = iterAutoBoundExpr a
stepTH baseTH` where `stepTH = (kSimPackedStep g).
towerHeight`. -/
private theorem kSimTowerBound_towerHeight_ge_packedStep
    {a k : ℕ}
    (h : Fin (k + 1) → ERMor1 a)
    (g : Fin (k + 1) → ERMor1 (a + 1 + (k + 1))) :
    (kSimPackedStep g).towerHeight ≤
      (kSimTowerBound h g).towerHeight := by
  unfold kSimTowerBound
  exact ERMor1.iterAutoBoundExpr_towerHeight_ge_d _ _ _

/-- Structural lower bound on `kSimTowerBound`'s tower
height in terms of the maximum-over-step-family child tower
height. -/
private theorem kSimTowerBound_towerHeight_ge_max_step_child
    {a k : ℕ}
    (h : Fin (k + 1) → ERMor1 a)
    (g : Fin (k + 1) → ERMor1 (a + 1 + (k + 1))) :
    ERMor1.natPair.towerHeight + 2 +
      (Finset.univ : Finset (Fin (k + 1))).sup
        (fun l =>
          (ERMor1.comp (g l) kSimStepContext).towerHeight) ≤
      (kSimTowerBound h g).towerHeight :=
  le_trans
    (kSimPackedStep_towerHeight_ge_propagate g)
    (kSimTowerBound_towerHeight_ge_packedStep h g)
```

- [ ] **Step E.5.4: Run `lake build` + `lake test`**

Run: `lake build && lake test`
Expected: PASS, no warnings.

- [ ] **Step E.5.5: Commit**

```bash
git add GebLean/LawvereKSimPolynomialBound.lean
git commit -m "$(cat <<'EOF'
kSimTowerBound towerHeight ≥ packed-step / max-child (Task 17c E.5)

Two private lemmas:
- kSimTowerBound_towerHeight_ge_packedStep: routes through
  iterAutoBoundExpr_towerHeight_ge_d to bound stepTH from
  below by (kSimPackedStep g).towerHeight.
- kSimTowerBound_towerHeight_ge_max_step_child: composes
  with the existing kSimPackedStep_towerHeight_ge_propagate
  to bound by max_l (comp (g l) kSimStepContext).towerHeight
  plus a small constant.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task E.6: `kToER simrec` towerHeight ≥ max-child

**Files:**

- Modify: `GebLean/LawvereKSimPolynomialBound.lean`
  (insert after `kSimTowerBound_towerHeight_ge_max_step_child`)

The simrec wrapping (`LawvereKSimER.lean:58–93`) is:

```text
kToER (simrec i h g) =
  comp (kSimSzudzikUnpackAt a i.val)
    (fun j => if j.val = 0 then recur else proj …)
where
  recur = boundedRec (kSimPackedBase h_ER)
                     (kSimPackedStep g_ER)
                     (kSimTowerBound h_ER g_ER)
  h_ER l = kToER (h_fam l) _
  g_ER l = kToER (g_fam l) _
```

By the towerHeight recursion,
`(kToER simrec).towerHeight =
(kSimSzudzikUnpackAt a i.val).towerHeight +
sup_j (branch j).towerHeight + 1`,
where branch 0 = recur and branch j>0 = proj (atomic).

`(recur).towerHeight =
(boundedRec base step bound).towerHeight ≥
bound.towerHeight = (kSimTowerBound h_ER g_ER).towerHeight`
(by E.4's `_ge_bound` corollary).

By E.5.2,
`(kSimTowerBound h_ER g_ER).towerHeight ≥
ERMor1.natPair.towerHeight + 2 +
sup_l (comp (g_ER l) kSimStepContext).towerHeight ≥
ERMor1.natPair.towerHeight + 2 + sup_l (g_ER l).towerHeight`
(the last `≥` because `comp f g`'s towerHeight always
exceeds `g`'s sup, hence in particular each `g_ER l`'s
towerHeight, by `Finset.le_sup`).

For the **combined-max form** also covering `h_ER`, route
through `kSimPackedBase_towerHeight_ge_propagate` plus a
new corollary

```text
kSimTowerBound_towerHeight_ge_max_base_child :
  (kSimTowerBound h_ER g_ER).towerHeight ≥
  natPair.tH + 2 + sup_l (h_ER l).towerHeight + (search-overhead)
```

via the `boundedRec`'s `base` argument flowing through
`boundedRecPred`'s `boundedSearch`.  The search-overhead is
a closed positive constant; since it strictly exceeds 0,
the inequality

```text
(kSimTowerBound h_ER g_ER).towerHeight ≥
  max (sup_l (h_ER l).towerHeight)
      (sup_l (g_ER l).towerHeight) + small_const
```

follows from combining the step-side bound (E.5.2) with the
base-side bound via `max_le_iff`.

For the auxiliary lemma's clients, the combined form is
sufficient.  We state it directly.

- [ ] **Step E.6.1: State the auxiliary lemma**

```lean
/-- Auxiliary structural lemma for the Phase IV-B chain:
`kToER (simrec h_fam g_fam i)`'s tower height dominates the
maximum-over-children tower height plus a small structural
constant.  This is the level-2 analog of
`kToER_level0_towerHeight_ge_const` (Phase III A.5.2.1).
The `small_const` is ≥ 1 (covering the `+1`-per-comp wrap
plus structural overheads of `kSimSzudzikUnpackAt` and the
`boundedRec` encoding). -/
private theorem kToER_simrec_towerHeight_ge_max_child_tH
    {a k : ℕ}
    (h_fam : Fin (k + 1) → KMor1 a)
    (g_fam : Fin (k + 1) → KMor1 (a + 1 + (k + 1)))
    (h_h : ∀ l, (h_fam l).level ≤ 1)
    (h_g : ∀ l, (g_fam l).level ≤ 1)
    (i : Fin (k + 1))
    (hyp : (KMor1.simrec i h_fam g_fam).level ≤ 2) :
    max
      ((Finset.univ : Finset (Fin (k + 1))).sup
        (fun l =>
          (kToER (h_fam l)
            (Nat.le_succ_of_le (h_h l))).towerHeight))
      ((Finset.univ : Finset (Fin (k + 1))).sup
        (fun l =>
          (kToER (g_fam l)
            (Nat.le_succ_of_le (h_g l))).towerHeight)) ≤
      (kToER (KMor1.simrec i h_fam g_fam) hyp).towerHeight := by
  _
```

The lemma's RHS is the simrec's `kToER.towerHeight`; the
LHS is the combined-max over children, with NO `+ small_const`
term — the structural overheads will be hidden inside the
slack between LHS and RHS.  (The Phase IV-B main lemma
needs the existence of slack, not an explicit constant.)

- [ ] **Step E.6.2: Prove the lemma**

```lean
private theorem kToER_simrec_towerHeight_ge_max_child_tH
    {a k : ℕ}
    (h_fam : Fin (k + 1) → KMor1 a)
    (g_fam : Fin (k + 1) → KMor1 (a + 1 + (k + 1)))
    (h_h : ∀ l, (h_fam l).level ≤ 1)
    (h_g : ∀ l, (g_fam l).level ≤ 1)
    (i : Fin (k + 1))
    (hyp : (KMor1.simrec i h_fam g_fam).level ≤ 2) :
    max
      ((Finset.univ : Finset (Fin (k + 1))).sup
        (fun l =>
          (kToER (h_fam l)
            (Nat.le_succ_of_le (h_h l))).towerHeight))
      ((Finset.univ : Finset (Fin (k + 1))).sup
        (fun l =>
          (kToER (g_fam l)
            (Nat.le_succ_of_le (h_g l))).towerHeight)) ≤
      (kToER (KMor1.simrec i h_fam g_fam) hyp).towerHeight := by
  -- Step 1: unfold kToER's simrec case to expose
  -- comp (kSimSzudzikUnpackAt _) [recur, ...].
  unfold kToER
  -- Step 2: the outer `comp` adds `tH(unpackAt) + sup +
  -- 1`.  The sup picks recur (which dominates the proj
  -- branches), so it suffices to bound `recur.tH` from
  -- below by max(h_sup, g_sup).
  simp only [ERMor1.towerHeight]
  -- Step 3: recur = boundedRec(base, step, bound) with
  -- bound = kSimTowerBound h_ER g_ER.  By
  -- boundedRec_towerHeight_ge_bound (E.4), recur.tH ≥
  -- bound.tH.
  -- Step 4: bound.tH ≥ (kSimPackedStep g_ER).tH (E.5.1)
  -- which propagates to ≥ sup_l (g_ER l).tH + small.
  have hg_le :
      (Finset.univ : Finset (Fin (k + 1))).sup
        (fun l =>
          (kToER (g_fam l)
            (Nat.le_succ_of_le (h_g l))).towerHeight) ≤
      (kSimTowerBound _ _).towerHeight := by
    -- Combine kSimTowerBound_towerHeight_ge_max_step_child
    -- with Finset.le_sup at each l.
    sorry  -- detailed proof: thread through the step's
            -- comp(g_l, kSimStepContext) and use
            -- Finset.le_sup of (g_l).tH ≤
            -- (comp g_l kSimStepContext).tH.
  -- Step 5: similarly for h_fam via the base side.
  have hh_le :
      (Finset.univ : Finset (Fin (k + 1))).sup
        (fun l =>
          (kToER (h_fam l)
            (Nat.le_succ_of_le (h_h l))).towerHeight) ≤
      (kSimTowerBound _ _).towerHeight := by
    sorry  -- detailed proof: thread through
            -- kSimPackedBase_towerHeight_ge_propagate plus
            -- the boundedRec base-side flow through
            -- boundedRecPred.
  -- Step 6: combine via max_le_iff and lift through the
  -- outer comp.
  have hbound_le :
      (kSimTowerBound _ _).towerHeight ≤
        (ERMor1.boundedRec _ _ _).towerHeight :=
    ERMor1.boundedRec_towerHeight_ge_bound _ _ _
  apply max_le
  · -- h-side
    calc _ ≤ (kSimTowerBound _ _).towerHeight := hh_le
      _ ≤ (ERMor1.boundedRec _ _ _).towerHeight := hbound_le
      _ ≤ _ := by
          -- lift through the outer comp
          have hbranch_le_sup :
              (ERMor1.boundedRec _ _ _).towerHeight ≤
                Finset.univ.sup _ := Finset.le_sup
                  (Finset.mem_univ ⟨0, by omega⟩)
          omega
  · -- g-side, parallel
    calc _ ≤ (kSimTowerBound _ _).towerHeight := hg_le
      _ ≤ (ERMor1.boundedRec _ _ _).towerHeight := hbound_le
      _ ≤ _ := by
          have hbranch_le_sup :
              (ERMor1.boundedRec _ _ _).towerHeight ≤
                Finset.univ.sup _ := Finset.le_sup
                  (Finset.mem_univ ⟨0, by omega⟩)
          omega
```

The two `sorry`s are filled by detailed mechanical proofs
threading through `kSimPackedStep_towerHeight_ge_propagate`
/ `kSimPackedBase_towerHeight_ge_propagate` plus the
appropriate `boundedRec_towerHeight_ge_*` corollaries from
E.4 — the underscore branches in the outer `comp` need to
be discharged with explicit `if` resolution (the `j.val = 0`
case selects `recur`, all other cases pick `proj` which has
towerHeight 0).

Each `sorry` is a sub-task of E.6:

- [ ] **Step E.6.3: Fill `hg_le` (g-family side)**

Replace the first `sorry` with the detailed step.  Use
`kSimTowerBound_towerHeight_ge_max_step_child` (E.5.2) to
bound by `natPair.tH + 2 + sup_l (comp g_l kSimStepContext)
.tH`, then unfold `(comp g_l kSimStepContext).tH = g_l.tH +
sup kSimStepContext-component.tH + 1 ≥ g_l.tH + 1` via the
sup over comp.  Finally apply `Finset.sup_le` plus
`Finset.le_sup` to lift each individual `g_ER l` bound to
the family sup.

- [ ] **Step E.6.4: Fill `hh_le` (h-family side)**

Replace the second `sorry`.  Threads through
`kSimPackedBase_towerHeight_ge_propagate` (`g_l` family
replaced by `h_l` family with `comp h_l kSimStepContext`
replaced by `h_l` directly — the base side does not wrap
in `kSimStepContext`).  Then through
`boundedRec_towerHeight_ge_base` (E.4 symmetric corollary)
to lift through the boundedRec layer instead of the
`bound` argument — since `kSimPackedBase` enters as
`base` of the boundedRec, not as `bound`.

- [ ] **Step E.6.5: Resolve the `if`-dite branch**

The outer `comp` of `kToER simrec` has `(fun j => if
j.val = 0 then recur else proj …)`.  At j = 0 the branch
is `recur`; at j > 0 it is `proj _` (atomic, towerHeight
0).  The sup over the branches simplifies to
`(recur).towerHeight` (since 0-towerHeight branches
contribute nothing to a max).  Use `Finset.le_sup` at
`⟨0, _⟩` to extract the `recur` bound from the sup.

- [ ] **Step E.6.6: Run `lake build` + `lake test`**

Run: `lake build && lake test`
Expected: PASS, no warnings.

- [ ] **Step E.6.7: Commit**

```bash
git add GebLean/LawvereKSimPolynomialBound.lean
git commit -m "$(cat <<'EOF'
kToER simrec towerHeight ≥ combined-max child (Task 17c E.6)

Auxiliary structural lemma kToER_simrec_towerHeight_ge_max_child_tH:
  max (max_l (kToER (h_fam l)).tH) (max_l (kToER (g_fam l)).tH)
    ≤ (kToER (simrec i h_fam g_fam) hyp).tH.
Routes through:
- E.4 (boundedRec_towerHeight_ge_bound / _ge_base) to lift
  bounds across the boundedRec encoding;
- E.5 (kSimTowerBound_towerHeight_ge_max_step_child) plus
  the existing kSimPackedStep_towerHeight_ge_propagate to
  reach the g-family children;
- kSimPackedBase_towerHeight_ge_propagate (already landed)
  to reach the h-family children.

The outer `comp (kSimSzudzikUnpackAt _) ...` wrapping is
discharged by Finset.le_sup at the `recur` branch (j = 0).

This is the Step-1 deliverable of the Phase IV-B
implementation; the main inequality
KMor1.linearBoundLog_le_towerHeight (Step 2) consumes it
in the simrec case of its structural induction.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task E.7: Tests + final verification

**Files:**

- Modify: `GebLeanTests/Phase4Investigation.lean`
  (append concrete-witness tests for E.6)

- [ ] **Step E.7.1: Add #guard for the auxiliary
  lemma on `addK`**

```lean
-- E.6 sanity: the combined-max child bound holds on addK,
-- whose h_fam (level 0, 1 child) and g_fam (level 0, 1
-- child) translate to atomic ER terms with towerHeight 0,
-- while (kToER addK).towerHeight = 1117.  The lemma
-- predicts max(0, 0) = 0 ≤ 1117 — trivially.
#guard 0 ≤ addK_ER_tH
```

This is a sanity #guard, not a proper test of the lemma's
proof — but the lemma is verified by `lake build` already.
The #guard documents the expected slack on the addK
witness.

- [ ] **Step E.7.2: Run `lake build` + `lake test`**

Run: `lake build && lake test`
Expected: PASS, no warnings, all 1559+ tests pass.

- [ ] **Step E.7.3: Commit**

```bash
git add GebLeanTests/Phase4Investigation.lean
git commit -m "$(cat <<'EOF'
Phase4Investigation: addK sanity #guard for auxiliary lemma (Task 17c E.7)

Adds a documentation #guard for the auxiliary lemma
kToER_simrec_towerHeight_ge_max_child_tH (Task 17c E.6):
on the addK witness, the lemma predicts max(0, 0) ≤ 1117
(trivially), confirming the structural slack pattern.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Wong Prop. 4.6 mapping recap

The auxiliary lemma threads Wong's exponent-tracking recipe
(Recursion Class Ch. 4 Prop. 4.6) through our specific
`towerHeight` recursion:

- **Composition** `C(f, g_1, …, g_k)`: Wong's exponent
  `m + max j(i)`.  Project: ER `comp f g` has tH =
  `f.tH + sup_i (g i).tH + 1`.
- **Bounded recursion** `R(g, f, e)`: Wong's exponent
  inherited from `e`'s.  Project: ER `boundedRec base
  step bound` has tH ≥ `bound.tH` (E.4).
- **Iterated bound term**: Wong's `(e_{n+2})^k(max(x⃗))`
  at level `n + 3`.  Project: `kSimTowerBound =
  iterAutoBoundExpr a stepTH baseTH`, with tH ≥
  `stepTH` (E.5.1).

The auxiliary lemma chains these: K^sim simrec wraps a
`boundedRec` whose `bound` is `kSimTowerBound` whose
`d`-parameter is `(kSimPackedStep g_ER).towerHeight` which
propagates to `max_l (g_ER l).tH + small_const`.  The
`base` argument of the same `boundedRec` is
`kSimPackedBase h_ER` whose towerHeight propagates to
`max_l (h_ER l).tH + small_const'`.  Combining the two
sides yields the combined-max form.

---

## Self-review checklist

**Spec coverage**: every numbered task in the resumption
prompt v2 (Step 1) is covered:

- ✓ Exact theorem statement (E.6.1).
- ✓ Lean module placement (file structure section).
- ✓ Wong Prop. 4.6 mapping (Wong recap section above).
- ✓ Dependency on existing `_ge_propagate` lemmas (E.5.2,
  E.6.3, E.6.4).
- ✓ Per-step build/test checkpoints (every task ends with
  `lake build && lake test`).
- ✓ Per-task commit subjects ending in `(Task 17c X.Y)`.

**Placeholder scan**: two `sorry`s in E.6.2 (the
`hg_le` / `hh_le` `have`s) are explicitly listed as
sub-tasks E.6.3 and E.6.4 with detailed unfold instructions.
These are not unhandled placeholders — they are
intentional, named, planned sub-steps with concrete
filling instructions.

**Type consistency**: all theorem statements use the same
`(h_h : ∀ l, (h_fam l).level ≤ 1)` /
`(h_g : ∀ l, (g_fam l).level ≤ 1)` hypothesis form across
E.5 and E.6.  All RHS uses `(kToER … (Nat.le_succ_of_le …))
.towerHeight` consistently.  No name collisions with
existing lemmas.

**Note on the `_eq` form vs `_ge_*` form trade-off in E.3**:
the plan recommends the single-constant
`boundedRec_towerHeight_overhead` form for brevity and
provides the multi-constant breakdown as an alternative.
Implementer's discretion — both close E.4's corollaries.

---

## Out-of-scope deferred work

Step 2 of the resumption-prompt-v2 process (writing the
plan for `KMor1.linearBoundLog_le_towerHeight`) is a
separate plan, written after this auxiliary plan is
approved and (preferably) executed.  The main lemma's plan
will consume `kToER_simrec_towerHeight_ge_max_child_tH`
(E.6) in its simrec case.

Step 3 (subagent-driven-development execution) is the
implementation phase, post-approval.
