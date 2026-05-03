# Step 4 — K^sim majorization theorems (Tourlakis 0.1.0.10)

Spec for cycle 4 of the ER ↔ K^sim_2 categorical-equivalence
formalization (master design:
`docs/research/2026-05-02-er-ksim2-equiv-via-urm-master-design.md`).
This cycle lands the K^sim → ER `A_n^r` majorization theorems
implementing Tourlakis 2018 §0.1.0.10, plus the ER-side
context-sum named composites and a step-5 plug-in bridge
lemma.  All majorization-arithmetic risk is concentrated in
this step; step 5's `kToER` cycle becomes structural
plumbing only.

## §1 Status and motivation

### §1.1 Goal

Realize Tourlakis 2018 §0.1.0.10 (the majorization theorem
for K^sim level 2) as a pair of structural-induction
theorems in Lean.  Together with step 3's named composites
(`ERMor1.A_one_iter`, `ERMor1.A_two_iter`) and step 2's
simultaneous bounded recursion infrastructure
(`ERMor1.simultaneousBoundedRec`,
`simultaneousBoundedRec_interp_correct`), this provides the
last remaining input to step 5's `kToER` simrec case.

Concretely, for every `f : KMor1 a` with `f.level ≤ n` (where
`n ≤ 2`), produce a Lean-computable `(r, offset) : ℕ × ℕ`
such that:

```text
∀ v : Fin a → ℕ,
  f.interp v ≤ (ERMor1.A_n_iter r).interp ![vMax v + offset]
```

### §1.2 Scope

In scope:

- `GebLean/LawvereKSimMajorization.lean` (top-level,
  K^sim ↔ ER bridge module):
  - Private `vMax` abbreviation.
  - ER-side: `ERMor1.sumCtxER`, `ERMor1.sumCtxERPlusOffset`
    named composites, with closed-form `@[simp]` interp
    lemmas and dominance helpers
    (`vMax_le_sumCtxER`,
    `vMax_add_offset_le_sumCtxERPlusOffset`).
  - Cross-family translation lemmas
    (`linearBound_le_A_one_iter`,
    `A_one_iter_le_two_pow_succ`,
    `two_pow_succ_mul_succ_le_tower_two`,
    `A_one_iter_le_A_two_iter_two`,
    `A_one_iter_compose`).
  - K^sim-side defs: `KMor1.majorize_one`, `KMor1.majorize`.
  - K^sim-side dominance theorems:
    `KMor1.majorize_by_A_one_iter`,
    `KMor1.simrecVec_le_A_one_iter`,
    `KMor1.majorize_by_A_two_iter`.
  - Step-5 bridge: `KMor1.majorize_by_componentBound`.
- Tests: `GebLeanTests/LawvereKSimMajorization.lean`.

Out of scope (step 5 owns):

- `kToER : ∀ {a} (f : KMor1 a), f.level ≤ 2 → ERMor1 a`
  structural-induction definition.
- `kToER`'s correctness theorem
  (`f.interp = (kToER f h).interp`).
- `kToERFunctor` and the equivalence of categories
  `LawvereKSimDCat 2 ≌ LawvereERCat`.

Out of scope and not anyone's job:

- A K^sim-side `A_n` analogue: master design §3.3 builds
  `A_n` on the ER side only.  Step 4 produces ER-side
  bounds for K^sim morphisms; the K^sim side has no
  `A_n` family of its own.
- Tighter atomic-case `r` values: §4.3 below documents
  why all atoms get uniform `r = 2`.
- `ERMor1.maxCtxER` (max-of-context, tighter than sum):
  master design §3.5 line 1108–1113 explicitly authorizes
  `sumCtxER` for the bound construction; building a
  separate `maxCtxER` would require ER-level `subN`/`max`
  composition that buys nothing for step 5's needs.

### §1.3 Implementation flexibility vs literature contract

Per CLAUDE.md "Non-negotiable interfaces for categories
formalizing pre-existing mathematical objects": the
mathematical content is fixed by literature; Lean
representation choices may flex.

**Literature-fixed (non-negotiable):**

- The shape `f.interp v ≤ A_n_iter r (vMax v + offset)`
  with `n ≤ 2` (Tourlakis 2018 §0.1.0.10).
- The level-2 simrec case's tower height stays at `r = 2`,
  with offset linear in the children's majorant constants
  (master design §3.4 lines 1051–1053:
  `r_2 := 2`, `offset_2 := r_H + r_G + 2`).
- The cross-family bound `A_1^k(x) ≤ A_2^2(x + k + 2)`
  (master design §3.4 lines 1027–1029).

**Lean-side flexible:**

- Exact arithmetic of the iteration bound's `r`/`offset`
  values (the implementer may produce any pair
  satisfying the dominance theorem; tighter is fine but
  not required).
- Choice of `Nat.log 2 (·) + 1` vs an alternative
  ceiling-log formulation in `linearBound_le_A_one_iter`.
- Auxiliary-lemma factoring inside the level-2 simrec
  proof.
- Exact `Fin.foldr` patterns for the `comp` and `simrec`
  cases of `KMor1.majorize` (mirroring `KMor1.linearBound`
  is recommended but not required).
- Whether to derive `(2, 2)` or `(2, 3)` etc. as the
  atomic-case `(r, offset)` triples — any uniform-`r ≥ 2`
  choice that satisfies the dominance theorem is fine.

The implementer may revise any Lean-side representation
during implementation if proofs reveal a cleaner path,
provided the literature contract is preserved.

## §2 Architecture and module layout

One new top-level module:

### §2.1 `GebLean/LawvereKSimMajorization.lean`

- Imports:
  - `GebLean.LawvereKSim` (for `KMor1`, `KMor1.level`,
    `KMor1.interp`, `KMor1.simrecVec`, and their interp
    simp lemmas).
  - `GebLean.LawvereKSimPolynomialBound` (for
    `KMor1.linearBound` and
    `KMor1.linearBound_dominates` at the level-1 case).
  - `GebLean.Utilities.ERAMajorants` (for
    `ERMor1.A_one_iter`, `ERMor1.A_two_iter`, and their
    closed-form `@[simp]` interp lemmas
    `interp_A_one_iter`, `interp_A_two_iter`).
  - `GebLean.Utilities.ERArith` (for `ERMor1.addN`,
    `ERMor1.natN`, and their interp simp lemmas).
  - `GebLean.Utilities.Tower` (for `tower`,
    `tower_mono_right`, `tower_mono_left`, `self_le_tower`,
    and `tower_comp`).
  - Mathlib: `Mathlib.Data.Nat.Log` (for `Nat.log`),
    `Mathlib.Algebra.BigOperators.Fin` (for the sum
    machinery used by `interp_sumCtxER`).
- Namespace: `GebLean`, with definitions under `KMor1`
  (majorize family), under `ERMor1` (`sumCtxER`
  variants), and a private file-local `vMax` abbreviation.

### §2.2 Tests

- `GebLeanTests/LawvereKSimMajorization.lean`.

### §2.3 Imports at skeleton-creation time

Per discipline-1 (steps 1–3 lessons): each new module's
import is registered in `GebLean.lean` (or
`GebLeanTests.lean` for tests) immediately when the
skeleton file is created, before any code is added to it.
This guarantees `lake build` re-elaborates the new module
on every subsequent task, catching linter regressions in
real time.

### §2.4 Dependency graph

```text
LawvereKSim                    (existing)
  ↓
LawvereKSimPolynomialBound     (existing)
  ↓
ERAMajorants                   (existing, step 3)
  ↓
LawvereKSimMajorization        [step 4, this cycle]
  ↓
LawvereKSimER (kToER)          [step 5]
```

## §3 ER-side helpers

All in `namespace GebLean.ERMor1`.

### §3.1 `ERMor1.sumCtxER : (n : ℕ) → ERMor1 n`

```lean
/-- n-ary sum of the input context: `(sumCtxER n).interp v
= ∑ i, v i`.  Built bottom-up by recursion on `n` from the
binary `addN`.  Master design §3.5 lines 1108–1113 (the
`kToER` simrec componentBound construction).

At `n = 0`: empty sum, realized as `zeroN 0`.
At `n + 1`: `addN (proj (Fin.last n)) (sumCtxER n
∘ embed_castSucc)`. -/
def sumCtxER : (n : ℕ) → ERMor1 n
  | 0     => ERMor1.zeroN 0
  | n + 1 =>
      ERMor1.comp ERMor1.addN fun i => match i with
        | ⟨0, _⟩ => ERMor1.proj (Fin.last n)
        | ⟨1, _⟩ => ERMor1.comp (sumCtxER n)
                      (fun j : Fin n =>
                        ERMor1.proj (Fin.castSucc j))
```

```lean
@[simp] theorem interp_sumCtxER (n : ℕ) (v : Fin n → ℕ) :
    (sumCtxER n).interp v = ∑ i, v i
```

Proof: induction on `n` using `interp_addN`, `interp_proj`,
`interp_zeroN`, and mathlib's `Fin.sum_univ_succ` /
`Fin.sum_univ_castSucc`.

```lean
theorem vMax_le_sumCtxER (n : ℕ) (v : Fin n → ℕ) :
    (Finset.univ : Finset (Fin n)).sup v ≤
      (sumCtxER n).interp v
```

Proof: rewrite RHS via `interp_sumCtxER`, then
`Finset.sup_le_sum` (or equivalent) for `ℕ`-valued
families on `Fin n`.

### §3.2 `ERMor1.sumCtxERPlusOffset : (n offset : ℕ) → ERMor1 n`

```lean
/-- n-ary sum plus a constant offset:
`(sumCtxERPlusOffset n offset).interp v = (∑ i, v i) + offset`.
Step-5 plug-in for the `simultaneousBoundedRec` componentBound
slot, absorbing the `KMor1.majorize` offset.  Master design
§3.5 lines 1108–1113. -/
def sumCtxERPlusOffset (n offset : ℕ) : ERMor1 n :=
  ERMor1.comp ERMor1.addN fun i => match i with
    | ⟨0, _⟩ => sumCtxER n
    | ⟨1, _⟩ => ERMor1.natN n offset
```

```lean
@[simp] theorem interp_sumCtxERPlusOffset
    (n offset : ℕ) (v : Fin n → ℕ) :
    (sumCtxERPlusOffset n offset).interp v
      = (∑ i, v i) + offset
```

```lean
theorem vMax_add_offset_le_sumCtxERPlusOffset
    (n offset : ℕ) (v : Fin n → ℕ) :
    (Finset.univ : Finset (Fin n)).sup v + offset ≤
      (sumCtxERPlusOffset n offset).interp v
```

Proof: combine `vMax_le_sumCtxER` with `Nat.add_le_add_right`.

## §4 Cross-family translation lemmas

All in `namespace GebLean`, file-local.  Pure Nat
arithmetic; no `KMor1` content.

### §4.1 `linearBound_le_A_one_iter` (γ.1)

```lean
/-- Translate a linear bound `c · x + d` into an `A_1^r`
bound, with explicit
`r := max (Nat.log 2 (c + 1) + 1) (Nat.log 2 (d + 2) + 1)`.
Master design §3.4 lines 884–898; Tourlakis 2018 §0.1.0.10
(majorization for atomic and level-1 cases). -/
theorem linearBound_le_A_one_iter (c d : ℕ) :
    let r := max (Nat.log 2 (c + 1) + 1)
                 (Nat.log 2 (d + 2) + 1)
    ∀ x, c * x + d ≤ (ERMor1.A_one_iter r).interp ![x]
```

Proof: rewrite RHS via `interp_A_one_iter` to closed form
`2^r · x + (2^{r+1} − 2)`.  Use `Nat.lt_pow_succ_log_self`
(mathlib) to derive `c + 1 ≤ 2^(Nat.log 2 (c+1) + 1)`, hence
`c ≤ 2^r`.  Same for `d + 2 ≤ 2^(r+1)`, hence
`d ≤ 2^{r+1} − 2`.  Combine via `omega`.

### §4.2 `A_one_iter_le_two_pow_succ` (γ.2)

```lean
/-- Closed-form bound: `A_1^k(x) ≤ 2^{k+1} · (x + 1)`.
Master design §3.4 lines 1015–1019. -/
theorem A_one_iter_le_two_pow_succ (k x : ℕ) :
    (ERMor1.A_one_iter k).interp ![x] ≤ 2^(k+1) * (x + 1)
```

Proof: by `interp_A_one_iter`, LHS = `2^k · x + (2^{k+1} − 2)`.
RHS expands to `2^{k+1} · x + 2^{k+1} = 2 · 2^k · x + 2 · 2^k`.
Difference: `2^k · x + (2 · 2^k − 2) ≤ 2 · 2^k · x + 2 · 2^k`,
which holds by `omega` once `1 ≤ 2^k` (from `Nat.one_le_pow`)
is in scope.

### §4.3 `two_pow_succ_mul_succ_le_tower_two` (γ.3)

```lean
/-- Cross-family bound: `2^{k+1} · (x + 1) ≤ tower 2 (x + k + 2)`.
Master design §3.4 lines 1027–1029.  Composing γ.2 + γ.3
yields `A_1^k(x) ≤ A_2^2(x + k + 2)`. -/
theorem two_pow_succ_mul_succ_le_tower_two (k x : ℕ) :
    2^(k+1) * (x + 1) ≤ tower 2 (x + k + 2)
```

Proof chain:

```text
2^{k+1} · (x+1)
  ≤ 2^{k+1} · 2^{x+1}        (by le_two_pow_self on x+1)
  = 2^{k + x + 2}             (by pow_add; rearrange)
  ≤ 2^{2^{x + k + 2}}         (by le_two_pow_self on
                               k + x + 2 plus
                               pow_le_pow_right)
  = tower 2 (x + k + 2)       (by tower_succ twice)
```

Each step is a small `Nat.pow_*` lemma already in mathlib or
`Tower.lean`.

### §4.4 `A_one_iter_le_A_two_iter_two` (composed corollary)

```lean
/-- Combined cross-family bound: `A_1^k(x) ≤ A_2^2(x + k + 2)`.
Master design §3.4 lines 1015–1029; Tourlakis 2018 §0.1.0.10.
-/
theorem A_one_iter_le_A_two_iter_two (k x : ℕ) :
    (ERMor1.A_one_iter k).interp ![x]
      ≤ (ERMor1.A_two_iter 2).interp ![x + k + 2]
```

Proof: compose γ.2 + γ.3 + `interp_A_two_iter`.

### §4.5 `A_one_iter_compose`

```lean
/-- Composition of `A_1` iterates:
`A_1^a(A_1^b(x)) = A_1^(a+b)(x)`.  Master design §3.4
lines 994–1007 (used implicitly in the `M_n` closed-form
inductive proof). -/
theorem A_one_iter_compose (a b x : ℕ) :
    (ERMor1.A_one_iter a).interp
      ![(ERMor1.A_one_iter b).interp ![x]]
      = (ERMor1.A_one_iter (a + b)).interp ![x]
```

Proof: induction on `a`, both sides reducing via
`interp_A_one_iter` to closed-form Nat expressions
combinable via `pow_add`.

## §5 K^sim majorization defs

### §5.1 `KMor1.majorize_one`

```lean
/-- Level-≤1 majorize witness: returns `(r, offset)` such
that `f.interp v ≤ A_1^r (vMax v + offset)`.  Master design
§3.4 (parenthetical at line 933).  Wrapper around
`KMor1.linearBound` plus γ.1. -/
def KMor1.majorize_one : {a : ℕ} → (f : KMor1 a) →
    f.level ≤ 1 → ℕ × ℕ :=
  fun f h =>
    let p := KMor1.linearBound f h
    let r := max (Nat.log 2 (p.1 + 1) + 1)
                 (Nat.log 2 (p.2 + 2) + 1)
    (r, 0)
```

The offset is uniformly `0` because γ.1 produces an
`A_1^r` bound with no input offset.

### §5.2 `KMor1.majorize`

```lean
/-- Level-≤2 majorize witness: returns `(r, offset)` such
that `f.interp v ≤ A_2^r (vMax v + offset)`.  Structural
recursion on `f`.  Master design §3.4 lines 916–937.

All atomic cases use uniform `r = 2` (per §4.3 of this
spec): tighter atom-level `r` values would force
per-case upcasting at every `comp`/`simrec` node, while
uniform `r ≥ 2` propagates via tower additivity without
upcasting.  The atom-level offset values (`zero` ↦ `2`,
`succ` ↦ `3`, etc.) are chosen so that the dominance
theorem closes with `omega` after rewriting via
`interp_A_two_iter` and `self_le_tower`. -/
def KMor1.majorize : {a : ℕ} → (f : KMor1 a) →
    f.level ≤ 2 → ℕ × ℕ
  | _, .zero,         _ => (2, 2)
  | _, .succ,         _ => (2, 3)
  | _, .proj _,       _ => (2, 2)
  | _, .comp f gs,    h =>
      have hf  : f.level ≤ 2  := /- from level/comp -/
      have hgs : ∀ i, (gs i).level ≤ 2 := /- ditto -/
      let p_f  := KMor1.majorize f hf
      let r_g  := Fin.foldr _ (fun i acc =>
                    max acc
                      (KMor1.majorize (gs i) (hgs i)).1) 0
      let o_g  := Fin.foldr _ (fun i acc =>
                    max acc
                      (KMor1.majorize (gs i) (hgs i)).2) 0
      (p_f.1 + r_g, p_f.2 + o_g)
  | _, .raise f,      h =>
      have hf : f.level ≤ 1 := /- raise adds 1 to level -/
      let p := KMor1.majorize_one f hf
      (2, p.2 + p.1 + 2)
  | _, .simrec _ h_fam g_fam, hyp =>
      have hh : ∀ j, (h_fam j).level ≤ 1 :=
        /- simrec adds 1 to max-children -/
      have hg : ∀ j, (g_fam j).level ≤ 1 :=
        /- ditto -/
      let r_H := Fin.foldr _ (fun j acc =>
                   max acc
                     (KMor1.majorize_one (h_fam j) (hh j)).1) 0
      let o_H := Fin.foldr _ (fun j acc =>
                   max acc
                     (KMor1.majorize_one (h_fam j) (hh j)).2) 0
      let r_G := Fin.foldr _ (fun j acc =>
                   max acc
                     (KMor1.majorize_one (g_fam j) (hg j)).1) 0
      let o_G := Fin.foldr _ (fun j acc =>
                   max acc
                     (KMor1.majorize_one (g_fam j) (hg j)).2) 0
      (2, r_H + r_G + o_H + o_G + 2)
```

The simrec offset matches master design lines 1051–1053
(`offset_2 := r_H + r_G + 2`), with `o_H + o_G` additionally
accumulating the children's offsets.  The implementer
may discover during proof that a slightly different
offset value works; per §1.3 the precise value is
flexible as long as the dominance theorem closes.

## §6 K^sim majorization theorems

### §6.1 `KMor1.majorize_by_A_one_iter`

```lean
/-- Level-≤1 majorization (Tourlakis 2018 §0.1.0.10
restricted to level 1).  Master design §3.4
(parenthetical at line 933). -/
theorem KMor1.majorize_by_A_one_iter
    {a : ℕ} (f : KMor1 a) (h : f.level ≤ 1)
    (v : Fin a → ℕ) :
    f.interp v ≤
      (ERMor1.A_one_iter
        (KMor1.majorize_one f h).1).interp
          ![vMax v + (KMor1.majorize_one f h).2]
```

Proof: rewrite RHS via `interp_A_one_iter`, unfold
`majorize_one` to expose the `(c, d)` from
`KMor1.linearBound`, apply `KMor1.linearBound_dominates`
(existing) to get `f.interp v ≤ c · vMax v + d`, then γ.1
to bound by `A_1^r`.

### §6.2 `KMor1.simrecVec_le_A_one_iter`

```lean
/-- Closed-form bound on simrecVec: every component at
step `n` is dominated by an `A_1`-iter applied to
`max(n, vMax params)`, with iteration count linear in `n`.
Master design §3.4 lines 985–1007 (the `M_n` closed-form
inductive proof on `n`).  Tourlakis 2018 §0.1.0.10
proof of the level-2 case. -/
theorem KMor1.simrecVec_le_A_one_iter
    {a k : ℕ}
    (h_fam : Fin (k + 1) → KMor1 a)
    (g_fam : Fin (k + 1) → KMor1 (a + 1 + (k + 1)))
    (hh : ∀ j, (h_fam j).level ≤ 1)
    (hg : ∀ j, (g_fam j).level ≤ 1)
    (r_H o_H r_G o_G : ℕ)
    (hbase : ∀ j x,
      (h_fam j).interp x
        ≤ (ERMor1.A_one_iter r_H).interp ![vMax x + o_H])
    (hstep : ∀ j y,
      (g_fam j).interp y
        ≤ (ERMor1.A_one_iter r_G).interp ![vMax y + o_G])
    (params : Fin a → ℕ) (n : ℕ) :
    ∀ j,
      KMor1.simrecVec h_fam g_fam params n j
        ≤ (ERMor1.A_one_iter (r_H + n * r_G)).interp
            ![max n (vMax params) + o_H + n * o_G]
```

Proof: induction on `n`, mirroring master design lines
985–1007.

- **Base (n = 0)**: `simrecVec ... 0 j = (h_fam j).interp params`.
  Apply `hbase j params`.  Conclude via
  `vMax params ≤ max 0 (vMax params)` and trivial 0
  arithmetic.
- **Step (n → n+1)**: by IH, every entry of `simrecVec ... n`
  is bounded by an iterate of `A_1` at exponent
  `r_H + n · r_G` applied to `max n (vMax params) + o_H + n · o_G`.
  The step computes `(g_fam j).interp` of the concatenated
  context (counter, params, prev-component slots).  Bound
  vMax of that concatenated context by IH and `n ≤ max (n+1) ...`.
  Apply `hstep j`.  Compose with IH via `A_one_iter_compose`.
  Fold terms into the desired form
  `max (n+1) (vMax params) + o_H + (n+1) · o_G`.

The succ-case proof is the largest single proof in the
cycle.  Per §9.2.4, factor into named sub-lemmas
(`simrecVec_step_input_bound`, `step_dominance_apply`,
etc.) for tractability.

### §6.3 `KMor1.majorize_by_A_two_iter`

```lean
/-- Level-≤2 majorization (Tourlakis 2018 §0.1.0.10).
Master design §3.4 lines 916–937. -/
theorem KMor1.majorize_by_A_two_iter
    {a : ℕ} (f : KMor1 a) (h : f.level ≤ 2)
    (v : Fin a → ℕ) :
    f.interp v ≤
      (ERMor1.A_two_iter
        (KMor1.majorize f h).1).interp
          ![vMax v + (KMor1.majorize f h).2]
```

Proof: structural induction on `f`, mirroring
`KMor1.majorize`'s `def` cases:

- **`zero`/`proj`/`succ`**: unfold `majorize` to `(2, ·)`,
  rewrite RHS to `tower 2 (vMax v + ·)`, dominate the LHS
  by the explicit small constant via `self_le_tower` plus
  `omega`.
- **`comp`**: apply IH to `f` and each `gs i`; take maxes
  via `Fin.foldr_max_ge` (existing in
  `LawvereKSimPolynomialBound.lean`); compose two
  `tower r₁`/`tower r₂` bounds via `tower_comp` and
  `tower_mono_right` (Auxiliary lemma
  `tower_compose_offsets` per §6.4).
- **`raise`**: from `(raise f).level ≤ 2` derive
  `f.level ≤ 1`.  Apply `majorize_by_A_one_iter` to `f`
  to get an `A_1^k`-bound; convert via
  `A_one_iter_le_A_two_iter_two` (γ corollary).
  `(raise f).interp = f.interp` (per `interp_raise`)
  transfers the bound directly.
- **`simrec`**: apply `simrecVec_le_A_one_iter` (§6.2) to
  bound every component.  Specialize at `n = v 0`.
  Bound `n` by `vMax v`.  Convert the `A_1^{linear-in-n}`
  bound to `A_2^2(linear-in-input)` via
  `A_one_iter_le_A_two_iter_two`.  Collect into
  `tower 2 (vMax v + r_H + r_G + o_H + o_G + 2)`.

### §6.4 Auxiliary lemmas

Small support lemmas, file-local:

- `vMax_apply_le {a} (v : Fin a → ℕ) (i : Fin a) :
  v i ≤ vMax v` — one-line `Finset.le_sup`.
- `vMax_le_of_pointwise {a} (v : Fin a → ℕ) (M : ℕ) :
  (∀ i, v i ≤ M) → vMax v ≤ M` — `Finset.sup_le`.
- `vMax_cons {a} (n : ℕ) (v : Fin a → ℕ) :
  vMax (Fin.cons n v) = max n (vMax v)` — by manual
  unfolding or mathlib's `Fin.sup_cons`-style lemma if
  available.  Per §9.2.6, fall back to manual induction
  if no direct mathlib lemma applies.
- `tower_compose_offsets (a b x c d : ℕ) :
  tower a (tower b (x + c) + d) ≤ tower (a + b) (x + c + d)`
  — used in the comp case.  Pure tower arithmetic via
  `tower_comp` and `tower_mono_right`.

## §7 Step-5 bridge lemma

```lean
/-- Step-5 plug-in: combines `majorize_by_A_two_iter` with
`sumCtxERPlusOffset` to produce the dominance hypothesis
shape that `ERMor1.simultaneousBoundedRec_interp_correct`
consumes.  Master design §3.5 lines 1099–1116 (the kToER
simrec componentBound construction). -/
theorem KMor1.majorize_by_componentBound
    {a : ℕ} (f : KMor1 a) (h : f.level ≤ 2)
    (v : Fin a → ℕ) :
    let p := KMor1.majorize f h
    f.interp v ≤
      (ERMor1.comp (ERMor1.A_two_iter p.1)
        ![ERMor1.sumCtxERPlusOffset a p.2]).interp v
```

Proof: unfold via `interp_comp`, `interp_A_two_iter`,
`interp_sumCtxERPlusOffset`.  RHS becomes
`tower (majorize.1) ((∑ i, v i) + majorize.2)`.  LHS
bounded by `tower (majorize.1) (vMax v + majorize.2)`
(from `majorize_by_A_two_iter` plus
`interp_A_two_iter`).  Chain via `vMax_le_sumCtxER` and
`tower_mono_right`.  Three-to-four-line `calc`.

## §8 Tests

### §8.1 `GebLeanTests/LawvereKSimMajorization.lean`

```lean
import GebLean.LawvereKSimMajorization

namespace GebLean

/-- Level-1 simrec witness: addK = simrec_0 base=proj
step=succ(prev). -/
private def addK : KMor1 2 :=
  KMor1.simrec (a := 1) (k := 0) ⟨0, by decide⟩
    (fun _ => KMor1.proj 0)
    (fun _ => KMor1.comp KMor1.succ
                fun _ : Fin 1 =>
                  KMor1.proj ⟨2, by decide⟩)

example : addK.level ≤ 1 := by decide
example : addK.level = 1 := by decide

-- Atomic majorize_one witnesses: offset = 0, r ≥ 1.
#guard (KMor1.majorize_one (KMor1.zero (n := 1))
          (by decide)).2 = 0
#guard (KMor1.majorize_one (KMor1.proj (0 : Fin 2))
          (by decide)).2 = 0
#guard (KMor1.majorize_one KMor1.succ (by decide)).2 = 0

-- addK exercises level-1 simrec: r positive, offset 0.
#guard (KMor1.majorize_one addK (by decide)).1 ≥ 1
#guard (KMor1.majorize_one addK (by decide)).2 = 0

-- Atomic majorize witnesses: r = 2 uniform.
#guard (KMor1.majorize (KMor1.zero (n := 1))
          (by decide)).1 = 2
#guard (KMor1.majorize KMor1.succ (by decide)).1 = 2
#guard (KMor1.majorize (KMor1.proj (0 : Fin 2))
          (by decide)).1 = 2

-- addK exercises level-1 path through `KMor1.majorize`'s
-- raise/comp branches: r still 2.
#guard (KMor1.majorize addK (by decide)).1 = 2

-- Concrete-input dominance: addK.interp ![1, 1] = 2 per
-- existing addK semantics (see GebLeanTests/
-- LawvereKSimInterp.lean).
#guard
  let p := KMor1.majorize addK (by decide)
  addK.interp ![1, 1]
    ≤ (ERMor1.A_two_iter p.1).interp ![max 1 1 + p.2]

-- Atomic dominance: succ.interp ![3] = 4.
#guard
  let p := KMor1.majorize KMor1.succ (by decide)
  KMor1.succ.interp ![3]
    ≤ (ERMor1.A_two_iter p.1).interp ![3 + p.2]

end GebLean
```

ER-side `#guard`s on `A_two_iter r` for `r ≥ 1` rely on
`interp_A_two_iter` (existing simp lemma from step 3)
firing inside `decide`, after which the RHS becomes
`tower 2 (·)` over Nat — `decide`-tractable for tiny
inputs.

### §8.2 Re-exports

Both done at skeleton-creation time:

- `GebLean.lean`: `import GebLean.LawvereKSimMajorization`
  near the other top-level imports (alphabetical).
- `GebLeanTests.lean`:
  `import GebLeanTests.LawvereKSimMajorization` near
  the other test imports.

## §9 Risks and mitigations

### §9.1 `Nat.log 2` slack in γ.1

`Nat.log 2 (c + 1) + 1` overestimates `⌈log_2 (c + 1)⌉` by
up to 1 bit.  The slack is harmless (the bound is still
valid; `r` is just slightly larger than the literature
minimum).  Mitigation: documented in γ.1's docstring;
`#guard`s on `majorize_one` lock down the chosen formula.

### §9.2 Structural recursion termination on `KMor1.majorize`

Lean's structural-recursion checker handles structural
recursion on `KMor1` (which has finite-arity constructors)
without manual termination proofs — the existing
`KMor1.linearBound` and `KMor1.level` defs use the same
pattern.  Mitigation: mirror the `KMor1.linearBound`
definition shape exactly (in particular `Fin.foldr` for
the `comp` and `simrec` children), which is known to
elaborate.

### §9.3 `Fin.foldr` over child majorize results

`KMor1.majorize`'s `comp` and `simrec` cases call
`Fin.foldr` over child majorize-bounds, mirroring
`KMor1.linearBound`'s structure.  Pattern-matched
correctness depends on `Fin.foldr`'s unfolding lemmas
being in scope — `Fin.foldr_max_ge` exists in
`LawvereKSimPolynomialBound.lean` already.  Mitigation:
re-use the existing `Fin.foldr_max_ge` (and add a sister
lemma for the offset slot if needed).

### §9.4 Level-2 simrec iteration arithmetic size

`simrecVec_le_A_one_iter`'s succ-case proof is the largest
single proof in the cycle.  The arithmetic involves
rewriting via `interp_A_one_iter`, applying IH at the
prev-component slots, applying `hstep` at the step
function, composing via `A_one_iter_compose`, and folding
terms.  Mitigation: factor into 3–5 named sub-lemmas
(e.g. `simrecVec_step_input_bound`,
`step_dominance_apply`, etc.) per CLAUDE.md
factor-out-lemmas guidance.  Each sub-lemma is
independently verifiable.  The prose proof (master
design lines 985–1007) gives a step-by-step derivation
the implementation transcribes.

### §9.5 Atomic `r = 2` uniformity vs literature tightness

The literature gives tight bounds at atoms (e.g.
`proj.interp v ≤ vMax v`, exactly `tower 0 (vMax v)`);
this spec uses uniform `r = 2`.  This is over-tight at
atoms but eliminates per-case upcasting at composition
nodes.  The cost is irrelevant to step 5 (which only
consumes the existence of *some* `r`, not its tightness).
Mitigation: documented in §5.2's docstring and
explicitly in §1.3's flexibility list.

### §9.6 `vMax_cons` in the simrec case

The simrec induction needs to relate
`vMax (Fin.cons n params) = max n (vMax params)`.  The
exact form depends on whether mathlib's `Fin.cons`
interacts cleanly with `Finset.univ.sup`.  If not, write
the lemma manually via `Fin.sum_univ_succ`-style
induction over `Fin (a + 1)`.  Mitigation: verify during
implementation; fall back to manual induction.

### §9.7 `markdownlint-cli2` clean

Spec and plan must pass `markdownlint-cli2`.  Mitigation:
run after writing each doc; fix inline.

### §9.8 Step-5 dependency stability

Step 5's `kToER` simrec case will consume
`majorize_by_componentBound` (§7) directly.  If step 5
later discovers it needs a slightly different bound shape
(e.g. a max-of-context rather than sum-of-context bound,
or a different offset arrangement), step 4 may need a
follow-up patch.  Mitigation: master design §3.5 already
prescribes `sumCtxER`-shaped componentBound; the bridge
lemma's signature mirrors that prescription.  Adversarial
review of the step-5 plan will catch any signature
mismatch before step 5 implementation begins.

## §10 Acceptance criteria

A clean build (`lake build` and `lake test`) with no
warnings, no `sorry`, no `admit`, after which:

1. `GebLean/LawvereKSimMajorization.lean` exists with:
   - Private `vMax` abbreviation.
   - `ERMor1.sumCtxER`, `ERMor1.sumCtxERPlusOffset`
     named composites with closed-form `@[simp]` interp
     lemmas and dominance helpers.
   - `linearBound_le_A_one_iter`,
     `A_one_iter_le_two_pow_succ`,
     `two_pow_succ_mul_succ_le_tower_two`,
     `A_one_iter_le_A_two_iter_two`,
     `A_one_iter_compose` cross-family lemmas.
   - `KMor1.majorize_one`, `KMor1.majorize` defs.
   - `KMor1.majorize_by_A_one_iter`,
     `KMor1.simrecVec_le_A_one_iter`,
     `KMor1.majorize_by_A_two_iter` dominance theorems.
   - `KMor1.majorize_by_componentBound` step-5 bridge.
   - Auxiliary lemmas (`vMax_apply_le`,
     `vMax_le_of_pointwise`, `vMax_cons`,
     `tower_compose_offsets`).
   - Module docstring citing Tourlakis 2018 §0.1.0.10
     and master design §3.4 / §3.5.
   - Per-entity docstrings carrying the citations from
     §3 / §4 / §5 / §6 / §7.
2. `GebLeanTests/LawvereKSimMajorization.lean` exists with
   the `#guard`s from §8.1.
3. `GebLean.lean` imports `GebLean.LawvereKSimMajorization`.
4. `GebLeanTests.lean` imports
   `GebLeanTests.LawvereKSimMajorization`.
5. No regressions in existing test surface.
6. `markdownlint-cli2` clean on the spec, plan, and any
   docs touched.
