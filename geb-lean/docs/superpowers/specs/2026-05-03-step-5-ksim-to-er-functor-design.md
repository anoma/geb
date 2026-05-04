# Step 5 — `kToER` structural-recursion functor (master design §3.5)

Spec for cycle 5 of the ER ↔ K^sim_2 categorical-equivalence
formalization (master design:
`docs/research/2026-05-02-er-ksim2-equiv-via-urm-master-design.md`).
This cycle lands the forward functor of the categorical
equivalence: a structural-recursion translation
`kToER : KMor1 a → ERMor1 a` for K^sim morphisms of level ≤ 2,
its correctness theorem `kToER_interp`, the multi-output
companion `kToERN` plus its correctness theorem, and the
categorical functor `kToERFunctor : LawvereKSimDCat 2 ⥤
LawvereERCat`.  All majorization-arithmetic risk was absorbed
in step 4 (`KMor1.majorize_by_A_two_iter`,
`KMor1.majorize_by_componentBound`) and step 2
(`simultaneousBoundedRec_interp_correct`).  Step 5 is
predominantly structural plumbing.

## §1 Status and motivation

### §1.1 Goal

Realize the structural-recursion functor described in master
design §3.5 as the load-bearing forward direction of the ER ↔
K^sim_2 categorical equivalence.  Concretely:

```text
kToER : ∀ {a : ℕ} (f : KMor1 a), f.level ≤ 2 → ERMor1 a
kToER_interp :
  ∀ {a : ℕ} (f : KMor1 a) (h : f.level ≤ 2) (v : Fin a → ℕ),
    (kToER f h).interp v = f.interp v
kToERFunctor : LawvereKSimDCat 2 ⥤ LawvereERCat
```

The simrec case wires `ERMor1.simultaneousBoundedRec` (step 2)
with `KMor1.majorize_by_componentBound` (step 4) to discharge
the dominance hypothesis; no fresh majorization arithmetic at
this layer.

### §1.2 Scope

In scope:

- `GebLean/LawvereKSimER.lean` (new top-level module):
  - `kToER` structural-induction definition.
  - `kToERN` multi-output companion.
  - `kToER_interp` correctness theorem (the universal
    statement assembled from per-case helpers).
  - `kToERN_interp` componentwise correctness.
  - Three named auxiliaries supporting `kToER_interp`'s
    simrec case: `kToER_simrec_dominates`,
    `kToER_simrec_bound_mono`,
    `kToER_interp_simrec` (the simrec case proof, exposed
    as a citable lemma).
  - `kToERN_compat_extEq` Quotient-lift well-definedness
    helper.
  - `kToERFunctor : LawvereKSimDCat 2 ⥤ LawvereERCat` with
    `map_id` and `map_comp` baked in.
- `GebLean/LawvereKSimMajorization.lean` (existing module, one
  added theorem):
  - `KMor1.majorize_simrec_index_indep` — the index-
    independence fact about `KMor1.majorize` at simrec, used
    by `kToER_simrec_dominates`.
- Tests: `GebLeanTests/LawvereKSimER.lean` (Profile Y: Tier 1
  atomic `#guard`s, Tier 2 `addK`-style `example` proof via
  `kToER_interp`, Tier 3 functor sanity).

Opportunistic step-11 helpers (Scope B):

- The implementer may add small helpers that are easier to
  write while the step-5 context is fresh and that step 11
  (the categorical iso) is likely to consume.  Candidates
  include `kToERFunctor_obj_eq : kToERFunctor.obj n = n`,
  `kToERFunctor_map_quot : ⟦kToERN ...⟧ = kToERFunctor.map ⟨..⟩`,
  or compositional rewrites about `kToERFunctor` interacting
  with `KSimMor.includeSucc`.  Any helpers added are
  documented in the docstring of the lemma and noted in
  `.session/workstreams/er-ksim2-equiv-via-urm.md` so step 11
  can find them.  Implementer-discretion; not required.

Out of scope (step 7–10 own):

- `erToK : ERMor1 a → KMor1 a` of level ≤ 2 and `erToKFunctor`
  (URM-simulation chain; master design §4–§9).
- The categorical iso
  `LawvereKSimDCat 2 ≌ LawvereERCat` (step 11).
- A K^sim-side multi-output `KSimMorN` quotient distinct
  from `KMorNQuo n m` (the existing `KMorN` ↔ `KMorNQuo`
  layer is sufficient).

Out of scope and not anyone's job:

- Refactoring or removing `LawvereKSimERDirect.lean` (the
  prior superseded direct-translation effort).  Its docstring
  already marks it as superseded; per CLAUDE.md "never remove
  functionality unprompted", it stays.
- A K^sim-side `kToERN_interp_quot` lemma about quotient
  classes beyond what the functor's well-definedness
  obligation requires.  If step 11 needs more, step 11 builds
  it.

### §1.3 Implementation flexibility vs literature contract

Per CLAUDE.md "Non-negotiable interfaces for categories
formalizing pre-existing mathematical objects": the
mathematical content is fixed by Tourlakis 2018 and master
design; Lean representation choices may flex.

**Literature-fixed (non-negotiable):**

- The translation shape per master design §3.5 lines 1089–
  1116: each K^sim constructor maps to a one-line invocation
  of an ER named composite or `simultaneousBoundedRec`.
- `kToER`'s simrec case routes through
  `ERMor1.simultaneousBoundedRec` with the bound built from
  `ERMor1.A_two_iter` and `ERMor1.sumCtxERPlusOffset`
  (Tourlakis 2018 §0.1.0.34 + §0.1.0.10 chained).
- `kToER_interp` proves Tourlakis 2018 §0.1.0.44 ⊆ direction
  pointwise for level ≤ 2.
- `kToERFunctor` is the forward functor of the categorical
  iso (master design §3 cycle structure: step 5 forward,
  step 10 reverse, step 11 iso).

**Lean-side flexible:**

- Per-case helper-lemma factoring (Factoring R: three named
  simrec-branch helpers).
- Whether the kToER level-discharge `have`s at `comp`,
  `raise`, and `simrec` use the same tactic shape as step
  4's `KMor1.majorize` (recommended for consistency, but
  not mandatory).
- Whether the functor's `map_id` / `map_comp` close by
  `rfl` or fall back to `Quotient.sound`-and-compute.
  Both equally acceptable; implementer chooses based on
  what works.

## §2 Architectural pivot inheritance

This step inherits master design's architectural pivot
(`docs/research/2026-05-02-ksim-to-er-architectural-pivot-handoff.md`)
from the prior `kToERDirect` approach.  In the new approach,
all level-2 dominance is handled outside `kToER` (steps 2 and
4); `kToER` itself is a clean structural recursion with
`simultaneousBoundedRec` at the simrec node.  The prior
`LawvereKSimERDirect.lean` (119 lines) survives as an opt-out
reference but is not consumed by step 5 or any later step.

The "victory lap" claim: with steps 2 + 4 in place, step 5's
total proof obligation is:

1. Per-constructor `kToER` clause (atomic / comp / raise /
   simrec) — definitional or one-line.
2. Per-constructor `kToER_interp` clause — definitional for
   atoms; one-line + IH for comp + raise; ~20–30 lines for
   simrec via three named auxiliaries.
3. Per-component `kToERN` and its interp — pointwise lift,
   ~5 lines.
4. `kToERFunctor` morphism map well-definedness — Quotient
   lift over depth_witness, well-definedness via
   `kToERN_compat_extEq` + `Quotient.exact`.
5. Functor laws — `rfl` or `Quotient.sound` + 5–10 lines.

Total expected file size ~250–400 lines for
`LawvereKSimER.lean` (vs step 4's `LawvereKSimMajorization.lean`
at 935 lines).

## §3 Module file layout

### §3.1 Files added / edited

```text
GebLean/LawvereKSimInterp.lean                       [step 5 ADDS]
  KMor1.simrecVec_eq_Nat_simRecVec
    -- Bridges KMor1's K^sim-side simrec interpreter to the
    -- Nat-side flatten consumed by step 2's
    -- simultaneousBoundedRec_interp_correct.  Proved by
    -- induction on the iteration counter (~15 lines: base
    -- case rfl, step case rewrites the dite-based stepCtx
    -- to Fin.append-based form, mirroring the existing
    -- private interp_simrec_eq_simrecVec proof at lines
    -- 121-155 of LawvereKSimInterp.lean).

GebLean/LawvereKSimMajorization.lean                 [step 5 ADDS]
  KMor1.majorize_simrec_index_indep
    -- One-line lemma; proof is rfl-or-fallback per §6.1.1.
    -- Asserts KMor1.majorize at simrec ignores the output
    -- index argument.
  ERMor1.sumCtxER_cons_le_of_le
    -- Default plan: add it at task time (§6.1.3 needs it
    -- for the bound-monotonicity proof; no analogous
    -- Fin.foldr lemma is currently in the codebase).  Skip
    -- only if the implementer finds an inline-clean tactic
    -- (e.g. via Fin.foldr_succ + omega) that does not
    -- require the helper.

GebLean/LawvereKSimER.lean                           [step 5 NEW]
  kToER, kToERN, kToER_interp, kToERN_interp,
  kToER_simrec_dominates, kToER_simrec_bound_mono,
  kToER_interp_simrec, kToERN_compat_extEq, kToERFunctor.
  Optional opportunistic step-11 helpers (Scope B).

GebLean.lean                                         [step 5 EDITS]
  Add `import GebLean.LawvereKSimER` (alphabetically
  between `LawvereKSim*` siblings).

GebLeanTests/LawvereKSimER.lean                      [step 5 NEW]
  Tier 1 atomic #guard tests.
  Tier 2 universal-theorem `example` proofs (with an
    inline-constructed addK : KMor1 2; see §9.2).
  Tier 3 kToERFunctor sanity checks.

GebLeanTests.lean                                    [step 5 EDITS]
  Add `import GebLeanTests.LawvereKSimER`
  (alphabetically).
```

### §3.2 `LawvereKSimER.lean` import set

The new module's import header (alphabetised):

```lean
import GebLean.LawvereER
import GebLean.LawvereERQuot
import GebLean.LawvereKSim
import GebLean.LawvereKSimInterp
import GebLean.LawvereKSimMajorization
import GebLean.LawvereKSimQuot
import GebLean.Utilities.ERAMajorants
import GebLean.Utilities.ERSimultaneousBoundedRec
```

Some of these are pulled transitively (e.g.,
`LawvereERBoundComputable` via `LawvereKSimMajorization`),
so the implementer prunes per `lean_unused_imports` /
mathlib lints.  The set above is the explicit minimum
required to name every API consumed in §§4–8.

## §4 The structural recursion `kToER`

### §4.1 Public signature

```lean
def kToER : ∀ {a : ℕ} (f : KMor1 a), f.level ≤ 2 → ERMor1 a
```

Citation: master design §3.5 lines 1089–1116.

### §4.2 Per-constructor cases

```lean
| _, .zero,         _ => ERMor1.zeroN _
| _, .succ,         _ => ERMor1.succ
| _, .proj i,       _ => ERMor1.proj i
| _, .comp f gs,    h =>
    have hf  : f.level ≤ 2 :=
      le_trans (le_max_left _ _) h
    have hgs : ∀ i, (gs i).level ≤ 2 := fun i =>
      le_trans
        (Finset.le_sup
          (f := fun j => (gs j).level)
          (Finset.mem_univ i))
        (le_trans (le_max_right _ _) h)
    ERMor1.comp (kToER f hf)
      (fun i => kToER (gs i) (hgs i))
| _, .raise f,      h =>
    have hf : f.level ≤ 2 := by
      unfold KMor1.level at h; omega
    kToER f hf
| _, .simrec (a := a) (k := k) i h_fam g_fam, hyp =>
    have h_h : ∀ j, (h_fam j).level ≤ 2 := fun j => by
      have h1 : (h_fam j).level ≤ 1 :=
        le_trans
          (Finset.le_sup
            (f := fun l => (h_fam l).level)
            (Finset.mem_univ j))
          (le_trans (le_max_left _ _)
            (Nat.le_of_succ_le_succ
              (by unfold KMor1.level at hyp; exact hyp)))
      omega
    have h_g : ∀ j, (g_fam j).level ≤ 2 := fun j => by
      have h1 : (g_fam j).level ≤ 1 :=
        le_trans
          (Finset.le_sup
            (f := fun l => (g_fam l).level)
            (Finset.mem_univ j))
          (le_trans (le_max_right _ _)
            (Nat.le_of_succ_le_succ
              (by unfold KMor1.level at hyp; exact hyp)))
      omega
    let bases : Fin (k + 1) → ERMor1 a :=
      fun j => kToER (h_fam j) (h_h j)
    let steps : Fin (k + 1) → ERMor1 (a + 1 + (k + 1)) :=
      fun j => kToER (g_fam j) (h_g j)
    let p : ℕ × ℕ :=
      KMor1.majorize (.simrec i h_fam g_fam) hyp
    let bound : ERMor1 (a + 1) :=
      ERMor1.comp (ERMor1.A_two_iter p.1)
        ![ERMor1.sumCtxERPlusOffset (a + 1) p.2]
    ERMor1.simultaneousBoundedRec k a bases steps bound i
```

### §4.3 Why `sumCtxERPlusOffset (a + 1) p.2` (not `sumCtxER (a+1)`)

Master design's pseudocode at line 1107 used `sumCtxER (a+1)`
without offset.  Step 4's bridge lemma
`KMor1.majorize_by_componentBound` provides the actual usable
shape: a bound built from `ERMor1.comp (A_two_iter p.1)
![ERMor1.sumCtxERPlusOffset a p.2]`, where `p.2` is the
`offset` extracted from `KMor1.majorize`.  Specialised at the
simrec branch (outer arity `a + 1`), this becomes
`sumCtxERPlusOffset (a + 1) p.2`.  The offset is non-zero
in general (e.g. `(2, 2)` for atomic constructors,
`(2, r_H + r_G + 2)` for simrec), so omitting it would break
step 4's bridge.

### §4.4 Termination

`kToER` is structurally recursive on the `KMor1` term — each
recursive call passes a strictly-smaller subterm.  Lean's
equation compiler handles this without a `decreasing_by`
annotation in the expected case.  If the equation compiler
needs help (e.g. because `KMor1`'s well-founded measure does
not auto-propagate through the `let bases` / `let steps`
binders), fall back to `termination_by f => f` or to
`termination_by structurally f`.

## §5 The `kToER_interp` correctness theorem

### §5.1 Public signature

```lean
theorem kToER_interp :
    ∀ {a : ℕ} (f : KMor1 a) (h : f.level ≤ 2)
      (v : Fin a → ℕ),
    (kToER f h).interp v = f.interp v
```

Citation: master design §3.5 lines 1130–1147; realises
Tourlakis 2018 §0.1.0.44 ⊆ direction pointwise for level ≤ 2.

### §5.2 Proof shape

Structural induction on `f`, dispatching to per-case helpers.

- Atomic cases (`zero`, `succ`, `proj`): definitional unfolding
  of named composite interps; closed by `simp only` or `rfl`
  on the corresponding `@[simp]` interp lemmas
  (`ERMor1.interp_zeroN`, `ERMor1.interp_succ`,
  `ERMor1.interp_proj`).
- `comp` case: unfold `kToER`'s comp branch;
  `ERMor1.interp_comp` rewrites the LHS;
  `KMor1.interp_comp` rewrites the RHS; recursive IH on `f`
  and `gs i` closes by `funext` + congruence.
- `raise` case: kToER passes through (`kToER (.raise f) h
  = kToER f hf`); `KMor1.interp_raise` reduces RHS to
  `f.interp`; recursive IH closes.
- `simrec` case: delegated to `kToER_interp_simrec` (§6).

### §5.3 Pseudocode

```lean
theorem kToER_interp
    {a : ℕ} (f : KMor1 a) (h : f.level ≤ 2)
    (v : Fin a → ℕ) :
    (kToER f h).interp v = f.interp v := by
  induction f with
  | zero => rfl  -- or simp [kToER, KMor1.interp_zero]
  | succ => rfl
  | proj i => rfl
  | comp f gs ih_f ih_gs =>
      simp only [kToER, KMor1.interp_comp, ERMor1.interp_comp]
      congr 1
      funext i
      exact ih_gs i ...
      -- and apply ih_f to the outer call
  | simrec i h_fam g_fam ih_h ih_g =>
      -- The IHs from `induction` over KMor1.simrec produce
      -- ih_h : ∀ j, (kToER (h_fam j) (h_h j)).interp = ...
      -- where h_h is the level-derivation in scope.  Pass
      -- to kToER_interp_simrec via a level-irrelevance
      -- adapter that re-quantifies over the level proof.
      exact kToER_interp_simrec i h_fam g_fam h v
        (fun j h' v' => by
          rw [show kToER (h_fam j) h' = kToER (h_fam j) _
              from rfl]
          exact ih_h j v')
        (fun j h' v' => by
          rw [show kToER (g_fam j) h' = kToER (g_fam j) _
              from rfl]
          exact ih_g j v')
  | raise f ih =>
      simp only [kToER, KMor1.interp_raise]
      exact ih ...
```

(Implementer adapts the recursor's per-case binder list and
hypothesis names to Lean 4's induction-on-`KMor1` shape.)

## §6 The simrec case: load-bearing proof

### §6.1 The bridge lemma `KMor1.simrecVec_eq_Nat_simRecVec`

`simultaneousBoundedRec_interp_correct` (step 2) consumes a
hypothesis using `Nat.simRecVec` (the value-side simultaneous
recursion); `KMor1.interp_simrec` rewrites the K^sim simrec
interp into `KMor1.simrecVec` form (which uses
`KMor1.interp` calls inline).  Bridging these two forms is
needed at multiple points in §6 and is therefore extracted
as its own lemma in `LawvereKSimInterp.lean`.

```lean
theorem KMor1.simrecVec_eq_Nat_simRecVec {a k : ℕ}
    (h : Fin (k + 1) → KMor1 a)
    (g : Fin (k + 1) → KMor1 (a + 1 + (k + 1)))
    (params : Fin a → ℕ) (n : ℕ) (j : Fin (k + 1)) :
    KMor1.simrecVec h g params n j
      = Nat.simRecVec k a
          (fun j' => (h j').interp)
          (fun j' => (g j').interp) n params j := by
  -- Induction on n.
  -- Base case (n = 0): rfl by definitional unfolding.
  -- Step case: KMor1.simrecVec uses an inline `dite`-based
  -- stepCtx; Nat.simRecVec uses `Fin.append (Fin.cons n x)`.
  -- The same equivalence already proved (privately) for
  -- KMor1.interp_simrec_eq_simrecVec at lines 121-155 of
  -- LawvereKSimInterp.lean — replicate that proof shape.
  --
  -- Proof skeleton (~25-40 lines, mirroring the existing
  -- private proof; "~15 lines" was an under-estimate).
  -- The IH must be quantified over the output index `j` so
  -- the step case can apply the IH componentwise to the
  -- previous-iter vector inside `Fin.append`:
  --
  --   intro n
  --   induction n with
  --   | zero => intro j; rfl
  --   | succ n ih =>
  --       intro j
  --       -- Step case: `KMor1.simrecVec` uses an inline
  --       -- `dite`-based stepCtx; `Nat.simRecVec` uses
  --       -- `Fin.append (Fin.cons n params) ...`.  Bridge:
  --       -- congr 1; funext idx; by_cases idx.val < a + 1;
  --       --   inner branch routes to (Fin.cons n params)
  --       --     via Fin.cons_zero / Fin.cons_succ;
  --       --   outer branch routes to ih via
  --       --     `congr_fun ih ⟨idx.val - (a + 1), ...⟩`.
  ...
```

Citation: master design §3.5; bridging step.

### §6.2 The four Factoring R helpers

#### §6.2.1 `KMor1.majorize_simrec_index_indep` (placement: `LawvereKSimMajorization.lean`)

```lean
theorem KMor1.majorize_simrec_index_indep
    {a k : ℕ}
    (i j : Fin (k + 1))
    (h_fam : Fin (k + 1) → KMor1 a)
    (g_fam : Fin (k + 1) → KMor1 (a + 1 + (k + 1)))
    (h_i : (KMor1.simrec i h_fam g_fam).level ≤ 2)
    (h_j : (KMor1.simrec j h_fam g_fam).level ≤ 2) :
    KMor1.majorize (KMor1.simrec i h_fam g_fam) h_i
      = KMor1.majorize (KMor1.simrec j h_fam g_fam) h_j := by
  -- Default plan: simp only [KMor1.majorize] followed by
  -- rfl.  Reason: KMor1.majorize's simrec branch (line 632
  -- of LawvereKSimMajorization.lean) returns
  -- (2, r_H + r_G + 2) without referencing the index (the
  -- constructor argument is bound to `_` in the `match`
  -- pattern); the simp unfolds the match, the rfl closes
  -- after proof-irrelevance for the level-discharge `have`s.
  simp only [KMor1.majorize]
```

If even the `simp only` is not enough (e.g., because the
internal `Fin.foldr`-based `r_H` / `r_G` computation does
not reduce through proof-irrelevance), prove via term-mode
construction by hand: extract `(2, r_H + r_G + 2)` directly
from both sides.  The implementer verifies via lean-lsp at
task time.

Citation: master design §3.5 + §3.4 (Tourlakis 0.1.0.10's
level-2 `r_2 = 2`, `offset_2 = r_H + r_G + 2`).

#### §6.2.2 `kToER_simrec_dominates`

The dominance hypothesis `simultaneousBoundedRec_interp_correct`
consumes is over the families *passed to `simultaneousBoundedRec`*
— at the kToER simrec branch, those are the kToER-translated
`bases` / `steps`, not the K^sim originals.  This helper
states the dominance directly in that shape, taking the
inductive hypotheses (kToER preserves interp on each child)
as explicit hypotheses to handle the IH-mediated rewrite
internally.

```lean
theorem kToER_simrec_dominates
    {a k : ℕ}
    (i : Fin (k + 1))
    (h_fam : Fin (k + 1) → KMor1 a)
    (g_fam : Fin (k + 1) → KMor1 (a + 1 + (k + 1)))
    (hyp : (KMor1.simrec i h_fam g_fam).level ≤ 2)
    (h_h : ∀ j, (h_fam j).level ≤ 2)
    (h_g : ∀ j, (g_fam j).level ≤ 2)
    (ih_h : ∀ (j : Fin (k + 1))
             (h' : (h_fam j).level ≤ 2)
             (v' : Fin a → ℕ),
       (kToER (h_fam j) h').interp v' = (h_fam j).interp v')
    (ih_g : ∀ (j : Fin (k + 1))
             (h' : (g_fam j).level ≤ 2)
             (v' : Fin (a + 1 + (k + 1)) → ℕ),
       (kToER (g_fam j) h').interp v' = (g_fam j).interp v')
    (n : ℕ) (x : Fin a → ℕ) :
    let p :=
      KMor1.majorize (.simrec i h_fam g_fam) hyp
    let bound : ERMor1 (a + 1) :=
      ERMor1.comp (ERMor1.A_two_iter p.1)
        ![ERMor1.sumCtxERPlusOffset (a + 1) p.2]
    ∀ (m : ℕ), m ≤ n → ∀ (j : Fin (k + 1)),
      Nat.simRecVec k a
          (fun j' => (kToER (h_fam j') (h_h j')).interp)
          (fun j' => (kToER (g_fam j') (h_g j')).interp)
          m x j
        ≤ bound.interp (Fin.cons m x) := by
  intro p bound m _ j
  -- Step 1: Use IHs to rewrite the kToER-translated families
  -- back to the K^sim-side ones.
  have h_bases :
      (fun j' => (kToER (h_fam j') (h_h j')).interp)
        = (fun j' => (h_fam j').interp) := by
    funext j' v'; exact ih_h j' (h_h j') v'
  have h_steps :
      (fun j' => (kToER (g_fam j') (h_g j')).interp)
        = (fun j' => (g_fam j').interp) := by
    funext j' v'; exact ih_g j' (h_g j') v'
  rw [h_bases, h_steps]
  -- Step 2: Bridge Nat.simRecVec to KMor1.simrecVec.
  rw [← KMor1.simrecVec_eq_Nat_simRecVec h_fam g_fam x m j]
  -- Step 3: Bridge KMor1.simrecVec back to
  -- (.simrec j h_fam g_fam).interp via reverse of
  -- KMor1.interp_simrec.  The reverse uses the equality
  -- (Fin.cons m x) 0 = m and (fun j' => (Fin.cons m x)
  -- (Fin.succ j')) = x, both rfl-or-simp.
  have h_rev :
      KMor1.simrecVec h_fam g_fam x m j
        = (KMor1.simrec j h_fam g_fam).interp
            (Fin.cons m x) := by
    rw [KMor1.interp_simrec]
    -- Empirically: bare `congr 2` closes both residual
    -- goals; `(Fin.cons m x) 0` reduces to `m` and
    -- `(fun j' => (Fin.cons m x) (Fin.succ j'))` reduces
    -- to `x` by `Fin.cons`'s computation rules without
    -- explicit simp.  Adding `<;> simp [Fin.cons_zero,
    -- Fin.cons_succ]` would trigger the unused-tactic
    -- linter under the project's `warningAsError = true`.
    -- If the bare `congr 2` leaves residual goals at task
    -- time, fall back to `congr 1; · ...; · funext j';
    -- exact Fin.cons_succ ...` per residual.
    congr 2
  rw [h_rev]
  -- Step 4: Apply majorize_by_componentBound at index j.
  have h_j : (KMor1.simrec j h_fam g_fam).level ≤ 2 := by
    -- KMor1.level at simrec ignores the index; both
    -- (.simrec j h_fam g_fam).level and (.simrec i h_fam
    -- g_fam).level reduce to the same expression.
    show _ ≤ 2
    simp only [KMor1.level]
    have := hyp
    simp only [KMor1.level] at this
    exact this
  have h_dom :=
    KMor1.majorize_by_componentBound
      (.simrec j h_fam g_fam) h_j (Fin.cons m x)
  -- Step 5: Use index-independence to identify the bound at
  -- index j with `bound` (built from the index-i majorize).
  rw [KMor1.majorize_simrec_index_indep j i h_fam g_fam
        h_j hyp] at h_dom
  exact h_dom
```

Citation: master design §3.5 + §3.4 (Tourlakis 0.1.0.10
level-2 majorization); §0.1.0.34 (bounded-recursion closure
the bridge corresponds to).

#### §6.2.3 `kToER_simrec_bound_mono`

```lean
theorem kToER_simrec_bound_mono
    {a k : ℕ}
    (i : Fin (k + 1))
    (h_fam : Fin (k + 1) → KMor1 a)
    (g_fam : Fin (k + 1) → KMor1 (a + 1 + (k + 1)))
    (hyp : (KMor1.simrec i h_fam g_fam).level ≤ 2)
    (n : ℕ) (x : Fin a → ℕ) :
    let p :=
      KMor1.majorize (.simrec i h_fam g_fam) hyp
    let bound : ERMor1 (a + 1) :=
      ERMor1.comp (ERMor1.A_two_iter p.1)
        ![ERMor1.sumCtxERPlusOffset (a + 1) p.2]
    ∀ (m : ℕ), m ≤ n →
      bound.interp (Fin.cons m x)
        ≤ bound.interp (Fin.cons n x) := by
  intro p bound m h_m_le_n
  simp only [bound, ERMor1.interp_comp,
    ERMor1.interp_A_two_iter,
    ERMor1.interp_sumCtxERPlusOffset,
    Matrix.cons_val_zero]
  -- Goal:
  -- tower p.1 ((sumCtxER (a+1)).interp (Fin.cons m x) + p.2)
  --   ≤ tower p.1 ((sumCtxER (a+1)).interp (Fin.cons n x) + p.2)
  apply tower_mono_right
  apply Nat.add_le_add_right
  exact ERMor1.sumCtxER_cons_le_of_le x h_m_le_n
```

The supporting helper, added to
`LawvereKSimMajorization.lean` near `interp_sumCtxER` /
`vMax_cons`:

```lean
theorem ERMor1.sumCtxER_cons_le_of_le {a : ℕ} (x : Fin a → ℕ)
    {m n : ℕ} (h : m ≤ n) :
    (ERMor1.sumCtxER (a + 1)).interp (Fin.cons m x)
      ≤ (ERMor1.sumCtxER (a + 1)).interp (Fin.cons n x) := by
  rw [ERMor1.interp_sumCtxER, ERMor1.interp_sumCtxER]
  -- (sumCtxER (a+1)).interp ctx evaluates to a Fin.foldr
  -- over (fun i acc => acc + ctx i).  The two foldrs
  -- differ only at index 0 (where Fin.cons m x = m,
  -- Fin.cons n x = n) and agree on every other index
  -- (where both reduce to x via Fin.cons_succ).
  --
  -- Proof strategy (10-15 lines):
  --
  -- 1. Generalize the foldr's initial accumulator (which
  --    is 0) to an arbitrary `acc₀` so the induction
  --    hypothesis stays applicable across nested folds.
  -- 2. Prove a small `Fin.foldr` monotonicity-in-acc
  --    lemma: for fixed body f, if acc₁ ≤ acc₂ then
  --    Fin.foldr n f acc₁ ≤ Fin.foldr n f acc₂.
  -- 3. Show that for any acc₀ and any context that
  --    agrees with `Fin.cons m x` on indices ≥ 1, the
  --    Fin.foldr value at the (a+1)-arity context
  --    differs from the corresponding (a+1)-arity
  --    Fin.cons n x foldr only by the slot-0
  --    accumulator increment (m vs n).
  -- 4. Apply with `m ≤ n` to close.
  --
  -- An alternative path: rewrite both sides via a
  -- `sumCtxER_cons_eq` lemma that explicitly factors as
  -- `(Fin.cons m x slot 0) + (sumCtxER a).interp x`, then
  -- close with `Nat.add_le_add_right` and `m ≤ n`.  Step 4
  -- uses an analogous shape for `vMax_cons` (line 875 of
  -- LawvereKSimMajorization.lean).  Implementer adopts
  -- whichever shape composes more cleanly with the
  -- existing `Fin.foldr_succ` / `Fin.foldr_succ_last`
  -- lemma names in current mathlib.
  _  -- task-time hole; closes per the strategy above
```

The pseudocode body intentionally elides the detailed
tactic shape because mathlib's `Fin.foldr_succ`-side lemma
names have shifted across recent versions and the
implementer should use `lean_local_search` / `lean_loogle`
at task time to find the current names.  The proof
mathematics is unambiguous; the Lean realisation is
implementer-discretion within the documented strategy.

Citation: master design §3.5; transitively step 4
`sumCtxERPlusOffset` (step 4 §3.5 lines 116-121).

#### §6.2.4 `kToER_interp_simrec` (assembly)

The IH arguments bind the level proof `h'` explicitly so
the theorem's signature does not reference any `kToER`
local `have` not in scope.

```lean
theorem kToER_interp_simrec
    {a k : ℕ}
    (i : Fin (k + 1))
    (h_fam : Fin (k + 1) → KMor1 a)
    (g_fam : Fin (k + 1) → KMor1 (a + 1 + (k + 1)))
    (h : (KMor1.simrec i h_fam g_fam).level ≤ 2)
    (v : Fin (a + 1) → ℕ)
    (ih_h : ∀ (j : Fin (k + 1))
             (h' : (h_fam j).level ≤ 2)
             (v' : Fin a → ℕ),
       (kToER (h_fam j) h').interp v' = (h_fam j).interp v')
    (ih_g : ∀ (j : Fin (k + 1))
             (h' : (g_fam j).level ≤ 2)
             (v' : Fin (a + 1 + (k + 1)) → ℕ),
       (kToER (g_fam j) h').interp v' = (g_fam j).interp v') :
    (kToER (.simrec i h_fam g_fam) h).interp v
      = (KMor1.simrec i h_fam g_fam).interp v := by
  -- Reconstruct the level-discharge h_h, h_g locally so the
  -- proof body matches kToER's simrec-branch shape.
  have h_h : ∀ j, (h_fam j).level ≤ 2 := fun j => by
    have h1 : (h_fam j).level ≤ 1 :=
      le_trans
        (Finset.le_sup
          (f := fun l => (h_fam l).level)
          (Finset.mem_univ j))
        (le_trans (le_max_left _ _)
          (Nat.le_of_succ_le_succ
            (by unfold KMor1.level at h; exact h)))
    omega
  have h_g : ∀ j, (g_fam j).level ≤ 2 := fun j => by
    have h1 : (g_fam j).level ≤ 1 :=
      le_trans
        (Finset.le_sup
          (f := fun l => (g_fam l).level)
          (Finset.mem_univ j))
        (le_trans (le_max_right _ _)
          (Nat.le_of_succ_le_succ
            (by unfold KMor1.level at h; exact h)))
    omega
  -- Step 1: cons/tail-shape v.
  set n := v 0
  set x := Fin.tail v
  have hv : v = Fin.cons n x := (Fin.cons_self_tail v).symm
  rw [hv]
  -- Step 2: unfold kToER's simrec branch, naming the
  -- ER-side bases / steps / bound.
  show (ERMor1.simultaneousBoundedRec k a
          (fun j => kToER (h_fam j) (h_h j))
          (fun j => kToER (g_fam j) (h_g j))
          (let p := KMor1.majorize (.simrec i h_fam g_fam) h
           ERMor1.comp (ERMor1.A_two_iter p.1)
             ![ERMor1.sumCtxERPlusOffset (a + 1) p.2])
          i).interp (Fin.cons n x) = _
  -- Step 3: apply simultaneousBoundedRec_interp_correct.
  rw [ERMor1.simultaneousBoundedRec_interp_correct
        k a _ _ _ n x i
        (kToER_simrec_dominates i h_fam g_fam h
          h_h h_g ih_h ih_g n x)
        (kToER_simrec_bound_mono i h_fam g_fam h n x)]
  -- Step 4: the LHS is now Nat.simRecVec over kToER-
  -- translated families; convert back via IH + bridge to
  -- (.simrec i h_fam g_fam).interp.
  have h_bases :
      (fun j' => (kToER (h_fam j') (h_h j')).interp)
        = (fun j' => (h_fam j').interp) := by
    funext j' v'; exact ih_h j' (h_h j') v'
  have h_steps :
      (fun j' => (kToER (g_fam j') (h_g j')).interp)
        = (fun j' => (g_fam j').interp) := by
    funext j' v'; exact ih_g j' (h_g j') v'
  rw [h_bases, h_steps]
  rw [← KMor1.simrecVec_eq_Nat_simRecVec h_fam g_fam x n i]
  -- Step 5: KMor1.interp_simrec rewrites the K^sim-side RHS
  -- into matching simrecVec form.
  rw [KMor1.interp_simrec]
  -- (Fin.cons n x) 0 reduces to n and
  -- (fun j' => (Fin.cons n x) (Fin.succ j')) reduces to x
  -- by Fin.cons's computation rules; `congr 1` (or `congr 2`
  -- depending on residual structure) closes definitionally.
  -- A trailing `<;> simp [...]` would trigger the unused-
  -- tactic linter under `warningAsError = true`.
  congr 1
```

(Implementer adapts the exact rewrite-ordering at task
time; the structural shape — IH-driven family rewrite,
bridge to K^sim simrecVec, then apply
`KMor1.interp_simrec` — is the canonical path.)

Citation: master design §3.5; Tourlakis 2018 §0.1.0.44
(K^sim_n ⊆ E^{n+1}; the level-2 case).

### §6.3 Risk callouts

- **`Fin.foldr` unfolding through `Fin.cons`.**  §6.2.3's
  proof of `kToER_simrec_bound_mono` requires that
  `(sumCtxER (a+1)).interp (Fin.cons m x)` decomposes
  cleanly so the `m`-slot can be bumped to `n`.  Step 4's
  `vMax_cons` (line 875) is the analogue for `vMax`; the
  spec's default plan adds `ERMor1.sumCtxER_cons_le_of_le`
  to `LawvereKSimMajorization.lean` at task time (~6 lines
  per §6.2.3).  Skip only if the implementer finds an
  inline-clean tactic (e.g. via `Fin.foldr_succ` + `omega`)
  that does not require the helper.

- **Equation compiler for `kToER` recursion.**  The simrec
  branch's `let bases / let steps / let p / let bound`
  bindings (or the equivalent inline construction) may
  require `termination_by` or `decreasing_by` annotations
  in some Lean configurations.  If the equation compiler
  rejects the inline form at task time, refactor by
  pulling the bound construction into a non-recursive
  helper `kToER_simrec_bound` taking
  `(a k h_fam g_fam hyp)` as explicit arguments and
  returning `ERMor1 (a + 1)`.  Step 4's `KMor1.majorize`
  uses similarly-shaped `let` chains in its `match` bodies
  without compiler complaints, so the inline form is the
  default expectation.

- **`KMor1.interp_simrec` rewriting.**  §6.2.4's proof
  uses `KMor1.interp_simrec` (a `@[simp]` lemma) to
  rewrite the K^sim-side simrec interp into `simrecVec`
  form.  The rewrite produces
  `KMor1.simrecVec h_fam g_fam (fun j' => ctx (Fin.succ j'))
  (ctx 0) i`, which is *eta-equivalent but not syntactically
  identical* to `KMor1.simrecVec h_fam g_fam (Fin.tail ctx)
  (ctx 0) i`.  At the simrec proof step, use `Fin.cons_zero`
  together with `Fin.cons_succ` to reduce the eta-form
  rather than relying on `Fin.tail_cons` (the latter
  rewrites only when
  the goal already has `Fin.tail` syntactically).  Step 4's
  line 814 used `change KMor1.simrecVec h_fam g_fam (Fin.tail
  v) (v 0) i ≤ _` to bridge — replicate that pattern at
  step 5's call site if needed.

- **`Fin.tail_cons` / `Fin.cons_zero` / `Fin.cons_succ` simp
  lemmas.**  These are mathlib-standard but the exact names
  may have shifted across Lean / mathlib versions.  Confirm
  at implementation time via `lean_local_search` or
  `lean_loogle`.

## §7 The multi-output `kToERN` and its companion

### §7.1 Definitions

```lean
def kToERN {n m : ℕ} (f : KMorN n m)
    (h : ∀ i, (f i).level ≤ 2) : ERMorN n m :=
  fun i => kToER (f i) (h i)

theorem kToERN_interp {n m : ℕ} (f : KMorN n m)
    (h : ∀ i, (f i).level ≤ 2)
    (v : Fin n → ℕ) (j : Fin m) :
    (kToERN f h j).interp v = (f j).interp v :=
  kToER_interp (f j) (h j) v
```

### §7.2 Quotient-lift compatibility

```lean
theorem kToERN_compat_extEq {n m : ℕ}
    {f g : KMorN n m}
    (hf : ∀ i, (f i).level ≤ 2) (hg : ∀ i, (g i).level ≤ 2)
    (hfg : ∀ v i, (f i).interp v = (g i).interp v) :
    ∀ v i, (kToERN f hf i).interp v = (kToERN g hg i).interp v
:= by
  intro v i
  rw [kToERN_interp, kToERN_interp]
  exact hfg v i
```

This is the load-bearing well-definedness lemma for
`kToERFunctor.map`'s Quotient-lift over `depth_witness`.

## §8 The categorical functor `kToERFunctor`

### §8.1 Public signature

```lean
def kToERFunctor : CategoryTheory.Functor
    (LawvereKSimDCat 2) LawvereERCat where
  obj n := n
  map := kToERFunctor_map
  map_id := kToERFunctor_map_id
  map_comp := kToERFunctor_map_comp
```

with the four fields factored out as separate definitions /
theorems for spec readability and for adversarial-review
isolation.

### §8.2 The morphism map

```lean
def kToERFunctor_map {n m : ℕ}
    (f : KSimMor 2 n m) : ERMorNQuo n m :=
  Quotient.liftOn f.depth_witness
    (fun rec => Quotient.mk (erMorNSetoid n m)
                 (kToERN rec.rep rec.rep_level))
    (fun rec₁ rec₂ _ => by
      apply Quotient.sound
      -- Setoid relation on ERMorN: extensional equality of
      -- interps componentwise.
      have h_eq :
          Quotient.mk (kMorNSetoid n m) rec₁.rep
            = Quotient.mk (kMorNSetoid n m) rec₂.rep :=
        rec₁.rep_eq.trans rec₂.rep_eq.symm
      have hrel :
          (kMorNSetoid n m).r rec₁.rep rec₂.rep :=
        Quotient.exact h_eq
      -- hrel : ∀ v i, (rec₁.rep i).interp v
      --              = (rec₂.rep i).interp v
      intro v i
      exact kToERN_compat_extEq rec₁.rep_level
        rec₂.rep_level (fun v' i' => hrel v' i') v i)
```

The well-definedness proof chains the two `rep_eq` fields
to establish `Quotient.mk _ rec₁.rep = Quotient.mk _
rec₂.rep`, then uses `Quotient.exact` to extract the
extensional equality, which `kToERN_compat_extEq` carries
to the ER side.

Citation: master design §3.5 lines 1153–1163.

### §8.3 Functor laws

The default plan is `Quotient.sound` + `simp`-then-extEq —
`rfl` may close them in some elaboration regimes but is not
guaranteed to fire through `Quotient.liftOn` on
`Quotient.mk` without a `simp only [Quotient.lift_mk]`-style
unfolding.  Implementer attempts `rfl` first; if it fails,
uses the documented `Quotient.sound`-and-compute path.

```lean
theorem kToERFunctor_map_id (n : LawvereKSimDCat 2) :
    kToERFunctor_map (𝟙 n) = 𝟙 (n : LawvereERCat) := by
  -- The `𝟙 n` in LawvereKSimDCat 2 has depth_witness =
  -- KMorNQuo.id_atDepth, whose Quotient representative has
  -- rep = KMorN.id n.  Apply Quotient.sound + extensional
  -- equality witnessed by kToER on KMor1.proj.
  apply Quotient.sound
  intro v i
  -- Goal: (kToERN (KMorN.id n) _ i).interp v
  --       = (ERMorN.id n i).interp v
  -- The Quotient.liftOn outer wrapper requires a
  -- Quotient.lift_mk / liftOn_mk firing first, then the
  -- inner kToERN / kToER simp lemmas match.
  simp only [Quotient.liftOn_mk, Quotient.lift_mk,
    kToERN, kToER, KMorN.id, ERMorN.id,
    KMor1.interp_proj, ERMor1.interp_proj]

theorem kToERFunctor_map_comp {n m k : ℕ}
    (f : KSimMor 2 n m) (g : KSimMor 2 m k) :
    kToERFunctor_map (f ≫ g)
      = kToERFunctor_map f ≫ kToERFunctor_map g := by
  -- Composition in LawvereKSimDCat 2 is via
  -- KMorNQuo.comp_atDepth, which produces a representative
  -- KMorN.comp f.rep g.rep.  kToERN commutes with comp
  -- pointwise; both sides reduce to the same ER class.
  apply Quotient.sound
  intro v i
  simp only [Quotient.liftOn_mk, Quotient.lift_mk,
    kToERN, kToER, KMorN.comp, ERMorN.comp,
    KMor1.interp_comp, ERMor1.interp_comp]
```

The `simp only` set may need additional lemmas the
implementer discovers at task time
(`Quotient.lift_mk` / `Quotient.mk_eq_mk`-style); add them
as needed.

If `rfl` happens to close: replace the `Quotient.sound`
tactic with `rfl`.  This is acceptable but not assumed.

The defeq-grounds for an opportunistic `rfl`:

- `kToER`'s comp branch translates `KMor1.comp f gs` literally
  to `ERMor1.comp (kToER f) (fun i => kToER (gs i))`.
- `kToERN` commutes with `KMorN.comp` pointwise.
- `KMorNQuo.comp_atDepth`'s representative is exactly
  `KMorN.comp f.rep g.rep`.

### §8.4 Opportunistic step-11 helpers (Scope B)

The following helpers are likely to be useful at step 11
(the categorical iso) and are easier to write while step 5's
context is fresh.  Implementer adds them at discretion;
none required.

```lean
-- Object-fixed-point: useful for step-11 functor-composition
-- arguments.
@[simp] theorem kToERFunctor_obj (n : LawvereKSimDCat 2) :
    kToERFunctor.obj n = n := rfl
```

Other candidates the implementer may consider:

- A version of `kToERFunctor.map` that operates on a raw
  representative: given `rep : KMorN n m` with each
  component at level ≤ 2, produce the ER quotient class
  directly, bypassing the `KSimMor` wrapper.  Such a
  helper would need a `Quotient.mk _ rep`-shaped
  `depth_witness` constructor — likely a small
  `KMorNQuo.atDepth.ofRep` add-on at task time.  Skip if
  the construction looks involved.

- Compatibility with `KSimMor.includeSucc d`: a lemma
  saying `kToERFunctor` commutes with the depth-weakening
  inclusion.  Useful only if step 11 explicitly invokes
  the inclusion functor; defer until step 11's plan asks
  for it.

Each helper added is documented in its docstring and noted
in `.session/workstreams/er-ksim2-equiv-via-urm.md`.

## §9 Tests (Profile Y)

Test module: `GebLeanTests/LawvereKSimER.lean`.

### §9.1 Tier 1 — atomic kToER `#guard` checks

```lean
example : kToER (a := 3) KMor1.zero (by simp [KMor1.level])
            = ERMor1.zeroN 3 := rfl
example : kToER KMor1.succ (by simp [KMor1.level])
            = ERMor1.succ := rfl
example : kToER (a := 3)
              (KMor1.proj (Fin.mk 1 (by omega)))
              (by simp [KMor1.level])
            = ERMor1.proj (Fin.mk 1 (by omega)) := rfl

example {f : KMor1 0} (h : (KMor1.raise f).level ≤ 2)
        (h' : f.level ≤ 2) :
    kToER (KMor1.raise f) h = kToER f h' := rfl
```

Implementer confirms `rfl` works; if level-discharge `have`s
prevent reduction, fall back to `simp [kToER]`.

### §9.2 Tier 2 — universal-theorem `example` proofs

Construct an inline `addK : KMor1 2` simrec witness in the
test module (the existing landed `addK` in
`GebLeanTests/LawvereKSimInterp.lean` is `private` and so
not importable; it is `KMor1 2`, not `KMor1 1`).  Inline
construction:

```lean
-- Inline addK: λ(x, y). x + y, level 1, simrec over
-- successor.
private def addK : KMor1 2 :=
  KMor1.simrec (k := 0)
    ⟨0, by omega⟩
    -- Base family at index 0: KMor1 1 returning the
    -- single parameter.
    (fun _ => KMor1.proj 0)
    -- Step family at index 0: KMor1 (1 + 1 + 1) =
    -- KMor1 3.  succ of slot 2 (the previous-iter value).
    (fun _ =>
      KMor1.comp KMor1.succ
        ![KMor1.proj 2])

example : (kToER addK (by simp [addK, KMor1.level])).interp
              ![3, 5]
            = addK.interp ![3, 5] :=
  kToER_interp addK _ _

example : (kToER addK (by simp [addK, KMor1.level])).interp
              ![0, 7]
            = addK.interp ![0, 7] :=
  kToER_interp addK _ _
```

If `addK` is not exported, the implementer constructs an
inline `addK` (5–10 lines, copying from the Phase-1 test).
The RHS reduces to the K^sim numeric value (`8`, `7`); the
LHS is taken on faith via `kToER_interp` and never evaluated
on the ER side.  This is the discipline-#4 pattern:
universal theorem at concrete inputs replaces direct ER
`.interp` `#guard`.

### §9.3 Tier 3 — `kToERFunctor` sanity

```lean
example : kToERFunctor.obj 5 = 5 := rfl

example {n : ℕ} :
    kToERFunctor.map (𝟙 (n : LawvereKSimDCat 2))
      = 𝟙 (kToERFunctor.obj n) :=
  kToERFunctor.map_id n
```

## §10 Discipline cross-references

- **Discipline #1 (import-at-skeleton-creation)**: when
  creating `GebLean/LawvereKSimER.lean`, simultaneously add
  `import GebLean.LawvereKSimER` to `GebLean.lean`.  Same for
  the test module ↔ `GebLeanTests.lean`.  Imports go in
  case-insensitive alphabetical order.

- **Build verification before commit**: after every task
  touching a `.lean` file, run `lake build` (and `lake test`
  where applicable).  Inspect output for `error:` and
  `warning:` lines.  Because every new file is imported
  into `GebLean.lean` / `GebLeanTests.lean` at skeleton-
  creation time (discipline #1), `lake build` is the
  authoritative check.

- **LSP-staleness handling**: if lean-lsp output appears
  stale (e.g., a recently-added definition not yet visible),
  use `mcp__lean-lsp__lean_build` to rebuild and restart the
  LSP server.  Avoid manual `.olean` removal — that triggers
  permission prompts and is unnecessary given the import-at-
  skeleton-creation discipline.

- **Discipline #3 (pre-existing infrastructure check)**:
  pre-flight grep `kToER`, `kToERN`, `kToERFunctor`,
  `kToER_interp`, `kToERN_interp`, `kToER_simrec_*`,
  `KMor1.majorize_simrec_index_indep` — confirmed clean as
  of step-5 spec writing time.  Implementer re-checks at
  task time.

- **Discipline #4 (ER-side `.interp` discipline)**: tier-2
  tests use `kToER_interp` at concrete inputs, not direct
  ER-side `#guard` evaluation.

- **Style (CLAUDE.md banned-word list)**: no
  "fundamental" / "actually" / "key" / "core" / "advanced" /
  "complex" / "simple" / "advantage" / "benefit" / "important"
  / "challenge" / "yes" / "wait" / "hmm" / "sorry" / "careful"
  / "important" / "difficult" / "blocked" / "incomplete" /
  "future" / "issue" / "problem" / "block" — neither in code
  nor in docstrings.  Apply also to commit messages.

- **Citation discipline**: every public def/theorem in
  `LawvereKSimER.lean` has a docstring citing master design
  §3.5 and the relevant Tourlakis 2018 paragraph
  (§0.1.0.34 + §0.1.0.10 for the simrec branch; §0.1.0.44
  for `kToER_interp` itself).

- **Toolchain / `nlinarith` not in scope**: per
  `LawvereKSimMajorization`'s import set, `nlinarith` is not
  available; use `omega` plus explicit `Nat.*` lemmas.  Step
  5 inherits this.  `LawvereKSimER.lean` only depends on
  step 4's bridge plus step 2's correctness theorem and
  produces no fresh majorization arithmetic, so `omega` should
  suffice for what little arithmetic remains.

## §11 Acceptance criteria

The step-5 cycle is complete when:

1. `GebLean/LawvereKSimMajorization.lean` defines
   `KMor1.majorize_simrec_index_indep` with no `sorry` and no
   warnings.

2. `GebLean/LawvereKSimER.lean` defines `kToER`, `kToERN`,
   the three Factoring R helpers, `kToER_interp`,
   `kToERN_interp`, `kToERN_compat_extEq`, and `kToERFunctor`
   with no `sorry` and no warnings.  All public declarations
   carry docstrings citing master design §3.5 and the
   relevant Tourlakis 2018 paragraph.

3. `GebLeanTests/LawvereKSimER.lean` exercises Tier 1
   (atomic `#guard`s), Tier 2 (`example` via `kToER_interp`
   on `addK`), and Tier 3 (`kToERFunctor` obj/map sanity).

4. `lake build` and `lake test` complete with zero errors
   and zero warnings.

5. The cycle-end review (a full
   `git diff origin/terence/develop..HEAD`) finds no
   substantive defects.

6. `.session/workstreams/er-ksim2-equiv-via-urm.md` is
   updated with step 5's completion entry, listing what was
   produced (and any opportunistic Scope-B helpers added).

## §12 Reference catalogue

- Master design §3.5 (lines 1089–1163): `kToER` definition
  and proof outline; functor-lift sketch.
- Master design §3.6: Tourlakis result-to-Lean-entity map.
  §0.1.0.34 + §0.1.0.10 (simrec case);
  §0.1.0.44 (kToER_interp).
- Step 2 spec
  (`docs/superpowers/specs/2026-05-03-step-2-er-simultaneous-bounded-rec-design.md`):
  defines `simultaneousBoundedRec_interp_correct` consumed
  by §6.1.4.
- Step 4 spec
  (`docs/superpowers/specs/2026-05-03-step-4-ksim-majorization-design.md`):
  defines `KMor1.majorize_by_componentBound` (the bridge)
  consumed by §6.1.2, plus `sumCtxERPlusOffset`,
  `interp_sumCtxERPlusOffset`, and other step-4 lemmas.
- `GebLean/LawvereKSim.lean`: KMor1 inductive, `KMor1.level`,
  `KMor1.interp`.
- `GebLean/LawvereKSimQuot.lean`: `KSimMor`,
  `KMorNQuo.atDepth`, `LawvereKSimDCat`, `KSimMor.ext`.
- `GebLean/LawvereERQuot.lean`: `LawvereERCat`, `ERMorNQuo`,
  `erMorNSetoid`.
- Tourlakis 2018 §0.1.0.34, §0.1.0.10, §0.1.0.44
  (cited via master design §3.6 catalogue).
