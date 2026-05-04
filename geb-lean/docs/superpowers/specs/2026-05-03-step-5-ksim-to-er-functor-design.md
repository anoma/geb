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

```text
GebLean/LawvereKSimMajorization.lean                 [step 5 ADDS]
  KMor1.majorize_simrec_index_indep
    -- One-line lemma; proof is rfl (or near-rfl).
    -- Asserts that KMor1.majorize at simrec ignores the
    -- output index argument.
  ERMor1.sumCtxER_cons_le_of_le                  [conditional]
    -- Added only if §6.1.3's bound-monotonicity proof needs
    -- it (i.e. if no analogous Fin.foldr lemma is already
    -- available).  Implementer assesses at task time.

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
  Tier 2 universal-theorem `example` proofs.
  Tier 3 kToERFunctor sanity checks.

GebLeanTests.lean                                    [step 5 EDITS]
  Add `import GebLeanTests.LawvereKSimER`
  (alphabetically).
```

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
      exact kToER_interp_simrec i h_fam g_fam h v
        (fun j v' => ih_h j v')
        (fun j v' => ih_g j v')
  | raise f ih =>
      simp only [kToER, KMor1.interp_raise]
      exact ih ...
```

(Implementer adapts the recursor's per-case binder list and
hypothesis names to Lean 4's induction-on-`KMor1` shape.)

## §6 The simrec case: load-bearing proof

### §6.1 The three Factoring R helpers

#### §6.1.1 `KMor1.majorize_simrec_index_indep` (placement: `LawvereKSimMajorization.lean`)

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
  rfl
```

The proof is `rfl` because `KMor1.majorize`'s simrec branch
(line 632 of `LawvereKSimMajorization.lean`) returns
`(2, r_H + r_G + 2)` without referencing the index `i` (the
constructor argument is bound to `_` in the `match`
pattern).  If `rfl` does not close it directly because of
Lean's elaboration of the level-discharge `have`s, fall back
to `simp only [KMor1.majorize]` followed by `rfl`.

Citation: master design §3.5 + §3.4.

#### §6.1.2 `kToER_simrec_dominates`

```lean
theorem kToER_simrec_dominates
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
    ∀ (m : ℕ), m ≤ n → ∀ (j : Fin (k + 1)),
      Nat.simRecVec k a (fun j' => (h_fam j').interp)
          (fun j' => (g_fam j').interp) m x j
        ≤ bound.interp (Fin.cons m x) := by
  intro p bound m _ j
  -- LHS = (KMor1.simrec j h_fam g_fam).interp (Fin.cons m x)
  -- via KMor1.interp_simrec + Fin.tail_cons + Fin.cons_zero
  have h_j : (KMor1.simrec j h_fam g_fam).level ≤ 2 := by
    have hfact :
        (KMor1.simrec j h_fam g_fam).level
          = (KMor1.simrec i h_fam g_fam).level := by
      simp [KMor1.level]
    rw [hfact]; exact hyp
  have h_dom :
      (KMor1.simrec j h_fam g_fam).interp (Fin.cons m x)
        ≤ (ERMor1.comp (ERMor1.A_two_iter
              (KMor1.majorize (.simrec j h_fam g_fam) h_j).1)
            ![ERMor1.sumCtxERPlusOffset (a + 1)
                (KMor1.majorize (.simrec j h_fam g_fam) h_j).2]
          ).interp (Fin.cons m x) :=
    KMor1.majorize_by_componentBound
      (.simrec j h_fam g_fam) h_j (Fin.cons m x)
  -- Use index-independence to identify the two bound terms.
  rw [KMor1.majorize_simrec_index_indep j i ...] at h_dom
  -- Convert (.simrec j h_fam g_fam).interp at Fin.cons m x
  -- into Nat.simRecVec k a ... m x j.
  simp only [KMor1.interp_simrec, Fin.tail_cons,
    Fin.cons_zero] at h_dom
  exact h_dom
```

Citation: master design §3.5 + step 4 §3.5 bridge.

#### §6.1.3 `kToER_simrec_bound_mono`

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
  -- Unfold bound and rewrite via @[simp] interp lemmas.
  simp only [bound, ERMor1.interp_comp,
    ERMor1.interp_A_two_iter,
    ERMor1.interp_sumCtxERPlusOffset,
    Matrix.cons_val_zero]
  -- Goal: tower p.1 ((sumCtxER (a+1)).interp (Fin.cons m x)
  --                  + p.2)
  --       ≤ tower p.1 ((sumCtxER (a+1)).interp (Fin.cons n x)
  --                    + p.2)
  apply tower_mono_right
  apply Nat.add_le_add_right
  -- Need: (sumCtxER (a+1)).interp (Fin.cons m x)
  --        ≤ (sumCtxER (a+1)).interp (Fin.cons n x)
  -- This follows from a sumCtxER_cons-style helper or by
  -- direct Fin.foldr-induction.
  exact sumCtxER_cons_le_of_le h_m_le_n x
```

Where `sumCtxER_cons_le_of_le` is a small helper
(implementer adds it to step 4's module if not already
present, near `vMax_cons` / `interp_sumCtxER`):

```lean
theorem ERMor1.sumCtxER_cons_le_of_le {a m n : ℕ}
    (x : Fin a → ℕ) (h : m ≤ n) :
    (ERMor1.sumCtxER (a + 1)).interp (Fin.cons m x)
      ≤ (ERMor1.sumCtxER (a + 1)).interp (Fin.cons n x) := by
  rw [ERMor1.interp_sumCtxER, ERMor1.interp_sumCtxER]
  -- Induction or direct calculation on Fin.foldr.
  -- The Fin.cons m x sum factors as m + (Fin.foldr ... x);
  -- bound the m-component by n, unchanged on the rest.
  -- Tactic shape: `gcongr` if available, else induction.
  ...
```

Citation: master design §3.5; transitively step 4 §3.

#### §6.1.4 `kToER_interp_simrec` (assembly)

```lean
theorem kToER_interp_simrec
    {a k : ℕ}
    (i : Fin (k + 1))
    (h_fam : Fin (k + 1) → KMor1 a)
    (g_fam : Fin (k + 1) → KMor1 (a + 1 + (k + 1)))
    (h : (KMor1.simrec i h_fam g_fam).level ≤ 2)
    (v : Fin (a + 1) → ℕ)
    (ih_h : ∀ (j : Fin (k + 1)) (v' : Fin a → ℕ),
      (kToER (h_fam j) (h_h j)).interp v' = (h_fam j).interp v')
    (ih_g : ∀ (j : Fin (k + 1)) (v' : Fin (a + 1 + (k + 1)) → ℕ),
      (kToER (g_fam j) (h_g j)).interp v' = (g_fam j).interp v') :
    (kToER (.simrec i h_fam g_fam) h).interp v
      = (KMor1.simrec i h_fam g_fam).interp v := by
  set n := v 0
  set x := Fin.tail v
  have hv : v = Fin.cons n x := (Fin.cons_self_tail v).symm
  rw [hv]
  -- LHS unfolds to simultaneousBoundedRec ... bound i applied
  -- at Fin.cons n x.
  simp only [kToER]
  rw [ERMor1.simultaneousBoundedRec_interp_correct
        k a (fun j => kToER (h_fam j) _)
            (fun j => kToER (g_fam j) _)
            (ERMor1.comp (ERMor1.A_two_iter ...)
              ![ERMor1.sumCtxERPlusOffset (a + 1) ...])
            n x i
        (kToER_simrec_dominates i h_fam g_fam h n x)
        (kToER_simrec_bound_mono i h_fam g_fam h n x)]
  -- Now LHS = simRecVec k a (fun j' => (kToER (h_fam j')).interp)
  --             (fun j' => (kToER (g_fam j')).interp) n x i.
  -- Use ih_h, ih_g to replace each kToER-interp by the K^sim
  -- interp, recovering simRecVec ... n x i.
  have h_bases :
      (fun j' => (kToER (h_fam j') _).interp)
        = (fun j' => (h_fam j').interp) := by
    funext j' v'; exact ih_h j' v'
  have h_steps :
      (fun j' => (kToER (g_fam j') _).interp)
        = (fun j' => (g_fam j').interp) := by
    funext j' v'; exact ih_g j' v'
  rw [h_bases, h_steps]
  -- RHS: KMor1.interp_simrec rewrites to simRecVec ... n x i.
  simp only [KMor1.interp_simrec, Fin.tail_cons, Fin.cons_zero]
```

(Implementer adapts argument-passing for the bound's `p.1`
and `p.2` projections; the placeholders `...` indicate where
the actual `KMor1.majorize (.simrec i h_fam g_fam) h` reduction
materializes.)

### §6.2 Risk callouts

- **`Fin.foldr` unfolding through `Fin.cons`.**  Step 6.1.3's
  proof of `kToER_simrec_bound_mono` requires that
  `(sumCtxER (a+1)).interp (Fin.cons m x)` decomposes
  cleanly so the `m`-slot can be bumped to `n`.  Step 4's
  `vMax_cons` (line 875) is the analogue for `vMax`; if no
  `sumCtxER_cons` exists yet, add it (~5 lines) or unfold
  `Fin.foldr` directly via `Fin.foldr_succ`.  Implementer
  to assess at task time.

- **Equation compiler for `kToER` recursion.**  The simrec
  branch's `let bases / let steps / let p / let bound`
  bindings may confuse Lean's equation compiler, requiring
  `termination_by` or `decreasing_by` annotations.  If so,
  pull the let-bindings into a separate helper `kToER_simrec`
  taking `(bases, steps, bound, i)` as explicit arguments.

- **`KMor1.interp_simrec`'s `change`-or-`simp` shape.**
  Step 4's line 814 used `change KMor1.simrecVec ... ≤ _` to
  bridge the goal-text mismatch.  Step 5's simrec proof may
  need the same trick.  Reuse the existing `change` pattern.

- **`Fin.tail_cons` / `Fin.cons_zero` simp lemmas.**  These
  are mathlib-standard but their exact names may have shifted
  across Lean / mathlib versions.  Confirm at implementation
  time via `lean_local_search` or `lean_loogle`.

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
      -- Setoid relation on ERMorN: extensional equality.
      intro v i
      apply kToERN_compat_extEq
        rec₁.rep_level rec₂.rep_level
        ?_ v i
      -- Goal: ∀ v i, (rec₁.rep i).interp v = (rec₂.rep i).interp v
      have hrel : kMorNSetoid n m |>.r rec₁.rep rec₂.rep := by
        apply Quotient.exact
        rw [rec₁.rep_eq, rec₂.rep_eq]
      exact hrel)
```

Citation: master design §3.5 lines 1153–1163.

### §8.3 Functor laws

```lean
theorem kToERFunctor_map_id (n : LawvereKSimDCat 2) :
    kToERFunctor_map (𝟙 n) = 𝟙 (n : LawvereERCat) := by
  -- The `𝟙 n` in LawvereKSimDCat 2 has depth_witness with
  -- rep = KMorN.id n; kToERN (KMorN.id n) _ is fun i =>
  -- ERMor1.proj i = ERMorN.id n (definitionally).
  -- Quotient.mk of that is 𝟙 in LawvereERCat.
  rfl
  -- Fallback if rfl too weak:
  -- apply Quotient.sound
  -- intro v i
  -- simp [kToER, kToERN, KMorN.id, ERMorN.id]

theorem kToERFunctor_map_comp {n m k : ℕ}
    (f : KSimMor 2 n m) (g : KSimMor 2 m k) :
    kToERFunctor_map (f ≫ g)
      = kToERFunctor_map f ≫ kToERFunctor_map g := by
  rfl
  -- Fallback if rfl too weak:
  -- apply Quotient.sound
  -- intro v i
  -- simp [kToER, kToERN, KMorN.comp, ERMorN.comp]
```

The `rfl` closes are expected because:

- `kToER`'s comp branch translates `KMor1.comp f gs` literally
  to `ERMor1.comp (kToER f) (fun i => kToER (gs i))`.
- `kToERN` commutes with `KMorN.comp` pointwise (`fun i =>
  kToER (KMor1.comp (fst i) snd) = ERMor1.comp (kToER fst i)
  (fun j => kToER (snd j))`).
- `KMorNQuo.comp_atDepth`'s representative is exactly
  `KMorN.comp f.rep g.rep`.

If the Quotient layer's elaboration hides this defeq, the
`Quotient.sound` + `simp` fallback is at most 5 lines per
law.

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

-- Quotient-class commutation.
theorem kToERFunctor_map_quot {n m : ℕ}
    (rep : KMorN n m)
    (h_lvl : ∀ i, (rep i).level ≤ 2)
    (h_dw : KMorNQuo.atDepth 2 (Quotient.mk _ rep)) :
    kToERFunctor.map ⟨Quotient.mk _ rep, h_dw⟩
      = Quotient.mk _ (kToERN rep h_lvl) := by
  ...

-- KSimMor.includeSucc compatibility (if step 11 needs it).
-- ...
```

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
block reduction, fall back to `simp [kToER]`.

### §9.2 Tier 2 — universal-theorem `example` proofs

Use the `addK : KMor1 1` simrec witness from Phase-1
task #239 (level 1 — fits within the level-2 hypothesis).

```lean
example : (kToER addK (by simp [KMor1.level])).interp ![3, 5]
            = addK.interp ![3, 5] :=
  kToER_interp addK _ _

example : (kToER addK (by simp [KMor1.level])).interp ![0, 7]
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
   substantive issues.

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
