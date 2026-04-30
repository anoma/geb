# `kToER` forward translation: implementation plan

> **For agentic workers**: REQUIRED SUB-SKILL: Use
> `superpowers:subagent-driven-development` (recommended) or
> `superpowers:executing-plans` to implement this plan
> task-by-task.  Steps use checkbox (`- [ ]`) syntax for
> tracking.

**Goal**: Implement the forward translation
`kToER : (f : KMor1 a) → f.level ≤ 2 → ERMor1 a` and its
multi-output companion `kToERN`, prove
interp-preservation, and lift to a categorical functor
`F : KSimMor 2 ⥤ LawvereERCat`.

**Architecture**: Per-constructor structural recursion;
atomic constructors map directly; `comp` and `raise`
recurse; `simrec` at depth ≤ 2 (children at depth ≤ 1)
encodes simultaneous recursion via Szudzik pairing and
runs it through `ERMor1.boundedRec` with a tower-height
bound from `ERMor1.towerBound`.  A precondition refactor
adjusts Phase 1's `KMorNQuo.atDepth` from a Prop
existential to a data-bearing Setoid quotient so the
functor's representative extraction is constructive.

**Tech Stack**: Lean 4 with mathlib; existing GebLean
infrastructure (`ERMor1`, `ERMor1.boundedRec`,
`ERMor1.towerBound`, `Nat.seqPack`/`Nat.seqAt`,
`KMor1`/`KMorN`/`KMorNQuo`, `KSimMor d` /
`LawvereKSimDCat d`); category-theory layer from
`Mathlib.CategoryTheory`.

**Spec**: `docs/plans/2026-04-29-lawvere-k-sim-ktoer-design.md`.

**Tooling note**: Lean MCP skills are available to
implementer subagents — `lean_goal` for inspecting
intermediate proof states, `lean_multi_attempt` for
batch-testing tactics at a position, and the deep-search
proof-completion route under the `lean4` plugin's
`*-filler-deep` skill.  These are particularly relevant
for `boundedRec`'s well-definedness obligations and the
Szudzik round-trip lemmas.

---

## File structure

The plan creates and modifies these files:

- **Modify**: `GebLean/LawvereKSimQuot.lean` — refactor
  `KMorNQuo.atDepth` to a Setoid-quotient (Task 1).
- **Create**: `GebLean/Utilities/KSimSzudzikSimrec.lean` —
  Szudzik pack/unpack ER terms, the packed base/step
  builders, and the tower-bound builder (Tasks 3–8).
- **Create**: `GebLean/LawvereKSimER.lean` — `kToER`,
  `kToERN`, interp-preservation theorems, and the functor
  `kToERFunctor` (Tasks 9–17).
- **Create**: `GebLeanTests/LawvereKSimER.lean` — three
  tiers of `#guard` tests (Tasks 18–20).
- **Modify**: `GebLean.lean` — re-export new modules
  (Task 21).
- **Modify**: `GebLeanTests.lean` — register new test
  module (Task 21).

The Szudzik file groups together Phase-2-specific helpers
that are not used elsewhere; if any helper is later
needed in another module it can be promoted to a more
general utility location at that time.

---

## Task 1: Refactor `KMorNQuo.atDepth` to data-bearing Setoid quotient

**Files**:

- Modify: `GebLean/LawvereKSimQuot.lean`

This is component C1.  Replace the Prop existential with a
data-bearing raw witness wrapped in a Quotient using the
always-true Setoid relation, so that all elements remain
equal as Lean values (preserving proof-irrelevance) while
constructive consumers can extract a representative via
`Quotient.lift`.

- [ ] **Step 1.1: Add `KMorNQuo.AtDepthRaw` structure and
  Setoid instance**

Replace the existing definition of `KMorNQuo.atDepth`
(lines 367–375) with the following new declarations,
placing them in the same location:

```lean
/-- Constructive raw witness that a `KMorNQuo n m` class
admits a representative whose components all have
`KMor1.level ≤ d`.  Carries the representative tuple, a
proof of the level bound, and a proof that it represents
the given equivalence class. -/
structure KMorNQuo.AtDepthRaw {n m : ℕ} (d : ℕ)
    (q : KMorNQuo n m) where
  rep        : KMorN n m
  rep_level  : ∀ i : Fin m, (rep i).level ≤ d
  rep_eq     : Quotient.mk (kMorNSetoid n m) rep = q

/-- The always-true Setoid on `KMorNQuo.AtDepthRaw`,
making all raw witnesses equivalent.  Quotienting by this
relation produces a Subsingleton type whose unique element
encapsulates the existence claim. -/
instance kMorNQuoAtDepthSetoid {n m : ℕ} (d : ℕ)
    (q : KMorNQuo n m) :
    Setoid (KMorNQuo.AtDepthRaw d q) where
  r _ _ := True
  iseqv :=
    ⟨fun _ => trivial,
     fun _ => trivial,
     fun _ _ => trivial⟩

/-- Data-bearing depth witness: the Quotient of
`KMorNQuo.AtDepthRaw` by the always-true Setoid.  All
elements are equal as Lean values via
`Quotient.sound trivial`. -/
def KMorNQuo.atDepth {n m : ℕ} (d : ℕ)
    (q : KMorNQuo n m) : Type :=
  Quotient (kMorNQuoAtDepthSetoid d q)

/-- All elements of `KMorNQuo.atDepth d q` are equal,
preserving the proof-irrelevance behaviour of the
original Prop formulation. -/
instance KMorNQuo.atDepth.subsingleton {n m d : ℕ}
    (q : KMorNQuo n m) :
    Subsingleton (KMorNQuo.atDepth d q) where
  allEq a b :=
    Quotient.ind₂ (motive := fun a b => a = b)
      (fun _ _ => Quotient.sound trivial) a b
```

- [ ] **Step 1.2: Run `lake build` to confirm the new
  declarations compile**

```bash
lake build GebLean.LawvereKSimQuot
```

Expected: PASS for the file up through the `Subsingleton`
instance; the existing `id_atDepth`, `comp_atDepth`,
`KSimMor`, `KSimMor.ext`, `Category` instance, and
`KSimMor.includeSucc` will subsequently fail because
their bodies expect the Prop formulation.

- [ ] **Step 1.3: Refactor `KMorNQuo.id_atDepth` from
  Prop theorem to data def**

Replace the existing `theorem KMorNQuo.id_atDepth` (lines
377–381) with:

```lean
/-- Constructive depth witness for the identity
quotient morphism. -/
def KMorNQuo.id_atDepth {n d : ℕ} :
    KMorNQuo.atDepth d (KMorNQuo.id n) :=
  Quotient.mk _
    { rep        := KMorN.id n
      rep_level  := fun _ => by
        simp [KMorN.id, KMor1.level]
      rep_eq     := rfl }
```

- [ ] **Step 1.4: Refactor `KMorNQuo.comp_atDepth` from
  Prop theorem to data def**

Replace the existing `theorem KMorNQuo.comp_atDepth`
(lines 383–401) with:

```lean
/-- Constructive depth witness for composition.  Lifts
the witness extraction across both quotient arguments
via `Quotient.lift₂`, then re-quotients the resulting
raw witness. -/
def KMorNQuo.comp_atDepth {n m k d : ℕ}
    {f : KMorNQuo n m} {g : KMorNQuo m k}
    (hf : KMorNQuo.atDepth d f)
    (hg : KMorNQuo.atDepth d g) :
    KMorNQuo.atDepth d (KMorNQuo.comp f g) := by
  refine Quotient.liftOn₂
    (s₁ := kMorNQuoAtDepthSetoid d f)
    (s₂ := kMorNQuoAtDepthSetoid d g)
    hf hg
    (fun fr gr =>
      Quotient.mk _
        { rep := KMorN.comp gr.rep fr.rep
          rep_level := ?_
          rep_eq := ?_ })
    (fun _ _ _ _ _ _ => Quotient.sound trivial)
  · intro i
    simp only [KMorN.comp, KMor1.level]
    refine Nat.max_le.mpr ⟨gr.rep_level i, ?_⟩
    apply Finset.sup_le
    intro j _
    exact fr.rep_level j
  · rw [← fr.rep_eq, ← gr.rep_eq]; rfl
```

- [ ] **Step 1.5: Update `KSimMor.ext` proof**

The existing `KSimMor.ext` (lines 437–441) becomes:

```lean
@[ext] theorem KSimMor.ext {d n m : ℕ}
    {x y : KSimMor d n m} (h : x.hom = y.hom) :
    x = y := by
  cases x; cases y
  subst h
  congr 1
  exact Subsingleton.elim _ _
```

`depth_witness` is now `Subsingleton`-valued, so any
two witnesses on the same `hom` are equal via the
`Subsingleton` instance from Step 1.1.  If `congr 1`
closes the goal directly (mathlib's `congr` sometimes
discharges Subsingleton subgoals automatically), the
trailing `exact` becomes redundant; the implementer may
remove it.

- [ ] **Step 1.6: Update the depth-d `Category` instance**

The `CategoryStruct` and `Category` instances at lines
423–453 should still compile as written, because:

- The `id`/`comp` fields use `KMorNQuo.id_atDepth` and
  `KMorNQuo.comp_atDepth`, both of which now produce
  values of the `atDepth` type rather than Prop elements.
- The `id_comp`, `comp_id`, `assoc` proofs end with
  `apply KSimMor.ext` followed by the `KMorNQuo` law,
  which still applies to the `hom` field.

After Step 1.5, run:

```bash
lake build GebLean.LawvereKSimQuot
```

Expected: PASS for the `Category` instance; only the
`KSimMor.includeSucc` definition (next step) remains.

- [ ] **Step 1.7: Update `KSimMor.includeSucc` to extract
  the rep via `Quotient.lift`**

Replace the existing `KSimMor.includeSucc` (lines
461–473) with:

```lean
/-- The inclusion functor weakening the depth from `d`
to `d + 1`.  On objects it is the identity (both
categories have the same `ℕ`-shaped object collection);
on morphisms it forwards the underlying `KMorNQuo` and
weakens the depth witness via monotonicity. -/
def KSimMor.includeSucc (d : ℕ) :
    CategoryTheory.Functor
      (LawvereKSimDCat d)
      (LawvereKSimDCat (d + 1)) where
  obj n := n
  map {n m} h :=
    ⟨h.hom,
      Quotient.liftOn
        (s := kMorNQuoAtDepthSetoid d h.hom)
        h.depth_witness
        (fun raw =>
          Quotient.mk _
            { rep        := raw.rep
              rep_level  := fun i =>
                Nat.le_succ_of_le (raw.rep_level i)
              rep_eq     := raw.rep_eq })
        (fun _ _ _ => Quotient.sound trivial)⟩
  map_id _ := KSimMor.ext rfl
  map_comp _ _ := KSimMor.ext rfl
```

- [ ] **Step 1.8: Run `lake build` to verify the file is
  clean**

```bash
lake build GebLean.LawvereKSimQuot
```

Expected: PASS, no warnings.

- [ ] **Step 1.9: Run the existing K^sim test suite**

```bash
lake test
```

Expected: PASS, no failures.  The Phase 1 test files
`GebLeanTests/LawvereKSimQuot.lean` exercise the
quotient category, the depth-restricted subcategory, and
`includeSucc`; they should continue to pass since the
external interface of `KSimMor` is unchanged.

- [ ] **Step 1.10: Commit**

```bash
git add GebLean/LawvereKSimQuot.lean
git commit -m "Refactor KMorNQuo.atDepth to data-bearing Setoid quotient

Replace the Prop existential with a structure carrying
the representative and its level bound, then quotient by
the always-true Setoid.  Preserves proof-irrelevance via
a Subsingleton instance while allowing constructive
extraction of representatives through Quotient.lift.
Required for the upcoming kToER functor's well-defined
representative extraction."
```

---

## Task 2: Create `GebLean/Utilities/KSimSzudzikSimrec.lean` skeleton

**Files**:

- Create: `GebLean/Utilities/KSimSzudzikSimrec.lean`

Establish a new module under `Utilities/` to host the
Phase-2-specific Szudzik-based pack/unpack ER terms and
the simrec packed-iteration helpers.  The file follows
the existing utility-module conventions (single-purpose,
imports only what it uses, opens
`namespace GebLean … end GebLean`).

- [ ] **Step 2.1: Create the module skeleton**

Write the following to `GebLean/Utilities/KSimSzudzikSimrec.lean`:

```lean
import GebLean.LawvereER
import GebLean.LawvereERBoundComputable
import GebLean.Utilities.ERArith
import GebLean.Utilities.SzudzikSeq

/-!
# Szudzik-based simrec helpers for `kToER`

ER-side combinators packing a `(k+1)`-tuple of ER values
into a single ℕ via iterated right-associated Szudzik
pairing, the inverse component-extraction term, and the
packed base/step builders for translating a K^sim
`simrec` term to an `ERMor1` term using
`ERMor1.boundedRec`.

The pack/unpack ER terms compose `ERMor1.natPair`,
`ERMor1.natUnpairFst`, and `ERMor1.natUnpairSnd` per the
sequence-encoding rules of `Nat.seqPack` and
`Nat.seqAt` from `Utilities/SzudzikSeq.lean`.

See `docs/plans/2026-04-29-lawvere-k-sim-ktoer-design.md`,
component C5.
-/

namespace GebLean

end GebLean
```

- [ ] **Step 2.2: Run `lake build` to confirm the
  skeleton compiles**

```bash
lake build GebLean.Utilities.KSimSzudzikSimrec
```

Expected: PASS, no warnings.

- [ ] **Step 2.3: Commit**

```bash
git add GebLean/Utilities/KSimSzudzikSimrec.lean
git commit -m "Add module skeleton for K^sim simrec Szudzik helpers

New utility module GebLean/Utilities/KSimSzudzikSimrec.lean
will host the ER-side pack/unpack combinators and packed
base/step builders used to translate a level-2 K^sim
simrec term to an ERMor1 term via boundedRec."
```

---

## Task 3: `kSimSzudzikPackList` ER term and interp lemma

**Files**:

- Modify: `GebLean/Utilities/KSimSzudzikSimrec.lean`

The ER-side packer for a finite tuple of ER terms.  Given
a family `t : Fin (k + 1) → ERMor1 a`, produce
`packList t : ERMor1 a` whose interpretation at `ctx`
equals `Nat.seqPack` of the values
`[t_0.interp ctx, …, t_k.interp ctx]`.

- [ ] **Step 3.1: Add the recursive `packList` definition**

Append to `GebLean/Utilities/KSimSzudzikSimrec.lean`
inside the `namespace GebLean` block:

```lean
/-- Pack a `(k + 1)`-tuple of ER terms into a single ER
term whose interp is the iterated right-associated
Szudzik pairing of the tuple's interps, terminated with
`0` (mirroring `Nat.seqPack`). -/
def kSimSzudzikPackList :
    {a k : ℕ} → (Fin (k + 1) → ERMor1 a) → ERMor1 a
  | a, 0,     t =>
      ERMor1.comp ERMor1.succ
        (fun (_ : Fin 1) =>
          ERMor1.comp ERMor1.natPair
            (fun i => match i with
              | ⟨0, _⟩ => t 0
              | ⟨1, _⟩ => ERMor1.zeroN a))
  | a, k + 1, t =>
      ERMor1.comp ERMor1.succ
        (fun (_ : Fin 1) =>
          ERMor1.comp ERMor1.natPair
            (fun i => match i with
              | ⟨0, _⟩ => t 0
              | ⟨1, _⟩ =>
                  kSimSzudzikPackList (a := a) (k := k)
                    (fun j => t j.succ)))
```

- [ ] **Step 3.2: Add the interp lemma at the base case**

Append:

```lean
@[simp] theorem kSimSzudzikPackList_zero_interp {a : ℕ}
    (t : Fin 1 → ERMor1 a) (ctx : Fin a → ℕ) :
    (kSimSzudzikPackList (k := 0) t).interp ctx =
      Nat.pair ((t 0).interp ctx) 0 + 1 := by
  unfold kSimSzudzikPackList
  simp only [ERMor1.interp_comp, ERMor1.interp_succ,
    ERMor1.interp_natPair, ERMor1.interp_zeroN]
  rfl
```

- [ ] **Step 3.3: Add the interp lemma at the step case**

Append:

```lean
@[simp] theorem kSimSzudzikPackList_succ_interp
    {a k : ℕ} (t : Fin (k + 2) → ERMor1 a)
    (ctx : Fin a → ℕ) :
    (kSimSzudzikPackList (k := k + 1) t).interp ctx =
      Nat.pair ((t 0).interp ctx)
        ((kSimSzudzikPackList (k := k)
          (fun j => t j.succ)).interp ctx) + 1 := by
  unfold kSimSzudzikPackList
  simp only [ERMor1.interp_comp, ERMor1.interp_succ,
    ERMor1.interp_natPair]
  rfl
```

- [ ] **Step 3.4: Add the closed-form interp characterisation**

Append:

```lean
/-- Interpretation of `kSimSzudzikPackList` equals
`Nat.seqPack` applied to the list of component interps. -/
theorem kSimSzudzikPackList_interp :
    {a k : ℕ} → (t : Fin (k + 1) → ERMor1 a) →
      (ctx : Fin a → ℕ) →
      (kSimSzudzikPackList t).interp ctx =
        Nat.seqPack
          ((List.finRange (k + 1)).map
            (fun j => (t j).interp ctx))
  | _, 0,     t, ctx => by
      simp [List.finRange,
        Nat.seqPack]
  | _, k + 1, t, ctx => by
      simp only [kSimSzudzikPackList_succ_interp]
      rw [kSimSzudzikPackList_interp (k := k)
        (fun j => t j.succ) ctx]
      simp [List.finRange,
        List.map_cons, Nat.seqPack]
```

- [ ] **Step 3.5: Run `lake build`**

```bash
lake build GebLean.Utilities.KSimSzudzikSimrec
```

Expected: PASS, no warnings.

- [ ] **Step 3.6: Commit**

```bash
git add GebLean/Utilities/KSimSzudzikSimrec.lean
git commit -m "Add kSimSzudzikPackList ER term and interp lemmas

Pack a (k + 1)-tuple of ER terms into a single ER term
whose interp matches Nat.seqPack of the component interps."
```

---

## Task 4: `kSimSzudzikUnpackAt` ER term and interp lemma

**Files**:

- Modify: `GebLean/Utilities/KSimSzudzikSimrec.lean`

The component-extraction ER term: given an arity `a` and
a fixed index `i : ℕ` (statically known), produce
`unpackAt a i : ERMor1 (a + 1)` whose interp at
`Fin.cons packed ctx` returns `Nat.seqAt packed i`.  The
arity-`a + 1` shape allows direct composition with the
output of `boundedRec` (which has shape `ERMor1 (k + 1)`
with the counter in slot `0`).

- [ ] **Step 4.1: Add the recursive `unpackAt` definition**

Append to `GebLean/Utilities/KSimSzudzikSimrec.lean`:

```lean
/-- Component selector: `unpackAt a i` is an ER term of
arity `a + 1` whose interp at `Fin.cons packed ctx`
returns `Nat.seqAt packed i`.  The recursion descends
through `i` peeling off Szudzik pairs via
`natUnpairSnd`, then takes a `natUnpairFst` at the
target depth. -/
def kSimSzudzikUnpackAt : (a : ℕ) → (i : ℕ) →
    ERMor1 (a + 1)
  | a, 0     =>
      ERMor1.comp ERMor1.natUnpairFst
        (fun (_ : Fin 1) =>
          ERMor1.comp ERMor1.predN
            (fun (_ : Fin 1) =>
              ERMor1.proj (k := a + 1) ⟨0, by omega⟩))
  | a, i + 1 =>
      ERMor1.comp (kSimSzudzikUnpackAt a i)
        (fun j =>
          if h : j.val = 0 then
            ERMor1.comp ERMor1.natUnpairSnd
              (fun (_ : Fin 1) =>
                ERMor1.comp ERMor1.predN
                  (fun (_ : Fin 1) =>
                    ERMor1.proj (k := a + 1)
                      ⟨0, by omega⟩))
          else
            ERMor1.proj (k := a + 1)
              ⟨j.val, by
                have := j.isLt; omega⟩)
```

Note: `ERMor1.predN n` is the cut-off predecessor at
arity `n`, producing
`if x = 0 then 0 else x − 1`.  It exists in
`Utilities/ERArith.lean` (verify with
`grep predN GebLean/Utilities/ERArith.lean`); if it does
not exist under that exact name, the implementer should
substitute the correct existing predecessor combinator
(it is constructed from `sub` and `oneN`).  The sequence
encoding `n + 1` is decoded by predecessor before
applying `unpair`.

- [ ] **Step 4.2: Add the interp lemma at the base case**

Append:

```lean
@[simp] theorem kSimSzudzikUnpackAt_zero_interp {a : ℕ}
    (packed : ℕ) (ctx : Fin a → ℕ) :
    (kSimSzudzikUnpackAt a 0).interp
        (Fin.cons packed ctx) =
      (Nat.unpair (packed - 1)).1 := by
  unfold kSimSzudzikUnpackAt
  simp [ERMor1.interp_comp, ERMor1.interp_natUnpairFst,
    ERMor1.interp_predN, ERMor1.interp_proj,
    Fin.cons_zero]
```

If `predN`'s name or semantics differ in the codebase,
adjust both this lemma and the definition above
accordingly; the goal of the lemma is the equation as
stated (the right-hand side is the desired closed form).

- [ ] **Step 4.3: Add the closed-form interp lemma
  matching `Nat.seqAt`**

Append:

```lean
/-- Interpretation of `kSimSzudzikUnpackAt`: extracting
the `i`-th component from a packed value. -/
theorem kSimSzudzikUnpackAt_interp_eq_seqAt :
    {a : ℕ} → (i : ℕ) → (packed : ℕ) →
      (ctx : Fin a → ℕ) →
      (kSimSzudzikUnpackAt a i).interp
          (Fin.cons packed ctx) =
        Nat.seqAt packed i
  | _, 0,     0,         _   => by
      simp [kSimSzudzikUnpackAt, Nat.seqAt]
  | _, 0,     n + 1,     _   => by
      simp [kSimSzudzikUnpackAt, Nat.seqAt,
        ERMor1.interp_comp, ERMor1.interp_natUnpairFst,
        ERMor1.interp_predN, Fin.cons_zero]
  | _, i + 1, 0,         _   => by
      simp [kSimSzudzikUnpackAt, Nat.seqAt]
  | a, i + 1, n + 1,     ctx => by
      unfold kSimSzudzikUnpackAt
      simp only [ERMor1.interp_comp]
      have ih := kSimSzudzikUnpackAt_interp_eq_seqAt
        (a := a) (i := i)
        (packed := (Nat.unpair n).2) (ctx := ctx)
      simp [Fin.cons, Nat.seqAt, ih,
        ERMor1.interp_comp, ERMor1.interp_natUnpairSnd,
        ERMor1.interp_predN, ERMor1.interp_proj]
```

The implementer is encouraged to use `lean_goal` and
`lean_multi_attempt` here to find the exact `simp` set
that closes each branch; the four-way case split on
`(i, packed)` reflects the four cases in the definition
of `Nat.seqAt`.

- [ ] **Step 4.4: Run `lake build`**

```bash
lake build GebLean.Utilities.KSimSzudzikSimrec
```

Expected: PASS, no warnings.

- [ ] **Step 4.5: Commit**

```bash
git add GebLean/Utilities/KSimSzudzikSimrec.lean
git commit -m "Add kSimSzudzikUnpackAt ER term and seqAt interp lemma

Component selector kSimSzudzikUnpackAt a i has arity
a + 1 and extracts the i-th component from a Szudzik-
packed value.  Its interpretation equals Nat.seqAt
packed i."
```

---

## Task 5: `kSimSzudzikUnpackAt` round-trip with `kSimSzudzikPackList`

**Files**:

- Modify: `GebLean/Utilities/KSimSzudzikSimrec.lean`

The round-trip property: extracting the `i`-th component
of a packed family recovers `(t i).interp ctx` (for `i`
in range).

- [ ] **Step 5.1: Add the round-trip lemma**

Append to `GebLean/Utilities/KSimSzudzikSimrec.lean`:

```lean
/-- Round-trip: extracting the `i`-th component of a
Szudzik-packed family recovers the `i`-th component's
interpretation. -/
theorem kSimSzudzikUnpackAt_packList {a k : ℕ}
    (t : Fin (k + 1) → ERMor1 a) (i : Fin (k + 1))
    (ctx : Fin a → ℕ) :
    (kSimSzudzikUnpackAt a i.val).interp
        (Fin.cons
          ((kSimSzudzikPackList t).interp ctx) ctx) =
      (t i).interp ctx := by
  rw [kSimSzudzikUnpackAt_interp_eq_seqAt,
    kSimSzudzikPackList_interp]
  have hlen :
      ((List.finRange (k + 1)).map
        (fun j => (t j).interp ctx)).length = k + 1 := by
    simp [List.length_map, List.length_finRange]
  rw [Nat.seqAt_seqPack
    (xs := (List.finRange (k + 1)).map
      (fun j => (t j).interp ctx))
    (i := i.val) (h := by rw [hlen]; exact i.isLt)]
  simp [List.get_map, List.finRange,
    List.get_finRange]
```

If the trailing `simp` does not close, the implementer
should examine the goal with `lean_goal` and pick
explicit `List.get` / `List.finRange` / `Fin.val`
rewrites to massage the LHS into `(t i).interp ctx`.

- [ ] **Step 5.2: Run `lake build`**

```bash
lake build GebLean.Utilities.KSimSzudzikSimrec
```

Expected: PASS, no warnings.

- [ ] **Step 5.3: Commit**

```bash
git add GebLean/Utilities/KSimSzudzikSimrec.lean
git commit -m "Prove kSimSzudzikUnpackAt + packList round-trip

The i-th component selector applied to a Szudzik-packed
family recovers the i-th component's interpretation."
```

---

## Task 6: `kSimPackedBase` builder and interp lemma

**Files**:

- Modify: `GebLean/Utilities/KSimSzudzikSimrec.lean`

Wraps `kSimSzudzikPackList` for the base-family input of
the simrec translation: pack the values
`(h_0_ER ȳ, …, h_k_ER ȳ)`.  This is just the `packList`
applied to a `Fin (k + 1) → ERMor1 a` family; the
purpose of the named wrapper is to give the simrec
translation a directly-named composite per the
bottom-up named-composite discipline.

- [ ] **Step 6.1: Add the wrapper definition and interp
  lemma**

Append:

```lean
/-- Base-family packer for `simrec` translation: packs
the family `h : Fin (k + 1) → ERMor1 a` into a single
`ERMor1 a` whose interp at `ctx` Szudzik-packs the
component interps. -/
def kSimPackedBase {a k : ℕ}
    (h : Fin (k + 1) → ERMor1 a) : ERMor1 a :=
  kSimSzudzikPackList h

@[simp] theorem kSimPackedBase_interp {a k : ℕ}
    (h : Fin (k + 1) → ERMor1 a) (ctx : Fin a → ℕ) :
    (kSimPackedBase h).interp ctx =
      Nat.seqPack
        ((List.finRange (k + 1)).map
          (fun j => (h j).interp ctx)) :=
  kSimSzudzikPackList_interp h ctx
```

- [ ] **Step 6.2: Run `lake build`**

```bash
lake build GebLean.Utilities.KSimSzudzikSimrec
```

Expected: PASS, no warnings.

- [ ] **Step 6.3: Commit**

```bash
git add GebLean/Utilities/KSimSzudzikSimrec.lean
git commit -m "Add kSimPackedBase builder and interp lemma

Simrec base-family packer wrapping kSimSzudzikPackList."
```

---

## Task 7: `kSimPackedStep` builder and interp lemma

**Files**:

- Modify: `GebLean/Utilities/KSimSzudzikSimrec.lean`

The packed-step ER term used inside `boundedRec`.  Given
the K^sim arity parameters `a, k` and the per-component
step terms `g : Fin (k + 1) → ERMor1 (a + 1 + (k + 1))`
already translated to ER, build an ER term of arity
`a + 2` (counter index `0`, packed previous value `1`,
parameters `2..a+1`) whose interp packs the
component-wise application of each `g_j_ER` to the
unpacked previous values.

The arity `a + 2` is what `boundedRec` expects for its
`step` argument: slot `0` is the iteration index `j`,
slot `1` is the previous-iteration packed value, and
slots `2..a+1` are the K^sim recursion's parameters
`ȳ : Fin a`.  The resulting interp value is
`Nat.seqPack [g_0_ER (j, ȳ, prev_0..prev_k), ..., g_k_ER (...)]`.

- [ ] **Step 7.1: Add the per-component step-context
  builder**

The K^sim simrec step morphisms `g_j` have signature
`KMor1 (a + 1 + (k + 1))`, that is, arity
`(a + 1) + (k + 1)`.  In their call context, slot `0`
is the recursion variable (the iteration index), slots
`1..a` are the parameters `ȳ`, and slots `a + 1..a + k + 1`
are the previous-iteration values
`prev_0, …, prev_k`.

After translation, each `g_j_ER : ERMor1 (a + 1 + (k + 1))`.
We need to substitute its `(a + 1 + (k + 1))`-shaped input
context using the ambient `(a + 2)`-shaped
`(j, prev, ȳ)` context plus the `(k + 1)` unpacked
previous values.

Append a helper that builds the substitution family:

```lean
/-- Context substitution family for the simrec packed
step.  Translates the ambient `(a + 2)`-shaped step
context `(j, prev, ȳ)` plus the previous-iteration
packed value into the `(a + 1 + (k + 1))`-shaped K^sim
step context expected by each `g_j_ER`. -/
def kSimStepContext {a k : ℕ} :
    Fin (a + 1 + (k + 1)) → ERMor1 (a + 2) :=
  fun idx =>
    if h₀ : idx.val = 0 then
      ERMor1.proj (k := a + 2) ⟨0, by omega⟩
    else if h₁ : idx.val < a + 1 then
      ERMor1.proj (k := a + 2)
        ⟨idx.val - 1 + 2, by
          have := idx.isLt; omega⟩
    else
      kSimSzudzikUnpackAt (a + 1)
        (idx.val - (a + 1))
        |>.comp (fun j =>
          if h : j.val = 0 then
            ERMor1.proj (k := a + 2) ⟨1, by omega⟩
          else
            ERMor1.proj (k := a + 2)
              ⟨j.val + 1, by
                have := j.isLt; omega⟩)
```

(The trailing `.comp` substitutes the `(a + 1 + 1) = a + 2`-shaped
input of `kSimSzudzikUnpackAt`'s `(a + 1)`-arity-plus-one
context with: slot `0` = packed previous value (slot `1`
of the ambient context), slots `1..a + 1` = parameters
(slots `2..a + 1` of the ambient context).  The
implementer should examine the elaboration here with
`lean_goal` and adjust the index arithmetic if Lean
rejects any branch; the type signature pins the desired
result.)

- [ ] **Step 7.2: Add `kSimPackedStep` definition**

Append:

```lean
/-- Step-family packer for `simrec` translation: at
ambient context `(j, prev, ȳ)`, applies each `g_j_ER` to
the K^sim step context built by `kSimStepContext` and
Szudzik-packs the resulting `(k + 1)`-vector. -/
def kSimPackedStep {a k : ℕ}
    (g : Fin (k + 1) → ERMor1 (a + 1 + (k + 1))) :
    ERMor1 (a + 2) :=
  kSimSzudzikPackList
    (fun j =>
      ERMor1.comp (g j) kSimStepContext)
```

- [ ] **Step 7.3: Add the `kSimPackedStep` interp
  characterisation**

Append:

```lean
@[simp] theorem kSimPackedStep_interp {a k : ℕ}
    (g : Fin (k + 1) → ERMor1 (a + 1 + (k + 1)))
    (ctx : Fin (a + 2) → ℕ) :
    (kSimPackedStep g).interp ctx =
      Nat.seqPack
        ((List.finRange (k + 1)).map
          (fun j =>
            (g j).interp
              (fun idx =>
                kSimStepContext idx |>.interp ctx))) := by
  unfold kSimPackedStep
  rw [kSimSzudzikPackList_interp]
  simp only [List.map_map, Function.comp_def,
    ERMor1.interp_comp]
```

- [ ] **Step 7.4: Run `lake build`**

```bash
lake build GebLean.Utilities.KSimSzudzikSimrec
```

Expected: PASS, no warnings.

- [ ] **Step 7.5: Commit**

```bash
git add GebLean/Utilities/KSimSzudzikSimrec.lean
git commit -m "Add kSimPackedStep builder and interp lemma

Step-family packer for simrec translation: packs the
component-wise application of each step morphism to
the K^sim step context built from the ambient ER
context and the unpacked previous values."
```

---

## Task 8: `kSimTowerBound` for the simrec recursion

**Files**:

- Modify: `GebLean/Utilities/KSimSzudzikSimrec.lean`

The bound term passed to `ERMor1.boundedRec`.  The
tower-bound infrastructure in
`GebLean/LawvereERBoundComputable.lean` exposes
`ERMor1.towerBound : {n : ℕ} → ERMor1 n → ERMor1 n`
satisfying `(t.towerBound).interp ctx ≥ t.interp ctx`
pointwise.  For `boundedRec` we need a bound for the
nominal `Nat.rec` trace's value at every iteration.

The simrec packed iteration's value at iteration `j` is
`Nat.seqPack` of a `(k + 1)`-vector of values, each at
most the maximum of the per-step ER terms applied to the
ambient context and the previous-iteration values.  An
unconditional dominator is the tower bound of the packed
step term itself, evaluated at the worst-case packed
context.

A workable construction: take the tower bound of
`kSimPackedStep g` plus `1`, lifted to the
`(a + 1)`-arity bound shape required by `boundedRec`.

- [ ] **Step 8.1: Add `kSimTowerBound`**

Append:

```lean
/-- Bound term for the simrec packed recursion's
`boundedRec`.  Composes `towerBound` of the packed-step
term with a fixed re-indexing that turns the
`(a + 2)`-shaped step context into the `(a + 1)`-shaped
bound context expected by `boundedRec`.  The bound
expression is independent of the iteration counter and
dominates the per-iteration trace value uniformly. -/
def kSimTowerBound {a k : ℕ}
    (h : Fin (k + 1) → ERMor1 a)
    (g : Fin (k + 1) → ERMor1 (a + 1 + (k + 1))) :
    ERMor1 (a + 1) :=
  ERMor1.comp
    ((kSimPackedStep g).towerBound)
    (fun i =>
      if h₀ : i.val = 0 then
        ERMor1.proj (k := a + 1) ⟨0, by omega⟩
      else if h₁ : i.val = 1 then
        ERMor1.comp (kSimPackedBase h)
          (fun j =>
            ERMor1.proj (k := a + 1)
              ⟨j.val + 1, by
                have := j.isLt; omega⟩)
      else
        ERMor1.proj (k := a + 1)
          ⟨i.val - 1, by
            have := i.isLt; omega⟩)
```

This composes `(kSimPackedStep g).towerBound` (an ER
term of arity `a + 2`) with a substitution turning the
`(a + 1)`-shaped bound context (slot `0` = iteration
counter, slots `1..a` = parameters) into an
`(a + 2)`-shaped step context (slot `0` = counter, slot
`1` = packed previous value substituted with the base
pack, slots `2..a + 1` = parameters).

- [ ] **Step 8.2: Add the bound dominance lemma**

Append:

```lean
/-- The bound dominates the packed-recursion trace
uniformly in the iteration count.  The proof composes
`ERMor1.interp_le_towerBound` with the substitution
underlying `kSimTowerBound`.  The implementer should
expand `kSimTowerBound` and `kSimPackedStep` and use
`ERMor1.interp_le_towerBound`. -/
theorem kSimTowerBound_dominates {a k : ℕ}
    (h : Fin (k + 1) → ERMor1 a)
    (g : Fin (k + 1) → ERMor1 (a + 1 + (k + 1)))
    (j : ℕ) (params : Fin a → ℕ) :
    Nat.rec
      ((kSimPackedBase h).interp params)
      (fun i prev =>
        (kSimPackedStep g).interp
          (Fin.cons i (Fin.cons prev params)))
      j ≤
      (kSimTowerBound h g).interp
        (Fin.cons j params) := by
  -- Expand kSimTowerBound and apply
  -- ERMor1.interp_le_towerBound; the substitution
  -- builds a context where the towerBound's
  -- guarantee covers the recursion trace.
  -- See the spec doc, §"Data flow: the simrec
  -- case in detail".
  sorry
```

Note: this `sorry` is a placeholder pending tactic
exploration; the implementer must replace it with a
working proof before committing.  Use the Lean MCP
`lean_goal` and `lean_multi_attempt` skills, and the
`*-filler-deep` route under the `lean4` plugin if the
proof becomes long.  The dominance result follows from:

- `ERMor1.interp_le_towerBound` for an unconditional
  upper bound by the packed step's tower envelope;
- a small monotonicity argument showing the
  trace at iteration `j` is dominated by an iterated
  step over a context bounded above by the same
  envelope (possible because `towerBound` is monotone
  in its context sum).

Note from the project conventions in `CLAUDE.md`:
**No `sorry` may remain in committed code.**  This
plan deliberately uses `sorry` as a planning marker to
signal that the proof requires tactic exploration; the
task's "commit" step is gated on the proof being
discharged.

- [ ] **Step 8.3: Discharge the `sorry`**

Replace the `sorry` in `kSimTowerBound_dominates` with a
proof.  Recommended approach: use
`Nat.rec_le_self_of_step_le` or a direct induction on
`j`; at each step, use
`ERMor1.interp_le_towerBound` to bound the step's
output, then composability of `towerBound` under the
substitution.  Re-run `lake build` after each tactic
attempt; the goal is to remove the `sorry` entirely.

If the proof proves intractable inside the planned
shape, **escalate to the controller** (see
`subagent-driven-development.md`'s `BLOCKED` handling)
rather than weakening the lemma.  Possible adjustments
within the design contract:

- Strengthen the bound (e.g. use
  `tower (towerHeight + lh + a + 2)` of the param sum
  with a larger constant offset).
- Factor through an auxiliary "trace-to-bound" lemma
  expressing the recursion's value as
  `Nat.rec` of tower-bounded values and applying
  `tower_mono`.

- [ ] **Step 8.4: Run `lake build`**

```bash
lake build GebLean.Utilities.KSimSzudzikSimrec
```

Expected: PASS, no warnings, **no `sorry`**.

- [ ] **Step 8.5: Run `lake test`**

```bash
lake test
```

Expected: PASS.

- [ ] **Step 8.6: Commit**

```bash
git add GebLean/Utilities/KSimSzudzikSimrec.lean
git commit -m "Add kSimTowerBound and dominance lemma

Bound term for simrec's boundedRec, composed from the
packed-step term's towerBound and a substitution that
threads the base pack into the bound context.  The
dominance lemma confirms the bound covers the packed
recursion trace uniformly in the iteration count."
```

---

## Task 9: Create `GebLean/LawvereKSimER.lean` skeleton with atomic `kToER` cases

**Files**:

- Create: `GebLean/LawvereKSimER.lean`

Establish the new module that hosts `kToER`, `kToERN`,
the interp-preservation theorems, and the categorical
functor.  Implement the atomic constructors (`zero`,
`succ`, `proj`) of `kToER`, leaving `comp`, `raise`, and
`simrec` for subsequent tasks.

- [ ] **Step 9.1: Create the module skeleton**

Write to `GebLean/LawvereKSimER.lean`:

```lean
import GebLean.LawvereKSim
import GebLean.LawvereKSimInterp
import GebLean.LawvereKSimQuot
import GebLean.LawvereERQuot
import GebLean.Utilities.KSimSzudzikSimrec

/-!
# Forward translation `kToER : K^sim → ER`

Translation of K^sim term-language morphisms (depth ≤ 2)
to elementary-recursive `ERMor1` terms.  Atomic
constructors map to ER atoms; `comp` and `raise` recurse;
`simrec` at depth ≤ 2 (children at depth ≤ 1) is encoded
via Szudzik pairing and `ERMor1.boundedRec` with a tower
bound.

The function-level translation `kToER` is paired with a
multi-output companion `kToERN` and an
interp-preservation theorem `kToER_interp` /
`kToERN_interp`.  The translation is then lifted to a
categorical functor
`kToERFunctor : KSimMor 2 ⥤ LawvereERCat` using the
data-bearing `KMorNQuo.atDepth` Setoid quotient from
Phase 1's refactored `LawvereKSimQuot.lean`.

See `docs/plans/2026-04-29-lawvere-k-sim-ktoer-design.md`.
-/

namespace GebLean

end GebLean
```

- [ ] **Step 9.2: Add the `kToER` declaration with the
  atomic cases**

Append inside the `namespace GebLean` block:

```lean
/-- Forward translation: maps a K^sim morphism of level
≤ 2 to an `ERMor1` term of the same arity.  Defined by
structural recursion on the K^sim term; each case
discharges its level-bound assumption to the recursive
calls.  `simrec` requires `level ≤ 2` because its
children are at level ≤ 1 and translate to ER terms by
the recursive hypothesis (the case is filled in
subsequent tasks). -/
def kToER : {a : ℕ} → (f : KMor1 a) → f.level ≤ 2 →
    ERMor1 a
  | _, .zero,        _ => ERMor1.zeroN _
  | _, .succ,        _ => ERMor1.succ
  | _, .proj i,      _ => ERMor1.proj i
  | _, .comp _ _,    _ => sorry
  | _, .simrec _ _ _, _ => sorry
  | _, .raise _,     _ => sorry
```

The `sorry`s at the non-atomic constructors are
placeholders to be filled in Tasks 10–12.  This is a
planning marker; per `CLAUDE.md` no `sorry` may remain
in committed code.  In intermediate `lake build` runs
during this task only, the `sorry` warnings are
expected; they must be eliminated before the
**commit step of Task 12**, which is the only commit
covering the full `kToER` definition.

To avoid this `sorry`-warning regression in
intermediate commits, **defer the actual commit of
`GebLean/LawvereKSimER.lean` until Task 12's commit
step.**  Steps 9.3, 10.x, 11.x, 12.x are all "build but
do not commit".

- [ ] **Step 9.3: Run `lake build` to confirm the
  skeleton compiles**

```bash
lake build GebLean.LawvereKSimER
```

Expected: PASS with `declaration uses 'sorry'` warnings
only (these are eliminated in Tasks 10–12).  **Do not
commit yet.**

---

## Task 10: `kToER` `comp` case

**Files**:

- Modify: `GebLean/LawvereKSimER.lean`

Add the `comp` translation: recurse on the function part
and on each argument, then `ERMor1.comp` the results.
The level-bound hypothesis on `comp f gs` decomposes via
`Nat.max_le` and `Finset.sup_le` into bounds on `f` and
each `gs i`.

- [ ] **Step 10.1: Replace the `comp` `sorry`**

Replace the `comp` arm of `kToER` (in
`GebLean/LawvereKSimER.lean`) with:

```lean
  | _, .comp f gs,   h => by
      have hf : f.level ≤ 2 := by
        have := Nat.le_of_max_le_left
          (a := f.level)
          (b := Finset.univ.sup
            (fun i => (gs i).level))
          (le_trans (Nat.le_refl _)
            (by simpa [KMor1.level] using h))
        exact this
      have hgs : ∀ i, (gs i).level ≤ 2 := fun i => by
        have hsup := Nat.le_of_max_le_right
          (a := f.level)
          (b := Finset.univ.sup
            (fun i => (gs i).level))
          (le_trans (Nat.le_refl _)
            (by simpa [KMor1.level] using h))
        exact le_trans
          (Finset.le_sup
            (f := fun i => (gs i).level)
            (Finset.mem_univ i))
          hsup
      exact ERMor1.comp (kToER f hf)
        (fun i => kToER (gs i) (hgs i))
```

Replace `by simpa [KMor1.level] using h` with whatever
`simp`-normal form Lean accepts for unfolding the
`KMor1.level` of `comp`; the implementer can try
`unfold KMor1.level at h` first and adjust as needed.

- [ ] **Step 10.2: Run `lake build`**

```bash
lake build GebLean.LawvereKSimER
```

Expected: PASS with remaining `sorry` warnings only on
`simrec` and `raise`.  **Do not commit yet.**

---

## Task 11: `kToER` `raise` case

**Files**:

- Modify: `GebLean/LawvereKSimER.lean`

Add the `raise` translation: recurse on the inner term.
By the level rule
`(KMor1.raise f).level = f.level + 1`, a bound
`(raise f).level ≤ 2` implies `f.level ≤ 1 ≤ 2`, so
the recursive call is well-typed.

- [ ] **Step 11.1: Replace the `raise` `sorry`**

Replace the `raise` arm of `kToER` with:

```lean
  | _, .raise f,     h => by
      have hf : f.level ≤ 2 := by
        have := h
        unfold KMor1.level at this
        omega
      exact kToER f hf
```

- [ ] **Step 11.2: Run `lake build`**

```bash
lake build GebLean.LawvereKSimER
```

Expected: PASS with `sorry` warning only on `simrec`.
**Do not commit yet.**

---

## Task 12: `kToER` `simrec` case

**Files**:

- Modify: `GebLean/LawvereKSimER.lean`

The bulk of the translation: encode the simultaneous
primitive recursion at depth 2 (children at depth ≤ 1)
via the C5 helpers (`kSimPackedBase`, `kSimPackedStep`,
`kSimTowerBound`) and `ERMor1.boundedRec`, then project
the requested output index via `kSimSzudzikUnpackAt`.

- [ ] **Step 12.1: Replace the `simrec` `sorry`**

Replace the `simrec` arm of `kToER` with:

```lean
  | _, .simrec (a := a) (k := k) i h g, hyp => by
      have hh : ∀ j, (h j).level ≤ 1 := fun j => by
        have := hyp
        unfold KMor1.level at this
        have hsup_le : Finset.univ.sup
            (fun j => (h j).level) ≤ 1 := by omega
        exact le_trans
          (Finset.le_sup (f := fun j => (h j).level)
            (Finset.mem_univ j))
          hsup_le
      have hg_lvl : ∀ j, (g j).level ≤ 1 := fun j => by
        have := hyp
        unfold KMor1.level at this
        have hsup_le : Finset.univ.sup
            (fun j => (g j).level) ≤ 1 := by omega
        exact le_trans
          (Finset.le_sup (f := fun j => (g j).level)
            (Finset.mem_univ j))
          hsup_le
      let h_ER : Fin (k + 1) → ERMor1 a :=
        fun j => kToER (h j)
          (le_trans (hh j) (by norm_num))
      let g_ER : Fin (k + 1) → ERMor1 (a + 1 + (k + 1)) :=
        fun j => kToER (g j)
          (le_trans (hg_lvl j) (by norm_num))
      let recur : ERMor1 (a + 1) :=
        ERMor1.boundedRec
          (kSimPackedBase h_ER)
          (kSimPackedStep g_ER)
          (kSimTowerBound h_ER g_ER)
      exact ERMor1.comp
        (kSimSzudzikUnpackAt a i.val) (fun j =>
          if h_eq : j.val = 0 then recur
          else ERMor1.proj (k := a + 1)
            ⟨j.val, by
              have := j.isLt; omega⟩)
```

The composition with `kSimSzudzikUnpackAt a i.val`
projects the `i`-th component out of the packed
recursion result.  The `if`-branch in the substitution
selects the recursion in slot `0` (the counter slot of
`kSimSzudzikUnpackAt a i.val`'s arity-`(a + 1)` shape)
and forwards remaining parameters straight through.

- [ ] **Step 12.2: Run `lake build`**

```bash
lake build GebLean.LawvereKSimER
```

Expected: PASS with no `sorry` warnings, no other
warnings.

- [ ] **Step 12.3: Run `lake test`**

```bash
lake test
```

Expected: PASS.

- [ ] **Step 12.4: Commit**

```bash
git add GebLean/LawvereKSimER.lean
git commit -m "Add kToER forward translation (KMor1 level≤2 → ERMor1)

Per-constructor structural recursion translating each
K^sim morphism of level ≤ 2 to an ERMor1 term.  Atomic
constructors map directly; comp and raise recurse;
simrec encodes the simultaneous-recursion vector via
Szudzik pairing and runs it through ERMor1.boundedRec
with a tower-height bound from kSimTowerBound, then
projects the requested output via kSimSzudzikUnpackAt."
```

---

## Task 13: Multi-output `kToERN`

**Files**:

- Modify: `GebLean/LawvereKSimER.lean`

Pointwise lift of `kToER` to the multi-output Lawvere
arity.

- [ ] **Step 13.1: Add `kToERN` definition**

Append to `GebLean/LawvereKSimER.lean`:

```lean
/-- Multi-output forward translation: pointwise lift of
`kToER` over a `KMorN` family. -/
def kToERN {a m : ℕ} (f : KMorN a m)
    (h : ∀ i, (f i).level ≤ 2) : ERMorN a m :=
  fun i => kToER (f i) (h i)
```

- [ ] **Step 13.2: Run `lake build`**

```bash
lake build GebLean.LawvereKSimER
```

Expected: PASS, no warnings.

- [ ] **Step 13.3: Commit**

```bash
git add GebLean/LawvereKSimER.lean
git commit -m "Add kToERN multi-output forward translation

Pointwise lift of kToER over a KMorN family."
```

---

## Task 14: Interp-preservation theorem `kToER_interp`

**Files**:

- Modify: `GebLean/LawvereKSimER.lean`

The principal correctness theorem: at every context, the
ER interpretation of the translated term equals the
K^sim interpretation of the original.

- [ ] **Step 14.1: Add the theorem statement and atomic
  cases**

Append:

```lean
/-- Interp preservation of `kToER`: the ER
interpretation of `kToER f h` equals the K^sim
interpretation of `f`, at every context. -/
theorem kToER_interp :
    {a : ℕ} → (f : KMor1 a) → (h : f.level ≤ 2) →
      (ctx : Fin a → ℕ) →
      (kToER f h).interp ctx = f.interp ctx
  | _, .zero,        _, _   => by
      simp [kToER, KMor1.interp_zero]
  | _, .succ,        _, _   => by
      simp [kToER, KMor1.interp_succ]
  | _, .proj _,      _, _   => by
      simp [kToER, KMor1.interp_proj]
  | _, .comp f gs,   h, ctx => by
      simp only [kToER, KMor1.interp_comp,
        ERMor1.interp_comp]
      congr 1
      funext i
      exact kToER_interp (gs i) _ ctx
  | _, .raise f,     h, ctx => by
      simp only [kToER, KMor1.interp_raise]
      exact kToER_interp f _ ctx
  | _, .simrec _ _ _, _, _   => by
      sorry
```

The `comp` and `raise` cases reduce by interp-rewriting
plus the inductive hypothesis.  The `simrec` case is
filled in Step 14.2.

- [ ] **Step 14.2: Discharge the `simrec` case**

Replace the `simrec` `sorry` with a proof composing:

- `ERMor1.interp_comp` (from `LawvereER.lean`) for the
  outer composition with `kSimSzudzikUnpackAt i.val`.
- `kSimSzudzikUnpackAt_packList` (Task 5) for the
  round-trip property.
- `kToER_interp` recursive hypotheses on each `h j` and
  `g j`.
- `KMor1.interp_simrec` and `KMor1.simrecVec`
  (from `LawvereKSimInterp.lean`) characterising the
  K^sim simrec's interp.
- `ERMor1.boundedRec_eq_natRec_of_bounded` (from
  `Utilities/ERArith.lean`) reducing `boundedRec` to
  plain `Nat.rec` when the bound dominates, using
  `kSimTowerBound_dominates` (Task 8).

The proof skeleton is:

```lean
  | _, .simrec (a := a) (k := k) i h g, hyp, ctx => by
      simp only [kToER]
      -- unfold the recursion variable from ctx
      let recVar : ℕ := ctx 0
      let params : Fin a → ℕ := fun j => ctx (Fin.succ j)
      change _ = (KMor1.simrec i h g).interp ctx
      rw [KMor1.interp_simrec]
      -- The LHS reduces, after kSimSzudzikUnpackAt_packList,
      -- to the i-th component of a Nat.seqPack of the
      -- packed recursion's per-iteration values.  By
      -- boundedRec_eq_natRec_of_bounded (with
      -- kSimTowerBound_dominates), this packed recursion
      -- equals Nat.rec of the per-iteration packed values.
      -- The induction step matches simrecVec by
      -- kSimPackedBase_interp / kSimPackedStep_interp +
      -- the round-trip.  Combining, both sides agree.
      sorry
```

The `sorry` is a planning marker; the implementer must
discharge it before commit.  Use `lean_goal` to
inspect intermediate states; the proof's structure is a
two-level induction (the outer combination of bounded-
to-Nat-rec reduction; the inner equation of `Nat.rec`
trace with `simrecVec`).

If the proof grows beyond 60 lines, factor out
**lemma** `kToER_simrec_packed_recursion_eq_simrecVec`
encapsulating the inner `Nat.rec` equation (per
`CLAUDE.md`'s factoring-out-lemmas advice).  Place this
auxiliary lemma immediately above the main theorem.

- [ ] **Step 14.3: Run `lake build`**

```bash
lake build GebLean.LawvereKSimER
```

Expected: PASS, no warnings, no `sorry`.

- [ ] **Step 14.4: Run `lake test`**

```bash
lake test
```

Expected: PASS.

- [ ] **Step 14.5: Commit**

```bash
git add GebLean/LawvereKSimER.lean
git commit -m "Prove kToER_interp: K^sim → ER interp preservation

Structural induction on KMor1 terms.  Atomic cases
reduce by interp rewrites; comp and raise use the
inductive hypothesis directly.  The simrec case
combines kSimSzudzikUnpackAt_packList,
boundedRec_eq_natRec_of_bounded with
kSimTowerBound_dominates, KMor1.simrecVec, and the
recursive interp hypotheses on each h_j and g_j."
```

---

## Task 15: Interp-preservation theorem `kToERN_interp`

**Files**:

- Modify: `GebLean/LawvereKSimER.lean`

Pointwise lift of `kToER_interp` to multi-output.

- [ ] **Step 15.1: Add the theorem**

Append:

```lean
/-- Interp preservation of `kToERN`. -/
theorem kToERN_interp {a m : ℕ} (f : KMorN a m)
    (h : ∀ i, (f i).level ≤ 2) (ctx : Fin a → ℕ) :
    (kToERN f h).interp ctx = f.interp ctx := by
  funext i
  simp only [kToERN, ERMorN.interp, KMorN.interp]
  exact kToER_interp (f i) (h i) ctx
```

- [ ] **Step 15.2: Run `lake build`**

```bash
lake build GebLean.LawvereKSimER
```

Expected: PASS, no warnings.

- [ ] **Step 15.3: Commit**

```bash
git add GebLean/LawvereKSimER.lean
git commit -m "Prove kToERN_interp: pointwise lift of kToER_interp"
```

---

## Task 16: Functor `kToERFunctor` definition

**Files**:

- Modify: `GebLean/LawvereKSimER.lean`

The categorical packaging: lift the function-level
translation to a functor between the depth-2 K^sim
quotient category and the ER quotient category.

The action on morphisms uses `Quotient.lift` on the
data-bearing depth witness from Task 1: for any
`raw : KMorNQuo.AtDepthRaw 2 h.hom`, the ER quotient
class `Quotient.mk _ (kToERN raw.rep raw.rep_level)` is
independent of the choice of `raw` (because all `raw`
values are Setoid-equivalent under the always-true
relation, and the result type is a Quotient itself; we
exploit `Subsingleton.allEq` rather than needing to
prove an equation between the ER classes for two
different reps).

The well-definedness equation we *do* need is that
two raw witnesses for the *same* `h.hom` produce ER
classes with the same interpretation.  Both reps have
the same K^sim interp (since they represent the same
quotient class), so by `kToERN_interp` both ER images
have the same interp, so they live in the same
`erMorNSetoid` equivalence class.

- [ ] **Step 16.1: Identify or define `erMorNSetoid` and
  `ERMorNQuo`**

Inspect `GebLean/LawvereERQuot.lean` to determine the
existing names for the ER setoid and its quotient.
Common candidates: `erMorNSetoid n m` and
`ERMorNQuo n m`.  Adjust subsequent steps to use the
correct names.

```bash
grep -n "Setoid\|Quotient\|ERMor.*Quo" \
  GebLean/LawvereERQuot.lean | head -20
```

If `erMorNSetoid` exists with the same shape as
`kMorNSetoid` (extensional equality at every context),
the subsequent code applies directly.  If the ER
quotient is structured differently, adjust the
substitutions accordingly; the spec allows this without
contract change.

- [ ] **Step 16.2: Add the functor's `obj` and `map`
  fields**

Append to `GebLean/LawvereKSimER.lean`:

```lean
/-- The forward translation lifts to a functor from the
depth-2 K^sim Lawvere category to the ER Lawvere
category.  On objects it is the identity; on morphisms
it extracts the level-≤-2 representative via
`Quotient.lift`, applies `kToERN`, and re-quotients in
the ER category. -/
def kToERFunctor :
    CategoryTheory.Functor
      (LawvereKSimDCat 2)
      LawvereERCat where
  obj n := n
  map {n m} h :=
    Quotient.liftOn
      (s := kMorNQuoAtDepthSetoid 2 h.hom)
      h.depth_witness
      (fun raw =>
        Quotient.mk (erMorNSetoid n m)
          (kToERN raw.rep raw.rep_level))
      (fun raw₁ raw₂ _ => by
        apply Quotient.sound
        intro ctx
        rw [kToERN_interp, kToERN_interp]
        have h_eq : raw₁.rep_eq.symm.trans raw₂.rep_eq
            = (Quotient.mk _ raw₁.rep =
              Quotient.mk _ raw₂.rep) := rfl
        have hext : ∀ ctx,
            raw₁.rep.interp ctx = raw₂.rep.interp ctx :=
          Quotient.exact (raw₁.rep_eq.trans
            raw₂.rep_eq.symm)
        exact hext ctx)
  map_id _ := by
    sorry
  map_comp _ _ := by
    sorry
```

The `map_id` and `map_comp` `sorry`s are filled in
Task 17.

- [ ] **Step 16.3: Run `lake build`**

```bash
lake build GebLean.LawvereKSimER
```

Expected: PASS with `sorry` warnings only on `map_id`
and `map_comp`.  **Do not commit yet.**

---

## Task 17: Functor laws `map_id` and `map_comp`

**Files**:

- Modify: `GebLean/LawvereKSimER.lean`

Discharge the functoriality obligations for
`kToERFunctor`.

- [ ] **Step 17.1: Discharge `map_id`**

Replace the `map_id` `sorry` with:

```lean
  map_id n := by
    -- The identity in the depth-2 K^sim category has
    -- depth_witness = KMorNQuo.id_atDepth, whose rep
    -- is KMorN.id n with all components KMor1.proj _,
    -- each at level 0.  kToERN of this rep is
    -- ERMorN.id n.
    apply Quotient.sound
    intro ctx
    funext i
    -- Unfold the lift and reduce to interp equality.
    -- kToER of KMor1.proj i is ERMor1.proj i; the
    -- identity case is straightforward.
    simp [kToERN, kToER, KMorN.id, KMor1.level,
      ERMorN.id, ERMor1.interp_proj,
      KMor1.interp_proj]
```

The implementer should adjust the `simp` set if Lean
rejects any lemma name; use `lean_goal` and
`lean_local_search` to find the correct ones.

- [ ] **Step 17.2: Discharge `map_comp`**

Replace the `map_comp` `sorry` with:

```lean
  map_comp f g := by
    -- f, g : KSimMor 2.  Their composition has
    -- depth_witness = comp_atDepth f.depth_witness
    -- g.depth_witness, whose rep is the KMorN.comp of
    -- the constituent reps.  kToERN distributes over
    -- KMorN.comp pointwise, matching ERMorN.comp.
    apply Quotient.sound
    intro ctx
    -- The proof reduces to a pointwise interp equation
    -- discharged by kToER_interp and KMor1.interp_comp.
    funext i
    -- Use Quotient.ind on f.depth_witness and
    -- g.depth_witness to extract concrete reps.
    sorry
```

The `sorry` is a planning marker; the implementer
discharges it by induction on
`f.depth_witness` and `g.depth_witness` to extract
representatives, then computing the ER and K^sim
interps on both sides via `kToER_interp` and
`kToERN_interp`.

If the proof grows beyond 30 lines, factor out a lemma
`kToERN_comp_interp` stating that
`(kToERN (KMorN.comp gr fr) _).interp ctx
   = (kToERN gr _).interp ((kToERN fr _).interp ctx)`,
which simplifies the main proof to
`Quotient.sound` applied to a single interp equation.

- [ ] **Step 17.3: Run `lake build`**

```bash
lake build GebLean.LawvereKSimER
```

Expected: PASS, no warnings, no `sorry`.

- [ ] **Step 17.4: Run `lake test`**

```bash
lake test
```

Expected: PASS.

- [ ] **Step 17.5: Commit**

```bash
git add GebLean/LawvereKSimER.lean
git commit -m "Add kToERFunctor : KSimMor 2 ⥤ LawvereERCat with laws

Lifts the function-level kToERN to a categorical
functor between the depth-2 K^sim quotient category
and the ER quotient category.  Action on morphisms
uses Quotient.lift on the data-bearing depth witness
from the refactored KMorNQuo.atDepth.  Functor laws
follow by Quotient.sound applied to interp equalities."
```

---

## Task 18: Per-constructor `#guard` spot checks (Tier 1)

**Files**:

- Create: `GebLeanTests/LawvereKSimER.lean`

Smoke-test each atomic constructor of `kToER` at small
inputs and verify the ER interpretation matches the
K^sim interpretation.

- [ ] **Step 18.1: Create the test file with atomic
  spot checks**

Write to `GebLeanTests/LawvereKSimER.lean`:

```lean
import GebLean.LawvereKSimER
import Mathlib.Data.Fin.VecNotation

/-!
# Tier 1 tests for `kToER`

Per-constructor `#guard` spot checks confirming that
applying `kToER` to each atomic K^sim constructor at
small contexts produces the expected ERMor1 value.
-/

open GebLean

private def ctx0 : Fin 0 → ℕ := Fin.elim0
private def ctx1 (x : ℕ) : Fin 1 → ℕ := fun _ => x
private def ctx2 (x y : ℕ) : Fin 2 → ℕ := ![x, y]
private def ctx3 (x y z : ℕ) : Fin 3 → ℕ := ![x, y, z]

-- zero at empty context: kToER preserves the constant
-- 0.
private theorem zero_level :
    (KMor1.zero (n := 0)).level ≤ 2 := by
  simp [KMor1.level]

#guard
  (kToER (KMor1.zero (n := 0)) zero_level).interp
    ctx0 == 0

-- succ: kToER preserves the successor function.
private theorem succ_level :
    KMor1.succ.level ≤ 2 := by
  simp [KMor1.level]

#guard
  (kToER KMor1.succ succ_level).interp (ctx1 5) == 6

-- proj: kToER preserves projection.
private theorem proj_level {n : ℕ} (i : Fin n) :
    (KMor1.proj i).level ≤ 2 := by
  simp [KMor1.level]

#guard
  (kToER (KMor1.proj (0 : Fin 2))
    (proj_level _)).interp (ctx2 7 3) == 7

#guard
  (kToER (KMor1.proj (1 : Fin 2))
    (proj_level _)).interp (ctx2 7 3) == 3

-- raise: identity on interp.
private theorem raise_succ_level :
    (KMor1.raise KMor1.succ).level ≤ 2 := by
  simp [KMor1.level]

#guard
  (kToER (KMor1.raise KMor1.succ)
    raise_succ_level).interp (ctx1 5) == 6

-- comp: kToER preserves composition.
private def succProj0 : KMor1 2 :=
  KMor1.comp KMor1.succ
    (fun _ : Fin 1 => KMor1.proj (0 : Fin 2))

private theorem succProj0_level : succProj0.level ≤ 2 := by
  simp [succProj0, KMor1.level, Finset.sup]

#guard
  (kToER succProj0 succProj0_level).interp
    (ctx2 7 3) == 8
```

- [ ] **Step 18.2: Run `lake test`**

```bash
lake test
```

Expected: PASS.

- [ ] **Step 18.3: Commit**

```bash
git add GebLeanTests/LawvereKSimER.lean
git commit -m "Tier 1 tests: per-constructor kToER spot checks"
```

---

## Task 19: `addK` round-trip test (Tier 2)

**Files**:

- Modify: `GebLeanTests/LawvereKSimER.lean`

End-to-end exercise of the `simrec` translation on the
existing `addK` term (Phase 1 Task 10): translate to ER
and verify that the ER interpretation computes
addition.

- [ ] **Step 19.1: Add the addK test fixture**

Append to `GebLeanTests/LawvereKSimER.lean`:

```lean
/-- Addition `λ x y. x + y` as a level-1 K^sim composite
(reproduced from `GebLeanTests/LawvereKSimInterp.lean`):
simrec on the first argument with base `proj 0` of the
parameter slot and step `succ` applied to the previous
value (in slot 2 of the step context). -/
private def addK : KMor1 2 :=
  KMor1.simrec (k := 0) (a := 1)
    (0 : Fin 1)
    (fun _ : Fin 1 => KMor1.proj (0 : Fin 1))
    (fun _ : Fin 1 =>
      KMor1.comp KMor1.succ
        (fun _ : Fin 1 => KMor1.proj (2 : Fin 3)))

-- The simrec adds 1 to the max of children (level 0)
-- so addK.level = 1 ≤ 2.
private theorem addK_level : addK.level ≤ 2 := by
  decide

private def addK_ER : ERMor1 2 := kToER addK addK_level

#guard addK_ER.interp (ctx2 3 5) == 8
#guard addK_ER.interp (ctx2 0 0) == 0
#guard addK_ER.interp (ctx2 7 1) == 8
#guard addK_ER.interp (ctx2 4 4) == 8
```

- [ ] **Step 19.2: Run `lake test`**

```bash
lake test
```

Expected: PASS.  These tests validate that the entire
simrec translation pipeline (Szudzik pack/unpack,
`boundedRec`, tower bound) produces a correct ER term
on a known small example.

- [ ] **Step 19.3: Commit**

```bash
git add GebLeanTests/LawvereKSimER.lean
git commit -m "Tier 2 test: addK simrec end-to-end translation"
```

---

## Task 20: Functor `F` sanity test (Tier 3)

**Files**:

- Modify: `GebLeanTests/LawvereKSimER.lean`

Verify that the categorical packaging (functor
`kToERFunctor`) exposes the same translation as the
function-level `kToER`.

- [ ] **Step 20.1: Add the functor sanity test**

Append:

```lean
/-- The level-1 simrec `addK` lifted to a `KSimMor 2`
value via the data-bearing depth witness.  `addK`
itself is a `KMor1 2` (arity 2 input); wrapping it as
the unique component of a singleton `KMorN 2 1` family
gives a depth-2 K^sim morphism `2 ⟶ 1`. -/
private def addK_KSimMor : KSimMor 2 2 1 :=
  ⟨Quotient.mk _ (fun _ : Fin 1 => addK),
    Quotient.mk _
      { rep        := fun _ : Fin 1 => addK
        rep_level  := fun _ => addK_level
        rep_eq     := rfl }⟩

private def addK_ER_via_F : ERMorNQuo 2 1 :=
  kToERFunctor.map addK_KSimMor

-- Pick a representative; verify its interp.
-- Quotient.lift on addK_ER_via_F yields a function
-- from the rep to ℕ; we exercise the functor's
-- translation by lifting and applying interp pointwise.
#guard
  (Quotient.lift
    (s := erMorNSetoid 2 1)
    (fun (rep : ERMorN 2 1) => rep.interp (ctx2 3 5) 0)
    (fun a b hab => by
      have := hab (ctx2 3 5)
      exact congrFun this 0)
    addK_ER_via_F) == 8
```

If `ERMorNQuo` is named differently in
`GebLean/LawvereERQuot.lean` (cf. Task 16's grep step),
adjust the type annotation accordingly.  Likewise if
the underlying `kToERFunctor.map` action returns a
different name for the ER quotient class type.

- [ ] **Step 20.2: Run `lake test`**

```bash
lake test
```

Expected: PASS.

- [ ] **Step 20.3: Commit**

```bash
git add GebLeanTests/LawvereKSimER.lean
git commit -m "Tier 3 test: kToERFunctor sanity check on addK"
```

---

## Task 21: Re-export new modules and register tests

**Files**:

- Modify: `GebLean.lean`
- Modify: `GebLeanTests.lean`

Make the new modules visible from the library entry
point and register the test module so `lake test`
exercises it.

- [ ] **Step 21.1: Add the import lines to `GebLean.lean`**

Add to `GebLean.lean`, in alphabetical order with the
existing imports (`import GebLean.LawvereKSimQuot` is
already present from Phase 1):

```lean
import GebLean.LawvereKSimER
import GebLean.Utilities.KSimSzudzikSimrec
```

The `LawvereKSimER` import goes near the other
`LawvereKSim*` imports; the
`Utilities.KSimSzudzikSimrec` import goes near the
other `Utilities.*` imports.

- [ ] **Step 21.2: Add the test import to
  `GebLeanTests.lean`**

Add to `GebLeanTests.lean`:

```lean
import GebLeanTests.LawvereKSimER
```

Place it near the other `LawvereKSim*` test imports.

- [ ] **Step 21.3: Run `lake build` and `lake test`**

```bash
lake build
lake test
```

Expected: PASS for both, no warnings.

- [ ] **Step 21.4: Commit**

```bash
git add GebLean.lean GebLeanTests.lean
git commit -m "Re-export LawvereKSimER and KSimSzudzikSimrec modules

Register the new forward-translation modules in the
library entry point and the test driver."
```

---

## Task 22: Final verification

**Files**:

- (no source modifications)

Confirm the full sub-project's build state is clean and
audits the deliverables.

- [ ] **Step 22.1: Full build**

```bash
lake build
```

Expected: PASS, no warnings, no errors.

- [ ] **Step 22.2: Full test suite**

```bash
lake test
```

Expected: PASS.  All Phase 1 K^sim tests and the new
Phase 2 sub-project 1 tests should run successfully.

- [ ] **Step 22.3: `sorry` audit**

```bash
grep -rn "sorry\|admit" GebLean/LawvereKSimER.lean \
  GebLean/Utilities/KSimSzudzikSimrec.lean \
  GebLeanTests/LawvereKSimER.lean
```

Expected: no matches.  If any are found, return to the
relevant task and discharge them before considering
the sub-project complete.

- [ ] **Step 22.4: Banned-word audit**

```bash
PATTERN='fundamental|insight|advanced|simple|simpler'
PATTERN+='|advantage|benefit|important|challenge'
PATTERN+='|incomplete|future|issue|problem|block'
grep -rniE "$PATTERN" \
  GebLean/LawvereKSimER.lean \
  GebLean/Utilities/KSimSzudzikSimrec.lean \
  GebLeanTests/LawvereKSimER.lean
```

Expected: no matches in source comments or docstrings.
If any are found, rephrase per `CLAUDE.md`'s style
guidelines.

- [ ] **Step 22.5: Markdown lint of the spec and plan**

```bash
markdownlint-cli2 \
  docs/plans/2026-04-29-lawvere-k-sim-ktoer-design.md \
  docs/plans/2026-04-29-lawvere-k-sim-ktoer-plan.md
```

Expected: no warnings.  Fix any reported issues.

- [ ] **Step 22.6: Confirm interp-preservation discipline**

For each helper introduced in
`GebLean/Utilities/KSimSzudzikSimrec.lean`, confirm
there is at least one `@[simp]`-tagged interp lemma
characterising its closed-form behaviour:

- `kSimSzudzikPackList`: `kSimSzudzikPackList_zero_interp`,
  `kSimSzudzikPackList_succ_interp`.
- `kSimSzudzikUnpackAt`: `kSimSzudzikUnpackAt_zero_interp`.
- `kSimPackedBase`: `kSimPackedBase_interp`.
- `kSimPackedStep`: `kSimPackedStep_interp`.

If any helper lacks an interp lemma, add one.  This
enforces the bottom-up named-composite discipline (P10:
interpret-and-verify).

- [ ] **Step 22.7: Commit any audit fixes (if needed)**

If Steps 22.3–22.6 surfaced any required fixes, commit
them under a message of the form:

```bash
git commit -m "Final verification fixes: <short description>"
```

If no fixes were needed, no commit is required.

---

## Summary of deliverables

By the end of Task 22, the repository contains:

- A data-bearing `KMorNQuo.atDepth` Setoid quotient
  refactor in `GebLean/LawvereKSimQuot.lean`.
- A new `GebLean/Utilities/KSimSzudzikSimrec.lean`
  with `kSimSzudzikPackList`, `kSimSzudzikUnpackAt`,
  `kSimPackedBase`, `kSimPackedStep`,
  `kSimTowerBound`, the round-trip and dominance
  lemmas, and per-helper interp characterisations.
- A new `GebLean/LawvereKSimER.lean` with `kToER`,
  `kToERN`, `kToER_interp`, `kToERN_interp`, and the
  functor `kToERFunctor : KSimMor 2 ⥤ LawvereERCat`.
- A new `GebLeanTests/LawvereKSimER.lean` with three
  tiers of `#guard` tests (atomic spot checks,
  `addK` end-to-end, functor sanity).
- Updated re-export files (`GebLean.lean`,
  `GebLeanTests.lean`).

The categorical equivalence
`KSimMor 2 ≌ LawvereERCat` is **not** complete after
this sub-project — it requires the backward direction
(sub-project 4) and supporting infrastructure
(sub-projects 2 and 3).  The deliverable here is a
complete, verified forward functor, which is one of the
two functors that will eventually be assembled into
the equivalence.
