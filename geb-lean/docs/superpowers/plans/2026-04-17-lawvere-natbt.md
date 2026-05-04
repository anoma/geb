# LawvereNatBT Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan task-by-task.
> Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Build `LawvereNatBT`, a two-sorted Lawvere theory over ℕ
and labeled BT, with a finite-limit completion `LawvereNatBTLex`,
categorically equivalent to `LawvereER` via Szudzik-based bridges.

**Architecture:** Two-sorted terms indexed by `(n, m) : ℕ × ℕ` and
output sort `{.nat, .bt}`.  Generators: LawvereER's arithmetic on the
ℕ side, `leaf / node / proj / comp / foldBT` on the BT side, and
bridges `encodeBT / decodeBT`.  Equational content given by
extensional equality of interpretations.  Equivalence with
`LawvereER` realized by the embedding `n ↦ (n, 0)`, whose
essential-surjectivity witness is iterated Szudzik packing.

**Tech Stack:** Lean 4 with mathlib (`CategoryTheory`,
`Nat.Pairing`).  Reuses existing project infrastructure:
`GebLean/LawvereER.lean`, `GebLean/LawvereERQuot.lean`,
`GebLean/LawvereBT.lean`, `GebLean/LawvereBTPrimrec.lean`
(`encodeBT`/`decodeBT`), `GebLean/LawvereTreeER*.lean`
(Phase 4g.1 unlabeled tree theory, kept as a parallel development).

**Design spec:**
`docs/superpowers/specs/2026-04-17-lawvere-natbt-design.md`.

**Workstream tracker entry:**
`.session/workstreams/lawvere-elementary-recursive.md`.

---

## File Structure

### Library files to create (under `GebLean/`)

| File | Responsibility |
|---|---|
| `LawvereNatBT.lean` | Labeled `BTL` inductive; `NatBTMor1` terms; tuples `NatBTMorN`; structural interpretation; id and comp at the tuple level. |
| `LawvereNatBTQuot.lean` | Extensional-equality setoid; `NatBTMorNQuo` quotient; `Category LawvereNatBTCat`; `HasChosenFiniteProducts`. |
| `LawvereNatBTInterp.lean` | Interpretation functor `LawvereNatBTCat ⥤ Type`; faithfulness. |
| `LawvereNatBT0.lean` | `isNatBT0` predicate; `LawvereNatBT0Cat` via `FullSubcategory`; restricted `HasChosenFiniteProducts`; on-the-nose isomorphism `LawvereERCat ≅ LawvereNatBT0Cat`. |
| `LawvereNatBTEquiv.lean` | Essential surjectivity of `natBT0Inclusion : LawvereNatBT0Cat ↪ LawvereNatBTCat` via Szudzik packing; composition into the categorical equivalence `LawvereERCat ≃ LawvereNatBTCat`. |
| `LawvereNatBTTransport.lean` | Ackermann non-fullness and tetration non-elementarity, transported across the equivalence. |
| `LawvereNatBTLex.lean` | `LawvereNatBTLexCat` via decidable subobjects; `HasChosenFiniteProducts`; `HasChosenEqualizers`; `HasChosenFiniteLimits`. |
| `LawvereNatBTSubtypes.lean` | Unlabeled BT subtype; finite-alphabet BT subtype; faithful embedding `LawvereTreeER ↪ LawvereNatBT`. |

### Test files to create (under `GebLeanTests/`)

One test module per library file, exercising small concrete examples
and `#guard` assertions.

### Files to modify

* `GebLean.lean` — add imports for each new library module.
* `GebLeanTests.lean` — add imports for each new test module.
* `.session/workstreams/lawvere-elementary-recursive.md` — mark the
  sub-project complete on finish.

---

## Stage α: base theory

### Task 1: Decide labeled BT representation and create `BTL`

**Files:**

* Create: `GebLean/LawvereNatBT.lean`

**Design note:** the spec left the labeled BT implementation open
between (a) a new inductive `BTL` with `leaf : ℕ → BTL` and
`node : BTL → BTL → BTL`, and (b) a polynomial-functor
parameterization.  This plan commits to route (a), direct inductive,
for readability.  If polynomial-functor route is preferred later, the
downstream lemmas are mechanical to port.

- [ ] **Step 1: Create the file with imports and header**

```lean
import GebLean.LawvereER
import GebLean.LawvereERQuot
import GebLean.LawvereBT
import GebLean.LawvereBTPrimrec

/-!
# Two-Sort Lawvere Theory over ℕ and Labeled Binary Trees

Morphisms indexed by domain arity `(n, m) : ℕ × ℕ` and output
sort (`.nat` or `.bt`).  Generators combine `LawvereER`'s ℕ-sort
arithmetic, structural BT operations (`leaf`, `node`, `proj`,
`comp`, `foldBT`), and bridges `encodeBT` / `decodeBT`.  The
combined theory is equivalent as a category to `LawvereER`.

See `docs/superpowers/specs/2026-04-17-lawvere-natbt-design.md`
for rationale and design decisions.
-/

namespace GebLean

end GebLean
```

- [ ] **Step 2: Define the labeled `BTL` inductive**

Inside `namespace GebLean`:

```lean
/-- Labeled binary tree: leaves carry a `ℕ` label, internal nodes
are binary-branching with no label of their own.  The unlabeled
`BT` from `GebLean/LawvereBT.lean` embeds as `BTL` with all leaf
labels equal to 0. -/
inductive BTL : Type where
  | leaf (n : ℕ) : BTL
  | node (l r : BTL) : BTL
  deriving Repr, DecidableEq, Inhabited
```

- [ ] **Step 3: Define a BT-fold over `BTL` at Type-level**

```lean
/-- Catamorphism over `BTL`.  `baseLeaf` processes the label at a
leaf; `stepNode` combines the two recursive results at a node. -/
def BTL.fold {α : Type*} (baseLeaf : ℕ → α) (stepNode : α → α → α) :
    BTL → α
  | BTL.leaf n => baseLeaf n
  | BTL.node l r => stepNode (BTL.fold baseLeaf stepNode l)
                             (BTL.fold baseLeaf stepNode r)

@[simp] theorem BTL.fold_leaf {α : Type*} (baseLeaf : ℕ → α)
    (stepNode : α → α → α) (n : ℕ) :
    BTL.fold baseLeaf stepNode (BTL.leaf n) = baseLeaf n := rfl

@[simp] theorem BTL.fold_node {α : Type*} (baseLeaf : ℕ → α)
    (stepNode : α → α → α) (l r : BTL) :
    BTL.fold baseLeaf stepNode (BTL.node l r) =
      stepNode (BTL.fold baseLeaf stepNode l)
               (BTL.fold baseLeaf stepNode r) := rfl
```

- [ ] **Step 4: Szudzik-style encode/decode `BTL ↔ ℕ`**

```lean
/-- Szudzik-based Gödel encoding of labeled BT.  `leaf n` maps to
`2 * n`; `node l r` maps to `2 * pair(encode l, encode r) + 1`. -/
def BTL.encode : BTL → ℕ
  | BTL.leaf n => 2 * n
  | BTL.node l r => 2 * (Nat.pair l.encode r.encode) + 1

/-- Inverse of `BTL.encode`. -/
def BTL.decode : ℕ → BTL
  | n =>
      if n % 2 = 0 then BTL.leaf (n / 2)
      else
        let p := n / 2
        BTL.node (BTL.decode (Nat.unpair p).1)
                 (BTL.decode (Nat.unpair p).2)
  termination_by n => n
  decreasing_by
    all_goals
      have : (Nat.unpair (n / 2)).1 ≤ n / 2 :=
        Nat.unpair_left_le _
      have : (Nat.unpair (n / 2)).2 ≤ n / 2 :=
        Nat.unpair_right_le _
      omega
```

- [ ] **Step 5: Prove round-trip theorems**

```lean
theorem BTL.decode_encode (t : BTL) :
    BTL.decode t.encode = t := by
  induction t with
  | leaf n => simp [BTL.encode, BTL.decode]
  | node l r ihl ihr =>
      simp [BTL.encode, BTL.decode, Nat.unpair_pair, ihl, ihr]
      -- The if-branch for odd codes applies; details adapt to
      -- Mathlib's pair/unpair simp set.

theorem BTL.encode_decode (n : ℕ) :
    (BTL.decode n).encode = n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
      by_cases h : n % 2 = 0
      · simp [BTL.decode, h, BTL.encode]
        omega
      · simp [BTL.decode, h]
        -- Unfold, apply ih to the two smaller values, rebuild via
        -- Nat.pair_unpair and the odd-code arithmetic.
        sorry -- implementer: replace with actual proof
```

Note: the decode/encode round-trip is straightforward but requires
careful handling of the parity split; the implementer writes the
full proofs (no `sorry` at final).

- [ ] **Step 6: Build and commit**

```bash
lake build GebLean.LawvereNatBT
```

Expected: PASS.

```bash
git add GebLean/LawvereNatBT.lean
git commit -m "Add BTL labeled binary tree with fold and Gödel bijection"
```

---

### Task 2: `NatBTMor1` term type and output sort

**Files:**

* Modify: `GebLean/LawvereNatBT.lean`

- [ ] **Step 1: Define the `Sort` discriminator**

```lean
/-- Discriminator for the output sort of a two-sort morphism.
`.nat` means the morphism produces a natural number; `.bt` means
it produces a labeled binary tree. -/
inductive NatBTSort : Type where
  | nat
  | bt
  deriving DecidableEq, Repr
```

- [ ] **Step 2: Define `NatBTMor1` inductive**

```lean
/-- Morphism in the two-sort Lawvere theory.  Indexed by a domain
arity `(n, m) : ℕ × ℕ` and an output sort `σ : NatBTSort`.  The
constructors partition into ℕ-sort generators, BT-sort generators,
and bridge generators. -/
inductive NatBTMor1 : (ℕ × ℕ) → NatBTSort → Type where
  -- ℕ-sort generators (mirroring LawvereER)
  | zero {nm : ℕ × ℕ} : NatBTMor1 nm .nat
  | succ {nm : ℕ × ℕ} (x : NatBTMor1 nm .nat) : NatBTMor1 nm .nat
  | natProj {nm : ℕ × ℕ} (i : Fin nm.1) : NatBTMor1 nm .nat
  | sub {nm : ℕ × ℕ} (a b : NatBTMor1 nm .nat) :
      NatBTMor1 nm .nat
  | compNat {nm nm' : ℕ × ℕ}
      (f : NatBTMor1 nm' .nat)
      (gNat : Fin nm'.1 → NatBTMor1 nm .nat)
      (gBT  : Fin nm'.2 → NatBTMor1 nm .bt) :
      NatBTMor1 nm .nat
  | bsum {nm : ℕ × ℕ}
      (f : NatBTMor1 (nm.1 + 1, nm.2) .nat) :
      NatBTMor1 (nm.1 + 1, nm.2) .nat
  | bprod {nm : ℕ × ℕ}
      (f : NatBTMor1 (nm.1 + 1, nm.2) .nat) :
      NatBTMor1 (nm.1 + 1, nm.2) .nat
  -- BT-sort generators
  | leafBT {nm : ℕ × ℕ}
      (label : NatBTMor1 nm .nat) :
      NatBTMor1 nm .bt
  | nodeBT {nm : ℕ × ℕ}
      (l r : NatBTMor1 nm .bt) :
      NatBTMor1 nm .bt
  | btProj {nm : ℕ × ℕ} (i : Fin nm.2) : NatBTMor1 nm .bt
  | compBT {nm nm' : ℕ × ℕ}
      (f : NatBTMor1 nm' .bt)
      (gNat : Fin nm'.1 → NatBTMor1 nm .nat)
      (gBT  : Fin nm'.2 → NatBTMor1 nm .bt) :
      NatBTMor1 nm .bt
  | foldBTNat {nm : ℕ × ℕ}
      (baseLeaf : NatBTMor1 (nm.1 + 1, nm.2) .nat)
      (stepNode : NatBTMor1 (nm.1 + 2, nm.2) .nat)
      (tree : NatBTMor1 nm .bt) :
      NatBTMor1 nm .nat
  | foldBTBT {nm : ℕ × ℕ}
      (baseLeaf : NatBTMor1 (nm.1 + 1, nm.2) .bt)
      (stepNode : NatBTMor1 (nm.1, nm.2 + 2) .bt)
      (tree : NatBTMor1 nm .bt) :
      NatBTMor1 nm .bt
  -- Bridge generators
  | encodeBT {nm : ℕ × ℕ}
      (t : NatBTMor1 nm .bt) : NatBTMor1 nm .nat
  | decodeBT {nm : ℕ × ℕ}
      (k : NatBTMor1 nm .nat) : NatBTMor1 nm .bt
```

- [ ] **Step 3: Define the output-sort carrier**

```lean
/-- Target type for a morphism's output sort under the standard
interpretation. -/
def NatBTSort.carrier : NatBTSort → Type
  | .nat => ℕ
  | .bt  => BTL
```

- [ ] **Step 4: Build and commit**

```bash
lake build GebLean.LawvereNatBT
```

Expected: PASS.

```bash
git add GebLean/LawvereNatBT.lean
git commit -m "Add NatBTMor1 two-sort term inductive"
```

---

### Task 3: Interpretation `NatBTMor1.interp`

**Files:**

* Modify: `GebLean/LawvereNatBT.lean`

- [ ] **Step 1: Define the interpretation**

```lean
/-- Standard interpretation of a two-sort morphism: maps a
`(Fin n → ℕ)` context for the ℕ inputs and a `(Fin m → BTL)`
context for the BT inputs to a value of the output sort's carrier
type. -/
def NatBTMor1.interp {nm : ℕ × ℕ} {σ : NatBTSort}
    (f : NatBTMor1 nm σ)
    (ctxN : Fin nm.1 → ℕ) (ctxB : Fin nm.2 → BTL) :
    σ.carrier := by
  induction f with
  | zero => exact 0
  | succ _ ih => exact ih + 1
  | natProj i => exact ctxN i
  | sub _ _ iha ihb => exact iha - ihb
  | compNat f gNat gBT ih ihNat ihBT =>
      exact ih (fun i => ihNat i) (fun i => ihBT i)
  | bsum f ih =>
      exact natBSum (ctxN 0)
        (fun i => ih (Fin.cons i (Fin.tail ctxN)) ctxB)
  | bprod f ih =>
      exact natBProd (ctxN 0)
        (fun i => ih (Fin.cons i (Fin.tail ctxN)) ctxB)
  | leafBT _ ihLabel => exact BTL.leaf ihLabel
  | nodeBT _ _ ihl ihr => exact BTL.node ihl ihr
  | btProj i => exact ctxB i
  | compBT f gNat gBT ih ihNat ihBT =>
      exact ih (fun i => ihNat i) (fun i => ihBT i)
  | foldBTNat baseLeaf stepNode tree ihBase ihStep ihTree =>
      exact ihTree.fold
        (fun lbl => ihBase (Fin.cons lbl ctxN) ctxB)
        (fun a b =>
          ihStep (Fin.cons a (Fin.cons b ctxN)) ctxB)
  | foldBTBT baseLeaf stepNode tree ihBase ihStep ihTree =>
      exact ihTree.fold
        (fun lbl => ihBase (Fin.cons lbl ctxN) ctxB)
        (fun a b =>
          ihStep ctxN (Fin.cons a (Fin.cons b ctxB)))
  | encodeBT _ ih => exact ih.encode
  | decodeBT _ ih => exact BTL.decode ih
```

Note: the exact shape of the `interp` definition depends on
whether induction handles dependent-sort constructors smoothly.
The implementer picks between `def ... := by induction` and a
pattern-match definition.  Both produce the same interpretation
function.

- [ ] **Step 2: Add `@[simp]` reduction lemmas**

Provide `@[simp]` lemmas for each constructor matching the
interpretation clause, so downstream `simp` calls reduce
`NatBTMor1.interp` on specific terms cleanly.  Names:
`interp_zero`, `interp_succ`, `interp_natProj`, etc.

- [ ] **Step 3: Build and commit**

```bash
lake build GebLean.LawvereNatBT
git add GebLean/LawvereNatBT.lean
git commit -m "Add NatBTMor1.interp with per-constructor simp lemmas"
```

---

### Task 4: `NatBTMorN` tuples, identity, composition

**Files:**

* Modify: `GebLean/LawvereNatBT.lean`

- [ ] **Step 1: Define the tuple type**

```lean
/-- A morphism `(n, m) → (n', m')` in the two-sort theory: `n'`
ℕ-valued components and `m'` BT-valued components, each a
`NatBTMor1` with domain arity `(n, m)`. -/
structure NatBTMorN (nm nm' : ℕ × ℕ) where
  natComps : Fin nm'.1 → NatBTMor1 nm .nat
  btComps  : Fin nm'.2 → NatBTMor1 nm .bt
```

- [ ] **Step 2: Define identity tuple**

```lean
/-- Identity morphism `(n, m) → (n, m)`: projections at each
sort. -/
def NatBTMorN.id (nm : ℕ × ℕ) : NatBTMorN nm nm where
  natComps i := NatBTMor1.natProj i
  btComps i := NatBTMor1.btProj i
```

- [ ] **Step 3: Define tuple composition**

```lean
/-- Composition via substitution at both sorts. -/
def NatBTMorN.comp {nm nm' nm'' : ℕ × ℕ}
    (f : NatBTMorN nm nm') (g : NatBTMorN nm' nm'') :
    NatBTMorN nm nm'' where
  natComps i :=
    NatBTMor1.compNat (g.natComps i) f.natComps f.btComps
  btComps i :=
    NatBTMor1.compBT (g.btComps i) f.natComps f.btComps
```

- [ ] **Step 4: Define the tuple interpretation**

```lean
def NatBTMorN.interp {nm nm' : ℕ × ℕ} (f : NatBTMorN nm nm')
    (ctxN : Fin nm.1 → ℕ) (ctxB : Fin nm.2 → BTL) :
    (Fin nm'.1 → ℕ) × (Fin nm'.2 → BTL) :=
  (fun i => (f.natComps i).interp ctxN ctxB,
   fun i => (f.btComps i).interp ctxN ctxB)
```

- [ ] **Step 5: Prove `interp_id` and `interp_comp`**

```lean
@[simp] theorem NatBTMorN.interp_id (nm : ℕ × ℕ)
    (ctxN : Fin nm.1 → ℕ) (ctxB : Fin nm.2 → BTL) :
    (NatBTMorN.id nm).interp ctxN ctxB = (ctxN, ctxB) := by
  simp [NatBTMorN.id, NatBTMorN.interp]
  -- reduce each component via interp_natProj / interp_btProj

@[simp] theorem NatBTMorN.interp_comp {nm nm' nm'' : ℕ × ℕ}
    (f : NatBTMorN nm nm') (g : NatBTMorN nm' nm'')
    (ctxN : Fin nm.1 → ℕ) (ctxB : Fin nm.2 → BTL) :
    (NatBTMorN.comp f g).interp ctxN ctxB =
      let ⟨ctxN', ctxB'⟩ := f.interp ctxN ctxB
      g.interp ctxN' ctxB' := by
  simp [NatBTMorN.comp, NatBTMorN.interp]
  -- reduce each component via interp_compNat / interp_compBT
```

- [ ] **Step 6: Build and commit**

```bash
lake build GebLean.LawvereNatBT
git add GebLean/LawvereNatBT.lean
git commit -m "Add NatBTMorN tuple type with id and composition"
```

---

### Task 5: Extensional equality setoid

**Files:**

* Create: `GebLean/LawvereNatBTQuot.lean`

- [ ] **Step 1: Create the file with header**

```lean
import GebLean.LawvereNatBT
import Mathlib.CategoryTheory.Category.Basic
import GebLean.Utilities.ComputableLimits

/-!
# Quotient Category for `LawvereNatBT`

`NatBTMorN` quotiented by extensional equality of interpretations
yields a category `LawvereNatBTCat` with chosen finite products.
-/

namespace GebLean

end GebLean
```

- [ ] **Step 2: Define the setoid**

```lean
/-- Extensional equality of `NatBTMorN` tuples: two tuples are
equivalent iff their interpretations agree on every context. -/
def natBTMorNRel (nm nm' : ℕ × ℕ) :
    NatBTMorN nm nm' → NatBTMorN nm nm' → Prop :=
  fun f g => ∀ (ctxN : Fin nm.1 → ℕ) (ctxB : Fin nm.2 → BTL),
    f.interp ctxN ctxB = g.interp ctxN ctxB

instance natBTMorNSetoid (nm nm' : ℕ × ℕ) :
    Setoid (NatBTMorN nm nm') where
  r := natBTMorNRel nm nm'
  iseqv := ⟨
    fun _ _ _ => rfl,
    fun h c d => (h c d).symm,
    fun h₁ h₂ c d => (h₁ c d).trans (h₂ c d)
  ⟩
```

- [ ] **Step 3: Build and commit**

```bash
lake build GebLean.LawvereNatBTQuot
git add GebLean/LawvereNatBTQuot.lean
git commit -m "Add extensional-equality setoid for NatBTMorN"
```

---

### Task 6: `NatBTMorNQuo` quotient type, identity, composition

**Files:**

* Modify: `GebLean/LawvereNatBTQuot.lean`

- [ ] **Step 1: Define the quotient type**

```lean
/-- Morphism class in `LawvereNatBTCat`: a `NatBTMorN` up to
extensional equivalence. -/
def NatBTMorNQuo (nm nm' : ℕ × ℕ) : Type :=
  Quotient (natBTMorNSetoid nm nm')
```

- [ ] **Step 2: Identity**

```lean
def NatBTMorNQuo.id (nm : ℕ × ℕ) : NatBTMorNQuo nm nm :=
  Quotient.mk _ (NatBTMorN.id nm)
```

- [ ] **Step 3: Composition via `Quotient.lift₂`**

```lean
def NatBTMorNQuo.comp {nm nm' nm'' : ℕ × ℕ}
    (f : NatBTMorNQuo nm nm') (g : NatBTMorNQuo nm' nm'') :
    NatBTMorNQuo nm nm'' :=
  Quotient.liftOn₂ f g
    (fun a b => Quotient.mk _ (NatBTMorN.comp a b))
    (fun a₁ b₁ a₂ b₂ h₁ h₂ => by
      apply Quotient.sound
      intro ctxN ctxB
      simp [NatBTMorN.interp_comp, h₁ ctxN ctxB]
      -- compose with h₂ evaluated on the transformed context
      sorry) -- implementer completes
```

- [ ] **Step 4: Prove category laws**

```lean
theorem NatBTMorNQuo.id_comp {nm nm' : ℕ × ℕ}
    (f : NatBTMorNQuo nm nm') :
    NatBTMorNQuo.comp (NatBTMorNQuo.id nm) f = f := by
  refine Quotient.inductionOn f ?_
  intro a
  apply Quotient.sound
  intro ctxN ctxB
  simp [NatBTMorN.comp, NatBTMorN.id, NatBTMorN.interp]
  -- reduces to equality via compNat / compBT interp simps

theorem NatBTMorNQuo.comp_id {nm nm' : ℕ × ℕ}
    (f : NatBTMorNQuo nm nm') :
    NatBTMorNQuo.comp f (NatBTMorNQuo.id nm') = f := by
  refine Quotient.inductionOn f ?_
  intro a
  apply Quotient.sound
  intro ctxN ctxB
  simp [NatBTMorN.comp, NatBTMorN.id]

theorem NatBTMorNQuo.assoc {nm nm' nm'' nm''' : ℕ × ℕ}
    (f : NatBTMorNQuo nm nm') (g : NatBTMorNQuo nm' nm'')
    (h : NatBTMorNQuo nm'' nm''') :
    NatBTMorNQuo.comp (NatBTMorNQuo.comp f g) h =
      NatBTMorNQuo.comp f (NatBTMorNQuo.comp g h) := by
  refine Quotient.inductionOn₃ f g h ?_
  intros a b c
  apply Quotient.sound
  intro ctxN ctxB
  simp [NatBTMorN.interp_comp]
```

- [ ] **Step 5: Build and commit**

```bash
lake build GebLean.LawvereNatBTQuot
git add GebLean/LawvereNatBTQuot.lean
git commit -m "Add NatBTMorNQuo quotient with identity, comp, category laws"
```

---

### Task 7: `LawvereNatBTCat` as a `Category`

**Files:**

* Modify: `GebLean/LawvereNatBTQuot.lean`

- [ ] **Step 1: Define the category carrier**

```lean
open CategoryTheory

/-- Carrier type for the base category: pairs `(n, m) : ℕ × ℕ`. -/
def LawvereNatBTCat : Type := ℕ × ℕ

instance : CategoryStruct LawvereNatBTCat where
  Hom nm nm' := NatBTMorNQuo nm nm'
  id := NatBTMorNQuo.id
  comp := NatBTMorNQuo.comp

instance : Category LawvereNatBTCat where
  id_comp := NatBTMorNQuo.id_comp
  comp_id := NatBTMorNQuo.comp_id
  assoc := NatBTMorNQuo.assoc
```

- [ ] **Step 2: Build and commit**

```bash
lake build GebLean.LawvereNatBTQuot
git add GebLean/LawvereNatBTQuot.lean
git commit -m "Add Category instance for LawvereNatBTCat"
```

---

### Task 8: `HasChosenFiniteProducts LawvereNatBTCat`

**Files:**

* Modify: `GebLean/LawvereNatBTQuot.lean`

- [ ] **Step 1: Define product structure**

The product of `(n₁, m₁)` and `(n₂, m₂)` is
`(n₁ + n₂, m₁ + m₂)`.  Projections use `natProj` / `btProj` with
offset indices via `Fin.addCases`.

```lean
def LawvereNatBTCat.prod (a b : LawvereNatBTCat) :
    LawvereNatBTCat :=
  (a.1 + b.1, a.2 + b.2)

def LawvereNatBTCat.fst (a b : LawvereNatBTCat) :
    (LawvereNatBTCat.prod a b) ⟶ a := by
  refine Quotient.mk _ ?_
  exact
    { natComps i :=
        NatBTMor1.natProj (Fin.castAdd b.1 i)
      btComps i :=
        NatBTMor1.btProj (Fin.castAdd b.2 i) }

def LawvereNatBTCat.snd (a b : LawvereNatBTCat) :
    (LawvereNatBTCat.prod a b) ⟶ b := by
  refine Quotient.mk _ ?_
  exact
    { natComps i :=
        NatBTMor1.natProj (Fin.natAdd a.1 i)
      btComps i :=
        NatBTMor1.btProj (Fin.natAdd a.2 i) }

def LawvereNatBTCat.pair {x a b : LawvereNatBTCat}
    (f : x ⟶ a) (g : x ⟶ b) :
    x ⟶ (LawvereNatBTCat.prod a b) := by
  refine Quotient.liftOn₂ f g ?_ ?_
  · intro f' g'
    refine Quotient.mk _ ?_
    exact
      { natComps i :=
          i.addCases (fun j => f'.natComps j) (fun j => g'.natComps j)
        btComps i :=
          i.addCases (fun j => f'.btComps j) (fun j => g'.btComps j) }
  · intros _ _ _ _ h₁ h₂
    apply Quotient.sound
    intro ctxN ctxB
    ext i
    · rcases i.addCases_eq with ⟨_, hh⟩ | ⟨_, hh⟩
      -- dispatch per Fin.addCases branch; use h₁ / h₂ as appropriate
      sorry -- implementer completes
    · sorry -- implementer completes (bt components)
```

- [ ] **Step 2: Terminal object `(0, 0)`**

```lean
instance : Unique (NatBTMorNQuo x (0, 0)) where
  default := NatBTMorNQuo.id ... -- actually the empty tuple
  uniq := by
    intro f
    refine Quotient.inductionOn f ?_
    intro f'
    apply Quotient.sound
    intro ctxN ctxB
    ext i
    · exact i.elim0
    · exact i.elim0
```

- [ ] **Step 3: Assemble `HasChosenFiniteProducts` instance**

```lean
instance : HasChosenFiniteProducts LawvereNatBTCat where
  terminal := ...
  product a b := ...
  -- full shape follows the existing pattern in
  -- `GebLean/LawvereERQuot.lean`'s `HasChosenFiniteProducts
  -- LawvereERCat`
```

- [ ] **Step 4: Build and commit**

```bash
lake build GebLean.LawvereNatBTQuot
git add GebLean/LawvereNatBTQuot.lean
git commit -m "Add HasChosenFiniteProducts for LawvereNatBTCat"
```

---

### Task 9: Interpretation functor into `Type`

**Files:**

* Create: `GebLean/LawvereNatBTInterp.lean`

- [ ] **Step 1: Create file with header and imports**

```lean
import GebLean.LawvereNatBTQuot
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Functor.FullyFaithful

/-!
# Interpretation Functor for `LawvereNatBTCat`

Sends `(n, m)` to `(Fin n → ℕ) × (Fin m → BTL)` and each morphism
class to its interpretation.
-/

namespace GebLean

open CategoryTheory

end GebLean
```

- [ ] **Step 2: Define the functor**

```lean
/-- Interpretation functor: `(n, m) ↦ (Fin n → ℕ) × (Fin m → BTL)`
on objects; on morphisms, apply `NatBTMorN.interp`. -/
def natBTInterpFunctor :
    LawvereNatBTCat ⥤ Type where
  obj nm := (Fin nm.1 → ℕ) × (Fin nm.2 → BTL)
  map {nm nm'} f := fun ⟨ctxN, ctxB⟩ =>
    Quotient.liftOn f
      (fun f' => f'.interp ctxN ctxB)
      (fun _ _ h => h ctxN ctxB)
  map_id nm := by
    funext ⟨ctxN, ctxB⟩
    simp [NatBTMorNQuo.id, NatBTMorN.interp_id]
  map_comp {_ _ _} f g := by
    funext ⟨ctxN, ctxB⟩
    refine Quotient.inductionOn₂ f g ?_
    intro a b
    simp [NatBTMorNQuo.comp, NatBTMorN.interp_comp]
```

- [ ] **Step 3: Prove faithfulness**

```lean
instance : natBTInterpFunctor.Faithful where
  map_injective {nm nm'} {f g} h := by
    refine Quotient.inductionOn₂ f g ?_
    intro a b hab
    apply Quotient.sound
    intro ctxN ctxB
    exact congrFun hab ⟨ctxN, ctxB⟩
```

- [ ] **Step 4: Build and commit**

```bash
lake build GebLean.LawvereNatBTInterp
git add GebLean/LawvereNatBTInterp.lean
git commit -m "Add natBTInterpFunctor with faithfulness"
```

---

### Task 10: Register Stage α and write tests

**Files:**

* Modify: `GebLean.lean`
* Create: `GebLeanTests/LawvereNatBT.lean`
* Create: `GebLeanTests/LawvereNatBTQuot.lean`
* Create: `GebLeanTests/LawvereNatBTInterp.lean`
* Modify: `GebLeanTests.lean`

- [ ] **Step 1: Register library modules**

Add to `GebLean.lean` (in appropriate alphabetical position):

```lean
import GebLean.LawvereNatBT
import GebLean.LawvereNatBTQuot
import GebLean.LawvereNatBTInterp
```

- [ ] **Step 2: Write `GebLeanTests/LawvereNatBT.lean`**

```lean
import GebLean.LawvereNatBT

open GebLean

-- BTL round-trip on small examples
#guard BTL.decode (BTL.encode (BTL.leaf 0)) = BTL.leaf 0
#guard BTL.decode (BTL.encode (BTL.leaf 7)) = BTL.leaf 7
#guard BTL.decode
  (BTL.encode (BTL.node (BTL.leaf 2) (BTL.leaf 3))) =
  BTL.node (BTL.leaf 2) (BTL.leaf 3)

-- Interpretation of specific small NatBTMor1 terms
#guard (NatBTMor1.zero (nm := (0, 0))).interp
  Fin.elim0 Fin.elim0 = 0
```

- [ ] **Step 3: Write `GebLeanTests/LawvereNatBTQuot.lean`**

Small type-check examples for identity and composition; `#guard`
for category-law spot-checks.

- [ ] **Step 4: Write `GebLeanTests/LawvereNatBTInterp.lean`**

```lean
import GebLean.LawvereNatBTInterp

open GebLean CategoryTheory

example : LawvereNatBTCat ⥤ Type := natBTInterpFunctor
example : natBTInterpFunctor.Faithful := inferInstance
```

- [ ] **Step 5: Register test modules**

Add to `GebLeanTests.lean`:

```lean
import GebLeanTests.LawvereNatBT
import GebLeanTests.LawvereNatBTQuot
import GebLeanTests.LawvereNatBTInterp
```

- [ ] **Step 6: Build and test**

```bash
lake build && lake test
```

Expected: both PASS with no warnings.

- [ ] **Step 7: Commit**

```bash
git add GebLean.lean GebLeanTests/LawvereNatBT.lean \
        GebLeanTests/LawvereNatBTQuot.lean \
        GebLeanTests/LawvereNatBTInterp.lean GebLeanTests.lean
git commit -m "Register and test Stage α of LawvereNatBT"
```

---

## Stage β: three-stage equivalence with `LawvereER`

The equivalence `LawvereERCat ≃ LawvereNatBTCat` factors as three
separate stages, each independently meaningful:

```
LawvereERCat  ≅  LawvereNatBTPureCat  ≃  LawvereNatBT0Cat  ↪  LawvereNatBTCat
       (Stage 3                    (Stage 2                   (Stage 1
        on-the-nose iso)            back-translation           FullSubcategory
                                    via ER-Szudzik)            + Szudzik on objects)

                LawvereERCat  ≃  LawvereNatBTCat  (Stage β goal)
```

The four categories:

* **`LawvereNatBTCat`** ("TreeER") — the two-sort base category
  from Stage α.
* **`LawvereNatBT0Cat`** ("Tree0ER") — the `FullSubcategory` of
  `LawvereNatBTCat` whose objects have BT-arity zero.  Hom-sets
  are inherited verbatim (and may include morphism classes whose
  representatives use `encodeBT`/`foldBTNat` internally).
* **`LawvereNatBTPureCat`** ("TreeNatER") — the strict-ER fragment
  of `LawvereNatBT0Cat`'s hom-sets: morphism classes containing
  some representative whose every sub-term is in the strict-ER
  fragment (no `encodeBT`/`foldBTNat`/etc. anywhere).
* **`LawvereERCat`** ("NatER") — the existing ℕ-only theory.

Implementation order (and the work each task represents):

| Task | Subject | Notes |
|---|---|---|
| 11 | `LawvereNatBT0Cat` (Stage 1's subcategory) | DONE — commit `4f806f6d` |
| 12 | ER-derived `Nat.pair`/`Nat.unpair` | New Szudzik infra |
| 13 | ER-derived `BTL.encode`/`BTL.decode`/fold-on-code | New Szudzik infra |
| 14 | `NatBTMor1.toER` back-translation | Stage 2 substrate |
| 15 | `LawvereNatBTPureCat` + Stage 3 trivial iso | Stage 3 |
| 16 | Stage 1 essential surjectivity (Szudzik on objects) | Independent of Tasks 12-15 |
| 17 | Stage 2 equivalence (back-translation packaged) | Depends on Tasks 12-15 |
| 18 | Compose three stages → `LawvereERCat ≃ LawvereNatBTCat` | Depends on Tasks 16-17 |
| 19 | Transport Phase 4f Ackermann + tetration non-fullness | Depends on Task 18 |
| 20 | Register Stage β + tests | |

Tasks 12, 13, 14, 17, 18 are flagged proof-heavy.  Tasks 16 and
19 are moderate; Task 15 is mostly definitional packaging.

### Task 11: `LawvereNatBT0Cat` via `FullSubcategory` (DONE)

**Status:** Complete as of commit `4f806f6d` ("Add
LawvereNatBT0Cat as FullSubcategory of LawvereNatBTCat").  Module
`GebLean/LawvereNatBT0.lean` provides:

* `isNatBT0 : ObjectProperty LawvereNatBTCat` (`fun nm => nm.2 = 0`)
* `LawvereNatBT0Cat := isNatBT0.FullSubcategory`
* `natBT0Inclusion := isNatBT0.ι : LawvereNatBT0Cat ⥤ LawvereNatBTCat`
  (with `Full`/`Faithful` instances inherited from mathlib)
* `lawvereNatBT0Terminal`, `lawvereNatBT0Product`, and
  `instance : HasChosenFiniteProducts LawvereNatBT0Cat`

The original Step-by-step task description below is preserved
for reference.  Skip when implementing — go to Task 12.

#### (Original) Task 11 spec

**Files:**

* Create: `GebLean/LawvereNatBT0.lean`

- [ ] **Step 1: Header and imports**

```lean
import GebLean.LawvereNatBTQuot
import Mathlib.CategoryTheory.FullSubcategory
import Mathlib.CategoryTheory.ObjectProperty.Basic
import GebLean.Utilities.ComputableLimits

/-!
# `LawvereNatBT0`: the `m = 0` Full Subcategory of `LawvereNatBT`

The full subcategory of `LawvereNatBTCat` whose objects have BT
arity zero.  Provides the intermediate category for Stage β's
two-step factorization
`LawvereERCat ≅ LawvereNatBT0Cat ↪ LawvereNatBTCat`.

Inherits its `HasChosenFiniteProducts` from `LawvereNatBTCat`:
the product of `(n₁, 0)` and `(n₂, 0)` is `(n₁ + n₂, 0)`, still
in the subcategory; the terminal `(0, 0)` is also in the
subcategory.
-/

namespace GebLean

open CategoryTheory

end GebLean
```

- [ ] **Step 2: Define the object property and the subcategory**

```lean
/-- Predicate selecting `LawvereNatBTCat` objects with BT
arity zero. -/
def isNatBT0 : LawvereNatBTCat → Prop := fun nm => nm.2 = 0

/-- The full subcategory of `LawvereNatBTCat` on `m = 0`
objects. -/
def LawvereNatBT0Cat : Type :=
  FullSubcategory isNatBT0

instance : Category LawvereNatBT0Cat :=
  FullSubcategory.category isNatBT0
```

(Names like `FullSubcategory.category`, `FullSubcategory.ι`,
`FullSubcategory.lift` are the standard mathlib API.  If the
exact identifiers differ in this mathlib version, look up the
current convention via `lean_local_search` or
`mcp__lean-lsp__lean_hover_info` and use the actual API names.)

- [ ] **Step 3: The full faithful inclusion**

```lean
/-- The `FullSubcategory` inclusion functor.  Full and faithful
by construction. -/
def natBT0Inclusion : LawvereNatBT0Cat ⥤ LawvereNatBTCat :=
  FullSubcategory.ι isNatBT0

instance : natBT0Inclusion.Full := inferInstance
instance : natBT0Inclusion.Faithful := inferInstance
```

- [ ] **Step 4: Restrict `HasChosenFiniteProducts`**

The product of two `(n, 0)` objects is `(n₁ + n₂, 0)`, which
satisfies `isNatBT0`; the terminal `(0, 0)` satisfies it too.
Restricting the chosen-finite-products data to the subcategory
is a mechanical lift.

```lean
def lawvereNatBT0Product (a b : LawvereNatBT0Cat) :
    ChosenBinaryProduct a b where
  obj := ⟨(a.obj.1 + b.obj.1, 0), rfl⟩
  fst := -- inherit from LawvereNatBTCat via FullSubcategory
    sorry  -- implementer fills in via the parent product fst
  snd := sorry
  lift := sorry
  lift_fst := sorry
  lift_snd := sorry
  lift_uniq := sorry

def lawvereNatBT0Terminal : ChosenTerminal LawvereNatBT0Cat where
  obj := ⟨(0, 0), rfl⟩
  from_ a := -- inherit
    sorry
  uniq := sorry

instance : HasChosenFiniteProducts LawvereNatBT0Cat where
  terminal := lawvereNatBT0Terminal
  product := lawvereNatBT0Product
```

Note: the `sorry`s here are placeholders for the implementer to
complete by lifting the underlying `LawvereNatBTCat` data
through the `FullSubcategory` inclusion.  The argument is
mechanical: every operation in
`HasChosenFiniteProducts LawvereNatBTCat` lands in the
subcategory because `(n₁, 0) × (n₂, 0)` and the terminal
satisfy `isNatBT0`.

- [ ] **Step 5: Register module + build + commit**

Add `import GebLean.LawvereNatBT0` to `GebLean.lean` in the
appropriate alphabetical position.

```bash
lake build GebLean.LawvereNatBT0
lake test
git add GebLean/LawvereNatBT0.lean GebLean.lean
git commit -m "Add LawvereNatBT0Cat as FullSubcategory of LawvereNatBTCat"
```

---

### Task 12: ER-derived `Nat.pair` and `Nat.unpair`

**Goal:** Package mathlib's `Nat.pair` and `Nat.unpair` as derived
`ERMor1` terms with `@[simp]`-marked correctness theorems.

**Files:**

* Create: `GebLean/Utilities/ERTreeArith.lean`
* Modify: `GebLean.lean`

- [ ] **Step 1: Header and imports**

[USE the same imports and docstring as in the spec's
"ER-derived Szudzik infrastructure" section: import
LawvereER, LawvereERArith, LawvereERBool, Utilities/SzudzikSeq,
Mathlib.Data.Nat.Pairing.  See
docs/superpowers/specs/2026-04-17-lawvere-natbt-design.md.]

- [ ] **Step 2: ER-derived `Nat.pair`**

`Nat.pair x y = if x < y then y * y + x else x * x + x + y`
(Szudzik bijection, mathlib's convention).  Required ER
ingredients:

* Comparison `x < y`: implementable as a 0/1 indicator using
  truncated subtraction.
* Conditional `if b then t else f`: as `(1 - b) * f + b * t`
  where `b ∈ {0, 1}`.
* `+`, `*`: addition via `bsum (proj 1)` style; multiplication
  via `bsum (proj 1)` (already in `LawvereERArith.lean`).

```lean
/-- ER-derived term computing Szudzik's pairing.  Interpretation
agrees with `Nat.pair`. -/
def ERMor1.natPair : ERMor1 2 :=
  -- Implementer assembles using comparison + conditional + arith
  sorry

@[simp] theorem ERMor1.interp_natPair (x y : ℕ) :
    (ERMor1.natPair).interp ![x, y] = Nat.pair x y := by
  sorry
```

Implementer notes:

* Look at `GebLean/LawvereERBool.lean` for the conditional/
  boolean-indicator pattern (`subSwap`, `boolEqNat`).
* Use `ERMor1.zeroN`/`ERMor1.oneN` for ℕ constants.
* The proof reduces to unfolding the definition and matching
  the cases `x < y`, `x ≥ y`.  Mathlib's `Nat.pair` is in
  `Mathlib.Data.Nat.Pairing`.

- [ ] **Step 3: ER-derived `Nat.unpair`**

`Nat.unpair n = let s := Nat.sqrt n; if n - s*s < s then
(n - s*s, s) else (s, n - s*s - s)`.

ER needs `Nat.sqrt`, which is iteratively bounded.  Build:

```lean
/-- Iterative ℕ-sqrt as an ER term. -/
def ERMor1.natSqrt : ERMor1 1 :=
  -- bsum-based bounded search up to n
  sorry

def ERMor1.natUnpairFst : ERMor1 1 := sorry
def ERMor1.natUnpairSnd : ERMor1 1 := sorry

@[simp] theorem ERMor1.interp_natUnpairFst (n : ℕ) :
    (ERMor1.natUnpairFst).interp ![n] = (Nat.unpair n).1 := sorry

@[simp] theorem ERMor1.interp_natUnpairSnd (n : ℕ) :
    (ERMor1.natUnpairSnd).interp ![n] = (Nat.unpair n).2 := sorry
```

Implementer notes:

* `Nat.sqrt n ≤ n`, so a bounded search via `bsum` works.
* Check `GebLean/NatNNO.lean` and `GebLean/NatElegantPair.lean`
  for existing `isqrt`-related infrastructure that may be
  reusable.

- [ ] **Step 4: Round-trip lemmas**

```lean
@[simp] theorem ERMor1.natUnpairFst_pair (x y : ℕ) :
    (ERMor1.natUnpairFst).interp
        ![(ERMor1.natPair).interp ![x, y]] = x := by
  simp [Nat.unpair_pair]

@[simp] theorem ERMor1.natUnpairSnd_pair (x y : ℕ) :
    (ERMor1.natUnpairSnd).interp
        ![(ERMor1.natPair).interp ![x, y]] = y := by
  simp [Nat.unpair_pair]
```

- [ ] **Step 5: Register, build, commit**

Add `import GebLean.Utilities.ERTreeArith` to `GebLean.lean`.

```bash
lake build
lake test
git add GebLean/Utilities/ERTreeArith.lean GebLean.lean
git commit -m "Add ER-derived natPair/natUnpair with correctness"
```

---

### Task 13: ER-derived `BTL` fold-on-code

**Goal:** Two parts.  First, extend
`Utilities/SzudzikSeq.lean` with a labeled-BTL version of
`treeFoldOnCode`.  Second, package the new labeled-fold-on-code
as an `ERMor1` term.

**Files:**

* Modify: `GebLean/Utilities/SzudzikSeq.lean`
* Modify: `GebLean/Utilities/ERTreeArith.lean`

- [ ] **Step 1: `Nat.foldBTLOnCode` in SzudzikSeq.lean**

```lean
/-- Course-of-values fold on a `BTL` Gödel code.
Even codes `2 * n` decode to `BTL.leaf n`; odd codes
`2 * pair l r + 1` decode to `BTL.node (decode l) (decode r)`.
The leaf branch receives the label; the node branch receives the
two recursive results. -/
def Nat.foldBTLOnCode {α : Type*}
    (baseLeaf : ℕ → α) (stepNode : α → α → α) :
    ℕ → α := sorry

@[simp] theorem Nat.foldBTLOnCode_zero {α : Type*}
    (baseLeaf : ℕ → α) (stepNode : α → α → α) :
    Nat.foldBTLOnCode baseLeaf stepNode 0 = baseLeaf 0 := sorry

theorem Nat.foldBTLOnCode_encode {α : Type*}
    (baseLeaf : ℕ → α) (stepNode : α → α → α) (t : BTL) :
    Nat.foldBTLOnCode baseLeaf stepNode (BTL.encode t) =
      BTL.fold baseLeaf stepNode t := sorry
```

Mirrors `Nat.treeFoldOnCode` (lines 70-180 of SzudzikSeq.lean)
but for labeled BTL.  Use `Nat.treeFoldOnCode` and
`Nat.treeFoldOnCode_encodeBT` as templates.

- [ ] **Step 2: `ERMor1.foldBTLOnCode` in ERTreeArith.lean**

```lean
/-- ER-derived term simulating `BTL.fold` on a Gödel code. -/
def ERMor1.foldBTLOnCode {n : ℕ}
    (baseLeaf : ERMor1 (n + 1)) (stepNode : ERMor1 (n + 2)) :
    ERMor1 (n + 1) := sorry

@[simp] theorem ERMor1.interp_foldBTLOnCode {n : ℕ}
    (baseLeaf : ERMor1 (n + 1)) (stepNode : ERMor1 (n + 2))
    (ctx : Fin (n + 1) → ℕ) :
    (ERMor1.foldBTLOnCode baseLeaf stepNode).interp ctx =
      Nat.foldBTLOnCode
        (fun lbl =>
          baseLeaf.interp (Fin.cons lbl (Fin.tail ctx)))
        (fun a b => stepNode.interp
          (Fin.cons a (Fin.cons b (Fin.tail ctx))))
        (ctx 0) := sorry
```

See `GebLean/LawvereTreeERArith.lean`'s `TreeERMor1.treeFoldOnCode`
for an analogous packaging.  ER's unrestricted composition makes
this packaging a direct assembly rather than a per-case extension
of the TreeERMor1 version.

- [ ] **Step 3: Build, test, commit**

```bash
lake build
lake test
git add GebLean/Utilities/SzudzikSeq.lean \
        GebLean/Utilities/ERTreeArith.lean
git commit -m "Add ER-derived BTL fold-on-code with correctness"
```

---

### Task 14: `NatBTMor1.toER` back-translation + correctness

**Goal:** Define `NatBTMor1.toER` and `NatBTMor1.toER_bt`
(mutually recursive structural translation), with extensional
correctness theorems.  Substrate of Stage 2.

**Files:**

* Create: `GebLean/LawvereNatBTBackTrans.lean`
* Modify: `GebLean.lean`

- [ ] **Step 1: Header and imports**

Imports: `GebLean.LawvereNatBT`, `GebLean.Utilities.ERTreeArith`.
Docstring: see Stage β heading and the spec.

- [ ] **Step 2: Define `NatBTMor1.toER` and `NatBTMor1.toER_bt`**

Mutually recursive.  For `.nat` cases:

* `zero` → `ERMor1.zeroN _`.
* `succ x` → `ERMor1.comp ERMor1.succ (fun _ => x.toER)`.
* `natProj i` → `ERMor1.proj i`.
* `sub a b` → ER-comp of `ERMor1.sub` with `a.toER`, `b.toER`.
* `compNat (nm' := (k, 0)) f gNat _gBT` → `ERMor1.comp f.toER
  (fun i => (gNat i).toER)`.  Pattern-match on `nm' = (k, 0)`
  to capture the BT-arity-zero invariant.
* `bsum f` → `ERMor1.bsum f.toER`.
* `bprod f` → `ERMor1.bprod f.toER`.
* `foldBTNat baseLeaf stepNode tree` →
  `ERMor1.comp (ERMor1.foldBTLOnCode baseLeaf.toER stepNode.toER)
   (Fin.cons tree.toER_bt (fun i => ERMor1.proj i))`.
* `encodeBT t` → `t.toER_bt`.

For `.bt` cases:

* `leafBT label` → `2 * label.toER` (use `ERMor1.bsum (proj 1)`
  with bound 2, or a dedicated `mul2` helper).
* `nodeBT l r` → `ERMor1.succ (2 * Nat.pair (l.toER_bt) (r.toER_bt))`,
  using `ERMor1.natPair` from Task 12.
* `btProj i` → `i.elim0`.
* `compBT (nm' := (k, 0)) f gNat _gBT` → analogous to compNat.
* `foldBTBT _ _ _` → excluded by BT-arity-zero invariant on
  the ambient term.  Implementer either refines the inductive
  type or handles via absurd hypothesis.
* `decodeBT k` → `k.toER` (since `BTL.encode (BTL.decode k) = k`).

The `foldBTBT` exclusion needs an inductive invariant.  Two
approaches:

* **Path A:** Define a refined inductive `NatBTMor1Strict0`
  excluding `foldBTBT` and `compBT` with non-trivial `nm'.2`.
* **Path B:** Use a structural-induction helper with an
  ambient `NatBTMor1.allBTArity0` invariant.

Pick whichever leads to cleaner Lean code.

- [ ] **Step 3: Correctness theorems**

```lean
theorem NatBTMor1.toER_interp {n : ℕ}
    (t : NatBTMor1 (n, 0) .nat) (ctxN : Fin n → ℕ) :
    (t.toER).interp ctxN = t.interp ctxN Fin.elim0 := sorry

theorem NatBTMor1.toER_bt_interp {n : ℕ}
    (t : NatBTMor1 (n, 0) .bt) (ctxN : Fin n → ℕ) :
    (t.toER_bt).interp ctxN =
      (t.interp ctxN Fin.elim0).encode := sorry
```

Mutually recursive proofs.  Use Tasks 12-13's correctness
theorems plus per-constructor `@[simp]` interp lemmas plus
`Nat.unpair_pair`/`Nat.pair_unpair` as needed.

- [ ] **Step 4: Lift to `NatBTMorN` tuples**

```lean
def NatBTMorN.toER {n m : ℕ} (f : NatBTMorN (n, 0) (m, 0)) :
    ERMorN n m :=
  fun i => (f.natComps i).toER

theorem NatBTMorN.toER_interp {n m : ℕ}
    (f : NatBTMorN (n, 0) (m, 0)) (ctxN : Fin n → ℕ) :
    (f.toER).interp ctxN = (f.interp ctxN Fin.elim0).1 := by
  funext i
  exact (f.natComps i).toER_interp ctxN
```

- [ ] **Step 5: Build, test, commit**

```bash
lake build
lake test
git add GebLean/LawvereNatBTBackTrans.lean GebLean.lean
git commit -m "Add NatBTMor1.toER back-translation with correctness"
```

---

### Task 15: `LawvereNatBTPureCat` (TreeNatER) + Stage 3 iso

**Goal:** Define `LawvereNatBTPureCat` as a thin wrapper around
`LawvereERCat` with on-the-nose iso.

**Files:**

* Create: `GebLean/LawvereNatBTPure.lean`
* Modify: `GebLean.lean`

- [ ] **Step 1: Header and imports**

Imports: `GebLean.LawvereERQuot`, `GebLean.LawvereNatBT0`,
`Mathlib.CategoryTheory.Equivalence`.

- [ ] **Step 2: Define the wrapper**

```lean
@[ext]
structure LawvereNatBTPureObj where
  base : ℕ

def LawvereNatBTPureCat : Type := LawvereNatBTPureObj

instance : CategoryStruct LawvereNatBTPureCat where
  Hom a b := ERMorNQuo a.base b.base
  id a := ERMorNQuo.id a.base
  comp f g := ERMorNQuo.comp f g

instance : Category LawvereNatBTPureCat where
  id_comp := fun f => ERMorNQuo.id_comp f
  comp_id := fun f => ERMorNQuo.comp_id f
  assoc := fun f g h => ERMorNQuo.comp_assoc f g h
```

- [ ] **Step 3: Stage 3 functors**

```lean
def natBTJ : LawvereERCat ⥤ LawvereNatBTPureCat where
  obj n := ⟨n⟩
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl

def natBTKPure : LawvereNatBTPureCat ⥤ LawvereERCat where
  obj a := a.base
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl
```

- [ ] **Step 4: Stage 3 equivalence**

```lean
def natBTPureEquivalence : LawvereERCat ≌ LawvereNatBTPureCat where
  functor := natBTJ
  inverse := natBTKPure
  unitIso := Iso.refl _
  counitIso := Iso.refl _
  functor_unitIso_comp _ := rfl
```

(If `Iso.refl` and `rfl` don't work directly, fall back to
`NatIso.ofComponents` with identity components.)

- [ ] **Step 5: Build, test, commit**

Add `import GebLean.LawvereNatBTPure` to `GebLean.lean`.

```bash
lake build
lake test
git add GebLean/LawvereNatBTPure.lean GebLean.lean
git commit -m "Add LawvereNatBTPureCat and Stage 3 iso to LawvereERCat"
```

---

### Task 16: Stage 1 essential surjectivity (Szudzik on objects)

**Goal:** Prove `natBT0Inclusion` is essentially surjective via
the per-object iso `(n, m) ≅ (n + m, 0)`.

**Files:**

* Create: `GebLean/LawvereNatBTEquiv.lean`
* Modify: `GebLean.lean`

- [ ] **Step 1: Header and imports**

Imports: `GebLean.LawvereNatBT0`, `GebLean.LawvereNatBTPure`,
`Mathlib.CategoryTheory.Equivalence`.

- [ ] **Step 2: Pack/Unpack and per-object iso**

```lean
def natBTPack (nm : LawvereNatBTCat) : nm ⟶ (nm.1 + nm.2, 0) := by
  refine Quotient.mk _ ?_
  exact
    { natComps i :=
        i.addCases
          (fun j => NatBTMor1.natProj j)
          (fun j => NatBTMor1.encodeBT (NatBTMor1.btProj j))
      btComps := Fin.elim0 }

def natBTUnpack (nm : LawvereNatBTCat) : (nm.1 + nm.2, 0) ⟶ nm := by
  refine Quotient.mk _ ?_
  exact
    { natComps i :=
        NatBTMor1.natProj (Fin.castAdd nm.2 i)
      btComps i :=
        NatBTMor1.decodeBT (NatBTMor1.natProj (Fin.natAdd nm.1 i)) }

theorem natBTPack_unpack (nm : LawvereNatBTCat) :
    natBTPack nm ≫ natBTUnpack nm = 𝟙 nm := by
  apply Quotient.sound
  intro ctxN ctxB
  -- BT part: decodeBT ∘ encodeBT = id via BTL.decode_encode.
  sorry

theorem natBTUnpack_pack (nm : LawvereNatBTCat) :
    natBTUnpack nm ≫ natBTPack nm = 𝟙 (nm.1 + nm.2, 0) := by
  apply Quotient.sound
  intro ctxN ctxB
  sorry

def natBTIsoPack (nm : LawvereNatBTCat) : nm ≅ (nm.1 + nm.2, 0) where
  hom := natBTPack nm
  inv := natBTUnpack nm
  hom_inv_id := natBTPack_unpack nm
  inv_hom_id := natBTUnpack_pack nm
```

- [ ] **Step 3: Essential surjectivity**

```lean
instance : natBT0Inclusion.EssSurj where
  mem_essImage nm :=
    ⟨⟨(nm.1 + nm.2, 0), rfl⟩, ⟨(natBTIsoPack nm).symm⟩⟩
```

- [ ] **Step 4: Stage 1 equivalence**

```lean
noncomputable def natBTSubInclEquiv :
    LawvereNatBT0Cat ≌ LawvereNatBTCat :=
  natBT0Inclusion.asEquivalence
```

- [ ] **Step 5: Build, test, commit**

Add `import GebLean.LawvereNatBTEquiv` to `GebLean.lean`.

```bash
lake build
lake test
git add GebLean/LawvereNatBTEquiv.lean GebLean.lean
git commit -m "Add Stage 1 equivalence via Szudzik on objects"
```

---

### Task 17: Stage 2 equivalence (back-translation)

**Goal:** Package the back-translation from Task 14 as a
categorical equivalence
`LawvereNatBTPureCat ≃ LawvereNatBT0Cat`.

**Files:**

* Modify: `GebLean/LawvereNatBTEquiv.lean`

- [ ] **Step 1: Forward functor (inclusion of strict-ER)**

Define `ERMor1.toNatBT_of_ER : ERMor1 n → NatBTMor1 (n, 0) .nat`
by structural recursion (the syntactic embedding of ER terms as
NatBT terms with no BT machinery).  Lift to `ERMorN.toNatBT` and
`ERMorNQuo.toNatBT_of_ER`.  Use this in:

```lean
def natBTPureToTree0 : LawvereNatBTPureCat ⥤ LawvereNatBT0Cat where
  obj a := ⟨(a.base, 0), rfl⟩
  map {a b} f := -- wrap ERMorNQuo a.base b.base as NatBTMorNQuo
    sorry
  map_id := sorry
  map_comp := sorry
```

- [ ] **Step 2: Backward functor (back-translation)**

```lean
def tree0ToPure : LawvereNatBT0Cat ⥤ LawvereNatBTPureCat where
  obj a := ⟨a.obj.1⟩
  map {a b} f :=
    Quotient.lift
      (fun raw => Quotient.mk _ (NatBTMorN.toER raw))
      (fun _ _ h => by sorry)
      f
  map_id := sorry
  map_comp := sorry
```

- [ ] **Step 3: Round-trip natural isos**

```lean
theorem natBTPureToTree0_tree0ToPure :
    natBTPureToTree0 ⋙ tree0ToPure = 𝟭 LawvereNatBTPureCat := sorry

def tree0ToPure_natBTPureToTree0 :
    tree0ToPure ⋙ natBTPureToTree0 ≅ 𝟭 LawvereNatBT0Cat := by
  refine NatIso.ofComponents (fun a => ?_) ?_
  · sorry
  · sorry
```

- [ ] **Step 4: Stage 2 equivalence**

```lean
def natBTPureTree0Equiv :
    LawvereNatBTPureCat ≌ LawvereNatBT0Cat where
  functor := natBTPureToTree0
  inverse := tree0ToPure
  unitIso := eqToIso natBTPureToTree0_tree0ToPure.symm
  counitIso := tree0ToPure_natBTPureToTree0
  functor_unitIso_comp _ := by sorry
```

- [ ] **Step 5: Build, test, commit**

```bash
lake build
lake test
git add GebLean/LawvereNatBTEquiv.lean
git commit -m "Add Stage 2 equivalence via NatBTMor1.toER back-translation"
```

---

### Task 18: Compose three stages

**Goal:** Final `LawvereERCat ≃ LawvereNatBTCat`.

**Files:**

* Modify: `GebLean/LawvereNatBTEquiv.lean`

- [ ] **Step 1: Compose**

```lean
noncomputable def natBTEquivalence :
    LawvereERCat ≌ LawvereNatBTCat :=
  natBTPureEquivalence.trans
    (natBTPureTree0Equiv.trans natBTSubInclEquiv)
```

- [ ] **Step 2: Build, test, commit**

```bash
lake build
lake test
git add GebLean/LawvereNatBTEquiv.lean
git commit -m "Compose three-stage equivalence LawvereERCat ≃ LawvereNatBTCat"
```

---

### Task 19: Transport Ackermann non-fullness

**Files:**

* Create: `GebLean/LawvereNatBTTransport.lean`

- [ ] **Step 1: Create file**

```lean
import GebLean.LawvereNatBTEquiv
import GebLean.LawvereERInterp
import GebLean.LawvereERPrimrec
import GebLean.LawvereERTetration

/-!
# Transport of Phase 4f Results to `LawvereNatBT`

Ackermann non-fullness (Phase 4f.1) and tetration non-elementarity
(Phase 4f.2) are proved for `LawvereER`.  Via the categorical
equivalence, both lift verbatim to `LawvereNatBT`.
-/

namespace GebLean

open CategoryTheory

end GebLean
```

- [ ] **Step 2: Define the induced interp on `LawvereNatBTCat`**

```lean
/-- Induced interpretation on the `.nat`-output fragment of
`LawvereNatBTCat`.  For morphisms `(n, 0) → (1, 0)` — that is,
ℕ-valued morphisms with no BT inputs — the interpretation is a
function `(Fin n → ℕ) → ℕ`, matching `erInterpFunctor` via the
equivalence. -/
def natBTInterpNat :
    LawvereNatBTCat ⥤ Type :=
  natBTInterpFunctor
```

- [ ] **Step 3: Transport Ackermann non-fullness**

```lean
/-- Ackermann cannot be represented as a `LawvereNatBTCat` morphism
`((2, 0) : LawvereNatBTCat) ⟶ (1, 0)` with ℕ-valued inputs and
output — a direct consequence of `LawvereER`'s non-fullness via
Ackermann (Phase 4f.1), transported across the equivalence. -/
theorem natBTInterp_not_full_via_ackermann :
    ¬ natBTInterpFunctor.Full := by
  intro h
  -- Use the equivalence to translate the hypothesis back to
  -- `erInterpFunctor.Full`, contradicting
  -- `erInterpFunctor_not_full` from `LawvereERPrimrec`.
  sorry
```

- [ ] **Step 4: Transport tetration non-elementarity**

```lean
/-- Tetration cannot be represented as a `LawvereNatBTCat`
morphism — a direct consequence of `tetration_not_ER` from Phase
4f.2, transported across the equivalence. -/
theorem natBTInterp_not_full_via_tetration :
    ¬ natBTInterpFunctor.Full := by
  intro h
  -- Use the equivalence to translate back to
  -- `erInterpFunctor_not_full_via_tetration` from
  -- `LawvereERTetration`.
  sorry
```

- [ ] **Step 5: Build and commit**

```bash
lake build GebLean.LawvereNatBTTransport
git add GebLean/LawvereNatBTTransport.lean
git commit -m "Transport Ackermann and tetration non-elementarity to LawvereNatBT"
```

---

### Task 20: Register Stage β and write tests

**Files:**

* Modify: `GebLean.lean` (verify all Stage β library modules
  are imported; Tasks 11-19 each registered theirs)
* Create: `GebLeanTests/LawvereNatBT0.lean`
* Create: `GebLeanTests/LawvereERTreeArith.lean`
* Create: `GebLeanTests/LawvereNatBTBackTrans.lean`
* Create: `GebLeanTests/LawvereNatBTPure.lean`
* Create: `GebLeanTests/LawvereNatBTEquiv.lean`
* Create: `GebLeanTests/LawvereNatBTTransport.lean`
* Modify: `GebLeanTests.lean`

- [ ] **Step 1: Verify library module registration**

Tasks 11-19 each registered their library module in
`GebLean.lean` as part of the task's commit.  Confirm the
following imports are present (no new ones to add):

```lean
import GebLean.LawvereNatBT0
import GebLean.Utilities.ERTreeArith
import GebLean.LawvereNatBTBackTrans
import GebLean.LawvereNatBTPure
import GebLean.LawvereNatBTEquiv
import GebLean.LawvereNatBTTransport
```

- [ ] **Step 2: Write tests**

```lean
-- GebLeanTests/LawvereNatBT0.lean
import GebLean.LawvereNatBT0
open GebLean CategoryTheory

example : Category LawvereNatBT0Cat := inferInstance
example :
    HasChosenFiniteProducts LawvereNatBT0Cat := inferInstance
example : LawvereNatBT0Cat ⥤ LawvereNatBTCat := natBT0Inclusion
example : natBT0Inclusion.Full := inferInstance
example : natBT0Inclusion.Faithful := inferInstance
```

```lean
-- GebLeanTests/LawvereERTreeArith.lean
import GebLean.Utilities.ERTreeArith
open GebLean

-- Spot-check ER-derived Szudzik primitives
#guard (ERMor1.natPair).interp ![3, 5] = Nat.pair 3 5
#guard (ERMor1.natUnpairFst).interp
    ![Nat.pair 3 5] = 3
#guard (ERMor1.natUnpairSnd).interp
    ![Nat.pair 3 5] = 5

-- Spot-check fold-on-code on a small tree
example : (ERMor1.foldBTLOnCode
    (ERMor1.proj 0) (ERMor1.proj 0)).interp
    ![BTL.encode (BTL.leaf 7)] = 7 := by
  simp [Nat.foldBTLOnCode_encode]
```

```lean
-- GebLeanTests/LawvereNatBTBackTrans.lean
import GebLean.LawvereNatBTBackTrans
open GebLean

-- Back-translation type-checks
example {n : ℕ} (t : NatBTMor1 (n, 0) .nat) :
    ERMor1 n := t.toER

example {n : ℕ} (t : NatBTMor1 (n, 0) .bt) :
    ERMor1 n := t.toER_bt
```

```lean
-- GebLeanTests/LawvereNatBTPure.lean
import GebLean.LawvereNatBTPure
open GebLean CategoryTheory

example : Category LawvereNatBTPureCat := inferInstance
example : LawvereERCat ⥤ LawvereNatBTPureCat := natBTJ
example : LawvereNatBTPureCat ⥤ LawvereERCat := natBTKPure
example : LawvereERCat ≌ LawvereNatBTPureCat := natBTPureEquivalence
```

```lean
-- GebLeanTests/LawvereNatBTEquiv.lean
import GebLean.LawvereNatBTEquiv
open GebLean CategoryTheory

example : natBT0Inclusion.EssSurj := inferInstance
example : LawvereNatBTPureCat ≌ LawvereNatBT0Cat :=
  natBTPureTree0Equiv
example : LawvereNatBT0Cat ≌ LawvereNatBTCat := natBTSubInclEquiv
example : LawvereERCat ≌ LawvereNatBTCat := natBTEquivalence
```

```lean
-- GebLeanTests/LawvereNatBTTransport.lean
import GebLean.LawvereNatBTTransport
open GebLean CategoryTheory

example : ¬ natBTInterpFunctor.Full :=
  natBTInterp_not_full_via_ackermann
example : ¬ natBTInterpFunctor.Full :=
  natBTInterp_not_full_via_tetration
```

- [ ] **Step 3: Register test modules and run**

Add to `GebLeanTests.lean`:

```lean
import GebLeanTests.LawvereNatBT0
import GebLeanTests.LawvereERTreeArith
import GebLeanTests.LawvereNatBTBackTrans
import GebLeanTests.LawvereNatBTPure
import GebLeanTests.LawvereNatBTEquiv
import GebLeanTests.LawvereNatBTTransport
```

```bash
lake build && lake test
```

Expected: both PASS cleanly.

- [ ] **Step 4: Commit**

```bash
git add GebLean.lean GebLeanTests/LawvereNatBT0.lean \
        GebLeanTests/LawvereERTreeArith.lean \
        GebLeanTests/LawvereNatBTBackTrans.lean \
        GebLeanTests/LawvereNatBTPure.lean \
        GebLeanTests/LawvereNatBTEquiv.lean \
        GebLeanTests/LawvereNatBTTransport.lean GebLeanTests.lean
git commit -m "Register and test Stage β of LawvereNatBT"
```

---

## Stage γ: lex completion and subtypes

### Task 21: `LawvereNatBTLexCat` via decidable subobjects

**Files:**

* Create: `GebLean/LawvereNatBTLex.lean`

- [ ] **Step 1: Create file and mirror `LawvereERLex`'s pattern**

```lean
import GebLean.LawvereNatBTQuot
import GebLean.LawvereERLex

/-!
# Lex Completion of `LawvereNatBTCat`

Decidable subobjects mirror `LawvereERLex`'s pattern: objects are
pairs `((n, m), p)` with `p` a decidable predicate on
`ℕⁿ × BTLᵐ`; morphisms respect `p`.  Finite products are via
predicate conjunction; equalizers via predicate refinement via
equality on all output components.
-/

namespace GebLean

open CategoryTheory

end GebLean
```

- [ ] **Step 2: Define boolean predicates via NatBTMor1**

Predicates on `ℕⁿ × BTLᵐ` as `NatBTMor1 (n, m) .nat` terms
interpreting into `{0, 1}` (or any numerical boolean convention —
use the same convention as `LawvereERLex`).

```lean
/-- Boolean predicate on `LawvereNatBTCat`-objects: a `.nat`-sort
term whose interpretation is at most 1.  Mirrors
`ERBoolPred` from `LawvereERLex.lean`. -/
structure NatBTBoolPred (nm : ℕ × ℕ) where
  term : NatBTMor1 nm .nat
  eval_le_one : ∀ ctxN ctxB, term.interp ctxN ctxB ≤ 1
```

- [ ] **Step 3: Define the lex objects**

```lean
structure LexObjNatBT where
  base : ℕ × ℕ
  pred : NatBTBoolPred base

-- equality-by-predicate can be via the quotient setoid, mirroring
-- `LexObj` in `LawvereERLex`
```

- [ ] **Step 4: Define lex morphisms and the category**

```lean
-- Mirror `LawvereERLex`'s `LawvereERLexCat` construction:
-- morphisms as NatBTMor1 tuples that respect the source predicate,
-- quotiented by extensional equality restricted to the source
-- predicate's carrier.

def LawvereNatBTLexCat : Type := LexObjNatBT
instance : Category LawvereNatBTLexCat := ...
```

- [ ] **Step 5: Build and commit**

```bash
lake build GebLean.LawvereNatBTLex
git add GebLean/LawvereNatBTLex.lean
git commit -m "Add LawvereNatBTLexCat via decidable subobjects"
```

---

### Task 22: Finite products and equalizers on the lex

**Files:**

* Modify: `GebLean/LawvereNatBTLex.lean`

Follow the exact pattern of `LawvereERLex.lean`'s finite products
and equalizers.  Chosen finite products from conjunction of
predicates; chosen equalizers from refining the source predicate
with componentwise equality via `NatBTBoolPred`'s `allEq` analogue.
Assemble `HasChosenFiniteProducts`, `HasChosenEqualizers`, and
`HasChosenFiniteLimits`.

- [ ] **Step 1: Define conjunction and equality-refinement of
  predicates**

- [ ] **Step 2: Define product and equalizer objects**

- [ ] **Step 3: Prove universal properties**

- [ ] **Step 4: Assemble the typeclass instances**

- [ ] **Step 5: Build and commit**

```bash
lake build GebLean.LawvereNatBTLex
git add GebLean/LawvereNatBTLex.lean
git commit -m "Add finite products and equalizers for LawvereNatBTLexCat"
```

---

### Task 23: Unlabeled-BT subtype and finite-alphabet subtype

**Files:**

* Create: `GebLean/LawvereNatBTSubtypes.lean`

- [ ] **Step 1: Define the unlabeled-BT predicate**

```lean
import GebLean.LawvereNatBTLex
import GebLean.LawvereTreeER

/-!
# Specific Decidable Subobjects of LawvereNatBT

* Unlabeled BT: leaves with label 0.
* Finite-alphabet BT: leaves with label ≤ k.
* Faithful embedding `LawvereTreeER ↪ LawvereNatBT`.
-/

namespace GebLean

open CategoryTheory

/-- Predicate: "every leaf label equals 0".  As a `NatBTBoolPred`,
this is a NatBTMor1 term that folds the input BT (via `foldBTNat`)
and returns 1 if the folded computation confirms all labels are
zero, 0 otherwise. -/
def unlabeledPred (nm : ℕ × ℕ) : NatBTBoolPred nm :=
  ... -- encode via foldBTNat and boolean AND
```

- [ ] **Step 2: Define the finite-alphabet predicate**

```lean
def finAlphabetPred (nm : ℕ × ℕ) (k : ℕ) : NatBTBoolPred nm :=
  ... -- encode via foldBTNat and boolean-AND with "≤ k" check
```

- [ ] **Step 3: Faithful embedding `LawvereTreeER ↪ LawvereNatBT`**

```lean
def lawvereTreeERToNatBT :
    LawvereTreeERCat ⥤ LawvereNatBTCat where
  obj n := (0, n)
  map f := ...
  -- translate unlabeled BT operations to labeled BT operations
  -- with all `leaf` constructors replaced by `leafBT 0`
```

- [ ] **Step 4: Prove faithfulness**

```lean
instance : lawvereTreeERToNatBT.Faithful where
  map_injective := by
    -- reduce to extensional equality on chain-BTs; since all leaf
    -- labels are 0, the labeling is uniform and distinct unlabeled
    -- morphisms remain distinct after embedding
    sorry
```

- [ ] **Step 5: Build and commit**

```bash
lake build GebLean.LawvereNatBTSubtypes
git add GebLean/LawvereNatBTSubtypes.lean
git commit -m "Add unlabeled and finite-alphabet subtypes plus LawvereTreeER embedding"
```

---

### Task 24: Register Stage γ and write tests

**Files:**

* Modify: `GebLean.lean`
* Create: `GebLeanTests/LawvereNatBTLex.lean`
* Create: `GebLeanTests/LawvereNatBTSubtypes.lean`
* Modify: `GebLeanTests.lean`

- [ ] **Step 1: Register library modules**

Add to `GebLean.lean`:

```lean
import GebLean.LawvereNatBTLex
import GebLean.LawvereNatBTSubtypes
```

- [ ] **Step 2: Write tests**

```lean
-- GebLeanTests/LawvereNatBTLex.lean
import GebLean.LawvereNatBTLex
open GebLean CategoryTheory
example : HasChosenFiniteProducts LawvereNatBTLexCat := inferInstance
example : HasChosenEqualizers LawvereNatBTLexCat := inferInstance
example : HasChosenFiniteLimits LawvereNatBTLexCat := inferInstance
```

```lean
-- GebLeanTests/LawvereNatBTSubtypes.lean
import GebLean.LawvereNatBTSubtypes
open GebLean CategoryTheory
example : LawvereTreeERCat ⥤ LawvereNatBTCat := lawvereTreeERToNatBT
example : lawvereTreeERToNatBT.Faithful := inferInstance
```

- [ ] **Step 3: Register test modules**

Add to `GebLeanTests.lean`:

```lean
import GebLeanTests.LawvereNatBTLex
import GebLeanTests.LawvereNatBTSubtypes
```

- [ ] **Step 4: Build and test**

```bash
lake build && lake test
```

Expected: both PASS cleanly.

- [ ] **Step 5: Commit**

```bash
git add GebLean.lean GebLeanTests/LawvereNatBTLex.lean \
        GebLeanTests/LawvereNatBTSubtypes.lean GebLeanTests.lean
git commit -m "Register and test Stage γ of LawvereNatBT"
```

---

## Finalization

### Task 25: Update the workstream tracker

**Files:**

* Modify: `.session/workstreams/lawvere-elementary-recursive.md`

- [ ] **Step 1: Append completion paragraph**

Under the Phase 4g.2 heading, add:

```markdown
Phase 4g.2 redesigned as `LawvereNatBT` (spec
`docs/superpowers/specs/2026-04-17-lawvere-natbt-design.md`):
two-sorted Lawvere theory over ℕ and labeled BT, categorically
equivalent to `LawvereER` via Szudzik-based bridges.  See
`GebLean/LawvereNatBT*.lean` and `GebLean/LawvereNatBTLex.lean`.
Phase 4g.1's single-sort unlabeled theory is preserved as a
parallel development and embeds into `LawvereNatBT` via
`GebLean/LawvereNatBTSubtypes.lean`'s `lawvereTreeERToNatBT`.
```

- [ ] **Step 2: Mark the sub-project complete**

If the tracker has a checkbox for Phase 4g.2, update it to done
with the `LawvereNatBT` design name.

- [ ] **Step 3: Commit**

```bash
git add .session/workstreams/lawvere-elementary-recursive.md
git commit -m "Mark Phase 4g.2 complete via LawvereNatBT redesign"
```

---

## Self-Review

**Spec coverage:**

* D1 (ℕ × ℕ indexing) — Tasks 2, 4, 7.
* D2 (labeled BT with ℕ leaves) — Task 1.
* D3 (bridge generators in both directions) — Task 2 constructor
  list includes `encodeBT` and `decodeBT`.
* D4 (fold-only BT generators, no destructors) — Task 2 constructor
  list includes `leafBT`, `nodeBT`, `btProj`, `compBT`, `foldBTNat`,
  `foldBTBT` and nothing else.
* D5 (ℕ arithmetic unchanged from LawvereER) — Task 2 constructors
  mirror `ERMor1` exactly on the ℕ sort.
* D6 (three-stage factorization
  `LawvereERCat ≃ LawvereNatBTPureCat ≃ LawvereNatBT0Cat ≃
  LawvereNatBTCat`) — Tasks 11–18 (substrate 12–14; Stage 3
  iso 15; Stage 1 equivalence 16; Stage 2 equivalence 17;
  composition 18).
* D7 (faithful embedding of `LawvereTreeER`) — Task 23.
* D8 (lex completion with decidable subobjects) — Tasks 21–23.

**Placeholder scan:**

The plan contains `sorry` placeholders inside tactic proofs where
the exact tactic script is implementation-dependent (e.g., the
`comp` well-definedness proof, Mathlib-specific equivalence-builder
invocations).  These are flagged with "implementer completes"
comments; the final implementation must replace every `sorry` with
a real proof before the task's commit.

Conceptual-level `...` placeholders appear only in the lex Task
22's sub-step body, where the full construction mirrors
`LawvereERLex.lean` — the implementer follows the existing file as
a template and fills in the analogous structure.  No task has a
conceptually unspecified goal.

**Type consistency:**

* `NatBTMor1`, `NatBTMorN`, `NatBTMorNQuo`, `LawvereNatBTCat`,
  `LawvereNatBTLexCat` used consistently across tasks.
* `NatBTSort` with constructors `.nat` and `.bt` used uniformly
  from Task 2 onward.
* `BTL` with `BTL.leaf` and `BTL.node` (labeled) distinct from
  `BT.leaf` / `BT.node` (unlabeled, from Phase 4g.1).
* `LawvereNatBT0Cat` is the `m = 0` `FullSubcategory` of
  `LawvereNatBTCat`; `natBT0Inclusion : LawvereNatBT0Cat ⥤
  LawvereNatBTCat` is its inclusion (full and faithful by
  construction; essentially surjective by Task 13).
* `natBTJ : LawvereERCat ⥤ LawvereNatBTPureCat` and
  `natBTKPure : LawvereNatBTPureCat ⥤ LawvereERCat` are the
  mutually-inverse functors of Task 15's Stage 3 on-the-nose
  equivalence `natBTPureEquivalence`.
* `LawvereNatBTPureCat` is the thin wrapper around `LawvereERCat`
  introduced in Task 15.
* Task 12 supplies the ER-derived Szudzik pairing:
  `ERMor1.natPair`, `ERMor1.natUnpairFst`,
  `ERMor1.natUnpairSnd`.  Task 13 supplies `Nat.foldBTLOnCode`
  and `ERMor1.foldBTLOnCode`.  Task 14 supplies
  `NatBTMor1.toER` and `NatBTMor1.toER_bt`.
* Task 16 supplies `natBTPack`, `natBTUnpack`, `natBTIsoPack`,
  and `natBTSubInclEquiv : LawvereNatBT0Cat ≌ LawvereNatBTCat`.
* Task 17 supplies `natBTPureToTree0`, `tree0ToPure`, and
  `natBTPureTree0Equiv : LawvereNatBTPureCat ≌ LawvereNatBT0Cat`.
* `natBTEquivalence : LawvereERCat ≌ LawvereNatBTCat` is the
  composed equivalence of Task 18.
* `natBTInterpFunctor` is the `Type`-valued interpretation;
  `lawvereTreeERToNatBT` is the embedding of Phase 4g.1's theory.

**Risk flags:**

* The exact Mathlib API for `FullSubcategory` (Task 11) and for
  assembling a categorical equivalence from fully-faithful +
  essentially-surjective data (Tasks 16-18) may have evolved
  across mathlib versions.  The implementer should verify the
  current names (`FullSubcategory.category`,
  `FullSubcategory.ι`, `FullSubcategory.lift`,
  `Functor.asEquivalence`, `Equivalence.ofFullyFaithful`, etc.)
  via `lean_local_search` and `lean_hover_info`, and adapt the
  task's skeleton accordingly.  A small `noncomputable`
  annotation may be needed at the equivalence-builder
  invocation; if a constructive alternative exists, prefer it.
* Task 14's `NatBTMor1.toER` back-translation requires handling
  `foldBTBT` and `compBT` with non-zero BT arity via an
  inductive invariant (Path A: refined `NatBTMor1Strict0`; Path
  B: ambient `allBTArity0` predicate).  If the straightforward
  structural recursion does not type-check, factor through an
  auxiliary lemma showing every `NatBTMor1 (n, 0) .bt` term
  reduces extensionally to `decodeBT k` for some
  `k : ERMor1 n`, then handle the remaining cases by appeal to
  the round-trip equations.
* The lex-completion tasks (21, 22, 23) mirror `LawvereERLex.lean`
  closely; if the existing file's structure doesn't port cleanly
  — e.g., if equality-refinement of predicates needs a different
  proof for the two-sort case — escalate with a halt notice and
  we adjust.
