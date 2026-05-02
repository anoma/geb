# BTPair: Bijection between Finite-Alphabet Binary Trees and ℕ

## Goal

Implement, in a new file `GebLean/PLang/BTPair.lean`, the
"tree of finite alphabet" pairing algorithm described at
<https://en.wikipedia.org/wiki/Pairing_function#Restriction_to_natural_numbers>.

Concretely, for any `n : ℕ`, exhibit a bijection

```lean
BTα (Fin (n + 1)) ≃ ℕ
```

where `BTα α` is the parametric labeled-binary-tree type
specializing the Type-level free monad of `polyProdType` at the
`α`-fibered carrier. Compose through `ℕ` to obtain
`BTα (Fin (n + 1)) ≃ BTα (Fin (m + 1))` for any `m, n`, and
specialize at `m = 0` (composed with `Fin 1 ≃ PUnit`) to obtain
`BTα (Fin (n + 1)) ≃ BT.{0}`, where `BT.{0}` is the existing
unlabeled binary tree from `LawvereBT.lean`.

The encoding additionally orders trees by depth: trees of depth
≤ `d` are exactly those whose encoding is ≤ that of the perfect
depth-`d` tree.

Companion housekeeping work:

- Add aliases in `PLang/Syntax.lean` for the Type-specialization
  of the free monad, and for the four evaluation functors
  (`polyProd` / `polyProdFreeM` at general `X`, plus their
  `Type` specializations).
- Relocate the existing `encodeBT` / `decodeBT` / round-trip
  theorems / `Encodable BT.{0}` instance from
  `LawvereBTPrimrec.lean` to `BTPair.lean`, recovering them as
  the `n = 0` case of the new generic encoding (with explicit
  connecting lemmas for both encode and decode).

## Mathlib-first

Before introducing any auxiliary lemma — particularly
arithmetic, finite-set, ordering, or tree-related results —
first check whether mathlib already provides it. Use
`lean_local_search`, `lean_leansearch`, `lean_loogle`, and the
Loogle web tool. Prefer a mathlib import to a re-derivation.

Specific lookups for this work:

- `Fin 1 ≃ PUnit` (candidates: `Fin.equivPUnit`,
  `Equiv.equivOfUnique`, `finOneEquiv`).
- `Nat.pair` monotonicity in either argument.
- Any existing `Tree.depth` / `Tree.height` predicate that
  could be reused if compatible.

## Architecture

Three changes:

1. **`PLang/Syntax.lean`** — five new `abbrev`s next to the
   existing `polyProdType` and `polyProdFreeM`.
2. **`PLang/BTPair.lean`** (new) — parametric labeled binary
   trees, the encoding bijection, the alphabet-shift bijection,
   the perfect-tree generator, the depth-ordering theorem, and
   the relocated unlabeled-tree API.
3. **`LawvereBTPrimrec.lean`** — loses the relocated block;
   imports the new module so existing call sites compile
   unchanged.

`PLang.lean` gets `BTPair` added to its re-exports.

## Section 1 — Aliases in `PLang/Syntax.lean`

```lean
/-- The free monad of `polyProdType`, specialized to `Type` via
`X = PUnit`. -/
abbrev polyProdFreeMType : PolyEndo PUnit.{u + 1} :=
  polyProdFreeM PUnit.{u + 1}

abbrev polyProdEvalFunctor (X : Type u) : Over X ⥤ Over X :=
  polyBetweenEvalFunctor X X (polyProd X)

abbrev polyProdFreeMEvalFunctor (X : Type u) :
    Over X ⥤ Over X :=
  polyBetweenEvalFunctor X X (polyProdFreeM X)

abbrev polyProdTypeEvalFunctor :
    Over PUnit.{u + 1} ⥤ Over PUnit.{u + 1} :=
  polyProdEvalFunctor PUnit.{u + 1}

abbrev polyProdFreeMTypeEvalFunctor :
    Over PUnit.{u + 1} ⥤ Over PUnit.{u + 1} :=
  polyProdFreeMEvalFunctor PUnit.{u + 1}
```

## Section 2 — `BTα` parametric type and basic operations

```lean
def BTα.carrier (α : Type u) : Over PUnit.{u + 1} :=
  Over.mk (fun _ : α => PUnit.unit)

abbrev BTα (α : Type u) : Type u :=
  PolyFreeM (BTα.carrier α) polyProdType PUnit.unit

def BTα.leaf {α : Type u} (a : α) : BTα α :=
  polyFreeMPure (BTα.carrier α) polyProdType ⟨a, rfl⟩

def BTα.node {α : Type u} (l r : BTα α) : BTα α :=
  polyProdFreeMNode (BTα.carrier α) l r

def BTα.fold {α β : Type u}
    (onLeaf : α → β) (onNode : β → β → β) (t : BTα α) : β :=
  polyProdFreeMFoldAt (BTα.carrier α)
    (onLeaf := fun {_} v => onLeaf v.val)
    (onNode := onNode) t

@[simp] theorem BTα.fold_leaf
    {α β : Type u} (onLeaf : α → β) (onNode : β → β → β) (a : α) :
    BTα.fold onLeaf onNode (BTα.leaf a) = onLeaf a

@[simp] theorem BTα.fold_node
    {α β : Type u} (onLeaf : α → β) (onNode : β → β → β)
    (l r : BTα α) :
    BTα.fold onLeaf onNode (BTα.node l r) =
      onNode (BTα.fold onLeaf onNode l)
        (BTα.fold onLeaf onNode r)

theorem BTα.leaf_or_node {α : Type u} (t : BTα α) :
    (∃ a, t = BTα.leaf a) ∨ (∃ l r, t = BTα.node l r)
```

`leaf_or_node` mirrors `BT.leaf_or_node` in `LawvereBT.lean`,
extending the leaf case from `PUnit.unit` to an arbitrary
`a : α`.

## Section 3 — Encoding to `Nat`

```lean
def encodeBTn (n : ℕ) (t : BTα.{0} (Fin (n + 1))) : ℕ :=
  BTα.fold (fun i : Fin (n + 1) => i.val)
    (fun el er => (n + 1) + Nat.pair el er) t

@[simp] theorem encodeBTn_leaf (n : ℕ) (i : Fin (n + 1)) :
    encodeBTn n (BTα.leaf i) = i.val

@[simp] theorem encodeBTn_node (n : ℕ)
    (l r : BTα.{0} (Fin (n + 1))) :
    encodeBTn n (BTα.node l r) =
      (n + 1) + Nat.pair (encodeBTn n l) (encodeBTn n r)

def decodeBTn (n : ℕ) : ℕ → BTα.{0} (Fin (n + 1))
  | k =>
    if h : k < n + 1 then
      BTα.leaf ⟨k, h⟩
    else
      let r := k - (n + 1)
      BTα.node
        (decodeBTn n (Nat.unpair r).1)
        (decodeBTn n (Nat.unpair r).2)
  termination_by k => k
  decreasing_by
    all_goals
      have hge : n + 1 ≤ k := Nat.not_lt.mp h
      have hlt : k - (n + 1) < k := by omega
      first
        | exact Nat.lt_of_le_of_lt
            (Nat.unpair_left_le _) hlt
        | exact Nat.lt_of_le_of_lt
            (Nat.unpair_right_le _) hlt

@[simp] theorem decodeBTn_lt (n k : ℕ) (h : k < n + 1) :
    decodeBTn n k = BTα.leaf ⟨k, h⟩

@[simp] theorem decodeBTn_ge (n k : ℕ) (h : ¬ k < n + 1) :
    decodeBTn n k =
      let r := k - (n + 1)
      BTα.node
        (decodeBTn n (Nat.unpair r).1)
        (decodeBTn n (Nat.unpair r).2)
```

## Section 4 — Round-trips and the bijection

```lean
theorem decodeBTn_encodeBTn (n : ℕ)
    (t : BTα.{0} (Fin (n + 1))) :
    decodeBTn n (encodeBTn n t) = t

theorem encodeBTn_decodeBTn (n k : ℕ) :
    encodeBTn n (decodeBTn n k) = k

def equivBTnNat (n : ℕ) : BTα.{0} (Fin (n + 1)) ≃ ℕ where
  toFun     := encodeBTn n
  invFun    := decodeBTn n
  left_inv  := decodeBTn_encodeBTn n
  right_inv := encodeBTn_decodeBTn n
```

The first round-trip is structural induction over the underlying
W-type (via `BTα.leaf_or_node`); the second is strong induction
on `k`. Both follow the patterns in `LawvereBTPrimrec.lean`'s
`decodeBT_encodeBT_gen` and `LawvereNatBT.lean`'s
`BTL.encode_decode`.

## Section 5 — Alphabet-shift bijection and bridge to `BT.{0}`

```lean
def equivBTnBTm (n m : ℕ) :
    BTα.{0} (Fin (n + 1)) ≃ BTα.{0} (Fin (m + 1)) :=
  (equivBTnNat n).trans (equivBTnNat m).symm

def equivBTnBT1 (n : ℕ) :
    BTα.{0} (Fin (n + 1)) ≃ BTα.{0} (Fin 1) :=
  equivBTnBTm n 0

def BTα.equivOfEquiv {α β : Type u} (e : α ≃ β) :
    BTα α ≃ BTα β where
  toFun :=
    BTα.fold (fun a => BTα.leaf (e a)) BTα.node
  invFun :=
    BTα.fold (fun b => BTα.leaf (e.symm b)) BTα.node
  left_inv  := -- structural induction via leaf_or_node
    sorry
  right_inv := sorry

def equivBTαPUnitBT : BTα.{0} PUnit ≃ BT.{0} :=
  -- toFun  := BTα.fold (fun _ => BT.leaf) BT.node
  -- invFun := BT.fold (BTα.leaf PUnit.unit) BTα.node
  sorry

def finOneEquivPUnit : Fin 1 ≃ PUnit :=
  -- check mathlib first; if absent, define directly
  sorry

def equivBTnBT (n : ℕ) : BTα.{0} (Fin (n + 1)) ≃ BT.{0} :=
  ((equivBTnBT1 n).trans
    (BTα.equivOfEquiv finOneEquivPUnit)).trans equivBTαPUnitBT
```

The bridge `equivBTαPUnitBT` is needed because
`BT.carrier = overTerminal PUnit = Over.mk (fun x : PUnit => x)`
while `BTα.carrier PUnit = Over.mk (fun _ : PUnit => PUnit.unit)`.
These functions are propositionally equal (PUnit has one
element) but not definitionally — folding through both with
`leaf` / `node` operations yields a clean equivalence without
manipulating the carrier object directly.

## Section 6 — Recovering the existing unlabeled API

```lean
def encodeBT : BT.{0} → ℕ :=
  BT.fold 0 (fun el er => Nat.pair el er + 1)

def decodeBT : ℕ → BT.{0}
  | 0     => BT.leaf
  | n + 1 =>
    BT.node (decodeBT (Nat.unpair n).1)
      (decodeBT (Nat.unpair n).2)
  termination_by n => n
  decreasing_by
    · exact Nat.lt_succ_of_le (Nat.unpair_left_le n)
    · exact Nat.lt_succ_of_le (Nat.unpair_right_le n)

theorem decodeBT_encodeBT (t : BT.{0}) :
    decodeBT (encodeBT t) = t

theorem encodeBT_injective : Function.Injective encodeBT

instance : Encodable BT.{0} where
  encode  := encodeBT
  decode  := fun n => some (decodeBT n)
  encodek := by intro t; simp [decodeBT_encodeBT]
```

Definitions and proofs are textually identical to the existing
ones in `LawvereBTPrimrec.lean:18-127`. The relocation is purely
spatial.

Connecting lemmas to the generic encoding:

```lean
theorem encodeBT_eq_encodeBTn_zero (t : BT.{0}) :
    encodeBT t = encodeBTn 0 ((equivBTnBT 0).symm t)

theorem decodeBT_eq_decodeBTn_zero (k : ℕ) :
    decodeBT k = (equivBTnBT 0) (decodeBTn 0 k)
```

Both are proved by structural induction (on `t` for `encode`,
via `Nat.strongRecOn` on `k` for `decode`), reducing to the
leaf/node simp lemmas plus `Nat.pair_unpair` / `Nat.unpair_pair`.

## Section 7 — Perfect tree, depth, and depth ordering

```lean
def BTα.depth {α : Type u} : BTα α → ℕ :=
  BTα.fold (fun _ => 0) (fun dl dr => 1 + max dl dr)

def fullBTn (n d : ℕ) : BTα.{0} (Fin (n + 1)) :=
  match d with
  | 0     => BTα.leaf ⟨n, Nat.lt_succ_self n⟩
  | d + 1 => BTα.node (fullBTn n d) (fullBTn n d)

def fullBT (d : ℕ) : BT.{0} :=
  match d with
  | 0     => BT.leaf
  | d + 1 => BT.node (fullBT d) (fullBT d)

@[simp] theorem fullBTn_zero (n : ℕ) :
    fullBTn n 0 = BTα.leaf ⟨n, Nat.lt_succ_self n⟩ := rfl

@[simp] theorem fullBTn_succ (n d : ℕ) :
    fullBTn n (d + 1) =
      BTα.node (fullBTn n d) (fullBTn n d) := rfl

-- Analogous fullBT_zero / fullBT_succ.
```

Closed-form recurrences:

```lean
theorem encodeBTn_fullBTn_succ (n d : ℕ) :
    encodeBTn n (fullBTn n (d + 1)) =
      let x := encodeBTn n (fullBTn n d)
      (x + 1) ^ 2 + n

@[simp] theorem encodeBT_fullBT_succ (d : ℕ) :
    encodeBT (fullBT (d + 1)) = (encodeBT (fullBT d) + 1) ^ 2
```

Proof of `encodeBTn_fullBTn_succ`: unfold `fullBTn_succ` and
`encodeBTn_node`, expand `Nat.pair x x = x*x + 2*x` because
`x ≥ n` triggers the `else` branch of `Nat.pair`, then
arithmetic.

Depth-ordering theorem:

```lean
theorem encodeBTn_le_fullBTn_iff_depth_le {n : ℕ}
    (t : BTα.{0} (Fin (n + 1))) (d : ℕ) :
    encodeBTn n t ≤ encodeBTn n (fullBTn n d) ↔
      BTα.depth t ≤ d
```

Proof obligations:

- `BTα.depth (BTα.node l r) ≤ d + 1
    ↔ BTα.depth l ≤ d ∧ BTα.depth r ≤ d` — discharged by
  `Nat.max_le`.
- `Nat.pair` is monotone in both arguments (mathlib check
  first; if absent, prove a one-line lemma in `Utilities/`).
- One arithmetic step linking `(x + 1)^2 + n` to the encoding
  recurrence.

Strict-monotonicity corollary, derived from the biconditional:

```lean
theorem encodeBTn_lt_of_depth_lt {n : ℕ}
    (t₁ t₂ : BTα.{0} (Fin (n + 1)))
    (h : BTα.depth t₁ < BTα.depth t₂) :
    encodeBTn n t₁ < encodeBTn n t₂ := by
  -- Let d := depth t₂.  We have d ≥ 1 and depth t₁ ≤ d - 1.
  -- By the iff: encodeBTn t₁ ≤ encodeBTn (fullBTn (d - 1)).
  -- Suppose for contradiction encodeBTn t₂ ≤ encodeBTn t₁.
  -- Then encodeBTn t₂ ≤ encodeBTn (fullBTn (d - 1)), so by the
  -- iff again, depth t₂ ≤ d - 1, contradicting depth t₂ = d.
  -- Strict-`<` on the encoding follows.
  sorry
```

Specializations to the unlabeled case (via the bridge):

```lean
def BT.depth (t : BT.{0}) : ℕ :=
  BTα.depth (equivBTαPUnitBT.symm t)

theorem encodeBT_le_fullBT_iff_depth_le
    (t : BT.{0}) (d : ℕ) :
    encodeBT t ≤ encodeBT (fullBT d) ↔ BT.depth t ≤ d

theorem encodeBT_lt_of_depth_lt
    (t₁ t₂ : BT.{0}) (h : BT.depth t₁ < BT.depth t₂) :
    encodeBT t₁ < encodeBT t₂
```

## Section 8 — Build sequence

Per `CLAUDE.md`'s "one definition at a time" discipline,
`lake build` (and `lake test` once tests are added) is verified
after each step. Order:

1. Add the five `abbrev`s to `PLang/Syntax.lean`.
2. Create `PLang/BTPair.lean` with `BTα.carrier`, `BTα`,
   `BTα.leaf`, `BTα.node`, `BTα.fold`, the simp lemmas, and
   `BTα.leaf_or_node`.
3. Add `encodeBTn` with its simp lemmas.
4. Add `decodeBTn` with termination proof and simp lemmas.
5. Prove `decodeBTn_encodeBTn`, then `encodeBTn_decodeBTn`;
   define `equivBTnNat`.
6. Define `equivBTnBTm`, `equivBTnBT1`, `BTα.equivOfEquiv`,
   `finOneEquivPUnit` (mathlib check), `equivBTαPUnitBT`,
   `equivBTnBT`.
7. Cut `encodeBT … Encodable BT.{0}` (lines 18-127) from
   `LawvereBTPrimrec.lean`; paste into `BTPair.lean`. Add
   `import GebLean.PLang.BTPair` to `LawvereBTPrimrec.lean`.
   Add the two connecting lemmas.
8. Define `BTα.depth`, `fullBTn`, `fullBT`, and their simp
   lemmas. Prove the closed-form recurrences.
9. Prove `encodeBTn_le_fullBTn_iff_depth_le` (mathlib check
   for `Nat.pair` monotonicity first). Derive
   `encodeBTn_lt_of_depth_lt`. Specialize to the unlabeled
   case.
10. Add `BTPair` to `PLang.lean`'s re-exports.
11. Add tests.

## Tests

```lean
-- Encoding leaves at small alphabets.
#guard encodeBTn 0 (BTα.leaf (0 : Fin 1)) = 0
#guard encodeBTn 1 (BTα.leaf (0 : Fin 2)) = 0
#guard encodeBTn 1 (BTα.leaf (1 : Fin 2)) = 1

-- Encoding a one-level node.
#guard
  encodeBTn 1
    (BTα.node (BTα.leaf (0 : Fin 2)) (BTα.leaf (1 : Fin 2))) =
    2 + Nat.pair 0 1

-- Round-trip on small naturals.
#guard encodeBTn 0 (decodeBTn 0 0) = 0
#guard encodeBTn 0 (decodeBTn 0 5) = 5
#guard encodeBTn 1 (decodeBTn 1 7) = 7

-- Alphabet shift sanity check.
#guard
  encodeBTn 2 ((equivBTnBTm 1 2) (BTα.leaf (1 : Fin 2))) =
    encodeBTn 1 (BTα.leaf (1 : Fin 2))

-- Perfect-tree encoding values, depths 0 through 5.
-- Sequence is OEIS A003095(d + 1) − 1
-- (counts of binary trees of depth ≤ d, minus one).
#guard encodeBT (fullBT 0) = 0
#guard encodeBT (fullBT 1) = 1
#guard encodeBT (fullBT 2) = 4
#guard encodeBT (fullBT 3) = 25
#guard encodeBT (fullBT 4) = 676
#guard encodeBT (fullBT 5) = 458329

-- Labeled perfect-tree values for small (n, d).
#guard encodeBTn 1 (fullBTn 1 0) = 1
#guard encodeBTn 2 (fullBTn 2 0) = 2

-- Depth-ordering smoke check (constructive evidence; the
-- theorem is the proper guarantee).
#guard
  encodeBT (BT.node BT.leaf BT.leaf) <
    encodeBT (BT.node (BT.node BT.leaf BT.leaf) BT.leaf)
```

## File summary

- **Modified**: `GebLean/PLang/Syntax.lean` (five new aliases).
- **New**: `GebLean/PLang/BTPair.lean` (parametric BT, encoding,
  alphabet shift, perfect tree, depth ordering, relocated
  unlabeled API, connecting lemmas).
- **Modified**: `GebLean/LawvereBTPrimrec.lean` (relocated
  block removed; new import added).
- **Modified**: `GebLean/PLang.lean` (re-export `BTPair`).
- **New / modified**: a `test/` file with the `#guard` tests
  above.
