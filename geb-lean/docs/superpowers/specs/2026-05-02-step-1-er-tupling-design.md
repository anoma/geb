# Step 1 — Foundational ER-side tupling infrastructure

Spec for cycle 1 of the ER ↔ K^sim_2 categorical-equivalence
formalization (master design:
`docs/research/2026-05-02-er-ksim2-equiv-via-urm-master-design.md`).
This cycle lands the foundational fixed-length k-tuple Szudzik
pairing infrastructure on the ER side; K^sim-side tupling is
out of scope per the master design's §3.1 note (and is
deferred to step 9 if needed for the URM simulator).

## §1 Status and motivation

### §1.1 Goal

Land the named-composite `Nat`- and `ER`-level definitions
that realize Tourlakis 2018 §0.1.0.34, p. 14's k-tuple coding
scheme `[[z_1, …, z_k]]^{(k)}`, with bijection theorems and
polynomial value bounds. Downstream cycles consume these
through:

- Step 2: `ERMor1.simultaneousBoundedRec` packs intermediate
  state via `Nat.tuplePack` and unpacks via `Nat.tupleAt`,
  using the polynomial bound to certify staying in ER.
- Steps 3 onward: the same bound formula propagates through
  `simultaneousBoundedRec` arithmetic into the `A_n^r`
  majorization (§3.4) and into `kToER` (§3.5).

### §1.2 Scope

In scope:

- `GebLean/Utilities/Tupling.lean`: `Nat.tuplePack`,
  `Nat.tupleAt`, bijection theorems
  (`tupleAt_tuplePack`, `tuplePack_tupleAt`),
  `Nat.tupleAt_le`, `Nat.tuplePackCoef`,
  `Nat.tuplePack_le`.
- `GebLean/Utilities/ERTupling.lean`: `ERMor1.tuplePack`,
  `ERMor1.tupleAt`, `@[simp]` interp lemmas, `PolyBound`
  builders `ofTuplePack` and `ofTupleAt`, ERMorN-quotient
  round-trip lemmas.
- `LawvereERCat.tupleIso (k : ℕ) : (k + 1) ≅ 1` — best-
  effort, gated on the §5 checklist; if the gate fails the
  spec's §8 "open follow-ups" records the diagnosis.
- Smoke tests + boundary `example` lemmas covering encoding
  orientation, identity case, round-trip on small concrete
  tuples, and the `tuplePackCoef` recurrence.

Out of scope:

- K^sim-side tupling (per master design §3.1).
- `simultaneousBoundedRec` (step 2).
- `A_n^r` named composites (step 3).
- Any majorization or bound-arithmetic theorems beyond
  `Nat.tuplePack_le` and `Nat.tupleAt_le`.
- Refactoring of the existing variable-length
  `Nat.seqPack` / `Nat.seqAt` in `SzudzikSeq.lean`.

### §1.3 Indexing convention

Throughout this spec the parameter `k : ℕ` of `tuplePack`
and `tupleAt` indexes a tuple of length `k + 1`. The
bijection `(Fin (k+1) → ℕ) ↔ ℕ` is meaningful only for
non-empty products; using `Fin (k+1)` rather than `Fin k`
with a `k ≥ 1` side condition makes the empty tuple
unrepresentable.

This matches the post-correction master design §3.1 (commit
`9c806cb8`).

### §1.4 Orientation convention

`Nat.tuplePack` follows Tourlakis 2018 §0.1.0.34, p. 14's
*left-fold* recurrence:

```text
[[z_1]]^{(1)}        = z_1
[[z_1, …, z_k]]^{(k)} = J([[z_1, …, z_{k-1}]]^{(k-1)}, z_k)
                       (for k ≥ 2)
```

That is, the prefix-pack is paired with the new last element.
Our right-associated alternative (used in the existing
`Nat.seqPack` in `SzudzikSeq.lean`) pairs the head with the
packed tail; for the same reason we choose the Tourlakis
orientation here, `Nat.seqPack` retains its own orientation
in its own module. Each function's orientation matches the
literature target it transcribes; the local convention is
per-function, not codebase-wide.

The bound formula `tuplePack k v ≤ tuplePackCoef k *
(M+1)^{2^k}` is identical in either orientation.

## §2 Architecture and module layout

Two new modules under `GebLean/Utilities/`, in dependency
order:

### §2.1 `GebLean/Utilities/Tupling.lean` (`Nat`-level)

Imports: `Mathlib.Data.Nat.Pairing` and
`Mathlib.Data.Fin.Tuple.Basic` (the latter for `Fin.init`,
`Fin.lastCases`, and the reduction lemmas
`Fin.lastCases_last` / `Fin.lastCases_castSucc`). Standalone
otherwise — does not import `SzudzikSeq.lean`,
`ComputationalComplexity.lean`, or any ER-related module.

Namespace: `Nat`.

Public surface:

- `Nat.tuplePack : (k : ℕ) → (Fin (k+1) → ℕ) → ℕ`
- `Nat.tupleAt : (k : ℕ) → ℕ → Fin (k+1) → ℕ`
- `Nat.tuplePackCoef : ℕ → ℕ`
- `@[simp] Nat.tuplePack_zero`, `Nat.tuplePack_succ`,
  `Nat.tupleAt_zero`, `Nat.tupleAt_succ_last`,
  `Nat.tupleAt_succ_castSucc`
- `Nat.tupleAt_tuplePack`, `Nat.tuplePack_tupleAt`
- `Nat.tupleAt_le`, `Nat.tuplePack_le`

### §2.2 `GebLean/Utilities/ERTupling.lean` (ER-level)

Imports: `GebLean.Utilities.Tupling`, `GebLean.Utilities.ERArith`,
`GebLean.LawvereERPolynomialBound`. Namespace: `GebLean`,
sub-namespaces `ERMor1` and `ERMor1.PolyBound`.

Public surface:

- `ERMor1.tuplePack : (k : ℕ) → ERMor1 (k + 1)`
- `ERMor1.tupleAt : (k : ℕ) → Fin (k + 1) → ERMor1 1`
- `@[simp] ERMor1.interp_tuplePack`,
  `@[simp] ERMor1.interp_tupleAt`
- `ERMor1.PolyBound.ofTuplePack`,
  `ERMor1.PolyBound.ofTupleAt`
- Two named-helper composites bridging single-output to
  multi-output: `ERMorN.lift : ERMor1 n → ERMorN n 1` (the
  one-element vector view) and
  `ERMorN.ofVec : (Fin m → ERMor1 n) → ERMorN n m` (a
  named identity coercion, since
  `ERMorN n m := Fin m → ERMor1 n`). These exist solely so
  the §4.4 round-trip lemma signatures and the §5.3 iso
  construction cite a stable interface; they are otherwise
  trivial.
- `ERMorN.tupleAt_tuplePack`, `ERMorN.tuplePack_tupleAt`
  (round-trip at the ERMorN-quotient level)
- `LawvereERCat.tupleIso (k : ℕ) : (k + 1) ≅ 1` — gated
  per §5

Both modules added to `GebLean.lean`'s public surface.

### §2.3 Test files

- `GebLeanTests/Tupling.lean`
- `GebLeanTests/ERTupling.lean`

Both registered in `GebLeanTests.lean`.

### §2.4 Dependency graph for downstream Path-2 modules

```text
Tupling.lean                              [step 1, this cycle]
   ↓
ERTupling.lean                            [step 1, this cycle]
   ↓
ERSimultaneousBoundedRec.lean             [step 2]
   ↓
ERAMajorants.lean                         [step 3]
   ↓
LawvereKSimMajorization.lean              [step 4]
   ↓
LawvereKSimER.lean                        [step 5]
```

## §3 `Nat`-level entities (`Tupling.lean`)

### §3.1 Definitions

```lean
namespace Nat

/-- Pack a `(k+1)`-tuple of naturals into a single natural via
iterated left-associated Szudzik pairing.  Realizes Tourlakis
2018 §0.1.0.34, p. 14's `[[z_1, …, z_{k+1}]]^{(k+1)}` (with
Szudzik replacing Cantor's J).  Master design §3.1.  -/
def tuplePack : (k : ℕ) → (Fin (k+1) → ℕ) → ℕ
  | 0,     v => v 0
  | k + 1, v =>
      Nat.pair (tuplePack k (Fin.init v))
        (v (Fin.last (k+1)))

/-- Extract the `i`-th component from a packed `(k+1)`-tuple.
Inverse of `tuplePack`.  Realizes Tourlakis 2018 §0.1.0.34,
p. 14's `Π^{k+1}_i` projections (with index orientation
matched to the left-fold recurrence).  Master design §3.1.  -/
def tupleAt : (k : ℕ) → ℕ → Fin (k+1) → ℕ
  | 0,     n, _ => n
  | k + 1, n, i =>
      Fin.lastCases (motive := fun _ : Fin (k+2) => ℕ)
        ((Nat.unpair n).2)
        (fun j : Fin (k+1) => tupleAt k (Nat.unpair n).1 j)
        i

/-- Closed-form coefficient witnessing the polynomial bound
`tuplePack k v ≤ tuplePackCoef k * (M+1)^(2^k)`.  Recurrence
derived from `Nat.pair_le_sq` per master design §3.1.  -/
def tuplePackCoef : ℕ → ℕ
  | 0     => 1
  | k + 1 => (tuplePackCoef k + 2)^2

end Nat
```

### §3.2 `@[simp]` interp lemmas

```lean
@[simp] theorem Nat.tuplePack_zero (v : Fin 1 → ℕ) :
    Nat.tuplePack 0 v = v 0 := rfl

@[simp] theorem Nat.tuplePack_succ (k : ℕ)
    (v : Fin (k+2) → ℕ) :
    Nat.tuplePack (k+1) v
      = Nat.pair (Nat.tuplePack k (Fin.init v))
          (v (Fin.last (k+1))) := rfl

@[simp] theorem Nat.tupleAt_zero (n : ℕ) (i : Fin 1) :
    Nat.tupleAt 0 n i = n := rfl

/-- `tupleAt` reduction at the last index: peels one
`Nat.unpair` step on the right. -/
@[simp] theorem Nat.tupleAt_succ_last (k n : ℕ) :
    Nat.tupleAt (k+1) n (Fin.last (k+1))
      = (Nat.unpair n).2 := by
  simp [Nat.tupleAt, Fin.lastCases_last]

/-- `tupleAt` reduction at a non-last index: peels one
`Nat.unpair` step on the left and recurses at depth `k`. -/
@[simp] theorem Nat.tupleAt_succ_castSucc (k n : ℕ)
    (j : Fin (k+1)) :
    Nat.tupleAt (k+1) n j.castSucc
      = Nat.tupleAt k (Nat.unpair n).1 j := by
  simp [Nat.tupleAt, Fin.lastCases_castSucc]
```

These two lemmas reduce the bijection-theorem proofs in §3.3
to a clean `induction k; · rfl; · simp [Nat.unpair_pair, ...]`
shape rather than manual `Fin.lastCases` invocations.

### §3.3 Bijection theorems

```lean
/-- Round-trip: extracting component `i` from a pack returns
the original component.  Realizes Tourlakis 2018 §0.1.0.34,
p. 14's `Π^k_i [[z_1,…,z_k]]^{(k)} = z_i`.  -/
theorem Nat.tupleAt_tuplePack (k : ℕ) (v : Fin (k+1) → ℕ)
    (i : Fin (k+1)) :
    Nat.tupleAt k (Nat.tuplePack k v) i = v i

/-- Round-trip: packing the components extracted from a
packed natural returns the original natural.  -/
theorem Nat.tuplePack_tupleAt (k n : ℕ) :
    Nat.tuplePack k (Nat.tupleAt k n) = n
```

Proof outline (both): induction on `k`. Base case is by
`rfl` (1-tuple identity). Recursive case unfolds `tuplePack
(k+1)`, applies `Nat.unpair_pair` to peel one Szudzik step,
and applies the IH on the prefix. The `Fin.lastCases` step in
`tupleAt` reduces to `Fin.lastCases_last` (for `i =
Fin.last`) or `Fin.lastCases_castSucc` (for `i =
j.castSucc`).

### §3.4 Polynomial bounds

```lean
/-- Every component extracted from a packed natural is
bounded by the packed natural itself.  Mirrors the existing
`Nat.seqAt_le` for variable-length packs (`SzudzikSeq.lean`),
applied via `Nat.unpair_left_le` / `Nat.unpair_right_le`.  -/
theorem Nat.tupleAt_le (k n : ℕ) (i : Fin (k+1)) :
    Nat.tupleAt k n i ≤ n

/-- Polynomial value bound on `tuplePack`.  At parameter `k`
(packing `(k+1)`-tuples), `tuplePack k v` is bounded by
`tuplePackCoef k * (M + 1)^(2^k)` where `M = sup v` over
`Fin (k+1)`.  Cites Tourlakis 2018 §0.1.0.34, p. 14 (proof
that pairing stays in `E^2`); master design §3.1.  -/
theorem Nat.tuplePack_le (k : ℕ) (v : Fin (k+1) → ℕ) :
    Nat.tuplePack k v
      ≤ Nat.tuplePackCoef k *
          ((Finset.univ : Finset (Fin (k+1))).sup v + 1)^(2^k)
```

Proof outline:

- `tupleAt_le` by induction on `k`, peeling `unpair` steps;
  uses `Nat.unpair_left_le` and `Nat.unpair_right_le`.
- `tuplePack_le` by induction on `k`. Let
  `M = (Finset.univ : Finset (Fin (k+1))).sup v`.
  - Base (`k = 0`): `tuplePack 0 v = v 0 ≤ M ≤ M + 1
    = 1 * (M + 1)^1 = tuplePackCoef 0 * (M+1)^{2^0}`.
  - Step (`k → k+1`): let
    `M' = (Finset.univ : Finset (Fin (k+2))).sup v`. By
    `Nat.pair_le_sq`,

    ```text
    tuplePack (k+1) v
      ≤ (tuplePack k (Fin.init v) + v (Fin.last (k+1)) + 1)^2
    ```

    For the IH on `Fin.init v` we need
    `(Finset.univ : Finset (Fin (k+1))).sup (Fin.init v) ≤ M'`.
    Since `Fin.init v i = v i.castSucc`, this reduces to
    `Finset.sup_le` followed by
    `Finset.le_sup (Finset.mem_univ i.castSucc) :
       v i.castSucc ≤ M'`. The IH then gives

    ```text
    tuplePack k (Fin.init v)
      ≤ tuplePackCoef k * (M' + 1)^{2^k}
    ```

    by monotonicity of `(_ + 1)^{2^k}`.
    Combined with `v (Fin.last (k+1)) ≤ M'`, we obtain

    ```text
    tuplePack k (Fin.init v) + v (Fin.last (k+1)) + 1
      ≤ tuplePackCoef k * (M' + 1)^{2^k} + (M' + 1)
      ≤ (tuplePackCoef k + 1) * (M' + 1)^{2^k}
      ≤ (tuplePackCoef k + 2) * (M' + 1)^{2^k}
    ```

    using `(M' + 1) ≤ (M' + 1)^{2^k}` (since `2^k ≥ 1`,
    base case `k = 0` gives `(M' + 1)^1 = M' + 1`).
    Squaring both sides:

    ```text
    tuplePack (k+1) v
      ≤ (tuplePackCoef k + 2)^2 * (M' + 1)^{2 * 2^k}
      = tuplePackCoef (k+1) * (M' + 1)^{2^{k+1}}
    ```

The arithmetic shares structure with `seqPack_le_pow_aux` in
`ComputationalComplexity.lean` but is proven fresh in this
cycle to honor the per-function literature alignment;
opportunistic refactoring is deferred to a follow-up cycle.

## §4 ER-level entities (`ERTupling.lean`)

### §4.1 Named composites

```lean
namespace GebLean
namespace ERMor1

/-- ER named composite for fixed-length `(k+1)`-tuple Szudzik
pack.  Built bottom-up from `proj`, `natPair`, `comp` per
CLAUDE.md "bottom-up named-composite discipline".  Mirrors
`Nat.tuplePack`'s left-fold recurrence (master design §3.1;
Tourlakis 2018 §0.1.0.34, p. 14).  -/
def tuplePack : (k : ℕ) → ERMor1 (k + 1)
  | 0     => ERMor1.proj 0
  | k + 1 =>
      ERMor1.comp ERMor1.natPair
        ![ ERMor1.comp (tuplePack k)
             (fun i : Fin (k + 1) => ERMor1.proj i.castSucc)
         , ERMor1.proj (Fin.last (k + 1)) ]

/-- ER named composite extracting component `i` from a packed
`(k+1)`-tuple.  Built bottom-up from `proj`, `natUnpairFst`,
`natUnpairSnd`, `comp`.  Mirrors `Nat.tupleAt`'s left-fold
recurrence.  -/
def tupleAt : (k : ℕ) → Fin (k + 1) → ERMor1 1
  | 0,     _ => ERMor1.proj 0
  | k + 1, i =>
      Fin.lastCases (motive := fun _ : Fin (k+2) => ERMor1 1)
        ERMor1.natUnpairSnd
        (fun j : Fin (k+1) =>
          ERMor1.comp (tupleAt k j) ![ERMor1.natUnpairFst])
        i

end ERMor1
end GebLean
```

### §4.2 `@[simp]` interp lemmas

```lean
@[simp] theorem ERMor1.interp_tuplePack (k : ℕ)
    (v : Fin (k+1) → ℕ) :
    (ERMor1.tuplePack k).interp v = Nat.tuplePack k v

@[simp] theorem ERMor1.interp_tupleAt (k : ℕ)
    (i : Fin (k+1)) (n : ℕ) :
    (ERMor1.tupleAt k i).interp ![n] = Nat.tupleAt k n i
```

Proof outline: induction on `k`. Base case is `rfl` (or
one-line `simp`). Recursive case unfolds the ER definition,
applies the existing interp lemmas
`ERMor1.interp_natPair`, `ERMor1.interp_natUnpairFst`,
`ERMor1.interp_natUnpairSnd`, `ERMor1.interp_proj`,
`ERMor1.interp_comp`, plus the IH; matches the recursive
definition of `Nat.tuplePack` / `Nat.tupleAt`.

### §4.3 PolyBound builders

```lean
namespace ERMor1.PolyBound

/-- PolyBound builder for `tuplePack k`.  Cites master design
§3.1: `tuplePack k v ≤ tuplePackCoef k * (M+1)^(2^k)`.  -/
def ofTuplePack (k : ℕ) :
    PolyBound (ERMor1.tuplePack k) where
  degree      := 2^k
  coefficient := Nat.tuplePackCoef k
  constant    := 0
  bounds      := fun ctx => by
    rw [ERMor1.interp_tuplePack]
    simpa using Nat.tuplePack_le k ctx

/-- PolyBound builder for `tupleAt k i`.  Linear bound from
`Nat.tupleAt_le` (single-arity context). -/
def ofTupleAt (k : ℕ) (i : Fin (k+1)) :
    PolyBound (ERMor1.tupleAt k i) where
  degree      := 1
  coefficient := 1
  constant    := 0
  bounds      := fun ctx => by
    rw [ERMor1.interp_tupleAt]
    simpa using Nat.tupleAt_le k (ctx 0) i

end ERMor1.PolyBound
```

### §4.4 ERMorN-quotient round-trip lemmas

#### §4.4.1 Bridging helpers `ERMorN.lift` and `ERMorN.ofVec`

```lean
/-- One-element vector view of a single-output ER term.
`ERMorN.lift f i = f` for the unique `i : Fin 1`. Auxiliary
helper supporting the `ERMorN`-quotient round-trip lemmas
named in master design §3.1; bridges single-output
`ERMor1.tuplePack` to the multi-output `ERMorN` interface
on which the round-trip equation is stated. -/
def ERMorN.lift {n : ℕ} (f : ERMor1 n) : ERMorN n 1 :=
  fun _ => f

/-- Named identity coercion from a vector of single-output
ER terms to the multi-output `ERMorN`. Definitionally `g`,
since `ERMorN n m := Fin m → ERMor1 n`. Auxiliary helper
supporting the round-trip lemmas named in master design
§3.1; gives the `Fin (k+1) → ERMor1 1` family of `tupleAt`
projections a stable `ERMorN 1 (k+1)` interface for the
quotient-level lemma signatures. -/
def ERMorN.ofVec {n m : ℕ} (g : Fin m → ERMor1 n) :
    ERMorN n m := g
```

#### §4.4.2 Round-trip lemmas

The composition convention is per `LawvereER.lean:167-170`:
`ERMorN.comp (f : ERMorN n m) (g : ERMorN m k) : ERMorN n k`
runs `f` first, then `g`. So "first pack, then unpack"
applies `lift (tuplePack k) : ERMorN (k+1) 1` first, then
`ofVec (fun i => tupleAt k i) : ERMorN 1 (k+1)`, yielding an
`ERMorN (k+1) (k+1)` candidate for `id (k+1)`. The other
direction reverses.

The relation is the explicit setoid relation
`(erMorNSetoid n m).r` from `LawvereERQuot.lean:23-32`,
written out longhand because `erMorNSetoid` is declared as a
`def` (not an `instance`) and the rest of the codebase
follows the same explicit-setoid convention (see
`LawvereERQuot.lean:75, 90, 134` for representative call
sites). This avoids `≈`/`Setoid` instance-resolution friction.

```lean
/-- Round-trip at the ERMorN-quotient level: first packing,
then component-wise unpacking, is extensionally equal to the
identity at arity `(k+1)`.  Restates
`Nat.tupleAt_tuplePack` at the morphism-quotient level. -/
theorem ERMorN.tupleAt_tuplePack (k : ℕ) :
    (erMorNSetoid (k+1) (k+1)).r
      (ERMorN.comp
        (ERMorN.lift (ERMor1.tuplePack k))
        (ERMorN.ofVec
           (fun i : Fin (k+1) => ERMor1.tupleAt k i)))
      (ERMorN.id (k+1))

/-- Round-trip in the other direction: first component-wise
unpacking, then packing, is extensionally equal to the
identity at arity `1`.  Restates `Nat.tuplePack_tupleAt`. -/
theorem ERMorN.tuplePack_tupleAt (k : ℕ) :
    (erMorNSetoid 1 1).r
      (ERMorN.comp
        (ERMorN.ofVec
           (fun i : Fin (k+1) => ERMor1.tupleAt k i))
        (ERMorN.lift (ERMor1.tuplePack k)))
      (ERMorN.id 1)
```

Both lemma proofs unfold `(erMorNSetoid · ·).r` to its
defining relation `∀ ctx, f.interp ctx = g.interp ctx`
(per `LawvereERQuot.lean:23-29`); then unfold `ERMorN.comp`,
`ERMorN.id`, `ERMorN.lift`, `ERMorN.ofVec` to functions of
indices, unfold `ERMor1.comp.interp` via the existing
`@[simp] ERMor1.interp_comp`, and reduce to the Nat-level
bijection theorems via the §4.2 interp simp lemmas. The two
helper-interp reductions

```lean
@[simp] theorem ERMorN.lift_apply {n : ℕ} (f : ERMor1 n)
    (i : Fin 1) :
    ERMorN.lift f i = f := rfl

@[simp] theorem ERMorN.ofVec_apply {n m : ℕ}
    (g : Fin m → ERMor1 n) (i : Fin m) :
    ERMorN.ofVec g i = g i := rfl
```

are added to §4.4.1's helper definitions so the proof's
unfolding is mechanical.

## §5 Categorical iso `(k + 1) ≅ 1` (gated, best-effort)

### §5.1 Goal

Witness that the `(k+1)`-fold product of the generator
collapses to the generator in `LawvereERCat`, packaged as a
categorical iso whose `hom` is `[ERMor1.tuplePack k]` and
whose `inv` is the tuple-of-`ERMor1.tupleAt`s. The iso laws
reduce to the §4.4 round-trip lemmas via `Quot.sound`.

### §5.2 Gate checklist

The iso lands in this cycle iff *all three* of the following
hold. The implementer reads `LawvereERCat.lean` first and
mechanically ticks each box:

- [ ] **G1: Object indexing.** The objects of `LawvereERCat`
      accept `(k + 1 : LawvereERCat)` and `(1 : LawvereERCat)`
      directly; the natural-number indexing of objects is
      already the generator-power encoding (no coercion or
      lifting needed).
- [ ] **G2: Hom-set shapes.** The morphism types
      `(k + 1 : LawvereERCat) ⟶ 1` and
      `(1 : LawvereERCat) ⟶ (k + 1)` are quotients of
      `ERMorN (k+1) 1` and `ERMorN 1 (k+1)` respectively
      (per `LawvereERQuot.lean`'s `ERMorNQuo` shape).
      Wrapping a single-output `ERMor1.tuplePack k` to
      `ERMorN (k+1) 1` requires `ERMorN.lift`; wrapping a
      family `Fin (k+1) → ERMor1 1` to `ERMorN 1 (k+1)`
      uses `ERMorN.ofVec` (definitionally identity). The
      §4.4.1 helpers exist precisely to make this wrapping
      a stable named operation.
- [ ] **G3: Iso laws via Quotient.sound.** `hom_inv_id` and
      `inv_hom_id` reduce to
      `Quotient.sound (s := erMorNSetoid · ·)` applied to
      §4.4's round-trip lemmas plus standard category-theory
      boilerplate (`Category.id_comp`, `Category.comp_id`,
      `Functor.map_comp`, etc.); no new infrastructure is
      required beyond the §4.4.1 helpers. The codebase's
      existing convention is the explicit-setoid form
      `Quotient.sound (s := erMorNSetoid n m) ...`
      (see `LawvereERQuot.lean:60, 75, 90, 134`).

### §5.3 Construction (gate-passing form)

```lean
namespace LawvereERCat

/-- Decorative iso: in `LawvereERCat`, the `(k+1)`-fold
product of the generator is isomorphic to the generator,
witnessed by `ERMor1.tuplePack` and the tuple of
`ERMor1.tupleAt`s.  Master design §3.1.  -/
def tupleIso (k : ℕ) : (k + 1 : LawvereERCat) ≅ 1 where
  hom        := Quotient.mk (erMorNSetoid (k+1) 1)
                  (ERMorN.lift (ERMor1.tuplePack k))
  inv        := Quotient.mk (erMorNSetoid 1 (k+1))
                  (ERMorN.ofVec
                    (fun i : Fin (k+1) => ERMor1.tupleAt k i))
  hom_inv_id := by
    exact Quotient.sound
      (s := erMorNSetoid (k+1) (k+1))
      (ERMorN.tupleAt_tuplePack k)
  inv_hom_id := by
    exact Quotient.sound
      (s := erMorNSetoid 1 1)
      (ERMorN.tuplePack_tupleAt k)

end LawvereERCat
```

### §5.4 Gate-failure procedure

If any of G1–G3 fails, do *not* absorb the obstruction into
this cycle. Instead, write the diagnosis in §8.3 below
("open follow-ups: categorical iso deferral") with:

1. Which of G1, G2, G3 fails.
2. A 1–2 sentence reading of where in
   `LawvereERCat.lean` the obstruction lies, with a line
   reference.
3. A proposed Step 1.5 cycle scope summarizing what
   infrastructure would need to land before the iso is
   reachable.

The deferral is itself a diagnostic signal that
`LawvereERCat`'s setup may need reconsideration; surfacing
the obstruction is the point.

## §6 Tests

### §6.1 Smoke `#guard`s

In `TuplingTests.lean` and `ERTuplingTests.lean`. Locked-in
encoding direction, identity case, and small-tuple
round-trips:

```lean
-- Head/tail orientation locks: the prefix-pack is on the
-- LEFT of `pair`; the new last element is on the RIGHT.
#guard Nat.tuplePack 1 ![3, 5] = Nat.pair 3 5
#guard Nat.tupleAt 1 (Nat.pair 3 5) 0 = 3
#guard Nat.tupleAt 1 (Nat.pair 3 5) 1 = 5

-- Identity case (k = 0).
#guard Nat.tuplePack 0 ![7] = 7
#guard Nat.tupleAt 0 17 0 = 17

-- Round-trip on a small concrete 3-tuple.
#guard Nat.tupleAt 2 (Nat.tuplePack 2 ![3, 5, 7]) 0 = 3
#guard Nat.tupleAt 2 (Nat.tuplePack 2 ![3, 5, 7]) 1 = 5
#guard Nat.tupleAt 2 (Nat.tuplePack 2 ![3, 5, 7]) 2 = 7

-- ER side mirrors Nat side.
#guard (ERMor1.tuplePack 1).interp ![3, 5] = Nat.pair 3 5
#guard (ERMor1.tupleAt 2 1).interp
         ![Nat.tuplePack 2 ![3, 5, 7]] = 5
```

### §6.2 Boundary `example` lemmas

Make the recurrence visible to readers:

```lean
/-- At `k = 0` the bound is the identity linear bound
(degree 1, coefficient 1, constant 0). -/
example (v : Fin 1 → ℕ) : Nat.tuplePack 0 v ≤ v 0 := by
  simp [Nat.tuplePack]

/-- `tuplePackCoef 0 = 1`, witnessing the recurrence base. -/
example : Nat.tuplePackCoef 0 = 1 := rfl

/-- `tuplePackCoef 1 = 9`, since `(1 + 2)^2 = 9`.  Locks
the recurrence's first step. -/
example : Nat.tuplePackCoef 1 = 9 := rfl

/-- `tuplePackCoef 2 = 121`, since `(9 + 2)^2 = 121`.  Locks
the second step (degree 4 with coefficient 121). -/
example : Nat.tuplePackCoef 2 = 121 := rfl

/-- Bound at the `M = 0` corner case: at `k = 1`,
`tuplePack 1 ![0, 0] = pair 0 0 = 0 ≤ 9 * 1 = 9`. -/
example :
    Nat.tuplePack 1 ![0, 0]
      ≤ Nat.tuplePackCoef 1 * 1^(2^1) := by
  decide

/-- Bound at a small concrete input. -/
example :
    Nat.tuplePack 1 ![3, 5]
      ≤ Nat.tuplePackCoef 1 * (5 + 1)^(2^1) := by
  decide

/-- ER-side PolyBound smoke: `ofTuplePack 1` produces the
expected (degree, coefficient, constant). -/
example : (ERMor1.PolyBound.ofTuplePack 1).degree = 2 := rfl
example : (ERMor1.PolyBound.ofTuplePack 1).coefficient = 9 := rfl
example : (ERMor1.PolyBound.ofTuplePack 1).constant = 0 := rfl
```

### §6.3 Test scope

No Plausible (the bijection theorems and bound theorem are
universal — randomization adds no coverage). No large-`k`
stress tests (`tuplePackCoef k` grows fast; `decide`-tactic
timing degrades for `k ≥ 3`. Smoke and boundary tests are
restricted to `k ≤ 2`).

## §7 Citations

Per CLAUDE.md "Literature-citation discipline (transcription
workstreams only)". Each entity carries the citation in its
docstring.

### §7.1 `Nat`-side entities

- **`Nat.tuplePack`** — Tourlakis 2018 §0.1.0.34, p. 14:
  defines `[[z_1,…,z_k]]^{(k)}` recursively as
  `J([[z_1,…,z_{k-1}]]^{(k-1)}, z_k)` for `k ≥ 2`. Our
  realization uses Szudzik (mathlib `Nat.pair`) instead of
  Cantor's `J = (x+y)² + x`; both are bijections
  `ℕ × ℕ → ℕ` polynomially bounded by `(x+y+1)²`. Master
  design §3.1.
- **`Nat.tupleAt`** — Tourlakis 2018 §0.1.0.34, p. 14:
  defines `Π^k_i` projections as `LK^{k-i}` (for
  `2 ≤ i ≤ k`) and `K^{k-1}` (for `i = 1`). Our realization
  mirrors the structure with `K`/`L` replaced by
  `Nat.unpair.fst`/`Nat.unpair.snd`. Master design §3.1.
- **`Nat.tupleAt_tuplePack`, `Nat.tuplePack_tupleAt`** —
  Implicit in Tourlakis 2018 §0.1.0.34, p. 14's
  `Π^k_i [[z_1,…,z_k]]^{(k)} = z_i`. Underlying single-step
  bijection: mathlib `Nat.unpair_pair`, `Nat.pair_unpair`.
- **`Nat.tuplePackCoef`, `Nat.tuplePack_le`** — Master
  design §3.1 (corrected formulation per commit `9c806cb8`).
  Underlying quadratic bound: `Nat.pair_le_sq` in
  `ComputationalComplexity.lean` (cites Tourlakis 2018
  §0.1.0.34 + Damnjanovic Lemma 6.1 (2)).
- **`Nat.tupleAt_le`** — Mirrors existing `Nat.seqAt_le` in
  `SzudzikSeq.lean`. Underlying lemmas: mathlib
  `Nat.unpair_left_le`, `Nat.unpair_right_le`.

### §7.2 ER-side entities

- **`ERMor1.tuplePack`, `ERMor1.tupleAt`** — Master design
  §3.1 (Lean entities, ER layer). Built from atomic
  `ERMor1` generators per CLAUDE.md "bottom-up
  named-composite discipline".
- **`ERMor1.interp_tuplePack`, `ERMor1.interp_tupleAt`** —
  Master design §3.1. Standard interp-composition
  unfolding.
- **`ERMor1.PolyBound.ofTuplePack`, `.ofTupleAt`** — Master
  design §3.1 (PolyBound builders) and §15.12 (punch-list
  claim verifier). Built from `Nat.tuplePack_le` and
  `Nat.tupleAt_le`.
- **`ERMorN.tupleAt_tuplePack`,
  `ERMorN.tuplePack_tupleAt`** — Master design §3.1
  (round-trip at quotient level).
- **`LawvereERCat.tupleIso`** — Master design §3.1
  (categorical packaging). Gated; gate-failure diagnosis
  lives in §8.3.

### §7.3 Cross-reference network

- `docs/research/2026-05-02-er-ksim2-equiv-via-urm-master-design.md`
  — §3.1 (Lean entities), §3.2 (consumer of
  `Nat.tuplePack_le`), §3.7 (module file layout), §15.12
  (punch-list claim verifier).
- `docs/research/2026-04-30-ksim-polynomial-bound-references.md`
  — variable-length context for the related `Nat.seqPack`
  / `seqPackBound` infrastructure.
- Master-design correction commit `9c806cb8` — formula
  correction `(M + c_k)^{2^k}` →
  `tuplePackCoef k * (M+1)^{2^k}` and `Fin (k+1)` indexing
  convention.

## §8 Open follow-ups and risks

### §8.1 Lean ergonomic risks

Each item lists the predicted friction and a documented
fallback so the implementer does not have to redesign:

1. **`Fin.lastCases` ergonomics.** Mathlib coverage is less
   extensive than `Fin.cases`. If a proof step that should
   close by `simp [Fin.lastCases_castSucc, Fin.lastCases_last]`
   resists, fallback is explicit
   `if h : i = Fin.last _ then … else …` decomposition with
   `Fin.castSucc_injective` for the negative case.
2. **`Fin.init` interaction with `Finset.sup`.** The bound
   proof step
   `(Finset.univ : Finset (Fin (k+1))).sup (Fin.init v)
     ≤ (Finset.univ : Finset (Fin (k+2))).sup v`
   may not be a one-liner. Fallback: apply `Finset.sup_le`,
   intro `i`, transitivity through
   `v i.castSucc ≤ Finset.sup … v` via
   `Finset.le_sup (Finset.mem_univ _)`.
3. **ER-side arity-shift typing.** Composing
   `tuplePack k : ERMor1 (k+1)` against a family
   `Fin (k+1) → ERMor1 (k+2)` may require explicit type
   annotations on `proj i.castSucc` and
   `proj (Fin.last (k+1))`. Fallback: write
   `(ERMor1.proj i.castSucc : ERMor1 (k+2))` etc. inline.
4. **`tuplePackCoef k` growth.** `tuplePackCoef 0 = 1`,
   `tuplePackCoef 1 = 9`, `tuplePackCoef 2 = 121`,
   `tuplePackCoef 3 = 15129`, `tuplePackCoef 4 ≈ 2.3·10⁸`.
   `decide`-based smoke tests are restricted to `k ≤ 2`
   accordingly; bound theorems use these as parameters and
   are not slowed by their size.
5. **`ERMorN.lift` / `ERMorN.ofVec` implicit-argument
   resolution.** `ERMorN.lift {n : ℕ} (f : ERMor1 n) :
   ERMorN n 1` may need explicit `(n := k+1)` when applied
   to `ERMor1.tuplePack k` if Lean's elaborator can pin
   `n` from the body but not from the call-site context.
   Similarly for `ERMorN.ofVec`'s `m` argument when applied
   to `fun i : Fin (k+1) => ERMor1.tupleAt k i`. Fallback:
   write `ERMorN.lift (n := k+1) (ERMor1.tuplePack k)` and
   `ERMorN.ofVec (m := k+1) (...)` explicitly.

### §8.2 Master-design forward constraints

The §3.1 master-design correction (commit `9c806cb8`)
replaced the additive `(M + c_k)^{2^k}` shape with the
multiplicative `tuplePackCoef k * (M+1)^{2^k}` shape. Step 2's
`simultaneousBoundedRec` cycle and step 4's majorization
cycle must consume the multiplicative form; no path
recreates the additive form. This spec records the
constraint as a forward-looking obligation.

The `tuplePackCoef k` constants grow doubly-exponentially:
`tuplePackCoef 4 ≈ 2.3·10⁸`, `tuplePackCoef 5 ≈ 5.2·10¹⁶`.
Step 2's `simultaneousBoundedRec_polyBound` proof will
instantiate `tuplePackCoef k` at the K^sim-simrec's
child-count `k` (in the `(k+1)`-tuple convention; child
count `k+1`); for typical K^sim_2 simrec witnesses (e.g.
`addK` at `k = 1`, giving `tuplePackCoef 1 = 9`) the literal
is small, but level-2 simrec witnesses with 4+ children will
produce 9-digit coefficient literals. This is not a soundness
concern (the bound holds for any `k`), but step 2's
documentation should surface the literal value to readers
via a doc-comment near the polyBound builder so that error
messages are interpretable.

### §8.4 K^sim-side tupling explicitly out of scope

Per master design §3.1's "K^sim layer (NOT BUILT under Path 2)"
note, this cycle deliberately omits `KMor1.tuplePack` /
`KMor1.tupleAt`. Path 2's `kToER` translation routes through
`ERMor1.simultaneousBoundedRec`, which only consumes ER-side
tupling. K^sim-side tupling at level ≤ 2, if needed by the
erToK URM simulator (step 9), requires a non-naive
construction beyond this cycle's scope.

### §8.5 Orientation match with `Nat.seqPack`

`Nat.seqPack` (in `Utilities/SzudzikSeq.lean`) is right-fold
(`pair head (rec tail) + 1`); `Nat.tuplePack` (this cycle) is
left-fold (`pair (rec init) last`). The orientations are
deliberately per-function — each matches its own literature
target. A subsequent cycle may unify both via a
generalization from which both emerge as special cases;
until that generalization is identified, the per-function
orientation stands.

## §9 Implementation order and bottom-up named-composite discipline

The implementer follows this order (mirroring CLAUDE.md's
"bottom-up named-composite discipline" — every
named-composite construct is defined before its consumer):

1. `GebLean/Utilities/Tupling.lean`:
   1. `Nat.tuplePack`, `Nat.tupleAt`, `Nat.tuplePackCoef`.
   2. **Mathlib name verification.** Before writing the
      `@[simp]` recursive-case lemmas, verify the exact
      mathlib names by `#check @Fin.lastCases_last` and
      `#check @Fin.lastCases_castSucc`. If the names have
      drifted in the pinned mathlib commit, update §3.2 and
      §3.3 to match.
   3. `@[simp]` interp lemmas (`tuplePack_zero`,
      `tuplePack_succ`, `tupleAt_zero`,
      `tupleAt_succ_last`, `tupleAt_succ_castSucc`).
   4. `Nat.tupleAt_le`.
   5. `Nat.tupleAt_tuplePack`, `Nat.tuplePack_tupleAt`.
   6. `Nat.tuplePack_le`.
2. `GebLeanTests/Tupling.lean`: §6.1 (Nat-side
   smoke) and §6.2 (Nat-side boundary examples).
3. `GebLean/Utilities/ERTupling.lean`:
   1. `ERMor1.tuplePack`, `ERMor1.tupleAt`.
   2. `@[simp]` interp lemmas (`interp_tuplePack`,
      `interp_tupleAt`).
   3. `ERMor1.PolyBound.ofTuplePack`,
      `ERMor1.PolyBound.ofTupleAt`.
   4. `ERMorN.lift`, `ERMorN.ofVec` (the §4.4.1 helpers).
   5. `ERMorN.tupleAt_tuplePack`,
      `ERMorN.tuplePack_tupleAt`.
4. `GebLeanTests/ERTupling.lean`: §6.1 (ER-side
   smoke) and §6.2 (ER-side boundary examples).
5. **Citation cross-check.** Verify each entity's docstring
   contains the §7-listed citation verbatim, not a
   shortened paraphrase. Cross-reference the §7.1/§7.2
   tables.
6. **Gate check (§5.2).** Read `LawvereERCat.lean`; tick
   G1, G2, G3 mechanically.
7. If gate passes: `LawvereERCat.tupleIso`, appended to
   `ERTupling.lean`. Delete §8.3.
8. If gate fails: fill §8.3 with the diagnosis. Do not land
   any iso scaffolding.
9. Re-export both modules from `GebLean.lean`; register
   both test files in `GebLeanTests.lean`.
10. `lake build`, `lake test`, `markdownlint-cli2` clean on
    any new docs.

## §10 Success criteria

- `Tupling.lean` and `ERTupling.lean` compile with no
  warnings (no `sorry`, no `admit`, no unused-variable
  warnings, no linter warnings).
- All theorems in §3 and §4 stated and proven.
- All `#guard`s in §6.1 and `example`s in §6.2 pass at
  build time.
- §5.2 gate ticked: either §5.3 iso lands or §8.3
  diagnosis is filled.
- Both modules added to `GebLean.lean`; both test files
  registered in `GebLeanTests.lean`.
- `lake build` and `lake test` pass clean.
- `markdownlint-cli2` clean on this spec and on any new
  research-doc updates the cycle produces.
