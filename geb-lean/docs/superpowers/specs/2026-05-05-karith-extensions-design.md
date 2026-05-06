# KArith Extensions Design

Four enhancements to the existing K^sim arithmetic library
(`Utilities/KArith.lean`), plus a small refactor to its dependency
`LawvereKSimInterp.lean`:

1. Generalize the dite ↔ Fin.append bridge from `interp_rec1_succ`
   into a public reusable simrec lemma; refactor `interp_rec1_succ`
   as a short corollary.
2. Add a `KMor1.permArgs` utility (precompose with a context
   permutation) and a `KMor1.swap` specialization for the common
   2-argument case; refactor `KMor1.monus` to use `swap`.
3. Add `KMor1.eq` (Tourlakis predicate-as-zero `χ(x = y)`) and
   `KMor1.condEq` (`if x = y then z else z'`).
4. Add `KMor1.pow` (two-variable exponentiation) at K^sim_2 via the
   Marchenkov / Wikipedia formula `x^y = 2^((xy+x+1)·y) mod
   (2^(xy+x+1) ∸ x)`.

Predecessor spec:
`docs/superpowers/specs/2026-05-05-karith-design.md` (the original
twelve-function K^sim arithmetic library, now committed on branch
`worktree-karith-impl`).

## 1. Background

The KArith library (~24 commits on `worktree-karith-impl`) provides
twelve K^sim arithmetic functions (`pred`, `isZero`, `add`, `double`,
`cond`, `notEq1`, `mult`, `monus`, `pow2`, `mod`, `div`, `divNat`)
each with a `@[simp]`-marked correctness theorem. Two patterns
emerged that are worth promoting to reusable utilities:

- The dite ↔ `Fin.append (Fin.cons …)` bridge from
  `interp_rec1_succ` (~70 lines) is a property of `KMor1.simrec`
  generally, not just of the `rec1` wrapper. Promoting it to a
  public lemma `KMor1.simrecVec_succ_append` makes it reusable for
  subsequent K^sim simrec analyses.
- The argument-swap pattern in `KMor1.monus` (composing
  `monusSwapped` with a `proj`-swap context) generalizes to a
  permutation-of-arguments utility `KMor1.permArgs`.

Two new functions complete the user-facing surface of the library:

- `KMor1.eq` provides decidable equality on `Nat` lifted to a K^sim
  morphism, in Tourlakis's predicate-as-zero convention so that
  `cond ∘ eq` directly gives `if x = y then ... else ...`. The
  natural composite `condEq` exposes this pattern as a single
  4-argument K^sim morphism.
- `KMor1.pow` is two-variable exponentiation `λ(x, y). x^y`. The
  obvious simrec construction (`pow(x, 0) = 1`, `pow(x, y+1) =
  mult(x, pow(x, y))`) puts it at level 3 because the step uses
  `mult` (level 2). The Wikipedia "Further Examples" formula
  ([Elementary recursive function][wiki]) gives a level-2
  composition: `x^y = 2^((xy+x+1)·y) mod (2^(xy+x+1) ∸ x)`. All
  components (mult, pow2, monus, mod, succ) are already at level
  ≤ 2 in `KArith`, so the composition stays at K^sim_2. The proof
  of correctness uses standard mathlib lemmas (`Nat.pow_mul`,
  `Nat.pow_mod`) plus a bound `x^y + x < 2^(xy+x+1)` proved by a
  short induction.

[wiki]: https://en.wikipedia.org/wiki/Elementary_recursive_function#Superposition_bases_for_elementary_functions

## 2. Module organization

- **Modify `GebLean/LawvereKSimInterp.lean`**: add the general
  `KMor1.simrecVec_succ_append` public theorem; move the
  dite-bridge proof there from `interp_rec1_succ`; refactor
  `interp_rec1_succ` as a short corollary. Also add
  `KMor1.interp_permArgs` and `KMor1.interp_swap`.
- **Modify `GebLean/LawvereKSim.lean`**: add `KMor1.permArgs` and
  `KMor1.swap` definitions (level-preserving by construction).
- **Modify `GebLean/Utilities/KArith.lean`**:
  - Refactor `KMor1.monus` to use `KMor1.swap KMor1.monusSwapped`
    (the `interp_monus` `@[simp]` statement is unchanged; only the
    proof body shifts).
  - Add a private helper `KMor1.signum : KMor1 1` (`signum n = 1
    iff n > 0, 0 iff n = 0`) — needed for `eq`'s normalized 0/1
    output.
  - Add `KMor1.eq : KMor1 2` and `@[simp] KMor1.interp_eq`.
  - Add `KMor1.condEq : KMor1 4` and `@[simp]
    KMor1.interp_condEq`.
  - Add Nat-level helpers `KMor1.pow_bound` and
    `KMor1.pow_formula`.
  - Add `KMor1.pow : KMor1 2` and `@[simp] KMor1.interp_pow`.
- **Modify `GebLeanTests/Utilities/KArith.lean`**: add `#guard`s
  for the new functions.

## 3. Refactor: `simrecVec_succ_append`

### 3.1 New theorem in `LawvereKSimInterp.lean`

```lean
/-- Step-case interp for `simrecVec` in `Fin.append (Fin.cons …)`
form: equivalent to `simrecVec_succ` (which produces a dite-form
context) but with the context expressed via the standard
`Fin.append` of the `Fin.cons` of the recursion variable + params
and the previous-vector singleton family. -/
@[simp] theorem KMor1.simrecVec_succ_append {a k : ℕ}
    (h : Fin (k + 1) → KMor1 a)
    (g : Fin (k + 1) → KMor1 (a + 1 + (k + 1)))
    (params : Fin a → ℕ) (n : ℕ) (j : Fin (k + 1)) :
    KMor1.simrecVec h g params (n + 1) j
      = (g j).interp (Fin.append (Fin.cons n params)
                                  (KMor1.simrecVec h g params n))
```

Proof body: the existing dite-bridge proof from `interp_rec1_succ`,
generalized to arbitrary `k + 1` instead of `k = 0` (which had
specialized to `Fin 1` for the prev-vector). The two
`Fin.castAdd` and `Fin.natAdd` casts and the inner `Fin.cons_zero`
and `Fin.cons_succ` case-splits work identically; the right-side
singleton `(fun _ : Fin 1 => prev_val)` becomes the general
`KMor1.simrecVec h g params n` (a `Fin (k+1) → ℕ` family).

### 3.2 Refactored `interp_rec1_succ`

```lean
@[simp] theorem KMor1.interp_rec1_succ {a : ℕ}
    (h : KMor1 a) (g : KMor1 (a + 2))
    (n : ℕ) (params : Fin a → ℕ) :
    (KMor1.rec1 h g).interp (Fin.cons (n + 1) params)
      = g.interp (Fin.append (Fin.cons n params)
          (fun _ : Fin 1 =>
            (KMor1.rec1 h g).interp (Fin.cons n params))) := by
  unfold KMor1.rec1
  rw [KMor1.interp_simrec]
  rw [show (Fin.cons (n + 1) params : Fin (a + 1) → ℕ) 0 = n + 1 by
        simp [Fin.cons_zero],
      show (fun j : Fin a =>
              (Fin.cons (n + 1) params : Fin (a + 1) → ℕ)
                (Fin.succ j))
            = params by funext j; simp [Fin.cons_succ]]
  rw [KMor1.simrecVec_succ_append]
  -- Reduce the trailing `simrecVec ... n` (a Fin 1 → ℕ family)
  -- back into the (rec1 h g).interp form via folding.
  congr 1
  funext j
  fin_cases j
  -- The single-index lookup `simrecVec _ _ _ n ⟨0, _⟩` equals
  -- `(rec1 h g).interp (Fin.cons n params)` by interp_simrec
  -- backwards on rec1.
  show KMor1.simrecVec (fun _ => h) (fun _ => g) params n
        ⟨0, by decide⟩
      = (KMor1.rec1 h g).interp (Fin.cons n params)
  unfold KMor1.rec1
  rw [KMor1.interp_simrec]
  rw [show (Fin.cons n params : Fin (a + 1) → ℕ) 0 = n by
        simp [Fin.cons_zero],
      show (fun j : Fin a =>
              (Fin.cons n params : Fin (a + 1) → ℕ)
                (Fin.succ j))
            = params by funext j; simp [Fin.cons_succ]]
```

The exact tactic chain may simplify further during implementation
(e.g., `simp [KMor1.interp_simrec, KMor1.simrecVec_succ_append,
Fin.cons_zero, Fin.cons_succ]` might close it directly). The aim is
~10–15 lines, replacing the original ~70-line bridge proof.

## 4. `permArgs` and `swap`

### 4.1 Definitions in `LawvereKSim.lean`

```lean
/-- Precompose a `KMor1 m` term with a context permutation
`σ : Fin n → Fin m`. Given `f : KMor1 m`, produces a `KMor1 n`
that interprets at context `c : Fin n → ℕ` as `f.interp (c ∘ σ)`.

Built from `comp` and `proj` only; no new constructors. The level
is unchanged: `(f.permArgs σ).level = f.level` (since `comp` takes
`max` of children's levels and the `proj`s have level 0). -/
def KMor1.permArgs {n m : ℕ} (σ : Fin n → Fin m) (f : KMor1 m) :
    KMor1 n :=
  KMor1.comp f (fun i => KMor1.proj (σ i))

/-- Argument-swap for 2-argument K^sim morphisms:
`(f.swap).interp ![a, b] = f.interp ![b, a]`. Specialization of
`permArgs` to the swap permutation on `Fin 2`. -/
def KMor1.swap (f : KMor1 2) : KMor1 2 :=
  KMor1.permArgs
    (fun i => match i with
      | ⟨0, _⟩ => ⟨1, by decide⟩
      | ⟨1, _⟩ => ⟨0, by decide⟩) f
```

### 4.2 Interp lemmas in `LawvereKSimInterp.lean`

```lean
@[simp] theorem KMor1.interp_permArgs {n m : ℕ}
    (σ : Fin n → Fin m) (f : KMor1 m) (ctx : Fin n → ℕ) :
    (f.permArgs σ).interp ctx = f.interp (fun i => ctx (σ i)) := by
  unfold KMor1.permArgs
  rw [KMor1.interp_comp]
  rfl

@[simp] theorem KMor1.interp_swap (f : KMor1 2) (ctx : Fin 2 → ℕ) :
    (KMor1.swap f).interp ctx
      = f.interp (fun i => match i with
                            | ⟨0, _⟩ => ctx 1
                            | ⟨1, _⟩ => ctx 0) := by
  unfold KMor1.swap
  rw [KMor1.interp_permArgs]
  -- The σ image-context reduces to the match expression.
  rfl
```

Alternative `interp_swap` statement using `Matrix.cons` notation if
preferred: `(KMor1.swap f).interp ctx = f.interp ![ctx 1, ctx 0]`.
The `match` form may unify more cleanly with downstream rewrites
(e.g., the `monus` refactor below); pick whichever closes downstream
proofs more easily during implementation.

### 4.3 `monus` refactor

Replace the existing definition:

```lean
def KMor1.monus : KMor1 2 :=
  KMor1.comp KMor1.monusSwapped (fun i => match i with
    | ⟨0, _⟩ => KMor1.proj ⟨1, by decide⟩
    | ⟨1, _⟩ => KMor1.proj ⟨0, by decide⟩)
```

with:

```lean
def KMor1.monus : KMor1 2 := KMor1.swap KMor1.monusSwapped
```

The `interp_monus` `@[simp]` statement (`KMor1.monus.interp ctx =
ctx 0 - ctx 1`) is unchanged. Its proof body shifts to use
`interp_swap` and `interp_monusSwapped`:

```lean
@[simp] theorem KMor1.interp_monus (ctx : Fin 2 → ℕ) :
    KMor1.monus.interp ctx = ctx 0 - ctx 1 := by
  unfold KMor1.monus
  rw [KMor1.interp_swap, KMor1.interp_monusSwapped]
```

The `swap` substitutes `ctx 1` for slot 0 and `ctx 0` for slot 1
inside `monusSwapped`, which then computes `ctx 0 - ctx 1` per its
`interp_monusSwapped` lemma (`monusSwapped(y, x) = x - y`).

### 4.4 Level

Both `permArgs` and `swap` preserve level: `(f.permArgs σ).level =
f.level` and `(KMor1.swap f).level = f.level`. The `comp` with
atomic `proj`s adds nothing to the max-of-children. We do not state
this as a lemma (the existing `decide`-based level checks suffice).

## 5. `eq` and `condEq`

### 5.1 Helper: `KMor1.signum`

```lean
/-- Sign function: `signum(0) = 0`, `signum(n+1) = 1`. Equivalently
`signum(n) = 1 - (1 - n)` (composition of two `isZero`s). Used as
the level-1 helper for normalizing `eq`'s output to {0, 1}. -/
private def KMor1.signum : KMor1 1 :=
  KMor1.comp KMor1.isZero (fun _ : Fin 1 => KMor1.isZero)

@[simp] private theorem KMor1.interp_signum (ctx : Fin 1 → ℕ) :
    KMor1.signum.interp ctx = if ctx 0 = 0 then 0 else 1 := by
  unfold KMor1.signum
  rw [KMor1.interp_comp, KMor1.interp_isZero, KMor1.interp_isZero]
  rcases ctx 0 with _ | n
  · simp
  · simp
```

(If a public `signum` is later useful, drop `private`. For this
spec it's only used by `eq`.)

### 5.2 `KMor1.eq`

Construction: `eq(x, y) = signum((x ∸ y) + (y ∸ x))`. The inner
sum vanishes exactly at `x = y`; `signum` normalizes to 0 (when
equal) or 1 (when not).

```lean
/-- Characteristic of the predicate `x = y` (Tourlakis convention):
`eq(x, y) = 0` iff `x = y`, `eq(x, y) = 1` iff `x ≠ y`.

Composes with `cond` for the natural "if x = y then z else z'":
`cond(eq(x, y), z, z') = if x = y then z else z'` (because
`cond(0, z, z') = z` per Tourlakis PR §0.1.0.17(6) and Tourlakis
convention has `eq(x, y) = 0 iff x = y`).

The name refers to the predicate being characterized; per
Tourlakis convention, the value is 0 when the predicate holds.

Tourlakis Notes 10.2.20 (`λx.x = a ∈ K_{1,*}` for fixed `a`,
generalized here to two-variable equality via Boolean closure of
K_{n,*} per Notes 10.2.14 plus `monus` at K^sim_2). -/
def KMor1.eq : KMor1 2 :=
  KMor1.comp KMor1.signum (fun _ : Fin 1 =>
    KMor1.comp KMor1.add (fun i => match i with
      | ⟨0, _⟩ => KMor1.monus
      | ⟨1, _⟩ => KMor1.swap KMor1.monus))

@[simp] theorem KMor1.interp_eq (ctx : Fin 2 → ℕ) :
    KMor1.eq.interp ctx = if ctx 0 = ctx 1 then 0 else 1 := by
  unfold KMor1.eq
  rw [KMor1.interp_comp, KMor1.interp_signum,
      KMor1.interp_comp, KMor1.interp_add,
      KMor1.interp_monus, KMor1.interp_swap, KMor1.interp_monus]
  -- Goal involves `if (ctx 0 - ctx 1) + (ctx 1 - ctx 0) = 0
  --                then 0 else 1` and we want
  --                `if ctx 0 = ctx 1 then 0 else 1`.
  by_cases h : ctx 0 = ctx 1
  · simp [h]
  · -- ctx 0 ≠ ctx 1: WLOG one of the truncated subtractions is
    -- positive, so the sum is positive.
    rcases lt_or_gt_of_ne h with hlt | hgt
    · simp [Nat.sub_eq_zero_of_le (le_of_lt hlt),
            Nat.sub_pos_of_lt hlt, h]
      omega
    · simp [Nat.sub_eq_zero_of_le (le_of_lt hgt),
            Nat.sub_pos_of_lt hgt, h]
      omega
```

Level: `monus` is K^sim_2; `swap` preserves; `add` is K^sim_1;
outer `signum` is K^sim_1; max = 2.

### 5.3 `KMor1.condEq`

```lean
/-- "If x = y then z else z'": composition of `cond` with
`eq(x, y)` as the switch.

`condEq(x, y, z, z') = z` when `x = y`, `z'` otherwise. Uses
`cond`'s convention `cond(0, z, z') = z` plus Tourlakis
`eq(x, y) = 0 iff x = y`. -/
def KMor1.condEq : KMor1 4 :=
  KMor1.comp KMor1.cond (fun i => match i with
    | ⟨0, _⟩ =>
        -- eq applied to slots 0, 1 of the outer 4-arg ctx
        KMor1.eq.permArgs (fun j => match j with
          | ⟨0, _⟩ => ⟨0, by decide⟩
          | ⟨1, _⟩ => ⟨1, by decide⟩)
    | ⟨1, _⟩ => KMor1.proj ⟨2, by decide⟩
    | ⟨2, _⟩ => KMor1.proj ⟨3, by decide⟩)

@[simp] theorem KMor1.interp_condEq (ctx : Fin 4 → ℕ) :
    KMor1.condEq.interp ctx
      = if ctx 0 = ctx 1 then ctx 2 else ctx 3 := by
  unfold KMor1.condEq
  rw [KMor1.interp_comp, KMor1.interp_cond, KMor1.interp_permArgs,
      KMor1.interp_eq, KMor1.interp_proj, KMor1.interp_proj]
  by_cases h : ctx 0 = ctx 1
  · simp [h]
  · simp [h]
```

(The `permArgs` lifts `eq` from `Fin 2` to `Fin 4` by selecting
slots 0, 1 — the inclusion of `Fin 2` into `Fin 4`'s first two
slots. If a more direct `comp eq ![proj 0, proj 1]` pattern proves
cleaner during implementation, use that instead; both produce the
same level-2 morphism.)

Level: `eq` is K^sim_2; `permArgs` preserves; `cond` is K^sim_1;
outer `comp` keeps at 2.

## 6. `pow`

The Wikipedia formula is

  `x^y = 2^((xy + x + 1) · y) mod (2^(xy + x + 1) ∸ x)`.

It is a closed-form composition of `mult`, `add`, `succ`, `pow2`,
`monus`, `mod` — all already at K^sim_2 in this library. The
construction therefore lands at K^sim_2 with no need for a
new simrec.

The proof of correctness has three pieces:

- `pow_bound : ∀ x y, x^y + x < 2^(x*y + x + 1)` (Nat-level).
- `pow_formula : ∀ x y, x^y =
  2^((x*y + x + 1) * y) % (2^(x*y + x + 1) - x)` (Nat-level).
- `interp_pow` (K^sim-level): unfolds the composition and applies
  `pow_formula`.

### 6.1 `KMor1.pow_bound`

Statement (Nat-level, lives in the `Nat` namespace within
`Utilities/KArith.lean` for proximity, or in a new `Utilities/`
file if preferred):

```lean
/-- Bound used in the Wikipedia/Marchenkov formula for `x^y`:
`x^y + x < 2^(x*y + x + 1)`. The bound holds because:
- `x = 0`: `0^y + 0 ≤ 1 < 2 = 2^1`.
- `y = 0`: `1 + x < 2^(x + 1)` by `Nat.lt_two_pow_self` plus
  one extra factor of 2.
- `x ≥ 1, y ≥ 1`: `x^y ≤ 2^(x*y)` (since `x ≤ 2^x` for `x ≥ 1`),
  so `x^y + x ≤ 2^(x*y) + 2^(x*y) = 2^(x*y + 1) ≤ 2^(x*y + x + 1)`.

Proved by induction on `y` with case-split on `x = 0`. -/
private theorem KMor1.pow_bound (x y : ℕ) :
    x ^ y + x < 2 ^ (x * y + x + 1) := by
  induction y with
  | zero =>
    -- x^0 + x = 1 + x < 2^(x + 1)
    simp [Nat.pow_zero]
    have := Nat.lt_two_pow_self (n := x + 1)
    omega
  | succ y ih =>
    sorry  -- iterate; uses Nat.pow_succ + ih + Nat.pow_le_pow_right
```

The base case uses `Nat.lt_two_pow_self : n < 2^n` (mathlib). The
succ case combines `ih`, `Nat.pow_succ` (`x^(y+1) = x^y * x`), and
`Nat.pow_le_pow_right` (monotonicity in the exponent). The
implementation may need `Nat.mul_lt_mul_*` and `omega` for the
arithmetic.

### 6.2 `KMor1.pow_formula`

```lean
/-- Wikipedia/Marchenkov formula for `x^y`:

  `x^y = 2^((x*y + x + 1) * y) mod (2^(x*y + x + 1) - x)`.

Proof sketch:
- Let `m := x*y + x + 1`. By `pow_bound` at index `0` (i.e.
  `1 + x < 2^(x + 1) ≤ 2^m`), `2^m > x`, so `2^m - x` is genuine
  Nat subtraction (≥ 1).
- `2^(m*y) = (2^m)^y` by `Nat.pow_mul`.
- Modular: `2^m ≡ x (mod 2^m - x)` because `2^m = (2^m - x) + x`.
- Hence `(2^m)^y ≡ x^y (mod 2^m - x)`, by `Nat.pow_mod`-style
  reasoning (or direct induction on `y`).
- `x^y < 2^m - x` by `pow_bound` (rearranged), so
  `x^y mod (2^m - x) = x^y` by `Nat.mod_eq_of_lt`.
- Combining: `2^(m*y) mod (2^m - x) = x^y mod (2^m - x) = x^y`. -/
private theorem KMor1.pow_formula (x y : ℕ) :
    x ^ y =
      2 ^ ((x * y + x + 1) * y) %
        (2 ^ (x * y + x + 1) - x) := by
  sorry  -- see proof sketch above
```

Implementation note: the proof may want to introduce
`m := x * y + x + 1` and `M := 2^m - x` via `set` to keep terms
manageable. Mathlib lemmas to consider:
`Nat.pow_mul`, `Nat.pow_mod`, `Nat.mod_eq_of_lt`,
`Nat.add_sub_cancel'` (with the bound from `pow_bound`).

### 6.3 `KMor1.pow`

```lean
/-- Exponentiation `pow(x, y) = x ^ y` at K^sim_2.

Construction follows the Marchenkov / Wikipedia formula
`x^y = 2^((xy + x + 1) · y) mod (2^(xy + x + 1) ∸ x)`, a closed
composition of `mult`, `add`, `succ`, `pow2`, `monus`, `mod` (all
at K^sim_2). The result lands at K^sim_2 by composition; a direct
simrec construction `pow(x, y+1) = mult(x, pow(x, y))` would land
at level 3 because the step uses `mult`.

Marchenkov 2007 §1: `x^y` is in the elementary class `S = {x+y,
x∸y, x/y, 2^x}`. This particular composition is the one given
by Prunescu, Sauras-Altuzarra, Shunia (2025) in the basis
`{n+m, n mod m, 2^n}` (Wikipedia's "Further Examples"). -/
def KMor1.pow : KMor1 2 :=
  -- Build `m := x*y + x + 1` first.
  let mTerm : KMor1 2 :=
    KMor1.comp KMor1.succ (fun _ : Fin 1 =>
      KMor1.comp KMor1.add (fun i => match i with
        | ⟨0, _⟩ => KMor1.mult
        | ⟨1, _⟩ => KMor1.proj ⟨0, by decide⟩))
  -- Numerator: `2^(m * y)`
  let numerator : KMor1 2 :=
    KMor1.comp KMor1.pow2 (fun _ : Fin 1 =>
      KMor1.comp KMor1.mult (fun i => match i with
        | ⟨0, _⟩ => mTerm
        | ⟨1, _⟩ => KMor1.proj ⟨1, by decide⟩))
  -- Divisor: `2^m ∸ x`
  let divisor : KMor1 2 :=
    KMor1.comp KMor1.monus (fun i => match i with
      | ⟨0, _⟩ => KMor1.comp KMor1.pow2
                    (fun _ : Fin 1 => mTerm)
      | ⟨1, _⟩ => KMor1.proj ⟨0, by decide⟩)
  -- Result: `numerator mod divisor`
  KMor1.comp KMor1.mod (fun i => match i with
    | ⟨0, _⟩ => numerator
    | ⟨1, _⟩ => divisor)

@[simp] theorem KMor1.interp_pow (ctx : Fin 2 → ℕ) :
    KMor1.pow.interp ctx = ctx 0 ^ ctx 1 := by
  unfold KMor1.pow
  -- Normalize the let-bindings via `simp only` of the relevant
  -- interp lemmas:
  simp only [KMor1.interp_comp, KMor1.interp_mod, KMor1.interp_pow2,
             KMor1.interp_mult, KMor1.interp_add, KMor1.interp_succ,
             KMor1.interp_monus, KMor1.interp_proj]
  -- Now the goal is the Nat-level formula. Apply pow_formula
  -- (with the appropriate arrangement of `(ctx 0)`, `(ctx 1)`).
  exact (KMor1.pow_formula (ctx 0) (ctx 1)).symm
```

Level: every component is at K^sim_2 or below; composition at the
outermost `mod` keeps the maximum at 2.

## 7. Tests

In `GebLeanTests/Utilities/KArith.lean`:

```lean
-- swap (verify against monusSwapped recovering monus)
#guard (KMor1.swap KMor1.monusSwapped).interp ![5, 3] == 2
#guard (KMor1.swap KMor1.add).interp ![3, 7] == 10

-- eq
#guard KMor1.eq.interp ![3, 3] == 0
#guard KMor1.eq.interp ![3, 5] == 1
#guard KMor1.eq.interp ![5, 3] == 1
#guard KMor1.eq.interp ![0, 0] == 0

-- condEq
#guard KMor1.condEq.interp ![3, 3, 11, 22] == 11
#guard KMor1.condEq.interp ![3, 5, 11, 22] == 22
#guard KMor1.condEq.interp ![0, 0, 11, 22] == 11

-- pow
#guard KMor1.pow.interp ![2, 3] == 8
#guard KMor1.pow.interp ![3, 2] == 9
#guard KMor1.pow.interp ![1, 5] == 1
#guard KMor1.pow.interp ![5, 1] == 5
#guard KMor1.pow.interp ![0, 0] == 1
#guard KMor1.pow.interp ![0, 1] == 0
#guard KMor1.pow.interp ![5, 0] == 1
#guard KMor1.pow.interp ![2, 5] == 32
```

The `pow` `#guard`s involve mod of large powers of two. Empirical
risk: kernel reduction of `2^(2*3+2+1) = 2^9 = 512` raised to the
power 3 (i.e. `2^27`) is well within Lean's Nat-evaluation
capacity. The largest computation in the test set is
`2^(2*5+2+1) * 5 = 2^65`, which is a 66-bit arbitrary-precision
Nat — large but instant. If any `#guard` stalls, fall back to
`example : foo = bar := by simp` using the proved `@[simp]`
lemmas.

## 8. Build / commit ordering

1. Add `KMor1.simrecVec_succ_append`; refactor `interp_rec1_succ`.
   Verify the existing `KArith` proofs still pass.
2. Add `KMor1.permArgs` + `interp_permArgs`.
3. Add `KMor1.swap` + `interp_swap`.
4. Refactor `KMor1.monus` to use `swap`.
5. Add private `KMor1.signum` + `interp_signum`.
6. Add `KMor1.eq` + `interp_eq`.
7. Add `KMor1.condEq` + `interp_condEq`.
8. Prove `KMor1.pow_bound`.
9. Prove `KMor1.pow_formula`.
10. Add `KMor1.pow` + `interp_pow`.
11. Add tests.
12. Final verification.

Each step builds + tests cleanly before committing.

## 9. Out of scope

- General K^sim morphisms beyond elementary functions (the entire
  ⋃_n K^sym_n hierarchy equals primitive recursion, which does not
  contain Ackermann; mathlib's `Nat.Primrec.not_primrec_ackermann`
  formalizes this. Ackermann and faster-growing functions are
  therefore inexpressible in K^sim at any level, not merely
  out-of-scope here).
- Higher-arity equality predicates (`Fin k`-valued tuple
  equality); only 2-argument `eq` is provided.
- A general `pow_bound` / `pow_formula` for `Nat`-level lemmas
  beyond what `KMor1.pow` needs.
- Integer-square-root, factorial, GCD — natural follow-ons but
  not part of this spec.

## 10. Risk register

- **`pow_formula` proof complexity**: the substantive risk. It
  combines `Nat.pow_mul`, modular-exponent reasoning, and
  `Nat.mod_eq_of_lt`. Mitigation: factor as `pow_bound` (commit 8)
  and `pow_formula` (commit 9), each a standalone `Nat` lemma. If
  `pow_formula` resists, fall back to a direct simrec-on-`y`
  `pow_alt` that lands at K^sim_3, with `pow` swapped to it (level
  3 violates the user's level-2 target and would prompt re-spec).
- **`monus` refactor preserving downstream**: the `interp_monus`
  `@[simp]` lemma's statement is unchanged. Existing `monus`
  consumers should be unaffected.
- **`signum` collision**: previous K^sim work briefly considered
  `signum` as a helper for `notEq1`'s original (boolean-true)
  construction, then dropped. Verify no existing `signum`
  declaration before adding the new one.
- **`interp_rec1_succ` refactor preservation**: lemma name and
  `@[simp]` attribute unchanged. Downstream uses are unaffected.

## 11. References

- Original spec:
  `docs/superpowers/specs/2026-05-05-karith-design.md` — the
  twelve-function K^sim arithmetic library. This extension spec
  references the function definitions and conventions established
  there (`monus`, `cond`, `notEq1`, `pow2`, `mod`, etc.).
- Tourlakis, *Notes on Computability*, Notes 10.2.20 (`λx.x = a ∈
  K_{1,*}`), Notes 10.2.14 (Boolean closure of K_{n,*}), PR
  §0.1.0.17(6) (`switch`).
- Marchenkov 2007 §1, equation (2): basis `{x+y, x∸y, x/y, 2^x}`
  for the Kalmar elementary functions.
- Wikipedia "Further Examples" under
  *Elementary recursive function § Superposition bases*: the
  formula `x^y = 2^((xy+x+1)·y) mod (2^(xy+x+1) ∸ x)` from
  Prunescu, Sauras-Altuzarra, Shunia (2025).
- Mathlib: `Nat.pow_mul`, `Nat.pow_mod`, `Nat.mod_eq_of_lt`,
  `Nat.lt_two_pow_self`, `Nat.Primrec.not_primrec_ackermann`.
