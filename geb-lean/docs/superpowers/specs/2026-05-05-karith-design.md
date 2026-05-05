# KArith design

K^sim arithmetic library: a sibling of `Utilities/ERArith.lean` for the
`KMor1` Lawvere-theory term language defined in `LawvereKSim.lean`.
Provides ten elementary arithmetic functions at the lowest hierarchy
levels permitted by Tourlakis's K^sim hierarchy, each with a proven
`@[simp]` interp theorem against its standard `Nat`-valued meaning.

This is a pure transcription workstream: every function corresponds to
a published witness in Tourlakis's *Notes on Computability* (2019–2022)
or *Primitive Recursive Complexity Topics* (2018), and every `def` and
`theorem` carries a specific section/proposition citation per the
literature-citation discipline in `CLAUDE.md`.

## 1. Background

### 1.1 The K^sim hierarchy

Tourlakis (PR-complexity-topics §0.1.0.7; Notes 10.2.7) defines the
K^sim hierarchy:

- `K^sim_0` is the closure of `{λx.x, λx.x+1}` under substitution.
- `K^sim_{n+1}` is the closure of `K^sim_n ∪ R^sim_{n+1}` under
  substitution, where `R^sim_{n+1}` is the family of functions obtained
  from simultaneous primitive recursion (`simprim`) over `K^sim_n`.

The Lean encoding (`GebLean/LawvereKSim.lean`) follows this exactly: a
`KMor1 n` syntactic level (`KMor1.level`) of `n` corresponds to
membership in `K^sim_n`. Level 0 covers constants and shifted
projections; `simrec` and `raise` each add one level; `comp` takes the
maximum.

The Tourlakis classification table (Notes Prop 10.2.12) places the ten
functions of this design at levels:

| Function | K^sim level | Source |
| --- | --- | --- |
| `pred` (= λx.x ∸ 1) | 1 | PR §0.1.0.17(4); Notes 10.2.12 r2 |
| `isZero` (= λx.1 ∸ x) | 1 | PR §0.1.0.17(3) |
| `add` (= λxy.x+y) | 1 | PR §0.1.0.17(1); Notes 10.2.12 r1 |
| `double` (= λx.2x) | 1 | derived from `add` |
| `cond` (switch, λxyz. y if x=0 else z) | 1 | PR §0.1.0.17(6) |
| `notEq1` (= χ(x ≠ 1) per Tourlakis) | 1 | PR §0.1.0.20 + Notes 10.2.14 |
| `mult` (= λxy.xy) | 2 | PR §0.1.0.17(b); Notes 10.2.12 r4 |
| `monus` (= λxy.x ∸ y) | 2 | PR §0.1.0.17(a); Notes 10.2.12 r6 |
| `pow2` (= λx.2^x) | 2 | PR §0.1.0.17(c); Notes 10.2.12 r5 |
| `mod` (= λxy.rem(x,y)) | ≤ 2 | Marchenkov 2007; Notes 4.2.3 |

### 1.2 Lean encoding conventions

The `KMor1` `simrec` constructor encodes Tourlakis's `simprim`. With
parameters `a k : ℕ`, output index `i : Fin (k+1)`, base family
`h : Fin (k+1) → KMor1 a` and step family
`g : Fin (k+1) → KMor1 (a + 1 + (k + 1))`, it produces a term of
`KMor1 (a + 1)` with semantics

```text
f_i(0,    y⃗) = h_i(y⃗)
f_i(x+1,  y⃗) = g_i(x, y⃗, f_0(x,y⃗), …, f_k(x,y⃗))
```

Slot 0 of the `(a+1)`-arity result is the recursion variable; slots
`1..a` are the parameters.

In the step-context for `g_i`, the slots are:

- slot 0: recursion variable `x`
- slots `1..a`: parameters `y⃗`
- slots `a+1..a+k+1`: previous values `f_0(x,y⃗), …, f_k(x,y⃗)`

The single-output non-simultaneous specialization
(`k = 0`, `i = 0`) is so common that we add a thin wrapper, `KMor1.rec1`
(see §3).

## 2. Module layout

- `GebLean/LawvereKSim.lean`: add `KMor1.rec1` shortly after the `KMor1`
  inductive definition. Definition only; no interp content.
- `GebLean/LawvereKSimInterp.lean`: add `KMor1.interp_rec1_zero` and
  `KMor1.interp_rec1_succ` `@[simp]` lemmas, derived from the existing
  `KMor1.simrecVec_zero` and `KMor1.simrecVec_succ`.
- `GebLean/Utilities/KArith.lean` (new): the ten arithmetic functions,
  their `@[simp]` interp theorems, and `example : foo.level ≤ N` level
  proofs. Sibling of `GebLean/Utilities/ERArith.lean`.
- `GebLean.lean`: re-export `Utilities/KArith.lean`.
- Inline `#guard` blocks in `Utilities/KArith.lean` (mirroring
  `Utilities/ERArith.lean`): small-input evaluation tests for each
  function plus boundary cases.

## 3. `rec1`: the non-simultaneous primrec wrapper

### 3.1 Definition

```lean
/-- Single-output (non-simultaneous) primitive recursion at arity
`a + 1`.  The base `h : KMor1 a` returns the value at recursion
variable `0`; the step `g : KMor1 (a + 2)` receives the recursion
variable, the parameters, and the previous value, in this slot order:

* slot `0`            : recursion variable `x`
* slots `1, …, a`     : parameters `y_1, …, y_a`
* slot `a + 1`        : previous value `f(x, y⃗)`

It returns the value at `x + 1`.  Definitional reduction to
`KMor1.simrec` with `k = 0`, `i = 0`.

Tourlakis Notes 10.2.7 (definition of K^sim, with simultaneous
recursion as the primitive); the non-simultaneous case is the
`k = 0` specialization. -/
def KMor1.rec1 {a : ℕ} (h : KMor1 a) (g : KMor1 (a + 2)) :
    KMor1 (a + 1) :=
  KMor1.simrec (a := a) (k := 0) (i := 0)
    (fun _ => h) (fun _ => g)
```

### 3.2 Interp lemmas

```lean
@[simp] theorem KMor1.interp_rec1_zero {a : ℕ}
    (h : KMor1 a) (g : KMor1 (a + 2))
    (params : Fin a → ℕ) :
    (KMor1.rec1 h g).interp (Fin.cons 0 params)
      = h.interp params

@[simp] theorem KMor1.interp_rec1_succ {a : ℕ}
    (h : KMor1 a) (g : KMor1 (a + 2))
    (n : ℕ) (params : Fin a → ℕ) :
    (KMor1.rec1 h g).interp (Fin.cons (n + 1) params)
      = g.interp (Fin.append (Fin.cons n params)
          (fun _ : Fin 1 =>
            (KMor1.rec1 h g).interp (Fin.cons n params)))
```

`interp_rec1_zero` reduces directly via `simrec` interp +
`simrecVec_zero` and is `rfl`-close. `interp_rec1_succ` is **not**
definitional: the existing `simrecVec_succ` produces the step context
in dite form (`if idx.val < a + 1 then …`), whereas the lemma above
states the equivalent `Fin.append (Fin.cons …)` form. Bridging the
two requires `funext idx; rcases idx with ⟨v, h_v⟩; by_cases v < a+1;
…` plus `Fin.cons_zero`/`Fin.cons_succ`/`Fin.append_left`/
`Fin.append_right` rewrites — the same shape as the existing proof of
`KMor1.simrecVec_eq_Nat_simRecVec` in `LawvereKSimInterp.lean`. This
is not a one-line `rfl`.

### 3.3 Level

`(KMor1.rec1 h g).level = max h.level g.level + 1` by definitional
unfolding, matching the existing `level_simrec`.

## 4. Function-by-function spec

Conventions for the rest of this section:

- Every function is `def`'d in `GebLean/Utilities/KArith.lean` under
  `namespace GebLean`.
- Every function gets a `@[simp]` interp theorem.
- Every function gets `example : foo.level ≤ N := by decide`.
- Names go under the `KMor1` namespace (e.g. `KMor1.pred`).
- Docstrings cite Tourlakis at the level of section/example/proposition.
- For functions with naturally-recursive parameters in the "wrong" slot
  for K^sim (where slot 0 is the recursion variable), an explicit named
  swap or helper is provided.

### 4.1 `pred : KMor1 1`

Source: PR §0.1.0.17(4).

```text
pred(0)   = 0
pred(x+1) = x
```

```lean
def KMor1.pred : KMor1 1 :=
  KMor1.rec1
    (h := KMor1.zero)            -- value at 0
    (g := KMor1.proj ⟨0, by decide⟩)
    -- step ctx is Fin (0+2) = Fin 2: slot 0 = recvar x, slot 1 = prev
    -- step returns x = proj 0

@[simp] theorem KMor1.interp_pred (ctx : Fin 1 → ℕ) :
    KMor1.pred.interp ctx = (ctx 0).pred
```

Level proof: `example : KMor1.pred.level = 1 := by decide`.

### 4.2 `isZero : KMor1 1`

Source: PR §0.1.0.17(3); equivalent to `λx.1 ∸ x`.

```text
isZero(0)   = 1
isZero(x+1) = 0
```

Helper at K_0 (made non-private since `pow2` reuses it; both live in
the same module but the constant `1` at any arity is generally useful):

```lean
def KMor1.one : KMor1 0 :=
  KMor1.comp KMor1.succ (fun _ => KMor1.zero)
```

with `@[simp] interp_one : KMor1.one.interp ctx = 1` (definitional).

```lean
def KMor1.isZero : KMor1 1 :=
  KMor1.rec1
    (h := KMor1.one)             -- value at 0 is 1
    (g := KMor1.zero)            -- value at x+1 is 0

@[simp] theorem KMor1.interp_isZero (ctx : Fin 1 → ℕ) :
    KMor1.isZero.interp ctx = if ctx 0 = 0 then 1 else 0
```

Level: 1.

### 4.3 `add : KMor1 2`

Source: PR §0.1.0.17(1); Notes 10.2.12 row 1.

```text
add(0,   y) = y
add(x+1, y) = succ(add(x, y))
```

```lean
def KMor1.add : KMor1 2 :=
  KMor1.rec1
    (h := KMor1.proj ⟨0, by decide⟩)         -- a = 1; base ctx = (y); return y
    (g := KMor1.comp KMor1.succ
            (fun _ : Fin 1 => KMor1.proj ⟨2, by decide⟩))
    -- step ctx is Fin (1+2) = Fin 3: slot 0 = x, slot 1 = y, slot 2 = prev
    -- step returns succ(prev) = succ(proj 2)

@[simp] theorem KMor1.interp_add (ctx : Fin 2 → ℕ) :
    KMor1.add.interp ctx = ctx 0 + ctx 1
```

Level: 1.

### 4.4 `double : KMor1 1`

Derived; PR §0.1.0.17 implicit. Direct construction at level 1 to keep
the dependency chain shallow (`pow2` only needs `double`, not `add`).

```text
double(0)   = 0
double(x+1) = succ(succ(double(x)))
```

```lean
def KMor1.double : KMor1 1 :=
  KMor1.rec1
    (h := KMor1.zero)
    (g := KMor1.comp KMor1.succ
            (fun _ : Fin 1 =>
              KMor1.comp KMor1.succ
                (fun _ : Fin 1 => KMor1.proj ⟨1, by decide⟩)))
    -- a = 0; step ctx Fin 2: slot 0 = x, slot 1 = prev
    -- return succ(succ(prev))

@[simp] theorem KMor1.interp_double (ctx : Fin 1 → ℕ) :
    KMor1.double.interp ctx = 2 * ctx 0
```

Level: 1.

### 4.5 `cond : KMor1 3`

Source: PR §0.1.0.17(6) ("switch").

```text
cond(0,   y, z) = y
cond(x+1, y, z) = z
```

```lean
def KMor1.cond : KMor1 3 :=
  KMor1.rec1
    (h := KMor1.proj ⟨0, by decide⟩)
    -- a = 2; base ctx = (y, z); return y = proj 0
    (g := KMor1.proj ⟨2, by decide⟩)
    -- step ctx is Fin (2+2) = Fin 4
    -- slots 0 = x, 1 = y, 2 = z, 3 = prev; step returns z = proj 2

@[simp] theorem KMor1.interp_cond (ctx : Fin 3 → ℕ) :
    KMor1.cond.interp ctx = if ctx 0 = 0 then ctx 1 else ctx 2
```

Level: 1.

### 4.6 `notEq1 : KMor1 1`

Source: PR §0.1.0.20 (Corollary placing `λx. x = a` in K_{1,*}) +
Notes 10.2.14 (Boolean closure of K_{n,*}).

**Convention**: Tourlakis's predicate-as-zero convention. The
characteristic of a predicate `P(x)` is a function `χ_P` with
`χ_P(x) = 0` iff `P(x)` holds and `χ_P(x) ≠ 0` (normalized to 1)
otherwise. `notEq1` is the characteristic of the predicate `x ≠ 1`,
hence the value pattern below — the name `notEq1` evokes the
predicate being characterized, not the value semantics:

```text
notEq1(0)   = 0       -- x ≠ 1 holds at x = 0, so χ = 0
notEq1(1)   = 1       -- x ≠ 1 fails at x = 1, so χ ≠ 0
notEq1(n+2) = 0       -- x ≠ 1 holds at x ≥ 2, so χ = 0
```

(This is opposite the boolean-true convention; the Lean K^sim
formalization adheres to Tourlakis's convention throughout to
minimize cognitive switching against the source.)

Construction following Tourlakis's standard approach for `x = a`
predicates (composition only, no new recursion):

```text
notEq1(x) = isZero((x ∸ 1) + (1 ∸ x))
        = isZero(pred(x) + isZero(x))
```

Verification of values:

- `x = 0`: `isZero(pred(0) + isZero(0)) = isZero(0 + 1) = isZero(1) = 0` ✓
- `x = 1`: `isZero(pred(1) + isZero(1)) = isZero(0 + 0) = isZero(0) = 1` ✓
- `x = 2`: `isZero(pred(2) + isZero(2)) = isZero(1 + 0) = isZero(1) = 0` ✓
- `x ≥ 2`: `isZero(pred(x) + 0) = isZero(x − 1) = 0` (since x ≥ 2 ⇒
  x − 1 ≥ 1) ✓

```lean
def KMor1.notEq1 : KMor1 1 :=
  KMor1.comp KMor1.isZero (fun _ : Fin 1 =>
    KMor1.comp KMor1.add (fun i => match i with
      | ⟨0, _⟩ => KMor1.pred
      | ⟨1, _⟩ => KMor1.isZero))

@[simp] theorem KMor1.interp_notEq1 (ctx : Fin 1 → ℕ) :
    KMor1.notEq1.interp ctx = if ctx 0 = 1 then 1 else 0
```

Level: 1 (max of `isZero` (1), `add` (1), inner `pred`/`isZero` (1)
is 1; outer `comp`s do not raise level).

### 4.7 `mult : KMor1 2`

Source: PR §0.1.0.17(b); Notes 10.2.12 row 4.

```text
mult(0,   y) = 0
mult(x+1, y) = y + mult(x, y)
```

```lean
def KMor1.mult : KMor1 2 :=
  KMor1.rec1
    (h := KMor1.zero)
    (g := KMor1.comp KMor1.add (fun i =>
      match i with
      | ⟨0, _⟩ => KMor1.proj ⟨1, by decide⟩       -- y
      | ⟨1, _⟩ => KMor1.proj ⟨2, by decide⟩))     -- prev
    -- a = 1; step ctx Fin 3: slot 0 = x, slot 1 = y, slot 2 = prev

@[simp] theorem KMor1.interp_mult (ctx : Fin 2 → ℕ) :
    KMor1.mult.interp ctx = ctx 0 * ctx 1
```

Level: 2 (outer `rec1` adds 1 to max child level which is 1 for `add`).

### 4.8 `monus : KMor1 2`

Source: PR §0.1.0.17(a); Notes 10.2.12 row 6.

```text
monus(x, 0)   = x
monus(x, y+1) = pred(monus(x, y))
```

K^sim's `simrec` recurses on slot 0; we want to recurse on `y` (the
second arg). Strategy: build a swapped helper `monusSwapped(y, x)` that
recurses on slot 0, then expose `monus(x, y)` as a `comp` that swaps
the projections. The swap is a level-0 composition, so the final level
is unchanged.

```lean
private def KMor1.monusSwapped : KMor1 2 :=
  KMor1.rec1
    (h := KMor1.proj ⟨0, by decide⟩)
    -- a = 1; base ctx = (x); return x
    (g := KMor1.comp KMor1.pred
            (fun _ : Fin 1 => KMor1.proj ⟨2, by decide⟩))
    -- step ctx Fin 3: slot 0 = y, slot 1 = x, slot 2 = prev; return pred(prev)

@[simp] private theorem KMor1.interp_monusSwapped (ctx : Fin 2 → ℕ) :
    KMor1.monusSwapped.interp ctx = ctx 1 - ctx 0

def KMor1.monus : KMor1 2 :=
  KMor1.comp KMor1.monusSwapped (fun i =>
    match i with
    | ⟨0, _⟩ => KMor1.proj ⟨1, by decide⟩       -- y → slot 0 of monusSwapped
    | ⟨1, _⟩ => KMor1.proj ⟨0, by decide⟩)      -- x → slot 1 of monusSwapped

@[simp] theorem KMor1.interp_monus (ctx : Fin 2 → ℕ) :
    KMor1.monus.interp ctx = ctx 0 - ctx 1
```

Level: 2 (`monusSwapped` is 2; outer `comp` keeps it at 2).

### 4.9 `pow2 : KMor1 1`

Source: PR §0.1.0.17(c); Notes 10.2.12 row 5.

```text
pow2(0)   = 1
pow2(x+1) = double(pow2(x))
```

```lean
def KMor1.pow2 : KMor1 1 :=
  KMor1.rec1
    (h := KMor1.one)
    (g := KMor1.comp KMor1.double
            (fun _ : Fin 1 => KMor1.proj ⟨1, by decide⟩))
    -- a = 0; step ctx Fin 2: slot 0 = x, slot 1 = prev; return double(prev)

@[simp] theorem KMor1.interp_pow2 (ctx : Fin 1 → ℕ) :
    KMor1.pow2.interp ctx = 2 ^ ctx 0
```

Level: 2 (outer `rec1` adds 1 to `double`'s level 1).

### 4.10 `mod : KMor1 2`

Source — placement: Marchenkov 2007 (PDF
`superpositions-elementary-arithmetic-functions-marchenkov.pdf`,
abstract and equation (2)) establishes that `{x+y, x∸y, x/y, 2^x}`
is a superposition basis for the Kalmar elementary functions,
i.e. ER. Marchenkov's §1 also defines `rm(x, y)` as the remainder
of `x` divided by `y`, with `rm(x, 0) = x` (matching Lean's
`Nat.mod_zero`). Since `rm(x, y) = x ∸ ((x/y) · y)` and ER is
closed under multiplication and `∸`, we have `rm ∈ ER`. By Notes
10.2.20 (`K^sim_n = L_n`) plus Meyer–Ritchie (`L_2 = ER`),
ER = K^sim_2, hence `rm ∈ K^sim_2`. We therefore claim
`mod.level ≤ 2`; the spec does not assert tight placement
(Tourlakis 10.2.16 places only the fixed-divisor `rem(x, 2)` at
K^sim_1, leaving the general-divisor lower bound open in the
literature).

Source — construction technique: Notes 4.2.3 (`rem(x, 2) ∈ K_1^sim`
via simultaneous recursion with a companion "shifted-row" function).
The construction below generalizes Tourlakis 4.2.3's
two-function-simrec technique from the fixed-divisor case (`y = 2`)
to the general-divisor case. This generalization is not literally
present in Tourlakis; per the literature-citation discipline the
docstring of `KMor1.mod` and `KMor1.modAux` will explicitly note
"generalization of Tourlakis Notes 4.2.3 technique to general
divisor; placement in K^sim_2 follows from Marchenkov 2007 basis".

This is the only function in the spec that requires true simultaneous
(system-size > 1) primitive recursion in our K^sim Lean encoding.
Construction: track two functions jointly,

```text
f₀(x, y) = rem(x, y)                  -- the result
f₁(x, y) = (y ∸ 1) ∸ rem(x, y)        -- "distance to wrap"
```

so that the comparison "would `rem + 1` reach `y`?" reduces to
"is `f₁` zero?", which `cond` (level 1) can dispatch directly on
`f₁`.

```text
f₀(0,   y) = 0
f₁(0,   y) = pred(y)
f₀(x+1, y) = cond(f₁(x, y), 0,           succ(f₀(x, y)))
f₁(x+1, y) = cond(f₁(x, y), pred(y),     pred(f₁(x, y)))
```

Verification (recall `cond(0, b1, b2) = b1`, `cond(n+1, b1, b2) = b2`):

- `y = 0`: `pred(0) = 0`, so `f₁(0, 0) = 0`. At each step `cond`
  switches on `f₁_prev = 0`, picking `branch1`. So `f₀(x+1, 0) = 0`
  and `f₁(x+1, 0) = pred(0) = 0` for all x. Hence `modAux(x, 0) = 0`.
  (Note: the outer `KMor1.mod` per §4.10.1 short-circuits this
  branch via its own outer `cond` on `y`, returning `x` when `y = 0`
  to match `Nat.mod_zero`. The y = 0 internal walkthrough above is
  thus unused at the `KMor1.mod` level; it is included for
  completeness of `KMor1.modAux`'s standalone semantics.)
- `y ≥ 1`: `f₁(0, y) = y - 1`. At each step:
  - if `f₁_prev > 0` (no wrap), `cond` picks `branch2`:
    `f₀(x+1, y) = succ(f₀_prev)`, `f₁(x+1, y) = pred(f₁_prev)`.
  - if `f₁_prev = 0` (wrap), `cond` picks `branch1`:
    `f₀(x+1, y) = 0`, `f₁(x+1, y) = pred(y) = y - 1`.
  So `f₁` cycles through `y-1, y-2, …, 0, y-1, y-2, …`, producing
  `f₀ = 0, 1, 2, …, y-1, 0, 1, 2, …` = `x % y`. ✓

```lean
private def KMor1.modAux : KMor1 2 :=
  KMor1.simrec (a := 1) (k := 1) (i := ⟨0, by decide⟩)
    (h := fun i => match i with
      | ⟨0, _⟩ => KMor1.zero       -- f₀(0, y) = 0
      | ⟨1, _⟩ => KMor1.pred)      -- f₁(0, y) = pred(y)
    (g := fun i =>
      -- step ctx is Fin (1 + 1 + 2) = Fin 4:
      -- slot 0 = x, slot 1 = y, slot 2 = prev_f₀, slot 3 = prev_f₁
      match i with
      | ⟨0, _⟩ =>
          -- f₀ step: cond(prev_f₁, 0, succ(prev_f₀))
          KMor1.comp KMor1.cond (fun j => match j with
            | ⟨0, _⟩ => KMor1.proj ⟨3, by decide⟩
            | ⟨1, _⟩ => KMor1.zero
            | ⟨2, _⟩ => KMor1.comp KMor1.succ
                          (fun _ : Fin 1 => KMor1.proj ⟨2, by decide⟩))
      | ⟨1, _⟩ =>
          -- f₁ step: cond(prev_f₁, pred(y), pred(prev_f₁))
          KMor1.comp KMor1.cond (fun j => match j with
            | ⟨0, _⟩ => KMor1.proj ⟨3, by decide⟩
            | ⟨1, _⟩ => KMor1.comp KMor1.pred
                          (fun _ : Fin 1 => KMor1.proj ⟨1, by decide⟩)
            | ⟨2, _⟩ => KMor1.comp KMor1.pred
                          (fun _ : Fin 1 => KMor1.proj ⟨3, by decide⟩)))
```

Level proof: `modAux` is one `simrec` over children of level ≤ 1
(`zero`, `pred`, `cond` (1), `succ`); `simrec` adds 1; final level 2.

#### 4.10.1 Convention for `mod(x, 0)`

User intent (per session clarification): match the standard
`Nat.mod` convention, i.e. `x % 0 = x` (Lean: `Nat.mod_zero`).

`modAux` produces `0` at `y = 0`, not `x`. Wrap with one outer `cond`:

```lean
def KMor1.mod : KMor1 2 :=
  KMor1.comp KMor1.cond (fun i => match i with
    | ⟨0, _⟩ => KMor1.proj ⟨1, by decide⟩       -- switch on y
    | ⟨1, _⟩ => KMor1.proj ⟨0, by decide⟩       -- if y = 0, return x
    | ⟨2, _⟩ => KMor1.modAux)                  -- else, run modAux

@[simp] theorem KMor1.interp_mod (ctx : Fin 2 → ℕ) :
    KMor1.mod.interp ctx = ctx 0 % ctx 1
```

Level: 2 (outer `cond` and `modAux` are both 2; outer `comp` keeps at 2).

**Proof obligation for `interp_mod`** (the only nontrivial interp
proof in the module). Case-split on `ctx 1 = 0` vs `> 0`:

- `ctx 1 = 0` case: `KMor1.mod` outer `cond` selects branch 1
  (`proj 0 = ctx 0`); the result is `ctx 0` directly. Combined with
  `Nat.mod_zero : x % 0 = x` gives the equality.
- `ctx 1 > 0` case: outer `cond` selects branch 2 (`modAux`); the
  result is `modAux.interp ctx`. Reduce to a helper lemma
  `KMor1.modAux_components` stating: for all `x : ℕ`, `y : ℕ`, with
  `y ≥ 1`, the joint vector returned by `KMor1.simrecVec` for the
  `modAux` recursion at step `x` with parameter `y` equals
  `![x % y, (y - 1) - x % y]`. Proof by induction on `x`:
  - Base `x = 0`: vector is `![0, pred(y)] = ![0, y - 1]` with
    `0 % y = 0` and `(y - 1) - 0 = y - 1`, both for `y ≥ 1`.
  - Step `x → x + 1`: by IH the prev vector is
    `![x % y, (y - 1) - x % y]`. Case-split on
    `(y - 1) - x % y = 0` (i.e. `x % y = y - 1`, the wrap point):
    - Wrap case: `cond` picks branch 1; new vector is
      `![0, y - 1]`. Need `(x + 1) % y = 0` (true since
      `x % y = y - 1` ⇒ `x ≡ -1 (mod y)` ⇒ `x + 1 ≡ 0 (mod y)`)
      and `(y - 1) - 0 = y - 1`. Mathlib lemma:
      `Nat.add_mod_right` or `Nat.succ_mod_self`.
    - No-wrap case (`(y - 1) - x % y > 0`): `cond` picks branch 2;
      new vector is `![succ(x % y), pred((y - 1) - x % y)]`. Need
      `(x + 1) % y = (x % y) + 1` and
      `(y - 1) - ((x % y) + 1) = pred((y - 1) - x % y)`. Mathlib
      lemma: `Nat.add_mod` plus `Nat.mod_eq_of_lt` for the
      condition `(x % y) + 1 < y`.

The `interp_mod` lemma then projects component 0 of the joint
vector. Decomposition: (a) `modAux_components` as a separate lemma,
(b) the wrap-case mathlib bridge, (c) the no-wrap-case mathlib bridge,
(d) the final `interp_mod` assembly.

## 5. Tests

### 5.1 Coverage

For each of the ten user-facing functions, in `test/KArithTest.lean`
(or per-module `#guard` blocks in `Utilities/KArith.lean`):

For each function, 3 to 6 `#guard` cases on small inputs, plus
`example : foo.level ≤ N := by decide`. Tests live inline in
`Utilities/KArith.lean` (mirroring `Utilities/ERArith.lean`'s pattern).

Tests cover at minimum: identity-like input, generic small input, and
the boundary case relevant to the function's recurrence. For `mod`
the boundary set is wider because the construction's wrap-detection
must be exercised.

```lean
#guard KMor1.pred.interp ![0] = 0
#guard KMor1.pred.interp ![1] = 0
#guard KMor1.pred.interp ![5] = 4
#guard KMor1.isZero.interp ![0] = 1
#guard KMor1.isZero.interp ![1] = 0
#guard KMor1.isZero.interp ![10] = 0
#guard KMor1.add.interp ![0, 7] = 7
#guard KMor1.add.interp ![3, 4] = 7
#guard KMor1.double.interp ![0] = 0
#guard KMor1.double.interp ![5] = 10
#guard KMor1.cond.interp ![0, 11, 22] = 11
#guard KMor1.cond.interp ![1, 11, 22] = 22
#guard KMor1.cond.interp ![2, 11, 22] = 22
#guard KMor1.notEq1.interp ![0] = 0    -- Tourlakis χ(x ≠ 1)
#guard KMor1.notEq1.interp ![1] = 1
#guard KMor1.notEq1.interp ![2] = 0
#guard KMor1.notEq1.interp ![5] = 0
#guard KMor1.mult.interp ![0, 7] = 0
#guard KMor1.mult.interp ![3, 4] = 12
#guard KMor1.monus.interp ![5, 3] = 2
#guard KMor1.monus.interp ![3, 5] = 0
#guard KMor1.monus.interp ![5, 5] = 0
#guard KMor1.pow2.interp ![0] = 1
#guard KMor1.pow2.interp ![1] = 2
#guard KMor1.pow2.interp ![4] = 16
#guard KMor1.mod.interp ![0, 5] = 0
#guard KMor1.mod.interp ![5, 1] = 0
#guard KMor1.mod.interp ![5, 5] = 0
#guard KMor1.mod.interp ![6, 3] = 0
#guard KMor1.mod.interp ![7, 3] = 1
#guard KMor1.mod.interp ![3, 0] = 3
```

### 5.2 Test sizing risk

Per the prior session memory note
`feedback_godel_interp_not_decidable_in_tests.md`, deeply nested
`simrec` interpretations evaluate symbolically and can stall a `#guard`.
All inputs above are bounded by ~16 with at most level-2 simrecs.
Empirical verification (via `mcp__lean-lsp__lean_run_code` against
minimal reproductions of each construction) confirms all `#guard`s
in §5.1 evaluate in milliseconds, including the `mod` system-size-2
simrec at inputs `(7, 3)` and `(5, 1)`. Mitigation if a `#guard`
unexpectedly stalls: switch from `#guard foo = bar` to
`example : foo = bar := by simp` using the proven `@[simp]` interp
lemmas, which avoids kernel reduction of the underlying simrec tree.

## 6. Build sequence

Per `CLAUDE.md` workflow §1, §3, every increment must build with `lake
build` and `lake test`, no warnings, no `sorry`. Order:

1. Add `KMor1.rec1` to `LawvereKSim.lean`. Smoke-check `level` reduces
   correctly with one trivial `example`.
2. Add `interp_rec1_zero`, `interp_rec1_succ` to
   `LawvereKSimInterp.lean`. Verify with one trivial `#guard`.
3. Create `Utilities/KArith.lean`. Add functions in dependency order:
   - Phase 1 (level 1, no KArith deps): `one` (private),
     `pred`, `isZero`, `add`, `double`, `cond`, `notEq1`. Each
     function landed independently with its `@[simp]` interp lemma
     and `level` example proof, building cleanly.
   - Phase 2 (level 2, deps on Phase 1): `mult`, `monusSwapped`
     (private), `monus`, `pow2`. Each landed independently with proofs.
   - Phase 3: `modAux` (private), `mod`. The `mod` correctness proof
     (`interp_mod`) is the longest proof in the spec; its inductive
     helper `modAux_components` is built first.
4. Re-export `Utilities/KArith` from `GebLean.lean`.
5. Add tests; `lake test` must pass.

## 7. Out of scope

- Higher-level functions (Ackermann, tetration, bsum, bprod) — not part
  of this spec.
- Quotient lifts (`KSimMor` morphisms via `KMorNQuo`) of these functions
  — not part of this spec.
- `kToER` translations of these functions — handled uniformly by the
  existing `kToERFunctor`; no per-function bridge needed here.
- Modification of any existing inline `addK` test fixture from Step 5;
  that test stays as it is, independent of `KArith.add`.

## 8. Risk register

- **`mod` convention reconciliation**: §4.10.1's outer `cond` adds one
  composition. If the implementation finds a cleaner encoding directly
  producing `Nat.mod` semantics (including the `y = 0` case), we switch.
- **Symbolic `#guard` blowup**: §5.2 mitigation in place.
- **`monusSwapped` arg-order swap surface area**: the swap helper is
  private and its interp lemma is proved against `ctx 1 - ctx 0`,
  exposing only `KMor1.monus` with the conventional `ctx 0 - ctx 1`
  semantics.
- **`mod` literature placement vs construction technique**: §4.10
  cites Marchenkov 2007 for the placement claim (`mod ∈ K^sim_2`) and
  Tourlakis Notes 4.2.3 for the inspiration of the two-function
  simrec technique. The specific generalization from `rem(x, 2)` to
  general-divisor `rem(x, y)` is not literally in either source; the
  docstring of `KMor1.mod` and `KMor1.modAux` must explicitly state
  this generalization per the literature-citation discipline.
- **`decide` for `level` proofs**: empirically verified to work for
  all spec functions including the system-size-2 `modAux`. (Test
  performed via `mcp__lean-lsp__lean_run_code` against minimal
  reproductions of each construction.) If a subsequent change to
  `KMor1.level` or `Finset.univ.sup` reduction breaks this, fall
  back to explicit `unfold KMor1.level; simp [...]`.
- **`interp_rec1_succ` is propositional, not definitional**: §3.2
  notes the proof shape (dite ↔ `Fin.append (Fin.cons …)` bridge,
  modeled on `KMor1.simrecVec_eq_Nat_simRecVec`).
- **`interp_mod` proof scope**: §4.10.1 spells out the inductive
  structure and the four sub-lemmas (`modAux_components`, wrap case
  bridge, no-wrap case bridge, final assembly).

## 9. References

- Tourlakis, *Notes on Computability* (2019–2022),
  `.claude/docs/arithmetic-hierarchies/tourlakis-Computability-Notes-ROOT.pdf`
  — Definition 10.2.7, Proposition 10.2.12, Example 4.2.3,
  Definitions 10.2.13–10.2.20.
- Tourlakis, *Primitive Recursive Complexity Topics* (2018),
  `.claude/docs/arithmetic-hierarchies/PR-complexity-topics.pdf`
  — Definition 0.1.0.7, Example 0.1.0.17, Proposition 0.1.0.20.
- `docs/lawvere-k-sim-hierarchy.md` — design principles P1–P10 for the
  Lean K^sim formalization, including the level rule
  (`simrec`/`raise` add 1; `comp` takes max).
- `GebLean/Utilities/ERArith.lean` — sibling module for `ERMor1`-side
  arithmetic; this spec mirrors its structure.
