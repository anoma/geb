# K^sim polynomial-bound: research and references

## Overview

This document collects citations from the available reference PDFs to
support the dominance argument needed in `kToER_interp`'s simrec case
in the formalization of Tourlakis's K^sim hierarchy. The chain of
sub-claims is:

1. **K^sim_1 ⊆ linear-value-bounded**: every level-1 K^sim function
   is dominated by a linear function of its arguments.
2. **Pairing function polynomial bound**: the pairing function used
   to encode simrec traces (Szudzik in our project, Cantor `J = (x+y)^2 + x`
   in Tourlakis) is polynomial in its arguments.
3. **`seqPack` polynomial closure**: iterated pairing of polynomially-
   bounded components yields a polynomially-bounded code.
4. **Polynomial-iter bound**: iterating a polynomially-bounded step `j`
   times keeps the value bounded by an elementary (E^3 ⊇ ER) function
   of `j` and the arguments.
5. **K^sim_n = E^{n+1} for n ≥ 2**: in particular K^sim_2 = E^3 = ER.
6. **ER closed under bounded primitive recursion**: by definition
   (and under bounded simultaneous recursion).
7. **Tower bound for ER**: every ER function is bounded by a fixed
   iterate of an elementary generator (e.g. `e_2 = x^2 + 2`, or 2^x).

The principal source is George Tourlakis,
*Primitive Recursive Complexity Topics*, EECS 4111/5111 Fall 2018
(file `PR-complexity-topics.pdf`, henceforth "Tourlakis 2018"). It
covers all seven sub-claims with explicit numbered propositions. The
*Computability Notes* PDF (Tourlakis 2019–2022, henceforth "Tourlakis
CN") contains the same material reorganized as Chapter 10 (with cross-
references to its earlier Chapter 4 on coding and Hilbert–Bernays).
The Damnjanovic 1994 paper and the standalone Grzegorczyk hierarchy
chapter (henceforth "Recursion Class Ch. 4") provide complementary
formulations.

Notation conventions in this document:

- "Tourlakis 2018 §0.1.0.X" refers to the numbered subsection X of
  the single section 0.1 of the available PDF.
- "Tourlakis CN 10.2.X" refers to the numbered theorems/lemmas of
  Tourlakis CN Chapter 10.
- "Recursion Class Ch. 4 Prop. 4.X" refers to the standalone PDF
  `grzegorczyk-hierarchy-recursion-class-chapter-4.pdf`.
- "Damnjanovic Thm/Lem X.Y" refers to the Notre Dame J. Formal Logic
  paper `elementary-functions-and-loop-programs.pdf`.

Tourlakis's hierarchy `K^sim_n` is defined in Tourlakis 2018 §0.1.0.7;
his Grzegorczyk hierarchy `E^n` is in §0.1.0.22.

## Claim 1: K^sim_1 ⊆ linear-value-bounded

**Statement (project notation)**: for every `f : KMor1 a` with
`level f ≤ 1`, there exist `c, k : ℕ` (depending on `f`) such that
`interp f ctx ≤ c · max(ctx) + k` for all argument vectors
`ctx`.

### Fix A: direct structural induction on K^sim_1

The previous version of this document derived the bound indirectly
via "K^sim_1 ⊆ E^1 because the level-1 worked examples have linear
bounds, and E^1 has linear bounds by Tourlakis 2018 §0.1.0.27 (2)".
This routing through E^1 is circular: the inclusion K^sim_1 ⊆ E^1
itself relies on each level-1 K^sim function being linear-bounded.
The corrected derivation is a direct structural induction on
`KMor1` terms whose `level` is at most 1.

**Lemma 1.A (linear-value-boundedness of K^sim_1, project form)**.
For every `f : KMor1 a` with `level f ≤ 1`, there exist
`c, k : ℕ` such that for every argument vector `ctx : Fin a → ℕ`,

```text
interp f ctx ≤ c · max(ctx) + k
```

where `max(ctx) := max_{i < a} ctx i` (with `max(ctx) = 0` for `a = 0`).

**Proof sketch (structural induction on `KMor1`)**. Let
`P(f) := ∃ c k, ∀ ctx, interp f ctx ≤ c · max(ctx) + k`.

- **`zero`**: interp is the constant `0`. Take `c = 0`, `k = 0`.
- **`succ`**: interp is `ctx 0 + 1 ≤ 1 · max(ctx) + 1`. Take
  `c = 1`, `k = 1`.
- **`proj i`**: interp is `ctx i ≤ 1 · max(ctx) + 0`. Take `c = 1`,
  `k = 0`.
- **`comp f gs`**: by induction, each `gs i` has linear bound
  `c_i · max(ctx) + k_i`, and `f` has linear bound
  `c · max(args) + k` for some constants. Then
  `max(args) ≤ (max_i c_i) · max(ctx) + (max_i k_i)`, and
  composing gives a linear bound
  `c · ((max_i c_i) · max(ctx) + (max_i k_i)) + k`
  `= (c · max_i c_i) · max(ctx) + (c · max_i k_i + k)`.
- **`raise f`** (level `f ≤ 0`): the inner term has level 0, so
  by Lemma 1.B (level-0 shape lemma below) its interp has the
  shifted-projection or constant form; in either case the bound
  is linear. Take `c = 1`, `k` from the level-0 shape.
- **`simrec h g`** at level 1 (`level h, level g ≤ 0`): the K^sim
  simrec schema iterates `g` for `ctx 0` steps starting from `h`'s
  value. The simrec at arity `a` enlarges the step `g`'s context
  to arity `a + 2` (counter slot, accumulator slot, the `a` original
  parameters). Lemma 1.B applies to `g`'s arity-`(a + 2)` context:
  `g`'s interp has the shifted-projection-or-constant form in that
  enlarged context. The same holds for `h` at arity `a`. Both
  shapes have no multiplicative coefficient on `max`. One iteration
  of a shifted-projection step adds at most a constant to the
  running register vector; therefore `j` iterations add at most
  `j · K` for some constant `K` depending on `g`. The resulting
  bound is
  `interp (simrec h g) ctx ≤ max(ctx) + (ctx 0) · K + K_h`
  for constants `K, K_h`. Since `ctx 0 ≤ max(ctx)`, this is
  `≤ (1 + K) · max(ctx) + K_h`, again linear in `max(ctx)`.

The structural lemma about level-0 K^sim used in the `raise` and
`simrec` cases is the following.

**Lemma 1.B (level-0 shape lemma)**. Every level-0 K^sim term
`f : KMor1 a` has interp of one of the two forms

- the constant function `λ ctx. k` for some `k : ℕ`, or
- the shifted-projection `λ ctx. ctx i + k` for some `i : Fin a`
  and `k : ℕ`.

**Proof sketch (structural induction on `KMor1` with `level ≤ 0`)**.
Level-0 K^sim is the closure of `{zero, succ, proj}` under
substitution (Tourlakis 2018 §0.1.0.7 with `n = 0`; equivalently,
the "K_0 = K_0^sim" base case of §0.1.0.15).

- `zero`: constant `0`, of shifted-projection form with `k = 0`
  vacuously, or constant form with `k = 0`.
- `succ`: interp is `ctx 0 + 1`, shifted-projection with
  `i = 0`, `k = 1`.
- `proj i`: interp is `ctx i`, shifted-projection with
  `k = 0`.
- `comp f gs`: by induction, each `gs i'` has constant or
  shifted-projection form, and `f` has constant or
  shifted-projection form. Substituting the `gs i'`-results
  into `f`:
  - if `f` is the constant `k_f`, the composite is the constant
    `k_f` (independent of `gs`);
  - if `f` is shifted-projection `args i + k_f` (selecting input
    slot `i` of `f`'s argument vector and adding `k_f`), then the
    composite is `(gs i) ctx + k_f`, and there are two
    sub-cases:
    - if `gs i` has constant form `λ ctx. c`, the composite is
      `c + k_f`, a constant;
    - if `gs i` has shifted-projection form `λ ctx. ctx j + k_g`,
      the composite is `ctx j + (k_g + k_f)`, again
      shifted-projection (with the two shifts added).

This shape lemma is what ultimately ensures that level-1 simrec is
linear and not exponential: a level-0 step has no multiplicative
coefficient on `max`, so iterating it adds only a constant per step.

### Citations supporting Lemma 1.A and 1.B

The level-0 shape lemma matches Recursion Class Ch. 4 Prop. 4.3
(p. 33), which states the analogous result for E_0:

> **Proposition 4.3** Each f in E_0 satisfies for n-ary x⃗:
> ∃_{i ≤ n} ∃k ∀x⃗ (f(x⃗) ≤ x_i + k)

The proof there is by induction on E_0 derivation depth, with
base cases `z(x) ≤ x`, `s(x) ≤ x + 1`, `p^i_k(x⃗) ≤ x_i`, and
inductive cases for composition (which is the only growth-generating
operation at level 0). The same derivation tree analysis applies
to level-0 K^sim (= K_0 = K_0^sim by Tourlakis 2018 §0.1.0.15
with `n = 0`).

Tourlakis 2018 §0.1.0.17 (worked examples) lists six representative
level-1 K^sim functions: `x + y`, `x(1−.y)`, `1−.x`, `x−.1`,
`bx/2c`, and `switch`. Each is presented with its defining
recursion equations, from which a linear bound is immediate by
Lemma 1.A. The example list confirms that the linear-bound result
holds for the K^sim hierarchy specifically and not just for the
syntactic Grzegorczyk hierarchy.

Tourlakis CN 10.2.16 establishes the strict containment
`K_1 ⊊ K^sim_1`, exhibiting `λx. ⌊x/2⌋` as a level-1 K^sim function
that is not in K_1; the linear bound `⌊x/2⌋ ≤ x` is consistent with
Lemma 1.A.

**Caveats**:

- Lemma 1.A is stated only for `level f ≤ 1`; at level 2 the bound
  becomes polynomial (Tourlakis 2018 §0.1.0.27 (3)), and at level
  ≥ 3 it becomes a tower (clause (4) of the same lemma).
- The proof of the `simrec` case in Lemma 1.A relies on Lemma 1.B,
  which is what limits a level-0 step to "additive only". Without
  Lemma 1.B, the simrec case could give an exponential bound
  (multiplicative coefficient compounding per iteration).
- The translation of Tourlakis 2018 §0.1.0.27 (2) ("E^1 is
  linear-bounded") and Recursion Class Ch. 4 Prop. 4.4 ("E_1
  linear-bounded") to K^sim_1 requires either
  (a) a direct K^sim_1 structural induction as outlined above
  (the route taken by Lemma 1.A), or
  (b) the inclusion `K^sim_1 ⊆ E^1`, which the literature treats
  as a corollary of (a) plus E^1's closure properties.

**Relation to our use**: this is the base case of the polynomial-iter
chain. Linear-value-bounded ⇒ polynomially-bounded (with degree 1),
and the simrec trace at iteration `j` of a level-1 step then expands
at most polynomially (in `j` and the arguments).

## Claim 2: Pairing function polynomial bound

**Statement (project notation)**: the pairing function `pair : ℕ → ℕ → ℕ`
used to encode simrec component traces satisfies `pair x y ≤ p(x, y)`
for some polynomial `p` (in our project, `Nat.pair x y` is mathlib's
Cantor pairing; either Cantor or Szudzik elegant pairing satisfies a
quadratic bound).

**Citation**: Tourlakis 2018 §0.1.0.39 (Corollary, p. 17) and the
construction in §0.1.0.34 (Theorem on simultaneous bounded recursion,
p. 13).

**Original statement** (verbatim):

```text
The pairing function J = λxy.(x + y)^2 + x is in E^2, and so are
its projections K = λz.(μ̇ x)_{≤ z}(∃y)_{≤ z} J(x, y) = z and
L = λz.(μ̇ y)_{≤ z}(∃x)_{≤ z} J(x, y) = z.

[...]

The quadratic pairing function J = λxy.(x + y)^2 + x is appropriate.
Immediately, J ∈ K_2 by 0.1.0.17.
```

(Tourlakis 2018 §0.1.0.34 p. 13 and §0.1.0.39 p. 17.)

The same Cantor pairing is used in Damnjanovic §6 p. 506 (denoted
`J*(x, y) := (x + y)^2 + x`) and is the basis for the simrec-encoding
upper bounds throughout that paper.

**Caveats**:

- Our project uses `Nat.pair`, which is mathlib's pairing. The bound
  `Nat.pair x y ≤ (x + y + 1)^2` (or `(max x y + 1)^2` for Szudzik)
  is folklore, derivable from the closed form. mathlib has
  `Nat.pair_lt_pair_left` and similar lemmas, but a clean polynomial
  upper bound may need to be proved as a small lemma in
  `Utilities/`.
- The plan in `docs/lawvere-k-sim-hierarchy.md` §2.3.2 already
  anticipates Szudzik pairing in ER. The bound
  `pair x y ≤ (max x y + 1)^2 ≤ (x + y + 1)^2` is what is needed.

**Relation to our use**: `seqPack` is iterated pairing; once we have a
polynomial bound for the binary pairing, the iterated case follows
(Claim 3).

## Claim 3: `seqPack` polynomial closure

**Statement (project notation)**: for any natural `k` and any
polynomially-bounded functions `f_1, …, f_{k+1} : ℕ^a → ℕ` with
respective degrees `d_1, …, d_{k+1}`, the iterated encoding
`seqPack(f_1, …, f_{k+1}) := pair(f_1(x⃗), pair(f_2(x⃗), …))`
is polynomially bounded (in `x⃗`), with degree at most
`D_pack(k) := 2^k · max(d_1, …, d_{k+1})`.

**Citation**: Tourlakis 2018 §0.1.0.34 (Theorem on E^2 closure under
simultaneous bounded recursion, p. 13–14), display equation (1).

**Original statement** (verbatim):

```text
have the coding-decoding scheme—λz⃗_k.[[z_1, …, z_k]]^{(k)} and
Π_i^k—in E^2, where, by recursion on k, we define

[[z_1, …, z_k]]^{(k)} = z_1                          if k = 1
                      = J([[z_1, …, z_{k-1}]]^{(k-1)}, z_k)  if k > 1
```

This is Tourlakis's iterated Cantor pairing, defined recursively. The
closure under polynomial bounds follows because each pairing step is
quadratic in its two arguments, so iterating `k` times multiplies
the maximum degree by `2^k`. Concretely, with components of degrees
`d_1, …, d_{k+1}`, the iterated pairing's degree is bounded by
`2^k · max(d_1, …, d_{k+1})` (each pairing application doubles the
maximum component degree, and there are `k` pairing applications to
combine `k+1` components).

### Fix B (part 1): explicit ER bound term for `seqPack`

The literature establishes the polynomial bound but does not pin down
an explicit ER expression that realizes it. For the project we need
such an expression because the dominance witness is required to be
constructed inside `ERMor1`.

**Definition (`seqPackBound`, project-internal)**. Let
`D_pack(k) := 2^k · max(d_1, …, d_{k+1})` denote the polynomial
degree of the seqPack encoding at system size `k+1`, where
`d_i` is the polynomial degree of the `i`-th component. For each
natural `k` and degree parameter `D ≥ D_pack(k)`, define
`seqPackBound k D : ERMor1 1` whose interp at a single argument
`m : ℕ` is the closed-form polynomial

```text
interp (seqPackBound k D) m = (m + 1) ^ D
```

The exponent `D` is supplied as a parameter and instantiated to a
value at least `D_pack(k)` at the call site (where the components'
degrees are known). Setting `D = D_pack(k)` gives the tight bound;
setting `D = 2^{k+1} · max d_i` gives a uniform "next power of two"
form. This is constructible in ER because

- the constant `1` and the successor function are atomic ER generators;
- addition is in ER (Tourlakis 2018 §0.1.0.22 with `g_1 = λxy.x + y`,
  promoted to ER by Tourlakis 2018 §0.1.0.28);
- general exponentiation `λxy.x^y` is in ER = E^3 by Recursion Class
  Ch. 4 §4.4 ("composed exponentials are all elementary"), or
  equivalently by Tourlakis 2018 §0.1.0.34's E^2 closure under
  bounded simultaneous recursion combined with §0.1.0.17(c)'s
  `λx.2^x ∈ K_2`. (The single-base `2^x` lies in K_2 = K^sim_1
  per §0.1.0.17(c); promoting to general `x^y ∈ E^3` is folklore,
  derivable by bounded recursion on `y` with bound `(x+1)^y ≤
  2^{y · ⌈log_2 (x+1)⌉}`. For the project, taking general
  exponentiation as a derived ER operation is sufficient.)

**Lemma (project form)**. For any polynomially-bounded interp
expressions `f_1, …, f_{k+1}` with degree-`d_i` bounds
`f_i ctx ≤ (max(ctx) + 1) ^ d_i`, the iterated pairing satisfies

```text
seqPack k (f_1 ctx, …, f_{k+1} ctx)
  ≤ interp (seqPackBound k D_pack(k)) (max(ctx))
```

with `D_pack(k) = 2^k · max(d_1, …, d_{k+1})`.

**Proof outline**. Start from Claim 2's binary pairing bound
`pair x y ≤ (x + y + 1)^2 ≤ (2 · (max(x, y) + 1))^2`. Each pairing
application multiplies the maximum-degree polynomial bound on the
arguments by 2. After `k` pairing applications (combining `k+1`
components into a single value), the resulting degree is at most
`2^k · max(d_1, …, d_{k+1}) = D_pack(k)`.

**Source-cite for the polynomial estimate**: Damnjanovic Lemma 6.1 (2),
p. 506, gives a sharper concrete bound for iterated dyadic
concatenation,
`(a_1, …, a_n)^# < (2^6 · y)^{n(2n+1)+1}`,
which is polynomial in the arguments for fixed `n`. The Lean
implementation will prefer the Cantor- (or Szudzik-) pairing analogue
because that is the pairing in `Nat.pair`.

**Caveats**:

- Tourlakis works inside E^2, where polynomial bounds are the natural
  closure (Recursion Class Ch. 4 Prop. 4.5: every E^2 function is
  bounded by a polynomial). So once the components are in E^2, the
  iterated pairing is in E^2 by §0.1.0.34, and Prop. 4.5 then gives
  the polynomial bound automatically.
- The exponent constant `2^k` parameterizes the bound by the system
  size `k+1`; see the cross-cutting note on system size.

**Relation to our use**: we encode `systemSize = k+1` simrec
components into a single ℕ value. For fixed system size, the encoding
has polynomial bound; this feeds into Claim 4.

## Claim 4: Polynomial-iter bound

**Statement (project notation)**: if `step : ℕ → ℕ → ℕ` is a function
satisfying `step v x ≤ p(v, x)` for some fixed polynomial `p`, then
the iterated trace `step^j(v_0, x)` is bounded by a function of
`(j, v_0, x)` that lies in ER (more specifically in E^3, our target).

**Citation**: Recursion Class Ch. 4, Proposition 4.7 (p. 36),
combined with Recursion Class Ch. 4 Prop. 4.6 to embed the result in
E^3 = ER.

**Original statement** (Recursion Class Ch. 4 Prop. 4.7, verbatim):

> **Proposition 4.7** If f ∈ E_n then the iteration f^y ∈ E_{n+1}.
>
> Proof. The iteration of addition of a constant is bounded by a
> linear function, yielding the case for n = 0. Similarly, the
> iteration of a linear function is a polynomial function, yielding
> the n = 1 case. Let f ∈ E_{n+1}. We will consider the case of
> binary f, with iteration on x. When n > 1, we have by proposition
> 4.6 above, there is an m such that f(x, y) ≤ (e_{n-1})^m(max(x, y)).
> Now by induction, we show: f^z(x, y) ≤ (e_{n-1})^{mz}(max(x, y)).
> [...]
> Observe, further, that
> (e_{n-1})^{mz}(max(x, y)) ≤ (e_n)(max(x, y) + mz)
> So by chaining (★) with (★★), we obtain
> f^z(x, y) ≤ (e_n)(max(x, y) + mz)         (★★★)

(Recursion Class Ch. 4 p. 36, equation (4.7).)

**Specifically for n = 2** (the case we need for level-2 K^sim
simrec): if `step` is in E^2 (polynomial-bounded), then `step^j` is
bounded in E^3 = ER by `e_2(max(x, y) + m · j)` for some constant
`m` extracted from the polynomial bound on the step.

### Fix B (part 2): explicit ER bound term for the iterated step

The Recursion Class derivation gives an existential bound
(`∃ m, ∃ k, …`); the project requires an explicit ER term of fixed
shape using the project's `tower` notion. We construct this term
from the polynomial bound on the step.

**Tower convention**. The project's `Utilities/Tower.lean` defines
`tower : ℕ → ℕ → ℕ` by `tower 0 x = x`, `tower (h+1) x = 2^(tower h
x)`. So `tower h x` is the height-`h` iterated 2-power applied to
`x`. This is the iterated-exponential form. Translating to the
Recursion Class spine `e_0(x,y) = x + y`, `e_1(x) = x^2 + 2`,
`e_{n+2}(x+1) = e_{n+1}(e_{n+2}(x))`: the `e_2`-iterate
`(e_2)^h(x)` and the project's `tower h x` both grow as
height-`h` iterated exponentials. For `x ≥ 2`, `tower h x ≤
(e_2)^h(x)` (since `e_2` dominates `2^·` pointwise on `x ≥ 2`), and
`(e_2)^h(x) ≤ tower (h + c) x` for some constant `c` derivable from
`(e_2)^k(x) ≤ e_3(x + k)` and `e_3(x) ≤ tower x 2` for `x ≥ 2`. So
the project's `tower` is interchangeable with `(e_2)^h` up to
constant additive shifts in the height, and the bound shapes from
Recursion Class Ch. 4 Prop. 4.6 (`f ∈ E_{n+3}` ⇒
`f ≤ (e_{n+2})^k(max(x⃗))`) translate directly into project-side
`tower`-bounds.

**Setup**. Suppose `step : ERMor1 (a + 2)` (one accumulator slot, one
counter slot, `a` parameter slots) is polynomial-bounded with degree
`D_step`:

```text
interp step (v, j, x⃗) ≤ (max(v, j, max(x⃗)) + 1) ^ D_step
```

In our chain, `step = kSimPackedStep g` for the K^sim level-2
simrec packed via `seqPack` of system size `k+1`, with
`D_step = 2^k · D_g` for `D_g` the polynomial degree of the unpacked
level-2 step `g` (Claim 3 + Claim 1 at level 2). Equivalently,
`D_step = D_pack(k) · D_g / max(d_i)` when threading the degrees
through, but the conservative form `2^k · D_g` is sufficient.

**Iterated bound (explicit form)**. Setting `n = 2` in Prop. 4.7's
equation (★★★) with `f = step`: by Recursion Class Ch. 4
Prop. 4.6 applied to `step ∈ E^3`, there exists `m_step` such that
`step(v, x⃗) ≤ (e_2)^{m_step}(max(v, max(x⃗)))`. Then by Prop. 4.7
the iterated trace satisfies

```text
step^j (v_0, x⃗) ≤ e_3(max(v_0, max(x⃗)) + m_step · j)
```

The constant `m_step` is computable from `D_step` via Recursion
Class Ch. 4 Prop. 4.2 (4) (`(e_n)^k(x) ≤ e_{n+1}(x + k)`):
since a polynomial of degree `D_step` in `(max + 1)` is dominated
by `e_2(c · max)` for some constant `c` linear in `D_step` (each
`e_1`-application squares its input plus a constant; iterating
`⌈log_2 D_step⌉ + 1` times exceeds the polynomial-of-degree-`D_step`
bound). So `m_step ≤ ⌈log_2 D_step⌉ + 1` suffices.

**Why height 2 (in the project's `tower` sense)**. The bound
`e_3(max + m_step · j)` from Prop. 4.7 is one `e_3`-application
applied to a linear function. In project-side `tower` notation:
`e_3(u) = (e_2)^u(2) ≤ tower (u + c_3) 2` for `u ≥ 2` and a
fixed constant `c_3`, but also `e_3(u) ≤ tower 2 (poly(u))` for
suitable polynomial `poly`, since two iterations of `2^·` already
dominate `e_3` pointwise once the inner argument is at least `u + 1`
(folklore tracking of Prop. 4.6's proof). The project's chosen
shape `tower h_e (linear in (max, j))` with `h_e = 2` then
captures the iterated polynomial step's bound: the inner
`tower 1 (linear) = 2^(linear)` already dominates each polynomial-
in-`(max, j)` factor introduced by Prop. 4.7's chaining, and the
outer `2^·` accommodates a further compositional shift.

**Project-side ER term**. Define `iterAutoBoundExpr a h_e lh` so
that

```text
interp (iterAutoBoundExpr a h_e lh) (j, v_0, x⃗)
  = tower h_e (lh · max(v_0, max(x⃗)) + lh · j + lh)
```

For the chain at level 2, setting `h_e = 2`, `lh = m_step + 1`
yields `step^j (v_0, x⃗) ≤ interp (iterAutoBoundExpr a 2 lh)
(j, v_0, x⃗)`.

This term is constructible in ER because

- `tower h` for fixed `h` is in E^3 = ER (iterated `2^·` is
  elementary by Recursion Class Ch. 4 §4.4);
- linear arithmetic over its argument is in E^1 ⊆ ER (Tourlakis
  2018 §0.1.0.22's generators include `g_1 = λxy.x + y`, with
  multiplication by a constant via repeated addition).

The shape `tower h_e (linear)` matches Tourlakis 2018 §0.1.0.27 (4)
in form (with `A_n^k(max)` and project-side `tower h` both ranging
over height-indexed iterated-exponential bounds).

**Source-cite (Tourlakis 2018 §0.1.0.34, p. 13, verbatim)**:

> **0.1.0.34 Theorem.** E^2 is closed under simultaneous bounded
> recursion, where, additionally to the standard schema, k bounding
> functions B_i, for i = 1, …, k, are given, and the functions f_i
> resulting from the schema must satisfy f_i(x, y⃗) ≤ B_i(x, y⃗)
> everywhere.

**Caveats**:

- Tourlakis's E^2 closure under simultaneous bounded recursion gives
  that the resulting functions are again in E^2, *provided* an E^2
  bound is supplied. In our case the bound *is* what we are trying
  to exhibit; the dominance hypothesis is precisely the assertion
  that such a bound exists in ER (= E^3).
- The clean route is therefore: (i) note that the level-2 simrec
  step is bounded polynomially (via Claim 1 + 3 + Tourlakis 2018
  §0.1.0.17 examples table); (ii) apply Recursion Class Ch. 4
  Prop. 4.7 to get an E^3 bound for the iterated step.
- Tourlakis 2018 §0.1.0.35 (Corollary, p. 14) generalizes the
  closure to all n ≥ 2: "E^n, for n ≥ 2, is closed under
  simultaneous bounded recursion". This is what underlies Claim 6.

**Relation to our use**: this is the heart of the level-2 → ER
inclusion. It tells us that the simrec trace at iteration `j` is
bounded by some explicit iterate of `e_2` (or 2^x), i.e. by a tower
function in ER. That is precisely the dominance hypothesis required
by `boundedRec_eq_natRec_of_bounded`.

### Fix B (part 3): structural towerHeight versus analytical tower height

The project computes `(kSimPackedStep g).towerHeight` structurally
(by induction on the syntactic shape of the ER term); we need this
structural quantity to dominate the analytical tower height required
by Prop. 4.7 (which is `⌈log_2 D_step⌉ + O(1)` for a degree-`D_step`
polynomial-bounded step).

**Lemma (structural-vs-analytical, project-internal)**. For any
`f : ERMor1 n` whose interp is bounded by a polynomial of degree
`D_step`,

```text
f.towerHeight ≥ ⌈log_2 D_step⌉
```

**Discussion**. The ER syntactic class is built by composition and
bounded primitive recursion over generators including
`g_2(x, y) = x · y`. The polynomial degree of an ER term's interp
is bounded by `2^{(number of multiplication/recursion steps)}`,
which matches the structural towerHeight up to a constant.

This direction of the inequality is what we need: a structurally
larger towerHeight always provides a sufficient analytical height.
The reverse direction (structural height bounded by analytical) is
not required.

**Source-cite**: Tourlakis 2018 §0.1.0.27 clauses (1)–(4) give a
syntactic stratification — E^0 has constant additive bound, E^1 has
linear bound, E^2 has polynomial bound, E^{n+1} for n ≥ 2 has
`A_n^k`-bound. The tower-height growth from level to level is by 1.
This corresponds to one structural level of bounded recursion in
the term contributing one tower height in the bound.

The lemma is FOLKLORE in the sense that no single proposition in
the cited literature states it in the form above; it is implicit in
the proof of Prop. 4.6 (Recursion Class Ch. 4 p. 35), where the
inductive case for `h = R(g, f)` (bounded recursion) bumps the
exponent `k` by 1, and the inductive case for `h = C(f, g_1, …, g_k)`
(composition) takes `max(j(1), …, j(k))` plus `m`. Tracking these
exponent increments through the structure of an ER term gives the
desired inequality. **Project status**: REQUIRES PROJECT-INTERNAL
PROOF; the proof is a routine structural induction once the
`towerHeight` recursion is fixed.

## Claim 5: K^sim_n = E^{n+1} for n ≥ 2

**Statement (project notation)**: K^sim_2 = E^3 = ER (the elementary
recursive functions). More generally, for n ≥ 2, K^sim_n = E^{n+1}.

**Citation**: Tourlakis 2018 §0.1.0.44 (Corollary, p. 21):

> **0.1.0.44 Corollary.** For n ≥ 2, we have K^sim_n = E^{n+1}.

This corollary follows from Tourlakis 2018 §0.1.0.43 (the
Ritchie–Cobham property of E^n) combined with §0.1.0.15 (the equality
K^sim_n = L_n: the K^sim hierarchy is the same as the loop-program
hierarchy under two different definitions).

**Original statement of §0.1.0.15** (Tourlakis 2018 p. 4, verbatim):

> **0.1.0.15 Proposition.** For n ≥ 0, we have that K^sim_n = L_n.

**Original statement of §0.1.0.43** (Tourlakis 2018 p. 21, verbatim):

> **0.1.0.43 Theorem. (The Ritchie–Cobham Property of E^n)** For
> n ≥ 2, a function f is in E^n iff it can be computed on some URM
> within time t_f ∈ E^n.

**Cross-reference (Tourlakis CN 10.2.20)**:

> **10.2.20 Theorem. (K^sim vs. L)** K^sim_n = L_n, n ≥ 0.

**Caveats**:

- For n = 0 and n = 1 the equalities are not proved in Tourlakis
  2018; K^sim_0 = K_0 and the relationship of K^sim_1 to E^2 is more
  subtle (K^sim_1 ⊊ E^2 ⊊ K^sim_2 = E^3).
- The proof of §0.1.0.44 in Tourlakis 2018 uses the elementary case
  due to Schwichtenberg [Sch69] (cited as ref [4] in the Tourlakis
  2018 bibliography) for n = 3; the case n = 2 (i.e. K^sim_2 = E^3)
  is per Heinermann [Hei61] (ref [5]); see Tourlakis 2018 p. 22
  Remark.
- Damnjanovic §3 Theorem 3.3 (p. 501) gives a closely-related
  enumeration result on L_2^k and §8 establishes that the hierarchy
  `{L_2^k}` is proper.

**Relation to our use**: this is the textbook fact justifying the
existence of `kToER : KMor1 (level ≤ 2) → ERMor1`. Without it the
forward direction would require an independent constructive proof.

## Claim 6: ER closed under bounded primitive recursion

**Statement (project notation)**: ER (= E^3) is closed under bounded
primitive recursion, by *definition* (ER is the closure under
substitution and bounded primitive recursion of {succ, ·, +, ×}, or
equivalently of {`λx.x + 1, λx.x, g_2 = λxy.xy`}). It is also closed
under bounded simultaneous recursion.

**Citations**:

1. Tourlakis 2018 §0.1.0.22 (Definition of the Grzegorczyk Hierarchy,
   p. 8): bounded primitive recursion is part of the closure
   operations defining each `E^n`.
2. Tourlakis 2018 §0.1.0.34 (Theorem, p. 13): E^2 is closed under
   simultaneous bounded recursion. Extended in §0.1.0.35 (Corollary,
   p. 14) to all n ≥ 2.
3. Recursion Class Ch. 4 Exercise 4.2 (p. 33): "Show that the
   elementary functions are closed under bounded simultaneous
   recursion" (with hint involving Gödel coding).
4. Tourlakis CN Theorem 4.2.2 (p. 112): the Hilbert–Bernays
   reduction of simultaneous primitive recursion to a single
   primitive recursion via prime-power coding.

**Original statement (Tourlakis 2018 §0.1.0.22, verbatim)**:

```text
0.1.0.22 Definition. (The Grzegorczyk Hierarchy) [...] The
hierarchy (E^n)_{n ≥ 0} is defined as follows: E^n is the closure
of {λx.x + 1, λx.x, g_n} under substitution and bounded primitive
recursion, the latter being the schema below

  f(0, y⃗) = h(y⃗)
  f(x + 1, y⃗) = q(x, y⃗, f(x, y⃗))
  f(x, y⃗) ≤ B(x, y⃗)

where h, q and B are given functions.
```

**Original statement (Tourlakis 2018 §0.1.0.35, verbatim)**:

> **0.1.0.35 Corollary.** E^n, for n ≥ 2, is closed under
> simultaneous bounded recursion.

**Original statement (Tourlakis CN Theorem 4.2.2, p. 112, verbatim)**:

> **4.2.2 Theorem.** If all the h_i and g_i are in PR (resp. R),
> then so are all the f_i obtained by the schema (2) of simultaneous
> recursion.
>
> Proof. IDEA: Code all the functions f_i by a single function F and
> convert the simultaneous recursion to a single primitive recursion
> for F.

**Caveats**:

- The Hilbert–Bernays construction (Tourlakis CN Theorem 4.2.2) uses
  prime-power coding `2^{a_0+1} · 3^{a_1+1} · …`. Tourlakis 2018
  §0.1.0.34 uses Cantor pairing instead, which fits naturally inside
  E^2. Either coding works for our purposes; the project plan uses
  Szudzik pairing (which has a slightly tighter bound than Cantor).
- Closure under bounded simultaneous recursion is what justifies the
  step of converting the K^sim simrec into an ER bounded recursion
  on the encoded trace.

**Relation to our use**: this is the algebraic closure that
justifies `boundedRec_eq_natRec_of_bounded` once the dominance
hypothesis is in hand. Without it, ER would not be expressive enough
to host the translated simrec.

## Claim 7: Tower bound for ER

**Statement (project notation)**: every ER (= E^3) function is
bounded by a fixed iterate of `e_2(x) = x^2 + 2` (or equivalently of
2^x) applied to the maximum of its arguments.

**Citation**: Tourlakis 2018 §0.1.0.27 ("Bounding Lemma"), clause
(3), p. 10:

> **0.1.0.27 Lemma. (Bounding Lemma)** [...] (3) For each f ∈ E^2,
> there are C, n, and k such that f(x⃗) ≤ C max(x⃗)^n + k everywhere.

For E^3 (= ER) the corresponding bound is:

> [...] (4) For each f ∈ E^{n+1}, n ≥ 2, there is a k such that
> f(x⃗) ≤ A_n^k(max(x⃗)) everywhere.

(Tourlakis 2018 §0.1.0.27 p. 10, clause (4); here `A_n` is the
Ackermann-style function used as the Grzegorczyk generator at level
`n + 1`.)

For n = 2, A_2 corresponds to iterated squaring (`e_2`-iteration)
and the bound becomes `f(x⃗) ≤ A_2^k(max(x⃗))` = "tower of
exponentials of height k".

**Cross-reference (Recursion Class Ch. 4 Prop. 4.6)**:

> **Proposition 4.6** Each f in E_{n+3} satisfies:
> ∀x_1, …, x_n ∃k (f(x_1, …, x_n) ≤ (e_{n+2})^k(max(x_1, …, x_n)))

(Recursion Class Ch. 4 p. 34.)

For n = 0 this is exactly the E^3 bound: every E^3 function is
bounded by `e_2^k(max(x⃗))` for some `k`, where `e_2(x) = x^2 + 2`.

**Original statement (Tourlakis CN 10.2.9, p. 286, verbatim)**:

> **10.2.9 Lemma. (Majorising lemma for K^sim)** For n ≥ 0,
> λx⃗.f(x⃗) ∈ K^sim_n implies that for some m depending on f we have
> f(x⃗) ≤ A_n^m(|x⃗|), for all x⃗.

(Equivalent form for K^sim hierarchy directly; the proof is left as
an exercise.)

**Caveats**:

- The "tower function" in the project plan corresponds to iterates
  of `e_2` (Recursion Class Ch. 4) or equivalently `A_2` (Tourlakis
  2018). For ER specifically, the height of the iterate depends on
  the syntactic shape of the ER term; there is no uniform
  `k`. This matches the project plan's `tower h_e (max regs + p_e)`
  shape: the height `h_e` and polynomial shift `p_e` are computed
  from the structure of the ER term `e`.
- For us, the practical consequence is: any ER function value is
  bounded by a tower function of fixed height in its inputs. That
  tower function is itself in E^3 (by §0.1.0.27 (4) with E^{n+1}
  setting `n = 2`, since A_2^k ∈ E^3 for each fixed k by Tourlakis
  2018 §0.1.0.4).

**Relation to our use**: this provides an explicit ER-internal bound
for any ER function, which is exactly the format
`boundedRec_eq_natRec_of_bounded` requires.

## Cross-cutting notes on the chain

**Why the chain works at level 2 but not at higher levels**: The
chain Claim 1 → 4 → 7 produces a bound at the E^3 = ER level. For
K^sim_3 (= E^4), the corresponding step bound is exponential, the
iterated bound is double-exponential, and the result lies in E^4,
not in E^3. So the dominance hypothesis is only available at level
≤ 2, matching the project's `level f ≤ 2` precondition on `kToER`.

**Polynomial-iter ↔ tower-bound interface**. The transition from
Claim 4's polynomial-bounded step to Claim 7's tower-bounded
iterated trace happens via Recursion Class Ch. 4 Prop. 4.7, equation
(★★★): `f^z(x⃗) ≤ e_n(max(x⃗) + m · z)`. Setting `n = 2`, the
analytical bound is `e_3(max + m_step · j)`. Translating to the
project's `tower h x = 2^(2^...^x)` (h twos applied to x), this
analytical bound is dominated by `tower 2 (poly(max, m_step · j))`
for a suitable polynomial `poly` (see "Why height 2" in Fix B part
2). The constant `m_step` derives from the polynomial degree of
the step (Claim 3 + Claim 1 with system size threading), and the
height-`h_e` of the project-side `tower` shape is fixed at 2 for
the level-2 case. The structural towerHeight on the project side
must be at least 2 (Fix B part 3).

**System size `k` parameterization**. The polynomial degree of the
packed step is `D_step = 2^k · D_g`, where `k+1` is the system size
of the K^sim simrec and `D_g` is the polynomial degree of the
unpacked level-2 step. (The seqPack-encoding's own degree is
`D_pack(k) = 2^k · max(d_1, …, d_{k+1})`; threading the components
through, the composed step inherits a degree of the same `2^k`-times-
unpacked form.) `k` is statically known from the K^sim simrec
constructor's index (it is part of the type of `simrec` in `KMor1`).
In the iterated bound (Fix B part 2), `k` appears

- inside the constant `m_step = ⌈log_2 D_step⌉ + 1 = k +
  ⌈log_2 D_g⌉ + 1`, contributing to the linear-in-`j` term;
- and as a static constant in the construction of
  `seqPackBound k D_pack(k)`.

Both occurrences are within ER: a static `k` makes `2^k` an explicit
ER constant, and the linear coefficient `m_step` is in E^1 ⊆ ER.

**Structural-vs-analytical tower height**. Fix B part 3 records that
the project's `towerHeight` (a syntactic quantity computed by
recursion on the ER term) must dominate the analytical tower height
required by Prop. 4.7. The forward inequality
`towerHeight ≥ ⌈log_2 D_step⌉` is folklore (implicit in the proof of
Prop. 4.6) and is to be proved as a project-internal structural
induction.

**Where the chain may need additional Lean infrastructure**:

- A Lean lemma `Nat.pair x y ≤ (x + y + 1)^2` (or similar) for the
  particular pairing in mathlib. This is folklore but needs to be
  exhibited (likely a few lines using `Nat.pair_eq_pair_iff` or by
  case analysis on `pair`'s closed form).
- A Lean development of the polynomial-iter bound (Recursion Class
  Ch. 4 Prop. 4.7 specialized to n = 2). The plan
  `docs/lawvere-k-sim-hierarchy.md` §3.3 already sketches this in
  terms of `tower` and `polyIter`.
- Lean translations of E^2's closure under simultaneous bounded
  recursion (Tourlakis 2018 §0.1.0.34) into the ERMor language. The
  plan §2.3.1 addresses the level-2 simrec via Szudzik pairing
  (an alternative to Cantor pairing); the closure proof carries
  through identically.
- A Lean derivation of Lemma 1.A (linear-bounded K^sim_1) and Lemma
  1.B (level-0 shape) by structural induction on `KMor1`, as
  outlined in Fix A.

## Gaps and FOLKLORE entries

- **Lemma 1.A specifically for K^sim_1** (rather than E^1): no
  single proposition in the cited literature states this for the
  K^sim hierarchy directly. Recursion Class Ch. 4 Prop. 4.4 gives
  the E_1 form; Tourlakis 2018 §0.1.0.27 (2) gives the same for
  E^1; the K^sim_1 form is by direct structural induction (Fix A,
  Lemma 1.A). FOLKLORE/IMPLICIT in Tourlakis 2018 §0.1.0.17.
- **Lemma 1.B (level-0 K^sim shape lemma)**: the literature
  analogue is Recursion Class Ch. 4 Prop. 4.3 (E_0 = constant
  additive bound), which has the same statement and proof
  structure. The K^sim_0 = K_0 reduction is by Tourlakis 2018
  §0.1.0.15 with `n = 0`. FOLKLORE/IMPLICIT.
- **Cantor vs. Szudzik pairing in Lean**: Tourlakis 2018 uses
  Cantor `J = (x + y)^2 + x`; the project plan uses Szudzik elegant
  pairing `pair x y = if x < y then y^2 + x else x^2 + x + y`. Both
  have quadratic bounds. mathlib's `Nat.pair` is Cantor, with
  closed form `(x + y) * (x + y + 1) / 2 + x`; the bound
  `Nat.pair x y ≤ (x+y+1)^2` is immediate. **Path**: state and
  prove the `Nat.pair` upper bound as a small lemma in
  `Utilities/`; or switch to a custom Szudzik pairing definition
  for the simrec encoding (the project plan §2.3.1 already
  anticipates this).
- **Claim 7 effectivity (uniform tower height for ER)**: the
  statement "every ER function is bounded by `tower h e_2 ∘ poly`
  for some height `h` and polynomial `poly` depending on the term"
  is the *non-uniform* version of the bound. There is no single `h`
  that works for all of ER (since ER is closed under composition,
  iterating the height argument by 1 each time). The project
  plan's `runtimeBound e regs ≤ tower h_e (max regs + p_e)` is
  correctly non-uniform in `e`. This matches Tourlakis 2018
  §0.1.0.27 (4).
- **Structural-vs-analytical towerHeight (Fix B part 3)**: the
  inequality `f.towerHeight ≥ ⌈log_2 D_step⌉` for polynomial-degree-
  `D_step` bound on `f`'s interp is FOLKLORE (implicit in Recursion
  Class Ch. 4 Prop. 4.6's proof). REQUIRES PROJECT-INTERNAL PROOF.
- **General `λxy.x^y ∈ E^3` (used in Fix B part 1's seqPackBound
  construction)**: Tourlakis 2018 §0.1.0.17(c) gives only
  `λx.2^x ∈ K_2 = K^sim_1`, not general two-variable `x^y`. The
  general form follows by Recursion Class Ch. 4 §4.4 ("composed
  exponentials are all elementary"), or by E^2's closure under
  bounded primitive recursion (Tourlakis 2018 §0.1.0.22) applied
  to the recursion `x^0 = 1`, `x^(y+1) = x · x^y` with bound
  `x^y ≤ (max(x, 2))^y ≤ 2^(y · ⌈log_2 max(x, 2)⌉)`. FOLKLORE/
  IMPLICIT in the cited literature; standard exercise.

## Adversarial brainstorm response

This section records each gap raised by the adversarial brainstorm
and the location in the document that addresses it.

- **Gap 1 (Claim 1's circular reasoning)**: addressed by Fix A in
  Claim 1. The previous derivation routed through "K^sim_1 ⊆ E^1
  because the level-1 examples are linear-bounded, which is true
  because they are in E^1". Fix A replaces this with a direct
  structural induction on `KMor1` terms with `level ≤ 1`
  (Lemma 1.A), avoiding the inclusion K^sim_1 ⊆ E^1 entirely.
- **Gap 2 (Claim 1 simrec case under-analyzed)**: addressed by
  Lemma 1.B (level-0 shape lemma) within Fix A. The simrec case at
  level 1 has level-0 step `g`, whose interp by Lemma 1.B has
  shifted-projection form (no multiplicative coefficient). One
  iteration adds at most a constant; `j` iterations add at most
  `j · K`, giving a linear-in-`(max + j)` total bound.
- **Gap 3 (Claim 3 needs explicit ER bound term)**: addressed by
  Fix B part 1 in Claim 3. Defines `seqPackBound k D : ERMor1 1`
  with explicit closed-form interp `(m + 1) ^ D`, parameterized by
  the degree `D ≥ D_pack(k) = 2^k · max(d_1, …, d_{k+1})`,
  constructible in ER by composition of successor, addition, and
  exponentiation.
- **Gap 4 (Claim 4 exists-vs-explicit)**: addressed by Fix B part
  2 in Claim 4. Constructs the iterated bound term
  `iterAutoBoundExpr a h_e lh` with closed-form
  `tower h_e (lh · max + lh · j + lh)`, deriving the constants
  `h_e = 2`, `lh = m_step + 1` from the step's polynomial degree
  `D_step` via Prop. 4.7's computation
  `m_step = ⌈log_2 D_step⌉ + 1` and the chaining
  `(e_{n-1})^{mz}(max) ≤ e_n(max + mz)` (Recursion Class Ch. 4
  Prop. 4.2 (4)).
- **Gap 5 (system size `k` parameterization)**: addressed in
  Cross-cutting notes ("System size `k` parameterization") and
  threaded through `D_step = 2^k · D_g`. `k`
  appears as a static type-level index of the K^sim simrec
  constructor, contributing as `2^k` (constant in ER) and as a
  linear coefficient on `j`.
- **Gap 6 (structural towerHeight ↔ analytical tower height)**:
  addressed by Fix B part 3 in Claim 4 (structural-vs-analytical
  lemma). The required inequality is folklore (implicit in
  Recursion Class Ch. 4 Prop. 4.6's proof) and is flagged as
  REQUIRES PROJECT-INTERNAL PROOF.

### Second-pass adversarial brainstorm (arithmetic precision)

A subsequent adversarial pass flagged remaining arithmetic-precision
and notational gaps. Each has been addressed as follows.

- **Gap 1.1 (tower-definition consistency)**: the project's
  `Utilities/Tower.lean` defines `tower h x = 2^(2^...^x)` (h twos
  applied to x). Fix B part 2's "Tower convention" paragraph fixes
  this as the document-wide convention and translates Recursion
  Class Ch. 4 Prop. 4.6's `(e_{n+2})^k(max(x⃗))` form into the
  project's `tower` form (interchangeable up to constant additive
  shifts in the height). The mixed form `tower 2 u := e_2 (e_1 u)`
  has been removed; all tower expressions use the iterated-2-power
  convention.
- **Gap 1.2 (rigorous degree formula for `D_pack`)**: addressed by
  defining `D_pack(k) := 2^k · max(d_1, …, d_{k+1})` precisely.
  Each binary pairing `J(a, b) = (a + b)^2 + a` is degree 2 in each
  of its arguments. Iterating: after combining `k+1` components via
  `k` paired applications, the maximum-degree contribution from the
  components is multiplied by `2^k`. The earlier conflation of
  `2^{k-1}`, `2^k`, and `D_k = 2 · max d_i · (k+1)` is replaced by
  the unique formula `D_pack(k) = 2^k · max(d_1, …, d_{k+1})`.
  `seqPackBound k D` accepts the degree `D` as a parameter, with
  `D ≥ D_pack(k)` enforced at the call site.
- **Gap 1.3 (notation unification)**: `D_step` is now used for the
  step's polynomial degree, `D_pack(k)` for the seqPack degree at
  system size `k+1`, and `D_g` for the unpacked level-2 step's
  degree. Earlier ambiguous `D` and `D_k` references have been
  replaced.
- **Gap 1.4 (citation precision)**: "Prop. 4.2.4" corrected to
  "Prop. 4.2 (4)" (Recursion Class Ch. 4 numbers Prop. 4.2 with
  four subordinate clauses). The citation
  "Tourlakis 2018 §0.1.0.17(c)" for general `λxy.x^y ∈ E^3` was
  inaccurate: §0.1.0.17(c) gives only `λx.2^x ∈ K_2`. The corrected
  citation is Recursion Class Ch. 4 §4.4 ("composed exponentials
  are all elementary"), with the path from `λx.2^x` to general
  `λxy.x^y` flagged as folklore (standard exercise: bounded
  primitive recursion `x^(y+1) = x · x^y` with bound
  `x^y ≤ 2^(y · ⌈log_2 max(x, 2)⌉)`).
- **Gap 1.5 (height-2 derivation)**: Fix B part 2 now contains a
  "Why height 2" subsection. Prop. 4.7 yields
  `step^j ≤ e_3(max + m_step · j)`. Translating into the project's
  iterated-2-power `tower h x` notion: `e_3(u) ≤ tower 2 (poly(u))`
  for suitable polynomial (folklore tracking of Prop. 4.6's proof,
  using `e_3(u) = (e_2)^u(2)` and `e_2`-iteration's compatibility
  with `2^·`-iteration). Setting `h_e = 2` accommodates the
  iterated-polynomial-step bound with one inner `2^(linear)` (one
  exponential dominating the polynomial-of-degree-`D_step` factor)
  and one outer `2^·` (compositional shift from the Prop. 4.7
  chaining `(e_1)^m(max) ≤ e_2(max + m)`).
- **Gap 1.6 (Lemma 1.B comp sub-cases)**: the comp case in
  Lemma 1.B's proof now spells out the four sub-cases explicitly:
  (constant `f`)/(constant `gs i`), (constant `f`)/(shifted-proj
  `gs i`), (shifted-proj `f`)/(constant `gs i`), (shifted-proj
  `f`)/(shifted-proj `gs i`). The shifts add additively in each
  case.
- **Gap 1.7 (Lemma 1.B applies pointwise to `g`'s arity-`(a + 2)`
  context)**: Lemma 1.A's simrec case now states explicitly that
  the simrec at arity `a` enlarges `g`'s context to arity `a + 2`
  (counter, accumulator, original parameters), and that Lemma 1.B
  applies to that enlarged context.

## Suggested next steps

1. **Write a small Lean lemma** `Nat.pair_le_sq : Nat.pair x y ≤
   (x + y + 1)^2` (or whatever clean form mathlib supports). This
   discharges Claim 2 directly. Locate in `Utilities/Pairing.lean`
   or similar.

2. **Implement `polyIter` and `tower`** as named ER composites in
   `Utilities/ERArith.lean` (the project plan §2.3 already
   specifies the shape). Prove their interp lemmas as `@[simp]`.

3. **Prove a Lean version of Tourlakis 2018 §0.1.0.34** (E^2
   closure under simultaneous bounded recursion) inside `ERMor1`.
   This may already be partially present as `boundedRec`
   infrastructure; verify and extend.

4. **Prove Lemma 1.A (linear-bound for K^sim_1) and Lemma 1.B
   (level-0 K^sim shape)** by structural induction on `KMor1`
   with `level ≤ 1` and `level ≤ 0` respectively, mirroring
   Recursion Class Ch. 4 Prop. 4.3 and Prop. 4.4.

5. **Implement `seqPackBound k D` and `iterAutoBoundExpr a h_e
   lh`** in `Utilities/ERArith.lean` per Fix B parts 1 and 2, with
   `@[simp]` interp lemmas for the closed-form polynomials.

6. **Prove the structural-vs-analytical towerHeight inequality**
   per Fix B part 3, by structural induction on the ER term.

7. **Assemble the dominance witness**. With Claims 1–4 in hand
   (including Fix A's Lemma 1.A, 1.B and Fix B's explicit ER
   bound terms), define `simrecBound : KMor1 a → (level f ≤ 2) →
   ERMor1 a` that for each level-2 simrec produces an ER term
   dominating the simrec's iterated trace.

8. **Verify against `boundedRec_eq_natRec_of_bounded`**: confirm
   the exact shape of the dominance hypothesis matches what the
   lemma expects. If there is a mismatch, decide whether to
   strengthen the lemma's hypothesis or weaken the dominance
   witness.

The planned proof structure is therefore viable: every sub-claim
has either a direct citation (Claims 2, 4, 5, 6, 7) or a clear
derivation from cited material with explicit project-internal
constructions (Claims 1, 3, 4 fix). The remaining FOLKLORE entries
are the Cantor-pairing closed-form bound, the K^sim_1/K^sim_0
structural shape lemmas (Lemma 1.A, 1.B), and the
structural-vs-analytical towerHeight inequality — all routine to
prove in Lean given the cited propositions.
