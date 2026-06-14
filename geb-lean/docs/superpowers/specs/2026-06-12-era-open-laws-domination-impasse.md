# Exponential domination and the recovery kernel — Era open-laws Phase 4

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [1 The obligation](#1-the-obligation)
- [2 Why it resists: the witness is forced and needs subtraction](#2-why-it-resists-the-witness-is-forced-and-needs-subtraction)
- [3 Empirical confirmation: base derives, the doubling step blocks](#3-empirical-confirmation-base-derives-the-doubling-step-blocks)
- [4 Routes considered and excluded](#4-routes-considered-and-excluded)
- [5 What is delivered](#5-what-is-delivered)
- [6 Update (2026-06-13): truncated subtraction restored](#6-update-2026-06-13-truncated-subtraction-restored)
- [7 The obstruction sharpened: the recovery kernel](#7-the-obstruction-sharpened-the-recovery-kernel)
- [8 Reframing: the difficulty is minimization cost](#8-reframing-the-difficulty-is-minimization-cost)

<!-- END doctoc -->

Status report for the open obligation gating Phase 4 of the
Era open-laws workstream
(`docs/superpowers/specs/2026-06-12-era-open-laws-design.md`
§7.3, §9). Phases 0–3 and the `esubAt` template (Phase 4a Tasks
4a.1–4a.2) are complete, committed, and axiom-clean. Phase 4a
Task 4a.3 (exponential domination) is the staged-exit point
reached here; the seven remaining open-law deliverables depend
on it.

## 1 The obligation

The two shape-decided template laws `esubAt_of_lt` and
`esubAt_of_add` discharge every remainder site in the
subtraction, multiplication, division, and exponentiation
derivations, but `esubAt_of_add` consumes a domination
hypothesis

```text
hdom : Derivable eraDefs ⟨eexp2 e, u +ᵉ .succ p⟩
```

for an explicit witness term `p`. The first consumer is
`sub_zero` (`u ∸ 0`), whose canonical exponent is `e = u +ᵉ 0`
and whose dividend is `u`, so the required instance is

```text
2^u = u +ᵉ .succ p          (equivalently, 2^u > u, open u).
```

Deriving this family of instances for open `u` is the
obligation. No member with a non-closed `u` has a verified
derivation.

## 2 Why it resists: the witness is forced and needs subtraction

The equation `2^u = u +ᵉ .succ p` determines `p` uniquely in the
standard model: `p = 2^u − u − 1`. The recursion of this value
is purely additive,

```text
p(0) = 0,        p(S u) = p(u) +ᵉ p(u) +ᵉ u
```

(from `2^{S u} = 2·2^u`), so no `∸` appears in the recurrence.
But the calculus has no facility to introduce a new function
symbol with this recurrence: `eraDefs` is fixed at the seven
equations, and the user has excluded extending it. The witness
must therefore be written as an explicit term over
`{+, mod, 2^x}`. The unique closed-form basis term with value
`2^u − u − 1` is

```text
eexp2 u ∸ᵉ .succ u,
```

which uses the truncated subtraction `∸` whose recursion laws
are precisely the Phase-4 deliverables that domination is needed
to prove. This is the circularity recorded in the spec §8.

## 3 Empirical confirmation: base derives, the doubling step blocks

Set domination up as a `uniq` induction on `x`:

```text
D(x) :  Derivable eraDefs ⟨eexp2 x, x +ᵉ .succ (eexp2 x ∸ᵉ .succ x)⟩
```

taking the explicit witness `T(x) := eexp2 x ∸ᵉ .succ x`.

- Base (`x = 0`) derives. Confirmed in Lean against the
  committed file: `eexp2 0 ∸ᵉ S 0` reduces to `S 0 ∸ᵉ S 0`
  (`esub_congr` on `exp2_zero`) and then to `0` (`sub_self`),
  so the right side is `0 +ᵉ S 0 = 1 = eexp2 0` by `zero_add`
  and `exp2_zero`.
- The `uniq` F-step premise is
  `⟨eexp2 (S x), eexp2 x +ᵉ eexp2 x⟩` with step functional
  `H := .var 1 +ᵉ .var 1`; this is exactly `derivable_exp2_succ`.
- The `uniq` G-step premise reduces to

  ```text
  S x +ᵉ S (eexp2 (S x) ∸ᵉ S (S x))
      = (x +ᵉ S T(x)) +ᵉ (x +ᵉ S T(x)),
  ```

  whose object-level proof requires the esub doubling recursion

  ```text
  eexp2 (S x) ∸ᵉ S (S x)
      = (eexp2 x ∸ᵉ S x) +ᵉ (eexp2 x ∸ᵉ S x) +ᵉ x.
  ```

  Evaluating either `esub` on the left or right via
  `esubAt_of_add` requires the domination instances
  `2^{S x} = S (S x) +ᵉ S q` and `2^x = S x +ᵉ S r` — i.e.
  domination again. The circle closes on the G-step.

So the obstruction is localized to a single premise, and that
premise is the truncated-subtraction doubling law, which is not
derivable ahead of domination.

## 4 Routes considered and excluded

- Direct `uniq` on the domination equation with an additive
  witness recurrence: the witness has no basis-term closed form
  without `∸` (§2); spec §8, first item.
- `uniq` on `u %ᵉ eexp2 u = u`: the step is a
  mod-of-successor-dividend equation outside the three mod
  axioms; spec §8, second item.
- Two-variable domination by `uniq`: the base stays open in the
  second variable; spec §8, third item.
- Goodstein's recovery equation (17) `a +ᵉ (b ∸ᵉ a) = b +ᵉ (a ∸ᵉ b)`
  as a primary route: its derivation consumes `b ∸ 0 = b` and
  `S a ∸ S b = a ∸ b`, both Phase-4 targets needing domination,
  and introduces an auxiliary recursive function with no
  counterpart under fixed `eraDefs`; spec §7.7, §8 fourth item.
- Exponent-stability (`esubAt e u v = esubAt e' u v`) to push
  the exponent above any threshold: proving stability evaluates
  the `esub` at both exponents, each needing its own domination;
  the binding constraint (smallest exponent, `e ≈ u` for
  `sub_zero`) is unchanged.

## 5 What is delivered

Committed on `feat/era-open-laws`, all axioms contained in
`{propext, Quot.sound}`:

- Phase 0: `derivable_zero_add`, `Derivable.ext_succ`
  (Goodstein E₃).
- Phase 1: `derivable_succ_add`, `derivable_add_comm`,
  `derivable_add_assoc`.
- Phase 2: `derivable_zero_mod`, `derivable_mod_self`.
- Phase 3: `derivable_sub_self`, `derivable_zero_sub`, and the
  four unconditional deliverables `derivable_pred_zero`,
  `derivable_mul_zero`, `derivable_div_zero`,
  `derivable_zero_div` (plus `derivable_edmul_zero`).
- Phase 4a template: `esubAt`, `esub_eq_esubAt`,
  `derivable_esubAt_of_lt`, `derivable_esubAt_of_add`.

Four of the eleven §4 deliverables are theorems. The template
laws reduce each of the remaining seven to domination instances,
so domination is the single obligation standing between the
current state and the full pre-reduction API.

## 6 Update (2026-06-13): truncated subtraction restored

The decision taken was a variant of option 2: restore truncated
subtraction as a fourth basis primitive with its four recursion
axioms (spec §9a), rather than add a domination axiom. This
delivered the four subtraction-cluster laws as axiom instances
and Goodstein's subtraction development (`sub_succ_succ`,
`sub_self`, `zero_sub`, `add_sub_cancel`) cleanly, plus the
`∸`-order algebra `sub_add`, `add_sub_cancel_left`,
`add_sub_add_left`, `self_sub_add`, `one_le_two_pow`.

## 7 The obstruction sharpened: the recovery kernel

With `∸` primitive, the order algebra reduces the domination
obstruction to a single named equation, the **recovery equation**

```text
b ∸ c = 0  →  b +ᵉ (c ∸ᵉ b) = c        (b ≤ c ⟹ c = b + (c − b)),
```

equivalently first-argument monotonicity of `∸`
(`b ≤ Sb ⟹ b ∸ c ≤ Sb ∸ c`), equivalently Goodstein's recovery
equation (17) `a + (b∸a) = b + (a∸b)`, equivalently
commutativity of `max(a,b) = a + (b∸a)`. Four independent attacks
(min/max closed forms with `min(a,b) = a ∸ (a∸b)`; the
`min + (a∸b) = a` induction; the power-specific recovery by
`uniq`; antisymmetry of the order) each reduce back to recovery.

Recovery is not reachable from elementary `∸`-algebra: `S a ∸ᵉ b`
has no equational reduction (it requires the case split
`a < b` / `a ≥ b`, inexpressible in the logic-free calculus).
Goodstein's only route to (17) telescopes
`f(a,b) = f(a∸1, b∸1) + sg(a+b)` against the bounded sum
`φ(n,a,b) = Σ_{k<n} sg((a∸k)+(b∸k)) = min(n, max(a,b))` and uses
φ's manifest symmetry. While `min`, `max`, and `sg` are each
closed terms over the basis, deriving the **equation** (17) this
way still requires φ's telescoping recursion, whose own
derivation hits the same first-argument-successor wall — the
Marchenkov-`F(a,b)`-level machinery, and the original impasse one
layer in.

## 8 Reframing: the difficulty is minimization cost

The eleven open laws are exactly the recursion axioms of the
richer pre-reduction basis: the four `∸` laws are `tsub`'s
axioms (now restored), and `mul_zero`/`mul_succ`,
`pow_zero`/`pow_succ`, `div_zero`/`zero_div`/`div_succ` are the
recursion axioms of primitive `·`, `^`, `⌊/⌋` in the five-element
basis at `daab65a9`. Deriving them over `{+, mod, 2^x}` produces
no new mathematical content; it re-derives, over a smaller basis,
equations that were axioms when those operations were primitive.
The only genuinely new content the minimal basis would buy is the
redundancy/expressibility theorems — which are the
Marchenkov/[PSS26] result, already established at the function
level in the literature, and which themselves need domination.

"Logic-free" requires a *finite* basis with finitely many
defining equations, not a *minimal* one. The recommendation is
therefore to adopt a convenient finite basis — restore `·`,
`⌊/⌋`, `^` as primitives alongside `{+, mod, 2^x, ∸}` — under
which all eleven laws are axioms, the impasse dissolves, and the
file simplifies (the Mazzanti-formula derivation chain becomes
unnecessary). The minimal-basis result is then cited as a
function-level expressibility theorem (Marchenkov→PSS), optionally
accompanied by object-level redundancy theorems where tractable.
