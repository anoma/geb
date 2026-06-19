# Era recovery and E1–E5 — deferred-workstream context

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [1 Purpose and how to use this note](#1-purpose-and-how-to-use-this-note)
- [2 What E1–E5 are](#2-what-e1e5-are)
- [3 What "recovery" is](#3-what-recovery-is)
- [4 Semantic versus object level, and the link to completeness](#4-semantic-versus-object-level-and-the-link-to-completeness)
- [5 Status: done, verified, blocked](#5-status-done-verified-blocked)
- [6 The verified reduction: recovery from succ_sub_split](#6-the-verified-reduction-recovery-from-succ_sub_split)
- [7 The resolution: succ_sub_split needs Goodstein's φ](#7-the-resolution-succ_sub_split-needs-goodsteins-%CF%86)
- [8 Discarded leads](#8-discarded-leads)
- [9 Literature map](#9-literature-map)
- [10 Related documents](#10-related-documents)
- [11 Where a future brainstorm should start](#11-where-a-future-brainstorm-should-start)
- [12 Design-space synthesis (2026-06-19)](#12-design-space-synthesis-2026-06-19)
  - [12.1 Three formulations of ERA](#121-three-formulations-of-era)
  - [12.2 Redundancy versus recovery](#122-redundancy-versus-recovery)
  - [12.3 Semantic versus object level — what is and is not proved](#123-semantic-versus-object-level--what-is-and-is-not-proved)
  - [12.4 φ in full, and why not `max`](#124-%CF%86-in-full-and-why-not-max)
  - [12.5 Designing a maximally-expressive finite basis (#3)](#125-designing-a-maximally-expressive-finite-basis-3)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

## 1 Purpose and how to use this note

This note consolidates the context for the deferred object-level
workstream on `Era.lean`: the redundancy theorems E1–E5 and the
"recovery" lemma they all rest on. It is written so a future
brainstorm can begin already knowing what the problem is, what has
been proven, where the obstruction lies, and what the resolution
appears to be — without rediscovering the analysis.

It is not a spec. The deferred workstream still needs its own
brainstorm, spec, and plan. This note is the seed for that
brainstorm. The companion forward workstream — semantic
completeness of the basis — has its own spec at
`docs/superpowers/specs/2026-06-14-era-completeness-bounded-sum-design.md`;
§ 4 below explains how the two relate.

## 2 What E1–E5 are

`Era.lean` carries a seven-operation basis
`{add, mod, pow2, tsub, mul, div, pow}`. Only `{add, mod, pow2}` are
the genuine minimal generators (Prunescu–Sauras-Altuzarra–Shunia,
arXiv:2505.23787). The other four — `tsub`, `mul`, `div`, `pow` —
are convenience operations: each is redundant, definable from the
three generators.

E1–E5 are the five redundancy theorems that establish this
redundancy inside the equation calculus, as `Derivable eraDefs`
equations. For example E1 is

```text
x ∸ᵉ y = subFormula x y        -- subFormula uses only {add, mod, pow2}
```

so truncated subtraction provably equals an encoding over the bare
generators. The five encodings (`subFormula`, `edmul`,
`divFormula`, `mulFormula`, `powFormula`) and their `ℕ`-level
correctness identities already exist in `Era.lean`; the missing
content is the object-level (`Derivable`) lifting. The full list,
the encodings, and the method are in
`docs/superpowers/specs/2026-06-13-era-rich-basis-design.md` § 5–§ 6.

## 3 What "recovery" is

Every E1–E5 proof depends on a single order-arithmetic lemma. The
name is Goodstein's: his recovery equation (Goodstein 1954,
equation (17)) is

```text
a + (b ∸ a) = b + (a ∸ b)      -- both sides equal max(a, b)
```

equivalently the conditional `b ≤ c → b + (c ∸ b) = c`, which
"recovers" `c` from `b` and the truncated difference `c ∸ b`. It is
the basic fact that lets truncated subtraction, `mod`, and division
be manipulated in the calculus; the E1–E5 proofs use it to
discharge their domination and division-with-remainder side
conditions.

Recovery is awkward precisely because the calculus is logic-free:
`Derivable` proves only universally-quantified equations, with no
implications or inequalities, under a single-variable uniqueness
rule (`uniq`) plus `ext_succ`. An order fact such as recovery has
no conditional form to assert; its unconditional form forces the
indicator term `1 ∸ (b ∸ a)`, which mixes a minuend-variable
occurrence with a subtrahend-variable occurrence. Basis `∸`
recurses only on its subtrahend (`x ∸ S y = (x ∸ y) ∸ 1`); there is
no recursion for successor-on-the-minuend (`S a ∸ b`). So no single
`uniq` on `a` or on `b` closes recovery — the obstruction first
recorded as M2 in the rich-basis spec.

## 4 Semantic versus object level, and the link to completeness

`Era` exists at two levels, and the recovery workstream and the
completeness workstream sit on opposite sides of the divide.

- Semantic level (`Tm.eval`): which `ℕ → ℕ` functions the terms
  denote. The completeness spec lives here. It proves the basis
  denotes exactly the Kalmár elementary functions `E³`, and needs
  bounded summation as a basis term with an `eval` lemma.
- Object level (`Derivable`): which equations the logic-free
  calculus proves. Recovery and E1–E5 live here. They need
  Goodstein's bounded-sum auxiliary `φ` to derive an equation.

The two are independent at the proof level: completeness never
needs recovery, and recovery never needs completeness. But they are
siblings through one shared engine — bounded summation. Completeness
builds the semantic version (`eraBSum` with its `eval` lemma);
recovery needs the object-level version (`φ` with a `Derivable`
recursion). The strongest form of E1–E5 — redundancy over the bare
three generators — has, as its hard core, the object-level twin of
exactly the bounded-sum engine the completeness spec builds
semantically. Building the semantic engine first is lower-risk and
would leave the object-level version better understood.

## 5 Status: done, verified, blocked

Done in `Era.lean` (object level): Goodstein's order algebra
equations (1)–(9) (`derivable_sub_succ_succ`, `derivable_sub_self`,
`derivable_zero_sub`, `derivable_add_sub_cancel`,
`derivable_add_sub_cancel_left`, `derivable_add_sub_add_left`,
`derivable_sub_add`, and the additive algebra). The `esubAt`
subtraction template and partial domination
(`derivable_one_le_two_pow`) are present. Only Goodstein's (17) is
missing from his pp. 249–254 development.

Verified this session (see § 6): recovery reduces, in Lean and
axiom-clean, to the single lemma

```text
succ_sub_split :  S a ∸ b = (a ∸ b) + (1 ∸ (b ∸ a))
```

Blocked: `succ_sub_split` itself. Its own `uniq` step is
self-referential (the step on either variable reproduces the
lemma), so it is not single-`uniq`-derivable; it needs Goodstein's
`φ` (§ 7).

## 6 The verified reduction: recovery from succ_sub_split

The reduction was proved by `uniq` on `a` with the indicator step
functional `H := prev + (1 ∸ (b ∸ a))`. Under this `H`, `stepF`
reduces to the derivable helper `S(c ∸ 1) = c + (1 ∸ c)`, and
`stepG` is exactly `succ_sub_split`. So recovery follows from
`succ_sub_split` and nothing else.

The proof below compiled against `Era.lean` with axioms
`propext`, `Quot.sound` only (no `sorryAx`, no `Classical.choice`).
It was produced as a throwaway spike and is preserved here rather
than committed as live code; re-home it into `Era.lean` when the
workstream resumes.

```lean
import GebLean.Era

namespace EraRecovery

open Era

/-- Helper: `S (c ∸ 1) = c + (1 ∸ c)`.  By `ext_succ`: at `0`,
`S(0∸1)=1=0+(1∸0)`; at `S c`, `S(Sc∸1)=Sc` and `Sc+(1∸Sc)=Sc+0=Sc`
(using `1 ∸ S c = 0`). -/
theorem derivable_succ_pred_eq {n : Nat} (c : ETm n) :
    Derivable eraDefs ⟨.succ (c ∸ᵉ one), c +ᵉ (one ∸ᵉ c)⟩ := by
  have base : Derivable eraDefs
      ⟨.succ ((.var 0 : ETm 1) ∸ᵉ one), (.var 0) +ᵉ (one ∸ᵉ (.var 0))⟩ := by
    refine Derivable.ext_succ ?h0 ?hS
    case h0 =>
      have hl : Derivable eraDefs ⟨.succ ((.zero : ETm 0) ∸ᵉ one), one⟩ :=
        Derivable.succ_congr derivable_pred_zero
      have hr : Derivable eraDefs ⟨(.zero : ETm 0) +ᵉ (one ∸ᵉ .zero), one⟩ :=
        (derivable_zero_add (one ∸ᵉ .zero)).trans (derivable_sub_zero one)
      have h := hl.trans hr.symm
      simp only [Tm.subst, etsub_subst, eadd_subst] at h ⊢
      exact h
    case hS =>
      have hone_sub_succ : Derivable eraDefs ⟨one ∸ᵉ .succ (.var 0 : ETm 1), .zero⟩ :=
        (derivable_sub_succ_succ (.zero) (.var 0)).trans (derivable_zero_sub (.var 0))
      have hl : Derivable eraDefs ⟨.succ (.succ (.var 0 : ETm 1) ∸ᵉ one), .succ (.var 0)⟩ :=
        Derivable.succ_congr (derivable_pred_succ (.var 0))
      have hr : Derivable eraDefs
          ⟨.succ (.var 0 : ETm 1) +ᵉ (one ∸ᵉ .succ (.var 0)), .succ (.var 0)⟩ :=
        (eadd_congr (.refl (.succ (.var 0 : ETm 1))) hone_sub_succ).trans
          (derivable_add_zero (.succ (.var 0)))
      have h := hl.trans hr.symm
      simp only [Tm.subst, etsub_subst, eadd_subst] at h ⊢
      exact h
  have h := base.inst (fun _ => c)
  simp only [Tm.subst, etsub_subst, eadd_subst] at h
  exact h

/-- Recovery (Goodstein 1954 (17)) from `succ_sub_split`, by `uniq` on the
first argument with the indicator step functional `H := prev + (1 ∸ (b ∸ a))`. -/
theorem recovery_of_succ_sub_split
    (hsplit : ∀ {n : Nat} (a b : ETm n),
      Derivable eraDefs ⟨.succ a ∸ᵉ b, (a ∸ᵉ b) +ᵉ (one ∸ᵉ (b ∸ᵉ a))⟩)
    {n : Nat} (a b : ETm n) :
    Derivable eraDefs ⟨a +ᵉ (b ∸ᵉ a), b +ᵉ (a ∸ᵉ b)⟩ := by
  have base : Derivable eraDefs
      ⟨(.var 0 : ETm 2) +ᵉ ((.var 1) ∸ᵉ (.var 0)),
        (.var 1) +ᵉ ((.var 0) ∸ᵉ (.var 1))⟩ := by
    refine Derivable.uniq
      (H := (.var 1) +ᵉ (one ∸ᵉ ((.var 2) ∸ᵉ (.var 0)))) ?base ?stepF ?stepG
    case base =>
      have hl : Derivable eraDefs ⟨(.zero : ETm 1) +ᵉ ((.var 0) ∸ᵉ .zero), .var 0⟩ :=
        (derivable_zero_add ((.var 0) ∸ᵉ .zero)).trans (derivable_sub_zero (.var 0))
      have hr : Derivable eraDefs ⟨(.var 0 : ETm 1) +ᵉ (.zero ∸ᵉ (.var 0)), .var 0⟩ :=
        (eadd_congr (.refl (.var 0)) (derivable_zero_sub (.var 0))).trans
          (derivable_add_zero (.var 0))
      have h := hl.trans hr.symm
      simp only [Tm.subst, etsub_subst, eadd_subst, sub0, fcons] at h ⊢
      exact h
    case stepF =>
      have hl : Derivable eraDefs
          ⟨.succ (.var 0 : ETm 2) +ᵉ ((.var 1) ∸ᵉ .succ (.var 0)),
            .succ ((.var 0) +ᵉ (((.var 1) ∸ᵉ (.var 0)) ∸ᵉ one))⟩ :=
        (eadd_congr (.refl (.succ (.var 0)))
            (derivable_sub_succ (.var 1) (.var 0))).trans
          (derivable_succ_add (.var 0) (((.var 1) ∸ᵉ (.var 0)) ∸ᵉ one))
      have hmid : Derivable eraDefs
          ⟨.succ ((.var 0 : ETm 2) +ᵉ (((.var 1) ∸ᵉ (.var 0)) ∸ᵉ one)),
            (.var 0) +ᵉ ((.var 1) ∸ᵉ (.var 0)) +ᵉ (one ∸ᵉ ((.var 1) ∸ᵉ (.var 0)))⟩ := by
        have h1 : Derivable eraDefs
            ⟨.succ ((.var 0 : ETm 2) +ᵉ (((.var 1) ∸ᵉ (.var 0)) ∸ᵉ one)),
              (.var 0) +ᵉ .succ (((.var 1) ∸ᵉ (.var 0)) ∸ᵉ one)⟩ :=
          (derivable_add_succ (.var 0) (((.var 1) ∸ᵉ (.var 0)) ∸ᵉ one)).symm
        have h2 : Derivable eraDefs
            ⟨(.var 0 : ETm 2) +ᵉ .succ (((.var 1) ∸ᵉ (.var 0)) ∸ᵉ one),
              (.var 0) +ᵉ (((.var 1) ∸ᵉ (.var 0)) +ᵉ (one ∸ᵉ ((.var 1) ∸ᵉ (.var 0))))⟩ :=
          eadd_congr (.refl (.var 0)) (derivable_succ_pred_eq ((.var 1) ∸ᵉ (.var 0)))
        exact (h1.trans h2).trans
          (derivable_add_assoc (.var 0) ((.var 1) ∸ᵉ (.var 0))
            (one ∸ᵉ ((.var 1) ∸ᵉ (.var 0)))).symm
      have h := hl.trans hmid
      simp only [Tm.subst, etsub_subst, eadd_subst, bump, recArgs, fcons] at h ⊢
      exact h
    case stepG =>
      have h : Derivable eraDefs
          ⟨(.var 1 : ETm 2) +ᵉ (.succ (.var 0) ∸ᵉ (.var 1)),
            (.var 1) +ᵉ ((.var 0) ∸ᵉ (.var 1)) +ᵉ (one ∸ᵉ ((.var 1) ∸ᵉ (.var 0)))⟩ :=
        (eadd_congr (.refl (.var 1)) (hsplit (.var 0) (.var 1))).trans
          (derivable_add_assoc (.var 1) ((.var 0) ∸ᵉ (.var 1))
            (one ∸ᵉ ((.var 1) ∸ᵉ (.var 0)))).symm
      simp only [Tm.subst, etsub_subst, eadd_subst, bump, recArgs, fcons] at h ⊢
      exact h
  have h := base.inst (fcons a (fcons b Fin.elim0))
  simp only [Tm.subst, etsub_subst, eadd_subst, fcons] at h
  exact h

end EraRecovery
```

## 7 The resolution: succ_sub_split needs Goodstein's φ

Goodstein 1954 (pp. 251–252) derives (17) with a bounded-sum
auxiliary `φ(n, a, b) = Σ_{k<n} sg((a ∸ k) + (b ∸ k))` recursing on
a fresh counter `n`. Because `n` appears only as a subtrahend
(`a ∸ n`, `b ∸ n`), the diagonal slides down by subtrahend
recursion alone: the successor-on-the-minuend wall is never hit.
This is the only known route, and it requires `φ`.

Two ways to realise `φ` over the fixed basis were analysed:

- Option 1 — `φ` as a basis term. Circular. Goodstein's `φ` equals
  `min(n, max(a, b))`; the natural closed form `min(x, y) = x ∸ (x ∸ y)`
  has a recursion `min(S n, M) = S n ∸ (S n ∸ M)` whose subterm
  `S n ∸ M` is `succ_sub_split` itself. The only theoretical escape
  is Marchenkov's positional `2^{2w}` construction (the same engine
  the completeness spec builds), heavy and unproven at the object
  level.
- Option 2 — `φ` as a fresh elementary symbol with recursion
  axioms (a definitional extension `defs⁺`). Clean: the recursion
  is posited with the counter in subtrahend position, so
  `succ_sub_split` then derives by `uniq` on `n`. Reuse the
  existing `eraDefs` algebra via `Derivable.mono` (a one-paragraph
  structural induction, verified this session). Cost: a non-minimal
  but finite, scheme-free basis.

Both stay inside `E³`: bounded sum and bounded product are
Kalmár-elementary (Marchenkov's defining closure), not general
primitive recursion, so naming them as auxiliaries does not leave
the class. Bounded sum and bounded product as schemes are
higher-order and would make the basis ERMor1-like; only specific
fixed-arity instances are needed, each already an `eraDefs` term in
principle.

The standing recommendation is Option 2 for a self-contained
recovery/E1–E5 result, with Option 1 (pure minimal basis) pursued
only if and when the completeness spec's object-level engine makes
it cheap.

## 8 Discarded leads

- Szudzik elegant pairing / course-of-values recursion (the prior
  handoff's leading idea): unnecessary and stronger than needed.
  Goodstein's recovery uses only single-variable `uniq` on a
  counter plus a bounded sum; no pairing, no double recursion.
- Direct `uniq` on `a` or `b` for recovery or `succ_sub_split`:
  blocked by the successor-on-the-minuend wall (§ 3).
- `φ` as a basis term via the `min` closed form: circular (§ 7).

## 9 Literature map

- R. L. Goodstein, "Logic-free formalisations of recursive
  arithmetic", *Math. Scand.* 2 (1954) 247–261. The direct
  ancestor of `Era.lean`'s calculus: his Sb₁/Sb₂/T/U/E₃ are
  `Era.lean`'s `subst`/`euclid`/`uniq`/`ext_succ`. His order
  algebra (1)–(9) is already transcribed; (17) is the gap; the `φ`
  construction is pp. 251–252; the induction schemata I₁/I₂/I₃ and
  the bounded-product auxiliary `q` are pp. 252–254 (likely
  unnecessary given the § 6 shortcut, which reaches recovery
  without I₂/I₃).
- M. Prunescu, L. Sauras-Altuzarra, J. M. Shunia, arXiv:2505.23787:
  the generator basis and the E1–E5 encodings (Lemma 2, Lemma 3,
  "Further examples").
- S. S. Marchenkov, *J. Appl. Ind. Math.* 1(3) (2007) 351–360:
  bounded sum/product as the closure operations of `E³`; the
  positional engine relevant to Option 1.
- S. Mazzanti, *MLQ* 48:1 (2002) 93–104: `σ(x) = exp₂ C(2x, x)`.

The three source PDFs were read in full during the brainstorm and
were located at the user's `wingeb/` directory (Goodstein,
Marchenkov, PSS).

## 10 Related documents

- `docs/superpowers/specs/2026-06-13-era-rich-basis-design.md` § 5–§ 7:
  the E1–E5 list, encodings, method, and the original recovery
  problem statement with the M2 outcome.
- `docs/superpowers/specs/2026-06-12-era-open-laws-domination-impasse.md`:
  the earlier domination impasse.
- `docs/superpowers/specs/2026-06-14-era-completeness-bounded-sum-design.md`:
  the companion semantic completeness workstream (the bounded-sum
  engine at the `eval` level).

## 11 Where a future brainstorm should start

1. Confirm the § 4 framing: recovery/E1–E5 is object-level, distinct
   from completeness, and gated on `succ_sub_split`.
2. Re-home the § 6 reduction into `Era.lean` (it is verified, so this
   is mechanical) so `succ_sub_split` is the single remaining target.
3. Decide Option 2 versus Option 1 (§ 7). Option 2 is the
   recommended self-contained route; Option 1 becomes attractive
   only if the completeness engine has landed and its object-level
   form is within reach.
4. Under Option 2, the milestone is: extend `eraDefs` to `defs⁺`
   with `φ` (certified elementary), derive `succ_sub_split` by `uniq`
   on the counter, obtain recovery via § 6, then E1–E5 via the
   existing `esubAt` machinery.

## 12 Design-space synthesis (2026-06-19)

A consolidated record of a clarifying discussion, framing the recovery /
E1–E5 work (this note's subject) inside the broader question of *which*
ERA basis one is formalising. Cross-references the detail above.

### 12.1 Three formulations of ERA

At least three distinct bases are worth separating:

1. **Scheme basis (`ERMor1`-like).** Bounded sum and bounded product are
   taken as *schemes* — operations parametrised by an arbitrary summand
   *term* `g`. That is higher-order, hence an *infinite* basis (one
   instance per summand shape), and powerful: bounded recursion of the
   Kalmár-elementary functions is derivable from it. Essentially
   `ERMor1` itself.
2. **Minimal basis.** `{0, succ, projᵢ, +, x mod y, 2ˣ}` (Prunescu–
   Sauras-Altuzarra–Shunia). Finite; fewest assumptions.
3. **Maximally-expressive finite basis.** A *finite* basis chosen not for
   minimality but to be as expressive — and as easy to write terms in —
   as a finite first-order basis can be.

The equivalence of any two is the same theorem and the same proof effort;
the choice only affects how short terms are when a basis is taken *in
isolation*.

### 12.2 Redundancy versus recovery

- **Redundancy** (the E1–E5 *goal*, § 2): the object-level `Derivable
  eraDefs` equations identifying each rich-basis convenience primitive
  with a `…Formula` encoding built only from the minimal generators —
  `derivable_sub_eq_subFormula`, `derivable_two_mul_eq_edmul`,
  `derivable_div_eq_divFormula`, `derivable_mul_eq_mulFormula`,
  `derivable_pow_eq_powFormula` (M3–M7), plus pure-generator closure (M8).
  Proving them shows each convenience primitive is *eliminable* as a basis
  element — that the rich basis is non-minimal *inside the calculus*.
- **Recovery** (the *lever*, § 3): the single order-arithmetic lemma every
  E1–E5 proof rests on — Goodstein 1954 (17), `a + (b ∸ a) = b + (a ∸ b)`
  (both sides `= max(a, b)`). It "recovers" a value from a truncated
  difference; it is what lets `∸`, `mod`, and division be manipulated in
  the logic-free calculus.

Redundancy is the deliverable; recovery is the tool. The obstruction (M2)
is that recovery's unconditional form forces the indicator `1 ∸ (b ∸ a)`,
needing successor-on-the-minuend (`S a ∸ b`), for which basis `∸` has no
recursion (it recurses only on its subtrahend). Verified (§ 6): recovery
reduces to `succ_sub_split`, blocked behind Goodstein's φ.

### 12.3 Semantic versus object level — what is and is not proved

Two levels (§ 4): semantic (`Tm.eval` into `ℕ` — "the metalanguage") and
object (`Derivable eraDefs` — the logic-free calculus). `eraSound` lifts
object to semantic, so **any E1–E5 proved object-level discharges its
semantic version for free**; the object-level statements are strictly
stronger. The converse (semantic ⇒ object) is exactly what fails — that is
the recovery obstruction.

Status of the *redundancy* (as distinct from completeness):

- The `…Formula` encodings exist as terms (`subFormula`, `edmul`,
  `divFormula`, `mulFormula`, `powFormula`, `Era.lean`).
- E1's *semantic* redundancy is proved and named: `subFormula_eval`
  (`subFormula` equals truncated subtraction as a `ℕ` function, all
  `x, y`).
- E2–E5 semantic correctness is established only on **numerals**
  (`numeral_dmul`, `numeral_mulFormula`, `numeral_divFormula`, …).
- **No** object-level `derivable_*_eq_*Formula` exists.

Crucially, `era_complete` + `era_sound_er` prove **completeness of the
finite rich basis** (`Era ≃ E³` as denoted functions), *not* **minimality**.
The completeness witnesses use the rich primitives directly (the `sub` case
is `Tm.var 0 ∸ᵉ Tm.var 1`; `eraBSum` uses `/ᵉ`, `^ᵉ`). So the minimal
sub-basis `{+, mod, 2ˣ}` has *not* been shown to suffice, at *either* level.
The Mazzanti/PSAS minimality theorem is therefore *not* formalised; the
encodings + `subFormula_eval` + the numeral lemmas are its ingredients, not
the assembled result.

### 12.4 φ in full, and why not `max`

Goodstein's auxiliary (§ 7), in full:

```text
φ(n, a, b) = Σ_{k<n} sg((a ∸ k) + (b ∸ k))      =  min(n, max(a, b))
```

(`sg` = signum). The summand is `1` exactly when `k < max(a, b)`, so the
sum counts up to `min(n, max(a, b))`; for `n ≥ max(a, b)` it delivers
`max(a, b)`, the right-hand side of recovery.

φ earns its place by **structure, not value**: it is a bounded *sum* whose
single recursion variable (the counter `n`, appearing as `a ∸ n`, `b ∸ n`)
sits in *subtrahend* position, so one `uniq` on `n` closes `succ_sub_split`
and the successor-on-minuend wall is never touched.

Adding `max` as a primitive instead does **not** help:

- As an *axiom* (`max = a + (b ∸ a)` plus symmetry): symmetry of `max` *is*
  recovery, so this *assumes* the result — eliminating the derivation
  rather than shortening it, and `max`'s own object-level redundancy is
  recovery again.
- With its *natural recursion* (`max(S a, S b) = S max(a, b)`, …): an
  irreducibly two-argument simultaneous descent, which the single-variable
  calculus cannot take and which reintroduces the same wall.

φ's non-obvious contribution is *linearisation* — collapsing the
two-argument order fact `max` into a one-dimensional subtrahend-only count.
`max` as a primitive does not inherit that trick; φ (Option 2, § 7) is the
minimal *honest* addition that makes recovery *derivable* rather than
*assumed*.

### 12.5 Designing a maximally-expressive finite basis (#3)

Goal: a *finite* basis in which bounded sum / bounded product are as short
to write as possible. Two structural facts bound what is achievable.

- **A finite basis cannot contain a scheme.** Bounded sum/product take an
  arbitrary summand *term*; that is higher-order. So #3 can never make an
  *arbitrary* bounded sum a single primitive application — only a short
  *composition*. Any operator that does take a summand/predicate parameter
  turns #3 back into #1.
- **The construction reduces bounded sum to one keystone.** The
  completeness engine factors as `bounded sum → recSeq → histCode →
  #{Diophantine zeros} → HW(packM)/w − tᵏ`, where `packM` is a closed form
  (cube-sum → product of geometric progressions). Everything outside the
  read-off is `+ ∸ · / ^ mod 2ˣ`.

Consequences for #3:

- **φ does not help expressiveness.** It is one fixed bounded sum (the
  recovery auxiliary), not a general tool; it belongs to the
  recovery/redundancy (object) side, not the expressiveness side.
- **The richest single fixed-arity addition is the Hamming weight `HW`**
  (binary digit sum). Every count — hence bounded sum *and* bounded product
  (same engine, `·` for `+`) — reduces to it. In the present basis `HW`
  (`eraSigma`/`hwClosed`) sits atop a deep sub-tower (`ν₂` of the central
  binomial, via Kummer); making `HW` primitive collapses that sub-tower and
  turns the count read-off into a one-liner.
- A pairing function (cheap sequence coding) and the already-present
  `2ˣ`/`div`/`mod` are the supporting coding substrate.

**The ceiling.** Even with `HW` primitive, a bounded sum of arbitrary `g`
is *not* a one-liner: it still needs `diophOf g` (the Diophantine encoding
of `g`'s graph), whose size dominates the term. The genuinely deep step is
the *factorisation identity* `cubeSum_factor`, a theorem inside the
equivalence proof — not a primitive. So fixed-arity additions (`HW` above
all) shorten the *leaves*; nothing fixed-arity trivialises the *scheme*.

A reasonable #3 "sweet spot" is therefore
`{0, succ, projᵢ, +, ∸, ·, /, ^, mod, 2ˣ, HW, ⟨·,·⟩ + proj}` — the rich
basis plus the counting/coding leaves — in which bounded sum/product are
`HW`-of-a-closed-form-pack-of-`diophOf(g)`: short modulo the unavoidable
encoding of `g`, with the deepest sub-towers gone. The equivalence to #1
and the reduction to #2 remain the same unavoidable proofs; only term sizes
in #3-in-isolation improve.
