# LawvereGodelT Typed-Term Rebuild Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> `superpowers:subagent-driven-development` (recommended) or
> `superpowers:executing-plans` to implement this plan
> task-by-task.  Steps use checkbox (`* [ ]`) syntax for
> tracking.

**Goal:** Rebuild `LawvereGodelTCat` on top of a
signature-parameterized typed `GodelTTerm S n σ`; formalize
Beckmann-Weiermann's full proof package (Lemma 16, strong
normalization, Tait-Martin-Löf confluence, numeral normal form,
completeness) at the typed-term level; deliver the categorical
equivalence `LawvereGodelTCat ≌ LawvereERCat` via the
Beckmann-Weiermann theorem, and the binary-tree extension
`LawvereGodelTBTCat ≌ LawvereGodelTCat` via Szudzik encoding
written internally.

**Architecture:** A single signature-parameterized inductive
`GodelTTerm S n σ` over `S : Set GodelTBase`, with the nucleus
specialized at `S = {.nat}` and the binary-tree extension at
`S = {.nat, .tree}`.  Free variables are base-typed only.  The
categorical quotient is by the equivalence closure of B-W's
syntactic reduction relation `▷`.  All structural results
(substitution, reduction, Lemma 16, SN, confluence,
completeness) are proven once parametrically over `S` and
specialized at instantiation.

**Tech Stack:** Lean 4 + mathlib.  Builds on existing project
infrastructure: `LawvereERCat` (Wikipedia-style ER), the
`Utilities/Tower.lean` tower-of-twos function, the
`LawvereERBoundComputable.lean` `iterT` /
`iterAutoBoundExpr` helpers (Task E.2 from the superseded
2026-04-21 plan), the `Utilities/SzudzikSeq.lean` infrastructure,
and the existing unlabeled-binary-tree type `BTL`.

**Design spec:**
`docs/superpowers/specs/2026-04-25-lawvere-godelt-typed-design.md`
(local, gitignored).

**Reference paper:**
`.claude/docs/characterizing-elementary-recursive-functions-fragment-godels-t.pdf`.

**Workstream tracker:**
`.session/workstreams/lawvere-elementary-recursive.md`.

**Branch:** `terence/syntax`.

---

## Progress as of 2026-04-27 (twenty-eight commits)

Twenty-eight commits land sequentially on `terence/syntax`,
implementing α through almost-complete δ.5.  The build is
clean and tests pass at every commit.

### Completed stages

* **Stage α** (`fe99d5c4`): old fresh-inductive `GodelTMor1`
  scaffolding torn down.  `Utilities/GodelTBracket.lean`
  taken out of the build path (still on disk; revisited
  in stage ν).
* **Stage β** (`82ee007f` through `03d98ebc`, ten commits):
  signature-parameterized `GodelTBase`, `GodelTType S`,
  `GodelTType.level`, `GodelTType.interp`,
  `GodelTBase.carrier`, the `GodelTTerm S n σ` inductive
  with arity-polymorphic atomic constructors, `interp`
  with `btlIter` helper, `subst`, `interp_subst`,
  `subst_var`, twelve per-constructor `@[simp]` interp
  lemmas, sanity tests.  `BTL` is imported from
  `GebLean.LawvereNatBT`; constructors are `BTL.leaf` and
  `BTL.node`.
* **Stage γ** (`44aa1174` through `f958a21b`, five
  commits): `Reduces` (`▷`) inductive per Beckmann-Weiermann
  Definition 4 with reduction rules for P / K / S /
  disc / iter / treeIter plus two `app` congruence rules,
  `Reduces.Star` reflexive-transitive closure (`▷*`),
  `Reduces.Equiv` equivalence closure (`≈`) with
  `refl` / `base_fwd` / `base_bwd` / `trans` constructors
  and a derived `symm`, `Reduces.interp_invariance`
  soundness lifted to Star and Equiv, reduction tests.

### Stage δ progress

* **δ.1** (`453d273e`): `LawvereGodelTLemma16.lean` skeleton.
* **δ.2** (`dfe04f85`): `GodelTTerm.lh`, `GodelTTerm.d`,
  `GodelTTerm.G` structural measures.  `G` is implemented
  via a top-level `match` on the term (rather than
  pattern-binding `σ` per branch) to satisfy Lean's
  equation-compiler unification.
* **δ.3** (`f3e59c55`): `GodelTTerm.bracketLevel` per
  Beckmann-Weiermann Definition 8, with twenty-two
  `@[simp]` rfl lemmas exposing each clause.

  The rule-14/15 case (general `app` not iter-headed) is
  factored into auxiliary `bracketLevelAppGen` (general)
  and `bracketLevelAppIter` (iter-form) helpers to avoid
  pattern overlap and to give Lean a clean structural
  recursion: the rule-14 self-reference
  `[ab]_{i+1}` is computed as an internal downward
  `Nat.rec` iteration from `g(σ)+1` to `i`, with seed
  `f.bracketLevel (g+1)` (rule 15 at the boundary).

* **δ.4** (`048c72f4`): paper-faithful Lemma 5 instances
  proven for our `bracketLevel`:

  * `bracketLevel_app_eq`: for `i ≤ σ.level` and
    non-iter head, `[app f a]_i = 2^[app f a]_{i+1} *
    ([f]_i + [a]_i)`.  Proof case-splits on `i + 1 ≤
    σ.level`; the `i = σ.level` case unfolds one
    Nat.rec step explicitly.
  * `bracketLevel_app_high`: for `i > σ.level` and
    non-iter head, `[app f a]_i = [f]_i`.
  * Plus `isIterHead` syntactic predicate.

  The `bracketLevel` definition was lightly refactored
  (without changing semantics) to remove pattern overlap
  that prevented the proofs from going through under
  `backward.isDefEq.respectTransparency = false`.

* **δ.5 (partial)** (`75506450`): five of the ten redex
  majorization lemmas plus four supporting helpers.

  Proved: `majorizes_redP_zero`, `majorizes_redP_succ`,
  `majorizes_redK`, `majorizes_redDisc_zero`,
  `majorizes_redDisc_succ`.  Each derives from
  `bracketLevel_app_eq` plus arithmetic.

  Helpers: `bracketLevel_app_ge_arg`,
  `bracketLevel_app_strict_arg`,
  `bracketLevel_app_high_ge`, the `≫` notation
  via `GodelTTerm.majorizes`.

* **δ.5 auxiliaries and four more redex lemmas**
  (2026-04-26 / 27, seven additional commits):

  * `50c91c3f`: `G_ge_level`, `bracketLevel_high_zero`
    (B-W Lemma 2 — brackets vanish above type level).
  * `9a205d06`: `majorizes_redTreeIter_leaf`.
  * `481ea46c`: `lh_pos`, `lh_app`, `lh_app_lt_left`,
    `lh_app_lt_right` structural helpers.
  * `fb302703`: `bracketLevel_zero_pos_arrow_NN`.  For any
    closed-or-open `t : N → N`, `1 ≤ [t]_0`.  Combined
    strong induction establishing the stronger mutual
    claim that arrow-typed terms either have positive
    bracket or argument type N→N.
  * `1e983c3a`: `majorizes_redIter_zero` (B-W Lemma 12).
    Uses the positivity auxiliary.
  * `f4f2df34`: `majorizes_redIter_succ` (B-W Lemma 13).
    Tower-gap argument, ~324 lines.  Unconditional strict
    decrease.
  * `68607215`: `majorizes_redTreeIter_node` for σ.level=0.
    ~470 lines.  General σ generalization deferred (see
    "Pending δ.5 work" below).

  **Multi-level argument required for the iter cases**:
  rule 11 gives `[I_ρ t^0]_1 = 1` for `g(ρ) = 0`, so for
  an outer `app` over an iter-form head, by rule 14 the
  exponent is `2^[head]_1 ≥ 2`.  This gives the strict
  inequality `[RHS]_0 < 2 · ([head]_0 + [arg]_0) ≤
  [LHS]_0` even when the iter rule's level-0
  pass-through `[I_ρ t^0]_0 = [t^0]_0` makes
  `[head]_0 = 0` for a base-typed-variable `t^0`.

### Pending δ.5 work (2026-04-27)

1. **`majorizes_redS`** (B-W Lemma 11, S combinator).
   Three subagent dispatches (one Sonnet, two Opus) have
   reported BLOCKED.  Detailed strategy and research
   findings:
   `docs/superpowers/notes/2026-04-27-redS-proof-strategy.md`
   (local, gitignored).  B-W defer the proof to Schütte
   1977 (textbook, paywalled).  The `majorizes_redIter_succ`
   proof is the structural template — explicit `set`
   abbreviations + step-by-step `bracketLevel_app_eq`/`_high`
   rewrites + careful arithmetic, ~400-700 lines expected.
   Currently being attempted directly in conversation.

2. **Generalize `majorizes_redTreeIter_node`** to remove
   the `hσ : σ.level = 0` hypothesis.  Required because
   `Reduces.redTreeIter_node` is for general σ, so
   `bracketLevel_strict` needs the general majorization.
   Pattern after `majorizes_redK` and
   `majorizes_redTreeIter_leaf` for general-σ handling.

3. **`Reduces.bracketLevel_le_at`** (helper) and
   **`Reduces.bracketLevel_strict`** (the main theorem of
   stage δ.5).  Both proven by `induction h` over the 12
   `Reduces` constructors.  Each base reduction case
   delegates to the corresponding `majorizes_red*` lemma's
   `.1` (strict) or `.2` (monotone) projection.  Two
   congruence cases (`redApp_left`, `redApp_right`)
   handled via case-split on `f.isIterHead` plus
   `bracketLevel_app_eq` arithmetic.

### Pending stages

* **δ.6** Lemma 16 (the main theorem).
* **δ.7** Lemma 17 (substitution of numerals).
* **ε** Strong normalization.
* **ζ** Tait-Martin-Löf confluence.
* **η** Numeral normal form + completeness.
* **θ** Categorical structure.
* **ι** Equivalence Nucleus ≌ LawvereERCat.
* **κ** Binary-tree extension.
* **λ** Szudzik-encoded equivalence BT ≌ Nucleus.
* **μ** Cross-stage tests.
* **ν** Programmer ergonomics (deferred).

### Implementation notes carried forward

The following implementation choices made during δ.1-δ.5
are part of the project state and should be preserved by
follow-on stages:

* `bracketLevel`'s rule-14 self-reference uses a downward
  `Nat.rec` iteration; the literal multiplicative form is
  recovered as `bracketLevel_app_eq` with the
  `i ≤ σ.level` precondition.
* `isIterHead : GodelTTerm S n σ → Bool` is the syntactic
  predicate distinguishing the bare `iter` /  `treeIter`
  constants from other heads.
* `bracketLevelAppIter` and `bracketLevelAppGen` are
  factored helpers; downstream proofs may unfold these to
  see the underlying clauses.
* `GodelTTerm.btlIter` is the structurally-recursive
  helper used by `interp` for the `treeIter` case
  (label-discarding fold over `BTL`).

---

## Project rules (inherited from CLAUDE.md)

* `lake build` and `lake test` after every code change.  Both
  must succeed with zero warnings before a commit lands.  Never
  `lake clean` or `lake env lean`.
* No `sorry` / `admit` / `Classical` / `noncomputable` /
  `axiom`.  Quotient and Quot may be used with their
  constructive API (`mk`, `lift`, `ind`, `sound`); avoid
  `Quotient.out` / `Quot.out` (which require `Classical.choice`).
* 80-character line limit.  All code in `namespace GebLean …
  end GebLean`.  Forbidden words in persistent writing per
  CLAUDE.md.  No emojis.  No "TODO" comments.  No
  copyright/author notices.
* Commit message trailer: `Co-Authored-By: Claude Opus 4.7
  (1M context) <noreply@anthropic.com>`.
* `autoImplicit = false`, `relaxedAutoImplicit = false` per
  `lakefile.toml`: write binders explicitly.
* "Try one proof step at a time"; factor lemmas when stuck;
  prefer `_` placeholders to view goals over `sorry`.

---

## File structure overview

### Files to create

* `GebLean/LawvereGodelT.lean` (replaces existing; stage α-β):
  `GodelTBase`, `GodelTType S`, base type carriers, type-level
  helpers.
* `GebLean/LawvereGodelTTerm.lean` (stage β): the `GodelTTerm
  S n σ` inductive plus per-constructor simp lemmas, `interp`,
  `subst`, `interp_subst`, `subst_var`.
* `GebLean/LawvereGodelTReduces.lean` (stage γ): the `Reduces`
  relation (`▷`), `Reduces.star` (`▷*`), `Reduces.equiv`
  (`≈`), and `Reduces.interp_invariance`.
* `GebLean/LawvereGodelTLemma16.lean` (stage δ): `g`,
  `[ ]_i`, `G`, `d`, `lh` and Lemma 16's full proof following
  Beckmann-Weiermann Lemmas 5-15.  Substitution Lemma 17.
* `GebLean/LawvereGodelTNormalize.lean` (stage ε):
  `Reduces.bracketLevel_strict`, well-founded `▷` recursion,
  total `normalize` returning the unique normal form.
* `GebLean/LawvereGodelTConfluence.lean` (stage ζ): parallel
  reduction `▷ₚ`, diamond property, Church-Rosser.
* `GebLean/LawvereGodelTCompleteness.lean` (stage η): numeral
  normal form for closed base-typed terms; completeness of `≈`
  for extensional equality.
* `GebLean/LawvereGodelTQuot.lean` (replaces existing;
  stage θ): `GodelTMor1`, `GodelTMorN`, `≈`-quotient setoid
  `godelTReducesEquivSetoid`, `Category LawvereGodelTCat`,
  `HasChosenFiniteProducts`.
* `GebLean/LawvereGodelTInterp.lean` (replaces existing;
  stage θ): faithful `godelTInterpFunctor`.
* `GebLean/LawvereGodelTERCatEquiv.lean` (replaces existing;
  stage ι): `erToGodelT`, `godelTToER` via logical-relations
  `GodelTRep`, equivalence functors and isos.
* `GebLean/Utilities/GodelTERTranslate.lean` (stage ι): derived
  defs `succT`, `predT`, `subT`, `bsumT`, `bprodT` (each ER
  constructor's T\* translation) with `interp_*` lemmas.
* `GebLean/LawvereGodelTBT.lean` (stage κ): specializations
  and helpers for `S = {.nat, .tree}`; tree-side definitions,
  BT-only `interp` cases, BT-only `Reduces` rules.
* `GebLean/LawvereGodelTBTQuot.lean` (stage κ): tuple,
  quotient, Category, HasChosenFiniteProducts at the BT
  specialization with pair-of-ℕ arities.
* `GebLean/LawvereGodelTBTSzudzik.lean` (stage λ): `treeCode`,
  `treeDecode` as nuclear morphisms; round-trip lemmas.
* `GebLean/LawvereGodelTBTEquiv.lean` (stage λ): `btToNucleus`,
  `nucleusToBT` functors; categorical equivalence
  `LawvereGodelTBTCat ≌ LawvereGodelTCat`.
* `GebLeanTests/LawvereGodelTTerm.lean` (stage β/γ): `#guard`
  tests for `interp`, `subst`, `Reduces`.
* `GebLeanTests/LawvereGodelTLemma16.lean` (stage δ): tests
  for Lemma 16 on small terms.
* `GebLeanTests/LawvereGodelTCompleteness.lean` (stage η):
  completeness tests.
* `GebLeanTests/LawvereGodelTERCatEquiv.lean` (rebuilt;
  stage ι): nucleus equivalence tests.
* `GebLeanTests/LawvereGodelTBT.lean` (stage μ): tree-side
  primitives, Szudzik round-trip, sample tree-recursive
  functions.

### Files to delete

| File | Stage |
|---|---|
| `GebLean/LawvereGodelTQuot.lean` (existing version) | α |
| `GebLean/LawvereGodelTInterp.lean` (existing version) | α |
| `GebLean/LawvereGodelTERCatEquiv.lean` (existing version) | α |
| `GebLean/Utilities/GodelTBracket.lean` (rebuilt at ν) | α (defer ν) |
| `GebLean/Utilities/GodelTBound.lean` (Task E.1 measures) | α |
| `GebLeanTests/LawvereGodelT.lean` (old test) | α |
| `GebLeanTests/LawvereGodelTERCatEquiv.lean` (old test) | α |

### Files to keep intact

* `GebLean/LawvereER.lean`, `GebLean/LawvereERQuot.lean`,
  `GebLean/LawvereERInterp.lean`, all `LawvereERLex*` /
  `LawvereERBool*` / `LawvereERDelta*` / `LawvereERPrimrec*` /
  `LawvereERTetration*` files.
* `GebLean/Utilities/ERArith.lean` (including the
  `ERMor1.natN` from Task E.2).
* `GebLean/Utilities/Tower.lean`,
  `GebLean/LawvereERBoundComputable.lean` (including the
  `ERMor1.iterT`, `iterAutoBoundExpr`, `interp_iterT_of_bounded`
  helpers from Task E.2).
* `GebLean/Utilities/SzudzikSeq.lean`,
  `GebLean/Utilities/RegisterMachine.lean`,
  `GebLean/Utilities/ERTreeArith.lean`.

---

## Stage α: Cleanup

Task ID: `#188`.

Removes the existing fresh-inductive `GodelTMor1` scaffolding so
the new typed-term build can proceed without import cycles or
name clashes.

### Task α.1: Delete the existing scaffolding

**Files:**

* Delete: `GebLean/LawvereGodelTQuot.lean`,
  `GebLean/LawvereGodelTInterp.lean`,
  `GebLean/LawvereGodelTERCatEquiv.lean`,
  `GebLean/Utilities/GodelTBound.lean`,
  `GebLeanTests/LawvereGodelT.lean`,
  `GebLeanTests/LawvereGodelTERCatEquiv.lean`.
* Modify: `GebLean.lean` and `GebLeanTests.lean` to remove
  the deleted modules from the import lists.

The existing `GebLean/LawvereGodelT.lean` (with `GodelTType` and
`GodelTTerm`) will be replaced wholesale in stage β.  Leave it
in place for now but note that stage β's first task overwrites
it.

`GebLean/Utilities/GodelTBracket.lean` is also kept as-is for
now and is not exported from `GebLean.lean` until stage ν
revisits it.  (If `GebLean.lean` already imports it, leave the
import; the file will continue to build because it depends only
on the existing `LawvereGodelT.lean` skeleton.)

* [ ] **Step 1: Delete the listed files.**

```bash
rm GebLean/LawvereGodelTQuot.lean \
   GebLean/LawvereGodelTInterp.lean \
   GebLean/LawvereGodelTERCatEquiv.lean \
   GebLean/Utilities/GodelTBound.lean \
   GebLeanTests/LawvereGodelT.lean \
   GebLeanTests/LawvereGodelTERCatEquiv.lean
```

* [ ] **Step 2: Update `GebLean.lean` to drop the deleted
  modules.**

Read the current contents of `GebLean.lean`, remove the lines
importing each of `LawvereGodelTQuot`, `LawvereGodelTInterp`,
`LawvereGodelTERCatEquiv`, and `Utilities.GodelTBound`.  Leave
`LawvereGodelT` itself in place (will be edited in stage β) and
leave `Utilities.GodelTBracket` in place.

* [ ] **Step 3: Update `GebLeanTests.lean` to drop the deleted
  test modules.**

Remove the lines importing `LawvereGodelT` and
`LawvereGodelTERCatEquiv` from `GebLeanTests.lean`.

* [ ] **Step 4: `lake build`.**

Expected: clean build with zero warnings.

* [ ] **Step 5: `lake test`.**

Expected: tests pass.

* [ ] **Step 6: Commit.**

```bash
git add -A
git commit -m "$(cat <<'EOF'
Stage α: tear down old fresh-inductive GodelTMor1 scaffolding

Delete the old `LawvereGodelTQuot.lean`, `LawvereGodelTInterp.lean`,
`LawvereGodelTERCatEquiv.lean`, and `Utilities/GodelTBound.lean`
files together with their test modules.  These are being
replaced by the typed-term build per the 2026-04-25 design spec.
The existing `LawvereGodelT.lean` (with `GodelTType` and
`GodelTTerm`) is retained for now; stage β replaces it
wholesale.  The `Utilities/GodelTBracket.lean` utility is kept
out of the build path until stage ν revisits it.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

### Stage α completion criterion

* All listed files deleted.
* `GebLean.lean` and `GebLeanTests.lean` no longer reference
  them.
* `lake build` clean; `lake test` passes.
* HEAD has the cleanup commit.

---

## Stage β: Scaffolding

Task ID: `#189`.

Defines `GodelTBase`, `GodelTType S`, `GodelTTerm S n σ`,
`interp`, `subst`, `interp_subst`, `subst_var`, plus
per-constructor simp lemmas.

### Task β.1: Replace `LawvereGodelT.lean` with new base/type module

**Files:**

* Modify (full overwrite): `GebLean/LawvereGodelT.lean`.
* Modify: `GebLean.lean` (re-add the import; it should already
  be there).

* [ ] **Step 1: Overwrite `GebLean/LawvereGodelT.lean`.**

```lean
import Mathlib.Data.Set.Insert
import GebLean.Utilities.NatBT

namespace GebLean

/-- Base types in the typed combinatory system.  `nat` is
always available; `tree` is opt-in via the `S : Set GodelTBase`
parameter. -/
inductive GodelTBase : Type
  | nat
  | tree
  deriving DecidableEq, Repr, Inhabited

/-- Carrier of each base type. -/
def GodelTBase.carrier : GodelTBase → Type
  | .nat => Nat
  | .tree => BTL

/-- Types over a chosen base-type set.  `arrow` is the only
type former besides `base`; this matches B-W Definition 1. -/
inductive GodelTType (S : Set GodelTBase) : Type
  | base (b : GodelTBase) (h : b ∈ S) : GodelTType S
  | arrow : GodelTType S → GodelTType S → GodelTType S

namespace GodelTType

/-- Standard interpretation of a type: base types use their
carriers, arrow types are Lean function types. -/
def interp {S : Set GodelTBase} : GodelTType S → Type
  | .base b _ => b.carrier
  | .arrow σ τ => σ.interp → τ.interp

/-- Type-level measure `g` from B-W Definition 7.  `g (.base
_) = 0`; `g (.arrow σ τ) = max (g σ + 1) (g τ)`. -/
def level {S : Set GodelTBase} : GodelTType S → Nat
  | .base _ _ => 0
  | .arrow σ τ => max (σ.level + 1) τ.level

end GodelTType

/-- Convenience: `nat`-base type at any S that contains
`.nat`.  Used pervasively below. -/
abbrev GodelTType.baseN {S : Set GodelTBase}
    (h : GodelTBase.nat ∈ S) : GodelTType S :=
  .base .nat h

/-- Convenience: `tree`-base type at any S that contains
`.tree`. -/
abbrev GodelTType.baseT {S : Set GodelTBase}
    (h : GodelTBase.tree ∈ S) : GodelTType S :=
  .base .tree h

end GebLean
```

* [ ] **Step 2: `lake build`.**

Expected: clean build.  `BTL` may need its existing import
location confirmed; if `GebLean.Utilities.NatBT` is not the
correct module for `BTL`, replace the import accordingly (search
`grep -r "inductive BTL" GebLean/` for the right path).

* [ ] **Step 3: Commit.**

```bash
git add GebLean/LawvereGodelT.lean
git commit -m "Stage β.1: introduce GodelTBase, GodelTType S, type-level helpers

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>"
```

### Task β.2: Define the `GodelTTerm S n σ` inductive

**Files:**

* Create: `GebLean/LawvereGodelTTerm.lean`.
* Modify: `GebLean.lean` to import it.

* [ ] **Step 1: Write the file with the inductive only.**

```lean
import GebLean.LawvereGodelT

namespace GebLean

/-- B-W's typed combinatory system, parameterized by a set of
available base types.  Free variables are base-typed only and
indexed by `Fin n`.  Higher-typed terms are always closed —
there is no λ-abstraction at the term level; abstraction is
realized by `K` and `S`. -/
inductive GodelTTerm (S : Set GodelTBase) :
    Nat → GodelTType S → Type
  | var {n : Nat} (i : Fin n) (h : GodelTBase.nat ∈ S) :
      GodelTTerm S n (.base .nat h)
  | app {n : Nat} {σ τ : GodelTType S}
      (f : GodelTTerm S n (.arrow σ τ))
      (a : GodelTTerm S n σ) :
      GodelTTerm S n τ
  | zero (h : GodelTBase.nat ∈ S) :
      GodelTTerm S 0 (.base .nat h)
  | succ (h : GodelTBase.nat ∈ S) :
      GodelTTerm S 0 (.arrow (.base .nat h) (.base .nat h))
  | pred (h : GodelTBase.nat ∈ S) :
      GodelTTerm S 0 (.arrow (.base .nat h) (.base .nat h))
  | K (σ τ : GodelTType S) :
      GodelTTerm S 0 (.arrow σ (.arrow τ σ))
  | S_comb (ρ σ τ : GodelTType S) :
      GodelTTerm S 0
        (.arrow (.arrow ρ (.arrow σ τ))
          (.arrow (.arrow ρ σ) (.arrow ρ τ)))
  | disc {h : GodelTBase.nat ∈ S} (σ : GodelTType S) :
      GodelTTerm S 0
        (.arrow (.base .nat h) (.arrow σ (.arrow σ σ)))
  | iter (h : GodelTBase.nat ∈ S) :
      GodelTTerm S 0
        (.arrow (.base .nat h)
          (.arrow (.arrow (.base .nat h) (.base .nat h))
            (.arrow (.base .nat h) (.base .nat h))))
  | leaf (h : GodelTBase.tree ∈ S) :
      GodelTTerm S 0 (.base .tree h)
  | node (h : GodelTBase.tree ∈ S) :
      GodelTTerm S 0
        (.arrow (.base .tree h)
          (.arrow (.base .tree h) (.base .tree h)))
  | treeIter (h : GodelTBase.tree ∈ S) (σ : GodelTType S) :
      GodelTTerm S 0
        (.arrow (.base .tree h)
          (.arrow σ (.arrow (.arrow σ (.arrow σ σ)) σ)))

end GebLean
```

* [ ] **Step 2: Add the import to `GebLean.lean`.**

Insert `import GebLean.LawvereGodelTTerm` after the
`LawvereGodelT` import.

* [ ] **Step 3: `lake build`.**

Expected: clean build.

* [ ] **Step 4: Commit.**

```bash
git add GebLean/LawvereGodelTTerm.lean GebLean.lean
git commit -m "Stage β.2: define GodelTTerm S n σ inductive

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>"
```

### Task β.3: Define `GodelTTerm.interp`

**Files:**

* Modify: `GebLean/LawvereGodelTTerm.lean`.

* [ ] **Step 1: Append the `interp` definition.**

Add after the inductive's `end GebLean`-prefix — i.e., still
inside `namespace GebLean`:

```lean
/-- Standard interpretation of a `GodelTTerm S n σ` against a
base-typed environment `Fin n → ℕ`.  Each constructor maps to
its set-theoretic semantics. -/
def GodelTTerm.interp {S : Set GodelTBase} :
    {n : Nat} → {σ : GodelTType S} →
    GodelTTerm S n σ → (Fin n → Nat) → σ.interp
  | _, _, .var i _, env =>
      env i
  | _, _, .app f a, env =>
      f.interp env (a.interp env)
  | _, _, .zero _, _ =>
      (0 : Nat)
  | _, _, .succ _, _ =>
      Nat.succ
  | _, _, .pred _, _ =>
      Nat.pred
  | _, _, .K _ _, _ =>
      fun a _ => a
  | _, _, .S_comb _ _ _, _ =>
      fun f g x => f x (g x)
  | _, _, .disc _, _ =>
      fun n a b =>
        match n with
        | 0 => a
        | _ + 1 => b
  | _, _, .iter _, _ =>
      fun count step base =>
        Nat.rec base (fun _ prev => step prev) count
  | _, _, .leaf _, _ =>
      BTL.leaf
  | _, _, .node _, _ =>
      BTL.branch
  | _, _, .treeIter _ _, _ =>
      fun t base step =>
        BTL.rec base (fun l r ih_l ih_r => step ih_l ih_r) t
```

Confirm the `BTL.branch` and `BTL.rec` constructor names against
the existing project definitions; adjust if the actual names
differ.

* [ ] **Step 2: `lake build`.**

Expected: clean build.

* [ ] **Step 3: Commit.**

```bash
git commit -am "Stage β.3: define GodelTTerm.interp

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>"
```

### Task β.4: Per-constructor `interp` simp lemmas

**Files:**

* Modify: `GebLean/LawvereGodelTTerm.lean`.

* [ ] **Step 1: Append simp lemmas one per constructor.**

```lean
@[simp] theorem GodelTTerm.interp_var
    {S : Set GodelTBase} {n : Nat} (i : Fin n)
    (h : GodelTBase.nat ∈ S) (env : Fin n → Nat) :
    (GodelTTerm.var (S := S) i h).interp env = env i := rfl

@[simp] theorem GodelTTerm.interp_app
    {S : Set GodelTBase} {n : Nat}
    {σ τ : GodelTType S}
    (f : GodelTTerm S n (.arrow σ τ))
    (a : GodelTTerm S n σ) (env : Fin n → Nat) :
    (GodelTTerm.app f a).interp env =
      f.interp env (a.interp env) := rfl

@[simp] theorem GodelTTerm.interp_zero
    {S : Set GodelTBase} (h : GodelTBase.nat ∈ S)
    (env : Fin 0 → Nat) :
    (GodelTTerm.zero (S := S) h).interp env = 0 := rfl

-- (succ, pred, K, S_comb, disc, iter, leaf, node, treeIter
-- analogous; one per line)
```

Add the matching simp lemmas for `succ`, `pred`, `K`, `S_comb`,
`disc`, `iter`, `leaf`, `node`, `treeIter` following the same
pattern.  Each is `rfl`.

* [ ] **Step 2: `lake build`.**

Expected: clean build, no warnings.

* [ ] **Step 3: Commit.**

```bash
git commit -am "Stage β.4: per-constructor interp simp lemmas

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>"
```

### Task β.5: Define `GodelTTerm.subst`

**Files:**

* Modify: `GebLean/LawvereGodelTTerm.lean`.

* [ ] **Step 1: Append the substitution function.**

```lean
/-- Substitute base-typed terms (in arity m) for the free
variables of a term in arity n.  Direct structural recursion;
no binders, no capture. -/
def GodelTTerm.subst {S : Set GodelTBase} {n m : Nat} :
    {σ : GodelTType S} →
    (Fin n → GodelTTerm S m
      (.base .nat (Set.mem_of_eq_of_mem rfl
        (Set.mem_insert_iff.mpr (Or.inl rfl)))) → False) →
    GodelTTerm S n σ → GodelTTerm S m σ := sorry
```

The above is a sketch that won't compile — the membership-proof
threading is awkward.  Replace with a cleaner form: assume
`hN : GodelTBase.nat ∈ S` is in scope as a typeclass-bound
hypothesis or thread it via the substitution map's type:

```lean
def GodelTTerm.subst {S : Set GodelTBase} (hN : GodelTBase.nat ∈ S)
    {n m : Nat} :
    (Fin n → GodelTTerm S m (.base .nat hN)) →
    {σ : GodelTType S} → GodelTTerm S n σ → GodelTTerm S m σ
  | ε, _, .var i h =>
      have : h = hN := by rfl
      ε i  -- after equating the proofs
  | _, _, .app f a => sorry
  | _, _, .zero h => .zero h
  | _, _, .succ h => .succ h
  | _, _, .pred h => .pred h
  | _, _, .K σ τ => .K σ τ
  | _, _, .S_comb ρ σ τ => .S_comb ρ σ τ
  | _, _, .disc σ => .disc σ
  | _, _, .iter h => .iter h
  | _, _, .leaf h => .leaf h
  | _, _, .node h => .node h
  | _, _, .treeIter h σ => .treeIter h σ
```

Resolve the membership-proof issue by either:

1. Using `Subsingleton` proof irrelevance: since `b ∈ S` for
   `b : GodelTBase` and `S : Set GodelTBase` is propositional,
   any two proofs are equal; the `var i h` case can rewrite `h`
   to `hN` via `Subsingleton.elim`.

2. Or refactoring `var`'s signature so the membership proof
   is implicit and drawn from a single canonical source.

Whichever path is cleanest given Lean's elaboration.  The
`app` case requires recursion on both `f` and `a`:

```lean
  | ε, _, .app f a => .app (f.subst hN ε) (a.subst hN ε)
```

Use `_` placeholders to view goals while resolving the proof
plumbing.

* [ ] **Step 2: `lake build`.**

If type elaboration is fighting back, the cleanest fallback is
to add a `[Fact (GodelTBase.nat ∈ S)]` instance class on the
nucleus and binary-tree-extended specializations; pull `hN`
from the instance.

* [ ] **Step 3: Once `subst` compiles, commit.**

```bash
git commit -am "Stage β.5: define GodelTTerm.subst

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>"
```

### Task β.6: Prove `GodelTTerm.interp_subst` and `subst_var`

**Files:**

* Modify: `GebLean/LawvereGodelTTerm.lean`.

* [ ] **Step 1: State and prove `interp_subst`.**

```lean
theorem GodelTTerm.interp_subst {S : Set GodelTBase}
    (hN : GodelTBase.nat ∈ S) {n m : Nat}
    (ε : Fin n → GodelTTerm S m (.base .nat hN))
    {σ : GodelTType S} (t : GodelTTerm S n σ)
    (env : Fin m → Nat) :
    (t.subst hN ε).interp env =
      t.interp (fun i => (ε i).interp env) := by
  induction t with
  | var i h => simp [GodelTTerm.subst]
  | app f a ih_f ih_a => simp [GodelTTerm.subst, ih_f, ih_a]
  | zero h => simp [GodelTTerm.subst]
  | succ h => simp [GodelTTerm.subst]
  | pred h => simp [GodelTTerm.subst]
  | K σ τ => simp [GodelTTerm.subst]
  | S_comb ρ σ τ => simp [GodelTTerm.subst]
  | disc σ => simp [GodelTTerm.subst]
  | iter h => simp [GodelTTerm.subst]
  | leaf h => simp [GodelTTerm.subst]
  | node h => simp [GodelTTerm.subst]
  | treeIter h σ => simp [GodelTTerm.subst]
```

If `simp` can't close cases automatically, fall back to manual
`unfold GodelTTerm.subst` plus `rfl` per case.

* [ ] **Step 2: State and prove `subst_var`.**

```lean
theorem GodelTTerm.subst_var {S : Set GodelTBase}
    (hN : GodelTBase.nat ∈ S) {n : Nat}
    {σ : GodelTType S} (t : GodelTTerm S n σ) :
    t.subst hN (fun i => .var i hN) = t := by
  induction t <;> simp [GodelTTerm.subst, *]
```

* [ ] **Step 3: `lake build`.  Commit.**

```bash
git commit -am "Stage β.6: prove interp_subst and subst_var

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>"
```

### Task β.7: Initial sanity tests

**Files:**

* Create: `GebLeanTests/LawvereGodelTTerm.lean`.
* Modify: `GebLeanTests.lean` to import it.

* [ ] **Step 1: Write the test module.**

```lean
import GebLean.LawvereGodelTTerm

namespace GebLean

private def Snat : Set GodelTBase := {GodelTBase.nat}
private def hNS : GodelTBase.nat ∈ Snat := by decide

private def numeral (n : Nat) :
    GodelTTerm Snat 0 (.base .nat hNS) :=
  match n with
  | 0 => .zero hNS
  | k + 1 => .app (.succ hNS) (numeral k)

#guard (numeral 5).interp Fin.elim0 = 5

#guard (GodelTTerm.app (.app (.K _ _) (numeral 7))
          (numeral 3)).interp Fin.elim0 = 7

end GebLean
```

* [ ] **Step 2: Register in `GebLeanTests.lean`.**

* [ ] **Step 3: `lake test`.  Commit.**

```bash
git commit -am "Stage β.7: initial GodelTTerm sanity tests

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>"
```

### Stage β completion criterion

* `GebLean/LawvereGodelT.lean` and
  `GebLean/LawvereGodelTTerm.lean` build cleanly and define
  `GodelTBase`, `GodelTType S`, `GodelTTerm S n σ`, `interp`,
  `subst`, `interp_subst`, `subst_var`, plus simp lemmas per
  constructor.
* `lake test` includes basic sanity tests and passes.

---

## Stage γ: Reduction relation

Task ID: `#190`.

Defines `Reduces` (`▷`), its reflexive-transitive closure
`Reduces.star` (`▷*`), and the equivalence closure
`Reduces.equiv` (`≈`).  Proves `Reduces.interp_invariance`.

### Task γ.1: Inductive `Reduces`

**Files:**

* Create: `GebLean/LawvereGodelTReduces.lean`.
* Modify: `GebLean.lean`.

* [ ] **Step 1: Define the relation.**

```lean
import GebLean.LawvereGodelTTerm

namespace GebLean

/-- One-step reduction relation per Beckmann-Weiermann
Definition 4.  Tree-flavored reductions appear as additional
constructors gated by `GodelTBase.tree ∈ S`. -/
inductive GodelTTerm.Reduces {S : Set GodelTBase} {n : Nat} :
    {σ : GodelTType S} →
    GodelTTerm S n σ → GodelTTerm S n σ → Prop
  -- pred
  | redP_zero (hN : GodelTBase.nat ∈ S) :
      Reduces (.app (.pred hN) (.zero hN)) (.zero hN)
  | redP_succ (hN : GodelTBase.nat ∈ S)
      (t : GodelTTerm S n (.base .nat hN)) :
      Reduces (.app (.pred hN) (.app (.succ hN) t)) t
  -- K
  | redK (σ τ : GodelTType S)
      (a : GodelTTerm S n σ) (b : GodelTTerm S n τ) :
      Reduces (.app (.app (.K σ τ) a) b) a
  -- S
  | redS (ρ σ τ : GodelTType S)
      (f : GodelTTerm S n (.arrow ρ (.arrow σ τ)))
      (g : GodelTTerm S n (.arrow ρ σ))
      (x : GodelTTerm S n ρ) :
      Reduces (.app (.app (.app (.S_comb ρ σ τ) f) g) x)
        (.app (.app f x) (.app g x))
  -- disc
  | redDisc_zero {hN : GodelTBase.nat ∈ S}
      (σ : GodelTType S)
      (a b : GodelTTerm S n σ) :
      Reduces
        (.app (.app (.app (.disc (h := hN) σ) (.zero hN)) a)
              b) a
  | redDisc_succ {hN : GodelTBase.nat ∈ S}
      (σ : GodelTType S)
      (t : GodelTTerm S n (.base .nat hN))
      (a b : GodelTTerm S n σ) :
      Reduces
        (.app (.app (.app (.disc (h := hN) σ)
          (.app (.succ hN) t)) a) b) b
  -- iter
  | redIter_zero (hN : GodelTBase.nat ∈ S)
      (a : GodelTTerm S n
        (.arrow (.base .nat hN) (.base .nat hN)))
      (b : GodelTTerm S n (.base .nat hN)) :
      Reduces (.app (.app (.app (.iter hN) (.zero hN)) a) b) b
  | redIter_succ (hN : GodelTBase.nat ∈ S)
      (t : GodelTTerm S n (.base .nat hN))
      (a : GodelTTerm S n
        (.arrow (.base .nat hN) (.base .nat hN)))
      (b : GodelTTerm S n (.base .nat hN)) :
      Reduces (.app (.app (.app (.iter hN)
        (.app (.succ hN) t)) a) b)
        (.app a (.app (.app (.app (.iter hN) t) a) b))
  -- treeIter
  | redTreeIter_leaf (hT : GodelTBase.tree ∈ S)
      (σ : GodelTType S)
      (a : GodelTTerm S n σ)
      (b : GodelTTerm S n (.arrow σ (.arrow σ σ))) :
      Reduces (.app (.app (.app (.treeIter hT σ)
        (.leaf hT)) a) b) a
  | redTreeIter_node (hT : GodelTBase.tree ∈ S)
      (σ : GodelTType S)
      (l r : GodelTTerm S n (.base .tree hT))
      (a : GodelTTerm S n σ)
      (b : GodelTTerm S n (.arrow σ (.arrow σ σ))) :
      Reduces (.app (.app (.app (.treeIter hT σ)
          (.app (.app (.node hT) l) r)) a) b)
        (.app
          (.app b
            (.app (.app (.app (.treeIter hT σ) l) a) b))
          (.app (.app (.app (.treeIter hT σ) r) a) b))
  -- congruence rules
  | redApp_left {σ τ : GodelTType S}
      {f g : GodelTTerm S n (.arrow σ τ)}
      (h : Reduces f g) (a : GodelTTerm S n σ) :
      Reduces (.app f a) (.app g a)
  | redApp_right {σ τ : GodelTType S}
      (f : GodelTTerm S n (.arrow σ τ))
      {a b : GodelTTerm S n σ} (h : Reduces a b) :
      Reduces (.app f a) (.app f b)

end GebLean
```

* [ ] **Step 2: `lake build`.**  Add the import to
  `GebLean.lean`.  Commit.

```bash
git add GebLean/LawvereGodelTReduces.lean GebLean.lean
git commit -m "Stage γ.1: GodelTTerm.Reduces inductive (▷)

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>"
```

### Task γ.2: Reflexive-transitive closure `Reduces.star`

**Files:**

* Modify: `GebLean/LawvereGodelTReduces.lean`.

* [ ] **Step 1: Append the closure inductive.**

```lean
/-- Reflexive-transitive closure of `▷`. -/
inductive GodelTTerm.Reduces.Star {S : Set GodelTBase} {n : Nat} :
    {σ : GodelTType S} →
    GodelTTerm S n σ → GodelTTerm S n σ → Prop
  | refl {σ : GodelTType S} (t : GodelTTerm S n σ) :
      Star t t
  | step {σ : GodelTType S}
      {t u v : GodelTTerm S n σ}
      (h₁ : t.Reduces u) (h₂ : Star u v) :
      Star t v

scoped notation:50 t " ▷* " s =>
  GebLean.GodelTTerm.Reduces.Star t s
```

* [ ] **Step 2: Helpers: trans, single-step lift.**

```lean
theorem GodelTTerm.Reduces.Star.trans {S n}
    {σ : GodelTType S} {t u v : GodelTTerm S n σ}
    (h₁ : t ▷* u) (h₂ : u ▷* v) : t ▷* v := by
  induction h₁ with
  | refl _ => exact h₂
  | step h ih_tail ih => exact .step h (ih h₂)

theorem GodelTTerm.Reduces.toStar {S n}
    {σ : GodelTType S} {t u : GodelTTerm S n σ}
    (h : t.Reduces u) : t ▷* u :=
  .step h (.refl _)
```

* [ ] **Step 3: `lake build`.  Commit.**

### Task γ.3: Equivalence closure `Reduces.Equiv` (`≈`)

**Files:**

* Modify: `GebLean/LawvereGodelTReduces.lean`.

* [ ] **Step 1: Define the symmetric-transitive closure.**

```lean
/-- Equivalence closure of `▷*`: smallest equivalence relation
containing `▷`. -/
inductive GodelTTerm.Reduces.Equiv {S : Set GodelTBase} {n : Nat} :
    {σ : GodelTType S} →
    GodelTTerm S n σ → GodelTTerm S n σ → Prop
  | reflexive {σ} (t : GodelTTerm S n σ) : Equiv t t
  | symm_step {σ} {t u v : GodelTTerm S n σ}
      (h : Equiv u v) (r : t.Reduces u) : Equiv v t
  | trans_step {σ} {t u v : GodelTTerm S n σ}
      (h₁ : Equiv t u) (h₂ : Equiv u v) : Equiv t v
  | base {σ} {t u : GodelTTerm S n σ} (r : t.Reduces u) :
      Equiv t u

scoped notation:50 t " ≈ " s =>
  GebLean.GodelTTerm.Reduces.Equiv t s
```

(Note: the inductive's `symm_step` is one path to encode
symmetry; alternatively define `Equiv` as the smallest
equivalence and prove it properly closed under the four laws.
Whichever spelling compiles.)

* [ ] **Step 2: Equivalence-relation properties: refl, symm,
  trans.**

```lean
theorem GodelTTerm.Reduces.Equiv.refl {S n σ}
    (t : GodelTTerm S n σ) : t ≈ t := .reflexive t

theorem GodelTTerm.Reduces.Equiv.symm {S n σ}
    {t u : GodelTTerm S n σ} (h : t ≈ u) : u ≈ t := by
  induction h with
  | reflexive _ => exact .reflexive _
  | symm_step h r ih => sorry -- complete by case analysis
  | trans_step h₁ h₂ ih₁ ih₂ => exact .trans_step ih₂ ih₁
  | base r => sorry
```

Replace `sorry` with the proper proofs.  If the chosen `Equiv`
spelling makes proofs awkward, redefine as the
reflexive-symmetric-transitive closure of `▷` directly:

```lean
inductive GodelTTerm.Reduces.Equiv ... where
  | refl_step (t) : Equiv t t
  | base_fwd (r : t.Reduces u) : Equiv t u
  | base_bwd (r : t.Reduces u) : Equiv u t
  | trans (h₁ : Equiv t u) (h₂ : Equiv u v) : Equiv t v
```

with `symm` defined by structural induction.  This form is
cleaner.

* [ ] **Step 3: `lake build`.  Commit.**

### Task γ.4: Soundness — `Reduces.interp_invariance`

**Files:**

* Modify: `GebLean/LawvereGodelTReduces.lean`.

* [ ] **Step 1: Prove the rule-by-rule lemma.**

```lean
theorem GodelTTerm.Reduces.interp_invariance
    {S : Set GodelTBase} {n : Nat}
    {σ : GodelTType S} {t s : GodelTTerm S n σ}
    (h : t.Reduces s) (env : Fin n → Nat) :
    t.interp env = s.interp env := by
  induction h with
  | redP_zero hN => rfl
  | redP_succ hN t => simp [GodelTTerm.interp]
  | redK σ τ a b => rfl
  | redS ρ σ τ f g x => rfl
  | redDisc_zero σ a b => rfl
  | redDisc_succ σ t a b => simp [GodelTTerm.interp]
  | redIter_zero hN a b => rfl
  | redIter_succ hN t a b => simp [GodelTTerm.interp]
  | redTreeIter_leaf hT σ a b => rfl
  | redTreeIter_node hT σ l r a b => simp [GodelTTerm.interp]
  | redApp_left h_red a ih =>
      simp [GodelTTerm.interp, ih]
  | redApp_right f h_red ih =>
      simp [GodelTTerm.interp, ih]
```

* [ ] **Step 2: Lift to `Star` and `Equiv`.**

```lean
theorem GodelTTerm.Reduces.Star.interp_invariance
    {S n σ} {t u : GodelTTerm S n σ}
    (h : t ▷* u) (env : Fin n → Nat) :
    t.interp env = u.interp env := by
  induction h with
  | refl _ => rfl
  | step r tail ih =>
      rw [GodelTTerm.Reduces.interp_invariance r env, ih]

theorem GodelTTerm.Reduces.Equiv.interp_invariance
    {S n σ} {t u : GodelTTerm S n σ}
    (h : t ≈ u) (env : Fin n → Nat) :
    t.interp env = u.interp env := by
  induction h with
  | refl_step _ => rfl
  | base_fwd r =>
      exact GodelTTerm.Reduces.interp_invariance r env
  | base_bwd r =>
      exact (GodelTTerm.Reduces.interp_invariance r env).symm
  | trans h₁ h₂ ih₁ ih₂ => rw [ih₁, ih₂]
```

(Names match whichever `Equiv` form was chosen in γ.3.)

* [ ] **Step 3: `lake build`.  Commit.**

### Task γ.5: Reduction tests

**Files:**

* Modify: `GebLeanTests/LawvereGodelTTerm.lean` (extend).

* [ ] **Step 1: Add reduction tests.**

```lean
example : (GodelTTerm.app (.app (.K _ _) (numeral 5))
            (numeral 3)).Reduces (numeral 5) := by
  exact .redK _ _ (numeral 5) (numeral 3)

example : (GodelTTerm.app (.app (.app (.iter hNS)
            (numeral 3)) (.succ hNS)) (numeral 0))
            .interp Fin.elim0 = 3 := by
  -- by reduction or by direct interp computation
  rfl
```

* [ ] **Step 2: `lake test`.  Commit.**

### Stage γ completion criterion

* `Reduces`, `Reduces.Star`, `Reduces.Equiv` defined.
* `Reduces.interp_invariance` and lifts to `Star` / `Equiv`
  proven.
* Tests pass.

---

## Stage δ: Lemma 16 (paper-faithful tower bound)

Task ID: `#191`.

The substantive mathematical stage.  Defines the structural
measures `g`, `[ ]_i`, `G`, `d`, `lh` per Beckmann-Weiermann
Definitions 7-10 and proves Lemma 16's tower bound by structural
induction following the paper's Lemmas 5-15.  Substitution
Lemma 17 follows.

This stage is large.  Per the paper, the proof is ~10 pages.
Expect 800-1500 lines of Lean.  Subdivide aggressively.

### Task δ.1: Type-level helpers

**Files:**

* Create: `GebLean/LawvereGodelTLemma16.lean`.

* [ ] **Step 1: File header + imports.**

```lean
import GebLean.LawvereGodelTReduces
import GebLean.Utilities.Tower

namespace GebLean

/-! # Lemma 16: structural tower bound for GodelTTerm

Following Beckmann-Weiermann 2000 Definitions 7-10 and the
proof of Lemma 16 on pp. 480-484.  All measures are defined
parametrically over `S : Set GodelTBase`. -/

end GebLean
```

* [ ] **Step 2: Confirm `tower` from `Utilities/Tower.lean`
  matches B-W's `2_m`.**

The existing `tower` should have `tower 0 x = x` and
`tower (m + 1) x = 2 ^ tower m x`.  If the existing definition
differs, use it as-is and adjust subsequent statements.

* [ ] **Step 3: Commit.**

### Task δ.2: Term-level measures `lh` and `d`

**Files:**

* Modify: `GebLean/LawvereGodelTLemma16.lean`.

* [ ] **Step 1: Define `lh` (term tree size).**

```lean
def GodelTTerm.lh {S : Set GodelTBase} :
    {n : Nat} → {σ : GodelTType S} →
    GodelTTerm S n σ → Nat
  | _, _, .var _ _ => 1
  | _, _, .app f a => f.lh + a.lh + 1
  | _, _, .zero _ => 1
  | _, _, .succ _ => 1
  | _, _, .pred _ => 1
  | _, _, .K _ _ => 1
  | _, _, .S_comb _ _ _ => 1
  | _, _, .disc _ => 1
  | _, _, .iter _ => 1
  | _, _, .leaf _ => 1
  | _, _, .node _ => 1
  | _, _, .treeIter _ _ => 1
```

* [ ] **Step 2: Define `d` (iter-nesting depth).**

Per B-W Definition 10: `d` counts the maximum depth of nested
`iter` (or `treeIter`) operators.  Reformulated for typed
applicative form:

```lean
def GodelTTerm.d {S : Set GodelTBase} :
    {n : Nat} → {σ : GodelTType S} →
    GodelTTerm S n σ → Nat
  | _, _, .var _ _ => 0
  | _, _, .app f a => max f.d a.d
  | _, _, .zero _ => 0
  | _, _, .succ _ => 0
  | _, _, .pred _ => 0
  | _, _, .K _ _ => 0
  | _, _, .S_comb _ _ _ => 0
  | _, _, .disc _ => 0
  | _, _, .iter _ => 1
  | _, _, .leaf _ => 0
  | _, _, .node _ => 0
  | _, _, .treeIter _ _ => 1
```

The `iter` and `treeIter` constants contribute `1` to depth; the
`app`-rule's max-of-children captures depth through nesting.
This matches the B-W formulation when iter is applied to its
arguments via `app`.

* [ ] **Step 3: Define `G` (max type level).**

```lean
def GodelTTerm.G {S : Set GodelTBase} :
    {n : Nat} → {σ : GodelTType S} →
    GodelTTerm S n σ → Nat
  | _, σ, .var _ _ => σ.level
  | _, _, .app f a => max f.G a.G
  | _, σ, .zero _ => σ.level
  | _, σ, .succ _ => σ.level
  | _, σ, .pred _ => σ.level
  | _, σ, .K _ _ => σ.level
  | _, σ, .S_comb _ _ _ => σ.level
  | _, σ, .disc _ => σ.level
  | _, σ, .iter _ => σ.level
  | _, σ, .leaf _ => σ.level
  | _, σ, .node _ => σ.level
  | _, σ, .treeIter _ _ => σ.level
```

* [ ] **Step 4: `lake build`.  Commit.**

### Task δ.3: The level-indexed value `[ ]_i`

**Files:**

* Modify: `GebLean/LawvereGodelTLemma16.lean`.

* [ ] **Step 1: Define `bracketLevel` per B-W Definition 8.**

```lean
def GodelTTerm.bracketLevel {S : Set GodelTBase} :
    {n : Nat} → {σ : GodelTType S} →
    Nat → GodelTTerm S n σ → Nat
  | _, _, _, .var _ _ => 0
  -- Definition 8 cases 2-7 for combinators:
  | _, _, 0, .zero _ => 0
  | _, _, _ + 1, .zero _ => 0
  | _, _, 0, .succ _ => 1
  | _, _, _ + 1, .succ _ => 0
  | _, _, 0, .pred _ => 1
  | _, _, _ + 1, .pred _ => 0
  | _, _, 0, .K _ _ => 1
  | _, σ, i + 1, .K _ _ =>
      if i + 1 ≤ σ.level then 1 else 0
  -- ... continue for S_comb, disc, iter ...
  -- iter's case is the substantive one.  Per Definition 8
  -- rules 10-13 for `I_ρ t^0`:
  --   [I_ρ t^0]_0 := [t^0]_0
  --   [I_ρ t^0]_i := 1 if 1 ≤ i ≤ g ρ + 1
  --   [I_ρ t^0]_i := [t^0]_0 if i = g ρ + 2
  --   [I_ρ t^0]_i := 0 if i > g ρ + 2
  -- In our applicative form the t^0 argument appears via app,
  -- so this gets folded into the app case.
  | _, _, i, .app f a =>
      -- Definition 8 case 14: [a^{στ} b^σ]_i :=
      --   2^([a^{στ}b^σ]_{i+1}) * ([a^{στ}]_i + [b^σ]_i)
      --   if i ≤ g σ and a^{στ} is not an iterator;
      --   otherwise = [a^{στ}]_i.
      sorry  -- complete with the case split per Def 8 rule 14-15
  -- tree analogues...
  | _, _, _, .leaf _ => 1  -- placeholder; B-W tree-extension form
  | _, _, _, .node _ => 1  -- placeholder
  | _, _, _, .treeIter _ _ => 1  -- placeholder
```

This is the largest single definition.  Subdivide if needed:
introduce a helper `bracketLevelApp` for the `app` case that
itself dispatches on whether the head of the application is an
iterator.

The exact case structure follows B-W Definition 8 verbatim;
work through the paper one rule at a time, replacing each
`sorry` with the matching Lean expression.

* [ ] **Step 2: Per-constructor simp lemmas for
  `bracketLevel`.**

For each constructor (`var`, `zero`, `succ`, etc.) state and
prove the corresponding clause as a `@[simp]` lemma.  These are
unfoldings of the definition.

* [ ] **Step 3: `lake build`.  Commit.**

### Task δ.4: Lemma 5 (combinator subterm bound)

**Files:**

* Modify: `GebLean/LawvereGodelTLemma16.lean`.

The paper's Lemma 5: `[a^{στ} b^σ]_i ≤ 2^{[ab]_{i+1}} *
([a]_i + [b]_i)` if `i ≤ g σ` (multiplicative-formula upper
bound).  Lemma 5.2 gives the ≥ analogue when `i > g σ`.

* [ ] **Step 1: State and prove Lemma 5.1 (the ≤ direction).**

```lean
theorem GodelTTerm.lemma5_one {S n}
    {σ τ : GodelTType S}
    (a : GodelTTerm S n (.arrow σ τ))
    (b : GodelTTerm S n σ)
    (i : Nat) (hi : i ≤ σ.level)
    (hNotIter : ¬ a.isIterHead) :
    (GodelTTerm.app a b).bracketLevel i ≤
      2 ^ (GodelTTerm.app a b).bracketLevel (i + 1) *
        (a.bracketLevel i + b.bracketLevel i) := by
  -- Definition 8 case 14 unfolds to equality, so the bound is
  -- by reflexivity (the case split's = side of Definition 8).
  sorry
```

(`isIterHead` is a helper predicate distinguishing whether `a`
has the form `iter t` or similar; define it alongside.)

* [ ] **Step 2: Lemma 5.2 analogue.**

* [ ] **Step 3: Commit.**

### Task δ.5: Lemmas 6-13 (combinator-specific bounds)

**Files:**

* Modify: `GebLean/LawvereGodelTLemma16.lean`.

Lemmas 6-12 each state a `≫` (majorization) relationship
between a redex's left-hand and right-hand sides.  Lemma 13
states `t ▷ s → s.bracketLevel 0 < t.bracketLevel 0` (strict
decrease).

* [ ] **Step 1: Auxiliary `≫` predicate.**

```lean
def GodelTTerm.majorizes {S n}
    {σ : GodelTType S} (t s : GodelTTerm S n σ) : Prop :=
  t.bracketLevel 0 > s.bracketLevel 0 ∧
  ∀ i ≤ σ.level, t.bracketLevel i ≥ s.bracketLevel i
```

* [ ] **Step 2: Lemma 6 (`P(O) ≫ O`).**

```lean
theorem GodelTTerm.lemma6 {S n} (hN : GodelTBase.nat ∈ S) :
    GodelTTerm.majorizes
      (.app (.pred (S := S) (n := n) hN) (.zero hN))
      (.zero hN) := by
  refine ⟨?_, ?_⟩
  · simp [GodelTTerm.bracketLevel]; omega
  · intro i hi
    simp [GodelTTerm.bracketLevel]; omega
```

* [ ] **Steps 3-9: Lemmas 7-12 analogously.**

Each is a similar 5-15 line proof using arithmetic on the
`bracketLevel` definition's clauses.  Work through the paper.

* [ ] **Step 10: Lemma 13.**

```lean
theorem GodelTTerm.Reduces.bracketLevel_strict {S n}
    {σ : GodelTType S} {t s : GodelTTerm S n σ}
    (h : t.Reduces s) :
    s.bracketLevel 0 < t.bracketLevel 0 := by
  induction h with
  | redP_zero hN => exact (GodelTTerm.lemma6 hN).1
  | redP_succ hN t => exact (GodelTTerm.lemma7 hN t).1
  -- ... one case per reduction rule, each delegating to the
  --     corresponding Lemma 6-12 instance ...
  | redApp_left h_red a ih => sorry  -- congruence: by IH
  | redApp_right f h_red ih => sorry  -- congruence: by IH
```

The congruence cases use Lemma 4 from the paper (which we'd
state as auxiliary lemmas about `bracketLevel` under `app`-with-
reduction).

* [ ] **Step 11: Commit.**

### Task δ.6: Lemma 16

**Files:**

* Modify: `GebLean/LawvereGodelTLemma16.lean`.

The main theorem.  By structural induction on `t`.

* [ ] **Step 1: State Lemma 16.**

```lean
theorem GodelTTerm.lemma16 {S : Set GodelTBase} {n : Nat}
    {σ : GodelTType S} (t : GodelTTerm S n σ)
    (i : Nat) (hi : i ≤ σ.level) :
    t.bracketLevel i ≤
      tower ((t.G + 1) * t.d + t.G + 1 - i)
            ((t.G + 1) * t.d + t.G + 1 - i + 2 * t.lh) := by
  induction t with
  | var i_ h => sorry
  | app f a ih_f ih_a => sorry
  | zero h => sorry
  | succ h => sorry
  | pred h => sorry
  | K σ τ => sorry
  | S_comb ρ σ τ => sorry
  | disc σ => sorry
  | iter h => sorry
  | leaf h => sorry
  | node h => sorry
  | treeIter h σ => sorry
```

* [ ] **Step 2: Atomic constructor cases.**

Each atomic constructor's `bracketLevel` is a small constant
(0 or 1).  The right-hand side is `tower (positive) (positive +
2 * 1)` ≥ 1.  Discharge by arithmetic and tower monotonicity.

* [ ] **Step 3: `var` case.**

`bracketLevel i (var _ _) = 0 ≤ anything`.

* [ ] **Step 4: `app` case (the substantive case).**

```lean
  | app f a ih_f ih_a => by
    -- bracketLevel i (app f a) by Definition 8 case 14:
    --   = 2^(bracketLevel (i+1) (app f a)) * (bracketLevel i f
    --       + bracketLevel i a)  [if i ≤ g σ_a, a not iter-head]
    --   = bracketLevel i f       [otherwise]
    -- Apply IH to f and a.
    -- For the multiplicative case, use that 2^x * (y + z)
    -- ≤ tower(K)(M) for K = max(f.G, a.G) + ... and M = f.lh
    -- + a.lh + linear-in-args.  This involves the standard
    -- tower-arithmetic absorption.
    sorry
```

This case is the bulk of the work.  Follow B-W's proof on
pp. 482-484.  Subdivide into helper lemmas: `lemma16_app_iter`
(when the app's head is `iter` or `treeIter`),
`lemma16_app_combinator` (when the head is K, S, disc, etc.),
`lemma16_app_app` (when the head is itself an app).  Each helper
states the bound for that sub-case and combines via tower
arithmetic.

* [ ] **Step 5: Tower arithmetic helpers.**

Likely needed:

```lean
theorem GebLean.tower_mul_le_tower_add_one
    (m k x y : Nat) (h : 2 ≤ x) :
    2 ^ (tower m k) * (x + y) ≤ tower (m + 1) (max x y + 2) := by
  sorry

theorem GebLean.tower_add_le_tower_succ ...
```

These mirror the existing `LawvereERBoundComputable`'s
`mul_tower_le_tower_add_two` etc.  Some may already exist;
search and reuse.

* [ ] **Step 6: Commit.**

### Task δ.7: Lemma 17 (substitution of numerals)

**Files:**

* Modify: `GebLean/LawvereGodelTLemma16.lean`.

* [ ] **Step 1: Define `numeral` and `treeNumeral` helpers.**

```lean
def numeral {S} (hN : GodelTBase.nat ∈ S) (n : Nat) :
    GodelTTerm S 0 (.base .nat hN) :=
  match n with
  | 0 => .zero hN
  | k + 1 => .app (.succ hN) (numeral hN k)

@[simp] theorem numeral_lh {S} (hN : GodelTBase.nat ∈ S) (n : Nat) :
    (numeral hN n).lh = 2 * n + 1 := by
  induction n <;> simp [numeral, GodelTTerm.lh, *]
```

* [ ] **Step 2: Lemma 17.**

```lean
theorem GodelTTerm.lemma17 {S : Set GodelTBase}
    (hN : GodelTBase.nat ∈ S) {n : Nat}
    {σ : GodelTType S} (t : GodelTTerm S n σ)
    (ms : Fin n → Nat) :
    (t.subst hN (fun i => numeral hN (ms i))).lh ≤
      t.lh + 2 * (Finset.univ.sum ms) := by
  induction t with
  | var i h => simp [GodelTTerm.subst, numeral_lh]; omega
  | app f a ih_f ih_a => simp [GodelTTerm.subst, GodelTTerm.lh, ih_f, ih_a]; omega
  -- atomic cases: lh stays 1.
  | _ => simp [GodelTTerm.subst, GodelTTerm.lh]; omega
```

* [ ] **Step 3: Commit.**

### Stage δ completion criterion

* `lh`, `d`, `G`, `bracketLevel` defined.
* Lemmas 5-13 proven, Lemma 16 proven, Lemma 17 proven.
* `lake build` clean (no `sorry`).
* `lake test` passes (tests added in stage μ).

---

## Stage ε: Strong normalization

Task ID: `#192`.

Uses Lemma 13's strict-decrease + Lemma 16's tower bound to
prove that every reduction sequence terminates.  Defines a total
`normalize` returning the unique normal form of every term.

### Task ε.1: Strict-decrease + well-founded recursion

**Files:**

* Create: `GebLean/LawvereGodelTNormalize.lean`.

* [ ] **Step 1: Define the well-founded relation.**

```lean
import GebLean.LawvereGodelTLemma16

namespace GebLean

/-- Reverse of `▷` viewed as a relation on `GodelTTerm`.
Well-founded by Lemma 13 + bracketLevel 0 strict decrease. -/
theorem GodelTTerm.Reduces.wf {S n σ} :
    WellFounded (fun (t s : GodelTTerm S n σ) => s.Reduces t) := by
  apply WellFounded.intro
  intro t
  -- well-founded by induction on bracketLevel 0 t.
  exact (Nat.lt_wfRel.wf.apply (t.bracketLevel 0)).elim
    (fun _ => sorry) -- supply via lemma13
```

The exact Lean syntax for "well-founded by image into ℕ" is
`WellFounded.onFun` or similar; consult mathlib for the right
combinator.  The key fact is `t.Reduces s → s.bracketLevel 0 <
t.bracketLevel 0`.

* [ ] **Step 2: `lake build`.  Commit.**

### Task ε.2: One-step reduction function

**Files:**

* Modify: `GebLean/LawvereGodelTNormalize.lean`.

* [ ] **Step 1: Define `reduceStep`.**

```lean
/-- Try to perform a single leftmost-outermost reduction step.
Returns `none` if the term is already in normal form. -/
def GodelTTerm.reduceStep {S : Set GodelTBase} :
    {n : Nat} → {σ : GodelTType S} →
    GodelTTerm S n σ → Option (GodelTTerm S n σ)
  -- Pattern-match on each redex shape.  Try head first;
  -- if no head redex, recurse left-then-right under app.
  | _, _, .app (.pred _) (.zero _), some (.zero _)
  -- ... (one case per reduction rule, plus congruence
  --     fallthroughs for app)
  | _, _, _, none
```

Define carefully to ensure totality and to match `Reduces`'s
relation.

* [ ] **Step 2: Soundness.**

```lean
theorem GodelTTerm.reduceStep_sound {S n σ}
    (t : GodelTTerm S n σ) :
    ∀ s, t.reduceStep = some s → t.Reduces s
```

* [ ] **Step 3: Completeness.**

```lean
theorem GodelTTerm.reduceStep_complete {S n σ}
    (t : GodelTTerm S n σ) :
    t.reduceStep = none ↔ ∀ s, ¬ t.Reduces s
```

* [ ] **Step 4: Commit.**

### Task ε.3: Total `normalize`

**Files:**

* Modify: `GebLean/LawvereGodelTNormalize.lean`.

* [ ] **Step 1: Define `normalize` by well-founded recursion.**

```lean
def GodelTTerm.normalize {S : Set GodelTBase} {n σ}
    (t : GodelTTerm S n σ) : GodelTTerm S n σ :=
  match h : t.reduceStep with
  | none => t
  | some s =>
    have : s.bracketLevel 0 < t.bracketLevel 0 := by
      have hred := GodelTTerm.reduceStep_sound t s h
      exact GodelTTerm.Reduces.bracketLevel_strict hred
    s.normalize
  termination_by t.bracketLevel 0
```

* [ ] **Step 2: Properties.**

```lean
theorem GodelTTerm.normalize_normal {S n σ}
    (t : GodelTTerm S n σ) :
    t.normalize.reduceStep = none

theorem GodelTTerm.reduces_star_normalize {S n σ}
    (t : GodelTTerm S n σ) :
    t ▷* t.normalize
```

* [ ] **Step 3: Commit.**

### Stage ε completion criterion

* `Reduces.wf`, `reduceStep`, `normalize` defined and proven
  total/correct.
* `lake build` clean.

---

## Stage ζ: Confluence

Task ID: `#193`.

Tait-Martin-Löf parallel-reduction proof of confluence.

### Task ζ.1: Parallel reduction `▷ₚ`

**Files:**

* Create: `GebLean/LawvereGodelTConfluence.lean`.

* [ ] **Step 1: Define parallel reduction.**

The Tait-Martin-Löf trick: define `▷ₚ` as a relation that
contracts arbitrarily many redexes simultaneously in one step,
including reflexivity.  Then prove the diamond property:
`t ▷ₚ s₁ ∧ t ▷ₚ s₂ → ∃ r, s₁ ▷ₚ r ∧ s₂ ▷ₚ r`.

```lean
inductive GodelTTerm.ParReduces {S n} :
    {σ : GodelTType S} →
    GodelTTerm S n σ → GodelTTerm S n σ → Prop
  | refl {σ} (t : GodelTTerm S n σ) : ParReduces t t
  | app {σ τ} (f f' : GodelTTerm S n (.arrow σ τ))
      (a a' : GodelTTerm S n σ)
      (hf : ParReduces f f') (ha : ParReduces a a') :
      ParReduces (.app f a) (.app f' a')
  -- one constructor per redex form: parallel-reduces both
  -- sub-terms then contracts the head redex.
  | redK_par σ τ a a' b b'
      (ha : ParReduces a a') (hb : ParReduces b b') :
      ParReduces (.app (.app (.K σ τ) a) b) a'
  -- ... S_comb, disc, pred, iter, leaf, node, treeIter analogues
```

* [ ] **Step 2: Relate `▷ₚ` and `▷*`.**

```lean
theorem GodelTTerm.Reduces.toPar {S n σ} {t s : GodelTTerm S n σ}
    (h : t.Reduces s) : t.ParReduces s

theorem GodelTTerm.ParReduces.toStar {S n σ}
    {t s : GodelTTerm S n σ} (h : t.ParReduces s) : t ▷* s
```

* [ ] **Step 3: Commit.**

### Task ζ.2: Diamond property

**Files:**

* Modify: `GebLean/LawvereGodelTConfluence.lean`.

* [ ] **Step 1: Define the "complete development" function.**

```lean
def GodelTTerm.devel {S n σ}
    (t : GodelTTerm S n σ) : GodelTTerm S n σ
  -- Contract every visible redex in t in one pass.
```

* [ ] **Step 2: Prove `t ▷ₚ s → s ▷ₚ t.devel`.**

This is the standard "triangle" lemma: every parallel reduction
factors through the complete development.

* [ ] **Step 3: Diamond.**

```lean
theorem GodelTTerm.ParReduces.diamond {S n σ}
    {t s₁ s₂ : GodelTTerm S n σ}
    (h₁ : t.ParReduces s₁) (h₂ : t.ParReduces s₂) :
    ∃ r, s₁.ParReduces r ∧ s₂.ParReduces r := by
  exact ⟨t.devel, par_to_devel h₁, par_to_devel h₂⟩
```

* [ ] **Step 4: Commit.**

### Task ζ.3: Church-Rosser for `▷*`

**Files:**

* Modify: `GebLean/LawvereGodelTConfluence.lean`.

* [ ] **Step 1: Prove confluence.**

```lean
theorem GodelTTerm.Reduces.Star.confluent {S n σ}
    {t s₁ s₂ : GodelTTerm S n σ}
    (h₁ : t ▷* s₁) (h₂ : t ▷* s₂) :
    ∃ r, s₁ ▷* r ∧ s₂ ▷* r
```

By taking `▷*`-chains and lifting to parallel-reduction chains;
diamond on parallel-reduction lifts to confluence on `▷*` via
the standard "tiling" argument.

* [ ] **Step 2: Uniqueness of normal forms.**

```lean
theorem GodelTTerm.normalize_unique {S n σ}
    (t : GodelTTerm S n σ)
    (s : GodelTTerm S n σ)
    (h_reach : t ▷* s) (h_normal : ∀ u, ¬ s.Reduces u) :
    s = t.normalize
```

* [ ] **Step 3: Commit.**

### Stage ζ completion criterion

* Parallel reduction defined; diamond proven; Church-Rosser for
  `▷*` follows; normal forms are unique.

---

## Stage η: Numeral normal form and completeness

Task ID: `#194`.

### Task η.1: Numeral normal form

**Files:**

* Create: `GebLean/LawvereGodelTCompleteness.lean`.

* [ ] **Step 1: State the closed-base-typed normal-form lemma.**

```lean
theorem GodelTTerm.closed_base_normal_is_numeral {S}
    (hN : GodelTBase.nat ∈ S)
    (t : GodelTTerm S 0 (.base .nat hN))
    (h : ∀ s, ¬ t.Reduces s) :
    ∃ k : Nat, t = numeral hN k
```

* [ ] **Step 2: Proof by induction on term structure.**

The closed normal forms of base type are characterized by a
syntactic case analysis: the only constants of base type at
arity 0 are `zero`; all other terms must be applications, and
applications in normal form must have a head that doesn't admit
any redex pattern.  By inspection of the constructor types, the
only normal-form base-typed closed terms are stacks of
`succ`-applications terminating in `zero`.

* [ ] **Step 3: Tree analogue.**

```lean
theorem GodelTTerm.closed_tree_normal_is_treeNumeral {S}
    (hT : GodelTBase.tree ∈ S)
    (t : GodelTTerm S 0 (.base .tree hT))
    (h : ∀ s, ¬ t.Reduces s) :
    ∃ τ : BTL, t = treeNumeral hT τ
```

where `treeNumeral` builds a `GodelTTerm` from a `BTL` using
`leaf` and `node`.

* [ ] **Step 4: Commit.**

### Task η.2: Completeness for closed terms

**Files:**

* Modify: `GebLean/LawvereGodelTCompleteness.lean`.

* [ ] **Step 1: State and prove.**

```lean
theorem GodelTTerm.equiv_iff_interp_eq_closed {S}
    (hN : GodelTBase.nat ∈ S)
    (t s : GodelTTerm S 0 (.base .nat hN)) :
    t ≈ s ↔ t.interp Fin.elim0 = s.interp Fin.elim0 := by
  refine ⟨fun h => h.interp_invariance _, fun h => ?_⟩
  -- Reverse direction: by SN + confluence + normal-form-is-numeral.
  obtain ⟨nt, hnt_reach, hnt_normal⟩ := exists_normal_form t
  obtain ⟨ns, hns_reach, hns_normal⟩ := exists_normal_form s
  obtain ⟨kt, h_eq_t⟩ := closed_base_normal_is_numeral hN nt hnt_normal
  obtain ⟨ks, h_eq_s⟩ := closed_base_normal_is_numeral hN ns hns_normal
  have hin_t : nt.interp Fin.elim0 = kt := by
    rw [h_eq_t]; exact numeral_interp hN kt
  have hin_s : ns.interp Fin.elim0 = ks := by
    rw [h_eq_s]; exact numeral_interp hN ks
  have h_int_t : t.interp Fin.elim0 = kt := by
    rw [Reduces.Star.interp_invariance hnt_reach]; exact hin_t
  have h_int_s : s.interp Fin.elim0 = ks := by
    rw [Reduces.Star.interp_invariance hns_reach]; exact hin_s
  have h_kt_ks : kt = ks := by rw [← h_int_t, h, h_int_s]
  rw [h_eq_t, h_eq_s, h_kt_ks] at *
  -- t and s both reduce to the same numeral.  Combine the two
  -- reductions to get t ≈ s.
  exact .trans (.star_to_equiv hnt_reach)
    (.symm (.star_to_equiv hns_reach))
```

* [ ] **Step 2: Commit.**

### Task η.3: Completeness for open terms

**Files:**

* Modify: `GebLean/LawvereGodelTCompleteness.lean`.

* [ ] **Step 1: State and prove via numeral substitution.**

```lean
theorem GodelTTerm.equiv_iff_interp_eq {S}
    (hN : GodelTBase.nat ∈ S) {n : Nat}
    (t s : GodelTTerm S n (.base .nat hN)) :
    t ≈ s ↔
      ∀ env : Fin n → Nat, t.interp env = s.interp env := by
  refine ⟨fun h env => h.interp_invariance env, fun h => ?_⟩
  -- For each env, the numeral substitution
  --   t.subst hN (fun i => numeral hN (env i))
  -- is closed and base-typed.  By the closed completeness
  -- (η.2), if t.interp env = s.interp env for all env, then
  -- the numeral-substituted versions are ≈.  The substitution
  -- map is in fact a special case of Reduces-equivalence.
  sorry  -- complete via η.2 + a separate lemma about
         -- t ≈ s ↔ ∀ ms, t[m̄] ≈ s[m̄].
```

The forward direction (closed → open) requires a separate
result: if `t.subst hN (fun i => numeral hN (ms i)) ≈ s.subst
hN (fun i => numeral hN (ms i))` for all `ms`, then `t ≈ s`.
This is the Beckmann-Weiermann Section 4 result.

* [ ] **Step 2: Commit.**

### Stage η completion criterion

* Numeral normal form proven for closed terms.
* Completeness `t ≈ s ↔ ∀ env, t.interp env = s.interp env` for
  base-typed (open or closed) nucleus terms.

---

## Stage θ: Categorical structure

Task ID: `#195`.

### Task θ.1: Setoid + quotient

**Files:**

* Create: `GebLean/LawvereGodelTQuot.lean`.

* [ ] **Step 1: Define `GodelTMor1` abbreviation.**

```lean
import GebLean.LawvereGodelTCompleteness
import Mathlib.CategoryTheory.Category.Basic
import GebLean.Utilities.ComputableLimits

namespace GebLean

abbrev SnatOnly : Set GodelTBase := {GodelTBase.nat}

theorem GebLean.hN_SnatOnly : GodelTBase.nat ∈ SnatOnly := by decide

abbrev GodelTMor1 (n : Nat) :=
  GodelTTerm SnatOnly n (.base .nat hN_SnatOnly)

abbrev GodelTMorN (n m : Nat) := Fin m → GodelTMor1 n
```

* [ ] **Step 2: Setoid by `≈`.**

```lean
def godelTMorNReducesEquivSetoid (n m : Nat) :
    Setoid (GodelTMorN n m) where
  r f g := ∀ i, GodelTTerm.Reduces.Equiv (f i) (g i)
  iseqv := { refl := ..., symm := ..., trans := ... }
```

* [ ] **Step 3: Commit.**

### Task θ.2: Composition (substitution)

**Files:**

* Modify: `GebLean/LawvereGodelTQuot.lean`.

* [ ] **Step 1: Define `GodelTMorN.comp`.**

```lean
def GodelTMorN.comp {n m k : Nat}
    (f : GodelTMorN n m) (g : GodelTMorN m k) :
    GodelTMorN n k :=
  fun i => (g i).subst hN_SnatOnly f
```

* [ ] **Step 2: Lift to quotient via `Quotient.lift₂`.**

* [ ] **Step 3: Identity, category laws.**

* [ ] **Step 4: Commit.**

### Task θ.3: `HasChosenFiniteProducts`

**Files:**

* Modify: `GebLean/LawvereGodelTQuot.lean`.

* [ ] **Step 1: Define `terminal`, `fst`, `snd`, `pair`,
  uniqueness, etc.**

Mirroring the existing `LawvereERCat` shape, but with the
substitution-based `comp`.

* [ ] **Step 2: Commit.**

### Task θ.4: Faithful interp functor

**Files:**

* Create: `GebLean/LawvereGodelTInterp.lean`.

* [ ] **Step 1: Define functor.**

* [ ] **Step 2: Commit.**

### Stage θ completion criterion

* `Category LawvereGodelTCat` and `HasChosenFiniteProducts`
  built on the `≈`-quotient.

---

## Stage ι: Equivalence Nucleus ≌ LawvereERCat

Task ID: `#196`.

### Task ι.1: Derived T\* terms for ER constructors

**Files:**

* Create: `GebLean/Utilities/GodelTERTranslate.lean`.

* [ ] **Step 1: `succT`, `predT`, `subT`.**

```lean
def succT {n} : GodelTMor1 n → GodelTMor1 n
def predT {n} : GodelTMor1 n → GodelTMor1 n
def subT {n} : GodelTMor1 n → GodelTMor1 n → GodelTMor1 n
```

with `interp_*` lemmas.

* [ ] **Step 2: `bsumT`, `bprodT`.**

These need iter over a substituted body; complete with care.

* [ ] **Step 3: Commit.**

### Task ι.2: `erToGodelT` and tuple lift

**Files:**

* Create: `GebLean/LawvereGodelTERCatEquiv.lean`.

* [ ] **Step 1: Term-level translation.**

```lean
def ERMor1.toGodelT : ERMor1 n → GodelTMor1 n
  | .zero => -- arity-0 special case via app of K
  | .succ => -- arity-1
  -- ...
```

* [ ] **Step 2: Tuple lift; quotient lift; functor.**

* [ ] **Step 3: Commit.**

### Task ι.3: `godelTToER` via logical relations

**Files:**

* Modify: `GebLean/LawvereGodelTERCatEquiv.lean`.

* [ ] **Step 1: Define `GodelTRep`.**

```lean
def GodelTRep : {S : Set GodelTBase} → GodelTType S → Nat → Type
  | _, .base GodelTBase.nat _, n => ERMor1 n
  | _, .arrow σ τ, n => GodelTRep σ n → GodelTRep τ n
  | _, .base GodelTBase.tree _, _ => sorry  -- handled in BT extension
```

* [ ] **Step 2: Translation per constructor.**

Each constructor returns a `GodelTRep σ n`.  The `iter` case
uses `ERMor1.iterT` with adequacy from Lemma 16.

* [ ] **Step 3: Tuple lift; quotient lift; functor.**

* [ ] **Step 4: Commit.**

### Task ι.4: Equivalence assembly

**Files:**

* Modify: `GebLean/LawvereGodelTERCatEquiv.lean`.

* [ ] **Step 1: Round-trip lemmas and unit/counit isos.**

* [ ] **Step 2: `lawvereGodelTERCatEquivalence`.**

* [ ] **Step 3: Tests.**

### Stage ι completion criterion

* Categorical equivalence `LawvereGodelTCat ≌ LawvereERCat`
  fully proven.

---

## Stage κ: Binary-tree extension

Task ID: `#197`.

### Task κ.1: BT specialization

**Files:**

* Create: `GebLean/LawvereGodelTBT.lean`.

* [ ] **Step 1: Define the BT specialization abbreviations.**

```lean
abbrev SnatTree : Set GodelTBase := {GodelTBase.nat, GodelTBase.tree}

def hN_SnatTree : GodelTBase.nat ∈ SnatTree := by decide
def hT_SnatTree : GodelTBase.tree ∈ SnatTree := by decide

abbrev GodelTBTMor1Nat (n : Nat) :=
  GodelTTerm SnatTree n (.base .nat hN_SnatTree)
abbrev GodelTBTMor1Tree (n : Nat) :=
  GodelTTerm SnatTree n (.base .tree hT_SnatTree)
```

* [ ] **Step 2: Verify tree-side `Reduces` rules from γ.1
  apply.**

The `redTreeIter_leaf` and `redTreeIter_node` rules from γ
already cover the tree extension because `Reduces` is
parameterized over `S`.  Just specialize.

* [ ] **Step 3: Commit.**

### Task κ.2: Lemma 16 cases for tree primitives

**Files:**

* Modify: `GebLean/LawvereGodelTLemma16.lean` (extend existing
  proof's tree cases).

* [ ] **Step 1: Fill in the `leaf`, `node`, `treeIter` cases of
  `bracketLevel`.**

Per B-W's tree extension treatment (Section 5 of the paper),
which gives the tree-iter analogue's `[ ]_i` rules.

* [ ] **Step 2: Verify Lemma 16's structural induction now
  covers the tree cases.**

This may require small additional lemmas for tree-iter's
contraction.

* [ ] **Step 3: Commit.**

### Task κ.3: BT categorical structure

**Files:**

* Create: `GebLean/LawvereGodelTBTQuot.lean`.

* [ ] **Step 1: Pair-of-ℕ arities for BT objects.**

```lean
abbrev BTArity : Type := Nat × Nat

def BTArity.flat : BTArity → Nat
  | (n_nat, n_tree) => n_nat + n_tree

def GodelTBTMorN (a b : BTArity) := ... -- pair of nat-typed and tree-typed components
```

* [ ] **Step 2: Setoid, quotient, Category,
  HasChosenFiniteProducts.**

Mirror stage θ but with two morphism kinds (nat-output and
tree-output).

* [ ] **Step 3: Commit.**

### Stage κ completion criterion

* `LawvereGodelTBTCat` defined with binary product objects
  `(n_nat, n_tree)`.

---

## Stage λ: Szudzik-encoded equivalence BT ≌ Nucleus

Task ID: `#198`.

### Task λ.1: `treeCode` and `treeDecode`

**Files:**

* Create: `GebLean/LawvereGodelTBTSzudzik.lean`.

* [ ] **Step 1: Build Szudzik-style pair encoding inside the
  nucleus.**

Reuse `Utilities/SzudzikSeq.lean` infrastructure adapted to the
nucleus's primitives.

* [ ] **Step 2: `treeCode : GodelTMor1 1` (BTL → ℕ).**

```lean
def treeCode : GodelTMor1 1 := ... -- nuclear morphism
```

* [ ] **Step 3: `treeDecode : GodelTMor1 1` and the
  round-trip.**

* [ ] **Step 4: Commit.**

### Task λ.2: Forward functor `btToNucleus`

**Files:**

* Create: `GebLean/LawvereGodelTBTEquiv.lean`.

* [ ] **Step 1: Object map.**

`(n_nat, n_tree) ↦ n_nat + n_tree` (each tree slot replaced by a
single ℕ slot).

* [ ] **Step 2: Morphism map.**

For each `GodelTBTMor1Nat (n_nat, n_tree)` term, replace `leaf`
and `node` with their Szudzik-coded analogues; replace
`treeIter` with the `iter` over the encoded representation.

For each `GodelTBTMor1Tree (n_nat, n_tree)` term, the output
is a tree code at `GodelTMor1 (n_nat + n_tree)`.

* [ ] **Step 3: Functoriality (id + comp).**

* [ ] **Step 4: Commit.**

### Task λ.3: Backward functor `nucleusToBT`

**Files:**

* Modify: `GebLean/LawvereGodelTBTEquiv.lean`.

* [ ] **Step 1: Inclusion functor.**

Every nucleus morphism `n → 1` lifts to a BT morphism
`(n, 0) → (1, 0)` by re-interpreting at the larger
`SnatTree` parameter.

* [ ] **Step 2: Functoriality.**

* [ ] **Step 3: Commit.**

### Task λ.4: Equivalence assembly

**Files:**

* Modify: `GebLean/LawvereGodelTBTEquiv.lean`.

* [ ] **Step 1: Round-trip natural isos.**

* [ ] **Step 2: `lawvereGodelTBTEquivalence`.**

* [ ] **Step 3: Commit.**

### Stage λ completion criterion

* `LawvereGodelTBTCat ≌ LawvereGodelTCat` fully proven via
  Szudzik encoding.

---

## Stage μ: Cross-stage tests

Task ID: `#199`.

### Task μ.1: Lemma 16 sample tests

**Files:**

* Create: `GebLeanTests/LawvereGodelTLemma16.lean`.

* [ ] **Step 1: `#guard` Lemma 16 instances on small nucleus
  terms.**

```lean
example : (numeral hN_SnatOnly 5).bracketLevel 0 ≤
            tower 1 (1 + 2 * 11) := lemma16 _ 0 (by simp)
```

* [ ] **Step 2: Plausible property tests where natural.**

* [ ] **Step 3: Commit.**

### Task μ.2: Equivalence round-trip tests

**Files:**

* Create: `GebLeanTests/LawvereGodelTERCatEquiv.lean`.

* [ ] **Step 1: Round-trip `ERMor1` via toGodelT then
  godelTToER.**

* [ ] **Step 2: Sample programs (factorial, exponential).**

### Task μ.3: BT round-trip tests

**Files:**

* Create: `GebLeanTests/LawvereGodelTBT.lean`.

* [ ] **Step 1: Tree encoding round-trips.**

* [ ] **Step 2: Tree-recursive functions (size, depth, mirror,
  fold).**

* [ ] **Step 3: Plausible random tree round-trips.**

### Stage μ completion criterion

* All test files registered and passing under `lake test`.

---

## Stage ν: Programmer ergonomics (deferred)

Task ID: `#200`.

Adapts `Utilities/GodelTBracket.lean` to the variable-aware
representation; provides λ-style notation that elaborates via
bracket abstraction.

May be deferred indefinitely; not on the critical path.

### Task ν.1 onwards: deferred

---

## Execution notes

### Commit cadence

Every checkbox bullet corresponds to a commit-or-near-commit
state.  Commits should land at the end of each `**Step**` group
that produces a clean build.  Use the
`Co-Authored-By: Claude Opus 4.7 (1M context)
<noreply@anthropic.com>` trailer.

### Risk notes

* **Stage δ (Lemma 16) is the largest body of proof work.**
  Subdivide into helper lemmas aggressively.  Estimate 2-4
  weeks of work for an experienced Lean prover.
* **Stage ζ (confluence) requires the parallel-reduction
  technique** which is well-known but its bookkeeping in Lean
  is detail-heavy.  Consult mathlib for any existing
  Tait-Martin-Löf-flavored infrastructure.
* **Stage η's open-term completeness** requires the
  numeral-substitution argument.  Beckmann-Weiermann Section 4
  page 487 onwards is the reference.
* **Stage ι's logical-relations `godelTToER`** is the main
  new mathematical content beyond the SN/CR machinery.  The
  `iter` case uses `ERMor1.iterT` (already in the codebase
  from Task E.2, commit `4346b496`) with adequacy from
  Lemma 16.  The lifting between term arities under iter
  requires explicit Fin-shifting.

### Mathlib upstream candidacy

Per the design spec, the following modules are candidate
upstream contributions and should carry a docstring noting that:

* `LawvereGodelTTerm.lean` (`GodelTTerm` infrastructure).
* `LawvereGodelTLemma16.lean` (Lemma 16 tower bound; corresponds
  to `Mathlib.Computability.Elementary.TowerBound`).
* `LawvereGodelTQuot.lean` + `LawvereGodelTERCatEquiv.lean`
  (categorical Lawvere theory of ER).
* `LawvereGodelTBTEquiv.lean` (Szudzik-coded tree extension).

Each is self-contained.  Earmark by a single docstring line at
the top of each file noting the upstream candidacy.

---

## Self-review checklist (writer)

* [x] Spec coverage: each section of the spec maps to a stage
      in this plan.
* [x] B-W theorem (Lemma 16 + SN + CR + completeness) has
      its own dedicated stages (δ-η).
* [x] Equivalence preservation across the rebuild is structured
      stage-by-stage; each commit ends with `lake build` and
      `lake test` clean.
* [x] Files-to-create / files-to-delete enumerated.
* [x] CLAUDE.md rules inherited (line length, no `sorry`, etc.).
* [x] Tests planned for each stage.
* [x] B-W paper citation.
* [x] Existing infrastructure (Tasks E.1, E.2 from old plan)
      noted as preserved or repurposed.

---

## Resume prompt for fresh session

After landing this plan, follow-on sessions can resume with the
following invocation pattern:

> Continue executing the typed-term GodelT rebuild per the plan
> at `docs/superpowers/plans/2026-04-25-lawvere-godelt-typed-rebuild.md`.
> Spec at `docs/superpowers/specs/2026-04-25-lawvere-godelt-typed-design.md`.
> Workstream tracker at `.session/workstreams/lawvere-elementary-recursive.md`.
> Use `superpowers:subagent-driven-development` (recommended)
> or `superpowers:executing-plans`.
