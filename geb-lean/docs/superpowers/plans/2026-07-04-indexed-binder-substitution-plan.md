# Indexed binder-substitution kit implementation plan

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Global constraints](#global-constraints)
- [Consumed interfaces (verbatim, current pin)](#consumed-interfaces-verbatim-current-pin)
- [File structure](#file-structure)
- [Task 1: the binding signature and its endofunctor](#task-1-the-binding-signature-and-its-endofunctor)
- [Task 2: the term type](#task-2-the-term-type)
- [Task 3: thinnings](#task-3-thinnings)
- [Task 4: the generic traversal (the Kit)](#task-4-the-generic-traversal-the-kit)
- [Task 5: renaming](#task-5-renaming)
- [Task 6: substitution and the environment helpers](#task-6-substitution-and-the-environment-helpers)
- [Task 7: the substitution-lemma suite](#task-7-the-substitution-lemma-suite)
- [Task 8: the bundled `RelativeMonad`](#task-8-the-bundled-relativemonad)
- [Task 9: the STLC test calculus and area wiring](#task-9-the-stlc-test-calculus-and-area-wiring)
- [Self-review checklist (run before adversarial review)](#self-review-checklist-run-before-adversarial-review)
- [References](#references)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan task-by-task.
> Steps use checkbox (`- [ ]`) syntax for tracking. User review of this
> plan precedes any execution.

**Goal:** Build a reusable kit for intrinsically-typed syntax with
binders on the `PolyFix` stack — signatures, terms, renaming,
capture-avoiding substitution, the substitution-lemma suite, and a
bundled `RelativeMonad` abstraction — exercised on the simply-typed
lambda calculus.

**Architecture:** Terms are the free monad `PolyFreeM` of a
context-and-sort-indexed signature endofunctor over the diagonal
variable family (a single `PolyFix` over `Ctx × Ty`, generalizing the
repository's `RIdent`). Renaming and substitution are two instances of
one generic `PolyFix.ind` traversal (the Allais "Kit"); the law suite is
proved once, generic over the signature; the universal property is
packaged as a `RelativeMonad` instance in the Altenkirch-Chapman-Uustalu
framing.

**Tech Stack:** Lean 4 (toolchain pin `v4.29.0-rc6`), Lake, the
in-repository `PolyEndo`/`PolyFix`/`PolyFreeM` stack
(`GebLean/PolyAlg.lean`), `jj`, `markdownlint-cli2`, `doctoc`.

**Spec:**
`docs/superpowers/specs/2026-07-04-indexed-binder-substitution-design.md`.
Research note:
`docs/superpowers/notes/2026-07-04-binder-substitution-research.md`.

**Branch:** `feat/indexed-binder-substitution`, stacked on
`feat/ramified-p5-definability` (`d0c97ed5`). The research note and
design spec are its first two commits.

## Global constraints

Every task inherits these (spec sections 1.3, 1.4; `CLAUDE.md`;
`.claude/rules/lean-coding.md`):

- Decision 8: every recursive type is a `PolyFix` of a `PolyEndo`; no
  Lean-native recursive inductive types. `Var` and `Thinning` are
  first-order (non-recursive) indexing data and are exempt.
- No `noncomputable`; axiom hygiene (`propext`, `Quot.sound`,
  `Classical.choice` only, enforced by `lake build GebLeanAxiomChecks`);
  `sorry` never in a committed state (permitted only between the skill
  steps of a single task); `admit` never; use `_` for a genuine
  placeholder.
- Pre-commit Lean triad (`bash scripts/pre-commit.sh`: `lake test`,
  `lake lint`, `lake build GebLeanAxiomChecks`) before every commit that
  touches a `.lean` file; `doctoc --update-only` and
  `markdownlint-cli2` for every `.md`.
- `jj` only; no raw mutating `git`; no push without user line-by-line
  review.
- Commit messages `<type>(<scope>): <subject>`, imperative, lowercase,
  no trailing period, subject <= 72 chars, ending with the trailer
  `Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>`.
- Prose/naming style: `snake_case` theorems, `lowerCamelCase` defs,
  `UpperCamelCase` structures; module docstring `/-! -/` after imports;
  declaration docstrings on every `def`/`structure`/major theorem;
  citation at point of use (Allais et al. ICFP 2018,
  DOI `10.1145/3236785`; Altenkirch-Chapman-Uustalu FoSSaCS 2010; the
  research note for the universal property). All kit declarations live
  under `namespace GebLean.Binding`, avoiding collision with the
  `Ramified` clone laws.
- The append-at-end binder convention: a binder binding sorts `Ξ`
  extends the ambient context `Γ` to `Γ ++ Ξ`.
- **Elaboration-adjustment convention (binding scope of the code
  blocks):** the Lean signatures, equational contracts, and test bodies
  below are binding for names, arities, and semantic content; the
  precise implicit-argument placement, universe annotations, transport
  (`▸` / `cast`) bookkeeping, and tactic proofs are adjusted at
  elaboration time (the same convention the Phase 5 sub-plan used).
  A task is complete when its module builds, its tests pass, and the
  axiom gate is clean.

## Consumed interfaces (verbatim, current pin)

The substrate, from `GebLean/PolyAlg.lean` and `GebLean/Polynomial.lean`:

```lean
-- PolyAlg.lean:55 — indexed polynomial endofunctor on Over X
abbrev PolyEndo (X : Type u) : Cat := PolyFunctorBetweenCat X X
-- Polynomial.lean — a PolyEndo is built pointwise as a coproduct of
-- representables: `fun x => ccrObjMk (fun pos => Over.mk dir)`
-- (see the precedents below).

-- PolyAlg.lean:176 — the indexed W-type and its constructor
inductive PolyFix (P : PolyEndo X) : X → Type u
  | mk (x : X) (i : polyBetweenIndex X X P x)
      (children : ∀ e : (polyBetweenFamily X X P x i).left,
        PolyFix P ((polyBetweenFamily X X P x i).hom e)) : PolyFix P x
-- PolyAlg.lean:206 — the dependent eliminator (Sort-valued motive:
-- admits a function-typed motive, as Task 4 uses)
def PolyFix.ind {motive : ∀ {x}, PolyFix P x → Sort _}
    (step : …) {x} (t : PolyFix P x) : motive t

-- PolyAlg.lean:3293,:3344,:3950,:3980 — the free monad
def polyTranslate (A : Over X) (P : PolyEndo X) : PolyEndo X  -- A + P(-)
abbrev PolyFreeM (A : Over X) (P : PolyEndo X) (x : X) : Type u
  := PolyFix (polyTranslate A P) x
def polyFreeMPure (A) (P) {x} (a : {v // A.hom v = x}) : PolyFreeM A P x
def polyFreeMBind (A B : Over X) (P) {x} (t : PolyFreeM A P x)
    (f : ∀ y, {a : A.left // A.hom a = y} → PolyFreeM B P y) : PolyFreeM A P x
```

The closest precedents to copy (contexts-as-parameters, no binders):

```lean
-- GebLean/Ramified/Term.lean:93 — a signature endofunctor
def SortedSig.polyEndo (sig : SortedSig S) : PolyEndo S :=
  fun s => ccrObjMk fun o : { p : sig.Op // sig.result p = s } =>
    Over.mk (fun i : Fin (sig.arity o.val).length => (sig.arity o.val).get i)
-- Term.lean:100,:107,:113,:120 — varOver, Tm, var, op
def varOver (Γ : Ctx S) : Over S := Over.mk Γ.get
def Tm (sig) (Γ) : S → Type := PolyFreeM (varOver Γ) sig.polyEndo
def Tm.var {sig Γ} (i : Fin Γ.length) : Tm sig Γ (Γ.get i) :=
  polyFreeMPure (varOver Γ) sig.polyEndo ⟨i, rfl⟩
def Tm.op {sig Γ} (o) (args) : Tm sig Γ (sig.result o) :=
  PolyFix.mk (sig.result o) (Sum.inr ⟨o, rfl⟩) args

-- GebLean/Ramified/HigherOrder.lean:262,:271,:280,:288 — context-SHIFTING
-- directions (the pattern the binder signature generalizes)
def identTarget (A) (Γ) (τ) : (s : IdentShape A Γ τ) → IdentDir A Γ τ s →
    List RType × RType
  | Sum.inr (Sum.inl m), i => (m.params ++ List.replicate (A.ar i) τ, τ)  -- extends Γ
def identEndo (A : AlgSig) : PolyEndo (List RType × RType) :=
  fun idx => ccrObjMk fun s : IdentShape A idx.1 idx.2 =>
    Over.mk fun d : IdentDir A idx.1 idx.2 s => identTarget A idx.1 idx.2 s d
def RIdent (A) (Γ) (τ) : Type := PolyFix (identEndo A) (Γ, τ)
```

## File structure

New source under `GebLean/Binding/`; tests under
`GebLeanTests/Binding/`. Each source module is added to the directory
index `GebLean/Binding.lean` (created in Task 1), which is imported into
`GebLean.lean`; each test module is imported into
`GebLeanTests/Binding.lean` (created in Task 1), which is imported into
`GebLeanTests.lean`. This follows the `Ramified` / `GebLeanTests.Ramified`
precedent and ensures `lake build`, `lake test`, and the axiom gate all
cover the new modules.

| File | Contents | Task |
| --- | --- | --- |
| `GebLean/Binding/Signature.lean` | `Ctx`, `Var`, `BinderSig`, `BinderSig.polyEndo` | 1 |
| `GebLean/Binding/Term.lean` | `varOver`, `Tm`, `Tm.var`, `Tm.op`, simp lemmas | 2 |
| `GebLean/Binding/Thinning.lean` | `Thinning`, laws, `app`, `weakAppend` | 3 |
| `GebLean/Binding/Kit.lean` | `Kit`, `Env`, `traverse`, traversal simp lemmas | 4 |
| `GebLean/Binding/Renaming.lean` | `ren`, functoriality laws | 5 |
| `GebLean/Binding/Substitution.lean` | `sub`, `Env` helpers, `instantiate` | 6 |
| `GebLean/Binding/Laws.lean` | fusion + monoid laws | 7 |
| `GebLean/Binding/RelativeMonad.lean` | `RelativeMonad`, the `Tm` instance | 8 |
| `GebLean/Binding/Examples/Stlc.lean` | the STLC test calculus | 9 |
| `GebLean/Binding.lean` | directory index | 1, extended per task |
| `GebLeanTests/Binding/*.lean` | per-task test modules | each |
| `GebLeanTests/Binding.lean` | test directory index | 1, extended per task |

---

## Task 1: the binding signature and its endofunctor

**Files:**

- Create: `GebLean/Binding/Signature.lean`
- Create: `GebLean/Binding.lean` (directory index)
- Modify: `GebLean.lean` (add `import GebLean.Binding`)
- Create: `GebLeanTests/Binding/Signature.lean`
- Create: `GebLeanTests/Binding.lean` (test index)
- Modify: `GebLeanTests.lean` (add `import GebLeanTests.Binding`)

**Interfaces:**

- Consumes: `PolyEndo`, `ccrObjMk`, `Over.mk` (`GebLean/PolyAlg.lean`,
  `GebLean/Polynomial.lean`); the `SortedSig.polyEndo` / `identEndo`
  precedents.
- Produces:

```lean
abbrev Ctx (Ty : Type u) : Type u := List Ty
def Var (Γ : Ctx Ty) (s : Ty) : Type := { i : Fin Γ.length // Γ.get i = s }
structure BinderSig (Ty : Type u) where
  Op : Type u
  result : Op → Ty
  args : Op → List (Ctx Ty × Ty)     -- per argument: (bound sorts, sort)
def BinderSig.polyEndo (S : BinderSig Ty) : PolyEndo (Ctx Ty × Ty)
@[simp] theorem BinderSig.polyEndo_eval {S : BinderSig Ty} {Γ s} : …
  -- the spec §3.1 characterization: positions at (Γ, s) are
  -- { o // S.result o = s }; direction j targets (Γ ++ Ξ_j, t_j)
```

- [ ] **Step 1: write the failing test.** In
  `GebLeanTests/Binding/Signature.lean`:

```lean
import GebLean.Binding.Signature
namespace GebLean.Binding.Test
open GebLean.Binding
-- two positions of the same sort in a context are distinct data
-- (the anti-collapse property: Var is Type-valued, not Prop)
example : (⟨0, rfl⟩ : Var [true, true] true).1
        ≠ (⟨1, rfl⟩ : Var [true, true] true).1 := by decide
-- a variable's sort is read off its position
example : ((⟨1, rfl⟩ : Var [false, true] true)).1 = 1 := by decide
end GebLean.Binding.Test
```

- [ ] **Step 2: run to verify it fails.** Run:
  `lake build GebLeanTests.Binding.Signature`
  Expected: FAIL with `unknown identifier 'Var'` /
  `unknown namespace 'GebLean.Binding'`.

- [ ] **Step 3: implement.** Write `GebLean/Binding/Signature.lean` with
  the module docstring (`# Binding signatures`, main definitions,
  references to Allais et al. and the research note) and:

```lean
namespace GebLean.Binding
universe u
variable {Ty : Type u}

abbrev Ctx (Ty : Type u) : Type u := List Ty

/-- A variable: a `Type`-valued de Bruijn position into the context
whose sort is `s`. Not the `Prop` membership `s ∈ Γ`, which is
proof-irrelevant and would collapse distinct occurrences. First-order
data, exempt from decision 8. -/
def Var (Γ : Ctx Ty) (s : Ty) : Type := { i : Fin Γ.length // Γ.get i = s }

/-- A signature of operations with binding: each operation has a result
sort and a list of arguments; an argument `(Ξ, t)` is a subterm of sort
`t` in the ambient context extended by the bound sorts `Ξ` (append-at-end
convention). -/
structure BinderSig (Ty : Type u) where
  Op : Type u
  result : Op → Ty
  args : Op → List (Ctx Ty × Ty)

/-- The context-and-sort-indexed signature endofunctor (decision 8;
follows the context-shifting-direction pattern of `identEndo`,
`HigherOrder.lean:271`, with the append-at-end convention its own). At
output index `(Γ, s)` the positions are operations with result `s`; the
direction at argument `j = (Ξ, t)` targets the extended index
`(Γ ++ Ξ, t)`. -/
def BinderSig.polyEndo (S : BinderSig Ty) : PolyEndo (Ctx Ty × Ty) :=
  fun idx => ccrObjMk fun o : { o : S.Op // S.result o = idx.2 } =>
    Over.mk fun j : Fin (S.args o.val).length =>
      (idx.1 ++ ((S.args o.val).get j).1, ((S.args o.val).get j).2)

end GebLean.Binding
```

Create `GebLean/Binding.lean` with `import GebLean.Binding.Signature`;
add `import GebLean.Binding` to `GebLean.lean` (alphabetical position).
Create `GebLeanTests/Binding.lean` with
`import GebLeanTests.Binding.Signature`; add
`import GebLeanTests.Binding` to `GebLeanTests.lean`.

- [ ] **Step 4: run to verify it passes.** Run:
  `lake test` (builds `GebLeanTests` including the new module).
  Expected: PASS (no errors).

- [ ] **Step 5: pre-commit and commit.** Run `bash scripts/pre-commit.sh`
  (expect all green). Then:

```bash
jj describe -m "feat(binding): add binding signatures and their endofunctor

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
jj bookmark set feat/indexed-binder-substitution -r @
jj new
```

---

## Task 2: the term type

**Files:**

- Create: `GebLean/Binding/Term.lean`
- Modify: `GebLean/Binding.lean` (add import)
- Create: `GebLeanTests/Binding/Term.lean`
- Modify: `GebLeanTests/Binding.lean` (add import)

**Interfaces:**

- Consumes: `Var`, `BinderSig`, `BinderSig.polyEndo` (Task 1);
  `PolyFreeM`, `polyFreeMPure`, `PolyFix.mk`
  (`GebLean/PolyAlg.lean:3344,:3950,:176`); the `Tm`/`Tm.var`/`Tm.op`
  precedent (`Term.lean:107,:113,:120`).
- Produces:

```lean
def varOver : Over (Ctx Ty × Ty)
def Tm (S : BinderSig Ty) (Γ : Ctx Ty) (s : Ty) : Type
def Tm.var {S : BinderSig Ty} {Γ s} (x : Var Γ s) : Tm S Γ s
def Tm.op {S : BinderSig Ty} {Γ} (o : S.Op)
    (args : ∀ j : Fin (S.args o).length,
      Tm S (Γ ++ ((S.args o).get j).1) ((S.args o).get j).2) :
    Tm S Γ (S.result o)
```

- [ ] **Step 1: write the failing test.** In
  `GebLeanTests/Binding/Term.lean`:

```lean
import GebLean.Binding.Term
namespace GebLean.Binding.Test
open GebLean.Binding
-- a one-operation signature: a constant `k` of sort `()` (no args)
def sigK : BinderSig Unit := { Op := Unit, result := fun _ => (),
  args := fun _ => [] }
-- the constant is a closed term; a variable is a term
example : Tm sigK [] () := Tm.op () (fun j => j.elim0)
example : Tm sigK [()] () := Tm.var ⟨0, rfl⟩
end GebLean.Binding.Test
```

- [ ] **Step 2: run to verify it fails.** Run:
  `lake build GebLeanTests.Binding.Term`
  Expected: FAIL with `unknown identifier 'Tm'`.

- [ ] **Step 3: implement.** Write `GebLean/Binding/Term.lean` (module
  docstring citing the diagonal-leaf rationale of the research note
  section 4):

```lean
namespace GebLean.Binding
universe u
variable {Ty : Type u}

/-- The diagonal variable family: total space `Σ Γ, Fin Γ.length`, with
fiber over `(Γ, s)` equal to `Var Γ s`. The context is part of the index
(binders shift it), so the leaf object cannot depend on a fixed `Γ`. -/
def varOver : Over (Ctx Ty × Ty) :=
  Over.mk (fun p : (Σ Γ : Ctx Ty, Fin Γ.length) => (p.1, p.1.get p.2))

/-- Terms with binders over `S` at context `Γ` and sort `s`: the free
monad of `S.polyEndo` over the diagonal variable family, a single
`PolyFix` over `Ctx × Ty` (decision 8). -/
def Tm (S : BinderSig Ty) (Γ : Ctx Ty) (s : Ty) : Type :=
  PolyFreeM varOver S.polyEndo (Γ, s)

/-- A variable term (the free monad's unit at the variable's leaf). -/
def Tm.var {S : BinderSig Ty} {Γ : Ctx Ty} {s : Ty} (x : Var Γ s) :
    Tm S Γ s :=
  polyFreeMPure varOver S.polyEndo ⟨⟨Γ, x.1⟩, by simpa using x.2⟩

/-- An operation applied to a tuple of argument terms, each in the
ambient context extended by that argument's bound sorts. -/
def Tm.op {S : BinderSig Ty} {Γ : Ctx Ty} (o : S.Op)
    (args : ∀ j : Fin (S.args o).length,
      Tm S (Γ ++ ((S.args o).get j).1) ((S.args o).get j).2) :
    Tm S Γ (S.result o) :=
  PolyFix.mk (Γ, S.result o) (Sum.inr ⟨o, rfl⟩) args

end GebLean.Binding
```

Add `import GebLean.Binding.Term` to `GebLean/Binding.lean`; add
`import GebLeanTests.Binding.Term` to `GebLeanTests/Binding.lean`.
(The exact leaf-element packaging in `Tm.var` — the subtype proof
`by simpa using x.2` — is adjusted at elaboration per the
elaboration-adjustment convention; the precedent is
`Term.lean:113`'s `⟨i, rfl⟩`.)

- [ ] **Step 4: run to verify it passes.** Run: `lake test`.
  Expected: PASS.

- [ ] **Step 5: pre-commit and commit.** `bash scripts/pre-commit.sh`;
  then `jj describe -m "feat(binding): add the term type over the diagonal
  variable family"` (with trailer), `jj bookmark set …`, `jj new`.

---

## Task 3: thinnings

**Files:**

- Create: `GebLean/Binding/Thinning.lean`
- Modify: `GebLean/Binding.lean`, `GebLeanTests/Binding.lean` (imports)
- Create: `GebLeanTests/Binding/Thinning.lean`

**Interfaces:**

- Consumes: `Ctx`, `Var` (Task 1).
- Produces:

```lean
inductive Thinning : Ctx Ty → Ctx Ty → Type            -- keep/drop OPE
def Thinning.id {Γ} : Thinning Γ Γ
def Thinning.weak {Γ s} : Thinning Γ (s :: Γ)
def Thinning.lift {Γ Δ s} : Thinning Γ Δ → Thinning (s :: Γ) (s :: Δ)
def Thinning.weakAppend {Γ Ξ} : Thinning Γ (Γ ++ Ξ)
def Thinning.comp {Γ Δ Θ} : Thinning Γ Δ → Thinning Δ Θ → Thinning Γ Θ
def Thinning.app {Γ Δ s} : Thinning Γ Δ → Var Γ s → Var Δ s
theorem Thinning.app_id {Γ s} (x : Var Γ s) : Thinning.id.app x = x
theorem Thinning.app_comp {Γ Δ Θ s} (ρ : Thinning Γ Δ) (τ : Thinning Δ Θ)
    (x : Var Γ s) : (ρ.comp τ).app x = τ.app (ρ.app x)
```

`Thinning` is first-order data on `Ctx` (an inductive relation of
keep/drop steps, not `PolyFix` — decision 8 does not apply, spec
section 3.3). `List.Sublist` is `Prop`-valued and cannot compute `app`,
so a `Type`-valued relation is defined here.

- [ ] **Step 1: write the failing test.** In
  `GebLeanTests/Binding/Thinning.lean`:

```lean
import GebLean.Binding.Thinning
namespace GebLean.Binding.Test
open GebLean.Binding
-- weakening shifts the sole variable of [()] past a new head
example : (Thinning.weak.app (⟨0, rfl⟩ : Var [()] ())).1
        = (⟨1, rfl⟩ : Var [(), ()] ()).1 := by decide
-- app of the identity thinning is the identity
example (x : Var [()] ()) : Thinning.id.app x = x := Thinning.app_id x
end GebLean.Binding.Test
```

- [ ] **Step 2: run to verify it fails.** Run:
  `lake build GebLeanTests.Binding.Thinning`
  Expected: FAIL with `unknown identifier 'Thinning'`.

- [ ] **Step 3: implement.** Write `GebLean/Binding/Thinning.lean` with
  `Thinning` as the keep/drop OPE inductive, each declaration
  docstringed, and `app` acting on the `Fin`-index of a `Var`
  (transporting the sort proof). Prove `app_id` and `app_comp` by
  induction on the thinning. `weakAppend` is built from `weak`/`lift`
  (or directly by induction on `Γ`); `comp` is defined by recursion on
  the second thinning; `Thinning.id`/`weak`/`lift` are the constructors
  or immediate derivations.

- [ ] **Step 4: run to verify it passes.** Run: `lake test`.
  Expected: PASS.

- [ ] **Step 5: pre-commit and commit.** `bash scripts/pre-commit.sh`;
  `jj describe -m "feat(binding): add context thinnings and their variable
  action"` (with trailer); `jj bookmark set …`; `jj new`.

---

## Task 4: the generic traversal (the Kit)

This is the crux of the kit and the likely hard spot; commit
incrementally within the task (the `Kit`/`Env` scaffolding, then
`traverse`, then each simp lemma) and stop and report if the
environment-under-binder fold resists rather than grinding.

**Files:**

- Create: `GebLean/Binding/Kit.lean`
- Modify: `GebLean/Binding.lean`, `GebLeanTests/Binding.lean` (imports)
- Create: `GebLeanTests/Binding/Kit.lean`

**Interfaces:**

- Consumes: `Tm`, `Tm.var`, `Tm.op` (Task 2); `Thinning`,
  `Thinning.weakAppend`, `Thinning.app` (Task 3); `PolyFix.ind`
  (`GebLean/PolyAlg.lean:206`).
- Produces:

```lean
structure Kit (S : BinderSig Ty) (V : Ctx Ty → Ty → Type) where
  var  : ∀ {Γ s}, Var Γ s → V Γ s
  toTm : ∀ {Γ s}, V Γ s → Tm S Γ s
  wk   : ∀ {Γ Δ s}, Thinning Γ Δ → V Γ s → V Δ s
def Env (V : Ctx Ty → Ty → Type) (Γ Δ : Ctx Ty) : Type
  := ∀ (s : Ty), Var Γ s → V Δ s
def Env.underBinder {S V} (K : Kit S V) {Γ Δ Ξ} (ρ : Env V Γ Δ) :
    Env V (Γ ++ Ξ) (Δ ++ Ξ)   -- traverse-internal: weaken + add fresh vars
def varKit (S : BinderSig Ty) : Kit S Var                  -- the renaming Kit
def traverse {S V} (K : Kit S V) {Γ Δ s}
    (ρ : Env V Γ Δ) (t : Tm S Γ s) : Tm S Δ s
@[simp] theorem traverse_var {S V} (K : Kit S V) {Γ Δ s}
    (ρ : Env V Γ Δ) (x : Var Γ s) :
    traverse K ρ (Tm.var x) = K.toTm (ρ s x)
@[simp] theorem traverse_op {S V} (K : Kit S V) {Γ Δ} (ρ : Env V Γ Δ)
    (o) (args) :
    traverse K ρ (Tm.op o args)
      = Tm.op o (fun j => traverse K (Env.underBinder K ρ) (args j))
```

`varKit S` is the variables-Kit `{ var := id, toTm := Tm.var,
wk := Thinning.app }`; `Env.underBinder` (used only inside `traverse`)
weakens the old values along `Thinning.weakAppend` and maps the freshly
bound variables of `Ξ` to `K.var`.

- [ ] **Step 1: write the failing test** (deferred to the identity Kit
  built in Task 5's renaming; here the test exercises only the reduction
  equations against a trivial Kit). In `GebLeanTests/Binding/Kit.lean`:

```lean
import GebLean.Binding.Kit
namespace GebLean.Binding.Test
open GebLean.Binding
-- traverse of the identity environment over a variable reduces by
-- traverse_var to that variable, using the Kit.lean varKit
example (S : BinderSig Unit) (x : Var [()] ()) :
    traverse (varKit S) (fun _ y => y) (Tm.var x)
      = (varKit S).toTm x := by simp [traverse_var]
end GebLean.Binding.Test
```

- [ ] **Step 2: run to verify it fails.** Run:
  `lake build GebLeanTests.Binding.Kit`
  Expected: FAIL with `unknown identifier 'Kit'`.

- [ ] **Step 3a: implement `Kit`, `Env`, `varKit`, `Env.underBinder`.**
  `Env.underBinder K ρ` maps a variable of `Γ ++ Ξ`: split it with the
  append-variable eliminator (defined here or inlined) — a `Ξ`-variable
  maps to `K.var` of the corresponding fresh variable of `Δ ++ Ξ`; a
  `Γ`-variable maps to `K.wk Thinning.weakAppend (ρ s x)` (weaken the
  old value along the suffix embedding `Δ ⊆ Δ ++ Ξ`). `varKit S` is
  `{ var := id, toTm := Tm.var, wk := Thinning.app }`. Commit.

- [ ] **Step 3b: implement `traverse`** by `PolyFix.ind` with the
  environment-abstracting motive
  `motive {x} _ := ∀ Δ, Env V x.1 Δ → Tm S Δ x.2`. The step function
  cases the `polyTranslate` shape: a leaf (`Sum.inl`) recovers the
  `Var Γ s` and returns `fun Δ ρ => K.toTm (ρ s x)`; an operation node
  (`Sum.inr ⟨o, _⟩`) with per-direction induction hypotheses returns
  `fun Δ ρ => Tm.op o (fun j => IH j (Δ ++ Ξ_j) (Env.underBinder K ρ))`.
  Apply at `Δ`, `ρ`. Commit once it builds.

- [ ] **Step 3c: prove `traverse_var` and `traverse_op`** as the
  definitional/`PolyFix.ind`-computation lemmas (mark `@[simp]`). Commit.

- [ ] **Step 4: run to verify it passes.** Run: `lake test`.
  Expected: PASS (the `Kit.lean` test and all prior).

- [ ] **Step 5: pre-commit and commit.** `bash scripts/pre-commit.sh`;
  `jj describe -m "feat(binding): add the generic binder-aware traversal"`
  (with trailer); `jj bookmark set …`; `jj new`.

---

## Task 5: renaming

**Files:**

- Create: `GebLean/Binding/Renaming.lean`
- Modify: `GebLean/Binding.lean`, `GebLeanTests/Binding.lean` (imports)
- Create: `GebLeanTests/Binding/Renaming.lean`

**Interfaces:**

- Consumes: `traverse`, `Kit`, `Env`, `varKit` (Task 4); `Thinning`,
  `Thinning.id`, `Thinning.comp`, `Thinning.app` (Task 3).
- Produces:

```lean
def renEnv {Γ Δ} (ρ : Thinning Γ Δ) : Env Var Γ Δ    -- = fun s x => ρ.app x
def ren {S : BinderSig Ty} {Γ Δ s} (ρ : Thinning Γ Δ)
    (t : Tm S Γ s) : Tm S Δ s                          -- traverse (varKit S)
theorem ren_id {S Γ s} (t : Tm S Γ s) : ren Thinning.id t = t
theorem ren_comp {S Γ Δ Θ s} (ρ : Thinning Γ Δ) (τ : Thinning Δ Θ)
    (t : Tm S Γ s) : ren (ρ.comp τ) t = ren τ (ren ρ t)
```

`ren` is `traverse` at the variables-Kit `varKit`
(`var := id`, `toTm := Tm.var`, `wk := Thinning.app`) with the
environment `renEnv ρ`.

- [ ] **Step 1: write the failing test.** In
  `GebLeanTests/Binding/Renaming.lean`:

```lean
import GebLean.Binding.Renaming
namespace GebLean.Binding.Test
open GebLean.Binding
def sigK : BinderSig Unit := { Op := Unit, result := fun _ => (),
  args := fun _ => [] }
-- renaming by the identity thinning is the identity, on a variable
example (x : Var [()] ()) :
    ren (S := sigK) Thinning.id (Tm.var x) = Tm.var x := ren_id _
-- weakening a variable term shifts its index (via ren_comp/traverse_var)
example (x : Var [()] ()) :
    ren (S := sigK) Thinning.weak (Tm.var x)
      = Tm.var (Thinning.weak.app x) := by simp [ren, renEnv, traverse_var]
end GebLean.Binding.Test
```

- [ ] **Step 2: run to verify it fails.** Run:
  `lake build GebLeanTests.Binding.Renaming`
  Expected: FAIL with `unknown identifier 'ren'`.

- [ ] **Step 3: implement** `renEnv` and `ren := traverse (varKit S)
  (renEnv ρ)` (consuming `varKit` from Task 4), and prove
  `ren_id`/`ren_comp` by `PolyFix.ind` on the term using the `traverse`
  simp lemmas and `Thinning.app_id`/`app_comp` (Task 3).

- [ ] **Step 4: run to verify it passes.** Run: `lake test`.
  Expected: PASS.

- [ ] **Step 5: pre-commit and commit.** `bash scripts/pre-commit.sh`;
  `jj describe -m "feat(binding): add renaming and its functor laws"`
  (with trailer); `jj bookmark set …`; `jj new`.

---

## Task 6: substitution and the environment helpers

**Files:**

- Create: `GebLean/Binding/Substitution.lean`
- Modify: `GebLean/Binding.lean`, `GebLeanTests/Binding.lean` (imports)
- Create: `GebLeanTests/Binding/Substitution.lean`

**Interfaces:**

- Consumes: `traverse`, `Kit`, `Env` (Task 4); `ren` (Task 5);
  `Tm.var` (Task 2).
- Produces:

```lean
def subKit (S : BinderSig Ty) : Kit S (Tm S)             -- var:=Tm.var,
                                                          -- toTm:=id, wk:=ren
def sub {S : BinderSig Ty} {Γ Δ s} (σ : Env (Tm S) Γ Δ)
    (t : Tm S Γ s) : Tm S Δ s                            -- traverse subKit
def idEnv {S : BinderSig Ty} {Γ} : Env (Tm S) Γ Γ        -- fun s x => Tm.var x
def splitVar {Γ Ξ s} : Var (Γ ++ Ξ) s → Var Γ s ⊕ Var Ξ s
def extendEnv {S : BinderSig Ty} {Γ Δ Ξ} (σ : Env (Tm S) Γ Δ)
    (m : ∀ t, Var Ξ t → Tm S Δ t) : Env (Tm S) (Γ ++ Ξ) Δ
def instantiate {S : BinderSig Ty} {Γ Ξ s}
    (m : ∀ t, Var Ξ t → Tm S Γ t) (t : Tm S (Γ ++ Ξ) s) : Tm S Γ s
  -- := sub (extendEnv idEnv m) t
def instantiate₁ {S : BinderSig Ty} {Γ a s}
    (u : Tm S Γ a) (t : Tm S (Γ ++ [a]) s) : Tm S Γ s
  -- the single-variable specialization (beta / destructor substitution):
  -- instantiate at the singleton meta-map sending the sole bound
  -- variable of [a] to u, internalizing the Fin 1 / sort-proof transport
```

`instantiate₁` internalizes, once, the transport that a caller writing
`fun t v => …` would otherwise need (recover `a = t` from `v.2` and the
`Fin 1` singleton `v.1 = 0`, then move `u`); it is the single-variable
form every Phase-6 reduction uses (spec section 5's `instantiate` is the
general multi-variable form).

- [ ] **Step 1: write the failing test.** In
  `GebLeanTests/Binding/Substitution.lean`:

```lean
import GebLean.Binding.Substitution
namespace GebLean.Binding.Test
open GebLean.Binding
def sigK : BinderSig Unit := { Op := Unit, result := fun _ => (),
  args := fun _ => [] }
-- substituting by the identity environment is the identity, on a var
example (x : Var [()] ()) :
    sub (S := sigK) idEnv (Tm.var x) = Tm.var x := by
  simp [sub, idEnv, subKit, traverse_var]
-- instantiate₁ replaces the single bound variable of [()] ++ [()]
example (u : Tm sigK [()] ()) :
    instantiate₁ (Γ := [()]) (a := ()) u (Tm.var ⟨1, rfl⟩) = u := by
  simp [instantiate₁, instantiate, sub, extendEnv, idEnv, subKit, splitVar,
    traverse_var]
end GebLean.Binding.Test
```

- [ ] **Step 2: run to verify it fails.** Run:
  `lake build GebLeanTests.Binding.Substitution`
  Expected: FAIL with `unknown identifier 'sub'`.

- [ ] **Step 3: implement** `subKit`, `sub`, `idEnv`, `splitVar` (by
  comparing the position index against `Γ.length`), `extendEnv` (route
  each variable through `splitVar`: a `Γ`-variable to `σ`, a
  `Ξ`-variable to `m`), `instantiate := sub (extendEnv idEnv m)`, and
  `instantiate₁ u := instantiate (fun t v => …)` where the singleton
  meta-map sends the sole `[a]`-variable to `u` (recover `a = t` from
  `v.2` and `Subsingleton (Fin 1)`, then transport `u`). The
  `instantiate₁` test may need one auxiliary `@[simp]` lemma on
  `splitVar` at a concrete index; add it if the `simp` does not close.

- [ ] **Step 4: run to verify it passes.** Run: `lake test`.
  Expected: PASS.

- [ ] **Step 5: pre-commit and commit.** `bash scripts/pre-commit.sh`;
  `jj describe -m "feat(binding): add substitution and the environment
  helpers"` (with trailer); `jj bookmark set …`; `jj new`.

---

## Task 7: the substitution-lemma suite

The second likely hard spot; prove and commit one law at a time (each is
an independent `PolyFix.ind` on the term). Stop and report if a fusion
law resists rather than grinding.

**Files:**

- Create: `GebLean/Binding/Laws.lean`
- Modify: `GebLean/Binding.lean`, `GebLeanTests/Binding.lean` (imports)
- Create: `GebLeanTests/Binding/Laws.lean`

**Interfaces:**

- Consumes: `ren`, `ren_id`, `ren_comp` (Task 5); `sub`, `idEnv`,
  `subKit` (Task 6); the `traverse` simp lemmas and `Env.underBinder`
  (Task 4).
- Produces:

```lean
theorem ren_sub {S Γ Δ Θ s} (ρ : Thinning Γ Δ) (σ : Env (Tm S) Δ Θ)
    (t : Tm S Γ s) : sub σ (ren ρ t) = sub (fun s x => σ s (ρ.app x)) t
theorem sub_ren {S Γ Δ Θ s} (σ : Env (Tm S) Γ Δ) (ρ : Thinning Δ Θ)
    (t : Tm S Γ s) : ren ρ (sub σ t) = sub (fun s x => ren ρ (σ s x)) t
theorem sub_var {S Γ Δ s} (σ : Env (Tm S) Γ Δ) (x : Var Γ s) :
    sub σ (Tm.var x) = σ s x            -- left unit
theorem sub_id {S Γ s} (t : Tm S Γ s) : sub idEnv t = t    -- right unit
theorem sub_sub {S Γ Δ Θ s} (σ : Env (Tm S) Γ Δ)
    (τ : Env (Tm S) Δ Θ) (t : Tm S Γ s) :
    sub τ (sub σ t) = sub (fun s x => sub τ (σ s x)) t      -- assoc
-- the under-binder interaction lemmas the operation case of each law
-- needs (how ren/sub commute with going under a binder, i.e. with
-- Env.underBinder); named so the executor sees the real sub-goals:
theorem underBinder_ren {S V Γ Δ Ξ} (K : Kit S V) (ρ : Env V Γ Δ) : …
theorem underBinder_sub {S V Γ Δ Ξ} (K : Kit S V) (ρ : Env V Γ Δ) : …
```

- [ ] **Step 1: write the failing test.** In
  `GebLeanTests/Binding/Laws.lean`:

```lean
import GebLean.Binding.Laws
namespace GebLean.Binding.Test
open GebLean.Binding
def sigK : BinderSig Unit := { Op := Unit, result := fun _ => (),
  args := fun _ => [] }
-- the left-unit law on a concrete variable
example (σ : Env (Tm sigK) [()] [()]) (x : Var [()] ()) :
    sub σ (Tm.var x) = σ () x := sub_var σ x
-- the right-unit law
example (t : Tm sigK [()] ()) : sub idEnv t = t := sub_id t
end GebLean.Binding.Test
```

- [ ] **Step 2: run to verify it fails.** Run:
  `lake build GebLeanTests.Binding.Laws`
  Expected: FAIL with `unknown identifier 'sub_var'`.

- [ ] **Step 3: implement**, one law per commit, by `PolyFix.ind` on
  `t` using the `traverse` simp lemmas, the `Env.underBinder`
  interaction lemmas `underBinder_ren`/`underBinder_sub` (how `ren`/`sub`
  commute with going under a binder — the operation case's central
  sub-goals, proved first), and the renaming laws. Order: `sub_var`
  (`rfl`/`traverse_var`), then `underBinder_ren`/`underBinder_sub`, then
  `ren_sub` and `sub_ren` (push `ren`/`sub` under binders), then
  `sub_id`, then `sub_sub` (uses `ren_sub`/`sub_ren` at the binder case).

- [ ] **Step 4: run to verify it passes.** Run: `lake test`.
  Expected: PASS.

- [ ] **Step 5: pre-commit and commit** (the final law's commit;
  earlier laws already committed per the incremental guidance).
  `bash scripts/pre-commit.sh`;
  `jj describe -m "feat(binding): prove the substitution-lemma suite"`
  (with trailer); `jj bookmark set …`; `jj new`.

---

## Task 8: the bundled `RelativeMonad`

**Files:**

- Create: `GebLean/Binding/RelativeMonad.lean`
- Modify: `GebLean/Binding.lean`, `GebLeanTests/Binding.lean` (imports)
- Create: `GebLeanTests/Binding/RelativeMonad.lean`

**Interfaces:**

- Consumes: `Tm`, `Tm.var` (Task 2); `sub`, `idEnv` (Task 6);
  `sub_var`, `sub_id`, `sub_sub` (Task 7).
- Produces:

```lean
structure RelativeMonad {J0 : Type u} {C : Type v} (J : J0 → C)
    (hom : C → C → Type w) (T : J0 → C) where
  unit : ∀ X, hom (J X) (T X)
  ext  : ∀ {X Y}, hom (J X) (T Y) → hom (T X) (T Y)
  ext_unit : ∀ {X Y} (k : hom (J X) (T Y)), … -- ext k ∘ unit = k
  unit_ext : ∀ {X}, ext (unit X) = id …        -- ext unit = id
  ext_ext  : ∀ {X Y Z} (k) (l), …              -- ext l ∘ ext k = ext (ext l ∘ k)
def Tm.relativeMonad (S : BinderSig Ty) :
    RelativeMonad (J0 := Ctx Ty) (fun Γ => (fun s => Var Γ s))
      (fun X Y => ∀ s, X s → Y s) (fun Γ => Tm S Γ)
```

The ambient category is `C = Set^Ty` (`fun s => _`), `J0 = Ctx`,
`hom X Y = ∀ s, X s → Y s`, `unit = Tm.var`, `ext = sub` (spec
section 3.7). The three law fields are exactly `sub_var`, `sub_id`,
`sub_sub` (Task 7), possibly after `funext`.

- [ ] **Step 1: write the failing test.** In
  `GebLeanTests/Binding/RelativeMonad.lean`:

```lean
import GebLean.Binding.RelativeMonad
namespace GebLean.Binding.Test
open GebLean.Binding
def sigK : BinderSig Unit := { Op := Unit, result := fun _ => (),
  args := fun _ => [] }
-- the relative monad exists and its ext is sub on a concrete term
example (t : Tm sigK [()] ()) :
    (Tm.relativeMonad sigK).ext (fun s x => Tm.var x) () t = t := by
  simpa using sub_id t
end GebLean.Binding.Test
```

- [ ] **Step 2: run to verify it fails.** Run:
  `lake build GebLeanTests.Binding.RelativeMonad`
  Expected: FAIL with `unknown identifier 'RelativeMonad'`.

- [ ] **Step 3: implement** the `RelativeMonad` structure (each field
  docstringed; the three law fields stated as the equalities above,
  spelled out with the concrete `hom`) and `Tm.relativeMonad`, whose
  law fields are discharged from `sub_var`/`sub_id`/`sub_sub` (via
  `funext` where a pointwise law is needed). The module docstring
  records the initial-Sigma-monoid / free-relative-monad reading and the
  deferred `Mon_` convergence target (spec sections 3.7, 8).

- [ ] **Step 4: run to verify it passes.** Run: `lake test`.
  Expected: PASS.

- [ ] **Step 5: pre-commit and commit.** `bash scripts/pre-commit.sh`;
  `jj describe -m "feat(binding): package substitution as a relative
  monad"` (with trailer); `jj bookmark set …`; `jj new`.

---

## Task 9: the STLC test calculus and area wiring

**Files:**

- Create: `GebLean/Binding/Examples/Stlc.lean`
- Modify: `GebLean/Binding.lean`, `GebLeanTests/Binding.lean` (imports)
- Create: `GebLeanTests/Binding/Stlc.lean`

**Interfaces:**

- Consumes: the whole kit (Tasks 1-8).
- Produces:

```lean
inductive StlcTy : Type | base | arrow (a b : StlcTy)
def stlcSig : BinderSig StlcTy      -- app : (a⇒b), a → b ; lam : binds a, body b
def stlcBody (a : StlcTy) : Tm stlcSig [a] a := Tm.var ⟨0, rfl⟩  -- the bound var
def stlcId (a : StlcTy) : Tm stlcSig [] (StlcTy.arrow a a)   -- λx. x
```

`stlcSig` has two operation families: `app a b` with
`args = [([], StlcTy.arrow a b), ([], a)]` and result `b`; `lam a b`
with `args = [([a], b)]` (binds one `a`) and result
`StlcTy.arrow a b`. (`Op` is the sum of the two index families;
elaboration fixes the encoding.)

- [ ] **Step 1: write the failing test.** In
  `GebLeanTests/Binding/Stlc.lean`:

```lean
import GebLean.Binding.Examples.Stlc
namespace GebLean.Binding.Test
open GebLean.Binding
-- the identity term is well-formed and beta-instantiating it at a
-- closed argument returns the argument
-- stlcBody a : Tm stlcSig [a] a := Tm.var ⟨0, rfl⟩; here Γ = [], so
-- Γ ++ [a] = [a], and instantiate₁ returns the closed argument u
example (a : StlcTy) (u : Tm stlcSig [] a) :
    instantiate₁ (Γ := []) (a := a) u (stlcBody a) = u := by
  simp [stlcBody, instantiate₁, instantiate, sub, extendEnv, idEnv,
    subKit, splitVar, traverse_var]
end GebLean.Binding.Test
```

- [ ] **Step 2: run to verify it fails.** Run:
  `lake build GebLeanTests.Binding.Stlc`
  Expected: FAIL with `unknown identifier 'stlcSig'`.

- [ ] **Step 3: implement** `StlcTy`, `stlcSig`, `stlcBody`, `stlcId`,
  and worked `example`s exercising `var`, `ren`, `sub`, `instantiate`,
  and each law on concrete STLC terms (the acceptance test). Confirm
  `GebLean/Binding.lean` imports every submodule and
  `GebLean/Binding/Examples/Stlc.lean`; confirm `GebLeanTests/Binding.lean`
  imports every test module.

- [ ] **Step 4: run to verify it passes.** Run: `lake test`.
  Expected: PASS (the whole `Binding` test tree).

- [ ] **Step 5: pre-commit and commit.** `bash scripts/pre-commit.sh`;
  `jj describe -m "feat(binding): add the STLC example and wire the area
  index"` (with trailer); `jj bookmark set …`; `jj new`.

---

## Self-review checklist (run before adversarial review)

- Every spec section 3 component maps to a task: 3.1 -> Task 1;
  3.2 -> Task 2; 3.3 -> Task 3; 3.4 -> Task 4; 3.5 -> Tasks 5-6;
  3.6 -> Task 7; 3.7 -> Task 8; 3.8 -> Task 9. The spec section 5
  `Env` helpers map to Task 6.
- No placeholder text; every code step shows concrete signatures/tests;
  proof tactics are covered by the elaboration-adjustment convention
  (stated in Global constraints), which the Phase 5 sub-plan established.
- Names agree across tasks: `Ctx`, `Var`, `BinderSig`,
  `BinderSig.polyEndo`, `varOver`, `Tm`, `Tm.var`, `Tm.op`, `Thinning`,
  `Thinning.app`/`id`/`weak`/`lift`/`weakAppend`/`comp`,
  `Thinning.app_id`/`app_comp`, `Kit`, `Env`, `varKit`,
  `Env.underBinder`, `underBinder_ren`/`underBinder_sub`, `traverse`,
  `traverse_var`, `traverse_op`, `renEnv`, `ren`, `ren_id`, `ren_comp`,
  `subKit`, `sub`, `idEnv`, `splitVar`, `extendEnv`, `instantiate`,
  `instantiate₁`, `ren_sub`, `sub_ren`, `sub_var`, `sub_id`, `sub_sub`,
  `RelativeMonad`, `Tm.relativeMonad`, `StlcTy`, `stlcSig`, `stlcBody`,
  `stlcId`.
- Substrate signatures quoted match the current pin (file:line given in
  Consumed interfaces).

## References

- Spec:
  `docs/superpowers/specs/2026-07-04-indexed-binder-substitution-design.md`.
- Research note (universal property, substrate map):
  `docs/superpowers/notes/2026-07-04-binder-substitution-research.md`.
- G. Allais et al., "A Type- and Scope-Safe Universe of Syntaxes with
  Binding", ICFP 2018, DOI `10.1145/3236785`.
- T. Altenkirch, J. Chapman, T. Uustalu, "Monads Need Not Be
  Endofunctors", FoSSaCS 2010, DOI `10.1007/978-3-642-12032-9_21`.
