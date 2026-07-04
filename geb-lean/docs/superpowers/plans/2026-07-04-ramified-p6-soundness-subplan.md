# Ramified recurrence Phase 6 (soundness) sub-plan

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Global constraints](#global-constraints)
- [Consumed interfaces (verbatim, current pin)](#consumed-interfaces-verbatim-current-pin)
  - [The binder-substitution kit (`GebLean/Binding/*`; L1, landed)](#the-binder-substitution-kit-gebleanbinding-l1-landed)
  - [The ramified side (Phases 1-5)](#the-ramified-side-phases-1-5)
  - [The ER / K-sim landing (pre-existing)](#the-er--k-sim-landing-pre-existing)
- [Standing decisions recorded by this sub-plan](#standing-decisions-recorded-by-this-sub-plan)
- [File structure](#file-structure)
- [Execution notes](#execution-notes)
- [Sub-phase 6.1 (L2): the applicative calculi and Proposition 7](#sub-phase-61-l2-the-applicative-calculi-and-proposition-7)
  - [Task 6.1a: the applicative signatures](#task-61a-the-applicative-signatures)
  - [Task 6.1b: the reduction relations](#task-61b-the-reduction-relations)
  - [Task 6.1c: Proposition 7 (1) to (3) — the eq. (9) translation](#task-61c-proposition-7-1-to-3--the-eq-9-translation)
  - [Task 6.1d: Proposition 7 (3) to (4) — case/dstr from F](#task-61d-proposition-7-3-to-4--casedstr-from-f)
- [Sub-phase 6.2 (L3): representation in `1λ(A)` — gated](#sub-phase-62-l3-representation-in-1%CE%BBa--gated)
- [Sub-phase 6.3 (L4): the normalization bound — gated](#sub-phase-63-l4-the-normalization-bound--gated)
- [Sub-phase 6.4 (L5): the landing normalizer — gated](#sub-phase-64-l5-the-landing-normalizer--gated)
- [Sub-phase 6.5 (L6): the collapse packaging](#sub-phase-65-l6-the-collapse-packaging)
  - [Task 6.5a: `SynCatFO` and `collapseDenotation`](#task-65a-syncatfo-and-collapsedenotation)
  - [Task 6.5b: `collapseFunctor` and faithfulness](#task-65b-collapsefunctor-and-faithfulness)
- [Self-review checklist (run before adversarial review)](#self-review-checklist-run-before-adversarial-review)
- [References](#references)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan task-by-task.
> Steps use checkbox (`- [ ]`) syntax for tracking. User review of this
> sub-plan precedes any execution.

**Goal:** Prove the soundness direction of the ramified-recurrence
characterization — every morphism between object-sort contexts of
`RMRecCat natAlgSig` denotes an elementary recursive function — and
package it as `collapseFunctor : SynCatFO (higherOrder natAlgSig) _ =>
LawvereERCat` with `Faithful`, by transcribing Leivant III sections 4-5
(route L, fixed by gates G1/G2/G3).

**Architecture:** Route L, all transcription. The applicative calculi
`RλMR-omega` / `RλMR-omega_o` and the representation calculus `1λ(A)`
are instantiated as `BinderSig` instances of the landed
indexed-binder-substitution kit (`GebLean/Binding/*`), so their terms,
renaming, capture-avoiding substitution, and β-reduction come from the
kit. Proposition 7 translates `RMRec-omega` into the applicative
calculus; Proposition 11 represents it in `1λ(A)`; Lemma 12 and
Proposition 13 bound normalization time by `O((2_{q+1}(h))^2)`; the
landing implements the normalizer on term codes as a clocked
`K`-morphism, transferred to ER across `erKSimEquiv`. `collapseFunctor`
packages the result; well-definedness and faithfulness are by
construction with interpretative hom-sets, the substance being the
normalization argument.

**Tech Stack:** Lean 4 (toolchain pin `v4.29.0-rc6`), Lake, the
in-repository `PolyEndo`/`PolyFix` stack, the `Binding` kit, the
`LawvereER`/`LawvereKSim` layers, `jj`, `markdownlint-cli2`, `doctoc`.

**Master plan (fixes Phase 6's boundaries, route, decisions):**
`docs/superpowers/plans/2026-07-02-ramified-recurrence-plan.md` (Phase 6).
**Gate record (G1 no-bridge, G2 no-reuse, G3 K^sim landing):**
`docs/superpowers/notes/2026-07-02-ramified-gates-decisions.md`.
**Spec (s6.3 route, s6.4 landing):**
`docs/superpowers/specs/2026-07-01-ramified-recurrence-approaches-design.md`.

**Branch:** `feat/ramified-p6-soundness`, stacked on the binder-kit tip
`feat/indexed-binder-substitution` (`6aa43899`), which is itself stacked
on `feat/ramified-p5-definability`. Phase 6 therefore sees both the
ramified Phases 1-5 and the `Binding` kit.

**Source (do not commit; cite DOI `10.1016/S0168-0072(98)00040-2`):**
Leivant III local PDF at `/home/terence/wingeb/`; Phase 6 transcribes
sections 4-5 (paper pp. 222-229). The mathematical digest supporting
this sub-plan is reproduced task-by-task below.

## Global constraints

The master plan's Global constraints apply verbatim (toolchain pin; no
`noncomputable`; axiom hygiene enforced by `lake build
GebLeanAxiomChecks`; `sorry` only between skill steps, never committed;
`admit` never; pre-commit Lean triad before every `.lean` commit;
markdownlint + doctoc for every `.md`; `jj` only, no push without user
line-by-line review; commit messages `<type>(<scope>): <subject>`
imperative lowercase no-trailing-period <=72 chars ending with
`Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>`;
generic user references; prose style; citation-at-point-of-use;
decision 8 — every recursive type is a `PolyFix` of a `PolyEndo`).

Phase-specific:

- **Transcription fidelity.** Every definition and theorem carries its
  Leivant III section/lemma/equation number and the DOI. The
  transcription-versus-novel status of each construct is recorded in
  its docstring; novel packaging (the `collapseFunctor` assembly, the
  term-code landing) is marked as such.
- **Elaboration-adjustment convention** (as the Phase 5 and binder-kit
  plans): the Lean signatures, equational contracts, and test bodies
  below are binding for names, arities, and semantic content; exact
  implicit-argument placement, universe annotations, transport
  bookkeeping, and tactic proofs are settled at elaboration. A task is
  complete when its module builds, its tests pass, and the axiom gate
  is clean.
- **No `#guard` on clocked composites.** Per the pitfalls record,
  interpretations of clocked machine composites and deep normalization
  chains are never `#guard`-ed; state `example` proofs from the
  interpretation lemmas instead.

## Consumed interfaces (verbatim, current pin)

### The binder-substitution kit (`GebLean/Binding/*`; L1, landed)

```lean
-- Signature.lean
abbrev Ctx (Ty : Type u) : Type u := List Ty
def Var (Γ : Ctx Ty) (s : Ty) : Type := { i : Fin Γ.length // Γ.get i = s }
structure BinderSig (Ty : Type u) where
  Op : Type u ; result : Op → Ty ; args : Op → List (Ctx Ty × Ty)
def BinderSig.polyEndo (S : BinderSig Ty) : PolyEndo (Ctx Ty × Ty)
-- Term.lean
def Tm (S : BinderSig Ty) (Γ : Ctx Ty) (s : Ty) : Type
def Tm.var {S Γ s} (x : Var Γ s) : Tm S Γ s
def Tm.op {S Γ} (o : S.Op)
    (args : ∀ j : Fin (S.args o).length,
      Tm S (Γ ++ ((S.args o).get j).1) ((S.args o).get j).2) : Tm S Γ (S.result o)
-- Thinning.lean / Renaming.lean
inductive Thinning : Ctx Ty → Ctx Ty → Type
def ren {S Γ Δ s} (ρ : Thinning Γ Δ) (t : Tm S Γ s) : Tm S Δ s
theorem ren_id … ; theorem ren_comp …
-- Substitution.lean
def Env (V) (Γ Δ) : Type := ∀ s, Var Γ s → V Δ s
def sub {S Γ Δ s} (σ : Env (Tm S) Γ Δ) (t : Tm S Γ s) : Tm S Δ s
def idEnv {S Γ} : Env (Tm S) Γ Γ
def instantiate₁ {S Γ a s} (u : Tm S Γ a) (t : Tm S (Γ ++ [a]) s) : Tm S Γ s
-- Laws.lean
theorem sub_var … ; theorem ren_sub … ; theorem sub_ren …
theorem sub_id … ; theorem sub_sub …            -- the substitution monoid laws
-- RelativeMonad.lean
def Tm.relativeMonad (S : BinderSig Ty) : RelativeMonad …
```

`Ty : Type 0` on the substitution layer (kit limitation, adjudicated);
the Leivant calculi's sort types (r-types, simple types) are `Type 0`,
so this does not bind.

### The ramified side (Phases 1-5)

```lean
-- Definability/Top.lean
def ObjCtx (n : ℕ) : Type := Fin n → { s : RType // s.IsObj }
def oCtx (m : ℕ) : ObjCtx m
def ramifiedDenotation {n m} {Γ : ObjCtx n} {Δ : ObjCtx m}
    (g : Hom (higherOrder natAlgSig) (interpQuotRel _) Γ.toCtx Δ.toCtx) :
    (Fin n → ℕ) → (Fin m → ℕ)
theorem erMor_ramified_definable {a} (e : ERMor1 a) : …   -- Phase 5 (Lemma 6)
-- Interp.lean / HigherOrder.lean
def interpSetoid … ; def interpQuotRel (P : Presentation) : QuotRel P.sig
abbrev RMRecCat (A : AlgSig) := SynCat (higherOrder A) (interpQuotRel (higherOrder A))
def standardModel (P : Presentation) : SortedModel P.sig
def Hom.eval … ; def HomTuple.eval …
-- Algebras.lean
def natFreeAlgEquiv : FreeAlg natAlgSig ≃ ℕ
```

### The ER / K-sim landing (pre-existing)

```lean
-- LawvereER.lean
def ERMorN (n m : ℕ) : Type := Fin m → ERMor1 n
def erMorNSetoid (n m : ℕ) : Setoid (ERMorN n m)     -- extensional interp equality
-- LawvereERKSim/Equivalence.lean:183 (+96,:126 strict round-trips)
def erKSimEquiv : LawvereERCat ≌ LawvereKSimDCat 2
-- Utilities/KSimURMSimulator.lean:544 — the executed clocked-simulator pattern
def KSimURMSimulator.simulate {a} (P : URMProgram a) : KMor1 (a + 1)
-- Utilities/Tower.lean — the tower bound `tower : ℕ → ℕ → ℕ` and its monotonicity
-- Mathlib.CategoryTheory.ObjectProperty.FullSubcategory — the SynCatFO idiom
--   (precedent: GebLean/LawvereNatBT0.lean)
```

## Standing decisions recorded by this sub-plan

1. **The calculi are `BinderSig` instances.** `RλMR-omega`,
   `RλMR-omega_o`, and `1λ(A)` are each a `BinderSig` over their sort
   type (r-types for the first two, simple types for `1λ(A)`), with the
   constants (`c_i^θ`, `R^τ`, `F^τ` / `dstr` / `case`) and application
   and abstraction as operations. This realizes decision 8's "PolyFix of
   indexed signature endofunctors" via the kit (`BinderSig.polyEndo`).
   The reductions (β, η, recurrence, flat) are relations on `Tm`,
   defined with `instantiate₁`/`sub` for the substitution steps.
2. **K^sim landing (G3 default, confirmed).** The normalizer's natural
   presentation is a state-transition step function on term codes (one
   reduction step per tick), matching the `KSimURMSimulator` /
   `erToKFunctor` precedent; it is realized K^sim-side and transferred
   across `erKSimEquiv`. The ER alternative landing is not taken: the step
   function is not naturally ER-side arithmetic. Reason recorded here per
   G3's caveat.
3. **Two-level plan depth (no-speculation).** Sub-phases 6.1 (L2) and
   6.5 (collapse) are fully bite-sized. Sub-phases 6.2 (L3, the
   representation and Prop 11), 6.3 (L4, Lemma 12 / Prop 13), and 6.4
   (L5, the normalizer landing) carry deliverable and interface detail
   with their internal proof-step detail gated to an execution-time
   mini-sub-plan written after their prerequisites land. This mirrors the
   master plan's own Phase 6 gate and the Phase 5 Task 5.4 / Era 6.4c
   precedents: fabricating the step detail of the Lemma 12
   normalization-time argument or the normalizer's semantic-adequacy
   proof before the calculi and codes exist would violate the
   no-speculation discipline. Each mini-sub-plan is itself
   adversarially reviewed and user-reviewed before its execution.
4. **`collapseDenotation` is `ramifiedDenotation`.** The master plan's
   `collapseDenotation` is the Phase 5 `ramifiedDenotation`
   (`Definability/Top.lean`), restated as the standard-model
   interpretation of an object-sort-context morphism read through
   `natFreeAlgEquiv` into `(Fin n → ℕ) → (Fin m → ℕ)`. `SynCatFO` is the
   full subcategory of `RMRecCat natAlgSig` on object-sort contexts,
   via `ObjectProperty.FullSubcategory`. Because the in-scope proof is
   hosted over `natAlgSig` (master-plan decision 3), `SynCatFO` is the
   `natAlgSig` instance of the master plan's general
   `SynCatFO (P) (r)`; the general two-argument form is the interface,
   this sub-plan instantiates it, and Phase 7's `SynCatFO` consumption
   reads the instantiated form.
5. **Decision 8 governs recursive data, not Prop relations.** Decision 8
   ("every recursive type is a `PolyFix` of a `PolyEndo`") secures the
   constructive-only guarantee for executable data. Prop-valued
   inductively-defined relations — the reduction relations of 6.1
   (`RlmrOStep` and its variants), normality, and the representation
   relation of 6.2 — are proofs, not computational objects, so they are
   exempt, exactly as the landed kit exempts the first-order data `Var`
   and `Thinning` (`GebLean/Binding/Signature.lean:60`,
   `Thinning.lean:52`, each with an "exempt from decision 8" docstring).
   Each such relation carries the same exemption docstring. Reflexive-
   transitive closures reuse mathlib `Relation.ReflTransGen` rather than
   a bespoke recursive `Reduces` (reuse rule). Any recursive `def` that
   is Type-valued data (for example a term-code function) remains bound
   by decision 8 and is a `PolyFix` or a structurally-recursive function
   over one.

## File structure

New source under `GebLean/Ramified/Soundness/`; tests under
`GebLeanTests/Ramified/Soundness/`. Directory index
`GebLean/Ramified/Soundness.lean` imported into the ramified index.

| File | Contents | Sub-phase |
| --- | --- | --- |
| `Soundness/Applicative.lean` | `rlmrSig`/`rlmrOSig` (`BinderSig`), the reductions, Prop 7 translation | 6.1 |
| `Soundness/OneLambda.lean` | `oneLambdaSig`, Berarducci-Böhm `a^σ`, bar-translation, Prop 11 | 6.2 |
| `Soundness/Normalize.lean` | redex rank/height, Lemma 12, Prop 13 | 6.3 |
| `Soundness/Normalizer.lean` | term codes, the K^sim normalizer, the clock, adequacy, `erKSimEquiv` transfer | 6.4 |
| `Soundness/Collapse.lean` | `SynCatFO`, `collapseDenotation`, `collapseFunctor`, `Faithful` | 6.5 |
| `Soundness.lean` | directory index | all |

## Execution notes

- Execute via superpowers:subagent-driven-development; fresh ledger
  section in `.superpowers/sdd/progress.md`; verify `@` is a new empty
  commit before bookmarking after each subagent (the hash-rewrite
  lesson).
- Sub-phases 6.2-6.4 do not begin until their mini-sub-plan has been
  adversarially reviewed to convergence and user-reviewed.
- Lesson (carried from Phase 5 and the binder kit): the hard proofs
  (Lemma 12, the normalizer adequacy) hit resource limits; bank each
  compiling helper lemma as its own commit, hold no more than 2-3
  lemmas' uncommitted proven work, and stop and report rather than iterate
  a whnf/normalization loop.

---

## Sub-phase 6.1 (L2): the applicative calculi and Proposition 7

Leivant III section 4.1 (p. 222), Proposition 7 (p. 222-223). The
composite of interest for soundness is `(1) => (4)`: `RMRec-omega`
(Phase 5's `RMRecCat`/`RIdent`) definability implies definability by a
term of `RλMR-omega_o`. The paper routes it as `(1) => (3)` via the
eq. (9) translation (recurrence with parameters becomes closed `R^τ`),
then `(3) => (4)` "similar to Lemma 1".

Deliverable: `rlmrSig A : BinderSig (RType)` and `rlmrOSig A :
BinderSig (RType)` (the full and destructor/case variants); their β/η,
recurrence, and flat reduction relations on `Tm`; and the translation
`RIdent A Γ τ → Tm (rlmrOSig A) (map …) …` with an interpretation-
agreement lemma (the applicative term denotes the same standard-model
function as the ramified identifier).

### Task 6.1a: the applicative signatures

**Files:** Create `GebLean/Ramified/Soundness/Applicative.lean`,
`GebLeanTests/Ramified/Soundness/Applicative.lean`; index wiring.

**Interfaces produced:**

```lean
-- constants c_i^θ : θ^{r_i} → θ ; R^τ : α_1..α_k, Ω τ → τ ; and
-- (rlmrOSig) dstr_j : o → o, case^θ : o, θ^k → θ. Application and
-- abstraction are the kit's Tm.op arguments / binder positions.
def rlmrSig (A : AlgSig) : BinderSig RType
def rlmrOSig (A : AlgSig) : BinderSig RType
```

- [ ] **Step 1: failing test.** An `example` forming a small closed
  `Tm (rlmrOSig natAlgSig) [] RType.o` (a constructor applied to
  nothing) and checking it elaborates.
- [ ] **Step 2: run — fails** (`unknown identifier 'rlmrSig'`).
- [ ] **Step 3: implement** `rlmrSig`/`rlmrOSig` as `BinderSig` records
  (`Op` = the constant inventory as an inductive; `result`/`args`
  per section 4.1's typing, with `R^τ`'s recurrence-argument binder and
  the `case`/`dstr` arities). Cite section 4.1.
- [ ] **Step 4: run — passes** (`lake test`).
- [ ] **Step 5: pre-commit; commit** (`feat(ramified): add the applicative
  calculi as binder signatures`).

### Task 6.1b: the reduction relations

**Interfaces produced:**

```lean
inductive RlmrOStep {A Γ s} : Tm (rlmrOSig A) Γ s → Tm (rlmrOSig A) Γ s → Prop
  -- β and η (via the kit's instantiate₁/sub), recurrence reduction
  -- (R^τ E_1..E_k (c_i t⃗) ⇒ E_i (R^τ E⃗ t_1)..), flat reduction
  -- (dstr_j (c_i t⃗) ⇒ t_j ; case (c_i t⃗) b⃗ ⇒ b_i).
```

- [ ] Steps: failing test (a single recurrence-reduction step on a
  concrete term reduces as expected, via the kit's `instantiate₁`);
  implement the inductive with one constructor per reduction rule (the
  substitution in β is `instantiate₁`); prove the one-step example;
  pre-commit; commit (`feat(ramified): add the applicative reduction
  relations`).

### Task 6.1c: Proposition 7 (1) to (3) — the eq. (9) translation

**Interfaces produced:**

```lean
-- eq. (9): ramified monotonic recurrence f(x⃗)(c_i(a⃗)) = g_ci(x⃗)(f(x⃗)(a⃗))
-- with each g_ci a term G_i becomes F = λx⃗. R^τ (G_1 x⃗) .. (G_k x⃗).
-- Targets the full calculus rlmrSig (item (3)).
def prop7Full {A Γ τ} (d : RIdent A Γ τ) : Tm (rlmrSig A) (mapCtx Γ) (mapTy τ)
theorem prop7Full_interp {A Γ τ} (d : RIdent A Γ τ) :
    -- the applicative term's standard denotation equals RIdent.interp d
    …
```

- [ ] Steps: failing test (`prop7Full` on `ramAdd` denotes addition,
  stated as an `example` from the interp lemmas — not `#guard`);
  implement `prop7Full` by `RIdent`'s recursor (`PolyFix.ind`), mapping
  `defn`/`mrec`/`frec` per eq. (9) (recurrence with parameters becomes a
  closed `R^τ` applied to the translated step terms); prove
  `prop7Full_interp` by induction on the identifier (bank the
  `defn`/`mrec`/`frec` cases as separate commits if large); pre-commit;
  commit(s) (`feat(ramified): transcribe Proposition 7 eq. 9`).

### Task 6.1d: Proposition 7 (3) to (4) — case/dstr from F

Leivant states `(3) => (4)` is "similar to Lemma 1"; its transcription
reconstructs that argument at the applicative level (`case`/`dstr`
expressed via the flat operator `F`, as in section 4.1 examples (1)-(2)).
The ramified-side Lemma 1 is the Phase 5 template
(`GebLean/Ramified/Definability/Flat.lean`, `higherOrderO`/`RMRecCatO`);
reuse its case-split structure.

**Interfaces produced:**

```lean
def prop7ToO {A Γ τ} (E : Tm (rlmrSig A) Γ τ) : Tm (rlmrOSig A) Γ τ
theorem prop7ToO_interp {A Γ τ} (E : Tm (rlmrSig A) Γ τ) :
    -- the o-variant term denotes the same standard function as E
    …
def prop7Translate {A Γ τ} (d : RIdent A Γ τ) : Tm (rlmrOSig A) (mapCtx Γ) (mapTy τ)
  -- := prop7ToO (prop7Full d)
```

- [ ] Steps: failing test (`prop7Translate` on `ramAdd` denotes
  addition, as an `example`); implement `prop7ToO` by the term recursor,
  replacing `F` with the `case`/`dstr` realization (and vice versa) per
  Examples (1)-(2), following the `Flat.lean` case-split template; prove
  `prop7ToO_interp` by induction; define `prop7Translate` as the
  composite; pre-commit; commit(s) (`feat(ramified): transcribe
  Proposition 7 (3) to (4)`).

---

## Sub-phase 6.2 (L3): representation in `1λ(A)` — gated

Leivant III sections 4.2-4.3 (pp. 223-226): `1λ(A)` (simply typed
lambda calculus with `dstr`/`case`), the Berarducci-Böhm representation
`a^σ`, the type map `τ ↦ τ̄` and term map `E ↦ Ē` (section 4.2), and
Lemmas 8-10 and Proposition 11 (`F̄` represents `F`).

Deliverable (interface-level; step detail via mini-sub-plan 6.2.0):

```lean
def oneLambdaSig : BinderSig SimpleTy               -- 1λ(A): STLC + dstr/case
def bbRep (a : FreeAlg A) (σ : SimpleTy) : Tm oneLambdaSig [] (abstractTy σ)  -- a^σ
def barTy (τ : RType) : SimpleTy                     -- τ̄
def barTm {Γ τ} (E : Tm (rlmrOSig A) Γ τ) : Tm oneLambdaSig (barCtx Γ) (barTy τ)  -- Ē
theorem prop11_represents {A} (F : Tm (rlmrOSig A) [] τ) :
    Represents (barTm F) F                            -- Prop 11
```

Prop 11 is an induction on the length of `F` (cases: variable, `c_i^o`,
`case`/`dstr`, `c_i^{Ωτ}` via Lemma 9, application via Lemma 8, `λ`,
and `R^τ` via Lemma 10). `Represents` is the section-4.2 logical
relation (object type: reduces to `a`/`a^{τ̄}`; arrow type: preserves
representation under application).

**Mini-sub-plan 6.2.0** (written after 6.1 lands): elaborates
`SimpleTy`, `oneLambdaSig`, the `Represents` relation, `bbRep`,
`barTy`/`barTm`, Lemmas 8-10, and the Prop 11 induction into bite-sized
tasks. It decides, as an explicit gated item, `SimpleTy`'s decision-8
realization: whether `SimpleTy` (base `o`, `arrow`) is reused as the
`{o, →}` fragment of the existing `RType` (`RType` minus `Ω`, already a
`PolyFix`; reuse rule) or realized as a fresh `PolyFix`, and records the
reason. Reason for gating the sub-phase: the exact shape of `Represents`
and the Lemma 9/10 helper lemmas depend on the concrete `rlmrOSig`/`Tm`
shapes 6.1 produces.

---

## Sub-phase 6.3 (L4): the normalization bound — gated

Leivant III section 5 (pp. 226-227): Lemma 12 (a term of height `h`,
redex rank `q` normalizes to a normal term of height `<= 2_q(h)` in time
`O((2_{q+1}(h))^2)`) and Proposition 13 (represented functions are
elementary-time computable, using Lemma 4 to reduce to target type `o`).

Deliverable (interface-level; step detail via mini-sub-plan 6.3.0):

```lean
def height {Γ s} (t : Tm oneLambdaSig Γ s) : ℕ
def redexRank {Γ s} (t : Tm oneLambdaSig Γ s) : ℕ
theorem lemma12 {Γ s} (t : Tm oneLambdaSig Γ s) :
    ∃ n : Tm oneLambdaSig Γ s, Normal n ∧ Reduces t n ∧
      height n ≤ tower (redexRank t) (height t) ∧
      normalizeSteps t ≤ … -- O((2_{q+1}(h))^2)
theorem prop13_elementary {A τ} (F : Tm (rlmrOSig A) [] (RType.omega τ ⟶ RType.o)) : …
```

Lemma 12 cites an external result [36] for the rank-stratified
β-normalization height bound `<= 2_q(h)`; Leivant supplies only the time
accounting on top (the cost model: one β-step costs proportional to the
result size; case/`dstr` reductions decrease size and create no new
β-redexes, giving the square). **Mini-sub-plan 6.3.0** decides, and
records the reason: (a) whether mathlib or a transcribable published
proof supplies the rank-stratified normalization height bound, or it is
reproved here; and (b) the exact cost model (a step-counting relation on
`Tm`) against which the `O((2_{q+1}(h))^2)` bound is stated. Reason for
gating: this is the workstream's single hardest proof; its structure
depends on the reduction relation and code representation 6.1/6.4 fix,
and the external-result decision is a research step. The height bound is
the likely resource limit — plan it for incremental commits from the
start.

---

## Sub-phase 6.4 (L5): the landing normalizer — gated

Spec s6.4; gate G3 (K^sim landing). The normalizer on `1λ(A)` term
codes runs in elementary time (Lemma 12) and computes the represented
function; realize it as a clocked `K`-morphism and transfer to ER.

Deliverable (interface-level; step detail via mini-sub-plan 6.4.0):

```lean
def codeTm {Γ s} : Tm oneLambdaSig Γ s → ℕ                  -- Gödel code of a term
def normStep : ℕ → ℕ                                        -- one reduction step on codes
def normalizer (a : ℕ) : KMor1 (a + 1)                      -- clocked K-morphism (simulate-style)
theorem normalizer_clock {…} : … ≤ tower … …                -- Lemma 12 bound, K-expressible
theorem normalizer_adequate {A τ} (F : Tm (rlmrOSig A) [] (RType.omega τ ⟶ RType.o)) (a : ℕ) :
    -- the normalizer's output equals the standard denotation of F at a
    …
def collapseER {A} (F : Tm (rlmrOSig A) …) : ERMorN … …     -- transfer across erKSimEquiv
theorem collapseER_interp … :                               -- the adequacy bridge 6.5b consumes:
    (collapseER F).interp = …                               -- = collapseDenotation of F's source morphism
```

Two substances beyond the clock (spec, master-plan boundary): the
term-code representation with a faithful `normStep` (a state-transition
step, hence K^sim per decision 2), and **semantic adequacy** —
reduction is sound for the standard model, and the normal form at type
`o` reads off as the denotation. **Mini-sub-plan 6.4.0** elaborates the
code representation, `normStep`, the `KSimURMSimulator`-style
`normalizer`, the clock (from Lemma 12, in K-expressible tower form),
the adequacy proof, and the `erKSimEquiv` transfer. Reason for gating:
the largest single deliverable of the workstream; depends on 6.2/6.3.

---

## Sub-phase 6.5 (L6): the collapse packaging

Master-plan boundary; spec s6.1. Packages 6.1-6.4 into the functor.

### Task 6.5a: `SynCatFO` and `collapseDenotation`

**Files:** Create `GebLean/Ramified/Soundness/Collapse.lean`, tests,
index wiring.

**Interfaces produced:**

```lean
def isObjCtx : ObjectProperty (RMRecCat natAlgSig)         -- object-sort contexts
abbrev SynCatFO : Type := isObjCtx.FullSubcategory
def SynCatFO.toObjCtx (Γ : SynCatFO) : Σ n, ObjCtx n       -- the ObjCtx coercion
def objLen (Γ : SynCatFO) : ℕ := Γ.toObjCtx.1
def collapseDenotation {Γ Δ : SynCatFO} (g : Γ ⟶ Δ) :
    (Fin (objLen Γ) → ℕ) → (Fin (objLen Δ) → ℕ)            -- via ramifiedDenotation
theorem collapseDenotation_comp {Γ Δ Θ : SynCatFO} (g : Γ ⟶ Δ) (h : Δ ⟶ Θ) :
    collapseDenotation (g ≫ h) = collapseDenotation h ∘ collapseDenotation g
theorem collapseDenotation_id (Γ : SynCatFO) :
    collapseDenotation (𝟙 Γ) = id
```

- [ ] **Step 1: failing test** — `collapseDenotation (𝟙 Γ) = id` as an
  `example`.
- [ ] **Step 2: run — fails.**
- [ ] **Step 3: coercion.** Implement `isObjCtx` / `SynCatFO` via
  `ObjectProperty.FullSubcategory` (precedent `LawvereNatBT0.lean`), and
  `SynCatFO.toObjCtx` / `objLen` — the explicit bridge from a
  full-subcategory object (a `Ctx RType` plus an `isObjCtx` proof) to
  the Phase 5 `ObjCtx n`, threading the object-sort proof (the argument
  bookkeeping the master plan assigned to this sub-plan). Commit.
- [ ] **Step 4: denotation.** Implement `collapseDenotation` as the
  Phase 5 `ramifiedDenotation` (`Definability/Top.lean:154`) read
  through `SynCatFO.toObjCtx` and the full-subcategory hom
  (`g : Γ ⟶ Δ ↦ Hom … Γ.toObjCtx Δ.toObjCtx`). Commit.
- [ ] **Step 5: functoriality.** Prove `collapseDenotation_id`
  (closes the failing test) and `collapseDenotation_comp` (composition
  of standard-model evaluations) — these are what `collapseFunctor`'s
  `map_id`/`map_comp` consume in 6.5b. Pre-commit; commit
  (`feat(ramified): add SynCatFO and the collapse denotation`).

### Task 6.5b: `collapseFunctor` and faithfulness

**Interfaces produced:**

```lean
def collapseFunctor : SynCatFO ⥤ LawvereERCat
instance : collapseFunctor.Faithful
```

The key adequacy lemma (from 6.4) is `collapseER_interp`: the interp of
the landed `ERMorN` equals `collapseDenotation g`. `collapseFunctor`'s
`map_id`/`map_comp` then follow from `collapseDenotation_id`/`_comp`
(6.5a) through `collapseER_interp` and `erMorNSetoid` extensionality;
`Faithful` follows because equal `ERMorN` interps force equal
`collapseDenotation`, hence equal `SynCatFO` interp-quotient morphisms.

- [ ] Steps: failing test (`collapseFunctor` on the Phase 2 doubling
  morphism yields an `ERMorN` whose interp equals doubling, as an
  `example` from the interp lemmas — not `#guard`); implement
  `collapseFunctor` — object map identity on `ℕ`-arities, morphism map
  the 6.4 `collapseER` of the morphism's applicative translation (6.1)
  represented in `1λ(A)` (6.2) and landed (6.4); prove `map_id`/`map_comp`
  from `collapseDenotation_id`/`_comp` via `collapseER_interp` and
  `erMorNSetoid` extensionality; prove `Faithful` by construction; bank
  the functor and the instance as separate commits; pre-commit;
  commit(s) (`feat(ramified): assemble collapseFunctor and prove
  faithfulness`).

---

## Self-review checklist (run before adversarial review)

- Route L boundary items map to sub-phases, none dropped or merged
  away: L1 (the applicative-calculi apparatus) = the landed binder kit
  (the substitution substrate, broken out of L1) plus Tasks 6.1a/6.1b
  (the specific calculi `rlmrSig`/`rlmrOSig` and their reductions);
  L2 (Proposition 7) = Tasks 6.1c/6.1d; L3 -> 6.2; L4 -> 6.3; L5 -> 6.4;
  the collapse packaging -> 6.5. Sub-phase 6.1 intentionally groups the
  L1 calculi with the L2 translation (a grouping for one branch, not a
  merge that drops either boundary item).
- Gated sub-phases (6.2, 6.3, 6.4) each name their mini-sub-plan and its
  gating reason (no-speculation); the two-level structure is recorded in
  standing decision 3.
- Names agree with the master plan (`SynCatFO`, `collapseDenotation`,
  `collapseFunctor`, `ramifiedDenotation`, `RMRecCat`, `natAlgSig`,
  `erKSimEquiv`) and the kit (`BinderSig`, `Tm`, `sub`, `instantiate₁`).
- Consumed-interface signatures quoted match the current pin.
- The K^sim landing reason is recorded (standing decision 2, G3 caveat).

## References

- D. Leivant, "Ramified recurrence and computational complexity III",
  APAL 96 (1999) 209-229, DOI `10.1016/S0168-0072(98)00040-2`.
- Master plan / gate record / spec: paths in the header.
- Binder-substitution research note (the L1 substrate):
  `docs/superpowers/notes/2026-07-04-binder-substitution-research.md`.
