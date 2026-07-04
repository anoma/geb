# Ramified recurrence Phase 5 (definability) sub-plan

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Global constraints](#global-constraints)
- [Standing decisions recorded by this sub-plan](#standing-decisions-recorded-by-this-sub-plan)
- [Consumed interfaces (verbatim, current pin)](#consumed-interfaces-verbatim-current-pin)
- [File structure](#file-structure)
- [Execution notes (binding on the controller and executors)](#execution-notes-binding-on-the-controller-and-executors)
- [Task 5.1: Lemma 2 — simultaneous recurrence reduces to plain](#task-51-lemma-2--simultaneous-recurrence-reduces-to-plain)
  - [Task 5.1a: evaluation helpers](#task-51a-evaluation-helpers)
  - [Task 5.1b: case, destructor, choose](#task-51b-case-destructor-choose)
  - [Task 5.1c: the simultaneous family](#task-51c-the-simultaneous-family)
- [Task 5.2: Lemma 1 — flat recurrence versus destructors and case](#task-52-lemma-1--flat-recurrence-versus-destructors-and-case)
  - [Task 5.2a: the destructor/case signature and its flat realization](#task-52a-the-destructorcase-signature-and-its-flat-realization)
  - [Task 5.2b: the O-variant presentation](#task-52b-the-o-variant-presentation)
  - [Task 5.2c: translation O-variant into the flat presentation](#task-52c-translation-o-variant-into-the-flat-presentation)
  - [Task 5.2d: translation of flat recurrence into the O-variant](#task-52d-translation-of-flat-recurrence-into-the-o-variant)
- [Task 5.3: clock-format arithmetic](#task-53-clock-format-arithmetic)
- [Task 5.4: Lemma 6 — elementary-time machines are ramified-definable](#task-54-lemma-6--elementary-time-machines-are-ramified-definable)
  - [Task 5.4a: the generalized section 2.4 ladder](#task-54a-the-generalized-section-24-ladder)
  - [Task 5.4b: the machine-state simultaneous recurrence](#task-54b-the-machine-state-simultaneous-recurrence)
  - [Task 5.4c: the eq. (8) assembly and the Lemma 6 statement](#task-54c-the-eq-8-assembly-and-the-lemma-6-statement)
- [Task 5.5: the definability family](#task-55-the-definability-family)
- [Self-review checklist (run before adversarial review)](#self-review-checklist-run-before-adversarial-review)
- [References](#references)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan task-by-task.
> Steps use checkbox (`- [ ]`) syntax for tracking. User review of
> this sub-plan precedes any execution.

**Goal:** Prove the definability direction of the ramified-recurrence
workstream — for every ER morphism, an object-sort context and a
ramified realizer with matching denotation (`erMor_ramified_definable`)
— by transcribing Leivant III Lemma 2 (simultaneous recurrence),
Lemma 1 (flat recurrence versus destructors and case), the clock
arithmetic, and Lemma 6 (elementary-time machines are
ramified-definable) against the zero-test URM step relation.

**Architecture:** This sub-plan elaborates Tasks 5.1-5.5 of the master
plan (`docs/superpowers/plans/2026-07-02-ramified-recurrence-plan.md`,
Phase 5) into stepwise detail. The task boundaries, deliverable
statements, and the Lemma 6 adaptation decision (master plan
decision 1: transcribe Lemma 6's proof shape directly against
`GebLean.URMState.step`) are preserved unchanged; this document only
adds step detail, sub-task splits, and the interface reconciliations
the Phase 2-4 review record assigned to Task 5.0. New Lean source
lives in `GebLean/Ramified/Definability/*.lean` plus targeted
modifications of `GebLean/Ramified/OmegaShift.lean`,
`GebLean/Ramified/SynCat.lean`, and `GebLean/Ramified/Algebras.lean`.

**Tech Stack:** as the master plan (Lean 4 `v4.29.0-rc6` pin, Lake,
the in-repository `PolyEndo`/`PolyFix` stack, `jj`,
`markdownlint-cli2`, `doctoc`).

**Branch:** `feat/ramified-p5-definability`, stacked on
`feat/ramified-p4-firstorder` (f2f5d9be). The branch's first commit
(056e5640) corrects `OmegaShift.lean`'s kappa-hat domain docstrings
against the source and precedes this sub-plan.

## Global constraints

The master plan's Global constraints section applies verbatim to
every task below (toolchain pin; no `noncomputable`; axiom hygiene;
`sorry` discipline; pre-commit Lean triad; markdownlint + doctoc;
`jj` only, no push without user line-by-line review; commit-message
format with the `Co-Authored-By: Claude Fable 5
<noreply@anthropic.com>` trailer; generic user references; prose
style; citation-at-point-of-use with the binding glossary
vocabulary; no Lean-native recursive inductive types — every
recursive type is a `PolyFix` of a `PolyEndo`, decision 8; known
pitfalls, including the `#guard` restrictions).

Test discipline specific to this phase (Phase 2/3 review record):
value checks over `RType`-indexed data follow the fallback ladder —
canonical constructors first, then smallest terms, then proven
`@[simp]` lemmas or `example ... := rfl`, then `decide` via the
`DecidableEq RType` / `DecidablePred RType.IsObj` instances. Heavy
composite interpretations (clocked machine composites, deep
recurrence trees) are never `#guard`-ed; state `example` proofs from
the interpretation lemmas instead.

## Standing decisions recorded by this sub-plan

1. **Provisional ratification.** The four Phase 2-3 adjudications
   (kappa-hat `IsObj` restriction; identifier constants + curried
   holes; carrier-level `ramTwoPow`; Task 3.2 honest partial) are
   treated as provisionally ratified (controller decision 2026-07-03,
   user unavailable at prompt time; reversible at user review of the
   stacked branches). Phase 5 content is nearly invariant to this:
   items 2-4 below already carry the corrections the ratifications
   presuppose.
2. **The clock is in-system.** Lemma 6's realizer (eq. (8), p. 221)
   is a morphism whose only data is its input context, so the clock
   composite `c × 2_q(sz(input))` must be built from object-language
   morphisms. Task 5.4a therefore delivers the in-system `2_m`
   family, `sz`, and the addition/multiplication copies at general
   object sorts (paper s2.4(2)-(6)), resolving the Phase 2 review's
   binding Task 5.0 note. The carrier-level `ramTwoPow` and its
   `ramTwoPow_interp` tower alignment remain the ℕ-side ingredients
   of the correctness proof (Task 5.3's stated reading), consumed
   unchanged.
3. **Full kappa-hat.** The paper's kappa-hat is total over r-types
   via the pointwise constructor lifts `c_i^τ` (s2.4(1), p. 216).
   Task 5.4a adds `kappaHatFull` at every r-type, the canonical
   functionals `C^τ`, the coercions `κ_τ` and the general `δ_θ` —
   Lemma 6's input sort `Ω(η → η)` requires `κ` at the arrow sort
   `η → η`. The committed `kappaHatIdent` instances remain the
   object-sort specializations, with an agreement lemma.
4. **sz at the general typing.** The paper's `sz` has input at
   `Ω(θ → θ)` (s2.4(6)); the committed `ramSize` (mrec at `Ω o`) is
   the `1 + X` specialization. Task 5.4a adds `szAtIdent` at the
   general typing; the clock composite consumes it. Over `1 + X` its
   count is the constructor count (input count + 1); Task 5.3's
   monotonicity lemmas absorb the offset.
5. **Simultaneous recurrence is realized function-valued.** Eq. (7)'s
   displayed reduction calls `f-hat` at instantiated selector values
   `b_j` inside its own step, which `RIdent.mrec` cannot express (a
   step sees only the parameters and the recursive results of the
   single identifier being defined, at its own parameters). The
   transcription realizes the simultaneous family by a recurrence
   whose recursive results carry the function sort `o → τ` (selector
   to value), matching Lemma 6's own description of the reduced
   `[π₁]` as "defined ... by ramified recurrence in type `o → o`"
   (p. 221). Consequence: the count argument of the derived family
   sits at `Ω(o → τ)` rather than the paper's `Ω τ` — a presentation
   adaptation of the spec s1.2 kind, recorded in the docstring, and
   absorbed by eq. (8)'s assembly (the `2_q` family exists at every
   object sort, so the clock is simply targeted at `Ω(o → τ)`). The
   same monotonic reading drops eq. (6)'s subterm arguments from the
   clause data: `RIdent.mrec`'s steps read the parameters and the
   recursive results, not the subterms, and Lemma 6's clauses do not
   use them; this omission is part of the recorded adaptation.
6. **objToNat stays in `Examples.lean`.** The conditional move
   ("beside `interp_isObj` if `Definability/*` should not import the
   ladder") does not fire: `Definability/*` imports `Examples.lean`
   regardless — for `objToNat` itself, the coercion instances
   (`ramKappa`/`ramDeltaIdent` at the tower sorts), and the
   construction patterns Task 5.4a's generalizations follow.
7. **No `DecidablePred RIdent.FirstOrder` task.** Phase 5's
   statements do not certify first-order membership; if an isolated
   certificate is needed it is written manually (`ramAdd_fo` style,
   Phase 4 record). The `DecidablePred` instance remains a deferred
   candidate.
8. **ramifiedDenotation is stated through `natFreeAlgEquiv`** (the
   master plan's Task 5.5 text), with `rfl`-simp lemmas
   (`natFreeAlgEquiv_apply`, `natFreeAlgEquiv_symm_apply`) added in
   `Algebras.lean` so proofs reduce to the committed
   `freeAlgToNat`-phrased interpretation lemmas.

## Consumed interfaces (verbatim, current pin)

ER/URM side (as fixed by the master plan's Task 5.0 block):

```lean
-- GebLean/LawvereERKSim/Compiler.lean:1590
def compileER {a : ℕ} (e : ERMor1 a) : URMProgram a

-- GebLean/LawvereERKSim/Top.lean:55 — pre-stop correctness
theorem compileER_pre_stop_correct {a : ℕ} (e : ERMor1 a)
    (v : Fin a → ℕ) : ...

-- GebLean/LawvereERKSim/Top.lean:89
theorem compileER_runFor {a : ℕ} (e : ERMor1 a) (v : Fin a → ℕ)
    (t' : ℕ) (ht' : compileER_runtime e v ≤ t') :
    (URMState.runFor (compileER e)
        (URMState.init (compileER e) v) t').regs
      (compileER e).outputReg = e.interp v

-- GebLean/LawvereERKSim/RuntimeBound.lean:225
theorem boundExprKParams_dominates {a : ℕ} (e : ERMor1 a) :
    ∀ (v : Fin a → ℕ),
      LawvereERKSim.compileER_runtime e v ≤
        tower (boundExprKParams e).1
          (Fin.maxOfNat _ v + (boundExprKParams e).2) ∧
      e.interp v ≤
        tower (boundExprKParams e).1
          (Fin.maxOfNat _ v + (boundExprKParams e).2)

-- GebLean/Utilities/Tower.lean:17,:27,:42,:51,:61,:65
def tower : ℕ → ℕ → ℕ
theorem self_le_tower (k x : ℕ) : x ≤ tower k x
theorem tower_mono_right (k : ℕ) {x y : ℕ} (h : x ≤ y) : ...
theorem tower_comp (j k x : ℕ) : ...
theorem le_two_pow_self (n : ℕ) : n ≤ 2 ^ n
theorem tower_mono_left {k₁ k₂ : ℕ} (h : k₁ ≤ k₂) (x : ℕ) : ...

-- GebLean/Utilities/ZeroTestURM.lean:89,:122,:143,:155,:179,:254
-- URMInstr (assign/inc/dec/jumpZ/stop), URMProgram (numRegs,
-- instrs, outputReg, inputRegs + injectivity/disjointness),
-- URMState (pc, regs), URMState.step, URMState.runFor,
-- URMState.init

-- GebLean/LawvereKSimInterp.lean:66 — the simultaneous-recursion
-- reference shape Task 5.1's interpretation lemma mirrors
def KMor1.simrecVec {a k : ℕ} (h : Fin (k + 1) → KMor1 a)
    (g : Fin (k + 1) → KMor1 (a + 1 + (k + 1)))
    (params : Fin a → ℕ) : ℕ → (Fin (k + 1) → ℕ)
```

Ramified side (Phases 1-4, current branch stack):

```lean
-- GebLean/Ramified/HigherOrder.lean:281,:294,:305,:394,:498
def RIdent.defn (d : DefnShape A Γ τ)
    (children : (j : Fin d.numHoles) →
      RIdent A (d.holeIdx j).1 (d.holeIdx j).2) : RIdent A Γ τ
def RIdent.mrec (params : List RType) (τ : RType)
    (steps : (i : A.B) →
      RIdent A (params ++ List.replicate (A.ar i) τ) τ) :
    RIdent A (params ++ [RType.omega τ]) τ
def RIdent.frec (params : List RType) (τ : RType)
    (clauses : (i : A.B) →
      RIdent A (params ++ List.replicate (A.ar i) RType.o) τ) :
    RIdent A (params ++ [RType.o]) τ
def RIdent.interp (f : RIdent A Γ τ) : ...
abbrev RMRecCat (A : AlgSig) :=
  SynCat (higherOrder A) (interpQuotRel (higherOrder A))
-- defnSig (:198) = ((constructorSig + appSig) + holeSig)
--   + holeConstSig — saturated and curried identifier holes;
-- identConstSig (:459) — identifier constants at curried sorts;
-- curryInterp (:158), appChain (:407),
-- RIdent.interp_eq_appChain_curryInterp (:436).

-- GebLean/Ramified/OmegaShift.lean:100,:118,:138 (lines at 056e5640)
def RType.omegaShift (t : RType) : RType
def kappaHatStep (A : AlgSig) (τ : RType) (hτ : τ.IsObj)
    (i : A.B) : RIdent A (List.replicate (A.ar i) τ) τ
def kappaHatIdent (A : AlgSig) (τ : RType) (hτ : τ.IsObj) :
    RIdent A [RType.omega τ] τ
-- kappaHatIdent_interp: denotation = identity on the carrier copy

-- GebLean/Ramified/Examples.lean:96,:116,:135,:212,:310,:410,
-- :543,:596,:611,:630,:641
def objToNat {s : RType} (hs : s.IsObj)
    (x : RType.interp (FreeAlg natAlgSig) s) : Nat
def ramKappa (m : Nat) :
    RIdent natAlgSig [RType.tower (m + 1)] (RType.tower m)
def ramDeltaIdent : (m : Nat) →
    RIdent natAlgSig [RType.tower m] RType.o
def ramAdd : RIdent natAlgSig [RType.o, RType.omega RType.o] RType.o
def ramMul :
    RIdent natAlgSig [RType.omega RType.o, RType.omega RType.o]
      RType.o
def ramSize : RIdent natAlgSig [RType.omega RType.o] RType.o
def ramExp : RIdent natAlgSig [RType.omega ramFun] ramFun
theorem ramExp_interp ... :
    freeAlgToNat ((ramExp.interp ρ) x)
      = freeAlgToNat x + 2 ^ freeAlgToNat (ρ 0)
def ramTwoPowStep (x : FreeAlg natAlgSig) : FreeAlg natAlgSig
def ramTwoPow : Nat → FreeAlg natAlgSig → FreeAlg natAlgSig
theorem ramTwoPow_interp (m : Nat) (x : FreeAlg natAlgSig) :
    freeAlgToNat (ramTwoPow m x) = GebLean.tower m (freeAlgToNat x)

-- GebLean/Ramified/Algebras.lean:300
def natFreeAlgEquiv : FreeAlg natAlgSig ≃ ℕ
-- toFun = freeAlgToNat, invFun = natToFreeAlg
--   (GebLean/Ramified/AlgSig.lean:118,:126)

-- GebLean/Ramified/SynCat.lean:104,:128,:176,:236
def HomTuple (P : Presentation) (Γ Δ : Ctx P.S) : Type
def Hom (P : Presentation) (r : QuotRel P.sig) (Γ Δ : Ctx P.S) :
    Type
def SynCat (P : Presentation) (_r : QuotRel P.sig) : Type
def joinTuple ... -- product pairing of hom-tuples

-- GebLean/Ramified/FirstOrder.lean:218,:236,:262,:296 — the op
-- case-split and term-translation templates for Task 5.2's
-- translations (Phase 4 review record)
def foOp ... ; def foTm ... ; theorem foTm_eval ...
def foInclusion (A : AlgSig) : ...
```

## File structure

| File | Contents | Task |
| --- | --- | --- |
| `GebLean/Ramified/SynCat.lean` (modify) | `HomTuple.eval`, `Hom.eval`, singleton-context helpers | 5.1a |
| `GebLean/Ramified/Definability/Simultaneous.lean` | `ramCase`, `ramDstr`, `chooseIdent`, the simultaneous family, interpretation lemmas | 5.1b-c |
| `GebLean/Ramified/Definability/Flat.lean` | `dstrCaseSig`, O-variant presentation, two-way translations | 5.2 |
| `GebLean/Ramified/Definability/Bounds.lean` | clock-format ℕ arithmetic | 5.3 |
| `GebLean/Ramified/OmegaShift.lean` (modify) | `cLift`, `kappaHatFull`, `canonIdent`, `kappaIdent`, `deltaIdent` | 5.4a |
| `GebLean/Ramified/Definability/Ladder.lean` | `expAtIdent`, `clockSort`, `twoPowIdent`, `szAtIdent`, `addAtIdent`, `mulAtIdent`, numerals at object sorts | 5.4a |
| `GebLean/Ramified/Definability/Machine.lean` | URM step clauses, `stt`/`[φ]` family, eq. (8) assembly, Lemma 6 | 5.4b-c |
| `GebLean/Ramified/Algebras.lean` (modify) | `natFreeAlgEquiv` `rfl`-simp lemmas | 5.5 |
| `GebLean/Ramified/Definability/Top.lean` | `ObjCtx`, `oCtx`, `ramifiedDenotation`, `erMor_ramified_definable` | 5.5 |
| `GebLean/Ramified/Definability.lean` | directory index | 5.1, extended per task |
| `GebLeanTests/Ramified/Definability/*.lean` | per-task test modules (+ index, `GebLeanTests/Ramified.lean` import) | each |

Interface blocks below are binding for names, arities, and semantic
content; implicit-argument placement, universe annotations, and
transport (`cast`) bookkeeping may be adjusted at elaboration time.
All Phase 5 content is over `natAlgSig` unless a declaration is
naturally `A`-generic at no extra cost (the master plan's decision 3
hosts the proof over `1 + X`).

## Execution notes (binding on the controller and executors)

- Execute via superpowers:subagent-driven-development, fresh ledger
  section "Phase 5" in the parent repo's `.superpowers/sdd/progress.md`
  (already opened by Task 5.0); one implementer subagent per sub-task,
  reviewer between sub-tasks.
- After each implementer returns, verify the working copy `@` is a
  new empty commit before moving any bookmark (Phase 2 hash-rewrite
  lesson).
- Pre-commit triad (`bash scripts/pre-commit.sh`) before every commit
  touching `.lean`; `doctoc` + `markdownlint-cli2` for every `.md`.
- Each sub-task ends with a commit; the branch is always at a
  compiling, test-passing state.
- Citation discipline: every transcribed declaration names the
  paper's section/lemma/equation and carries DOI
  `10.1016/S0168-0072(98)00040-2`; novel packaging is marked as such.
  The Otto precedent paragraph (gate G4 wording) goes in the module
  docstring of `Definability/Top.lean` (the Phase 2 definability
  module named by the G4 record).

---

## Task 5.1: Lemma 2 — simultaneous recurrence reduces to plain

Master-plan deliverable (unchanged): the ramified
simultaneous-recurrence schema (paper section 2.6, eqs. (6)-(7)) as a
derived construction over `higherOrder natAlgSig` — a family of
identifiers with the simultaneous defining equations — with an
interpretation lemma matching the classical simultaneous system (the
shape of `KMor1.simrecVec`, restated over the ramified sorts).
Docstrings cite Leivant III Lemma 2 (section 2.6, eqs. (6)-(7),
p. 217-218 incl. footnote 6).

### Task 5.1a: evaluation helpers

**Files:**

- Modify: `GebLean/Ramified/SynCat.lean`
- Test: `GebLeanTests/Ramified/SynCat.lean` (extend)

**Interfaces (produces):**

```lean
/-- Evaluate a hom-tuple at an environment of the model `M`:
componentwise `Tm.eval`. -/
def HomTuple.eval {P : Presentation} {Γ Δ : Ctx P.S}
    (f : HomTuple P Γ Δ) (M : SortedModel P.sig) (ρ : M.Env Γ) :
    M.Env Δ

/-- Evaluate a hom (a quotient class) at the standard model:
well-defined because `interpQuotRel` is extensional equality of
`eval` at that model (`Quotient.lift`). -/
def Hom.eval {P : Presentation} {Γ Δ : Ctx P.S}
    (f : Hom P (interpQuotRel P) Γ Δ)
    (ρ : (standardModel P).Env Γ) : (standardModel P).Env Δ

@[simp] theorem Hom.eval_mk ... -- eval ∘ Quotient.mk = tuple eval
theorem Hom.eval_comp ...       -- eval respects ≫

/-- The morphism `[σ₁, ..., σₖ] ⟶ [τ]` applying an identifier to the
context's variables (the `kappaHatTuple` pattern, hoisted). -/
def identHom {A : AlgSig} {Γ : List RType} {τ : RType}
    (f : RIdent A Γ τ) :
    Hom (higherOrder A) (interpQuotRel (higherOrder A)) Γ [τ]
theorem identHom_eval ...       -- eval reads off RIdent.interp
```

- [ ] **Step 1: failing tests.** In the existing SynCat test module:
  `Hom.eval` of the identity hom on a one-sort context is the
  identity (`example ... := rfl` on a small environment); the
  `identHom` value check (`identHom ramAdd` at the environment
  `(2, 3)` reads `5` through `freeAlgToNat`, an `example` from
  `ramAdd_interp_env`) is placed in Task 5.1b's new test module
  unconditionally, keeping this task's tests free of an
  Examples-import decision. `lake test`, confirm failure.
- [ ] **Step 2: implement** (`Quotient.lift` with the setoid law as
  the well-definedness proof; `identHom` generalizes
  `kappaHatTuple`'s `Fin.cons (Tm.op ... Tm.var) finZeroElim`
  pattern). Novel packaging; no paper citation.
- [ ] **Step 3: verify, pre-commit triad, commit** (message
  `feat(ramified): add hom evaluation and identifier-morphism helpers`).

### Task 5.1b: case, destructor, choose

**Files:**

- Create: `GebLean/Ramified/Definability/Simultaneous.lean`,
  `GebLean/Ramified/Definability.lean`
- Create: `GebLeanTests/Ramified/Definability/Simultaneous.lean`
  (+ index files, `GebLeanTests/Ramified.lean` import)
- Modify: `GebLean/Ramified.lean` (import the new index)

**Interfaces (produces):**

```lean
/-- case^τ : o, τ^k → τ (paper section 2.5 and eq. (2)): the flat
recurrence whose clause at constructor `c_i` returns the i-th
parameter. Result sort τ arbitrary (`RIdent.frec` permits it), so
the eq. (2) explicit-definition lift is not needed as a separate
construction; its statement is recorded in the docstring. -/
def ramCase (τ : RType) :
    RIdent natAlgSig
      ([τ, τ] ++ [RType.o]) τ
-- context: one parameter per constructor of natAlgSig (order
-- false, true), recurrence argument at o last

/-- dstr : o → o over 1 + X (paper sections 2.5, 4.1): predecessor;
dstr(0) = 0 (the j > r_i clause returns the argument), dstr(succ a)
= a. Flat recurrence reading the subterm. -/
def ramDstr : RIdent natAlgSig [RType.o] RType.o

/-- choose over m + 1 entries : o, τ^(m+1) → τ (Lemma 2's selector,
p. 218): choose(z, y₀ ... y_m) = y_j if z is the numeral j; every
selector value ≥ m falls through to the last entry y_m
(chooseIdent_interp_ge; the machine simulation's implicit-halt arm
relies on the fall-through). Indexed at m + 1 so the family is
total. Built by induction on m from `ramCase` and `ramDstr`
compositions, per the proof of Lemma 2. -/
def chooseIdent (m : Nat) (τ : RType) :
    RIdent natAlgSig (RType.o :: List.replicate (m + 1) τ) τ

theorem ramCase_interp ...   -- clause selection on carrier values
theorem ramDstr_interp ...   -- pred on counts
theorem chooseIdent_interp (m : Nat) (τ : RType) ... :
    -- on selector numeral j ≤ m, denotation = the entry y_j
theorem chooseIdent_interp_ge (m : Nat) (τ : RType) ... :
    -- on selector numeral j ≥ m, denotation = the last entry y_m
```

- [ ] **Step 1: failing tests.** `#guard`-ladder checks at `τ = o`:
  `ramCase` selects by constructor on `0` and `succ 0`;
  `ramDstr` at `0, 1, 3` gives `0, 0, 2`; `chooseIdent 3 o` (four
  entries) at selectors `0, 2, 3` returns the matching entry, and
  the fall-through cases return the last entry: `chooseIdent 2 o`
  at selector `5` and `chooseIdent 3 o` at selector `7` (small
  numerals;
  read through `freeAlgToNat`).
- [ ] **Step 2: implement.** `chooseIdent` recursion: base
  `chooseIdent 0` returns its sole entry (an explicit definition),
  and `chooseIdent (m + 1)` at entries `y₀ ... y_{m+1}` is
  `case^τ(y₀, chooseIdent m (dstr z) (y₁ ...), z)` — argument order
  per the committed `frec` convention (recurrence argument last);
  the composite is an explicit definition (`RIdent.defn`) whose
  holes reference `ramCase τ`, `ramDstr`, and `chooseIdent m τ`.
  The fall-through for selectors beyond the entry count is a
  consequence of the recursion (selectors larger than the entry
  count reach the base, which returns its sole entry — the last);
  prove `chooseIdent_interp_ge` alongside `chooseIdent_interp`.
  Citations: Lemma 2 proof, section 2.6; case/dstr, section 2.5.
- [ ] **Step 3: verify, pre-commit triad, commit** (message
  `feat(ramified): add case, destructor, and selector identifiers`).

### Task 5.1c: the simultaneous family

**Files:**

- Modify: `GebLean/Ramified/Definability/Simultaneous.lean` (+ test)

**Interfaces (produces):**

```lean
/-- Clause data for an m-fold ramified simultaneous (monotonic)
recurrence at result sort τ with parameters `params` (paper
section 2.6, eq. (6), monotonic reading): for each component j and
constructor i, a step identifier seeing the parameters and the m
recursive results of all components at each subterm, presented at
the function sort `o → τ` (selector-indexed; standing decision 5).
-/
def SimulSteps (m : Nat) (params : List RType) (τ : RType) : Type :=
  (j : Fin m) → (i : Bool) →
    RIdent natAlgSig
      (params ++ List.replicate (natAlgSig.ar i)
        (RType.arrow RType.o τ) ++ [RType.o]) τ
-- the trailing o is the selector position of the function-valued
-- carrier; the step reads recursive results as o → τ values and
-- extracts components by applying them to selector numerals

/-- The single function-valued recurrence realizing the family:
recurrence in type `o → τ` (recursive results carry `o → τ`), count
argument at `Ω(o → τ)`. Its step at constructor i builds, as the
value at selector u, `choose(u, step₁ᵢ ..., step_mᵢ)` — the Lemma 2
reduction (eq. (7)) with the parameter-instantiated recursive calls
replaced by selector application (standing decision 5). -/
def simulIdent {m : Nat} (hm : 0 < m) (params : List RType)
    (τ : RType) (steps : SimulSteps m params τ) :
    RIdent natAlgSig
      (params ++ [RType.omega (RType.arrow RType.o τ)])
      (RType.arrow RType.o τ)

/-- The j-th component: apply the function-valued recurrence to the
selector numeral j (explicit definition; f_j = f-hat(b_j)). -/
def simulProj {m : Nat} (hm : 0 < m) (params : List RType)
    (τ : RType) (steps : SimulSteps m params τ) (j : Fin m) :
    RIdent natAlgSig
      (params ++ [RType.omega (RType.arrow RType.o τ)]) τ

/-- The carrier-level reference solution, mirroring
`KMor1.simrecVec` over the ramified sorts: componentwise value
after n steps, by recursion on n. Novel packaging. -/
def simulSol {m : Nat} (params : List RType) (τ : RType)
    (steps : SimulSteps m params τ)
    (pe : ∀ i : Fin params.length,
      RType.interp (FreeAlg natAlgSig) (params.get i)) :
    Nat → Fin m → RType.interp (FreeAlg natAlgSig) τ

/-- The interpretation lemma: the projected components satisfy the
simultaneous defining equations — `simulProj j` at count numeral n
denotes `simulSol ... n j`. -/
theorem simulProj_interp ...
```

- [ ] **Step 1: failing tests.** A two-component family at `τ = o`
  — the alternating pair `f₁(n+1) = f₂(n)`,
  `f₂(n+1) = succ (f₁(n))`, base `(0, 0)`; `#guard` its components
  at counts `0, 1, 2, 3` through `freeAlgToNat` against the closed
  forms.
- [ ] **Step 2: implement.** The `mrec` step at constructor `true`
  is an explicit definition whose body is the curried-hole
  combinator form (the `ramExpStep` pattern, Examples.lean:516) of
  an auxiliary identifier with the selector appended to the context;
  that auxiliary's body is `chooseIdent (m - 1) τ` — well-formed
  under `hm : 0 < m`, carrying exactly the family's `m` entries
  `y₀ ... y_{m-1}`; the projections use selector numerals `j < m`,
  so the fall-through is unreachable from `simulProj` — applied to
  the selector
  variable and, for each j, the j-th step identifier applied to the
  parameters and the recursive-result variables (as `o → τ` values).
  Docstring: transcription of Lemma 2 with the standing-decision-5
  adaptation displayed (`f-hat` in type `o → τ`; count at
  `Ω(o → τ)`; the paper's eq. (7) and footnote 6 quoted with the
  glossary vocabulary).
- [ ] **Step 3: verify, pre-commit triad, commit** (message
  `feat(ramified): transcribe Lemma 2 simultaneous recurrence`).

---

## Task 5.2: Lemma 1 — flat recurrence versus destructors and case

Master-plan deliverable (unchanged): `dstrCaseSig` as a `SortedSig`
summand (spec s4.2 sketch), forming the destructor/case presentation
variant; and the two-way definability reduction of paper section 2.5,
Lemma 1, as interpretation-preserving translations between the two
variants. This is the `RMRec-omega_o` to `RMRec-omega` leg the
definability chain ends with (spec s6.2 step 3); in this sub-plan the
chain consumes direction (a) (the derived-identifier realization of
the `dstrCaseSig` operations), which lets Task 5.4's construction
land directly in `RMRecCat natAlgSig` as the master plan's Task 5.4
statement requires.

### Task 5.2a: the destructor/case signature and its flat realization

**Files:**

- Create: `GebLean/Ramified/Definability/Flat.lean` (+ test module,
  index imports)

**Interfaces (produces):**

```lean
/-- The destructor/case operations (paper section 2.5): destructors
dstr_j : o → o (j up to the largest arity) and, at each object sort
θ, a case operation case^θ : o, θ^k → θ (k the number of
constructors). Spec s4.2's sketch signature. -/
def dstrCaseSig (A : AlgSig) (IsObj : RType → Prop) :
    SortedSig RType

/-- Standard semantics: dstr_j reads the j-th subterm (the argument
itself when j exceeds the arity, paper section 4.1's reduction
rules); case^θ selects the branch of the main constructor. -/
def dstrCaseModel (op : (dstrCaseSig natAlgSig RType.IsObj).Op)
    (args : ∀ i, RType.interp (FreeAlg natAlgSig)
      (((dstrCaseSig natAlgSig RType.IsObj).arity op).get i)) :
    RType.interp (FreeAlg natAlgSig)
      ((dstrCaseSig natAlgSig RType.IsObj).result op)

/-- Direction (a) of Lemma 1 (the containment RRec_o ⊆ RRec): each
dstrCaseSig operation realized as a derived identifier by flat
recurrence in `higherOrder natAlgSig` — `ramDstr` and `ramCase` of
Task 5.1b — with interpretation agreement. -/
def dstrCaseToFlat (op : (dstrCaseSig natAlgSig RType.IsObj).Op) :
    RIdent natAlgSig
      ((dstrCaseSig natAlgSig RType.IsObj).arity op)
      ((dstrCaseSig natAlgSig RType.IsObj).result op)
theorem dstrCaseToFlat_interp ...
```

- [ ] **Step 1: failing tests.** `#guard` the `dstrCaseModel`
  semantics on small values (dstr on `0, 3`; case at `o` on both
  constructors), and agreement of `dstrCaseToFlat` with
  `dstrCaseModel` on the same values.
- [ ] **Step 2: implement** (over `natAlgSig` the destructor family
  is `ramDstr` alone — arities are ≤ 1; `case^θ` for object `θ`
  instantiates `ramCase θ`; the general-`A` signature shape is kept,
  the realization is `natAlgSig`-scoped). Citations: Lemma 1's
  trivial direction, section 2.5.
- [ ] **Step 3: verify, pre-commit triad, commit** (message
  `feat(ramified): add destructor-case signature and flat realization`).

### Task 5.2b: the O-variant presentation

**Files:**

- Modify: `GebLean/Ramified/Definability/Flat.lean` (+ test)

**Interfaces (produces):**

```lean
-- Mirrors of HigherOrder.lean's identifier layer with flat
-- recurrence removed and dstrCaseSig added to the term signature
-- (paper section 2.5: "flat recurrence is replaced by the
-- destructor functions ... and case functions"):
def defnSigO (A : AlgSig) (n : Nat)
    (holeIdx : Fin n → List RType × RType) : SortedSig RType
--   = defnSig's summands with dstrCaseSig added
structure DefnShapeO (A : AlgSig) (Γ : List RType) (τ : RType)
def IdentShapeO ... : Type   -- DefnShapeO ⊕ MrecShape (no frec)
def identEndoO (A : AlgSig) : PolyEndo (List RType × RType)
def RIdentO (A : AlgSig) (Γ : List RType) (τ : RType) : Type
def RIdentO.interp ...
def higherOrderO (A : AlgSig) : Presentation
abbrev RMRecCatO (A : AlgSig) :=
  SynCat (higherOrderO A) (interpQuotRel (higherOrderO A))
```

- [ ] **Step 1: failing tests.** Build the doubling identifier in
  the O-variant (mrec over dstr/case-free steps) and a case-split
  through the primitive `case` operation; `#guard` small values.
- [ ] **Step 2: implement**, mirroring `HigherOrder.lean`'s
  construction (shapes/dirs/`identTarget`/`PolyFix`); the mirror is
  deliberate — parameterizing `HigherOrder.lean` over an extra
  operations summand would rewrite committed Phase 2-4 modules
  pending user review, and the mirror is confined to one module.
  Record this choice in the implementation notes. Citation:
  section 2.5's definition of `RMRec_o^omega`.
- [ ] **Step 3: verify, pre-commit triad, commit** (message
  `feat(ramified): add the destructor-case presentation variant`).

### Task 5.2c: translation O-variant into the flat presentation

**Files:**

- Modify: `GebLean/Ramified/Definability/Flat.lean` (+ test)

**Interfaces (produces):**

```lean
/-- Lemma 1, direction (a) at the system level: translate O-variant
identifiers, terms, and hom-tuples into `higherOrder natAlgSig`,
realizing dstr/case occurrences by `dstrCaseToFlat`. Follows the
foOp/foTm case-split template (FirstOrder.lean:218,:236). -/
def ocIdent {Γ τ} : RIdentO natAlgSig Γ τ → RIdent natAlgSig Γ τ
def ocTm {Γ : Ctx RType} {s : RType} :
    Tm (higherOrderO natAlgSig).sig Γ s →
    Tm (higherOrder natAlgSig).sig Γ s
def ocHomMap (Γ Δ : Ctx RType) :
    HomTuple (higherOrderO natAlgSig) Γ Δ →
    HomTuple (higherOrder natAlgSig) Γ Δ
theorem ocIdent_interp ...   -- interpretation preserved
theorem ocTm_eval ...
def ocInclusion : RMRecCatO natAlgSig ⥤ RMRecCat natAlgSig
-- functor laws through Quotient.sound, the foInclusion template
```

- [ ] **Step 1: failing tests.** Translate the Task 5.2b doubling
  and case-split; `#guard` denotation agreement at small values.
- [ ] **Step 2: implement** (structural recursion on `RIdentO` via
  `PolyFix.ind`; term translation op-by-op with the dstr/case ops
  routed through `dstrCaseToFlat`).
- [ ] **Step 3: verify, pre-commit triad, commit** (message
  `feat(ramified): translate the destructor-case variant into flat`).

### Task 5.2d: translation of flat recurrence into the O-variant

**Files:**

- Modify: `GebLean/Ramified/Definability/Flat.lean` (+ test)

**Interfaces (produces):**

```lean
/-- Lemma 1, converse direction (section 2.5's proof): each flat
recurrence f(x-vec)(a) with clauses g_ci becomes the explicit
definition case(γ_c1, ..., γ_ck, a) with
γ_ci = g_ci(x-vec)(dstr_1(a), ..., dstr_ri(a)); by induction on the
identifier the g_ci are already translated. -/
def flatToOc {Γ τ} : RIdent natAlgSig Γ τ → RIdentO natAlgSig Γ τ
theorem flatToOc_interp ...
```

- [ ] **Step 1: failing tests.** Translate `ramDstr` (itself a flat
  recurrence) and the Phase 2 predecessor case split; `#guard`
  denotation agreement.
- [ ] **Step 2: implement**; the docstring displays Lemma 1's proof
  equation with the glossary vocabulary and cites section 2.5.
- [ ] **Step 3: verify, pre-commit triad, commit** (message
  `feat(ramified): translate flat recurrence into destructors and case`).

---

## Task 5.3: clock-format arithmetic

Master-plan deliverable, as amended by standing decision 2: the
bound conversion of spec s6.2 step 2's clock — from
`tower μ (Fin.maxOfNat _ v + offset)`
(`boundExprKParams_dominates`) to Leivant's `c * 2_q (sz input)`
format — "pure ℕ inequalities relating `tower` to the `2_m` ladder
(via `ramTwoPow_interp` from Phase 2) and `sz`, monotonicity, and
the componentwise max-over-inputs handling the arity remark needs"
(master plan Task 5.3). Amendment: the object-language link to the
`2_m` ladder is carried by `twoPowIdent_interp` (Task 5.4a, standing
decision 2); `ramTwoPow_interp` remains the ℕ-side tower alignment
this task's lemmas compose with. `Tower.lean` already carries
`tower_comp`, `tower_mono_right`, `tower_mono_left`,
`self_le_tower`, and `le_two_pow_self`; this task adds only what is
missing.

**Files:**

- Create: `GebLean/Ramified/Definability/Bounds.lean` (+ test,
  index imports)

**Interfaces (produces):**

```lean
/-- x + k ≤ tower k x: k applications of succ_le (n + 1 ≤ 2^n). -/
theorem add_le_tower (k x : ℕ) : x + k ≤ tower k x

/-- The additive offset absorbed into the height:
tower μ (x + k) ≤ tower (μ + k) x, via add_le_tower,
tower_mono_right, and tower_comp. -/
theorem tower_add_le_tower (μ k x : ℕ) :
    tower μ (x + k) ≤ tower (μ + k) x

/-- The clock format: for every μ, offset there are c and q with
tower μ (x + offset) ≤ c * tower q x for all x — Leivant's
c · 2_q shape (Lemma 6 hypothesis format), with c = 1 and
q = μ + offset. Stated with explicit c to keep Lemma 6's statement
at the paper's generality. -/
theorem tower_clock_format (μ k : ℕ) :
    ∃ c q, ∀ x, tower μ (x + k) ≤ c * tower q x

/-- max over inputs versus the staggered in-system size sum:
Fin.maxOfNat n v ≤ (∑ i, (v i + 1)), and monotone transport into
tower/clock composites (the arity remark, spec s6.2). -/
theorem maxOfNat_le_sum_succ ...
theorem clock_mono ...   -- c * tower q monotone in the argument
```

- [ ] **Step 1: failing tests.** `#guard` numeric instances
  (`tower_add_le_tower` at `μ = 1, k = 2, x = 1` via `decide` on the
  inequality; `add_le_tower` at small values); `example` instances
  of the ∃-form.
- [ ] **Step 2: implement** (induction on `k` for `add_le_tower`;
  the rest composes existing Tower.lean lemmas). No new mathematics
  (spec s6.2); docstrings cite the conversion role and Lemma 6's
  clock shape, section 3.2.
- [ ] **Step 3: verify, pre-commit triad, commit** (message
  `feat(ramified): add clock-format tower arithmetic`).

---

## Task 5.4: Lemma 6 — elementary-time machines are ramified-definable

Master-plan deliverable (unchanged): the Lemma 6 transcription (paper
section 3.2) against the zero-test URM step relation (plan
decision 1): machine state tracked by functions `stt` and `[φ]`
defined by ramified simultaneous recurrence (Task 5.1) over
`URMState.step`, clocked by the ramified `2_q` composed with `sz`
(Task 5.3, Phase 2 ladder); the realizer takes its input at the
object sort `Ω(η → η)` per eq. (8) (p. 221). The n-input, m-output
case is assembled componentwise with the clock bound taken over all
inputs (spec s6.2 arity remark). Docstrings record the s1.2
embedding argument as fidelity justification for the URM adaptation.

Deliverable location note: `URMProgram` is single-output, so this
task's statement (`urm_ramified_definable`) is unary-output; the
m-output componentwise assembly of the deliverable sentence is
realized at Task 5.5 (`erMorN_ramified_definable`), under the master
plan's Task 5.5 delegation of "the exact multi-output form (m
outputs componentwise)" to this sub-plan.

Sort bookkeeping fixed by this sub-plan (standing decisions 2-5):
the count sort of the simultaneous family is `ω := Ω(o → o)`
(τ = o); the clock composite is targeted at `ω`; `2_q` is taken at
`θ := Ω ω` so the constant multiple lands at `ω` through the
multiplication copy `(Ω ω)² → ω`; the per-input size computations
are staggered across `Ω`-shifted sorts so the addition copies
`θ', Ω θ' → θ'` chain (worked scheme in Task 5.4c). The paper's
"Let θ = Ωo" display carries surface sort slips (its `×: θ² → o`
does not land at the count sort); the executor reconciles against
the source and records the reconciliation in the docstring as a
presentation adaptation (spec s1.2).

### Task 5.4a: the generalized section 2.4 ladder

**Files:**

- Modify: `GebLean/Ramified/OmegaShift.lean` (coercions)
- Create: `GebLean/Ramified/Definability/Ladder.lean` (numeric
  family; + tests, index imports)

**Interfaces (produces):**

```lean
-- OmegaShift.lean additions (all A-generic where free):

/-- The pointwise constructor lift c_i^τ (paper s2.4(1), p. 216):
for τ = σ-vec → θ, c_i^τ(u₁ ... u_r)(x-vec) =
c_i^θ(u₁(x-vec) ... u_r(x-vec)), an explicit definition (curried
holes + app chains). At an object τ this is the constructor
operation itself (the committed kappaHatStep). -/
def cLift (A : AlgSig) (τ : RType) (i : A.B) :
    RIdent A (List.replicate (A.ar i) τ) τ

/-- kappa-hat at every r-type (paper s2.4(1)): the ramified
monotonic recurrence with steps cLift. Agrees with kappaHatIdent at
object sorts (kappaHatFull_eq_kappaHatIdent). -/
def kappaHatFull (A : AlgSig) (τ : RType) :
    RIdent A [RType.omega τ] τ
theorem kappaHatFull_eq_kappaHatIdent ...
--   extensional agreement at IsObj sorts
theorem kappaHatFull_interp ...  -- the recurrence semantics

/-- The canonical functional C^τ = λ x-vec. α^θ (paper s2.4 intro,
p. 215), given a 0-ary constructor (carried as data per the AlgSig
convention). -/
def canonIdent (A : AlgSig) (b₀ : A.B) (h₀ : A.ar b₀ = 0)
    (τ : RType) : RIdent A [] τ

/-- The final object sort of an r-type: θ for τ = σ-vec → θ
(paper p. 213: "every r-type τ is of the form σ-vec → θ"). By
PolyFix.ind on the type structure (o and Ω-types are their own
target; an arrow's target is its codomain's). -/
def RType.objTarget : RType → RType
theorem RType.objTarget_isObj (τ : RType) : τ.objTarget.IsObj

/-- κ_τ : Ω τ → θ (paper s2.4(1)): kappaHatFull applied to the
canonical functionals; extensionally the identity. -/
def kappaIdent (A : AlgSig) (b₀ : A.B) (h₀ : A.ar b₀ = 0)
    (τ : RType) : RIdent A [RType.omega τ] τ.objTarget

/-- δ_θ : θ → o for every object sort θ (paper s2.4(1)): composing
κ downward, by structural recursion on the r-type. Extensionally
the identity (deltaIdent_interp); generalizes the tower-sort
ramDeltaIdent. -/
def deltaIdent (A : AlgSig) (b₀ : A.B) (h₀ : A.ar b₀ = 0)
    (θ : RType) (hθ : θ.IsObj) : RIdent A [θ] RType.o
theorem deltaIdent_interp ...   -- objToNat-identity

-- Ladder.lean (natAlgSig):

/-- Numerals at any object sort (constructor operations exist at
every IsObj sort). -/
def numeralTm {Γ : Ctx RType} (s : RType) (hs : s.IsObj) (n : Nat) :
    Tm (higherOrder natAlgSig).sig Γ s

/-- The exp copy at object sort θ: e^θ : Ω(θ → θ) → (θ → θ), the
ramExp construction with o replaced by θ — the implied
generalization of the displayed e : Ω(o → o) → (o → o) (paper
s2.4(3)); the s2.4(3) "more generally" clause asserts the resulting
exp copy of type Ω(θ → θ) → θ, delivered here as the value of e^θ
at the 0 numeral (the twoPowIdent step). -/
def expAtIdent (θ : RType) (hθ : θ.IsObj) :
    RIdent natAlgSig [RType.omega (RType.arrow θ θ)]
      (RType.arrow θ θ)
theorem expAtIdent_interp ...   -- counts: x + 2^n, as ramExp_interp

/-- The input-sort chain of the in-system 2_m family (paper
s2.4(4)): clockSort 0 θ = θ; clockSort (m+1) θ =
Ω(clockSort m θ → clockSort m θ). Each is an object sort. -/
def clockSort : Nat → RType → RType
theorem clockSort_isObj ...

/-- The in-system 2_m family (paper s2.4(4)): 2_m : clockSort m θ →
θ, by induction on m — 2_0 the identity, 2_{m+1} = 2_m ∘ (value of
e^{clockSort m θ} at the 0 numeral input); counts align with
GebLean.tower (twoPowIdent_interp), the object-language counterpart
of the carrier-level ramTwoPow/ramTwoPow_interp pair. -/
def twoPowIdent (m : Nat) (θ : RType) (hθ : θ.IsObj) :
    RIdent natAlgSig [clockSort m θ] θ
theorem twoPowIdent_interp ...  -- objToNat = tower m ∘ objToNat

/-- sz at the general typing (paper s2.4(6)): addsz : Ω(θ → θ) →
(θ → θ) by ramified recurrence (g_j composition steps), sz(a) =
addsz(a)(α). Over 1 + X the count is the constructor count:
objToNat (sz a) = objToNat a + 1 (szAtIdent_interp; the committed
ramSize is the o-sorted mrec specialization with count identity).
-/
def szAtIdent (θ : RType) (hθ : θ.IsObj) :
    RIdent natAlgSig [RType.omega (RType.arrow θ θ)] θ
theorem szAtIdent_interp ...

/-- Addition and multiplication copies at object sort θ (paper
s2.4(2) "more generally"): + : θ, Ω θ → θ and x : (Ω θ)² → θ. -/
def addAtIdent (θ : RType) (hθ : θ.IsObj) :
    RIdent natAlgSig [θ, RType.omega θ] θ
def mulAtIdent (θ : RType) (hθ : θ.IsObj) :
    RIdent natAlgSig [RType.omega θ, RType.omega θ] θ
theorem addAtIdent_interp ... ; theorem mulAtIdent_interp ...
```

- [ ] **Step 1: failing tests.** Coercions: `kappaHatFull` at `o`
  agrees with `kappaHatIdent` on `0, 3`; at the arrow sort `o → o`
  its denotation on the numeral `2` is the 2-fold `cLift` composite
  (an `example` from `kappaHatFull_interp`); `deltaIdent` at
  `Ω(o → o)` reads the identity on `0, 3`. Ladder: `expAtIdent` at
  `θ = Ω o` on small values; `twoPowIdent 2` reads `tower 2` at
  `1`; `szAtIdent` reads count + 1 at `0, 3`; `addAtIdent`/
  `mulAtIdent` at `Ω o` on `2 + 3`, `2 * 3`. All through
  `objToNat`/`freeAlgToNat`, `#guard` ladder discipline.
- [ ] **Step 2: implement the coercions** (`cLift` via the
  curried-hole machinery — the `ramExpStep` pattern; `kappaHatFull`
  as `RIdent.mrec [] τ (cLift ...)`; `deltaIdent` by `PolyFix.ind`
  on the object sort's structure). Pre-commit triad; commit
  (message `feat(ramified): add full kappa-hat and general coercions`).
- [ ] **Step 3: implement the numeric family** (θ-generalizations
  of the committed `ramExp`/`ramAdd`/`ramMul`/`ramSize`
  constructions; interpretation proofs follow the committed
  `freeAlgToNat_ramExp_recurse` induction shape with `objToNat`
  transports). Pre-commit triad; commit (message
  `feat(ramified): add the in-system clock ladder at object sorts`).
- [ ] **Step 4: verify** the whole ladder's interpretation lemmas
  are stated in the exact composite forms Task 5.4c consumes
  (`objToNat`-phrased, tower-aligned).

### Task 5.4b: the machine-state simultaneous recurrence

**Files:**

- Create: `GebLean/Ramified/Definability/Machine.lean` (+ test,
  index imports)

**Interfaces (produces):**

```lean
/-- The per-component step clauses of the machine simulation
(Lemma 6's stt and [φ] clauses, p. 221): for a URMProgram p, the
simultaneous family has 1 + numRegs components at τ = o (component
0 the program counter, component r+1 the register r); the step at
the successor constructor case-splits on the counter value (nested
chooseIdent over the instruction list) and applies, per
instruction, the constructor (inc), ramDstr (dec), ramCase on the
tested register (jumpZ), the constant numeral `c` via numeralTm
(assign — the zero-test URM's assign writes a constant,
ZeroTestURM.lean:90), or the identity (stop) — all explicit
definitions from constructor, destructor, and case functions, as
the Lemma 6 proof requires. Each component's case-split — the pc
component and every register component alike — carries a final
identity arm: `URMState.step` is the identity at every
`pc ≥ instrs.size` (the implicit halt state; `jumpZ` targets are
arbitrary naturals, so runs reach such values), and `chooseIdent`'s
fall-through routes every out-of-range selector to its last
entry. -/
def urmSteps {a : ℕ} (p : URMProgram a) :
    SimulSteps (1 + p.numRegs) (List.replicate a RType.o) RType.o

/-- The machine-tracking family: sttIdent p = simulProj ... 0;
regIdent p r = simulProj ... (r+1); parameters the a inputs at o,
count at ω = Ω(o → o). -/
def sttIdent {a : ℕ} (p : URMProgram a) :
    RIdent natAlgSig
      (List.replicate a RType.o
        ++ [RType.omega (RType.arrow RType.o RType.o)]) RType.o
def regIdent {a : ℕ} (p : URMProgram a) (r : Fin p.numRegs) :
    RIdent natAlgSig
      (List.replicate a RType.o
        ++ [RType.omega (RType.arrow RType.o RType.o)]) RType.o

/-- Correctness against the step relation, by induction on the
count (the Lemma 6 invariant): at count numeral t and input
parameters v, the components denote the pc and registers of
URMState.runFor p (URMState.init p v) t. -/
theorem urm_simul_interp {a : ℕ} (p : URMProgram a)
    (v : Fin a → ℕ) (t : ℕ) :
    freeAlgToNat ((sttIdent p).interp (urmEnv p v t))
        = (URMState.runFor p (URMState.init p v) t).pc ∧
      ∀ r : Fin p.numRegs,
        freeAlgToNat ((regIdent p r).interp (urmEnv p v t))
          = (URMState.runFor p (URMState.init p v) t).regs r
-- urmEnv p v t: the environment loading the input numerals at the
-- o positions and the count numeral t at the Ω(o → o) position
-- (transported along the carrier-copy equalities).
```

- [ ] **Step 1: failing tests.** A two-instruction program (inc
  then stop): `#guard` the register component at counts `0, 1, 2`
  equals `runFor`'s register (small values); the pc component
  freezes at the stop instruction. An implicit-halt fixture: the
  one-instruction program `[inc 0]` — after one step the pc leaves
  the instruction range and the state must freeze (`#guard` the
  register component at counts `1, 2, 3` all equal `1`); this
  exercises the identity arm and the `chooseIdent` fall-through.
- [ ] **Step 2: implement `urmSteps`** (the instruction case-split
  is data-driven over `p.instrs`; each arm is a composition of
  Task 5.1b/5.2a identifiers; the base clause loads
  `URMState.init`'s convention: pc 0, input registers from the
  parameters, work registers 0).
- [ ] **Step 3: prove `urm_simul_interp`** (induction on `t`;
  the step case chains `simulProj_interp` with a case analysis
  matching `URMState.step`'s definition arm by arm).
- [ ] **Step 4: verify, pre-commit triad, commit** (message
  `feat(ramified): simulate the zero-test URM by simultaneous recurrence`).

### Task 5.4c: the eq. (8) assembly and the Lemma 6 statement

**Files:**

- Modify: `GebLean/Ramified/Definability/Machine.lean` (+ test)

**Interfaces (produces):**

```lean
/-- The realizer's input context: input i sits at
inSort p i := Ω(θᵢ → θᵢ) with θᵢ := Ω^{n-1-i}(clockSort q (Ω ω)) —
the staggered sorts letting the size computations chain through
the addition copies (θ', Ω θ' → θ'): the i-th size lands at θᵢ,
partial sums descend one Ω per input, the total lands at
clockSort q (Ω ω), 2_q lands at Ω ω, and the constant multiple
lands at ω through the multiplication copy. Every entry is an
object sort beyond the tower sorts, as spec s6.1 requires. -/
def machineCtx (a q : ℕ) : Ctx RType
theorem machineCtx_isObj (a q : ℕ) :
    ∀ i : Fin (machineCtx a q).length,
      ((machineCtx a q).get i).IsObj
theorem machineCtx_length (a q : ℕ) : (machineCtx a q).length = a

/-- Lemma 6 (paper section 3.2, eq. (8)) against the zero-test URM
(plan decision 1): for p computing f within time c * tower q of
the max input (stated in the runFor-stabilized form — the
idempotent-end convention's URM rendering), a morphism of
RMRecCat natAlgSig over machineCtx whose denotation is f. The
realizer composes, in the object language: deltaIdent on each
input (the parameter loading), the staggered szAtIdent/addAtIdent
sum, twoPowIdent q, the constant multiple via mulAtIdent and
numeralTm, and the count-fed regIdent for the output register.
The docstring records the s1.2 embedding argument (URM versus
Leivant's register machines) as the fidelity justification, and
the eq. (8) sort reconciliation (standing decision 5 and the
Task 5.4 preamble). -/
def machineRealizer {a : ℕ} (p : URMProgram a) (c q : ℕ) :
    Hom (higherOrder natAlgSig)
      (interpQuotRel (higherOrder natAlgSig))
      (machineCtx a q) [RType.o]

/-- The numeric environment over machineCtx: position i carries the
numeral of v i, transported to the carrier copy of its object sort
(natToFreeAlg + the interp_isObj cast; objToNat's inverse
direction). -/
def machineEnv {a : ℕ} (q : ℕ) (v : Fin a → ℕ) :
    (standardModel (higherOrder natAlgSig)).Env (machineCtx a q)

theorem urm_ramified_definable {a : ℕ} (p : URMProgram a)
    (f : (Fin a → ℕ) → ℕ) (c q : ℕ)
    (hf : ∀ (v : Fin a → ℕ) (t : ℕ),
      c * tower q (Fin.maxOfNat a v) ≤ t →
      (URMState.runFor p (URMState.init p v) t).regs p.outputReg
        = f v) :
    ∀ v, freeAlgToNat
        ((machineRealizer p c q).eval (machineEnv q v) 0) = f v
```

- [ ] **Step 1: failing tests.** The inc-then-stop program through
  the full realizer at inputs `0, 2` — stated as `example` proofs
  from the interpretation lemmas (never `#guard`: the composite is
  clocked, pitfalls discipline).
- [ ] **Step 2: implement `machineRealizer`** (a `HomTuple` whose
  sole term composes the ladder identifiers through `Tm.op`
  app-chains; `identHom`/`joinTuple` helpers).
- [ ] **Step 3: prove `urm_ramified_definable`**: the clock
  denotation is `c * tower q (∑ (vᵢ + 1))` by the ladder's
  interpretation lemmas; `maxOfNat_le_sum_succ` + `clock_mono`
  (Task 5.3) give `c * tower q (maxOfNat v) ≤` clock denotation;
  `hf` at `t :=` clock denotation and `urm_simul_interp` close the
  read-off.
- [ ] **Step 4: verify, pre-commit triad, commit** (message
  `feat(ramified): transcribe Lemma 6 against the zero-test URM`).

---

## Task 5.5: the definability family

Master-plan deliverable (unchanged): for every ER morphism, an
object-sort context and a ramified realizer with matching denotation
— chaining `compileER_pre_stop_correct` / `compileER_runFor` +
`boundExprKParams_dominates` (step 1) into Task 5.4 (step 2) into
Task 5.2 (step 3; consumed as direction (a), inlined in Task 5.4's
landing in `RMRecCat`).

**Files:**

- Modify: `GebLean/Ramified/Algebras.lean` (`rfl`-simp lemmas)
- Create: `GebLean/Ramified/Definability/Top.lean` (+ test, index
  imports)

**Interfaces (produces; the master plan's Task 5.5 block realized):**

```lean
-- Algebras.lean:
@[simp] theorem natFreeAlgEquiv_apply (t : FreeAlg natAlgSig) :
    natFreeAlgEquiv t = freeAlgToNat t := rfl
@[simp] theorem natFreeAlgEquiv_symm_apply (n : ℕ) :
    natFreeAlgEquiv.symm n = natToFreeAlg n := rfl

-- Top.lean:
/-- Object-sort contexts of length n (spec s6.1): every entry an
object sort — arbitrary object sorts, beyond the tower sorts
(Lemma 6's realizer input sits at Ω(η → η)-form sorts). The
{s // IsObj s} subtype pattern (Phase 4 review record). -/
def ObjCtx (n : ℕ) : Type := Fin n → { s : RType // s.IsObj }
def ObjCtx.toCtx {n : ℕ} (Γ : ObjCtx n) : Ctx RType
def oCtx (m : ℕ) : ObjCtx m     -- m copies of o
-- length/get simp lemmas for toCtx

/-- The numeric denotation of a morphism between object-sort
contexts: environments built from (Fin n → ℕ) through
natFreeAlgEquiv.symm and the carrier-copy casts (objToNat's
inverse direction), evaluated by Hom.eval, read back through
natFreeAlgEquiv (standing decision 8). -/
def ramifiedDenotation {n m : ℕ} {Γ : ObjCtx n} {Δ : ObjCtx m}
    (g : Hom (higherOrder natAlgSig)
      (interpQuotRel (higherOrder natAlgSig)) Γ.toCtx Δ.toCtx) :
    (Fin n → ℕ) → (Fin m → ℕ)

/-- The definability family (spec s6.1's completeness input; the
denotational content of Leivant III Theorem 14's (1) ⇒ (2)
direction at the 1 + X instantiation): every ER morphism has an
object-sort context and realizer with matching denotation. Chain:
compileER +
boundExprKParams_dominates + tower_clock_format feed
urm_ramified_definable; the realizer is machineRealizer over
machineCtx. -/
theorem erMor_ramified_definable {a : ℕ} (e : ERMor1 a) :
    ∃ (Γ : ObjCtx a)
      (g : Hom (higherOrder natAlgSig)
        (interpQuotRel (higherOrder natAlgSig))
          Γ.toCtx (oCtx 1).toCtx),
      ramifiedDenotation g = fun v _ => e.interp v
-- (oCtx 1).toCtx is definitionally [RType.o]; the master plan's
-- `Γ ⟶ ([RType.o] : RMRecCat natAlgSig)` form is recovered by the
-- SynCat coercion.

/-- The m-output form, assembled componentwise with a common clock
(c, q taken as the maxima over the components, so the m realizers
share machineCtx; the tuple is joinTuple's product pairing). -/
theorem erMorN_ramified_definable {a m : ℕ}
    (e : Fin m → ERMor1 a) :
    ∃ (Γ : ObjCtx a)
      (g : Hom (higherOrder natAlgSig)
        (interpQuotRel (higherOrder natAlgSig))
          Γ.toCtx (oCtx m).toCtx),
      ramifiedDenotation g = fun v j => (e j).interp v
```

- [ ] **Step 1: failing tests.** `ramifiedDenotation` of the
  identity hom on `oCtx 2` is the identity (`example ... := rfl` or
  via the simp lemmas); of `identHom ramAdd` (cast to the `ObjCtx`
  form) is addition at `(2, 3)`; an `example` instantiating
  `erMor_ramified_definable` on a concrete small `ERMor1` (e.g. a
  projection or successor composite) — existence via the theorem,
  not kernel reduction.
- [ ] **Step 2: implement** the simp lemmas and `ObjCtx` layer;
  then `ramifiedDenotation` (through `Hom.eval`, Task 5.1a); then
  the chain: `boundExprKParams_dominates` gives the tower bound;
  `tower_add_le_tower`/`tower_clock_format` convert to the
  `c * tower q (maxOfNat v)` hypothesis; `compileER_runFor`
  supplies the runFor-stabilized computation of `e.interp`;
  `urm_ramified_definable` at `p := compileER e` yields the
  realizer; `Γ := machineCtx` entries with `machineCtx_isObj`.
  Module docstring carries the G4 Otto precedent paragraph and the
  Theorem 14 (1) ⇒ (2) citation (section 6.1 of the paper via
  sections 2.7/3.2; DOI `10.1016/S0168-0072(98)00040-2`), and
  notes that Phase 7 re-states the family as
  `ramified_definability` against `collapseDenotation`.
- [ ] **Step 3: verify, pre-commit triad, commit** (message
  `feat(ramified): assemble the ER definability family`).
- [ ] **Step 4: phase review.** Run
  superpowers:requesting-code-review over the branch;
  superpowers:verification-before-completion before any completion
  claim; resolve findings; offer the branch for user line-by-line
  review together with this sub-plan's standing decisions.

---

## Self-review checklist (run before adversarial review)

- Task boundaries, deliverable statements, and plan decision 1
  match the master plan's Phase 5 section, with two recorded
  amendments: the Task 5.3 ladder-link supersession (standing
  decision 2, noted in the Task 5.3 preamble) and the relocation of
  the m-output componentwise assembly to Task 5.5 under the
  master's own Task 5.5 delegation (noted in the Task 5.4
  preamble). The structural additions are sub-task splits (5.1a-c,
  5.2a-d, 5.4a-c) and the modify-file additions the collected
  Task 5.0 inputs direct.
- All seven collected Task 5.0 inputs are addressed: full kappa-hat
  (5.4a; standing decision 3), the in-system clock (5.4a/c;
  decision 2), sz typing (5.4a; decision 4), `natFreeAlgEquiv` simp
  lemmas and the `ramifiedDenotation` statement form (5.5;
  decision 8), objToNat placement (decision 6), `ObjCtx` pattern +
  `Hom.eval` early motion + `foOp` template + no-`Decidable`
  certificates (5.1a, 5.2c, decision 7), `#guard` fallback ladder
  (Global constraints).
- Every interface consumed by a later task is produced by an
  earlier one (`ramCase`/`ramDstr`/`chooseIdent` before
  `simulIdent`; `SimulSteps` before `urmSteps`; the ladder before
  the assembly; Bounds before 5.4c/5.5).
- Deviations from the paper's surface presentation are each named,
  justified under spec s1.2, and assigned a docstring record
  (standing decisions 2, 4, 5; the eq. (8) sort reconciliation).
- No placeholder text; every code step names concrete declarations
  or the committed pattern it instantiates.

## References

- D. Leivant, "Ramified recurrence and computational complexity
  III: Higher type recurrence and elementary complexity", APAL 96
  (1999) 209-229. DOI `10.1016/S0168-0072(98)00040-2`. Sections
  2.4-2.6 (pp. 215-218), 3.1-3.2 (pp. 219-221, Lemma 6 and
  eq. (8)).
- Master plan:
  `docs/superpowers/plans/2026-07-02-ramified-recurrence-plan.md`
  (Phase 5; consumed-interfaces block; decisions 1-8).
- Spec:
  `docs/superpowers/specs/2026-07-01-ramified-recurrence-approaches-design.md`
  (s1.2, s4.2, s6.1, s6.2).
- Gate record:
  `docs/superpowers/notes/2026-07-02-ramified-gates-decisions.md`
  (G4 precedent wording).
- J. R. Otto, "Complexity Doctrines", PhD thesis, McGill
  University, 1995, DOI `10.82308/7828` (precedent line, gate G4).
