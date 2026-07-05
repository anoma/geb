import Mathlib.Data.Finset.Sort
import GebLean.Binding.Term
import GebLean.Binding.Substitution
import GebLean.Binding.Laws
import GebLean.Ramified.HigherOrder
import GebLean.Ramified.Definability.Flat

/-!
# The applicative calculi as binder signatures

The object-sorted applicative λ-calculus `RλMR_o^ω(𝔸)` of Leivant III
section 4.1 (p. 222), realized as a binding signature (`BinderSig`) over the
ramified types, an instance of the indexed binder-substitution kit
(`GebLean/Binding/`). The calculus types terms by r-types and builds them from
typed variables by λ-abstraction (`lam`) and application (`app`) over a family
of typed constants: the constructors `c_iθ : θ^{r_i} → θ`, the recurrence
combinators `R^τ : α_1, …, α_k, Ωτ → τ`, the destructors `dstr_j : o → o`, and
the case combinators `case^θ : o, θ^k → θ`.

The soundness arm `(1)⟹(4)` of Leivant III Proposition 7 (`prop7Translate`) is
transcribed directly to this object-sorted calculus, inlining the paper's
flat-operator realization (the `(3)⟹(4)` step, §4.1 Examples 1–2) into the
flat-recurrence case, rather than routing through the full calculus `RλMR^ω`
with its flat-recurrence combinators `F^τ : ξ_1, …, ξ_k, o → τ`.

All constants are nullary operations of the signature: their full curried arrow
type is the operation's result and their argument list is empty (the source
builds terms from the constants "by λ-abstraction and application", so only
`app` and `lam` carry arguments or binders). `app` and `lam` are the two
operations that carry subterm arguments; `lam σ τ` binds one variable of sort
`σ` in a body of sort `τ` (the append-at-end binder `Ξ = [σ]` of `BinderSig`).

## Main definitions

* `ctorList` — the shared ordered enumeration of a finite algebra's
  constructor labels, reused across all of Phase 6.1.
* `stepTypes` — the list of step-function types `[c_i-arity fold]` common to the
  recurrence and flat-recurrence combinators.
* `RlmrOOp` — the operation type of the object-sorted calculus.
* `rlmrOSig` — the signature of `RλMR_o^ω`: `app`, `lam`, `con`, `recur`,
  `dstr`, `case`.
* `app'`, `lam'`, `boundVar` — the application, abstraction, and bound-variable
  combinators of `rlmrOSig`.
* `appSpine`, `replicateSpine` — iterated application of a curried head to a
  dependent, respectively homogeneous, argument tuple.
* `stepEnvOfFun`, `recCombinator` — the recurrence combinator `R^τ E⃗` and the
  per-constructor-to-positional step-tuple conversion it uses.
* `ctorAt` — the constructor label at an enumeration position.
* `RlmrOStep` — one-step reduction of `RλMR_o^ω(A)` (Leivant III section 4.1).
* `ctorIdx`, `stepAtLabel` — the label-to-position lookup on `ctorList natAlgSig`
  and the positional read-out of a recursor's step function it enables.
* `envCastCtx`, `envExtend` — the environment transport across `Γ ++ [] = Γ` and
  the environment extension by one bound value.
* `appEvalOp`, `appEval` — the standard-model denotation of an operation node and
  the standard-model evaluator of an object-sorted applicative term over
  `natAlgSig` (Leivant III section 4.1, the standard semantics of section 2.7).
* `lamSpine`, `suffixThinning` — iterated λ-abstraction of a context suffix and
  the suffix inclusion into an append-at-end context.
* `joinEnv` — the semantic environment gluing a prefix environment with a suffix
  environment, the arbitrary-suffix generalization of `childEnv`.
* `defnModelTerm`, `prop7DefnStep` — the applicative-term model of a definition's
  body and the direct translation of an explicit-definition identifier.
* `caseAtType`, `frecBranch`, `prop7MrecStep`, `prop7FrecStep` — the higher-type
  case realization, one flat-recurrence branch, and the direct translations of a
  monotone- and a flat-recurrence identifier.
* `prop7TranslateStep`, `prop7Translate` — the per-node translation step and the
  direct Proposition 7 translation.

## Main statements

* `ctorList_length` — the constructor enumeration has length `A.numCtors`.
* `ctorList_get_ctorIdx` — `ctorIdx` is a right inverse of the enumeration
  read-off.
* `appEval_var`, `appEval_op`, `appEval_congr_ctx` — the fold's base and
  operation cases and the context-transport coherence.
* `appEval_app'`, `appEval_lam'`, `appEval_con`, `appEval_recur`, `appEval_dstr`,
  `appEval_case` — the evaluation of `appEval` through the term combinators.
* `arrow_node_eq` — an `arrow`-shape free-algebra node is the `RType.arrow` of
  its two children.
* `appEval_ren`, `appEval_lamSpine` — renaming fusion for `appEval` and the
  evaluation of the applicative λ-spine.
* `prop7MrecStep_interp` — the monotone-recurrence step of the Proposition 7
  translation preserves the denoted function.
* `prop7Translate_interp` — the direct Proposition 7 translation preserves the
  denoted function (the soundness arm `(1)⟹(4)`).

## Implementation notes

`RlmrOOp` is a finite non-recursive enumeration (like the fields of `BinderSig`
itself), not a `PolyFix` W-type; decision 8's requirement that recursive types
be W-types of a `PolyEndo` does not apply to this first-order label data.

## References

D. Leivant, "Ramified recurrence and computational complexity III: Higher type
recurrence and elementary complexity", Annals of Pure and Applied Logic 96
(1999) 209-229, DOI `10.1016/S0168-0072(98)00040-2`. The object-sorted
applicative λ-calculus `RλMR_o^ω`, its typed constants, and the destructor and
case operations are section 4.1 (p. 222); Proposition 7's soundness arm
`(1)⟹(4)` and its flat-operator realization (§4.1 Examples 1–2) are the same
section. The `BinderSig` realization is novel packaging.

## Tags

ramified recurrence, applicative calculus, lambda calculus, binding signature,
higher type, soundness
-/

namespace GebLean.Ramified

open GebLean.Binding

/-- The canonical `LinearOrder` on the constructor labels of the `1 + X` word
algebra `natAlgSig`, its labels being `Bool`. Supplies the ordered enumeration
`ctorList natAlgSig` used by the recurrence combinators of the applicative
signatures over `natAlgSig`; mirrors `instFintypeNatAlgSigB`. -/
instance instLinearOrderNatAlgSigB : LinearOrder natAlgSig.B :=
  (inferInstance : LinearOrder Bool)

/-- The ordered enumeration of a finite free-algebra signature's constructor
labels. The recurrence combinator `R^τ` and the flat-recurrence combinator
`F^τ` are `k`-fold products whose summands differ by constructor arity, so
their result types need a fixed order on `A.B`; this definition supplies it as
the canonical ascending sort under `[LinearOrder A.B]`. The concrete order is
immaterial to correctness, provided the same `ctorList` is reused by the
reductions and the interpretation of Phase 6.1 — a consistency contract on all
consumers, met automatically since the sort is determined by the order
instance. A `LinearOrder`, rather than a bare `Fintype`, is required because
`Fintype` provides no constructive enumeration (its `Finset.toList` is
`noncomputable`), whereas `Finset.sort` is computable. -/
def ctorList (A : AlgSig) [Fintype A.B] [LinearOrder A.B] : List A.B :=
  Finset.univ.sort (· ≤ ·)

/-- The list of step-function types of a recurrence-style combinator over a
finite algebra `A`: one entry per constructor `c_i`, namely `base^{r_i} →
result` (the curried arrow with `r_i = A.ar c_i` copies of `base`). At
`base = result = τ` these are the types `α_i ≡ τ^{r_i} → τ` of the recurrence
combinator `R^τ`; at `base = o`, `result = τ` they are the types
`ξ_i ≡ o^{r_i} → τ` of the flat-recurrence combinator `F^τ` (Leivant III
section 4.1). -/
def stepTypes (A : AlgSig) [Fintype A.B] [LinearOrder A.B] (base result : RType) :
    List RType :=
  (ctorList A).map (fun b => RType.curried (List.replicate (A.ar b) base) result)

/-- The operations of the object-sorted applicative calculus `RλMR_o^ω(A)`
(Leivant III section 4.1): application, λ-abstraction, the constructor and
recurrence constants, and — replacing the flat-recurrence combinator — the
destructors `dstr_j : o → o` for `j < A.maxArity` and the case combinators
`case θ : o, θ^k → θ`. A finite non-recursive label type. -/
inductive RlmrOOp (A : AlgSig) [Fintype A.B] where
  /-- Application at domain sort `σ` and codomain sort `τ`. -/
  | app (σ τ : RType)
  /-- λ-abstraction binding a variable of sort `σ` in a body of sort `τ`. -/
  | lam (σ τ : RType)
  /-- The constructor constant `c_bθ : θ^{A.ar b} → θ` at an object type `θ`
  (Leivant restricts the constructor constants to object sorts). -/
  | con (θ : RType) (hθ : θ.IsObj) (b : A.B)
  /-- The recurrence combinator `R^τ : α_1, …, α_k, Ωτ → τ`. -/
  | recur (τ : RType)
  /-- The destructor `dstr_j : o → o`, `j` ranging over `Fin A.maxArity`. -/
  | dstr (j : Fin A.maxArity)
  /-- The case combinator `case θ : o, θ^k → θ` at an object type `θ`
  (Leivant restricts the case operations to object sorts). -/
  | case (θ : RType) (hθ : θ.IsObj)

/-- The binding signature of the object-sorted applicative calculus
`RλMR_o^ω(A)` (Leivant III section 4.1): the application `app`, the abstraction
`lam`, the constructor constants `con`, and the recurrence combinator `recur`,
together with the destructors `dstr j : o.arrow o` and the case combinators
`case θ : o.arrow (θ^k → θ)` realizing flat recurrence (both nullary). Novel
packaging of section 4.1. -/
def rlmrOSig (A : AlgSig) [Fintype A.B] [LinearOrder A.B] : BinderSig RType where
  Op := RlmrOOp A
  result := fun
    | .app _ τ => τ
    | .lam σ τ => RType.arrow σ τ
    | .con θ _ b => RType.curried (List.replicate (A.ar b) θ) θ
    | .recur τ => RType.curried (stepTypes A τ τ) (RType.arrow (RType.omega τ) τ)
    | .dstr _ => RType.arrow RType.o RType.o
    | .case θ _ => RType.arrow RType.o (RType.curried (List.replicate A.numCtors θ) θ)
  args := fun
    | .app σ τ => [([], RType.arrow σ τ), ([], σ)]
    | .lam σ τ => [([σ], τ)]
    | .con _ _ _ => []
    | .recur _ => []
    | .dstr _ => []
    | .case _ _ => []

/-- Application node `f x` of `rlmrOSig`: the operation `app σ τ`, whose two
subterm arguments carry the empty binder context. Since `Γ ++ [] = Γ` is not
definitional (`List.append` recurses on its first argument), the function and
argument terms are transported into the argument context `Γ ++ []` along
`List.append_nil`. -/
def app' {A : AlgSig} [Fintype A.B] [LinearOrder A.B] {Γ : Binding.Ctx RType}
    {σ τ : RType} (f : Binding.Tm (rlmrOSig A) Γ (RType.arrow σ τ))
    (x : Binding.Tm (rlmrOSig A) Γ σ) : Binding.Tm (rlmrOSig A) Γ τ :=
  Binding.Tm.op (S := rlmrOSig A) (RlmrOOp.app σ τ) (fun j =>
    Fin.cases ((List.append_nil Γ).symm ▸ f)
      (fun k => Fin.cases ((List.append_nil Γ).symm ▸ x) (fun l => l.elim0) k) j)

/-- Abstraction node `λ(:σ). b` of `rlmrOSig`: the operation `lam σ τ`, whose
sole subterm argument binds one variable of sort `σ` at the end of the context,
so the body `b` lives in `Γ ++ [σ]` with no transport required. -/
def lam' {A : AlgSig} [Fintype A.B] [LinearOrder A.B] {Γ : Binding.Ctx RType}
    {σ τ : RType} (b : Binding.Tm (rlmrOSig A) (Γ ++ [σ]) τ) :
    Binding.Tm (rlmrOSig A) Γ (RType.arrow σ τ) :=
  Binding.Tm.op (S := rlmrOSig A) (RlmrOOp.lam σ τ)
    (fun j => Fin.cases b (fun k => k.elim0) j)

/-- The variable bound by `lam' σ …`: the unique variable of the singleton
suffix `[σ]`, embedded into `Γ ++ [σ]` by the suffix inclusion
`Var.appendRight`. -/
def boundVar {Γ : Binding.Ctx RType} {σ : RType} : Binding.Var (Γ ++ [σ]) σ :=
  Binding.Var.appendRight Γ ⟨0, rfl⟩

/-- Iterated application of a head term `f` at a curried arrow sort to a
dependent tuple of arguments whose sorts are `Ts`, producing the curried result.
Recursion on `Ts`: peel the head sort via `app'`, using that
`RType.curried (T :: Ts) r = RType.arrow T (RType.curried Ts r)` holds
definitionally (`RType.curried_cons`). -/
def appSpine {A : AlgSig} [Fintype A.B] [LinearOrder A.B] {Γ : Binding.Ctx RType}
    {result : RType} : (Ts : List RType) →
    Binding.Tm (rlmrOSig A) Γ (RType.curried Ts result) →
    (∀ i : Fin Ts.length, Binding.Tm (rlmrOSig A) Γ (Ts.get i)) →
    Binding.Tm (rlmrOSig A) Γ result
  | [], head, _ => head
  | _ :: Ts', head, args =>
      appSpine Ts' (app' head (args ⟨0, Nat.succ_pos _⟩)) (fun i => args i.succ)

/-- Application of a head at a homogeneous curried sort `base^n → result` to a
tuple of `n` arguments all of sort `base`: `appSpine` specialized to
`Ts = List.replicate n base`, with the per-index sort reduced to `base` via
`List.getElem_replicate`. The uniform interface (`Fin n → Tm Γ base`) hides the
`List.replicate`-position transport from callers building constructor and
recurrence redexes. -/
def replicateSpine {A : AlgSig} [Fintype A.B] [LinearOrder A.B]
    {Γ : Binding.Ctx RType} {result : RType} (n : Nat) (base : RType)
    (head : Binding.Tm (rlmrOSig A) Γ (RType.curried (List.replicate n base) result))
    (args : Fin n → Binding.Tm (rlmrOSig A) Γ base) :
    Binding.Tm (rlmrOSig A) Γ result :=
  appSpine (List.replicate n base) head (fun idx => by
    rw [List.get_eq_getElem, List.getElem_replicate]
    exact args (idx.cast List.length_replicate))

/-- The positional step-term tuple of the recurrence combinator, assembled from a
per-constructor family `Estep`: the argument tuple `appSpine` consumes for the
head `R^τ`, whose `idx`-th sort is `(stepTypes A τ τ).get idx =
α_{ctorList.get idx}`. Reduces that sort via `List.getElem_map`, so the caller
supplies one step term per constructor label rather than per enumeration
position. -/
def stepEnvOfFun {A : AlgSig} [Fintype A.B] [LinearOrder A.B]
    {Γ : Binding.Ctx RType} {τ : RType}
    (Estep : ∀ b : A.B,
      Binding.Tm (rlmrOSig A) Γ (RType.curried (List.replicate (A.ar b) τ) τ)) :
    ∀ idx : Fin (stepTypes A τ τ).length,
      Binding.Tm (rlmrOSig A) Γ ((stepTypes A τ τ).get idx) :=
  fun idx => by
    unfold stepTypes
    rw [List.get_eq_getElem, List.getElem_map]
    exact Estep _

/-- The recurrence combinator saturated with its step terms, `R^τ E⃗`: the head
`recur τ` applied along `stepTypes A τ τ` to the positional step tuple built from
`Estep`, leaving a function of sort `Ωτ → τ` awaiting the recurrence argument
(Leivant III section 4.1). -/
def recCombinator {A : AlgSig} [Fintype A.B] [LinearOrder A.B]
    {Γ : Binding.Ctx RType} {τ : RType}
    (Estep : ∀ b : A.B,
      Binding.Tm (rlmrOSig A) Γ (RType.curried (List.replicate (A.ar b) τ) τ)) :
    Binding.Tm (rlmrOSig A) Γ (RType.arrow (RType.omega τ) τ) :=
  appSpine (stepTypes A τ τ)
    (Binding.Tm.op (S := rlmrOSig A) (RlmrOOp.recur τ) (fun j => j.elim0))
    (stepEnvOfFun Estep)

/-- Iterated λ-abstraction of a context suffix into curried arrows: from a body
in the append-at-end extension `Γ ++ Δ` at sort `τ`, the term in `Γ` at the
curried sort `RType.curried Δ τ` binding the suffix `Δ` from the outside in.
Recursion on `Δ`: peel the head sort via `lam'`, reassociating the append
`Γ ++ (σ :: Δ') = (Γ ++ [σ]) ++ Δ'` (`List.append_assoc`) so the tail
abstraction sees the freshly bound variable at the end of its context. The
combinator dual to `appSpine`, used to turn a child identifier's open body into
a combinator value or a recurrence step function. -/
def lamSpine {A : AlgSig} [Fintype A.B] [LinearOrder A.B] {Γ : Binding.Ctx RType} :
    (Δ : List RType) → {τ : RType} →
    Binding.Tm (rlmrOSig A) (Γ ++ Δ) τ → Binding.Tm (rlmrOSig A) Γ (RType.curried Δ τ)
  | [], _τ, body =>
    cast (congrArg (fun c => Binding.Tm (rlmrOSig A) c _) (List.append_nil Γ)) body
  | σ :: Δ', _τ, body =>
    lam' (lamSpine Δ'
      (cast (congrArg (fun c => Binding.Tm (rlmrOSig A) c _)
        (List.append_assoc Γ [σ] Δ').symm) body))

/-- The constructor enumeration `ctorList A` has length `A.numCtors`: the sorted
enumeration of `Finset.univ` has cardinality `Fintype.card A.B`. -/
theorem ctorList_length {A : AlgSig} [Fintype A.B] [LinearOrder A.B] :
    (ctorList A).length = A.numCtors := by
  unfold ctorList AlgSig.numCtors
  rw [Finset.length_sort]
  exact Finset.card_univ

/-- The constructor label at enumeration position `idx : Fin A.numCtors`: the
`idx`-th entry of `ctorList A`, indexing through `ctorList_length`. Names the
scrutinee constructor of the case rule from a branch position, so its contractum
selects the branch `b idx` without an `idxOf` search. -/
def ctorAt {A : AlgSig} [Fintype A.B] [LinearOrder A.B] (idx : Fin A.numCtors) : A.B :=
  (ctorList A).get (idx.cast ctorList_length.symm)

/-- One-step reduction of the object-sorted applicative calculus `RλMR_o^ω(A)`
(Leivant III section 4.1, p. 222). A `Prop`-valued inductively-defined relation:
its inhabitants are reduction proofs, not computational data, so decision 8's
requirement that recursive data be a `PolyFix` W-type does not apply. The six
rules are β and η for the `lam`/`app`
fragment, the recurrence contraction, the two destructor cases (`dstr` on a
matching or non-matching argument position), and the case contraction; redexes
and contracta are built from the term combinators `app'`, `lam'`,
`replicateSpine`, and `recCombinator`. -/
inductive RlmrOStep {A : AlgSig} [Fintype A.B] [LinearOrder A.B]
    {Γ : Binding.Ctx RType} :
    {s : RType} → Binding.Tm (rlmrOSig A) Γ s → Binding.Tm (rlmrOSig A) Γ s → Prop where
  /-- β: `(λx:σ. b) N ⇒ b[x := N]`, the substitution `instantiate₁`. -/
  | beta {σ τ : RType} (b : Binding.Tm (rlmrOSig A) (Γ ++ [σ]) τ)
      (N : Binding.Tm (rlmrOSig A) Γ σ) :
      RlmrOStep (app' (lam' b) N) (Binding.instantiate₁ N b)
  /-- η: `λx:σ. (M x) ⇒ M`. The body applies the pre-weakened `M` (renamed along
  the suffix embedding into `Γ ++ [σ]`) to the freshly bound variable, so no
  free-variable side condition is needed. -/
  | eta {σ τ : RType} (M : Binding.Tm (rlmrOSig A) Γ (RType.arrow σ τ)) :
      RlmrOStep
        (lam' (app' (Binding.ren (Binding.Thinning.weakAppend (Ξ := [σ])) M)
          (Binding.Tm.var boundVar))) M
  /-- Recurrence: `R^τ E⃗ (c_i^{Ωτ} t₁…t_{r_i}) ⇒ E_i (R^τ E⃗ t₁)…(R^τ E⃗ t_{r_i})`.
  The recurrence combinator `R^τ E⃗ = recCombinator Estep` is applied to the
  constructor `c_i` at the shifted object type `Ωτ = RType.omega τ`; the
  contractum applies the `i`-th step term `Estep i` to the recursive results. -/
  | recurrence {τ : RType} (i : A.B)
      (Estep : ∀ b : A.B,
        Binding.Tm (rlmrOSig A) Γ (RType.curried (List.replicate (A.ar b) τ) τ))
      (t : Fin (A.ar i) → Binding.Tm (rlmrOSig A) Γ (RType.omega τ)) :
      RlmrOStep
        (app' (recCombinator Estep)
          (replicateSpine (A.ar i) (RType.omega τ)
            (Binding.Tm.op (S := rlmrOSig A) (RlmrOOp.con (RType.omega τ) (Or.inr rfl) i)
              (fun j => j.elim0)) t))
        (replicateSpine (A.ar i) τ (Estep i)
          (fun j => app' (recCombinator Estep) (t j)))
  /-- Destructor hit (`j < r_i`): `dstr_j (c_i^o a₁…a_{r_i}) ⇒ a_j`. -/
  | dstrHit {i : A.B} (j : Fin A.maxArity) (h : j.val < A.ar i)
      (a : Fin (A.ar i) → Binding.Tm (rlmrOSig A) Γ RType.o) :
      RlmrOStep
        (app' (Binding.Tm.op (S := rlmrOSig A) (RlmrOOp.dstr j) (fun k => k.elim0))
          (replicateSpine (A.ar i) RType.o
            (Binding.Tm.op (S := rlmrOSig A) (RlmrOOp.con RType.o (Or.inl rfl) i)
              (fun k => k.elim0)) a))
        (a ⟨j.val, h⟩)
  /-- Destructor miss (`j ≥ r_i`): `dstr_j (c_i^o ā) ⇒ c_i^o ā`, identity on the
  scrutinee. -/
  | dstrMiss {i : A.B} (j : Fin A.maxArity) (h : A.ar i ≤ j.val)
      (a : Fin (A.ar i) → Binding.Tm (rlmrOSig A) Γ RType.o) :
      RlmrOStep
        (app' (Binding.Tm.op (S := rlmrOSig A) (RlmrOOp.dstr j) (fun k => k.elim0))
          (replicateSpine (A.ar i) RType.o
            (Binding.Tm.op (S := rlmrOSig A) (RlmrOOp.con RType.o (Or.inl rfl) i)
              (fun k => k.elim0)) a))
        (replicateSpine (A.ar i) RType.o
          (Binding.Tm.op (S := rlmrOSig A) (RlmrOOp.con RType.o (Or.inl rfl) i)
            (fun k => k.elim0)) a)
  /-- Case: `case^θ (c_i^o ā) b₁…b_k ⇒ b_i`, selecting the branch at the
  scrutinee constructor's enumeration position `idx`. -/
  | case {θ : RType} (hθ : θ.IsObj) (idx : Fin A.numCtors)
      (a : Fin (A.ar (ctorAt idx)) → Binding.Tm (rlmrOSig A) Γ RType.o)
      (b : Fin A.numCtors → Binding.Tm (rlmrOSig A) Γ θ) :
      RlmrOStep
        (replicateSpine A.numCtors θ
          (app' (Binding.Tm.op (S := rlmrOSig A) (RlmrOOp.case θ hθ) (fun k => k.elim0))
            (replicateSpine (A.ar (ctorAt idx)) RType.o
              (Binding.Tm.op (S := rlmrOSig A) (RlmrOOp.con RType.o (Or.inl rfl) (ctorAt idx))
                (fun k => k.elim0)) a))
          b)
        (b idx)

/-- The enumeration position of a constructor label of `natAlgSig` in
`ctorList natAlgSig`: the first index at which the label occurs. Inverts
`ctorAt` on the standard signature, letting the standard-model recursor recover
the step function that the positional step tuple stores for a given label
(`stepAtLabel`). -/
def ctorIdx (b : natAlgSig.B) : Fin (ctorList natAlgSig).length :=
  ⟨(ctorList natAlgSig).idxOf b,
    List.idxOf_lt_length_of_mem (by
      rw [ctorList]; exact (Finset.mem_sort _).mpr (Finset.mem_univ b))⟩

/-- `ctorIdx` is a right inverse of the enumeration read-off: the label at
position `ctorIdx b` of `ctorList natAlgSig` is `b`. -/
theorem ctorList_get_ctorIdx (b : natAlgSig.B) :
    (ctorList natAlgSig).get (ctorIdx b) = b := by
  simp only [List.get_eq_getElem, ctorIdx]
  exact List.getElem_idxOf _

/-- The step function of a recurrence over `natAlgSig` at result sort `τ` for a
constructor label `b`, read out of the positional step environment `stepEnv`
that the applicative recursor stores over `stepTypes natAlgSig τ τ`: the entry
at `b`'s enumeration position `ctorIdx b`, transported from the position's sort
to `b`'s step type `τ^{ar b} → τ`. The label-to-position lookup inverts
`stepEnvOfFun`, so the recursor's contraction reaches the step term that the
reduction rule `RlmrOStep.recurrence` selects. -/
def stepAtLabel {τ : RType}
    (stepEnv : ∀ idx : Fin (stepTypes natAlgSig τ τ).length,
      RType.interp (FreeAlg natAlgSig) ((stepTypes natAlgSig τ τ).get idx))
    (b : natAlgSig.B) :
    RType.interp (FreeAlg natAlgSig)
      (RType.curried (List.replicate (natAlgSig.ar b) τ) τ) := by
  have hlen : (stepTypes natAlgSig τ τ).length = (ctorList natAlgSig).length := by
    rw [stepTypes, List.length_map]
  have hb : (ctorIdx b).val < (stepTypes natAlgSig τ τ).length := by
    rw [hlen]; exact (ctorIdx b).isLt
  refine cast (congrArg (RType.interp (FreeAlg natAlgSig)) ?_)
    (stepEnv ⟨(ctorIdx b).val, hb⟩)
  simp only [stepTypes, List.get_eq_getElem, List.getElem_map]
  exact congrArg (fun c => RType.curried (List.replicate (natAlgSig.ar c) τ) τ)
    (ctorList_get_ctorIdx b)

/-- Transport of a semantic environment along an equality of contexts. Realizes
the definitional coincidence `Γ ++ [] = Γ` (not definitional, since `List.append`
recurses on its first argument) at the level of environments, the semantic
counterpart of the `List.append_nil` transport in `app'`. -/
def envCastCtx {Γ Δ : Binding.Ctx RType} (h : Γ = Δ)
    (ρ : ∀ i : Fin Γ.length, RType.interp (FreeAlg natAlgSig) (Γ.get i)) :
    ∀ i : Fin Δ.length, RType.interp (FreeAlg natAlgSig) (Δ.get i) := h ▸ ρ

/-- Extension of a semantic environment by one value at the end of the context,
the semantic counterpart of the append-at-end binder of `lam'`: from an
environment `ρ` for `Γ` and a value `v` at sort `σ`, the environment for
`Γ ++ [σ]` sending the freshly bound last position to `v` and the old positions
to `ρ`. Reuses `childEnv` at the singleton suffix `[σ] = List.replicate 1 σ`. -/
def envExtend {Γ : Binding.Ctx RType} {σ : RType}
    (ρ : ∀ i : Fin Γ.length, RType.interp (FreeAlg natAlgSig) (Γ.get i))
    (v : RType.interp (FreeAlg natAlgSig) σ) :
    ∀ i : Fin (Γ ++ [σ]).length, RType.interp (FreeAlg natAlgSig) ((Γ ++ [σ]).get i) :=
  childEnv Γ σ 1 ρ (fun _ => v)

/-- The standard-model denotation of an operation node of the object-sorted
applicative calculus over `natAlgSig`: given the denotations `ih` of the node's
subterms (each a function of an environment for the ambient context extended by
that subterm's bound sorts), the value of the node as a function of an
environment for the ambient context. The per-operation dispatch, the semantic
twin of the operation case of `Binding.traverse` and the applicative analogue of
`RIdentO.interpStep`:

* `app` applies the function denotation to the argument denotation, transporting
  the environment across `Γ ++ [] = Γ` (`envCastCtx`);
* `lam` produces the semantic function, extending the environment by the bound
  value (`envExtend`);
* `con` is the curried constructor `stdConstructorInterp` at the object sort;
* `recur` is the curried closed recurrence `FreeAlg.recurse` reading its step
  functions positionally (`stepAtLabel`) and its recurrence argument last;
* `dstr` is the destructor `dstrRead`;
* `case` is the branch selector `caseSelect`, curried over its branches; over
  `natAlgSig` (`numCtors = 2`) the case denotation reads exactly two branches,
  at enumeration positions `0` and `1`. -/
def appEvalOp {Γ : Binding.Ctx RType} (o : RlmrOOp natAlgSig)
    (ih : ∀ j : Fin ((rlmrOSig natAlgSig).args o).length,
      (∀ i : Fin (Γ ++ (((rlmrOSig natAlgSig).args o).get j).1).length,
        RType.interp (FreeAlg natAlgSig)
          ((Γ ++ (((rlmrOSig natAlgSig).args o).get j).1).get i)) →
        RType.interp (FreeAlg natAlgSig) (((rlmrOSig natAlgSig).args o).get j).2) :
    (∀ i : Fin Γ.length, RType.interp (FreeAlg natAlgSig) (Γ.get i)) →
      RType.interp (FreeAlg natAlgSig) ((rlmrOSig natAlgSig).result o) := by
  cases o with
  | app σ τ =>
    have h0 : (0 : Nat) < ((rlmrOSig natAlgSig).args (RlmrOOp.app σ τ)).length :=
      Nat.zero_lt_two
    have h1 : (1 : Nat) < ((rlmrOSig natAlgSig).args (RlmrOOp.app σ τ)).length :=
      Nat.one_lt_two
    exact fun ρ =>
      (ih ⟨0, h0⟩ (envCastCtx (List.append_nil Γ).symm ρ))
        (ih ⟨1, h1⟩ (envCastCtx (List.append_nil Γ).symm ρ))
  | lam σ τ =>
    have h0 : (0 : Nat) < ((rlmrOSig natAlgSig).args (RlmrOOp.lam σ τ)).length :=
      Nat.zero_lt_one
    exact fun ρ v => ih ⟨0, h0⟩ (envExtend ρ v)
  | con θ hθ b =>
    exact fun _ρ =>
      curryInterp natAlgSig (List.replicate (natAlgSig.ar b) θ) θ
        (stdConstructorInterp natAlgSig (⟨θ, hθ⟩, b))
  | recur τ =>
    exact fun _ρ =>
      curryInterp natAlgSig (stepTypes natAlgSig τ τ) (RType.arrow (RType.omega τ) τ)
        (fun stepEnv z =>
          FreeAlg.recurse (A := natAlgSig) (P := Unit)
            (fun i _ _sub phi =>
              appChain natAlgSig (List.replicate (natAlgSig.ar i) τ) τ
                (stepAtLabel stepEnv i)
                (childEnv [] τ (natAlgSig.ar i) finZeroElim phi))
            () z)
  | dstr j => exact fun _ρ => dstrRead j.val
  | case θ hθ =>
    exact fun _ρ z =>
      curryInterp natAlgSig (List.replicate natAlgSig.numCtors θ) θ
        (fun branchEnv =>
          caseSelect z
            (cast (congrArg (RType.interp (FreeAlg natAlgSig))
              (by rw [List.get_eq_getElem, List.getElem_replicate]))
              (branchEnv ⟨0, (by decide : (0:Nat) < 2)⟩))
            (cast (congrArg (RType.interp (FreeAlg natAlgSig))
              (by rw [List.get_eq_getElem, List.getElem_replicate]))
              (branchEnv ⟨1, (by decide : (1:Nat) < 2)⟩)))

/-- The standard-model denotation of an object-sorted applicative term: a
function from a semantic environment at its context to a value at its sort, over
the standard carrier `FreeAlg natAlgSig`. Env-passing fold via `PolyFix.ind`
(decision 8), the semantic twin of `Binding.traverse` (`GebLean/Binding/Kit.lean`)
and the applicative analogue of `RIdentO.interp` (Leivant III section 4.1). A
variable leaf reads the environment at that variable's position; an operation
node dispatches through `appEvalOp` on the denotations of its subterms under the
binder-extended environment. -/
def appEval {Γ : Binding.Ctx RType} {s : RType}
    (t : Binding.Tm (rlmrOSig natAlgSig) Γ s) :
    (∀ i : Fin Γ.length, RType.interp (FreeAlg natAlgSig) (Γ.get i)) →
      RType.interp (FreeAlg natAlgSig) s :=
  PolyFix.ind (P := polyTranslate (Binding.varOver (Ty := RType)) (rlmrOSig natAlgSig).polyEndo)
    (motive := fun {x} _ =>
      (∀ i : Fin x.1.length, RType.interp (FreeAlg natAlgSig) (x.1.get i)) →
        RType.interp (FreeAlg natAlgSig) x.2)
    (fun {_x} i children ih =>
      match i, children, ih with
      | Sum.inl a, _, _ => fun ρ => (leafVar a).2 ▸ ρ (leafVar a).1
      | Sum.inr p, _, ih => fun ρ => p.2 ▸ appEvalOp p.val (fun j => ih ⟨j⟩) ρ) t

/-- `appEval` at a variable reads the environment at that variable's position,
transported along the variable's sort proof. The base case of the fold. -/
@[simp] theorem appEval_var {Γ : Binding.Ctx RType} {s : RType} (x : Binding.Var Γ s)
    (ρ : ∀ i : Fin Γ.length, RType.interp (FreeAlg natAlgSig) (Γ.get i)) :
    appEval (Binding.Tm.var x) ρ = x.2 ▸ ρ x.1 := by
  obtain ⟨i, hi⟩ := x
  subst hi
  rfl

/-- `appEval` at an operation node dispatches through `appEvalOp` on the
denotations of the node's subterms. The operation case of the fold, the
`PolyFix.ind` β-reduction that all the combinator evaluation lemmas rest on
(the analogue of `Binding.traverse_op`). -/
theorem appEval_op {Γ : Binding.Ctx RType} (o : RlmrOOp natAlgSig)
    (args : ∀ j : Fin ((rlmrOSig natAlgSig).args o).length,
      Binding.Tm (rlmrOSig natAlgSig) (Γ ++ (((rlmrOSig natAlgSig).args o).get j).1)
        (((rlmrOSig natAlgSig).args o).get j).2)
    (ρ : ∀ i : Fin Γ.length, RType.interp (FreeAlg natAlgSig) (Γ.get i)) :
    appEval (Binding.Tm.op o args) ρ = appEvalOp o (fun j => appEval (args j)) ρ := rfl

/-- Transport of `appEval` across an equality of contexts: evaluating the
context-transported term at the transported environment agrees with evaluating
the original. Discharges the `Γ ++ [] = Γ` mismatch of `app'`. -/
theorem appEval_congr_ctx {Γ Δ : Binding.Ctx RType} {s : RType} (h : Γ = Δ)
    (t : Binding.Tm (rlmrOSig natAlgSig) Γ s)
    (ρ : ∀ i : Fin Γ.length, RType.interp (FreeAlg natAlgSig) (Γ.get i)) :
    appEval (h ▸ t) (envCastCtx h ρ) = appEval t ρ := by
  subst h
  rfl

/-- `appEval` on an application node `app' f x` is the application of the
function denotation to the argument denotation (the β-reduction of the
applicative fragment). -/
@[simp] theorem appEval_app' {Γ : Binding.Ctx RType} {σ τ : RType}
    (f : Binding.Tm (rlmrOSig natAlgSig) Γ (RType.arrow σ τ))
    (x : Binding.Tm (rlmrOSig natAlgSig) Γ σ)
    (ρ : ∀ i : Fin Γ.length, RType.interp (FreeAlg natAlgSig) (Γ.get i)) :
    appEval (app' f x) ρ = appEval f ρ (appEval x ρ) :=
  congrArg₂ (fun (g : RType.interp (FreeAlg natAlgSig) (RType.arrow σ τ)) y => g y)
    (appEval_congr_ctx (List.append_nil Γ).symm f ρ)
    (appEval_congr_ctx (List.append_nil Γ).symm x ρ)

/-- `appEval` on an abstraction node `lam' b` is the semantic function extending
the environment by the bound value (the denotation of λ-abstraction). -/
@[simp] theorem appEval_lam' {Γ : Binding.Ctx RType} {σ τ : RType}
    (b : Binding.Tm (rlmrOSig natAlgSig) (Γ ++ [σ]) τ)
    (ρ : ∀ i : Fin Γ.length, RType.interp (FreeAlg natAlgSig) (Γ.get i)) :
    appEval (lam' b) ρ = fun v => appEval b (envExtend ρ v) := rfl

/-- `appEval` on a constructor constant `con θ hθ b` is the curried constructor
`stdConstructorInterp` at the object sort `θ`. -/
@[simp] theorem appEval_con {Γ : Binding.Ctx RType} {θ : RType} (hθ : θ.IsObj)
    (b : natAlgSig.B)
    (args : ∀ j : Fin ((rlmrOSig natAlgSig).args (RlmrOOp.con θ hθ b)).length,
      Binding.Tm (rlmrOSig natAlgSig)
        (Γ ++ (((rlmrOSig natAlgSig).args (RlmrOOp.con θ hθ b)).get j).1)
        (((rlmrOSig natAlgSig).args (RlmrOOp.con θ hθ b)).get j).2)
    (ρ : ∀ i : Fin Γ.length, RType.interp (FreeAlg natAlgSig) (Γ.get i)) :
    appEval (Binding.Tm.op (RlmrOOp.con θ hθ b) args) ρ
      = curryInterp natAlgSig (List.replicate (natAlgSig.ar b) θ) θ
          (stdConstructorInterp natAlgSig (⟨θ, hθ⟩, b)) := rfl

/-- `appEval` on a recurrence constant `recur τ` is the curried closed
recurrence, reading its step functions positionally and its recurrence argument
last. -/
@[simp] theorem appEval_recur {Γ : Binding.Ctx RType} {τ : RType}
    (args : ∀ j : Fin ((rlmrOSig natAlgSig).args (RlmrOOp.recur τ)).length,
      Binding.Tm (rlmrOSig natAlgSig)
        (Γ ++ (((rlmrOSig natAlgSig).args (RlmrOOp.recur τ)).get j).1)
        (((rlmrOSig natAlgSig).args (RlmrOOp.recur τ)).get j).2)
    (ρ : ∀ i : Fin Γ.length, RType.interp (FreeAlg natAlgSig) (Γ.get i)) :
    appEval (Binding.Tm.op (RlmrOOp.recur τ) args) ρ
      = curryInterp natAlgSig (stepTypes natAlgSig τ τ) (RType.arrow (RType.omega τ) τ)
          (fun stepEnv z =>
            FreeAlg.recurse (A := natAlgSig) (P := Unit)
              (fun i _ _sub phi =>
                appChain natAlgSig (List.replicate (natAlgSig.ar i) τ) τ
                  (stepAtLabel stepEnv i)
                  (childEnv [] τ (natAlgSig.ar i) finZeroElim phi))
              () z) := rfl

/-- `appEval` on a destructor constant `dstr j` is the destructor `dstrRead`. -/
@[simp] theorem appEval_dstr {Γ : Binding.Ctx RType} (j : Fin natAlgSig.maxArity)
    (args : ∀ k : Fin ((rlmrOSig natAlgSig).args (RlmrOOp.dstr j)).length,
      Binding.Tm (rlmrOSig natAlgSig)
        (Γ ++ (((rlmrOSig natAlgSig).args (RlmrOOp.dstr j)).get k).1)
        (((rlmrOSig natAlgSig).args (RlmrOOp.dstr j)).get k).2)
    (ρ : ∀ i : Fin Γ.length, RType.interp (FreeAlg natAlgSig) (Γ.get i)) :
    appEval (Binding.Tm.op (RlmrOOp.dstr j) args) ρ = dstrRead j.val := rfl

/-- `appEval` on a case constant `case θ hθ` is the branch selector `caseSelect`,
curried over its branches; over `natAlgSig` (`numCtors = 2`) it reads exactly the
two branches at enumeration positions `0` and `1`. -/
@[simp] theorem appEval_case {Γ : Binding.Ctx RType} {θ : RType} (hθ : θ.IsObj)
    (args : ∀ j : Fin ((rlmrOSig natAlgSig).args (RlmrOOp.case θ hθ)).length,
      Binding.Tm (rlmrOSig natAlgSig)
        (Γ ++ (((rlmrOSig natAlgSig).args (RlmrOOp.case θ hθ)).get j).1)
        (((rlmrOSig natAlgSig).args (RlmrOOp.case θ hθ)).get j).2)
    (ρ : ∀ i : Fin Γ.length, RType.interp (FreeAlg natAlgSig) (Γ.get i)) :
    appEval (Binding.Tm.op (RlmrOOp.case θ hθ) args) ρ
      = fun z => curryInterp natAlgSig (List.replicate natAlgSig.numCtors θ) θ
          (fun branchEnv =>
            caseSelect z
              (cast (congrArg (RType.interp (FreeAlg natAlgSig))
                (by rw [List.get_eq_getElem, List.getElem_replicate]))
                (branchEnv ⟨0, (by decide : (0:Nat) < 2)⟩))
              (cast (congrArg (RType.interp (FreeAlg natAlgSig))
                (by rw [List.get_eq_getElem, List.getElem_replicate]))
                (branchEnv ⟨1, (by decide : (1:Nat) < 2)⟩))) := rfl

/-- `appEval` on an iterated application `appSpine Ts f args` is the semantic
application chain `appChain` of the function denotation to the argument
denotations. The applicative-fragment β-reduction lifted to a whole spine, by
induction on `Ts` from `appEval_app'`. -/
@[simp] theorem appEval_appSpine {Γ : Binding.Ctx RType} {result : RType} :
    (Ts : List RType) →
    (f : Binding.Tm (rlmrOSig natAlgSig) Γ (RType.curried Ts result)) →
    (args : ∀ i : Fin Ts.length, Binding.Tm (rlmrOSig natAlgSig) Γ (Ts.get i)) →
    (ρ : ∀ i : Fin Γ.length, RType.interp (FreeAlg natAlgSig) (Γ.get i)) →
    appEval (appSpine Ts f args) ρ
      = appChain natAlgSig Ts result (appEval f ρ) (fun i => appEval (args i) ρ)
  | [], _f, _args, _ρ => rfl
  | _T :: Ts', f, args, ρ => by
    rw [appSpine, appEval_appSpine Ts', appEval_app']
    rfl

/-- `appEval` on the saturated recurrence combinator `recCombinator Estep` is the
curried closed recurrence reading its step functions positionally from the
`appEval`-denoted step terms. Collapses the `appEval_recur` currying along the
step spine via `appChain_curryInterp`. -/
@[simp] theorem appEval_recCombinator {Γ : Binding.Ctx RType} {τ : RType}
    (Estep : ∀ b : natAlgSig.B,
      Binding.Tm (rlmrOSig natAlgSig) Γ (RType.curried (List.replicate (natAlgSig.ar b) τ) τ))
    (ρ : ∀ i : Fin Γ.length, RType.interp (FreeAlg natAlgSig) (Γ.get i)) :
    appEval (recCombinator Estep) ρ
      = fun z => FreeAlg.recurse (A := natAlgSig) (P := Unit)
          (fun i _ _sub phi =>
            appChain natAlgSig (List.replicate (natAlgSig.ar i) τ) τ
              (stepAtLabel (fun idx => appEval (stepEnvOfFun Estep idx) ρ) i)
              (childEnv [] τ (natAlgSig.ar i) finZeroElim phi))
          () z := by
  rw [recCombinator, appEval_appSpine]
  exact appChain_curryInterp natAlgSig (stepTypes natAlgSig τ τ)
    (RType.arrow (RType.omega τ) τ) _ (fun i => appEval (stepEnvOfFun Estep i) ρ)

/-- The semantic renaming environment of a thinning `θ : Thinning Γ Δ`: pull a
`Δ`-indexed environment back to a `Γ`-indexed one by reading each `Γ`-position
through `θ`, transported along `θ`'s sort proof. The standard-model counterpart
of `renEnv` (`GebLean/Binding/Renaming.lean`); it reconciles the syntactic
renaming `Binding.ren θ` with `appEval` in `appEval_ren` (Leivant III §4.1). -/
def renEnvSem {Γ Δ : Binding.Ctx RType} (θ : Binding.Thinning Γ Δ)
    (ρ : ∀ i : Fin Δ.length, RType.interp (FreeAlg natAlgSig) (Δ.get i)) :
    ∀ i : Fin Γ.length, RType.interp (FreeAlg natAlgSig) (Γ.get i) :=
  fun i => (θ.app ⟨i, rfl⟩).2 ▸ ρ (θ.app ⟨i, rfl⟩).1

/-- The parallel append of `θ` acts on a suffix-embedded prefix variable
`Thinning.weakAppend.app v` by renaming `v` under `θ` and re-embedding the result
into the suffix-extended target. The `Binding.Var`-level computation rule that
`renEnvSem_appendId_childEnv` uses at prefix positions. -/
theorem appendId_app_weakAppend {Γ Δ Ξ : Binding.Ctx RType} {s : RType}
    (θ : Binding.Thinning Γ Δ) (v : Binding.Var Γ s) :
    (Binding.Thinning.appendId θ Ξ).app (Binding.Thinning.weakAppend.app v)
      = Binding.Thinning.weakAppend.app (θ.app v) := by
  rw [Binding.Thinning.appendId_app]
  exact Binding.Var.appendCases_weakAppend _ Γ _ v

/-- The parallel append of `θ` acts on a suffix inclusion `Var.appendRight Γ y`
by re-including `y` past the renamed prefix `Δ`. The `Binding.Var`-level
computation rule that `renEnvSem_appendId_childEnv` uses at suffix positions. -/
theorem appendId_app_appendRight {Γ Δ Ξ : Binding.Ctx RType} {s : RType}
    (θ : Binding.Thinning Γ Δ) (y : Binding.Var Ξ s) :
    (Binding.Thinning.appendId θ Ξ).app (Binding.Var.appendRight Γ y)
      = Binding.Var.appendRight Δ y := by
  rw [Binding.Thinning.appendId_app]
  exact Binding.Var.appendCases_appendRight _ Γ _ y

/-- The suffix embedding `Thinning.weakAppend` preserves a variable's underlying
position: embedding the prefix `Γ` into `Γ ++ Ξ` keeps every position of `Γ`
fixed. -/
theorem weakAppend_app_val : {Γ Ξ : Binding.Ctx RType} → {s : RType} →
    (v : Binding.Var Γ s) →
      ((Binding.Thinning.weakAppend (Γ := Γ) (Ξ := Ξ)).app v).1.val = v.1.val
  | [], _, _, v => v.1.elim0
  | a :: Γ', Ξ, _s, ⟨i, hi⟩ => by
      cases i using Fin.cases with
      | zero => rfl
      | succ i' =>
          have h := Binding.Thinning.weakAppend_app_succ (Γ := Γ') (Ξ := Ξ) a ⟨i', hi⟩
          rw [show (⟨i'.succ, hi⟩ : Binding.Var (a :: Γ') _)
                = Binding.Var.succ a ⟨i', hi⟩ from rfl, h]
          exact congrArg (· + 1) (weakAppend_app_val (Γ := Γ') (Ξ := Ξ) ⟨i', hi⟩)

/-- The suffix inclusion `Var.appendRight Γ` shifts a suffix variable's position
past the whole prefix `Γ`. -/
theorem appendRight_val : {Ξ : Binding.Ctx RType} → {s : RType} →
    (Γ : Binding.Ctx RType) → (y : Binding.Var Ξ s) →
      (Binding.Var.appendRight Γ y).1.val = Γ.length + y.1.val
  | _, _, [], y => (Nat.zero_add _).symm
  | _, _, a :: Γ', y => by
      rw [Binding.Var.appendRight_cons, List.length_cons]
      have hsucc : (Binding.Var.succ a (Binding.Var.appendRight Γ' y)).1.val
          = (Binding.Var.appendRight Γ' y).1.val + 1 := rfl
      rw [hsucc, appendRight_val Γ' y]
      omega

/-- The action of a thinning on a variable determines the target position from
the source position alone: two variables with the same underlying index (but
possibly distinct sort proofs) map to the same target position. -/
theorem thinning_app_fst {Γ Δ : Binding.Ctx RType} (θ : Binding.Thinning Γ Δ) :
    ∀ {s s' : RType} (x : Binding.Var Γ s) (x' : Binding.Var Γ s'),
      x.1 = x'.1 → (θ.app x).1 = (θ.app x').1 := by
  induction θ with
  | nil => intro _ _ x _ _; exact x.1.elim0
  | keep a ρ' ih =>
      intro _ _ x x' hx
      obtain ⟨i, hi⟩ := x
      obtain ⟨i', hi'⟩ := x'
      simp only at hx
      subst hx
      cases i using Fin.cases with
      | zero => rfl
      | succ i0 =>
          rw [show (⟨i0.succ, hi⟩ : Binding.Var (a :: _) _) = Binding.Var.succ a ⟨i0, hi⟩ from rfl,
            show (⟨i0.succ, hi'⟩ : Binding.Var (a :: _) _) = Binding.Var.succ a ⟨i0, hi'⟩ from rfl,
            Binding.Thinning.app_keep_of_succ, Binding.Thinning.app_keep_of_succ]
          exact congrArg Fin.succ (ih ⟨i0, hi⟩ ⟨i0, hi'⟩ rfl)
  | drop a ρ' ih =>
      intro _ _ x x' hx
      rw [Binding.Thinning.app_drop, Binding.Thinning.app_drop]
      exact congrArg Fin.succ (ih x x' hx)

/-- The recurrence-context environment reads its parameter value, heterogeneously,
at any position below `params.length`. The value-level companion of
`childEnv_finAppL`. -/
theorem childEnv_heq_left {C : RType → Type} {params : List RType} {σ : RType}
    {n : Nat} (xvec : ∀ i : Fin params.length, C (params.get i))
    (rest : Fin n → C σ) (k : Fin (params ++ List.replicate n σ).length)
    (h : k.val < params.length) :
    childEnv params σ n xvec rest k ≍ xvec ⟨k.val, h⟩ := by
  unfold childEnv
  rw [dif_pos h]
  exact cast_heq _ _

/-- The recurrence-context environment reads its appended value, heterogeneously,
at any position at or beyond `params.length`. The value-level companion of
`childEnv_finAppR`. -/
theorem childEnv_heq_right {C : RType → Type} {params : List RType} {σ : RType}
    {n : Nat} (xvec : ∀ i : Fin params.length, C (params.get i))
    (rest : Fin n → C σ) (k : Fin (params ++ List.replicate n σ).length)
    (h : ¬ k.val < params.length) (hb : k.val - params.length < n) :
    childEnv params σ n xvec rest k ≍ rest ⟨k.val - params.length, hb⟩ := by
  unfold childEnv
  rw [dif_neg h]
  exact cast_heq _ _

/-- The tautological variable at a left-injected position is the prefix
embedding of the tautological variable at the source position. Bridges the
`finAppL` split of `childEnv` to the `Var.appendCases` split of
`Thinning.appendId_app`. -/
theorem taut_finAppL_eq {Γ Ξ : Binding.Ctx RType} (i : Fin Γ.length) :
    (⟨finAppL Γ Ξ i, rfl⟩ : Binding.Var (Γ ++ Ξ) ((Γ ++ Ξ).get (finAppL Γ Ξ i)))
      = Binding.Thinning.weakAppend.app ⟨i, (get_finAppL Γ Ξ i).symm⟩ :=
  Subtype.ext (Fin.ext (by rw [weakAppend_app_val]; rfl))

/-- The tautological variable at a right-injected position is the suffix
inclusion of the tautological variable at the suffix position. Bridges the
`finAppR` split of `childEnv` to the `Var.appendCases` split of
`Thinning.appendId_app`. -/
theorem taut_finAppR_eq {Γ Ξ : Binding.Ctx RType} (j : Fin Ξ.length) :
    (⟨finAppR Γ Ξ j, rfl⟩ : Binding.Var (Γ ++ Ξ) ((Γ ++ Ξ).get (finAppR Γ Ξ j)))
      = Binding.Var.appendRight Γ ⟨j, (get_finAppR Γ Ξ j).symm⟩ :=
  Subtype.ext (Fin.ext (by rw [appendRight_val]; rfl))

/-- The semantic renaming environment of the parallel append `θ.appendId Ξ`
acting on a recurrence-context gluing `childEnv Δ σ n ρ rest` equals the gluing
of the pulled-back parameter environment `renEnvSem θ ρ` with the same suffix
values `rest`. The environment-level naturality reconciling `Binding.ren`'s
`Env.underBinder` with `appEval`'s binder-extended environments (the crux of
`appEval_ren` at the `app`/`lam` operation nodes; `Ξ = List.replicate n σ`). -/
theorem renEnvSem_appendId_childEnv {Γ Δ : Binding.Ctx RType} {σ : RType} {n : Nat}
    (θ : Binding.Thinning Γ Δ)
    (ρ : ∀ i : Fin Δ.length, RType.interp (FreeAlg natAlgSig) (Δ.get i))
    (rest : Fin n → RType.interp (FreeAlg natAlgSig) σ) :
    renEnvSem (Binding.Thinning.appendId θ (List.replicate n σ)) (childEnv Δ σ n ρ rest)
      = childEnv Γ σ n (renEnvSem θ ρ) rest := by
  funext k
  refine finApp_cases (Γ := Γ) (Δ := List.replicate n σ)
    (motive := fun k =>
      renEnvSem (Binding.Thinning.appendId θ (List.replicate n σ)) (childEnv Δ σ n ρ rest) k
        = childEnv Γ σ n (renEnvSem θ ρ) rest k)
    (fun i => ?_) (fun j => ?_) k
  · apply eq_of_heq
    have hfin : (finAppL Γ (List.replicate n σ) i).val < Γ.length := i.isLt
    have hvar : (Binding.Thinning.appendId θ (List.replicate n σ)).app
          ⟨finAppL Γ (List.replicate n σ) i, rfl⟩
        = (Binding.Thinning.weakAppend (Ξ := List.replicate n σ)).app
            (θ.app ⟨i, (get_finAppL Γ (List.replicate n σ) i).symm⟩) := by
      rw [taut_finAppL_eq]; exact appendId_app_weakAppend θ _
    have hVval : ((Binding.Thinning.appendId θ (List.replicate n σ)).app
          ⟨finAppL Γ (List.replicate n σ) i, rfl⟩).1.val
        = (θ.app ⟨i, rfl⟩).1.val := by
      rw [congrArg (fun v => v.1.val) hvar, weakAppend_app_val]
      exact congrArg Fin.val (thinning_app_fst θ _ _ rfl)
    have hlt' : ((Binding.Thinning.appendId θ (List.replicate n σ)).app
          ⟨finAppL Γ (List.replicate n σ) i, rfl⟩).1.val < Δ.length := by
      rw [hVval]; exact (θ.app _).1.isLt
    have hLHS : renEnvSem (Binding.Thinning.appendId θ (List.replicate n σ))
        (childEnv Δ σ n ρ rest) (finAppL Γ (List.replicate n σ) i)
          ≍ renEnvSem θ ρ i := by
      have hpos : (⟨((Binding.Thinning.appendId θ (List.replicate n σ)).app
            ⟨finAppL Γ (List.replicate n σ) i, rfl⟩).1.val, hlt'⟩ : Fin Δ.length)
          = (θ.app ⟨i, rfl⟩).1 := Fin.ext hVval
      simp only [renEnvSem]
      refine (eqRec_heq _ _).trans ((childEnv_heq_left ρ rest _ hlt').trans ?_)
      refine HEq.trans ?_ (eqRec_heq _ _).symm
      exact hpos ▸ HEq.rfl
    have hRHS : childEnv Γ σ n (renEnvSem θ ρ) rest (finAppL Γ (List.replicate n σ) i)
        ≍ renEnvSem θ ρ i :=
      (childEnv_heq_left (renEnvSem θ ρ) rest _ hfin).trans (heq_of_eq rfl)
    exact hLHS.trans hRHS.symm
  · apply eq_of_heq
    have hj : j.val < n := lt_of_lt_of_eq j.isLt List.length_replicate
    have hvalR : (finAppR Γ (List.replicate n σ) j).val = Γ.length + j.val := rfl
    have hgeR : ¬ (finAppR Γ (List.replicate n σ) j).val < Γ.length := by
      rw [hvalR]; omega
    have hbR : (finAppR Γ (List.replicate n σ) j).val - Γ.length < n := by
      rw [hvalR]; omega
    have hvar : (Binding.Thinning.appendId θ (List.replicate n σ)).app
          ⟨finAppR Γ (List.replicate n σ) j, rfl⟩
        = Binding.Var.appendRight Δ ⟨j, (get_finAppR Γ (List.replicate n σ) j).symm⟩ := by
      rw [taut_finAppR_eq]; exact appendId_app_appendRight θ _
    have hVval : ((Binding.Thinning.appendId θ (List.replicate n σ)).app
          ⟨finAppR Γ (List.replicate n σ) j, rfl⟩).1.val = Δ.length + j.val := by
      rw [congrArg (fun v => v.1.val) hvar, appendRight_val]
    have hgeL : ¬ ((Binding.Thinning.appendId θ (List.replicate n σ)).app
          ⟨finAppR Γ (List.replicate n σ) j, rfl⟩).1.val < Δ.length := by
      rw [hVval]; omega
    have hbL : ((Binding.Thinning.appendId θ (List.replicate n σ)).app
          ⟨finAppR Γ (List.replicate n σ) j, rfl⟩).1.val - Δ.length < n := by
      rw [hVval]; omega
    have hLHS : renEnvSem (Binding.Thinning.appendId θ (List.replicate n σ))
        (childEnv Δ σ n ρ rest) (finAppR Γ (List.replicate n σ) j)
          ≍ rest ⟨j.val, hj⟩ := by
      have hvaleqL : ((Binding.Thinning.appendId θ (List.replicate n σ)).app
            ⟨finAppR Γ (List.replicate n σ) j, rfl⟩).1.val - Δ.length = j.val := by
        rw [hVval]; omega
      have hposL : (⟨((Binding.Thinning.appendId θ (List.replicate n σ)).app
            ⟨finAppR Γ (List.replicate n σ) j, rfl⟩).1.val - Δ.length, hbL⟩ : Fin n)
          = ⟨j.val, hj⟩ := Fin.ext hvaleqL
      simp only [renEnvSem]
      refine (eqRec_heq _ _).trans ((childEnv_heq_right ρ rest _ hgeL hbL).trans ?_)
      exact heq_of_eq (congrArg rest hposL)
    have hvaleqR : (finAppR Γ (List.replicate n σ) j).val - Γ.length = j.val := by
      rw [hvalR]; omega
    have hposR : (⟨(finAppR Γ (List.replicate n σ) j).val - Γ.length, hbR⟩ : Fin n)
        = ⟨j.val, hj⟩ := Fin.ext hvaleqR
    have hRHS : childEnv Γ σ n (renEnvSem θ ρ) rest (finAppR Γ (List.replicate n σ) j)
        ≍ rest ⟨j.val, hj⟩ :=
      (childEnv_heq_right (renEnvSem θ ρ) rest _ hgeR hbR).trans
        (heq_of_eq (congrArg rest hposR))
    exact hLHS.trans hRHS.symm

/-- Reading a context-transported environment at a position below the source
length recovers the source value, heterogeneously. -/
theorem envCastCtx_apply_heq {Γ Δ : Binding.Ctx RType} (h : Γ = Δ)
    (ρ : ∀ i : Fin Γ.length, RType.interp (FreeAlg natAlgSig) (Γ.get i))
    (k : Fin Δ.length) (hk : k.val < Γ.length) :
    envCastCtx h ρ k ≍ ρ ⟨k.val, hk⟩ := by
  subst h
  exact HEq.rfl

/-- The context transport across `Δ ++ [] = Δ` is the empty-suffix recurrence
gluing: the environment `childEnv Δ σ 0` with no appended values. -/
theorem envCastCtx_eq_childEnv_zero {Δ : Binding.Ctx RType} (σ : RType)
    (ρ : ∀ i : Fin Δ.length, RType.interp (FreeAlg natAlgSig) (Δ.get i)) :
    envCastCtx (List.append_nil Δ).symm ρ = childEnv Δ σ 0 ρ finZeroElim := by
  funext k
  have hlt : k.val < Δ.length :=
    lt_of_lt_of_eq k.isLt (congrArg List.length (List.append_nil Δ))
  exact eq_of_heq ((envCastCtx_apply_heq _ ρ k hlt).trans
    (childEnv_heq_left ρ finZeroElim k hlt).symm)

/-- The `app`-node environment reconciliation (empty binder suffix): the semantic
renaming of the `Γ ++ [] = Γ` transport of `ρ` equals the transport of the
renamed `ρ`. The `app` arm of `appEvalOp_renEnvSem`. -/
theorem renEnvSem_appendId_nil {Γ Δ : Binding.Ctx RType} (θ : Binding.Thinning Γ Δ)
    (ρ : ∀ i : Fin Δ.length, RType.interp (FreeAlg natAlgSig) (Δ.get i)) :
    renEnvSem (Binding.Thinning.appendId θ []) (envCastCtx (List.append_nil Δ).symm ρ)
      = envCastCtx (List.append_nil Γ).symm (renEnvSem θ ρ) := by
  rw [envCastCtx_eq_childEnv_zero RType.o, envCastCtx_eq_childEnv_zero RType.o]
  exact renEnvSem_appendId_childEnv θ ρ finZeroElim

/-- The `lam`-node environment reconciliation (singleton binder suffix): the
semantic renaming of the binder-extended `ρ` equals the extension of the renamed
`ρ`. The `lam` arm of `appEvalOp_renEnvSem`. -/
theorem renEnvSem_appendId_extend {Γ Δ : Binding.Ctx RType} {σ : RType}
    (θ : Binding.Thinning Γ Δ)
    (ρ : ∀ i : Fin Δ.length, RType.interp (FreeAlg natAlgSig) (Δ.get i))
    (v : RType.interp (FreeAlg natAlgSig) σ) :
    renEnvSem (Binding.Thinning.appendId θ [σ]) (envExtend ρ v)
      = envExtend (renEnvSem θ ρ) v :=
  renEnvSem_appendId_childEnv (n := 1) θ ρ (fun _ => v)

/-- Per-operation naturality of `appEvalOp` under semantic renaming: evaluating a
node over the target context `Δ` on the binder-weakened, pulled-back subterm
denotations equals evaluating over the source context `Γ` on the subterm
denotations at the pulled-back environment. The `app` and `lam` arms use the two
environment reconciliations; the nullary constants ignore both the subterm family
and the environment. The operation case of `appEval_ren` (Leivant III §4.1). -/
theorem appEvalOp_renEnvSem {Γ Δ : Binding.Ctx RType} (o : RlmrOOp natAlgSig)
    (θ : Binding.Thinning Γ Δ)
    (g : ∀ j : Fin ((rlmrOSig natAlgSig).args o).length,
      (∀ i : Fin (Γ ++ (((rlmrOSig natAlgSig).args o).get j).1).length,
        RType.interp (FreeAlg natAlgSig)
          ((Γ ++ (((rlmrOSig natAlgSig).args o).get j).1).get i)) →
        RType.interp (FreeAlg natAlgSig) (((rlmrOSig natAlgSig).args o).get j).2)
    (ρ : ∀ i : Fin Δ.length, RType.interp (FreeAlg natAlgSig) (Δ.get i)) :
    appEvalOp (Γ := Δ) o
        (fun j ρ'' => g j (renEnvSem
          (Binding.Thinning.appendId θ (((rlmrOSig natAlgSig).args o).get j).1) ρ'')) ρ
      = appEvalOp (Γ := Γ) o g (renEnvSem θ ρ) := by
  cases o with
  | app σ τ =>
      simp only [appEvalOp]
      have h0 : renEnvSem (Binding.Thinning.appendId θ
            (((rlmrOSig natAlgSig).args (RlmrOOp.app σ τ)).get ⟨0, Nat.zero_lt_two⟩).1)
          (envCastCtx (List.append_nil Δ).symm ρ)
            = envCastCtx (List.append_nil Γ).symm (renEnvSem θ ρ) := renEnvSem_appendId_nil θ ρ
      have h1 : renEnvSem (Binding.Thinning.appendId θ
            (((rlmrOSig natAlgSig).args (RlmrOOp.app σ τ)).get ⟨1, Nat.one_lt_two⟩).1)
          (envCastCtx (List.append_nil Δ).symm ρ)
            = envCastCtx (List.append_nil Γ).symm (renEnvSem θ ρ) := renEnvSem_appendId_nil θ ρ
      rw [h0, h1]
      rfl
  | lam σ τ =>
      simp only [appEvalOp]
      funext v
      have h : renEnvSem (Binding.Thinning.appendId θ
            (((rlmrOSig natAlgSig).args (RlmrOOp.lam σ τ)).get ⟨0, Nat.zero_lt_one⟩).1)
          (envExtend ρ v) = envExtend (renEnvSem θ ρ) v := renEnvSem_appendId_extend θ ρ v
      rw [h]
      rfl
  | con θ' hθ b => rfl
  | recur τ => rfl
  | dstr j => rfl
  | case θ' hθ => rfl

/-- Renaming fusion at a variable leaf: evaluating a renamed variable reads the
thinning through `renEnvSem`. Factored with a free sort variable so the sort
proof can be discharged by substitution. -/
theorem appEval_ren_var {Γ Δ : Binding.Ctx RType} {s : RType} (θ : Binding.Thinning Γ Δ)
    (x : Binding.Var Γ s)
    (ρ : ∀ i : Fin Δ.length, RType.interp (FreeAlg natAlgSig) (Δ.get i)) :
    appEval (Binding.ren θ (Binding.Tm.var x)) ρ
      = appEval (Binding.Tm.var x) (renEnvSem θ ρ) := by
  rw [Binding.ren, Binding.traverse_var]
  simp only [Binding.varKit, Binding.renEnv]
  rw [appEval_var, appEval_var]
  obtain ⟨pos, hsort⟩ := x
  subst hsort
  simp only [renEnvSem]

/-- Renaming fusion for `appEval` (Leivant III §4.1): evaluating a renamed term
at an environment equals evaluating the original at the semantically renamed
environment. The base case reads the thinning through `renEnvSem`; the operation
case is `appEvalOp_renEnvSem` on the binder-weakened subterm denotations. Stated
over an arbitrary index so the induction on the term goes through. -/
@[simp] theorem appEval_ren : ∀ {y : Binding.Ctx RType × RType}
    (t : PolyFix (polyTranslate (Binding.varOver (Ty := RType)) (rlmrOSig natAlgSig).polyEndo) y)
    {Δ : Binding.Ctx RType} (θ : Binding.Thinning y.1 Δ)
    (ρ : ∀ i : Fin Δ.length, RType.interp (FreeAlg natAlgSig) (Δ.get i)),
    appEval (Binding.ren θ t) ρ = appEval t (renEnvSem θ ρ) := by
  intro y t
  induction t with
  | mk y idx children ih =>
    intro Δ θ ρ
    cases idx with
    | inl a =>
      rw [show (PolyFix.mk y (Sum.inl a) children : Binding.Tm (rlmrOSig natAlgSig) y.1 y.2)
            = Binding.Tm.var (leafVar a) from by
              obtain ⟨⟨Γ', i'⟩, rfl⟩ := a
              congr 1
              funext e
              exact e.elim]
      exact appEval_ren_var θ (leafVar a) ρ
    | inr p =>
      obtain ⟨Γ', s'⟩ := y
      change { o : (rlmrOSig natAlgSig).Op // (rlmrOSig natAlgSig).result o = s' } at p
      revert children ih
      obtain ⟨o, rfl⟩ := p
      intro children ih
      rw [show (PolyFix.mk (Γ', (rlmrOSig natAlgSig).result o) (Sum.inr ⟨o, rfl⟩) children
            : Binding.Tm (rlmrOSig natAlgSig) Γ' ((rlmrOSig natAlgSig).result o))
            = Binding.Tm.op o (fun j => children ⟨j⟩) from rfl]
      rw [Binding.ren, Binding.traverse_op]
      simp only [Binding.underBinder_renEnv]
      rw [appEval_op, appEval_op]
      have hfam : (fun j => appEval (Binding.traverse (Binding.varKit (rlmrOSig natAlgSig))
            (Binding.renEnv (Binding.Thinning.appendId θ
              (((rlmrOSig natAlgSig).args o).get j).1)) (children ⟨j⟩)))
          = (fun (j : Fin ((rlmrOSig natAlgSig).args o).length) ρ'' =>
              appEval (children ⟨j⟩) (renEnvSem (Binding.Thinning.appendId θ
                (((rlmrOSig natAlgSig).args o).get j).1) ρ'')) := by
        funext j ρ''
        exact ih ⟨j⟩ (Binding.Thinning.appendId θ _) ρ''
      rw [hfam]
      exact appEvalOp_renEnvSem o θ (fun j => appEval (children ⟨j⟩)) ρ

/-- Heterogeneous congruence for `appEval`: evaluating heterogeneously equal terms
gives heterogeneously equal denotations. -/
theorem appEval_heq {Γ : Binding.Ctx RType} {s₁ s₂ : RType}
    (t₁ : Binding.Tm (rlmrOSig natAlgSig) Γ s₁) (t₂ : Binding.Tm (rlmrOSig natAlgSig) Γ s₂)
    (ρ : ∀ i : Fin Γ.length, RType.interp (FreeAlg natAlgSig) (Γ.get i))
    (hs : s₁ = s₂) (h : t₁ ≍ t₂) : appEval t₁ ρ ≍ appEval t₂ ρ := by
  subst hs
  cases h
  exact HEq.rfl

/-- Positional read-out inverts the per-constructor step tuple: reading the
recursor's step for label `i` off the `appEval`-denoted positional tuple built
from `Estep` recovers `appEval (Estep i)`. Inverts `stepEnvOfFun` through
`ctorList_get_ctorIdx`. The step-tuple inversion of the `mrec` agreement proof. -/
theorem stepAtLabel_stepEnvOfFun {Γ : Binding.Ctx RType} {τ : RType}
    (Estep : ∀ b : natAlgSig.B,
      Binding.Tm (rlmrOSig natAlgSig) Γ (RType.curried (List.replicate (natAlgSig.ar b) τ) τ))
    (ρ : ∀ i : Fin Γ.length, RType.interp (FreeAlg natAlgSig) (Γ.get i))
    (i : natAlgSig.B) :
    stepAtLabel (fun idx => appEval (stepEnvOfFun Estep idx) ρ) i = appEval (Estep i) ρ := by
  apply eq_of_heq
  unfold stepAtLabel
  refine (cast_heq _ _).trans ?_
  refine appEval_heq _ _ ρ ?_ ?_
  · simp only [stepTypes, List.get_eq_getElem, List.getElem_map]
    exact congrArg (fun c => RType.curried (List.replicate (natAlgSig.ar c) τ) τ)
      (ctorList_get_ctorIdx i)
  · unfold stepEnvOfFun
    simp only [id_eq, eq_mpr_eq_cast]
    refine ((cast_heq _ _).trans (cast_heq _ _)).trans ?_
    have hEstep : ∀ {b b' : natAlgSig.B}, b = b' → Estep b ≍ Estep b' := by
      intro b b' h; cases h; exact HEq.rfl
    exact hEstep (by rw [← List.get_eq_getElem]; exact ctorList_get_ctorIdx i)

/-- The semantic environment over a concatenated context `Γ ++ Δ`, gluing an
environment `ρ` for the prefix with an environment `cv` for the suffix: below
`Γ.length` it reads `ρ`, otherwise `cv`. The semantic counterpart of `joinTuple`
(`GebLean/Ramified/SynCat.lean`) and the arbitrary-suffix generalization of
`childEnv` (whose suffix is `List.replicate n σ`); the join threaded through
`lamSpine`'s abstraction in `appEval_lamSpine` (Leivant III §4.1). -/
def joinEnv {Γ Δ : Binding.Ctx RType}
    (ρ : ∀ i : Fin Γ.length, RType.interp (FreeAlg natAlgSig) (Γ.get i))
    (cv : ∀ j : Fin Δ.length, RType.interp (FreeAlg natAlgSig) (Δ.get j)) :
    ∀ k : Fin (Γ ++ Δ).length, RType.interp (FreeAlg natAlgSig) ((Γ ++ Δ).get k) :=
  fun k =>
    if h : k.val < Γ.length then
      cast (congrArg (RType.interp (FreeAlg natAlgSig)) (get_append_lt Γ Δ k h).symm)
        (ρ ⟨k.val, h⟩)
    else
      cast (congrArg (RType.interp (FreeAlg natAlgSig)) (get_append_ge Γ Δ k h).symm)
        (cv ⟨k.val - Γ.length, by
          have hk : k.val < Γ.length + Δ.length :=
            Nat.lt_of_lt_of_eq k.isLt List.length_append
          omega⟩)

/-- `joinEnv` reads its prefix environment, heterogeneously, at any position below
`Γ.length`. -/
theorem joinEnv_heq_left {Γ Δ : Binding.Ctx RType}
    (ρ : ∀ i : Fin Γ.length, RType.interp (FreeAlg natAlgSig) (Γ.get i))
    (cv : ∀ j : Fin Δ.length, RType.interp (FreeAlg natAlgSig) (Δ.get j))
    (k : Fin (Γ ++ Δ).length) (h : k.val < Γ.length) :
    joinEnv ρ cv k ≍ ρ ⟨k.val, h⟩ := by
  unfold joinEnv
  rw [dif_pos h]
  exact cast_heq _ _

/-- `joinEnv` reads its suffix environment, heterogeneously, at any position at or
beyond `Γ.length`. -/
theorem joinEnv_heq_right {Γ Δ : Binding.Ctx RType}
    (ρ : ∀ i : Fin Γ.length, RType.interp (FreeAlg natAlgSig) (Γ.get i))
    (cv : ∀ j : Fin Δ.length, RType.interp (FreeAlg natAlgSig) (Δ.get j))
    (k : Fin (Γ ++ Δ).length) (h : ¬ k.val < Γ.length)
    (hb : k.val - Γ.length < Δ.length) :
    joinEnv ρ cv k ≍ cv ⟨k.val - Γ.length, hb⟩ := by
  unfold joinEnv
  rw [dif_neg h]
  exact cast_heq _ _

/-- Peeling one binder off a `joinEnv`: transporting the join of a
one-value-extended prefix `envExtend ρ v` with a suffix `cv` back across the
append reassociation equals the join of `ρ` with the cons `Fin.cons v cv`. The
environment reconciliation the step case of `appEval_lamSpine` needs, matching
`lamSpine`'s `List.append_assoc` reassociation cast. -/
theorem joinEnv_envExtend {Γ : Binding.Ctx RType} {σ : RType} {Δ' : List RType}
    (ρ : ∀ i : Fin Γ.length, RType.interp (FreeAlg natAlgSig) (Γ.get i))
    (v : RType.interp (FreeAlg natAlgSig) σ)
    (cv : ∀ j : Fin Δ'.length, RType.interp (FreeAlg natAlgSig) (Δ'.get j)) :
    envCastCtx (List.append_assoc Γ [σ] Δ')
        (joinEnv (Γ := Γ ++ [σ]) (Δ := Δ') (envExtend ρ v) cv)
      = joinEnv (Γ := Γ) (Δ := σ :: Δ') ρ (Fin.cons v cv) := by
  funext k
  apply eq_of_heq
  have hσL : (Γ ++ [σ]).length = Γ.length + 1 := by simp
  have hkub : k.val < Γ.length + 1 + Δ'.length := by
    have hk := k.isLt
    simp only [List.length_append, List.length_cons, List.length_nil] at hk
    omega
  have hklen : k.val < ((Γ ++ [σ]) ++ Δ').length := by
    simp only [List.length_append, List.length_singleton]; omega
  have keyZero : ∀ (i : Fin (Δ'.length + 1)), i.val = 0 →
      @Fin.cons Δ'.length (fun j => RType.interp (FreeAlg natAlgSig) ((σ :: Δ').get j))
        v cv i ≍ v := by
    intro i hi
    rw [show i = 0 from Fin.ext hi]
    exact heq_of_eq (Fin.cons_zero
      (α := fun j => RType.interp (FreeAlg natAlgSig) ((σ :: Δ').get j)) v cv)
  have keySucc : ∀ (i : Fin (Δ'.length + 1)) (m : Fin Δ'.length),
      i.val = m.val + 1 →
      @Fin.cons Δ'.length (fun j => RType.interp (FreeAlg natAlgSig) ((σ :: Δ').get j))
        v cv i ≍ cv m := by
    intro i m hi
    rw [show i = m.succ from Fin.ext (by rw [Fin.val_succ]; exact hi)]
    exact heq_of_eq (Fin.cons_succ
      (α := fun j => RType.interp (FreeAlg natAlgSig) ((σ :: Δ').get j)) v cv m)
  refine (envCastCtx_apply_heq (List.append_assoc Γ [σ] Δ')
    (joinEnv (envExtend ρ v) cv) k hklen).trans ?_
  by_cases h1 : k.val < Γ.length
  · have hkσ : k.val < (Γ ++ [σ]).length := by omega
    refine (joinEnv_heq_left (envExtend ρ v) cv ⟨k.val, hklen⟩ hkσ).trans ?_
    refine (childEnv_heq_left (n := 1) ρ (fun _ => v) ⟨k.val, hkσ⟩ h1).trans ?_
    exact (joinEnv_heq_left ρ (Fin.cons v cv) k h1).symm
  · by_cases h2 : k.val < Γ.length + 1
    · have hkeq : k.val = Γ.length := by omega
      have hkσ : k.val < (Γ ++ [σ]).length := by omega
      have hnl : ¬ (⟨k.val, hkσ⟩ : Fin (Γ ++ [σ]).length).val < Γ.length := by
        simp only; omega
      have hb1 : (⟨k.val, hkσ⟩ : Fin (Γ ++ [σ]).length).val - Γ.length < 1 := by
        simp only; omega
      have hb2 : k.val - Γ.length < (σ :: Δ').length := by
        rw [List.length_cons]; omega
      have hib : k.val - Γ.length < Δ'.length + 1 := by simpa using hb2
      refine (joinEnv_heq_left (envExtend ρ v) cv ⟨k.val, hklen⟩ hkσ).trans ?_
      refine (childEnv_heq_right (n := 1) ρ (fun _ => v) ⟨k.val, hkσ⟩ hnl hb1).trans ?_
      refine HEq.trans ?_ (joinEnv_heq_right ρ (Fin.cons v cv) k h1 hb2).symm
      exact (keyZero ⟨k.val - Γ.length, hib⟩ (by change k.val - Γ.length = 0; omega)).symm
    · have hkσ_ge : ¬ k.val < (Γ ++ [σ]).length := by omega
      have hbσ : k.val - (Γ ++ [σ]).length < Δ'.length := by omega
      have hb2 : k.val - Γ.length < (σ :: Δ').length := by
        rw [List.length_cons]; omega
      have hib : k.val - Γ.length < Δ'.length + 1 := by simpa using hb2
      refine (joinEnv_heq_right (envExtend ρ v) cv ⟨k.val, hklen⟩ hkσ_ge hbσ).trans ?_
      refine HEq.trans ?_ (joinEnv_heq_right ρ (Fin.cons v cv) k h1 hb2).symm
      exact HEq.symm (keySucc ⟨k.val - Γ.length, hib⟩
        ⟨k.val - (Γ ++ [σ]).length, hbσ⟩
        (by change k.val - Γ.length = (k.val - (Γ ++ [σ]).length) + 1; omega))

/-- Transport of `appEval` across a context equality presented as an explicit
`cast` on the context slot (`lamSpine`'s reassociation form of the transport):
evaluating the cast term equals evaluating the original at the inversely
transported environment. The `cast`-shaped companion of `appEval_congr_ctx`. -/
theorem appEval_cast_ctx {Γ Δ : Binding.Ctx RType} {s : RType} (h : Γ = Δ)
    (t : Binding.Tm (rlmrOSig natAlgSig) Γ s)
    (ρ : ∀ i : Fin Δ.length, RType.interp (FreeAlg natAlgSig) (Δ.get i)) :
    appEval (cast (congrArg (fun c => Binding.Tm (rlmrOSig natAlgSig) c s) h) t) ρ
      = appEval t (envCastCtx h.symm ρ) := by
  subst h
  rfl

/-- Renaming fusion evaluates the applicative λ-spine (Leivant III §4.1): the
denotation of `lamSpine Δ body` at `ρ` is the currying of the denotation of
`body` at the join of `ρ` with the abstracted arguments. Proved by induction on
`Δ` from `appEval_lam'`, threading `lamSpine`'s `List.append_assoc` reassociation
via `joinEnv_envExtend`. -/
theorem appEval_lamSpine : (Γ : Binding.Ctx RType) → (Δ : List RType) → {τ : RType} →
    (body : Binding.Tm (rlmrOSig natAlgSig) (Γ ++ Δ) τ) →
    (ρ : ∀ i : Fin Γ.length, RType.interp (FreeAlg natAlgSig) (Γ.get i)) →
    appEval (lamSpine Δ body) ρ
      = curryInterp natAlgSig Δ τ (fun cv => appEval body (joinEnv ρ cv))
  | Γ, [], τ, body, ρ => by
    change appEval (cast (congrArg (fun c => Binding.Tm (rlmrOSig natAlgSig) c τ)
      (List.append_nil Γ)) body) ρ = appEval body (joinEnv ρ finZeroElim)
    rw [appEval_cast_ctx (List.append_nil Γ) body ρ]
    congr 1
    funext i
    apply eq_of_heq
    have hi : i.val < Γ.length :=
      lt_of_lt_of_eq i.isLt (congrArg List.length (List.append_nil Γ))
    refine (envCastCtx_apply_heq (List.append_nil Γ).symm ρ i hi).trans ?_
    exact (joinEnv_heq_left ρ finZeroElim i hi).symm
  | Γ, σ :: Δ', τ, body, ρ => by
    change appEval (lam' (lamSpine Δ' (cast (congrArg
      (fun c => Binding.Tm (rlmrOSig natAlgSig) c τ)
      (List.append_assoc Γ [σ] Δ').symm) body))) ρ = _
    rw [appEval_lam']
    funext v
    rw [appEval_lamSpine (Γ ++ [σ]) Δ']
    change curryInterp natAlgSig Δ' τ
        (fun cv => appEval (cast (congrArg (fun c => Binding.Tm (rlmrOSig natAlgSig) c τ)
          (List.append_assoc Γ [σ] Δ').symm) body) (joinEnv (envExtend ρ v) cv))
      = curryInterp natAlgSig Δ' τ
        (fun cv => appEval body (joinEnv ρ (Fin.cons v cv)))
    congr 1
    funext cv
    rw [appEval_cast_ctx (List.append_assoc Γ [σ] Δ').symm body (joinEnv (envExtend ρ v) cv)]
    congr 1
    exact joinEnv_envExtend ρ v cv

/-- The thinning embedding the suffix `Ξ` of an append-at-end context into the
whole `Γ ++ Ξ`: drop every entry of the prefix `Γ`, then keep every entry of
`Ξ` (the identity on the suffix). The suffix-inclusion counterpart of
`Binding.Thinning.weakAppend` (which embeds the prefix), needed to weaken a
child identifier's open body — living in its own context `Ξ` — into the ambient
extension `Γ ++ Ξ` before abstracting it with `lamSpine`. -/
def suffixThinning : (Γ : Binding.Ctx RType) → {Ξ : Binding.Ctx RType} →
    Binding.Thinning Ξ (Γ ++ Ξ)
  | [], _ => Binding.Thinning.id
  | a :: Γ', _ => Binding.Thinning.drop a (suffixThinning Γ')

/-- The applicative-term model of an explicit definition's body (the direct
Proposition 7 translation, Leivant III §4.1): the body signature
`defnSig natAlgSig` interpreted into `RλMR_o^ω` terms in the ambient context `Γ`.
Mirrors `defnModel` (`GebLean/Ramified/HigherOrder.lean`) but valued in
applicative terms rather than standard-model values — the constructor operation
becomes a `con`-headed application (`appSpine`), application becomes `app'`, a
saturated hole substitutes the translated child `ih j` along the argument terms
(`Binding.sub`), and a curried hole abstracts the translated child into a
combinator value, weakening it into `Γ`'s context (`suffixThinning`) and binding
its own context with `lamSpine`. -/
def defnModelTerm {Γ : Binding.Ctx RType} (n : Nat)
    (holeIdx : Fin n → List RType × RType)
    (ih : ∀ j : Fin n, Binding.Tm (rlmrOSig natAlgSig) (holeIdx j).1 (holeIdx j).2) :
    SortedModel (defnSig natAlgSig n holeIdx) where
  carrier := fun σ => Binding.Tm (rlmrOSig natAlgSig) Γ σ
  interpOp op args :=
    match op with
    | Sum.inl (Sum.inl (Sum.inl cop)) =>
      appSpine (List.replicate (natAlgSig.ar cop.2) cop.1.val)
        (Binding.Tm.op (S := rlmrOSig natAlgSig)
          (RlmrOOp.con cop.1.val cop.1.2 cop.2) (fun k => k.elim0)) args
    | Sum.inl (Sum.inl (Sum.inr _aop)) =>
      app' (args ⟨0, Nat.zero_lt_two⟩) (args ⟨1, Nat.one_lt_two⟩)
    | Sum.inl (Sum.inr j) => Binding.sub (fun _s x => x.2 ▸ args x.1) (ih j)
    | Sum.inr j => lamSpine (holeIdx j).1 (Binding.ren (suffixThinning Γ) (ih j))

/-- The direct Proposition 7 translation of an explicit-definition identifier
(Leivant III §4.1, the soundness arm `(1)⟹(4)`): fold the defining body against
the applicative-term model `defnModelTerm`, over the identity environment
sending each context position to its own variable. The translated child
identifiers `ih` fill the body's holes. -/
def prop7DefnStep {Γ : Binding.Ctx RType} {τ : RType} (d : DefnShape natAlgSig Γ τ)
    (ih : ∀ j : Fin d.numHoles,
      Binding.Tm (rlmrOSig natAlgSig) (d.holeIdx j).1 (d.holeIdx j).2) :
    Binding.Tm (rlmrOSig natAlgSig) Γ τ :=
  d.body.eval (defnModelTerm (Γ := Γ) d.numHoles d.holeIdx ih)
    (fun i => Binding.Tm.var ⟨i, rfl⟩)

/-- The direct Proposition 7 translation of a ramified monotone-recurrence
identifier (Leivant III §4.1, eq. (9), the soundness arm `(1)⟹(4)`): the
recurrence combinator `R^τ E⃗` applied to the recurrence argument, in open form
over the context `params ++ [Ωτ]`. Each step term `E_b` is the translated child
`ih b` — living in `params ++ τ^{ar b}` with its `ar b` recursive-result
variables free — λ-abstracted over that suffix (`lamSpine`) into a step function
`params ⊢ τ^{ar b} → τ`, then weakened past the recurrence argument
(`Binding.ren Thinning.weakAppend`). The recurrence argument is the sole suffix
variable of `params ++ [Ωτ]` (`boundVar`). -/
def prop7MrecStep {τ : RType} (params : List RType)
    (ih : (i : natAlgSig.B) →
      Binding.Tm (rlmrOSig natAlgSig)
        (params ++ List.replicate (natAlgSig.ar i) τ) τ) :
    Binding.Tm (rlmrOSig natAlgSig) (params ++ [RType.omega τ]) τ :=
  app'
    (recCombinator (fun b =>
      Binding.ren Binding.Thinning.weakAppend
        (lamSpine (List.replicate (natAlgSig.ar b) τ) (ih b))))
    (Binding.Tm.var (boundVar (Γ := params) (σ := RType.omega τ)))

/-- The semantic renaming of the prefix embedding `Thinning.weakAppend` reads the
parameter prefix of a recurrence-context environment: `renEnvSem weakAppend`
agrees with `envHead`. The reconciliation of the fused renaming with the
recurrence step's parameter read (`prop7MrecStep_interp`). -/
theorem renEnvSem_weakAppend_eq_envHead {params : List RType} {ω : RType}
    (ρ : ∀ k : Fin (params ++ [ω]).length,
      RType.interp (FreeAlg natAlgSig) ((params ++ [ω]).get k)) :
    renEnvSem Binding.Thinning.weakAppend ρ = envHead params ω ρ := by
  funext i
  apply eq_of_heq
  simp only [renEnvSem, envHead]
  refine (eqRec_heq _ _).trans ?_
  refine HEq.trans ?_ (cast_heq _ _).symm
  have hpos : (Binding.Thinning.weakAppend.app
      (⟨i, rfl⟩ : Binding.Var params (params.get i))).1 = finAppL params [ω] i :=
    Fin.ext (by rw [weakAppend_app_val]; simp [finAppL])
  rw [hpos]

/-- The join of a parameter environment with the closed recurrence-result gluing
`childEnv [] σ n finZeroElim phi` equals the full recurrence-context gluing
`childEnv params σ n ρ phi`. The reconciliation of `appEval_lamSpine`'s join with
the recurrence step's `childEnv` (`prop7MrecStep_interp`). -/
theorem joinEnv_childEnv_nil {params : List RType} {σ : RType} {n : Nat}
    (ρ : ∀ i : Fin params.length, RType.interp (FreeAlg natAlgSig) (params.get i))
    (phi : Fin n → RType.interp (FreeAlg natAlgSig) σ) :
    joinEnv (Γ := params) (Δ := List.replicate n σ) ρ
        (childEnv [] σ n finZeroElim phi)
      = childEnv params σ n ρ phi := by
  funext k
  refine finApp_cases (Γ := params) (Δ := List.replicate n σ)
    (motive := fun k => joinEnv ρ (childEnv [] σ n finZeroElim phi) k
      = childEnv params σ n ρ phi k)
    (fun i => ?_) (fun j => ?_) k
  · apply eq_of_heq
    have hlt : (finAppL params (List.replicate n σ) i).val < params.length := i.isLt
    exact (joinEnv_heq_left ρ (childEnv [] σ n finZeroElim phi) _ hlt).trans
      (childEnv_heq_left ρ phi _ hlt).symm
  · apply eq_of_heq
    have hjn : j.val < n := lt_of_lt_of_eq j.isLt List.length_replicate
    have hge : ¬ (finAppR params (List.replicate n σ) j).val < params.length := by
      simp only [finAppR]; omega
    have hbn : (finAppR params (List.replicate n σ) j).val - params.length < n := by
      simp only [finAppR]; omega
    have hbΔ : (finAppR params (List.replicate n σ) j).val - params.length
        < (List.replicate n σ).length := lt_of_lt_of_eq hbn List.length_replicate.symm
    refine (joinEnv_heq_right ρ (childEnv [] σ n finZeroElim phi) _ hge hbΔ).trans ?_
    refine (childEnv_heq_right (params := []) finZeroElim phi
      ⟨_, hbΔ⟩ (Nat.not_lt_zero _) (by simpa using hbn)).trans ?_
    refine HEq.trans ?_ (childEnv_heq_right ρ phi _ hge hbn).symm
    exact heq_of_eq (congrArg phi (Fin.ext (by simp)))

/-- Evaluating the sole suffix variable `boundVar` of `params ++ [ω]` reads the
recurrence argument `envLast`. The recurrence-argument reconciliation of
`prop7MrecStep_interp`. -/
theorem boundVar_appEval_eq_envLast {params : List RType} {ω : RType}
    (ρ : ∀ k : Fin (params ++ [ω]).length,
      RType.interp (FreeAlg natAlgSig) ((params ++ [ω]).get k)) :
    appEval (Binding.Tm.var (boundVar (Γ := params) (σ := ω))) ρ = envLast params ω ρ := by
  rw [appEval_var]
  apply eq_of_heq
  refine (eqRec_heq _ _).trans ?_
  simp only [envLast]
  refine HEq.trans ?_ (cast_heq _ _).symm
  have hpos : (boundVar (Γ := params) (σ := ω)).1 = finAppR params [ω] ⟨0, by simp⟩ := by
    apply Fin.ext
    unfold boundVar
    rw [appendRight_val]
    simp [finAppR]
  rw [hpos]

/-- The monotone-recurrence step of the direct Proposition 7 translation preserves
the denoted function (Leivant III §4.1, eq. (9), the soundness arm `(1)⟹(4)`):
`appEval` of `prop7MrecStep params ihT` at a recurrence-context environment agrees
with `RIdent.interpStep`'s `mrec` arm, given that the translated children `ihT`
denote the semantic children `ihS`. Assembled from `appEval_app'`,
`appEval_recCombinator`, `stepAtLabel_stepEnvOfFun`, `appEval_ren`,
`appEval_lamSpine`, and `appChain_curryInterp`, reconciled through
`renEnvSem_weakAppend_eq_envHead`, `joinEnv_childEnv_nil`, and
`boundVar_appEval_eq_envLast`. -/
theorem prop7MrecStep_interp {τ : RType} (params : List RType)
    (ihT : (i : natAlgSig.B) →
      Binding.Tm (rlmrOSig natAlgSig) (params ++ List.replicate (natAlgSig.ar i) τ) τ)
    (ihS : (i : natAlgSig.B) →
      (∀ k : Fin (params ++ List.replicate (natAlgSig.ar i) τ).length,
        RType.interp (FreeAlg natAlgSig)
          ((params ++ List.replicate (natAlgSig.ar i) τ).get k)) →
        RType.interp (FreeAlg natAlgSig) τ)
    (hchild : ∀ (b : natAlgSig.B)
      (ρ' : ∀ k : Fin (params ++ List.replicate (natAlgSig.ar b) τ).length,
        RType.interp (FreeAlg natAlgSig)
          ((params ++ List.replicate (natAlgSig.ar b) τ).get k)),
      appEval (ihT b) ρ' = ihS b ρ')
    (ρ : ∀ k : Fin (params ++ [RType.omega τ]).length,
      RType.interp (FreeAlg natAlgSig) ((params ++ [RType.omega τ]).get k)) :
    appEval (prop7MrecStep params ihT) ρ
      = FreeAlg.recurse (A := natAlgSig) (P := Unit)
          (fun i _ _sub phi =>
            ihS i (childEnv params τ (natAlgSig.ar i)
              (envHead params (RType.omega τ) ρ) phi))
          () (envLast params (RType.omega τ) ρ) := by
  rw [prop7MrecStep, appEval_app', appEval_recCombinator]
  refine congrArg₂ (fun s a => FreeAlg.recurse (A := natAlgSig) (P := Unit) s () a) ?_
    (boundVar_appEval_eq_envLast ρ)
  funext i _u sub phi
  rw [stepAtLabel_stepEnvOfFun]
  rw [congrArg (fun A => appChain natAlgSig (List.replicate (natAlgSig.ar i) τ) τ A
      (childEnv [] τ (natAlgSig.ar i) finZeroElim phi))
    (appEval_ren (lamSpine (List.replicate (natAlgSig.ar i) τ) (ihT i))
      Binding.Thinning.weakAppend ρ)]
  rw [appEval_lamSpine params (List.replicate (natAlgSig.ar i) τ) (ihT i),
    appChain_curryInterp, hchild, renEnvSem_weakAppend_eq_envHead,
    joinEnv_childEnv_nil]

/-- `appEval` on a homogeneous application spine `replicateSpine n base head args`
is the semantic application chain of the head denotation to the argument
denotations, reindexed off `List.replicate` (Leivant III §4.1). Specializes
`appEval_appSpine` to `Ts = List.replicate n base`, discharging the
`List.getElem_replicate` sort transport on each argument via `appEval_heq`. -/
theorem appEval_replicateSpine {Γ : Binding.Ctx RType} {result : RType} (n : Nat)
    (base : RType)
    (head : Binding.Tm (rlmrOSig natAlgSig) Γ (RType.curried (List.replicate n base) result))
    (args : Fin n → Binding.Tm (rlmrOSig natAlgSig) Γ base)
    (ρ : ∀ i : Fin Γ.length, RType.interp (FreeAlg natAlgSig) (Γ.get i)) :
    appEval (replicateSpine n base head args) ρ
      = appChain natAlgSig (List.replicate n base) result (appEval head ρ)
          (fun i => cast (congrArg (RType.interp (FreeAlg natAlgSig))
            (show base = (List.replicate n base).get i from by
              rw [List.get_eq_getElem, List.getElem_replicate]))
            (appEval (args (Fin.cast List.length_replicate i)) ρ)) := by
  rw [replicateSpine, appEval_appSpine]
  congr 1
  funext i
  apply eq_of_heq
  refine (appEval_heq _ _ ρ ?_ ?_).trans (cast_heq _ _).symm
  · rw [List.get_eq_getElem, List.getElem_replicate]
  · simp only [eq_mpr_eq_cast]
    exact (cast_heq _ _).trans (cast_heq _ _)

/-- The semantic substitution environment of a term environment
`σ : Env (Tm S) Γ Δ`: read each `Γ`-position's tautological variable through
`σ` and evaluate the resulting `Δ`-term at `ρ`. The standard-model counterpart
of the substitution kit `subKit`; it reconciles the syntactic substitution
`Binding.sub σ` with `appEval` in `appEval_sub` (Leivant III §4.1). The
substitution analogue of `renEnvSem`. -/
def subEnvSem {Γ Δ : Binding.Ctx RType}
    (σ : Binding.Env (Binding.Tm (rlmrOSig natAlgSig)) Γ Δ)
    (ρ : ∀ i : Fin Δ.length, RType.interp (FreeAlg natAlgSig) (Δ.get i)) :
    ∀ i : Fin Γ.length, RType.interp (FreeAlg natAlgSig) (Γ.get i) :=
  fun i => appEval (σ (Γ.get i) ⟨i, rfl⟩) ρ

/-- Evaluating a term environment at two positions of the same underlying index
but possibly distinct sorts gives heterogeneously equal denotations: the value
`σ s ⟨i, hi⟩` depends on the position `i` alone, up to the sort transport. -/
theorem subEnvSem_val_heq {Γ Δ : Binding.Ctx RType}
    (σ : Binding.Env (Binding.Tm (rlmrOSig natAlgSig)) Γ Δ)
    {s s' : RType} (hs : s = s') (i : Fin Γ.length)
    (hi : Γ.get i = s) (hi' : Γ.get i = s') :
    σ s ⟨i, hi⟩ ≍ σ s' ⟨i, hi'⟩ := by
  subst hs
  rfl

/-- The semantic renaming of the prefix embedding `Thinning.weakAppend` reads
the prefix environment of a recurrence-context gluing `childEnv Δ σ n ρ rest`:
`renEnvSem weakAppend` recovers `ρ`. The arbitrary-suffix generalization of
`renEnvSem_weakAppend_eq_envHead`, discharging the binder-weakening step of
`subEnvSem_underBinder_childEnv` via `appEval_ren`. -/
theorem renEnvSem_weakAppend_childEnv {Δ : Binding.Ctx RType} {σ : RType} {n : Nat}
    (ρ : ∀ i : Fin Δ.length, RType.interp (FreeAlg natAlgSig) (Δ.get i))
    (rest : Fin n → RType.interp (FreeAlg natAlgSig) σ) :
    renEnvSem (Binding.Thinning.weakAppend (Ξ := List.replicate n σ))
        (childEnv Δ σ n ρ rest) = ρ := by
  funext i
  apply eq_of_heq
  simp only [renEnvSem]
  refine (eqRec_heq _ _).trans ?_
  have hpos : ((Binding.Thinning.weakAppend (Ξ := List.replicate n σ)).app
      (⟨i, rfl⟩ : Binding.Var Δ (Δ.get i))).1 = finAppL Δ (List.replicate n σ) i :=
    Fin.ext (by rw [weakAppend_app_val]; simp [finAppL])
  rw [hpos, childEnv_finAppL]
  exact cast_heq _ _

/-- The semantic substitution environment of an under-binder weakening
`Env.underBinder subKit σ` acting on a recurrence-context gluing
`childEnv Δ σ' n ρ rest` equals the gluing of the substituted prefix environment
`subEnvSem σ ρ` with the same suffix values `rest`. The substitution analogue of
`renEnvSem_appendId_childEnv` (the crux of `appEval_sub` at the `app`/`lam`
nodes): at prefix positions the binder-weakening `wk = ren weakAppend` is pushed
through `appEval` by `appEval_ren` and collapsed by `renEnvSem_weakAppend_childEnv`;
at suffix positions the freshly bound variable reads `rest` directly. -/
theorem subEnvSem_underBinder_childEnv {Γ Δ : Binding.Ctx RType} {σ' : RType} {n : Nat}
    (σ : Binding.Env (Binding.Tm (rlmrOSig natAlgSig)) Γ Δ)
    (ρ : ∀ i : Fin Δ.length, RType.interp (FreeAlg natAlgSig) (Δ.get i))
    (rest : Fin n → RType.interp (FreeAlg natAlgSig) σ') :
    subEnvSem (Binding.Env.underBinder (Binding.subKit (rlmrOSig natAlgSig))
        (Ξ := List.replicate n σ') σ) (childEnv Δ σ' n ρ rest)
      = childEnv Γ σ' n (subEnvSem σ ρ) rest := by
  funext k
  refine finApp_cases (Γ := Γ) (Δ := List.replicate n σ')
    (motive := fun k =>
      subEnvSem (Binding.Env.underBinder (Binding.subKit (rlmrOSig natAlgSig))
        (Ξ := List.replicate n σ') σ) (childEnv Δ σ' n ρ rest) k
        = childEnv Γ σ' n (subEnvSem σ ρ) rest k)
    (fun i => ?_) (fun j => ?_) k
  · apply eq_of_heq
    have hfin : (finAppL Γ (List.replicate n σ') i).val < Γ.length := i.isLt
    have hvar : Binding.Env.underBinder (Binding.subKit (rlmrOSig natAlgSig))
          (Ξ := List.replicate n σ') σ
          ((Γ ++ List.replicate n σ').get (finAppL Γ (List.replicate n σ') i))
          ⟨finAppL Γ (List.replicate n σ') i, rfl⟩
        = Binding.ren Binding.Thinning.weakAppend
            (σ ((Γ ++ List.replicate n σ').get (finAppL Γ (List.replicate n σ') i))
              ⟨i, (get_finAppL Γ (List.replicate n σ') i).symm⟩) := by
      simp only [Binding.Env.underBinder, Binding.subKit]
      rw [taut_finAppL_eq]
      exact Binding.Var.appendCases_weakAppend _ Γ _ _
    have hLHS : subEnvSem (Binding.Env.underBinder (Binding.subKit (rlmrOSig natAlgSig))
          (Ξ := List.replicate n σ') σ) (childEnv Δ σ' n ρ rest)
          (finAppL Γ (List.replicate n σ') i) ≍ subEnvSem σ ρ i := by
      simp only [subEnvSem]
      rw [hvar]
      rw [appEval_ren (σ ((Γ ++ List.replicate n σ').get (finAppL Γ (List.replicate n σ') i))
            ⟨i, (get_finAppL Γ (List.replicate n σ') i).symm⟩)
          Binding.Thinning.weakAppend (childEnv Δ σ' n ρ rest),
        renEnvSem_weakAppend_childEnv]
      exact appEval_heq _ _ ρ (get_finAppL Γ (List.replicate n σ') i)
        (subEnvSem_val_heq σ (get_finAppL Γ (List.replicate n σ') i) i _ rfl)
    have hRHS : childEnv Γ σ' n (subEnvSem σ ρ) rest (finAppL Γ (List.replicate n σ') i)
        ≍ subEnvSem σ ρ i :=
      (childEnv_heq_left (subEnvSem σ ρ) rest _ hfin).trans (heq_of_eq rfl)
    exact hLHS.trans hRHS.symm
  · apply eq_of_heq
    have hj : j.val < n := lt_of_lt_of_eq j.isLt List.length_replicate
    have hvalR : (finAppR Γ (List.replicate n σ') j).val = Γ.length + j.val := rfl
    have hgeR : ¬ (finAppR Γ (List.replicate n σ') j).val < Γ.length := by rw [hvalR]; omega
    have hbR : (finAppR Γ (List.replicate n σ') j).val - Γ.length < n := by rw [hvalR]; omega
    have hvar : Binding.Env.underBinder (Binding.subKit (rlmrOSig natAlgSig))
          (Ξ := List.replicate n σ') σ
          ((Γ ++ List.replicate n σ').get (finAppR Γ (List.replicate n σ') j))
          ⟨finAppR Γ (List.replicate n σ') j, rfl⟩
        = Binding.Tm.var (Binding.Var.appendRight Δ
            ⟨j, (get_finAppR Γ (List.replicate n σ') j).symm⟩) := by
      simp only [Binding.Env.underBinder, Binding.subKit]
      rw [taut_finAppR_eq]
      exact Binding.Var.appendCases_appendRight _ Γ _ _
    have hLHS : subEnvSem (Binding.Env.underBinder (Binding.subKit (rlmrOSig natAlgSig))
          (Ξ := List.replicate n σ') σ) (childEnv Δ σ' n ρ rest)
          (finAppR Γ (List.replicate n σ') j) ≍ rest ⟨j.val, hj⟩ := by
      have hposval : (Binding.Var.appendRight Δ
          (⟨j, (get_finAppR Γ (List.replicate n σ') j).symm⟩ :
            Binding.Var (List.replicate n σ') _)).1.val = Δ.length + j.val := by
        rw [appendRight_val]
      have hgeD : ¬ (Binding.Var.appendRight Δ
          (⟨j, (get_finAppR Γ (List.replicate n σ') j).symm⟩ :
            Binding.Var (List.replicate n σ') _)).1.val < Δ.length := by rw [hposval]; omega
      have hbD : (Binding.Var.appendRight Δ
          (⟨j, (get_finAppR Γ (List.replicate n σ') j).symm⟩ :
            Binding.Var (List.replicate n σ') _)).1.val - Δ.length < n := by rw [hposval]; omega
      have hvaleqD : (Binding.Var.appendRight Δ
          (⟨j, (get_finAppR Γ (List.replicate n σ') j).symm⟩ :
            Binding.Var (List.replicate n σ') _)).1.val - Δ.length = j.val := by
        rw [hposval]; omega
      have hposD : (⟨(Binding.Var.appendRight Δ
          (⟨j, (get_finAppR Γ (List.replicate n σ') j).symm⟩ :
            Binding.Var (List.replicate n σ') _)).1.val - Δ.length, hbD⟩ : Fin n)
          = ⟨j.val, hj⟩ := Fin.ext hvaleqD
      simp only [subEnvSem]
      rw [hvar, appEval_var]
      refine (eqRec_heq _ _).trans ((childEnv_heq_right ρ rest _ hgeD hbD).trans ?_)
      exact heq_of_eq (congrArg rest hposD)
    have hvaleqR : (finAppR Γ (List.replicate n σ') j).val - Γ.length = j.val := by
      rw [hvalR]; omega
    have hposR : (⟨(finAppR Γ (List.replicate n σ') j).val - Γ.length, hbR⟩ : Fin n)
        = ⟨j.val, hj⟩ := Fin.ext hvaleqR
    have hRHS : childEnv Γ σ' n (subEnvSem σ ρ) rest (finAppR Γ (List.replicate n σ') j)
        ≍ rest ⟨j.val, hj⟩ :=
      (childEnv_heq_right (subEnvSem σ ρ) rest _ hgeR hbR).trans
        (heq_of_eq (congrArg rest hposR))
    exact hLHS.trans hRHS.symm

/-- The `app`-node substitution reconciliation (empty binder suffix): the
semantic substitution of the `Γ ++ [] = Γ` transport of `ρ` equals the transport
of the substituted `ρ`. The `app` arm of `appEvalOp_subEnvSem`. -/
theorem subEnvSem_underBinder_nil {Γ Δ : Binding.Ctx RType}
    (σ : Binding.Env (Binding.Tm (rlmrOSig natAlgSig)) Γ Δ)
    (ρ : ∀ i : Fin Δ.length, RType.interp (FreeAlg natAlgSig) (Δ.get i)) :
    subEnvSem (Binding.Env.underBinder (Binding.subKit (rlmrOSig natAlgSig)) (Ξ := []) σ)
        (envCastCtx (List.append_nil Δ).symm ρ)
      = envCastCtx (List.append_nil Γ).symm (subEnvSem σ ρ) := by
  rw [envCastCtx_eq_childEnv_zero RType.o, envCastCtx_eq_childEnv_zero RType.o]
  exact subEnvSem_underBinder_childEnv σ ρ finZeroElim

/-- The `lam`-node substitution reconciliation (singleton binder suffix): the
semantic substitution of the binder-extended `ρ` equals the extension of the
substituted `ρ`. The `lam` arm of `appEvalOp_subEnvSem`. -/
theorem subEnvSem_underBinder_extend {Γ Δ : Binding.Ctx RType} {σ' : RType}
    (σ : Binding.Env (Binding.Tm (rlmrOSig natAlgSig)) Γ Δ)
    (ρ : ∀ i : Fin Δ.length, RType.interp (FreeAlg natAlgSig) (Δ.get i))
    (v : RType.interp (FreeAlg natAlgSig) σ') :
    subEnvSem (Binding.Env.underBinder (Binding.subKit (rlmrOSig natAlgSig)) (Ξ := [σ']) σ)
        (envExtend ρ v)
      = envExtend (subEnvSem σ ρ) v :=
  subEnvSem_underBinder_childEnv (n := 1) σ ρ (fun _ => v)

/-- Per-operation naturality of `appEvalOp` under semantic substitution: the
substitution analogue of `appEvalOp_renEnvSem`. The `app` and `lam` arms use the
two substitution reconciliations; the nullary constants ignore both the subterm
family and the environment. The operation case of `appEval_sub` (Leivant III
§4.1). -/
theorem appEvalOp_subEnvSem {Γ Δ : Binding.Ctx RType} (o : RlmrOOp natAlgSig)
    (σ : Binding.Env (Binding.Tm (rlmrOSig natAlgSig)) Γ Δ)
    (g : ∀ j : Fin ((rlmrOSig natAlgSig).args o).length,
      (∀ i : Fin (Γ ++ (((rlmrOSig natAlgSig).args o).get j).1).length,
        RType.interp (FreeAlg natAlgSig)
          ((Γ ++ (((rlmrOSig natAlgSig).args o).get j).1).get i)) →
        RType.interp (FreeAlg natAlgSig) (((rlmrOSig natAlgSig).args o).get j).2)
    (ρ : ∀ i : Fin Δ.length, RType.interp (FreeAlg natAlgSig) (Δ.get i)) :
    appEvalOp (Γ := Δ) o
        (fun j ρ'' => g j (subEnvSem (Binding.Env.underBinder (Binding.subKit (rlmrOSig natAlgSig))
          (Ξ := (((rlmrOSig natAlgSig).args o).get j).1) σ) ρ'')) ρ
      = appEvalOp (Γ := Γ) o g (subEnvSem σ ρ) := by
  cases o with
  | app σ' τ =>
      simp only [appEvalOp]
      have h0 : subEnvSem (Binding.Env.underBinder (Binding.subKit (rlmrOSig natAlgSig))
            (Ξ := (((rlmrOSig natAlgSig).args (RlmrOOp.app σ' τ)).get ⟨0, Nat.zero_lt_two⟩).1) σ)
          (envCastCtx (List.append_nil Δ).symm ρ)
            = envCastCtx (List.append_nil Γ).symm (subEnvSem σ ρ) :=
        subEnvSem_underBinder_nil σ ρ
      have h1 : subEnvSem (Binding.Env.underBinder (Binding.subKit (rlmrOSig natAlgSig))
            (Ξ := (((rlmrOSig natAlgSig).args (RlmrOOp.app σ' τ)).get ⟨1, Nat.one_lt_two⟩).1) σ)
          (envCastCtx (List.append_nil Δ).symm ρ)
            = envCastCtx (List.append_nil Γ).symm (subEnvSem σ ρ) :=
        subEnvSem_underBinder_nil σ ρ
      rw [h0, h1]
      rfl
  | lam σ' τ =>
      simp only [appEvalOp]
      funext v
      have h : subEnvSem (Binding.Env.underBinder (Binding.subKit (rlmrOSig natAlgSig))
            (Ξ := (((rlmrOSig natAlgSig).args (RlmrOOp.lam σ' τ)).get ⟨0, Nat.zero_lt_one⟩).1) σ)
          (envExtend ρ v) = envExtend (subEnvSem σ ρ) v := subEnvSem_underBinder_extend σ ρ v
      rw [h]
      rfl
  | con θ' hθ b => rfl
  | recur τ => rfl
  | dstr j => rfl
  | case θ' hθ => rfl

/-- Substitution fusion at a variable leaf: substituting a variable reads the
environment through `subEnvSem`. Factored via `sub_var`. -/
theorem appEval_sub_var {Γ Δ : Binding.Ctx RType} {s : RType}
    (σ : Binding.Env (Binding.Tm (rlmrOSig natAlgSig)) Γ Δ) (x : Binding.Var Γ s)
    (ρ : ∀ i : Fin Δ.length, RType.interp (FreeAlg natAlgSig) (Δ.get i)) :
    appEval (Binding.sub σ (Binding.Tm.var x)) ρ
      = appEval (Binding.Tm.var x) (subEnvSem σ ρ) := by
  rw [Binding.sub_var, appEval_var]
  obtain ⟨pos, hsort⟩ := x
  subst hsort
  simp only [subEnvSem]

/-- Substitution fusion for `appEval` (Leivant III §4.1): evaluating a
substituted term at an environment equals evaluating the original at the
semantically substituted environment. The base case reads the environment
through `subEnvSem`; the operation case is `appEvalOp_subEnvSem` on the
binder-weakened subterm denotations. The substitution analogue of `appEval_ren`,
whose binder-weakening step (`wk = ren`) reuses `appEval_ren`. Stated over an
arbitrary index so the induction on the term goes through. -/
@[simp] theorem appEval_sub : ∀ {y : Binding.Ctx RType × RType}
    (t : PolyFix (polyTranslate (Binding.varOver (Ty := RType)) (rlmrOSig natAlgSig).polyEndo) y)
    {Δ : Binding.Ctx RType} (σ : Binding.Env (Binding.Tm (rlmrOSig natAlgSig)) y.1 Δ)
    (ρ : ∀ i : Fin Δ.length, RType.interp (FreeAlg natAlgSig) (Δ.get i)),
    appEval (Binding.sub σ t) ρ = appEval t (subEnvSem σ ρ) := by
  intro y t
  induction t with
  | mk y idx children ih =>
    intro Δ σ ρ
    cases idx with
    | inl a =>
      rw [show (PolyFix.mk y (Sum.inl a) children : Binding.Tm (rlmrOSig natAlgSig) y.1 y.2)
            = Binding.Tm.var (leafVar a) from by
              obtain ⟨⟨Γ', i'⟩, rfl⟩ := a
              congr 1
              funext e
              exact e.elim]
      exact appEval_sub_var σ (leafVar a) ρ
    | inr p =>
      obtain ⟨Γ', s'⟩ := y
      change { o : (rlmrOSig natAlgSig).Op // (rlmrOSig natAlgSig).result o = s' } at p
      revert children ih
      obtain ⟨o, rfl⟩ := p
      intro children ih
      rw [show (PolyFix.mk (Γ', (rlmrOSig natAlgSig).result o) (Sum.inr ⟨o, rfl⟩) children
            : Binding.Tm (rlmrOSig natAlgSig) Γ' ((rlmrOSig natAlgSig).result o))
            = Binding.Tm.op o (fun j => children ⟨j⟩) from rfl]
      rw [Binding.sub, Binding.traverse_op, appEval_op, appEval_op]
      have hfam : (fun j => appEval (Binding.traverse (Binding.subKit (rlmrOSig natAlgSig))
            (Binding.Env.underBinder (Binding.subKit (rlmrOSig natAlgSig)) σ) (children ⟨j⟩)))
          = (fun (j : Fin ((rlmrOSig natAlgSig).args o).length) ρ'' =>
              appEval (children ⟨j⟩) (subEnvSem (Binding.Env.underBinder
                (Binding.subKit (rlmrOSig natAlgSig)) σ) ρ'')) := by
        funext j ρ''
        exact ih ⟨j⟩ (Binding.Env.underBinder (Binding.subKit (rlmrOSig natAlgSig)) σ) ρ''
      rw [hfam]
      exact appEvalOp_subEnvSem o σ (fun j => appEval (children ⟨j⟩)) ρ

/-- An `arrow`-shape free-algebra node is the `RType.arrow` of its two children.
A fact local to `caseAtType`, discharging the node-reconstruction transport of
its arrow case (`RType.interp` avoids the transport by returning a `Type`; a
term-valued recursion cannot). -/
theorem arrow_node_eq (x : PUnit)
    (childx : Fin (rTypeSig.ar RTypeShape.arrow) → RType) :
    (PolyFix.mk x RTypeShape.arrow childx : RType)
      = RType.arrow (childx ⟨0, by decide⟩) (childx ⟨1, by decide⟩) := by
  rw [RType.arrow, FreeAlg.mk]
  have hx : x = PUnit.unit := Subsingleton.elim x PUnit.unit
  subst hx
  congr 1
  funext e
  match e with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl

/-- Case analysis at an arbitrary result sort `τ`, η-expanding through arrows
down to the object-sorted `case` combinator (Leivant III §4.1 Examples 1–2, the
push of `case` under λ that realizes flat recurrence at higher type). At an
object sort (`o` or `Ωσ`) it is the `case` operation applied to the recurrence
argument `z` and the branches; at `arrow σ ρ` it is
`λ(w : σ). case^ρ z (b₀ w) … (b_{k-1} w)`, weakening `z` and the branches under
the fresh binder and recursing on the codomain. Recursion on `τ` via
`PolyFix.ind`, generalized over the ambient context so the arrow case may grow
it. -/
def caseAtType : (τ : RType) → (Γ : Binding.Ctx RType) →
    Binding.Tm (rlmrOSig natAlgSig) Γ RType.o →
    (Fin natAlgSig.numCtors → Binding.Tm (rlmrOSig natAlgSig) Γ τ) →
    Binding.Tm (rlmrOSig natAlgSig) Γ τ :=
  PolyFix.ind (P := rTypeSig.polyEndo)
    (motive := fun {_} t => (Γ : Binding.Ctx RType) →
      Binding.Tm (rlmrOSig natAlgSig) Γ RType.o →
      (Fin natAlgSig.numCtors → Binding.Tm (rlmrOSig natAlgSig) Γ t) →
      Binding.Tm (rlmrOSig natAlgSig) Γ t)
    (fun {x} i childx ih =>
      match i, childx, ih with
      | RTypeShape.o, childx, _ih => fun _Γ z bs =>
        replicateSpine natAlgSig.numCtors (PolyFix.mk x RTypeShape.o childx)
          (app' (Binding.Tm.op (S := rlmrOSig natAlgSig)
            (RlmrOOp.case (PolyFix.mk x RTypeShape.o childx) (Or.inl rfl))
            (fun k => k.elim0)) z) bs
      | RTypeShape.omega, childx, _ih => fun _Γ z bs =>
        replicateSpine natAlgSig.numCtors (PolyFix.mk x RTypeShape.omega childx)
          (app' (Binding.Tm.op (S := rlmrOSig natAlgSig)
            (RlmrOOp.case (PolyFix.mk x RTypeShape.omega childx) (Or.inr rfl))
            (fun k => k.elim0)) z) bs
      | RTypeShape.arrow, childx, ih => fun Γ z bs =>
        let d0 : Fin (rTypeSig.ar RTypeShape.arrow) := ⟨0, by decide⟩
        let d1 : Fin (rTypeSig.ar RTypeShape.arrow) := ⟨1, by decide⟩
        let σ : RType := childx d0
        (arrow_node_eq x childx).symm ▸
          lam' (ih d1 (Γ ++ [σ])
            (Binding.ren Binding.Thinning.weakAppend z)
            (fun k => app'
              (Binding.ren Binding.Thinning.weakAppend ((arrow_node_eq x childx) ▸ bs k))
              (Binding.Tm.var boundVar))))

/-- One branch of the flat-recurrence realization (Leivant III §4.1 Example 2):
the translated clause `clause` for constructor `i`, moved into the recurrence
context `params ++ [o]` by substitution. The parameter variables embed
unchanged (`Binding.Thinning.weakAppend`); each of the `ar i` subterm variables
is replaced by `dstr_j` applied to the recurrence argument `z`, reading the
`j`-th immediate subterm of the scrutinee. -/
def frecBranch {τ : RType} (params : List RType) (i : natAlgSig.B)
    (clause : Binding.Tm (rlmrOSig natAlgSig)
      (params ++ List.replicate (natAlgSig.ar i) RType.o) τ)
    (z : Binding.Tm (rlmrOSig natAlgSig) (params ++ [RType.o]) RType.o) :
    Binding.Tm (rlmrOSig natAlgSig) (params ++ [RType.o]) τ :=
  Binding.sub
    (Binding.extendEnv
      (fun _s v => Binding.Tm.var (Binding.Thinning.weakAppend.app v))
      (fun t w =>
        have hlen : (List.replicate (natAlgSig.ar i) RType.o).length = natAlgSig.ar i :=
          List.length_replicate
        have hval : w.1.val < natAlgSig.ar i :=
          Nat.lt_of_lt_of_le w.1.isLt (le_of_eq hlen)
        have hlt : w.1.val < natAlgSig.maxArity :=
          Nat.lt_of_lt_of_le hval (Finset.le_sup (f := natAlgSig.ar) (Finset.mem_univ i))
        have hot : RType.o = t := by
          have hrep : (List.replicate (natAlgSig.ar i) RType.o).get w.1 = RType.o := by
            rw [List.get_eq_getElem, List.getElem_replicate]
          exact hrep ▸ w.2
        hot ▸ app' (Binding.Tm.op (S := rlmrOSig natAlgSig)
          (RlmrOOp.dstr ⟨w.1.val, hlt⟩) (fun k => k.elim0)) z))
    clause

/-- Evaluating a flat-recurrence branch `frecBranch params i clause z` at `ρ` is
the evaluation of the translated `clause` at the recurrence-context environment
whose parameter slots read `ρ`'s parameters (`envHead`) and whose `ar i` subterm
slots read the immediate subterms of the recurrence argument `appEval z ρ`
(`dstrRead`). Since `frecBranch` is a `Binding.sub`, apply `appEval_sub` and
reconcile `subEnvSem` of the branch's `extendEnv` with the `childEnv` gluing:
the parameter variables embed by `weakAppend`, the subterm variables by the
destructor `dstr`. Leivant III §4.1 Example 2. -/
theorem appEval_frecBranch {τ : RType} (params : List RType) (i : natAlgSig.B)
    (clause : Binding.Tm (rlmrOSig natAlgSig)
      (params ++ List.replicate (natAlgSig.ar i) RType.o) τ)
    (z : Binding.Tm (rlmrOSig natAlgSig) (params ++ [RType.o]) RType.o)
    (ρ : ∀ k : Fin (params ++ [RType.o]).length,
      RType.interp (FreeAlg natAlgSig) ((params ++ [RType.o]).get k)) :
    appEval (frecBranch params i clause z) ρ
      = appEval clause (childEnv params RType.o (natAlgSig.ar i)
          (envHead params RType.o ρ) (fun j => dstrRead j.val (appEval z ρ))) := by
  rw [frecBranch]
  refine (appEval_sub clause _ ρ).trans ?_
  congr 1
  funext p
  refine finApp_cases (Γ := params) (Δ := List.replicate (natAlgSig.ar i) RType.o)
    (motive := fun p => subEnvSem _ ρ p
      = childEnv params RType.o (natAlgSig.ar i) (envHead params RType.o ρ)
          (fun j => dstrRead j.val (appEval z ρ)) p)
    (fun i0 => ?_) (fun j => ?_) p
  · apply eq_of_heq
    have hext : Binding.extendEnv
        (fun _s v => Binding.Tm.var (Binding.Thinning.weakAppend.app v))
        (fun t w =>
          have hlen : (List.replicate (natAlgSig.ar i) RType.o).length = natAlgSig.ar i :=
            List.length_replicate
          have hval : w.1.val < natAlgSig.ar i :=
            Nat.lt_of_lt_of_le w.1.isLt (le_of_eq hlen)
          have hlt : w.1.val < natAlgSig.maxArity :=
            Nat.lt_of_lt_of_le hval (Finset.le_sup (f := natAlgSig.ar) (Finset.mem_univ i))
          have hot : RType.o = t := by
            have hrep : (List.replicate (natAlgSig.ar i) RType.o).get w.1 = RType.o := by
              rw [List.get_eq_getElem, List.getElem_replicate]
            exact hrep ▸ w.2
          (hot ▸ app' (Binding.Tm.op (S := rlmrOSig natAlgSig)
            (RlmrOOp.dstr ⟨w.1.val, hlt⟩) (fun k => k.elim0)) z
            : Binding.Tm (rlmrOSig natAlgSig) (params ++ [RType.o]) t))
        ((params ++ List.replicate (natAlgSig.ar i) RType.o).get
          (finAppL params (List.replicate (natAlgSig.ar i) RType.o) i0))
        ⟨finAppL params (List.replicate (natAlgSig.ar i) RType.o) i0, rfl⟩
        = Binding.Tm.var (Binding.Thinning.weakAppend.app
            (⟨i0, (get_finAppL params (List.replicate (natAlgSig.ar i) RType.o) i0).symm⟩ :
              Binding.Var params _)) := by
      simp only [Binding.extendEnv, Binding.splitVar]
      rw [taut_finAppL_eq, Binding.Var.appendCases_weakAppend]
    simp only [subEnvSem]
    rw [hext, appEval_var, childEnv_finAppL]
    refine (eqRec_heq _ _).trans (HEq.trans ?_ (cast_heq _ _).symm)
    simp only [envHead]
    refine HEq.trans ?_ (cast_heq _ _).symm
    have hpos : (Binding.Thinning.weakAppend.app
        (⟨i0, (get_finAppL params (List.replicate (natAlgSig.ar i) RType.o) i0).symm⟩ :
          Binding.Var params _)).1 = finAppL params [RType.o] i0 :=
      Fin.ext (by rw [weakAppend_app_val]; simp [finAppL])
    rw [hpos]
  · apply eq_of_heq
    have hj : j.val < natAlgSig.ar i := lt_of_lt_of_eq j.isLt List.length_replicate
    have hext : Binding.extendEnv
        (fun _s v => Binding.Tm.var (Binding.Thinning.weakAppend.app v))
        (fun t w =>
          have hlen : (List.replicate (natAlgSig.ar i) RType.o).length = natAlgSig.ar i :=
            List.length_replicate
          have hval : w.1.val < natAlgSig.ar i :=
            Nat.lt_of_lt_of_le w.1.isLt (le_of_eq hlen)
          have hlt : w.1.val < natAlgSig.maxArity :=
            Nat.lt_of_lt_of_le hval (Finset.le_sup (f := natAlgSig.ar) (Finset.mem_univ i))
          have hot : RType.o = t := by
            have hrep : (List.replicate (natAlgSig.ar i) RType.o).get w.1 = RType.o := by
              rw [List.get_eq_getElem, List.getElem_replicate]
            exact hrep ▸ w.2
          (hot ▸ app' (Binding.Tm.op (S := rlmrOSig natAlgSig)
            (RlmrOOp.dstr ⟨w.1.val, hlt⟩) (fun k => k.elim0)) z
            : Binding.Tm (rlmrOSig natAlgSig) (params ++ [RType.o]) t))
        ((params ++ List.replicate (natAlgSig.ar i) RType.o).get
          (finAppR params (List.replicate (natAlgSig.ar i) RType.o) j))
        ⟨finAppR params (List.replicate (natAlgSig.ar i) RType.o) j, rfl⟩
        = (have hlt : j.val < natAlgSig.maxArity :=
            Nat.lt_of_lt_of_le hj (Finset.le_sup (f := natAlgSig.ar) (Finset.mem_univ i))
          (show RType.o = (params ++ List.replicate (natAlgSig.ar i) RType.o).get
              (finAppR params (List.replicate (natAlgSig.ar i) RType.o) j) from by
            rw [get_finAppR, List.get_eq_getElem, List.getElem_replicate]) ▸
            app' (Binding.Tm.op (S := rlmrOSig natAlgSig)
              (RlmrOOp.dstr ⟨j.val, hlt⟩) (fun k => k.elim0)) z) := by
      simp only [Binding.extendEnv, Binding.splitVar]
      rw [taut_finAppR_eq, Binding.Var.appendCases_appendRight]
    simp only [subEnvSem]
    rw [hext, childEnv_finAppR _ _ _ hj]
    refine HEq.trans ?_ ((cast_heq _ _).trans (cast_heq _ _)).symm
    refine (appEval_heq _ (app' (Binding.Tm.op (S := rlmrOSig natAlgSig)
        (RlmrOOp.dstr ⟨j.val, (Nat.lt_of_lt_of_le hj
          (Finset.le_sup (f := natAlgSig.ar) (Finset.mem_univ i)))⟩)
        (fun k => k.elim0)) z) ρ ?_ (eqRec_heq _ _)).trans ?_
    · rw [get_finAppR, List.get_eq_getElem, List.getElem_replicate]
    · refine heq_of_eq ?_
      rw [appEval_app']
      exact congrFun (appEval_dstr _ (fun k => k.elim0) ρ) (appEval z ρ)

/-- The direct Proposition 7 translation of a flat-recurrence identifier
(Leivant III §4.1 Examples 1–2, the inlined `(3)⟹(4)` step of the soundness arm
`(1)⟹(4)`): case analysis at the result sort `τ` on the recurrence argument (the
sole suffix variable of `params ++ [o]`), the branch at enumeration position
`idx` being the translated clause for the constructor `ctorAt idx` with its
subterm variables read off the recurrence argument by destructors (`frecBranch`).
Flat recurrence reads the subterms of the recurrence argument, not recursive
results, so it is realized by `case`/`dstr` rather than the recurrence
combinator. -/
def prop7FrecStep {τ : RType} (params : List RType)
    (ih : (i : natAlgSig.B) →
      Binding.Tm (rlmrOSig natAlgSig)
        (params ++ List.replicate (natAlgSig.ar i) RType.o) τ) :
    Binding.Tm (rlmrOSig natAlgSig) (params ++ [RType.o]) τ :=
  caseAtType τ (params ++ [RType.o])
    (Binding.Tm.var (boundVar (Γ := params) (σ := RType.o)))
    (fun idx =>
      frecBranch params (ctorAt idx) (ih (ctorAt idx))
        (Binding.Tm.var (boundVar (Γ := params) (σ := RType.o))))

/-- The translation step of `prop7Translate` at one identifier node, the
applicative-term twin of `RIdent.interpStep` (`GebLean/Ramified/HigherOrder.lean`):
a `defn` folds its body into an applicative term (`prop7DefnStep`); a `mrec`
builds the recurrence combinator applied to the recurrence argument
(`prop7MrecStep`); a `frec` builds the `case`/`dstr` realization
(`prop7FrecStep`). The translated child identifiers are supplied by `ih`. -/
def prop7TranslateStep (Γ : List RType) (τ : RType)
    (shape : IdentShape natAlgSig Γ τ)
    (ih : ∀ dir : IdentDir natAlgSig Γ τ shape,
      Binding.Tm (rlmrOSig natAlgSig) (identTarget natAlgSig Γ τ shape dir).1
        (identTarget natAlgSig Γ τ shape dir).2) :
    Binding.Tm (rlmrOSig natAlgSig) Γ τ := by
  rcases shape with d | ⟨params, rfl⟩ | ⟨params, rfl⟩
  · exact prop7DefnStep d ih
  · exact prop7MrecStep params ih
  · exact prop7FrecStep params ih

/-- The direct Proposition 7 translation (Leivant III §4.1, the soundness arm
`(1)⟹(4)`): every ramified identifier over `natAlgSig` is defined by a term of
the object-sorted applicative calculus `RλMR_o^ω`, in open form at the
identifier's own context and result sort. Realized by structural recursion via
`PolyFix.ind` (decision 8), mirroring `RIdent.interp` and dispatching each node
through `prop7TranslateStep`. The paper routes `(1)⟹(3)⟹(4)`; the `(3)⟹(4)`
flat-operator step (§4.1 Examples 1–2) is inlined into the flat-recurrence case
of `prop7TranslateStep`. Novel packaging. -/
def prop7Translate {Γ : List RType} {τ : RType} (d : RIdent natAlgSig Γ τ) :
    Binding.Tm (rlmrOSig natAlgSig) Γ τ :=
  PolyFix.ind (P := identEndo natAlgSig)
    (motive := fun {x} _ => Binding.Tm (rlmrOSig natAlgSig) x.1 x.2)
    (fun {x} shape _children ih => prop7TranslateStep x.1 x.2 shape ih) d

end GebLean.Ramified
