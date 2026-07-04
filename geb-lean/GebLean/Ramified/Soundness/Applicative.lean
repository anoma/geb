import Mathlib.Data.Finset.Sort
import GebLean.Binding.Term
import GebLean.Binding.Substitution
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
