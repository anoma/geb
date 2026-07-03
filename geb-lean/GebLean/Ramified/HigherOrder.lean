import GebLean.Ramified.SynCat
import GebLean.Ramified.RType

/-!
# The higher-order presentation and schema identifiers

The higher-order system of Leivant's higher-type ramified recurrence: the
application operations at arrow sorts, the schema-generated identifiers
(explicit definitions, ramified monotonic recurrences, and flat recurrences)
over a base algebra, and the multi-sorted presentation assembling the
constructor summand, application, and the identifiers. Each identifier carries
its defining semantics, generated together with the signature as `ERMor1` does
for its theory (`GebLean/LawvereER.lean`); `RIdent.interp` folds an identifier
into the standard carriers `RType.interp (FreeAlg A)`, and `standardModel
(higherOrder A)` interprets every operation of the presentation there.

These definitions are novel packaging. `RIdent` is realized (decision 8) as the
`PolyFix` W-type of an indexed signature endofunctor over the index type
`List RType × RType` (context, result sort): the shapes carry each schema
former's non-recursive data — for `defn`, the defining term as a skeleton over
the base signature with holes for identifier occurrences; for `mrec`/`frec`,
the recurrence parameters — and the directions, the children in the fixed
point, are exactly the previously defined identifiers those holes and clauses
reference (a `Tm` value cannot occupy a direction). The multi-sorted
presentation and its syntactic category instantiate the packaging whose
precedent line is recorded in `GebLean/Ramified/SynCat.lean`'s references; the
data-types-a-la-carte assembly reuses `SortedSig.sum`
(`GebLean/Ramified/SortedSig.lean`) and the W-type realization reuses
`PolyFix` (`GebLean/PolyAlg.lean`).

## Main definitions

* `appSig` — the application signature: one operation per `(σ, τ)`, of arity
  `[σ → τ, σ]` and result `τ`.
* `RIdent` — the schema-generated identifiers over a base algebra `A`, indexed
  by context and result sort.
* `RIdent.defn`, `RIdent.mrec`, `RIdent.frec` — the derived schema formers
  (explicit definition, ramified monotonic recurrence eq. (4), flat recurrence
  eq. (5)).
* `RIdent.interp` — the denotation of an identifier as a function on the
  standard carriers.
* `RType.curried` — the curried arrow sort `σ₁ → ⋯ → σₙ → τ` of a context and
  result sort.
* `curryInterp` — the currying of an identifier's denotation into the iterated
  function space at its curried sort.
* `appChain` — the iterated application of a value at a curried sort to an
  argument environment.
* `identSig` — the saturated identifier summand: operations are the identifiers,
  each of its context as arity and result sort as result.
* `identConstSig` — the identifier-constant summand: one nullary operation per
  identifier, of its curried arrow sort as result.
* `higherOrder` — the higher-order presentation over `A`.
* `RMRecCat` — the syntactic category of the higher-order system.

## Main statements

* `appChain_curryInterp` — the application chain inverts the currying.
* `RIdent.interp_eq_appChain_curryInterp` — coherence: the saturated
  identifier's denotation equals the application chain of its constant's
  denotation.

## Implementation notes

`RIdent.interp` recurses on the identifier via `PolyFix.ind`. A `defn` is
interpreted by folding its body term against a model whose hole operations are
the recursive results (`Tm.eval`); a `mrec` and a `frec` recurse on the
recurrence argument via `FreeAlg.recurse`, the monotonic (`mrec`) step ignoring
the subterms and reading the recursive results, the flat (`frec`) step reading
the subterms with no recursive results. The recurrence-argument sort — `Ω τ`
for `mrec`, `o` for `frec` — is enforced by the constructor indices; both denote
a copy of the base carrier (Leivant III section 2.7), on which the recurrence
runs.

## References

D. Leivant, "Ramified recurrence and computational complexity III: Higher type
recurrence and elementary complexity", Annals of Pure and Applied Logic 96
(1999) 209-229, DOI `10.1016/S0168-0072(98)00040-2`. The schema of higher-type
identifiers — explicit definitions, ramified monotonic recurrence (eq. (4)),
and flat recurrence (eq. (5)) — is section 2.3; the monotonic fragment, in which
the step functions read the recursive results but not the subterms, is section
2.1; every object sort denotes a copy of the base carrier in section 2.7. The
schema-generation pattern (signature and defining semantics generated together)
follows the repository precedent `GebLean.ERMor1` (`GebLean/LawvereER.lean`).
The multi-sorted-presentation packaging and its doctrinal precedent are recorded
in `GebLean/Ramified/SynCat.lean`'s references. The data-types-a-la-carte
factoring follows W. Swierstra, "Data types a la carte", Journal of Functional
Programming 18 (2008) 423-436, DOI `10.1017/S0956796808006758`.

## Tags

ramified recurrence, higher type, application, schema identifier, explicit
definition, monotonic recurrence, flat recurrence, presentation, syntactic
category, W-type
-/

namespace GebLean.Ramified

open CategoryTheory

/-- The application signature (Leivant III section 2.3, the higher-order
system): for each pair `(σ, τ)` of r-types, an operation of arity `[σ → τ, σ]`
and result `τ`, applying a function to an argument. Novel packaging. -/
def appSig : SortedSig RType where
  Op := RType × RType
  arity op := [RType.arrow op.1 op.2, op.1]
  result op := op.2

/-- The denotation of an object sort is a copy of the carrier (Leivant III
section 2.7): for any `s` with `s.IsObj`, `RType.interp C s = C`. -/
theorem RType.interp_isObj (C : Type) {s : RType} (h : s.IsObj) :
    RType.interp C s = C := by
  rcases s with ⟨_, i, children⟩
  rcases h with h | h <;> (simp only [RType.shape, PolyFix.index] at h; subst h; rfl)

/-- The interpretation of a constructor operation over the standard carriers:
the free-algebra constructor `FreeAlg.mk` at the label, on the arguments read as
base-carrier elements (every object sort denotes a copy of `FreeAlg A`). Novel
packaging. -/
def stdConstructorInterp (A : AlgSig)
    (op : (constructorSig A RType.IsObj).Op)
    (args : ∀ i : Fin ((constructorSig A RType.IsObj).arity op).length,
      RType.interp (FreeAlg A) (((constructorSig A RType.IsObj).arity op).get i)) :
    RType.interp (FreeAlg A) ((constructorSig A RType.IsObj).result op) := by
  refine cast (RType.interp_isObj (FreeAlg A) op.1.2).symm
    (FreeAlg.mk op.2 (fun i => ?_))
  have hlt : i.val < ((constructorSig A RType.IsObj).arity op).length := by
    simp only [constructorSig, List.length_replicate]; exact i.isLt
  have hg : ((constructorSig A RType.IsObj).arity op).get ⟨i.val, hlt⟩ = op.1.val := by
    simp only [constructorSig, List.get_eq_getElem, List.getElem_replicate]
  exact cast (by rw [hg]; exact RType.interp_isObj (FreeAlg A) op.1.2)
    (args ⟨i.val, hlt⟩)

/-- The interpretation of an application operation over the standard carriers:
function application, reading the first argument at `σ → τ` as a function and
applying it to the second at `σ`. Novel packaging. -/
def stdAppInterp (A : AlgSig) (op : appSig.Op)
    (args : ∀ i : Fin (appSig.arity op).length,
      RType.interp (FreeAlg A) ((appSig.arity op).get i)) :
    RType.interp (FreeAlg A) (appSig.result op) :=
  have g : RType.interp (FreeAlg A) (RType.arrow op.1 op.2) :=
    args ⟨0, by simp [appSig]⟩
  g (args ⟨1, by simp [appSig]⟩)

/-- The hole signature of an explicit definition: one operation per hole, of
the hole's context as arity and the hole's result sort as result. A hole stands
for an application of a previously defined identifier. Novel packaging. -/
def holeSig (n : Nat) (holeIdx : Fin n → List RType × RType) : SortedSig RType where
  Op := Fin n
  arity j := (holeIdx j).1
  result j := (holeIdx j).2

/-- The base signature of an explicit definition's body: the constructor
summand, application, and the holes for previously defined identifiers. Novel
packaging. -/
def defnSig (A : AlgSig) (n : Nat) (holeIdx : Fin n → List RType × RType) :
    SortedSig RType :=
  ((constructorSig A RType.IsObj).sum appSig).sum (holeSig n holeIdx)

/-- The non-recursive data of an explicit definition (Leivant III section 2.3):
a defining term over the base signature extended by hole operations, one hole
per occurrence of a previously defined identifier. The directions of the fixed
point are the identifiers those holes reference. Novel packaging. -/
structure DefnShape (A : AlgSig) (Γ : List RType) (τ : RType) where
  /-- The number of identifier holes in the body. -/
  numHoles : Nat
  /-- The context and result sort each hole's referenced identifier carries. -/
  holeIdx : Fin numHoles → List RType × RType
  /-- The defining term over the base signature with holes, in context `Γ` at
  sort `τ`. -/
  body : Tm (defnSig A numHoles holeIdx) Γ τ

/-- The non-recursive data of a ramified monotonic recurrence (Leivant III
section 2.3, eq. (4)): the recurrence parameters, with the recurrence argument
sitting at `Ω τ` at the end of the context. The directions are the step
functions, previously defined identifiers. Novel packaging. -/
structure MrecShape (A : AlgSig) (Γ : List RType) (τ : RType) where
  /-- The recurrence parameters (the paper's `x_vec`). -/
  params : List RType
  /-- The context is the parameters followed by the recurrence argument at
  `Ω τ`. -/
  hΓ : Γ = params ++ [RType.omega τ]

/-- The non-recursive data of a flat recurrence (Leivant III section 2.3,
eq. (5)): the recurrence parameters, with the recurrence argument sitting at
`o` at the end of the context. The directions are the clauses, previously
defined identifiers. Novel packaging. -/
structure FrecShape (A : AlgSig) (Γ : List RType) (τ : RType) where
  /-- The recurrence parameters (the paper's `x_vec`). -/
  params : List RType
  /-- The context is the parameters followed by the recurrence argument at
  `o`. -/
  hΓ : Γ = params ++ [RType.o]

/-- The shape type of the identifier signature endofunctor at index `(Γ, τ)`:
the disjoint union of the three schema formers' non-recursive data. Novel
packaging. -/
def IdentShape (A : AlgSig) (Γ : List RType) (τ : RType) : Type :=
  DefnShape A Γ τ ⊕ MrecShape A Γ τ ⊕ FrecShape A Γ τ

/-- The direction type at a shape: the holes of a `defn`, and the constructor
labels of a `mrec` or `frec` (one step function or clause per label). Novel
packaging. -/
def IdentDir (A : AlgSig) (Γ : List RType) (τ : RType) :
    IdentShape A Γ τ → Type
  | Sum.inl d => Fin d.numHoles
  | Sum.inr (Sum.inl _) => A.B
  | Sum.inr (Sum.inr _) => A.B

/-- The target index of a direction: the context and result sort of the
referenced identifier. A `defn` hole targets its stored index; a `mrec` step
function targets `(params ++ replicate (A.ar i) τ, τ)` (parameters and recursive
results at `τ`); a `frec` clause targets `(params ++ replicate (A.ar i) o, τ)`
(parameters and subterms at `o`). Novel packaging. -/
def identTarget (A : AlgSig) (Γ : List RType) (τ : RType) :
    (s : IdentShape A Γ τ) → IdentDir A Γ τ s → List RType × RType
  | Sum.inl d, j => d.holeIdx j
  | Sum.inr (Sum.inl m), i => (m.params ++ List.replicate (A.ar i) τ, τ)
  | Sum.inr (Sum.inr fr), i => (fr.params ++ List.replicate (A.ar i) RType.o, τ)

/-- The identifier signature endofunctor over the index type `List RType × RType`
(context, result sort): shapes are the schema formers' data, directions are the
referenced identifiers. Novel packaging (decision 8). -/
def identEndo (A : AlgSig) : PolyEndo (List RType × RType) :=
  fun idx => ccrObjMk fun s : IdentShape A idx.1 idx.2 =>
    Over.mk fun d : IdentDir A idx.1 idx.2 s => identTarget A idx.1 idx.2 s d

/-- The schema-generated identifiers over a base algebra `A`, indexed by context
and result sort (Leivant III section 2.3): explicit definitions and ramified
monotonic recurrences (eq. (4)) and flat recurrences (eq. (5)) over previously
defined identifiers. Realized (decision 8) as the `PolyFix` W-type of the
indexed signature endofunctor `identEndo A`. Novel packaging. -/
def RIdent (A : AlgSig) (Γ : List RType) (τ : RType) : Type :=
  PolyFix (identEndo A) (Γ, τ)

/-- An explicit definition (Leivant III section 2.3): the defining term `d`
together with the referenced identifiers filling its holes. Novel packaging. -/
def RIdent.defn {A : AlgSig} {Γ : List RType} {τ : RType} (d : DefnShape A Γ τ)
    (children : (j : Fin d.numHoles) → RIdent A (d.holeIdx j).1 (d.holeIdx j).2) :
    RIdent A Γ τ :=
  PolyFix.mk (Γ, τ) (Sum.inl d) children

/-- A ramified monotonic recurrence (Leivant III section 2.3, eq. (4)): with
parameters `x_vec` of sorts `params` and recurrence argument at `Ω τ`, and one
step function per constructor of `A`,
`f (x_vec, c_i (a_vec)) = g_ci (x_vec, phi_vec)`, where `phi_j = f (x_vec, a_j)`
are the recursive results. The recurrence is monotonic: the step functions read
the parameters and the recursive results, not the subterms. The recurrence
argument sits at `Ω τ` and the recursive results and output at `τ`. Novel
packaging. -/
def RIdent.mrec {A : AlgSig} (params : List RType) (τ : RType)
    (steps : (i : A.B) → RIdent A (params ++ List.replicate (A.ar i) τ) τ) :
    RIdent A (params ++ [RType.omega τ]) τ :=
  PolyFix.mk (params ++ [RType.omega τ], τ) (Sum.inr (Sum.inl ⟨params, rfl⟩))
    (fun i => steps i)

/-- A flat recurrence (Leivant III section 2.3, eq. (5)): with parameters
`x_vec` of sorts `params` and recurrence argument at `o`, and one clause per
constructor of `A`, `f (x_vec, c_i (a_vec)) = h_ci (x_vec, a_vec)`. The
recurrence is flat: the clauses read the parameters and the subterms `a_vec`,
with no recursive results (a case analysis / destructor). Novel packaging. -/
def RIdent.frec {A : AlgSig} (params : List RType) (τ : RType)
    (clauses : (i : A.B) → RIdent A (params ++ List.replicate (A.ar i) RType.o) τ) :
    RIdent A (params ++ [RType.o]) τ :=
  PolyFix.mk (params ++ [RType.o], τ) (Sum.inr (Sum.inr ⟨params, rfl⟩))
    (fun i => clauses i)

/-- The model interpreting an explicit definition's body: the standard carriers,
with constructors and application read as usual and each hole read by the
recursive result of the referenced identifier. Novel packaging. -/
def defnModel (A : AlgSig) (n : Nat) (holeIdx : Fin n → List RType × RType)
    (ih : ∀ j : Fin n,
      (∀ i : Fin (holeIdx j).1.length,
        RType.interp (FreeAlg A) ((holeIdx j).1.get i)) →
        RType.interp (FreeAlg A) (holeIdx j).2) :
    SortedModel (defnSig A n holeIdx) where
  carrier := RType.interp (FreeAlg A)
  interpOp op args :=
    match op with
    | Sum.inl (Sum.inl cop) => stdConstructorInterp A cop args
    | Sum.inl (Sum.inr aop) => stdAppInterp A aop args
    | Sum.inr j => ih j args

/-- The environment over `params ++ replicate n σ` built from a parameter
environment and `n` values at sort `σ`: the recursive results (`mrec`) or the
subterms (`frec`) of a recurrence step. Novel packaging. -/
def childEnv {C : RType → Type} (params : List RType) (σ : RType) (n : Nat)
    (xvec : ∀ i : Fin params.length, C (params.get i))
    (rest : Fin n → C σ)
    (k : Fin (params ++ List.replicate n σ).length) :
    C ((params ++ List.replicate n σ).get k) :=
  if h : k.val < params.length then
    cast (congrArg C (get_append_lt params (List.replicate n σ) k h).symm)
      (xvec ⟨k.val, h⟩)
  else
    have hb : k.val - params.length < n := by
      have hlen : (params ++ List.replicate n σ).length = params.length + n := by
        rw [List.length_append, List.length_replicate]
      have hk : k.val < params.length + n := Nat.lt_of_lt_of_eq k.isLt hlen
      omega
    have hget : (params ++ List.replicate n σ).get k = σ := by
      rw [get_append_ge params (List.replicate n σ) k h]
      simp [List.get_eq_getElem, List.getElem_replicate]
    cast (congrArg C hget.symm) (rest ⟨k.val - params.length, hb⟩)

/-- The parameter environment read off a recurrence context `params ++ [ω]`. -/
def envHead {C : RType → Type} (params : List RType) (ω : RType)
    (ρ : ∀ k : Fin (params ++ [ω]).length, C ((params ++ [ω]).get k)) :
    ∀ i : Fin params.length, C (params.get i) :=
  fun i => cast (congrArg C (get_finAppL params [ω] i)) (ρ (finAppL params [ω] i))

/-- The recurrence argument read off a recurrence context `params ++ [ω]`. -/
def envLast {C : RType → Type} (params : List RType) (ω : RType)
    (ρ : ∀ k : Fin (params ++ [ω]).length, C ((params ++ [ω]).get k)) : C ω :=
  let idx : Fin [ω].length := ⟨0, by simp⟩
  cast (congrArg C (get_finAppR params [ω] idx)) (ρ (finAppR params [ω] idx))

/-- The recursion step of `RIdent.interp` at one identifier node: a `defn`
folds its body against `defnModel`; a `mrec` recurses on the recurrence argument
with the monotonic step (parameters and recursive results); a `frec` recurses
with the flat step (parameters and subterms). Novel packaging. -/
def RIdent.interpStep (A : AlgSig) (Γ : List RType) (τ : RType)
    (shape : IdentShape A Γ τ)
    (ih : ∀ d : IdentDir A Γ τ shape,
      (∀ i : Fin (identTarget A Γ τ shape d).1.length,
        RType.interp (FreeAlg A) ((identTarget A Γ τ shape d).1.get i)) →
        RType.interp (FreeAlg A) (identTarget A Γ τ shape d).2) :
    (∀ i : Fin Γ.length, RType.interp (FreeAlg A) (Γ.get i)) →
      RType.interp (FreeAlg A) τ := by
  rcases shape with d | ⟨params, rfl⟩ | ⟨params, rfl⟩
  · exact fun ρ => d.body.eval (defnModel A d.numHoles d.holeIdx ih) ρ
  · exact fun ρ =>
      FreeAlg.recurse (A := A) (P := Unit)
        (fun i _ _sub phi =>
          ih i (childEnv params τ (A.ar i) (envHead params (RType.omega τ) ρ) phi))
        () (envLast params (RType.omega τ) ρ)
  · exact fun ρ =>
      FreeAlg.recurse (A := A) (P := Unit)
        (fun i _ sub _phi =>
          ih i (childEnv params RType.o (A.ar i) (envHead params RType.o ρ)
            (fun j => sub j)))
        () (envLast params RType.o ρ)

/-- The denotation of an identifier over the standard carriers `RType.interp
(FreeAlg A)`: a function from an environment at the identifier's context to a
value at its result sort. Realized by structural recursion via `PolyFix.ind`
(decision 8), following the precedent `GebLean.ERMor1.interp`
(`GebLean/LawvereER.lean`). Novel packaging. -/
def RIdent.interp {A : AlgSig} {Γ : List RType} {τ : RType} (f : RIdent A Γ τ) :
    (∀ i : Fin Γ.length, RType.interp (FreeAlg A) (Γ.get i)) →
      RType.interp (FreeAlg A) τ :=
  PolyFix.ind (P := identEndo A)
    (motive := fun {x} _ =>
      (∀ i : Fin x.1.length, RType.interp (FreeAlg A) (x.1.get i)) →
        RType.interp (FreeAlg A) x.2)
    (fun {x} shape _children ih => RIdent.interpStep A x.1 x.2 shape ih) f

/-- The curried arrow sort of a context and result sort: `σ₁ → ⋯ → σₙ → τ` for
`Γ = [σ₁, …, σₙ]`, the right fold of `RType.arrow` over `Γ` with base `τ`. The
sort at which an identifier of context `Γ` and result `τ` sits as a value
(Leivant III section 2.3, the higher-order system: identifiers are terms at
higher types). Novel packaging. -/
def RType.curried (Γ : List RType) (τ : RType) : RType := Γ.foldr RType.arrow τ

@[simp] theorem RType.curried_nil (τ : RType) : RType.curried [] τ = τ := rfl

@[simp] theorem RType.curried_cons (σ : RType) (Γ : List RType) (τ : RType) :
    RType.curried (σ :: Γ) τ = RType.arrow σ (RType.curried Γ τ) := rfl

/-- The currying of a function on environments into the iterated function space
at the curried sort: from a map `Env Γ → interp τ` to a value at
`interp (RType.curried Γ τ)`, consuming the context sorts one at a time. The
denotation of an identifier's constant is `curryInterp` of the identifier's
denotation. Novel packaging. -/
def curryInterp (A : AlgSig) : (Γ : List RType) → (τ : RType) →
    ((∀ i : Fin Γ.length, RType.interp (FreeAlg A) (Γ.get i)) →
      RType.interp (FreeAlg A) τ) →
    RType.interp (FreeAlg A) (RType.curried Γ τ)
  | [], _τ, g => g finZeroElim
  | σ :: Γ', τ, g => fun x : RType.interp (FreeAlg A) σ =>
      curryInterp A Γ' τ (fun ρ' => g (Fin.cons x ρ'))

/-- The application chain: iterated application of a value at a curried sort
`RType.curried Γ τ` to an argument environment `Env Γ`, yielding a value at `τ`.
The application former's action on an identifier's constant, recovering the
saturated identifier's denotation. Novel packaging. -/
def appChain (A : AlgSig) : (Γ : List RType) → (τ : RType) →
    RType.interp (FreeAlg A) (RType.curried Γ τ) →
    (∀ i : Fin Γ.length, RType.interp (FreeAlg A) (Γ.get i)) →
    RType.interp (FreeAlg A) τ
  | [], _τ, c, _ρ => c
  | σ :: Γ', τ, c, ρ =>
      appChain A Γ' τ ((c : RType.interp (FreeAlg A) σ →
        RType.interp (FreeAlg A) (RType.curried Γ' τ)) (ρ 0)) (fun i => ρ i.succ)

/-- The application chain inverts the currying: applying `curryInterp A Γ τ g`
to an environment `ρ` recovers `g ρ`. Proved by induction on `Γ`; the step folds
the leading argument back into the environment via `Fin.cons_self_tail`. -/
theorem appChain_curryInterp (A : AlgSig) : (Γ : List RType) → (τ : RType) →
    (g : (∀ i : Fin Γ.length, RType.interp (FreeAlg A) (Γ.get i)) →
      RType.interp (FreeAlg A) τ) →
    (ρ : ∀ i : Fin Γ.length, RType.interp (FreeAlg A) (Γ.get i)) →
    appChain A Γ τ (curryInterp A Γ τ g) ρ = g ρ
  | [], _τ, g, _ρ => congrArg g (funext (fun i => i.elim0))
  | σ :: Γ', τ, g, ρ => by
    change appChain A Γ' τ (curryInterp A Γ' τ (fun ρ' => g (Fin.cons (ρ 0) ρ')))
        (fun i => ρ i.succ) = g ρ
    rw [appChain_curryInterp A Γ' τ (fun ρ' => g (Fin.cons (ρ 0) ρ')) (fun i => ρ i.succ)]
    exact congrArg g (Fin.cons_self_tail ρ)

/-- Coherence of the two identifier surfacings (Leivant III section 2.3, the
higher-order system): the saturated identifier's denotation equals the
application chain of its constant's denotation. The constant of `f` denotes
`curryInterp A Γ τ f.interp`; applying it along the argument environment via
`appChain` recovers `f.interp`. Novel packaging. -/
theorem RIdent.interp_eq_appChain_curryInterp {A : AlgSig} {Γ : List RType}
    {τ : RType} (f : RIdent A Γ τ)
    (ρ : ∀ i : Fin Γ.length, RType.interp (FreeAlg A) (Γ.get i)) :
    f.interp ρ = appChain A Γ τ (curryInterp A Γ τ f.interp) ρ :=
  (appChain_curryInterp A Γ τ f.interp ρ).symm

/-- The saturated identifier summand of the higher-order presentation:
operations are the schema-generated identifiers, of context as arity and result
sort as result. Each identifier also has a nullary constant form in
`identConstSig`, a value at its curried arrow sort; the two surfacings agree by
`RIdent.interp_eq_appChain_curryInterp`. Novel packaging. -/
def identSig (A : AlgSig) : SortedSig RType where
  Op := Σ Γ : List RType, Σ τ : RType, RIdent A Γ τ
  arity op := op.1
  result op := op.2.1

/-- The identifier-constant summand of the higher-order presentation (Leivant
III section 2.3, the higher-order system, DOI `10.1016/S0168-0072(98)00040-2`):
one nullary operation per identifier `f : RIdent A Γ τ`, with result the curried
arrow sort `RType.curried Γ τ`. This is the transcription-faithful reading of
the paper's identifiers as combinators — an identifier is a term at the higher
type `σ₁ → ⋯ → σₙ → τ`, and the application former is what fills arrow-sorted
recurrence clauses by partial application. Novel packaging. -/
def identConstSig (A : AlgSig) : SortedSig RType where
  Op := Σ Γ : List RType, Σ τ : RType, RIdent A Γ τ
  arity _op := []
  result op := RType.curried op.1 op.2.1

/-- The standard model of the higher-order presentation over `A`: the standard
carriers, with constructors and application read as usual, each saturated
identifier read by its own denotation, and each identifier constant read by the
currying of that denotation. Novel packaging. -/
def higherOrderModel (A : AlgSig) :
    SortedModel
      ((((constructorSig A RType.IsObj).sum appSig).sum (identSig A)).sum
        (identConstSig A)) where
  carrier := RType.interp (FreeAlg A)
  interpOp op args :=
    match op with
    | Sum.inl (Sum.inl (Sum.inl cop)) => stdConstructorInterp A cop args
    | Sum.inl (Sum.inl (Sum.inr aop)) => stdAppInterp A aop args
    | Sum.inl (Sum.inr iop) => iop.2.2.interp args
    | Sum.inr icop => curryInterp A icop.1 icop.2.1 icop.2.2.interp

/-- The higher-order presentation over `A` (Leivant III section 2.3): the
constructor summand at every object sort, application, the schema-generated
identifiers as saturated operations, and their nullary constants at the curried
arrow sorts, summed by `SortedSig.sum`, with the standard model interpreting
each operation over the standard carriers. Novel packaging. -/
def higherOrder (A : AlgSig) : Presentation where
  S := RType
  sig :=
    ((((constructorSig A RType.IsObj).sum appSig).sum (identSig A)).sum
      (identConstSig A))
  IsObj := RType.IsObj
  alg := A
  std := higherOrderModel A

/-- The syntactic category of the higher-order system over `A`: the generic
syntactic category of `higherOrder A` under interpretative equality at the
standard model. The Phase 1 `Category` and `CartesianMonoidalCategory` instances
of `SynCat` apply. Novel packaging. -/
abbrev RMRecCat (A : AlgSig) :=
  SynCat (higherOrder A) (interpQuotRel (higherOrder A))

end GebLean.Ramified
