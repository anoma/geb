import GebLean.Ramified.Definability.Simultaneous

/-!
# The destructor/case presentation and its flat realization

The destructor/case operations of Leivant III (section 2.5's `RRec_o` layer):
the destructors `dstr_j : o → o` reading a subterm of the recurrence argument
and, at each object sort `θ`, the case operation `case^θ : o, θ^k → θ`
branching on the main constructor. `dstrCaseSig` packages them as a
`SortedSig` summand generic in a free-algebra signature `A`; `dstrCaseModel`
gives the standard semantics of section 4.1 (a destructor returns the `j`-th
subterm, or the whole argument when `j` reaches the arity; the case operation
selects the branch of the argument's top constructor); and `dstrCaseToFlat`
realizes each operation over the `1 + X` word algebra `natAlgSig` as a derived
identifier of the higher-order system (`GebLean/Ramified/HigherOrder.lean`),
witnessing the containment direction `RRec_o ⊆ RRec` of Lemma 1 by flat
recurrence (`ramDstr` and `ramCase` of
`GebLean/Ramified/Definability/Simultaneous.lean`), with `dstrCaseToFlat_interp`
proving the two agree.

The module also assembles the O-variant presentation itself: the object-sorted
systems `RRec_o^omega` / `RMRec_o^omega` of section 2.5, in which flat
recurrence is replaced by the destructor and case functions. `RIdentO` mirrors
the identifier layer of `GebLean/Ramified/HigherOrder.lean` with the flat
recurrence former removed and `dstrCaseSig` added to the term signature;
`higherOrderO` is the resulting presentation over `natAlgSig` and `RMRecCatO`
its syntactic category.

## Main definitions

* `AlgSig.numCtors`, `AlgSig.maxArity` — the constructor count and the largest
  arity of a finite free-algebra signature.
* `dstrCaseSig` — the destructor/case summand over `A`: destructors indexed by
  `Fin A.maxArity` and case operations indexed by the object sorts.
* `dstrCaseModel` — the standard semantics over `natAlgSig` (section 4.1).
* `dstrCaseToFlat` — the realization of each operation as a derived identifier
  of `higherOrder natAlgSig` (Lemma 1, containment direction).
* `defnSigO`, `DefnShapeO`, `IdentShapeO`, `RIdentO` — the O-variant identifier
  layer: explicit definitions over a body signature carrying the
  destructor/case operations, and ramified monotonic recurrences; no flat
  recurrence.
* `RIdentO.defn`, `RIdentO.mrec` — the derived schema formers.
* `RIdentO.interp` — the denotation of an O-variant identifier on the standard
  carriers.
* `higherOrderO` — the O-variant presentation over `natAlgSig`.
* `RMRecCatO` — the syntactic category of the O-variant system.

## Main statements

* `dstrCaseToFlat_interp` — the realization agrees with the standard semantics:
  `(dstrCaseToFlat op).interp = dstrCaseModel op`.

## Implementation notes

The destructor count `A.maxArity` and constructor count `A.numCtors` are the
finite quantities `Finset.univ.sup A.ar` and `Fintype.card A.B`, so `dstrCaseSig`
carries a `Fintype A.B` instance; over `natAlgSig` they reduce to `1` and `2`,
leaving the single predecessor destructor `dstr_0` and the binary case
operation `case^θ : o, θ, θ → θ`. The case operation's argument order places the
recurrence argument first (`o :: θ^k`, faithful to `case^θ : o, θ^k → θ`),
while the flat recurrence `ramCase` places it last (`θ^k ++ [o]`, the eq. (5)
convention); `dstrCaseFlatCase` bridges the two by an explicit definition
applying `ramCase θ` to the reordered variables. The standard semantics is
expressed by the carrier-level operations `dstrRead` and `caseSelect`, each a
`FreeAlg.recurse` reading the top constructor; the model routes through the
concrete-context helpers `dstrCaseModelDstr` and `dstrCaseModelCase` so that
the argument environment is read at the literal context.

`dstrCaseSig` is generic in `A`; `dstrCaseModel` and `dstrCaseToFlat` are
`natAlgSig`-scoped. The signature packaging is novel; the destructor/case
operations transcribe Leivant III section 2.5, their semantics section 4.1, and
their flat definability the containment direction of Lemma 1.

The O-variant layer mirrors `GebLean/Ramified/HigherOrder.lean`'s identifier
layer declaration for declaration, with two deltas: the flat-recurrence former
is removed and `dstrCaseSig` is added to the term signature. The mirror is
deliberate: parameterizing `HigherOrder.lean`'s identifier layer over an extra
operations summand would rewrite that module and every consumer of the
higher-order system, while the mirror is confined to this module. `MrecShape`
carries no flat-recurrence dependence and is reused as is. `dstrCaseSig` sits at the same injection
position — after the application summand — in both `defnSigO` and
`higherOrderO`'s signature, so the two signatures' injections stay parallel
(as `defnSig`'s do with `higherOrder`'s). The signature layer (`defnSigO`
through `identConstSigO`) is generic in `A` with the `Fintype A.B` instance
threaded through; the model layer (`defnModelO` through `RMRecCatO`) is
`natAlgSig`-scoped, following `dstrCaseModel`'s scoping — a generic
interpretation of the case operation would require an enumeration of `A.B` to
order the branches, which `Fintype` does not provide constructively.

## References

D. Leivant, "Ramified recurrence and computational complexity III: Higher type
recurrence and elementary complexity", Annals of Pure and Applied Logic 96
(1999) 209-229, DOI `10.1016/S0168-0072(98)00040-2`. The destructor and case
operations of the object-sorted recurrence class `RRec_o` are section 2.5 (the
destructors of type `o → o`; the case operation `case^θ : o, θ^k → θ` with `k`
the number of constructors); their reduction rules — a destructor returns the
`j`-th subterm, or the argument itself when `j` reaches the arity — are section
4.1; the containment `RRec_o ⊆ RRec` (the case and destructor functions are
definable by flat recurrence) is the trivial direction of Lemma 1. The
object-sorted systems `RRec_o^omega` / `RMRec_o^omega` — flat recurrence
replaced by the destructor and case functions — are defined in section 2.5;
`higherOrderO` transcribes their term signature.

## Tags

ramified recurrence, destructor, case, flat recurrence, definability, object
sort, presentation, syntactic category
-/

namespace GebLean.Ramified

open CategoryTheory

/-- The standard `Fintype` structure on the constructor labels of the `1 + X`
word algebra `natAlgSig`, its labels being `Bool`. Supplies the finite counts
`natAlgSig.numCtors` and `natAlgSig.maxArity`. -/
instance instFintypeNatAlgSigB : Fintype natAlgSig.B := (inferInstance : Fintype Bool)

/-- The number of constructor labels of a finite free-algebra signature: the
cardinality of `A.B`. The count `k` of case branches of `case^θ`
(Leivant III section 2.5). -/
def AlgSig.numCtors (A : AlgSig) [Fintype A.B] : Nat := Fintype.card A.B

/-- The largest arity of a finite free-algebra signature: the supremum of the
constructor arities. The destructor family `dstr_j : o → o` runs over
`j < A.maxArity` (Leivant III section 2.5). -/
def AlgSig.maxArity (A : AlgSig) [Fintype A.B] : Nat := Finset.univ.sup A.ar

/-- Leivant III section 2.5's destructor/case operations, as a `SortedSig`
summand generic in a finite free-algebra signature `A`: the destructors
`dstr_j : o → o` indexed by `Fin A.maxArity`, and, at each object sort `θ`
(a sort satisfying `IsObj`), a case operation `case^θ : o, θ^k → θ` with `k`
the number of constructors `A.numCtors`, its arity placing the recurrence
argument at `o` first and the `k` branches at `θ` after. Novel packaging. -/
def dstrCaseSig (A : AlgSig) [Fintype A.B] (IsObj : RType → Prop) : SortedSig RType where
  Op := Fin A.maxArity ⊕ { θ : RType // IsObj θ }
  arity := Sum.elim (fun _ => [RType.o])
    (fun θ => RType.o :: List.replicate A.numCtors θ.val)
  result := Sum.elim (fun _ => RType.o) (fun θ => θ.val)

/-- The single hole of the case realization: the case function `ramCase θ` at
its own context `[θ, θ, o]` (branches first, recurrence argument last). -/
def caseHoleIdx (θ : RType) : Fin 1 → List RType × RType :=
  Function.const _ ([θ, θ, RType.o], θ)

/-- The realization of `case^θ : o, θ, θ → θ` over `natAlgSig` as a derived
identifier (Leivant III Lemma 1, containment direction): the explicit
definition at context `[o, θ, θ]` whose body applies the case function
`ramCase θ` (hole `0`, at context `[θ, θ, o]`) to the two branch variables and
then the recurrence-argument variable, reordering the recurrence argument from
first to last. Novel packaging. -/
def dstrCaseFlatCase (θ : RType) : RIdent natAlgSig [RType.o, θ, θ] θ :=
  RIdent.defn ⟨1, caseHoleIdx θ,
    Tm.op (sig := defnSig natAlgSig 1 (caseHoleIdx θ)) (Sum.inl (Sum.inr (0 : Fin 1)))
      (Fin.cons (Tm.var 1) (Fin.cons (Tm.var 2) (Fin.cons (Tm.var 0) finZeroElim)))⟩
    (fun _ => ramCase θ)

/-- Leivant III Lemma 1's containment direction `RRec_o ⊆ RRec`: each
`dstrCaseSig natAlgSig` operation realized as a derived identifier of
`higherOrder natAlgSig` by flat recurrence. Over `natAlgSig` the destructor
family is the single predecessor `ramDstr` (the arities are `≤ 1`); the case
operation `case^θ` is `dstrCaseFlatCase θ`, the reorder wrapper around the case
function `ramCase θ`. Novel packaging. -/
def dstrCaseToFlat (op : (dstrCaseSig natAlgSig RType.IsObj).Op) :
    RIdent natAlgSig ((dstrCaseSig natAlgSig RType.IsObj).arity op)
      ((dstrCaseSig natAlgSig RType.IsObj).result op) :=
  match op with
  | Sum.inl _j => ramDstr
  | Sum.inr θ => dstrCaseFlatCase θ.val

/-- The case operation's carrier-level semantics (Leivant III section 4.1): on
a recurrence argument `z` and two branches `y₀`, `y₁` it returns the branch of
`z`'s top constructor, `y₀` at the nullary constructor and `y₁` at the unary
constructor. Realized by `FreeAlg.recurse` reading the top label. -/
def caseSelect {C : Type} (z : FreeAlg natAlgSig) (y0 y1 : C) : C :=
  FreeAlg.recurse (A := natAlgSig) (P := Unit) (fun b _ _ _ => cond b y1 y0) () z

/-- The destructor's carrier-level semantics (Leivant III section 4.1): on a
recurrence argument `z` the destructor `dstr_j` returns the `j`-th subterm of
`z`'s top constructor when `j` is below its arity, and the argument `z` itself
otherwise. Realized by `FreeAlg.recurse` reading the top constructor's
subterms. -/
def dstrRead (j : Nat) (z : FreeAlg natAlgSig) : FreeAlg natAlgSig :=
  FreeAlg.recurse (A := natAlgSig) (P := Unit)
    (fun b _ sub _rec => if h : j < natAlgSig.ar b then sub ⟨j, h⟩ else FreeAlg.mk b sub) () z

/-- The case operation's standard semantics at the concrete context `[o, θ, θ]`:
`caseSelect` on the recurrence argument (position `0`) and the two branches
(positions `1`, `2`). -/
def dstrCaseModelCase (θ : RType)
    (args : ∀ i : Fin ([RType.o, θ, θ] : Ctx RType).length,
      RType.interp (FreeAlg natAlgSig) (([RType.o, θ, θ] : Ctx RType).get i)) :
    RType.interp (FreeAlg natAlgSig) θ :=
  caseSelect (args 0) (args 1) (args 2)

/-- The destructor's standard semantics at the concrete context `[o]`:
`dstrRead j` on the sole recurrence argument. -/
def dstrCaseModelDstr (j : Nat)
    (args : ∀ i : Fin ([RType.o] : Ctx RType).length,
      RType.interp (FreeAlg natAlgSig) (([RType.o] : Ctx RType).get i)) :
    RType.interp (FreeAlg natAlgSig) RType.o :=
  dstrRead j (args 0)

/-- Leivant III section 4.1's standard semantics of the destructor/case
operations over `natAlgSig`: a destructor `dstr_j` reads the `j`-th subterm of
the recurrence argument (the argument itself when `j` reaches the arity), and
the case operation `case^θ` selects the branch of the argument's main
constructor. Novel packaging. -/
def dstrCaseModel (op : (dstrCaseSig natAlgSig RType.IsObj).Op)
    (args : ∀ i : Fin ((dstrCaseSig natAlgSig RType.IsObj).arity op).length,
      RType.interp (FreeAlg natAlgSig) (((dstrCaseSig natAlgSig RType.IsObj).arity op).get i)) :
    RType.interp (FreeAlg natAlgSig) ((dstrCaseSig natAlgSig RType.IsObj).result op) :=
  match op, args with
  | Sum.inl j, args => dstrCaseModelDstr j.val args
  | Sum.inr θ, args => dstrCaseModelCase θ.val args

/-- The case semantics agrees with the case function on the reordered
environment: `caseSelect z y₀ y₁` is the denotation of `ramCase θ` on the
environment `(y₀, y₁, z)`. -/
theorem caseSelect_eq (θ : RType) (z : FreeAlg natAlgSig)
    (y0 y1 : RType.interp (FreeAlg natAlgSig) θ) :
    caseSelect z y0 y1 = (ramCase θ).interp (caseEnv θ y0 y1 z) := by
  cases z with
  | mk _ b subs =>
    change caseSelect (FreeAlg.mk b subs) y0 y1
      = (ramCase θ).interp (caseEnv θ y0 y1 (FreeAlg.mk b subs))
    rw [ramCase_interp θ y0 y1 b subs]; rfl

/-- The destructor semantics at index `0` agrees with the predecessor
`ramDstr`: `dstrRead 0 z` is the denotation of `ramDstr` on the environment of
`z`. -/
theorem dstrRead_zero_eq (z : FreeAlg natAlgSig) :
    dstrRead 0 z = ramDstr.interp (dstrEnv z) := by
  cases z with
  | mk _ b subs => cases b with
    | false =>
      change dstrRead 0 (FreeAlg.mk false subs)
        = ramDstr.interp (dstrEnv (FreeAlg.mk false subs))
      rw [ramDstr_interp_zero]
      exact congrArg (FreeAlg.mk (A := natAlgSig) false) (funext (fun i => i.elim0))
    | true =>
      change dstrRead 0 (FreeAlg.mk true subs)
        = ramDstr.interp (dstrEnv (FreeAlg.mk true subs))
      rw [ramDstr_interp_succ]; rfl

/-- The case realization denotes the case semantics: the derived identifier
`dstrCaseFlatCase θ` at an environment `args` denotes `caseSelect` of its three
entries. The explicit definition unfolds to `ramCase θ` on the reordered
environment, matched to `caseEnv` pointwise, then discharged by
`caseSelect_eq`. -/
theorem dstrCaseFlatCase_interp (θ : RType)
    (args : ∀ i : Fin ([RType.o, θ, θ] : Ctx RType).length,
      RType.interp (FreeAlg natAlgSig) (([RType.o, θ, θ] : Ctx RType).get i)) :
    (dstrCaseFlatCase θ).interp args = caseSelect (args 0) (args 1) (args 2) := by
  rw [caseSelect_eq]
  refine congrArg (ramCase θ).interp (funext (fun e => ?_))
  induction e using Fin.cases with
  | zero => rfl
  | succ e' => induction e' using Fin.cases with
    | zero => rfl
    | succ e'' => induction e'' using Fin.cases with
      | zero => rfl
      | succ e3 => exact e3.elim0

/-- The destructor realization denotes the destructor semantics at index `0`:
`ramDstr` at an environment `args` denotes `dstrRead 0` of its sole entry.
Reduces `ramDstr` to the environment of `args 0` and applies
`dstrRead_zero_eq`. -/
theorem dstrAgree
    (args : ∀ i : Fin ([RType.o] : Ctx RType).length,
      RType.interp (FreeAlg natAlgSig) (([RType.o] : Ctx RType).get i)) :
    ramDstr.interp args = dstrRead 0 (args 0) := by
  rw [dstrRead_zero_eq]
  refine congrArg ramDstr.interp (funext (fun i => ?_))
  induction i using Fin.cases with
  | zero => rfl
  | succ k => exact k.elim0

/-- Leivant III Lemma 1's containment direction: the flat realization agrees
with the standard semantics — `(dstrCaseToFlat op).interp` equals
`dstrCaseModel op` on every environment. The destructor arm uses
`Fin A.maxArity = Fin 1` to fix the index to `0` and applies `dstrAgree`; the
case arm applies `dstrCaseFlatCase_interp`. -/
theorem dstrCaseToFlat_interp (op : (dstrCaseSig natAlgSig RType.IsObj).Op)
    (args : ∀ i : Fin ((dstrCaseSig natAlgSig RType.IsObj).arity op).length,
      RType.interp (FreeAlg natAlgSig)
        (((dstrCaseSig natAlgSig RType.IsObj).arity op).get i)) :
    (dstrCaseToFlat op).interp args = dstrCaseModel op args := by
  match op, args with
  | Sum.inl j, args =>
    have hj : j.val = 0 := by have h : j.val < 1 := j.isLt; omega
    change ramDstr.interp args = dstrCaseModelDstr j.val args
    rw [hj]
    exact dstrAgree args
  | Sum.inr θ, args => exact dstrCaseFlatCase_interp θ.val args

/-- The base signature of an O-variant explicit definition's body (Leivant III
section 2.5, the object-sorted systems: flat recurrence is replaced by the
destructor and case functions): the constructor summand, application, the
destructor/case operations, the saturated holes for previously defined
identifiers, and their curried-combinator forms. `defnSig`'s summands
(`GebLean/Ramified/HigherOrder.lean`) with `dstrCaseSig` inserted after the
application summand; the same injection position is used in `higherOrderO`.
Novel packaging. -/
def defnSigO (A : AlgSig) [Fintype A.B] (n : Nat)
    (holeIdx : Fin n → List RType × RType) : SortedSig RType :=
  ((((constructorSig A RType.IsObj).sum appSig).sum (dstrCaseSig A RType.IsObj)).sum
    (holeSig n holeIdx)).sum (holeConstSig n holeIdx)

/-- The non-recursive data of an O-variant explicit definition (Leivant III
sections 2.3 and 2.5): a defining term over the base signature extended by the
destructor/case operations and by hole operations, one hole per occurrence of
a previously defined identifier. The directions of the fixed point are the
identifiers those holes reference. Novel packaging. -/
structure DefnShapeO (A : AlgSig) [Fintype A.B] (Γ : List RType) (τ : RType) where
  /-- The number of identifier holes in the body. -/
  numHoles : Nat
  /-- The context and result sort each hole's referenced identifier carries. -/
  holeIdx : Fin numHoles → List RType × RType
  /-- The defining term over the base signature with destructors, case
  operations, and holes, in context `Γ` at sort `τ`. -/
  body : Tm (defnSigO A numHoles holeIdx) Γ τ

/-- The shape type of the O-variant identifier signature endofunctor at index
`(Γ, τ)`: the disjoint union of the two schema formers' non-recursive data —
explicit definition and ramified monotonic recurrence. Flat recurrence is
absent (Leivant III section 2.5: the destructor and case functions replace
it); the recurrence data `MrecShape` is reused from
`GebLean/Ramified/HigherOrder.lean`. Novel packaging. -/
def IdentShapeO (A : AlgSig) [Fintype A.B] (Γ : List RType) (τ : RType) : Type :=
  DefnShapeO A Γ τ ⊕ MrecShape A Γ τ

/-- The direction type at an O-variant shape: the holes of a `defn`, and the
constructor labels of a `mrec` (one step function per label). Novel
packaging. -/
def IdentDirO (A : AlgSig) [Fintype A.B] (Γ : List RType) (τ : RType) :
    IdentShapeO A Γ τ → Type
  | Sum.inl d => Fin d.numHoles
  | Sum.inr _ => A.B

/-- The target index of an O-variant direction: the context and result sort of
the referenced identifier. A `defn` hole targets its stored index; a `mrec`
step function targets `(params ++ replicate (A.ar i) τ, τ)` (parameters and
recursive results at `τ`). Novel packaging. -/
def identTargetO (A : AlgSig) [Fintype A.B] (Γ : List RType) (τ : RType) :
    (s : IdentShapeO A Γ τ) → IdentDirO A Γ τ s → List RType × RType
  | Sum.inl d, j => d.holeIdx j
  | Sum.inr m, i => (m.params ++ List.replicate (A.ar i) τ, τ)

/-- The O-variant identifier signature endofunctor over the index type
`List RType × RType` (context, result sort): shapes are the schema formers'
data, directions are the referenced identifiers. Novel packaging. -/
def identEndoO (A : AlgSig) [Fintype A.B] : PolyEndo (List RType × RType) :=
  fun idx => ccrObjMk fun s : IdentShapeO A idx.1 idx.2 =>
    Over.mk fun d : IdentDirO A idx.1 idx.2 s => identTargetO A idx.1 idx.2 s d

/-- The schema-generated identifiers of the O-variant over a base algebra `A`,
indexed by context and result sort (Leivant III section 2.5, the object-sorted
systems `RRec_o^omega` / `RMRec_o^omega`): explicit definitions — over a body
signature carrying the destructor and case operations — and ramified monotonic
recurrences (eq. (4)) over previously defined identifiers; flat recurrence is
absent. Realized as the `PolyFix` W-type of the indexed signature endofunctor
`identEndoO A`, mirroring `RIdent`. Novel packaging. -/
def RIdentO (A : AlgSig) [Fintype A.B] (Γ : List RType) (τ : RType) : Type :=
  PolyFix (identEndoO A) (Γ, τ)

/-- An O-variant explicit definition (Leivant III sections 2.3 and 2.5): the
defining term `d` together with the referenced identifiers filling its holes.
Novel packaging. -/
def RIdentO.defn {A : AlgSig} [Fintype A.B] {Γ : List RType} {τ : RType}
    (d : DefnShapeO A Γ τ)
    (children : (j : Fin d.numHoles) → RIdentO A (d.holeIdx j).1 (d.holeIdx j).2) :
    RIdentO A Γ τ :=
  PolyFix.mk (Γ, τ) (Sum.inl d) children

/-- An O-variant ramified monotonic recurrence (Leivant III section 2.3,
eq. (4), retained by the object-sorted systems of section 2.5): with
parameters `x_vec` of sorts `params` and recurrence argument at `Ω τ`, and one
step function per constructor of `A`,
`f (x_vec, c_i (a_vec)) = g_ci (x_vec, phi_vec)`, where `phi_j = f (x_vec, a_j)`
are the recursive results. Novel packaging. -/
def RIdentO.mrec {A : AlgSig} [Fintype A.B] (params : List RType) (τ : RType)
    (steps : (i : A.B) → RIdentO A (params ++ List.replicate (A.ar i) τ) τ) :
    RIdentO A (params ++ [RType.omega τ]) τ :=
  PolyFix.mk (params ++ [RType.omega τ], τ) (Sum.inr ⟨params, rfl⟩)
    (fun i => steps i)

/-- The model interpreting an O-variant explicit definition's body over
`natAlgSig`: the standard carriers, with constructors and application read as
usual, the destructor and case operations by their standard semantics
`dstrCaseModel` (Leivant III section 4.1), each saturated hole by the recursive
result of the referenced identifier, and each curried hole by the currying
(`curryInterp`) of that recursive result. Scoped to `natAlgSig` because
`dstrCaseModel` is. Novel packaging. -/
def defnModelO (n : Nat) (holeIdx : Fin n → List RType × RType)
    (ih : ∀ j : Fin n,
      (∀ i : Fin (holeIdx j).1.length,
        RType.interp (FreeAlg natAlgSig) ((holeIdx j).1.get i)) →
        RType.interp (FreeAlg natAlgSig) (holeIdx j).2) :
    SortedModel (defnSigO natAlgSig n holeIdx) where
  carrier := RType.interp (FreeAlg natAlgSig)
  interpOp op args :=
    match op with
    | Sum.inl (Sum.inl (Sum.inl (Sum.inl cop))) => stdConstructorInterp natAlgSig cop args
    | Sum.inl (Sum.inl (Sum.inl (Sum.inr aop))) => stdAppInterp natAlgSig aop args
    | Sum.inl (Sum.inl (Sum.inr dop)) => dstrCaseModel dop args
    | Sum.inl (Sum.inr j) => ih j args
    | Sum.inr j => curryInterp natAlgSig (holeIdx j).1 (holeIdx j).2 (ih j)

/-- The recursion step of `RIdentO.interp` at one identifier node: a `defn`
folds its body against `defnModelO`; a `mrec` recurses on the recurrence
argument with the monotonic step (parameters and recursive results). Novel
packaging. -/
def RIdentO.interpStep (Γ : List RType) (τ : RType)
    (shape : IdentShapeO natAlgSig Γ τ)
    (ih : ∀ d : IdentDirO natAlgSig Γ τ shape,
      (∀ i : Fin (identTargetO natAlgSig Γ τ shape d).1.length,
        RType.interp (FreeAlg natAlgSig)
          ((identTargetO natAlgSig Γ τ shape d).1.get i)) →
        RType.interp (FreeAlg natAlgSig) (identTargetO natAlgSig Γ τ shape d).2) :
    (∀ i : Fin Γ.length, RType.interp (FreeAlg natAlgSig) (Γ.get i)) →
      RType.interp (FreeAlg natAlgSig) τ := by
  rcases shape with d | ⟨params, rfl⟩
  · exact fun ρ => d.body.eval (defnModelO d.numHoles d.holeIdx ih) ρ
  · exact fun ρ =>
      FreeAlg.recurse (A := natAlgSig) (P := Unit)
        (fun i _ _sub phi =>
          ih i (childEnv params τ (natAlgSig.ar i)
            (envHead params (RType.omega τ) ρ) phi))
        () (envLast params (RType.omega τ) ρ)

/-- The denotation of an O-variant identifier over the standard carriers
`RType.interp (FreeAlg natAlgSig)`: a function from an environment at the
identifier's context to a value at its result sort. Realized by structural
recursion via `PolyFix.ind`, mirroring `RIdent.interp`
(`GebLean/Ramified/HigherOrder.lean`). Novel packaging. -/
def RIdentO.interp {Γ : List RType} {τ : RType} (f : RIdentO natAlgSig Γ τ) :
    (∀ i : Fin Γ.length, RType.interp (FreeAlg natAlgSig) (Γ.get i)) →
      RType.interp (FreeAlg natAlgSig) τ :=
  PolyFix.ind (P := identEndoO natAlgSig)
    (motive := fun {x} _ =>
      (∀ i : Fin x.1.length, RType.interp (FreeAlg natAlgSig) (x.1.get i)) →
        RType.interp (FreeAlg natAlgSig) x.2)
    (fun {x} shape _children ih => RIdentO.interpStep x.1 x.2 shape ih) f

/-- The saturated identifier summand of the O-variant presentation: operations
are the O-variant schema-generated identifiers, of context as arity and result
sort as result. Mirrors `identSig`. Novel packaging. -/
def identSigO (A : AlgSig) [Fintype A.B] : SortedSig RType where
  Op := Σ Γ : List RType, Σ τ : RType, RIdentO A Γ τ
  arity op := op.1
  result op := op.2.1

/-- The identifier-constant summand of the O-variant presentation: one nullary
operation per O-variant identifier `f : RIdentO A Γ τ`, with result the
curried arrow sort `RType.curried Γ τ` — the identifiers-as-combinators
reading (Leivant III section 2.3, the higher-order system). Mirrors
`identConstSig`. Novel packaging. -/
def identConstSigO (A : AlgSig) [Fintype A.B] : SortedSig RType where
  Op := Σ Γ : List RType, Σ τ : RType, RIdentO A Γ τ
  arity _op := []
  result op := RType.curried op.1 op.2.1

/-- The standard model of the O-variant presentation over `natAlgSig`: the
standard carriers, with constructors and application read as usual, the
destructor and case operations by `dstrCaseModel` (Leivant III section 4.1),
each saturated identifier by its own denotation, and each identifier constant
by the currying of that denotation. Novel packaging. -/
def higherOrderModelO :
    SortedModel
      (((((constructorSig natAlgSig RType.IsObj).sum appSig).sum
        (dstrCaseSig natAlgSig RType.IsObj)).sum (identSigO natAlgSig)).sum
        (identConstSigO natAlgSig)) where
  carrier := RType.interp (FreeAlg natAlgSig)
  interpOp op args :=
    match op with
    | Sum.inl (Sum.inl (Sum.inl (Sum.inl cop))) => stdConstructorInterp natAlgSig cop args
    | Sum.inl (Sum.inl (Sum.inl (Sum.inr aop))) => stdAppInterp natAlgSig aop args
    | Sum.inl (Sum.inl (Sum.inr dop)) => dstrCaseModel dop args
    | Sum.inl (Sum.inr iop) => iop.2.2.interp args
    | Sum.inr icop => curryInterp natAlgSig icop.1 icop.2.1 icop.2.2.interp

/-- The O-variant presentation over `natAlgSig` (Leivant III section 2.5, the
object-sorted systems `RRec_o^omega` / `RMRec_o^omega`, in which flat
recurrence is replaced by the destructor and case functions): the constructor
summand at every object sort, application, the destructor/case operations, the
O-variant schema-generated identifiers as saturated operations, and their
nullary constants at the curried arrow sorts, summed by `SortedSig.sum`, with
the standard model interpreting each operation over the standard carriers.
Mirrors `higherOrder` with the destructor/case summand added and flat
recurrence removed from the identifier schema. Novel packaging. -/
def higherOrderO : Presentation where
  S := RType
  sig :=
    ((((constructorSig natAlgSig RType.IsObj).sum appSig).sum
      (dstrCaseSig natAlgSig RType.IsObj)).sum (identSigO natAlgSig)).sum
      (identConstSigO natAlgSig)
  IsObj := RType.IsObj
  alg := natAlgSig
  std := higherOrderModelO

/-- The syntactic category of the O-variant system over `natAlgSig`: the
generic syntactic category of `higherOrderO` under interpretative equality at
the standard model. The Phase 1 `Category` and `CartesianMonoidalCategory`
instances of `SynCat` apply. Novel packaging. -/
abbrev RMRecCatO := SynCat higherOrderO (interpQuotRel higherOrderO)

end GebLean.Ramified
