import GebLean.Ramified.Soundness.BarRep
import GebLean.Binding.Measures
import Mathlib.Algebra.BigOperators.Fin

/-!
# Ramified recurrence: the Lemma 12 normalization bound

The order measure `RType.ord` on ramified types, the redex-rank measure
`redexRank` on terms of the simply-typed calculus `1λ(A)`, and their role in
Lemma 12's normalization bound (Leivant III section 4.2, p. 224), the last step
of the soundness development bounding the length of the reduction path of a
bar-translated term (`GebLean/Ramified/Soundness/BarRep.lean`).

The order layer `RType.ord` measures the arrow-nesting depth of an r-type,
ignoring `Omega` shifts (decision P1: the totalization choice
`ord (Ω τ) = ord τ`, novel packaging — Leivant's order measure is stated only
on the simple types the bar-translation produces, and `Omega` never appears in
a simple type; extending `ord` over all of `RType` by ignoring `Omega` lets
later development state the bound uniformly without a simplicity side condition
on every occurrence).

The redex layer detects the genuine redexes of `1λ(A)` (Leivant III section 4.2,
p. 224) by Bool-valued structural recursion and measures each. A node is a
genuine redex only when it is a β-redex `app' (lam' b) N`, a saturated
destructor application `dstr j` over a `con`-headed sort-`o` argument, or a
saturated case spine over a `con`-headed scrutinee. For sort-`o` terms,
`con`-headedness implies saturation by the intrinsic sorts (section 4.3's
head-form observation), which is what makes Bool-valued structural detection
sufficient. Following the p. 224 subtlety that ι-redexes count rank exactly `1`
while the cycle machinery reads only the β-rank, the aggregate `redexRank`
splits into `betaRedexRank` and `hasIota`.

## Main definitions

* `RType.ord` — the order of an r-type: `ord o = 0`,
  `ord (τ → σ) = max (1 + ord τ) (ord σ)`, `ord (Ω τ) = ord τ`.
* `OneLambda.conHeaded` — the head of the application spine is a `con`.
* `OneLambda.topBetaRank` — the order of the applied abstraction's arrow sort
  if the node is a β-redex, else `0`.
* `OneLambda.iotaSpine` — the node's function spine bottoms out at a destructor
  or case head over a `con`-headed scrutinee, ignoring saturation.
* `OneLambda.topIota` — the node is a saturated destructor- or case-redex over
  a `con`-headed scrutinee: `iotaSpine` restricted to result sort `o`.
* `OneLambda.IsLam` — the node is a `lam` operation.
* `OneLambda.betaRedexRank` — the maximum of `topBetaRank` over all subterm
  positions.
* `OneLambda.hasIota` — some subterm position is an ι-redex.
* `OneLambda.redexRank` — the aggregate `max (betaRedexRank t) (if hasIota t
  then 1 else 0)`.
* `OneLambda.Normal` — `redexRank t = 0`.

## Main statements

* `RType.one_le_ord_arrow` — every arrow type has order at least `1`.
* `OneLambda.size_app'`, `OneLambda.height_app'`, `OneLambda.size_lam'`,
  `OneLambda.height_lam'` — the measure equations at the application and
  abstraction combinators.
* `OneLambda.betaRedexRank_le_redexRank` — the β-rank bounds the aggregate rank.
* `OneLambda.normal_iff` — a term is normal iff it has β-rank `0` and no
  ι-redex.
* `OneLambda.redexRank_app'` — the aggregate rank of an application in terms of
  the ranks of its subterms and the top detectors.

## References

D. Leivant, "Ramified recurrence and computational complexity III: Higher
type recurrence and elementary complexity", Annals of Pure and Applied
Logic 96 (1999) 209-229, DOI `10.1016/S0168-0072(98)00040-2`, section 2.2
(p. 213): the order of a simple type; section 4.2 (p. 224): the redexes, their
ranks, and normality of `1λ(A)`.

## Tags

ramified recurrence, order, redex, redex rank, normal form, normalization,
simply-typed lambda calculus
-/

namespace GebLean.Ramified

/-- The order of an r-type (Leivant III section 2.2, p. 213): `ord o = 0`,
`ord (τ → σ) = max (1 + ord τ) (ord σ)`. The `Omega` clause `ord (Ω τ) = ord
τ` is decision P1's totalization choice, ignoring the shift since Leivant's
order measure is stated only on the `Omega`-free simple types. Realized by
the dependent eliminator `PolyFix.ind` (decision 8), following `barTy`'s
pattern (`GebLean/Ramified/Soundness/BarRep.lean`). -/
def RType.ord (τ : RType) : ℕ :=
  PolyFix.ind (P := rTypeSig.polyEndo) (motive := fun {_} _ => ℕ)
    (fun i childx ih =>
      match i, childx, ih with
      | RTypeShape.o, _, _ => 0
      | RTypeShape.arrow, _, ih =>
        max (ih (⟨0, by decide⟩ : Fin (rTypeSig.ar RTypeShape.arrow)) + 1)
          (ih (⟨1, by decide⟩ : Fin (rTypeSig.ar RTypeShape.arrow)))
      | RTypeShape.omega, _, ih =>
        ih (⟨0, by decide⟩ : Fin (rTypeSig.ar RTypeShape.omega))) τ

@[simp] theorem RType.ord_o : RType.o.ord = 0 := rfl

@[simp] theorem RType.ord_arrow (τ σ : RType) :
    (RType.arrow τ σ).ord = max (τ.ord + 1) σ.ord := rfl

@[simp] theorem RType.ord_omega (τ : RType) : (RType.omega τ).ord = τ.ord := rfl

/-- Every arrow type has order at least `1` (Leivant III section 2.2, p. 213):
`ord (τ → σ) ≥ 1 + ord τ ≥ 1`. -/
theorem RType.one_le_ord_arrow (τ σ : RType) : 1 ≤ (RType.arrow τ σ).ord := by
  rw [RType.ord_arrow]
  omega

open GebLean.Binding

namespace OneLambda

variable {A : AlgSig} [Fintype A.B]

/-- The size ignores the `Γ ++ [] = Γ` context transport that `app'` applies to
its subterms; the single-transport specialization of `Tm.size_cast` matching the
shape produced by `app'`. -/
private theorem size_appendNil {Γ : Binding.Ctx RType} {s : RType}
    (t : Binding.Tm (oneLambdaSig A) Γ s) :
    ((List.append_nil Γ).symm ▸ t).size = t.size :=
  Binding.Tm.size_cast (List.append_nil Γ).symm rfl t

/-- The height counterpart of `size_appendNil`. -/
private theorem height_appendNil {Γ : Binding.Ctx RType} {s : RType}
    (t : Binding.Tm (oneLambdaSig A) Γ s) :
    ((List.append_nil Γ).symm ▸ t).height = t.height :=
  Binding.Tm.height_cast (List.append_nil Γ).symm rfl t

/-- The node count of an application node: the node plus its function and
argument subterms. From `Tm.size_op`, folding the length-two argument tuple with
`Fin.sum_univ_two` and discharging the `Γ ++ [] = Γ` transports of `app'` by
`size_appendNil`. The `change` steps reduce the length index and the
`Fin.cases`-selected children by definitional unfolding, sidestepping the stuck
`List.length` that blocks syntactic rewriting. -/
@[simp] theorem size_app' {Γ : Binding.Ctx RType} {σ τ : RType}
    (f : Binding.Tm (oneLambdaSig A) Γ (RType.arrow σ τ))
    (x : Binding.Tm (oneLambdaSig A) Γ σ) :
    (app' f x).size = 1 + f.size + x.size := by
  refine (Binding.Tm.size_op (S := oneLambdaSig A) (Γ := Γ) (OneLambdaOp.app σ τ)
    (fun j => Fin.cases ((List.append_nil Γ).symm ▸ f)
      (fun k => Fin.cases ((List.append_nil Γ).symm ▸ x) (fun l => l.elim0) k) j)).trans ?_
  change (1 : ℕ) + ∑ _j : Fin 2, _ = _
  rw [Fin.sum_univ_two]
  change (1 : ℕ) + (((List.append_nil Γ).symm ▸ f).size + ((List.append_nil Γ).symm ▸ x).size) = _
  rw [size_appendNil, size_appendNil]
  omega

/-- The tree height of an application node: one above the maximum of its function
and argument subterms. From `Tm.height_op`, folding the length-two argument tuple
and discharging the `app'` transports by `height_appendNil`. -/
@[simp] theorem height_app' {Γ : Binding.Ctx RType} {σ τ : RType}
    (f : Binding.Tm (oneLambdaSig A) Γ (RType.arrow σ τ))
    (x : Binding.Tm (oneLambdaSig A) Γ σ) :
    (app' f x).height = 1 + max f.height x.height := by
  refine (Binding.Tm.height_op (S := oneLambdaSig A) (Γ := Γ) (OneLambdaOp.app σ τ)
    (fun j => Fin.cases ((List.append_nil Γ).symm ▸ f)
      (fun k => Fin.cases ((List.append_nil Γ).symm ▸ x) (fun l => l.elim0) k) j)).trans ?_
  change (1 : ℕ) + (Finset.univ : Finset (Fin 2)).sup _ = _
  rw [show (Finset.univ : Finset (Fin 2)) = {0, 1} from rfl, Finset.sup_insert,
    Finset.sup_singleton]
  change (1 : ℕ) + (((List.append_nil Γ).symm ▸ f).height ⊔ ((List.append_nil Γ).symm ▸ x).height)
    = _
  rw [height_appendNil, height_appendNil]

/-- The node count of an abstraction node: the node plus its body subterm. -/
@[simp] theorem size_lam' {Γ : Binding.Ctx RType} {σ τ : RType}
    (b : Binding.Tm (oneLambdaSig A) (Γ ++ [σ]) τ) :
    (lam' b).size = 1 + b.size := by
  refine (Binding.Tm.size_op (S := oneLambdaSig A) (Γ := Γ) (OneLambdaOp.lam σ τ)
    (fun j => Fin.cases b (fun k => k.elim0) j)).trans ?_
  change (1 : ℕ) + ∑ _j : Fin 1, _ = _
  rw [Fin.sum_univ_one]
  rfl

/-- The tree height of an abstraction node: one above its body subterm. -/
@[simp] theorem height_lam' {Γ : Binding.Ctx RType} {σ τ : RType}
    (b : Binding.Tm (oneLambdaSig A) (Γ ++ [σ]) τ) :
    (lam' b).height = 1 + b.height := by
  refine (Binding.Tm.height_op (S := oneLambdaSig A) (Γ := Γ) (OneLambdaOp.lam σ τ)
    (fun j => Fin.cases b (fun k => k.elim0) j)).trans ?_
  change (1 : ℕ) + (Finset.univ : Finset (Fin 1)).sup _ = _
  rw [show (Finset.univ : Finset (Fin 1)) = {0} from rfl, Finset.sup_singleton]
  rfl

/-- The head operation of a term: `some o` at an operation node `o`, `none` at a
variable. A non-recursive read of the top `PolyFix` node by `PolyFix.ind`
(decision 8), following the operation-directed dispatch of `barTm`
(`GebLean/Ramified/Soundness/BarRep.lean`). Novel packaging. -/
def headTag {Γ : Binding.Ctx RType} {s : RType}
    (t : Binding.Tm (oneLambdaSig A) Γ s) : Option (OneLambdaOp A) :=
  PolyFix.ind (P := polyTranslate Binding.varOver (oneLambdaSig A).polyEndo)
    (motive := fun {_} _ => Option (OneLambdaOp A))
    (fun i children ih =>
      match i, children, ih with
      | Sum.inl _, _, _ => none
      | Sum.inr p, _, _ => some p.val) t

/-- `headTag` at an operation node is that operation. -/
@[simp] theorem headTag_op {Γ : Binding.Ctx RType} (o : OneLambdaOp A)
    (args : ∀ j : Fin ((oneLambdaSig A).args o).length,
      Binding.Tm (oneLambdaSig A) (Γ ++ (((oneLambdaSig A).args o).get j).1)
        (((oneLambdaSig A).args o).get j).2) :
    headTag (Binding.Tm.op o args) = some o := rfl

/-- `headTag` at a variable is `none`. -/
@[simp] theorem headTag_var {Γ : Binding.Ctx RType} {s : RType} (x : Binding.Var Γ s) :
    headTag (Binding.Tm.var x : Binding.Tm (oneLambdaSig A) Γ s) = none := by
  obtain ⟨i, hi⟩ := x; subst hi; rfl

/-- `headTag` is invariant under transport of the context and sort indices. -/
theorem headTag_cast {Γ Γ' : Binding.Ctx RType} {s s' : RType}
    (hΓ : Γ = Γ') (hs : s = s') (t : Binding.Tm (oneLambdaSig A) Γ s) :
    headTag (hs ▸ hΓ ▸ t) = headTag t := by subst hΓ; subst hs; rfl

/-- `headTag` at an abstraction node is its `lam` operation. -/
@[simp] theorem headTag_lam' {Γ : Binding.Ctx RType} {σ τ : RType}
    (b : Binding.Tm (oneLambdaSig A) (Γ ++ [σ]) τ) :
    headTag (lam' b) = some (OneLambdaOp.lam σ τ) := rfl

/-- `headTag` at an application node is its `app` operation. -/
@[simp] theorem headTag_app' {Γ : Binding.Ctx RType} {σ τ : RType}
    (f : Binding.Tm (oneLambdaSig A) Γ (RType.arrow σ τ))
    (x : Binding.Tm (oneLambdaSig A) Γ σ) :
    headTag (app' f x) = some (OneLambdaOp.app σ τ) := rfl

/-- `headTag` ignores the `Γ ++ [] = Γ` transport that `app'` applies. -/
private theorem headTag_appendNil {Γ : Binding.Ctx RType} {s : RType}
    (t : Binding.Tm (oneLambdaSig A) Γ s) :
    headTag ((List.append_nil Γ).symm ▸ t) = headTag t :=
  headTag_cast (List.append_nil Γ).symm rfl t

/-- Whether the head operation of a term is a `lam` (any domain and codomain
sorts): the `Bool` core of `IsLam`. -/
def isLam {Γ : Binding.Ctx RType} {s : RType}
    (t : Binding.Tm (oneLambdaSig A) Γ s) : Bool :=
  match headTag t with
  | some (OneLambdaOp.lam _ _) => true
  | _ => false

/-- The node is an abstraction (Leivant III section 4.2): its head operation is
a `lam`. The `Prop`-valued predicate consumed by Task 6.3.6's shape invariant.
Transcription of section 4.2's abstraction head-form. -/
def IsLam {Γ : Binding.Ctx RType} {s : RType}
    (t : Binding.Tm (oneLambdaSig A) Γ s) : Prop := isLam t = true

/-- `isLam` is invariant under transport of the context and sort indices. -/
theorem isLam_cast {Γ Γ' : Binding.Ctx RType} {s s' : RType}
    (hΓ : Γ = Γ') (hs : s = s') (t : Binding.Tm (oneLambdaSig A) Γ s) :
    isLam (hs ▸ hΓ ▸ t) = isLam t := by subst hΓ; subst hs; rfl

/-- `isLam` ignores the `Γ ++ [] = Γ` transport that `app'` applies to its
subterms. -/
private theorem isLam_appendNil {Γ : Binding.Ctx RType} {s : RType}
    (t : Binding.Tm (oneLambdaSig A) Γ s) :
    isLam ((List.append_nil Γ).symm ▸ t) = isLam t := isLam_cast (List.append_nil Γ).symm rfl t

/-- `isLam` at an abstraction node is `true`. -/
@[simp] theorem isLam_lam' {Γ : Binding.Ctx RType} {σ τ : RType}
    (b : Binding.Tm (oneLambdaSig A) (Γ ++ [σ]) τ) : isLam (lam' b) = true := rfl

/-- `isLam` at an application node is `false`. -/
@[simp] theorem isLam_app' {Γ : Binding.Ctx RType} {σ τ : RType}
    (f : Binding.Tm (oneLambdaSig A) Γ (RType.arrow σ τ))
    (x : Binding.Tm (oneLambdaSig A) Γ σ) : isLam (app' f x) = false := rfl

/-- `isLam` at a variable is `false`. -/
@[simp] theorem isLam_var {Γ : Binding.Ctx RType} {s : RType} (x : Binding.Var Γ s) :
    isLam (Binding.Tm.var x : Binding.Tm (oneLambdaSig A) Γ s) = false := by
  simp only [isLam, headTag_var]

/-- The operation dispatch of `conHeaded`: `true` at a `con`, and at an `app`
the recursively-computed value on the function subterm; `false` otherwise. -/
def conHeadedOp (o : OneLambdaOp A) (rec : Fin ((oneLambdaSig A).args o).length → Bool) : Bool :=
  match o with
  | OneLambdaOp.con _ => true
  | OneLambdaOp.app _ _ => rec ⟨0, Nat.succ_pos 1⟩
  | _ => false

/-- Whether the head of the application spine is a `con` operation (Leivant III
section 4.2, p. 224): descending the function subterm of each `app` node, the
ultimate head is a constructor constant. The `con`-headedness test of a
sort-`o` scrutinee, where by section 4.3's head-form observation it implies
saturation. Structural recursion by `PolyFix.ind`; transcription of section
4.2's redex head-forms. -/
def conHeaded {Γ : Binding.Ctx RType} {s : RType}
    (t : Binding.Tm (oneLambdaSig A) Γ s) : Bool :=
  PolyFix.ind (P := polyTranslate Binding.varOver (oneLambdaSig A).polyEndo)
    (motive := fun {_} _ => Bool)
    (fun i children ih =>
      match i, children, ih with
      | Sum.inl _, _, _ => false
      | Sum.inr p, _, ih => conHeadedOp p.val (fun j => ih ⟨j⟩)) t

/-- `conHeaded` at an operation node dispatches through `conHeadedOp` on the
recursive values of its subterms. -/
@[simp] theorem conHeaded_op {Γ : Binding.Ctx RType} (o : OneLambdaOp A)
    (args : ∀ j : Fin ((oneLambdaSig A).args o).length,
      Binding.Tm (oneLambdaSig A) (Γ ++ (((oneLambdaSig A).args o).get j).1)
        (((oneLambdaSig A).args o).get j).2) :
    conHeaded (Binding.Tm.op o args) = conHeadedOp o (fun j => conHeaded (args j)) := rfl

/-- `conHeaded` at a variable is `false`. -/
@[simp] theorem conHeaded_var {Γ : Binding.Ctx RType} {s : RType} (x : Binding.Var Γ s) :
    conHeaded (Binding.Tm.var x : Binding.Tm (oneLambdaSig A) Γ s) = false := by
  obtain ⟨i, hi⟩ := x; subst hi; rfl

/-- `conHeaded` is invariant under transport of the context and sort indices. -/
theorem conHeaded_cast {Γ Γ' : Binding.Ctx RType} {s s' : RType}
    (hΓ : Γ = Γ') (hs : s = s') (t : Binding.Tm (oneLambdaSig A) Γ s) :
    conHeaded (hs ▸ hΓ ▸ t) = conHeaded t := by subst hΓ; subst hs; rfl

/-- `conHeaded` ignores the `Γ ++ [] = Γ` transport that `app'` applies. -/
private theorem conHeaded_appendNil {Γ : Binding.Ctx RType} {s : RType}
    (t : Binding.Tm (oneLambdaSig A) Γ s) :
    conHeaded ((List.append_nil Γ).symm ▸ t) = conHeaded t :=
  conHeaded_cast (List.append_nil Γ).symm rfl t

/-- `conHeaded` at an application node descends into the function subterm. -/
@[simp] theorem conHeaded_app' {Γ : Binding.Ctx RType} {σ τ : RType}
    (f : Binding.Tm (oneLambdaSig A) Γ (RType.arrow σ τ))
    (x : Binding.Tm (oneLambdaSig A) Γ σ) :
    conHeaded (app' f x) = conHeaded f := conHeaded_appendNil f

/-- The operation dispatch of `topBetaRank`: at an `app` whose function subterm
is an abstraction, the order of that abstraction's arrow sort; else `0`. -/
def topBetaRankOp {Γ : Binding.Ctx RType} (o : OneLambdaOp A)
    (children : ∀ j : Fin ((oneLambdaSig A).args o).length,
      Binding.Tm (oneLambdaSig A) (Γ ++ (((oneLambdaSig A).args o).get j).1)
        (((oneLambdaSig A).args o).get j).2) : ℕ :=
  match o with
  | OneLambdaOp.app σ τ =>
      if isLam (children ⟨0, Nat.succ_pos 1⟩) then RType.ord (RType.arrow σ τ) else 0
  | _ => 0

/-- The β-rank contributed at the top node (Leivant III section 4.2, p. 224):
`RType.ord` of the applied abstraction's arrow sort when the node is a β-redex
`app' (lam' b) N`, and `0` otherwise. A non-recursive read of the top node.
Transcription of section 4.2's redex rank. -/
def topBetaRank {Γ : Binding.Ctx RType} {s : RType}
    (t : Binding.Tm (oneLambdaSig A) Γ s) : ℕ :=
  PolyFix.ind (P := polyTranslate Binding.varOver (oneLambdaSig A).polyEndo)
    (motive := fun {_} _ => ℕ)
    (fun {x} i children ih =>
      match i, children, ih with
      | Sum.inl _, _, _ => 0
      | Sum.inr p, children, _ => topBetaRankOp (Γ := x.1) p.val (fun j => children ⟨j⟩)) t

/-- `topBetaRank` at an operation node is `topBetaRankOp` on its subterms. -/
@[simp] theorem topBetaRank_op {Γ : Binding.Ctx RType} (o : OneLambdaOp A)
    (args : ∀ j : Fin ((oneLambdaSig A).args o).length,
      Binding.Tm (oneLambdaSig A) (Γ ++ (((oneLambdaSig A).args o).get j).1)
        (((oneLambdaSig A).args o).get j).2) :
    topBetaRank (Binding.Tm.op o args) = topBetaRankOp o args := rfl

/-- `topBetaRank` at a variable is `0`. -/
@[simp] theorem topBetaRank_var {Γ : Binding.Ctx RType} {s : RType} (x : Binding.Var Γ s) :
    topBetaRank (Binding.Tm.var x : Binding.Tm (oneLambdaSig A) Γ s) = 0 := by
  obtain ⟨i, hi⟩ := x; subst hi; rfl

/-- `topBetaRank` at an application node is `RType.ord` of the arrow sort when the
function subterm is an abstraction, and `0` otherwise. -/
@[simp] theorem topBetaRank_app' {Γ : Binding.Ctx RType} {σ τ : RType}
    (f : Binding.Tm (oneLambdaSig A) Γ (RType.arrow σ τ))
    (x : Binding.Tm (oneLambdaSig A) Γ σ) :
    topBetaRank (app' f x) = if isLam f then RType.ord (RType.arrow σ τ) else 0 := by
  change (if isLam ((List.append_nil Γ).symm ▸ f) then RType.ord (RType.arrow σ τ) else 0) = _
  rw [isLam_appendNil]

/-- The operation dispatch of `iotaSpine`: at an `app` node, inspecting the head
of the function subterm — a `dstr` or a `case` gives the `con`-headedness of the
argument (the scrutinee), a further `app` continues the descent along the spine,
and anything else is `false`; non-`app` nodes are `false`. This dispatch ignores
saturation; the saturation guard is applied by `topIota`. -/
def iotaSpineOp {Γ : Binding.Ctx RType} (o : OneLambdaOp A)
    (children : ∀ j : Fin ((oneLambdaSig A).args o).length,
      Binding.Tm (oneLambdaSig A) (Γ ++ (((oneLambdaSig A).args o).get j).1)
        (((oneLambdaSig A).args o).get j).2)
    (rec : Fin ((oneLambdaSig A).args o).length → Bool) : Bool :=
  match o with
  | OneLambdaOp.app _ _ =>
      match headTag (children ⟨0, Nat.succ_pos 1⟩) with
      | some (OneLambdaOp.dstr _) => conHeaded (children ⟨1, Nat.one_lt_two⟩)
      | some OneLambdaOp.case => conHeaded (children ⟨1, Nat.one_lt_two⟩)
      | some (OneLambdaOp.app _ _) => rec ⟨0, Nat.succ_pos 1⟩
      | _ => false
  | _ => false

/-- Whether the function spine of the node bottoms out at a `dstr` or `case` head
over a `con`-headed scrutinee (Leivant III section 4.2, p. 224), ignoring
saturation: a `dstr j` or `case` applied — via the spine's function subterms — to
a `con`-headed argument. The ungated spine detector; `topIota` restricts it to
saturated nodes by the result-sort guard. Structural recursion by `PolyFix.ind`;
transcription of section 4.2's ι-redex head-forms. -/
def iotaSpine {Γ : Binding.Ctx RType} {s : RType}
    (t : Binding.Tm (oneLambdaSig A) Γ s) : Bool :=
  PolyFix.ind (P := polyTranslate Binding.varOver (oneLambdaSig A).polyEndo)
    (motive := fun {_} _ => Bool)
    (fun {x} i children ih =>
      match i, children, ih with
      | Sum.inl _, _, _ => false
      | Sum.inr p, children, ih =>
        iotaSpineOp (Γ := x.1) p.val (fun j => children ⟨j⟩) (fun j => ih ⟨j⟩)) t

/-- `iotaSpine` at an operation node is `iotaSpineOp` on its subterms, with the
recursive `iotaSpine` on the function subterm for the spine descent. -/
@[simp] theorem iotaSpine_op {Γ : Binding.Ctx RType} (o : OneLambdaOp A)
    (args : ∀ j : Fin ((oneLambdaSig A).args o).length,
      Binding.Tm (oneLambdaSig A) (Γ ++ (((oneLambdaSig A).args o).get j).1)
        (((oneLambdaSig A).args o).get j).2) :
    iotaSpine (Binding.Tm.op o args) = iotaSpineOp o args (fun j => iotaSpine (args j)) := rfl

/-- `iotaSpine` at a variable is `false`. -/
@[simp] theorem iotaSpine_var {Γ : Binding.Ctx RType} {s : RType} (x : Binding.Var Γ s) :
    iotaSpine (Binding.Tm.var x : Binding.Tm (oneLambdaSig A) Γ s) = false := by
  obtain ⟨i, hi⟩ := x; subst hi; rfl

/-- `iotaSpine` at an abstraction node is `false`: a `lam` head is not an
ι-redex. -/
@[simp] theorem iotaSpine_lam' {Γ : Binding.Ctx RType} {σ τ : RType}
    (b : Binding.Tm (oneLambdaSig A) (Γ ++ [σ]) τ) : iotaSpine (lam' b) = false := rfl

/-- `iotaSpine` is invariant under transport of the context and sort indices. -/
theorem iotaSpine_cast {Γ Γ' : Binding.Ctx RType} {s s' : RType}
    (hΓ : Γ = Γ') (hs : s = s') (t : Binding.Tm (oneLambdaSig A) Γ s) :
    iotaSpine (hs ▸ hΓ ▸ t) = iotaSpine t := by subst hΓ; subst hs; rfl

/-- `iotaSpine` ignores the `Γ ++ [] = Γ` transport that `app'` applies. -/
private theorem iotaSpine_appendNil {Γ : Binding.Ctx RType} {s : RType}
    (t : Binding.Tm (oneLambdaSig A) Γ s) :
    iotaSpine ((List.append_nil Γ).symm ▸ t) = iotaSpine t :=
  iotaSpine_cast (List.append_nil Γ).symm rfl t

/-- `iotaSpine` at an application node inspects the head of the function subterm:
a destructor or case head over a `con`-headed argument bottoms the spine; a
further application continues the spine descent. -/
theorem iotaSpine_app' {Γ : Binding.Ctx RType} {σ τ : RType}
    (f : Binding.Tm (oneLambdaSig A) Γ (RType.arrow σ τ))
    (x : Binding.Tm (oneLambdaSig A) Γ σ) :
    iotaSpine (app' f x)
      = (match headTag f with
         | some (OneLambdaOp.dstr _) => conHeaded x
         | some OneLambdaOp.case => conHeaded x
         | some (OneLambdaOp.app _ _) => iotaSpine f
         | _ => false) := by
  change (match headTag ((List.append_nil Γ).symm ▸ f) with
      | some (OneLambdaOp.dstr _) => conHeaded ((List.append_nil Γ).symm ▸ x)
      | some OneLambdaOp.case => conHeaded ((List.append_nil Γ).symm ▸ x)
      | some (OneLambdaOp.app _ _) => iotaSpine ((List.append_nil Γ).symm ▸ f)
      | _ => false) = _
  rw [headTag_appendNil, conHeaded_appendNil, iotaSpine_appendNil]

/-- The ι-redex indicator at the top node (Leivant III section 4.2, p. 224):
whether the node is a genuine saturated destructor- or case-redex over a
`con`-headed scrutinee. The result-sort guard `s.shape = RTypeShape.o` restricts
the ungated `iotaSpine` to saturated nodes: `case : o^{numCtors+1} → o` and
`dstr : o → o`, so a `dstr`- or `case`-spine node of result sort `o` is exactly
one saturated through the intrinsic sorts, and every genuine ι-redex (the
`OneLambdaStep.dstrHit`/`dstrMiss`/`case` shape) has result sort `o` at its root.
The guard removes exactly the unsaturated `iotaSpine` flags — an arrow-sorted
partial application such as `app' case scrut` — and no genuine redex.
Non-recursive read of the top node. Transcription of section 4.2's ι-redex
head-forms. -/
def topIota {Γ : Binding.Ctx RType} {s : RType}
    (t : Binding.Tm (oneLambdaSig A) Γ s) : Bool :=
  if s.shape = RTypeShape.o then iotaSpine t else false

/-- `topIota` at a variable is `false`. -/
@[simp] theorem topIota_var {Γ : Binding.Ctx RType} {s : RType} (x : Binding.Var Γ s) :
    topIota (Binding.Tm.var x : Binding.Tm (oneLambdaSig A) Γ s) = false := by
  simp only [topIota, iotaSpine_var, ite_self]

/-- `topIota` at an abstraction node is `false`: a `lam`-headed node has arrow
sort, and a `lam` head is not an ι-redex. -/
@[simp] theorem topIota_lam' {Γ : Binding.Ctx RType} {σ τ : RType}
    (b : Binding.Tm (oneLambdaSig A) (Γ ++ [σ]) τ) : topIota (lam' b) = false := by
  simp only [topIota, iotaSpine_lam', ite_self]

/-- `topIota` is invariant under transport of the context and sort indices. -/
theorem topIota_cast {Γ Γ' : Binding.Ctx RType} {s s' : RType}
    (hΓ : Γ = Γ') (hs : s = s') (t : Binding.Tm (oneLambdaSig A) Γ s) :
    topIota (hs ▸ hΓ ▸ t) = topIota t := by subst hΓ; subst hs; rfl

/-- `topIota` at an application node applies the result-sort saturation guard to
the spine detector: an ι-redex requires result sort `o` together with a
destructor- or case-headed spine over a `con`-headed argument. -/
theorem topIota_app' {Γ : Binding.Ctx RType} {σ τ : RType}
    (f : Binding.Tm (oneLambdaSig A) Γ (RType.arrow σ τ))
    (x : Binding.Tm (oneLambdaSig A) Γ σ) :
    topIota (app' f x)
      = (if τ.shape = RTypeShape.o then
          (match headTag f with
           | some (OneLambdaOp.dstr _) => conHeaded x
           | some OneLambdaOp.case => conHeaded x
           | some (OneLambdaOp.app _ _) => iotaSpine f
           | _ => false)
         else false) := by
  simp only [topIota, iotaSpine_app']

/-- The β-rank measure (Leivant III section 4.2, p. 224): the maximum of
`topBetaRank` over every subterm position. Structural recursion by
`PolyFix.ind` maxing the top contribution with the children's ranks. The cycle
machinery of Lemma 12 reads only this component of the aggregate `redexRank`.
Transcription of section 4.2's rank measure. -/
def betaRedexRank {Γ : Binding.Ctx RType} {s : RType}
    (t : Binding.Tm (oneLambdaSig A) Γ s) : ℕ :=
  PolyFix.ind (P := polyTranslate Binding.varOver (oneLambdaSig A).polyEndo)
    (motive := fun {_} _ => ℕ)
    (fun {x} i children ih =>
      match i, children, ih with
      | Sum.inl _, _, _ => 0
      | Sum.inr p, children, ih =>
        max (topBetaRankOp (Γ := x.1) p.val (fun j => children ⟨j⟩))
          (Finset.univ.sup (fun j => ih ⟨j⟩))) t

/-- `betaRedexRank` at an operation node is the maximum of the top β-rank and the
β-ranks of the subterms. -/
@[simp] theorem betaRedexRank_op {Γ : Binding.Ctx RType} (o : OneLambdaOp A)
    (args : ∀ j : Fin ((oneLambdaSig A).args o).length,
      Binding.Tm (oneLambdaSig A) (Γ ++ (((oneLambdaSig A).args o).get j).1)
        (((oneLambdaSig A).args o).get j).2) :
    betaRedexRank (Binding.Tm.op o args)
      = max (topBetaRank (Binding.Tm.op o args))
          (Finset.univ.sup (fun j => betaRedexRank (args j))) := rfl

/-- `betaRedexRank` at a variable is `0`. -/
@[simp] theorem betaRedexRank_var {Γ : Binding.Ctx RType} {s : RType} (x : Binding.Var Γ s) :
    betaRedexRank (Binding.Tm.var x : Binding.Tm (oneLambdaSig A) Γ s) = 0 := by
  obtain ⟨i, hi⟩ := x; subst hi; rfl

/-- `betaRedexRank` is invariant under transport of the context and sort. -/
theorem betaRedexRank_cast {Γ Γ' : Binding.Ctx RType} {s s' : RType}
    (hΓ : Γ = Γ') (hs : s = s') (t : Binding.Tm (oneLambdaSig A) Γ s) :
    betaRedexRank (hs ▸ hΓ ▸ t) = betaRedexRank t := by subst hΓ; subst hs; rfl

/-- `betaRedexRank` ignores the `Γ ++ [] = Γ` transport that `app'` applies. -/
private theorem betaRedexRank_appendNil {Γ : Binding.Ctx RType} {s : RType}
    (t : Binding.Tm (oneLambdaSig A) Γ s) :
    betaRedexRank ((List.append_nil Γ).symm ▸ t) = betaRedexRank t :=
  betaRedexRank_cast (List.append_nil Γ).symm rfl t

/-- `betaRedexRank` at an application node is the maximum of the top β-rank and
the β-ranks of the function and argument subterms. -/
@[simp] theorem betaRedexRank_app' {Γ : Binding.Ctx RType} {σ τ : RType}
    (f : Binding.Tm (oneLambdaSig A) Γ (RType.arrow σ τ))
    (x : Binding.Tm (oneLambdaSig A) Γ σ) :
    betaRedexRank (app' f x)
      = max (topBetaRank (app' f x)) (max (betaRedexRank f) (betaRedexRank x)) := by
  change max (topBetaRank (app' f x)) ((Finset.univ : Finset (Fin 2)).sup _) = _
  rw [show (Finset.univ : Finset (Fin 2)) = {0, 1} from rfl, Finset.sup_insert,
    Finset.sup_singleton]
  change max (topBetaRank (app' f x))
    (betaRedexRank ((List.append_nil Γ).symm ▸ f) ⊔ betaRedexRank ((List.append_nil Γ).symm ▸ x))
      = _
  rw [betaRedexRank_appendNil, betaRedexRank_appendNil]

/-- `betaRedexRank` at an abstraction node is the β-rank of its body (a `lam`
head contributes no top β-rank). -/
@[simp] theorem betaRedexRank_lam' {Γ : Binding.Ctx RType} {σ τ : RType}
    (b : Binding.Tm (oneLambdaSig A) (Γ ++ [σ]) τ) :
    betaRedexRank (lam' b) = betaRedexRank b := by
  change max 0 ((Finset.univ : Finset (Fin 1)).sup _) = _
  rw [show (Finset.univ : Finset (Fin 1)) = {0} from rfl, Finset.sup_singleton]
  change max 0 (betaRedexRank b) = _
  omega

/-- The ι-redex indicator (Leivant III section 4.2, p. 224): whether some subterm
position is a destructor- or case-redex over a `con`-headed scrutinee.
Structural recursion by `PolyFix.ind` disjoining the top detector with the
children. Per the p. 224 aggregate, an ι-redex counts rank exactly `1`, so the
cycle machinery reads this indicator separately from `betaRedexRank`.
Transcription of section 4.2's ι-redex census. -/
def hasIota {Γ : Binding.Ctx RType} {s : RType}
    (t : Binding.Tm (oneLambdaSig A) Γ s) : Bool :=
  PolyFix.ind (P := polyTranslate Binding.varOver (oneLambdaSig A).polyEndo)
    (motive := fun {_} _ => Bool)
    (fun {x} i children ih =>
      match i, children, ih with
      | Sum.inl _, _, _ => false
      | Sum.inr p, children, ih =>
        (if x.2.shape = RTypeShape.o then
          iotaSpineOp (Γ := x.1) p.val (fun j => children ⟨j⟩)
            (fun j => iotaSpine (children ⟨j⟩))
         else false)
          || Finset.univ.sup (fun j => ih ⟨j⟩)) t

/-- `hasIota` at an operation node disjoins the top ι-redex detector with the
ι-redex indicators of the subterms. -/
@[simp] theorem hasIota_op {Γ : Binding.Ctx RType} (o : OneLambdaOp A)
    (args : ∀ j : Fin ((oneLambdaSig A).args o).length,
      Binding.Tm (oneLambdaSig A) (Γ ++ (((oneLambdaSig A).args o).get j).1)
        (((oneLambdaSig A).args o).get j).2) :
    hasIota (Binding.Tm.op o args)
      = (topIota (Binding.Tm.op o args) || Finset.univ.sup (fun j => hasIota (args j))) := rfl

/-- `hasIota` at a variable is `false`. -/
@[simp] theorem hasIota_var {Γ : Binding.Ctx RType} {s : RType} (x : Binding.Var Γ s) :
    hasIota (Binding.Tm.var x : Binding.Tm (oneLambdaSig A) Γ s) = false := by
  obtain ⟨i, hi⟩ := x; subst hi; rfl

/-- `hasIota` is invariant under transport of the context and sort. -/
theorem hasIota_cast {Γ Γ' : Binding.Ctx RType} {s s' : RType}
    (hΓ : Γ = Γ') (hs : s = s') (t : Binding.Tm (oneLambdaSig A) Γ s) :
    hasIota (hs ▸ hΓ ▸ t) = hasIota t := by subst hΓ; subst hs; rfl

/-- `hasIota` ignores the `Γ ++ [] = Γ` transport that `app'` applies. -/
private theorem hasIota_appendNil {Γ : Binding.Ctx RType} {s : RType}
    (t : Binding.Tm (oneLambdaSig A) Γ s) :
    hasIota ((List.append_nil Γ).symm ▸ t) = hasIota t :=
  hasIota_cast (List.append_nil Γ).symm rfl t

/-- `hasIota` at an application node disjoins the top ι-redex detector with the
ι-redex indicators of the function and argument subterms. -/
@[simp] theorem hasIota_app' {Γ : Binding.Ctx RType} {σ τ : RType}
    (f : Binding.Tm (oneLambdaSig A) Γ (RType.arrow σ τ))
    (x : Binding.Tm (oneLambdaSig A) Γ σ) :
    hasIota (app' f x) = (topIota (app' f x) || hasIota f || hasIota x) := by
  change (topIota (app' f x) || (Finset.univ : Finset (Fin 2)).sup _) = _
  rw [show (Finset.univ : Finset (Fin 2)) = {0, 1} from rfl, Finset.sup_insert,
    Finset.sup_singleton]
  change (topIota (app' f x)
    || (hasIota ((List.append_nil Γ).symm ▸ f) ⊔ hasIota ((List.append_nil Γ).symm ▸ x))) = _
  rw [hasIota_appendNil, hasIota_appendNil]
  cases hasIota f <;> cases hasIota x <;> cases topIota (app' f x) <;> rfl

/-- `hasIota` at an abstraction node is the ι-redex indicator of its body (a
`lam` head is not an ι-redex). -/
@[simp] theorem hasIota_lam' {Γ : Binding.Ctx RType} {σ τ : RType}
    (b : Binding.Tm (oneLambdaSig A) (Γ ++ [σ]) τ) :
    hasIota (lam' b) = hasIota b := by
  refine (hasIota_op (Γ := Γ) (OneLambdaOp.lam σ τ)
    (fun j => Fin.cases b (fun k => k.elim0) j)).trans ?_
  change (topIota (lam' b) || (Finset.univ : Finset (Fin 1)).sup _) = _
  rw [show (Finset.univ : Finset (Fin 1)) = {0} from rfl, Finset.sup_singleton, topIota_lam']
  rfl

/-- The aggregate redex rank of a term (Leivant III section 4.2, p. 224): the
maximum of the β-rank and the ι-redex contribution, which counts `1` when an
ι-redex is present. The p. 224 aggregate, split into `betaRedexRank` and
`hasIota` (decision P6). Transcription of section 4.2's redex rank. -/
def redexRank {Γ : Binding.Ctx RType} {s : RType}
    (t : Binding.Tm (oneLambdaSig A) Γ s) : ℕ :=
  max (betaRedexRank t) (if hasIota t then 1 else 0)

/-- A term is normal (Leivant III section 4.2, p. 224) when its redex rank is
`0`: it contains no β-redex and no ι-redex. Decision P6's `def`. Transcription
of section 4.2's normal form. -/
def Normal {Γ : Binding.Ctx RType} {s : RType}
    (t : Binding.Tm (oneLambdaSig A) Γ s) : Prop := redexRank t = 0

/-- The β-rank bounds the aggregate redex rank. -/
theorem betaRedexRank_le_redexRank {Γ : Binding.Ctx RType} {s : RType}
    (t : Binding.Tm (oneLambdaSig A) Γ s) : betaRedexRank t ≤ redexRank t :=
  le_max_left _ _

/-- A term is normal iff it has β-rank `0` and no ι-redex. -/
theorem normal_iff {Γ : Binding.Ctx RType} {s : RType}
    (t : Binding.Tm (oneLambdaSig A) Γ s) :
    Normal t ↔ betaRedexRank t = 0 ∧ hasIota t = false := by
  unfold Normal redexRank
  cases h : hasIota t <;> simp

/-- The aggregate redex rank of an application node in terms of the ranks of its
subterms and the top detectors `topBetaRank` and `topIota`. -/
@[simp] theorem redexRank_app' {Γ : Binding.Ctx RType} {σ τ : RType}
    (f : Binding.Tm (oneLambdaSig A) Γ (RType.arrow σ τ))
    (x : Binding.Tm (oneLambdaSig A) Γ σ) :
    redexRank (app' f x)
      = max (topBetaRank (app' f x))
          (max (max (redexRank f) (redexRank x)) (if topIota (app' f x) then 1 else 0)) := by
  unfold redexRank
  simp only [betaRedexRank_app', hasIota_app']
  cases hf : hasIota f <;> cases hx : hasIota x <;> cases ht : topIota (app' f x) <;>
    simp <;> omega

end OneLambda

end GebLean.Ramified
