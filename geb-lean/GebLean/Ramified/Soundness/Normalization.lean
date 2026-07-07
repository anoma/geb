import GebLean.Ramified.Soundness.BarRep
import GebLean.Binding.Measures
import GebLean.Utilities.Tower
import Mathlib.Algebra.BigOperators.Fin
import Cslib.Foundations.Data.RelatesInSteps

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
* `OneLambda.stepWithin` — the size-bounded one-step reduction: an `OneLambdaStep`
  whose target has size at most a fixed ceiling.

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
* `OneLambda.normal_conc`, `OneLambda.normal_bbRep` — the value forms of the
  bar-translation are normal.
* `OneLambda.exists_iota_step_of_hasIota` — a β-normal term with an ι-redex
  takes a step that strictly decreases the size, does not increase the height,
  and preserves β-normality.
* `OneLambda.relatesInSteps_mono`, `OneLambda.stepWithin_mono`,
  `OneLambda.relatesInSteps_stepWithin_reflTransGen` — monotonicity of a counted
  chain in its relation and of `stepWithin` in its ceiling, and the projection of
  a counted `stepWithin` chain to a `Relation.ReflTransGen` reduction.
* `OneLambda.relatesInSteps_app'_left`, `OneLambda.relatesInSteps_app'_right`,
  `OneLambda.relatesInSteps_lamBody` — counted chains lift through the congruence
  rules at the same length, with the size ceiling shifted by the fixed sibling.
* `OneLambda.betaRedexRank_ren`, `OneLambda.isLam_ren` — invariance of the β-rank
  and the abstraction detector under renaming.
* `OneLambda.betaRedexRank_instantiate₁_le` — the β-rank of a single-variable
  substitution instance is bounded by the β-ranks of the body and the substituted
  term together with the order of the substituted sort (note N2).
* `OneLambda.relatesInSteps_stepWithin_size_le` — the endpoint of a counted
  `stepWithin` chain obeys the chain's size ceiling whenever the start does.
* `OneLambda.size_le_two_pow_height` — the arity inequality at `oneLambdaSig`:
  a term's size is bounded by `2` raised to its height.

## References

D. Leivant, "Ramified recurrence and computational complexity III: Higher
type recurrence and elementary complexity", Annals of Pure and Applied
Logic 96 (1999) 209-229, DOI `10.1016/S0168-0072(98)00040-2`, section 2.2
(p. 213): the order of a simple type; section 4.2 (p. 224): the redexes, their
ranks, and normality of `1λ(A)`; section 5, proof paragraph (ii) (p. 226): the
substitution redex-rank bound (note N2); section 5, proof paragraph (iii)
(p. 226): the ι-phase step accounting.

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

/-- `betaRedexRank` is invariant under a context `cast`: transporting a term
along a context equality leaves its β-rank unchanged. The `cast`-presentation
counterpart of `betaRedexRank_cast`, matching the transports of `lamSpine`. -/
private theorem betaRedexRank_castCtx {Γ Γ' : Binding.Ctx RType} {s : RType}
    (h : Γ = Γ') (t : Binding.Tm (oneLambdaSig A) Γ s) :
    betaRedexRank (cast (congrArg (fun c => Binding.Tm (oneLambdaSig A) c s) h) t)
      = betaRedexRank t := by cases h; rfl

/-- `hasIota` is invariant under a context `cast`. The `cast`-presentation
counterpart of `hasIota_cast`. -/
private theorem hasIota_castCtx {Γ Γ' : Binding.Ctx RType} {s : RType}
    (h : Γ = Γ') (t : Binding.Tm (oneLambdaSig A) Γ s) :
    hasIota (cast (congrArg (fun c => Binding.Tm (oneLambdaSig A) c s) h) t) = hasIota t := by
  cases h; rfl

/-- An `Eq.mpr` transport is heterogeneously equal to its argument: it carries
the value across a type equality without changing it. Reconciles the `Eq.mpr`
sort transports the source of `replicateSpine` emits. -/
private theorem eqMpr_heq {α β : Sort _} (h : α = β) (x : β) : HEq (Eq.mpr h x) x := by
  subst h; rfl

/-- `betaRedexRank` respects heterogeneous term equality at sorts identified by
`hs`: the β-rank is a sort-agnostic natural number, so heterogeneously-equal
terms share it. Reconciles the per-argument `Eq.mpr` sort transports of
`replicateSpine`. -/
private theorem betaRedexRank_heq {Γ : Binding.Ctx RType} {a b : RType}
    (hs : a = b) {t : Binding.Tm (oneLambdaSig A) Γ a} {u : Binding.Tm (oneLambdaSig A) Γ b}
    (h : HEq t u) : betaRedexRank t = betaRedexRank u := by cases hs; rw [eq_of_heq h]

/-- `hasIota` respects heterogeneous term equality at sorts identified by `hs`. -/
private theorem hasIota_heq {Γ : Binding.Ctx RType} {a b : RType}
    (hs : a = b) {t : Binding.Tm (oneLambdaSig A) Γ a} {u : Binding.Tm (oneLambdaSig A) Γ b}
    (h : HEq t u) : hasIota t = hasIota u := by cases hs; rw [eq_of_heq h]

/-- The spine-safety invariant of the value forms `conc` and `bbRep` (Leivant III
section 4.2, p. 223): a term with no β-redex and no ι-redex that is not itself an
abstraction and whose head operation is a constructor, a variable, or an
application (never a destructor, a case, or an abstraction). Preserved by
application to a redex-free argument (`spineSafe_app'`), it is the property
carried through the constructor spines of `conc` and the variable-headed fold of
`bbRep`. Novel packaging; the substance is section 4.2's normal-form head-form. -/
private def SpineSafe {Γ : Binding.Ctx RType} {s : RType}
    (t : Binding.Tm (oneLambdaSig A) Γ s) : Prop :=
  betaRedexRank t = 0 ∧ hasIota t = false ∧ isLam t = false ∧ iotaSpine t = false ∧
    (headTag t = none ∨ (∃ b, headTag t = some (OneLambdaOp.con b)) ∨
      ∃ σ τ, headTag t = some (OneLambdaOp.app σ τ))

/-- A variable is spine-safe: it carries no redexes, is not an abstraction, and
its head is a variable. -/
private theorem spineSafe_var {Γ : Binding.Ctx RType} {s : RType} (x : Binding.Var Γ s) :
    SpineSafe (Binding.Tm.var x : Binding.Tm (oneLambdaSig A) Γ s) :=
  ⟨betaRedexRank_var x, hasIota_var x, isLam_var x, iotaSpine_var x, Or.inl (headTag_var x)⟩

/-- A constructor constant is spine-safe: it carries no redexes, is not an
abstraction, and its head is a `con`. -/
private theorem spineSafe_con {Γ : Binding.Ctx RType} (b : A.B) :
    SpineSafe (Binding.Tm.op (S := oneLambdaSig A) (Γ := Γ) (OneLambdaOp.con b)
      (fun k => k.elim0)) := by
  refine ⟨rfl, ?_, rfl, rfl, Or.inr (Or.inl ⟨b, rfl⟩)⟩
  rw [hasIota_op]
  simp only [topIota, iotaSpine_op, iotaSpineOp, ite_self, Bool.false_or]
  rfl

/-- Spine-safety is preserved by application to a redex-free argument: if `f` is
spine-safe and `x` carries no β- or ι-redex, then `app' f x` is spine-safe. Since
`f` is not an abstraction the node is not a β-redex, and since the head of `f` is
a constructor, a variable, or an application (never a destructor or a case) the
node is not an ι-redex, so both ranks stay `0`. -/
private theorem spineSafe_app' {Γ : Binding.Ctx RType} {σ τ : RType}
    (f : Binding.Tm (oneLambdaSig A) Γ (RType.arrow σ τ))
    (x : Binding.Tm (oneLambdaSig A) Γ σ)
    (hf : SpineSafe f) (hxβ : betaRedexRank x = 0) (hxι : hasIota x = false) :
    SpineSafe (app' f x) := by
  obtain ⟨hfβ, hfι, hfL, hfS, hfH⟩ := hf
  have hmatch : (match headTag f with
      | some (OneLambdaOp.dstr _) => conHeaded x
      | some OneLambdaOp.case => conHeaded x
      | some (OneLambdaOp.app _ _) => iotaSpine f
      | _ => false) = false := by
    rcases hfH with h | ⟨b, h⟩ | ⟨σ', τ', h⟩ <;> simp [h, hfS]
  refine ⟨?_, ?_, isLam_app' f x, ?_, Or.inr (Or.inr ⟨σ, τ, headTag_app' f x⟩)⟩
  · rw [betaRedexRank_app', topBetaRank_app', hfL, hfβ, hxβ]; simp
  · rw [hasIota_app', topIota_app', hfι, hxι, hmatch]; simp
  · rw [iotaSpine_app', hmatch]

/-- Spine-safety is preserved by an application spine over redex-free arguments:
if `head` is spine-safe and every argument carries no β- or ι-redex, then
`appSpine Ts head args` is spine-safe. By recursion on `Ts`, extending the head
one application at a time through `spineSafe_app'`. -/
private theorem spineSafe_appSpine {Γ : Binding.Ctx RType} {result : RType} :
    (Ts : List RType) →
    (head : Binding.Tm (oneLambdaSig A) Γ (RType.curried Ts result)) →
    (args : ∀ i : Fin Ts.length, Binding.Tm (oneLambdaSig A) Γ (Ts.get i)) →
    SpineSafe head →
    (∀ i, betaRedexRank (args i) = 0 ∧ hasIota (args i) = false) →
    SpineSafe (appSpine Ts head args)
  | [], _head, _args, hhead, _hargs => hhead
  | _T :: Ts', head, args, hhead, hargs => by
      rw [appSpine]
      exact spineSafe_appSpine Ts' (app' head (args ⟨0, Nat.succ_pos _⟩))
        (fun i => args i.succ)
        (spineSafe_app' head (args ⟨0, Nat.succ_pos _⟩) hhead
          (hargs ⟨0, Nat.succ_pos _⟩).1 (hargs ⟨0, Nat.succ_pos _⟩).2)
        (fun i => hargs i.succ)

/-- Spine-safety is preserved by a homogeneous application spine over redex-free
arguments. The `replicateSpine` instance of `spineSafe_appSpine`, reconciling the
per-index `Eq.mpr` sort transports through the heterogeneous rank lemmas
`betaRedexRank_heq` and `hasIota_heq`. -/
private theorem spineSafe_replicateSpine {Γ : Binding.Ctx RType} {result : RType}
    (n : Nat) (base : RType)
    (head : Binding.Tm (oneLambdaSig A) Γ (RType.curried (List.replicate n base) result))
    (args : Fin n → Binding.Tm (oneLambdaSig A) Γ base)
    (hhead : SpineSafe head)
    (hargs : ∀ i, betaRedexRank (args i) = 0 ∧ hasIota (args i) = false) :
    SpineSafe (replicateSpine n base head args) := by
  rw [replicateSpine]
  refine spineSafe_appSpine (List.replicate n base) head _ hhead (fun idx => ?_)
  have hs : (List.replicate n base).get idx = base := by
    rw [List.get_eq_getElem, List.getElem_replicate]
  refine ⟨(betaRedexRank_heq hs ?_).trans (hargs (idx.cast List.length_replicate)).1,
    (hasIota_heq hs ?_).trans (hargs (idx.cast List.length_replicate)).2⟩ <;>
    exact (eqMpr_heq _ _).trans (eqMpr_heq _ _)

/-- The concrete term of a free-algebra value is normal (Leivant III section 4.2,
p. 223): `conc a` is a constructor-headed application spine, carrying no β-redex
and no ι-redex. By recurrence-structural induction on `a`, the constructor spine
at each node is spine-safe (`spineSafe_replicateSpine` over the constructor head
`spineSafe_con`). Anchors Proposition 13's uniform rank constant on the concrete
side. Transcription of section 4.2's normality of the concrete representation. -/
theorem normal_conc (a : FreeAlg A) : Normal (conc a) := by
  rw [normal_iff]
  have h : SpineSafe (conc a) := by
    refine PolyFix.ind (P := A.polyEndo) (motive := fun {_} a => SpineSafe (conc a))
      (fun b children ih => ?_) a
    change SpineSafe (conc (FreeAlg.mk b children))
    rw [conc_mk]
    exact spineSafe_replicateSpine (A.ar b) RType.o _ _ (spineSafe_con b)
      (fun i => ⟨(ih i).1, (ih i).2.1⟩)
  exact ⟨h.1, h.2.1⟩

/-- The β-rank ignores the iterated abstraction `lamSpine`: a `lam` head
contributes no β-rank, so `betaRedexRank (lamSpine Δ body) = betaRedexRank body`.
By recursion on `Δ`, peeling one `lam'` at a time (`betaRedexRank_lam'`) and
discharging the binder-associativity transports by `betaRedexRank_castCtx`. -/
private theorem betaRedexRank_lamSpine :
    {Γ : Binding.Ctx RType} → (Δ : List RType) → {τ : RType} →
    (body : Binding.Tm (oneLambdaSig A) (Γ ++ Δ) τ) →
    betaRedexRank (lamSpine Δ body) = betaRedexRank body
  | Γ, [], _τ, body => by
      rw [lamSpine]; exact betaRedexRank_castCtx (List.append_nil Γ) body
  | Γ, σ :: Δ', _τ, body => by
      rw [lamSpine]
      exact (betaRedexRank_lam' _).trans ((betaRedexRank_lamSpine Δ' _).trans
        (betaRedexRank_castCtx (List.append_assoc Γ [σ] Δ').symm body))

/-- The ι-redex indicator ignores the iterated abstraction `lamSpine`: a `lam`
head is not an ι-redex, so `hasIota (lamSpine Δ body) = hasIota body`. By
recursion on `Δ` as for `betaRedexRank_lamSpine`. -/
private theorem hasIota_lamSpine :
    {Γ : Binding.Ctx RType} → (Δ : List RType) → {τ : RType} →
    (body : Binding.Tm (oneLambdaSig A) (Γ ++ Δ) τ) →
    hasIota (lamSpine Δ body) = hasIota body
  | Γ, [], _τ, body => by
      rw [lamSpine]; exact hasIota_castCtx (List.append_nil Γ) body
  | Γ, σ :: Δ', _τ, body => by
      rw [lamSpine]
      exact (hasIota_lam' _).trans ((hasIota_lamSpine Δ' _).trans
        (hasIota_castCtx (List.append_assoc Γ [σ] Δ').symm body))

/-- The Berarducci-Böhm representation of a free-algebra value is normal (Leivant
III section 4.2, p. 223): `bbRep a σ` abstracts the constructor variables `c̄`
over a variable-headed application spine, carrying no β-redex and no ι-redex. The
inner fold is spine-safe (`spineSafe_replicateSpine` over the variable head
`spineSafe_var`, by recurrence-structural induction on `a`), and the outer
`lamSpine` contributes no redex (`betaRedexRank_lamSpine`, `hasIota_lamSpine`).
Anchors Proposition 13's uniform rank constant on the abstract side.
Transcription of section 4.2's normality of the abstract representation. -/
theorem normal_bbRep (a : FreeAlg natAlgSig) (σ : RType) : Normal (bbRep a σ) := by
  rw [normal_iff]
  have hinner : SpineSafe (FreeAlg.recurse (A := natAlgSig) (P := Unit)
      (C := Binding.Tm (oneLambdaSig natAlgSig) (stepTypes natAlgSig σ σ) σ)
      (fun b _ _sub rec =>
        replicateSpine (natAlgSig.ar b) σ (Binding.Tm.var (ctorVar b)) rec) () a) := by
    refine PolyFix.ind (P := natAlgSig.polyEndo)
      (motive := fun {_} a => SpineSafe (FreeAlg.recurse (A := natAlgSig) (P := Unit)
        (C := Binding.Tm (oneLambdaSig natAlgSig) (stepTypes natAlgSig σ σ) σ)
        (fun b _ _sub rec =>
          replicateSpine (natAlgSig.ar b) σ (Binding.Tm.var (ctorVar b)) rec) () a))
      (fun b children ih => ?_) a
    change SpineSafe (FreeAlg.recurse (A := natAlgSig) (P := Unit)
      (C := Binding.Tm (oneLambdaSig natAlgSig) (stepTypes natAlgSig σ σ) σ)
      (fun b _ _sub rec =>
        replicateSpine (natAlgSig.ar b) σ (Binding.Tm.var (ctorVar b)) rec) ()
        (FreeAlg.mk b children))
    rw [FreeAlg.recurse_mk]
    exact spineSafe_replicateSpine (natAlgSig.ar b) σ _ _ (spineSafe_var (ctorVar b))
      (fun i => ⟨(ih i).1, (ih i).2.1⟩)
  unfold bbRep
  exact ⟨(betaRedexRank_lamSpine _ _).trans hinner.1,
    (hasIota_lamSpine _ _).trans hinner.2.1⟩

/-- Transporting a term along a context equality and back along its inverse is
the identity. The round-trip cancellation discharging the `Γ ++ [] = Γ`
transports that `app'` re-applies to already-transported subterms. -/
private theorem eqRec_symm_eqRec {Γ Γ' : Binding.Ctx RType} {s : RType} (h : Γ = Γ')
    (t : Binding.Tm (oneLambdaSig A) Γ s) :
    h.symm ▸ (h ▸ t : Binding.Tm (oneLambdaSig A) Γ' s) = t := by cases h; rfl

/-- A reduction step transports along a context equality: the congruence- and
redex-rule shapes are context-generic. -/
private theorem oneLambdaStep_cast [LinearOrder A.B] {Γ Γ' : Binding.Ctx RType} {s : RType}
    (hΓ : Γ = Γ') {t u : Binding.Tm (oneLambdaSig A) Γ s} (h : OneLambdaStep t u) :
    OneLambdaStep (hΓ ▸ t : Binding.Tm (oneLambdaSig A) Γ' s) (hΓ ▸ u) := by
  cases hΓ; exact h

/-- Every application node is an `app'`: the η-expansion of `Tm.op` at an `app`
operation, recovering the combinator form from an arbitrary argument tuple. The
subterms are transported out of the argument context `Γ ++ []` along
`List.append_nil`; `app'` transports them back. -/
private theorem op_app_eta {Γ : Binding.Ctx RType} {σ τ : RType}
    (args : ∀ j : Fin (((oneLambdaSig A).args (OneLambdaOp.app σ τ)).length),
      Binding.Tm (oneLambdaSig A) (Γ ++ (((oneLambdaSig A).args (OneLambdaOp.app σ τ)).get j).1)
        (((oneLambdaSig A).args (OneLambdaOp.app σ τ)).get j).2) :
    Binding.Tm.op (OneLambdaOp.app σ τ) args
      = app' (List.append_nil Γ ▸ (args ⟨0, Nat.succ_pos 1⟩ :
            Binding.Tm (oneLambdaSig A) (Γ ++ []) (RType.arrow σ τ)))
          (List.append_nil Γ ▸ (args ⟨1, Nat.one_lt_two⟩ :
            Binding.Tm (oneLambdaSig A) (Γ ++ []) σ)) := by
  unfold app'
  congr 1
  funext j
  match j with
  | ⟨0, _⟩ => exact (eqRec_symm_eqRec (List.append_nil Γ) _).symm
  | ⟨1, _⟩ => exact (eqRec_symm_eqRec (List.append_nil Γ) _).symm

/-- Every abstraction node is a `lam'`: the η-expansion of `Tm.op` at a `lam`
operation. The sole subterm lives at the binder-extended context `Γ ++ [σ]`
directly, so no transport is required. -/
private theorem op_lam_eta {Γ : Binding.Ctx RType} {σ τ : RType}
    (args : ∀ j : Fin (((oneLambdaSig A).args (OneLambdaOp.lam σ τ)).length),
      Binding.Tm (oneLambdaSig A) (Γ ++ (((oneLambdaSig A).args (OneLambdaOp.lam σ τ)).get j).1)
        (((oneLambdaSig A).args (OneLambdaOp.lam σ τ)).get j).2) :
    Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.lam σ τ) args
      = lam' (σ := σ) (τ := τ)
          (args ⟨0, Nat.one_pos⟩ : Binding.Tm (oneLambdaSig A) (Γ ++ [σ]) τ) := by
  unfold lam'
  congr 1
  funext j
  match j with
  | ⟨0, _⟩ => rfl

/-- Every application node is an `app'` of some function and argument at the
node's own context: the existential packaging of `op_app_eta`, whose components
carry the plain arrow and domain sorts. -/
private theorem op_app_inv {Γ : Binding.Ctx RType} {σ τ : RType}
    (args : ∀ j : Fin (((oneLambdaSig A).args (OneLambdaOp.app σ τ)).length),
      Binding.Tm (oneLambdaSig A) (Γ ++ (((oneLambdaSig A).args (OneLambdaOp.app σ τ)).get j).1)
        (((oneLambdaSig A).args (OneLambdaOp.app σ τ)).get j).2) :
    ∃ (f : Binding.Tm (oneLambdaSig A) Γ (RType.arrow σ τ))
      (x : Binding.Tm (oneLambdaSig A) Γ σ),
      Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.app σ τ) args = app' f x :=
  ⟨_, _, op_app_eta args⟩

/-- Every abstraction node is a `lam'` of some body at the binder-extended
context: the existential packaging of `op_lam_eta`. -/
private theorem op_lam_inv {Γ : Binding.Ctx RType} {σ τ : RType}
    (args : ∀ j : Fin (((oneLambdaSig A).args (OneLambdaOp.lam σ τ)).length),
      Binding.Tm (oneLambdaSig A) (Γ ++ (((oneLambdaSig A).args (OneLambdaOp.lam σ τ)).get j).1)
        (((oneLambdaSig A).args (OneLambdaOp.lam σ τ)).get j).2) :
    ∃ b : Binding.Tm (oneLambdaSig A) (Γ ++ [σ]) τ,
      Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.lam σ τ) args = lam' b :=
  ⟨_, op_lam_eta args⟩

/-- The head-form cases of a term of `1λ(A)`: a variable, or an operation node
whose result sort transports to the term's sort. The non-recursive case
principle on the `PolyFix` structure, packaging the index dance of the term
measures' inductions for reuse by the redex inversions. Novel packaging. -/
private theorem tm_cases {Γ : Binding.Ctx RType} {s : RType}
    (t : Binding.Tm (oneLambdaSig A) Γ s) :
    (∃ x : Binding.Var Γ s, t = Binding.Tm.var x) ∨
    ∃ (o : OneLambdaOp A) (hs : (oneLambdaSig A).result o = s)
      (args : ∀ j : Fin (((oneLambdaSig A).args o).length),
        Binding.Tm (oneLambdaSig A) (Γ ++ (((oneLambdaSig A).args o).get j).1)
          (((oneLambdaSig A).args o).get j).2),
      t = (hs ▸ Binding.Tm.op (S := oneLambdaSig A) o args
            : Binding.Tm (oneLambdaSig A) Γ s) := by
  suffices haux : ∀ {y : Binding.Ctx RType × RType}
      (t : PolyFix (polyTranslate Binding.varOver (oneLambdaSig A).polyEndo) y),
      (∃ x : Binding.Var y.1 y.2,
        t = (Binding.Tm.var x : Binding.Tm (oneLambdaSig A) y.1 y.2)) ∨
      ∃ (o : OneLambdaOp A) (hs : (oneLambdaSig A).result o = y.2)
        (args : ∀ j : Fin (((oneLambdaSig A).args o).length),
          Binding.Tm (oneLambdaSig A) (y.1 ++ (((oneLambdaSig A).args o).get j).1)
            (((oneLambdaSig A).args o).get j).2),
        t = (hs ▸ Binding.Tm.op (S := oneLambdaSig A) o args
              : Binding.Tm (oneLambdaSig A) y.1 y.2) from haux t
  intro y t
  cases t with
  | mk y idx children =>
    cases idx with
    | inl a =>
      refine Or.inl ⟨Binding.leafVar a, ?_⟩
      obtain ⟨⟨Γ', i'⟩, rfl⟩ := a
      congr 1
      funext e
      exact e.elim
    | inr p =>
      obtain ⟨Γ', s'⟩ := y
      change { o : OneLambdaOp A // (oneLambdaSig A).result o = s' } at p
      revert children
      obtain ⟨o, rfl⟩ := p
      intro children
      exact Or.inr ⟨o, rfl, fun j => children ⟨j⟩, rfl⟩

/-- The operation node behind a `headTag` value: a term whose head tag is
`some o` is an operation node at `o`, its sort the transported result sort of
`o`. The inversion consumed by the redex-shape recognitions. -/
private theorem exists_op_of_headTag {Γ : Binding.Ctx RType} {s : RType}
    {t : Binding.Tm (oneLambdaSig A) Γ s} {o : OneLambdaOp A} (h : headTag t = some o) :
    ∃ (hs : (oneLambdaSig A).result o = s)
      (args : ∀ j : Fin (((oneLambdaSig A).args o).length),
        Binding.Tm (oneLambdaSig A) (Γ ++ (((oneLambdaSig A).args o).get j).1)
          (((oneLambdaSig A).args o).get j).2),
      t = (hs ▸ Binding.Tm.op (S := oneLambdaSig A) o args
            : Binding.Tm (oneLambdaSig A) Γ s) := by
  rcases tm_cases t with ⟨x, rfl⟩ | ⟨o', hs, args, rfl⟩
  · rw [headTag_var] at h
    simp at h
  · have ho : o' = o := by
      have := (headTag_cast rfl hs (Binding.Tm.op (S := oneLambdaSig A) o' args)).symm.trans h
      rw [headTag_op] at this
      exact Option.some.inj this
    subst ho
    exact ⟨hs, args, rfl⟩

/-- An r-type of shape `o` is the base type `o`: the nullary shape determines
the node. -/
private theorem eq_o_of_shape_o {s : RType} (h : s.shape = RTypeShape.o) : s = RType.o := by
  rcases s with ⟨_, i, children⟩
  have hi : i = RTypeShape.o := h
  subst hi
  change FreeAlg.mk (A := rTypeSig) RTypeShape.o children = RType.o
  exact congrArg (FreeAlg.mk (A := rTypeSig) RTypeShape.o) (funext fun e => e.elim0)

/-- An arrow type is not the base type `o`: their shapes differ. -/
private theorem arrow_ne_o (σ τ : RType) : RType.arrow σ τ ≠ RType.o := fun hcon => by
  have := congrArg RType.shape hcon
  simp at this

/-- The curried sort of a homogeneous spine absorbs one further `o`-argument of
its result sort: `o^n → (o → ρ) = o^{n+1} → ρ`. The sort-level bookkeeping of
`replicateSpine_snoc`. -/
private theorem curried_replicate_snoc (n : ℕ) (ρ : RType) :
    RType.curried (List.replicate n RType.o) (RType.arrow RType.o ρ)
      = RType.curried (List.replicate (n + 1) RType.o) ρ := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (RType.arrow RType.o) ih

/-- Sort transport of a term, packaged as a definition so that its source and
target sorts are pinned by the equality proof's type and cast-commutation
lemmas match syntactically. -/
private def castSort {Γ : Binding.Ctx RType} {s s' : RType} (h : s = s')
    (t : Binding.Tm (oneLambdaSig A) Γ s) : Binding.Tm (oneLambdaSig A) Γ s' := h ▸ t

/-- Transport along a self-equality is the identity, by proof irrelevance. -/
private theorem castSort_self {Γ : Binding.Ctx RType} {s : RType} (h : s = s)
    (t : Binding.Tm (oneLambdaSig A) Γ s) : castSort h t = t := rfl

/-- Transport along a composite of sort equalities is the transport along the
composite equality. -/
private theorem castSort_trans {Γ : Binding.Ctx RType} {a b c : RType} (h₁ : a = b) (h₂ : b = c)
    (t : Binding.Tm (oneLambdaSig A) Γ a) :
    castSort h₂ (castSort h₁ t) = castSort (h₁.trans h₂) t := by
  cases h₂; rfl

/-- An application whose function is transported in its codomain sort is the
transport of the application: `app'` commutes with a codomain cast. -/
private theorem app'_castSort {Γ : Binding.Ctx RType} {σ τ τ' : RType} (hτ : τ = τ')
    (harr : RType.arrow σ τ = RType.arrow σ τ')
    (f : Binding.Tm (oneLambdaSig A) Γ (RType.arrow σ τ))
    (x : Binding.Tm (oneLambdaSig A) Γ σ) :
    app' (castSort harr f) x = castSort hτ (app' f x) := by
  cases hτ; rfl

/-- The function subterm of an application is no larger than the application. -/
private theorem size_le_size_app' {Γ : Binding.Ctx RType} {σ τ : RType}
    (f : Binding.Tm (oneLambdaSig A) Γ (RType.arrow σ τ))
    (x : Binding.Tm (oneLambdaSig A) Γ σ) : Tm.size f ≤ Tm.size (app' f x) := by
  rw [size_app']; omega

/-- The argument subterm of an application is strictly smaller than the
application. -/
private theorem size_arg_lt_size_app' {Γ : Binding.Ctx RType} {σ τ : RType}
    (f : Binding.Tm (oneLambdaSig A) Γ (RType.arrow σ τ))
    (x : Binding.Tm (oneLambdaSig A) Γ σ) : Tm.size x < Tm.size (app' f x) := by
  rw [size_app']
  have := Tm.one_le_size f
  omega

/-- The function subterm of an application is no taller than the application. -/
private theorem height_le_height_app' {Γ : Binding.Ctx RType} {σ τ : RType}
    (f : Binding.Tm (oneLambdaSig A) Γ (RType.arrow σ τ))
    (x : Binding.Tm (oneLambdaSig A) Γ σ) : Tm.height f ≤ Tm.height (app' f x) := by
  rw [height_app']; omega

/-- The argument subterm of an application sits strictly below the application's
height. -/
private theorem height_arg_lt_height_app' {Γ : Binding.Ctx RType} {σ τ : RType}
    (f : Binding.Tm (oneLambdaSig A) Γ (RType.arrow σ τ))
    (x : Binding.Tm (oneLambdaSig A) Γ σ) : Tm.height x < Tm.height (app' f x) := by
  rw [height_app']; omega

/-- The β-rank of the function subterm of an application is bounded by the
application's β-rank. -/
private theorem betaRedexRank_le_betaRedexRank_app' {Γ : Binding.Ctx RType} {σ τ : RType}
    (f : Binding.Tm (oneLambdaSig A) Γ (RType.arrow σ τ))
    (x : Binding.Tm (oneLambdaSig A) Γ σ) :
    betaRedexRank f ≤ betaRedexRank (app' f x) := by
  rw [betaRedexRank_app']; omega

/-- The β-rank of the argument subterm of an application is bounded by the
application's β-rank. -/
private theorem betaRedexRank_arg_le_betaRedexRank_app' {Γ : Binding.Ctx RType} {σ τ : RType}
    (f : Binding.Tm (oneLambdaSig A) Γ (RType.arrow σ τ))
    (x : Binding.Tm (oneLambdaSig A) Γ σ) :
    betaRedexRank x ≤ betaRedexRank (app' f x) := by
  rw [betaRedexRank_app']; omega

/-- Peeling the first argument of a homogeneous spine: an `(n+1)`-argument spine
is the `n`-argument spine over the head applied to the first argument. -/
private theorem replicateSpine_cons {Γ : Binding.Ctx RType} {result : RType} (n : ℕ)
    (base : RType)
    (head : Binding.Tm (oneLambdaSig A) Γ (RType.curried (List.replicate (n + 1) base) result))
    (a : Fin (n + 1) → Binding.Tm (oneLambdaSig A) Γ base) :
    replicateSpine (n + 1) base head a
      = replicateSpine n base
          (app' (σ := base) (τ := RType.curried (List.replicate n base) result) head
            (a ⟨0, n.succ_pos⟩))
          (fun i => a i.succ) := rfl

/-- The last-index composite of a `Fin.snoc` with the successor embedding is the
`Fin.snoc` of the composite: reading a snoc-extended tuple at shifted indices
drops the first entry. -/
private theorem fin_snoc_comp_succ {n : ℕ} {C : Sort _} (a : Fin (n + 1) → C) (w : C) :
    (fun i : Fin (n + 1) => Fin.snoc (α := fun _ => C) a w i.succ)
      = Fin.snoc (α := fun _ => C) (fun i => a i.succ) w := by
  funext i
  induction i using Fin.lastCases with
  | last => simp [Fin.succ_last]
  | cast i => simp only [Fin.succ_castSucc, Fin.snoc_castSucc]

/-- Appending one further argument to a homogeneous spine: applying an
`n`-argument spine to one more base-sort argument is the `(n+1)`-argument spine
at the sort-transported head over the `Fin.snoc`-extended argument tuple. -/
private theorem replicateSpine_snoc {Γ : Binding.Ctx RType} {ρ : RType} :
    (n : ℕ) →
    (head : Binding.Tm (oneLambdaSig A) Γ
      (RType.curried (List.replicate n RType.o) (RType.arrow RType.o ρ))) →
    (a : Fin n → Binding.Tm (oneLambdaSig A) Γ RType.o) →
    (w : Binding.Tm (oneLambdaSig A) Γ RType.o) →
    app' (replicateSpine n RType.o head a) w
      = replicateSpine (n + 1) RType.o (castSort (curried_replicate_snoc n ρ) head)
          (Fin.snoc a w)
  | 0, head, a, w => rfl
  | n + 1, head, a, w => by
      calc app' (replicateSpine (n + 1) RType.o head a) w
          = app' (replicateSpine n RType.o
              (app' (σ := RType.o) head (a ⟨0, n.succ_pos⟩)) (fun i => a i.succ)) w := by
            rw [replicateSpine_cons]
        _ = replicateSpine (n + 1) RType.o
              (castSort (curried_replicate_snoc n ρ)
                (app' (σ := RType.o) head (a ⟨0, n.succ_pos⟩)))
              (Fin.snoc (fun i => a i.succ) w) :=
            replicateSpine_snoc n _ _ w
        _ = replicateSpine (n + 1) RType.o
              (app' (σ := RType.o) (castSort (curried_replicate_snoc (n + 1) ρ) head)
                (a ⟨0, n.succ_pos⟩))
              (Fin.snoc (fun i => a i.succ) w) :=
            congrArg
              (fun H => replicateSpine (n + 1) RType.o H (Fin.snoc (fun i => a i.succ) w))
              (app'_castSort (curried_replicate_snoc n ρ)
                (curried_replicate_snoc (n + 1) ρ) head (a ⟨0, n.succ_pos⟩)).symm
        _ = replicateSpine (n + 1 + 1) RType.o
              (castSort (curried_replicate_snoc (n + 1) ρ) head) (Fin.snoc a w) := by
            rw [replicateSpine_cons (n + 1) RType.o
              (castSort (curried_replicate_snoc (n + 1) ρ) head) (Fin.snoc a w),
              fin_snoc_comp_succ]
            rfl

/-- The head of a homogeneous spine is no larger than the spine. -/
private theorem size_head_le_replicateSpine {Γ : Binding.Ctx RType} {result : RType} :
    (n : ℕ) → (base : RType) →
    (head : Binding.Tm (oneLambdaSig A) Γ (RType.curried (List.replicate n base) result)) →
    (a : Fin n → Binding.Tm (oneLambdaSig A) Γ base) →
    Tm.size head ≤ Tm.size (replicateSpine n base head a)
  | 0, _base, _head, _a => le_refl _
  | n + 1, base, head, a => by
      rw [replicateSpine_cons]
      exact le_trans (size_le_size_app' head (a ⟨0, n.succ_pos⟩))
        (size_head_le_replicateSpine n base _ _)

/-- Every argument of a homogeneous spine is strictly smaller than the spine. -/
private theorem size_arg_lt_replicateSpine {Γ : Binding.Ctx RType} {result : RType} :
    (n : ℕ) → (base : RType) →
    (head : Binding.Tm (oneLambdaSig A) Γ (RType.curried (List.replicate n base) result)) →
    (a : Fin n → Binding.Tm (oneLambdaSig A) Γ base) → (i : Fin n) →
    Tm.size (a i) < Tm.size (replicateSpine n base head a)
  | n + 1, base, head, a, ⟨0, _⟩ => by
      rw [replicateSpine_cons]
      exact lt_of_lt_of_le (size_arg_lt_size_app' head (a ⟨0, n.succ_pos⟩))
        (size_head_le_replicateSpine n base _ _)
  | n + 1, base, head, a, ⟨iv + 1, hi⟩ => by
      rw [replicateSpine_cons]
      exact size_arg_lt_replicateSpine n base _ (fun i => a i.succ)
        ⟨iv, Nat.lt_of_succ_lt_succ hi⟩

/-- The head of a homogeneous spine is no taller than the spine. -/
private theorem height_head_le_replicateSpine {Γ : Binding.Ctx RType} {result : RType} :
    (n : ℕ) → (base : RType) →
    (head : Binding.Tm (oneLambdaSig A) Γ (RType.curried (List.replicate n base) result)) →
    (a : Fin n → Binding.Tm (oneLambdaSig A) Γ base) →
    Tm.height head ≤ Tm.height (replicateSpine n base head a)
  | 0, _base, _head, _a => le_refl _
  | n + 1, base, head, a => by
      rw [replicateSpine_cons]
      exact le_trans (height_le_height_app' head (a ⟨0, n.succ_pos⟩))
        (height_head_le_replicateSpine n base _ _)

/-- Every argument of a homogeneous spine sits strictly below the spine's
height. -/
private theorem height_arg_lt_replicateSpine {Γ : Binding.Ctx RType} {result : RType} :
    (n : ℕ) → (base : RType) →
    (head : Binding.Tm (oneLambdaSig A) Γ (RType.curried (List.replicate n base) result)) →
    (a : Fin n → Binding.Tm (oneLambdaSig A) Γ base) → (i : Fin n) →
    Tm.height (a i) < Tm.height (replicateSpine n base head a)
  | n + 1, base, head, a, ⟨0, _⟩ => by
      rw [replicateSpine_cons]
      exact lt_of_lt_of_le (height_arg_lt_height_app' head (a ⟨0, n.succ_pos⟩))
        (height_head_le_replicateSpine n base _ _)
  | n + 1, base, head, a, ⟨iv + 1, hi⟩ => by
      rw [replicateSpine_cons]
      exact height_arg_lt_replicateSpine n base _ (fun i => a i.succ)
        ⟨iv, Nat.lt_of_succ_lt_succ hi⟩

/-- The β-rank of the head of a homogeneous spine is bounded by the spine's
β-rank. -/
private theorem betaRedexRank_head_le_replicateSpine {Γ : Binding.Ctx RType} {result : RType} :
    (n : ℕ) → (base : RType) →
    (head : Binding.Tm (oneLambdaSig A) Γ (RType.curried (List.replicate n base) result)) →
    (a : Fin n → Binding.Tm (oneLambdaSig A) Γ base) →
    betaRedexRank head ≤ betaRedexRank (replicateSpine n base head a)
  | 0, _base, _head, _a => le_refl _
  | n + 1, base, head, a => by
      rw [replicateSpine_cons]
      exact le_trans (betaRedexRank_le_betaRedexRank_app' head (a ⟨0, n.succ_pos⟩))
        (betaRedexRank_head_le_replicateSpine n base _ _)

/-- The β-rank of every argument of a homogeneous spine is bounded by the
spine's β-rank. -/
private theorem betaRedexRank_arg_le_replicateSpine {Γ : Binding.Ctx RType} {result : RType} :
    (n : ℕ) → (base : RType) →
    (head : Binding.Tm (oneLambdaSig A) Γ (RType.curried (List.replicate n base) result)) →
    (a : Fin n → Binding.Tm (oneLambdaSig A) Γ base) → (i : Fin n) →
    betaRedexRank (a i) ≤ betaRedexRank (replicateSpine n base head a)
  | n + 1, base, head, a, ⟨0, _⟩ => by
      rw [replicateSpine_cons]
      exact le_trans (betaRedexRank_arg_le_betaRedexRank_app' head (a ⟨0, n.succ_pos⟩))
        (betaRedexRank_head_le_replicateSpine n base _ _)
  | n + 1, base, head, a, ⟨iv + 1, hi⟩ => by
      rw [replicateSpine_cons]
      exact betaRedexRank_arg_le_replicateSpine n base _ (fun i => a i.succ)
        ⟨iv, Nat.lt_of_succ_lt_succ hi⟩

/-- The generalized constructor-spine inversion (Leivant III section 4.3's
head-form observation), tracking the pending-argument count: a `conHeaded` term
of sort `o^k → o` is a constructor constant `con i` applied along an
application spine to `n` arguments of sort `o`, with `A.ar i = n + k`. The
intrinsic sorts force the count bookkeeping; the sort transports record the
curried-sort arithmetic. By strong induction on the term size. -/
private theorem conHeaded_inv_aux :
    (N : ℕ) → ∀ {Γ : Binding.Ctx RType} {s : RType} (t : Binding.Tm (oneLambdaSig A) Γ s),
    Tm.size t ≤ N → conHeaded t = true →
    ∃ (i : A.B) (n k : ℕ) (_ : A.ar i = n + k)
      (hs : s = RType.curried (List.replicate k RType.o) RType.o)
      (hh : RType.curried (List.replicate (A.ar i) RType.o) RType.o
          = RType.curried (List.replicate n RType.o)
              (RType.curried (List.replicate k RType.o) RType.o))
      (a : Fin n → Binding.Tm (oneLambdaSig A) Γ RType.o),
      t = castSort hs.symm (replicateSpine n RType.o
            (castSort hh (Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.con i)
              (fun l => l.elim0))) a)
  | 0, _, _, t, hN, _ => absurd (Tm.one_le_size t) (by omega)
  | N + 1, Γ, s, t, hN, h => by
      rcases tm_cases t with ⟨x0, ht⟩ | ⟨o, hs0, args, ht⟩
      · subst ht
        rw [conHeaded_var] at h
        simp at h
      · cases o with
        | app σ τ =>
            have hs1 : τ = s := hs0
            subst hs1
            replace ht : t = Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.app σ τ) args :=
              ht
            obtain ⟨f, x, hfx⟩ := op_app_inv args
            rw [hfx] at ht
            subst ht
            rw [size_app'] at hN
            rw [conHeaded_app'] at h
            obtain ⟨i, n, k, hnk, hsf, hh, a, hf⟩ := conHeaded_inv_aux N f (by omega) h
            cases k with
            | zero =>
                rw [List.replicate_zero, RType.curried_nil] at hsf
                exact absurd hsf (arrow_ne_o σ τ)
            | succ k' =>
                have hsf' := hsf
                rw [List.replicate_succ, RType.curried_cons, RType.arrow_eq_arrow] at hsf'
                obtain ⟨hσ, hτ⟩ := hsf'
                subst hσ
                subst hτ
                replace hf : f = replicateSpine n RType.o
                    (castSort hh (Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.con i)
                      (fun l => l.elim0))) a := hf
                refine ⟨i, n + 1, k', by omega, rfl,
                  hh.trans (curried_replicate_snoc n
                    (RType.curried (List.replicate k' RType.o) RType.o)),
                  Fin.snoc a x, ?_⟩
                rw [hf]
                exact (replicateSpine_snoc n _ a x).trans
                  (congrArg (fun H => replicateSpine (n + 1) RType.o H (Fin.snoc a x))
                    (castSort_trans hh (curried_replicate_snoc n _) _))
        | lam σ τ =>
            have hs1 : RType.arrow σ τ = s := hs0
            subst hs1
            replace ht : t = Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.lam σ τ) args :=
              ht
            subst ht
            replace h : false = true := h
            exact Bool.noConfusion h
        | con i =>
            have hs1 : RType.curried (List.replicate (A.ar i) RType.o) RType.o = s := hs0
            subst hs1
            replace ht : t = Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.con i) args :=
              ht
            subst ht
            refine ⟨i, 0, A.ar i, (Nat.zero_add _).symm, rfl, rfl, fun l => l.elim0, ?_⟩
            change Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.con i) args
              = Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.con i) fun l => l.elim0
            exact congrArg _ (funext fun j => j.elim0)
        | dstr j =>
            have hs1 : RType.arrow RType.o RType.o = s := hs0
            subst hs1
            replace ht : t = Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.dstr j) args :=
              ht
            subst ht
            replace h : false = true := h
            exact Bool.noConfusion h
        | case =>
            have hs1 : RType.arrow RType.o
                (RType.curried (List.replicate A.numCtors RType.o) RType.o) = s := hs0
            subst hs1
            replace ht : t = Binding.Tm.op (S := oneLambdaSig A) OneLambdaOp.case args := ht
            subst ht
            replace h : false = true := h
            exact Bool.noConfusion h

/-- The constructor-headed inversion at the base sort (Leivant III section
4.3's head-form observation): a `conHeaded` term of sort `o` is a constructor
constant applied to a full argument tuple — `con`-headedness at sort `o`
implies saturation through the intrinsic sorts. -/
private theorem conHeaded_o_inv {Γ : Binding.Ctx RType}
    {x : Binding.Tm (oneLambdaSig A) Γ RType.o} (h : conHeaded x = true) :
    ∃ (i : A.B) (a : Fin (A.ar i) → Binding.Tm (oneLambdaSig A) Γ RType.o),
      x = replicateSpine (A.ar i) RType.o
          (Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.con i) (fun l => l.elim0)) a := by
  obtain ⟨i, n, k, hnk, hs, hh, a, hx⟩ := conHeaded_inv_aux (Tm.size x) x le_rfl h
  cases k with
  | succ k' =>
      have hs' := hs
      rw [List.replicate_succ, RType.curried_cons] at hs'
      exact absurd hs'.symm (arrow_ne_o _ _)
  | zero =>
      have hn : A.ar i = n := hnk
      subst hn
      exact ⟨i, a, hx⟩

/-- The ι-spine inversion (Leivant III section 4.2, p. 224), tracking the
pending-argument count: a term whose `iotaSpine` detector fires is either a
destructor applied to a `con`-headed scrutinee — necessarily at sort `o` — or
a case combinator applied to a `con`-headed scrutinee and then, along the
application spine, to `n` branch arguments with `A.numCtors = n + k` pending.
By strong induction on the term size; the sort transports record the
curried-sort arithmetic. -/
private theorem iotaSpine_inv_aux :
    (N : ℕ) → ∀ {Γ : Binding.Ctx RType} {s : RType} (t : Binding.Tm (oneLambdaSig A) Γ s),
    Tm.size t ≤ N → iotaSpine t = true →
    (∃ (j : Fin A.maxArity) (w : Binding.Tm (oneLambdaSig A) Γ RType.o) (hs : s = RType.o),
      conHeaded w = true ∧
      t = castSort hs.symm (app' (Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.dstr j)
            (fun l => l.elim0)) w)) ∨
    (∃ (n k : ℕ) (_ : A.numCtors = n + k)
      (hs : s = RType.curried (List.replicate k RType.o) RType.o)
      (hh : RType.arrow RType.o (RType.curried (List.replicate A.numCtors RType.o) RType.o)
          = RType.arrow RType.o (RType.curried (List.replicate n RType.o)
              (RType.curried (List.replicate k RType.o) RType.o)))
      (scrut : Binding.Tm (oneLambdaSig A) Γ RType.o)
      (b : Fin n → Binding.Tm (oneLambdaSig A) Γ RType.o),
      conHeaded scrut = true ∧
      t = castSort hs.symm (replicateSpine n RType.o
            (app' (castSort hh (Binding.Tm.op (S := oneLambdaSig A) OneLambdaOp.case
              (fun l => l.elim0))) scrut) b))
  | 0, _, _, t, hN, _ => absurd (Tm.one_le_size t) (by omega)
  | N + 1, Γ, s, t, hN, h => by
      rcases tm_cases t with ⟨x0, ht⟩ | ⟨o, hs0, args, ht⟩
      · subst ht
        rw [iotaSpine_var] at h
        simp at h
      · cases o with
        | app σ τ =>
            have hs1 : τ = s := hs0
            subst hs1
            replace ht : t = Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.app σ τ) args :=
              ht
            obtain ⟨f, x, hfx⟩ := op_app_inv args
            rw [hfx] at ht
            subst ht
            rw [size_app'] at hN
            rw [iotaSpine_app'] at h
            rcases hhf : headTag f with _ | o'
            · rw [hhf] at h
              replace h : false = true := h
              exact Bool.noConfusion h
            · rw [hhf] at h
              cases o' with
              | app σ' τ' =>
                  replace h : iotaSpine f = true := h
                  rcases iotaSpine_inv_aux N f (by omega) h with
                    ⟨j, w, hso, hcw, hfA⟩ | ⟨n, k, hnk, hsB, hh, scrut, b, hcs, hfB⟩
                  · exact absurd hso (arrow_ne_o σ τ)
                  · cases k with
                    | zero =>
                        rw [List.replicate_zero, RType.curried_nil] at hsB
                        exact absurd hsB (arrow_ne_o σ τ)
                    | succ k' =>
                        have hsB' := hsB
                        rw [List.replicate_succ, RType.curried_cons,
                          RType.arrow_eq_arrow] at hsB'
                        obtain ⟨hσ, hτ⟩ := hsB'
                        subst hσ
                        subst hτ
                        replace hfB : f = replicateSpine n RType.o
                            (app' (castSort hh (Binding.Tm.op (S := oneLambdaSig A)
                              OneLambdaOp.case (fun l => l.elim0))) scrut) b := hfB
                        refine Or.inr ⟨n + 1, k', by omega, rfl,
                          hh.trans (congrArg (RType.arrow RType.o)
                            (curried_replicate_snoc n
                              (RType.curried (List.replicate k' RType.o) RType.o))),
                          scrut, Fin.snoc b x, hcs, ?_⟩
                        rw [hfB]
                        refine (replicateSpine_snoc n _ b x).trans ?_
                        refine congrArg
                          (fun H => replicateSpine (n + 1) RType.o H (Fin.snoc b x)) ?_
                        refine (app'_castSort (curried_replicate_snoc n _)
                          (congrArg (RType.arrow RType.o) (curried_replicate_snoc n _))
                          (castSort hh (Binding.Tm.op (S := oneLambdaSig A) OneLambdaOp.case
                            (fun l => l.elim0))) scrut).symm.trans ?_
                        exact congrArg (fun F => app' F scrut)
                          (castSort_trans hh (congrArg (RType.arrow RType.o)
                            (curried_replicate_snoc n
                              (RType.curried (List.replicate k' RType.o) RType.o)))
                            (Binding.Tm.op (S := oneLambdaSig A) OneLambdaOp.case
                              (fun l => l.elim0)))
              | dstr j =>
                  replace h : conHeaded x = true := h
                  obtain ⟨hsd, args', hfd⟩ := exists_op_of_headTag hhf
                  replace hsd : RType.arrow RType.o RType.o = RType.arrow σ τ := hsd
                  rw [RType.arrow_eq_arrow] at hsd
                  obtain ⟨hσ, hτ⟩ := hsd
                  subst hσ
                  subst hτ
                  refine Or.inl ⟨j, x, rfl, h, ?_⟩
                  replace hfd : f = Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.dstr j)
                      args' := hfd
                  rw [hfd]
                  refine congrArg (fun F => app' F x) ?_
                  change Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.dstr j) args'
                    = Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.dstr j)
                        fun l => l.elim0
                  exact congrArg _ (funext fun l => l.elim0)
              | case =>
                  replace h : conHeaded x = true := h
                  obtain ⟨hsc, args', hfc⟩ := exists_op_of_headTag hhf
                  replace hsc : RType.arrow RType.o (RType.curried
                      (List.replicate A.numCtors RType.o) RType.o) = RType.arrow σ τ := hsc
                  rw [RType.arrow_eq_arrow] at hsc
                  obtain ⟨hσ, hτ⟩ := hsc
                  subst hσ
                  subst hτ
                  refine Or.inr ⟨0, A.numCtors, (Nat.zero_add _).symm, rfl, rfl, x,
                    fun l => l.elim0, h, ?_⟩
                  replace hfc : f = Binding.Tm.op (S := oneLambdaSig A) OneLambdaOp.case
                      args' := hfc
                  rw [hfc]
                  refine congrArg (fun F => app' F x) ?_
                  change Binding.Tm.op (S := oneLambdaSig A) OneLambdaOp.case args'
                    = Binding.Tm.op (S := oneLambdaSig A) OneLambdaOp.case fun l => l.elim0
                  exact congrArg _ (funext fun l => l.elim0)
              | lam σ' τ' =>
                  replace h : false = true := h
                  exact Bool.noConfusion h
              | con i =>
                  replace h : false = true := h
                  exact Bool.noConfusion h
        | lam σ τ =>
            have hs1 : RType.arrow σ τ = s := hs0
            subst hs1
            replace ht : t = Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.lam σ τ) args :=
              ht
            subst ht
            replace h : false = true := h
            exact Bool.noConfusion h
        | con i =>
            have hs1 : RType.curried (List.replicate (A.ar i) RType.o) RType.o = s := hs0
            subst hs1
            replace ht : t = Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.con i) args :=
              ht
            subst ht
            replace h : false = true := h
            exact Bool.noConfusion h
        | dstr j =>
            have hs1 : RType.arrow RType.o RType.o = s := hs0
            subst hs1
            replace ht : t = Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.dstr j) args :=
              ht
            subst ht
            replace h : false = true := h
            exact Bool.noConfusion h
        | case =>
            have hs1 : RType.arrow RType.o
                (RType.curried (List.replicate A.numCtors RType.o) RType.o) = s := hs0
            subst hs1
            replace ht : t = Binding.Tm.op (S := oneLambdaSig A) OneLambdaOp.case args := ht
            subst ht
            replace h : false = true := h
            exact Bool.noConfusion h

/-- The base type is not a curried sort with pending arguments: `o = o^k → o`
forces `k = 0`. -/
private theorem eq_zero_of_o_eq_curried {k : ℕ}
    (h : RType.o = RType.curried (List.replicate k RType.o) RType.o) : k = 0 := by
  cases k with
  | zero => rfl
  | succ k' =>
      rw [List.replicate_succ, RType.curried_cons] at h
      exact absurd h.symm (arrow_ne_o _ _)

/-- Every constructor label appears in the sorted enumeration: `ctorAt` is
surjective. -/
private theorem exists_ctorAt_eq [LinearOrder A.B] (i : A.B) :
    ∃ idx : Fin A.numCtors, ctorAt idx = i := by
  have hmem : i ∈ ctorList A := by
    unfold ctorList
    exact (Finset.mem_sort _).mpr (Finset.mem_univ i)
  obtain ⟨m, hm⟩ := List.get_of_mem hmem
  exact ⟨m.cast ctorList_length, hm⟩

/-- The strengthened induction form of `exists_iota_step_of_hasIota` (plan note
N6): the extra final clause — a step inside a term of non-`o` sort preserves
the `isLam` head flag — closes the `appL` congruence case, where β-normality
of the rewritten application requires the stepped function subterm not to
become an abstraction. By strong induction on the term size. -/
private theorem exists_iota_step_aux [LinearOrder A.B] :
    (N : ℕ) → ∀ {Γ : Binding.Ctx RType} {s : RType} (t : Binding.Tm (oneLambdaSig A) Γ s),
    Tm.size t ≤ N → hasIota t = true → betaRedexRank t = 0 →
    ∃ t', OneLambdaStep t t' ∧ Tm.size t' < Tm.size t ∧ Tm.height t' ≤ Tm.height t ∧
      betaRedexRank t' = 0 ∧ (s.shape ≠ RTypeShape.o → isLam t' = isLam t)
  | 0, _, _, t, hN, _, _ => absurd (Tm.one_le_size t) (by omega)
  | N + 1, Γ, s, t, hN, h, hβ => by
      rcases tm_cases t with ⟨x0, ht⟩ | ⟨o, hs0, args, ht⟩
      · subst ht
        rw [hasIota_var] at h
        simp at h
      · cases o with
        | lam σ τ =>
            have hs1 : RType.arrow σ τ = s := hs0
            subst hs1
            replace ht : t = Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.lam σ τ) args :=
              ht
            obtain ⟨b, hb⟩ := op_lam_inv args
            rw [hb] at ht
            subst ht
            rw [size_lam'] at hN
            rw [hasIota_lam'] at h
            rw [betaRedexRank_lam'] at hβ
            obtain ⟨b', hstep, hsz, hht, hβ', _⟩ := exists_iota_step_aux N b (by omega) h hβ
            refine ⟨lam' b', OneLambdaStep.lamBody hstep, ?_, ?_, ?_, fun _ => rfl⟩
            · rw [size_lam', size_lam']; omega
            · rw [height_lam', height_lam']; omega
            · rw [betaRedexRank_lam']; exact hβ'
        | con i =>
            have hs1 : RType.curried (List.replicate (A.ar i) RType.o) RType.o = s := hs0
            subst hs1
            replace ht : t = Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.con i) args :=
              ht
            subst ht
            have hfalse : hasIota (Binding.Tm.op (S := oneLambdaSig A) (Γ := Γ)
                (OneLambdaOp.con i) args) = false := by
              rw [hasIota_op]
              simp only [topIota, iotaSpine_op, iotaSpineOp, ite_self, Bool.false_or]
              rfl
            exact Bool.noConfusion (hfalse.symm.trans h)
        | dstr j =>
            have hs1 : RType.arrow RType.o RType.o = s := hs0
            subst hs1
            replace ht : t = Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.dstr j) args :=
              ht
            subst ht
            have hfalse : hasIota (Binding.Tm.op (S := oneLambdaSig A) (Γ := Γ)
                (OneLambdaOp.dstr j) args) = false := by
              rw [hasIota_op]
              simp only [topIota, iotaSpine_op, iotaSpineOp, ite_self, Bool.false_or]
              rfl
            exact Bool.noConfusion (hfalse.symm.trans h)
        | case =>
            have hs1 : RType.arrow RType.o
                (RType.curried (List.replicate A.numCtors RType.o) RType.o) = s := hs0
            subst hs1
            replace ht : t = Binding.Tm.op (S := oneLambdaSig A) OneLambdaOp.case args := ht
            subst ht
            have hfalse : hasIota (Binding.Tm.op (S := oneLambdaSig A) (Γ := Γ)
                OneLambdaOp.case args) = false := by
              rw [hasIota_op]
              simp only [topIota, iotaSpine_op, iotaSpineOp, ite_self, Bool.false_or]
              rfl
            exact Bool.noConfusion (hfalse.symm.trans h)
        | app σ τ =>
            have hs1 : τ = s := hs0
            subst hs1
            replace ht : t = Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.app σ τ) args :=
              ht
            obtain ⟨f, x, hfx⟩ := op_app_inv args
            rw [hfx] at ht
            subst ht
            rw [size_app'] at hN
            rw [hasIota_app'] at h
            cases htop : topIota (app' f x) with
            | false =>
                rw [htop, Bool.false_or] at h
                have hβ2 := hβ
                rw [betaRedexRank_app'] at hβ2
                have hβf : betaRedexRank f = 0 := by omega
                have hβx : betaRedexRank x = 0 := by omega
                have htb : topBetaRank (app' f x) = 0 := by omega
                cases hfio : hasIota f with
                | true =>
                    have hLf : isLam f = false := by
                      rw [topBetaRank_app'] at htb
                      cases hLf' : isLam f with
                      | false => rfl
                      | true =>
                          rw [hLf'] at htb
                          rw [if_pos rfl] at htb
                          have := RType.one_le_ord_arrow σ τ
                          omega
                    obtain ⟨f', hstep, hsz, hht, hβ', hLam⟩ :=
                      exists_iota_step_aux N f (by omega) hfio hβf
                    have hLf' : isLam f' = false := (hLam (by simp)).trans hLf
                    refine ⟨app' f' x, OneLambdaStep.appL x hstep, ?_, ?_, ?_, fun _ => rfl⟩
                    · rw [size_app', size_app']; omega
                    · rw [height_app', height_app']; omega
                    · rw [betaRedexRank_app', topBetaRank_app', hLf']
                      rw [if_neg (by simp)]
                      omega
                | false =>
                    rw [hfio, Bool.false_or] at h
                    obtain ⟨x', hstep, hsz, hht, hβ', _⟩ :=
                      exists_iota_step_aux N x (by omega) h hβx
                    refine ⟨app' f x', OneLambdaStep.appR f hstep, ?_, ?_, ?_, fun _ => rfl⟩
                    · rw [size_app', size_app']; omega
                    · rw [height_app', height_app']; omega
                    · rw [betaRedexRank_app']
                      have htb' : topBetaRank (app' f x') = topBetaRank (app' f x) := by
                        rw [topBetaRank_app', topBetaRank_app']
                      omega
            | true =>
                have hsh : τ.shape = RTypeShape.o := by
                  by_contra hcon
                  unfold topIota at htop
                  rw [if_neg hcon] at htop
                  simp at htop
                have hτo := eq_o_of_shape_o hsh
                subst hτo
                have hio : iotaSpine (app' f x) = true := by
                  unfold topIota at htop
                  rwa [if_pos hsh] at htop
                rcases iotaSpine_inv_aux (Tm.size (app' f x)) (app' f x) le_rfl hio with
                  ⟨j, w, hso, hcw, htEq⟩ | ⟨n, k, hnk, hsB, hh, scrut, b, hcs, htEq⟩
                · -- destructor redex
                  replace htEq : app' f x = app'
                      (Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.dstr j)
                        (fun l => l.elim0)) w := htEq
                  obtain ⟨i, a, hwEq⟩ := conHeaded_o_inv hcw
                  rw [hwEq] at htEq
                  rw [htEq] at hβ ⊢
                  rcases Nat.lt_or_ge j.val (A.ar i) with hj | hj
                  · refine ⟨a ⟨j.val, hj⟩, OneLambdaStep.dstrHit j hj a, ?_, ?_, ?_,
                      fun habs => absurd rfl habs⟩
                    · exact lt_trans
                        (size_arg_lt_replicateSpine (A.ar i) RType.o _ a ⟨j.val, hj⟩)
                        (size_arg_lt_size_app' _ _)
                    · exact le_of_lt (lt_trans
                        (height_arg_lt_replicateSpine (A.ar i) RType.o _ a ⟨j.val, hj⟩)
                        (height_arg_lt_height_app' _ _))
                    · exact Nat.le_zero.mp
                        (((betaRedexRank_arg_le_replicateSpine (A.ar i) RType.o _ a
                            ⟨j.val, hj⟩).trans
                          (betaRedexRank_arg_le_betaRedexRank_app' _ _)).trans
                          (le_of_eq hβ))
                  · refine ⟨_, OneLambdaStep.dstrMiss j hj a, ?_, ?_, ?_,
                      fun habs => absurd rfl habs⟩
                    · exact size_arg_lt_size_app' _ _
                    · exact le_of_lt (height_arg_lt_height_app' _ _)
                    · exact Nat.le_zero.mp
                        ((betaRedexRank_arg_le_betaRedexRank_app' _ _).trans (le_of_eq hβ))
                · -- case redex
                  have hk : k = 0 := eq_zero_of_o_eq_curried hsB
                  subst hk
                  have hn : A.numCtors = n := hnk
                  subst hn
                  replace htEq : app' f x = replicateSpine A.numCtors RType.o
                      (app' (Binding.Tm.op (S := oneLambdaSig A) OneLambdaOp.case
                        (fun l => l.elim0)) scrut) b := htEq
                  obtain ⟨i, a, hscrEq⟩ := conHeaded_o_inv hcs
                  obtain ⟨idx, hidx⟩ := exists_ctorAt_eq i
                  subst hidx
                  rw [hscrEq] at htEq
                  rw [htEq] at hβ ⊢
                  refine ⟨b idx, OneLambdaStep.case idx a b, ?_, ?_, ?_,
                    fun habs => absurd rfl habs⟩
                  · exact size_arg_lt_replicateSpine A.numCtors RType.o _ b idx
                  · exact le_of_lt (height_arg_lt_replicateSpine A.numCtors RType.o _ b idx)
                  · exact Nat.le_zero.mp
                      ((betaRedexRank_arg_le_replicateSpine A.numCtors RType.o _ b idx).trans
                        (le_of_eq hβ))

/-- Lemma 12's ι-step existence (Leivant III section 4.2, p. 224, with the
ι-phase accounting of section 5, proof paragraph (iii), p. 226): a β-normal
term with an ι-redex takes a `OneLambdaStep` that strictly decreases the size,
does not increase the height, and preserves β-normality. The strict size
decrease is a recorded strengthening of the paper's decrease: each contractum
is an immediate constituent of its redex (`dstrHit`, `case`) or drops the
destructor node (`dstrMiss`). -/
theorem exists_iota_step_of_hasIota {Γ s} [LinearOrder A.B]
    (t : Binding.Tm (oneLambdaSig A) Γ s)
    (h : hasIota t = true) (hβ : betaRedexRank t = 0) :
    ∃ t', OneLambdaStep t t' ∧ Tm.size t' < Tm.size t ∧
      Tm.height t' ≤ Tm.height t ∧ betaRedexRank t' = 0 := by
  obtain ⟨t', hstep, hsz, hht, hβ', _⟩ := exists_iota_step_aux (Tm.size t) t le_rfl h hβ
  exact ⟨t', hstep, hsz, hht, hβ'⟩

/-- The size-bounded counted step relation (Leivant III section 4.2, realizing
the spec's size-invariant intersection relation): a single `OneLambdaStep` whose
target has size at most `M`. Restricting the reduction to a size ceiling makes
its counted chains `Relation.RelatesInSteps` bound the reduction length while the
individual terms stay inside a fixed size envelope. Novel packaging. -/
def stepWithin [LinearOrder A.B] (M : ℕ) {Γ : Binding.Ctx RType} {s : RType} :
    Binding.Tm (oneLambdaSig A) Γ s → Binding.Tm (oneLambdaSig A) Γ s → Prop :=
  fun a b => OneLambdaStep a b ∧ Tm.size b ≤ M

/-- The size ceiling of `stepWithin` is monotone: a step within `M` is a step
within any larger ceiling `M'`. -/
theorem stepWithin_mono [LinearOrder A.B] {M M' : ℕ} (h : M ≤ M')
    {Γ : Binding.Ctx RType} {s : RType}
    {a b : Binding.Tm (oneLambdaSig A) Γ s} (hab : stepWithin M a b) :
    stepWithin M' a b :=
  ⟨hab.1, le_trans hab.2 h⟩

/-- Monotonicity of a counted chain in its relation: a chain of `r`-steps is a
chain of `r'`-steps at the same length whenever `r` refines to `r'`. Derived from
CSLib's `Relation.RelatesInSteps.map` at the identity carrier map. -/
theorem relatesInSteps_mono {α : Type*} {r r' : α → α → Prop}
    (h : ∀ a b, r a b → r' a b) {a b : α} {n : ℕ}
    (hab : Relation.RelatesInSteps r a b n) : Relation.RelatesInSteps r' a b n :=
  Relation.RelatesInSteps.map id h hab

/-- A counted `stepWithin` chain projects to a `Relation.ReflTransGen` reduction:
forgetting both the step count and the size ceiling recovers the ordinary
reflexive-transitive reduction. -/
theorem relatesInSteps_stepWithin_reflTransGen [LinearOrder A.B] {M : ℕ}
    {Γ : Binding.Ctx RType} {s : RType}
    {a b : Binding.Tm (oneLambdaSig A) Γ s} {n : ℕ}
    (h : Relation.RelatesInSteps (stepWithin M) a b n) :
    Relation.ReflTransGen OneLambdaStep a b :=
  (relatesInSteps_mono (fun _ _ hab => hab.1) h).reflTransGen

/-- A counted chain in the function subterm lifts through the application
congruence rule `OneLambdaStep.appL`: a chain `f ⇒* f'` of `stepWithin M` steps
of length `k` gives a chain `app' f x ⇒* app' f' x` of the same length `k` at the
size ceiling shifted by the fixed argument `x` (the additive constant
`Tm.size x + 1` is the size the application node adds over its function subterm,
read off `size_app'`). Novel packaging of decision D2/P3's size-invariant chain
lifting. -/
theorem relatesInSteps_app'_left [LinearOrder A.B] {M : ℕ}
    {Γ : Binding.Ctx RType} {σ τ : RType}
    {f f' : Binding.Tm (oneLambdaSig A) Γ (RType.arrow σ τ)}
    (x : Binding.Tm (oneLambdaSig A) Γ σ) {k : ℕ}
    (h : Relation.RelatesInSteps (stepWithin M) f f' k) :
    Relation.RelatesInSteps (stepWithin (M + Tm.size x + 1)) (app' f x) (app' f' x) k := by
  induction h with
  | refl => exact Relation.RelatesInSteps.refl _
  | tail g g' n hchain hstep ih =>
      refine Relation.RelatesInSteps.tail (app' f x) (app' g x) (app' g' x) n ih
        ⟨OneLambdaStep.appL x hstep.1, ?_⟩
      rw [size_app']
      have := hstep.2
      omega

/-- A counted chain in the argument subterm lifts through the application
congruence rule `OneLambdaStep.appR`: a chain `x ⇒* x'` of `stepWithin M` steps of
length `k` gives a chain `app' f x ⇒* app' f x'` of the same length `k` at the
size ceiling shifted by the fixed function `f` (the additive constant
`Tm.size f + 1` read off `size_app'`). Novel packaging of decision D2/P3. -/
theorem relatesInSteps_app'_right [LinearOrder A.B] {M : ℕ}
    {Γ : Binding.Ctx RType} {σ τ : RType}
    (f : Binding.Tm (oneLambdaSig A) Γ (RType.arrow σ τ))
    {x x' : Binding.Tm (oneLambdaSig A) Γ σ} {k : ℕ}
    (h : Relation.RelatesInSteps (stepWithin M) x x' k) :
    Relation.RelatesInSteps (stepWithin (M + Tm.size f + 1)) (app' f x) (app' f x') k := by
  induction h with
  | refl => exact Relation.RelatesInSteps.refl _
  | tail g g' n hchain hstep ih =>
      refine Relation.RelatesInSteps.tail (app' f x) (app' f g) (app' f g') n ih
        ⟨OneLambdaStep.appR f hstep.1, ?_⟩
      rw [size_app']
      have := hstep.2
      omega

/-- A counted chain in the abstraction body lifts through the congruence rule
`OneLambdaStep.lamBody`: a chain `b ⇒* b'` of `stepWithin M` steps of length `k` in
the binder-extended context `Γ ++ [σ]` gives a chain `lam' b ⇒* lam' b'` of the
same length `k` in `Γ` at the size ceiling shifted by the abstraction node (the
additive constant `1` read off `size_lam'`). Novel packaging of decision
D2/P3. -/
theorem relatesInSteps_lamBody [LinearOrder A.B] {M : ℕ}
    {Γ : Binding.Ctx RType} {σ τ : RType}
    {b b' : Binding.Tm (oneLambdaSig A) (Γ ++ [σ]) τ} {k : ℕ}
    (h : Relation.RelatesInSteps (stepWithin M) b b' k) :
    Relation.RelatesInSteps (stepWithin (M + 1)) (lam' b) (lam' b') k := by
  induction h with
  | refl => exact Relation.RelatesInSteps.refl _
  | tail c c' n hchain hstep ih =>
      refine Relation.RelatesInSteps.tail (lam' b) (lam' c) (lam' c') n ih
        ⟨OneLambdaStep.lamBody hstep.1, ?_⟩
      rw [size_lam']
      have := hstep.2
      omega

/-- `isLam` is invariant under renaming: a renaming preserves the head operation
of a term. The redex-detection sibling of `Tm.size_ren`/`Tm.height_ren`. -/
theorem isLam_ren {Γ Δ : Binding.Ctx RType} {s : RType} (ρ : Binding.Thinning Γ Δ)
    (t : Binding.Tm (oneLambdaSig A) Γ s) : isLam (Binding.ren ρ t) = isLam t := by
  rcases tm_cases t with ⟨x, rfl⟩ | ⟨o, hs, args, rfl⟩
  · rw [Binding.ren, Binding.traverse_var]
    simp only [Binding.varKit, isLam_var]
  · subst hs
    rw [Binding.ren, Binding.traverse_op]
    rfl

/-- `betaRedexRank` is invariant under renaming: a renaming preserves the
operation tree and therefore every `topBetaRank` contribution, using `isLam_ren`
at each application node. The redex-rank sibling of `Tm.size_ren`. -/
@[simp] theorem betaRedexRank_ren {Γ Δ : Binding.Ctx RType} {s : RType}
    (ρ : Binding.Thinning Γ Δ) (t : Binding.Tm (oneLambdaSig A) Γ s) :
    betaRedexRank (Binding.ren ρ t) = betaRedexRank t := by
  suffices h : ∀ {y : Binding.Ctx RType × RType}
      (t : PolyFix (polyTranslate Binding.varOver (oneLambdaSig A).polyEndo) y)
      {Δ : Binding.Ctx RType} (ρ : Binding.Thinning y.1 Δ),
      betaRedexRank (Γ := Δ) (Binding.traverse (Binding.varKit (oneLambdaSig A))
          (Binding.renEnv ρ) t)
        = betaRedexRank (Γ := y.1) (s := y.2) t from h t ρ
  intro y t
  induction t with
  | mk y idx children ih =>
    intro Δ ρ
    cases idx with
    | inl a =>
      rw [show (PolyFix.mk y (Sum.inl a) children : Binding.Tm (oneLambdaSig A) y.1 y.2)
            = Binding.Tm.var (Binding.leafVar a) from by
              obtain ⟨⟨Γ', i'⟩, rfl⟩ := a
              congr 1
              funext e
              exact e.elim]
      simp only [Binding.traverse_var, Binding.varKit, betaRedexRank_var]
    | inr p =>
      obtain ⟨Γ', s'⟩ := y
      change { o : OneLambdaOp A // (oneLambdaSig A).result o = s' } at p
      revert children ih
      obtain ⟨o, rfl⟩ := p
      intro children ih
      change betaRedexRank (Binding.traverse (Binding.varKit (oneLambdaSig A)) (Binding.renEnv ρ)
            (Binding.Tm.op (S := oneLambdaSig A) o (fun j => children ⟨j⟩)))
          = betaRedexRank (Binding.Tm.op (S := oneLambdaSig A) o (fun j => children ⟨j⟩))
      rw [Binding.traverse_op, betaRedexRank_op, betaRedexRank_op]
      congr 1
      · cases o with
        | app σ'' τ'' =>
          have hlam : isLam (Binding.traverse (Binding.varKit (oneLambdaSig A))
              (Binding.Env.underBinder (Binding.varKit (oneLambdaSig A)) (Binding.renEnv ρ))
              (children ⟨0, Nat.succ_pos 1⟩))
            = isLam (children ⟨0, Nat.succ_pos 1⟩) := by
            rw [Binding.underBinder_renEnv]; exact isLam_ren _ _
          simp only [topBetaRank_op, topBetaRankOp, hlam]
        | lam _ _ => simp only [topBetaRank_op, topBetaRankOp]
        | con _ => simp only [topBetaRank_op, topBetaRankOp]
        | dstr _ => simp only [topBetaRank_op, topBetaRankOp]
        | case => simp only [topBetaRank_op, topBetaRankOp]
      · refine Finset.sup_congr rfl fun j _ => ?_
        rw [Binding.underBinder_renEnv]
        exact ih ⟨j⟩ (Binding.Thinning.appendId ρ _)

/-- The per-image bound of note N2's substitution redex-rank invariant: the
β-rank of an image, together with the order of its sort when the image is a `lam`.
A `lam` image dropped into function position creates a β-redex of exactly that
order; a variable image (`isLam` false) creates none, so its sort is exempt — the
exemption that makes the invariant stable under `Env.underBinder`, whose fresh
images are variables. -/
private def subBound {Γ : Binding.Ctx RType} (u : RType)
    (w : Binding.Tm (oneLambdaSig A) Γ u) : ℕ :=
  max (betaRedexRank w) (if isLam w then RType.ord u else 0)

/-- The β-rank of an image is bounded by its `subBound`. -/
private theorem betaRedexRank_le_subBound {Γ : Binding.Ctx RType} (u : RType)
    (w : Binding.Tm (oneLambdaSig A) Γ u) : betaRedexRank w ≤ subBound u w :=
  le_max_left _ _

/-- The `subBound` of a variable image is `0`: a variable has no β-redex and is
not a `lam`. -/
private theorem subBound_var {Γ : Binding.Ctx RType} (u : RType) (x : Binding.Var Γ u) :
    subBound u (Binding.Tm.var x : Binding.Tm (oneLambdaSig A) Γ u) = 0 := by
  unfold subBound
  rw [betaRedexRank_var, isLam_var]
  simp

/-- `subBound` is invariant under renaming (`betaRedexRank_ren`, `isLam_ren`),
so a renamed image keeps its bound. -/
private theorem subBound_ren {Γ Δ : Binding.Ctx RType} (u : RType)
    (ρ : Binding.Thinning Γ Δ) (w : Binding.Tm (oneLambdaSig A) Γ u) :
    subBound u (Binding.ren ρ w) = subBound u w := by
  simp only [subBound, betaRedexRank_ren, isLam_ren]

/-- `subBound` is invariant under transport of the sort index. -/
private theorem subBound_cast {Γ : Binding.Ctx RType} {u u' : RType} (h : u = u')
    (w : Binding.Tm (oneLambdaSig A) Γ u) :
    subBound u' (h ▸ w) = subBound u w := by subst h; rfl

/-- The head of a substitution instance is a `lam` only if the original head is a
`lam` or the substituted variable's image is a `lam`. The substitution rebuilds an
operation node with its head unchanged, so a fresh `lam` head can arise only at a
variable leaf, from that leaf's image. -/
private theorem isLam_sub_imp {Γ Δ : Binding.Ctx RType} {s : RType}
    (σ : Binding.Env (Binding.Tm (oneLambdaSig A)) Γ Δ)
    (t : Binding.Tm (oneLambdaSig A) Γ s) (h : isLam (Binding.sub σ t) = true) :
    isLam t = true ∨ ∃ x : Binding.Var Γ s, isLam (σ s x) = true := by
  rcases tm_cases t with ⟨x, rfl⟩ | ⟨o, hs, args, rfl⟩
  · exact Or.inr ⟨x, by rwa [Binding.sub_var] at h⟩
  · refine Or.inl ?_
    subst hs
    have h' : isLam (Binding.traverse (Binding.subKit (oneLambdaSig A)) σ
        (Binding.Tm.op (S := oneLambdaSig A) o args)) = true := h
    rw [Binding.traverse_op] at h'
    exact h'

/-- The environment-generalized redex-rank bound of note N2: substituting along an
environment whose images all satisfy `subBound _ _ ≤ M` raises the β-rank by at
most `M`. Proved by the kit's substitution induction; the binder case feeds the
under-binder environment, whose fresh images are variables (`subBound = 0`) and
whose old images are renamings (`subBound` preserved by `subBound_ren`). The
top-node β-redex created at an application whose function is a variable leaf is
bounded through `isLam_sub_imp` by the leaf image's sort order, which the invariant
carries for `lam` images. Novel packaging serving Leivant III section 5, proof
paragraph (ii), p. 226. -/
private theorem betaRedexRank_sub_le {Γ Δ : Binding.Ctx RType} {s : RType}
    (σ : Binding.Env (Binding.Tm (oneLambdaSig A)) Γ Δ)
    (t : Binding.Tm (oneLambdaSig A) Γ s) {M : ℕ}
    (hσ : ∀ u (x : Binding.Var Γ u), subBound u (σ u x) ≤ M) :
    betaRedexRank (Binding.sub σ t) ≤ max (betaRedexRank t) M := by
  suffices h : ∀ {y : Binding.Ctx RType × RType}
      (t : PolyFix (polyTranslate Binding.varOver (oneLambdaSig A).polyEndo) y)
      {Δ : Binding.Ctx RType} (σ : Binding.Env (Binding.Tm (oneLambdaSig A)) y.1 Δ),
      (∀ u (x : Binding.Var y.1 u), subBound u (σ u x) ≤ M) →
      betaRedexRank (Γ := Δ) (Binding.traverse (Binding.subKit (oneLambdaSig A)) σ t)
        ≤ max (betaRedexRank (Γ := y.1) (s := y.2) t) M from h t σ hσ
  intro y t
  induction t with
  | mk y idx children ih =>
    intro Δ σ hσ
    cases idx with
    | inl a =>
      rw [show (PolyFix.mk y (Sum.inl a) children : Binding.Tm (oneLambdaSig A) y.1 y.2)
            = Binding.Tm.var (Binding.leafVar a) from by
              obtain ⟨⟨Γ', i'⟩, rfl⟩ := a
              congr 1
              funext e
              exact e.elim]
      rw [Binding.traverse_var]
      simp only [Binding.subKit, id, betaRedexRank_var]
      exact le_trans (le_trans (betaRedexRank_le_subBound _ _) (hσ y.2 (Binding.leafVar a)))
        (le_max_right _ _)
    | inr p =>
      obtain ⟨Γ', s'⟩ := y
      change { o : OneLambdaOp A // (oneLambdaSig A).result o = s' } at p
      revert children ih
      obtain ⟨o, rfl⟩ := p
      intro children ih
      change betaRedexRank (Binding.traverse (Binding.subKit (oneLambdaSig A)) σ
            (Binding.Tm.op (S := oneLambdaSig A) o (fun j => children ⟨j⟩)))
          ≤ max (betaRedexRank (Binding.Tm.op (S := oneLambdaSig A) o (fun j => children ⟨j⟩))) M
      rw [Binding.traverse_op, betaRedexRank_op, betaRedexRank_op]
      have hunder : ∀ (Ξ : Binding.Ctx RType) u (x : Binding.Var (Γ' ++ Ξ) u),
          subBound u (Binding.Env.underBinder (Binding.subKit (oneLambdaSig A)) (Ξ := Ξ) σ u x)
            ≤ M := by
        intro Ξ u x
        simp only [Binding.Env.underBinder, Binding.subKit]
        rw [Binding.Var.appendCases_natural (subBound u)]
        apply Binding.Var.appendCases_le
        · intro y
          rw [subBound_var]
          exact Nat.zero_le _
        · intro v
          rw [subBound_ren]
          exact hσ u v
      have htkey : topBetaRank (Binding.Tm.op (S := oneLambdaSig A) o
            (fun j => Binding.traverse (Binding.subKit (oneLambdaSig A))
              (Binding.Env.underBinder (Binding.subKit (oneLambdaSig A)) σ) (children ⟨j⟩)))
          ≤ max (topBetaRank (Binding.Tm.op (S := oneLambdaSig A) o (fun j => children ⟨j⟩))) M :=
        by
        cases o with
        | app σ'' τ'' =>
          simp only [topBetaRank_op, topBetaRankOp]
          by_cases hs1 : isLam (Binding.traverse (Binding.subKit (oneLambdaSig A))
              (Binding.Env.underBinder (Binding.subKit (oneLambdaSig A)) σ)
              (children ⟨0, Nat.succ_pos 1⟩)) = true
          · rw [if_pos hs1]
            rcases isLam_sub_imp (Binding.Env.underBinder (Binding.subKit (oneLambdaSig A)) σ)
                (children ⟨0, Nat.succ_pos 1⟩) hs1 with hc | ⟨y, hy⟩
            · rw [if_pos hc]
              exact le_max_left _ _
            · have hb := hunder [] (RType.arrow σ'' τ'') y
              have hy' : isLam (Binding.Env.underBinder (Binding.subKit (oneLambdaSig A)) σ
                  (RType.arrow σ'' τ'') y) = true := hy
              have hO : RType.ord (RType.arrow σ'' τ'')
                  ≤ subBound (RType.arrow σ'' τ'')
                    (Binding.Env.underBinder (Binding.subKit (oneLambdaSig A)) σ
                      (RType.arrow σ'' τ'') y) := by
                unfold subBound
                rw [if_pos hy']
                exact le_max_right _ _
              exact le_trans (le_trans hO hb) (le_max_right _ _)
          · rw [if_neg hs1]
            exact Nat.zero_le _
        | lam _ _ => simp [topBetaRank_op, topBetaRankOp]
        | con _ => simp [topBetaRank_op, topBetaRankOp]
        | dstr _ => simp [topBetaRank_op, topBetaRankOp]
        | case => simp [topBetaRank_op, topBetaRankOp]
      apply max_le
      · exact le_trans htkey (by
          have := le_max_left (topBetaRank (Binding.Tm.op (S := oneLambdaSig A) o
            (fun j => children ⟨j⟩)))
            (Finset.univ.sup (fun j => betaRedexRank (children ⟨j⟩)))
          omega)
      · apply Finset.sup_le
        intro j _
        have hj := ih ⟨j⟩ (Binding.Env.underBinder (Binding.subKit (oneLambdaSig A)) σ)
          (fun u x => hunder _ u x)
        have hle : betaRedexRank (children ⟨j⟩)
            ≤ Finset.univ.sup (fun k => betaRedexRank (children ⟨k⟩)) :=
          Finset.le_sup (f := fun k => betaRedexRank (children ⟨k⟩)) (Finset.mem_univ j)
        exact le_trans hj (max_le_max (le_trans hle (le_max_right _ _)) (le_refl M))

/-- Note N2 (Leivant III section 4.2, p. 224; ι-phase accounting of section 5,
proof paragraph (iii), p. 226): the β-rank of a single-variable substitution
instance is bounded by the β-ranks of the body and the substituted term together
with the order of the substituted sort. The substituted term dropped into function
position can create a β-redex of rank `RType.ord σ`, but no higher; the corollary
of `betaRedexRank_sub_le` at the instantiating environment, whose sole non-variable
image is `N` (sort `σ`) and whose old images are the identity variables. -/
theorem betaRedexRank_instantiate₁_le {Γ : Binding.Ctx RType} {σ τ : RType}
    (N : Binding.Tm (oneLambdaSig A) Γ σ) (b : Binding.Tm (oneLambdaSig A) (Γ ++ [σ]) τ) :
    betaRedexRank (Binding.instantiate₁ N b)
      ≤ max (betaRedexRank b) (max (betaRedexRank N) (RType.ord σ)) := by
  unfold Binding.instantiate₁ Binding.instantiate
  refine betaRedexRank_sub_le _ b ?_
  intro u x
  rw [Binding.extendEnv_apply, Binding.Var.appendCases_natural (subBound u)]
  apply Binding.Var.appendCases_le
  · intro w
    obtain ⟨i, hi⟩ := w
    cases i using Fin.cases with
    | zero =>
      subst hi
      refine max_le (le_max_left _ _) (le_trans ?_ (le_max_right _ _))
      split
      · exact le_refl _
      · exact Nat.zero_le _
    | succ j => exact j.elim0
  · intro v
    simp only [Binding.idEnv]
    rw [subBound_var]
    exact Nat.zero_le _

/-- The endpoint of a counted `stepWithin` chain obeys the chain's size ceiling
whenever the start does: a step's target is bounded by the ceiling by
definition, and an empty chain ends at its start. Consumed when composing
cycles, where the endpoint of one chain seeds the ceiling hypothesis of the
next. -/
theorem relatesInSteps_stepWithin_size_le [LinearOrder A.B] {M : ℕ}
    {Γ : Binding.Ctx RType} {s : RType}
    {a b : Binding.Tm (oneLambdaSig A) Γ s} {n : ℕ}
    (h : Relation.RelatesInSteps (stepWithin M) a b n) (ha : Tm.size a ≤ M) :
    Tm.size b ≤ M := by
  cases h with
  | refl => exact ha
  | tail _ _ _ _ hstep => exact hstep.2

/-- The arity inequality at `oneLambdaSig`: every operation has at most two
subterm arguments (`app` has two, `lam` one, the constants none), so a term's
size is bounded by `2` raised to its height (Leivant III section 5, proof
paragraph (ii), p. 226) — the instance of `Tm.size_le_pow_height` at `m = 2`. -/
theorem size_le_two_pow_height {Γ : Binding.Ctx RType} {s : RType}
    (t : Binding.Tm (oneLambdaSig A) Γ s) : Tm.size t ≤ 2 ^ Tm.height t :=
  Tm.size_le_pow_height t le_rfl (fun o => by cases o <;> simp [oneLambdaSig])

/-- An abstraction-headed term at an arrow sort is a `lam'` of some body: the
inversion of the `isLam` detector, recovering the body for the contraction case
of the rank-elimination cycle. -/
private theorem exists_lam'_of_isLam {Γ : Binding.Ctx RType} {σ τ : RType}
    {f : Binding.Tm (oneLambdaSig A) Γ (RType.arrow σ τ)} (h : isLam f = true) :
    ∃ b : Binding.Tm (oneLambdaSig A) (Γ ++ [σ]) τ, f = lam' b := by
  unfold isLam at h
  rcases hht : headTag f with _ | o
  · rw [hht] at h
    exact Bool.noConfusion h
  · rw [hht] at h
    cases o with
    | lam σ' τ' =>
        obtain ⟨hs, args, hEq⟩ := exists_op_of_headTag hht
        have hs1 : RType.arrow σ' τ' = RType.arrow σ τ := hs
        rw [RType.arrow_eq_arrow] at hs1
        obtain ⟨rfl, rfl⟩ := hs1
        replace hEq : f
            = Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.lam σ' τ') args := hEq
        obtain ⟨b, hb⟩ := op_lam_inv args
        exact ⟨b, hEq.trans hb⟩
    | app σ' τ' => exact Bool.noConfusion h
    | con i => exact Bool.noConfusion h
    | dstr j => exact Bool.noConfusion h
    | case => exact Bool.noConfusion h

/-- The conclusion of one rank-elimination cycle at rank budget `q` and size
ceiling `M` (notes N3/N5): a counted `stepWithin M` chain from `t` to a term of
β-rank below `q`, with the endpoint height bounded by `2 ^ Tm.height t`, the
step count by `Tm.size t`, and the shape invariant — an abstraction endpoint
forces an abstraction start or a sort of order at most `q`. The motive of the
`beta_cycle` induction, packaged so its per-node case lemmas share one
statement. -/
private def BetaCycle [LinearOrder A.B] {Γ : Binding.Ctx RType} {s : RType}
    (q M : ℕ) (t : Binding.Tm (oneLambdaSig A) Γ s) : Prop :=
  ∃ (t' : Binding.Tm (oneLambdaSig A) Γ s) (k : ℕ),
    Relation.RelatesInSteps (stepWithin M) t t' k ∧
    betaRedexRank t' ≤ q - 1 ∧
    Tm.height t' ≤ 2 ^ Tm.height t ∧
    k ≤ Tm.size t ∧
    (IsLam t' → IsLam t ∨ RType.ord s ≤ q)

/-- The identity cycle: a term already of β-rank `0` satisfies the cycle
conclusion with the empty chain. Discharges the variable and constant leaves of
the `beta_cycle` induction. -/
private theorem betaCycle_of_rank_zero [LinearOrder A.B] {Γ : Binding.Ctx RType}
    {s : RType} {q M : ℕ} {t : Binding.Tm (oneLambdaSig A) Γ s}
    (ht : betaRedexRank t = 0) : BetaCycle q M t :=
  ⟨t, 0, Relation.RelatesInSteps.refl t, by omega, Nat.lt_two_pow_self.le,
    Nat.zero_le _, fun h => Or.inl h⟩

/-- The abstraction case of the rank-elimination cycle (note N3): the body's
cycle lifts through `relatesInSteps_lamBody`, the abstraction node adding one to
the size ceiling and the height. The endpoint is an abstraction, but so is the
start — the shape invariant's left disjunct. -/
private theorem betaCycle_lam' [LinearOrder A.B] {Γ : Binding.Ctx RType} {σ τ : RType}
    {q : ℕ} {b : Binding.Tm (oneLambdaSig A) (Γ ++ [σ]) τ}
    (hb : BetaCycle q (Tm.size b + 2 ^ (2 ^ Tm.height b)) b)
    {M : ℕ} (hM : Tm.size (lam' b) + 2 ^ (2 ^ Tm.height (lam' b)) ≤ M) :
    BetaCycle q M (lam' b) := by
  obtain ⟨b', k, hchain, hrank, hheight, hk, _⟩ := hb
  have hle : Tm.size b + 2 ^ (2 ^ Tm.height b) + 1 ≤ M := by
    rw [size_lam', height_lam'] at hM
    have hpow : 2 ^ (2 ^ Tm.height b) ≤ 2 ^ (2 ^ (1 + Tm.height b)) :=
      Nat.pow_le_pow_right (by omega) (Nat.pow_le_pow_right (by omega) (by omega))
    omega
  refine ⟨lam' b', k,
    relatesInSteps_mono (fun _ _ => stepWithin_mono hle) (relatesInSteps_lamBody hchain),
    ?_, ?_, ?_, fun _ => Or.inl (isLam_lam' b)⟩
  · rwa [betaRedexRank_lam']
  · rw [height_lam', height_lam']
    have h2 : (1 : ℕ) ≤ 2 ^ Tm.height b := Nat.one_le_two_pow
    have h3 : 2 ^ (1 + Tm.height b) = 2 * 2 ^ Tm.height b := by rw [pow_add, pow_one]
    omega
  · rw [size_lam']
    omega

end OneLambda

end GebLean.Ramified
