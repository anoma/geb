import GebLean.Binding.Term
import GebLean.Binding.Thinning

/-!
# The generic binder-aware traversal (the kit)

The traversal layer of an indexed binder-substitution kit (decision 8): a
`Kit` packages the three operations that a binder-aware fold needs at its
leaves — reading a variable, embedding a value as a term, and weakening a
value along a thinning — and an environment carries a value of the target
context at each variable of the source context. The renaming kit `varKit`
instantiates the leaf operations to variable-for-variable renaming.

## Main definitions

* `Kit` — the leaf operations of a binder-aware traversal over a value family.
* `Env` — an environment: a value of the target context at each variable of
  the source context.
* `Var.appendRight` — the suffix inclusion of a variable of `Ξ` into `Δ ++ Ξ`.
* `Var.appendCases` — the append-variable eliminator splitting a variable of
  `Γ ++ Ξ` into a variable of `Γ` or of `Ξ`.
* `Env.underBinder` — weakening of an environment under a binder: the freshly
  bound variables map to themselves, the old values weaken along the suffix
  embedding.
* `varKit` — the renaming kit.
* `leafVar` — recovery of a `Var` from a leaf of the diagonal variable family.
* `traverse` — the generic binder-aware fold of a term against an environment.

## Main statements

* `traverse_var` — `traverse` at a variable reads the environment.
* `traverse_op` — `traverse` at an operation node recurses into the arguments
  under the binder-weakened environment.

## References

The kit presentation of binder-aware traversal follows G. Allais, R. Atkey,
J. Chapman, C. McBride, and J. McKinna, "A type and scope safe universe of
syntaxes with binding: their semantics and proofs", Proceedings of the ACM on
Programming Languages 2 (ICFP), 2018, DOI `10.1145/3236785`.
-/

namespace GebLean.Binding

open CategoryTheory

universe u v

variable {Ty : Type u}

/-- A substitution kit over a value family `V`: the leaf operations a
binder-aware traversal needs. `var` reads a variable as a value, `toTm`
embeds a value as a term, and `wk` weakens a value along a thinning. -/
structure Kit (S : BinderSig Ty) (V : Ctx Ty → Ty → Type) where
  /-- Read a variable as a value. -/
  var : ∀ {Γ s}, Var Γ s → V Γ s
  /-- Embed a value as a term. -/
  toTm : ∀ {Γ s}, V Γ s → Tm S Γ s
  /-- Weaken a value along a thinning. -/
  wk : ∀ {Γ Δ s}, Thinning Γ Δ → V Γ s → V Δ s

/-- An environment over a value family `V` from the source context `Γ` to the
target context `Δ`: a value of `Δ` at every variable of `Γ`, of that
variable's sort. -/
def Env (V : Ctx Ty → Ty → Type) (Γ Δ : Ctx Ty) : Type u :=
  ∀ (s : Ty), Var Γ s → V Δ s

/-- The suffix inclusion of a variable of `Ξ` into the append-at-end extension
`Δ ++ Ξ`: shift its position past every entry of the prefix `Δ`. -/
def Var.appendRight : {Ξ : Ctx Ty} → {s : Ty} → (Δ : Ctx Ty) → Var Ξ s →
    Var (Δ ++ Ξ) s
  | _, _, [], y => y
  | _, _, _ :: Δ, y => Var.succ _ (Var.appendRight Δ y)

/-- The append-variable eliminator: a variable of `Γ ++ Ξ` is either a
variable of the prefix `Γ` (handled by `fromΓ`) or of the suffix `Ξ` (handled
by `fromΞ`). Recursion on `Γ`, peeling entries off the front as in
`Thinning.app`. -/
def Var.appendCases {Ξ : Ctx Ty} {s : Ty} {motive : Sort v}
    (fromΞ : Var Ξ s → motive) :
    (Γ : Ctx Ty) → (Var Γ s → motive) → Var (Γ ++ Ξ) s → motive
  | [], _, x => fromΞ x
  | a :: Γ, fromΓ, ⟨i, hi⟩ => by
      cases i using Fin.cases with
      | zero => exact fromΓ ⟨0, hi⟩
      | succ i' =>
          exact Var.appendCases fromΞ Γ (fun v => fromΓ (Var.succ a v)) ⟨i', hi⟩

/-- Weakening of an environment under a binder that binds the sorts `Ξ`: a
freshly bound variable of `Ξ` maps to itself (read by `K.var`), and an old
variable of `Γ` maps to its old value weakened along the suffix embedding
`Δ ⊆ Δ ++ Ξ` (via `K.wk Thinning.weakAppend`). -/
def Env.underBinder {S : BinderSig Ty} {V : Ctx Ty → Ty → Type}
    (K : Kit S V) {Γ Δ Ξ : Ctx Ty} (ρ : Env V Γ Δ) : Env V (Γ ++ Ξ) (Δ ++ Ξ) :=
  fun s x =>
    Var.appendCases (fun y => K.var (Var.appendRight Δ y)) Γ
      (fun v => K.wk Thinning.weakAppend (ρ s v)) x

/-- The renaming kit: variables are their own values, embedded as terms by
`Tm.var` and weakened by `Thinning.app`. -/
def varKit (S : BinderSig Ty) : Kit S Var where
  var := id
  toTm := Tm.var
  wk := Thinning.app

/-- Recover the `Var` at index `p` from a leaf of the diagonal variable
family: a leaf is a context-position pair `⟨Γ, i⟩` together with a proof that
`(Γ, Γ.get i)` equals `p`, which transports the tautological variable
`⟨i, rfl⟩` to `Var p.1 p.2`. -/
def leafVar {p : Ctx Ty × Ty}
    (a : {v : (varOver (Ty := Ty)).left // varOver.hom v = p}) : Var p.1 p.2 :=
  cast (congrArg (fun q : Ctx Ty × Ty => Var q.1 q.2) a.2) ⟨a.1.2, rfl⟩

/-- The generic binder-aware traversal: fold a term `t` against an environment
`ρ`, realized by the dependent eliminator `PolyFix.ind` with an
environment-abstracting motive so the environment and target context can grow
under binders. A variable leaf reads the environment and embeds the result via
`K.toTm`; an operation node rebuilds the operation, recursing into each
argument under the binder-weakened environment `Env.underBinder K ρ`. -/
def traverse {S : BinderSig Ty} {V : Ctx Ty → Ty → Type} (K : Kit S V)
    {Γ Δ : Ctx Ty} {s : Ty} (ρ : Env V Γ Δ) (t : Tm S Γ s) : Tm S Δ s :=
  PolyFix.ind (P := polyTranslate varOver S.polyEndo)
    (motive := fun {x} _ => ∀ Δ', Env V x.1 Δ' → Tm S Δ' x.2)
    (fun {x} i children ih =>
      match i, children, ih with
      | Sum.inl a, _, _ => fun _ ρ' => K.toTm (ρ' x.2 (leafVar a))
      | Sum.inr p, _, ih => fun Δ' ρ' =>
          p.2 ▸ Tm.op p.val
            (fun j => ih ⟨j⟩ (Δ' ++ ((S.args p.val).get j).1)
              (Env.underBinder K ρ'))) t Δ ρ

/-- `traverse` at a variable reads the environment at that variable and embeds
the result via `K.toTm`. -/
@[simp] theorem traverse_var {S : BinderSig Ty} {V : Ctx Ty → Ty → Type}
    (K : Kit S V) {Γ Δ : Ctx Ty} {s : Ty} (ρ : Env V Γ Δ) (x : Var Γ s) :
    traverse K ρ (Tm.var x) = K.toTm (ρ s x) := by
  obtain ⟨i, hi⟩ := x
  subst hi
  rfl

/-- `traverse` at an operation node recurses into each argument under the
binder-weakened environment `Env.underBinder K ρ`, rebuilding the node. -/
@[simp] theorem traverse_op {S : BinderSig Ty} {V : Ctx Ty → Ty → Type}
    (K : Kit S V) {Γ Δ : Ctx Ty} (ρ : Env V Γ Δ) (o : S.Op)
    (args : ∀ j : Fin (S.args o).length,
      Tm S (Γ ++ ((S.args o).get j).1) ((S.args o).get j).2) :
    traverse K ρ (Tm.op o args)
      = Tm.op o (fun j => traverse K (Env.underBinder K ρ) (args j)) := rfl

end GebLean.Binding
