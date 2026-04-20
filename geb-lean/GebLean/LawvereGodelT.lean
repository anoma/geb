import Mathlib.Data.Fin.Basic

/-!
# `LawvereGodelT`: Restricted Gödel-T Fragment T*

A typed combinatory logic encoding Beckmann-Weiermann's T*
fragment of Gödel's T (B-W 2000, "Characterizing the
elementary recursive functions by a fragment of Gödel's T").
T*'s discipline restricts the iterator `𝒥_ρ` to type-0
applications, which fixes its expressivity to exactly the
elementary recursive functions.

Each GodelT term has a named ER backing in
`GebLean/Utilities/`; the categorical equivalence with
`LawvereERCat` is preserved by construction (see
`GebLean/LawvereGodelTERCatEquiv.lean`).
-/

namespace GebLean

/-- T*'s type system: a base type `base` (interpreted as ℕ)
and non-dependent arrow types. -/
inductive GodelTType : Type
  | base : GodelTType
  | arrow (σ τ : GodelTType) : GodelTType
  deriving DecidableEq, Repr, Inhabited

/-- Set-theoretic interpretation of a GodelT type: the base
type is ℕ and arrow types are Lean function spaces.  The
definition is reducible so that elaboration of numerals and
Lean functions at `base.interp`/`arrow _ _` .interp succeeds
without explicit casts. -/
@[reducible] def GodelTType.interp : GodelTType → Type
  | .base => ℕ
  | .arrow σ τ => σ.interp → τ.interp

/-- The curried n-ary ground function type: `arrow0 0 = base`
and `arrow0 (n + 1) = arrow base (arrow0 n)`. -/
def GodelTType.arrow0 : ℕ → GodelTType
  | 0 => .base
  | n + 1 => .arrow .base (arrow0 n)

@[simp] theorem GodelTType.arrow0_zero :
    GodelTType.arrow0 0 = .base := rfl

@[simp] theorem GodelTType.arrow0_succ (n : ℕ) :
    GodelTType.arrow0 (n + 1) = .arrow .base (arrow0 n) := rfl

/-- T*'s term inductive: typed combinatory logic with
constants (`zero`, `succ`, `pred`, `K`, `S`, `disc`) and a
placement-restricted iterator whose counter is always of
base type.  The grammar enforces B-W's T* discipline
syntactically: `iter` takes its counter via the
ground-typed `t : GodelTTerm .base` parameter. -/
inductive GodelTTerm : GodelTType → Type
  | zero : GodelTTerm .base
  | succ : GodelTTerm (.arrow .base .base)
  | pred : GodelTTerm (.arrow .base .base)
  | K (σ τ : GodelTType) :
      GodelTTerm (.arrow σ (.arrow τ σ))
  | S (ρ σ τ : GodelTType) :
      GodelTTerm
        (.arrow (.arrow ρ (.arrow σ τ))
          (.arrow (.arrow ρ σ) (.arrow ρ τ)))
  | disc (σ : GodelTType) :
      GodelTTerm
        (.arrow .base (.arrow σ (.arrow σ σ)))
  | iter (ρ : GodelTType) (t : GodelTTerm .base) :
      GodelTTerm (.arrow (.arrow ρ ρ) (.arrow ρ ρ))
  | app {σ τ : GodelTType}
      (f : GodelTTerm (.arrow σ τ)) (a : GodelTTerm σ) :
      GodelTTerm τ

/-- Standard interpretation of T* terms.  Each constructor
maps to its set-theoretic semantics; `iter` reduces to
`Nat.rec` over the iteration count `t.interp`. -/
def GodelTTerm.interp : {σ : GodelTType} →
    GodelTTerm σ → σ.interp
  | _, .zero => 0
  | _, .succ => Nat.succ
  | _, .pred => Nat.pred
  | _, .K _ _ => fun a _ => a
  | _, .S _ _ _ => fun f g x => f x (g x)
  | _, .disc _ => fun n a b =>
      match n with
      | 0 => a
      | _ + 1 => b
  | _, .iter _ t => fun step base =>
      Nat.rec base (fun _ prev => step prev) t.interp
  | _, .app f a => f.interp a.interp

@[simp] theorem GodelTTerm.interp_zero :
    GodelTTerm.zero.interp = 0 := rfl

@[simp] theorem GodelTTerm.interp_succ :
    GodelTTerm.succ.interp = Nat.succ := rfl

@[simp] theorem GodelTTerm.interp_pred :
    GodelTTerm.pred.interp = Nat.pred := rfl

@[simp] theorem GodelTTerm.interp_K (σ τ : GodelTType) :
    (GodelTTerm.K σ τ).interp = (fun a _ => a) := rfl

@[simp] theorem GodelTTerm.interp_S (ρ σ τ : GodelTType) :
    (GodelTTerm.S ρ σ τ).interp =
      (fun f g x => f x (g x)) := rfl

@[simp] theorem GodelTTerm.interp_disc (σ : GodelTType) :
    (GodelTTerm.disc σ).interp =
      (fun n a b => match n with
        | 0 => a
        | _ + 1 => b) := rfl

@[simp] theorem GodelTTerm.interp_iter (ρ : GodelTType)
    (t : GodelTTerm .base) :
    (GodelTTerm.iter ρ t).interp =
      (fun step base =>
        Nat.rec base (fun _ prev => step prev) t.interp) :=
  rfl

@[simp] theorem GodelTTerm.interp_app {σ τ : GodelTType}
    (f : GodelTTerm (.arrow σ τ)) (a : GodelTTerm σ) :
    (f.app a).interp = f.interp a.interp := rfl

/-- T⁻ membership: a `GodelTTerm` is pure when no `iter`
constructor appears anywhere in its term tree.  Decidable by
tree-walk; see the instance below. -/
def GodelTPure : {σ : GodelTType} → GodelTTerm σ → Prop
  | _, .zero => True
  | _, .succ => True
  | _, .pred => True
  | _, .K _ _ => True
  | _, .S _ _ _ => True
  | _, .disc _ => True
  | _, .iter _ _ => False
  | _, .app f a => GodelTPure f ∧ GodelTPure a

instance GodelTPure.decidable :
    {σ : GodelTType} → (t : GodelTTerm σ) →
      Decidable (GodelTPure t)
  | _, .zero => instDecidableTrue
  | _, .succ => instDecidableTrue
  | _, .pred => instDecidableTrue
  | _, .K _ _ => instDecidableTrue
  | _, .S _ _ _ => instDecidableTrue
  | _, .disc _ => instDecidableTrue
  | _, .iter _ _ => instDecidableFalse
  | _, .app f a =>
      have := decidable f
      have := decidable a
      instDecidableAnd

end GebLean
