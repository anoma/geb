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
type is ℕ and arrow types are Lean function spaces. -/
def GodelTType.interp : GodelTType → Type
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

end GebLean
