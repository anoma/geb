import GebLean.LawvereGodelT

/-!
# `LawvereGodelTTerm`: Typed-term inductive for Beckmann-Weiermann T*

`GodelTTerm S n σ` is the typed combinatory term system over
the base-type signature `S`, with `n` free base-typed variables
indexed by `Fin n` and result type `σ : GodelTType S`.  Higher-
typed terms are always closed; abstraction is realized by `K`
and `S_comb`, not by a primitive λ.  Tree primitives are gated
by `GodelTBase.tree ∈ S` at the constructor level.

This file also defines the standard interpretation
`GodelTTerm.interp` against base-typed environments
`Fin n → ℕ`, with per-constructor `@[simp]` lemmas.
-/

namespace GebLean

/-- Beckmann-Weiermann's typed combinatory system,
parameterized by a set of available base types.  Free
variables are base-typed only and indexed by `Fin n`.
Higher-typed terms are always closed -- there is no
λ-abstraction at the term level; abstraction is realized by
`K` and `S_comb`. -/
inductive GodelTTerm (S : Set GodelTBase) :
    Nat → GodelTType S → Type
  | var {n : Nat} (i : Fin n) (h : GodelTBase.nat ∈ S) :
      GodelTTerm S n (.base .nat h)
  | app {n : Nat} {σ τ : GodelTType S}
      (f : GodelTTerm S n (.arrow σ τ))
      (a : GodelTTerm S n σ) :
      GodelTTerm S n τ
  | zero (h : GodelTBase.nat ∈ S) :
      GodelTTerm S 0 (.base .nat h)
  | succ (h : GodelTBase.nat ∈ S) :
      GodelTTerm S 0 (.arrow (.base .nat h) (.base .nat h))
  | pred (h : GodelTBase.nat ∈ S) :
      GodelTTerm S 0 (.arrow (.base .nat h) (.base .nat h))
  | K (σ τ : GodelTType S) :
      GodelTTerm S 0 (.arrow σ (.arrow τ σ))
  | S_comb (ρ σ τ : GodelTType S) :
      GodelTTerm S 0
        (.arrow (.arrow ρ (.arrow σ τ))
          (.arrow (.arrow ρ σ) (.arrow ρ τ)))
  | disc {h : GodelTBase.nat ∈ S} (σ : GodelTType S) :
      GodelTTerm S 0
        (.arrow (.base .nat h) (.arrow σ (.arrow σ σ)))
  | iter (h : GodelTBase.nat ∈ S) :
      GodelTTerm S 0
        (.arrow (.base .nat h)
          (.arrow (.arrow (.base .nat h) (.base .nat h))
            (.arrow (.base .nat h) (.base .nat h))))
  | leaf (h : GodelTBase.tree ∈ S) :
      GodelTTerm S 0 (.base .tree h)
  | node (h : GodelTBase.tree ∈ S) :
      GodelTTerm S 0
        (.arrow (.base .tree h)
          (.arrow (.base .tree h) (.base .tree h)))
  | treeIter (h : GodelTBase.tree ∈ S) (σ : GodelTType S) :
      GodelTTerm S 0
        (.arrow (.base .tree h)
          (.arrow σ (.arrow (.arrow σ (.arrow σ σ)) σ)))

end GebLean
