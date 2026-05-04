import GebLean.LawvereGodelTTerm

/-!
# `LawvereGodelTReduces`: reduction relations for `GodelTTerm`

This file defines the one-step reduction relation `▷` per
Beckmann-Weiermann Definition 4 as `GodelTTerm.Reduces`,
together with its reflexive-transitive closure
`GodelTTerm.Reduces.Star` (`▷*`) and its equivalence closure
`GodelTTerm.Reduces.Equiv` (`≈`).  Soundness of reduction
under the standard interpretation is established as
`GodelTTerm.Reduces.interp_invariance` and lifted to `Star`
and `Equiv`.
-/

namespace GebLean

/-- One-step reduction `▷` per Beckmann-Weiermann
Definition 4.  Tree-flavored reductions appear as additional
constructors gated by `GodelTBase.tree ∈ S`. -/
inductive GodelTTerm.Reduces {S : Set GodelTBase} {n : Nat} :
    {σ : GodelTType S} →
    GodelTTerm S n σ → GodelTTerm S n σ → Prop
  | redP_zero (hN : GodelTBase.nat ∈ S) :
      Reduces (.app (.pred (n := n) hN) (.zero hN))
        (.zero hN)
  | redP_succ (hN : GodelTBase.nat ∈ S)
      (t : GodelTTerm S n (.base .nat hN)) :
      Reduces (.app (.pred hN) (.app (.succ hN) t)) t
  | redK (σ τ : GodelTType S)
      (a : GodelTTerm S n σ) (b : GodelTTerm S n τ) :
      Reduces (.app (.app (.K (n := n) σ τ) a) b) a
  | redS (ρ σ τ : GodelTType S)
      (f : GodelTTerm S n (.arrow ρ (.arrow σ τ)))
      (g : GodelTTerm S n (.arrow ρ σ))
      (x : GodelTTerm S n ρ) :
      Reduces
        (.app (.app (.app (.S_comb (n := n) ρ σ τ) f) g) x)
        (.app (.app f x) (.app g x))
  | redDisc_zero {hN : GodelTBase.nat ∈ S}
      (σ : GodelTType S)
      (a b : GodelTTerm S n σ) :
      Reduces
        (.app (.app (.app (.disc (n := n) (h := hN) σ)
          (.zero hN)) a) b) a
  | redDisc_succ {hN : GodelTBase.nat ∈ S}
      (σ : GodelTType S)
      (t : GodelTTerm S n (.base .nat hN))
      (a b : GodelTTerm S n σ) :
      Reduces
        (.app (.app (.app (.disc (n := n) (h := hN) σ)
          (.app (.succ hN) t)) a) b) b
  | redIter_zero (hN : GodelTBase.nat ∈ S)
      (a : GodelTTerm S n
        (.arrow (.base .nat hN) (.base .nat hN)))
      (b : GodelTTerm S n (.base .nat hN)) :
      Reduces (.app (.app (.app (.iter (n := n) hN)
        (.zero hN)) a) b) b
  | redIter_succ (hN : GodelTBase.nat ∈ S)
      (t : GodelTTerm S n (.base .nat hN))
      (a : GodelTTerm S n
        (.arrow (.base .nat hN) (.base .nat hN)))
      (b : GodelTTerm S n (.base .nat hN)) :
      Reduces (.app (.app (.app (.iter (n := n) hN)
        (.app (.succ hN) t)) a) b)
        (.app a (.app (.app (.app (.iter hN) t) a) b))
  | redTreeIter_leaf (hT : GodelTBase.tree ∈ S)
      (σ : GodelTType S)
      (a : GodelTTerm S n σ)
      (b : GodelTTerm S n (.arrow σ (.arrow σ σ))) :
      Reduces (.app (.app (.app
        (.treeIter (n := n) hT σ) (.leaf hT)) a) b) a
  | redTreeIter_node (hT : GodelTBase.tree ∈ S)
      (σ : GodelTType S)
      (l r : GodelTTerm S n (.base .tree hT))
      (a : GodelTTerm S n σ)
      (b : GodelTTerm S n (.arrow σ (.arrow σ σ))) :
      Reduces (.app (.app (.app
        (.treeIter (n := n) hT σ)
        (.app (.app (.node hT) l) r)) a) b)
        (.app
          (.app b
            (.app (.app (.app (.treeIter hT σ) l) a) b))
          (.app (.app (.app (.treeIter hT σ) r) a) b))
  | redApp_left {σ τ : GodelTType S}
      {f g : GodelTTerm S n (.arrow σ τ)}
      (h : Reduces f g) (a : GodelTTerm S n σ) :
      Reduces (.app f a) (.app g a)
  | redApp_right {σ τ : GodelTType S}
      (f : GodelTTerm S n (.arrow σ τ))
      {a b : GodelTTerm S n σ} (h : Reduces a b) :
      Reduces (.app f a) (.app f b)

/-- Reflexive-transitive closure of `▷`. -/
inductive GodelTTerm.Reduces.Star {S : Set GodelTBase}
    {n : Nat} :
    {σ : GodelTType S} →
    GodelTTerm S n σ → GodelTTerm S n σ → Prop
  | refl {σ : GodelTType S} (t : GodelTTerm S n σ) :
      Star t t
  | step {σ : GodelTType S}
      {t u v : GodelTTerm S n σ}
      (h₁ : t.Reduces u) (h₂ : Star u v) :
      Star t v

theorem GodelTTerm.Reduces.Star.trans {S : Set GodelTBase}
    {n : Nat} {σ : GodelTType S}
    {t u v : GodelTTerm S n σ}
    (h₁ : Star t u) (h₂ : Star u v) : Star t v := by
  induction h₁ with
  | refl _ => exact h₂
  | step h _ ih => exact .step h (ih h₂)

theorem GodelTTerm.Reduces.toStar {S : Set GodelTBase}
    {n : Nat} {σ : GodelTType S}
    {t u : GodelTTerm S n σ} (h : t.Reduces u) :
    Reduces.Star t u :=
  .step h (.refl _)

/-- Equivalence closure of `▷`: smallest equivalence relation
containing the one-step reduction. -/
inductive GodelTTerm.Reduces.Equiv {S : Set GodelTBase}
    {n : Nat} :
    {σ : GodelTType S} →
    GodelTTerm S n σ → GodelTTerm S n σ → Prop
  | refl {σ : GodelTType S} (t : GodelTTerm S n σ) :
      Equiv t t
  | base_fwd {σ : GodelTType S}
      {t u : GodelTTerm S n σ} (r : t.Reduces u) :
      Equiv t u
  | base_bwd {σ : GodelTType S}
      {t u : GodelTTerm S n σ} (r : t.Reduces u) :
      Equiv u t
  | trans {σ : GodelTType S}
      {t u v : GodelTTerm S n σ}
      (h₁ : Equiv t u) (h₂ : Equiv u v) :
      Equiv t v

theorem GodelTTerm.Reduces.Equiv.symm {S : Set GodelTBase}
    {n : Nat} {σ : GodelTType S}
    {t u : GodelTTerm S n σ} (h : Equiv t u) :
    Equiv u t := by
  induction h with
  | refl _ => exact .refl _
  | base_fwd r => exact .base_bwd r
  | base_bwd r => exact .base_fwd r
  | trans _ _ ih₁ ih₂ => exact .trans ih₂ ih₁

/-- Reduction preserves interp.  The substantive lemma: each
redex's two sides have the same standard interpretation. -/
theorem GodelTTerm.Reduces.interp_invariance
    {S : Set GodelTBase} {n : Nat}
    {σ : GodelTType S} {t s : GodelTTerm S n σ}
    (h : t.Reduces s) (env : Fin n → Nat) :
    t.interp env = s.interp env := by
  induction h with
  | redP_zero hN => simp
  | redP_succ hN t => simp
  | redK σ τ a b => simp
  | redS ρ σ τ f g x => simp
  | redDisc_zero σ a b => simp
  | redDisc_succ σ t a b => simp
  | redIter_zero hN a b => simp
  | redIter_succ hN t a b => simp
  | redTreeIter_leaf hT σ a b =>
      simp [GodelTTerm.btlIter]
  | redTreeIter_node hT σ l r a b =>
      simp [GodelTTerm.btlIter]
  | redApp_left _ _ ih =>
      simp [ih]
  | redApp_right _ _ ih =>
      simp [ih]

theorem GodelTTerm.Reduces.Star.interp_invariance
    {S : Set GodelTBase} {n : Nat} {σ : GodelTType S}
    {t u : GodelTTerm S n σ} (h : Star t u)
    (env : Fin n → Nat) : t.interp env = u.interp env := by
  induction h with
  | refl _ => rfl
  | step r _ ih =>
      rw [GodelTTerm.Reduces.interp_invariance r env, ih]

theorem GodelTTerm.Reduces.Equiv.interp_invariance
    {S : Set GodelTBase} {n : Nat} {σ : GodelTType S}
    {t u : GodelTTerm S n σ} (h : Equiv t u)
    (env : Fin n → Nat) : t.interp env = u.interp env := by
  induction h with
  | refl _ => rfl
  | base_fwd r =>
      exact GodelTTerm.Reduces.interp_invariance r env
  | base_bwd r =>
      exact (GodelTTerm.Reduces.interp_invariance r env).symm
  | trans _ _ ih₁ ih₂ => rw [ih₁, ih₂]

end GebLean
