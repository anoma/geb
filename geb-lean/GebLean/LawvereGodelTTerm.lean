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
  | zero {n : Nat} (h : GodelTBase.nat ∈ S) :
      GodelTTerm S n (.base .nat h)
  | succ {n : Nat} (h : GodelTBase.nat ∈ S) :
      GodelTTerm S n (.arrow (.base .nat h) (.base .nat h))
  | pred {n : Nat} (h : GodelTBase.nat ∈ S) :
      GodelTTerm S n (.arrow (.base .nat h) (.base .nat h))
  | K {n : Nat} (σ τ : GodelTType S) :
      GodelTTerm S n (.arrow σ (.arrow τ σ))
  | S_comb {n : Nat} (ρ σ τ : GodelTType S) :
      GodelTTerm S n
        (.arrow (.arrow ρ (.arrow σ τ))
          (.arrow (.arrow ρ σ) (.arrow ρ τ)))
  | disc {n : Nat} {h : GodelTBase.nat ∈ S} (σ : GodelTType S) :
      GodelTTerm S n
        (.arrow (.base .nat h) (.arrow σ (.arrow σ σ)))
  | iter {n : Nat} (h : GodelTBase.nat ∈ S) :
      GodelTTerm S n
        (.arrow (.base .nat h)
          (.arrow (.arrow (.base .nat h) (.base .nat h))
            (.arrow (.base .nat h) (.base .nat h))))
  | leaf {n : Nat} (h : GodelTBase.tree ∈ S) :
      GodelTTerm S n (.base .tree h)
  | node {n : Nat} (h : GodelTBase.tree ∈ S) :
      GodelTTerm S n
        (.arrow (.base .tree h)
          (.arrow (.base .tree h) (.base .tree h)))
  | treeIter {n : Nat} (h : GodelTBase.tree ∈ S)
      (σ : GodelTType S) :
      GodelTTerm S n
        (.arrow (.base .tree h)
          (.arrow σ (.arrow (.arrow σ (.arrow σ σ)) σ)))

/-- Tree iterator on `BTL` ignoring leaf labels: returns
`base` at every leaf and combines child results via `step` at
every node.  Used as the semantics of `GodelTTerm.treeIter`. -/
def GodelTTerm.btlIter {α : Type} (base : α) (step : α → α → α) :
    BTL → α
  | .leaf _ => base
  | .node l r =>
      step (GodelTTerm.btlIter base step l)
        (GodelTTerm.btlIter base step r)

/-- Standard interpretation of a `GodelTTerm S n σ` against a
base-typed environment `Fin n → ℕ`.  Each constructor maps to
its set-theoretic semantics; tree primitives use `BTL.leaf 0`
as the canonical leaf, `BTL.node` as the binary constructor,
and `GodelTTerm.btlIter` (label-discarding fold) as the
recursor. -/
def GodelTTerm.interp {S : Set GodelTBase} :
    {n : Nat} → {σ : GodelTType S} →
    GodelTTerm S n σ → (Fin n → Nat) → σ.interp
  | _, _, .var i _, env =>
      env i
  | _, _, .app f a, env =>
      f.interp env (a.interp env)
  | _, _, .zero _, _ =>
      (0 : Nat)
  | _, _, .succ _, _ =>
      Nat.succ
  | _, _, .pred _, _ =>
      Nat.pred
  | _, _, .K _ _, _ =>
      fun a _ => a
  | _, _, .S_comb _ _ _, _ =>
      fun f g x => f x (g x)
  | _, _, .disc _, _ =>
      fun n a b =>
        match n with
        | 0 => a
        | _ + 1 => b
  | _, _, .iter _, _ =>
      fun count step base =>
        Nat.rec base (fun _ prev => step prev) count
  | _, _, .leaf _, _ =>
      BTL.leaf 0
  | _, _, .node _, _ =>
      BTL.node
  | _, _, .treeIter _ _, _ =>
      fun t base step => GodelTTerm.btlIter base step t

@[simp] theorem GodelTTerm.interp_var
    {S : Set GodelTBase} {n : Nat} (i : Fin n)
    (h : GodelTBase.nat ∈ S) (env : Fin n → Nat) :
    (GodelTTerm.var (S := S) i h).interp env = env i := by
  simp [GodelTTerm.interp]

@[simp] theorem GodelTTerm.interp_app
    {S : Set GodelTBase} {n : Nat}
    {σ τ : GodelTType S}
    (f : GodelTTerm S n (.arrow σ τ))
    (a : GodelTTerm S n σ) (env : Fin n → Nat) :
    (GodelTTerm.app f a).interp env =
      f.interp env (a.interp env) := by
  simp [GodelTTerm.interp]

@[simp] theorem GodelTTerm.interp_zero
    {S : Set GodelTBase} {n : Nat} (h : GodelTBase.nat ∈ S)
    (env : Fin n → Nat) :
    (GodelTTerm.zero (S := S) (n := n) h).interp env = 0 := by
  simp [GodelTTerm.interp]

@[simp] theorem GodelTTerm.interp_succ
    {S : Set GodelTBase} {n : Nat} (h : GodelTBase.nat ∈ S)
    (env : Fin n → Nat) :
    (GodelTTerm.succ (S := S) (n := n) h).interp env =
      Nat.succ := by
  simp [GodelTTerm.interp]

@[simp] theorem GodelTTerm.interp_pred
    {S : Set GodelTBase} {n : Nat} (h : GodelTBase.nat ∈ S)
    (env : Fin n → Nat) :
    (GodelTTerm.pred (S := S) (n := n) h).interp env =
      Nat.pred := by
  simp [GodelTTerm.interp]

@[simp] theorem GodelTTerm.interp_K
    {S : Set GodelTBase} {n : Nat} (σ τ : GodelTType S)
    (env : Fin n → Nat) :
    (GodelTTerm.K (S := S) (n := n) σ τ).interp env =
      (fun a _ => a) := by
  simp [GodelTTerm.interp]

@[simp] theorem GodelTTerm.interp_S_comb
    {S : Set GodelTBase} {n : Nat} (ρ σ τ : GodelTType S)
    (env : Fin n → Nat) :
    (GodelTTerm.S_comb (S := S) (n := n) ρ σ τ).interp env =
      (fun f g x => f x (g x)) := by
  simp [GodelTTerm.interp]

@[simp] theorem GodelTTerm.interp_disc
    {S : Set GodelTBase} {n : Nat} {h : GodelTBase.nat ∈ S}
    (σ : GodelTType S) (env : Fin n → Nat) :
    (GodelTTerm.disc (S := S) (n := n) (h := h) σ).interp env =
      (fun n a b => match n with
        | 0 => a
        | _ + 1 => b) := by
  simp [GodelTTerm.interp]

@[simp] theorem GodelTTerm.interp_iter
    {S : Set GodelTBase} {n : Nat} (h : GodelTBase.nat ∈ S)
    (env : Fin n → Nat) :
    (GodelTTerm.iter (S := S) (n := n) h).interp env =
      (fun count step base =>
        Nat.rec base (fun _ prev => step prev) count) := by
  simp [GodelTTerm.interp]

@[simp] theorem GodelTTerm.interp_leaf
    {S : Set GodelTBase} {n : Nat} (h : GodelTBase.tree ∈ S)
    (env : Fin n → Nat) :
    (GodelTTerm.leaf (S := S) (n := n) h).interp env =
      BTL.leaf 0 := by
  simp [GodelTTerm.interp]

@[simp] theorem GodelTTerm.interp_node
    {S : Set GodelTBase} {n : Nat} (h : GodelTBase.tree ∈ S)
    (env : Fin n → Nat) :
    (GodelTTerm.node (S := S) (n := n) h).interp env =
      BTL.node := by
  simp [GodelTTerm.interp]

@[simp] theorem GodelTTerm.interp_treeIter
    {S : Set GodelTBase} {n : Nat} (h : GodelTBase.tree ∈ S)
    (σ : GodelTType S) (env : Fin n → Nat) :
    (GodelTTerm.treeIter (S := S) (n := n) h σ).interp env =
      (fun t base step =>
        GodelTTerm.btlIter base step t) := by
  simp [GodelTTerm.interp]

/-- Substitute base-typed terms (in arity m) for the free
variables of a term in arity n.  Direct structural recursion;
no binders ⇒ no capture concerns. -/
def GodelTTerm.subst {S : Set GodelTBase}
    (hN : GodelTBase.nat ∈ S) {n m : Nat} :
    {σ : GodelTType S} →
    (Fin n → GodelTTerm S m (.base .nat hN)) →
    GodelTTerm S n σ → GodelTTerm S m σ
  | _, ε, .var i _      => ε i
  | _, ε, .app f a      => .app (f.subst hN ε) (a.subst hN ε)
  | _, _, .zero h       => .zero h
  | _, _, .succ h       => .succ h
  | _, _, .pred h       => .pred h
  | _, _, .K σ τ        => .K σ τ
  | _, _, .S_comb ρ σ τ => .S_comb ρ σ τ
  | _, _, .disc σ       => .disc σ
  | _, _, .iter h       => .iter h
  | _, _, .leaf h       => .leaf h
  | _, _, .node h       => .node h
  | _, _, .treeIter h σ => .treeIter h σ

theorem GodelTTerm.interp_subst {S : Set GodelTBase}
    (hN : GodelTBase.nat ∈ S) {n m : Nat}
    (ε : Fin n → GodelTTerm S m (.base .nat hN))
    {σ : GodelTType S} (t : GodelTTerm S n σ)
    (env : Fin m → Nat) :
    (t.subst hN ε).interp env =
      t.interp (fun i => (ε i).interp env) := by
  induction t with
  | var i h => simp [GodelTTerm.subst]
  | app f a ih_f ih_a => simp [GodelTTerm.subst, ih_f, ih_a]
  | zero h => simp [GodelTTerm.subst]
  | succ h => simp [GodelTTerm.subst]
  | pred h => simp [GodelTTerm.subst]
  | K σ τ => simp [GodelTTerm.subst]
  | S_comb ρ σ τ => simp [GodelTTerm.subst]
  | disc σ => simp [GodelTTerm.subst]
  | iter h => simp [GodelTTerm.subst]
  | leaf h => simp [GodelTTerm.subst]
  | node h => simp [GodelTTerm.subst]
  | treeIter h σ => simp [GodelTTerm.subst]

theorem GodelTTerm.subst_var {S : Set GodelTBase}
    (hN : GodelTBase.nat ∈ S) {n : Nat}
    {σ : GodelTType S} (t : GodelTTerm S n σ) :
    t.subst hN (fun i => .var i hN) = t := by
  induction t with
  | var i h => simp [GodelTTerm.subst]
  | app f a ih_f ih_a => simp [GodelTTerm.subst, ih_f, ih_a]
  | zero h => simp [GodelTTerm.subst]
  | succ h => simp [GodelTTerm.subst]
  | pred h => simp [GodelTTerm.subst]
  | K σ τ => simp [GodelTTerm.subst]
  | S_comb ρ σ τ => simp [GodelTTerm.subst]
  | disc σ => simp [GodelTTerm.subst]
  | iter h => simp [GodelTTerm.subst]
  | leaf h => simp [GodelTTerm.subst]
  | node h => simp [GodelTTerm.subst]
  | treeIter h σ => simp [GodelTTerm.subst]

end GebLean
