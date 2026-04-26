import GebLean.LawvereGodelTReduces
import GebLean.Utilities.Tower

/-!
# Lemma 16: structural tower bound for `GodelTTerm`

Following Beckmann-Weiermann 2000 Definitions 7-10 and the
proof of Lemma 16 on pp. 480-484.  All measures are defined
parametrically over `S : Set GodelTBase` and apply uniformly
to the nucleus (`S = {.nat}`) and the binary-tree extension
(`S = {.nat, .tree}`).

`tower` from `Utilities/Tower.lean` matches Beckmann-Weiermann's
`2_m`: `tower 0 x = x`, `tower (k+1) x = 2 ^ tower k x`.
-/

namespace GebLean

/-- Term tree size, mirroring Beckmann-Weiermann's `lh(a)`.
Each constructor (variable or atomic constant) contributes 1;
`app` sums the sub-sizes plus 1. -/
def GodelTTerm.lh {S : Set GodelTBase} :
    {n : Nat} → {σ : GodelTType S} →
    GodelTTerm S n σ → Nat
  | _, _, .var _ _      => 1
  | _, _, .app f a      => f.lh + a.lh + 1
  | _, _, .zero _       => 1
  | _, _, .succ _       => 1
  | _, _, .pred _       => 1
  | _, _, .K _ _        => 1
  | _, _, .S_comb _ _ _ => 1
  | _, _, .disc _       => 1
  | _, _, .iter _       => 1
  | _, _, .leaf _       => 1
  | _, _, .node _       => 1
  | _, _, .treeIter _ _ => 1

/-- Iter-nesting depth, mirroring Beckmann-Weiermann's `d(a)`
from Definition 10.  The `iter` and `treeIter` constants
contribute 1 to the nesting depth; `app` takes the max of its
two children.  All other constructors contribute 0. -/
def GodelTTerm.d {S : Set GodelTBase} :
    {n : Nat} → {σ : GodelTType S} →
    GodelTTerm S n σ → Nat
  | _, _, .var _ _      => 0
  | _, _, .app f a      => max f.d a.d
  | _, _, .zero _       => 0
  | _, _, .succ _       => 0
  | _, _, .pred _       => 0
  | _, _, .K _ _        => 0
  | _, _, .S_comb _ _ _ => 0
  | _, _, .disc _       => 0
  | _, _, .iter _       => 1
  | _, _, .leaf _       => 0
  | _, _, .node _       => 0
  | _, _, .treeIter _ _ => 1

/-- Maximum type level among all sub-terms of a term.  At a
constant or variable of type `σ`, contributes `σ.level`; at
`app f a`, takes the max over `f.G` and `a.G`. -/
def GodelTTerm.G {S : Set GodelTBase} {n : Nat} {σ : GodelTType S}
    (t : GodelTTerm S n σ) : Nat :=
  match t with
  | .var _ _      => σ.level
  | .app f a      => max f.G a.G
  | .zero _       => σ.level
  | .succ _       => σ.level
  | .pred _       => σ.level
  | .K _ _        => σ.level
  | .S_comb _ _ _ => σ.level
  | .disc _       => σ.level
  | .iter _       => σ.level
  | .leaf _       => σ.level
  | .node _       => σ.level
  | .treeIter _ _ => σ.level

/-- Bracket measure `[·]_i` from Beckmann-Weiermann Definition 8
(pp. 480-481).  Each term-and-level pair receives a natural
number used in the proof of Lemma 16's tower bound.

Atomic combinators of type `τ` (rules 8-9): `1` if `i ≤ g(τ)`,
else `0`.  In the typed encoding `K`, `S_comb`, `iter`, `leaf`,
`node`, and `treeIter` are all combinators in this sense.

Iter applied to its first (numeral-shaped) argument (rules
10-13): the iterated type `ρ` is always a base type (`nat` for
`iter`, `tree` for `treeIter`), so `g(ρ) = 0` and the case
dispatch on `i` collapses to: `i = 0 → [t]_0`; `i = 1 → 1`;
`i = 2 → [t]_0`; `i ≥ 3 → 0`.

General application (rules 14-15): if the head is not an
iter-form, branch on whether `i ≤ g(σ)` (where σ is the right
argument's type).  Rule 14 (`i ≤ g(σ)`) refers to `[ab]_{i+1}`
itself; this is realized as a downward iteration from `g(σ)`
to `i` with seed `[a]_{g(σ)+1}` (rule 15 at the boundary).
Rule 15 (`i > g(σ)`) returns `[a]_i`. -/
def GodelTTerm.bracketLevel {S : Set GodelTBase} {n : Nat}
    {σ : GodelTType S}
    (t : GodelTTerm S n σ) (i : Nat) : Nat :=
  match t, i with
  | .var _ _, _ => 0
  | .zero _, _ => 0
  | .succ _, 0 => 1
  | .succ _, _ + 1 => 0
  | .pred _, 0 => 1
  | .pred _, _ + 1 => 0
  | .disc _, 0 => 1
  | .disc _, _ + 1 => 0
  | .K _ _, i => if i ≤ σ.level then 1 else 0
  | .S_comb _ _ _, i => if i ≤ σ.level then 1 else 0
  | .iter _, i => if i ≤ σ.level then 1 else 0
  | .leaf _, i => if i ≤ σ.level then 1 else 0
  | .node _, i => if i ≤ σ.level then 1 else 0
  | .treeIter _ _, i => if i ≤ σ.level then 1 else 0
  | .app (.iter _) t, 0 => t.bracketLevel 0
  | .app (.iter _) _, 1 => 1
  | .app (.iter _) t, 2 => t.bracketLevel 0
  | .app (.iter _) _, _ + 3 => 0
  | .app (.treeIter _ _) t, 0 => t.bracketLevel 0
  | .app (.treeIter _ _) _, 1 => 1
  | .app (.treeIter _ _) t, 2 => t.bracketLevel 0
  | .app (.treeIter _ _) _, _ + 3 => 0
  | .app (σ := σ_inner) f a, i =>
      let g := σ_inner.level
      if i ≤ g then
        Nat.rec (motive := fun _ => Nat) (f.bracketLevel (g + 1))
          (fun k prev =>
            2 ^ prev * (f.bracketLevel (g - k) +
              a.bracketLevel (g - k)))
          (g + 1 - i)
      else
        f.bracketLevel i

@[simp] theorem GodelTTerm.bracketLevel_var
    {S : Set GodelTBase} {n : Nat} (i : Fin n)
    (h : GodelTBase.nat ∈ S) (k : Nat) :
    (GodelTTerm.var (S := S) i h).bracketLevel k = 0 := rfl

@[simp] theorem GodelTTerm.bracketLevel_zero
    {S : Set GodelTBase} {n : Nat} (h : GodelTBase.nat ∈ S)
    (k : Nat) :
    (GodelTTerm.zero (S := S) (n := n) h).bracketLevel k = 0 := rfl

@[simp] theorem GodelTTerm.bracketLevel_succ_zero
    {S : Set GodelTBase} {n : Nat} (h : GodelTBase.nat ∈ S) :
    (GodelTTerm.succ (S := S) (n := n) h).bracketLevel 0 = 1 :=
  rfl

@[simp] theorem GodelTTerm.bracketLevel_succ_pos
    {S : Set GodelTBase} {n : Nat} (h : GodelTBase.nat ∈ S)
    (k : Nat) :
    (GodelTTerm.succ (S := S) (n := n) h).bracketLevel
      (k + 1) = 0 := rfl

@[simp] theorem GodelTTerm.bracketLevel_pred_zero
    {S : Set GodelTBase} {n : Nat} (h : GodelTBase.nat ∈ S) :
    (GodelTTerm.pred (S := S) (n := n) h).bracketLevel 0 = 1 :=
  rfl

@[simp] theorem GodelTTerm.bracketLevel_pred_pos
    {S : Set GodelTBase} {n : Nat} (h : GodelTBase.nat ∈ S)
    (k : Nat) :
    (GodelTTerm.pred (S := S) (n := n) h).bracketLevel
      (k + 1) = 0 := rfl

@[simp] theorem GodelTTerm.bracketLevel_disc_zero
    {S : Set GodelTBase} {n : Nat} {h : GodelTBase.nat ∈ S}
    (σ : GodelTType S) :
    (GodelTTerm.disc (S := S) (n := n) (h := h) σ).bracketLevel
      0 = 1 := rfl

@[simp] theorem GodelTTerm.bracketLevel_disc_pos
    {S : Set GodelTBase} {n : Nat} {h : GodelTBase.nat ∈ S}
    (σ : GodelTType S) (k : Nat) :
    (GodelTTerm.disc (S := S) (n := n) (h := h) σ).bracketLevel
      (k + 1) = 0 := rfl

@[simp] theorem GodelTTerm.bracketLevel_K
    {S : Set GodelTBase} {n : Nat} (σ τ : GodelTType S)
    (i : Nat) :
    (GodelTTerm.K (S := S) (n := n) σ τ).bracketLevel i =
      if i ≤ (GodelTType.arrow σ (.arrow τ σ)).level then 1
      else 0 := rfl

@[simp] theorem GodelTTerm.bracketLevel_S_comb
    {S : Set GodelTBase} {n : Nat} (ρ σ τ : GodelTType S)
    (i : Nat) :
    (GodelTTerm.S_comb (S := S) (n := n) ρ σ τ).bracketLevel i =
      if i ≤ (GodelTType.arrow (.arrow ρ (.arrow σ τ))
          (.arrow (.arrow ρ σ) (.arrow ρ τ))).level then 1
      else 0 := rfl

@[simp] theorem GodelTTerm.bracketLevel_iter
    {S : Set GodelTBase} {n : Nat} (h : GodelTBase.nat ∈ S)
    (i : Nat) :
    (GodelTTerm.iter (S := S) (n := n) h).bracketLevel i =
      if i ≤ (GodelTType.arrow (.base .nat h)
          (.arrow (.arrow (.base .nat h) (.base .nat h))
            (.arrow (.base .nat h) (.base .nat h)))).level then 1
      else 0 := rfl

@[simp] theorem GodelTTerm.bracketLevel_leaf
    {S : Set GodelTBase} {n : Nat} (h : GodelTBase.tree ∈ S)
    (i : Nat) :
    (GodelTTerm.leaf (S := S) (n := n) h).bracketLevel i =
      if i ≤ (GodelTType.base GodelTBase.tree h).level then 1
      else 0 := rfl

@[simp] theorem GodelTTerm.bracketLevel_node
    {S : Set GodelTBase} {n : Nat} (h : GodelTBase.tree ∈ S)
    (i : Nat) :
    (GodelTTerm.node (S := S) (n := n) h).bracketLevel i =
      if i ≤ (GodelTType.arrow (.base .tree h)
          (.arrow (.base .tree h) (.base .tree h))).level then 1
      else 0 := rfl

@[simp] theorem GodelTTerm.bracketLevel_treeIter
    {S : Set GodelTBase} {n : Nat} (h : GodelTBase.tree ∈ S)
    (σ : GodelTType S) (i : Nat) :
    (GodelTTerm.treeIter (S := S) (n := n) h σ).bracketLevel i =
      if i ≤ (GodelTType.arrow (.base .tree h)
          (.arrow σ (.arrow (.arrow σ (.arrow σ σ)) σ))).level
        then 1
      else 0 := rfl

@[simp] theorem GodelTTerm.bracketLevel_app_iter_zero
    {S : Set GodelTBase} {n : Nat} (h : GodelTBase.nat ∈ S)
    (t : GodelTTerm S n (.base .nat h)) :
    (GodelTTerm.app (GodelTTerm.iter h) t).bracketLevel 0 =
      t.bracketLevel 0 := rfl

@[simp] theorem GodelTTerm.bracketLevel_app_iter_one
    {S : Set GodelTBase} {n : Nat} (h : GodelTBase.nat ∈ S)
    (t : GodelTTerm S n (.base .nat h)) :
    (GodelTTerm.app (GodelTTerm.iter h) t).bracketLevel 1 = 1 :=
  rfl

@[simp] theorem GodelTTerm.bracketLevel_app_iter_two
    {S : Set GodelTBase} {n : Nat} (h : GodelTBase.nat ∈ S)
    (t : GodelTTerm S n (.base .nat h)) :
    (GodelTTerm.app (GodelTTerm.iter h) t).bracketLevel 2 =
      t.bracketLevel 0 := rfl

@[simp] theorem GodelTTerm.bracketLevel_app_iter_ge_three
    {S : Set GodelTBase} {n : Nat} (h : GodelTBase.nat ∈ S)
    (t : GodelTTerm S n (.base .nat h)) (k : Nat) :
    (GodelTTerm.app (GodelTTerm.iter h) t).bracketLevel
      (k + 3) = 0 := rfl

@[simp] theorem GodelTTerm.bracketLevel_app_treeIter_zero
    {S : Set GodelTBase} {n : Nat} (h : GodelTBase.tree ∈ S)
    (σ : GodelTType S) (t : GodelTTerm S n (.base .tree h)) :
    (GodelTTerm.app (GodelTTerm.treeIter h σ) t).bracketLevel
      0 = t.bracketLevel 0 := rfl

@[simp] theorem GodelTTerm.bracketLevel_app_treeIter_one
    {S : Set GodelTBase} {n : Nat} (h : GodelTBase.tree ∈ S)
    (σ : GodelTType S) (t : GodelTTerm S n (.base .tree h)) :
    (GodelTTerm.app (GodelTTerm.treeIter h σ) t).bracketLevel
      1 = 1 := rfl

@[simp] theorem GodelTTerm.bracketLevel_app_treeIter_two
    {S : Set GodelTBase} {n : Nat} (h : GodelTBase.tree ∈ S)
    (σ : GodelTType S) (t : GodelTTerm S n (.base .tree h)) :
    (GodelTTerm.app (GodelTTerm.treeIter h σ) t).bracketLevel
      2 = t.bracketLevel 0 := rfl

@[simp] theorem GodelTTerm.bracketLevel_app_treeIter_ge_three
    {S : Set GodelTBase} {n : Nat} (h : GodelTBase.tree ∈ S)
    (σ : GodelTType S) (t : GodelTTerm S n (.base .tree h))
    (k : Nat) :
    (GodelTTerm.app (GodelTTerm.treeIter h σ) t).bracketLevel
      (k + 3) = 0 := rfl

end GebLean
