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

/-- The head of an application is the bare `iter` or
`treeIter` constant.  Used to dispatch between rules 10-13
(iter-form) and rules 14-15 (general `app`) of
Beckmann-Weiermann Definition 8. -/
def GodelTTerm.isIterHead {S : Set GodelTBase}
    {n : Nat} {σ : GodelTType S} :
    GodelTTerm S n σ → Bool
  | .iter _ => true
  | .treeIter _ _ => true
  | _ => false

/-- Bracket measure for a general application `app f a`,
parameterized by the recursive bracketLevel of subterms.
Used as the rule-14/15 case of `bracketLevel` when `f` is not
the bare iter/treeIter constant.  When `i ≤ σ.level`, computed
via downward `Nat.rec` iteration from `σ.level + 1` to `i`,
matching Beckmann-Weiermann Definition 8 case 14.  When
`i > σ.level`, returns `bf i` (rule 15). -/
def GodelTTerm.bracketLevelAppGen (g : Nat) (i : Nat)
    (bf : Nat → Nat) (ba : Nat → Nat) : Nat :=
  if i ≤ g then
    Nat.rec (motive := fun _ => Nat) (bf (g + 1))
      (fun k prev =>
        2 ^ prev * (bf (g - k) + ba (g - k)))
      (g + 1 - i)
  else
    bf i

/-- Bracket measure for an iter-form application
`app (iter _) t` (rules 10-13 of Beckmann-Weiermann
Definition 8).  Since the iterated type ρ is base `nat` with
`g(ρ) = 0`, the case dispatch on `i` collapses to four
discrete cases. -/
def GodelTTerm.bracketLevelAppIter (i : Nat) (bt : Nat) :
    Nat :=
  match i with
  | 0 => bt
  | 1 => 1
  | 2 => bt
  | _ + 3 => 0

/-- Bracket measure `[·]_i` from Beckmann-Weiermann Definition 8
(pp. 480-481).  Each term-and-level pair receives a natural
number used in the proof of Lemma 16's tower bound.

Atomic combinators of type `τ` (rules 8-9): `1` if `i ≤ g(τ)`,
else `0`.  In the typed encoding `K`, `S_comb`, `iter`, `leaf`,
`node`, and `treeIter` are all combinators in this sense.

Iter applied to its first (numeral-shaped) argument (rules
10-13) is delegated to `bracketLevelAppIter`; general
applications (rules 14-15) are delegated to
`bracketLevelAppGen`.  The iter-vs-general dispatch is
performed by `isIterHead`. -/
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
  | .app (σ := σ_inner) f a, i =>
      if f.isIterHead then
        GodelTTerm.bracketLevelAppIter i (a.bracketLevel 0)
      else
        GodelTTerm.bracketLevelAppGen σ_inner.level i
          f.bracketLevel a.bracketLevel

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

/-- For an application whose head is not the bare iter or
treeIter constant, `bracketLevel` reduces to
`bracketLevelAppGen`, which directly encodes Beckmann-Weiermann
Definition 8 cases 14-15. -/
theorem GodelTTerm.bracketLevel_app_of_not_iter
    {S : Set GodelTBase} {n : Nat}
    {σ τ : GodelTType S}
    (f : GodelTTerm S n (.arrow σ τ))
    (a : GodelTTerm S n σ)
    (i : Nat)
    (hNotIter : f.isIterHead = false) :
    (GodelTTerm.app f a).bracketLevel i =
      GodelTTerm.bracketLevelAppGen σ.level i
        f.bracketLevel a.bracketLevel := by
  change (if f.isIterHead then _ else _) = _
  rw [hNotIter]
  rfl

/-- Beckmann-Weiermann Lemma 5.1 (multiplicative form).
For an application `app f a` whose head `f` is not the bare
iter/treeIter constant, and at level `i ≤ g(σ)` (where σ is
the type of the right argument):

  [app f a]_i = 2^[app f a]_{i+1} * ([f]_i + [a]_i).

This is paper-faithful equality: our `bracketLevel`'s internal
`Nat.rec` downward iteration unfolds to this form when the
threshold check `i ≤ σ.level` succeeds. -/
theorem GodelTTerm.bracketLevel_app_eq
    {S : Set GodelTBase} {n : Nat}
    {σ τ : GodelTType S}
    (f : GodelTTerm S n (.arrow σ τ))
    (a : GodelTTerm S n σ)
    (i : Nat) (hi : i ≤ σ.level)
    (hNotIter : f.isIterHead = false) :
    (GodelTTerm.app f a).bracketLevel i =
      2 ^ (GodelTTerm.app f a).bracketLevel (i + 1) *
        (f.bracketLevel i + a.bracketLevel i) := by
  rw [GodelTTerm.bracketLevel_app_of_not_iter f a i hNotIter,
      GodelTTerm.bracketLevel_app_of_not_iter f a (i + 1)
        hNotIter]
  unfold GodelTTerm.bracketLevelAppGen
  rw [if_pos hi]
  have hsucc : σ.level + 1 - i = (σ.level - i) + 1 := by
    omega
  rw [hsucc]
  rcases Nat.lt_or_ge (i + 1) (σ.level + 1) with hi1 | hi1
  · have hi1' : i + 1 ≤ σ.level := Nat.lt_succ_iff.mp hi1
    rw [if_pos hi1']
    have hsub : σ.level + 1 - (i + 1) = σ.level - i := by
      omega
    rw [hsub]
    have hg : σ.level - (σ.level - i) = i := by omega
    simp only [hg]
  · have hi1' : ¬ i + 1 ≤ σ.level := by omega
    rw [if_neg hi1']
    have hi_eq : i = σ.level := by omega
    have hsubz : σ.level - i = 0 := by omega
    rw [hsubz]
    change 2 ^ f.bracketLevel (σ.level + 1) *
        (f.bracketLevel (σ.level - 0) +
          a.bracketLevel (σ.level - 0)) = _
    have hgz : σ.level - 0 = σ.level := by omega
    rw [hgz, hi_eq]

/-- Beckmann-Weiermann Lemma 5.2 (pass-through form).
For an application `app f a` whose head `f` is not the bare
iter/treeIter constant, and at level `i > g(σ)`:

  [app f a]_i = [f]_i.

This is rule 15 of Beckmann-Weiermann Definition 8. -/
theorem GodelTTerm.bracketLevel_app_high
    {S : Set GodelTBase} {n : Nat}
    {σ τ : GodelTType S}
    (f : GodelTTerm S n (.arrow σ τ))
    (a : GodelTTerm S n σ)
    (i : Nat) (hi : σ.level < i)
    (hNotIter : f.isIterHead = false) :
    (GodelTTerm.app f a).bracketLevel i =
      f.bracketLevel i := by
  rw [GodelTTerm.bracketLevel_app_of_not_iter f a i hNotIter]
  unfold GodelTTerm.bracketLevelAppGen
  rw [if_neg (Nat.not_le_of_lt hi)]

/-- For an application `app f a` whose head is not the bare
iter/treeIter constant, and at level `i ≤ g(σ)` (σ the right
argument's type): `[a]_i ≤ [app f a]_i` and
`[f]_i ≤ [app f a]_i`. -/
theorem GodelTTerm.bracketLevel_app_ge_arg
    {S : Set GodelTBase} {n : Nat}
    {σ τ : GodelTType S}
    (f : GodelTTerm S n (.arrow σ τ))
    (a : GodelTTerm S n σ)
    (i : Nat) (hi : i ≤ σ.level)
    (hNotIter : f.isIterHead = false) :
    a.bracketLevel i ≤ (GodelTTerm.app f a).bracketLevel i ∧
    f.bracketLevel i ≤ (GodelTTerm.app f a).bracketLevel i := by
  rw [GodelTTerm.bracketLevel_app_eq f a i hi hNotIter]
  have hp : 1 ≤ 2 ^ (GodelTTerm.app f a).bracketLevel (i + 1) :=
    Nat.one_le_iff_ne_zero.mpr (by positivity)
  refine ⟨?_, ?_⟩
  · calc a.bracketLevel i
        ≤ f.bracketLevel i + a.bracketLevel i := by omega
      _ ≤ 2 ^ (GodelTTerm.app f a).bracketLevel (i + 1) *
            (f.bracketLevel i + a.bracketLevel i) := by
              exact Nat.le_mul_of_pos_left _ hp
  · calc f.bracketLevel i
        ≤ f.bracketLevel i + a.bracketLevel i := by omega
      _ ≤ 2 ^ (GodelTTerm.app f a).bracketLevel (i + 1) *
            (f.bracketLevel i + a.bracketLevel i) := by
              exact Nat.le_mul_of_pos_left _ hp

/-- For an application `app f a` whose head is not the bare
iter/treeIter constant, at level `i ≤ g(σ)`, with `[f]_i ≥ 1`:
`[a]_i < [app f a]_i`. -/
theorem GodelTTerm.bracketLevel_app_strict_arg
    {S : Set GodelTBase} {n : Nat}
    {σ τ : GodelTType S}
    (f : GodelTTerm S n (.arrow σ τ))
    (a : GodelTTerm S n σ)
    (i : Nat) (hi : i ≤ σ.level)
    (hNotIter : f.isIterHead = false)
    (hF : 1 ≤ f.bracketLevel i) :
    a.bracketLevel i < (GodelTTerm.app f a).bracketLevel i := by
  rw [GodelTTerm.bracketLevel_app_eq f a i hi hNotIter]
  have hp : 1 ≤ 2 ^ (GodelTTerm.app f a).bracketLevel (i + 1) :=
    Nat.one_le_iff_ne_zero.mpr (by positivity)
  calc a.bracketLevel i
      < f.bracketLevel i + a.bracketLevel i := by omega
    _ ≤ 2 ^ (GodelTTerm.app f a).bracketLevel (i + 1) *
          (f.bracketLevel i + a.bracketLevel i) := by
            exact Nat.le_mul_of_pos_left _ hp

/-- Beckmann-Weiermann's `≫` majorization relation
(Definition 9): `a ≫ b` if `[a]_0 > [b]_0` and `[a]_i ≥ [b]_i`
for all `i ≤ g(σ)` (where σ is the common type). -/
def GodelTTerm.majorizes {S : Set GodelTBase} {n : Nat}
    {σ : GodelTType S} (t s : GodelTTerm S n σ) : Prop :=
  s.bracketLevel 0 < t.bracketLevel 0 ∧
  ∀ i, i ≤ σ.level → s.bracketLevel i ≤ t.bracketLevel i

/-- Beckmann-Weiermann Lemma 6: `P(0) ≫ 0`. -/
theorem GodelTTerm.majorizes_redP_zero {S : Set GodelTBase}
    {n : Nat} (hN : GodelTBase.nat ∈ S) :
    GodelTTerm.majorizes
      (.app (.pred (n := n) (S := S) hN) (.zero hN))
      (.zero (n := n) (S := S) hN) := by
  have hNotIter :
      (GodelTTerm.pred (n := n) (S := S) hN).isIterHead = false := rfl
  have hLevel :
      (GodelTType.base GodelTBase.nat hN).level = 0 := rfl
  have hHi : (GodelTTerm.app (.pred (n := n) (S := S) hN)
      (.zero hN)).bracketLevel 1 = 0 := by
    rw [GodelTTerm.bracketLevel_app_high _ _ 1
      (by rw [hLevel]; exact Nat.zero_lt_one) hNotIter]
    rfl
  have hZero : (GodelTTerm.app (.pred (n := n) (S := S) hN)
      (.zero hN)).bracketLevel 0 = 1 := by
    rw [GodelTTerm.bracketLevel_app_eq _ _ 0
      (by rw [hLevel]) hNotIter, hHi]
    rfl
  refine ⟨?_, ?_⟩
  · rw [hZero]; exact Nat.zero_lt_one
  · intro i _
    rw [GodelTTerm.bracketLevel_zero]
    exact Nat.zero_le _

/-- Beckmann-Weiermann Lemma 7: `P(S^+ t) ≫ t`. -/
theorem GodelTTerm.majorizes_redP_succ {S : Set GodelTBase}
    {n : Nat} (hN : GodelTBase.nat ∈ S)
    (t : GodelTTerm S n (.base .nat hN)) :
    GodelTTerm.majorizes
      (.app (.pred (n := n) hN) (.app (.succ hN) t)) t := by
  have hPredNotIter :
      (GodelTTerm.pred (n := n) (S := S) hN).isIterHead = false := rfl
  have hSuccNotIter :
      (GodelTTerm.succ (n := n) (S := S) hN).isIterHead = false := rfl
  have hLevel :
      (GodelTType.base GodelTBase.nat hN).level = 0 := rfl
  have hSuccHi :
      (GodelTTerm.app (.succ (n := n) hN) t).bracketLevel 1 = 0 := by
    rw [GodelTTerm.bracketLevel_app_high _ _ 1
      (by rw [hLevel]; exact Nat.zero_lt_one) hSuccNotIter]
    rfl
  have hSuccZero :
      (GodelTTerm.app (.succ (n := n) hN) t).bracketLevel 0 =
        1 + t.bracketLevel 0 := by
    rw [GodelTTerm.bracketLevel_app_eq _ _ 0
      (by rw [hLevel]) hSuccNotIter, hSuccHi]
    change 2 ^ 0 * (1 + t.bracketLevel 0) = 1 + t.bracketLevel 0
    simp
  have hPredHi :
      (GodelTTerm.app (.pred (n := n) hN)
        (.app (.succ hN) t)).bracketLevel 1 = 0 := by
    rw [GodelTTerm.bracketLevel_app_high _ _ 1
      (by rw [hLevel]; exact Nat.zero_lt_one) hPredNotIter]
    rfl
  have hPredZero :
      (GodelTTerm.app (.pred (n := n) hN)
        (.app (.succ hN) t)).bracketLevel 0 =
        1 + (1 + t.bracketLevel 0) := by
    rw [GodelTTerm.bracketLevel_app_eq _ _ 0
      (by rw [hLevel]) hPredNotIter, hPredHi, hSuccZero]
    change 2 ^ 0 * (1 + (1 + t.bracketLevel 0)) = _
    simp
  refine ⟨?_, ?_⟩
  · rw [hPredZero]; omega
  · intro i hi
    rw [hLevel] at hi
    obtain rfl : i = 0 := Nat.le_zero.mp hi
    rw [hPredZero]; omega

/-- For an application `app f a` whose head is not the bare
iter/treeIter constant, at level `i > g(σ)`, with
`x.bracketLevel i ≤ f.bracketLevel i`:
`x.bracketLevel i ≤ (app f a).bracketLevel i`. -/
theorem GodelTTerm.bracketLevel_app_high_ge
    {S : Set GodelTBase} {n : Nat}
    {σ τ : GodelTType S}
    (f : GodelTTerm S n (.arrow σ τ))
    (a : GodelTTerm S n σ)
    (i : Nat) (hi : σ.level < i)
    (hNotIter : f.isIterHead = false)
    {x : Nat} (hx : x ≤ f.bracketLevel i) :
    x ≤ (GodelTTerm.app f a).bracketLevel i := by
  rw [GodelTTerm.bracketLevel_app_high f a i hi hNotIter]
  exact hx

/-- Beckmann-Weiermann Lemma 8: `K_στ a b ≫ a`. -/
theorem GodelTTerm.majorizes_redK {S : Set GodelTBase}
    {n : Nat} (σ τ : GodelTType S)
    (a : GodelTTerm S n σ) (b : GodelTTerm S n τ) :
    GodelTTerm.majorizes
      (.app (.app (.K (n := n) σ τ) a) b) a := by
  have hKNotIter :
      (GodelTTerm.K (n := n) (S := S) σ τ).isIterHead = false := rfl
  have hAppKaNotIter :
      (GodelTTerm.app (GodelTTerm.K (n := n) (S := S) σ τ) a).isIterHead =
        false := rfl
  have hKLevel :
      (GodelTType.arrow σ (.arrow τ σ)).level ≥ σ.level + 1 := by
    change max (σ.level + 1) (max (τ.level + 1) σ.level) ≥ σ.level + 1
    omega
  have hK_one : ∀ i, i ≤ σ.level →
      (GodelTTerm.K (n := n) (S := S) σ τ).bracketLevel i = 1 := by
    intro i hi
    rw [GodelTTerm.bracketLevel_K]
    have : i ≤ (GodelTType.arrow σ (.arrow τ σ)).level := by omega
    rw [if_pos this]
  refine ⟨?_, ?_⟩
  · -- Strict at i = 0.
    have hK0 : (GodelTTerm.K (n := n) (S := S) σ τ).bracketLevel 0 = 1 :=
      hK_one 0 (Nat.zero_le _)
    have hInner :
        a.bracketLevel 0 <
          (GodelTTerm.app (.K (n := n) σ τ) a).bracketLevel 0 := by
      apply GodelTTerm.bracketLevel_app_strict_arg _ _ 0
        (Nat.zero_le _) hKNotIter
      rw [hK0]
    -- For outer, σ_inner = τ; 0 ≤ τ.level always.
    have hOuter :
        (GodelTTerm.app (.K (n := n) σ τ) a).bracketLevel 0 ≤
          (GodelTTerm.app (.app (.K (n := n) σ τ) a) b).bracketLevel 0 :=
      ((GodelTTerm.bracketLevel_app_ge_arg _ b 0
        (Nat.zero_le _) hAppKaNotIter).2)
    omega
  · intro i hi
    have hInner :
        a.bracketLevel i ≤
          (GodelTTerm.app (.K (n := n) σ τ) a).bracketLevel i :=
      ((GodelTTerm.bracketLevel_app_ge_arg _ a i hi hKNotIter).1)
    rcases Nat.lt_or_ge τ.level i with hτ | hτ
    · -- i > τ.level: outer pass-through.
      exact GodelTTerm.bracketLevel_app_high_ge _ b i hτ hAppKaNotIter
        hInner
    · -- i ≤ τ.level: outer multiplicative.
      have hOuter :
          (GodelTTerm.app (.K (n := n) σ τ) a).bracketLevel i ≤
            (GodelTTerm.app (.app (.K (n := n) σ τ) a) b).bracketLevel
              i :=
        ((GodelTTerm.bracketLevel_app_ge_arg _ b i hτ hAppKaNotIter).2)
      omega

/-- Beckmann-Weiermann Lemma 9: `D_σ 0 a b ≫ a`. -/
theorem GodelTTerm.majorizes_redDisc_zero {S : Set GodelTBase}
    {n : Nat} {hN : GodelTBase.nat ∈ S}
    (σ : GodelTType S)
    (a b : GodelTTerm S n σ) :
    GodelTTerm.majorizes
      (.app (.app (.app
        (.disc (n := n) (h := hN) σ) (.zero hN)) a) b) a := by
  have hDiscNotIter :
      (GodelTTerm.disc (n := n) (S := S) (h := hN) σ).isIterHead =
        false := rfl
  have hAppDZ_NotIter :
      (GodelTTerm.app (GodelTTerm.disc (n := n) (S := S)
        (h := hN) σ) (.zero hN)).isIterHead = false := rfl
  have hAppDZA_NotIter :
      (GodelTTerm.app (GodelTTerm.app (GodelTTerm.disc
        (n := n) (S := S) (h := hN) σ) (.zero hN))
        a).isIterHead = false := rfl
  have hNatLevel : (GodelTType.base GodelTBase.nat hN).level = 0 := rfl
  -- Compute `[app .disc 0_]_0 ≥ 1`.
  have hAppDZ_ge_one_zero :
      1 ≤ (GodelTTerm.app (.disc (n := n) (h := hN) σ)
        (.zero hN)).bracketLevel 0 := by
    rw [GodelTTerm.bracketLevel_app_eq _ _ 0
      (by rw [hNatLevel]) hDiscNotIter]
    have hp : 1 ≤ 2 ^ (GodelTTerm.app (.disc (n := n) (h := hN) σ)
        (.zero hN)).bracketLevel (0 + 1) :=
      Nat.one_le_iff_ne_zero.mpr (by positivity)
    have hd0 : (GodelTTerm.disc
        (n := n) (S := S) (h := hN) σ).bracketLevel 0 = 1 := rfl
    have hz0 : (GodelTTerm.zero (n := n) (S := S) hN).bracketLevel 0
        = 0 := rfl
    rw [hd0, hz0]
    exact Nat.le_mul_of_pos_left _ hp
  refine ⟨?_, ?_⟩
  · -- Strict at i = 0.
    have hMidStrict :
        a.bracketLevel 0 <
          (GodelTTerm.app (.app (.disc (h := hN) σ)
            (.zero hN)) a).bracketLevel 0 := by
      apply GodelTTerm.bracketLevel_app_strict_arg _ _ 0
        (Nat.zero_le _) hAppDZ_NotIter
      exact hAppDZ_ge_one_zero
    have hOuter :
        (GodelTTerm.app (.app (.disc (h := hN) σ)
          (.zero hN)) a).bracketLevel 0 ≤
          (GodelTTerm.app (.app (.app (.disc (h := hN) σ)
            (.zero hN)) a) b).bracketLevel 0 :=
      ((GodelTTerm.bracketLevel_app_ge_arg _ b 0
        (Nat.zero_le _) hAppDZA_NotIter).2)
    omega
  · intro i hi
    have hMid :
        a.bracketLevel i ≤
          (GodelTTerm.app (.app (.disc (h := hN) σ)
            (.zero hN)) a).bracketLevel i :=
      ((GodelTTerm.bracketLevel_app_ge_arg _ a i hi
        hAppDZ_NotIter).1)
    rcases Nat.lt_or_ge σ.level i with hσ | hσ
    · exact GodelTTerm.bracketLevel_app_high_ge _ b i hσ
        hAppDZA_NotIter hMid
    · have hOuter :
          (GodelTTerm.app (.app (.disc (h := hN) σ)
            (.zero hN)) a).bracketLevel i ≤
            (GodelTTerm.app (.app (.app (.disc (h := hN) σ)
              (.zero hN)) a) b).bracketLevel i :=
        ((GodelTTerm.bracketLevel_app_ge_arg _ b i hσ
          hAppDZA_NotIter).2)
      omega

/-- Beckmann-Weiermann Lemma 10: `D_σ (S^+ t) a b ≫ b`. -/
theorem GodelTTerm.majorizes_redDisc_succ {S : Set GodelTBase}
    {n : Nat} {hN : GodelTBase.nat ∈ S}
    (σ : GodelTType S)
    (t : GodelTTerm S n (.base .nat hN))
    (a b : GodelTTerm S n σ) :
    GodelTTerm.majorizes
      (.app (.app (.app
        (.disc (n := n) (h := hN) σ)
        (.app (.succ hN) t)) a) b) b := by
  have hDiscNotIter :
      (GodelTTerm.disc (n := n) (S := S) (h := hN) σ).isIterHead =
        false := rfl
  have hAppDS_NotIter :
      (GodelTTerm.app (GodelTTerm.disc (n := n) (S := S)
        (h := hN) σ) (.app (.succ hN) t)).isIterHead = false := rfl
  have hAppDSA_NotIter :
      (GodelTTerm.app (GodelTTerm.app (GodelTTerm.disc
        (n := n) (S := S) (h := hN) σ) (.app (.succ hN) t))
        a).isIterHead = false := rfl
  have hNatLevel : (GodelTType.base GodelTBase.nat hN).level = 0 := rfl
  -- `[app .disc (app .succ t)]_0 ≥ 1`.
  have hAppDS_ge_one_zero :
      1 ≤ (GodelTTerm.app (.disc (n := n) (h := hN) σ)
        (.app (.succ hN) t)).bracketLevel 0 := by
    rw [GodelTTerm.bracketLevel_app_eq _ _ 0
      (by rw [hNatLevel]) hDiscNotIter]
    have hp : 1 ≤ 2 ^ (GodelTTerm.app (.disc (n := n) (h := hN) σ)
        (.app (.succ hN) t)).bracketLevel (0 + 1) :=
      Nat.one_le_iff_ne_zero.mpr (by positivity)
    have hd0 : (GodelTTerm.disc
        (n := n) (S := S) (h := hN) σ).bracketLevel 0 = 1 := rfl
    rw [hd0]
    calc (1 : Nat)
        ≤ 1 + (GodelTTerm.app (.succ hN) t).bracketLevel 0 := by omega
      _ ≤ 2 ^ _ * (1 + (GodelTTerm.app (.succ hN) t).bracketLevel 0) :=
          Nat.le_mul_of_pos_left _ hp
  -- `[app (app .disc (app .succ t)) a]_0 ≥ 1`.
  have hMid_ge_one_zero :
      1 ≤ (GodelTTerm.app (.app (.disc (n := n) (h := hN) σ)
        (.app (.succ hN) t)) a).bracketLevel 0 := by
    rw [GodelTTerm.bracketLevel_app_eq _ _ 0
      (Nat.zero_le _) hAppDS_NotIter]
    have hp : 1 ≤ 2 ^ (GodelTTerm.app (.app (.disc (n := n) (h := hN) σ)
        (.app (.succ hN) t)) a).bracketLevel (0 + 1) :=
      Nat.one_le_iff_ne_zero.mpr (by positivity)
    calc (1 : Nat)
        ≤ (GodelTTerm.app (.disc (n := n) (h := hN) σ)
            (.app (.succ hN) t)).bracketLevel 0 + a.bracketLevel 0 := by
              have := hAppDS_ge_one_zero; omega
      _ ≤ 2 ^ _ * _ := Nat.le_mul_of_pos_left _ hp
  refine ⟨?_, ?_⟩
  · have hStrict :
        b.bracketLevel 0 <
          (GodelTTerm.app (.app (.app (.disc (h := hN) σ)
            (.app (.succ hN) t)) a) b).bracketLevel 0 := by
      apply GodelTTerm.bracketLevel_app_strict_arg _ _ 0
        (Nat.zero_le _) hAppDSA_NotIter
      exact hMid_ge_one_zero
    exact hStrict
  · intro i hi
    exact (GodelTTerm.bracketLevel_app_ge_arg _ b i hi
      hAppDSA_NotIter).1


/-- For any term `t` of type `σ`, `G(t) ≥ σ.level`. -/
theorem GodelTTerm.G_ge_level {S : Set GodelTBase} {n : Nat}
    {σ : GodelTType S} (t : GodelTTerm S n σ) :
    σ.level ≤ t.G := by
  induction t with
  | var _ _ => rfl
  | zero _ => rfl
  | succ _ => rfl
  | pred _ => rfl
  | disc _ => rfl
  | K _ _ => rfl
  | S_comb _ _ _ => rfl
  | iter _ => rfl
  | leaf _ => rfl
  | node _ => rfl
  | treeIter _ _ => rfl
  | app f _a ihf _iha =>
      -- f : GodelTTerm S n (σ_inner.arrow σ).
      -- G(app f a) = max(G f, G a) ≥ G(f) ≥ (σ_inner→σ).level ≥ σ.level
      simp only [GodelTTerm.G]
      simp only [GodelTType.level] at ihf
      omega

/-- B-W Lemma 2: `[a]_i = 0` for all `i > G(a)`. -/
theorem GodelTTerm.bracketLevel_high_zero {S : Set GodelTBase}
    {n : Nat} {σ : GodelTType S}
    (t : GodelTTerm S n σ) (i : Nat)
    (hi : t.G < i) : t.bracketLevel i = 0 := by
  induction t with
  | var _ _ => rfl
  | zero _ => rfl
  | succ _ =>
      simp only [GodelTTerm.G] at hi
      cases i with
      | zero => simp [GodelTType.level] at hi
      | succ k => rfl
  | pred _ =>
      simp only [GodelTTerm.G] at hi
      cases i with
      | zero => simp [GodelTType.level] at hi
      | succ k => rfl
  | disc _ =>
      simp only [GodelTTerm.G] at hi
      cases i with
      | zero => simp [GodelTType.level] at hi
      | succ k => rfl
  | K σ' τ' =>
      simp only [GodelTTerm.G] at hi
      simp only [GodelTTerm.bracketLevel]
      rw [if_neg (by omega)]
  | S_comb ρ' σ' τ' =>
      simp only [GodelTTerm.G] at hi
      simp only [GodelTTerm.bracketLevel]
      rw [if_neg (by omega)]
  | iter _ =>
      simp only [GodelTTerm.G] at hi
      simp only [GodelTTerm.bracketLevel]
      rw [if_neg (by omega)]
  | leaf _ =>
      simp only [GodelTTerm.G] at hi
      simp only [GodelTTerm.bracketLevel]
      rw [if_neg (by omega)]
  | node _ =>
      simp only [GodelTTerm.G] at hi
      simp only [GodelTTerm.bracketLevel]
      rw [if_neg (by omega)]
  | treeIter _ _ =>
      simp only [GodelTTerm.G] at hi
      simp only [GodelTTerm.bracketLevel]
      rw [if_neg (by omega)]
  | app f a ihf _iha =>
      simp only [GodelTTerm.G] at hi
      -- G(app f a) = max(G f, G a); so G f < i.
      have hGf : f.G < i := by omega
      by_cases hIter : f.isIterHead = true
      · -- iter-form: f is bare iter or treeIter.
        -- iter has G = 2, treeIter has G ≥ 2, so i ≥ 3,
        -- making bracketLevelAppIter i _ = 0.
        simp only [GodelTTerm.bracketLevel, if_pos hIter,
          GodelTTerm.bracketLevelAppIter]
        cases f with
        | iter hN =>
            have hGiter :
                (GodelTTerm.iter (S := S) (n := n) hN).G = 2 := rfl
            simp only [hGiter] at hGf hi
            rcases i with _ | _ | _ | k <;> simp_all
        | treeIter hT σ' =>
            have hGti :
                (GodelTTerm.treeIter (S := S) (n := n) hT σ').G ≥ 2 := by
              simp [GodelTTerm.G, GodelTType.level]
            have h3i : 2 < i := Nat.lt_of_le_of_lt hGti hGf
            rcases i with _ | _ | _ | k <;> simp_all
        | _ => exact absurd hIter (by simp [GodelTTerm.isIterHead])
      · -- non-iter app: rule 15 gives [app f a]_i = [f]_i when
        -- i > σ_inner.level.  Since G(f) ≥ (σ_inner→τ).level
        -- ≥ σ_inner.level + 1 and G(f) < i, we have σ_inner.level < i.
        have hNotIter : f.isIterHead = false := by
          cases h : f.isIterHead <;> simp_all
        -- f : GodelTTerm S n (σ✝.arrow τ✝), so we need σ✝.level < i.
        -- G(f) ≥ (σ✝.arrow τ✝).level ≥ σ✝.level + 1, giving σ✝.level < i.
        have hfGLevel := f.G_ge_level
        simp only [GodelTType.level] at hfGLevel
        rw [GodelTTerm.bracketLevel_app_high f a i (by omega) hNotIter]
        exact ihf hGf

/-- Beckmann-Weiermann for the binary-tree extension:
`treeIter σ leaf a b ≫ a`. -/
theorem GodelTTerm.majorizes_redTreeIter_leaf
    {S : Set GodelTBase} {n : Nat}
    (hT : GodelTBase.tree ∈ S) (σ : GodelTType S)
    (a : GodelTTerm S n σ)
    (b : GodelTTerm S n (.arrow σ (.arrow σ σ))) :
    GodelTTerm.majorizes
      (.app (.app (.app (.treeIter (n := n) hT σ)
        (.leaf hT)) a) b) a := by
  have hhead'NotIter :
      (GodelTTerm.app (GodelTTerm.treeIter (S := S) (n := n) hT σ)
        (GodelTTerm.leaf hT)).isIterHead = false := rfl
  have hheadNotIter :
      (GodelTTerm.app (GodelTTerm.app (GodelTTerm.treeIter
        (S := S) (n := n) hT σ) (GodelTTerm.leaf hT))
        a).isIterHead = false := rfl
  have hhead'_ge_one :
      1 ≤ (GodelTTerm.app (GodelTTerm.treeIter
        (S := S) (n := n) hT σ)
        (GodelTTerm.leaf hT)).bracketLevel 0 := by
    rw [GodelTTerm.bracketLevel_app_treeIter_zero]
    rfl
  refine ⟨?_, ?_⟩
  · have hMid :
        a.bracketLevel 0 <
          (GodelTTerm.app (GodelTTerm.app (GodelTTerm.treeIter
            (S := S) (n := n) hT σ) (GodelTTerm.leaf hT))
            a).bracketLevel 0 := by
      apply GodelTTerm.bracketLevel_app_strict_arg _ _ 0
        (Nat.zero_le _) hhead'NotIter
      exact hhead'_ge_one
    have hOuter :
        (GodelTTerm.app (GodelTTerm.app (GodelTTerm.treeIter
          (S := S) (n := n) hT σ) (GodelTTerm.leaf hT))
          a).bracketLevel 0 ≤
          (GodelTTerm.app (GodelTTerm.app (GodelTTerm.app
            (GodelTTerm.treeIter (S := S) (n := n) hT σ)
            (GodelTTerm.leaf hT)) a) b).bracketLevel 0 :=
      ((GodelTTerm.bracketLevel_app_ge_arg _ b 0
        (Nat.zero_le _) hheadNotIter).2)
    omega
  · intro i hi
    have hMid :
        a.bracketLevel i ≤
          (GodelTTerm.app (GodelTTerm.app (GodelTTerm.treeIter
            (S := S) (n := n) hT σ) (GodelTTerm.leaf hT))
            a).bracketLevel i :=
      ((GodelTTerm.bracketLevel_app_ge_arg _ a i hi
        hhead'NotIter).1)
    rcases Nat.lt_or_ge (σ.level + 1) i with hσ | hσ
    · have hσb :
          (GodelTType.arrow σ (.arrow σ σ)).level < i := by
        change max (σ.level + 1) (max (σ.level + 1) σ.level) < i
        omega
      exact GodelTTerm.bracketLevel_app_high_ge _ b i hσb
        hheadNotIter hMid
    · have hσb :
          i ≤ (GodelTType.arrow σ (.arrow σ σ)).level := by
        change i ≤ max (σ.level + 1) (max (σ.level + 1) σ.level)
        omega
      have hOuter :
          (GodelTTerm.app (GodelTTerm.app (GodelTTerm.treeIter
            (S := S) (n := n) hT σ) (GodelTTerm.leaf hT))
            a).bracketLevel i ≤
            (GodelTTerm.app (GodelTTerm.app (GodelTTerm.app
              (GodelTTerm.treeIter (S := S) (n := n) hT σ)
              (GodelTTerm.leaf hT)) a) b).bracketLevel i :=
        ((GodelTTerm.bracketLevel_app_ge_arg _ b i hσb
          hheadNotIter).2)
      omega

/-- Term-size strict-positivity helper. -/
theorem GodelTTerm.lh_pos {S : Set GodelTBase} {n : Nat}
    {σ : GodelTType S} (t : GodelTTerm S n σ) : 0 < t.lh := by
  cases t <;> simp [GodelTTerm.lh]

/-- `app`-formula for `lh`. -/
@[simp] theorem GodelTTerm.lh_app
    {S : Set GodelTBase} {n : Nat} {σ τ : GodelTType S}
    (f : GodelTTerm S n (.arrow σ τ))
    (a : GodelTTerm S n σ) :
    (GodelTTerm.app f a).lh = f.lh + a.lh + 1 := by
  simp [GodelTTerm.lh]

/-- A sub-application's left child is strictly smaller. -/
theorem GodelTTerm.lh_app_lt_left
    {S : Set GodelTBase} {n : Nat} {σ τ : GodelTType S}
    (f : GodelTTerm S n (.arrow σ τ))
    (a : GodelTTerm S n σ) :
    f.lh < (GodelTTerm.app f a).lh := by
  have := a.lh_pos; simp; omega

/-- A sub-application's right child is strictly smaller. -/
theorem GodelTTerm.lh_app_lt_right
    {S : Set GodelTBase} {n : Nat} {σ τ : GodelTType S}
    (f : GodelTTerm S n (.arrow σ τ))
    (a : GodelTTerm S n σ) :
    a.lh < (GodelTTerm.app f a).lh := by
  have := f.lh_pos; simp; omega

-- Combined induction: for all k, the following two statements hold.
-- (A) All N→N terms of lh = k have bracketLevel 0 ≥ 1.
-- (B) For any arrow-typed f of lh = k:
--     [f]_0 ≥ 1, OR σ (f's argument type) equals N→N.
-- Mutually: (A) uses (B), and (B) uses (A).
private theorem GodelTTerm.bracketLevel_zero_pos_combined
    {S : Set GodelTBase} {hN : GodelTBase.nat ∈ S} {n : Nat}
    (k : Nat) :
    (∀ (t : GodelTTerm S n
        (.arrow (.base .nat hN) (.base .nat hN))),
      t.lh = k → 1 ≤ t.bracketLevel 0) ∧
    (∀ {σ τ : GodelTType S}
      (f : GodelTTerm S n (.arrow σ τ)),
      f.lh = k →
      (1 ≤ f.bracketLevel 0) ∨
      (σ = .arrow (.base .nat hN) (.base .nat hN))) := by
  induction k using Nat.strong_induction_on with
  | _ k IH =>
    have IHA : ∀ m < k,
        ∀ (t : GodelTTerm S n
            (.arrow (.base .nat hN) (.base .nat hN))),
          t.lh = m → 1 ≤ t.bracketLevel 0 :=
      fun m hm => (IH m hm).1
    have IHB : ∀ m < k,
        ∀ {σ τ : GodelTType S}
          (f : GodelTTerm S n (.arrow σ τ)),
          f.lh = m →
          (1 ≤ f.bracketLevel 0) ∨
          (σ = .arrow (.base .nat hN) (.base .nat hN)) :=
      fun m hm => (IH m hm).2
    constructor
    · -- Part (A): t : N→N with t.lh = k.
      intro t htk
      cases t with
      | succ _ => rfl
      | pred _ => rfl
      | app f a =>
          have hflt : f.lh < k := by
            rw [← htk]; exact GodelTTerm.lh_app_lt_left f a
          have halt : a.lh < k := by
            rw [← htk]; exact GodelTTerm.lh_app_lt_right f a
          -- f : σ → (N→N), a : σ.
          -- f.isIterHead = false (type rules out bare iter/treeIter).
          have hfNotIter :
              f.isIterHead = false := by cases f <;> rfl
          rw [GodelTTerm.bracketLevel_app_eq f a 0
            (Nat.zero_le _) hfNotIter]
          have hp :
              1 ≤ 2 ^ (GodelTTerm.app f a).bracketLevel 1 :=
            Nat.one_le_iff_ne_zero.mpr (by positivity)
          -- IHB on f : σ → (N→N): [f]_0 ≥ 1 or σ = N→N.
          rcases IHB f.lh hflt f rfl with hf1 | hσNN
          · -- [f]_0 ≥ 1.  Sum ≥ 1.
            calc (1 : Nat)
                ≤ f.bracketLevel 0 := hf1
              _ ≤ f.bracketLevel 0 + a.bracketLevel 0 := by omega
              _ ≤ 2 ^ _ * (f.bracketLevel 0 + a.bracketLevel 0) :=
                Nat.le_mul_of_pos_left _ hp
          · -- σ = N→N, so a : N→N.  IHA on a.
            subst hσNN
            have haNN : 1 ≤ a.bracketLevel 0 :=
              IHA a.lh halt a rfl
            calc (1 : Nat)
                ≤ a.bracketLevel 0 := haNN
              _ ≤ f.bracketLevel 0 + a.bracketLevel 0 := by omega
              _ ≤ 2 ^ _ * (f.bracketLevel 0 + a.bracketLevel 0) :=
                Nat.le_mul_of_pos_left _ hp
    · -- Part (B): f : σ → τ with f.lh = k.
      intro σ τ f hfk
      cases f with
      | succ _ =>
          exact Or.inl (by rfl)
      | pred _ =>
          exact Or.inl (by rfl)
      | K _ _ =>
          exact Or.inl (by
            simp [GodelTTerm.bracketLevel_K, GodelTType.level])
      | S_comb _ _ _ =>
          exact Or.inl (by
            simp [GodelTTerm.bracketLevel_S_comb, GodelTType.level])
      | disc _ =>
          exact Or.inl (by rfl)
      | iter _ =>
          -- f = .iter _. bracketLevel 0 = 1 (level ≥ 2 ≥ 0).
          exact Or.inl (by
            simp [GodelTTerm.bracketLevel_iter, GodelTType.level])
      | node _ =>
          exact Or.inl (by
            simp [GodelTTerm.bracketLevel_node, GodelTType.level])
      | treeIter _ _ =>
          exact Or.inl (by
            simp [GodelTTerm.bracketLevel_treeIter, GodelTType.level])
      | app f' g =>
          -- f = .app f' g : σ → τ.
          have hf'lt : f'.lh < k := by
            rw [← hfk]; exact GodelTTerm.lh_app_lt_left f' g
          have hglt : g.lh < k := by
            rw [← hfk]; exact GodelTTerm.lh_app_lt_right f' g
          by_cases hf'iter : f'.isIterHead = true
          · cases f' with
            | iter _ =>
                -- f = .app (.iter _) g. σ of f equals N→N by type.
                exact Or.inr rfl
            | treeIter hT σ' =>
                -- f = .app (.treeIter hT σ') g : σ → τ, g : BT.
                -- Goal: [f]_0 ≥ 1, i.e. [g]_0 ≥ 1, by
                -- bracketLevel_app_treeIter_zero.
                refine Or.inl ?_
                rw [GodelTTerm.bracketLevel_app_treeIter_zero]
                -- All BT terms of lh < k have bracketLevel 0 ≥ 1.
                -- Proved by strong induction on lh within this case,
                -- using IHB from the outer induction.
                suffices h : ∀ (j : Nat) (q : GodelTTerm S n
                    (.base .tree hT)),
                    q.lh < k → q.lh = j → 1 ≤ q.bracketLevel 0 from
                  h g.lh g hglt rfl
                intro j
                induction j using Nat.strong_induction_on with
                | _ j IHg =>
                intro q hqk hjq
                cases q with
                | leaf _ =>
                    simp [GodelTTerm.bracketLevel_leaf, GodelTType.level]
                | app fg ag =>
                    have hfglt : fg.lh < k :=
                      Nat.lt_trans (GodelTTerm.lh_app_lt_left fg ag) hqk
                    have hfgNotIter :
                        fg.isIterHead = false := by cases fg; all_goals rfl
                    rcases IHB fg.lh hfglt fg rfl with hfg1 | hσ'NN
                    · -- [fg]_0 ≥ 1.
                      calc (1 : Nat)
                          ≤ fg.bracketLevel 0 := hfg1
                        _ ≤ (GodelTTerm.app fg ag).bracketLevel 0 :=
                          (GodelTTerm.bracketLevel_app_ge_arg fg ag 0
                            (Nat.zero_le _) hfgNotIter).2
                    · -- σ' = N→N, so ag : N→N.  IHA on ag.
                      subst hσ'NN
                      have haglt : ag.lh < k :=
                        Nat.lt_trans (GodelTTerm.lh_app_lt_right fg ag) hqk
                      have hag1 : 1 ≤ ag.bracketLevel 0 :=
                        IHA ag.lh haglt ag rfl
                      calc (1 : Nat)
                          ≤ ag.bracketLevel 0 := hag1
                        _ ≤ (GodelTTerm.app fg ag).bracketLevel 0 :=
                          (GodelTTerm.bracketLevel_app_ge_arg fg ag 0
                            (Nat.zero_le _) hfgNotIter).1
            | _ => exact absurd hf'iter (by simp [GodelTTerm.isIterHead])
          · -- f'.isIterHead = false.
            have hf'NI : f'.isIterHead = false := by
              simp only [Bool.eq_false_iff]; exact hf'iter
            rcases IHB f'.lh hf'lt f' rfl with hf'1 | hσ'NN
            · -- [f']_0 ≥ 1.  bracketLevel_app_ge_arg gives [f]_0 ≥ 1.
              exact Or.inl (hf'1.trans
                (GodelTTerm.bracketLevel_app_ge_arg f' g 0
                  (Nat.zero_le _) hf'NI).2)
            · -- σ' = N→N, so g : N→N.  IHA gives [g]_0 ≥ 1.
              -- bracketLevel_app_ge_arg gives [f]_0 ≥ [g]_0 ≥ 1.
              subst hσ'NN
              have hg1 : 1 ≤ g.bracketLevel 0 :=
                IHA g.lh hglt g rfl
              exact Or.inl (hg1.trans
                (GodelTTerm.bracketLevel_app_ge_arg f' g 0
                  (Nat.zero_le _) hf'NI).1)

-- Theorem 1: positivity of bracketLevel 0 for terms of type N→N.
theorem GodelTTerm.bracketLevel_zero_pos_arrow_NN
    {S : Set GodelTBase} {hN : GodelTBase.nat ∈ S} {n : Nat}
    (t : GodelTTerm S n
        (.arrow (.base .nat hN) (.base .nat hN))) :
    1 ≤ t.bracketLevel 0 :=
  (GodelTTerm.bracketLevel_zero_pos_combined t.lh).1 t rfl

end GebLean
