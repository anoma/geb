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

/-- Non-strict bracket dominance: `t.dominates s` if at every
level `i ≤ σ.level`,
`s.bracketLevel i ≤ t.bracketLevel i`.

Mirrors the monotone-at-`i` clause of `majorizes`.  The range
restriction matches `majorizes`'s and reflects that bracket
values are not in general comparable above `σ.level` for
compound `.app` terms. -/
def GodelTTerm.dominates {S : Set GodelTBase} {n : Nat}
    {σ : GodelTType S} (t s : GodelTTerm S n σ) : Prop :=
  ∀ i, i ≤ σ.level → s.bracketLevel i ≤ t.bracketLevel i

theorem GodelTTerm.dominates_refl {S : Set GodelTBase}
    {n : Nat} {σ : GodelTType S} (t : GodelTTerm S n σ) :
    t.dominates t :=
  fun _ _ => Nat.le_refl _

theorem GodelTTerm.dominates_trans {S : Set GodelTBase}
    {n : Nat} {σ : GodelTType S}
    {t s u : GodelTTerm S n σ}
    (h₁ : t.dominates s) (h₂ : s.dominates u) :
    t.dominates u :=
  fun i hi => Nat.le_trans (h₂ i hi) (h₁ i hi)

theorem GodelTTerm.majorizes_imp_dominates {S : Set GodelTBase}
    {n : Nat} {σ : GodelTType S}
    {t s : GodelTTerm S n σ} (h : t.majorizes s) :
    t.dominates s := h.2

/-- Bracket dominance propagates through binary application:
if both heads are non-iter and both arguments are pointwise-
dominated within their type levels, the application is
pointwise-dominated within its type level. -/
theorem GodelTTerm.dominates_app {S : Set GodelTBase}
    {n : Nat} {σ τ : GodelTType S}
    (f f' : GodelTTerm S n (.arrow σ τ))
    (a a' : GodelTTerm S n σ)
    (hf : f.isIterHead = false) (hf' : f'.isIterHead = false)
    (hF : f'.dominates f) (hA : a'.dominates a) :
    (GodelTTerm.app f' a').dominates (GodelTTerm.app f a) := by
  set M := (GodelTType.arrow σ τ).level with hM_def
  have hM_ge_τ : τ.level ≤ M := by
    rw [hM_def]; change τ.level ≤ max (σ.level + 1) τ.level
    omega
  suffices h : ∀ k, ∀ i, k + i = M → i ≤ M →
      (GodelTTerm.app f a).bracketLevel i ≤
        (GodelTTerm.app f' a').bracketLevel i by
    intro i hi
    have hiM : i ≤ M := Nat.le_trans hi hM_ge_τ
    exact h (M - i) i (by omega) hiM
  intro k
  induction k with
  | zero =>
    intro i hi_sum hi_le
    obtain rfl : i = M := by omega
    have hiσ : σ.level < M := by
      rw [hM_def]; change σ.level < max (σ.level + 1) τ.level
      omega
    rw [GodelTTerm.bracketLevel_app_high f a M hiσ hf,
        GodelTTerm.bracketLevel_app_high f' a' M hiσ hf']
    exact hF M (Nat.le_refl _)
  | succ k ih =>
    intro i hi_sum hi_le
    rcases Nat.lt_or_ge σ.level i with hiσ | hiσ
    · rw [GodelTTerm.bracketLevel_app_high f a i hiσ hf,
          GodelTTerm.bracketLevel_app_high f' a' i hiσ hf']
      exact hF i hi_le
    · rw [GodelTTerm.bracketLevel_app_eq f a i hiσ hf,
          GodelTTerm.bracketLevel_app_eq f' a' i hiσ hf']
      have hSucc_le : i + 1 ≤ M := by omega
      have hStepInner :
          (GodelTTerm.app f a).bracketLevel (i + 1) ≤
            (GodelTTerm.app f' a').bracketLevel (i + 1) :=
        ih (i + 1) (by omega) hSucc_le
      have hPow :
          2 ^ (GodelTTerm.app f a).bracketLevel (i + 1) ≤
            2 ^ (GodelTTerm.app f' a').bracketLevel (i + 1) :=
        Nat.pow_le_pow_right (by decide) hStepInner
      have hF_at : f.bracketLevel i ≤ f'.bracketLevel i := by
        apply hF i
        show i ≤ (GodelTType.arrow σ τ).level
        rw [← hM_def]
        exact hi_le
      have hA_at : a.bracketLevel i ≤ a'.bracketLevel i :=
        hA i hiσ
      have hSum :
          f.bracketLevel i + a.bracketLevel i ≤
            f'.bracketLevel i + a'.bracketLevel i := by omega
      exact Nat.mul_le_mul hPow hSum

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

/-- Beckmann-Weiermann Lemma 16 (iter-zero case):
`iter 0 a b ≫ b`. -/
theorem GodelTTerm.majorizes_redIter_zero
    {S : Set GodelTBase} {n : Nat}
    (hN : GodelTBase.nat ∈ S)
    (a : GodelTTerm S n
      (.arrow (.base .nat hN) (.base .nat hN)))
    (b : GodelTTerm S n (.base .nat hN)) :
    GodelTTerm.majorizes
      (.app (.app (.app (.iter (n := n) hN)
        (.zero hN)) a) b) b := by
  -- Abbreviations for the nested sub-terms.
  -- T₀ = app .iter .zero : (N→N) → (N→N)
  -- T₁ = app T₀ a       : N → N
  -- T₂ = app T₁ b       : N
  set T₀ := GodelTTerm.app (GodelTTerm.iter (S := S) (n := n) hN)
    (GodelTTerm.zero hN) with hT₀_def
  set T₁ := GodelTTerm.app T₀ a with hT₁_def
  set T₂ := GodelTTerm.app T₁ b with hT₂_def
  have hT₀NotIter : T₀.isIterHead = false := rfl
  have hT₁NotIter : T₁.isIterHead = false := rfl
  -- [T₀]_0 = 0 (bracketLevel_app_iter_zero; zero has [·]_0 = 0).
  have hT₀_zero : T₀.bracketLevel 0 = 0 := by
    simp [hT₀_def, GodelTTerm.bracketLevel_app_iter_zero,
      GodelTTerm.bracketLevel_zero]
  -- [a]_0 ≥ 1 (positivity theorem).
  have ha_pos : 1 ≤ a.bracketLevel 0 :=
    GodelTTerm.bracketLevel_zero_pos_arrow_NN a
  -- [T₁]_0 ≥ 1.
  -- level(N→N) = 1, so bracketLevel_app_eq at i=0 applies:
  -- [T₁]_0 = 2^[T₁]_1 * ([T₀]_0 + [a]_0) = 2^... * [a]_0.
  have hNNlevel : (GodelTType.arrow (.base .nat hN)
      (.base .nat hN)).level = 1 := by
    simp [GodelTType.level]
  have hT₁_zero_eq :
      T₁.bracketLevel 0 =
        2 ^ T₁.bracketLevel 1 *
          (T₀.bracketLevel 0 + a.bracketLevel 0) :=
    GodelTTerm.bracketLevel_app_eq T₀ a 0
      (by rw [hNNlevel]; omega) hT₀NotIter
  have hT₁_pos : 1 ≤ T₁.bracketLevel 0 := by
    rw [hT₁_zero_eq, hT₀_zero]
    simp only [Nat.zero_add]
    exact Nat.le_trans ha_pos
      (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _))
  -- Now prove majorization.
  refine ⟨?_, ?_⟩
  · -- Strict: [b]_0 < [T₂]_0.
    -- bracketLevel_app_strict_arg: [T₁]_0 ≥ 1 gives [b]_0 < [T₂]_0.
    exact GodelTTerm.bracketLevel_app_strict_arg T₁ b 0
      (Nat.zero_le _) hT₁NotIter hT₁_pos
  · -- Monotone: ∀ i ≤ N.level = 0, [b]_i ≤ [T₂]_i.
    intro i hi
    -- N.level = 0, so i = 0.
    obtain rfl : i = 0 := Nat.le_zero.mp hi
    exact Nat.le_of_lt (GodelTTerm.bracketLevel_app_strict_arg T₁ b 0
      (Nat.zero_le _) hT₁NotIter hT₁_pos)

/-- Beckmann-Weiermann Lemma 16 (iter-succ case):
`iter (S t) a b ≫ a (iter t a b)`. -/
theorem GodelTTerm.majorizes_redIter_succ
    {S : Set GodelTBase} {n : Nat}
    (hN : GodelTBase.nat ∈ S)
    (t : GodelTTerm S n (.base .nat hN))
    (a : GodelTTerm S n
      (.arrow (.base .nat hN) (.base .nat hN)))
    (b : GodelTTerm S n (.base .nat hN)) :
    GodelTTerm.majorizes
      (.app (.app (.app (.iter (n := n) hN)
        (.app (.succ hN) t)) a) b)
      (.app a (.app (.app (.app (.iter hN) t) a) b)) := by
  -- LHS: T₀' = iter(succ t), T₁' = T₀' a, T₂' = T₁' b.
  -- RHS: Tinner₀ = iter t, Tinner₁ = Tinner₀ a,
  --      Tinner₂ = Tinner₁ b, RHS_term = a Tinner₂.
  set T₀' := GodelTTerm.app
    (GodelTTerm.iter (S := S) (n := n) hN)
    (.app (.succ hN) t) with hT₀'_def
  set T₁' := GodelTTerm.app T₀' a with hT₁'_def
  set T₂' := GodelTTerm.app T₁' b with hT₂'_def
  set Tinner₀ := GodelTTerm.app
    (GodelTTerm.iter (S := S) (n := n) hN)
    t with hTinner₀_def
  set Tinner₁ := GodelTTerm.app Tinner₀ a
    with hTinner₁_def
  set Tinner₂ := GodelTTerm.app Tinner₁ b
    with hTinner₂_def
  -- isIterHead flags.
  have hT₀'NI : T₀'.isIterHead = false := rfl
  have hT₁'NI : T₁'.isIterHead = false := rfl
  have hTinner₀NI : Tinner₀.isIterHead = false := rfl
  have hTinner₁NI : Tinner₁.isIterHead = false := rfl
  have haNI : a.isIterHead = false := by cases a <;> rfl
  -- Type level values.
  have hNlevel :
      (GodelTType.base GodelTBase.nat hN).level = 0 := rfl
  have hNNlevel :
      (GodelTType.arrow (.base .nat hN)
        (.base .nat hN)).level = 1 := by
    simp [GodelTType.level]
  -- Abbreviate bracketLevel values.
  set τ := t.bracketLevel 0 with hτ_def
  set α := a.bracketLevel 0 with hα_def
  set α₁ := a.bracketLevel 1 with hα₁_def
  set β := b.bracketLevel 0 with hβ_def
  -- succ t bracketLevel computations.
  have hSuccNI :
      (GodelTTerm.succ (n := n) (S := S) hN).isIterHead =
        false := rfl
  have hSt_bl1 :
      (.app (.succ hN) t : GodelTTerm S n _).bracketLevel
        1 = 0 := by
    rw [GodelTTerm.bracketLevel_app_high _ _ 1
      (by rw [hNlevel]; omega) hSuccNI]; rfl
  have hSt_bl0 :
      (.app (.succ hN) t : GodelTTerm S n _).bracketLevel
        0 = 1 + τ := by
    rw [GodelTTerm.bracketLevel_app_eq _ _ 0
      (by rw [hNlevel]) hSuccNI, hSt_bl1]
    simp [GodelTTerm.bracketLevel_succ_zero, ← hτ_def]
  -- T₀' bracketLevel values.
  have hT₀'_bl0 : T₀'.bracketLevel 0 = 1 + τ := by
    rw [hT₀'_def, GodelTTerm.bracketLevel_app_iter_zero,
      hSt_bl0]
  have hT₀'_bl1 : T₀'.bracketLevel 1 = 1 := by
    rw [hT₀'_def, GodelTTerm.bracketLevel_app_iter_one]
  have hT₀'_bl2 : T₀'.bracketLevel 2 = 1 + τ := by
    rw [hT₀'_def, GodelTTerm.bracketLevel_app_iter_two,
      hSt_bl0]
  -- T₁' bracketLevel values.
  -- [T₁']_2 = [T₀']_2 = 1+τ (pass-through, i=2 > 1).
  have hT₁'_bl2 : T₁'.bracketLevel 2 = 1 + τ := by
    rw [hT₁'_def,
      GodelTTerm.bracketLevel_app_high T₀' a 2
        (by rw [hNNlevel]; omega) hT₀'NI, hT₀'_bl2]
  -- [T₁']_1 = 2^(1+τ) * (1 + α₁).
  have hT₁'_bl1 :
      T₁'.bracketLevel 1 = 2 ^ (1 + τ) * (1 + α₁) := by
    rw [hT₁'_def,
      GodelTTerm.bracketLevel_app_eq T₀' a 1
        (by rw [hNNlevel]) hT₀'NI,
      show (GodelTTerm.app T₀' a).bracketLevel 2 =
          1 + τ from hT₁'_bl2,
      hT₀'_bl1]
  -- Set M = T₁'.bracketLevel 1.
  set M := T₁'.bracketLevel 1 with hM_def
  -- [T₁']_0 = 2^M * (1+τ+α).
  have hT₁'_bl0 :
      T₁'.bracketLevel 0 = 2 ^ M * (1 + τ + α) := by
    rw [hT₁'_def,
      GodelTTerm.bracketLevel_app_eq T₀' a 0
        (by rw [hNNlevel]; omega) hT₀'NI,
      show (GodelTTerm.app T₀' a).bracketLevel 1 = M
        from rfl,
      hT₀'_bl0]
  -- [T₂']_1 = M (pass-through, i=1 > 0).
  have hT₂'_bl1 : T₂'.bracketLevel 1 = M := by
    rw [hT₂'_def,
      GodelTTerm.bracketLevel_app_high T₁' b 1
        (by rw [hNlevel]; omega) hT₁'NI]
  -- [T₂']_0 = 2^M * (2^M*(1+τ+α) + β).
  have hT₂'_bl0 :
      T₂'.bracketLevel 0 =
        2 ^ M * (2 ^ M * (1 + τ + α) + β) := by
    rw [hT₂'_def,
      GodelTTerm.bracketLevel_app_eq T₁' b 0
        (by rw [hNlevel]) hT₁'NI,
      show (GodelTTerm.app T₁' b).bracketLevel 1 = M
        from hT₂'_bl1,
      hT₁'_bl0]
  -- Tinner₀ bracketLevel values.
  have hTi₀_bl0 : Tinner₀.bracketLevel 0 = τ := by
    rw [hTinner₀_def, GodelTTerm.bracketLevel_app_iter_zero]
  have hTi₀_bl1 : Tinner₀.bracketLevel 1 = 1 := by
    rw [hTinner₀_def, GodelTTerm.bracketLevel_app_iter_one]
  have hTi₀_bl2 : Tinner₀.bracketLevel 2 = τ := by
    rw [hTinner₀_def, GodelTTerm.bracketLevel_app_iter_two]
  -- Tinner₁ bracketLevel values.
  -- [Tinner₁]_2 = τ (pass-through, i=2 > 1).
  have hTi₁_bl2 : Tinner₁.bracketLevel 2 = τ := by
    rw [hTinner₁_def,
      GodelTTerm.bracketLevel_app_high Tinner₀ a 2
        (by rw [hNNlevel]; omega) hTinner₀NI, hTi₀_bl2]
  -- [Tinner₁]_1 = 2^τ * (1+α₁).
  have hTi₁_bl1 :
      Tinner₁.bracketLevel 1 = 2 ^ τ * (1 + α₁) := by
    rw [hTinner₁_def,
      GodelTTerm.bracketLevel_app_eq Tinner₀ a 1
        (by rw [hNNlevel]) hTinner₀NI,
      show Tinner₁.bracketLevel 2 = τ from hTi₁_bl2,
      hTi₀_bl1]
  -- Set Q = Tinner₁.bracketLevel 1.
  set Q := Tinner₁.bracketLevel 1 with hQ_def
  -- [Tinner₁]_0 = 2^Q * (τ+α).
  have hTi₁_bl0 :
      Tinner₁.bracketLevel 0 = 2 ^ Q * (τ + α) := by
    rw [hTinner₁_def,
      GodelTTerm.bracketLevel_app_eq Tinner₀ a 0
        (by rw [hNNlevel]; omega) hTinner₀NI,
      show (GodelTTerm.app Tinner₀ a).bracketLevel 1 = Q
        from rfl,
      hTi₀_bl0]
  -- [Tinner₂]_1 = Q (pass-through, i=1 > 0).
  have hTi₂_bl1 : Tinner₂.bracketLevel 1 = Q := by
    rw [hTinner₂_def,
      GodelTTerm.bracketLevel_app_high Tinner₁ b 1
        (by rw [hNlevel]; omega) hTinner₁NI]
  -- [Tinner₂]_0 = 2^Q * (2^Q*(τ+α) + β).
  have hTi₂_bl0 :
      Tinner₂.bracketLevel 0 =
        2 ^ Q * (2 ^ Q * (τ + α) + β) := by
    rw [hTinner₂_def,
      GodelTTerm.bracketLevel_app_eq Tinner₁ b 0
        (by rw [hNlevel]) hTinner₁NI,
      show (GodelTTerm.app Tinner₁ b).bracketLevel 1 = Q
        from hTi₂_bl1,
      hTi₁_bl0]
  -- RHS bracketLevel values.
  -- [RHS]_1 = α₁ (pass-through, domain N, i=1 > 0).
  have hRHS_bl1 :
      (GodelTTerm.app a Tinner₂).bracketLevel 1 = α₁ := by
    rw [GodelTTerm.bracketLevel_app_high a Tinner₂ 1
      (by rw [hNlevel]; omega) haNI]
  -- [RHS]_0 = 2^α₁ * (α + 2^Q*(2^Q*(τ+α)+β)).
  have hRHS_bl0 :
      (GodelTTerm.app a Tinner₂).bracketLevel 0 =
        2 ^ α₁ * (α + 2 ^ Q * (2 ^ Q * (τ + α) + β)) := by
    rw [GodelTTerm.bracketLevel_app_eq a Tinner₂ 0
      (by rw [hNlevel]) haNI,
      show (GodelTTerm.app a Tinner₂).bracketLevel 1 = α₁
        from hRHS_bl1,
      hTi₂_bl0]
  -- M = 2*Q (from the explicit expressions).
  have hMQ : M = 2 * Q := by
    rw [hT₁'_bl1, hTi₁_bl1,
      show 2 ^ (1 + τ) = 2 * 2 ^ τ from by
        rw [show 1 + τ = τ + 1 from by omega, Nat.pow_succ]; ring]
    ring
  -- 2^M = 2^Q * 2^Q.
  have h2M_sq : 2 ^ M = 2 ^ Q * 2 ^ Q := by
    rw [hMQ, show 2 * Q = Q + Q from by ring, Nat.pow_add]
  -- α₁ < M (from bracketLevel_app_strict_arg at level 1).
  have hα₁_lt_M : α₁ < M := by
    apply GodelTTerm.bracketLevel_app_strict_arg
      T₀' a 1 (by rw [hNNlevel]) hT₀'NI
    rw [hT₀'_bl1]
  -- M ≥ 2*(1+α₁) (since M = 2^(1+τ)*(1+α₁) ≥ 2*(1+α₁)).
  have hM_ge : 2 * (1 + α₁) ≤ M := by
    rw [hT₁'_bl1]
    have h2pow : 2 ≤ 2 ^ (1 + τ) :=
      calc (2 : Nat) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (1 + τ) :=
          Nat.pow_le_pow_right (by omega) (by omega)
    exact Nat.mul_le_mul_right (1 + α₁) h2pow
  -- Q ≥ 1+α₁ (since Q = 2^τ*(1+α₁) ≥ 1+α₁).
  have hQ_ge : 1 + α₁ ≤ Q := by
    rw [hTi₁_bl1]
    have h1pow : 1 ≤ 2 ^ τ := Nat.one_le_two_pow
    exact Nat.le_trans (by omega)
      (Nat.mul_le_mul_right (1 + α₁) h1pow)
  -- 2 * 2^α₁ ≤ 2^Q (from α₁+1 ≤ Q).
  have h2F_le_e : 2 * 2 ^ α₁ ≤ 2 ^ Q := by
    have hpow : 2 ^ (α₁ + 1) ≤ 2 ^ Q :=
      Nat.pow_le_pow_right (by omega)
        (show α₁ + 1 ≤ Q from by omega)
    rw [Nat.pow_succ, Nat.mul_comm] at hpow
    exact hpow
  -- 2 ≤ 2^Q (from Q ≥ 1).
  have he_ge2 : 2 ≤ 2 ^ Q :=
    calc (2 : Nat) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ Q :=
        Nat.pow_le_pow_right (by omega)
          (show 1 ≤ Q from by omega)
  -- α ≥ 1 (from bracketLevel_zero_pos_arrow_NN).
  have hα_pos : 1 ≤ α :=
    GodelTTerm.bracketLevel_zero_pos_arrow_NN a
  -- Main strict inequality:
  -- 2^α₁*(α + 2^Q*(2^Q*(τ+α)+β)) < 2^M*(2^M*(1+τ+α)+β).
  have hstrict :
      2 ^ α₁ * (α + 2 ^ Q * (2 ^ Q * (τ + α) + β)) <
        2 ^ M * (2 ^ M * (1 + τ + α) + β) := by
    rw [h2M_sq]
    -- e = 2^Q, F = 2^α₁.  Goal after substitution:
    -- F*(α + e*(e*(τ+α)+β)) < e^2*(e^2*(1+τ+α)+β).
    set e := 2 ^ Q with he_def
    set F := 2 ^ α₁ with hF_def
    -- F ≤ e (from 2F ≤ e).
    have hFe : F ≤ e := by omega
    -- 2*(F*e^2) ≤ e^3 (from 2F ≤ e, multiply by e^2).
    have h2Fee2 : 2 * (F * (e * e)) ≤ e * e * e :=
      calc 2 * (F * (e * e)) = 2 * F * (e * e) := by ring
        _ ≤ e * (e * e) :=
            Nat.mul_le_mul_right (e * e) h2F_le_e
        _ = e * e * e := by ring
    -- F*e ≤ e^2, F*e^2 ≤ e^3.
    have hFee : F * e ≤ e * e :=
      Nat.mul_le_mul_right e hFe
    -- 1 ≤ e^2 (from e ≥ 2).
    have hee_pos : 1 ≤ e * e := by
      calc (1 : Nat) = 1 * 1 := by ring
        _ ≤ e * e := by
          apply Nat.mul_le_mul <;> omega
    -- α < e^2*(1+τ+α): from 1 ≤ e^2.
    have hα_lt : α < e * e * (1 + τ + α) :=
      calc α < 1 + τ + α := by omega
        _ ≤ e * e * (1 + τ + α) :=
            Nat.le_mul_of_pos_left _ (by omega)
    -- F*α < F*e^2*(1+τ+α) (from hα_lt since F ≥ 1).
    have hF_pos : 0 < F := by positivity
    have hFα_lt : F * α < F * (e * e) * (1 + τ + α) := by
      have step1 : F * α < F * (e * e * (1 + τ + α)) :=
        Nat.mul_lt_mul_of_pos_left hα_lt hF_pos
      calc F * α < F * (e * e * (1 + τ + α)) := step1
        _ = F * (e * e) * (1 + τ + α) := by ring
    -- Main: show the expanded inequality.
    have hLHS : F * (α + e * (e * (τ + α) + β)) =
        F * α + F * (e * e) * (τ + α) + F * e * β := by ring
    have hRHS : e * e * (e * e * (1 + τ + α) + β) =
        e * e * e * e * (1 + τ + α) + e * e * β := by ring
    rw [hLHS, hRHS]
    -- F*α + F*e^2*(τ+α) + F*e*β
    -- < F*e^2*(1+τ+α) + F*e^2*(τ+α) + e^2*β    [using hFα_lt, hFee*β]
    -- = F*e^2*(1+2*(τ+α)) + e^2*β
    -- Since 2*(F*e^2) ≤ e^3:
    -- 2*(F*e^2*(1+2*(τ+α))) ≤ e^3*(1+2*(τ+α)) ≤ 2*e^4*(1+τ+α)
    -- (last: e^3*(1+2*(τ+α)) ≤ 2*e^4*(1+τ+α) from e*(1+τ+α) ≥ (1+2*(τ+α))/2).
    -- F*(e*e) ≤ e*(e*e) = e^3 (multiply F ≤ e by e^2).
    have hFee2 : F * (e * e) ≤ e * (e * e) :=
      Nat.mul_le_mul_right (e * e) hFe
    have hFee3 : F * (e * e) ≤ e * e * e := by
      calc F * (e * e) ≤ e * (e * e) := hFee2
        _ = e * e * e := by ring
    -- F*(e*e)*(1+τ+α) + F*(e*e)*(τ+α) = F*(e*e)*(1+2*(τ+α)).
    -- F*(e*e)*(1+2*(τ+α)) ≤ e³*(1+2*(τ+α)) [hFee3].
    -- e³*(1+2*(τ+α)) ≤ e⁴*(1+τ+α) [e≥2 gives e*(1+τ+α) ≥ 1+2*(τ+α)].
    have he_ge : 1 + 2 * (τ + α) ≤ e * (1 + τ + α) := by
      calc 1 + 2 * (τ + α)
          ≤ 2 * (1 + τ + α) := by omega
        _ ≤ e * (1 + τ + α) :=
            Nat.mul_le_mul_right _ he_ge2
    have hFee_sq_bound :
        F * (e * e) * (1 + τ + α) + F * (e * e) * (τ + α) ≤
          e * e * e * e * (1 + τ + α) := by
      have hring : F * (e * e) * (1 + τ + α) +
          F * (e * e) * (τ + α) =
          F * (e * e) * (1 + 2 * (τ + α)) := by ring
      rw [hring]
      calc F * (e * e) * (1 + 2 * (τ + α))
          ≤ e * e * e * (1 + 2 * (τ + α)) :=
              Nat.mul_le_mul_right _ hFee3
        _ ≤ e * e * e * (e * (1 + τ + α)) :=
              Nat.mul_le_mul_left _ he_ge
        _ = e * e * e * e * (1 + τ + α) := by ring
    have hFeB : F * e * β ≤ e * e * β :=
      Nat.mul_le_mul_right β hFee
    -- The main strict bound by combining pieces.
    -- Step 1a: use hFα_lt to get strict inequality on first pair.
    have hstep1a :
        F * α + F * (e * e) * (τ + α) <
          F * (e * e) * (1 + τ + α) + F * (e * e) * (τ + α) :=
      Nat.add_lt_add_right hFα_lt _
    -- Step 1b: add F*e*β ≤ e*e*β to the right end.
    have hstep1 :
        F * α + F * (e * e) * (τ + α) + F * e * β <
          F * (e * e) * (1 + τ + α) +
            F * (e * e) * (τ + α) + e * e * β :=
      Nat.add_lt_add_of_lt_of_le hstep1a hFeB
    calc F * α + F * (e * e) * (τ + α) + F * e * β
        < F * (e * e) * (1 + τ + α) +
            F * (e * e) * (τ + α) + e * e * β := hstep1
      _ ≤ e * e * e * e * (1 + τ + α) + e * e * β :=
            Nat.add_le_add_right hFee_sq_bound _
  -- Conclude majorization.
  refine ⟨?_, ?_⟩
  · -- Strict: [RHS]_0 < [T₂']_0.
    rw [hRHS_bl0, hT₂'_bl0]
    exact hstrict
  · -- Monotone: ∀ i ≤ 0, [RHS]_i ≤ [T₂']_i.
    intro i hi
    obtain rfl : i = 0 := Nat.le_zero.mp hi
    rw [hRHS_bl0, hT₂'_bl0]
    exact Nat.le_of_lt hstrict


/-- `bracketLevelAppGen` is monotone in both function-level and
argument-level inputs (pointwise). -/
theorem GodelTTerm.bracketLevelAppGen_mono
    (g i : Nat)
    (bf1 bf2 ba1 ba2 : Nat → Nat)
    (hf : ∀ j, bf1 j ≤ bf2 j)
    (ha : ∀ j, ba1 j ≤ ba2 j) :
    GodelTTerm.bracketLevelAppGen g i bf1 ba1 ≤
      GodelTTerm.bracketLevelAppGen g i bf2 ba2 := by
  unfold GodelTTerm.bracketLevelAppGen
  split_ifs with hi
  · induction (g + 1 - i) with
    | zero => exact hf (g + 1)
    | succ k ih =>
        simp only []
        apply Nat.mul_le_mul
        · exact Nat.pow_le_pow_right (by omega) ih
        · exact Nat.add_le_add (hf (g - k)) (ha (g - k))
  · exact hf i

/-- Monotonicity of `treeIter t` bracketLevel in `t.bracketLevel 0`. -/
private theorem GodelTTerm.bracketLevel_treeIter_arg_mono
    {S : Set GodelTBase} {n : Nat}
    (hT : GodelTBase.tree ∈ S) (σ : GodelTType S)
    (t1 t2 : GodelTTerm S n (.base .tree hT))
    (h : t1.bracketLevel 0 ≤ t2.bracketLevel 0)
    (j : Nat) :
    (GodelTTerm.app (GodelTTerm.treeIter hT σ) t1).bracketLevel j ≤
      (GodelTTerm.app (GodelTTerm.treeIter hT σ) t2).bracketLevel j := by
  rcases j with _ | _ | _ | k
  · simp only [GodelTTerm.bracketLevel_app_treeIter_zero]; exact h
  · rw [GodelTTerm.bracketLevel_app_treeIter_one,
        GodelTTerm.bracketLevel_app_treeIter_one]
  · rw [show (0 + 1 + 1 : Nat) = 2 from rfl,
        GodelTTerm.bracketLevel_app_treeIter_two,
        GodelTTerm.bracketLevel_app_treeIter_two]; exact h
  · rw [GodelTTerm.bracketLevel_app_treeIter_ge_three,
        GodelTTerm.bracketLevel_app_treeIter_ge_three]

/-- Monotonicity of `[app f a]_i` when `f` is replaced by a
pointwise-larger non-iter-head term (same `a`). -/
private theorem GodelTTerm.bracketLevel_app_mono_left
    {S : Set GodelTBase} {n : Nat}
    {σ τ : GodelTType S}
    (f1 f2 : GodelTTerm S n (.arrow σ τ))
    (a : GodelTTerm S n σ)
    (hf : ∀ j, f1.bracketLevel j ≤ f2.bracketLevel j)
    (hf1NI : f1.isIterHead = false)
    (hf2NI : f2.isIterHead = false)
    (i : Nat) (_ : i ≤ σ.level) :
    (GodelTTerm.app f1 a).bracketLevel i ≤
      (GodelTTerm.app f2 a).bracketLevel i := by
  rw [GodelTTerm.bracketLevel_app_of_not_iter f1 a i hf1NI,
      GodelTTerm.bracketLevel_app_of_not_iter f2 a i hf2NI]
  exact GodelTTerm.bracketLevelAppGen_mono σ.level i
    f1.bracketLevel f2.bracketLevel
    a.bracketLevel a.bracketLevel
    hf (fun _ => le_refl _)

/-- Monotonicity of `[app f a]_i` in both `f` and `a`. -/
private theorem GodelTTerm.bracketLevel_app_mono
    {S : Set GodelTBase} {n : Nat}
    {σ τ : GodelTType S}
    (f1 f2 : GodelTTerm S n (.arrow σ τ))
    (a1 a2 : GodelTTerm S n σ)
    (hf : ∀ j, f1.bracketLevel j ≤ f2.bracketLevel j)
    (ha : ∀ j, a1.bracketLevel j ≤ a2.bracketLevel j)
    (hf1NI : f1.isIterHead = false)
    (hf2NI : f2.isIterHead = false)
    (i : Nat) (_ : i ≤ σ.level) :
    (GodelTTerm.app f1 a1).bracketLevel i ≤
      (GodelTTerm.app f2 a2).bracketLevel i := by
  rw [GodelTTerm.bracketLevel_app_of_not_iter f1 a1 i hf1NI,
      GodelTTerm.bracketLevel_app_of_not_iter f2 a2 i hf2NI]
  exact GodelTTerm.bracketLevelAppGen_mono σ.level i
    f1.bracketLevel f2.bracketLevel
    a1.bracketLevel a2.bracketLevel
    hf ha

/-- Beckmann-Weiermann Lemma 16 (treeIter-node case):
`treeIter (node l r) a b ≫ b (treeIter l a b) (treeIter r a b)`
for base-typed σ (σ.level = 0). -/
theorem GodelTTerm.majorizes_redTreeIter_node
    {S : Set GodelTBase} {n : Nat}
    (hT : GodelTBase.tree ∈ S) (σ : GodelTType S)
    (hσ : σ.level = 0)
    (l r : GodelTTerm S n (.base .tree hT))
    (a : GodelTTerm S n σ)
    (b : GodelTTerm S n (.arrow σ (.arrow σ σ))) :
    GodelTTerm.majorizes
      (.app (.app (.app (.treeIter (n := n) hT σ)
        (.app (.app (.node hT) l) r)) a) b)
      (.app
        (.app b
          (.app (.app (.app (.treeIter hT σ) l) a) b))
        (.app (.app (.app (.treeIter hT σ) r) a) b)) := by
  have hTlevel : (GodelTType.base GodelTBase.tree hT).level = 0 := rfl
  -- NLR = node l r, and its bracketLevel.
  set NLR := GodelTTerm.app
    (GodelTTerm.app (GodelTTerm.node (S := S) (n := n) hT) l) r
    with hNLR_def
  have hNLRNI : NLR.isIterHead = false := rfl
  -- node : T→(T→T) has level 1.
  have hNlevel : (GodelTType.arrow (.base .tree hT)
      (.arrow (.base .tree hT) (.base .tree hT))).level = 1 := by
    simp [GodelTType.level]
  have hNodeNI : (GodelTTerm.node (S := S) (n := n) hT).isIterHead =
      false := rfl
  -- [app node l]_1 = 1 (pass-through, T.level=0 < 1).
  set nodeL := GodelTTerm.app (GodelTTerm.node (S := S) (n := n) hT) l
  have hNodel_bl1 : nodeL.bracketLevel 1 = 1 := by
    rw [show nodeL = GodelTTerm.app
        (GodelTTerm.node (S := S) (n := n) hT) l from rfl,
      GodelTTerm.bracketLevel_app_high _ _ 1
        (by rw [hTlevel]; omega) hNodeNI]
    simp [GodelTTerm.bracketLevel_node, hNlevel]
  set lBL := l.bracketLevel 0
  set rBL := r.bracketLevel 0
  have hNodel_bl0 : nodeL.bracketLevel 0 = 2 * (1 + lBL) := by
    rw [show nodeL = GodelTTerm.app
        (GodelTTerm.node (S := S) (n := n) hT) l from rfl,
      GodelTTerm.bracketLevel_app_eq _ _ 0
        (by rw [hTlevel]) hNodeNI, hNodel_bl1]
    simp only [GodelTTerm.bracketLevel_node, hNlevel]
    rfl
  have hNLR_bl1 : NLR.bracketLevel 1 = 1 := by
    rw [hNLR_def,
      GodelTTerm.bracketLevel_app_high _ _ 1
        (by rw [hTlevel]; omega) hNLRNI, hNodel_bl1]
  set N := NLR.bracketLevel 0
  have hNLR_bl0 : N = 2 * (2 * (1 + lBL) + rBL) := by
    have : N = NLR.bracketLevel 0 := rfl
    rw [this, hNLR_def,
      GodelTTerm.bracketLevel_app_eq _ _ 0
        (by rw [hTlevel]) hNLRNI,
      hNLR_bl1, hNodel_bl0]
    omega
  have hN_ge4 : 4 ≤ N := by rw [hNLR_bl0]; omega
  set TI_NLR := GodelTTerm.app
    (GodelTTerm.treeIter (S := S) (n := n) hT σ) NLR
  set TI_l := GodelTTerm.app
    (GodelTTerm.treeIter (S := S) (n := n) hT σ) l
  set TI_r := GodelTTerm.app
    (GodelTTerm.treeIter (S := S) (n := n) hT σ) r
  have hTI_NLRNI : TI_NLR.isIterHead = false := rfl
  have hTI_lNI : TI_l.isIterHead = false := rfl
  have hTI_rNI : TI_r.isIterHead = false := rfl
  have hTI_NLR_bl0 : TI_NLR.bracketLevel 0 = N :=
    GodelTTerm.bracketLevel_app_treeIter_zero hT σ NLR
  have hTI_NLR_bl1 : TI_NLR.bracketLevel 1 = 1 :=
    GodelTTerm.bracketLevel_app_treeIter_one hT σ NLR
  have hTI_NLR_bl2 : TI_NLR.bracketLevel 2 = N := by
    rw [GodelTTerm.bracketLevel_app_treeIter_two]
  have hTI_l_bl0 : TI_l.bracketLevel 0 = lBL :=
    GodelTTerm.bracketLevel_app_treeIter_zero hT σ l
  have hTI_r_bl0 : TI_r.bracketLevel 0 = rBL :=
    GodelTTerm.bracketLevel_app_treeIter_zero hT σ r
  have hN_ge_l : lBL ≤ N := by rw [hNLR_bl0]; omega
  have hN_ge_r : rBL ≤ N := by rw [hNLR_bl0]; omega
  have hTI_NLR_ge_l : ∀ j,
      TI_l.bracketLevel j ≤ TI_NLR.bracketLevel j :=
    GodelTTerm.bracketLevel_treeIter_arg_mono hT σ l NLR
      (by exact hN_ge_l)
  have hTI_NLR_ge_r : ∀ j,
      TI_r.bracketLevel j ≤ TI_NLR.bracketLevel j :=
    GodelTTerm.bracketLevel_treeIter_arg_mono hT σ r NLR
      (by exact hN_ge_r)
  -- TI_NLR_a = TI_NLR a, TI_l_a = TI_l a, TI_r_a = TI_r a.
  set TI_NLR_a := GodelTTerm.app TI_NLR a
  set TI_l_a := GodelTTerm.app TI_l a
  set TI_r_a := GodelTTerm.app TI_r a
  have hTI_NLR_aNI : TI_NLR_a.isIterHead = false := rfl
  have hTI_l_aNI : TI_l_a.isIterHead = false := rfl
  have hTI_r_aNI : TI_r_a.isIterHead = false := rfl
  have hTI_NLR_a_ge_l_all : ∀ j,
      TI_l_a.bracketLevel j ≤ TI_NLR_a.bracketLevel j := fun j => by
    rcases Nat.lt_or_ge σ.level j with hj | hj
    · rw [show TI_l_a = GodelTTerm.app TI_l a from rfl,
          GodelTTerm.bracketLevel_app_high TI_l a j hj hTI_lNI,
          show TI_NLR_a = GodelTTerm.app TI_NLR a from rfl,
          GodelTTerm.bracketLevel_app_high TI_NLR a j hj hTI_NLRNI]
      exact hTI_NLR_ge_l j
    · exact GodelTTerm.bracketLevel_app_mono_left
        TI_l TI_NLR a hTI_NLR_ge_l hTI_lNI hTI_NLRNI j hj
  have hTI_NLR_a_ge_r_all : ∀ j,
      TI_r_a.bracketLevel j ≤ TI_NLR_a.bracketLevel j := fun j => by
    rcases Nat.lt_or_ge σ.level j with hj | hj
    · rw [show TI_r_a = GodelTTerm.app TI_r a from rfl,
          GodelTTerm.bracketLevel_app_high TI_r a j hj hTI_rNI,
          show TI_NLR_a = GodelTTerm.app TI_NLR a from rfl,
          GodelTTerm.bracketLevel_app_high TI_NLR a j hj hTI_NLRNI]
      exact hTI_NLR_ge_r j
    · exact GodelTTerm.bracketLevel_app_mono_left
        TI_r TI_NLR a hTI_NLR_ge_r hTI_rNI hTI_NLRNI j hj
  set Rl := GodelTTerm.app TI_l_a b
  set Rr := GodelTTerm.app TI_r_a b
  set LHS := GodelTTerm.app TI_NLR_a b
  have hbNI : b.isIterHead = false := by cases b <;> rfl
  have hbTypeLevel :
      (GodelTType.arrow σ (.arrow σ σ)).level = σ.level + 1 := by
    simp [GodelTType.level]
  have hLHS_ge_Rl : ∀ j, j ≤ σ.level →
      Rl.bracketLevel j ≤ LHS.bracketLevel j := fun j hj =>
    GodelTTerm.bracketLevel_app_mono
      TI_l_a TI_NLR_a b b
      hTI_NLR_a_ge_l_all
      (fun _ => le_refl _) hTI_l_aNI hTI_NLR_aNI j
      (by rw [hbTypeLevel]; omega)
  have hLHS_ge_Rr : ∀ j, j ≤ σ.level →
      Rr.bracketLevel j ≤ LHS.bracketLevel j := fun j hj =>
    GodelTTerm.bracketLevel_app_mono
      TI_r_a TI_NLR_a b b
      hTI_NLR_a_ge_r_all
      (fun _ => le_refl _) hTI_r_aNI hTI_NLR_aNI j
      (by rw [hbTypeLevel]; omega)
  -- b_Rl = b Rl, RHS = b_Rl Rr.
  set b_Rl := GodelTTerm.app b Rl
  set RHS := GodelTTerm.app b_Rl Rr
  have hbRlNI : b_Rl.isIterHead = false := rfl
  -- TI_NLR_a_0 positivity.
  have hTI_NLR_a_bl0_eq :
      TI_NLR_a.bracketLevel 0 =
        2 ^ TI_NLR_a.bracketLevel 1 * (N + a.bracketLevel 0) := by
    rw [show TI_NLR_a = GodelTTerm.app TI_NLR a from rfl,
      GodelTTerm.bracketLevel_app_eq TI_NLR a 0
        (Nat.zero_le _) hTI_NLRNI,
      hTI_NLR_bl0]
  have hTI_NLR_a_pos : 1 ≤ TI_NLR_a.bracketLevel 0 := by
    rw [hTI_NLR_a_bl0_eq]
    calc (1 : Nat) ≤ N + a.bracketLevel 0 := by omega
      _ ≤ _ := Nat.le_mul_of_pos_left _
            (Nat.one_le_iff_ne_zero.mpr (by positivity))
  -- Abbreviate bracketLevel values.
  have hbTypeLevel1 :
      (GodelTType.arrow σ (.arrow σ σ)).level = 1 := by
    rw [hbTypeLevel, hσ]
  set β₁ := b.bracketLevel 1 with hβ₁_def
  set β₀ := b.bracketLevel 0 with hβ₀_def
  set α₀ := a.bracketLevel 0 with hα₀_def
  -- TI_l_a, TI_r_a bracketLevels (pass-through at i≥1 since σ.level=0).
  have hTI_l_a_bl1 : TI_l_a.bracketLevel 1 =
      TI_l.bracketLevel 1 := by
    rw [show TI_l_a = GodelTTerm.app TI_l a from rfl,
      GodelTTerm.bracketLevel_app_high TI_l a 1
        (by rw [hσ]; omega) hTI_lNI]
  have hTI_l_bl1_val : TI_l.bracketLevel 1 = 1 :=
    GodelTTerm.bracketLevel_app_treeIter_one hT σ l
  have hTI_l_a_bl1_val : TI_l_a.bracketLevel 1 = 1 := by
    rw [hTI_l_a_bl1, hTI_l_bl1_val]
  have hTI_l_a_bl2 : TI_l_a.bracketLevel 2 =
      TI_l.bracketLevel 2 := by
    rw [show TI_l_a = GodelTTerm.app TI_l a from rfl,
      GodelTTerm.bracketLevel_app_high TI_l a 2
        (by rw [hσ]; omega) hTI_lNI]
  have hTI_l_bl2_val : TI_l.bracketLevel 2 = lBL :=
    GodelTTerm.bracketLevel_app_treeIter_two hT σ l
  have hTI_l_a_bl2_val : TI_l_a.bracketLevel 2 = lBL := by
    rw [hTI_l_a_bl2, hTI_l_bl2_val]
  have hTI_l_a_bl0 :
      TI_l_a.bracketLevel 0 = 2 * (lBL + α₀) := by
    rw [show TI_l_a = GodelTTerm.app TI_l a from rfl,
      GodelTTerm.bracketLevel_app_eq TI_l a 0
        (by rw [hσ]) hTI_lNI,
      hTI_l_a_bl1_val, hTI_l_bl0]
    simp [← hα₀_def]
  have hTI_r_a_bl1 : TI_r_a.bracketLevel 1 =
      TI_r.bracketLevel 1 := by
    rw [show TI_r_a = GodelTTerm.app TI_r a from rfl,
      GodelTTerm.bracketLevel_app_high TI_r a 1
        (by rw [hσ]; omega) hTI_rNI]
  have hTI_r_bl1_val : TI_r.bracketLevel 1 = 1 :=
    GodelTTerm.bracketLevel_app_treeIter_one hT σ r
  have hTI_r_a_bl1_val : TI_r_a.bracketLevel 1 = 1 := by
    rw [hTI_r_a_bl1, hTI_r_bl1_val]
  have hTI_r_a_bl2 : TI_r_a.bracketLevel 2 =
      TI_r.bracketLevel 2 := by
    rw [show TI_r_a = GodelTTerm.app TI_r a from rfl,
      GodelTTerm.bracketLevel_app_high TI_r a 2
        (by rw [hσ]; omega) hTI_rNI]
  have hTI_r_bl2_val : TI_r.bracketLevel 2 = rBL :=
    GodelTTerm.bracketLevel_app_treeIter_two hT σ r
  have hTI_r_a_bl2_val : TI_r_a.bracketLevel 2 = rBL := by
    rw [hTI_r_a_bl2, hTI_r_bl2_val]
  have hTI_r_a_bl0 :
      TI_r_a.bracketLevel 0 = 2 * (rBL + α₀) := by
    rw [show TI_r_a = GodelTTerm.app TI_r a from rfl,
      GodelTTerm.bracketLevel_app_eq TI_r a 0
        (by rw [hσ]) hTI_rNI,
      hTI_r_a_bl1_val, hTI_r_bl0]
    simp [← hα₀_def]
  -- TI_NLR_a bracketLevels.
  have hTI_NLR_a_bl1_val : TI_NLR_a.bracketLevel 1 = 1 := by
    rw [show TI_NLR_a = GodelTTerm.app TI_NLR a from rfl,
      GodelTTerm.bracketLevel_app_high TI_NLR a 1
        (by rw [hσ]; omega) hTI_NLRNI,
      hTI_NLR_bl1]
  have hTI_NLR_a_bl2_val : TI_NLR_a.bracketLevel 2 = N := by
    rw [show TI_NLR_a = GodelTTerm.app TI_NLR a from rfl,
      GodelTTerm.bracketLevel_app_high TI_NLR a 2
        (by rw [hσ]; omega) hTI_NLRNI,
      hTI_NLR_bl2]
  have hTI_NLR_a_bl0_val :
      TI_NLR_a.bracketLevel 0 = 2 * (N + α₀) := by
    rw [hTI_NLR_a_bl0_eq, hTI_NLR_a_bl1_val]
    norm_num
  -- Rl bracketLevels (arg type b : σ→σ→σ, level 1).
  have hRlNI : Rl.isIterHead = false := rfl
  have hRl_bl2 : Rl.bracketLevel 2 = lBL := by
    rw [show Rl = GodelTTerm.app TI_l_a b from rfl,
      GodelTTerm.bracketLevel_app_high TI_l_a b 2
        (by rw [hbTypeLevel1]; omega) hTI_l_aNI,
      hTI_l_a_bl2_val]
  have hRl_bl1 :
      Rl.bracketLevel 1 = 2 ^ lBL * (1 + β₁) := by
    rw [show Rl = GodelTTerm.app TI_l_a b from rfl,
      GodelTTerm.bracketLevel_app_eq TI_l_a b 1
        (by rw [hbTypeLevel1]) hTI_l_aNI,
      show (GodelTTerm.app TI_l_a b).bracketLevel 2 = lBL
        from hRl_bl2,
      hTI_l_a_bl1_val, ← hβ₁_def]
  have hRl_bl0 :
      Rl.bracketLevel 0 =
        2 ^ (2 ^ lBL * (1 + β₁)) *
          (2 * (lBL + α₀) + β₀) := by
    rw [show Rl = GodelTTerm.app TI_l_a b from rfl,
      GodelTTerm.bracketLevel_app_eq TI_l_a b 0
        (by rw [hbTypeLevel1]; omega) hTI_l_aNI,
      show (GodelTTerm.app TI_l_a b).bracketLevel 1 =
          2 ^ lBL * (1 + β₁) from hRl_bl1,
      hTI_l_a_bl0, ← hβ₀_def]
  -- Rr bracketLevels (same structure as Rl).
  have hRrNI : Rr.isIterHead = false := rfl
  have hRr_bl2 : Rr.bracketLevel 2 = rBL := by
    rw [show Rr = GodelTTerm.app TI_r_a b from rfl,
      GodelTTerm.bracketLevel_app_high TI_r_a b 2
        (by rw [hbTypeLevel1]; omega) hTI_r_aNI,
      hTI_r_a_bl2_val]
  have hRr_bl1 :
      Rr.bracketLevel 1 = 2 ^ rBL * (1 + β₁) := by
    rw [show Rr = GodelTTerm.app TI_r_a b from rfl,
      GodelTTerm.bracketLevel_app_eq TI_r_a b 1
        (by rw [hbTypeLevel1]) hTI_r_aNI,
      show (GodelTTerm.app TI_r_a b).bracketLevel 2 = rBL
        from hRr_bl2,
      hTI_r_a_bl1_val, ← hβ₁_def]
  have hRr_bl0 :
      Rr.bracketLevel 0 =
        2 ^ (2 ^ rBL * (1 + β₁)) *
          (2 * (rBL + α₀) + β₀) := by
    rw [show Rr = GodelTTerm.app TI_r_a b from rfl,
      GodelTTerm.bracketLevel_app_eq TI_r_a b 0
        (by rw [hbTypeLevel1]; omega) hTI_r_aNI,
      show (GodelTTerm.app TI_r_a b).bracketLevel 1 =
          2 ^ rBL * (1 + β₁) from hRr_bl1,
      hTI_r_a_bl0, ← hβ₀_def]
  -- b_Rl bracketLevels (arg type Rl : σ, σ.level = 0).
  have hbRl_bl1 : b_Rl.bracketLevel 1 = β₁ := by
    rw [show b_Rl = GodelTTerm.app b Rl from rfl,
      GodelTTerm.bracketLevel_app_high b Rl 1
        (by rw [hσ]; omega) hbNI]
  have hbRl_bl0 :
      b_Rl.bracketLevel 0 =
        2 ^ β₁ * (β₀ + Rl.bracketLevel 0) := by
    rw [show b_Rl = GodelTTerm.app b Rl from rfl,
      GodelTTerm.bracketLevel_app_eq b Rl 0
        (by rw [hσ]) hbNI,
      show (GodelTTerm.app b Rl).bracketLevel 1 = β₁
        from hbRl_bl1, ← hβ₀_def]
  -- RHS bracketLevels (arg type Rr : σ, σ.level = 0).
  have hRHS_bl1 : RHS.bracketLevel 1 = β₁ := by
    rw [show RHS = GodelTTerm.app b_Rl Rr from rfl,
      GodelTTerm.bracketLevel_app_high b_Rl Rr 1
        (by rw [hσ]; omega) hbRlNI,
      hbRl_bl1]
  have hRHS_bl0 :
      RHS.bracketLevel 0 =
        2 ^ β₁ * (b_Rl.bracketLevel 0 + Rr.bracketLevel 0) := by
    rw [show RHS = GodelTTerm.app b_Rl Rr from rfl,
      GodelTTerm.bracketLevel_app_eq b_Rl Rr 0
        (by rw [hσ]) hbRlNI,
      show (GodelTTerm.app b_Rl Rr).bracketLevel 1 = β₁
        from hRHS_bl1]
  -- LHS bracketLevels.
  have hLHS_bl2 : LHS.bracketLevel 2 = N := by
    rw [show LHS = GodelTTerm.app TI_NLR_a b from rfl,
      GodelTTerm.bracketLevel_app_high TI_NLR_a b 2
        (by rw [hbTypeLevel1]; omega) hTI_NLR_aNI,
      hTI_NLR_a_bl2_val]
  have hLHS_bl1 :
      LHS.bracketLevel 1 = 2 ^ N * (1 + β₁) := by
    rw [show LHS = GodelTTerm.app TI_NLR_a b from rfl,
      GodelTTerm.bracketLevel_app_eq TI_NLR_a b 1
        (by rw [hbTypeLevel1]) hTI_NLR_aNI,
      show (GodelTTerm.app TI_NLR_a b).bracketLevel 2 = N
        from hLHS_bl2,
      hTI_NLR_a_bl1_val, ← hβ₁_def]
  have hLHS_bl0 :
      LHS.bracketLevel 0 =
        2 ^ (2 ^ N * (1 + β₁)) *
          (2 * (N + α₀) + β₀) := by
    rw [show LHS = GodelTTerm.app TI_NLR_a b from rfl,
      GodelTTerm.bracketLevel_app_eq TI_NLR_a b 0
        (by rw [hbTypeLevel1]; omega) hTI_NLR_aNI,
      show (GodelTTerm.app TI_NLR_a b).bracketLevel 1 =
          2 ^ N * (1 + β₁) from hLHS_bl1,
      hTI_NLR_a_bl0_val, ← hβ₀_def]
  -- Height comparison: LHS.bl 1 ≥ 16 * Rl.bl 1.
  -- N - lBL ≥ 4 (from N = 4+4lBL+2rBL ≥ lBL+4).
  have hN_ge_lBL4 : lBL + 4 ≤ N := by rw [hNLR_bl0]; omega
  have hN_ge_rBL4 : rBL + 4 ≤ N := by rw [hNLR_bl0]; omega
  -- Let H = 2^N*(1+β₁), Rl₁ = 2^lBL*(1+β₁), Rr₁ = 2^rBL*(1+β₁).
  set H := 2 ^ N * (1 + β₁) with hH_def
  set Rl₁ := 2 ^ lBL * (1 + β₁) with hRl₁_def
  set Rr₁ := 2 ^ rBL * (1 + β₁) with hRr₁_def
  -- 16*Rl₁ ≤ H (from 2^(N-lBL) ≥ 16).
  have hH_ge_16Rl1 : 16 * Rl₁ ≤ H := by
    rw [hH_def, hRl₁_def]
    calc 16 * (2 ^ lBL * (1 + β₁))
        = 2 ^ lBL * 16 * (1 + β₁) := by ring
      _ ≤ 2 ^ N * (1 + β₁) := by
          apply Nat.mul_le_mul_right
          calc 2 ^ lBL * 16 = 2 ^ lBL * 2 ^ 4 := by norm_num
            _ = 2 ^ (lBL + 4) := by rw [Nat.pow_add]
            _ ≤ 2 ^ N :=
                Nat.pow_le_pow_right (by omega) hN_ge_lBL4
  -- 16*Rr₁ ≤ H (from 2^(N-rBL) ≥ 16).
  have hH_ge_16Rr1 : 16 * Rr₁ ≤ H := by
    rw [hH_def, hRr₁_def]
    calc 16 * (2 ^ rBL * (1 + β₁))
        = 2 ^ rBL * 16 * (1 + β₁) := by ring
      _ ≤ 2 ^ N * (1 + β₁) := by
          apply Nat.mul_le_mul_right
          calc 2 ^ rBL * 16 = 2 ^ rBL * 2 ^ 4 := by norm_num
            _ = 2 ^ (rBL + 4) := by rw [Nat.pow_add]
            _ ≤ 2 ^ N :=
                Nat.pow_le_pow_right (by omega) hN_ge_rBL4
  -- β₁ < Rl₁ (since 2^lBL*(1+β₁) ≥ 1+β₁ > β₁).
  have hβ₁_lt_Rl1 : β₁ < Rl₁ := by
    have hge : 1 + β₁ ≤ Rl₁ := by
      rw [hRl₁_def]
      exact Nat.le_mul_of_pos_left _ (Nat.two_pow_pos lBL)
    omega
  -- β₁ < Rr₁.
  have hβ₁_lt_Rr1 : β₁ < Rr₁ := by
    have hge : 1 + β₁ ≤ Rr₁ := by
      rw [hRr₁_def]
      exact Nat.le_mul_of_pos_left _ (Nat.two_pow_pos rBL)
    omega
  -- 2β₁ + Rl₁ + 3 ≤ H (height bound for Rl branch).
  have hK1_lt_H : 2 * β₁ + Rl₁ + 3 ≤ H := by
    have h1 : 1 + β₁ ≤ Rl₁ := by
      rw [hRl₁_def]
      exact Nat.le_mul_of_pos_left _ (Nat.two_pow_pos lBL)
    omega
  -- β₁ + Rr₁ + 3 ≤ H (height bound for Rr branch).
  have hK2_lt_H : β₁ + Rr₁ + 3 ≤ H := by
    have h1 : 1 + β₁ ≤ Rr₁ := by
      rw [hRr₁_def]
      exact Nat.le_mul_of_pos_left _ (Nat.two_pow_pos rBL)
    omega
  -- P = 2*(N+α₀)+β₀, Pl ≤ P, Pr ≤ P.
  have hPl_le_P : 2 * (lBL + α₀) + β₀ ≤ 2 * (N + α₀) + β₀ := by
    have := hN_ge_l; omega
  have hPr_le_P : 2 * (rBL + α₀) + β₀ ≤ 2 * (N + α₀) + β₀ := by
    have := hN_ge_r; omega
  -- H ≥ 3 (from H ≥ 16*Rl₁ ≥ 16).
  have hH3 : 3 ≤ H := by
    have h1 : 1 + β₁ ≤ Rl₁ := by
      rw [hRl₁_def]
      exact Nat.le_mul_of_pos_left _ (Nat.two_pow_pos lBL)
    omega
  -- Tower bound: 2^(2β₁) + 2^(2β₁+Rl₁) + 2^(β₁+Rr₁) < 2^H.
  have hterm_bound :
      2 ^ (2 * β₁) + 2 ^ (2 * β₁ + Rl₁) +
        2 ^ (β₁ + Rr₁) < 2 ^ H := by
    have hA : 2 ^ (2 * β₁) ≤ 2 ^ (H - 3) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have hB : 2 ^ (2 * β₁ + Rl₁) ≤ 2 ^ (H - 3) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have hC : 2 ^ (β₁ + Rr₁) ≤ 2 ^ (H - 3) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have h3pow : 2 ^ (H - 3) * 3 < 2 ^ H := by
      have hpow : 2 ^ H = 2 ^ (H - 3) * 2 ^ 3 := by
        rw [← Nat.pow_add]; congr 1; omega
      rw [hpow]
      apply Nat.mul_lt_mul_of_pos_left _ (Nat.two_pow_pos _)
      norm_num
    calc 2 ^ (2 * β₁) + 2 ^ (2 * β₁ + Rl₁) + 2 ^ (β₁ + Rr₁)
        ≤ 2 ^ (H - 3) + 2 ^ (H - 3) + 2 ^ (H - 3) :=
            Nat.add_le_add (Nat.add_le_add hA hB) hC
      _ = 2 ^ (H - 3) * 3 := by ring
      _ < 2 ^ H := h3pow
  -- Prove strict: RHS.bl 0 < LHS.bl 0.
  have hStrict :
      RHS.bracketLevel 0 < LHS.bracketLevel 0 := by
    rw [hRHS_bl0, hbRl_bl0, hRl_bl0, hRr_bl0, hLHS_bl0]
    -- Now the goal is a pure Nat inequality.
    have hP_pos : 0 < 2 * (N + α₀) + β₀ := by omega
    have hβ₀_le_P : β₀ ≤ 2 * (N + α₀) + β₀ := by omega
    have hRHS_upper :
        2 ^ β₁ *
          (2 ^ β₁ * (β₀ + 2 ^ Rl₁ * (2 * (lBL + α₀) + β₀)) +
            2 ^ Rr₁ * (2 * (rBL + α₀) + β₀)) ≤
          (2 * (N + α₀) + β₀) *
            (2 ^ (2 * β₁) + 2 ^ (2 * β₁ + Rl₁) +
              2 ^ (β₁ + Rr₁)) := by
      have hPl : 2 * (lBL + α₀) + β₀ ≤ 2 * (N + α₀) + β₀ :=
        hPl_le_P
      have hPr : 2 * (rBL + α₀) + β₀ ≤ 2 * (N + α₀) + β₀ :=
        hPr_le_P
      have hpow2β₁ : 2 ^ (2 * β₁) = 2 ^ β₁ * 2 ^ β₁ := by
        rw [← Nat.pow_add]; congr 1; omega
      have hpowRl : 2 ^ (2 * β₁ + Rl₁) = 2 ^ β₁ * (2 ^ β₁ * 2 ^ Rl₁) := by
        rw [← Nat.pow_add, ← Nat.pow_add]; congr 1; omega
      have hpowRr : 2 ^ (β₁ + Rr₁) = 2 ^ β₁ * 2 ^ Rr₁ :=
        Nat.pow_add 2 β₁ Rr₁
      set P := 2 * (N + α₀) + β₀
      set Pl := 2 * (lBL + α₀) + β₀
      set Pr := 2 * (rBL + α₀) + β₀
      set B := 2 ^ β₁
      set Rl := 2 ^ Rl₁
      set Rr := 2 ^ Rr₁
      have hb1 : 1 ≤ B := Nat.one_le_two_pow
      have hRl1 : 1 ≤ Rl := Nat.one_le_two_pow
      have hRr1 : 1 ≤ Rr := Nat.one_le_two_pow
      have hPl' : Pl ≤ P := hPl_le_P
      have hPr' : Pr ≤ P := hPr_le_P
      have hβ₀P : β₀ ≤ P := hβ₀_le_P
      -- rw unfolds 2^(2β₁) = B*B, 2^(2β₁+Rl₁) = B*(B*Rl), 2^(β₁+Rr₁) = B*Rr
      rw [hpow2β₁, hpowRl, hpowRr]
      -- Goal: B*(B*(β₀+Rl*Pl)+Rr*Pr) ≤ P*(B*B+B*(B*Rl)+B*Rr)
      -- = B*(B*(β₀+Rl*Pl)+Rr*Pr) ≤ B*P*(B+B*Rl+Rr)
      -- Follows from: β₀ ≤ P, Pl ≤ P, Pr ≤ P, 1 ≤ Rl, 1 ≤ Rr
      calc B * (B * (β₀ + Rl * Pl) + Rr * Pr)
          = B * B * β₀ + B * B * Rl * Pl + B * Rr * Pr := by ring
        _ ≤ B * B * P + B * B * Rl * P + B * Rr * P :=
            Nat.add_le_add
              (Nat.add_le_add
                (Nat.mul_le_mul_left _ hβ₀P)
                (Nat.mul_le_mul_left _ hPl'))
              (Nat.mul_le_mul_left _ hPr')
        _ = P * (B * B + B * (B * Rl) + B * Rr) := by ring
    calc 2 ^ β₁ *
          (2 ^ β₁ * (β₀ + 2 ^ Rl₁ * (2 * (lBL + α₀) + β₀)) +
            2 ^ Rr₁ * (2 * (rBL + α₀) + β₀))
        ≤ (2 * (N + α₀) + β₀) *
            (2 ^ (2 * β₁) + 2 ^ (2 * β₁ + Rl₁) +
              2 ^ (β₁ + Rr₁)) := hRHS_upper
      _ < (2 * (N + α₀) + β₀) * 2 ^ H :=
            Nat.mul_lt_mul_of_pos_left hterm_bound hP_pos
      _ = 2 ^ H * (2 * (N + α₀) + β₀) := by ring
  refine ⟨?_, ?_⟩
  · exact hStrict
  · intro i hi
    obtain rfl : i = 0 := Nat.le_zero.mp (by rwa [hσ] at hi)
    exact Nat.le_of_lt hStrict

end GebLean
