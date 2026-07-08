import GebLean.Ramified.Soundness.CodeTm

/-!
# Ramified recurrence: code-level substitution

The code-level realization layer of the deterministic normalizer of the
simply-typed calculus `1λ(natAlgSig)` (Leivant III section 4.2): the numeric
image of single-variable substitution together with the numeric images of the
redex detectors of `GebLean/Ramified/Soundness/Normalization.lean`. `subCode j e`
is the numeric shadow of `Binding.instantiate₁`: it rewrites the Gödel code
`codeTm d` of a body into the code of the reduct `codeTm (instantiate₁ e d)`,
working purely on the `Nat.pair` numerals with `codeTm e` supplied as the
substituend code. The detectors `betaRankCode`, `hasIotaCode`, `normalCode` and
their supporting reads recompute the redex measures of `Normalization.lean` on
the Gödel code, each proved to agree with its term-level counterpart under
`codeTm` (the mirror theorems); their dispatch on the operation kind bit reads
the operation-node structure rather than the term's index data.

`shiftCode j` is the code-level image of the append-at-end weakening
`ren Thinning.weakAppend`: because `codeTm` records de Bruijn *levels* (the
variable index `x.1.val`, which is the position of the variable's binder counted
from the outermost context entry), a variable's code depends on the ambient
context length. Weakening the target context by one entry at the end therefore
increments the level of every variable whose binder lies at or beyond the
insertion point; `shiftCode j` performs exactly that increment on the code,
bumping every variable leaf of level at least `j` by one and leaving the
operation structure otherwise intact.

`subCode j e` dispatches on the code shape. A variable leaf `Nat.pair 0 i`
rewrites by the three-way comparison of its level `i` against the substituted
level `j`: below `j` it is unchanged, at `j` it becomes the substituend code
`e`, and above `j` it drops by one (the substituted variable's level is
vacated). An operation node `Nat.pair 1 (Nat.pair op pack)` recurses into its
child codes, keeping the substituted level `j` fixed throughout (the append-at-
end convention leaves the target level of the substituted variable unchanged
under every binder). The substituend code, by contrast, is weakened by
`shiftCode j` whenever the recursion crosses an abstraction node, mirroring the
term-level weakening that `Binding.instantiate₁` applies to `e` under a binder.

## Main definitions

* `OneLambda.shiftCode` — the code-level append-at-end weakening: increment every
  variable leaf of level at least `j` by one.
* `OneLambda.subCode` — the code-level single-variable substitution: rewrite a
  body code against a substituted level `j` and a substituend code `e`.
* `OneLambda.isLamCode`, `OneLambda.conHeadedCode`, `OneLambda.topBetaRankCode`,
  `OneLambda.iotaSpineCode`, `OneLambda.resultShapeCode`, `OneLambda.topIotaCode`,
  `OneLambda.betaRankCode`, `OneLambda.hasIotaCode`, `OneLambda.normalCode` — the
  code-level images of the term-level redex detectors of `Normalization.lean`
  (`isLam`, `conHeaded`, `topBetaRank`, `iotaSpine`, the result-sort gate,
  `topIota`, `betaRedexRank`, `hasIota`, `Normal`).

## Main statements

* `OneLambda.shiftCode_var`, `OneLambda.shiftCode_app`, `OneLambda.shiftCode_lam`,
  `OneLambda.shiftCode_const` — the node equations of `shiftCode`.
* `OneLambda.subCode_var`, `OneLambda.subCode_app`, `OneLambda.subCode_lam`,
  `OneLambda.subCode_const` — the node equations of `subCode`.
* `OneLambda.codeTm_ren_shift`, `OneLambda.codeTm_ren_weakAppend` — the fusion of
  the append-at-end weakening with the code-level shift: renaming along a
  single-insertion thinning shifts the term code at the insertion level.
* `OneLambda.codeTm_ren_of_levels_eq`, `OneLambda.codeTm_ren_weakAppend_nil` —
  the term code is invariant under position-preserving renamings.
* `OneLambda.shiftCode_shiftCode` — the degeneracy identity of the code-level
  shifts: `shiftCode (L + 1) ∘ shiftCode j = shiftCode j ∘ shiftCode L` for
  `j ≤ L`.
* `OneLambda.codeTm_sub` — the environment-generalized commutation of the
  code-level substitution with the kit substitution.
* `OneLambda.subCode_codeTm` — the mirror theorem: `subCode Γ.length (codeTm e)
  (codeTm d) = codeTm (Binding.instantiate₁ e d)`.
* `OneLambda.isLamCode_codeTm`, `OneLambda.conHeadedCode_codeTm`,
  `OneLambda.topBetaRankCode_codeTm`, `OneLambda.iotaSpineCode_codeTm`,
  `OneLambda.topIotaCode_codeTm`, `OneLambda.betaRankCode_codeTm`,
  `OneLambda.hasIotaCode_codeTm` — the detector mirrors: reading each detector off
  a term code agrees with the term-level detector on the term.
* `OneLambda.normalCode_codeTm` — the normal-form mirror: `normalCode (codeTm t) =
  true ↔ Normal t`.
* `OneLambda.codeTm_headForm` — the transport-free bridge between a term code's
  kind and operation-kind reads and the term-level `headTag`.
* `OneLambda.shapeCode_codeRType_zero_iff` — reading the shape off a type code
  detects the base sort `o`.

## Implementation notes

`shiftCode` and `subCode` are strong recursions on the code value, terminating by
the same pairing bounds that guard `ordCode` and `decodeWord`
(`GebLean/Ramified/Soundness/CodeTm.lean`): each child code sits strictly below
its node code through `Nat.unpair_left_le`/`Nat.unpair_right_le` and the strict
step `OneLambda.self_lt_pair_one` past the kind bit `1`. Both dispatch on the
operation kind bit `(Nat.unpair op).1` to recover the node's arity — `0` for the
binary application, `1` for the unary abstraction, and every other value for the
nullary constants — so the child codes are unpacked at fixed depths rather than
by walking the `List.foldr Nat.pair 0` terminator (which is indistinguishable
from a level-`0` variable code, since `Nat.pair 0 0 = 0`).

The substituend weakening under a binder reflects that `codeTm` is *not* stable
under `ren Thinning.weakAppend`: a substituend's own bound variables have levels
at or above the target context length, so a weakening that lengthens the target
context raises them. The single-step image of that weakening is `shiftCode j`
(the fusion `codeTm (ren Thinning.weakAppend t) = shiftCode Δ.length (codeTm t)`
identifies the two); `subCode` therefore applies `shiftCode j` to `e` at each
abstraction node it descends through.

## References

D. Leivant, "Ramified recurrence and computational complexity III: Higher
type recurrence and elementary complexity", Annals of Pure and Applied Logic 96
(1999) 209-229, DOI `10.1016/S0168-0072(98)00040-2`, section 4.2 (p. 223): the
operations and terms of the simply-typed calculus `1λ(A)`, and its
single-variable substitution. The code-level substitution `subCode` and the
code-level weakening `shiftCode` are a novel realization; the substitution
convention transcribes the append-at-end de Bruijn presentation of
`GebLean/Binding/Substitution.lean`.

## Tags

ramified recurrence, Gödel numbering, de Bruijn level, substitution, weakening,
well-founded recursion, term code, redex, redex rank, normal form, normalization
-/

namespace GebLean.Ramified

open GebLean.Binding

namespace OneLambda

/-- The code-level append-at-end weakening: increment every variable leaf of
level at least `j` by one, leaving the operation structure intact. The numeric
image of `ren Thinning.weakAppend` under `codeTm`, by strong recursion on the
code value: a variable node `Nat.pair 0 i` bumps its level when `j ≤ i`; an
operation node recurses into its child codes at the fixed depths given by the
operation kind bit `(Nat.unpair op).1` (`0` binary, `1` unary, else nullary),
keeping `j` unchanged since levels are counted from the outermost entry. Novel
realization. -/
def shiftCode (j : ℕ) (c : ℕ) : ℕ :=
  match h : (Nat.unpair c).1, (Nat.unpair (Nat.unpair (Nat.unpair c).2).1).1 with
  | 0, _ =>
      if (Nat.unpair c).2 < j then Nat.pair 0 (Nat.unpair c).2
      else Nat.pair 0 ((Nat.unpair c).2 + 1)
  | 1, 0 =>
      Nat.pair 1 (Nat.pair (Nat.unpair (Nat.unpair c).2).1
        (Nat.pair (shiftCode j (Nat.unpair (Nat.unpair (Nat.unpair c).2).2).1)
          (Nat.pair (shiftCode j (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair c).2).2).2).1)
            0)))
  | 1, 1 =>
      Nat.pair 1 (Nat.pair (Nat.unpair (Nat.unpair c).2).1
        (Nat.pair (shiftCode j (Nat.unpair (Nat.unpair (Nat.unpair c).2).2).1) 0))
  | _, _ => c
  termination_by c
  decreasing_by
    all_goals
      have key : (Nat.unpair c).2 < c := by
        conv_rhs => rw [← Nat.pair_unpair c, h]
        exact self_lt_pair_one _
      first
      | exact Nat.lt_of_le_of_lt
          (le_trans (Nat.unpair_left_le _) (Nat.unpair_right_le _)) key
      | exact Nat.lt_of_le_of_lt
          (le_trans (le_trans (Nat.unpair_left_le _) (Nat.unpair_right_le _))
            (Nat.unpair_right_le _)) key

/-- The node equation of `shiftCode` at a variable leaf `Nat.pair 0 i`: the level
`i` is bumped when it lies at or beyond the insertion level `j`. -/
theorem shiftCode_var (j i : ℕ) :
    shiftCode j (Nat.pair 0 i) =
      if i < j then Nat.pair 0 i else Nat.pair 0 (i + 1) := by
  rw [shiftCode]; split <;> simp_all [Nat.unpair_pair]

/-- The node equation of `shiftCode` at an application node (op kind bit `0`): the
weakening recurses into the two child codes at the fixed level `j`. -/
theorem shiftCode_app (j op c0 c1 : ℕ) (hop : (Nat.unpair op).1 = 0) :
    shiftCode j (Nat.pair 1 (Nat.pair op (Nat.pair c0 (Nat.pair c1 0))))
      = Nat.pair 1 (Nat.pair op
          (Nat.pair (shiftCode j c0) (Nat.pair (shiftCode j c1) 0))) := by
  rw [shiftCode]; split <;> simp_all [Nat.unpair_pair]

/-- The node equation of `shiftCode` at an abstraction node (op kind bit `1`): the
weakening recurses into the sole body child code at the fixed level `j`. -/
theorem shiftCode_lam (j op c0 : ℕ) (hop : (Nat.unpair op).1 = 1) :
    shiftCode j (Nat.pair 1 (Nat.pair op (Nat.pair c0 0)))
      = Nat.pair 1 (Nat.pair op (Nat.pair (shiftCode j c0) 0)) := by
  rw [shiftCode]; split <;> simp_all [Nat.unpair_pair]

/-- The node equation of `shiftCode` at a nullary constant node (op kind bit at
least `2`): the code is unchanged. -/
theorem shiftCode_const (j op pack : ℕ) (hop : 2 ≤ (Nat.unpair op).1) :
    shiftCode j (Nat.pair 1 (Nat.pair op pack)) = Nat.pair 1 (Nat.pair op pack) := by
  rw [shiftCode]; split <;> simp_all [Nat.unpair_pair]

/-- The node equation of `shiftCode` at an application node with an arbitrary
children pack: the recursion reads the two child codes at the fixed unpacking
depths and rebuilds the pack with the terminator `0`. The `shiftCode_app`
generalization consumed by the strong induction of `shiftCode_shiftCode`. -/
theorem shiftCode_app_pack (j op pack : ℕ) (hop : (Nat.unpair op).1 = 0) :
    shiftCode j (Nat.pair 1 (Nat.pair op pack))
      = Nat.pair 1 (Nat.pair op (Nat.pair (shiftCode j (Nat.unpair pack).1)
          (Nat.pair (shiftCode j (Nat.unpair (Nat.unpair pack).2).1) 0))) := by
  rw [shiftCode]; split <;> simp_all [Nat.unpair_pair]

/-- The node equation of `shiftCode` at an abstraction node with an arbitrary
children pack: the recursion reads the sole body child code at the fixed
unpacking depth and rebuilds the pack with the terminator `0`. The
`shiftCode_lam` generalization consumed by the strong induction of
`shiftCode_shiftCode`. -/
theorem shiftCode_lam_pack (j op pack : ℕ) (hop : (Nat.unpair op).1 = 1) :
    shiftCode j (Nat.pair 1 (Nat.pair op pack))
      = Nat.pair 1 (Nat.pair op (Nat.pair (shiftCode j (Nat.unpair pack).1) 0)) := by
  rw [shiftCode]; split <;> simp_all [Nat.unpair_pair]

/-- The dispatch unfolding of `shiftCode` at a code whose top tag is at least
`2`: no such code is a variable leaf or an operation node, so the code is
unchanged. -/
theorem shiftCode_pair_of_two_le (j tag p : ℕ) (htag : 2 ≤ tag) :
    shiftCode j (Nat.pair tag p) = Nat.pair tag p := by
  rw [shiftCode]; split <;> simp_all [Nat.unpair_pair]

/-- The unpacked form of `shiftCode_pair_of_two_le`: a code whose top tag is at
least `2` is unchanged by the shift. -/
theorem shiftCode_of_two_le (j : ℕ) {c : ℕ} (h : 2 ≤ (Nat.unpair c).1) :
    shiftCode j c = c := by
  conv_lhs => rw [← Nat.pair_unpair c]
  rw [shiftCode_pair_of_two_le _ _ _ h]
  exact Nat.pair_unpair c

/-- The degeneracy identity of the code-level shifts, the de Bruijn analogue of
the simplicial identity `σ_{L+1} ∘ σ_j = σ_j ∘ σ_L` for `j ≤ L`: inserting at
level `j` and then at level `L + 1` equals inserting at level `L` and then at
level `j`. By strong recursion on the code value through the node equations; at
a variable leaf the identity is the three-way position arithmetic. Consumed by
`codeTm_sub`'s binder case, reconciling the fixed-level substituend weakening
`shiftCode j` of `subCode_lam` with the ambient-level weakening that
`Binding.instantiate₁` applies under a binder. Novel realization. -/
theorem shiftCode_shiftCode {j L : ℕ} (hjL : j ≤ L) (c : ℕ) :
    shiftCode (L + 1) (shiftCode j c) = shiftCode j (shiftCode L c) := by
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    rcases Nat.lt_trichotomy (Nat.unpair c).1 1 with h1 | h1 | h1
    · -- variable leaf: three-way position arithmetic
      have h0 : (Nat.unpair c).1 = 0 := by omega
      have hc : c = Nat.pair 0 (Nat.unpair c).2 := by
        conv_lhs => rw [← Nat.pair_unpair c, h0]
      rw [hc, shiftCode_var, shiftCode_var]
      split_ifs <;> rw [shiftCode_var, shiftCode_var] <;> split_ifs <;>
        first
          | rfl
          | (exfalso; omega)
    · -- operation node: dispatch on the operation kind bit
      have hp : (Nat.unpair c).2 < c := by
        conv_rhs => rw [← Nat.pair_unpair c, h1]
        exact self_lt_pair_one _
      have hc : c = Nat.pair 1 (Nat.pair (Nat.unpair (Nat.unpair c).2).1
          (Nat.unpair (Nat.unpair c).2).2) := by
        conv_lhs => rw [← Nat.pair_unpair c, h1, ← Nat.pair_unpair (Nat.unpair c).2]
      rcases Nat.lt_trichotomy (Nat.unpair (Nat.unpair (Nat.unpair c).2).1).1 1
        with h2 | h2 | h2
      · -- application: recurse into the two children
        have h2' : (Nat.unpair (Nat.unpair (Nat.unpair c).2).1).1 = 0 := by omega
        have hc0 : (Nat.unpair (Nat.unpair (Nat.unpair c).2).2).1 < c :=
          Nat.lt_of_le_of_lt
            (le_trans (Nat.unpair_left_le _) (Nat.unpair_right_le _)) hp
        have hc1 : (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair c).2).2).2).1 < c :=
          Nat.lt_of_le_of_lt
            (le_trans (le_trans (Nat.unpair_left_le _) (Nat.unpair_right_le _))
              (Nat.unpair_right_le _)) hp
        conv_lhs => rw [hc, shiftCode_app_pack _ _ _ h2', shiftCode_app _ _ _ _ h2']
        conv_rhs => rw [hc, shiftCode_app_pack _ _ _ h2', shiftCode_app _ _ _ _ h2']
        rw [ih _ hc0, ih _ hc1]
      · -- abstraction: recurse into the sole body child
        have hc0 : (Nat.unpair (Nat.unpair (Nat.unpair c).2).2).1 < c :=
          Nat.lt_of_le_of_lt
            (le_trans (Nat.unpair_left_le _) (Nat.unpair_right_le _)) hp
        conv_lhs => rw [hc, shiftCode_lam_pack _ _ _ h2, shiftCode_lam _ _ _ h2]
        conv_rhs => rw [hc, shiftCode_lam_pack _ _ _ h2, shiftCode_lam _ _ _ h2]
        rw [ih _ hc0]
      · -- nullary constant: both shifts are the identity
        have h2' : 2 ≤ (Nat.unpair (Nat.unpair (Nat.unpair c).2).1).1 := by omega
        conv_lhs => rw [hc, shiftCode_const _ _ _ h2', shiftCode_const _ _ _ h2']
        conv_rhs => rw [hc, shiftCode_const _ _ _ h2', shiftCode_const _ _ _ h2']
    · -- top tag at least `2`: all four shifts are the identity
      have h1' : 2 ≤ (Nat.unpair c).1 := by omega
      rw [shiftCode_of_two_le j h1', shiftCode_of_two_le (L + 1) h1',
        shiftCode_of_two_le L h1', shiftCode_of_two_le j h1']

/-- The code-level single-variable substitution: rewrite a body code against a
substituted level `j` and a substituend code `e`, the numeric image of
`Binding.instantiate₁` under `codeTm`. By strong recursion on the code value: a
variable leaf `Nat.pair 0 i` rewrites by the three-way comparison of its level
`i` with `j` (below `j` unchanged, at `j` the substituend `e`, above `j` dropped
by one); an operation node recurses into its child codes at the fixed depths
given by the operation kind bit `(Nat.unpair op).1`, keeping `j` fixed. The
substituend `e` is weakened by `shiftCode j` at each abstraction node the
recursion descends through, mirroring the term-level weakening of `e` under a
binder. Novel realization. -/
def subCode (j e : ℕ) (c : ℕ) : ℕ :=
  match h : (Nat.unpair c).1, (Nat.unpair (Nat.unpair (Nat.unpair c).2).1).1 with
  | 0, _ =>
      if (Nat.unpair c).2 < j then Nat.pair 0 (Nat.unpair c).2
      else if (Nat.unpair c).2 = j then e
      else Nat.pair 0 ((Nat.unpair c).2 - 1)
  | 1, 0 =>
      Nat.pair 1 (Nat.pair (Nat.unpair (Nat.unpair c).2).1
        (Nat.pair (subCode j e (Nat.unpair (Nat.unpair (Nat.unpair c).2).2).1)
          (Nat.pair (subCode j e
            (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair c).2).2).2).1) 0)))
  | 1, 1 =>
      Nat.pair 1 (Nat.pair (Nat.unpair (Nat.unpair c).2).1
        (Nat.pair (subCode j (shiftCode j e) (Nat.unpair (Nat.unpair (Nat.unpair c).2).2).1)
          0))
  | _, _ => c
  termination_by c
  decreasing_by
    all_goals
      have key : (Nat.unpair c).2 < c := by
        conv_rhs => rw [← Nat.pair_unpair c, h]
        exact self_lt_pair_one _
      first
      | exact Nat.lt_of_le_of_lt
          (le_trans (Nat.unpair_left_le _) (Nat.unpair_right_le _)) key
      | exact Nat.lt_of_le_of_lt
          (le_trans (le_trans (Nat.unpair_left_le _) (Nat.unpair_right_le _))
            (Nat.unpair_right_le _)) key

/-- The node equation of `subCode` at a variable leaf `Nat.pair 0 i`: the
three-way comparison of the level `i` with the substituted level `j`. -/
theorem subCode_var (j e i : ℕ) :
    subCode j e (Nat.pair 0 i) =
      if i < j then Nat.pair 0 i else if i = j then e else Nat.pair 0 (i - 1) := by
  rw [subCode]; split <;> simp_all [Nat.unpair_pair]

/-- The node equation of `subCode` at an application node (op kind bit `0`): the
substitution recurses into the two child codes with the substituend `e` and level
`j` unchanged. -/
theorem subCode_app (j e op c0 c1 : ℕ) (hop : (Nat.unpair op).1 = 0) :
    subCode j e (Nat.pair 1 (Nat.pair op (Nat.pair c0 (Nat.pair c1 0))))
      = Nat.pair 1 (Nat.pair op
          (Nat.pair (subCode j e c0) (Nat.pair (subCode j e c1) 0))) := by
  rw [subCode]; split <;> simp_all [Nat.unpair_pair]

/-- The node equation of `subCode` at an abstraction node (op kind bit `1`): the
substitution recurses into the sole body child with the substituend weakened by
`shiftCode j` and the level `j` unchanged. -/
theorem subCode_lam (j e op c0 : ℕ) (hop : (Nat.unpair op).1 = 1) :
    subCode j e (Nat.pair 1 (Nat.pair op (Nat.pair c0 0)))
      = Nat.pair 1 (Nat.pair op (Nat.pair (subCode j (shiftCode j e) c0) 0)) := by
  rw [subCode]; split <;> simp_all [Nat.unpair_pair]

/-- The node equation of `subCode` at a nullary constant node (op kind bit at
least `2`): the code is unchanged. -/
theorem subCode_const (j e op pack : ℕ) (hop : 2 ≤ (Nat.unpair op).1) :
    subCode j e (Nat.pair 1 (Nat.pair op pack)) = Nat.pair 1 (Nat.pair op pack) := by
  rw [subCode]; split <;> simp_all [Nat.unpair_pair]

/-- The term code is invariant under renaming along a position-preserving
thinning: if `ρ` sends every variable to a variable at the same numeric
position — so the target is a same-length resorting of the context, in
practice the `Γ ++ [] = Γ` reassociation embeddings — the code, which records
positions and not sort proofs, is unchanged. The environment-generalized
induction of `tmOpMax_ren`, the position action threaded to the under-binder
thinnings by `Thinning.appendId_app_val`. Novel realization. -/
theorem codeTm_ren_of_levels_eq {Γ Δ : Binding.Ctx RType} {s : RType}
    (ρ : Binding.Thinning Γ Δ) (hlen : Δ.length = Γ.length)
    (hρ : ∀ {u : RType} (x : Binding.Var Γ u), (ρ.app x).1.val = x.1.val)
    (t : Binding.Tm (oneLambdaSig natAlgSig) Γ s) :
    codeTm (Binding.ren ρ t) = codeTm t := by
  suffices h : ∀ {y : Binding.Ctx RType × RType}
      (t : PolyFix (polyTranslate Binding.varOver (oneLambdaSig natAlgSig).polyEndo) y)
      {Δ : Binding.Ctx RType} (ρ : Binding.Thinning y.1 Δ),
      Δ.length = y.1.length →
      (∀ {u : RType} (x : Binding.Var y.1 u), (ρ.app x).1.val = x.1.val) →
      codeTm (Γ := Δ) (Binding.traverse (Binding.varKit _) (Binding.renEnv ρ) t)
        = codeTm (Γ := y.1) (s := y.2) t from h t ρ hlen hρ
  intro y t
  induction t with
  | mk y idx children ih =>
    intro Δ ρ hlen hρ
    cases idx with
    | inl a =>
      rw [show (PolyFix.mk y (Sum.inl a) children
            : Binding.Tm (oneLambdaSig natAlgSig) y.1 y.2)
            = Binding.Tm.var (Binding.leafVar a) from by
              obtain ⟨⟨Γ', i'⟩, rfl⟩ := a
              congr 1
              funext e
              exact e.elim]
      simp only [Binding.traverse_var, Binding.varKit, Binding.renEnv, codeTm_var]
      exact congrArg (Nat.pair 0) (hρ (Binding.leafVar a))
    | inr p =>
      obtain ⟨Γ', s'⟩ := y
      change { o : (oneLambdaSig natAlgSig).Op // (oneLambdaSig natAlgSig).result o = s' } at p
      revert children ih
      obtain ⟨o, rfl⟩ := p
      intro children ih
      rw [show (PolyFix.mk (Γ', (oneLambdaSig natAlgSig).result o) (Sum.inr ⟨o, rfl⟩) children
            : Binding.Tm (oneLambdaSig natAlgSig) Γ' ((oneLambdaSig natAlgSig).result o))
            = Binding.Tm.op (S := oneLambdaSig natAlgSig) o (fun j => children ⟨j⟩)
            from rfl]
      replace hlen : List.length Δ = List.length Γ' := hlen
      replace hρ : ∀ {u : RType} (x : Binding.Var Γ' u), (ρ.app x).1.val = x.1.val :=
        fun x => hρ x
      have hlen' : ∀ Ξc : Binding.Ctx RType, (Δ ++ Ξc).length = (Γ' ++ Ξc).length :=
        fun Ξc => by simp only [List.length_append, hlen]
      rw [Binding.traverse_op, codeTm_op, codeTm_op]
      refine congrArg (fun q => Nat.pair 1 (Nat.pair (codeOp o)
        (List.foldr Nat.pair 0 (List.ofFn q)))) (funext fun i => ?_)
      rw [Binding.underBinder_renEnv]
      refine ih ⟨i⟩ (Binding.Thinning.appendId ρ _) (hlen' _) (fun x => ?_)
      have hx := Binding.Thinning.appendId_app_val (L := 0) (d := 0) ρ (Nat.zero_le _)
        (by omega) (fun v => by rw [hρ v, if_neg (Nat.not_lt_zero _)]; omega) x
      simpa using hx

/-- The term code of a renaming along a single-insertion thinning is the code
shifted at the insertion level: if `ρ` inserts one entry at position
`L ≤ Γ.length` — its action on variable positions is the identity below `L`
and the successor at or above `L` — then `codeTm (ren ρ t) = shiftCode L
(codeTm t)`. The environment-generalized induction of `tmOpMax_ren`: the
binder case rewrites the under-binder environment to the parallel append
`Thinning.appendId ρ Ξ`, which inserts at the same position by
`Thinning.appendId_app_val`, and fires the `shiftCode` node equations through
the operation kind bits. Novel realization. -/
theorem codeTm_ren_shift {Γ Δ : Binding.Ctx RType} {s : RType} (L : ℕ)
    (ρ : Binding.Thinning Γ Δ) (hlen : Δ.length = Γ.length + 1) (hL : L ≤ Γ.length)
    (hρ : ∀ {u : RType} (x : Binding.Var Γ u),
      (ρ.app x).1.val = if x.1.val < L then x.1.val else x.1.val + 1)
    (t : Binding.Tm (oneLambdaSig natAlgSig) Γ s) :
    codeTm (Binding.ren ρ t) = shiftCode L (codeTm t) := by
  suffices h : ∀ {y : Binding.Ctx RType × RType}
      (t : PolyFix (polyTranslate Binding.varOver (oneLambdaSig natAlgSig).polyEndo) y)
      {Δ : Binding.Ctx RType} (ρ : Binding.Thinning y.1 Δ),
      Δ.length = y.1.length + 1 → L ≤ y.1.length →
      (∀ {u : RType} (x : Binding.Var y.1 u),
        (ρ.app x).1.val = if x.1.val < L then x.1.val else x.1.val + 1) →
      codeTm (Γ := Δ) (Binding.traverse (Binding.varKit _) (Binding.renEnv ρ) t)
        = shiftCode L (codeTm (Γ := y.1) (s := y.2) t) from h t ρ hlen hL hρ
  intro y t
  induction t with
  | mk y idx children ih =>
    intro Δ ρ hlen hL hρ
    cases idx with
    | inl a =>
      rw [show (PolyFix.mk y (Sum.inl a) children
            : Binding.Tm (oneLambdaSig natAlgSig) y.1 y.2)
            = Binding.Tm.var (Binding.leafVar a) from by
              obtain ⟨⟨Γ', i'⟩, rfl⟩ := a
              congr 1
              funext e
              exact e.elim]
      simp only [Binding.traverse_var, Binding.varKit, Binding.renEnv, codeTm_var]
      rw [hρ (Binding.leafVar a), shiftCode_var]
      split_ifs <;> rfl
    | inr p =>
      obtain ⟨Γ', s'⟩ := y
      change { o : (oneLambdaSig natAlgSig).Op // (oneLambdaSig natAlgSig).result o = s' } at p
      revert children ih
      obtain ⟨o, rfl⟩ := p
      intro children ih
      rw [show (PolyFix.mk (Γ', (oneLambdaSig natAlgSig).result o) (Sum.inr ⟨o, rfl⟩) children
            : Binding.Tm (oneLambdaSig natAlgSig) Γ' ((oneLambdaSig natAlgSig).result o))
            = Binding.Tm.op (S := oneLambdaSig natAlgSig) o (fun j => children ⟨j⟩)
            from rfl]
      replace hlen : List.length Δ = List.length Γ' + 1 := hlen
      replace hL : L ≤ List.length Γ' := hL
      replace hρ : ∀ {u : RType} (x : Binding.Var Γ' u),
          (ρ.app x).1.val = if x.1.val < L then x.1.val else x.1.val + 1 :=
        fun x => hρ x
      rw [Binding.traverse_op, codeTm_op, codeTm_op]
      simp only [Binding.underBinder_renEnv]
      have hlen' : ∀ Ξc : Binding.Ctx RType, (Δ ++ Ξc).length = (Γ' ++ Ξc).length + 1 :=
        fun Ξc => by simp only [List.length_append, hlen]; omega
      have hL' : ∀ Ξc : Binding.Ctx RType, L ≤ (Γ' ++ Ξc).length :=
        fun Ξc => by simp only [List.length_append]; omega
      have hact : ∀ (Ξc : Binding.Ctx RType) {u : RType} (x : Binding.Var (Γ' ++ Ξc) u),
          ((Binding.Thinning.appendId ρ Ξc).app x).1.val
            = if x.1.val < L then x.1.val else x.1.val + 1 :=
        fun Ξc {u} x => Binding.Thinning.appendId_app_val ρ hL hlen hρ x
      cases o with
      | app σa τa =>
          have h0 := ih ⟨(0 : Fin 2)⟩ (Binding.Thinning.appendId ρ _) (hlen' _) (hL' _)
            (hact _)
          have h1 := ih ⟨(1 : Fin 2)⟩ (Binding.Thinning.appendId ρ _) (hlen' _) (hL' _)
            (hact _)
          refine Eq.trans (congrArg (fun q => Nat.pair 1
              (Nat.pair (codeOp (OneLambdaOp.app σa τa)) q))
              (congrArg₂ Nat.pair h0 (congrArg₂ Nat.pair h1 rfl)))
            (shiftCode_app L (codeOp (OneLambdaOp.app σa τa)) _ _
              (by simp [codeOp, Nat.unpair_pair])).symm
      | lam σa τa =>
          have h0 := ih ⟨(0 : Fin 1)⟩ (Binding.Thinning.appendId ρ _) (hlen' _) (hL' _)
            (hact _)
          refine Eq.trans (congrArg (fun q => Nat.pair 1
              (Nat.pair (codeOp (OneLambdaOp.lam σa τa)) q))
              (congrArg₂ Nat.pair h0 rfl))
            (shiftCode_lam L (codeOp (OneLambdaOp.lam σa τa)) _
              (by simp [codeOp, Nat.unpair_pair])).symm
      | con b =>
          exact (shiftCode_const L (codeOp (OneLambdaOp.con b)) _
            (by simp [codeOp, Nat.unpair_pair])).symm
      | dstr i =>
          exact (shiftCode_const L (codeOp (OneLambdaOp.dstr i)) _
            (by simp [codeOp, Nat.unpair_pair])).symm
      | case =>
          exact (shiftCode_const L (codeOp OneLambdaOp.case) _
            (by simp [codeOp, Nat.unpair_pair])).symm

/-- The fusion of the append-at-end weakening with the code-level shift:
renaming along the singleton suffix embedding `Thinning.weakAppend` — the
weakening `Binding.instantiate₁` applies to its substituend under each binder —
shifts the term code at the ambient context length. The `codeTm_ren_shift`
instance at the suffix embedding, whose position action is the identity, with
every position of `Δ` below the insertion level `Δ.length`. -/
theorem codeTm_ren_weakAppend {Δ : Binding.Ctx RType} {b s : RType}
    (t : Binding.Tm (oneLambdaSig natAlgSig) Δ s) :
    codeTm (Binding.ren (Binding.Thinning.weakAppend (Ξ := [b])) t)
      = shiftCode Δ.length (codeTm t) :=
  codeTm_ren_shift Δ.length Binding.Thinning.weakAppend (by simp) le_rfl
    (fun x => by rw [Binding.Thinning.weakAppend_app_val, if_pos x.1.isLt]) t

/-- The append-at-end weakening by an empty suffix leaves the term code
unchanged: the `codeTm_ren_of_levels_eq` instance at the suffix embedding
`Thinning.weakAppend` with suffix `[]`, whose position action is the
identity. -/
theorem codeTm_ren_weakAppend_nil {Δ : Binding.Ctx RType} {s : RType}
    (t : Binding.Tm (oneLambdaSig natAlgSig) Δ s) :
    codeTm (Binding.ren (Binding.Thinning.weakAppend (Ξ := [])) t) = codeTm t :=
  codeTm_ren_of_levels_eq Binding.Thinning.weakAppend (by simp)
    (fun x => Binding.Thinning.weakAppend_app_val x) t

/-- The environment-generalized commutation of the code-level substitution with
the kit substitution: if every image of the environment `σ` carries the code
that `subCode j e` assigns to its source variable's code — with the source
context one entry longer than the target (invariant of the substituted entry),
the substituted level `j` at most the target length, and the substituend code
`e` shifted equally at the target length and at `j` — then substitution along
`σ` commutes with `subCode j e` on term codes. The induction skeleton of
`tmOpMax_sub_le`. The binder case re-establishes the pointwise hypothesis for
`Env.underBinder`: the fresh suffix variable maps to the vacated position by
`subCode_var`, and the old images weaken by `codeTm_ren_weakAppend`
(`codeTm_ren_weakAppend_nil` at the binder-free arguments), reconciled at the
substituted level through the shift invariant and the degeneracy identity
`shiftCode_shiftCode`. Novel realization. -/
theorem codeTm_sub (j : ℕ) {Γ Δ : Binding.Ctx RType} {s : RType}
    (σ : Binding.Env (Binding.Tm (oneLambdaSig natAlgSig)) Γ Δ) (e : ℕ)
    (hlen : Γ.length = Δ.length + 1) (hj : j ≤ Δ.length)
    (he : shiftCode Δ.length e = shiftCode j e)
    (hσ : ∀ (u : RType) (x : Binding.Var Γ u),
      codeTm (σ u x) = subCode j e (Nat.pair 0 x.1.val))
    (t : Binding.Tm (oneLambdaSig natAlgSig) Γ s) :
    codeTm (Binding.sub σ t) = subCode j e (codeTm t) := by
  suffices h : ∀ {y : Binding.Ctx RType × RType}
      (t : PolyFix (polyTranslate Binding.varOver (oneLambdaSig natAlgSig).polyEndo) y)
      {Δ : Binding.Ctx RType}
      (σ : Binding.Env (Binding.Tm (oneLambdaSig natAlgSig)) y.1 Δ) (e : ℕ),
      y.1.length = Δ.length + 1 → j ≤ Δ.length →
      shiftCode Δ.length e = shiftCode j e →
      (∀ (u : RType) (x : Binding.Var y.1 u),
        codeTm (σ u x) = subCode j e (Nat.pair 0 x.1.val)) →
      codeTm (Γ := Δ) (Binding.traverse (Binding.subKit _) σ t)
        = subCode j e (codeTm (Γ := y.1) (s := y.2) t) from h t σ e hlen hj he hσ
  intro y t
  induction t with
  | mk y idx children ih =>
    intro Δ σ e hlen hj he hσ
    cases idx with
    | inl a =>
      rw [show (PolyFix.mk y (Sum.inl a) children
            : Binding.Tm (oneLambdaSig natAlgSig) y.1 y.2)
            = Binding.Tm.var (Binding.leafVar a) from by
              obtain ⟨⟨Γ', i'⟩, rfl⟩ := a
              congr 1
              funext e'
              exact e'.elim]
      rw [Binding.traverse_var, codeTm_var]
      simp only [Binding.subKit, id]
      exact hσ y.2 (Binding.leafVar a)
    | inr p =>
      obtain ⟨Γ', s'⟩ := y
      change { o : (oneLambdaSig natAlgSig).Op // (oneLambdaSig natAlgSig).result o = s' } at p
      revert children ih
      obtain ⟨o, rfl⟩ := p
      intro children ih
      replace hlen : List.length Γ' = List.length Δ + 1 := hlen
      replace hσ : ∀ (u : RType) (x : Binding.Var Γ' u),
          codeTm (σ u x) = subCode j e (Nat.pair 0 x.1.val) := fun u x => hσ u x
      rw [show (PolyFix.mk (Γ', (oneLambdaSig natAlgSig).result o) (Sum.inr ⟨o, rfl⟩) children
            : Binding.Tm (oneLambdaSig natAlgSig) Γ' ((oneLambdaSig natAlgSig).result o))
            = Binding.Tm.op (S := oneLambdaSig natAlgSig) o (fun j' => children ⟨j'⟩)
            from rfl]
      rw [Binding.traverse_op, codeTm_op, codeTm_op]
      -- the pointwise hypothesis under a binder-free argument
      have hσnil : ∀ (u : RType) (x : Binding.Var (Γ' ++ ([] : Binding.Ctx RType)) u),
          codeTm (Binding.Env.underBinder (Binding.subKit (oneLambdaSig natAlgSig))
              (Ξ := ([] : Binding.Ctx RType)) σ u x)
            = subCode j e (Nat.pair 0 x.1.val) := by
        intro u x
        simp only [Binding.Env.underBinder, Binding.subKit]
        have hold : ∀ v : Binding.Var Γ' u,
            codeTm (Binding.ren (Binding.Thinning.weakAppend (Ξ := [])) (σ u v))
              = subCode j e (Nat.pair 0 v.1.val) :=
          fun v => (codeTm_ren_weakAppend_nil (σ u v)).trans (hσ u v)
        exact (Binding.Var.appendCases_natural codeTm _ Γ' _ x).trans
          (Binding.Var.appendCases_val _ Γ' (fun n => subCode j e (Nat.pair 0 n)) _
            hold (fun (w : Binding.Var ([] : Binding.Ctx RType) u) => w.1.elim0) x)
      -- the pointwise hypothesis under a single binder, at the shifted substituend
      have hσone : ∀ (b : RType) (u : RType) (x : Binding.Var (Γ' ++ [b]) u),
          codeTm (Binding.Env.underBinder (Binding.subKit (oneLambdaSig natAlgSig))
              (Ξ := [b]) σ u x)
            = subCode j (shiftCode j e) (Nat.pair 0 x.1.val) := by
        intro b u x
        simp only [Binding.Env.underBinder, Binding.subKit]
        have hold : ∀ v : Binding.Var Γ' u,
            codeTm (Binding.ren (Binding.Thinning.weakAppend (Ξ := [b])) (σ u v))
              = subCode j (shiftCode j e) (Nat.pair 0 v.1.val) := by
          intro v
          rw [codeTm_ren_weakAppend, hσ u v]
          have hv : v.1.val < Δ.length + 1 := hlen ▸ v.1.isLt
          rcases Nat.lt_trichotomy v.1.val j with h1 | h1 | h1
          · rw [subCode_var, if_pos h1, subCode_var, if_pos h1, shiftCode_var,
              if_pos (by omega)]
          · rw [subCode_var, if_neg (by omega), if_pos h1, subCode_var,
              if_neg (by omega), if_pos h1]
            exact he
          · rw [subCode_var, if_neg (by omega), if_neg (by omega), subCode_var,
              if_neg (by omega), if_neg (by omega), shiftCode_var, if_pos (by omega)]
        have hnew : ∀ w : Binding.Var [b] u,
            codeTm (Binding.Tm.var (S := oneLambdaSig natAlgSig)
                (Binding.Var.appendRight Δ w))
              = subCode j (shiftCode j e) (Nat.pair 0 (Γ'.length + w.1.val)) := by
          intro w
          rw [codeTm_var, Binding.Var.appendRight_val, subCode_var,
            if_neg (by omega), if_neg (by omega)]
          exact congrArg (Nat.pair 0) (by omega)
        exact (Binding.Var.appendCases_natural codeTm _ Γ' _ x).trans
          (Binding.Var.appendCases_val _ Γ'
            (fun n => subCode j (shiftCode j e) (Nat.pair 0 n)) _ hold hnew x)
      cases o with
      | app σa τa =>
          have hlennil : (Γ' ++ ([] : Binding.Ctx RType)).length
              = (Δ ++ ([] : Binding.Ctx RType)).length + 1 := by
            simp only [List.append_nil]; exact hlen
          have hjnil : j ≤ (Δ ++ ([] : Binding.Ctx RType)).length := by
            simp only [List.append_nil]; exact hj
          have henil : shiftCode (Δ ++ ([] : Binding.Ctx RType)).length e
              = shiftCode j e := by
            simp only [List.append_nil]; exact he
          have h0 := ih ⟨(0 : Fin 2)⟩
            (Binding.Env.underBinder (Binding.subKit (oneLambdaSig natAlgSig))
              (Ξ := ([] : Binding.Ctx RType)) σ) e hlennil hjnil henil hσnil
          have h1 := ih ⟨(1 : Fin 2)⟩
            (Binding.Env.underBinder (Binding.subKit (oneLambdaSig natAlgSig))
              (Ξ := ([] : Binding.Ctx RType)) σ) e hlennil hjnil henil hσnil
          refine Eq.trans (congrArg (fun q => Nat.pair 1
              (Nat.pair (codeOp (OneLambdaOp.app σa τa)) q))
              (congrArg₂ Nat.pair h0 (congrArg₂ Nat.pair h1 rfl)))
            (subCode_app j e (codeOp (OneLambdaOp.app σa τa)) _ _
              (by simp [codeOp, Nat.unpair_pair])).symm
      | lam σa τa =>
          have hlenone : (Γ' ++ [σa]).length = (Δ ++ [σa]).length + 1 := by
            simp only [List.length_append, List.length_cons, List.length_nil]
            omega
          have hjone : j ≤ (Δ ++ [σa]).length := by
            simp only [List.length_append]
            omega
          have heone : shiftCode (Δ ++ [σa]).length (shiftCode j e)
              = shiftCode j (shiftCode j e) := by
            have hlist : (Δ ++ [σa]).length = Δ.length + 1 := by simp
            rw [hlist, shiftCode_shiftCode hj e, he]
          have h0 := ih ⟨(0 : Fin 1)⟩
            (Binding.Env.underBinder (Binding.subKit (oneLambdaSig natAlgSig))
              (Ξ := [σa]) σ) (shiftCode j e) hlenone hjone heone (hσone σa)
          refine Eq.trans (congrArg (fun q => Nat.pair 1
              (Nat.pair (codeOp (OneLambdaOp.lam σa τa)) q))
              (congrArg₂ Nat.pair h0 rfl))
            (subCode_lam j e (codeOp (OneLambdaOp.lam σa τa)) _
              (by simp [codeOp, Nat.unpair_pair])).symm
      | con b =>
          exact (subCode_const j e (codeOp (OneLambdaOp.con b)) _
            (by simp [codeOp, Nat.unpair_pair])).symm
      | dstr i =>
          exact (subCode_const j e (codeOp (OneLambdaOp.dstr i)) _
            (by simp [codeOp, Nat.unpair_pair])).symm
      | case =>
          exact (subCode_const j e (codeOp OneLambdaOp.case) _
            (by simp [codeOp, Nat.unpair_pair])).symm

/-- The commutation of the code-level substitution with single-variable
instantiation (the mirror theorem of the code-normalizer's substitution layer):
rewriting the code of a body `d` by `subCode` at the substituted level
`Γ.length` with the substituend code `codeTm e` computes the code of the
genuine reduct `Binding.instantiate₁ e d`. The `codeTm_sub` corollary at the
instantiating environment, whose fresh image is `e` (the `i = j` branch of
`subCode_var`) and whose old images are variables below the substituted level
(the `i < j` branch). Novel realization. -/
theorem subCode_codeTm {Γ : Binding.Ctx RType} {a s : RType}
    (e : Binding.Tm (oneLambdaSig natAlgSig) Γ a)
    (d : Binding.Tm (oneLambdaSig natAlgSig) (Γ ++ [a]) s) :
    subCode Γ.length (codeTm e) (codeTm d) = codeTm (Binding.instantiate₁ e d) := by
  unfold Binding.instantiate₁ Binding.instantiate
  refine (codeTm_sub Γ.length _ (codeTm e) (by simp) le_rfl rfl ?_ d).symm
  intro u x
  rw [Binding.extendEnv_apply]
  have hold : ∀ v : Binding.Var Γ u,
      codeTm (Binding.idEnv (S := oneLambdaSig natAlgSig) u v)
        = subCode Γ.length (codeTm e) (Nat.pair 0 v.1.val) := by
    intro v
    simp only [Binding.idEnv, codeTm_var]
    rw [subCode_var, if_pos v.1.isLt]
  have hnew : ∀ w : Binding.Var [a] u,
      codeTm (Binding.metaOne (S := oneLambdaSig natAlgSig) e u w)
        = subCode Γ.length (codeTm e) (Nat.pair 0 (Γ.length + w.1.val)) := by
    intro w
    obtain ⟨i, hi⟩ := w
    cases i using Fin.cases with
    | zero =>
        refine (codeTm_cast rfl hi e).trans ?_
        rw [subCode_var, if_neg (by simp), if_pos (by simp)]
        rfl
    | succ k => exact k.elim0
  exact (Binding.Var.appendCases_natural codeTm _ Γ _ x).trans
    (Binding.Var.appendCases_val _ Γ
      (fun n => subCode Γ.length (codeTm e) (Nat.pair 0 n)) _ hold hnew x)

/-- The code-level image of the abstraction detector `isLam`: a code is a `lam`
node when its top kind bit is `1` (an operation node) and its operation kind bit
is `1` (the abstraction operation). Non-recursive read of the top node. Novel
realization. -/
def isLamCode (c : ℕ) : Bool :=
  (Nat.unpair c).1 == 1 && (Nat.unpair (Nat.unpair (Nat.unpair c).2).1).1 == 1

/-- The node equation of `isLamCode` at a variable leaf `Nat.pair 0 i`: a
variable is never an abstraction. -/
theorem isLamCode_var (i : ℕ) : isLamCode (Nat.pair 0 i) = false := by
  simp [isLamCode, Nat.unpair_pair]

/-- The node equation of `isLamCode` at an operation node `Nat.pair 1 (Nat.pair
op pack)`: the node is an abstraction exactly when the operation kind bit is
`1`. -/
theorem isLamCode_op (op pack : ℕ) :
    isLamCode (Nat.pair 1 (Nat.pair op pack)) = ((Nat.unpair op).1 == 1) := by
  simp [isLamCode, Nat.unpair_pair]

/-- The abstraction-detector mirror: reading `isLamCode` off a term code agrees
with the term-level abstraction detector `isLam`. By cases on the top node, the
operation kind bits of `codeOp` selecting the `lam` operation. -/
theorem isLamCode_codeTm {Γ : Binding.Ctx RType} {s : RType}
    (t : Binding.Tm (oneLambdaSig natAlgSig) Γ s) :
    isLamCode (codeTm t) = isLam t := by
  suffices h : ∀ {y : Binding.Ctx RType × RType}
      (t : PolyFix (polyTranslate Binding.varOver (oneLambdaSig natAlgSig).polyEndo) y),
      isLamCode (codeTm (Γ := y.1) (s := y.2) t) = isLam (Γ := y.1) (s := y.2) t from h t
  intro y t
  induction t with
  | mk y idx children ih =>
    cases idx with
    | inl a =>
      rw [show (PolyFix.mk y (Sum.inl a) children
            : Binding.Tm (oneLambdaSig natAlgSig) y.1 y.2)
            = Binding.Tm.var (Binding.leafVar a) from by
              obtain ⟨⟨Γ', i'⟩, rfl⟩ := a
              congr 1
              funext e
              exact e.elim]
      rw [codeTm_var, isLamCode_var, isLam_var]
    | inr p =>
      obtain ⟨Γ', s'⟩ := y
      change { o : (oneLambdaSig natAlgSig).Op // (oneLambdaSig natAlgSig).result o = s' } at p
      revert children ih
      obtain ⟨o, rfl⟩ := p
      intro children ih
      rw [show (PolyFix.mk (Γ', (oneLambdaSig natAlgSig).result o) (Sum.inr ⟨o, rfl⟩) children
            : Binding.Tm (oneLambdaSig natAlgSig) Γ' ((oneLambdaSig natAlgSig).result o))
            = Binding.Tm.op (S := oneLambdaSig natAlgSig) o (fun j => children ⟨j⟩)
            from rfl]
      rw [codeTm_op, isLamCode_op]
      cases o <;> simp [codeOp, Nat.unpair_pair, isLam, headTag_op]

set_option linter.unusedVariables false in
/-- The operation dispatch of `conHeadedCode`: the code-level image of `conHeaded`
descending the function child of an application. Strong recursion on the code
value: an application node (operation kind bit `0`) recurses into its function
child code; a constructor node (kind bit `2`) is `true`; every other node is
`false`. Novel realization. The `linter.unusedVariables` disable covers the
`match`-bound discriminant equation, referenced only in the termination proof of
this single-recursive-call definition. -/
def conHeadedCode (c : ℕ) : Bool :=
  match h : (Nat.unpair c).1, (Nat.unpair (Nat.unpair (Nat.unpair c).2).1).1 with
  | 1, 0 => conHeadedCode (Nat.unpair (Nat.unpair (Nat.unpair c).2).2).1
  | 1, 2 => true
  | _, _ => false
  termination_by c
  decreasing_by
    have key : (Nat.unpair c).2 < c := by
      conv_rhs => rw [← Nat.pair_unpair c, h]
      exact self_lt_pair_one _
    exact Nat.lt_of_le_of_lt
      (le_trans (Nat.unpair_left_le _) (Nat.unpair_right_le _)) key

/-- The node equation of `conHeadedCode` at a variable leaf `Nat.pair 0 i`: a
variable is not `con`-headed. -/
theorem conHeadedCode_var (i : ℕ) : conHeadedCode (Nat.pair 0 i) = false := by
  rw [conHeadedCode]; split <;> simp_all [Nat.unpair_pair]

/-- The node equation of `conHeadedCode` at an application node (operation kind
bit `0`): the spine descends into the function child code. -/
theorem conHeadedCode_app (op c0 c1 : ℕ) (hop : (Nat.unpair op).1 = 0) :
    conHeadedCode (Nat.pair 1 (Nat.pair op (Nat.pair c0 (Nat.pair c1 0))))
      = conHeadedCode c0 := by
  rw [conHeadedCode]; split <;> simp_all [Nat.unpair_pair]

/-- The node equation of `conHeadedCode` at a constructor node (operation kind
bit `2`): the head is a constructor. -/
theorem conHeadedCode_con (op pack : ℕ) (hop : (Nat.unpair op).1 = 2) :
    conHeadedCode (Nat.pair 1 (Nat.pair op pack)) = true := by
  rw [conHeadedCode]; split <;> simp_all [Nat.unpair_pair]

/-- The node equation of `conHeadedCode` at an operation node whose kind bit is
neither `0` (application) nor `2` (constructor): the head is not a
constructor. -/
theorem conHeadedCode_op_false (op pack : ℕ)
    (hop0 : (Nat.unpair op).1 ≠ 0) (hop2 : (Nat.unpair op).1 ≠ 2) :
    conHeadedCode (Nat.pair 1 (Nat.pair op pack)) = false := by
  rw [conHeadedCode]; split <;> simp_all [Nat.unpair_pair]

/-- The `con`-headedness mirror: reading `conHeadedCode` off a term code agrees
with the term-level spine detector `conHeaded`. Structural induction on the term
via `PolyFix.ind`, the operation kind bits of `codeOp` feeding the code node
equations, and the induction hypothesis on the function child at an
application. -/
theorem conHeadedCode_codeTm {Γ : Binding.Ctx RType} {s : RType}
    (t : Binding.Tm (oneLambdaSig natAlgSig) Γ s) :
    conHeadedCode (codeTm t) = conHeaded t := by
  suffices h : ∀ {y : Binding.Ctx RType × RType}
      (t : PolyFix (polyTranslate Binding.varOver (oneLambdaSig natAlgSig).polyEndo) y),
      conHeadedCode (codeTm (Γ := y.1) (s := y.2) t) = conHeaded (Γ := y.1) (s := y.2) t from h t
  intro y t
  induction t with
  | mk y idx children ih =>
    cases idx with
    | inl a =>
      rw [show (PolyFix.mk y (Sum.inl a) children
            : Binding.Tm (oneLambdaSig natAlgSig) y.1 y.2)
            = Binding.Tm.var (Binding.leafVar a) from by
              obtain ⟨⟨Γ', i'⟩, rfl⟩ := a
              congr 1
              funext e
              exact e.elim]
      rw [codeTm_var, conHeadedCode_var, conHeaded_var]
    | inr p =>
      obtain ⟨Γ', s'⟩ := y
      change { o : (oneLambdaSig natAlgSig).Op // (oneLambdaSig natAlgSig).result o = s' } at p
      revert children ih
      obtain ⟨o, rfl⟩ := p
      intro children ih
      rw [show (PolyFix.mk (Γ', (oneLambdaSig natAlgSig).result o) (Sum.inr ⟨o, rfl⟩) children
            : Binding.Tm (oneLambdaSig natAlgSig) Γ' ((oneLambdaSig natAlgSig).result o))
            = Binding.Tm.op (S := oneLambdaSig natAlgSig) o (fun j => children ⟨j⟩)
            from rfl]
      rw [codeTm_op, conHeaded_op]
      cases o with
      | app σ τ =>
          exact Eq.trans
            (conHeadedCode_app (codeOp (OneLambdaOp.app σ τ)) (codeTm (children ⟨(0 : Fin 2)⟩))
              (codeTm (children ⟨(1 : Fin 2)⟩)) (by simp [codeOp, Nat.unpair_pair]))
            (ih ⟨(0 : Fin 2)⟩)
      | lam σ τ =>
          rw [conHeadedCode_op_false _ _ (by simp [codeOp, Nat.unpair_pair])
            (by simp [codeOp, Nat.unpair_pair])]
          rfl
      | con b =>
          rw [conHeadedCode_con _ _ (by simp [codeOp, Nat.unpair_pair])]
          rfl
      | dstr j =>
          rw [conHeadedCode_op_false _ _ (by simp [codeOp, Nat.unpair_pair])
            (by simp [codeOp, Nat.unpair_pair])]
          rfl
      | case =>
          rw [conHeadedCode_op_false _ _ (by simp [codeOp, Nat.unpair_pair])
            (by simp [codeOp, Nat.unpair_pair])]
          rfl

/-- The code-level image of the top β-rank `topBetaRank`: a non-recursive read of
the top node. At an application node (operation kind bit `0`) whose function
child code is a `lam` node, the order read off the applied arrow-sort code
(rebuilt as `Nat.pair 1` over the application tag's domain/codomain pair);
otherwise `0`. Novel realization. -/
def topBetaRankCode (c : ℕ) : ℕ :=
  match (Nat.unpair c).1, (Nat.unpair (Nat.unpair (Nat.unpair c).2).1).1 with
  | 1, 0 =>
      if isLamCode (Nat.unpair (Nat.unpair (Nat.unpair c).2).2).1 then
        ordCode (Nat.pair 1 (Nat.unpair (Nat.unpair (Nat.unpair c).2).1).2)
      else 0
  | _, _ => 0

/-- The node equation of `topBetaRankCode` at a variable leaf `Nat.pair 0 i`: a
variable contributes no top β-rank. -/
theorem topBetaRankCode_var (i : ℕ) : topBetaRankCode (Nat.pair 0 i) = 0 := by
  rw [topBetaRankCode]; split <;> simp_all [Nat.unpair_pair]

/-- The node equation of `topBetaRankCode` at an application node (operation kind
bit `0`): the top β-rank is the order read off the applied arrow-sort code when
the function child is a `lam`, and `0` otherwise. -/
theorem topBetaRankCode_app (op c0 c1 : ℕ) (hop : (Nat.unpair op).1 = 0) :
    topBetaRankCode (Nat.pair 1 (Nat.pair op (Nat.pair c0 (Nat.pair c1 0))))
      = if isLamCode c0 then ordCode (Nat.pair 1 (Nat.unpair op).2) else 0 := by
  rw [topBetaRankCode]; split <;> simp_all [Nat.unpair_pair]

/-- The node equation of `topBetaRankCode` at an operation node whose kind bit is
not `0`: no such node is an application, so the top β-rank is `0`. -/
theorem topBetaRankCode_op_ne_app (op pack : ℕ) (hop : (Nat.unpair op).1 ≠ 0) :
    topBetaRankCode (Nat.pair 1 (Nat.pair op pack)) = 0 := by
  rw [topBetaRankCode]; split <;> simp_all [Nat.unpair_pair]

/-- The top-β-rank mirror: reading `topBetaRankCode` off a term code agrees with
the term-level top β-rank `topBetaRank`. By cases on the top node; at an
application the applied arrow-sort code rebuilds `codeRType (arrow σ τ)`, whose
`ordCode` is `RType.ord (arrow σ τ)` by `ordCode_codeRType`, and the function
child's abstraction status transfers by `isLamCode_codeTm`. -/
theorem topBetaRankCode_codeTm {Γ : Binding.Ctx RType} {s : RType}
    (t : Binding.Tm (oneLambdaSig natAlgSig) Γ s) :
    topBetaRankCode (codeTm t) = topBetaRank t := by
  suffices h : ∀ {y : Binding.Ctx RType × RType}
      (t : PolyFix (polyTranslate Binding.varOver (oneLambdaSig natAlgSig).polyEndo) y),
      topBetaRankCode (codeTm (Γ := y.1) (s := y.2) t)
        = topBetaRank (Γ := y.1) (s := y.2) t from h t
  intro y t
  induction t with
  | mk y idx children ih =>
    cases idx with
    | inl a =>
      rw [show (PolyFix.mk y (Sum.inl a) children
            : Binding.Tm (oneLambdaSig natAlgSig) y.1 y.2)
            = Binding.Tm.var (Binding.leafVar a) from by
              obtain ⟨⟨Γ', i'⟩, rfl⟩ := a
              congr 1
              funext e
              exact e.elim]
      rw [codeTm_var, topBetaRankCode_var, topBetaRank_var]
    | inr p =>
      obtain ⟨Γ', s'⟩ := y
      change { o : (oneLambdaSig natAlgSig).Op // (oneLambdaSig natAlgSig).result o = s' } at p
      revert children ih
      obtain ⟨o, rfl⟩ := p
      intro children ih
      rw [show (PolyFix.mk (Γ', (oneLambdaSig natAlgSig).result o) (Sum.inr ⟨o, rfl⟩) children
            : Binding.Tm (oneLambdaSig natAlgSig) Γ' ((oneLambdaSig natAlgSig).result o))
            = Binding.Tm.op (S := oneLambdaSig natAlgSig) o (fun j => children ⟨j⟩)
            from rfl]
      rw [codeTm_op, topBetaRank_op]
      cases o with
      | app σ τ =>
          have hord : ordCode (Nat.pair 1 (Nat.unpair (codeOp (OneLambdaOp.app σ τ))).2)
              = RType.ord (RType.arrow σ τ) := by
            rw [show (Nat.unpair (codeOp (OneLambdaOp.app σ τ))).2
                = Nat.pair (codeRType σ) (codeRType τ) from by simp [codeOp, Nat.unpair_pair],
              ← codeRType_arrow, ordCode_codeRType]
          refine Eq.trans (topBetaRankCode_app (codeOp (OneLambdaOp.app σ τ))
            (codeTm (children ⟨(0 : Fin 2)⟩)) (codeTm (children ⟨(1 : Fin 2)⟩))
            (by simp [codeOp, Nat.unpair_pair])) ?_
          rw [isLamCode_codeTm, hord]
          rfl
      | lam σ τ =>
          rw [topBetaRankCode_op_ne_app _ _ (by simp [codeOp, Nat.unpair_pair])]
          rfl
      | con b =>
          rw [topBetaRankCode_op_ne_app _ _ (by simp [codeOp, Nat.unpair_pair])]
          rfl
      | dstr j =>
          rw [topBetaRankCode_op_ne_app _ _ (by simp [codeOp, Nat.unpair_pair])]
          rfl
      | case =>
          rw [topBetaRankCode_op_ne_app _ _ (by simp [codeOp, Nat.unpair_pair])]
          rfl

set_option linter.unusedVariables false in
/-- The code-level image of the spine detector `iotaSpine`: strong recursion on
the code descending the function child of an application spine. At an application
node (operation kind bit `0`) it inspects the function child code: a destructor
head (kind bit `3`) or a case head (kind bit `4`) bottoms the spine at the
`con`-headedness of the argument child; a further application head (kind bit `0`)
continues the descent into the function child; every other head is `false`.
Non-application nodes are `false`. Novel realization. The `linter.unusedVariables`
disable covers the `match`-bound discriminant equation, referenced only in the
termination proof. -/
def iotaSpineCode (c : ℕ) : Bool :=
  match h : (Nat.unpair c).1, (Nat.unpair (Nat.unpair (Nat.unpair c).2).1).1,
      (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair c).2).2).1).1,
      (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair c).2).2).1).2).1).1
      with
  | 1, 0, 1, 3 => conHeadedCode (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair c).2).2).2).1
  | 1, 0, 1, 4 => conHeadedCode (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair c).2).2).2).1
  | 1, 0, 1, 0 => iotaSpineCode (Nat.unpair (Nat.unpair (Nat.unpair c).2).2).1
  | _, _, _, _ => false
  termination_by c
  decreasing_by
    have key : (Nat.unpair c).2 < c := by
      conv_rhs => rw [← Nat.pair_unpair c, h]
      exact self_lt_pair_one _
    exact Nat.lt_of_le_of_lt
      (le_trans (Nat.unpair_left_le _) (Nat.unpair_right_le _)) key

/-- The node equation of `iotaSpineCode` at a variable leaf `Nat.pair 0 i`: a
variable does not bottom an ι-spine. -/
theorem iotaSpineCode_var (i : ℕ) : iotaSpineCode (Nat.pair 0 i) = false := by
  rw [iotaSpineCode]; split <;> simp_all [Nat.unpair_pair]

/-- The node equation of `iotaSpineCode` at an operation node whose kind bit is
not `0`: no such node is an application, so it does not bottom an ι-spine. -/
theorem iotaSpineCode_op_ne_app (op pack : ℕ) (hop : (Nat.unpair op).1 ≠ 0) :
    iotaSpineCode (Nat.pair 1 (Nat.pair op pack)) = false := by
  rw [iotaSpineCode]; split <;> simp_all [Nat.unpair_pair]

/-- The node equation of `iotaSpineCode` at an application node (operation kind
bit `0`) with function child code `c0` and argument child code `c1`: the spine
dispatches on the function child's head kind bits. -/
theorem iotaSpineCode_app (op c0 c1 : ℕ) (hop : (Nat.unpair op).1 = 0) :
    iotaSpineCode (Nat.pair 1 (Nat.pair op (Nat.pair c0 (Nat.pair c1 0))))
      = (match (Nat.unpair c0).1, (Nat.unpair (Nat.unpair (Nat.unpair c0).2).1).1 with
         | 1, 3 => conHeadedCode c1
         | 1, 4 => conHeadedCode c1
         | 1, 0 => iotaSpineCode c0
         | _, _ => false) := by
  rw [iotaSpineCode]
  split <;> simp_all [Nat.unpair_pair]

/-- The head-form reads of a term code: either the top kind bit is `0` and the
head operation is absent (a variable), or the top kind bit is `1`, the operation
kind bit reads the operation's `codeOp` kind, and the head operation is that
operation. The transport-free bridge between the code reads that `iotaSpineCode`
dispatches on and the term-level `headTag`. -/
theorem codeTm_headForm {Γ : Binding.Ctx RType} {s : RType}
    (t : Binding.Tm (oneLambdaSig natAlgSig) Γ s) :
    ((Nat.unpair (codeTm t)).1 = 0 ∧ headTag t = none) ∨
    ∃ o : OneLambdaOp natAlgSig, (Nat.unpair (codeTm t)).1 = 1 ∧
      (Nat.unpair (Nat.unpair (Nat.unpair (codeTm t)).2).1).1 = (Nat.unpair (codeOp o)).1 ∧
      headTag t = some o := by
  suffices h : ∀ {y : Binding.Ctx RType × RType}
      (t : PolyFix (polyTranslate Binding.varOver (oneLambdaSig natAlgSig).polyEndo) y),
      ((Nat.unpair (codeTm (Γ := y.1) (s := y.2) t)).1 = 0
          ∧ headTag (Γ := y.1) (s := y.2) t = none) ∨
      ∃ o : OneLambdaOp natAlgSig, (Nat.unpair (codeTm (Γ := y.1) (s := y.2) t)).1 = 1 ∧
        (Nat.unpair (Nat.unpair (Nat.unpair (codeTm (Γ := y.1) (s := y.2) t)).2).1).1
          = (Nat.unpair (codeOp o)).1 ∧
        headTag (Γ := y.1) (s := y.2) t = some o from h t
  intro y t
  induction t with
  | mk y idx children ih =>
    cases idx with
    | inl a =>
      rw [show (PolyFix.mk y (Sum.inl a) children
            : Binding.Tm (oneLambdaSig natAlgSig) y.1 y.2)
            = Binding.Tm.var (Binding.leafVar a) from by
              obtain ⟨⟨Γ', i'⟩, rfl⟩ := a
              congr 1
              funext e
              exact e.elim]
      exact Or.inl ⟨by rw [codeTm_var, Nat.unpair_pair], headTag_var _⟩
    | inr p =>
      obtain ⟨Γ', s'⟩ := y
      change { o : (oneLambdaSig natAlgSig).Op // (oneLambdaSig natAlgSig).result o = s' } at p
      revert children ih
      obtain ⟨o, rfl⟩ := p
      intro children ih
      rw [show (PolyFix.mk (Γ', (oneLambdaSig natAlgSig).result o) (Sum.inr ⟨o, rfl⟩) children
            : Binding.Tm (oneLambdaSig natAlgSig) Γ' ((oneLambdaSig natAlgSig).result o))
            = Binding.Tm.op (S := oneLambdaSig natAlgSig) o (fun j => children ⟨j⟩)
            from rfl]
      refine Or.inr ⟨o, ?_, ?_, headTag_op _ _⟩
      · simp only [codeTm_op, Nat.unpair_pair]
      · simp only [codeTm_op, Nat.unpair_pair]

/-- The spine-detector mirror: reading `iotaSpineCode` off a term code agrees
with the term-level spine detector `iotaSpine`. Structural induction on the term;
at an application the function child's head is read off its code by
`codeTm_headForm`, dispatching to `conHeadedCode_codeTm` at a destructor or case
head and to the induction hypothesis at a further application. -/
theorem iotaSpineCode_codeTm {Γ : Binding.Ctx RType} {s : RType}
    (t : Binding.Tm (oneLambdaSig natAlgSig) Γ s) :
    iotaSpineCode (codeTm t) = iotaSpine t := by
  suffices h : ∀ {y : Binding.Ctx RType × RType}
      (t : PolyFix (polyTranslate Binding.varOver (oneLambdaSig natAlgSig).polyEndo) y),
      iotaSpineCode (codeTm (Γ := y.1) (s := y.2) t)
        = iotaSpine (Γ := y.1) (s := y.2) t from h t
  intro y t
  induction t with
  | mk y idx children ih =>
    cases idx with
    | inl a =>
      rw [show (PolyFix.mk y (Sum.inl a) children
            : Binding.Tm (oneLambdaSig natAlgSig) y.1 y.2)
            = Binding.Tm.var (Binding.leafVar a) from by
              obtain ⟨⟨Γ', i'⟩, rfl⟩ := a
              congr 1
              funext e
              exact e.elim]
      rw [codeTm_var, iotaSpineCode_var, iotaSpine_var]
    | inr p =>
      obtain ⟨Γ', s'⟩ := y
      change { o : (oneLambdaSig natAlgSig).Op // (oneLambdaSig natAlgSig).result o = s' } at p
      revert children ih
      obtain ⟨o, rfl⟩ := p
      intro children ih
      rw [show (PolyFix.mk (Γ', (oneLambdaSig natAlgSig).result o) (Sum.inr ⟨o, rfl⟩) children
            : Binding.Tm (oneLambdaSig natAlgSig) Γ' ((oneLambdaSig natAlgSig).result o))
            = Binding.Tm.op (S := oneLambdaSig natAlgSig) o (fun j => children ⟨j⟩)
            from rfl]
      rw [codeTm_op, iotaSpine_op]
      cases o with
      | app σ τ =>
          refine Eq.trans (iotaSpineCode_app (codeOp (OneLambdaOp.app σ τ))
            (codeTm (children ⟨⟨0, Nat.succ_pos 1⟩⟩)) (codeTm (children ⟨⟨1, Nat.one_lt_two⟩⟩))
            (by simp [codeOp, Nat.unpair_pair])) ?_
          simp only [iotaSpineOp]
          rcases codeTm_headForm (children ⟨⟨0, Nat.succ_pos 1⟩⟩) with
            ⟨hk, hht⟩ | ⟨o', hk, hfop, hht⟩
          · simp [hk, hht]
          · simp only [hk, hfop, hht]
            cases o' with
            | app σ' τ' => simpa [codeOp, Nat.unpair_pair] using ih ⟨⟨0, Nat.succ_pos 1⟩⟩
            | lam σ' τ' => simp [codeOp, Nat.unpair_pair]
            | con b => simp [codeOp, Nat.unpair_pair]
            | dstr j =>
                simp only [codeOp, Nat.unpair_pair]
                exact conHeadedCode_codeTm (children ⟨⟨1, Nat.one_lt_two⟩⟩)
            | case =>
                simp only [codeOp, Nat.unpair_pair]
                exact conHeadedCode_codeTm (children ⟨⟨1, Nat.one_lt_two⟩⟩)
      | lam σ τ =>
          rw [iotaSpineCode_op_ne_app _ _ (by simp [codeOp, Nat.unpair_pair])]
          rfl
      | con b =>
          rw [iotaSpineCode_op_ne_app _ _ (by simp [codeOp, Nat.unpair_pair])]
          rfl
      | dstr j =>
          rw [iotaSpineCode_op_ne_app _ _ (by simp [codeOp, Nat.unpair_pair])]
          rfl
      | case =>
          rw [iotaSpineCode_op_ne_app _ _ (by simp [codeOp, Nat.unpair_pair])]
          rfl

/-- The result-sort shape read off an operation-node code: the numeric shape of
the node's result sort, computed from the operation tag. At an application
(operation kind bit `0`) it is the shape of the codomain sort code carried in the
tag; abstractions, destructors, and the case combinator have arrow result sorts
(shape `1`); the constructor and variable readings are don't-care (default `0`),
where the spine detector already vanishes. Novel realization; the plan's named
helper (`resultShapeCode`). -/
def resultShapeCode (c : ℕ) : ℕ :=
  match (Nat.unpair (Nat.unpair (Nat.unpair c).2).1).1 with
  | 0 => shapeCode (codCode (Nat.unpair (Nat.unpair c).2).1)
  | 1 => 1
  | 3 => 1
  | 4 => 1
  | _ => 0

/-- The node equation of `resultShapeCode` at an application node (operation kind
bit `0`): the result shape is the shape of the codomain sort code read off the
operation tag. -/
theorem resultShapeCode_app (op pack : ℕ) (hop : (Nat.unpair op).1 = 0) :
    resultShapeCode (Nat.pair 1 (Nat.pair op pack)) = shapeCode (codCode op) := by
  rw [resultShapeCode]
  simp only [Nat.unpair_pair, hop]

/-- Reading the shape off a type code detects the base sort `o`: `shapeCode
(codeRType τ)` is `0` exactly when `τ` has base shape. By structural induction on
the r-type through the `codeRType` node tags. -/
theorem shapeCode_codeRType_zero_iff (τ : RType) :
    shapeCode (codeRType τ) = 0 ↔ RType.shape τ = RTypeShape.o :=
  PolyFix.ind (P := rTypeSig.polyEndo)
    (motive := fun {_} t => shapeCode (codeRType t) = 0 ↔ RType.shape t = RTypeShape.o)
    (fun i childx ih =>
      match i, childx, ih with
      | RTypeShape.o, _, _ => by
          change (Nat.unpair (Nat.pair 0 0)).1 = 0 ↔ _
          simp [Nat.unpair_pair, RType.shape, PolyFix.index]
      | RTypeShape.arrow, childx, _ => by
          change (Nat.unpair (Nat.pair 1 _)).1 = 0 ↔ _
          simp [Nat.unpair_pair, RType.shape, PolyFix.index]
      | RTypeShape.omega, childx, _ => by
          change (Nat.unpair (Nat.pair 2 _)).1 = 0 ↔ _
          simp [Nat.unpair_pair, RType.shape, PolyFix.index]) τ

/-- The code-level image of the sort-gated ι-redex detector `topIota`: the spine
detector `iotaSpineCode` restricted to codes whose result-sort shape is the base
sort `o` (`resultShapeCode c = 0`). Novel realization. -/
def topIotaCode (c : ℕ) : Bool :=
  if resultShapeCode c = 0 then iotaSpineCode c else false

/-- The node equation of `topIotaCode` at a variable leaf `Nat.pair 0 i`: a
variable is not a top ι-redex. -/
theorem topIotaCode_var (i : ℕ) : topIotaCode (Nat.pair 0 i) = false := by
  simp only [topIotaCode, iotaSpineCode_var, ite_self]

/-- The top-ι mirror: reading `topIotaCode` off a term code agrees with the
term-level sort-gated ι-redex detector `topIota`. The spine content transfers by
`iotaSpineCode_codeTm`; at an application the result-shape gate reads the codomain
sort shape, agreeing with the term's result-sort gate by
`shapeCode_codeRType_zero_iff`, and at every other node the spine content already
vanishes. -/
theorem topIotaCode_codeTm {Γ : Binding.Ctx RType} {s : RType}
    (t : Binding.Tm (oneLambdaSig natAlgSig) Γ s) :
    topIotaCode (codeTm t) = topIota t := by
  suffices h : ∀ {y : Binding.Ctx RType × RType}
      (t : PolyFix (polyTranslate Binding.varOver (oneLambdaSig natAlgSig).polyEndo) y),
      topIotaCode (codeTm (Γ := y.1) (s := y.2) t)
        = topIota (Γ := y.1) (s := y.2) t from h t
  intro y t
  induction t with
  | mk y idx children ih =>
    cases idx with
    | inl a =>
      rw [show (PolyFix.mk y (Sum.inl a) children
            : Binding.Tm (oneLambdaSig natAlgSig) y.1 y.2)
            = Binding.Tm.var (Binding.leafVar a) from by
              obtain ⟨⟨Γ', i'⟩, rfl⟩ := a
              congr 1
              funext e
              exact e.elim]
      rw [codeTm_var, topIotaCode_var, topIota_var]
    | inr p =>
      obtain ⟨Γ', s'⟩ := y
      change { o : (oneLambdaSig natAlgSig).Op // (oneLambdaSig natAlgSig).result o = s' } at p
      revert children ih
      obtain ⟨o, rfl⟩ := p
      intro children ih
      rw [show (PolyFix.mk (Γ', (oneLambdaSig natAlgSig).result o) (Sum.inr ⟨o, rfl⟩) children
            : Binding.Tm (oneLambdaSig natAlgSig) Γ' ((oneLambdaSig natAlgSig).result o))
            = Binding.Tm.op (S := oneLambdaSig natAlgSig) o (fun j => children ⟨j⟩)
            from rfl]
      cases o with
      | app σ τ =>
          have hshape : resultShapeCode (codeTm
              (Binding.Tm.op (S := oneLambdaSig natAlgSig) (OneLambdaOp.app σ τ)
                (fun j => children ⟨j⟩))) = shapeCode (codeRType τ) := by
            rw [codeTm_op, resultShapeCode_app _ _ (by simp [codeOp, Nat.unpair_pair])]
            simp [codeOp, codCode, argCode, Nat.unpair_pair]
          change (if resultShapeCode (codeTm
              (Binding.Tm.op (S := oneLambdaSig natAlgSig) (OneLambdaOp.app σ τ)
                (fun j => children ⟨j⟩))) = 0
              then iotaSpineCode (codeTm
                (Binding.Tm.op (S := oneLambdaSig natAlgSig) (OneLambdaOp.app σ τ)
                  (fun j => children ⟨j⟩)))
              else false)
            = (if τ.shape = RTypeShape.o
              then iotaSpine (Binding.Tm.op (S := oneLambdaSig natAlgSig) (OneLambdaOp.app σ τ)
                (fun j => children ⟨j⟩))
              else false)
          rw [hshape, iotaSpineCode_codeTm]
          by_cases hτ : τ.shape = RTypeShape.o
          · rw [if_pos ((shapeCode_codeRType_zero_iff τ).mpr hτ), if_pos hτ]
          · rw [if_neg (fun h => hτ ((shapeCode_codeRType_zero_iff τ).mp h)), if_neg hτ]
      | lam σ τ =>
          simp only [topIotaCode, topIota, iotaSpineCode_codeTm, iotaSpine_op,
            iotaSpineOp, ite_self]
      | con b =>
          simp only [topIotaCode, topIota, iotaSpineCode_codeTm, iotaSpine_op,
            iotaSpineOp, ite_self]
      | dstr j =>
          simp only [topIotaCode, topIota, iotaSpineCode_codeTm, iotaSpine_op,
            iotaSpineOp, ite_self]
      | case =>
          simp only [topIotaCode, topIota, iotaSpineCode_codeTm, iotaSpine_op,
            iotaSpineOp, ite_self]

set_option linter.unusedVariables false in
/-- The code-level image of the β-rank measure `betaRedexRank`: strong recursion
on the code taking the maximum of the top β-rank `topBetaRankCode` with the
β-ranks of the child codes. An application node (operation kind bit `0`) maxes the
top rank over both children; an abstraction node (kind bit `1`) recurses into its
body child; every other node is `0`. Novel realization. The
`linter.unusedVariables` disable covers the `match`-bound discriminant equation,
referenced only in the termination proof. -/
def betaRankCode (c : ℕ) : ℕ :=
  match h : (Nat.unpair c).1, (Nat.unpair (Nat.unpair (Nat.unpair c).2).1).1 with
  | 1, 0 =>
      max (topBetaRankCode c)
        (max (betaRankCode (Nat.unpair (Nat.unpair (Nat.unpair c).2).2).1)
          (betaRankCode (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair c).2).2).2).1))
  | 1, 1 => betaRankCode (Nat.unpair (Nat.unpair (Nat.unpair c).2).2).1
  | _, _ => 0
  termination_by c
  decreasing_by
    all_goals
      have key : (Nat.unpair c).2 < c := by
        conv_rhs => rw [← Nat.pair_unpair c, h]
        exact self_lt_pair_one _
      first
      | exact Nat.lt_of_le_of_lt
          (le_trans (Nat.unpair_left_le _) (Nat.unpair_right_le _)) key
      | exact Nat.lt_of_le_of_lt
          (le_trans (le_trans (Nat.unpair_left_le _) (Nat.unpair_right_le _))
            (Nat.unpair_right_le _)) key

/-- The node equation of `betaRankCode` at a variable leaf `Nat.pair 0 i`. -/
theorem betaRankCode_var (i : ℕ) : betaRankCode (Nat.pair 0 i) = 0 := by
  rw [betaRankCode]; split <;> simp_all [Nat.unpair_pair]

/-- The node equation of `betaRankCode` at an application node (operation kind bit
`0`): the maximum of the top β-rank and the β-ranks of the two children. -/
theorem betaRankCode_app (op c0 c1 : ℕ) (hop : (Nat.unpair op).1 = 0) :
    betaRankCode (Nat.pair 1 (Nat.pair op (Nat.pair c0 (Nat.pair c1 0))))
      = max (topBetaRankCode (Nat.pair 1 (Nat.pair op (Nat.pair c0 (Nat.pair c1 0)))))
          (max (betaRankCode c0) (betaRankCode c1)) := by
  rw [betaRankCode]; split <;> simp_all [Nat.unpair_pair]

/-- The node equation of `betaRankCode` at an abstraction node (operation kind bit
`1`): the β-rank of the body child (an abstraction contributes no top β-rank). -/
theorem betaRankCode_lam (op c0 : ℕ) (hop : (Nat.unpair op).1 = 1) :
    betaRankCode (Nat.pair 1 (Nat.pair op (Nat.pair c0 0))) = betaRankCode c0 := by
  rw [betaRankCode]; split <;> simp_all [Nat.unpair_pair]

/-- The node equation of `betaRankCode` at an operation node whose kind bit is at
least `2` (a nullary constant): no β-rank. -/
theorem betaRankCode_op_ge_two (op pack : ℕ) (hop : 2 ≤ (Nat.unpair op).1) :
    betaRankCode (Nat.pair 1 (Nat.pair op pack)) = 0 := by
  rw [betaRankCode]; split <;> simp_all [Nat.unpair_pair]

/-- The β-rank mirror: reading `betaRankCode` off a term code agrees with the
term-level β-rank `betaRedexRank`. Structural induction on the term; the top β-rank
transfers by `topBetaRankCode_codeTm` and the child ranks by the induction
hypothesis, with the children maximum reconciled with the term-level `Finset.sup`. -/
theorem betaRankCode_codeTm {Γ : Binding.Ctx RType} {s : RType}
    (t : Binding.Tm (oneLambdaSig natAlgSig) Γ s) :
    betaRankCode (codeTm t) = betaRedexRank t := by
  suffices h : ∀ {y : Binding.Ctx RType × RType}
      (t : PolyFix (polyTranslate Binding.varOver (oneLambdaSig natAlgSig).polyEndo) y),
      betaRankCode (codeTm (Γ := y.1) (s := y.2) t)
        = betaRedexRank (Γ := y.1) (s := y.2) t from h t
  intro y t
  induction t with
  | mk y idx children ih =>
    cases idx with
    | inl a =>
      rw [show (PolyFix.mk y (Sum.inl a) children
            : Binding.Tm (oneLambdaSig natAlgSig) y.1 y.2)
            = Binding.Tm.var (Binding.leafVar a) from by
              obtain ⟨⟨Γ', i'⟩, rfl⟩ := a
              congr 1
              funext e
              exact e.elim]
      rw [codeTm_var, betaRankCode_var, betaRedexRank_var]
    | inr p =>
      obtain ⟨Γ', s'⟩ := y
      change { o : (oneLambdaSig natAlgSig).Op // (oneLambdaSig natAlgSig).result o = s' } at p
      revert children ih
      obtain ⟨o, rfl⟩ := p
      intro children ih
      rw [show (PolyFix.mk (Γ', (oneLambdaSig natAlgSig).result o) (Sum.inr ⟨o, rfl⟩) children
            : Binding.Tm (oneLambdaSig natAlgSig) Γ' ((oneLambdaSig natAlgSig).result o))
            = Binding.Tm.op (S := oneLambdaSig natAlgSig) o (fun j => children ⟨j⟩)
            from rfl]
      cases o with
      | app σ τ =>
          rw [betaRedexRank_op]
          refine Eq.trans (betaRankCode_app (codeOp (OneLambdaOp.app σ τ))
            (codeTm (children ⟨(0 : Fin 2)⟩)) (codeTm (children ⟨(1 : Fin 2)⟩))
            (by simp [codeOp, Nat.unpair_pair])) ?_
          congr 1
          · exact topBetaRankCode_codeTm (Binding.Tm.op (S := oneLambdaSig natAlgSig)
              (OneLambdaOp.app σ τ) (fun j => children ⟨j⟩))
          · change max (betaRankCode (codeTm (children ⟨(0 : Fin 2)⟩)))
                (betaRankCode (codeTm (children ⟨(1 : Fin 2)⟩)))
              = (Finset.univ : Finset (Fin 2)).sup (fun j => betaRedexRank (children ⟨j⟩))
            rw [show (Finset.univ : Finset (Fin 2)) = {0, 1} from rfl,
              Finset.sup_insert, Finset.sup_singleton]
            exact congrArg₂ max (ih ⟨(0 : Fin 2)⟩) (ih ⟨(1 : Fin 2)⟩)
      | lam σ τ =>
          rw [betaRedexRank_op,
            show topBetaRank (Binding.Tm.op (S := oneLambdaSig natAlgSig)
              (OneLambdaOp.lam σ τ) (fun j => children ⟨j⟩)) = 0 from by rw [topBetaRank_op]; rfl]
          refine Eq.trans (betaRankCode_lam (codeOp (OneLambdaOp.lam σ τ))
            (codeTm (children ⟨(0 : Fin 1)⟩)) (by simp [codeOp, Nat.unpair_pair])) ?_
          change betaRankCode (codeTm (children ⟨(0 : Fin 1)⟩))
            = max 0 ((Finset.univ : Finset (Fin 1)).sup (fun j => betaRedexRank (children ⟨j⟩)))
          rw [show (Finset.univ : Finset (Fin 1)) = {0} from rfl, Finset.sup_singleton,
            Nat.zero_max]
          exact ih ⟨(0 : Fin 1)⟩
      | con b =>
          rw [codeTm_op, betaRankCode_op_ge_two _ _ (by simp [codeOp, Nat.unpair_pair]),
            betaRedexRank_op,
            show topBetaRank (Binding.Tm.op (S := oneLambdaSig natAlgSig)
              (OneLambdaOp.con b) (fun j => children ⟨j⟩)) = 0 from by rw [topBetaRank_op]; rfl]
          change (0 : ℕ) = max 0 ((Finset.univ : Finset (Fin 0)).sup _)
          simp [Finset.univ_eq_empty]
      | dstr j =>
          rw [codeTm_op, betaRankCode_op_ge_two _ _ (by simp [codeOp, Nat.unpair_pair]),
            betaRedexRank_op,
            show topBetaRank (Binding.Tm.op (S := oneLambdaSig natAlgSig)
              (OneLambdaOp.dstr j) (fun k => children ⟨k⟩)) = 0 from by rw [topBetaRank_op]; rfl]
          change (0 : ℕ) = max 0 ((Finset.univ : Finset (Fin 0)).sup _)
          simp [Finset.univ_eq_empty]
      | case =>
          rw [codeTm_op, betaRankCode_op_ge_two _ _ (by simp [codeOp, Nat.unpair_pair]),
            betaRedexRank_op,
            show topBetaRank (Binding.Tm.op (S := oneLambdaSig natAlgSig)
              OneLambdaOp.case (fun j => children ⟨j⟩)) = 0 from by rw [topBetaRank_op]; rfl]
          change (0 : ℕ) = max 0 ((Finset.univ : Finset (Fin 0)).sup _)
          simp [Finset.univ_eq_empty]

set_option linter.unusedVariables false in
/-- The code-level image of the ι-redex census `hasIota`: strong recursion on the
code disjoining the top ι-redex detector `topIotaCode` with the ι-redex census of
the child codes. An application node (operation kind bit `0`) disjoins over both
children; an abstraction node (kind bit `1`) recurses into its body child; every
other node is `false`. Novel realization. The `linter.unusedVariables` disable
covers the `match`-bound discriminant equation, referenced only in the termination
proof. -/
def hasIotaCode (c : ℕ) : Bool :=
  match h : (Nat.unpair c).1, (Nat.unpair (Nat.unpair (Nat.unpair c).2).1).1 with
  | 1, 0 =>
      topIotaCode c || hasIotaCode (Nat.unpair (Nat.unpair (Nat.unpair c).2).2).1
        || hasIotaCode (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair c).2).2).2).1
  | 1, 1 => hasIotaCode (Nat.unpair (Nat.unpair (Nat.unpair c).2).2).1
  | _, _ => false
  termination_by c
  decreasing_by
    all_goals
      have key : (Nat.unpair c).2 < c := by
        conv_rhs => rw [← Nat.pair_unpair c, h]
        exact self_lt_pair_one _
      first
      | exact Nat.lt_of_le_of_lt
          (le_trans (Nat.unpair_left_le _) (Nat.unpair_right_le _)) key
      | exact Nat.lt_of_le_of_lt
          (le_trans (le_trans (Nat.unpair_left_le _) (Nat.unpair_right_le _))
            (Nat.unpair_right_le _)) key

/-- The node equation of `hasIotaCode` at a variable leaf `Nat.pair 0 i`. -/
theorem hasIotaCode_var (i : ℕ) : hasIotaCode (Nat.pair 0 i) = false := by
  rw [hasIotaCode]; split <;> simp_all [Nat.unpair_pair]

/-- The node equation of `hasIotaCode` at an application node (operation kind bit
`0`): the top ι-redex detector disjoined with the census of both children. -/
theorem hasIotaCode_app (op c0 c1 : ℕ) (hop : (Nat.unpair op).1 = 0) :
    hasIotaCode (Nat.pair 1 (Nat.pair op (Nat.pair c0 (Nat.pair c1 0))))
      = (topIotaCode (Nat.pair 1 (Nat.pair op (Nat.pair c0 (Nat.pair c1 0))))
          || hasIotaCode c0 || hasIotaCode c1) := by
  rw [hasIotaCode]; split <;> simp_all [Nat.unpair_pair]

/-- The node equation of `hasIotaCode` at an abstraction node (operation kind bit
`1`): the census of the body child (an abstraction is not an ι-redex). -/
theorem hasIotaCode_lam (op c0 : ℕ) (hop : (Nat.unpair op).1 = 1) :
    hasIotaCode (Nat.pair 1 (Nat.pair op (Nat.pair c0 0))) = hasIotaCode c0 := by
  rw [hasIotaCode]; split <;> simp_all [Nat.unpair_pair]

/-- The node equation of `hasIotaCode` at an operation node whose kind bit is at
least `2` (a nullary constant): no ι-redex. -/
theorem hasIotaCode_op_ge_two (op pack : ℕ) (hop : 2 ≤ (Nat.unpair op).1) :
    hasIotaCode (Nat.pair 1 (Nat.pair op pack)) = false := by
  rw [hasIotaCode]; split <;> simp_all [Nat.unpair_pair]

/-- The ι-census mirror: reading `hasIotaCode` off a term code agrees with the
term-level ι-redex census `hasIota`. Structural induction on the term; the top
ι-redex detector transfers by `topIotaCode_codeTm` and the child censuses by the
induction hypothesis. -/
theorem hasIotaCode_codeTm {Γ : Binding.Ctx RType} {s : RType}
    (t : Binding.Tm (oneLambdaSig natAlgSig) Γ s) :
    hasIotaCode (codeTm t) = hasIota t := by
  suffices h : ∀ {y : Binding.Ctx RType × RType}
      (t : PolyFix (polyTranslate Binding.varOver (oneLambdaSig natAlgSig).polyEndo) y),
      hasIotaCode (codeTm (Γ := y.1) (s := y.2) t)
        = hasIota (Γ := y.1) (s := y.2) t from h t
  intro y t
  induction t with
  | mk y idx children ih =>
    cases idx with
    | inl a =>
      rw [show (PolyFix.mk y (Sum.inl a) children
            : Binding.Tm (oneLambdaSig natAlgSig) y.1 y.2)
            = Binding.Tm.var (Binding.leafVar a) from by
              obtain ⟨⟨Γ', i'⟩, rfl⟩ := a
              congr 1
              funext e
              exact e.elim]
      rw [codeTm_var, hasIotaCode_var, hasIota_var]
    | inr p =>
      obtain ⟨Γ', s'⟩ := y
      change { o : (oneLambdaSig natAlgSig).Op // (oneLambdaSig natAlgSig).result o = s' } at p
      revert children ih
      obtain ⟨o, rfl⟩ := p
      intro children ih
      rw [show (PolyFix.mk (Γ', (oneLambdaSig natAlgSig).result o) (Sum.inr ⟨o, rfl⟩) children
            : Binding.Tm (oneLambdaSig natAlgSig) Γ' ((oneLambdaSig natAlgSig).result o))
            = Binding.Tm.op (S := oneLambdaSig natAlgSig) o (fun j => children ⟨j⟩)
            from rfl]
      cases o with
      | app σ τ =>
          have hsup : (Finset.univ.sup (fun j => hasIota (children ⟨j⟩)) : Bool)
              = (hasIota (children ⟨(0 : Fin 2)⟩) || hasIota (children ⟨(1 : Fin 2)⟩)) := by
            change (Finset.univ : Finset (Fin 2)).sup _ = _
            rw [show (Finset.univ : Finset (Fin 2)) = {0, 1} from rfl,
              Finset.sup_insert, Finset.sup_singleton]
            rfl
          rw [hasIota_op, hsup]
          refine Eq.trans (hasIotaCode_app (codeOp (OneLambdaOp.app σ τ))
            (codeTm (children ⟨(0 : Fin 2)⟩)) (codeTm (children ⟨(1 : Fin 2)⟩))
            (by simp [codeOp, Nat.unpair_pair])) ?_
          rw [Bool.or_assoc]
          exact congrArg₂ (· || ·)
            (topIotaCode_codeTm (Binding.Tm.op (S := oneLambdaSig natAlgSig)
              (OneLambdaOp.app σ τ) (fun j => children ⟨j⟩)))
            (congrArg₂ (· || ·) (ih ⟨(0 : Fin 2)⟩) (ih ⟨(1 : Fin 2)⟩))
      | lam σ τ =>
          have hsup : (Finset.univ.sup (fun j => hasIota (children ⟨j⟩)) : Bool)
              = hasIota (children ⟨(0 : Fin 1)⟩) := by
            change (Finset.univ : Finset (Fin 1)).sup _ = _
            rw [show (Finset.univ : Finset (Fin 1)) = {0} from rfl, Finset.sup_singleton]
          rw [hasIota_op, hsup,
            show topIota (Binding.Tm.op (S := oneLambdaSig natAlgSig)
              (OneLambdaOp.lam σ τ) (fun j => children ⟨j⟩)) = false from by
                simp only [topIota, iotaSpine_op, iotaSpineOp, ite_self],
            Bool.false_or]
          refine Eq.trans (hasIotaCode_lam (codeOp (OneLambdaOp.lam σ τ))
            (codeTm (children ⟨(0 : Fin 1)⟩)) (by simp [codeOp, Nat.unpair_pair])) ?_
          exact ih ⟨(0 : Fin 1)⟩
      | con b =>
          rw [codeTm_op, hasIotaCode_op_ge_two _ _ (by simp [codeOp, Nat.unpair_pair]),
            hasIota_op,
            show topIota (Binding.Tm.op (S := oneLambdaSig natAlgSig)
              (OneLambdaOp.con b) (fun j => children ⟨j⟩)) = false from by
                simp only [topIota, iotaSpine_op, iotaSpineOp, ite_self]]
          change (false : Bool) = (false || (Finset.univ : Finset (Fin 0)).sup _)
          simp [Finset.univ_eq_empty]
      | dstr j =>
          rw [codeTm_op, hasIotaCode_op_ge_two _ _ (by simp [codeOp, Nat.unpair_pair]),
            hasIota_op,
            show topIota (Binding.Tm.op (S := oneLambdaSig natAlgSig)
              (OneLambdaOp.dstr j) (fun k => children ⟨k⟩)) = false from by
                simp only [topIota, iotaSpine_op, iotaSpineOp, ite_self]]
          change (false : Bool) = (false || (Finset.univ : Finset (Fin 0)).sup _)
          simp [Finset.univ_eq_empty]
      | case =>
          rw [codeTm_op, hasIotaCode_op_ge_two _ _ (by simp [codeOp, Nat.unpair_pair]),
            hasIota_op,
            show topIota (Binding.Tm.op (S := oneLambdaSig natAlgSig)
              OneLambdaOp.case (fun j => children ⟨j⟩)) = false from by
                simp only [topIota, iotaSpine_op, iotaSpineOp, ite_self]]
          change (false : Bool) = (false || (Finset.univ : Finset (Fin 0)).sup _)
          simp [Finset.univ_eq_empty]

/-- The code-level image of the normal-form predicate `Normal`: a code is normal
when its β-rank is `0` and it carries no ι-redex. Novel realization. -/
def normalCode (c : ℕ) : Bool := (betaRankCode c == 0) && !hasIotaCode c

/-- The normality mirror: the code-level normal-form detector holds exactly when
the term is `Normal`. By the β-rank and ι-census mirrors together with
`normal_iff`. -/
theorem normalCode_codeTm {Γ : Binding.Ctx RType} {s : RType}
    (t : Binding.Tm (oneLambdaSig natAlgSig) Γ s) :
    normalCode (codeTm t) = true ↔ Normal t := by
  rw [normalCode, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq,
    betaRankCode_codeTm, hasIotaCode_codeTm, normal_iff]

end OneLambda

end GebLean.Ramified
