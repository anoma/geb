import GebLean.Ramified.Soundness.CodeTm

/-!
# Ramified recurrence: code-level substitution

The code-level image of single-variable substitution on the terms of the
simply-typed calculus `1λ(natAlgSig)` (Leivant III section 4.2), opening the
realization layer of the deterministic normalizer. `subCode j e` is the numeric
shadow of `Binding.instantiate₁`: it rewrites the Gödel code `codeTm d` of a
body into the code of the reduct `codeTm (instantiate₁ e d)`, working purely on
the `Nat.pair` numerals with `codeTm e` supplied as the substituend code.

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
well-founded recursion, term code
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

/-- The children pack of a binary node: `List.foldr Nat.pair 0` over a
two-element tuple is the right-nested pair closed by the terminator. -/
private theorem foldrPack_two (f : Fin 2 → ℕ) :
    List.foldr Nat.pair 0 (List.ofFn f) = Nat.pair (f 0) (Nat.pair (f 1) 0) := rfl

/-- The children pack of a unary node: `List.foldr Nat.pair 0` over a
one-element tuple is the sole entry closed by the terminator. -/
private theorem foldrPack_one (f : Fin 1 → ℕ) :
    List.foldr Nat.pair 0 (List.ofFn f) = Nat.pair (f 0) 0 := rfl

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

end OneLambda

end GebLean.Ramified
