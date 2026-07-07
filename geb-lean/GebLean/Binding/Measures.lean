import GebLean.Binding.Laws
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Term measures

Signature-agnostic size and height measures on the terms of an indexed
binder-substitution kit (decision 8). `Tm.size` counts nodes; `Tm.height` is
the tree height in the standard `1 + max`-over-children form, with an empty
maximum of `0`, so a leaf (a variable) and a nullary operation both have size
and height `1`. Both are folds by the dependent eliminator `PolyFix.ind`,
following `barTy`'s pattern, summing over the `Fin`-indexed children with
`∑ j, …` and maxing with `Finset.univ.sup`. Renaming preserves both measures,
since it is structure-preserving on the operation tree.

## Main definitions

* `Tm.size` — the node count of a term.
* `Tm.height` — the tree height of a term (`1 + max` over children).

## Main statements

* `Tm.size_var`, `Tm.size_op` — the fold equations for `Tm.size`.
* `Tm.height_var`, `Tm.height_op` — the fold equations for `Tm.height`.
* `Tm.one_le_size`, `Tm.one_le_height` — positivity of both measures.
* `Tm.height_le_size` — the height bounds the size.
* `Tm.size_cast`, `Tm.height_cast` — invariance under transport of the
  context and sort indices.
* `Tm.size_ren`, `Tm.height_ren` — invariance under renaming.
* `Tm.height_sub_le`, `Tm.size_sub_le` — the substitution bounds: substituting
  along an environment whose images are measure-bounded raises the height
  additively and the size multiplicatively by that bound.
* `Tm.height_instantiate₁_le`, `Tm.size_instantiate₁_le` — the single-variable
  specializations, bounding a beta/destructor reduction's measures.
* `Tm.size_le_pow_height` — the arity inequality: the size is bounded by an
  arity bound raised to the height.

## References

The tree height in the `1 + max`-over-children form is D. Leivant, "Ramified
recurrence and computational complexity III: Higher type recurrence and
elementary complexity", Annals of Pure and Applied Logic 96 (1999) 209-229,
DOI `10.1016/S0168-0072(98)00040-2`, section 2.1, p. 211. The substitution
bounds and the arity inequality are the kit-level facts consumed by the same
work's section 5, proof paragraph (ii), p. 226. The binder-signature
conventions follow G. Allais, R. Atkey, J. Chapman, C. McBride, and J. McKinna,
"A type and scope safe universe of syntaxes with binding: their semantics and
proofs", Proceedings of the ACM on Programming Languages 2 (ICFP), 2018,
DOI `10.1145/3236785`.

## Tags

term measure, size, height, binder, de Bruijn
-/

namespace GebLean.Binding

open CategoryTheory

universe u

variable {Ty : Type u}

/-- The node count of a term: a variable counts `1`, and an operation node
counts `1` plus the sum of the counts of its arguments. Novel packaging of the
standard tree size in the kit; a fold by `PolyFix.ind` following `barTy`. -/
def Tm.size {S : BinderSig Ty} {Γ : Ctx Ty} {s : Ty} (t : Tm S Γ s) : ℕ :=
  PolyFix.ind (P := polyTranslate varOver S.polyEndo) (motive := fun {_} _ => ℕ)
    (fun i children ih =>
      match i, children, ih with
      | Sum.inl _, _, _ => 1
      | Sum.inr p, _, ih => 1 + Finset.univ.sum fun j : Fin (S.args p.val).length => ih ⟨j⟩) t

/-- The tree height of a term in the `1 + max`-over-children form (Leivant III
section 2.1, p. 211): a variable has height `1`, and an operation node has
height `1` plus the maximum of the heights of its arguments, the empty maximum
being `0`. A fold by `PolyFix.ind` following `barTy`. -/
def Tm.height {S : BinderSig Ty} {Γ : Ctx Ty} {s : Ty} (t : Tm S Γ s) : ℕ :=
  PolyFix.ind (P := polyTranslate varOver S.polyEndo) (motive := fun {_} _ => ℕ)
    (fun i children ih =>
      match i, children, ih with
      | Sum.inl _, _, _ => 1
      | Sum.inr p, _, ih =>
        1 + Finset.univ.sup fun j : Fin (S.args p.val).length => ih ⟨j⟩) t

/-- The size of a variable term is `1`. -/
@[simp] theorem Tm.size_var {S : BinderSig Ty} {Γ : Ctx Ty} {s : Ty} (x : Var Γ s) :
    (Tm.var x : Tm S Γ s).size = 1 := by
  obtain ⟨i, hi⟩ := x
  subst hi
  rfl

/-- The size of an operation node is `1` plus the sum of the sizes of its
arguments. -/
@[simp] theorem Tm.size_op {S : BinderSig Ty} {Γ : Ctx Ty} (o : S.Op)
    (args : ∀ j : Fin (S.args o).length,
      Tm S (Γ ++ ((S.args o).get j).1) ((S.args o).get j).2) :
    (Tm.op o args).size = 1 + ∑ j, (args j).size := rfl

/-- The height of a variable term is `1`. -/
@[simp] theorem Tm.height_var {S : BinderSig Ty} {Γ : Ctx Ty} {s : Ty} (x : Var Γ s) :
    (Tm.var x : Tm S Γ s).height = 1 := by
  obtain ⟨i, hi⟩ := x
  subst hi
  rfl

/-- The height of an operation node is `1` plus the maximum of the heights of
its arguments. -/
@[simp] theorem Tm.height_op {S : BinderSig Ty} {Γ : Ctx Ty} (o : S.Op)
    (args : ∀ j : Fin (S.args o).length,
      Tm S (Γ ++ ((S.args o).get j).1) ((S.args o).get j).2) :
    (Tm.op o args).height = 1 + Finset.univ.sup fun j => (args j).height := rfl

/-- Both measures ignore transport of a term across an equality of its context
and sort indices; stated for `size`. Consumed by the `app'`/`lam'` measure
equations. -/
theorem Tm.size_cast {S : BinderSig Ty} {Γ Γ' : Ctx Ty} {s s' : Ty}
    (hΓ : Γ = Γ') (hs : s = s') (t : Tm S Γ s) :
    (hs ▸ hΓ ▸ t : Tm S Γ' s').size = t.size := by
  subst hΓ; subst hs; rfl

/-- Both measures ignore transport of a term across an equality of its context
and sort indices; stated for `height`. -/
theorem Tm.height_cast {S : BinderSig Ty} {Γ Γ' : Ctx Ty} {s s' : Ty}
    (hΓ : Γ = Γ') (hs : s = s') (t : Tm S Γ s) :
    (hs ▸ hΓ ▸ t : Tm S Γ' s').height = t.height := by
  subst hΓ; subst hs; rfl

/-- Every term has size at least `1`. -/
theorem Tm.one_le_size {S : BinderSig Ty} {Γ : Ctx Ty} {s : Ty} (t : Tm S Γ s) :
    1 ≤ t.size := by
  suffices h : ∀ {y : Ctx Ty × Ty} (t : PolyFix (polyTranslate varOver S.polyEndo) y),
      1 ≤ Tm.size (S := S) (Γ := y.1) (s := y.2) t from h t
  intro y t
  induction t with
  | mk y i children ih =>
    cases i with
    | inl _ => exact Nat.le_refl 1
    | inr _ => exact Nat.le_add_right 1 _

/-- Every term has height at least `1`. -/
theorem Tm.one_le_height {S : BinderSig Ty} {Γ : Ctx Ty} {s : Ty} (t : Tm S Γ s) :
    1 ≤ t.height := by
  suffices h : ∀ {y : Ctx Ty × Ty} (t : PolyFix (polyTranslate varOver S.polyEndo) y),
      1 ≤ Tm.height (S := S) (Γ := y.1) (s := y.2) t from h t
  intro y t
  induction t with
  | mk y i children ih =>
    cases i with
    | inl _ => exact Nat.le_refl 1
    | inr _ => exact Nat.le_add_right 1 _

/-- The height of a term bounds its size. -/
theorem Tm.height_le_size {S : BinderSig Ty} {Γ : Ctx Ty} {s : Ty} (t : Tm S Γ s) :
    t.height ≤ t.size := by
  suffices h : ∀ {y : Ctx Ty × Ty} (t : PolyFix (polyTranslate varOver S.polyEndo) y),
      Tm.height (S := S) (Γ := y.1) (s := y.2) t
        ≤ Tm.size (S := S) (Γ := y.1) (s := y.2) t from h t
  intro y t
  induction t with
  | mk y i children ih =>
    cases i with
    | inl _ => exact Nat.le_refl 1
    | inr p =>
      refine Nat.add_le_add_left (Finset.sup_le fun j _ => ?_) 1
      exact (ih ⟨j⟩).trans
        (Finset.single_le_sum
          (f := fun k : Fin (S.args p.val).length => Tm.size (children ⟨k⟩))
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ j))

/-- Renaming along a thinning preserves the size: a renaming is
structure-preserving on the operation tree. -/
@[simp] theorem Tm.size_ren {S : BinderSig Ty} {Γ Δ : Ctx Ty} {s : Ty}
    (ρ : Thinning Γ Δ) (t : Tm S Γ s) : (ren ρ t).size = t.size := by
  suffices h : ∀ {y : Ctx Ty × Ty} (t : PolyFix (polyTranslate varOver S.polyEndo) y)
      {Δ : Ctx Ty} (ρ : Thinning y.1 Δ),
      Tm.size (S := S) (Γ := Δ) (traverse (varKit S) (renEnv ρ) t)
        = Tm.size (S := S) (Γ := y.1) (s := y.2) t from h t ρ
  intro y t
  induction t with
  | mk y idx children ih =>
    intro Δ ρ
    cases idx with
    | inl a =>
      rw [show (PolyFix.mk y (Sum.inl a) children : Tm S y.1 y.2)
            = Tm.var (leafVar a) from by
              obtain ⟨⟨Γ', i'⟩, rfl⟩ := a
              congr 1
              funext e
              exact e.elim]
      simp only [traverse_var, varKit, renEnv, Tm.size_var]
    | inr p =>
      obtain ⟨Γ', s'⟩ := y
      change { o : S.Op // S.result o = s' } at p
      revert children ih
      obtain ⟨o, rfl⟩ := p
      intro children ih
      rw [show (PolyFix.mk (Γ', S.result o) (Sum.inr ⟨o, rfl⟩) children
            : Tm S Γ' (S.result o))
            = Tm.op o (fun j => children ⟨j⟩) from rfl]
      rw [traverse_op, Tm.size_op, Tm.size_op]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [underBinder_renEnv]
      exact ih ⟨j⟩ (Thinning.appendId ρ _)

/-- Renaming along a thinning preserves the height: a renaming is
structure-preserving on the operation tree. -/
@[simp] theorem Tm.height_ren {S : BinderSig Ty} {Γ Δ : Ctx Ty} {s : Ty}
    (ρ : Thinning Γ Δ) (t : Tm S Γ s) : (ren ρ t).height = t.height := by
  suffices h : ∀ {y : Ctx Ty × Ty} (t : PolyFix (polyTranslate varOver S.polyEndo) y)
      {Δ : Ctx Ty} (ρ : Thinning y.1 Δ),
      Tm.height (S := S) (Γ := Δ) (traverse (varKit S) (renEnv ρ) t)
        = Tm.height (S := S) (Γ := y.1) (s := y.2) t from h t ρ
  intro y t
  induction t with
  | mk y idx children ih =>
    intro Δ ρ
    cases idx with
    | inl a =>
      rw [show (PolyFix.mk y (Sum.inl a) children : Tm S y.1 y.2)
            = Tm.var (leafVar a) from by
              obtain ⟨⟨Γ', i'⟩, rfl⟩ := a
              congr 1
              funext e
              exact e.elim]
      simp only [traverse_var, varKit, renEnv, Tm.height_var]
    | inr p =>
      obtain ⟨Γ', s'⟩ := y
      change { o : S.Op // S.result o = s' } at p
      revert children ih
      obtain ⟨o, rfl⟩ := p
      intro children ih
      rw [show (PolyFix.mk (Γ', S.result o) (Sum.inr ⟨o, rfl⟩) children
            : Tm S Γ' (S.result o))
            = Tm.op o (fun j => children ⟨j⟩) from rfl]
      rw [traverse_op, Tm.height_op, Tm.height_op]
      congr 1
      refine Finset.sup_congr rfl fun j _ => ?_
      rw [underBinder_renEnv]
      exact ih ⟨j⟩ (Thinning.appendId ρ _)

/-- The append-variable eliminator falls within a common `ℕ`-bound: if both the
suffix branch `fromΞ` and the prefix branch `fromΓ` are bounded by `c`, so is the
eliminator's result. Recursion on the prefix `Γ`, mirroring `Var.appendCases`.
Novel; consumed by the under-binder measure bounds of the substitution lemmas and
by the instantiation corollaries. -/
theorem Var.appendCases_le {Ξ : Ctx Ty} {s : Ty} {c : ℕ}
    (fromΞ : Var Ξ s → ℕ) (hΞ : ∀ y, fromΞ y ≤ c) :
    (Γ : Ctx Ty) → (fromΓ : Var Γ s → ℕ) → (∀ v, fromΓ v ≤ c) →
      (x : Var (Γ ++ Ξ) s) → Var.appendCases fromΞ Γ fromΓ x ≤ c
  | [], _, _, x => hΞ x
  | a :: Γ, fromΓ, hΓ, ⟨i, hi⟩ => by
      cases i using Fin.cases with
      | zero => exact hΓ ⟨0, hi⟩
      | succ i' =>
          exact Var.appendCases_le fromΞ hΞ Γ (fun v => fromΓ (Var.succ a v))
            (fun v => hΓ (Var.succ a v)) ⟨i', hi⟩

/-- The substitution bound on height: substituting along an environment `σ` whose
images all have height at most `H` (with `1 ≤ H`) raises the height by at most `H`
(Leivant III section 5, proof paragraph (ii), p. 226). Proved by the kit's
substitution induction; the binder case feeds the induction hypothesis the
under-binder environment, whose fresh images are variables (height `1 ≤ H`) and
whose old images are renamings (height preserved by `Tm.height_ren`). The
environment-generalized form is novel packaging. -/
theorem Tm.height_sub_le {Ty : Type} {S : BinderSig Ty} {Γ Δ : Ctx Ty} {s : Ty}
    (σ : Env (Tm S) Γ Δ) (t : Tm S Γ s) {H : ℕ} (hH : 1 ≤ H)
    (hσ : ∀ u (x : Var Γ u), (σ u x).height ≤ H) :
    (sub σ t).height ≤ t.height + H := by
  suffices h : ∀ {y : Ctx Ty × Ty} (t : PolyFix (polyTranslate varOver S.polyEndo) y)
      {Δ : Ctx Ty} (σ : Env (Tm S) y.1 Δ),
      (∀ u (x : Var y.1 u), Tm.height (σ u x) ≤ H) →
      Tm.height (S := S) (Γ := Δ) (traverse (subKit S) σ t)
        ≤ Tm.height (S := S) (Γ := y.1) (s := y.2) t + H by
    exact h t σ hσ
  intro y t
  induction t with
  | mk y idx children ih =>
    intro Δ σ hσ
    cases idx with
    | inl a =>
      rw [show (PolyFix.mk y (Sum.inl a) children : Tm S y.1 y.2)
            = Tm.var (leafVar a) from by
              obtain ⟨⟨Γ', i'⟩, rfl⟩ := a
              congr 1
              funext e
              exact e.elim]
      rw [traverse_var, Tm.height_var]
      simp only [subKit, id]
      exact le_trans (hσ y.2 (leafVar a)) (Nat.le_add_left H 1)
    | inr p =>
      obtain ⟨Γ', s'⟩ := y
      change { o : S.Op // S.result o = s' } at p
      revert children ih
      obtain ⟨o, rfl⟩ := p
      intro children ih
      rw [show (PolyFix.mk (Γ', S.result o) (Sum.inr ⟨o, rfl⟩) children
            : Tm S Γ' (S.result o))
            = Tm.op o (fun j => children ⟨j⟩) from rfl]
      simp only [traverse_op, Tm.height_op]
      rw [Nat.add_assoc]
      apply Nat.add_le_add_left
      apply Finset.sup_le
      intro j _
      have hbound :
          Tm.height (traverse (subKit S) (Env.underBinder (subKit S) σ) (children ⟨j⟩))
            ≤ Tm.height (children ⟨j⟩) + H := by
        apply ih ⟨j⟩
        intro u x
        simp only [Env.underBinder, subKit]
        rw [Var.appendCases_natural Tm.height]
        apply Var.appendCases_le
        · intro y; rw [Tm.height_var]; exact hH
        · intro v; rw [Tm.height_ren]; exact hσ u v
      refine le_trans hbound (Nat.add_le_add_right ?_ H)
      exact Finset.le_sup (f := fun k => Tm.height (children ⟨k⟩)) (Finset.mem_univ j)

/-- The substitution bound on size: substituting along an environment `σ` whose
images all have size at most `N` (with `1 ≤ N`) multiplies the size by at most `N`
(Leivant III section 5, proof paragraph (ii), p. 226). Proved by the kit's
substitution induction; the binder case feeds the induction hypothesis the
under-binder environment, whose fresh images are variables (size `1 ≤ N`) and
whose old images are renamings (size preserved by `Tm.size_ren`). The
environment-generalized form is novel packaging. -/
theorem Tm.size_sub_le {Ty : Type} {S : BinderSig Ty} {Γ Δ : Ctx Ty} {s : Ty}
    (σ : Env (Tm S) Γ Δ) (t : Tm S Γ s) {N : ℕ} (hN : 1 ≤ N)
    (hσ : ∀ u (x : Var Γ u), (σ u x).size ≤ N) :
    (sub σ t).size ≤ t.size * N := by
  suffices h : ∀ {y : Ctx Ty × Ty} (t : PolyFix (polyTranslate varOver S.polyEndo) y)
      {Δ : Ctx Ty} (σ : Env (Tm S) y.1 Δ),
      (∀ u (x : Var y.1 u), Tm.size (σ u x) ≤ N) →
      Tm.size (S := S) (Γ := Δ) (traverse (subKit S) σ t)
        ≤ Tm.size (S := S) (Γ := y.1) (s := y.2) t * N by
    exact h t σ hσ
  intro y t
  induction t with
  | mk y idx children ih =>
    intro Δ σ hσ
    cases idx with
    | inl a =>
      rw [show (PolyFix.mk y (Sum.inl a) children : Tm S y.1 y.2)
            = Tm.var (leafVar a) from by
              obtain ⟨⟨Γ', i'⟩, rfl⟩ := a
              congr 1
              funext e
              exact e.elim]
      rw [traverse_var, Tm.size_var]
      simp only [subKit, id, Nat.one_mul]
      exact hσ y.2 (leafVar a)
    | inr p =>
      obtain ⟨Γ', s'⟩ := y
      change { o : S.Op // S.result o = s' } at p
      revert children ih
      obtain ⟨o, rfl⟩ := p
      intro children ih
      rw [show (PolyFix.mk (Γ', S.result o) (Sum.inr ⟨o, rfl⟩) children
            : Tm S Γ' (S.result o))
            = Tm.op o (fun j => children ⟨j⟩) from rfl]
      simp only [traverse_op, Tm.size_op]
      have hbound : ∀ j : Fin (S.args o).length,
          Tm.size (traverse (subKit S) (Env.underBinder (subKit S) σ) (children ⟨j⟩))
            ≤ Tm.size (children ⟨j⟩) * N := by
        intro j
        apply ih ⟨j⟩
        intro u x
        simp only [Env.underBinder, subKit]
        rw [Var.appendCases_natural Tm.size]
        apply Var.appendCases_le
        · intro y; rw [Tm.size_var]; exact hN
        · intro v; rw [Tm.size_ren]; exact hσ u v
      have hsum :
          (∑ j, Tm.size (traverse (subKit S) (Env.underBinder (subKit S) σ) (children ⟨j⟩)))
            ≤ ∑ j, Tm.size (children ⟨j⟩) * N := Finset.sum_le_sum fun j _ => hbound j
      calc 1 + (∑ j, Tm.size (traverse (subKit S) (Env.underBinder (subKit S) σ) (children ⟨j⟩)))
          ≤ 1 + ∑ j, Tm.size (children ⟨j⟩) * N := Nat.add_le_add_left hsum 1
        _ ≤ (1 + ∑ j, Tm.size (children ⟨j⟩)) * N := by
            rw [Nat.add_mul, Nat.one_mul, Finset.sum_mul]
            exact Nat.add_le_add_right hN _

/-- The single-variable substitution bound on height: instantiating the sole
bound variable of a body `b` by a term `N` raises the height by at most `N`'s
height (Leivant III section 5, proof paragraph (ii), p. 226). The corollary of
`Tm.height_sub_le` at the instantiating environment, whose new image is `N`
(height `N.height`) and whose old images are variables (height `1 ≤ N.height`). -/
theorem Tm.height_instantiate₁_le {Ty : Type} {S : BinderSig Ty} {Γ : Ctx Ty} {a s : Ty}
    (N : Tm S Γ a) (b : Tm S (Γ ++ [a]) s) :
    (instantiate₁ N b).height ≤ b.height + N.height := by
  unfold instantiate₁ instantiate
  refine Tm.height_sub_le _ b (Tm.one_le_height N) ?_
  intro u x
  rw [extendEnv_apply, Var.appendCases_natural Tm.height]
  apply Var.appendCases_le
  · intro w
    obtain ⟨i, hi⟩ := w
    cases i using Fin.cases with
    | zero => exact le_of_eq (Tm.height_cast rfl hi N)
    | succ j => exact j.elim0
  · intro v
    simp only [idEnv, Tm.height_var]
    exact Tm.one_le_height N

/-- The single-variable substitution bound on size: instantiating the sole bound
variable of a body `b` by a term `N` multiplies the size by at most `N`'s size
(Leivant III section 5, proof paragraph (ii), p. 226). The corollary of
`Tm.size_sub_le` at the instantiating environment, whose new image is `N` (size
`N.size`) and whose old images are variables (size `1 ≤ N.size`). -/
theorem Tm.size_instantiate₁_le {Ty : Type} {S : BinderSig Ty} {Γ : Ctx Ty} {a s : Ty}
    (N : Tm S Γ a) (b : Tm S (Γ ++ [a]) s) :
    (instantiate₁ N b).size ≤ b.size * N.size := by
  unfold instantiate₁ instantiate
  refine Tm.size_sub_le _ b (Tm.one_le_size N) ?_
  intro u x
  rw [extendEnv_apply, Var.appendCases_natural Tm.size]
  apply Var.appendCases_le
  · intro w
    obtain ⟨i, hi⟩ := w
    cases i using Fin.cases with
    | zero => exact le_of_eq (Tm.size_cast rfl hi N)
    | succ j => exact j.elim0
  · intro v
    simp only [idEnv, Tm.size_var]
    exact Tm.one_le_size N

/-- The arity inequality: a term's size is bounded by an arity bound `m` (with
`2 ≤ m` and `(S.args o).length ≤ m` for every operation `o`) raised to its height
(Leivant III section 5, proof paragraph (ii), p. 226; for the one-lambda
signature `oneLambdaSig`, `m = 2`, so `size ≤ 2 ^ height`). Proved from the
strengthened form `size t + 1 ≤ m ^ height t`, which closes the induction where
the direct `size t ≤ m ^ height t` does not: a node with `k ≤ m` children of
size at most `m ^ h - 1` and height at most `h` has size at most
`1 + m * (m ^ h - 1) ≤ m ^ (h + 1) - 1` for `m ≥ 2`. -/
theorem Tm.size_le_pow_height {Ty : Type} {S : BinderSig Ty} {Γ : Ctx Ty} {s : Ty}
    (t : Tm S Γ s) {m : ℕ} (hm : 2 ≤ m) (harity : ∀ o : S.Op, (S.args o).length ≤ m) :
    t.size ≤ m ^ t.height := by
  suffices h : ∀ {y : Ctx Ty × Ty} (t : PolyFix (polyTranslate varOver S.polyEndo) y),
      Tm.size (S := S) (Γ := y.1) (s := y.2) t + 1
        ≤ m ^ Tm.height (S := S) (Γ := y.1) (s := y.2) t by
    have ht := h t
    omega
  intro y t
  induction t with
  | mk y i children ih =>
    cases i with
    | inl a =>
      change (1 : ℕ) + 1 ≤ m ^ 1
      rw [pow_one]
      omega
    | inr p =>
      obtain ⟨Γ', s'⟩ := y
      change { o : S.Op // S.result o = s' } at p
      revert children ih
      obtain ⟨o, rfl⟩ := p
      intro children ih
      rw [show (PolyFix.mk (Γ', S.result o) (Sum.inr ⟨o, rfl⟩) children
            : Tm S Γ' (S.result o))
            = Tm.op o (fun j => children ⟨j⟩) from rfl]
      simp only [Tm.size_op, Tm.height_op]
      set h := Finset.univ.sup (fun j : Fin (S.args o).length => Tm.height (children ⟨j⟩))
        with hh
      have hpow : 1 ≤ m ^ h := Nat.one_le_pow _ _ (by omega)
      have hsum : (∑ j, Tm.size (children ⟨j⟩)) ≤ (S.args o).length * (m ^ h - 1) := by
        calc (∑ j, Tm.size (children ⟨j⟩))
            ≤ ∑ _j : Fin (S.args o).length, (m ^ h - 1) := by
              apply Finset.sum_le_sum
              intro j _
              have hle : Tm.height (children ⟨j⟩) ≤ h := by
                rw [hh]
                exact Finset.le_sup (f := fun k => Tm.height (children ⟨k⟩)) (Finset.mem_univ j)
              have hstep : Tm.size (children ⟨j⟩) + 1 ≤ m ^ h :=
                le_trans (ih ⟨j⟩) (Nat.pow_le_pow_right (by omega) hle)
              omega
          _ = (S.args o).length * (m ^ h - 1) := by
              simp [Finset.sum_const, Finset.card_univ]
      have hk : (S.args o).length * (m ^ h - 1) ≤ m * (m ^ h - 1) :=
        Nat.mul_le_mul (harity o) (le_refl _)
      have harith : 2 + m * (m ^ h - 1) ≤ m ^ (1 + h) := by
        have e : m * (m ^ h - 1) + m = m * m ^ h := by
          rw [← Nat.mul_succ]
          congr 1
          omega
        rw [pow_add, pow_one]
        omega
      calc 1 + (∑ j, Tm.size (children ⟨j⟩)) + 1
          ≤ 2 + m * (m ^ h - 1) := by
            have h1 := hsum
            have h2 := hk
            omega
        _ ≤ m ^ (1 + h) := harith

end GebLean.Binding
