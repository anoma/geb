import GebLean.Binding.Renaming
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

## References

The tree height in the `1 + max`-over-children form is D. Leivant, "Ramified
recurrence and computational complexity III: Higher type recurrence and
elementary complexity", Annals of Pure and Applied Logic 96 (1999) 209-229,
DOI `10.1016/S0168-0072(98)00040-2`, section 2.1, p. 211. The binder-signature
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

end GebLean.Binding
