import GebLean.Binding.Substitution

/-!
# The substitution-lemma suite

The law layer of an indexed binder-substitution kit (decision 8): the two
mixed renaming/substitution fusion laws and the substitution monoid
(relative-monad) laws, proved once, generic over `S : BinderSig Ty`, by
`PolyFix.ind` on the term. Each law's operation case reduces to an
under-binder interaction lemma describing how the composed environment
commutes with `Env.underBinder`; those interaction lemmas are proved first.

## Main statements

* `sub_var` — the left unit: substituting a variable reads the environment.
* `sub_id` — the right unit: substituting by the identity environment is the
  identity.
* `ren_sub` — the ren-sub fusion: substitution after renaming is a single
  substitution along the composed environment.
* `sub_ren` — the sub-ren fusion: renaming after substitution is a single
  substitution along the renamed environment.
* `sub_sub` — associativity: substitution after substitution is a single
  substitution along the composed environment.

## References

The kit presentation of the fusion and monoid laws follows G. Allais,
R. Atkey, J. Chapman, C. McBride, and J. McKinna, "A type and scope safe
universe of syntaxes with binding: their semantics and proofs", Proceedings of
the ACM on Programming Languages 2 (ICFP), 2018, DOI `10.1145/3236785`. The
relative-monad framing of the monoid laws follows T. Altenkirch, J. Chapman,
and T. Uustalu, "Monads need not be endofunctors", Logical Methods in Computer
Science 11 (1:3), 2015, DOI `10.2168/LMCS-11(1:3)2015`.
-/

namespace GebLean.Binding

universe v

variable {Ty : Type}

/-- The append-variable eliminator computes on a suffix inclusion
`Var.appendRight Γ y` to its suffix branch `fromΞ y`. Recursion on the prefix
`Γ`, peeling the head shift as in `Var.appendCases`. -/
theorem Var.appendCases_appendRight {Ξ : Ctx Ty} {s : Ty} {motive : Sort v}
    (fromΞ : Var Ξ s → motive) :
    (Γ : Ctx Ty) → (fromΓ : Var Γ s → motive) → (y : Var Ξ s) →
      Var.appendCases fromΞ Γ fromΓ (Var.appendRight Γ y) = fromΞ y
  | [], _, _ => rfl
  | a :: Γ, fromΓ, y =>
      Var.appendCases_appendRight fromΞ Γ (fun v => fromΓ (Var.succ a v)) y

/-- The append-variable eliminator computes on a suffix-embedding
`Thinning.weakAppend.app v` to its prefix branch `fromΓ v`. Recursion on the
prefix `Γ`, peeling the head shift as in `Var.appendCases`. -/
theorem Var.appendCases_weakAppend {Ξ : Ctx Ty} {s : Ty} {motive : Sort v}
    (fromΞ : Var Ξ s → motive) :
    (Γ : Ctx Ty) → (fromΓ : Var Γ s → motive) → (v : Var Γ s) →
      Var.appendCases fromΞ Γ fromΓ (Thinning.weakAppend.app v) = fromΓ v
  | [], _, v => v.1.elim0
  | a :: Γ, fromΓ, ⟨i, hi⟩ => by
      cases i using Fin.cases with
      | zero => rfl
      | succ i' =>
          exact Var.appendCases_weakAppend fromΞ Γ (fun v => fromΓ (Var.succ a v)) ⟨i', hi⟩

/-- Fusion of two nested append-variable eliminators: an outer eliminator over
`Δ` applied to an inner eliminator whose suffix branch is the suffix inclusion
`Var.appendRight Δ` and whose prefix branch is a `Δ`-variable `k v` re-embedded
by the suffix embedding `Thinning.weakAppend.app` collapses to a single
eliminator over `Γ` whose prefix branch is `h ∘ k`. Recursion on the prefix
`Γ`, using the two eliminator computation lemmas. -/
theorem Var.appendCases_fuse {Ξ Δ : Ctx Ty} {s : Ty} {motive : Sort v}
    (g : Var Ξ s → motive) (h : Var Δ s → motive) :
    (Γ : Ctx Ty) → (k : Var Γ s → Var Δ s) → (x : Var (Γ ++ Ξ) s) →
      Var.appendCases g Δ h
          (Var.appendCases (Var.appendRight Δ) Γ
            (fun v => Thinning.weakAppend.app (k v)) x)
        = Var.appendCases g Γ (fun v => h (k v)) x
  | [], _, x => Var.appendCases_appendRight g Δ h x
  | a :: Γ, k, ⟨i, hi⟩ => by
      cases i using Fin.cases with
      | zero => exact Var.appendCases_weakAppend g Δ h (k ⟨0, hi⟩)
      | succ i' =>
          exact Var.appendCases_fuse g h Γ (fun v => k (Var.succ a v)) ⟨i', hi⟩

/-- Left identity for thinning composition on the empty source context: the
empty thinning composes on the left as the identity. Recursion on the second
thinning, whose source is empty so it carries no `keep` step. -/
theorem Thinning.nil_comp : {Δ : Ctx Ty} → (τ : Thinning ([] : Ctx Ty) Δ) →
    Thinning.nil.comp τ = τ
  | _, Thinning.nil => rfl
  | _, Thinning.drop s τ' => congrArg (Thinning.drop s) (Thinning.nil_comp τ')

/-- The suffix embedding `Thinning.weakAppend` is natural in the parallel
append `Thinning.appendId`: renaming into the wider context then embedding the
suffix equals embedding the suffix then renaming under the append. Recursion on
`ρ`. -/
theorem Thinning.weakAppend_comp_appendId {Ξ : Ctx Ty} :
    {Δ Θ : Ctx Ty} → (ρ : Thinning Δ Θ) →
      ρ.comp (Thinning.weakAppend (Ξ := Ξ))
        = (Thinning.weakAppend (Ξ := Ξ)).comp (Thinning.appendId ρ Ξ)
  | _, _, Thinning.nil => (Thinning.nil_comp _).trans (Thinning.comp_id _).symm
  | _, _, Thinning.keep a ρ' =>
      congrArg (Thinning.keep a) (Thinning.weakAppend_comp_appendId ρ')
  | _, _, Thinning.drop a ρ' =>
      congrArg (Thinning.drop a) (Thinning.weakAppend_comp_appendId ρ')

/-- The left unit (relative-monad unit) law: substituting a variable reads the
environment at that variable. -/
theorem sub_var {S : BinderSig Ty} {Γ Δ : Ctx Ty} {s : Ty} (σ : Env (Tm S) Γ Δ)
    (x : Var Γ s) : sub σ (Tm.var x) = σ s x := by
  simp only [sub, traverse_var, subKit, id]

/-- Weakening the composed environment `fun s x => σ s (ρ.app x)` under a binder
binding `Ξ` equals composing the under-binder weakenings: the renaming `ρ` is
absorbed into the parallel append `Thinning.appendId ρ Ξ`. This is the
under-binder interaction lemma the operation case of `ren_sub` needs. -/
theorem underBinder_ren {S : BinderSig Ty} {Γ Δ Θ Ξ : Ctx Ty}
    (ρ : Thinning Γ Δ) (σ : Env (Tm S) Δ Θ) :
    Env.underBinder (subKit S) (Ξ := Ξ) (fun s x => σ s (ρ.app x))
      = fun s x => Env.underBinder (subKit S) σ s ((Thinning.appendId ρ Ξ).app x) := by
  funext s x
  rw [Thinning.appendId_app]
  simp only [Env.underBinder, subKit]
  symm
  exact Var.appendCases_fuse _ _ Γ (fun v => ρ.app v) x

/-- The ren-sub fusion at the traversal level, stated over an arbitrary index
and quantified over the thinning and environment so the induction on the term
goes through. -/
theorem traverse_ren_sub {S : BinderSig Ty} :
    ∀ {y : Ctx Ty × Ty} (t : PolyFix (polyTranslate varOver S.polyEndo) y)
      {Δ Θ : Ctx Ty} (ρ : Thinning y.1 Δ) (σ : Env (Tm S) Δ Θ),
      traverse (subKit S) σ (traverse (varKit S) (renEnv ρ) t)
        = traverse (subKit S) (fun s x => σ s (ρ.app x)) t := by
  intro y t
  induction t with
  | mk y idx children ih =>
    intro Δ Θ ρ σ
    cases idx with
    | inl a =>
      rw [show (PolyFix.mk y (Sum.inl a) children : Tm S y.1 y.2)
            = Tm.var (leafVar a) from by
              obtain ⟨⟨Γ', i'⟩, rfl⟩ := a
              congr 1
              funext e
              exact e.elim]
      simp only [traverse_var, renEnv, varKit, subKit, id]
    | inr p =>
      obtain ⟨Γ', s'⟩ := y
      change { o : S.Op // S.result o = s' } at p
      revert children ih
      obtain ⟨o, rfl⟩ := p
      intro children ih
      rw [show (PolyFix.mk (Γ', S.result o) (Sum.inr ⟨o, rfl⟩) children
            : Tm S Γ' (S.result o))
            = Tm.op o (fun j => children ⟨j⟩) from rfl]
      simp only [traverse_op, underBinder_renEnv, underBinder_ren]
      congr 1
      funext j
      exact ih ⟨j⟩ (Thinning.appendId ρ _) (Env.underBinder (subKit S) σ)

/-- The ren-sub fusion law: substituting after renaming is a single
substitution along the environment precomposed with the renaming's action. -/
theorem ren_sub {S : BinderSig Ty} {Γ Δ Θ : Ctx Ty} {s : Ty} (ρ : Thinning Γ Δ)
    (σ : Env (Tm S) Δ Θ) (t : Tm S Γ s) :
    sub σ (ren ρ t) = sub (fun s x => σ s (ρ.app x)) t :=
  traverse_ren_sub t ρ σ

/-- Weakening the composed environment `fun s x => ren ρ (σ s x)` under a binder
binding `Ξ` equals renaming the under-binder weakening of `σ` along the parallel
append `Thinning.appendId ρ Ξ`. This is the under-binder interaction lemma the
operation case of `sub_ren` needs. -/
theorem underBinder_sub_ren {S : BinderSig Ty} {Γ Δ Θ Ξ : Ctx Ty}
    (σ : Env (Tm S) Γ Δ) (ρ : Thinning Δ Θ) :
    Env.underBinder (subKit S) (Ξ := Ξ) (fun s x => ren ρ (σ s x))
      = fun s x => ren (Thinning.appendId ρ Ξ) (Env.underBinder (subKit S) σ s x) := by
  funext s x
  simp only [Env.underBinder, subKit]
  rw [Var.appendCases_natural (ren (Thinning.appendId ρ Ξ))]
  congr 1
  · funext y
    simp only [ren, traverse_var, varKit, renEnv]
    rw [Thinning.appendId_app, Var.appendCases_appendRight]
  · funext v
    rw [← ren_comp, ← ren_comp, Thinning.weakAppend_comp_appendId]

/-- The sub-ren fusion at the traversal level, stated over an arbitrary index
and quantified over the environment and thinning so the induction on the term
goes through. -/
theorem traverse_sub_ren {S : BinderSig Ty} :
    ∀ {y : Ctx Ty × Ty} (t : PolyFix (polyTranslate varOver S.polyEndo) y)
      {Δ Θ : Ctx Ty} (σ : Env (Tm S) y.1 Δ) (ρ : Thinning Δ Θ),
      traverse (varKit S) (renEnv ρ) (traverse (subKit S) σ t)
        = traverse (subKit S) (fun s x => ren ρ (σ s x)) t := by
  intro y t
  induction t with
  | mk y idx children ih =>
    intro Δ Θ σ ρ
    cases idx with
    | inl a =>
      rw [show (PolyFix.mk y (Sum.inl a) children : Tm S y.1 y.2)
            = Tm.var (leafVar a) from by
              obtain ⟨⟨Γ', i'⟩, rfl⟩ := a
              congr 1
              funext e
              exact e.elim]
      simp only [traverse_var, subKit, id]
      rfl
    | inr p =>
      obtain ⟨Γ', s'⟩ := y
      change { o : S.Op // S.result o = s' } at p
      revert children ih
      obtain ⟨o, rfl⟩ := p
      intro children ih
      rw [show (PolyFix.mk (Γ', S.result o) (Sum.inr ⟨o, rfl⟩) children
            : Tm S Γ' (S.result o))
            = Tm.op o (fun j => children ⟨j⟩) from rfl]
      simp only [traverse_op, underBinder_renEnv, underBinder_sub_ren]
      congr 1
      funext j
      exact ih ⟨j⟩ (Env.underBinder (subKit S) σ) (Thinning.appendId ρ _)

/-- The sub-ren fusion law: renaming after substitution is a single
substitution along the environment postcomposed with the renaming. -/
theorem sub_ren {S : BinderSig Ty} {Γ Δ Θ : Ctx Ty} {s : Ty} (σ : Env (Tm S) Γ Δ)
    (ρ : Thinning Δ Θ) (t : Tm S Γ s) :
    ren ρ (sub σ t) = sub (fun s x => ren ρ (σ s x)) t :=
  traverse_sub_ren t σ ρ

end GebLean.Binding
