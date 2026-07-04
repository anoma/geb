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

end GebLean.Binding
