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

/-- Splitting a variable of `Γ ++ Ξ` by `Var.appendCases` into the suffix
inclusion and the suffix embedding and rejoining recovers the variable. Read
off `Thinning.appendId_app` at the identity thinning. -/
theorem Var.appendCases_self {Ξ Γ : Ctx Ty} {s : Ty} (x : Var (Γ ++ Ξ) s) :
    Var.appendCases (fun y => Var.appendRight Γ y) Γ
        (fun v => Thinning.weakAppend.app v) x = x := by
  have h := Thinning.appendId_app (Ξ := Ξ) (Thinning.id : Thinning Γ Γ) x
  simp only [Thinning.appendId_id, Thinning.app_id] at h
  exact h.symm

/-- Weakening the identity environment under a binder binding `Ξ` is again the
identity environment. This is the under-binder interaction lemma the operation
case of `sub_id` needs. -/
theorem underBinder_idEnv {S : BinderSig Ty} {Γ Ξ : Ctx Ty} :
    Env.underBinder (subKit S) (idEnv (Γ := Γ))
      = (idEnv : Env (Tm S) (Γ ++ Ξ) (Γ ++ Ξ)) := by
  funext s x
  simp only [Env.underBinder, subKit, idEnv, ren, traverse_var, varKit, renEnv]
  rw [← Var.appendCases_natural Tm.var, Var.appendCases_self]

/-- The right unit at the traversal level: the traversal at the substitution kit
along the identity environment is the identity, stated over an arbitrary index
so the induction on the term goes through. -/
theorem traverse_idEnv {S : BinderSig Ty} :
    ∀ {y : Ctx Ty × Ty} (t : PolyFix (polyTranslate varOver S.polyEndo) y),
      traverse (subKit S) (idEnv (Γ := y.1)) t = t := by
  intro y t
  induction t with
  | mk y idx children ih =>
    cases idx with
    | inl a =>
      rw [show (PolyFix.mk y (Sum.inl a) children : Tm S y.1 y.2)
            = Tm.var (leafVar a) from by
              obtain ⟨⟨Γ', i'⟩, rfl⟩ := a
              congr 1
              funext e
              exact e.elim]
      simp only [traverse_var, subKit, idEnv, id]
    | inr p =>
      obtain ⟨Γ', s'⟩ := y
      change { o : S.Op // S.result o = s' } at p
      revert children ih
      obtain ⟨o, rfl⟩ := p
      intro children ih
      rw [show (PolyFix.mk (Γ', S.result o) (Sum.inr ⟨o, rfl⟩) children
            : Tm S Γ' (S.result o))
            = Tm.op o (fun j => children ⟨j⟩) from rfl]
      rw [traverse_op]
      congr 1
      funext j
      rw [underBinder_idEnv]
      exact ih ⟨j⟩

/-- The right unit (relative-monad unit) law: substituting by the identity
environment is the identity. -/
theorem sub_id {S : BinderSig Ty} {Γ : Ctx Ty} {s : Ty} (t : Tm S Γ s) :
    sub idEnv t = t :=
  traverse_idEnv t

/-- Weakening the composed environment `fun s x => sub τ (σ s x)` under a binder
binding `Ξ` equals composing the under-binder weakenings by substitution. The
old-variable branch reconciles the two weakened composites through the fusion
laws `sub_ren` and `ren_sub`. This is the under-binder interaction lemma the
operation case of `sub_sub` needs. -/
theorem underBinder_sub {S : BinderSig Ty} {Γ Δ Θ Ξ : Ctx Ty}
    (σ : Env (Tm S) Γ Δ) (τ : Env (Tm S) Δ Θ) :
    Env.underBinder (subKit S) (Ξ := Ξ) (fun s x => sub τ (σ s x))
      = fun s x =>
          sub (Env.underBinder (subKit S) τ) (Env.underBinder (subKit S) σ s x) := by
  funext s x
  change Var.appendCases (fun y => Tm.var (Var.appendRight Θ y)) Γ
        (fun v => ren Thinning.weakAppend (sub τ (σ s v))) x
      = sub (Env.underBinder (subKit S) τ)
          (Var.appendCases (fun y => Tm.var (Var.appendRight Δ y)) Γ
            (fun v => ren Thinning.weakAppend (σ s v)) x)
  rw [Var.appendCases_natural (sub (Env.underBinder (subKit S) τ))]
  congr 1
  · funext y
    rw [sub_var]
    simp only [Env.underBinder, subKit]
    rw [Var.appendCases_appendRight]
  · funext v
    rw [sub_ren, ren_sub]
    congr 1
    funext s' x'
    simp only [Env.underBinder, subKit]
    rw [Var.appendCases_weakAppend]

/-- The substitution associativity at the traversal level, stated over an
arbitrary index and quantified over the environments so the induction on the
term goes through. -/
theorem traverse_sub_sub {S : BinderSig Ty} :
    ∀ {y : Ctx Ty × Ty} (t : PolyFix (polyTranslate varOver S.polyEndo) y)
      {Δ Θ : Ctx Ty} (σ : Env (Tm S) y.1 Δ) (τ : Env (Tm S) Δ Θ),
      traverse (subKit S) τ (traverse (subKit S) σ t)
        = traverse (subKit S) (fun s x => sub τ (σ s x)) t := by
  intro y t
  induction t with
  | mk y idx children ih =>
    intro Δ Θ σ τ
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
      simp only [traverse_op, underBinder_sub]
      congr 1
      funext j
      exact ih ⟨j⟩ (Env.underBinder (subKit S) σ) (Env.underBinder (subKit S) τ)

/-- The associativity (relative-monad Kleisli-extension) law: substitution after
substitution is a single substitution along the composed environment. -/
theorem sub_sub {S : BinderSig Ty} {Γ Δ Θ : Ctx Ty} {s : Ty} (σ : Env (Tm S) Γ Δ)
    (τ : Env (Tm S) Δ Θ) (t : Tm S Γ s) :
    sub τ (sub σ t) = sub (fun s x => sub τ (σ s x)) t :=
  traverse_sub_sub t σ τ

/-- Transporting a head-shifted variable `Var.succ a v` across a context equality
prepended by a head entry `a` peels the transport onto the tail. Proved by
`subst`; the recursion step of `Var.appendCases_append_assoc`. -/
theorem Var.transport_cons_succ {a : Ty} {C C' : Ctx Ty} {s : Ty} (e : C = C')
    (v : Var C s) :
    (congrArg (a :: ·) e) ▸ Var.succ a v = Var.succ a (e ▸ v) := by
  cases e; rfl

/-- Transporting the head variable `⟨0, _⟩` across a context equality prepended by
a head entry `a` leaves it fixed at position `0`. Proved by `subst`; the base
step of `Var.appendCases_append_assoc`. -/
theorem Var.transport_cons_zero {a : Ty} {C C' : Ctx Ty} {s : Ty} (e : C = C')
    (hi : List.get (a :: C) 0 = s) :
    (congrArg (a :: ·) e) ▸ (⟨0, hi⟩ : Var (a :: C) s)
      = (⟨0, hi⟩ : Var (a :: C') s) := by
  cases e; rfl

/-- Reassociating a nested append eliminator through the context associativity
`Γ ++ (Ξ₁ ++ Ξ₂) = (Γ ++ Ξ₁) ++ Ξ₂`: splitting a variable of `(Γ ++ Ξ₁) ++ Ξ₂`
(transported from `Γ ++ (Ξ₁ ++ Ξ₂)`) at the outer boundary `(Γ ++ Ξ₁) | Ξ₂`
equals splitting the original variable at `Γ | (Ξ₁ ++ Ξ₂)`, with the suffix
branch further split at `Ξ₁ | Ξ₂`, embedding a prefix `Γ`-variable through
`Thinning.weakAppend` and a middle `Ξ₁`-variable through `Var.appendRight`.
Recursion on the prefix `Γ`, peeling the head shift as in `Var.appendCases`. -/
theorem Var.appendCases_append_assoc {Ξ₁ Ξ₂ : Ctx Ty} {s : Ty} {motive : Sort v}
    (fromΞ₂ : Var Ξ₂ s → motive) :
    (Γ : Ctx Ty) → (fromΓΞ₁ : Var (Γ ++ Ξ₁) s → motive) →
    (x : Var (Γ ++ (Ξ₁ ++ Ξ₂)) s) →
      Var.appendCases fromΞ₂ (Γ ++ Ξ₁) fromΓΞ₁ ((List.append_assoc Γ Ξ₁ Ξ₂).symm ▸ x)
        = Var.appendCases
            (Var.appendCases fromΞ₂ Ξ₁ (fun w => fromΓΞ₁ (Var.appendRight Γ w))) Γ
            (fun v => fromΓΞ₁ (Thinning.weakAppend.app v)) x
  | [], fromΓΞ₁, x => rfl
  | a :: Γ, fromΓΞ₁, ⟨i, hi⟩ => by
      cases i using Fin.cases with
      | zero =>
          exact congrArg (Var.appendCases fromΞ₂ (a :: Γ ++ Ξ₁) fromΓΞ₁)
            (Var.transport_cons_zero (List.append_assoc Γ Ξ₁ Ξ₂).symm hi)
      | succ i' =>
          refine (congrArg (Var.appendCases fromΞ₂ (a :: Γ ++ Ξ₁) fromΓΞ₁)
            (Var.transport_cons_succ (List.append_assoc Γ Ξ₁ Ξ₂).symm ⟨i', hi⟩)).trans ?_
          refine (Var.appendCases_append_assoc fromΞ₂ Γ
            (fun w => fromΓΞ₁ (Var.succ a w)) ⟨i', hi⟩).trans ?_
          simp only [Var.appendCases_cons_succ, Var.appendRight_cons,
            Thinning.weakAppend_app_succ]

/-- Prepending a shared head entry `a` commutes with a codomain transport of a
thinning: `keep a (e ▸ ρ) = (congrArg (a :: ·) e) ▸ keep a ρ`. Proved by `subst`. -/
theorem Thinning.keep_transport_cod {a : Ty} {Γ B B' : Ctx Ty} (e : B = B')
    (ρ : Thinning Γ B) :
    Thinning.keep a (e ▸ ρ) = (congrArg (a :: ·) e) ▸ Thinning.keep a ρ := by
  cases e; rfl

/-- Suffix embeddings compose out of the empty prefix: embedding `[] ⊆ Ξ₁` then
`Ξ₁ ⊆ Ξ₁ ++ Ξ₂` embeds `[] ⊆ Ξ₁ ++ Ξ₂`. Recursion on `Ξ₁`; the base step of
`Thinning.weakAppend_comp_weakAppend`. -/
theorem Thinning.weakAppend_nil_comp_weakAppend : (Ξ₁ Ξ₂ : Ctx Ty) →
    (Thinning.weakAppend (Γ := ([] : Ctx Ty)) (Ξ := Ξ₁)).comp
        (Thinning.weakAppend (Γ := Ξ₁) (Ξ := Ξ₂))
      = Thinning.weakAppend (Γ := ([] : Ctx Ty)) (Ξ := Ξ₁ ++ Ξ₂)
  | [], _ => Thinning.nil_comp _
  | b :: Ξ₁', Ξ₂ =>
      congrArg (Thinning.drop b) (Thinning.weakAppend_nil_comp_weakAppend Ξ₁' Ξ₂)

/-- Suffix embeddings compose through the context associativity: embedding
`Δ ⊆ Δ ++ Ξ₁` then `(Δ ++ Ξ₁) ⊆ (Δ ++ Ξ₁) ++ Ξ₂` equals, up to the
`List.append_assoc` transport, the single embedding `Δ ⊆ Δ ++ (Ξ₁ ++ Ξ₂)`.
Recursion on the prefix `Δ`, threading the head shift through
`Thinning.keep_transport_cod`. -/
theorem Thinning.weakAppend_comp_weakAppend {Ξ₁ Ξ₂ : Ctx Ty} : (Δ : Ctx Ty) →
    (Thinning.weakAppend (Γ := Δ) (Ξ := Ξ₁)).comp
        (Thinning.weakAppend (Γ := Δ ++ Ξ₁) (Ξ := Ξ₂))
      = (List.append_assoc Δ Ξ₁ Ξ₂).symm ▸ Thinning.weakAppend (Γ := Δ) (Ξ := Ξ₁ ++ Ξ₂)
  | [] => Thinning.weakAppend_nil_comp_weakAppend Ξ₁ Ξ₂
  | a :: Δ => by
      refine Eq.trans (b := Thinning.keep a
          ((Thinning.weakAppend (Γ := Δ) (Ξ := Ξ₁)).comp
            (Thinning.weakAppend (Γ := Δ ++ Ξ₁) (Ξ := Ξ₂)))) rfl ?_
      rw [Thinning.weakAppend_comp_weakAppend Δ]
      exact Thinning.keep_transport_cod (List.append_assoc Δ Ξ₁ Ξ₂).symm _

/-- Renaming along a codomain-transported thinning pulls the transport out: for
`h : Δ = Δ'`, `ren (h ▸ ρ) t = h ▸ ren ρ t`. Proved by `subst`. -/
theorem ren_transport_cod {S : BinderSig Ty} {Γ Δ Δ' : Ctx Ty} {s : Ty} (h : Δ = Δ')
    (ρ : Thinning Γ Δ) (t : Tm S Γ s) :
    ren (h ▸ ρ) t = h ▸ ren ρ t := by
  cases h; rfl

/-- Iterated weakening along the two suffix embeddings equals, up to the
`List.append_assoc` transport, a single weakening along the combined suffix. The
term-level image of `Thinning.weakAppend_comp_weakAppend` under `ren`, obtained
through `ren_comp`. -/
theorem ren_weakAppend_append {S : BinderSig Ty} {Δ Ξ₁ Ξ₂ : Ctx Ty} {s : Ty}
    (t : Tm S Δ s) :
    ren (Thinning.weakAppend (Ξ := Ξ₂)) (ren (Thinning.weakAppend (Ξ := Ξ₁)) t)
      = (List.append_assoc Δ Ξ₁ Ξ₂).symm ▸ ren (Thinning.weakAppend (Ξ := Ξ₁ ++ Ξ₂)) t := by
  rw [← ren_comp, Thinning.weakAppend_comp_weakAppend Δ, ren_transport_cod]

/-- The suffix inclusion `Var.appendRight` reassociates across a nested append:
transporting `Var.appendRight Δ y` of a suffix variable `y : Var (Ξ₁ ++ Ξ₂) s`
along `Δ ++ (Ξ₁ ++ Ξ₂) = (Δ ++ Ξ₁) ++ Ξ₂` splits `y` at the boundary `Ξ₁ | Ξ₂`,
sending the `Ξ₂`-branch through `Var.appendRight (Δ ++ Ξ₁)` and the `Ξ₁`-branch
through `Var.appendRight Δ` re-embedded by `Thinning.weakAppend`. Recursion on the
prefix `Δ`, threading the head shift through `Var.appendCases_natural`. -/
theorem Var.appendRight_append_assoc {Ξ₁ Ξ₂ : Ctx Ty} {s : Ty} : (Δ : Ctx Ty) →
    (y : Var (Ξ₁ ++ Ξ₂) s) →
    (List.append_assoc Δ Ξ₁ Ξ₂).symm ▸ Var.appendRight Δ y
      = Var.appendCases (Var.appendRight (Δ ++ Ξ₁)) Ξ₁
          (fun w => Thinning.weakAppend.app (Var.appendRight Δ w)) y
  | [], y => (Var.appendCases_self y).symm
  | a :: Δ, y => by
      have step := Var.transport_cons_succ (a := a) (List.append_assoc Δ Ξ₁ Ξ₂).symm
        (Var.appendRight Δ y)
      rw [Var.appendRight_append_assoc Δ y] at step
      change (congrArg (a :: ·) (List.append_assoc Δ Ξ₁ Ξ₂).symm) ▸
        Var.succ a (Var.appendRight Δ y) = _
      rw [step]
      exact Var.appendCases_natural (Var.succ a) (Var.appendRight (Δ ++ Ξ₁)) Ξ₁
        (fun w => Thinning.weakAppend.app (Var.appendRight Δ w)) y

/-- Embedding a variable as a term commutes with a codomain transport: for
`e : Δ = Δ'`, `Tm.var (e ▸ v) = e ▸ Tm.var v`. Proved by `subst`. -/
theorem Tm.var_transport_cod {S : BinderSig Ty} {Δ Δ' : Ctx Ty} {s : Ty} (e : Δ = Δ')
    (v : Var Δ s) : Tm.var (e ▸ v) = e ▸ (Tm.var v : Tm S Δ s) := by
  cases e; rfl

/-- Weakening an environment under two nested binder contexts `Ξ₁` then `Ξ₂`
equals, up to the `List.append_assoc` transports on the source and target
contexts, weakening once under the combined binder context `Ξ₁ ++ Ξ₂`. The
syntactic reassociation analog of the denotational `joinEnv_envExtend`: the
freshly bound variables reassociate through `Var.appendRight_append_assoc`
(under `Tm.var`), and the old values reassociate through
`ren_weakAppend_append`. Dispatched pointwise by `Var.appendCases_append_assoc`. -/
theorem underBinder_append {S : BinderSig Ty} {Γ Δ Ξ₁ Ξ₂ : Ctx Ty}
    (ρ : Env (Tm S) Γ Δ) (s : Ty) (x : Var (Γ ++ (Ξ₁ ++ Ξ₂)) s) :
    Env.underBinder (subKit S) (Ξ := Ξ₂) (Env.underBinder (subKit S) (Ξ := Ξ₁) ρ) s
        ((List.append_assoc Γ Ξ₁ Ξ₂).symm ▸ x)
      = (List.append_assoc Δ Ξ₁ Ξ₂).symm ▸
          Env.underBinder (subKit S) (Ξ := Ξ₁ ++ Ξ₂) ρ s x := by
  change Var.appendCases (fun y => Tm.var (Var.appendRight (Δ ++ Ξ₁) y)) (Γ ++ Ξ₁)
      (fun v => ren Thinning.weakAppend (Env.underBinder (subKit S) (Ξ := Ξ₁) ρ s v))
      ((List.append_assoc Γ Ξ₁ Ξ₂).symm ▸ x)
    = (List.append_assoc Δ Ξ₁ Ξ₂).symm ▸
        Var.appendCases (fun y => Tm.var (Var.appendRight Δ y)) Γ
          (fun v => ren Thinning.weakAppend (ρ s v)) x
  rw [Var.appendCases_append_assoc (fun y => Tm.var (Var.appendRight (Δ ++ Ξ₁) y)) Γ
        (fun v => ren Thinning.weakAppend (Env.underBinder (subKit S) (Ξ := Ξ₁) ρ s v)) x]
  have hnat := Var.appendCases_natural
      (fun z : Tm S (Δ ++ (Ξ₁ ++ Ξ₂)) s => (List.append_assoc Δ Ξ₁ Ξ₂).symm ▸ z)
      (fun y => Tm.var (Var.appendRight Δ y)) Γ (fun v => ren Thinning.weakAppend (ρ s v)) x
  rw [hnat]
  congr 1
  · funext y
    simp only [Env.underBinder, subKit, Var.appendCases_appendRight, ren, traverse_var,
      varKit, renEnv]
    rw [← Tm.var_transport_cod, Var.appendRight_append_assoc Δ y]
    exact (Var.appendCases_natural Tm.var (Var.appendRight (Δ ++ Ξ₁)) Ξ₁
      (fun w => Thinning.weakAppend.app (Var.appendRight Δ w)) y).symm
  · funext v
    simp only [Env.underBinder, subKit, Var.appendCases_weakAppend]
    exact ren_weakAppend_append (ρ s v)

end GebLean.Binding
