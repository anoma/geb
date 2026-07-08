import GebLean.Binding.Kit

/-!
# Renaming

Renaming is the instance of the generic binder-aware traversal (`traverse`) at
the renaming kit `varKit`, with the renaming environment `renEnv ρ` reading a
variable through a thinning `ρ`. Its two functor laws, `ren_id` and `ren_comp`,
exhibit renaming as a (contravariant) action of the thinning category on terms:
the identity thinning acts as the identity, and thinning composition acts by
composition of renamings.

## Main definitions

* `renEnv` — the renaming environment of a thinning: read each variable through
  the thinning.
* `ren` — renaming of a term along a thinning, `traverse` at `varKit`.

## Main statements

* `ren_id` — renaming along the identity thinning is the identity.
* `ren_comp` — renaming along a composite thinning is the composite of the
  renamings.

## References

The kit presentation of renaming and its functor laws follows G. Allais,
R. Atkey, J. Chapman, C. McBride, and J. McKinna, "A type and scope safe
universe of syntaxes with binding: their semantics and proofs", Proceedings of
the ACM on Programming Languages 2 (ICFP), 2018, DOI `10.1145/3236785`.
-/

namespace GebLean.Binding

universe u v

variable {Ty : Type u}

/-- Naturality of the append-variable eliminator `Var.appendCases`:
post-composing a function `g` with an eliminator equals eliminating with the two
`g`-post-composed branches. Recursion on the prefix `Γ`, mirroring
`Var.appendCases`. -/
theorem Var.appendCases_natural {Ξ : Ctx Ty} {s : Ty} {motive motive' : Sort v}
    (g : motive → motive') (fromΞ : Var Ξ s → motive) :
    (Γ : Ctx Ty) → (fromΓ : Var Γ s → motive) → (x : Var (Γ ++ Ξ) s) →
      g (Var.appendCases fromΞ Γ fromΓ x)
        = Var.appendCases (fun y => g (fromΞ y)) Γ (fun v => g (fromΓ v)) x
  | [], _, _ => rfl
  | a :: Γ, fromΓ, ⟨i, hi⟩ => by
      cases i using Fin.cases with
      | zero => rfl
      | succ i' =>
          exact Var.appendCases_natural g fromΞ Γ (fun v => fromΓ (Var.succ a v)) ⟨i', hi⟩

/-- `Var.appendRight` at a cons prefix shifts its result past the head entry. -/
theorem Var.appendRight_cons {Ξ : Ctx Ty} {s : Ty} (a : Ty) (Δ : Ctx Ty)
    (y : Var Ξ s) :
    Var.appendRight (a :: Δ) y = Var.succ a (Var.appendRight Δ y) := rfl

/-- Positional evaluation of the append-variable eliminator: when the prefix
branch reads a position map `F` at the variable's numeric position and the
suffix branch reads `F` at the prefix-displaced position, the eliminator reads
`F` at the position of the appended variable. Recursion on the prefix `Γ`,
mirroring `Var.appendCases`. -/
theorem Var.appendCases_val {Ξ : Ctx Ty} {s : Ty} {motive : Sort v}
    (fromΞ : Var Ξ s → motive) :
    (Γ : Ctx Ty) → (F : ℕ → motive) → (fromΓ : Var Γ s → motive) →
    (∀ v : Var Γ s, fromΓ v = F v.1.val) →
    (∀ y : Var Ξ s, fromΞ y = F (Γ.length + y.1.val)) →
    (x : Var (Γ ++ Ξ) s) → Var.appendCases fromΞ Γ fromΓ x = F x.1.val
  | [], F, _, _, hΞ, x => (hΞ x).trans (congrArg F (Nat.zero_add _))
  | a :: Γ, F, fromΓ, hΓ, hΞ, ⟨i, hi⟩ => by
      cases i using Fin.cases with
      | zero => exact hΓ ⟨0, hi⟩
      | succ i' =>
          exact Var.appendCases_val fromΞ Γ (fun n => F (n + 1))
            (fun v => fromΓ (Var.succ a v)) (fun v => hΓ (Var.succ a v))
            (fun y => (hΞ y).trans (congrArg F (Nat.succ_add Γ.length y.1.val)))
            ⟨i', hi⟩

/-- The suffix inclusion `Var.appendRight` displaces a variable's numeric
position by the prefix length. Recursion on the prefix `Δ`, mirroring
`Var.appendRight`. -/
theorem Var.appendRight_val {Ξ : Ctx Ty} {s : Ty} :
    (Δ : Ctx Ty) → (y : Var Ξ s) →
      (Var.appendRight Δ y).1.val = Δ.length + y.1.val
  | [], _ => (Nat.zero_add _).symm
  | a :: Δ, y => by
      rw [Var.appendRight_cons]
      change (Var.appendRight Δ y).1.val + 1 = (a :: Δ).length + y.1.val
      rw [Var.appendRight_val Δ y]
      simp only [List.length_cons]
      omega

/-- The suffix embedding `Thinning.weakAppend` at a cons prefix commutes with the
head shift `Var.succ a`. -/
theorem Thinning.weakAppend_app_succ {Γ Ξ : Ctx Ty} {s : Ty} (a : Ty) (v : Var Γ s) :
    (Thinning.weakAppend (Γ := a :: Γ) (Ξ := Ξ)).app (Var.succ a v)
      = Var.succ a ((Thinning.weakAppend (Γ := Γ) (Ξ := Ξ)).app v) := rfl

/-- The suffix embedding `Thinning.weakAppend` preserves a variable's numeric
position: every entry of the prefix is kept, so a prefix variable's position in
`Γ ++ Ξ` is unchanged. Recursion on the prefix `Γ`, mirroring
`Thinning.weakAppend`. -/
theorem Thinning.weakAppend_app_val {Ξ : Ctx Ty} :
    {Γ : Ctx Ty} → {s : Ty} → (v : Var Γ s) →
      ((Thinning.weakAppend (Ξ := Ξ)).app v).1.val = v.1.val
  | [], _, v => v.1.elim0
  | _ :: Γ, _, ⟨i, hi⟩ => by
      cases i using Fin.cases with
      | zero => rfl
      | succ i' =>
          change ((Thinning.weakAppend (Γ := Γ) (Ξ := Ξ)).app ⟨i', hi⟩).1.val + 1
              = i'.val + 1
          rw [Thinning.weakAppend_app_val ⟨i', hi⟩]

/-- `Var.appendCases` at a cons prefix on a shifted index peels the head entry,
recursing on the tail prefix with the head-shifted `Γ`-branch. -/
theorem Var.appendCases_cons_succ {Ξ Γ : Ctx Ty} {s : Ty} {motive : Sort v}
    (fromΞ : Var Ξ s → motive) (a : Ty) (fromΓ : Var (a :: Γ) s → motive)
    (i' : Fin (Γ ++ Ξ).length) (hi : (a :: Γ ++ Ξ).get i'.succ = s) :
    Var.appendCases fromΞ (a :: Γ) fromΓ ⟨i'.succ, hi⟩
      = Var.appendCases fromΞ Γ (fun v => fromΓ (Var.succ a v)) ⟨i', hi⟩ := rfl

/-- The parallel append of a thinning: extend `ρ : Thinning Γ Δ` by keeping every
entry of a common suffix `Ξ`, yielding `Thinning (Γ ++ Ξ) (Δ ++ Ξ)`. Recursion on
`ρ`; the empty thinning becomes the identity on `Ξ`. This is the thinning-level
counterpart of `Env.underBinder` on the renaming kit. -/
def Thinning.appendId : {Γ Δ : Ctx Ty} → Thinning Γ Δ → (Ξ : Ctx Ty) →
    Thinning (Γ ++ Ξ) (Δ ++ Ξ)
  | _, _, Thinning.nil, _ => Thinning.id
  | _, _, Thinning.keep a ρ', Ξ => Thinning.keep a (Thinning.appendId ρ' Ξ)
  | _, _, Thinning.drop a ρ', Ξ => Thinning.drop a (Thinning.appendId ρ' Ξ)

/-- `Thinning.app` at a `keep` commutes with the head shift `Var.succ a`. -/
theorem Thinning.app_keep_of_succ {Γ Δ : Ctx Ty} {s a : Ty} (ρ : Thinning Γ Δ)
    (v : Var Γ s) :
    (Thinning.keep a ρ).app (Var.succ a v) = Var.succ a (ρ.app v) := rfl

/-- `Thinning.app` at a `drop` prepends the head shift `Var.succ a`. -/
theorem Thinning.app_drop {Γ Δ : Ctx Ty} {s a : Ty} (ρ : Thinning Γ Δ)
    (x : Var Γ s) :
    (Thinning.drop a ρ).app x = Var.succ a (ρ.app x) := rfl

/-- The action of the parallel append `Thinning.appendId ρ Ξ` on a variable of
`Γ ++ Ξ` splits, via `Var.appendCases`, into the suffix inclusion on
`Ξ`-variables and `ρ` followed by the prefix embedding on `Γ`-variables.
Recursion on `ρ`, using `Var.appendCases_natural` to pull out the head shift. -/
theorem Thinning.appendId_app {Ξ : Ctx Ty} {s : Ty} {Γ Δ : Ctx Ty}
    (ρ : Thinning Γ Δ) :
    ∀ x : Var (Γ ++ Ξ) s,
      (Thinning.appendId ρ Ξ).app x
        = Var.appendCases (fun y => Var.appendRight Δ y) Γ
            (fun v => Thinning.weakAppend.app (ρ.app v)) x := by
  induction ρ with
  | nil =>
      intro x
      exact Thinning.app_id x
  | keep a ρ' ih =>
      intro x
      obtain ⟨i, hi⟩ := x
      cases i using Fin.cases with
      | zero => rfl
      | succ i' =>
          simp only [Thinning.appendId, Var.appendCases_cons_succ,
            Var.appendRight_cons, Thinning.app_keep_of_succ,
            Thinning.weakAppend_app_succ]
          exact (congrArg (Var.succ a) (ih ⟨i', hi⟩)).trans
            (Var.appendCases_natural (Var.succ a) _ _ _ ⟨i', hi⟩)
  | drop a ρ' ih =>
      intro x
      simp only [Thinning.appendId, Thinning.app_drop, Var.appendRight_cons,
        Thinning.weakAppend_app_succ]
      exact (congrArg (Var.succ a) (ih x)).trans
        (Var.appendCases_natural (Var.succ a) _ _ _ x)

/-- The numeric position action of the parallel append `Thinning.appendId ρ Ξ`:
if `ρ` acts on positions as the identity below `L` and as the displacement by
`d` at or above `L` — the action of a thinning inserting `d` entries at
position `L ≤ Γ.length` — then the parallel append acts by the same position
map on the extended context. The suffix variables lie at positions at least
`Γ.length`, where the two branches of `Thinning.appendId_app` displace by the
length difference `d`; the prefix variables inherit `ρ`'s action through the
position-preserving suffix embedding. -/
theorem Thinning.appendId_app_val {Γ Δ Ξ : Ctx Ty} {s : Ty} {L d : ℕ}
    (ρ : Thinning Γ Δ) (hL : L ≤ Γ.length) (hlen : Δ.length = Γ.length + d)
    (hρ : ∀ {u : Ty} (v : Var Γ u),
      (ρ.app v).1.val = if v.1.val < L then v.1.val else v.1.val + d)
    (x : Var (Γ ++ Ξ) s) :
    ((Thinning.appendId ρ Ξ).app x).1.val
      = if x.1.val < L then x.1.val else x.1.val + d := by
  refine (congrArg (fun w : Var (Δ ++ Ξ) s => w.1.val)
      (Thinning.appendId_app ρ x)).trans
    ((Var.appendCases_natural (fun w : Var (Δ ++ Ξ) s => w.1.val) _ Γ _ x).trans ?_)
  exact Var.appendCases_val _ Γ (fun n => if n < L then n else n + d) _
    (fun v => (Thinning.weakAppend_app_val (ρ.app v)).trans (hρ v))
    (fun y => by
      simp only [Var.appendRight_val]
      rw [if_neg (by omega)]
      omega)
    x

/-- Right identity for thinning composition. -/
theorem Thinning.comp_id {Γ Δ : Ctx Ty} (ρ : Thinning Γ Δ) :
    ρ.comp Thinning.id = ρ := by
  induction ρ with
  | nil => rfl
  | keep a ρ' ih => exact congrArg (Thinning.keep a) ih
  | drop a ρ' ih => exact congrArg (Thinning.drop a) ih

/-- The parallel append is functorial in thinning composition. -/
theorem Thinning.appendId_comp {Ξ : Ctx Ty} {Γ Δ Θ : Ctx Ty} (ρ : Thinning Γ Δ)
    (τ : Thinning Δ Θ) :
    Thinning.appendId (ρ.comp τ) Ξ
      = (Thinning.appendId ρ Ξ).comp (Thinning.appendId τ Ξ) := by
  induction τ generalizing Γ with
  | nil => exact (Thinning.comp_id _).symm
  | keep a τ' ih =>
      cases ρ with
      | keep _ ρ' => exact congrArg (Thinning.keep a) (ih ρ')
      | drop _ ρ' => exact congrArg (Thinning.drop a) (ih ρ')
  | drop a τ' ih => exact congrArg (Thinning.drop a) (ih ρ)

/-- The parallel append preserves the identity thinning. -/
theorem Thinning.appendId_id {Ξ : Ctx Ty} : {Γ : Ctx Ty} →
    Thinning.appendId (Thinning.id : Thinning Γ Γ) Ξ = Thinning.id
  | [] => rfl
  | a :: Γ => congrArg (Thinning.keep a) (Thinning.appendId_id (Γ := Γ))

/-- The renaming environment of a thinning `ρ`: at each variable, read its image
under `ρ` as a value of the renaming kit (a variable of the target context). -/
def renEnv {Γ Δ : Ctx Ty} (ρ : Thinning Γ Δ) : Env Var Γ Δ :=
  fun _ x => ρ.app x

/-- Renaming of a term along a thinning `ρ`: the generic traversal at the
renaming kit `varKit` with the renaming environment `renEnv ρ`. -/
def ren {S : BinderSig Ty} {Γ Δ : Ctx Ty} {s : Ty} (ρ : Thinning Γ Δ)
    (t : Tm S Γ s) : Tm S Δ s :=
  traverse (varKit S) (renEnv ρ) t

/-- Weakening the renaming environment of `ρ` under a binder binding `Ξ` equals
the renaming environment of the parallel append `Thinning.appendId ρ Ξ`. This is
the environment-level form of `Thinning.appendId_app`. -/
theorem underBinder_renEnv {S : BinderSig Ty} {Γ Δ Ξ : Ctx Ty} (ρ : Thinning Γ Δ) :
    Env.underBinder (varKit S) (renEnv ρ)
      = renEnv (Thinning.appendId ρ Ξ) := by
  funext s x
  simp only [Env.underBinder, varKit, renEnv, id]
  exact (Thinning.appendId_app ρ x).symm

/-- The traversal at the renaming kit along the identity renaming environment is
the identity, stated over an arbitrary index so the induction on the term goes
through. -/
theorem traverse_renEnv_id {S : BinderSig Ty} :
    ∀ {y : Ctx Ty × Ty} (t : PolyFix (polyTranslate varOver S.polyEndo) y),
      traverse (varKit S) (renEnv (Thinning.id : Thinning y.1 y.1)) t = t := by
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
      rw [traverse_var]
      exact congrArg Tm.var (Thinning.app_id (leafVar a))
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
      rw [underBinder_renEnv, Thinning.appendId_id]
      exact ih ⟨j⟩

/-- The traversal at the renaming kit is functorial in thinning composition,
stated over an arbitrary index and quantified over the thinnings so the induction
on the term goes through. -/
theorem traverse_renEnv_comp {S : BinderSig Ty} :
    ∀ {y : Ctx Ty × Ty} (t : PolyFix (polyTranslate varOver S.polyEndo) y)
      {Δ Θ : Ctx Ty} (ρ : Thinning y.1 Δ) (τ : Thinning Δ Θ),
      traverse (varKit S) (renEnv (ρ.comp τ)) t
        = traverse (varKit S) (renEnv τ) (traverse (varKit S) (renEnv ρ) t) := by
  intro y t
  induction t with
  | mk y idx children ih =>
    intro Δ Θ ρ τ
    cases idx with
    | inl a =>
      rw [show (PolyFix.mk y (Sum.inl a) children : Tm S y.1 y.2)
            = Tm.var (leafVar a) from by
              obtain ⟨⟨Γ', i'⟩, rfl⟩ := a
              congr 1
              funext e
              exact e.elim]
      simp only [traverse_var, renEnv, varKit]
      exact congrArg Tm.var (Thinning.app_comp ρ τ (leafVar a))
    | inr p =>
      obtain ⟨Γ', s'⟩ := y
      change { o : S.Op // S.result o = s' } at p
      revert children ih
      obtain ⟨o, rfl⟩ := p
      intro children ih
      rw [show (PolyFix.mk (Γ', S.result o) (Sum.inr ⟨o, rfl⟩) children
            : Tm S Γ' (S.result o))
            = Tm.op o (fun j => children ⟨j⟩) from rfl]
      simp only [traverse_op]
      congr 1
      funext j
      simp only [underBinder_renEnv, Thinning.appendId_comp]
      exact ih ⟨j⟩ (Thinning.appendId ρ _) (Thinning.appendId τ _)

/-- Renaming along the identity thinning is the identity. -/
theorem ren_id {S : BinderSig Ty} {Γ : Ctx Ty} {s : Ty} (t : Tm S Γ s) :
    ren Thinning.id t = t :=
  traverse_renEnv_id t

/-- Renaming along a composite thinning is the composite of the renamings. -/
theorem ren_comp {S : BinderSig Ty} {Γ Δ Θ : Ctx Ty} {s : Ty} (ρ : Thinning Γ Δ)
    (τ : Thinning Δ Θ) (t : Tm S Γ s) :
    ren (ρ.comp τ) t = ren τ (ren ρ t) :=
  traverse_renEnv_comp t ρ τ

end GebLean.Binding
