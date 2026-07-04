import GebLean.Binding.Signature

/-!
# Context thinnings

Context thinnings (order-preserving embeddings, OPEs): first-order data on
`Ctx`, not `PolyFix` syntax (decision 8 does not apply). Each step of a
thinning either keeps an entry (present on both sides, at the head) or
drops an entry (present only on the wider side, at the head); composing
these steps embeds the shorter context's variables into the wider one
while preserving their relative order. `List.Sublist` is the analogous
`Prop`-valued relation on lists, but a `Prop` cannot compute `Thinning.app`
into the `Type`-valued `Var`, so `Thinning` is a bespoke `Type`-valued
inductive instead.

## Main definitions

* `Thinning` — the keep/drop OPE inductive on `Ctx Ty`.
* `Thinning.id` — the identity thinning.
* `Thinning.weak` — the thinning dropping one freshly-prepended entry.
* `Thinning.lift` — extending a thinning by keeping one shared head entry.
* `Thinning.weakAppend` — the suffix embedding `Γ ⊆ Γ ++ Ξ`, needed by the
  under-binder weakening of the append-at-end context-extension convention.
* `Thinning.comp` — thinning composition.
* `Thinning.app` — the action of a thinning on a variable, transporting its
  position and sort proof from the narrower context to the wider one.

## Main statements

* `Thinning.app_id` — `Thinning.id` acts as the identity on variables.
* `Thinning.app_comp` — `Thinning.app` is functorial in thinning composition.

## References

The keep/drop presentation of order-preserving embeddings follows G.
Allais, R. Atkey, J. Chapman, C. McBride, and J. McKinna, "A type and
scope safe universe of syntaxes with binding: their semantics and
proofs", Proceedings of the ACM on Programming Languages 2 (ICFP), 2018,
DOI `10.1145/3236785`.
-/

namespace GebLean.Binding

universe u

variable {Ty : Type u}

/-- A context thinning: an order-preserving embedding of `Γ` into `Δ`,
presented as a sequence of keep/drop steps read off the head of `Δ`. A
`keep` step consumes a shared head entry from both contexts; a `drop`
step consumes a head entry present only in `Δ`. First-order data on `Ctx`,
exempt from decision 8. -/
inductive Thinning : Ctx Ty → Ctx Ty → Type u where
  /-- The empty thinning, embedding the empty context into itself. -/
  | nil : Thinning [] []
  /-- Keep a shared head entry `s`, extending a thinning of the tails. -/
  | keep {Γ Δ : Ctx Ty} (s : Ty) : Thinning Γ Δ → Thinning (s :: Γ) (s :: Δ)
  /-- Drop a head entry `s` present only on the wider side. -/
  | drop {Γ Δ : Ctx Ty} (s : Ty) : Thinning Γ Δ → Thinning Γ (s :: Δ)

/-- The identity thinning, keeping every entry of `Γ`. -/
def Thinning.id : {Γ : Ctx Ty} → Thinning Γ Γ
  | [] => Thinning.nil
  | _ :: Γ => Thinning.keep _ (Thinning.id (Γ := Γ))

/-- The thinning dropping one freshly-prepended head entry, embedding `Γ`
into `s :: Γ`. -/
def Thinning.weak {Γ : Ctx Ty} {s : Ty} : Thinning Γ (s :: Γ) :=
  Thinning.drop s Thinning.id

/-- Extend a thinning by one shared head entry `s`. -/
def Thinning.lift {Γ Δ : Ctx Ty} {s : Ty} (ρ : Thinning Γ Δ) :
    Thinning (s :: Γ) (s :: Δ) :=
  Thinning.keep s ρ

/-- The thinning embedding every entry of `Γ` into the append-at-end
extension `Γ ++ Ξ`: keep every entry of `Γ` (peeled off the front), then
drop every entry of `Ξ` (the whole of the remaining suffix). This is the
suffix embedding the under-binder weakening of the append-at-end context
convention needs. -/
def Thinning.weakAppend : {Γ Ξ : Ctx Ty} → Thinning Γ (Γ ++ Ξ)
  | [], Ξ => dropAll Ξ
  | _ :: Γ, Ξ => Thinning.keep _ (Thinning.weakAppend (Γ := Γ) (Ξ := Ξ))
where
  /-- Drop every entry of `Ξ`, embedding the empty context into it. -/
  dropAll : (Ξ : Ctx Ty) → Thinning [] Ξ
    | [] => Thinning.nil
    | s :: Ξ => Thinning.drop s (dropAll Ξ)

/-- Thinning composition: recursion on the second thinning. -/
def Thinning.comp {Γ Δ Θ : Ctx Ty} (ρ : Thinning Γ Δ) :
    Thinning Δ Θ → Thinning Γ Θ
  | Thinning.nil => ρ
  | Thinning.drop s τ' => Thinning.drop s (Thinning.comp ρ τ')
  | Thinning.keep s τ' =>
      match ρ with
      | Thinning.keep _ ρ' => Thinning.keep s (Thinning.comp ρ' τ')
      | Thinning.drop _ ρ' => Thinning.drop s (Thinning.comp ρ' τ')

/-- Shift a variable's position past a freshly-prepended head entry `t`,
preserving its sort proof. The shifted position `x.1.succ` reads off the
same entry of `t :: Γ` that `x.1` read off `Γ`, definitionally. -/
def Var.succ {Γ : Ctx Ty} (t : Ty) {s : Ty} (x : Var Γ s) : Var (t :: Γ) s :=
  ⟨x.1.succ, x.2⟩

/-- The action of a thinning on a variable: transports the variable's
`Fin` position (and its sort proof) from the narrower context to the
wider one, by recursion on the thinning. -/
def Thinning.app {Γ Δ : Ctx Ty} {s : Ty} : Thinning Γ Δ → Var Γ s → Var Δ s
  | Thinning.nil, x => x.1.elim0
  | Thinning.keep _ ρ', ⟨i, hi⟩ => by
      cases i using Fin.cases with
      | zero => exact ⟨0, hi⟩
      | succ i' => exact Var.succ _ (Thinning.app ρ' ⟨i', hi⟩)
  | Thinning.drop _ ρ', x => Var.succ _ (Thinning.app ρ' x)

/-- `Thinning.app` of the identity thinning is the identity on variables. -/
theorem Thinning.app_id : {Γ : Ctx Ty} → {s : Ty} → (x : Var Γ s) → Thinning.id.app x = x
  | [], _, x => x.1.elim0
  | _ :: Γ, s, ⟨i, hi⟩ => by
      cases i using Fin.cases with
      | zero => rfl
      | succ i' => exact congrArg (Var.succ _) (Thinning.app_id (Γ := Γ) ⟨i', hi⟩)

/-- `Thinning.app` is functorial in thinning composition. -/
theorem Thinning.app_comp : {Γ Δ Θ : Ctx Ty} → {s : Ty} → (ρ : Thinning Γ Δ) →
    (τ : Thinning Δ Θ) → (x : Var Γ s) → (ρ.comp τ).app x = τ.app (ρ.app x)
  | _, _, _, _, ρ, Thinning.nil, x => (ρ.app x).1.elim0
  | _, _, _, _, ρ, Thinning.drop _ τ', x =>
      congrArg (Var.succ _) (Thinning.app_comp ρ τ' x)
  | _, _, _, _, Thinning.keep _ ρ', Thinning.keep _ τ', ⟨i, hi⟩ => by
      cases i using Fin.cases with
      | zero => rfl
      | succ i' => exact congrArg (Var.succ _) (Thinning.app_comp ρ' τ' ⟨i', hi⟩)
  | _, _, _, _, Thinning.drop _ ρ', Thinning.keep _ τ', x =>
      congrArg (Var.succ _) (Thinning.app_comp ρ' τ' x)

end GebLean.Binding
