/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Prototypes.LF.Metatheory.HSubstRename
public import Geb.Prototypes.LF.Typing

set_option doc.verso true in
/-!
# Weakening

The judgments of canonical LF are stable under renaming (\[HarperLicata2007\], Lemmas 2.6
and 2.7, weakening and exchange, in de Bruijn form): an expression judged in a context is judged,
renamed, in any context into which the renaming maps each variable to one of the renamed type
({lit}`CtxRen`). Weakening by a variable is the renaming by the successor into the extended
context ({lit}`CtxRen.succ`). The constants of the signature are taken closed, so that renaming
leaves their kinds and types in place.

The instantiation of a classifier along a spine commutes with renaming ({lit}`spine_rename`),
by the commutation of hereditary substitution with renaming ({name}`Geb.LF.hsub_rename`) and the
invariance of erasure ({name}`Geb.LF.erase_rename`); the judgments then by induction on the
expression ({lit}`judge_rename`).

## Main definitions

* {lit}`Mode.rename` — the renaming of the type a mode checks against.
* {lit}`CtxRen` — a renaming between contexts that respects the variables' types.
* {lit}`SigClosed` — the kinds and types of the constants are closed.

## Main statements

* {lit}`CtxRen.lift`, {lit}`CtxRen.succ` — renamings under a binder, and weakening.
* {lit}`spine_rename` — the instantiation along a spine commutes with renaming.
* {lit}`judgeWith_rename`, {lit}`judge_rename` — the judgments are stable under renaming.
* {lit}`judge_shift` — weakening by a variable.

## References

* \[HarperLicata2007\], Section 2.3.

## Tags

logical framework, LF, weakening, exchange, renaming
-/

set_option doc.verso true

@[expose] public section

namespace Geb.LF

/-- The renaming of the type a mode checks against. -/
def Mode.rename (ρ : ℕ → ℕ) : Mode → Mode
  | .kind => .kind
  | .type => .type
  | .check a => .check (a.rename ρ)

/-- The type of a variable in a context, weakened past the variables declared after it. -/
def varType (Γ : Ctx) (i : ℕ) : Option Expr :=
  Γ[i]?.map fun (a : Expr) ↦ a.rename (· + (i + 1))

/-- A renaming of variables from one context to another respects their types: it maps each
variable to one whose type is the renamed type. -/
def CtxRen (Γ Δ : Ctx) (ρ : ℕ → ℕ) : Prop :=
  ∀ (i : ℕ) (a : Expr), varType Γ i = some a → varType Δ (ρ i) = some (a.rename ρ)

/-- The kinds and types of the constants are closed: renaming leaves them in place. -/
def SigClosed (sig : Sig) : Prop :=
  ∀ (c : ℕ) (a : Expr), sig[c]? = some a → ∀ ρ : ℕ → ℕ, a.rename ρ = a

/-- A renaming that respects types, lifted under a binder, respects the types of the contexts
extended by a type and its renaming. -/
theorem CtxRen.lift {Γ Δ : Ctx} {ρ : ℕ → ℕ} (h : CtxRen Γ Δ ρ) (a : Expr) :
    CtxRen (a :: Γ) (Expr.rename a ρ :: Δ) (liftR ρ) := by
  intro i b hb
  rcases i with _ | i
  · simp only [varType, List.getElem?_cons_zero, Option.map_some, Option.some.injEq] at hb
    subst hb
    change varType (a.rename ρ :: Δ) 0 = _
    simp only [varType, List.getElem?_cons_zero, Option.map_some, Option.some.injEq,
      rename_rename]
    congr 1
  · simp only [varType, List.getElem?_cons_succ] at hb
    obtain ⟨a', ha', rfl⟩ := Option.map_eq_some_iff.mp hb
    have h' := h i (a'.rename (· + (i + 1))) (by simp [varType, ha'])
    obtain ⟨b', hb', hb'e⟩ := Option.map_eq_some_iff.mp h'
    change varType (a.rename ρ :: Δ) (ρ i + 1) = _
    simp only [varType, List.getElem?_cons_succ, hb', Option.map_some, Option.some.injEq]
    have := congrArg (fun e ↦ e.rename Nat.succ) hb'e
    simp only [rename_rename] at this ⊢
    convert this using 2

/-- Weakening by a variable is a renaming that respects types: the successor, into the context
extended by the variable's type. -/
theorem CtxRen.succ (Γ : Ctx) (a : Expr) : CtxRen Γ (a :: Γ) Nat.succ := by
  intro i b hb
  obtain ⟨b', hb', rfl⟩ := Option.map_eq_some_iff.mp hb
  simp only [varType, List.getElem?_cons_succ, hb', Option.map_some, rename_rename]
  rfl

/-- The computation rule of the judgments. -/
theorem judgeWith_node (eqv : Expr → Expr → Bool) (sig : Sig) (l : Label) (cs : List Expr) :
    judgeWith eqv sig (RoseTree.node l cs) =
      judgeStep eqv sig l (cs.map fun c ↦ (c, judgeWith eqv sig c)) :=
  RoseTree.para_node _ l cs

/-- The renaming of a product renames its domain, and its codomain under the binder. -/
theorem rename_pi (a b : Expr) (ρ : ℕ → ℕ) :
    (Expr.pi a b).rename ρ = Expr.pi (a.rename ρ) (b.rename (liftR ρ)) := by
  rw [Expr.pi, rename_node]
  rfl

/-- The renaming of an abstraction renames its body under the binder. -/
theorem rename_lam (m : Expr) (ρ : ℕ → ℕ) :
    (Expr.lam m).rename ρ = Expr.lam (m.rename (liftR ρ)) := by
  rw [Expr.lam, rename_node]
  rfl

/-- The instantiation of a classifier along a spine commutes with renaming, given that each
argument's check does. -/
theorem spine_rename {J : Expr → Ctx → Mode → Bool} {Γ Δ : Ctx} {ρ : ℕ → ℕ} :
    ∀ (ms : List Expr) (c r : Expr), spine Γ c (ms.map fun m ↦ (m, J m)) = some r →
      (∀ m ∈ ms, ∀ a, J m Γ (.check a) = true → J (m.rename ρ) Δ (.check (a.rename ρ)) = true) →
      spine Δ (c.rename ρ) ((ms.map fun m ↦ m.rename ρ).map fun m ↦ (m, J m)) =
        some (r.rename ρ) :=
  fun ms ↦ ms.rec (motive := fun ms ↦ ∀ (c r : Expr),
      spine Γ c (ms.map fun m ↦ (m, J m)) = some r →
      (∀ m ∈ ms, ∀ a, J m Γ (.check a) = true → J (m.rename ρ) Δ (.check (a.rename ρ)) = true) →
      spine Δ (c.rename ρ) ((ms.map fun m ↦ m.rename ρ).map fun m ↦ (m, J m)) =
        some (r.rename ρ))
    (fun c r h _ ↦ by
      simp only [spine, List.map_nil, List.foldlM_nil, Option.pure_def, Option.some.injEq] at h ⊢
      rw [h])
    (fun m ms ih c r h hm ↦ by
      simp only [spine, List.map_cons, List.foldlM_cons, Option.bind_eq_bind] at h ⊢
      obtain ⟨c', hc', hr⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨l, cs, rfl⟩ := exists_node c
      rw [RoseTree.label_node, RoseTree.children_node] at hc'
      rcases l with _ | _ | _ | _
      · simp at hc'
      · rcases cs with _ | ⟨a, _ | ⟨b, _ | ⟨d, cs⟩⟩⟩
        · simp at hc'
        · simp at hc'
        · simp only at hc'
          split_ifs at hc' with hJ
          have hpi : (RoseTree.node Label.pi [a, b] : Expr) = Expr.pi a b := rfl
          rw [hpi, rename_pi, Expr.pi, RoseTree.label_node, RoseTree.children_node]
          simp only
          simp only [hm m (by simp) a hJ, ↓reduceIte]
          rw [erase_rename]
          have hs := hsub_rename (Expr.erase a) b m 0 ρ c' hc'
          simp only [zero_add, Function.iterate_one, Function.iterate_zero_apply] at hs
          rw [hs, Option.bind_some]
          exact ih c' r hr fun m' hm' ↦ hm m' (List.mem_cons_of_mem _ hm')
        · simp at hc'
      · simp at hc'
      · simp at hc')

/-- The classifier of a renamed head is the renamed classifier. -/
theorem classOf_rename {sig : Sig} (hsig : SigClosed sig) {Γ Δ : Ctx} {ρ : ℕ → ℕ}
    (hρ : CtxRen Γ Δ ρ) {h : Head} {a : Expr} (ha : classOf sig Γ h = some a) :
    classOf sig Δ (h.rename ρ) = some (a.rename ρ) := by
  rcases h with i | c
  · exact hρ i a ha
  · change sig[c]? = some (a.rename ρ)
    rw [hsig c a ha ρ]
    exact ha

/-- Renaming preserves whether an expression is an application. -/
@[simp] theorem IsApp_rename (e : Expr) (ρ : ℕ → ℕ) : IsApp (e.rename ρ) = IsApp e := by
  obtain ⟨l, cs, rfl⟩ := exists_node e
  rw [rename_node, IsApp, IsApp, RoseTree.label_node, RoseTree.label_node]
  rcases l with _ | _ | _ | _ <;> rfl

/-- Pairing with positions and mapping by a function that ignores them is mapping. -/
theorem zipIdx_map_fst {α β : Type} (f : α → β) (l : List α) :
    (l.zipIdx.map fun p ↦ f p.1) = l.map f :=
  List.ext_getElem (by simp) fun k _ _ ↦ by
    simp only [List.getElem_map, List.getElem_zipIdx, zero_add]

/-- The kind of types is left in place by renaming. -/
@[simp] theorem rename_type (ρ : ℕ → ℕ) : Expr.type.rename ρ = Expr.type := by
  rw [Expr.type, rename_node]
  rfl

/-- The judgments are stable under a renaming that respects types, for an equality of types that
renaming preserves, and a signature of closed declarations. -/
theorem judgeWith_rename {eqv : Expr → Expr → Bool}
    (heqv : ∀ a b ρ, eqv a b = true → eqv (a.rename ρ) (b.rename ρ) = true)
    {sig : Sig} (hsig : SigClosed sig) :
    ∀ (e : Expr) (Γ Δ : Ctx) (ρ : ℕ → ℕ) (md : Mode), CtxRen Γ Δ ρ →
      judgeWith eqv sig e Γ md = true → judgeWith eqv sig (e.rename ρ) Δ (md.rename ρ) = true :=
  RoseTree.ind fun l cs ih Γ Δ ρ md hρ h ↦ by
    rw [judgeWith_node] at h
    rw [rename_node, judgeWith_node]
    have hargs : ∀ m ∈ cs, ∀ a, judgeWith eqv sig m Γ (.check a) = true →
        judgeWith eqv sig (Expr.rename m ρ) Δ (.check (a.rename ρ)) = true :=
      fun m hm a ha ↦ ih m hm Γ Δ ρ (.check a) hρ ha
    rcases md with _ | _ | p
    · rcases l with _ | _ | _ | (i | c)
      · rcases cs with _ | ⟨d, cs⟩
        · rfl
        · simp [judgeStep] at h
      · rcases cs with _ | ⟨a, _ | ⟨b, _ | ⟨d, cs⟩⟩⟩
        · simp [judgeStep] at h
        · simp [judgeStep] at h
        · simp only [judgeStep, List.map_cons, List.map_nil, Bool.and_eq_true] at h
          simp only [Mode.rename, judgeStep, List.zipIdx_cons, List.zipIdx_nil, List.map_cons,
            List.map_nil, Label.rename, Label.binders, Function.iterate_zero_apply,
            Function.iterate_one, zero_add, Bool.and_eq_true]
          exact ⟨ih a (by simp) Γ Δ ρ .type hρ h.1,
            ih b (by simp) (a :: Γ) (Expr.rename a ρ :: Δ) (liftR ρ) .kind (hρ.lift a) h.2⟩
        · simp [judgeStep] at h
      · simp [judgeStep] at h
      · simp [judgeStep] at h
      · simp [judgeStep] at h
    · rcases l with _ | _ | _ | (i | c)
      · simp [judgeStep] at h
      · rcases cs with _ | ⟨a, _ | ⟨b, _ | ⟨d, cs⟩⟩⟩
        · simp [judgeStep] at h
        · simp [judgeStep] at h
        · simp only [judgeStep, List.map_cons, List.map_nil, Bool.and_eq_true] at h
          simp only [Mode.rename, judgeStep, List.zipIdx_cons, List.zipIdx_nil, List.map_cons,
            List.map_nil, Label.rename, Label.binders, Function.iterate_zero_apply,
            Function.iterate_one, zero_add, Bool.and_eq_true]
          exact ⟨ih a (by simp) Γ Δ ρ .type hρ h.1,
            ih b (by simp) (a :: Γ) (Expr.rename a ρ :: Δ) (liftR ρ) .type (hρ.lift a) h.2⟩
        · simp [judgeStep] at h
      · simp [judgeStep] at h
      · simp [judgeStep] at h
      · simp only [judgeStep, beq_iff_eq, Option.bind_eq_some_iff] at h
        obtain ⟨k, hk, hs⟩ := h
        simp only [Mode.rename, judgeStep, Label.rename, Head.rename, Label.binders_app,
          Function.iterate_zero_apply, zipIdx_map_fst fun m : Expr ↦ m.rename ρ, beq_iff_eq,
          Option.bind_eq_some_iff]
        refine ⟨k, hk, ?_⟩
        have := spine_rename cs k Expr.type hs hargs
        rwa [hsig c k hk ρ, rename_type] at this
    · rcases l with _ | _ | _ | hd
      · simp [judgeStep] at h
      · simp [judgeStep] at h
      · rcases cs with _ | ⟨m, _ | ⟨d, cs⟩⟩
        · simp [judgeStep] at h
        · obtain ⟨pl, pcs, rfl⟩ := exists_node p
          simp only [judgeStep, List.map_cons, List.map_nil, RoseTree.label_node,
            RoseTree.children_node] at h
          rcases pl with _ | _ | _ | _
          · simp at h
          · rcases pcs with _ | ⟨a, _ | ⟨b, _ | ⟨d', pcs⟩⟩⟩
            · simp at h
            · simp at h
            · simp only [Mode.rename, judgeStep, List.zipIdx_cons, List.zipIdx_nil,
                List.map_cons, List.map_nil, Label.rename, Label.binders,
                Function.iterate_zero_apply, Function.iterate_one, zero_add, rename_node,
                RoseTree.label_node, RoseTree.children_node]
              exact ih m (by simp) (a :: Γ) (Expr.rename a ρ :: Δ) (liftR ρ) (.check b)
                (hρ.lift a) h
            · simp at h
          · simp at h
          · simp at h
        · simp [judgeStep] at h
      · simp only [judgeStep, Bool.and_eq_true] at h
        obtain ⟨hp, hm⟩ := h
        simp only [Mode.rename, judgeStep, Label.rename, Label.binders_app,
          Function.iterate_zero_apply, zipIdx_map_fst fun m : Expr ↦ m.rename ρ, IsApp_rename, hp,
          Bool.true_and]
        rcases hC : classOf sig Γ hd with _ | C
        · rw [hC] at hm
          simp at hm
        · rw [hC, Option.bind_some] at hm
          rcases hS : spine Γ C (cs.map fun c ↦ (c, judgeWith eqv sig c)) with _ | A
          · rw [hS] at hm
            simp at hm
          · rw [hS] at hm
            rw [classOf_rename hsig hρ hC, Option.bind_some, spine_rename cs C A hS hargs]
            exact heqv A p ρ hm

/-- The judgments, types compared as expressions, are stable under a renaming that respects
types. -/
theorem judge_rename {sig : Sig} (hsig : SigClosed sig) (e : Expr) {Γ Δ : Ctx} {ρ : ℕ → ℕ}
    (md : Mode) (hρ : CtxRen Γ Δ ρ) (h : judge sig e Γ md = true) :
    judge sig (e.rename ρ) Δ (md.rename ρ) = true :=
  judgeWith_rename (fun a b ρ hab ↦ by rw [beq_iff_eq] at hab ⊢; rw [hab]) hsig e Γ Δ ρ md hρ h

/-- Weakening: a judgment in a context holds, weakened, in the context extended by a type. -/
theorem judge_shift {sig : Sig} (hsig : SigClosed sig) (e : Expr) (Γ : Ctx) (a : Expr)
    (md : Mode) (h : judge sig e Γ md = true) :
    judge sig e.shift (a :: Γ) (md.rename Nat.succ) = true :=
  judge_rename hsig e md (CtxRen.succ Γ a) h

end Geb.LF

end
