/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Prototypes.LF.Metatheory.Weakening

set_option doc.verso true in
/-!
# Renaming on the variables an expression mentions

The judgments of canonical LF are stable under a renaming that respects the types of the
variables an expression mentions ({lit}`judgeWith_renameOn`), whatever it does to the others: the
judgments consult the context only at a node's head variable, so that a renaming need respect
the types of the variables that occur. Strengthening, the removal from the context of a variable
an expression does not mention, is the instance at a renaming that skips the removed variable;
\[HarperLicata2007\], Section 2.4.1, transports canonical forms between contexts that differ
in declarations their type does not depend on by subordination.

## Main definitions

* {lit}`liftB` — a predicate on variables lifted under a binder.
* {lit}`Expr.OccursOnly` — whether every variable an expression mentions satisfies a predicate.
* {lit}`CtxRenOn` — a renaming respects the types of the variables satisfying a predicate.

## Main statements

* {lit}`occursOnly_node_iff` — the computation of {lit}`Expr.OccursOnly` at a node.
* {lit}`occursOnly_mono` — {lit}`Expr.OccursOnly` is monotone in its predicate.
* {lit}`judgeWith_renameOn` — the judgments are stable under a renaming that respects the types
  of the variables an expression mentions.

## References

* \[HarperLicata2007\], Section 2.4.1.

## Tags

logical framework, LF, renaming, strengthening
-/

set_option doc.verso true

@[expose] public section

namespace Geb.LF

/-- A predicate on variables lifted under a binder: the bound variable satisfies it, and each
other variable as it did outside. -/
def liftB (S : ℕ → Bool) : ℕ → Bool := fun i ↦ match i with
  | 0 => true
  | j + 1 => S j

/-- One step of whether every variable an expression mentions satisfies a predicate: the node's
head variable, where it has one, and those of each child, under the variables the node binds over
it. -/
def occursOnlyStep (l : Label) (cs : List ((ℕ → Bool) → Bool)) (S : ℕ → Bool) : Bool :=
  (match l with
    | .app (.var i) => S i
    | _ => true) &&
  (cs.zipIdx.map fun p ↦ p.1 (liftB^[l.binders p.2] S)).all id

/-- Whether every variable an expression mentions satisfies a predicate. -/
def Expr.OccursOnly (e : Expr) (S : ℕ → Bool) : Bool := RoseTree.elim occursOnlyStep e S

/-- The computation rule of {name}`Geb.LF.Expr.OccursOnly`. -/
theorem occursOnly_node (l : Label) (cs : List Expr) (S : ℕ → Bool) :
    Expr.OccursOnly (RoseTree.node l cs) S =
      occursOnlyStep l (cs.map fun c ↦ Expr.OccursOnly c) S := by
  unfold Expr.OccursOnly
  rw [RoseTree.elim_node]

/-- Every variable a node mentions satisfies a predicate exactly when its head variable does,
where it has one, and every variable each child mentions satisfies the predicate lifted under the
variables the node binds over it. -/
theorem occursOnly_node_iff {l : Label} {cs : List Expr} {S : ℕ → Bool} :
    Expr.OccursOnly (RoseTree.node l cs) S = true ↔
      (∀ i, l = .app (.var i) → S i = true) ∧
        ∀ (idx : ℕ) (h : idx < cs.length),
          Expr.OccursOnly cs[idx] (liftB^[l.binders idx] S) = true := by
  have hall : ((cs.map fun c ↦ Expr.OccursOnly c).zipIdx.map
      fun p ↦ p.1 (liftB^[l.binders p.2] S)).all id = true ↔
      ∀ (idx : ℕ) (h : idx < cs.length),
        Expr.OccursOnly cs[idx] (liftB^[l.binders idx] S) = true := by
    rw [List.all_eq_true]
    constructor
    · intro h idx hidx
      have := h _ (List.getElem_mem (l := (cs.map fun c ↦ Expr.OccursOnly c).zipIdx.map
        fun p ↦ p.1 (liftB^[l.binders p.2] S)) (n := idx) (by simpa using hidx))
      simpa only [List.getElem_map, List.getElem_zipIdx, zero_add, id] using this
    · intro h x hx
      obtain ⟨idx, hidx, rfl⟩ := List.mem_iff_getElem.mp hx
      simp only [List.getElem_map, List.getElem_zipIdx, zero_add, id]
      exact h idx (by simpa using hidx)
  rw [occursOnly_node]
  rcases l with _ | _ | _ | (i | c)
  · rw [occursOnlyStep, Bool.true_and, hall]
    · exact ⟨fun h ↦ ⟨(fun _ h' ↦ nomatch h'), h⟩, fun h ↦ h.2⟩
    · exact fun _ h ↦ nomatch h
  · rw [occursOnlyStep, Bool.true_and, hall]
    · exact ⟨fun h ↦ ⟨(fun _ h' ↦ nomatch h'), h⟩, fun h ↦ h.2⟩
    · exact fun _ h ↦ nomatch h
  · rw [occursOnlyStep, Bool.true_and, hall]
    · exact ⟨fun h ↦ ⟨(fun _ h' ↦ nomatch h'), h⟩, fun h ↦ h.2⟩
    · exact fun _ h ↦ nomatch h
  · rw [occursOnlyStep, Bool.and_eq_true, hall]
    exact ⟨fun h ↦ ⟨fun i' h' ↦ (by cases h'; exact h.1), h.2⟩, fun h ↦ ⟨h.1 i rfl, h.2⟩⟩
  · rw [occursOnlyStep, Bool.true_and, hall]
    · exact ⟨fun h ↦ ⟨(fun _ h' ↦ nomatch h'), h⟩, fun h ↦ h.2⟩
    · exact fun _ h ↦ nomatch h

/-- Every variable an expression mentions satisfies any predicate weaker than one it satisfies. -/
theorem occursOnly_mono : ∀ (e : Expr) {S S' : ℕ → Bool}, (∀ i, S i = true → S' i = true) →
    e.OccursOnly S = true → e.OccursOnly S' = true :=
  RoseTree.ind fun l cs ih S S' hSS' h ↦ by
    have hlift : ∀ b i, (liftB^[b] S) i = true → (liftB^[b] S') i = true := fun b ↦
      Nat.rec (motive := fun b ↦ ∀ i, (liftB^[b] S) i = true → (liftB^[b] S') i = true) hSS'
        (fun b ihb i hi ↦ by
          rw [Function.iterate_succ_apply'] at hi ⊢
          rcases i with _ | i
          · rfl
          · exact ihb i hi) b
    obtain ⟨hhead, hch⟩ := occursOnly_node_iff.mp h
    exact occursOnly_node_iff.mpr ⟨fun i hi ↦ hSS' i (hhead i hi), fun idx hidx ↦
      ih _ (List.getElem_mem hidx) (hlift _) (hch idx hidx)⟩

/-- A renaming of variables from one context to another respects the types of the variables that
satisfy a predicate. -/
def CtxRenOn (S : ℕ → Bool) (Γ Δ : Ctx) (ρ : ℕ → ℕ) : Prop :=
  ∀ (i : ℕ) (a : Expr), S i = true → varType Γ i = some a → varType Δ (ρ i) = some (a.rename ρ)

/-- A renaming that respects the types of the variables satisfying a predicate, lifted under a
binder, respects those of the variables satisfying the lifted predicate in the contexts extended
by a type and its renaming. -/
theorem CtxRenOn.lift {S : ℕ → Bool} {Γ Δ : Ctx} {ρ : ℕ → ℕ} (h : CtxRenOn S Γ Δ ρ) (a : Expr) :
    CtxRenOn (liftB S) (a :: Γ) (a.rename ρ :: Δ) (liftR ρ) := by
  intro i b hi hb
  rcases i with _ | i
  · simp only [varType, List.getElem?_cons_zero, Option.map_some, Option.some.injEq] at hb
    subst hb
    change varType (a.rename ρ :: Δ) 0 = _
    simp only [varType, List.getElem?_cons_zero, Option.map_some, Option.some.injEq,
      rename_rename]
    congr 1
  · simp only [varType, List.getElem?_cons_succ] at hb
    obtain ⟨a', ha', rfl⟩ := Option.map_eq_some_iff.mp hb
    have h' := h i (a'.rename (· + (i + 1))) hi (by simp [varType, ha'])
    obtain ⟨b', hb', hb'e⟩ := Option.map_eq_some_iff.mp h'
    change varType (a.rename ρ :: Δ) (ρ i + 1) = _
    simp only [varType, List.getElem?_cons_succ, hb', Option.map_some, Option.some.injEq]
    have := congrArg (fun e ↦ e.rename Nat.succ) hb'e
    simp only [rename_rename] at this ⊢
    convert this using 2

/-- The classifier of a renamed head, where its variable satisfies the predicate on which the
renaming respects types, is the renamed classifier. -/
theorem classOf_renameOn {sig : Sig} (hsig : SigClosed sig) {S : ℕ → Bool} {Γ Δ : Ctx}
    {ρ : ℕ → ℕ} (hρ : CtxRenOn S Γ Δ ρ) {h : Head} (hS : ∀ i, h = .var i → S i = true)
    {a : Expr} (ha : classOf sig Γ h = some a) :
    classOf sig Δ (h.rename ρ) = some (a.rename ρ) := by
  rcases h with i | c
  · exact hρ i a (hS i rfl) ha
  · change sig[c]? = some (a.rename ρ)
    rw [hsig c a ha ρ]
    exact ha

/-- The judgments are stable under a renaming that respects the types of the variables an
expression mentions, for an equality of types that renaming preserves, and a signature of closed
declarations. -/
theorem judgeWith_renameOn {eqv : Expr → Expr → Bool}
    (heqv : ∀ a b ρ, eqv a b = true → eqv (a.rename ρ) (b.rename ρ) = true)
    {sig : Sig} (hsig : SigClosed sig) :
    ∀ (e : Expr) (S : ℕ → Bool) (Γ Δ : Ctx) (ρ : ℕ → ℕ) (md : Mode), CtxRenOn S Γ Δ ρ →
      e.OccursOnly S = true → judgeWith eqv sig e Γ md = true →
        judgeWith eqv sig (e.rename ρ) Δ (md.rename ρ) = true :=
  RoseTree.ind fun l cs ih S Γ Δ ρ md hρ ho h ↦ by
    obtain ⟨hhead, hch⟩ := occursOnly_node_iff.mp ho
    rw [judgeWith_node] at h
    rw [rename_node, judgeWith_node]
    have happ : ∀ (hd : Head), l = .app hd → ∀ m ∈ cs, ∀ a,
        judgeWith eqv sig m Γ (.check a) = true →
          judgeWith eqv sig (Expr.rename m ρ) Δ (.check (a.rename ρ)) = true := by
      intro hd hl m hm a ha
      obtain ⟨idx, hidx, rfl⟩ := List.mem_iff_getElem.mp hm
      have := hch idx hidx
      rw [hl, Label.binders_app, Function.iterate_zero_apply] at this
      exact ih _ hm S Γ Δ ρ (.check a) hρ this ha
    have h₀ : ∀ (idx : ℕ) (hidx : idx < cs.length), l.binders idx = 0 →
        Expr.OccursOnly cs[idx] S = true := fun idx hidx hb ↦ by
      simpa [hb] using hch idx hidx
    have h₁ : ∀ (idx : ℕ) (hidx : idx < cs.length), l.binders idx = 1 →
        Expr.OccursOnly cs[idx] (liftB S) = true := fun idx hidx hb ↦ by
      simpa [hb] using hch idx hidx
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
          exact ⟨ih a (by simp) S Γ Δ ρ .type hρ (h₀ 0 (by simp) rfl) h.1,
            ih b (by simp) (liftB S) (a :: Γ) (Expr.rename a ρ :: Δ) (liftR ρ) .kind
              (hρ.lift a) (h₁ 1 (by simp) rfl) h.2⟩
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
          exact ⟨ih a (by simp) S Γ Δ ρ .type hρ (h₀ 0 (by simp) rfl) h.1,
            ih b (by simp) (liftB S) (a :: Γ) (Expr.rename a ρ :: Δ) (liftR ρ) .type
              (hρ.lift a) (h₁ 1 (by simp) rfl) h.2⟩
        · simp [judgeStep] at h
      · simp [judgeStep] at h
      · simp [judgeStep] at h
      · simp only [judgeStep, beq_iff_eq, Option.bind_eq_some_iff] at h
        obtain ⟨k, hk, hs⟩ := h
        simp only [Mode.rename, judgeStep, Label.rename, Head.rename, Label.binders_app,
          Function.iterate_zero_apply, zipIdx_map_fst fun m : Expr ↦ m.rename ρ, beq_iff_eq,
          Option.bind_eq_some_iff]
        refine ⟨k, hk, ?_⟩
        have := spine_rename cs k Expr.type hs (happ (.const c) rfl)
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
              exact ih m (by simp) (liftB S) (a :: Γ) (Expr.rename a ρ :: Δ) (liftR ρ)
                (.check b) (hρ.lift a) (h₁ 0 (by simp) rfl) h
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
            rw [classOf_renameOn hsig hρ (fun i hi ↦ hhead i (by rw [hi])) hC, Option.bind_some,
              spine_rename cs C A hS (happ hd rfl)]
            exact heqv A p ρ hm

/-- The judgments, types compared as expressions, are stable under a renaming that respects the
types of the variables an expression mentions. -/
theorem judge_renameOn {sig : Sig} (hsig : SigClosed sig) (e : Expr) {S : ℕ → Bool}
    {Γ Δ : Ctx} {ρ : ℕ → ℕ} (md : Mode) (hρ : CtxRenOn S Γ Δ ρ) (ho : e.OccursOnly S = true)
    (h : judge sig e Γ md = true) : judge sig (e.rename ρ) Δ (md.rename ρ) = true :=
  judgeWith_renameOn (fun a b ρ hab ↦ by rw [beq_iff_eq] at hab ⊢; rw [hab]) hsig e S Γ Δ ρ md hρ
    ho h

end Geb.LF

end
