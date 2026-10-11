/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.LF.Metatheory.Weakening
public import Mathlib.Data.List.Infix

set_option doc.verso true in
/-!
# Scoping

An expression judged in a context has its free variables among the context's: its renaming
depends only on the renaming's values below the context's length ({lit}`judgeWith_scoped`). In
particular the kind or type of each constant of a formed signature, judged in the empty context,
is closed ({lit}`Sig.ok_closed`), which discharges the hypothesis of weakening
({name}`Geb.LF.judge_rename`). An expression is in scope in a context when it is so, a property
stated by its renamings rather than by a fold of its own ({lit}`ScopedBelow`).

The proof is by induction on the expression, through the inversion of the judgments at a node
({lit}`judgeWith_node_inv`): a judged node's head variable, where it has one, is in the context,
and each child is judged in the context extended by as many types as the node binds over it.

## Main definitions

* {lit}`ScopedBelow` — an expression's renaming depends only on the variables below a bound.

## Main statements

* {lit}`spine_args` — the arguments of a spine that instantiates are checked.
* {lit}`judgeWith_node_inv` — the inversion of the judgments at a node.
* {lit}`judgeWith_scoped` — a judged expression is in the scope of its context.
* {lit}`Sig.ok_closed` — the declarations of a formed signature are closed.

## Tags

logical framework, LF, scoping, closed term
-/

set_option doc.verso true

@[expose] public section

namespace Geb.LF

/-- An expression's renaming depends only on the renaming's values below {lit}`k`: its free
variables are below {lit}`k`. -/
def ScopedBelow (k : ℕ) (e : Expr) : Prop :=
  ∀ ρ σ : ℕ → ℕ, (∀ i < k, ρ i = σ i) → e.rename ρ = e.rename σ

/-- Renamings that agree below {lit}`k` agree, lifted under {lit}`b` binders, below
{lit}`k + b`. -/
theorem iterate_liftR_agree {k : ℕ} {ρ σ : ℕ → ℕ} (h : ∀ i < k, ρ i = σ i) (b : ℕ) :
    ∀ i < k + b, liftR^[b] ρ i = liftR^[b] σ i := by
  intro i hi
  rw [iterate_liftR_apply, iterate_liftR_apply]
  split_ifs with hib
  · rfl
  · rw [h (i - b) (by omega)]

/-- The arguments of a spine along which a classifier instantiates are each checked against a
type. -/
theorem spine_args {J : Expr → Ctx → Mode → Bool} {Γ : Ctx} :
    ∀ (ms : List Expr) (c r : Expr), spine Γ c (ms.map fun m ↦ (m, J m)) = some r →
      ∀ m ∈ ms, ∃ a, J m Γ (.check a) = true :=
  fun ms ↦ ms.rec (motive := fun ms ↦ ∀ (c r : Expr),
      spine Γ c (ms.map fun m ↦ (m, J m)) = some r → ∀ m ∈ ms, ∃ a, J m Γ (.check a) = true)
    (fun _ _ _ m hm ↦ absurd hm List.not_mem_nil)
    (fun m ms ih c r h m' hm' ↦ by
      simp only [spine, List.map_cons, List.foldlM_cons] at h
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
          rcases List.mem_cons.mp hm' with rfl | hm'
          · exact ⟨a, hJ⟩
          · exact ih c' r hr m' hm'
        · simp at hc'
      · simp at hc'
      · simp at hc')

/-- The inversion of the judgments at a node: a judged node's head variable, where it has one,
is in the context, and each child is judged in a context extended by as many types as the node
binds over it. -/
theorem judgeWith_node_inv {eqv : Expr → Expr → Bool} {sig : Sig} {l : Label} {cs : List Expr}
    {Γ : Ctx} {md : Mode} (h : judgeWith eqv sig (RoseTree.node l cs) Γ md = true) :
    (∀ i, l = .app (.var i) → i < Γ.length) ∧
      ∀ (k : ℕ) (hk : k < cs.length), ∃ (Γ' : Ctx) (md' : Mode),
        Γ'.length = Γ.length + l.binders k ∧ judgeWith eqv sig cs[k] Γ' md' = true := by
  rw [judgeWith_node] at h
  have hpi : ∀ {a b : Expr} {ma mb : Mode} {Γb : Ctx}, Γb.length = Γ.length + 1 →
      judgeWith eqv sig a Γ ma = true → judgeWith eqv sig b Γb mb = true →
      ∀ (k : ℕ) (hk : k < [a, b].length), ∃ (Γ' : Ctx) (md' : Mode),
        Γ'.length = Γ.length + Label.pi.binders k ∧ judgeWith eqv sig [a, b][k] Γ' md' = true := by
    intro a b ma mb Γb hΓb ha hb k hk
    rcases k with _ | _ | k
    · exact ⟨Γ, ma, rfl, ha⟩
    · exact ⟨Γb, mb, hΓb, hb⟩
    · exact absurd hk (by simp)
  have hargs : ∀ {hd : Head} {c r : Expr},
      spine Γ c (cs.map fun c ↦ (c, judgeWith eqv sig c)) = some r →
      ∀ (k : ℕ) (hk : k < cs.length), ∃ (Γ' : Ctx) (md' : Mode),
        Γ'.length = Γ.length + (Label.app hd).binders k ∧ judgeWith eqv sig cs[k] Γ' md' = true :=
    fun hs k hk ↦ by
      obtain ⟨a, ha⟩ := spine_args cs _ _ hs cs[k] (List.getElem_mem hk)
      exact ⟨Γ, .check a, rfl, ha⟩
  rcases md with _ | _ | p
  · rcases l with _ | _ | _ | (i | c)
    · rcases cs with _ | ⟨d, cs⟩
      · exact ⟨fun i h ↦ (by cases h), fun k hk ↦ absurd hk (by simp)⟩
      · simp [judgeStep] at h
    · rcases cs with _ | ⟨a, _ | ⟨b, _ | ⟨d, cs⟩⟩⟩
      · simp [judgeStep] at h
      · simp [judgeStep] at h
      · simp only [judgeStep, List.map_cons, List.map_nil, Bool.and_eq_true] at h
        exact ⟨fun i h ↦ (by cases h), hpi (Γb := a :: Γ) rfl h.1 h.2⟩
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
        exact ⟨fun i h ↦ (by cases h), hpi (Γb := a :: Γ) rfl h.1 h.2⟩
      · simp [judgeStep] at h
    · simp [judgeStep] at h
    · simp [judgeStep] at h
    · simp only [judgeStep, beq_iff_eq, Option.bind_eq_some_iff] at h
      obtain ⟨k, -, hs⟩ := h
      exact ⟨fun i h ↦ (by cases h), hargs hs⟩
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
          · refine ⟨fun i h ↦ (by cases h), fun k hk ↦ ?_⟩
            rcases k with _ | k
            · exact ⟨a :: Γ, .check b, rfl, h⟩
            · simp at hk
          · simp at h
        · simp at h
        · simp at h
      · simp [judgeStep] at h
    · simp only [judgeStep, Bool.and_eq_true] at h
      obtain ⟨-, hm⟩ := h
      rcases hC : classOf sig Γ hd with _ | C
      · rw [hC] at hm
        simp at hm
      · rw [hC, Option.bind_some] at hm
        rcases hS : spine Γ C (cs.map fun c ↦ (c, judgeWith eqv sig c)) with _ | A
        · rw [hS] at hm
          simp at hm
        · refine ⟨fun i hi ↦ ?_, hargs hS⟩
          cases hi
          simp only [classOf, Option.map_eq_some_iff] at hC
          obtain ⟨a, ha, -⟩ := hC
          exact (List.getElem?_eq_some_iff.mp ha).1

/-- A judged expression is in the scope of its context. -/
theorem judgeWith_scoped {eqv : Expr → Expr → Bool} {sig : Sig} :
    ∀ (e : Expr) (Γ : Ctx) (md : Mode), judgeWith eqv sig e Γ md = true →
      ScopedBelow Γ.length e :=
  RoseTree.ind fun l cs ih Γ md h ρ σ hρσ ↦ by
    obtain ⟨hvar, hch⟩ := judgeWith_node_inv h
    rw [rename_node, rename_node]
    congr 1
    · rcases l with _ | _ | _ | (i | c)
      · rfl
      · rfl
      · rfl
      · simp only [Label.rename, Head.rename, hρσ i (hvar i rfl)]
      · rfl
    · refine List.ext_getElem (by simp) fun k h₁ h₂ ↦ ?_
      simp only [List.getElem_map, List.getElem_zipIdx, zero_add]
      obtain ⟨Γ', md', hlen, hj⟩ := hch k (by simpa using h₁)
      exact ih _ (List.getElem_mem _) Γ' md' hj _ _ (by
        rw [hlen]
        exact iterate_liftR_agree hρσ _)

/-- An expression in scope below zero is closed: renaming leaves it in place. -/
theorem ScopedBelow.rename_eq {e : Expr} (h : ScopedBelow 0 e) (ρ : ℕ → ℕ) : e.rename ρ = e :=
  (h ρ id fun i hi ↦ absurd hi (Nat.not_lt_zero i)).trans (rename_id e)

/-- The declarations of a formed signature are closed. -/
theorem Sig.ok_closed {sig : Sig} (h : sig.ok = true) : SigClosed sig := by
  intro c a hc ρ
  obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp hc
  rw [Sig.ok, List.all_eq_true] at h
  have hmem : (sig[c], sig.take c) ∈ sig.zip sig.inits := by
    rw [List.mem_iff_getElem]
    refine ⟨c, by simp [List.length_inits]; omega, ?_⟩
    simp [List.getElem_inits]
  have hd := h _ hmem
  simp only [Bool.or_eq_true, IsKind, IsType] at hd
  rcases hd with hd | hd
  · exact ScopedBelow.rename_eq (judgeWith_scoped _ [] _ hd) ρ
  · exact ScopedBelow.rename_eq (judgeWith_scoped _ [] _ hd) ρ

/-- One step of whether an expression's free variables are below a bound, at a node of a label,
from its children's: an application's head variable is below the bound, and each child's free
variables are below the bound raised by the variables the node binds over it. -/
def freeBelowStep (l : Label) (cs : List (ℕ → Bool)) (k : ℕ) : Bool :=
  (match l with
    | .app (.var i) => decide (i < k)
    | _ => true) &&
  (cs.zipIdx.map fun p ↦ p.1 (k + l.binders p.2)).all id

/-- Whether an expression's free variables are below a bound, decided by a fold. -/
def Expr.FreeBelow (e : Expr) (k : ℕ) : Bool := RoseTree.elim freeBelowStep e k

/-- The computation rule of the bound on free variables. -/
theorem freeBelow_node (l : Label) (cs : List Expr) (k : ℕ) :
    Expr.FreeBelow (RoseTree.node l cs) k = freeBelowStep l (cs.map fun c ↦ c.FreeBelow) k := by
  unfold Expr.FreeBelow
  rw [RoseTree.elim_node]

/-- The instantiation along a spine depends on its arguments' checks only. -/
theorem spine_congr {Γ Γ' : Ctx} :
    ∀ (ms : List Expr) (J J' : Expr → Ctx → Mode → Bool) (c : Expr),
      (∀ m ∈ ms, ∀ a, J m Γ (.check a) = J' m Γ' (.check a)) →
      spine Γ c (ms.map fun m ↦ (m, J m)) = spine Γ' c (ms.map fun m ↦ (m, J' m)) :=
  fun ms ↦ ms.rec (motive := fun ms ↦ ∀ (J J' : Expr → Ctx → Mode → Bool) (c : Expr),
      (∀ m ∈ ms, ∀ a, J m Γ (.check a) = J' m Γ' (.check a)) →
      spine Γ c (ms.map fun m ↦ (m, J m)) = spine Γ' c (ms.map fun m ↦ (m, J' m)))
    (fun _ _ _ _ ↦ rfl)
    (fun m ms ih J J' c h ↦ by
      simp only [spine, List.map_cons, List.foldlM_cons]
      obtain ⟨l, cs, rfl⟩ := exists_node c
      rw [RoseTree.label_node, RoseTree.children_node]
      rcases l with _ | _ | _ | _
      · rfl
      · rcases cs with _ | ⟨a, _ | ⟨b, _ | ⟨d, cs⟩⟩⟩
        · rfl
        · rfl
        · simp only
          rw [h m (by simp) a]
          by_cases hJ : J' m Γ' (.check a) = true
          · simp only [hJ, ↓reduceIte]
            cases hsub (Expr.erase a) m b 0 with
            | none => rfl
            | some c' => exact ih J J' c' fun m' hm' ↦ h m' (List.mem_cons_of_mem _ hm')
          · simp only [hJ, Bool.false_eq_true, ↓reduceIte]
            rfl
        · rfl
      · rfl
      · rfl)

/-- An expression's free variables are below a bound exactly when its head variable, where it
has one, is, and each child's are below the bound raised by the variables the node binds over
it. -/
theorem freeBelow_node_iff {l : Label} {cs : List Expr} {k : ℕ} :
    Expr.FreeBelow (RoseTree.node l cs) k = true ↔
      (∀ i, l = .app (.var i) → i < k) ∧
        ∀ (idx : ℕ) (h : idx < cs.length), Expr.FreeBelow cs[idx] (k + l.binders idx) = true := by
  have hall : ((cs.map fun c ↦ c.FreeBelow).zipIdx.map fun p ↦ p.1 (k + l.binders p.2)).all id =
      true ↔ ∀ (idx : ℕ) (h : idx < cs.length),
        Expr.FreeBelow cs[idx] (k + l.binders idx) = true := by
    rw [List.all_eq_true]
    constructor
    · intro h idx hidx
      have := h _ (List.getElem_mem (l := (cs.map fun c ↦ c.FreeBelow).zipIdx.map
        fun p ↦ p.1 (k + l.binders p.2)) (n := idx) (by simpa using hidx))
      simpa only [List.getElem_map, List.getElem_zipIdx, zero_add, id] using this
    · intro h x hx
      obtain ⟨idx, hidx, rfl⟩ := List.mem_iff_getElem.mp hx
      simp only [List.getElem_map, List.getElem_zipIdx, zero_add, id]
      exact h idx (by simpa using hidx)
  rw [freeBelow_node]
  rcases l with _ | _ | _ | (i | c)
  · rw [freeBelowStep, Bool.true_and, hall]
    · exact ⟨fun h ↦ ⟨(fun _ h' ↦ nomatch h'), h⟩, fun h ↦ h.2⟩
    · exact fun _ h ↦ nomatch h
  · rw [freeBelowStep, Bool.true_and, hall]
    · exact ⟨fun h ↦ ⟨(fun _ h' ↦ nomatch h'), h⟩, fun h ↦ h.2⟩
    · exact fun _ h ↦ nomatch h
  · rw [freeBelowStep, Bool.true_and, hall]
    · exact ⟨fun h ↦ ⟨(fun _ h' ↦ nomatch h'), h⟩, fun h ↦ h.2⟩
    · exact fun _ h ↦ nomatch h
  · rw [freeBelowStep, Bool.and_eq_true, hall, decide_eq_true_eq]
    exact ⟨fun h ↦ ⟨fun i' h' ↦ (by cases h'; exact h.1), h.2⟩, fun h ↦ ⟨h.1 i rfl, h.2⟩⟩
  · rw [freeBelowStep, Bool.true_and, hall]
    · exact ⟨fun h ↦ ⟨(fun _ h' ↦ nomatch h'), h⟩, fun h ↦ h.2⟩
    · exact fun _ h ↦ nomatch h

/-- The judgments of an expression depend on its context only at its free variables: in two
contexts that agree below a bound on its free variables, they agree. -/
theorem judgeWith_congr_ctx {eqv : Expr → Expr → Bool} {sig : Sig} :
    ∀ (e : Expr) (Γ Γ' : Ctx) (k : ℕ) (md : Mode), (∀ i < k, Γ[i]? = Γ'[i]?) →
      e.FreeBelow k = true → judgeWith eqv sig e Γ md = judgeWith eqv sig e Γ' md :=
  RoseTree.ind fun l cs ih Γ Γ' k md hΓ hfb ↦ by
    obtain ⟨hhead, hc⟩ := freeBelow_node_iff.mp hfb
    have hext : ∀ a, ∀ i < k + 1, (a :: Γ)[i]? = (a :: Γ')[i]? := fun a i hi ↦ by
      rcases i with _ | i
      · rfl
      · exact hΓ i (by omega)
    have hargs : (∀ i, l ≠ .pi ∧ l ≠ .lam) → ∀ m ∈ cs, ∀ a,
        judgeWith eqv sig m Γ (.check a) = judgeWith eqv sig m Γ' (.check a) := fun hl m hm a ↦ by
      obtain ⟨idx, hidx, rfl⟩ := List.mem_iff_getElem.mp hm
      have hb : l.binders idx = 0 := by
        rcases l with _ | _ | _ | _
        · rfl
        · exact absurd rfl (hl 0).1
        · exact absurd rfl (hl 0).2
        · rfl
      have := hc idx hidx
      rw [hb, Nat.add_zero] at this
      exact ih _ hm Γ Γ' k _ hΓ this
    have hclass : ∀ h : Head, (∀ i, h = .var i → i < k) → classOf sig Γ h = classOf sig Γ' h :=
      fun h hh ↦ by
        rcases h with i | c
        · change Γ[i]?.map _ = Γ'[i]?.map _
          rw [hΓ i (hh i rfl)]
        · rfl
    rw [judgeWith_node]
    rcases md with _ | _ | p
    · rcases l with _ | _ | _ | (i | c)
      · rcases cs with _ | ⟨d, cs⟩
        · rfl
        · rfl
      · rcases cs with _ | ⟨a, _ | ⟨b, _ | ⟨d, cs⟩⟩⟩
        · rfl
        · rfl
        · simp only [judgeStep, List.map_cons, List.map_nil]
          rw [ih a (by simp) Γ Γ' k _ hΓ (by simpa [Label.binders] using hc 0 (by simp)),
            ih b (by simp) _ _ (k + 1) _ (hext a) (by simpa [Label.binders] using hc 1 (by simp))]
        · rfl
      · rfl
      · rfl
      · rfl
    · rcases l with _ | _ | _ | (i | c)
      · rfl
      · rcases cs with _ | ⟨a, _ | ⟨b, _ | ⟨d, cs⟩⟩⟩
        · rfl
        · rfl
        · simp only [judgeStep, List.map_cons, List.map_nil]
          rw [ih a (by simp) Γ Γ' k _ hΓ (by simpa [Label.binders] using hc 0 (by simp)),
            ih b (by simp) _ _ (k + 1) _ (hext a) (by simpa [Label.binders] using hc 1 (by simp))]
        · rfl
      · rfl
      · rfl
      · simp only [judgeStep]
        rcases sig[c]? with _ | K
        · rfl
        · simp only [Option.bind_some]
          rw [spine_congr (Γ := Γ) (Γ' := Γ') cs _ _ K (hargs fun _ ↦ ⟨nofun, nofun⟩)]
    · rcases l with _ | _ | _ | hd
      · rfl
      · rfl
      · rcases cs with _ | ⟨m, _ | ⟨d, cs⟩⟩
        · rfl
        · obtain ⟨pl, pcs, rfl⟩ := exists_node p
          simp only [judgeStep, List.map_cons, List.map_nil, RoseTree.label_node,
            RoseTree.children_node]
          rcases pl with _ | _ | _ | _
          · rfl
          · rcases pcs with _ | ⟨a, _ | ⟨b, _ | ⟨d', pcs⟩⟩⟩
            · rfl
            · rfl
            · simp only
              exact ih m (by simp) _ _ (k + 1) _ (hext a)
                (by simpa [Label.binders] using hc 0 (by simp))
            · rfl
          · rfl
          · rfl
        · rfl
      · simp only [judgeStep]
        rw [hclass hd fun i h ↦ hhead i (by rw [h])]
        rcases classOf sig Γ' hd with _ | C
        · rfl
        · simp only [Option.bind_some]
          rw [spine_congr (Γ := Γ) (Γ' := Γ') cs _ _ C (hargs fun _ ↦ ⟨nofun, nofun⟩)]

/-- An expression whose free variables are below a bound is in scope below it. -/
theorem freeBelow_scoped : ∀ (e : Expr) (k : ℕ), e.FreeBelow k = true → ScopedBelow k e :=
  RoseTree.ind fun l cs ih k hfb ρ σ hρσ ↦ by
    obtain ⟨hhead, hc⟩ := freeBelow_node_iff.mp hfb
    rw [rename_node, rename_node]
    congr 1
    · rcases l with _ | _ | _ | (i | c)
      · rfl
      · rfl
      · rfl
      · simp only [Label.rename, Head.rename, hρσ i (hhead i rfl)]
      · rfl
    · refine List.ext_getElem (by simp) fun idx h₁ h₂ ↦ ?_
      simp only [List.getElem_map, List.getElem_zipIdx, zero_add]
      exact ih _ (List.getElem_mem _) _ (hc idx (by simpa using h₁)) _ _
        (iterate_liftR_agree hρσ _)

/-- A judged expression's free variables are below its context's length. -/
theorem judgeWith_freeBelow {eqv : Expr → Expr → Bool} {sig : Sig} :
    ∀ (e : Expr) (Γ : Ctx) (md : Mode), judgeWith eqv sig e Γ md = true →
      e.FreeBelow Γ.length = true :=
  RoseTree.ind fun l cs ih Γ md h ↦ by
    obtain ⟨hvar, hch⟩ := judgeWith_node_inv h
    refine freeBelow_node_iff.mpr ⟨hvar, fun idx hidx ↦ ?_⟩
    obtain ⟨Γ', md', hlen, hj⟩ := hch idx hidx
    rw [← hlen]
    exact ih _ (List.getElem_mem _) Γ' md' hj

/-- Renaming leaves a closed expression in place. -/
theorem rename_closed {e : Expr} (h : e.FreeBelow 0 = true) (ρ : ℕ → ℕ) : e.rename ρ = e :=
  ScopedBelow.rename_eq (freeBelow_scoped e 0 h) ρ

/-- Substitution into a closed expression leaves it in place, whatever the reduction. -/
theorem hsubWith_closed {e : Expr} (h : e.FreeBelow 0 = true)
    (red : Expr → List Expr → Option Expr) (n : Expr) (j : ℕ) : hsubWith red e n j = some e := by
  have := hsubWith_vacuous red e n j
  rwa [rename_closed h] at this

end Geb.LF

end
