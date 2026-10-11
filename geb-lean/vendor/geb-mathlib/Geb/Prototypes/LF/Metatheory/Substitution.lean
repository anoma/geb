/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Prototypes.LF.Metatheory.Composition
public import Geb.Prototypes.LF.Metatheory.Scope
public import Geb.Prototypes.LF.Metatheory.TypeShape

set_option doc.verso true in
/-!
# The substitution theorem

Hereditary substitutions exist and preserve the judgments (\[HarperLicata2007\], Theorem
2.11): where a term {lit}`M₀` checks against {lit}`A₀` in {lit}`ΓL`, and an expression is judged
in {lit}`ΓR ++ A₀ :: ΓL`, the hereditary substitution of {lit}`M₀` for the variable of
{lit}`A₀` into the expression, into the types of {lit}`ΓR` ({lit}`substCtx`) and into the type it
is checked against ({lit}`substMode`) exists, and the substituted expression is judged in the
substituted context.

The proof follows \[HarperLicata2007\]: a lexicographic induction on the simple type of
{lit}`A₀` and on the expression, with the statement strengthened to contexts and types known only
to have the shape of types ({name}`Geb.LF.Expr.TypeShape`). At an application of a head other
than the substituted variable, the substitution commutes with the instantiation of the head's
classifier along the spine by the composition of hereditary substitutions
({name}`Geb.LF.comp`), the erasures of the domains unchanged. At an application of the
substituted variable the substitution is the reduction of {lit}`M₀` applied to the substituted
spine, which checks against the instantiated classifier ({lit}`ReduceAt`) by the theorem at the
simple types of the domains, smaller than that of {lit}`A₀`.

## Main definitions

* {lit}`substCtx`, {lit}`substMode` — the substitution into the inner context and into a mode.
* {lit}`SubstAt`, {lit}`ReduceAt` — the theorem at a simple type, and the checking of a reduction.

## Main statements

* {lit}`varType_subst_lt`, {lit}`varType_subst_eq`, {lit}`varType_subst_gt` — the types of the
  variables under substitution.
* {lit}`spine_subst` — the substitution commutes with the instantiation along a spine.
* {lit}`subst` — the substitution theorem.

## References

* \[HarperLicata2007\], Theorem 2.11.

## Tags

logical framework, LF, hereditary substitution, substitution theorem, cut admissibility
-/

set_option doc.verso true

@[expose] public section

namespace Geb.LF

/-- The substitution of {lit}`m`, at the simple type {lit}`α`, for the variable below an inner
context: each type, innermost first, substituted at its own depth, the variable at the number of
types after it. -/
def substCtx (α : SimpleTy) (m : Expr) (ΓR : Ctx) : Option Ctx :=
  ΓR.foldr (fun a acc ↦ acc.bind fun Γ' ↦
    (hsub α (m.rename (· + Γ'.length)) a Γ'.length).map (· :: Γ')) (some [])

/-- The substitution into a mode: into the type it checks against. -/
def substMode (α : SimpleTy) (n : Expr) (md : Mode) (j : ℕ) : Option Mode :=
  match md with
    | .kind => some .kind
    | .type => some .type
    | .check a => (hsub α n a j).map .check

/-- The substitution into an extended inner context. -/
theorem substCtx_cons (α : SimpleTy) (m a : Expr) (ΓR : Ctx) :
    substCtx α m (a :: ΓR) = (substCtx α m ΓR).bind fun Γ' ↦
      (hsub α (m.rename (· + Γ'.length)) a Γ'.length).map (· :: Γ') :=
  rfl

/-- The substitution into an inner context keeps its length. -/
theorem substCtx_length (α : SimpleTy) (m : Expr) :
    ∀ (ΓR ΓR' : Ctx), substCtx α m ΓR = some ΓR' → ΓR'.length = ΓR.length :=
  fun ΓR ↦ ΓR.rec (motive := fun ΓR ↦ ∀ ΓR', substCtx α m ΓR = some ΓR' →
      ΓR'.length = ΓR.length)
    (fun ΓR' h ↦ by
      change some [] = some ΓR' at h
      rw [← Option.some.inj h])
    (fun a ΓR ih ΓR' h ↦ by
      rw [substCtx_cons, Option.bind_eq_some_iff] at h
      obtain ⟨Γ', hΓ', h⟩ := h
      obtain ⟨a', -, rfl⟩ := Option.map_eq_some_iff.mp h
      simp [ih Γ' hΓ'])

/-- Renaming by adding {lit}`a` and then {lit}`b` is renaming by adding their sum. -/
theorem rename_add_add (e : Expr) (a b : ℕ) :
    (e.rename (· + a)).rename (· + b) = e.rename (· + (a + b)) := by
  rw [rename_rename]
  congr 1
  funext x
  simp only [Function.comp_apply]
  omega

/-- The type of a variable past an extension of its context is weakened by one. -/
theorem varType_cons_succ (a : Expr) (Γ : Ctx) (i : ℕ) :
    varType (a :: Γ) (i + 1) = (varType Γ i).map fun t ↦ t.rename (· + 1) := by
  simp only [varType, List.getElem?_cons_succ, Option.map_map]
  congr 1
  funext t
  simp only [Function.comp_apply, rename_add_add]

/-- The type of a variable past a prefix of its context is weakened by the prefix's length. -/
theorem varType_append (Δ Γ : Ctx) (i : ℕ) :
    varType (Δ ++ Γ) (Δ.length + i) = (varType Γ i).map fun t ↦ t.rename (· + Δ.length) :=
  Δ.rec (motive := fun Δ ↦ varType (Δ ++ Γ) (Δ.length + i) =
      (varType Γ i).map fun t ↦ t.rename (· + Δ.length))
    (by
      beta_reduce
      rw [List.nil_append, List.length_nil, Nat.zero_add]
      cases varType Γ i with
      | none => rfl
      | some t => exact congrArg some (rename_add_zero t).symm)
    (fun a Δ ih ↦ by
      beta_reduce
      rw [List.cons_append, List.length_cons, show Δ.length + 1 + i = Δ.length + i + 1 by omega,
        varType_cons_succ, ih, Option.map_map]
      congr 1
      funext t
      simp only [Function.comp_apply, rename_add_add])

/-- A context is renamed into itself extended by a prefix, by adding the prefix's length. -/
theorem CtxRen.append (Δ Γ : Ctx) : CtxRen Γ (Δ ++ Γ) (· + Δ.length) := by
  intro i a ha
  change varType (Δ ++ Γ) (i + Δ.length) = _
  rw [show i + Δ.length = Δ.length + i by omega, varType_append, ha]
  rfl

/-- The type of a variable of the inner context: its substitution is the substituted context's
type of it. -/
theorem varType_subst_lt (α : SimpleTy) (M₀ A₀ : Expr) (ΓL : Ctx) :
    ∀ (ΓR ΓR' : Ctx) (i : ℕ) (t : Expr), substCtx α M₀ ΓR = some ΓR' → i < ΓR.length →
      varType (ΓR ++ A₀ :: ΓL) i = some t →
      ∃ t', hsub α (M₀.rename (· + ΓR.length)) t ΓR.length = some t' ∧
        varType (ΓR' ++ ΓL) i = some t' :=
  fun ΓR ↦ ΓR.rec (motive := fun ΓR ↦ ∀ (ΓR' : Ctx) (i : ℕ) (t : Expr),
      substCtx α M₀ ΓR = some ΓR' → i < ΓR.length → varType (ΓR ++ A₀ :: ΓL) i = some t →
      ∃ t', hsub α (M₀.rename (· + ΓR.length)) t ΓR.length = some t' ∧
        varType (ΓR' ++ ΓL) i = some t')
    (fun _ i _ _ hi _ ↦ absurd hi (Nat.not_lt_zero i))
    (fun a ΓR ih ΓR' i t h hi ht ↦ by
      rw [substCtx_cons, Option.bind_eq_some_iff] at h
      obtain ⟨Γ₀, hΓ₀, h⟩ := h
      obtain ⟨a', ha', rfl⟩ := Option.map_eq_some_iff.mp h
      have hlen := substCtx_length α M₀ ΓR Γ₀ hΓ₀
      rw [hlen] at ha'
      rcases i with _ | i
      · simp only [List.cons_append, varType, List.getElem?_cons_zero, Option.map_some,
          Option.some.injEq] at ht
        subst ht
        refine ⟨a'.rename (· + (0 + 1)), ?_, by simp [varType]⟩
        have := hsub_weaken α a (M₀.rename (· + ΓR.length)) ΓR.length (0 + 1) a' ha'
        rwa [rename_add_add, show ΓR.length + (0 + 1) = (a :: ΓR).length by simp] at this
      · rw [List.cons_append, varType_cons_succ, Option.map_eq_some_iff] at ht
        obtain ⟨t₀, ht₀, rfl⟩ := ht
        obtain ⟨t₀', ht₀', hv⟩ := ih Γ₀ i t₀ hΓ₀ (by simpa using hi) ht₀
        refine ⟨t₀'.rename (· + 1), ?_, ?_⟩
        · have := hsub_weaken α t₀ (M₀.rename (· + ΓR.length)) ΓR.length 1 t₀' ht₀'
          rwa [rename_add_add, show ΓR.length + 1 = (a :: ΓR).length by simp] at this
        · rw [List.cons_append, varType_cons_succ, hv]
          rfl)

/-- Substitution for the variable of index {lit}`j` into an expression weakened past it, by
{lit}`j + 1`, gives the expression weakened by {lit}`j`. -/
theorem hsub_rename_add_succ (α : SimpleTy) (n e : Expr) (j : ℕ) :
    hsub α n (e.rename (· + (j + 1))) j = some (e.rename (· + j)) := by
  rw [rename_add_succ]
  exact hsubWith_vacuous _ _ _ _

/-- The type of the substituted variable: its substitution is its type, weakened past the inner
context. -/
theorem varType_subst_eq (α : SimpleTy) (M₀ A₀ : Expr) (ΓL ΓR : Ctx) :
    varType (ΓR ++ A₀ :: ΓL) ΓR.length = some (A₀.rename (· + (ΓR.length + 1))) ∧
      hsub α (M₀.rename (· + ΓR.length)) (A₀.rename (· + (ΓR.length + 1))) ΓR.length =
        some (A₀.rename (· + ΓR.length)) := by
  refine ⟨?_, hsub_rename_add_succ _ _ _ _⟩
  have := varType_append ΓR (A₀ :: ΓL) 0
  rw [Nat.add_zero] at this
  rw [this]
  simp only [varType, List.getElem?_cons_zero, Option.map_some, Option.some.injEq,
    rename_add_add]
  congr 2
  funext x
  omega

/-- The type of a variable of the outer context: its substitution is the type of the variable
renumbered past the removed one. -/
theorem varType_subst_gt (α : SimpleTy) (M₀ A₀ : Expr) (ΓL ΓR ΓR' : Ctx)
    (h : substCtx α M₀ ΓR = some ΓR') (i : ℕ) (t : Expr)
    (ht : varType (ΓR ++ A₀ :: ΓL) (ΓR.length + 1 + i) = some t) :
    ∃ t', hsub α (M₀.rename (· + ΓR.length)) t ΓR.length = some t' ∧
      varType (ΓR' ++ ΓL) (ΓR.length + i) = some t' := by
  rw [show ΓR.length + 1 + i = ΓR.length + (i + 1) by omega, varType_append,
    varType_cons_succ, Option.map_map, Option.map_eq_some_iff] at ht
  obtain ⟨t₀, ht₀, rfl⟩ := ht
  refine ⟨t₀.rename (· + ΓR.length), ?_, ?_⟩
  · simp only [Function.comp_apply, rename_add_add]
    rw [show 1 + ΓR.length = ΓR.length + 1 by omega]
    exact hsub_rename_add_succ _ _ _ _
  · rw [← substCtx_length α M₀ ΓR ΓR' h, varType_append, ht₀]
    rfl

/-- The classifier of a variable other than the substituted one: its substitution is the
classifier of the variable renumbered past the removed one. -/
theorem classOf_subst_var {sig : Sig} (α : SimpleTy) (M₀ A₀ : Expr) (ΓL ΓR ΓR' : Ctx)
    (h : substCtx α M₀ ΓR = some ΓR') (i : ℕ) (hi : i ≠ ΓR.length) (C : Expr)
    (hC : classOf sig (ΓR ++ A₀ :: ΓL) (.var i) = some C) :
    ∃ C', hsub α (M₀.rename (· + ΓR.length)) C ΓR.length = some C' ∧
      classOf sig (ΓR' ++ ΓL) (.var (renumber ΓR.length i)) = some C' := by
  change varType _ i = some C at hC
  change ∃ C', _ ∧ varType _ (renumber ΓR.length i) = some C'
  by_cases hlt : i < ΓR.length
  · rw [show renumber ΓR.length i = i by unfold renumber; split_ifs <;> omega]
    exact varType_subst_lt α M₀ A₀ ΓL ΓR ΓR' i C h hlt hC
  · obtain ⟨i₀, rfl⟩ : ∃ i₀, i = ΓR.length + 1 + i₀ := ⟨i - ΓR.length - 1, by omega⟩
    rw [show renumber ΓR.length (ΓR.length + 1 + i₀) = ΓR.length + i₀ by
      unfold renumber; split_ifs <;> omega]
    exact varType_subst_gt α M₀ A₀ ΓL ΓR ΓR' h i₀ C hC

/-- The substitution into a product: into its domain, and into its codomain under the binder. -/
theorem hsub_pi (α : SimpleTy) (n a b : Expr) (j : ℕ) (c : Expr)
    (h : hsub α n (Expr.pi a b) j = some c) :
    ∃ a' b', hsub α n a j = some a' ∧ hsub α n.shift b (j + 1) = some b' ∧ c = Expr.pi a' b' := by
  rw [hsub_eq, Expr.pi, hsubWith_node_of_ne _ _ (fun i h ↦ by cases h), Option.map_eq_map,
    Option.map_eq_some_iff] at h
  obtain ⟨ys, hys, rfl⟩ := h
  rw [mapM_id_eq_some_iff] at hys
  rcases ys with _ | ⟨a', _ | ⟨b', _ | ⟨d, ys⟩⟩⟩
  · simp at hys
  · simp at hys
  · simp only [List.zipIdx_cons, List.zipIdx_nil, List.map_cons, List.map_nil,
      List.cons.injEq] at hys
    exact ⟨a', b', hys.1, hys.2.1, rfl⟩
  · simp at hys

/-- The substitution into a product whose domain and codomain substitute. -/
theorem hsub_pi_of (α : SimpleTy) (n a b a' b' : Expr) (j : ℕ) (ha : hsub α n a j = some a')
    (hb : hsub α n.shift b (j + 1) = some b') :
    hsub α n (Expr.pi a b) j = some (Expr.pi a' b') := by
  rw [hsub_eq, Expr.pi, hsubWith_node_of_ne _ _ (fun i h ↦ by cases h)]
  simp only [List.zipIdx_cons, List.zipIdx_nil, List.map_cons, List.map_nil,
    show Label.pi.binders 0 = 0 from rfl, show Label.pi.binders 1 = 1 from rfl,
    Function.iterate_zero_apply, Function.iterate_one, Nat.add_zero]
  rw [← hsub_eq, ← hsub_eq, ha, hb]
  rfl

/-- The hereditary substitution commutes with the instantiation of a classifier of the shape of
types along a spine, given that it preserves the check of each argument: the substituted
arguments instantiate the substituted classifier to the substituted result. -/
theorem spine_subst {sig : Sig} (α₀ : SimpleTy) (N : Expr) (j : ℕ) (Γ Γ' : Ctx) :
    ∀ (ms : List Expr) (C C' P : Expr), C.TypeShape = true →
      spine Γ C (ms.map fun m ↦ (m, judge sig m)) = some P →
      hsub α₀ N C j = some C' →
      (∀ m ∈ ms, ∀ A A', judge sig m Γ (.check A) = true → A.TypeShape = true →
        hsub α₀ N A j = some A' →
        ∃ m', hsub α₀ N m j = some m' ∧ judge sig m' Γ' (.check A') = true) →
      ∃ ms' P', (ms.map fun m ↦ hsub α₀ N m j).mapM id = some ms' ∧
        hsub α₀ N P j = some P' ∧ spine Γ' C' (ms'.map fun m ↦ (m, judge sig m)) = some P' :=
  fun ms ↦ ms.rec (motive := fun ms ↦ ∀ (C C' P : Expr), C.TypeShape = true →
      spine Γ C (ms.map fun m ↦ (m, judge sig m)) = some P →
      hsub α₀ N C j = some C' →
      (∀ m ∈ ms, ∀ A A', judge sig m Γ (.check A) = true → A.TypeShape = true →
        hsub α₀ N A j = some A' →
        ∃ m', hsub α₀ N m j = some m' ∧ judge sig m' Γ' (.check A') = true) →
      ∃ ms' P', (ms.map fun m ↦ hsub α₀ N m j).mapM id = some ms' ∧
        hsub α₀ N P j = some P' ∧ spine Γ' C' (ms'.map fun m ↦ (m, judge sig m)) = some P')
    (fun C C' P _ hsp hC _ ↦ by
      simp only [spine, List.map_nil, List.foldlM_nil, Option.pure_def,
        Option.some.injEq] at hsp
      subst hsp
      exact ⟨[], C', rfl, hC, rfl⟩)
    (fun m ms ih C C' P hTS hsp hC hargs ↦ by
      simp only [spine, List.map_cons, List.foldlM_cons] at hsp
      obtain ⟨C₂, hC₂, hrest⟩ := Option.bind_eq_some_iff.mp hsp
      obtain ⟨l, cs, rfl⟩ := exists_node C
      rw [RoseTree.label_node, RoseTree.children_node] at hC₂
      rcases l with _ | _ | _ | _
      · simp at hC₂
      · rcases cs with _ | ⟨A, _ | ⟨B, _ | ⟨d, cs⟩⟩⟩
        · simp at hC₂
        · simp at hC₂
        · simp only at hC₂
          split_ifs at hC₂ with hm
          rw [typeShape_node] at hTS
          simp only [List.map_cons, List.map_nil, typeShapeStep, Bool.and_eq_true] at hTS
          obtain ⟨A', B', hA', hB', rfl⟩ := hsub_pi α₀ N A B j C' hC
          obtain ⟨m', hm', hm'J⟩ := hargs m (by simp) A A' hm hTS.1 hA'
          obtain ⟨C₂', hC₂', hB'C⟩ := comp α₀ (Expr.erase A) B 0 j N m C₂ m' B'
            (by rw [rename_add_zero]; exact hC₂) hm'
            (by
              rw [show 0 + 1 + j = j + 1 by omega, show (· + (0 + 1)) = Nat.succ from rfl]
              exact hB')
          rw [rename_add_zero, Nat.zero_add] at hC₂'
          rw [rename_add_zero] at hB'C
          have hTS₂ := (typeShape_hsubWith _ B m 0 C₂ hTS.2 hC₂).1
          obtain ⟨ms', P', hms', hP', hsp'⟩ := ih C₂ C₂' P hTS₂ hrest hC₂'
            fun m hm ↦ hargs m (List.mem_cons_of_mem _ hm)
          refine ⟨m' :: ms', P', ?_, hP', ?_⟩
          · rw [mapM_id_eq_some_iff] at hms' ⊢
            simp only [List.map_cons, hm', hms']
          · simp only [spine, List.map_cons, List.foldlM_cons]
            rw [Expr.pi, RoseTree.label_node, RoseTree.children_node]
            simp only [hm'J, ↓reduceIte]
            rw [(typeShape_hsubWith _ A N j A' hTS.1 hA').2, hB'C]
            exact hsp'
        · simp at hC₂
      · simp at hC₂
      · simp at hC₂)

/-- The substitution theorem at a simple type: where {lit}`M₀` checks against {lit}`A₀` of that
simple type in {lit}`ΓL`, an expression judged in {lit}`ΓR ++ A₀ :: ΓL`, its context and the
type it checks against of the shape of types, substitutes, with the context and the mode, to an
expression judged in the substituted context. -/
def SubstAt (sig : Sig) (α₀ : SimpleTy) : Prop :=
  ∀ (ΓL : Ctx) (A₀ M₀ : Expr), A₀.erase = α₀ → A₀.TypeShape = true →
    judge sig M₀ ΓL (.check A₀) = true →
    ∀ (e : Expr) (ΓR ΓR' : Ctx) (md md' : Mode), (∀ a ∈ ΓR ++ ΓL, a.TypeShape = true) →
      (∀ a, md = .check a → a.TypeShape = true) →
      substCtx α₀ M₀ ΓR = some ΓR' → judge sig e (ΓR ++ A₀ :: ΓL) md = true →
      substMode α₀ (M₀.rename (· + ΓR.length)) md ΓR.length = some md' →
      ∃ e', hsub α₀ (M₀.rename (· + ΓR.length)) e ΓR.length = some e' ∧
        judge sig e' (ΓR' ++ ΓL) md' = true

/-- The reduction at a simple type of a term checking against a classifier of that simple type,
applied to a spine along which the classifier instantiates to an atomic type, checks against
that type. -/
def ReduceAt (sig : Sig) (α₀ : SimpleTy) : Prop :=
  ∀ (Γ : Ctx) (n c p : Expr) (ms : List Expr), c.erase = α₀ → c.TypeShape = true →
    (∀ a ∈ Γ, a.TypeShape = true) → judge sig n Γ (.check c) = true →
    spine Γ c (ms.map fun m ↦ (m, judge sig m)) = some p → IsApp p = true →
    ∃ r, reduce α₀ n ms = some r ∧ judge sig r Γ (.check p) = true

/-- A term checking against a product is an abstraction whose body checks against the codomain
in the context extended by the domain. -/
theorem judge_check_pi_inv {sig : Sig} {Γ : Ctx} {n a b : Expr}
    (h : judge sig n Γ (.check (Expr.pi a b)) = true) :
    ∃ body, n = Expr.lam body ∧ judge sig body (a :: Γ) (.check b) = true := by
  obtain ⟨l, cs, rfl⟩ := exists_node n
  rw [judge, judgeWith_node] at h
  rcases l with _ | _ | _ | hd
  · simp [judgeStep] at h
  · simp [judgeStep] at h
  · rcases cs with _ | ⟨body, _ | ⟨d, cs⟩⟩
    · simp [judgeStep] at h
    · simp only [judgeStep, List.map_cons, List.map_nil, Expr.pi, RoseTree.label_node,
        RoseTree.children_node] at h
      exact ⟨body, rfl, h⟩
    · simp [judgeStep] at h
  · simp only [judgeStep, Bool.and_eq_true] at h
    simp [IsApp, Expr.pi] at h

/-- An expression of the shape of types that is an application is that of a constant, and erases
to the base type of the constant. -/
theorem erase_of_typeShape_isApp {e : Expr} (hs : e.TypeShape = true) (ha : IsApp e = true) :
    ∃ c, e.erase = RoseTree.node (.base c) [] := by
  obtain ⟨l, cs, rfl⟩ := exists_node e
  rw [typeShape_node] at hs
  rcases l with _ | _ | _ | (i | c)
  · simp [IsApp] at ha
  · simp [IsApp] at ha
  · simp [IsApp] at ha
  · simp [typeShapeStep] at hs
  · exact ⟨c, rfl⟩

/-- The reduction lemma at a simple type, given the substitution theorem and the reduction lemma
at its children. -/
theorem reduceAt_node {sig : Sig} (l : SimpleLabel) (cs : List SimpleTy)
    (ih : ∀ c ∈ cs, SubstAt sig c ∧ ReduceAt sig c) : ReduceAt sig (RoseTree.node l cs) := by
  intro Γ n c p ms hce hcTS hΓ hn hsp hp
  rcases ms with _ | ⟨m, ms⟩
  · simp only [spine, List.map_nil, List.foldlM_nil, Option.pure_def,
      Option.some.injEq] at hsp
    subst hsp
    obtain ⟨c', hc'⟩ := erase_of_typeShape_isApp hcTS hp
    rw [hce] at hc'
    obtain ⟨rfl, rfl⟩ := RoseTree.node_eq_iff.mp hc'
    exact ⟨n, rfl, hn⟩
  · simp only [spine, List.map_cons, List.foldlM_cons] at hsp
    obtain ⟨C₂, hC₂, hrest⟩ := Option.bind_eq_some_iff.mp hsp
    obtain ⟨cl, ccs, rfl⟩ := exists_node c
    rw [RoseTree.label_node, RoseTree.children_node] at hC₂
    rcases cl with _ | _ | _ | _
    · simp at hC₂
    · rcases ccs with _ | ⟨A, _ | ⟨B, _ | ⟨d, ccs⟩⟩⟩
      · simp at hC₂
      · simp at hC₂
      · simp only at hC₂
        split_ifs at hC₂ with hm
        rw [typeShape_node] at hcTS
        simp only [List.map_cons, List.map_nil, typeShapeStep, Bool.and_eq_true] at hcTS
        rw [erase_node] at hce
        simp only [List.map_cons, List.map_nil, eraseStep] at hce
        obtain ⟨hl, hcs⟩ := RoseTree.node_eq_iff.mp hce
        rw [RoseTree.label_node] at hl
        rw [RoseTree.children_node] at hcs
        subst hl hcs
        obtain ⟨body, rfl, hbody⟩ := judge_check_pi_inv hn
        obtain ⟨body', hbody', hbody'J⟩ := (ih (Expr.erase A) (by simp)).1 Γ A m rfl hcTS.1 hm
          body [] [] (.check B) (.check C₂) (by simpa using hΓ)
          (fun a h ↦ by cases h; exact hcTS.2) rfl (by simpa using hbody)
          (by simp only [substMode, List.length_nil, rename_add_zero, hC₂, Option.map_some])
        rw [List.length_nil, rename_add_zero] at hbody'
        obtain ⟨r, hr, hrJ⟩ := (ih (Expr.erase B) (by simp)).2 Γ body' C₂ p ms
          (typeShape_hsubWith _ B m 0 C₂ hcTS.2 hC₂).2
          (typeShape_hsubWith _ B m 0 C₂ hcTS.2 hC₂).1 hΓ (by simpa using hbody'J) hrest hp
        refine ⟨r, ?_, hrJ⟩
        rw [reduce_node]
        simp only [List.map_cons, List.map_nil, reduceStep, Expr.lam, RoseTree.label_node,
          RoseTree.children_node]
        rw [← hsub_eq, hbody', Option.bind_some]
        exact hr
      · simp at hC₂
    · simp at hC₂
    · simp at hC₂

/-- Substitution into the kind of types leaves it in place. -/
theorem hsub_type (α : SimpleTy) (n : Expr) (j : ℕ) : hsub α n Expr.type j = some Expr.type := by
  rw [hsub_eq, Expr.type, hsubWith_node_of_ne _ _ (fun i h ↦ by cases h)]
  rfl

/-- Substitution into an abstraction is substitution into its body under the binder. -/
theorem hsub_lam (α : SimpleTy) (n b : Expr) (j : ℕ) :
    hsub α n (Expr.lam b) j = Expr.lam <$> hsub α n.shift b (j + 1) := by
  rw [hsub_eq, Expr.lam, hsubWith_node_of_ne _ _ (fun i h ↦ by cases h)]
  simp only [List.zipIdx_cons, List.zipIdx_nil, List.map_cons, List.map_nil,
    show Label.lam.binders 0 = 1 from rfl, Function.iterate_one]
  rw [← hsub_eq]
  cases hsub α n.shift b (j + 1) <;> rfl

/-- Substitution into the application of a constant is substitution into its spine. -/
theorem hsub_const (α : SimpleTy) (n : Expr) (c : ℕ) (cs : List Expr) (j : ℕ) :
    hsub α n (Expr.const c cs) j = (Expr.const c ·) <$> (cs.map fun m ↦ hsub α n m j).mapM id := by
  rw [hsub_eq, Expr.const, Expr.app, hsubWith_node_of_ne _ _ (fun i h ↦ by cases h)]
  simp only [Label.binders_app, Function.iterate_zero_apply, Nat.add_zero]
  rw [zipIdx_map_fst fun m : Expr ↦ hsubWith (reduce α) m n j]
  rfl

/-- Weakening an expression weakened by {lit}`j` is weakening it by {lit}`j + 1`. -/
theorem shift_rename_add (m : Expr) (j : ℕ) : (m.rename (· + j)).shift = m.rename (· + (j + 1)) :=
  rename_add_add m j 1

/-- The kinds and types of the declarations of a formed signature have the shape of types. -/
theorem Sig.ok_typeShape {sig : Sig} (h : sig.ok = true) (c : ℕ) (a : Expr)
    (hc : sig[c]? = some a) : a.TypeShape = true := by
  obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp hc
  rw [Sig.ok, List.all_eq_true] at h
  have hmem : (sig[c], sig.take c) ∈ sig.zip sig.inits := by
    rw [List.mem_iff_getElem]
    refine ⟨c, by simp [List.length_inits]; omega, ?_⟩
    simp [List.getElem_inits]
  have hd := h _ hmem
  simp only [Bool.or_eq_true, IsKind, IsType] at hd
  rcases hd with hd | hd
  · exact (judgeWith_typeShape _ []).1 hd
  · exact (judgeWith_typeShape _ []).2 hd

/-- The type of a variable of a context of types of the shape has the shape. -/
theorem varType_typeShape {Γ : Ctx} (hΓ : ∀ a ∈ Γ, a.TypeShape = true) {i : ℕ} {t : Expr}
    (h : varType Γ i = some t) : t.TypeShape = true := by
  obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp h
  rw [typeShape_rename]
  exact hΓ a (List.mem_of_getElem? ha)

/-- The substitution into a context of types of the shape is one. -/
theorem substCtx_typeShape (α : SimpleTy) (m : Expr) :
    ∀ (ΓR ΓR' : Ctx), (∀ a ∈ ΓR, a.TypeShape = true) → substCtx α m ΓR = some ΓR' →
      ∀ a ∈ ΓR', a.TypeShape = true :=
  fun ΓR ↦ ΓR.rec (motive := fun ΓR ↦ ∀ ΓR', (∀ a ∈ ΓR, a.TypeShape = true) →
      substCtx α m ΓR = some ΓR' → ∀ a ∈ ΓR', a.TypeShape = true)
    (fun ΓR' _ h a ha ↦ by
      change some [] = some ΓR' at h
      rw [← Option.some.inj h] at ha
      exact absurd ha List.not_mem_nil)
    (fun b ΓR ih ΓR' hs h a ha ↦ by
      rw [substCtx_cons, Option.bind_eq_some_iff] at h
      obtain ⟨Γ₀, hΓ₀, h⟩ := h
      obtain ⟨b', hb', rfl⟩ := Option.map_eq_some_iff.mp h
      rcases List.mem_cons.mp ha with rfl | ha
      · exact (typeShape_hsubWith _ b _ _ _ (hs b List.mem_cons_self) hb').1
      · exact ih Γ₀ (fun x hx ↦ hs x (List.mem_cons_of_mem _ hx)) hΓ₀ a ha)

/-- The substitution into an application of the shape of types is an application. -/
theorem isApp_hsub {α : SimpleTy} {n p p' : Expr} {j : ℕ} (hs : p.TypeShape = true)
    (ha : IsApp p = true) (h : hsub α n p j = some p') : IsApp p' = true := by
  obtain ⟨l, cs, rfl⟩ := exists_node p
  rw [typeShape_node] at hs
  rcases l with _ | _ | _ | (i | c)
  · simp [IsApp] at ha
  · simp [IsApp] at ha
  · simp [IsApp] at ha
  · simp [typeShapeStep] at hs
  · rw [hsub_eq, hsubWith_node_of_ne _ _ (fun i h ↦ by cases h), Option.map_eq_map,
      Option.map_eq_some_iff] at h
    obtain ⟨ys, -, rfl⟩ := h
    rfl

/-- The substitution theorem at a simple type, given the reduction lemma at it. -/
theorem substAt_of {sig : Sig} (hsig : sig.ok = true) {α₀ : SimpleTy} (hred : ReduceAt sig α₀) :
    SubstAt sig α₀ := by
  intro ΓL A₀ M₀ hA₀e hA₀s hM₀ e
  have hclosed := Sig.ok_closed hsig
  refine RoseTree.ind (P := fun e ↦ ∀ (ΓR ΓR' : Ctx) (md md' : Mode),
      (∀ a ∈ ΓR ++ ΓL, a.TypeShape = true) → (∀ a, md = .check a → a.TypeShape = true) →
      substCtx α₀ M₀ ΓR = some ΓR' → judge sig e (ΓR ++ A₀ :: ΓL) md = true →
      substMode α₀ (M₀.rename (· + ΓR.length)) md ΓR.length = some md' →
      ∃ e', hsub α₀ (M₀.rename (· + ΓR.length)) e ΓR.length = some e' ∧
        judge sig e' (ΓR' ++ ΓL) md' = true) (fun l cs ih ↦ ?_) e
  intro ΓR ΓR' md md' hΓs hmd hsc he hmdsub
  have hlen := substCtx_length α₀ M₀ ΓR ΓR' hsc
  -- the extension of the inner context by a type that substitutes
  have hext : ∀ a a', hsub α₀ (M₀.rename (· + ΓR.length)) a ΓR.length = some a' →
      substCtx α₀ M₀ (a :: ΓR) = some (a' :: ΓR') := fun a a' ha ↦ by
    rw [substCtx_cons, hsc, Option.bind_some, hlen, ha]
    rfl
  -- the arguments of a spine substitute and check
  have hargs : ∀ m ∈ cs, ∀ A A', judge sig m (ΓR ++ A₀ :: ΓL) (.check A) = true →
      A.TypeShape = true → hsub α₀ (M₀.rename (· + ΓR.length)) A ΓR.length = some A' →
      ∃ m', hsub α₀ (M₀.rename (· + ΓR.length)) m ΓR.length = some m' ∧
        judge sig m' (ΓR' ++ ΓL) (.check A') = true :=
    fun m hm A A' hmA hA hA' ↦ ih m hm ΓR ΓR' (.check A) (.check A') hΓs
      (fun a h ↦ by cases h; exact hA) hsc hmA (by simp [substMode, hA'])
  -- the contexts' types have the shape of types
  have hΓfs : ∀ a ∈ ΓR ++ A₀ :: ΓL, a.TypeShape = true := fun a ha ↦ by
    rcases List.mem_append.mp ha with ha | ha
    · exact hΓs a (List.mem_append_left _ ha)
    · rcases List.mem_cons.mp ha with rfl | ha
      · exact hA₀s
      · exact hΓs a (List.mem_append_right _ ha)
  have hΓ's : ∀ a ∈ ΓR' ++ ΓL, a.TypeShape = true := fun a ha ↦ by
    rcases List.mem_append.mp ha with ha | ha
    · exact substCtx_typeShape α₀ M₀ ΓR ΓR'
        (fun x hx ↦ hΓs x (List.mem_append_left _ hx)) hsc a ha
    · exact hΓs a (List.mem_append_right _ ha)
  -- a product, judged as a kind or a type
  have hpi : ∀ (a b : Expr) (mb : Mode), cs = [a, b] → (mb = .kind ∨ mb = .type) →
      judge sig a (ΓR ++ A₀ :: ΓL) .type = true → judge sig b (a :: (ΓR ++ A₀ :: ΓL)) mb = true →
      ∃ e', hsub α₀ (M₀.rename (· + ΓR.length)) (Expr.pi a b) ΓR.length = some e' ∧
        judge sig e' (ΓR' ++ ΓL) mb = true := by
    intro a b mb hcs hmb ha hb
    obtain ⟨a', ha', ha'J⟩ := ih a (by simp [hcs]) ΓR ΓR' .type .type hΓs
      (fun _ h ↦ by cases h) hsc ha rfl
    have has : a.TypeShape = true := (judgeWith_typeShape a _).2 ha
    obtain ⟨b', hb', hb'J⟩ := ih b (by simp [hcs]) (a :: ΓR) (a' :: ΓR') mb mb
      (fun x hx ↦ by
        rcases List.mem_cons.mp hx with rfl | hx
        · exact has
        · exact hΓs x hx)
      (fun x h ↦ by rcases hmb with rfl | rfl <;> cases h) (hext a a' ha') hb
      (by rcases hmb with rfl | rfl <;> rfl)
    refine ⟨Expr.pi a' b', hsub_pi_of _ _ _ _ _ _ _ ha' (by
      rw [shift_rename_add]
      simpa using hb'), ?_⟩
    rw [judge, Expr.pi, judgeWith_node]
    rcases hmb with rfl | rfl
    · simp only [judgeStep, List.map_cons, List.map_nil, Bool.and_eq_true]
      exact ⟨ha'J, hb'J⟩
    · simp only [judgeStep, List.map_cons, List.map_nil, Bool.and_eq_true]
      exact ⟨ha'J, hb'J⟩
  rcases md with _ | _ | p
  · simp only [substMode, Option.some.injEq] at hmdsub
    subst hmdsub
    rw [judge, judgeWith_node] at he
    rcases l with _ | _ | _ | (i | c)
    · rcases cs with _ | ⟨d, cs⟩
      · exact ⟨Expr.type, hsub_type _ _ _, rfl⟩
      · simp [judgeStep] at he
    · rcases cs with _ | ⟨a, _ | ⟨b, _ | ⟨d, cs⟩⟩⟩
      · simp [judgeStep] at he
      · simp [judgeStep] at he
      · simp only [judgeStep, List.map_cons, List.map_nil, Bool.and_eq_true] at he
        exact hpi a b .kind rfl (Or.inl rfl) he.1 he.2
      · simp [judgeStep] at he
    · simp [judgeStep] at he
    · simp [judgeStep] at he
    · simp [judgeStep] at he
  · simp only [substMode, Option.some.injEq] at hmdsub
    subst hmdsub
    rw [judge, judgeWith_node] at he
    rcases l with _ | _ | _ | (i | c)
    · simp [judgeStep] at he
    · rcases cs with _ | ⟨a, _ | ⟨b, _ | ⟨d, cs⟩⟩⟩
      · simp [judgeStep] at he
      · simp [judgeStep] at he
      · simp only [judgeStep, List.map_cons, List.map_nil, Bool.and_eq_true] at he
        exact hpi a b .type rfl (Or.inr rfl) he.1 he.2
      · simp [judgeStep] at he
    · simp [judgeStep] at he
    · simp [judgeStep] at he
    · simp only [judgeStep, beq_iff_eq, Option.bind_eq_some_iff] at he
      obtain ⟨K, hK, hsp⟩ := he
      have hKs := Sig.ok_typeShape hsig c K hK
      have hKsub : hsub α₀ (M₀.rename (· + ΓR.length)) K ΓR.length = some K := by
        have := hsubWith_vacuous (reduce α₀) K (M₀.rename (· + ΓR.length)) ΓR.length
        rwa [hclosed c K hK] at this
      obtain ⟨ms', P', hms', hP', hsp'⟩ :=
        spine_subst α₀ _ _ _ (ΓR' ++ ΓL) cs K K Expr.type hKs hsp hKsub hargs
      rw [hsub_type, Option.some.injEq] at hP'
      subst hP'
      refine ⟨Expr.const c ms', ?_, ?_⟩
      · change hsub _ _ (Expr.const c cs) _ = _
        rw [hsub_const, hms']
        rfl
      · rw [judge, Expr.const, Expr.app, judgeWith_node]
        simp only [judgeStep, hK, Option.bind_some]
        exact beq_iff_eq.mpr hsp'
  · obtain ⟨p', hp', rfl⟩ := Option.map_eq_some_iff.mp hmdsub
    have hps := hmd p rfl
    rw [judge, judgeWith_node] at he
    rcases l with _ | _ | _ | hd
    · simp [judgeStep] at he
    · simp [judgeStep] at he
    · rcases cs with _ | ⟨body, _ | ⟨d, cs⟩⟩
      · simp [judgeStep] at he
      · obtain ⟨pl, pcs, rfl⟩ := exists_node p
        simp only [judgeStep, List.map_cons, List.map_nil, RoseTree.label_node,
          RoseTree.children_node] at he
        rcases pl with _ | _ | _ | _
        · simp at he
        · rcases pcs with _ | ⟨A, _ | ⟨B, _ | ⟨d', pcs⟩⟩⟩
          · simp at he
          · simp at he
          · rw [typeShape_node] at hps
            simp only [List.map_cons, List.map_nil, typeShapeStep, Bool.and_eq_true] at hps
            obtain ⟨A', B', hA', hB', rfl⟩ := hsub_pi α₀ _ A B _ p' hp'
            obtain ⟨body', hbody', hbody'J⟩ := ih body (by simp) (A :: ΓR) (A' :: ΓR')
              (.check B) (.check B')
              (fun x hx ↦ by
                rcases List.mem_cons.mp hx with rfl | hx
                · exact hps.1
                · exact hΓs x hx)
              (fun x h ↦ by cases h; exact hps.2) (hext A A' hA') he
              (by
                simp only [substMode, List.length_cons]
                rw [← shift_rename_add, hB']
                rfl)
            refine ⟨Expr.lam body', ?_, ?_⟩
            · change hsub _ _ (Expr.lam body) _ = _
              rw [hsub_lam, shift_rename_add]
              simp only [List.length_cons] at hbody'
              rw [hbody']
              rfl
            · rw [judge, Expr.lam, judgeWith_node]
              simp only [judgeStep, List.map_cons, List.map_nil, Expr.pi, RoseTree.label_node,
                RoseTree.children_node]
              exact hbody'J
          · simp at he
        · simp at he
        · simp at he
      · simp [judgeStep] at he
    · simp only [judgeStep, Bool.and_eq_true] at he
      obtain ⟨hpa, hm⟩ := he
      have hp'a := isApp_hsub hps hpa hp'
      rcases hC : classOf sig (ΓR ++ A₀ :: ΓL) hd with _ | C
      · rw [hC] at hm
        simp at hm
      · rw [hC, Option.bind_some] at hm
        rcases hS : spine (ΓR ++ A₀ :: ΓL) C (cs.map fun c ↦ (c, judgeWith (· == ·) sig c))
          with _ | P
        · rw [hS] at hm
          simp at hm
        · rw [hS] at hm
          simp only [beq_iff_eq] at hm
          subst hm
          have hspine : ∀ C', C.TypeShape = true →
              hsub α₀ (M₀.rename (· + ΓR.length)) C ΓR.length = some C' →
              ∃ ms', (cs.map fun m ↦ hsub α₀ (M₀.rename (· + ΓR.length)) m ΓR.length).mapM id =
                some ms' ∧
                spine (ΓR' ++ ΓL) C' (ms'.map fun m ↦ (m, judgeWith (· == ·) sig m)) =
                  some p' := fun C' hCs hC' ↦ by
            obtain ⟨ms', P', hms', hP', hsp'⟩ := spine_subst α₀ (M₀.rename (· + ΓR.length))
              ΓR.length (ΓR ++ A₀ :: ΓL) (ΓR' ++ ΓL) cs C C' P hCs hS hC' hargs
            rw [hp', Option.some.injEq] at hP'
            subst hP'
            exact ⟨ms', hms', hsp'⟩
          rcases hd with i | c
          · by_cases hij : i = ΓR.length
            · subst hij
              obtain ⟨hv, hvs⟩ := varType_subst_eq α₀ M₀ A₀ ΓL ΓR
              have hCeq : C = A₀.rename (· + (ΓR.length + 1)) := by
                change varType _ _ = some C at hC
                rw [hv] at hC
                exact (Option.some.inj hC).symm
              subst hCeq
              obtain ⟨ms', hms', hsp'⟩ := hspine _ (by rw [typeShape_rename]; exact hA₀s) hvs
              obtain ⟨r, hr, hrJ⟩ := hred (ΓR' ++ ΓL) (M₀.rename (· + ΓR.length))
                (A₀.rename (· + ΓR.length)) p' ms' (by rw [erase_rename]; exact hA₀e)
                (by rw [typeShape_rename]; exact hA₀s) hΓ's
                (by
                  have := judge_rename hclosed M₀ (.check A₀) (CtxRen.append ΓR' ΓL) hM₀
                  rwa [hlen] at this) hsp' hp'a
              refine ⟨r, ?_, hrJ⟩
              change hsub _ _ (Expr.var ΓR.length cs) _ = _
              rw [hsub_var, hms', Option.bind_some]
              simp only [↓reduceIte]
              exact hr
            · obtain ⟨C', hC', hC'Γ⟩ := classOf_subst_var α₀ M₀ A₀ ΓL ΓR ΓR' hsc i hij C hC
              obtain ⟨ms', hms', hsp'⟩ := hspine C' (varType_typeShape hΓfs hC) hC'
              refine ⟨Expr.var (renumber ΓR.length i) ms', ?_, ?_⟩
              · change hsub _ _ (Expr.var i cs) _ = _
                rw [hsub_var, hms', Option.bind_some]
                simp only [hij, ↓reduceIte]
              · rw [judge, Expr.var, Expr.app, judgeWith_node]
                simp only [judgeStep, hp'a, Bool.true_and, hC'Γ, Option.bind_some, hsp',
                  beq_self_eq_true]
          · have hK : sig[c]? = some C := hC
            have hKsub : hsub α₀ (M₀.rename (· + ΓR.length)) C ΓR.length = some C := by
              have := hsubWith_vacuous (reduce α₀) C (M₀.rename (· + ΓR.length)) ΓR.length
              rwa [hclosed c C hK] at this
            obtain ⟨ms', hms', hsp'⟩ := hspine C (Sig.ok_typeShape hsig c C hK) hKsub
            refine ⟨Expr.const c ms', ?_, ?_⟩
            · change hsub _ _ (Expr.const c cs) _ = _
              rw [hsub_const, hms']
              rfl
            · rw [judge, Expr.const, Expr.app, judgeWith_node]
              simp only [judgeStep, hp'a, Bool.true_and, classOf, hK, Option.bind_some, hsp',
                beq_self_eq_true]

/-- The substitution theorem and the reduction lemma at every simple type, by induction on it. -/
theorem substAt_reduceAt {sig : Sig} (hsig : sig.ok = true) :
    ∀ α : SimpleTy, SubstAt sig α ∧ ReduceAt sig α :=
  RoseTree.ind fun l cs ih ↦
    have hr := reduceAt_node l cs ih
    ⟨substAt_of hsig hr, hr⟩

/-- The formation of an extended context: its type is a type in the context, which is formed. -/
theorem Ctx.ok_cons (sig : Sig) (a : Expr) (Γ : Ctx) :
    Ctx.ok sig (a :: Γ) = (IsType sig Γ a && Ctx.ok sig Γ) := by
  simp only [Ctx.ok, List.tails_cons, List.all_cons]

/-- A formed context's types have the shape of types. -/
theorem Ctx.ok_typeShape (sig : Sig) :
    ∀ Γ : Ctx, Ctx.ok sig Γ = true → ∀ a ∈ Γ, a.TypeShape = true :=
  fun Γ ↦ Γ.rec (motive := fun Γ ↦ Ctx.ok sig Γ = true → ∀ a ∈ Γ, a.TypeShape = true)
    (fun _ a ha ↦ absurd ha List.not_mem_nil)
    (fun b Γ ih h a ha ↦ by
      rw [Ctx.ok_cons, Bool.and_eq_true] at h
      rcases List.mem_cons.mp ha with rfl | ha
      · exact (judgeWith_typeShape _ Γ).2 h.1
      · exact ih h.2 a ha)

/-- A context extending a formed context is formed only if that context is. -/
theorem Ctx.ok_of_append (sig : Sig) (Γ : Ctx) :
    ∀ Δ : Ctx, Ctx.ok sig (Δ ++ Γ) = true → Ctx.ok sig Γ = true :=
  fun Δ ↦ Δ.rec (motive := fun Δ ↦ Ctx.ok sig (Δ ++ Γ) = true → Ctx.ok sig Γ = true)
    id
    (fun a Δ ih h ↦ by
      rw [List.cons_append, Ctx.ok_cons, Bool.and_eq_true] at h
      exact ih h.2)

/-- The substitution into the types of a formed inner context exists, and gives a formed
context. -/
theorem substCtx_ok {sig : Sig} (hsig : sig.ok = true) {ΓL : Ctx} {A₀ M₀ : Expr}
    (hA₀s : A₀.TypeShape = true) (hM₀ : Checks sig ΓL M₀ A₀ = true) :
    ∀ ΓR : Ctx, Ctx.ok sig (ΓR ++ A₀ :: ΓL) = true →
      ∃ ΓR', substCtx (Expr.erase A₀) M₀ ΓR = some ΓR' ∧ Ctx.ok sig (ΓR' ++ ΓL) = true :=
  fun ΓR ↦ ΓR.rec (motive := fun ΓR ↦ Ctx.ok sig (ΓR ++ A₀ :: ΓL) = true →
      ∃ ΓR', substCtx (Expr.erase A₀) M₀ ΓR = some ΓR' ∧ Ctx.ok sig (ΓR' ++ ΓL) = true)
    (fun h ↦ by
      rw [List.nil_append, Ctx.ok_cons, Bool.and_eq_true] at h
      exact ⟨[], rfl, h.2⟩)
    (fun a ΓR ih h ↦ by
      have hall := Ctx.ok_typeShape sig _ h
      rw [List.cons_append, Ctx.ok_cons, Bool.and_eq_true] at h
      obtain ⟨ΓR', hsc, hok⟩ := ih h.2
      have hlen := substCtx_length _ M₀ ΓR ΓR' hsc
      obtain ⟨a', ha', ha'J⟩ := (substAt_reduceAt hsig (Expr.erase A₀)).1 ΓL A₀ M₀ rfl hA₀s
        hM₀ a ΓR ΓR' .type .type
        (fun x hx ↦ by
          rcases List.mem_append.mp hx with hx | hx
          · exact hall x (List.mem_cons_of_mem _ (List.mem_append_left _ hx))
          · exact hall x (List.mem_cons_of_mem _
              (List.mem_append_right _ (List.mem_cons_of_mem _ hx))))
        (fun _ h ↦ by cases h) hsc h.1 rfl
      refine ⟨a' :: ΓR', ?_, ?_⟩
      · rw [substCtx_cons, hsc, Option.bind_some, hlen, ha']
        rfl
      · rw [List.cons_append, Ctx.ok_cons, Bool.and_eq_true]
        exact ⟨ha'J, hok⟩)

/-- The substitution theorem (\[HarperLicata2007\], Theorem 2.11): where
{lit}`ΓR ++ A₀ :: ΓL` is a formed context and {lit}`M₀` checks against {lit}`A₀` in {lit}`ΓL`,
the substitution of {lit}`M₀` for the variable of {lit}`A₀` into {lit}`ΓR` exists and gives a
formed context, and every judgment in {lit}`ΓR ++ A₀ :: ΓL`, its type a type there where it is
checked against one, substitutes, with its mode, to a judgment in the substituted context. -/
theorem subst {sig : Sig} (hsig : sig.ok = true) {ΓL : Ctx} {A₀ M₀ : Expr}
    (hM₀ : Checks sig ΓL M₀ A₀ = true) :
    ∀ ΓR : Ctx, Ctx.ok sig (ΓR ++ A₀ :: ΓL) = true →
      ∃ ΓR', substCtx (Expr.erase A₀) M₀ ΓR = some ΓR' ∧ Ctx.ok sig (ΓR' ++ ΓL) = true ∧
        ∀ (e : Expr) (md : Mode),
          (∀ a, md = .check a → IsType sig (ΓR ++ A₀ :: ΓL) a = true) →
          judge sig e (ΓR ++ A₀ :: ΓL) md = true →
          ∃ md' e', substMode (Expr.erase A₀) (M₀.rename (· + ΓR.length)) md ΓR.length = some md' ∧
            hsub (Expr.erase A₀) (M₀.rename (· + ΓR.length)) e ΓR.length = some e' ∧
            judge sig e' (ΓR' ++ ΓL) md' = true := by
  intro ΓR hctx
  have hA₀ΓL := Ctx.ok_of_append sig (A₀ :: ΓL) ΓR hctx
  rw [Ctx.ok_cons, Bool.and_eq_true] at hA₀ΓL
  have hA₀s : A₀.TypeShape = true := (judgeWith_typeShape A₀ ΓL).2 hA₀ΓL.1
  have hSA := (substAt_reduceAt hsig (Expr.erase A₀)).1 ΓL A₀ M₀ rfl hA₀s hM₀
  -- the theorem for a given inner context, its substitution in hand
  have main : ∀ ΓR', substCtx (Expr.erase A₀) M₀ ΓR = some ΓR' →
      ∀ (e : Expr) (md : Mode),
        (∀ a, md = .check a → IsType sig (ΓR ++ A₀ :: ΓL) a = true) →
        judge sig e (ΓR ++ A₀ :: ΓL) md = true →
        ∃ md' e', substMode (Expr.erase A₀) (M₀.rename (· + ΓR.length)) md ΓR.length = some md' ∧
          hsub (Expr.erase A₀) (M₀.rename (· + ΓR.length)) e ΓR.length = some e' ∧
          judge sig e' (ΓR' ++ ΓL) md' = true := by
    intro ΓR' hsc e md hmd he
    have hΓs : ∀ a ∈ ΓR ++ ΓL, a.TypeShape = true := fun a ha ↦ by
      have hall := Ctx.ok_typeShape sig _ hctx
      rcases List.mem_append.mp ha with ha | ha
      · exact hall a (List.mem_append_left _ ha)
      · exact hall a (List.mem_append_right _ (List.mem_cons_of_mem _ ha))
    have hmd' : ∃ md', substMode (Expr.erase A₀) (M₀.rename (· + ΓR.length)) md ΓR.length =
        some md' := by
      rcases md with _ | _ | a
      · exact ⟨.kind, rfl⟩
      · exact ⟨.type, rfl⟩
      · obtain ⟨a', ha', -⟩ := hSA a ΓR ΓR' .type .type hΓs (fun _ h ↦ by cases h) hsc
          (hmd a rfl) rfl
        exact ⟨.check a', by simp [substMode, ha']⟩
    obtain ⟨md', hmd'⟩ := hmd'
    obtain ⟨e', he', he'J⟩ := hSA e ΓR ΓR' md md' hΓs
      (fun a h ↦ by
        subst h
        exact (judgeWith_typeShape a _).2 (hmd a rfl)) hsc he hmd'
    exact ⟨md', e', hmd', he', he'J⟩
  obtain ⟨ΓR', hsc, hok⟩ := substCtx_ok hsig hA₀s hM₀ ΓR hctx
  exact ⟨ΓR', hsc, hok, main ΓR' hsc⟩

end Geb.LF

end
