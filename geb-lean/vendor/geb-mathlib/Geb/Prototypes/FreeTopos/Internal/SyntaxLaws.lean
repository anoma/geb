/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Internal.Inversion

set_option doc.verso true in
/-!
# The laws of renaming and substitution

Renaming and substitution of the internal language's terms, each lifted under a binder and
leaving the step of a rose-tree fold in its own context, obey the laws of a monad of terms
over variables: well-scoped λ-terms form a relative monad on the finite sets
(\[AltenkirchChapmanUustalu2015\], Example 2.1), and the terms here, over all de Bruijn
indices, obey the same laws. Renaming is a functor: it preserves composites
({lit}`rename_rename`) and fixes a term under a map that fixes every index ({lit}`rename_id`).
Substitution is the binding of the monad whose unit is the variable: substitution at a variable
is its term ({lit}`subst_var`), substitution of each variable for itself fixes a term
({lit}`subst_id`), and substitution after a substitution is substitution of the substituted terms
({lit}`subst_subst`); renaming is substitution of variables ({lit}`rename_eq_subst`). The two laws
that fix a term hold of a term whose variables are leaves ({lit}`VarLeaves`), since renaming and
substitution rebuild a variable as a leaf; the variables of every term that compiles are leaves
({lit}`varLeaves_of_compile`), so the two laws hold of every term that compiles
({lit}`rename_id_of_compile`, {lit}`subst_id_of_compile`).

Each law is stated with a hypothesis on the maps at each index, so that its lifting under a
binder needs no extensionality; the associativity of substitution under a binder rests on the
laws that commute renaming with substitution ({lit}`subst_rename`, {lit}`rename_subst`). Every
node is a variable, an abstraction, a fold, or plain, renaming and substituting in each child
({lit}`shape`), and each proof treats each kind once.

## Main definitions

* {lit}`Plain` — a label whose node renames and substitutes in each child.
* {lit}`VarLeaves` — a term's variables are leaves.

## Main statements

* {lit}`shape` — the kinds of node.
* {lit}`rename_rename`, {lit}`rename_id` — renaming is a functor.
* {lit}`subst_var`, {lit}`subst_id`, {lit}`subst_subst` — the unit laws and the associativity of
  substitution.
* {lit}`subst_rename`, {lit}`rename_subst`, {lit}`rename_eq_subst` — renaming and substitution
  commute, and renaming is substitution of variables.
* {lit}`varLeaves_of_compile`, {lit}`rename_id_of_compile`, {lit}`subst_id_of_compile` — the
  variables of a term that compiles are leaves, and the laws that fix a term hold of it.

## References

* \[AltenkirchChapmanUustalu2015\]

## Tags

internal language, de Bruijn indices, renaming, substitution, monad laws
-/

set_option doc.verso true

@[expose] public section

namespace Geb.FreeTopos.Internal.Term

open PartialHorn (Tree)

/-- A label at a number of children whose node renames, substitutes in, and tests the occurrence
of a variable in, each child in the node's own context. -/
def Plain (l : Label) (n : ℕ) : Prop :=
  ∀ cs : List Term, cs.length = n →
    (∀ (F : Term → (ℕ → ℕ) → Term) (f : ℕ → ℕ),
      renameStep l (cs.map fun c ↦ (c, F c)) f = RoseTree.node l (cs.map fun c ↦ F c f)) ∧
    (∀ (F : Term → (ℕ → Term) → Term) (σ : ℕ → Term),
      substStep l (cs.map fun c ↦ (c, F c)) σ = RoseTree.node l (cs.map fun c ↦ F c σ)) ∧
    ∀ (F : Term → ℕ → Bool) (d : ℕ),
      occursStep l (cs.map fun c ↦ (c, F c)) d = cs.any fun c ↦ F c d

/-- Every node is a variable, an abstraction of one body, a fold of a natural number or of a list
with its start, its step and its argument, a fold of a rose tree with its step and its argument,
or plain. -/
theorem shape (l : Label) (cs : List Term) :
    (∃ i, l = .var i) ∨ (∃ a t, l = .lam a ∧ cs = [t]) ∨
      (∃ z s m, (l = .natRec ∨ l = .listRec) ∧ cs = [z, s, m]) ∨
      (∃ c s m, l = .roseRec c ∧ cs = [s, m]) ∨ Plain l cs.length := by
  have plain : ∀ {l : Label} {n : ℕ}, (∀ cs : List Term, cs.length = n →
      (∀ (F : Term → (ℕ → ℕ) → Term) (f : ℕ → ℕ),
        renameStep l (cs.map fun c ↦ (c, F c)) f = RoseTree.node l (cs.map fun c ↦ F c f)) ∧
      (∀ (F : Term → (ℕ → Term) → Term) (σ : ℕ → Term),
        substStep l (cs.map fun c ↦ (c, F c)) σ = RoseTree.node l (cs.map fun c ↦ F c σ)) ∧
      ∀ (F : Term → ℕ → Bool) (d : ℕ),
        occursStep l (cs.map fun c ↦ (c, F c)) d = cs.any fun c ↦ F c d) →
      Plain l n := id
  cases l with
  | var i => exact .inl ⟨i, rfl⟩
  | _ =>
    rcases cs with _ | ⟨c₁, _ | ⟨c₂, _ | ⟨c₃, _ | ⟨c₄, cs⟩⟩⟩⟩
    all_goals first
      | exact .inr (.inl ⟨_, _, rfl, rfl⟩)
      | exact .inr (.inr (.inl ⟨_, _, _, .inl rfl, rfl⟩))
      | exact .inr (.inr (.inl ⟨_, _, _, .inr rfl, rfl⟩))
      | exact .inr (.inr (.inr (.inl ⟨_, _, _, rfl, rfl⟩)))
      | refine .inr (.inr (.inr (.inr (plain fun cs' h ↦ ?_))))
        rcases cs' with _ | ⟨d₁, _ | ⟨d₂, _ | ⟨d₃, _ | ⟨d₄, cs'⟩⟩⟩⟩
        all_goals first
          | exact ⟨fun _ _ ↦ rfl, fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩
          | (exfalso; simp only [List.length_cons, List.length_nil] at h; omega)
          | (refine ⟨?_, ?_, ?_⟩ <;> intros <;>
              simp only [renameStep, substStep, occursStep, List.map_cons, List.map_map,
                Function.comp_def, List.any_cons, List.any_map])

/-- A plain node renames each child. -/
theorem rename_plain {l : Label} {n : ℕ} (hp : Plain l n) {cs : List Term} (hl : cs.length = n)
    (f : ℕ → ℕ) : rename (RoseTree.node l cs) f = RoseTree.node l (cs.map fun c ↦ rename c f) := by
  rw [rename_node]
  exact (hp cs hl).1 _ f

/-- A plain node substitutes in each child. -/
theorem subst_plain {l : Label} {n : ℕ} (hp : Plain l n) {cs : List Term} (hl : cs.length = n)
    (σ : ℕ → Term) : subst (RoseTree.node l cs) σ = RoseTree.node l (cs.map fun c ↦ subst c σ) := by
  rw [subst_node]
  exact (hp cs hl).2.1 _ σ

/-- Whether a term's variables are leaves, as a term that compiles has them. -/
def VarLeaves : Term → Bool :=
  RoseTree.elim fun l bs ↦ (match l with | .var _ => bs.isEmpty | _ => true) && bs.all id

/-- A node's variables are leaves exactly when it is a leaf if a variable and its children's
variables are leaves. -/
theorem varLeaves_node (l : Label) (cs : List Term) :
    VarLeaves (RoseTree.node l cs) = true ↔
      (∀ i, l = .var i → cs = []) ∧ ∀ c ∈ cs, VarLeaves c = true := by
  cases l <;> simp [VarLeaves]

/-- Renaming after a renaming is renaming by the composite. -/
theorem rename_rename :
    ∀ (t : Term) (f g h : ℕ → ℕ), (∀ i, g (f i) = h i) → rename (rename t f) g = rename t h :=
  RoseTree.ind fun l cs ih f g h hfg ↦ by
    have lift : ∀ {f g h : ℕ → ℕ}, (∀ i, g (f i) = h i) → ∀ i, liftR g (liftR f i) = liftR h i :=
      fun hfg i ↦ by
        rcases i with _ | j
        · rfl
        · simp [liftR, hfg j]
    have hlift := lift hfg
    rcases shape l cs with ⟨i, rfl⟩ | ⟨a, t, rfl, rfl⟩ | ⟨z, s, m, hl, rfl⟩ | ⟨c, s, m, rfl, rfl⟩ |
      hp
    · simp [rename_node, renameStep, var, hfg i]
    · simp only [rename_node, renameStep, List.map_cons, List.map_nil]
      rw [ih t (by simp) _ _ _ hlift]
    · rcases hl with rfl | rfl
      · simp only [rename_node, renameStep, List.map_cons, List.map_nil]
        rw [ih z (by simp) f g h hfg, ih s (by simp) _ _ _ hlift, ih m (by simp) f g h hfg]
      · simp only [rename_node, renameStep, List.map_cons, List.map_nil]
        rw [ih z (by simp) f g h hfg, ih s (by simp) _ _ _ (lift hlift), ih m (by simp) f g h hfg]
    · simp only [rename_node, renameStep, List.map_cons, List.map_nil]
      rw [ih s (by simp) _ _ _ hlift, ih m (by simp) f g h hfg]
    · rw [rename_plain hp rfl, rename_plain hp (by simp), rename_plain hp rfl, List.map_map]
      exact congrArg _ (List.map_congr_left fun c hc ↦ ih c hc f g h hfg)

/-- A plain node tests the occurrence of a variable in each child. -/
theorem occurs_plain {l : Label} {n : ℕ} (hp : Plain l n) {cs : List Term} (hl : cs.length = n)
    (d : ℕ) : occurs (RoseTree.node l cs) d = cs.any fun c ↦ occurs c d := by
  rw [occurs_node]
  exact (hp cs hl).2.2 _ d

/-- A property holds at a variable a lifted renaming takes to a successor exactly when it holds at
the successor of a variable the renaming takes to the predecessor. -/
theorem exists_liftR (Q : ℕ → Prop) (f : ℕ → ℕ) (j : ℕ) :
    (∃ i, Q i ∧ liftR f i = j + 1) ↔ ∃ i, Q (i + 1) ∧ f i = j := by
  constructor
  · rintro ⟨_ | i, hq, h⟩
    · exact (Nat.succ_ne_zero j h.symm).elim
    · exact ⟨i, hq, Nat.succ.inj h⟩
  · rintro ⟨i, hq, rfl⟩
    exact ⟨i + 1, hq, rfl⟩

/-- A variable occurs in a renamed term exactly when it is the renaming of one that occurs in the
term. -/
theorem occurs_rename :
    ∀ (t : Term) (f : ℕ → ℕ) (j : ℕ), occurs (rename t f) j = true ↔
      ∃ i, occurs t i = true ∧ f i = j :=
  RoseTree.ind fun l cs ih f j ↦ by
    rcases shape l cs with ⟨i, rfl⟩ | ⟨a, t, rfl, rfl⟩ | ⟨z, s, m, hl, rfl⟩ | ⟨c, s, m, rfl, rfl⟩ |
      hp
    · simp only [rename_node, renameStep, var, occurs_node, occursStep, beq_iff_eq]
      exact ⟨fun h ↦ ⟨i, rfl, h⟩, fun ⟨_, h, h'⟩ ↦ h ▸ h'⟩
    · simp only [rename_node, renameStep, occurs_node, occursStep, List.map_cons, List.map_nil]
      exact (ih t (by simp) _ (j + 1)).trans (exists_liftR (fun i ↦ occurs t i = true) f j)
    · have hz := ih z (by simp) f j
      have hm := ih m (by simp) f j
      rcases hl with rfl | rfl
      · have hs := (ih s (by simp) _ (j + 1)).trans (exists_liftR (fun i ↦ occurs s i = true) f j)
        simp only [rename_node, renameStep, occurs_node, occursStep, List.map_cons, List.map_nil,
          Bool.or_eq_true, hz, hs, hm, or_and_right, exists_or]
      · have hs := (ih s (by simp) _ (j + 2)).trans
          ((exists_liftR (fun i ↦ occurs s i = true) _ (j + 1)).trans
            (exists_liftR (fun i ↦ occurs s (i + 1) = true) f j))
        simp only [rename_node, renameStep, occurs_node, occursStep, List.map_cons, List.map_nil,
          Bool.or_eq_true, hz, hs, hm, or_and_right, exists_or]
    · have hs := (ih s (by simp) _ (j + 1)).trans (exists_liftR (fun i ↦ occurs s i = true) f j)
      have hm := ih m (by simp) f j
      simp only [rename_node, renameStep, occurs_node, occursStep, List.map_cons, List.map_nil,
        Bool.or_eq_true, hs, hm, or_and_right, exists_or]
    · rw [rename_plain hp rfl, occurs_plain hp (by simp), List.any_map]
      simp only [List.any_eq_true, Function.comp_apply]
      constructor
      · rintro ⟨c, hc, h⟩
        obtain ⟨i, hi, rfl⟩ := (ih c hc f j).mp h
        exact ⟨i, by rw [occurs_plain hp rfl, List.any_eq_true]; exact ⟨c, hc, hi⟩, rfl⟩
      · rintro ⟨i, hi, rfl⟩
        rw [occurs_plain hp rfl, List.any_eq_true] at hi
        obtain ⟨c, hc, hi⟩ := hi
        exact ⟨c, hc, (ih c hc f _).mpr ⟨i, hi, rfl⟩⟩

/-- Renaming by a map that fixes every index leaves a term whose variables are leaves. -/
theorem rename_id :
    ∀ t : Term, VarLeaves t = true → ∀ f : ℕ → ℕ, (∀ i, f i = i) → rename t f = t :=
  RoseTree.ind fun l cs ih ht f hf ↦ by
    obtain ⟨hv, hcs⟩ := (varLeaves_node l cs).mp ht
    have lift : ∀ {f : ℕ → ℕ}, (∀ i, f i = i) → ∀ i, liftR f i = i := fun hf i ↦ by
      rcases i with _ | j
      · rfl
      · simp [liftR, hf j]
    have hlift := lift hf
    rcases shape l cs with ⟨i, rfl⟩ | ⟨a, t, rfl, rfl⟩ | ⟨z, s, m, hl, rfl⟩ | ⟨c, s, m, rfl, rfl⟩ |
      hp
    · obtain rfl := hv i rfl
      simp [rename_node, renameStep, var, hf i]
    · simp only [rename_node, renameStep, List.map_cons, List.map_nil]
      rw [ih t (by simp) (hcs t (by simp)) _ hlift]
    · rcases hl with rfl | rfl
      · simp only [rename_node, renameStep, List.map_cons, List.map_nil]
        rw [ih z (by simp) (hcs z (by simp)) f hf, ih s (by simp) (hcs s (by simp)) _ hlift,
          ih m (by simp) (hcs m (by simp)) f hf]
      · simp only [rename_node, renameStep, List.map_cons, List.map_nil]
        rw [ih z (by simp) (hcs z (by simp)) f hf, ih s (by simp) (hcs s (by simp)) _ (lift hlift),
          ih m (by simp) (hcs m (by simp)) f hf]
    · simp only [rename_node, renameStep, List.map_cons, List.map_nil]
      rw [ih s (by simp) (hcs s (by simp)) _ hlift, ih m (by simp) (hcs m (by simp)) f hf]
    · rw [rename_plain hp rfl]
      exact congrArg _ ((List.map_congr_left fun c hc ↦ ih c hc (hcs c hc) f hf).trans
        (List.map_id cs))

/-- Substitution at a node of a variable is the variable's term. -/
theorem subst_var_node (i : ℕ) (cs : List Term) (σ : ℕ → Term) :
    subst (RoseTree.node (.var i) cs) σ = σ i := by
  rw [subst_node]
  rfl

/-- Substitution at a variable is the substituted term: the unit law of substitution on the
left. -/
theorem subst_var (i : ℕ) (σ : ℕ → Term) : subst (var i) σ = σ i := subst_var_node i [] σ

/-- Substitution of each variable for itself leaves a term whose variables are leaves: the unit
law of substitution on the right. -/
theorem subst_id :
    ∀ t : Term, VarLeaves t = true → ∀ σ : ℕ → Term, (∀ i, σ i = var i) → subst t σ = t :=
  RoseTree.ind fun l cs ih ht σ hσ ↦ by
    obtain ⟨hv, hcs⟩ := (varLeaves_node l cs).mp ht
    have lift : ∀ {σ : ℕ → Term}, (∀ i, σ i = var i) → ∀ i, liftS σ i = var i := fun hσ i ↦ by
      rcases i with _ | j
      · rfl
      · simp [liftS, hσ j, var, rename_node, renameStep]
    have hlift := lift hσ
    rcases shape l cs with ⟨i, rfl⟩ | ⟨a, t, rfl, rfl⟩ | ⟨z, s, m, hl, rfl⟩ | ⟨c, s, m, rfl, rfl⟩ |
      hp
    · obtain rfl := hv i rfl
      exact (subst_var i σ).trans (hσ i)
    · simp only [subst_node, substStep, List.map_cons, List.map_nil]
      rw [ih t (by simp) (hcs t (by simp)) _ hlift]
    · rcases hl with rfl | rfl
      · simp only [subst_node, substStep, List.map_cons, List.map_nil]
        rw [ih z (by simp) (hcs z (by simp)) σ hσ, ih s (by simp) (hcs s (by simp)) _ hlift,
          ih m (by simp) (hcs m (by simp)) σ hσ]
      · simp only [subst_node, substStep, List.map_cons, List.map_nil]
        rw [ih z (by simp) (hcs z (by simp)) σ hσ, ih s (by simp) (hcs s (by simp)) _ (lift hlift),
          ih m (by simp) (hcs m (by simp)) σ hσ]
    · simp only [subst_node, substStep, List.map_cons, List.map_nil]
      rw [ih s (by simp) (hcs s (by simp)) _ hlift, ih m (by simp) (hcs m (by simp)) σ hσ]
    · rw [subst_plain hp rfl]
      exact congrArg _ ((List.map_congr_left fun c hc ↦ ih c hc (hcs c hc) σ hσ).trans
        (List.map_id cs))

/-- A node other than a variable whose children's variables are leaves has its variables leaves. -/
theorem varLeaves_of_children {l : Label} {cs : List Term} (hl : ∀ i, l ≠ .var i)
    (hc : ∀ c ∈ cs, VarLeaves c = true) : VarLeaves (RoseTree.node l cs) = true :=
  (varLeaves_node l cs).mpr ⟨fun i h ↦ (hl i h).elim, hc⟩

/-- A variable is a leaf. -/
theorem varLeaves_var (i : ℕ) : VarLeaves (var i) = true :=
  (varLeaves_node _ _).mpr ⟨fun _ _ ↦ rfl, by simp⟩

/-- Renaming keeps the variables of a term leaves. -/
theorem varLeaves_rename :
    ∀ t : Term, VarLeaves t = true → ∀ f : ℕ → ℕ, VarLeaves (rename t f) = true :=
  RoseTree.ind fun l cs ih ht f ↦ by
    obtain ⟨hv, hcs⟩ := (varLeaves_node l cs).mp ht
    have ch : ∀ c ∈ cs, ∀ f, VarLeaves (rename c f) = true := fun c hc f ↦ ih c hc (hcs c hc) f
    rcases shape l cs with ⟨i, rfl⟩ | ⟨a, t, rfl, rfl⟩ | ⟨z, s, m, hl, rfl⟩ | ⟨c, s, m, rfl, rfl⟩ |
      hp
    · obtain rfl := hv i rfl
      rw [rename_node]
      exact varLeaves_var _
    · simp only [rename_node, renameStep, List.map_cons, List.map_nil]
      exact varLeaves_of_children (fun _ h ↦ by cases h) (by simpa using ch t (by simp) _)
    · rcases hl with rfl | rfl
      · simp only [rename_node, renameStep, List.map_cons, List.map_nil]
        exact varLeaves_of_children (fun _ h ↦ by cases h)
          (by simpa using ⟨ch z (by simp) _, ch s (by simp) _, ch m (by simp) _⟩)
      · simp only [rename_node, renameStep, List.map_cons, List.map_nil]
        exact varLeaves_of_children (fun _ h ↦ by cases h)
          (by simpa using ⟨ch z (by simp) _, ch s (by simp) _, ch m (by simp) _⟩)
    · simp only [rename_node, renameStep, List.map_cons, List.map_nil]
      exact varLeaves_of_children (fun _ h ↦ by cases h)
        (by simpa using ⟨ch s (by simp) _, ch m (by simp) _⟩)
    · rw [rename_plain hp rfl]
      refine (varLeaves_node _ _).mpr ⟨fun i hi ↦ by rw [hv i hi]; rfl, fun x hx ↦ ?_⟩
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
      exact ch c hc f

/-- Substitution of terms whose variables are leaves keeps the variables of a term leaves. -/
theorem varLeaves_subst :
    ∀ t : Term, VarLeaves t = true → ∀ σ : ℕ → Term, (∀ i, VarLeaves (σ i) = true) →
      VarLeaves (subst t σ) = true :=
  RoseTree.ind fun l cs ih ht σ hσ ↦ by
    obtain ⟨hv, hcs⟩ := (varLeaves_node l cs).mp ht
    have ch : ∀ c ∈ cs, ∀ σ : ℕ → Term, (∀ i, VarLeaves (σ i) = true) →
        VarLeaves (subst c σ) = true := fun c hc σ hσ ↦ ih c hc (hcs c hc) σ hσ
    have lift : ∀ {σ : ℕ → Term}, (∀ i, VarLeaves (σ i) = true) →
        ∀ i, VarLeaves (liftS σ i) = true := fun hσ i ↦ by
      rcases i with _ | i
      · exact varLeaves_var 0
      · exact varLeaves_rename _ (hσ i) _
    rcases shape l cs with ⟨i, rfl⟩ | ⟨a, t, rfl, rfl⟩ | ⟨z, s, m, hl, rfl⟩ | ⟨c, s, m, rfl, rfl⟩ |
      hp
    · obtain rfl := hv i rfl
      rw [subst_var_node]
      exact hσ i
    · simp only [subst_node, substStep, List.map_cons, List.map_nil]
      exact varLeaves_of_children (fun _ h ↦ by cases h) (by simpa using ch t (by simp) _ (lift hσ))
    · rcases hl with rfl | rfl
      · simp only [subst_node, substStep, List.map_cons, List.map_nil]
        exact varLeaves_of_children (fun _ h ↦ by cases h) (by simpa using
          ⟨ch z (by simp) _ hσ, ch s (by simp) _ (lift hσ), ch m (by simp) _ hσ⟩)
      · simp only [subst_node, substStep, List.map_cons, List.map_nil]
        exact varLeaves_of_children (fun _ h ↦ by cases h) (by simpa using
          ⟨ch z (by simp) _ hσ, ch s (by simp) _ (lift (lift hσ)), ch m (by simp) _ hσ⟩)
    · simp only [subst_node, substStep, List.map_cons, List.map_nil]
      exact varLeaves_of_children (fun _ h ↦ by cases h)
        (by simpa using ⟨ch s (by simp) _ (lift hσ), ch m (by simp) _ hσ⟩)
    · rw [subst_plain hp rfl]
      refine (varLeaves_node _ _).mpr ⟨fun i hi ↦ by rw [hv i hi]; rfl, fun x hx ↦ ?_⟩
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
      exact ch c hc σ hσ

/-- The substitution of no objects leaves a label in place. -/
theorem _root_.Geb.FreeTopos.Internal.Label.osubst_nil (l : Label) : l.osubst [] = l := by
  have h : PartialHorn.subst [] = id := funext PartialHorn.subst_nil
  cases l <;> simp only [Label.osubst, h, List.map_id, id]

/-- The substitution of no objects leaves a term in place. -/
theorem _root_.Geb.FreeTopos.Internal.Term.osubst_nil : ∀ t : Term, Term.osubst [] t = t :=
  RoseTree.ind fun l cs ih ↦ by
    rw [Term.osubst_node, Label.osubst_nil]
    exact congrArg _ ((List.map_congr_left ih).trans (List.map_id cs))

/-- Substitutions that agree at the variables occurring in a term substitute in it alike. -/
theorem subst_congr :
    ∀ (t : Term) (σ τ : ℕ → Term), (∀ i, occurs t i = true → σ i = τ i) → subst t σ = subst t τ :=
  RoseTree.ind fun l cs ih σ τ hστ ↦ by
    have lift : ∀ {t : Term} {d : ℕ} {σ τ : ℕ → Term},
        (∀ i, occurs t (i + 1 + d) = true → σ i = τ i) →
        ∀ i, occurs t (i + d) = true → liftS σ i = liftS τ i := fun h i hi ↦ by
      rcases i with _ | j
      · rfl
      · simp only [liftS, h j hi]
    have at_ : ∀ i, occursStep l (cs.map fun c ↦ (c, occurs c)) i = true → σ i = τ i :=
      fun i hi ↦ hστ i (by rw [occurs_node]; exact hi)
    have or₂ : ∀ {a b : Bool}, a = true ∨ b = true → (a || b) = true := fun h ↦ by
      rcases h with rfl | rfl
      · exact Bool.true_or _
      · exact Bool.or_true _
    have or₃ : ∀ {a b c : Bool}, a = true ∨ b = true ∨ c = true → (a || b || c) = true :=
      fun h ↦ by
        rcases h with h | h
        · exact or₂ (.inl (or₂ (.inl h)))
        · rcases h with h | h
          · exact or₂ (.inl (or₂ (.inr h)))
          · exact or₂ (.inr h)
    rcases shape l cs with ⟨i, rfl⟩ | ⟨a, t, rfl, rfl⟩ | ⟨z, s, m, hl, rfl⟩ | ⟨c, s, m, rfl, rfl⟩ |
      hp
    · rw [subst_var_node, subst_var_node]
      exact at_ i (beq_self_eq_true i)
    · simp only [subst_node, substStep, List.map_cons, List.map_nil]
      rw [ih t List.mem_cons_self _ _ (lift (t := t) (d := 0) fun i hi ↦ at_ i hi)]
    · rcases hl with rfl | rfl
      · simp only [subst_node, substStep, List.map_cons, List.map_nil]
        rw [ih z List.mem_cons_self σ τ fun i hi ↦ at_ i (or₃ (.inl hi)),
          ih s (List.mem_cons_of_mem _ List.mem_cons_self) _ _
            (lift (t := s) (d := 0) fun i hi ↦ at_ i (or₃ (.inr (.inl hi)))),
          ih m (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) σ τ
            fun i hi ↦ at_ i (or₃ (.inr (.inr hi)))]
      · simp only [subst_node, substStep, List.map_cons, List.map_nil]
        rw [ih z List.mem_cons_self σ τ fun i hi ↦ at_ i (or₃ (.inl hi)),
          ih s (List.mem_cons_of_mem _ List.mem_cons_self) _ _ (lift (t := s) (d := 0)
            (lift (t := s) (d := 1) fun i hi ↦ at_ i (or₃ (.inr (.inl hi))))),
          ih m (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) σ τ
            fun i hi ↦ at_ i (or₃ (.inr (.inr hi)))]
    · simp only [subst_node, substStep, List.map_cons, List.map_nil]
      rw [ih s List.mem_cons_self _ _
          (lift (t := s) (d := 0) fun i hi ↦ at_ i (or₂ (.inl hi))),
        ih m (List.mem_cons_of_mem _ List.mem_cons_self) σ τ fun i hi ↦ at_ i (or₂ (.inr hi))]
    · rw [subst_plain hp rfl, subst_plain hp rfl]
      exact congrArg _ (List.map_congr_left fun c hc ↦ ih c hc σ τ fun i hi ↦
        hστ i (by rw [occurs_plain hp rfl]; exact List.any_eq_true.mpr ⟨c, hc, hi⟩))

/-- Substitution after a renaming is substitution of the renamed indices' terms. -/
theorem subst_rename :
    ∀ (t : Term) (f : ℕ → ℕ) (σ τ : ℕ → Term), (∀ i, σ (f i) = τ i) →
      subst (rename t f) σ = subst t τ :=
  RoseTree.ind fun l cs ih f σ τ hστ ↦ by
    have lift : ∀ {f : ℕ → ℕ} {σ τ : ℕ → Term}, (∀ i, σ (f i) = τ i) →
        ∀ i, liftS σ (liftR f i) = liftS τ i := fun hστ i ↦ by
      rcases i with _ | j
      · rfl
      · simp [liftR, liftS, hστ j]
    have hlift := lift hστ
    rcases shape l cs with ⟨i, rfl⟩ | ⟨a, t, rfl, rfl⟩ | ⟨z, s, m, hl, rfl⟩ | ⟨c, s, m, rfl, rfl⟩ |
      hp
    · simp only [rename_node, renameStep]
      exact (subst_var (f i) σ).trans ((hστ i).trans (subst_var_node i cs τ).symm)
    · simp only [rename_node, subst_node, renameStep, substStep, List.map_cons, List.map_nil]
      rw [ih t (by simp) _ _ _ hlift]
    · rcases hl with rfl | rfl
      · simp only [rename_node, subst_node, renameStep, substStep, List.map_cons, List.map_nil]
        rw [ih z (by simp) f σ τ hστ, ih s (by simp) _ _ _ hlift, ih m (by simp) f σ τ hστ]
      · simp only [rename_node, subst_node, renameStep, substStep, List.map_cons, List.map_nil]
        rw [ih z (by simp) f σ τ hστ, ih s (by simp) _ _ _ (lift hlift), ih m (by simp) f σ τ hστ]
    · simp only [rename_node, subst_node, renameStep, substStep, List.map_cons, List.map_nil]
      rw [ih s (by simp) _ _ _ hlift, ih m (by simp) f σ τ hστ]
    · rw [rename_plain hp rfl, subst_plain hp (by simp), subst_plain hp rfl, List.map_map]
      exact congrArg _ (List.map_congr_left fun c hc ↦ ih c hc f σ τ hστ)

/-- Renaming after a substitution is substitution of the renamed terms. -/
theorem rename_subst :
    ∀ (t : Term) (σ : ℕ → Term) (f : ℕ → ℕ) (τ : ℕ → Term), (∀ i, rename (σ i) f = τ i) →
      rename (subst t σ) f = subst t τ :=
  RoseTree.ind fun l cs ih σ f τ hστ ↦ by
    have lift : ∀ {σ : ℕ → Term} {f : ℕ → ℕ} {τ : ℕ → Term}, (∀ i, rename (σ i) f = τ i) →
        ∀ i, rename (liftS σ i) (liftR f) = liftS τ i := fun {σ f τ} hστ i ↦ by
      rcases i with _ | j
      · simp [liftS, liftR, var, rename_node, renameStep]
      · change rename (rename (σ j) Nat.succ) (liftR f) = rename (τ j) Nat.succ
        rw [← hστ j, rename_rename (σ j) f Nat.succ (fun k ↦ f k + 1) fun _ ↦ rfl]
        exact rename_rename _ _ _ _ fun _ ↦ rfl
    have hlift := lift hστ
    rcases shape l cs with ⟨i, rfl⟩ | ⟨a, t, rfl, rfl⟩ | ⟨z, s, m, hl, rfl⟩ | ⟨c, s, m, rfl, rfl⟩ |
      hp
    · rw [subst_var_node, subst_var_node]
      exact hστ i
    · simp only [rename_node, subst_node, renameStep, substStep, List.map_cons, List.map_nil]
      rw [ih t (by simp) _ _ _ hlift]
    · rcases hl with rfl | rfl
      · simp only [rename_node, subst_node, renameStep, substStep, List.map_cons, List.map_nil]
        rw [ih z (by simp) σ f τ hστ, ih s (by simp) _ _ _ hlift, ih m (by simp) σ f τ hστ]
      · simp only [rename_node, subst_node, renameStep, substStep, List.map_cons, List.map_nil]
        rw [ih z (by simp) σ f τ hστ, ih s (by simp) _ _ _ (lift hlift), ih m (by simp) σ f τ hστ]
    · simp only [rename_node, subst_node, renameStep, substStep, List.map_cons, List.map_nil]
      rw [ih s (by simp) _ _ _ hlift, ih m (by simp) σ f τ hστ]
    · rw [subst_plain hp rfl, rename_plain hp (by simp), subst_plain hp rfl, List.map_map]
      exact congrArg _ (List.map_congr_left fun c hc ↦ ih c hc σ f τ hστ)

/-- Substitution after a substitution is substitution of the substituted terms: the associativity
of substitution. -/
theorem subst_subst :
    ∀ (t : Term) (σ τ ρ : ℕ → Term), (∀ i, subst (σ i) τ = ρ i) →
      subst (subst t σ) τ = subst t ρ :=
  RoseTree.ind fun l cs ih σ τ ρ hρ ↦ by
    have lift : ∀ {σ τ ρ : ℕ → Term}, (∀ i, subst (σ i) τ = ρ i) →
        ∀ i, subst (liftS σ i) (liftS τ) = liftS ρ i := fun {σ τ ρ} hρ i ↦ by
      rcases i with _ | j
      · exact subst_var 0 _
      · change subst (rename (σ j) Nat.succ) (liftS τ) = rename (ρ j) Nat.succ
        rw [subst_rename (σ j) Nat.succ (liftS τ) (fun k ↦ rename (τ k) Nat.succ) fun _ ↦ rfl,
          ← hρ j]
        exact (rename_subst (σ j) τ Nat.succ _ fun _ ↦ rfl).symm
    have hlift := lift hρ
    rcases shape l cs with ⟨i, rfl⟩ | ⟨a, t, rfl, rfl⟩ | ⟨z, s, m, hl, rfl⟩ | ⟨c, s, m, rfl, rfl⟩ |
      hp
    · rw [subst_var_node, subst_var_node]
      exact hρ i
    · simp only [subst_node, substStep, List.map_cons, List.map_nil]
      rw [ih t (by simp) _ _ _ hlift]
    · rcases hl with rfl | rfl
      · simp only [subst_node, substStep, List.map_cons, List.map_nil]
        rw [ih z (by simp) σ τ ρ hρ, ih s (by simp) _ _ _ hlift, ih m (by simp) σ τ ρ hρ]
      · simp only [subst_node, substStep, List.map_cons, List.map_nil]
        rw [ih z (by simp) σ τ ρ hρ, ih s (by simp) _ _ _ (lift hlift), ih m (by simp) σ τ ρ hρ]
    · simp only [subst_node, substStep, List.map_cons, List.map_nil]
      rw [ih s (by simp) _ _ _ hlift, ih m (by simp) σ τ ρ hρ]
    · rw [subst_plain hp rfl, subst_plain hp (by simp), subst_plain hp rfl, List.map_map]
      exact congrArg _ (List.map_congr_left fun c hc ↦ ih c hc σ τ ρ hρ)

/-- Renaming is substitution of the renamed variables. -/
theorem rename_eq_subst :
    ∀ (t : Term) (f : ℕ → ℕ) (σ : ℕ → Term), (∀ i, var (f i) = σ i) → rename t f = subst t σ :=
  RoseTree.ind fun l cs ih f σ hσ ↦ by
    have lift : ∀ {f : ℕ → ℕ} {σ : ℕ → Term}, (∀ i, var (f i) = σ i) →
        ∀ i, var (liftR f i) = liftS σ i := fun hσ i ↦ by
      rcases i with _ | j
      · rfl
      · simp [liftR, liftS, ← hσ j, var, rename_node, renameStep]
    have hlift := lift hσ
    rcases shape l cs with ⟨i, rfl⟩ | ⟨a, t, rfl, rfl⟩ | ⟨z, s, m, hl, rfl⟩ | ⟨c, s, m, rfl, rfl⟩ |
      hp
    · rw [subst_var_node, rename_node]
      exact hσ i
    · simp only [rename_node, subst_node, renameStep, substStep, List.map_cons, List.map_nil]
      rw [ih t (by simp) _ _ hlift]
    · rcases hl with rfl | rfl
      · simp only [rename_node, subst_node, renameStep, substStep, List.map_cons, List.map_nil]
        rw [ih z (by simp) f σ hσ, ih s (by simp) _ _ hlift, ih m (by simp) f σ hσ]
      · simp only [rename_node, subst_node, renameStep, substStep, List.map_cons, List.map_nil]
        rw [ih z (by simp) f σ hσ, ih s (by simp) _ _ (lift hlift), ih m (by simp) f σ hσ]
    · simp only [rename_node, subst_node, renameStep, substStep, List.map_cons, List.map_nil]
      rw [ih s (by simp) _ _ hlift, ih m (by simp) f σ hσ]
    · rw [rename_plain hp rfl, subst_plain hp rfl]
      exact congrArg _ (List.map_congr_left fun c hc ↦ ih c hc f σ hσ)

/-- The variables of a term that compiles are leaves. -/
theorem varLeaves_of_compile {G : Globals} {n : ℕ} (s : Term) :
    ∀ (X : Tree) (e : List (Tree × Tree)) (r : Tree × Tree), compile G n s X e = some r →
      VarLeaves s = true := by
  refine RoseTree.ind (P := fun s ↦ ∀ (X : Tree) (e : List (Tree × Tree)) (r : Tree × Tree),
    compile G n s X e = some r → VarLeaves s = true) (fun l cs ih ↦ ?_) s
  intro X e r h
  have leaves : (∀ i, l ≠ .var i) → (∀ c ∈ cs, ∃ X e r, compile G n c X e = some r) →
      VarLeaves (RoseTree.node l cs) = true := fun hl hc ↦
    (varLeaves_node l cs).mpr ⟨fun i hi ↦ (hl i hi).elim, fun c hc' ↦
      let ⟨X, e, r, h⟩ := hc c hc'
      ih c hc' X e r h⟩
  cases l with
  | var i =>
    obtain ⟨rfl, -⟩ := compile_var_iff.mp h
    exact (varLeaves_node _ _).mpr ⟨fun _ _ ↦ rfl, by simp⟩
  | star =>
    obtain ⟨rfl, -⟩ := compile_star_iff.mp h
    exact leaves (fun _ h ↦ by cases h) (by simp)
  | pair =>
    obtain ⟨t, u, f, a, g, b, rfl, ht, hu, -⟩ := compile_pair_iff.mp h
    exact leaves (fun _ h ↦ by cases h) (by simpa using ⟨⟨_, _, _, _, ht⟩, ⟨_, _, _, _, hu⟩⟩)
  | fst =>
    obtain ⟨t, f, a, b, rfl, ht, -⟩ := compile_fst_iff.mp h
    exact leaves (fun _ h ↦ by cases h) (by simpa using ⟨_, _, _, _, ht⟩)
  | snd =>
    obtain ⟨t, f, a, b, rfl, ht, -⟩ := compile_snd_iff.mp h
    exact leaves (fun _ h ↦ by cases h) (by simpa using ⟨_, _, _, _, ht⟩)
  | lam a =>
    obtain ⟨t, f, b, rfl, -, ht, -⟩ := compile_lam_iff.mp h
    exact leaves (fun _ h ↦ by cases h) (by simpa using ⟨_, _, _, _, ht⟩)
  | app =>
    obtain ⟨t, u, rfl, f, a, b, ht, g, hu, -⟩ := compile_app_iff.mp h
    exact leaves (fun _ h ↦ by cases h) (by simpa using ⟨⟨_, _, _, _, ht⟩, ⟨_, _, _, _, hu⟩⟩)
  | arr k θ =>
    obtain ⟨t, rfl, p, -, g, ht, -⟩ := compile_arr_iff.mp h
    exact leaves (fun _ h ↦ by cases h) (by simpa using ⟨_, _, _, _, ht⟩)
  | natRec =>
    obtain ⟨z, s, m, rfl, z', c, hz, s', hs, m', hm, -⟩ := compile_natRec_iff.mp h
    exact leaves (fun _ h ↦ by cases h)
      (by simpa using ⟨⟨_, _, _, _, hz⟩, ⟨_, _, _, _, hs⟩, ⟨_, _, _, _, hm⟩⟩)
  | listRec =>
    obtain ⟨z, s, m, rfl, m', a, hm, z', c, hz, s', hs, -⟩ := compile_listRec_iff.mp h
    exact leaves (fun _ h ↦ by cases h)
      (by simpa using ⟨⟨_, _, _, _, hz⟩, ⟨_, _, _, _, hs⟩, ⟨_, _, _, _, hm⟩⟩)
  | roseRec c =>
    obtain ⟨s, m, m', t, a, F, s', rfl, -, hm, -, hs, -⟩ := compile_roseRec_iff.mp h
    exact leaves (fun _ h ↦ by cases h) (by simpa using ⟨⟨_, _, _, _, hs⟩, ⟨_, _, _, _, hm⟩⟩)
  | defn k θ =>
    obtain ⟨d, rs, -, hrs, -⟩ := compile_defn_iff.mp h
    refine leaves (fun _ h ↦ by cases h) fun c hc ↦ ?_
    rw [PartialHorn.mapM_eq_some_iff] at hrs
    obtain ⟨r', -, hr'⟩ := List.mem_map.mp (hrs ▸ List.mem_map_of_mem hc :
      compile G n c X e ∈ rs.map some)
    exact ⟨X, e, r', hr'.symm⟩
  | eq =>
    obtain ⟨t, u, rfl, f, a, ht, g, hu, -⟩ := compile_eq_iff.mp h
    exact leaves (fun _ h ↦ by cases h) (by simpa using ⟨⟨_, _, _, _, ht⟩, ⟨_, _, _, _, hu⟩⟩)

/-- Renaming by a map that fixes every index leaves a term that compiles. -/
theorem rename_id_of_compile {G : Globals} {n : ℕ} {t : Term} {X : Tree}
    {e : List (Tree × Tree)} {r : Tree × Tree} (h : compile G n t X e = some r) (f : ℕ → ℕ)
    (hf : ∀ i, f i = i) : rename t f = t :=
  rename_id t (varLeaves_of_compile t X e r h) f hf

/-- Substitution of each variable for itself leaves a term that compiles. -/
theorem subst_id_of_compile {G : Globals} {n : ℕ} {t : Term} {X : Tree}
    {e : List (Tree × Tree)} {r : Tree × Tree} (h : compile G n t X e = some r)
    (σ : ℕ → Term) (hσ : ∀ i, σ i = var i) : subst t σ = t :=
  subst_id t (varLeaves_of_compile t X e r h) σ hσ

end Geb.FreeTopos.Internal.Term

end
