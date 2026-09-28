/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Prototypes.FreeTopos.Internal.Compile

set_option doc.verso true in
/-!
# The inversion of the compilation

For each label, the compilation of a node of that label succeeds exactly when its children's
compilations do, with the types the label requires, and its result is then the one the label
builds from theirs.

## Main statements

* {lit}`compile_node` — the compilation of a node is its step at its children's compilations.
* {lit}`compile_pair_iff` and the other lemmas of the form {lit}`compile_*_iff` — the inversion
  of each label's step.

## Tags

internal language, compilation, inversion
-/

set_option doc.verso true

@[expose] public section

namespace Geb.FreeTopos.Internal

open PartialHorn (Tree op)
open Sorts
open scoped FinEnum

variable {G : Globals} {n : ℕ}

/-- The factors of a product are its arguments. -/
theorem prodParts_eq_some {p a b : Tree} : prodParts p = some (a, b) ↔ p = prod a b := by
  constructor
  · intro h
    unfold prodParts at h
    split at h
    · split_ifs at h with hp
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some_inj.mp h)
      exact hp
    · simp at h
  · rintro rfl
    simp [prodParts, prod, op]

/-- The summands of a coproduct are its arguments. -/
theorem coprodParts_eq_some {p a b : Tree} : coprodParts p = some (a, b) ↔ p = coprod a b := by
  constructor
  · intro h
    unfold coprodParts at h
    split at h
    · split_ifs at h with hp
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some_inj.mp h)
      exact hp
    · simp at h
  · rintro rfl
    simp [coprodParts, coprod, op]

/-- The domain and codomain of an exponential are its arguments. -/
theorem expParts_eq_some {p a b : Tree} : expParts p = some (a, b) ↔ p = exp a b := by
  constructor
  · intro h
    unfold expParts at h
    split at h
    · split_ifs at h with hp
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some_inj.mp h)
      exact hp
    · simp at h
  · rintro rfl
    simp [expParts, exp, op]

/-- A rose-tree object over a type of labels is not the rose-tree object. -/
theorem lrose_ne_rose (a : Tree) : lrose a ≠ rose := fun h ↦ by
  simpa [lrose, rose, op] using congrArg RoseTree.label h

/-- A rose-tree object's type of labels and fold: the natural numbers object and the fold of the
rose-tree object, or a rose-tree object's type of labels and the fold over it. -/
theorem roseParts_eq_some {p a : Tree} {F : Tree → Tree} : roseParts p = some (a, F) ↔
    (p = rose ∧ a = nat ∧ F = roseRec) ∨ (p = lrose a ∧ F = lroseRec a) := by
  constructor
  · intro h
    unfold roseParts at h
    split_ifs at h with h₀
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some_inj.mp h)
      exact .inl ⟨h₀, rfl, rfl⟩
    · split at h
      · split_ifs at h with hp
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some_inj.mp h)
        exact .inr ⟨hp, rfl⟩
      · simp at h
  · rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · simp [roseParts]
    · rw [roseParts, if_neg (lrose_ne_rose a)]
      simp [lrose, op]

/-- The type of labels of a rose-tree object over it is its argument. -/
theorem roseParts_lrose (a : Tree) : roseParts (lrose a) = some (a, lroseRec a) :=
  roseParts_eq_some.mpr (.inr ⟨rfl, rfl⟩)

/-- The element type of a list object is its argument. -/
theorem listPart_eq_some {p a : Tree} : listPart p = some a ↔ p = list a := by
  constructor
  · intro h
    unfold listPart at h
    split at h
    · split_ifs at h with hp
      obtain rfl := Option.some_inj.mp h
      exact hp
    · simp at h
  · rintro rfl
    simp [listPart, list, op]

/-- The compilation of a node is its step at its children's compilations. -/
theorem compile_node (l : Label) (cs : List Term) (X : Tree) (e : List (Tree × Tree)) :
    compile G n (RoseTree.node l cs) X e =
      compileStep G n l (cs.map fun c ↦ (c, compile G n c)) X e :=
  congrFun (congrFun (RoseTree.para_node _ l cs) X) e

/-- The compilation of a pair. -/
theorem compile_pair_iff {cs : List Term} {X : Tree} {e : List (Tree × Tree)}
    {r : Tree × Tree} : compile G n (RoseTree.node .pair cs) X e = some r ↔
      ∃ t u f a g b, cs = [t, u] ∧ compile G n t X e = some (f, a) ∧
        compile G n u X e = some (g, b) ∧ (pair f g, prod a b) = r := by
  rw [compile_node]
  rcases cs with _ | ⟨t, _ | ⟨u, _ | ⟨v, cs⟩⟩⟩ <;>
    simp [compileStep, Option.bind_eq_some_iff, Prod.exists]

/-- The compilation of a variable. -/
theorem compile_var_iff {i : ℕ} {cs : List Term} {X : Tree} {e : List (Tree × Tree)}
    {r : Tree × Tree} : compile G n (RoseTree.node (.var i) cs) X e = some r ↔
      cs = [] ∧ e[i]? = some r := by
  rw [compile_node]
  rcases cs with _ | ⟨t, cs⟩ <;> simp [compileStep]

/-- The compilation of the element of the terminal object. -/
theorem compile_star_iff {cs : List Term} {X : Tree} {e : List (Tree × Tree)}
    {r : Tree × Tree} : compile G n (RoseTree.node .star cs) X e = some r ↔
      cs = [] ∧ (bang X, one) = r := by
  rw [compile_node]
  rcases cs with _ | ⟨t, cs⟩ <;> simp [compileStep]

/-- The compilation of a first component. -/
theorem compile_fst_iff {cs : List Term} {X : Tree} {e : List (Tree × Tree)}
    {r : Tree × Tree} : compile G n (RoseTree.node .fst cs) X e = some r ↔
      ∃ t f a b, cs = [t] ∧ compile G n t X e = some (f, prod a b) ∧
        (comp (fst a b) f, a) = r := by
  rw [compile_node]
  rcases cs with _ | ⟨t, _ | ⟨u, cs⟩⟩ <;>
    simp [compileStep, Option.bind_eq_some_iff, Prod.exists, prodParts_eq_some]

/-- The compilation of a second component. -/
theorem compile_snd_iff {cs : List Term} {X : Tree} {e : List (Tree × Tree)}
    {r : Tree × Tree} : compile G n (RoseTree.node .snd cs) X e = some r ↔
      ∃ t f a b, cs = [t] ∧ compile G n t X e = some (f, prod a b) ∧
        (comp (snd a b) f, b) = r := by
  rw [compile_node]
  rcases cs with _ | ⟨t, _ | ⟨u, cs⟩⟩ <;>
    simp [compileStep, Option.bind_eq_some_iff, Prod.exists, prodParts_eq_some]

/-- The compilation of an abstraction. -/
theorem compile_lam_iff {a : Tree} {cs : List Term} {X : Tree} {e : List (Tree × Tree)}
    {r : Tree × Tree} : compile G n (RoseTree.node (.lam a) cs) X e = some r ↔
      ∃ t f b, cs = [t] ∧ IsTy G n a = true ∧
        compile G n t (prod X a) (extEnv X a e) = some (f, b) ∧
        (curry X a f, exp a b) = r := by
  rw [compile_node]
  rcases cs with _ | ⟨t, _ | ⟨u, cs⟩⟩ <;>
    simp [compileStep, Option.bind_eq_some_iff, Prod.exists]

/-- The compilation of an application. -/
theorem compile_app_iff {cs : List Term} {X : Tree} {e : List (Tree × Tree)}
    {r : Tree × Tree} : compile G n (RoseTree.node .app cs) X e = some r ↔
      ∃ t u, cs = [t, u] ∧ ∃ f a b, compile G n t X e = some (f, exp a b) ∧
        ∃ g, compile G n u X e = some (g, a) ∧ (comp (ev a b) (pair f g), b) = r := by
  rw [compile_node]
  rcases cs with _ | ⟨t, _ | ⟨u, _ | ⟨v, cs⟩⟩⟩ <;>
    simp [compileStep, Option.bind_eq_some_iff, Prod.exists, expParts_eq_some]

/-- The compilation of an application of a primitive arrow. -/
theorem compile_arr_iff {k : ℕ} {θ : List Tree} {cs : List Term} {X : Tree}
    {e : List (Tree × Tree)} {r : Tree × Tree} :
    compile G n (RoseTree.node (.arr k θ) cs) X e = some r ↔
      ∃ t, cs = [t] ∧ ∃ p, G.prims[k]? = some p ∧ ∃ g, compile G n t X e =
        some (g, PartialHorn.subst θ p.dom) ∧ θ.length = p.arity ∧ θ.all (IsTy G n) = true ∧
        (comp (PartialHorn.subst θ p.arrow) g, PartialHorn.subst θ p.cod) = r := by
  rw [compile_node]
  rcases cs with _ | ⟨t, _ | ⟨u, cs⟩⟩ <;>
    simp [compileStep, Option.bind_eq_some_iff, Prod.exists, and_assoc]

/-- The compilation of a fold of a natural number. -/
theorem compile_natRec_iff {cs : List Term} {X : Tree} {e : List (Tree × Tree)}
    {r : Tree × Tree} : compile G n (RoseTree.node .natRec cs) X e = some r ↔
      ∃ z s m, cs = [z, s, m] ∧ ∃ z' c, compile G n z one [] = some (z', c) ∧
        ∃ s', compile G n s c [(idt c, c)] = some (s', c) ∧
        ∃ m', compile G n m X e = some (m', nat) ∧ (comp (natRec z' s') m', c) = r := by
  rw [compile_node]
  rcases cs with _ | ⟨z, _ | ⟨s, _ | ⟨m, _ | ⟨v, cs⟩⟩⟩⟩ <;>
    simp [compileStep, Option.bind_eq_some_iff, Prod.exists]

/-- The compilation of a fold of a list. -/
theorem compile_listRec_iff {cs : List Term} {X : Tree} {e : List (Tree × Tree)}
    {r : Tree × Tree} : compile G n (RoseTree.node .listRec cs) X e = some r ↔
      ∃ z s m, cs = [z, s, m] ∧ ∃ m' a, compile G n m X e = some (m', list a) ∧
        ∃ z' c, compile G n z one [] = some (z', c) ∧
        ∃ s', compile G n s (prod a c) [(snd a c, c), (fst a c, a)] = some (s', c) ∧
        (comp (listRec a z' s') m', c) = r := by
  rw [compile_node]
  rcases cs with _ | ⟨z, _ | ⟨s, _ | ⟨m, _ | ⟨v, cs⟩⟩⟩⟩ <;>
    simp [compileStep, Option.bind_eq_some_iff, Prod.exists, listPart_eq_some]

/-- The compilation of a fold of a rose tree. -/
theorem compile_roseRec_iff {c : Tree} {cs : List Term} {X : Tree} {e : List (Tree × Tree)}
    {r : Tree × Tree} : compile G n (RoseTree.node (.roseRec c) cs) X e = some r ↔
      ∃ s m m' t a F s', cs = [s, m] ∧ IsTy G n c = true ∧ compile G n m X e = some (m', t) ∧
        roseParts t = some (a, F) ∧
        compile G n s (prod a (list c)) [(idt (prod a (list c)), prod a (list c))] =
          some (s', c) ∧ (comp (F s') m', c) = r := by
  rw [compile_node]
  rcases cs with _ | ⟨s, _ | ⟨m, _ | ⟨v, cs⟩⟩⟩ <;>
    simp [compileStep, Option.bind_eq_some_iff, Prod.exists]

/-- A definition is a given definition of the language exactly when it is that one. -/
theorem Definition.language?_eq_some {d : Definition} {d' : Defn} :
    d.language? = some d' ↔ d = .language d' := by
  cases d <;> simp [Definition.language?]

/-- The definition of the language at a position, where there is one. -/
theorem bind_language?_eq_some {o : Option Definition} {d : Defn} :
    o.bind Definition.language? = some d ↔ o = some (.language d) := by
  simp [Option.bind_eq_some_iff, Definition.language?_eq_some]

/-- The compilation of an application of a definition. -/
theorem compile_defn_iff {k : ℕ} {θ : List Tree} {cs : List Term} {X : Tree}
    {e : List (Tree × Tree)} {r : Tree × Tree} :
    compile G n (RoseTree.node (.defn k θ) cs) X e = some r ↔
      ∃ d rs, G.defs[k]? = some (.language d) ∧ cs.mapM (fun c ↦ compile G n c X e) = some rs ∧
        θ.length = d.arity ∧ θ.all (IsTy G n) = true ∧
        rs.map Prod.snd = d.params.map (PartialHorn.subst θ) ∧
        (comp (op (G.base + k) θ) (tuple X (rs.map Prod.fst)), PartialHorn.subst θ d.type) = r := by
  rw [compile_node]
  simp [compileStep, Option.bind_eq_some_iff, List.mapM_map, Function.comp_def, and_assoc,
    Definition.language?_eq_some]

/-- The compilation of an equality. -/
theorem compile_eq_iff {cs : List Term} {X : Tree} {e : List (Tree × Tree)} {r : Tree × Tree} :
    compile G n (RoseTree.node .eq cs) X e = some r ↔
      ∃ t u, cs = [t, u] ∧ ∃ f a, compile G n t X e = some (f, a) ∧
        ∃ g, compile G n u X e = some (g, a) ∧ (comp (chi (diag a)) (pair f g), omega) = r := by
  rw [compile_node]
  rcases cs with _ | ⟨t, _ | ⟨u, _ | ⟨v, cs⟩⟩⟩ <;>
    simp [compileStep, Option.bind_eq_some_iff, Prod.exists]

end Geb.FreeTopos.Internal

end
