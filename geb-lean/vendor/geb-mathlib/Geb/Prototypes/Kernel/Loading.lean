/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Kernel.Reader
public import Geb.Prototypes.Kernel.Subst

set_option doc.verso true in
/-!
# Loading a program, one definition at a time

{name}`Geb.Kernel.load` checks and evaluates a program's definitions in order, each in the
globals the definitions before it load. This module states the loading as a fold of one step
({lit}`loadStep`), so that a program's loading can be proved one definition at a time, and reads
a definition's meaning off a step that appends its global. A step is proved from the definition's
meaning ({lit}`loadStep_of_infer`), and the meaning from the equations of the checker-evaluator at
the forms of term ({lit}`Geb/Prototypes/GoedelT/Equations.lean`), with those of a variable, a
primitive and a reference here. A reference is proved in globals that are a list reversed
({lit}`infer_ref_reverse`), so that the global it names is reached from the last one appended,
the list of the globals before a definition being built by appending.

## Main definitions

* {lit}`loadStep` — the step of loading a program.

## Main statements

* {lit}`load_eq_foldl` — loading a program is the fold of its step.
* {lit}`infer_of_loadStep` — a definition that loads has a meaning at its global's type.
* {lit}`loadStep_of_infer` — a definition with a meaning loads the global of its meaning.
* {lit}`infer_ref_reverse` — the meaning of a reference in globals that are a list reversed.

## Tags

program, loading, global environment
-/

set_option doc.verso true

@[expose] public section

namespace Geb.Kernel

/-- The step of loading a program: a definition checked and evaluated in the globals before it,
and appended to them. -/
def loadStep (acc : Option (List Glob)) (t : Tree) : Option (List Glob) := do
  let G ← acc
  let m ← infer G [] t
  some (G ++ [⟨m.1, m.2 ()⟩])

/-- A list of globals with one more appended. -/
def snoc (G : List Glob) (g : Glob) : List Glob := G ++ [g]

/-- Loading a program is the fold of its step over its definitions. -/
theorem load_eq_foldl (D : List Tree) : load D = D.foldl loadStep (some []) := rfl

/-- A step that appends a global, followed by the rest of the fold. -/
theorem foldl_loadStep_cons {D : List Tree} {t : Tree} {G G' : List Glob} {g : Glob}
    (h : loadStep (some G) t = some (G ++ [g]))
    (h' : D.foldl loadStep (some (G ++ [g])) = some G') :
    (t :: D).foldl loadStep (some G) = some G' := by
  rw [List.foldl_cons, h, h']

/-- Globals with one more appended, followed by a list, are the globals followed by that one and
the list. -/
theorem snoc_append {G S T : List Glob} {g : Glob} (h : G ++ g :: S = T) : snoc G g ++ S = T := by
  rw [snoc, List.append_assoc]
  exact h

/-- A program that loads to globals loads to a list they are equal to, followed by nothing. -/
theorem load_eq_of_append_nil {D : List Tree} {G G' : List Glob} (h : load D = some G)
    (h' : G ++ [] = G') : load D = some G' := by
  rw [h, ← h', List.append_nil]

/-- A definition that loads after globals has, in them, a meaning at the type of the global it
appends. -/
theorem infer_of_loadStep {G : List Glob} {t : Tree} {g : Glob}
    (h : loadStep (some G) t = some (snoc G g)) : ∃ f, infer G [] t = some ⟨g.1, f⟩ := by
  unfold loadStep snoc at h
  simp only [Option.bind_eq_bind, Option.bind_some] at h
  rcases hm : infer G [] t with _ | m
  · rw [hm] at h
    cases h
  · rw [hm, Option.bind_some] at h
    obtain rfl := (List.cons.inj (List.append_cancel_left (Option.some.inj h))).1
    exact ⟨m.2, rfl⟩

/-- The innermost variable of a context has the context's first type. -/
theorem infer_var0 (G : List Glob) (Γ : Ctx) (A : Tree) :
    infer G (A :: Γ) (Tm.var 0) = some ⟨A, Prod.fst⟩ := rfl

/-- A definition with a meaning in the globals before it appends the global of its type and its
value. -/
theorem loadStep_of_infer {G : List Glob} {t A : Tree} {f : Ctx.den [] → Ty.den A}
    (h : infer G [] t = some ⟨A, f⟩) : loadStep (some G) t = some (snoc G ⟨A, f ()⟩) := by
  simp only [loadStep, h, Option.bind_eq_bind, Option.bind_some, snoc]

/-- The denotation of a variable bound in the context: its lookup there. -/
theorem infer_var_get (G : List Glob) (Γ : Ctx) (i : ℕ) (h : (Γ.var i).isSome = true) :
    infer G Γ (Tm.var i) = some ⟨((Γ.var i).get h).1, ((Γ.var i).get h).2⟩ := by
  rw [infer_var, Option.some_get]

/-- The denotation of a primitive: its entry in {name}`prims`. -/
theorem infer_prim (G : List Glob) (Γ : Ctx) (i : ℕ) (h : i < prims.length) :
    infer G Γ (mk Label.prim [leaf i]) = some ⟨prims[i].1, fun _ ↦ prims[i].2⟩ := by
  simp only [mk, infer_node, List.map_cons, List.map_nil, inferStep, leaf, RoseTree.label_node,
    List.getElem?_eq_getElem h, Option.map_some, constant]

/-- The denotation of a reference, in globals that are a list reversed: the global of that list
as far from its end as the reference's index is from the start. -/
theorem infer_ref_reverse {G R : List Glob} (Γ : Ctx) (i j : ℕ) {A : Tree} {a : Ty.den A}
    (hG : G = R.reverse) (h : i + j + 1 = R.length) (hg : R[i]? = some ⟨A, a⟩) :
    infer G Γ (mk Label.ref [leaf j]) = some ⟨A, fun _ ↦ a⟩ := by
  have hj : G[j]? = some ⟨A, a⟩ := by
    rw [hG, List.getElem?_reverse (by omega), show R.length - 1 - j = i by omega, hg]
  simp only [mk, infer_node, List.map_cons, List.map_nil, inferStep, leaf, RoseTree.label_node,
    hj, Option.map_some, constant]

/-- Globals that are a list reversed, with one more appended, are the list with that one before
it, reversed. -/
theorem snoc_reverse {G R : List Glob} (g : Glob) (h : G = R.reverse) :
    snoc G g = (g :: R).reverse := by
  rw [snoc, h, List.reverse_cons]

/-- The length of a list with one more global before it. -/
theorem length_cons_of {R : List Glob} {m : ℕ} (g : Glob) (h : R.length = m) :
    (g :: R).length = m + 1 := by
  rw [List.length_cons, h]

end Geb.Kernel

end
