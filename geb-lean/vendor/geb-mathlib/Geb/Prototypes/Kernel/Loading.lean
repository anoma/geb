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
a definition's meaning off a step that appends its global.

## Main definitions

* {lit}`loadStep` — the step of loading a program.
* {lit}`defType` — the type of a definition in the globals before it.

## Main statements

* {lit}`load_eq_foldl` — loading a program is the fold of its step.
* {lit}`infer_of_loadStep` — a definition that loads has a meaning at its global's type.

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

/-- The type of a definition in the globals before it, or the type of trees where it is
ill-typed. -/
def defType (G : List Glob) (t : Tree) : Tree := ((infer G [] t).map (·.1)).getD tT

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

end Geb.Kernel

end
