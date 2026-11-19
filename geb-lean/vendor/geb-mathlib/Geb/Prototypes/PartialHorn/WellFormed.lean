/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.PartialHorn.Definitional

set_option doc.verso true in
/-!
# The decision of a list of definitions' well-formedness

Whether each definition of a list is well formed over the signature the definitions before it
extend ({name}`Geb.PartialHorn.DefnsWF`) is decided by a function: a definition is well formed
when its body has its sort in its context and each of its arguments occurs in the body, both
decidable. The statements about a definitional extension take the well-formedness as a
hypothesis; the decision gives it of a given list of definitions, such as those a program of the
internal language compiles to, by evaluation.

## Main definitions

* {lit}`Defn.wfb` — whether a definition is well formed over a signature.
* {lit}`defnsWFb` — whether each definition of a list is, over the signature the definitions
  before it extend.

## Main statements

* {lit}`Defn.wf_of_wfb`, {lit}`defnsWF_of_defnsWFb` — the definitions the decisions accept are
  well formed.

## Tags

definition, definitional extension, partial Horn logic, decision
-/

set_option doc.verso true

@[expose] public section

namespace Geb.PartialHorn

open scoped FinEnum

/-- Whether a definition is well formed over a signature: its body has its sort in its context,
and each of its arguments occurs in the body. -/
def Defn.wfb (S : Sig) (d : Defn) : Bool :=
  sortOf S d.ctx d.body == some d.sort && (List.range d.ctx.length).all fun i ↦ Occurs i d.body

/-- A definition the decision accepts is well formed. -/
theorem Defn.wf_of_wfb {S : Sig} {d : Defn} (h : d.wfb S = true) : d.WF S := by
  simp only [Defn.wfb, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  exact ⟨h.1, h.2⟩

/-- Whether each definition of a list is well formed over the signature that the definitions
before it extend. -/
def defnsWFb (ds : List Defn) : Sig → Bool :=
  ds.foldr (fun d k S ↦ d.wfb S && k (S.extend d)) fun _ ↦ true

/-- The definitions of a list the decision accepts are well formed, each over the signature the
definitions before it extend. -/
theorem defnsWF_of_defnsWFb :
    ∀ (ds : List Defn) (S : Sig), defnsWFb ds S = true → DefnsWF S ds :=
  List.rec (fun _ _ ↦ trivial) fun d ds ih S h ↦ by
    have h' : d.wfb S = true ∧ defnsWFb ds (S.extend d) = true := by
      simpa [defnsWFb] using h
    exact ⟨Defn.wf_of_wfb h'.1, ih (S.extend d) h'.2⟩

end Geb.PartialHorn

end
