/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Internal.Development

set_option doc.verso true in
/-!
# Composing developments by the validity of their statements

A development of theorems may be checked after the statements of theorems another development
proves, its derivations citing them by their positions among those statements, rather than after
the other development's derivations. Developments so checked compose by validity: the theorems of a
development are valid in every model in which the theorems it continues from are, so that a
collection of developments of which each continues from those before it, in no one order of them,
proves its theorems without a single list of all their declarations, and the check of each reads
none of the derivations of the others.

## Main definitions

* {lit}`Decl.isTheorem` — whether a declaration is one of a theorem of the language.
* {lit}`thmsOf` — the statements of a development's theorems.
* {lit}`checkAfter` — whether a development of theorems checks after given statements.

## Main statements

* {lit}`valid_of_checkAfter` — the theorems of a development are valid where the statements it
  continues from are.

## Tags

internal language, development, soundness
-/

set_option doc.verso true

@[expose] public section

namespace Geb.FreeTopos.Internal

open PartialHorn (Model IsModel)

universe v

/-- Whether a declaration is one of a theorem of the language. -/
def Decl.isTheorem : Decl → Bool
  | .language _ _ => true
  | _ => false

/-- The statements of a development's theorems. -/
def thmsOf (ds : List Decl) : List Thm :=
  ds.filterMap fun
    | .language a _ => some a
    | _ => none

/-- The environment of the given statements. -/
def entriesOf (before : List Thm) : Array Entry := (before.map Entry.language).toArray

/-- Whether a development of theorems checks after the given statements. -/
def checkAfter (G : Globals) (before : List Thm) (ds : List Decl) : Bool :=
  ds.all Decl.isTheorem && (checkDev G (entriesOf before) ds).isSome

/-- A development of theorems that checks keeps the constants, keeps the entries it begins with,
and has an entry of each of its statements. -/
theorem checkDev_theorems (G : Globals) (ds : List Decl) :
    ds.all Decl.isTheorem = true → ∀ {E : Array Entry} {G' : Globals} {Ef : Array Entry},
      checkDev G E ds = some (G', Ef) → G' = G ∧
        (∀ (j : ℕ) (e : Entry), E[j]? = some e → Ef[j]? = some e) ∧
        ∀ a ∈ thmsOf ds, ∃ j : ℕ, Ef[j]? = some (Entry.language a) :=
  ds.rec
    (motive := fun ds ↦ ds.all Decl.isTheorem = true → ∀ {E : Array Entry} {G' : Globals}
      {Ef : Array Entry}, checkDev G E ds = some (G', Ef) → G' = G ∧
        (∀ (j : ℕ) (e : Entry), E[j]? = some e → Ef[j]? = some e) ∧
        ∀ a ∈ thmsOf ds, ∃ j : ℕ, Ef[j]? = some (Entry.language a))
    (fun _ {E G' Ef} h ↦ by
      simp only [checkDev, List.foldlM_nil, Option.pure_def, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, fun _ _ hj ↦ hj, fun a ha ↦ (List.not_mem_nil ha).elim⟩)
    fun d ds ih hall {E G' Ef} h ↦ by
      simp only [List.all_cons, Bool.and_eq_true] at hall
      simp only [checkDev, List.foldlM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨⟨G₁, E₁⟩, hs, hr⟩ := h
      cases d with
      | language a d =>
        simp only [Decl.step] at hs
        split at hs
        · simp only [Option.some.injEq, Prod.mk.injEq] at hs
          obtain ⟨rfl, rfl⟩ := hs
          obtain ⟨rfl, hkeep, hthms⟩ := ih hall.2 hr
          refine ⟨rfl, fun j e hj ↦ hkeep j e ?_, fun b hb ↦ ?_⟩
          · rcases Nat.lt_or_ge j E.size with hlt | hge
            · rw [Array.getElem?_push_lt hlt, ← Array.getElem?_eq_getElem hlt]
              exact hj
            · rw [Array.getElem?_eq_none hge] at hj
              cases hj
          · simp only [thmsOf, List.filterMap_cons, List.mem_cons] at hb
            rcases hb with rfl | hb
            · refine ⟨E.size, hkeep _ _ ?_⟩
              rw [Array.getElem?_push_size]
            · exact hthms b hb
        · cases hs
      | _ => cases hall.1

/-- The entries of the given statements are valid where the statements are. -/
theorem entriesOf_valid {defs : List PartialHorn.Defn} {M : Model.{v} (ext defs).sig}
    {G : Globals} {before : List Thm} (hE : ∀ a ∈ before, a.Valid M G) :
    ∀ (j : ℕ) (e : Entry), (entriesOf before)[j]? = some e → e.Valid M G := fun j e hj ↦ by
  simp only [entriesOf, List.getElem?_toArray, List.getElem?_map, Option.map_eq_some_iff] at hj
  obtain ⟨a, ha, rfl⟩ := hj
  exact hE a (List.mem_of_getElem? ha)

/-- The theorems of a development that checks after given statements are valid in a model in which
those statements are, the constants being those of the invariant ({name}`DevInv`) that holds of
them with no entries. -/
theorem valid_of_checkAfter {pre F : List PartialHorn.Defn} {M : Model.{v} (ext (pre ++ F)).sig}
    (hM : IsModel (ext (pre ++ F)) M) {G : Globals} (hF : compileDefs G = some F)
    (hbase : G.base = sig.length + pre.length) (hinv : DevInv M G G #[]) {before : List Thm}
    {ds : List Decl} (hE : ∀ a ∈ before, a.Valid M G) (h : checkAfter G before ds = true) :
    ∀ a ∈ thmsOf ds, a.Valid M G := fun a ha ↦ by
  simp only [checkAfter, Bool.and_eq_true, Option.isSome_iff_exists] at h
  obtain ⟨hall, ⟨G', Ef⟩, hc⟩ := h
  obtain ⟨rfl, -, hthms⟩ := checkDev_theorems G ds hall hc
  have hinv' : DevInv M G' G' (entriesOf before) := { hinv with entries := entriesOf_valid hE }
  obtain ⟨j, hj⟩ := hthms a ha
  exact (devInv_checkDev hM hF hbase ds hc hinv').entries j _ hj

end Geb.FreeTopos.Internal

end
