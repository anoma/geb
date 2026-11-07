/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Prototypes.FreeTopos.Internal.Substitution

set_option doc.verso true in
/-!
# The types of terms

The type of a term in a context, computed without its arrow. The compilation
({name}`Geb.FreeTopos.Internal.compile`) computes a term's arrow and type together, and compiles a
fold's start and step over the product of the types of the fold's parameters, which it finds by
testing which variables of the context the start or the step mentions. A term's type depends on
the types of the variables it mentions alone
({name}`Geb.FreeTopos.Internal.compile_retype_on`), so a fold's start has its type in the
fold's context and its step in that context extended by the variables the step binds, as the
compilation of a fold's parts states ({name}`Geb.FreeTopos.Internal.compile_natRec_parts` and
its converse {name}`Geb.FreeTopos.Internal.compile_natRec_of_parts`, and their analogues at
lists and rose trees). The type computed so is the compilation's
({lit}`typeOf_eq_compile`).

## Main definitions

* {lit}`typeOf` — the type of a term in a context.
* {lit}`typeStepFast`, {lit}`typeOfFast` — the inference as compiled, from the children's types
  alone.

## Main statements

* {lit}`typeOf_eq_typeOfFast` — the inference is {lit}`typeOfFast`, which the compiler runs.
* {lit}`typeOf_eq_compile` — the type of a term in the types of an environment is the type the
  term compiles to in it.

## Tags

internal language, typed lambda calculus, type inference
-/

set_option doc.verso true

@[expose] public section

namespace Geb.FreeTopos.Internal

open PartialHorn (Tree)
open scoped FinEnum

variable (G : Globals) (n : ℕ)

/-- One step of the inference of types, at a node of a label, from its children's: the type of
the node's term in {lit}`n` object variables, in a context of types, with the constants of
{lit}`G`. An abstraction's body has its type in the context extended by the abstraction's
variable, a fold's start in the context and its step in the context extended by the variables it
binds. -/
def typeStep (l : Label) (cs : List (Term × (List Tree → Option Tree))) (Γ : List Tree) :
    Option Tree :=
  match l, cs with
    | .var i, [] => Γ[i]?
    | .star, [] => some one
    | .pair, [(_, t), (_, u)] => do
      let a ← t Γ
      let b ← u Γ
      pure (prod a b)
    | .fst, [(_, t)] => do
      let (a, _) ← prodParts (← t Γ)
      pure a
    | .snd, [(_, t)] => do
      let (_, b) ← prodParts (← t Γ)
      pure b
    | .lam a, [(_, t)] => if IsTy G n a then (t (a :: Γ)).map (exp a) else none
    | .app, [(_, t), (_, u)] => do
      let (a, b) ← expParts (← t Γ)
      if (← u Γ) = a then pure b else none
    | .arr k θ, [(_, t)] => do
      let p ← G.prims[k]?
      let d ← t Γ
      if θ.length = p.arity ∧ θ.all (IsTy G n) ∧ d = PartialHorn.subst θ p.dom then
        pure (PartialHorn.subst θ p.cod)
      else none
    | .natRec, [(_, z), (_, s), (_, m)] => do
      let c ← z Γ
      let c' ← s (c :: Γ)
      let t ← m Γ
      if c' = c ∧ t = nat then pure c else none
    | .listRec, [(_, z), (_, s), (_, m)] => do
      let a ← listPart (← m Γ)
      let c ← z Γ
      let c' ← s (c :: a :: Γ)
      if c' = c then pure c else none
    | .roseRec c, [(_, s), (_, m)] =>
      if IsTy G n c then do
        let (a, _) ← roseParts (← m Γ)
        let c' ← s (prod a (list c) :: Γ)
        if c' = c then pure c else none
      else none
    | .eq, [(_, t), (_, u)] => do
      let a ← t Γ
      let b ← u Γ
      if a = b then pure omega else none
    | .defn k θ, cs => do
      let d ← (G.defs[k]?).bind Definition.language?
      let ts ← cs.mapM fun c ↦ c.2 Γ
      if θ.length = d.arity ∧ θ.all (IsTy G n) ∧ ts = d.params.map (PartialHorn.subst θ) then
        pure (PartialHorn.subst θ d.type)
      else none
    | _, _ => none

/-- The type of a term in {lit}`n` object variables, in a context of types, with the constants of
{lit}`G`; nothing when the term is not well typed. -/
def typeOf : Term → List Tree → Option Tree :=
  RoseTree.para (typeStep G n)

/-- One step of the inference of types from the children's inferences alone, which are all
{lit}`typeStep` reads. -/
def typeStepFast (l : Label) (cs : List (List Tree → Option Tree)) (Γ : List Tree) :
    Option Tree :=
  match l, cs with
    | .var i, [] => Γ[i]?
    | .star, [] => some one
    | .pair, [t, u] => do
      let a ← t Γ
      let b ← u Γ
      pure (prod a b)
    | .fst, [t] => do
      let (a, _) ← prodParts (← t Γ)
      pure a
    | .snd, [t] => do
      let (_, b) ← prodParts (← t Γ)
      pure b
    | .lam a, [t] => if IsTy G n a then (t (a :: Γ)).map (exp a) else none
    | .app, [t, u] => do
      let (a, b) ← expParts (← t Γ)
      if (← u Γ) = a then pure b else none
    | .arr k θ, [t] => do
      let p ← G.prims[k]?
      let d ← t Γ
      if θ.length = p.arity ∧ θ.all (IsTy G n) ∧ d = PartialHorn.subst θ p.dom then
        pure (PartialHorn.subst θ p.cod)
      else none
    | .natRec, [z, s, m] => do
      let c ← z Γ
      let c' ← s (c :: Γ)
      let t ← m Γ
      if c' = c ∧ t = nat then pure c else none
    | .listRec, [z, s, m] => do
      let a ← listPart (← m Γ)
      let c ← z Γ
      let c' ← s (c :: a :: Γ)
      if c' = c then pure c else none
    | .roseRec c, [s, m] =>
      if IsTy G n c then do
        let (a, _) ← roseParts (← m Γ)
        let c' ← s (prod a (list c) :: Γ)
        if c' = c then pure c else none
      else none
    | .eq, [t, u] => do
      let a ← t Γ
      let b ← u Γ
      if a = b then pure omega else none
    | .defn k θ, cs => do
      let d ← (G.defs[k]?).bind Definition.language?
      let ts ← cs.mapM fun c ↦ c Γ
      if θ.length = d.arity ∧ θ.all (IsTy G n) ∧ ts = d.params.map (PartialHorn.subst θ) then
        pure (PartialHorn.subst θ d.type)
      else none
    | _, _ => none

/-- The inference of types as compiled: the fold of {lit}`typeStepFast`, which reads the children's
types alone and so does not rebuild the term at each node as {lit}`typeOf`'s paramorphism does. -/
def typeOfFast : Term → List Tree → Option Tree :=
  RoseTree.elim (typeStepFast G n)

variable {G n}

/-- The type of a node is its step at its children's types. -/
theorem typeOf_node (l : Label) (cs : List Term) (Γ : List Tree) :
    typeOf G n (RoseTree.node l cs) Γ = typeStep G n l (cs.map fun c ↦ (c, typeOf G n c)) Γ :=
  congrFun (RoseTree.para_node _ l cs) Γ

/-- The step of the inference from the children's inferences alone is {lit}`typeStep`. -/
theorem typeStepFast_map (l : Label) (cs : List (Term × (List Tree → Option Tree)))
    (Γ : List Tree) : typeStepFast G n l (cs.map Prod.snd) Γ = typeStep G n l cs Γ := by
  cases l
  case defn k θ => simp [typeStepFast, typeStep, List.mapM_map, Function.comp_def]
  all_goals rcases cs with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, cs⟩⟩⟩⟩ <;> rfl

/-- The inference of types is {lit}`typeOfFast`, by which the compiler replaces it. -/
@[csimp] theorem typeOf_eq_typeOfFast : @typeOf = @typeOfFast := by
  funext G n t
  refine RoseTree.ind (P := fun t ↦ typeOf G n t = typeOfFast G n t)
    (fun l cs ih ↦ funext fun Γ ↦ ?_) t
  rw [typeOf_node, typeOfFast, RoseTree.elim_node, ← typeOfFast, ← typeStepFast_map, List.map_map]
  exact congrArg (typeStepFast G n l · Γ) (List.map_congr_left fun c hc ↦ ih c hc)

/-- The types of an environment extended by a variable are the variable's type before the
environment's types. -/
theorem map_snd_extEnv (X a : Tree) (e : List (Tree × Tree)) :
    (extEnv X a e).map Prod.snd = a :: e.map Prod.snd := by
  simp [extEnv]

/-- A type is the second component of a result when the result determines it and it determines a
result of that second component. -/
theorem eq_map_snd_of {o : Option Tree} {p : Option (Tree × Tree)}
    (h₁ : ∀ r, p = some r → o = some r.2) (h₂ : ∀ a, o = some a → ∃ f, p = some (f, a)) :
    o = p.map Prod.snd := by
  rcases p with _ | r
  · rcases o with _ | a
    · rfl
    · obtain ⟨f, hf⟩ := h₂ a rfl
      simp at hf
  · rw [h₁ r rfl, Option.map_some]

/-- The results of a partial function followed by a function, over a list, are the function's
images of the partial function's results. -/
theorem mapM_map_option {α β γ : Type} (g : α → Option β) (h : β → γ) (l : List α) :
    l.mapM (fun a ↦ (g a).map h) = (l.mapM g).map (List.map h) :=
  l.rec (by simp) fun a l ih ↦ by
    rcases hg : g a with _ | b
    · simp [List.mapM_cons, hg]
    · rcases hl : l.mapM g with _ | bs <;> simp_all [List.mapM_cons]

/-- The results of two partial functions over a list are equal when the functions agree at its
elements. -/
theorem mapM_congr_mem {α β : Type} {f g : α → Option β} (l : List α)
    (h : ∀ a ∈ l, f a = g a) : l.mapM f = l.mapM g :=
  l.rec (motive := fun l ↦ (∀ a ∈ l, f a = g a) → l.mapM f = l.mapM g) (fun _ ↦ rfl)
    (fun a l ih h ↦ by
      simp only [List.mapM_cons, h a List.mem_cons_self,
        ih fun b hb ↦ h b (List.mem_cons_of_mem a hb)]) h

/-- A term compiles to the type it has in the types of an environment, where its type is the
type it compiles to. -/
theorem compile_of_typeOf {t : Term} {X c : Tree} {e : List (Tree × Tree)}
    (h : typeOf G n t (e.map Prod.snd) = (compile G n t X e).map Prod.snd)
    (ht : typeOf G n t (e.map Prod.snd) = some c) : ∃ f, compile G n t X e = some (f, c) := by
  rw [h] at ht
  obtain ⟨⟨f, c'⟩, hf, rfl⟩ := Option.map_eq_some_iff.mp ht
  exact ⟨f, hf⟩

/-- The type of a term in the types of an environment is the type it compiles to in that
environment, over any object. -/
theorem typeOf_eq_compile (s : Term) :
    ∀ (X : Tree) (e : List (Tree × Tree)),
      typeOf G n s (e.map Prod.snd) = (compile G n s X e).map Prod.snd := by
  refine RoseTree.ind (P := fun s ↦ ∀ (X : Tree) (e : List (Tree × Tree)),
    typeOf G n s (e.map Prod.snd) = (compile G n s X e).map Prod.snd) (fun l cs ih ↦ ?_) s
  intro X e
  cases l with
  | natRec =>
    rcases cs with _ | ⟨z, _ | ⟨s, _ | ⟨m, _ | ⟨v, cs⟩⟩⟩⟩ <;>
      try (simp [typeOf_node, compile_node, typeStep, compileStep]; done)
    have hz := ih z (by simp)
    have hs := ih s (by simp)
    have hm := ih m (by simp)
    refine eq_map_snd_of (fun r h ↦ ?_) (fun A h ↦ ?_)
    · obtain ⟨⟨zf, hzf⟩, ⟨sf, hsf⟩, ⟨mf, hmf⟩⟩ := compile_natRec_parts h
      have hs' := hs (prod X r.2) (extEnv X r.2 e)
      rw [map_snd_extEnv, hsf] at hs'
      rw [typeOf_node]
      simp [typeStep, hz X e, hzf, hs', hm X e, hmf]
    · rw [typeOf_node] at h
      simp only [List.map_cons, List.map_nil, typeStep, Option.bind_eq_bind,
        Option.bind_eq_some_iff] at h
      obtain ⟨c, hc, c', hc', t, ht, h⟩ := h
      split_ifs at h with hct
      obtain ⟨hcc, htn⟩ := hct
      have hA : c = A := Option.some.inj h
      subst hA
      rw [hcc] at hc'
      rw [htn] at ht
      obtain ⟨zf, hzf⟩ := compile_of_typeOf (hz X e) hc
      obtain ⟨sf, hsf⟩ := compile_of_typeOf (hs (prod X c) (extEnv X c e))
        (by rw [map_snd_extEnv]; exact hc')
      obtain ⟨mf, hmf⟩ := compile_of_typeOf (hm X e) ht
      obtain ⟨⟨f, c₀⟩, hr, rfl⟩ := compile_natRec_of_parts hzf hsf hmf
      exact ⟨f, hr⟩
  | listRec =>
    rcases cs with _ | ⟨z, _ | ⟨s, _ | ⟨m, _ | ⟨v, cs⟩⟩⟩⟩ <;>
      try (simp [typeOf_node, compile_node, typeStep, compileStep]; done)
    have hz := ih z (by simp)
    have hs := ih s (by simp)
    have hm := ih m (by simp)
    refine eq_map_snd_of (fun r h ↦ ?_) (fun A h ↦ ?_)
    · obtain ⟨mf, a, hmf, ⟨zf, hzf⟩, ⟨sf, hsf⟩⟩ := compile_listRec_parts h
      have hs' := hs (prod (prod X a) r.2) (extEnv (prod X a) r.2 (extEnv X a e))
      rw [map_snd_extEnv, map_snd_extEnv, hsf] at hs'
      rw [typeOf_node]
      simp [typeStep, hz X e, hzf, hs', hm X e, hmf,
        (listPart_eq_some (p := list a) (a := a)).mpr rfl]
    · rw [typeOf_node] at h
      simp only [List.map_cons, List.map_nil, typeStep, Option.bind_eq_bind,
        Option.bind_eq_some_iff] at h
      obtain ⟨t, ht, a, ha, c, hc, c', hc', h⟩ := h
      split_ifs at h with hcc
      subst hcc
      obtain rfl := Option.some.inj h
      obtain rfl := listPart_eq_some.mp ha
      obtain ⟨zf, hzf⟩ := compile_of_typeOf (hz X e) hc
      obtain ⟨sf, hsf⟩ := compile_of_typeOf (hs (prod (prod X a) c') (extEnv (prod X a) c'
        (extEnv X a e))) (by rw [map_snd_extEnv, map_snd_extEnv]; exact hc')
      obtain ⟨mf, hmf⟩ := compile_of_typeOf (hm X e) ht
      obtain ⟨⟨f, c₀⟩, hr, rfl⟩ := compile_listRec_of_parts hmf hzf hsf
      exact ⟨f, hr⟩
  | roseRec c =>
    rcases cs with _ | ⟨s, _ | ⟨m, _ | ⟨v, cs⟩⟩⟩ <;>
      try (simp [typeOf_node, compile_node, typeStep, compileStep]; done)
    have hs := ih s (by simp)
    have hm := ih m (by simp)
    refine eq_map_snd_of (fun r h ↦ ?_) (fun A h ↦ ?_)
    · obtain ⟨hct, hr, mf, t, a, F, hmf, ht, sf, hsf⟩ := compile_roseRec_parts h
      have hs' := hs (prod X (prod a (list c))) (extEnv X (prod a (list c)) e)
      rw [map_snd_extEnv, hsf] at hs'
      rw [typeOf_node, hr]
      simp [typeStep, hct, hs', hm X e, hmf, ht]
    · rw [typeOf_node] at h
      simp only [List.map_cons, List.map_nil, typeStep] at h
      split_ifs at h with hct
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨t, ht, ⟨a, F⟩, haF, c', hc', h⟩ := h
      split_ifs at h with hcc
      subst hcc
      obtain rfl := Option.some.inj h
      obtain ⟨sf, hsf⟩ := compile_of_typeOf (hs (prod X (prod a (list c')))
        (extEnv X (prod a (list c')) e)) (by rw [map_snd_extEnv]; exact hc')
      obtain ⟨mf, hmf⟩ := compile_of_typeOf (hm X e) ht
      obtain ⟨⟨f, c₀⟩, hr, rfl⟩ := compile_roseRec_of_parts hct hmf haF hsf
      exact ⟨f, hr⟩
  | defn k θ =>
    rw [typeOf_node, compile_node]
    simp only [typeStep, compileStep, List.mapM_map, Function.comp_def]
    rw [mapM_congr_mem cs fun c hc ↦ ih c hc X e, mapM_map_option]
    rcases (G.defs[k]?).bind Definition.language? with _ | d
    · rfl
    simp only [List.all_eq_true, Option.pure_def, Option.bind_eq_bind, Option.bind_some,
      Option.map_bind, Function.comp_apply, Option.map_if]
    rcases cs.mapM (fun c ↦ compile G n c X e) with _ | rs <;> simp
  | lam a =>
    rw [typeOf_node, compile_node]
    rcases cs with _ | ⟨t, _ | ⟨u, cs⟩⟩ <;>
      simp only [List.map_cons, List.map_nil, typeStep, compileStep, Option.map_none]
    split
    · rw [← map_snd_extEnv X a e, ih t (by simp) (prod X a) (extEnv X a e)]
      rcases compile G n t (prod X a) (extEnv X a e) with _ | ⟨f, b⟩ <;> simp
    · rfl
  | var i =>
    rcases cs with _ | ⟨t, cs⟩ <;>
      simp [typeOf_node, compile_node, typeStep, compileStep, List.getElem?_map]
  | star => rcases cs with _ | ⟨t, cs⟩ <;> simp [typeOf_node, compile_node, typeStep, compileStep]
  | pair | app | eq =>
    rw [typeOf_node, compile_node]
    rcases cs with _ | ⟨t, _ | ⟨u, _ | ⟨v, cs⟩⟩⟩ <;>
      simp only [List.map_cons, List.map_nil, typeStep, compileStep, Option.map_none]
    rw [ih t (by simp) X e, ih u (by simp) X e]
    rcases compile G n t X e with _ | ⟨f, a⟩ <;> rcases compile G n u X e with _ | ⟨g, b⟩ <;>
      simp
  | fst | snd =>
    rw [typeOf_node, compile_node]
    rcases cs with _ | ⟨t, _ | ⟨u, cs⟩⟩ <;>
      simp only [List.map_cons, List.map_nil, typeStep, compileStep, Option.map_none]
    rw [ih t (by simp) X e]
    rcases compile G n t X e with _ | ⟨f, a⟩ <;> simp
  | arr k θ =>
    rw [typeOf_node, compile_node]
    rcases cs with _ | ⟨t, _ | ⟨u, cs⟩⟩ <;>
      simp only [List.map_cons, List.map_nil, typeStep, compileStep, Option.map_none]
    rw [ih t (by simp) X e]
    rcases G.prims[k]? with _ | p <;> rcases compile G n t X e with _ | ⟨f, a⟩ <;> simp

end Geb.FreeTopos.Internal

end
