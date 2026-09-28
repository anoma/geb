/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Kernel.Basic

set_option doc.verso true in
/-!
# Substitution in kernel terms

Weakening and substitution of the kernel's terms, which are rose trees with de Bruijn
variables, and their agreement with the denotation {lit}`infer`: a weakened term denotes its
denotation composed with the projection that forgets the added variables, and a term with a
term substituted for its innermost variable denotes its denotation at the value of the
substituted term.

Both are instances of one traversal, which rebuilds a term and replaces each variable by a
term computed from its index and the number of binders around it. One lemma relates the
traversal to the denotation, given the corresponding relation for variables, and each
instance supplies that relation.

## Main definitions

* {lit}`Tm.var` — the variable of an index.
* {lit}`Ctx.ext`, {lit}`Ctx.drop` — maps of contexts' denotations.
* {lit}`trav` — the traversal replacing variables.
* {lit}`wk`, {lit}`subst` — weakening, and substitution for the innermost variable.

## Main statements

* {lit}`infer_trav` — the traversal agrees with the denotation.
* {lit}`infer_wk`, {lit}`infer_subst` — weakening and substitution agree with it.

## Implementation notes

The traversal descends only into the children of a node that are terms: the body of an
abstraction, at one more binder, and every child of an application, a pair, a projection, a
conditional and a list's head and tail. Type annotations, quoted trees and the indices of
primitives and references are kept, so that a quoted tree is never read as a term.

## Tags

bootstrap, kernel, de Bruijn index, substitution, weakening, denotational semantics
-/

set_option doc.verso true

@[expose] public section

namespace Geb.Kernel

open scoped FinEnum

/-- The variable of a de Bruijn index. -/
def Tm.var (i : ℕ) : Tree := RoseTree.node Label.var [leaf i]

namespace Ctx

/-- A map of the denotations of contexts, extended by a prefix whose values it keeps. -/
def ext {Γ Δ : Ctx} (ρ : Δ.den → Γ.den) : (Θ : Ctx) → (Θ ++ Δ).den → (Θ ++ Γ).den :=
  List.rec ρ fun _ _ ih e ↦ (e.1, ih e.2)

/-- The values of a context below a prefix. -/
def drop {Γ : Ctx} : (W : Ctx) → (W ++ Γ).den → Γ.den :=
  List.rec id fun _ _ ih e ↦ ih e.2

end Ctx

/-- The traversal of a term replacing each variable: the variable of index {lit}`i` under
{lit}`k` binders becomes {lit}`v k i`, and every other node is rebuilt. -/
def trav (v : ℕ → ℕ → Tree) : Tree → ℕ → Tree :=
  RoseTree.para fun l rs k ↦
    match l, rs with
    | Label.var, [(n, _)] => v k n.label
    | Label.lam, [(A, _), (_, b)] => RoseTree.node Label.lam [A, b (k + 1)]
    | Label.app, _ | Label.unit, _ | Label.pair, _ | Label.fst, _ | Label.snd, _ | Label.cond, _
    | Label.cons, _ =>
      RoseTree.node l (rs.map fun r ↦ r.2 k)
    | _, _ => RoseTree.node l (rs.map Prod.fst)

/-- The denotation of a node: the checker-evaluator's step at the node's children. -/
theorem infer_node (G : List Glob) (Γ : Ctx) (l : ℕ) (cs : List Tree) :
    infer G Γ (RoseTree.node l cs) =
      inferStep l (cs.map fun c ↦ (c, RoseTree.para inferStep c)) G Γ := by
  simp only [infer, RoseTree.para_node]

/-- The traversal of a node all of whose children are terms traverses each child. -/
theorem trav_node_term (v : ℕ → ℕ → Tree) (k : ℕ) {l : ℕ} (hl : l ∈ [10, 11, 12, 13, 14, 16, 20])
    (cs : List Tree) :
    trav v (RoseTree.node l cs) k = RoseTree.node l (cs.map fun c ↦ trav v c k) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [trav, RoseTree.para_node, Function.comp_def]

/-- The children of a node, paired with their denotations, when they are one child. -/
theorem map_para_eq_one {cs : List Tree} {x : Tree} {s : Sem}
    (h : cs.map (fun c ↦ (c, RoseTree.para inferStep c)) = [(x, s)]) :
    cs = [x] ∧ s = RoseTree.para inferStep x := by
  obtain ⟨c, _, rfl, hc, hnil⟩ := List.map_eq_cons_iff.mp h
  obtain rfl := List.map_eq_nil_iff.mp hnil
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hc
  exact ⟨rfl, rfl⟩

/-- The children of a node, paired with their denotations, when they are two children. -/
theorem map_para_eq_two {cs : List Tree} {x y : Tree} {s t : Sem}
    (h : cs.map (fun c ↦ (c, RoseTree.para inferStep c)) = [(x, s), (y, t)]) :
    cs = [x, y] ∧ s = RoseTree.para inferStep x ∧ t = RoseTree.para inferStep y := by
  obtain ⟨c, _, rfl, hc, h'⟩ := List.map_eq_cons_iff.mp h
  obtain ⟨rfl, rfl⟩ := map_para_eq_one h'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hc
  exact ⟨rfl, rfl, rfl⟩

/-- The children of a node, paired with their denotations, when they are three children. -/
theorem map_para_eq_three {cs : List Tree} {x y z : Tree} {s t u : Sem}
    (h : cs.map (fun c ↦ (c, RoseTree.para inferStep c)) = [(x, s), (y, t), (z, u)]) :
    cs = [x, y, z] ∧ s = RoseTree.para inferStep x ∧ t = RoseTree.para inferStep y ∧
      u = RoseTree.para inferStep z := by
  obtain ⟨c, _, rfl, hc, h'⟩ := List.map_eq_cons_iff.mp h
  obtain ⟨rfl, rfl, rfl⟩ := map_para_eq_two h'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hc
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The traversal agrees with the denotation, given that each variable's replacement does. -/
theorem infer_trav {G : List Glob} {Γ Δ : Ctx} (ρ : Δ.den → Γ.den) (v : ℕ → ℕ → Tree)
    (hv : ∀ (Θ : Ctx) (i : ℕ) (A : Tree) (f : (Θ ++ Γ).den → Ty.den A),
      Ctx.var (Θ ++ Γ) i = some ⟨A, f⟩ →
        infer G (Θ ++ Δ) (v Θ.length i) = some ⟨A, f ∘ Ctx.ext ρ Θ⟩) :
    ∀ (t : Tree) (Θ : Ctx) (m : Meaning (Θ ++ Γ)), infer G (Θ ++ Γ) t = some m →
      infer G (Θ ++ Δ) (trav v t Θ.length) = some ⟨m.1, m.2 ∘ Ctx.ext ρ Θ⟩ := by
  refine RoseTree.ind fun l cs ih Θ m h ↦ ?_
  rw [infer_node] at h
  unfold inferStep at h
  split at h
  case h_1 n s heq =>
    obtain ⟨rfl, rfl⟩ := map_para_eq_one heq
    obtain ⟨A, f⟩ := m
    simp only [trav, RoseTree.para_node, List.map_cons, List.map_nil]
    exact hv Θ n.label A f h
  case h_2 c sA c' b heq =>
    obtain ⟨rfl, rfl, rfl⟩ := map_para_eq_two heq
    split at h
    · rename_i hA
      obtain ⟨mb, hb, rfl⟩ := Option.map_eq_some_iff.mp h
      have hb' := ih c' (by simp) (c :: Θ) mb hb
      simp only [trav, RoseTree.para_node, List.map]
      rw [infer_node]
      simp only [inferStep, List.map, hA, ↓reduceIte]
      change Option.map _ (infer G ((c :: Θ) ++ Δ) (trav v c' (c :: Θ).length)) = _
      rw [hb']
      rfl
    · cases h
  case h_4 heq =>
    obtain rfl := List.map_eq_nil_iff.mp heq
    cases h
    simp only [trav, RoseTree.para_node, List.map_nil, infer_node, inferStep]
    rfl
  case h_8 t st heq =>
    obtain ⟨rfl, rfl⟩ := map_para_eq_one heq
    cases h
    simp only [trav, RoseTree.para_node, List.map_cons, List.map_nil, infer_node, inferStep]
    rfl
  case h_10 A sA heq =>
    obtain ⟨rfl, rfl⟩ := map_para_eq_one heq
    split at h
    · rename_i hA
      cases h
      simp only [trav, RoseTree.para_node, List.map_cons, List.map_nil, infer_node, inferStep, hA,
        ↓reduceIte]
      rfl
    · cases h
  case h_11 A sA heq =>
    obtain ⟨rfl, rfl⟩ := map_para_eq_one heq
    split at h
    · rename_i hA
      cases h
      simp only [trav, RoseTree.para_node, List.map_cons, List.map_nil, infer_node, inferStep, hA,
        ↓reduceIte]
      rfl
    · cases h
  case h_12 A sA heq =>
    obtain ⟨rfl, rfl⟩ := map_para_eq_one heq
    split at h
    · rename_i hA
      cases h
      simp only [trav, RoseTree.para_node, List.map_cons, List.map_nil, infer_node, inferStep, hA,
        ↓reduceIte]
      rfl
    · cases h
  case h_14 A sA B sB heq =>
    obtain ⟨rfl, rfl, rfl⟩ := map_para_eq_two heq
    split at h
    · rename_i hAB
      cases h
      simp only [trav, RoseTree.para_node, List.map_cons, List.map_nil, infer_node, inferStep, hAB,
        ↓reduceIte]
      rfl
    · cases h
  case h_17 A sA B sB heq =>
    obtain ⟨rfl, rfl, rfl⟩ := map_para_eq_two heq
    split at h
    · rename_i hAB
      cases h
      simp only [trav, RoseTree.para_node, List.map_cons, List.map_nil, infer_node, inferStep, hAB,
        ↓reduceIte]
      rfl
    · cases h
  case h_15 k sk heq =>
    obtain ⟨rfl, rfl⟩ := map_para_eq_one heq
    obtain ⟨g, hg, rfl⟩ := Option.map_eq_some_iff.mp h
    simp only [trav, RoseTree.para_node, List.map_cons, List.map_nil, infer_node, inferStep, hg,
      Option.map_some]
    rfl
  case h_16 k sk heq =>
    obtain ⟨rfl, rfl⟩ := map_para_eq_one heq
    obtain ⟨g, hg, rfl⟩ := Option.map_eq_some_iff.mp h
    simp only [trav, RoseTree.para_node, List.map_cons, List.map_nil, infer_node, inferStep, hg,
      Option.map_some]
    rfl
  case h_18 => cases h
  case h_3 cf f cx x heq =>
    obtain ⟨rfl, rfl, rfl⟩ := map_para_eq_two heq
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨mf, hf, mx, hx, ⟨A, B, hAB⟩, harr, h⟩ := h
    have hf' := ih cf (by simp) Θ mf hf
    have hx' := ih cx (by simp) Θ mx hx
    simp only [infer] at hf' hx'
    rw [trav_node_term v _ (by simp), infer_node]
    simp only [List.map_cons, List.map_nil, inferStep, Option.bind_eq_bind, hf', hx',
      Option.bind_some, harr]
    split at h
    · rename_i hA
      cases h
      split
      · rfl
      · contradiction
    · cases h
  case h_5 ca a cb b heq =>
    obtain ⟨rfl, rfl, rfl⟩ := map_para_eq_two heq
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨ma, ha, mb, hb, h⟩ := h
    have ha' := ih ca (by simp) Θ ma ha
    have hb' := ih cb (by simp) Θ mb hb
    simp only [infer] at ha' hb'
    rw [trav_node_term v _ (by simp), infer_node]
    simp only [List.map_cons, List.map_nil, inferStep, Option.bind_eq_bind, ha', hb',
      Option.bind_some]
    cases h
    rfl
  case h_6 cp p heq =>
    obtain ⟨rfl, rfl⟩ := map_para_eq_one heq
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨mp, hp, ⟨A, B, hAB⟩, hprod, h⟩ := h
    have hp' := ih cp (by simp) Θ mp hp
    simp only [infer] at hp'
    rw [trav_node_term v _ (by simp), infer_node]
    simp only [List.map_cons, List.map_nil, inferStep, Option.bind_eq_bind, hp', Option.bind_some,
      hprod]
    cases h
    rfl
  case h_7 cp p heq =>
    obtain ⟨rfl, rfl⟩ := map_para_eq_one heq
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨mp, hp, ⟨A, B, hAB⟩, hprod, h⟩ := h
    have hp' := ih cp (by simp) Θ mp hp
    simp only [infer] at hp'
    rw [trav_node_term v _ (by simp), infer_node]
    simp only [List.map_cons, List.map_nil, inferStep, Option.bind_eq_bind, hp', Option.bind_some,
      hprod]
    cases h
    rfl
  case h_9 cc c ca a cb b heq =>
    obtain ⟨rfl, rfl, rfl, rfl⟩ := map_para_eq_three heq
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨mc, hc, ma, ha, mb, hb, h⟩ := h
    have hc' := ih cc (by simp) Θ mc hc
    have ha' := ih ca (by simp) Θ ma ha
    have hb' := ih cb (by simp) Θ mb hb
    simp only [infer] at hc' ha' hb'
    rw [trav_node_term v _ (by simp), infer_node]
    simp only [List.map_cons, List.map_nil, inferStep, Option.bind_eq_bind, hc', ha', hb',
      Option.bind_some]
    split at h
    · rename_i hT
      split at h
      · rename_i hB
        cases h
        split
        · rfl
        · contradiction
      · cases h
    · cases h
  case h_13 cx x cxs xs heq =>
    obtain ⟨rfl, rfl, rfl⟩ := map_para_eq_two heq
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨mx, hx, mxs, hxs, ⟨A, hA⟩, hlist, h⟩ := h
    have hx' := ih cx (by simp) Θ mx hx
    have hxs' := ih cxs (by simp) Θ mxs hxs
    simp only [infer] at hx' hxs'
    rw [trav_node_term v _ (by simp), infer_node]
    simp only [List.map_cons, List.map_nil, inferStep, Option.bind_eq_bind, hx', hxs',
      Option.bind_some, hlist]
    split at h
    · rename_i hE
      cases h
      split
      · rfl
      · contradiction
    · cases h

namespace Ctx

/-- The innermost variable of a context. -/
@[simp] theorem var_cons_zero (A : Tree) (Γ : Ctx) :
    var (A :: Γ) 0 = some ⟨A, Prod.fst⟩ := rfl

/-- A variable below the innermost one. -/
@[simp] theorem var_cons_succ (A : Tree) (Γ : Ctx) (i : ℕ) :
    var (A :: Γ) (i + 1) = (var Γ i).map fun p ↦ ⟨p.1, p.2 ∘ Prod.snd⟩ := rfl

/-- A variable of a context below a prefix, counted past the prefix. -/
theorem var_append_add (W Γ : Ctx) (i : ℕ) :
    var (W ++ Γ) (i + W.length) = (var Γ i).map fun p ↦ ⟨p.1, p.2 ∘ drop W⟩ :=
  List.rec (motive := fun W ↦
      var (W ++ Γ) (i + W.length) = (var Γ i).map fun p ↦ ⟨p.1, p.2 ∘ drop W⟩)
    (by simp [drop])
    (fun B W ih ↦ by
      change var (B :: (W ++ Γ)) (i + W.length + 1) = _
      rw [var_cons_succ, ih, Option.map_map]
      rfl)
    W

/-- A variable of a context with a context inserted below a prefix. -/
theorem var_insert (W Γ : Ctx) :
    ∀ (Θ : Ctx) (i : ℕ) (A : Tree) (f : (Θ ++ Γ).den → Ty.den A),
      var (Θ ++ Γ) i = some ⟨A, f⟩ →
        var (Θ ++ (W ++ Γ)) (if i < Θ.length then i else i + W.length) =
          some ⟨A, f ∘ ext (drop W) Θ⟩ :=
  List.rec
    (fun i A f h ↦ by
      change var Γ i = some ⟨A, f⟩ at h
      change var (W ++ Γ) (i + W.length) = _
      rw [var_append_add, h, Option.map_some]
      rfl)
    (fun B Θ ih i A f h ↦ by
      rcases i with _ | i
      · simp only [List.cons_append, var_cons_zero, Option.some.injEq] at h
        obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.mp h
        obtain rfl := eq_of_heq h
        simp only [List.cons_append, List.length_cons, Nat.zero_lt_succ, ↓reduceIte,
          var_cons_zero]
        rfl
      · simp only [List.cons_append, var_cons_succ, Option.map_eq_some_iff] at h
        obtain ⟨⟨A', g⟩, hg, h⟩ := h
        obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.mp h
        obtain rfl := eq_of_heq h
        have := ih i A' g hg
        simp only [List.cons_append, List.length_cons, Nat.add_lt_add_iff_right]
        split
        · rename_i hi
          simp only [hi, ↓reduceIte] at this
          simp only [var_cons_succ, this, Option.map_some]
          rfl
        · rename_i hi
          simp only [hi, ↓reduceIte] at this
          rw [Nat.add_right_comm, var_cons_succ, this, Option.map_some]
          rfl)

end Ctx

/-- The denotation of a variable is its lookup in the context. -/
@[simp] theorem infer_var (G : List Glob) (Γ : Ctx) (i : ℕ) :
    infer G Γ (Tm.var i) = Γ.var i := by
  simp [Tm.var, infer_node, inferStep, leaf]

/-- The replacement of a variable when weakening by {lit}`n` variables, below {lit}`k`
binders. -/
def wkVar (n k i : ℕ) : Tree := Tm.var (if i < k then i else i + n)

/-- A term with {lit}`n` variables inserted below its free variables. -/
def wk (n : ℕ) (t : Tree) : Tree := trav (wkVar n) t 0

/-- A weakened term denotes its denotation at the values below the inserted variables. -/
theorem infer_wk {G : List Glob} {Γ : Ctx} (W : Ctx) {t : Tree} {m : Meaning Γ}
    (h : infer G Γ t = some m) :
    infer G (W ++ Γ) (wk W.length t) = some ⟨m.1, m.2 ∘ Ctx.drop W⟩ :=
  infer_trav (Γ := Γ) (Δ := W ++ Γ) (Ctx.drop W) (wkVar W.length)
    (fun Θ i A f hf ↦ by rw [wkVar, infer_var]; exact Ctx.var_insert W Γ Θ i A f hf) t [] m h

/-- The replacement of a variable when substituting {lit}`u` for the innermost free variable,
below {lit}`k` binders. -/
def substVar (u : Tree) (k i : ℕ) : Tree :=
  if i < k then Tm.var i else if i = k then wk k u else Tm.var (i - 1)

/-- A term with {lit}`u` substituted for its innermost free variable. -/
def subst (u t : Tree) : Tree := trav (substVar u) t 0

/-- The replacement of each variable in substitution denotes the variable's value at the
extended context. -/
theorem infer_substVar {G : List Glob} {Γ : Ctx} {A u : Tree} {fu : Γ.den → Ty.den A}
    (hu : infer G Γ u = some ⟨A, fu⟩) :
    ∀ (Θ : Ctx) (i : ℕ) (B : Tree) (f : (Θ ++ A :: Γ).den → Ty.den B),
      Ctx.var (Θ ++ A :: Γ) i = some ⟨B, f⟩ →
        infer G (Θ ++ Γ) (substVar u Θ.length i) =
          some ⟨B, f ∘ Ctx.ext (Γ := A :: Γ) (fun e ↦ (fu e, e)) Θ⟩ :=
  List.rec
    (fun i B f h ↦ by
      change Ctx.var (A :: Γ) i = some ⟨B, f⟩ at h
      rcases i with _ | i
      · simp only [Ctx.var_cons_zero, Option.some.injEq] at h
        obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.mp h
        obtain rfl := eq_of_heq h
        simp only [substVar, List.length_nil, Nat.lt_irrefl, ↓reduceIte]
        exact infer_wk [] hu
      · simp only [Ctx.var_cons_succ, Option.map_eq_some_iff] at h
        obtain ⟨⟨B', g⟩, hg, h⟩ := h
        obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.mp h
        obtain rfl := eq_of_heq h
        simp only [substVar, List.length_nil, Nat.not_lt_zero, ↓reduceIte, Nat.add_one_ne_zero,
          Nat.add_sub_cancel, infer_var]
        exact hg)
    (fun C Θ ih i B f h ↦ by
      rcases i with _ | i
      · change Ctx.var (C :: (Θ ++ A :: Γ)) 0 = some ⟨B, f⟩ at h
        simp only [Ctx.var_cons_zero, Option.some.injEq] at h
        obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.mp h
        obtain rfl := eq_of_heq h
        simp only [substVar, List.length_cons, Nat.zero_lt_succ, ↓reduceIte, infer_var]
        rfl
      · change Ctx.var (C :: (Θ ++ A :: Γ)) (i + 1) = some ⟨B, f⟩ at h
        simp only [Ctx.var_cons_succ, Option.map_eq_some_iff] at h
        obtain ⟨⟨B', g⟩, hg, h⟩ := h
        obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.mp h
        obtain rfl := eq_of_heq h
        have hi := ih i B' g hg
        simp only [substVar, List.length_cons, Nat.add_lt_add_iff_right, Nat.add_right_cancel_iff]
        simp only [substVar] at hi
        split
        · rename_i hlt
          simp only [hlt, ↓reduceIte, infer_var] at hi
          change Ctx.var (C :: (Θ ++ Γ)) (i + 1) = _
          rw [Ctx.var_cons_succ, hi, Option.map_some]
          rfl
        · rename_i hlt
          split
          · rename_i heq
            subst heq
            simp only [Nat.lt_irrefl, ↓reduceIte] at hi
            rw [infer_wk Θ hu] at hi
            have hw := infer_wk (C :: Θ) hu
            simp only [Option.some.injEq] at hi
            obtain ⟨rfl, hfg⟩ := Sigma.mk.inj_iff.mp hi
            refine hw.trans (congrArg some (Sigma.ext rfl (heq_of_eq ?_)))
            funext e
            exact congrFun (eq_of_heq hfg) e.2
          · rename_i hne
            have hk : Θ.length < i := by omega
            simp only [hlt, hne, ↓reduceIte, infer_var] at hi
            obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
            simp only [Nat.add_sub_cancel] at hi ⊢
            change Ctx.var (C :: (Θ ++ Γ)) (j + 1) = _
            rw [Ctx.var_cons_succ, hi, Option.map_some]
            rfl)

/-- A term with a term substituted for its innermost free variable denotes its denotation at
the substituted term's value. -/
theorem infer_subst {G : List Glob} {Γ : Ctx} {A u t : Tree} {fu : Γ.den → Ty.den A}
    {m : Meaning (A :: Γ)} (hu : infer G Γ u = some ⟨A, fu⟩) (ht : infer G (A :: Γ) t = some m) :
    infer G Γ (subst u t) = some ⟨m.1, fun e ↦ m.2 (fu e, e)⟩ :=
  infer_trav (Γ := A :: Γ) (Δ := Γ) (fun e ↦ (fu e, e)) (substVar u) (infer_substVar hu) t [] m ht

end Geb.Kernel

end
