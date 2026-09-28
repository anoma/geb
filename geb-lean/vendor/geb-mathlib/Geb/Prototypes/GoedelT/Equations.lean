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
# Gödel's T over rose trees

A variant of Gödel's T \[Goedel1958\], the quantifier-free theory of the primitive recursive
functionals of finite type, whose atomic formulas are equations between terms of one type and
which has a rule of induction (\[AvigadFeferman1998\], Section 2.2). The functionals here are
the kernel's terms, of the unit, product, function, list and tree types, the rose trees with
natural-number labels standing in place of the natural numbers; a formula is a sequent, an
equation derived from equational hypotheses; and the rules are the laws of a cartesian closed
category with list objects and a rose-tree object, the η rules among them. Its checker was the
bootstrap's first, which the metalogic's retires, the kernel's programs translating soundly into
the internal language of the free topos.

A sequent is a context, a list of hypotheses and a conclusion, each an equation between two terms
of a type in that context; it is valid when, at every value of the context at which the
hypotheses hold, both sides of the conclusion have its type and denote the same value.

A certificate is a rose tree whose node's label names a rule and whose children are its
premises' certificates and the terms and types the rule names. The checker is a fold over the
certificate that computes each conclusion from its premises' conclusions, trusting no stated
conclusion; its result is a function of an environment of a program's definitions and theorems
about it, the global environment the definitions load, the context and the hypotheses. Its rules
are those of equality; congruence of every term former; the β and η rules of functions, pairs
and the unit type; the δ rules, each a primitive at literals equal to the literal of its value;
weakening, cut and instantiation of the innermost variable; the computation rules of the
conditional at a quoted tree, of the right fold and case analysis of lists, of iteration and of
the fold of trees; induction on lists, on trees and on labels; references to definitions;
iteration's reading of the label, and the conditional as an iteration; and instances of the
axioms and of the theorems, each variable replaced by a term of its type. Its soundness is
proved against the denotation {name}`Geb.Kernel.infer`.

The axioms are the defining equations of the primitives, each from the universal property of
the object it acts on: the rose-tree object's structure map is inverse to the label and the
children, by Lambek's lemma; the labels are its natural numbers object, whose arithmetic is
defined by iteration; the arity and the children by index are defined by the right fold and case
analysis of lists; and equality of trees is the characteristic map of the diagonal.

## Main definitions

* {lit}`Eqn`, {lit}`Eqn.Holds`, {lit}`Valid` — equations, their truth at a value of the
  context, and valid sequents.
* {lit}`Loaded` — the agreement of a program's definitions with a global environment.
* {lit}`Thm`, {lit}`Env`, {lit}`Env.Sound` — theorems, environments of definitions and
  theorems, and their soundness for a global environment.
* {lit}`axioms` — the defining equations of the primitives.
* {lit}`instAll`, {lit}`Thm.inst`, {lit}`Thm.cite` — an equation at terms for its variables.
* {lit}`mapBy` — the kernel term of a map over a list, by the right fold.
* {lit}`listLit`, {lit}`IsLit` — the literal of a list of trees, and the test for a literal.
* {lit}`checkCore`, {lit}`checkMore`, {lit}`check` — the rules, and the checker.

## Main statements

* {lit}`Geb.Kernel.infer_append` — extending the global environment keeps denotations.
* {lit}`load_loaded` — a loaded program's definitions agree with its environment.
* {lit}`axioms_valid` — the defining equations of the primitives hold.
* {lit}`valid_thm_inst` — a theorem holds at terms of its variables' types.
* {lit}`check_sound` — every conclusion the checker computes is valid.

## Implementation notes

An induction rule moves the hypotheses below the induction variable: the checker lowers them
and checks that they are typed there, a decidable check in place of the converse of weakening.
The rules are dispatched in two matches of labels, so that each match's case analysis in the
soundness proof stays small.

The checker evaluates no term but a primitive at literals: a checker written in the kernel's
own language could not evaluate every closed term, since a total language has no total
interpreter of its own terms, and each δ rule is a primitive's own value. Evaluation of a closed
term is derived from the δ rules, the computation rules and congruence.

An axiom is cited by its index in {lit}`axioms` and a theorem by its index among an
environment's theorems, each by its own rule, and the labels of the rules, as the table of
axioms, are only extended: a certificate therefore checks alike when axioms or rules are added,
as they are for a new primitive.

## References

* \[Goedel1958\], the theory T.
* \[AvigadFeferman1998\], Section 2.2, for T as a quantifier-free theory with a rule of
  induction.

## Tags

bootstrap, Gödel's T, equational logic, proof certificate, System T, soundness
-/

set_option doc.verso true

@[expose] public section

namespace Geb.Kernel

open scoped FinEnum

/-- A function type read as one. -/
@[simp] theorem Ty.arrow?_tArrow (A B : Tree) : Ty.arrow? (tArrow A B) = some ⟨A, B, rfl⟩ := rfl

/-- A product type read as one. -/
@[simp] theorem Ty.prod?_tProd (A B : Tree) : Ty.prod? (tProd A B) = some ⟨A, B, rfl⟩ := rfl

/-- A list type read as one. -/
@[simp] theorem Ty.list?_tList (A : Tree) : Ty.list? (tList A) = some ⟨A, rfl⟩ := rfl

/-- The denotation of an application of a term of a function type. -/
theorem infer_app {G : List Glob} {Γ : Ctx} {f x A B : Tree}
    {ff : Γ.den → Ty.den (tArrow A B)} {fx : Γ.den → Ty.den A}
    (hf : infer G Γ f = some ⟨tArrow A B, ff⟩) (hx : infer G Γ x = some ⟨A, fx⟩) :
    infer G Γ (mk Label.app [f, x]) = some ⟨B, fun e ↦ ff e (fx e)⟩ := by
  simp only [infer] at hf hx
  simp only [mk, infer_node, List.map_cons, List.map_nil, inferStep, Option.bind_eq_bind, hf, hx,
    Option.bind_some, Ty.arrow?_tArrow]
  split
  · rfl
  · contradiction

/-- The denotation of an abstraction. -/
theorem infer_lam {G : List Glob} {Γ : Ctx} {A b B : Tree} {fb : Ctx.den (A :: Γ) → Ty.den B}
    (hA : Ty.IsTy A = true) (hb : infer G (A :: Γ) b = some ⟨B, fb⟩) :
    infer G Γ (mk Label.lam [A, b]) = some ⟨tArrow A B, fun e a ↦ fb (a, e)⟩ := by
  simp only [infer] at hb
  simp only [mk, infer_node, List.map_cons, List.map_nil, inferStep, hA, ↓reduceIte, hb,
    Option.map_some]

/-- The denotation of the unit value. -/
theorem infer_unit (G : List Glob) (Γ : Ctx) :
    infer G Γ (mk Label.unit []) = some ⟨tUnit, fun _ ↦ ()⟩ := by
  simp only [mk, infer_node, List.map_nil, inferStep]

/-- The denotation of a pair. -/
theorem infer_pair {G : List Glob} {Γ : Ctx} {a b A B : Tree} {fa : Γ.den → Ty.den A}
    {fb : Γ.den → Ty.den B} (ha : infer G Γ a = some ⟨A, fa⟩) (hb : infer G Γ b = some ⟨B, fb⟩) :
    infer G Γ (mk Label.pair [a, b]) = some ⟨tProd A B, fun e ↦ (fa e, fb e)⟩ := by
  simp only [infer] at ha hb
  simp only [mk, infer_node, List.map_cons, List.map_nil, inferStep, Option.bind_eq_bind, ha, hb,
    Option.bind_some]

/-- The denotation of the first projection. -/
theorem infer_fst {G : List Glob} {Γ : Ctx} {p A B : Tree} {fp : Γ.den → Ty.den (tProd A B)}
    (hp : infer G Γ p = some ⟨tProd A B, fp⟩) :
    infer G Γ (mk Label.fst [p]) = some ⟨A, fun e ↦ (fp e).1⟩ := by
  simp only [infer] at hp
  simp only [mk, infer_node, List.map_cons, List.map_nil, inferStep, Option.bind_eq_bind, hp,
    Option.bind_some, Ty.prod?_tProd]
  rfl

/-- The denotation of the second projection. -/
theorem infer_snd {G : List Glob} {Γ : Ctx} {p A B : Tree} {fp : Γ.den → Ty.den (tProd A B)}
    (hp : infer G Γ p = some ⟨tProd A B, fp⟩) :
    infer G Γ (mk Label.snd [p]) = some ⟨B, fun e ↦ (fp e).2⟩ := by
  simp only [infer] at hp
  simp only [mk, infer_node, List.map_cons, List.map_nil, inferStep, Option.bind_eq_bind, hp,
    Option.bind_some, Ty.prod?_tProd]
  rfl

/-- The denotation of a quoted tree. -/
theorem infer_quote (G : List Glob) (Γ : Ctx) (t : Tree) :
    infer G Γ (mk Label.quote [t]) = some ⟨tT, fun _ ↦ t⟩ := by
  simp only [mk, infer_node, List.map_cons, List.map_nil, inferStep]

/-- The denotation of a conditional. -/
theorem infer_if {G : List Glob} {Γ : Ctx} {c a b A : Tree} {fc : Γ.den → Ty.den tT}
    {fa fb : Γ.den → Ty.den A} (hc : infer G Γ c = some ⟨tT, fc⟩)
    (ha : infer G Γ a = some ⟨A, fa⟩) (hb : infer G Γ b = some ⟨A, fb⟩) :
    infer G Γ (mk Label.cond [c, a, b]) =
      some ⟨A, fun e ↦ if (fc e : Tree).label ≠ 0 then fa e else fb e⟩ := by
  simp only [infer] at hc ha hb
  simp only [mk, infer_node, List.map_cons, List.map_nil, inferStep, Option.bind_eq_bind, hc, ha,
    hb, Option.bind_some]
  split
  · rfl
  · contradiction

/-- The denotation of the empty list. -/
theorem infer_nil {G : List Glob} {Γ : Ctx} {A : Tree} (hA : Ty.IsTy A = true) :
    infer G Γ (mk Label.nil [A]) = some ⟨tList A, fun _ ↦ []⟩ := by
  simp only [mk, infer_node, List.map_cons, List.map_nil, inferStep, hA, ↓reduceIte]
  rfl

/-- The denotation of a list of a head and a tail. -/
theorem infer_cons {G : List Glob} {Γ : Ctx} {x xs A : Tree} {fx : Γ.den → Ty.den A}
    {fxs : Γ.den → Ty.den (tList A)} (hx : infer G Γ x = some ⟨A, fx⟩)
    (hxs : infer G Γ xs = some ⟨tList A, fxs⟩) :
    infer G Γ (mk Label.cons [x, xs]) = some ⟨tList A, fun e ↦ fx e :: fxs e⟩ := by
  simp only [infer] at hx hxs
  simp only [mk, infer_node, List.map_cons, List.map_nil, inferStep, Option.bind_eq_bind, hx, hxs,
    Option.bind_some, Ty.list?_tList]
  split
  · rfl
  · contradiction

/-- The denotation of the right fold of lists. -/
theorem infer_foldr {G : List Glob} {Γ : Ctx} {A B : Tree} (hA : Ty.IsTy A = true)
    (hB : Ty.IsTy B = true) :
    infer G Γ (mk Label.foldr [A, B]) = some ⟨foldrTy A B, fun _ ↦ foldrDen A B⟩ := by
  simp only [mk, infer_node, List.map_cons, List.map_nil, inferStep, hA, hB, Bool.and_self,
    ↓reduceIte]
  rfl

/-- A term's denotation is unchanged when the global environment is extended. -/
theorem infer_append {G : List Glob} (G' : List Glob) :
    ∀ (t : Tree) (Γ : Ctx) (m : Meaning Γ), infer G Γ t = some m →
      infer (G ++ G') Γ t = some m := by
  refine RoseTree.ind fun l cs ih Γ m h ↦ ?_
  rw [infer_node] at h
  unfold inferStep at h
  split at h
  case h_1 n s heq =>
    obtain ⟨rfl, rfl⟩ := map_para_eq_one heq
    simp only [infer_node, List.map_cons, List.map_nil, inferStep]
    exact h
  case h_2 c sA c' b heq =>
    obtain ⟨rfl, rfl, rfl⟩ := map_para_eq_two heq
    split at h
    · rename_i hA
      obtain ⟨mb, hb, rfl⟩ := Option.map_eq_some_iff.mp h
      have hb' := ih c' (by simp) (c :: Γ) mb hb
      simp only [infer] at hb'
      simp only [infer_node, List.map_cons, List.map_nil, inferStep, hA, ↓reduceIte, hb',
        Option.map_some]
    · cases h
  case h_3 cf f cx x heq =>
    obtain ⟨rfl, rfl, rfl⟩ := map_para_eq_two heq
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨mf, hf, mx, hx, ⟨A, B, hAB⟩, harr, h⟩ := h
    have hf' := ih cf (by simp) Γ mf hf
    have hx' := ih cx (by simp) Γ mx hx
    simp only [infer] at hf' hx'
    simp only [infer_node, List.map_cons, List.map_nil, inferStep, Option.bind_eq_bind, hf', hx',
      Option.bind_some, harr]
    exact h
  case h_4 heq =>
    obtain rfl := List.map_eq_nil_iff.mp heq
    cases h
    simp only [infer_node, List.map_nil, inferStep]
  case h_5 ca a cb b heq =>
    obtain ⟨rfl, rfl, rfl⟩ := map_para_eq_two heq
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨ma, ha, mb, hb, h⟩ := h
    have ha' := ih ca (by simp) Γ ma ha
    have hb' := ih cb (by simp) Γ mb hb
    simp only [infer] at ha' hb'
    simp only [infer_node, List.map_cons, List.map_nil, inferStep, Option.bind_eq_bind, ha', hb',
      Option.bind_some]
    exact h
  case h_6 cp p heq =>
    obtain ⟨rfl, rfl⟩ := map_para_eq_one heq
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨mp, hp, ⟨A, B, hAB⟩, hprod, h⟩ := h
    have hp' := ih cp (by simp) Γ mp hp
    simp only [infer] at hp'
    simp only [infer_node, List.map_cons, List.map_nil, inferStep, Option.bind_eq_bind, hp',
      Option.bind_some, hprod]
    exact h
  case h_7 cp p heq =>
    obtain ⟨rfl, rfl⟩ := map_para_eq_one heq
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨mp, hp, ⟨A, B, hAB⟩, hprod, h⟩ := h
    have hp' := ih cp (by simp) Γ mp hp
    simp only [infer] at hp'
    simp only [infer_node, List.map_cons, List.map_nil, inferStep, Option.bind_eq_bind, hp',
      Option.bind_some, hprod]
    exact h
  case h_8 t st heq =>
    obtain ⟨rfl, rfl⟩ := map_para_eq_one heq
    cases h
    simp only [infer_node, List.map_cons, List.map_nil, inferStep]
  case h_9 cc c ca a cb b heq =>
    obtain ⟨rfl, rfl, rfl, rfl⟩ := map_para_eq_three heq
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨mc, hc, ma, ha, mb, hb, h⟩ := h
    have hc' := ih cc (by simp) Γ mc hc
    have ha' := ih ca (by simp) Γ ma ha
    have hb' := ih cb (by simp) Γ mb hb
    simp only [infer] at hc' ha' hb'
    simp only [infer_node, List.map_cons, List.map_nil, inferStep, Option.bind_eq_bind, hc', ha',
      hb', Option.bind_some]
    exact h
  case h_10 A sA heq =>
    obtain ⟨rfl, rfl⟩ := map_para_eq_one heq
    split at h
    · rename_i hA
      cases h
      simp only [infer_node, List.map_cons, List.map_nil, inferStep, hA, ↓reduceIte]
    · cases h
  case h_11 A sA heq =>
    obtain ⟨rfl, rfl⟩ := map_para_eq_one heq
    split at h
    · rename_i hA
      cases h
      simp only [infer_node, List.map_cons, List.map_nil, inferStep, hA, ↓reduceIte]
    · cases h
  case h_12 A sA heq =>
    obtain ⟨rfl, rfl⟩ := map_para_eq_one heq
    split at h
    · rename_i hA
      cases h
      simp only [infer_node, List.map_cons, List.map_nil, inferStep, hA, ↓reduceIte]
    · cases h
  case h_13 cx x cxs xs heq =>
    obtain ⟨rfl, rfl, rfl⟩ := map_para_eq_two heq
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨mx, hx, mxs, hxs, ⟨A, hA⟩, hlist, h⟩ := h
    have hx' := ih cx (by simp) Γ mx hx
    have hxs' := ih cxs (by simp) Γ mxs hxs
    simp only [infer] at hx' hxs'
    simp only [infer_node, List.map_cons, List.map_nil, inferStep, Option.bind_eq_bind, hx', hxs',
      Option.bind_some, hlist]
    exact h
  case h_14 A sA B sB heq =>
    obtain ⟨rfl, rfl, rfl⟩ := map_para_eq_two heq
    split at h
    · rename_i hAB
      cases h
      simp only [infer_node, List.map_cons, List.map_nil, inferStep, hAB, ↓reduceIte]
    · cases h
  case h_15 k sk heq =>
    obtain ⟨rfl, rfl⟩ := map_para_eq_one heq
    simp only [infer_node, List.map_cons, List.map_nil, inferStep]
    exact h
  case h_16 n sn heq =>
    obtain ⟨rfl, rfl⟩ := map_para_eq_one heq
    obtain ⟨g, hg, rfl⟩ := Option.map_eq_some_iff.mp h
    simp only [infer_node, List.map_cons, List.map_nil, inferStep,
      List.getElem?_append_left (List.getElem?_eq_some_iff.mp hg).1, hg, Option.map_some]
  case h_17 A sA B sB heq =>
    obtain ⟨rfl, rfl, rfl⟩ := map_para_eq_two heq
    split at h
    · rename_i hAB
      cases h
      simp only [infer_node, List.map_cons, List.map_nil, inferStep, hAB, ↓reduceIte]
    · cases h
  case h_18 => cases h

/-- The denotation of the primitive giving a tree's label. -/
theorem infer_label (G : List Glob) (Γ : Ctx) :
    infer G Γ (mk Label.prim [leaf Prim.label]) =
      some ⟨tArrow tT tT, fun _ ↦ Const.label⟩ := rfl

/-- The denotation of the primitive building a node. -/
theorem infer_nodePrim (G : List Glob) (Γ : Ctx) :
    infer G Γ (mk Label.prim [leaf Prim.node]) =
      some ⟨tArrow tT (tArrow (tList tT) tT), fun _ ↦ Const.node⟩ :=
  rfl

/-- The denotation of the primitive adding labels. -/
theorem infer_add (G : List Glob) (Γ : Ctx) :
    infer G Γ (mk Label.prim [leaf Prim.add]) =
      some ⟨tArrow tT (tArrow tT tT), fun _ ↦ Const.add⟩ := rfl

/-- The denotation of the primitive giving a tree's child by index. -/
theorem infer_childPrim (G : List Glob) (Γ : Ctx) :
    infer G Γ (mk Label.prim [leaf Prim.child]) =
      some ⟨tArrow tT (tArrow tT tT), fun _ ↦ Const.child⟩ := rfl

/-- The denotation of the primitive giving a tree's children. -/
theorem infer_childrenPrim (G : List Glob) (Γ : Ctx) :
    infer G Γ (mk Label.prim [leaf Prim.children]) =
      some ⟨tArrow tT (tList tT), fun _ ↦ Const.children⟩ := rfl

/-- The denotation of the primitive subtracting labels. -/
theorem infer_sub (G : List Glob) (Γ : Ctx) :
    infer G Γ (mk Label.prim [leaf Prim.sub]) =
      some ⟨tArrow tT (tArrow tT tT), fun _ ↦ Const.sub⟩ := rfl

/-- The denotation of the primitive dividing labels. -/
theorem infer_div (G : List Glob) (Γ : Ctx) :
    infer G Γ (mk Label.prim [leaf Prim.div]) =
      some ⟨tArrow tT (tArrow tT tT), fun _ ↦ Const.div⟩ := rfl

/-- The denotation of the primitive giving the remainder of labels. -/
theorem infer_mod (G : List Glob) (Γ : Ctx) :
    infer G Γ (mk Label.prim [leaf Prim.mod]) =
      some ⟨tArrow tT (tArrow tT tT), fun _ ↦ Const.mod⟩ := rfl

/-- The denotation of the primitive comparing labels for equality. -/
theorem infer_eqPrim (G : List Glob) (Γ : Ctx) :
    infer G Γ (mk Label.prim [leaf Prim.eq]) =
      some ⟨tArrow tT (tArrow tT tT), fun _ ↦ Const.eq⟩ := rfl

/-- The denotation of the fold of trees. -/
theorem infer_fold {G : List Glob} {Γ : Ctx} {A : Tree} (hA : Ty.IsTy A = true) :
    infer G Γ (mk Label.fold [A]) = some ⟨foldTy A, fun _ ↦ foldDen A⟩ := by
  simp only [mk, infer_node, List.map_cons, List.map_nil, inferStep, hA, ↓reduceIte]
  rfl

/-- The denotation of iteration. -/
theorem infer_iter {G : List Glob} {Γ : Ctx} {A : Tree} (hA : Ty.IsTy A = true) :
    infer G Γ (mk Label.iter [A]) = some ⟨iterTy A, fun _ ↦ iterDen A⟩ := by
  simp only [mk, infer_node, List.map_cons, List.map_nil, inferStep, hA, ↓reduceIte]
  rfl

/-- The denotation of case analysis of lists. -/
theorem infer_lcase {G : List Glob} {Γ : Ctx} {A B : Tree} (hA : Ty.IsTy A = true)
    (hB : Ty.IsTy B = true) :
    infer G Γ (mk Label.lcase [A, B]) = some ⟨lcaseTy A B, fun _ ↦ lcaseDen A B⟩ := by
  simp only [mk, infer_node, List.map_cons, List.map_nil, inferStep, hA, hB, Bool.and_self,
    ↓reduceIte]
  rfl

/-- A closed term, weakened into a context, denotes its value there. -/
theorem infer_closed {G : List Glob} {t : Tree} {m : Meaning []} (h : infer G [] t = some m)
    (Γ : Ctx) : ∃ f : Γ.den → Ty.den m.1, infer G Γ (wk Γ.length t) = some ⟨m.1, f⟩ ∧
      ∀ e, f e = m.2 () := by
  have key : ∀ Δ : Ctx, Δ = Γ ++ [] → ∃ f : Δ.den → Ty.den m.1,
      infer G Δ (wk Γ.length t) = some ⟨m.1, f⟩ ∧ ∀ e, f e = m.2 () := by
    intro Δ hΔ
    subst hΔ
    exact ⟨m.2 ∘ Ctx.drop Γ, infer_wk Γ h, fun _ ↦ rfl⟩
  exact key Γ (List.append_nil Γ).symm

end Geb.Kernel

namespace Geb.GoedelT

open Geb.Kernel
open scoped FinEnum

/-- An equation between two terms of a type. -/
@[ext] structure Eqn where
  /-- The type of both sides. -/
  ty : Tree
  /-- The left side. -/
  lhs : Tree
  /-- The right side. -/
  rhs : Tree
deriving DecidableEq

/-- The type of a term in a context, when it has one. -/
def typeOf (G : List Glob) (Γ : Ctx) (t : Tree) : Option Tree := (infer G Γ t).map (·.1)

namespace Eqn

/-- An equation holds at a value of its context: both sides have its type, and their
denotations agree there. -/
def Holds (G : List Glob) (Γ : Ctx) (q : Eqn) (e : Γ.den) : Prop :=
  ∃ f g : Γ.den → Ty.den q.ty, infer G Γ q.lhs = some ⟨q.ty, f⟩ ∧
    infer G Γ q.rhs = some ⟨q.ty, g⟩ ∧ f e = g e

/-- An equation with both sides weakened by {lit}`n` variables. -/
def wk (n : ℕ) (q : Eqn) : Eqn := ⟨q.ty, Kernel.wk n q.lhs, Kernel.wk n q.rhs⟩

/-- An equation with its innermost variable removed, the equation it weakens when that variable
does not occur in it. -/
def lower (q : Eqn) : Eqn :=
  ⟨q.ty, subst (Kernel.mk Label.quote [leaf 0]) q.lhs, subst (Kernel.mk Label.quote [leaf 0]) q.rhs⟩

/-- Whether both sides of an equation have its type in a context. -/
def Typed (G : List Glob) (Γ : Ctx) (q : Eqn) : Prop :=
  typeOf G Γ q.lhs = some q.ty ∧ typeOf G Γ q.rhs = some q.ty

instance (G : List Glob) (Γ : Ctx) (q : Eqn) : Decidable (q.Typed G Γ) :=
  inferInstanceAs (Decidable (_ ∧ _))

end Eqn

/-- A sequent is valid: both sides of its conclusion have its type, and their denotations agree
at every value of the context at which its hypotheses hold. -/
def Valid (G : List Glob) (Γ : Ctx) (H : List Eqn) (q : Eqn) : Prop :=
  ∃ f g : Γ.den → Ty.den q.ty, infer G Γ q.lhs = some ⟨q.ty, f⟩ ∧
    infer G Γ q.rhs = some ⟨q.ty, g⟩ ∧ ∀ e, (∀ h ∈ H, h.Holds G Γ e) → f e = g e

/-- A program's definitions and a global environment agree: each definition denotes, in the
whole environment, the global at its position. -/
def Loaded (D : List Tree) (G : List Glob) : Prop :=
  D.length = G.length ∧ ∀ (j : ℕ) (t : Tree) (g : Glob), D[j]? = some t → G[j]? = some g →
    infer G [] t = some ⟨g.1, fun _ ↦ g.2⟩

/-- A definition loaded after the others agrees with the environment extended by its global. -/
theorem Loaded.snoc {D : List Tree} {G : List Glob} {t : Tree} {m : Meaning []}
    (h : Loaded D G) (ht : infer G [] t = some m) :
    Loaded (D ++ [t]) (G ++ [⟨m.1, m.2 ()⟩]) := by
  refine ⟨by rw [List.length_append, List.length_append, h.1]; rfl, fun j u g hu hg ↦ ?_⟩
  rcases Nat.lt_or_ge j D.length with hj | hj
  · rw [List.getElem?_append_left hj] at hu
    rw [List.getElem?_append_left (h.1 ▸ hj)] at hg
    exact infer_append _ _ _ _ (h.2 j u g hu hg)
  · have hlt := (List.getElem?_eq_some_iff.mp hu).1
    rw [List.length_append, List.length_singleton] at hlt
    obtain rfl : j = D.length := by omega
    rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero,
      Option.some.injEq] at hu
    rw [h.1, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero,
      Option.some.injEq] at hg
    subst hu hg
    exact infer_append _ _ _ _ ht

/-- Loading from nothing gives nothing. -/
theorem foldl_load_none : ∀ D : List Tree, D.foldl (fun acc t ↦ do
    let G ← acc
    let m ← infer G [] t
    some (G ++ [⟨m.1, m.2 ()⟩])) none = none :=
  List.rec rfl fun _ _ ih ↦ ih

/-- Loading definitions after agreeing ones keeps the agreement. -/
theorem loaded_foldl : ∀ (D D0 : List Tree) (G0 G : List Glob), Loaded D0 G0 →
    D.foldl (fun acc t ↦ do
      let G ← acc
      let m ← infer G [] t
      some (G ++ [⟨m.1, m.2 ()⟩])) (some G0) = some G → Loaded (D0 ++ D) G :=
  List.rec
    (fun D0 G0 G h hf ↦ by
      rw [List.foldl_nil, Option.some.injEq] at hf
      subst hf
      rwa [List.append_nil])
    (fun t D ih D0 G0 G h hf ↦ by
      rw [List.foldl_cons] at hf
      rw [Option.bind_eq_bind, Option.bind_some] at hf
      cases ht : infer G0 [] t with
      | none =>
        rw [ht] at hf
        exact absurd ((foldl_load_none D).symm.trans hf) fun h ↦ nomatch h
      | some m =>
        rw [ht] at hf
        have := ih (D0 ++ [t]) _ G (h.snoc ht) hf
        rwa [List.append_assoc, List.singleton_append] at this)

/-- A theorem: an equation valid in a context under no hypotheses. -/
@[ext] structure Thm where
  /-- The context. -/
  ctx : Ctx
  /-- The equation. -/
  eqn : Eqn
deriving DecidableEq

/-- A theorem holds in a global environment: its equation is valid in its context. -/
def Thm.Valid (G : List Glob) (th : Thm) : Prop := GoedelT.Valid G th.ctx [] th.eqn

/-- The global facts a certificate may cite: a program's definitions, and theorems about it. -/
structure Env where
  /-- The program's definitions. -/
  defs : List Tree
  /-- The theorems. -/
  thms : List Thm

/-- An environment is sound for a global environment: its definitions are loaded into it and
its theorems hold in it. -/
def Env.Sound (E : Env) (G : List Glob) : Prop := Loaded E.defs G ∧ ∀ th ∈ E.thms, th.Valid G

/-- A loaded program's definitions agree with its environment. -/
theorem load_loaded {D : List Tree} {G : List Glob} (h : load D = some G) : Loaded D G :=
  loaded_foldl D [] [] G
    ⟨rfl, fun _ _ _ ht _ ↦ absurd ht (by rw [List.getElem?_nil]; exact fun h ↦ nomatch h)⟩
    h

/-- The list of a function's values at the elements of a list, as a kernel term: the right fold
putting the value of {lit}`body`, in which the variable {lit}`1` is the element, in front of the
result. -/
def mapBy (A B body xs : Tree) : Tree :=
  apps (mk Label.foldr [A, tList B]) [mk Label.lam [A, mk Label.lam [tList B, mk Label.cons [body,
      Tm.var 0]]], mk Label.nil [B], xs]

/-- The argument and result types of a function type. -/
def arrowParts (F : Tree) : Option (Tree × Tree) :=
  match F.children with
  | [A, B] => if F = tArrow A B then some (A, B) else none
  | _ => none

/-- The component types of a product type. -/
def prodParts (P : Tree) : Option (Tree × Tree) :=
  match P.children with
  | [A, B] => if P = tProd A B then some (A, B) else none
  | _ => none

/-- The element type of a list type. -/
def listParts (L : Tree) : Option Tree :=
  match L.children with
  | [A] => if L = tList A then some A else none
  | _ => none

/-- The weakening of a term by {lit}`n` variables below {lit}`k` bound ones. -/
def wkAt (k n : ℕ) (t : Tree) : Tree := trav (wkVar n) t k

/-- An equation with its innermost variable replaced by a term. -/
def Eqn.subst (u : Tree) (q : Eqn) : Eqn := ⟨q.ty, Kernel.subst u q.lhs, Kernel.subst u q.rhs⟩

/-- An equation with both sides weakened by {lit}`n` variables below {lit}`k` bound ones. -/
def Eqn.wkAt (k n : ℕ) (q : Eqn) : Eqn :=
  ⟨q.ty, GoedelT.wkAt k n q.lhs, GoedelT.wkAt k n q.rhs⟩

/-- An equation with its variables replaced by terms, innermost first: each term, weakened past
the variables after it, replaces the innermost variable in turn. -/
def instAll : List Tree → Eqn → Eqn :=
  List.rec id fun u us ih q ↦ ih (q.subst (Kernel.wk us.length u))

/-- A theorem's equation in a context, at terms for its variables: its sides weakened past the
context, and its variables replaced by the terms. -/
def Thm.inst (th : Thm) (Γ : Ctx) (us : List Tree) : Eqn :=
  instAll us (th.eqn.wkAt th.ctx.length Γ.length)

/-- A theorem cited in a context at terms for its variables: its instance there, when the terms
have the types of its context. -/
def Thm.cite (th : Thm) (G : List Glob) (Γ : Ctx) (us : List Tree) : Option Eqn :=
  if List.Forall₂ (fun u A ↦ typeOf G Γ u = some A) us th.ctx then some (th.inst Γ us) else none

/-- The quoted leaf of a label, the numeral of the label. -/
def num (n : ℕ) : Tree := mk Label.quote [leaf n]

/-- A primitive, by index, applied to arguments. -/
def prim (k : ℕ) (xs : List Tree) : Tree := apps (mk Label.prim [leaf k]) xs

/-- The successor of a label, its sum with one: the structure map of the natural numbers object
that the labels form. -/
def succT (t : Tree) : Tree := prim Prim.add [t, num 1]

/-- The type of pairs of trees. -/
def tT2 : Tree := tProd tT tT

/-- The label of a node is the label of its first argument: with the next two, the primitive
building a node is inverse to its label and its list of children. -/
def axLabelNode : Thm :=
  ⟨[tT, tList tT], ⟨tT, prim Prim.label [prim Prim.node [Tm.var 0, Tm.var 1]],
      prim Prim.label [Tm.var 0]⟩⟩

/-- The children of a node are its list of children. -/
def axChildrenNode : Thm :=
  ⟨[tT, tList tT], ⟨tList tT, prim Prim.children [prim Prim.node [Tm.var 0, Tm.var 1]], Tm.var 1⟩⟩

/-- A tree is the node of its label over its children. -/
def axNodeEta : Thm := ⟨[tT], ⟨tT, prim Prim.node [prim Prim.label [Tm.var 0],
    prim Prim.children [Tm.var 0]], Tm.var 0⟩⟩

/-- A label is a leaf: labels form the natural numbers object inside the trees. -/
def axChildrenLabel : Thm := ⟨[tT], ⟨tList tT, prim Prim.children [prim Prim.label [Tm.var 0]],
    mk Label.nil [tT]⟩⟩

/-- The successor of a label is a label. -/
def axLabelSucc : Thm := ⟨[tT], ⟨tT, prim Prim.label [succT (Tm.var 0)], succT (Tm.var 0)⟩⟩

/-- Addition iterates the successor, from the label of its first argument. -/
def axAddIter : Thm :=
  ⟨[tT, tT], ⟨tT, prim Prim.add [Tm.var 0, Tm.var 1],
    apps (mk Label.iter [tT]) [mk Label.lam [tT, succT (Tm.var 0)], prim Prim.label [Tm.var 0],
        Tm.var 1]⟩⟩

/-- The predecessor, the difference with one, is the first component of the iteration from a
pair of zeros that moves the second component to the first and replaces it by its successor. -/
def axPredIter : Thm :=
  ⟨[tT], ⟨tT, prim Prim.sub [Tm.var 0, num 1],
    mk Label.fst [apps (mk Label.iter [tT2]) [mk Label.lam [tT2,
        mk Label.pair [mk Label.snd [Tm.var 0], succT (mk Label.snd [Tm.var 0])]],
      mk Label.pair [num 0, num 0], Tm.var 0]]⟩⟩

/-- Truncated subtraction iterates the predecessor, from the label of its first argument. -/
def axSubIter : Thm :=
  ⟨[tT, tT], ⟨tT, prim Prim.sub [Tm.var 0, Tm.var 1],
    apps (mk Label.iter [tT]) [mk Label.lam [tT, prim Prim.sub [Tm.var 0, num 1]],
        prim Prim.label [Tm.var 0], Tm.var 1]⟩⟩

/-- Multiplication iterates the addition of its first argument, from zero. -/
def axMulIter : Thm :=
  ⟨[tT, tT], ⟨tT, prim Prim.mul [Tm.var 0, Tm.var 1],
    apps (mk Label.iter [tT]) [mk Label.lam [tT, prim Prim.add [Tm.var 0, Tm.var 1]], num 0,
        Tm.var 1]⟩⟩

/-- The iteration, as many times as the label of the variable {lit}`0`, of the step of division
by the label of the variable {lit}`1` on a pair of a quotient and a remainder: the remainder's
successor, and the quotient's successor with the remainder zero when that successor is the
divisor. -/
def divMod : Tree :=
  apps (mk Label.iter [tT2]) [mk Label.lam [tT2,
      mk Label.cond [prim Prim.eq [succT (mk Label.snd [Tm.var 0]), Tm.var 2],
      mk Label.pair [succT (mk Label.fst [Tm.var 0]),
          num 0], mk Label.pair [mk Label.fst [Tm.var 0], succT (mk Label.snd [Tm.var 0])]]],
    mk Label.pair [num 0, num 0], Tm.var 0]

/-- Division is the quotient of the iterated step of division. -/
def axDivIter : Thm := ⟨[tT, tT], ⟨tT, prim Prim.div [Tm.var 0, Tm.var 1], mk Label.fst [divMod]⟩⟩

/-- The remainder is the remainder of the iterated step of division. -/
def axModIter : Thm := ⟨[tT, tT], ⟨tT, prim Prim.mod [Tm.var 0, Tm.var 1], mk Label.snd [divMod]⟩⟩

/-- Equality of labels is the test for zero of the sum of the two truncated differences. -/
def axEqDef : Thm :=
  ⟨[tT, tT], ⟨tT, prim Prim.eq [Tm.var 0, Tm.var 1], apps (mk Label.iter [tT]) [mk Label.lam [tT,
      num 0], num 1,
    prim Prim.add [prim Prim.sub [Tm.var 0, Tm.var 1], prim Prim.sub [Tm.var 1, Tm.var 0]]]⟩⟩

/-- A label is less than another when their truncated difference is not zero. -/
def axLtDef : Thm :=
  ⟨[tT, tT], ⟨tT, prim Prim.lt [Tm.var 0, Tm.var 1],
    apps (mk Label.iter [tT]) [mk Label.lam [tT, num 1], num 0, prim Prim.sub [Tm.var 1,
        Tm.var 0]]⟩⟩

/-- The logarithm of a label is zero below two, and otherwise the successor of the logarithm of
its half. -/
def axLog2Def : Thm :=
  ⟨[tT], ⟨tT, prim Prim.log2 [Tm.var 0],
    mk Label.cond [prim Prim.lt [Tm.var 0, num 2], num 0,
        succT (prim Prim.log2 [prim Prim.div [Tm.var 0, num 2]])]⟩⟩

/-- The arity of a tree is the length of its children, the right fold counting them. -/
def axArityDef : Thm :=
  ⟨[tT], ⟨tT, prim Prim.arity [Tm.var 0],
    apps (mk Label.foldr [tT, tT]) [mk Label.lam [tT, mk Label.lam [tT, succT (Tm.var 0)]], num 0,
        prim Prim.children [Tm.var 0]]⟩⟩

/-- The tail of a list of trees, by case analysis. -/
def tailT : Tree :=
  mk Label.lam [tList tT,
    apps (mk Label.lcase [tT, tList tT]) [Tm.var 0, mk Label.nil [tT], mk Label.lam [tT,
        mk Label.lam [tList tT, Tm.var 0]]]]

/-- A tree's child by index is the head of its children with the tail taken that many times,
and zero when that list is empty. -/
def axChildDef : Thm :=
  ⟨[tT, tT], ⟨tT, prim Prim.child [Tm.var 0, Tm.var 1],
    apps (mk Label.lcase [tT, tT]) [apps (mk Label.iter [tList tT]) [tailT,
        prim Prim.children [Tm.var 0], Tm.var 1], num 0,
      mk Label.lam [tT, mk Label.lam [tList tT, Tm.var 1]]]⟩⟩

/-- Equality of trees holds of a tree and itself. -/
def axEqualRefl : Thm := ⟨[tT], ⟨tT, prim Prim.equal [Tm.var 0, Tm.var 0], num 1⟩⟩

/-- Trees that are equal replace each other: the conditional on their equality choosing the
second when it holds is the first. -/
def axEqualSubst : Thm :=
  ⟨[tT, tT], ⟨tT, mk Label.cond [prim Prim.equal [Tm.var 0, Tm.var 1], Tm.var 1, Tm.var 0],
      Tm.var 0⟩⟩

/-- Equality of trees takes the values one and zero only. -/
def axEqualBool : Thm :=
  ⟨[tT, tT],
    ⟨tT, mk Label.cond [prim Prim.equal [Tm.var 0, Tm.var 1], num 1, num 0],
        prim Prim.equal [Tm.var 0, Tm.var 1]⟩⟩

/-- The defining equations of the kernel's primitives, each a theorem in the context of its
variables: the rose-tree object's structure map is inverse to its label and its children, the
labels are its natural numbers object, the arithmetic of labels is defined through iteration,
the arity and the children by index through the right fold and case analysis of lists, and
equality of trees is the characteristic map of the diagonal. -/
def axioms : List Thm :=
  [axLabelNode, axChildrenNode, axNodeEta, axChildrenLabel, axLabelSucc, axAddIter, axPredIter,
   axSubIter, axMulIter, axDivIter, axModIter, axEqDef, axLtDef, axLog2Def, axArityDef,
   axChildDef, axEqualRefl, axEqualSubst, axEqualBool]

/-- The literal of a list of trees: each tree quoted, in front of the empty list of trees. -/
def listLit (xs : List Tree) : Tree := xs.foldr (fun x r ↦ mk Label.cons [mk Label.quote [x],
    r]) (mk Label.nil [tT])

/-- Whether a term is a list literal: the empty list, or a quoted tree in front of a list
literal. -/
def IsListLit : Tree → Bool :=
  RoseTree.para fun l rs ↦
    match l, rs with
    | Label.nil, [_] => true
    | Label.cons, [(x, _), (_, r)] => x.label == Label.quote && x.children.length == 1 && r
    | _, _ => false

/-- Whether a term is a literal: a quoted tree, or a list literal. -/
def IsLit (t : Tree) : Bool := t.label == Label.quote && t.children.length == 1 || IsListLit t

/-- The literal of a closed term's value, when its type is that of trees or of lists of
trees. -/
def lit? (m : Meaning []) : Option Tree :=
  if h : m.1 = tT then some (mk Label.quote [cast (congrArg Ty.den h) (m.2 ())])
  else if h : m.1 = tList tT then some (listLit (cast (congrArg Ty.den h) (m.2 ())))
  else none

namespace Rule

/-- The label of the rule of a hypothesis, by index. -/
@[match_pattern] abbrev hyp : ℕ := 0

/-- The label of the rule of reflexivity. -/
@[match_pattern] abbrev refl : ℕ := 1

/-- The label of the rule of symmetry. -/
@[match_pattern] abbrev symm : ℕ := 2

/-- The label of the rule of transitivity. -/
@[match_pattern] abbrev trans : ℕ := 3

/-- The label of the rule of congruence of application. -/
@[match_pattern] abbrev congApp : ℕ := 4

/-- The label of the rule of congruence of abstraction. -/
@[match_pattern] abbrev congLam : ℕ := 5

/-- The label of the rule of congruence of pairs. -/
@[match_pattern] abbrev congPair : ℕ := 6

/-- The label of the rule of congruence of the first projection. -/
@[match_pattern] abbrev congFst : ℕ := 7

/-- The label of the rule of congruence of the second projection. -/
@[match_pattern] abbrev congSnd : ℕ := 8

/-- The label of the rule of congruence of the list of a head and a tail. -/
@[match_pattern] abbrev congCons : ℕ := 9

/-- The label of the rule of congruence of the conditional. -/
@[match_pattern] abbrev congCond : ℕ := 10

/-- The label of the rule of the β rule of functions. -/
@[match_pattern] abbrev beta : ℕ := 11

/-- The label of the rule of the η rule of functions. -/
@[match_pattern] abbrev eta : ℕ := 12

/-- The label of the rule of the β rule of the first projection. -/
@[match_pattern] abbrev betaFst : ℕ := 13

/-- The label of the rule of the β rule of the second projection. -/
@[match_pattern] abbrev betaSnd : ℕ := 14

/-- The label of the rule of the η rule of pairs. -/
@[match_pattern] abbrev etaPair : ℕ := 15

/-- The label of the rule of the η rule of the unit type. -/
@[match_pattern] abbrev etaUnit : ℕ := 16

/-- The label of the δ rule: a primitive at literals is the literal of its value. -/
@[match_pattern] abbrev delta : ℕ := 17

/-- The label of the rule of weakening. -/
@[match_pattern] abbrev weaken : ℕ := 18

/-- The label of the rule of cut. -/
@[match_pattern] abbrev cut : ℕ := 19

/-- The label of the rule of instantiation of the innermost variable by a term. -/
@[match_pattern] abbrev instVar : ℕ := 20

/-- The label of the rule of the right fold of lists at the empty list. -/
@[match_pattern] abbrev foldrNil : ℕ := 21

/-- The label of the rule of the right fold of lists at a list of a head and a tail. -/
@[match_pattern] abbrev foldrCons : ℕ := 22

/-- The label of the rule of induction on a list. -/
@[match_pattern] abbrev indList : ℕ := 23

/-- The label of the rule of case analysis of lists at the empty list. -/
@[match_pattern] abbrev lcaseNil : ℕ := 24

/-- The label of the rule of case analysis of lists at a list of a head and a tail. -/
@[match_pattern] abbrev lcaseCons : ℕ := 25

/-- The label of the rule of iteration at the label zero. -/
@[match_pattern] abbrev iterZero : ℕ := 26

/-- The label of the rule of iteration at the successor of a label. -/
@[match_pattern] abbrev iterSucc : ℕ := 27

/-- The label of the rule of the fold of trees at a node. -/
@[match_pattern] abbrev foldNode : ℕ := 28

/-- The label of the rule of induction on a tree. -/
@[match_pattern] abbrev indTree : ℕ := 29

/-- The label of the rule of induction on the label of a tree. -/
@[match_pattern] abbrev indLabel : ℕ := 30

/-- The label of the rule of a reference to a definition, the definition weakened into the
context. -/
@[match_pattern] abbrev unfold : ℕ := 31

/-- The label of the rule of the conditional at a quoted tree. -/
@[match_pattern] abbrev condQuote : ℕ := 32

/-- The label of the rule of an instance of an axiom, cited by its index in {lit}`axioms`. -/
@[match_pattern] abbrev ax : ℕ := 33

/-- The label of the rule of iteration's reading of the label of the tree it iterates over. -/
@[match_pattern] abbrev iterLabel : ℕ := 34

/-- The label of the rule of the conditional as the iteration of a constant function. -/
@[match_pattern] abbrev condIter : ℕ := 35

/-- The label of the rule of an instance of a theorem, cited by its index among an environment's
theorems. -/
@[match_pattern] abbrev thm : ℕ := 36

end Rule

/-- The checker's result at a certificate: the conclusion, as a function of a program's
definitions, its global environment, the context and the hypotheses, or nothing when the
certificate does not check. -/
abbrev Chk : Type := Env → List Glob → Ctx → List Eqn → Option Eqn

/-- The rules of equality, congruence, computation, substitution, the right fold of lists and
induction on lists, by the label of a certificate's node: its children are the premises'
certificates, with their results, and the terms and types the rule names. -/
def checkCore (l : ℕ) (cs : List (Tree × Chk)) : Chk := fun E G Γ H ↦
  match l, cs with
  -- a hypothesis, by index
  | Rule.hyp, [(i, _)] => H[i.label]?.bind fun q ↦ if q.Typed G Γ then some q else none
  -- reflexivity, symmetry and transitivity
  | Rule.refl, [(t, _)] => (typeOf G Γ t).map fun A ↦ ⟨A, t, t⟩
  | Rule.symm, [(_, p)] => (p E G Γ H).map fun q ↦ ⟨q.ty, q.rhs, q.lhs⟩
  | Rule.trans, [(_, p), (_, p')] => (p E G Γ H).bind fun q ↦ (p' E G Γ H).bind fun q' ↦
    if q.ty = q'.ty ∧ q.rhs = q'.lhs then some ⟨q.ty, q.lhs, q'.rhs⟩ else none
  -- congruence: application, abstraction, pairs, projections, lists and the conditional
  | Rule.congApp, [(_, p), (_, p')] => (p E G Γ H).bind fun q ↦ (p' E G Γ H).bind fun q' ↦
    (arrowParts q.ty).bind fun AB ↦
      if q'.ty = AB.1 then some ⟨AB.2, mk Label.app [q.lhs, q'.lhs], mk Label.app [q.rhs,
          q'.rhs]⟩ else none
  | Rule.congLam, [(A, _), (_, p)] =>
    if Ty.IsTy A then
      (p E G (A :: Γ) (H.map (Eqn.wk 1))).map fun q ↦
        ⟨tArrow A q.ty, mk Label.lam [A, q.lhs], mk Label.lam [A, q.rhs]⟩
    else none
  | Rule.congPair, [(_, p), (_, p')] => (p E G Γ H).bind fun q ↦ (p' E G Γ H).map fun q' ↦
    ⟨tProd q.ty q'.ty, mk Label.pair [q.lhs, q'.lhs], mk Label.pair [q.rhs, q'.rhs]⟩
  | Rule.congFst, [(_, p)] => (p E G Γ H).bind fun q ↦ (prodParts q.ty).map fun AB ↦
    ⟨AB.1, mk Label.fst [q.lhs], mk Label.fst [q.rhs]⟩
  | Rule.congSnd, [(_, p)] => (p E G Γ H).bind fun q ↦ (prodParts q.ty).map fun AB ↦
    ⟨AB.2, mk Label.snd [q.lhs], mk Label.snd [q.rhs]⟩
  | Rule.congCons, [(_, p), (_, p')] => (p E G Γ H).bind fun q ↦ (p' E G Γ H).bind fun q' ↦
    if q'.ty = tList q.ty then some ⟨q'.ty, mk Label.cons [q.lhs, q'.lhs], mk Label.cons [q.rhs,
        q'.rhs]⟩ else none
  | Rule.congCond, [(_, p), (_, p'), (_, p'')] =>
    (p E G Γ H).bind fun q ↦ (p' E G Γ H).bind fun q' ↦ (p'' E G Γ H).bind fun q'' ↦
      if q.ty = tT ∧ q''.ty = q'.ty then
        some ⟨q'.ty, mk Label.cond [q.lhs, q'.lhs, q''.lhs], mk Label.cond [q.rhs, q'.rhs, q''.rhs]⟩
      else none
  -- computation: the β and η rules of functions, pairs and the unit type
  | Rule.beta, [(A, _), (b, _), (a, _)] =>
    if Ty.IsTy A ∧ typeOf G Γ a = some A then
      (typeOf G (A :: Γ) b).map fun B ↦ ⟨B, mk Label.app [mk Label.lam [A, b], a], subst a b⟩
    else none
  | Rule.eta, [(f, _)] => (typeOf G Γ f).bind fun F ↦ (arrowParts F).bind fun AB ↦
    if Ty.IsTy AB.1 then some ⟨F, f, mk Label.lam [AB.1, mk Label.app [Kernel.wk 1 f,
        Tm.var 0]]⟩ else none
  | Rule.betaFst, [(a, _), (b, _)] => (typeOf G Γ a).bind fun A ↦ (typeOf G Γ b).map fun _ ↦
    ⟨A, mk Label.fst [mk Label.pair [a, b]], a⟩
  | Rule.betaSnd, [(a, _), (b, _)] => (typeOf G Γ a).bind fun _ ↦ (typeOf G Γ b).map fun B ↦
    ⟨B, mk Label.snd [mk Label.pair [a, b]], b⟩
  | Rule.etaPair, [(p, _)] => (typeOf G Γ p).bind fun P ↦ (prodParts P).map fun _ ↦
    ⟨P, mk Label.pair [mk Label.fst [p], mk Label.snd [p]], p⟩
  | Rule.etaUnit, [(t, _)] => if typeOf G Γ t = some tUnit then some ⟨tUnit, t,
      mk Label.unit []⟩ else none
  -- a primitive at literals is the literal of its value
  | Rule.delta, (k, _) :: as =>
    match Γ with
    | [] =>
      if (as.map Prod.fst).all IsLit then
        let t := apps (mk Label.prim [k]) (as.map Prod.fst)
        (infer G [] t).bind fun m ↦ (lit? m).map fun v ↦ ⟨m.1, t, v⟩
      else none
    | _ :: _ => none
  -- weakening, cut and instantiation of the innermost variable
  | Rule.weaken, [(_, p)] =>
    match Γ with
    | _ :: Γ' => (p E G Γ' []).map (Eqn.wk 1)
    | [] => none
  | Rule.cut, [(_, p), (_, p')] => (p E G Γ H).bind fun h ↦ p' E G Γ (h :: H)
  | Rule.instVar, [(u, _), (_, p)] => (typeOf G Γ u).bind fun A ↦
    (p E G (A :: Γ) (H.map (Eqn.wk 1))).map fun q ↦ ⟨q.ty, subst u q.lhs, subst u q.rhs⟩
  -- the right fold of lists at the empty list and at a list of a head and a tail
  | Rule.foldrNil, [(A, _), (B, _), (g, _), (z, _)] =>
    if Ty.IsTy A ∧ Ty.IsTy B ∧ typeOf G Γ g = some (tArrow A (tArrow B B)) ∧
        typeOf G Γ z = some B then
      some ⟨B, apps (mk Label.foldr [A, B]) [g, z, mk Label.nil [A]], z⟩
    else none
  | Rule.foldrCons, [(A, _), (B, _), (g, _), (z, _), (x, _), (xs, _)] =>
    if Ty.IsTy A ∧ Ty.IsTy B ∧ typeOf G Γ g = some (tArrow A (tArrow B B)) ∧
        typeOf G Γ z = some B ∧ typeOf G Γ x = some A ∧ typeOf G Γ xs = some (tList A) then
      some ⟨B, apps (mk Label.foldr [A, B]) [g, z, mk Label.cons [x, xs]],
        apps g [x, apps (mk Label.foldr [A, B]) [g, z, xs]]⟩
    else none
  -- induction on the innermost variable, a list: the case of the empty list, and the case of a
  -- head and a tail under the hypothesis for the tail
  | Rule.indList, [(s, _), (t, _), (_, p0), (_, p1)] =>
    match Γ with
    | L :: Γ' => (listParts L).bind fun A ↦ (typeOf G Γ s).bind fun B ↦
      let H0 := H.map Eqn.lower
      let c := mk Label.cons [Tm.var 1, Tm.var 0]
      if Ty.IsTy A ∧ typeOf G Γ t = some B ∧ H0.map (Eqn.wk 1) = H ∧ (∀ h ∈ H0, h.Typed G Γ') ∧
          p0 E G Γ' H0 = some ⟨B, subst (mk Label.nil [A]) s, subst (mk Label.nil [A]) t⟩ ∧
          p1 E G (L :: A :: Γ') (⟨B, wkAt 1 1 s, wkAt 1 1 t⟩ :: H0.map (Eqn.wk 2)) =
            some ⟨B, subst c (wkAt 1 2 s), subst c (wkAt 1 2 t)⟩ then
        some ⟨B, s, t⟩
      else none
    | [] => none
  | _, _ => none

/-- The rules of case analysis of lists, iteration, the fold of trees, induction on trees and on
labels, and references to definitions, by the label of a certificate's node. -/
def checkMore (l : ℕ) (cs : List (Tree × Chk)) : Chk := fun E G Γ H ↦
  match l, cs with
  -- case analysis of lists at the empty list and at a list of a head and a tail
  | Rule.lcaseNil, [(A, _), (B, _), (n, _), (c, _)] =>
    if Ty.IsTy A ∧ Ty.IsTy B ∧ typeOf G Γ n = some B ∧
        typeOf G Γ c = some (tArrow A (tArrow (tList A) B)) then
      some ⟨B, apps (mk Label.lcase [A, B]) [mk Label.nil [A], n, c], n⟩
    else none
  | Rule.lcaseCons, [(A, _), (B, _), (x, _), (xs, _), (n, _), (c, _)] =>
    if Ty.IsTy A ∧ Ty.IsTy B ∧ typeOf G Γ n = some B ∧
        typeOf G Γ c = some (tArrow A (tArrow (tList A) B)) ∧ typeOf G Γ x = some A ∧
        typeOf G Γ xs = some (tList A) then
      some ⟨B, apps (mk Label.lcase [A, B]) [mk Label.cons [x, xs], n, c], apps c [x, xs]⟩
    else none
  -- iteration at the label zero and at the successor of a label
  | Rule.iterZero, [(A, _), (s, _), (z, _)] =>
    if Ty.IsTy A ∧ typeOf G Γ s = some (tArrow A A) ∧ typeOf G Γ z = some A then
      some ⟨A, apps (mk Label.iter [A]) [s, z, mk Label.quote [leaf 0]], z⟩
    else none
  | Rule.iterSucc, [(A, _), (s, _), (z, _), (n, _)] =>
    if Ty.IsTy A ∧ typeOf G Γ s = some (tArrow A A) ∧ typeOf G Γ z = some A ∧
        typeOf G Γ n = some tT then
      some ⟨A, apps (mk Label.iter [A]) [s, z, apps (mk Label.prim [leaf Prim.add]) [n,
          mk Label.quote [leaf 1]]],
        mk Label.app [s, apps (mk Label.iter [A]) [s, z, n]]⟩
    else none
  -- the fold of trees at a node
  | Rule.foldNode, [(A, _), (f, _), (x, _), (xs, _)] =>
    if Ty.IsTy A ∧ typeOf G Γ f = some (tArrow tT (tArrow (tList A) A)) ∧
        typeOf G Γ x = some tT ∧ typeOf G Γ xs = some (tList tT) then
      some ⟨A, apps (mk Label.fold [A]) [f, apps (mk Label.prim [leaf Prim.node]) [x, xs]],
        apps f [mk Label.app [mk Label.prim [leaf Prim.label], x],
          mapBy tT A (apps (mk Label.fold [A]) [Kernel.wk 2 f, Tm.var 1]) xs]⟩
    else none
  -- induction on the innermost variable, a tree, under the hypothesis for its children
  | Rule.indTree, [(s, _), (t, _), (_, p1)] =>
    match Γ with
    | L :: Γ' => (typeOf G Γ s).bind fun B ↦
      let H0 := H.map Eqn.lower
      let nd := apps (mk Label.prim [leaf Prim.node]) [Tm.var 1, Tm.var 0]
      if L = tT ∧ Ty.IsTy B ∧ typeOf G Γ t = some B ∧ H0.map (Eqn.wk 1) = H ∧
          (∀ h ∈ H0, h.Typed G Γ') ∧
          p1 E G (tList tT :: tT :: Γ')
              (⟨tList B, mapBy tT B (subst (Tm.var 1) (wkAt 1 4 s)) (Tm.var 0),
                mapBy tT B (subst (Tm.var 1) (wkAt 1 4 t)) (Tm.var 0)⟩ :: H0.map (Eqn.wk 2)) =
            some ⟨B, subst nd (wkAt 1 2 s), subst nd (wkAt 1 2 t)⟩ then
        some ⟨B, s, t⟩
      else none
    | [] => none
  -- induction on the label of the innermost variable, a tree
  | Rule.indLabel, [(s, _), (t, _), (_, p0), (_, p1)] =>
    match Γ with
    | L :: Γ' => (typeOf G Γ s).bind fun B ↦
      let H0 := H.map Eqn.lower
      let suc := apps (mk Label.prim [leaf Prim.add]) [Tm.var 0, mk Label.quote [leaf 1]]
      let lab := mk Label.app [mk Label.prim [leaf Prim.label], Tm.var 0]
      if L = tT ∧ typeOf G Γ t = some B ∧ H0.map (Eqn.wk 1) = H ∧ (∀ h ∈ H0, h.Typed G Γ') ∧
          p0 E G Γ' H0 = some ⟨B, subst (mk Label.quote [leaf 0]) s,
              subst (mk Label.quote [leaf 0]) t⟩ ∧
          p1 E G Γ (⟨B, s, t⟩ :: H) =
            some ⟨B, subst suc (wkAt 1 1 s), subst suc (wkAt 1 1 t)⟩ then
        some ⟨B, subst lab (wkAt 1 1 s), subst lab (wkAt 1 1 t)⟩
      else none
    | [] => none
  -- a reference to a definition is the definition, weakened into the context
  | Rule.unfold, [(j, _)] =>
    E.defs[j.label]?.bind fun t ↦ (typeOf G Γ (mk Label.ref [j])).map fun A ↦
      ⟨A, mk Label.ref [j], Kernel.wk Γ.length t⟩
  -- the conditional at a quoted tree
  | Rule.condQuote, [(c, _), (a, _), (b, _)] => (typeOf G Γ a).bind fun A ↦
    if typeOf G Γ b = some A then some ⟨A, mk Label.cond [mk Label.quote [c], a, b],
        if c.label ≠ 0 then a else b⟩
    else none
  -- an instance of an axiom, each variable replaced by a term of its type
  | Rule.ax, (j, _) :: us => axioms[j.label]?.bind (·.cite G Γ (us.map Prod.fst))
  -- iteration reads the label of the tree it iterates over
  | Rule.iterLabel, [(A, _), (s, _), (z, _), (t, _)] =>
    if Ty.IsTy A ∧ typeOf G Γ s = some (tArrow A A) ∧ typeOf G Γ z = some A ∧
        typeOf G Γ t = some tT then
      some ⟨A, apps (mk Label.iter [A]) [s, z, t], apps (mk Label.iter [A]) [s, z,
          mk Label.app [mk Label.prim [leaf Prim.label], t]]⟩
    else none
  -- the conditional is the iteration of a constant function from its second branch
  | Rule.condIter, [(A, _), (c, _), (a, _), (b, _)] =>
    if Ty.IsTy A ∧ typeOf G Γ c = some tT ∧ typeOf G Γ a = some A ∧ typeOf G Γ b = some A then
      some ⟨A, mk Label.cond [c, a, b],
        apps (mk Label.iter [A]) [mk Label.lam [A, Kernel.wk 1 a], b, c]⟩
    else none
  -- an instance of a theorem, each variable replaced by a term of its type
  | Rule.thm, (j, _) :: us => E.thms[j.label]?.bind (·.cite G Γ (us.map Prod.fst))
  | _, _ => none

/-- One rule of the checker, by the label of a certificate's node. -/
def checkStep (l : ℕ) (cs : List (Tree × Chk)) : Chk :=
  if l < Rule.lcaseNil then checkCore l cs else checkMore l cs

/-- The checker: the conclusion of a certificate, in a program's definitions and global
environment, a context and a list of hypotheses, or nothing when the certificate does not
check. -/
def check (c : Tree) : Chk := RoseTree.para checkStep c

section Soundness

variable {G : List Glob} {Γ : Ctx} {H : List Eqn}

/-- A term has a type exactly when it has a denotation at that type. -/
theorem typeOf_eq_some {t A : Tree} : typeOf G Γ t = some A ↔ ∃ f, infer G Γ t = some ⟨A, f⟩ := by
  unfold typeOf
  constructor
  · intro h
    obtain ⟨⟨A', f⟩, hm, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨f, hm⟩
  · rintro ⟨f, hf⟩
    rw [hf]
    rfl

/-- A term has one denotation at a type. -/
theorem infer_unique {t A : Tree} {f g : Γ.den → Ty.den A} (hf : infer G Γ t = some ⟨A, f⟩)
    (hg : infer G Γ t = some ⟨A, g⟩) : f = g := by
  rw [hf] at hg
  exact eq_of_heq (Sigma.mk.inj_iff.mp (Option.some.inj hg)).2

/-- The denotations of both sides of a typed equation. -/
theorem Eqn.Typed.exists {q : Eqn} (h : q.Typed G Γ) :
    ∃ f g : Γ.den → Ty.den q.ty, infer G Γ q.lhs = some ⟨q.ty, f⟩ ∧
      infer G Γ q.rhs = some ⟨q.ty, g⟩ :=
  let ⟨f, hf⟩ := typeOf_eq_some.mp h.1
  let ⟨g, hg⟩ := typeOf_eq_some.mp h.2
  ⟨f, g, hf, hg⟩

/-- An equation that holds equates the values of its sides' denotations. -/
theorem Eqn.Holds.eq {q : Eqn} {e : Γ.den} {f g : Γ.den → Ty.den q.ty} (h : q.Holds G Γ e)
    (hf : infer G Γ q.lhs = some ⟨q.ty, f⟩) (hg : infer G Γ q.rhs = some ⟨q.ty, g⟩) :
    f e = g e := by
  obtain ⟨f', g', hf', hg', he⟩ := h
  rw [infer_unique hf hf', infer_unique hg hg']
  exact he

/-- A weakened equation holds where the equation holds below the added variables. -/
theorem Eqn.holds_wk (W : Ctx) {q : Eqn} {e : (W ++ Γ).den} (h : q.Holds G Γ (Ctx.drop W e)) :
    (q.wk W.length).Holds G (W ++ Γ) e := by
  obtain ⟨f, g, hf, hg, he⟩ := h
  exact ⟨f ∘ Ctx.drop W, g ∘ Ctx.drop W, infer_wk W hf, infer_wk W hg, he⟩

/-- A function type's parts read back. -/
theorem arrowParts_eq {F A B : Tree} (h : arrowParts F = some (A, B)) : F = tArrow A B := by
  unfold arrowParts at h
  split at h
  · split at h
    · cases h
      assumption
    · cases h
  · cases h

/-- A product type's parts read back. -/
theorem prodParts_eq {P A B : Tree} (h : prodParts P = some (A, B)) : P = tProd A B := by
  unfold prodParts at h
  split at h
  · split at h
    · cases h
      assumption
    · cases h
  · cases h

/-- A list type's element type read back. -/
theorem listParts_eq {L A : Tree} (h : listParts L = some A) : L = tList A := by
  unfold listParts at h
  split at h
  · split at h
    · cases h
      assumption
    · cases h
  · cases h

/-- The denotation of a map: the function's values at the list's elements. -/
theorem infer_mapBy {A B body xs : Tree} {g : Ty.den A → Γ.den → Ty.den B}
    {fxs : Γ.den → Ty.den (tList A)} (hA : Ty.IsTy A = true) (hB : Ty.IsTy B = true)
    (hb : infer G (tList B :: A :: Γ) body = some ⟨B, fun d ↦ g d.2.1 d.2.2⟩)
    (hxs : infer G Γ xs = some ⟨tList A, fxs⟩) :
    infer G Γ (mapBy A B body xs) =
      some ⟨tList B, fun e ↦ ((fxs e : List (Ty.den A)).map fun c ↦ g c e : List (Ty.den B))⟩ := by
  have hLB : Ty.IsTy (tList B) = true := hB
  have hr : infer G (tList B :: A :: Γ) (Tm.var 0) = some ⟨tList B, Prod.fst⟩ := by
    rw [infer_var]
    rfl
  have hl := infer_lam hA (infer_lam hLB (infer_cons hb hr))
  refine (infer_app (infer_app (infer_app (infer_foldr hA hLB) hl) (infer_nil hB)) hxs).trans
    (congrArg some (Sigma.ext rfl (heq_of_eq (funext fun e ↦ ?_))))
  change List.foldr (fun c r ↦ g c e :: r) [] (fxs e) = List.map (fun c ↦ g c e) (fxs e)
  exact List.map_eq_foldr.symm

/-- A typed hypothesis is valid. -/
theorem valid_hyp {q : Eqn} (hq : q ∈ H) (ht : q.Typed G Γ) : Valid G Γ H q :=
  let ⟨f, g, hf, hg⟩ := ht.exists
  ⟨f, g, hf, hg, fun _ hH ↦ (hH q hq).eq hf hg⟩

/-- Reflexivity. -/
theorem valid_refl {t A : Tree} (ht : typeOf G Γ t = some A) : Valid G Γ H ⟨A, t, t⟩ :=
  let ⟨f, hf⟩ := typeOf_eq_some.mp ht
  ⟨f, f, hf, hf, fun _ _ ↦ rfl⟩

/-- Symmetry. -/
theorem valid_symm {q : Eqn} (h : Valid G Γ H q) : Valid G Γ H ⟨q.ty, q.rhs, q.lhs⟩ :=
  let ⟨f, g, hf, hg, he⟩ := h
  ⟨g, f, hg, hf, fun e hH ↦ (he e hH).symm⟩

/-- Transitivity. -/
theorem valid_trans {q q' : Eqn} (h : Valid G Γ H q) (h' : Valid G Γ H q') (hty : q.ty = q'.ty)
    (hm : q.rhs = q'.lhs) : Valid G Γ H ⟨q.ty, q.lhs, q'.rhs⟩ := by
  obtain ⟨A, s, t⟩ := q
  obtain ⟨A', t', u⟩ := q'
  obtain rfl : A = A' := hty
  obtain rfl : t = t' := hm
  obtain ⟨f, g, hf, hg, he⟩ := h
  obtain ⟨f', g', hf', hg', he'⟩ := h'
  obtain rfl := infer_unique hg hf'
  exact ⟨f, g', hf, hg', fun e hH ↦ (he e hH).trans (he' e hH)⟩

/-- Congruence of application. -/
theorem valid_app {q q' : Eqn} {A B : Tree} (h : Valid G Γ H q) (h' : Valid G Γ H q')
    (hF : arrowParts q.ty = some (A, B)) (hx : q'.ty = A) :
    Valid G Γ H ⟨B, mk Label.app [q.lhs, q'.lhs], mk Label.app [q.rhs, q'.rhs]⟩ := by
  obtain ⟨F, s, s'⟩ := q
  obtain ⟨A', t, t'⟩ := q'
  obtain rfl := arrowParts_eq hF
  obtain rfl : A' = A := hx
  obtain ⟨f, g, hf, hg, he⟩ := h
  obtain ⟨f', g', hf', hg', he'⟩ := h'
  exact ⟨_, _, infer_app hf hf', infer_app hg hg', fun e hH ↦ by rw [he e hH, he' e hH]⟩

/-- Congruence of abstraction. -/
theorem valid_lam {A : Tree} {q : Eqn} (hA : Ty.IsTy A = true)
    (h : Valid G (A :: Γ) (H.map (Eqn.wk 1)) q) :
    Valid G Γ H ⟨tArrow A q.ty, mk Label.lam [A, q.lhs], mk Label.lam [A, q.rhs]⟩ := by
  obtain ⟨f, g, hf, hg, he⟩ := h
  refine ⟨_, _, infer_lam hA hf, infer_lam hA hg, fun e hH ↦ funext fun a ↦ he (a, e) ?_⟩
  intro h hmem
  obtain ⟨h0, h0mem, rfl⟩ := List.mem_map.mp hmem
  exact Eqn.holds_wk [A] (hH h0 h0mem)

/-- Congruence of pairing. -/
theorem valid_pair {q q' : Eqn} (h : Valid G Γ H q) (h' : Valid G Γ H q') :
    Valid G Γ H
      ⟨tProd q.ty q'.ty, mk Label.pair [q.lhs, q'.lhs], mk Label.pair [q.rhs, q'.rhs]⟩ := by
  obtain ⟨f, g, hf, hg, he⟩ := h
  obtain ⟨f', g', hf', hg', he'⟩ := h'
  exact ⟨_, _, infer_pair hf hf', infer_pair hg hg', fun e hH ↦ by rw [he e hH, he' e hH]⟩

/-- Congruence of the first projection. -/
theorem valid_fst {q : Eqn} {A B : Tree} (h : Valid G Γ H q) (hP : prodParts q.ty = some (A, B)) :
    Valid G Γ H ⟨A, mk Label.fst [q.lhs], mk Label.fst [q.rhs]⟩ := by
  obtain ⟨P, s, s'⟩ := q
  obtain rfl := prodParts_eq hP
  obtain ⟨f, g, hf, hg, he⟩ := h
  exact ⟨_, _, infer_fst hf, infer_fst hg, fun e hH ↦ by rw [he e hH]⟩

/-- Congruence of the second projection. -/
theorem valid_snd {q : Eqn} {A B : Tree} (h : Valid G Γ H q) (hP : prodParts q.ty = some (A, B)) :
    Valid G Γ H ⟨B, mk Label.snd [q.lhs], mk Label.snd [q.rhs]⟩ := by
  obtain ⟨P, s, s'⟩ := q
  obtain rfl := prodParts_eq hP
  obtain ⟨f, g, hf, hg, he⟩ := h
  exact ⟨_, _, infer_snd hf, infer_snd hg, fun e hH ↦ by rw [he e hH]⟩

/-- Congruence of the list of a head and a tail. -/
theorem valid_cons {q q' : Eqn} (h : Valid G Γ H q) (h' : Valid G Γ H q')
    (hl : q'.ty = tList q.ty) :
    Valid G Γ H ⟨q'.ty, mk Label.cons [q.lhs, q'.lhs], mk Label.cons [q.rhs, q'.rhs]⟩ := by
  obtain ⟨A, s, s'⟩ := q
  obtain ⟨L, t, t'⟩ := q'
  obtain rfl : L = tList A := hl
  obtain ⟨f, g, hf, hg, he⟩ := h
  obtain ⟨f', g', hf', hg', he'⟩ := h'
  exact ⟨_, _, infer_cons hf hf', infer_cons hg hg', fun e hH ↦ by rw [he e hH, he' e hH]⟩

/-- Congruence of the conditional. -/
theorem valid_if {q q' q'' : Eqn} (h : Valid G Γ H q) (h' : Valid G Γ H q')
    (h'' : Valid G Γ H q'') (hc : q.ty = tT) (hty : q''.ty = q'.ty) :
    Valid G Γ H
      ⟨q'.ty, mk Label.cond [q.lhs, q'.lhs, q''.lhs], mk Label.cond [q.rhs, q'.rhs, q''.rhs]⟩ := by
  obtain ⟨C, c, c'⟩ := q
  obtain ⟨A, a, a'⟩ := q'
  obtain ⟨A', b, b'⟩ := q''
  obtain rfl : C = tT := hc
  obtain rfl : A' = A := hty
  obtain ⟨f, g, hf, hg, he⟩ := h
  obtain ⟨f', g', hf', hg', he'⟩ := h'
  obtain ⟨f'', g'', hf'', hg'', he''⟩ := h''
  exact ⟨_, _, infer_if hf hf' hf'', infer_if hg hg' hg'', fun e hH ↦ by
    rw [he e hH, he' e hH, he'' e hH]⟩

/-- The β rule of functions. -/
theorem valid_beta {A a b B : Tree} (hA : Ty.IsTy A = true) (ha : typeOf G Γ a = some A)
    (hb : typeOf G (A :: Γ) b = some B) :
    Valid G Γ H ⟨B, mk Label.app [mk Label.lam [A, b], a], subst a b⟩ := by
  obtain ⟨fa, hfa⟩ := typeOf_eq_some.mp ha
  obtain ⟨fb, hfb⟩ := typeOf_eq_some.mp hb
  exact ⟨_, _, infer_app (infer_lam hA hfb) hfa, infer_subst hfa hfb, fun _ _ ↦ rfl⟩

/-- The η rule of functions. -/
theorem valid_eta {f F A B : Tree} (hf : typeOf G Γ f = some F) (hF : arrowParts F = some (A, B))
    (hA : Ty.IsTy A = true) :
    Valid G Γ H ⟨F, f, mk Label.lam [A, mk Label.app [Kernel.wk 1 f, Tm.var 0]]⟩ := by
  obtain rfl := arrowParts_eq hF
  obtain ⟨ff, hff⟩ := typeOf_eq_some.mp hf
  have hw : infer G (A :: Γ) (Kernel.wk 1 f) = some ⟨tArrow A B, ff ∘ Prod.snd⟩ := infer_wk [A] hff
  have hv : infer G (A :: Γ) (Tm.var 0) = some ⟨A, Prod.fst⟩ := by rw [infer_var]; rfl
  exact ⟨ff, _, hff, infer_lam hA (infer_app hw hv), fun _ _ ↦ rfl⟩

/-- The β rule of the first projection. -/
theorem valid_fstBeta {a b A B : Tree} (ha : typeOf G Γ a = some A) (hb : typeOf G Γ b = some B) :
    Valid G Γ H ⟨A, mk Label.fst [mk Label.pair [a, b]], a⟩ := by
  obtain ⟨fa, hfa⟩ := typeOf_eq_some.mp ha
  obtain ⟨fb, hfb⟩ := typeOf_eq_some.mp hb
  exact ⟨_, fa, infer_fst (infer_pair hfa hfb), hfa, fun _ _ ↦ rfl⟩

/-- The β rule of the second projection. -/
theorem valid_sndBeta {a b A B : Tree} (ha : typeOf G Γ a = some A) (hb : typeOf G Γ b = some B) :
    Valid G Γ H ⟨B, mk Label.snd [mk Label.pair [a, b]], b⟩ := by
  obtain ⟨fa, hfa⟩ := typeOf_eq_some.mp ha
  obtain ⟨fb, hfb⟩ := typeOf_eq_some.mp hb
  exact ⟨_, fb, infer_snd (infer_pair hfa hfb), hfb, fun _ _ ↦ rfl⟩

/-- The η rule of pairs. -/
theorem valid_pairEta {p P A B : Tree} (hp : typeOf G Γ p = some P)
    (hP : prodParts P = some (A, B)) :
    Valid G Γ H ⟨P, mk Label.pair [mk Label.fst [p], mk Label.snd [p]], p⟩ := by
  obtain rfl := prodParts_eq hP
  obtain ⟨fp, hfp⟩ := typeOf_eq_some.mp hp
  exact ⟨_, fp, infer_pair (infer_fst hfp) (infer_snd hfp), hfp, fun _ _ ↦ rfl⟩

/-- The η rule of the unit type. -/
theorem valid_unitEta {t : Tree} (ht : typeOf G Γ t = some tUnit) :
    Valid G Γ H ⟨tUnit, t, mk Label.unit []⟩ := by
  obtain ⟨ft, hft⟩ := typeOf_eq_some.mp ht
  exact ⟨ft, _, hft, infer_unit G Γ, fun _ _ ↦ rfl⟩

/-- A list literal denotes its list of trees. -/
theorem infer_listLit (G : List Glob) (Γ : Ctx) :
    ∀ xs : List Tree, infer G Γ (listLit xs) = some ⟨tList tT, fun _ ↦ xs⟩ :=
  List.rec (infer_nil rfl) fun x _ ih ↦ infer_cons (infer_quote G Γ x) ih

/-- A closed term of the type of trees or of lists of trees is the literal of its value. -/
theorem valid_lit {H : List Eqn} {t v : Tree} {m : Meaning []} (ht : infer G [] t = some m)
    (hv : lit? m = some v) : Valid G [] H ⟨m.1, t, v⟩ := by
  obtain ⟨A, f⟩ := m
  simp only [lit?] at hv
  split at hv
  · rename_i hA
    cases hv
    subst hA
    exact ⟨f, _, ht, infer_quote G [] (f ()), fun _ _ ↦ rfl⟩
  · split at hv
    · rename_i hA
      cases hv
      subst hA
      exact ⟨f, _, ht, infer_listLit G [] (f ()), fun _ _ ↦ rfl⟩
    · cases hv

/-- Weakening by one variable. -/
theorem valid_weaken {A : Tree} {q : Eqn} (h : Valid G Γ [] q) : Valid G (A :: Γ) H (q.wk 1) := by
  obtain ⟨f, g, hf, hg, he⟩ := h
  exact ⟨f ∘ Prod.snd, g ∘ Prod.snd, infer_wk [A] hf, infer_wk [A] hg,
    fun e _ ↦ he e.2 fun _ hx ↦ absurd hx List.not_mem_nil⟩

/-- Cut: a hypothesis proved is discharged. -/
theorem valid_cut {h q : Eqn} (hh : Valid G Γ H h) (hq : Valid G Γ (h :: H) q) : Valid G Γ H q := by
  obtain ⟨f, g, hf, hg, he⟩ := hh
  obtain ⟨f', g', hf', hg', he'⟩ := hq
  refine ⟨f', g', hf', hg', fun e hH ↦ he' e ?_⟩
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact ⟨f, g, hf, hg, he e hH⟩
  · exact hH x hx

/-- Instantiation of the innermost variable by a term. -/
theorem valid_inst {u A : Tree} {q : Eqn} (hu : typeOf G Γ u = some A)
    (h : Valid G (A :: Γ) (H.map (Eqn.wk 1)) q) :
    Valid G Γ H ⟨q.ty, subst u q.lhs, subst u q.rhs⟩ := by
  obtain ⟨fu, hfu⟩ := typeOf_eq_some.mp hu
  obtain ⟨f, g, hf, hg, he⟩ := h
  refine ⟨_, _, infer_subst hfu hf, infer_subst hfu hg, fun e hH ↦ he (fu e, e) ?_⟩
  intro x hx
  obtain ⟨h0, h0mem, rfl⟩ := List.mem_map.mp hx
  exact Eqn.holds_wk [A] (hH h0 h0mem)

/-- The right fold of lists at the empty list. -/
theorem valid_foldrNil {A B g z : Tree} (hA : Ty.IsTy A = true) (hB : Ty.IsTy B = true)
    (hg : typeOf G Γ g = some (tArrow A (tArrow B B))) (hz : typeOf G Γ z = some B) :
    Valid G Γ H ⟨B, apps (mk Label.foldr [A, B]) [g, z, mk Label.nil [A]], z⟩ := by
  obtain ⟨fg, hfg⟩ := typeOf_eq_some.mp hg
  obtain ⟨fz, hfz⟩ := typeOf_eq_some.mp hz
  exact ⟨_, fz, infer_app (infer_app (infer_app (infer_foldr hA hB) hfg) hfz) (infer_nil hA), hfz,
    fun _ _ ↦ rfl⟩

/-- The right fold of lists at a list of a head and a tail. -/
theorem valid_foldrCons {A B g z x xs : Tree} (hA : Ty.IsTy A = true) (hB : Ty.IsTy B = true)
    (hg : typeOf G Γ g = some (tArrow A (tArrow B B))) (hz : typeOf G Γ z = some B)
    (hx : typeOf G Γ x = some A) (hxs : typeOf G Γ xs = some (tList A)) :
    Valid G Γ H ⟨B, apps (mk Label.foldr [A, B]) [g, z, mk Label.cons [x, xs]],
      apps g [x, apps (mk Label.foldr [A, B]) [g, z, xs]]⟩ := by
  obtain ⟨fg, hfg⟩ := typeOf_eq_some.mp hg
  obtain ⟨fz, hfz⟩ := typeOf_eq_some.mp hz
  obtain ⟨fx, hfx⟩ := typeOf_eq_some.mp hx
  obtain ⟨fxs, hfxs⟩ := typeOf_eq_some.mp hxs
  have hc := infer_app (infer_app (infer_foldr (G := G) (Γ := Γ) hA hB) hfg) hfz
  exact ⟨_, _, infer_app hc (infer_cons hfx hfxs),
    infer_app (infer_app hfg hfx) (infer_app hc hfxs), fun _ _ ↦ rfl⟩

/-- A term weakened below bound variables denotes its denotation at the values below the
inserted variables. -/
theorem infer_wkAt (Θ W : Ctx) {t : Tree} {m : Meaning (Θ ++ Γ)}
    (h : infer G (Θ ++ Γ) t = some m) :
    infer G (Θ ++ (W ++ Γ)) (wkAt Θ.length W.length t) =
      some ⟨m.1, m.2 ∘ Ctx.ext (Ctx.drop W) Θ⟩ :=
  infer_trav (Γ := Γ) (Δ := W ++ Γ) (Ctx.drop W) (wkVar W.length)
    (fun Θ i A f hf ↦ by rw [wkVar, infer_var]; exact Ctx.var_insert W Γ Θ i A f hf) t Θ m h

/-- Induction on the innermost variable, a list. -/
theorem valid_indList {Γ' : Ctx} {A B s t : Tree} (hA : Ty.IsTy A = true)
    (hs : typeOf G (tList A :: Γ') s = some B) (ht : typeOf G (tList A :: Γ') t = some B)
    (hH : (H.map Eqn.lower).map (Eqn.wk 1) = H) (hT : ∀ h ∈ H.map Eqn.lower, h.Typed G Γ')
    (h0 : Valid G Γ' (H.map Eqn.lower) ⟨B, subst (mk Label.nil [A]) s, subst (mk Label.nil [A]) t⟩)
    (h1 : Valid G (tList A :: A :: Γ')
      (⟨B, wkAt 1 1 s, wkAt 1 1 t⟩ :: (H.map Eqn.lower).map (Eqn.wk 2))
      ⟨B, subst (mk Label.cons [Tm.var 1, Tm.var 0]) (wkAt 1 2 s),
        subst (mk Label.cons [Tm.var 1, Tm.var 0]) (wkAt 1 2 t)⟩) :
    Valid G (tList A :: Γ') H ⟨B, s, t⟩ := by
  obtain ⟨fs, hfs⟩ := typeOf_eq_some.mp hs
  obtain ⟨ft, hft⟩ := typeOf_eq_some.mp ht
  refine ⟨fs, ft, hfs, hft, fun ⟨ys, e⟩ hHe ↦ ?_⟩
  -- the hypotheses hold below the list
  have hH0 : ∀ h ∈ H.map Eqn.lower, h.Holds G Γ' e := by
    intro h hmem
    obtain ⟨f0, g0, hf0, hg0⟩ := (hT h hmem).exists
    have hw : h.wk 1 ∈ H := hH ▸ List.mem_map_of_mem hmem
    exact ⟨f0, g0, hf0, hg0, (hHe _ hw).eq (infer_wk [tList A] hf0) (infer_wk [tList A] hg0)⟩
  -- the denotations of the sides of the premises
  obtain ⟨f0, g0, hf0, hg0, he0⟩ := h0
  obtain rfl := infer_unique hf0 (infer_subst (infer_nil hA) hfs)
  obtain rfl := infer_unique hg0 (infer_subst (infer_nil hA) hft)
  have hc : infer G (tList A :: A :: Γ') (mk Label.cons [Tm.var 1, Tm.var 0]) =
      some ⟨tList A, fun d ↦ d.2.1 :: d.1⟩ :=
    infer_cons (by rw [infer_var]; rfl) (by rw [infer_var]; rfl)
  obtain ⟨f1, g1, hf1, hg1, he1⟩ := h1
  obtain rfl := infer_unique hf1 (infer_subst hc (infer_wkAt [tList A] [tList A, A] hfs))
  obtain rfl := infer_unique hg1 (infer_subst hc (infer_wkAt [tList A] [tList A, A] hft))
  refine List.rec (motive := fun ys ↦ fs (ys, e) = ft (ys, e)) (he0 e hH0) (fun x ys ih ↦ ?_) ys
  refine he1 (ys, (x, e)) fun h hmem ↦ ?_
  rcases List.mem_cons.mp hmem with rfl | hmem
  · exact ⟨_, _, infer_wkAt [tList A] [A] hfs, infer_wkAt [tList A] [A] hft, ih⟩
  · obtain ⟨h', h'mem, rfl⟩ := List.mem_map.mp hmem
    exact Eqn.holds_wk [tList A, A] (hH0 h' h'mem)

/-- A child of a node paired with its result by a paramorphism is one of the node's children,
and its result is the paramorphism's at it. -/
theorem mem_of_map_para {β : Type} {f : ℕ → List (Tree × β) → β} {cs : List Tree}
    {ps : List (Tree × β)} {c : Tree} {s : β} (h : cs.map (fun c ↦ (c, RoseTree.para f c)) = ps)
    (hm : (c, s) ∈ ps) : c ∈ cs ∧ s = RoseTree.para f c := by
  subst h
  obtain ⟨c', hc', he⟩ := List.mem_map.mp hm
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
  exact ⟨hc', rfl⟩

/-- The conclusion of each rule of {lit}`checkCore` is valid when its premises' conclusions are. -/
theorem checkCore_sound {l : ℕ} {cs : List Tree} {E : Env} {G : List Glob} {Γ : Ctx}
    {H : List Eqn} {q : Eqn}
    (ih : ∀ c ∈ cs, ∀ (E : Env) (G : List Glob) (Γ : Ctx) (H : List Eqn) (q : Eqn),
      E.Sound G → check c E G Γ H = some q → Valid G Γ H q) (hE : E.Sound G)
    (h : checkCore l (cs.map fun c ↦ (c, RoseTree.para checkStep c)) E G Γ H = some q) :
    Valid G Γ H q := by
  simp only [checkCore] at h
  split at h
  case h_1 i si heq =>
    obtain ⟨q', hq', h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · cases h
      exact valid_hyp (List.mem_of_getElem? hq') ‹_›
    · cases h
  case h_2 t st heq =>
    obtain ⟨A, hA, rfl⟩ := Option.map_eq_some_iff.mp h
    exact valid_refl hA
  case h_3 cp p heq =>
    obtain ⟨hc, rfl⟩ := mem_of_map_para (c := cp) (s := p) heq (by simp)
    obtain ⟨q', hq', rfl⟩ := Option.map_eq_some_iff.mp h
    exact valid_symm (ih cp hc E G Γ H q' hE hq')
  case h_4 cp p cp' p' heq =>
    obtain ⟨hc, rfl⟩ := mem_of_map_para (c := cp) (s := p) heq (by simp)
    obtain ⟨hc', rfl⟩ := mem_of_map_para (c := cp') (s := p') heq (by simp)
    obtain ⟨q1, h1, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨q2, h2, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · rename_i hcond
      cases h
      exact valid_trans (ih cp hc E G Γ H q1 hE h1) (ih cp' hc' E G Γ H q2 hE h2) hcond.1 hcond.2
    · cases h
  case h_5 cp p cp' p' heq =>
    obtain ⟨hc, rfl⟩ := mem_of_map_para (c := cp) (s := p) heq (by simp)
    obtain ⟨hc', rfl⟩ := mem_of_map_para (c := cp') (s := p') heq (by simp)
    obtain ⟨q1, h1, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨q2, h2, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨⟨A, B⟩, hAB, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · rename_i hx
      cases h
      exact valid_app (ih cp hc E G Γ H q1 hE h1) (ih cp' hc' E G Γ H q2 hE h2) hAB hx
    · cases h
  case h_6 A sA cp p heq =>
    obtain ⟨hc, rfl⟩ := mem_of_map_para (c := cp) (s := p) heq (by simp)
    split at h
    · rename_i hA
      obtain ⟨q', hq', rfl⟩ := Option.map_eq_some_iff.mp h
      exact valid_lam hA (ih cp hc E G (A :: Γ) (H.map (Eqn.wk 1)) q' hE hq')
    · cases h
  case h_7 cp p cp' p' heq =>
    obtain ⟨hc, rfl⟩ := mem_of_map_para (c := cp) (s := p) heq (by simp)
    obtain ⟨hc', rfl⟩ := mem_of_map_para (c := cp') (s := p') heq (by simp)
    obtain ⟨q1, h1, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨q2, h2, rfl⟩ := Option.map_eq_some_iff.mp h
    exact valid_pair (ih cp hc E G Γ H q1 hE h1) (ih cp' hc' E G Γ H q2 hE h2)
  case h_8 cp p heq =>
    obtain ⟨hc, rfl⟩ := mem_of_map_para (c := cp) (s := p) heq (by simp)
    obtain ⟨q1, h1, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨⟨A, B⟩, hAB, rfl⟩ := Option.map_eq_some_iff.mp h
    exact valid_fst (ih cp hc E G Γ H q1 hE h1) hAB
  case h_9 cp p heq =>
    obtain ⟨hc, rfl⟩ := mem_of_map_para (c := cp) (s := p) heq (by simp)
    obtain ⟨q1, h1, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨⟨A, B⟩, hAB, rfl⟩ := Option.map_eq_some_iff.mp h
    exact valid_snd (ih cp hc E G Γ H q1 hE h1) hAB
  case h_10 cp p cp' p' heq =>
    obtain ⟨hc, rfl⟩ := mem_of_map_para (c := cp) (s := p) heq (by simp)
    obtain ⟨hc', rfl⟩ := mem_of_map_para (c := cp') (s := p') heq (by simp)
    obtain ⟨q1, h1, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨q2, h2, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · rename_i hl
      cases h
      exact valid_cons (ih cp hc E G Γ H q1 hE h1) (ih cp' hc' E G Γ H q2 hE h2) hl
    · cases h
  case h_11 cp p cp' p' cp'' p'' heq =>
    obtain ⟨hc, rfl⟩ := mem_of_map_para (c := cp) (s := p) heq (by simp)
    obtain ⟨hc', rfl⟩ := mem_of_map_para (c := cp') (s := p') heq (by simp)
    obtain ⟨hc'', rfl⟩ := mem_of_map_para (c := cp'') (s := p'') heq (by simp)
    obtain ⟨q1, h1, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨q2, h2, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨q3, h3, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · rename_i hcond
      cases h
      exact valid_if (ih cp hc E G Γ H q1 hE h1) (ih cp' hc' E G Γ H q2 hE h2)
        (ih cp'' hc'' E G Γ H q3 hE h3) hcond.1 hcond.2
    · cases h
  case h_12 A sA b sb a sa heq =>
    split at h
    · rename_i hcond
      obtain ⟨B, hB, rfl⟩ := Option.map_eq_some_iff.mp h
      exact valid_beta hcond.1 hcond.2 hB
    · cases h
  case h_13 f sf heq =>
    obtain ⟨F, hF, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨⟨A, B⟩, hAB, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · rename_i hA
      cases h
      exact valid_eta hF hAB hA
    · cases h
  case h_14 a sa b sb heq =>
    obtain ⟨A, hA, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨B, hB, rfl⟩ := Option.map_eq_some_iff.mp h
    exact valid_fstBeta hA hB
  case h_15 a sa b sb heq =>
    obtain ⟨A, hA, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨B, hB, rfl⟩ := Option.map_eq_some_iff.mp h
    exact valid_sndBeta hA hB
  case h_16 p sp heq =>
    obtain ⟨P, hP, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨⟨A, B⟩, hAB, rfl⟩ := Option.map_eq_some_iff.mp h
    exact valid_pairEta hP hAB
  case h_17 t st heq =>
    split at h
    · rename_i ht
      cases h
      exact valid_unitEta ht
    · cases h
  case h_18 k sk as heq =>
    split at h
    · split at h
      · obtain ⟨m, hm, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.mp h
        exact valid_lit hm hv
      · cases h
    · cases h
  case h_19 cp p heq =>
    obtain ⟨hc, rfl⟩ := mem_of_map_para (c := cp) (s := p) heq (by simp)
    split at h
    · rename_i A Γ'
      obtain ⟨q', hq', rfl⟩ := Option.map_eq_some_iff.mp h
      exact valid_weaken (ih cp hc E G Γ' [] q' hE hq')
    · cases h
  case h_20 cp p cp' p' heq =>
    obtain ⟨hc, rfl⟩ := mem_of_map_para (c := cp) (s := p) heq (by simp)
    obtain ⟨hc', rfl⟩ := mem_of_map_para (c := cp') (s := p') heq (by simp)
    obtain ⟨hq, hq1, h⟩ := Option.bind_eq_some_iff.mp h
    exact valid_cut (ih cp hc E G Γ H hq hE hq1) (ih cp' hc' E G Γ (hq :: H) q hE h)
  case h_21 u su cp p heq =>
    obtain ⟨hc, rfl⟩ := mem_of_map_para (c := cp) (s := p) heq (by simp)
    obtain ⟨A, hA, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨q', hq', rfl⟩ := Option.map_eq_some_iff.mp h
    exact valid_inst hA (ih cp hc E G (A :: Γ) (H.map (Eqn.wk 1)) q' hE hq')
  case h_22 A sA B sB g sg z sz heq =>
    split at h
    · rename_i hcond
      cases h
      exact valid_foldrNil hcond.1 hcond.2.1 hcond.2.2.1 hcond.2.2.2
    · cases h
  case h_23 A sA B sB g sg z sz x sx xs sxs heq =>
    split at h
    · rename_i hcond
      cases h
      obtain ⟨hA, hB, hg, hz, hx, hxs⟩ := hcond
      exact valid_foldrCons hA hB hg hz hx hxs
    · cases h
  case h_24 s ss t st cp0 p0 cp1 p1 heq =>
    obtain ⟨hc0, rfl⟩ := mem_of_map_para (c := cp0) (s := p0) heq (by simp)
    obtain ⟨hc1, rfl⟩ := mem_of_map_para (c := cp1) (s := p1) heq (by simp)
    split at h
    · rename_i L Γ'
      obtain ⟨A, hL, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨B, hB, h⟩ := Option.bind_eq_some_iff.mp h
      obtain rfl := listParts_eq hL
      split at h
      · rename_i hcond
        cases h
        obtain ⟨hA, ht, hH, hT, hp0, hp1⟩ := hcond
        exact valid_indList hA hB ht hH hT (ih cp0 hc0 _ _ _ _ _ hE hp0)
          (ih cp1 hc1 _ _ _ _ _ hE hp1)
      · cases h
    · cases h
  case h_25 => cases h

/-- Case analysis of lists at the empty list. -/
theorem valid_lcaseNil {A B n c : Tree} (hA : Ty.IsTy A = true) (hB : Ty.IsTy B = true)
    (hn : typeOf G Γ n = some B) (hc : typeOf G Γ c = some (tArrow A (tArrow (tList A) B))) :
    Valid G Γ H ⟨B, apps (mk Label.lcase [A, B]) [mk Label.nil [A], n, c], n⟩ := by
  obtain ⟨fn, hfn⟩ := typeOf_eq_some.mp hn
  obtain ⟨fc, hfc⟩ := typeOf_eq_some.mp hc
  exact ⟨_, fn, infer_app (infer_app (infer_app (infer_lcase hA hB) (infer_nil hA)) hfn) hfc, hfn,
    fun _ _ ↦ rfl⟩

/-- Case analysis of lists at a list of a head and a tail. -/
theorem valid_lcaseCons {A B x xs n c : Tree} (hA : Ty.IsTy A = true) (hB : Ty.IsTy B = true)
    (hn : typeOf G Γ n = some B) (hc : typeOf G Γ c = some (tArrow A (tArrow (tList A) B)))
    (hx : typeOf G Γ x = some A) (hxs : typeOf G Γ xs = some (tList A)) :
    Valid G Γ H
      ⟨B, apps (mk Label.lcase [A, B]) [mk Label.cons [x, xs], n, c], apps c [x, xs]⟩ := by
  obtain ⟨fn, hfn⟩ := typeOf_eq_some.mp hn
  obtain ⟨fc, hfc⟩ := typeOf_eq_some.mp hc
  obtain ⟨fx, hfx⟩ := typeOf_eq_some.mp hx
  obtain ⟨fxs, hfxs⟩ := typeOf_eq_some.mp hxs
  exact ⟨_, _,
    infer_app (infer_app (infer_app (infer_lcase hA hB) (infer_cons hfx hfxs)) hfn) hfc,
    infer_app (infer_app hfc hfx) hfxs, fun _ _ ↦ rfl⟩

/-- Iteration at the label zero. -/
theorem valid_iterZero {A s z : Tree} (hA : Ty.IsTy A = true)
    (hs : typeOf G Γ s = some (tArrow A A)) (hz : typeOf G Γ z = some A) :
    Valid G Γ H ⟨A, apps (mk Label.iter [A]) [s, z, mk Label.quote [leaf 0]], z⟩ := by
  obtain ⟨fs, hfs⟩ := typeOf_eq_some.mp hs
  obtain ⟨fz, hfz⟩ := typeOf_eq_some.mp hz
  exact ⟨_, fz, infer_app (infer_app (infer_app (infer_iter hA) hfs) hfz) (infer_quote G Γ _), hfz,
    fun _ _ ↦ rfl⟩

/-- Iteration at the successor of a label. -/
theorem valid_iterSucc {A s z n : Tree} (hA : Ty.IsTy A = true)
    (hs : typeOf G Γ s = some (tArrow A A)) (hz : typeOf G Γ z = some A)
    (hn : typeOf G Γ n = some tT) :
    Valid G Γ H
      ⟨A, apps (mk Label.iter [A]) [s, z,
          apps (mk Label.prim [leaf Prim.add]) [n, mk Label.quote [leaf 1]]],
        mk Label.app [s, apps (mk Label.iter [A]) [s, z, n]]⟩ := by
  obtain ⟨fs, hfs⟩ := typeOf_eq_some.mp hs
  obtain ⟨fz, hfz⟩ := typeOf_eq_some.mp hz
  obtain ⟨fn, hfn⟩ := typeOf_eq_some.mp hn
  have hi := infer_app (infer_app (infer_iter (G := G) (Γ := Γ) hA) hfs) hfz
  have hsucc := infer_app (infer_app (infer_add G Γ) hfn) (infer_quote G Γ (leaf 1))
  exact ⟨_, _, infer_app hi hsucc, infer_app hfs (infer_app hi hfn), fun _ _ ↦ rfl⟩

/-- The fold of trees at a node. -/
theorem valid_foldNode {A f x xs : Tree} (hA : Ty.IsTy A = true)
    (hf : typeOf G Γ f = some (tArrow tT (tArrow (tList A) A))) (hx : typeOf G Γ x = some tT)
    (hxs : typeOf G Γ xs = some (tList tT)) :
    Valid G Γ H ⟨A, apps (mk Label.fold [A]) [f, apps (mk Label.prim [leaf Prim.node]) [x, xs]],
      apps f [mk Label.app [mk Label.prim [leaf Prim.label], x],
        mapBy tT A (apps (mk Label.fold [A]) [Kernel.wk 2 f, Tm.var 1]) xs]⟩ := by
  obtain ⟨ff, hff⟩ := typeOf_eq_some.mp hf
  obtain ⟨fx, hfx⟩ := typeOf_eq_some.mp hx
  obtain ⟨fxs, hfxs⟩ := typeOf_eq_some.mp hxs
  have hnode := infer_app (infer_app (infer_nodePrim G Γ) hfx) hfxs
  have hlhs := infer_app (infer_app (infer_fold hA) hff) hnode
  have hw : infer G (tList A :: tT :: Γ) (Kernel.wk 2 f) =
      some ⟨_, ff ∘ Ctx.drop [tList A, tT]⟩ := infer_wk [tList A, tT] hff
  have hv : infer G (tList A :: tT :: Γ) (Tm.var 1) = some ⟨tT, fun d ↦ d.2.1⟩ := by
    rw [infer_var]
    rfl
  have hbody := infer_app (infer_app (infer_fold hA) hw) hv
  have hmap := infer_mapBy (g := fun c e ↦ foldDen A (ff e) c) (rfl : Ty.IsTy tT = true) hA hbody
    hfxs
  have hrhs := infer_app (infer_app hff (infer_app (infer_label G Γ) hfx)) hmap
  exact ⟨_, _, hlhs, hrhs, fun e _ ↦
    RoseTree.elim_node (fun l rs ↦ ff e (leaf l) rs) (fx e : Tree).label (fxs e)⟩

/-- Induction on the innermost variable, a tree, under the hypothesis for its children. -/
theorem valid_indTree {Γ' : Ctx} {B s t : Tree} (hB : Ty.IsTy B = true)
    (hs : typeOf G (tT :: Γ') s = some B) (ht : typeOf G (tT :: Γ') t = some B)
    (hH : (H.map Eqn.lower).map (Eqn.wk 1) = H) (hT : ∀ h ∈ H.map Eqn.lower, h.Typed G Γ')
    (h1 : Valid G (tList tT :: tT :: Γ')
      (⟨tList B, mapBy tT B (subst (Tm.var 1) (wkAt 1 4 s)) (Tm.var 0),
        mapBy tT B (subst (Tm.var 1) (wkAt 1 4 t)) (Tm.var 0)⟩ ::
          (H.map Eqn.lower).map (Eqn.wk 2))
      ⟨B, subst (apps (mk Label.prim [leaf Prim.node]) [Tm.var 1, Tm.var 0]) (wkAt 1 2 s),
        subst (apps (mk Label.prim [leaf Prim.node]) [Tm.var 1, Tm.var 0]) (wkAt 1 2 t)⟩) :
    Valid G (tT :: Γ') H ⟨B, s, t⟩ := by
  obtain ⟨fs, hfs⟩ := typeOf_eq_some.mp hs
  obtain ⟨ft, hft⟩ := typeOf_eq_some.mp ht
  refine ⟨fs, ft, hfs, hft, fun ⟨τ, e⟩ hHe ↦ ?_⟩
  have hH0 : ∀ h ∈ H.map Eqn.lower, h.Holds G Γ' e := by
    intro h hmem
    obtain ⟨f0, g0, hf0, hg0⟩ := (hT h hmem).exists
    have hw : h.wk 1 ∈ H := hH ▸ List.mem_map_of_mem hmem
    exact ⟨f0, g0, hf0, hg0, (hHe _ hw).eq (infer_wk [tT] hf0) (infer_wk [tT] hg0)⟩
  have hnd : infer G (tList tT :: tT :: Γ')
      (apps (mk Label.prim [leaf Prim.node]) [Tm.var 1, Tm.var 0]) =
      some ⟨tT, fun d ↦ Const.node d.2.1 d.1⟩ :=
    infer_app (infer_app (infer_nodePrim _ _) (by rw [infer_var]; rfl)) (by rw [infer_var]; rfl)
  obtain ⟨f1, g1, hf1, hg1, he1⟩ := h1
  obtain rfl := infer_unique hf1 (infer_subst hnd (infer_wkAt [tT] [tList tT, tT] hfs))
  obtain rfl := infer_unique hg1 (infer_subst hnd (infer_wkAt [tT] [tList tT, tT] hft))
  have hv1 : infer G (tList B :: tT :: tList tT :: tT :: Γ') (Tm.var 1) =
      some ⟨tT, fun d ↦ d.2.1⟩ := by
    rw [infer_var]
    rfl
  have hv0 : infer G (tList tT :: tT :: Γ') (Tm.var 0) = some ⟨tList tT, Prod.fst⟩ := by
    rw [infer_var]
    rfl
  have hms := infer_mapBy (g := fun c (d : Ctx.den (tList tT :: tT :: Γ')) ↦ fs (c, d.2.2))
    (rfl : Ty.IsTy tT = true) hB
    (infer_subst hv1 (infer_wkAt [tT] [tList B, tT, tList tT, tT] hfs)) hv0
  have hmt := infer_mapBy (g := fun c (d : Ctx.den (tList tT :: tT :: Γ')) ↦ ft (c, d.2.2))
    (rfl : Ty.IsTy tT = true) hB
    (infer_subst hv1 (infer_wkAt [tT] [tList B, tT, tList tT, tT] hft)) hv0
  refine RoseTree.ind (P := fun τ ↦ fs (τ, e) = ft (τ, e)) (fun a cs ihc ↦ ?_) τ
  refine he1 (cs, (leaf a, e)) fun h hmem ↦ ?_
  rcases List.mem_cons.mp hmem with rfl | hmem
  · exact ⟨_, _, hms, hmt, List.map_congr_left ihc⟩
  · obtain ⟨h', h'mem, rfl⟩ := List.mem_map.mp hmem
    exact Eqn.holds_wk [tList tT, tT] (hH0 h' h'mem)

/-- Induction on the label of the innermost variable, a tree. -/
theorem valid_indLabel {Γ' : Ctx} {B s t : Tree}
    (hs : typeOf G (tT :: Γ') s = some B) (ht : typeOf G (tT :: Γ') t = some B)
    (hH : (H.map Eqn.lower).map (Eqn.wk 1) = H) (hT : ∀ h ∈ H.map Eqn.lower, h.Typed G Γ')
    (h0 : Valid G Γ' (H.map Eqn.lower)
      ⟨B, subst (mk Label.quote [leaf 0]) s, subst (mk Label.quote [leaf 0]) t⟩)
    (h1 : Valid G (tT :: Γ') (⟨B, s, t⟩ :: H)
      ⟨B, subst (apps (mk Label.prim [leaf Prim.add]) [Tm.var 0,
          mk Label.quote [leaf 1]]) (wkAt 1 1 s),
        subst (apps (mk Label.prim [leaf Prim.add]) [Tm.var 0,
            mk Label.quote [leaf 1]]) (wkAt 1 1 t)⟩) :
    Valid G (tT :: Γ') H
      ⟨B, subst (mk Label.app [mk Label.prim [leaf Prim.label], Tm.var 0]) (wkAt 1 1 s),
        subst (mk Label.app [mk Label.prim [leaf Prim.label], Tm.var 0]) (wkAt 1 1 t)⟩ := by
  obtain ⟨fs, hfs⟩ := typeOf_eq_some.mp hs
  obtain ⟨ft, hft⟩ := typeOf_eq_some.mp ht
  have hv0 : infer G (tT :: Γ') (Tm.var 0) = some ⟨tT, Prod.fst⟩ := by
    rw [infer_var]
    rfl
  have hlab := infer_app (infer_label G (tT :: Γ')) hv0
  have hsuc :=
    infer_app (infer_app (infer_add G (tT :: Γ')) hv0) (infer_quote G (tT :: Γ') (leaf 1))
  refine ⟨_, _, infer_subst hlab (infer_wkAt [tT] [tT] hfs),
    infer_subst hlab (infer_wkAt [tT] [tT] hft), fun ⟨n, e⟩ hHe ↦ ?_⟩
  have hH0 : ∀ h ∈ H.map Eqn.lower, h.Holds G Γ' e := by
    intro h hmem
    obtain ⟨f0, g0, hf0, hg0⟩ := (hT h hmem).exists
    have hw : h.wk 1 ∈ H := hH ▸ List.mem_map_of_mem hmem
    exact ⟨f0, g0, hf0, hg0, (hHe _ hw).eq (infer_wk [tT] hf0) (infer_wk [tT] hg0)⟩
  obtain ⟨f0, g0, hf0, hg0, he0⟩ := h0
  obtain rfl := infer_unique hf0 (infer_subst (infer_quote G Γ' (leaf 0)) hfs)
  obtain rfl := infer_unique hg0 (infer_subst (infer_quote G Γ' (leaf 0)) hft)
  obtain ⟨f1, g1, hf1, hg1, he1⟩ := h1
  obtain rfl := infer_unique hf1 (infer_subst hsuc (infer_wkAt [tT] [tT] hfs))
  obtain rfl := infer_unique hg1 (infer_subst hsuc (infer_wkAt [tT] [tT] hft))
  refine Nat.rec (motive := fun k ↦ fs (leaf k, e) = ft (leaf k, e)) (he0 e hH0)
    (fun k ih ↦ ?_) n.label
  refine he1 (leaf k, e) fun h hmem ↦ ?_
  rcases List.mem_cons.mp hmem with rfl | hmem
  · exact ⟨fs, ft, hfs, hft, ih⟩
  · rw [← hH] at hmem
    obtain ⟨h', h'mem, rfl⟩ := List.mem_map.mp hmem
    exact Eqn.holds_wk [tT] (hH0 h' h'mem)

/-- A reference to a definition is the definition, weakened into the context. -/
theorem valid_unfold {E : Env} {j t A : Tree} (hE : E.Sound G) (ht : E.defs[j.label]? = some t)
    (hA : typeOf G Γ (mk Label.ref [j]) = some A) :
    Valid G Γ H ⟨A, mk Label.ref [j], Kernel.wk Γ.length t⟩ := by
  have href : infer G Γ (mk Label.ref [j]) = G[j.label]?.map constant := by
    simp only [mk, infer_node, List.map_cons, List.map_nil, inferStep]
  obtain ⟨fr, hfr⟩ := typeOf_eq_some.mp hA
  rw [href] at hfr
  obtain ⟨⟨A', v⟩, hg, hgc⟩ := Option.map_eq_some_iff.mp hfr
  obtain ⟨rfl, hv⟩ := Sigma.mk.inj_iff.mp hgc
  obtain rfl := eq_of_heq hv
  obtain ⟨f, hf, hfe⟩ := infer_closed (hE.1.2 _ _ _ ht hg) Γ
  exact ⟨_, f, href.trans (by rw [hg]; rfl), hf, fun e _ ↦ (hfe e).symm⟩

/-- The conditional at a quoted tree is its first branch when the tree's label is not zero,
and its second when it is. -/
theorem valid_ifQuote {c a b A : Tree} (ha : typeOf G Γ a = some A) (hb : typeOf G Γ b = some A) :
    Valid G Γ H ⟨A, mk Label.cond [mk Label.quote [c], a, b], if c.label ≠ 0 then a else b⟩ := by
  obtain ⟨fa, hfa⟩ := typeOf_eq_some.mp ha
  obtain ⟨fb, hfb⟩ := typeOf_eq_some.mp hb
  have hif := infer_if (infer_quote G Γ c) hfa hfb
  by_cases hc : c.label = 0
  · simp only [hc, ne_eq, not_true_eq_false, ↓reduceIte] at hif ⊢
    exact ⟨_, fb, hif, hfb, fun _ _ ↦ rfl⟩
  · simp only [hc, ne_eq, not_false_eq_true, ↓reduceIte] at hif ⊢
    exact ⟨_, fa, hif, hfa, fun _ _ ↦ rfl⟩

/-- A sequent valid in a context is valid in the context extended below. -/
theorem valid_wkAt_ctx {Δ : Ctx} {q : Eqn} (h : Valid G Δ [] q) (Γ : Ctx) :
    Valid G (Δ ++ Γ) [] (q.wkAt Δ.length Γ.length) := by
  have h' : Valid G (Δ ++ []) [] q := (List.append_nil Δ).symm ▸ h
  obtain ⟨f, g, hf, hg, he⟩ := h'
  have hv : Valid G (Δ ++ (Γ ++ [])) [] (q.wkAt Δ.length Γ.length) :=
    ⟨_, _, infer_wkAt Δ Γ hf, infer_wkAt Δ Γ hg,
      fun e _ ↦ he _ fun _ hx ↦ absurd hx List.not_mem_nil⟩
  rwa [List.append_nil] at hv

/-- An equation valid in a context is valid with its variables replaced by terms of their types,
innermost first. -/
theorem valid_instAll {us : List Tree} {Δ : Ctx}
    (hus : List.Forall₂ (fun u A ↦ typeOf G Γ u = some A) us Δ) :
    ∀ {q : Eqn}, Valid G (Δ ++ Γ) [] q → Valid G Γ [] (instAll us q) := by
  refine List.Forall₂.rec
    (motive := fun us Δ _ ↦ ∀ {q : Eqn}, Valid G (Δ ++ Γ) [] q → Valid G Γ [] (instAll us q))
    (fun hq ↦ hq) (fun {u A us Δ} hu hrest ih {q} hq ↦ ?_) hus
  obtain ⟨fu, hfu⟩ := typeOf_eq_some.mp hu
  have hwk := infer_wk Δ hfu
  rw [← hrest.length_eq] at hwk
  exact ih (valid_inst (typeOf_eq_some.mpr ⟨_, hwk⟩) hq)

/-- A valid sequent without hypotheses is valid under any hypotheses. -/
theorem Valid.weakenHyps {q : Eqn} (h : Valid G Γ [] q) : Valid G Γ H q := by
  obtain ⟨f, g, hf, hg, he⟩ := h
  exact ⟨f, g, hf, hg, fun e _ ↦ he e fun _ hx ↦ absurd hx List.not_mem_nil⟩

/-- Iterating the successor from a label adds the number of iterations to it. -/
theorem repeat_succ_leaf (a : ℕ) :
    ∀ k : ℕ, Nat.repeat (fun x ↦ Const.add x (leaf 1)) k (leaf a) = leaf (a + k) :=
  Nat.rec rfl fun _ ih ↦ congrArg (fun x ↦ Const.add x (leaf 1)) ih

/-- Iterating the step of the predecessor from a pair of zeros gives the predecessor and the
number of iterations. -/
theorem repeat_pred_pair :
    ∀ k : ℕ, Nat.repeat (fun p : Tree × Tree ↦ (p.2, Const.add p.2 (leaf 1))) k (leaf 0, leaf 0) =
      (leaf (k - 1), leaf k) :=
  Nat.rec rfl fun _ ih ↦ congrArg (fun p : Tree × Tree ↦ (p.2, Const.add p.2 (leaf 1))) ih

/-- Iterating the predecessor from a label subtracts the number of iterations from it. -/
theorem repeat_pred_leaf (a : ℕ) :
    ∀ k : ℕ, Nat.repeat (fun x ↦ Const.sub x (leaf 1)) k (leaf a) = leaf (a - k) :=
  Nat.rec rfl fun _ ih ↦ congrArg (fun x ↦ Const.sub x (leaf 1)) ih

/-- Iterating the addition of a tree's label from zero multiplies it by the number of
iterations. -/
theorem repeat_add_leaf (m : Tree) :
    ∀ k : ℕ, Nat.repeat (fun x ↦ Const.add x m) k (leaf 0) = leaf (m.label * k) :=
  Nat.rec rfl fun _ ih ↦ congrArg (fun x ↦ Const.add x m) ih

/-- Iterating a constant function is the start at zero iterations and the constant after. -/
theorem repeat_const {α : Type} (c z : α) (k : ℕ) :
    Nat.repeat (fun _ ↦ c) k z = if k = 0 then z else c := by
  cases k with
  | zero => rfl
  | succ k => rfl

/-- The step of division by a label, on a pair of a quotient and a remainder. -/
def divModStep (n : Tree) (p : Tree × Tree) : Tree × Tree :=
  if (Const.eq (Const.add p.2 (leaf 1)) n).label ≠ 0 then (Const.add p.1 (leaf 1), leaf 0)
  else (p.1, Const.add p.2 (leaf 1))

/-- Iterating the step of division from a pair of zeros gives the quotient and the remainder of
the number of iterations. -/
theorem repeat_divModStep (n : Tree) :
    ∀ k : ℕ, Nat.repeat (divModStep n) k (leaf 0, leaf 0) =
      (leaf (k / n.label), leaf (k % n.label)) := by
  refine Nat.rec (by simp only [Nat.zero_div, Nat.zero_mod]; rfl) fun k ih ↦ ?_
  change divModStep n (Nat.repeat (divModStep n) k (leaf 0, leaf 0)) = _
  rw [ih]
  change (if (ofBool (k % n.label + 1 == n.label)).label ≠ 0 then
      (leaf (k / n.label + 1), leaf 0) else (leaf (k / n.label), leaf (k % n.label + 1))) =
    (leaf ((k + 1) / n.label), leaf ((k + 1) % n.label))
  have hk := Nat.mod_add_div k n.label
  by_cases h : k % n.label + 1 = n.label
  · have hb : 0 < n.label := by omega
    have hq : (k + 1) / n.label = k / n.label + 1 ∧ (k + 1) % n.label = 0 :=
      (Nat.div_mod_unique hb).mpr ⟨by rw [Nat.mul_succ]; omega, hb⟩
    simp only [ofBool, h, beq_self_eq_true, ↓reduceIte, hq.1, hq.2, leaf, RoseTree.label_node,
      ne_eq, one_ne_zero, not_false_eq_true]
  · have hq : (k + 1) / n.label = k / n.label ∧ (k + 1) % n.label = k % n.label + 1 := by
      rcases Nat.eq_zero_or_pos n.label with hb | hb
      · simp only [hb, Nat.div_zero, Nat.mod_zero, and_self]
      · exact (Nat.div_mod_unique hb).mpr ⟨by omega, by have := Nat.mod_lt k hb; omega⟩
    simp only [ofBool, beq_iff_eq, h, ↓reduceIte, hq.1, hq.2, leaf, RoseTree.label_node,
      ne_eq, not_true_eq_false]

/-- The list tail taken as many times as a number is the list without that many elements. -/
theorem repeat_tail : ∀ (k : ℕ) (xs : List Tree),
    Nat.repeat (fun xs ↦ Const.lcase xs [] fun _ r ↦ r) k xs = xs.drop k := by
  refine Nat.rec (fun _ ↦ rfl) fun k ih xs ↦ ?_
  change Const.lcase (Nat.repeat _ k xs) [] (fun _ r ↦ r) = _
  rw [ih, ← List.tail_drop]
  cases xs.drop k <;> rfl

/-- Counting a list by the right fold gives its length. -/
theorem foldr_count :
    ∀ xs : List Tree, xs.foldr (fun _ n ↦ Const.add n (leaf 1)) (leaf 0) = leaf xs.length :=
  List.rec rfl fun _ _ ih ↦ congrArg (fun n ↦ Const.add n (leaf 1)) ih

/-- The denotation of the successor of a tree. -/
theorem infer_succT {t : Tree} {f : Γ.den → Ty.den tT} (h : infer G Γ t = some ⟨tT, f⟩) :
    infer G Γ (succT t) = some ⟨tT, fun e ↦ Const.add (f e) (leaf 1)⟩ :=
  infer_app (infer_app (infer_add G Γ) h) (infer_quote G Γ (leaf 1))

theorem valid_axLabelNode (G : List Glob) : axLabelNode.Valid G := ⟨_, _, rfl, rfl, fun _ _ ↦ rfl⟩

theorem valid_axChildrenNode (G : List Glob) : axChildrenNode.Valid G :=
  ⟨fun e : Tree × List Tree × Unit ↦ Const.children (Const.node e.1 e.2.1), fun e ↦ e.2.1, rfl,
    rfl, fun e _ ↦ RoseTree.children_node _ e.2.1⟩

theorem valid_axNodeEta (G : List Glob) : axNodeEta.Valid G :=
  ⟨fun e : Tree × Unit ↦ Const.node (Const.label e.1) (Const.children e.1), fun e ↦ e.1, rfl, rfl,
    fun e _ ↦ RoseTree.node_label_children e.1⟩

theorem valid_axChildrenLabel (G : List Glob) : axChildrenLabel.Valid G :=
  ⟨fun e : Tree × Unit ↦ Const.children (Const.label e.1), fun _ ↦ [], rfl, rfl,
    fun _ _ ↦ RoseTree.children_node _ _⟩

theorem valid_axLabelSucc (G : List Glob) : axLabelSucc.Valid G := ⟨_, _, rfl, rfl, fun _ _ ↦ rfl⟩

theorem valid_axAddIter (G : List Glob) : axAddIter.Valid G :=
  ⟨fun e : Tree × Tree × Unit ↦ Const.add e.1 e.2.1,
    fun e ↦ Const.iter (fun x ↦ Const.add x (leaf 1)) (Const.label e.1) e.2.1, rfl, rfl,
    fun _ _ ↦ (repeat_succ_leaf _ _).symm⟩

theorem valid_axPredIter (G : List Glob) : axPredIter.Valid G := by
  have hp : infer G [tT2, tT] (Tm.var 0) = some ⟨tT2, fun e ↦ e.1⟩ := rfl
  have hx : infer G [tT] (Tm.var 0) = some ⟨tT, fun e ↦ e.1⟩ := rfl
  have hlam := infer_lam (A := tT2) rfl (infer_pair (infer_snd hp) (infer_succT (infer_snd hp)))
  have hz := infer_pair (infer_quote G [tT] (leaf 0)) (infer_quote G [tT] (leaf 0))
  have hit := infer_app (infer_app (infer_app (infer_iter (A := tT2) rfl) hlam) hz) hx
  refine ⟨_, _, infer_app (infer_app (infer_sub G _) hx) (infer_quote G _ (leaf 1)),
    infer_fst hit, fun (e : Tree × Unit) _ ↦ ?_⟩
  change Const.sub e.1 (leaf 1) =
    (Nat.repeat (fun p : Tree × Tree ↦ (p.2, Const.add p.2 (leaf 1))) e.1.label
      (leaf 0, leaf 0)).1
  rw [repeat_pred_pair]
  rfl

theorem valid_axSubIter (G : List Glob) : axSubIter.Valid G :=
  ⟨fun e : Tree × Tree × Unit ↦ Const.sub e.1 e.2.1,
    fun e ↦ Const.iter (fun x ↦ Const.sub x (leaf 1)) (Const.label e.1) e.2.1, rfl, rfl,
    fun _ _ ↦ (repeat_pred_leaf _ _).symm⟩

theorem valid_axMulIter (G : List Glob) : axMulIter.Valid G :=
  ⟨fun e : Tree × Tree × Unit ↦ Const.mul e.1 e.2.1,
    fun e ↦ Const.iter (fun x ↦ Const.add x e.1) (leaf 0) e.2.1, rfl, rfl,
    fun _ _ ↦ (repeat_add_leaf _ _).symm⟩

/-- The denotation of the iterated step of division. -/
theorem infer_divMod (G : List Glob) :
    infer G [tT, tT] divMod =
      some ⟨tT2, fun e ↦ Const.iter (divModStep e.2.1) (leaf 0, leaf 0) e.1⟩ := by
  have hp : infer G [tT2, tT, tT] (Tm.var 0) = some ⟨tT2, fun e ↦ e.1⟩ := rfl
  have hn : infer G [tT2, tT, tT] (Tm.var 2) = some ⟨tT, fun e ↦ e.2.2.1⟩ := rfl
  have hm : infer G [tT, tT] (Tm.var 0) = some ⟨tT, fun e ↦ e.1⟩ := rfl
  have hcond := infer_app (infer_app (infer_eqPrim G _) (infer_succT (infer_snd hp))) hn
  have ha := infer_pair (infer_succT (infer_fst hp)) (infer_quote G _ (leaf 0))
  have hb := infer_pair (infer_fst hp) (infer_succT (infer_snd hp))
  have hlam := infer_lam (A := tT2) rfl (infer_if hcond ha hb)
  have hz := infer_pair (infer_quote G [tT, tT] (leaf 0)) (infer_quote G [tT, tT] (leaf 0))
  exact infer_app (infer_app (infer_app (infer_iter (A := tT2) rfl) hlam) hz) hm

theorem valid_axDivIter (G : List Glob) : axDivIter.Valid G := by
  have hm : infer G [tT, tT] (Tm.var 0) = some ⟨tT, fun e ↦ e.1⟩ := rfl
  have hn : infer G [tT, tT] (Tm.var 1) = some ⟨tT, fun e ↦ e.2.1⟩ := rfl
  exact ⟨_, _, infer_app (infer_app (infer_div G _) hm) hn, infer_fst (infer_divMod G),
    fun e _ ↦ (congrArg Prod.fst (repeat_divModStep _ _)).symm⟩

theorem valid_axModIter (G : List Glob) : axModIter.Valid G := by
  have hm : infer G [tT, tT] (Tm.var 0) = some ⟨tT, fun e ↦ e.1⟩ := rfl
  have hn : infer G [tT, tT] (Tm.var 1) = some ⟨tT, fun e ↦ e.2.1⟩ := rfl
  exact ⟨_, _, infer_app (infer_app (infer_mod G _) hm) hn, infer_snd (infer_divMod G),
    fun e _ ↦ (congrArg Prod.snd (repeat_divModStep _ _)).symm⟩

theorem valid_axEqDef (G : List Glob) : axEqDef.Valid G := by
  refine ⟨fun e : Tree × Tree × Unit ↦ Const.eq e.1 e.2.1,
    fun e ↦ Const.iter (fun _ ↦ leaf 0) (leaf 1) (Const.add (Const.sub e.1 e.2.1)
      (Const.sub e.2.1 e.1)), rfl, rfl, fun (e : Tree × Tree × Unit) _ ↦ ?_⟩
  change ofBool (e.1.label == e.2.1.label) =
    Nat.repeat (fun _ ↦ leaf 0) (e.1.label - e.2.1.label + (e.2.1.label - e.1.label)) (leaf 1)
  rw [repeat_const]
  by_cases h : e.1.label = e.2.1.label
  · simp only [ofBool, h, beq_self_eq_true, ↓reduceIte, Nat.sub_self, Nat.add_zero]
  · have hk : e.1.label - e.2.1.label + (e.2.1.label - e.1.label) ≠ 0 := by omega
    simp only [ofBool, beq_iff_eq, h, hk, ↓reduceIte]

theorem valid_axLtDef (G : List Glob) : axLtDef.Valid G := by
  refine ⟨fun e : Tree × Tree × Unit ↦ Const.lt e.1 e.2.1,
    fun e ↦ Const.iter (fun _ ↦ leaf 1) (leaf 0) (Const.sub e.2.1 e.1), rfl, rfl,
    fun (e : Tree × Tree × Unit) _ ↦ ?_⟩
  change ofBool (decide (e.1.label < e.2.1.label)) =
    Nat.repeat (fun _ ↦ leaf 1) (e.2.1.label - e.1.label) (leaf 0)
  rw [repeat_const]
  by_cases h : e.1.label < e.2.1.label
  · have hk : e.2.1.label - e.1.label ≠ 0 := by omega
    simp only [ofBool, h, hk, decide_true, ↓reduceIte]
  · have hk : e.2.1.label - e.1.label = 0 := by omega
    simp only [ofBool, h, hk, decide_false, ↓reduceIte, Bool.false_eq_true]

theorem valid_axLog2Def (G : List Glob) : axLog2Def.Valid G := by
  refine ⟨fun e : Tree × Unit ↦ Const.log2 e.1,
    fun e ↦ if (Const.lt e.1 (leaf 2)).label ≠ 0 then leaf 0
      else Const.add (Const.log2 (Const.div e.1 (leaf 2))) (leaf 1), rfl, rfl,
    fun (e : Tree × Unit) _ ↦ ?_⟩
  change leaf (Nat.log2 e.1.label) =
    if (ofBool (decide (e.1.label < 2))).label ≠ 0 then leaf 0
      else leaf (Nat.log2 (e.1.label / 2) + 1)
  rw [Nat.log2_def]
  by_cases h : e.1.label < 2
  · have h2 : ¬ 2 ≤ e.1.label := by omega
    simp only [ofBool, h, h2, decide_true, ↓reduceIte]
    rfl
  · have h2 : 2 ≤ e.1.label := by omega
    simp only [ofBool, h, h2, decide_false, ↓reduceIte, Bool.false_eq_true]
    rfl

theorem valid_axArityDef (G : List Glob) : axArityDef.Valid G := by
  refine ⟨fun e : Tree × Unit ↦ Const.arity e.1,
    fun e ↦ Const.foldr (fun _ n ↦ Const.add n (leaf 1)) (leaf 0) (Const.children e.1), rfl, rfl,
    fun (e : Tree × Unit) _ ↦ ?_⟩
  change Const.arity e.1 = List.foldr (fun _ n ↦ Const.add n (leaf 1)) (leaf 0) e.1.children
  rw [foldr_count]
  obtain ⟨⟨_, k⟩, g⟩ := e.1
  exact congrArg leaf List.length_ofFn.symm

theorem valid_axChildDef (G : List Glob) : axChildDef.Valid G := by
  have hxs : infer G [tList tT, tT, tT] (Tm.var 0) = some ⟨tList tT, fun e ↦ e.1⟩ := rfl
  have hr : infer G [tList tT, tT, tList tT, tT, tT] (Tm.var 0) =
      some ⟨tList tT, fun e ↦ e.1⟩ := rfl
  have hlc := infer_app (infer_app (infer_app (infer_lcase (A := tT) (B := tList tT) rfl rfl) hxs)
    (infer_nil rfl)) (infer_lam rfl (infer_lam rfl hr))
  have ht : infer G [tT, tT] (Tm.var 0) = some ⟨tT, fun e ↦ e.1⟩ := rfl
  have hi : infer G [tT, tT] (Tm.var 1) = some ⟨tT, fun e ↦ e.2.1⟩ := rfl
  have hit := infer_app (infer_app (infer_app (infer_iter (A := tList tT) rfl)
    (infer_lam (A := tList tT) rfl hlc)) (infer_app (infer_childrenPrim G _) ht)) hi
  have hh : infer G [tList tT, tT, tT, tT] (Tm.var 1) = some ⟨tT, fun e ↦ e.2.1⟩ := rfl
  refine ⟨_, _, infer_app (infer_app (infer_childPrim G _) ht) hi,
    infer_app (infer_app (infer_app (infer_lcase (A := tT) (B := tT) rfl rfl) hit)
      (infer_quote G _ (leaf 0))) (infer_lam rfl (infer_lam rfl hh)),
    fun (e : Tree × Tree × Unit) _ ↦ ?_⟩
  change Const.child e.1 e.2.1 =
    Const.lcase (Nat.repeat (fun xs ↦ Const.lcase xs [] fun _ r ↦ r) e.2.1.label e.1.children)
      (leaf 0) (fun x _ ↦ x)
  rw [repeat_tail]
  obtain ⟨⟨⟨_, k⟩, g⟩, i, _⟩ := e
  change (if h : i.label < k then g ⟨i.label, h⟩ else leaf 0) =
    Const.lcase ((List.ofFn g).drop i.label) (leaf 0) (fun x _ ↦ x)
  have hl : ∀ xs : List Tree, Const.lcase xs (leaf 0) (fun x _ ↦ x) = xs.head?.getD (leaf 0) :=
    fun xs ↦ by cases xs <;> rfl
  rw [hl, List.head?_drop, List.getElem?_ofFn]
  split <;> rfl

theorem valid_axEqualRefl (G : List Glob) : axEqualRefl.Valid G := by
  refine ⟨fun e : Tree × Unit ↦ Const.equal e.1 e.1, fun _ ↦ leaf 1, rfl, rfl,
    fun (e : Tree × Unit) _ ↦ ?_⟩
  change ofBool (decide (e.1 = e.1)) = leaf 1
  rw [decide_eq_true rfl]
  rfl

theorem valid_axEqualSubst (G : List Glob) : axEqualSubst.Valid G := by
  refine ⟨fun e : Tree × Tree × Unit ↦ if (Const.equal e.1 e.2.1).label ≠ 0 then e.2.1 else e.1,
    fun e ↦ e.1, rfl, rfl, fun (e : Tree × Tree × Unit) _ ↦ ?_⟩
  change (if (ofBool (decide (e.1 = e.2.1))).label ≠ 0 then e.2.1 else e.1) = e.1
  by_cases h : e.1 = e.2.1
  · rw [← h]
    split <;> rfl
  · simp only [ofBool, h, decide_false, Bool.false_eq_true, ↓reduceIte]
    rfl

theorem valid_axEqualBool (G : List Glob) : axEqualBool.Valid G := by
  refine ⟨fun e : Tree × Tree × Unit ↦
      if (Const.equal e.1 e.2.1).label ≠ 0 then leaf 1 else leaf 0,
    fun e ↦ Const.equal e.1 e.2.1, rfl, rfl, fun (e : Tree × Tree × Unit) _ ↦ ?_⟩
  change (if (ofBool (decide (e.1 = e.2.1))).label ≠ 0 then leaf 1 else leaf 0) =
    ofBool (decide (e.1 = e.2.1))
  cases decide (e.1 = e.2.1) <;> rfl

/-- The defining equations of the primitives hold in every global environment. -/
theorem axioms_valid (G : List Glob) : ∀ th ∈ axioms, th.Valid G := by
  simp only [axioms, List.forall_mem_cons]
  exact ⟨valid_axLabelNode G, valid_axChildrenNode G, valid_axNodeEta G, valid_axChildrenLabel G,
    valid_axLabelSucc G, valid_axAddIter G, valid_axPredIter G, valid_axSubIter G,
    valid_axMulIter G, valid_axDivIter G, valid_axModIter G, valid_axEqDef G, valid_axLtDef G,
    valid_axLog2Def G, valid_axArityDef G, valid_axChildDef G, valid_axEqualRefl G,
    valid_axEqualSubst G, valid_axEqualBool G, fun _ h ↦ absurd h List.not_mem_nil⟩

/-- A theorem holding in the global environment holds at terms of its variables' types. -/
theorem valid_thm_inst {th : Thm} {us : List Tree} (hth : th.Valid G)
    (hus : List.Forall₂ (fun u A ↦ typeOf G Γ u = some A) us th.ctx) :
    Valid G Γ H (th.inst Γ us) :=
  (valid_instAll hus (valid_wkAt_ctx hth Γ)).weakenHyps

/-- A cited theorem holding in the global environment has a valid instance. -/
theorem valid_cite {th : Thm} {us : List Tree} {q : Eqn} (hth : th.Valid G)
    (h : th.cite G Γ us = some q) : Valid G Γ H q := by
  unfold Thm.cite at h
  split at h
  · cases h
    exact valid_thm_inst hth ‹_›
  · cases h

/-- Iteration reads the label of the tree it iterates over. -/
theorem valid_iterLabel {A s z t : Tree} (hA : Ty.IsTy A = true)
    (hs : typeOf G Γ s = some (tArrow A A)) (hz : typeOf G Γ z = some A)
    (ht : typeOf G Γ t = some tT) :
    Valid G Γ H
      ⟨A, apps (mk Label.iter [A]) [s, z, t], apps (mk Label.iter [A]) [s, z,
          mk Label.app [mk Label.prim [leaf Prim.label], t]]⟩ := by
  obtain ⟨fs, hfs⟩ := typeOf_eq_some.mp hs
  obtain ⟨fz, hfz⟩ := typeOf_eq_some.mp hz
  obtain ⟨ft, hft⟩ := typeOf_eq_some.mp ht
  have hi := infer_app (infer_app (infer_iter (G := G) (Γ := Γ) hA) hfs) hfz
  exact ⟨_, _, infer_app hi hft, infer_app hi (infer_app (infer_label G Γ) hft), fun _ _ ↦ rfl⟩

/-- The conditional is the iteration of a constant function from its second branch. -/
theorem valid_ifIter {A c a b : Tree} (hA : Ty.IsTy A = true) (hc : typeOf G Γ c = some tT)
    (ha : typeOf G Γ a = some A) (hb : typeOf G Γ b = some A) :
    Valid G Γ H ⟨A, mk Label.cond [c, a, b],
      apps (mk Label.iter [A]) [mk Label.lam [A, Kernel.wk 1 a], b, c]⟩ := by
  obtain ⟨fc, hfc⟩ := typeOf_eq_some.mp hc
  obtain ⟨fa, hfa⟩ := typeOf_eq_some.mp ha
  obtain ⟨fb, hfb⟩ := typeOf_eq_some.mp hb
  refine ⟨_, _, infer_if hfc hfa hfb,
    infer_app (infer_app (infer_app (infer_iter hA) (infer_lam hA (infer_wk [A] hfa))) hfb) hfc,
    fun e _ ↦ ?_⟩
  simp only [iterDen, Const.iter]
  generalize RoseTree.label (fc e) = n
  cases n with
  | zero => rfl
  | succ k => rfl

/-- The conclusion of each rule of {lit}`checkMore` is valid when its premises' conclusions are. -/
theorem checkMore_sound {l : ℕ} {cs : List Tree} {E : Env} {G : List Glob} {Γ : Ctx}
    {H : List Eqn} {q : Eqn}
    (ih : ∀ c ∈ cs, ∀ (E : Env) (G : List Glob) (Γ : Ctx) (H : List Eqn) (q : Eqn),
      E.Sound G → check c E G Γ H = some q → Valid G Γ H q) (hE : E.Sound G)
    (h : checkMore l (cs.map fun c ↦ (c, RoseTree.para checkStep c)) E G Γ H = some q) :
    Valid G Γ H q := by
  simp only [checkMore] at h
  split at h
  case h_1 A sA B sB n sn c sc heq =>
    split at h
    · rename_i hcond
      cases h
      obtain ⟨hA, hB, hn, hc⟩ := hcond
      exact valid_lcaseNil hA hB hn hc
    · cases h
  case h_2 A sA B sB x sx xs sxs n sn c sc heq =>
    split at h
    · rename_i hcond
      cases h
      obtain ⟨hA, hB, hn, hc, hx, hxs⟩ := hcond
      exact valid_lcaseCons hA hB hn hc hx hxs
    · cases h
  case h_3 A sA s ss z sz heq =>
    split at h
    · rename_i hcond
      cases h
      exact valid_iterZero hcond.1 hcond.2.1 hcond.2.2
    · cases h
  case h_4 A sA s ss z sz n sn heq =>
    split at h
    · rename_i hcond
      cases h
      obtain ⟨hA, hs, hz, hn⟩ := hcond
      exact valid_iterSucc hA hs hz hn
    · cases h
  case h_5 A sA f sf x sx xs sxs heq =>
    split at h
    · rename_i hcond
      cases h
      obtain ⟨hA, hf, hx, hxs⟩ := hcond
      exact valid_foldNode hA hf hx hxs
    · cases h
  case h_6 s ss t st cp1 p1 heq =>
    obtain ⟨hc1, rfl⟩ := mem_of_map_para (c := cp1) (s := p1) heq (by simp)
    split at h
    · rename_i L Γ'
      obtain ⟨B, hB, h⟩ := Option.bind_eq_some_iff.mp h
      split at h
      · rename_i hcond
        cases h
        obtain ⟨rfl, hBt, ht, hH, hT, hp1⟩ := hcond
        exact valid_indTree hBt hB ht hH hT (ih cp1 hc1 _ _ _ _ _ hE hp1)
      · cases h
    · cases h
  case h_7 s ss t st cp0 p0 cp1 p1 heq =>
    obtain ⟨hc0, rfl⟩ := mem_of_map_para (c := cp0) (s := p0) heq (by simp)
    obtain ⟨hc1, rfl⟩ := mem_of_map_para (c := cp1) (s := p1) heq (by simp)
    split at h
    · rename_i L Γ'
      obtain ⟨B, hB, h⟩ := Option.bind_eq_some_iff.mp h
      split at h
      · rename_i hcond
        cases h
        obtain ⟨rfl, ht, hH, hT, hp0, hp1⟩ := hcond
        exact valid_indLabel hB ht hH hT (ih cp0 hc0 _ _ _ _ _ hE hp0)
          (ih cp1 hc1 _ _ _ _ _ hE hp1)
      · cases h
    · cases h
  case h_8 j sj heq =>
    obtain ⟨t, ht, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨A, hA, rfl⟩ := Option.map_eq_some_iff.mp h
    exact valid_unfold hE ht hA
  case h_9 c sc a sa b sb heq =>
    obtain ⟨A, hA, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · rename_i hB
      cases h
      exact valid_ifQuote hA hB
    · cases h
  case h_10 j sj us heq =>
    obtain ⟨th, hth, h⟩ := Option.bind_eq_some_iff.mp h
    exact valid_cite (axioms_valid G th (List.mem_of_getElem? hth)) h
  case h_11 A sA s ss z sz t st heq =>
    split at h
    · rename_i hcond
      cases h
      obtain ⟨hA, hs, hz, ht⟩ := hcond
      exact valid_iterLabel hA hs hz ht
    · cases h
  case h_12 A sA c sc a sa b sb heq =>
    split at h
    · rename_i hcond
      cases h
      obtain ⟨hA, hc, ha, hb⟩ := hcond
      exact valid_ifIter hA hc ha hb
    · cases h
  case h_13 j sj us heq =>
    obtain ⟨th, hth, h⟩ := Option.bind_eq_some_iff.mp h
    exact valid_cite (hE.2 th (List.mem_of_getElem? hth)) h
  case h_14 => cases h

/-- Every conclusion the checker computes, in a program's definitions and the environment they
load, is valid. -/
theorem check_sound : ∀ (c : Tree) (E : Env) (G : List Glob) (Γ : Ctx) (H : List Eqn)
    (q : Eqn), E.Sound G → check c E G Γ H = some q → Valid G Γ H q := by
  refine RoseTree.ind fun l cs ih E G Γ H q hE h ↦ ?_
  simp only [check, RoseTree.para_node, checkStep] at h
  split at h
  · exact checkCore_sound ih hE h
  · exact checkMore_sound ih hE h

end Soundness

end Geb.GoedelT

end
