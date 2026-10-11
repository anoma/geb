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
equation under equational hypotheses. Its statements are what a proof about kernel programs
concludes: such a proof is made in the metalogic, about the programs' translations into its
internal language, and the translation's soundness carries a theorem back to the programs
({lit}`Geb.FreeTopos.Translation.thm`).

A sequent is a context, a list of hypotheses and a conclusion, each an equation between two terms
of a type in that context; it is valid when, at every value of the context at which the
hypotheses hold, both sides of the conclusion have its type and denote the same value.

## Main definitions

* {lit}`Eqn`, {lit}`Eqn.Holds`, {lit}`Valid` — equations, their truth at a value of the
  context, and valid sequents.
* {lit}`Loaded` — the agreement of a program's definitions with a global environment.
* {lit}`Thm`, {lit}`Thm.Valid` — theorems, and their truth in a global environment.

## Main statements

* {lit}`Geb.Kernel.infer_append` — extending the global environment keeps denotations.
* {lit}`load_loaded` — a loaded program's definitions agree with its environment.

## References

* \[Goedel1958\], the theory T.
* \[AvigadFeferman1998\], Section 2.2, for T as a quantifier-free theory with a rule of
  induction.

## Tags

bootstrap, Gödel's T, equational logic, System T
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
  case h_18 A sA heq =>
    obtain ⟨rfl, rfl⟩ := map_para_eq_one heq
    split at h
    · rename_i hA
      cases h
      simp only [infer_node, List.map_cons, List.map_nil, inferStep, hA, ↓reduceIte]
    · cases h
  case h_19 => cases h

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

/-- The denotation of the fold of trees whose step sees the node itself. -/
theorem infer_para {G : List Glob} {Γ : Ctx} {A : Tree} (hA : Ty.IsTy A = true) :
    infer G Γ (mk Label.para [A]) = some ⟨foldTy A, fun _ ↦ paraDen A⟩ := by
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

/-- A loaded program's definitions agree with its environment. -/
theorem load_loaded {D : List Tree} {G : List Glob} (h : load D = some G) : Loaded D G :=
  loaded_foldl D [] [] G
    ⟨rfl, fun _ _ _ ht _ ↦ absurd ht (by rw [List.getElem?_nil]; exact fun h ↦ nomatch h)⟩
    h

end Geb.GoedelT

end
