/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Prototypes.PartialHorn.Development
public import Geb.Prototypes.PartialHorn.Point

set_option doc.verso true in
/-!
# The term model and completeness

An equation is derivable in a context under hypotheses, with an environment of theorems, when a
certificate concludes it. Each rule of the checker gives a closure property of derivability.
Derivable equality is an equivalence relation on the terms derivably defined, and a congruence
for the operations.

The term model of a context under hypotheses \[Kawase2024\] has as values the classes of the
terms of a sort in the context that are derivably defined, modulo derivable equality; an
operation is defined at classes exactly when its application to their representatives has a sort
and is derivably defined, and its value is the application's class. At the assignment of each
variable of the context to its own class, a term's value is its class when it has a sort and is
derivably defined, and is undefined otherwise, so that an equation holds there exactly when it is
derivable between terms of one sort. The term model is a model of every theory whose axioms are
in scope and equate terms of one sort, and in it the hypotheses hold at that assignment when they
equate terms of one sort.

Completeness follows: an equation that holds in every model of such a theory under such
hypotheses is derivable (\[PalmgrenVickers2007\], Theorem 22, for the initial model of
closed terms). The extensions of a theory by well-formed definitions keep its axioms in scope, as
they keep them equations of terms of one sort.

## Main definitions

* {lit}`Derivable` — derivability by a certificate.
* {lit}`TermModel.termModel` — the term model of a context under hypotheses.
* {lit}`TermModel.generic` — the assignment of each variable to its own class.

## Main statements

* {lit}`TermModel.eval_generic` — a term of a sort, derivably defined, has its class as value.
* {lit}`TermModel.holds_generic_iff` — an equation holds at the generic assignment exactly when
  it is derivable between terms of one sort.
* {lit}`TermModel.isModel` — the term model is a model of a theory whose axioms are in scope and
  equate terms of one sort.
* {lit}`derivable_iff_valid` — completeness: derivability is validity in every model.
* {lit}`scoped_extendAll` — definitional extensions keep a theory's axioms in scope.

## References

* \[PalmgrenVickers2007\], Theorem 22.
* \[Kawase2024\], Section 6.3.

## Tags

partial Horn logic, term model, completeness, provable equality, quotient
-/

set_option doc.verso true

@[expose] public section

namespace Geb.PartialHorn

section Derivable

variable (T : Theory) (E : Array Seq) (Γ : List ℕ) (H : List Eqn)

/-- An equation is derivable in a context under hypotheses, with an environment of theorems: a
certificate concludes it. -/
def Derivable (q : Eqn) : Prop := ∃ c, check T E c Γ H = some q

variable {T E Γ H}

/-- The checker at a node is the node's rule at its children's certificates and results. -/
theorem check_node (l : ℕ) (cs : List Tree) :
    check T E (RoseTree.node l cs) Γ H =
      checkStep T E l (cs.map fun c ↦ (c, check T E c)) Γ H := by
  rw [check, RoseTree.para_node]
  rfl

/-- The certificates of derivable equations, one for each. -/
theorem exists_certs (qs : List Eqn) (h : ∀ q ∈ qs, Derivable T E Γ H q) :
    ∃ ps : List Tree, ps.map (fun p ↦ check T E p Γ H) = qs.map some :=
  qs.rec (motive := fun qs ↦ (∀ q ∈ qs, Derivable T E Γ H q) →
      ∃ ps : List Tree, ps.map (fun p ↦ check T E p Γ H) = qs.map some)
    (fun _ ↦ ⟨[], rfl⟩)
    (fun q qs ih h ↦ by
      obtain ⟨p, hp⟩ := h q List.mem_cons_self
      obtain ⟨ps, hps⟩ := ih fun q' hq' ↦ h q' (List.mem_cons_of_mem q hq')
      exact ⟨p :: ps, by simp [hp, hps]⟩) h

namespace Derivable

/-- A hypothesis is derivable. -/
theorem hyp {i : ℕ} {q : Eqn} (h : H[i]? = some q) : Derivable T E Γ H q :=
  ⟨Cert.hyp i, by simpa [Cert.hyp, check_node, checkStep, Cert.leaf] using h⟩

/-- A variable of the context is derivably defined. -/
theorem refl {i : ℕ} (hi : i < Γ.length) : Derivable T E Γ H ⟨var i, var i⟩ :=
  ⟨Cert.refl i, by simp [Cert.refl, check_node, checkStep, Cert.leaf, hi]⟩

/-- Symmetry. -/
theorem symm {t u : Tree} (h : Derivable T E Γ H ⟨t, u⟩) : Derivable T E Γ H ⟨u, t⟩ := by
  obtain ⟨p, hp⟩ := h
  exact ⟨Cert.symm p, by simp [Cert.symm, check_node, checkStep, hp]⟩

/-- Transitivity. -/
theorem trans {t u v : Tree} (h : Derivable T E Γ H ⟨t, u⟩) (h' : Derivable T E Γ H ⟨u, v⟩) :
    Derivable T E Γ H ⟨t, v⟩ := by
  obtain ⟨p, hp⟩ := h
  obtain ⟨p', hp'⟩ := h'
  refine ⟨Cert.trans p p', ?_⟩
  simp only [Cert.trans, check_node, checkStep, List.map_cons, List.map_nil]
  rw [hp, hp', Option.bind_some, Option.bind_some]
  exact if_pos rfl

/-- The left side of a derivable equation is derivably defined. -/
theorem left {t u : Tree} (h : Derivable T E Γ H ⟨t, u⟩) : Derivable T E Γ H ⟨t, t⟩ :=
  h.trans h.symm

/-- The right side of a derivable equation is derivably defined. -/
theorem right {t u : Tree} (h : Derivable T E Γ H ⟨t, u⟩) : Derivable T E Γ H ⟨u, u⟩ :=
  h.symm.trans h

/-- Congruence of an operation at a derivably defined application. -/
theorem cong {k : ℕ} {qs : List Eqn}
    (hd : Derivable T E Γ H ⟨op k (qs.map Eqn.lhs), op k (qs.map Eqn.lhs)⟩)
    (hqs : ∀ q ∈ qs, Derivable T E Γ H q) :
    Derivable T E Γ H ⟨op k (qs.map Eqn.lhs), op k (qs.map Eqn.rhs)⟩ := by
  obtain ⟨d, hd⟩ := hd
  obtain ⟨ps, hps⟩ := exists_certs qs hqs
  refine ⟨Cert.cong d ps, ?_⟩
  have hl : (ps.map fun p ↦ (check T E p Γ H).map Eqn.lhs) = (qs.map Eqn.lhs).map some := by
    have h := congrArg (List.map (Option.map Eqn.lhs)) hps
    rw [List.map_map, List.map_map] at h
    rw [List.map_map]
    exact h
  have hr : (ps.map fun p ↦ (check T E p Γ H).map Eqn.rhs) = (qs.map Eqn.rhs).map some := by
    have h := congrArg (List.map (Option.map Eqn.rhs)) hps
    rw [List.map_map, List.map_map] at h
    rw [List.map_map]
    exact h
  rw [← mapM_eq_some_iff] at hr
  have hr' : (ps.map fun c ↦ (c, check T E c)).mapM (fun p ↦ (p.2 Γ H).map Eqn.rhs) =
      some (qs.map Eqn.rhs) := by
    rw [List.mapM_map]
    exact hr
  rw [Cert.cong, check_node, List.map_cons]
  simp only [checkStep]
  rw [hd, Option.bind_some]
  rw [if_pos ⟨Nat.succ_ne_zero k, by rw [List.map_map, op, RoseTree.children_node]; exact hl⟩,
    hr', Option.map_some]
  rfl

/-- Strictness: an argument of a derivably defined application is derivably defined. -/
theorem strict {k j : ℕ} {ts : List Tree} {u t : Tree} (hd : Derivable T E Γ H ⟨op k ts, u⟩)
    (hj : ts[j]? = some t) : Derivable T E Γ H ⟨t, t⟩ := by
  obtain ⟨d, hd⟩ := hd
  exact ⟨Cert.strict j d, by simp [Cert.strict, check_node, checkStep, Cert.leaf, hd, op, hj]⟩

/-- An instance of an axiom in scope, at derivably defined terms of its context's sorts, whose
hypotheses' instances are derivable. -/
theorem ax {j : ℕ} {a : Seq} (ha : T.axioms[j]? = some a) (hsc : a.Scoped = true)
    {ts : List Tree} (hts : ts.map (sortOf T.sig Γ) = a.ctx.map some)
    (hd : ∀ t ∈ ts, Derivable T E Γ H ⟨t, t⟩) (hh : ∀ h ∈ a.hyps, Derivable T E Γ H (h.subst ts)) :
    Derivable T E Γ H (a.concl.subst ts) := by
  obtain ⟨ds, hds⟩ := exists_certs (ts.map fun t ↦ ⟨t, t⟩) (by simpa using hd)
  obtain ⟨hs, hhs⟩ := exists_certs (a.hyps.map (Eqn.subst ts)) (by simpa using hh)
  have hlt : ts.length = a.ctx.length := by simpa using congrArg List.length hts
  have hld : ds.length = a.ctx.length := by simpa [hlt] using congrArg List.length hds
  refine ⟨Cert.ax j ts ds hs, ?_⟩
  rw [Cert.ax, check_node, List.cons_append, List.cons_append, List.map_cons, List.map_append,
    List.map_append]
  set f : Tree → Tree × Chk := fun c ↦ (c, check T E c)
  have h₁ : ((ts.map f ++ ds.map f ++ hs.map f).take a.ctx.length).map Prod.fst = ts := by
    rw [List.append_assoc, List.take_left' (by simpa using hlt)]
    simp [f, Function.comp_def]
  have h₂ : (((ts.map f ++ ds.map f ++ hs.map f).drop a.ctx.length).take a.ctx.length) =
      ds.map f := by
    rw [List.append_assoc, List.drop_left' (by simpa using hlt), List.take_left' (by simpa)]
  have h₃ : (ts.map f ++ ds.map f ++ hs.map f).drop (a.ctx.length + a.ctx.length) =
      hs.map f := by
    rw [← List.drop_drop, List.append_assoc, List.drop_left' (by simpa using hlt),
      List.drop_left' (by simpa)]
  simp only [checkStep]
  rw [Cert.leaf, leafIndex_leaf, Option.bind_some, ha, Option.bind_some, inst]
  rw [h₁, h₂, h₃]
  have hds' : (ds.map f).map (fun c ↦ (c.2 Γ H).map Eqn.lhs) = ts.map some := by
    simpa [f, Function.comp_def] using congrArg (List.map (Option.map Eqn.lhs)) hds
  have hhs' : (hs.map f).map (fun c ↦ c.2 Γ H) = a.hyps.map fun h ↦ some (h.subst ts) := by
    simpa [f, Function.comp_def] using hhs
  exact if_pos ⟨hsc, hts, hds', hhs'⟩

end Derivable

/-- Derivable equations whose sides are elementwise the terms of two lists relate those lists'
applications of an operation, when the first is derivably defined. -/
theorem Derivable.cong_of_forall₂ {k : ℕ} {ts us : List Tree}
    (h : List.Forall₂ (fun t u ↦ Derivable T E Γ H ⟨t, u⟩) ts us)
    (hd : Derivable T E Γ H ⟨op k ts, op k ts⟩) : Derivable T E Γ H ⟨op k ts, op k us⟩ := by
  obtain ⟨qs, hl, hr, hqs⟩ : ∃ qs : List Eqn, qs.map Eqn.lhs = ts ∧ qs.map Eqn.rhs = us ∧
      ∀ q ∈ qs, Derivable T E Γ H q :=
    h.rec (motive := fun ts us _ ↦ ∃ qs : List Eqn, qs.map Eqn.lhs = ts ∧ qs.map Eqn.rhs = us ∧
        ∀ q ∈ qs, Derivable T E Γ H q)
      ⟨[], rfl, rfl, by simp⟩
      fun {t u _ _} htu _ ih ↦ by
        obtain ⟨qs, hl, hr, hqs⟩ := ih
        exact ⟨⟨t, u⟩ :: qs, by simp [hl], by simp [hr],
          List.forall_mem_cons.mpr ⟨htu, hqs⟩⟩
  subst hl hr
  exact Derivable.cong hd hqs

end Derivable

namespace TermModel

section Carrier

variable (T : Theory) (E : Array Seq) (Γ : List ℕ) (H : List Eqn)

/-- A representative: a sort and a term of that sort in the context, derivably defined. -/
abbrev Rep : Type :=
  {p : ℕ × Tree // sortOf T.sig Γ p.2 = some p.1 ∧ Derivable T E Γ H ⟨p.2, p.2⟩}

/-- Representatives are equivalent when they have one sort and their terms are derivably
equal. -/
instance setoid : Setoid (Rep T E Γ H) where
  r a b := a.1.1 = b.1.1 ∧ Derivable T E Γ H ⟨a.1.2, b.1.2⟩
  iseqv := ⟨fun a ↦ ⟨rfl, a.2.2⟩, fun h ↦ ⟨h.1.symm, h.2.symm⟩,
    fun h h' ↦ ⟨h.1.trans h'.1, h.2.trans h'.2⟩⟩

/-- The classes of representatives. -/
abbrev Cls : Type := Quotient (setoid T E Γ H)

variable {T E Γ H}

/-- The sort of a class. -/
def Cls.sort : Cls T E Γ H → ℕ := Quotient.lift (fun r ↦ r.1.1) fun _ _ h ↦ h.1

variable (T E Γ H)

/-- The values of a sort: the classes of that sort. -/
def Car (s : ℕ) : Type := {v : Cls T E Γ H // v.sort = s}

/-- The sorted values. -/
abbrev Val : Type := Σ s, Car T E Γ H s

variable {T E Γ H}

/-- A class as a sorted value. -/
def toVal (v : Cls T E Γ H) : Val T E Γ H := ⟨v.sort, v, rfl⟩

/-- Representatives of one sort whose terms are equal have one class. -/
theorem mk_congr {s s' : ℕ} {t t' : Tree} (hs : s = s') (ht : t = t') {p p'} :
    (⟦⟨(s, t), p⟩⟧ : Cls T E Γ H) = ⟦⟨(s', t'), p'⟩⟧ := by
  subst hs ht
  rfl

/-- The class of a term, defined when the term has a sort and is derivably defined. -/
def cls (t : Tree) : Part (Cls T E Γ H) :=
  ⟨(sortOf T.sig Γ t).isSome ∧ Derivable T E Γ H ⟨t, t⟩,
    fun h ↦ ⟦⟨((sortOf T.sig Γ t).get h.1, t), (Option.some_get h.1).symm, h.2⟩⟧⟩

/-- The class of a term of a sort, derivably defined. -/
theorem cls_eq_some {t : Tree} {s : ℕ} (hs : sortOf T.sig Γ t = some s)
    (hd : Derivable T E Γ H ⟨t, t⟩) : cls t = Part.some ⟦⟨(s, t), hs, hd⟩⟧ :=
  Part.eq_some_iff.mpr ⟨⟨by simp [hs], hd⟩, by
    change (⟦_⟧ : Cls T E Γ H) = _
    congr
    simp [hs]⟩

/-- A value of the class of a term is its class, at its sort. -/
theorem eq_of_mem_cls {t : Tree} {v : Cls T E Γ H} (h : v ∈ cls t) :
    ∃ s, ∃ (hs : sortOf T.sig Γ t = some s) (hd : Derivable T E Γ H ⟨t, t⟩),
      v = ⟦⟨(s, t), hs, hd⟩⟧ := by
  obtain ⟨⟨h₁, h₂⟩, rfl⟩ := h
  exact ⟨_, (Option.some_get h₁).symm, h₂, rfl⟩

/-- The terms of a list of representatives. -/
def terms (rs : List (Rep T E Γ H)) : List Tree := rs.map fun r ↦ r.1.2

/-- The operation at a list of representatives: the class of the application to their
terms. -/
def opRep (k : ℕ) (rs : List (Rep T E Γ H)) : Part (Val T E Γ H) :=
  (cls (op k (terms rs))).map toVal

/-- The operation at elementwise equivalent lists of representatives is one partial value. -/
theorem opRep_respects (k : ℕ) (rs rs' : List (Rep T E Γ H))
    (h : List.Forall₂ (· ≈ ·) rs rs') : opRep k rs = opRep k rs' := by
  have hsorts : (terms rs).map (sortOf T.sig Γ) = (terms rs').map (sortOf T.sig Γ) := by
    rw [← List.forall₂_eq_eq_eq, terms, terms, List.map_map, List.map_map,
      List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    exact h.imp fun r r' hr ↦ by simp [r.2.1, r'.2.1, hr.1]
  have hsort : sortOf T.sig Γ (op k (terms rs)) = sortOf T.sig Γ (op k (terms rs')) := by
    rw [op, op, sortOf_node_succ, sortOf_node_succ, hsorts]
  have hrel : List.Forall₂ (fun t u ↦ Derivable T E Γ H ⟨t, u⟩) (terms rs) (terms rs') := by
    rw [terms, terms, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    exact h.imp fun _ _ hr ↦ hr.2
  have hrel' : List.Forall₂ (fun t u ↦ Derivable T E Γ H ⟨t, u⟩) (terms rs') (terms rs) :=
    List.Forall₂.flip (hrel.imp fun _ _ h ↦ h.symm)
  refine Part.ext' ?_ fun h₁ h₂ ↦ ?_
  · exact ⟨fun ⟨hs, hd⟩ ↦ ⟨hsort ▸ hs, (Derivable.cong_of_forall₂ hrel hd).right⟩,
      fun ⟨hs, hd⟩ ↦ ⟨hsort ▸ hs, (Derivable.cong_of_forall₂ hrel' hd).right⟩⟩
  · refine congrArg toVal (Quotient.sound ⟨?_, Derivable.cong_of_forall₂ hrel h₁.2⟩)
    exact Option.some_injective _ ((Option.some_get _).trans (hsort.trans (Option.some_get _).symm))

/-- A list of classes, as the class of the list of their representatives, elementwise. -/
def seq : List (Cls T E Γ H) → Quot (List.Forall₂ (· ≈ ·) : List (Rep T E Γ H) → _ → Prop) :=
  List.rec (Quot.mk _ []) fun v _ ih ↦ Quot.map₂ List.cons
    (fun _ _ _ h ↦ List.Forall₂.cons (Setoid.refl _) h)
    (fun _ _ _ h ↦ List.Forall₂.cons h (List.forall₂_same.mpr fun _ _ ↦ Setoid.refl _)) v ih

/-- The list of the classes of representatives is the class of their list. -/
theorem seq_mk (rs : List (Rep T E Γ H)) : seq (rs.map fun r ↦ ⟦r⟧) = Quot.mk _ rs :=
  rs.rec rfl fun r rs ih ↦ by
    rw [List.map_cons]
    dsimp only [seq]
    exact congrArg (Quot.map₂ List.cons _ _ ⟦r⟧) ih

variable (T E Γ H)

/-- The term model of a context under hypotheses: the classes of the terms of each sort
derivably defined, modulo derivable equality; an operation is defined at classes exactly when its
application to their representatives has a sort and is derivably defined, with the application's
class. -/
def termModel : Model.{0} T.sig where
  Car := Car T E Γ H
  op k args := Quot.lift (opRep k) (opRep_respects k) (seq (args.map fun w ↦ w.2.1))
  op_sort {k args w} hw := by
    generalize seq (args.map fun w ↦ w.2.1) = q at hw
    induction q using Quot.ind with
    | mk rs =>
      obtain ⟨v, hv, rfl⟩ := (Part.mem_map_iff _).mp hw
      obtain ⟨s, hs, -, rfl⟩ := eq_of_mem_cls hv
      rw [op, sortOf_node_succ, Option.bind_eq_some_iff] at hs
      obtain ⟨o, ho, hs⟩ := hs
      split_ifs at hs
      rw [ho, Option.map_some]
      exact hs

variable {T E Γ H}

/-- A class, as a value of the term model. -/
def val (v : Cls T E Γ H) : (termModel T E Γ H).Val := toVal v

/-- The operation of the term model at the values of representatives is the operation at
them. -/
theorem op_termModel (k : ℕ) (rs : List (Rep T E Γ H)) :
    (termModel T E Γ H).op k (rs.map fun r ↦ val ⟦r⟧) = opRep k rs := by
  change Quot.lift _ _ (seq ((rs.map fun r ↦ toVal ⟦r⟧).map fun w ↦ w.2.1)) = _
  rw [List.map_map]
  exact congrArg (Quot.lift _ _) (seq_mk rs)

/-- Every list of values of the term model is the list of the values of representatives. -/
theorem exists_reps (ws : List (termModel T E Γ H).Val) :
    ∃ rs : List (Rep T E Γ H), ws = rs.map fun r ↦ val ⟦r⟧ :=
  ws.rec ⟨[], rfl⟩ fun w _ ih ↦ by
    obtain ⟨rs, rfl⟩ := ih
    obtain ⟨s, v, rfl⟩ := w
    obtain ⟨r, rfl⟩ := Quotient.exists_rep v
    exact ⟨r :: rs, rfl⟩

variable (T E Γ H)

/-- The class of a variable of the context. -/
def varCls (i : Fin Γ.length) : Cls T E Γ H :=
  ⟦⟨(Γ[i], var i), by simp [var, sortOf_node_zero], Derivable.refl i.2⟩⟧

/-- The generic assignment: each variable of the context to its class. -/
def generic : List (termModel T E Γ H).Val := List.ofFn fun i ↦ val (varCls T E Γ H i)

variable {T E Γ H}

/-- The generic assignment has the context's sorts. -/
theorem generic_sorts : (generic T E Γ H).map Sigma.fst = Γ := by
  rw [generic, List.map_ofFn]
  exact List.ofFn_getElem

/-- The generic assignment's value at an index of the context is the class of its variable. -/
theorem getElem?_generic (i : ℕ) : (generic T E Γ H)[i]? =
    if h : i < Γ.length then some (val (varCls T E Γ H ⟨i, h⟩)) else none :=
  List.getElem?_ofFn

/-- The operation at representatives of one sort derivably defined at them. -/
theorem opRep_eq_some {k : ℕ} {rs : List (Rep T E Γ H)} {s : ℕ}
    (hs : sortOf T.sig Γ (op k (terms rs)) = some s)
    (hd : Derivable T E Γ H ⟨op k (terms rs), op k (terms rs)⟩) :
    opRep k rs = Part.some (toVal ⟦⟨(s, op k (terms rs)), hs, hd⟩⟧) := by
  rw [opRep, cls_eq_some hs hd, Part.map_some]

/-- A value of the operation at representatives is the class of the application to their
terms. -/
theorem eq_of_mem_opRep {k : ℕ} {rs : List (Rep T E Γ H)} {w : Val T E Γ H} (h : w ∈ opRep k rs) :
    ∃ s, ∃ (hs : sortOf T.sig Γ (op k (terms rs)) = some s)
      (hd : Derivable T E Γ H ⟨op k (terms rs), op k (terms rs)⟩),
      w = toVal ⟦⟨(s, op k (terms rs)), hs, hd⟩⟧ := by
  obtain ⟨v, hv, rfl⟩ := (Part.mem_map_iff _).mp h
  obtain ⟨s, hs, hd, rfl⟩ := eq_of_mem_cls hv
  exact ⟨s, hs, hd, rfl⟩

/-- The representatives of a list of terms, each of a sort and derivably defined. -/
def repsOf (cs : List Tree) (hs : ∀ c ∈ cs, (sortOf T.sig Γ c).isSome)
    (hd : ∀ c ∈ cs, Derivable T E Γ H ⟨c, c⟩) : List (Rep T E Γ H) :=
  cs.attach.map fun c ↦ ⟨((sortOf T.sig Γ c.1).get (hs c.1 c.2), c.1),
    (Option.some_get _).symm, hd c.1 c.2⟩

/-- The terms of the representatives of a list of terms are the terms. -/
theorem terms_repsOf {cs : List Tree} {hs hd} :
    terms (repsOf (T := T) (E := E) (Γ := Γ) (H := H) cs hs hd) = cs := by
  simp [terms, repsOf]

/-- The value of an application to terms, each derivably defined with its class as value at the
generic assignment, is the operation at their representatives. -/
theorem eval_op_generic {k : ℕ} {cs : List Tree} {hs hd}
    (hev : ∀ c (h : c ∈ cs), eval (termModel T E Γ H) (generic T E Γ H) c =
      Part.some (val ⟦⟨((sortOf T.sig Γ c).get (hs c h), c), (Option.some_get _).symm,
        hd c h⟩⟧)) :
    eval (termModel T E Γ H) (generic T E Γ H) (op k cs) = opRep k (repsOf cs hs hd) := by
  have hmap : cs.map (eval (termModel T E Γ H) (generic T E Γ H)) =
      ((repsOf cs hs hd).map fun r ↦ val ⟦r⟧).map Part.some := by
    rw [repsOf, List.map_map, List.map_map]
    conv_lhs => rw [← List.attach_map_subtype_val cs, List.map_map]
    exact List.map_congr_left fun c _ ↦ hev c.1 c.2
  rw [eval_op, (mapM_part_eq_some_iff _ _).mpr hmap, Part.bind_some, op_termModel]

/-- A term of a sort, derivably defined, has its class as value at the generic assignment. -/
theorem eval_generic : ∀ t : Tree, ∀ {s : ℕ} (hs : sortOf T.sig Γ t = some s)
    (hd : Derivable T E Γ H ⟨t, t⟩),
    eval (termModel T E Γ H) (generic T E Γ H) t = Part.some (val ⟦⟨(s, t), hs, hd⟩⟧) :=
  RoseTree.ind fun l cs ih s hs hd ↦ by
    rcases l with _ | k
    · rcases cs with _ | ⟨c, _ | ⟨c', cs⟩⟩
      · simp [sortOf] at hs
      · obtain ⟨hcl, hs'⟩ := sortOf_node_zero_eq_some.mp hs
        have hv : RoseTree.node 0 [c] = var c.label := by
          rw [var, ← hcl, RoseTree.node_label_children]
        obtain ⟨hi, hΓ⟩ := List.getElem?_eq_some_iff.mp hs'
        rw [eval_node_zero hcl, getElem?_generic]
        simp only [hi, ↓reduceDIte, Part.coe_some]
        exact congrArg (fun v ↦ Part.some (val v)) (mk_congr hΓ hv.symm)
      · simp [sortOf] at hs
    · have hs' := hs
      rw [sortOf_node_succ, Option.bind_eq_some_iff] at hs'
      obtain ⟨o, -, hs'⟩ := hs'
      split_ifs at hs' with hsorts
      have hsome : ∀ c ∈ cs, (sortOf T.sig Γ c).isSome := fun c hc' ↦ by
        obtain ⟨s', -, hs'⟩ := List.mem_map.mp (hsorts ▸ List.mem_map_of_mem hc')
        rw [← hs']
        rfl
      have hder : ∀ c ∈ cs, Derivable T E Γ H ⟨c, c⟩ := fun c hc' ↦ by
        obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hc'
        exact Derivable.strict (k := k) hd hj
      have h := eval_op_generic (k := k) (hs := hsome) (hd := hder)
        fun c hc' ↦ ih c hc' (Option.some_get _).symm (hder c hc')
      have hrs : op k (terms (repsOf cs hsome hder)) = RoseTree.node (k + 1) cs :=
        congrArg (op k) terms_repsOf
      change eval _ _ (op k cs) = _
      rw [h, opRep_eq_some (hrs ▸ hs) (hrs ▸ hd)]
      exact congrArg (fun v ↦ Part.some (toVal v)) (mk_congr rfl hrs)

/-- A term defined at the generic assignment is of a sort and derivably defined, with its class
as value. -/
theorem eq_of_eval_generic : ∀ t : Tree, ∀ {w : (termModel T E Γ H).Val},
    eval (termModel T E Γ H) (generic T E Γ H) t = Part.some w →
      ∃ s, ∃ (hs : sortOf T.sig Γ t = some s) (hd : Derivable T E Γ H ⟨t, t⟩),
        w = val ⟦⟨(s, t), hs, hd⟩⟧ :=
  RoseTree.ind fun l cs ih w he ↦ by
    rcases l with _ | k
    · rcases cs with _ | ⟨c, _ | ⟨c', cs⟩⟩
      · exact absurd he (by simp [eval])
      · obtain ⟨hcl, he⟩ := eval_node_zero_eq_some.mp he
        have hv : RoseTree.node 0 [c] = var c.label := by
          rw [var, ← hcl, RoseTree.node_label_children]
        rw [getElem?_generic] at he
        split_ifs at he with hi
        · rw [Part.coe_some, Part.some_inj] at he
          subst he
          refine ⟨Γ[c.label], ?_, hv ▸ Derivable.refl hi, congrArg val (mk_congr rfl hv.symm)⟩
          rw [sortOf_node_zero _ hcl, List.getElem?_eq_getElem hi]
        · exact absurd he (by simp)
      · exact absurd he (by simp [eval])
    · have hex : ∀ c ∈ cs, ∃ w, eval (termModel T E Γ H) (generic T E Γ H) c = Part.some w := by
        rw [eval_node_succ, part_bind_eq_some_iff] at he
        obtain ⟨ws, hws, -⟩ := he
        rw [mapM_part_eq_some_iff] at hws
        intro c hc'
        obtain ⟨w', -, hw'⟩ := List.mem_map.mp (hws ▸ List.mem_map_of_mem hc')
        exact ⟨w', hw'.symm⟩
      have hih : ∀ c (_ : c ∈ cs), ∃ s, ∃ (hs : sortOf T.sig Γ c = some s)
          (hd : Derivable T E Γ H ⟨c, c⟩), eval (termModel T E Γ H) (generic T E Γ H) c =
            Part.some (val ⟦⟨(s, c), hs, hd⟩⟧) := fun c h ↦ by
        obtain ⟨w', hw'⟩ := hex c h
        obtain ⟨s, hs, hd, rfl⟩ := ih c h hw'
        exact ⟨s, hs, hd, hw'⟩
      have hsome : ∀ c ∈ cs, (sortOf T.sig Γ c).isSome := fun c h ↦ by
        obtain ⟨s, hs, -⟩ := hih c h
        rw [hs]
        rfl
      have hder : ∀ c ∈ cs, Derivable T E Γ H ⟨c, c⟩ := fun c h ↦ by
        obtain ⟨-, -, hd, -⟩ := hih c h
        exact hd
      have h := eval_op_generic (k := k) (hs := hsome) (hd := hder) fun c hc' ↦ by
        obtain ⟨s, hs, hd, hev⟩ := hih c hc'
        rw [hev]
        exact congrArg (fun v ↦ Part.some (val v))
          (mk_congr (Option.some_inj.mp (hs.symm.trans (Option.some_get _).symm)) rfl)
      change eval _ _ (op k cs) = _ at he
      rw [h] at he
      obtain ⟨s, hs, hd, rfl⟩ := eq_of_mem_opRep (Part.eq_some_iff.mp he)
      have hrs : op k (terms (repsOf cs hsome hder)) = RoseTree.node (k + 1) cs :=
        congrArg (op k) terms_repsOf
      exact ⟨s, hrs ▸ hs, hrs ▸ hd, congrArg toVal (mk_congr rfl hrs)⟩

/-- An equation holds at the generic assignment exactly when it is derivable and its sides have
one sort. -/
theorem holds_generic_iff {t u : Tree} :
    Eqn.Holds (termModel T E Γ H) (generic T E Γ H) ⟨t, u⟩ ↔
      Derivable T E Γ H ⟨t, u⟩ ∧ ∃ s, sortOf T.sig Γ t = some s ∧ sortOf T.sig Γ u = some s := by
  constructor
  · rintro ⟨w, h₁, h₂⟩
    obtain ⟨s, hs, hd, rfl⟩ := eq_of_eval_generic t h₁
    obtain ⟨s', hs', hd', he⟩ := eq_of_eval_generic u h₂
    obtain ⟨hss, htu⟩ := Quotient.exact (congrArg (fun w ↦ w.2.1) he)
    have hss' : s = s' := hss
    exact ⟨htu, s, hs, hss' ▸ hs'⟩
  · rintro ⟨htu, s, hs, hs'⟩
    exact ⟨_, eval_generic t hs htu.left, (eval_generic u hs' htu.right).trans
      (congrArg (fun v ↦ Part.some (val v)) (Quotient.sound ⟨rfl, htu.symm⟩))⟩

variable (T E Γ H) in
/-- The term model is a model of every theory whose axioms are in scope and equate terms of one
sort. -/
theorem isModel (hT : ∀ a ∈ T.axioms, a.Scoped = true ∧ SidesSorted T.sig a) :
    IsModel T (termModel T E Γ H) := by
  intro a ha σ hσ hH
  obtain ⟨hsc, s, hl, hr⟩ := hT a ha
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp ha
  obtain ⟨rs, rfl⟩ := exists_reps σ
  have hlen : (terms rs).length = a.ctx.length := by simpa [terms] using congrArg List.length hσ
  have hev : (terms rs).map (eval (termModel T E Γ H) (generic T E Γ H)) =
      (rs.map fun r ↦ val ⟦r⟧).map Part.some := by
    rw [terms, List.map_map, List.map_map]
    exact List.map_congr_left fun r _ ↦ eval_generic _ r.2.1 r.2.2
  have hsorts : (terms rs).map (sortOf T.sig Γ) = a.ctx.map some := by
    rw [← hσ, terms, List.map_map, List.map_map, List.map_map]
    exact List.map_congr_left fun r _ ↦ r.2.1
  have hsc' := hsc
  simp only [Seq.Scoped, Bool.and_eq_true, List.all_eq_true, Eqn.Scoped] at hsc'
  obtain ⟨hsh, hscl, hscr⟩ := hsc'
  rw [← hlen] at hsh hscl hscr
  have hhyp : ∀ h ∈ a.hyps, Derivable T E Γ H (h.subst (terms rs)) := fun h hh ↦ by
    obtain ⟨w, h₁, h₂⟩ := hH h hh
    obtain ⟨hl', hr'⟩ := hsh h hh
    exact (holds_generic_iff.mp
      ⟨w, (eval_subst hev _ hl').trans h₁, (eval_subst hev _ hr').trans h₂⟩).1
  have hc := Derivable.ax hj hsc hsorts (fun t ht ↦ by
    obtain ⟨r, -, rfl⟩ := List.mem_map.mp ht
    exact r.2.2) hhyp
  obtain ⟨w, h₁, h₂⟩ := holds_generic_iff.mpr
    ⟨hc, s, sortOf_subst hsorts _ hl, sortOf_subst hsorts _ hr⟩
  exact ⟨w, (eval_subst hev _ hscl).symm.trans h₁, (eval_subst hev _ hscr).symm.trans h₂⟩

/-- The hypotheses hold at the generic assignment when each equates terms of one sort. -/
theorem hyps_generic (hH : ∀ h ∈ H, SidesSorted T.sig ⟨Γ, [], h⟩) :
    ∀ h ∈ H, h.Holds (termModel T E Γ H) (generic T E Γ H) := fun h hh ↦ by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hh
  exact holds_generic_iff.mpr ⟨Derivable.hyp hi, hH h hh⟩

end Carrier

end TermModel

/-- The extensions of a theory by well-formed definitions keep its axioms in scope, and the
definitions' own are in scope. -/
theorem scoped_extendAll (ds : List Defn) :
    ∀ T : Theory, (∀ a ∈ T.axioms, a.Scoped = true) → DefnsWF T.sig ds →
      ∀ a ∈ (T.extendAll ds).axioms, a.Scoped = true :=
  ds.rec (fun _ h _ ↦ h) fun d ds ih T h hds ↦ by
    refine ih (T.extend d) (fun a ha ↦ ?_) hds.2
    rcases List.mem_append.mp ha with ha | ha
    · exact h a ha
    · have hb : Scoped d.ctx.length d.body = true := scoped_of_sortOf _ hds.1.sort
      have hv : Scoped d.ctx.length (opVars T.sig.length d.ctx.length) = true := by
        rw [opVars, op, scoped_node_succ, List.all_eq_true]
        intro c hc
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc
        rw [var]
        exact scoped_node_zero_iff.mpr ⟨rfl, List.mem_range.mp hi⟩
      simp only [Defn.axioms, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl <;>
        simp only [Seq.Scoped, Eqn.Scoped, List.all_cons, List.all_nil, hb, hv, Bool.and_self]

open TermModel in
/-- Completeness: an equation that holds in every model of a theory whose axioms are in scope
and equate terms of one sort, under hypotheses each equating terms of one sort, is derivable. -/
theorem derivable_of_valid {T : Theory} {E : Array Seq}
    (hT : ∀ a ∈ T.axioms, a.Scoped = true ∧ SidesSorted T.sig a) {Γ : List ℕ} {H : List Eqn}
    (hH : ∀ h ∈ H, SidesSorted T.sig ⟨Γ, [], h⟩) {q : Eqn}
    (hv : ∀ M : Model.{0} T.sig, IsModel T M → Valid M Γ H q) : Derivable T E Γ H q :=
  (holds_generic_iff.mp (hv _ (isModel T E Γ H hT) _ generic_sorts (hyps_generic hH))).1

/-- Completeness and soundness: under the hypotheses of completeness, with an environment of
theorems valid in every model of the theory, an equation is derivable exactly when it is valid
in every model of the theory. -/
theorem derivable_iff_valid {T : Theory} {E : Array Seq}
    (hE : ∀ M : Model.{0} T.sig, IsModel T M → ∀ a ∈ E, a.Valid M)
    (hT : ∀ a ∈ T.axioms, a.Scoped = true ∧ SidesSorted T.sig a) {Γ : List ℕ} {H : List Eqn}
    (hH : ∀ h ∈ H, SidesSorted T.sig ⟨Γ, [], h⟩) {q : Eqn} :
    Derivable T E Γ H q ↔ ∀ M : Model.{0} T.sig, IsModel T M → Valid M Γ H q :=
  ⟨fun ⟨c, hc⟩ M hM ↦ check_sound (List.prefix_refl _) hM (hE M hM) c Γ H q hc,
    derivable_of_valid hT hH⟩

end Geb.PartialHorn

end
