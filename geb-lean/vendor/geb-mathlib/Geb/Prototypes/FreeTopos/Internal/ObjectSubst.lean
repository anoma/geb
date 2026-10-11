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
# The substitution of objects by a function

The substitution of objects for the object variables of a type
({name}`Geb.PartialHorn.subst`) replaces the variable of index {lit}`i` by the object at
position {lit}`i` of a list and leaves a variable past the list in place. Its generalization to a
function of the index ({lit}`substF`), and to the types of a term's labels ({lit}`Term.osubstF`),
composes without a bound on the variables: the substitution by a function after the substitution
by another is the substitution by the second's values substituted by the first
({lit}`substF_comp`, {lit}`Term.osubstF_comp`), the substitution of each variable for itself is the
identity, and the substitution by a list is the substitution by the function of its positions.
Substitutions that agree below the number of object variables substitute alike in a type in
their scope and in a term that compiles with them.

## Main definitions

* {lit}`substF` — the substitution of objects for the variables of a type, by a function.
* {lit}`Label.osubstF`, {lit}`Term.osubstF` — the substitution in a label's types and in a term's.

## Main statements

* {lit}`substF_comp`, {lit}`Term.osubstF_comp` — the composition of substitutions.
* {lit}`Term.osubst_eq_osubstF` — the substitution by a list is the substitution by a function.
* {lit}`Term.osubstF_congr_of_compile` — substitutions agreeing below the object variables agree
  on a term that compiles.

## Tags

internal language, object variable, substitution, composition
-/

set_option doc.verso true

@[expose] public section

namespace Geb.FreeTopos.Internal

open PartialHorn (Tree)

/-- A list of two or more elements is not of one. -/
theorem cons_cons_ne_singleton {α : Type} {a b x : α} {l : List α} : a :: b :: l ≠ [x] :=
  fun h ↦ Nat.succ_ne_zero _ (Nat.succ.inj (congrArg List.length h))

/-- The empty list is not of one element. -/
theorem nil_ne_singleton {α : Type} {x : α} : ([] : List α) ≠ [x] :=
  fun h ↦ Nat.succ_ne_zero _ (congrArg List.length h).symm

/-- The substitution of a type for each variable of a type, given by a function of the variable's
index; a node of label zero that is not a variable is left in place. -/
def substF (τ : ℕ → Tree) : Tree → Tree :=
  RoseTree.para fun l cs ↦ match l, cs with
    | 0, [(i, _)] => if i.children.isEmpty then τ i.label else RoseTree.node 0 [i]
    | l, cs => RoseTree.node l (cs.map Prod.snd)

/-- The substitution by a list is the substitution by the function of its positions. -/
theorem subst_eq_substF (ts : List Tree) :
    PartialHorn.subst ts = substF fun i ↦ ts[i]?.getD (PartialHorn.var i) :=
  rfl

/-- The substitution at a variable's node. -/
theorem substF_node_zero (τ : ℕ → Tree) {i : Tree} (hi : i.children = []) :
    substF τ (RoseTree.node 0 [i]) = τ i.label := by
  rw [substF, RoseTree.para_node]
  simp only [List.map_cons, List.map_nil, hi, List.isEmpty_nil, ↓reduceIte]

/-- The substitution leaves a node of label zero over a child that is not a leaf in place. -/
theorem substF_node_zero_of_not (τ : ℕ → Tree) {i : Tree} (hi : i.children ≠ []) :
    substF τ (RoseTree.node 0 [i]) = RoseTree.node 0 [i] := by
  rw [substF, RoseTree.para_node]
  simp only [List.map_cons, List.map_nil]
  rw [if_neg (by rwa [List.isEmpty_iff])]

/-- The substitution at an operation's node substitutes in the arguments. -/
theorem substF_node_succ (τ : ℕ → Tree) (k : ℕ) (cs : List Tree) :
    substF τ (RoseTree.node (k + 1) cs) = RoseTree.node (k + 1) (cs.map (substF τ)) := by
  rw [substF, RoseTree.para_node]
  change RoseTree.node (k + 1) ((cs.map fun c ↦ (c, substF τ c)).map Prod.snd) = _
  rw [List.map_map]
  rfl

/-- The substitution at a variable is the variable's value. -/
theorem substF_var (τ : ℕ → Tree) (i : ℕ) : substF τ (PartialHorn.var i) = τ i :=
  substF_node_zero τ rfl

/-- The substitution at a node of label zero over other than one child substitutes in each. -/
theorem substF_node_zero_other (τ : ℕ → Tree) {cs : List Tree} (hcs : ∀ i, cs ≠ [i]) :
    substF τ (RoseTree.node 0 cs) = RoseTree.node 0 (cs.map (substF τ)) := by
  rw [substF, RoseTree.para_node]
  rcases cs with _ | ⟨i, _ | ⟨j, cs⟩⟩
  · rfl
  · exact _root_.absurd rfl (hcs i)
  · change RoseTree.node 0 (((i :: j :: cs).map fun c ↦ (c, substF τ c)).map Prod.snd) = _
    rw [List.map_map]
    rfl

/-- The substitution by a function after the substitution by another is the substitution by the
second's values substituted by the first. -/
theorem substF_comp (τ₁ τ₂ : ℕ → Tree) :
    ∀ t : Tree, substF τ₂ (substF τ₁ t) = substF (fun i ↦ substF τ₂ (τ₁ i)) t :=
  RoseTree.ind fun l cs ih ↦ by
    rcases l with _ | k
    · rcases cs with _ | ⟨i, _ | ⟨i', cs⟩⟩
      · rfl
      · by_cases hi : i.children = []
        · rw [substF_node_zero _ hi, substF_node_zero _ hi]
        · rw [substF_node_zero_of_not _ hi, substF_node_zero_of_not _ hi,
            substF_node_zero_of_not _ hi]
      · have hcs' : ∀ c, i :: i' :: cs ≠ [c] := fun _ ↦ cons_cons_ne_singleton
        have hm : ∀ c, (i :: i' :: cs).map (substF τ₁) ≠ [c] := fun _ ↦ cons_cons_ne_singleton
        rw [substF_node_zero_other τ₁ hcs', substF_node_zero_other τ₂ hm,
          substF_node_zero_other _ hcs', List.map_map]
        exact congrArg _ (List.map_congr_left fun c hc ↦ ih c hc)
    · rw [substF_node_succ, substF_node_succ, substF_node_succ, List.map_map]
      exact congrArg _ (List.map_congr_left fun c hc ↦ ih c hc)

/-- The substitution of each variable for itself leaves a type in place. -/
theorem substF_var_id : ∀ t : Tree, substF PartialHorn.var t = t :=
  RoseTree.ind fun l cs ih ↦ by
    rcases l with _ | k
    · rcases cs with _ | ⟨i, _ | ⟨i', cs⟩⟩
      · rfl
      · by_cases hi : i.children = []
        · rw [substF_node_zero _ hi, PartialHorn.var, ← RoseTree.node_label_children i, hi,
            RoseTree.label_node]
        · exact substF_node_zero_of_not _ hi
      · rw [substF_node_zero_other _ fun _ ↦ cons_cons_ne_singleton]
        exact congrArg _ ((List.map_congr_left ih).trans (List.map_id _))
    · rw [substF_node_succ]
      exact congrArg _ ((List.map_congr_left ih).trans (List.map_id cs))

/-- Substitutions that agree below a bound substitute alike in a type in scope below it. -/
theorem substF_congr {n : ℕ} {τ τ' : ℕ → Tree} (h : ∀ i < n, τ i = τ' i) :
    ∀ t : Tree, PartialHorn.Scoped n t = true → substF τ t = substF τ' t :=
  RoseTree.ind fun l cs ih ht ↦ by
    rcases l with _ | k
    · rcases cs with _ | ⟨i, _ | ⟨j, cs⟩⟩
      · rfl
      · obtain ⟨hi, hlt⟩ := PartialHorn.scoped_node_zero_iff.mp ht
        rw [substF_node_zero _ hi, substF_node_zero _ hi]
        exact h _ hlt
      · exact _root_.absurd ht (by simp [PartialHorn.Scoped])
    · rw [PartialHorn.scoped_node_succ, List.all_eq_true] at ht
      rw [substF_node_succ, substF_node_succ]
      exact congrArg _ (List.map_congr_left fun c hc ↦ ih c hc (ht c hc))

/-- The substitution of an object for the object variable of index {lit}`x`, the variables
above it lowered by one. -/
def objAt (x : ℕ) (b : Tree) : ℕ → Tree := fun y ↦
  if y < x then PartialHorn.var y else if y = x then b else PartialHorn.var (y - 1)

/-- The raising of the object variables of a type by {lit}`q`. -/
def shiftObj (q : ℕ) (b : Tree) : Tree := substF (fun z ↦ PartialHorn.var (z + q)) b

/-- The substitution of a list of objects, the first outermost, for the object variables of a
scope as long as the list, the variables past the scope lowered past it. -/
def objScope (bs : List Tree) : ℕ → Tree := fun z ↦
  if z < bs.length then bs.reverse[z]?.getD (PartialHorn.var z)
  else PartialHorn.var (z - bs.length)

/-- The substitution for the scope of no objects is the identity. -/
theorem objScope_nil : objScope [] = PartialHorn.var := funext fun z ↦ by
  simp only [objScope, List.length_nil, Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero]

/-- The substitution for the scope of a list of objects, after the substitution of the first,
raised past the rest, for the outermost variable of the scope. -/
theorem objScope_cons (b : Tree) (bs : List Tree) (z : ℕ) :
    substF (objScope bs) (objAt bs.length (shiftObj bs.length b) z) = objScope (b :: bs) z := by
  unfold objAt
  by_cases hlt : z < bs.length
  · rw [if_pos hlt, substF_var, objScope, objScope, if_pos hlt,
      if_pos (by rw [List.length_cons]; omega), List.reverse_cons,
      List.getElem?_append_left (by rw [List.length_reverse]; exact hlt)]
  · by_cases heq : z = bs.length
    · subst heq
      rw [if_neg hlt, if_pos rfl, shiftObj, substF_comp, objScope,
        if_pos (by rw [List.length_cons]; omega), List.reverse_cons,
        List.getElem?_append_right (by rw [List.length_reverse]), List.length_reverse,
        Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
      refine Eq.trans (congrArg (substF · b) (funext fun w ↦ ?_)) (substF_var_id b)
      rw [substF_var, objScope, if_neg (by omega), Nat.add_sub_cancel]
    · rw [if_neg hlt, if_neg heq, substF_var, objScope, objScope,
        if_neg (by omega), if_neg (by rw [List.length_cons]; omega),
        List.length_cons, show z - 1 - bs.length = z - (bs.length + 1) by omega]

/-- The substitution of objects, by a function, in the types and arrows of a label. -/
def Label.osubstF (τ : ℕ → Tree) : Label → Label
  | .lam a => .lam (substF τ a)
  | .arr k θ' => .arr k (θ'.map (substF τ))
  | .roseRec c => .roseRec (substF τ c)
  | .defn k θ' => .defn k (θ'.map (substF τ))
  | l => l

/-- The substitution of objects, by a function, in the types and arrows of a term. -/
def Term.osubstF (τ : ℕ → Tree) : Term → Term :=
  RoseTree.elim fun l cs ↦ RoseTree.node (l.osubstF τ) cs

/-- The substitution of objects in a node substitutes in its label and its children. -/
theorem Term.osubstF_node (τ : ℕ → Tree) (l : Label) (cs : List Term) :
    Term.osubstF τ (RoseTree.node l cs) =
      RoseTree.node (l.osubstF τ) (cs.map (Term.osubstF τ)) :=
  RoseTree.elim_node _ l cs

/-- The substitution by a list in a label is the substitution by the function of its positions. -/
theorem Label.osubst_eq_osubstF (θ : List Tree) (l : Label) :
    l.osubst θ = l.osubstF fun i ↦ θ[i]?.getD (PartialHorn.var i) := by
  cases l <;> rfl

/-- The substitution by a list in a term is the substitution by the function of its positions. -/
theorem Term.osubst_eq_osubstF (θ : List Tree) :
    ∀ t : Term, Term.osubst θ t = Term.osubstF (fun i ↦ θ[i]?.getD (PartialHorn.var i)) t :=
  RoseTree.ind fun l cs ih ↦ by
    rw [Term.osubst_node, Term.osubstF_node, Label.osubst_eq_osubstF]
    exact congrArg _ (List.map_congr_left ih)

/-- The substitution in a label after another is the substitution by the composite. -/
theorem Label.osubstF_comp (τ₁ τ₂ : ℕ → Tree) (l : Label) :
    (l.osubstF τ₁).osubstF τ₂ = l.osubstF fun i ↦ substF τ₂ (τ₁ i) := by
  cases l <;> simp only [Label.osubstF, substF_comp, List.map_map, Function.comp_def]

/-- The substitution in a term after another is the substitution by the composite. -/
theorem Term.osubstF_comp (τ₁ τ₂ : ℕ → Tree) :
    ∀ t : Term, Term.osubstF τ₂ (Term.osubstF τ₁ t) =
      Term.osubstF (fun i ↦ substF τ₂ (τ₁ i)) t :=
  RoseTree.ind fun l cs ih ↦ by
    rw [Term.osubstF_node, Term.osubstF_node, Term.osubstF_node, Label.osubstF_comp, List.map_map]
    exact congrArg _ (List.map_congr_left ih)

/-- The substitution of each variable for itself leaves a label in place. -/
theorem Label.osubstF_var (l : Label) : l.osubstF PartialHorn.var = l := by
  have h : substF PartialHorn.var = id := funext substF_var_id
  cases l <;> simp only [Label.osubstF, h, List.map_id, id]

/-- The substitution of each variable for itself leaves a term in place. -/
theorem Term.osubstF_var : ∀ t : Term, Term.osubstF PartialHorn.var t = t :=
  RoseTree.ind fun l cs ih ↦ by
    rw [Term.osubstF_node, Label.osubstF_var]
    exact congrArg _ ((List.map_congr_left ih).trans (List.map_id cs))

/-- The test of occurrence at a node depends on the children's tests alone. -/
theorem occursStep_snd (l : Label) (xs : List (Term × (ℕ → Bool))) :
    Term.occursStep l xs = Term.occursStep l (xs.map fun p ↦ (Term.star, p.2)) := by
  rcases xs with _ | ⟨⟨_, _⟩, _ | ⟨⟨_, _⟩, _ | ⟨⟨_, _⟩, _ | ⟨⟨_, _⟩, xs⟩⟩⟩⟩ <;> cases l <;>
    first
      | rfl
      | (funext d
         simp only [Term.occursStep, List.map_cons, List.any_cons, List.any_map,
           Function.comp_def])

/-- The test of occurrence at a node does not depend on the types of its label. -/
theorem occursStep_osubstF (τ : ℕ → Tree) (l : Label) (xs : List (Term × (ℕ → Bool))) :
    Term.occursStep (l.osubstF τ) xs = Term.occursStep l xs := by
  rcases xs with _ | ⟨⟨_, _⟩, _ | ⟨⟨_, _⟩, _ | ⟨⟨_, _⟩, _ | ⟨⟨_, _⟩, xs⟩⟩⟩⟩ <;> cases l <;> rfl

/-- The substitution of objects leaves the variables a term mentions. -/
theorem Term.occurs_osubstF (τ : ℕ → Tree) :
    ∀ t : Term, Term.occurs (Term.osubstF τ t) = Term.occurs t :=
  RoseTree.ind fun l cs ih ↦ funext fun d ↦ by
    rw [Term.osubstF_node, Term.occurs_node, Term.occurs_node, occursStep_osubstF,
      occursStep_snd l ((cs.map (Term.osubstF τ)).map fun c ↦ (c, Term.occurs c)),
      occursStep_snd l (cs.map fun c ↦ (c, Term.occurs c)), List.map_map, List.map_map,
      List.map_map]
    exact congrArg (fun xs ↦ Term.occursStep l xs d)
      (List.map_congr_left fun c hc ↦ by simp only [Function.comp_apply, ih c hc])

/-- A label substituted in is a variable exactly when it is. -/
theorem Label.osubstF_eq_var {τ : ℕ → Tree} {l : Label} {i : ℕ} (h : l.osubstF τ = .var i) :
    l = .var i := by
  cases l <;> first | exact h | exact nomatch h

/-- The substitution of objects keeps a term's variables leaves. -/
theorem Term.varLeaves_osubstF (τ : ℕ → Tree) :
    ∀ t : Term, Term.VarLeaves t = true → Term.VarLeaves (Term.osubstF τ t) = true :=
  RoseTree.ind fun l cs ih ht ↦ by
    obtain ⟨hv, hcs⟩ := (Term.varLeaves_node l cs).mp ht
    rw [Term.osubstF_node]
    refine (Term.varLeaves_node _ _).mpr ⟨fun i hi ↦ ?_, fun x hx ↦ ?_⟩
    · rw [hv i (Label.osubstF_eq_var hi), List.map_nil]
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
      exact ih c hc (hcs c hc)

/-- Substitutions that agree below the number of object variables substitute alike in a term that
compiles with them. -/
theorem Term.osubstF_congr_of_compile {G : Globals} {n : ℕ} {τ τ' : ℕ → Tree}
    (hτ : ∀ i < n, τ i = τ' i) (s : Term) :
    ∀ (X : Tree) (e : List (Tree × Tree)) (r : Tree × Tree), compile G n s X e = some r →
      Term.osubstF τ s = Term.osubstF τ' s := by
  refine RoseTree.ind (P := fun s ↦ ∀ (X : Tree) (e : List (Tree × Tree)) (r : Tree × Tree),
    compile G n s X e = some r → Term.osubstF τ s = Term.osubstF τ' s) (fun l cs ih ↦ ?_) s
  intro X e r h
  have node : l.osubstF τ = l.osubstF τ' → (∀ c ∈ cs, ∃ X e r, compile G n c X e = some r) →
      Term.osubstF τ (RoseTree.node l cs) = Term.osubstF τ' (RoseTree.node l cs) :=
    fun hl hc ↦ by
      rw [Term.osubstF_node, Term.osubstF_node, hl]
      exact congrArg _ (List.map_congr_left fun c hc' ↦
        let ⟨X, e, r, h⟩ := hc c hc'
        ih c hc' X e r h)
  have ty : ∀ a, IsTy G n a = true → substF τ a = substF τ' a := fun a ha ↦
    substF_congr hτ a (scoped_of_isTy (G := G) a ha)
  have tys : ∀ θ : List Tree, θ.all (IsTy G n) = true → θ.map (substF τ) = θ.map (substF τ') :=
    fun θ hθ ↦ List.map_congr_left fun a ha ↦ ty a (List.all_eq_true.mp hθ a ha)
  cases l with
  | var i =>
    obtain ⟨rfl, -⟩ := compile_var_iff.mp h
    exact node rfl (by simp)
  | star =>
    obtain ⟨rfl, -⟩ := compile_star_iff.mp h
    exact node rfl (by simp)
  | pair =>
    obtain ⟨t, u, f, a, g, b, rfl, ht, hu, -⟩ := compile_pair_iff.mp h
    exact node rfl (by simpa using ⟨⟨_, _, _, _, ht⟩, ⟨_, _, _, _, hu⟩⟩)
  | fst =>
    obtain ⟨t, f, a, b, rfl, ht, -⟩ := compile_fst_iff.mp h
    exact node rfl (by simpa using ⟨_, _, _, _, ht⟩)
  | snd =>
    obtain ⟨t, f, a, b, rfl, ht, -⟩ := compile_snd_iff.mp h
    exact node rfl (by simpa using ⟨_, _, _, _, ht⟩)
  | lam a =>
    obtain ⟨t, f, b, rfl, ha, ht, -⟩ := compile_lam_iff.mp h
    exact node (congrArg Label.lam (ty a ha)) (by simpa using ⟨_, _, _, _, ht⟩)
  | app =>
    obtain ⟨t, u, rfl, f, a, b, ht, g, hu, -⟩ := compile_app_iff.mp h
    exact node rfl (by simpa using ⟨⟨_, _, _, _, ht⟩, ⟨_, _, _, _, hu⟩⟩)
  | arr k θ =>
    obtain ⟨t, rfl, p, -, g, ht, -, hθ, -⟩ := compile_arr_iff.mp h
    exact node (congrArg (Label.arr k) (tys θ hθ)) (by simpa using ⟨_, _, _, _, ht⟩)
  | natRec =>
    obtain ⟨z, s, m, rfl, z', c, hz, s', hs, m', hm, -⟩ := compile_natRec_iff.mp h
    exact node rfl (by simpa using ⟨⟨_, _, _, _, hz⟩, ⟨_, _, _, _, hs⟩, ⟨_, _, _, _, hm⟩⟩)
  | listRec =>
    obtain ⟨z, s, m, rfl, m', a, hm, z', c, hz, s', hs, -⟩ := compile_listRec_iff.mp h
    exact node rfl (by simpa using ⟨⟨_, _, _, _, hz⟩, ⟨_, _, _, _, hs⟩, ⟨_, _, _, _, hm⟩⟩)
  | roseRec c =>
    obtain ⟨s, m, m', t, a, F, s', rfl, hc, hm, -, hs, -⟩ := compile_roseRec_iff.mp h
    exact node (congrArg Label.roseRec (ty c hc))
      (by simpa using ⟨⟨_, _, _, _, hs⟩, ⟨_, _, _, _, hm⟩⟩)
  | defn k θ =>
    obtain ⟨d, rs, -, hrs, -, hθ, -⟩ := compile_defn_iff.mp h
    refine node (congrArg (Label.defn k) (tys θ hθ)) fun c hc ↦ ?_
    rw [PartialHorn.mapM_eq_some_iff] at hrs
    obtain ⟨r', -, hr'⟩ := List.mem_map.mp (hrs ▸ List.mem_map_of_mem hc :
      compile G n c X e ∈ rs.map some)
    exact ⟨X, e, r', hr'.symm⟩
  | eq =>
    obtain ⟨t, u, rfl, f, a, ht, g, hu, -⟩ := compile_eq_iff.mp h
    exact node rfl (by simpa using ⟨⟨_, _, _, _, ht⟩, ⟨_, _, _, _, hu⟩⟩)

end Geb.FreeTopos.Internal

end
