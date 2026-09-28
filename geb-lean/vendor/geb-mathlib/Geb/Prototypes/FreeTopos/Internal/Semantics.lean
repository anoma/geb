/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Coproducts
public import Geb.Prototypes.FreeTopos.Internal.Inversion

set_option doc.verso true in
/-!
# The semantics of the compilation

The compilation of the internal language's terms is compositional, sound and natural in every
model of the theory extended by definitions. The value of a term's arrow depends only on the
values of its environment's arrows ({lit}`compile_envEq`). A term's arrow is an arrow from the
environment's object to the term's type when the environment's arrows, the primitive arrows and
the definitions' operations are arrows ({lit}`compile_hom`). In an environment whose arrows are
precomposed with an arrow, a term's arrow is precomposed with it ({lit}`compile_comp`), the
naturality of the interpretation of Part I of \[LambekScott1986\]; its case of abstraction is
the naturality of currying ({name}`Geb.FreeTopos.curry_comp`).

## Main definitions

* {lit}`EnvEq` — two environments of the same types whose arrows have equal values.
* {lit}`EnvHom` — an environment of arrows from an object.
* {lit}`PrimsHom`, {lit}`DefsHom`, {lit}`ObjsHom` — the primitive arrows and the definitions'
  operations are arrows, and the object definitions' operations take objects to objects.

## Main statements

* {lit}`compile_envEq` — the compilation respects environments of equal values.
* {lit}`compile_hom` — the compilation is sound for typing.
* {lit}`compile_comp` — the compilation is natural.

## References

* \[LambekScott1986\], Part I, for the interpretation of the typed λ-calculus in a
  cartesian closed category.

## Tags

internal language, categorical semantics, compositionality
-/

set_option doc.verso true

@[expose] public section

namespace Geb.FreeTopos.Internal

open PartialHorn (Tree op eval Model IsModel)
open Sorts
open scoped FinEnum

universe v

/-- A result of a second partial function at each element of a list, related to the first's,
lifts to the lists of results. -/
theorem mapM_lift {α β γ : Type} {f : α → Option β} {g : α → Option γ} {R : β → γ → Prop}
    (l : List α) : ∀ {rs : List β}, l.mapM f = some rs →
      (∀ a ∈ l, ∀ r, f a = some r → ∃ r', g a = some r' ∧ R r r') →
      ∃ rs', l.mapM g = some rs' ∧ List.Forall₂ R rs rs' :=
  l.rec (motive := fun l ↦ ∀ {rs : List β}, l.mapM f = some rs →
      (∀ a ∈ l, ∀ r, f a = some r → ∃ r', g a = some r' ∧ R r r') →
      ∃ rs', l.mapM g = some rs' ∧ List.Forall₂ R rs rs')
    (fun h _ ↦ by
      obtain rfl : [] = _ := by simpa using h
      exact ⟨[], rfl, .nil⟩)
    (fun a l ih rs h hfg ↦ by
      simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at h
      obtain ⟨r, hr, rs₀, hrs₀, rfl⟩ := h
      obtain ⟨r', hr', hR⟩ := hfg a List.mem_cons_self r hr
      obtain ⟨rs', hrs', hR'⟩ := ih hrs₀ fun a' ha' ↦ hfg a' (List.mem_cons_of_mem _ ha')
      exact ⟨r' :: rs', by simp [List.mapM_cons, hr', hrs'], .cons hR hR'⟩)

section Congruence

variable {defs : List PartialHorn.Defn} {M : Model.{v} (ext defs).sig} {ρ : List M.Val}

variable (M ρ) in
/-- Two results of the same type whose arrows have equal values. -/
def ResEq (r r' : Tree × Tree) : Prop := r'.2 = r.2 ∧ eval M ρ r'.1 = eval M ρ r.1

variable (M ρ) in
/-- Two environments, each variable of the first of the same type in the second, with an arrow
of equal value. -/
def EnvEq (e e' : List (Tree × Tree)) : Prop :=
  ∀ (i : ℕ) (p : Tree × Tree), e[i]? = some p → ∃ q, e'[i]? = some q ∧ ResEq M ρ p q

/-- Results related pointwise have the same types. -/
theorem map_snd_of_forall₂ {rs rs' : List (Tree × Tree)} (h : List.Forall₂ (ResEq M ρ) rs rs') :
    rs'.map Prod.snd = rs.map Prod.snd :=
  h.rec (motive := fun rs rs' _ ↦ rs'.map Prod.snd = rs.map Prod.snd) rfl
    fun hr _ ih ↦ by simp [hr.1, ih]

/-- Tuples of arrows related pointwise have equal values. -/
theorem eval_tuple_of_forall₂ (X : Tree) {rs rs' : List (Tree × Tree)}
    (h : List.Forall₂ (ResEq M ρ) rs rs') :
    eval M ρ (tuple X (rs'.map Prod.fst)) = eval M ρ (tuple X (rs.map Prod.fst)) :=
  h.rec (motive := fun rs rs' _ ↦
      eval M ρ (tuple X (rs'.map Prod.fst)) = eval M ρ (tuple X (rs.map Prod.fst))) rfl
    fun hr hrs ih ↦ by
      rcases hrs with _ | ⟨_, _⟩
      · exact hr.2
      · exact eval_op₂_congr 9 ih hr.2

/-- A rose-tree object's fold respects the value of its step. -/
theorem eval_roseParts_congr {t a s s' : Tree} {F : Tree → Tree} (h : roseParts t = some (a, F))
    (hs : eval M ρ s = eval M ρ s') : eval M ρ (F s) = eval M ρ (F s') := by
  rcases roseParts_eq_some.mp h with ⟨-, -, rfl⟩ | ⟨-, rfl⟩
  · exact eval_op₁_congr 39 hs
  · exact eval_op₂_congr 42 rfl hs

/-- Extending environments of equal values by a variable keeps their values equal. -/
theorem EnvEq.ext {e e' : List (Tree × Tree)} (h : EnvEq M ρ e e') (X a : Tree) :
    EnvEq M ρ (extEnv X a e) (extEnv X a e') := by
  intro i p hp
  rcases i with _ | j
  · exact ⟨p, by simpa [extEnv] using hp, rfl, rfl⟩
  · simp only [extEnv, List.getElem?_cons_succ, List.getElem?_map, Option.map_eq_some_iff] at hp
    obtain ⟨p₀, hp₀, rfl⟩ := hp
    obtain ⟨q₀, hq₀, h₂, h₁⟩ := h j p₀ hp₀
    exact ⟨(comp q₀.1 (fst X a), q₀.2), by simp [extEnv, hq₀], h₂, eval_op₂_congr 3 h₁ rfl⟩

/-- The compilation respects environments of equal values: in one whose arrows have the values
of another's, a term has the same type and an arrow of the same value. -/
theorem compile_envEq {G : Globals} {n : ℕ} (s : Term) :
    ∀ (X : Tree) (e : List (Tree × Tree)) (r : Tree × Tree), compile G n s X e = some r →
      ∀ e', EnvEq M ρ e e' → ∃ r', compile G n s X e' = some r' ∧ ResEq M ρ r r' := by
  refine RoseTree.ind (P := fun s ↦ ∀ (X : Tree) (e : List (Tree × Tree)) (r : Tree × Tree),
    compile G n s X e = some r →
      ∀ e', EnvEq M ρ e e' → ∃ r', compile G n s X e' = some r' ∧ ResEq M ρ r r')
    (fun l cs ih ↦ ?_) s
  intro X e r h e' he
  cases l with
  | var i =>
    obtain ⟨rfl, hi⟩ := compile_var_iff.mp h
    obtain ⟨q, hq, hr⟩ := he i r hi
    exact ⟨q, compile_var_iff.mpr ⟨rfl, hq⟩, hr⟩
  | star =>
    obtain ⟨rfl, rfl⟩ := compile_star_iff.mp h
    exact ⟨_, compile_star_iff.mpr ⟨rfl, rfl⟩, rfl, rfl⟩
  | pair =>
    obtain ⟨t, u, f, a, g, b, rfl, ht, hu, rfl⟩ := compile_pair_iff.mp h
    obtain ⟨⟨f', a'⟩, ht', rfl, hf⟩ := ih t (by simp) X e _ ht e' he
    obtain ⟨⟨g', b'⟩, hu', rfl, hg⟩ := ih u (by simp) X e _ hu e' he
    exact ⟨_, compile_pair_iff.mpr ⟨t, u, f', a', g', b', rfl, ht', hu', rfl⟩, rfl,
      eval_op₂_congr 9 hf hg⟩
  | fst =>
    obtain ⟨t, f, a, b, rfl, ht, rfl⟩ := compile_fst_iff.mp h
    obtain ⟨⟨f', p⟩, ht', rfl, hf⟩ := ih t (by simp) X e _ ht e' he
    exact ⟨_, compile_fst_iff.mpr ⟨t, f', a, b, rfl, ht', rfl⟩, rfl, eval_op₂_congr 3 rfl hf⟩
  | snd =>
    obtain ⟨t, f, a, b, rfl, ht, rfl⟩ := compile_snd_iff.mp h
    obtain ⟨⟨f', p⟩, ht', rfl, hf⟩ := ih t (by simp) X e _ ht e' he
    exact ⟨_, compile_snd_iff.mpr ⟨t, f', a, b, rfl, ht', rfl⟩, rfl, eval_op₂_congr 3 rfl hf⟩
  | lam a =>
    obtain ⟨t, f, b, rfl, hty, ht, rfl⟩ := compile_lam_iff.mp h
    obtain ⟨⟨f', b'⟩, ht', rfl, hf⟩ := ih t (by simp) _ _ _ ht _ (he.ext X a)
    exact ⟨_, compile_lam_iff.mpr ⟨t, f', b', rfl, hty, ht', rfl⟩, rfl,
      eval_op₃_congr 24 rfl rfl hf⟩
  | app =>
    obtain ⟨t, u, rfl, f, a, b, ht, g, hu, rfl⟩ := compile_app_iff.mp h
    obtain ⟨⟨f', p⟩, ht', rfl, hf⟩ := ih t (by simp) X e _ ht e' he
    obtain ⟨⟨g', a'⟩, hu', rfl, hg⟩ := ih u (by simp) X e _ hu e' he
    exact ⟨_, compile_app_iff.mpr ⟨t, u, rfl, f', a', b, ht', g', hu', rfl⟩, rfl,
      eval_op₂_congr 3 rfl (eval_op₂_congr 9 hf hg)⟩
  | arr k θ =>
    obtain ⟨t, rfl, p, hp, g, ht, hl, hθ, rfl⟩ := compile_arr_iff.mp h
    obtain ⟨⟨g', d'⟩, ht', rfl, hg⟩ := ih t (by simp) X e _ ht e' he
    exact ⟨_, compile_arr_iff.mpr ⟨t, rfl, p, hp, g', ht', hl, hθ, rfl⟩, rfl,
      eval_op₂_congr 3 rfl hg⟩
  | natRec =>
    obtain ⟨z, s, m, rfl, z', c, hz, s', hs, m', hm, rfl⟩ := compile_natRec_iff.mp h
    obtain ⟨⟨m'', t⟩, hm', rfl, hmv⟩ := ih m (by simp) X e _ hm e' he
    exact ⟨_, compile_natRec_iff.mpr ⟨z, s, m, rfl, z', c, hz, s', hs, m'', hm', rfl⟩, rfl,
      eval_op₂_congr 3 rfl hmv⟩
  | listRec =>
    obtain ⟨z, s, m, rfl, m', a, hm, z', c, hz, s', hs, rfl⟩ := compile_listRec_iff.mp h
    obtain ⟨⟨m'', t⟩, hm', rfl, hmv⟩ := ih m (by simp) X e _ hm e' he
    exact ⟨_, compile_listRec_iff.mpr ⟨z, s, m, rfl, m'', a, hm', z', c, hz, s', hs, rfl⟩, rfl,
      eval_op₂_congr 3 rfl hmv⟩
  | roseRec c =>
    obtain ⟨s, m, m', t, a, F, s', rfl, hc, hm, ht, hs, rfl⟩ := compile_roseRec_iff.mp h
    obtain ⟨⟨m'', t'⟩, hm', rfl, hmv⟩ := ih m (by simp) X e _ hm e' he
    exact ⟨_, compile_roseRec_iff.mpr ⟨s, m, m'', _, a, F, s', rfl, hc, hm', ht, hs, rfl⟩, rfl,
      eval_op₂_congr 3 rfl hmv⟩
  | eq =>
    obtain ⟨t, u, rfl, f, a, ht, g, hu, rfl⟩ := compile_eq_iff.mp h
    obtain ⟨⟨f', a'⟩, ht', rfl, hf⟩ := ih t (by simp) X e _ ht e' he
    obtain ⟨⟨g', b'⟩, hu', rfl, hg⟩ := ih u (by simp) X e _ hu e' he
    exact ⟨_, compile_eq_iff.mpr ⟨_, _, rfl, f', _, ht', g', hu', rfl⟩, rfl,
      eval_op₂_congr 3 rfl (eval_op₂_congr 9 hf hg)⟩
  | defn k θ =>
    obtain ⟨d, rs, hd, hrs, hl, hθ, hty, rfl⟩ := compile_defn_iff.mp h
    obtain ⟨rs', hrs', hR⟩ := mapM_lift (g := fun c ↦ compile G n c X e') cs hrs
      fun c hc r hr ↦ ih c hc X e r hr e' he
    exact ⟨_, compile_defn_iff.mpr ⟨d, rs', hd, hrs', hl, hθ,
      (map_snd_of_forall₂ hR).trans hty, rfl⟩, rfl,
      eval_op₂_congr 3 rfl (eval_tuple_of_forall₂ X hR)⟩

end Congruence

/-- An element of a list of results of a partial function over a list is its value at an
element. -/
theorem exists_of_mapM {α β : Type} {f : α → Option β} {l : List α} {rs : List β}
    (h : l.mapM f = some rs) {r : β} (hr : r ∈ rs) : ∃ a ∈ l, f a = some r := by
  rw [PartialHorn.mapM_eq_some_iff] at h
  obtain ⟨a, ha, he⟩ := List.mem_map.mp (h ▸ List.mem_map_of_mem hr : some r ∈ l.map f)
  exact ⟨a, ha, he⟩

section Types

variable {G : Globals}

/-- Whether a type is one: the equation of the type operations. -/
theorem isTy_op (n k : ℕ) (cs : List Tree) :
    IsTy G n (op k cs) = (G.isTyOp k cs.length && cs.all (IsTy G n)) := by
  simp only [IsTy, op, RoseTree.para_node, List.length_map]
  rw [List.all_map]
  rfl

/-- A node of label zero over one child is a type exactly when the child is a leaf whose label
is below the number of object variables. -/
theorem isTy_var_node_iff {n : ℕ} {i : Tree} :
    IsTy G n (RoseTree.node 0 [i]) = true ↔ i.children = [] ∧ i.label < n := by
  simp [IsTy]

/-- A variable is a type when its index is below the number of object variables. -/
theorem isTy_var {n i : ℕ} : IsTy G n (PartialHorn.var i) = true ↔ i < n :=
  isTy_var_node_iff.trans (by simp)

/-- A product of types is a type. -/
theorem isTy_prod {n : ℕ} {a b : Tree} : IsTy G n (prod a b) = (IsTy G n a && IsTy G n b) := by
  simp [prod, isTy_op, Globals.isTyOp, tyOps]

/-- A coproduct of types is a type. -/
theorem isTy_coprod {n : ℕ} {a b : Tree} : IsTy G n (coprod a b) = (IsTy G n a && IsTy G n b) := by
  simp [coprod, isTy_op, Globals.isTyOp, tyOps]

/-- An exponential of types is a type. -/
theorem isTy_exp {n : ℕ} {a b : Tree} : IsTy G n (exp a b) = (IsTy G n a && IsTy G n b) := by
  simp [exp, isTy_op, Globals.isTyOp, tyOps]

/-- A list object of a type is a type. -/
theorem isTy_list {n : ℕ} {a : Tree} : IsTy G n (list a) = IsTy G n a := by
  simp [list, isTy_op, Globals.isTyOp, tyOps]

/-- A rose-tree object over a type of labels is a type. -/
theorem isTy_lrose {n : ℕ} {a : Tree} : IsTy G n (lrose a) = IsTy G n a := by
  simp [lrose, isTy_op, Globals.isTyOp, tyOps]

/-- A rose-tree object's type of labels is a type where the object is. -/
theorem isTy_of_roseParts {n : ℕ} {t a : Tree} {F : Tree → Tree} (h : roseParts t = some (a, F))
    (ht : IsTy G n t = true) : IsTy G n a = true := by
  rcases roseParts_eq_some.mp h with ⟨-, rfl, -⟩ | ⟨rfl, -⟩
  · simp [nat, isTy_op, Globals.isTyOp, tyOps]
  · simpa [isTy_lrose] using ht

/-- The terminal object is a type. -/
theorem isTy_one {n : ℕ} : IsTy G n one = true := by simp [one, isTy_op, Globals.isTyOp, tyOps]

/-- The initial object is a type. -/
theorem isTy_zero {n : ℕ} : IsTy G n zero = true := by simp [zero, isTy_op, Globals.isTyOp, tyOps]

/-- The subobject classifier is a type. -/
theorem isTy_omega {n : ℕ} : IsTy G n omega = true := by
  simp [omega, isTy_op, Globals.isTyOp, tyOps]

/-- The natural numbers object is a type. -/
theorem isTy_nat {n : ℕ} : IsTy G n nat = true := by simp [nat, isTy_op, Globals.isTyOp, tyOps]

/-- The rose-tree object is a type. -/
theorem isTy_rose {n : ℕ} : IsTy G n rose = true := by simp [rose, isTy_op, Globals.isTyOp, tyOps]

/-- A type in {lit}`m` object variables, with types in {lit}`n` substituted for them, is a type in
{lit}`n`. -/
theorem isTy_subst {m n : ℕ} {θ : List Tree} (hl : θ.length = m) (hθ : θ.all (IsTy G n) = true) :
    ∀ A : Tree, IsTy G m A = true → IsTy G n (PartialHorn.subst θ A) = true :=
  RoseTree.ind fun l cs ih hA ↦ by
    rcases l with _ | k
    · rcases cs with _ | ⟨i, _ | ⟨j, cs⟩⟩
      · simp [IsTy] at hA
      rotate_left
      · simp [IsTy] at hA
      obtain ⟨hc, hA⟩ := isTy_var_node_iff.mp hA
      rw [PartialHorn.subst_node_zero _ hc]
      have hi : i.label < θ.length := hl ▸ hA
      rw [List.getElem?_eq_getElem hi, Option.getD_some]
      exact List.all_eq_true.mp hθ _ (List.getElem_mem hi)
    · change IsTy G m (op k cs) = true at hA
      rw [isTy_op, Bool.and_eq_true, List.all_eq_true] at hA
      change IsTy G n (PartialHorn.subst θ (op k cs)) = true
      rw [subst_op, isTy_op, Bool.and_eq_true, List.all_eq_true, List.length_map]
      exact ⟨hA.1, fun c hc ↦ by
        obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hc
        exact ih c' hc' (hA.2 c' hc')⟩

end Types

section Typing

variable {defs : List PartialHorn.Defn} {M : Model.{v} (ext defs).sig} {ρ : List M.Val}

variable (M) in
/-- Each object definition's operation takes objects to an object. -/
def ObjsHom (G : Globals) : Prop :=
  ∀ (k m : ℕ) (b : Tree), G.defs[k]? = some (.object m b) →
    ∀ ws : List M.Val, ws.map Sigma.fst = List.replicate m obj →
      ∃ w, M.op (G.base + k) ws = Part.some w ∧ w.1 = obj

/-- Objects have values, objects. -/
theorem exists_vals_of_isObj :
    ∀ cs : List Tree, (∀ c ∈ cs, IsObj M ρ c) → ∃ ws : List M.Val,
      cs.map (eval M ρ) = ws.map Part.some ∧ ws.map Sigma.fst = List.replicate cs.length obj :=
  List.rec (fun _ ↦ ⟨[], rfl, rfl⟩) fun c cs ih h ↦ by
    obtain ⟨w, hw, hws⟩ := h c List.mem_cons_self
    obtain ⟨ws, h₁, h₂⟩ := ih fun c' hc' ↦ h c' (List.mem_cons_of_mem _ hc')
    exact ⟨w :: ws, by simp [hw, h₁], by simp [hws, h₂, List.replicate_succ]⟩

/-- A type denotes an object at an assignment of objects to its variables. -/
theorem isObj_of_isTy (hM : IsModel (ext defs) M) {G : Globals} (hO : ObjsHom M G) {n : ℕ}
    (hρ : ρ.map Sigma.fst = List.replicate n obj) :
    ∀ A : Tree, IsTy G n A = true → IsObj M ρ A :=
  RoseTree.ind fun l cs ih hA ↦ by
    rcases l with _ | k
    · rcases cs with _ | ⟨i, _ | ⟨j, cs⟩⟩
      · simp [IsTy] at hA
      rotate_left
      · simp [IsTy] at hA
      obtain ⟨hc, hA⟩ := isTy_var_node_iff.mp hA
      have hlen : ρ.length = n := by simpa using congrArg List.length hρ
      have hi : i.label < ρ.length := hlen ▸ hA
      refine ⟨ρ[i.label], ?_, ?_⟩
      · rw [PartialHorn.eval_node_zero hc, List.getElem?_eq_getElem hi]
        rfl
      · have := congrArg (·[i.label]?) hρ
        simp only [List.getElem?_map, List.getElem?_eq_getElem hi,
          List.getElem?_replicate] at this
        simpa [hA] using this
    · change IsTy G n (op k cs) = true at hA
      rw [isTy_op, Bool.and_eq_true, List.all_eq_true] at hA
      have hc : ∀ c ∈ cs, IsObj M ρ c := fun c hc ↦ ih c hc (hA.2 c hc)
      change IsObj M ρ (op k cs)
      have h₁ := hA.1
      simp only [Globals.isTyOp, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at h₁
      rcases h₁ with h₁ | ⟨hk, hm⟩
      rotate_left
      · -- an object definition
        split at hm
        · rename_i m' b hdef
          obtain rfl : m' = cs.length := by simpa using hm
          obtain ⟨ws, hws, hwsort⟩ := exists_vals_of_isObj cs hc
          obtain ⟨w, hw, hwo⟩ := hO _ _ b hdef ws hwsort
          rw [Nat.add_sub_cancel' hk] at hw
          exact ⟨w, (eval_op_of_values hws k).trans hw, hwo⟩
        · simp at hm
      simp only [tyOps, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h₁
      rcases h₁ with ⟨rfl, hl⟩ | ⟨rfl, hl⟩ | ⟨rfl, hl⟩ | ⟨rfl, hl⟩ | ⟨rfl, hl⟩ | ⟨rfl, hl⟩ |
          ⟨rfl, hl⟩ | ⟨rfl, hl⟩ | ⟨rfl, hl⟩ | ⟨rfl, hl⟩
      · obtain rfl := List.length_eq_zero_iff.mp hl
        exact isObj_one hM
      · obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp hl
        exact isObj_prod hM (hc a (by simp)) (hc b (by simp))
      · obtain rfl := List.length_eq_zero_iff.mp hl
        exact isObj_zero hM
      · obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp hl
        exact isObj_coprod hM (hc a (by simp)) (hc b (by simp))
      · obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp hl
        exact isObj_exp hM (hc a (by simp)) (hc b (by simp))
      · obtain rfl := List.length_eq_zero_iff.mp hl
        exact isObj_omega hM
      · obtain rfl := List.length_eq_zero_iff.mp hl
        exact isObj_nat hM
      · obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp hl
        exact isObj_list hM (hc a (by simp))
      · obtain rfl := List.length_eq_zero_iff.mp hl
        exact isObj_rose hM
      · obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp hl
        exact isObj_lrose hM (hc a (by simp))


variable (M ρ) in
/-- An environment over an object, each of whose variables' types is a type and whose arrow is
an arrow from the object to it. -/
def EnvHom (G : Globals) (n : ℕ) (X : Tree) (e : List (Tree × Tree)) : Prop :=
  IsObj M ρ X ∧ ∀ p ∈ e, Hom M ρ p.1 X p.2 ∧ IsTy G n p.2 = true

variable (M ρ) in
/-- Each primitive arrow, at types, is an arrow between its domain and its codomain. -/
def PrimsHom (G : Globals) (n : ℕ) : Prop :=
  ∀ (k : ℕ) (p : Prim), G.prims[k]? = some p →
    ∀ θ : List Tree, θ.length = p.arity → θ.all (IsTy G n) = true →
      Hom M ρ (PartialHorn.subst θ p.arrow) (PartialHorn.subst θ p.dom)
        (PartialHorn.subst θ p.cod)

variable (M ρ) in
/-- Each definition of the language's operation, at types, is an arrow from the product of its
parameters' types to its value's type, and each object definition's operation takes objects to an
object. -/
def DefsHom (G : Globals) (n : ℕ) : Prop :=
  (∀ (k : ℕ) (d : Defn), G.defs[k]? = some (.language d) →
    ∀ θ : List Tree, θ.length = d.arity → θ.all (IsTy G n) = true →
      Hom M ρ (op (G.base + k) θ) (ctxObj (d.params.map (PartialHorn.subst θ)))
        (PartialHorn.subst θ d.type)) ∧ ObjsHom M G

section

variable (hM : IsModel (ext defs) M)
include hM

/-- Extending an environment by a variable of a type keeps it an environment of arrows. -/
theorem EnvHom.ext {G : Globals} {n : ℕ} {X a : Tree} {e : List (Tree × Tree)}
    (h : EnvHom M ρ G n X e) (ha : IsObj M ρ a) (hat : IsTy G n a = true) :
    EnvHom M ρ G n (prod X a) (extEnv X a e) := by
  refine ⟨isObj_prod hM h.1 ha, fun p hp ↦ ?_⟩
  simp only [extEnv, List.mem_cons, List.mem_map] at hp
  rcases hp with rfl | ⟨q, hq, rfl⟩
  · exact ⟨snd_hom hM h.1 ha, hat⟩
  · exact ⟨comp_hom hM (fst_hom hM h.1 ha) (h.2 q hq).1, (h.2 q hq).2⟩

/-- A tuple of arrows from an object is an arrow to the product of their codomains. -/
theorem tuple_hom {X : Tree} (hX : IsObj M ρ X) :
    ∀ rs : List (Tree × Tree), (∀ r ∈ rs, Hom M ρ r.1 X r.2) →
      Hom M ρ (tuple X (rs.map Prod.fst)) X (ctxObj (rs.map Prod.snd)) :=
  List.rec (fun _ ↦ bang_hom hM hX) fun r rs ih h ↦ by
    rcases rs with _ | ⟨r', rs⟩
    · exact h r List.mem_cons_self
    · exact pair_hom hM (ih fun q hq ↦ h q (List.mem_cons_of_mem _ hq)) (h r List.mem_cons_self)

/-- A rose-tree object's fold by a step is an arrow from the object. -/
theorem roseParts_hom {t a s C : Tree} {F : Tree → Tree}
    (h : roseParts t = some (a, F)) (ha : IsObj M ρ a) (hs : Hom M ρ s (prod a (list C)) C) :
    Hom M ρ (F s) t C := by
  rcases roseParts_eq_some.mp h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact roseRec_hom hM hs
  · exact lroseRec_hom hM ha hs

/-- The compilation is sound: a term's arrow is an arrow from the environment's object to the
term's type, which is a type, when the environment's arrows, the primitive arrows and the
definitions' operations are arrows. -/
theorem compile_hom {G : Globals} {n : ℕ} (hG : G.WF)
    (hρ : ρ.map Sigma.fst = List.replicate n obj) (hps : PrimsHom M ρ G n)
    (hds : DefsHom M ρ G n) (s : Term) :
    ∀ (X : Tree) (e : List (Tree × Tree)) (r : Tree × Tree), compile G n s X e = some r →
      EnvHom M ρ G n X e → Hom M ρ r.1 X r.2 ∧ IsTy G n r.2 = true := by
  refine RoseTree.ind (P := fun s ↦ ∀ (X : Tree) (e : List (Tree × Tree)) (r : Tree × Tree),
    compile G n s X e = some r → EnvHom M ρ G n X e →
      Hom M ρ r.1 X r.2 ∧ IsTy G n r.2 = true) (fun l cs ih ↦ ?_) s
  intro X e r h he
  have hobj := isObj_of_isTy hM hds.2 hρ
  cases l with
  | var i =>
    obtain ⟨rfl, hi⟩ := compile_var_iff.mp h
    exact he.2 r (List.mem_of_getElem? hi)
  | star =>
    obtain ⟨rfl, rfl⟩ := compile_star_iff.mp h
    exact ⟨bang_hom hM he.1, isTy_one⟩
  | pair =>
    obtain ⟨t, u, f, a, g, b, rfl, ht, hu, rfl⟩ := compile_pair_iff.mp h
    obtain ⟨hf, hat⟩ := ih t (by simp) X e _ ht he
    obtain ⟨hg, hbt⟩ := ih u (by simp) X e _ hu he
    exact ⟨pair_hom hM hf hg, by simp [isTy_prod, hat, hbt]⟩
  | fst =>
    obtain ⟨t, f, a, b, rfl, ht, rfl⟩ := compile_fst_iff.mp h
    obtain ⟨hf, hpt⟩ := ih t (by simp) X e _ ht he
    simp only [isTy_prod, Bool.and_eq_true] at hpt
    exact ⟨comp_hom hM hf (fst_hom hM (hobj a hpt.1) (hobj b hpt.2)), hpt.1⟩
  | snd =>
    obtain ⟨t, f, a, b, rfl, ht, rfl⟩ := compile_snd_iff.mp h
    obtain ⟨hf, hpt⟩ := ih t (by simp) X e _ ht he
    simp only [isTy_prod, Bool.and_eq_true] at hpt
    exact ⟨comp_hom hM hf (snd_hom hM (hobj a hpt.1) (hobj b hpt.2)), hpt.2⟩
  | lam a =>
    obtain ⟨t, f, b, rfl, hat, ht, rfl⟩ := compile_lam_iff.mp h
    obtain ⟨hf, hbt⟩ := ih t (by simp) _ _ _ ht (he.ext hM (hobj a hat) hat)
     
    exact ⟨curry_hom hM he.1 (hobj a hat) hf, by simp [isTy_exp, hat, hbt]⟩
  | app =>
    obtain ⟨t, u, rfl, f, a, b, ht, g, hu, rfl⟩ := compile_app_iff.mp h
    obtain ⟨hf, hpt⟩ := ih t (by simp) X e _ ht he
    obtain ⟨hg, -⟩ := ih u (by simp) X e _ hu he
    simp only [isTy_exp, Bool.and_eq_true] at hpt
    exact ⟨comp_hom hM (pair_hom hM hf hg) (ev_hom hM (hobj a hpt.1) (hobj b hpt.2)), hpt.2⟩
  | arr k θ =>
    obtain ⟨t, rfl, p, hp, g, ht, hl, hθ, rfl⟩ := compile_arr_iff.mp h
    obtain ⟨hg, -⟩ := ih t (by simp) X e _ ht he
    exact ⟨comp_hom hM hg (hps k p hp θ hl hθ), isTy_subst hl hθ _ (hG.prims k p hp).2.2⟩
  | natRec =>
    obtain ⟨z, s, m, rfl, z', c, hz, s', hs, m', hm, rfl⟩ := compile_natRec_iff.mp h
    obtain ⟨hz', hct⟩ := ih z (by simp) _ _ _ hz ⟨isObj_one hM, by simp⟩
    have hc := hobj c hct
    obtain ⟨hs', -⟩ := ih s (by simp) _ _ _ hs ⟨hc, by simpa using ⟨idt_hom hM hc, hct⟩⟩
     
    obtain ⟨hm', -⟩ := ih m (by simp) X e _ hm he
    exact ⟨comp_hom hM hm' (natRec_hom hM hz' hs'), hct⟩
  | listRec =>
    obtain ⟨z, s, m, rfl, m', a, hm, z', c, hz, s', hs, rfl⟩ := compile_listRec_iff.mp h
    obtain ⟨hm', hlt⟩ := ih m (by simp) X e _ hm he
    rw [isTy_list] at hlt
    obtain ⟨hz', hct⟩ := ih z (by simp) _ _ _ hz ⟨isObj_one hM, by simp⟩
    have hA := hobj a hlt
    have hc := hobj c hct
    obtain ⟨hs', -⟩ := ih s (by simp) _ _ _ hs ⟨isObj_prod hM hA hc, by
        simpa using ⟨⟨snd_hom hM hA hc, hct⟩, fst_hom hM hA hc, hlt⟩⟩
    exact ⟨comp_hom hM hm' (listRec_hom hM hA hz' hs'), hct⟩
  | roseRec c =>
    obtain ⟨s, m, m', t, a, F, s', rfl, hct, hm, ht, hs, rfl⟩ := compile_roseRec_iff.mp h
    obtain ⟨hm', htt⟩ := ih m (by simp) X e _ hm he
    have hat := isTy_of_roseParts ht htt
    have hPt : IsTy G n (prod a (list c)) = true := by simp [isTy_prod, isTy_list, hat, hct]
    have hP := hobj _ hPt
    obtain ⟨hs', -⟩ := ih s (by simp) _ _ _ hs ⟨hP, by simpa using ⟨idt_hom hM hP, hPt⟩⟩
    exact ⟨comp_hom hM hm' (roseParts_hom hM ht (hobj a hat) hs'), hct⟩
  | eq =>
    obtain ⟨t, u, rfl, f, a, ht, g, hu, rfl⟩ := compile_eq_iff.mp h
    obtain ⟨hf, hat⟩ := ih t (by simp) X e _ ht he
    obtain ⟨hg, -⟩ := ih u (by simp) X e _ hu he
    exact ⟨comp_hom hM (pair_hom hM hf hg) (chi_diag_hom hM (hobj a hat)), isTy_omega⟩
  | defn k θ =>
    obtain ⟨d, rs, hd, hrs, hl, hθ, hty, rfl⟩ := compile_defn_iff.mp h
    have hr : ∀ r ∈ rs, Hom M ρ r.1 X r.2 := fun r hr ↦ by
      obtain ⟨c, hc, hcr⟩ := exists_of_mapM hrs hr
      exact (ih c hc X e r hcr he).1
    have ht := tuple_hom hM he.1 rs hr
    rw [hty] at ht
    exact ⟨comp_hom hM ht (hds.1 k d hd θ hl hθ), isTy_subst hl hθ _ (hG.defs k d hd).2⟩

end

/-- The environment whose arrows are an environment's precomposed with an arrow. -/
def precomp (h : Tree) (e : List (Tree × Tree)) : List (Tree × Tree) :=
  e.map fun p ↦ (comp p.1 h, p.2)

section

variable (hM : IsModel (ext defs) M)
include hM

/-- A tuple of arrows related pointwise to precomposites with an arrow is the tuple
precomposed with it. -/
theorem eval_tuple_comp {X Y h : Tree} (hh : Hom M ρ h Y X) {rs rs' : List (Tree × Tree)}
    (hR : List.Forall₂ (fun r r' ↦ ResEq M ρ (comp r.1 h, r.2) r') rs rs')
    (hr : ∀ r ∈ rs, Hom M ρ r.1 X r.2) :
    eval M ρ (tuple Y (rs'.map Prod.fst)) = eval M ρ (comp (tuple X (rs.map Prod.fst)) h) ∧
      rs'.map Prod.snd = rs.map Prod.snd :=
  hR.rec (motive := fun rs rs' _ ↦ (∀ r ∈ rs, Hom M ρ r.1 X r.2) →
      eval M ρ (tuple Y (rs'.map Prod.fst)) = eval M ρ (comp (tuple X (rs.map Prod.fst)) h) ∧
        rs'.map Prod.snd = rs.map Prod.snd)
    (fun _ ↦ ⟨(comp_bang hM hh).symm, rfl⟩)
    (fun {r r' rs rs'} hrr hrest ih hr ↦ by
      have hrs : ∀ q ∈ rs, Hom M ρ q.1 X q.2 := fun q hq ↦ hr q (List.mem_cons_of_mem _ hq)
      obtain ⟨ih₁, ih₂⟩ := ih hrs
      refine ⟨?_, by simp [ih₂, hrr.1]⟩
      rcases hrest with _ | ⟨_, _⟩
      · exact hrr.2
      · exact (eval_op₂_congr 9 ih₁ hrr.2).trans (pair_comp hM
          (tuple_hom hM hh.isObj_cod _ hrs) (hr r List.mem_cons_self) hh).symm) hr

/-- The compilation is natural: in an environment whose arrows are precomposed with an arrow, a
term has the same type and its arrow precomposed with it. -/
theorem compile_comp {G : Globals} {n : ℕ} (hG : G.WF)
    (hρ : ρ.map Sigma.fst = List.replicate n obj) (hps : PrimsHom M ρ G n)
    (hds : DefsHom M ρ G n) (s : Term) :
    ∀ (X : Tree) (e : List (Tree × Tree)) (r : Tree × Tree), compile G n s X e = some r →
      EnvHom M ρ G n X e → ∀ Y h, Hom M ρ h Y X →
      ∃ r', compile G n s Y (precomp h e) = some r' ∧ ResEq M ρ (comp r.1 h, r.2) r' := by
  refine RoseTree.ind (P := fun s ↦ ∀ (X : Tree) (e : List (Tree × Tree)) (r : Tree × Tree),
    compile G n s X e = some r → EnvHom M ρ G n X e → ∀ Y h, Hom M ρ h Y X →
      ∃ r', compile G n s Y (precomp h e) = some r' ∧ ResEq M ρ (comp r.1 h, r.2) r')
    (fun l cs ih ↦ ?_) s
  intro X e r hc he Y h hh
  have hobj := isObj_of_isTy hM hds.2 hρ
  have hty := compile_hom hM hG hρ hps hds
  cases l with
  | var i =>
    obtain ⟨rfl, hi⟩ := compile_var_iff.mp hc
    exact ⟨_, compile_var_iff.mpr ⟨rfl, by simp [precomp, hi]⟩, rfl, rfl⟩
  | star =>
    obtain ⟨rfl, rfl⟩ := compile_star_iff.mp hc
    exact ⟨_, compile_star_iff.mpr ⟨rfl, rfl⟩, rfl, (comp_bang hM hh).symm⟩
  | pair =>
    obtain ⟨t, u, f, a, g, b, rfl, ht, hu, rfl⟩ := compile_pair_iff.mp hc
    obtain ⟨⟨f', a'⟩, ht', rfl, hf⟩ := ih t (by simp) X e _ ht he Y h hh
    obtain ⟨⟨g', b'⟩, hu', rfl, hg⟩ := ih u (by simp) X e _ hu he Y h hh
    exact ⟨_, compile_pair_iff.mpr ⟨t, u, f', a', g', b', rfl, ht', hu', rfl⟩, rfl,
      (eval_op₂_congr 9 hf hg).trans (pair_comp hM (hty t X e _ ht he).1
        (hty u X e _ hu he).1 hh).symm⟩
  | fst =>
    obtain ⟨t, f, a, b, rfl, ht, rfl⟩ := compile_fst_iff.mp hc
    obtain ⟨⟨f', p⟩, ht', rfl, hf⟩ := ih t (by simp) X e _ ht he Y h hh
    obtain ⟨hft, hpt⟩ := hty t X e _ ht he
    simp only [isTy_prod, Bool.and_eq_true] at hpt
    exact ⟨_, compile_fst_iff.mpr ⟨t, f', a, b, rfl, ht', rfl⟩, rfl,
      (eval_op₂_congr 3 rfl hf).trans
        (comp_assoc hM hh hft (fst_hom hM (hobj a hpt.1) (hobj b hpt.2)))⟩
  | snd =>
    obtain ⟨t, f, a, b, rfl, ht, rfl⟩ := compile_snd_iff.mp hc
    obtain ⟨⟨f', p⟩, ht', rfl, hf⟩ := ih t (by simp) X e _ ht he Y h hh
    obtain ⟨hft, hpt⟩ := hty t X e _ ht he
    simp only [isTy_prod, Bool.and_eq_true] at hpt
    exact ⟨_, compile_snd_iff.mpr ⟨t, f', a, b, rfl, ht', rfl⟩, rfl,
      (eval_op₂_congr 3 rfl hf).trans
        (comp_assoc hM hh hft (snd_hom hM (hobj a hpt.1) (hobj b hpt.2)))⟩
  | lam a =>
    obtain ⟨t, f, b, rfl, hat, ht, rfl⟩ := compile_lam_iff.mp hc
    have hA := hobj a hat
    have hX := he.1
    have hY := hh.isObj_dom
    have heA := he.ext hM hA hat
    have fY := fst_hom hM hY hA
    have sY := snd_hom hM hY hA
    have fX := fst_hom hM hX hA
    have hhf := comp_hom hM fY hh
    have hx := pair_hom hM hhf sY
    obtain ⟨⟨f₁, b₁⟩, ht₁, rfl, hf₁⟩ :=
      ih t (by simp) _ _ _ ht heA _ _ hx
    -- the environment precomposed with the product of the arrow with the identity is the
    -- extension of the precomposed environment
    have hee : EnvEq M ρ (precomp (pair (comp h (fst Y a)) (snd Y a)) (extEnv X a e))
        (extEnv Y a (precomp h e)) := by
      intro i p hp
      rcases i with _ | j
      · obtain rfl : (comp (snd X a) (pair (comp h (fst Y a)) (snd Y a)), a) = p := by
          simpa [precomp, extEnv] using hp
        exact ⟨(snd Y a, a), by simp [extEnv], rfl, (snd_pair hM hhf sY).symm⟩
      · simp only [precomp, extEnv, List.map_cons, List.getElem?_cons_succ, List.map_map,
          List.getElem?_map, Option.map_eq_some_iff, Function.comp_apply] at hp
        obtain ⟨q, hq, rfl⟩ := hp
        have hqh := (he.2 q (List.mem_of_getElem? hq)).1
        refine ⟨(comp (comp q.1 h) (fst Y a), q.2), by simp [precomp, extEnv, hq], rfl, ?_⟩
        exact ((comp_assoc hM fY hh hqh).symm.trans
          (eval_op₂_congr 3 rfl (fst_pair hM hhf sY).symm)).trans (comp_assoc hM hx fX hqh)
    obtain ⟨⟨f₂, b₂⟩, ht₂, rfl, hf₂⟩ := compile_envEq t _ _ _ ht₁ _ hee
    obtain ⟨hft, -⟩ := hty t _ _ _ ht heA
    exact ⟨_, compile_lam_iff.mpr ⟨t, f₂, b₂, rfl, hat, ht₂, rfl⟩, rfl,
      (eval_op₃_congr 24 rfl rfl (hf₂.trans hf₁)).trans (curry_comp hM hA hft hh).symm⟩
  | app =>
    obtain ⟨t, u, rfl, f, a, b, ht, g, hu, rfl⟩ := compile_app_iff.mp hc
    obtain ⟨⟨f', p⟩, ht', rfl, hf⟩ := ih t (by simp) X e _ ht he Y h hh
    obtain ⟨⟨g', a'⟩, hu', rfl, hg⟩ := ih u (by simp) X e _ hu he Y h hh
    obtain ⟨hft, hpt⟩ := hty t X e _ ht he
    obtain ⟨hgt, -⟩ := hty u X e _ hu he
    simp only [isTy_exp, Bool.and_eq_true] at hpt
    have hp := pair_hom hM hft hgt
    exact ⟨_, compile_app_iff.mpr ⟨t, u, rfl, f', a', b, ht', g', hu', rfl⟩, rfl,
      ((eval_op₂_congr 3 rfl ((eval_op₂_congr 9 hf hg).trans
        (pair_comp hM hft hgt hh).symm)).trans
        (comp_assoc hM hh hp (ev_hom hM (hobj a' hpt.1) (hobj b hpt.2))))⟩
  | arr k θ =>
    obtain ⟨t, rfl, p, hp, g, ht, hl, hθ, rfl⟩ := compile_arr_iff.mp hc
    obtain ⟨⟨g', d'⟩, ht', rfl, hg⟩ := ih t (by simp) X e _ ht he Y h hh
    obtain ⟨hgt, -⟩ := hty t X e _ ht he
    exact ⟨_, compile_arr_iff.mpr ⟨t, rfl, p, hp, g', ht', hl, hθ, rfl⟩, rfl,
      (eval_op₂_congr 3 rfl hg).trans (comp_assoc hM hh hgt (hps k p hp θ hl hθ))⟩
  | natRec =>
    obtain ⟨z, s, m, rfl, z', c, hz, s', hs, m', hm, rfl⟩ := compile_natRec_iff.mp hc
    obtain ⟨⟨m'', t⟩, hm', rfl, hmv⟩ := ih m (by simp) X e _ hm he Y h hh
    obtain ⟨hz', hct⟩ := hty z _ _ _ hz ⟨isObj_one hM, by simp⟩
    have hC := hobj c hct
    obtain ⟨hs', -⟩ := hty s _ _ _ hs ⟨hC, by simpa using ⟨idt_hom hM hC, hct⟩⟩
     
    obtain ⟨hmt, -⟩ := hty m X e _ hm he
    exact ⟨_, compile_natRec_iff.mpr ⟨z, s, m, rfl, z', c, hz, s', hs, m'', hm', rfl⟩, rfl,
      (eval_op₂_congr 3 rfl hmv).trans (comp_assoc hM hh hmt (natRec_hom hM hz' hs'))⟩
  | listRec =>
    obtain ⟨z, s, m, rfl, m', a, hm, z', c, hz, s', hs, rfl⟩ := compile_listRec_iff.mp hc
    obtain ⟨⟨m'', t⟩, hm', rfl, hmv⟩ := ih m (by simp) X e _ hm he Y h hh
    obtain ⟨hmt, hlt⟩ := hty m X e _ hm he
    rw [isTy_list] at hlt
    obtain ⟨hz', hct⟩ := hty z _ _ _ hz ⟨isObj_one hM, by simp⟩
    have hA := hobj a hlt
    have hC := hobj c hct
    obtain ⟨hs', -⟩ := hty s _ _ _ hs ⟨isObj_prod hM hA hC, by
        simpa using ⟨⟨snd_hom hM hA hC, hct⟩, fst_hom hM hA hC, hlt⟩⟩
    exact ⟨_, compile_listRec_iff.mpr ⟨z, s, m, rfl, m'', a, hm', z', c, hz, s', hs, rfl⟩, rfl,
      (eval_op₂_congr 3 rfl hmv).trans (comp_assoc hM hh hmt (listRec_hom hM hA hz' hs'))⟩
  | roseRec c =>
    obtain ⟨s, m, m', t, a, F, s', rfl, hct, hm, ht, hs, rfl⟩ := compile_roseRec_iff.mp hc
    obtain ⟨hmt, htt⟩ := hty m X e _ hm he
    have hat := isTy_of_roseParts ht htt
    have hPt : IsTy G n (prod a (list c)) = true := by simp [isTy_prod, isTy_list, hat, hct]
    have hP := hobj _ hPt
    obtain ⟨hs', -⟩ := hty s _ _ _ hs ⟨hP, by simpa using ⟨idt_hom hM hP, hPt⟩⟩
    have hF := roseParts_hom hM ht (hobj a hat) hs'
    obtain ⟨⟨m'', t'⟩, hm', rfl, hmv⟩ := ih m (by simp) X e _ hm he Y h hh
    exact ⟨_, compile_roseRec_iff.mpr ⟨s, m, m'', _, a, F, s', rfl, hct, hm', ht, hs, rfl⟩, rfl,
      (eval_op₂_congr 3 rfl hmv).trans (comp_assoc hM hh hmt hF)⟩
  | eq =>
    obtain ⟨t, u, rfl, f, a, ht, g, hu, rfl⟩ := compile_eq_iff.mp hc
    obtain ⟨hft, hat⟩ := hty t X e _ ht he
    obtain ⟨hgt, -⟩ := hty u X e _ hu he
    obtain ⟨⟨f', a'⟩, ht', rfl, hf⟩ := ih t (by simp) X e _ ht he Y h hh
    obtain ⟨⟨g', b'⟩, hu', rfl, hg⟩ := ih u (by simp) X e _ hu he Y h hh
    have hp := pair_hom hM hft hgt
    exact ⟨_, compile_eq_iff.mpr ⟨_, _, rfl, f', _, ht', g', hu', rfl⟩, rfl,
      (eval_op₂_congr 3 rfl ((eval_op₂_congr 9 hf hg).trans (pair_comp hM hft hgt hh).symm)).trans
        (comp_assoc hM hh hp (chi_diag_hom hM (hobj _ hat)))⟩
  | defn k θ =>
    obtain ⟨d, rs, hd, hrs, hl, hθ, htys, rfl⟩ := compile_defn_iff.mp hc
    have hr : ∀ r ∈ rs, Hom M ρ r.1 X r.2 := fun r hr ↦ by
      obtain ⟨c, hc, hcr⟩ := exists_of_mapM hrs hr
      exact (hty c X e r hcr he).1
    obtain ⟨rs', hrs', hR⟩ := mapM_lift (g := fun c ↦ compile G n c Y (precomp h e)) cs hrs
      fun c hc r hr ↦ ih c hc X e r hr he Y h hh
    obtain ⟨htu, hsn⟩ := eval_tuple_comp hM hh hR hr
    have ht := tuple_hom hM he.1 rs hr
    rw [htys] at ht
    exact ⟨_, compile_defn_iff.mpr ⟨d, rs', hd, hrs', hl, hθ, hsn.trans htys, rfl⟩, rfl,
      (eval_op₂_congr 3 rfl htu).trans
        (comp_assoc hM hh ht (hds.1 k d hd θ hl hθ))⟩

end

end Typing

end Geb.FreeTopos.Internal

end
