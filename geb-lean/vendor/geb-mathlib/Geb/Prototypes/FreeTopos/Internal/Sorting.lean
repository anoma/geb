/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Internal.Semantics

set_option doc.verso true in
/-!
# The sorts of the compiled terms

The terms the compilation produces are well sorted in the signature of the theory extended by the
definitions of the combinators, in the context of the object variables: a type is an object, and
a term's arrow is an arrow ({lit}`compile_sortOf`), when each primitive arrow is an arrow in its
object parameters and each definition's operation takes objects to an arrow.

## Main statements

* {lit}`sortOf_of_isTy` — a type is an object.
* {lit}`compile_sortOf` — a compiled arrow is an arrow.
* {lit}`theory_ofSig` — the theory's axioms are of its signature.

## Tags

internal language, compilation, many-sorted signature
-/

set_option doc.verso true

@[expose] public section

namespace Geb.FreeTopos.Internal

open PartialHorn (Tree op sortOf)
open Sorts
open scoped FinEnum

variable {defs : List PartialHorn.Defn}

/-- The iterated extension of a signature appends the definitions' operations. -/
theorem sig_extendAll_eq (ds : List PartialHorn.Defn) :
    ∀ S : PartialHorn.Sig, S.extendAll ds = S ++ ds.map fun d ↦ (d.ctx, d.sort) :=
  ds.rec (fun S ↦ (List.append_nil S).symm) fun d ds ih S ↦ by
    change (S.extend d).extendAll ds = _
    rw [ih, PartialHorn.Sig.extend, List.map_cons, List.append_assoc, List.singleton_append]

/-- An application of an operation of the theory to arguments of its argument sorts has its
result sort, in every extension. -/
theorem sortOf_op {Γ : List ℕ} {k : ℕ} {ss : List ℕ} {s : ℕ} (hk : sig[k]? = some (ss, s))
    {cs : List Tree} (hcs : cs.map (sortOf (ext defs).sig Γ) = ss.map some) :
    sortOf (ext defs).sig Γ (op k cs) = some s := by
  have hlt : k < sig.length := (List.getElem?_eq_some_iff.mp hk).1
  have hsig : (ext defs).sig[k]? = sig[k]? :=
    (congrArg (·[k]?) (PartialHorn.Theory.extendAll_sig defs theory)).trans
      (sig_extendAll_getElem? defs sig hlt)
  rw [op, PartialHorn.sortOf_node_succ, hsig, hk, Option.bind_some]
  simp [hcs]

section Constructors

variable {Γ : List ℕ}

/-- A composite of arrows is an arrow. -/
theorem sortOf_comp {g f : Tree} (hg : sortOf (ext defs).sig Γ g = some arr)
    (hf : sortOf (ext defs).sig Γ f = some arr) : sortOf (ext defs).sig Γ (comp g f) = some arr :=
  sortOf_op rfl (by simp [hg, hf])

/-- A pairing of arrows is an arrow. -/
theorem sortOf_pair {f g : Tree} (hf : sortOf (ext defs).sig Γ f = some arr)
    (hg : sortOf (ext defs).sig Γ g = some arr) : sortOf (ext defs).sig Γ (pair f g) = some arr :=
  sortOf_op rfl (by simp [hf, hg])

/-- A product of objects is an object. -/
theorem sortOf_prod {a b : Tree} (ha : sortOf (ext defs).sig Γ a = some obj)
    (hb : sortOf (ext defs).sig Γ b = some obj) : sortOf (ext defs).sig Γ (prod a b) = some obj :=
  sortOf_op rfl (by simp [ha, hb])

/-- The first projection of objects is an arrow. -/
theorem sortOf_fst {a b : Tree} (ha : sortOf (ext defs).sig Γ a = some obj)
    (hb : sortOf (ext defs).sig Γ b = some obj) : sortOf (ext defs).sig Γ (fst a b) = some arr :=
  sortOf_op rfl (by simp [ha, hb])

/-- The second projection of objects is an arrow. -/
theorem sortOf_snd {a b : Tree} (ha : sortOf (ext defs).sig Γ a = some obj)
    (hb : sortOf (ext defs).sig Γ b = some obj) : sortOf (ext defs).sig Γ (snd a b) = some arr :=
  sortOf_op rfl (by simp [ha, hb])

/-- The evaluation of objects is an arrow. -/
theorem sortOf_ev {a b : Tree} (ha : sortOf (ext defs).sig Γ a = some obj)
    (hb : sortOf (ext defs).sig Γ b = some obj) : sortOf (ext defs).sig Γ (ev a b) = some arr :=
  sortOf_op rfl (by simp [ha, hb])

/-- A currying is an arrow. -/
theorem sortOf_curry {c a f : Tree} (hc : sortOf (ext defs).sig Γ c = some obj)
    (ha : sortOf (ext defs).sig Γ a = some obj) (hf : sortOf (ext defs).sig Γ f = some arr) :
    sortOf (ext defs).sig Γ (curry c a f) = some arr :=
  sortOf_op rfl (by simp [hc, ha, hf])

/-- The arrow from an object to the terminal object is an arrow. -/
theorem sortOf_bang {a : Tree} (ha : sortOf (ext defs).sig Γ a = some obj) :
    sortOf (ext defs).sig Γ (bang a) = some arr :=
  sortOf_op rfl (by simp [ha])

/-- The identity of an object is an arrow. -/
theorem sortOf_idt {a : Tree} (ha : sortOf (ext defs).sig Γ a = some obj) :
    sortOf (ext defs).sig Γ (idt a) = some arr :=
  sortOf_op rfl (by simp [ha])

/-- The characteristic map of an arrow is an arrow. -/
theorem sortOf_chi {m : Tree} (hm : sortOf (ext defs).sig Γ m = some arr) :
    sortOf (ext defs).sig Γ (chi m) = some arr :=
  sortOf_op rfl (by simp [hm])

/-- The terminal object is an object. -/
theorem sortOf_one : sortOf (ext defs).sig Γ one = some obj := sortOf_op rfl rfl

/-- A fold of the natural numbers object is an arrow. -/
theorem sortOf_natRec {z s : Tree} (hz : sortOf (ext defs).sig Γ z = some arr)
    (hs : sortOf (ext defs).sig Γ s = some arr) :
    sortOf (ext defs).sig Γ (natRec z s) = some arr :=
  sortOf_op rfl (by simp [hz, hs])

/-- A fold of a list object is an arrow. -/
theorem sortOf_listRec {a z s : Tree} (ha : sortOf (ext defs).sig Γ a = some obj)
    (hz : sortOf (ext defs).sig Γ z = some arr) (hs : sortOf (ext defs).sig Γ s = some arr) :
    sortOf (ext defs).sig Γ (listRec a z s) = some arr :=
  sortOf_op rfl (by simp [ha, hz, hs])

/-- A fold of the natural numbers object with a parameter is an arrow. -/
theorem sortOf_natRecP {P C z S : Tree} (hP : sortOf (ext defs).sig Γ P = some obj)
    (hC : sortOf (ext defs).sig Γ C = some obj) (hz : sortOf (ext defs).sig Γ z = some arr)
    (hS : sortOf (ext defs).sig Γ S = some arr) :
    sortOf (ext defs).sig Γ (natRecP P C z S) = some arr := by
  have hE : sortOf (ext defs).sig Γ (exp P C) = some obj := sortOf_op rfl (by simp [hP, hC])
  have hN : sortOf (ext defs).sig Γ nat = some obj := sortOf_op rfl rfl
  exact sortOf_comp (sortOf_ev hP hC) (sortOf_pair (sortOf_comp (sortOf_natRec
    (sortOf_curry sortOf_one hP (sortOf_comp hz (sortOf_snd sortOf_one hP)))
    (sortOf_curry hE hP (sortOf_comp hS (sortOf_pair (sortOf_snd hE hP) (sortOf_ev hP hC)))))
    (sortOf_snd hP hN)) (sortOf_fst hP hN))

/-- A fold of a list object with a parameter is an arrow. -/
theorem sortOf_listRecP {P A C z S : Tree} (hP : sortOf (ext defs).sig Γ P = some obj)
    (hA : sortOf (ext defs).sig Γ A = some obj) (hC : sortOf (ext defs).sig Γ C = some obj)
    (hz : sortOf (ext defs).sig Γ z = some arr) (hS : sortOf (ext defs).sig Γ S = some arr) :
    sortOf (ext defs).sig Γ (listRecP P A C z S) = some arr := by
  have hE : sortOf (ext defs).sig Γ (exp P C) = some obj := sortOf_op rfl (by simp [hP, hC])
  have hL : sortOf (ext defs).sig Γ (list A) = some obj := sortOf_op rfl (by simp [hA])
  have hAE := sortOf_prod hA hE
  exact sortOf_comp (sortOf_ev hP hC) (sortOf_pair (sortOf_comp (sortOf_listRec hA
    (sortOf_curry sortOf_one hP (sortOf_comp hz (sortOf_snd sortOf_one hP)))
    (sortOf_curry hAE hP (sortOf_comp hS (sortOf_pair (sortOf_pair (sortOf_snd hAE hP)
      (sortOf_comp (sortOf_fst hA hE) (sortOf_fst hAE hP))) (sortOf_comp (sortOf_ev hP hC)
        (sortOf_pair (sortOf_comp (sortOf_snd hA hE) (sortOf_fst hAE hP)) (sortOf_snd hAE hP)))))))
    (sortOf_snd hP hL)) (sortOf_fst hP hL))

/-- A fold of a rose-tree object is an arrow. -/
theorem sortOf_roseParts {t a s : Tree} {F : Tree → Tree} (h : roseParts t = some (a, F))
    (ha : sortOf (ext defs).sig Γ a = some obj) (hs : sortOf (ext defs).sig Γ s = some arr) :
    sortOf (ext defs).sig Γ (F s) = some arr := by
  rcases roseParts_eq_some.mp h with ⟨-, -, rfl⟩ | ⟨-, rfl⟩
  · exact sortOf_op rfl (by simp [hs])
  · exact sortOf_op rfl (by simp [ha, hs])

/-- The action of a list object with a parameter is an arrow. -/
theorem sortOf_listMapP {P A C f : Tree} (hP : sortOf (ext defs).sig Γ P = some obj)
    (hA : sortOf (ext defs).sig Γ A = some obj) (hC : sortOf (ext defs).sig Γ C = some obj)
    (hf : sortOf (ext defs).sig Γ f = some arr) :
    sortOf (ext defs).sig Γ (listMapP P A C f) = some arr := by
  have hL : sortOf (ext defs).sig Γ (list C) = some obj := sortOf_op rfl (by simp [hC])
  have hPA := sortOf_prod hP hA
  exact sortOf_listRecP hP hA hL (sortOf_comp (sortOf_op rfl (by simp [hC])) (sortOf_bang hP))
    (sortOf_comp (sortOf_op rfl (by simp [hC]))
      (sortOf_pair (sortOf_comp hf (sortOf_fst hPA hL)) (sortOf_snd hPA hL)))

/-- A fold of a rose-tree object with a parameter is an arrow, where its fold without one is. -/
theorem sortOf_roseRecP {F : Tree → Tree}
    (hF : ∀ {s : Tree}, sortOf (ext defs).sig Γ s = some arr →
      sortOf (ext defs).sig Γ (F s) = some arr) {P a t C S : Tree}
    (hP : sortOf (ext defs).sig Γ P = some obj) (ha : sortOf (ext defs).sig Γ a = some obj)
    (ht : sortOf (ext defs).sig Γ t = some obj) (hC : sortOf (ext defs).sig Γ C = some obj)
    (hS : sortOf (ext defs).sig Γ S = some arr) :
    sortOf (ext defs).sig Γ (roseRecP F P a t C S) = some arr := by
  have hE : sortOf (ext defs).sig Γ (exp P C) = some obj := sortOf_op rfl (by simp [hP, hC])
  have hLE : sortOf (ext defs).sig Γ (list (exp P C)) = some obj := sortOf_op rfl (by simp [hE])
  have hQ := sortOf_prod ha hLE
  have hev := sortOf_comp (sortOf_ev hP hC) (sortOf_pair (sortOf_snd hP hE) (sortOf_fst hP hE))
  have hT : sortOf (ext defs).sig Γ (roseStepP P a C S) = some arr :=
    sortOf_comp hS (sortOf_pair (sortOf_snd hQ hP) (sortOf_pair
      (sortOf_comp (sortOf_fst ha hLE) (sortOf_fst hQ hP)) (sortOf_comp
        (sortOf_listMapP hP hE hC hev) (sortOf_pair (sortOf_snd hQ hP)
          (sortOf_comp (sortOf_snd ha hLE) (sortOf_fst hQ hP))))))
  exact sortOf_comp (sortOf_ev hP hC) (sortOf_pair
    (sortOf_comp (hF (sortOf_curry hQ hP hT)) (sortOf_snd hP ht)) (sortOf_fst hP ht))

end Constructors

section Types

variable {G : Globals}
  (hdefs : ∀ (k : ℕ) (d : Definition), G.defs[k]? = some d →
    (ext defs).sig[G.base + k]? = some d.sig)
include hdefs

/-- A type is an object, in the context of its object variables, when each definition's
operation has the arities and sort of its definition. -/
theorem sortOf_of_isTy {n : ℕ} :
    ∀ A : Tree, IsTy G n A = true → sortOf (ext defs).sig (List.replicate n obj) A = some obj :=
  RoseTree.ind fun l cs ih hA ↦ by
    rcases l with _ | k
    · rcases cs with _ | ⟨i, _ | ⟨j, cs⟩⟩
      · simp [IsTy] at hA
      rotate_left
      · simp [IsTy] at hA
      obtain ⟨hc, hA⟩ := isTy_var_node_iff.mp hA
      rw [PartialHorn.sortOf_node_zero _ hc]
      simp [hA]
    · change IsTy G n (op k cs) = true at hA
      rw [isTy_op, Bool.and_eq_true, List.all_eq_true] at hA
      have hc : ∀ c ∈ cs, sortOf (ext defs).sig (List.replicate n obj) c = some obj :=
        fun c hc ↦ ih c hc (hA.2 c hc)
      change sortOf _ _ (op k cs) = _
      have h₁ := hA.1
      simp only [Globals.isTyOp, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at h₁
      rcases h₁ with h₁ | ⟨hk, hm⟩
      rotate_left
      · -- an object definition
        split at hm
        · rename_i m' b hdef
          obtain rfl : m' = cs.length := by simpa using hm
          have hs := hdefs _ _ hdef
          rw [Nat.add_sub_cancel' hk] at hs
          rw [op, PartialHorn.sortOf_node_succ, hs, Option.bind_some]
          have hcs : cs.map (sortOf (ext defs).sig (List.replicate n obj)) =
              (List.replicate cs.length obj).map some := by
            rw [List.map_replicate]
            refine List.ext_getElem (by simp) fun i h₁ _ ↦ ?_
            simp only [List.getElem_map, List.getElem_replicate]
            exact hc _ (List.getElem_mem (by simpa using h₁))
          simp [Definition.sig, hcs]
        · simp at hm
      simp only [tyOps, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h₁
      rcases h₁ with ⟨rfl, hl⟩ | ⟨rfl, hl⟩ | ⟨rfl, hl⟩ | ⟨rfl, hl⟩ | ⟨rfl, hl⟩ | ⟨rfl, hl⟩ |
          ⟨rfl, hl⟩ | ⟨rfl, hl⟩ | ⟨rfl, hl⟩ | ⟨rfl, hl⟩
      · obtain rfl := List.length_eq_zero_iff.mp hl
        exact sortOf_op rfl rfl
      · obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp hl
        exact sortOf_op rfl (by simp [hc a (by simp), hc b (by simp)])
      · obtain rfl := List.length_eq_zero_iff.mp hl
        exact sortOf_op rfl rfl
      · obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp hl
        exact sortOf_op rfl (by simp [hc a (by simp), hc b (by simp)])
      · obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp hl
        exact sortOf_op rfl (by simp [hc a (by simp), hc b (by simp)])
      · obtain rfl := List.length_eq_zero_iff.mp hl
        exact sortOf_op rfl rfl
      · obtain rfl := List.length_eq_zero_iff.mp hl
        exact sortOf_op rfl rfl
      · obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp hl
        exact sortOf_op rfl (by simp [hc a (by simp)])
      · obtain rfl := List.length_eq_zero_iff.mp hl
        exact sortOf_op rfl rfl
      · obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp hl
        exact sortOf_op rfl (by simp [hc a (by simp)])

/-- Types are objects, in the context of their object variables. -/
theorem map_sortOf_of_isTy {n : ℕ} {θ : List Tree} (hθ : θ.all (IsTy G n) = true) :
    θ.map (sortOf (ext defs).sig (List.replicate n obj)) =
      (List.replicate θ.length obj).map some := by
  rw [List.map_replicate]
  refine List.ext_getElem (by simp) fun i h₁ _ ↦ ?_
  simp only [List.getElem_map, List.getElem_replicate]
  exact sortOf_of_isTy hdefs _ (List.all_eq_true.mp hθ _ (List.getElem_mem (by simpa using h₁)))

end Types

/-- A tuple of arrows is an arrow. -/
theorem sortOf_tuple {Γ : List ℕ} {X : Tree} (hX : sortOf (ext defs).sig Γ X = some obj) :
    ∀ fs : List Tree, (∀ f ∈ fs, sortOf (ext defs).sig Γ f = some arr) →
      sortOf (ext defs).sig Γ (tuple X fs) = some arr :=
  List.rec (fun _ ↦ sortOf_bang hX) fun f fs ih h ↦ by
    rcases fs with _ | ⟨g, fs⟩
    · exact h f List.mem_cons_self
    · exact sortOf_pair (ih fun f' hf' ↦ h f' (List.mem_cons_of_mem _ hf')) (h f List.mem_cons_self)

section Contexts

variable {G : Globals}
  (hdefs : ∀ (k : ℕ) (d : Definition), G.defs[k]? = some d →
    (ext defs).sig[G.base + k]? = some d.sig)
include hdefs

/-- The product of a context of types is an object. -/
theorem sortOf_ctxObj {n : ℕ} :
    ∀ Γ : List Tree, Γ.all (IsTy G n) = true →
      sortOf (ext defs).sig (List.replicate n obj) (ctxObj Γ) = some obj :=
  List.rec (fun _ ↦ sortOf_one) fun a Γ ih h ↦ by
    simp only [List.all_cons, Bool.and_eq_true] at h
    rcases Γ with _ | ⟨b, Γ⟩
    · exact sortOf_of_isTy hdefs a h.1
    · exact sortOf_prod (ih h.2) (sortOf_of_isTy hdefs a h.1)

/-- A context's projections are arrows, to types. -/
theorem sortOf_stdEnv {n : ℕ} :
    ∀ Γ : List Tree, Γ.all (IsTy G n) = true → ∀ p ∈ stdEnv Γ,
      sortOf (ext defs).sig (List.replicate n obj) p.1 = some arr ∧ IsTy G n p.2 = true :=
  List.rec (fun _ p hp ↦ by simp [stdEnv] at hp) fun a Γ ih h p hp ↦ by
    simp only [List.all_cons, Bool.and_eq_true] at h
    have hA := sortOf_of_isTy (defs := defs) hdefs a h.1
    rcases Γ with _ | ⟨b, Γ⟩
    · obtain rfl : p = (idt a, a) := by simpa [stdEnv] using hp
      exact ⟨sortOf_idt hA, h.1⟩
    change p ∈ extEnv (ctxObj (b :: Γ)) a (stdEnv (b :: Γ)) at hp
    simp only [extEnv, List.mem_cons, List.mem_map] at hp
    have hX := sortOf_ctxObj (defs := defs) hdefs (b :: Γ) h.2
    rcases hp with rfl | ⟨q, hq, rfl⟩
    · exact ⟨sortOf_snd hX hA, h.1⟩
    · exact ⟨sortOf_comp (ih h.2 q hq).1 (sortOf_fst hX hA), (ih h.2 q hq).2⟩

/-- The environment of a fold's start or step has an object and arrows to types, when the types
it binds are types and the fold's environment's entries arrows to types. -/
theorem sortOf_foldEnvIn {n : ℕ} {bs : List Tree} (hbs : bs.all (IsTy G n) = true) {k : ℕ}
    {e : List (Tree × Tree)}
    (he : ∀ p ∈ e, sortOf (ext defs).sig (List.replicate n obj) p.1 = some arr ∧
      IsTy G n p.2 = true) (z s : Term) :
    sortOf (ext defs).sig (List.replicate n obj) (foldEnvIn bs k e z s).1 = some obj ∧
      ∀ p ∈ (foldEnvIn bs k e z s).2, sortOf (ext defs).sig (List.replicate n obj) p.1 = some arr ∧
        IsTy G n p.2 = true := by
  have hΓ : (bs ++ (foldPs k e z s).map Prod.snd).all (IsTy G n) = true := by
    simp only [List.all_append, hbs, Bool.true_and, List.all_eq_true, List.mem_map]
    rintro _ ⟨p, hp, rfl⟩
    exact (he p (mem_of_mem_foldPs hp)).2
  have hX := sortOf_ctxObj hdefs _ hΓ
  refine ⟨hX, fun p hp ↦ ?_⟩
  rcases mem_selEnv hp with hp | rfl
  · exact sortOf_stdEnv hdefs _ hΓ p hp
  · exact ⟨sortOf_idt hX, isTy_ctxObj _ hΓ⟩

end Contexts

/-- A fold of the natural numbers object at parameters is an arrow. -/
theorem sortOf_natFold {Γ' : List ℕ} {Γ : List Tree} {X c z s m : Tree} {fs : List Tree}
    (hX : sortOf (ext defs).sig Γ' X = some obj)
    (hP : sortOf (ext defs).sig Γ' (ctxObj Γ) = some obj)
    (hC : sortOf (ext defs).sig Γ' c = some obj) (hz : sortOf (ext defs).sig Γ' z = some arr)
    (hs : sortOf (ext defs).sig Γ' s = some arr) (hm : sortOf (ext defs).sig Γ' m = some arr)
    (hfs : ∀ f ∈ fs, sortOf (ext defs).sig Γ' f = some arr) :
    sortOf (ext defs).sig Γ' (natFold Γ c z s (tuple X fs) m) = some arr := by
  rcases Γ with _ | ⟨b, Γ⟩
  · exact sortOf_comp (sortOf_natRec hz hs) hm
  · exact sortOf_comp (sortOf_natRecP hP hC hz hs) (sortOf_pair (sortOf_tuple hX fs hfs) hm)

/-- A fold of a rose-tree object at parameters is an arrow. -/
theorem sortOf_roseFold {Γ' : List ℕ} {F : Tree → Tree}
    (hF : ∀ {s : Tree}, sortOf (ext defs).sig Γ' s = some arr →
      sortOf (ext defs).sig Γ' (F s) = some arr) {Γ : List Tree} {X a t c s m : Tree}
    {fs : List Tree} (hX : sortOf (ext defs).sig Γ' X = some obj)
    (hP : sortOf (ext defs).sig Γ' (ctxObj Γ) = some obj)
    (ha : sortOf (ext defs).sig Γ' a = some obj) (ht : sortOf (ext defs).sig Γ' t = some obj)
    (hC : sortOf (ext defs).sig Γ' c = some obj) (hs : sortOf (ext defs).sig Γ' s = some arr)
    (hm : sortOf (ext defs).sig Γ' m = some arr)
    (hfs : ∀ f ∈ fs, sortOf (ext defs).sig Γ' f = some arr) :
    sortOf (ext defs).sig Γ' (roseFold F Γ a t c s (tuple X fs) m) = some arr := by
  rcases Γ with _ | ⟨b, Γ⟩
  · exact sortOf_comp (hF hs) hm
  · exact sortOf_comp (sortOf_roseRecP hF hP ha ht hC hs) (sortOf_pair (sortOf_tuple hX fs hfs) hm)

/-- A fold of a list object at parameters is an arrow. -/
theorem sortOf_listFold {Γ' : List ℕ} {Γ : List Tree} {X a c z s m : Tree} {fs : List Tree}
    (hX : sortOf (ext defs).sig Γ' X = some obj)
    (hP : sortOf (ext defs).sig Γ' (ctxObj Γ) = some obj)
    (hA : sortOf (ext defs).sig Γ' a = some obj) (hC : sortOf (ext defs).sig Γ' c = some obj)
    (hz : sortOf (ext defs).sig Γ' z = some arr) (hs : sortOf (ext defs).sig Γ' s = some arr)
    (hm : sortOf (ext defs).sig Γ' m = some arr)
    (hfs : ∀ f ∈ fs, sortOf (ext defs).sig Γ' f = some arr) :
    sortOf (ext defs).sig Γ' (listFold Γ a c z s (tuple X fs) m) = some arr := by
  rcases Γ with _ | ⟨b, Γ⟩
  · exact sortOf_comp (sortOf_listRec hA hz hs) hm
  · exact sortOf_comp (sortOf_listRecP hP hA hC hz hs) (sortOf_pair (sortOf_tuple hX fs hfs) hm)

/-- An environment of arrows of typed variables, extended by a variable of a type, is an
environment of arrows of typed variables. -/
theorem extEnv_sortOf {G : Globals} {n : ℕ} {X a : Tree} {e : List (Tree × Tree)}
    (hX : sortOf (ext defs).sig (List.replicate n obj) X = some obj)
    (hA : sortOf (ext defs).sig (List.replicate n obj) a = some obj) (hat : IsTy G n a = true)
    (he : ∀ p ∈ e, sortOf (ext defs).sig (List.replicate n obj) p.1 = some arr ∧
      IsTy G n p.2 = true) :
    ∀ p ∈ extEnv X a e, sortOf (ext defs).sig (List.replicate n obj) p.1 = some arr ∧
      IsTy G n p.2 = true := fun p hp ↦ by
  simp only [extEnv, List.mem_cons, List.mem_map] at hp
  rcases hp with rfl | ⟨q, hq, rfl⟩
  · exact ⟨sortOf_snd hX hA, hat⟩
  · exact ⟨sortOf_comp (he q hq).1 (sortOf_fst hX hA), (he q hq).2⟩

/-- The compiled terms are well sorted: a term's arrow is an arrow, and its type a type, when the
environment's object is an object and its arrows arrows, each primitive arrow is an arrow in its
object parameters, and each definition's operation takes objects to an arrow. -/
theorem compile_sortOf {G : Globals} (hG : G.WF) {n : ℕ}
    (hprims : ∀ (k : ℕ) (p : Prim), G.prims[k]? = some p →
      sortOf (ext defs).sig (List.replicate p.arity obj) p.arrow = some arr)
    (hdefs : ∀ (k : ℕ) (d : Definition), G.defs[k]? = some d →
      (ext defs).sig[G.base + k]? = some d.sig)
    (s : Term) :
    ∀ (X : Tree) (e : List (Tree × Tree)) (r : Tree × Tree), compile G n s X e = some r →
      sortOf (ext defs).sig (List.replicate n obj) X = some obj →
      (∀ p ∈ e, sortOf (ext defs).sig (List.replicate n obj) p.1 = some arr ∧
        IsTy G n p.2 = true) →
      sortOf (ext defs).sig (List.replicate n obj) r.1 = some arr ∧ IsTy G n r.2 = true := by
  refine RoseTree.ind (P := fun s ↦ ∀ (X : Tree) (e : List (Tree × Tree)) (r : Tree × Tree),
    compile G n s X e = some r →
      sortOf (ext defs).sig (List.replicate n obj) X = some obj →
      (∀ p ∈ e, sortOf (ext defs).sig (List.replicate n obj) p.1 = some arr ∧
        IsTy G n p.2 = true) →
      sortOf (ext defs).sig (List.replicate n obj) r.1 = some arr ∧ IsTy G n r.2 = true)
    (fun l cs ih ↦ ?_) s
  intro X e r h hX he
  have hty := sortOf_of_isTy (defs := defs) hdefs (n := n)
  cases l with
  | var i =>
    obtain ⟨rfl, hi⟩ := compile_var_iff.mp h
    exact he r (List.mem_of_getElem? hi)
  | star =>
    obtain ⟨rfl, rfl⟩ := compile_star_iff.mp h
    exact ⟨sortOf_bang hX, isTy_one⟩
  | pair =>
    obtain ⟨t, u, f, a, g, b, rfl, ht, hu, rfl⟩ := compile_pair_iff.mp h
    obtain ⟨hf, hat⟩ := ih t (by simp) X e _ ht hX he
    obtain ⟨hg, hbt⟩ := ih u (by simp) X e _ hu hX he
    exact ⟨sortOf_pair hf hg, by simp [isTy_prod, hat, hbt]⟩
  | fst =>
    obtain ⟨t, f, a, b, rfl, ht, rfl⟩ := compile_fst_iff.mp h
    obtain ⟨hf, hpt⟩ := ih t (by simp) X e _ ht hX he
    simp only [isTy_prod, Bool.and_eq_true] at hpt
    exact ⟨sortOf_comp (sortOf_fst (hty a hpt.1) (hty b hpt.2)) hf, hpt.1⟩
  | snd =>
    obtain ⟨t, f, a, b, rfl, ht, rfl⟩ := compile_snd_iff.mp h
    obtain ⟨hf, hpt⟩ := ih t (by simp) X e _ ht hX he
    simp only [isTy_prod, Bool.and_eq_true] at hpt
    exact ⟨sortOf_comp (sortOf_snd (hty a hpt.1) (hty b hpt.2)) hf, hpt.2⟩
  | lam a =>
    obtain ⟨t, f, b, rfl, hat, ht, rfl⟩ := compile_lam_iff.mp h
    have hA := hty a hat
    have hP : sortOf (ext defs).sig (List.replicate n obj) (prod X a) = some obj :=
      sortOf_prod hX hA
    obtain ⟨hf, hbt⟩ := ih t (by simp) _ _ _ ht hP (extEnv_sortOf hX hA hat he)
    exact ⟨sortOf_curry hX hA hf, by simp [isTy_exp, hat, hbt]⟩
  | app =>
    obtain ⟨t, u, rfl, f, a, b, ht, g, hu, rfl⟩ := compile_app_iff.mp h
    obtain ⟨hf, hpt⟩ := ih t (by simp) X e _ ht hX he
    obtain ⟨hg, -⟩ := ih u (by simp) X e _ hu hX he
    simp only [isTy_exp, Bool.and_eq_true] at hpt
    exact ⟨sortOf_comp (sortOf_ev (hty a hpt.1) (hty b hpt.2)) (sortOf_pair hf hg), hpt.2⟩
  | arr k θ =>
    obtain ⟨t, rfl, p, hp, g, ht, hl, hθ, rfl⟩ := compile_arr_iff.mp h
    obtain ⟨hg, -⟩ := ih t (by simp) X e _ ht hX he
    have hθs := map_sortOf_of_isTy (defs := defs) hdefs hθ
    rw [hl] at hθs
    exact ⟨sortOf_comp (PartialHorn.sortOf_subst hθs _ (hprims k p hp)) hg,
      isTy_subst hl hθ _ (hG.prims k p hp).2.2⟩
  | natRec =>
    obtain ⟨z, s, m, rfl, z', c, hz, s', hs, m', hm, rfl⟩ := compile_natRec_iff.mp h
    have hF := sortOf_foldEnvIn hdefs (bs := []) rfl he (k := 1) z s
    obtain ⟨hz', hct⟩ := ih z (by simp) _ _ _ hz hF.1 hF.2
    have hF' := sortOf_foldEnvIn hdefs (bs := [c]) (by simp [hct]) he (k := 1) z s
    obtain ⟨hs', -⟩ := ih s (by simp) _ _ _ hs hF'.1 hF'.2
    obtain ⟨hm', -⟩ := ih m (by simp) X e _ hm hX he
    refine ⟨sortOf_natFold hX hF.1 (hty c hct) hz' hs' hm' fun f hf ↦ ?_, hct⟩
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hf
    exact (he p (mem_of_mem_foldPs hp)).1
  | listRec =>
    obtain ⟨z, s, m, rfl, m', a, hm, z', c, hz, s', hs, rfl⟩ := compile_listRec_iff.mp h
    obtain ⟨hm', hlt⟩ := ih m (by simp) X e _ hm hX he
    rw [isTy_list] at hlt
    have hF := sortOf_foldEnvIn hdefs (bs := []) rfl he (k := 2) z s
    obtain ⟨hz', hct⟩ := ih z (by simp) _ _ _ hz hF.1 hF.2
    have hF' := sortOf_foldEnvIn hdefs (bs := [c, a]) (by simp [hct, hlt]) he (k := 2) z s
    obtain ⟨hs', -⟩ := ih s (by simp) _ _ _ hs hF'.1 hF'.2
    refine ⟨sortOf_listFold hX hF.1 (hty a hlt) (hty c hct) hz' hs' hm' fun f hf ↦ ?_, hct⟩
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hf
    exact (he p (mem_of_mem_foldPs hp)).1
  | roseRec c =>
    obtain ⟨s, m, m', t, a, F, s', rfl, hct, hm, ht, hs, rfl⟩ := compile_roseRec_iff.mp h
    obtain ⟨hm', htt⟩ := ih m (by simp) X e _ hm hX he
    have hat := isTy_of_roseParts ht htt
    have hPt : IsTy G n (prod a (list c)) = true := by simp [isTy_prod, isTy_list, hat, hct]
    have hF' := sortOf_foldEnvIn hdefs (bs := [prod a (list c)]) (by simp [hPt]) he (k := 1)
      Term.star s
    obtain ⟨hs', -⟩ := ih s (by simp) _ _ _ hs hF'.1 hF'.2
    have hF0 := sortOf_foldEnvIn hdefs (bs := []) rfl he (k := 1) Term.star s
    refine ⟨sortOf_roseFold (fun h ↦ sortOf_roseParts ht (hty a hat) h) hX hF0.1 (hty a hat)
      (hty t htt) (hty c hct) hs' hm' fun f hf ↦ ?_, hct⟩
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hf
    exact (he p (mem_of_mem_foldPs hp)).1
  | eq =>
    obtain ⟨t, u, rfl, f, a, ht, g, hu, rfl⟩ := compile_eq_iff.mp h
    obtain ⟨hf, hat⟩ := ih t (by simp) X e _ ht hX he
    obtain ⟨hg, -⟩ := ih u (by simp) X e _ hu hX he
    have hA := hty a hat
    exact ⟨sortOf_comp (sortOf_chi (sortOf_pair (sortOf_idt hA) (sortOf_idt hA)))
      (sortOf_pair hf hg), isTy_omega⟩
  | defn k θ =>
    obtain ⟨d, rs, hd, hrs, hl, hθ, htys, rfl⟩ := compile_defn_iff.mp h
    have hr : ∀ f ∈ rs.map Prod.fst, sortOf (ext defs).sig (List.replicate n obj) f = some arr :=
      fun f hf ↦ by
        obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hf
        obtain ⟨c, hc, hcr⟩ := exists_of_mapM hrs hr
        exact (ih c hc X e r hcr hX he).1
    have hθs := map_sortOf_of_isTy (defs := defs) hdefs hθ
    rw [hl] at hθs
    have hop : sortOf (ext defs).sig (List.replicate n obj) (op (G.base + k) θ) = some arr := by
      rw [op, PartialHorn.sortOf_node_succ, hdefs k _ hd, Option.bind_some]
      simp [hθs, Definition.sig]
    exact ⟨sortOf_comp hop (sortOf_tuple hX _ hr), isTy_subst hl hθ _ (hG.defs k d hd).2⟩

/-- The theory's axioms are of its signature. -/
theorem theory_ofSig : theory.OfSig := by
  have h : axioms.all (fun a ↦ (a.concl :: a.hyps).all fun q ↦
      PartialHorn.OpsBelow sig.length q.lhs && PartialHorn.OpsBelow sig.length q.rhs) = true := by
    decide
  intro a ha q hq
  have hq' := List.all_eq_true.mp (List.all_eq_true.mp h a ha) q hq
  rwa [Bool.and_eq_true] at hq'


end Geb.FreeTopos.Internal

end
