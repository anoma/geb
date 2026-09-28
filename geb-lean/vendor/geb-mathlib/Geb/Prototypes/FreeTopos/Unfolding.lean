/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Prototypes.FreeTopos.Arrows
public import Geb.Prototypes.PartialHorn.Definitional

set_option doc.verso true in
/-!
# The unfolding of definitions in a term

The unfolding of a list of definitions in a term ({lit}`unfoldTerm`), the last first, as the
unfolding of a sequent ({name}`Geb.PartialHorn.unfoldAll`) unfolds each of its equations' sides:
a term of the signature extended by the definitions becomes one of the signature. It leaves an
application of an operation of the signature an application of the operation to the unfolded
arguments, and replaces an application of a definition's operation, at arguments without
definitions, by the unfolded body with the arguments substituted for its variables; for the
latter, the unfolding of one definition commutes with a substitution in a well-sorted term.

## Main definitions

* {lit}`unfoldTerm` — the unfolding of a list of definitions in a term.

## Main statements

* {lit}`unfoldAll_eq` — the unfolding of a sequent unfolds its equations' sides.
* {lit}`unfoldTerm_op_lt` — at an operation of the signature.
* {lit}`unfoldTerm_op_defn` — at a definition's operation.
* {lit}`unfoldOp_subst` — the unfolding of one definition commutes with substitution.

## Tags

definitional extension, unfolding, substitution, partial Horn logic
-/

set_option doc.verso true

@[expose] public section

namespace Geb.FreeTopos

open PartialHorn

variable {S : Sig}

/-- The unfolding of a list of definitions in a term, the last first, so that each definition's
unfolding meets only the definitions before it. -/
def unfoldTerm (S : Sig) (ds : List Defn) (t : Tree) : Tree :=
  ds.rec (motive := fun _ ↦ Sig → Tree) (fun _ ↦ t)
    (fun d _ ih S ↦ unfoldOp S.length d.body (ih (S.extend d))) S

/-- The unfolding of a sequent unfolds its equations' sides. -/
theorem unfoldAll_eq (ds : List Defn) :
    ∀ (S : Sig) (a : Seq), unfoldAll S ds a =
      ⟨a.ctx, a.hyps.map fun q ↦ ⟨unfoldTerm S ds q.lhs, unfoldTerm S ds q.rhs⟩,
        ⟨unfoldTerm S ds a.concl.lhs, unfoldTerm S ds a.concl.rhs⟩⟩ :=
  ds.rec (motive := fun ds ↦ ∀ (S : Sig) (a : Seq), unfoldAll S ds a =
      ⟨a.ctx, a.hyps.map fun q ↦ ⟨unfoldTerm S ds q.lhs, unfoldTerm S ds q.rhs⟩,
        ⟨unfoldTerm S ds a.concl.lhs, unfoldTerm S ds a.concl.rhs⟩⟩)
    (fun _ a ↦ by simp [unfoldAll, unfoldTerm])
    (fun d ds ih S a ↦ by
      change (unfoldAll (S.extend d) ds a).unfoldOp S.length d.body = _
      rw [ih]
      simp [Seq.unfoldOp, Eqn.unfoldOp, unfoldTerm, Function.comp_def])

/-- The unfolding leaves a term of the signature. -/
theorem unfoldTerm_of_opsBelow (ds : List Defn) :
    ∀ (S : Sig) (t : Tree), OpsBelow S.length t = true → unfoldTerm S ds t = t :=
  ds.rec (motive := fun ds ↦ ∀ (S : Sig) (t : Tree), OpsBelow S.length t = true →
      unfoldTerm S ds t = t)
    (fun _ _ _ ↦ rfl)
    (fun d ds ih S t ht ↦ by
      change unfoldOp S.length d.body (unfoldTerm (S.extend d) ds t) = t
      rw [ih _ t (opsBelow_mono (by simp [Sig.extend]) t ht)]
      exact unfoldOp_of_opsBelow _ _ t ht)

/-- The unfolding of definitions followed by others is the unfolding of the first in a term of
the signature extended by them. -/
theorem unfoldTerm_append (e : List Defn) (ds : List Defn) :
    ∀ (S : Sig) (t : Tree), OpsBelow (S.extendAll ds).length t = true →
      unfoldTerm S (ds ++ e) t = unfoldTerm S ds t :=
  ds.rec (motive := fun ds ↦ ∀ (S : Sig) (t : Tree), OpsBelow (S.extendAll ds).length t = true →
      unfoldTerm S (ds ++ e) t = unfoldTerm S ds t)
    (fun S t ht ↦ unfoldTerm_of_opsBelow e S t ht)
    (fun d ds ih S t ht ↦ by
      change unfoldOp S.length d.body (unfoldTerm (S.extend d) (ds ++ e) t) =
        unfoldOp S.length d.body (unfoldTerm (S.extend d) ds t)
      rw [ih (S.extend d) t ht])

/-- The unfolding of an application of an operation of the signature is the application of the
operation to the unfolded arguments. -/
theorem unfoldTerm_op_lt (ds : List Defn) {k : ℕ} (ts : List Tree) :
    ∀ (S : Sig), k < S.length → unfoldTerm S ds (op k ts) = op k (ts.map (unfoldTerm S ds)) :=
  ds.rec (motive := fun ds ↦ ∀ (S : Sig), k < S.length →
      unfoldTerm S ds (op k ts) = op k (ts.map (unfoldTerm S ds)))
    (fun _ _ ↦ (congrArg (op k) (List.map_id' ts)).symm)
    (fun d ds ih S hk ↦ by
      change unfoldOp S.length d.body (unfoldTerm (S.extend d) ds (op k ts)) = _
      rw [ih _ (by simp [Sig.extend]; omega), op, unfoldOp_node_succ,
        if_neg (Nat.ne_of_lt hk), List.map_map]
      rfl)

/-- The unfolding of one definition commutes with a substitution of terms it leaves in place,
in a well-sorted term: the definition's body is in the scope of the arguments at each of its
applications. -/
theorem unfoldOp_subst {S' : Sig} {n : ℕ} {b : Tree} {c : List ℕ} {s₀ : ℕ}
    (hn : S'[n]? = some (c, s₀)) (hb : Scoped c.length b = true) {θ : List Tree}
    (hθ : ∀ u ∈ θ, unfoldOp n b u = u) :
    ∀ (t : Tree) {Γ : List ℕ} {s : ℕ}, sortOf S' Γ t = some s →
      unfoldOp n b (subst θ t) = subst θ (unfoldOp n b t) :=
  RoseTree.ind fun l cs ih Γ s ht ↦ by
    rcases l with _ | k
    · rw [unfoldOp_node_zero]
      rcases cs with _ | ⟨i, _ | ⟨i', cs⟩⟩
      · simp [sortOf] at ht
      · by_cases hi : i.children = []
        · rw [subst_node_zero _ hi]
          rcases hθi : θ[i.label]? with _ | u
          · simp only [Option.getD_none]
            exact unfoldOp_node_zero n b _
          · exact hθ u (List.mem_of_getElem? hθi)
        · rw [subst_node_zero_of_not _ hi, unfoldOp_node_zero]
      · simp [sortOf] at ht
    · rw [sortOf_node_succ] at ht
      obtain ⟨o, ho, ht⟩ := Option.bind_eq_some_iff.mp ht
      split_ifs at ht with hcs
      have hsorted : ∀ c' ∈ cs, ∃ s', sortOf S' Γ c' = some s' := fun c' hc' ↦ by
        have : sortOf S' Γ c' ∈ o.1.map some := hcs ▸ List.mem_map_of_mem hc'
        obtain ⟨s', -, hs'⟩ := List.mem_map.mp this
        exact ⟨s', hs'.symm⟩
      have hrec : ∀ c' ∈ cs, unfoldOp n b (subst θ c') = subst θ (unfoldOp n b c') :=
        fun c' hc' ↦
          let ⟨_, hs'⟩ := hsorted c' hc'
          ih c' hc' hs'
      rw [subst_node_succ, unfoldOp_node_succ, unfoldOp_node_succ, List.map_map]
      split_ifs with hk
      · subst hk
        obtain rfl : o = (c, s₀) := Option.some_inj.mp (ho.symm.trans hn)
        have hlen : (cs.map (unfoldOp k b)).length = c.length := by
          simpa using congrArg List.length hcs
        rw [subst_subst θ _ b (hlen ▸ hb), List.map_map]
        exact congrArg (fun us ↦ subst us b) (List.map_congr_left hrec)
      · rw [subst_node_succ, List.map_map]
        exact congrArg (RoseTree.node (k + 1)) (List.map_congr_left hrec)

/-- The signature extended by a list of definitions is the signature followed by their
operations. -/
theorem extendAll_eq (ds : List Defn) :
    ∀ S : Sig, S.extendAll ds = S ++ ds.map fun d ↦ (d.ctx, d.sort) :=
  ds.rec (motive := fun ds ↦ ∀ S : Sig, S.extendAll ds = S ++ ds.map fun d ↦ (d.ctx, d.sort))
    (fun S ↦ by simp [Sig.extendAll])
    (fun d ds ih S ↦ by
      change (S.extend d).extendAll ds = _
      rw [ih]
      simp [Sig.extend])

/-- A definition of a well-formed list is well formed over the definitions before it. -/
theorem defnsWF_getElem (ds : List Defn) :
    ∀ (S : Sig) {j : ℕ} {d : Defn}, DefnsWF S ds → ds[j]? = some d →
      d.WF (S.extendAll (ds.take j)) :=
  ds.rec (motive := fun ds ↦ ∀ (S : Sig) {j : ℕ} {d : Defn}, DefnsWF S ds → ds[j]? = some d →
      d.WF (S.extendAll (ds.take j)))
    (fun _ _ _ _ h ↦ by simp at h)
    (fun d₀ ds ih S j d hwf hj ↦ by
      rcases j with _ | i
      · obtain rfl : d₀ = d := by simpa using hj
        exact hwf.1
      · exact ih (S.extend d₀) hwf.2 (by simpa using hj))

/-- The unfolding of a list of well-formed definitions takes a term of the extension to one of
the signature, of the same sort. -/
theorem sortOf_unfoldTerm (ds : List Defn) :
    ∀ (S : Sig) {Γ : List ℕ} {t : Tree} {s : ℕ}, DefnsWF S ds →
      sortOf (S.extendAll ds) Γ t = some s → sortOf S Γ (unfoldTerm S ds t) = some s :=
  ds.rec (motive := fun ds ↦ ∀ (S : Sig) {Γ : List ℕ} {t : Tree} {s : ℕ}, DefnsWF S ds →
      sortOf (S.extendAll ds) Γ t = some s → sortOf S Γ (unfoldTerm S ds t) = some s)
    (fun _ _ _ _ _ h ↦ h)
    (fun _ _ ih _ _ _ _ hwf h ↦ sortOf_unfold hwf.1 _ (ih _ hwf.2 h))

/-- The unfolding of an application of a definition's operation, at arguments of the signature,
is the unfolded body with the arguments substituted for its variables. -/
theorem unfoldTerm_op_defn (ds : List Defn) :
    ∀ (S : Sig) {j : ℕ} {d : Defn} {θ : List Tree}, DefnsWF S ds → ds[j]? = some d →
      (∀ u ∈ θ, OpsBelow S.length u = true) →
      unfoldTerm S ds (op (S.length + j) θ) = subst θ (unfoldTerm S ds d.body) :=
  ds.rec (motive := fun ds ↦ ∀ (S : Sig) {j : ℕ} {d : Defn} {θ : List Tree}, DefnsWF S ds →
      ds[j]? = some d → (∀ u ∈ θ, OpsBelow S.length u = true) →
      unfoldTerm S ds (op (S.length + j) θ) = subst θ (unfoldTerm S ds d.body))
    (fun _ _ _ _ _ h ↦ by simp at h)
    (fun d₀ ds ih S j d θ hwf hj hθ ↦ by
      have hlt : S.length < (S.extend d₀).length := by simp [Sig.extend]
      have hθ' : ∀ u ∈ θ, OpsBelow (S.extend d₀).length u = true := fun u hu ↦
        opsBelow_mono hlt.le u (hθ u hu)
      have hθ₀ : ∀ u ∈ θ, unfoldOp S.length d₀.body u = u := fun u hu ↦
        unfoldOp_of_opsBelow _ _ u (hθ u hu)
      change unfoldOp S.length d₀.body (unfoldTerm (S.extend d₀) ds _) =
        subst θ (unfoldOp S.length d₀.body (unfoldTerm (S.extend d₀) ds d.body))
      rcases j with _ | i
      · obtain rfl : d₀ = d := by simpa using hj
        have hb := opsBelow_of_sortOf d₀.body hwf.1.sort
        rw [Nat.add_zero, unfoldTerm_op_lt ds θ _ hlt, unfoldTerm_of_opsBelow ds _ d₀.body
          (opsBelow_mono hlt.le _ hb), unfoldOp_of_opsBelow _ _ _ hb, op, unfoldOp_node_succ,
          if_pos rfl, List.map_map]
        exact congrArg (fun us ↦ subst us d₀.body) ((List.map_congr_left fun u hu ↦
          (congrArg (unfoldOp _ _) (unfoldTerm_of_opsBelow ds _ u (hθ' u hu))).trans
            (hθ₀ u hu)).trans θ.map_id)
      · have hj' : ds[i]? = some d := by simpa using hj
        have hidx : S.length + (i + 1) = (S.extend d₀).length + i := by
          simp [Sig.extend]; omega
        rw [hidx, ih (S.extend d₀) hwf.2 hj' hθ']
        have hdwf := defnsWF_getElem ds (S.extend d₀) hwf.2 hj'
        have hsort : sortOf ((S.extend d₀).extendAll ds) d.ctx d.body = some d.sort := by
          refine sortOf_of_prefix ?_ hdwf.sort
          rw [extendAll_eq, extendAll_eq]
          exact (List.prefix_append_right_inj _).mpr ((List.take_prefix i ds).map _)
        exact unfoldOp_subst (getElem?_extend_self (S := S) (d := d₀))
          (scoped_of_sortOf _ hwf.1.sort) hθ₀ _ (sortOf_unfoldTerm ds _ hwf.2 hsort))

end Geb.FreeTopos

end
