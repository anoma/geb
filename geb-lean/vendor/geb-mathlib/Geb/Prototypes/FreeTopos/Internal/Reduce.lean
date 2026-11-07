/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Prototypes.FreeTopos.Internal.Prove

set_option doc.verso true

/-!
# The prover's reductions, their results alone

The prover's reductions ({name}`Geb.FreeTopos.Internal.normalize`,
{name}`Geb.FreeTopos.Internal.eval`) compute, with the term a reduction reaches, the derivation of
its rewriting and a mark of whether it rewrites. The derivation decides nothing the reduction
does: each choice reads the terms and the marks alone, and the mark of a composite rewriting is
the disjunction of its parts'. The reductions below compute the term and the mark alone, by the
same steps, and each is the projection of the reduction it follows
({lit}`normalizeR_eq`, {lit}`evalR_eq`). A checker that performs a reduction for its result, as
the conversion checker's steps do, computes it so without building the derivation it discards,
and the soundness of such a step is that of the reduction it projects.

## Main definitions

* {lit}`normalizeR` — the innermost normalization's result and mark.
* {lit}`ResultReduction`, {lit}`evalR` — the reduction to a depth's result and mark.

## Main statements

* {lit}`normalizeR_eq` — the innermost normalization's result alone is the projection of
  {name}`Geb.FreeTopos.Internal.normalize`.
* {lit}`evalR_eq` — the reduction to a depth's result alone is the projection of
  {name}`Geb.FreeTopos.Internal.eval`.

## Tags

internal language, prover, normalization, reduction, conversion
-/

@[expose] public section

namespace Geb.FreeTopos.Internal

open PartialHorn (Tree)

/-- A reduction's result and mark, its derivation left out. -/
def Reduced.result (x : Term × Deriv × Bool) : Term × Bool := (x.1, x.2.2)

variable (G : Globals) (E : Array Entry) (n : ℕ)

/-- One step of the normalization innermost first, its result and mark alone, the subterms
normalized by {lit}`rec`: the step {name}`Geb.FreeTopos.Internal.normStep` takes. -/
def normStepR (rs : List NormRule) (rec : List Tree → List Term → Term → Option (Term × Bool)) :
    List Tree → List Term → Term → Option (Term × Bool) := fun Γ Φ t ↦ do
  let Γs ← childCtxs G n t.label t.children Γ Φ
  let cs ← (Γs.zip t.children).mapM fun ((Δ, Ψ), u) ↦ rec Δ Ψ u
  let t₁ := RoseTree.node t.label (cs.map Prod.fst)
  match rootRewrite G E n rs Γ Φ t₁ with
  | some (t₂, _) => do
    let (t₃, _) ← rec Γ Φ t₂
    pure (t₃, true)
  | none => pure (t₁, cs.any (·.2))

/-- The normal form of a term in a context under hypotheses, by rules, innermost first, within a
depth of {lit}`fuel`, marked when it rewrites: the result of
{name}`Geb.FreeTopos.Internal.normalize`. -/
def normalizeR (rs : List NormRule) (fuel : ℕ) :
    List Tree → List Term → Term → Option (Term × Bool) :=
  fuel.rec (fun _ _ t ↦ some (t, false)) fun _ rec ↦ normStepR G E n rs rec

/-- A reduction of terms to a depth, its result in a context under hypotheses marked when it
rewrites. -/
abbrev ResultReduction : Type := Depth → List Tree → List Term → Term → Option (Term × Bool)

/-- The first rule that rewrites a term at its root, its result reduced to a depth by
{lit}`rec`; or the term with the mark {lit}`b₁`: the result of
{name}`Geb.FreeTopos.Internal.atRoot`. -/
def atRootR (rs : List NormRule) (rec : ResultReduction) (Γ : List Tree) (Φ : List Term)
    (dp : Depth) (t₁ : Term) (b₁ : Bool) : Option (Term × Bool) :=
  match rootRewrite G E n rs Γ Φ t₁ with
  | some (t₂, _) => do
    let (t₃, _) ← rec dp Γ Φ t₂
    pure (t₃, true)
  | none => pure (t₁, b₁)

/-- The reduction of an application's argument once its function {lit}`f'` is in weak head normal
form, its result and mark alone: its weak normal form where the function is an abstraction whose
variable {lit}`uses` counts more than once, the argument itself where it counts once at most,
and its weak head normal form where the function is not an abstraction. -/
def argR (rec : ResultReduction) (Γ : List Tree) (Φ : List Term) (f' u : Term) :
    Option (Term × Bool) :=
  match f'.label, f'.children with
  | .lam _, [b] => if uses b 0 < 2 then some (u, false) else rec .weak Γ Φ u
  | _, _ => rec .head Γ Φ u

/-- One step of the weak head normal form at a node other than an application of a function to
an argument, its result and mark alone: the first rule that rewrites the root, else the weak head
normal form of the child it depends on and the first rule that then rewrites the root. -/
def headOtherR (rs : List NormRule) (rec : ResultReduction) (Γ : List Tree) (Φ : List Term)
    (t : Term) : Option (Term × Bool) :=
  match rootRewrite G E n rs Γ Φ t with
  | some (t₁, _) => do
    let (t₂, _) ← rec .head Γ Φ t₁
    pure (t₂, true)
  | none => match headChild t.label t.children with
    | none => some (t, false)
    | some i => do
      let c ← t.children[i]?
      let (c', bc) ← rec .head Γ Φ c
      if bc then atRootR G E n rs rec Γ Φ .head (RoseTree.node t.label (t.children.set i c')) true
      else some (t, false)

/-- One step of the weak head normal form, its result and mark alone, the subterms reduced by
{lit}`rec`: the step {name}`Geb.FreeTopos.Internal.headStep` takes. -/
def headStepR (rs : List NormRule) (rec : ResultReduction) (Γ : List Tree) (Φ : List Term)
    (t : Term) : Option (Term × Bool) :=
  match t.label, t.children with
  | .app, [f, u] => do
    let (f', bf) ← rec .head Γ Φ f
    let (u', bu) ← argR rec Γ Φ f' u
    atRootR G E n rs rec Γ Φ .head (Term.app f' u') (bf || bu)
  | _, _ => headOtherR G E n rs rec Γ Φ t

/-- The reduction past the weak head normal form {lit}`w`, reached with the mark {lit}`bw`, to a
depth, its result and mark alone, the subterms reduced by {lit}`rec`: the step
{name}`Geb.FreeTopos.Internal.deepStep` takes. -/
def deepStepR (rs : List NormRule) (rec : ResultReduction) (depth : Depth) (Γ : List Tree)
    (Φ : List Term) (w : Term) (bw : Bool) : Option (Term × Bool) :=
  match depth with
  | .head => pure (w, bw)
  | .weak => do
    let cs ← w.children.zipIdx.mapM fun (u, i) ↦
      if keepsWeak w.label i then some (u, false) else rec .weak Γ Φ u
    let t₁ := RoseTree.node w.label (cs.map Prod.fst)
    if cs.any (·.2) then atRootR G E n rs rec Γ Φ .weak t₁ true else pure (t₁, bw)
  | .open => do
    let Γs ← childCtxs G n w.label w.children Γ Φ
    let cs ← ((Γs.zip w.children).zipIdx).mapM fun (((Δ, Ψ), u), i) ↦
      if keepsFold w.label i then some (u, false) else rec .open Δ Ψ u
    let t₁ := RoseTree.node w.label (cs.map Prod.fst)
    if cs.any (·.2) then atRootR G E n rs rec Γ Φ .open t₁ true else pure (t₁, bw)
  | .full => do
    let Γs ← childCtxs G n w.label w.children Γ Φ
    let cs ← (Γs.zip w.children).mapM fun ((Δ, Ψ), u) ↦ rec .full Δ Ψ u
    let t₁ := RoseTree.node w.label (cs.map Prod.fst)
    match rootRewrite G E n rs Γ Φ t₁ with
    | some (t₂, _) => do
      let (t₃, _) ← rec .full Γ Φ t₂
      pure (t₃, true)
    | none => pure (t₁, bw || cs.any (·.2))

/-- One step of the reduction to a depth, its result and mark alone: the weak head normal form,
and the reduction past it, the subterms reduced by {lit}`rec`. -/
def evalStepR (rs : List NormRule) (rec : ResultReduction) : ResultReduction :=
  fun depth Γ Φ t ↦ do
    let (w, bw) ← headStepR G E n rs rec Γ Φ t
    deepStepR G E n rs rec depth Γ Φ w bw

/-- The reduction of a term in a context under hypotheses, by rules, to a depth, within a depth
of recursion of {lit}`fuel`, marked when it rewrites: the result of
{name}`Geb.FreeTopos.Internal.eval`. -/
def evalR (rs : List NormRule) (fuel : ℕ) : ResultReduction :=
  fuel.rec (fun _ _ _ t ↦ some (t, false)) fun _ rec ↦ evalStepR G E n rs rec

/-! The results alone are the projections. -/

/-- The mark of one rewriting after another is the disjunction of theirs. -/
theorem dTrans_snd (d₁ d₂ : Deriv × Bool) : (dTrans d₁ d₂).2 = (d₁.2 || d₂.2) := by
  rcases d₁ with ⟨_, _ | _⟩ <;> rcases d₂ with ⟨_, _ | _⟩ <;> rfl

/-- The mark of a congruence is the disjunction of its children's. -/
theorem dCong_snd (cs : List (Deriv × Bool)) : (dCong cs).2 = cs.any (·.2) := by
  unfold dCong
  split <;> simp_all [dRefl]

/-- A function's results at each element of a list, each mapped, are the map of its results. -/
theorem mapM_map_result {α β γ : Type} (f : α → Option β) (g : β → γ) (l : List α) :
    (l.mapM f).map (List.map g) = l.mapM fun a ↦ (f a).map g :=
  List.rec (by simp) (fun a l ih ↦ by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def]
    cases f a with
    | none => rfl
    | some b =>
      simp only [Option.bind_some, Option.map_some]
      rw [← ih]
      cases l.mapM f <;> rfl) l

/-- A reduction's results alone. -/
def Reduction.result (rec : Reduction) : ResultReduction := fun dp Γ Φ t ↦
  (rec dp Γ Φ t).map Reduced.result

/-- The rewriting at the root, its result alone, is {lit}`atRootR` at the results alone. -/
theorem atRoot_result (rs : List NormRule) (rec : Reduction) (Γ : List Tree) (Φ : List Term)
    (dp : Depth) (t₁ : Term) (d₁ : Deriv × Bool) :
    (atRoot G E n rs rec Γ Φ dp t₁ d₁).map Reduced.result =
      atRootR G E n rs rec.result Γ Φ dp t₁ d₁.2 := by
  unfold atRoot atRootR Reduction.result
  cases rootRewrite G E n rs Γ Φ t₁ with
  | none => rfl
  | some p =>
    simp only [Option.bind_eq_bind, Option.pure_def]
    cases rec dp Γ Φ p.1 with
    | none => rfl
    | some x => simp [Reduced.result, dTrans_snd]

/-- The congruence rewriting one child of a list in its place, the others by the identity, is
marked where that child's rewriting is. -/
theorem dCong_set_snd {cs : List Term} {i : ℕ} {c : Term} (hi : cs[i]? = some c)
    (dc : Deriv × Bool) :
    (dCong ((List.range cs.length).map fun j ↦ if j = i then dc else dRefl)).2 = dc.2 := by
  have hlt : i < cs.length := (List.getElem?_eq_some_iff.mp hi).1
  rw [dCong_snd, List.any_map]
  cases hd : dc.2 with
  | true => exact List.any_eq_true.mpr ⟨i, List.mem_range.mpr hlt, by simp [hd]⟩
  | false =>
    refine List.any_eq_false.mpr fun j _ ↦ ?_
    by_cases hj : j = i <;> simp [hj, hd, dRefl]

/-- The reduction of an application's argument, its result alone, is {lit}`argR` at the results
alone. -/
theorem arg_result (rec : Reduction) (Γ : List Tree) (Φ : List Term) (f' u : Term)
    (k : Term × Deriv × Bool → Option (Term × Deriv × Bool))
    (k' : Term × Bool → Option (Term × Bool))
    (hk : ∀ x, (k x).map Reduced.result = k' (Reduced.result x)) :
    (match f'.label, f'.children with
      | .lam _, [b] => if uses b 0 < 2 then k (u, dRefl) else (rec .weak Γ Φ u).bind k
      | _, _ => (rec .head Γ Φ u).bind k).map Reduced.result =
      (argR rec.result Γ Φ f' u).bind k' := by
  have hb (o : Option (Term × Deriv × Bool)) :
      (o.bind k).map Reduced.result = (o.map Reduced.result).bind k' := by
    cases o <;> simp [hk]
  unfold argR Reduction.result
  generalize f'.label = l
  generalize f'.children = cs
  cases l <;> rcases cs with _ | ⟨b, _ | ⟨c, cs⟩⟩ <;> dsimp only <;> try exact hb _
  split
  · simp [hk, Reduced.result, dRefl]
  · exact hb _

/-- One step of the weak head normal form, its result alone, is {lit}`headStepR` at the results
alone. -/
theorem headStep_result (rs : List NormRule) (rec : Reduction) (Γ : List Tree) (Φ : List Term)
    (t : Term) :
    (headStep G E n rs rec Γ Φ t).map Reduced.result = headStepR G E n rs rec.result Γ Φ t := by
  unfold headStep headStepR headOtherR
  generalize t.label = l
  generalize t.children = cs
  cases l <;> rcases cs with _ | ⟨f, _ | ⟨u, _ | ⟨w, cs⟩⟩⟩ <;> dsimp only
  case app.cons.cons.nil =>
    simp only [Option.bind_eq_bind]
    cases hf : rec .head Γ Φ f with
    | none => simp [Reduction.result, hf]
    | some x =>
      obtain ⟨f', df⟩ := x
      simp only [Reduction.result, hf, Option.bind_some, Option.map_some, Reduced.result]
      refine arg_result rec Γ Φ f' u
        (fun x ↦ atRoot G E n rs rec Γ Φ .head (Term.app f' x.1) (dCong [df, x.2]))
        (fun x ↦ atRootR G E n rs rec.result Γ Φ .head (Term.app f' x.1) (df.2 || x.2))
        fun ⟨u', du⟩ ↦ ?_
      rw [atRoot_result, dCong_snd]
      simp [Reduced.result]
  all_goals
    split
    · rename_i t₁ dr hr
      simp only [hr, Option.bind_eq_bind, Option.pure_def]
      cases h₂ : rec .head Γ Φ t₁ <;> simp [Reduction.result, h₂, Reduced.result, dTrans_snd]
    · rename_i hr
      simp only [hr]
      split
      · rename_i hh
        simp [hh, Reduced.result, dRefl]
      · rename_i i hh
        simp only [hh, Option.bind_eq_bind]
        cases hc : (_ : List Term)[i]? with
        | none => rfl
        | some c =>
          simp only [Option.bind_some]
          cases h₂ : rec .head Γ Φ c with
          | none => simp [Reduction.result, h₂]
          | some x =>
            obtain ⟨c', dc⟩ := x
            simp only [Reduction.result, h₂, Option.bind_some, Option.map_some, Reduced.result]
            split
            · rename_i hb
              rw [atRoot_result, dCong_set_snd hc, hb]
            · simp [Reduced.result, dRefl]

/-- The results of a function at each element of a list, followed by a computation from them,
the result alone, are the results alone followed by a computation from those, where the
function's and the computation's results alone are those of the second pair. -/
theorem mapM_bind_result {α : Type} (l : List α) (f : α → Option (Term × Deriv × Bool))
    (f' : α → Option (Term × Bool)) (hf : ∀ a, (f a).map Reduced.result = f' a)
    (K : List (Term × Deriv × Bool) → Option (Term × Deriv × Bool))
    (K' : List (Term × Bool) → Option (Term × Bool))
    (hK : ∀ cs, (K cs).map Reduced.result = K' (cs.map Reduced.result)) :
    ((l.mapM f).bind K).map Reduced.result = (l.mapM f').bind K' := by
  have : l.mapM f' = (l.mapM f).map (List.map Reduced.result) := by
    rw [mapM_map_result]
    congr 1
    funext a
    exact (hf a).symm
  rw [this]
  cases l.mapM f <;> simp [hK]

/-- A list's terms, its results' terms. -/
theorem map_result_fst (cs : List (Term × Deriv × Bool)) :
    (cs.map Reduced.result).map Prod.fst = cs.map Prod.fst := by
  simp [Reduced.result, Function.comp_def]

/-- Whether a list of results is marked, its results' marks. -/
theorem any_result (cs : List (Term × Deriv × Bool)) :
    (cs.map Reduced.result).any (·.2) = cs.any (·.2.2) := by
  simp [List.any_map, Reduced.result, Function.comp_def]

/-- Whether a list of derivations of results is marked, its results' marks. -/
theorem any_snd (cs : List (Term × Deriv × Bool)) :
    (cs.map Prod.snd).any (·.2) = cs.any (·.2.2) := by
  simp [List.any_map, Function.comp_def]

/-- The reduction past a weak head normal form, its result alone, is {lit}`deepStepR` at the
results alone. -/
theorem deepStep_result (rs : List NormRule) (rec : Reduction) (depth : Depth) (Γ : List Tree)
    (Φ : List Term) (w : Term) (dw : Deriv × Bool) :
    (deepStep G E n rs rec depth Γ Φ w dw).map Reduced.result =
      deepStepR G E n rs rec.result depth Γ Φ w dw.2 := by
  cases depth with
  | head => rfl
  | weak =>
    simp only [deepStep, deepStepR, Option.bind_eq_bind]
    refine mapM_bind_result _ _ _ (fun ⟨u, i⟩ ↦ ?_) _ _ fun cs ↦ ?_
    · rw [any_result, map_result_fst]
      split
      · rename_i h
        rw [atRoot_result, dTrans_snd, dCong_snd, any_snd, h, Bool.or_true]
      · rename_i h
        rw [Bool.not_eq_true] at h
        simp only [Option.pure_def, Option.map_some, Reduced.result, dTrans_snd, dCong_snd,
          any_snd, h, Bool.or_false]
    · split <;> simp_all [Reduction.result, Reduced.result, dRefl]
  | «open» =>
    simp only [deepStep, deepStepR, Option.bind_eq_bind]
    cases childCtxs G n w.label w.children Γ Φ with
    | none => rfl
    | some Γs =>
      simp only [Option.bind_some]
      refine mapM_bind_result _ _ _ (fun ⟨⟨⟨Δ, Ψ⟩, u⟩, i⟩ ↦ ?_) _ _ fun cs ↦ ?_
      · rw [any_result, map_result_fst]
        split
        · rename_i h
          rw [atRoot_result, dTrans_snd, dCong_snd, any_snd, h, Bool.or_true]
        · rename_i h
          rw [Bool.not_eq_true] at h
          simp only [Option.pure_def, Option.map_some, Reduced.result, dTrans_snd, dCong_snd,
            any_snd, h, Bool.or_false]
      · split <;> simp_all [Reduction.result, Reduced.result, dRefl]
  | full =>
    simp only [deepStep, deepStepR, Option.bind_eq_bind]
    cases childCtxs G n w.label w.children Γ Φ with
    | none => rfl
    | some Γs =>
      simp only [Option.bind_some]
      refine mapM_bind_result _ _ _ (fun ⟨⟨Δ, Ψ⟩, u⟩ ↦ rfl) _ _ fun cs ↦ ?_
      rw [any_result, map_result_fst]
      cases hr : rootRewrite G E n rs Γ Φ (RoseTree.node w.label (cs.map Prod.fst)) with
      | none => simp [Reduced.result, dTrans_snd, dCong_snd, Function.comp_def]
      | some p =>
        simp only [Option.pure_def]
        cases h₃ : rec .full Γ Φ p.1 <;>
          simp [Reduction.result, h₃, Reduced.result, dTrans_snd]

/-- One step of the reduction to a depth, its result alone, is {lit}`evalStepR` at the results
alone. -/
theorem evalStep_result (rs : List NormRule) (rec : Reduction) :
    (evalStep G E n rs rec).result = evalStepR G E n rs rec.result := by
  funext depth Γ Φ t
  have hh := headStep_result G E n rs rec Γ Φ t
  simp only [Reduction.result, evalStep, evalStepR, Option.bind_eq_bind] at hh ⊢
  rw [← hh]
  cases headStep G E n rs rec Γ Φ t with
  | none => rfl
  | some x => exact deepStep_result G E n rs rec depth Γ Φ x.1 x.2

/-- The reduction to a depth, computing its result alone, is the projection of
{name}`Geb.FreeTopos.Internal.eval`, at every fuel. -/
theorem evalR_eq (rs : List NormRule) (fuel : ℕ) :
    evalR G E n rs fuel = (eval G E n rs fuel).result :=
  Nat.rec (motive := fun f ↦ evalR G E n rs f = (eval G E n rs f).result) rfl
    (fun k ih ↦ by
      change evalStepR G E n rs (evalR G E n rs k) = (evalStep G E n rs (eval G E n rs k)).result
      rw [ih, evalStep_result]) fuel

/-- One step of the normalization innermost first, its result alone, is {lit}`normStepR` at the
results alone. -/
theorem normStep_result (rs : List NormRule)
    (rec : List Tree → List Term → Term → Option (Term × Deriv × Bool)) (Γ : List Tree)
    (Φ : List Term) (t : Term) :
    (normStep G E n rs rec Γ Φ t).map Reduced.result =
      normStepR G E n rs (fun Γ Φ t ↦ (rec Γ Φ t).map Reduced.result) Γ Φ t := by
  simp only [normStep, normStepR, Option.bind_eq_bind]
  cases childCtxs G n t.label t.children Γ Φ with
  | none => rfl
  | some Γs =>
    simp only [Option.bind_some]
    refine mapM_bind_result _ _ _ (fun ⟨⟨Δ, Ψ⟩, u⟩ ↦ rfl) _ _ fun cs ↦ ?_
    rw [map_result_fst, any_result]
    cases hr : rootRewrite G E n rs Γ Φ (RoseTree.node t.label (cs.map Prod.fst)) with
    | none =>
      simp only [Option.pure_def, Option.map_some]
      split <;> simp_all [Reduced.result, dRefl]
    | some p =>
      simp only [Option.pure_def]
      cases rec Γ Φ p.1 <;> simp [Reduced.result, dTrans_snd]

/-- The innermost normalization, computing its result alone, is the projection of
{name}`Geb.FreeTopos.Internal.normalize`, at every fuel. -/
theorem normalizeR_eq (rs : List NormRule) (fuel : ℕ) :
    normalizeR G E n rs fuel = fun Γ Φ t ↦ (normalize G E n rs fuel Γ Φ t).map Reduced.result :=
  Nat.rec (motive := fun f ↦
      normalizeR G E n rs f = fun Γ Φ t ↦ (normalize G E n rs f Γ Φ t).map Reduced.result)
    rfl
    (fun k ih ↦ by
      change normStepR G E n rs (normalizeR G E n rs k) = fun Γ Φ t ↦
        (normStep G E n rs (normalize G E n rs k) Γ Φ t).map Reduced.result
      funext Γ Φ t
      rw [ih, normStep_result]) fuel

end Geb.FreeTopos.Internal

end
