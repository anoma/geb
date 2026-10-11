/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Prototypes.LF.Topos.ProofCheck
public import Geb.Prototypes.LF.Topos.Theorems
import Mathlib.Data.Nat.Cast.Order.Basic -- shake: keep
import Mathlib.Tactic.NormNum

set_option doc.verso true in
/-!
# The soundness of the decoding of proofs

A canonical LF term of the family of proofs of a formula, in an LF context of term and proof
variables inside variables of {lit}`tp`, decodes ({name}`Geb.LF.Topos.decPf`) to a derivation
that the internal language's checker accepts as a proof of the formula's decoding, in the internal
context of the term variables' types under the hypotheses of the proof variables' formulas, in as
many object variables as the context has variables of {lit}`tp`. The signature may be extended
by the theorems of a development, the unfoldings of definitions and the inductions on quotients
({name}`Geb.LF.Topos.ExtDecl`), whose applications decode to the language's applications of the
theorems' entries, to the unfoldings and to the language's inductions on the quotients. The
declaration of an induction on a quotient, its leading arguments substituted, is its body at the
encodings of the quotient and of the projection's domain at the objects they decode to
({lit}`hsubs_quotBody`), and the rest of its spine decodes as that of the case analysis on a
coproduct does ({lit}`sound_quotBody`).

## Main definitions

* {lit}`TmCtx` — an LF context of proofs matches an environment and an internal context at its
  term variables.
* {lit}`PfCtx` — it matches them at its proof variables, and hypotheses.

## Main statements

* {lit}`termOf_typed` — the adequacy of the representation of terms in an LF context of proofs.
* {lit}`thm_spine` — the decoding of the spine of an application of a theorem's declaration.
* {lit}`sound_thm` — the soundness of the decoding of an application of a theorem.
* {lit}`deltaThm_wellFormed` — the unfolding of a definition the language admits is well formed.
* {lit}`sound_delta` — the soundness of the decoding of an application of an unfolding.
* {lit}`sound_quotInd` — the soundness of the decoding of an application of the induction on a
  quotient.
* {lit}`pfSound`, {lit}`decPf_sound` — the soundness of the decoding of proofs.
* {lit}`decPf_checks` — a proof in a context of term variables decodes to a derivation of a
  theorem of the internal language.

## Implementation notes

The type of a rule instantiates along its arguments by hereditary substitution, which leaves the
instances of a motive, an LF abstraction, at its arguments: these are renamings of the motive's
body where the argument is a variable ({lit}`hsub_var_base`), substitutions into it that commute
with the surrounding renamings where it is a term ({lit}`hsub_hole`), and are left in place by the
substitution of a proof, whose variable they do not mention ({lit}`hsubWith_vacuous'`).

## References

* \[HarperLicata2007\], Sections 3.2 and 3.4, for the adequacy of the representations of
  syntax and of judgments.

## Tags

logical framework, LF, adequacy, soundness, proof, derivation, internal language
-/

set_option doc.verso true

@[expose] public section

namespace Geb.LF.Topos

open FreeTopos.Internal (Term Deriv Globals Entry check typeIn instVar weaken1 ctxObj stdEnv)

/-- An LF context of proofs matches an environment and an internal context in {lit}`n` object
variables at its term variables: its declarations past the environment's are the {lit}`n` of
{lit}`tp`, and the others of families of terms or of proofs; each variable of a family of terms is
of the encoding, at the offset of the environment's variables, of the type the environment's
renaming of its variable indexes in the internal context; the internal context has as many
variables as the environment has term variables, and its types are encoded. -/
structure TmCtx (k : PrimIdx) (n : ℕ) (ΓLF : Ctx) (env : List (Option ℕ))
    (Γ : List PartialHorn.Tree) : Prop where
  len : ΓLF.length = env.length + n
  shape : ∀ a ∈ ΓLF, (∃ A, a = tm A) ∨ (∃ F, a = pf F) ∨ a = tp
  tpVar : ∀ i, ΓLF[i]? = some tp ↔ env.length ≤ i ∧ i < env.length + n
  tmVar : ∀ (i : ℕ) (A : Expr), varType ΓLF i = some (tm A) →
    ∃ a, encTy k env.length a = some A ∧ Γ[tmIdx env i]? = some a
  numTm : Γ.length = numTm env
  enc : ∃ ΓT, encCtx k n Γ = some ΓT

variable {sg : Sig} {n : ℕ} {ΓLF : Ctx} {env : List (Option ℕ)} {Γ : List PartialHorn.Tree}
  {k : PrimIdx}

/-- The family of proofs is injective. -/
theorem pf_inj {F F' : Expr} (h : pf F = pf F') : F = F' := by
  simpa only [pf, Expr.const, Expr.app, node_inj, List.cons.injEq, and_true, true_and] using h

/-- No family of proofs is a family of terms. -/
theorem pf_ne_tm {F A : Expr} : pf F ≠ tm A := fun h ↦ by
  have := congrArg RoseTree.label h
  simp only [pf, tm, Expr.const, Expr.app, RoseTree.label_node, Label.app.injEq,
    Head.const.injEq] at this
  exact absurd this (by decide)

/-- No family of terms is the kind of types. -/
theorem tm_ne_tp {A : Expr} : tm A ≠ tp := fun h ↦ by
  have := congrArg RoseTree.label h
  simp only [tp, tm, Expr.const, Expr.app, RoseTree.label_node, Label.app.injEq,
    Head.const.injEq] at this
  exact absurd this (by decide)

/-- No family of proofs is the kind of types. -/
theorem pf_ne_tp {F : Expr} : pf F ≠ tp := fun h ↦ by
  have := congrArg RoseTree.label h
  simp only [tp, pf, Expr.const, Expr.app, RoseTree.label_node, Label.app.injEq,
    Head.const.injEq] at this
  exact absurd this (by decide)

/-- A renamed expression that is a family of terms is the family of terms of the renamed
index. -/
theorem tm_rename_inj {B T : Expr} {ρ : ℕ → ℕ} (h : T.rename ρ = tm B) :
    ∃ B₀, T = tm B₀ ∧ B = B₀.rename ρ := by
  obtain ⟨l, cs, rfl⟩ : ∃ l cs, T = RoseTree.node l cs :=
    ⟨_, _, (RoseTree.node_label_children T).symm⟩
  rw [rename_node, tm, Expr.const, Expr.app, node_inj] at h
  obtain ⟨hl, hcs⟩ := h
  rcases l with _ | _ | _ | (i | c)
  · exact absurd hl (by simp [Label.rename])
  · exact absurd hl (by simp [Label.rename])
  · exact absurd hl (by simp [Label.rename])
  · exact absurd hl (by simp [Label.rename, Head.rename])
  · obtain rfl : c = 6 := by simpa [Label.rename, Head.rename] using hl
    rcases cs with _ | ⟨B₀, _ | ⟨B₁, cs⟩⟩
    · exact absurd hcs (by simp)
    · simp only [List.zipIdx_cons, List.zipIdx_nil, List.map_cons, List.map_nil, Label.binders,
        Function.iterate_zero, id, List.cons.injEq, and_true] at hcs
      exact ⟨B₀, rfl, hcs.symm⟩
    · exact absurd hcs (by simp)

/-- The renaming of a context's variables past an environment's to the internal context's moves
them past the environment's term variables. -/
theorem tmIdx_ge : ∀ (env : List (Option ℕ)) (i : ℕ), env.length ≤ i →
    tmIdx env i + env.length = i + numTm env := by
  intro env
  refine List.rec (motive := fun env ↦ ∀ i, env.length ≤ i →
    tmIdx env i + env.length = i + numTm env) (fun i _ ↦ rfl) (fun o env ih i hi ↦ ?_) env
  rcases i with _ | i
  · exact absurd hi (Nat.not_succ_le_zero _)
  · have := ih i (Nat.le_of_succ_le_succ hi)
    rcases o with _ | h
    · change liftR (tmIdx env) (i + 1) + (env.length + 1) = i + 1 + (numTm env + 1)
      simp only [liftR]
      omega
    · change tmIdx env i + (env.length + 1) = i + 1 + numTm env
      omega

/-- The declarations of a context matching an environment have the shape of types whose
products' domains are of terms. -/
theorem TmCtx.typeShape (hc : TmCtx k n ΓLF env Γ) :
    ∀ a ∈ ΓLF, Expr.TypeShape a = true ∧ Expr.DomsOK a = true := fun a ha ↦ by
  rcases hc.shape a ha with ⟨A, rfl⟩ | ⟨F, rfl⟩ | rfl <;>
    exact ⟨by simp only [tm, pf, tp, Expr.const, Expr.app, typeShape_node]; rfl,
      by simp only [tm, pf, tp, Expr.const, Expr.app, domsOK_node]; rfl⟩

/-- The variables of a context matching an environment whose types are families of terms are
inside the environment's. -/
theorem TmCtx.lt_of_varType_tm (hc : TmCtx k n ΓLF env Γ) {i : ℕ} {A : Expr}
    (h : varType ΓLF i = some (tm A)) : i < env.length := by
  obtain ⟨T, hT, hTA⟩ := Option.map_eq_some_iff.mp h
  by_contra hi
  have hlen := (List.getElem?_eq_some_iff.mp hT).1
  obtain rfl : T = tp := by
    rcases hc.shape T (List.mem_of_getElem? hT) with ⟨B, rfl⟩ | ⟨F, rfl⟩ | rfl
    · exact absurd ((hc.tpVar i).mpr ⟨by omega, by rw [hc.len] at hlen; omega⟩) (by
        rw [hT]; exact fun h ↦ tm_ne_tp (Option.some.inj h))
    · exact absurd ((hc.tpVar i).mpr ⟨by omega, by rw [hc.len] at hlen; omega⟩) (by
        rw [hT]; exact fun h ↦ pf_ne_tp (Option.some.inj h))
    · rfl
  rw [tp_rename] at hTA
  exact tm_ne_tp hTA.symm

/-- A context matching an environment, extended by the family of terms of an encoded type,
matches the environment extended by a term variable and the internal context extended by the
type. -/
theorem TmCtx.consTm (hc : TmCtx k n ΓLF env Γ) {a : PartialHorn.Tree} {A : Expr}
    (ha : encTy k env.length a = some A) : TmCtx k n (tm A :: ΓLF) (none :: env) (a :: Γ) where
  len := by rw [List.length_cons, hc.len, List.length_cons]; omega
  shape b hb := by
    rcases List.mem_cons.mp hb with rfl | hb
    · exact .inl ⟨A, rfl⟩
    · exact hc.shape b hb
  tpVar i := by
    rcases i with _ | i
    · simp only [List.getElem?_cons_zero, Option.some.injEq, List.length_cons]
      exact ⟨fun h ↦ absurd h tm_ne_tp, fun h ↦ absurd h.1 (Nat.not_succ_le_zero _)⟩
    · rw [List.getElem?_cons_succ, hc.tpVar i, List.length_cons]
      exact ⟨fun h ↦ ⟨by omega, by omega⟩, fun h ↦ ⟨by omega, by omega⟩⟩
  tmVar i B hi := by
    rcases i with _ | i
    · have hB : tm B = tm (A.rename (· + 1)) := by
        rw [← tm_rename]
        exact (Option.some.inj hi).symm
      obtain rfl := tm_inj hB
      exact ⟨a, by rw [List.length_cons]; exact encTy_add ha, rfl⟩
    · rw [varType_cons_succ] at hi
      obtain ⟨T, hT, hTB⟩ := Option.map_eq_some_iff.mp hi
      obtain ⟨B₀, rfl, rfl⟩ := tm_rename_inj hTB
      obtain ⟨b, hb, hΓ⟩ := hc.tmVar i B₀ hT
      exact ⟨b, by rw [List.length_cons]; exact encTy_add hb, hΓ⟩
  numTm := by rw [List.length_cons, hc.numTm]; rfl
  enc := by
    obtain ⟨ΓT, hΓ⟩ := hc.enc
    exact ⟨_, encCtx_cons (encTy_rename a _ A ha Γ.length (fun i ↦ i - env.length + Γ.length)
      fun i hi ↦ by beta_reduce; omega) hΓ⟩

variable {G : Globals}

/-- The standard environment of a context has a variable for each of its types. -/
theorem length_stdEnv (Γ : List PartialHorn.Tree) : (stdEnv Γ).length = Γ.length :=
  (List.length_map (f := Prod.snd)).symm.trans
    (congrArg List.length (FreeTopos.Internal.map_snd_stdEnv Γ))

/-- The adequacy of the representation of terms in an LF context of proofs: a canonical term of
the family of terms of an encoded type, in a context matching an environment and an internal
context, decodes in the environment to a term of the type in the internal context. A term
mentions no proof variable, its type's products' domains being of terms, so that its renaming to
the internal context's variables checks in the context of the term variables and the variables of
{lit}`tp` alone. -/
theorem termOf_typed (hk : k.Valid G) (hsg : SigExt G k sg)
    (hc : TmCtx k n ΓLF env Γ) {a : PartialHorn.Tree} {A M : Expr}
    (ha : encTy k env.length a = some A) (hj : judge sg M ΓLF (.check (tm A)) = true) :
    ∃ s, termOf k env M = some s ∧ typeIn G n Γ s = some a := by
  have ho := judge_occursOnly hsg M ΓLF (tm A) hc.typeShape
    (by simp only [tm, Expr.const, Expr.app, typeShape_node]; rfl) rfl
    (by simp only [tm, Expr.const, Expr.app, domsOK_node]; rfl) hj
  obtain ⟨ΓT, hΓT⟩ := hc.enc
  have hρ' : ∀ i, env.length ≤ i → tmIdx env i + env.length = i + Γ.length := fun i hi ↦ by
    rw [hc.numTm]
    exact tmIdx_ge env i hi
  have hρ : CtxRenOn (fun i ↦ (varType ΓLF i).any TermHead) ΓLF ΓT (tmIdx env) := by
    intro i T hS hT
    obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp hT
    rcases hc.shape b (List.mem_of_getElem? hb) with ⟨B, rfl⟩ | ⟨F, rfl⟩ | rfl
    · obtain ⟨c, hc', hΓ⟩ := hc.tmVar i (B.rename (· + (i + 1))) (by
        rw [varType, hb, Option.map_some, tm_rename])
      obtain ⟨B', hB', hv⟩ := varType_encCtx hΓT hΓ
      rw [hv, tm_rename, tm_rename,
        Option.some.inj (hB'.symm.trans (encTy_rename c _ _ hc' _ _ hρ'))]
    · simp only [hT, Option.any_some, TermHead, headDepth_rename, pf, Expr.const, Expr.app,
        headDepth_node, headDepthStep] at hS
      exact absurd hS (by decide)
    · obtain ⟨hi, hin⟩ := (hc.tpVar i).mp hb
      have := hρ' i hi
      rw [show tmIdx env i = Γ.length + (i - env.length) by omega,
        varType_encCtx_tp hΓT (by omega), tp_rename, tp_rename]
  have hj' := judge_renameOn (Sig.ok_closed hsg.ok) M (.check (tm A)) hρ ho hj
  rw [Mode.rename, tm_rename] at hj'
  have hA' := encTy_rename a _ A ha Γ.length (tmIdx env) hρ'
  obtain ⟨s, r, hd, hcomp, hr, -⟩ := (tmComplete hsg hk (M.rename (tmIdx env))).1
    (ctxObj Γ) (stdEnv Γ) ΓT _ (by rw [FreeTopos.Internal.map_snd_stdEnv]; exact hΓT) hj'
  rw [length_stdEnv, hc.numTm] at hd hr
  refine ⟨s, hd, ?_⟩
  rw [typeIn, hcomp, Option.map_some, encTy_inj hr (hc.numTm ▸ hA')]

/-- A term weakened by a new innermost variable has, in the context extended by the variable's
type, the type it had. -/
theorem typeIn_weaken1 {s : Term} {C a : PartialHorn.Tree} (h : typeIn G n Γ s = some C) :
    typeIn G n (a :: Γ) (weaken1 s) = some C := by
  obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp h
  have hsnd : (stdEnv (a :: Γ)).tail.map Prod.snd = (stdEnv Γ).map Prod.snd := by
    rw [List.map_tail, FreeTopos.Internal.map_snd_stdEnv, FreeTopos.Internal.map_snd_stdEnv]
    rfl
  obtain ⟨f, hf⟩ := FreeTopos.Internal.compile_retype s _ _ r hr (ctxObj (a :: Γ)) _ hsnd
  rw [typeIn, weaken1, FreeTopos.Internal.compile_rename s _ _ _ (· + 1) _ hf
    (fun i _ ↦ List.getElem?_tail.symm) fun _ _ ↦ Nat.succ_lt_succ]
  rfl

/-- An environment extended by a term variable has one more term variable. -/
theorem numTm_cons_none (env : List (Option ℕ)) : numTm (none :: env) = numTm env + 1 := rfl

/-- An environment extended by a proof variable has as many term variables. -/
theorem numTm_cons_some (env : List (Option ℕ)) (h : ℕ) : numTm (some h :: env) = numTm env :=
  rfl

/-- The goal that a lifted shift moves the variables past one environment's term variables to
the same positions past another's, for concrete extensions of an environment. -/
local macro "numTm_ren" : tactic =>
  `(tactic| (intro i hi; rcases i with _ | _ | _ | _ | i <;>
    (try simp only [numTm_cons_none, numTm_cons_some, liftR, Function.comp_apply] at hi ⊢) <;>
    omega))

/-- The renaming of a context extended by a term variable, after the weakening of an LF term, is
the weakening of the renaming of the context. -/
theorem tmIdx_none_succ (env : List (Option ℕ)) (i : ℕ) :
    tmIdx (none :: env) (i + 1) = tmIdx env i + 1 := rfl

/-- The renaming of a context extended by a proof variable skips it. -/
theorem tmIdx_some_succ (env : List (Option ℕ)) (h i : ℕ) :
    tmIdx (some h :: env) (i + 1) = tmIdx env i := rfl

/-- The decoding of an LF term weakened by a term variable, in the environment extended by it, is
the weakening of its decoding. -/
theorem termOf_consTm {F : Expr} {j : ℕ} {φ : MTerm}
    (h : termOf k env (F.rename (· + j)) = some φ) :
    termOf k (none :: env) (F.rename (· + (j + 1))) = some (weaken1 φ) := by
  have := dec_rename _ (numTm env) (numTm env + 1) (· + 1) φ h fun i _ ↦ by beta_reduce; omega
  rw [rename_rename, rename_rename] at this
  rw [termOf, rename_rename]
  exact this

/-- The decoding of an LF term weakened by a proof variable, in the environment extended by it,
is its decoding. -/
theorem termOf_consPf {F : Expr} {j h : ℕ} :
    termOf k (some h :: env) (F.rename (· + (j + 1))) =
      termOf k env (F.rename (· + j)) := by
  rw [termOf, termOf, rename_rename, rename_rename]
  rfl

/-- An LF context of proofs matches an environment, an internal context and hypotheses: it
matches the environment and the internal context at its term variables, each proof variable is
of the family of proofs of a formula that decodes to the hypothesis the environment indexes, and
the hypotheses are formulas. -/
structure PfCtx (G : Globals) (k : PrimIdx) (n : ℕ) (ΓLF : Ctx) (env : List (Option ℕ))
    (Γ : List PartialHorn.Tree) (Φ : List Term) : Prop extends TmCtx k n ΓLF env Γ where
  pfVar : ∀ (i : ℕ) (F : Expr), ΓLF[i]? = some (pf F) →
    ∃ h φ, env[i]? = some (some h) ∧ termOf k env (F.rename (· + (i + 1))) = some φ ∧
      Φ[h]? = some φ
  typed : ∀ φ ∈ Φ, typeIn G n Γ φ = some FreeTopos.omega

variable {Φ : List Term}

/-- A context matching an environment, an internal context and hypotheses, extended by the
family of terms of an encoded type, matches them extended by a term variable, the type, and the
hypotheses weakened. -/
theorem PfCtx.consTm (hc : PfCtx G k n ΓLF env Γ Φ) {a : PartialHorn.Tree} {A : Expr}
    (ha : encTy k env.length a = some A) :
    PfCtx G k n (tm A :: ΓLF) (none :: env) (a :: Γ) (Φ.map weaken1) where
  toTmCtx := hc.toTmCtx.consTm ha
  pfVar i F hi := by
    rcases i with _ | i
    · exact absurd (Option.some.inj hi).symm pf_ne_tm
    · obtain ⟨h, φ, he, hφ, hΦ⟩ := hc.pfVar i F hi
      exact ⟨h, weaken1 φ, he, termOf_consTm hφ, by rw [List.getElem?_map, hΦ]; rfl⟩
  typed φ hφ := by
    obtain ⟨ψ, hψ, rfl⟩ := List.mem_map.mp hφ
    exact typeIn_weaken1 (hc.typed ψ hψ)

/-- A context matching an environment, an internal context and hypotheses, extended by the
family of proofs of a formula that decodes to a formula, matches the environment extended by a
proof variable of the next hypothesis, the internal context, and the hypotheses extended by the
formula. -/
theorem PfCtx.consPf (hc : PfCtx G k n ΓLF env Γ Φ) {F : Expr} {φ : MTerm}
    (hφ : termOf k env F = some φ) (hφt : typeIn G n Γ φ = some FreeTopos.omega) :
    PfCtx G k n (pf F :: ΓLF) (some Φ.length :: env) Γ (Φ ++ [φ]) where
  len := by rw [List.length_cons, hc.len, List.length_cons]; omega
  shape b hb := by
    rcases List.mem_cons.mp hb with rfl | hb
    · exact .inr (.inl ⟨F, rfl⟩)
    · exact hc.shape b hb
  tpVar i := by
    rcases i with _ | i
    · simp only [List.getElem?_cons_zero, Option.some.injEq, List.length_cons]
      exact ⟨fun h ↦ absurd h pf_ne_tp, fun h ↦ absurd h.1 (Nat.not_succ_le_zero _)⟩
    · rw [List.getElem?_cons_succ, hc.tpVar i, List.length_cons]
      exact ⟨fun h ↦ ⟨by omega, by omega⟩, fun h ↦ ⟨by omega, by omega⟩⟩
  tmVar i B hi := by
    rcases i with _ | i
    · obtain ⟨B₀, h, -⟩ := tm_rename_inj (Option.some.inj hi)
      exact absurd h pf_ne_tm
    · rw [varType_cons_succ] at hi
      obtain ⟨T, hT, hTB⟩ := Option.map_eq_some_iff.mp hi
      obtain ⟨B₀, rfl, rfl⟩ := tm_rename_inj hTB
      obtain ⟨b, hb, hΓ⟩ := hc.tmVar i B₀ hT
      exact ⟨b, by rw [List.length_cons]; exact encTy_add hb, hΓ⟩
  numTm := hc.numTm
  enc := hc.enc
  pfVar i F' hi := by
    rcases i with _ | i
    · obtain rfl : F = F' := pf_inj (Option.some.inj hi)
      refine ⟨Φ.length, φ, rfl, ?_, by
        rw [List.getElem?_append_right (le_refl _), Nat.sub_self]; rfl⟩
      rw [termOf, rename_rename]
      exact hφ
    · obtain ⟨h, ψ, he, hψ, hΦ⟩ := hc.pfVar i F' hi
      refine ⟨h, ψ, he, by rw [termOf_consPf]; exact hψ, ?_⟩
      rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hΦ).1, hΦ]
  typed ψ hψ := by
    rcases List.mem_append.mp hψ with hψ | hψ
    · exact hc.typed ψ hψ
    · obtain rfl := List.mem_singleton.mp hψ
      exact hφt

/-- A context matching an environment, an internal context and hypotheses matches them with a
further formula among the hypotheses. -/
theorem PfCtx.addHyp (hc : PfCtx G k n ΓLF env Γ Φ) {ψ : Term}
    (hψ : typeIn G n Γ ψ = some FreeTopos.omega) : PfCtx G k n ΓLF env Γ (Φ ++ [ψ]) where
  toTmCtx := hc.toTmCtx
  pfVar i F hi := by
    obtain ⟨h, φ, he, hφ, hΦ⟩ := hc.pfVar i F hi
    exact ⟨h, φ, he, hφ, by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hΦ).1,
      hΦ]⟩
  typed φ hφ := by
    rcases List.mem_append.mp hφ with hφ | hφ
    · exact hc.typed φ hφ
    · obtain rfl := List.mem_singleton.mp hφ
      exact hψ

/-- The declarations whose types end in {lit}`pf` are the rules, of indices from 18 to 29, from
34 to 36, 40 and 41, 45 and 46, 47, and from 53 to 56. -/
theorem sig_head_pf₀ {c : ℕ} {T : Expr} (hc : sig[c]? = some T) (h : T.headDepth.1 = some 17) :
    c ∈ [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 34, 35, 36, 40, 41, 45, 46, 47, 53,
      54, 55, 56] := by
  have key : (sig.zipIdx.all fun p ↦ !(p.1.headDepth.1 == some 17) ||
      decide (p.2 ∈ [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 34, 35, 36, 40, 41, 45, 46,
        47, 53, 54, 55, 56])) = true := by
    decide +kernel
  rw [List.all_eq_true] at key
  obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp hc
  have := key (sig[c], c) (by
    rw [List.mem_iff_getElem]
    exact ⟨c, by simpa using hlt, by simp⟩)
  simp only [h, beq_self_eq_true, Bool.not_true, Bool.false_or, decide_eq_true_eq] at this
  exact this

/-- The declarations of an extension of the signature, within the signature, whose types end in
{lit}`pf` are the signature's rules. -/
theorem sig_head_pf (hsg : SigExt G k sg) {c : ℕ} {T : Expr} (hc : sg[c]? = some T)
    (h : T.headDepth.1 = some 17) (hlt : c < sig.length) :
    c ∈ [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 34, 35, 36, 40, 41, 45, 46, 47, 53,
      54, 55, 56] ∧ sig[c]? = some T := by
  have hc' := hsg.of_lt hc hlt
  exact ⟨sig_head_pf₀ hc' h, hc'⟩

/-- The decoding of an LF abstraction of a proof is its body's. -/
theorem decPf_lam (body : Expr) (env : List (Option ℕ)) (m : ℕ) :
    decPf k (Expr.lam body) env m = decPf k body env m :=
  congrFun (congrFun (RoseTree.para_node _ _ _) env) m

/-- The soundness of the decoding of proofs at a term: in every context matching an environment,
an internal context in {lit}`n` object variables and hypotheses, where the term checks against
the family of proofs of a formula that decodes, it decodes to a derivation that proves the
decoding. -/
def PfSoundAt (sg : Sig) (G : Globals) (k : PrimIdx) (E : Array Entry) (n : ℕ) (M : Expr) :
    Prop :=
  ∀ (ΓLF : Ctx) (env : List (Option ℕ)) (Γ : List PartialHorn.Tree) (Φ : List Term) (F : Expr)
    (φ : MTerm), PfCtx G k n ΓLF env Γ Φ → judge sg M ΓLF (.check (pf F)) = true →
    termOf k env F = some φ →
    ∃ D, decPf k M env Φ.length = some D ∧ (check G E n D).2 Γ Φ φ = true

/-- A property of the bodies of a term where it checks against a product: the term is an
abstraction whose body checks against the codomain, and has the property. -/
def PfLam (sg : Sig) (Q : Expr → Prop) (M : Expr) : Prop :=
  ∀ (ΓLF : Ctx) (T P : Expr), judge sg M ΓLF (.check (Expr.pi T P)) = true →
    ∃ body, M = Expr.lam body ∧ judge sg body (T :: ΓLF) (.check P) = true ∧ Q body

/-- The soundness of the decoding of proofs at a term, and at the bodies of one, of two and of
three abstractions it is: the premises of the rules bind at most three variables. -/
def PfSound (sg : Sig) (G : Globals) (k : PrimIdx) (E : Array Entry) (n : ℕ) (M : Expr) :
    Prop :=
  PfSoundAt sg G k E n M ∧
    PfLam sg (fun b ↦ PfSoundAt sg G k E n b ∧
      PfLam sg (fun b' ↦ PfSoundAt sg G k E n b' ∧ PfLam sg (PfSoundAt sg G k E n) b') b) M

/-- A property of the bodies of a term follows from a stronger one. -/
theorem PfLam.mono {Q Q' : Expr → Prop} {M : Expr} (h : PfLam sg Q M) (hQ : ∀ b, Q b → Q' b) :
    PfLam sg Q' M := fun ΓLF T P hj ↦ by
  obtain ⟨b, h₁, h₂, h₃⟩ := h ΓLF T P hj
  exact ⟨b, h₁, h₂, hQ b h₃⟩

/-- Substitution into an expression weakened past the substituted variable gives it. -/
theorem hsubWith_shift (red : Expr → List Expr → Option Expr) (e n : Expr) :
    hsubWith red (e.rename Nat.succ) n 0 = some e :=
  hsubWith_vacuous red e n 0

/-- Substitution into an expression weakened past the substituted variable, under a binder, gives
it. -/
theorem hsubWith_shift₁ (red : Expr → List Expr → Option Expr) (e n : Expr) :
    hsubWith red (e.rename (liftR Nat.succ)) n 1 = some e :=
  hsubWith_vacuous red e n 1

/-- Substitution under a binder into an expression weakened twice gives it weakened once. -/
theorem hsubWith_shift_shift (red : Expr → List Expr → Option Expr) (e n : Expr) :
    hsubWith red ((e.rename Nat.succ).rename Nat.succ) n 1 = some (e.rename Nat.succ) := by
  rw [show (e.rename Nat.succ).rename Nat.succ = (e.rename Nat.succ).rename (liftR Nat.succ) by
    rw [rename_rename, rename_rename]; rfl]
  exact hsubWith_shift₁ red _ n

/-- Substitution under two binders into an expression weakened thrice gives it weakened twice. -/
theorem hsubWith_shift₃ (red : Expr → List Expr → Option Expr) (e n : Expr) :
    hsubWith red (((e.rename Nat.succ).rename Nat.succ).rename Nat.succ) n 2 =
      some ((e.rename Nat.succ).rename Nat.succ) := by
  rw [show ((e.rename Nat.succ).rename Nat.succ).rename Nat.succ =
      ((e.rename Nat.succ).rename Nat.succ).rename (liftR^[2] Nat.succ) by
    rw [rename_rename, rename_rename, rename_rename, rename_rename]; rfl]
  exact hsubWith_vacuous red _ n 2

/-- In an expression judged with a family of terms innermost, the innermost variable occurs
unapplied, the family being of base type. -/
theorem appliedAt_of_judge_tm (hsg : SigExt G k sg) {E A : Expr} {Γ : Ctx} (hΓ : ∀ a ∈ Γ,
  Expr.TypeShape a = true)
    {md : Mode} (hmd : ModeShape md = true)
    (hj : judge sg E (tm A :: Γ) md = true) :
    Expr.AppliedAt (EtaLongSpine (RoseTree.node (SimpleLabel.base 6) [])) E 0 = true := by
  have hΓ' : ∀ a ∈ tm A :: Γ, Expr.TypeShape a = true := fun a ha ↦ by
    rcases List.mem_cons.mp ha with rfl | ha
    · simp only [tm, Expr.const, Expr.app, typeShape_node]; rfl
    · exact hΓ a ha
  have h := (judge_appliedAt hsg.ok E (tm A :: Γ) md hΓ' hmd hj).1 0 ((tm A).rename (· + 1)) rfl
  rwa [erase_rename] at h

/-- Substituting the innermost variable of a family of terms for the variable it renames, in an
expression judged with it, gives the expression: its occurrences are unapplied, the family being
of base type. -/
theorem hsub_var0_self (hsg : SigExt G k sg) {E A : Expr} {Γ : Ctx} (hΓ : ∀ a ∈ Γ,
  Expr.TypeShape a = true)
    {md : Mode} (hmd : ModeShape md = true)
    (hj : judge sg E (tm A :: Γ) md = true) :
    hsubWith (reduceStep (SimpleLabel.base 6) []) (E.rename (liftR Nat.succ))
      (RoseTree.node (.app (.var 0)) []) 0 = some E := by
  have h := hsub_eta_identity (appliedAt_of_judge_tm hsg hΓ hmd hj)
  rw [hsub_eq, show reduce (RoseTree.node (SimpleLabel.base 6) []) =
    reduceStep (SimpleLabel.base 6) [] from reduce_node _ _] at h
  exact h

/-- Substituting the innermost variable for itself in an expression weakened under it, where the
expression is judged with a family of terms innermost, gives the weakened expression. -/
theorem hsub_var0_self_weak (hsg : SigExt G k sg) {E A : Expr} {Γ : Ctx} (hΓ : ∀ a ∈ Γ,
  Expr.TypeShape a = true)
    {P : Expr} (hP : P.TypeShape = true)
    (hj : judge sg E (tm A :: Γ) (.check P) = true) :
    hsubWith (reduceStep (SimpleLabel.base 6) [])
      ((E.rename (liftR Nat.succ)).rename (liftR Nat.succ)) (RoseTree.node (.app (.var 0)) []) 0 =
        some (E.rename (liftR Nat.succ)) := by
  have hj' := judge_rename (Sig.ok_closed hsg.ok) E (.check P)
    (CtxRen.lift (CtxRen.succ Γ (tm A)) (tm A)) hj
  rw [tm_rename] at hj'
  refine hsub_var0_self (Γ := tm A :: Γ) hsg (fun a ha ↦ ?_) ?_ hj'
  · rcases List.mem_cons.mp ha with rfl | ha
    · simp only [tm, Expr.const, Expr.app, typeShape_node]; rfl
    · exact hΓ a ha
  · simp only [Mode.rename, ModeShape, typeShape_rename, hP]

/-- Substitution at a base type into an expression whose occurrences of the substituted variable
are unapplied has a value: no reduction is needed. -/
theorem hsubWith_base_total (c : ℕ) :
    ∀ (e n : Expr) (j : ℕ),
      Expr.AppliedAt (EtaLongSpine (RoseTree.node (SimpleLabel.base c) [])) e j = true →
      ∃ e', hsubWith (reduceStep (SimpleLabel.base c) []) e n j = some e' :=
  RoseTree.ind fun l cs ih n j h ↦ by
    obtain ⟨hv, hcs⟩ := appliedAt_node_iff.mp h
    have hch : ∀ (m : Expr) (b : ℕ → ℕ), (∀ idx, b idx = l.binders idx) →
        ∃ ys, (cs.zipIdx.map fun p ↦ hsubWith (reduceStep (SimpleLabel.base c) []) p.1
          (Expr.shift^[b p.2] m) (j + b p.2)).mapM id = some ys := fun m b hb ↦
      exists_mapM_id _ fun k hk ↦ by
        simp only [List.length_map, List.length_zipIdx] at hk
        simp only [List.getElem_map, List.getElem_zipIdx, zero_add, hb]
        exact ih _ (List.getElem_mem hk) _ _ (hcs k hk)
    rcases l with _ | _ | _ | (i | c')
    rotate_left 3
    · obtain ⟨ys, hys⟩ := hch n (fun _ ↦ 0) fun _ ↦ rfl
      rw [hsubWith_var]
      have hys' : (cs.map fun x ↦ hsubWith (reduceStep (SimpleLabel.base c) []) x n j).mapM id =
          some ys := by
        rw [← hys]
        congr 1
        exact List.ext_getElem (by simp) fun k _ _ ↦ by simp
      rw [hys', Option.bind_some]
      by_cases hij : i = j
      · subst hij
        have hnil : cs = [] := by
          have := hv i rfl rfl
          simpa [EtaLongSpine, etaLong_node, etaLongStep] using this
        subst hnil
        obtain rfl : ys = [] := by simpa using hys'
        simp [reduceStep]
      · simp [hij]
    all_goals
      obtain ⟨ys, hys⟩ := hch n (fun idx ↦ Label.binders _ idx) fun _ ↦ rfl
      rw [hsubWith_node_of_ne _ _ (fun _ h ↦ by cases h)]
      exact ⟨_, by rw [hys]; rfl⟩

/-- Substituting a variable at a base type into a renaming of an expression whose occurrences of
the innermost variable are unapplied is a renaming of the expression: the one taking the
innermost variable to the substituted one. -/
theorem hsub_var_base {c : ℕ} {E : Expr}
    (hE : Expr.AppliedAt (EtaLongSpine (RoseTree.node (SimpleLabel.base c) [])) E 0 = true)
    (f ρ : ℕ → ℕ) (hf0 : f 0 = 0) (hf : ∀ i, f (i + 1) = ρ (i + 1) + 1) {k : ℕ} (hk : ρ 0 = k) :
    hsubWith (reduceStep (SimpleLabel.base c) []) (E.rename f) (Expr.var k []) 0 =
      some (E.rename ρ) := by
  have h := hsub_rename _ _ _ 0 ρ _ (hsub_eta_identity hE)
  rw [hsub_eq, show reduce (RoseTree.node (SimpleLabel.base c) []) =
    reduceStep (SimpleLabel.base c) [] from reduce_node _ _, rename_rename] at h
  rw [show f = liftR^[0 + 1] ρ ∘ liftR Nat.succ from funext fun i ↦ by
    rcases i with _ | i
    · exact hf0
    · exact hf i]
  rw [← hk]
  exact h

/-- The application of a two-place LF abstraction, weakened past two variables, to the outer of
them, by hereditary substitution at a base type: the abstraction of its body with the bound
variable it replaces made the next. -/
theorem hsub_lam_var₁ (hsg : SigExt G k sg) {sb A C C' : Expr} {Γ : Ctx} (hΓ : ∀ a ∈ Γ,
  Expr.TypeShape a = true)
    (hj : judge sg sb (tm C :: tm A :: Γ) (.check (tm C')) = true) :
    hsubWith (reduceStep (SimpleLabel.base 6) [])
      ((Expr.lam sb).rename (liftR (Nat.succ ∘ Nat.succ)))
      (RoseTree.node (Label.app (Head.var 1)) []) 0 =
        some (Expr.lam (sb.rename (liftR Nat.succ))) := by
  have hP : ModeShape (.check (Expr.pi (tm C) (tm C'))) = true := by
    simp only [ModeShape, Expr.pi, tm, Expr.const, Expr.app, typeShape_node]; rfl
  rw [show (RoseTree.node (Label.app (Head.var 1)) [] : Expr) = Expr.var 1 [] from rfl,
    hsub_var_base (appliedAt_of_judge_tm hsg hΓ hP (judge_lam hj)) (liftR (Nat.succ ∘ Nat.succ))
      (fun i ↦ match i with | 0 => 1 | i + 1 => i + 2) rfl (fun _ ↦ rfl) rfl, rename_lam,
    show liftR (fun i ↦ match i with | 0 => 1 | i + 1 => i + 2) = liftR Nat.succ from
      funext fun i ↦ by rcases i with _ | _ | i <;> rfl]

/-- Substitution into a renaming of an expression whose image skips the substituted variable
gives the renaming that lowers the variables above it. -/
theorem hsubWith_vacuous' (red : Expr → List Expr → Option Expr) (E n : Expr) {j : ℕ}
    {f g : ℕ → ℕ} (h : ∀ i, f i = (liftR^[j] Nat.succ) (g i)) :
    hsubWith red (E.rename f) n j = some (E.rename g) := by
  rw [show E.rename f = (E.rename g).rename (liftR^[j] Nat.succ) by
    rw [rename_rename]; exact congrArg _ (funext h)]
  exact hsubWith_vacuous red _ n j

/-- Substitution at a base type into a renaming of an expression, at the image of its innermost
variable, is the renaming of the substitution at the innermost variable, where the renaming
skips that image otherwise. -/
theorem hsub_hole {c : ℕ} {E n X : Expr}
    (hX : hsubWith (reduceStep (SimpleLabel.base c) []) E n 0 = some X) {τ σ : ℕ → ℕ} {j : ℕ}
    (hτ : τ 0 = j) (hσ : ∀ i, τ (i + 1) ≠ j ∧ renumber j (τ (i + 1)) = σ i) :
    hsubWith (reduceStep (SimpleLabel.base c) []) (E.rename τ) (n.rename σ) j =
      some (X.rename σ) := by
  have hred : RenameCompat (reduceStep (SimpleLabel.base c) []) := by
    rw [← show reduce (RoseTree.node (SimpleLabel.base c) []) =
      reduceStep (SimpleLabel.base c) [] from reduce_node _ _]
    exact reduce_rename _
  refine hsubWith_holeRen hred E n 0 j σ τ X ⟨hτ, fun i hi ↦ ?_⟩ hX
  obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi
  exact hσ i

/-- The computation of the instantiation of a declaration's type along a spine, in a
hypothesis. -/
local macro "lf_spine_at" h:ident "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (set_option linter.unusedSimpArgs false in
    simp [spine, Expr.arrow, Expr.pi, Expr.shift, Expr.var, Expr.app, rename_node, Label.rename,
      Head.rename, liftR, hsub_eq, hsubWith_node, hsubStep, Label.binders, reduce_node,
      reduceStep, Expr.erase, eraseStep, renumber, -Nat.not_ofNat_lt_one, -Nat.add_eq_right,
      hsubWith_shift, hsubWith_shift₁, hsubWith_shift_shift, hsubWith_shift₃, Expr.lam,
      $hs,*] at $h:ident))

/-- The computation of the instantiation of a declaration's type along a spine, in a hypothesis,
with the renamings and substitutions of the arguments of {lit}`tp`, which may mention object
variables, brought to normal form. -/
local macro "lf_spine_open_at" h:ident "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (set_option linter.unusedSimpArgs false in
    simp [spine, Expr.arrow, Expr.pi, Expr.shift, Expr.var, Expr.app, rename_node, Label.rename,
      Head.rename, liftR, hsub_eq, hsubWith_node, hsubStep, Label.binders, reduce_node,
      reduceStep, Expr.erase, eraseStep, renumber, -Nat.not_ofNat_lt_one, -Nat.add_eq_right,
      hsubWith_shift, hsubWith_shift₁, hsubWith_shift_shift, hsubWith_shift₃, Expr.lam,
      hsubWith_succ₀, hsubWith_succ₁, hsubWith_succ₂, hsubWith_succ₃, hsubWith_succ₄,
      hsubWith_succ₅, $hs,*] at $h:ident))

/-- The variables of a context matching an environment whose types end in {lit}`tp` are of
{lit}`tp` itself, past the environment's and fewer than {lit}`n` past them. -/
theorem TmCtx.heads₀ (hc : TmCtx k n ΓLF env Γ) :
    ∀ i t, varType ΓLF i = some t → t.TypeShape = true ∧
      (t.headDepth.1 = some 0 → t = tp ∧ env.length ≤ i ∧ i < env.length + n) := by
  intro i t ht
  obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp ht
  rw [typeShape_rename, headDepth_rename]
  rcases hc.shape b (List.mem_of_getElem? hb) with ⟨B, rfl⟩ | ⟨F, rfl⟩ | rfl
  · exact ⟨rfl, fun h ↦ absurd (Option.some.inj (h.symm.trans rfl : some 0 = some 6)) (by decide)⟩
  · exact ⟨rfl, fun h ↦ absurd (Option.some.inj (h.symm.trans rfl : some 0 = some 17))
      (by decide)⟩
  · exact ⟨rfl, fun _ ↦ ⟨tp_rename _, (hc.tpVar i).mp hb⟩⟩

/-- The decoding of an LF term renamed to the internal context's variables, at the offset of the
environment's term variables, is its decoding in the environment. -/
theorem dec_tmIdx (e : Expr) : dec k (e.rename (tmIdx env)) (numTm env) = termOf k env e := rfl

/-- The decoding of a type renamed to the internal context's variables, at the offset of the
environment's term variables, is the type its encoding at the offset of the environment's
variables encodes. -/
theorem decTy_tmIdx {a : PartialHorn.Tree} {A : Expr} (h : encTy k env.length a = some A) :
    decTy k (numTm env) (A.rename (tmIdx env)) = some a :=
  decTy_encTy _ a _ (encTy_rename a _ A h _ _ (tmIdx_ge env))

/-- The decoding of an application of a constant in an environment, from its arguments' renamings
and decodings. -/
theorem termOf_const (c : ℕ) (args : List Expr) :
    termOf k env (Expr.const c args) =
      decStep k (.app (.const c)) (args.map fun a ↦ (a.rename (tmIdx env),
        dec k (a.rename (tmIdx env)))) (numTm env) := by
  rw [termOf, Expr.const, Expr.app, rename_app_node, dec_node, List.map_map]
  rfl

/-- The decoding of a proof that applies a constant, from its arguments' decodings. -/
theorem decPf_const (c : ℕ) (args : List Expr) (env : List (Option ℕ)) (m : ℕ) :
    decPf k (Expr.const c args) env m =
      decPfStep k (.app (.const c)) (args.map fun a ↦ (a, decPf k a)) env m :=
  congrFun (congrFun (RoseTree.para_node _ _ _) env) m

/-- The decoding of an LF abstraction in an environment is the abstraction, over the placeholder
type, of its body's decoding in the environment extended by a term variable. -/
theorem termOf_lam (b : Expr) :
    termOf k env (Expr.lam b) =
      (termOf k (none :: env) b).map (Term.lam FreeTopos.one) := by
  rw [termOf, rename_lam, Expr.lam, dec_node]
  rfl

/-- The decoding of an expression into which a term of base type is substituted for the innermost
variable, in an environment, is the instantiation of the decoding of the expression, in the
environment extended by a term variable, at the decoding of the term. -/
theorem termOf_hsub₀ {e n e' : Expr} {s u : MTerm}
    (h : hsubWith (reduceStep (SimpleLabel.base 6) []) e n 0 = some e')
    (hs : termOf k (none :: env) e = some s) (hu : termOf k env n = some u) :
    termOf k env e' = some (Term.subst s (instVar u)) := by
  rw [← show reduce (RoseTree.node (SimpleLabel.base 6) []) = reduceStep (SimpleLabel.base 6) []
    from reduce_node _ _] at h
  have h' := hsubWith_rename (reduce_rename _) e n 0 (tmIdx env) e' h
  rw [← substAt_zero]
  exact dec_hsub _ _ _ 0 (numTm env + 1) _ s u hs hu (Nat.succ_pos _) h'

/-- The decoding of an LF term weakened by a term variable, in the environment extended by it, is
the weakening of its decoding. -/
theorem termOf_shift {z : Expr} {sz : MTerm} (h : termOf k env z = some sz) :
    termOf k (none :: env) (z.rename Nat.succ) = some (weaken1 sz) := by
  have := dec_rename _ (numTm env) (numTm env + 1) Nat.succ sz h fun i _ ↦ by omega
  rw [rename_rename] at this
  rw [termOf, rename_rename]
  exact this

/-- The decoding of an LF term weakened by a term variable under the innermost one, in the
environment extended by it under the innermost, is the weakening of its decoding under the
innermost variable. -/
theorem termOf_shift_lift {e : Expr} {x : MTerm} (h : termOf k (none :: env) e = some x) :
    termOf k (none :: none :: env) (e.rename (liftR Nat.succ)) =
      some (Term.rename x (liftR Nat.succ)) := by
  have := dec_rename _ (numTm env + 1) (numTm env + 2) (liftR Nat.succ) x h fun i hi ↦ by
    rcases i with _ | i
    · omega
    · simp only [liftR]
      omega
  rw [rename_rename] at this
  rw [termOf, rename_rename, show tmIdx (none :: none :: env) ∘ liftR Nat.succ =
    liftR Nat.succ ∘ tmIdx (none :: env) from funext fun i ↦ by rcases i with _ | i <;> rfl]
  exact this

/-- A term weakened under the innermost variable and substituted at the lifted instantiation is
itself. -/
theorem subst_rename_liftR_liftS {t : Term} (ht : Term.VarLeaves t = true) (u : Term) :
    Term.subst (Term.rename t (liftR Nat.succ)) (Term.liftS (instVar u)) = t := by
  rw [Term.subst_rename t _ _ Term.var fun i ↦ by rcases i with _ | i <;> rfl,
    Term.subst_id t ht _ fun _ ↦ rfl]

/-- An expression weakened twice is weakened by two. -/
theorem rename_succ_two (e : Expr) : (e.rename Nat.succ).rename Nat.succ = e.rename (· + 2) := by
  rw [rename_rename]
  rfl

/-- An expression weakened four times is weakened by four. -/
theorem rename_succ_four (e : Expr) :
    (((e.rename Nat.succ).rename Nat.succ).rename Nat.succ).rename Nat.succ = e.rename (· + 4) := by
  rw [rename_rename, rename_rename, rename_rename]
  rfl

/-- The decoding of a renamed LF term, in an environment whose renaming of term variables agrees
with the renaming's: the decoding renamed. -/
theorem termOf_rename {env' : List (Option ℕ)} {e : Expr} {x : MTerm} (f g : ℕ → ℕ)
    (h : termOf k env e = some x) (hfg : ∀ i, tmIdx env' (f i) = g (tmIdx env i))
    (hg : ∀ i, numTm env ≤ i → g i + numTm env = i + numTm env') :
    termOf k env' (e.rename f) = some (Term.rename x g) := by
  have := dec_rename _ _ _ g x h hg
  rw [rename_rename] at this
  rw [termOf, rename_rename, show tmIdx env' ∘ f = g ∘ tmIdx env from funext hfg]
  exact this

/-- The decoding of an expression into which a term of base type is substituted for the variable
of index one, in an environment, is the substitution into the decoding of the expression, in the
environment extended by two term variables, of the decoding of the term, in the environment
extended by one. -/
theorem termOf_hsub₁ {e n e' : Expr} {s u : MTerm}
    (h : hsubWith (reduceStep (SimpleLabel.base 6) []) e n 1 = some e')
    (hs : termOf k (none :: none :: env) e = some s) (hu : termOf k (none :: env) n = some u) :
    termOf k (none :: env) e' = some (Term.subst s (substAt 1 u)) := by
  rw [← show reduce (RoseTree.node (SimpleLabel.base 6) []) = reduceStep (SimpleLabel.base 6) []
    from reduce_node _ _] at h
  exact dec_hsub _ _ _ 1 (numTm env + 2) _ s u hs hu (by omega)
    (hsubWith_rename (reduce_rename _) e n 1 (tmIdx env) e' h)

/-- The decoding of the right side of the computation of the fold at a successor: the step at
the fold of the predecessor, the step instantiated at it after its substitution under the
predecessor's binder. -/
theorem natSucc_rhs {sz ssb sn : Term} (hz : Term.VarLeaves sz = true)
    (hb : Term.VarLeaves ssb = true) :
    Term.subst (Term.subst (Term.rename ssb (liftR Nat.succ)) (instVar (Term.natRec (weaken1 sz)
        (Term.rename ssb (liftR Nat.succ)) (Term.var 0)))) (instVar sn) =
    Term.subst ssb (instVar (Term.natRec sz ssb sn)) := by
  rw [Term.subst_subst _ _ _ _ fun _ ↦ rfl]
  refine Term.subst_rename ssb _ _ _ fun i ↦ ?_
  rcases i with _ | i
  · change Term.subst (Term.natRec (weaken1 sz) (Term.rename ssb (liftR Nat.succ)) (Term.var 0))
      (instVar sn) = _
    rw [show Term.subst (Term.natRec (weaken1 sz) (Term.rename ssb (liftR Nat.succ)) (Term.var 0))
        (instVar sn) = Term.natRec (Term.subst (weaken1 sz) (instVar sn))
          (Term.subst (Term.rename ssb (liftR Nat.succ)) (Term.liftS (instVar sn))) sn from rfl,
      subst_weaken1_instVar hz, subst_rename_liftR_liftS hb]
    rfl
  · rfl

/-- The decoding of the right side of the computation of the fold of a list at a construction:
the step at the element and the fold of the rest, the step's two variables substituted in turn,
under the weakening past the element and the rest, and then the element and the rest. -/
theorem listCons_rhs {sz ss sh st : Term} (hz : Term.VarLeaves sz = true)
    (hs : Term.VarLeaves ss = true) (hh : Term.VarLeaves sh = true) :
    Term.subst (Term.subst (Term.subst
        (Term.rename ss (liftR fun i ↦ match i with | 0 => 1 | i + 1 => i + 2))
        (instVar (Term.listRec (weaken1 (weaken1 sz)) (Term.rename ss (liftR (liftR (· + 2))))
          (Term.var 0))))
        (substAt 1 (weaken1 sh))) (instVar st) =
      Term.subst ss (FreeTopos.Internal.instVar2 (Term.listRec sz ss st) sh) := by
  rw [Term.subst_subst _ _ _ _ fun _ ↦ rfl, Term.subst_subst _ _ _ _ fun _ ↦ rfl]
  refine Term.subst_rename ss _ _ _ fun i ↦ ?_
  rcases i with _ | _ | i
  · set ρ : ℕ → Term := fun i ↦ Term.subst (substAt 1 (weaken1 sh) i) (instVar st) with hρ
    change Term.subst (Term.listRec (weaken1 (weaken1 sz))
      (Term.rename ss (liftR (liftR (· + 2)))) (Term.var 0)) ρ = Term.listRec sz ss st
    have h₁ : Term.subst (weaken1 (weaken1 sz)) ρ = sz := by
      rw [weaken1, weaken1, Term.subst_rename _ _ _ _ fun _ ↦ rfl,
        Term.subst_rename _ _ _ _ fun _ ↦ rfl]
      exact Term.subst_id sz hz _ fun _ ↦ rfl
    have h₂ : Term.subst (Term.rename ss (liftR (liftR (· + 2)))) (Term.liftS (Term.liftS ρ)) =
        ss := by
      rw [Term.subst_rename _ _ _ _ fun _ ↦ rfl]
      refine Term.subst_id ss hs _ fun j ↦ ?_
      rcases j with _ | _ | j
      · rfl
      · rfl
      · rfl
    rw [Term.listRec, Term.subst_node]
    simp only [Term.substStep, List.map_cons, List.map_nil, h₁, h₂]
    rfl
  · change Term.subst (weaken1 sh) (instVar st) = sh
    exact subst_weaken1_instVar hh st
  · rfl

/-- The decoding of the right side of the computation of the fold of a rose tree at a
construction: the step at the pair of the label and the fold of the children's list by the
construction of a list from the fold of each child, the step under the weakening past the label
and the children, and then the label and the children substituted in turn. -/
theorem roseNode_rhs {kn kc : ℕ} {c : PartialHorn.Tree} (ss : Term) {sl : Term}
    (hl : Term.VarLeaves sl = true) (scs : Term) :
    Term.subst (Term.subst (Term.subst (Term.rename ss (liftR (· + 2)))
        (instVar (Term.pair (Term.var 1) (Term.listRec (Term.arr kn [c] Term.star)
          (Term.arr kc [c] (Term.pair (Term.roseRec c (Term.rename ss (liftR (· + 4)))
            (Term.var 1)) (Term.var 0))) (Term.var 0)))))
        (substAt 1 (weaken1 sl))) (instVar scs) =
      Term.subst ss (instVar (Term.pair sl (Term.listRec (Term.arr kn [c] Term.star)
        (Term.arr kc [c] (Term.pair (Term.roseRec c (FreeTopos.Internal.weakenStep2 ss)
          (Term.var 1)) (Term.var 0))) scs))) := by
  rw [Term.subst_subst _ _ _ _ fun _ ↦ rfl, Term.subst_subst _ _ _ _ fun _ ↦ rfl]
  refine Term.subst_rename ss _ _ _ fun i ↦ ?_
  rcases i with _ | i
  · set ρ : ℕ → Term := fun i ↦ Term.subst (substAt 1 (weaken1 sl) i) (instVar scs) with hρ
    have h₁ : ρ 1 = sl := subst_weaken1_instVar hl scs
    have h₂ : Term.subst (Term.rename ss (liftR (· + 4)))
        (Term.liftS (Term.liftS (Term.liftS ρ))) = FreeTopos.Internal.weakenStep2 ss := by
      rw [Term.subst_rename _ _ _ _ fun _ ↦ rfl, FreeTopos.Internal.weakenStep2,
        Term.rename_eq_subst ss _ _ fun _ ↦ rfl]
      exact congrArg _ (funext fun j ↦ by rcases j with _ | j <;> rfl)
    change Term.subst (Term.pair (Term.var 1) (Term.listRec (Term.arr kn [c] Term.star)
      (Term.arr kc [c] (Term.pair (Term.roseRec c (Term.rename ss (liftR (· + 4)))
        (Term.var 1)) (Term.var 0))) (Term.var 0))) ρ = _
    rw [show Term.subst (Term.pair (Term.var 1) (Term.listRec (Term.arr kn [c] Term.star)
        (Term.arr kc [c] (Term.pair (Term.roseRec c (Term.rename ss (liftR (· + 4)))
          (Term.var 1)) (Term.var 0))) (Term.var 0))) ρ =
        Term.pair (ρ 1) (Term.listRec (Term.arr kn [c] Term.star)
          (Term.arr kc [c] (Term.pair (Term.roseRec c (Term.subst (Term.rename ss (liftR (· + 4)))
            (Term.liftS (Term.liftS (Term.liftS ρ)))) (Term.var 1)) (Term.var 0))) (ρ 0)) from rfl,
      h₁, h₂]
    rfl
  · rfl

/-- The innermost term variable decodes to the innermost variable. -/
theorem termOf_var0 : termOf k (none :: env) (Expr.var 0) = some (Term.var 0) := rfl

/-- The decoding of an LF term weakened by a proof variable, in the environment extended by it,
is its decoding. -/
theorem termOf_consPf_shift (F : Expr) (h : ℕ) :
    termOf k (some h :: env) (F.rename Nat.succ) = termOf k env F := by
  rw [termOf, termOf, rename_rename]
  rfl

variable (E : Array Entry) (hk : k.Valid G) (hsg : SigExt G k sg)

include hk hsg in
/-- The soundness of the decoding of reflexivity. -/
theorem sound_refl (hc : PfCtx G k n ΓLF env Γ Φ) {A t F : Expr} {φ : MTerm}
    (hS : spine ΓLF (Expr.pi tp (Expr.pi (tm (v 0)) (pf (eq (v 1) (v 0) (v 0)))))
      [(A, judge sg A), (t, judge sg t)] = some (pf F))
    (hφ : termOf k env F = some φ) :
    ∃ D, decPf k (Expr.const 18 [A, t]) env Φ.length = some D ∧
      (check G E n D).2 Γ Φ φ = true := by
  have hA := spine_tp₁ hS
  obtain ⟨a, ha, -⟩ := tyComplete hsg hc.heads₀ A hA
  simp only [tm, tp, pf, eq, Expr.const, Expr.app] at hS
  lf_spine_open_at hS [Option.bind_eq_some_iff]
  obtain ⟨-, ht, hF⟩ := hS
  simp only [node_inj, List.cons.injEq, and_true, true_and] at hF
  subst hF
  obtain ⟨u, hu, -⟩ := termOf_typed hk hsg hc.toTmCtx ha ht
  rw [show RoseTree.node (.app (.const 16)) [A, t, t] = Expr.const 16 [A, t, t] from rfl,
    termOf_const] at hφ
  simp only [List.map_cons, List.map_nil, decStep, dec_tmIdx, hu, Option.bind_eq_bind,
    Option.bind_some,
    Option.pure_def, Option.some.injEq] at hφ
  subst hφ
  exact ⟨joinD reflD reflD, by rw [decPf_const]; rfl, check_join (check_refl _) (check_refl _)⟩

include hk hsg in
/-- The soundness of the decoding of the computation of a pair's first component. -/
theorem sound_fstPair (hc : PfCtx G k n ΓLF env Γ Φ) {A B a b F : Expr} {φ : MTerm}
    (hS : spine ΓLF (Expr.pi tp (Expr.pi tp (Expr.pi (tm (v 1)) (Expr.pi (tm (v 1))
      (pf (eq (v 3) (fst (v 3) (v 2) (pair (v 3) (v 2) (v 1) (v 0))) (v 1)))))))
      [(A, judge sg A), (B, judge sg B), (a, judge sg a), (b, judge sg b)] = some (pf F))
    (hφ : termOf k env F = some φ) :
    ∃ D, decPf k (Expr.const 21 [A, B, a, b]) env Φ.length = some D ∧
      (check G E n D).2 Γ Φ φ = true := by
  have hT := spine_tp₂ hS
  obtain ⟨xa, hxa, -⟩ := tyComplete hsg hc.heads₀ A hT.1
  obtain ⟨xb, hxb, -⟩ := tyComplete hsg hc.heads₀ B hT.2
  simp only [tm, tp, pf, eq, fst, pair, Expr.const, Expr.app] at hS
  lf_spine_open_at hS [Option.bind_eq_some_iff]
  obtain ⟨-, -, ha, hb, hF⟩ := hS
  simp only [node_inj, List.cons.injEq, and_true, true_and] at hF
  subst hF
  obtain ⟨sa, hsa, -⟩ := termOf_typed hk hsg hc.toTmCtx hxa ha
  obtain ⟨sb, hsb, -⟩ := termOf_typed hk hsg hc.toTmCtx hxb hb
  rw [show RoseTree.node (.app (.const 16)) [A, RoseTree.node (.app (.const 9))
      [A, B, RoseTree.node (.app (.const 8)) [A, B, a, b]], a] =
      Expr.const 16 [A, Expr.const 9 [A, B, Expr.const 8 [A, B, a, b]], a] from rfl] at hφ
  simp only [termOf_const, List.map_cons, List.map_nil, decStep, dec_tmIdx, hsa, hsb,
    Option.bind_eq_bind,
    Option.bind_some, Option.pure_def, Option.map_eq_map, Option.map_some,
    Option.some.injEq] at hφ
  subst hφ
  exact ⟨joinD (ruleD .fstPair) reflD, by rw [decPf_const]; rfl,
    check_join (check_fstPair _ _) (check_refl _)⟩


include hk hsg in
/-- The soundness of the decoding of the computation of a pair's second component. -/
theorem sound_sndPair (hc : PfCtx G k n ΓLF env Γ Φ) {A B a b F : Expr} {φ : MTerm}
    (hS : spine ΓLF (Expr.pi tp (Expr.pi tp (Expr.pi (tm (v 1)) (Expr.pi (tm (v 1))
      (pf (eq (v 2) (snd (v 3) (v 2) (pair (v 3) (v 2) (v 1) (v 0))) (v 0)))))))
      [(A, judge sg A), (B, judge sg B), (a, judge sg a), (b, judge sg b)] = some (pf F))
    (hφ : termOf k env F = some φ) :
    ∃ D, decPf k (Expr.const 22 [A, B, a, b]) env Φ.length = some D ∧
      (check G E n D).2 Γ Φ φ = true := by
  have hT := spine_tp₂ hS
  obtain ⟨xa, hxa, -⟩ := tyComplete hsg hc.heads₀ A hT.1
  obtain ⟨xb, hxb, -⟩ := tyComplete hsg hc.heads₀ B hT.2
  simp only [tm, tp, pf, eq, snd, pair, Expr.const, Expr.app] at hS
  lf_spine_open_at hS [Option.bind_eq_some_iff]
  obtain ⟨-, -, ha, hb, hF⟩ := hS
  simp only [node_inj, List.cons.injEq, and_true, true_and] at hF
  subst hF
  obtain ⟨sa, hsa, -⟩ := termOf_typed hk hsg hc.toTmCtx hxa ha
  obtain ⟨sb, hsb, -⟩ := termOf_typed hk hsg hc.toTmCtx hxb hb
  rw [show RoseTree.node (.app (.const 16)) [B, RoseTree.node (.app (.const 10))
      [A, B, RoseTree.node (.app (.const 8)) [A, B, a, b]], b] =
      Expr.const 16 [B, Expr.const 10 [A, B, Expr.const 8 [A, B, a, b]], b] from rfl] at hφ
  simp only [termOf_const, List.map_cons, List.map_nil, decStep, dec_tmIdx, hsa, hsb,
    Option.bind_eq_bind,
    Option.bind_some, Option.pure_def, Option.map_eq_map, Option.map_some,
    Option.some.injEq] at hφ
  subst hφ
  exact ⟨joinD (ruleD .sndPair) reflD, by rw [decPf_const]; rfl,
    check_join (check_sndPair _ _) (check_refl _)⟩

include hk hsg in
/-- The soundness of the decoding of the η rule of pairs. -/
theorem sound_pairEta (hc : PfCtx G k n ΓLF env Γ Φ) {A B p F : Expr} {φ : MTerm}
    (hS : spine ΓLF (Expr.pi tp (Expr.pi tp (Expr.pi (tm (prod (v 1) (v 0)))
      (pf (eq (prod (v 2) (v 1))
        (pair (v 2) (v 1) (fst (v 2) (v 1) (v 0)) (snd (v 2) (v 1) (v 0))) (v 0))))))
      [(A, judge sg A), (B, judge sg B), (p, judge sg p)] = some (pf F))
    (hφ : termOf k env F = some φ) :
    ∃ D, decPf k (Expr.const 23 [A, B, p]) env Φ.length = some D ∧
      (check G E n D).2 Γ Φ φ = true := by
  have hT := spine_tp₂ hS
  obtain ⟨xa, hxa, -⟩ := tyComplete hsg hc.heads₀ A hT.1
  obtain ⟨xb, hxb, -⟩ := tyComplete hsg hc.heads₀ B hT.2
  simp only [tm, tp, pf, eq, prod, fst, snd, pair, Expr.const, Expr.app] at hS
  lf_spine_open_at hS [Option.bind_eq_some_iff]
  obtain ⟨-, -, hp, hF⟩ := hS
  simp only [node_inj, List.cons.injEq, and_true, true_and] at hF
  subst hF
  have hxab : encTy k env.length (FreeTopos.prod xa xb) = some (prod A B) := by
    rw [encTy_prod, hxa, hxb]; rfl
  obtain ⟨sp, hsp, -⟩ := termOf_typed hk hsg hc.toTmCtx hxab hp
  rw [show RoseTree.node (.app (.const 16)) [RoseTree.node (.app (.const 2)) [A, B],
      RoseTree.node (.app (.const 8)) [A, B, RoseTree.node (.app (.const 9)) [A, B, p],
        RoseTree.node (.app (.const 10)) [A, B, p]], p] =
      Expr.const 16 [prod A B, Expr.const 8 [A, B, Expr.const 9 [A, B, p],
        Expr.const 10 [A, B, p]], p] from rfl] at hφ
  simp only [termOf_const, List.map_cons, List.map_nil, decStep, dec_tmIdx, hsp,
    Option.bind_eq_bind,
    Option.bind_some, Option.pure_def, Option.map_eq_map, Option.map_some,
    Option.some.injEq] at hφ
  subst hφ
  exact ⟨joinD (ruleD .pairEta) reflD, by rw [decPf_const]; rfl,
    check_join (check_pairEta _) (check_refl _)⟩

include hk hsg in
/-- The soundness of the decoding of the η rule of the terminal object. -/
theorem sound_unitEta (hc : PfCtx G k n ΓLF env Γ Φ) {t F : Expr} {φ : MTerm}
    (hS : spine ΓLF (Expr.pi (tm one) (pf (eq one (v 0) star))) [(t, judge sg t)] =
      some (pf F))
    (hφ : termOf k env F = some φ) :
    ∃ D, decPf k (Expr.const 24 [t]) env Φ.length = some D ∧
      (check G E n D).2 Γ Φ φ = true := by
  simp only [tm, pf, eq, one, star, Expr.const, Expr.app] at hS
  lf_spine_at hS [Option.bind_eq_some_iff]
  obtain ⟨ht, hF⟩ := hS
  simp only [node_inj, List.cons.injEq, and_true, true_and] at hF
  subst hF
  obtain ⟨st, hst, hty⟩ := termOf_typed (a := FreeTopos.one) hk hsg hc.toTmCtx rfl ht
  rw [show RoseTree.node (.app (.const 16)) [RoseTree.node (.app (.const 1)) [], t,
      RoseTree.node (.app (.const 7)) []] = Expr.const 16 [one, t, Expr.const 7 []] from rfl] at hφ
  simp only [termOf_const, List.map_cons, List.map_nil, decStep, dec_tmIdx, hst,
    Option.bind_eq_bind,
    Option.bind_some, Option.pure_def, Option.some.injEq] at hφ
  subst hφ
  exact ⟨joinD (ruleD .unitEta) reflD, by rw [decPf_const]; rfl,
    check_join (check_unitEta hty) (check_refl _)⟩

include hk hsg in
/-- The soundness of the decoding of β. -/
theorem sound_beta (hc : PfCtx G k n ΓLF env Γ Φ) {A B f a F : Expr} {φ : MTerm}
    (hS : spine ΓLF (Expr.pi tp (Expr.pi tp (Expr.pi (Expr.arrow (tm (v 1)) (tm (v 0)))
      (Expr.pi (tm (v 2))
      (pf (eq (v 2) (app (v 3) (v 2) (lam (v 3) (v 2) (Expr.lam (Expr.var 2 [v 0]))) (v 0))
        (Expr.var 1 [v 0])))))))
      [(A, judge sg A), (B, judge sg B), (f, judge sg f), (a, judge sg a)] = some (pf F))
    (hφ : termOf k env F = some φ) :
    ∃ D, decPf k (Expr.const 20 [A, B, f, a]) env Φ.length = some D ∧
      (check G E n D).2 Γ Φ φ = true := by
  have hT := spine_tp₂ hS
  obtain ⟨xa, hxa, -⟩ := tyComplete hsg hc.heads₀ A hT.1
  obtain ⟨xb, hxb, -⟩ := tyComplete hsg hc.heads₀ B hT.2
  simp only [tm, tp, pf, eq, app, lam, Expr.const, Expr.app] at hS
  lf_spine_open_at hS [Option.bind_eq_some_iff]
  obtain ⟨-, -, a₁, b, ⟨hf, h₁, h₂⟩, ha, a₂, h₃, b₁, h₄, hF⟩ := hS
  obtain ⟨fb, rfl, hfb⟩ := judge_check_pi_inv hf
  have hfbs : Expr.TypeShape (tm (B.rename Nat.succ)) = true := by
    simp only [tm, Expr.const, Expr.app, typeShape_node]; rfl
  simp only [Expr.lam, rename_node, RoseTree.label_node, RoseTree.children_node, List.zipIdx,
    List.map_cons, List.map_nil, Label.binders, Function.iterate_one, Label.rename] at h₁ h₂
  have hΓs := fun a ha ↦ (hc.typeShape a ha).1
  rw [hsub_var0_self hsg hΓs (md := .check (tm (B.rename Nat.succ))) hfbs hfb,
    Option.some.injEq] at h₂
  rw [hsub_var0_self_weak hsg hΓs hfbs hfb, Option.some.injEq] at h₁
  subst h₁ h₂
  rw [hsubWith_shift₁, Option.some.injEq] at h₃
  subst h₃
  simp only [node_inj, List.cons.injEq, and_true, true_and] at hF
  subst hF
  obtain ⟨sa, hsa, -⟩ := termOf_typed hk hsg hc.toTmCtx hxa ha
  obtain ⟨sf, hsf, -⟩ := termOf_typed hk hsg (hc.toTmCtx.consTm hxa) (encTy_add hxb) hfb
  have hb₁ := termOf_hsub₀ h₄ hsf hsa
  rw [show RoseTree.node (.app (.const 16)) [B, RoseTree.node (.app (.const 12))
      [A, B, RoseTree.node (.app (.const 11)) [A, B, RoseTree.node .lam [fb]], a], b₁] =
      Expr.const 16 [B, Expr.const 12 [A, B, Expr.const 11 [A, B, Expr.lam fb], a], b₁]
      from rfl] at hφ
  simp only [termOf_const, termOf_lam, List.map_cons, List.map_nil, decStep, dec_tmIdx, hsa, hsf,
    hb₁,
    decTy_tmIdx hxa, Option.map_some, relam_lam, Option.bind_eq_bind,
    Option.bind_some, Option.pure_def, Option.some.injEq] at hφ
  subst hφ
  exact ⟨joinD (ruleD .beta) reflD, by rw [decPf_const]; rfl,
    check_join (check_beta _ _ _) (check_refl _)⟩

include hk hsg in
/-- The soundness of the decoding of the computation of the fold at zero. -/
theorem sound_natZero (hc : PfCtx G k n ΓLF env Γ Φ) {C z s F : Expr} {φ : MTerm}
    (hS : spine ΓLF (Expr.pi tp (Expr.pi (tm (v 0)) (Expr.pi (Expr.arrow (tm (v 1)) (tm (v 1)))
      (pf (eq (v 2) (natRec (v 2) (v 1) (Expr.lam (Expr.var 1 [v 0])) zero) (v 1))))))
      [(C, judge sg C), (z, judge sg z), (s, judge sg s)] = some (pf F))
    (hφ : termOf k env F = some φ) :
    ∃ D, decPf k (Expr.const 25 [C, z, s]) env Φ.length = some D ∧
      (check G E n D).2 Γ Φ φ = true := by
  obtain ⟨xc, hxc, -⟩ := tyComplete hsg hc.heads₀ C (spine_tp₁ hS)
  simp only [tm, tp, pf, eq, natRec, zero, zeroAt, star, Expr.const, Expr.app] at hS
  lf_spine_open_at hS [Option.bind_eq_some_iff]
  obtain ⟨-, hz', hs', x, hx, hF⟩ := hS
  obtain ⟨sb, rfl, hsb⟩ := judge_check_pi_inv hs'
  have hCs : Expr.TypeShape (tm (C.rename Nat.succ)) = true := by
    simp only [tm, Expr.const, Expr.app, typeShape_node]; rfl
  simp only [Expr.lam, rename_node, RoseTree.label_node, RoseTree.children_node, List.zipIdx,
    List.map_cons, List.map_nil, Label.binders, Function.iterate_one, Label.rename] at hx
  rw [hsub_var0_self hsg (fun a ha ↦ (hc.typeShape a ha).1) (md := .check (tm (C.rename Nat.succ)))
      hCs hsb,
    Option.some.injEq] at hx
  subst hx
  simp only [node_inj, List.cons.injEq, and_true, true_and] at hF
  subst hF
  obtain ⟨sz, hsz, -⟩ := termOf_typed hk hsg hc.toTmCtx hxc hz'
  obtain ⟨ss, hss, -⟩ := termOf_typed hk hsg (hc.toTmCtx.consTm hxc) (encTy_add hxc) hsb
  rw [show RoseTree.node (.app (.const 16)) [C, RoseTree.node (.app (.const 15))
      [C, z, RoseTree.node .lam [sb], RoseTree.node (.app (.const 13))
        [RoseTree.node (.app (.const 7)) []]], z] =
      Expr.const 16 [C, Expr.const 15 [C, z, Expr.lam sb, Expr.const 13 [Expr.const 7 []]], z]
      from rfl] at hφ
  simp only [termOf_const, termOf_lam, List.map_cons, List.map_nil, decStep, dec_tmIdx, hsz, hss,
    Option.map_some, lamBody_lam, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
    Option.map_eq_map, Option.some.injEq] at hφ
  subst hφ
  exact ⟨joinD (ruleD (.natZero k.zero)) reflD, by rw [decPf_const]; rfl,
    check_join (check_natZero hk.zero _ _) (check_refl _)⟩

include hk hsg in
/-- The soundness of the decoding of the computation of the case analysis at a left
injection. -/
theorem sound_caseInl (hc : PfCtx G k n ΓLF env Γ Φ) {A B C g h u F : Expr} {φ : MTerm}
    (hS : spine ΓLF (Expr.pi tp (Expr.pi tp (Expr.pi tp (Expr.pi (tm (exp (v 2) (v 0)))
      (Expr.pi (tm (exp (v 2) (v 1))) (Expr.pi (tm (v 4))
        (pf (eq (v 3) (app (coprod (v 5) (v 4)) (v 3)
            (case (v 5) (v 4) (v 3) (pair (exp (v 5) (v 3)) (exp (v 4) (v 3)) (v 2) (v 1)))
            (inl (v 5) (v 4) (v 0)))
          (app (v 5) (v 3) (v 2) (v 0))))))))))
      [(A, judge sg A), (B, judge sg B), (C, judge sg C), (g, judge sg g), (h, judge sg h),
        (u, judge sg u)] = some (pf F))
    (hφ : termOf k env F = some φ) :
    ∃ D, decPf k (Expr.const 53 [A, B, C, g, h, u]) env Φ.length = some D ∧
      (check G E n D).2 Γ Φ φ = true := by
  have hT := spine_tp₃ hS
  obtain ⟨xa, hxa, -⟩ := tyComplete hsg hc.heads₀ A hT.1
  obtain ⟨xb, hxb, -⟩ := tyComplete hsg hc.heads₀ B hT.2.1
  obtain ⟨xc, hxc, -⟩ := tyComplete hsg hc.heads₀ C hT.2.2
  simp only [tm, tp, pf, eq, app, coprod, case, pair, exp, inl, Expr.const, Expr.app] at hS
  lf_spine_open_at hS [Option.bind_eq_some_iff]
  obtain ⟨-, -, -, hg, hh, hu, hF⟩ := hS
  simp only [node_inj, List.cons.injEq, and_true, true_and] at hF
  subst hF
  have hac : encTy k env.length (FreeTopos.exp xa xc) = some (exp A C) := by
    rw [encTy_exp, hxa, hxc]; rfl
  have hbc : encTy k env.length (FreeTopos.exp xb xc) = some (exp B C) := by
    rw [encTy_exp, hxb, hxc]; rfl
  obtain ⟨sgg, hsgg, -⟩ := termOf_typed hk hsg hc.toTmCtx hac hg
  obtain ⟨sh, hsh, -⟩ := termOf_typed hk hsg hc.toTmCtx hbc hh
  obtain ⟨su, hsu, -⟩ := termOf_typed hk hsg hc.toTmCtx hxa hu
  change termOf k env (Expr.const 16 [C, Expr.const 12 [Expr.const 48 [A, B], C,
    Expr.const 52 [A, B, C, Expr.const 8 [Expr.const 3 [A, C], Expr.const 3 [B, C], g, h]],
    Expr.const 50 [A, B, u]], Expr.const 12 [A, C, g, u]]) = some φ at hφ
  simp only [termOf_const, List.map_cons, List.map_nil, decStep, dec_tmIdx, hsgg, hsh, hsu,
    decTy_tmIdx hxa,
    decTy_tmIdx hxb, decTy_tmIdx hxc, Option.bind_eq_bind, Option.bind_some,
    Option.pure_def, Option.some.injEq] at hφ
  subst hφ
  exact ⟨joinD (ruleD (.caseInl k.case k.inl)) reflD, by rw [decPf_const]; rfl,
    check_join (check_caseInl hk.case hk.inl _ _ _ _ _) (check_refl _)⟩

include hk hsg in
/-- The soundness of the decoding of the computation of the case analysis at a right
injection. -/
theorem sound_caseInr (hc : PfCtx G k n ΓLF env Γ Φ) {A B C g h u F : Expr} {φ : MTerm}
    (hS : spine ΓLF (Expr.pi tp (Expr.pi tp (Expr.pi tp (Expr.pi (tm (exp (v 2) (v 0)))
      (Expr.pi (tm (exp (v 2) (v 1))) (Expr.pi (tm (v 3))
        (pf (eq (v 3) (app (coprod (v 5) (v 4)) (v 3)
            (case (v 5) (v 4) (v 3) (pair (exp (v 5) (v 3)) (exp (v 4) (v 3)) (v 2) (v 1)))
            (inr (v 5) (v 4) (v 0)))
          (app (v 4) (v 3) (v 1) (v 0))))))))))
      [(A, judge sg A), (B, judge sg B), (C, judge sg C), (g, judge sg g), (h, judge sg h),
        (u, judge sg u)] = some (pf F))
    (hφ : termOf k env F = some φ) :
    ∃ D, decPf k (Expr.const 54 [A, B, C, g, h, u]) env Φ.length = some D ∧
      (check G E n D).2 Γ Φ φ = true := by
  have hT := spine_tp₃ hS
  obtain ⟨xa, hxa, -⟩ := tyComplete hsg hc.heads₀ A hT.1
  obtain ⟨xb, hxb, -⟩ := tyComplete hsg hc.heads₀ B hT.2.1
  obtain ⟨xc, hxc, -⟩ := tyComplete hsg hc.heads₀ C hT.2.2
  simp only [tm, tp, pf, eq, app, coprod, case, pair, exp, inr, Expr.const, Expr.app] at hS
  lf_spine_open_at hS [Option.bind_eq_some_iff]
  obtain ⟨-, -, -, hg, hh, hu, hF⟩ := hS
  simp only [node_inj, List.cons.injEq, and_true, true_and] at hF
  subst hF
  have hac : encTy k env.length (FreeTopos.exp xa xc) = some (exp A C) := by
    rw [encTy_exp, hxa, hxc]; rfl
  have hbc : encTy k env.length (FreeTopos.exp xb xc) = some (exp B C) := by
    rw [encTy_exp, hxb, hxc]; rfl
  obtain ⟨sgg, hsgg, -⟩ := termOf_typed hk hsg hc.toTmCtx hac hg
  obtain ⟨sh, hsh, -⟩ := termOf_typed hk hsg hc.toTmCtx hbc hh
  obtain ⟨su, hsu, -⟩ := termOf_typed hk hsg hc.toTmCtx hxb hu
  change termOf k env (Expr.const 16 [C, Expr.const 12 [Expr.const 48 [A, B], C,
    Expr.const 52 [A, B, C, Expr.const 8 [Expr.const 3 [A, C], Expr.const 3 [B, C], g, h]],
    Expr.const 51 [A, B, u]], Expr.const 12 [B, C, h, u]]) = some φ at hφ
  simp only [termOf_const, List.map_cons, List.map_nil, decStep, dec_tmIdx, hsgg, hsh, hsu,
    decTy_tmIdx hxa,
    decTy_tmIdx hxb, decTy_tmIdx hxc, Option.bind_eq_bind, Option.bind_some,
    Option.pure_def, Option.some.injEq] at hφ
  subst hφ
  exact ⟨joinD (ruleD (.caseInr k.case k.inr)) reflD, by rw [decPf_const]; rfl,
    check_join (check_caseInr hk.case hk.inr _ _ _ _ _) (check_refl _)⟩

include hk hsg in
/-- The soundness of the decoding of case analysis on a coproduct. -/
theorem sound_coprodInd (hc : PfCtx G k n ΓLF env Γ Φ) {A B P d₁ d₂ c F : Expr} {φ : MTerm}
    (ih₁ : PfLam sg (PfSoundAt sg G k E n) d₁) (ih₂ : PfLam sg (PfSoundAt sg G k E n) d₂)
    (hS : spine ΓLF (Expr.pi tp (Expr.pi tp (Expr.pi (Expr.arrow (tm (coprod (v 1) (v 0)))
        (tm omega))
      (Expr.arrow (Expr.pi (tm (v 2)) (pf (Expr.var 1 [inl (v 3) (v 2) (v 0)])))
        (Expr.arrow (Expr.pi (tm (v 1)) (pf (Expr.var 1 [inr (v 3) (v 2) (v 0)])))
          (Expr.pi (tm (coprod (v 2) (v 1))) (pf (Expr.var 1 [v 0]))))))))
      [(A, judge sg A), (B, judge sg B), (P, judge sg P), (d₁, judge sg d₁),
        (d₂, judge sg d₂), (c, judge sg c)] = some (pf F))
    (hφ : termOf k env F = some φ) :
    ∃ D, decPf k (Expr.const 55 [A, B, P, d₁, d₂, c]) env Φ.length = some D ∧
      (check G E n D).2 Γ Φ φ = true := by
  have hT := spine_tp₂ hS
  obtain ⟨xa, hxa, hIa⟩ := tyComplete hsg hc.heads₀ A hT.1
  obtain ⟨xb, hxb, hIb⟩ := tyComplete hsg hc.heads₀ B hT.2
  simp only [tm, tp, pf, omega, coprod, inl, inr, Expr.const, Expr.app] at hS
  lf_spine_open_at hS [Option.bind_eq_some_iff]
  obtain ⟨-, -, a, a₁, b, ⟨hP, ha, ha₁, hb⟩, a₂, a₃, ⟨hd₁, ha₂, ha₃⟩, a₄, ⟨hd₂, ha₄⟩, hcc, a₅,
    ha₅, hF⟩ := hS
  obtain ⟨Pb, rfl, hPb⟩ := judge_check_pi_inv hP
  simp only [Expr.lam, rename_node, RoseTree.label_node, RoseTree.children_node, List.zipIdx,
    List.map_cons, List.map_nil, Label.binders, Function.iterate_one, Label.rename] at ha ha₁ hb
  have hcab : encTy k env.length (FreeTopos.coprod xa xb) = some (coprod A B) := by
    rw [encTy_coprod, hxa, hxb]; rfl
  have hΓs := fun a ha ↦ (hc.typeShape a ha).1
  have hOs : ModeShape (.check (tm omega)) = true := by
    simp only [ModeShape, tm, Expr.const, Expr.app, typeShape_node]; rfl
  have hApp := appliedAt_of_judge_tm (A := coprod A B) hsg hΓs hOs hPb
  -- the motive at the conclusion's variable, past the two premises
  rw [rename_rename, rename_rename] at hb
  obtain rfl := Option.some.inj (hb.symm.trans (hsub_var_base hApp
    ((liftR Nat.succ ∘ liftR Nat.succ) ∘ liftR Nat.succ)
    (fun i ↦ match i with | 0 => 0 | i + 1 => i + 3) rfl (fun _ ↦ rfl) rfl))
  obtain rfl := Option.some.inj (ha₃.symm.trans (hsubWith_vacuous' _ _ _ (j := 2)
    (g := liftR Nat.succ) fun i ↦ by rcases i with _ | i <;> rfl))
  obtain rfl := Option.some.inj (ha₄.symm.trans
    (hsubWith_vacuous' _ _ _ (j := 1) (g := id) fun _ ↦ rfl))
  rw [rename_id] at ha₅
  simp only [node_inj, List.cons.injEq, and_true, true_and] at hF
  subst hF
  -- the motive at the right injection, under the left premise
  have hPb1 := judge_rename (Sig.ok_closed hsg.ok) Pb _
    (CtxRen.lift (CtxRen.succ ΓLF (tm B)) (tm (coprod A B))) hPb
  rw [Mode.rename, show Expr.rename (RoseTree.node (.app (.const 6))
    [RoseTree.node (.app (.const 4)) []]) (liftR Nat.succ) = tm omega from
      rename_closed (tm_closed rfl) _, tm_rename] at hPb1
  have hΓB : ∀ x ∈ tm B :: ΓLF, Expr.TypeShape x = true := fun x hx ↦ by
    rcases List.mem_cons.mp hx with rfl | hx
    · simp only [tm, Expr.const, Expr.app, typeShape_node]; rfl
    · exact hΓs x hx
  have hApp1 := appliedAt_of_judge_tm hsg hΓB hOs hPb1
  let Nr : Expr := RoseTree.node (.app (.const 51))
    [A.rename Nat.succ, B.rename Nat.succ, RoseTree.node (.app (.var 0)) []]
  obtain ⟨X₁, hX₁⟩ := hsubWith_base_total 6 _ Nr 0 hApp1
  have hred : RenameCompat (reduceStep (SimpleLabel.base 6) []) := by
    rw [← show reduce (RoseTree.node (SimpleLabel.base 6) []) =
      reduceStep (SimpleLabel.base 6) [] from reduce_node _ _]
    exact reduce_rename _
  have hX₁' := hsubWith_rename hred _ _ 0 (liftR Nat.succ) X₁ hX₁
  rw [rename_rename, show liftR^[0 + 1] (liftR Nat.succ) ∘ liftR Nat.succ =
      liftR Nat.succ ∘ liftR Nat.succ from funext fun i ↦ by rcases i with _ | i <;> rfl,
    show Nr.rename (liftR^[0] (liftR Nat.succ)) = RoseTree.node (.app (.const 51))
        [(A.rename Nat.succ).rename Nat.succ, (B.rename Nat.succ).rename Nat.succ,
          RoseTree.node (.app (.var 0)) []] by
      simp only [Nr, Function.iterate_zero, id, rename_app_node, List.map_cons, List.map_nil,
        rename_rename]
      rfl] at hX₁'
  rw [← rename_rename] at hX₁'
  obtain rfl := Option.some.inj (ha₁.symm.trans hX₁')
  rw [Function.iterate_zero_apply, show liftR Nat.succ = liftR^[1] Nat.succ from rfl,
    hsubWith_vacuous, Option.some.injEq] at ha₂
  subst ha₂
  -- the decodings
  obtain ⟨sp, hsp, hpt⟩ := termOf_typed (a := FreeTopos.omega) hk hsg (hc.toTmCtx.consTm hcab) rfl
    hPb
  obtain ⟨sc, hsc, hct⟩ := termOf_typed hk hsg hc.toTmCtx hcab hcc
  obtain rfl := Option.some.inj (hφ.symm.trans (termOf_hsub₀ ha₅ hsp hsc))
  have hS₁ : termOf k (none :: none :: env) (Pb.rename (liftR Nat.succ)) =
      some (Term.rename sp (liftR Nat.succ)) :=
    termOf_rename _ _ hsp (fun i ↦ by rcases i with _ | i <;> rfl) fun i hi ↦ by
      rcases i with _ | i
      · exact absurd hi (by simp [numTm])
      · simp only [liftR, numTm]
        omega
  have hinj : ∀ (kk : ℕ) (cc : ℕ), (cc = 50 ∧ kk = k.inl) ∨ (cc = 51 ∧ kk = k.inr) →
      termOf k (none :: env) (RoseTree.node (.app (.const cc)) [A.rename Nat.succ,
        B.rename Nat.succ, RoseTree.node (.app (.var 0)) []]) =
        some (Term.arr kk [xa, xb] (Term.var 0)) := by
    rintro kk cc (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
    · rw [show RoseTree.node (.app (.const _)) [A.rename Nat.succ, B.rename Nat.succ,
          RoseTree.node (.app (.var 0)) []] =
        Expr.const _ [A.rename Nat.succ, B.rename Nat.succ, Expr.var 0 []] from rfl, termOf_const]
      simp only [List.map_cons, List.map_nil, decStep, dec_tmIdx,
        decTy_tmIdx (env := none :: env) (encTy_succ hxa),
        decTy_tmIdx (env := none :: env) (encTy_succ hxb), Option.bind_eq_bind, Option.bind_some,
        Option.pure_def]
      rfl
  have hfl : ∀ X kk, termOf k (none :: env) X = some (Term.subst (Term.rename sp (liftR Nat.succ))
      (instVar (Term.arr kk [xa, xb] (Term.var 0)))) → termOf k (none :: env) X =
      some (Term.subst sp (FreeTopos.Internal.atVar0 (Term.arr kk [xa, xb] (Term.var 0)))) :=
    fun X kk h ↦ h.trans (congrArg some
      (Term.subst_rename sp _ _ _ fun i ↦ by rcases i with _ | i <;> rfl))
  have ha' := hfl _ _ (termOf_hsub₀ (env := none :: env) ha hS₁ (hinj k.inl 50 (.inl ⟨rfl, rfl⟩)))
  have ha₂' := hfl _ _ (termOf_hsub₀ (env := none :: env) hX₁ hS₁
    (hinj k.inr 51 (.inr ⟨rfl, rfl⟩)))
  have hlen : (Φ.map weaken1 ++ [truth]).length = Φ.length + 1 := by
    rw [List.length_append, List.length_map, List.length_singleton]
  obtain ⟨body₁, rfl, hb1, hs₁⟩ := ih₁ ΓLF _ _ hd₁
  obtain ⟨body₂, rfl, hb2, hs₂⟩ := ih₂ ΓLF _ _ hd₂
  obtain ⟨D₁, hD₁, hcD₁⟩ := hs₁ _ _ _ _ _ _ ((hc.consTm hxa).addHyp
    (typeIn_truth (G := G) (Γ := xa :: Γ))) hb1 ha'
  obtain ⟨D₂, hD₂, hcD₂⟩ := hs₂ _ _ _ _ _ _ ((hc.consTm hxb).addHyp
    (typeIn_truth (G := G) (Γ := xb :: Γ))) hb2 ha₂'
  rw [hlen] at hD₁ hD₂
  refine ⟨indD (FreeTopos.coprod xa xb) (.coprodInd k.inl k.inr) sp sc Φ.length [D₁, D₂], ?_,
    check_coprodIndD hk.inl hk.inr (by rw [FreeTopos.Internal.isTy_coprod, hIa, hIb]; rfl) hpt hct
      hc.typed hcD₁ hcD₂⟩
  rw [decPf_const, show ∀ xs, decPfStep k (Label.app (Head.const 55)) xs env Φ.length =
    decPfStepCoprod k 55 xs env Φ.length from fun _ ↦ rfl]
  simp only [decPfStepCoprod, List.map_cons, List.map_nil, termOf_lam, hsp, hsc, decPf_lam,
    hD₁, hD₂, decTy_encTy _ xa A hxa, decTy_encTy _ xb B hxb, Option.map_some, Option.bind_eq_bind,
    Option.bind_some, lamBody_lam, Option.pure_def]

include hk hsg in
/-- The soundness of the decoding of a formula from a term of the initial object. -/
theorem sound_exfalso (hc : PfCtx G k n ΓLF env Γ Φ) {z ψ F : Expr} {φ : MTerm}
    (hS : spine ΓLF (Expr.pi (tm initial) (Expr.pi (tm omega) (pf (v 0))))
      [(z, judge sg z), (ψ, judge sg ψ)] = some (pf F))
    (hφ : termOf k env F = some φ) :
    ∃ D, decPf k (Expr.const 56 [z, ψ]) env Φ.length = some D ∧
      (check G E n D).2 Γ Φ φ = true := by
  simp only [tm, pf, omega, initial, Expr.const, Expr.app] at hS
  lf_spine_at hS [Option.bind_eq_some_iff]
  obtain ⟨hz, hψ, hF⟩ := hS
  simp only [node_inj, List.cons.injEq, and_true, true_and] at hF
  subst hF
  obtain ⟨sz, hsz, hzt⟩ := termOf_typed (a := FreeTopos.zero) hk hsg hc.toTmCtx rfl hz
  obtain ⟨sψ, hsψ, hψt⟩ := termOf_typed (a := FreeTopos.omega) hk hsg hc.toTmCtx rfl hψ
  obtain rfl := Option.some.inj (hφ.symm.trans hsψ)
  refine ⟨_, ?_, check_exfalsoD hψt hzt⟩
  rw [decPf_const, show ∀ xs, decPfStep k (Label.app (Head.const 56)) xs env Φ.length =
    decPfStepCoprod k 56 xs env Φ.length from fun _ ↦ rfl]
  simp only [decPfStepCoprod, List.map_cons, List.map_nil, hsz, hsψ, Option.bind_eq_bind,
    Option.bind_some, Option.pure_def]

include hk hsg in
/-- The soundness of the decoding of the computation of the fold at a successor. -/
theorem sound_natSucc (hc : PfCtx G k n ΓLF env Γ Φ) {C z s N F : Expr} {φ : MTerm}
    (hS : spine ΓLF (Expr.pi tp (Expr.pi (tm (v 0)) (Expr.pi (Expr.arrow (tm (v 1)) (tm (v 1)))
      (Expr.pi (tm nat)
      (pf (eq (v 3) (natRec (v 3) (v 2) (Expr.lam (Expr.var 2 [v 0])) (succ (v 0)))
        (Expr.var 1 [natRec (v 3) (v 2) (Expr.lam (Expr.var 2 [v 0])) (v 0)])))))))
      [(C, judge sg C), (z, judge sg z), (s, judge sg s), (N, judge sg N)] = some (pf F))
    (hφ : termOf k env F = some φ) :
    ∃ D, decPf k (Expr.const 26 [C, z, s, N]) env Φ.length = some D ∧
      (check G E n D).2 Γ Φ φ = true := by
  obtain ⟨xc, hxc, -⟩ := tyComplete hsg hc.heads₀ C (spine_tp₁ hS)
  simp only [tm, tp, pf, eq, natRec, succ, nat, Expr.const, Expr.app] at hS
  lf_spine_open_at hS [Option.bind_eq_some_iff]
  obtain ⟨-, hz', b₀, a₁, ⟨hs', h₂, b', h₂', h₃⟩, hn, b₁, h₅, a₃, h₆, hF⟩ := hS
  obtain ⟨sb, rfl, hsb⟩ := judge_check_pi_inv hs'
  have hCs : Expr.TypeShape (tm (C.rename Nat.succ)) = true := by
    simp only [tm, Expr.const, Expr.app, typeShape_node]; rfl
  have hΓs := fun a ha ↦ (hc.typeShape a ha).1
  simp only [Expr.lam, rename_node, RoseTree.label_node, RoseTree.children_node, List.zipIdx,
    List.map_cons, List.map_nil, Label.binders, Function.iterate_one, Label.rename] at h₂ h₂' h₃
  rw [hsub_var0_self_weak hsg hΓs hCs hsb, Option.some.injEq] at h₂ h₂'
  subst h₂ h₂'
  rw [hsubWith_shift₁, Option.some.injEq] at h₅
  subst h₅
  simp only [node_inj, List.cons.injEq, and_true, true_and] at hF
  subst hF
  obtain ⟨sz, hsz, hzt⟩ := termOf_typed hk hsg hc.toTmCtx hxc hz'
  obtain ⟨ss, hss, hst⟩ := termOf_typed hk hsg (hc.toTmCtx.consTm hxc) (encTy_add hxc) hsb
  obtain ⟨sn, hsn, hnt⟩ := termOf_typed (a := FreeTopos.nat) hk hsg hc.toTmCtx rfl hn
  have hR : termOf k (none :: env) (Expr.const 15 [C, z.rename Nat.succ,
      Expr.lam (sb.rename (liftR Nat.succ)), Expr.var 0]) =
      some (Term.natRec (weaken1 sz) (Term.rename ss (liftR Nat.succ)) (Term.var 0)) := by
    simp only [termOf_const, termOf_lam, List.map_cons, List.map_nil, decStep, dec_tmIdx,
      termOf_shift hsz, termOf_shift_lift hss, Option.map_some, lamBody_lam,
      Option.bind_eq_bind, Option.bind_some, Option.pure_def]
    rfl
  have ha₁ := termOf_hsub₀ (env := none :: env) h₃ (termOf_shift_lift hss) hR
  have ha₃ := termOf_hsub₀ h₆ ha₁ hsn
  rw [natSucc_rhs (varLeaves_of_typeIn hzt) (varLeaves_of_typeIn hst)] at ha₃
  rw [show RoseTree.node (.app (.const 16)) [C, RoseTree.node (.app (.const 15))
      [C, z, RoseTree.node .lam [sb], RoseTree.node (.app (.const 14)) [N]], a₃] =
      Expr.const 16 [C, Expr.const 15 [C, z, Expr.lam sb, Expr.const 14 [N]], a₃]
      from rfl] at hφ
  simp only [termOf_const, termOf_lam, List.map_cons, List.map_nil, decStep, dec_tmIdx, hsz, hss,
    hsn,
    ha₃, Option.map_some, lamBody_lam, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
    Option.map_eq_map, Option.some.injEq] at hφ
  subst hφ
  exact ⟨joinD (ruleD (.natSucc k.succ)) reflD, by rw [decPf_const]; rfl,
    check_join (check_natSucc hk.succ _ _ _) (check_refl _)⟩

include hk hsg in
/-- The soundness of the decoding of the computation of the fold of a list at the empty list. -/
theorem sound_listNil (hc : PfCtx G k n ΓLF env Γ Φ) {A C z s F : Expr} {φ : MTerm}
    (hS : spine ΓLF (Expr.pi tp (Expr.pi tp (Expr.pi (tm (v 0))
      (Expr.pi (Expr.arrow (tm (v 2)) (Expr.arrow (tm (v 1)) (tm (v 1))))
        (pf (eq (v 2) (listRec (v 3) (v 2) (v 1) (Expr.lam (Expr.lam (Expr.var 2 [v 1, v 0])))
          (nil (v 3))) (v 1)))))))
      [(A, judge sg A), (C, judge sg C), (z, judge sg z), (s, judge sg s)] = some (pf F))
    (hφ : termOf k env F = some φ) :
    ∃ D, decPf k (Expr.const 34 [A, C, z, s]) env Φ.length = some D ∧
      (check G E n D).2 Γ Φ φ = true := by
  have hT := spine_tp₂ hS
  obtain ⟨xa, hxa, -⟩ := tyComplete hsg hc.heads₀ A hT.1
  obtain ⟨xc, hxc, -⟩ := tyComplete hsg hc.heads₀ C hT.2
  simp only [tm, tp, pf, eq, listRec, nil, nilAt, star, Expr.const, Expr.app] at hS
  lf_spine_open_at hS [Option.bind_eq_some_iff]
  obtain ⟨-, -, hz', hs', x, hx, hF⟩ := hS
  obtain ⟨sb₁, rfl, hsb₁⟩ := judge_check_pi_inv hs'
  obtain ⟨sb, rfl, hsb⟩ := judge_check_pi_inv hsb₁
  have hΓs := fun a ha ↦ (hc.typeShape a ha).1
  have hΓA : ∀ a ∈ tm A :: ΓLF, Expr.TypeShape a = true := fun a ha ↦ by
    rcases List.mem_cons.mp ha with rfl | ha
    · simp only [tm, Expr.const, Expr.app, typeShape_node]; rfl
    · exact hΓs a ha
  rw [rename_rename, rename_lam] at hx
  simp only [show ∀ X : Expr, RoseTree.label (Expr.lam X) = Label.lam from fun _ ↦ rfl,
    show ∀ X : Expr, RoseTree.children (Expr.lam X) = [X] from fun _ ↦ rfl] at hx
  rw [hsub_lam_var₁ hsg hΓs hsb, Option.bind_some] at hx
  simp only [show ∀ X : Expr, RoseTree.label (Expr.lam X) = Label.lam from fun _ ↦ rfl,
    show ∀ X : Expr, RoseTree.children (Expr.lam X) = [X] from fun _ ↦ rfl] at hx
  have hCs : ModeShape (.check (tm ((C.rename Nat.succ).rename Nat.succ))) = true := by
    simp only [ModeShape, tm, Expr.const, Expr.app, typeShape_node]; rfl
  rw [hsub_var0_self hsg hΓA hCs hsb, Option.some.injEq] at hx
  subst hx
  simp only [node_inj, List.cons.injEq, and_true, true_and] at hF
  subst hF
  obtain ⟨sz, hsz, -⟩ := termOf_typed hk hsg hc.toTmCtx hxc hz'
  obtain ⟨ss, hss, -⟩ := termOf_typed hk hsg ((hc.toTmCtx.consTm hxa).consTm (encTy_succ hxc))
    (encTy_succ (encTy_succ hxc)) hsb
  change termOf k env (Expr.const 16 [C, Expr.const 33 [A, C, z, Expr.lam (Expr.lam sb),
    Expr.const 31 [A, Expr.const 7 []]], z]) = some φ at hφ
  simp only [termOf_const, termOf_lam, List.map_cons, List.map_nil, decStep, dec_tmIdx, hsz, hss,
    decTy_tmIdx hxa, Option.map_some, lamBody_lam, Option.bind_eq_bind,
    Option.bind_some, Option.pure_def, Option.some.injEq] at hφ
  subst hφ
  exact ⟨joinD (ruleD (.listNil k.nil)) reflD, by rw [decPf_const]; rfl,
    check_join (check_listNil hk.nil _ _ _) (check_refl _)⟩

include hk hsg in
/-- The soundness of the decoding of the computation of the fold of a list at a construction. -/
theorem sound_listCons (hc : PfCtx G k n ΓLF env Γ Φ) {A C z s h t F : Expr} {φ : MTerm}
    (hS : spine ΓLF (Expr.pi tp (Expr.pi tp (Expr.pi (tm (v 0))
      (Expr.pi (Expr.arrow (tm (v 2)) (Expr.arrow (tm (v 1)) (tm (v 1))))
        (Expr.pi (tm (v 3)) (Expr.pi (tm (list (v 4)))
          (pf (eq (v 4)
            (listRec (v 5) (v 4) (v 3) (Expr.lam (Expr.lam (Expr.var 4 [v 1, v 0])))
              (cons (v 5) (pair (v 5) (list (v 5)) (v 1) (v 0))))
            (Expr.var 2 [v 1,
              listRec (v 5) (v 4) (v 3) (Expr.lam (Expr.lam (Expr.var 4 [v 1, v 0])))
                (v 0)])))))))))
      [(A, judge sg A), (C, judge sg C), (z, judge sg z), (s, judge sg s), (h, judge sg h),
        (t, judge sg t)] = some (pf F))
    (hφ : termOf k env F = some φ) :
    ∃ D, decPf k (Expr.const 35 [A, C, z, s, h, t]) env Φ.length = some D ∧
      (check G E n D).2 Γ Φ φ = true := by
  have hT := spine_tp₂ hS
  obtain ⟨xa, hxa, -⟩ := tyComplete hsg hc.heads₀ A hT.1
  obtain ⟨xc, hxc, -⟩ := tyComplete hsg hc.heads₀ C hT.2
  simp only [tm, tp, pf, eq, listRec, cons, pair, list, Expr.const, Expr.app] at hS
  lf_spine_open_at hS [Option.bind_eq_some_iff]
  obtain ⟨-, -, hz', a₀, b, ⟨hs', ha₀, a', ha', hb⟩, a₁, b₁, ⟨hh, ha₁, hb₁⟩, ht, a₂, ha₂, b₂,
    hb₂, hF⟩ := hS
  obtain ⟨sb₁, rfl, hsb₁⟩ := judge_check_pi_inv hs'
  obtain ⟨sb, rfl, hsb⟩ := judge_check_pi_inv hsb₁
  have hΓs := fun a ha ↦ (hc.typeShape a ha).1
  have hΓA : ∀ a ∈ tm A :: ΓLF, Expr.TypeShape a = true := fun a ha ↦ by
    rcases List.mem_cons.mp ha with rfl | ha
    · simp only [tm, Expr.const, Expr.app, typeShape_node]; rfl
    · exact hΓs a ha
  have hCs : ModeShape (.check (tm ((C.rename Nat.succ).rename Nat.succ))) = true := by
    simp only [ModeShape, tm, Expr.const, Expr.app, typeShape_node]; rfl
  have hP : ModeShape (.check (Expr.pi (tm (C.rename Nat.succ))
      (tm ((C.rename Nat.succ).rename Nat.succ)))) = true := by
    simp only [ModeShape, Expr.pi, tm, Expr.const, Expr.app, typeShape_node]; rfl
  have hE := appliedAt_of_judge_tm hsg hΓs hP (judge_lam hsb)
  have hE₀ := appliedAt_of_judge_tm hsg hΓA hCs hsb
  have lamL : ∀ X : Expr, RoseTree.label (Expr.lam X) = Label.lam := fun _ ↦ rfl
  have lamC : ∀ X : Expr, RoseTree.children (Expr.lam X) = [X] := fun _ ↦ rfl
  have v₁ : (RoseTree.node (Label.app (Head.var 1)) [] : Expr) = Expr.var 1 [] := rfl
  have v₀ : (RoseTree.node (Label.app (Head.var 0)) [] : Expr) = Expr.var 0 [] := rfl
  -- the step at the two innermost variables, under the weakening past the element and the rest
  rw [rename_succ_four, rename_lam] at ha₀ ha'
  simp only [lamL, lamC] at ha₀ ha'
  rw [v₁, hsub_var_base hE (liftR (· + 4)) (fun i ↦ match i with | 0 => 1 | i + 1 => i + 4) rfl
    (fun _ ↦ rfl) rfl, Option.bind_some, rename_lam] at ha₀ ha'
  simp only [lamL, lamC] at ha₀ ha'
  rw [v₀, hsub_var_base hE₀ _ (liftR (liftR (· + 2))) rfl
    (fun i ↦ by rcases i with _ | i <;> rfl) (k := 0) rfl, Option.some.injEq] at ha₀ ha'
  subst ha₀ ha'
  -- the step applied to the element, under the weakening past the element and the rest
  rw [rename_succ_two, rename_lam] at hb
  simp only [lamL, lamC] at hb
  rw [v₁, hsub_var_base hE (liftR (· + 2)) (fun i ↦ match i with | 0 => 1 | i + 1 => i + 2) rfl
    (fun _ ↦ rfl) rfl, Option.bind_some, rename_lam] at hb
  simp only [lamL, lamC] at hb
  -- the element and the rest substituted into the start's step, which mentions neither
  rw [show sb.rename (liftR (liftR (· + 2))) =
      (sb.rename (liftR (liftR Nat.succ))).rename (liftR^[3] Nat.succ) by
    rw [rename_rename]
    exact congrArg _ (funext fun i ↦ by rcases i with _ | _ | i <;> rfl),
    hsubWith_vacuous, Option.some.injEq] at ha₁
  subst ha₁
  rw [show sb.rename (liftR (liftR Nat.succ)) = sb.rename (liftR^[2] Nat.succ) from rfl,
    hsubWith_vacuous, Option.some.injEq] at ha₂
  subst ha₂
  simp only [node_inj, List.cons.injEq, and_true, true_and] at hF
  subst hF
  -- the decodings
  obtain ⟨sz, hsz, hzt⟩ := termOf_typed hk hsg hc.toTmCtx hxc hz'
  obtain ⟨ss, hss, hst⟩ := termOf_typed hk hsg ((hc.toTmCtx.consTm hxa).consTm (encTy_succ hxc))
    (encTy_succ (encTy_succ hxc)) hsb
  obtain ⟨sh, hsh, hht⟩ := termOf_typed hk hsg hc.toTmCtx hxa hh
  obtain ⟨st, hst', -⟩ := termOf_typed (a := FreeTopos.list xa) hk hsg hc.toTmCtx
    (by rw [encTy_list, hxa]; rfl) ht
  have hS₂ : termOf k (none :: none :: none :: none :: env) (sb.rename (liftR (liftR (· + 2)))) =
      some (Term.rename ss (liftR (liftR (· + 2)))) :=
    termOf_rename _ _ hss (fun i ↦ by rcases i with _ | _ | i <;> rfl) (by numTm_ren)
  have hS₁ : termOf k (none :: none :: none :: env)
      (sb.rename (liftR fun i ↦ match i with | 0 => 1 | i + 1 => i + 2)) =
      some (Term.rename ss (liftR fun i ↦ match i with | 0 => 1 | i + 1 => i + 2)) :=
    termOf_rename _ _ hss (fun i ↦ by rcases i with _ | _ | i <;> rfl) (by numTm_ren)
  have hR : termOf k (none :: none :: env) (Expr.const 33 [A, C,
      (z.rename Nat.succ).rename Nat.succ,
      Expr.lam (Expr.lam (sb.rename (liftR (liftR (· + 2))))), Expr.var 0 []]) =
      some (Term.listRec (weaken1 (weaken1 sz)) (Term.rename ss (liftR (liftR (· + 2))))
        (Term.var 0)) := by
    simp only [termOf_const, termOf_lam, List.map_cons, List.map_nil, decStep, dec_tmIdx,
      termOf_shift (termOf_shift hsz), hS₂, Option.map_some, lamBody_lam, Option.bind_eq_bind,
      Option.bind_some, Option.pure_def]
    rfl
  have hb' := termOf_hsub₀ (env := none :: none :: env) hb hS₁ hR
  have hb₁' := termOf_hsub₁ hb₁ hb' (termOf_shift hsh)
  have hb₂' := termOf_hsub₀ hb₂ hb₁' hst'
  rw [listCons_rhs (varLeaves_of_typeIn hzt) (varLeaves_of_typeIn hst)
    (varLeaves_of_typeIn hht)] at hb₂'
  change termOf k env (Expr.const 16 [C, Expr.const 33 [A, C, z, Expr.lam (Expr.lam sb),
    Expr.const 32 [A, Expr.const 8 [A, Expr.const 30 [A], h, t]]], b₂]) = some φ at hφ
  simp only [termOf_const, termOf_lam, List.map_cons, List.map_nil, decStep, dec_tmIdx, hsz, hss,
    hsh,
    hst', hb₂', decTy_tmIdx hxa, Option.map_some, lamBody_lam,
    Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at hφ
  subst hφ
  exact ⟨joinD (ruleD (.listCons k.cons)) reflD, by rw [decPf_const]; rfl,
    check_join (check_listCons hk.cons _ _ _ _ _) (check_refl _)⟩

include hk hsg in
/-- The soundness of the decoding of the computation of the fold of a rose tree at a
construction. -/
theorem sound_roseNode (hc : PfCtx G k n ΓLF env Γ Φ) {C s l cs F : Expr} {φ : MTerm}
    (hS : spine ΓLF (Expr.pi tp (Expr.pi (Expr.arrow (tm (prod nat (list (v 0)))) (tm (v 0)))
      (Expr.pi (tm nat) (Expr.pi (tm (list rose))
        (pf (eq (v 3) (roseRec (v 3) (Expr.lam (Expr.var 3 [v 0]))
            (node (pair nat (list rose) (v 1) (v 0))))
          (Expr.var 2 [pair nat (list (v 3)) (v 1) (listRec rose (list (v 3)) (nil (v 3))
            (Expr.lam (Expr.lam (cons (v 5) (pair (v 5) (list (v 5))
              (roseRec (v 5) (Expr.lam (Expr.var 5 [v 0])) (v 1)) (v 0))))) (v 0))])))))))
      [(C, judge sg C), (s, judge sg s), (l, judge sg l), (cs, judge sg cs)] = some (pf F))
    (hφ : termOf k env F = some φ) :
    ∃ D, decPf k (Expr.const 40 [C, s, l, cs]) env Φ.length = some D ∧
      (check G E n D).2 Γ Φ φ = true := by
  obtain ⟨xc, hxc, -⟩ := tyComplete hsg hc.heads₀ C (spine_tp₁ hS)
  have hpc : encTy k env.length (FreeTopos.prod FreeTopos.nat (FreeTopos.list xc)) =
      some (prod nat (list C)) := by rw [encTy_prod, encTy_list, hxc]; rfl
  simp only [tm, tp, pf, eq, roseRec, node, listRec, nil, nilAt, cons, pair, list, prod, nat,
    rose, star, Expr.const, Expr.app] at hS
  lf_spine_open_at hS [Option.bind_eq_some_iff]
  obtain ⟨-, a₀, b, ⟨hs', ha₀, a', ha', hb⟩, a₁, b₁, ⟨hl, ha₁, hb₁⟩, hcs, a₂, ha₂, b₂, hb₂,
    hF⟩ := hS
  obtain ⟨sb, rfl, hsb⟩ := judge_check_pi_inv hs'
  have hΓs := fun a ha ↦ (hc.typeShape a ha).1
  have hCs : ModeShape (.check (tm (C.rename Nat.succ))) = true := by
    simp only [ModeShape, tm, Expr.const, Expr.app, typeShape_node]; rfl
  have hE := appliedAt_of_judge_tm hsg (A := prod nat (list C)) hΓs hCs hsb
  have lamL : ∀ X : Expr, RoseTree.label (Expr.lam X) = Label.lam := fun _ ↦ rfl
  have lamC : ∀ X : Expr, RoseTree.children (Expr.lam X) = [X] := fun _ ↦ rfl
  have v₀ : (RoseTree.node (Label.app (Head.var 0)) [] : Expr) = Expr.var 0 [] := rfl
  have r3 : ∀ e : Expr, ((e.rename Nat.succ).rename Nat.succ).rename Nat.succ = e.rename (· + 3) :=
    fun e ↦ by rw [rename_rename, rename_rename]; rfl
  have r5 : ∀ e : Expr, ((((e.rename Nat.succ).rename Nat.succ).rename Nat.succ).rename
      Nat.succ).rename Nat.succ = e.rename (· + 5) :=
    fun e ↦ by rw [rename_rename, rename_rename, rename_rename, rename_rename]; rfl
  -- the step at the innermost variable, under the weakening past the label and the children
  rw [r3, rename_lam] at ha₀
  rw [r5, rename_lam] at ha'
  simp only [lamL, lamC] at ha₀ ha'
  rw [v₀, hsub_var_base hE (liftR (· + 3)) (liftR (· + 2)) rfl (fun _ ↦ rfl) (k := 0) rfl,
    Option.some.injEq] at ha₀
  rw [v₀, hsub_var_base hE (liftR (· + 5)) (liftR (· + 4)) rfl (fun _ ↦ rfl) (k := 0) rfl,
    Option.some.injEq] at ha'
  subst ha₀ ha'
  -- the label and the children substituted into the outer step, which mentions neither
  rw [hsubWith_vacuous' _ _ _ (g := liftR (· + 1)) fun i ↦ by rcases i with _ | i <;> rfl,
    Option.some.injEq] at ha₁
  subst ha₁
  rw [hsubWith_vacuous' _ _ _ (g := id) fun i ↦ by rcases i with _ | i <;> rfl, rename_id,
    Option.some.injEq] at ha₂
  subst ha₂
  -- the step applied to the pair, under the weakening past the label and the children
  rw [rename_succ_two, rename_lam] at hb
  simp only [lamL, lamC] at hb
  simp only [node_inj, List.cons.injEq, and_true, true_and] at hF
  subst hF
  -- the decodings
  let C₂ : Expr := (C.rename Nat.succ).rename Nat.succ
  let C₄ : Expr := (C₂.rename Nat.succ).rename Nat.succ
  obtain ⟨ss, hss, hst⟩ := termOf_typed hk hsg (hc.toTmCtx.consTm hpc) (encTy_add hxc) hsb
  obtain ⟨sl, hsl, hlt⟩ := termOf_typed (a := FreeTopos.nat) hk hsg hc.toTmCtx rfl hl
  obtain ⟨scs, hscs, -⟩ := termOf_typed (a := FreeTopos.list FreeTopos.rose) hk hsg hc.toTmCtx rfl
    hcs
  have hS₂ : termOf k (none :: none :: none :: env) (sb.rename (liftR (· + 2))) =
      some (Term.rename ss (liftR (· + 2))) :=
    termOf_rename _ _ hss (fun i ↦ by rcases i with _ | i <;> rfl) (by numTm_ren)
  have hS₄ : termOf k (none :: none :: none :: none :: none :: env) (sb.rename (liftR (· + 4))) =
      some (Term.rename ss (liftR (· + 4))) :=
    termOf_rename _ _ hss (fun i ↦ by rcases i with _ | i <;> rfl) (by numTm_ren)
  have hP : termOf k (none :: none :: env) (Expr.const 8 [Expr.const 5 [], Expr.const 30 [C₂],
      Expr.var 1 [], Expr.const 33 [Expr.const 37 [], Expr.const 30 [C₂],
        Expr.const 31 [C₂, Expr.const 7 []],
        Expr.lam (Expr.lam (Expr.const 32 [C₄, Expr.const 8 [C₄, Expr.const 30 [C₄],
          Expr.const 39 [C₄, Expr.lam (sb.rename (liftR (· + 4))), Expr.var 1 []],
          Expr.var 0 []]])), Expr.var 0 []]]) =
      some (Term.pair (Term.var 1) (Term.listRec (Term.arr k.nil [xc] Term.star)
        (Term.arr k.cons [xc] (Term.pair (Term.roseRec xc (Term.rename ss (liftR (· + 4)))
          (Term.var 1)) (Term.var 0))) (Term.var 0))) := by
    simp only [termOf_const, termOf_lam, List.map_cons, List.map_nil, decStep, dec_tmIdx, hS₄,
      C₂, C₄, decTy_tmIdx (env := none :: none :: env) (encTy_succ (encTy_succ hxc)),
      decTy_tmIdx (env := none :: none :: none :: none :: env)
        (encTy_succ (encTy_succ (encTy_succ (encTy_succ hxc)))), Option.map_some, lamBody_lam,
      Option.bind_eq_bind, Option.bind_some, Option.pure_def]
    rfl
  have hb' := termOf_hsub₀ (env := none :: none :: env) hb hS₂ hP
  have hb₁' := termOf_hsub₁ hb₁ hb' (termOf_shift hsl)
  have hb₂' := termOf_hsub₀ hb₂ hb₁' hscs
  rw [roseNode_rhs ss (varLeaves_of_typeIn hlt)] at hb₂'
  change termOf k env (Expr.const 16 [C, Expr.const 39 [C, Expr.lam sb,
    Expr.const 38 [Expr.const 8 [Expr.const 5 [], Expr.const 30 [Expr.const 37 []], l, cs]]],
    b₂]) = some φ at hφ
  simp only [termOf_const, termOf_lam, List.map_cons, List.map_nil, decStep, dec_tmIdx, hss, hsl,
    hscs,
    hb₂', decTy_tmIdx hxc, Option.map_eq_map, Option.map_some,
    lamBody_lam, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at hφ
  subst hφ
  exact ⟨joinD (ruleD (.roseNode k.node k.nil k.cons)) reflD, by rw [decPf_const]; rfl,
    check_join (check_roseNode (.inl hk.node) hk.nil hk.cons _ _ _ _) (check_refl _)⟩

include hk hsg in
/-- The soundness of the decoding of the computation of the fold of a rose tree of labels of a type
at a construction. -/
theorem sound_lroseNode (hc : PfCtx G k n ΓLF env Γ Φ) {A C s l cs F : Expr} {φ : MTerm}
    (hS : spine ΓLF (Expr.pi tp (Expr.pi tp
      (Expr.pi (Expr.arrow (tm (prod (v 1) (list (v 0)))) (tm (v 0))) (Expr.pi (tm (v 2))
        (Expr.pi (tm (list (lrose (v 3))))
          (pf (eq (v 3) (lroseRec (v 4) (v 3) (Expr.lam (Expr.var 3 [v 0]))
              (lnode (v 4) (pair (v 4) (list (lrose (v 4))) (v 1) (v 0))))
            (Expr.var 2 [pair (v 4) (list (v 3)) (v 1) (listRec (lrose (v 4)) (list (v 3))
              (nil (v 3)) (Expr.lam (Expr.lam (cons (v 5) (pair (v 5) (list (v 5))
                (lroseRec (v 6) (v 5) (Expr.lam (Expr.var 5 [v 0])) (v 1)) (v 0))))) (v 0))]))))))))
      [(A, judge sg A), (C, judge sg C), (s, judge sg s), (l, judge sg l),
        (cs, judge sg cs)] = some (pf F))
    (hφ : termOf k env F = some φ) :
    ∃ D, decPf k (Expr.const 45 [A, C, s, l, cs]) env Φ.length = some D ∧
      (check G E n D).2 Γ Φ φ = true := by
  have hT := spine_tp₂ hS
  obtain ⟨xa, hxa, -⟩ := tyComplete hsg hc.heads₀ A hT.1
  obtain ⟨xc, hxc, -⟩ := tyComplete hsg hc.heads₀ C hT.2
  have hpc : encTy k env.length (FreeTopos.prod xa (FreeTopos.list xc)) =
      some (prod A (list C)) := by
    rw [encTy_prod, encTy_list, hxa, hxc]; rfl
  simp only [tm, tp, pf, eq, lroseRec, lnode, listRec, nil, nilAt, cons, pair, list, prod, lrose,
    star, Expr.const, Expr.app] at hS
  lf_spine_open_at hS [Option.bind_eq_some_iff]
  obtain ⟨-, -, a₀, b, ⟨hs', ha₀, a', ha', hb⟩, a₁, b₁, ⟨hl, ha₁, hb₁⟩, hcs, a₂, ha₂, b₂, hb₂,
    hF⟩ := hS
  obtain ⟨sb, rfl, hsb⟩ := judge_check_pi_inv hs'
  have hΓs := fun a ha ↦ (hc.typeShape a ha).1
  have hCs : ModeShape (.check (tm (C.rename Nat.succ))) = true := by
    simp only [ModeShape, tm, Expr.const, Expr.app, typeShape_node]; rfl
  have hE := appliedAt_of_judge_tm hsg (A := prod A (list C)) hΓs hCs hsb
  have lamL : ∀ X : Expr, RoseTree.label (Expr.lam X) = Label.lam := fun _ ↦ rfl
  have lamC : ∀ X : Expr, RoseTree.children (Expr.lam X) = [X] := fun _ ↦ rfl
  have v₀ : (RoseTree.node (Label.app (Head.var 0)) [] : Expr) = Expr.var 0 [] := rfl
  have r3 : ∀ e : Expr, ((e.rename Nat.succ).rename Nat.succ).rename Nat.succ = e.rename (· + 3) :=
    fun e ↦ by rw [rename_rename, rename_rename]; rfl
  have r5 : ∀ e : Expr, ((((e.rename Nat.succ).rename Nat.succ).rename Nat.succ).rename
      Nat.succ).rename Nat.succ = e.rename (· + 5) :=
    fun e ↦ by rw [rename_rename, rename_rename, rename_rename, rename_rename]; rfl
  -- the step at the innermost variable, under the weakening past the label and the children
  rw [r3, rename_lam] at ha₀
  rw [r5, rename_lam] at ha'
  simp only [lamL, lamC] at ha₀ ha'
  rw [v₀, hsub_var_base hE (liftR (· + 3)) (liftR (· + 2)) rfl (fun _ ↦ rfl) (k := 0) rfl,
    Option.some.injEq] at ha₀
  rw [v₀, hsub_var_base hE (liftR (· + 5)) (liftR (· + 4)) rfl (fun _ ↦ rfl) (k := 0) rfl,
    Option.some.injEq] at ha'
  subst ha₀ ha'
  -- the label and the children substituted into the outer step, which mentions neither
  rw [hsubWith_vacuous' _ _ _ (g := liftR (· + 1)) fun i ↦ by rcases i with _ | i <;> rfl,
    Option.some.injEq] at ha₁
  subst ha₁
  rw [hsubWith_vacuous' _ _ _ (g := id) fun i ↦ by rcases i with _ | i <;> rfl, rename_id,
    Option.some.injEq] at ha₂
  subst ha₂
  -- the step applied to the pair, under the weakening past the label and the children
  rw [rename_succ_two, rename_lam] at hb
  simp only [lamL, lamC] at hb
  simp only [node_inj, List.cons.injEq, and_true, true_and] at hF
  subst hF
  -- the decodings
  let A₂ : Expr := (A.rename Nat.succ).rename Nat.succ
  let A₄ : Expr := (A₂.rename Nat.succ).rename Nat.succ
  let C₂ : Expr := (C.rename Nat.succ).rename Nat.succ
  let C₄ : Expr := (C₂.rename Nat.succ).rename Nat.succ
  obtain ⟨ss, hss, hst⟩ := termOf_typed hk hsg (hc.toTmCtx.consTm hpc) (encTy_add hxc) hsb
  obtain ⟨sl, hsl, hlt⟩ := termOf_typed hk hsg hc.toTmCtx hxa hl
  obtain ⟨scs, hscs, -⟩ := termOf_typed (a := FreeTopos.list (FreeTopos.lrose xa)) hk hsg
    hc.toTmCtx
    (by rw [encTy_list, encTy_lrose, hxa]; rfl) hcs
  have hS₂ : termOf k (none :: none :: none :: env) (sb.rename (liftR (· + 2))) =
      some (Term.rename ss (liftR (· + 2))) :=
    termOf_rename _ _ hss (fun i ↦ by rcases i with _ | i <;> rfl) (by numTm_ren)
  have hS₄ : termOf k (none :: none :: none :: none :: none :: env) (sb.rename (liftR (· + 4))) =
      some (Term.rename ss (liftR (· + 4))) :=
    termOf_rename _ _ hss (fun i ↦ by rcases i with _ | i <;> rfl) (by numTm_ren)
  have hP : termOf k (none :: none :: env) (Expr.const 8 [A₂, Expr.const 30 [C₂],
      Expr.var 1 [], Expr.const 33 [Expr.const 42 [A₂], Expr.const 30 [C₂],
        Expr.const 31 [C₂, Expr.const 7 []],
        Expr.lam (Expr.lam (Expr.const 32 [C₄, Expr.const 8 [C₄, Expr.const 30 [C₄],
          Expr.const 44 [A₄, C₄, Expr.lam (sb.rename (liftR (· + 4))), Expr.var 1 []],
          Expr.var 0 []]])), Expr.var 0 []]]) =
      some (Term.pair (Term.var 1) (Term.listRec (Term.arr k.nil [xc] Term.star)
        (Term.arr k.cons [xc] (Term.pair (Term.roseRec xc (Term.rename ss (liftR (· + 4)))
          (Term.var 1)) (Term.var 0))) (Term.var 0))) := by
    simp only [termOf_const, termOf_lam, List.map_cons, List.map_nil, decStep, dec_tmIdx, hS₄,
      C₂, C₄, decTy_tmIdx (env := none :: none :: env) (encTy_succ (encTy_succ hxc)),
      decTy_tmIdx (env := none :: none :: none :: none :: env)
        (encTy_succ (encTy_succ (encTy_succ (encTy_succ hxc)))), Option.map_some, lamBody_lam,
      Option.bind_eq_bind, Option.bind_some, Option.pure_def]
    rfl
  have hb' := termOf_hsub₀ (env := none :: none :: env) hb hS₂ hP
  have hb₁' := termOf_hsub₁ hb₁ hb' (termOf_shift hsl)
  have hb₂' := termOf_hsub₀ hb₂ hb₁' hscs
  rw [roseNode_rhs ss (varLeaves_of_typeIn hlt)] at hb₂'
  change termOf k env (Expr.const 16 [C, Expr.const 44 [A, C, Expr.lam sb,
    Expr.const 43 [A, Expr.const 8 [A, Expr.const 30 [Expr.const 42 [A]], l, cs]]],
    b₂]) = some φ at hφ
  simp only [termOf_const, termOf_lam, List.map_cons, List.map_nil, decStep, dec_tmIdx, hss, hsl,
    hscs,
    hb₂', decTy_tmIdx hxa, decTy_tmIdx hxc,
    Option.map_some, lamBody_lam, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
    Option.some.injEq] at hφ
  subst hφ
  exact ⟨joinD (ruleD (.roseNode k.lnode k.nil k.cons)) reflD, by rw [decPf_const]; rfl,
    check_join (check_roseNode (.inr hk.lnode) hk.nil hk.cons _ _ _ _) (check_refl _)⟩

include hk hsg in
/-- The soundness of the decoding of function extensionality. -/
theorem sound_funExt (hc : PfCtx G k n ΓLF env Γ Φ) {A B f g dH F : Expr} {φ : MTerm}
    (ihH : PfLam sg (PfSoundAt sg G k E n) dH)
    (hS : spine ΓLF (Expr.pi tp (Expr.pi tp (Expr.pi (tm (exp (v 1) (v 0)))
      (Expr.pi (tm (exp (v 2) (v 1)))
      (Expr.arrow (Expr.pi (tm (v 3))
          (pf (eq (v 3) (app (v 4) (v 3) (v 2) (v 0)) (app (v 4) (v 3) (v 1) (v 0)))))
        (pf (eq (exp (v 3) (v 2)) (v 1) (v 0))))))))
      [(A, judge sg A), (B, judge sg B), (f, judge sg f), (g, judge sg g),
        (dH, judge sg dH)] = some (pf F))
    (hφ : termOf k env F = some φ) :
    ∃ D, decPf k (Expr.const 27 [A, B, f, g, dH]) env Φ.length = some D ∧
      (check G E n D).2 Γ Φ φ = true := by
  have hT := spine_tp₂ hS
  obtain ⟨xa, hxa, -⟩ := tyComplete hsg hc.heads₀ A hT.1
  obtain ⟨xb, hxb, -⟩ := tyComplete hsg hc.heads₀ B hT.2
  simp only [tm, tp, pf, eq, exp, app, Expr.const, Expr.app] at hS
  lf_spine_open_at hS [Option.bind_eq_some_iff]
  obtain ⟨-, -, hf, hg, hdH, hF⟩ := hS
  simp only [node_inj, List.cons.injEq, and_true, true_and] at hF
  subst hF
  have hxab : encTy k env.length (FreeTopos.exp xa xb) = some (exp A B) := by
    rw [encTy_exp, hxa, hxb]; rfl
  obtain ⟨sf, hsf, hft⟩ := termOf_typed hk hsg hc.toTmCtx hxab hf
  obtain ⟨sgg, hsgg, -⟩ := termOf_typed hk hsg hc.toTmCtx hxab hg
  obtain ⟨body, rfl, hbody, hsound⟩ := ihH ΓLF _ _ hdH
  have hF' : termOf k (none :: env) (Expr.const 16 [B,
      Expr.const 12 [A, B, f.rename Nat.succ, Expr.var 0],
      Expr.const 12 [A, B, g.rename Nat.succ, Expr.var 0]]) =
      some (Term.eq (Term.app (weaken1 sf) (Term.var 0))
        (Term.app (weaken1 sgg) (Term.var 0))) := by
    simp only [termOf_const, List.map_cons, List.map_nil, decStep, dec_tmIdx, termOf_shift hsf,
      termOf_shift hsgg, termOf_var0, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  obtain ⟨D', hD', hcheck⟩ := hsound _ _ _ _ _ _ (hc.consTm hxa) hbody hF'
  rw [List.length_map] at hD'
  rw [show RoseTree.node (.app (.const 16)) [RoseTree.node (.app (.const 3)) [A, B], f, g] =
      Expr.const 16 [Expr.const 3 [A, B], f, g] from rfl] at hφ
  simp only [termOf_const, List.map_cons, List.map_nil, decStep, dec_tmIdx, hsf, hsgg,
    Option.bind_eq_bind,
    Option.bind_some, Option.pure_def, Option.some.injEq] at hφ
  subst hφ
  refine ⟨nd .funExt [D'], ?_, check_funExt hft hcheck⟩
  rw [decPf_const]
  simp only [List.map_cons, List.map_nil, decPfStep.eq_def, decPf_lam, hD', Option.bind_eq_bind,
    Option.bind_some, Option.pure_def]

include hk hsg in
/-- The soundness of the decoding of propositional extensionality. -/
theorem sound_propExt (hc : PfCtx G k n ΓLF env Γ Φ) {P Q d₁ d₂ F : Expr} {φ : MTerm}
    (ih₁ : PfLam sg (PfSoundAt sg G k E n) d₁) (ih₂ : PfLam sg (PfSoundAt sg G k E n) d₂)
    (hS : spine ΓLF (Expr.pi (tm omega) (Expr.pi (tm omega)
      (Expr.arrow (Expr.arrow (pf (v 1)) (pf (v 0)))
        (Expr.arrow (Expr.arrow (pf (v 0)) (pf (v 1))) (pf (eq omega (v 1) (v 0)))))))
      [(P, judge sg P), (Q, judge sg Q), (d₁, judge sg d₁), (d₂, judge sg d₂)] =
        some (pf F))
    (hφ : termOf k env F = some φ) :
    ∃ D, decPf k (Expr.const 28 [P, Q, d₁, d₂]) env Φ.length = some D ∧
      (check G E n D).2 Γ Φ φ = true := by
  simp only [tm, pf, eq, omega, Expr.const, Expr.app] at hS
  lf_spine_at hS [Option.bind_eq_some_iff]
  obtain ⟨hP, hQ, hd₁, hd₂, hF⟩ := hS
  simp only [node_inj, List.cons.injEq, and_true, true_and] at hF
  subst hF
  obtain ⟨sP, hsP, hPt⟩ := termOf_typed (a := FreeTopos.omega) hk hsg hc.toTmCtx rfl hP
  obtain ⟨sQ, hsQ, hQt⟩ := termOf_typed (a := FreeTopos.omega) hk hsg hc.toTmCtx rfl hQ
  obtain ⟨b₁, rfl, hb₁, hsound₁⟩ := ih₁ ΓLF _ _ hd₁
  obtain ⟨b₂, rfl, hb₂, hsound₂⟩ := ih₂ ΓLF _ _ hd₂
  obtain ⟨D₁, hD₁, hc₁⟩ := hsound₁ _ _ _ _ _ _ (hc.consPf hsP hPt) hb₁
    (by rw [termOf_consPf_shift]; exact hsQ)
  obtain ⟨D₂, hD₂, hc₂⟩ := hsound₂ _ _ _ _ _ _ (hc.consPf hsQ hQt) hb₂
    (by rw [termOf_consPf_shift]; exact hsP)
  rw [List.length_append, List.length_singleton] at hD₁ hD₂
  rw [show RoseTree.node (.app (.const 16)) [RoseTree.node (.app (.const 4)) [], P, Q] =
      Expr.const 16 [omega, P, Q] from rfl] at hφ
  simp only [termOf_const, List.map_cons, List.map_nil, decStep, dec_tmIdx, hsP, hsQ,
    Option.bind_eq_bind,
    Option.bind_some, Option.pure_def, Option.some.injEq] at hφ
  subst hφ
  refine ⟨nd .propExt [D₁, D₂], ?_, check_propExt hPt hQt hc₁ hc₂⟩
  rw [decPf_const]
  simp only [List.map_cons, List.map_nil, decPfStep.eq_def, decPf_lam, hD₁, hD₂,
    Option.bind_eq_bind, Option.bind_some, Option.pure_def]

include hk hsg in
/-- The soundness of the decoding of the substitution of equals. -/
theorem sound_leib (hc : PfCtx G k n ΓLF env Γ Φ) {A P t u dh dp F : Expr} {φ : MTerm}
    (ihh : PfSoundAt sg G k E n dh) (ihp : PfSoundAt sg G k E n dp)
    (hS : spine ΓLF (Expr.pi tp (Expr.pi (Expr.arrow (tm (v 0)) (tm omega))
      (Expr.pi (tm (v 1)) (Expr.pi (tm (v 2))
      (Expr.arrow (pf (eq (v 3) (v 1) (v 0)))
        (Expr.arrow (pf (Expr.var 2 [v 1])) (pf (Expr.var 2 [v 0]))))))))
      [(A, judge sg A), (P, judge sg P), (t, judge sg t), (u, judge sg u),
        (dh, judge sg dh), (dp, judge sg dp)] = some (pf F))
    (hφ : termOf k env F = some φ) :
    ∃ D, decPf k (Expr.const 19 [A, P, t, u, dh, dp]) env Φ.length = some D ∧
      (check G E n D).2 Γ Φ φ = true := by
  obtain ⟨xa, hxa, hIxa⟩ := tyComplete hsg hc.heads₀ A (spine_tp₁ hS)
  simp only [tm, tp, pf, eq, omega, Expr.const, Expr.app] at hS
  lf_spine_open_at hS [Option.bind_eq_some_iff]
  obtain ⟨-, a, b, ⟨hP, ha, hb⟩, a₁, b₁, ⟨ht, ha₁, hb₁⟩, a', b', ⟨hu, ha', hb'⟩, a₂, a₃,
    ⟨hdh, ha₂, ha₃⟩, hdp, x, hx, hF⟩ := hS
  obtain ⟨Pb, rfl, hPb⟩ := judge_check_pi_inv hP
  simp only [Expr.lam, rename_node, RoseTree.label_node, RoseTree.children_node, List.zipIdx,
    List.map_cons, List.map_nil, Label.binders, Function.iterate_one, Label.rename] at ha hb
  rw [rename_rename, rename_rename] at ha
  rw [rename_rename, rename_rename, rename_rename] at hb
  rw [rename_rename] at ha₁ hb'
  rw [rename_rename, rename_rename] at hb₁
  have hΓs := fun a ha ↦ (hc.typeShape a ha).1
  have hOs : ModeShape (.check (tm omega)) = true := by
    simp only [ModeShape, tm, Expr.const, Expr.app, typeShape_node]; rfl
  have hApp := appliedAt_of_judge_tm hsg hΓs hOs hPb
  obtain ⟨Xt, hXt⟩ := hsubWith_base_total 6 Pb t 0 hApp
  obtain ⟨Xu, hXu⟩ := hsubWith_base_total 6 Pb u 0 hApp
  have hσ₂ : ∀ i : ℕ, i + 1 + 2 ≠ 2 ∧ renumber 2 (i + 1 + 2) = (Nat.succ ∘ Nat.succ) i :=
    fun i ↦ ⟨by omega, by simp only [renumber, Function.comp_apply]; split_ifs <;> omega⟩
  -- the motive at `t`, the type of `dp`
  obtain rfl := Option.some.inj (ha.symm.trans (hsub_var_base hApp
    ((liftR Nat.succ ∘ liftR Nat.succ) ∘ liftR Nat.succ) (· + 2) rfl (fun _ ↦ rfl) rfl))
  obtain rfl := Option.some.inj (ha₁.symm.trans (hsub_hole hXt (τ := (· + 2)) rfl hσ₂))
  obtain rfl := Option.some.inj (ha'.symm.trans
    (hsubWith_vacuous' _ _ _ (j := 1) (g := Nat.succ) fun _ ↦ rfl))
  rw [hsubWith_shift, Option.some.injEq] at ha₂
  subst ha₂
  -- the motive at `u`, the conclusion
  obtain rfl := Option.some.inj (hb.symm.trans (hsub_var_base hApp
    (((liftR Nat.succ ∘ liftR Nat.succ) ∘ liftR Nat.succ) ∘ liftR Nat.succ)
    (fun i ↦ match i with | 0 => 2 | k + 1 => k + 4) rfl (fun _ ↦ rfl) rfl))
  obtain rfl := Option.some.inj (hb₁.symm.trans (hsubWith_vacuous' _ _ _ (j := 3)
    (g := fun i ↦ match i with | 0 => 2 | k + 1 => k + 3) fun i ↦ by rcases i with _ | i <;> rfl))
  obtain rfl := Option.some.inj (hb'.symm.trans (hsub_hole hXu
    (τ := fun i ↦ match i with | 0 => 2 | k + 1 => k + 3) rfl hσ₂))
  obtain rfl := Option.some.inj (ha₃.symm.trans
    (hsubWith_vacuous' _ _ _ (j := 1) (g := Nat.succ) fun _ ↦ rfl))
  rw [hsubWith_shift, Option.some.injEq] at hx
  subst hx
  simp only [node_inj, List.cons.injEq, and_true, true_and] at hF
  subst hF
  -- the decodings
  obtain ⟨st, hst, htt⟩ := termOf_typed hk hsg hc.toTmCtx hxa ht
  obtain ⟨su, hsu, hut⟩ := termOf_typed hk hsg hc.toTmCtx hxa hu
  obtain ⟨sp, hsp, hpt⟩ := termOf_typed (a := FreeTopos.omega) hk hsg (hc.toTmCtx.consTm hxa)
    rfl hPb
  have hXt' := termOf_hsub₀ hXt hsp hst
  obtain rfl := Option.some.inj (hφ.symm.trans (termOf_hsub₀ hXu hsp hsu))
  have heq : termOf k env (Expr.const 16 [A, t, u]) = some (Term.eq st su) := by
    simp only [termOf_const, List.map_cons, List.map_nil, decStep, dec_tmIdx, hst, hsu,
      Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  have hψ := typeIn_eq htt hut
  obtain ⟨Dh, hDh, hch⟩ := ihh _ _ _ _ _ _ hc hdh heq
  obtain ⟨Dp, hDp, hcp⟩ := ihp _ _ _ _ _ _ (hc.addHyp hψ) hdp hXt'
  rw [List.length_append, List.length_singleton] at hDp
  refine ⟨leibD xa sp st su Φ.length Dh Dp, ?_,
    check_leibD (hIxa) hpt htt hut hch hcp⟩
  rw [decPf_const]
  simp only [List.map_cons, List.map_nil, decPfStep.eq_def, termOf_lam, hsp, hst, hsu, hDh, hDp,
    decTy_encTy _ xa A hxa, Option.map_some, Option.bind_eq_bind, Option.bind_some, lamBody_lam,
    Option.pure_def]

include hk hsg in
/-- The soundness of the decoding of congruence. -/
theorem sound_cong (hc : PfCtx G k n ΓLF env Γ Φ) {A B f a b dh F : Expr} {φ : MTerm}
    (ihh : PfSoundAt sg G k E n dh)
    (hS : spine ΓLF (Expr.pi tp (Expr.pi tp (Expr.pi (Expr.arrow (tm (v 1)) (tm (v 0)))
      (Expr.pi (tm (v 2)) (Expr.pi (tm (v 3))
        (Expr.arrow (pf (eq (v 4) (v 1) (v 0)))
          (pf (eq (v 3) (Expr.var 2 [v 1]) (Expr.var 2 [v 0])))))))))
      [(A, judge sg A), (B, judge sg B), (f, judge sg f), (a, judge sg a), (b, judge sg b),
        (dh, judge sg dh)] = some (pf F))
    (hφ : termOf k env F = some φ) :
    ∃ D, decPf k (Expr.const 47 [A, B, f, a, b, dh]) env Φ.length = some D ∧
      (check G E n D).2 Γ Φ φ = true := by
  have hT := spine_tp₂ hS
  obtain ⟨xa, hxa, hIxa⟩ := tyComplete hsg hc.heads₀ A hT.1
  obtain ⟨xb, hxb, -⟩ := tyComplete hsg hc.heads₀ B hT.2
  simp only [tm, tp, pf, eq, Expr.const, Expr.app] at hS
  lf_spine_open_at hS [Option.bind_eq_some_iff]
  obtain ⟨-, -, a₁, b₁, ⟨hf, ha₁, hb₁⟩, a₂, b₂, ⟨ha, ha₂, hb₂⟩, a₃, b₃, ⟨hb, ha₃, hb₃⟩, hdh, a₄,
    ha₄, b₄, hb₄, hF⟩ := hS
  obtain ⟨fb, rfl, hfb⟩ := judge_check_pi_inv hf
  have hΓs := fun a ha ↦ (hc.typeShape a ha).1
  have hBs : ModeShape (.check (tm (B.rename Nat.succ))) = true := by
    simp only [ModeShape, tm, Expr.const, Expr.app, typeShape_node]; rfl
  have hApp := appliedAt_of_judge_tm (A := A) hsg hΓs hBs hfb
  obtain ⟨Xa, hXa⟩ := hsubWith_base_total 6 fb a 0 hApp
  obtain ⟨Xb, hXb⟩ := hsubWith_base_total 6 fb b 0 hApp
  have lamL : ∀ X : Expr, RoseTree.label (Expr.lam X) = Label.lam := fun _ ↦ rfl
  have lamC : ∀ X : Expr, RoseTree.children (Expr.lam X) = [X] := fun _ ↦ rfl
  have r3 : ∀ e : Expr, ((e.rename Nat.succ).rename Nat.succ).rename Nat.succ = e.rename (· + 3) :=
    fun e ↦ by rw [rename_rename, rename_rename]; rfl
  rw [r3, rename_lam] at ha₁ hb₁
  simp only [lamL, lamC] at ha₁ hb₁
  -- the function at the variables of the left and the right sides
  rw [show (RoseTree.node (Label.app (Head.var 2)) [] : Expr) = Expr.var 2 [] from rfl,
    hsub_var_base hApp (liftR (· + 3)) (fun i ↦ match i with | 0 => 2 | i + 1 => i + 3) rfl
      (fun _ ↦ rfl) rfl, Option.some.injEq] at ha₁
  rw [show (RoseTree.node (Label.app (Head.var 1)) [] : Expr) = Expr.var 1 [] from rfl,
    hsub_var_base hApp (liftR (· + 3)) (fun i ↦ match i with | 0 => 1 | i + 1 => i + 3) rfl
      (fun _ ↦ rfl) rfl, Option.some.injEq] at hb₁
  subst ha₁ hb₁
  -- the left side substituted, at the left side's variable, and past the right side's
  rw [rename_succ_two, hsub_hole hXa (τ := fun i ↦ match i with | 0 => 2 | i + 1 => i + 3)
    (σ := (· + 2)) rfl fun i ↦ ⟨show i + 3 ≠ 2 by omega,
      show renumber 2 (i + 3) = i + 2 by simp only [renumber]; split_ifs <;> omega⟩,
    Option.some.injEq] at ha₂
  rw [hsubWith_vacuous' _ _ _ (j := 2) (g := fun i ↦ match i with | 0 => 1 | i + 1 => i + 2)
    fun i ↦ by rcases i with _ | i <;> rfl, Option.some.injEq] at hb₂
  subst ha₂ hb₂
  -- the right side substituted, past the left side's value, and at the right side's variable
  rw [hsubWith_vacuous' _ _ _ (j := 1) (g := Nat.succ) fun i ↦ by rcases i with _ | i <;> rfl,
    Option.some.injEq] at ha₃
  rw [hsub_hole hXb (τ := fun i ↦ match i with | 0 => 1 | i + 1 => i + 2) (σ := Nat.succ) rfl
    fun i ↦ ⟨show i + 2 ≠ 1 by omega,
      show renumber 1 (i + 2) = i + 1 by simp only [renumber]; split_ifs <;> omega⟩,
    Option.some.injEq] at hb₃
  subst ha₃ hb₃
  rw [hsubWith_shift, Option.some.injEq] at ha₄ hb₄
  subst ha₄ hb₄
  simp only [node_inj, List.cons.injEq, and_true, true_and] at hF
  subst hF
  -- the decodings
  obtain ⟨sfb, hsfb, hfbt⟩ := termOf_typed hk hsg (hc.toTmCtx.consTm hxa) (encTy_add hxb) hfb
  obtain ⟨sa, hsa, hat⟩ := termOf_typed hk hsg hc.toTmCtx hxa ha
  obtain ⟨sb, hsb, hbt⟩ := termOf_typed hk hsg hc.toTmCtx hxa hb
  have hXa' := termOf_hsub₀ hXa hsfb hsa
  have hXb' := termOf_hsub₀ hXb hsfb hsb
  -- the function at the left side is a term of the codomain, by the substitution theorem
  obtain ⟨e', he', he'J⟩ := (substAt_reduceAt hsg.ok (Expr.erase (tm A))).1 ΓLF (tm A) a rfl
    (by simp only [tm, Expr.const, Expr.app, typeShape_node]; rfl) ha fb [] []
    (.check (tm (B.rename Nat.succ))) (.check (tm B)) (by simpa using hΓs)
    (fun _ h ↦ by cases h; simp only [tm, Expr.const, Expr.app, typeShape_node]; rfl) rfl hfb
    (by simp only [substMode, List.length_nil]
        rw [hsub_eq, ← tm_rename, hsubWith_succ₀]; rfl)
  obtain rfl : Xa = e' := (Option.some.inj (he'.symm.trans (by
    rw [hsub_eq, show Expr.erase (tm A) = RoseTree.node (SimpleLabel.base 6) [] from rfl,
      reduce_node, List.length_nil, show a.rename (· + 0) = a from rename_id a]
    exact hXa))).symm
  obtain ⟨sXa, hsXa, hXat⟩ := termOf_typed hk hsg hc.toTmCtx hxb he'J
  obtain rfl := Option.some.inj (hsXa.symm.trans hXa')
  change termOf k env (Expr.const 16 [B, Xa, Xb]) = some φ at hφ
  simp only [termOf_const, List.map_cons, List.map_nil, decStep, dec_tmIdx, hXa', hXb',
    Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at hφ
  subst hφ
  have heq : termOf k env (Expr.const 16 [A, a, b]) = some (Term.eq sa sb) := by
    simp only [termOf_const, List.map_cons, List.map_nil, decStep, dec_tmIdx, hsa, hsb,
      Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  obtain ⟨Dh, hDh, hch⟩ := ihh _ _ _ _ _ _ hc hdh heq
  have hX := varLeaves_of_typeIn hXat
  have hpt : typeIn G n (xa :: Γ) (congMotive sfb sa) = some FreeTopos.omega :=
    typeIn_eq (typeIn_weaken1 hXat) hfbt
  have hmot : ∀ u, Term.subst (congMotive sfb sa) (instVar u) =
      Term.eq (Term.subst sfb (instVar sa)) (Term.subst sfb (instVar u)) := fun u ↦ by
    rw [← subst_weaken1_instVar hX u]
    rfl
  have hcp := check_leibD (hIxa) hpt hat hbt hch
    (Dp := joinD reflD reflD) (by rw [hmot]; exact check_join (check_refl _) (check_refl _))
  rw [hmot] at hcp
  refine ⟨_, ?_, hcp⟩
  rw [decPf_const]
  simp only [List.map_cons, List.map_nil, decPfStep.eq_def, termOf_lam, hsfb, hsa, hsb, hDh,
    decTy_encTy _ xa A hxa, Option.map_some, Option.bind_eq_bind, Option.bind_some, lamBody_lam,
    Option.pure_def]

include hk hsg in
/-- The soundness of the decoding of induction on the natural numbers. -/
theorem sound_natInd (hc : PfCtx G k n ΓLF env Γ Φ) {P d₀ ds N F : Expr} {φ : MTerm}
    (ih₀ : PfSoundAt sg G k E n d₀)
    (ihs : PfLam sg (fun b ↦ PfLam sg (PfSoundAt sg G k E n) b) ds)
    (hS : spine ΓLF (Expr.pi (Expr.arrow (tm nat) (tm omega))
      (Expr.arrow (pf (Expr.var 0 [zero]))
        (Expr.arrow (Expr.pi (tm nat) (Expr.arrow (pf (Expr.var 1 [v 0]))
            (pf (Expr.var 1 [succ (v 0)]))))
          (Expr.pi (tm nat) (pf (Expr.var 1 [v 0]))))))
      [(P, judge sg P), (d₀, judge sg d₀), (ds, judge sg ds), (N, judge sg N)] =
        some (pf F))
    (hφ : termOf k env F = some φ) :
    ∃ D, decPf k (Expr.const 29 [P, d₀, ds, N]) env Φ.length = some D ∧
      (check G E n D).2 Γ Φ φ = true := by
  simp only [tm, pf, nat, omega, zero, zeroAt, star, succ, Expr.const, Expr.app] at hS
  lf_spine_at hS [Option.bind_eq_some_iff]
  obtain ⟨a, a₁, b, a₂, ⟨hP, ha, ha₁, hb, ha₂⟩, a₃, b₁, a₄, ⟨hd₀, ha₃, hb₁, ha₄⟩, a', ⟨hds, ha'⟩,
    hn, a₅, ha₅, hF⟩ := hS
  obtain ⟨Pb, rfl, hPb⟩ := judge_check_pi_inv hP
  simp only [Expr.lam, rename_node, RoseTree.label_node, RoseTree.children_node, List.zipIdx,
    List.map_cons, List.map_nil, Label.binders, Function.iterate_one, Label.rename] at ha ha₁ hb ha₂
  rw [rename_rename] at ha₁ hb₁ ha₄
  rw [rename_rename, rename_rename] at hb ha₂
  have hΓs := fun a ha ↦ (hc.typeShape a ha).1
  have hOs : ModeShape (.check (tm omega)) = true := by
    simp only [ModeShape, tm, Expr.const, Expr.app, typeShape_node]; rfl
  have hnatc : nat.FreeBelow 0 = true := rfl
  have hApp := appliedAt_of_judge_tm hsg hΓs hOs hPb
  -- the motive at the step's variable, the type of the step's hypothesis
  obtain rfl := Option.some.inj (ha₁.symm.trans (hsub_var_base hApp
    (liftR Nat.succ ∘ liftR Nat.succ) (liftR Nat.succ) rfl (fun _ ↦ rfl) rfl))
  obtain rfl := Option.some.inj (ha₃.symm.trans
    (hsubWith_vacuous' _ _ _ (j := 1) (g := id) fun _ ↦ rfl))
  -- the motive at the conclusion's variable
  obtain rfl := Option.some.inj (ha₂.symm.trans (hsub_var_base hApp
    ((liftR Nat.succ ∘ liftR Nat.succ) ∘ liftR Nat.succ)
    (fun i ↦ match i with | 0 => 0 | k + 1 => k + 3) rfl (fun _ ↦ rfl) rfl))
  obtain rfl := Option.some.inj (ha₄.symm.trans (hsubWith_vacuous' _ _ _ (j := 2)
    (g := liftR Nat.succ) fun i ↦ by rcases i with _ | i <;> rfl))
  obtain rfl := Option.some.inj (ha'.symm.trans
    (hsubWith_vacuous' _ _ _ (j := 1) (g := id) fun _ ↦ rfl))
  -- the motive at the successor of the step's variable, the step's conclusion
  have hR2 : CtxRen ΓLF (tm nat :: tm nat :: ΓLF) (Nat.succ ∘ Nat.succ) := fun i T hT ↦ by
    have h₂ := CtxRen.succ (tm nat :: ΓLF) (tm nat) _ _ (CtxRen.succ ΓLF (tm nat) i T hT)
    rwa [rename_rename] at h₂
  have hPb2 := judge_rename (Sig.ok_closed hsg.ok) Pb _ (CtxRen.lift hR2 (tm nat)) hPb
  rw [Mode.rename, show Expr.rename (RoseTree.node (.app (.const 6))
    [RoseTree.node (.app (.const 4)) []]) (liftR (Nat.succ ∘ Nat.succ)) = tm omega from
      rename_closed (tm_closed rfl) _] at hPb2
  have hΓs2 : ∀ x ∈ tm nat :: tm nat :: ΓLF, Expr.TypeShape x = true := fun x hx ↦ by
    simp only [List.mem_cons] at hx
    rcases hx with rfl | rfl | hx
    · simp only [tm, Expr.const, Expr.app, typeShape_node]; rfl
    · simp only [tm, Expr.const, Expr.app, typeShape_node]; rfl
    · exact hΓs x hx
  have hApp2 := appliedAt_of_judge_tm hsg hΓs2 hOs hPb2
  obtain ⟨Y, hY⟩ := hsubWith_base_total 6 _ (Expr.const 14 [Expr.var 1 []]) 0 hApp2
  have hred : RenameCompat (reduceStep (SimpleLabel.base 6) []) := by
    rw [← show reduce (RoseTree.node (SimpleLabel.base 6) []) =
      reduceStep (SimpleLabel.base 6) [] from reduce_node _ _]
    exact reduce_rename _
  have hbY := hsubWith_rename hred _ _ 0 (liftR^[2] Nat.succ) Y hY
  rw [rename_rename, show liftR^[0 + 1] (liftR^[2] Nat.succ) ∘ liftR (Nat.succ ∘ Nat.succ) =
    (liftR Nat.succ ∘ liftR Nat.succ) ∘ liftR Nat.succ from
      funext fun i ↦ by rcases i with _ | i <;> rfl] at hbY
  obtain rfl := Option.some.inj (hb.symm.trans hbY)
  rw [Function.iterate_zero_apply, hsubWith_vacuous, Option.some.injEq] at hb₁
  subst hb₁
  simp only [node_inj, List.cons.injEq, and_true, true_and] at hF
  subst hF
  -- the decodings
  obtain ⟨sp, hsp, hpt⟩ := termOf_typed (a := FreeTopos.omega) hk hsg
    (hc.toTmCtx.consTm (a := FreeTopos.nat) rfl) rfl hPb
  obtain ⟨sn, hsn, hnt⟩ := termOf_typed (a := FreeTopos.nat) hk hsg hc.toTmCtx rfl hn
  have hid : termOf k (none :: env) (Pb.rename id) = some sp := by
    rw [termOf, rename_rename]
    exact hsp
  obtain rfl := Option.some.inj (hφ.symm.trans (termOf_hsub₀ ha₅ hid hsn))
  have hzero : termOf k env (Expr.const 13 [Expr.const 7 []]) =
      some (Term.arr k.zero [] Term.star) := by
    simp only [termOf_const, List.map_cons, List.map_nil, decStep, dec_tmIdx, Option.map_eq_map,
      Option.map_some]
  have ha0 := termOf_hsub₀ ha hsp hzero
  have hlen : (Φ.map weaken1 ++ [truth]).length = Φ.length + 1 := by
    rw [List.length_append, List.length_map, List.length_singleton]
  have hc₂ := ((hc.consTm (a := FreeTopos.nat) (A := nat) rfl).addHyp
    (typeIn_truth (G := G) (Γ := FreeTopos.nat :: Γ))).consPf hid hpt
  rw [hlen] at hc₂
  have hY' : termOf k (some (Φ.length + 1) :: none :: env) Y =
      some (FreeTopos.Internal.natSuccAt k.succ sp) := by
    have h₁ : termOf k (none :: some (Φ.length + 1) :: none :: env)
        (Pb.rename (liftR (Nat.succ ∘ Nat.succ))) = some (Term.rename sp (liftR Nat.succ)) := by
      have := dec_rename _ (numTm (none :: env)) (numTm (none :: env) + 1) (liftR Nat.succ) sp
        hsp (by numTm_ren)
      rw [rename_rename] at this
      rw [termOf, rename_rename, show tmIdx (none :: some (Φ.length + 1) :: none :: env) ∘
        liftR (Nat.succ ∘ Nat.succ) = liftR Nat.succ ∘ tmIdx (none :: env) from
          funext fun i ↦ by rcases i with _ | i <;> rfl]
      exact this
    have h₂ : termOf k (some (Φ.length + 1) :: none :: env)
        (Expr.const 14 [Expr.var 1 []]) = some (Term.arr k.succ [] (Term.var 0)) := rfl
    rw [termOf_hsub₀ hY h₁ h₂, FreeTopos.Internal.natSuccAt,
      Term.subst_rename sp _ _ (FreeTopos.Internal.atVar0 (Term.arr k.succ [] (Term.var 0)))
        fun i ↦ by rcases i with _ | i <;> rfl]
  obtain ⟨D₀, hD₀, hc₀⟩ := ih₀ _ _ _ _ _ _ (hc.addHyp typeIn_truth) hd₀ ha0
  rw [List.length_append, List.length_singleton] at hD₀
  obtain ⟨body₁, rfl, hb1, hlam⟩ := ihs ΓLF _ _ hds
  obtain ⟨body₂, rfl, hb2, hsound⟩ := hlam _ _ _ hb1
  obtain ⟨Ds, hDs, hcs⟩ := hsound _ _ _ _ _ _ hc₂ hb2 hY'
  have hDs' : decPf k body₂ (some (Φ.length + 1) :: none :: env) (Φ.length + 2) =
      some Ds := by
    rw [List.length_append, hlen, List.length_singleton] at hDs
    exact hDs
  refine ⟨indD FreeTopos.nat (.natIndHyp k.zero k.succ) sp sn Φ.length [D₀, Ds], ?_,
    check_natIndD hk.zero hk.succ hpt hnt hc.typed hc₀ hcs⟩
  rw [decPf_const]
  simp only [List.map_cons, List.map_nil, decPfStep.eq_def, termOf_lam, hsp, hsn, hD₀, decPf_lam,
    hDs', Option.map_some, Option.bind_eq_bind, Option.bind_some, lamBody,
    Term.lam, RoseTree.label_node, RoseTree.children_node, Option.pure_def]

include hk hsg in
/-- The soundness of the decoding of induction on lists. -/
theorem sound_listInd (hc : PfCtx G k n ΓLF env Γ Φ) {A P d₀ ds l F : Expr} {φ : MTerm}
    (ih₀ : PfSoundAt sg G k E n d₀)
    (ihs : PfLam sg (fun b ↦ PfLam sg (fun b' ↦ PfLam sg (PfSoundAt sg G k E n) b') b) ds)
    (hS : spine ΓLF (Expr.pi tp (Expr.pi (Expr.arrow (tm (list (v 0))) (tm omega))
      (Expr.arrow (pf (Expr.var 0 [nil (v 1)]))
        (Expr.arrow (Expr.pi (tm (v 1)) (Expr.pi (tm (list (v 2)))
            (Expr.arrow (pf (Expr.var 2 [v 0]))
              (pf (Expr.var 2 [cons (v 3) (pair (v 3) (list (v 3)) (v 1) (v 0))])))))
          (Expr.pi (tm (list (v 1))) (pf (Expr.var 1 [v 0])))))))
      [(A, judge sg A), (P, judge sg P), (d₀, judge sg d₀), (ds, judge sg ds),
        (l, judge sg l)] = some (pf F))
    (hφ : termOf k env F = some φ) :
    ∃ D, decPf k (Expr.const 36 [A, P, d₀, ds, l]) env Φ.length = some D ∧
      (check G E n D).2 Γ Φ φ = true := by
  obtain ⟨xa, hxa, hIxa⟩ := tyComplete hsg hc.heads₀ A (spine_tp₁ hS)
  simp only [tm, tp, pf, list, omega, nil, nilAt, star, cons, pair, Expr.const, Expr.app] at hS
  lf_spine_open_at hS [Option.bind_eq_some_iff]
  obtain ⟨-, a, a₁, b, a₂, ⟨hP, ha, ha₁, hb, ha₂⟩, a₃, b₁, a₄, ⟨hd₀, ha₃, hb₁, ha₄⟩, a', ⟨hds, ha'⟩,
    hl, a₅, ha₅, hF⟩ := hS
  obtain ⟨Pb, rfl, hPb⟩ := judge_check_pi_inv hP
  simp only [Expr.lam, rename_node, RoseTree.label_node, RoseTree.children_node, List.zipIdx,
    List.map_cons, List.map_nil, Label.binders, Function.iterate_one, Label.rename] at ha ha₁ hb ha₂
  rw [rename_rename, rename_rename] at ha₁ ha₂
  rw [rename_rename, rename_rename, rename_rename] at hb
  have hΓs := fun a ha ↦ (hc.typeShape a ha).1
  have hOs : ModeShape (.check (tm omega)) = true := by
    simp only [ModeShape, tm, Expr.const, Expr.app, typeShape_node]; rfl
  have hla : encTy k env.length (FreeTopos.list xa) = some (list A) := by rw [encTy_list, hxa]; rfl
  have hApp := appliedAt_of_judge_tm hsg hΓs hOs hPb
  -- the motive at the step's rest, the type of the step's hypothesis
  obtain rfl := Option.some.inj (ha₁.symm.trans (hsub_var_base hApp
    ((liftR Nat.succ ∘ liftR Nat.succ) ∘ liftR Nat.succ)
    (fun i ↦ match i with | 0 => 0 | i + 1 => i + 3) rfl (fun _ ↦ rfl) rfl))
  obtain rfl := Option.some.inj (ha₃.symm.trans (hsubWith_vacuous' _ _ _ (j := 2)
    (g := liftR Nat.succ) fun i ↦ by rcases i with _ | i <;> rfl))
  -- the motive at the conclusion's variable
  obtain rfl := Option.some.inj (ha₂.symm.trans (hsub_var_base hApp
    ((liftR Nat.succ ∘ liftR Nat.succ) ∘ liftR Nat.succ)
    (fun i ↦ match i with | 0 => 0 | i + 1 => i + 3) rfl (fun _ ↦ rfl) rfl))
  obtain rfl := Option.some.inj (ha₄.symm.trans (hsubWith_vacuous' _ _ _ (j := 2)
    (g := liftR Nat.succ) fun i ↦ by rcases i with _ | i <;> rfl))
  obtain rfl := Option.some.inj (ha'.symm.trans
    (hsubWith_vacuous' _ _ _ (j := 1) (g := id) fun _ ↦ rfl))
  -- the motive at the construction of the step's element and rest, the step's conclusion
  have hR3 : CtxRen ΓLF (tm (list A) :: tm (list A) :: tm (list A) :: ΓLF)
      (Nat.succ ∘ Nat.succ ∘ Nat.succ) := fun i T hT ↦ by
    have h₁ := CtxRen.succ ΓLF (tm (list A)) i T hT
    have h₂ := CtxRen.succ (tm (list A) :: ΓLF) (tm (list A)) _ _ h₁
    have h₃ := CtxRen.succ (tm (list A) :: tm (list A) :: ΓLF) (tm (list A)) _ _ h₂
    rwa [rename_rename, rename_rename] at h₃
  have hPb3 := judge_rename (Sig.ok_closed hsg.ok) Pb _ (CtxRen.lift hR3 (tm (list A))) hPb
  rw [Mode.rename, show Expr.rename (RoseTree.node (.app (.const 6))
    [RoseTree.node (.app (.const 4)) []]) (liftR (Nat.succ ∘ Nat.succ ∘ Nat.succ)) = tm omega from
      rename_closed (tm_closed rfl) _, tm_rename] at hPb3
  have hΓs3 : ∀ x ∈ tm (list A) :: tm (list A) :: tm (list A) :: ΓLF, Expr.TypeShape x = true :=
    fun x hx ↦ by
      simp only [List.mem_cons] at hx
      rcases hx with rfl | rfl | rfl | hx
      · simp only [tm, Expr.const, Expr.app, typeShape_node]; rfl
      · simp only [tm, Expr.const, Expr.app, typeShape_node]; rfl
      · simp only [tm, Expr.const, Expr.app, typeShape_node]; rfl
      · exact hΓs x hx
  have hApp3 := appliedAt_of_judge_tm hsg hΓs3 hOs hPb3
  obtain ⟨Y, hY⟩ := hsubWith_base_total 6 _
    (Expr.const 32 [((A.rename Nat.succ).rename Nat.succ).rename Nat.succ,
      Expr.const 8 [((A.rename Nat.succ).rename Nat.succ).rename Nat.succ,
      Expr.const 30 [((A.rename Nat.succ).rename Nat.succ).rename Nat.succ], Expr.var 2 [],
        Expr.var 1 []]]) 0 hApp3
  have hred : RenameCompat (reduceStep (SimpleLabel.base 6) []) := by
    rw [← show reduce (RoseTree.node (SimpleLabel.base 6) []) =
      reduceStep (SimpleLabel.base 6) [] from reduce_node _ _]
    exact reduce_rename _
  have hbY := hsubWith_rename hred _ _ 0 (liftR^[3] Nat.succ) Y hY
  rw [rename_rename, show liftR^[0 + 1] (liftR^[3] Nat.succ) ∘
      liftR (Nat.succ ∘ Nat.succ ∘ Nat.succ) =
    ((liftR Nat.succ ∘ liftR Nat.succ) ∘ liftR Nat.succ) ∘ liftR Nat.succ from
      funext fun i ↦ by rcases i with _ | i <;> rfl] at hbY
  have hn3 : (Expr.const 32 [((A.rename Nat.succ).rename Nat.succ).rename Nat.succ,
    Expr.const 8 [((A.rename Nat.succ).rename Nat.succ).rename Nat.succ,
      Expr.const 30 [((A.rename Nat.succ).rename Nat.succ).rename Nat.succ], Expr.var 2 [],
      Expr.var 1 []]]).rename (liftR^[0] (liftR^[3] Nat.succ)) =
      Expr.const 32 [(((A.rename Nat.succ).rename Nat.succ).rename Nat.succ).rename Nat.succ,
        Expr.const 8 [(((A.rename Nat.succ).rename Nat.succ).rename Nat.succ).rename Nat.succ,
          Expr.const 30 [(((A.rename Nat.succ).rename Nat.succ).rename Nat.succ).rename Nat.succ],
            Expr.var 2 [],
          Expr.var 1 []]] := by
    simp only [Function.iterate_zero, id, Expr.const, Expr.var, Expr.app, rename_app_node,
      List.map_cons, List.map_nil, Head.rename, rename_rename]
    rfl
  rw [hn3] at hbY
  obtain rfl := Option.some.inj (hb.symm.trans hbY)
  rw [Function.iterate_zero_apply, hsubWith_vacuous, Option.some.injEq] at hb₁
  subst hb₁
  simp only [node_inj, List.cons.injEq, and_true, true_and] at hF
  subst hF
  -- the decodings
  obtain ⟨sp, hsp,
    hpt⟩ := termOf_typed (a := FreeTopos.omega) hk hsg (hc.toTmCtx.consTm hla) rfl hPb
  obtain ⟨sl, hsl, hlt⟩ := termOf_typed hk hsg hc.toTmCtx hla hl
  have hid : termOf k (none :: env) (Pb.rename id) = some sp := by
    rw [termOf, rename_rename]
    exact hsp
  obtain rfl := Option.some.inj (hφ.symm.trans (termOf_hsub₀ ha₅ hid hsl))
  have hnil : termOf k env (Expr.const 31 [A, Expr.const 7 []]) =
      some (Term.arr k.nil [xa] Term.star) := by
    simp only [termOf_const, List.map_cons, List.map_nil, decStep, dec_tmIdx, decTy_tmIdx hxa,
      Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  have ha0 := termOf_hsub₀ ha hsp hnil
  -- the motive at the rest, under the element: the motive weakened past the element
  have hPb1 := judge_rename (Sig.ok_closed hsg.ok) Pb _
    (CtxRen.lift (CtxRen.succ ΓLF (tm A)) (tm (list A))) hPb
  rw [Mode.rename, show Expr.rename (RoseTree.node (.app (.const 6))
    [RoseTree.node (.app (.const 4)) []]) (liftR Nat.succ) = tm omega from
      rename_closed (tm_closed rfl) _, tm_rename] at hPb1
  obtain ⟨sq, hsq, hqt⟩ := termOf_typed (a := FreeTopos.omega) hk hsg
    ((hc.toTmCtx.consTm hxa).consTm (encTy_succ hla)) rfl hPb1
  have hsq' : termOf k (none :: none :: env) (Pb.rename (liftR Nat.succ)) =
      some (FreeTopos.Internal.weakenElem sp) :=
    termOf_rename _ _ hsp (fun i ↦ by rcases i with _ | i <;> rfl) (by numTm_ren)
  obtain rfl := Option.some.inj (hsq.symm.trans hsq')
  have hc₂ := (((hc.consTm hxa).consTm (encTy_succ hla)).addHyp
    (typeIn_truth (G := G) (Γ := FreeTopos.list xa :: xa :: Γ))).consPf hsq' hqt
  have hlen : ((Φ.map weaken1).map weaken1 ++ [truth]).length = Φ.length + 1 := by
    rw [List.length_append, List.length_map, List.length_map, List.length_singleton]
  rw [hlen] at hc₂
  -- the motive at the construction, the step's conclusion
  have hY' : termOf k (some (Φ.length + 1) :: none :: none :: env) Y =
      some (FreeTopos.Internal.listConsAt k.cons xa sp) := by
    have h₁ : termOf k (none :: some (Φ.length + 1) :: none :: none :: env)
        (Pb.rename (liftR (Nat.succ ∘ Nat.succ ∘ Nat.succ))) =
        some (Term.rename sp (liftR (· + 2))) :=
      termOf_rename _ _ hsp (fun i ↦ by rcases i with _ | i <;> rfl) (by numTm_ren)
    have h₂ : termOf k (some (Φ.length + 1) :: none :: none :: env)
        (Expr.const 32 [((A.rename Nat.succ).rename Nat.succ).rename Nat.succ,
          Expr.const 8 [((A.rename Nat.succ).rename Nat.succ).rename Nat.succ,
          Expr.const 30 [((A.rename Nat.succ).rename Nat.succ).rename Nat.succ], Expr.var 2 [],
            Expr.var 1 []]]) =
        some (Term.arr k.cons [xa] (Term.pair (Term.var 1) (Term.var 0))) := by
      simp only [termOf_const, List.map_cons, List.map_nil, decStep, dec_tmIdx,
        decTy_tmIdx (env := some (Φ.length + 1) :: none :: none :: env)
          (encTy_succ (encTy_succ (encTy_succ hxa))),
        Option.bind_eq_bind, Option.bind_some, Option.pure_def]
      rfl
    rw [termOf_hsub₀ hY h₁ h₂]
    exact congrArg some (Term.subst_rename sp _ _ _ fun i ↦ by rcases i with _ | i <;> rfl)
  obtain ⟨D₀, hD₀, hc₀⟩ := ih₀ _ _ _ _ _ _ (hc.addHyp typeIn_truth) hd₀ ha0
  rw [List.length_append, List.length_singleton] at hD₀
  obtain ⟨body₁, rfl, hb1, hlam⟩ := ihs ΓLF _ _ hds
  obtain ⟨body₂, rfl, hb2, hlam'⟩ := hlam _ _ _ hb1
  obtain ⟨body₃, rfl, hb3, hsound⟩ := hlam' _ _ _ hb2
  obtain ⟨Ds, hDs, hcs⟩ := hsound _ _ _ _ _ _ hc₂ hb3 hY'
  have hDs' : decPf k body₃ (some (Φ.length + 1) :: none :: none :: env) (Φ.length + 2) =
      some Ds := by
    rw [List.length_append, hlen, List.length_singleton] at hDs
    exact hDs
  have hw : (Φ ++ [truth]).map FreeTopos.Internal.weaken2 =
      (Φ.map weaken1).map weaken1 ++ [truth] := by
    rw [List.map_append, List.map_map]
    refine congrArg₂ _ (List.map_congr_left fun φ _ ↦ ?_) rfl
    exact (Term.rename_rename φ _ _ _ fun _ ↦ rfl).symm
  have hIs : FreeTopos.Internal.IsTy G n (FreeTopos.list xa) = true := by
    rw [FreeTopos.Internal.isTy_list]; exact hIxa
  refine ⟨indD (FreeTopos.list xa) (.listIndHyp k.nil k.cons) sp sl Φ.length [D₀, Ds], ?_,
    check_listIndD hk.nil hk.cons hIs hpt hlt hc.typed hc₀ (by rw [hw]; exact hcs)⟩
  rw [decPf_const]
  simp only [List.map_cons, List.map_nil, decPfStep.eq_def, termOf_lam, hsp, hsl, hD₀, decPf_lam,
    hDs',
    decTy_encTy _ xa A hxa, Option.map_some, Option.bind_eq_bind, Option.bind_some, lamBody_lam,
    Option.pure_def]

include hk hsg in
/-- The soundness of the decoding of induction on rose trees. -/
theorem sound_roseInd (hc : PfCtx G k n ΓLF env Γ Φ) {P ds t F : Expr} {φ : MTerm}
    (ihs : PfLam sg (fun b ↦ PfLam sg (fun b' ↦ PfLam sg (PfSoundAt sg G k E n) b') b) ds)
    (hS : spine ΓLF (Expr.pi (Expr.arrow (tm rose) (tm omega))
      (Expr.arrow (Expr.pi (tm nat) (Expr.pi (tm (list rose))
          (Expr.arrow (pf (eq (list omega)
              (listRec rose (list omega) (nil omega) (Expr.lam (Expr.lam (cons omega
                (pair omega (list omega) (Expr.var 4 [v 1]) (v 0))))) (v 0))
              (listRec rose (list omega) (nil omega) (Expr.lam (Expr.lam (cons omega
                (pair omega (list omega) (eq one star star) (v 0))))) (v 0))))
            (pf (Expr.var 2 [node (pair nat (list rose) (v 1) (v 0))])))))
        (Expr.pi (tm rose) (pf (Expr.var 1 [v 0])))))
      [(P, judge sg P), (ds, judge sg ds), (t, judge sg t)] = some (pf F))
    (hφ : termOf k env F = some φ) :
    ∃ D, decPf k (Expr.const 41 [P, ds, t]) env Φ.length = some D ∧
      (check G E n D).2 Γ Φ φ = true := by
  simp only [tm, pf, eq, listRec, nil, nilAt, cons, pair, list, nat, rose, omega, one, star, node,
    Expr.const, Expr.app] at hS
  lf_spine_at hS [Option.bind_eq_some_iff]
  obtain ⟨a, b, a₁, ⟨hP, ha, hb, ha₁⟩, a₂, ⟨hds, ha₂⟩, ht, a₃, ha₃, hF⟩ := hS
  obtain ⟨Pb, rfl, hPb⟩ := judge_check_pi_inv hP
  have hΓs := fun a ha ↦ (hc.typeShape a ha).1
  have hOs : ModeShape (.check (tm omega)) = true := by
    simp only [ModeShape, tm, Expr.const, Expr.app, typeShape_node]; rfl
  have hApp := appliedAt_of_judge_tm (A := rose) hsg hΓs hOs hPb
  have lamL : ∀ X : Expr, RoseTree.label (Expr.lam X) = Label.lam := fun _ ↦ rfl
  have lamC : ∀ X : Expr, RoseTree.children (Expr.lam X) = [X] := fun _ ↦ rfl
  have v₁ : (RoseTree.node (Label.app (Head.var 1)) [] : Expr) = Expr.var 1 [] := rfl
  have v₀ : (RoseTree.node (Label.app (Head.var 0)) [] : Expr) = Expr.var 0 [] := rfl
  have r3 : ∀ e : Expr, ((e.rename Nat.succ).rename Nat.succ).rename Nat.succ = e.rename (· + 3) :=
    fun e ↦ by rw [rename_rename, rename_rename]; rfl
  rw [rename_succ_four, rename_lam] at ha
  rw [r3, rename_lam] at hb
  rw [rename_succ_two, rename_lam] at ha₁
  simp only [lamL, lamC] at ha hb ha₁
  -- the motive at each child, in the hypothesis
  rw [v₁, hsub_var_base hApp (liftR (· + 4)) (fun i ↦ match i with | 0 => 1 | i + 1 => i + 4) rfl
    (fun _ ↦ rfl) rfl, Option.some.injEq] at ha
  subst ha
  -- the motive at the conclusion's variable
  rw [v₀, hsub_var_base hApp (liftR (· + 2)) (liftR (· + 1)) rfl (fun _ ↦ rfl) (k := 0) rfl,
    Option.some.injEq] at ha₁
  subst ha₁
  rw [hsubWith_vacuous' _ _ _ (g := id) fun i ↦ by rcases i with _ | i <;> rfl, rename_id,
    Option.some.injEq] at ha₂
  subst ha₂
  simp only [node_inj, List.cons.injEq, and_true, true_and] at hF
  subst hF
  -- the decodings
  obtain ⟨sp, hsp, hpt⟩ := termOf_typed (a := FreeTopos.omega) hk hsg
    (hc.toTmCtx.consTm (a := FreeTopos.rose) rfl) rfl hPb
  obtain ⟨st, hst, htt⟩ := termOf_typed (a := FreeTopos.rose) hk hsg hc.toTmCtx rfl ht
  obtain rfl := Option.some.inj (hφ.symm.trans (termOf_hsub₀ ha₃ hsp hst))
  -- the hypothesis that the motive holds at each child
  have hS₄ : termOf k (none :: none :: none :: none :: env)
      (Pb.rename fun i ↦ match i with | 0 => 1 | i + 1 => i + 4) =
      some (Term.rename sp fun i ↦ match i with | 0 => 1 | i + 1 => i + 4) :=
    termOf_rename _ _ hsp (fun i ↦ by rcases i with _ | i <;> rfl) (by numTm_ren)
  have hH : termOf k (none :: none :: env) (Expr.const 16 [Expr.const 30 [Expr.const 4 []],
      Expr.const 33 [Expr.const 37 [], Expr.const 30 [Expr.const 4 []],
        Expr.const 31 [Expr.const 4 [], Expr.const 7 []],
        Expr.lam (Expr.lam (Expr.const 32 [Expr.const 4 [], Expr.const 8 [Expr.const 4 [],
          Expr.const 30 [Expr.const 4 []], Pb.rename fun i ↦ match i with | 0 => 1 | i + 1 => i + 4,
          Expr.var 0 []]])), Expr.var 0 []],
      Expr.const 33 [Expr.const 37 [], Expr.const 30 [Expr.const 4 []],
        Expr.const 31 [Expr.const 4 [], Expr.const 7 []],
        Expr.lam (Expr.lam (Expr.const 32 [Expr.const 4 [], Expr.const 8 [Expr.const 4 [],
          Expr.const 30 [Expr.const 4 []],
          Expr.const 16 [Expr.const 1 [], Expr.const 7 [], Expr.const 7 []], Expr.var 0 []]])),
        Expr.var 0 []]]) =
      some (FreeTopos.Internal.roseHyp k.nil k.cons sp) := by
    simp only [termOf_const, termOf_lam, List.map_cons, List.map_nil, decStep, dec_tmIdx, hS₄,
      Option.bind_eq_bind, Option.bind_some, Option.pure_def]
    rfl
  have hc₂ := (((hc.consTm (a := FreeTopos.nat) (A := nat) rfl).consTm
    (a := FreeTopos.list FreeTopos.rose) (A := list rose) rfl).addHyp
    (typeIn_truth (G := G) (Γ := FreeTopos.list FreeTopos.rose :: FreeTopos.nat :: Γ))).consPf
    hH (typeIn_roseHyp hk.nil hk.cons hpt)
  have hlen : ((Φ.map weaken1).map weaken1 ++ [truth]).length = Φ.length + 1 := by
    rw [List.length_append, List.length_map, List.length_map, List.length_singleton]
  rw [hlen] at hc₂
  -- the motive at the construction, the step's conclusion
  have hY' : termOf k (some (Φ.length + 1) :: none :: none :: env) b =
      some (FreeTopos.Internal.roseNodeAt k.node FreeTopos.rose FreeTopos.nat sp) := by
    have h₁ : termOf k (none :: some (Φ.length + 1) :: none :: none :: env)
        (Pb.rename (liftR (· + 3))) = some (Term.rename sp (liftR (· + 2))) :=
      termOf_rename _ _ hsp (fun i ↦ by rcases i with _ | i <;> rfl) (by numTm_ren)
    have h₂ : termOf k (some (Φ.length + 1) :: none :: none :: env)
        (Expr.const 38 [Expr.const 8 [Expr.const 5 [], Expr.const 30 [Expr.const 37 []],
          Expr.var 2 [], Expr.var 1 []]]) =
        some (Term.arr k.node [] (Term.pair (Term.var 1) (Term.var 0))) := rfl
    rw [termOf_hsub₀ hb h₁ h₂]
    refine congrArg some (Term.subst_rename sp _ _ _ fun i ↦ ?_)
    rcases i with _ | i
    · exact congrArg (Term.arr k.node · _) (if_pos rfl).symm
    · rfl
  obtain ⟨body₁, rfl, hb1, hlam⟩ := ihs ΓLF _ _ hds
  obtain ⟨body₂, rfl, hb2, hlam'⟩ := hlam _ _ _ hb1
  obtain ⟨body₃, rfl, hb3, hsound⟩ := hlam' _ _ _ hb2
  obtain ⟨Ds, hDs, hcs⟩ := hsound _ _ _ _ _ _ hc₂ hb3 hY'
  have hDs' : decPf k body₃ (some (Φ.length + 1) :: none :: none :: env) (Φ.length + 2) =
      some Ds := by
    rw [List.length_append, hlen, List.length_singleton] at hDs
    exact hDs
  have hw : (Φ ++ [truth]).map FreeTopos.Internal.weaken2 =
      (Φ.map weaken1).map weaken1 ++ [truth] := by
    rw [List.map_append, List.map_map]
    refine congrArg₂ _ (List.map_congr_left fun φ _ ↦ ?_) rfl
    exact (Term.rename_rename φ _ _ _ fun _ ↦ rfl).symm
  refine ⟨indD FreeTopos.rose (.roseIndHyp k.node k.nil k.cons) sp st Φ.length [Ds], ?_,
    check_roseIndD roseParts_rose (.inl ⟨hk.node, rfl⟩) hk.nil hk.cons
      FreeTopos.Internal.isTy_rose hpt htt hc.typed (by rw [hw]; exact hcs)⟩
  rw [decPf_const]
  simp only [List.map_cons, List.map_nil, decPfStep.eq_def, termOf_lam, hsp, hst, decPf_lam, hDs',
    Option.map_some, Option.bind_eq_bind, Option.bind_some, lamBody_lam, Option.pure_def]

include hk hsg in
/-- The soundness of the decoding of induction on rose trees of labels of a type. -/
theorem sound_lroseInd (hc : PfCtx G k n ΓLF env Γ Φ) {A P ds t F : Expr} {φ : MTerm}
    (ihs : PfLam sg (fun b ↦ PfLam sg (fun b' ↦ PfLam sg (PfSoundAt sg G k E n) b') b) ds)
    (hS : spine ΓLF (Expr.pi tp (Expr.pi (Expr.arrow (tm (lrose (v 0))) (tm omega))
      (Expr.arrow (Expr.pi (tm (v 1)) (Expr.pi (tm (list (lrose (v 2))))
          (Expr.arrow (pf (eq (list omega)
              (listRec (lrose (v 3)) (list omega) (nil omega) (Expr.lam (Expr.lam (cons omega
                (pair omega (list omega) (Expr.var 4 [v 1]) (v 0))))) (v 0))
              (listRec (lrose (v 3)) (list omega) (nil omega) (Expr.lam (Expr.lam (cons omega
                (pair omega (list omega) (eq one star star) (v 0))))) (v 0))))
            (pf (Expr.var 2 [lnode (v 3) (pair (v 3) (list (lrose (v 3))) (v 1) (v 0))])))))
        (Expr.pi (tm (lrose (v 1))) (pf (Expr.var 1 [v 0]))))))
      [(A, judge sg A), (P, judge sg P), (ds, judge sg ds), (t, judge sg t)] = some (pf F))
    (hφ : termOf k env F = some φ) :
    ∃ D, decPf k (Expr.const 46 [A, P, ds, t]) env Φ.length = some D ∧
      (check G E n D).2 Γ Φ φ = true := by
  obtain ⟨xa, hxa, hIxa⟩ := tyComplete hsg hc.heads₀ A (spine_tp₁ hS)
  have hra : encTy k env.length (FreeTopos.lrose xa) = some (lrose A) := by
    rw [encTy_lrose, hxa]; rfl
  simp only [tm, tp, pf, eq, listRec, nil, nilAt, cons, pair, list, lrose, omega, one, star, lnode,
    Expr.const, Expr.app] at hS
  lf_spine_open_at hS [Option.bind_eq_some_iff]
  obtain ⟨-, a, b, a₁, ⟨hP, ha, hb, ha₁⟩, a₂, ⟨hds, ha₂⟩, ht, a₃, ha₃, hF⟩ := hS
  obtain ⟨Pb, rfl, hPb⟩ := judge_check_pi_inv hP
  have hΓs := fun a ha ↦ (hc.typeShape a ha).1
  have hOs : ModeShape (.check (tm omega)) = true := by
    simp only [ModeShape, tm, Expr.const, Expr.app, typeShape_node]; rfl
  have hApp := appliedAt_of_judge_tm (A := lrose A) hsg hΓs hOs hPb
  have lamL : ∀ X : Expr, RoseTree.label (Expr.lam X) = Label.lam := fun _ ↦ rfl
  have lamC : ∀ X : Expr, RoseTree.children (Expr.lam X) = [X] := fun _ ↦ rfl
  have v₁ : (RoseTree.node (Label.app (Head.var 1)) [] : Expr) = Expr.var 1 [] := rfl
  have v₀ : (RoseTree.node (Label.app (Head.var 0)) [] : Expr) = Expr.var 0 [] := rfl
  have r3 : ∀ e : Expr, ((e.rename Nat.succ).rename Nat.succ).rename Nat.succ = e.rename (· + 3) :=
    fun e ↦ by rw [rename_rename, rename_rename]; rfl
  rw [rename_succ_four, rename_lam] at ha
  rw [r3, rename_lam] at hb
  rw [rename_succ_two, rename_lam] at ha₁
  simp only [lamL, lamC] at ha hb ha₁
  -- the motive at each child, in the hypothesis
  rw [v₁, hsub_var_base hApp (liftR (· + 4)) (fun i ↦ match i with | 0 => 1 | i + 1 => i + 4) rfl
    (fun _ ↦ rfl) rfl, Option.some.injEq] at ha
  subst ha
  -- the motive at the conclusion's variable
  rw [v₀, hsub_var_base hApp (liftR (· + 2)) (liftR (· + 1)) rfl (fun _ ↦ rfl) (k := 0) rfl,
    Option.some.injEq] at ha₁
  subst ha₁
  rw [hsubWith_vacuous' _ _ _ (g := id) fun i ↦ by rcases i with _ | i <;> rfl, rename_id,
    Option.some.injEq] at ha₂
  subst ha₂
  simp only [node_inj, List.cons.injEq, and_true, true_and] at hF
  subst hF
  -- the decodings
  obtain ⟨sp, hsp,
    hpt⟩ := termOf_typed (a := FreeTopos.omega) hk hsg (hc.toTmCtx.consTm hra) rfl hPb
  obtain ⟨st, hst, htt⟩ := termOf_typed hk hsg hc.toTmCtx hra ht
  obtain rfl := Option.some.inj (hφ.symm.trans (termOf_hsub₀ ha₃ hsp hst))
  -- the hypothesis that the motive holds at each child
  have hS₄ : termOf k (none :: none :: none :: none :: env)
      (Pb.rename fun i ↦ match i with | 0 => 1 | i + 1 => i + 4) =
      some (Term.rename sp fun i ↦ match i with | 0 => 1 | i + 1 => i + 4) :=
    termOf_rename _ _ hsp (fun i ↦ by rcases i with _ | i <;> rfl) (by numTm_ren)
  have hH : termOf k (none :: none :: env) (Expr.const 16 [Expr.const 30 [Expr.const 4 []],
      Expr.const 33 [Expr.const 42 [(A.rename Nat.succ).rename Nat.succ],
        Expr.const 30 [Expr.const 4 []],
        Expr.const 31 [Expr.const 4 [], Expr.const 7 []],
        Expr.lam (Expr.lam (Expr.const 32 [Expr.const 4 [], Expr.const 8 [Expr.const 4 [],
          Expr.const 30 [Expr.const 4 []], Pb.rename fun i ↦ match i with | 0 => 1 | i + 1 => i + 4,
          Expr.var 0 []]])), Expr.var 0 []],
      Expr.const 33 [Expr.const 42 [(A.rename Nat.succ).rename Nat.succ],
        Expr.const 30 [Expr.const 4 []],
        Expr.const 31 [Expr.const 4 [], Expr.const 7 []],
        Expr.lam (Expr.lam (Expr.const 32 [Expr.const 4 [], Expr.const 8 [Expr.const 4 [],
          Expr.const 30 [Expr.const 4 []],
          Expr.const 16 [Expr.const 1 [], Expr.const 7 [], Expr.const 7 []], Expr.var 0 []]])),
        Expr.var 0 []]]) =
      some (FreeTopos.Internal.roseHyp k.nil k.cons sp) := by
    simp only [termOf_const, termOf_lam, List.map_cons, List.map_nil, decStep, dec_tmIdx, hS₄,
      Option.bind_eq_bind, Option.bind_some, Option.pure_def]
    rfl
  have hc₂ := (((hc.consTm hxa).consTm (a := FreeTopos.list (FreeTopos.lrose xa))
    (A := list (lrose (A.rename Nat.succ)))
    (by rw [encTy_list, List.length_cons, encTy_succ hra]; rfl)).addHyp
    (typeIn_truth (G := G) (Γ := FreeTopos.list (FreeTopos.lrose xa) :: xa :: Γ))).consPf
    hH (typeIn_roseHyp hk.nil hk.cons hpt)
  have hlen : ((Φ.map weaken1).map weaken1 ++ [truth]).length = Φ.length + 1 := by
    rw [List.length_append, List.length_map, List.length_map, List.length_singleton]
  rw [hlen] at hc₂
  -- the motive at the construction, the step's conclusion
  have hY' : termOf k (some (Φ.length + 1) :: none :: none :: env) b =
      some (FreeTopos.Internal.roseNodeAt k.lnode (FreeTopos.lrose xa) xa sp) := by
    have h₁ : termOf k (none :: some (Φ.length + 1) :: none :: none :: env)
        (Pb.rename (liftR (· + 3))) = some (Term.rename sp (liftR (· + 2))) :=
      termOf_rename _ _ hsp (fun i ↦ by rcases i with _ | i <;> rfl) (by numTm_ren)
    have h₂ : termOf k (some (Φ.length + 1) :: none :: none :: env)
        (Expr.const 43 [((A.rename Nat.succ).rename Nat.succ).rename Nat.succ,
          Expr.const 8 [((A.rename Nat.succ).rename Nat.succ).rename Nat.succ,
          Expr.const 30 [Expr.const 42 [((A.rename Nat.succ).rename Nat.succ).rename Nat.succ]],
          Expr.var 2 [], Expr.var 1 []]]) =
        some (Term.arr k.lnode [xa] (Term.pair (Term.var 1) (Term.var 0))) := by
      simp only [termOf_const, List.map_cons, List.map_nil, decStep, dec_tmIdx,
        decTy_tmIdx (env := some (Φ.length + 1) :: none :: none :: env)
          (encTy_succ (encTy_succ (encTy_succ hxa))),
        Option.bind_eq_bind, Option.bind_some, Option.pure_def]
      rfl
    rw [termOf_hsub₀ hb h₁ h₂]
    refine congrArg some (Term.subst_rename sp _ _ _ fun i ↦ ?_)
    rcases i with _ | i
    · exact congrArg (Term.arr k.lnode · _) (if_neg (lrose_ne_rose xa)).symm
    · rfl
  obtain ⟨body₁, rfl, hb1, hlam⟩ := ihs ΓLF _ _ hds
  obtain ⟨body₂, rfl, hb2, hlam'⟩ := hlam _ _ _ hb1
  obtain ⟨body₃, rfl, hb3, hsound⟩ := hlam' _ _ _ hb2
  obtain ⟨Ds, hDs, hcs⟩ := hsound _ _ _ _ _ _ hc₂ hb3 hY'
  have hDs' : decPf k body₃ (some (Φ.length + 1) :: none :: none :: env) (Φ.length + 2) =
      some Ds := by
    rw [List.length_append, hlen, List.length_singleton] at hDs
    exact hDs
  have hw : (Φ ++ [truth]).map FreeTopos.Internal.weaken2 =
      (Φ.map weaken1).map weaken1 ++ [truth] := by
    rw [List.map_append, List.map_map]
    refine congrArg₂ _ (List.map_congr_left fun φ _ ↦ ?_) rfl
    exact (Term.rename_rename φ _ _ _ fun _ ↦ rfl).symm
  refine ⟨indD (FreeTopos.lrose xa) (.roseIndHyp k.lnode k.nil k.cons) sp st Φ.length [Ds], ?_,
    check_roseIndD (roseParts_lrose xa) (.inr ⟨hk.lnode, rfl⟩) hk.nil hk.cons
      (by rw [FreeTopos.Internal.isTy_lrose]; exact hIxa) hpt htt hc.typed
      (by rw [hw]; exact hcs)⟩
  rw [decPf_const]
  simp only [List.map_cons, List.map_nil, decPfStep.eq_def, termOf_lam, hsp, hst, decPf_lam, hDs',
    decTy_encTy _ xa A hxa, Option.map_some, Option.bind_eq_bind, Option.bind_some, lamBody_lam,
    Option.pure_def]

/-- The soundness of the decoding of a proof variable: the hypothesis the environment indexes. -/
theorem sound_hyp (hc : PfCtx G k n ΓLF env Γ Φ) {i : ℕ} {ms : List Expr} {C F : Expr}
    {φ : MTerm} (hC : classOf sg ΓLF (.var i) = some C)
    (hS : spine ΓLF C (ms.map fun m ↦ (m, judge sg m)) = some (pf F))
    (hφ : termOf k env F = some φ) :
    ∃ D, decPf k (Expr.app (.var i) ms) env Φ.length = some D ∧
      (check G E n D).2 Γ Φ φ = true := by
  obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp hC
  have hCs : Expr.TypeShape (b.rename (· + (i + 1))) = true := by
    rw [typeShape_rename]
    rcases hc.shape b (List.mem_of_getElem? hb) with ⟨B, rfl⟩ | ⟨F', rfl⟩ | rfl <;>
      · simp only [tm, pf, tp, Expr.const, Expr.app, typeShape_node]; rfl
  obtain ⟨h₁, h₂⟩ := spine_headDepth _ _ _ hCs hS
  rw [headDepth_rename] at h₁ h₂
  rcases hc.shape b (List.mem_of_getElem? hb) with ⟨B, rfl⟩ | ⟨F', rfl⟩ | rfl
  · simp only [tm, pf, Expr.const, Expr.app, headDepth_node, headDepthStep] at h₁
    exact absurd h₁ (by decide)
  rotate_left
  · simp only [tp, pf, Expr.const, Expr.app, headDepth_node, headDepthStep] at h₁
    exact absurd h₁ (by decide)
  · simp only [pf, Expr.const, Expr.app, headDepth_node, headDepthStep, List.length_map] at h₂
    obtain rfl := List.length_eq_zero_iff.mp (by omega : ms.length = 0)
    simp only [List.map_nil, spine, List.foldlM_nil, Option.pure_def, Option.some.injEq] at hS
    obtain ⟨h, φ', he, hφ', hΦ⟩ := hc.pfVar i F' hb
    rw [pf, Expr.const, Expr.app, rename_app_node] at hS
    simp only [Head.rename, List.map_cons, List.map_nil, pf, Expr.const, Expr.app, node_inj,
      List.cons.injEq, and_true, true_and] at hS
    subst hS
    obtain rfl := Option.some.inj (hφ'.symm.trans hφ)
    refine ⟨ruleD (.hyp h), ?_, check_hyp hΦ⟩
    rw [decPf, Expr.app, RoseTree.para_node]
    simp only [List.map_nil, decPfStep.eq_def, he]

/-- The step of the decoding of proofs at a constant past the signature is the decoding of an
application of a theorem of the extension. -/
theorem decPfStep_thm {c : ℕ} (hc : sig.length ≤ c)
    (xs : List (Expr × (List (Option ℕ) → ℕ → Option Deriv))) (env : List (Option ℕ)) (m : ℕ) :
    decPfStep k (.app (.const c)) xs env m =
      decPfThm k nd (joinD (ruleD .delta) reflD) indD c xs env m := by
  obtain ⟨i, rfl⟩ : ∃ i, c = i + 57 :=
    ⟨c - 57, by rw [show sig.length = 57 from rfl] at hc; omega⟩
  rfl

include hk hsg in
/-- The decoding, in a context matching an environment, of a formula of a theorem with types and
terms substituted for its object variables and variables: the instance of the formula at the
decoded types and terms. -/
theorem termOf_inst {a : FreeTopos.Internal.Thm}
    {xs : List PartialHorn.Tree} {Xs Ms : List Expr} {σ' : List MTerm}
    (hxs : List.Forall₂ (fun X x ↦ encTy k env.length x = some X) Xs xs)
    (hσ : List.Forall₂ (fun M u ↦ termOf k env M = some u ∧ Term.VarLeaves u = true) Ms σ')
    (hty : ∀ A ∈ a.ctx, FreeTopos.Internal.IsTy G a.arity A = true)
    {ΓT : Ctx} (hΓT : encCtx k a.arity a.ctx = some ΓT) (hXs : Xs.length = a.arity)
    (hMs : Ms.length = a.ctx.length) {s : MTerm} {Y Y' : Expr}
    (hY : enc G a.arity k s (ctxObj a.ctx) (stdEnv a.ctx) = some Y)
    (hts : FreeTopos.Internal.typeIn G a.arity a.ctx s = some FreeTopos.omega)
    (h : hsubs (RoseTree.node (.base 6) []) (Xs ++ Ms) Y = some Y') :
    termOf k env Y' = some (FreeTopos.Internal.instTerm xs.reverse σ'.reverse s) := by
  obtain ⟨r, hr, -⟩ := Option.map_eq_some_iff.mp hts
  have hsc := scopedBelow_enc hsg hk hty hΓT hr hY
  have hcl : ∀ ρ, Y.rename (liftR^[a.arity + a.ctx.length] ρ) = Y := fun ρ ↦ by
    rw [Nat.add_comm]
    exact ScopedBelow.rename_iterate hsc ρ
  have hdec : dec k Y a.ctx.length = some s := by
    rw [← length_stdEnv]
    exact dec_enc s _ _ Y hY
  have hocc : ∀ i, Term.occurs s i = true → i < a.ctx.length := fun i hi ↦ by
    have := FreeTopos.Internal.compile_occurs_lt s _ _ r hr i hi
    rwa [length_stdEnv] at this
  have hvl := Term.varLeaves_of_compile s _ _ r hr
  have hxl : xs.length = a.arity := hxs.length_eq.symm.trans hXs
  rw [hsubs_append, hMs] at h
  obtain ⟨Y₁, hY₁, h₂⟩ := Option.bind_eq_some_iff.mp h
  -- the substitution of the types, in the context of the object variables alone
  have hρ := hsubsPre_rename _ (fun i ↦ i - env.length) a.ctx.length Xs Y Y₁ hY₁
  rw [hXs, hcl] at hρ
  have hx₀ : ∀ X x, encTy k env.length x = some X →
      encTy k 0 x = some (X.rename (· - env.length)) :=
    fun X x hx ↦ encTy_rename x env.length X hx 0 _ fun i hi ↦ by omega
  have hxs₀ : List.Forall₂ (fun Xk b ↦ ∀ e, encTy k e b = some (Xk.rename (· + e)))
      (Xs.map fun X ↦ X.rename (· - env.length)) xs :=
    List.forall₂_map_left_iff.mpr (hxs.imp fun X x hx e ↦ by
      have := encTy_add (d := e) (hx₀ X x hx)
      rwa [Nat.zero_add] at this)
  have hph := dec_hsubsPre_obj (k := k) _ xs Y _ s hxs₀ hdec hocc hρ
  -- the context's term variables restored
  have htm := hsubsPre_rename _ (tmIdx env) a.ctx.length Xs Y Y₁ hY₁
  rw [hXs, hcl] at htm
  have hsh := hsubsPre_rename _ (· + numTm env) a.ctx.length _ Y _ hρ
  rw [List.length_map, hXs, hcl] at hsh
  have hmaps : (Xs.map fun X ↦ X.rename (· - env.length)).map (fun X ↦ X.rename (· + numTm env)) =
      Xs.map fun X ↦ X.rename (tmIdx env) := by
    rw [List.map_map]
    refine List.map_congr_left fun X hX ↦ ?_
    obtain ⟨x, hx⟩ := forall₂_left_mem hxs X hX
    have h₁ := encTy_rename x 0 _ (hx₀ X x hx) (numTm env) (· + numTm env) fun i _ ↦ by
      beta_reduce; omega
    have h₂ := encTy_rename x env.length X hx (numTm env) (tmIdx env) fun i hi ↦
      tmIdx_ge env i hi
    exact Option.some.inj (h₁.symm.trans h₂)
  rw [hmaps] at hsh
  have heq := Option.some.inj (htm.symm.trans hsh)
  have hdec₁ : dec k (Y₁.rename (liftR^[a.ctx.length] (tmIdx env)))
      (numTm env + a.ctx.length) = some (Term.rename
        (Term.osubstF (FreeTopos.Internal.objScope xs) s)
          (liftR^[a.ctx.length] (· + numTm env))) := by
    rw [heq]
    exact dec_rename _ a.ctx.length _ _ _ hph fun i hi ↦ by
      obtain ⟨i, rfl⟩ : ∃ i', i = i' + a.ctx.length := ⟨i - a.ctx.length, by omega⟩
      rw [iterate_liftR_add]
      omega
  -- the substitution of the terms
  have hrn := hsubs_rename _ (tmIdx env) Ms Y₁ Y' h₂
  rw [hMs] at hrn
  have hdh := dec_hsubs (k := k) _ _ _ (numTm env) _ σ' _
    (by rw [List.length_map, hMs]; exact hdec₁)
    (Term.varLeaves_rename _ (Term.varLeaves_osubstF _ _ hvl) _)
    (List.forall₂_map_left_iff.mpr hσ) hrn
  have hσl : σ'.length = a.ctx.length := hσ.length_eq.symm.trans hMs
  refine hdh.trans (congrArg some ?_)
  rw [FreeTopos.Internal.instTerm, Term.osubst_eq_osubstF,
    Term.osubstF_congr_of_compile (τ' := fun z ↦ xs.reverse[z]?.getD (PartialHorn.var z))
      (fun z hz ↦ by rw [FreeTopos.Internal.objScope, if_pos (by rw [hxl]; exact hz)])
      s _ _ r hr,
    Term.subst_rename _ _ _
      (fun i ↦ scopeSubst σ' (liftR^[a.ctx.length] (· + numTm env) i)) fun _ ↦ rfl]
  refine Term.subst_congr _ _ _ fun i hi ↦ ?_
  rw [Term.occurs_osubstF] at hi
  have hi' := hocc i hi
  rw [iterate_liftR_lt _ _ i hi', scopeSubst, if_pos (by rw [hσl]; exact hi')]

include hsg in
/-- The leading arguments of a spine, each checking against the kind of types, decode to types
whose encodings they are. -/
theorem spine_tys (hc : PfCtx G k n ΓLF env Γ Φ) {cs : List Expr} {m : ℕ}
    (hargs : ∀ i < m, ∃ D' M, hsubs (RoseTree.node (.base 6) []) (cs.take i) tp = some D' ∧
      cs[i]? = some M ∧ judge sg M ΓLF (.check D') = true) :
    ∃ xs, (cs.take m).mapM (fun M ↦ decTy k env.length M) = some xs ∧
      List.Forall₂ (fun x M ↦ encTy k env.length x = some M ∧
        FreeTopos.Internal.IsTy G n x = true) xs (cs.take m) := by
  have htys : List.Forall₂ (fun M M' ↦ ∃ x, decTy k env.length M = some x ∧
      (encTy k env.length x = some M' ∧ FreeTopos.Internal.IsTy G n x = true))
      (cs.take m) (cs.take m) :=
    forall₂_of_getElem rfl fun i h₁ _ ↦ by
      have hi : i < m := by
        rw [List.length_take] at h₁
        omega
      obtain ⟨D', M, hD', hM, hJ⟩ := hargs i hi
      obtain rfl := hsubs_tp hD'
      rw [List.getElem_take]
      obtain rfl := Option.some.inj ((List.getElem?_eq_getElem (by
        rw [List.length_take] at h₁
        omega)).symm.trans hM)
      obtain ⟨x, hx, hxt⟩ := tyComplete hsg hc.heads₀ _ hJ
      exact ⟨x, decTy_encTy _ x _ hx, hx, hxt⟩
  exact mapM_of_forall₂ htys

include hk hsg in
/-- The decoding of the spine of an application of a theorem's declaration: its leading
arguments decode to the types of the theorem's object variables, the next to terms of the
instances of the types of its variables, the formula it proves decodes to the instance of the
theorem's conclusion, and its other arguments are proofs of formulas that decode to the instances
of its hypotheses. -/
theorem thm_spine (hc : PfCtx G k n ΓLF env Γ Φ) {cs : List Expr} {a : FreeTopos.Internal.Thm}
    {C F : Expr} (hwf : a.wellFormed G = true) (hC : thmTy G k a = some C)
    (hS : spine ΓLF C (cs.map fun m ↦ (m, judge sg m)) = some (pf F)) :
    ∃ (xs : List PartialHorn.Tree) (σ' : List MTerm),
      (cs.take a.arity).mapM (fun M ↦ decTy k env.length M) = some xs ∧
      ((cs.drop a.arity).take a.ctx.length).mapM (fun M ↦ termOf k env M) = some σ' ∧
      xs.length = a.arity ∧ σ'.length = a.ctx.length ∧
      (∀ x ∈ xs.reverse, FreeTopos.Internal.IsTy G n x = true) ∧
      List.Forall₂ (fun s b ↦ FreeTopos.Internal.typeIn G n Γ s = some b) σ'.reverse
        (a.ctx.map (PartialHorn.subst xs.reverse)) ∧
      termOf k env F = some (FreeTopos.Internal.instTerm xs.reverse σ'.reverse a.concl) ∧
      List.Forall₂ (fun p h ↦ ∃ H, judge sg p ΓLF (.check (pf H)) = true ∧
        termOf k env H = some (FreeTopos.Internal.instTerm xs.reverse σ'.reverse h))
        (cs.drop (a.arity + a.ctx.length)) a.hyps := by
  -- the theorem is well formed
  rw [FreeTopos.Internal.Thm.wellFormed, Bool.and_eq_true, Bool.and_eq_true] at hwf
  have hty := List.all_eq_true.mp hwf.1.1
  have hhyps : ∀ h ∈ a.hyps, FreeTopos.Internal.typeIn G a.arity a.ctx h =
      some FreeTopos.omega := fun h hh ↦ of_decide_eq_true_at (List.all_eq_true.mp hwf.1.2 h hh)
  have hconcl := of_decide_eq_true_at hwf.2
  obtain ⟨ΓT, Hs, X, hΓT, hHs, hX, rfl⟩ := thmTy_eq_some hC
  obtain ⟨T', hT', hT'len, hT'i⟩ := encCtx_reverse hΓT
  have hΓlen : ΓT.reverse.length = a.arity + a.ctx.length := by
    rw [hT', List.length_append, List.length_replicate, hT'len]
  have hDs : ∀ D ∈ ΓT.reverse, D = tp ∨ ∃ A, D = tm A := by
    rw [hT']
    intro D hD
    rcases List.mem_append.mp hD with hD | hD
    · exact .inl (List.eq_of_mem_replicate hD)
    · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hD
      obtain ⟨A, hA, -⟩ := hT'i i _
        (List.getElem?_eq_getElem (by rw [List.length_reverse, ← hT'len]; exact hi))
      rw [List.getElem?_eq_getElem hi, Option.some.injEq] at hA
      exact .inr ⟨A, hA⟩
  -- the spine: the types, the terms and the proofs
  obtain ⟨hlen, hargs, R', hR', hS'⟩ := spine_piTele_gen (J := judge sg) (P := pf F) rfl hDs hS
  rw [hΓlen] at hlen hR' hS'
  rw [take_add'] at hR'
  obtain ⟨Hs', X', hHs', hX', rfl⟩ := hsubs_arrows_pf hR'
  obtain ⟨hps, hFX⟩ := spine_arrows (J := judge sg) rfl hS'
  obtain rfl := pf_inj hFX
  have hXsl : (cs.take a.arity).length = a.arity := by
    rw [List.length_take]
    omega
  have hMsl : ((cs.drop a.arity).take a.ctx.length).length = a.ctx.length := by
    rw [List.length_take, List.length_drop]
    omega
  -- the types decode
  obtain ⟨xs, hxsM, hxs⟩ := spine_tys hsg hc fun i hi ↦ hargs i tp (by
    rw [hT', List.getElem?_append_left (by rw [List.length_replicate]; exact hi),
      List.getElem?_replicate_of_lt hi])
  have hxs' : List.Forall₂ (fun X x ↦ encTy k env.length x = some X) (cs.take a.arity) xs :=
    List.Forall₂.flip (R := fun X x ↦ encTy k env.length x = some X) (hxs.imp fun _ _ h ↦ h.1)
  have hxl : xs.length = a.arity := hxs.length_eq.trans hXsl
  -- the terms decode, to terms of the instances of the variables' types
  have hterms : List.Forall₂ (fun M A ↦ ∃ s, termOf k env M = some s ∧
      (FreeTopos.Internal.typeIn G n Γ s = some (PartialHorn.subst xs.reverse A) ∧
        Term.VarLeaves s = true))
      ((cs.drop a.arity).take a.ctx.length) a.ctx.reverse :=
    forall₂_of_getElem (by rw [hMsl, List.length_reverse]) fun i hi₁ hi₂ ↦ by
      have hi : i < a.ctx.length := by
        rw [hMsl] at hi₁
        exact hi₁
      obtain ⟨Aenc, hAenc, hAe⟩ := hT'i i _ (List.getElem?_eq_getElem hi₂)
      obtain ⟨D', M, hD', hM, hJ⟩ := hargs (a.arity + i) (tm Aenc) (by
        rw [hT', List.getElem?_append_right (by rw [List.length_replicate]; omega),
          List.length_replicate, Nat.add_sub_cancel_left]
        exact hAenc)
      rw [take_add', hsubs_append, List.length_take, List.length_drop,
        Nat.min_eq_left (by omega)] at hD'
      obtain ⟨E₀, hE₀, hD'⟩ := Option.bind_eq_some_iff.mp hD'
      obtain ⟨E₁, hE₁, rfl⟩ := hsubsPre_const₁ hE₀
      obtain ⟨E₂, hE₂, rfl⟩ := hsubs_const₁ hD'
      have hbs : List.Forall₂ (fun Xk b ↦ ∀ e, encTy k e b = some (Xk.rename (· + e)))
          (cs.take a.arity) (xs.map (FreeTopos.Internal.shiftObj env.length)) :=
        List.forall₂_map_right_iff.mpr (hxs'.imp fun X x hx e ↦
          encTy_shiftObj (off := e) _ _ (by rw [Nat.add_comm]; exact encTy_add hx))
      have he₁ := encTy_hsubsPre_obj _ _ _ _ _ hbs hAe hE₁
      have hlm : ((cs.drop a.arity).take i).length = i := by
        rw [List.length_take, List.length_drop]
        omega
      have he₂ := hsubs_encTy _ _ _ _ (by rw [hlm]; exact he₁) hE₂
      have hA := hty _ (List.mem_reverse.mp (List.getElem_mem hi₂))
      have hsub : FreeTopos.Internal.substF
          (FreeTopos.Internal.objScope (xs.map (FreeTopos.Internal.shiftObj env.length)))
          a.ctx.reverse[i] = FreeTopos.Internal.shiftObj env.length
            (PartialHorn.subst xs.reverse a.ctx.reverse[i]) := by
        rw [FreeTopos.Internal.subst_eq_substF, FreeTopos.Internal.shiftObj,
          FreeTopos.Internal.substF_comp]
        refine FreeTopos.Internal.substF_congr (n := a.arity) (fun z hz ↦ ?_) _
          (FreeTopos.Internal.scoped_of_isTy (G := G) _ hA)
        rw [FreeTopos.Internal.objScope, if_pos (by rw [List.length_map, hxl]; exact hz),
          ← List.map_reverse, List.getElem?_map,
          List.getElem?_eq_getElem (by rw [List.length_reverse, hxl]; exact hz)]
        rfl
      rw [hsub] at he₂
      have h₃ := encTy_of_shiftObj (off := 0) _ _ he₂
      rw [Nat.zero_add] at h₃
      rw [List.getElem_take, List.getElem_drop]
      obtain rfl := Option.some.inj ((List.getElem?_eq_getElem (by omega)).symm.trans hM)
      obtain ⟨u, hu, hut⟩ := termOf_typed hk hsg hc.toTmCtx h₃ hJ
      obtain ⟨r, hr, -⟩ := Option.map_eq_some_iff.mp hut
      exact ⟨u, hu, hut, Term.varLeaves_of_compile u _ _ r hr⟩
  obtain ⟨σ', hσM, hσt⟩ := mapM_of_forall₂ hterms
  have hσf := forall₂_of_mapM hσM
  have hσl : ∀ u ∈ σ', Term.VarLeaves u = true := fun u hu ↦
    (forall₂_left_mem hσt u hu).elim fun _ h ↦ h.2
  have hσ2 : List.Forall₂ (fun M u ↦ termOf k env M = some u ∧ Term.VarLeaves u = true)
      ((cs.drop a.arity).take a.ctx.length) σ' :=
    (List.Forall₂.flip (R := fun M u ↦ u ∈ σ' ∧ termOf k env M = some u)
      (forall₂_mem (List.Forall₂.flip (R := fun u M ↦ termOf k env M = some u) hσf))).imp
      fun M u h ↦ ⟨h.2, hσl u h.1⟩
  have hσlen : σ'.length = a.ctx.length := hσf.length_eq.symm.trans hMsl
  -- the formulas
  have key : ∀ (s : MTerm) (Y Y' : Expr),
      enc G a.arity k s (ctxObj a.ctx) (stdEnv a.ctx) = some Y →
      FreeTopos.Internal.typeIn G a.arity a.ctx s = some FreeTopos.omega →
      hsubs (RoseTree.node (.base 6) []) (cs.take a.arity ++ (cs.drop a.arity).take a.ctx.length)
        Y = some Y' →
      termOf k env Y' = some (FreeTopos.Internal.instTerm xs.reverse σ'.reverse s) :=
    fun s Y Y' hY hts h ↦ termOf_inst hk hsg hxs' hσ2 hty hΓT hXsl hMsl hY hts h
  -- the hypotheses
  have hhyp : List.Forall₂ (fun h H' ↦ termOf k env H' =
      some (FreeTopos.Internal.instTerm xs.reverse σ'.reverse h)) a.hyps Hs' :=
    forall₂_comp (fun h H H' hH hH' ↦ key h H H' hH.2 (hhyps h hH.1) hH')
      (forall₂_mem (forall₂_of_mapM hHs)) hHs'
  have hσr : List.Forall₂ (fun s b ↦ FreeTopos.Internal.typeIn G n Γ s = some b) σ'.reverse
      (a.ctx.map (PartialHorn.subst xs.reverse)) := by
    rw [← List.reverse_reverse (a.ctx.map _)]
    refine List.forall₂_reverse_iff.mpr ?_
    rw [← List.map_reverse]
    exact List.forall₂_map_right_iff.mpr (hσt.imp fun _ _ h ↦ h.1)
  refine ⟨xs, σ', hxsM, hσM, hxl, hσlen, fun x hx ↦
    (forall₂_left_mem hxs x (List.mem_reverse.mp hx)).elim fun _ h ↦ h.2, hσr,
    key a.concl X F hX hconcl hX', forall₂_comp (fun p H h hpH hHh ↦ ⟨H, hpH, hHh⟩) hps
      (List.Forall₂.flip (R := fun H' h ↦ termOf k env H' =
        some (FreeTopos.Internal.instTerm xs.reverse σ'.reverse h)) hhyp)⟩

include hk hsg in
/-- The soundness of the decoding of an application of a theorem of the extension: its leading
arguments decode to the types of the theorem's object variables, the next to terms of the
instances of the types of its variables, its others are proofs of the instances of its
hypotheses, which decode soundly, and the application decodes to the application of the
theorem's entry, which proves the instance of its conclusion. -/
theorem sound_thm (hc : PfCtx G k n ΓLF env Γ Φ) {c j : ℕ} {cs : List Expr}
    {a : FreeTopos.Internal.Thm} {C F : Expr} {φ : MTerm} (hlt : sig.length ≤ c)
    (hthm : k.ext[c - sig.length]? = some (.thm j a.arity a.ctx.length))
    (he : (E[j]?).bind FreeTopos.Internal.Entry.language? = some a)
    (hwf : a.wellFormed G = true) (hC : thmTy G k a = some C)
    (ih : ∀ M ∈ cs, PfSoundAt sg G k E n M)
    (hS : spine ΓLF C (cs.map fun m ↦ (m, judge sg m)) = some (pf F))
    (hφ : termOf k env F = some φ) :
    ∃ D, decPf k (Expr.const c cs) env Φ.length = some D ∧ (check G E n D).2 Γ Φ φ = true := by
  obtain ⟨xs, σ', hxsM, hσM, hxl, hσlen, hθ, hσr, hF, hhyp⟩ := thm_spine hk hsg hc hwf hC hS
  obtain rfl := Option.some.inj (hφ.symm.trans hF)
  -- the proofs decode, to proofs of the instances of the hypotheses
  have hproofs : List.Forall₂ (fun p h ↦ ∃ D, decPf k p env Φ.length = some D ∧
      (check G E n D).2 Γ Φ (FreeTopos.Internal.instTerm xs.reverse σ'.reverse h) = true)
      (cs.drop (a.arity + a.ctx.length)) a.hyps :=
    (forall₂_mem hhyp).imp fun p _ ⟨hp, H, hJ, hH⟩ ↦
      ih p (List.mem_of_mem_drop hp) ΓLF env Γ Φ H _ hc hJ hH
  obtain ⟨Ds, hDs', hDchk⟩ := mapM_of_forall₂ hproofs
  refine ⟨_, ?_, check_apply he ?_ rfl hDchk.length_eq fun x hx ↦ ?_⟩
  · rw [decPf_const, decPfStep_thm hlt, decPfThm, if_pos hlt, hthm]
    simp only [← List.map_take, ← List.map_drop, List.mapM_map, Function.comp_def, hxsM, hσM,
      hDs', Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  · simp only [FreeTopos.Internal.instOk, List.length_reverse, hxl, hσlen, decide_true,
      Bool.true_and, Bool.and_eq_true, List.all_eq_true]
    refine ⟨⟨hθ, trivial⟩, fun x hx ↦ ?_⟩
    obtain ⟨u, b⟩ := x
    refine @decide_eq_true _ ?_ ?_
    exact List.forall₂_zip hσr hx
  · obtain ⟨d, h⟩ := x
    exact List.forall₂_zip hDchk hx

open FreeTopos.Internal (Defn compile IsTy) in
/-- The unfolding of a definition of parameters and value of types, whose body compiles, is well
formed: the definition at its variables, applied to its parameters, and its body are terms of its
value's type. -/
theorem deltaThm_wellFormed {kd : ℕ} {d : Defn} {cd : PartialHorn.Defn}
    (hd : G.defs[kd]? = some (.language d)) (hok : (Rank.ofDefn d).ok G = true)
    (hc : d.compile G = some cd) : (deltaThm kd d).wellFormed G = true := by
  simp only [Rank.ok, Rank.ofDefn, Bool.and_eq_true] at hok
  obtain ⟨hps, hty⟩ := hok
  obtain ⟨cb, hcb, -⟩ := FreeTopos.Internal.Defn.compile_eq_some hc
  -- the object variables substitute identically into a type in their scope
  have hid : ∀ A, IsTy G d.arity A = true →
      PartialHorn.subst ((List.range d.arity).map PartialHorn.var) A = A := fun A hA ↦ by
    rw [FreeTopos.Internal.subst_eq_substF,
      FreeTopos.Internal.substF_congr (τ' := PartialHorn.var) (fun i hi ↦ by
        rw [List.getElem?_map, List.getElem?_range hi]
        rfl) A (FreeTopos.Internal.scoped_of_isTy A hA),
      FreeTopos.Internal.substF_var_id]
  -- the parameters compile to their types
  have hstd := FreeTopos.Internal.map_snd_stdEnv d.params
  have hrs : ((List.range d.params.length).map Term.var).mapM
      (fun c ↦ compile G d.arity c (ctxObj d.params) (stdEnv d.params)) =
        some (stdEnv d.params) := by
    rw [List.mapM_map]
    have hl := congrArg List.length hstd
    rw [List.length_map] at hl
    refine mapM_of_forall₂_eq (forall₂_of_getElem (by rw [List.length_range, hl]) fun i h₁ h₂ ↦ ?_)
    rw [Function.comp_apply, List.getElem_range, Term.var]
    exact FreeTopos.Internal.compile_var_iff.mpr ⟨rfl, List.getElem?_eq_getElem h₂⟩
  -- the definition at its variables, applied to its parameters
  have hdefn : compile G d.arity (Term.defn kd ((List.range d.arity).map PartialHorn.var)
      ((List.range d.params.length).map Term.var)) (ctxObj d.params) (stdEnv d.params) =
      some (_, PartialHorn.subst ((List.range d.arity).map PartialHorn.var) d.type) :=
    FreeTopos.Internal.compile_defn_iff.mpr ⟨d, stdEnv d.params, hd, hrs,
    by rw [List.length_map, List.length_range],
    List.all_eq_true.mpr fun x hx ↦ by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      exact FreeTopos.Internal.isTy_var.mpr (List.mem_range.mp hi),
    by
      rw [hstd]
      exact ((List.map_congr_left fun A hA ↦ hid A (List.all_eq_true.mp hps A hA)).trans
        (List.map_id _)).symm,
    rfl⟩
  rw [hid _ hty] at hdefn
  refine FreeTopos.Internal.Thm.wellFormed_iff.mpr
    ⟨hps, fun h hh ↦ (nomatch (show h ∈ ([] : List Term) from hh)), ?_⟩
  change (compile G d.arity (Term.eq (Term.defn kd ((List.range d.arity).map PartialHorn.var)
    ((List.range d.params.length).map Term.var)) d.body) (ctxObj d.params)
    (stdEnv d.params)).map Prod.snd = some FreeTopos.omega
  rw [Term.eq, FreeTopos.Internal.compile_eq_iff.mpr ⟨_, _, rfl, _, _, hdefn, _, hcb, rfl⟩]
  rfl

open FreeTopos.Internal (Defn Definition) in
/-- The declaration of the unfolding of a definition mentions the definition's constant, so the
indices name the definition. -/
theorem tmConst_of_thmTy_delta {kd : ℕ} {d : Defn} {T : Expr}
    (hd : G.defs[kd]? = some (.language d)) (h : thmTy G k (deltaThm kd d) = some T) :
    ∃ c, k.tmConst (.defn kd) d.arity d.params.length = some c := by
  obtain ⟨-, -, X, -, -, hX, -⟩ := thmTy_eq_some h
  change enc G d.arity k (RoseTree.node .eq [Term.defn kd
    ((List.range d.arity).map PartialHorn.var) ((List.range d.params.length).map Term.var),
    d.body]) (ctxObj d.params) (stdEnv d.params) = some X at hX
  rw [enc_node] at hX
  simp only [List.map_cons, List.map_nil, encStep, Option.bind_eq_bind,
    Option.bind_eq_some_iff] at hX
  obtain ⟨_, -, _, -, M₁, hM₁, -⟩ := hX
  rw [Term.defn, enc_node, encStep_defn] at hM₁
  simp only [encTm, Option.bind_eq_bind, TmHead.rank, hd, Option.bind_some, Definition.language?,
    Option.map_some, Option.bind_eq_some_iff] at hM₁
  obtain ⟨c, hc, -⟩ := hM₁
  exact ⟨c, hc⟩

include hk hsg in
/-- The soundness of the decoding of an application of the unfolding of a definition: the
formula it proves decodes to the equation of the definition, at the objects and applied to the
terms its leading arguments decode to, with the definition's body at them, which the unfolding
at the left side and reflexivity at the right prove. -/
theorem sound_delta (hc : PfCtx G k n ΓLF env Γ Φ) {c kd : ℕ} {d : FreeTopos.Internal.Defn}
    {cs : List Expr} {C F : Expr} {φ : MTerm} (hlt : sig.length ≤ c)
    (hext : k.ext[c - sig.length]? = some (.delta kd d.arity d.params.length))
    (hd : G.defs[kd]? = some (.language d)) {cd : PartialHorn.Defn}
    (hcd : FreeTopos.Internal.Defn.compile G d = some cd) (hC : thmTy G k (deltaThm kd d) = some C)
    (hS : spine ΓLF C (cs.map fun m ↦ (m, judge sg m)) = some (pf F))
    (hφ : termOf k env F = some φ) :
    ∃ D, decPf k (Expr.const c cs) env Φ.length = some D ∧ (check G E n D).2 Γ Φ φ = true := by
  -- the definition's parameters and value are of types, so its unfolding is well formed
  obtain ⟨c', hc'⟩ := tmConst_of_thmTy_delta hd hC
  obtain ⟨i, hi, -⟩ := Option.map_eq_some_iff.mp hc'
  obtain ⟨d', T', -, -, hd', -, -, hok, -, -⟩ :=
    hsg.tms i (.defn kd) _ _ (ExtConst.find?_spec _ _ _ hi)
  simp only [TmHead.rank, hd, Option.bind_some, FreeTopos.Internal.Definition.language?,
    Option.map_some, Option.some.injEq] at hd'
  subst hd'
  obtain ⟨xs, σ', -, -, hxl, hσlen, -, -, hF, -⟩ :=
    thm_spine hk hsg hc (deltaThm_wellFormed hd hok hcd) hC hS
  obtain rfl := Option.some.inj (hφ.symm.trans hF)
  refine ⟨joinD (ruleD .delta) reflD, ?_, ?_⟩
  · rw [decPf_const, decPfStep_thm hlt, decPfThm, if_pos hlt, hext]
  · have hθl : d.arity = xs.reverse.length := by rw [List.length_reverse, hxl]; rfl
    have hσl : d.params.length = σ'.reverse.length := by rw [List.length_reverse, hσlen]; rfl
    change (check G E n (joinD (ruleD .delta) reflD)).2 Γ Φ (FreeTopos.Internal.instTerm
      xs.reverse σ'.reverse (Term.eq (Term.defn kd ((List.range d.arity).map PartialHorn.var)
        ((List.range d.params.length).map Term.var)) d.body)) = true
    rw [instTerm_eq, hθl, hσl, instTerm_defn_vars]
    exact check_join (check_delta hd _ _) (check_refl _)

/-- At a base type, the substitution into the body of the declaration of the induction on a
quotient substitutes into the encodings of its types, each under the binders outside it, and into
the projection's application, under the motive and the variable of its domain. -/
theorem hsub_quotBody {c₀ j : ℕ} {n Q₀ A Q₁ M R : Expr}
    (h : hsub (RoseTree.node (.base c₀) []) n (quotBody Q₀ A Q₁ M) j = some R) :
    ∃ Q₀' A' Q₁' M', hsub (RoseTree.node (.base c₀) []) n Q₀ j = some Q₀' ∧
      hsub (RoseTree.node (.base c₀) []) n.shift A (j + 1) = some A' ∧
      hsub (RoseTree.node (.base c₀) []) n.shift Q₁ (j + 1) = some Q₁' ∧
      hsub (RoseTree.node (.base c₀) []) n.shift.shift M (j + 1 + 1) = some M' ∧
      R = quotBody Q₀' A' Q₁' M' := by
  unfold quotBody Expr.arrow at h
  obtain ⟨a₁, b₁, ha₁, hb₁, rfl⟩ := hsub_pi _ _ _ _ _ _ h
  obtain ⟨a₂, b₂, ha₂, hb₂, rfl⟩ := hsub_pi _ _ _ _ _ _ ha₁
  obtain ⟨Q₀', hQ₀, rfl⟩ := hsub_const₁ ha₂
  obtain ⟨B₂, hB₂, rfl⟩ := hsub_shift_inv hb₂
  obtain ⟨o, ho, rfl⟩ := hsub_const₁ hB₂
  rw [omega, hsub_const] at ho
  obtain rfl := Option.some.inj ho.symm
  obtain ⟨a₃, b₃, ha₃, hb₃, rfl⟩ := hsub_pi _ _ _ _ _ _ hb₁
  obtain ⟨A', b₄, hA, hb₄, rfl⟩ := hsub_pi _ _ _ _ _ _ ha₃
  obtain ⟨v₁, hv₁, rfl⟩ := hsub_const₁ hb₄
  obtain ⟨Y, hY, rfl⟩ := hsub_shift_inv hb₃
  obtain ⟨Q₁', b₅, hQ₁, hb₅, rfl⟩ := hsub_pi _ _ _ _ _ _ hY
  obtain ⟨v₂, hv₂, rfl⟩ := hsub_const₁ hb₅
  obtain ⟨A'', hA', rfl⟩ := hsub_const₁ hA
  obtain ⟨Q₁'', hQ₁', rfl⟩ := hsub_const₁ hQ₁
  have hr : renumber (j + 1 + 1) 1 = 1 := if_neg (by omega)
  have hr₀ : renumber (j + 1 + 1) 0 = 0 := if_neg (by omega)
  have hne : ¬ (1 = j + 1 + 1) := by omega
  rw [hsub_var] at hv₁ hv₂
  rcases hM : hsub (RoseTree.node (.base c₀) []) n.shift.shift M (j + 1 + 1) with _ | M'
  · simp only [List.map_cons, List.map_nil, hM, List.mapM_cons, id, Option.bind_eq_bind,
      Option.bind_none] at hv₁
    exact nomatch hv₁
  simp only [List.map_cons, List.map_nil, hM, List.mapM_cons, List.mapM_nil, id,
    Option.bind_eq_bind, Option.bind_some, Option.pure_def, if_neg hne, hr,
    Option.some.injEq] at hv₁
  simp only [List.map_cons, List.map_nil, hsub_var, List.mapM_cons, List.mapM_nil, id,
    Option.bind_eq_bind, Option.bind_some, Option.pure_def, if_neg hne, hr, hr₀,
    if_neg (show ¬ (0 = j + 1 + 1) by omega), Option.some.injEq] at hv₂
  subst hv₁ hv₂
  exact ⟨Q₀', A'', Q₁'', M', hQ₀, hA', hQ₁', rfl, rfl⟩

/-- At a base type, the substitutions of a list of terms into the body of the declaration of the
induction on a quotient substitute into the encodings of its types and into the projection's
application, each under the binders outside it. -/
theorem hsubs_quotBody {c₀ : ℕ} :
    ∀ (ms : List Expr) {Q₀ A Q₁ M R : Expr},
      hsubs (RoseTree.node (.base c₀) []) ms (quotBody Q₀ A Q₁ M) = some R →
      ∃ Q₀' A' Q₁' M', hsubsPre (RoseTree.node (.base c₀) []) ms 0 Q₀ = some Q₀' ∧
        hsubsPre (RoseTree.node (.base c₀) []) ms 1 A = some A' ∧
        hsubsPre (RoseTree.node (.base c₀) []) ms 1 Q₁ = some Q₁' ∧
        hsubsPre (RoseTree.node (.base c₀) []) ms 2 M = some M' ∧ R = quotBody Q₀' A' Q₁' M' := by
  intro ms
  refine List.rec (motive := fun ms ↦ ∀ {Q₀ A Q₁ M R : Expr},
      hsubs (RoseTree.node (.base c₀) []) ms (quotBody Q₀ A Q₁ M) = some R →
      ∃ Q₀' A' Q₁' M', hsubsPre (RoseTree.node (.base c₀) []) ms 0 Q₀ = some Q₀' ∧
        hsubsPre (RoseTree.node (.base c₀) []) ms 1 A = some A' ∧
        hsubsPre (RoseTree.node (.base c₀) []) ms 1 Q₁ = some Q₁' ∧
        hsubsPre (RoseTree.node (.base c₀) []) ms 2 M = some M' ∧ R = quotBody Q₀' A' Q₁' M')
    (fun {Q₀ A Q₁ M R} h ↦ ⟨Q₀, A, Q₁, M, rfl, rfl, rfl, rfl, (Option.some.inj h).symm⟩)
    (fun m ms ih {Q₀ A Q₁ M R} h ↦ ?_) ms
  rw [hsubs_cons] at h
  obtain ⟨R₁, hR₁, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨Q₀₁, A₁, Q₁₁, M₁, h₀, hA, hQ, hM, rfl⟩ := hsub_quotBody hR₁
  obtain ⟨Q₀', A', Q₁', M', h₀', hA', hQ', hM', rfl⟩ := ih h
  have hs : ∀ b, Expr.shift^[ms.length + (b + 1)] m = (Expr.shift^[ms.length + b] m).shift :=
    fun b ↦ Function.iterate_succ_apply' _ _ _
  refine ⟨Q₀', A', Q₁', M', ?_, ?_, ?_, ?_, rfl⟩
  · rw [hsubsPre_cons, Nat.add_zero, h₀, Option.bind_some]
    exact h₀'
  · rw [hsubsPre_cons, hs 0, Nat.add_zero, hA, Option.bind_some]
    exact hA'
  · rw [hsubsPre_cons, hs 0, Nat.add_zero, hQ, Option.bind_some]
    exact hQ'
  · rw [hsubsPre_cons, hs 1, hs 0, Nat.add_zero, hM, Option.bind_some]
    exact hM'

/-- At a base type, the substitutions of a list of terms for the outermost variables of a scope,
inside which are {lit}`d` further variables, into a constant applied to expressions weakened past
them, to the variables, the outermost first, and to the innermost variable: the constant applied
to the expressions and the terms, each weakened past the further variables, and to the innermost
variable. -/
theorem hsubsPre_projApp {c₀ c d : ℕ} (hd : 0 < d) :
    ∀ (ms Zs : List Expr), hsubsPre (RoseTree.node (.base c₀) []) ms d
      (Expr.const c (Zs.map (·.rename (· + (ms.length + d))) ++
        ((List.range ms.length).reverse.map fun i ↦ Expr.var (d + i)) ++ [Expr.var 0])) =
      some (Expr.const c ((Zs ++ ms).map (·.rename (· + d)) ++ [Expr.var 0])) := by
  intro ms
  refine List.rec (motive := fun ms ↦ ∀ Zs : List Expr, hsubsPre (RoseTree.node (.base c₀) []) ms d
      (Expr.const c (Zs.map (·.rename (· + (ms.length + d))) ++
        ((List.range ms.length).reverse.map fun i ↦ Expr.var (d + i)) ++ [Expr.var 0])) =
      some (Expr.const c ((Zs ++ ms).map (·.rename (· + d)) ++ [Expr.var 0])))
    (fun Zs ↦ ?_) (fun m ms ih Zs ↦ ?_) ms
  · simp only [List.length_nil, Nat.zero_add, List.range_zero, List.reverse_nil, List.map_nil,
      List.append_nil]
    rfl
  have hred : ∀ x, reduce (RoseTree.node (.base c₀) []) x [] = some x := fun x ↦ by
    rw [reduce_node]
    rfl
  have hstep : hsub (RoseTree.node (.base c₀) []) (Expr.shift^[ms.length + d] m)
      (Expr.const c (Zs.map (·.rename (· + ((m :: ms).length + d))) ++
        ((List.range (m :: ms).length).reverse.map fun i ↦ Expr.var (d + i)) ++ [Expr.var 0]))
      (ms.length + d) =
      some (Expr.const c ((Zs ++ [m]).map (·.rename (· + (ms.length + d))) ++
        ((List.range ms.length).reverse.map fun i ↦ Expr.var (d + i)) ++ [Expr.var 0])) := by
    refine hsub_const_of (mapM_of_forall₂_eq ?_)
    rw [List.length_cons, List.range_succ, List.reverse_append, List.reverse_singleton,
      List.singleton_append, List.map_cons, List.map_append, List.map_singleton,
      List.append_assoc, List.append_assoc, List.append_assoc, List.singleton_append,
      List.cons_append]
    refine List.rel_append (List.forall₂_map_left_iff.mpr (List.forall₂_map_right_iff.mpr
      (List.forall₂_same.mpr fun Z _ ↦ ?_))) (.cons ?_ (List.rel_append
        (List.forall₂_map_left_iff.mpr (List.forall₂_map_right_iff.mpr
          (List.forall₂_same.mpr fun i hi ↦ ?_))) (.cons ?_ .nil)))
    · rw [hsub_eq]
      exact hsubWith_vacuous' _ _ _ fun i ↦ by
        rw [show i + (ms.length + 1 + d) = i + 1 + (ms.length + d) by omega,
          iterate_liftR_add]
    · rw [hsub_var, show d + ms.length = ms.length + d by omega]
      simp only [List.map_nil, List.mapM_nil, Option.pure_def, Option.bind_some, ite_true, hred,
        iterate_shift]
    · have hi' := List.mem_range.mp (List.mem_reverse.mp hi)
      rw [hsub_var]
      simp only [List.map_nil, List.mapM_nil, Option.pure_def, Option.bind_some,
        if_neg (show ¬ (d + i = ms.length + d) by omega),
        show renumber (ms.length + d) (d + i) = d + i from if_neg (by omega)]
    · rw [hsub_var]
      simp only [List.map_nil, List.mapM_nil, Option.pure_def, Option.bind_some,
        if_neg (show ¬ (0 = ms.length + d) by omega),
        show renumber (ms.length + d) 0 = 0 from if_neg (by omega)]
  rw [hsubsPre_cons, hstep, Option.bind_some, ih (Zs ++ [m]), List.append_assoc,
    List.singleton_append]

include hk hsg in
/-- The soundness of the decoding of the induction on a quotient, its object parameters
instantiated at the objects {lit}`θ`: the motive, the proof at the projection's image of a
variable, whose application {lit}`N` decodes to the projection at the objects, and the term decode,
and the derivation of the motive at the term by the language's induction on the quotient proves
the formula the application proves. -/
theorem sound_quotBody (hc : PfCtx G k n ΓLF env Γ Φ) {kq : ℕ} {p : FreeTopos.Internal.Prim}
    {θ : List PartialHorn.Tree} {Qe De N P d t F : Expr} {φ : MTerm}
    (hp : G.prims[kq]? = some p) (hq : p.coeqParts.isSome = true) (hθl : θ.length = p.arity)
    (hθ : θ.all (FreeTopos.Internal.IsTy G n) = true)
    (hQt : FreeTopos.Internal.IsTy G n (PartialHorn.subst θ p.cod) = true)
    (hQ : encTy k env.length (PartialHorn.subst θ p.cod) = some Qe)
    (hD : encTy k env.length (PartialHorn.subst θ p.dom) = some De)
    (hN : termOf k (none :: env) N = some (Term.arr kq θ (Term.var 0)))
    (ih : PfLam sg (PfSoundAt sg G k E n) d)
    (hS : spine ΓLF (quotBody Qe De.shift Qe.shift (N.rename (liftR Nat.succ)))
      [(P, judge sg P), (d, judge sg d), (t, judge sg t)] = some (pf F))
    (hφ : termOf k env F = some φ) :
    ∃ pb st D, (termOf k env P).bind lamBody = some pb ∧ termOf k env t = some st ∧
      decPf k d (none :: env) (Φ.length + 1) = some D ∧
      (check G E n (indD (PartialHorn.subst θ p.cod) (.quotInd kq θ) pb st Φ.length [D])).2
        Γ Φ φ = true := by
  simp only [quotBody, tm, pf, omega, Expr.const, Expr.app] at hS
  lf_spine_open_at hS [Option.bind_eq_some_iff]
  obtain ⟨a, a₁, ⟨hP, ha, ha₁⟩, a₂, ⟨hd, ha₂⟩, htt, a₃, ha₃, hF⟩ := hS
  obtain ⟨Pb, rfl, hPb⟩ := judge_check_pi_inv hP
  simp only [Expr.lam, rename_node, RoseTree.label_node, RoseTree.children_node, List.zipIdx,
    List.map_cons, List.map_nil, Label.binders, Function.iterate_one, Label.rename] at ha ha₁
  have hΓs := fun a ha ↦ (hc.typeShape a ha).1
  have hOs : ModeShape (.check (tm omega)) = true := by
    simp only [ModeShape, tm, Expr.const, Expr.app, typeShape_node]; rfl
  have hApp := appliedAt_of_judge_tm (A := Qe) hsg hΓs hOs hPb
  -- the motive at the conclusion's variable, past the premise
  rw [rename_rename] at ha₁
  obtain rfl := Option.some.inj (ha₁.symm.trans (hsub_var_base hApp
    (liftR Nat.succ ∘ liftR Nat.succ) (fun i ↦ match i with | 0 => 0 | i + 1 => i + 2) rfl
    (fun _ ↦ rfl) rfl))
  obtain rfl := Option.some.inj (ha₂.symm.trans
    (hsubWith_vacuous' _ _ _ (j := 1) (g := id) fun i ↦ by rcases i with _ | i <;> rfl))
  rw [rename_id] at ha₃
  simp only [node_inj, List.cons.injEq, and_true, true_and] at hF
  subst hF
  -- the decodings
  obtain ⟨sp, hsp, hpt⟩ := termOf_typed (a := FreeTopos.omega) hk hsg (hc.toTmCtx.consTm hQ) rfl
    hPb
  obtain ⟨sc, hsc, hct⟩ := termOf_typed hk hsg hc.toTmCtx hQ htt
  obtain rfl := Option.some.inj (hφ.symm.trans (termOf_hsub₀ ha₃ hsp hsc))
  have hS₁ : termOf k (none :: none :: env) (Pb.rename (liftR Nat.succ)) =
      some (Term.rename sp (liftR Nat.succ)) :=
    termOf_rename _ _ hsp (fun i ↦ by rcases i with _ | i <;> rfl) fun i hi ↦ by
      rcases i with _ | i
      · exact absurd hi (by simp [numTm])
      · simp only [liftR, numTm]
        omega
  have ha' : termOf k (none :: env) a = some (Term.subst sp
      (FreeTopos.Internal.atVar0 (Term.arr kq θ (Term.var 0)))) :=
    (termOf_hsub₀ (env := none :: env) ha hS₁ hN).trans (congrArg some
      (Term.subst_rename sp _ _ _ fun i ↦ by rcases i with _ | i <;> rfl))
  have hlen : (Φ.map weaken1 ++ [truth]).length = Φ.length + 1 := by
    rw [List.length_append, List.length_map, List.length_singleton]
  obtain ⟨body, rfl, hb, hs⟩ := ih ΓLF _ _ hd
  obtain ⟨D, hD', hcD⟩ := hs _ _ _ _ _ _ ((hc.consTm hD).addHyp
    (typeIn_truth (G := G) (Γ := PartialHorn.subst θ p.dom :: Γ))) hb ha'
  rw [hlen] at hD'
  refine ⟨sp, sc, D, ?_, hsc, by rw [decPf_lam]; exact hD',
    check_quotIndD hp hq hθl hθ hQt hpt hct hc.typed hcD⟩
  rw [termOf_lam, hsp]
  rfl

/-- The body of the declaration of the induction on a quotient has three products. -/
theorem headDepth_quotBody (Q₀ A Q₁ M : Expr) : (quotBody Q₀ A Q₁ M).headDepth.2 = 3 := by
  simp only [quotBody, Expr.arrow, Expr.shift, Expr.pi, headDepth_node, headDepth_rename,
    List.map_cons, List.map_nil, headDepthStep]
  rfl

include hk hsg in
/-- The soundness of the decoding of an application of the induction on a quotient: its leading
arguments decode to the objects of the projection's object parameters, and the motive, the proof
at the projection's image of a variable and the term decode, so that the application decodes to
the derivation of the motive at the term by the language's induction on the quotient, which
proves the formula the application proves. -/
theorem sound_quotInd (hc : PfCtx G k n ΓLF env Γ Φ) {c kq : ℕ} {p : FreeTopos.Internal.Prim}
    {cs : List Expr} {C F : Expr} {φ : MTerm} (hlt : sig.length ≤ c)
    {op : ℕ} (hext : k.ext[c - sig.length]? = some (.quotInd kq p.arity op))
    (hp : G.prims[kq]? = some p)
    (hpc : p.cod = PartialHorn.op op (FreeTopos.Internal.objVars p.arity))
    (hq : p.coeqParts.isSome = true)
    (hC : quotIndTy k kq p = some C) (hsgC : sg[c]? = some C)
    (ih : ∀ M ∈ cs, PfLam sg (PfSoundAt sg G k E n) M)
    (hS : spine ΓLF C (cs.map fun m ↦ (m, judge sg m)) = some (pf F))
    (hφ : termOf k env F = some φ) :
    ∃ D, decPf k (Expr.const c cs) env Φ.length = some D ∧ (check G E n D).2 Γ Φ φ = true := by
  -- the number of arguments
  obtain ⟨-, h₂⟩ := spine_headDepth _ C _ (Sig.ok_typeShape hsg.ok c C hsgC) hS
  simp only [quotIndTy, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at hC
  obtain ⟨cq, hcq, Q₀, hQ₀, A₁, hA₁, Q₁, hQ₁, rfl⟩ := hC
  rw [headDepth_piTele_snd, List.length_replicate, headDepth_quotBody, List.length_map,
    show (pf F).headDepth.2 = 0 from rfl, Nat.add_zero] at h₂
  -- the projection is a constant of the language, of types
  obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.mp hcq
  have hpe := ExtConst.find?_spec _ _ _ hi
  obtain ⟨r, T', -, hfx, hr, -, -, hok, -, -⟩ := hsg.tms i (.arr kq) _ _ hpe
  simp only [TmHead.rank, hp, Option.map_some, Option.some.injEq] at hr
  subst hr
  simp only [Rank.ok, Rank.ofPrim, List.all_cons, List.all_nil, Bool.and_true,
    Bool.and_eq_true] at hok
  obtain ⟨hdom, hcod⟩ := hok
  -- the types
  obtain ⟨-, hargs, R', hR', hS'⟩ := spine_piTele_gen (J := judge sg) (P := pf F) rfl
    (fun D hD ↦ .inl (List.eq_of_mem_replicate hD)) hS
  rw [List.length_replicate] at hR' hS'
  obtain ⟨xs, hxsM, hxs⟩ := spine_tys hsg hc (m := p.arity) fun i hi ↦
    hargs i tp (List.getElem?_replicate_of_lt hi)
  have hXsl : (cs.take p.arity).length = p.arity := by
    rw [List.length_take]
    omega
  have hxl : xs.length = p.arity := hxs.length_eq.trans hXsl
  have hxsE : List.Forall₂ (fun X x ↦ encTy k env.length x = some X) (cs.take p.arity) xs :=
    List.Forall₂.flip (R := fun X x ↦ encTy k env.length x = some X) (hxs.imp fun _ _ h ↦ h.1)
  have hθ : xs.reverse.all (FreeTopos.Internal.IsTy G n) = true :=
    List.all_eq_true.mpr fun x hx ↦
      (forall₂_left_mem hxs x (List.mem_reverse.mp hx)).elim fun _ h ↦ h.2
  have hθl : xs.reverse.length = p.arity := by rw [List.length_reverse, hxl]
  -- the body
  obtain ⟨Q₀', A', Q₁', M', h₀, hA, hQ, hM, rfl⟩ := hsubs_quotBody _ hR'
  have hsc : ∀ P, FreeTopos.Internal.IsTy G p.arity P = true →
      PartialHorn.Scoped xs.length P = true := fun P hP ↦ by
    rw [hxl]
    exact FreeTopos.Internal.scoped_of_isTy _ hP
  have hQe := hsubsPre_encTy_subst hxsE hQ₀ (hsc _ hcod) h₀
  rw [Nat.zero_add] at hQe
  have hQ₁e := hsubsPre_encTy_subst hxsE hQ₁ (hsc _ hcod) hQ
  rw [Nat.add_comm] at hQ₁e
  obtain rfl := Option.some.inj (hQ₁e.symm.trans (encTy_succ hQe))
  have hAe := hsubsPre_encTy_subst hxsE hA₁ (hsc _ hdom) hA
  rw [Nat.add_comm] at hAe
  obtain ⟨De, hDe, rfl⟩ := encTy_pred (j := 0) hAe (Nat.succ_pos _)
  rw [Nat.add_sub_cancel] at hDe
  have hM' := hsubsPre_projApp (c₀ := 6) (c := sig.length + i) (d := 2) (by omega)
    (cs.take p.arity) []
  rw [List.map_nil, List.nil_append, List.nil_append, hXsl] at hM'
  obtain rfl := Option.some.inj (hM.symm.trans hM')
  -- the projection's application to the variable of its domain
  have hren : Expr.const (sig.length + i)
      ((cs.take p.arity).map (·.rename (· + 2)) ++ [Expr.var 0]) =
      (Expr.const (sig.length + i) ((cs.take p.arity).map Expr.shift ++ [Expr.var 0])).rename
        (liftR Nat.succ) := by
    simp only [Expr.const, Expr.app, rename_app_node, List.map_append, List.map_map]
    refine congrArg₂ RoseTree.node rfl (congrArg₂ (· ++ ·) (List.map_congr_left fun X _ ↦ ?_) rfl)
    rw [Function.comp_apply, Expr.shift, rename_rename]
    rfl
  have hN : termOf k (none :: env)
      (Expr.const (sig.length + i) ((cs.take p.arity).map Expr.shift ++ [Expr.var 0])) =
      some (Term.arr kq xs.reverse (Term.var 0)) := by
    have he : k.ext[sig.length + i - sig.length]? = some (.tm (.arr kq) p.arity 1) := by
      rw [Nat.add_sub_cancel_left]
      exact hpe
    rw [termOf_const, decStep_tm k (Nat.le_add_right _ _)]
    refine (decTm_of k (θ := xs) (args := [Term.var 0]) (Nat.le_add_right _ _) he hfx ?_ ?_
      ?_).trans rfl
    · simp only [List.length_map, List.length_append, hXsl, List.length_singleton]
    · rw [List.map_append, List.take_left' (by rw [List.length_map, List.length_map, hXsl]),
        List.mapM_map, List.mapM_map]
      exact mapM_of_forall₂_eq (hxsE.imp fun X x hx ↦
        decTy_tmIdx (env := none :: env) (encTy_succ hx))
    · rw [List.map_append, List.drop_left' (by rw [List.length_map, List.length_map, hXsl])]
      rfl
  -- the three arguments past the types
  obtain ⟨P, d, t, hPdt⟩ : ∃ P d t, cs.drop p.arity = [P, d, t] :=
    List.length_eq_three.mp (by rw [List.length_drop]; omega)
  rw [hPdt, hren, List.map_cons, List.map_cons, List.map_cons, List.map_nil] at hS'
  have hmem : d ∈ cs := List.mem_of_mem_drop (by rw [hPdt]; simp)
  obtain ⟨pb, st, D, hpb, hst, hD, hchk⟩ := sound_quotBody E hk hsg hc hp hq hθl hθ
    (FreeTopos.Internal.isTy_subst hθl hθ _ hcod) hQe hDe hN (ih d hmem) hS' hφ
  rw [hpc, ← hθl, subst_op_vars] at hchk
  refine ⟨_, ?_, hchk⟩
  obtain ⟨sP, hsP, hlb⟩ := Option.bind_eq_some_iff.mp hpb
  rw [decPf_const, decPfStep_thm hlt, decPfThm, if_pos hlt, hext]
  dsimp only
  rw [← List.map_drop, hPdt]
  simp only [List.map_cons, List.map_nil, ← List.map_take, List.mapM_map, Function.comp_def,
    hxsM, hsP, hlb, hst, hD, Option.bind_eq_bind, Option.bind_some, Option.pure_def]

variable (hth : ExtDecl G E k sg)

include hk hsg hth in
/-- The soundness of the decoding of proofs: a canonical LF term of the family of proofs of a
formula, in a context matching an environment, an internal context and hypotheses, where the
formula decodes, decodes to a derivation that the internal language's checker accepts as a proof
of the formula's decoding; and likewise at the bodies of one and of two abstractions it is. -/
theorem pfSound : ∀ M : Expr, PfSound sg G k E n M :=
  RoseTree.ind fun l cs ih ↦ by
    have hlam : ∀ c ∈ cs,
      PfLam sg (PfSoundAt sg G k E n) c := fun c hc ↦ (ih c hc).2.mono fun _ h ↦ h.1
    have hlam₂ : ∀ c ∈ cs, PfLam sg (fun b ↦ PfLam sg (PfSoundAt sg G k E n) b) c := fun c hc ↦
      (ih c hc).2.mono fun _ h ↦ h.2.mono fun _ h' ↦ h'.1
    have hlam₃ : ∀ c ∈ cs,
      PfLam sg (fun b ↦ PfLam sg (fun b' ↦ PfLam sg (PfSoundAt sg G k E n) b') b) c :=
      fun c hc ↦ (ih c hc).2.mono fun _ h ↦ h.2.mono fun _ h' ↦ h'.2
    refine ⟨fun ΓLF env Γ Φ F φ hc hj hφ ↦ ?_, fun ΓLF T P hj ↦ ?_⟩
    · obtain ⟨h, ms, hM⟩ := judge_atomic_app rfl hj
      obtain ⟨rfl, rfl⟩ := node_inj.mp hM
      obtain ⟨C, hC, hS⟩ := judge_app_inv hj
      rcases h with i | c
      · exact sound_hyp E hc hC hS hφ
      by_cases hlt : c < sig.length
      swap
      · have hle := Nat.le_of_not_lt hlt
        have hC' : sg[sig.length + (c - sig.length)]? = some C := by
          rw [Nat.add_sub_cancel' hle]
          exact hC
        obtain ⟨x, hx⟩ : ∃ x, k.ext[c - sig.length]? = some x :=
          ⟨_, List.getElem?_eq_getElem (by
            have := (List.getElem?_eq_some_iff.mp hC).1
            rw [hsg.len] at this
            omega)⟩
        rcases x with ⟨j, m, p⟩ | ⟨h, m, p⟩ | ⟨kd, m, p⟩ | ⟨op, m⟩ | ⟨kq, m, op⟩
        · obtain ⟨a, T, he, rfl, rfl, hwf, hT, hsgT⟩ := hth.1 _ j m p hx
          obtain rfl := Option.some.inj (hsgT.symm.trans hC')
          exact sound_thm E hk hsg hc hle hx he hwf hT (fun M hM ↦ (ih M hM).1) hS hφ
        · -- the declaration of a constant of the language ends in a family of terms
          obtain ⟨d, T, -, -, -, -, -, -, hT, hsgT⟩ := hsg.tms _ h m p hx
          obtain rfl := Option.some.inj (hsgT.symm.trans hC')
          obtain ⟨h₁, -⟩ := spine_headDepth _ _ _ (Sig.ok_typeShape hsg.ok c _ hC) hS
          simp only [defTy, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
            Option.some.injEq] at hT
          obtain ⟨ΓT, -, Td, -, rfl⟩ := hT
          rw [headDepth_piTele] at h₁
          exact absurd (show some 17 = some 6 from h₁) (by decide)
        · obtain ⟨d, T, hd, rfl, rfl, ⟨cd, hcd⟩, hT, hsgT⟩ := hth.2.1 _ kd m p hx
          obtain rfl := Option.some.inj (hsgT.symm.trans hC')
          exact sound_delta E hk hsg hc hle hx hd hcd hT hS hφ
        · -- the declaration of an object definition ends in the kind of types
          obtain rfl := Option.some.inj (hC'.symm.trans (hsg.objs _ op m hx).2)
          obtain ⟨h₁, -⟩ := spine_headDepth _ _ _ (Sig.ok_typeShape hsg.ok c _ hC) hS
          rw [headDepth_piTele] at h₁
          exact absurd (show some 17 = some 0 from h₁) (by decide)
        · obtain ⟨p, T, hp, rfl, hpc, hq, hT, hsgT⟩ := hth.2.2 _ kq m op hx
          obtain rfl := Option.some.inj (hsgT.symm.trans hC')
          exact sound_quotInd E hk hsg hc hle hx hp hpc hq hT hC hlam hS hφ
      have hCs := Sig.ok_typeShape hsg.ok c C hC
      obtain ⟨h₁, h₂⟩ := spine_headDepth _ C _ hCs hS
      obtain ⟨hc', hC⟩ := sig_head_pf hsg hC (by rw [← h₁]; rfl) hlt
      have hlen : cs.length = C.headDepth.2 := by
        rw [show (pf F).headDepth.2 = 0 from rfl, List.length_map] at h₂
        omega
      have mem : ∀ {x : Expr} {xs : List Expr}, x ∈ x :: xs := List.mem_cons_self
      have mem' : ∀ {x y : Expr} {xs : List Expr}, x ∈ xs → x ∈ y :: xs := List.mem_cons_of_mem _
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
      rcases hc' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · obtain rfl : C = _ := Option.some.inj (hC.symm.trans rfl)
        obtain ⟨A, t, rfl⟩ := List.length_eq_two.mp (hlen : cs.length = 2)
        exact sound_refl E hk hsg hc hS hφ
      · obtain rfl : C = _ := Option.some.inj (hC.symm.trans rfl)
        obtain ⟨A, cs, rfl⟩ := List.exists_cons_of_length_eq_add_one (hlen : cs.length = 5 + 1)
        obtain ⟨P, cs, rfl⟩ :=
          List.exists_cons_of_length_eq_add_one (Nat.succ.inj (hlen : cs.length + 1 = 5 + 1))
        obtain ⟨t, cs, rfl⟩ := List.exists_cons_of_length_eq_add_one
          (Nat.succ.inj (Nat.succ.inj (hlen : cs.length + 1 + 1 = 4 + 1 + 1)))
        obtain ⟨u, dh, dp, rfl⟩ := List.length_eq_three.mp (Nat.succ.inj (Nat.succ.inj
          (Nat.succ.inj (hlen : cs.length + 1 + 1 + 1 = 3 + 1 + 1 + 1))))
        exact sound_leib E hk hsg hc (ih dh (mem' (mem' (mem' (mem' mem))))).1
          (ih dp (mem' (mem' (mem' (mem' (mem' mem)))))).1 hS hφ
      · obtain rfl : C = _ := Option.some.inj (hC.symm.trans rfl)
        obtain ⟨A, cs, rfl⟩ := List.exists_cons_of_length_eq_add_one (hlen : cs.length = 3 + 1)
        obtain ⟨B, f, a, rfl⟩ :=
          List.length_eq_three.mp (Nat.succ.inj (hlen : cs.length + 1 = 3 + 1))
        exact sound_beta E hk hsg hc hS hφ
      · obtain rfl : C = _ := Option.some.inj (hC.symm.trans rfl)
        obtain ⟨A, cs, rfl⟩ := List.exists_cons_of_length_eq_add_one (hlen : cs.length = 3 + 1)
        obtain ⟨B, a, b, rfl⟩ :=
          List.length_eq_three.mp (Nat.succ.inj (hlen : cs.length + 1 = 3 + 1))
        exact sound_fstPair E hk hsg hc hS hφ
      · obtain rfl : C = _ := Option.some.inj (hC.symm.trans rfl)
        obtain ⟨A, cs, rfl⟩ := List.exists_cons_of_length_eq_add_one (hlen : cs.length = 3 + 1)
        obtain ⟨B, a, b, rfl⟩ :=
          List.length_eq_three.mp (Nat.succ.inj (hlen : cs.length + 1 = 3 + 1))
        exact sound_sndPair E hk hsg hc hS hφ
      · obtain rfl : C = _ := Option.some.inj (hC.symm.trans rfl)
        obtain ⟨A, B, p, rfl⟩ := List.length_eq_three.mp (hlen : cs.length = 3)
        exact sound_pairEta E hk hsg hc hS hφ
      · obtain rfl : C = _ := Option.some.inj (hC.symm.trans rfl)
        obtain ⟨t, rfl⟩ := List.length_eq_one_iff.mp (hlen : cs.length = 1)
        exact sound_unitEta E hk hsg hc hS hφ
      · obtain rfl : C = _ := Option.some.inj (hC.symm.trans rfl)
        obtain ⟨C', z, s', rfl⟩ := List.length_eq_three.mp (hlen : cs.length = 3)
        exact sound_natZero E hk hsg hc hS hφ
      · obtain rfl : C = _ := Option.some.inj (hC.symm.trans rfl)
        obtain ⟨C', cs, rfl⟩ := List.exists_cons_of_length_eq_add_one (hlen : cs.length = 3 + 1)
        obtain ⟨z, s', n, rfl⟩ :=
          List.length_eq_three.mp (Nat.succ.inj (hlen : cs.length + 1 = 3 + 1))
        exact sound_natSucc E hk hsg hc hS hφ
      · obtain rfl : C = _ := Option.some.inj (hC.symm.trans rfl)
        obtain ⟨A, cs, rfl⟩ := List.exists_cons_of_length_eq_add_one (hlen : cs.length = 4 + 1)
        obtain ⟨B, cs, rfl⟩ :=
          List.exists_cons_of_length_eq_add_one (Nat.succ.inj (hlen : cs.length + 1 = 4 + 1))
        obtain ⟨f, g, dH, rfl⟩ := List.length_eq_three.mp
          (Nat.succ.inj (Nat.succ.inj (hlen : cs.length + 1 + 1 = 3 + 1 + 1)))
        exact sound_funExt E hk hsg hc (hlam dH (mem' (mem' (mem' (mem' mem))))) hS hφ
      · obtain rfl : C = _ := Option.some.inj (hC.symm.trans rfl)
        obtain ⟨P, cs, rfl⟩ := List.exists_cons_of_length_eq_add_one (hlen : cs.length = 3 + 1)
        obtain ⟨Q, d₁, d₂, rfl⟩ :=
          List.length_eq_three.mp (Nat.succ.inj (hlen : cs.length + 1 = 3 + 1))
        exact sound_propExt E hk hsg hc (hlam d₁ (mem' (mem' mem)))
          (hlam d₂ (mem' (mem' (mem' mem)))) hS hφ
      · obtain rfl : C = _ := Option.some.inj (hC.symm.trans rfl)
        obtain ⟨P, cs, rfl⟩ := List.exists_cons_of_length_eq_add_one (hlen : cs.length = 3 + 1)
        obtain ⟨d₀, ds, n, rfl⟩ :=
          List.length_eq_three.mp (Nat.succ.inj (hlen : cs.length + 1 = 3 + 1))
        exact sound_natInd E hk hsg hc (ih d₀ (mem' mem)).1 (hlam₂ ds (mem' (mem' mem))) hS hφ
      · obtain rfl : C = _ := Option.some.inj (hC.symm.trans rfl)
        obtain ⟨A, C', z, s', rfl⟩ := List.length_eq_four.mp (hlen : cs.length = 4)
        exact sound_listNil E hk hsg hc hS hφ
      · obtain rfl : C = _ := Option.some.inj (hC.symm.trans rfl)
        obtain ⟨A, cs, rfl⟩ := List.exists_cons_of_length_eq_add_one (hlen : cs.length = 5 + 1)
        obtain ⟨C', cs, rfl⟩ :=
          List.exists_cons_of_length_eq_add_one (Nat.succ.inj (hlen : cs.length + 1 = 5 + 1))
        obtain ⟨z, s', h, t, rfl⟩ := List.length_eq_four.mp
          (Nat.succ.inj (Nat.succ.inj (hlen : cs.length + 1 + 1 = 4 + 1 + 1)))
        exact sound_listCons E hk hsg hc hS hφ
      · obtain rfl : C = _ := Option.some.inj (hC.symm.trans rfl)
        obtain ⟨A, cs, rfl⟩ := List.exists_cons_of_length_eq_add_one (hlen : cs.length = 4 + 1)
        obtain ⟨P, d₀, ds, l, rfl⟩ :=
          List.length_eq_four.mp (Nat.succ.inj (hlen : cs.length + 1 = 4 + 1))
        exact sound_listInd E hk hsg hc (ih d₀ (mem' (mem' mem))).1
          (hlam₃ ds (mem' (mem' (mem' mem)))) hS hφ
      · obtain rfl : C = _ := Option.some.inj (hC.symm.trans rfl)
        obtain ⟨C', s', l, t, rfl⟩ := List.length_eq_four.mp (hlen : cs.length = 4)
        exact sound_roseNode E hk hsg hc hS hφ
      · obtain rfl : C = _ := Option.some.inj (hC.symm.trans rfl)
        obtain ⟨P, ds, t, rfl⟩ := List.length_eq_three.mp (hlen : cs.length = 3)
        exact sound_roseInd E hk hsg hc (hlam₃ ds (mem' mem)) hS hφ
      · obtain rfl : C = _ := Option.some.inj (hC.symm.trans rfl)
        obtain ⟨A, cs, rfl⟩ := List.exists_cons_of_length_eq_add_one (hlen : cs.length = 4 + 1)
        obtain ⟨C', s', l, t, rfl⟩ :=
          List.length_eq_four.mp (Nat.succ.inj (hlen : cs.length + 1 = 4 + 1))
        exact sound_lroseNode E hk hsg hc hS hφ
      · obtain rfl : C = _ := Option.some.inj (hC.symm.trans rfl)
        obtain ⟨A, P, ds, t, rfl⟩ := List.length_eq_four.mp (hlen : cs.length = 4)
        exact sound_lroseInd E hk hsg hc (hlam₃ ds (mem' (mem' mem))) hS hφ
      · obtain rfl : C = _ := Option.some.inj (hC.symm.trans rfl)
        obtain ⟨A, cs, rfl⟩ := List.exists_cons_of_length_eq_add_one (hlen : cs.length = 5 + 1)
        obtain ⟨B, cs, rfl⟩ :=
          List.exists_cons_of_length_eq_add_one (Nat.succ.inj (hlen : cs.length + 1 = 5 + 1))
        obtain ⟨f, a, b, dh, rfl⟩ := List.length_eq_four.mp
          (Nat.succ.inj (Nat.succ.inj (hlen : cs.length + 1 + 1 = 4 + 1 + 1)))
        exact sound_cong E hk hsg hc (ih dh (mem' (mem' (mem' (mem' (mem' mem)))))).1 hS hφ
      · obtain rfl : C = _ := Option.some.inj (hC.symm.trans rfl)
        obtain ⟨A, cs, rfl⟩ := List.exists_cons_of_length_eq_add_one (hlen : cs.length = 5 + 1)
        obtain ⟨B, cs, rfl⟩ :=
          List.exists_cons_of_length_eq_add_one (Nat.succ.inj (hlen : cs.length + 1 = 5 + 1))
        obtain ⟨C', g, h, u, rfl⟩ := List.length_eq_four.mp
          (Nat.succ.inj (Nat.succ.inj (hlen : cs.length + 1 + 1 = 4 + 1 + 1)))
        exact sound_caseInl E hk hsg hc hS hφ
      · obtain rfl : C = _ := Option.some.inj (hC.symm.trans rfl)
        obtain ⟨A, cs, rfl⟩ := List.exists_cons_of_length_eq_add_one (hlen : cs.length = 5 + 1)
        obtain ⟨B, cs, rfl⟩ :=
          List.exists_cons_of_length_eq_add_one (Nat.succ.inj (hlen : cs.length + 1 = 5 + 1))
        obtain ⟨C', g, h, u, rfl⟩ := List.length_eq_four.mp
          (Nat.succ.inj (Nat.succ.inj (hlen : cs.length + 1 + 1 = 4 + 1 + 1)))
        exact sound_caseInr E hk hsg hc hS hφ
      · obtain rfl : C = _ := Option.some.inj (hC.symm.trans rfl)
        obtain ⟨A, cs, rfl⟩ := List.exists_cons_of_length_eq_add_one (hlen : cs.length = 5 + 1)
        obtain ⟨B, cs, rfl⟩ :=
          List.exists_cons_of_length_eq_add_one (Nat.succ.inj (hlen : cs.length + 1 = 5 + 1))
        obtain ⟨P, d₁, d₂, c, rfl⟩ := List.length_eq_four.mp
          (Nat.succ.inj (Nat.succ.inj (hlen : cs.length + 1 + 1 = 4 + 1 + 1)))
        exact sound_coprodInd E hk hsg hc (hlam d₁ (mem' (mem' (mem' mem))))
          (hlam d₂ (mem' (mem' (mem' (mem' mem))))) hS hφ
      · obtain rfl : C = _ := Option.some.inj (hC.symm.trans rfl)
        obtain ⟨z, φ', rfl⟩ := List.length_eq_two.mp (hlen : cs.length = 2)
        exact sound_exfalso E hk hsg hc hS hφ
    · obtain ⟨body, hM, hbJ⟩ := judge_check_pi_inv hj
      obtain ⟨rfl, rfl⟩ := node_inj.mp hM
      exact ⟨body, rfl, hbJ, (ih body List.mem_cons_self).1,
        (ih body List.mem_cons_self).2.mono fun _ h ↦ ⟨h.1, h.2.mono fun _ h' ↦ h'.1⟩⟩

include hk hsg hth in
/-- The soundness of the decoding of proofs, at a proof in a context matching an environment, an
internal context and hypotheses. -/
theorem decPf_sound {ΓLF : Ctx} {env : List (Option ℕ)} {Γ : List PartialHorn.Tree}
    {Φ : List Term} {M F : Expr} {φ : MTerm} (hc : PfCtx G k n ΓLF env Γ Φ)
    (hj : judge sg M ΓLF (.check (pf F)) = true) (hφ : termOf k env F = some φ) :
    ∃ D, decPf k M env Φ.length = some D ∧ (check G E n D).2 Γ Φ φ = true :=
  (pfSound E hk hsg hth M).1 _ _ _ _ _ _ hc hj hφ

/-- The renaming of a context of term variables alone is the identity. -/
theorem tmIdx_replicate (n : ℕ) : ∀ i, tmIdx (List.replicate n none) i = i :=
  Nat.rec (motive := fun n ↦ ∀ i, tmIdx (List.replicate n none) i = i) (fun _ ↦ rfl)
    (fun n ih i ↦ by
      rcases i with _ | i
      · rfl
      · exact congrArg (· + 1) (ih i)) n

/-- An environment of term variables alone has as many term variables as entries. -/
theorem numTm_replicate (n : ℕ) : numTm (List.replicate n none) = n :=
  Nat.rec (motive := fun n ↦ numTm (List.replicate n none) = n) rfl
    (fun n ih ↦ by beta_reduce; rw [List.replicate_succ, numTm_cons_none, ih]) n

/-- A renamed expression that is the kind of types is the kind of types. -/
theorem tp_rename_inj {T : Expr} {ρ : ℕ → ℕ} (h : T.rename ρ = tp) : T = tp := by
  obtain ⟨l, cs, rfl⟩ : ∃ l cs, T = RoseTree.node l cs :=
    ⟨_, _, (RoseTree.node_label_children T).symm⟩
  rw [rename_node, tp, Expr.const, Expr.app, node_inj] at h
  obtain ⟨hl, hcs⟩ := h
  rcases l with _ | _ | _ | (i | c)
  · exact absurd hl (by simp [Label.rename])
  · exact absurd hl (by simp [Label.rename])
  · exact absurd hl (by simp [Label.rename])
  · exact absurd hl (by simp [Label.rename, Head.rename])
  · obtain rfl : c = 0 := by simpa [Label.rename, Head.rename] using hl
    obtain rfl : cs = [] := by simpa using hcs
    rfl

/-- The declarations of the encoding of a context in {lit}`n` object variables: families of terms
at its variables of terms, and {lit}`tp` at the {lit}`n` past them. -/
theorem encCtx_getElem? {ΓLF : Ctx} (h : encCtx k n Γ = some ΓLF) {i : ℕ} {b : Expr}
    (hb : ΓLF[i]? = some b) :
    ((∃ A, b = tm A) ∧ i < Γ.length) ∨ (b = tp ∧ Γ.length ≤ i ∧ i < Γ.length + n) := by
  have hv : varType ΓLF i = some (b.rename (· + (i + 1))) := by rw [varType, hb, Option.map_some]
  rcases varType_encCtx_inv h hv with ⟨a, A, ha, -, hA⟩ | ⟨h₁, h₂, hA⟩
  · obtain ⟨A₀, rfl, -⟩ := tm_rename_inj hA
    exact .inl ⟨⟨A₀, rfl⟩, (List.getElem?_eq_some_iff.mp ha).1⟩
  · exact .inr ⟨tp_rename_inj hA, h₁, h₂⟩

/-- An encoded context in {lit}`n` object variables matches the environment of as many term
variables, the internal context, and no hypotheses. -/
theorem PfCtx.ofEnc {ΓLF : Ctx} (h : encCtx k n Γ = some ΓLF) :
    PfCtx G k n ΓLF (List.replicate Γ.length none) Γ [] where
  len := by rw [length_encCtx h, List.length_replicate]
  shape b hb := by
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
    rcases encCtx_getElem? h (List.getElem?_eq_getElem hi) with ⟨⟨A, he⟩, -⟩ | ⟨he, -⟩
    · exact .inl ⟨A, he⟩
    · exact .inr (.inr he)
  tpVar i := by
    rw [List.length_replicate]
    constructor
    · intro hi
      rcases encCtx_getElem? h hi with ⟨⟨A, he⟩, -⟩ | ⟨-, h₁, h₂⟩
      · exact absurd he.symm tm_ne_tp
      · exact ⟨h₁, h₂⟩
    · rintro ⟨h₁, h₂⟩
      have hlt : i < ΓLF.length := by rw [length_encCtx h]; exact h₂
      rcases encCtx_getElem? h (List.getElem?_eq_getElem hlt) with ⟨-, h₃⟩ | ⟨he, -⟩
      · omega
      · rw [List.getElem?_eq_getElem hlt, he]
  tmVar i A hi := by
    rcases varType_encCtx_inv h hi with ⟨a, A', ha, hA', he⟩ | ⟨-, -, he⟩
    · obtain rfl := tm_inj he
      rw [tmIdx_replicate, List.length_replicate]
      exact ⟨a, hA', ha⟩
    · exact absurd he tm_ne_tp
  numTm := (numTm_replicate _).symm
  enc := ⟨ΓLF, h⟩
  pfVar i F hi := by
    rcases encCtx_getElem? h hi with ⟨⟨A, he⟩, -⟩ | ⟨he, -⟩
    · exact absurd he pf_ne_tm
    · exact absurd he pf_ne_tp
  typed φ hφ := nomatch hφ

include hk hsg hth in
/-- The soundness of the decoding of proofs, at a proof of a formula in a context of {lit}`n`
variables of {lit}`tp` and term variables of encoded types, types in {lit}`n` object variables:
the proof decodes to a derivation that proves, as a theorem of the internal language in
{lit}`n` object variables without hypotheses, the formula's decoding. -/
theorem decPf_checks {ΓLF : Ctx} (h : encCtx k n Γ = some ΓLF)
    (hΓ : Γ.all (FreeTopos.Internal.IsTy G n) = true) {M F : Expr}
    (hF : judge sg F ΓLF (.check (tm omega)) = true)
    (hj : judge sg M ΓLF (.check (pf F)) = true) :
    ∃ D φ, decPf k M (List.replicate Γ.length none) 0 = some D ∧
      termOf k (List.replicate Γ.length none) F = some φ ∧
      FreeTopos.Internal.Thm.checks G E ⟨n, Γ, [], φ⟩ D = true := by
  have hc : PfCtx G k n ΓLF (List.replicate Γ.length none) Γ [] := PfCtx.ofEnc h
  obtain ⟨φ, hφ, hφt⟩ := termOf_typed (a := FreeTopos.omega) hk hsg hc.toTmCtx rfl hF
  obtain ⟨D, hD, hch⟩ := decPf_sound E hk hsg hth hc hj hφ
  refine ⟨D, φ, hD, hφ, ?_⟩
  simp only [FreeTopos.Internal.Thm.checks, List.all_nil, Bool.and_true, hφt, decide_true,
    hch, hΓ]

end Geb.LF.Topos

end
