/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Prototypes.LF.Topos.Telescope
import Mathlib.Tactic.NormNum

set_option doc.verso true in
/-!
# The soundness and completeness of the encoding of terms

The encoding of a term of the internal language ({name}`Geb.LF.Topos.enc`) that compiles is a
canonical LF term of the family of terms of its type's encoding ({lit}`enc_checks`), and every
canonical LF term of such a family, in a context of the encoded types, is the encoding of a term
that compiles, its decoding ({lit}`tmComplete`): the adequacy of the representation of terms
(\[HarperLicata2007\], Section 3.2). Both hold in an extension of the signature that declares
the constants of the language an indices' table names ({name}`Geb.LF.Topos.SigExt`), definitions
and primitive arrows alike, an application of such a constant instantiating its declaration as a
telescope.

## Main statements

* {lit}`enc_checks` — the encoding of a term that compiles checks.
* {lit}`tmComplete` — a canonical term of a family of terms decodes to a term that compiles,
  whose encoding it is.

## References

* \[HarperLicata2007\], Section 3.2, for adequacy.

## Tags

logical framework, LF, adequacy, Mitchell–Bénabou language
-/

set_option doc.verso true

@[expose] public section

namespace Geb.LF.Topos

variable {sg : Sig}

/-- The computation of the instantiation of a declaration's type along a spine of symbolic
arguments: the hereditary substitutions unfolded node by node, with the given facts about the
arguments, their checks and their closedness among them. The set of lemmas is shared by every
declaration, and a given computation uses only some of them. -/
local macro "lf_spine" "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (set_option linter.unusedSimpArgs false in
    simp [spine, Expr.arrow, Expr.pi, Expr.shift, Expr.var, Expr.app, rename_node, Label.rename,
      Head.rename, liftR, hsub_eq, hsubWith_node, hsubStep, Label.binders, reduce_node,
      reduceStep, Expr.erase, eraseStep, renumber, -Nat.not_ofNat_lt_one, -Nat.add_eq_right,
      rename_succ_eq_add, rename_add_add, hsubWith_rename_add_succ, rename_add_zero, rename_fun_id,
      $hs,*]))

/-- The computation of the instantiation of a declaration's type along a spine, in a
hypothesis. -/
local macro "lf_spine_at" h:ident "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (set_option linter.unusedSimpArgs false in
    simp [spine, Expr.arrow, Expr.pi, Expr.shift, Expr.var, Expr.app, rename_node, Label.rename,
      Head.rename, liftR, hsub_eq, hsubWith_node, hsubStep, Label.binders, reduce_node,
      reduceStep, Expr.erase, eraseStep, renumber, -Nat.not_ofNat_lt_one, -Nat.add_eq_right,
      rename_succ_eq_add, rename_add_add, hsubWith_rename_add_succ, rename_add_zero, rename_fun_id,
      $hs,*] at $h:ident))

section Soundness

variable {G : FreeTopos.Internal.Globals} {n : ℕ} {k : PrimIdx}

/-- The extension of an environment whose types are types by a variable of a type. -/
theorem extEnv_isTy {X a : PartialHorn.Tree} {e : MEnv} (ha : FreeTopos.Internal.IsTy G n a = true)
    (he : ∀ p ∈ e, FreeTopos.Internal.IsTy G n p.2 = true) :
    ∀ p ∈ FreeTopos.Internal.extEnv X a e, FreeTopos.Internal.IsTy G n p.2 = true := by
  intro p hp
  simp only [FreeTopos.Internal.extEnv, List.mem_cons, List.mem_map] at hp
  rcases hp with rfl | ⟨q, hq, rfl⟩
  · exact ha
  · exact he q hq

/-- The encoding of an application of a constant of the language, other than a primitive arrow
the indices name, to objects and to terms that compile, whose encodings check, is a canonical LF
term of the family of terms of the encoding of the instance of its value's type. -/
theorem enc_checks_tm (hsg : SigExt G k sg) {h : TmHead} {d : Rank} (hd : h.rank G = some d)
    {θ : List PartialHorn.Tree} {cs : List MTerm} {rs : List (PartialHorn.Tree × PartialHorn.Tree)}
    {X : PartialHorn.Tree} {e : MEnv} {ΓLF : Ctx} {M : Expr}
    (he : ∀ p ∈ e, FreeTopos.Internal.IsTy G n p.2 = true)
    (hΓ : encCtx k n (e.map Prod.snd) = some ΓLF)
    (hrs : cs.mapM (fun c ↦ FreeTopos.Internal.compile G n c X e) = some rs)
    (hθl : θ.length = d.arity) (hθty : θ.all (FreeTopos.Internal.IsTy G n) = true)
    (hrst : rs.map Prod.snd = d.params.map (PartialHorn.subst θ))
    (ih : ∀ t ∈ cs, ∀ (X : PartialHorn.Tree) (e : MEnv) (ΓLF : Ctx) (M : Expr)
      (r : PartialHorn.Tree × PartialHorn.Tree), (∀ p ∈ e, FreeTopos.Internal.IsTy G n p.2 = true) →
      encCtx k n (e.map Prod.snd) = some ΓLF → enc G n k t X e = some M →
      FreeTopos.Internal.compile G n t X e = some r →
      FreeTopos.Internal.IsTy G n r.2 = true ∧
        ∃ A, encTy k e.length r.2 = some A ∧ judge sg M ΓLF (.check (tm A)))
    (henc : encTm G k h θ (cs.map fun c ↦ (c, enc G n k c)) X e = some M) :
    FreeTopos.Internal.IsTy G n (PartialHorn.subst θ d.type) = true ∧
      ∃ A, encTy k e.length (PartialHorn.subst θ d.type) = some A ∧
        judge sg M ΓLF (.check (tm A)) := by
  have htp : ∀ j < n, varType ΓLF (e.length + j) = some tp := fun j hj ↦ by
    simpa only [List.length_map] using varType_encCtx_tp hΓ hj
  have hcl : cs.length = d.params.length := by
    rw [← length_of_mapM hrs, ← List.length_map (f := Prod.snd), hrst, List.length_map]
  simp only [encTm, Option.bind_eq_bind, hd, Option.bind_some] at henc
  obtain ⟨c, hc, henc⟩ := Option.bind_eq_some_iff.mp henc
  rw [if_pos ⟨hθl, by rw [List.length_map]; exact hcl⟩] at henc
  obtain ⟨Ts, hTs, henc⟩ := Option.bind_eq_some_iff.mp henc
  obtain ⟨Ms, hMs, henc⟩ := Option.bind_eq_some_iff.mp henc
  obtain rfl := Option.some.inj henc
  obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.mp hc
  obtain ⟨d', T, -, -, hd', -, -, hdok, hT, hsgc⟩ :=
    hsg.tms i h d.arity d.params.length (ExtConst.find?_spec _ _ _ hi)
  rw [hd, Option.some.injEq] at hd'
  cases hd'
  simp only [Rank.ok, Bool.and_eq_true, List.all_eq_true] at hdok
  simp only [defTy, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at hT
  obtain ⟨ΓT, hΓT, Td, hTd, rfl⟩ := hT
  obtain ⟨T', hT', hT'len, hT'i⟩ := encCtx_reverse hΓT
  have hxs : List.Forall₂ (fun X x ↦ encTy k e.length x = some X) Ts θ.reverse :=
    List.Forall₂.flip (R := fun X x ↦ encTy k e.length x = some X) (forall₂_of_mapM hTs)
  have hTsl : Ts.length = d.arity := by rw [length_of_mapM hTs, List.length_reverse, hθl]
  have hMsl : Ms.length = d.params.length := by
    rw [length_of_mapM hMs, List.length_reverse, List.length_map, hcl]
  have hθr : θ.reverse.length = d.arity := by rw [List.length_reverse, hθl]
  obtain ⟨E, hE, hEenc⟩ := hsubs_tm_encTy hxs hMsl hTd
    (by rw [hθr]; exact FreeTopos.Internal.scoped_of_isTy (G := G) _ hdok.2)
  rw [List.reverse_reverse] at hEenc
  refine ⟨FreeTopos.Internal.isTy_subst hθl hθty _ hdok.2, E, hEenc,
    judge_const hsgc ?_ rfl⟩
  have hDs : ∀ D ∈ ΓT.reverse, D = tp ∨ ∃ A, D = tm A := fun D hD ↦
    encCtx_tpTm hΓT D (List.mem_reverse.mp hD)
  refine spine_piTele_fwd (J := judge sg) hDs
    (by rw [List.length_append, hTsl, hMsl, hT', List.length_append, List.length_replicate,
      hT'len]) (fun idx D m hD hm ↦ ?_) hE
  by_cases hidx : idx < d.arity
  · rw [hT', List.getElem?_append_left (by rw [List.length_replicate]; exact hidx),
      List.getElem?_replicate_of_lt hidx, Option.some.injEq] at hD
    subst hD
    rw [List.getElem?_append_left (by rw [hTsl]; exact hidx)] at hm
    obtain ⟨x, hx⟩ : ∃ x, θ.reverse[idx]? = some x :=
      ⟨_, List.getElem?_eq_getElem (by rw [hθr]; exact hidx)⟩
    have hxX := forall₂_getElem? hxs idx m x hm hx
    exact ⟨tp, hsubs_tp_fwd _, encTy_checks hsg G x _ m hxX
      (List.all_eq_true.mp hθty x (List.mem_reverse.mp (List.mem_of_getElem? hx))) ΓLF htp⟩
  · obtain ⟨i', rfl⟩ : ∃ i', idx = d.arity + i' := ⟨idx - d.arity, by omega⟩
    rw [hT', List.getElem?_append_right (by rw [List.length_replicate]; omega),
      List.length_replicate, Nat.add_sub_cancel_left] at hD
    have hi' : i' < d.params.length := by
      rw [← hT'len]; exact (List.getElem?_eq_some_iff.mp hD).1
    obtain ⟨P, hP⟩ : ∃ P, d.params.reverse[i']? = some P :=
      ⟨_, List.getElem?_eq_getElem (by rw [List.length_reverse]; exact hi')⟩
    obtain ⟨A₀, hA₀, hA₀e⟩ := hT'i i' P hP
    rw [hA₀, Option.some.injEq] at hD
    subst hD
    rw [List.getElem?_append_right (by omega), hTsl, Nat.add_sub_cancel_left] at hm
    rw [take_add', List.take_left' hTsl, List.drop_left' hTsl]
    have hPty := hdok.1 P (List.mem_reverse.mp (List.mem_of_getElem? hP))
    have hPs := FreeTopos.Internal.scoped_of_isTy (G := G) _ hPty
    obtain ⟨E', hE', hE'enc⟩ := hsubs_tm_encTy hxs (Ms := Ms.take i')
      (by rw [List.length_take]; omega) hA₀e (by rw [hθr]; exact hPs)
    rw [List.reverse_reverse] at hE'enc
    refine ⟨tm E', hE', ?_⟩
    -- the argument is the encoding of the term of the parameter, of its type
    obtain ⟨t, ht⟩ : ∃ t, cs.reverse[i']? = some t :=
      ⟨_, List.getElem?_eq_getElem (by rw [List.length_reverse]; omega)⟩
    obtain ⟨rt, hrt⟩ : ∃ rt, rs.reverse[i']? = some rt :=
      ⟨_, List.getElem?_eq_getElem (by
        rw [List.length_reverse, length_of_mapM hrs]; omega)⟩
    have hct : FreeTopos.Internal.compile G n t X e = some rt :=
      forall₂_getElem? (List.forall₂_reverse_iff.mpr (forall₂_of_mapM hrs)) i' t rt ht hrt
    have hmt : enc G n k t X e = some m := by
      have := forall₂_getElem? (forall₂_of_mapM hMs) i' (t, enc G n k t) m
        (by rw [← List.map_reverse, List.getElem?_map, ht]; rfl) hm
      exact this
    have hrt2 : rt.2 = PartialHorn.subst θ P := by
      have h₁ := congrArg (·[i']?) (congrArg List.reverse hrst)
      simp only [← List.map_reverse, List.getElem?_map, hrt, hP, Option.map_some] at h₁
      exact Option.some.inj h₁
    obtain ⟨-, A, hA, hJ⟩ := ih t (List.mem_reverse.mp (List.mem_of_getElem? ht)) X e ΓLF m
      rt he hΓ hmt hct
    rw [hrt2, hE'enc, Option.some.injEq] at hA
    rw [← hA] at hJ
    exact hJ

/-- Encoding is sound: the encoding of a term of the fragment in {lit}`n` object variables, in an
environment whose types are types in them and encoded, is a canonical LF term of the family of
terms of the encoding of its type, a type in them, at the offset of the environment's
variables. -/
theorem enc_checks (hsg : SigExt G k sg) (hk : k.Valid G) :
    ∀ (s : MTerm) (X : PartialHorn.Tree) (e : MEnv) (ΓLF : Ctx) (M : Expr)
      (r : PartialHorn.Tree × PartialHorn.Tree), (∀ p ∈ e, FreeTopos.Internal.IsTy G n p.2 = true) →
      encCtx k n (e.map Prod.snd) = some ΓLF → enc G n k s X e = some M →
      FreeTopos.Internal.compile G n s X e = some r →
      FreeTopos.Internal.IsTy G n r.2 = true ∧
        ∃ A, encTy k e.length r.2 = some A ∧ judge sg M ΓLF (.check (tm A)) = true :=
  RoseTree.ind fun l cs ih X e ΓLF M r he hΓ henc hcomp ↦ by
    have htp : ∀ j < n, varType ΓLF (e.length + j) = some tp := fun j hj ↦ by
      simpa only [List.length_map] using varType_encCtx_tp hΓ hj
    rw [enc_node] at henc
    rcases l with i | _ | _ | _ | _ | a | _ | ⟨j, θ⟩ | _ | _ | c | ⟨j, θ⟩ | _
    · obtain ⟨rfl, hi⟩ := FreeTopos.Internal.compile_var_iff.mp hcomp
      simp only [encStep, List.map_nil, Option.some.injEq] at henc
      subst henc
      have hi' : (e.map Prod.snd)[i]? = some r.2 := by simp [hi]
      obtain ⟨A, hA, hv⟩ := varType_encCtx hΓ hi'
      rw [List.length_map] at hA
      exact ⟨he _ (List.mem_of_getElem? hi), A, hA, judge_var rfl hv⟩
    · obtain ⟨rfl, rfl⟩ := FreeTopos.Internal.compile_star_iff.mp hcomp
      simp only [encStep, List.map_nil, Option.some.injEq] at henc
      subst henc
      exact ⟨FreeTopos.Internal.isTy_one, one, rfl, judge_const (T := tm one) (hsg.get rfl) rfl rfl⟩
    · obtain ⟨t, u, f, a, g, b, rfl, hct, hcu, rfl⟩ :=
        FreeTopos.Internal.compile_pair_iff.mp hcomp
      simp only [encStep, List.map_cons, List.map_nil, hct, hcu, Option.bind_eq_bind,
        Option.bind_some, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at henc
      obtain ⟨A, hA, B, hB, Mt, hMt, Mu, hMu, rfl⟩ := henc
      obtain ⟨hIA', A', hA', hMtJ⟩ := ih t (by simp) X e ΓLF Mt _ he hΓ hMt hct
      obtain ⟨hIB', B', hB', hMuJ⟩ := ih u (by simp) X e ΓLF Mu _ he hΓ hMu hcu
      simp only [hA, Option.some.injEq] at hA'
      simp only [hB, Option.some.injEq] at hB'
      subst hA' hB'
      refine ⟨by rw [FreeTopos.Internal.isTy_prod, hIA', hIB']; rfl, prod A B,
        by simp [encTy_prod, hA, hB], judge_const
        (T := Expr.pi tp (Expr.pi tp (Expr.arrow (tm (v 1)) (Expr.arrow (tm (v 0))
          (tm (prod (v 1) (v 0))))))) (hsg.get rfl) ?_ rfl⟩
      have hAt := encTy_checks hsg G a _ A hA hIA' ΓLF htp
      have hBt := encTy_checks hsg G b _ B hB hIB' ΓLF htp
      simp only [tm, tp, prod, Expr.const, Expr.app] at hAt hBt hMtJ hMuJ ⊢
      lf_spine [hAt, hBt, hMtJ, hMuJ]
    · obtain ⟨t, f, a, b, rfl, hct, rfl⟩ := FreeTopos.Internal.compile_fst_iff.mp hcomp
      have hp : FreeTopos.Internal.prodParts (FreeTopos.prod a b) = some (a, b) :=
        FreeTopos.Internal.prodParts_eq_some.mpr rfl
      simp only [encStep, List.map_cons, List.map_nil, hct, hp, Option.bind_eq_bind,
        Option.bind_some, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at henc
      obtain ⟨A, hA, B, hB, Mt, hMt, rfl⟩ := henc
      obtain ⟨hIP, P, hP, hMtJ⟩ := ih t (by simp) X e ΓLF Mt _ he hΓ hMt hct
      simp only [encTy_prod, hA, hB, Option.bind_some, Option.map_some, Option.some.injEq] at hP
      subst hP
      rw [FreeTopos.Internal.isTy_prod, Bool.and_eq_true] at hIP
      obtain ⟨hIa, hIb⟩ := hIP
      refine ⟨hIa, A, hA, judge_const (T := Expr.pi tp (Expr.pi tp
        (Expr.arrow (tm (prod (v 1) (v 0))) (tm (v 1))))) (hsg.get rfl) ?_ rfl⟩
      have hAt := encTy_checks hsg G a _ A hA hIa ΓLF htp
      have hBt := encTy_checks hsg G b _ B hB hIb ΓLF htp
      simp only [tm, tp, prod, Expr.const, Expr.app] at hAt hBt hMtJ ⊢
      lf_spine [hAt, hBt, hMtJ]
    · obtain ⟨t, f, a, b, rfl, hct, rfl⟩ := FreeTopos.Internal.compile_snd_iff.mp hcomp
      have hp : FreeTopos.Internal.prodParts (FreeTopos.prod a b) = some (a, b) :=
        FreeTopos.Internal.prodParts_eq_some.mpr rfl
      simp only [encStep, List.map_cons, List.map_nil, hct, hp, Option.bind_eq_bind,
        Option.bind_some, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at henc
      obtain ⟨A, hA, B, hB, Mt, hMt, rfl⟩ := henc
      obtain ⟨hIP, P, hP, hMtJ⟩ := ih t (by simp) X e ΓLF Mt _ he hΓ hMt hct
      simp only [encTy_prod, hA, hB, Option.bind_some, Option.map_some, Option.some.injEq] at hP
      subst hP
      rw [FreeTopos.Internal.isTy_prod, Bool.and_eq_true] at hIP
      obtain ⟨hIa, hIb⟩ := hIP
      refine ⟨hIb, B, hB, judge_const (T := Expr.pi tp (Expr.pi tp
        (Expr.arrow (tm (prod (v 1) (v 0))) (tm (v 0))))) (hsg.get rfl) ?_ rfl⟩
      have hAt := encTy_checks hsg G a _ A hA hIa ΓLF htp
      have hBt := encTy_checks hsg G b _ B hB hIb ΓLF htp
      simp only [tm, tp, prod, Expr.const, Expr.app] at hAt hBt hMtJ ⊢
      lf_spine [hAt, hBt, hMtJ]
    · obtain ⟨t, f, b, rfl, hIa, hct, rfl⟩ := FreeTopos.Internal.compile_lam_iff.mp hcomp
      simp only [encStep, List.map_cons, List.map_nil, hct, Option.bind_eq_bind,
        Option.bind_some, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at henc
      obtain ⟨A, hA, B, hB, Mb, hMb, rfl⟩ := henc
      have hΓ' : encCtx k n ((FreeTopos.Internal.extEnv X a e).map Prod.snd) =
          some (tm A :: ΓLF) := by
        simp only [FreeTopos.Internal.extEnv, List.map_cons, List.map_map]
        exact encCtx_cons (by simpa only [List.length_map] using hA)
          (by simpa [Function.comp_def] using hΓ)
      obtain ⟨hIb, B', hB', hMbJ⟩ := ih t (by simp) _ _ _ Mb _ (extEnv_isTy hIa he) hΓ' hMb hct
      rw [length_extEnv, encTy_add hB, Option.some.injEq] at hB'
      subst hB'
      have hlam := judge_lam hMbJ
      refine ⟨by rw [FreeTopos.Internal.isTy_exp, hIa, hIb]; rfl, exp A B,
        by simp [encTy_exp, hA, hB], judge_const
        (T := Expr.pi tp (Expr.pi tp (Expr.arrow (Expr.arrow (tm (v 1)) (tm (v 0)))
          (tm (exp (v 1) (v 0)))))) (hsg.get rfl) ?_ rfl⟩
      have hAt := encTy_checks hsg G a _ A hA hIa ΓLF htp
      have hBt := encTy_checks hsg G b _ B hB hIb ΓLF htp
      simp only [tm, tp, exp, Expr.const, Expr.app, Expr.pi] at hAt hBt hlam ⊢
      lf_spine [hAt, hBt, hlam]
    · obtain ⟨t, u, rfl, f, a, b, hct, g, hcu, rfl⟩ := FreeTopos.Internal.compile_app_iff.mp hcomp
      have hp : FreeTopos.Internal.expParts (FreeTopos.exp a b) = some (a, b) :=
        FreeTopos.Internal.expParts_eq_some.mpr rfl
      simp only [encStep, List.map_cons, List.map_nil, hct, hp, Option.bind_eq_bind,
        Option.bind_some, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at henc
      obtain ⟨A, hA, B, hB, Mt, hMt, Mu, hMu, rfl⟩ := henc
      obtain ⟨hIP, P, hP, hMtJ⟩ := ih t (by simp) X e ΓLF Mt _ he hΓ hMt hct
      obtain ⟨hIA', A', hA', hMuJ⟩ := ih u (by simp) X e ΓLF Mu _ he hΓ hMu hcu
      simp only [encTy_exp, hA, hB, Option.bind_some, Option.map_some, Option.some.injEq] at hP
      simp only [hA, Option.some.injEq] at hA'
      subst hP hA'
      rw [FreeTopos.Internal.isTy_exp, Bool.and_eq_true] at hIP
      obtain ⟨hIa, hIb⟩ := hIP
      refine ⟨hIb, B, hB,
        judge_const (T := Expr.pi tp (Expr.pi tp (Expr.arrow (tm (exp (v 1) (v 0)))
        (Expr.arrow (tm (v 1)) (tm (v 0)))))) (hsg.get rfl) ?_ rfl⟩
      have hAt := encTy_checks hsg G a _ A hA hIa ΓLF htp
      have hBt := encTy_checks hsg G b _ B hB hIb ΓLF htp
      simp only [tm, tp, exp, Expr.const, Expr.app] at hAt hBt hMtJ hMuJ ⊢
      lf_spine [hAt, hBt, hMtJ, hMuJ]
    · obtain ⟨t, rfl, p, hp, g, hct, hl, hθ, rfl⟩ := FreeTopos.Internal.compile_arr_iff.mp hcomp
      by_cases hfx : k.fixed j = true
      swap
      · rw [encStep_arr, if_neg hfx] at henc
        exact enc_checks_tm hsg (h := .arr j) (d := Rank.ofPrim p)
          (by simp only [TmHead.rank, hp, Option.map_some]) he hΓ
          (rs := [(g, PartialHorn.subst θ p.dom)]) (by rw [List.mapM_cons, hct]; rfl) hl hθ rfl
          ih henc
      rw [encStep_arr, if_pos hfx] at henc
      rcases θ with _ | ⟨θ₀, _ | ⟨θ₁, θ⟩⟩
      · by_cases hkz : j = k.zero
        · subst hkz
          rw [hk.zero, Option.some.injEq] at hp
          subst hp
          simp only [encFixed, List.map_cons, List.map_nil, ↓reduceIte, Option.map_eq_map,
            Option.map_eq_some_iff] at henc
          obtain ⟨Mt, hMt, rfl⟩ := henc
          obtain ⟨hIP, P, hP, hMtJ⟩ := ih t (by simp) X e ΓLF Mt _ he hΓ hMt hct
          simp only [FreeTopos.Internal.zeroPrim, PartialHorn.subst_nil] at hP ⊢
          rw [show encTy k e.length FreeTopos.one = some one from rfl, Option.some.injEq] at hP
          subst hP
          refine ⟨FreeTopos.Internal.isTy_nat, nat, rfl,
            judge_const (T := Expr.arrow (tm one) (tm nat)) (hsg.get rfl) ?_ rfl⟩
          simp only [tm, one, nat, Expr.const, Expr.app] at hMtJ ⊢
          lf_spine [hMtJ]
        · by_cases hks : j = k.succ
          · subst hks
            rw [hk.succ, Option.some.injEq] at hp
            subst hp
            simp only [encFixed, List.map_cons, List.map_nil, hkz, ↓reduceIte, Option.map_eq_map,
              Option.map_eq_some_iff] at henc
            obtain ⟨Mt, hMt, rfl⟩ := henc
            obtain ⟨hIP, P, hP, hMtJ⟩ := ih t (by simp) X e ΓLF Mt _ he hΓ hMt hct
            simp only [FreeTopos.Internal.succPrim, PartialHorn.subst_nil] at hP ⊢
            rw [show encTy k e.length FreeTopos.nat = some nat from rfl, Option.some.injEq] at hP
            subst hP
            refine ⟨FreeTopos.Internal.isTy_nat, nat, rfl,
              judge_const (T := Expr.arrow (tm nat) (tm nat)) (hsg.get rfl) ?_ rfl⟩
            simp only [tm, nat, Expr.const, Expr.app] at hMtJ ⊢
            lf_spine [hMtJ]
          · by_cases hkd : j = k.node
            · subst hkd
              rw [hk.node, Option.some.injEq] at hp
              subst hp
              simp only [encFixed, List.map_cons, List.map_nil, hkz, hks, ↓reduceIte,
                Option.map_eq_map, Option.map_eq_some_iff] at henc
              obtain ⟨Mt, hMt, rfl⟩ := henc
              obtain ⟨hIP, P, hP, hMtJ⟩ := ih t (by simp) X e ΓLF Mt _ he hΓ hMt hct
              simp only [FreeTopos.Internal.nodePrim, PartialHorn.subst_nil] at hP ⊢
              rw [show encTy k e.length
                (FreeTopos.prod FreeTopos.nat (FreeTopos.list FreeTopos.rose)) =
                some (prod nat (list rose)) from rfl, Option.some.injEq] at hP
              subst hP
              refine ⟨FreeTopos.Internal.isTy_rose, rose, rfl,
                judge_const (T := Expr.arrow (tm (prod nat (list rose)))
                (tm rose)) (hsg.get rfl) ?_ rfl⟩
              simp only [tm, nat, rose, prod, list, Expr.const, Expr.app] at hMtJ ⊢
              lf_spine [hMtJ]
            · simp [encFixed, hkz, hks, hkd] at henc
      · by_cases hkn : j = k.nil
        · subst hkn
          rw [hk.nil, Option.some.injEq] at hp
          subst hp
          have hIθ₀ := List.all_eq_true.mp hθ θ₀ (by simp)
          simp only [encFixed, List.map_cons, List.map_nil, ↓reduceIte, Option.bind_eq_bind,
            Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at henc
          obtain ⟨A, hA, Mt, hMt, rfl⟩ := henc
          obtain ⟨hIP, P, hP, hMtJ⟩ := ih t (by simp) X e ΓLF Mt _ he hΓ hMt hct
          rw [subst_nilPrim_dom, show encTy k e.length FreeTopos.one = some one from rfl,
            Option.some.injEq] at hP
          subst hP
          refine ⟨by rw [subst_nilPrim_cod, FreeTopos.Internal.isTy_list]; exact hIθ₀, list A,
            by rw [subst_nilPrim_cod, encTy_list, hA]; rfl,
            judge_const (T := Expr.pi tp (Expr.arrow (tm one) (tm (list (v 0)))))
              (hsg.get rfl) ?_ rfl⟩
          have hAt := encTy_checks hsg G θ₀ _ A hA hIθ₀ ΓLF htp
          simp only [tm, tp, one, list, Expr.const, Expr.app] at hAt hMtJ ⊢
          lf_spine [hAt, hMtJ]
        · by_cases hkc : j = k.cons
          · subst hkc
            rw [hk.cons, Option.some.injEq] at hp
            subst hp
            have hIθ₀ := List.all_eq_true.mp hθ θ₀ (by simp)
            simp only [encFixed, List.map_cons, List.map_nil, hkn, ↓reduceIte, Option.bind_eq_bind,
              Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at henc
            obtain ⟨A, hA, Mt, hMt, rfl⟩ := henc
            obtain ⟨hIP, P, hP, hMtJ⟩ := ih t (by simp) X e ΓLF Mt _ he hΓ hMt hct
            rw [subst_consPrim_dom, encTy_prod, encTy_list, hA] at hP
            simp only [Option.map_some, Option.bind_some, Option.some.injEq] at hP
            subst hP
            refine ⟨by rw [subst_consPrim_cod, FreeTopos.Internal.isTy_list]; exact hIθ₀, list A,
              by rw [subst_consPrim_cod, encTy_list, hA]; rfl,
              judge_const (T := Expr.pi tp (Expr.arrow (tm (prod (v 0) (list (v 0))))
                (tm (list (v 0))))) (hsg.get rfl) ?_ rfl⟩
            have hAt := encTy_checks hsg G θ₀ _ A hA hIθ₀ ΓLF htp
            simp only [tm, tp, prod, list, Expr.const, Expr.app] at hAt hMtJ ⊢
            lf_spine [hAt, hMtJ]
          · by_cases hkl : j = k.lnode
            · subst hkl
              rw [hk.lnode, Option.some.injEq] at hp
              subst hp
              have hIθ₀ := List.all_eq_true.mp hθ θ₀ (by simp)
              simp only [encFixed, List.map_cons, List.map_nil, hkn, hkc, ↓reduceIte,
                Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
                Option.some.injEq] at henc
              obtain ⟨A, hA, Mt, hMt, rfl⟩ := henc
              obtain ⟨hIP, P, hP, hMtJ⟩ := ih t (by simp) X e ΓLF Mt _ he hΓ hMt hct
              rw [subst_lnodePrim_dom, encTy_prod, encTy_list, encTy_lrose, hA] at hP
              simp only [Option.map_some, Option.bind_some, Option.some.injEq] at hP
              subst hP
              refine ⟨by rw [subst_lnodePrim_cod, FreeTopos.Internal.isTy_lrose]; exact hIθ₀,
                lrose A, by rw [subst_lnodePrim_cod, encTy_lrose, hA]; rfl,
                judge_const (T := Expr.pi tp (Expr.arrow (tm (prod (v 0) (list (lrose (v 0)))))
                  (tm (lrose (v 0))))) (hsg.get rfl) ?_ rfl⟩
              have hAt := encTy_checks hsg G θ₀ _ A hA hIθ₀ ΓLF htp
              simp only [tm, tp, prod, list, lrose, Expr.const, Expr.app] at hAt hMtJ ⊢
              lf_spine [hAt, hMtJ]
            · simp [encFixed, hkn, hkc, hkl] at henc
      · rcases θ with _ | ⟨θ₂, _ | ⟨θ₃, θ⟩⟩
        · by_cases hkl : j = k.inl
          · subst hkl
            rw [hk.inl, Option.some.injEq] at hp
            subst hp
            have hIθ₀ := List.all_eq_true.mp hθ θ₀ (by simp)
            have hIθ₁ := List.all_eq_true.mp hθ θ₁ (by simp)
            simp only [encFixed, List.map_cons, List.map_nil, ↓reduceIte, Option.bind_eq_bind,
              Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at henc
            obtain ⟨A, hA, B, hB, Mt, hMt, rfl⟩ := henc
            obtain ⟨hIP, P, hP, hMtJ⟩ := ih t (by simp) X e ΓLF Mt _ he hΓ hMt hct
            rw [subst_inlPrim_dom, hA, Option.some.injEq] at hP
            subst hP
            refine ⟨by rw [subst_inlPrim_cod, FreeTopos.Internal.isTy_coprod, hIθ₀, hIθ₁]; rfl,
              coprod A B, by rw [subst_inlPrim_cod, encTy_coprod, hA, hB]; rfl,
              judge_const (T := Expr.pi tp (Expr.pi tp (Expr.arrow (tm (v 1))
                (tm (coprod (v 1) (v 0)))))) (hsg.get rfl) ?_ rfl⟩
            have hAt := encTy_checks hsg G θ₀ _ A hA hIθ₀ ΓLF htp
            have hBt := encTy_checks hsg G θ₁ _ B hB hIθ₁ ΓLF htp
            simp only [tm, tp, coprod, Expr.const, Expr.app] at hAt hBt hMtJ ⊢
            lf_spine [hAt, hBt, hMtJ]
          · by_cases hkr : j = k.inr
            · subst hkr
              rw [hk.inr, Option.some.injEq] at hp
              subst hp
              have hIθ₀ := List.all_eq_true.mp hθ θ₀ (by simp)
              have hIθ₁ := List.all_eq_true.mp hθ θ₁ (by simp)
              simp only [encFixed, List.map_cons, List.map_nil, hkl, ↓reduceIte,
                Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
                Option.some.injEq] at henc
              obtain ⟨A, hA, B, hB, Mt, hMt, rfl⟩ := henc
              obtain ⟨hIP, P, hP, hMtJ⟩ := ih t (by simp) X e ΓLF Mt _ he hΓ hMt hct
              rw [subst_inrPrim_dom, hB, Option.some.injEq] at hP
              subst hP
              refine ⟨by rw [subst_inrPrim_cod, FreeTopos.Internal.isTy_coprod, hIθ₀, hIθ₁]; rfl,
                coprod A B, by rw [subst_inrPrim_cod, encTy_coprod, hA, hB]; rfl,
                judge_const (T := Expr.pi tp (Expr.pi tp (Expr.arrow (tm (v 0))
                  (tm (coprod (v 1) (v 0)))))) (hsg.get rfl) ?_ rfl⟩
              have hAt := encTy_checks hsg G θ₀ _ A hA hIθ₀ ΓLF htp
              have hBt := encTy_checks hsg G θ₁ _ B hB hIθ₁ ΓLF htp
              simp only [tm, tp, coprod, Expr.const, Expr.app] at hAt hBt hMtJ ⊢
              lf_spine [hAt, hBt, hMtJ]
            · simp [encFixed, hkl, hkr] at henc
        · by_cases hkc : j = k.case
          · subst hkc
            rw [hk.case, Option.some.injEq] at hp
            subst hp
            have hIθ₀ := List.all_eq_true.mp hθ θ₀ (by simp)
            have hIθ₁ := List.all_eq_true.mp hθ θ₁ (by simp)
            have hIθ₂ := List.all_eq_true.mp hθ θ₂ (by simp)
            simp only [encFixed, List.map_cons, List.map_nil, ↓reduceIte, Option.bind_eq_bind,
              Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at henc
            obtain ⟨A, hA, B, hB, C, hC, Mt, hMt, rfl⟩ := henc
            obtain ⟨hIP, P, hP, hMtJ⟩ := ih t (by simp) X e ΓLF Mt _ he hΓ hMt hct
            rw [subst_casePrim_dom, encTy_prod, encTy_exp, encTy_exp, hA, hB, hC] at hP
            simp only [Option.map_some, Option.bind_some, Option.some.injEq] at hP
            subst hP
            refine ⟨by rw [subst_casePrim_cod, FreeTopos.Internal.isTy_exp,
                FreeTopos.Internal.isTy_coprod, hIθ₀, hIθ₁, hIθ₂]; rfl, exp (coprod A B) C, by
                rw [subst_casePrim_cod, encTy_exp, encTy_coprod, hA, hB, hC]; rfl,
              judge_const (T := Expr.pi tp (Expr.pi tp (Expr.pi tp
                (Expr.arrow (tm (prod (exp (v 2) (v 0)) (exp (v 1) (v 0))))
                  (tm (exp (coprod (v 2) (v 1)) (v 0))))))) (hsg.get rfl) ?_ rfl⟩
            have hAt := encTy_checks hsg G θ₀ _ A hA hIθ₀ ΓLF htp
            have hBt := encTy_checks hsg G θ₁ _ B hB hIθ₁ ΓLF htp
            have hCt := encTy_checks hsg G θ₂ _ C hC hIθ₂ ΓLF htp
            simp only [tm, tp, prod, exp, coprod, Expr.const, Expr.app] at hAt hBt hCt hMtJ ⊢
            lf_spine [hAt, hBt, hCt, hMtJ]
          · simp [encFixed, hkc] at henc
        · simp [encFixed] at henc
    · obtain ⟨z, s, m, rfl, -⟩ := FreeTopos.Internal.compile_natRec_iff.mp hcomp
      obtain ⟨⟨zf, hcz⟩, ⟨sf, hcs⟩, mf, hcm⟩ := FreeTopos.Internal.compile_natRec_parts hcomp
      simp only [encStep, List.map_cons, List.map_nil, hcz, Option.bind_eq_bind,
        Option.bind_some, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at henc
      obtain ⟨C, hC, Mz, hMz, Ms, hMs, Mm, hMm, rfl⟩ := henc
      have hΓ' : encCtx k n ((FreeTopos.Internal.extEnv X r.2 e).map Prod.snd) =
          some (tm C :: ΓLF) := by
        simp only [FreeTopos.Internal.extEnv, List.map_cons, List.map_map]
        exact encCtx_cons (by simpa only [List.length_map] using hC)
          (by simpa [Function.comp_def] using hΓ)
      obtain ⟨hIr2, A₁, hA₁, hMzJ⟩ := ih z (by simp) X e ΓLF Mz _ he hΓ hMz hcz
      obtain ⟨-, A₂, hA₂, hMsJ⟩ := ih s (by simp) _ _ _ Ms _ (extEnv_isTy hIr2 he) hΓ' hMs hcs
      obtain ⟨-, N, hN, hMmJ⟩ := ih m (by simp) X e ΓLF Mm _ he hΓ hMm hcm
      rw [hC, Option.some.injEq] at hA₁
      rw [length_extEnv, encTy_add hC, Option.some.injEq] at hA₂
      subst hA₁ hA₂
      rw [show encTy k e.length FreeTopos.nat = some nat from rfl, Option.some.injEq] at hN
      subst hN
      have hfJ := judge_lam hMsJ
      refine ⟨hIr2, C, hC, judge_const (T := Expr.pi tp (Expr.arrow (tm (v 0))
        (Expr.arrow (Expr.arrow (tm (v 0)) (tm (v 0))) (Expr.arrow (tm nat) (tm (v 0))))))
        (hsg.get rfl) ?_ rfl⟩
      have hCt := encTy_checks hsg G r.2 _ C hC hIr2 ΓLF htp
      simp only [tm, tp, nat, Expr.const, Expr.app, Expr.pi] at hCt hMzJ hfJ hMmJ ⊢
      lf_spine [hCt, hMzJ, hfJ, hMmJ]
    · obtain ⟨z, s, m, rfl, -⟩ := FreeTopos.Internal.compile_listRec_iff.mp hcomp
      obtain ⟨mf, a, hcm, ⟨zf, hcz⟩, sf, hcs⟩ := FreeTopos.Internal.compile_listRec_parts hcomp
      simp only [encStep, List.map_cons, List.map_nil, hcz, hcm,
        FreeTopos.Internal.listPart_eq_some.mpr rfl, Option.bind_eq_bind, Option.bind_some,
        Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at henc
      obtain ⟨A, hA, C, hC, Mz, hMz, Ms, hMs, Mm, hMm, rfl⟩ := henc
      have hΓ' : encCtx k n ((FreeTopos.Internal.extEnv (FreeTopos.prod X a) r.2
          (FreeTopos.Internal.extEnv X a e)).map Prod.snd) =
          some (tm (C.rename (· + 1)) :: tm A :: ΓLF) := by
        simp only [FreeTopos.Internal.extEnv, List.map_cons, List.map_map]
        refine encCtx_cons ?_ (encCtx_cons (by simpa only [List.length_map] using hA)
          (by simpa [Function.comp_def] using hΓ))
        simpa only [List.length_map, List.length_cons] using encTy_add (d := 1) hC
      obtain ⟨hIr2, A₁, hA₁, hMzJ⟩ := ih z (by simp) X e ΓLF Mz _ he hΓ hMz hcz
      obtain ⟨hIL, L, hL, hMmJ⟩ := ih m (by simp) X e ΓLF Mm _ he hΓ hMm hcm
      have hIa : FreeTopos.Internal.IsTy G n a = true := by
        rwa [FreeTopos.Internal.isTy_list] at hIL
      obtain ⟨-, A₂, hA₂, hMsJ⟩ := ih s (by simp) _ _ _ Ms _
        (extEnv_isTy hIr2 (extEnv_isTy hIa he)) hΓ' hMs hcs
      rw [hC, Option.some.injEq] at hA₁
      rw [length_extEnv, length_extEnv, Nat.add_assoc, encTy_add hC, Option.some.injEq] at hA₂
      subst hA₁ hA₂
      rw [encTy_list, hA, Option.map_some, Option.some.injEq] at hL
      subst hL
      have hfJ := judge_lam (judge_lam hMsJ)
      refine ⟨hIr2, C, hC, judge_const (T := Expr.pi tp (Expr.pi tp (Expr.arrow (tm (v 0))
        (Expr.arrow (Expr.arrow (tm (v 1)) (Expr.arrow (tm (v 0)) (tm (v 0))))
          (Expr.arrow (tm (list (v 1))) (tm (v 0))))))) (hsg.get rfl) ?_ rfl⟩
      have hAt := encTy_checks hsg G a _ A hA hIa ΓLF htp
      have hCt := encTy_checks hsg G r.2 _ C hC hIr2 ΓLF htp
      simp only [tm, tp, list, Expr.const, Expr.app, Expr.pi] at hAt hCt hMzJ hfJ hMmJ ⊢
      lf_spine [hAt, hCt, hMzJ, hfJ, hMmJ]
    · obtain ⟨s, m, -, -, -, -, -, rfl, hIc, -⟩ := FreeTopos.Internal.compile_roseRec_iff.mp hcomp
      obtain ⟨hct, hrc, mf, t, a, F, hcm, ht, sf, hcs⟩ :=
        FreeTopos.Internal.compile_roseRec_parts hcomp
      simp only [encStep, List.map_cons, List.map_nil, hcm, Option.bind_eq_bind,
        Option.bind_some] at henc
      split at henc
      · next htl htc =>
        obtain rfl : t = FreeTopos.rose := by
          rw [← RoseTree.node_label_children t, htl, htc]
          rfl
        obtain ⟨rfl, rfl⟩ : a = FreeTopos.nat ∧ F = FreeTopos.roseRec := by
          simpa [FreeTopos.Internal.roseParts] using ht.symm
        simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at henc
        obtain ⟨C, hC, Ms, hMs, Mm, hMm, rfl⟩ := henc
        have hpc : encTy k e.length (FreeTopos.prod FreeTopos.nat (FreeTopos.list c)) =
            some (prod nat (list C)) := by rw [encTy_prod, encTy_list, hC]; rfl
        have hΓ' : encCtx k n ((FreeTopos.Internal.extEnv X (FreeTopos.prod FreeTopos.nat
            (FreeTopos.list c)) e).map Prod.snd) = some (tm (prod nat (list C)) :: ΓLF) := by
          simp only [FreeTopos.Internal.extEnv, List.map_cons, List.map_map]
          exact encCtx_cons (by simpa only [List.length_map] using hpc)
            (by simpa [Function.comp_def] using hΓ)
        have hIp : FreeTopos.Internal.IsTy G n
            (FreeTopos.prod FreeTopos.nat (FreeTopos.list c)) = true := by
          rw [FreeTopos.Internal.isTy_prod, FreeTopos.Internal.isTy_list, hIc]; rfl
        obtain ⟨-, A₂, hA₂, hMsJ⟩ := ih s (by simp) _ _ _ Ms _ (extEnv_isTy hIp he) hΓ' hMs hcs
        obtain ⟨-, T, hT, hMmJ⟩ := ih m (by simp) X e ΓLF Mm _ he hΓ hMm hcm
        rw [length_extEnv, ← hrc, encTy_add (hrc ▸ hC), Option.some.injEq] at hA₂
        subst hA₂
        rw [show encTy k e.length FreeTopos.rose = some rose from rfl, Option.some.injEq] at hT
        subst hT
        have hfJ := judge_lam hMsJ
        refine ⟨by rw [hrc]; exact hIc, C, by rw [hrc]; exact hC,
          judge_const (T := Expr.pi tp (Expr.arrow
          (Expr.arrow (tm (prod nat (list (v 0)))) (tm (v 0))) (Expr.arrow (tm rose) (tm (v 0)))))
          (hsg.get rfl) ?_ rfl⟩
        have hCt := encTy_checks hsg G c _ C hC hIc ΓLF htp
        simp only [tm, tp, nat, rose, prod, list, Expr.const, Expr.app, Expr.pi] at hCt hfJ hMmJ ⊢
        lf_spine [hCt, hfJ, hMmJ]
      · next a' htl htc =>
        obtain rfl : t = FreeTopos.lrose a' := by
          rw [← RoseTree.node_label_children t, htl, htc]
          rfl
        rw [roseParts_lrose, Option.some.injEq, Prod.mk.injEq] at ht
        obtain ⟨rfl, rfl⟩ := ht
        simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at henc
        obtain ⟨A, hA, C, hC, Ms, hMs, Mm, hMm, rfl⟩ := henc
        have hpc : encTy k e.length (FreeTopos.prod a' (FreeTopos.list c)) =
            some (prod A (list C)) := by
          rw [encTy_prod, encTy_list, hA, hC]; rfl
        have hΓ' : encCtx k n ((FreeTopos.Internal.extEnv X (FreeTopos.prod a'
            (FreeTopos.list c)) e).map Prod.snd) = some (tm (prod A (list C)) :: ΓLF) := by
          simp only [FreeTopos.Internal.extEnv, List.map_cons, List.map_map]
          exact encCtx_cons (by simpa only [List.length_map] using hpc)
            (by simpa [Function.comp_def] using hΓ)
        obtain ⟨hIT, T, hT, hMmJ⟩ := ih m (by simp) X e ΓLF Mm _ he hΓ hMm hcm
        have hIa' : FreeTopos.Internal.IsTy G n a' = true := by
          rwa [FreeTopos.Internal.isTy_lrose] at hIT
        have hIp : FreeTopos.Internal.IsTy G n (FreeTopos.prod a' (FreeTopos.list c)) = true := by
          rw [FreeTopos.Internal.isTy_prod, FreeTopos.Internal.isTy_list, hIa', hIc]; rfl
        obtain ⟨-, A₂, hA₂, hMsJ⟩ := ih s (by simp) _ _ _ Ms _ (extEnv_isTy hIp he) hΓ' hMs hcs
        rw [length_extEnv, ← hrc, encTy_add (hrc ▸ hC), Option.some.injEq] at hA₂
        subst hA₂
        rw [encTy_lrose, hA, Option.map_some, Option.some.injEq] at hT
        subst hT
        have hfJ := judge_lam hMsJ
        refine ⟨by rw [hrc]; exact hIc, C, by rw [hrc]; exact hC,
          judge_const (T := Expr.pi tp (Expr.pi tp (Expr.arrow
          (Expr.arrow (tm (prod (v 1) (list (v 0)))) (tm (v 0)))
          (Expr.arrow (tm (lrose (v 1))) (tm (v 0)))))) (hsg.get rfl) ?_ rfl⟩
        have hAt := encTy_checks hsg G a' _ A hA hIa' ΓLF htp
        have hCt := encTy_checks hsg G c _ C hC hIc ΓLF htp
        simp only [tm, tp, prod, list, lrose, Expr.const, Expr.app, Expr.pi] at hAt hCt hfJ hMmJ ⊢
        lf_spine [hAt, hCt, hfJ, hMmJ]
      · simp at henc
    · -- a definition
      obtain ⟨d, rs, hd, hrs, hθl, hθty, hrst, rfl⟩ :=
        FreeTopos.Internal.compile_defn_iff.mp hcomp
      rw [encStep_defn] at henc
      exact enc_checks_tm hsg (h := .defn j) (d := Rank.ofDefn d)
        (by simp only [TmHead.rank, hd, Option.bind_some, Option.map_some,
          FreeTopos.Internal.Definition.language?]) he hΓ hrs hθl hθty hrst ih henc
    · obtain ⟨t, u, rfl, f, a, hct, g, hcu, rfl⟩ := FreeTopos.Internal.compile_eq_iff.mp hcomp
      simp only [encStep, List.map_cons, List.map_nil, hct, Option.bind_eq_bind,
        Option.bind_some, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at henc
      obtain ⟨A, hA, Mt, hMt, Mu, hMu, rfl⟩ := henc
      obtain ⟨hIA₁, A₁, hA₁, hMtJ⟩ := ih t (by simp) X e ΓLF Mt _ he hΓ hMt hct
      obtain ⟨hIA₂, A₂, hA₂, hMuJ⟩ := ih u (by simp) X e ΓLF Mu _ he hΓ hMu hcu
      simp only [hA, Option.some.injEq] at hA₁ hA₂
      subst hA₁ hA₂
      refine ⟨FreeTopos.Internal.isTy_omega, omega, rfl,
        judge_const (T := Expr.pi tp (Expr.arrow (tm (v 0))
        (Expr.arrow (tm (v 0)) (tm omega)))) (hsg.get rfl) ?_ rfl⟩
      have hAt := encTy_checks hsg G a _ A hA hIA₁ ΓLF htp
      simp only [tm, tp, omega, Expr.const, Expr.app] at hAt hMtJ hMuJ ⊢
      lf_spine [hAt, hMtJ, hMuJ]

end Soundness

section Completeness

variable {G : FreeTopos.Internal.Globals} {n : ℕ} {k : PrimIdx}

/-- An application of a constant of the language to types in {lit}`n` object variables, as many
as its object parameters, and to terms that compile to the instances of its parameters' types
compiles to the instance of its value's type. -/
theorem compile_label {h : TmHead} {d : Rank} (hd : h.rank G = some d) {θ : List PartialHorn.Tree}
    {ss : List MTerm} {rs : List (PartialHorn.Tree × PartialHorn.Tree)} {X : PartialHorn.Tree}
    {e : MEnv} (hrs : ss.mapM (fun s ↦ FreeTopos.Internal.compile G n s X e) = some rs)
    (hθl : θ.length = d.arity) (hθty : θ.all (FreeTopos.Internal.IsTy G n) = true)
    (hrst : rs.map Prod.snd = d.params.map (PartialHorn.subst θ)) :
    ∃ f, FreeTopos.Internal.compile G n (RoseTree.node (h.label θ) ss) X e =
      some (f, PartialHorn.subst θ d.type) := by
  cases h with
  | defn kd =>
    obtain ⟨d', hd', rfl⟩ := Option.map_eq_some_iff.mp hd
    obtain ⟨D, hD, hl⟩ := Option.bind_eq_some_iff.mp hd'
    cases D with
    | language d₀ =>
      obtain rfl := Option.some.inj hl
      exact ⟨_, FreeTopos.Internal.compile_defn_iff.mpr ⟨_, rs, hD, hrs, hθl, hθty, hrst, rfl⟩⟩
    | object _ _ => exact nomatch hl
  | arr kp =>
    obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp hd
    rw [PartialHorn.mapM_eq_some_iff] at hrs
    rcases rs with _ | ⟨r₀, _ | ⟨_, _⟩⟩
    · exact nomatch hrst
    · rcases ss with _ | ⟨s₀, _ | ⟨s₁, ss⟩⟩
      · exact Nat.noConfusion (congrArg List.length hrs)
      · obtain ⟨hs₀, -⟩ := List.cons.inj hrs
        obtain ⟨hr₀, -⟩ := List.cons.inj hrst
        rw [show r₀ = (r₀.1, PartialHorn.subst θ p.dom) from Prod.ext rfl hr₀] at hs₀
        exact ⟨_, FreeTopos.Internal.compile_arr_iff.mpr ⟨s₀, rfl, p, hp, r₀.1, hs₀, hθl, hθty,
          rfl⟩⟩
      · exact absurd (congrArg List.length hrs)
          (by simp only [List.length_map, List.length_cons, List.length_nil]; omega)
    · exact absurd (congrArg List.length hrst)
        (by simp only [List.length_map, List.length_cons, List.length_nil, Rank.ofPrim]; omega)

/-- The conclusion of the completeness of the encoding in {lit}`n` object variables at a term, an
environment and a type: the term decodes, at the offset of the environment's variables, to a term
of the internal language that compiles in the environment to a type that the type encodes at that
offset, and whose encoding it is. -/
def TmConcl (G : FreeTopos.Internal.Globals) (n : ℕ) (k : PrimIdx) (M : Expr)
    (X : PartialHorn.Tree) (e : MEnv) (A : Expr) : Prop :=
  ∃ s r, dec k M e.length = some s ∧ FreeTopos.Internal.compile G n s X e = some r ∧
    encTy k e.length r.2 = some A ∧ enc G n k s X e = some M

/-- The completeness of the encoding at a term, of the family of terms of a type, and, where the
term checks against a product of families of terms, or against a product of families of terms
into such a product, at the body of the abstraction it is, or of the abstraction that is its body,
in every environment of the extended types. -/
def TmComplete (sg : Sig) (G : FreeTopos.Internal.Globals) (n : ℕ) (k : PrimIdx) (M : Expr) :
    Prop :=
  (∀ (X : PartialHorn.Tree) (e : MEnv) (ΓLF : Ctx) (A : Expr),
    encCtx k n (e.map Prod.snd) = some ΓLF →
    judge sg M ΓLF (.check (tm A)) = true → TmConcl G n k M X e A) ∧
  (∀ (Γ : List PartialHorn.Tree) (ΓLF : Ctx) (a : PartialHorn.Tree) (A' B' : Expr),
    encCtx k n Γ = some ΓLF → encTy k Γ.length a = some A' →
    judge sg M ΓLF (.check (Expr.pi (tm A') (tm B'))) = true →
    ∃ body, M = Expr.lam body ∧
      ∀ (X : PartialHorn.Tree) (e : MEnv), e.map Prod.snd = a :: Γ →
        TmConcl G n k body X e B') ∧
  (∀ (Γ : List PartialHorn.Tree) (ΓLF : Ctx) (a b : PartialHorn.Tree) (A' B' C' : Expr),
    encCtx k n Γ = some ΓLF → encTy k Γ.length a = some A' → encTy k (Γ.length + 1) b = some B' →
    judge sg M ΓLF (.check (Expr.pi (tm A') (Expr.pi (tm B') (tm C')))) = true →
    ∃ body, M = Expr.lam (Expr.lam body) ∧
      ∀ (X : PartialHorn.Tree) (e : MEnv), e.map Prod.snd = b :: a :: Γ →
        TmConcl G n k body X e C')

/-- The completeness of the encoding at a left injection. -/
theorem tmComplete_inl (hsg : SigExt G k sg) (hk : k.Valid G) {X1 X2 X3 : Expr}
    (ih : TmComplete sg G n k X3)
    {X : PartialHorn.Tree} {e : MEnv} {ΓLF : Ctx} {A : Expr}
    (hΓ : encCtx k n (e.map Prod.snd) = some ΓLF)
    (hS : spine ΓLF (Expr.pi tp (Expr.pi tp (Expr.arrow (tm (v 1)) (tm (coprod (v 1) (v 0))))))
      ([X1, X2, X3].map fun m ↦ (m, judge sg m)) = some (tm A)) :
    TmConcl G n k (Expr.const 50 [X1, X2, X3]) X e A := by
  unfold TmConcl
  have hheads₀ := encCtx_heads₀ hΓ
  simp only [List.length_map] at hheads₀
  simp only [List.map_cons, List.map_nil] at hS
  have hT := spine_tp₂ hS
  obtain ⟨a, ha, hIa⟩ := tyComplete hsg hheads₀ X1 hT.1
  obtain ⟨b, hb, hIb⟩ := tyComplete hsg hheads₀ X2 hT.2
  simp only [tm, tp, coprod, Expr.const, Expr.app] at hS
  lf_spine_at hS [Option.bind_eq_some_iff, Option.ite_none_right_eq_some]
  obtain ⟨-, -, ht, hA⟩ := hS
  simp only [node_inj, List.cons.injEq, and_true, true_and] at hA
  subst hA
  obtain ⟨st, ⟨g, c'⟩, hdt, hct, hrt, het⟩ := ih.1 X e ΓLF X1 hΓ ht
  obtain rfl := encTy_inj ha hrt
  refine ⟨FreeTopos.Internal.Term.arr k.inl [a, b] st, _, ?_,
    FreeTopos.Internal.compile_arr_iff.mpr ⟨st, rfl, _, hk.inl, g,
      by rw [subst_inlPrim_dom]; exact hct, rfl,
      by simp [hIa, hIb], rfl⟩,
    by rw [subst_inlPrim_cod, encTy_coprod, ha, hb]; rfl, ?_⟩
  · rw [Expr.const, Expr.app, dec_node]
    simp only [List.map_cons, List.map_nil, decStep, hdt, decTy_encTy _ a X1 ha,
      decTy_encTy _ b X2 hb, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  · rw [FreeTopos.Internal.Term.arr, enc_node, encStep_arr,
      if_pos (k.fixed_of_mem (by simp only [List.mem_cons, true_or, or_true]))]
    simp only [encFixed, List.map_cons, List.map_nil, ↓reduceIte, ha, hb, het,
      Option.bind_eq_bind, Option.bind_some, Option.pure_def]
    rfl

/-- The completeness of the encoding at a right injection. -/
theorem tmComplete_inr (hsg : SigExt G k sg) (hk : k.Valid G) {X1 X2 X3 : Expr}
    (ih : TmComplete sg G n k X3)
    {X : PartialHorn.Tree} {e : MEnv} {ΓLF : Ctx} {A : Expr}
    (hΓ : encCtx k n (e.map Prod.snd) = some ΓLF)
    (hS : spine ΓLF (Expr.pi tp (Expr.pi tp (Expr.arrow (tm (v 0)) (tm (coprod (v 1) (v 0))))))
      ([X1, X2, X3].map fun m ↦ (m, judge sg m)) = some (tm A)) :
    TmConcl G n k (Expr.const 51 [X1, X2, X3]) X e A := by
  unfold TmConcl
  have hheads₀ := encCtx_heads₀ hΓ
  simp only [List.length_map] at hheads₀
  simp only [List.map_cons, List.map_nil] at hS
  have hT := spine_tp₂ hS
  obtain ⟨a, ha, hIa⟩ := tyComplete hsg hheads₀ X1 hT.1
  obtain ⟨b, hb, hIb⟩ := tyComplete hsg hheads₀ X2 hT.2
  simp only [tm, tp, coprod, Expr.const, Expr.app] at hS
  lf_spine_at hS [Option.bind_eq_some_iff, Option.ite_none_right_eq_some]
  obtain ⟨-, -, ht, hA⟩ := hS
  simp only [node_inj, List.cons.injEq, and_true, true_and] at hA
  subst hA
  obtain ⟨st, ⟨g, c'⟩, hdt, hct, hrt, het⟩ := ih.1 X e ΓLF X2 hΓ ht
  obtain rfl := encTy_inj hb hrt
  refine ⟨FreeTopos.Internal.Term.arr k.inr [a, b] st, _, ?_,
    FreeTopos.Internal.compile_arr_iff.mpr ⟨st, rfl, _, hk.inr, g,
      by rw [subst_inrPrim_dom]; exact hct, rfl,
      by simp [hIa, hIb], rfl⟩,
    by rw [subst_inrPrim_cod, encTy_coprod, ha, hb]; rfl, ?_⟩
  · rw [Expr.const, Expr.app, dec_node]
    simp only [List.map_cons, List.map_nil, decStep, hdt, decTy_encTy _ a X1 ha,
      decTy_encTy _ b X2 hb, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  · rw [FreeTopos.Internal.Term.arr, enc_node, encStep_arr,
      if_pos (k.fixed_of_mem (by simp only [List.mem_cons, true_or, or_true]))]
    simp only [encFixed, List.map_cons, List.map_nil, hk.inr_ne_inl, ↓reduceIte, ha, hb, het,
      Option.bind_eq_bind, Option.bind_some, Option.pure_def]
    rfl

/-- The completeness of the encoding at a case analysis. -/
theorem tmComplete_case (hsg : SigExt G k sg) (hk : k.Valid G) {X1 X2 X3 X4 : Expr}
    (ih : TmComplete sg G n k X4)
    {X : PartialHorn.Tree} {e : MEnv} {ΓLF : Ctx} {A : Expr}
    (hΓ : encCtx k n (e.map Prod.snd) = some ΓLF)
    (hS : spine ΓLF (Expr.pi tp (Expr.pi tp (Expr.pi tp (Expr.arrow (tm (prod (exp (v 2) (v 0))
      (exp (v 1) (v 0)))) (tm (exp (coprod (v 2) (v 1)) (v 0)))))))
      ([X1, X2, X3, X4].map fun m ↦ (m, judge sg m)) = some (tm A)) :
    TmConcl G n k (Expr.const 52 [X1, X2, X3, X4]) X e A := by
  unfold TmConcl
  have hheads₀ := encCtx_heads₀ hΓ
  simp only [List.length_map] at hheads₀
  simp only [List.map_cons, List.map_nil] at hS
  have hT := spine_tp₃ hS
  obtain ⟨a, ha, hIa⟩ := tyComplete hsg hheads₀ X1 hT.1
  obtain ⟨b, hb, hIb⟩ := tyComplete hsg hheads₀ X2 hT.2.1
  obtain ⟨c, hc, hIc⟩ := tyComplete hsg hheads₀ X3 hT.2.2
  simp only [tm, tp, prod, exp, coprod, Expr.const, Expr.app] at hS
  lf_spine_at hS [Option.bind_eq_some_iff, Option.ite_none_right_eq_some]
  obtain ⟨-, -, -, ht, hA⟩ := hS
  simp only [node_inj, List.cons.injEq, and_true, true_and] at hA
  subst hA
  have hdom : encTy k e.length (FreeTopos.prod (FreeTopos.exp a c) (FreeTopos.exp b c)) =
      some (prod (exp X1 X3) (exp X2 X3)) := by
    rw [encTy_prod, encTy_exp, encTy_exp, ha, hb, hc]; rfl
  obtain ⟨st, ⟨g, c'⟩, hdt, hct, hrt, het⟩ :=
    ih.1 X e ΓLF (prod (exp X1 X3) (exp X2 X3)) hΓ ht
  obtain rfl := encTy_inj hdom hrt
  refine ⟨FreeTopos.Internal.Term.arr k.case [a, b, c] st, _, ?_,
    FreeTopos.Internal.compile_arr_iff.mpr ⟨st, rfl, _, hk.case, g,
      by rw [subst_casePrim_dom]; exact hct, rfl,
      by simp [hIa, hIb, hIc],
      rfl⟩,
    by rw [subst_casePrim_cod, encTy_exp, encTy_coprod, ha, hb, hc]; rfl, ?_⟩
  · rw [Expr.const, Expr.app, dec_node]
    simp only [List.map_cons, List.map_nil, decStep, hdt, decTy_encTy _ a X1 ha,
      decTy_encTy _ b X2 hb, decTy_encTy _ c X3 hc, Option.bind_eq_bind, Option.bind_some,
      Option.pure_def]
  · rw [FreeTopos.Internal.Term.arr, enc_node, encStep_arr,
      if_pos (k.fixed_of_mem (by simp only [List.mem_cons, true_or, or_true]))]
    simp only [encFixed, List.map_cons, List.map_nil, ↓reduceIte, ha, hb, hc, het,
      Option.bind_eq_bind, Option.bind_some, Option.pure_def]
    rfl

/-- Encoding is onto the canonical LF terms: every canonical term of the family of terms of a type,
in an encoded context, decodes to a term of the internal language that compiles, in an
environment of the context's types, to a type the type encodes, and whose encoding it is. -/
theorem tmComplete (hsg : SigExt G k sg) (hk : k.Valid G) :
    ∀ M : Expr, TmComplete sg G n k M :=
  RoseTree.ind fun l cs ih ↦ by
    refine ⟨fun X e ΓLF A hΓ hj ↦ ?_, fun Γ ΓLF a A' B' hΓ ha hj ↦ ?_,
      fun Γ ΓLF a b A' B' C' hΓ ha hb hj ↦ ?_⟩
    rotate_left
    · obtain ⟨body, hbody, hbJ⟩ := judge_check_pi_inv hj
      obtain ⟨rfl, rfl⟩ := node_inj.mp hbody
      refine ⟨body, rfl, fun X e he ↦ ?_⟩
      exact (ih body (by simp)).1 X e (tm A' :: ΓLF) B' (by rw [he]; exact encCtx_cons ha hΓ)
        hbJ
    · obtain ⟨body, hbody, hbJ⟩ := judge_check_pi_inv hj
      obtain ⟨rfl, rfl⟩ := node_inj.mp hbody
      obtain ⟨body', rfl, hb'⟩ :=
        (ih body (by simp)).2.1 (a :: Γ) (tm A' :: ΓLF) b B' C' (encCtx_cons ha hΓ) hb hbJ
      exact ⟨body', rfl, hb'⟩
    unfold TmConcl
    obtain ⟨h, ms, hM⟩ := judge_atomic_app rfl hj
    obtain ⟨rfl, rfl⟩ := node_inj.mp hM
    obtain ⟨C, hC, hS⟩ := judge_app_inv hj
    have hheads₀ := encCtx_heads₀ hΓ
    simp only [List.length_map] at hheads₀
    rcases h with i | c
    · rcases varType_encCtx_inv hΓ hC with ⟨a, A', ha, hA', rfl⟩ | ⟨-, -, rfl⟩
      swap
      · exact absurd (show some 6 = some 0 from (spine_headDepth _ _ _ rfl hS).1) (by decide)
      rw [List.length_map] at hA'
      have hlen := (spine_headDepth _ _ _ rfl hS).2
      rw [show (tm A).headDepth.2 = 0 from rfl, show (tm A').headDepth.2 = 0 from rfl,
        List.length_map] at hlen
      obtain rfl := List.length_eq_zero_iff.mp (by omega : cs.length = 0)
      simp only [List.map_nil, spine, List.foldlM_nil, Option.pure_def, Option.some.injEq,
        tm, Expr.const, Expr.app, node_inj, List.cons.injEq, and_true, true_and] at hS
      subst hS
      obtain ⟨f, hf⟩ := env_of_map_snd ha
      refine ⟨FreeTopos.Internal.Term.var i, (f, a), rfl,
        FreeTopos.Internal.compile_var_iff.mpr ⟨rfl, hf⟩, hA', ?_⟩
      rw [FreeTopos.Internal.Term.var, enc_node]
      rfl
    · have hCs := Sig.ok_typeShape hsg.ok c C hC
      obtain ⟨h₁, h₂⟩ := spine_headDepth _ C _ hCs hS
      by_cases hlt : c < sig.length
      swap
      · -- a definition
        obtain ⟨i, rfl⟩ : ∃ i, c = sig.length + i := ⟨c - sig.length, by omega⟩
        have hC' : sg[sig.length + i]? = some C := hC
        obtain ⟨hh, m, p, he⟩ := hsg.tmDefs i C hC' (by rw [← h₁]; rfl)
        obtain ⟨d, T, hfind, hfx, hd, rfl, rfl, hdok, hT, hsgc⟩ := hsg.tms i hh m p he
        obtain rfl := Option.some.inj (hsgc.symm.trans hC')
        simp only [Rank.ok, Bool.and_eq_true, List.all_eq_true] at hdok
        simp only [defTy, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
          Option.some.injEq] at hT
        obtain ⟨ΓT, hΓT, Td, hTd, rfl⟩ := hT
        obtain ⟨T', hT', hT'len, hT'i⟩ := encCtx_reverse hΓT
        have hΓlen : ΓT.reverse.length = d.arity + d.params.length := by
          rw [hT', List.length_append, List.length_replicate, hT'len]
        have hDs : ∀ D ∈ ΓT.reverse, D = tp ∨ ∃ A, D = tm A := fun D hD ↦
          encCtx_tpTm hΓT D (List.mem_reverse.mp hD)
        obtain ⟨hlen, hargs, R', hR', hS'⟩ :=
          spine_piTele_gen (J := judge sg) (P := tm A) rfl hDs hS
        rw [hΓlen] at hlen hR' hS'
        -- the types decode
        have htys : List.Forall₂ (fun M M' ↦ ∃ x, decTy k e.length M = some x ∧
            (encTy k e.length x = some M' ∧ FreeTopos.Internal.IsTy G n x = true))
            (cs.take d.arity) (cs.take d.arity) :=
          forall₂_of_getElem rfl fun idx hi₁ _ ↦ by
            have hidx : idx < d.arity := by rw [List.length_take] at hi₁; omega
            obtain ⟨D', M, hD', hM, hJ⟩ := hargs idx tp (by
              rw [hT', List.getElem?_append_left (by rw [List.length_replicate]; exact hidx),
                List.getElem?_replicate_of_lt hidx])
            obtain rfl := hsubs_tp hD'
            rw [List.getElem_take]
            obtain rfl := Option.some.inj ((List.getElem?_eq_getElem (by omega)).symm.trans hM)
            obtain ⟨x, hx, hxt⟩ := tyComplete hsg hheads₀ _ hJ
            exact ⟨x, decTy_encTy _ x _ hx, hx, hxt⟩
        obtain ⟨xs, hxsM, hxs⟩ := mapM_of_forall₂ htys
        have hxs' : List.Forall₂ (fun X x ↦ encTy k e.length x = some X) (cs.take d.arity) xs :=
          List.Forall₂.flip (R := fun X x ↦ encTy k e.length x = some X) (hxs.imp fun _ _ h ↦ h.1)
        have hxl : xs.length = d.arity := by
          rw [← hxs'.length_eq, List.length_take]
          omega
        have hMsl : ((cs.drop d.arity).take d.params.length).length = d.params.length := by
          rw [List.length_take, List.length_drop]
          omega
        -- the type of the application
        obtain ⟨E, hE, hEenc⟩ := hsubs_tm_encTy hxs' hMsl hTd
          (by rw [hxl]; exact FreeTopos.Internal.scoped_of_isTy (G := G) _ hdok.2)
        rw [take_add'] at hR'
        obtain rfl := Option.some.inj (hR'.symm.trans hE)
        have hdrop : cs.drop (d.arity + d.params.length) = [] := by
          rcases hrest : cs.drop (d.arity + d.params.length) with _ | ⟨x, rest⟩
          · rfl
          · rw [hrest, List.map_cons] at hS'
            exact nomatch hS'
        rw [hdrop] at hS'
        obtain rfl : E = A := tm_inj (Option.some.inj hS')
        have hcl : cs.length = d.arity + d.params.length := by
          have := List.drop_eq_nil_iff.mp hdrop
          omega
        have hMs : (cs.drop d.arity).take d.params.length = cs.drop d.arity :=
          List.take_of_length_le (by rw [List.length_drop]; omega)
        rw [hMs] at hMsl
        -- the terms decode, to terms of the instances of the parameters' types
        have hterms : List.Forall₂ (fun M P ↦ ∃ s, dec k M e.length = some s ∧
            (enc G n k s X e = some M ∧ ∃ r, FreeTopos.Internal.compile G n s X e = some r ∧
              r.2 = PartialHorn.subst xs.reverse P))
            (cs.drop d.arity) d.params.reverse :=
          forall₂_of_getElem (by rw [hMsl, List.length_reverse]) fun i' hi₁ hi₂ ↦ by
            have hi' : i' < d.params.length := by rw [List.length_reverse] at hi₂; exact hi₂
            obtain ⟨A₀, hA₀, hA₀e⟩ := hT'i i' _ (List.getElem?_eq_getElem hi₂)
            obtain ⟨D', M, hD', hM, hJ⟩ := hargs (d.arity + i') (tm A₀) (by
              rw [hT', List.getElem?_append_right (by rw [List.length_replicate]; omega),
                List.length_replicate, Nat.add_sub_cancel_left]
              exact hA₀)
            rw [take_add', hsubs_append, List.length_take, List.length_drop,
              Nat.min_eq_left (by omega)] at hD'
            have hPty := hdok.1 _ (List.mem_reverse.mp (List.getElem_mem hi₂))
            have hPs := FreeTopos.Internal.scoped_of_isTy (G := G) _ hPty
            obtain ⟨E', hE', hE'enc⟩ := hsubs_tm_encTy hxs' (Ms := (cs.drop d.arity).take i')
              (by rw [List.length_take, List.length_drop]; omega) hA₀e
              (by rw [hxl]; exact hPs)
            rw [hsubs_append, List.length_take, List.length_drop, Nat.min_eq_left (by omega)]
              at hE'
            obtain rfl := Option.some.inj (hD'.symm.trans hE')
            rw [List.getElem_drop]
            obtain rfl := Option.some.inj ((List.getElem?_eq_getElem (by omega)).symm.trans hM)
            obtain ⟨s', r, hds, hcs, hrs, hes⟩ :=
              (ih _ (List.getElem_mem (by omega))).1 X e ΓLF E' hΓ hJ
            exact ⟨s', hds, hes, r, hcs, encTy_inj hrs hE'enc⟩
        obtain ⟨ss, hssM, hssi⟩ := mapM_of_forall₂_idx (f := fun M ↦ dec k M e.length) hterms
        have hssl : ss.length = d.params.length := by rw [length_of_mapM hssM, hMsl]
        have hcomps : List.Forall₂ (fun s P ↦ ∃ r, FreeTopos.Internal.compile G n s X e = some r ∧
            r.2 = PartialHorn.subst xs.reverse P) ss d.params.reverse :=
          forall₂_of_getElem (by rw [hssl, List.length_reverse]) fun i' hi₁ hi₂ ↦
            (hssi i' _ _ _ (List.getElem?_eq_getElem (by rw [hMsl]; omega))
              (List.getElem?_eq_getElem hi₁) (List.getElem?_eq_getElem hi₂)).2
        obtain ⟨rs, hrsM, hrsi⟩ := mapM_of_forall₂_idx
          (f := fun s ↦ FreeTopos.Internal.compile G n s X e)
          (R := fun _ r P ↦ r.2 = PartialHorn.subst xs.reverse P)
          (hcomps.imp fun _ _ h ↦ h)
        have hrsl : rs.length = d.params.length := by rw [length_of_mapM hrsM, hssl]
        have hrs2 : rs.map Prod.snd = d.params.reverse.map (PartialHorn.subst xs.reverse) :=
          List.ext_getElem (by rw [List.length_map, List.length_map, hrsl, List.length_reverse])
            fun i' h₁ h₂ ↦ by
              rw [List.getElem_map, List.getElem_map]
              exact hrsi i' _ _ _
                (List.getElem?_eq_getElem (by rw [hssl, ← hrsl]; simpa using h₁))
                (List.getElem?_eq_getElem (by simpa using h₁))
                (List.getElem?_eq_getElem (by simpa using h₂))
        obtain ⟨f, hf⟩ := compile_label hd (mapM_reverse_of hrsM)
          (by rw [List.length_reverse, hxl])
          (List.all_eq_true.mpr fun x hx ↦
            (forall₂_left_mem hxs x (List.mem_reverse.mp hx)).elim fun _ h ↦ h.2)
          (by rw [List.map_reverse, hrs2, List.map_reverse, List.reverse_reverse])
        refine ⟨RoseTree.node (hh.label xs.reverse) ss.reverse, _, ?_, hf, hEenc, ?_⟩
        · rw [dec_node, decStep_tm k (by omega)]
          refine decTm_of k (by omega) (by rw [Nat.add_sub_cancel_left]; exact he) hfx
            (by rw [List.length_map, hcl]) ?_ ?_
          · rw [← List.map_take, List.mapM_map]
            exact hxsM
          · rw [← List.map_drop, List.mapM_map]
            exact hssM
        · have hTs : xs.mapM (encTy k e.length) = some (cs.take d.arity) :=
            mapM_of_forall₂_eq (hxs.imp fun _ _ h ↦ h.1)
          have hMs' : ss.mapM (fun s ↦ enc G n k s X e) = some (cs.drop d.arity) :=
            mapM_of_forall₂_eq (forall₂_of_getElem (by rw [hssl, hMsl]) fun i' h₁ h₂ ↦
              (hssi i' _ _ _ (List.getElem?_eq_getElem h₂) (List.getElem?_eq_getElem h₁)
                (List.getElem?_eq_getElem (by rw [List.length_reverse]; omega))).1)
          rw [enc_node, encStep_label G n k hfx]
          simp only [encTm, Option.bind_eq_bind, hd, Option.bind_some, PrimIdx.tmConst, hfind,
            Option.map_some]
          rw [if_pos ⟨by rw [List.length_reverse, hxl],
            by rw [List.length_map, List.length_reverse, hssl]⟩, List.reverse_reverse,
            ← List.map_reverse, List.reverse_reverse, List.mapM_map]
          simp only [hTs, Option.bind_some, Option.pure_def]
          rw [show ((fun x ↦ x.2 X e) ∘ fun c ↦ (c, enc G n k c)) = fun s ↦ enc G n k s X e
            from rfl, hMs', Option.bind_some, List.take_append_drop]
          rfl
      obtain ⟨hc, hC⟩ := sig_head_tm hsg hC (by rw [← h₁]; rfl) hlt
      have hlen : cs.length = C.headDepth.2 := by
        rw [show (tm A).headDepth.2 = 0 from rfl, List.length_map] at h₂
        omega
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · obtain rfl := Option.some.inj (hC.symm.trans rfl : some C = some (tm one))
        obtain rfl := List.length_eq_zero_iff.mp (hlen : cs.length = 0)
        simp only [List.map_nil, spine, List.foldlM_nil, Option.pure_def, Option.some.injEq,
          tm, Expr.const, Expr.app, node_inj, List.cons.injEq, and_true, true_and] at hS
        subst hS
        refine ⟨FreeTopos.Internal.Term.star, _,
          (by rw [dec_node]; rfl), FreeTopos.Internal.compile_star_iff.mpr ⟨rfl, rfl⟩, rfl, ?_⟩
        rw [FreeTopos.Internal.Term.star, enc_node]
        rfl
      · obtain rfl := Option.some.inj (hC.symm.trans rfl : some C = some (Expr.pi tp (Expr.pi tp
          (Expr.arrow (tm (v 1)) (Expr.arrow (tm (v 0)) (tm (prod (v 1) (v 0))))))))
        obtain ⟨A', cs, rfl⟩ :=
          List.exists_cons_of_length_eq_add_one (hlen : cs.length = 3 + 1)
        obtain ⟨B', t, u, rfl⟩ :=
          List.length_eq_three.mp (Nat.succ.inj (hlen : cs.length + 1 = 3 + 1))
        simp only [List.map_cons, List.map_nil] at hS
        have hT := spine_tp₂ hS
        obtain ⟨a, ha, hIa⟩ := tyComplete hsg hheads₀ A' hT.1
        obtain ⟨b, hb, hIb⟩ := tyComplete hsg hheads₀ B' hT.2
        simp only [tm, tp, prod, Expr.const, Expr.app] at hS
        lf_spine_at hS [Option.bind_eq_some_iff, Option.ite_none_right_eq_some]
        obtain ⟨-, -, ht, hu, hA⟩ := hS
        simp only [node_inj, List.cons.injEq, and_true, true_and] at hA
        subst hA
        obtain ⟨st, ⟨f, a'⟩, hdt, hct, hrt, het⟩ :=
          (ih t (by simp)).1 X e ΓLF A' hΓ ht
        obtain ⟨su, ⟨g, b'⟩, hdu, hcu, hru, heu⟩ :=
          (ih u (by simp)).1 X e ΓLF B' hΓ hu
        obtain rfl := encTy_inj hrt ha
        obtain rfl := encTy_inj hru hb
        refine ⟨FreeTopos.Internal.Term.pair st su, (FreeTopos.pair f g, FreeTopos.prod a' b'),
          ?_, FreeTopos.Internal.compile_pair_iff.mpr ⟨st, su, f, a', g, b', rfl, hct, hcu, rfl⟩,
          by rw [encTy_prod, ha, hb]; rfl, ?_⟩
        · rw [dec_node]
          simp only [List.map_cons, List.map_nil, decStep, hdt, hdu]
          rfl
        · rw [FreeTopos.Internal.Term.pair, enc_node]
          simp only [encStep, List.map_cons, List.map_nil, hct, hcu, ha, hb, het, heu,
            Option.bind_eq_bind, Option.bind_some]
          rfl
      · obtain rfl := Option.some.inj (hC.symm.trans rfl : some C = some
          (Expr.pi tp (Expr.pi tp (Expr.arrow (tm (prod (v 1) (v 0))) (tm (v 1))))))
        obtain ⟨X1, X2, X3, rfl⟩ := List.length_eq_three.mp (hlen : cs.length = 3)
        simp only [List.map_cons, List.map_nil] at hS
        have hT := spine_tp₂ hS
        obtain ⟨a, ha, hIa⟩ := tyComplete hsg hheads₀ X1 hT.1
        obtain ⟨b, hb, hIb⟩ := tyComplete hsg hheads₀ X2 hT.2
        simp only [tm, tp, prod, Expr.const, Expr.app] at hS
        lf_spine_at hS [Option.bind_eq_some_iff, Option.ite_none_right_eq_some]
        obtain ⟨-, -, hp, hA⟩ := hS
        simp only [node_inj, List.cons.injEq, and_true, true_and] at hA
        subst hA
        have hab : encTy k e.length (FreeTopos.prod a b) = some (prod X1 X2) := by
          rw [encTy_prod, ha, hb]; rfl
        obtain ⟨sp, ⟨f, c'⟩, hdp, hcp, hrp, hep⟩ :=
          (ih X3 (by simp)).1 X e ΓLF (prod X1 X2) hΓ hp
        obtain rfl := encTy_inj hrp hab
        refine ⟨FreeTopos.Internal.Term.fst sp, _, ?_,
          FreeTopos.Internal.compile_fst_iff.mpr ⟨sp, f, a, b, rfl, hcp, rfl⟩, ha, ?_⟩
        · rw [dec_node]
          simp only [List.map_cons, List.map_nil, decStep, hdp]
          rfl
        · rw [FreeTopos.Internal.Term.fst, enc_node]
          simp only [encStep, List.map_cons, List.map_nil, hcp, ha, hb, hep, Option.bind_eq_bind,
            Option.bind_some, FreeTopos.Internal.prodParts_eq_some.mpr rfl]
          rfl
      · obtain rfl := Option.some.inj (hC.symm.trans rfl : some C = some
          (Expr.pi tp (Expr.pi tp (Expr.arrow (tm (prod (v 1) (v 0))) (tm (v 0))))))
        obtain ⟨X1, X2, X3, rfl⟩ := List.length_eq_three.mp (hlen : cs.length = 3)
        simp only [List.map_cons, List.map_nil] at hS
        have hT := spine_tp₂ hS
        obtain ⟨a, ha, hIa⟩ := tyComplete hsg hheads₀ X1 hT.1
        obtain ⟨b, hb, hIb⟩ := tyComplete hsg hheads₀ X2 hT.2
        simp only [tm, tp, prod, Expr.const, Expr.app] at hS
        lf_spine_at hS [Option.bind_eq_some_iff, Option.ite_none_right_eq_some]
        obtain ⟨-, -, hp, hA⟩ := hS
        simp only [node_inj, List.cons.injEq, and_true, true_and] at hA
        subst hA
        have hab : encTy k e.length (FreeTopos.prod a b) = some (prod X1 X2) := by
          rw [encTy_prod, ha, hb]; rfl
        obtain ⟨sp, ⟨f, c'⟩, hdp, hcp, hrp, hep⟩ :=
          (ih X3 (by simp)).1 X e ΓLF (prod X1 X2) hΓ hp
        obtain rfl := encTy_inj hrp hab
        refine ⟨FreeTopos.Internal.Term.snd sp, _, ?_,
          FreeTopos.Internal.compile_snd_iff.mpr ⟨sp, f, a, b, rfl, hcp, rfl⟩, hb, ?_⟩
        · rw [dec_node]
          simp only [List.map_cons, List.map_nil, decStep, hdp]
          rfl
        · rw [FreeTopos.Internal.Term.snd, enc_node]
          simp only [encStep, List.map_cons, List.map_nil, hcp, ha, hb, hep, Option.bind_eq_bind,
            Option.bind_some, FreeTopos.Internal.prodParts_eq_some.mpr rfl]
          rfl
      · obtain rfl := Option.some.inj (hC.symm.trans rfl : some C = some
          (Expr.pi tp (Expr.pi tp (Expr.arrow (Expr.arrow (tm (v 1)) (tm (v 0)))
            (tm (exp (v 1) (v 0)))))))
        obtain ⟨X1, X2, X3, rfl⟩ := List.length_eq_three.mp (hlen : cs.length = 3)
        simp only [List.map_cons, List.map_nil] at hS
        have hT := spine_tp₂ hS
        obtain ⟨a, ha, hIa⟩ := tyComplete hsg hheads₀ X1 hT.1
        obtain ⟨b, hb, hIb⟩ := tyComplete hsg hheads₀ X2 hT.2
        simp only [tm, tp, exp, Expr.const, Expr.app] at hS
        lf_spine_at hS [Option.bind_eq_some_iff, Option.ite_none_right_eq_some]
        obtain ⟨-, -, hf, hA⟩ := hS
        simp only [node_inj, List.cons.injEq, and_true, true_and] at hA
        subst hA
        obtain ⟨body, rfl, hbody⟩ := (ih X3 (by simp)).2.1 (e.map Prod.snd) ΓLF a X1 _ hΓ
          (by rwa [List.length_map])
          hf
        obtain ⟨sb, ⟨fb, b'⟩, hdb, hcb, hrb, heb⟩ :=
          hbody (FreeTopos.prod X a) (FreeTopos.Internal.extEnv X a e)
            (by simp only [FreeTopos.Internal.extEnv, List.map_cons, List.map_map]; rfl)
        simp only [length_extEnv] at hdb hrb
        obtain rfl := encTy_inj hrb (encTy_add hb)
        refine ⟨FreeTopos.Internal.Term.lam a sb, _, ?_,
          FreeTopos.Internal.compile_lam_iff.mpr ⟨sb, fb, b', rfl, hIa, hcb,
            rfl⟩, by rw [encTy_exp, ha, hb]; rfl, ?_⟩
        · rw [dec_node]
          simp only [List.map_cons, List.map_nil, decStep, Expr.lam,
            dec_node, hdb, decTy_encTy _ a X1 ha]
          rfl
        · rw [FreeTopos.Internal.Term.lam, enc_node]
          simp only [encStep, List.map_cons, List.map_nil, hcb, ha, hb, heb,
            Option.bind_eq_bind, Option.bind_some]
          rfl
      · obtain rfl := Option.some.inj (hC.symm.trans rfl : some C = some
          (Expr.pi tp (Expr.pi tp (Expr.arrow (tm (exp (v 1) (v 0)))
            (Expr.arrow (tm (v 1)) (tm (v 0)))))))
        obtain ⟨X1, cs, rfl⟩ :=
          List.exists_cons_of_length_eq_add_one (hlen : cs.length = 3 + 1)
        obtain ⟨X2, X3, X4, rfl⟩ :=
          List.length_eq_three.mp (Nat.succ.inj (hlen : cs.length + 1 = 3 + 1))
        simp only [List.map_cons, List.map_nil] at hS
        have hT := spine_tp₂ hS
        obtain ⟨a, ha, hIa⟩ := tyComplete hsg hheads₀ X1 hT.1
        obtain ⟨b, hb, hIb⟩ := tyComplete hsg hheads₀ X2 hT.2
        simp only [tm, tp, exp, Expr.const, Expr.app] at hS
        lf_spine_at hS [Option.bind_eq_some_iff, Option.ite_none_right_eq_some]
        obtain ⟨-, -, ht, hu, hA⟩ := hS
        simp only [node_inj, List.cons.injEq, and_true, true_and] at hA
        subst hA
        have hab : encTy k e.length (FreeTopos.exp a b) = some (exp X1 X2) := by
          rw [encTy_exp, ha, hb]; rfl
        obtain ⟨st, ⟨f, c'⟩, hdt, hct, hrt, het⟩ :=
          (ih X3 (by simp)).1 X e ΓLF (exp X1 X2) hΓ ht
        obtain ⟨su, ⟨g, a'⟩, hdu, hcu, hru, heu⟩ :=
          (ih X4 (by simp)).1 X e ΓLF X1 hΓ hu
        obtain rfl := encTy_inj hrt hab
        obtain rfl := encTy_inj ha hru
        refine ⟨FreeTopos.Internal.Term.app st su, _, ?_,
          FreeTopos.Internal.compile_app_iff.mpr ⟨st, su, rfl, f, a, b, hct, g, hcu, rfl⟩, hb, ?_⟩
        · rw [dec_node]
          simp only [List.map_cons, List.map_nil, decStep, hdt, hdu]
          rfl
        · rw [FreeTopos.Internal.Term.app, enc_node]
          simp only [encStep, List.map_cons, List.map_nil, hct, ha, hb, het, heu,
            Option.bind_eq_bind, Option.bind_some, FreeTopos.Internal.expParts_eq_some.mpr rfl]
          rfl
      · obtain rfl := Option.some.inj (hC.symm.trans rfl : some C = some
          (Expr.arrow (tm one) (tm nat)))
        obtain ⟨X1, rfl⟩ := List.length_eq_one_iff.mp (hlen : cs.length = 1)
        simp only [List.map_cons, List.map_nil, tm, one, nat, Expr.const, Expr.app] at hS
        lf_spine_at hS [Option.bind_eq_some_iff, Option.ite_none_right_eq_some]
        obtain ⟨ht, hA⟩ := hS
        simp only [node_inj, List.cons.injEq, and_true, true_and] at hA
        subst hA
        obtain ⟨st, ⟨g, c'⟩, hdt, hct, hrt, het⟩ :=
          (ih X1 (by simp)).1 X e ΓLF one hΓ ht
        obtain rfl := encTy_inj hrt (rfl : encTy k e.length FreeTopos.one = some one)
        refine ⟨FreeTopos.Internal.Term.arr k.zero [] st, _, ?_,
          FreeTopos.Internal.compile_arr_iff.mpr ⟨st, rfl, _, hk.zero, g, hct, rfl, rfl, rfl⟩,
          rfl, ?_⟩
        · rw [dec_node]
          simp only [List.map_cons, List.map_nil, decStep, hdt]
          rfl
        · rw [FreeTopos.Internal.Term.arr, enc_node, encStep_arr,
            if_pos (k.fixed_of_mem (by simp only [List.mem_cons, true_or]))]
          simp only [encFixed, List.map_cons, List.map_nil, ↓reduceIte, het]
          rfl
      · obtain rfl := Option.some.inj (hC.symm.trans rfl : some C = some
          (Expr.arrow (tm nat) (tm nat)))
        obtain ⟨X1, rfl⟩ := List.length_eq_one_iff.mp (hlen : cs.length = 1)
        simp only [List.map_cons, List.map_nil, tm, nat, Expr.const, Expr.app] at hS
        lf_spine_at hS [Option.bind_eq_some_iff, Option.ite_none_right_eq_some]
        obtain ⟨ht, hA⟩ := hS
        simp only [node_inj, List.cons.injEq, and_true, true_and] at hA
        subst hA
        obtain ⟨st, ⟨g, c'⟩, hdt, hct, hrt, het⟩ :=
          (ih X1 (by simp)).1 X e ΓLF nat hΓ ht
        obtain rfl := encTy_inj hrt (rfl : encTy k e.length FreeTopos.nat = some nat)
        have hne : k.succ ≠ k.zero := fun h ↦ by
          have hd := congrArg FreeTopos.Internal.Prim.dom
            (Option.some.inj (hk.zero.symm.trans (h ▸ hk.succ)))
          exact absurd (congrArg RoseTree.label hd) (by decide)
        refine ⟨FreeTopos.Internal.Term.arr k.succ [] st, _, ?_,
          FreeTopos.Internal.compile_arr_iff.mpr ⟨st, rfl, _, hk.succ, g, hct, rfl, rfl, rfl⟩,
          rfl, ?_⟩
        · rw [dec_node]
          simp only [List.map_cons, List.map_nil, decStep, hdt]
          rfl
        · rw [FreeTopos.Internal.Term.arr, enc_node, encStep_arr,
            if_pos (k.fixed_of_mem (by simp only [List.mem_cons, true_or, or_true]))]
          simp only [encFixed, List.map_cons, List.map_nil, hne, ↓reduceIte, het]
          rfl
      · obtain rfl := Option.some.inj (hC.symm.trans rfl : some C = some
          (Expr.pi tp (Expr.arrow (tm (v 0)) (Expr.arrow (Expr.arrow (tm (v 0)) (tm (v 0)))
            (Expr.arrow (tm nat) (tm (v 0)))))))
        obtain ⟨X1, cs, rfl⟩ :=
          List.exists_cons_of_length_eq_add_one (hlen : cs.length = 3 + 1)
        obtain ⟨X2, X3, X4, rfl⟩ :=
          List.length_eq_three.mp (Nat.succ.inj (hlen : cs.length + 1 = 3 + 1))
        simp only [List.map_cons, List.map_nil] at hS
        obtain ⟨c, hc, hIc⟩ := tyComplete hsg hheads₀ X1 (spine_tp₁ hS)
        simp only [tm, tp, nat, Expr.const, Expr.app] at hS
        lf_spine_at hS [Option.bind_eq_some_iff, Option.ite_none_right_eq_some]
        obtain ⟨-, hzJ, hfJ, hm, hA⟩ := hS
        simp only [node_inj, List.cons.injEq, and_true, true_and] at hA
        subst hA
        obtain ⟨sz, ⟨fz, cz⟩, hdz, hcz, hrz, hez⟩ := (ih X2 (by simp)).1 X e ΓLF X1 hΓ hzJ
        obtain ⟨body, rfl, hbc⟩ := (ih X3 (by simp)).2.1 (e.map Prod.snd) ΓLF c X1 _ hΓ
          (by rwa [List.length_map]) hfJ
        obtain ⟨ss, ⟨fs, cs'⟩, hds, hcs, hrs, hes⟩ :=
          hbc (FreeTopos.prod X c) (FreeTopos.Internal.extEnv X c e)
            (by simp only [FreeTopos.Internal.extEnv, List.map_cons, List.map_map]; rfl)
        simp only [length_extEnv] at hds hrs
        obtain ⟨sm, ⟨fm, cm⟩, hdm, hcm, hrm, hem⟩ := (ih X4 (by simp)).1 X e ΓLF nat hΓ hm
        obtain rfl := encTy_inj hc hrz
        obtain rfl := encTy_inj (encTy_add hc) hrs
        obtain rfl := encTy_inj hrm (rfl : encTy k e.length FreeTopos.nat = some nat)
        obtain ⟨r, hr, hrc⟩ := FreeTopos.Internal.compile_natRec_of_parts hcz hcs hcm
        refine ⟨FreeTopos.Internal.Term.natRec sz ss sm, r, ?_, hr, by rw [hrc]; exact hc, ?_⟩
        · rw [dec_node]
          simp only [List.map_cons, List.map_nil, decStep, Expr.lam, dec_node, hdz, hds, hdm]
          rfl
        · rw [FreeTopos.Internal.Term.natRec, enc_node]
          simp only [encStep, List.map_cons, List.map_nil, hcz, hc, hez, hes, hem,
            Option.bind_eq_bind, Option.bind_some]
          rfl
      · obtain rfl := Option.some.inj (hC.symm.trans rfl : some C = some
          (Expr.pi tp (Expr.arrow (tm (v 0)) (Expr.arrow (tm (v 0)) (tm omega)))))
        obtain ⟨X1, X2, X3, rfl⟩ := List.length_eq_three.mp (hlen : cs.length = 3)
        simp only [List.map_cons, List.map_nil] at hS
        obtain ⟨a, ha, hIa⟩ := tyComplete hsg hheads₀ X1 (spine_tp₁ hS)
        simp only [tm, tp, omega, Expr.const, Expr.app] at hS
        lf_spine_at hS [Option.bind_eq_some_iff, Option.ite_none_right_eq_some]
        obtain ⟨-, ht, hu, hA⟩ := hS
        simp only [node_inj, List.cons.injEq, and_true, true_and] at hA
        subst hA
        obtain ⟨st, ⟨f, a₁⟩, hdt, hct, hrt, het⟩ :=
          (ih X2 (by simp)).1 X e ΓLF X1 hΓ ht
        obtain ⟨su, ⟨g, a₂⟩, hdu, hcu, hru, heu⟩ :=
          (ih X3 (by simp)).1 X e ΓLF X1 hΓ hu
        obtain rfl := encTy_inj ha hrt
        obtain rfl := encTy_inj ha hru
        refine ⟨FreeTopos.Internal.Term.eq st su, _, ?_,
          FreeTopos.Internal.compile_eq_iff.mpr ⟨st, su, rfl, f, a, hct, g, hcu, rfl⟩, rfl, ?_⟩
        · rw [dec_node]
          simp only [List.map_cons, List.map_nil, decStep, hdt, hdu]
          rfl
        · rw [FreeTopos.Internal.Term.eq, enc_node]
          simp only [encStep, List.map_cons, List.map_nil, hct, ha, het, heu,
            Option.bind_eq_bind, Option.bind_some]
          rfl
      · obtain rfl := Option.some.inj (hC.symm.trans rfl : some C = some
          (Expr.pi tp (Expr.arrow (tm one) (tm (list (v 0))))))
        obtain ⟨X1, X2, rfl⟩ := List.length_eq_two.mp (hlen : cs.length = 2)
        simp only [List.map_cons, List.map_nil] at hS
        obtain ⟨a, ha, hIa⟩ := tyComplete hsg hheads₀ X1 (spine_tp₁ hS)
        simp only [tm, tp, one, list, Expr.const, Expr.app] at hS
        lf_spine_at hS [Option.bind_eq_some_iff, Option.ite_none_right_eq_some]
        obtain ⟨-, ht, hA⟩ := hS
        simp only [node_inj, List.cons.injEq, and_true, true_and] at hA
        subst hA
        obtain ⟨st, ⟨g, c'⟩, hdt, hct, hrt, het⟩ := (ih X2 (by simp)).1 X e ΓLF one hΓ ht
        obtain rfl := encTy_inj hrt (rfl : encTy k e.length FreeTopos.one = some one)
        refine ⟨FreeTopos.Internal.Term.arr k.nil [a] st, _, ?_,
          FreeTopos.Internal.compile_arr_iff.mpr ⟨st, rfl, _, hk.nil, g,
            by rw [subst_nilPrim_dom]; exact hct, rfl,
            by simp [hIa], rfl⟩,
          by rw [subst_nilPrim_cod, encTy_list, ha]; rfl, ?_⟩
        · rw [dec_node]
          simp only [List.map_cons, List.map_nil, decStep, hdt, decTy_encTy _ a X1 ha,
            Option.bind_eq_bind, Option.bind_some, Option.pure_def]
        · rw [FreeTopos.Internal.Term.arr, enc_node, encStep_arr,
            if_pos (k.fixed_of_mem (by simp only [List.mem_cons, true_or, or_true]))]
          simp only [encFixed, List.map_cons, List.map_nil, ↓reduceIte, ha, het,
            Option.bind_eq_bind, Option.bind_some, Option.pure_def]
          rfl
      · obtain rfl := Option.some.inj (hC.symm.trans rfl : some C = some
          (Expr.pi tp (Expr.arrow (tm (prod (v 0) (list (v 0)))) (tm (list (v 0))))))
        obtain ⟨X1, X2, rfl⟩ := List.length_eq_two.mp (hlen : cs.length = 2)
        simp only [List.map_cons, List.map_nil] at hS
        obtain ⟨a, ha, hIa⟩ := tyComplete hsg hheads₀ X1 (spine_tp₁ hS)
        simp only [tm, tp, prod, list, Expr.const, Expr.app] at hS
        lf_spine_at hS [Option.bind_eq_some_iff, Option.ite_none_right_eq_some]
        obtain ⟨-, ht, hA⟩ := hS
        simp only [node_inj, List.cons.injEq, and_true, true_and] at hA
        subst hA
        have hpl : encTy k e.length (FreeTopos.prod a (FreeTopos.list a)) =
            some (prod X1 (list X1)) := by
          rw [encTy_prod, encTy_list, ha]; rfl
        obtain ⟨st, ⟨g, c'⟩, hdt, hct, hrt, het⟩ :=
          (ih X2 (by simp)).1 X e ΓLF (prod X1 (list X1)) hΓ ht
        obtain rfl := encTy_inj hrt hpl
        refine ⟨FreeTopos.Internal.Term.arr k.cons [a] st, _, ?_,
          FreeTopos.Internal.compile_arr_iff.mpr ⟨st, rfl, _, hk.cons, g,
            by rw [subst_consPrim_dom]; exact hct, rfl,
            by simp [hIa], rfl⟩,
          by rw [subst_consPrim_cod, encTy_list, ha]; rfl, ?_⟩
        · rw [dec_node]
          simp only [List.map_cons, List.map_nil, decStep, hdt, decTy_encTy _ a X1 ha,
            Option.bind_eq_bind, Option.bind_some, Option.pure_def]
        · rw [FreeTopos.Internal.Term.arr, enc_node, encStep_arr,
            if_pos (k.fixed_of_mem (by simp only [List.mem_cons, true_or, or_true]))]
          simp only [encFixed, List.map_cons, List.map_nil, hk.cons_ne_nil, ↓reduceIte, ha, het,
            Option.bind_eq_bind, Option.bind_some, Option.pure_def]
          rfl
      · obtain rfl := Option.some.inj (hC.symm.trans rfl : some C = some
          (Expr.pi tp (Expr.pi tp (Expr.arrow (tm (v 0))
            (Expr.arrow (Expr.arrow (tm (v 1)) (Expr.arrow (tm (v 0)) (tm (v 0))))
              (Expr.arrow (tm (list (v 1))) (tm (v 0))))))))
        obtain ⟨X1, cs, rfl⟩ :=
          List.exists_cons_of_length_eq_add_one (hlen : cs.length = 4 + 1)
        obtain ⟨X2, cs, rfl⟩ :=
          List.exists_cons_of_length_eq_add_one (Nat.succ.inj (hlen : cs.length + 1 = 4 + 1))
        obtain ⟨X3, X4, X5, rfl⟩ := List.length_eq_three.mp
          (Nat.succ.inj (Nat.succ.inj (hlen : cs.length + 1 + 1 = 4 + 1)))
        simp only [List.map_cons, List.map_nil] at hS
        have hT := spine_tp₂ hS
        obtain ⟨a, ha, hIa⟩ := tyComplete hsg hheads₀ X1 hT.1
        obtain ⟨c, hc, hIc⟩ := tyComplete hsg hheads₀ X2 hT.2
        simp only [tm, tp, list, Expr.const, Expr.app] at hS
        lf_spine_at hS [Option.bind_eq_some_iff, Option.ite_none_right_eq_some]
        obtain ⟨-, -, hzJ, hfJ, hm, hA⟩ := hS
        simp only [node_inj, List.cons.injEq, and_true, true_and] at hA
        subst hA
        obtain ⟨sz, ⟨fz, cz⟩, hdz, hcz, hrz, hez⟩ := (ih X3 (by simp)).1 X e ΓLF X2 hΓ hzJ
        obtain ⟨body, rfl, hbc⟩ :=
          (ih X4 (by simp)).2.2 (e.map Prod.snd) ΓLF a c X1 _ _ hΓ (by rwa [List.length_map])
            (by rw [List.length_map]; exact encTy_add hc) hfJ
        obtain ⟨ss, ⟨fs, cs'⟩, hds, hcs, hrs, hes⟩ :=
          hbc (FreeTopos.prod (FreeTopos.prod X a) c)
            (FreeTopos.Internal.extEnv (FreeTopos.prod X a) c (FreeTopos.Internal.extEnv X a e))
            (by simp only [FreeTopos.Internal.extEnv, List.map_cons, List.map_map]; rfl)
        simp only [length_extEnv] at hds hrs
        have hla : encTy k e.length (FreeTopos.list a) = some (list X1) := by
          rw [encTy_list, ha]; rfl
        obtain ⟨sm, ⟨fm, cm⟩, hdm, hcm, hrm, hem⟩ := (ih X5 (by simp)).1 X e ΓLF (list X1) hΓ hm
        obtain rfl := encTy_inj hc hrz
        have hc₂ : encTy k (e.length + 1 + 1) c = some (Expr.rename X2 (· + 2)) := by
          rw [Nat.add_assoc]
          exact encTy_add hc
        obtain rfl := encTy_inj hc₂ hrs
        obtain rfl := encTy_inj hrm hla
        obtain ⟨r, hr, hrc⟩ := FreeTopos.Internal.compile_listRec_of_parts hcm hcz hcs
        refine ⟨FreeTopos.Internal.Term.listRec sz ss sm, r, ?_, hr, by rw [hrc]; exact hc, ?_⟩
        · rw [dec_node]
          simp only [List.map_cons, List.map_nil, decStep, Expr.lam, dec_node, hdz, hds, hdm]
          rfl
        · rw [FreeTopos.Internal.Term.listRec, enc_node]
          simp only [encStep, List.map_cons, List.map_nil, hcz, hcm,
            FreeTopos.Internal.listPart_eq_some.mpr rfl, ha, hc, hez, hes, hem,
            Option.bind_eq_bind, Option.bind_some]
          rfl
      · obtain rfl := Option.some.inj (hC.symm.trans rfl : some C = some
          (Expr.arrow (tm (prod nat (list rose))) (tm rose)))
        obtain ⟨X1, rfl⟩ := List.length_eq_one_iff.mp (hlen : cs.length = 1)
        simp only [List.map_cons, List.map_nil, tm, nat, rose, prod, list, Expr.const,
          Expr.app] at hS
        lf_spine_at hS [Option.bind_eq_some_iff, Option.ite_none_right_eq_some]
        obtain ⟨ht, hA⟩ := hS
        simp only [node_inj, List.cons.injEq, and_true, true_and] at hA
        subst hA
        obtain ⟨st, ⟨g, c'⟩, hdt, hct, hrt, het⟩ :=
          (ih X1 (by simp)).1 X e ΓLF (prod nat (list rose)) hΓ ht
        obtain rfl := encTy_inj hrt (rfl : encTy k e.length (FreeTopos.prod FreeTopos.nat
          (FreeTopos.list FreeTopos.rose)) = some (prod nat (list rose)))
        refine ⟨FreeTopos.Internal.Term.arr k.node [] st, _, ?_,
          FreeTopos.Internal.compile_arr_iff.mpr ⟨st, rfl, _, hk.node, g, hct, rfl, rfl, rfl⟩,
          rfl, ?_⟩
        · rw [dec_node]
          simp only [List.map_cons, List.map_nil, decStep, hdt]
          rfl
        · rw [FreeTopos.Internal.Term.arr, enc_node, encStep_arr,
            if_pos (k.fixed_of_mem (by simp only [List.mem_cons, true_or, or_true]))]
          simp only [encFixed, List.map_cons, List.map_nil, hk.node_ne.1, hk.node_ne.2, ↓reduceIte,
            het]
          rfl
      · obtain rfl := Option.some.inj (hC.symm.trans rfl : some C = some
          (Expr.pi tp (Expr.arrow (Expr.arrow (tm (prod nat (list (v 0)))) (tm (v 0)))
            (Expr.arrow (tm rose) (tm (v 0))))))
        obtain ⟨X1, X2, X3, rfl⟩ := List.length_eq_three.mp (hlen : cs.length = 3)
        simp only [List.map_cons, List.map_nil] at hS
        obtain ⟨c, hc, hIc⟩ := tyComplete hsg hheads₀ X1 (spine_tp₁ hS)
        simp only [tm, tp, nat, rose, prod, list, Expr.const, Expr.app] at hS
        lf_spine_at hS [Option.bind_eq_some_iff, Option.ite_none_right_eq_some]
        obtain ⟨-, hfJ, hm, hA⟩ := hS
        simp only [node_inj, List.cons.injEq, and_true, true_and] at hA
        subst hA
        have hpc : encTy k e.length (FreeTopos.prod FreeTopos.nat (FreeTopos.list c)) =
            some (prod nat (list X1)) := by rw [encTy_prod, encTy_list, hc]; rfl
        obtain ⟨body, rfl, hbc⟩ := (ih X2 (by simp)).2.1 (e.map Prod.snd) ΓLF _ _ _ hΓ
          (by rw [List.length_map]; exact hpc) hfJ
        obtain ⟨ss, ⟨fs, cs'⟩, hds, hcs, hrs, hes⟩ :=
          hbc (FreeTopos.prod X (FreeTopos.prod FreeTopos.nat (FreeTopos.list c)))
            (FreeTopos.Internal.extEnv X (FreeTopos.prod FreeTopos.nat (FreeTopos.list c)) e)
            (by simp only [FreeTopos.Internal.extEnv, List.map_cons, List.map_map]; rfl)
        simp only [length_extEnv] at hds hrs
        obtain ⟨sm, ⟨fm, cm⟩, hdm, hcm, hrm, hem⟩ := (ih X3 (by simp)).1 X e ΓLF rose hΓ hm
        obtain rfl := encTy_inj (encTy_add hc) hrs
        obtain rfl := encTy_inj hrm (rfl : encTy k e.length FreeTopos.rose = some rose)
        obtain ⟨r, hr, hrc⟩ := FreeTopos.Internal.compile_roseRec_of_parts
          (hIc) hcm (show FreeTopos.Internal.roseParts FreeTopos.rose =
            some (FreeTopos.nat, FreeTopos.roseRec) by simp [FreeTopos.Internal.roseParts]) hcs
        refine ⟨FreeTopos.Internal.Term.roseRec c ss sm, r, ?_, hr, by rw [hrc]; exact hc, ?_⟩
        · rw [dec_node]
          simp only [List.map_cons, List.map_nil, decStep, Expr.lam, dec_node, hds, hdm,
            decTy_encTy _ c X1 hc]
          rfl
        · rw [FreeTopos.Internal.Term.roseRec, enc_node]
          simp only [encStep, List.map_cons, List.map_nil, hcm, hc, hes, hem,
            Option.bind_eq_bind, Option.bind_some]
          rfl
      · obtain rfl := Option.some.inj (hC.symm.trans rfl : some C = some
          (Expr.pi tp (Expr.arrow (tm (prod (v 0) (list (lrose (v 0))))) (tm (lrose (v 0))))))
        obtain ⟨X1, X2, rfl⟩ := List.length_eq_two.mp (hlen : cs.length = 2)
        simp only [List.map_cons, List.map_nil] at hS
        obtain ⟨a, ha, hIa⟩ := tyComplete hsg hheads₀ X1 (spine_tp₁ hS)
        simp only [tm, tp, prod, list, lrose, Expr.const, Expr.app] at hS
        lf_spine_at hS [Option.bind_eq_some_iff, Option.ite_none_right_eq_some]
        obtain ⟨-, ht, hA⟩ := hS
        simp only [node_inj, List.cons.injEq, and_true, true_and] at hA
        subst hA
        have hpl : encTy k e.length (FreeTopos.prod a (FreeTopos.list (FreeTopos.lrose a))) =
            some (prod X1 (list (lrose X1))) := by
          rw [encTy_prod, encTy_list, encTy_lrose, ha]; rfl
        obtain ⟨st, ⟨g, c'⟩, hdt, hct, hrt, het⟩ :=
          (ih X2 (by simp)).1 X e ΓLF (prod X1 (list (lrose X1))) hΓ ht
        obtain rfl := encTy_inj hrt hpl
        refine ⟨FreeTopos.Internal.Term.arr k.lnode [a] st, _, ?_,
          FreeTopos.Internal.compile_arr_iff.mpr ⟨st, rfl, _, hk.lnode, g,
            by rw [subst_lnodePrim_dom]; exact hct, rfl,
            by simp [hIa], rfl⟩,
          by rw [subst_lnodePrim_cod, encTy_lrose, ha]; rfl, ?_⟩
        · rw [dec_node]
          simp only [List.map_cons, List.map_nil, decStep, hdt, decTy_encTy _ a X1 ha,
            Option.bind_eq_bind, Option.bind_some, Option.pure_def]
        · rw [FreeTopos.Internal.Term.arr, enc_node, encStep_arr,
            if_pos (k.fixed_of_mem (by simp only [List.mem_cons, true_or, or_true]))]
          simp only [encFixed, List.map_cons, List.map_nil, hk.lnode_ne.1, hk.lnode_ne.2,
            ↓reduceIte, ha, het, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
          rfl
      · obtain rfl := Option.some.inj (hC.symm.trans rfl : some C = some
          (Expr.pi tp (Expr.pi tp (Expr.arrow (Expr.arrow (tm (prod (v 1) (list (v 0))))
            (tm (v 0))) (Expr.arrow (tm (lrose (v 1))) (tm (v 0)))))))
        obtain ⟨X1, X2, X3, X4, rfl⟩ := List.length_eq_four.mp (hlen : cs.length = 4)
        simp only [List.map_cons, List.map_nil] at hS
        have hT := spine_tp₂ hS
        obtain ⟨a, ha, hIa⟩ := tyComplete hsg hheads₀ X1 hT.1
        obtain ⟨c, hc, hIc⟩ := tyComplete hsg hheads₀ X2 hT.2
        simp only [tm, tp, prod, list, lrose, Expr.const, Expr.app] at hS
        lf_spine_at hS [Option.bind_eq_some_iff, Option.ite_none_right_eq_some]
        obtain ⟨-, -, hfJ, hm, hA⟩ := hS
        simp only [node_inj, List.cons.injEq, and_true, true_and] at hA
        subst hA
        have hpc : encTy k e.length (FreeTopos.prod a (FreeTopos.list c)) =
            some (prod X1 (list X2)) := by
          rw [encTy_prod, encTy_list, ha, hc]; rfl
        obtain ⟨body, rfl, hbc⟩ := (ih X3 (by simp)).2.1 (e.map Prod.snd) ΓLF _ _ _ hΓ
          (by rw [List.length_map]; exact hpc) hfJ
        obtain ⟨ss, ⟨fs, cs'⟩, hds, hcs, hrs, hes⟩ :=
          hbc (FreeTopos.prod X (FreeTopos.prod a (FreeTopos.list c)))
            (FreeTopos.Internal.extEnv X (FreeTopos.prod a (FreeTopos.list c)) e)
            (by simp only [FreeTopos.Internal.extEnv, List.map_cons, List.map_map]; rfl)
        simp only [length_extEnv] at hds hrs
        obtain ⟨sm, ⟨fm, cm⟩, hdm, hcm, hrm, hem⟩ :=
          (ih X4 (by simp)).1 X e ΓLF (lrose X1) hΓ hm
        obtain rfl := encTy_inj (encTy_add hc) hrs
        obtain rfl := encTy_inj hrm (show encTy k e.length (FreeTopos.lrose a) = some (lrose X1) by
          rw [encTy_lrose, ha]; rfl)
        obtain ⟨r, hr, hrc⟩ := FreeTopos.Internal.compile_roseRec_of_parts
          (hIc) hcm (roseParts_lrose a) hcs
        refine ⟨FreeTopos.Internal.Term.roseRec c ss sm, r, ?_, hr, by rw [hrc]; exact hc, ?_⟩
        · rw [dec_node]
          simp only [List.map_cons, List.map_nil, decStep, Expr.lam, dec_node, hds, hdm,
            decTy_encTy _ c X2 hc]
          rfl
        · rw [FreeTopos.Internal.Term.roseRec, enc_node]
          simp only [encStep, List.map_cons, List.map_nil, hcm, FreeTopos.lrose, PartialHorn.op,
            RoseTree.label_node, RoseTree.children_node, Nat.reduceAdd, ha, hc, hes, hem,
            Option.bind_eq_bind, Option.bind_some]
          rfl
      · obtain rfl := Option.some.inj (hC.symm.trans rfl : some C = some
          (Expr.pi tp (Expr.pi tp (Expr.arrow (tm (v 1)) (tm (coprod (v 1) (v 0)))))))
        obtain ⟨X1, X2, X3, rfl⟩ := List.length_eq_three.mp (hlen : cs.length = 3)
        exact tmComplete_inl hsg hk (ih X3 (by simp)) hΓ hS
      · obtain rfl := Option.some.inj (hC.symm.trans rfl : some C = some
          (Expr.pi tp (Expr.pi tp (Expr.arrow (tm (v 0)) (tm (coprod (v 1) (v 0)))))))
        obtain ⟨X1, X2, X3, rfl⟩ := List.length_eq_three.mp (hlen : cs.length = 3)
        exact tmComplete_inr hsg hk (ih X3 (by simp)) hΓ hS
      · obtain rfl := Option.some.inj (hC.symm.trans rfl : some C = some
          (Expr.pi tp (Expr.pi tp (Expr.pi tp (Expr.arrow (tm (prod (exp (v 2) (v 0))
            (exp (v 1) (v 0)))) (tm (exp (coprod (v 2) (v 1)) (v 0))))))))
        obtain ⟨X1, cs, rfl⟩ := List.exists_cons_of_length_eq_add_one (hlen : cs.length = 3 + 1)
        obtain ⟨X2, X3, X4, rfl⟩ :=
          List.length_eq_three.mp (Nat.succ.inj (hlen : cs.length + 1 = 3 + 1))
        exact tmComplete_case hsg hk (ih X4 (by simp)) hΓ hS

end Completeness

end Geb.LF.Topos

end
