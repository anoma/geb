/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.LF.Metatheory.Identity

set_option doc.verso true in
/-!
# The η-expansion of atomic terms

The η-expansion of an atomic term checks against the type the term synthesizes
(\[WatkinsEtAl2002\], Lemma 36): a head whose classifier instantiates along a spine to a
type, η-expanded at the type's erasure, is a canonical term of the type. The proof is by
induction on the erasure. At a product, the expansion abstracts over the domain, and its body
is the expansion at the codomain of the head applied to the spine and to the expansion of the
bound variable, which checks against the domain by the induction hypothesis; instantiating the
codomain with that expansion gives it back by the identity principle
({name}`Geb.LF.hsub_eta_identity`), which applies because a judged type applies each variable
only to spines that fill its type ({lit}`judge_appliedAt`).

## Main definitions

* {lit}`ModeShape` — that a mode's type, where it has one, has the shape of types.

## Main statements

* {lit}`spine_etaLongSpine` — the arguments along which a classifier instantiates to an atomic
  type fill its erasure.
* {lit}`judge_appliedAt` — judged expressions are η-long.
* {lit}`judge_eta` — the η-expansion of an atomic term checks against the type it synthesizes.

## References

* \[WatkinsEtAl2002\], Section 4.6.

## Tags

logical framework, LF, η-expansion, canonical forms
-/

set_option doc.verso true

@[expose] public section

namespace Geb.LF

/-- The first step of a spine: the classifier is a product, the first argument checks against
its domain, and the rest instantiates the codomain with the argument substituted. -/
theorem spine_cons_inv {Γ : Ctx} {c m : Expr} {J : Ctx → Mode → Bool}
    {ms : List (Expr × (Ctx → Mode → Bool))} {r : Expr}
    (h : spine Γ c ((m, J) :: ms) = some r) :
    ∃ a b c', c = Expr.pi a b ∧ J Γ (.check a) = true ∧ hsub (Expr.erase a) m b 0 = some c' ∧
      spine Γ c' ms = some r := by
  simp only [spine, List.foldlM_cons] at h
  obtain ⟨c', hc', hr⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨l, cs, rfl⟩ := exists_node c
  rw [RoseTree.label_node, RoseTree.children_node] at hc'
  rcases l with _ | _ | _ | _
  · simp at hc'
  · rcases cs with _ | ⟨a, _ | ⟨b, _ | ⟨d, cs⟩⟩⟩
    · simp at hc'
    · simp at hc'
    · simp only at hc'
      split_ifs at hc' with hJ
      exact ⟨a, b, c', rfl, hJ, hc', hr⟩
    · simp at hc'
  · simp at hc'
  · simp at hc'

/-- The domain and codomain of a product of the shape of types have the shape. -/
theorem typeShape_pi {a b : Expr} (h : (Expr.pi a b).TypeShape = true) :
    a.TypeShape = true ∧ b.TypeShape = true := by
  rw [Expr.pi, typeShape_node] at h
  simpa only [List.map_cons, List.map_nil, typeShapeStep, Bool.and_eq_true] using h

/-- The erasure of a product is the function type of its domain's and codomain's. -/
theorem erase_pi (a b : Expr) :
    (Expr.pi a b).erase = RoseTree.node .arrow [a.erase, b.erase] := by
  rw [Expr.pi, erase_node]
  rfl

/-- The arguments of a spine along which a classifier of the shape of types instantiates are
each checked against a type of the shape. -/
theorem spine_args_shape {J : Expr → Ctx → Mode → Bool} {Γ : Ctx} :
    ∀ (ms : List Expr) (c r : Expr), c.TypeShape = true →
      spine Γ c (ms.map fun m ↦ (m, J m)) = some r →
      ∀ m ∈ ms, ∃ a, a.TypeShape = true ∧ J m Γ (.check a) = true :=
  fun ms ↦ ms.rec (motive := fun ms ↦ ∀ (c r : Expr), c.TypeShape = true →
      spine Γ c (ms.map fun m ↦ (m, J m)) = some r →
      ∀ m ∈ ms, ∃ a, a.TypeShape = true ∧ J m Γ (.check a) = true)
    (fun _ _ _ _ m hm ↦ absurd hm List.not_mem_nil)
    (fun m ms ih c r hc h m' hm' ↦ by
      obtain ⟨a, b, c', rfl, hJ, hc', hr⟩ := spine_cons_inv h
      obtain ⟨ha, hb⟩ := typeShape_pi hc
      rcases List.mem_cons.mp hm' with rfl | hm'
      · exact ⟨a, ha, hJ⟩
      · exact ih c' r (typeShape_hsubWith _ b m 0 c' hb hc').1 hr m' hm')

/-- The arguments along which a classifier of the shape of types instantiates to an atomic type,
each η-long at the erasure of the type it checks against, fill the classifier's erasure. -/
theorem spine_etaLongSpine {sig : Sig} {Γ : Ctx} :
    ∀ (ms : List Expr) (c r : Expr), c.TypeShape = true →
      spine Γ c (ms.map fun m ↦ (m, judge sig m)) = some r → IsApp r = true →
      (∀ m ∈ ms, ∀ a, a.TypeShape = true → judge sig m Γ (.check a) = true →
        EtaLong a.erase m = true) →
      EtaLongSpine c.erase ms = true :=
  fun ms ↦ ms.rec (motive := fun ms ↦ ∀ (c r : Expr), c.TypeShape = true →
      spine Γ c (ms.map fun m ↦ (m, judge sig m)) = some r → IsApp r = true →
      (∀ m ∈ ms, ∀ a, a.TypeShape = true → judge sig m Γ (.check a) = true →
        EtaLong a.erase m = true) →
      EtaLongSpine c.erase ms = true)
    (fun c r hc h hr _ ↦ by
      simp only [spine, List.map_nil, List.foldlM_nil, Option.pure_def, Option.some.injEq] at h
      subst h
      obtain ⟨k, hk⟩ := erase_of_typeShape_isApp hc hr
      rw [hk, EtaLongSpine, etaLong_node]
      rfl)
    (fun m ms ih c r hc h hr hm ↦ by
      obtain ⟨a, b, c', rfl, hJ, hc', hrest⟩ := spine_cons_inv h
      obtain ⟨ha, hb⟩ := typeShape_pi hc
      obtain ⟨hc's, hc'e⟩ := typeShape_hsubWith _ b m 0 c' hb hc'
      rw [erase_pi, etaLongSpine_arrow, Bool.and_eq_true]
      refine ⟨hm m (by simp) a ha hJ, ?_⟩
      rw [← hc'e]
      exact ih c' r hc's hrest hr fun m' hm' ↦ hm m' (List.mem_cons_of_mem _ hm'))

/-- Whether a mode's type, where it has one, has the shape of types. -/
def ModeShape : Mode → Bool
  | .check p => p.TypeShape
  | _ => true

/-- An abstraction is η-long at a function type exactly when its body is η-long at the codomain
and applies the bound variable only to spines that fill the domain. -/
theorem etaLong_arrow_lam (α₁ α₂ : SimpleTy) (b : Expr) :
    EtaLong (RoseTree.node .arrow [α₁, α₂]) (Expr.lam b) =
      (EtaLong α₂ b && Expr.AppliedAt (EtaLongSpine α₁) b 0) := by
  rw [EtaLong, etaLong_node]
  rfl

/-- The judged expressions are η-long (\[HarperLicata2007\], Section 2.2): in an expression
judged in a context of types of the shape of types, every occurrence of a variable is applied
to a spine that fills the erasure of its type, and a term checked against a type of the shape is
η-long at the type's erasure. -/
theorem judge_appliedAt {sig : Sig} (hsig : sig.ok = true) :
    ∀ (E : Expr) (Γ : Ctx) (md : Mode), (∀ a ∈ Γ, a.TypeShape = true) → ModeShape md = true →
      judge sig E Γ md = true →
      (∀ j T, varType Γ j = some T → Expr.AppliedAt (EtaLongSpine T.erase) E j = true) ∧
        ∀ P, md = .check P → EtaLong P.erase E = true :=
  RoseTree.ind fun l cs ih Γ md hΓ hmd hj ↦ by
    have hsame : ∀ b ∈ cs, ∀ mb, ModeShape mb = true → judge sig b Γ mb = true →
        ∀ j T, varType Γ j = some T → Expr.AppliedAt (EtaLongSpine T.erase) b j = true :=
      fun b hb mb hmb hjb ↦ (ih b hb Γ mb hΓ hmb hjb).1
    have hext : ∀ b ∈ cs, ∀ (a : Expr) (mb : Mode), a.TypeShape = true → ModeShape mb = true →
        judge sig b (a :: Γ) mb = true →
        (∀ j T, varType Γ j = some T →
          Expr.AppliedAt (EtaLongSpine T.erase) b (j + 1) = true) ∧
        Expr.AppliedAt (EtaLongSpine a.erase) b 0 = true ∧
        ∀ P, mb = .check P → EtaLong P.erase b = true := by
      intro b hb a mb ha hmb hjb
      have hΓ' : ∀ x ∈ a :: Γ, x.TypeShape = true := fun x hx ↦ by
        rcases List.mem_cons.mp hx with rfl | hx
        · exact ha
        · exact hΓ x hx
      have hb' := ih b hb (a :: Γ) mb hΓ' hmb hjb
      refine ⟨fun j T hT ↦ ?_, ?_, hb'.2⟩
      · have hT' : varType (a :: Γ) (j + 1) = some (T.rename (· + 1)) := by
          rw [varType_cons_succ, hT]
          rfl
        have := hb'.1 (j + 1) _ hT'
        rwa [erase_rename] at this
      · have := hb'.1 0 (a.rename (· + (0 + 1))) rfl
        rwa [erase_rename] at this
    have hpi : ∀ (a b : Expr) (mb : Mode), cs = [a, b] → l = .pi → ModeShape mb = true →
        judge sig a Γ .type = true → judge sig b (a :: Γ) mb = true →
        ∀ j T, varType Γ j = some T →
          Expr.AppliedAt (EtaLongSpine T.erase) (RoseTree.node l cs) j = true := by
      intro a b mb hcs hl hmb ha hb j T hT
      subst hcs hl
      refine appliedAt_node_iff.mpr ⟨(fun i h ↦ nomatch h), fun idx hidx ↦ ?_⟩
      rcases idx with _ | _ | idx
      · exact hsame a (by simp) .type rfl ha j T hT
      · exact (hext b (by simp) a mb ((judgeWith_typeShape a Γ).2 ha) hmb hb).1 j T hT
      · exact absurd hidx (by simp only [List.length_cons, List.length_nil]; omega)
    rw [judge, judgeWith_node] at hj
    rcases md with _ | _ | P
    · refine ⟨?_, fun P h ↦ nomatch h⟩
      rcases l with _ | _ | _ | _
      · rcases cs with _ | ⟨d, cs⟩
        · exact fun j T _ ↦ appliedAt_node_iff.mpr ⟨(fun i h ↦ nomatch h),
            fun idx hidx ↦ absurd hidx (Nat.not_lt_zero _)⟩
        · simp [judgeStep] at hj
      · rcases cs with _ | ⟨a, _ | ⟨k, _ | ⟨d, cs⟩⟩⟩
        · simp [judgeStep] at hj
        · simp [judgeStep] at hj
        · simp only [judgeStep, List.map_cons, List.map_nil, Bool.and_eq_true] at hj
          exact hpi a k .kind rfl rfl rfl hj.1 hj.2
        · simp [judgeStep] at hj
      · simp [judgeStep] at hj
      · simp [judgeStep] at hj
    · refine ⟨?_, fun P h ↦ nomatch h⟩
      rcases l with _ | _ | _ | (i | c)
      · simp [judgeStep] at hj
      · rcases cs with _ | ⟨a, _ | ⟨b, _ | ⟨d, cs⟩⟩⟩
        · simp [judgeStep] at hj
        · simp [judgeStep] at hj
        · simp only [judgeStep, List.map_cons, List.map_nil, Bool.and_eq_true] at hj
          exact hpi a b .type rfl rfl rfl hj.1 hj.2
        · simp [judgeStep] at hj
      · simp [judgeStep] at hj
      · simp [judgeStep] at hj
      · intro j T hT
        simp only [judgeStep, beq_iff_eq, Option.bind_eq_some_iff] at hj
        obtain ⟨k, hk, hsp⟩ := hj
        refine appliedAt_node_iff.mpr ⟨(fun i h ↦ nomatch h), fun idx hidx ↦ ?_⟩
        obtain ⟨a, ha, hja⟩ := spine_args_shape cs k _ (Sig.ok_typeShape hsig c k hk) hsp
          cs[idx] (List.getElem_mem hidx)
        rw [Label.binders_app, Nat.add_zero]
        exact hsame _ (List.getElem_mem hidx) (.check a) ha hja j T hT
    · rcases l with _ | _ | _ | h
      · simp [judgeStep] at hj
      · simp [judgeStep] at hj
      · rcases cs with _ | ⟨b, _ | ⟨d, cs⟩⟩
        · simp [judgeStep] at hj
        · obtain ⟨pl, pcs, rfl⟩ := exists_node P
          rcases pl with _ | _ | _ | _
          · simp [judgeStep] at hj
          · rcases pcs with _ | ⟨a, _ | ⟨b', _ | ⟨d, pcs⟩⟩⟩
            · simp [judgeStep] at hj
            · simp [judgeStep] at hj
            · simp only [judgeStep, List.map_cons, List.map_nil, RoseTree.label_node,
                RoseTree.children_node] at hj
              obtain ⟨ha, hb'⟩ := typeShape_pi hmd
              obtain ⟨hocc, hocc₀, hlong⟩ := hext b (by simp) a (.check b') ha hb' hj
              refine ⟨fun j T hT ↦ appliedAt_node_iff.mpr ⟨(fun i h ↦ nomatch h),
                fun idx hidx ↦ ?_⟩, fun P hP ↦ ?_⟩
              · rcases idx with _ | idx
                · exact hocc j T hT
                · exact absurd hidx (by simp only [List.length_cons, List.length_nil]; omega)
              · obtain rfl := Mode.check.inj hP
                change EtaLong (Expr.pi a b').erase (Expr.lam b) = true
                rw [erase_pi, etaLong_arrow_lam, Bool.and_eq_true]
                exact ⟨hlong b' rfl, hocc₀⟩
            · simp [judgeStep] at hj
          · simp [judgeStep] at hj
          · simp [judgeStep] at hj
        · simp [judgeStep] at hj
      · simp only [judgeStep, Bool.and_eq_true] at hj
        obtain ⟨hP, hm⟩ := hj
        obtain ⟨C, hC, hS⟩ : ∃ C, classOf sig Γ h = some C ∧
            spine Γ C (cs.map fun c ↦ (c, judge sig c)) = some P := by
          split at hm
          · next R hR =>
            obtain ⟨C, hC, hS⟩ := Option.bind_eq_some_iff.mp hR
            exact ⟨C, hC, hS.trans (congrArg some (beq_iff_eq.mp hm))⟩
          · exact absurd hm Bool.false_ne_true
        have hCs : C.TypeShape = true := by
          rcases h with i | c
          · exact varType_typeShape hΓ hC
          · exact Sig.ok_typeShape hsig c C hC
        refine ⟨fun j T hT ↦ appliedAt_node_iff.mpr ⟨fun i hi hij ↦ ?_, fun idx hidx ↦ ?_⟩,
          fun P' hP' ↦ ?_⟩
        · cases hi
          subst hij
          obtain rfl : C = T := Option.some.inj (hC.symm.trans hT)
          exact spine_etaLongSpine cs C P hCs hS hP fun m hm a ha hja ↦
            (ih m hm Γ (.check a) hΓ ha hja).2 a rfl
        · obtain ⟨a, ha, hja⟩ := spine_args_shape cs C P hCs hS cs[idx] (List.getElem_mem hidx)
          rw [Label.binders_app, Nat.add_zero]
          exact hsame _ (List.getElem_mem hidx) (.check a) ha hja j T hT
        · obtain rfl := Mode.check.inj hP'
          obtain ⟨k, hk⟩ := erase_of_typeShape_isApp hmd hP
          rw [hk, EtaLong, etaLong_node]
          rfl

/-- The instantiation along a concatenation of spines is along the first, then the second. -/
theorem spine_append (Γ : Ctx) (c : Expr) (L₁ L₂ : List (Expr × (Ctx → Mode → Bool))) :
    spine Γ c (L₁ ++ L₂) = (spine Γ c L₁).bind fun c' ↦ spine Γ c' L₂ :=
  List.foldlM_append

/-- The η-expansion of an atomic term checks against the type it synthesizes
(\[WatkinsEtAl2002\], Lemma 36): where a head's classifier instantiates along a spine to
a type, in a context of types of the shape of types, the head applied to the spine, η-expanded at
the type's erasure, checks against the type. -/
theorem judge_eta {sig : Sig} (hsig : sig.ok = true) :
    ∀ (α : SimpleTy) (Γ : Ctx) (h : Head) (ms : List Expr) (C P : Expr),
      (∀ a ∈ Γ, a.TypeShape = true) → judge sig P Γ .type = true → P.erase = α →
      classOf sig Γ h = some C → spine Γ C (ms.map fun m ↦ (m, judge sig m)) = some P →
      judge sig (eta α h ms) Γ (.check P) = true :=
  RoseTree.ind fun l cs ih Γ h ms C P hΓ hP hα hC hS ↦ by
    obtain ⟨pl, pcs, rfl⟩ := exists_node P
    have hP' := hP
    rw [judge, judgeWith_node] at hP'
    rcases pl with _ | _ | _ | (i | c)
    · simp [judgeStep] at hP'
    · rcases pcs with _ | ⟨A, _ | ⟨B, _ | ⟨d, pcs⟩⟩⟩
      · simp [judgeStep] at hP'
      · simp [judgeStep] at hP'
      · simp only [judgeStep, List.map_cons, List.map_nil, Bool.and_eq_true] at hP'
        obtain ⟨hA, hB⟩ := hP'
        have hpe := hα
        rw [show (RoseTree.node Label.pi [A, B] : Expr) = Expr.pi A B from rfl, erase_pi] at hpe
        obtain ⟨rfl, rfl⟩ : l = .arrow ∧ cs = [(Expr.erase A), (Expr.erase B)] := by
          have := hpe.symm
          rwa [RoseTree.node_eq_iff, RoseTree.label_node, RoseTree.children_node] at this
        have hAs : (Expr.TypeShape A) = true := (judgeWith_typeShape A Γ).2 hA
        have hΓ' : ∀ x ∈ A :: Γ, (Expr.TypeShape x) = true := fun x hx ↦ by
          rcases List.mem_cons.mp hx with rfl | hx
          · exact hAs
          · exact hΓ x hx
        -- the expansion of the bound variable checks against its type
        have hx :
            judge sig (eta (Expr.erase A) (.var 0) []) (A :: Γ) (.check (Expr.shift A)) = true := by
          refine ih (Expr.erase A) (by simp) (A :: Γ) (.var 0) [] (Expr.shift A) (Expr.shift A) hΓ'
            (judge_shift (Sig.ok_closed hsig) A Γ A .type hA) (erase_rename A _) ?_ rfl
          change (A :: Γ)[0]?.map (fun (a : Expr) ↦ a.rename (· + (0 + 1))) = some (Expr.shift A)
          rfl
        -- substituting it for the bound variable of the codomain gives the codomain back
        have hocc := (judge_appliedAt hsig B (A :: Γ) .type hΓ' rfl hB).1 0
          (Expr.rename A (· + (0 + 1))) rfl
        rw [erase_rename] at hocc
        have hBid := hsub_eta_identity hocc
        -- the weakened spine instantiates the weakened classifier to the weakened type
        have hS₁ := spine_rename (Δ := A :: Γ) (ρ := Nat.succ) ms C _ hS
          fun m _ a hm ↦ judge_shift (Sig.ok_closed hsig) m Γ A (.check a) hm
        have hS' : spine (A :: Γ) (C.rename Nat.succ)
            ((ms.map Expr.shift ++ [eta (Expr.erase A) (.var 0) []]).map fun m ↦ (m, judge sig m)) =
              some B := by
          rw [List.map_append, spine_append]
          change spine (A :: Γ) (C.rename Nat.succ)
            ((ms.map fun m ↦ m.rename Nat.succ).map fun m ↦ (m, judge sig m)) >>= _ = _
          rw [hS₁, Option.bind_eq_bind, Option.bind_some,
            show (RoseTree.node Label.pi [A, B] : Expr) = Expr.pi A B from rfl, rename_pi]
          simp only [spine, List.map_cons, List.map_nil, List.foldlM_cons, List.foldlM_nil,
            Expr.pi, RoseTree.label_node, RoseTree.children_node]
          change (if judge sig (eta (Expr.erase A) (.var 0) []) (A :: Γ)
              (.check (Expr.shift A)) = true then
            hsub (Expr.erase (Expr.shift A)) (eta (Expr.erase A) (.var 0) [])
              (Expr.rename B (liftR Nat.succ)) 0
            else none).bind _ = _
          simp only [hx, ↓reduceIte]
          rw [Expr.shift, erase_rename, hBid]
          rfl
        rw [eta_arrow, judge, Expr.lam, judgeWith_node]
        simp only [judgeStep, List.map_cons, List.map_nil, RoseTree.label_node,
          RoseTree.children_node]
        exact ih (Expr.erase B) (by simp) (A :: Γ) (h.rename Nat.succ) _ (C.rename Nat.succ) B hΓ'
          hB
          rfl (classOf_rename (Sig.ok_closed hsig) (CtxRen.succ Γ A) hC) hS'
      · simp [judgeStep] at hP'
    · simp [judgeStep] at hP'
    · simp [judgeStep] at hP'
    · have hpe : Expr.erase (RoseTree.node (Label.app (.const c)) pcs) =
          RoseTree.node (.base c) [] := by
        rw [erase_node]
        rfl
      rw [hpe] at hα
      obtain ⟨rfl, rfl⟩ : l = .base c ∧ cs = [] := by
        have := hα.symm
        rwa [RoseTree.node_eq_iff, RoseTree.label_node, RoseTree.children_node] at this
      have hb : (classOf sig Γ h).bind
          (fun a ↦ spine Γ a (ms.map fun c ↦ (c, judgeWith (· == ·) sig c))) =
            some (RoseTree.node (Label.app (.const c)) pcs) := by
        rw [hC, Option.bind_some]
        exact hS
      rw [eta_base, judge, Expr.app, judgeWith_node]
      simp only [judgeStep, hb, beq_self_eq_true, Bool.and_true]
      rfl

end Geb.LF

end
