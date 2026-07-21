import GebLean.Ramified.SigEquiv
import GebLean.Ramified.SynCat

/-!
# Presentation equivalences and the syntactic-category equivalence

A `PresentationEquiv` between two presentations is a signature isomorphism
together with a sort-indexed equivalence of the standard models' carriers that
commutes with every operation's interpretation. Along such an equivalence the
term translation of `SortedSigEquiv.tmMap` preserves interpretation at the
standard model (`tmMap_eval`), so it descends to the interpretative quotient and
induces a functor between the syntactic categories (`synCatFunctor`). The
inverse presentation equivalence (`symm`) induces the inverse functor, and the
two assemble into an equivalence of syntactic categories (`synCatEquiv`).

This is the standard signature-morphism/reduct machinery of algebraic
specification (Sannella–Tarlecki, Chapter 1), specialized to signature
isomorphisms and their action on the syntactic (term-clone) category: a
signature isomorphism induces an equivalence of the associated Lawvere theories.

## Main definitions

* `PresentationEquiv` — a presentation isomorphism: a signature isomorphism and
  a carrier equivalence commuting with the operation interpretations.
* `PresentationEquiv.mapEnv` — the environment transport along the equivalence.
* `PresentationEquiv.synCatFunctor` — the induced functor of syntactic
  categories.
* `PresentationEquiv.symm` — the inverse presentation equivalence.
* `PresentationEquiv.synCatEquiv` — the induced equivalence of syntactic
  categories.

## Main statements

* `PresentationEquiv.tmMap_eval` — the term translation preserves interpretation
  at the standard model.

## References

The signature-morphism and reduct machinery follows D. Sannella, A. Tarlecki,
"Foundations of Algebraic Specification and Formal Software Development",
Springer, 2012, DOI `10.1007/978-3-642-17336-3`, Chapter 1.

## Tags

presentation, signature isomorphism, reduct, syntactic category, Lawvere theory,
equivalence of categories, term translation
-/

namespace GebLean.Ramified

open CategoryTheory

/-- A presentation isomorphism: a signature isomorphism `sigEquiv`, a
sort-indexed equivalence `carrierEquiv` of the standard models' carriers (an
equivalence, not an equality: two presentations built over distinct but
equivalent base carriers are related only by an equivalence of carriers, never
by an equality of them), and the commutation `interpOp_comm` of the
carrier equivalence with every operation's interpretation. The standard notion
of an isomorphism of presentations (Sannella–Tarlecki, Chapter 1). -/
structure PresentationEquiv (P P' : Presentation) where
  /-- The underlying signature isomorphism. -/
  sigEquiv : SortedSigEquiv P.sig P'.sig
  /-- The carrier equivalence at each sort. -/
  carrierEquiv : ∀ s, (standardModel P).carrier s ≃
    (standardModel P').carrier (sigEquiv.sortEquiv s)
  /-- The carrier equivalence commutes with the operation interpretations: the
  interpretation of a translated operation on translated arguments is the
  carrier-equivalence image of the original interpretation. -/
  interpOp_comm : ∀ (o : P.sig.Op)
      (args : ∀ i : Fin (P.sig.arity o).length, (standardModel P).carrier ((P.sig.arity o).get i)),
    cast (congrArg (standardModel P').carrier (sigEquiv.result_comm o))
        ((standardModel P').interpOp (sigEquiv.opEquiv o)
          (fun j => cast (congrArg (standardModel P').carrier (sigEquiv.get_arity o j))
            (carrierEquiv _ (args (Fin.cast (sigEquiv.arity_length o) j)))))
      = carrierEquiv (P.sig.result o) ((standardModel P).interpOp o args)

/-- Evaluation of a composite tuple is evaluation of the second at the
evaluated first (the semantic clone law `Tm.eval_subst`, componentwise). -/
theorem HomTuple.eval_comp {P : Presentation} {Γ Δ E : Ctx P.S}
    (f : HomTuple P Γ Δ) (g : HomTuple P Δ E) (M : SortedModel P.sig) (ρ : M.Env Γ) :
    (HomTuple.comp f g).eval M ρ = g.eval M (f.eval M ρ) :=
  funext (fun i => Tm.eval_subst M (g i) f ρ)

/-- Evaluation of `eqToHom` transports the environment along the object
equality. -/
theorem Hom.eval_eqToHom {P : Presentation} {Γ Δ : SynCat P (interpQuotRel P)}
    (h : Γ = Δ) (ρ : (standardModel P).Env Γ) :
    Hom.eval (eqToHom h) ρ = cast (congrArg (standardModel P).Env h) ρ := by
  subst h; rfl

/-- Two homs at the interpretative quotient are equal when their evaluations
agree on every environment. -/
theorem Hom.ext_eval {P : Presentation} {Γ Δ : Ctx P.S}
    {f g : Hom P (interpQuotRel P) Γ Δ}
    (h : ∀ ρ, Hom.eval f ρ = Hom.eval g ρ) : f = g := by
  induction f using Quotient.ind with
  | _ f' =>
  induction g using Quotient.ind with
  | _ g' => exact Quotient.sound (fun i ρ => congrFun (h ρ) i)

namespace PresentationEquiv

variable {P P' : Presentation}

/-- The environment transport along the equivalence: an environment over `Γ` in
the standard model of `P` becomes an environment over `Γ.map sortEquiv` in the
standard model of `P'`, pushing each value forward through `carrierEquiv` and the
mapped-context sort equality. -/
def mapEnv (e : PresentationEquiv P P') {Γ : Ctx P.S} (ρ : (standardModel P).Env Γ) :
    (standardModel P').Env (Γ.map e.sigEquiv.sortEquiv) :=
  fun j => cast (congrArg (standardModel P').carrier
      (e.sigEquiv.get_ctx Γ (Fin.cast (e.sigEquiv.ctx_length Γ).symm j)).symm)
    (e.carrierEquiv _ (ρ (Fin.cast (e.sigEquiv.ctx_length Γ).symm j)))

/-- The carrier equivalence commutes with transport along a sort equality. -/
theorem carrierEquiv_cast (e : PresentationEquiv P P') {a b : P.S} (h : a = b)
    (x : (standardModel P).carrier a) :
    cast (congrArg (standardModel P').carrier (congrArg e.sigEquiv.sortEquiv h))
        (e.carrierEquiv a x)
      = e.carrierEquiv b (cast (congrArg (standardModel P).carrier h) x) := by
  subst h; rfl

/-- The term translation preserves interpretation at the standard model: a term
and its translation denote carrier-equivalent values, the translation over the
mapped environment matching the carrier-equivalence image of the original. -/
theorem tmMap_eval (e : PresentationEquiv P P') {Γ : Ctx P.S} {s : P.S}
    (t : Tm P.sig Γ s) (ρ : (standardModel P).Env Γ) :
    (e.sigEquiv.tmMap t).eval (standardModel P') (e.mapEnv ρ)
      = e.carrierEquiv s (t.eval (standardModel P) ρ) := by
  induction t using PolyFix.ind with
  | step i childx ih =>
    cases i with
    | inl a =>
      refine Eq.trans (Tm.eval_transport (standardModel P') (e.mapEnv ρ)
          ((e.sigEquiv.get_ctx Γ a.1).trans (congrArg e.sigEquiv.sortEquiv a.2))
          (Tm.var (Fin.cast (e.sigEquiv.ctx_length Γ) a.1))) ?_
      refine Eq.trans ?_ (e.carrierEquiv_cast a.2 (ρ a.1))
      exact cast_cast _ _ _
    | inr o =>
      have key : ∀ j, (Tm.reind (e.sigEquiv.get_arity o.1 j)
          (e.sigEquiv.tmMap (childx (Fin.cast (e.sigEquiv.arity_length o.1) j)))).eval
            (standardModel P') (e.mapEnv ρ)
          = cast (congrArg (standardModel P').carrier (e.sigEquiv.get_arity o.1 j))
              (e.carrierEquiv _ (Tm.eval (standardModel P) ρ
                (childx (Fin.cast (e.sigEquiv.arity_length o.1) j)))) := by
        intro j
        rw [Tm.eval_transport]
        exact congrArg (cast _) (ih (Fin.cast (e.sigEquiv.arity_length o.1) j))
      have hop : (Tm.op (e.sigEquiv.opEquiv o.1) (fun j => Tm.reind (e.sigEquiv.get_arity o.1 j)
            (e.sigEquiv.tmMap (childx (Fin.cast (e.sigEquiv.arity_length o.1) j))))).eval
            (standardModel P') (e.mapEnv ρ)
          = (standardModel P').interpOp (e.sigEquiv.opEquiv o.1)
              (fun j => cast (congrArg (standardModel P').carrier (e.sigEquiv.get_arity o.1 j))
                (e.carrierEquiv _ (Tm.eval (standardModel P) ρ
                  (childx (Fin.cast (e.sigEquiv.arity_length o.1) j))))) :=
        congrArg ((standardModel P').interpOp (e.sigEquiv.opEquiv o.1)) (funext key)
      refine Eq.trans (Tm.eval_transport (standardModel P') (e.mapEnv ρ)
          ((e.sigEquiv.result_comm o.1).trans (congrArg e.sigEquiv.sortEquiv o.2))
          (Tm.op (e.sigEquiv.opEquiv o.1) (fun j => Tm.reind (e.sigEquiv.get_arity o.1 j)
            (e.sigEquiv.tmMap (childx (Fin.cast (e.sigEquiv.arity_length o.1) j)))))) ?_
      rw [hop]
      refine Eq.trans ?_ (e.carrierEquiv_cast o.2
        ((standardModel P).interpOp o.1 (fun j => Tm.eval (standardModel P) ρ (childx j))))
      rw [← e.interpOp_comm o.1 (fun j => Tm.eval (standardModel P) ρ (childx j))]
      exact (cast_cast _ _ _).symm

/-- The inverse environment transport: an environment over `Γ.map sortEquiv` in
the standard model of `P'` becomes an environment over `Γ` in the standard model
of `P`, pulling each value back through `carrierEquiv` and the mapped-context
sort equality. Inverse to `mapEnv`. -/
def unmapEnv (e : PresentationEquiv P P') {Γ : Ctx P.S}
    (ρ' : (standardModel P').Env (Γ.map e.sigEquiv.sortEquiv)) : (standardModel P).Env Γ :=
  fun i => (e.carrierEquiv (Γ.get i)).symm
    (cast (congrArg (standardModel P').carrier (e.sigEquiv.get_ctx Γ i))
      (ρ' (Fin.cast (e.sigEquiv.ctx_length Γ) i)))

/-- `mapEnv` is a left inverse of `unmapEnv`. -/
theorem mapEnv_unmapEnv (e : PresentationEquiv P P') {Γ : Ctx P.S}
    (ρ' : (standardModel P').Env (Γ.map e.sigEquiv.sortEquiv)) :
    e.mapEnv (e.unmapEnv ρ') = ρ' := by
  funext j
  simp only [mapEnv, unmapEnv, Equiv.apply_symm_apply, cast_cast]
  exact cast_eq _ _

/-- The term translation preserves interpretation at every environment: over any
environment `ρ'` on the mapped context, the translation denotes the
carrier-equivalence image of the original term at the pulled-back environment. -/
theorem tmMap_eval' (e : PresentationEquiv P P') {Γ : Ctx P.S} {s : P.S}
    (t : Tm P.sig Γ s) (ρ' : (standardModel P').Env (Γ.map e.sigEquiv.sortEquiv)) :
    (e.sigEquiv.tmMap t).eval (standardModel P') ρ'
      = e.carrierEquiv s (t.eval (standardModel P) (e.unmapEnv ρ')) := by
  have h := e.tmMap_eval t (e.unmapEnv ρ')
  rw [e.mapEnv_unmapEnv] at h
  exact h

/-- `unmapEnv` is a left inverse of `mapEnv`. -/
theorem unmapEnv_mapEnv (e : PresentationEquiv P P') {Γ : Ctx P.S}
    (ρ : (standardModel P).Env Γ) : e.unmapEnv (e.mapEnv ρ) = ρ := by
  funext i
  simp only [unmapEnv, mapEnv, cast_cast]
  exact (e.carrierEquiv (Γ.get i)).symm_apply_apply (ρ i)

/-- The morphism-tuple translation: translate each component by `tmMap`,
transported along the mapped-context sort equality. -/
def mapTuple (e : PresentationEquiv P P') {Γ Δ : Ctx P.S} (f : HomTuple P Γ Δ) :
    HomTuple P' (Γ.map e.sigEquiv.sortEquiv) (Δ.map e.sigEquiv.sortEquiv) :=
  fun j => Tm.reind (e.sigEquiv.get_ctx Δ (Fin.cast (e.sigEquiv.ctx_length Δ).symm j)).symm
    (e.sigEquiv.tmMap (f (Fin.cast (e.sigEquiv.ctx_length Δ).symm j)))

/-- Evaluation of a translated tuple is the mapped evaluation of the original at
the pulled-back environment: the translation conjugates evaluation by the
environment transport. -/
theorem mapTuple_eval_env (e : PresentationEquiv P P') {Γ Δ : Ctx P.S}
    (f : HomTuple P Γ Δ) (ρ' : (standardModel P').Env (Γ.map e.sigEquiv.sortEquiv)) :
    (e.mapTuple f).eval (standardModel P') ρ'
      = e.mapEnv ((f.eval (standardModel P) (e.unmapEnv ρ'))) := by
  funext j
  simp only [HomTuple.eval, mapTuple, mapEnv, Tm.eval_transport, tmMap_eval']

/-- The morphism map of the induced functor: translate a representative tuple by
`mapTuple` and re-quotient. Well-defined on the interpretative quotient because
`mapTuple` conjugates evaluation by the environment transport
(`mapTuple_eval_env`). -/
def mapHom (e : PresentationEquiv P P') {Γ Δ : Ctx P.S}
    (f : Hom P (interpQuotRel P) Γ Δ) :
    Hom P' (interpQuotRel P')
      (Γ.map e.sigEquiv.sortEquiv) (Δ.map e.sigEquiv.sortEquiv) :=
  Quotient.liftOn f (fun f' => Quotient.mk _ (e.mapTuple f'))
    (fun f₁ f₂ h => Quotient.sound (fun j ρ' => by
      have key : (f₁.eval (standardModel P) (e.unmapEnv ρ'))
          = (f₂.eval (standardModel P) (e.unmapEnv ρ')) :=
        funext (fun i => h i (e.unmapEnv ρ'))
      calc (e.mapTuple f₁ j).eval (standardModel P') ρ'
          = e.mapEnv (f₁.eval (standardModel P) (e.unmapEnv ρ')) j :=
            congrFun (e.mapTuple_eval_env f₁ ρ') j
        _ = e.mapEnv (f₂.eval (standardModel P) (e.unmapEnv ρ')) j := by rw [key]
        _ = (e.mapTuple f₂ j).eval (standardModel P') ρ' :=
            (congrFun (e.mapTuple_eval_env f₂ ρ') j).symm))

/-- The functor of syntactic categories induced by a presentation equivalence:
the object map `List.map sortEquiv` and the morphism map `mapHom`. Its identity
and composition laws hold by interpretative equality (`mapTuple_eval_env`), no
syntactic identities needed (the `foInclusion` pattern). -/
def synCatFunctor (e : PresentationEquiv P P') :
    SynCat P (interpQuotRel P) ⥤ SynCat P' (interpQuotRel P') where
  obj Γ := (Γ : Ctx P.S).map e.sigEquiv.sortEquiv
  map {Γ Δ} f := e.mapHom f
  map_id Γ := by
    refine Quotient.sound (fun j ρ' => ?_)
    calc (e.mapTuple (HomTuple.id P Γ) j).eval (standardModel P') ρ'
        = e.mapEnv ((HomTuple.id P Γ).eval (standardModel P) (e.unmapEnv ρ')) j :=
          congrFun (e.mapTuple_eval_env (HomTuple.id P Γ) ρ') j
      _ = e.mapEnv (e.unmapEnv ρ') j := rfl
      _ = ρ' j := congrFun (e.mapEnv_unmapEnv ρ') j
  map_comp {Γ Δ E} f g := by
    induction f using Quotient.ind with
    | _ f' =>
    induction g using Quotient.ind with
    | _ g' =>
      refine Quotient.sound (fun j ρ' => ?_)
      calc (e.mapTuple (HomTuple.comp f' g') j).eval (standardModel P') ρ'
          = e.mapEnv ((HomTuple.comp f' g').eval (standardModel P) (e.unmapEnv ρ')) j :=
            congrFun (e.mapTuple_eval_env (HomTuple.comp f' g') ρ') j
        _ = e.mapEnv (g'.eval (standardModel P) (f'.eval (standardModel P) (e.unmapEnv ρ'))) j := by
            rw [HomTuple.eval_comp]
        _ = e.mapEnv (g'.eval (standardModel P)
              (e.unmapEnv (e.mapEnv (f'.eval (standardModel P) (e.unmapEnv ρ'))))) j := by
            rw [e.unmapEnv_mapEnv]
        _ = (HomTuple.comp (e.mapTuple f') (e.mapTuple g') j).eval (standardModel P') ρ' := by
            have hc := HomTuple.eval_comp (e.mapTuple f') (e.mapTuple g') (standardModel P') ρ'
            rw [e.mapTuple_eval_env f', e.mapTuple_eval_env g'] at hc
            exact (congrFun hc j).symm

/-- The inverse carrier equivalence commutes with transport along a sort
equality. -/
theorem carrierEquiv_symm_cast (e : PresentationEquiv P P') {a b : P.S} (h : a = b)
    (y : (standardModel P').carrier (e.sigEquiv.sortEquiv a)) :
    cast (congrArg (standardModel P).carrier h) ((e.carrierEquiv a).symm y)
      = (e.carrierEquiv b).symm
          (cast (congrArg (standardModel P').carrier (congrArg e.sigEquiv.sortEquiv h)) y) := by
  subst h; rfl

/-- The forward operation-commutation solved for the `P`-interpretation. -/
theorem interpOp_symm_apply (e : PresentationEquiv P P') (o : P.sig.Op)
    (args : ∀ i : Fin (P.sig.arity o).length, (standardModel P).carrier ((P.sig.arity o).get i)) :
    (standardModel P).interpOp o args
      = (e.carrierEquiv (P.sig.result o)).symm
          (cast (congrArg (standardModel P').carrier (e.sigEquiv.result_comm o))
            ((standardModel P').interpOp (e.sigEquiv.opEquiv o)
              (fun j => cast (congrArg (standardModel P').carrier (e.sigEquiv.get_arity o j))
                (e.carrierEquiv _ (args (Fin.cast (e.sigEquiv.arity_length o) j)))))) := by
  rw [e.interpOp_comm o args, Equiv.symm_apply_apply]

/-- The inverse presentation equivalence: the inverse signature isomorphism, the
inverse carrier equivalences (conjugated by the sort round trip), and the
commutation re-derived from the forward one. -/
def symm (e : PresentationEquiv P P') : PresentationEquiv P' P where
  sigEquiv := e.sigEquiv.symm
  carrierEquiv := fun s' =>
    (Equiv.cast (congrArg (standardModel P').carrier
        (e.sigEquiv.sortEquiv.apply_symm_apply s').symm)).trans
      (e.carrierEquiv (e.sigEquiv.sortEquiv.symm s')).symm
  interpOp_comm := fun o' args' => by
    rw [e.interpOp_symm_apply]
    simp only [Equiv.trans_apply, Equiv.cast_apply]
    rw [e.carrierEquiv_symm_cast]
    case h => exact e.sigEquiv.symm.result_comm o'
    congr 1
    apply eq_of_heq
    refine (cast_heq _ _).trans ((cast_heq _ _).trans (HEq.trans ?_ (cast_heq _ _).symm))
    congr 1
    · exact e.sigEquiv.opEquiv.apply_symm_apply o'
    · have hlen := congrArg (fun o => (P'.sig.arity o).length)
        (e.sigEquiv.opEquiv.apply_symm_apply o')
      refine Function.hfunext (congrArg Fin hlen) ?_
      intro a a' ha
      have cancel : ∀ {s t : P.S} (h : s = t)
          (w : (standardModel P').carrier (e.sigEquiv.sortEquiv s)),
          HEq (e.carrierEquiv t (cast (congrArg (standardModel P).carrier h)
            ((e.carrierEquiv s).symm w))) w := by
        intro s t h w
        subst h
        rw [cast_eq]
        exact heq_of_eq (Equiv.apply_symm_apply _ _)
      have hXZ := e.sigEquiv.symm.get_arity o'
        (Fin.cast (e.sigEquiv.arity_length (e.sigEquiv.symm.opEquiv o')) a)
      refine (cast_heq _ _).trans ((cancel hXZ _).trans ((cast_heq _ _).trans ?_))
      congr 1
      apply Fin.ext
      simp only [Fin.val_cast]
      exact (Fin.heq_ext_iff hlen).mp ha

/-- Evaluation of a translated hom is the mapped evaluation at the pulled-back
environment. -/
theorem mapHom_eval (e : PresentationEquiv P P') {Γ Δ : Ctx P.S}
    (f : Hom P (interpQuotRel P) Γ Δ)
    (ρ' : (standardModel P').Env (Γ.map e.sigEquiv.sortEquiv)) :
    Hom.eval (e.mapHom f) ρ' = e.mapEnv (Hom.eval f (e.unmapEnv ρ')) := by
  induction f using Quotient.ind with
  | _ f' => exact e.mapTuple_eval_env f' ρ'

/-- The inverse carrier equivalence cancels the forward one, up to the sort
round trip. -/
theorem symm_carrierEquiv_comp (e : PresentationEquiv P P') {s : P.S}
    (x : (standardModel P).carrier s) :
    e.symm.carrierEquiv (e.sigEquiv.sortEquiv s) (e.carrierEquiv s x)
      = cast (congrArg (standardModel P).carrier
          (e.sigEquiv.sortEquiv.symm_apply_apply s).symm) x := by
  change (e.carrierEquiv (e.sigEquiv.sortEquiv.symm (e.sigEquiv.sortEquiv s))).symm
      (cast (congrArg (standardModel P').carrier
        (e.sigEquiv.sortEquiv.apply_symm_apply (e.sigEquiv.sortEquiv s)).symm)
        (e.carrierEquiv s x))
    = cast (congrArg (standardModel P).carrier
        (e.sigEquiv.sortEquiv.symm_apply_apply s).symm) x
  rw [Equiv.symm_apply_eq, ← e.carrierEquiv_cast]
  exact (e.sigEquiv.sortEquiv.symm_apply_apply s).symm

/-- The double environment transport (forward then inverse) is the context
round-trip cast. -/
theorem symm_mapEnv_mapEnv (e : PresentationEquiv P P') {Γ : Ctx P.S}
    (ρ : (standardModel P).Env Γ) :
    e.symm.mapEnv (e.mapEnv ρ)
      = cast (congrArg (standardModel P).Env (e.sigEquiv.ctx_map_map Γ).symm) ρ := by
  have hcancel : ∀ (s : P.S) (s' : P'.S) (hs : e.sigEquiv.sortEquiv s = s')
      (x : (standardModel P).carrier s),
      HEq (e.symm.carrierEquiv s'
        (cast (congrArg (standardModel P').carrier hs) (e.carrierEquiv s x))) x := by
    intro s s' hs x
    subst hs
    rw [cast_eq, e.symm_carrierEquiv_comp]
    exact cast_heq _ _
  suffices h : HEq (e.symm.mapEnv (e.mapEnv ρ)) ρ by
    exact (cast_eq_iff_heq.mpr h.symm).symm
  refine Function.hfunext (congrArg Fin (congrArg List.length (e.sigEquiv.ctx_map_map Γ))) ?_
  intro k k' hk
  simp only [mapEnv]
  refine HEq.trans (cast_heq _ _) ?_
  refine HEq.trans (hcancel _ _ ?_ _) ?_
  · exact (e.sigEquiv.get_ctx Γ _).symm
  · congr 1
    apply Fin.ext
    simp only [Fin.val_cast]
    exact (Fin.heq_ext_iff (congrArg List.length (e.sigEquiv.ctx_map_map Γ))).mp hk

/-- The double inverse environment transport recovers the original after the
context round-trip cast. -/
theorem unmapEnv_symm_unmapEnv (e : PresentationEquiv P P') {Γ : Ctx P.S}
    (ρ : (standardModel P).Env
      ((Γ.map e.sigEquiv.sortEquiv).map e.sigEquiv.sortEquiv.symm)) :
    e.unmapEnv (e.symm.unmapEnv ρ)
      = cast (congrArg (standardModel P).Env (e.sigEquiv.ctx_map_map Γ)) ρ := by
  have key : cast (congrArg (standardModel P).Env (e.sigEquiv.ctx_map_map Γ).symm)
      (e.unmapEnv (e.symm.unmapEnv ρ)) = ρ := by
    rw [← e.symm_mapEnv_mapEnv, e.mapEnv_unmapEnv, e.symm.mapEnv_unmapEnv]
  conv_rhs => rw [← key]
  rw [cast_cast, cast_eq]

/-- The forward carrier equivalence cancels the inverse one, up to the sort
round trip: the mirror of `symm_carrierEquiv_comp` with the roles of the two
carrier equivalences exchanged. -/
theorem carrierEquiv_symm_carrierEquiv_comp (e : PresentationEquiv P P') {s' : P'.S}
    (y : (standardModel P').carrier s') :
    e.carrierEquiv (e.sigEquiv.sortEquiv.symm s') (e.symm.carrierEquiv s' y)
      = cast (congrArg (standardModel P').carrier
          (e.sigEquiv.sortEquiv.apply_symm_apply s').symm) y := by
  change e.carrierEquiv (e.sigEquiv.sortEquiv.symm s')
      ((e.carrierEquiv (e.sigEquiv.sortEquiv.symm s')).symm
        (cast (congrArg (standardModel P').carrier
          (e.sigEquiv.sortEquiv.apply_symm_apply s').symm) y))
    = cast (congrArg (standardModel P').carrier
        (e.sigEquiv.sortEquiv.apply_symm_apply s').symm) y
  exact Equiv.apply_symm_apply _ _

/-- The double environment transport starting with the inverse: the mirror of
`symm_mapEnv_mapEnv`. -/
theorem mapEnv_symm_mapEnv (e : PresentationEquiv P P') {Δ : Ctx P'.S}
    (ρ : (standardModel P').Env Δ) :
    e.mapEnv (e.symm.mapEnv ρ)
      = cast (congrArg (standardModel P').Env (e.sigEquiv.ctx_map_map' Δ).symm) ρ := by
  have hcancel : ∀ (s' : P'.S) (s : P.S) (hs : e.sigEquiv.sortEquiv.symm s' = s)
      (x : (standardModel P').carrier s'),
      HEq (e.carrierEquiv s
        (cast (congrArg (standardModel P).carrier hs) (e.symm.carrierEquiv s' x))) x := by
    intro s' s hs x
    subst hs
    rw [cast_eq, e.carrierEquiv_symm_carrierEquiv_comp]
    exact cast_heq _ _
  suffices h : HEq (e.mapEnv (e.symm.mapEnv ρ)) ρ by
    exact (cast_eq_iff_heq.mpr h.symm).symm
  refine Function.hfunext (congrArg Fin (congrArg List.length (e.sigEquiv.ctx_map_map' Δ))) ?_
  intro k k' hk
  simp only [mapEnv]
  refine HEq.trans (cast_heq _ _) ?_
  refine HEq.trans (hcancel _ _ ?_ _) ?_
  · exact (e.sigEquiv.symm.get_ctx Δ _).symm
  · congr 1
    apply Fin.ext
    simp only [Fin.val_cast]
    exact (Fin.heq_ext_iff (congrArg List.length (e.sigEquiv.ctx_map_map' Δ))).mp hk

/-- The double inverse environment transport starting with the forward inverse:
the mirror of `unmapEnv_symm_unmapEnv`. -/
theorem symm_unmapEnv_unmapEnv (e : PresentationEquiv P P') {Δ : Ctx P'.S}
    (ρ : (standardModel P').Env
      ((Δ.map e.sigEquiv.sortEquiv.symm).map e.sigEquiv.sortEquiv)) :
    e.symm.unmapEnv (e.unmapEnv ρ)
      = cast (congrArg (standardModel P').Env (e.sigEquiv.ctx_map_map' Δ)) ρ := by
  have key : cast (congrArg (standardModel P').Env (e.sigEquiv.ctx_map_map' Δ).symm)
      (e.symm.unmapEnv (e.unmapEnv ρ)) = ρ := by
    rw [← e.mapEnv_symm_mapEnv, e.symm.mapEnv_unmapEnv, e.mapEnv_unmapEnv]
  conv_rhs => rw [← key]
  rw [cast_cast, cast_eq]

/-- The equivalence of syntactic categories induced by a presentation
equivalence: the functor of `e`, the functor of `e.symm`, and the unit and
counit isomorphisms at the propositional context round trips (their naturality
by interpretative equality, both directions of `tmMap_eval`). -/
def synCatEquiv (e : PresentationEquiv P P') :
    SynCat P (interpQuotRel P) ≌ SynCat P' (interpQuotRel P') :=
  CategoryTheory.Equivalence.mk e.synCatFunctor e.symm.synCatFunctor
    (NatIso.ofComponents
      (fun Γ => eqToIso (e.sigEquiv.ctx_map_map Γ).symm)
      (fun {Γ Δ} f => by
        apply Hom.ext_eval
        intro ρ
        change Hom.eval (Hom.comp ((𝟭 _).map f) _) ρ
          = Hom.eval (Hom.comp _ ((e.synCatFunctor ⋙ e.symm.synCatFunctor).map f)) ρ
        simp only [Functor.id_map, Functor.comp_map, synCatFunctor, eqToIso.hom]
        rw [Hom.eval_comp, Hom.eval_comp, Hom.eval_eqToHom, Hom.eval_eqToHom]
        erw [e.symm.mapHom_eval, e.mapHom_eval, e.unmapEnv_symm_unmapEnv]
        rw [e.symm_mapEnv_mapEnv]
        apply eq_of_heq
        refine (cast_heq _ _).trans (HEq.trans ?_ (cast_heq _ _).symm)
        congr 1
        exact eq_of_heq ((cast_heq _ _).trans (cast_heq _ _)).symm))
    (NatIso.ofComponents
      (fun Δ => eqToIso (e.sigEquiv.ctx_map_map' Δ))
      (fun {Γ Δ} f => by
        apply Hom.ext_eval
        intro ρ
        change Hom.eval (Hom.comp ((e.symm.synCatFunctor ⋙ e.synCatFunctor).map f) _) ρ
          = Hom.eval (Hom.comp _ ((𝟭 _).map f)) ρ
        simp only [Functor.id_map, Functor.comp_map, synCatFunctor, eqToIso.hom]
        rw [Hom.eval_comp, Hom.eval_comp, Hom.eval_eqToHom, Hom.eval_eqToHom]
        erw [e.mapHom_eval, e.symm.mapHom_eval, e.symm_unmapEnv_unmapEnv]
        rw [e.mapEnv_symm_mapEnv]
        apply eq_of_heq
        exact (cast_heq _ _).trans (cast_heq _ _)))

end PresentationEquiv

end GebLean.Ramified
