import GebLean.Ramified.Term

/-!
# Sorted-signature equivalences and the term translation

A `SortedSigEquiv` is a signature isomorphism between two multi-sorted
signatures: an equivalence of sort types and an equivalence of operations,
compatible with the arities and result sorts. Along such an equivalence the
term layer transports functorially: `SortedSigEquiv.tmMap` translates a term
over one signature to a term over the other, relabelling operations by the
operation equivalence and reindexing sorts by the sort equivalence. The
translation commutes with the term constructors (`tmMap_var`, `tmMap_op`),
with reindexing (`tmMap_reind`), and with substitution (`tmMap_subst`), and it
is invertible: `tmEquiv` packages the translation and its inverse as an
equivalence of term types.

This is the standard signature-morphism/reduct machinery of algebraic
specification, specialized to signature isomorphisms. The translation is the
action on terms of a signature isomorphism (a reduct along an isomorphism).

## Main definitions

* `SortedSigEquiv` — an isomorphism of multi-sorted signatures.
* `SortedSigEquiv.symm` — the inverse signature isomorphism.
* `SortedSigEquiv.sum` — the sum of two signature isomorphisms sharing a sort
  equivalence, over `SortedSig.sum`.
* `SortedSigEquiv.tmMap` — the term translation along a signature isomorphism.
* `SortedSigEquiv.tmEquiv` — the term translation packaged as an equivalence.

## Main statements

* `get_map` — reading `List.get` through `List.map`.
* `SortedSigEquiv.tmMap_var` / `tmMap_op` — the constructor-naturality of the
  translation.
* `SortedSigEquiv.tmMap_reind` — commutation with reindexing.
* `SortedSigEquiv.tmMap_subst` — commutation with substitution.

## References

The signature-morphism and reduct machinery follows D. Sannella, A. Tarlecki,
"Foundations of Algebraic Specification and Formal Software Development",
Springer, 2012, DOI `10.1007/978-3-642-17336-3`, Chapter 1.

## Tags

sorted signature, signature morphism, signature isomorphism, reduct, term
translation, free monad
-/

namespace GebLean.Ramified

/-- Reading `get` through `List.map`: the `get` of a mapped list is the map
applied to the `get` at the length-cast position. Neither core nor mathlib
carries this reading; they carry only `List.getElem_map`. -/
theorem get_map {S S' : Type} (f : S → S') (Γ : Ctx S) (i : Fin (Γ.map f).length) :
    (Γ.map f).get i = f (Γ.get (Fin.cast (by simp) i)) := by
  simp [List.get_eq_getElem]

/-- Reading `get` through a list equality: transport of the position along the
induced length equality. -/
theorem get_congr {S : Type} {l l' : List S} (h : l = l') (i : Fin l.length) :
    l.get i = l'.get (Fin.cast (congrArg List.length h) i) := by
  subst h
  rfl

/-- An isomorphism of multi-sorted signatures: an equivalence of sort types and
an equivalence of operations, compatible with arities and result sorts. The
standard notion of signature isomorphism (Sannella–Tarlecki, Chapter 1). -/
structure SortedSigEquiv {S S' : Type} (sig : SortedSig S) (sig' : SortedSig S') where
  /-- The equivalence of sort types. -/
  sortEquiv : S ≃ S'
  /-- The equivalence of operation types. -/
  opEquiv : sig.Op ≃ sig'.Op
  /-- The operation equivalence carries arities to mapped arities. -/
  arity_comm : ∀ o, sig'.arity (opEquiv o) = (sig.arity o).map sortEquiv
  /-- The operation equivalence carries result sorts to mapped result sorts. -/
  result_comm : ∀ o, sig'.result (opEquiv o) = sortEquiv (sig.result o)

namespace SortedSigEquiv

variable {S S' : Type} {sig : SortedSig S} {sig' : SortedSig S'}

/-- The mapped context has the same length as the original. -/
theorem ctx_length (e : SortedSigEquiv sig sig') (Γ : Ctx S) :
    Γ.length = (Γ.map e.sortEquiv).length := by
  simp

/-- The variable-node transport: the mapped context's sort at the cast position
is the image of the original sort. -/
theorem get_ctx (e : SortedSigEquiv sig sig') (Γ : Ctx S) (i : Fin Γ.length) :
    (Γ.map e.sortEquiv).get (Fin.cast (e.ctx_length Γ) i) = e.sortEquiv (Γ.get i) := by
  rw [get_map]
  exact congrArg e.sortEquiv (congrArg Γ.get (Fin.ext rfl))

/-- The translated arity has the same length as the original arity. -/
theorem arity_length (e : SortedSigEquiv sig sig') (o : sig.Op) :
    (sig'.arity (e.opEquiv o)).length = (sig.arity o).length := by
  simp [e.arity_comm]

/-- The operation-node transport: the translated arity's sort at a position is
the image of the original arity's sort at the cast position. -/
theorem get_arity (e : SortedSigEquiv sig sig') (o : sig.Op)
    (j : Fin (sig'.arity (e.opEquiv o)).length) :
    e.sortEquiv ((sig.arity o).get (Fin.cast (e.arity_length o) j)) =
      (sig'.arity (e.opEquiv o)).get j := by
  rw [get_congr (e.arity_comm o) j, get_map]
  exact congrArg e.sortEquiv (congrArg (sig.arity o).get (Fin.ext rfl))

/-- The inverse signature isomorphism: the equivalences reversed, with the
compatibility fields re-derived by applying the forward fields at
`opEquiv.symm o'` and cancelling. -/
def symm (e : SortedSigEquiv sig sig') : SortedSigEquiv sig' sig where
  sortEquiv := e.sortEquiv.symm
  opEquiv := e.opEquiv.symm
  arity_comm := fun o' => by
    have h := e.arity_comm (e.opEquiv.symm o')
    rw [Equiv.apply_symm_apply] at h
    rw [h, List.map_map, e.sortEquiv.symm_comp_self, List.map_id]
  result_comm := fun o' => by
    have h := e.result_comm (e.opEquiv.symm o')
    rw [Equiv.apply_symm_apply] at h
    rw [h, Equiv.symm_apply_apply]

/-- The sum of two signature isomorphisms sharing a sort equivalence: the
operation equivalence is the disjoint union of the summands', and the arity and
result compatibilities are inherited summand-wise. The signature-isomorphism
counterpart of `SortedSig.sum`. -/
def sum {sig₂ : SortedSig S} {sig₂' : SortedSig S'} (e : SortedSigEquiv sig sig')
    (e₂ : SortedSigEquiv sig₂ sig₂') (h : e₂.sortEquiv = e.sortEquiv) :
    SortedSigEquiv (sig.sum sig₂) (sig'.sum sig₂') where
  sortEquiv := e.sortEquiv
  opEquiv := Equiv.sumCongr e.opEquiv e₂.opEquiv
  arity_comm := by
    rintro (o | o₂)
    · exact e.arity_comm o
    · rw [← h]
      exact e₂.arity_comm o₂
  result_comm := by
    rintro (o | o₂)
    · exact e.result_comm o
    · rw [← h]
      exact e₂.result_comm o₂

/-- The term translation along a signature isomorphism, by `PolyFix.ind`: a
variable node becomes the reindexed translated variable; an operation node
becomes the relabelled operation applied to the reindexed translated children. -/
def tmMap (e : SortedSigEquiv sig sig') {Γ : Ctx S} {s : S} (t : Tm sig Γ s) :
    Tm sig' (Γ.map e.sortEquiv) (e.sortEquiv s) :=
  PolyFix.ind (P := polyTranslate (varOver Γ) sig.polyEndo)
    (motive := fun {s} _ => Tm sig' (Γ.map e.sortEquiv) (e.sortEquiv s))
    (fun {_s} i children ih =>
      match i, children, ih with
      | Sum.inl a, _, _ =>
          Tm.reind ((e.get_ctx Γ a.1).trans (congrArg e.sortEquiv a.2))
            (Tm.var (Fin.cast (e.ctx_length Γ) a.1))
      | Sum.inr o, _, ih =>
          Tm.reind ((e.result_comm o.val).trans (congrArg e.sortEquiv o.2))
            (Tm.op (e.opEquiv o.val)
              (fun j => Tm.reind (e.get_arity o.val j)
                (ih (Fin.cast (e.arity_length o.val) j))))) t

/-- Constructor-naturality at a variable node. -/
theorem tmMap_var (e : SortedSigEquiv sig sig') {Γ : Ctx S} (i : Fin Γ.length) :
    e.tmMap (Tm.var (sig := sig) i) =
      Tm.reind (e.get_ctx Γ i) (Tm.var (Fin.cast (e.ctx_length Γ) i)) :=
  rfl

/-- Constructor-naturality at an operation node. -/
theorem tmMap_op (e : SortedSigEquiv sig sig') {Γ : Ctx S} (o : sig.Op)
    (args : ∀ i : Fin (sig.arity o).length, Tm sig Γ ((sig.arity o).get i)) :
    e.tmMap (Tm.op o args) =
      Tm.reind (e.result_comm o) (Tm.op (e.opEquiv o)
        (fun j => Tm.reind (e.get_arity o j)
          (e.tmMap (args (Fin.cast (e.arity_length o) j))))) :=
  rfl

/-- Commutation with reindexing. -/
theorem tmMap_reind (e : SortedSigEquiv sig sig') {Γ : Ctx S} {a b : S} (h : a = b)
    (t : Tm sig Γ a) :
    e.tmMap (Tm.reind h t) = Tm.reind (congrArg e.sortEquiv h) (e.tmMap t) := by
  subst h
  rfl

/-- Commutation with substitution: translating a substitution is substituting
the translations, with each replacement term reindexed along the mapped
context's sort at its position. -/
theorem tmMap_subst (e : SortedSigEquiv sig sig') {Γ Δ : Ctx S} {s : S}
    (t : Tm sig Γ s) (σ : ∀ i : Fin Γ.length, Tm sig Δ (Γ.get i)) :
    e.tmMap (t.subst σ) =
      (e.tmMap t).subst
        (fun j => Tm.reind (e.get_ctx Γ (Fin.cast (e.ctx_length Γ).symm j)).symm
          (e.tmMap (σ (Fin.cast (e.ctx_length Γ).symm j)))) := by
  refine PolyFix.ind (P := polyTranslate (varOver Γ) sig.polyEndo)
    (motive := fun {s'} t => e.tmMap (Tm.subst t σ) =
      (e.tmMap t).subst
        (fun j => Tm.reind (e.get_ctx Γ (Fin.cast (e.ctx_length Γ).symm j)).symm
          (e.tmMap (σ (Fin.cast (e.ctx_length Γ).symm j))))) ?_ t
  intro s' i children ih
  match i, children, ih with
  | Sum.inl a, _, _ =>
      obtain ⟨a1, a2⟩ := a
      subst a2
      change e.tmMap (σ a1) =
        (Tm.reind (e.get_ctx Γ a1) (Tm.var (Fin.cast (e.ctx_length Γ) a1))).subst
          (fun j => Tm.reind (e.get_ctx Γ (Fin.cast (e.ctx_length Γ).symm j)).symm
            (e.tmMap (σ (Fin.cast (e.ctx_length Γ).symm j))))
      rw [Tm.subst_reind, Tm.var_subst]
      exact (Tm.reind_symm' (e.get_ctx Γ a1) (e.tmMap (σ a1))).symm
  | Sum.inr o, ch, ih =>
      change Tm.reind ((e.result_comm o.val).trans (congrArg e.sortEquiv o.2))
          (Tm.op (e.opEquiv o.val) (fun j => Tm.reind (e.get_arity o.val j)
            (e.tmMap (Tm.subst (ch (Fin.cast (e.arity_length o.val) j)) σ)))) =
        (Tm.reind ((e.result_comm o.val).trans (congrArg e.sortEquiv o.2))
          (Tm.op (e.opEquiv o.val) (fun j => Tm.reind (e.get_arity o.val j)
            (e.tmMap (ch (Fin.cast (e.arity_length o.val) j)))))).subst
          (fun j => Tm.reind (e.get_ctx Γ (Fin.cast (e.ctx_length Γ).symm j)).symm
            (e.tmMap (σ (Fin.cast (e.ctx_length Γ).symm j))))
      rw [Tm.subst_reind]
      refine congrArg (Tm.reind _) ?_
      change Tm.op (e.opEquiv o.val) (fun j => Tm.reind (e.get_arity o.val j)
          (e.tmMap (Tm.subst (ch (Fin.cast (e.arity_length o.val) j)) σ))) =
        Tm.op (e.opEquiv o.val) (fun j => (Tm.reind (e.get_arity o.val j)
          (e.tmMap (ch (Fin.cast (e.arity_length o.val) j)))).subst
          (fun j' => Tm.reind (e.get_ctx Γ (Fin.cast (e.ctx_length Γ).symm j')).symm
            (e.tmMap (σ (Fin.cast (e.ctx_length Γ).symm j')))))
      refine congrArg (Tm.op (e.opEquiv o.val)) (funext fun j => ?_)
      rw [Tm.subst_reind]
      exact congrArg (Tm.reind (e.get_arity o.val j)) (ih (Fin.cast (e.arity_length o.val) j))

/-- The double-map context identity: mapping by the sort equivalence and then
by its inverse returns the original context. -/
theorem ctx_map_map (e : SortedSigEquiv sig sig') (Γ : Ctx S) :
    (Γ.map e.sortEquiv).map e.sortEquiv.symm = Γ := by
  rw [List.map_map, e.sortEquiv.symm_comp_self, List.map_id]

/-- The context transport carrying a term over the doubly-mapped context back to
the original context. -/
def ctxCast (e : SortedSigEquiv sig sig') (Γ : Ctx S) {s : S}
    (w : Tm sig ((Γ.map e.sortEquiv).map e.sortEquiv.symm) s) : Tm sig Γ s :=
  cast (congrArg (fun c => Tm sig c s) (e.ctx_map_map Γ)) w

/-- The context transport is heterogeneously the identity. -/
theorem ctxCast_heq (e : SortedSigEquiv sig sig') (Γ : Ctx S) {s : S}
    (w : Tm sig ((Γ.map e.sortEquiv).map e.sortEquiv.symm) s) :
    HEq (e.ctxCast Γ w) w :=
  cast_heq _ _

/-- Variable terms in propositionally-equal contexts are heterogeneously
equal at corresponding positions. -/
theorem var_heq_var {T : Type} {σ : SortedSig T} {Γ Γ' : Ctx T} (h : Γ = Γ')
    (i : Fin Γ.length) :
    HEq (Tm.var (sig := σ) i) (Tm.var (sig := σ) (Fin.cast (congrArg List.length h) i)) := by
  subst h
  rfl

/-- Reindexing is heterogeneously the identity. -/
theorem reind_heq {T : Type} {σ : SortedSig T} {Γ : Ctx T} {a b : T} (h : a = b)
    (t : Tm σ Γ a) : HEq (Tm.reind h t) t := by
  subst h
  rfl

/-- Operation terms in propositionally-equal contexts with propositionally-equal
operations and heterogeneously-equal arguments are heterogeneously equal. -/
theorem op_heq {T : Type} {σ : SortedSig T} {Γ Γ' : Ctx T} (hΓ : Γ = Γ')
    {o o' : σ.Op} (ho : o' = o)
    (args : ∀ i : Fin (σ.arity o).length, Tm σ Γ ((σ.arity o).get i))
    (args' : ∀ i : Fin (σ.arity o').length, Tm σ Γ' ((σ.arity o').get i))
    (h : ∀ i : Fin (σ.arity o').length,
      HEq (args' i) (args (Fin.cast (congrArg (fun p => (σ.arity p).length) ho) i))) :
    HEq (Tm.op (Γ := Γ') o' args') (Tm.op (Γ := Γ) o args) := by
  subst hΓ
  subst ho
  exact heq_of_eq (congrArg (Tm.op o') (funext fun i => eq_of_heq (h i)))

/-- The round trip up to heterogeneous equality: translating and translating
back returns the original term (the transports being absorbed by `HEq`). -/
theorem tmMap_symm_tmMap_heq (e : SortedSigEquiv sig sig') {Γ : Ctx S} {s : S}
    (t : Tm sig Γ s) : HEq (e.symm.tmMap (e.tmMap t)) t := by
  refine PolyFix.ind (P := polyTranslate (varOver Γ) sig.polyEndo)
    (motive := fun {s'} t => HEq (e.symm.tmMap (e.tmMap t)) t) ?_ t
  intro s' i children ih
  match i, children, ih with
  | Sum.inl a, _, _ =>
      obtain ⟨a1, a2⟩ := a
      subst a2
      change HEq (e.symm.tmMap (e.tmMap (Tm.var (sig := sig) (Γ := Γ) a1))) _
      rw [tmMap_var, tmMap_reind, tmMap_var]
      refine (reind_heq _ _).trans ((reind_heq _ _).trans
        ((var_heq_var (e.ctx_map_map Γ) _).trans ?_))
      exact heq_of_eq (congrArg _ (funext fun e : PEmpty => e.elim))
  | Sum.inr o, ch, ih =>
      obtain ⟨op, hop⟩ := o
      subst hop
      change HEq (e.symm.tmMap (e.tmMap (Tm.op (sig := sig) (Γ := Γ) op ch)))
        (Tm.op (sig := sig) (Γ := Γ) op ch)
      rw [tmMap_op, tmMap_reind, tmMap_op]
      refine (reind_heq _ _).trans ((reind_heq _ _).trans ?_)
      refine op_heq (e.ctx_map_map Γ).symm (Equiv.symm_apply_apply e.opEquiv op) ch _ ?_
      intro j
      refine (reind_heq _ _).trans ?_
      rw [tmMap_reind]
      exact (reind_heq _ _).trans (ih _)

/-- The round trip: translating and translating back is the identity, up to the
context transport `ctx_map_map` and the sort transport `sortEquiv.symm_apply_apply`. -/
theorem tmMap_symm_tmMap (e : SortedSigEquiv sig sig') {Γ : Ctx S} {s : S}
    (t : Tm sig Γ s) :
    e.ctxCast Γ (Tm.reind (e.sortEquiv.symm_apply_apply s) (e.symm.tmMap (e.tmMap t))) = t := by
  apply eq_of_heq
  exact ((e.ctxCast_heq Γ _).trans (reind_heq _ _)).trans (e.tmMap_symm_tmMap_heq t)

/-- The double-map context identity in the other direction: mapping by the
inverse sort equivalence and then by the sort equivalence returns the context. -/
theorem ctx_map_map' (e : SortedSigEquiv sig sig') (Δ : Ctx S') :
    (Δ.map e.sortEquiv.symm).map e.sortEquiv = Δ := by
  rw [List.map_map, e.sortEquiv.self_comp_symm, List.map_id]

/-- The reverse round trip up to heterogeneous equality. -/
theorem tmMap_tmMap_symm_heq (e : SortedSigEquiv sig sig') {Δ : Ctx S'} {s' : S'}
    (u : Tm sig' Δ s') : HEq (e.tmMap (e.symm.tmMap u)) u := by
  refine PolyFix.ind (P := polyTranslate (varOver Δ) sig'.polyEndo)
    (motive := fun {s'} u => HEq (e.tmMap (e.symm.tmMap u)) u) ?_ u
  intro s'' i children ih
  match i, children, ih with
  | Sum.inl a, _, _ =>
      obtain ⟨a1, a2⟩ := a
      subst a2
      change HEq (e.tmMap (e.symm.tmMap (Tm.var (sig := sig') (Γ := Δ) a1))) _
      rw [tmMap_var, tmMap_reind, tmMap_var]
      refine (reind_heq _ _).trans ((reind_heq _ _).trans
        ((var_heq_var (e.ctx_map_map' Δ) _).trans ?_))
      exact heq_of_eq (congrArg _ (funext fun ee : PEmpty => ee.elim))
  | Sum.inr o, ch, ih =>
      obtain ⟨op, hop⟩ := o
      subst hop
      change HEq (e.tmMap (e.symm.tmMap (Tm.op (sig := sig') (Γ := Δ) op ch)))
        (Tm.op (sig := sig') (Γ := Δ) op ch)
      rw [tmMap_op, tmMap_reind, tmMap_op]
      refine (reind_heq _ _).trans ((reind_heq _ _).trans ?_)
      refine op_heq (e.ctx_map_map' Δ).symm (Equiv.apply_symm_apply e.opEquiv op) ch _ ?_
      intro j
      refine (reind_heq _ _).trans ?_
      rw [tmMap_reind]
      exact (reind_heq _ _).trans (ih _)

/-- The translation respects heterogeneous equality of its argument, given the
context and sort agree. -/
theorem tmMap_heq_arg (e : SortedSigEquiv sig sig') {Γ Γ₂ : Ctx S} (hΓ : Γ = Γ₂)
    {a a₂ : S} (ha : a = a₂) {A : Tm sig Γ a} {B : Tm sig Γ₂ a₂} (h : HEq A B) :
    HEq (e.tmMap A) (e.tmMap B) := by
  subst hΓ
  subst ha
  exact heq_of_eq (congrArg e.tmMap (eq_of_heq h))

/-- The reverse round trip. -/
theorem tmMap_tmMap_symm (e : SortedSigEquiv sig sig') {Γ : Ctx S} {s : S}
    (u : Tm sig' (Γ.map e.sortEquiv) (e.sortEquiv s)) :
    e.tmMap (e.ctxCast Γ (Tm.reind (e.sortEquiv.symm_apply_apply s) (e.symm.tmMap u))) = u := by
  apply eq_of_heq
  refine HEq.trans ?_ (e.tmMap_tmMap_symm_heq u)
  exact tmMap_heq_arg e (e.ctx_map_map Γ).symm (e.sortEquiv.symm_apply_apply s).symm
    ((e.ctxCast_heq Γ _).trans (reind_heq _ _))

/-- The term translation packaged as an equivalence. -/
def tmEquiv (e : SortedSigEquiv sig sig') (Γ : Ctx S) (s : S) :
    Tm sig Γ s ≃ Tm sig' (Γ.map e.sortEquiv) (e.sortEquiv s) where
  toFun t := e.tmMap t
  invFun u := e.ctxCast Γ (Tm.reind (e.sortEquiv.symm_apply_apply s) (e.symm.tmMap u))
  left_inv t := e.tmMap_symm_tmMap t
  right_inv u := e.tmMap_tmMap_symm u

end SortedSigEquiv

end GebLean.Ramified
