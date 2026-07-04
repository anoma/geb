import GebLean.Ramified.SortedSig

/-!
# The sorted term layer with clone laws

The syntactic terms of a multi-sorted signature over a context, realized on
the repository's free-monad structure (decision 8: every recursive type is a
`PolyFix` W-type of a `PolyEndo`, and substitution is free-monad bind).
`SortedSig.polyEndo` presents a multi-sorted signature as an indexed
polynomial endofunctor on the sort type; `Tm sig Γ` is the free monad of that
endofunctor at the context's variable family; `Tm.subst` is the free monad's
bind; and the clone laws `Tm.subst_id` and `Tm.subst_subst` are instances of
the free monad's right-unit and associativity laws.

These definitions are novel packaging: they present the free-algebra
conventions of Leivant III section 2.1 through this development's
polynomial-endofunctor stack (decision 8), consuming the repository's existing
free monad (`PolyFreeM`, `polyFreeMPure`, `polyFreeMBind`, and the monad laws
`polyFreeM_bind_pure`, `polyFreeM_bind_assoc` of `GebLean/PolyAlg.lean`) rather
than rebuilding it. The clone-law statements follow the repository precedent
`Era.Tm.subst_id` and `Era.Tm.subst_subst` (`GebLean/Era.lean`).

## Main definitions

* `Ctx` — a context: a finite list of sorts.
* `SortedSig.polyEndo` — the indexed polynomial signature endofunctor of a
  sorted signature over its sort type.
* `varOver` — the variable family of a context, as an object of `Over S`.
* `Tm` — terms over a signature in a context: the free monad of
  `SortedSig.polyEndo` at the context's variable family.
* `Tm.var` — a variable term (the free monad's unit at a position).
* `Tm.op` — an operation applied to argument terms (a `PolyFix` node).
* `Tm.subst` — simultaneous substitution (the free monad's bind).
* `Tm.reind` — reindexing of a term along an equality of its sort.
* `Tm.weaken` — substitution along a sort-preserving variable renaming.
* `QuotRel` — a quotient relation for the syntactic category: a per-hom setoid
  family closed under substitution in both positions.

## Main statements

* `Tm.subst_id` — substitution by the variable tuple is the identity (the
  free monad's right-unit law).
* `Tm.subst_subst` — substitution composes (the free monad's associativity
  law).
* `Tm.var_subst` — substituting a variable by a tuple selects that tuple entry
  (the free monad's left-unit law).
* `Tm.subst_reind` — substitution commutes with reindexing.
* `QuotRel.rel_reind` — a quotient relation is preserved by reindexing.

## Implementation notes

The free monad's bind takes leaf-substitution functions indexed by a sort
`y : S` and a fiber element of the variable family; the clone laws are stated
in the term vocabulary, where a substitution is a tuple
`∀ i, Tm sig Δ (Γ.get i)` indexed by context positions. The translation
inserts a transport of the substitution tuple along the fiber equality. The
associativity law therefore needs the fact that bind commutes with this
transport, reusing the existing `GebLean.polyFreeMBind_transport`
(`GebLean/PolyAlg.lean`).

## References

The free-algebra conventions realized here follow D. Leivant, "Ramified
recurrence and computational complexity III: Higher type recurrence and
elementary complexity", Annals of Pure and Applied Logic 96 (1999) 209-229,
DOI `10.1016/S0168-0072(98)00040-2`, section 2.1. The clone-law statements
follow the repository precedent `Era.Tm.subst_id` and `Era.Tm.subst_subst`
in `GebLean/Era.lean`.

## Tags

ramified recurrence, sorted term, substitution, clone laws, free monad,
polynomial functor, W-type
-/

namespace GebLean.Ramified

open CategoryTheory

variable {S : Type}

/-- A context: a finite list of sorts, read as a family of typed positions
(decision 7: contexts are parameters of the term layer). Novel packaging. -/
abbrev Ctx (S : Type) : Type := List S

/-- The indexed polynomial signature endofunctor of a sorted signature over
the sort type `S` (decision 8: multi-sorted signatures are subsumed by taking
the sort type as the domain and codomain of the slice polynomial endofunctor).
At output sort `s`, the shapes are the operations with result `s`, and the
directions at an operation are its arity positions, mapped to the argument
sorts. Novel packaging of the free-algebra conventions of Leivant III section
2.1 through this development's polynomial-endofunctor stack. -/
def SortedSig.polyEndo (sig : SortedSig S) : PolyEndo S :=
  fun s => ccrObjMk fun o : { p : sig.Op // sig.result p = s } =>
    Over.mk (fun i : Fin (sig.arity o.val).length => (sig.arity o.val).get i)

/-- The variable family of a context, as an object of `Over S`: the positions
of `Γ` (the type `Fin Γ.length`), fibered by their sorts (the map `Γ.get`).
Novel packaging. -/
def varOver (Γ : Ctx S) : Over S := Over.mk Γ.get

/-- Terms over a signature `sig` in a context `Γ`, indexed by their sort: the
repository's free monad of `sig.polyEndo` at the context's variable family
(decision 8; the free-monad layer of `GebLean/PolyAlg.lean` is consumed, not
rebuilt). A term at sort `s` is a `sig.polyEndo`-branching tree with
`Γ`-variable leaves. Novel packaging. -/
def Tm (sig : SortedSig S) (Γ : Ctx S) : S → Type :=
  PolyFreeM (varOver Γ) sig.polyEndo

/-- A variable term: the position `i` of `Γ`, as the free monad's unit
(`polyFreeMPure`) at that position's fiber element. Its sort is `Γ.get i`.
Novel packaging. -/
def Tm.var {sig : SortedSig S} {Γ : Ctx S} (i : Fin Γ.length) :
    Tm sig Γ (Γ.get i) :=
  polyFreeMPure (varOver Γ) sig.polyEndo ⟨i, rfl⟩

/-- An operation `o` applied to a tuple of argument terms, at the operation's
result sort: the `PolyFix` node at the shape `o` of `sig.polyEndo`, whose
directions are the arity positions. Novel packaging. -/
def Tm.op {sig : SortedSig S} {Γ : Ctx S} (o : sig.Op)
    (args : ∀ i : Fin (sig.arity o).length, Tm sig Γ ((sig.arity o).get i)) :
    Tm sig Γ (sig.result o) :=
  PolyFix.mk (sig.result o) (Sum.inr ⟨o, rfl⟩) args

/-- Simultaneous substitution: replace each variable of `t` by the
corresponding term of the tuple `σ`. Realized as the free monad's bind
(`polyFreeMBind`), reading `σ` as a map of the source variable family into
terms over the target context; the leaf function transports each `σ i` along
the fiber equality of the variable being replaced. Novel packaging. -/
def Tm.subst {sig : SortedSig S} {Γ Δ : Ctx S} {s : S}
    (t : Tm sig Γ s) (σ : ∀ i : Fin Γ.length, Tm sig Δ (Γ.get i)) :
    Tm sig Δ s :=
  polyFreeMBind (varOver Γ) (varOver Δ) sig.polyEndo t (fun _ a => a.2 ▸ σ a.1)

/-- Substitution by the variable tuple is the identity (the right-unit clone
law). An instance of the free monad's right-unit law `polyFreeM_bind_pure`,
after identifying the transported variable tuple with the monad's unit;
follows the precedent `Era.Tm.subst_id` (`GebLean/Era.lean`). -/
theorem Tm.subst_id {sig : SortedSig S} {Γ : Ctx S} {s : S} (t : Tm sig Γ s) :
    t.subst Tm.var = t := by
  unfold Tm.subst
  refine Eq.trans ?_ (polyFreeM_bind_pure (varOver Γ) sig.polyEndo t)
  congr 1
  funext y a
  obtain ⟨v, hv⟩ := a
  exact polyFreeMPure_transport (varOver Γ) sig.polyEndo hv v rfl

/-- Substitution composes: substituting by `σ` then `τ` equals substituting by
the pointwise composite (the associativity clone law). An instance of the free
monad's associativity law `polyFreeM_bind_assoc`, using
`GebLean.polyFreeMBind_transport` to move the transport past the inner bind;
follows the precedent `Era.Tm.subst_subst` (`GebLean/Era.lean`). -/
theorem Tm.subst_subst {sig : SortedSig S} {Γ Δ E : Ctx S} {s : S}
    (t : Tm sig Γ s) (σ : ∀ i : Fin Γ.length, Tm sig Δ (Γ.get i))
    (τ : ∀ i : Fin Δ.length, Tm sig E (Δ.get i)) :
    (t.subst σ).subst τ = t.subst (fun i => (σ i).subst τ) := by
  unfold Tm.subst
  rw [polyFreeM_bind_assoc]
  congr 1
  funext y a
  exact (polyFreeMBind_transport (varOver Δ) (varOver E) sig.polyEndo a.2 (σ a.1) _).symm

/-- Substituting a variable term by a tuple selects that tuple's entry at the
variable's position (the free monad's left-unit law `polyFreeM_pure_bind`). -/
theorem Tm.var_subst {sig : SortedSig S} {Γ Δ : Ctx S}
    (i : Fin Γ.length) (σ : ∀ j : Fin Γ.length, Tm sig Δ (Γ.get j)) :
    (Tm.var i).subst σ = σ i := rfl

/-- Reindex a term along an equality of its sort. -/
def Tm.reind {sig : SortedSig S} {Γ : Ctx S} {a b : S} (h : a = b)
    (t : Tm sig Γ a) : Tm sig Γ b := h ▸ t

/-- Reindexing along `rfl` is the identity. -/
@[simp] theorem Tm.reind_rfl {sig : SortedSig S} {Γ : Ctx S} {a : S}
    (t : Tm sig Γ a) : Tm.reind rfl t = t := rfl

/-- Reindexing then reindexing back along the reverse equality is the
identity. -/
theorem Tm.reind_symm {sig : SortedSig S} {Γ : Ctx S} {a b : S} (h : a = b)
    (t : Tm sig Γ a) : Tm.reind h.symm (Tm.reind h t) = t := by
  subst h; rfl

/-- Reindexing back then forward along an equality is the identity. -/
theorem Tm.reind_symm' {sig : SortedSig S} {Γ : Ctx S} {a b : S} (h : a = b)
    (t : Tm sig Γ b) : Tm.reind h (Tm.reind h.symm t) = t := by
  subst h; rfl

/-- Substitution commutes with reindexing of its input term. -/
theorem Tm.subst_reind {sig : SortedSig S} {Γ Δ : Ctx S} {a b : S}
    (h : a = b) (t : Tm sig Γ a)
    (σ : ∀ j : Fin Γ.length, Tm sig Δ (Γ.get j)) :
    (Tm.reind h t).subst σ = Tm.reind h (t.subst σ) := by
  subst h; rfl

/-- Weakening along a sort-preserving variable renaming `f`: substitution at
the variable tuple that sends position `i` to the variable `f i`, transported
along the sort equality `h`. A special case of `Tm.subst` (variable-to-variable
substitution). Novel packaging. -/
def Tm.weaken {sig : SortedSig S} {Γ Δ : Ctx S} {s : S}
    (f : Fin Γ.length → Fin Δ.length) (h : ∀ i, Δ.get (f i) = Γ.get i)
    (t : Tm sig Γ s) : Tm sig Δ s :=
  t.subst (fun i => Tm.reind (h i) (Tm.var (f i)))

/-- A quotient relation for the syntactic category: a per-hom setoid family on
terms together with the congruence law composition needs (substitution
respects the relation in both positions). The relation is a parameter of the
syntactic-category construction; interpretative and derivability
instantiations are supplied downstream. Novel packaging. -/
structure QuotRel (sig : SortedSig S) where
  /-- The per-context, per-sort setoid on terms. -/
  rel : (Γ : Ctx S) → (s : S) → Setoid (Tm sig Γ s)
  /-- Substitution respects the relation in both positions: related terms
  substituted by pointwise-related tuples yield related results. -/
  subst_congr :
    ∀ {Γ Δ s} (t t' : Tm sig Γ s)
      (σ σ' : ∀ i, Tm sig Δ (Γ.get i)),
      (rel Γ s) t t' → (∀ i, (rel Δ _) (σ i) (σ' i)) →
      (rel Δ s) (t.subst σ) (t'.subst σ')

/-- A quotient relation is preserved by reindexing along a sort equality. -/
theorem QuotRel.rel_reind {sig : SortedSig S} (r : QuotRel sig) {T : Ctx S}
    {a b : S} (h : a = b) {x y : Tm sig T a} (hxy : (r.rel T a) x y) :
    (r.rel T b) (Tm.reind h x) (Tm.reind h y) := by
  subst h; exact hxy

end GebLean.Ramified
