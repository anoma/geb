import GebLean.PolyBridge.Slice
import GebLean.Ramified.Term
import GebLean.SliceW.FreeM

/-!
# The sorted term layer on the slice free monad

A second realization of the sorted term layer with clone laws
(`GebLean/Ramified/Term.lean`) on the vendored `geb-mathlib` slice free monad
`SlicePFunctor.FreeM` (`GebLean/SliceW/FreeM.lean`) rather than the legacy
`PolyFreeM`. `Tm' sig Γ` is `SlicePFunctor.FreeM Γ.get (toSlice sig.polyEndo)`;
`Tm'.subst` is the slice free monad's `bind`; and the clone laws
`Tm'.subst_id` and `Tm'.subst_subst` are thin instances of `bind`'s
right-unit and associativity laws, mirroring the legacy proofs with
`SlicePFunctor.FreeM.bind_pure`, `SlicePFunctor.FreeM.bind_assoc`,
`SlicePFunctor.FreeM.pure_transport`, and `SlicePFunctor.FreeM.bind_transport`
in place of the legacy `polyFreeM_bind_pure`, `polyFreeM_bind_assoc`,
`polyFreeMPure_transport`, and `polyFreeMBind_transport`.

## Main definitions

* `Tm'` — terms over a signature in a context, indexed by their sort: the
  slice free monad of `toSlice sig.polyEndo` at the context's variable
  family `Γ.get`.
* `Tm'.var` — a variable term (the slice free monad's `pure` at a position).
* `Tm'.op` — an operation applied to argument terms (a `FreeM.node`).
* `Tm'.subst` — simultaneous substitution (the slice free monad's `bind`).
* `Tm'.reind` — reindexing of a term along an equality of its sort.
* `Tm'.weaken` — substitution along a sort-preserving variable renaming.

## Main statements

* `Tm'.subst_id` — substitution by the variable tuple is the identity.
* `Tm'.subst_subst` — substitution composes.
* `Tm'.var_subst` — substituting a variable by a tuple selects that tuple
  entry.
* `Tm'.subst_reind` — substitution commutes with reindexing.

## References

The free-algebra conventions realized here follow D. Leivant, "Ramified
recurrence and computational complexity III: Higher type recurrence and
elementary complexity", Annals of Pure and Applied Logic 96 (1999) 209-229,
DOI `10.1016/S0168-0072(98)00040-2`, section 2.1, transcribed by the legacy
`GebLean/Ramified/Term.lean`.

## Tags

ramified recurrence, sorted term, substitution, clone laws, free monad,
polynomial functor, slice category
-/

namespace GebLean.Ramified.Polynomial

open GebLean.Ramified GebLean.PolyBridge SlicePFunctor

variable {S : Type}

/-- Terms over a signature `sig` in a context `Γ`, indexed by their sort: the
slice free monad of `toSlice sig.polyEndo` at the context's variable family
`Γ.get`. A second realization of `Tm sig Γ` (`GebLean/Ramified/Term.lean`),
consuming the slice free monad (`GebLean/SliceW/FreeM.lean`) rather than
`PolyFreeM`. -/
def Tm' (sig : SortedSig S) (Γ : Ctx S) : S → Type :=
  FreeM Γ.get (toSlice sig.polyEndo)

/-- A variable term: the position `i` of `Γ`, as the slice free monad's `pure`
at that position's fiber element. Its sort is `Γ.get i`. -/
def Tm'.var {sig : SortedSig S} {Γ : Ctx S} (i : Fin Γ.length) :
    Tm' sig Γ (Γ.get i) :=
  FreeM.pure ⟨i, rfl⟩

/-- An operation `o` applied to a tuple of argument terms, at the operation's
result sort: the slice free monad's `node` at the shape `⟨sig.result o,
⟨o, rfl⟩⟩` of `toSlice sig.polyEndo`, whose directions are the arity
positions. -/
def Tm'.op {sig : SortedSig S} {Γ : Ctx S} (o : sig.Op)
    (args : ∀ i : Fin (sig.arity o).length, Tm' sig Γ ((sig.arity o).get i)) :
    Tm' sig Γ (sig.result o) :=
  FreeM.node (F := toSlice sig.polyEndo) ⟨sig.result o, ⟨o, rfl⟩⟩ args

/-- Simultaneous substitution: replace each variable of `t` by the
corresponding term of the tuple `σ`. Realized as the slice free monad's
`bind`, reading `σ` as a map of the source variable family into terms over
the target context; the leaf function transports each `σ i` along the fiber
equality of the variable being replaced. -/
def Tm'.subst {sig : SortedSig S} {Γ Δ : Ctx S} {s : S}
    (t : Tm' sig Γ s) (σ : ∀ i : Fin Γ.length, Tm' sig Δ (Γ.get i)) :
    Tm' sig Δ s :=
  t.bind (fun _ a => a.2 ▸ σ a.1)

/-- Substitution by the variable tuple is the identity (the right-unit clone
law). An instance of the slice free monad's right-unit law
`SlicePFunctor.FreeM.bind_pure`, after identifying the transported variable
tuple with the monad's `pure`; mirrors the legacy `Tm.subst_id`
(`GebLean/Ramified/Term.lean`). -/
theorem Tm'.subst_id {sig : SortedSig S} {Γ : Ctx S} {s : S} (t : Tm' sig Γ s) :
    t.subst Tm'.var = t := by
  unfold Tm'.subst
  refine Eq.trans ?_ (FreeM.bind_pure t)
  congr 1
  funext y a
  obtain ⟨v, hv⟩ := a
  exact FreeM.pure_transport hv v rfl

/-- Substitution composes: substituting by `σ` then `τ` equals substituting by
the pointwise composite (the associativity clone law). An instance of the
slice free monad's associativity law `SlicePFunctor.FreeM.bind_assoc`, using
`SlicePFunctor.FreeM.bind_transport` to move the transport past the inner
bind; mirrors the legacy `Tm.subst_subst` (`GebLean/Ramified/Term.lean`). -/
theorem Tm'.subst_subst {sig : SortedSig S} {Γ Δ E : Ctx S} {s : S}
    (t : Tm' sig Γ s) (σ : ∀ i : Fin Γ.length, Tm' sig Δ (Γ.get i))
    (τ : ∀ i : Fin Δ.length, Tm' sig E (Δ.get i)) :
    (t.subst σ).subst τ = t.subst (fun i => (σ i).subst τ) := by
  unfold Tm'.subst
  rw [FreeM.bind_assoc]
  congr 1
  funext y a
  exact FreeM.bind_transport a.2 (σ a.1) _

/-- Substituting a variable term by a tuple selects that tuple's entry at the
variable's position (the free monad's left-unit law
`SlicePFunctor.FreeM.pure_bind`; the transport at `rfl` vanishes
definitionally). -/
theorem Tm'.var_subst {sig : SortedSig S} {Γ Δ : Ctx S}
    (i : Fin Γ.length) (σ : ∀ j : Fin Γ.length, Tm' sig Δ (Γ.get j)) :
    (Tm'.var i).subst σ = σ i := by
  unfold Tm'.subst Tm'.var
  rw [FreeM.pure_bind]

/-- Reindex a term along an equality of its sort. -/
def Tm'.reind {sig : SortedSig S} {Γ : Ctx S} {a b : S} (h : a = b)
    (t : Tm' sig Γ a) : Tm' sig Γ b := h ▸ t

/-- Reindexing along `rfl` is the identity. -/
@[simp] theorem Tm'.reind_rfl {sig : SortedSig S} {Γ : Ctx S} {a : S}
    (t : Tm' sig Γ a) : Tm'.reind rfl t = t := rfl

/-- Substitution commutes with reindexing of its input term. -/
theorem Tm'.subst_reind {sig : SortedSig S} {Γ Δ : Ctx S} {a b : S}
    (h : a = b) (t : Tm' sig Γ a)
    (σ : ∀ j : Fin Γ.length, Tm' sig Δ (Γ.get j)) :
    (Tm'.reind h t).subst σ = Tm'.reind h (t.subst σ) := by
  subst h; rfl

/-- Weakening along a sort-preserving variable renaming `f`: substitution at
the variable tuple that sends position `i` to the variable `f i`, transported
along the sort equality `h`. A special case of `Tm'.subst`
(variable-to-variable substitution). -/
def Tm'.weaken {sig : SortedSig S} {Γ Δ : Ctx S} {s : S}
    (f : Fin Γ.length → Fin Δ.length) (h : ∀ i, Δ.get (f i) = Γ.get i)
    (t : Tm' sig Γ s) : Tm' sig Δ s :=
  t.subst (fun i => Tm'.reind (h i) (Tm'.var (f i)))

end GebLean.Ramified.Polynomial
